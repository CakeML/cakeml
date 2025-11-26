(*
  Formalization of the CP to ILP phase (shared infrastructure)
*)
Theory cp_to_ilp
Libs
  preamble
Ancestors
  cp ilp pbc pbc_encode sptree

(* The shared infrastructure for all encodings goes into this file *)

(* The datatype for reified variables in the ILP encoding *)
Datatype:
  reif =
  | Ge ('a varc) int (* Reifies X ≥ i *)
  | Eq ('a varc) int (* Reifies X = i *)
End

Definition reify_reif_def:
  reify_reif wi reif ⇔
  case reif of
    Ge X i => varc wi X ≥ i
  | Eq X i => varc wi X = i
End

(* The datatype for flags in the ILP encoding. *)
Datatype:
  flag =
  | Ne ('a + int) ('a + int)  (* Used to force X ≠ Y *)
  | Gem ('a + int) ('a + int) (* Used to force X ≥ Y in Array Max *)
  | Eqc ('a + int) ('a + int) (* Used to force X = Y in Count *)
  | Nv ('a list) int (* Used to force some element in As = v *)
  | Tb (('a varc # int) list) (* Forces Xs = t for a given row*)
End

Definition reify_flag_def:
  reify_flag wi flag ⇔
  case flag of
  | Ne X Y => varc wi X > varc wi Y
  | Gem X Y => varc wi X ≥ varc wi Y
  | Eqc X Y => varc wi X = varc wi Y
  | Tb Xts => EVERY (λ(X,t). varc wi X = t) Xts
  | Nv Xs v => MEM v $ MAP wi Xs
End

(*
  We first design and prove sound the
  abstract encodings into the Boolean variable type:
    ('a reif + 'a flag)
*)
Type avar[pp] = ``:('a reif + 'a flag)``
Type aiconstraint[pp] = ``:('a, 'a avar) iconstraint``

Definition reify_avar_def:
  reify_avar wi eb ⇔
  case eb of
    INL reif => reify_reif wi reif
  | INR flag => reify_flag wi flag
End

(***
  Helper encoding functions
***)

(* Encoding a single variable X_{>=i} ⇔ X ≥ i *)
Definition encode_ge_def:
  encode_ge (bnd:'a bounds) (Xi:'a varc) i =
  let cc =
    case Xi of
      INL X => ([(1,X)],[],i)
    | INR v => ([],[],1 - b2i (v ≥ i))
  in
  bimply_bits bnd [Pos (INL (Ge Xi i))] cc
End

Theorem encode_ge_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (INL (Ge X i)) ⇔ varc wi X ≥ i)
Proof
  rw[encode_ge_def]>>
  TOP_CASE_TAC>>
  simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def]
  >- metis_tac[]
  >- rw[b2i_alt]
QED

(* Encoding a single variable X = i, separate from encode_ge
  X_{=i} ⇔ X_{>=i} ∧ ~X_{>=i+1}
*)
Definition encode_eq_def:
  encode_eq bnd X i =
  (bimply_bits bnd [Pos (INL (Eq X i))]
    ([],[(1,Pos(INL (Ge X i)));(1, Neg (INL (Ge X (i+1))))],2))
End

Theorem encode_eq_sem[simp]:
  valid_assignment bnd wi ∧
  (wb (INL (Ge X i)) ⇔ varc wi X ≥ i) ∧
  (wb (INL (Ge X (i+1))) ⇔ varc wi X ≥ i+1)
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X i)
  =
  (wb (INL (Eq X i)) ⇔ varc wi X = i)
Proof
  rw[encode_eq_def]>>
  gs[iconstraint_sem_def,b2i_alt]>>
  rw[]>>
  eq_tac>>rw[]>>
  intLib.ARITH_TAC
QED

Definition encode_full_eq_def:
  encode_full_eq bnd X i =
  encode_ge bnd X i ++
  encode_ge bnd X (i+1) ++
  encode_eq bnd X i
End

Theorem encode_full_eq_sem[simp]:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_full_eq bnd X i)
  =
  ((wb (INL (Ge X i)) ⇔ varc wi X ≥ i) ∧
  (wb (INL (Ge X (i+1))) ⇔ varc wi X ≥ i+1) ∧
  (wb (INL (Eq X i)) ⇔ varc wi X = i))
Proof
  rw[encode_full_eq_def]>>
  metis_tac[encode_eq_sem]
QED

(*
(* encodes X ≥ 1,...,X ≥ n *)
Definition encode_ges_def:
  encode_ges bnd X n =
  FLAT (GENLIST (λi. encode_ge bnd X (&(i + 1))) n)
End

Theorem encode_ges_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ges bnd X n) =
  (∀i. 1 ≤ i ∧ i ≤ n ⇒ (wb (INL (Ge X &i)) ⇔ wi X ≥ &i))
Proof
  rw[encode_ges_def,encode_ge_sem,EVERY_FLAT,EVERY_GENLIST]>>
  iff_tac>>rw[]>>
  ‘∃j. i = j + 1’ by intLib.ARITH_TAC>>
  fs[]
QED

(* encodes X = 1,...,X = n *)
Definition encode_eqs_def:
  encode_eqs bnd X n =
  FLAT (GENLIST (λi. encode_eq bnd X (&(i + 1))) n)
End

Theorem FORALL_LT[local]:
  (∀i. i < n ⇒ P (int_of_num (i + 1))) ⇔ (∀i. 1 ≤ i ∧ i ≤ n ⇒ P $ int_of_num i)
Proof
  iff_tac>>
  rw[]>>
  ‘∃j. i = j + 1’ by intLib.ARITH_TAC>>
  fs[]
QED

Theorem FORALL_IMP_EQ = METIS_PROVE []
  ``(∀x. P x ⇒ (Q x ⇔ R x)) ⇒ ((∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x))``;

Theorem encode_eqs_sem[simp]:
  valid_assignment bnd wi ∧
  (∀i. 1 ≤ i ∧ i ≤ n + 1 ⇒ (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eqs bnd X n) =
  ∀i. 1 ≤ i ∧ i ≤ n ⇒ (wb (INL (Eq X &i)) ⇔ wi X = &i)
Proof
  rw[encode_eqs_def,EVERY_FLAT,EVERY_GENLIST,FORALL_LT]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  rw[]>>
  simp[GSYM integerTheory.INT]
QED
*)

(* Encodes a * X + b * Y ≥ c where both X, Y are varc *)
Definition mk_constraint_ge_def:
  mk_constraint_ge (a:int) X (b:int) Y (c:int) =
  case (X,Y) of
    (INL vX, INL vY) =>
      ([(a,vX);(b,vY)],[],c)
  | (INL vX, INR cY) =>
      ([(a,vX)],[],c - b * cY)
  | (INR cX, INL vY) =>
      ([(b,vY)],[],c - a * cX)
  | (INR cX, INR cY) =>
      ([],[],c - a * cX - b * cY)
End

Theorem mk_constraint_ge_sem[simp]:
  iconstraint_sem (mk_constraint_ge a X b Y c) (wi,wb) ⇔
  a * (varc wi X) + b * (varc wi Y) ≥ c
Proof
  rw[mk_constraint_ge_def]>>every_case_tac>>
  gvs[varc_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

(*
  General setup for problem encodings from
  mlstring-variabled CP constraints.

  mlstring constraint

  into

  (mlstring option # (mlstring, mlstring avar) iconstraint)

  The mlstring option is an annotation.
*)

(* TODO: replace ge/eq with faster representations. *)
Datatype:
  enc_conf =
    <|
       ge : ( (mlstring varc) # int list) list
     ; eq : ( (mlstring varc) # int list) list
    |>
End

(***
  Semantic tools
***)

(* lookup for when the given ge for a variable has been encoded *)
Definition has_ge_def:
  has_ge Y n ec =
  case ALOOKUP ec.ge Y of
    NONE => F
  | SOME ls => MEM n ls
End

Definition has_eq_def:
  has_eq Y n ec =
  case ALOOKUP ec.eq Y of
    NONE => F
  | SOME ls => MEM n ls
End

Definition good_reif_def:
  good_reif wb wi ec ⇔
  (∀Y n. has_ge Y n ec ⇒ (wb (INL (Ge Y n)) ⇔ varc wi Y ≥ n)) ∧
  (∀Y n. has_eq Y n ec ⇒ (wb (INL (Eq Y n)) ⇔ varc wi Y = n))
End

(* enc_rel, just a shorthand *)
Definition enc_rel_def:
  enc_rel wi es es' ec ec' ⇔
  (∀wb.
    EVERY (λx. iconstraint_sem (SND x) (wi,wb)) (append es) ∧
    good_reif wb wi ec ⇒
    good_reif wb wi ec') ∧
  ∀wb.
  good_reif wb wi ec ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) es' ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wb)) (append es))
End

Theorem enc_rel_Nil:
  enc_rel wi Nil [] ec ec
Proof
  rw[enc_rel_def]
QED

Theorem enc_rel_Append:
  enc_rel wi es xs ec ec' ∧
  enc_rel wi es' xs' ec' ec'' ⇒
  enc_rel wi (Append es es') (xs++xs') ec ec''
Proof
  rw[]>>
  fs[enc_rel_def]>>
  rw[]>>
  metis_tac[]
QED

(***
  Dealing with ge / eq
***)
Definition add_ge_def:
  add_ge Y n ec =
  let tt =
    (case ALOOKUP ec.ge Y of
      NONE => []
    | SOME ls => ls) in
  ec with ge := (Y,n::tt)::ec.ge
End

Definition add_eq_def:
  add_eq Y n ec =
  let tt =
    (case ALOOKUP ec.eq Y of
      NONE => []
    | SOME ls => ls) in
  ec with eq := (Y,n::tt)::ec.eq
End

Theorem has_ge_add_ge[simp]:
  has_ge X n (add_ge Y m ec) ⇔
  X = Y ∧ n = m ∨
  has_ge X n ec
Proof
  rw[has_ge_def,add_ge_def]>>every_case_tac>>simp[]
QED

Theorem has_ge_add_eq[simp]:
  has_ge X n (add_eq Y m ec) ⇔
  has_ge X n ec
Proof
  rw[has_ge_def,add_eq_def]>>every_case_tac>>simp[]
QED

Theorem has_eq_add_eq[simp]:
  has_eq X n (add_eq Y m ec) ⇔
  X = Y ∧ n = m ∨
  has_eq X n ec
Proof
  rw[has_eq_def,add_eq_def]>>every_case_tac>>simp[]
QED

Theorem has_eq_add_ge[simp]:
  has_eq X n (add_ge Y m ec) ⇔
  has_eq X n ec
Proof
  rw[has_eq_def,add_ge_def]>>every_case_tac>>simp[]
QED

Type ciconstraint[pp] = ``:(mlstring, mlstring avar) iconstraint``
Type ann_ciconstraint[pp] = ``:mlstring option # (mlstring, mlstring avar) iconstraint``

Definition format_varc_def:
  format_varc X =
  case X of
    INL s => strlit"v" ^ s
  | INR i => strlit"i" ^ int_to_string #"-" i
End

Definition format_reif_def:
  format_reif pref X i =
  concat[strlit"i[";format_varc X;strlit"][";pref;
    int_to_string #"-" i;strlit"]"]
End

(* Name of a reification *)
Definition enc_reif_def:
  enc_reif reif =
  case reif of
    Ge X i => format_reif (strlit"ge") X i
  | Eq X i => format_reif (strlit"eq") X i
End

(* Tool for sticking on annotations *)
Definition mk_annotate_def:
  (mk_annotate (_:mlstring list) ([]:ciconstraint list) = []) ∧
  (mk_annotate (x::xs) (y::ys) =
    (SOME x,y)::mk_annotate xs ys) ∧
  (mk_annotate [] ys =
    MAP (λy. (NONE,y)) ys)
End

(* TODO: what annotation should we use? *)
Definition cencode_ge_def:
  cencode_ge bnd Y n ec =
  if has_ge Y n ec
  then (Nil, ec)
  else
    let ec = add_ge Y n ec in
    let fmt = format_reif (strlit "ge") Y n in
    (List (
      mk_annotate [
        fmt ^ strlit"[f]";
        fmt ^ strlit"[r]"
      ]
      (encode_ge bnd Y n)), ec)
End

Definition cencode_eq_def:
  cencode_eq bnd Y n ec =
  if has_eq Y n ec
  then (Nil, ec)
  else
    let ec = add_eq Y n ec in
    let fmt = format_reif (strlit "eq") Y n in
    (List (
      mk_annotate [
        fmt ^ strlit"[f]";
        fmt ^ strlit"[r]"
      ]
      (encode_eq bnd Y n)), ec)
End

Definition cencode_full_eq_def:
  cencode_full_eq bnd Y n ec =
  let
    (x1,ec') = cencode_ge bnd Y n ec;
    (x2,ec'') = cencode_ge bnd Y (n+1) ec';
    (x3,ec''') = cencode_eq bnd Y n ec''
  in
    (Append x1 (Append x2 x3), ec''')
End

(* TODO: lemmas *)
Theorem iSUM_FILTER:
  iSUM (MAP (b2i o P) ls) = &(LENGTH $ FILTER P ls)
Proof
  Induct_on ‘ls’>>
  rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_b2i_bound:
  0 ≤ iSUM (MAP (λp. b2i (f p)) ls) ∧
  iSUM (MAP (λp. b2i (f p)) ls) ≤ &LENGTH ls
Proof
  Induct_on`ls`>>rw[iSUM_def,oneline b2i_def]>>
  intLib.ARITH_TAC
QED

Theorem add_ge_flip[local]:
  (a + x ≥ y ⇔
  y - (a:int) ≤ x)
Proof
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_b2i_ge_1[simp]:
  ∀ls.
  iSUM (MAP (λp. b2i (f p)) ls) ≥ 1 ⇔
  ∃x. MEM x ls ∧ f x
Proof
  Induct_on`ls`>>
  rw[iSUM_def]>>
  rw[Once (oneline b2i_def)]
  >- (
    simp[add_ge_flip]>>
    metis_tac[iSUM_MAP_b2i_bound])>>
  metis_tac[]
QED

Theorem iSUM_MAP_b2i_ge_LENGTH[simp]:
  ∀ls.
  iSUM (MAP (λp. b2i (f p)) ls) ≥ &LENGTH ls ⇔
  (∀x. MEM x ls ⇒ f x)
Proof
  Induct_on`ls`>>
  rw[iSUM_def]>>
  rw[Once (oneline b2i_def)]
  >- (
    fs[add_ge_flip,ADD1,integerTheory.int_ge]>>
    simp[GSYM integerTheory.INT_ADD,int_arithTheory.elim_minus_ones]>>
    metis_tac[])>>
  assume_tac iSUM_MAP_b2i_bound>>
  simp[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Definition false_constr_def:
  false_constr = (([], [], 1i):ciconstraint)
End

Theorem iconstraint_sem_false_constr[simp]:
  ¬iconstraint_sem false_constr w
Proof
  Cases_on`w`>>EVAL_TAC
QED

Definition cfalse_constr_def:
  cfalse_constr = (SOME (strlit"BAD INPUT"), false_constr)
End

Theorem enc_rel_cfalse_constr[simp]:
  enc_rel wi (List [cfalse_constr]) [false_constr] ec ec
Proof
  rw[enc_rel_def,cfalse_constr_def]
QED

Theorem enc_rel_List_refl_1:
  enc_rel wi (List [(ann,c)]) [c] ec ec
Proof
  rw[enc_rel_def]
QED

Definition init_ec_def:
  init_ec = <| ge := [] ; eq := [] |>
End

