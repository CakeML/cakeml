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
  | Ge ('a varc) int
    (* Reifies X ≥ i *)
  | Eq ('a varc) int (* Reifies X = i *)
End

Definition reify_reif_def:
  reify_reif wi reif ⇔
  case reif of
    Ge X i => varc wi X ≥ i
  | Eq X i => varc wi X = i
End

(* The datatype for flags in the ILP encoding.
  Each flag comes with a (separate) name for
    the constraint it belongs to.
  The (name,flag) pair variables are printed as:
  c[name](flag format...)
*)
Datatype:
  flag =
  | Indices (num list) (mlstring option)
    (* [i][n1][n2]...[optional string] *)
  | Flag mlstring
    (* b[name][annotated mlstring] *)
  | Values (int list) (mlstring option)
    (* [v][i1][i2]...[optional string] *)
End

Overload Index = ``λname n. (name,Indices [n] NONE)``;

Definition reify_flag_def:
  reify_flag cs wi (name,flag) ⇔
  case flag of
  | Indices ids ann =>
    (case ALOOKUP cs name of
    | SOME (Counting (AllDifferent Xs)) =>
      varc wi (EL (EL 0 ids) Xs) > varc wi (EL (EL 1 ids) Xs)
    | SOME (Counting (Count Xs Y _)) =>
      if ann = SOME (strlit"ge")
      then varc wi (EL (HD ids) Xs) ≥ varc wi Y
      else if ann = SOME (strlit"le")
      then varc wi (EL (HD ids) Xs) ≤ varc wi Y
      else varc wi (EL (HD ids) Xs) = varc wi Y
    | SOME (Counting (Among Xs iS _)) =>
      if ann = SOME (strlit"ge")
      then varc wi (EL (EL 0 ids) Xs) ≥ EL (EL 1 ids) iS
      else if ann = SOME (strlit"le")
      then varc wi (EL (EL 0 ids) Xs) ≤ EL (EL 1 ids) iS
      else if ann = SOME (strlit"eq")
      then varc wi (EL (EL 0 ids) Xs) = EL (EL 1 ids) iS
      else MEM (varc wi (EL (HD ids) Xs)) iS (* ann = SOME (strlit"fnd") *)
    | SOME (Extensional (Table tss Xs)) =>
      match_row (EL (HD ids) tss) (MAP (varc wi) Xs))
  | Flag ann =>
    (case ALOOKUP cs name of
    | SOME (Prim (Cmpop _ _ X Y)) =>
      if ann = strlit"lt"
      then varc wi X < varc wi Y
      else varc wi X > varc wi Y
    | SOME (Prim (Binop _ X Y Z)) =>
      if ann = strlit"lle"
      then varc wi X ≤ varc wi Z
      else if ann = strlit"rle"
      then varc wi Y ≤ varc wi Z
      else if ann = strlit"lge"
      then varc wi X ≥ varc wi Z
      else varc wi Y ≥ varc wi Z)
  | Values vs ann =>
    (case ALOOKUP cs name of
    | SOME (Counting (NValue Xs Y)) =>
      MEM (HD vs) $ MAP (varc wi) Xs)
End

Definition format_varc_def:
  format_varc X =
  case X of
    INL s => strlit"i[" ^ s ^ strlit "]"
  | INR i => strlit"n[" ^ int_to_string #"-" i ^ strlit"]"
End

Definition format_reif_def:
  format_reif reif =
  case reif of
    Ge X i =>
    concat[format_varc X;strlit"[ge";
      int_to_string #"-" i;strlit"]"]
  | Eq X i =>
    concat[format_varc X;strlit"[eq";
      int_to_string #"-" i;strlit"]"]
End

Definition format_annot_def:
  (format_annot NONE = strlit"") ∧
  (format_annot (SOME s) = strlit"[" ^ s ^ strlit"]")
End

Definition format_num_list_def:
  format_num_list (ls:num list) = concatWith (strlit"_") (MAP toString ls)
End

Definition format_int_list_def:
  format_int_list (ls:int list) = concatWith (strlit"_") (MAP (int_to_string #"-") ls)
End

Definition format_flag_def:
  format_flag (name,flag) =
  case flag of
    Flag ann =>
      strlit"b[" ^ name ^ strlit"][" ^ ann ^ strlit "]"
  | Indices ns annot =>
      strlit"x[" ^ name ^ strlit"][" ^ format_num_list ns ^ strlit"]" ^ format_annot annot
  | Values ns annot =>
      strlit"v[" ^ name ^ strlit"][" ^ format_int_list ns ^ strlit"]" ^ format_annot annot
End

Definition format_var_def:
  format_var v =
  case v of
    INL y => format_reif y
  | INR z => format_flag z
End

(*
  We first design and prove sound the
  abstract encodings into the Boolean variable type:
    ('a reif + flag)
*)
Type avar[pp] = ``:('a reif + (mlstring # flag))``
Type aiconstraint[pp] = ``:('a, 'a avar) iconstraint``

Definition reify_avar_def:
  reify_avar cs wi eb ⇔
  case eb of
    INL reif => reify_reif wi reif
  | INR nflag => reify_flag cs wi nflag
End

(***
  Helper encoding functions
***)

(* Encoding a single variable X_{>=i} ⇔ X ≥ i *)
Definition encode_ge_aux_def:
  encode_ge_aux Xi i =
    case Xi of
      INL X => ([(1,X)],[],i)
    | INR v => ([],[],1 - b2i (v ≥ i))
End

Definition encode_ge_def:
  encode_ge (bnd:'a bounds) (Xi:'a varc) i =
  bimply_bit bnd (Pos (INL (Ge Xi i)))
    (encode_ge_aux Xi i)
End

Theorem encode_ge_aux_sem[simp]:
  iconstraint_sem (encode_ge_aux X n) (wi,wb) ⇔ varc wi X ≥ n
Proof
  rw[encode_ge_aux_def]>>
  TOP_CASE_TAC>>
  simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def]>>
  rw[b2i_alt]
QED

Theorem encode_ge_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (INL (Ge X i)) ⇔ varc wi X ≥ i)
Proof
  rw[encode_ge_def]>>
  metis_tac[]
QED

(* Encoding a single variable X = i, separate from encode_ge
  X_{=i} ⇔ X_{>=i} ∧ ~X_{>=i+1}
*)
Definition encode_eq_aux_def:
  encode_eq_aux X i =
    ([],[(1,Pos(INL (Ge X i)));(1, Neg (INL (Ge X (i+1))))],2)
End

Definition encode_eq_def:
  encode_eq bnd X i =
  (bimply_bit bnd (Pos (INL (Eq X i)))
    (encode_eq_aux X i))
End

Theorem encode_eq_aux_sem[simp]:
  iconstraint_sem (encode_eq_aux X n) (wi,wb) ⇔
    wb (INL (Ge X n)) ∧
    ¬wb (INL (Ge X (n+1)))
Proof
  rw[encode_eq_aux_def]>>
  gs[iconstraint_sem_def,b2i_alt]>>
  rw[]
QED

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
  rename1`(_ ⇔ v) ⇔ _`>>
  Cases_on`v`>>rw[]>>
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

(* the two named equality constraints, held as a list *)
Definition mk_ge_def[simp]:
  mk_ge X Y = mk_constraint_ge 1 (X) (-1) (Y) 0
End

Definition mk_le_def[simp]:
  mk_le X Y = mk_ge Y X
End

(* For gt and lt, we'll have many different names for them *)
Definition mk_gt_def[simp]:
  mk_gt X Y = mk_constraint_ge 1 X (-1) Y 1
End

Definition mk_lt_def[simp]:
  mk_lt X Y = mk_gt Y X
End

Definition split_iclin_term_def:
  (split_iclin_term ([]:'a iclin_term)
    (acc:'a ilin_term) rhs = (acc,rhs)) ∧
  (split_iclin_term ((c,X)::xs) acc rhs =
    case X of
      INL v => split_iclin_term xs ((c,v)::acc) rhs
    | INR cc =>
      split_iclin_term xs acc (rhs - c * cc))
End

Theorem split_iclin_term_sound:
  ∀Xs rhs acc xs rhs'.
    split_iclin_term Xs acc rhs = (xs,rhs') ⇒
    eval_iclin_term wi Xs + eval_ilin_term wi acc - rhs =
    eval_ilin_term wi xs - rhs'
Proof
  Induct
  >-simp[split_iclin_term_def, eval_iclin_term_def, eval_ilin_term_def, iSUM_def]
  >-(
    Cases>>
    Cases_on ‘r’>>
    rw[split_iclin_term_def]>>
    last_x_assum $ drule_then mp_tac>>
    rw[eval_iclin_term_def, eval_ilin_term_def, iSUM_def, varc_def]>>
    intLib.ARITH_TAC)
QED

(*
  Helper functions for bit implications, but we
    specialize with annotations and only use a single bit
*)
Definition cimply_var_def:
  cimply_var bnd x cc =
  List
  [(SOME (format_var x ^ strlit "[f]"),
    (imply_bit bnd (Pos x) cc))]
End

Definition cvar_imply_def:
  cvar_imply bnd x cc =
  List
  [(SOME (format_var x ^ strlit "[r]"),
    (bits_imply bnd [Pos x] cc))]
End

Definition cnvar_imply_def:
  cnvar_imply bnd x cc =
  List
  [(SOME (format_var x ^ strlit "[nr]"),
    (bits_imply bnd [Neg x] cc))]
End

Definition cbimply_var_def:
  cbimply_var bnd x cc =
  let fmt = format_var x in
  List
  [(SOME (fmt ^ strlit "[f]"),
    (imply_bit bnd (Pos x) cc));
   (SOME (fmt ^ strlit "[r]"),
    (bits_imply bnd [Pos x] cc))]
End

(*
  General setup for problem encodings from
  mlstring-variabled CP constraints.

  mlstring constraint

  into

  (mlstring option # (mlstring, mlstring avar) iconstraint)

  The mlstring option is an annotation.
*)

(* TODO: replace ge/eq trackers with faster representations. *)
Datatype:
  enc_conf =
    <|
       ge : ( (mlstring varc) # int list) list
     ; eq : ( (mlstring varc) # int list) list
    |>
End

(***
  (Mostly) semantic tools
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
  (∀Y n. has_eq Y n ec ⇒ (wb (INL (Eq Y n)) ⇔
    wb (INL (Ge Y n)) ∧ ¬wb (INL (Ge Y (n + 1)))))
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

Theorem enc_rel_Nil[simp]:
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

Definition fold_cenc_def:
  (fold_cenc cenc [] ec = (Nil,ec)) ∧
  (fold_cenc cenc (x::xs) ec =
    let (ys,ec') = cenc x ec in
    let (yss,ec'') = fold_cenc cenc xs ec' in
    (Append ys yss, ec''))
End

Theorem enc_rel_fold_cenc:
  (∀h ec ys ec'.
    cf h ec = (ys, ec') ⇒
    enc_rel wi ys (f h) ec ec') ⇒
  ∀ls ec ys ec'.
  fold_cenc cf ls ec = (ys,ec') ⇒
  enc_rel wi ys
    (FLAT (MAP f ls)) ec ec'
Proof
  strip_tac>>
  Induct>>rw[fold_cenc_def]>>
  gvs[UNCURRY_EQ]>>
  metis_tac[enc_rel_Append]
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

(* Tool for sticking on annotations *)
Definition mk_annotate_def:
  (mk_annotate (_:mlstring list) ([]:ciconstraint list) = []) ∧
  (mk_annotate (x::xs) (y::ys) =
    (SOME x,y)::mk_annotate xs ys) ∧
  (mk_annotate [] ys =
    MAP (λy. (NONE,y)) ys)
End

Definition cencode_ge_def:
  cencode_ge bnd Y n ec =
  if has_ge Y n ec
  then (Nil, ec)
  else
    let ec = add_ge Y n ec in
    (cbimply_var bnd (INL (Ge Y n)) (encode_ge_aux Y n),ec)
End

Definition cencode_eq_def:
  cencode_eq bnd Y n ec =
  if has_eq Y n ec
  then (Nil, ec)
  else
    let ec = add_eq Y n ec in
    (cbimply_var bnd (INL (Eq Y n)) (encode_eq_aux Y n),ec)
End

Definition cencode_full_eq_def:
  cencode_full_eq bnd Y n ec =
  let
    (x1,ec') = cencode_ge bnd Y n ec;
    (x2,ec'') = cencode_ge bnd Y (n+1) ec';
    (x3,ec''') = cencode_eq bnd Y n ec''
  in
    (Append (Append x1 x2) x3, ec''')
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

(* domain of X given by bnd (as a list) *)
Definition domlist_def:
  domlist bnd (X:'a varc) =
  case X of
    INL vX =>
      (let
        (lb, ub) = bnd vX
      in
        if ub < lb
        then []
        else GENLIST (λn. &n + lb) (Num (ub - lb) + 1))
  | INR cX => [cX]
End

Theorem MEM_domlist:
  valid_assignment bnd wi ⇒
  MEM (varc wi X) (domlist bnd X)
Proof
  Cases_on ‘X’>>
  rw[domlist_def,valid_assignment_def,varc_def]>>
  rename1 ‘bnd x’>>
  Cases_on ‘bnd x’>>
  rw[MEM_GENLIST]>>
  res_tac
  >-intLib.ARITH_TAC>>
  qexists ‘Num (wi x - q)’>>
  intLib.ARITH_TAC
QED

(* bijection 0, -1, 1, -2, 2,... ⇔ 0, 1, 2, 3, 4,... and its inverse next *)
Definition intnum_def:
  intnum (n: int) =
  if n < 0 then 2 * Num (-n) - 1
  else 2 * Num n
End

Definition numint_def:
  numint (n: num): int =
  if EVEN n then &((n + 1) DIV 2)
  else -&((n + 1) DIV 2)
End

Theorem numint_inj:
  numint m = numint n ⇒ m = n
Proof
  simp[numint_def]>>
  intLib.ARITH_TAC
QED

Theorem numint_intnum:
  numint (intnum x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Theorem intnum_numint:
  intnum (numint x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Definition numset_to_intlist_def:
  numset_to_intlist t = MAP (numint o FST) $ toSortedAList t
End

Theorem ALL_DISTINCT_numset_to_intlist:
  ALL_DISTINCT $ numset_to_intlist t
Proof
  simp[numset_to_intlist_def,GSYM MAP_MAP_o]>>
  irule ALL_DISTINCT_MAP_INJ>>
  simp[ALL_DISTINCT_MAP_FST_toSortedAList,numint_inj]
QED

(* Union of all int values in domains of Xs *)
Definition union_dom_def:
  union_dom bnd Xs =
  numset_to_intlist $ FOLDL union LN $
    MAP (λX. list_to_num_set $ MAP intnum $ domlist bnd X) Xs
End

Theorem MEM_numset_to_intlist:
  MEM x (numset_to_intlist ns) ⇔
  intnum x ∈ domain ns
Proof
  rw[numset_to_intlist_def,GSYM MAP_MAP_o,MEM_MAP,EXISTS_PROD,
    MEM_toSortedAList,domain_lookup]>>
  metis_tac[intnum_numint,numint_intnum]
QED

Theorem domain_FOLDL_union:
  ∀ls t.
  x ∈ domain (FOLDL union t ls) ⇔
  x ∈ domain t ∨ ∃ns. ns ∈ set ls ∧ x ∈ domain ns
Proof
  Induct>>rw[]>>
  metis_tac[]
QED

Theorem EVERY_MEM_union_dom:
  valid_assignment bnd wi ⇒
  EVERY (λX. MEM (varc wi X) (union_dom bnd Xs)) Xs
Proof
  rw[EVERY_MEM,union_dom_def,MEM_numset_to_intlist,domain_FOLDL_union]>>
  simp[MEM_MAP,PULL_EXISTS,domain_list_to_num_set]>>
  metis_tac[MEM_domlist]
QED

Theorem ALL_DISTINCT_union_dom:
  ALL_DISTINCT $ union_dom bnd Xs
Proof
  simp[union_dom_def,ALL_DISTINCT_numset_to_intlist]
QED

Definition false_constr_def:
  false_constr = (([], [], 1i):ciconstraint)
End

Definition cfalse_constr_def:
  cfalse_constr = (List [(SOME (strlit"BAD INPUT"), false_constr)])
End

Theorem iconstraint_sem_false_constr[simp]:
  ¬iconstraint_sem false_constr w
Proof
  Cases_on`w`>>EVAL_TAC
QED

Theorem enc_rel_cfalse_constr[simp]:
  enc_rel wi cfalse_constr [false_constr] ec ec
Proof
  rw[enc_rel_def,cfalse_constr_def]
QED

Theorem enc_rel_List_refl_1:
  enc_rel wi (List [(ann,c)]) [c] ec ec
Proof
  rw[enc_rel_def]
QED

Theorem EVERY_SND_mk_annotate[simp]:
  ∀ann ls.
  EVERY (λx. iconstraint_sem (SND x) (wi,wb)) (mk_annotate ann ls) ⇔
  EVERY (λx. iconstraint_sem x (wi,wb)) ls
Proof
  ho_match_mp_tac mk_annotate_ind>>
  rw[mk_annotate_def]>>
  simp[EVERY_MAP]
QED

Theorem enc_rel_List_mk_annotate:
  enc_rel wi (List (mk_annotate ann ls)) ls ec ec
Proof
  rw[enc_rel_def]
QED

Overload abstr = ``\ls. MAP SND (append ls)``;
Overload abstrl = ``\ls. MAP SND ls``;

Definition cimply_var_n_def:
  cimply_var_n bnd x cc n =
  List
  [(SOME (format_var x ^ strlit "[f][" ^ n ^ strlit"]"),
    (imply_bit bnd (Pos x) cc))]
End

Theorem abstr_cimply_var[simp]:
  abstr (cimply_var bnd v c) =
  [imply_bit bnd (Pos v) c]
Proof
  rw[cimply_var_def]
QED

Theorem abstr_cimply_var_n[simp]:
  abstr (cimply_var_n bnd v c n) =
  [imply_bit bnd (Pos v) c]
Proof
  rw[cimply_var_n_def]
QED

Theorem abstr_cbimply_var[simp]:
  abstr (cbimply_var bnd v c) =
  REVERSE (bimply_bit bnd (Pos v) c)
Proof
  rw[cbimply_var_def,bimply_bit_def]
QED

Theorem abstr_cvar_imply[simp]:
  abstr (cvar_imply bnd v c) =
  [bits_imply bnd [Pos v] c]
Proof
  rw[cvar_imply_def]
QED

Theorem abstr_cnvar_imply[simp]:
  abstr (cnvar_imply bnd v c) =
  [bits_imply bnd [Neg v] c]
Proof
  rw[cnvar_imply_def]
QED

Theorem EVERY_SND:
  EVERY (\x. f (SND x)) ls =
  EVERY (\x. f x) (MAP SND ls)
Proof
  rw[EVERY_MAP]
QED

Theorem enc_rel_encode_ge:
  valid_assignment bnd wi ∧
  cencode_ge bnd X t ec = (x1,ec') ⇒
  enc_rel wi x1 (encode_ge bnd X t) ec ec'
Proof
  rw[cencode_ge_def]
  >-
    rw[enc_rel_def,good_reif_def]>>
  rw[enc_rel_def,good_reif_def]>>
  gvs[EVERY_SND]>>
  metis_tac[]
QED

Theorem enc_rel_encode_eq:
  valid_assignment bnd wi ∧
  cencode_eq bnd X t ec = (x1,ec') ⇒
  enc_rel wi x1 (encode_eq bnd X t) ec ec'
Proof
  rw[cencode_eq_def]
  >- (
    rw[enc_rel_def,good_reif_def]>>
    simp[encode_eq_def,iconstraint_sem_def])>>
  rw[enc_rel_def,good_reif_def]>>
  gs[EVERY_SND,encode_eq_sem]>>
  simp[encode_eq_def,iconstraint_sem_def]
QED

Theorem enc_rel_encode_full_eq:
  valid_assignment bnd wi ∧
  cencode_full_eq bnd X t ec = (x1,ec') ⇒
  enc_rel wi x1 (encode_full_eq bnd X t) ec ec'
Proof
  rw[cencode_full_eq_def,encode_full_eq_def]>>
  gvs[UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_eq>>
  simp[]>> first_x_assum $ irule_at Any>>
  irule enc_rel_Append>>
  metis_tac[enc_rel_encode_ge]
QED

Definition init_ec_def:
  init_ec = <| ge := [] ; eq := [] |>
End

Theorem enc_rel_abstr[simp]:
  enc_rel wi ls (abstr ls) ec ec
Proof
  rw[enc_rel_def,EVERY_MAP]
QED

Definition mk_name_def:
  mk_name name tag =
  strlit"c[" ^ name ^ strlit "][" ^ tag ^ strlit"]"
End

Theorem enc_rel_List_refl_mul:
  set ls' = set $ (abstrl ls) ⇒
  enc_rel wi (List ls) ls' ec ec
Proof
  rw[enc_rel_def]>>
  fs[EVERY_MEM,EXTENSION,MEM_MAP]>>
  metis_tac[]
QED

Theorem enc_rel_abstr_cong:
  set ls' = set $ (abstr ls) ⇒
  enc_rel wi ls ls' ec ec
Proof
  rw[enc_rel_def]>>
  fs[EVERY_MEM,EXTENSION,MEM_MAP]>>
  metis_tac[]
QED

(* at least one over literals.
  We define the raw version and abstract over it. *)
Definition at_least_one_def:
  at_least_one ls = ([], MAP (λl. (1,l)) ls, 1)
End

Definition cat_least_one_def:
  cat_least_one name ls =
    List [
      (SOME (mk_name name (strlit "al1")),
        at_least_one ls)]
End

Theorem at_least_one_sem[simp]:
  iconstraint_sem (at_least_one ls) (wi,wb) ⇔
  ∃l. MEM l ls ∧ lit wb l
Proof
  rw[iconstraint_sem_def,at_least_one_def,eval_lin_term_def]>>
  simp[MAP_MAP_o,o_DEF]
QED

Theorem abstr_cat_least_one[simp]:
  abstr (cat_least_one name ls) = [at_least_one ls]
Proof
  rw[cat_least_one_def]
QED

(* encodes (sum of the bitlist Bs) = Y *)
Definition encode_bitsum_def:
  encode_bitsum Bs Y =
  case Y of
    INL vY => [
      ([(-1i, vY)], MAP (λb. (1i, Pos b)) Bs, 0i);
      ([(1i, vY)], MAP (λb. (-1i, Pos b)) Bs, 0i)]
  | INR cY => [
      ([], MAP (λb. (1i, Pos b)) Bs, cY);
      ([], MAP (λb. (-1i, Pos b)) Bs, -cY)]
End

Theorem iSUM_MAP_lin:
  ∀ls a f b. iSUM (MAP (λx. a * f x + b) ls) = a * iSUM (MAP (λx. f x) ls) + b * &LENGTH ls
Proof
  Induct>>
  simp[iSUM_def,MAP,LENGTH]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_lin_const = iSUM_MAP_lin |> CONV_RULE (RESORT_FORALL_CONV List.rev) |> Q.SPEC `0` |> SRULE [] |> SPEC_ALL;

Theorem encode_bitsum_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_bitsum Bs Y) ⇔
  iSUM $ MAP (b2i o wb) Bs = varc wi Y)
Proof
  rw[encode_bitsum_def]>>
  CASE_TAC>>
  simp[varc_def,iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
    eval_iterm_def,eval_term_def,iSUM_def,MAP_MAP_o,combinTheory.o_ABS_R,
    iSUM_MAP_lin_const]>>
  simp[GSYM combinTheory.o_ABS_R,GSYM combinTheory.I_EQ_IDABS]>>
  intLib.ARITH_TAC
QED

Definition cencode_bitsum_def:
  cencode_bitsum Bs Y name =
  List
    (mk_annotate
      [mk_name name (strlit"ge"); mk_name name (strlit"le")]
      (encode_bitsum Bs Y)
    )
End

Theorem enc_rel_cencode_bitsum[simp]:
  enc_rel wi (cencode_bitsum Bs Y name) (encode_bitsum Bs Y) ec ec
Proof
  rw[cencode_bitsum_def,encode_bitsum_def]>>
  Cases_on ‘Y’>>
  simp[enc_rel_List_mk_annotate]
QED

(* Flatten a list of app lists *)
Definition flat_app_def:
  flat_app ls = FOLDR Append Nil ls
End

Theorem abstr_flat_app[simp]:
  abstr (flat_app ls) =
    FLAT (MAP abstr ls)
Proof
  `∀acc. abstr (FOLDR Append acc ls) = FLAT (MAP abstr ls) ++ abstr acc` by
    (Induct_on`ls`>>rw[flat_app_def])>>
  simp[flat_app_def]
QED

Theorem abstrl_mk_annotate[simp]:
  ∀ls ys.
  abstrl (mk_annotate ls ys) = ys
Proof
  ho_match_mp_tac mk_annotate_ind>>
  rw[mk_annotate_def]>>
  simp[MAP_MAP_o,o_DEF]
QED

Theorem abstr_cencode_bitsum[simp]:
  abstr (cencode_bitsum Bs Y name) = encode_bitsum Bs Y
Proof
  rw[cencode_bitsum_def]
QED

