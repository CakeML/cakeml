(*
  Formalization of the CP to ILP phase (lexicographical constraints)
*)
Theory cp_to_ilp_lexicographical
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp int_bitwiseExtra

(* First i elements equal (starts from 0, which is redundant *)
Definition pref_eq_def[simp]:
  pref_eq name (i:num) =
    INR (name, Indices [i] (SOME «pref»))
End

(* x > y decision at pos i (0-indexed) *)
Definition dec_at_def[simp]:
  dec_at name (i:num) =
    INR (name, Indices [i] (SOME «dec»))
End

(* x < y decision at pos i (0-indexed) *)
Definition inc_at_def[simp]:
  inc_at name (i:num) =
    INR (name, Indices [i] (SOME «inc»))
End

(* Prefix downwards chain for n elements, e.g.,
  conds & pref_eq [2] --> pref_eq [1]
  conds & pref_eq [3] --> pref_eq [2]
  conds & pref_eq [4] --> pref_eq [3]
  The conds are extra bits passed in. *)
Definition pref_imp_pref_def:
  pref_imp_pref bnd name conds n =
  List (GENLIST (λi.
    (SOME (mk_name name (toString i ^ «pp»)),
    bits_imply bnd (Pos (pref_eq name (i+2))::conds)
      ([],[(1,Pos (pref_eq name (i+1)))],1))) (n-1))
End

(* Prefix equal at i implies vars equal at i;
  assumes xs ys are truncated to the same length *)
Definition pref_imp_eq_def:
  pref_imp_eq bnd name conds xs ys =
  flat_app
  (MAPi (λi (x,y).
    List [(SOME (mk_name name (toString i ^ «pge»)),
        bits_imply bnd (Pos (pref_eq name (i+1))::conds) (mk_ge x y));
     (SOME (mk_name name (toString i ^ «ple»)),
        bits_imply bnd (Pos (pref_eq name (i+1))::conds) (mk_le x y));]
  ) (ZIP(xs,ys)))
End

(* Decision implies equal on the prefix, e.g.
  dec_at [2] --> pref_eq[2] *)
Definition dec_imp_pref_def:
  dec_imp_pref bnd name conds n =
  List (GENLIST (λi.
    (SOME (mk_name name (toString i ^ «dp»)),
    bits_imply bnd (Pos (dec_at name (i+1))::conds)
      ([],[(1,Pos (pref_eq name (i+1)))],1))) (n-1))
End

Definition inc_imp_pref_def:
  inc_imp_pref bnd name conds n =
  List (GENLIST (λi.
    (SOME (mk_name name (toString i ^ «ip»)),
    bits_imply bnd (Pos (inc_at name (i+1))::conds)
      ([],[(1,Pos (pref_eq name (i+1)))],1))) (n-1))
End

(* Decision implies vars > at i;
  assumes xs ys are truncated to the same length *)
Definition dec_imp_gt_def:
  dec_imp_gt bnd name conds xs ys =
  List (MAPi (λi (x,y).
     (SOME (mk_name name (toString i ^ «pge»)),
        bits_imply bnd (Pos (dec_at name i)::conds) (mk_gt x y))
  ) (ZIP(xs,ys)))
End

(* same, but for < *)
Definition inc_imp_lt_def:
  inc_imp_lt bnd name conds xs ys =
  List (MAPi (λi (x,y).
     (SOME (mk_name name (toString i ^ «pge»)),
        bits_imply bnd (Pos (inc_at name i)::conds) (mk_lt x y))
  ) (ZIP(xs,ys)))
End

Definition mk_lex_gte_al1_def:
  mk_lex_gte_al1 bnd name conds (lx:num) (ly:num) n eq =
  List [(SOME (mk_name name «al1»),
    bits_imply bnd conds
    (at_least_one
    (if lx > ly ∨ eq ∧ lx = ly then
      Pos (pref_eq name n)::
        (GENLIST (λi. Pos (dec_at name i)) n)
    else
        GENLIST (λi. Pos (dec_at name i)) n)))]
End

(* Encodes lex> or lex>= *)
Definition lex_gte_def:
  lex_gte bnd name conds Xs Ys eq =
  let
    lx = LENGTH Xs;
    ly = LENGTH Ys;
    n = MIN lx ly;
    xss = TAKE n Xs;
    yss = TAKE n Ys;
  in
    Append (pref_imp_pref bnd name conds n)
    (Append (pref_imp_eq bnd name conds xss yss)
    (Append (dec_imp_pref bnd name conds n)
    (Append (dec_imp_gt bnd name conds xss yss)
      (mk_lex_gte_al1 bnd name conds lx ly n eq ))))
End

Definition mk_lex_lte_al1_def:
  mk_lex_lte_al1 bnd name conds (lx:num) (ly:num) n eq =
  List [(SOME (mk_name name «al1»),
    bits_imply bnd conds
    (at_least_one
    (if lx < ly ∨ eq ∧ lx = ly then
      Pos (pref_eq name n)::
        (GENLIST (λi. Pos (inc_at name i)) n)
    else
        GENLIST (λi. Pos (inc_at name i)) n)))]
End

(* Encodes lex< or lex<= *)
Definition lex_lte_def:
  lex_lte bnd name conds Xs Ys eq =
  let
    lx = LENGTH Xs;
    ly = LENGTH Ys;
    n = MIN lx ly;
    xss = TAKE n Xs;
    yss = TAKE n Ys;
  in
    Append (pref_imp_pref bnd name conds n)
    (Append (pref_imp_eq bnd name conds xss yss)
    (Append (inc_imp_pref bnd name conds n)
    (Append (inc_imp_lt bnd name conds xss yss)
      (mk_lex_lte_al1 bnd name conds lx ly n eq ))))
End

Theorem b2i_ge_1[local]:
  b2i b ≥ 1 <=> b
Proof
  rw[oneline b2i_def]
QED

Theorem pref_imp_pref_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (pref_imp_pref bnd name conds n)) ⇔
  ∀i. i < n - 1 ⇒
    (EVERY (lit wb) conds ∧ wb (pref_eq name (i+2)) ⇒
      wb (pref_eq name (i+1))))
Proof
  rw[pref_imp_pref_def,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS]>>
  simp[iconstraint_sem_def,b2i_ge_1]>>
  metis_tac[]
QED

Theorem pref_imp_eq_sem:
  valid_assignment bnd wi ∧
  n ≤ LENGTH Xs ∧ n ≤ LENGTH Ys ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (pref_imp_eq bnd name conds (TAKE n Xs) (TAKE n Ys))) ⇔
  ∀i. i < n ⇒
    (EVERY (lit wb) conds ∧ wb (pref_eq name (i+1)) ⇒
      varc wi (EL i Xs) = varc wi (EL i Ys)))
Proof
  strip_tac>>
  simp[pref_imp_eq_def,EVERY_MEM,MEM_FLAT,MEM_MAPi,PULL_EXISTS,LENGTH_TAKE]>>
  eq_tac>>rw[]>>first_x_assum drule>>
  gvs[EL_ZIP, SF DNF_ss,EL_TAKE]>>
  rw[]>>gvs[EVERY_MEM]>>
  intLib.ARITH_TAC
QED

Theorem dec_imp_pref_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (dec_imp_pref bnd name conds n)) ⇔
  ∀i. i < n - 1 ⇒
    (EVERY (lit wb) conds ∧ wb (dec_at name (i+1)) ⇒
      wb (pref_eq name (i+1))))
Proof
  rw[dec_imp_pref_def,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS]>>
  simp[iconstraint_sem_def,b2i_ge_1]>>
  metis_tac[]
QED

Theorem dec_imp_gt_sem:
  valid_assignment bnd wi ∧
  n ≤ LENGTH Xs ∧ n ≤ LENGTH Ys ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (dec_imp_gt bnd name conds (TAKE n Xs) (TAKE n Ys))) ⇔
  ∀i. i < n ⇒
    (EVERY (lit wb) conds ∧ wb (dec_at name i) ⇒
      varc wi (EL i Xs) > varc wi (EL i Ys)))
Proof
  strip_tac>>
  simp[dec_imp_gt_def,EVERY_MEM,MEM_FLAT,MEM_MAPi,PULL_EXISTS,LENGTH_TAKE]>>
  eq_tac>>rw[]>>first_x_assum drule>>
  gvs[EL_ZIP, SF DNF_ss,EL_TAKE]>>
  rw[]>>gvs[EVERY_MEM]>>
  intLib.ARITH_TAC
QED

Theorem inc_imp_pref_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (inc_imp_pref bnd name conds n)) ⇔
  ∀i. i < n - 1 ⇒
    (EVERY (lit wb) conds ∧ wb (inc_at name (i+1)) ⇒
      wb (pref_eq name (i+1))))
Proof
  rw[inc_imp_pref_def,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS]>>
  simp[iconstraint_sem_def,b2i_ge_1]>>
  metis_tac[]
QED

Theorem inc_imp_lt_sem:
  valid_assignment bnd wi ∧
  n ≤ LENGTH Xs ∧ n ≤ LENGTH Ys ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (inc_imp_lt bnd name conds (TAKE n Xs) (TAKE n Ys))) ⇔
  ∀i. i < n ⇒
    (EVERY (lit wb) conds ∧ wb (inc_at name i) ⇒
      varc wi (EL i Xs) < varc wi (EL i Ys)))
Proof
  strip_tac>>
  simp[inc_imp_lt_def,EVERY_MEM,MEM_FLAT,MEM_MAPi,PULL_EXISTS,LENGTH_TAKE]>>
  eq_tac>>rw[]>>first_x_assum drule>>
  gvs[EL_ZIP, SF DNF_ss,EL_TAKE]>>
  rw[]>>gvs[EVERY_MEM]>>
  intLib.ARITH_TAC
QED

Definition row_gte_def:
  row_gte xs ys eq ⇔
  row_gt xs ys ∨ (eq ∧ xs = ys)
End

Theorem row_gte_T:
  row_gt xs ys ∨ xs = ys ⇔
  row_gte xs ys T
Proof
  rw[row_gte_def]
QED

Theorem mk_lex_gte_al1_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr
       (mk_lex_gte_al1 bnd name conds lx ly n eq)) ⇔
  (EVERY (lit wb) conds ⇒
    ((∃i. i < n ∧ wb (dec_at name i)) ∨
    wb (pref_eq name n) ∧
    ((∀i. i < n ⇒ ¬wb (dec_at name i)) ∧ lx > ly ∨
    (∀i. i < n ⇒ ¬wb (dec_at name i)) ∧ eq ∧ lx = ly))))
Proof
  rw[mk_lex_gte_al1_def,MEM_GENLIST,PULL_EXISTS]>>
  eq_tac>>rw[]>>
  gvs[]>>
  metis_tac[lit_def]
QED

Theorem mk_lex_lte_al1_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr
       (mk_lex_lte_al1 bnd name conds lx ly n eq)) ⇔
  (EVERY (lit wb) conds ⇒
  (∃i. i < n ∧ wb (inc_at name i)) ∨
  wb (pref_eq name n) ∧
  ((∀i. i < n ⇒ ¬wb (inc_at name i)) ∧ lx < ly ∨
  (∀i. i < n ⇒ ¬wb (inc_at name i)) ∧ eq ∧ lx = ly)))
Proof
  rw[mk_lex_lte_al1_def,MEM_GENLIST,PULL_EXISTS]>>
  eq_tac>>rw[]>>
  gvs[]>>
  metis_tac[lit_def]
QED

Theorem lex_gte_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical (Lex Zr cmp Xs Ys)) ∧
  (EVERY (lit (reify_avar cs wi)) conds ⇒
    row_gte (MAP (varc wi) Xs) (MAP (varc wi) Ys) eq) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (lex_gte bnd name conds Xs Ys eq))
Proof
  rw[lex_gte_def]
  >- simp[pref_imp_pref_sem,reify_avar_def,reify_flag_def]
  >- simp[pref_imp_eq_sem,reify_avar_def,reify_flag_def]
  >- simp[dec_imp_pref_sem,reify_avar_def,reify_flag_def]
  >- simp[dec_imp_gt_sem,reify_avar_def,reify_flag_def]
  >- (
    fs[row_gte_def,mk_lex_gte_al1_sem]>>
    simp[reify_avar_def,reify_flag_def]>>
    strip_tac>>
    gvs[row_gt_alt,EL_MAP,LIST_EQ_REWRITE]>>
    metis_tac[])
QED

Theorem lex_lte_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical (Lex Zr cmp Xs Ys)) ∧
  (EVERY (lit (reify_avar cs wi)) conds ⇒
    row_gte (MAP (varc wi) Ys) (MAP (varc wi) Xs) eq) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (lex_lte bnd name conds Xs Ys eq))
Proof
  rw[lex_lte_def]
  >- simp[pref_imp_pref_sem,reify_avar_def,reify_flag_def]
  >- simp[pref_imp_eq_sem,reify_avar_def,reify_flag_def]
  >- simp[inc_imp_pref_sem,reify_avar_def,reify_flag_def]
  >- simp[inc_imp_lt_sem,reify_avar_def,reify_flag_def]
  >- (
    fs[row_gte_def,mk_lex_lte_al1_sem]>>
    simp[reify_avar_def,reify_flag_def]>>
    strip_tac>>
    gvs[row_gt_alt,EL_MAP,LIST_EQ_REWRITE]>>
    gvs[integerTheory.INT_GT]>>
    metis_tac[])
QED

Theorem pref_eq_closed[local]:
  (∀i. i < n - 1 ⇒
      wb (INR (name,Indices [i + 2] (SOME «pref»))) ⇒
      wb (INR (name,Indices [i + 1] (SOME «pref»)))) ⇒
  wb (INR (name,Indices [n] (SOME «pref»))) ∧
  j < n ⇒
  wb (INR (name,Indices [j + 1] (SOME «pref»)))
Proof
  Induct_on`n - j`>>rw[]>>
  last_x_assum(qspecl_then[`n`,`j + 1`] mp_tac)>>
  simp[]>>
  Cases_on`n = j + 1` >> fs[]
QED

Theorem lex_gte_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (lex_gte bnd name conds Xs Ys eq)) ∧
  EVERY (lit wb) conds ⇒
  row_gte (MAP (varc wi) Xs) (MAP (varc wi) Ys) eq
Proof
  strip_tac>>
  qpat_x_assum`EVERY _ (abstr _)` mp_tac>>
  simp[lex_gte_def,row_gte_def,row_gt_alt]>>
  simp[pref_imp_pref_sem,dec_imp_pref_sem,dec_imp_gt_sem,pref_imp_eq_sem]>>
  simp[mk_lex_gte_al1_sem]>>rw[]
  >- (
    DISJ1_TAC>>DISJ1_TAC>>
    qexists_tac`i`>>simp[EL_MAP]>>
    Cases_on`i`>>gvs[ADD1]>>
    qpat_x_assum`∀_. _ ⇒ _ ⇒ wb _` $ drule_at Any>>
    impl_tac>- intLib.ARITH_TAC>>
    rw[]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at Any >> simp[]>>
    rw[]>>
    first_x_assum irule>>simp[]>>
    intLib.ARITH_TAC)
  >- (
    DISJ1_TAC>>DISJ2_TAC>>simp[EL_MAP]>>
    rw[]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at (Pos (el 1)) >> simp[])
  >- (
    DISJ2_TAC>>gvs[]>>
    rw[LIST_EQ_REWRITE,EL_MAP]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at (Pos (el 1)) >> simp[])
QED

Theorem lex_lte_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (lex_lte bnd name conds Xs Ys eq)) ∧
  EVERY (lit wb) conds ⇒
  row_gte (MAP (varc wi) Ys) (MAP (varc wi) Xs) eq
Proof
  strip_tac>>
  qpat_x_assum`EVERY _ (abstr _)` mp_tac>>
  simp[lex_lte_def,row_gte_def,row_gt_alt]>>
  simp[pref_imp_pref_sem,inc_imp_pref_sem,inc_imp_lt_sem,pref_imp_eq_sem]>>
  simp[mk_lex_lte_al1_sem]>>rw[]
  >- (
    DISJ1_TAC>>DISJ1_TAC>>
    qexists_tac`i`>>simp[EL_MAP]>>
    gvs[integerTheory.INT_GT]>>
    Cases_on`i`>>gvs[ADD1]>>
    rw[EQ_SYM_EQ]>>
    qpat_x_assum`∀_. _ ⇒ _ ⇒ wb _` $ drule_at Any>>
    impl_tac>- intLib.ARITH_TAC>>
    rw[]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at Any >> simp[]>>
    rw[]>>
    first_x_assum irule>>simp[]>>
    intLib.ARITH_TAC)
  >- (
    DISJ1_TAC>>DISJ2_TAC>>simp[EL_MAP]>>
    rw[EQ_SYM_EQ]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at (Pos (el 1)) >> simp[])
  >- (
    DISJ2_TAC>>gvs[]>>
    rw[EQ_SYM_EQ,LIST_EQ_REWRITE,EL_MAP]>>
    first_x_assum irule>>gvs[]>>
    irule pref_eq_closed>>
    first_x_assum $ irule_at (Pos (el 1)) >> simp[])
QED

Definition cencode_lex_gte_def:
  cencode_lex_gte bnd Zr name Xs Ys eq ec =
  case Zr of
    NONE =>
      (lex_gte bnd name [] Xs Ys eq, ec)
  | SOME (INL Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e $ lex_gte bnd name [reif_gen Zc] Xs Ys eq, ec')
  | SOME (INR Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e
          (Append (lex_gte bnd name [reif_gen Zc] Xs Ys eq)
          (lex_lte bnd name [negate (reif_gen Zc)] Xs Ys (¬eq))), ec')
End

Definition cencode_lex_lte_def:
  cencode_lex_lte bnd Zr name Xs Ys eq ec =
  case Zr of
    NONE =>
      (lex_lte bnd name [] Xs Ys eq, ec)
  | SOME (INL Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e $ lex_lte bnd name [reif_gen Zc] Xs Ys eq, ec')
  | SOME (INR Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e
          (Append (lex_lte bnd name [reif_gen Zc] Xs Ys eq)
          (lex_gte bnd name [negate (reif_gen Zc)] Xs Ys (¬eq))), ec')
End

Definition cencode_lex_def:
  cencode_lex bnd Zr cmp Xs Ys name ec =
  case cmp of
    GreaterThan  => cencode_lex_gte bnd Zr name Xs Ys F ec
  | GreaterEqual => cencode_lex_gte bnd Zr name Xs Ys T ec
  | LessThan     => cencode_lex_lte bnd Zr name Xs Ys F ec
  | LessEqual    => cencode_lex_lte bnd Zr name Xs Ys T ec
  | _ => (cfalse_constr, ec)
End

Definition encode_lex_gte_def:
  encode_lex_gte bnd Zr name Xs Ys eq =
  case Zr of
    NONE =>
      abstr (lex_gte bnd name [] Xs Ys eq)
  | SOME (INL Zc) =>
      encode_reif_gen bnd Zc ++
      abstr (lex_gte bnd name [reif_gen Zc] Xs Ys eq)
  | SOME (INR Zc) =>
      encode_reif_gen bnd Zc ++
      abstr (lex_gte bnd name [reif_gen Zc] Xs Ys eq) ++
      abstr (lex_lte bnd name [negate (reif_gen Zc)] Xs Ys (¬eq))
End

Definition encode_lex_lte_def:
  encode_lex_lte bnd Zr name Xs Ys eq =
  case Zr of
    NONE =>
      abstr (lex_lte bnd name [] Xs Ys eq)
  | SOME (INL Zc) =>
      encode_reif_gen bnd Zc ++
      abstr (lex_lte bnd name [reif_gen Zc] Xs Ys eq)
  | SOME (INR Zc) =>
      encode_reif_gen bnd Zc ++
      abstr (lex_lte bnd name [reif_gen Zc] Xs Ys eq) ++
      abstr (lex_gte bnd name [negate (reif_gen Zc)] Xs Ys (¬eq))
End

Definition encode_lex_def:
  encode_lex bnd Zr cmp Xs Ys name =
  case cmp of
    GreaterThan  => encode_lex_gte bnd Zr name Xs Ys F
  | GreaterEqual => encode_lex_gte bnd Zr name Xs Ys T
  | LessThan     => encode_lex_lte bnd Zr name Xs Ys F
  | LessEqual    => encode_lex_lte bnd Zr name Xs Ys T
  | _ => abstr cfalse_constr
End

Theorem row_gt_irref:
  ∀xs. ¬row_gt xs xs
Proof
  Induct>>rw[row_gt_def]>>
  intLib.ARITH_TAC
QED

Theorem row_gt_neq:
  ∀xs ys.
    xs ≠ ys ⇒
      (row_gt xs ys ⇔ ¬row_gt ys xs)
Proof
  ho_match_mp_tac row_gt_ind>>
  rw[row_gt_def]
  >- (
    eq_tac>>rw[]>>gvs[integerTheory.INT_GT]>>
    CCONTR_TAC>>gvs[]
    >- (
      last_x_assum kall_tac>>
      last_x_assum kall_tac>>
      intLib.ARITH_TAC)>>
    last_x_assum kall_tac>>
    intLib.ARITH_TAC)>>
  Cases_on`ys`>>rw[row_gt_def]
QED

Theorem row_gte_flip:
  row_gte xs ys b ⇔
  ¬row_gte ys xs (¬b)
Proof
  rw[row_gte_def]>>
  Cases_on`xs=ys`
  >-
    (Cases_on`b`>>gvs[row_gt_irref])>>
  metis_tac[row_gt_neq]
QED

Theorem encode_lex_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical (Lex Zr cmp Xs Ys)) ∧
  lex_sem Zr cmp Xs Ys wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lex bnd Zr cmp Xs Ys name)
Proof
  rw[encode_lex_def,lex_sem_def]>>
  Cases_on`cmp`>>fs[]
  >- ( (* GreaterEqual *)
    simp[encode_lex_gte_def]>>
    gvs[row_gte_T,reify_sem_def,AllCasePreds()]
    >- (irule lex_gte_sem_1>>gvs[])
    >- (
      irule_at Any lex_gte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      simp[reify_avar_def,reify_reif_def])
    >- (
      irule_at Any lex_gte_sem_1>>
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      CONJ_TAC >-
        simp[Once row_gte_flip]>>
      simp[reify_avar_def,reify_reif_def]))
  >- ( (* GreaterThan *)
    simp[encode_lex_gte_def]>>
    gvs[reify_sem_def,AllCasePreds()]
    >- (irule lex_gte_sem_1>>gvs[row_gte_def])
    >- (
      irule_at Any lex_gte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      simp[reify_avar_def,reify_reif_def,row_gte_def])
    >- (
      irule_at Any lex_gte_sem_1>>
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      CONJ_TAC >- (
        simp[row_gte_def]>>
        metis_tac[row_gt_neq])>>
      CONJ_TAC >- simp[row_gte_def]>>
      simp[reify_avar_def,reify_reif_def]))
  >- ( (* LessEqual *)
    simp[encode_lex_lte_def]>>
    pop_assum mp_tac>>
    simp[Once EQ_SYM_EQ,row_gte_T]>>
    rw[]>>
    gvs[reify_sem_def,AllCasePreds()]
    >- (irule lex_lte_sem_1>>simp[])
    >- (
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      simp[reify_avar_def,reify_reif_def])
    >- (
      irule_at Any lex_gte_sem_1>>
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      CONJ_TAC >-
        simp[Once row_gte_flip]>>
      simp[reify_avar_def,reify_reif_def]))
  >- ( (* LessThan *)
    simp[encode_lex_lte_def]>>
    gvs[reify_sem_def,AllCasePreds()]
    >- (irule lex_lte_sem_1>>gvs[row_gte_def])
    >- (
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      simp[reify_avar_def,reify_reif_def,row_gte_def])
    >- (
      irule_at Any lex_gte_sem_1>>
      irule_at Any lex_lte_sem_1>>
      simp[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      CONJ_TAC >- simp[row_gte_def]>>
      CONJ_TAC >- (
        simp[row_gte_def]>>
        metis_tac[row_gt_neq])>>
      simp[reify_avar_def,reify_reif_def]))
QED

Theorem encode_lex_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lex bnd Zr cmp Xs Ys name) ⇒
  lex_sem Zr cmp Xs Ys wi
Proof
  rw[encode_lex_def,lex_sem_def]>>
  Cases_on`cmp`>>fs[cfalse_constr_def]
  >- ( (* GreaterEqual *)
    fs[encode_lex_gte_def]>>
    simp[row_gte_T]>>
    every_case_tac>>
    gvs[reify_sem_def]
    >- (
      drule_then drule lex_gte_sem_2>>
      simp[])
    >- (
      drule_then drule lex_gte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen])
    >- (
      drule_then drule lex_gte_sem_2>>
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      eq_tac>>rw[]>>
      CCONTR_TAC>>
      gvs[Once row_gte_flip]))
  >- ( (* GreaterThan *)
    fs[encode_lex_gte_def]>>
    every_case_tac>>
    gvs[reify_sem_def]
    >- (
      drule_then drule lex_gte_sem_2>>
      gvs[row_gte_def])
    >- (
      drule_then drule lex_gte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen,row_gte_def])
    >- (
      drule_then drule lex_gte_sem_2>>
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen,row_gte_T]>>
      eq_tac>>rw[]>>gvs[]
      >- gvs[row_gte_def]>>
      CCONTR_TAC>>
      gvs[]>>
      qpat_x_assum`row_gte _ _ T` mp_tac>>
      simp[Once row_gte_flip,row_gte_def]))
  >- ( (* LessEqual *)
    fs[encode_lex_lte_def]>>
    simp[Once EQ_SYM_EQ]>>
    simp[row_gte_T]>>
    every_case_tac>>
    gvs[reify_sem_def]
    >- (
      drule_then drule lex_lte_sem_2>>
      simp[])
    >- (
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen])
    >- (
      drule_then drule lex_gte_sem_2>>
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
      eq_tac>>rw[]>>
      CCONTR_TAC>>
      gvs[Once row_gte_flip]))
  >- ( (* LessThan *)
    fs[encode_lex_lte_def]>>
    every_case_tac>>
    gvs[reify_sem_def]
    >- (
      drule_then drule lex_lte_sem_2>>
      gvs[row_gte_def])
    >- (
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen,row_gte_def])
    >- (
      drule_then drule lex_gte_sem_2>>
      drule_then drule lex_lte_sem_2>>
      every_case_tac>>rw[]>>
      gvs[encode_reif_gen_sem,lit_reify_avar_reif_gen,row_gte_T]>>
      eq_tac>>rw[]>>gvs[]
      >- gvs[row_gte_def]>>
      CCONTR_TAC>>
      gvs[]>>
      qpat_x_assum`row_gte _ _ T` mp_tac>>
      simp[Once row_gte_flip,row_gte_def]))
QED

Theorem cencode_lex_constr_sem:
  valid_assignment bnd wi ∧
  cencode_lex bnd Zr cmp Xs Ys name ec = (es,ec') ⇒
  enc_rel wi es (encode_lex bnd Zr cmp Xs Ys name) ec ec'
Proof
  fs[cencode_lex_def,encode_lex_def]>>
  Cases_on`cmp`>>rw[]>>
  gvs[encode_lex_gte_def,cencode_lex_gte_def,
    encode_lex_lte_def,cencode_lex_lte_def,AllCaseEqs(),UNCURRY_EQ]>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  rpt $ irule enc_rel_Append>>
  rpt $ irule_at Any enc_rel_encode_reif_gen>>
  simp[]>>
  irule enc_rel_abstr_cong>>
  simp[]
QED

(***
  value_precede / seq_precede_chain

  Per distinct chain value v, a proof-only first-occurrence index pos[v] ∈ [0,n]
  (the shared pos_num kernel, value-keyed). Pins force pos[v] to the leftmost
  occurrence (or the sentinel n); the precede constraints order first
  occurrences along the chain.
***)

(* one proof-only bit flag, keyed by chain VALUE v (an int) and bit b *)
Definition vp_posbit_def[simp]:
  vp_posbit name v b = INR (name, Values [v; &b] (SOME «pos»))
End

(* reified flag [pos[v] ≥ k] *)
Definition vp_ge_flag_def[simp]:
  vp_ge_flag name v k = INR (name, Values [v; &k] (SOME «pge»))
End

(* pos[v] ∈ [0,n] needs bit_width n bits (sentinel reaches n, hence n not n−1) *)
Definition vp_width_def:
  vp_width n = LENGTH (bits_of_num n)
End

(* the proof-only positive bit-sum for value v (the shared pos_num kernel) *)
Definition vp_pos_num_def:
  vp_pos_num name v w = pos_num (vp_posbit name v) w
End

(* pos[v] ≥ k *)
Definition vp_geq_term_def:
  vp_geq_term name v w k = (([], vp_pos_num name v w, &k):('a,'a avar) iconstraint)
End

(* pos[t] − pos[s] ≥ 1 *)
Definition vp_diff_term_def:
  vp_diff_term name t s w =
    (([], vp_pos_num name t w ++ flip_coeffs (vp_pos_num name s w), 1)
      :('a,'a avar) iconstraint)
End

Theorem vp_geq_term_sem[simp]:
  iconstraint_sem (vp_geq_term name v w k) (wi,wb) ⇔
  eval_lin_term wb (vp_pos_num name v w) ≥ &k
Proof
  rw[vp_geq_term_def]
QED

Theorem vp_diff_term_sem[simp]:
  iconstraint_sem (vp_diff_term name t s w) (wi,wb) ⇔
  eval_lin_term wb (vp_pos_num name t w) ≥ eval_lin_term wb (vp_pos_num name s w) + 1
Proof
  rw[vp_diff_term_def]>>
  intLib.ARITH_TAC
QED

(* characterization of the first-occurrence index (a LEAST) *)
Theorem vp_first_occ_le[local]:
  vp_first_occ wi Xs v ≤ LENGTH Xs
Proof
  PURE_REWRITE_TAC[vp_first_occ_def]>>
  numLib.LEAST_ELIM_TAC>>rw[]
  >- (qexists_tac`LENGTH Xs`>>simp[])>>
  gvs[]
QED

Theorem vp_first_occ_occ[local]:
  vp_first_occ wi Xs v < LENGTH Xs ⇒
  varc wi (EL (vp_first_occ wi Xs v) Xs) = v
Proof
  PURE_REWRITE_TAC[vp_first_occ_def]>>
  numLib.LEAST_ELIM_TAC>>rw[]
  >- (qexists_tac`LENGTH Xs`>>simp[])>>
  gvs[]
QED

Theorem vp_first_occ_least[local]:
  j < vp_first_occ wi Xs v ⇒ varc wi (EL j Xs) ≠ v
Proof
  PURE_REWRITE_TAC[vp_first_occ_def]>>
  numLib.LEAST_ELIM_TAC>>rw[]
  >- (qexists_tac`LENGTH Xs`>>simp[])>>
  qpat_x_assum`∀m. _ ⇒ _` (qspec_then`j` mp_tac)>>gvs[]
QED

(* ValuePrecede and SeqPrecedeChain annotate their proof-only flags
   identically; this captures the shared read-back so soundness is proved once *)
Definition vp_reifies_def:
  vp_reifies cs wi name Xs ⇔
  (∀v b. reify_avar cs wi (vp_posbit name v b) ⇔ BIT b (vp_first_occ wi Xs v)) ∧
  (∀v k. reify_avar cs wi (vp_ge_flag name v k) ⇔ &(vp_first_occ wi Xs v) ≥ &k)
End

Theorem vp_reifies_value_precede[local]:
  ALOOKUP cs name = SOME (Lexicographical (ValuePrecede ch Xs)) ⇒
  vp_reifies cs wi name Xs
Proof
  rw[vp_reifies_def,reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

Theorem vp_reifies_seq_precede_chain[local]:
  ALOOKUP cs name = SOME (Lexicographical (SeqPrecedeChain Xs)) ⇒
  vp_reifies cs wi name Xs
Proof
  rw[vp_reifies_def,reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

(* the proof-only bits read back as their intended meaning *)
Theorem reify_vp_pos[local]:
  vp_reifies cs wi name Xs ⇒
  (reify_avar cs wi (vp_posbit name v b) ⇔ BIT b (vp_first_occ wi Xs v))
Proof
  rw[vp_reifies_def]
QED

Theorem reify_vp_ge[local]:
  vp_reifies cs wi name Xs ⇒
  (reify_avar cs wi (vp_ge_flag name v k) ⇔ &(vp_first_occ wi Xs v) ≥ &k)
Proof
  rw[vp_reifies_def]
QED

(* under reify_avar the bit-sum reads back as the first-occurrence index *)
Theorem vp_pos_num_reify[local]:
  vp_reifies cs wi name Xs ⇒
  eval_lin_term (reify_avar cs wi)
    (vp_pos_num name v (vp_width (LENGTH Xs))) = &(vp_first_occ wi Xs v)
Proof
  rw[vp_pos_num_def]>>
  irule pos_num_reify_eq>>
  CONJ_TAC
  >- (rw[]>>drule reify_vp_pos>>simp[])
  >- (
    `vp_first_occ wi Xs v ≤ LENGTH Xs` by simp[vp_first_occ_le]>>
    `LENGTH Xs < 2 ** vp_width (LENGTH Xs)` by simp[vp_width_def,LESS_LENGTH_bits_of_num]>>
    simp[])
QED

(* per distinct chain value v (vi = its index in nub chain, for labels):
   vp_ge flag defs (k=1..n), upper-bound pins, existence pins. The bit-sum pv
   and the Eq-literal list are hoisted (computed once). *)
(* vp_ge flag defs: vp_ge_flag v k ⇔ pos[v] ≥ k, for k = 1..n *)
Definition vp_ge_defs_def:
  vp_ge_defs bnd name v pv n =
  flat_app (GENLIST (λj.
    cbimply_var bnd (vp_ge_flag name v (j+1)) ([], pv, &(j+1))) n)
End

(* upper-bound pins: (X = v) → pos[v] ≤ i  (npv = negated pos bits) *)
Definition vp_ub_pins_def:
  vp_ub_pins bnd name v npv Xs =
  List (MAPi (λi X.
    (SOME (mk_name name (toString i ^ «ub»)),
     bits_imply bnd [Pos (INL (Eq X v))] ([], npv, -&i))) Xs)
End

(* existence pins: [pos[v] ≥ i+1] ∨ ∃k≤i. X_k = v *)
Definition vp_ex_pins_def:
  vp_ex_pins name v eqlits n =
  List (GENLIST (λi.
    (SOME (mk_name name (toString i ^ «ex»)),
     at_least_one (Pos (vp_ge_flag name v (i+1)) :: TAKE (i+1) eqlits))) n)
End

(* per distinct chain value v: vp_ge defs + upper-bound pins + existence pins.
   The bit-sum pv (and its negation) and the Eq-literal list are hoisted. *)
Definition vp_value_block_def:
  vp_value_block bnd name Xs w v =
  let pv = vp_pos_num name v w;
      npv = flip_coeffs pv;
      eqlits = MAPi (λi X. Pos (INL (Eq X v))) Xs in
  Append (vp_ge_defs bnd name v pv (LENGTH Xs))
  (Append (vp_ub_pins bnd name v npv Xs)
          (vp_ex_pins name v eqlits (LENGTH Xs)))
End

(* per consecutive (s,t) of chain: precede (s≠t, guarded by t occurring) or
   "no s" (s=t, forces s absent) *)
Definition vp_precede_blocks_def:
  vp_precede_blocks bnd name w n pi ch =
  case ch of
    s::t::rest =>
      Append
        (List [
          if s = t then
            (SOME (mk_name name (toString pi ^ «nos»)), vp_geq_term name s w n)
          else
            (SOME (mk_name name (toString pi ^ «pr»)),
             bits_imply bnd [Neg (vp_ge_flag name t n)] (vp_diff_term name t s w))])
        (vp_precede_blocks bnd name w n (pi+1) (t::rest))
  | _ => Nil
End

(* the fresh (no shared-reif) part of the encoding *)
Definition vp_blocks_def:
  vp_blocks bnd name Xs ch =
  let w = vp_width (LENGTH Xs); n = LENGTH Xs in
  Append
    (flat_app (MAP (vp_value_block bnd name Xs w) (nub ch)))
    (vp_precede_blocks bnd name w n 0 ch)
End

Definition cencode_value_precede_def:
  cencode_value_precede bnd ch Xs name ec =
  let (egrid, ec') = cencode_eq_grid bnd Xs (nub ch) ec in
  (Append egrid (vp_blocks bnd name Xs ch), ec')
End

Definition encode_value_precede_def:
  encode_value_precede bnd ch Xs name =
  encode_eq_grid bnd Xs (nub ch) ++ abstr (vp_blocks bnd name Xs ch)
End

(* seq_precede_chain: clamp values to [1,m], m = min(max declared ub, n);
   delegate to value_precede with chain [1..m]. The clamp is emitted whenever
   m ≥ 1 (a value > m cannot satisfy the chain); the precede part only for m ≥ 2. *)
Definition vp_seq_m_def:
  vp_seq_m bnd Xs =
  let mx = FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs in
  MIN (if mx < 0 then 0 else Num mx) (LENGTH Xs)
End

Definition vp_clamp_def:
  vp_clamp name Xs m =
  List (MAPi (λi X.
    (SOME (mk_name name (toString i ^ «cl»)),
     mk_constraint_one_ge (-1) X (-&m))) Xs)
End

Definition cencode_seq_precede_chain_def:
  cencode_seq_precede_chain bnd Xs name ec =
  let m = vp_seq_m bnd Xs in
  if m < 1 then (Nil, ec)
  else if m < 2 then (vp_clamp name Xs m, ec)
  else
    let (e,ec') = cencode_value_precede bnd (GENLIST (λk. &(k+1)) m) Xs name ec in
    (Append (vp_clamp name Xs m) e, ec')
End

Definition encode_seq_precede_chain_def:
  encode_seq_precede_chain bnd Xs name =
  let m = vp_seq_m bnd Xs in
  if m < 1 then []
  else if m < 2 then abstr (vp_clamp name Xs m)
  else
    abstr (vp_clamp name Xs m) ++
    encode_value_precede bnd (GENLIST (λk. &(k+1)) m) Xs name
End

Theorem vp_ge_defs_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (vp_ge_defs bnd name v pv n)) ⇔
   ∀j. j < n ⇒
     (wb (vp_ge_flag name v (j+1)) ⇔ eval_lin_term wb pv ≥ &(j+1)))
Proof
  strip_tac>>
  simp[vp_ge_defs_def,abstr_flat_app]>>
  simp[EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,cbimply_var_def,append_thm]>>
  metis_tac[]
QED

Theorem vp_ub_pins_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (vp_ub_pins bnd name v npv Xs)) ⇔
   ∀i. i < LENGTH Xs ⇒
     (wb (INL (Eq (EL i Xs) v)) ⇒ eval_lin_term wb npv ≥ -&i))
Proof
  rw[vp_ub_pins_def,append_thm,EVERY_MEM,MEM_MAP,MEM_MAPi,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem vp_ex_pins_sem[local]:
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (vp_ex_pins name v eqlits n)) ⇔
   ∀i. i < n ⇒
     (wb (vp_ge_flag name v (i+1)) ∨
      ∃l. MEM l (TAKE (i+1) eqlits) ∧ lit wb l))
Proof
  rw[vp_ex_pins_def,append_thm,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS,
     at_least_one_sem]>>
  metis_tac[lit_def]
QED

(* the existence-clause literal list (a prefix of the Eq literals) is satisfied
   iff some earlier position takes value v *)
Theorem vp_take_eqlits[local]:
  i < LENGTH Xs ⇒
  ((∃l. MEM l (TAKE (i+1) (MAP (λX. Pos (INL (Eq X v))) Xs)) ∧ lit wb l) ⇔
   ∃k. k < i+1 ∧ wb (INL (Eq (EL k Xs) v)))
Proof
  rw[]>>
  `i + 1 ≤ LENGTH Xs` by simp[]>>
  simp[MEM_EL,LENGTH_TAKE,EL_TAKE,EL_MAP,PULL_EXISTS]>>
  `∀n. n < i+1 ⇒
     EL n (TAKE (i+1) (MAP (λX. Pos (INL (Eq X v))) Xs)) =
     Pos (INL (Eq (EL n Xs) v))` by
    (rw[]>>DEP_REWRITE_TAC[EL_TAKE,EL_MAP]>>simp[])>>
  metis_tac[lit_def]
QED

(* characterization of one value's block under an arbitrary wb *)
Theorem vp_value_block_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
     (abstr (vp_value_block bnd name Xs w v)) ⇔
   (∀j. j < LENGTH Xs ⇒
      (wb (vp_ge_flag name v (j+1)) ⇔
       eval_lin_term wb (vp_pos_num name v w) ≥ &(j+1))) ∧
   (∀i. i < LENGTH Xs ⇒
      (wb (INL (Eq (EL i Xs) v)) ⇒
       eval_lin_term wb (vp_pos_num name v w) ≤ &i)) ∧
   (∀i. i < LENGTH Xs ⇒
      (wb (vp_ge_flag name v (i+1)) ∨
       ∃k. k < i+1 ∧ wb (INL (Eq (EL k Xs) v)))))
Proof
  strip_tac>>
  simp[vp_value_block_def,append_thm,EVERY_APPEND,vp_ge_defs_sem,
       vp_ub_pins_sem,vp_ex_pins_sem]>>
  `∀(x:int) (i:num). -x ≥ -&i ⇔ x ≤ &i` by intLib.ARITH_TAC>>
  metis_tac[vp_take_eqlits]
QED

(* per-pair precede facts over an arbitrary wb (the bit-level analogue of
   value_precede_sem, mirroring vp_precede_blocks' recursion) *)
Definition vp_precede_holds_def:
  vp_precede_holds wb name w n ch =
  case ch of
    s::t::rest =>
      (if s = t then eval_lin_term wb (vp_pos_num name s w) ≥ &n
       else (¬wb (vp_ge_flag name t n) ⇒
             eval_lin_term wb (vp_pos_num name t w) ≥
             eval_lin_term wb (vp_pos_num name s w) + 1)) ∧
      vp_precede_holds wb name w n (t::rest)
  | _ => T
End

Theorem vp_precede_blocks_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
     (abstr (vp_precede_blocks bnd name w n pi ch)) ⇔
   vp_precede_holds wb name w n ch)
Proof
  strip_tac>>
  qid_spec_tac`pi`>>
  Induct_on`ch`>>
  rw[Once vp_precede_blocks_def,Once vp_precede_holds_def,append_thm]>>
  Cases_on`ch`>>
  gvs[append_thm,EVERY_APPEND]>>
  rw[]
QED

(* under reify_avar each per-value block's three pin facts hold — they are
   properties of the LEAST first-occurrence index *)
Theorem vp_value_block_reify[local]:
  valid_assignment bnd wi ∧
  vp_reifies cs wi name Xs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (vp_value_block bnd name Xs (vp_width (LENGTH Xs)) v))
Proof
  strip_tac>>
  `∀k. reify_avar cs wi (vp_ge_flag name v k) ⇔ &(vp_first_occ wi Xs v) ≥ &k` by
    metis_tac[reify_vp_ge]>>
  `eval_lin_term (reify_avar cs wi)
     (vp_pos_num name v (vp_width (LENGTH Xs))) = &(vp_first_occ wi Xs v)` by
    metis_tac[vp_pos_num_reify]>>
  `∀X. reify_avar cs wi (INL (Eq X v)) ⇔ varc wi X = v` by
    simp[reify_avar_def,reify_reif_def]>>
  simp[vp_value_block_sem]>>
  rw[]
  >- (CCONTR_TAC>>gvs[NOT_LESS_EQUAL]>>metis_tac[vp_first_occ_least])>>
  Cases_on`vp_first_occ wi Xs v ≤ i`
  >- (
    disj2_tac>>
    qexists_tac`vp_first_occ wi Xs v`>>
    `vp_first_occ wi Xs v < LENGTH Xs` by simp[]>>
    simp[vp_first_occ_occ])>>
  disj1_tac>>gvs[NOT_LESS_EQUAL,integerTheory.INT_GE,integerTheory.INT_LE]
QED

(* recursive per-adjacent-pair first-occurrence precede: the readback analogue of
   vp_precede_holds (eval = first-occ index). Mirrors the encoder's pairwise shape. *)
Definition vp_fo_holds_def:
  vp_fo_holds wi Xs ch ⇔
  case ch of
    s::t::rest =>
      (vp_first_occ wi Xs t < LENGTH Xs ⇒
       vp_first_occ wi Xs s < vp_first_occ wi Xs t) ∧
      vp_fo_holds wi Xs (t::rest)
  | _ => T
End

(* an occurrence of v at jj caps its first-occurrence index *)
Theorem vp_first_occ_leq[local]:
  jj < LENGTH Xs ∧ varc wi (EL jj Xs) = v ⇒ vp_first_occ wi Xs v ≤ jj
Proof
  rw[]>>CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
  metis_tac[vp_first_occ_least]
QED

(* adjacent strict-increase (wherever the later value occurs) lifts to all pairs:
   occurrence propagates backwards through the chain *)
Theorem vp_fo_allp[local]:
  (∀k. SUC k < LENGTH ch ⇒
     vp_first_occ wi Xs (EL (SUC k) ch) < LENGTH Xs ⇒
     vp_first_occ wi Xs (EL k ch) < vp_first_occ wi Xs (EL (SUC k) ch)) ⇒
  ∀i j. i < j ∧ j < LENGTH ch ⇒
    vp_first_occ wi Xs (EL j ch) < LENGTH Xs ⇒
    vp_first_occ wi Xs (EL i ch) < vp_first_occ wi Xs (EL j ch)
Proof
  strip_tac>>Induct_on`j`>>rw[]>>
  `vp_first_occ wi Xs (EL j ch) < vp_first_occ wi Xs (EL (SUC j) ch)` by
    (qpat_x_assum`∀k. SUC k < LENGTH ch ⇒ _`irule>>gvs[])>>
  Cases_on`i = j`>>fs[]>>
  `i < j` by gvs[]>>
  `vp_first_occ wi Xs (EL j ch) < LENGTH Xs` by
    (qpat_x_assum`vp_first_occ wi Xs (EL j ch) < _`mp_tac>>
     qpat_x_assum`vp_first_occ wi Xs (EL (SUC j) ch) < LENGTH Xs`mp_tac>>decide_tac)>>
  `vp_first_occ wi Xs (EL i ch) < vp_first_occ wi Xs (EL j ch)` by
    (first_x_assum irule>>gvs[])>>
  qpat_x_assum`vp_first_occ wi Xs (EL i ch) < _`mp_tac>>
  qpat_x_assum`vp_first_occ wi Xs (EL j ch) < vp_first_occ wi Xs (EL (SUC j) ch)`mp_tac>>
  decide_tac
QED

(* vp_fo_holds (recursive, by adjacent pairs) = the explicit ∀-adjacent form *)
Theorem vp_fo_holds_adj[local]:
  vp_fo_holds wi Xs ch ⇔
  ∀k. SUC k < LENGTH ch ⇒
    vp_first_occ wi Xs (EL (SUC k) ch) < LENGTH Xs ⇒
    vp_first_occ wi Xs (EL k ch) < vp_first_occ wi Xs (EL (SUC k) ch)
Proof
  Induct_on`ch`>>simp[Once vp_fo_holds_def]>>
  Cases_on`ch`>>simp[]>>
  gen_tac>>eq_tac>>rw[]
  >- (Cases_on`k`>>fs[])
  >- (first_x_assum(qspec_then`0`mp_tac)>>fs[])>>
  first_x_assum(qspec_then`SUC k`mp_tac)>>fs[]
QED

(* the recursive adjacent precede = the all-pairs occurrence semantics *)
Theorem vp_fo_holds_value_precede[local]:
  vp_fo_holds wi Xs ch ⇔ value_precede_sem ch Xs wi
Proof
  rw[vp_fo_holds_adj,value_precede_sem_def]>>
  eq_tac>>rw[]
  >- (
    `jj < LENGTH Xs` by fs[]>>
    `varc wi (EL jj Xs) = EL j ch` by gvs[EL_MAP]>>
    `vp_first_occ wi Xs (EL j ch) ≤ jj` by metis_tac[vp_first_occ_leq]>>
    `vp_first_occ wi Xs (EL j ch) < LENGTH Xs` by gvs[]>>
    `vp_first_occ wi Xs (EL i ch) < vp_first_occ wi Xs (EL j ch)` by
      (irule vp_fo_allp>>fs[])>>
    qexists_tac`vp_first_occ wi Xs (EL i ch)`>>
    `vp_first_occ wi Xs (EL i ch) < LENGTH Xs` by gvs[]>>
    `varc wi (EL (vp_first_occ wi Xs (EL i ch)) Xs) = EL i ch` by
      metis_tac[vp_first_occ_occ]>>
    gvs[EL_MAP])>>
  `varc wi (EL (vp_first_occ wi Xs (EL (SUC k) ch)) Xs) = EL (SUC k) ch` by
    metis_tac[vp_first_occ_occ]>>
  first_x_assum(qspecl_then[`k`,`SUC k`]mp_tac)>>
  impl_tac>- gvs[]>>
  disch_then(qspec_then`vp_first_occ wi Xs (EL (SUC k) ch)`mp_tac)>>
  impl_tac>- gvs[EL_MAP]>>
  rw[]>>
  `varc wi (EL ii Xs) = EL k ch` by gvs[EL_MAP]>>
  `vp_first_occ wi Xs (EL k ch) ≤ ii` by metis_tac[vp_first_occ_leq]>>
  gvs[]
QED

(* under reify_avar the precede blocks read back as the CP-level value_precede *)
Theorem vp_precede_holds_reify[local]:
  vp_reifies cs wi name Xs ⇒
  (vp_precede_holds (reify_avar cs wi) name (vp_width (LENGTH Xs)) (LENGTH Xs) ch ⇔
   value_precede_sem ch Xs wi)
Proof
  strip_tac>>
  simp[GSYM vp_fo_holds_value_precede]>>
  `∀v k. reify_avar cs wi (vp_ge_flag name v k) ⇔ &(vp_first_occ wi Xs v) ≥ &k` by
    metis_tac[reify_vp_ge]>>
  `∀v. eval_lin_term (reify_avar cs wi)
        (vp_pos_num name v (vp_width (LENGTH Xs))) = &(vp_first_occ wi Xs v)` by
    metis_tac[vp_pos_num_reify]>>
  Induct_on`ch`>>
  rw[Once vp_precede_holds_def,Once vp_fo_holds_def]>>
  Cases_on`ch`>>gvs[]>>
  Cases_on`vp_fo_holds wi Xs (h'::t)`>>
  gvs[integerTheory.INT_GE,integerTheory.INT_LE]>>
  rw[]>>gvs[]>>intLib.ARITH_TAC
QED

Theorem encode_value_precede_sem_1:
  valid_assignment bnd wi ∧
  vp_reifies cs wi name Xs ∧
  value_precede_sem ch Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_value_precede bnd ch Xs name)
Proof
  strip_tac>>
  simp[encode_value_precede_def,EVERY_APPEND]>>
  conj_tac
  >- rw[reify_avar_def,reify_reif_def]>>
  simp[vp_blocks_def,append_thm,EVERY_APPEND]>>
  reverse conj_tac
  >- (simp[vp_precede_blocks_sem]>>metis_tac[vp_precede_holds_reify])>>
  simp[EVERY_FLAT,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  rw[]>>
  `EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
     (abstr (vp_value_block bnd name Xs (vp_width (LENGTH Xs)) y))` by
    (irule vp_value_block_reify>>metis_tac[])>>
  fs[EVERY_MEM,MEM_MAP]>>metis_tac[]
QED

(* completeness bridge: under an arbitrary wb the per-value pins + the eq grid
   force the bit-sum to read back the first-occurrence index (sentinel n) *)
Theorem vp_pin_bridge[local]:
  (∀X. MEM X Xs ⇒ (wb (INL (Eq X v)) ⇔ varc wi X = v)) ∧
  (∀j. j < LENGTH Xs ⇒
     (wb (vp_ge_flag name v (j+1)) ⇔
      eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &(j+1))) ∧
  (∀i. i < LENGTH Xs ⇒
     (wb (INL (Eq (EL i Xs) v)) ⇒
      eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≤ &i)) ∧
  (∀i. i < LENGTH Xs ⇒
     (wb (vp_ge_flag name v (i+1)) ∨ ∃k. k < i+1 ∧ wb (INL (Eq (EL k Xs) v)))) ⇒
  (vp_first_occ wi Xs v < LENGTH Xs ⇒
     eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) =
     &(vp_first_occ wi Xs v)) ∧
  (vp_first_occ wi Xs v = LENGTH Xs ⇒
     eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &(LENGTH Xs))
Proof
  strip_tac>>
  qabbrev_tac`P = eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs)))`>>
  `0 ≤ P` by simp[Abbr`P`,vp_pos_num_def,pos_num_num_of_bits]>>
  `∀i. i < LENGTH Xs ⇒ (wb (INL (Eq (EL i Xs) v)) ⇔ varc wi (EL i Xs) = v)` by
    (rw[]>>first_x_assum irule>>simp[EL_MEM])>>
  `∀k. k < vp_first_occ wi Xs v ⇒ ¬wb (INL (Eq (EL k Xs) v))` by (
    rw[]>>
    `vp_first_occ wi Xs v ≤ LENGTH Xs` by simp[vp_first_occ_le]>>
    `k < LENGTH Xs` by simp[]>>
    metis_tac[vp_first_occ_least])>>
  reverse conj_tac
  >- (
    strip_tac>>
    Cases_on`LENGTH Xs = 0`>-(gvs[]>>intLib.ARITH_TAC)>>
    `LENGTH Xs - 1 + 1 = LENGTH Xs` by simp[]>>
    `∀k. k < LENGTH Xs ⇒ ¬wb (INL (Eq (EL k Xs) v))` by metis_tac[]>>
    `wb (vp_ge_flag name v (LENGTH Xs)) ⇔ P ≥ &LENGTH Xs` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ (_ ⇔ _ ≥ _)`
         (qspec_then`LENGTH Xs - 1` mp_tac)>>simp[])>>
    `wb (vp_ge_flag name v (LENGTH Xs))` by
      (qpat_x_assum`∀i. i < LENGTH Xs ⇒ (_ ∨ _)`
         (qspec_then`LENGTH Xs - 1` mp_tac)>>simp[]>>metis_tac[])>>
    metis_tac[])>>
  strip_tac>>
  `varc wi (EL (vp_first_occ wi Xs v) Xs) = v` by metis_tac[vp_first_occ_occ]>>
  `P ≤ &(vp_first_occ wi Xs v)` by metis_tac[]>>
  `&(vp_first_occ wi Xs v) ≤ P`
    suffices_by metis_tac[integerTheory.INT_LE_ANTISYM]>>
  Cases_on`vp_first_occ wi Xs v = 0`
  >-(qpat_x_assum`vp_first_occ wi Xs v = 0`(fn th => fs[th])>>simp[])>>
  `vp_first_occ wi Xs v - 1 + 1 = vp_first_occ wi Xs v` by simp[]>>
  `wb (vp_ge_flag name v (vp_first_occ wi Xs v)) ⇔
   P ≥ &(vp_first_occ wi Xs v)` by
    (qpat_x_assum`∀j. j < LENGTH Xs ⇒ (_ ⇔ _ ≥ _)`
       (qspec_then`vp_first_occ wi Xs v - 1` mp_tac)>>simp[])>>
  `wb (vp_ge_flag name v (vp_first_occ wi Xs v))` by
    (qpat_x_assum`∀i. i < LENGTH Xs ⇒ (_ ∨ _)`
       (qspec_then`vp_first_occ wi Xs v - 1` mp_tac)>>simp[]>>metis_tac[])>>
  gvs[integerTheory.INT_GE]
QED

(* the precede blocks (over an arbitrary wb) + the per-value first-occurrence
   readback give back the CP-level value_precede *)
Theorem value_precede_of_holds[local]:
  (∀v. MEM v ch ⇒
     (vp_first_occ wi Xs v < LENGTH Xs ⇒
        eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) =
        &(vp_first_occ wi Xs v)) ∧
     (vp_first_occ wi Xs v = LENGTH Xs ⇒
        eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥
        &LENGTH Xs) ∧
     (wb (vp_ge_flag name v (LENGTH Xs)) ⇔
        eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥
        &LENGTH Xs)) ∧
  vp_precede_holds wb name (vp_width (LENGTH Xs)) (LENGTH Xs) ch ⇒
  value_precede_sem ch Xs wi
Proof
  simp[GSYM vp_fo_holds_value_precede]>>
  Induct_on`ch`>>
  simp[Once vp_precede_holds_def,Once vp_fo_holds_def]>>
  Cases_on`ch`>>simp[]>>
  strip_tac>>strip_tac>>
  reverse conj_tac
  >- (first_x_assum irule>>simp[]>>metis_tac[])>>
  strip_tac>>
  `vp_first_occ wi Xs h' ≤ LENGTH Xs ∧ vp_first_occ wi Xs h ≤ LENGTH Xs` by
    simp[vp_first_occ_le]>>
  `eval_lin_term wb (vp_pos_num name h (vp_width (LENGTH Xs))) =
   &(vp_first_occ wi Xs h)` by metis_tac[]>>
  Cases_on`h' = h`
  >- gvs[integerTheory.INT_GE]>>
  gvs[]>>
  `¬(&vp_first_occ wi Xs h ≥ &LENGTH Xs)` by
    gvs[integerTheory.INT_GE,integerTheory.INT_LE]>>
  gvs[]>>
  reverse (Cases_on`vp_first_occ wi Xs h' < LENGTH Xs`)
  >- (
    (* h' absent: its readback forces eval ≥ n, contradicting the precede bound *)
    `vp_first_occ wi Xs h' = LENGTH Xs` by gvs[]>>
    `eval_lin_term wb (vp_pos_num name h' (vp_width (LENGTH Xs))) ≥ &LENGTH Xs`
      by metis_tac[]>>
    `F` suffices_by simp[]>>
    qpat_x_assum`&vp_first_occ wi Xs h ≥ _`mp_tac>>
    qpat_x_assum`eval_lin_term _ _ ≥ &LENGTH Xs`mp_tac>>
    qpat_x_assum`¬(&vp_first_occ wi Xs h ≥ _)`mp_tac>>
    rpt(pop_assum kall_tac)>>
    qabbrev_tac`A = &vp_first_occ wi Xs h : int`>>
    qabbrev_tac`N = &LENGTH Xs : int`>>
    qabbrev_tac`E = eval_lin_term wb (vp_pos_num name h' (vp_width (LENGTH Xs)))`>>
    intLib.ARITH_TAC)>>
  `eval_lin_term wb (vp_pos_num name h' (vp_width (LENGTH Xs))) =
   &(vp_first_occ wi Xs h')` by metis_tac[]>>
  gvs[]>>
  `&vp_first_occ wi Xs h' < &vp_first_occ wi Xs h` suffices_by
    simp[integerTheory.INT_LT]>>
  qpat_x_assum`&vp_first_occ wi Xs h ≥ _`mp_tac>>
  rpt(pop_assum kall_tac)>>
  qabbrev_tac`A = &vp_first_occ wi Xs h : int`>>
  qabbrev_tac`B = &vp_first_occ wi Xs h' : int`>>
  intLib.ARITH_TAC
QED

(* on an empty Xs every first-occurrence index is the (zero) sentinel, so every
   precede pair is vacuous *)
Theorem value_precede_sem_nil[local]:
  value_precede_sem ch [] wi
Proof
  Induct_on`ch`>>simp[Once value_precede_sem_def]>>
  Cases_on`ch`>>simp[]
QED

(* completeness, per value: the per-value block (with the eq grid) forces the
   first-occurrence readback (occ / absent) and the sentinel ge flag *)
Theorem value_precede_pins[local]:
  valid_assignment bnd wi ∧ LENGTH Xs ≠ 0 ∧
  (∀X. MEM X Xs ⇒ (wb (INL (Eq X v)) ⇔ varc wi X = v)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (vp_value_block bnd name Xs (vp_width (LENGTH Xs)) v)) ⇒
  (vp_first_occ wi Xs v < LENGTH Xs ⇒
     eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) =
     &(vp_first_occ wi Xs v)) ∧
  (vp_first_occ wi Xs v = LENGTH Xs ⇒
     eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &LENGTH Xs) ∧
  (wb (vp_ge_flag name v (LENGTH Xs)) ⇔
     eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &LENGTH Xs)
Proof
  strip_tac>>
  `(∀j. j < LENGTH Xs ⇒
      (wb (vp_ge_flag name v (j+1)) ⇔
       eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &(j+1))) ∧
   (∀i. i < LENGTH Xs ⇒
      (wb (INL (Eq (EL i Xs) v)) ⇒
       eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≤ &i)) ∧
   (∀i. i < LENGTH Xs ⇒
      (wb (vp_ge_flag name v (i+1)) ∨
       ∃k. k < i+1 ∧ wb (INL (Eq (EL k Xs) v))))` by
    metis_tac[vp_value_block_sem]>>
  `(LENGTH Xs - 1) + 1 = LENGTH Xs ∧ LENGTH Xs - 1 < LENGTH Xs` by
    (Cases_on`LENGTH Xs`>>fs[])>>
  `(vp_first_occ wi Xs v < LENGTH Xs ⇒
      eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) =
      &(vp_first_occ wi Xs v)) ∧
   (vp_first_occ wi Xs v = LENGTH Xs ⇒
      eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥
      &LENGTH Xs)` by (irule vp_pin_bridge>>gs[])>>
  `wb (vp_ge_flag name v (LENGTH Xs)) ⇔
   eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥ &LENGTH Xs` by (
    qpat_x_assum`∀j. j < LENGTH Xs ⇒ (_ ⇔ _ ≥ _)`
      (qspec_then`LENGTH Xs - 1`mp_tac)>>fs[])>>
  gs[]
QED

(* the per-value first-occurrence readback, for every value of the chain *)
Theorem value_precede_all_pins[local]:
  valid_assignment bnd wi ∧ LENGTH Xs ≠ 0 ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq_grid bnd Xs (nub ch)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λls. abstr ls)
      (MAP (vp_value_block bnd name Xs (vp_width (LENGTH Xs))) (nub ch)))) ⇒
  ∀v. MEM v ch ⇒
    (vp_first_occ wi Xs v < LENGTH Xs ⇒
       eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) =
       &(vp_first_occ wi Xs v)) ∧
    (vp_first_occ wi Xs v = LENGTH Xs ⇒
       eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥
       &LENGTH Xs) ∧
    (wb (vp_ge_flag name v (LENGTH Xs)) ⇔
       eval_lin_term wb (vp_pos_num name v (vp_width (LENGTH Xs))) ≥
       &LENGTH Xs)
Proof
  strip_tac>>gen_tac>>strip_tac>>
  `MEM v (nub ch)` by simp[MEM_nub]>>
  `EVERY (λx. iconstraint_sem x (wi,wb))
     (abstr (vp_value_block bnd name Xs (vp_width (LENGTH Xs)) v))` by (
    qpat_x_assum`EVERY _ (FLAT _)`mp_tac>>
    simp[EVERY_FLAT,EVERY_MAP,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
    metis_tac[])>>
  `∀X. MEM X Xs ⇒ (wb (INL (Eq X v)) ⇔ varc wi X = v)` by (
    qpat_x_assum`EVERY _ (encode_eq_grid _ _ _)`mp_tac>>
    simp[encode_eq_grid_sem]>>
    metis_tac[])>>
  metis_tac[value_precede_pins]
QED

Theorem encode_value_precede_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_value_precede bnd ch Xs name) ⇒
  value_precede_sem ch Xs wi
Proof
  strip_tac>>
  Cases_on`Xs = []`
  >- simp[value_precede_sem_nil]>>
  fs[encode_value_precede_def,EVERY_APPEND,vp_blocks_def,append_thm]>>
  `LENGTH Xs ≠ 0` by (Cases_on`Xs`>>fs[])>>
  `vp_precede_holds wb name (vp_width (LENGTH Xs)) (LENGTH Xs) ch` by
    metis_tac[vp_precede_blocks_sem]>>
  metis_tac[value_precede_of_holds,value_precede_all_pins]
QED

Theorem cencode_value_precede_sem:
  valid_assignment bnd wi ∧
  cencode_value_precede bnd ch Xs name ec = (es,ec') ⇒
  enc_rel wi es (encode_value_precede bnd ch Xs name) ec ec'
Proof
  rw[cencode_value_precede_def,encode_value_precede_def]>>
  pairarg_tac>>gvs[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_eq_grid>>
  first_assum (irule_at Any)>>
  simp[enc_rel_abstr]
QED

(* the clamp constraints hold iff every variable is bounded by m *)
Theorem vp_clamp_sem[local]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (vp_clamp name Xs m)) ⇔
  ∀X. MEM X Xs ⇒ varc wi X ≤ &m
Proof
  `∀(v:int). -1 * v ≥ -&m ⇔ v ≤ &m` by intLib.ARITH_TAC>>
  pop_assum(fn th =>
    simp[vp_clamp_def,combinTheory.o_DEF,EVERY_EL,indexedListsTheory.LENGTH_MAPi,
         indexedListsTheory.EL_MAPi,EL_MAP,th,EVERY_MEM,MEM_EL,PULL_EXISTS])
QED

(* every assigned value is dominated by the largest declared upper bound *)
Theorem vp_seq_ub[local]:
  valid_assignment bnd wi ⇒
  ∀X. MEM X Xs ⇒
    varc wi X ≤ FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs
Proof
  strip_tac>>Induct_on`Xs`>- simp[]>>
  gen_tac>>strip_tac>>strip_tac>>
  `varc wi X ≤ SND (varc_bnd bnd X)` by metis_tac[varc_bnd_valid]>>
  gvs[]
  >- (rw[integerTheory.INT_MAX]>>intLib.ARITH_TAC)>>
  `varc wi X ≤ FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs` by metis_tac[]>>
  rw[integerTheory.INT_MAX]>>intLib.ARITH_TAC
QED

(* when the clamp bound collapses to 0, no value can be positive *)
Theorem vp_seq_zero_ub[local]:
  valid_assignment bnd wi ∧ vp_seq_m bnd Xs = 0 ⇒
  ∀X. MEM X Xs ⇒ varc wi X ≤ 0
Proof
  rw[]>>
  `varc wi X ≤ FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs` by metis_tac[vp_seq_ub]>>
  `LENGTH Xs ≠ 0` by (Cases_on`Xs`>>fs[])>>
  qpat_x_assum`vp_seq_m _ _ = 0`mp_tac>>
  simp[vp_seq_m_def,MIN_DEF]>>
  rw[]>>intLib.ARITH_TAC
QED

(* seq forces value v ≥ 1 at position jj to be at most jj+1 (pigeonhole) *)
Theorem vp_seq_pigeon[local]:
  seq_precede_chain_sem Xs wi ⇒
  ∀jj. jj < LENGTH Xs ∧ 1 ≤ varc wi (EL jj Xs) ⇒
    varc wi (EL jj Xs) ≤ &(jj+1)
Proof
  strip_tac>>
  completeInduct_on`jj`>>
  rw[]>>
  reverse(Cases_on`2 ≤ varc wi (EL jj Xs)`)
  >- (
    irule integerTheory.INT_LE_TRANS>>qexists_tac`1`>>CONJ_TAC
    >- (qpat_x_assum`¬(2 ≤ _)`mp_tac>>rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    simp[integerTheory.INT_OF_NUM_LE])>>
  `EL jj (MAP (varc wi) Xs) = varc wi (EL jj Xs)` by (irule EL_MAP>>fs[])>>
  `∃i. i < jj ∧ EL i (MAP (varc wi) Xs) = EL jj (MAP (varc wi) Xs) − 1` by (
    qpat_x_assum`seq_precede_chain_sem _ _`mp_tac>>
    simp[seq_precede_chain_sem_def]>>
    disch_then match_mp_tac>>fs[])>>
  `i < LENGTH Xs` by fs[]>>
  `EL i (MAP (varc wi) Xs) = varc wi (EL i Xs)` by (irule EL_MAP>>fs[])>>
  `varc wi (EL i Xs) = varc wi (EL jj Xs) − 1` by fs[]>>
  `1 ≤ varc wi (EL i Xs)` by
    (qpat_x_assum`2 ≤ _`mp_tac>>qpat_x_assum`varc wi (EL i Xs) = _`mp_tac>>
     rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  `varc wi (EL i Xs) ≤ &(i+1)` by (first_x_assum irule>>fs[])>>
  `&(i+1) ≤ &jj` by (simp[integerTheory.INT_OF_NUM_LE]>>fs[])>>
  qpat_x_assum`&(i+1) ≤ &jj`mp_tac>>
  qpat_x_assum`varc wi (EL i Xs) ≤ _`mp_tac>>
  qpat_x_assum`varc wi (EL i Xs) = _`mp_tac>>
  rpt(pop_assum kall_tac)>>
  simp[GSYM integerTheory.INT_OF_NUM_ADD]>>intLib.ARITH_TAC
QED

(* seq propagates an occurrence of value b backwards to all 1 ≤ a < b *)
Theorem vp_seq_back[local]:
  seq_precede_chain_sem Xs wi ⇒
  ∀b jj. jj < LENGTH Xs ∧ varc wi (EL jj Xs) = &b ⇒
    ∀a. 1 ≤ a ∧ a < b ⇒ ∃ii. ii < jj ∧ varc wi (EL ii Xs) = &a
Proof
  strip_tac>>
  completeInduct_on`b`>>
  rw[]>>
  `2 ≤ b` by fs[]>>
  `EL jj (MAP (varc wi) Xs) = varc wi (EL jj Xs)` by (irule EL_MAP>>fs[])>>
  `2 ≤ varc wi (EL jj Xs)` by
    (gvs[]>>simp[integerTheory.INT_OF_NUM_LE])>>
  `∃q. q < jj ∧ EL q (MAP (varc wi) Xs) = EL jj (MAP (varc wi) Xs) − 1` by (
    qpat_x_assum`seq_precede_chain_sem _ _`mp_tac>>
    simp[seq_precede_chain_sem_def]>>
    disch_then match_mp_tac>>fs[])>>
  `q < LENGTH Xs` by fs[]>>
  `EL q (MAP (varc wi) Xs) = varc wi (EL q Xs)` by (irule EL_MAP>>fs[])>>
  `varc wi (EL q Xs) = &(b − 1)` by
    (gvs[]>>simp[integerTheory.INT_SUB,integerTheory.INT_OF_NUM_LE])>>
  Cases_on`a = b − 1`
  >- (qexists_tac`q`>>fs[])>>
  `a < b − 1` by fs[]>>
  qpat_x_assum`∀m. m < b ⇒ _`(qspec_then`b−1`mp_tac)>>
  impl_tac >- fs[]>>
  disch_then(qspec_then`q`mp_tac)>>
  impl_tac >- fs[]>>
  disch_then(qspec_then`a`mp_tac)>>
  impl_tac >- fs[]>>
  strip_tac>>
  qexists_tac`ii`>>fs[]
QED

(* seq bounds every value by the number of variables *)
Theorem vp_seq_len_ub[local]:
  seq_precede_chain_sem Xs wi ⇒
  ∀jj. jj < LENGTH Xs ⇒ varc wi (EL jj Xs) ≤ &(LENGTH Xs)
Proof
  rw[]>>
  Cases_on`1 ≤ varc wi (EL jj Xs)`
  >- (
    `varc wi (EL jj Xs) ≤ &(jj+1)` by metis_tac[vp_seq_pigeon]>>
    `&(jj+1) ≤ &(LENGTH Xs)` by (simp[integerTheory.INT_OF_NUM_LE]>>fs[])>>
    metis_tac[integerTheory.INT_LE_TRANS])>>
  `varc wi (EL jj Xs) ≤ 0` by
    (qpat_x_assum`¬(1 ≤ _)`mp_tac>>rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  `(0:int) ≤ &(LENGTH Xs)` by simp[]>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

(* seq ⇒ every value fits within the clamp bound m = min(max ub, n) *)
Theorem vp_seq_clamp_sound[local]:
  valid_assignment bnd wi ∧ seq_precede_chain_sem Xs wi ⇒
  ∀X. MEM X Xs ⇒ varc wi X ≤ &(vp_seq_m bnd Xs)
Proof
  rw[]>>
  `∃jj. jj < LENGTH Xs ∧ X = EL jj Xs` by metis_tac[MEM_EL]>>
  `varc wi X ≤ FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs` by metis_tac[vp_seq_ub]>>
  `varc wi X ≤ &(LENGTH Xs)` by metis_tac[vp_seq_len_ub]>>
  simp[vp_seq_m_def]>>
  qabbrev_tac`cl = if FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs < 0 then 0
              else Num (FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs)`>>
  `varc wi X ≤ &cl` by (
    rw[Abbr`cl`]
    >- (qpat_x_assum`varc wi X ≤ FOLDR _ _ _`mp_tac>>
        qpat_x_assum`FOLDR _ _ _ < 0`mp_tac>>
        rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    `&(Num (FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs)) =
       FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs` by (
      `0 ≤ FOLDR (λX a. int_max (SND (varc_bnd bnd X)) a) 0 Xs` by
        (qpat_x_assum`¬(FOLDR _ _ _ < 0)`mp_tac>>rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
      metis_tac[integerTheory.INT_OF_NUM])>>
    pop_assum SUBST1_TAC>>fs[])>>
  rw[MIN_DEF]>>fs[]
QED

(* the emitted clamp constraints force every value within m *)
Theorem vp_seq_clamp_holds[local]:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_seq_precede_chain bnd Xs name) ⇒
  ∀X. MEM X Xs ⇒ varc wi X ≤ &(vp_seq_m bnd Xs)
Proof
  strip_tac>>
  fs[encode_seq_precede_chain_def]>>
  reverse(Cases_on`vp_seq_m bnd Xs < 1`)>>fs[]
  >- (
    reverse(Cases_on`vp_seq_m bnd Xs < 2`)>>fs[]
    >- (fs[EVERY_APPEND]>>rw[]>>fs[vp_clamp_sem])>>
    rw[]>>fs[vp_clamp_sem])>>
  rw[]>>
  `varc wi X ≤ 0` by metis_tac[vp_seq_zero_ub]>>
  `vp_seq_m bnd Xs = 0` by fs[]>>
  `(0:int) ≤ &(vp_seq_m bnd Xs)` by simp[]>>
  intLib.ARITH_TAC
QED

(* seq ⇒ value_precede on the chain 1..m (any m) *)
Theorem value_precede_of_seq[local]:
  seq_precede_chain_sem Xs wi ⇒
  value_precede_sem (GENLIST (λk. &(k+1)) m) Xs wi
Proof
  rw[value_precede_sem_def]>>
  `jj < LENGTH Xs` by fs[]>>
  `EL jj (MAP (varc wi) Xs) = varc wi (EL jj Xs)` by (irule EL_MAP>>fs[])>>
  `EL j (GENLIST (λk. &(k+1)) m) = &(j+1)` by (simp[EL_GENLIST]>>fs[])>>
  `varc wi (EL jj Xs) = &(j+1)` by fs[]>>
  `∃ii. ii < jj ∧ varc wi (EL ii Xs) = &(i+1)` by (
    drule vp_seq_back>>
    disch_then(qspecl_then[`j+1`,`jj`,`i+1`]mp_tac)>>
    disch_then irule>>fs[])>>
  qexists_tac`ii`>>
  `ii < LENGTH Xs` by fs[]>>
  `EL ii (MAP (varc wi) Xs) = varc wi (EL ii Xs)` by (irule EL_MAP>>fs[])>>
  `EL i (GENLIST (λk. &(k+1)) m) = &(i+1)` by (simp[EL_GENLIST]>>fs[])>>
  fs[]
QED

(* value_precede on 1..m gives the predecessor step for a clamped value *)
Theorem value_precede_seq_step[local]:
  value_precede_sem (GENLIST (λk. &(k+1)) m) Xs wi ∧
  j < LENGTH Xs ∧ 2 ≤ varc wi (EL j Xs) ∧ varc wi (EL j Xs) ≤ &m ⇒
  ∃i. i < j ∧ varc wi (EL i Xs) = varc wi (EL j Xs) − 1
Proof
  strip_tac>>
  qabbrev_tac`v = varc wi (EL j Xs)`>>
  `0 ≤ v` by intLib.ARITH_TAC>>
  `&(Num v) = v` by metis_tac[integerTheory.INT_OF_NUM]>>
  `2 ≤ Num v` by (`(2:int) ≤ &(Num v)` by metis_tac[]>>fs[integerTheory.INT_OF_NUM_LE])>>
  `Num v ≤ m` by (`&(Num v) ≤ &m` by metis_tac[]>>fs[integerTheory.INT_OF_NUM_LE])>>
  `EL j (MAP (varc wi) Xs) = varc wi (EL j Xs)` by (irule EL_MAP>>fs[])>>
  qpat_x_assum`value_precede_sem _ _ _`mp_tac>>
  simp[value_precede_sem_def]>>
  disch_then(qspecl_then[`Num v - 2`,`Num v - 1`]mp_tac)>>
  impl_tac >- fs[]>>
  disch_then(qspec_then`j`mp_tac)>>
  impl_tac >- (
    `Num v − 1 < m` by fs[]>>
    `EL (Num v − 1) (GENLIST (λk. &(k+1)) m) = &(Num v)` by
      (simp[EL_GENLIST]>>`Num v − 1 + 1 = Num v` by fs[]>>simp[])>>
    fs[])>>
  strip_tac>>
  qexists_tac`ii`>>
  `ii < LENGTH Xs` by fs[]>>
  `EL ii (MAP (varc wi) Xs) = varc wi (EL ii Xs)` by (irule EL_MAP>>fs[])>>
  `Num v − 2 < m` by fs[]>>
  `EL (Num v − 2) (GENLIST (λk. &(k+1)) m) = &(Num v − 1)` by
    (simp[EL_GENLIST]>>`Num v − 2 + 1 = Num v − 1` by fs[]>>simp[])>>
  `1 ≤ Num v` by fs[]>>
  `Num v − 2 + 1 = Num v − 1` by fs[]>>
  `&(Num v − 1) = &(Num v) − &1` by metis_tac[integerTheory.INT_SUB]>>
  fs[]>>
  `&Num v = v` by metis_tac[integerTheory.INT_OF_NUM]>>
  pop_assum SUBST_ALL_TAC>>simp[]
QED

Theorem encode_seq_precede_chain_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical (SeqPrecedeChain Xs)) ∧
  seq_precede_chain_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_seq_precede_chain bnd Xs name)
Proof
  strip_tac>>
  `∀X. MEM X Xs ⇒ varc wi X ≤ &(vp_seq_m bnd Xs)` by metis_tac[vp_seq_clamp_sound]>>
  `vp_reifies cs wi name Xs` by metis_tac[vp_reifies_seq_precede_chain]>>
  simp[encode_seq_precede_chain_def]>>
  IF_CASES_TAC >- simp[]>>
  IF_CASES_TAC
  >- (simp[vp_clamp_sem]>>metis_tac[])>>
  simp[EVERY_APPEND]>>
  reverse conj_tac
  >- (irule encode_value_precede_sem_1>>fs[]>>metis_tac[value_precede_of_seq])>>
  simp[vp_clamp_sem]>>metis_tac[]
QED

Theorem encode_seq_precede_chain_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_seq_precede_chain bnd Xs name) ⇒
  seq_precede_chain_sem Xs wi
Proof
  strip_tac>>
  `∀X. MEM X Xs ⇒ varc wi X ≤ &(vp_seq_m bnd Xs)` by metis_tac[vp_seq_clamp_holds]>>
  simp[seq_precede_chain_sem_def]>>
  rw[]>>
  `EL j (MAP (varc wi) Xs) = varc wi (EL j Xs)` by (irule EL_MAP>>fs[])>>
  `MEM (EL j Xs) Xs` by (simp[MEM_EL]>>metis_tac[])>>
  `2 ≤ varc wi (EL j Xs)` by fs[]>>
  `varc wi (EL j Xs) ≤ &(vp_seq_m bnd Xs)` by metis_tac[]>>
  `2 ≤ vp_seq_m bnd Xs` by (
    `(2:int) ≤ &(vp_seq_m bnd Xs)` by metis_tac[integerTheory.INT_LE_TRANS]>>
    fs[integerTheory.INT_OF_NUM_LE])>>
  `value_precede_sem (GENLIST (λk. &(k+1)) (vp_seq_m bnd Xs)) Xs wi` by (
    `¬(vp_seq_m bnd Xs < 1) ∧ ¬(vp_seq_m bnd Xs < 2)` by fs[]>>
    qpat_x_assum`EVERY _ (encode_seq_precede_chain _ _ _)`mp_tac>>
    fs[encode_seq_precede_chain_def,EVERY_APPEND]>>
    metis_tac[encode_value_precede_sem_2])>>
  `∃i. i < j ∧ varc wi (EL i Xs) = varc wi (EL j Xs) − 1` by
    metis_tac[value_precede_seq_step]>>
  qexists_tac`i`>>fs[EL_MAP]
QED

Theorem cencode_seq_precede_chain_sem:
  valid_assignment bnd wi ∧
  cencode_seq_precede_chain bnd Xs name ec = (es,ec') ⇒
  enc_rel wi es (encode_seq_precede_chain bnd Xs name) ec ec'
Proof
  rw[cencode_seq_precede_chain_def,encode_seq_precede_chain_def]>>
  pairarg_tac>>gvs[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  metis_tac[cencode_value_precede_sem]
QED

Definition encode_lexicographical_constr_def:
  encode_lexicographical_constr bnd c name =
  case c of
    Lex Zr cmp Xs Ys => encode_lex bnd Zr cmp Xs Ys name
  | ValuePrecede ch Xs => encode_value_precede bnd ch Xs name
  | SeqPrecedeChain Xs => encode_seq_precede_chain bnd Xs name
End

Theorem encode_lexicographical_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical c) ∧
  lexicographical_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lexicographical_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_lexicographical_constr_def,lexicographical_constr_sem_def]>>
  metis_tac[encode_lex_sem_1,encode_value_precede_sem_1,
    encode_seq_precede_chain_sem_1,vp_reifies_value_precede]
QED

Theorem encode_lexicographical_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lexicographical_constr bnd c name) ⇒
  lexicographical_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_lexicographical_constr_def,lexicographical_constr_sem_def]>>
  metis_tac[encode_lex_sem_2,encode_value_precede_sem_2,
    encode_seq_precede_chain_sem_2]
QED

Definition cencode_lexicographical_constr_def:
  cencode_lexicographical_constr bnd c name ec =
  case c of
    Lex Zr cmp Xs Ys => cencode_lex bnd Zr cmp Xs Ys name ec
  | ValuePrecede ch Xs => cencode_value_precede bnd ch Xs name ec
  | SeqPrecedeChain Xs => cencode_seq_precede_chain bnd Xs name ec
End

Theorem cencode_lexicographical_constr_sem:
  valid_assignment bnd wi ∧
  cencode_lexicographical_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_lexicographical_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  rw[cencode_lexicographical_constr_def,encode_lexicographical_constr_def]>>
  metis_tac[cencode_lex_constr_sem,cencode_value_precede_sem,
    cencode_seq_precede_chain_sem]
QED
