(*
  Formalization of the CP to ILP phase (lexicographical constraints)
*)
Theory cp_to_ilp_lexicographical
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

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

Definition encode_lexicographical_constr_def:
  encode_lexicographical_constr bnd c name =
  case c of Lex Zr cmp Xs Ys =>
    encode_lex bnd Zr cmp Xs Ys name
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
  metis_tac[encode_lex_sem_1]
QED

Theorem encode_lexicographical_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lexicographical_constr bnd c name) ⇒
  lexicographical_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_lexicographical_constr_def,lexicographical_constr_sem_def]>>
  metis_tac[encode_lex_sem_2]
QED

Definition cencode_lexicographical_constr_def:
  cencode_lexicographical_constr bnd c name ec =
  case c of Lex Zr cmp Xs Ys =>
    cencode_lex bnd Zr cmp Xs Ys name ec
End

Theorem cencode_lexicographical_constr_sem:
  valid_assignment bnd wi ∧
  cencode_lexicographical_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_lexicographical_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  rw[cencode_lexicographical_constr_def,encode_lexicographical_constr_def]>>
  metis_tac[cencode_lex_constr_sem]
QED
