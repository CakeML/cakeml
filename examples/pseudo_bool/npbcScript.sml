(*
  Formalisation of normalised pseudo-boolean constraints
*)
open preamble pbcTheory;

val _ = new_theory "npbc";

val _ = numLib.temp_prefer_num();

Type var = “:num”

(* Normalized pseudoboolean constraints (xs,n) represents constraint xs ≥ n
An additional compactness assumption guarantees uniqueness *)
Type npbc = ``: ((int # var) list) #num``

(* semantics *)
Definition b2n_def[simp]:
  b2n T = 1:num ∧
  b2n F = 0:num
End

Definition eval_lit_def[simp]:
  eval_lit w b (v:var) =
  if b
  then 1 - b2n (w v)
  else b2n (w v)
End

Definition eval_term_def[simp]:
  eval_term w (c,v) = Num (ABS c) * eval_lit w (c < 0) v
End

Definition satisfies_npbc_def:
  satisfies_npbc w (xs,n) ⇔ SUM (MAP (eval_term w) xs) ≥ n
End

(* Tentative representation of PBF as a set of constraints *)
Definition satisfies_def:
  satisfies w npbf ⇔
  ∀c. c ∈ npbf ⇒ satisfies_npbc w c
End

Definition satisfiable_def:
  satisfiable npbf ⇔
  ∃w. satisfies w npbf
End

Definition unsatisfiable_def:
  unsatisfiable npbf ⇔ ¬satisfiable npbf
End

Definition eval_obj_def:
  eval_obj fopt w =
    case fopt of NONE => 0
    | SOME (f,c:int) => &(SUM (MAP (eval_term w) f)) + c
End

(* Optimality of an assignment
  Here, the special case with no objective is treated as 0
*)
Definition optimal_def:
  optimal w npbf fopt ⇔
    satisfies w npbf ∧
    ∀w'.
      satisfies w' npbf ⇒
      eval_obj fopt w ≤ eval_obj fopt w'
End

Definition optimal_val_def:
  optimal_val npbf fopt =
    if satisfiable npbf then
      SOME (eval_obj fopt (@w. optimal w npbf fopt))
    else
      NONE
End

(* compactness *)

Definition compact_def[simp]:
  compact ((xs,n):npbc) ⇔
    SORTED $< (MAP SND xs) ∧ (* implies that no var is mentioned twice *)
    EVERY (λc. c ≠ 0) (MAP FST xs)
End

(* addition -- implementation *)
Definition offset_def:
  offset c1 c2 =
  if (c1 < 0) = (c2 < 0) then 0 else
  let a1 = Num (ABS c1) in
  let a2 = Num (ABS c2) in
  if a1 <= a2 then a1 else a2
End

Definition add_terms_def:
  add_terms c1 c2 v zs (k:num) =
  let c = c1 + c2 in
  if c = 0 then (zs, k + Num(ABS c1))
  else
    ((c,v)::zs, k+ offset c1 c2)
End

Definition add_lists_def:
  add_lists [] [] = ([],0) ∧
  add_lists xs [] = (xs,0) ∧
  add_lists [] ys = (ys,0) ∧
  add_lists ((c,x)::xs) ((d,y)::ys) =
    if x < y then
      let (zs,n) = add_lists xs ((d,y)::ys) in
        ((c,x)::zs,n)
    else if y < x then
      let (zs,n) = add_lists ((c,x)::xs) ys in
        ((d,y)::zs,n)
    else (* x = y *)
      let (zs,n2) = add_lists xs ys in
        add_terms c d x zs n2
End

Definition add_def:
  add (xs,m) (ys,n) =
    let (xs,d) = add_lists xs ys in
      (xs,((m + n) - d))
End

(* addition -- proof *)

Theorem add_terms_thm:
  add_terms x y v zs k = (zs1,d) ⇒
  eval_term w (x,v) + eval_term w (y,v) + SUM (MAP (eval_term w) zs) + k =
  SUM (MAP (eval_term w) zs1) + d
Proof
  rw[add_terms_def,AllCaseEqs(),offset_def]>>
  Cases_on`x`>>Cases_on`y`>>gvs[]>>
  TRY (
    fs[integerTheory.INT_ADD_CALCULATE]>>
    Cases_on`w v`>>gs[]>> NO_TAC)
  >- (
   Cases_on`w v`>>gs[]>>
   intLib.ARITH_TAC)>>
  `n < n'` by intLib.ARITH_TAC>>
  simp[integerTheory.INT_ADD_CALCULATE]>>
  Cases_on`w v`>>gs[]
QED

Theorem add_lists_thm:
  ∀x y zs d.
    add_lists x y = (zs,d) ⇒
    SUM (MAP (eval_term w) x) + SUM (MAP (eval_term w) y) =
    SUM (MAP (eval_term w) zs) + d
Proof
  ho_match_mp_tac add_lists_ind \\ rw [] \\ gvs [add_lists_def]
  \\ Cases_on ‘x < y’ \\ fs []
  \\ Cases_on ‘y < x’ \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ `x = y` by gs[]
  \\ drule_all add_terms_thm
  \\ disch_then (qspec_then ‘w’ assume_tac)
  \\ gs [SUM_APPEND]
QED

Theorem add_thm:
  satisfies_npbc w c1 ∧ satisfies_npbc w c2 ⇒ satisfies_npbc w (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’ \\ fs [add_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [satisfies_npbc_def]
  \\ drule_all add_lists_thm
  \\ disch_then (qspec_then ‘w’ assume_tac)
  \\ fs []
QED

(* addition -- compactness *)

Triviality add_lists_sorted_lemma:
  ∀l1 l2 h t d x.
    add_lists l1 l2 = (h::t,d) ∧
    SORTED $< (x::MAP SND l1) ∧
    SORTED $< (x::MAP SND l2) ⇒
    x < SND h
Proof
  ho_match_mp_tac add_lists_ind \\ rpt strip_tac
  \\ fs [add_lists_def]
  THEN1 gvs []
  THEN1 gvs []
  \\ Cases_on ‘x < y’ \\ fs []
  \\ Cases_on ‘y < x’ \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE]
  \\ ‘x = y’ by fs [] \\ gvs []
  \\ last_x_assum drule_all \\ fs []
QED

Theorem add_lists_sorted:
   ∀l l' xs d.
     EVERY (λc. c ≠ 0) (MAP FST l) ∧ EVERY (λc. c ≠ 0) (MAP FST l') ∧
     SORTED $< (MAP SND l) ∧ SORTED $< (MAP SND l') ∧
     add_lists l l' = (xs,d) ⇒
     SORTED $< (MAP SND xs) ∧ EVERY (λc. c ≠ 0) (MAP FST xs)
Proof
  ho_match_mp_tac add_lists_ind
  \\ REVERSE (rpt strip_tac)
  \\ fs [add_lists_def] \\ gvs []
  \\ imp_res_tac SORTED_TL
  THEN1
   (Cases_on ‘x < y’ \\ fs [] THEN1 (pairarg_tac \\ gvs [])
    \\ Cases_on ‘y < x’ \\ fs [] THEN1 (pairarg_tac \\ gvs [])
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE])
  \\ Cases_on ‘x < y’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
    \\ drule add_lists_sorted_lemma \\ fs [])
  \\ Cases_on ‘y < x’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
    \\ drule add_lists_sorted_lemma \\ fs [])
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE]
  \\ Cases_on ‘zs’ \\ fs []
  \\ ‘x = y’ by fs [] \\ gvs []
  \\ drule_all add_lists_sorted_lemma
  \\ Cases_on ‘h’ \\ fs []
QED

Theorem compact_add:
  compact c1 ∧ compact c2 ⇒ compact (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’ \\ fs [add_def]
  \\ pairarg_tac \\ fs [] \\ metis_tac [add_lists_sorted]
QED

(* faster version of add_lists *)

Definition add_lists'_def:
  add_lists' xs ys zs n =
    case xs of
    | [] => (REV zs ys,n)
    | (x::xs1) =>
    case ys of
    | [] => (REV zs xs,n)
    | (y::ys1) =>
      let (cx,xn) = x in
      let (cy,yn) = y in
        if xn < yn then add_lists' xs1 ys (x::zs) n else
        if yn < xn then add_lists' xs ys1 (y::zs) n else
          let (zs1,n1) = add_terms cx cy xn zs n in
            add_lists' xs1 ys1 zs1 n1
End

Theorem add_lists'_thm:
  add_lists xs ys = add_lists' xs ys [] 0
Proof
  qsuff_tac ‘∀xs ys zs n.
    add_lists' xs ys zs n =
      let (zs0,n0) = add_lists xs ys in
        (REVERSE zs ++ zs0, n0+n)’
  >- (fs [] \\ pairarg_tac \\ fs [])
  \\ ho_match_mp_tac add_lists'_ind
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [add_lists'_def]
  \\ Cases_on ‘xs’ \\ fs [add_lists_def,REV_REVERSE_LEM]
  \\ Cases_on ‘ys’ \\ fs [add_lists_def,REV_REVERSE_LEM]
  \\ rename [‘add_lists (h1::_) (h2::_)’]
  \\ PairCases_on ‘h1’ \\ PairCases_on ‘h2’ \\ fs []
  \\ fs [add_lists_def,REV_REVERSE_LEM]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [DefnBase.one_line_ify NONE add_terms_def,AllCaseEqs()]
QED

(* division *)
Definition IQ_def:
  IQ (i:int) (j:int) =
       if 0 < j then
         if 0 ≤ i then &(Num i DIV Num j):int else -&(Num (-i) DIV Num j)
       else if 0 ≤ i then -&(Num i DIV Num (-j))
       else &(Num (-i) DIV Num (-j))
End

Definition div_ceiling_def:
  div_ceiling (m:int) (n:num) =
    IQ
      (if m < 0
      then m-(&n-1)
      else m+ (&n - 1)) &n
End

Theorem IQ_quot:
  j ≠ 0 ⇒
  IQ i j = i quot j
Proof
  simp[integerTheory.int_quot,IQ_def]
QED

Theorem div_ceiling_compute:
  k ≠ 0 ⇒
  div_ceiling (&n) k = & (n \\ k) ∧
  div_ceiling (-&n) k = - & (n \\ k)
Proof
  fs [div_ceiling_def,CEILING_DIV_def,IQ_quot] \\ rw []
  \\ Cases_on ‘k’ \\ fs []
  \\ fs [ADD1,integerTheory.INT_ADD_CALCULATE,
         integerTheory.INT_SUB_CALCULATE,DIV_EQ_X]
  \\ rw []
  \\ fs [ADD1,integerTheory.INT_ADD_CALCULATE,
         integerTheory.INT_SUB_CALCULATE,DIV_EQ_X]
  \\ qmatch_goalsub_abbrev_tac ‘_ DIV k’
  \\ ‘0 < k’ by fs [Abbr‘k’]
  \\ drule DIVISION
  \\ disch_then $ qspec_then ‘n+n'’ mp_tac
  \\ drule DIVISION
  \\ disch_then $ qspec_then ‘n’ mp_tac
  \\ strip_tac
  \\ rewrite_tac [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
  \\ decide_tac
QED

Theorem div_ceiling_sign:
  n ≠ 0 ⇒
  (div_ceiling m n < 0 ⇔ m < 0)
Proof
  Cases_on`m` \\ fs[div_ceiling_compute,IQ_quot]
  \\ fs [CEILING_DIV]
  \\ rw [] \\ Cases_on ‘1 < n’
  \\ gvs [DIV_EQ_0]
  \\ ‘n = 1’ by fs [] \\ fs []
QED

Theorem DIV_CEILING_EQ_0:
  n ≠ 0 ⇒ (m \\ n = 0 ⇔ m = 0)
Proof
  fs [CEILING_DIV,IQ_quot]
  \\ Cases_on ‘m = 0’ \\ fs [ZERO_DIV]
  \\ rw [] \\ Cases_on ‘1 < n’
  \\ gvs [DIV_EQ_0]
  \\ ‘n = 1’ by fs [] \\ fs []
QED

Definition divide_def:
  divide ((l,n):npbc) k =
    (MAP (λ(c,v). (div_ceiling c k, v)) l,n \\ k)
End

Theorem divide_thm:
  satisfies_npbc w c ∧ k ≠ 0 ⇒ satisfies_npbc w (divide c k)
Proof
  Cases_on ‘c’ \\ fs [divide_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ,CEILING_DIV_LE_X]
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ Induct_on ‘q’ \\ fs [FORALL_PROD]
  \\ fs [LEFT_ADD_DISTRIB] \\ rw []
  \\ irule (DECIDE “m ≤ m1 ∧ n ≤ n1 ⇒ m+n ≤ m1+n1:num”)
  \\ fs[] \\ Cases_on ‘p_1’ \\ gvs [div_ceiling_compute,DIV_CEILING_EQ_0]
  \\ fs [LE_MULT_CEILING_DIV]
QED

Theorem div_ceiling_eq_0:
  k ≠ 0 ⇒ (div_ceiling c k = 0 ⇔ c = 0)
Proof
  fs [div_ceiling_def,IQ_quot]
  \\ Cases_on ‘c = 0’ \\ fs []
  \\ Cases_on ‘k’
  \\ fs [ADD1,integerTheory.INT_ADD_CALCULATE,
         integerTheory.INT_SUB_CALCULATE,DIV_EQ_X]
  \\ Cases_on ‘c’
  \\ fs [ADD1,integerTheory.INT_ADD_CALCULATE,
         integerTheory.INT_SUB_CALCULATE,DIV_EQ_X]
  \\ rw []
  \\ fs [ADD1,integerTheory.INT_ADD_CALCULATE,
         integerTheory.INT_SUB_CALCULATE,DIV_EQ_X]
QED

Theorem compact_divide:
  compact c ∧ k ≠ 0 ⇒ compact (divide c k)
Proof
  Cases_on`c` \\
  rename1`(l,r)` \\
  rw[compact_def,divide_def]
  THEN1 (Induct_on `l` \\ fs [FORALL_PROD]
    \\ Cases_on ‘l’ \\ fs []
    \\ Cases_on ‘t’ \\ fs []
    \\ PairCases_on ‘h’ \\ fs [])
  \\ fs[EVERY_MAP,EVERY_MEM]
  \\ rw[] \\ first_x_assum drule
  \\ pairarg_tac \\ fs[]
  \\ fs[div_ceiling_eq_0]
QED

(* negation *)

Definition not_def:
  not ((l,n):npbc) =
    (MAP (λ(c,l). (-c,l)) l,
      SUM (MAP (λi. Num (ABS (FST i))) l) + 1 - n)
End

Theorem ADD_SUB:
  B ≥ C ⇒
  A + (B - C) = A + B - C
Proof
  rw[]
QED

Theorem ABS_coeff_ge:
  SUM (MAP (λi. Num (ABS (FST i))) l) ≥ SUM (MAP (eval_term w) l)
Proof
  Induct_on`l`>>fs[FORALL_PROD]>>rw[]
  \\ Cases_on ‘w p_2’ \\ fs []
QED

Theorem not_lhs:
  SUM (MAP (eval_term w) (MAP (λ(c,l). (-c,l)) l)) =
  SUM (MAP (λi. Num (ABS (FST i))) l) -
  SUM (MAP (eval_term w) l)
Proof
  Induct_on`l`>>fs[FORALL_PROD]>>rw[]
  >- intLib.ARITH_TAC
  \\ Cases_on ‘w p_2’ \\ fs []
  \\ TRY (last_x_assum (fn th => rewrite_tac [GSYM th]) \\ gvs [] \\ NO_TAC)
  \\ Cases_on ‘p_1’ \\ gvs []
  \\ DEP_REWRITE_TAC[ADD_SUB]
  \\ metis_tac[ABS_coeff_ge]
QED

Theorem not_thm:
  satisfies_npbc w (not c) ⇔ ~satisfies_npbc w c
Proof
  Cases_on ‘c’ \\ fs [not_def,satisfies_npbc_def,GREATER_EQ]
  \\ simp[not_lhs]
  \\ DEP_REWRITE_TAC[ADD_SUB]
  \\ simp[ABS_coeff_ge]
QED

Theorem compact_not:
  compact c ⇒ compact (not c)
Proof
  Cases_on ‘c’ \\
  rename1`(l,r)` \\
  reverse (rw [not_def,compact_def])
  THEN1 gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘t’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
QED

(* multiplication *)

Definition multiply_def:
  multiply ((l,n):npbc) k =
    if k = 0 then ([],0) else
      (MAP (λ(c,v). (c * & k, v)) l,n * k)
End

Theorem multiply_thm:
  satisfies_npbc w c ⇒ satisfies_npbc w (multiply c k)
Proof
  Cases_on ‘c’ \\
  rename1`(l,r)` \\ fs [multiply_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ drule LESS_MONO_MULT
  \\ disch_then (qspec_then`k` mp_tac)
  \\ REWRITE_TAC [Once MULT_COMM]
  \\ strip_tac
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ pop_assum kall_tac
  \\ Induct_on`l` \\ simp[] \\ Cases \\ rw[]
  \\ Cases_on ‘q’ \\ gvs []
  \\ fs [ADD1,integerTheory.INT_MUL_CALCULATE]
  \\ Cases_on ‘k’ \\ fs [MULT_CLAUSES,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
QED

Theorem compact_multiply:
  compact c ⇒ compact (multiply c k)
Proof
  Cases_on ‘c’ \\
  rename1`(l,r)` \\
  reverse (rw [multiply_def,compact_def])
  THEN1 gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘t’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
QED

(* saturation *)
Definition abs_min_def:
  abs_min c n =
  if Num(ABS c)  ≤ n then
    c
  else if c < 0 then -&n else &n
End

Definition saturate_def:
  saturate (l,n) =
    if n = 0 then ([],n)
    else (MAP (λ(c,v). (abs_min c n, v)) l, n)
End

Theorem eval_lit_bool:
  eval_lit w r n = 0 ∨ eval_lit w r n = 1
Proof
  Cases_on`r` \\ rw[eval_lit_def]
  \\ Cases_on`w n` \\ rw[b2n_def]
QED

Theorem saturate_thm:
  satisfies_npbc w c ⇒ satisfies_npbc w (saturate c)
Proof
  Cases_on ‘c’ \\ rename1`(l,n)` \\ fs [saturate_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ `∀a.
      n ≤ SUM (MAP (eval_term w) l) + a ⇒
      n ≤ SUM (MAP (eval_term w) (MAP (λ(c,v). (abs_min c n,v)) l)) + a` by (
    pop_assum kall_tac
    \\ Induct_on`l` \\ simp[] \\ Cases
    \\ simp[]
    \\ rw[]
    \\ ONCE_REWRITE_TAC[ADD_COMM]
    \\ ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    \\ first_x_assum match_mp_tac
    \\ fs[abs_min_def]
    \\ rw[] >> fs[]
    \\ Cases_on`w r` \\ fs[b2n_def]
    \\ rfs[] )
  \\ pop_assum (qspec_then`0` assume_tac) \\ fs[]
QED

Theorem compact_saturate:
  compact c ⇒ compact (saturate c)
Proof
  Cases_on ‘c’ \\  rename1`(l,n)` \\
  reverse (rw [saturate_def,compact_def])
  THEN1 (
    gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] \\
    rw[abs_min_def] )
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘t’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
QED

(*
Definition weaken_aux_def:
  (weaken_aux v [] n = ([],n)) ∧
  (weaken_aux v ((c:int,l)::xs) n =
    let (xs',n') = weaken_aux v xs n in
     if l = v then
      (xs',n'-Num(ABS c))
    else
      ((c,l)::xs',n'))
End
*)

(* List weakening
  assumes the constraint is compact
  weakens the vs in order *)
Definition weaken_aux_def:
  (weaken_aux vs [] n = ([],n)) ∧
  (weaken_aux [] xs n = (xs,n)) ∧
  (weaken_aux (v::vs) ((c:int,l)::xs) n =
    if l = v then
      weaken_aux vs xs (n-Num(ABS c))
    else
    let (xs',n') = weaken_aux (v::vs) xs n in
      ((c,l)::xs',n'))
End

(* weakening *)
Definition weaken_def:
  weaken (l,n) vs = weaken_aux vs l n
End

Theorem weaken_aux_theorem:
  ∀vs l n l' n' a.
  n ≤ SUM (MAP (eval_term w) l) + a ∧
  weaken_aux vs l n = (l',n') ⇒
  n' ≤ SUM (MAP (eval_term w) l') + a
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`SUM A`
  \\ TRY(qmatch_goalsub_abbrev_tac`B + SUM A`)
  \\ TRY(qmatch_goalsub_abbrev_tac`SUM A + B`)
  >- (
    qmatch_goalsub_abbrev_tac` _ ≤ rhs`
    \\ `rhs = (a + B) + SUM A` by
      (unabbrev_all_tac>>
      simp[])
    \\ pop_assum SUBST1_TAC
    \\ first_x_assum match_mp_tac
    \\ fs[])
  >- (
    first_x_assum irule
    \\ Cases_on`w l`
    \\ gvs[])
  \\ qmatch_goalsub_abbrev_tac` _ ≤ rhs`
  \\ `rhs = (a + B) + SUM A` by
    (unabbrev_all_tac>>
    simp[])
  \\ pop_assum SUBST1_TAC
  \\ fs[]
QED

(* set a = 0 *)
val weaken_aux_theorem0 =
  weaken_aux_theorem |>
  CONV_RULE (RESORT_FORALL_CONV (sort_vars ["a"])) |>
  Q.SPEC`0` |> SIMP_RULE std_ss [];

Theorem weaken_thm:
  satisfies_npbc w c ⇒ satisfies_npbc w (weaken c v)
Proof
  Cases_on ‘c’ \\ fs [weaken_def]
  \\ Cases_on`weaken_aux v q r`
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ match_mp_tac weaken_aux_theorem0
  \\ metis_tac[]
QED

Theorem weaken_aux_contains:
  ∀vs ls n ls' n' x.
  weaken_aux vs ls n = (ls',n') ∧
  MEM x ls' ⇒ MEM x ls
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ gvs[]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[]
QED

Theorem SORTED_weaken_aux:
  ∀vs ls n ls' n'.
  SORTED $< (MAP SND ls) ∧
  weaken_aux vs ls n = (ls',n') ⇒
  SORTED $< (MAP SND ls')
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  >-
    metis_tac[SORTED_TL]
  \\ qpat_x_assum `SORTED _ (_ :: _)` mp_tac
  \\ DEP_REWRITE_TAC [SORTED_EQ] \\ rw[]
  \\ drule weaken_aux_contains
  \\ metis_tac[MEM_MAP]
QED

Theorem compact_weaken:
  compact c ⇒ compact (weaken c v)
Proof
  Cases_on ‘c’ \\ rw[weaken_def]
  \\ Cases_on`weaken_aux v q r`
  \\ rw[]
  >-
    metis_tac[SORTED_weaken_aux]
  \\ fs[EVERY_MEM,FORALL_PROD]
  \\ metis_tac[weaken_aux_contains,MEM_MAP]
QED

(* clean up *)

Definition partition_def:
  partition [] ys zs = (ys,zs) ∧
  partition (x::xs) ys zs = partition xs zs (x::ys)
End

Theorem partition_length:
  ∀xs ys zs ys1 zs1.
    (ys1,zs1) = partition xs ys zs ⇒
    LENGTH ys1 + LENGTH zs1 = LENGTH xs + LENGTH zs + LENGTH ys ∧
    (ys ≠ [] ∧ zs ≠ [] ⇒ ys1 ≠ [] ∧ zs1 ≠ [])
Proof
  Induct \\ rw [partition_def]
  \\ last_x_assum drule \\ fs []
QED

Theorem partition_sum:
  ∀xs ys zs ys1 zs1.
    partition xs ys zs = (ys1,zs1) ⇒
    SUM (MAP (eval_term w) xs) + SUM (MAP (eval_term w) ys) + SUM (MAP (eval_term w) zs) =
    SUM (MAP (eval_term w) ys1) + SUM (MAP (eval_term w) zs1)
Proof
  Induct \\ rw [partition_def] \\ res_tac \\ fs []
QED

Definition clean_up_def:
  clean_up [] = ([],0) ∧
  clean_up [x] = ([x],0) ∧
  clean_up (x::y::xs) =
    let (ys,zs) = partition xs [x] [y] in
    let (ys1,k1) = clean_up ys in
    let (ys2,k2) = clean_up zs in
    let (res,k3) = add_lists ys1 ys2 in
      (res,k1+k2+k3)
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ drule partition_length \\ fs []
  \\ Cases_on ‘ys’ \\ Cases_on ‘zs’ \\ fs []
End

Theorem clean_up_thm:
  ∀xs ys d.
    clean_up xs = (ys,d) ⇒
    SUM (MAP (eval_term w) xs) = SUM (MAP (eval_term w) ys) + d
Proof
  ho_match_mp_tac clean_up_ind \\ rw []
  \\ gvs [clean_up_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_then (qspec_then ‘w’ assume_tac) partition_sum
  \\ drule_then (qspec_then ‘w’ assume_tac) add_lists_thm
  \\ gvs []
QED

Theorem EVERY_partition:
  ∀xs ys zs ys1 zs1 P.
    partition xs ys zs = (ys1,zs1) ∧ EVERY P xs ∧ EVERY P ys ∧ EVERY P zs ⇒
    EVERY P ys1 ∧ EVERY P zs1
Proof
  Induct \\ rw [partition_def]
  \\ res_tac \\ fs []
QED

Theorem clean_up_sorted:
  ∀xs ys d.
    clean_up xs = (ys,d) ∧ EVERY (λc. c ≠ 0) (MAP FST xs) ⇒
    SORTED $< (MAP SND ys) ∧ EVERY (λc. c ≠ 0) (MAP FST ys)
Proof
  ho_match_mp_tac clean_up_ind \\ rw []
  \\ gvs [clean_up_def]
  \\ rpt (pairarg_tac \\ full_simp_tac std_ss []) \\ gvs []
  \\ simp[EVERY_MAP]
  \\ imp_res_tac EVERY_partition \\ gvs []
  \\ fs[AND_IMP_INTRO]
  \\ drule_at (Pos last) add_lists_sorted
  \\ ntac 2 (last_x_assum mp_tac)
  \\ fs[EVERY_MAP]
QED

(* substitution/instantiation *)

Definition assign_def:
  assign f (w:num->bool) (n:num) =
    case f n of
    | NONE => w n
    | SOME (INL b) => b            (* concrete value b *)
    | SOME (INR (Pos v)) =>   w v  (* subst with var v *)
    | SOME (INR (Neg v)) => ~ w v  (* subst with negation of var v *)
End

Definition is_Pos_def[simp]:
  is_Pos (i:int) = (0 ≤ i)
End

Definition subst_aux_def:
  subst_aux f [] = ([],[],0) ∧
  subst_aux f ((c,l)::rest) =
    let (old,new,k) = subst_aux f rest in
      case f l of
      | NONE => ((c,l)::old,new,k)
      | SOME (INL b) => (old,new,if is_Pos c = b then k + Num (ABS c) else k)
      | SOME (INR (Pos n)) => (old,(c,n)::new,k)
      | SOME (INR (Neg n)) => (old,(0-c,n)::new,k)
End

Definition subst_lhs_def:
  subst_lhs f l =
    let (old,new,k) = subst_aux f l in
    let (sorted,k2) = clean_up new in
    let (result,k3) = add_lists old sorted in
    (result, k + k2 + k3)
End

Definition subst_def:
  subst f (l,n) =
  let (result,k) = subst_lhs f l in
      (result, n - k)
End

Theorem subst_lhs_thm:
  subst_lhs f l = (result,k) ⇒
  SUM (MAP (eval_term (assign f w)) l) =
  SUM (MAP (eval_term w) result) + k
Proof
  fs [subst_lhs_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rw[]
  \\ qsuff_tac
    ‘∀l old new k.
        subst_aux f l = (old,new,k) ⇒
        SUM (MAP (eval_term (assign f w)) l) =
        k + SUM (MAP (eval_term w) old ++ MAP (eval_term w) new)’
  >- (
    disch_then $ drule_then assume_tac \\ fs [SUM_APPEND]
    \\ drule_then (qspec_then ‘w’ assume_tac) clean_up_thm
    \\ drule_then (qspec_then ‘w’ assume_tac) add_lists_thm
    \\ gvs [])
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD]
  \\ pairarg_tac \\ fs []
  \\ rw []
  \\ Cases_on ‘p_1’   \\ gvs []
  \\ every_case_tac \\ gvs [assign_def]
  \\ fs[SUM_APPEND]
  \\ rename1`b2n (w a)`
  \\ Cases_on ‘w a’ \\ fs [SUM_APPEND]
QED

Theorem subst_thm:
  satisfies_npbc w (subst f c) = satisfies_npbc (assign f w) c
Proof
  Cases_on ‘c’ \\
  rename1‘(l,n)’ \\
  fs [satisfies_npbc_def,subst_def] \\
  pairarg_tac \\ fs[] \\
  drule subst_lhs_thm \\ strip_tac \\
  simp[satisfies_npbc_def]
QED

Definition subst_opt_aux_acc_def:
  subst_opt_aux_acc f [] a1 a2 k same =
    (if same then ([],[],k,T) else (REVERSE a1,REVERSE a2,k,same)) ∧
  subst_opt_aux_acc f ((c,l)::rest) a1 a2 k same =
    case f l of
    | NONE =>
        subst_opt_aux_acc f rest ((c,l)::a1) a2 k same
    | SOME (INL b) =>
      if is_Pos c = b then
        subst_opt_aux_acc f rest a1 a2 (k + Num (ABS c)) same
      else
        subst_opt_aux_acc f rest a1 a2 k F
    | SOME (INR (Pos n)) =>
        subst_opt_aux_acc f rest a1 ((c,n)::a2) k F
    | SOME (INR (Neg n)) =>
        subst_opt_aux_acc f rest a1 ((0-c,n)::a2) k F
End

(* The returned flag is T if any literal touched by the
    constraint is itself assigned to T under the substitution *)
Definition subst_opt_aux_def:
  subst_opt_aux f [] = ([],[],0,T) ∧
  subst_opt_aux f ((c,l)::rest) =
    let (old,new,k,same) = subst_opt_aux f rest in
      case f l of
      | NONE => ((c,l)::old,new,k,same)
      | SOME (INL b) =>
        if is_Pos c = b then
          (old,new, k + Num (ABS c), same)
        else
          (old,new, k, F)
      | SOME (INR (Pos n)) => (old,(c,n)::new,k,F)
      | SOME (INR (Neg n)) => (old,(0-c,n)::new,k,F)
End

Theorem subst_opt_aux_acc:
  ∀xs f a1 a2 k b.
    subst_opt_aux_acc f xs a1 a2 k b =
      let (x1,x2,k1,b1) = subst_opt_aux f xs in
        if b ∧ b1 then  ([],[],k + k1, b ∧ b1) else
          (REVERSE a1 ++ x1, REVERSE a2 ++ x2, k + k1, b ∧ b1)
Proof
  Induct
  \\ fs [subst_opt_aux_acc_def,subst_opt_aux_def,FORALL_PROD]
  \\ rw [] \\ CASE_TAC \\ fs []
  >- rpt (pairarg_tac \\ gvs [] \\ IF_CASES_TAC \\ fs [])
  \\ CASE_TAC \\ fs []
  >- (IF_CASES_TAC \\ fs [] \\ rpt (pairarg_tac \\ gvs []))
  \\ CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
QED

(* Computes the LHS term of the slack of a constraint under
   a partial assignment p (list of literals) *)
Definition lslack_def:
  lslack ls =
  SUM (MAP (Num o ABS o FST) ls)
End

Definition check_contradiction_def:
  check_contradiction ((ls,num):npbc) ⇔
    lslack ls < num
End

Theorem lslack_thm:
  ∀l. SUM (MAP (eval_term w) l) ≤ lslack l
Proof
  Induct \\ gvs [lslack_def,FORALL_PROD]
  \\ rw [] \\ Cases_on ‘w p_2’ \\ gvs []
QED

Theorem check_contradiction_unsat:
  check_contradiction c ⇒
  ¬satisfies_npbc w c
Proof
  Cases_on`c`>>
  rename1`(l,n)`>>
  rw[check_contradiction_def,satisfies_npbc_def,GREATER_EQ,GSYM NOT_LESS]>>
  irule LESS_EQ_LESS_TRANS >>
  pop_assum $ irule_at Any >>
  fs [lslack_thm]
QED

(* constraint c1 implies constraint c2 *)
Definition imp_def:
  imp c1 c2 ⇔
  check_contradiction (add c1 (not c2))
End

Theorem imp_thm:
  imp c1 c2 ∧
  satisfies_npbc w c1 ⇒ satisfies_npbc w c2
Proof
  rw[imp_def]>>
  drule add_thm>>
  strip_tac>>
  CCONTR_TAC>>
  fs[GSYM not_thm]>>
  first_x_assum drule>>
  drule check_contradiction_unsat>>
  metis_tac[]
QED

Definition subst_opt_def:
  subst_opt f (l,n) =
    let (old,new,k,same) = subst_opt_aux_acc f l [] [] 0 T in
      if same then NONE else
        let (sorted,k2) = clean_up new in
        let (result,k3) = add_lists old sorted in
        let res = (result,n - (k + k2 + k3)) in
        if SND res = 0 ∨ imp (l,n) res then NONE
        else SOME res
End

Theorem subst_opt_eq:
  subst_opt f (l,n) =
    let (old,new,k,same) = subst_opt_aux f l in
      if same then NONE else
        let (sorted,k2) = clean_up new in
        let (result,k3) = add_lists old sorted in
        let res = (result,n - (k + k2 + k3)) in
        if SND res = 0 ∨ imp (l,n) res then NONE
        else SOME res
Proof
  fs [subst_opt_aux_acc,subst_opt_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ ‘same = same'’ by (every_case_tac \\ fs [])
  \\ gvs [] \\ IF_CASES_TAC \\ gvs []
QED

Theorem subst_opt_aux_thm_1:
  ∀rest f old new k same.
    subst_opt_aux f rest = (old,new,k,same) ⇒
    subst_aux f rest = (old,new,k)
Proof
  Induct \\ fs [FORALL_PROD,subst_aux_def,subst_opt_aux_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ gvs []
  \\ CCONTR_TAC \\ gvs []
QED

Theorem subst_opt_SOME:
  subst_opt f c = SOME v ⇒ v = subst f c
Proof
  Cases_on ‘c’ \\ fs [subst_opt_eq,subst_def,subst_lhs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule_all subst_opt_aux_thm_1
  \\ rw [] \\ gvs []
QED

Theorem subst_opt_aux_thm_2:
  ∀rest f old new k.
  subst_opt_aux f rest = (old,new,k,T) ⇒
  SUM (MAP (eval_term (assign f w)) rest) ≥ SUM (MAP (eval_term w) rest)
Proof
  Induct \\ fs[FORALL_PROD,subst_opt_aux_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [AllCaseEqs()]
  \\ Cases_on ‘p_1’ \\ gvs []
  \\ first_x_assum drule
  \\ gvs [assign_def]
  \\ Cases_on`w p_2` \\ gvs [assign_def]
QED

Theorem subst_opt_NONE:
  subst_opt f c = NONE ⇒
  satisfies_npbc w c ⇒ satisfies_npbc w (subst f c)
Proof
  Cases_on ‘c’ \\ fs [subst_opt_eq]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw[]
  >- (
    fs[subst_thm]
    \\ fs[satisfies_npbc_def]
    \\ drule subst_opt_aux_thm_2
    \\ disch_then(qspec_then`w` assume_tac)
    \\ intLib.ARITH_TAC)
  >- (
    simp[subst_def,subst_lhs_def]>>
    rpt (pairarg_tac \\ fs [])>>
    drule subst_opt_aux_thm_1>>
    rw[]>>fs[]>>rw[]>>
    gvs[satisfies_npbc_def]>>
    gvs[])
  >- (
    simp[subst_def,subst_lhs_def]>>
    rpt (pairarg_tac \\ fs [])>>
    drule subst_opt_aux_thm_1>>
    rw[]>>fs[]>>rw[]>>
    drule imp_thm>>
    disch_then drule>>
    fs[])
QED

(* subst is compact *)

Theorem compact_subst:
  compact c ⇒ compact (subst f c)
Proof
  Cases_on ‘c’ \\
  rename1`(l,n)` \\
  fs [compact_def,subst_def,subst_lhs_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac
  \\ qsuff_tac ‘∀l old new k.
       SORTED $< (MAP SND l) ∧ EVERY (λc. c ≠ 0) (MAP FST l) ∧ subst_aux f l = (old,new,k) ⇒
       SORTED $< (MAP SND old) ∧ EVERY (λc. c ≠ 0) (MAP FST old) ∧ EVERY (λc. c ≠ 0) (MAP FST new)’
  THEN1
   (disch_then drule \\ fs [] \\ strip_tac
    \\ drule clean_up_sorted \\ fs [] \\ strip_tac
    \\ drule_all add_lists_sorted \\ fs [])
  \\ rpt (pop_assum kall_tac)
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on ‘f p_2’ \\ gvs []
  \\ imp_res_tac sortingTheory.SORTED_TL \\ gvs [AllCaseEqs()]
  \\ Cases_on ‘old'’ \\ fs []
  \\ qpat_x_assum ‘subst_aux f l = (h::t,new,k)’ mp_tac
  \\ qpat_x_assum ‘SORTED $< (p_2::MAP SND l)’ mp_tac
  \\ EVERY (map qid_spec_tac [‘p_1’,‘p_2’,‘t’,‘h’,‘new’,‘k’,‘l’])
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ Cases_on ‘f p_2'’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
  \\ first_x_assum irule
  \\ Cases_on ‘l'’ \\ fs []
  \\ every_case_tac \\ gvs []
QED

Definition sat_implies_def:
  sat_implies npbf npbf' ⇔
  ∀w. satisfies w npbf ⇒ satisfies w npbf'
End

Overload "⊨" = “sat_implies”
Overload "⇂" = “λf w. IMAGE (subst w) f”

val _ = set_fixity "redundant_wrt" (Infixl 500);
val _ = set_fixity "⊨" (Infixl 500);
val _ = set_fixity "⇂" (Infixl 502);

Definition redundant_wrt_def:
  c redundant_wrt f ⇔ (satisfiable f ⇔ satisfiable (f ∪ {c}))
End

Theorem satisfies_simp[simp]:
  satisfies w EMPTY = T ∧
  satisfies w (c INSERT f) = (satisfies_npbc w c ∧ satisfies w f) ∧
  satisfies w (f ∪ h) = (satisfies w f ∧ satisfies w h)
Proof
  fs [satisfies_def] \\ metis_tac []
QED

(* Statement of Prop 1 from Gocht/Nordstrom AAAI-21 *)

Theorem substitution_redundancy:
  c redundant_wrt f
  ⇔
  ∃w. f ∪ {not c} ⊨ (f ∪ {c}) ⇂ w
Proof
  eq_tac \\ fs [redundant_wrt_def]
  THEN1
   (rw [satisfiable_def,sat_implies_def,not_thm]
    \\ Cases_on ‘∃w. satisfies w f’ \\ fs []
    \\ qexists_tac ‘SOME o INL o w’
    \\ ‘∀w'. assign (SOME o INL o w) w' = w’ by fs [assign_def,FUN_EQ_THM]
    \\ fs [satisfies_def,PULL_EXISTS,subst_thm])
  \\ rw []
  \\ Cases_on ‘satisfiable f’ \\ fs []
  \\ fs [satisfiable_def]
  \\ fs [sat_implies_def,not_thm]
  \\ Cases_on ‘satisfies_npbc w' c’ THEN1 metis_tac []
  \\ first_x_assum drule_all
  \\ rw [subst_thm]
  \\ first_x_assum $ irule_at (Pos last)
  \\ fs [satisfies_def,PULL_EXISTS,subst_thm]
QED

val _ = Parse.hide "C";

Definition sat_ord_def:
  sat_ord f po w ⇔
  ∀z. satisfies z f ⇒
    po (assign w z) z
End

Definition sat_strict_ord_def:
  sat_strict_ord f po w ⇔
  sat_ord f po w ∧
  ∀z. satisfies z f ⇒
    ¬po z (assign w z)
End

Definition conf_valid_def:
  conf_valid C D po ⇔
  ∀p.
    satisfies p C ⇒
    ∃p'.
      satisfies p' (C ∪ D) ∧
      po p' p
End

Definition finite_support_def:
  finite_support po z ⇔
  ∀w w'.
    po w w' ⇔
    po (λv. if v ∈ z then w v else F)
       (λv. if v ∈ z then w' v else F)
End

Theorem FINITE_find_min:
  ∀s.
  FINITE s ∧ s ≠ {} ∧
  transitive po ⇒
  ∃p.
    p ∈ s ∧
    ∀p'. p' ∈ s ∧ po p' p ⇒ po p p'
Proof
  Induct_on`FINITE`>>rw[]>>
  Cases_on`s = {}`
  >- fs[]>>
  gvs[]>>
  Cases_on`po e p`
  >- (
    qexists_tac`e`>>rw[]>>
    fs[]>>
    metis_tac[transitive_def])>>
  metis_tac[]
QED

Theorem FINITE_support_find_min:
  (s : ('a -> bool) -> bool) ≠ {} ∧
  transitive po ∧
  finite_support po z ∧ FINITE z ⇒
  ∃p. p ∈ s ∧
    ∀p'. p' ∈ s ∧ po p' p ⇒ po p p'
Proof
  rw[]>>
  qabbrev_tac`R = λx (y:'a -> bool).
    ∀v. v ∈ z ⇒ x v = y v`>>
  `R equiv_on s` by (
    fs[equiv_on_def,Abbr`R`]>>
    metis_tac[])>>
  qabbrev_tac`sR = partition R s`>>
  `FINITE (POW z)` by metis_tac[FINITE_POW]>>
  `FINITE sR` by (
    pop_assum mp_tac>>
    match_mp_tac (FINITE_INJ |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO])>>
    qexists_tac`λS. {n | (∃ w. w ∈ S ∧ w n ∧ n ∈ z)}`>>
    simp[INJ_DEF,EXTENSION,IN_POW,SUBSET_DEF,Abbr`sR`,pred_setTheory.partition_def,Abbr`R`]>>
    rw[]>>
    simp[]>>
    metis_tac[])>>
  `∀x y z. y ∈ equiv_class R s x ⇒
    (po y z ⇔ po x z) ∧ (po z y ⇔ po z x)` by
    (rw[Abbr`R`]>>
    qpat_x_assum`finite_support _ _` mp_tac>>
    rewrite_tac[finite_support_def]>>
    disch_then (fn th => PURE_ONCE_REWRITE_TAC [th])>>
    qmatch_goalsub_abbrev_tac`po A C ⇔ po B D`>>
    `A = B ∧ C = D` by(
      unabbrev_all_tac>>
      simp[EXTENSION]>>
      metis_tac[])>>
    fs[])>>
  qabbrev_tac`spo = λS T. S ∈ sR ∧ T ∈ sR ∧
    ∃x y. x ∈ S ∧ y ∈ T ∧ po x y`>>
  `transitive spo` by (
    rw[transitive_def,Abbr`spo`,Abbr`sR`]>>
    qexists_tac`x`>>
    qexists_tac`y'`>>
    simp[]>>
    qpat_x_assum`S'' ∈ parition _ _` mp_tac>>
    simp[pred_setTheory.partition_def]>>
    rw[]>>
    metis_tac[transitive_def])>>
  drule FINITE_find_min>>
  disch_then (drule_at Any)>>
  impl_tac>- (
    fs[Abbr`sR`,pred_setTheory.partition_def,EXTENSION]>>
    first_x_assum (irule_at Any)>>
    qexists_tac`{y| y ∈ s ∧ R x y}`>>
    simp[])>>
  rw[]>>
  fs[Abbr`sR`]>>
  `∃pp. pp ∈ p` by (
    `p ≠ {}` by metis_tac[EMPTY_NOT_IN_partition]>>
    fs[EXTENSION]>>
    metis_tac[])>>
  qexists_tac`pp`>>rw[]
  >- (
    drule partition_SUBSET>>
    fs[SUBSET_DEF])>>
  rename1`po pp qq`>>
  `equiv_class R s qq ∈ partition R s` by
    (fs[pred_setTheory.partition_def] >>
    metis_tac[])>>
  first_x_assum drule>>
  impl_tac>- (
    simp[Abbr`spo`]>>
    `R qq qq` by fs[Abbr`R`]>>
    metis_tac[])>>
  rw[Abbr`spo`]>>
  gvs[pred_setTheory.partition_def]>>
  metis_tac[]
QED

(* the solution improving constraint is given by
  l + -l|w ≥ 0 *)
Definition obj_constraint_def:
  obj_constraint f (l,b:int) =
    let (result, k) = subst_lhs f (MAP (λ(c,l). (-c,l)) l) in
    let (add,n) = add_lists l result in
    (add, SUM (MAP (λi. Num (ABS (FST i))) l) - (k + n))
End

(* Preserving satisfiability and optimality *)
Definition sat_obj_def:
  sat_obj fopt s t ⇔
  ∀w.
    satisfies w s ⇒
    ∃w'. satisfies w' t ∧
      eval_obj fopt w' ≤ eval_obj fopt w
End

Definition redundant_wrt_obj_def:
  redundant_wrt_obj f obj c ⇔
    sat_obj obj f (f ∪ {c})
End

Theorem redundancy_conf_valid:
  transitive po ∧
  C ∪ D ∪ {not c} ⊨ (C ∪ D ∪ {c}) ⇂ w ∧
  sat_ord (C ∪ D ∪ {not c}) po w ∧
  conf_valid C D po ⇒
  conf_valid C (D ∪ {c}) po
Proof
  rw[conf_valid_def]>>
  first_x_assum drule>>
  rename1`satisfies pold C`>>
  strip_tac>>
  rename1`satisfies p C`>>
  Cases_on`satisfies_npbc p c`
  >-
    metis_tac[]>>
  qexists_tac`assign w p`>>
  fs[sat_implies_def]>>
  first_x_assum drule>>
  simp[not_thm,satisfies_def,PULL_EXISTS,subst_thm]>>
  fs[sat_ord_def]>>
  metis_tac[not_thm,transitive_def]
QED

Theorem optimal_exists:
  satisfies w npbf ⇒
  ∃w'.
    optimal w' npbf fopt
Proof
  rw[]>>
  Cases_on`fopt`>>fs[]
  >- (
    EVAL_TAC>>fs[]>>
    metis_tac[satisfies_def])>>
  Cases_on`x`>>fs[]>>
  rename1`(f,b)`>>
  qabbrev_tac`objs =
    IMAGE (λw. SUM (MAP (eval_term w) f)) {w | satisfies w npbf}`>>
  qabbrev_tac`opt = MIN_SET objs`>>
  `objs ≠ {}` by (
    unabbrev_all_tac>>
    fs[EXTENSION]>>
    metis_tac[])>>
  drule MIN_SET_LEM>>
  rw[]>>
  unabbrev_all_tac>>fs[]>>
  qexists_tac`w'`>>
  fs[optimal_def,PULL_EXISTS]>>rw[]>>
  first_x_assum drule>>
  rw[eval_obj_def]
QED

Theorem add_ge:
  x ≥ y - z ⇔
  x + z ≥ y
Proof
  rw[]
QED

Theorem add_ge_2:
  y ≥ z ⇒
  (x + (y-z) ≥ y ⇔ x ≥ z)
Proof
  rw[]
QED

Theorem satisfies_npbc_obj_constraint:
  satisfies_npbc s (obj_constraint w obj) ⇔
  eval_obj (SOME obj) (assign w s) ≤ eval_obj (SOME obj) s
Proof
  Cases_on`obj`>>
  rename1`(obj,c)`>>
  rw[obj_constraint_def,eval_obj_def]>>
  rpt(pairarg_tac>>fs[])>>
  simp[satisfies_npbc_def,add_ge]>>
  `n + SUM (MAP (eval_term s) add') = SUM (MAP (eval_term s) add') + n` by fs[]>>
  pop_assum SUBST_ALL_TAC>>
  drule add_lists_thm >>
  disch_then(qspec_then `s` sym_sub_tac)>>
  `k + (SUM (MAP (eval_term s) obj) + SUM (MAP (eval_term s) result)) = SUM (MAP (eval_term s) obj) + (SUM (MAP (eval_term s) result) + k)` by fs[]>>
  pop_assum SUBST_ALL_TAC>>
  drule subst_lhs_thm>>
  disch_then(qspec_then `s` sym_sub_tac)>>
  simp[not_lhs]>>
  DEP_REWRITE_TAC [add_ge_2]>>
  simp[ABS_coeff_ge]
QED

Theorem substitution_redundancy_obj:
  f ∪ {not c} ⊨ ((f ∪ {c}) ⇂ w ∪
    (case obj of NONE => {} | SOME obj => {obj_constraint w obj}))
  ⇒
  redundant_wrt_obj f obj c
Proof
  rw[redundant_wrt_obj_def, sat_obj_def,not_thm,sat_implies_def]
  \\ rename1`satisfies s f`
  \\ Cases_on ‘satisfies_npbc s c’
  >- (
    first_x_assum (irule_at Any)>>
    simp[])
  \\ first_x_assum drule_all
  \\ rw [subst_thm]
  \\ first_x_assum $ irule_at Any
  \\ every_case_tac
  >-
    fs [eval_obj_def,satisfies_def,PULL_EXISTS,subst_thm]
  \\ fs [satisfies_def,PULL_EXISTS,subst_thm,satisfies_npbc_obj_constraint]
QED

Definition conf_valid'_def:
  conf_valid' C D pres po obj ⇔
    ∀p.
      satisfies p C ⇒
      ∃p'.
           (∀x. x ∈ pres ⇒ p x = p' x) ∧
           satisfies p' (C ∪ D) ∧
           po p' p ∧
           eval_obj obj p' ≤ eval_obj obj p
End

Theorem dominance_conf_valid:
  transitive po ∧
  finite_support po z ∧ FINITE z ∧
  (∀x. x ∈ pres ⇒ w x = NONE) ∧
  C ∪ D ∪ {not c} ⊨ C ⇂ w ∧
  sat_strict_ord (C ∪ D ∪ {not c}) po w ∧
  (case obj of
   | NONE => T
   | SOME obj => C ∪ D ∪ {not c} ⊨ {obj_constraint w obj}) ∧
  conf_valid' C D pres po obj ⇒
  conf_valid' C (D ∪ {c}) pres po obj
Proof
  rw[conf_valid'_def]>>
  CCONTR_TAC>>
  gs[]>>
  fs[METIS_PROVE [] ``(A ∨ ¬B) ⇔ (¬A ⇒ ¬B)``]>>
  qabbrev_tac`s =
  {p |
   satisfies p C ∧
   ∀p'. (∀x. x ∈ pres ⇒ p x = p' x) ∧
        po p' p ∧ eval_obj obj p' ≤ eval_obj obj p ⇒
        ¬satisfies p' (C ∪ D ∪ {c})}`>>
  `s <> {}` by (
    rw[Abbr`s`,EXTENSION]>>
    metis_tac[])>>
  rename1`satisfies pold C`>>
  `∃p. p ∈ s ∧
    ∀p'. p' ∈ s ∧ po p' p ⇒ po p p'` by
    (match_mp_tac FINITE_support_find_min>>
    fs[])>>
  qpat_x_assum`s ≠ _ ` kall_tac>>
  `satisfies p C ∧
  ∀p'.
    (∀x. x ∈ pres ⇒ p x = p' x) ∧
    po p' p ∧ eval_obj obj p' ≤ eval_obj obj p ⇒
    (¬satisfies p' C ∨ ¬satisfies p' D)
      ∨ ¬satisfies_npbc p' c` by fs[Abbr`s`]>>
  last_x_assum drule>>strip_tac>>
  gvs[]>>
  `~satisfies_npbc p' c` by metis_tac[]>>
  fs[sat_strict_ord_def,sat_ord_def,not_thm]>>
  last_x_assum drule_all>>
  strip_tac>>
  qabbrev_tac`p'' = assign w p'`>>
  `po p'' p` by
    metis_tac[relationTheory.transitive_def]>>
  `¬po p p''` by
    metis_tac[relationTheory.transitive_def]>>
  `satisfies p'' C` by (
    fs[sat_implies_def,Abbr`p''`]>>
    fs[satisfies_def,PULL_EXISTS,subst_thm,not_thm])>>
  `p'' ∉ s` by metis_tac[]>>
  ‘eval_obj obj p'' ≤ eval_obj obj p'’ by
    (Cases_on ‘obj’ >- fs [eval_obj_def]
     \\ gvs [sat_implies_def,Abbr‘p''’]
     \\ rewrite_tac [GSYM satisfies_npbc_obj_constraint]
     \\ first_x_assum irule \\ fs [not_thm]) >>
  gs[Abbr`s`]>>
  rename1`satisfies_npbc pprime c`>>
  `po pprime p` by
    metis_tac[transitive_def]>>
  `!x. x ∈ pres ⇒ (p' x = pprime x)` by
    gvs[Abbr`p''`,assign_def]>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

(* set of syntactic variables *)
Definition npbc_vars_def:
  npbc_vars ((xs,n):npbc) = set (MAP SND xs)
End

Definition npbf_vars_def:
  npbf_vars npbf =
  BIGUNION (IMAGE npbc_vars npbf)
End

Theorem eq_var_subset_eval_term:
  ∀ls.
  set (MAP SND ls) ⊆ X ∧
  (∀n. n ∈ X ⇒ (w n ⇔ w' n)) ⇒
  MAP (eval_term w) ls = MAP (eval_term w') ls
Proof
  Induct>>rw[]>>
  Cases_on`h`>>fs[]
QED

Theorem npbc_vars_satisfies_npbc:
  npbc_vars c ⊆ X ∧
  (∀n. n ∈ X ⇒ w n = w' n) ⇒
  (satisfies_npbc w c ⇒
  satisfies_npbc w' c)
Proof
  Cases_on`c`>>
  rw[satisfies_npbc_def,npbc_vars_def]>>
  metis_tac[eq_var_subset_eval_term]
QED

Theorem npbf_vars_satisfies:
  npbf_vars f ⊆ X ∧
  (∀n. n ∈ X ⇒ w n = w' n) ⇒
  (satisfies w f ⇒
  satisfies w' f)
Proof
  rw[satisfies_def,npbf_vars_def]>>
  first_x_assum drule>>
  match_mp_tac npbc_vars_satisfies_npbc>>
  fs[IMAGE_DEF,SUBSET_DEF]>>
  metis_tac[]
QED

(* Syntactic representation of a po used in dominance proofs:
  ((f, us, vs), xs)
  such that:
  - |us| = |vs| and both lists distinct
  - vars(f) = us ∪ vs
  - |xs| = |us|
*)
Type spo = ``: (npbc list # var list # var list) # var list``

(* w ≤ w' iff
  the assignment mapping
  us -> w (xs)
  vs -> w' (xs)
  _  -> F
  satisfies f
*)
Definition po_of_spo_def:
  po_of_spo (((f,us,vs),xs):spo) =
  λw w'.
  let ss = ALOOKUP
    (ZIP (us,MAP (INL o w) xs) ++
     ZIP (vs,MAP (INL o w') xs)) in
  satisfies (assign ss (λn. F)) (set f)
End

Theorem MAP_MEM_BOOL:
  MAP (λv. f (MEM v xs) v) xs = MAP (λv. f T v) xs
Proof
  rw[MAP_EQ_f]
QED

Theorem finite_support_po_of_spo:
  finite_support (po_of_spo (fuv,xs)) (set xs)
Proof
  PairCases_on`fuv`>>
  rw[finite_support_def,po_of_spo_def]>>
  Cases_on`(∀x. MEM x xs ⇒ (w x ⇔ w' x))`>>simp[]>>
  qmatch_goalsub_abbrev_tac`satisfies (assign ww _) _ ⇔ satisfies (assign ww' _) _`>>
  qsuff_tac`ww = ww'`>>simp[]>>
  unabbrev_all_tac>>
  simp[o_DEF,MAP_MEM_BOOL]
QED

Theorem satisfies_subst_thm:
  satisfies w (fml ⇂ f) ⇔ satisfies (assign f w) fml
Proof
  rw[satisfies_def,PULL_EXISTS,subst_thm]
QED

Definition good_ord_def:
  good_ord (f,us,vs) ⇔
  npbf_vars (set f) ⊆ set us ∪ set vs ∧
  LENGTH us = LENGTH vs ∧
  ALL_DISTINCT (us ++ vs)
End

Theorem IMP_ALOOKUP_NONE:
  ¬MEM x xs ∧ LENGTH xs = LENGTH ys
  ⇒
  ALOOKUP (ZIP (xs,ys)) x = NONE
Proof
  rw[ALOOKUP_NONE,MAP_ZIP]
QED

Theorem ALOOKUP_ALL_DISTINCT_EL_IMP:
  ALL_DISTINCT vs ∧ LENGTH vs = LENGTH zs ∧ n < LENGTH vs ⇒
  ALOOKUP (ZIP (vs,zs)) (EL n vs) = SOME (EL n zs)
Proof
  rw[]>>
  `EL n vs = FST (EL n (ZIP(vs,zs)))` by
    simp[EL_ZIP]>>
  rw[]>>
  DEP_REWRITE_TAC [ALOOKUP_ALL_DISTINCT_EL]>>
  simp[Once EL_ZIP,MAP_ZIP]
QED

Theorem reflexive_po_of_spo:
  good_ord (f,us,vs) ∧
  LENGTH xs = LENGTH us ⇒
  {}
  ⊨
  (set f) ⇂
    ALOOKUP
    (ZIP (vs,MAP (INR o Pos) us)) ⇒
  reflexive (po_of_spo ((f,us,vs),xs))
Proof
  rw[reflexive_def,po_of_spo_def,sat_implies_def]>>
  fs[satisfies_subst_thm,good_ord_def]>>
  qabbrev_tac`
    ww =
    assign
      (ALOOKUP
         (ZIP (us,MAP (INL ∘ x) xs) ++
          ZIP (vs,MAP (INL ∘ x) xs)))
      (λn. F)`>>
  first_x_assum(qspec_then`ww` mp_tac)>>
  match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
  asm_exists_tac>>rw[]>>
  simp[assign_def,ALOOKUP_ZIP_MAP_SND]
  >- (
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    fs[ALL_DISTINCT_APPEND])
  >- (
    Cases_on`ALOOKUP (ZIP (vs,us)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    simp[Abbr`ww`,assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]>>
    rename1`ALOOKUP _ yy`>>
    `MEM yy us` by (
      drule ALOOKUP_MEM>>
      rw[MEM_ZIP,MEM_EL]>>
      metis_tac[])>>
    Cases_on`ALOOKUP (ZIP (us,xs)) yy`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    simp[]>>
    Cases_on`ALOOKUP (ZIP (vs,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    simp[]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    fs[ALL_DISTINCT_APPEND]>>
    CONJ_TAC>- metis_tac[]>>
    simp[]>>
    gvs[MEM_EL]>>
    rpt (qpat_x_assum`ALOOKUP _ _ = SOME _` mp_tac)>>
    DEP_REWRITE_TAC [ALOOKUP_ALL_DISTINCT_EL_IMP]>>
    simp[]>>rw[]>>
    metis_tac[ALL_DISTINCT_EL_IMP])
QED

Theorem transitive_po_of_spo:
  good_ord (f,us,vs) ∧
  LENGTH xs = LENGTH us ∧
  LENGTH ws = LENGTH us ∧
  ALL_DISTINCT ws ∧
  (∀y. MEM y ws ⇒ ¬ MEM y us ∧ ¬ MEM y vs)
  ⇒
  (set f) ∪
  (set f) ⇂
    ALOOKUP
    (ZIP (us,MAP (INR o Pos) vs) ++
     ZIP (vs,MAP (INR o Pos) ws))
  ⊨
  (set f) ⇂
    ALOOKUP
     (ZIP (vs,MAP (INR o Pos) ws)) ⇒
  transitive (po_of_spo ((f,us,vs),xs))
Proof
  rw[transitive_def,po_of_spo_def,sat_implies_def]>>
  fs[satisfies_subst_thm]>>
  fs[good_ord_def,ALL_DISTINCT_APPEND]>>
  qabbrev_tac`
    ww =
    assign
      (ALOOKUP
         (ZIP (us,MAP (INL ∘ x) xs) ++
          ZIP (vs,MAP (INL ∘ y) xs) ++
          ZIP (ws,MAP (INL ∘ z) xs)))
      (λn. F)`>>
  first_x_assum(qspec_then`ww` mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      qpat_x_assum`satisfies _ _` kall_tac>>
      qpat_x_assum`satisfies _ _` mp_tac>>
      match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
      asm_exists_tac>>rw[]>>
      simp[Abbr`ww`,assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]
      >- (
        Cases_on`ALOOKUP (ZIP (us,xs)) n`
        >- gs[MAP_ZIP,ALOOKUP_NONE]>>
        DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
        CONJ_TAC>- metis_tac[]>>
        simp[])>>
      Cases_on`ALOOKUP (ZIP (vs,xs)) n`
      >- gs[MAP_ZIP,ALOOKUP_NONE]>>
      DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
      CONJ_TAC>- metis_tac[]>>
      simp[])>>
    qpat_x_assum`satisfies _ _` mp_tac>>
    qpat_x_assum`satisfies _ _` kall_tac>>
    match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
    asm_exists_tac>>rw[]>>
    simp[Abbr`ww`,assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]
    >- (
      Cases_on`ALOOKUP (ZIP (us,xs)) n`
      >- gs[MAP_ZIP,ALOOKUP_NONE]>>
      Cases_on`ALOOKUP (ZIP (us,vs)) n`
      >- gs[MAP_ZIP,ALOOKUP_NONE]>>
      DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
      CONJ_TAC>- metis_tac[]>>
      simp[]>>
      rename1`ALOOKUP _ yy`>>
      `MEM yy vs` by (
        drule ALOOKUP_MEM>>
        rw[MEM_ZIP,MEM_EL]>>
        metis_tac[])>>
      Cases_on`ALOOKUP (ZIP (vs,xs)) yy`
      >- gs[MAP_ZIP,ALOOKUP_NONE]>>
      DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
      CONJ_TAC>- metis_tac[]>>
      gvs[MEM_EL]>>
      rpt (qpat_x_assum`ALOOKUP _ _ = SOME _` mp_tac)>>
      DEP_REWRITE_TAC [ALOOKUP_ALL_DISTINCT_EL_IMP]>>
      simp[]>>rw[]>>
      metis_tac[ALL_DISTINCT_EL_IMP])>>
    Cases_on`ALOOKUP (ZIP (vs,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    Cases_on`ALOOKUP (ZIP (vs,ws)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[]>>
    rename1`ALOOKUP _ yy`>>
    `MEM yy ws` by (
      drule ALOOKUP_MEM>>
      rw[MEM_ZIP,MEM_EL]>>
      metis_tac[])>>
    Cases_on`ALOOKUP (ZIP (ws,xs)) yy`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    gvs[MEM_EL]>>
    rpt (qpat_x_assum`ALOOKUP _ _ = SOME _` mp_tac)>>
    DEP_REWRITE_TAC [ALOOKUP_ALL_DISTINCT_EL_IMP]>>
    simp[]>>rw[]>>
    metis_tac[ALL_DISTINCT_EL_IMP])>>
  match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
  asm_exists_tac>>rw[]>>
  simp[assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]
  >- (
    Cases_on`ALOOKUP (ZIP (us,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[Abbr`ww`,assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND])
  >- (
    Cases_on`ALOOKUP (ZIP (vs,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    Cases_on`ALOOKUP (ZIP (vs,ws)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[Abbr`ww`,assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]>>
    rename1`ALOOKUP _ yy`>>
    `MEM yy ws` by (
      drule ALOOKUP_MEM>>
      rw[MEM_ZIP,MEM_EL]>>
      metis_tac[])>>
    Cases_on`ALOOKUP (ZIP (ws,xs)) yy`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[]>>
    gvs[MEM_EL]>>
    rpt (qpat_x_assum`ALOOKUP _ _ = SOME _` mp_tac)>>
    DEP_REWRITE_TAC [ALOOKUP_ALL_DISTINCT_EL_IMP]>>
    simp[]>>rw[]>>
    metis_tac[ALL_DISTINCT_EL_IMP])
QED

Theorem imp_sat_ord_po_of_spo:
  good_ord (f,us,vs) ∧
  LENGTH xs = LENGTH us ∧
  fml ∪ {not c} ⊨
  (set f) ⇂
  (λn.
    case ALOOKUP (ZIP (us,xs)) n of
      SOME v =>
        (case w v of NONE => SOME (INR (Pos v)) | r => r)
    | NONE => ALOOKUP (ZIP (vs, MAP (INR o Pos) xs)) n) ⇒
  sat_ord (fml ∪ {not c}) (po_of_spo ((f,us,vs),xs)) w
Proof
  rw[sat_ord_def,po_of_spo_def]>>
  gvs[sat_implies_def]>>
  first_x_assum drule>>
  fs[good_ord_def,ALL_DISTINCT_APPEND]>>
  simp[satisfies_subst_thm]>>
  match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
  asm_exists_tac>>rw[]>>
  simp[assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]
  >- (
    Cases_on`ALOOKUP (ZIP (us,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[assign_def]>>
    Cases_on`w x`>>simp[])
  >- (
    Cases_on`ALOOKUP (ZIP (vs,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[assign_def])
QED

Theorem imp_sat_strict_ord_po_of_spo:
  good_ord (f,us,vs) ∧
  LENGTH xs = LENGTH us ∧
  fml ∪ {not c} ⊨
  (set f) ⇂
  (λn.
    case ALOOKUP (ZIP (us,xs)) n of
      SOME v =>
        (case w v of NONE => SOME (INR (Pos v)) | r => r)
    | NONE => ALOOKUP (ZIP (vs, MAP (INR o Pos) xs)) n) ∧
  unsatisfiable (
    fml ∪ {not c} ∪
    (set f) ⇂
    (λn.
      case ALOOKUP (ZIP (vs,xs)) n of
        SOME v =>
          (case w v of NONE => SOME (INR (Pos v)) | r => r)
      | NONE => ALOOKUP (ZIP (us, MAP (INR o Pos) xs)) n)) ⇒
  sat_strict_ord (fml ∪ {not c}) (po_of_spo ((f,us,vs),xs)) w
Proof
  rw[sat_strict_ord_def]
  >-
    metis_tac[imp_sat_ord_po_of_spo]>>
  CCONTR_TAC>>
  qpat_x_assum`unsatisfiable _` mp_tac>>
  simp[unsatisfiable_def,satisfiable_def]>>
  asm_exists_tac>>
  fs[po_of_spo_def]>>
  qpat_x_assum`_ ⊨ _` kall_tac>>
  fs[good_ord_def,ALL_DISTINCT_APPEND]>>
  pop_assum mp_tac>>
  simp[satisfies_subst_thm]>>
  match_mp_tac (GEN_ALL npbf_vars_satisfies)>>
  asm_exists_tac>>rw[]>>
  simp[assign_def,ALOOKUP_ZIP_MAP_SND,ALOOKUP_APPEND]
  >- (
    Cases_on`ALOOKUP (ZIP (us,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[])
  >- (
    Cases_on`ALOOKUP (ZIP (vs,xs)) n`
    >- gs[MAP_ZIP,ALOOKUP_NONE]>>
    DEP_REWRITE_TAC[IMP_ALOOKUP_NONE]>>
    CONJ_TAC>- metis_tac[]>>
    simp[assign_def]>>
    Cases_on`w x`>>simp[])
QED

Definition sat_obj_po_def:
  sat_obj_po pres spoopt fopt s t ⇔
  ∀w.
    satisfies w s ⇒
    ∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies w' t ∧
      OPTION_ALL (λspo. (po_of_spo spo) w' w) spoopt ∧
      eval_obj fopt w' ≤ eval_obj fopt w
End

Definition redundant_wrt_obj_po_def:
  redundant_wrt_obj_po f pres ord obj c ⇔
    sat_obj_po pres ord obj f (f ∪ {c})
End

Definition list_list_insert_def:
  list_list_insert [] ys = LN ∧
  list_list_insert xs [] = LN ∧
  list_list_insert (x::xs) (y::ys) = insert x y (list_list_insert xs ys)
End

Theorem lookup_list_list_insert:
  ∀xs ys. lookup n (list_list_insert xs ys) = ALOOKUP (ZIP(xs,ys)) n
Proof
  Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [list_list_insert_def,ZIP_def]
  \\ rw [lookup_insert]
QED

(* The substituted order formula used in dominance order *)
Definition dom_subst_def:
  (dom_subst w NONE = []) ∧
  (dom_subst w (SOME ((f,us,vs),xs)) =
  let us_xs = list_list_insert us xs in
  let vs_xs = list_list_insert vs xs in
  let ww = (λn.
    case lookup n us_xs of
      SOME v =>
        (case w v of NONE => SOME (INR (Pos v)) | r => r)
    | NONE =>
        (case lookup n vs_xs of
         | SOME v => SOME (INR (Pos v))
         | NONE => NONE)) in
  MAP (subst ww) f)
End

(* Any installed spo must satisfy these conditions *)
Definition good_spo_def:
  good_spo spo ⇔
  good_ord (FST spo) ∧
  reflexive (po_of_spo spo) ∧
  transitive (po_of_spo spo) ∧
  LENGTH (SND spo) = LENGTH (FST (SND (FST spo)))
End

Theorem ALOOKUP_ZIP_MAP:
  ∀xs ys f n.
    ALOOKUP (ZIP (xs,MAP f ys)) n =
    case ALOOKUP (ZIP (xs,ys)) n of
    | NONE => NONE
    | SOME v => SOME (f v)
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [ZIP_def] \\ rw []
QED

Theorem substitution_redundancy_obj_po:
  OPTION_ALL good_spo ord ∧
  (∀x. x ∈ pres ⇒ w x = NONE) ∧
  f ∪ {not c} ⊨ ((f ∪ {c}) ⇂ w ∪
    (case obj of NONE => {}
      | SOME obj => {obj_constraint w obj})) ∧
  f ∪ {not c} ⊨ set (dom_subst w ord)
  ⇒
  redundant_wrt_obj_po f pres ord obj c
Proof
  simp[Once sat_implies_def]
  \\ rw[redundant_wrt_obj_po_def, sat_obj_po_def,not_thm]
  \\ rename1`satisfies s f`
  \\ Cases_on ‘satisfies_npbc s c’
  >- (
    qexists_tac`s`>>simp[]>>
    Cases_on`ord`>>
    fs[good_spo_def]>>
    metis_tac[reflexive_def,reflexive_po_of_spo,PAIR])
  \\ first_x_assum drule_all
  \\ rw [subst_thm]
  \\ first_x_assum $ irule_at Any
  \\ rw[]
  >-
    gvs[assign_def]
  >-
    fs[eval_obj_def,satisfies_def,PULL_EXISTS,subst_thm]
  >- (
    Cases_on`ord`>>fs[good_spo_def]>>
    PairCases_on`x`>>fs[]>>
    drule imp_sat_ord_po_of_spo>>
    disch_then drule>>
    fs[dom_subst_def,LIST_TO_SET_MAP,lookup_list_list_insert,ALOOKUP_ZIP_MAP]>>
    disch_then drule>>
    simp[sat_ord_def]>>
    disch_then match_mp_tac>>
    fs[not_thm])
  >- (
    every_case_tac
    >- fs [eval_obj_def] >>
    fs [satisfies_def,PULL_EXISTS,subst_thm,satisfies_npbc_obj_constraint])
QED

Theorem good_spo_dominance:
  good_spo ((f,us,vs),xs) ∧
  (∀x. x ∈ pres ⇒ w x = NONE) ∧
  C ⊆ fml ∧
  (∀w.
    satisfies w C ⇒
    ∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies w' fml ∧
      po_of_spo ((f,us,vs),xs) w' w ∧
      eval_obj obj w' ≤ eval_obj obj w) ∧
  fml ∪ {not c} ⊨ C ⇂ w ∧
  fml ∪ {not c} ⊨
  (set f) ⇂
    (λn.
      case ALOOKUP (ZIP (us,xs)) n of
        SOME v =>
          (case w v of NONE => SOME (INR (Pos v)) | r => r)
      | NONE => ALOOKUP (ZIP (vs, MAP (INR o Pos) xs)) n) ∧
  unsatisfiable (
    fml ∪ {not c} ∪
    (set f) ⇂
    (λn.
      case ALOOKUP (ZIP (vs,xs)) n of
        SOME v =>
          (case w v of NONE => SOME (INR (Pos v)) | r => r)
      | NONE => ALOOKUP (ZIP (us, MAP (INR o Pos) xs)) n)) ∧
  (case obj of
    NONE => T
  | SOME obj =>
    fml ∪ {not c} ⊨ {obj_constraint w obj}) ⇒
  (∀w.
    satisfies w C ⇒
    ∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies_npbc w' c ∧
      satisfies w' fml ∧
      po_of_spo ((f,us,vs),xs) w' w ∧
      eval_obj obj w' ≤ eval_obj obj w)
Proof
  rw[]>>
  `conf_valid' C (fml DIFF C) pres (po_of_spo ((f,us,vs),xs)) obj` by (
    fs[conf_valid'_def]>>rw[]>>
    last_x_assum drule>>
    rw[]>>
    pop_assum (irule_at Any)>>
    fs[satisfies_def,SUBSET_DEF])>>
  imp_res_tac dominance_conf_valid>>
  pop_assum mp_tac>>
  `C ∪ (fml DIFF C) = fml` by (
    fs[EXTENSION,SUBSET_DEF]>>
    metis_tac[])>>
  simp[]>>
  disch_then drule>>
  disch_then (qspec_then`set xs` mp_tac)>>
  simp[finite_support_po_of_spo]>>
  impl_tac>- (
    fs[good_spo_def]>>
    match_mp_tac imp_sat_strict_ord_po_of_spo>>
    simp[])>>
  simp[conf_valid'_def,redundant_wrt_obj_po_def,sat_obj_po_def]>>
  rw[]>>
  pop_assum drule>>
  rw[]>>
  pop_assum (irule_at Any)>>
  fs[satisfies_def]>>
  metis_tac[]
QED

Definition sem_concl_def:
  (sem_concl fml obj NoConcl = T) ∧
  (sem_concl fml obj DSat = satisfiable fml) ∧
  (sem_concl fml obj DUnsat = unsatisfiable fml) ∧
  (sem_concl fml obj (OBounds lbi ubi) =
    ((case lbi of
      NONE => unsatisfiable fml
    | SOME lb =>
      (∀w. satisfies w fml ⇒ lb ≤ eval_obj obj w)) ∧
    (case ubi of
      NONE => T
    | SOME ub =>
      (∃w. satisfies w fml ∧ eval_obj obj w ≤ ub))))
End

Definition pres_set_spt_def:
  pres_set_spt pres =
    case pres of NONE => {} | SOME pres => domain pres
End

Definition sem_output_def:
  (sem_output (fml: npbc set) obj pres bound fml' obj' pres' NoOutput = T) ∧
  (sem_output fml obj pres bound fml' obj' pres' Derivable =
    (satisfiable fml ⇒ npbc$satisfiable fml')) ∧
  (sem_output fml obj pres bound fml' obj' pres' Equisatisfiable =
    (satisfiable fml ⇔ satisfiable fml')) ∧
  (sem_output fml obj pres bound fml' obj' pres' Equioptimal =
    ∀v.
    (case bound of NONE => T | SOME b => v < b) ⇒
    (
      (∃w. satisfies w fml ∧ npbc$eval_obj obj w ≤ v) ⇔
      (∃w'. satisfies w' fml' ∧ eval_obj obj' w' ≤ v)
    ) ) ∧
  (sem_output fml obj pres bound fml' obj' pres' Equisolvable =
    ∀v.
    (case bound of NONE => T | SOME b => v < b) ⇒
    ∃f.
    (
        BIJ f
        (proj_pres pres {w | satisfies w fml ∧ eval_obj obj w ≤ v})
        (proj_pres pres' {w' | satisfies w' fml' ∧ eval_obj obj' w' ≤ v})
    )
  )
End

(* EXPERIMENTAL UNUSED *)
Type npbcspt = ``: (int spt) #num``

Definition lookup_default_def:
  lookup_default k t =
  case lookup k t of NONE => (0:int) | SOME v => v
End

Definition add_terms_spt_def:
  add_terms_spt c1 c2 v t (k:num) =
  let c = c1 + c2 in
  if c = 0 then (delete v t, k + Num (ABS c1))
  else
    (insert v c t, k + offset c1 c2)
End

Definition add_lists_spt_def:
  (add_lists_spt t [] = (t,0)) ∧
  (add_lists_spt t ((c,x)::xs) =
  let (t',n) = add_lists_spt t xs in
  add_terms_spt
    c (lookup_default x t') x t' n)
End

Definition add_spt_def:
  add_spt ((xs,m):npbcspt) (ys,n) =
    let (xs,d) = add_lists_spt xs ys in
      (xs,((m + n) - d))
End

Definition divide_spt_def:
  divide_spt ((l,n):npbcspt) k =
    (map (λc. div_ceiling c k) l,n \\ k)
End

Definition multiply_spt_def:
  multiply_spt ((l,n):npbcspt) k =
    if k = 0 then (LN,0) else
      (map (λc. c * & k) l,n * k)
End

Definition saturate_spt_def:
  saturate_spt ((l,n):npbcspt) =
    if n = 0 then (LN,n)
    else (map (λc. abs_min c n) l, n)
End

Definition weaken_spt_def:
  weaken_spt ((l,n):npbcspt) v =
  case lookup v l of
    NONE => (l,n)
  | SOME c =>
    (delete v l, n-Num(ABS c))
End

val _ = export_theory();
