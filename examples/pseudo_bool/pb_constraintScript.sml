(*
  Formalisation of normalised pseudo-boolean constraints
*)

open preamble pb_preconstraintTheory;

val _ = new_theory "pb_constraint";

val _ = numLib.prefer_num();

(*
  Normalized pseudoboolean constraints
  PBC xs n represents constraint xs ≥ n
  An additional compactness assumption guarantees uniqueness
*)
Datatype:
  npbc = PBC ((num # lit) list) num
End

(* semantics *)

Definition b2n_def[simp]:
  b2n T = 1:num ∧
  b2n F = 0:num
End

Definition eval_lit_def[simp]:
  eval_lit w (Pos v) =     b2n (w v) ∧
  eval_lit w (Neg v) = 1 - b2n (w v)
End

Definition eval_term_def[simp]:
  eval_term w (c,l) = c * eval_lit w l
End

Definition satisfies_npbc_def:
  satisfies_npbc w (PBC xs n) ⇔ SUM (MAP (eval_term w) xs) ≥ n
End

(* Tentative representation of PBF as a set of constraints *)
Definition satisfies_def:
  satisfies w pbf ⇔
  ∀c. c ∈ pbf ⇒ satisfies_npbc w c
End

Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

(* compactness *)

Definition get_var_def[simp]:
  get_var (Pos n) = n ∧
  get_var (Neg n) = n
End

Definition term_lt_def[simp]:
  term_lt (_,l1) (_,l2) = (get_var l1 < get_var l2)
End

Definition term_le_def[simp]:
  term_le (_,l1) (_,l2) = (get_var l1 <= get_var l2)
End

Definition compact_def[simp]:
  compact (PBC xs n) ⇔
    SORTED term_lt xs ∧ (* implies that no var is mentioned twice *)
    EVERY (λ(c,l). c ≠ 0) xs
End

(* addition -- implementation *)

Definition add_terms_def:
  add_terms (c1,Pos n) (c2,Pos _) = ([(c1+c2:num,Pos n)],0:num) ∧
  add_terms (c1,Neg n) (c2,Neg _) = ([(c1+c2,Neg n)],0) ∧
  add_terms (c1,Pos n) (c2,Neg _) =
    (if c1 = c2 then ([],c1) else
     if c1 < c2 then ([(c2-c1,Neg n)],c1) else
                     ([(c1-c2,Pos n)],c2)) ∧
  add_terms (c1,Neg n) (c2,Pos _) =
    (if c1 = c2 then ([],c1) else
     if c1 < c2 then ([(c2-c1,Pos n)],c1) else
                     ([(c1-c2,Neg n)],c2))
End

Definition add_lists_def:
  add_lists [] [] = ([],0) ∧
  add_lists xs [] = (xs,0) ∧
  add_lists [] ys = (ys,0) ∧
  add_lists (x::xs) (y::ys) =
    if term_lt x y then
      let (zs,n) = add_lists xs (y::ys) in
        (x::zs,n)
    else if term_lt y x then
      let (zs,n) = add_lists (x::xs) ys in
        (y::zs,n)
    else
      let (z,n1) = add_terms x y in
      let (zs,n2) = add_lists xs ys in
        (z++zs,n1+n2)
End

Definition add_def:
  add (PBC xs m) (PBC ys n) =
    let (xs,d) = add_lists xs ys in
      PBC xs ((m + n) - d)
End

(* addition -- proof *)

Theorem add_terms_thm:
  add_terms x y = (zs,d) ∧ ~term_lt x y ∧ ~term_lt y x ⇒
  eval_term w x + eval_term w y =
  SUM (MAP (eval_term w) zs) + d
Proof
  PairCases_on ‘x’ \\ PairCases_on ‘y’ \\ rw []
  \\ ‘get_var y1 = get_var x1’ by fs [] \\ fs [] \\ gvs []
  \\ Cases_on ‘x1’ \\ Cases_on ‘y1’ \\ gvs []
  \\ gvs [add_terms_def,AllCaseEqs()] \\ Cases_on ‘w n’ \\ gvs []
QED

Theorem add_lists_thm:
  ∀x y zs d.
    add_lists x y = (zs,d) ⇒
    SUM (MAP (eval_term w) x) + SUM (MAP (eval_term w) y) =
    SUM (MAP (eval_term w) zs) + d
Proof
  ho_match_mp_tac add_lists_ind \\ rw [] \\ gvs [add_lists_def]
  \\ Cases_on ‘term_lt x y’ \\ fs []
  \\ Cases_on ‘term_lt y x’ \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_all add_terms_thm
  \\ disch_then (qspec_then ‘w’ assume_tac)
  \\ fs [SUM_APPEND]
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
    SORTED term_lt (x::l1) ∧
    SORTED term_lt (x::l2) ⇒
    term_lt x h
Proof
  ho_match_mp_tac add_lists_ind \\ rpt strip_tac
  \\ fs [add_lists_def]
  THEN1 gvs []
  THEN1 gvs []
  \\ Cases_on ‘term_lt x y’ \\ fs []
  \\ Cases_on ‘term_lt y x’ \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ ‘(∃c l. z = [(c,l)] ∧ get_var l = get_var (SND x)) ∨ z = []’ by
    gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE]
  \\ gvs []
  THEN1 (Cases_on ‘x’ \\ fs [] \\ Cases_on ‘x'’ \\ fs [])
  \\ last_x_assum irule \\ fs []
  \\ rw [] \\ rename [‘SORTED _ (_::ll)’]
  \\ Cases_on ‘ll’ \\ fs []
  \\ Cases_on ‘x'’ \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ Cases_on ‘h'’ \\ gvs []
QED

Theorem add_lists_sorted:
   ∀l l' xs d.
     EVERY (λ(c,l). c ≠ 0) l ∧ EVERY (λ(c,l). c ≠ 0) l' ∧
     SORTED term_lt l ∧ SORTED term_lt l' ∧
     add_lists l l' = (xs,d) ⇒
     SORTED term_lt xs ∧ EVERY (λ(c,l). c ≠ 0) xs
Proof
  ho_match_mp_tac add_lists_ind
  \\ REVERSE (rpt strip_tac)
  \\ fs [add_lists_def] \\ gvs []
  \\ imp_res_tac SORTED_TL
  THEN1
   (Cases_on ‘term_lt x y’ \\ fs [] THEN1 (pairarg_tac \\ gvs [])
    \\ Cases_on ‘term_lt y x’ \\ fs [] THEN1 (pairarg_tac \\ gvs [])
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE])
  \\ Cases_on ‘term_lt x y’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
    \\ drule add_lists_sorted_lemma \\ fs [])
  \\ Cases_on ‘term_lt y x’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
    \\ drule add_lists_sorted_lemma \\ fs [])
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rename [‘get_var l1 < get_var l2’]
  \\ ‘z = [] ∨ ∃c l. z = [(c,l)] ∧ get_var l = get_var l1’ by
    gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE]
  \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
  \\ drule add_lists_sorted_lemma
  \\ disch_then irule \\ rw []
  \\ rename [‘_::l5’]
  \\ Cases_on ‘l5’ \\ fs []
  \\ Cases_on ‘h'’ \\ fs []
QED

Theorem compact_add:
  compact c1 ∧ compact c2 ⇒ compact (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’ \\ fs [add_def]
  \\ pairarg_tac \\ fs [] \\ metis_tac [add_lists_sorted]
QED

(* division *)

Definition div_ceiling_def:
  div_ceiling m n = (m + (n - 1)) DIV n
End

Theorem div_ceiling_le_x:
  k ≠ 0 ⇒ (div_ceiling n k ≤ m ⇔ n ≤ k * m)
Proof
  fs [div_ceiling_def,DIV_LE_X,LEFT_ADD_DISTRIB]
QED

Theorem div_ceiling:
  k ≠ 0 ⇒ div_ceiling n k = n DIV k + MIN (n MOD k) 1
Proof
  rewrite_tac [div_ceiling_def]
  \\ strip_tac
  \\ ‘0 < k’ by fs []
  \\ drule_then (qspec_then ‘n’ mp_tac) DIVISION
  \\ strip_tac
  \\ qpat_x_assum ‘n = _’ (fn th => CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [Once th])))
  \\ rewrite_tac [GSYM ADD_ASSOC]
  \\ asm_simp_tac std_ss [ADD_DIV_ADD_DIV]
  \\ Cases_on ‘n MOD k = 0’ THEN1 fs [DIV_EQ_X]
  \\ fs [DIV_EQ_X] \\ rw [MIN_DEF]
QED

Theorem le_mult_div_ceiling:
  k ≠ 0 ⇒ n ≤ k * div_ceiling n k
Proof
  rw [div_ceiling,MIN_DEF]
  \\ ‘0 < k’ by fs []
  \\ drule_then (qspec_then ‘n’ mp_tac) DIVISION
  \\ strip_tac
  \\ qpat_x_assum ‘n = _’ (fn th => CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [Once th])))
  \\ fs [LEFT_ADD_DISTRIB]
QED

Definition divide_def:
  divide (PBC l n) k =
    PBC (MAP (λ(c,v). (div_ceiling c k, v)) l) (div_ceiling n k)
End

Theorem divide_thm:
  satisfies_npbc w c ∧ k ≠ 0 ⇒ satisfies_npbc w (divide c k)
Proof
  Cases_on ‘c’ \\ fs [divide_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ,div_ceiling_le_x]
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ fs [LEFT_ADD_DISTRIB] \\ rw []
  \\ irule (DECIDE “m ≤ m1 ∧ n ≤ n1 ⇒ m+n ≤ m1+n1:num”)
  \\ fs [le_mult_div_ceiling]
QED

Theorem div_ceiling_ge_one:
  m ≠ 0 ∧ n ≠ 0 ⇒ 1 ≤ div_ceiling m n
Proof
  rw[div_ceiling_def]>>
  Cases_on`m`>>fs[ADD1]>>
  `0 < n` by fs[]>>
  drule ADD_DIV_RWT>>
  disch_then (fn th => DEP_REWRITE_TAC[th])>>fs[]
QED

Theorem compact_divide:
  compact c ∧ k ≠ 0 ⇒ compact (divide c k)
Proof
  Cases_on`c` \\ rw[compact_def,divide_def]
  THEN1 (Induct_on ‘l’ \\ fs [FORALL_PROD]
    \\ Cases_on ‘l’ \\ fs []
    \\ Cases_on ‘t’ \\ fs []
    \\ PairCases_on ‘h’ \\ fs [])
  \\ fs[EVERY_MAP,EVERY_MEM]
  \\ rw[] \\ first_x_assum drule
  \\ pairarg_tac \\ fs[]
  \\ strip_tac \\ imp_res_tac div_ceiling_ge_one
  \\ fs[]
QED

(* negation *)
Definition negate_def[simp]:
  negate (Pos n) = Neg n ∧
  negate (Neg n) = Pos n
End

Definition not_def:
  not (PBC l n) = PBC (MAP (I ## negate) l) (SUM (MAP FST l) + 1 - n)
End

Theorem not_thm:
  satisfies_npbc w (not c) ⇔ ~satisfies_npbc w c
Proof
  Cases_on ‘c’ \\ fs [not_def,satisfies_npbc_def,GREATER_EQ]
  \\ qid_spec_tac ‘n’
  \\ qid_spec_tac ‘l’
  \\ Induct \\ fs [FORALL_PROD] \\ rw []
  \\ Cases_on ‘p_2’ \\ fs [negate_def]
  \\ Cases_on ‘w n'’ \\ fs []
  \\ TRY (last_x_assum (fn th => rewrite_tac [GSYM th]) \\ gvs [] \\ NO_TAC)
  \\ Cases_on ‘p_1 ≤ n’
  \\ TRY (last_x_assum (qspec_then ‘n-p_1’ assume_tac) \\ gvs [] \\ NO_TAC)
  \\ fs [GSYM NOT_LESS]
  \\ last_x_assum (qspec_then ‘SUM (MAP (eval_term w) l)’ assume_tac) \\ gvs []
QED

(* multiplication *)
Definition multiply_def:
  multiply (PBC l n) k =
    if k = 0 then PBC [] 0 else
      PBC (MAP (λ(c,v). (c * k, v)) l) (n * k)
End

Theorem multiply_thm:
  satisfies_npbc w c ⇒ satisfies_npbc w (multiply c k)
Proof
  Cases_on ‘c’ \\ fs [multiply_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ drule LESS_MONO_MULT
  \\ disch_then (qspec_then`k` mp_tac)
  \\ REWRITE_TAC [Once MULT_COMM]
  \\ strip_tac
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ pop_assum kall_tac
  \\ Induct_on`l` \\ simp[] \\ Cases \\ rw[]
QED

Theorem compact_multiply:
  compact c ⇒ compact (multiply c k)
Proof
  Cases_on ‘c’ \\ reverse (rw [multiply_def,compact_def])
  THEN1 gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘t’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
QED

(* saturation *)
Definition saturate_def:
  saturate (PBC l n) =
    if n = 0 then PBC [] n
    else PBC (MAP (λ(c,v). (MIN c n, v)) l) n
End

Theorem eval_lit_bool:
  eval_lit w r = 0 ∨ eval_lit w r = 1
Proof
  Cases_on`r` \\ rw[eval_lit_def]
  \\ Cases_on`w n` \\ rw[b2n_def]
QED

Theorem saturate_thm:
  satisfies_npbc w c ⇒ satisfies_npbc w (saturate c)
Proof
  Cases_on ‘c’ \\ fs [saturate_def]
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ `∀a.
      n ≤ SUM (MAP (eval_term w) l) + a ⇒
      n ≤ SUM (MAP (eval_term w) (MAP (λ(c,v). (MIN c n,v)) l)) + a` by (
    pop_assum kall_tac
    \\ Induct_on`l` \\ simp[] \\ Cases
    \\ assume_tac eval_lit_bool
    \\ fs[MIN_DEF] \\ rw[]
    \\ ONCE_REWRITE_TAC[ADD_ASSOC]
    \\ first_x_assum match_mp_tac
    \\ fs[])
  \\ pop_assum (qspec_then`0` assume_tac) \\ fs[]
QED

Theorem compact_saturate:
  compact c ⇒ compact (saturate c)
Proof
  Cases_on ‘c’ \\ reverse (rw [saturate_def,compact_def])
  THEN1 gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘t’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
QED

Definition weaken_aux_def:
  (weaken_aux v [] n = ([],n)) ∧
  (weaken_aux v ((c,l)::xs) n =
    let (xs',n') = weaken_aux v xs n in
    if get_var l = v then
      (xs',n'-c)
    else
      ((c,l)::xs',n'))
End

(* weakening *)
Definition weaken_def:
  weaken (PBC l n) v =
    let (l',n') = weaken_aux v l n in
    PBC l' n'
End

Theorem weaken_aux_theorem:
  ∀v l n l' n' a.
  n ≤ SUM (MAP (eval_term w) l) + a ∧
  weaken_aux v l n = (l',n') ⇒
  n' ≤ SUM (MAP (eval_term w) l') + a
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ ( (* two subgoals *)
    first_x_assum(qspec_then`a + c * eval_lit w l` assume_tac) \\ rfs[]
    \\ `eval_lit w l = 0 ∨ eval_lit w l = 1` by fs[eval_lit_bool]
    \\ fs[] )
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
  \\ pairarg_tac \\ fs[]
  \\ rw [satisfies_npbc_def,GREATER_EQ]
  \\ match_mp_tac weaken_aux_theorem0
  \\ metis_tac[]
QED

Theorem weaken_aux_contains:
  ∀v ls n ls' n' x.
  weaken_aux v ls n = (ls',n') ∧
  MEM x ls' ⇒ MEM x ls
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[]
QED

Theorem SORTED_weaken_aux:
  ∀v ls n ls' n'.
  SORTED term_lt ls ∧
  weaken_aux v ls n = (ls',n') ⇒
  SORTED term_lt ls'
Proof
  ho_match_mp_tac weaken_aux_ind \\ rw[weaken_aux_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[]
  >-
    metis_tac[SORTED_TL]
  \\ qpat_x_assum `SORTED _ (_ :: _)` mp_tac
  \\ DEP_REWRITE_TAC [SORTED_EQ] \\ rw[]
  >-
    simp[transitive_def,FORALL_PROD]
  \\ drule weaken_aux_contains
  \\ metis_tac[]
QED

Theorem compact_weaken:
  compact c ⇒ compact (weaken c v)
Proof
  Cases_on ‘c’ \\ rw[weaken_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  >-
    metis_tac[SORTED_weaken_aux]
  \\ fs[EVERY_MEM,FORALL_PROD]
  \\ metis_tac[weaken_aux_contains]
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
    clean_up xs = (ys,d) ∧ EVERY (λ(c,l). c ≠ 0) xs ⇒
    SORTED term_lt ys ∧ EVERY (λ(c,l). c ≠ 0) ys
Proof
  ho_match_mp_tac clean_up_ind \\ rw []
  \\ gvs [clean_up_def]
  \\ rpt (pairarg_tac \\ full_simp_tac std_ss []) \\ gvs []
  \\ drule_at (Pos last) add_lists_sorted
  \\ impl_tac \\ rw [] \\ fs []
  \\ imp_res_tac EVERY_partition \\ gvs []
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
  is_Pos (Pos _) = T ∧
  is_Pos (Neg _) = F
End

Definition subst_aux_def:
  subst_aux f [] = ([],[],0) ∧
  subst_aux f ((c,l)::rest) =
    let (old,new,k) = subst_aux f rest in
      case f (get_var l) of
      | NONE => ((c,l)::old,new,k)
      | SOME (INL b) => (old,new,if is_Pos l = b then k+c else k)
      | SOME (INR n) => let x = (if is_Pos l then n else negate n) in
                          (old,(c,x)::new,k)
End

Definition subst_def:
  subst f (PBC l n) =
    let (old,new,k) = subst_aux f l in
    let (sorted,k2) = clean_up new in
    let (result,k3) = add_lists old sorted in
      (PBC result (n - (k + k2 + k3)))
End

Theorem subst_thm:
  satisfies_npbc w (subst f c) = satisfies_npbc (assign f w) c
Proof
  Cases_on ‘c’ \\ fs [satisfies_npbc_def,subst_def]
  \\ rpt (pairarg_tac \\ gvs [satisfies_npbc_def,GREATER_EQ])
  \\ ‘∀l old new k.
        subst_aux f l = (old,new,k) ⇒
        SUM (MAP (eval_term (assign f w)) l) =
        k + SUM (MAP (eval_term w) old ++ MAP (eval_term w) new)’ by
    (Induct \\ fs [subst_aux_def,FORALL_PROD]
     \\ pairarg_tac \\ fs []
     \\ rw []
     \\ Cases_on ‘f (get_var p_2)’ \\ gvs [assign_def]
     THEN1 (Cases_on ‘p_2’ \\ fs [assign_def])
     \\ Cases_on ‘x’ \\ gvs []
     THEN1 (Cases_on ‘p_2’ \\ fs [assign_def] \\ Cases_on ‘x'’ \\ fs [])
     \\ Cases_on ‘p_2’ \\ Cases_on ‘y’ \\ fs [assign_def]
     \\ Cases_on ‘w n'’ \\ fs [SUM_APPEND])
  \\ pop_assum $ drule_then assume_tac \\ fs [SUM_APPEND]
  \\ drule_then (qspec_then ‘w’ assume_tac) clean_up_thm
  \\ drule_then (qspec_then ‘w’ assume_tac) add_lists_thm
  \\ gvs []
QED

(* The returned flag is T if any literal touched by the constraint is
  itself assigned to T under the substitution *)
Definition subst_opt_aux_def:
  subst_opt_aux f [] = ([],[],0,T) ∧
  subst_opt_aux f ((c,l)::rest) =
    let (old,new,k,same) = subst_opt_aux f rest in
      case f (get_var l) of
      | NONE => ((c,l)::old,new,k,same)
      | SOME (INL b) =>
        if is_Pos l = b then
          (old,new, k+c, same)
        else
          (old,new, k, F)
      | SOME (INR n) => let x = (if is_Pos l then n else negate n) in
                          (old,(c,x)::new,k,F)
End

(* Computes the LHS term of the slack of a constraint under
  a partial assignment p (list of literals) *)
Definition lslack_def:
  lslack (PBC ls num) p =
  SUM (MAP FST (FILTER (λ(a,b). ¬MEM (negate b) p) ls))
End

Definition check_contradiction_def:
  check_contradiction (PBC ls num) =
  let l = lslack (PBC ls num) [] in
    l < num
End

Theorem check_contradiction_unsat:
  check_contradiction c ⇒
  ¬satisfies_npbc w c
Proof
  Cases_on`c`>>
  rw[check_contradiction_def,satisfies_npbc_def,lslack_def]>>
  qmatch_asmsub_abbrev_tac`MAP FST lss`>>
  `lss = l` by
    fs[Abbr`lss`,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD]>>
  rw[]>>
  `SUM (MAP (eval_term w) l) ≤ SUM (MAP FST l)` by
      (match_mp_tac SUM_MAP_same_LE>>
      fs[EVERY_MEM,FORALL_PROD]>>
      rw[]>>
      rename1`eval_lit w r`>>
      assume_tac eval_lit_bool>>
      fs[])>>
  fs[]
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
  subst_opt f (PBC l n) =
    let (old,new,k,same) = subst_opt_aux f l in
      if same then NONE else
        let (sorted,k2) = clean_up new in
        let (result,k3) = add_lists old sorted in
        let res = PBC result (n - (k + k2 + k3)) in
        if imp (PBC l n) res then NONE
        else SOME res
End

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
  Cases_on ‘c’ \\ fs [subst_opt_def,subst_def]
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
  \\ first_x_assum drule
  >-
    (Cases_on`p_2`>>fs[assign_def]) >>
  Cases_on`p_2`>>fs[assign_def]>>
  Cases_on`w n`>>fs[]
QED

Theorem subst_opt_NONE:
  subst_opt f c = NONE ⇒
  satisfies_npbc w c ⇒ satisfies_npbc w (subst f c)
Proof
  Cases_on ‘c’ \\ fs [subst_opt_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw[]
  >- (
    simp[subst_def]>>
    rpt (pairarg_tac \\ fs [])>>
    drule subst_opt_aux_thm_1>>
    rw[]>>fs[]>>rw[]>>
    drule imp_thm>>
    disch_then drule>>
    fs[])
  \\ fs[subst_thm]
  \\ fs[satisfies_npbc_def]
  \\ drule subst_opt_aux_thm_2
  \\ disch_then(qspec_then`w` assume_tac)
  \\ intLib.ARITH_TAC
QED

(* subst is compact *)

Theorem compact_subst:
  compact c ⇒ compact (subst f c)
Proof
  Cases_on ‘c’ \\ fs [compact_def,subst_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac
  \\ qsuff_tac ‘∀l old new k.
       SORTED term_lt l ∧ EVERY (λ(c,l). c ≠ 0) l ∧ subst_aux f l = (old,new,k) ⇒
       SORTED term_lt old ∧ EVERY (λ(c,l). c ≠ 0) old ∧ EVERY (λ(c,l). c ≠ 0) new’
  THEN1
   (disch_then drule \\ fs [] \\ strip_tac
    \\ drule clean_up_sorted \\ fs [] \\ strip_tac
    \\ drule_all add_lists_sorted \\ fs [])
  \\ rpt (pop_assum kall_tac)
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on ‘f (get_var p_2)’ \\ gvs []
  \\ imp_res_tac sortingTheory.SORTED_TL \\ gvs [AllCaseEqs()]
  \\ Cases_on ‘old'’ \\ fs []
  \\ qpat_x_assum ‘subst_aux f l = (h::t,new,k)’ mp_tac
  \\ qpat_x_assum ‘SORTED term_lt ((p_1,p_2)::l)’ mp_tac
  \\ EVERY (map qid_spec_tac [‘p_1’,‘p_2’,‘t’,‘h’,‘new’,‘k’,‘l’])
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ Cases_on ‘f (get_var p_2')’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
  \\ first_x_assum irule
  \\ Cases_on ‘l'’ \\ fs []
  \\ Cases_on ‘h'’ \\ fs []
QED

Definition sat_implies_def:
  sat_implies pbf pbf' ⇔
  ∀w. satisfies w pbf ⇒ satisfies w pbf'
End

Overload "⊨" = “sat_implies”
Overload "⇂" = “λf w. IMAGE (subst w) f”

val _ = set_fixity "redundant_wrt" (Infixl 500);
val _ = set_fixity "⊨" (Infixl 500);
val _ = set_fixity "⇂" (Infixl 501);

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

(* Ensure compact LHS in preconstraint form:
  sort by variables *)
Definition compact_lhs_def:
  (compact_lhs ((c1:int,l1)::(c2,l2)::cs) n =
    if get_var l1 = get_var l2 then
      if l1 = l2 then
        compact_lhs ((c1+c2,l1)::cs) n
      else
        compact_lhs ((c1-c2,l1)::cs) (n+c2)
    else
      let (cs',n') = compact_lhs ((c2,l2)::cs) n in
      ((c1,l1)::cs',n')) ∧
  (compact_lhs c n = (c,n))
End

Theorem compact_lhs_MEM:
  ∀xs n xs' n' y l.
  compact_lhs xs n = (xs',n') ∧
  MEM (y,l) xs' ⇒
  ∃y'. MEM (y',l) xs
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    pairarg_tac>>gs[]>>rw[]>>fs[]>>rw[]>>
    metis_tac[])
  >> metis_tac[]
QED

Theorem transitive_term_le:
  transitive term_le
Proof
  simp[transitive_def]>>
  rpt Cases >>
  simp[term_le_def]
QED

Theorem transitive_term_lt:
  transitive term_lt
Proof
  simp[transitive_def]>>
  rpt Cases >>
  simp[term_lt_def]
QED

Theorem get_var_eq_term_le:
  get_var l1 = get_var l2 ⇒
  (term_le (a,l1) x ⇔ term_le (b,l2) x)
Proof
  Cases_on`x`>>rw[term_le_def]
QED

Theorem compact_lhs_no_dup:
  ∀xs n xs' n'.
  SORTED term_le xs ∧
  compact_lhs xs n = (xs',n') ⇒
  SORTED term_lt xs'
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- (
    first_x_assum match_mp_tac>>
    qpat_x_assum `SORTED _ _` mp_tac>>
    DEP_REWRITE_TAC[SORTED_EQ]>>simp[transitive_term_le]>>
    metis_tac[get_var_eq_term_le])
  >- (
    first_x_assum match_mp_tac>>
    qpat_x_assum `SORTED _ _` mp_tac>>
    DEP_REWRITE_TAC[SORTED_EQ]>>simp[transitive_term_le]>>
    metis_tac[get_var_eq_term_le])>>
  pairarg_tac>>fs[]>>rw[]>>
  qpat_x_assum `SORTED _ _` mp_tac>>
  DEP_REWRITE_TAC[SORTED_EQ]>>
  simp[transitive_term_le,transitive_term_lt]>>
  simp[FORALL_PROD]>>rw[]>>
  drule compact_lhs_MEM>>
  disch_then drule>>strip_tac>>
  fs[]>>first_x_assum drule>>
  fs[]
QED

Theorem eval_lit_INT[simp]:
  &(eval_lit w r) = eval_lit w r
Proof
  Cases_on`r` \\ EVAL_TAC
  \\ Cases_on`w n` \\ EVAL_TAC
  \\ fs[]
QED

Theorem eval_lit_eq_flip:
  q * eval_lit w r = q + (-q * eval_lit w (negate r))
Proof
  Cases_on`r` \\ EVAL_TAC
  \\ Cases_on`w n` \\ EVAL_TAC
  \\ fs[]
QED

Theorem iSUM_PERM:
  ∀l1 l2. PERM l1 l2 ⇒
  iSUM l1 = iSUM l2
Proof
  ho_match_mp_tac PERM_IND>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_QSORT_term_le[simp]:
  iSUM (MAP (eval_term w) (QSORT term_le l)) =
  iSUM (MAP (eval_term w) l)
Proof
  match_mp_tac iSUM_PERM>>
  match_mp_tac PERM_MAP>>
  metis_tac[QSORT_PERM,PERM_SYM]
QED

Theorem compact_lhs_sound:
  ∀xs n xs' n'.
  compact_lhs xs n = (xs',n') ⇒
  iSUM (MAP (pb_preconstraint$eval_term w) xs) + n = iSUM (MAP (pb_preconstraint$eval_term w) xs') + n'
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- (
    (* l1 = l2 *)
    fs[iSUM_def]>>
    intLib.ARITH_TAC)
  >- (
    (* l1 = negate l2 *)
    fs[iSUM_def]>>
    qmatch_goalsub_abbrev_tac` A + _ + _`>>
    REWRITE_TAC[Once eval_lit_eq_flip]>>
    `negate l2 = l1` by
      (Cases_on`l1`>>Cases_on`l2`>>fs[])>>
    fs[Abbr`A`]>>
    qpat_x_assum`_ = _ + _` sym_sub_tac>>
    simp[integerTheory.INT_SUB_RDISTRIB]>>
    qmatch_goalsub_abbrev_tac`_ * wl2 + _ +_ = _ - _ + is + _`>>
    rpt (pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  pairarg_tac>>fs[]>>
  rw[]>>
  fs[iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition normalize_lhs_def:
  (normalize_lhs [] acc n = (REVERSE acc,n)) ∧
  (normalize_lhs ((x,l)::xs) acc n =
    if x < 0 then normalize_lhs xs ((Num(-x),negate l)::acc) (n+x)
    else if x > 0 then normalize_lhs xs ((Num x,l)::acc) n
    else normalize_lhs xs acc n)
End

Theorem normalize_lhs_normalizes:
  ∀ls acc n ls' n'.
  normalize_lhs ls acc n = (ls',n') ⇒
  iSUM (MAP (pb_preconstraint$eval_term w) ls) + &(SUM (MAP (eval_term w) acc)) + n = &(SUM (MAP (eval_term w) ls')) + n'
Proof
  Induct>>rw[normalize_lhs_def,iSUM_def]
  >-
    metis_tac[SUM_REVERSE,MAP_REVERSE] >>
  Cases_on`h`>>fs[normalize_lhs_def]>>
  every_case_tac>>fs[]
  >- intLib.ARITH_TAC>>
  first_x_assum drule>>
  simp[GSYM integerTheory.INT_ADD]
  >- (
    `&(Num q * eval_lit w r) = q * eval_lit w r` by (
      PURE_REWRITE_TAC[GSYM integerTheory.INT_MUL,eval_lit_INT]>>
      fs[integerTheory.INT_NOT_LT,GSYM integerTheory.INT_OF_NUM]) >>
    intLib.ARITH_TAC)
  >- (
    simp[Once eval_lit_eq_flip]>>
    `-q * eval_lit w (negate r) = &(Num (-q) * eval_lit w (negate r))` by (
      PURE_REWRITE_TAC[GSYM integerTheory.INT_MUL,eval_lit_INT]>>
      `0 ≤ -q` by fs[]>>
      pop_assum mp_tac>>
      PURE_REWRITE_TAC[GSYM integerTheory.INT_OF_NUM]>>
      simp[])>>
    intLib.ARITH_TAC)
  >- (
    `q=0` by intLib.ARITH_TAC>>
    simp[])
QED

Definition pbc_to_npbc_def:
  (pbc_to_npbc (GreaterEqual lhs n) =
    let (lhs',m') = compact_lhs (QSORT term_le lhs) 0 in
    let (lhs'',m'') = normalize_lhs lhs' [] 0 in
    let rhs = if n-(m'+m'') ≥ 0 then Num(n-(m'+m'')) else 0 in
    PBC lhs'' rhs) ∧
  (pbc_to_npbc (Equal xs n) = PBC [] 0)
End

Definition normalize_def:
  normalize pbf =
  let pbf' = FLAT (MAP pbc_ge pbf) in
  MAP pbc_to_npbc pbf'
End

Theorem pbc_to_npbc_thm:
  (∀xs n. pbc ≠ Equal xs n) ⇒
  (satisfies_pbc w pbc ⇔ satisfies_npbc w (pbc_to_npbc pbc))
Proof
  Cases_on`pbc`>>fs[]>>
  rw[satisfies_pbc_def,satisfies_npbc_def,pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  drule compact_lhs_sound>>
  disch_then(qspec_then`w` assume_tac)>>fs[]>>
  drule normalize_lhs_normalizes>>
  disch_then(qspec_then`w` assume_tac)>>fs[]>>
  simp[satisfies_npbc_def]>>
  intLib.ARITH_TAC
QED

Theorem normalize_thm:
  satisfies w (set pbf) ⇔
  satisfies w (set (normalize pbf))
Proof
  simp[normalize_def]>>
  qmatch_goalsub_abbrev_tac`MAP _ pbf'`>>
  `satisfies w (set pbf) ⇔ satisfies w (set pbf')` by
    (simp[Abbr`pbf'`]>>
    Induct_on`pbf`>>
    simp[]>>
    metis_tac[pbc_ge_thm])>>
  simp[]>>
  `!x. MEM x pbf' ⇒ (∀xs n. x ≠ Equal xs n)` by
    (simp[Abbr`pbf'`,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    Cases_on`y`>>simp[pbc_ge_def]>>
    rw[]>>simp[])>>
  pop_assum mp_tac>>
  rpt(pop_assum kall_tac)>>
  Induct_on`pbf'`>>simp[]>>
  rw[]>>
  metis_tac[pbc_to_npbc_thm]
QED

Theorem get_var_negate[simp]:
  get_var (negate r) = get_var r
Proof
  Cases_on`r`>>simp[]
QED

Theorem normalize_lhs_compact1:
  ∀lhs acc n lhs' n'.
  normalize_lhs lhs acc n = (lhs',n') ∧
  SORTED $< (MAP (get_var o SND) (REVERSE acc) ++ MAP (get_var o SND) lhs) ⇒
  SORTED term_lt lhs'
Proof
  Induct>>simp[normalize_lhs_def]
  >- (
    rw[GSYM MAP_REVERSE]>>
    fs[sorted_map]>>
    qmatch_asmsub_abbrev_tac`_ tlt _`>>
    `tlt = term_lt` by
      simp[Abbr`tlt`,FUN_EQ_THM,FORALL_PROD]>>
    fs[])>>
  Cases>>simp[normalize_lhs_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]
  >- (
    PURE_REWRITE_TAC[Once (GSYM APPEND_ASSOC),APPEND]>>
    fs[])
  >- (
    PURE_REWRITE_TAC[Once (GSYM APPEND_ASSOC),APPEND]>>
    fs[]) >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[SORTED_APPEND,SORTED_EQ]  >>
  CONJ_TAC>- simp[transitive_def]>>
  simp[]
QED

Theorem normalize_lhs_compact2:
  ∀lhs acc n lhs' n'.
  normalize_lhs lhs acc n = (lhs',n') ∧
  EVERY (λ(c,l). c ≠ 0) acc ⇒
  EVERY (λ(c,l). c ≠ 0) lhs'
Proof
  Induct>>simp[normalize_lhs_def]>>
  Cases>>fs[normalize_lhs_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  intLib.ARITH_TAC
QED

Theorem compact_pbc_to_npbc:
  compact (pbc_to_npbc c)
Proof
  Cases_on`c`>>rw[pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  imp_res_tac compact_lhs_no_dup>>
  pop_assum mp_tac>>
  impl_tac>- (
    match_mp_tac QSORT_SORTED>>
    fs[transitive_term_le]>>
    simp[total_def]>>
    Cases>>Cases>>simp[])>>
  strip_tac>>
  CONJ_TAC>- (
    match_mp_tac normalize_lhs_compact1>>
    asm_exists_tac>>
    simp[sorted_map]>>
    qmatch_goalsub_abbrev_tac`_ tlt _`>>
    `tlt = term_lt` by
      simp[Abbr`tlt`,FUN_EQ_THM,FORALL_PROD]>>
    fs[])>>
  match_mp_tac normalize_lhs_compact2>>
  asm_exists_tac>>
  simp[]
QED

Theorem normalize_compact:
  EVERY compact (normalize pbf)
Proof
  simp[normalize_def,EVERY_MAP,compact_pbc_to_npbc]
QED

(*

We need:
 - addition of constraints
 - division (same factor in each)
 - division (round up coeficients, follows from above version)
 - saturation
 - substitution function (either literal or zero, one)
 - negate a constraint (call it not(c))

 - we have a set of constraints F, and a constraint C,
   suppose we have cutting planes derivation from F UNION not(C)
   a contradiction (any 0 >= k for k > 0),
   then one should accept that F implies C

 - drat-like rule
 - implication (do not remove sat assignments)
 - dominance (more complicated than above)

 the tool:
  - every constraint gets an id
  - logs consist of operations over ids
  - and checking that ids are contraditions
  - another operation: id is exactly this constraint

 a proof is a formula + commands, the proof ends when infeasible set
 is found (finding the line 0 >= k for some k > 0)

*)

val _ = export_theory();
