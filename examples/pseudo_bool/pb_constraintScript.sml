(*
  A formalisation of pseudo-boolean constraints
*)

open preamble;

val _ = new_theory "pb_constraint";

val _ = numLib.prefer_num();

(* abstract syntax for normalised syntax *)

Type var = “:num”

Datatype:
  lit = Pos var | Neg var
End

Datatype:
  pb_constraint = PBC ((num # lit) list) num
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

Definition eval_pbc_def:
  eval_pbc w (PBC xs n) ⇔ SUM (MAP (eval_term w) xs) ≥ n
End

(* compactness *)

Definition get_var_def[simp]:
  get_var (Pos n) = n ∧
  get_var (Neg n) = n
End

Definition term_lt_def[simp]:
  term_lt (_,l1) (_,l2) = (get_var l1 < get_var l2)
End

Definition compact_def[simp]:
  compact (PBC xs n) ⇔
    SORTED term_lt xs ∧ (* implies that no var is mentioned twice *)
    EVERY (λ(c,l). c ≠ 0) xs ∧
    (n = 0 ⇒ xs = [])
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
      if m+n ≤ d then PBC [] 0 else
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
  eval_pbc w c1 ∧ eval_pbc w c2 ⇒ eval_pbc w (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’ \\ fs [add_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [eval_pbc_def]
  \\ drule_all add_lists_thm
  \\ disch_then (qspec_then ‘w’ assume_tac)
  \\ fs []
QED

(* addition -- compactness *)

Theorem add_lists_sorted:
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

Theorem compact_add:
  compact c1 ∧ compact c2 ⇒ compact (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’ \\ fs [add_def]
  \\ pairarg_tac \\ fs [] \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  \\ last_x_assum mp_tac
  \\ rpt (qpat_x_assum ‘SORTED _ _’ mp_tac)
  \\ rpt (qpat_x_assum ‘EVERY _ _’ mp_tac)
  \\ EVERY (map qid_spec_tac [‘d’,‘xs’,‘l'’,‘l’])
  \\ ho_match_mp_tac add_lists_ind
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
    \\ drule add_lists_sorted \\ fs [])
  \\ Cases_on ‘term_lt y x’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
    \\ drule add_lists_sorted \\ fs [])
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rename [‘get_var l1 < get_var l2’]
  \\ ‘z = [] ∨ ∃c l. z = [(c,l)] ∧ get_var l = get_var l1’ by
    gvs [AllCaseEqs(),add_terms_def |> DefnBase.one_line_ify NONE]
  \\ gvs [] \\ Cases_on ‘zs’ \\ fs []
  \\ drule add_lists_sorted
  \\ disch_then irule \\ rw []
  \\ rename [‘_::l5’]
  \\ Cases_on ‘l5’ \\ fs []
  \\ Cases_on ‘h'’ \\ fs []
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
  eval_pbc w c ∧ k ≠ 0 ⇒ eval_pbc w (divide c k)
Proof
  Cases_on ‘c’ \\ fs [divide_def]
  \\ rw [eval_pbc_def,GREATER_EQ,div_ceiling_le_x]
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ Induct_on ‘l’ \\ fs [FORALL_PROD]
  \\ fs [LEFT_ADD_DISTRIB] \\ rw []
  \\ irule (DECIDE “m ≤ m1 ∧ n ≤ n1 ⇒ m+n ≤ m1+n1:num”)
  \\ fs [le_mult_div_ceiling]
QED

(* negation *)

Definition negate_def[simp]:
  negate (Pos n) = Neg n ∧
  negate (Neg n) = Pos n
End

Definition not_def:
  not (PBC l n) = PBC (MAP (I ## negate) l) (SUM (MAP FST l) + 1 - n)
End

Theorem negate_thm:
  eval_pbc w (not c) ⇔ ~eval_pbc w c
Proof
  Cases_on ‘c’ \\ fs [not_def,eval_pbc_def,GREATER_EQ]
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
    PBC (MAP (λ(c,v). (c * k, v)) l) (n * k)
End

(* k ≠ 0 needed for compactness *)
Theorem multiply_thm:
  eval_pbc w c ⇒ eval_pbc w (multiply c k)
Proof
  Cases_on ‘c’ \\ fs [multiply_def]
  \\ rw [eval_pbc_def,GREATER_EQ]
  \\ drule LESS_MONO_MULT
  \\ disch_then (qspec_then`k` mp_tac)
  \\ REWRITE_TAC [Once MULT_COMM]
  \\ strip_tac
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ pop_assum kall_tac
  \\ Induct_on`l` \\ simp[] \\ Cases
  \\ rw[]
QED

(* saturation *)
Definition saturate_def:
  saturate (PBC l n) =
    PBC (MAP (λ(c,v). (MIN c n, v)) l) n
End

Theorem eval_lit_bool:
  eval_lit w r = 0 ∨ eval_lit w r = 1
Proof
  Cases_on`r` \\ rw[eval_lit_def]
  \\ Cases_on`w n` \\ rw[b2n_def]
QED

Theorem saturate_thm:
  eval_pbc w c ⇒ eval_pbc w (saturate c)
Proof
  Cases_on ‘c’ \\ fs [saturate_def]
  \\ rw [eval_pbc_def,GREATER_EQ]
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
  eval_pbc w c ⇒ eval_pbc w (weaken c v)
Proof
  Cases_on ‘c’ \\ fs [weaken_def]
  \\ pairarg_tac \\ fs[]
  \\ rw [eval_pbc_def,GREATER_EQ]
  \\ match_mp_tac weaken_aux_theorem0
  \\ metis_tac[]
QED

(* substitution/instantiation *)

Definition assign_def:
  assign f (w:num->bool) (n:num) =
    case lookup n f of
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
      case lookup (get_var l) f of
      | NONE => ((c,l)::old,new,k)
      | SOME (INL b) => (old,new,if is_Pos l = b then k+c else k)
      | SOME (INR n) => let x = (if is_Pos l then n else negate n) in
                          (old,(c,x)::new,k)
End

Definition subst_def:
  subst f (PBC l n) =
    let (old,new,k) = subst_aux f l in
      (PBC (old ++ new) (n - k))  (* TODO: replace ++ by addition *)
End

Theorem subst_thm:
  eval_pbc w (subst f c) = eval_pbc (assign f w) c
Proof
  Cases_on ‘c’ \\ fs [eval_pbc_def,subst_def]
  \\ pairarg_tac \\ gvs [eval_pbc_def,GREATER_EQ]
  \\ qsuff_tac
    ‘∀l old new k.
       subst_aux f l = (old,new,k) ⇒
       SUM (MAP (eval_term (assign f w)) l) =
       k + SUM (MAP (eval_term w) old ++ MAP (eval_term w) new)’
  THEN1 (disch_then drule \\ fs [])
  \\ Induct \\ fs [subst_aux_def,FORALL_PROD]
  \\ pairarg_tac \\ fs []
  \\ rw []
  \\ Cases_on ‘lookup (get_var p_2) f’ \\ gvs [assign_def]
  THEN1 (Cases_on ‘p_2’ \\ fs [assign_def])
  \\ Cases_on ‘x’ \\ gvs []
  THEN1 (Cases_on ‘p_2’ \\ fs [assign_def] \\ Cases_on ‘x'’ \\ fs [])
  \\ Cases_on ‘p_2’ \\ Cases_on ‘y’ \\ fs [assign_def]
  \\ Cases_on ‘w n'’ \\ fs [SUM_APPEND]
QED

(*

We need:
 - addition of constraints
 - division (same factor in each)
 - division (round up coeficients, follows from above version)
 - saturation

  3 * x + 1 * y + 1 * z >= 2
  ⇒
  (MIN 2 3) * x + (MIN 2 1) * y + (MIN 2 1) * z >= 2

 - substitution function (either literal or zero, one)
     num -> lit + bool

 YK: would it make sense to separate into subst (lit for lit) and
     inst (lit to const)? (Answer: perhaps it makes sense for impl.)

 YK: how does unit propagation work in this context?
 Stephan: perhaps we want to have the tool able to figure out
          unit propagation proof

 - negate a constraint (call it not(c))

  3 * x + 1 * y + 1 * z >= 2
-->
  3 * x + 1 * y + 1 * z < 2 and then noramlise
  3 * x + 1 * y + 1 * z ≤ 1
  -3 * x + -1 * y + -1 * z >= -1

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

(* junk

Definition get_val_def:
  get_val n s =
    case lookup n s of
    | NONE => (F,0)
    | SOME res => res
End

Definition update_term_def:
  update_term f (c,l) =
    case lookup (get_var l) f of
    | NONE => INL (c,l)
    | SOME (INL b) => INR (if is_Pos l = b then c else 0)
    | SOME (INR (Pos v)) => INL (c,if is_Pos l then Pos v else Neg v)
    | SOME (INR (Neg v)) => INL (c,if is_Pos l then Neg v else Pos v)
End

Definition subst_aux_def:
  subst_aux f (c,l) (s,k) =
    case update_term f (c,l) of
    | INR k' => (s,k+k')
    | INL (c',l') =>
      case lookup (get_var l) s of
      | NONE => (insert (get_var l) (c',l') s,k)
      | SOME (c1,l1) =>
        case add_terms (c',l') (c',l') of
        | ([],k') => (delete (get_var l) s,k+k')
        | (r::_,k') => (insert (get_var l) r s,k+k')
End

Definition subst_def:
  subst f (PBC l n) =
    let (s,k) = FOLDR (subst_aux f) (LN,0) l in
      PBC (MAP SND (toSortedAList s)) (n - k)
End

Theorem SUM_toSortedAList_NONE:
  lookup n s = NONE ⇒
  SUM (MAP (eval_term w) (MAP SND (toSortedAList (insert n x s)))) =
  eval_term w x + SUM (MAP (eval_term w) (MAP SND (toSortedAList s)))
Proof
  cheat
QED

Theorem SUM_toSortedAList_SOME:
  lookup n s = SOME y ⇒
  SUM (MAP (eval_term w) (MAP SND (toSortedAList (insert n x s)))) =
  eval_term w x + SUM (MAP (eval_term w) (MAP SND (toSortedAList (delete n s))))
Proof
  cheat
QED

Theorem SUM_toSortedAList_SOME_1:
  lookup n s = SOME y ⇒
  SUM (MAP (eval_term w) (MAP SND (toSortedAList s))) =
  eval_term w y + SUM (MAP (eval_term w) (MAP SND (toSortedAList (delete n s))))
Proof
  cheat
QED

Theorem subst_thm:
  eval_pbc w (subst f c) = eval_pbc (assign f w) c
Proof
  Cases_on ‘c’ \\ fs [eval_pbc_def,subst_def]
  \\ pairarg_tac \\ gvs [eval_pbc_def,GREATER_EQ]
  \\ qsuff_tac
    ‘∀l s' k' s k.
      FOLDR (subst_aux f) (s',k') l = (s,k) ⇒
      SUM (MAP (eval_term (assign f w)) l) +
      SUM (MAP (eval_term w) (MAP SND (toSortedAList s'))) + k' =
      SUM (MAP (eval_term w) (MAP SND (toSortedAList s))) + k’
  THEN1 (disch_then drule \\ fs [EVAL “toSortedAList LN”])
  \\ pop_assum kall_tac
  \\ Induct \\ fs [] \\ rw []
  \\ Cases_on ‘FOLDR (subst_aux f) (s',k') l’
  \\ rename [‘_ = (s2,k2)’]
  \\ first_x_assum drule \\ rw []
  \\ qabbrev_tac ‘d = SUM (MAP (eval_term w) (MAP SND (toSortedAList s')))’
  \\ last_x_assum mp_tac
  \\ PairCases_on ‘h’
  \\ rewrite_tac [subst_aux_def,update_term_def]
  \\ Cases_on ‘h1’ \\ fs [get_var_def,assign_def,is_Pos_def]

    Cases_on ‘lookup n f’ \\ fs []

      Cases_on ‘lookup n s2’ \\ fs [] \\ rw []
      THEN1 fs [SUM_toSortedAList_NONE]
      \\ gvs [add_terms_def,SUM_toSortedAList_SOME]

      drule SUM_toSortedAList_SOME_1

      \\ cheat

    \\ Cases_on ‘x’ \\ fs []
    THEN1 (Cases_on ‘x'’ \\ fs [] \\ rw [] \\ gvs [])
    \\ Cases_on ‘y’ \\ fs []

      Cases_on ‘lookup n s2’ \\ rw []
      \\ fs [SUM_toSortedAList_NONE]

  \\ drule FOLDR_subst_aux_lemma
  \\ fs [EVAL “toSortedAList LN”]
QED

*)

val _ = export_theory();
