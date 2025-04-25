(*
  Correctness proof for the freshen pass.
*)

open preamble
open dafny_astTheory
open dafny_evaluateTheory
open dafny_semanticPrimitivesTheory
open mlstringTheory
open mlintTheory
open quantHeuristicsTheory  (* LIST_LENGTH_1 *)

val _ = new_theory "dafny_freshenProof";

Definition lookup_def:
  lookup m old =
  case ALOOKUP m old of
  | NONE => «»
  | SOME cnt => «v» ^ num_to_str cnt
End

Definition add_fresh_def:
  add_fresh m (cnt: num) old = (cnt + 1, (old, cnt)::m)
End

Definition freshen_exp_def:
  freshen_exp m cnt (Lit l) = (cnt, Lit l) ∧
  freshen_exp m cnt (Var old) = (cnt, Var (lookup m old)) ∧
  freshen_exp m cnt (If tst thn els) =
    (let
       (cnt, tst) = freshen_exp m cnt tst;
       (cnt, thn) = freshen_exp m cnt thn;
       (cnt, els) = freshen_exp m cnt els
     in
       (cnt, If tst thn els)) ∧
  freshen_exp m cnt (UnOp uop e) =
    (let (cnt, e) = freshen_exp m cnt e in
       (cnt, UnOp uop e)) ∧
  freshen_exp m cnt (BinOp bop e₁ e₂) =
    (let (cnt, e₁) = freshen_exp m cnt e₁ in
     let (cnt, e₂) = freshen_exp m cnt e₂ in
       (cnt, BinOp bop e₁ e₂)) ∧
  freshen_exp m cnt (ArrLen arr) =
    (let
       (cnt, arr) = freshen_exp m cnt arr
     in
       (cnt, ArrLen arr)) ∧
  freshen_exp m cnt (ArrSel arr idx) =
    (let
       (cnt, arr) = freshen_exp m cnt arr;
       (cnt, idx) = freshen_exp m cnt idx
     in
       (cnt, ArrSel arr idx)) ∧
  freshen_exp m cnt (FunCall n args) =
    (let
       (cnt, args) = freshen_exps m cnt args
     in
       (cnt, FunCall n args)) ∧
  freshen_exp m cnt (Forall (old, vt) e) =
    (let
       (cnt, m) = add_fresh m cnt old;
       (cnt, e) = freshen_exp m cnt e
     in
       (cnt, Forall (lookup m old, vt) e)) ∧
  freshen_exps m cnt [] = (cnt, []) ∧
  freshen_exps m cnt (e::es) =
    (let
       (cnt, e) = freshen_exp m cnt e;
       (cnt, es) = freshen_exps m cnt es
     in
       (cnt, (e::es)))
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL (_,_,e) => exp_size e
                            | INR (_,_,e) => exp1_size e’
End

Theorem freshen_exp_mono:
  (∀m cnt e cnt' e'. freshen_exp m cnt e = (cnt', e') ⇒ cnt ≤ cnt') ∧
  (∀m cnt es cnt' es'. freshen_exps m cnt es = (cnt', es') ⇒ cnt ≤ cnt')
Proof
  ho_match_mp_tac freshen_exp_ind
  >> rpt strip_tac
  >> gvs [freshen_exp_def] >> rpt (pairarg_tac \\ gvs [])
  >> gvs [add_fresh_def]
QED

Definition state_rel_def:
  state_rel s t m cnt ⇔
  s.clock = t.clock ∧ s.heap = t.heap ∧ s.cout = t.cout ∧
  (∀var new_var. ALOOKUP m var = SOME new_var ⇒ new_var < cnt) ∧
  ∀var val.
     read_local s var = SOME val ⇒
     ∃new_var.
       ALOOKUP m var = SOME new_var ∧
       read_local t («v» ^ num_to_str new_var) = SOME val
End

Theorem state_rel_mono:
  ∀ s t m cnt cnt'.
    state_rel s t m cnt ∧ cnt ≤ cnt' ⇒ state_rel s t m cnt'
Proof
  gvs [state_rel_def] \\ rpt strip_tac \\ res_tac \\ gvs []
QED

Theorem mlstring_common_prefix:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
Proof
  rpt Cases
  \\ gvs [strcat_thm, implode_def]
QED

Theorem with_same_locals[simp]:
  ∀s. s with locals := s.locals = s
Proof
  gvs [state_component_equality]
QED

Theorem correct_freshen_exp:
  (∀s env e s' res t m cnt cnt' e'.
     evaluate_exp s env e = (s', res) ∧ state_rel s t m cnt ∧
     freshen_exp m cnt e = (cnt', e') ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exp t env e' = (t', res) ∧ state_rel s' t' m cnt') ∧
  (∀s env es s' res t m cnt cnt' es'.
     evaluate_exps s env es = (s', res) ∧ state_rel s t m cnt ∧
     freshen_exps m cnt es = (cnt', es') ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exps t env es' = (t', res) ∧ state_rel s' t' m cnt')
Proof
  ho_match_mp_tac evaluate_exp_ind \\ rpt strip_tac
  >~ [‘Lit l’] >-
   (gvs [evaluate_exp_def, freshen_exp_def])
  >~ [‘Var v’] >-
   (gvs [evaluate_exp_def, freshen_exp_def, state_rel_def, CaseEq "option"]
    \\ res_tac \\ gvs [lookup_def, SF SFY_ss])
  >~ [‘Forall (v,ty) e’] >-
   (full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ qabbrev_tac ‘f = λval. evaluate_exp (push_local s v val) env e’
    \\ gvs [] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp m1 cnt1 e = (cnt2,e2)’]
    \\ full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ ‘state_rel s t m cnt2’ by
      (gvs [state_rel_def, add_fresh_def] \\ rpt strip_tac
       \\ res_tac \\ imp_res_tac freshen_exp_mono \\ gvs [])
    \\ IF_CASES_TAC >- gvs []
    \\ ‘t.clock = s.clock’ by gvs [state_rel_def]
    \\ IF_CASES_TAC >- gvs []
    \\ qabbrev_tac ‘g = λval. evaluate_exp (push_local t (lookup m1 v) val) env e2’
    \\ ‘s' = s’ by gvs [AllCaseEqs()]
    \\ gvs []
    \\ qexists_tac ‘t’ \\ gvs []
    \\ qpat_x_assum ‘_ = (s,res)’ mp_tac
    \\ IF_CASES_TAC >- gvs []
    \\ gvs []
    \\ qsuff_tac ‘∀v. v ∈ all_values ty ⇒ SND (f v) = SND (g v)’ >-
     (rpt strip_tac \\ gvs [AllCaseEqs()] \\ metis_tac [])
    \\ unabbrev_all_tac \\ gvs []
    \\ qx_gen_tac ‘val’
    \\ Cases_on ‘evaluate_exp (push_local s v val) env e’ \\ gvs []
    \\ first_x_assum $ qspec_then ‘val’ mp_tac \\ gvs []
    \\ rpt strip_tac
    \\ gvs []
    \\ last_x_assum drule \\ fs []
    \\ disch_then $ drule_at $ Pos $ el 2
    \\ disch_then $ qspec_then ‘(push_local t (lookup m1 v) val)’ mp_tac
    \\ reverse impl_tac >- (strip_tac \\ gvs [])
    \\ gvs [state_rel_def,push_local_def]
    \\ conj_tac >-
     (gvs [add_fresh_def,AllCaseEqs()]
      \\ rpt strip_tac \\ gvs []
      \\ res_tac \\ gvs [])
    \\ gvs [read_local_def]
    \\ gvs [add_fresh_def]
    \\ gvs [lookup_def]
    \\ rpt strip_tac
    \\ rename [‘_ = SOME val2’]
    \\ IF_CASES_TAC \\ gvs []
    >- gvs [read_local_aux_def,FLOOKUP_SIMP]
    \\ ‘read_local_aux s.locals var = SOME val2’ by
      gvs [read_local_aux_def,FLOOKUP_SIMP]
    \\ first_x_assum drule
    \\ strip_tac \\ simp []
    \\ gvs [read_local_aux_def,FLOOKUP_SIMP]
    \\ reverse IF_CASES_TAC >- gvs []
    \\ gvs [mlstring_common_prefix, num_to_str_11]
    \\ res_tac \\ gvs [])
  >~ [‘FunCall name args’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exps _ _ _ = (cnt₁, args')’]
    \\ gvs [evaluate_exp_def]
    \\ Cases_on ‘FLOOKUP env.functions name’ \\ gvs []
    \\ namedCases_on ‘x’ ["in_ns body"] \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env args’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ last_x_assum kall_tac
    \\ rename [‘state_rel s₁ t₁ m cnt₁’]
    \\ gvs [set_up_call_def] \\ CASE_TAC \\ gvs []
    \\ rename [‘safe_zip _ _ = SOME ins’]
    \\ ‘s₁.clock = t₁.clock’ by gvs [state_rel_def]
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >- gvs [restore_locals_def]
    \\ namedCases_on ‘evaluate_exp (dec_clock (s₁ with locals := [FEMPTY |++ ins])) env body’ ["s₂ r"] \\ gvs []
    \\ ‘s₁ with locals := [FEMPTY |++ ins] = t₁ with locals := [FEMPTY |++ ins]’
      by gvs [state_component_equality, state_rel_def]
    \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ gvs [restore_locals_def, state_rel_def, read_local_def, SF SFY_ss])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_mono
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env tst’ ["s₁ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac state_rel_mono
    \\ rename [‘evaluate_exp t env tst' = (t₁,Rval tst_v)’]
    \\ namedCases_on ‘do_cond tst_v thn els’ ["", "branch"] \\ gvs []
    \\ namedCases_on ‘do_cond tst_v thn' els'’ ["", "branch'"] \\ gvs []
    \\ gvs [oneline do_cond_def, AllCaseEqs ()]
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ disch_then $ drule  \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac state_rel_mono)
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘do_uop uop v’ ["", "r"] \\ gvs [])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp m cnt e₀ = (cnt₁,e₀')’,
               ‘freshen_exp m cnt₁ e₁ = (cnt₂,e₁')’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e₀’ ["s₁ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["v₀", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ rename [‘evaluate_exp t₁ env e₁'’]
    \\ reverse $ namedCases_on ‘try_sc bop v₀’ ["", "r"] \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exp s₁ env e₁’ ["s₂ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["v₁", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘do_bop bop v₀ v₁’ ["", "r"] \\ gvs [])
  >~ [‘ArrLen arr’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"]
    \\ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs [])
  >~ [‘ArrSel arr idx’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ rename [‘evaluate_exp t _ _' = (t₁, _)’]
    \\ namedCases_on ‘evaluate_exp s₁ env idx’ ["s₂ r"]
    \\ namedCases_on ‘r’ ["idx_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate_exp t₁ _ _' = (t₂, _)’]
    \\ namedCases_on ‘index_array s₂ arr_v idx_v’ ["", "v"] \\ gvs []
    \\ namedCases_on ‘index_array t₂ arr_v idx_v’ ["", "v'"] \\ gvs []
    \\ gvs [index_array_def, state_rel_def, AllCaseEqs ()])
  >~ [‘freshen_exps m cnt []’] >- gvs [evaluate_exp_def, freshen_exp_def]
  >~ [‘freshen_exps m cnt (e::es)’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exps s₁ env es’ ["s₂ r"]
    \\ namedCases_on ‘r’ ["vs", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [])
QED

Definition rename_locals_def:
  (rename_locals m cnt [] = (cnt, m, [])) ∧
  (rename_locals m cnt (l::ls) =
   let (ln, lt) = l in
   let (cnt, m) = add_fresh m cnt ln in
   let l = (lookup m ln, lt) in
   let (cnt, m, ls) = rename_locals m cnt ls in
     (cnt, m, l::ls))
End

Theorem rename_locals_lt_not_mem:
  ∀m cnt locals cnt' m' locals' i.
    rename_locals m cnt locals = (cnt', m', locals') ∧ i < cnt ⇒
    ¬MEM («v» ^ toString i) (MAP FST locals')
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [rename_locals_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [add_fresh_def, lookup_def, mlstring_common_prefix, num_to_str_11]
  \\ ‘i < cnt + 1’ by gvs [] \\ last_x_assum drule_all \\ gvs []
QED

Theorem rename_locals_all_distinct:
  ∀m cnt locals cnt' m' locals'.
    rename_locals m cnt locals = (cnt', m', locals') ∧
    ALL_DISTINCT (MAP FST locals) ⇒
    ALL_DISTINCT (MAP FST locals')
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [rename_locals_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ last_x_assum $ drule_all \\ strip_tac \\ gvs []
  \\ gvs [add_fresh_def, lookup_def]
  \\ imp_res_tac rename_locals_lt_not_mem
  \\ pop_assum $ qspec_then ‘cnt’ mp_tac \\ gvs []
QED

Definition freshen_stmt_def:
  (freshen_stmt m cnt (Dec locals scope) =
   let (cnt, m, locals) = rename_locals m cnt locals in
   let (cnt, scope) = freshen_stmt m cnt scope in
     (cnt, Dec locals scope)) ∧
  (freshen_stmt m cnt (Then stmt₀ stmt₁) =
   let (cnt, stmt₀) = freshen_stmt m cnt stmt₀ in
   let (cnt, stmt₁) = freshen_stmt m cnt stmt₁ in
     (cnt, Then stmt₀ stmt₁)) ∧
  (freshen_stmt m cnt _ = ARB)
End

Theorem freshen_stmt_mono:
  ∀m cnt stmt cnt' stmt'.
    freshen_stmt m cnt stmt = (cnt', stmt') ⇒ cnt ≤ cnt'
Proof
  cheat
QED

Theorem locals_not_empty_pop_locals_some:
  ∀s. LENGTH s.locals > 0 ⇒ ∃s'. pop_locals s = SOME s'
Proof
  rpt strip_tac \\ gvs [pop_locals_def, LIST_LENGTH_1]
QED

Theorem evaluate_stmt_len_locals:
  evaluate_stmt s env scope = (s', r) ⇒
  LENGTH s'.locals = LENGTH s.locals
Proof
  cheat
QED



Theorem rename_locals_mono:
  ∀m cnt locals cnt' m' used.
    rename_locals m cnt locals = (cnt', m', used) ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [rename_locals_def, add_fresh_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ res_tac \\ gvs []
QED

Theorem correct_freshen_stmt:
  ∀s env stmt s' res t m cnt cnt' stmt'.
    evaluate_stmt s env stmt = (s', res) ∧ state_rel s t m cnt ∧
    freshen_stmt m cnt stmt = (cnt', stmt') ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'. evaluate_stmt t env stmt' = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Induct_on ‘stmt’ \\ rpt strip_tac
  >~ [‘Dec locals scope’] >-

   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ qabbrev_tac ‘s₁ = declare_locals s (MAP FST locals)’
    \\ qabbrev_tac ‘t₁ = declare_locals t (MAP FST locals')’
    \\ rename [‘rename_locals m cnt locals = (cnt₁, m₁, locals')’,
               ‘freshen_stmt m₁ cnt₁ scope = (cnt₂, scope')’,
               ‘evaluate_stmt s₁ env scope = (s₂, res)’]
    \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘evaluate_stmt t₁ env scope' = (t₂, res')’]
    \\ Cases_on ‘ALL_DISTINCT (MAP FST locals)’ \\ gvs []
    \\ imp_res_tac rename_locals_all_distinct \\ gvs []
    \\ rpt $ qpat_x_assum ‘ALL_DISTINCT _’ kall_tac
    \\ imp_res_tac evaluate_stmt_len_locals
    \\ ‘LENGTH s₂.locals > 0’ by (unabbrev_all_tac \\ gvs [declare_locals_def])
    \\ ‘LENGTH t₂.locals > 0’ by (unabbrev_all_tac \\ gvs [declare_locals_def])
    \\ imp_res_tac locals_not_empty_pop_locals_some \\ gvs []
    \\ rpt $ qpat_x_assum ‘LENGTH _ = _’ kall_tac
    \\ rpt $ qpat_x_assum ‘LENGTH _ > _’ kall_tac
    \\ rename [‘pop_locals s₂ = SOME s₃’] \\ pop_assum $ mp_tac
    \\ rename [‘pop_locals t₂ = SOME t₃’] \\ strip_tac
    \\ qsuff_tac ‘state_rel s₁ t₁ m₁ cnt₁’
    >- (strip_tac \\ last_x_assum $ drule_all \\ strip_tac \\ gvs []
        \\ rename [‘evaluate_stmt _ _ _' = (t₂, _)’]


        \\ gvs [state_rel_def, pop_locals_def, AllCaseEqs()]
        \\ conj_tac
        >- (imp_res_tac rename_locals_mono \\ imp_res_tac freshen_stmt_mono
            \\ rpt strip_tac \\ res_tac \\ gvs [])

        \\ rename [‘s₂.locals = decs::prev_locals’]
        \\ qpat_x_assum ‘s₂.locals = _’ mp_tac
        \\ rename [‘t₂.locals = decs'::prev_locals'’] \\ strip_tac
        \\ rpt strip_tac \\ gvs [read_local_def]
       )
    >- cheat)
  \\ cheat
QED


val _ = export_theory ();
