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

Triviality freshen_exp_mono:
  (∀m cnt e cnt' e'. freshen_exp m cnt e = (cnt', e') ⇒ cnt ≤ cnt') ∧
  (∀m cnt es cnt' es'. freshen_exps m cnt es = (cnt', es') ⇒ cnt ≤ cnt')
Proof
  ho_match_mp_tac freshen_exp_ind
  >> rpt strip_tac
  >> gvs [freshen_exp_def] >> rpt (pairarg_tac \\ gvs [])
  >> gvs [add_fresh_def]
QED

Definition locals_rel_def:
  locals_rel [] [] [] _ = T ∧
  locals_rel (sl::ss) (ml::ms) (tl::ts) (ub:num) =
  (let (snam, sval) = sl; (snam', tnum) = ml; (tnam, tval) = tl in
     (tnum < ub ∧ snam = snam' ∧ tnam = («v» ^ num_to_str tnum) ∧
      sval = tval ∧ locals_rel ss ms ts tnum)) ∧
  locals_rel _ _ _ _ = F
End

Definition state_rel_def:
  state_rel s t m cnt ⇔
  s.clock = t.clock ∧ s.heap = t.heap ∧ s.cout = t.cout ∧
  locals_rel s.locals m t.locals cnt
End

(* TODO Move to mlstring *)
Theorem mlstring_common_prefix:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
Proof
  rpt Cases \\ gvs [strcat_thm, implode_def]
QED

Triviality locals_rel_lookup_neq:
  ∀ss m ts ub i var.
    locals_rel ss m ts ub ∧ i ≥ ub ⇒ lookup m var ≠ «v» ^ toString i
Proof
  Induct_on ‘m’ \\ Cases_on ‘ss’ \\ Cases_on ‘ts’ \\ rpt strip_tac
  \\ gvs [locals_rel_def, lookup_def] >- gvs [strcat_thm, implode_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ FULL_CASE_TAC \\ gvs [mlstring_common_prefix, num_to_str_11]
  \\ ‘i ≥ tnum’ by gvs []
  \\ last_x_assum $ drule_all \\ rpt strip_tac \\ res_tac
QED

Triviality locals_rel_read_local:
  ∀ss m ts cnt var val.
    locals_rel ss m ts cnt ∧
    read_local ss var = SOME val ⇒
    read_local ts (lookup m var) = SOME val
Proof
  Induct_on ‘m’ \\ Cases_on ‘ss’ \\ Cases_on ‘ts’ \\ rpt strip_tac
  \\ gvs [locals_rel_def, read_local_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac locals_rel_lookup_neq \\ res_tac
  \\ rename [‘lookup ((snam,tnum)::m)’]
  \\ Cases_on ‘snam = var’ \\ gvs [lookup_def]
QED

Triviality locals_rel_mono:
  ∀ss m ts cnt cnt'.
    locals_rel ss m ts cnt ∧ cnt ≤ cnt' ⇒ locals_rel ss m ts cnt'
Proof
  Cases_on ‘m’ \\ Cases_on ‘ss’ \\ Cases_on ‘ts’ \\ rpt strip_tac
  \\ gvs [locals_rel_def] \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality state_rel_mono:
  ∀s t m cnt cnt'.
    state_rel s t m cnt ∧ cnt ≤ cnt' ⇒ state_rel s t m cnt'
Proof
  gvs [state_rel_def] \\ rpt strip_tac \\ imp_res_tac locals_rel_mono
QED

(* TODO Move to Dafny semantic primitives *)
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
    \\ imp_res_tac locals_rel_read_local)
  >~ [‘Forall (v,ty) e’] >-
   (full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ qabbrev_tac ‘f = λval. evaluate_exp (push_local s v val) env e’
    \\ gvs [] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp m₁ cnt₁ e = (cnt₂,e₂)’]
    \\ full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ ‘state_rel s t m cnt₂’ by
      (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono
       \\ gvs [add_fresh_def])
    \\ IF_CASES_TAC >- gvs []
    \\ ‘t.clock = s.clock’ by gvs [state_rel_def]
    \\ IF_CASES_TAC >- gvs []
    \\ qabbrev_tac ‘g = λval. evaluate_exp (push_local t (lookup m₁ v) val) env e₂’
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
    \\ disch_then $ qspec_then ‘(push_local t (lookup m₁ v) val)’ mp_tac
    \\ reverse impl_tac >- (strip_tac \\ gvs [])
    \\ gvs [state_rel_def, push_local_def,
            add_fresh_def, locals_rel_def, lookup_def])
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
    \\ namedCases_on ‘evaluate_exp (dec_clock (s₁ with locals := ins)) env body’
                     ["s₂ r"] \\ gvs []
    \\ ‘(s₁ with locals := ins) = (t₁ with locals := ins)’
      by gvs [state_component_equality, state_rel_def] \\ rpt strip_tac \\ gvs []
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

Definition freshen_stmt_def:
  (freshen_stmt m cnt (Dec local scope) =
   let (old, vt) = local in
   let (cnt, m) = add_fresh m cnt old in
   let (cnt, scope) = freshen_stmt m cnt scope in
     (cnt, Dec (lookup m old, vt) scope)) ∧
  (freshen_stmt m cnt (Then stmt₀ stmt₁) =
   let (cnt, stmt₀) = freshen_stmt m cnt stmt₀ in
   let (cnt, stmt₁) = freshen_stmt m cnt stmt₁ in
     (cnt, Then stmt₀ stmt₁)) ∧
  (freshen_stmt m cnt _ = ARB)
End

Triviality declare_local_len_gt:
  ∀s v. LENGTH (declare_local s v).locals = LENGTH s.locals + 1
Proof
  gvs [declare_local_def]
QED

Triviality evaluate_stmt_len_locals:
  ∀s env scope s' r.
    evaluate_stmt s env scope = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  cheat
QED

Triviality locals_not_empty_pop_locals_some:
  ∀s. LENGTH s.locals > 0 ⇒ ∃s'. pop_local s = SOME s'
Proof
  rpt strip_tac \\ gvs [pop_local_def, LIST_LENGTH_1]
QED

Triviality locals_rel_weaken_ub:
  ∀ss ms ts ub ub'.
    locals_rel ss ms ts ub ∧ ub < ub' ⇒ locals_rel ss ms ts ub'
Proof
  Cases_on ‘ss’ \\ Cases_on ‘ms’ \\ Cases_on ‘ts’
  \\ gvs [locals_rel_def] \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality locals_rel_pop:
  ∀sl ss ml ms tl ts ub.
    locals_rel (sl::ss) (ml::ms) (tl::ts) ub ⇒ locals_rel ss ms ts ub
Proof
  gvs [locals_rel_def] \\ rpt strip_tac \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac locals_rel_weaken_ub
QED

Triviality locals_rel_push:
  ∀ss ms ts cnt cnt' old v.
    locals_rel ss ms ts cnt ∧ cnt < cnt' ⇒
    locals_rel ((old, v)::ss) ((old, cnt)::ms)
      ((lookup ((old, cnt)::ms) old, v)::ts) cnt'
Proof
  gvs [locals_rel_def, lookup_def] \\ rpt strip_tac
QED

Theorem correct_freshen_stmt:
  ∀s env stmt s' res t m cnt cnt' stmt'.
    evaluate_stmt s env stmt = (s', res) ∧ state_rel s t m cnt ∧
    freshen_stmt m cnt stmt = (cnt', stmt') ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'. evaluate_stmt t env stmt' = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Induct_on ‘stmt’ \\ rpt strip_tac
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘add_fresh m cnt old = (cnt₁, m')’]
    \\ qabbrev_tac ‘s₁ = declare_local s old’
    \\ rename [‘freshen_stmt m' cnt₁ scope = (cnt₂, scope')’,
               ‘evaluate_stmt s₁ env scope = (s₂, r)’]
    \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ qabbrev_tac ‘t₁ = declare_local t (lookup m' old)’
    \\ rename [‘evaluate_stmt t₁ env scope' = (t₂, r')’]
    \\ qspecl_then [‘s’, ‘old’] assume_tac declare_local_len_gt
    \\ qspecl_then [‘t’, ‘lookup m' old’] assume_tac declare_local_len_gt
    \\ imp_res_tac evaluate_stmt_len_locals
    \\ imp_res_tac locals_not_empty_pop_locals_some
    \\ ‘LENGTH s₂.locals > 0’ by gvs []
    \\ ‘LENGTH t₂.locals > 0’ by gvs []
    \\ imp_res_tac locals_not_empty_pop_locals_some \\ gvs []
    \\ rpt $ qpat_x_assum ‘LENGTH _ = _’ kall_tac
    \\ rename [‘pop_local s₂ = SOME s₃’] \\ pop_assum $ mp_tac
    \\ rename [‘pop_local t₂ = SOME t₃’] \\ strip_tac
    \\ qsuff_tac ‘state_rel s₁ t₁ m' cnt₁’
    >- (strip_tac \\ last_x_assum $ drule_all \\ strip_tac \\ gvs []
        \\ rename [‘evaluate_stmt _ _ _' = (t₂, _)’]
        \\ gvs [state_rel_def, pop_local_def, add_fresh_def, AllCaseEqs()]
        \\ imp_res_tac locals_rel_pop)
    \\ unabbrev_all_tac
    \\ gvs [state_rel_def, declare_local_def, add_fresh_def]
    \\ imp_res_tac locals_rel_push \\ gvs [])
  \\ cheat
QED

val _ = export_theory ();
