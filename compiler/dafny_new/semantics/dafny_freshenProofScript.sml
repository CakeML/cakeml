(*
  Correctness proof for the freshen pass.
*)

open preamble
open dafny_astTheory
open dafny_evaluateTheory
open dafny_semanticPrimitivesTheory

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

Theorem mlstring_common_prefix:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
Proof
  rpt Cases
  \\ gvs [mlstringTheory.strcat_thm,mlstringTheory.implode_def]
QED

Theorem with_same_locals[simp]:
  ∀s. s with locals := s.locals = s
Proof
  gvs [state_component_equality]
QED

Theorem evaluate_exp_freshen_exp:
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
     (rpt strip_tac
      (* todo: try holyhammer *)
      \\ gvs [] \\ gvs [AllCaseEqs()] \\ metis_tac [])
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
    \\ gvs [mlstring_common_prefix,mlintTheory.num_to_str_11]
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
  \\ cheat

(*
  >- gvs [evaluate_exp_def, freshen_exp_def]
  >- gvs [evaluate_exp_def, freshen_exp_def, state_rel_def, CaseEq "option"]
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
   (*  >> rpt (pairarg_tac \\ gvs []) *)
   (*  >> last_x_assum $ drule_all >> strip_tac *)
   (*  >> gvs [evaluate_exp_def, oneline do_cond_def, AllCaseEqs ()] *)
   (*  >> qsuff_tac ‘∀c. MEM c (MAP SND m) ⇒ c < cnt''’ >> rpt strip_tac *)
   (*  >- (last_x_assum $ drule_all >> strip_tac >> gvs []) *)
   (*  >- (first_assum $ drule_then assume_tac >> imp_res_tac foo >> decide_tac) *)
   (*  >- (last_x_assum $ drule_all >> strip_tac >> gvs [])) *)
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
   (*  >> rpt (pairarg_tac \\ gvs []) *)
   (*  >> last_x_assum $ drule_all >> strip_tac >> gvs [evaluate_exp_def]) *)
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
   (*  >> rpt (pairarg_tac \\ gvs []) *)
   (*  >> rpt (last_x_assum $ drule_all >> strip_tac) >> gvs [evaluate_exp_def]) *)
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
   (*  >> rpt (pairarg_tac \\ gvs []) *)
   (*  >> last_x_assum $ drule_all >> strip_tac >> gvs [evaluate_exp_def]) *)
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
   (*  >> rpt (pairarg_tac \\ gvs []) *)
   (*  >> rpt (last_x_assum $ drule_all >> strip_tac) *)
   (*  >> gvs [evaluate_exp_def, index_array_def, state_rel_def]) *)
  >- cheat
   (* (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
  (*   >> rpt (pairarg_tac \\ gvs []) *)
  (*   >- gvs [evaluate_exp_def] *)
  (*   >- *)
  (*    (last_x_assum $ drule_all >> strip_tac >> gvs [evaluate_exp_def, state_rel_def]) *)
  (*   >- *)
  (*    (last_x_assum $ drule_all >> strip_tac *)
  (*     >> gvs [evaluate_exp_def, set_up_call_def, state_rel_def, AllCaseEqs ()]) *)
  (*   >- *)
  (*    (last_x_assum $ drule_all >> strip_tac *)
  (*     >> gvs [evaluate_exp_def, state_rel_def, set_up_call_def, *)
  (*             restore_locals_def, AllCaseEqs ()] *)
  (*     >> qsuff_tac ‘(t' with locals := [FEMPTY |++ params]) = (st₁ with locals := [FEMPTY |++ params])’ *)
  (*     >- (rpt strip_tac >> gvs [read_local_def]) *)
  (*     >- gvs [state_component_equality]) *)
  (*   >- *)
  (*    (last_x_assum $ drule_all >> strip_tac *)
  (*     >> gvs [evaluate_exp_def, set_up_call_def, state_rel_def, *)
  (*             restore_locals_def, AllCaseEqs ()] *)
  (*     >> qsuff_tac ‘(t' with locals := [FEMPTY |++ params]) = (st₁ with locals := [FEMPTY |++ params])’ *)
  (*     >- (rpt strip_tac >> gvs [read_local_def]) *)
  (*     >- gvs [state_component_equality]) *)
  (*   >- (last_x_assum $ drule_all >> strip_tac >> gvs [evaluate_exp_def])) *)
  (* >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def, AllCaseEqs ()] *)
  (*   >> rpt (pairarg_tac \\ gvs []) *)
  (*   >> gvs [evaluate_exp_def, state_rel_def, AllCaseEqs ()]) *)
  >-
   (gvs [freshen_exp_def] >> rpt (pairarg_tac \\ gvs [])
    >> gvs [evaluate_exp_def, state_rel_def, AllCaseEqs ()]
    >-
     (qexists ‘v’ >> gvs []
      >> Cases_on ‘evaluate_exp (dec_clock (push_local s vn v)) env e’ >> gvs []
      >> last_x_assum $ drule_then assume_tac
      >> pop_assum $ qspecl_then [‘dec_clock (push_local t (lookup m' vn) v)’,
                                  ‘m'’, ‘cnt''’, ‘cnt'’, ‘e''’] mp_tac
      >> impl_tac
      >- (gvs [dec_clock_def, push_local_def, add_fresh_def, AllCaseEqs ()]
          >> rpt strip_tac
          >- (Cases_on ‘vn = old’
              >- gvs [read_local_def, lookup_def, read_local_aux_def, FLOOKUP_SIMP]
              >- (gvs [read_local_def, FLOOKUP_SIMP, lookup_def] >> CASE_TAC
                  >> first_x_assum $ qspec_then ‘old’ assume_tac
                  >> gvs [read_local_aux_def, FLOOKUP_SIMP, AllCaseEqs ()] >> rpt strip_tac)))


      >> Cases_on ‘evalt v’ >> gvs []
      >> last_x_assum $ drule_then assume_tac
      >> imp_res_tac foobar

        >> pop_assum $ qspecl_then [‘(dec_clock (push_local t' var v))’, ‘m'’] assume_tac
        >> gvs [push_local_def, dec_clock_def, read_local_def,
                read_local_aux_def, FLOOKUP_SIMP, AllCaseEqs ()]
        >> first_x_assum $ drule_then assume_tac

    )



  (* >- (rename [‘Forall (var, ty)’, ‘state_rel s t’] *)
  (*     >> FULL_SIMP_TAC (srw_ss()) [evaluate_exp_def] *)
  (*     >> qmatch_goalsub_abbrev_tac ‘LET _ evalt’ >> simp [] *)
  (*     >> qmatch_asmsub_abbrev_tac ‘LET _ evals’ *)
  (*     >> qpat_x_assum ‘COND _ _ _ = _’ $ mp_tac >> *)
  (*     >- (first_assum $ irule_at Any >> gvs [] *)
  (*         >> Cases_on ‘evaluate_exp (dec_clock (push_local s var v)) env e’ >> gvs [] *)
  (*         >> last_x_assum $ drule >> rpt strip_tac >> gvs [] *)
  (*         >> pop_assum $ qspecl_then [‘(dec_clock (push_local t var v))’, ‘(FILTER (λ(old,new). old ≠ var) m)’] mp_tac *)
  (*         >> impl_tac *)
  (*         >- (simp [push_local_def, dec_clock_def] >> gvs [ALOOKUP_FILTER] >> rw[] *)
  (*             >- (CASE_TAC >> gvs [read_local_def, read_local_aux_def, FLOOKUP_SIMP] *)
  (*                 >- first_x_assum $ qspec_then ‘old’ (simp o single o Once o SYM) *)
  (*                 >- (rw [] *)
  (*                     >- (first_x_assum $ qspec_then ‘old’ (simp o single o Once o SYM) *)
  (*                     >> cheat) *)
  (*                     >- first_x_assum $ qspec_then ‘old’ (simp o single o Once o SYM))) *)
  (*             >- gvs [read_local_def, read_local_aux_def, FLOOKUP_SIMP]) *)
  (*         >> rpt strip_tac >> gvs []) *)
  (*     >- *)
*)
QED


val _ = export_theory ();
