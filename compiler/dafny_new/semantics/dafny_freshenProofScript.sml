(*
  Correctness proof for the freshen pass.
*)

open preamble
open dafny_astTheory
open dafny_evaluateTheory
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_freshenProof";


Definition state_rel_def:
  state_rel s t m ⇔
  s.clock = t.clock ∧ s.heap = t.heap ∧ s.cout = t.cout ∧
  ∀local val.
    read_local s local = SOME val ⇒
    ∃local'.
      ALOOKUP m local = SOME local' ∧ read_local t local' = SOME val
End

Definition is_exp_fail_def[simp]:
  is_exp_fail (Rerr _) = T ∧
  is_exp_fail _ = F
End

Theorem correct_exp:
  (∀s env e s' r m cnt cnt' e' t.
     evaluate_exp s env e = (s', r) ∧ freshen_exp m cnt e = SOME (cnt', e') ∧
     state_rel s t m ∧ ¬(is_exp_fail r)
     ⇒ ∃t'. evaluate_exp t env e' = (t', r) ∧ state_rel s' t' m) ∧
  (∀s env es s' r m cnt cnt' es' t.
     evaluate_exps s env es = (s', r) ∧
     freshen_exps m cnt es = SOME (cnt', es') ∧
     state_rel s t m ∧ ¬(is_exp_fail r)
     ⇒ ∃t'. evaluate_exps t env es' = (t', r) ∧ state_rel s' t' m)
Proof
QED

Theorem correct_exp:
  (∀s env e s' res t m cnt cnt' e'.
     evaluate_exp s env e = (s', res) ∧ state_rel s t m ∧
     freshen_exp m cnt e = (cnt', e') ∧ m_inv m cnt ⇒
     ∃t'. evaluate_exp t env e' = (t', res) ∧ state_rel s' t' m) ∧
  (∀s env es s' res t m cnt cnt' es'.
     evaluate_exps s env es = (s', res) ∧ state_rel s t m ∧
     freshen_exps m cnt es = (cnt', es') ∧ m_inv m cnt ⇒
     ∃t'. evaluate_exps t env es' = (t', res) ∧ state_rel s' t' m)
Proof




Definition lookup_def:
  lookup m old =
  case ALOOKUP m old of
  | NONE => old
  | SOME cnt => «v» ^ num_to_str cnt
End

Definition add_fresh_def:
  add_fresh m (cnt: num) old = (cnt + 1, (old, cnt)::m)
End

Definition freshen_exp_def:
  freshen_exp m cnt (Lit l) = (cnt + 1, Lit l) ∧
  freshen_exp m cnt (Var old) = (cnt + 1, Var (lookup m old)) ∧
  freshen_exp m cnt (If tst thn els) =
  (let
     (cnt, tst) = freshen_exp m cnt tst;
     (cnt, thn) = freshen_exp m cnt thn;
     (cnt, els) = freshen_exp m cnt els
   in
     (cnt, If tst thn els)) ∧
  freshen_exp m cnt (UnOp uop e) =
  (let
     (cnt, e) = freshen_exp m cnt e
   in
     (cnt, UnOp uop e)) ∧
  freshen_exp m cnt (BinOp bop e₁ e₂) =
  (let
     (cnt, e₁) = freshen_exp m cnt e₁;
     (cnt, e₂) = freshen_exp m cnt e₂
   in
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
  freshen_exps m cnt [] = (cnt + 1, []) ∧
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

Theorem foo:
  (∀m cnt e cnt' e'. freshen_exp m cnt e = (cnt', e') ⇒ cnt < cnt') ∧
  (∀m cnt es cnt' es'. freshen_exps m cnt es = (cnt', es') ⇒ cnt < cnt')
Proof
  ho_match_mp_tac freshen_exp_ind
  >> rpt strip_tac
  >> gvs [freshen_exp_def] >> rpt (pairarg_tac \\ gvs [])
  >> rpt (last_x_assum $ drule_all >> strip_tac) >> gvs [add_fresh_def]
QED

Definition state_rel_def:
  state_rel s t m ⇔
  s.clock = t.clock ∧ s.heap = t.heap ∧ s.cout = t.cout ∧
  ∀old. read_local t (lookup m old) = read_local s old
End

Definition m_inv_def[simp]:
  m_inv (m: (mlstring # num) list) cnt ⇔ ∀c. MEM c (MAP SND m) ⇒ c < cnt
End

Theorem foobar:
  push_local s var v = s' ⇒
  s.clock = s'.clock ∧ s.heap = s'.heap ∧ s.cout = s'.cout
Proof
  rpt strip_tac >> gvs [push_local_def]
QED

Theorem bar:
  (∀s env e s' res t m cnt cnt' e'.
     evaluate_exp s env e = (s', res) ∧ state_rel s t m ∧
     freshen_exp m cnt e = (cnt', e') ∧ m_inv m cnt ⇒
     ∃t'. evaluate_exp t env e' = (t', res) ∧ state_rel s' t' m) ∧
  (∀s env es s' res t m cnt cnt' es'.
     evaluate_exps s env es = (s', res) ∧ state_rel s t m ∧
     freshen_exps m cnt es = (cnt', es') ∧ m_inv m cnt ⇒
     ∃t'. evaluate_exps t env es' = (t', res) ∧ state_rel s' t' m)
Proof
  ho_match_mp_tac evaluate_exp_ind
  >> rpt strip_tac
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



val _ = export_theory ();
