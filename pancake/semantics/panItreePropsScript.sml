(*
    Props for Pancake ITree semantics and correspondence proof.
*)

open preamble
     itreeTauTheory panItreeSemTheory
     panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           panSemTheory in end;

val _ = new_theory "panItreeProps";

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;
Overload "case" = “itree_CASE”;

Theorem itree_bind_ret_inv:
  itree_bind t k = Ret x ⇒ ∃r. (k r) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’ >>
  fs [itree_bind_thm] >>
  metis_tac []
QED

Theorem itree_bind_ret_tree:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (metis_tac [itree_bind_thm]) >>
  fs [itree_bind_def]
QED

Theorem itree_bind_ret_inv_gen:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y ∧ (k y) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (qexists_tac ‘x'’ >> rw [] >>
      fs [itree_bind_thm]) >>
  fs [itree_bind_def]
QED

Theorem itree_bind_left_ident_over_f:
  f $ Ret x >>= k = f (k x)
Proof
  AP_TERM_TAC >>
  rw [itree_bind_thm]
QED

Theorem itree_eq_imp_wbisim:
  t = t' ⇒ t ≈ t'
Proof
  rw [Once itree_wbisim_strong_coind] >>
  rw [itree_wbisim_refl]
QED

Theorem itree_bind_left_ident_wbisim:
  Ret r >>= k ≈ k r
Proof
  rw [itree_eq_imp_wbisim]
QED

Theorem itree_bind_thm_wbisim:
  t ≈ Ret r ⇒ t >>= k ≈ k r
Proof
  disch_tac >>
  drule itree_bind_resp_t_wbisim >>
  rw [itree_bind_left_ident_wbisim]
QED

Theorem itree_wbisim_bind_trans:
  t1 ≈ t2 ∧ t1 >>= k ≈ t3 ⇒
  t2 >>= k ≈ t3
Proof
  strip_tac >>
  irule itree_wbisim_trans >>
  qexists_tac ‘t1 >>= k’ >>
  strip_tac
  >- (irule itree_bind_resp_t_wbisim >>
      rw [itree_wbisim_sym])
  >- (rw [])
QED

Theorem itree_wbisim_neq:
  Ret r ≈ Ret r' ⇔ r = r'
Proof
  EQ_TAC >>
  rw [Once itree_wbisim_cases]
QED

Theorem nat_not_const_eq:
  ¬(∀k:num. k = 0)
Proof
  rw []
QED

(** h_prog **)

Theorem h_prog_not_Tau:
  ∀prog s t. h_prog (prog, s) ≠ Tau t
Proof
  Induct>>
  fs[h_prog_def,
     h_prog_rule_dec_def,
     h_prog_rule_return_def,
     h_prog_rule_raise_def,
     h_prog_rule_ext_call_def,
     h_prog_rule_call_def,
     h_prog_rule_deccall_def,
     h_prog_rule_while_def,
     h_prog_rule_cond_def,
     h_prog_rule_sh_mem_load_def,
     h_prog_rule_sh_mem_store_def,
     h_prog_rule_seq_def,
     h_prog_rule_store_def,
     h_prog_rule_store_byte_def,
     h_prog_rule_assign_def]>>
  rpt gen_tac>>
  rpt (CASE_TAC>>fs[])>>
  simp[Once itree_iter_thm]>>
  rpt (CASE_TAC>>fs[])>>
  simp[h_prog_rule_sh_mem_store_nb_def]>>
  rpt (CASE_TAC>>fs[])>>
  Cases_on ‘m’>>
  simp[h_prog_rule_nb_op_def,
       h_prog_rule_sh_mem_load_nb_def]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem h_prog_Vis_INR:
  ∀prog s t.
  case prog of
    ExtCall _ _ _ _ _ => h_prog (prog, s) = Vis (INR x) k ⇒ k = Ret
  | ShMemLoad _ _ _ => h_prog (prog, s) = Vis (INR x) k ⇒ k = Ret
  | ShMemStore _ _ _ => h_prog (prog, s) = Vis (INR x) k ⇒ k = Ret
  | _ => h_prog (prog, s) ≠ Vis (INR x) k
Proof
  Induct>>
  fs[h_prog_def,
     h_prog_rule_dec_def,
     h_prog_rule_return_def,
     h_prog_rule_raise_def,
     h_prog_rule_ext_call_def,
     h_prog_rule_call_def,
     h_prog_rule_deccall_def,
     h_prog_rule_while_def,
     h_prog_rule_cond_def,
     h_prog_rule_sh_mem_load_def,
     h_prog_rule_sh_mem_store_def,
     h_prog_rule_seq_def,
     h_prog_rule_store_def,
     h_prog_rule_store_byte_def,
     h_prog_rule_assign_def]>>
  rpt gen_tac>>
  rpt (CASE_TAC>>fs[])>>
  simp[Once itree_iter_thm]>>
  rpt (CASE_TAC>>fs[])>>
  simp[h_prog_rule_sh_mem_store_nb_def]>>
  rpt (CASE_TAC>>fs[])>>
  Cases_on ‘m’>>
  simp[h_prog_rule_nb_op_def,
       h_prog_rule_sh_mem_load_nb_def]>>
  rpt (CASE_TAC>>fs[])
QED

(* a better version than the one in panPropsTheory *)
Theorem opt_mmap_eval_upd_clock_eq:
  !es s ck. OPT_MMAP (eval (s with clock := ck)) es =
            OPT_MMAP (eval s) es
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  metis_tac [panPropsTheory.eval_upd_clock_eq]
QED

Theorem wbisim_Ret_unique:
  X ≈ Ret x ∧ X ≈ Ret y ⇒ x = y
Proof
  strip_tac>>
  drule itree_wbisim_sym>>strip_tac>>
  drule itree_wbisim_trans>>
  disch_then $ rev_drule>>
  simp[Once itree_wbisim_cases]
QED

val _ = export_theory();
