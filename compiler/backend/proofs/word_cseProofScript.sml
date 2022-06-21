(*
  Correctness proof for word_cse
*)
open preamble alistTheory;
open wordLangTheory wordSemTheory wordPropsTheory word_simpTheory word_cseTheory;

val _ = new_theory "word_cseProof";

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_cse"];

Definition data_inv_def:
  data_inv (data:knowledge) (s:('a,'c,'ffi) wordSem$state) ⇔
    (∀r v. lookup r data.inst_map = SOME v ⇒ get_var r s = get_var v s) ∧
    (∀r v. lookup r data.och_map = SOME v ⇒ get_var r s = get_var v s)
End

Theorem canonicalRegs_correct[simp]:
  ∀data r s. data_inv data s ⇒ get_var (canonicalRegs data r) s = get_var r s
Proof
  rpt strip_tac \\
  gvs [data_inv_def, canonicalRegs_def] \\
  fs [lookup_any_def] \\
  Cases_on ‘lookup r data.inst_map’ \\ fs [] \\
  Cases_on ‘lookup r data.och_map’ \\ fs []
QED

(* setting up the goal *)

val goal = “
 λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
   ∀res s' data p' data'.
     evaluate (p, s) = (res, s') ∧ flat_exp_conventions p ∧
     data_inv data s ∧
     word_cse data p  = (data', p') ⇒
     evaluate (p', s) = (res, s') ∧
     (res = NONE ⇒ data_inv data' s')”

local
  val gst = goal |> Ho_Rewrite.PURE_ONCE_REWRITE_CONV [Once PFORALL_THM] |> concl |> rhs
  val ind_thm = evaluate_ind |> ISPEC goal |> GEN_BETA_RULE
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end;

(* proof of the cases *)

Theorem comp_Skip_correct:
  ^(get_goal "Skip")
Proof
  gvs[word_cse_def, evaluate_def]
QED

Theorem comp_Alloc_correct:
  ^(get_goal "Alloc")
Proof
  gvs[word_cse_def, data_inv_def, lookup_def, evaluate_def] \\
  gvs [AllCaseEqs()] \\
  cheat
  (* TODO make alloc forget everything for now *)
QED

Theorem comp_Move_correct:
  ^(get_goal "Move")
Proof
  cheat
(*
  rpt strip_tac \\
  rw[word_cse_def]
*)
QED

Theorem comp_Inst_correct:
  ^(get_goal "Inst")
Proof
  cheat
QED

Theorem comp_Assign_correct:
  ^(get_goal "Assign")
Proof
  fs[flat_exp_conventions_def]
QED

Theorem comp_Get_correct:
  ^(get_goal "Get")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def] \\
  gvs[AllCaseEqs(), PULL_EXISTS] \\
  cheat
QED

Theorem comp_Set_correct:
  ^(get_goal "wordLang$Set")
Proof
  cheat
  (*gvs[word_cse_def, data_inv_def]*)
QED

Theorem comp_OpCurrHeap_correct:
  ^(get_goal "OpCurrHeap")
Proof
  cheat
QED

Theorem comp_Store_correct:
  ^(get_goal "Store")
Proof
  fs[flat_exp_conventions_def]
QED

Theorem comp_Tick_correct:
  ^(get_goal "Tick")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def] \\
  rw [] \\
  fs [get_var_def, dec_clock_def]
QED

Theorem comp_MustTerminate_correct:
  ^(get_goal "MustTerminate")
Proof
  rpt gen_tac \\
  strip_tac \\
  rpt gen_tac \\
  gs[word_cse_def] \\
  pairarg_tac \\ gvs [evaluate_def,flat_exp_conventions_def] \\
  gvs [AllCaseEqs()] \\
  strip_tac
  >- gvs [evaluate_def] \\
  pairarg_tac \\ gvs [] \\
  first_x_assum (drule_at Any) \\
  impl_tac
  >- fs [data_inv_def, get_var_def] \\
  fs [evaluate_def] \\
  rw [] \\
  gvs [AllCaseEqs(), data_inv_def, get_var_def]
QED

Theorem comp_Seq_correct:
  ^(get_goal "wordLang$Seq")
Proof
  rpt gen_tac \\
  strip_tac \\
  rpt gen_tac \\
  strip_tac \\
  gvs[word_cse_def, evaluate_def, flat_exp_conventions_def] \\
  rpt (pairarg_tac \\ gvs []) \\
  reverse(gvs [AllCaseEqs(),evaluate_def])
  >- (pairarg_tac \\ gvs [] \\
      first_x_assum drule_all \\ gs []) \\
  pairarg_tac \\ gvs [] \\
  first_x_assum drule_all \\ gs [] \\
  strip_tac \\ gvs [] \\
  first_x_assum drule_all \\
  fs []
QED

Theorem comp_Return_correct:
  ^(get_goal "Return")
Proof
  fs[word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED

Theorem comp_Raise_correct:
  ^(get_goal "wordLang$Raise")
Proof
  fs[word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]

QED

Theorem comp_If_correct:
  ^(get_goal "wordLang$If")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ simp_tac std_ss [evaluate_def, AllCaseEqs(), word_cse_def, LET_THM]
  \\ rpt (pairarg_tac \\ simp [])
  \\ strip_tac
  \\ gvs [evaluate_def]
  \\ ‘get_var_imm (canonicalImmReg data ri) s = get_var_imm ri s’ by
    (Cases_on ‘ri’ \\ fs [get_var_imm_def, canonicalImmReg_def])
  \\ fs [flat_exp_conventions_def]
  \\ first_x_assum drule_all
  \\ rw []
  \\ simp [data_inv_def, empty_data_def, get_var_def, lookup_def]
QED

Theorem comp_LocValue_correct:
  ^(get_goal "wordLang$LocValue")
Proof
  gvs[word_cse_def, data_inv_def]
  \\ cheat
QED

(* DATA EMPTY *)

Theorem comp_Install_correct:
  ^(get_goal "wordLang$Install")
Proof
  gvs[word_cse_def, data_inv_def]
QED

Theorem comp_CodeBufferWrite_correct:
  ^(get_goal "wordLang$CodeBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def]
QED

Theorem comp_DataBufferWrite_correct:
  ^(get_goal "wordLang$DataBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def]
QED

Theorem comp_FFI_correct:
  ^(get_goal "wordLang$FFI")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def]
QED

Theorem comp_Call_correct:
  ^(get_goal "wordLang$Call")
Proof
  fs[word_cse_def]
QED

(* DATA EMPTY *)

Theorem comp_correct:
  ^(compile_correct_tm ())
Proof
  match_mp_tac (the_ind_thm()) >>
  rpt conj_tac >>
  MAP_FIRST MATCH_ACCEPT_TAC
    [comp_Skip_correct,comp_Alloc_correct,comp_Move_correct,comp_Inst_correct,comp_Assign_correct,
     comp_Get_correct,comp_Set_correct,comp_Store_correct,comp_Tick_correct,comp_MustTerminate_correct,
     comp_Seq_correct,comp_Return_correct,comp_Raise_correct,comp_If_correct,comp_LocValue_correct,
     comp_Install_correct,comp_CodeBufferWrite_correct,comp_DataBufferWrite_correct,
     comp_FFI_correct,comp_OpCurrHeap_correct,comp_Call_correct
    ]
QED

val _ = export_theory();
