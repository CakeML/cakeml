(*
  Correctness proof for word_cse
*)
open preamble alistTheory;
open wordLangTheory wordSemTheory wordPropsTheory word_simpTheory word_cseTheory;

val _ = new_theory "word_cseProof";

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_cse"];

Definition data_inv_def:
  data_inv (data:knowledge) (s:('a,'c,'ffi) wordSem$state) ⇔
    (∀r v. lookup r data.inst_map = SOME v ⇒
           get_var r s = get_var v s ∧
           v IN domain data.all_names ∧ r IN domain data.all_names) ∧
    (∀r v. lookup r data.och_map = SOME v ⇒
           get_var r s = get_var v s ∧
           v IN domain data.all_names ∧ r IN domain data.all_names) ∧
    (∀n c v. lookup data.inst_instrs (instToNumList (Const n c)) = SOME v ⇒
             lookup v s.locals = SOME (Word c) ∧
             v IN domain data.all_names) ∧
    (∀(a:'a arith) v. lookup data.inst_instrs (instToNumList (Arith a)) = SOME v ⇒
                      get_var v s = get_var (firstRegOfArith a) s ∧
                      v IN domain data.all_names ∧ firstRegOfArith a IN domain data.all_names) ∧
    map_ok data.inst_instrs
    (*
    (∀r (c:'a word) x v. lookup data.inst_instrs (instToNumList (Const r c)) = SOME x ⇒
           x IN domain data.all_names ∧ get_var x s = SOME (Word c)) ∧
    (∀r v (a:'a arith). lookup data.inst_instrs (instToNumList (Arith a)) = SOME v ∧ firstRegOfArith a = r ⇒
             get_var r s = get_var v s ∧
             r IN domain data.all_names ∧ v IN domain data.all_names)
     *)
End
(* domain_lookup lookup_insert*)

Theorem canonicalRegs_correct[simp]:
  ∀data r s. data_inv data s ⇒ get_var (canonicalRegs data r) s = get_var r s
Proof
  rpt strip_tac \\
  gvs [data_inv_def, canonicalRegs_def] \\
  fs [lookup_any_def] \\
  Cases_on ‘lookup r data.inst_map’ \\ fs [] \\
  Cases_on ‘lookup r data.och_map’ \\ fs []
QED

Theorem canonicalArith_correct[simp]:
  ∀data s a. data_inv data s ⇒ inst (Arith (canonicalArith data a)) s = inst (Arith a) s
Proof
  cheat
QED

Theorem firstRegOfArith_canonicalArith[simp]:
  ∀data a. firstRegOfArith (canonicalArith data a) = firstRegOfArith a
Proof
  rpt gen_tac \\ Cases_on ‘a’ \\ gvs [firstRegOfArith_def, canonicalArith_def]
QED


(* Some usefull proofs to automize *)

Theorem lookup_empty[simp]:
  ∀l. lookup (empty listCmp) l = NONE
Proof
  gen_tac
  \\ gvs [mlmapTheory.lookup_def, balanced_mapTheory.lookup_def,
          mlmapTheory.empty_def, balanced_mapTheory.empty_def]
QED

Theorem data_inv_insert_all_names[simp]:
  ∀data s r. data_inv data s ⇒ data_inv (data with all_names:=insert r () data.all_names) s
Proof
  rpt gen_tac
  \\ gvs [data_inv_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rw []
QED

Theorem TotOrd_listCmp[simp]:
  TotOrd listCmp
Proof
  cheat
QED

Theorem map_ok_empty[simp]:
  map_ok (empty listCmp)
Proof
  gvs [mlmapTheory.empty_thm]
QED

Theorem map_ok_insert[simp]:
  ∀m l v. map_ok m ⇒ map_ok (insert m l v)
Proof
  gvs [mlmapTheory.insert_thm]
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
  gvs[word_cse_def, data_inv_def, empty_data_def, sptreeTheory.lookup_def]
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
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on ‘i’
  >- (* Skip *)
   ( gvs [evaluate_def, data_inv_def, word_cse_def, word_cseInst_def,
          inst_def, flat_exp_conventions_def]
     \\ strip_tac
     \\ rw [] \\ gvs []
     \\ first_x_assum (drule_at Any) \\ gvs [] )

  >- (* Const *)
   ( gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def]
     \\ Cases_on ‘is_seen n data’ \\ gvs [evaluate_def]
     >- gvs [data_inv_def, empty_data_def, lookup_def]
     \\ gvs [is_seen_def] \\ Cases_on ‘lookup n data.all_names’ \\ gvs []
     \\ Cases_on ‘lookup data.inst_instrs (instToNumList (Const n c))’ \\ gvs[evaluate_def]
     >- ( Cases_on ‘inst (Const n c) s’ \\ gvs [data_inv_def, inst_def, assign_def]
          \\ Cases_on ‘word_exp s (Const c)’
          \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, word_exp_def]
          \\ strip_tac
          >- (rpt gen_tac \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs []
              \\ strip_tac \\ first_x_assum drule_all \\ rw [])
          \\ strip_tac
          >- (rpt gen_tac \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs []
              \\ strip_tac \\ first_x_assum drule_all \\ rw [])
          \\ strip_tac
          >- ( rpt gen_tac \\ gvs [mlmapTheory.lookup_insert]
               \\ Cases_on ‘c = c'’ \\ gvs [instToNumList_def, wordToNum_def]
               \\ strip_tac \\ first_x_assum drule_all
               \\ strip_tac
               \\ Cases_on ‘v = n’ \\ gvs [])
          \\ rpt gen_tac \\ gvs [instToNumList_def, arithToNumList_def, mlmapTheory.lookup_insert]
          \\ strip_tac
          \\ first_assum drule_all
          \\ strip_tac
          \\ Cases_on ‘v=n’ \\ gvs []
          \\ Cases_on ‘firstRegOfArith a = n’ \\ gvs []
        )
     \\ Cases_on ‘inst (Const n c) s’ \\ gvs [inst_def, assign_def, word_exp_def]
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ gvs [get_vars_def, get_var_def, set_vars_def, alist_insert_def, set_var_def])
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ rpt gen_tac
         \\ gvs [sptreeTheory.lookup_insert]
         \\ Cases_on ‘r = n’ \\ strip_tac \\ gvs []
         >- (Cases_on ‘n=v’ \\ gvs [set_var_def, get_var_def, lookup_insert])
         \\ gvs [set_var_def, get_var_def, lookup_insert]
         \\ first_x_assum drule_all \\ strip_tac \\ gvs []
         \\ Cases_on ‘v = n’ \\ gvs [domain_lookup])
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ rpt gen_tac \\ strip_tac
         \\ first_x_assum drule_all \\ strip_tac \\ gvs []
         \\ gvs [set_var_def, get_var_def, lookup_insert]
         \\ Cases_on ‘r = n’ \\ Cases_on ‘v = n’ \\ gvs [domain_lookup])
     \\ rpt gen_tac \\ strip_tac
     >- (first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
         \\ strip_tac \\ gvs [set_var_def, lookup_insert, domain_lookup]
         \\ Cases_on ‘v=n’ \\ gvs [] )
     \\ first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
     \\ strip_tac \\ gvs [set_var_def, get_var_def, lookup_insert, domain_lookup]
     \\ Cases_on ‘v = n’ \\ gvs []
     \\ Cases_on ‘firstRegOfArith a = n’ \\ gvs []
   )

  >- (* Arith *)
   ( gvs [word_cse_def, word_cseInst_def]
     \\ pairarg_tac \\ gvs []
     \\ Cases_on ‘is_seen (firstRegOfArith a) data’ \\ gvs []
     >- gvs [data_inv_def, empty_data_def, lookup_def]
     \\ Cases_on ‘lookup data.inst_instrs (instToNumList (Arith (canonicalArith data a)))’ \\ gvs [evaluate_def]
     >- ( strip_tac \\ cases_on ‘inst (Arith a) s’ \\ gvs []
          \\ gvs [data_inv_def]
          \\ strip_tac
          >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac
              \\ Cases_on ‘a’ \\ gvs [inst_def, assign_def]
              >- (Cases_on ‘word_exp s (Op b [Var n0; case r' of Reg r3 => Var r3 | Imm w => Const w])’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘word_exp s (Shift s'' (Var n0) n1)’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘get_vars [n1; n0] s’ \\ gvs [get_var_def, set_var_def]
                  \\ Cases_on ‘x’ \\ gvs []
                  \\ Cases_on ‘t’ \\ gvs []
                  \\ Cases_on ‘h'’ \\ gvs []
                  \\ Cases_on ‘h’ \\ gvs []
                  \\ Cases_on ‘t'’ \\ gvs []
                  \\ gvs [lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs []
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘get_vars [n1; n2] s’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘x’ \\ gvs []
                  \\ Cases_on ‘t’ \\ gvs []
                  \\ Cases_on ‘h'’ \\ gvs []
                  \\ Cases_on ‘h’ \\ gvs []
                  \\ Cases_on ‘t'’ \\ gvs []
                         \\ gvs [lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup]
                  \\ Cases_on ‘r=n0’ \\ Cases_on ‘v=n0’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup]
                  \\ cheat)
              >- (cheat)
              >- (cheat)
              >- (cheat)
              >- (cheat)
             )
          \\ cheat)
     \\ cheat
   )
  >- (* Mem *)
   ( Cases_on ‘a’
   \\ gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def, empty_data_def, lookup_def] )
  >- (* FP *)
   ( gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def, empty_data_def, lookup_def] )
QED

Theorem comp_Assign_correct:
  ^(get_goal "Assign")
Proof
  fs[flat_exp_conventions_def]
QED

Theorem comp_Get_correct:
  ^(get_goal "Get")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘is_seen v data’ \\ gvs [evaluate_def]
  >- gvs [empty_data_def, lookup_def, lookup_empty, sptreeTheory.lookup_def]
  \\ strip_tac
  \\ Cases_on ‘FLOOKUP s.store name’ \\ gvs[]
  \\ fs [get_var_def, set_var_def]
  \\ fs [lookup_insert, is_seen_def]
  \\ Cases_on ‘lookup v data.all_names’ \\ gvs [domain_lookup]
  \\ metis_tac [NOT_NONE_SOME]
QED
(* similare cases : Loc *)

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
  fs [get_var_def, dec_clock_def] \\
  first_x_assum drule_all \\ gs []
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
  >- (gvs [evaluate_def] \\
      pairarg_tac \\ gvs []) \\
  pairarg_tac \\ gvs [] \\
  first_x_assum (drule_at Any) \\
  impl_tac
  >- fs [data_inv_def, get_var_def, SF SFY_ss] \\
  fs [evaluate_def] \\
  rw [] \\
  gvs [AllCaseEqs(), data_inv_def, get_var_def, SF SFY_ss]
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
  gvs[word_cse_def, data_inv_def, evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘is_seen r data’ \\ gvs [evaluate_def]
  >- gvs [empty_data_def, lookup_def]
  \\ strip_tac
  \\ Cases_on ‘l1 ∈ domain s.code’ \\ gvs[]
  \\ fs [get_var_def, set_var_def]
  \\ fs [lookup_insert, is_seen_def]
  \\ Cases_on ‘lookup r data.all_names’ \\ gvs [domain_lookup]
  \\ metis_tac [NOT_NONE_SOME]
QED

(* DATA EMPTY *)

Theorem comp_Install_correct:
  ^(get_goal "wordLang$Install")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_CodeBufferWrite_correct:
  ^(get_goal "wordLang$CodeBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_DataBufferWrite_correct:
  ^(get_goal "wordLang$DataBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_FFI_correct:
  ^(get_goal "wordLang$FFI")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_Call_correct:
  ^(get_goal "wordLang$Call")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ cheat
(* never end
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
 *)
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
