(*
  Translate WASM-specialised functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory backend_cvTheory backend_64_cvTheory;
open backend_wasmTheory wasmLangTheory wasm_configTheory to_data_cvTheory;
open cake_to_wasmTheory stack_to_wasmTheory wasm_binary_formatTheory;

val _ = new_theory "backend_wasm_cv";

(*---------------------------------------------------------------------------*
  StackLang to WASM compiler
 *---------------------------------------------------------------------------*)

val _ = cv_auto_trans stack_to_wasmTheory.stack_to_wasm_def

(*---------------------------------------------------------------------------*
  WASM to binary format
 *---------------------------------------------------------------------------*)

(* leb128 *)

val _ = cv_trans_rec leb128Theory.enc_num_def
 (WF_REL_TAC ‘measure $ cv$c2n’
  \\ cv_termination_tac
  \\ rename [‘cv_div n’]
  \\ Cases_on ‘n’
  >- (gvs [DIV_LT_X] \\ Cases_on ‘128 − m’ \\ fs [cvTheory.c2b_def])
  >- fs [cvTheory.c2b_def])

val _ = cv_trans leb128Theory.enc_unsigned_word_def;
val _ = cv_trans leb128Theory.enc_w7s_def;
val _ = cv_trans leb128Theory.enc_signed_word8_def;
val _ = cv_trans leb128Theory.enc_signed_word32_def;
val _ = cv_trans leb128Theory.enc_signed_word64_def;

(* encoding of instr *)

val pre = cv_auto_trans_pre "enc_instr_list_pre enc_instr_pre"
            wasm_binary_formatTheory.enc_instr_def;
Theorem enc_instr_pre[cv_pre]:
  (∀v e. enc_instr_pre e v) ∧
  (∀v e. enc_instr_list_pre e v)
Proof
  ho_match_mp_tac (TypeBase.induction_of “:instr”)
  \\ simp [] \\ rpt strip_tac
  \\ simp [Once pre] \\ rw [] \\ gvs []
QED

(* encoding of module *)

val _ = cv_auto_trans wasm_binary_formatTheory.split_funcs_def
val _ = cv_auto_trans wasm_binary_formatTheory.enc_functype_def;
val _ = cv_trans wasm_binary_formatTheory.enc_limits_def;
val _ = cv_trans wasm_binary_formatTheory.enc_globaltype_def;
val _ = cv_auto_trans wasm_binary_formatTheory.enc_global_def;
val _ = cv_auto_trans wasm_binary_formatTheory.enc_code_def;
val _ = cv_auto_trans wasm_binary_formatTheory.enc_data_def;
val _ = cv_trans wasm_binary_formatTheory.enc_section_def;

Definition enc_listO_enc_functype_def:
  enc_listO_enc_functype [] = SOME [] ∧
  enc_listO_enc_functype (x::xs) =
     case enc_functype x of
     | NONE => NONE
     | SOME encx =>
       case enc_listO_enc_functype xs of
       | NONE => NONE
       | SOME encxs => SOME (encx ++ encxs)
End

Theorem enc_listO_enc_functype_thm:
  ∀xs. enc_listO enc_functype xs = enc_listO_enc_functype xs
Proof
  Induct \\ fs [enc_listO_enc_functype_def,enc_listO_def]
QED

val _ = cv_trans enc_listO_enc_functype_def;

Definition enc_listO_enc_global_def:
  enc_listO_enc_global [] = SOME [] ∧
  enc_listO_enc_global (x::xs) =
     case enc_global x of
     | NONE => NONE
     | SOME encx =>
       case enc_listO_enc_global xs of
       | NONE => NONE
       | SOME encxs => SOME (encx ++ encxs)
End

Theorem enc_listO_enc_global_thm:
  ∀xs. enc_listO enc_global xs = enc_listO_enc_global xs
Proof
  Induct \\ fs [enc_listO_enc_global_def,enc_listO_def]
QED

val _ = cv_trans enc_listO_enc_global_def;

Definition enc_listO_enc_code_def:
  enc_listO_enc_code [] = SOME [] ∧
  enc_listO_enc_code (x::xs) =
     case enc_code x of
     | NONE => NONE
     | SOME encx =>
       case enc_listO_enc_code xs of
       | NONE => NONE
       | SOME encxs => SOME (encx ++ encxs)
End

Theorem enc_listO_enc_code_thm:
  ∀xs. enc_listO enc_code xs = enc_listO_enc_code xs
Proof
  Induct \\ fs [enc_listO_enc_code_def,enc_listO_def]
QED

val _ = cv_trans enc_listO_enc_code_def;

Definition enc_listO_enc_data_def:
  enc_listO_enc_data [] = SOME [] ∧
  enc_listO_enc_data (x::xs) =
     case enc_data x of
     | NONE => NONE
     | SOME encx =>
       case enc_listO_enc_data xs of
       | NONE => NONE
       | SOME encxs => SOME (encx ++ encxs)
End

Theorem enc_listO_enc_data_thm:
  ∀xs. enc_listO enc_data xs = enc_listO_enc_data xs
Proof
  Induct \\ fs [enc_listO_enc_data_def,enc_listO_def]
QED

val _ = cv_trans enc_listO_enc_data_def;

val _ = wasm_binary_formatTheory.enc_module_def
          |> SRULE [wasm_binary_formatTheory.enc_vector_def,
                    wasm_binary_formatTheory.enc_vectorO_def,
                    enc_listO_enc_functype_thm,
                    enc_listO_enc_global_thm,
                    enc_listO_enc_code_thm,
                    enc_listO_enc_data_thm]
          |> cv_auto_trans;

(*---------------------------------------------------------------------------*
  Remaining wasm-specific functions
 *---------------------------------------------------------------------------*)

val pre = cv_auto_trans_pre "" comp_wasm_def;
Theorem comp_wasm_pre[cv_pre,local]:
  ∀v bs kf. comp_wasm_pre v bs kf
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_auto_trans compile_prog_wasm_def;

val pre = cv_auto_trans_pre "" compile_word_to_stack_wasm_def;
Theorem compile_word_to_stack_wasm_pre[cv_pre]:
  ∀k v bitmaps. compile_word_to_stack_wasm_pre k v bitmaps
Proof
  Induct_on`v`
  \\ rw [] \\ simp [Once pre]
QED

val pre = cv_trans_pre "" get_forced_wasm_def;
Theorem get_forced_wasm_pre[cv_pre,local]:
  ∀v acc. get_forced_wasm_pre v acc
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_trans word_alloc_inlogic_wasm_def;

val pre = cv_trans_pre "" inst_select_exp_wasm_def;
Theorem inst_select_exp_wasm_pre[cv_pre]:
  ∀v tar temp. inst_select_exp_wasm_pre tar temp v
Proof
  gen_tac \\ completeInduct_on ‘exp_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.exp_size_def]
QED

val pre = cv_trans_pre "" inst_select_wasm_def;
Theorem inst_select_wasm_pre[cv_pre,local]:
  ∀v temp. inst_select_wasm_pre temp v
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs [wordLangTheory.prog_size_def]
QED

val pre = each_inlogic_wasm_def |> cv_trans_pre "";
Theorem each_inlogic_wasm_pre[cv_pre,local]:
  ∀v. each_inlogic_wasm_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans word_to_word_inlogic_wasm_def;

val _ = cv_trans (compile_0_wasm_def
                    |> SRULE [data_to_wordTheory.stubs_def,
                              backend_64_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans backend_wasmTheory.to_word_0_wasm_def;
val _ = cv_auto_trans backend_wasmTheory.to_livesets_0_wasm_def;
val _ = cv_auto_trans (backend_wasmTheory.to_word_all_wasm_def
                         |> SRULE [data_to_wordTheory.stubs_def,to_map_compile_part,
                                   backend_64_cvTheory.inline]);

val _ = cv_auto_trans backend_wasmTheory.to_stack_all_wasm_def;
val _ = cv_auto_trans backend_wasmTheory.to_lab_all_wasm_def;

val _ = cv_auto_trans (backend_wasmTheory.from_word_0_to_stack_0_wasm_def
  |> SRULE [backend_64_cvTheory.inline,data_to_wordTheory.max_heap_limit_def]);

val _ = cv_trans compile_cake_to_stack_wasm_def;

Definition cake_to_wasm_binary_def:
  cake_to_wasm_binary (c:inc_config) p =
    case compile_cake_to_stack_wasm c p of
    | NONE => NONE
    | SOME (bm,p_out,names) =>
    case stack_to_wasm names bm p_out of
    | INL err => NONE (* TODO: preserve error messages *)
    | INR mod =>
    case enc_module mod of
    | NONE => NONE
    | SOME out => SOME (out : word8 list)
End

Theorem cake_to_wasm_binary_def[allow_rebind] =
  cake_to_wasm_binary_def |> SPEC_ALL |> Q.GENL [‘p’,‘c’];

Theorem cake_to_wasm_binary_IMP:
  cake_to_wasm_binary c p = SOME bytes ⇒
  ∃res.
    cake_to_wasm (inc_config_to_config wasm_config c) p = INR res ∧
    enc_module res = SOME bytes
Proof
  rw [cake_to_wasm_binary_def,AllCaseEqs()]
  \\ drule compile_cake_to_stack_wasm_thm \\ strip_tac
  \\ gvs [cake_to_wasm_def]
QED

(* main translations below *)

val _ = cv_trans backend_wasmTheory.to_livesets_wasm_def;
val _ = cv_trans cake_to_wasm_binary_def;
val _ = cv_auto_trans backend_wasmTheory.compile_cake_explore_wasm_def;

(* lemma used by automation *)

Theorem set_asm_conf_wasm_backend_config:
  set_asm_conf wasm_backend_config wasm_config = wasm_backend_config
Proof
  irule backendTheory.set_asm_conf_id \\ EVAL_TAC
QED

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
