(*
  Translate WASM-specialised functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory backend_cvTheory backend_64_cvTheory;
open backend_wasmTheory wasmLangTheory wasm_configTheory to_data_cvTheory;

val _ = new_theory "backend_wasm_cv";

(*---------------------------------------------------------------------------*
  StackLang to WASM compiler
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
  WASM to binary format
 *---------------------------------------------------------------------------*)

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

(* main translations below *)

val _ = cv_trans backend_wasmTheory.to_livesets_wasm_def;
(*
val _ = cv_trans backend_wasmTheory.compile_cake_wasm_def;
val _ = cv_auto_trans backend_wasmTheory.compile_cake_explore_wasm_def;
*)

(* lemma used by automation *)

Theorem set_asm_conf_wasm_backend_config:
  set_asm_conf wasm_backend_config wasm_config = wasm_backend_config
Proof
  irule backendTheory.set_asm_conf_id \\ EVAL_TAC
QED

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
