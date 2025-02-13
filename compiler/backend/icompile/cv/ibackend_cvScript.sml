(*
  CV translation for ibackend
*)
open preamble ibackendTheory
     backend_asmTheory
     backend_x64Theory
     to_data_cvTheory
     backend_64_cvTheory
     backend_x64_cvTheory
     cv_transLib
     x64_configTheory
     x64_targetTheory;

open backend_asmLib;
open helloProgTheory;

open reg_allocComputeLib;

val _ = new_theory"ibackend_cv";

(* using the default config for x64 *)
val arch_size = “:64”
val arch_spec = INST_TYPE [alpha |-> arch_size];

val asm_spec_mem_list = CONJUNCTS asm_spec_memory;
val (asm_spec, _) = asm_spec_raw asm_spec_mem_list x64_targetTheory.x64_config_def;
val asm_spec' = fn th => asm_spec th |> snd;

val _ = cv_auto_trans locationTheory.unknown_loc_def;

(* translating icompile_source_to_livesets *)
val _ = to_livesets_0_alt_def |>
  SIMP_RULE std_ss [backendTheory.word_internal_def,
  LET_DEF |> INST_TYPE [alpha |-> ``:bool``]] |> asm_spec' |> cv_auto_trans;

val _ = cv_auto_trans
  (icompile_bvl_to_bvi_prog_def
  |> SRULE [GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list]);

val _ = end_icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;

val _ = icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;

val _ = init_icompile_data_to_word_def |> asm_spec' |> arch_spec |> cv_auto_trans ;

val _ = cv_trans empty_word_iconf_def;

val _ = mk_iconfig_def |> cv_auto_trans ;

val _ = init_icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;

(* translating icompile *)

val _ = icompile_word_to_stack_def |> asm_spec';
val _ = end_icompile_word_to_stack_def |> asm_spec';

val (end_icompile_cake_x64_th,end_icompile_cake_x64_def) = end_icompile_cake_def |> asm_spec ;
val _ = end_icompile_cake_x64_def |> cv_auto_trans;

val (icompile_cake_x64_th, icompile_cake_x64_def) = icompile_cake_def |> asm_spec;
val _ = icompile_cake_x64_def |> cv_auto_trans;

val _ = icompile_word_to_stack_def |> asm_spec' |> cv_auto_trans;

Definition ic_w2s_mk_config_def:
  ic_w2s_mk_config k =
    (empty_word_iconf :'a word_iconfig) with
    <| k := k;
      bm := (List [4w:'a word], 1);
      sfs_list := [];
      fs := [0] |>
End

val _ = ic_w2s_mk_config_def |> arch_spec |> cv_auto_trans;

Theorem init_icompile_word_to_stack_thm:
  init_icompile_word_to_stack asm_conf word1_init =
  let k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs) in
  let word_iconf = ic_w2s_mk_config k in
  let (word_iconf, stack_init) = icompile_word_to_stack asm_conf word_iconf word1_init in
  let stack_init =
      (raise_stub_location,raise_stub k) ::
      (store_consts_stub_location,store_consts_stub k) :: stack_init in
    (word_iconf, stack_init)
Proof
  rw[init_icompile_word_to_stack_def,ic_w2s_mk_config_def]
QED

val _ = init_icompile_word_to_stack_thm |> asm_spec' |> cv_auto_trans;

val (init_icompile_cake_x64_th, init_icompile_cake_x64_def) = init_icompile_cake_def  |> SIMP_RULE std_ss [GSYM mk_iconfig_def] |> asm_spec;

val _ = init_icompile_cake_x64_def |> cv_auto_trans;

(* Testing the cv translation *)

(* basic setup *)
val prog = hello_prog_def |> rconc;
val prog1 = EVAL``TAKE 15 hello_prog`` |> rconc;
val prog2 = EVAL``TAKE 15 (DROP 15 hello_prog)`` |> rconc;

val c = x64_backend_config_def |> concl |> lhs;
val x64_inc_conf = backendTheory.config_to_inc_config_def
                     |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val inc_source_conf_init_vidx = EVAL “^(x64_inc_conf).inc_source_conf with
                                      <| init_vidx := 10000;
                                         do_elim := F;
                                      |>” |> rconc;
val inc_stack_conf_do_rawfall_f = EVAL “^(x64_inc_conf).inc_stack_conf with do_rawcall := F” |> rconc;

val x64_inc_conf = EVAL “^(x64_inc_conf) with
                         <| inc_source_conf := ^(inc_source_conf_init_vidx);
                            inc_stack_conf := ^(inc_stack_conf_do_rawfall_f) |>” |> rconc;

(* init phase *)

val init_ls = time cv_eval_raw “FST (SND (init_icompile_source_to_livesets_x64 ^(x64_inc_conf)))” |> rconc;
val init_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc init_ls;

val init_comp = time cv_eval “init_icompile_cake_x64 ^(x64_inc_conf) ^init_oracs”;

val init_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc init_comp)));

(* icompile phase *)

(* prog1 *)
val prog1_ls = time cv_eval_raw “(9n,FST (SND (case (icompile_source_to_livesets_x64 ^init_ic ^prog1) of NONE => ARB | SOME v => v)))” |> UNDISCH |> rconc;
val prog1_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc prog1_ls;

val prog1_comp = time cv_eval “icompile_cake_x64 ^init_ic ^prog1 ^prog1_oracs”;
val prog1_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc prog1_comp)));

val prog2_ls = time cv_eval_raw “(9n,FST (SND (case (icompile_source_to_livesets_x64 ^prog1_ic ^prog2) of NONE => ARB | SOME v => v)))” |> UNDISCH |> rconc;
val prog2_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc prog2_ls;

val prog2_comp = time cv_eval “icompile_cake_x64 ^prog1_ic ^prog2 ^prog2_oracs”;
val prog2_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc prog2_comp)));

(* end phase *)
val end_ls = time cv_eval_raw “(9n,FST (SND (end_icompile_source_to_livesets_x64 ^prog2_ic ^(x64_inc_conf))))” |> rconc;
val end_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc end_ls;

val end_comp = time cv_eval “end_icompile_cake_x64 ^prog2_ic ^(x64_inc_conf) ^end_oracs”;

(* TODO: merge
  prog1_comp
  prog2_comp
  into a fold *)

(* setting up the proof *)

val th = MATCH_MP
  (init_icompile_icompile_end_icompile_cake |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  (init_comp |> REWRITE_RULE[GSYM init_icompile_cake_x64_th])
  |> (fn th =>
        MATCH_MP th (prog1_comp |> REWRITE_RULE[GSYM icompile_cake_x64_th]))
  |> (fn th =>
        MATCH_MP th (end_comp |> REWRITE_RULE[GSYM end_icompile_cake_x64_th]))
  |> UNDISCH;

val h = hd (hyp th);

val conf_ok = EVAL h |> SIMP_RULE (bool_ss) [];

val th_final = PROVE_HYP conf_ok th;


val _ = export_theory();
