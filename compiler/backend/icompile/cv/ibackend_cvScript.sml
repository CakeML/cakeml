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

val _ = Globals.max_print_depth := 10;

(* helper *)
fun define_abbrev name tm =
  Feedback.trace ("Theory.allow_rebinds", 1)
    (mk_abbrev name) tm;

(* basic setup for testing *)
val prog = hello_prog_def |> rconc;
val basis_prog_def = define_abbrev "basis_prog" (EVAL``TAKE 93 hello_prog`` |> rconc);
val hello_prog_1_def = define_abbrev "hello_prog_1" (EVAL``DROP 93 hello_prog`` |> rconc);

(* config *)
val c = x64_backend_config_def |> concl |> lhs;
val x64_inc_conf = backendTheory.config_to_inc_config_def
                     |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val inc_source_conf_init_vidx = EVAL “^(x64_inc_conf).inc_source_conf with
                                      <| init_vidx := 100000;
                                         do_elim := F;
                                      |>” |> rconc;
val inc_stack_conf_do_rawcall_f = EVAL “^(x64_inc_conf).inc_stack_conf with do_rawcall := F” |> rconc;
val x64_inc_conf = (EVAL “^(x64_inc_conf) with
        <| inc_source_conf := ^(inc_source_conf_init_vidx);
           inc_stack_conf := ^(inc_stack_conf_do_rawcall_f) |>” |> rconc);

(* embedding *)
val res = (cv_trans_deep_embedding EVAL) basis_prog_def;
val res = (cv_trans_deep_embedding EVAL) hello_prog_1_def;

(* init phase *)
val init_ls = time cv_eval_raw “FST (init_icompile_source_to_livesets_x64 ^x64_inc_conf)” |> rconc;
(*  # runtime: 3.8s,    gctime: 0.15335s,     systime: 0.04283s. *)

val init_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc init_ls;
val init_oracs_def = define_abbrev "init_oracs" init_oracs;
val res = (cv_trans_deep_embedding EVAL) init_oracs_def;

val init_comp = time cv_eval “init_icompile_cake_x64 ^x64_inc_conf init_oracs”;
(* # runtime: 19.9s,    gctime: 1.2s,     systime: 0.35453s. *)
val init_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc init_comp)));


(* TRY embedding below *)
(* icompile phase *)


val basis_prog_ls = time cv_eval_raw “(9n,FST (case (icompile_source_to_livesets_x64 ^init_ic basis_prog) of NONE => ARB | SOME v => v))” |> UNDISCH |> rconc;
(* > # runtime: 14.9s,    gctime: 0.20970s,     systime: 1.1s. *)
val basis_prog_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc basis_prog_ls;
val basis_prog_oracs_def = define_abbrev "basis_prog_oracs" basis_prog_oracs;
val res = (cv_trans_deep_embedding EVAL) basis_prog_oracs_def;

val basis_prog_comp = time cv_eval “icompile_cake_x64 ^init_ic basis_prog basis_prog_oracs”;
(* > # runtime: 1m55s,    gctime: 9.8s,     systime: 4.7s. *)
val basis_prog_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc basis_prog_comp)));

val hello_prog_ls = time cv_eval_raw “(9n,FST (case (icompile_source_to_livesets_x64 ^basis_prog_ic hello_prog_1) of NONE => ARB | SOME v => v))” |> UNDISCH |> rconc;
(* > # runtime: 3m32s,    gctime: 32.5s,     systime: 50.7s. *)
val hello_prog_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc hello_prog_ls;
val hello_prog_oracs_def = define_abbrev "hello_prog_oracs" hello_prog_oracs;
val res = (cv_trans_deep_embedding EVAL) hello_prog_oracs_def;

val hello_prog_comp = time cv_eval “icompile_cake_x64 ^basis_prog_ic hello_prog_1 hello_prog_oracs”;
(* > # runtime: 3m53s,    gctime: 26.3s,     systime: 1m18s.*)
val hello_prog_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc hello_prog_comp)));

Theorem icompile_fold_icompile:
  ∀pss oracss ic ic' ic'' ps' p'.
  fold_icompile_cake ic asm_conf pss oracss = SOME (ic', ps') ∧
  icompile_cake ic' asm_conf p orac = SOME (ic'', p') ⇒
  fold_icompile_cake ic asm_conf (pss ++ [p]) (oracss ++ [orac]) = SOME (ic'', ps' ++ p')
Proof
  Induct_on ‘pss’
  >- (Cases_on ‘oracss’ >> rpt (rw[fold_icompile_cake_def]))
  >- (Cases_on ‘oracss’ >>
      rw[fold_icompile_cake_def] >>
      gvs[AllCaseEqs()] >>
      last_x_assum drule)
QED

val basis_prog_comp' = basis_prog_comp |> REWRITE_RULE [GSYM icompile_cake_x64_th];
val hello_prog_comp' = hello_prog_comp |> REWRITE_RULE [GSYM icompile_cake_x64_th];

val basis_prog_fold = MATCH_MP (icompile_fold_icompile |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                               (cj 1 fold_icompile_cake_def |> ISPECL [“^init_ic”, “x64_config”])
                        |> (fn th => MATCH_MP th basis_prog_comp') |> REWRITE_RULE [APPEND];

val hello_prog_fold = MATCH_MP (icompile_fold_icompile |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                          (basis_prog_fold) |> (fn th => MATCH_MP th hello_prog_comp');


(* end phase *)
val end_ls = time cv_eval_raw “(9n,FST (end_icompile_source_to_livesets_x64 ^hello_prog_ic ^(x64_inc_conf)))” |> rconc;
(* > # runtime: 3m25s,    gctime: 30.2s,     systime: 1m08s. *)
val end_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc end_ls;
val end_oracs_def = define_abbrev "end_oracs" end_oracs;
val res = (cv_trans_deep_embedding EVAL) end_oracs_def;


val end_comp = time cv_eval “end_icompile_cake_x64 ^hello_prog_ic ^(x64_inc_conf) end_oracs”;
(*  # runtime: 4m30s,    gctime: 33.9s,     systime: 1m32s. *)



(* setting up the proof *)

val th_fold = MATCH_MP
              (icompile_eq_cake |> REWRITE_RULE [GSYM AND_IMP_INTRO])
              (init_comp |> REWRITE_RULE[GSYM init_icompile_cake_x64_th])
                |> (fn th =>
                      MATCH_MP th (hello_prog_fold))
                |> (fn th =>
                      MATCH_MP th (end_comp |> REWRITE_RULE[GSYM end_icompile_cake_x64_th]))
                |> UNDISCH;

val h = hd (hyp th_fold);
val conf_ok = EVAL h |> SIMP_RULE (bool_ss) [];
val th_final_fold = PROVE_HYP conf_ok th_fold;

val th_rw = th_final_fold
              |> PURE_REWRITE_RULE [LET_THM]
              |> CONV_RULE BETA_CONV
              |> CONV_RULE BETA_CONV
              |> CONV_RULE BETA_CONV;

val [inc_conf, bm, p] = pairSyntax.strip_pair (th_rw |> rconc |> optionSyntax.dest_some);
val lab_prog_def = define_abbrev "lab_prog" p;
val bm_def = define_abbrev "bm" bm;

val res = (cv_trans_deep_embedding EVAL) lab_prog_def;
val res = (cv_trans_deep_embedding EVAL) bm_def;

val lab = time cv_eval ``from_lab_x64 ^inc_conf LN lab_prog bm`` ;
val first_byte = optionSyntax.dest_some (lab |> rconc)
              |> pairSyntax.dest_pair
              |> #1
              |> listSyntax.dest_list
              |> #1 |> hd |> numSyntax.int_of_term |> chr; (* does not work *)

val f = TextIO.openOut "hello";
val _ = TextIO.output1 (f, bytes);

val _ = export_theory();
