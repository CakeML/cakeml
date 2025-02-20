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

val _ = Globals.max_print_depth := 1;

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

(* basis *)
val basis_prog_ls = time cv_eval_raw
                         “(9n,FST (case (icompile_source_to_livesets_x64 ^init_ic basis_prog) of NONE => ARB | SOME v => v))”
                      |> UNDISCH
                      |> rconc;
(* > # runtime: 14.9s,    gctime: 0.20970s,     systime: 1.1s. *)
val basis_prog_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc basis_prog_ls;
val basis_prog_oracs_def = define_abbrev "basis_prog_oracs" basis_prog_oracs;
val res = (cv_trans_deep_embedding EVAL) basis_prog_oracs_def;
val basis_prog_comp = time cv_eval “icompile_cake_x64 ^init_ic basis_prog basis_prog_oracs”;
(* > # runtime: 1m55s,    gctime: 9.8s,     systime: 4.7s. *)
val basis_prog_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc basis_prog_comp)));


(* hello prog *)
val hello_prog_ls = time cv_eval_raw
                         “(9n,FST (case (icompile_source_to_livesets_x64 ^basis_prog_ic hello_prog_1) of NONE => ARB | SOME v => v))”
                      |> UNDISCH
                      |> rconc;
(* > # runtime: 3m32s,    gctime: 32.5s,     systime: 50.7s. *)
val hello_prog_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc hello_prog_ls;
val hello_prog_oracs_def = define_abbrev "hello_prog_oracs" hello_prog_oracs;
val res = (cv_trans_deep_embedding EVAL) hello_prog_oracs_def;
val hello_prog_comp = time cv_eval “icompile_cake_x64 ^basis_prog_ic hello_prog_1 hello_prog_oracs”;
(* > # runtime: 3m53s,    gctime: 26.3s,     systime: 1m18s.*)
val hello_prog_ic = #1 (pairSyntax.dest_pair (optionSyntax.dest_some (rconc hello_prog_comp)));

(* not using fold_icompile *)
(*
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
*)
val basis_prog_comp' = basis_prog_comp |> REWRITE_RULE [GSYM icompile_cake_x64_th];
val hello_prog_comp' = hello_prog_comp |> REWRITE_RULE [GSYM icompile_cake_x64_th];

val basis_hello_prog_comp = MATCH_MP (icompile_icompile_cake |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                     basis_prog_comp'
                              |> (fn th => MATCH_MP th hello_prog_comp');

(* end phase *)
val end_ls = time cv_eval_raw “(9n,FST (end_icompile_source_to_livesets_x64 ^hello_prog_ic ^(x64_inc_conf)))” |> rconc;
(* > # runtime: 3m25s,    gctime: 30.2s,     systime: 1m08s. *)
val end_oracs = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc end_ls;
val end_oracs_def = define_abbrev "end_oracs" end_oracs;
val res = (cv_trans_deep_embedding EVAL) end_oracs_def;
val end_comp = time cv_eval “end_icompile_cake_x64 ^hello_prog_ic ^(x64_inc_conf) end_oracs”;
(*  # runtime: 4m30s,    gctime: 33.9s,     systime: 1m32s. *)



(* setting up the proof *)

val conf_ok_imp_icompile_eq_th = MATCH_MP (init_icompile_icompile_end_icompile_cake |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                          (init_comp |> REWRITE_RULE[GSYM init_icompile_cake_x64_th])
                                   |> (fn th => MATCH_MP th basis_hello_prog_comp)
                                   |> (fn th => MATCH_MP th (end_comp |> REWRITE_RULE[GSYM end_icompile_cake_x64_th])) |> UNDISCH;

val conf_ok = hd (hyp conf_ok_imp_icompile_eq_th)
                |> EVAL |> SIMP_RULE (bool_ss) [];
val icompile_eq_th = PROVE_HYP conf_ok conf_ok_imp_icompile_eq_th;


val icompile_eq_rw = icompile_eq_th
              |> PURE_REWRITE_RULE [LET_THM]
              |> CONV_RULE BETA_CONV
              |> CONV_RULE BETA_CONV
              |> CONV_RULE BETA_CONV;

val _ = Globals.max_print_depth := 1;
val [inc_conf, bm, p] = pairSyntax.strip_pair (icompile_eq_rw |> rconc |> optionSyntax.dest_some);
val lab_prog_def = define_abbrev "lab_prog" p;
val bm_def = define_abbrev "bm" bm;

val res = (cv_trans_deep_embedding EVAL) lab_prog_def;
val res = (cv_trans_deep_embedding EVAL) bm_def;

val target_def = time cv_eval_raw ``from_lab_x64 ^inc_conf LN lab_prog bm`` ;

val to_option_some = cv_typeTheory.to_option_def |> cj 2;
val to_pair = cv_typeTheory.to_pair_def |> cj 1;
val c2n_Num = cvTheory.c2n_def |> cj 1;

val th = target_def |> CONV_RULE (PATH_CONV "r" (REWR_CONV to_option_some));
val th1 = th |> CONV_RULE (PATH_CONV "rr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrrrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrrrrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrrrrrr" (REWR_CONV to_pair)
                                     THENC PATH_CONV "rrrlr" (REWR_CONV c2n_Num)
                                     THENC PATH_CONV "rrrrrlr" (REWR_CONV c2n_Num)
                                     THENC PATH_CONV "rrrrrrrlr" (REWR_CONV c2n_Num))

fun abbrev_inside name path th = let
    val tm = dest_path path (concl th)
    val def = define_abbrev name tm
            in (def, CONV_RULE (PATH_CONV path (REWR_CONV (SYM def))) th) end;

val (code_def,th) = abbrev_inside "code" "rrlr" th1;
val (data_def,th) = abbrev_inside "data" "rrrrlr" th
val (ffis_def,th) = abbrev_inside "ffis" "rrrrrrlr" th
val (syms_def,th) = abbrev_inside "syms" "rrrrrrrrlr" th
val (conf_def,th) = abbrev_inside "conf" "rrrrrrrrr" th


val e = backend_x64_cvTheory.cv_x64_export_def |> concl |> strip_forall |> snd |> lhs;
val cv_ty = cvSyntax.cv;
fun get_one_subst name abbrev_def = mk_var(name,cvSyntax.cv) |-> (abbrev_def |> concl |> rhs |> rand);
fun cv_explode e = SPEC e basis_cvTheory.cv_mlstring_explode_def |> concl |> lhs;
fun cv_concat e = SPEC e basis_cvTheory.cv_mlstring_concat_def |> concl |> lhs;
fun cv_append e = SPEC e basis_cvTheory.cv_misc_append_def |> concl |> lhs;
val export_tm = e |> cv_append |> cv_concat |> cv_explode |> subst
    [get_one_subst "cv_ffi_names" ffis_def,
     get_one_subst "cv_data" data_def,
     get_one_subst "cv_bytes" code_def,
     get_one_subst "cv_syms" syms_def,
     (* TODO: exp/ret/pk need to be passed as arguments for in-logic
        Pancake compiler evaluation *)
     mk_var("cv_exp",cvSyntax.cv) |-> cvSyntax.mk_cv_num numSyntax.zero_tm,
     mk_var("cv_ret",cvSyntax.cv) |-> cvSyntax.mk_cv_num numSyntax.zero_tm,
     mk_var("cv_pk",cvSyntax.cv)  |-> cvSyntax.mk_cv_num numSyntax.zero_tm];
val _ = null (free_vars export_tm) orelse failwith "failed to eval export"

val l = cv_computeLib.cv_compute (cv_transLib.cv_eqs_for export_tm) export_tm
          |> concl |> rhs;

fun write_cv_char_list_to_file filename cv_char_list_tm = let
  val s = print ("Writing cv to file: " ^ filename ^"\n")
  val f = TextIO.openOut filename
  fun loop tm =
  if can (cvSyntax.dest_cv_pair) tm
  then
  let
    val (n,rest) = cvSyntax.dest_cv_pair tm
    val c = cvSyntax.dest_cv_num n |> numSyntax.int_of_term |> chr
    val _ = TextIO.output1(f,c)
    in
      loop rest
    end
  else
    ()
  val _ = loop cv_char_list_tm
  in TextIO.closeOut f end;


val _ = write_cv_char_list_to_file "hello_prog_ic" l;
val _ = case output_conf_filename of NONE => ()
                                  | SOME fname => write_cv_char_list_to_file fname
                            (conf_def |> concl |> rhs |> rand);

val _ = export_theory();
