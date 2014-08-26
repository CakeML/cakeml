open HolKernel boolLib bossLib pairTheory listTheory lcsymtacs miscLib
open ml_translatorTheory repl_funProofTheory compilerProofTheory ml_repl_moduleTheory
open evaluate_repl_decsTheory compile_repl_decsTheory

val _ = temp_tight_equality()
val _ = new_theory "bootstrap_lemmas"

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE

val _ = Globals.max_print_depth := 20

(* REPL module is closed (TODO: should be proved elsewhere?) *)

val all_env_dom_init =
  ``all_env_dom ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE)``
  |> (REWRITE_CONV [initSemEnvTheory.prim_sem_env_eq] THENC
      SIMP_CONV std_ss [evalPropsTheory.all_env_dom_def,libTheory.lookup_def] THENC
      SIMP_CONV (srw_ss()) [pred_setTheory.EXTENSION] THENC
      EVAL)

val closed_top_REPL = prove(
  ``closed_top ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE) (Tmod "REPL" NONE ml_repl_module_decls)``,
  simp[free_varsTheory.closed_top_def,all_env_dom_init,FV_decs_ml_repl_module_decls])

(* no_closures implies empty vlabs (TODO: should be moved?) *)

val v_to_i1_conv =
  ``v_to_i1 x (Conv y z) a`` |> SIMP_CONV (srw_ss())[Once modLangProofTheory.v_to_i1_cases]
val v_to_i1_lit =
  ``v_to_i1 x (Litv y) a`` |> SIMP_CONV (srw_ss())[Once modLangProofTheory.v_to_i1_cases]
val v_to_i2_conv =
  ``v_to_i2 x (Conv_i1 y z) a`` |> SIMP_CONV (srw_ss())[Once conLangProofTheory.v_to_i2_cases]
val v_to_i2_lit =
  ``v_to_i2 x (Litv_i1 y) a`` |> SIMP_CONV (srw_ss())[Once conLangProofTheory.v_to_i2_cases]
val v_to_exh_conv =
  ``v_to_exh x (Conv_i2 y z) a`` |> SIMP_CONV (srw_ss())[Once exhLangProofTheory.v_to_exh_cases]
val v_pat_conv =
  ``v_pat (Conv_pat x y) a`` |> SIMP_CONV (srw_ss()) [Once patLangProofTheory.v_pat_cases]
val syneq_conv =
  ``syneq (CConv x y) z`` |> SIMP_CONV (srw_ss()) [Once intLangTheory.syneq_cases]
val Cv_bv_conv =
  ``Cv_bv a (CConv x y) z`` |> SIMP_CONV (srw_ss()) [Once bytecodeProofTheory.Cv_bv_cases]
val Cv_bv_lit =
  ``Cv_bv a (CLitv y) z`` |> SIMP_CONV (srw_ss()) [Once bytecodeProofTheory.Cv_bv_cases]

val conv_rws = [printingTheory.v_bv_def,
  v_to_i1_conv,free_varsTheory.vs_to_i1_MAP,v_to_i1_lit,
  v_to_i2_conv,free_varsTheory.vs_to_i2_MAP,v_to_i2_lit,
  v_to_exh_conv,free_varsTheory.vs_to_exh_MAP,
  printingTheory.exh_Cv_def,
  v_pat_conv,syneq_conv,Cv_bv_conv,Cv_bv_lit]

val no_closures_vlabs = store_thm("no_closures_vlabs",
  ``∀b c d e f g.
    no_closures b ⇒
    v_to_i1 grd0 b c ∧
    v_to_i2 grd1 c d ∧
    v_to_exh grd2 d e ∧
    v_pat (v_to_pat e) f ∧
    syneq (v_to_Cv f) g
    ⇒
    vlabs g = {} ∧ all_vlabs g``,
  ho_match_mp_tac no_closures_ind >>
  simp[no_closures_def] >>
  simp[Q.SPECL[`X`,`Litv Y`](CONJUNCT1 modLangProofTheory.v_to_i1_cases)] >>
  simp[Q.SPECL[`X`,`Litv_i1 Y`](CONJUNCT1 conLangProofTheory.v_to_i2_cases)] >>
  simp (PULL_EXISTS::conv_rws) >>
  ntac 3 (rpt gen_tac >> strip_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS,EL_MAP,EVERY_MEM] >>
  fs[intLangExtraTheory.vlabs_list_MAP,Once pred_setTheory.EXTENSION,PULL_EXISTS,MEM_EL] >>
  METIS_TAC[])

(* bytecode state produce by repl_decs *)

val prim_invariant' = prove(
  ``invariant' (THE prim_sem_env) (FST(THE prim_env)) (THE prim_bs)``,
  METIS_TAC[initCompEnvTheory.prim_env_inv,optionTheory.THE_DEF,optionTheory.option_CASES,pairTheory.FST])

val prim_env_rs = prove(
  prim_invariant' |> RW[initCompEnvTheory.invariant'_def]
  |> concl |> strip_exists |> snd |> strip_conj |> el 5
  |> (fn tm => list_mk_exists(free_vars tm,tm)),
  METIS_TAC[prim_invariant',initCompEnvTheory.invariant'_def])

val tm = evaluate_call_repl_step
  |> SPEC_ALL |> concl |> rand |> strip_exists |> snd
  |> strip_conj |> last
val repl_all_env = tm |> funpow 3 rator |> rand
val repl_store = tm |> funpow 2 rator |> funpow 2 rand

val bootstrap_bc_state_exists = prove(
  ``∃bs grd.
      bc_eval (install_code ((SND(SND(compile_repl_decs)))++SND(THE prim_env)) initial_bc_state) = SOME bs ∧
      bc_fetch bs = SOME (Stop T) ∧
      EVERY IS_SOME bs.globals ∧
      env_rs ^repl_all_env ^repl_store grd (FST compile_repl_decs) bs``,
  mp_tac(MATCH_MP bigClockTheory.top_add_clock (CONJUNCT1 evaluate_repl_decs)) >>
  simp[] >>
  `∃c r. Tmod_state "REPL" ml_repl_module_decls = (c,r)` by METIS_TAC[pair_CASES] >> simp[] >>
  assume_tac(``(THE prim_sem_env).sem_store`` |> SIMP_CONV (srw_ss()) [initSemEnvTheory.prim_sem_env_eq]) >> simp[] >>
  disch_then(qx_choose_then`ck`(mp_tac o MATCH_MP compile_top_thm)) >>
  simp[] >>
  STRIP_ASSUME_TAC prim_env_rs >>
  pop_assum(mp_tac o MATCH_MP (RW[GSYM AND_IMP_INTRO]env_rs_change_clock)) >>
  simp[] >> disch_then(qspecl_then[`ck`,`SOME ck`]mp_tac) >> simp[] >>
  strip_tac >>
  CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["bs","rs","types"]))) >>
  `∃rss rsf bc. compile_repl_decs = (rss,rsf,bc)` by METIS_TAC[pair_CASES] >>
  disch_then(qspecl_then[`install_code bc (THE prim_bs with clock := SOME ck)`
                        ,`(FST (THE prim_env)).comp_rs`,`NONE`]mp_tac) >>
  simp[] >>
  fs[compile_repl_decs_def,closed_top_REPL] >>
  disch_then(qspecl_then[`genv,gtagenv,rd`]mp_tac) >>
  CONV_TAC(LAND_CONV(QUANT_CONV(LAND_CONV(SIMP_CONV(srw_ss())[initCompEnvTheory.install_code_def]))))>>
  simp[] >>
  discharge_hyps >- (
    match_mp_tac env_rs_with_bs_irr >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  strip_tac >>
  qexists_tac`bs' with clock := NONE` >>
  simp[GSYM PULL_EXISTS,bytecodeClockTheory.bc_fetch_with_clock] >>
  conj_tac >- (
    match_mp_tac(MP_CANON bytecodeEvalTheory.RTC_bc_next_bc_eval) >>
    reverse conj_tac >- (
      simp[bytecodeEvalTheory.bc_eval1_thm
          ,bytecodeEvalTheory.bc_eval1_def
          ,bytecodeClockTheory.bc_fetch_with_clock] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl)>>simp[]>>
    match_mp_tac bytecodeExtraTheory.RTC_bc_next_append_code >>
    assume_tac initCompEnvTheory.prim_bs_eq >>
    fs[initCompEnvTheory.prim_bs_def] >>
    imp_res_tac bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next >>
    first_assum(match_exists_tac o concl) >>
    simp[bytecodeTheory.bc_state_component_equality]>>
    REWRITE_TAC[initCompEnvTheory.install_code_def] >>
    EVAL_TAC >> simp[GSYM REVERSE_REV]) >>
  conj_tac >- (
    fs[initCompEnvTheory.install_code_def]>>
    first_x_assum match_mp_tac >>
    simp[initCompEnvTheory.prim_bs_eq] ) >>
  `(THE prim_sem_env).sem_envM = []` by fs[initSemEnvTheory.prim_sem_env_eq] >>
  fs[libTheory.emp_def] >>
  METIS_TAC[env_rs_change_clock,SND,FST])

val bootstrap_bc_state_def = new_specification("bootstrap_bc_state_def",["bootstrap_bc_state","bootstrap_grd"],bootstrap_bc_state_exists)

val repl_bc_state_def = Define`
  repl_bc_state = install_code compile_call_repl_step bootstrap_bc_state`

val repl_bc_state_clock = prove(
  ``bootstrap_bc_state.clock = NONE ∧ repl_bc_state.clock = NONE``,
  rw[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
  strip_assume_tac bootstrap_bc_state_def >>
  imp_res_tac bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_clock_less >>
  fs[optionTheory.OPTREL_def,initCompEnvTheory.install_code_def] >>
  fs[initCompEnvTheory.initial_bc_state_def,initCompEnvTheory.empty_bc_state_def])

(* Compiler's invariant, holds after compiling REPL *)

val COMPILER_RUN_INV_def = Define `
  COMPILER_RUN_INV bs grd inp out ⇔
     env_rs ^repl_all_env (update_io inp out ^repl_store) grd
       (FST compile_repl_decs) bs ∧
    (∃rf pc hdl. bs = repl_bc_state with <| pc := pc; refs := rf; handler := hdl |>) `

val COMPILER_RUN_INV_empty_stack = store_thm("COMPILER_RUN_INV_empty_stack",
  ``COMPILER_RUN_INV bs grd inp out ⇒ (bs.stack = [])``,
  rw[COMPILER_RUN_INV_def]>> PairCases_on`grd` >>
  Cases_on`Tmod_state "REPL" ml_repl_module_decls`>>
  fs[update_io_def,compilerProofTheory.env_rs_def])

val COMPILER_RUN_INV_init = store_thm("COMPILER_RUN_INV_init",
  ``COMPILER_RUN_INV repl_bc_state bootstrap_grd
       (dest_Refv (EL iloc (SND (Tmod_state "REPL" ml_repl_module_decls))))
       (dest_Refv (EL (iloc+1) (SND (Tmod_state "REPL" ml_repl_module_decls))))``,
  rw[COMPILER_RUN_INV_def,repl_bc_state_def] >- (
    Cases_on`Tmod_state "REPL" ml_repl_module_decls` >>
    simp[update_io_def] >>
    strip_assume_tac repl_env_def >> rfs[] >>
    Cases_on`EL iloc r`>>fs[]>>Cases_on`EL (iloc+1) r`>>fs[]>>
    ntac 2 (pop_assum (mp_tac o SYM)) >>
    simp[miscTheory.LUPDATE_SAME] >> rw[] >>
    strip_assume_tac bootstrap_bc_state_def >>
    MATCH_MP_TAC env_rs_with_bs_irr >>
    qexists_tac`bootstrap_bc_state with code := bootstrap_bc_state.code ++ REVERSE compile_call_repl_step` >>
    simp[initCompEnvTheory.install_code_def] >>
    rfs[]  >>
    MATCH_MP_TAC env_rs_append_code >>
    rfs[] >> first_assum(match_exists_tac o concl) >> simp[] >>
    simp[bytecodeTheory.bc_state_component_equality] >>
    simp[compilerTheory.compiler_state_component_equality] >>
    `∃x y z. bootstrap_grd = (x,y,z)` by metis_tac[pair_CASES] >>
    fs[env_rs_def] >>
    rator_x_assum`good_labels`mp_tac >>
    simp[bytecodeExtraTheory.good_labels_def,bytecodeExtraTheory.between_labels_def] >>
    simp[rich_listTheory.FILTER_APPEND,rich_listTheory.FILTER_REVERSE,
         rich_listTheory.EVERY_REVERSE,EVERY_MAP,miscTheory.between_def,
         EVERY_FILTER,compile_call_repl_step_labels] >>
    assume_tac compile_call_repl_step_labels >>
    fs[FILTER_EQ_NIL,EVERY_MEM] ) >>
  simp[bytecodeTheory.bc_state_component_equality])

(* Running the code preserves the invariant *)

val code_start_def = Define `
  code_start bs = next_addr bs.inst_length bootstrap_bc_state.code`;

val COMPILER_RUN_INV_repl_step = store_thm("COMPILER_RUN_INV_repl_step",
  ``COMPILER_RUN_INV bs1 grd1 inp1 out1 /\
    INPUT_TYPE x inp1 ==>
    ?bs2 out2 grd2.
      (bc_eval (bs1 with pc := code_start bs1) = SOME bs2) /\
      bc_fetch bs2 = SOME (Stop T) /\
      COMPILER_RUN_INV bs2 grd2 inp1 out2 /\
      OUTPUT_TYPE (basis_repl_step x) out2``,
  rw[Once COMPILER_RUN_INV_def,code_start_def] >>
  first_assum(mp_tac o MATCH_MP evaluate_call_repl_step) >>
  disch_then(qspec_then`out1`strip_assume_tac) >>
  pop_assum (mp_tac o MATCH_MP bigClockTheory.top_add_clock) >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>
  fs[update_io_def] >>
  disch_then(qx_choose_then`ck`STRIP_ASSUME_TAC) >>
  pop_assum(mp_tac o MATCH_MP compile_special_thm) >> simp[] >>
  disch_then(qspecl_then[`FST compile_repl_decs`]mp_tac) >>
  simp[GSYM compile_call_repl_step_def] >>
  simp[free_varsTheory.closed_top_def,evalPropsTheory.all_env_dom_def] >>
  disch_then(qspecl_then[`grd1`,`bootstrap_bc_state.code`
    ,`repl_bc_state with <| clock := SOME ck; refs := rf; handler := hdl|>`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      qmatch_assum_abbrev_tac`env_rs a b c d e` >>
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`e with clock := SOME ck` >>
      simp[Abbr`e`] >>
      match_mp_tac env_rs_change_clock >>
      first_assum(match_exists_tac o concl) >>
      simp[bytecodeTheory.bc_state_component_equality,Abbr`b`] ) >>
    simp[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
    simp[repl_env_def,compile_call_repl_step_labels] >>
    simp[compilerTerminationTheory.exp_to_i1_def,
         modLangTheory.dec_to_i1_def,
         modLangTheory.decs_to_i1_def,
         conLangTheory.decs_to_i2_def,
         compilerTerminationTheory.pat_to_i2_def,
         compilerTerminationTheory.exp_to_i2_def,
         exhLangTheory.exhaustive_match_def,
         exhLangTheory.add_default_def,
         compilerTerminationTheory.row_to_pat_def,
         compilerTerminationTheory.pat_to_exh_def,
         compilerTerminationTheory.sLet_pat_thm,
         decLangTheory.init_globals_def,
         patLangTheory.pure_pat_def,
         decLangTheory.decs_to_i3_def,
         compilerTerminationTheory.exp_to_exh_def,
         astTheory.pat_bindings_def,
         compilerTerminationTheory.is_unconditional_def,
         UNCURRY] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >>
    EVAL_TAC >>
    rw[finite_mapTheory.FLOOKUP_DEF] >>
    EVAL_TAC) >>
  strip_tac >>
  imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >> fs[] >>
  imp_res_tac bytecodeEvalTheory.RTC_bc_next_bc_eval >>
  pop_assum kall_tac >> pop_assum mp_tac >>
  discharge_hyps >-
    simp[bytecodeEvalTheory.bc_eval1_thm,
         bytecodeEvalTheory.bc_eval1_def,
         bytecodeClockTheory.bc_fetch_with_clock] >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`bs:bc_state = X Y` >>
  qmatch_assum_abbrev_tac`bc_eval bs2 = SOME Y` >>
  `bs = bs2` by (
    unabbrev_all_tac >>
    simp[bytecodeTheory.bc_state_component_equality,repl_bc_state_def] >>
    simp[initCompEnvTheory.install_code_def,repl_bc_state_clock] ) >>
  simp[Abbr`Y`,Abbr`bs2`,bytecodeClockTheory.bc_fetch_with_clock] >>
  qexists_tac`out'` >>
  simp[COMPILER_RUN_INV_def] >>
  qexists_tac`grd'` >>
  conj_asm1_tac >- (
    simp[update_io_def] >>
    MATCH_MP_TAC env_rs_change_clock >>
    simp[EXISTS_PROD] >> qexists_tac`0` >>
    first_assum(match_exists_tac o concl) >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[bytecodeTheory.bc_state_component_equality,repl_bc_state_clock] >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_preserves >> fs[] >>
  PairCases_on`grd1`>>PairCases_on`grd'`>>
  fs[env_rs_def,update_io_def] >> rw[] >> fs[] >>
  MATCH_MP_TAC EQ_SYM >>
  MATCH_MP_TAC bytecodeExtraTheory.same_length_gvrel_same >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_gvrel >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def] >>
  conj_tac >- (
    metis_tac
    [conLangProofTheory.to_i2_invariant_def,
     modLangProofTheory.to_i1_invariant_def,
     LIST_REL_LENGTH] ) >>
  simp[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
  simp[bootstrap_bc_state_def])

(* Data representation (TODO: move for easier re-use by x86-64?) *)

val map0 = ``FST(SND(FST compile_repl_decs).contags_env)``
val short_contags_env_def = Define`
  short_contags_env = SND ^map0`
val short_contags_env_eq =
  ``short_contags_env``
  |> (REWR_CONV short_contags_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)

val repl_contags_env_def = Define`
  repl_contags_env = THE (FLOOKUP (FST ^map0) "REPL")`
val repl_contags_env_eq =
  ``repl_contags_env``
  |> (REWR_CONV repl_contags_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)

fun mktm s = ``FST(lookup_tag_flat ^(stringSyntax.fromMLstring s) repl_contags_env)``
val inr_tag_def     = Define`inr_tag     = ^(mktm "Inr")`
val inl_tag_def     = Define`inl_tag     = ^(mktm "Inl")`
val errors_tag_def  = Define`errors_tag  = ^(mktm "Errors")`
val others_tag_def  = Define`others_tag  = ^(mktm "Others")`
val longs_tag_def   = Define`longs_tag   = ^(mktm "Longs")`
val numbers_tag_def = Define`numbers_tag = ^(mktm "Numbers")`
val strings_tag_def = Define`strings_tag = ^(mktm "Strings")`

val BlockNil_def  = Define `BlockNil = Block (block_tag+conLang$nil_tag) []`;
val BlockCons_def = Define `BlockCons (x,y) = Block (block_tag+conLang$cons_tag) [x;y]`;
val BlockPair_def = Define `BlockPair (x,y) = Block (block_tag+conLang$tuple_tag) [x;y]`;

val BlockList_def = Define `
  (BlockList [] = BlockNil) /\
  (BlockList (x::xs) = BlockCons(x,BlockList xs))`;

val BlockBool_def = Define `BlockBool b = Block (bool_to_tag b) []`;
val BlockSome_def = Define `BlockSome x = Block (block_tag+conLang$some_tag) [x]`;

val BlockInl_def = Define `BlockInl x = Block (block_tag+inl_tag) [x]`;
val BlockInr_def = Define `BlockInr x = Block (block_tag+inr_tag) [x]`;

val BlockOtherS_def  = Define `BlockOtherS x  = Block (block_tag+others_tag) [x]`;
val BlockLongS_def   = Define `BlockLongS x   = Block (block_tag+longs_tag) [x]`;
val BlockNumberS_def = Define `BlockNumberS x = Block (block_tag+numbers_tag) [x]`;
val BlockStringS_def = Define `BlockStringS x = Block (block_tag+strings_tag) [x]`;
val BlockErrorS_def  = Define `BlockErrorS    = Block (block_tag+errors_tag) []`;

val Chr_def = Define `Chr c = Number (& (ORD c))`;

val BlockSym_def = Define `
  (BlockSym (StringS s) = BlockStringS (BlockList (MAP Chr s))) /\
  (BlockSym (OtherS s) = BlockOtherS (BlockList (MAP Chr s))) /\
  (BlockSym (LongS s) = BlockLongS (BlockList (MAP Chr s))) /\
  (BlockSym (ErrorS) = BlockErrorS) /\
  (BlockSym (NumberS n) = BlockNumberS (Number n))`;

val BlockNum3_def = Define `
  BlockNum3 (x,y,z) =
    BlockPair (Number (&x), BlockPair (Number (&y),Number (&z)))`;

val has_primitive_types_def = Define`
  has_primitive_types gtagenv ⇔
    FLOOKUP gtagenv ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0:num) ∧
    FLOOKUP gtagenv ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2) ∧
    FLOOKUP gtagenv ("SOME",TypeId(Short"option")) = SOME (conLang$some_tag,1)`

val LIST_TYPE_CHAR_BlockList = prove(
  ``(FLOOKUP cm ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP cm ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀s l x y z b.
      LIST_TYPE CHAR s l ∧ v_bv (x,cm,y,z) l b
    ⇒ (b = BlockList (MAP Chr s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
    simp conv_rws >>
    simp[BlockList_def,BlockNil_def]) >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[BlockList_def,BlockCons_def] >>
  simp[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp conv_rws >>
  simp[Chr_def] >> rw[] >>
  fs[printingTheory.v_bv_def,printingTheory.exh_Cv_def] >>
  metis_tac[])

val LIST_TYPE_code_BlockList = prove(
  ``(FLOOKUP cm ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP cm ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀s l x y z b.
      LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM NUM)) s l ∧ v_bv (x,cm,y,z) l b
    ⇒ (b = BlockList (MAP BlockNum3 s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
    simp conv_rws >>
    simp[BlockList_def,BlockNil_def]) >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[BlockList_def,BlockCons_def] >>
  simp[FORALL_PROD,ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp conv_rws >>
  simp[BlockNum3_def,BlockPair_def] >>
  fs[printingTheory.v_bv_def,printingTheory.exh_Cv_def] >>
  metis_tac[])

val LIST_TYPE_v_bv = prove(
  ``(FLOOKUP (FST(SND d)) ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀ls v. LIST_TYPE A ls v ∧ (∀x y. MEM x ls ∧ A x y ⇒ v_bv d y (f x)) ⇒
      v_bv d v (BlockList (MAP f ls))``,
   strip_tac >>
   Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
     PairCases_on`d` >>
     simp[printingTheory.v_bv_def] >> fs[] >>
     simp (PULL_EXISTS::conv_rws) >>
     simp[BlockList_def,BlockNil_def] ) >>
   PairCases_on`d`>>fs[PULL_EXISTS]>>
   simp (PULL_EXISTS::conv_rws) >> rw[] >>
   simp[BlockList_def,BlockCons_def] >>
   fs[printingTheory.v_bv_def,PULL_EXISTS,printingTheory.exh_Cv_def] >>
   last_x_assum(qspec_then`v2_2`mp_tac) >> simp[] >> strip_tac >>
   first_x_assum(qspec_then`h`mp_tac) >> simp[] >>
   disch_then(qspec_then`v2_1`mp_tac) >> simp[] >> strip_tac >>
   rpt(first_assum(match_exists_tac o concl)>>simp[])) |> GEN_ALL

val LEXER_FUN_SYMBOL_TYPE_v_bv = prove(
  ``(FLOOKUP (FST(SND d)) ("Errors",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (errors_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("Others",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (others_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Longs",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (longs_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Numbers",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (numbers_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Strings",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (strings_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
    ⇒
    ∀x y. LEXER_FUN_SYMBOL_TYPE x y ⇒ v_bv d y (BlockSym x)``,
  strip_tac >> PairCases_on`d`>>fs[]>>
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
  simp(ml_translatorTheory.INT_def::PULL_EXISTS::conv_rws) >>
  simp[BlockSym_def] >>
  simp[BlockStringS_def,
       BlockNumberS_def,
       BlockLongS_def,
       BlockOtherS_def,
       BlockErrorS_def] >>
  rw[] >>
  (LIST_TYPE_v_bv
   |> Q.ISPEC`Chr`
   |> SIMP_RULE std_ss [FORALL_PROD,GSYM AND_IMP_INTRO]
   |> (fn th => first_x_assum(mp_tac o MATCH_MP th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def,Chr_def] >>
  simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS,GSYM CONJ_ASSOC] >>
  disch_then(qspecl_then[`d0`,`d2`,`d3`,`d4`]mp_tac) >>
  (discharge_hyps >- (
     simp[Once modLangProofTheory.v_to_i1_cases] >>
     simp[Once conLangProofTheory.v_to_i2_cases] >>
     simp[Once bytecodeProofTheory.Cv_bv_cases] )) >>
  METIS_TAC[])

(* Relationship between the invariant and the references *)

val repl_globals_env_def = Define`
  repl_globals_env = THE (FLOOKUP (FST(FST compile_repl_decs).globals_env) "REPL")`
val repl_globals_env_eq =
  ``repl_globals_env``
  |> (REWR_CONV repl_globals_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)
val repl_globals_env_flookup = prove(
  ``FLOOKUP (FST (FST compile_repl_decs).globals_env) "REPL" = SOME map ⇒
    map = repl_globals_env``,
  rw[repl_globals_env_def])

val iind_def = Define`
  iind = THE(FLOOKUP repl_globals_env "input")`
val iind_eq =
  ``iind``
  |> (REWR_CONV iind_def
      THENC PURE_ONCE_REWRITE_CONV[repl_globals_env_eq]
      THENC EVAL)

val oind_def = Define`
  oind = THE(FLOOKUP repl_globals_env "output")`
val oind_eq =
  ``oind``
  |> (REWR_CONV oind_def
      THENC PURE_ONCE_REWRITE_CONV[repl_globals_env_eq]
      THENC EVAL)

val inds_flookup = prove(
  ``FLOOKUP repl_globals_env "input" = SOME x ∧
    FLOOKUP repl_globals_env "output" = SOME y ⇒
    x = iind ∧ y = oind``,
  rw[iind_def,oind_def])

val ptrs_exist = prove(
  ``∃iptr optr.
    iind < LENGTH repl_bc_state.globals ∧
    oind < LENGTH repl_bc_state.globals ∧
    EL iind repl_bc_state.globals = SOME (RefPtr iptr) ∧
    EL oind repl_bc_state.globals = SOME (RefPtr optr)``,
  assume_tac COMPILER_RUN_INV_init >>
  fs[COMPILER_RUN_INV_def] >>
  pop_assum kall_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>fs[update_io_def] >>
  `∃x y z. bootstrap_grd = (x,y,z)` by METIS_TAC[pair_CASES] >>
  fs[env_rs_def]>>
  rator_x_assum`to_i1_invariant`mp_tac >>
  simp[modLangProofTheory.to_i1_invariant_def] >>
  simp[Once modLangProofTheory.v_to_i1_cases] >>
  rw[] >> simp[] >>
  rator_x_assum`global_env_inv_flat`mp_tac >>
  simp[repl_env_def,Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >>
  first_assum(qspec_then`"input"`mp_tac) >>
  first_x_assum(qspec_then`"output"`mp_tac) >>
  simp[] >> rw[] >> simp[] >>
  `map = repl_globals_env`  by (
    simp[repl_globals_env_def] ) >>
  rw[] >>
  imp_res_tac inds_flookup >> rw[] >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  fs[LIST_REL_EL_EQN,bytecodeProofTheory.Cenv_bs_def] >>
  rator_x_assum`s_refs`mp_tac >>
  simp[bytecodeProofTheory.s_refs_def,LIST_REL_EL_EQN] >>
  simp[optionTheory.OPTREL_def] >> strip_tac >>
  fs[Once modLangProofTheory.v_to_i1_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[optionTheory.OPTREL_def] >>
  qmatch_assum_rename_tac`EL iind grd0 = SOME (Loc_i1 iloc)`[] >>
  qmatch_assum_rename_tac`EL oind grd0 = SOME (Loc_i1 (iloc+1))`[] >>
  first_assum(qspec_then`iind`mp_tac) >>
  first_x_assum(qspec_then`oind`mp_tac) >>
  qpat_assum`∀n. n < LENGTH genv2 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  qpat_assum`∀n. n < LENGTH grd0 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  fs[Once conLangProofTheory.v_to_i2_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[Q.SPEC`CLoc X`(CONJUNCT1 (SPEC_ALL bytecodeProofTheory.Cv_bv_cases))])

val ptrs_def = new_specification("ptrs_def",["iptr","optr"],ptrs_exist)

val COMPILER_RUN_INV_references = store_thm("COMPILER_RUN_INV_references",
  ``∀bs grd input output.
    COMPILER_RUN_INV bs grd input output ⇒
    bs.globals = repl_bc_state.globals ∧
    iloc+1 < LENGTH (SND(SND grd)).sm ∧
    EL iloc (SND(SND grd)).sm = iptr ∧
    EL (iloc+1) (SND(SND grd)).sm = optr ∧
    ∃ibc obc.
      FLOOKUP bs.refs iptr = SOME (ValueArray [ibc]) ∧
      FLOOKUP bs.refs optr = SOME (ValueArray [obc]) ∧
      let gtagenv = FST(SND grd) in
      let d = (FST grd,gtagenv,(FST compile_repl_decs).exh,mk_pp (SND (SND grd)) bs) in
      v_bv d input ibc ∧ v_bv d output obc ∧
      has_primitive_types gtagenv ∧
      (∀n a t.
        (lookup n (Tmod_tys "REPL" ml_repl_module_decls) = SOME (a,t)) ⇒
        let tag = FST(lookup_tag_flat n repl_contags_env) in
          (FLOOKUP gtagenv (n,t) = SOME(tag,a)))``,
  rpt gen_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>fs[update_io_def] >>
  PairCases_on`grd`>> fs[env_rs_def]>>
  rator_x_assum`to_i1_invariant`mp_tac >>
  simp[modLangProofTheory.to_i1_invariant_def] >>
  simp[Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >> simp[] >>
  rator_x_assum`global_env_inv_flat`mp_tac >>
  simp[repl_env_def,Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >>
  first_assum(qspec_then`"input"`mp_tac) >>
  first_x_assum(qspec_then`"output"`mp_tac) >>
  simp[] >> strip_tac >> strip_tac >> simp[] >>
  `map = repl_globals_env`  by (
    simp[repl_globals_env_def] ) >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac inds_flookup >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[CONJ_ASSOC] >>
  qmatch_abbrev_tac`A ∧ B` >>
  qunabbrev_tac`B` >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  fs[LIST_REL_EL_EQN,bytecodeProofTheory.Cenv_bs_def] >>
  rator_x_assum`s_refs`mp_tac >>
  simp[bytecodeProofTheory.s_refs_def,LIST_REL_EL_EQN] >>
  simp[optionTheory.OPTREL_def] >> strip_tac >>
  fs[Once modLangProofTheory.v_to_i1_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[optionTheory.OPTREL_def] >>
  qmatch_assum_rename_tac`EL iind grd0 = SOME (Loc_i1 iloc)`[] >>
  qmatch_assum_rename_tac`EL oind grd0 = SOME (Loc_i1 (iloc+1))`[] >>
  first_assum(qspec_then`iind`mp_tac) >>
  first_x_assum(qspec_then`oind`mp_tac) >>
  qpat_assum`∀n. n < LENGTH genv2 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  qpat_assum`∀n. n < LENGTH grd0 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  fs[Once conLangProofTheory.v_to_i2_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[Q.SPEC`CLoc X`(CONJUNCT1 (SPEC_ALL bytecodeProofTheory.Cv_bv_cases))] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[libTheory.el_check_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_assum(qspec_then`iloc`mp_tac) >>
  first_x_assum(qspec_then`iloc+1`mp_tac) >>
  simp[EL_MAP] >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  ntac 2 strip_tac >>
  fs[bytecodeProofTheory.good_rd_def] >>
  strip_assume_tac ptrs_def >> fs[] >>
  conj_tac >- fs[markerTheory.Abbrev_def] >>
  rator_x_assum`EVERY`mp_tac >>
  simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >>
  simp[printingTheory.v_bv_def,PULL_EXISTS] >>
  fs[modLangProofTheory.s_to_i1_cases,conLangProofTheory.s_to_i2_cases] >>
  fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_to_i1 B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[modLangProofTheory.sv_to_i1_cases] >> ntac 2 strip_tac >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_to_i2 B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[conLangProofTheory.sv_to_i2_cases] >> ntac 2 strip_tac >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_rel B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[evalPropsTheory.sv_rel_cases] >>
  ntac 2 strip_tac >>
  fs[bytecodeProofTheory.sv_refv_rel_cases] >> rfs[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``Cv_bv`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``Cv_bv`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[printingTheory.exh_Cv_def,PULL_EXISTS] >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``syneq`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``syneq`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[GSYM CONJ_ASSOC] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``v_to_i1`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  reverse conj_tac >- (
    simp[has_primitive_types_def] >>
    rator_x_assum`cenv_inv`mp_tac >>
    simp[conLangProofTheory.cenv_inv_def] >>
    simp[conLangProofTheory.envC_tagged_def] >>
    strip_tac >>
    `∃x. FST(SND(FST compile_repl_decs).contags_env) = (x, short_contags_env)` by (
      simp[short_contags_env_def] >>
      METIS_TAC[pair_CASES,SND,PAIR_EQ] ) >>
    first_assum(qspec_then`Short"nil"`mp_tac) >>
    first_assum(qspec_then`Short"::"`mp_tac) >>
    first_x_assum(qspec_then`Short"SOME"`mp_tac) >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[initSemEnvTheory.prim_sem_env_eq,optionTheory.THE_DEF] >>
    REWRITE_TAC[
      semanticPrimitivesTheory.lookup_con_id_def,
      semanticPrimitivesTheory.merge_envC_def] >>
    EVAL_TAC >> simp[] >>
    REWRITE_TAC[short_contags_env_eq] >>
    EVAL_TAC >> rw[]) >>
  rpt gen_tac >> strip_tac >>
  rator_x_assum`cenv_inv`mp_tac >>
  simp[conLangProofTheory.cenv_inv_def] >>
  simp[conLangProofTheory.envC_tagged_def] >>
  strip_tac >>
  first_x_assum(qspec_then`Long"REPL"n`mp_tac) >>
  Q.PAT_ABBREV_TAC`p:envC = merge_envC X init_envC` >>
  `∃x y. p = (x,y)` by METIS_TAC[pair_CASES] >>
  qunabbrev_tac`p` >>
  simp[semanticPrimitivesTheory.lookup_con_id_def] >>
  qmatch_assum_abbrev_tac`merge_envC([("REPL",e)],emp) init_envC = X` >>
  `lookup "REPL" x = SOME e` by (
    qmatch_assum_rename_tac`merge_envC Y p = X`["Y"] >>
    Cases_on`p`>>fs[semanticPrimitivesTheory.merge_envC_def] >>
    fs[libTheory.merge_def,Abbr`X`] >> rw[] ) >>
  Cases_on`FST(SND(FST compile_repl_decs).contags_env)` >>
  simp[conLangTheory.lookup_tag_env_def,astTheory.id_to_n_def] >>
  strip_tac >>
  fs[conLangProofTheory.gtagenv_wf_def] >>
  fs[finite_mapTheory.FLOOKUP_DEF] >>
  simp[repl_contags_env_def,finite_mapTheory.FLOOKUP_DEF] >>
  IF_CASES_TAC >> fs[] >> METIS_TAC[])

(* Changing the references preserves the invariant *)

fun just_exists_suff_tac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = GEN_ALL(PART_MATCH (snd o dest_imp) th (hd bs))
    val (vs,c) = strip_forall (concl th)
    val (b',_) = dest_imp c
  in
    suff_tac(list_mk_exists(ws,list_mk_conj(b'::tl bs))) >|[assume_tac th,ALL_TAC]
  end g

val COMPILER_RUN_INV_INR = store_thm("COMPILER_RUN_INV_INR",
  ``COMPILER_RUN_INV bs grd inp outp /\ OUTPUT_TYPE (INR (msg,s)) outp ==>
    ?s_bc_val.
      iptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs optr =
         SOME (ValueArray [BlockInr (BlockPair (BlockList (MAP Chr msg),s_bc_val))])) /\
      !ts.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),s_bc_val))
        in
          ?grd new_inp.
            INPUT_TYPE (SOME (ts,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (iptr,ValueArray [inp_bc_val]))
              grd new_inp outp``,
  rw[] >>
  imp_res_tac COMPILER_RUN_INV_references >> simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[OUTPUT_TYPE_def] >>
  fs[ml_repl_stepTheory.SUM_TYPE_def] >>
  fs[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[LET_THM] >>
  rator_x_assum`v_bv`mp_tac >>
  simp[printingTheory.v_bv_def] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  rw[] >>
  first_assum(qspecl_then[`"Inr"`,`1`,`TypeId(Long"REPL""sum")`]mp_tac) >>
  discharge_hyps >- simp[sum_tags_exist] >>
  simp[Once UNCURRY] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[BlockInr_def,inr_tag_def] >>
  simp[BlockPair_def] >>
  fs[has_primitive_types_def] >>
  imp_res_tac LIST_TYPE_CHAR_BlockList >>
  pop_assum kall_tac >>
  conj_asm1_tac >- (
    pop_assum mp_tac >>
    simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS] >>
    disch_then match_mp_tac >>
    METIS_TAC[] ) >>
  rpt gen_tac >> strip_tac >>
  fs[GSYM STATE_TYPE_def] >>
  imp_res_tac INPUT_TYPE_exists >>
  first_x_assum(qspec_then`ts`strip_assume_tac) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rator_x_assum`COMPILER_RUN_INV`mp_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  simp[LEFT_EXISTS_AND_THM] >>
  reverse conj_tac >- (
    pop_assum SUBST1_TAC >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[EXISTS_PROD] >>
  PairCases_on`grd` >>
  qexists_tac`grd0` >> qexists_tac`grd1` >>
  rator_x_assum`env_rs`mp_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls` >>
  simp[update_io_def] >>
  simp[env_rs_def] >> strip_tac >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    qpat_assum`EVERY (sv_every closed) (LUPDATE X Y Z)`mp_tac >>
    simp[EVERY_MEM,MEM_LUPDATE,PULL_EXISTS] >>
    strip_tac >> gen_tac >> strip_tac >- METIS_TAC[] >>
    BasicProvers.VAR_EQ_TAC >>
    simp[EL_LUPDATE] >>
    reverse IF_CASES_TAC >- (
      first_x_assum(qspec_then`EL j r`match_mp_tac) >>
      simp[EL_LUPDATE] >> METIS_TAC[] ) >>
    simp[] >>
    conj_tac >- ( imp_res_tac INPUT_TYPE_closed >> fs[] ) >>
    assume_tac (CONJUNCT2 repl_env_def) >> rfs[] >>
    fsrw_tac[boolSimps.DNF_ss][] ) >>
  exists_suff_gen_then (mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[alpha|->``:num``]to_i1_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  disch_then just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[modLangProofTheory.to_i1_invariant_def] >>
  rator_x_assum`s_to_i1`mp_tac >>
  simp[modLangProofTheory.s_to_i1_cases] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data w (BlockList (MAP BlockSym ts))` by (
    fs[INPUT_TYPE_def,ml_repl_stepTheory.OPTION_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def,Abbr`data`] >>
    MATCH_MP_TAC (MP_CANON LIST_TYPE_v_bv) >>
    HINT_EXISTS_TAC >> simp[] >> rw[] >>
    match_mp_tac(MP_CANON (GEN_ALL LEXER_FUN_SYMBOL_TYPE_v_bv)) >>
    simp[] >>
    rpt conj_tac >>
    qmatch_abbrev_tac`FLOOKUP gtagenv (n,a) = SOME b` >>
    first_x_assum(qspec_then`n`mp_tac) >>
    disch_then(qspec_then`a`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    simp[Abbr`n`,sym_tags_exist] >>
    rw[Abbr`b`] >>
    rw[errors_tag_def,others_tag_def,longs_tag_def,numbers_tag_def,strings_tag_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  CONV_TAC SWAP_EXISTS_CONV >>
  Q.PAT_ABBREV_TAC`inp2 = Conv X [Conv Y [w; Z]]` >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data inp2 inp_bc_val` by (
    simp(Abbr`inp2`::Abbr`data`::PULL_EXISTS::conv_rws) >>
    simp[Abbr`inp_bc_val`,BlockSome_def] >>
    HINT_EXISTS_TAC >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[printingTheory.exh_Cv_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  qmatch_assum_rename_tac`v_to_i1 grd0 inp2 v12`[] >>
  qexists_tac`LUPDATE (Refv v12) iloc s1` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[Abbr`inp2`] >>
    assume_tac(CONJUNCT2 repl_env_def) >> rfs[] >>
    rw[] >>
    simp[modLangProofTheory.sv_to_i1_cases]) >>
  exists_suff_gen_then(mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[beta|->``:num``]to_i2_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >> (CONV_TAC (RESORT_EXISTS_CONV List.rev)) >>
  qexists_tac`genv2` >>
  pop_assum just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  rator_x_assum`s_to_i2`mp_tac >>
  simp[conLangProofTheory.s_to_i2_cases] >>
  strip_tac >>
  qmatch_assum_rename_tac`v_to_i2 grd1 v12 v22`[] >>
  qexists_tac`LUPDATE (Refv v22) iloc s2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    rw[] >> rw[conLangProofTheory.sv_to_i2_cases]) >>
  simp[miscTheory.LIST_REL_O,PULL_EXISTS,evalPropsTheory.sv_rel_O] >>
  qmatch_assum_rename_tac`v_to_exh Z v22 v23`["Z"] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  fs[miscTheory.LIST_REL_O,evalPropsTheory.sv_rel_O] >>
  qexists_tac`LUPDATE (Refv v23) iloc l3` >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qmatch_assum_rename_tac`exh_Cv v23 v24`[] >>
  qexists_tac`LUPDATE (Refv v24) iloc Cs` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  conj_tac >- (
    rator_x_assum`closed_vlabs`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,
         intLangExtraTheory.all_vlabs_csg_def] >>
    simp[EVERY_MEM,intLangExtraTheory.vlabs_csg_def] >>
    strip_tac >>
    `vlabs v24 = {} ∧ all_vlabs v24` by (
      MATCH_MP_TAC (MP_CANON (GEN_ALL no_closures_vlabs)) >>
      fs[printingTheory.exh_Cv_def] >>
      rw[Once CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      METIS_TAC[INPUT_TYPE_no_closures]) >>
    conj_tac >- (
      fs[evalPropsTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
      rw[] >> imp_res_tac MEM_LUPDATE_E >> fs[] >> METIS_TAC[] ) >>
    fs[intLangExtraTheory.vlabs_list_MAP,PULL_EXISTS] >>
    fs[evalPropsTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
    rw[] >> imp_res_tac MEM_LUPDATE_E >> fs[] >> METIS_TAC[pred_setTheory.NOT_IN_EMPTY] ) >>
  qexists_tac`grd2` >>
  MATCH_MP_TAC bytecodeProofTheory.Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  `iloc < LENGTH grd2.sm ∧ EL iloc grd2.sm = iptr` by simp[] >>
  `MEM iptr grd2.sm` by METIS_TAC[MEM_EL] >>
  reverse conj_tac >- rw[] >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def,bytecodeProofTheory.good_rd_def] >>
  conj_tac >- (
    fs[finite_mapTheory.FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[UNCURRY] >> strip_tac >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> fs[] ) >>
  conj_tac >- fs[EVERY_MEM] >>
  fs[LIST_REL_EL_EQN,EL_MAP,EL_LUPDATE] >>
  simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
  rw[] >> fs[] >- METIS_TAC[EL_ALL_DISTINCT_EL_EQ] >>
  METIS_TAC[EL_MAP])

val COMPILER_RUN_INV_INL = store_thm("COMPILER_RUN_INV_INL",
  ``COMPILER_RUN_INV bs grd inp outp /\ OUTPUT_TYPE (INL (code,s)) outp ==>
    ?s_bc_val.
      iptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs optr =
         SOME (ValueArray [BlockInl (BlockPair (BlockList (MAP BlockNum3 code),s_bc_val))])) /\
      !ts b.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),
                                      BlockPair (BlockBool b,s_bc_val)))
        in
          ?grd new_inp.
            INPUT_TYPE (SOME (ts,b,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (iptr,ValueArray[inp_bc_val]))
              grd new_inp outp``,
  rw[] >>
  imp_res_tac COMPILER_RUN_INV_references >> simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[OUTPUT_TYPE_def] >>
  fs[ml_repl_stepTheory.SUM_TYPE_def] >>
  fs[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[LET_THM] >>
  rator_x_assum`v_bv`mp_tac >>
  simp[printingTheory.v_bv_def] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  rw[] >>
  first_assum(qspecl_then[`"Inl"`,`1`,`TypeId(Long"REPL""sum")`]mp_tac) >>
  discharge_hyps >- simp[sum_tags_exist] >>
  simp[Once UNCURRY] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[BlockInl_def,inl_tag_def] >>
  simp[BlockPair_def] >>
  fs[has_primitive_types_def] >>
  imp_res_tac LIST_TYPE_code_BlockList >>
  pop_assum kall_tac >>
  conj_asm1_tac >- (
    pop_assum mp_tac >>
    simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS] >>
    disch_then match_mp_tac >>
    METIS_TAC[] ) >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`A s v1_2` >>
  `STATE_TYPE (b,s) (Conv NONE [Litv (Bool b); v1_2])` by (
    simp[STATE_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def] >>
    simp[ml_translatorTheory.BOOL_def] ) >>
  imp_res_tac INPUT_TYPE_exists >>
  first_x_assum(qspec_then`ts`strip_assume_tac) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rator_x_assum`COMPILER_RUN_INV`mp_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  simp[LEFT_EXISTS_AND_THM] >>
  reverse conj_tac >- (
    pop_assum SUBST1_TAC >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[EXISTS_PROD] >>
  PairCases_on`grd` >>
  qexists_tac`grd0` >> qexists_tac`grd1` >>
  rator_x_assum`env_rs`mp_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls` >>
  simp[update_io_def] >>
  simp[env_rs_def] >> strip_tac >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    qpat_assum`EVERY (sv_every closed) (LUPDATE X Y Z)`mp_tac >>
    simp[EVERY_MEM,MEM_LUPDATE,PULL_EXISTS] >>
    strip_tac >> gen_tac >> strip_tac >- METIS_TAC[] >>
    BasicProvers.VAR_EQ_TAC >>
    simp[EL_LUPDATE] >>
    reverse IF_CASES_TAC >- (
      first_x_assum(qspec_then`EL j r`match_mp_tac) >>
      simp[EL_LUPDATE] >> METIS_TAC[] ) >>
    simp[] >>
    conj_tac >- ( imp_res_tac INPUT_TYPE_closed >> fs[] ) >>
    assume_tac (CONJUNCT2 repl_env_def) >> rfs[] >>
    fsrw_tac[boolSimps.DNF_ss][] ) >>
  exists_suff_gen_then (mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[alpha|->``:num``]to_i1_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  disch_then just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[modLangProofTheory.to_i1_invariant_def] >>
  rator_x_assum`s_to_i1`mp_tac >>
  simp[modLangProofTheory.s_to_i1_cases] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data w (BlockList (MAP BlockSym ts))` by (
    fs[INPUT_TYPE_def,ml_repl_stepTheory.OPTION_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def,Abbr`data`] >>
    MATCH_MP_TAC (MP_CANON LIST_TYPE_v_bv) >>
    HINT_EXISTS_TAC >> simp[] >> rw[] >>
    match_mp_tac(MP_CANON (GEN_ALL LEXER_FUN_SYMBOL_TYPE_v_bv)) >>
    simp[] >>
    rpt conj_tac >>
    qmatch_abbrev_tac`FLOOKUP gtagenv (n,a) = SOME z` >>
    first_x_assum(qspec_then`n`mp_tac) >>
    disch_then(qspec_then`a`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    simp[Abbr`n`,sym_tags_exist] >>
    rw[Abbr`z`] >>
    rw[errors_tag_def,others_tag_def,longs_tag_def,numbers_tag_def,strings_tag_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  CONV_TAC SWAP_EXISTS_CONV >>
  Q.PAT_ABBREV_TAC`inp2 = Conv X [Conv Y [w; Z]]` >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data inp2 inp_bc_val` by (
    simp(Abbr`inp2`::Abbr`data`::conv_rws) >>
    simp[Abbr`inp_bc_val`,BlockSome_def] >>
    simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    fs[printingTheory.exh_Cv_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    simp[BlockBool_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  qmatch_assum_rename_tac`v_to_i1 grd0 inp2 v12`[] >>
  qexists_tac`LUPDATE (Refv v12) iloc s1` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[Abbr`inp2`] >>
    assume_tac(CONJUNCT2 repl_env_def) >> rfs[] >>
    rw[] >>
    simp[modLangProofTheory.sv_to_i1_cases]) >>
  exists_suff_gen_then(mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[beta|->``:num``]to_i2_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >> (CONV_TAC (RESORT_EXISTS_CONV List.rev)) >>
  qexists_tac`genv2` >>
  pop_assum just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  rator_x_assum`s_to_i2`mp_tac >>
  simp[conLangProofTheory.s_to_i2_cases] >>
  strip_tac >>
  qmatch_assum_rename_tac`v_to_i2 grd1 v12 v22`[] >>
  qexists_tac`LUPDATE (Refv v22) iloc s2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    rw[] >> rw[conLangProofTheory.sv_to_i2_cases]) >>
  simp[miscTheory.LIST_REL_O,PULL_EXISTS,evalPropsTheory.sv_rel_O] >>
  qmatch_assum_rename_tac`v_to_exh Z v22 v23`["Z"] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  fs[miscTheory.LIST_REL_O,evalPropsTheory.sv_rel_O] >>
  qexists_tac`LUPDATE (Refv v23) iloc l3` >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qmatch_assum_rename_tac`exh_Cv v23 v24`[] >>
  qexists_tac`LUPDATE (Refv v24) iloc Cs` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  conj_tac >- (
    rator_x_assum`closed_vlabs`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,
         intLangExtraTheory.all_vlabs_csg_def] >>
    simp[EVERY_MEM,intLangExtraTheory.vlabs_csg_def] >>
    strip_tac >>
    `vlabs v24 = {} ∧ all_vlabs v24` by (
      MATCH_MP_TAC (MP_CANON (GEN_ALL no_closures_vlabs)) >>
      fs[printingTheory.exh_Cv_def] >>
      rw[Once CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      METIS_TAC[INPUT_TYPE_no_closures]) >>
    conj_tac >- (
      fs[evalPropsTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
      rw[] >> imp_res_tac MEM_LUPDATE_E >> fs[] >> METIS_TAC[] ) >>
    fs[intLangExtraTheory.vlabs_list_MAP,PULL_EXISTS] >>
    fs[evalPropsTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
    rw[] >> imp_res_tac MEM_LUPDATE_E >> fs[] >> METIS_TAC[pred_setTheory.NOT_IN_EMPTY] ) >>
  qexists_tac`grd2` >>
  MATCH_MP_TAC bytecodeProofTheory.Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  `iloc < LENGTH grd2.sm ∧ EL iloc grd2.sm = iptr` by simp[] >>
  `MEM iptr grd2.sm` by METIS_TAC[MEM_EL] >>
  reverse conj_tac >- rw[] >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def,bytecodeProofTheory.good_rd_def] >>
  conj_tac >- (
    fs[finite_mapTheory.FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[UNCURRY] >> strip_tac >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> fs[] ) >>
  conj_tac >- fs[EVERY_MEM] >>
  fs[LIST_REL_EL_EQN,EL_MAP,EL_LUPDATE] >>
  simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
  rw[] >> fs[] >- METIS_TAC[EL_ALL_DISTINCT_EL_EQ] >>
  METIS_TAC[EL_MAP])

val _ = export_theory()
