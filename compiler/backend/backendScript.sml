open preamble
     source_to_modTheory
     mod_to_conTheory
     con_to_decTheory
     dec_to_exhTheory
     exh_to_patTheory
     pat_to_closTheory
     clos_to_bvlTheory
     bvl_to_bviTheory
     bvi_to_dataTheory
     data_to_wordTheory
     word_to_stackTheory
     stack_to_labTheory
     lab_to_targetTheory
local open primTypesTheory in end
open word_to_wordTheory

val _ = new_theory"backend";

val _ = Datatype`config =
  <| source_conf : source_to_mod$config
   ; mod_conf : mod_to_con$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : bvl_to_bvi$config
   ; data_conf : data_to_word$config
   ; word_to_word_conf : word_to_word$config
   ; word_conf : 'a word_to_stack$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   |>`;

val config_component_equality = theorem"config_component_equality";

val compile_def = Define`
  compile c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    let (c',p) = mod_to_con$compile c.mod_conf p in
    let c = c with mod_conf := c' in
    let (n,e) = con_to_dec$compile c.source_conf.next_global p in
    let c = c with source_conf updated_by (λc. c with next_global := n) in
    let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
    let e = exh_to_pat$compile e in
    let e = pat_to_clos$compile e in
    let (c',p) = clos_to_bvl$compile c.clos_conf e in
    let c = c with clos_conf := c' in
    let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc c.bvl_conf p in
    let c = c with clos_conf updated_by (λc. c with <| start:=s; next_loc:=n |>) in
    let p = bvi_to_data$compile_prog p in
    let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
    let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let c = c with word_conf := c' in
    let c = c with stack_conf updated_by
             (\c1. c1 with max_heap := 2 * max_heap_limit (:'a) c.data_conf) in
    let p = stack_to_lab$compile c.stack_conf c.data_conf c.word_conf (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3)) p in
      lab_to_target$compile c.lab_conf (p:'a prog)`;

val to_mod_def = Define`
  to_mod c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    (c,p)`;

val to_con_def = Define`
  to_con c p =
  let (c,p) = to_mod c p in
  let (c',p) = mod_to_con$compile c.mod_conf p in
  let c = c with mod_conf := c' in
  (c,p)`;

val to_dec_def = Define`
  to_dec c p =
  let (c,p) = to_con c p in
  let (n,e) = con_to_dec$compile c.source_conf.next_global p in
  let c = c with source_conf updated_by (λc. c with next_global := n) in
  (c,e)`;

val to_exh_def = Define`
  to_exh c p =
  let (c,e) = to_dec c p in
  let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
  (c,e)`;

val to_pat_def = Define`
  to_pat c p =
  let (c,e) = to_exh c p in
  let e = exh_to_pat$compile e in
  (c,e)`;

val to_clos_def = Define`
  to_clos c p =
  let (c,e) = to_pat c p in
  let e = pat_to_clos$compile e in
  (c,e)`;

val to_bvl_def = Define`
  to_bvl c p =
  let (c,e) = to_clos c p in
  let (c',p) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  (c,p)`;

val to_bvi_def = Define`
  to_bvi c p =
  let (c,p) = to_bvl c p in
  let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc c.bvl_conf p in
  let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
  (c,p)`;

val to_data_def = Define`
  to_data c p =
  let (c,p) = to_bvi c p in
  let p = bvi_to_data$compile_prog p in
  (c,p)`;

val to_word_def = Define`
  to_word c p =
  let (c,p) = to_data c p in
  let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  (c,p)`;

val to_stack_def = Define`
  to_stack c p =
  let (c,p) = to_word c p in
  let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  (c,p)`;

val to_lab_def = Define`
  to_lab c p =
  let (c,p) = to_stack c p in
  let c = c with stack_conf updated_by
           (\c1. c1 with max_heap := 2 * max_heap_limit (:'a) c.data_conf) in
  let p = stack_to_lab$compile c.stack_conf c.data_conf c.word_conf (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3)) p in
  (c,p:'a prog)`;

val to_target_def = Define`
  to_target c p =
  let (c,p) = to_lab c p in
    lab_to_target$compile c.lab_conf p`;

val compile_eq_to_target = Q.store_thm("compile_eq_to_target",
  `compile = to_target`,
  srw_tac[][FUN_EQ_THM,compile_def,
     to_target_def,
     to_lab_def,
     to_stack_def,
     to_word_def,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_pat_def,
     to_exh_def,
     to_dec_def,
     to_con_def,
     to_mod_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[])));

val prim_config_def = Define`
  prim_config =
    FST (to_dec <| source_conf := empty_config; mod_conf := empty_config |> (prim_types_program))`;

val from_lab_def = Define`
  from_lab c p =
    lab_to_target$compile c.lab_conf p`;

val from_stack_def = Define`
  from_stack c p =
  let c = c with stack_conf updated_by
           (\c1. c1 with max_heap := 2 * max_heap_limit (:'a) c.data_conf) in
  let p = stack_to_lab$compile c.stack_conf c.data_conf c.word_conf (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3)) p in
  from_lab c (p:'a prog)`;

val from_word_def = Define`
  from_word c p =
  let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  from_stack c p`;

val from_data_def = Define`
  from_data c p =
  let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  from_word c p`;

val from_bvi_def = Define`
  from_bvi c p =
  let p = bvi_to_data$compile_prog p in
  from_data c p`;

val from_bvl_def = Define`
  from_bvl c p =
  let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc c.bvl_conf p in
  let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
  from_bvi c p`;

val from_clos_def = Define`
  from_clos c e =
  let (c',p) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  from_bvl c p`;

val from_pat_def = Define`
  from_pat c e =
  let e = pat_to_clos$compile e in
  from_clos c e`;

val from_exh_def = Define`
  from_exh c e =
  let e = exh_to_pat$compile e in
  from_pat c e`;

val from_dec_def = Define`
  from_dec c e =
  let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
  from_exh c e`;

val from_con_def = Define`
  from_con c p =
  let (n,e) = con_to_dec$compile c.source_conf.next_global p in
  let c = c with source_conf updated_by (λc. c with next_global := n) in
  from_dec c e`;

val from_mod_def = Define`
  from_mod c p =
  let (c',p) = mod_to_con$compile c.mod_conf p in
  let c = c with mod_conf := c' in
  from_con c p`;

val from_source_def = Define`
  from_source c p =
  let (c',p) = source_to_mod$compile c.source_conf p in
  let c = c with source_conf := c' in
  from_mod c p`;

val compile_eq_from_source = Q.store_thm("compile_eq_from_source",
  `compile = from_source`,
  srw_tac[][FUN_EQ_THM,compile_def,
     from_source_def,
     from_lab_def,
     from_stack_def,
     from_word_def,
     from_data_def,
     from_bvi_def,
     from_bvl_def,
     from_clos_def,
     from_pat_def,
     from_exh_def,
     from_dec_def,
     from_con_def,
     from_mod_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[])));

(*
val to_livesets_def = Define`
  to_livesets (c:α backend$config) p =
  let (c',p) = to_data c p in
  let (data_conf,word_conf,asm_conf) = (c.data_conf,c.word_to_word_conf,c.lab_conf.asm_conf) in
  let p = stubs(:α) data_conf ++ MAP (compile_part data_conf) p in
  let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith, asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)) in
  let p =
    MAP (λ(name_num,arg_count,prog).
    let prog = word_simp$compile_exp prog in
    let maxv = max_var prog + 1 in
    let inst_prog = inst_select asm_conf maxv prog in
    let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
    let rm_prog = FST(remove_dead ssa_prog LN) in
    let prog = if two_reg_arith then three_to_two_reg rm_prog
                                else rm_prog in
     (name_num,arg_count,prog)) p in
  let clashmovforce = MAP (\(name_num,arg_count,prog). (get_clash_tree prog),get_prefs prog [],get_forced c.lab_conf.asm_conf prog []) p in
  ((reg_count,clashmovforce),c,p)`

val from_livesets_def = Define`
  from_livesets ((k,clashmovforce),c,p) =
  let (word_conf,asm_conf) = (c.word_to_word_conf,c.lab_conf.asm_conf) in
  let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
  let alg = word_conf.reg_alg in
  let prog_with_oracles = ZIP (n_oracles,ZIP(clashmovforec,p)) in
  let p =
    MAP (λ(col_opt,((tree,moves,force),name_num,arg_count,prog)).
      case oracle_colour_ok k col_opt tree prog of
        NONE =>
          (let (clash_graph,_) = clash_tree_to_spg tree [] LN in
             let col = reg_alloc alg clash_graph k moves
             in
               (name_num,arg_count,remove_must_terminate (apply_colour (total_colour col) prog)))
      | SOME col_prog => (name_num,arg_count,remove_must_terminate col_prog)) prog_with_oracles in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  from_word c p`

val compile_oracle = store_thm("compile_oracle",``
  from_livesets (to_livesets c p) = compile c p``,
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_pat_def,
     to_exh_def,
     to_dec_def,
     to_con_def,
     to_mod_def,to_livesets_def] >>
  fs[compile_def]>>
  pairarg_tac>>
  fs[data_to_wordTheory.compile_def,word_to_wordTheory.compile_def]>>
  fs[from_livesets_def,from_word_def,from_stack_def,from_lab_def]>>
  unabbrev_all_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_abbrev_tac`progs = MAP A B`>>
  qpat_abbrev_tac`progs' = MAP A B`>>
  qsuff_tac `progs = progs'`>>rw[]>>
  unabbrev_all_tac>>
  fs[next_n_oracle_def]>>
  rveq>>fs[]>>
  match_mp_tac LIST_EQ>>
  qmatch_goalsub_abbrev_tac`data_to_word$stubs _ _ ++ p2`
  \\ qmatch_goalsub_abbrev_tac`MAP f (data_to_word$stubs _ _)`
  \\ REWRITE_TAC[GSYM MAP_APPEND]
  \\ qpat_abbrev_tac`pp = _ ++ p2`
  \\ simp[MAP_MAP_o]
  \\ qpat_abbrev_tac`len = _ + LENGTH (data_to_word$stubs _ _)`
  \\ `len = LENGTH pp` by simp[Abbr`pp`,Abbr`p2`]
  \\ qunabbrev_tac`len` \\ fs[] >>
  rw[]>>fs[EL_MAP,EL_ZIP,full_compile_single_def,compile_single_def,Abbr`f`]>>
  rpt(pairarg_tac>>fs[])>>
  fs[word_to_wordTheory.compile_single_def,word_allocTheory.word_alloc_def]>>
  rveq>>fs[]>>
  BasicProvers.EVERY_CASE_TAC>>fs[])

val to_livesets_invariant = store_thm("to_livesets_invariant",``
  to_livesets (c with word_to_word_conf:=wc) p =
  let (rcm,c,p) = to_livesets c p in
    (rcm,c with word_to_word_conf:=wc,p)``,
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_pat_def,
     to_exh_def,
     to_dec_def,
     to_con_def,
     to_mod_def,to_livesets_def] >>
  unabbrev_all_tac>>fs[]>>
  rpt(rfs[]>>fs[]))

val to_data_change_config = Q.store_thm("to_data_change_config",
  `to_data c1 prog = (c1',prog') ⇒
   c2.source_conf = c1.source_conf ∧
   c2.mod_conf = c1.mod_conf ∧
   c2.clos_conf = c1.clos_conf ∧
   c2.bvl_conf = c1.bvl_conf
   ⇒
   to_data c2 prog =
     (c2 with <| source_conf := c1'.source_conf;
                 mod_conf := c1'.mod_conf;
                 clos_conf := c1'.clos_conf;
                 bvl_conf := c1'.bvl_conf |>,
      prog')`,
  rw[to_data_def,to_bvi_def,to_bvl_def,to_clos_def,to_pat_def,to_exh_def,to_dec_def,to_con_def,to_mod_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rw[] \\ fs[] \\ rfs[] \\ rveq \\ fs[] \\ rfs[] \\ rveq \\ fs[]
  \\ simp[config_component_equality]);
*)

val _ = export_theory();
