(*
  Composes all of the compiler phases within the compiler backend into
  a single compile function which is connected (in ../compilerScript.sml)
  to the front-end, i.e. parsing and type inference.
*)

open preamble
     source_to_sourceTheory
     source_to_flatTheory
     flat_to_closTheory
     clos_to_bvlTheory
     bvl_to_bviTheory
     bvi_to_dataTheory
     data_to_wordTheory
     word_to_stackTheory
     stack_to_labTheory
     lab_to_targetTheory
local open primTypesTheory in end
open word_to_wordTheory
open jsonLangTheory presLangTheory

val _ = new_theory"backend";

val _ = Datatype`config =
  <| source_conf : source_to_flat$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : bvl_to_bvi$config
   ; data_conf : data_to_word$config
   ; word_to_word_conf : word_to_word$config
   ; word_conf : word_to_stack$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; symbols : (mlstring # num # num) list
   ; tap_conf : tap_config
   |>`;

val config_component_equality = theorem"config_component_equality";

val attach_bitmaps_def = Define `
  attach_bitmaps names c bm (SOME (bytes, c')) =
    SOME (bytes, bm,
          c with <| lab_conf := c'
                  ; symbols := MAP (\(n,p,l). (lookup_any n names «NOTFOUND»,p,l)) c'.sec_pos_len
                  |>) /\
  attach_bitmaps names c bm NONE = NONE`

val compile_tap_def = Define`
  compile_tap c p =
    let p = source_to_source$compile p in
    let _ = empty_ffi (strlit "finished: source_to_source") in
    let (c',p) = source_to_flat$compile c.source_conf p in
    let td = tap_flat c.tap_conf p [] in
    let _ = empty_ffi (strlit "finished: source_to_flat") in
    let c = c with source_conf := c' in
    let p = flat_to_clos$compile_decs p in
    let td = tap_clos c.tap_conf p td in
    let _ = empty_ffi (strlit "finished: flat_to_clos") in
    let (c',p,names) = clos_to_bvl$compile c.clos_conf p in
    let c = c with clos_conf := c' in
    let _ = empty_ffi (strlit "finished: clos_to_bvl") in
    let (s,p,l,n1,n2,names) = bvl_to_bvi$compile c.clos_conf.start c.bvl_conf names p in
    let c = c with clos_conf updated_by (λc. c with start:=s) in
    let c = c with bvl_conf updated_by (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
    let _ = empty_ffi (strlit "finished: bvl_to_bvi") in
    let p = bvi_to_data$compile_prog p in
    let td = tap_data_lang c.tap_conf (p,names) td in
    let _ = empty_ffi (strlit "finished: bvi_to_data") in
    let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
    let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
      word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
      stack_remove$stub_names ())) names in
    let td = tap_word c.tap_conf (p,names) td in
    let _ = empty_ffi (strlit "finished: data_to_word") in
    let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let td = tap_stack c.tap_conf (p,names) td in
    let c = c with word_conf := c' in
    let _ = empty_ffi (strlit "finished: word_to_stack") in
    let p = stack_to_lab$compile
      c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1)
      (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3))
      (c.lab_conf.asm_conf.addr_offset) p in
    let td = tap_lab c.tap_conf (p,names) td in
    let _ = empty_ffi (strlit "finished: stack_to_lab") in
    let res = attach_bitmaps names c bm
      (lab_to_target$compile c.lab_conf (p:'a prog)) in
    let _ = empty_ffi (strlit "finished: lab_to_target") in
      (res, td)`;

val compile_def = Define`
  compile c p = FST (compile_tap c p)`;

val to_flat_def = Define`
  to_flat c p =
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$compile c.source_conf p in
    let c = c with source_conf := c' in
    (c,p)`;

val to_clos_def = Define`
  to_clos c p =
  let (c,p) = to_flat c p in
  let p = flat_to_clos$compile_decs p in
  (c,p)`;

val to_bvl_def = Define`
  to_bvl c p =
  let (c,p) = to_clos c p in
  let (c',p,names) = clos_to_bvl$compile c.clos_conf p in
  let c = c with clos_conf := c' in
  (c,p,names)`;

val to_bvi_def = Define`
  to_bvi c p =
  let (c,p,names) = to_bvl c p in
  let (s,p,l,n1,n2,names) = bvl_to_bvi$compile c.clos_conf.start c.bvl_conf names p in
  let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
    word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
    stack_remove$stub_names ())) names in
  let c = c with clos_conf updated_by (λc. c with start := s) in
  let c = c with bvl_conf updated_by (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
  (c,p,names)`;

val to_data_def = Define`
  to_data c p =
  let (c,p,names) = to_bvi c p in
  let p = bvi_to_data$compile_prog p in
  (c,p,names)`;

val to_word_0_def = Define`
  to_word_0 c p =
  let (c,p,names) = to_data c p in
  let p = data_to_word$compile_0 c.data_conf c.lab_conf.asm_conf p in
  (c,p,names)`;

val to_word_def = Define`
  to_word c p =
  let (c,p,names) = to_data c p in
  let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  (c,p,names)`;

Theorem to_word_thm:
  to_word c p =
  let (c,p,names) = to_word_0 c p in
  let (col,p) = compile c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  (c,p,names)
Proof
  fs [to_word_def,to_word_0_def,compile_0_def,data_to_wordTheory.compile_def]
  \\ pairarg_tac \\ fs []
QED

val to_stack_def = Define`
  to_stack c p =
  let (c,p,names) = to_word c p in
  let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  (bm,c,p,names)`;

val to_lab_def = Define`
  to_lab c p =
  let (bm,c,p,names) = to_stack c p in
  let p = stack_to_lab$compile
    c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1)
    (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3))
    (c.lab_conf.asm_conf.addr_offset) p in
  (bm,c,p:'a prog,names)`;

val to_target_def = Define`
  to_target c p =
  let (bm,c,p,names) = to_lab c p in
    attach_bitmaps names c bm (lab_to_target$compile c.lab_conf p)`;

Theorem compile_eq_to_target:
   compile = to_target
Proof
  srw_tac[][FUN_EQ_THM,compile_def,compile_tap_def,
     to_target_def,
     to_lab_def,
     to_stack_def,
     to_word_def,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]))
QED

Definition prim_src_config_def:
  prim_src_config =
    let (_, next, env, _, _) = compile_decs [] 1n empty_config.next empty_env
        ARB prim_types_program in
    (empty_config with <| next := next; mod_env := env |>)
End

Theorem prim_src_config_eq = EVAL ``prim_src_config``

val prim_config_def = Define`
  prim_config =
    FST (to_flat <| source_conf := empty_config |> (prim_types_program))`;

val prim_config_eq = save_thm("prim_config_eq",
  EVAL ``prim_config`` |> SIMP_RULE std_ss [FUNION_FUPDATE_1,FUNION_FEMPTY_1]);

val from_lab_def = Define`
  from_lab c names p bm =
    attach_bitmaps names c bm (lab_to_target$compile c.lab_conf p)`;

val from_stack_def = Define`
  from_stack c names p bm =
  let p = stack_to_lab$compile
    c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1)
    (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3))
    (c.lab_conf.asm_conf.addr_offset) p in
  from_lab c names (p:'a prog) bm`;

val from_word_def = Define`
  from_word c names p =
  let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  from_stack c names p bm`;

val from_word_0_def = Define`
  from_word_0 c names p =
  let (col,prog) = word_to_word$compile c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  from_word c names prog`;

val from_data_def = Define`
  from_data c names p =
  let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  from_word c names p`;

Theorem from_data_thm:
  from_data c names p =
  let p = data_to_word$compile_0 c.data_conf c.lab_conf.asm_conf p in
  from_word_0 c names p
Proof
  fs [from_data_def,data_to_wordTheory.compile_0_def,data_to_wordTheory.compile_def,
      from_word_0_def]
QED

val from_bvi_def = Define`
  from_bvi c names p =
  let p = bvi_to_data$compile_prog p in
    from_data c names p`;

val from_bvl_def = Define`
  from_bvl c names p =
  let (s,p,l,n1,n2,names) = bvl_to_bvi$compile c.clos_conf.start c.bvl_conf names p in
  let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
    word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
    stack_remove$stub_names ())) names in
  let c = c with clos_conf updated_by (λc. c with start:=s) in
  let c = c with bvl_conf updated_by (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
  from_bvi c names p`;

val from_clos_def = Define`
  from_clos c e =
  let (c',p,names) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  from_bvl c names p`;

val from_flat_def = Define`
  from_flat c p =
  let p = flat_to_clos$compile_decs p in
  from_clos c p`;

val from_source_def = Define`
  from_source c p =
  let p = source_to_source$compile p in
  let (c',p) = source_to_flat$compile c.source_conf p in
  let c = c with source_conf := c' in
  from_flat c p`;

Theorem compile_eq_from_source:
   compile = from_source
Proof
  srw_tac[][FUN_EQ_THM,compile_def,compile_tap_def,
     from_source_def,
     from_lab_def,
     from_stack_def,
     from_word_def,
     from_data_def,
     from_bvi_def,
     from_bvl_def,
     from_clos_def,
     from_flat_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]))
QED

val to_livesets_def = Define`
  to_livesets (c:α backend$config) p =
  let (c',p,names) = to_data c p in
  let (data_conf,word_conf,asm_conf) = (c.data_conf,c.word_to_word_conf,c.lab_conf.asm_conf) in
  let data_conf = (data_conf with <| has_fp_ops := (1 < asm_conf.fp_reg_count);
                                     has_fp_tern := (asm_conf.ISA = ARMv7 /\ 2 < asm_conf.fp_reg_count)|>) in
  let p = stubs(:α) data_conf ++ MAP (compile_part data_conf) p in
  let alg = word_conf.reg_alg in
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
  let data = MAP (\(name_num,arg_count,prog).
    let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
    (get_clash_tree prog,heu_moves,spillcosts,get_forced c.lab_conf.asm_conf prog [])) p
  in
    ((reg_count,data),c',names,p)`

val to_livesets_0_def = Define`
  to_livesets_0 (c:α backend$config,p,names: mlstring num_map) =
  let (word_conf,asm_conf) = (c.word_to_word_conf,c.lab_conf.asm_conf) in
  let alg = word_conf.reg_alg in
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
  let data = MAP (\(name_num,arg_count,prog).
    let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
    (get_clash_tree prog,heu_moves,spillcosts,get_forced c.lab_conf.asm_conf prog [])) p
  in
    ((reg_count,data),c,names,p)`

Theorem to_data_conf_inv:
  to_data c p = (c',p',names) ⇒
  c'.data_conf = c.data_conf ∧
  c'.word_conf = c.word_conf ∧
  c'.word_to_word_conf = c.word_to_word_conf ∧
  c'.stack_conf = c.stack_conf ∧
  c'.lab_conf = c.lab_conf
Proof
  strip_tac
  \\ fs [to_data_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_bvi_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_bvl_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_clos_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_flat_def] \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem to_liveset_0_thm:
  to_livesets c p = to_livesets_0 (to_word_0 c p)
Proof
  fs [to_livesets_def,to_livesets_0_def,to_word_0_def]
  \\ Cases_on ‘to_data c p’ \\ fs [] \\ PairCases_on ‘r’ \\ fs []
  \\ fs [to_livesets_0_def,to_word_0_def,data_to_wordTheory.compile_0_def]
  \\ imp_res_tac to_data_conf_inv \\ fs []
QED

val from_livesets_def = Define`
  from_livesets ((k,data),c,names,p) =
  let (word_conf,asm_conf) = (c.word_to_word_conf,c.lab_conf.asm_conf) in
  let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
  let alg = word_conf.reg_alg in
  let prog_with_oracles = ZIP (n_oracles,ZIP(data,p)) in
  let p =
    MAP (λ(col_opt,((tree,heu_moves,spillcosts,forced),name_num,arg_count,prog)).
      case oracle_colour_ok k col_opt tree prog forced of
        NONE =>
          let cp =
            (case select_reg_alloc alg spillcosts k heu_moves tree forced of
              M_success col =>
                (apply_colour (total_colour col) prog)
            | M_failure _ => prog (*cannot happen*)) in
          (name_num,arg_count,remove_must_terminate cp)
      | SOME col_prog => (name_num,arg_count,remove_must_terminate col_prog)) prog_with_oracles in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  from_word c names p`;

Triviality ZIP_MAP_MAP:
  ∀xs. ZIP (MAP f xs, MAP g xs) = MAP (λx. (f x, g x)) xs
Proof
  Induct \\ fs []
QED

Triviality EL_ZIP_MAP:
  ∀p q x.
    x < LENGTH q ∧ x < LENGTH p ⇒
    (EL x (ZIP (q, MAP f p))) = (λ(y,x). (x,f y)) (EL x (ZIP (p,q)))
Proof
  Induct \\ Cases_on ‘q’ \\ fs [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem from_word_0_to_livesets_0:
  from_word_0 c names p =
  from_livesets (to_livesets_0 (c,p,names))
Proof
  simp[to_livesets_0_def,from_word_0_def,from_livesets_def] >>
  simp[word_to_wordTheory.compile_def] >>
  Cases_on ‘next_n_oracle (LENGTH p) c.word_to_word_conf.col_oracle’ >> fs [] >>
  AP_TERM_TAC >>
  match_mp_tac LIST_EQ >>
  conj_tac THEN1 fs [Once MIN_COMM] >>
  fs [] \\ rpt strip_tac >>
  simp[MAP_MAP_o]>>
  simp[EL_MAP,EL_ZIP]>>
  fs [ZIP_MAP_MAP,EL_ZIP_MAP] >>
  rpt(pairarg_tac>>fs[])>>
  fs[full_compile_single_def]>>
  fs [compile_single_def,word_allocTheory.word_alloc_def] >>
  gvs [] >> BasicProvers.EVERY_CASE_TAC>>fs[]
QED

Theorem compile_oracle:
    from_livesets (to_livesets c p) = compile c p
Proof
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def,to_livesets_def] >>
  fs[compile_def,compile_tap_def]>>
  pairarg_tac>>
  fs[data_to_wordTheory.compile_def,word_to_wordTheory.compile_def]>>
  fs[from_livesets_def,from_word_def,from_stack_def,from_lab_def]>>
  unabbrev_all_tac>>fs[]>>
  rpt (pairarg_tac >> fs []) >>
  rveq>>fs[]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_abbrev_tac`progs = MAP A B`>>
  qpat_abbrev_tac`progs' = MAP A B`>>
  qsuff_tac `progs = progs'`>>rw[]>>
  unabbrev_all_tac>>
  fs[next_n_oracle_def]>>
  pop_assum mp_tac >>
  IF_CASES_TAC>>
  strip_tac>>rveq>>fs[]>>
  match_mp_tac LIST_EQ>>
  qmatch_goalsub_abbrev_tac`data_to_word$stubs _ _ ++ p2`
  \\ qmatch_goalsub_abbrev_tac`MAP f (data_to_word$stubs _ _)`
  \\ REWRITE_TAC[GSYM MAP_APPEND]
  \\ qpat_abbrev_tac`pp = _ ++ p2`
  \\ simp[MAP_MAP_o]
  \\ rw[]>>
  simp[EL_MAP,MIN_DEF,EL_ZIP,full_compile_single_def,EL_ZIP,LENGTH_TAKE]
  \\ qpat_abbrev_tac`len = _ + LENGTH (data_to_word$stubs _ _)`
  \\ `len = LENGTH pp` by simp[Abbr`pp`,Abbr`p2`]
  \\ qunabbrev_tac`len` \\ fs[] >>
  rw[]>>fs[EL_MAP,EL_ZIP,full_compile_single_def,compile_single_def,Abbr`f`]>>
  rpt(pairarg_tac>>fs[])>>
  fs[word_to_wordTheory.compile_single_def,word_allocTheory.word_alloc_def]>>
  rveq>>fs[]>>
  BasicProvers.EVERY_CASE_TAC>>fs[]
QED

Theorem compile_oracle_word_0:
  compile c p =
  let (c,p,names) = to_word_0 c p in
  from_word_0 c names p
Proof
  simp[from_word_0_to_livesets_0, GSYM compile_oracle,to_liveset_0_thm]>>
  pairarg_tac>>simp[]
QED

Theorem to_livesets_invariant:
  wc.reg_alg = c.word_to_word_conf.reg_alg ⇒
  to_livesets (c with word_to_word_conf:=wc) p =
  let (rcm,c,p) = to_livesets c p in
    (rcm,c with word_to_word_conf:=wc,p)
Proof
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def,to_livesets_def] >>
  unabbrev_all_tac>>fs[]>>
  rpt(rfs[]>>fs[])
QED

Theorem to_livesets_0_invariant:
  (wc.reg_alg = c.word_to_word_conf.reg_alg) ⇒
  (to_livesets_0 (c with word_to_word_conf:=wc,p,names) =
  let (rcm,c,p) = to_livesets_0 (c,p,names) in
    (rcm,c with word_to_word_conf:=wc,p))
Proof
  rw[FUN_EQ_THM,to_livesets_0_def]
QED

Theorem to_data_change_config:
   to_data c1 prog = (c1',prog') ⇒
   c2.source_conf = c1.source_conf ∧
   c2.clos_conf = c1.clos_conf ∧
   c2.bvl_conf = c1.bvl_conf
   ⇒
   to_data c2 prog =
     (c2 with <| source_conf := c1'.source_conf;
                 clos_conf := c1'.clos_conf;
                 bvl_conf := c1'.bvl_conf |>,
      prog')
Proof
  rw[to_data_def,to_bvi_def,to_bvl_def,to_clos_def,to_flat_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rw[] \\ fs[] \\ rfs[] \\ rveq \\ fs[] \\ rfs[] \\ rveq \\ fs[]
  \\ simp[config_component_equality]
QED

val ensure_fp_conf_ok_def = Define `
  ensure_fp_conf_ok asm_c c =
  c with <|has_fp_ops := (1 < asm_c.fp_reg_count);
          has_fp_tern := (asm_c.ISA = ARMv7 ∧ 2 < asm_c.fp_reg_count)|>`;

Overload bvl_inline_compile_prog[local] = ``bvl_inline$compile_prog``
Overload bvi_tailrec_compile_prog[local] = ``bvi_tailrec$compile_prog``
Overload bvi_to_data_compile_prog[local] = ``bvi_to_data$compile_prog``
Overload bvl_to_bvi_compile_prog[local] = ``bvl_to_bvi$compile_prog``
Overload bvl_to_bvi_compile_inc[local] = ``bvl_to_bvi$compile_inc``
Overload bvl_to_bvi_compile[local] = ``bvl_to_bvi$compile``
Overload bvi_to_data_compile[local] = ``bvi_to_data$compile``
Overload bvi_let_compile[local] = ``bvi_let$compile``
Overload bvl_const_compile[local] = ``bvl_const$compile``
Overload bvl_handle_compile[local] = ``bvl_handle$compile``
Overload bvl_inline_compile_inc[local] = ``bvl_inline$compile_inc``
Overload bvl_to_bvi_compile_exps[local] = ``bvl_to_bvi$compile_exps``
Overload flat_to_clos_inc_compile[local] = ``flat_to_clos$inc_compile_decs``
Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``

Datatype:
  backend_progs =
  <| env_id : num # num
   ; source_prog : ast$dec list
   ; flat_prog : flatLang$dec list
   ; clos_prog : closLang$exp list # (num # num # closLang$exp) list
   ; bvl_prog : (num # num # bvl$exp) list
   ; bvi_prog : (num # num # bvi$exp) list
   ; data_prog : (num # num # dataLang$prog) list
   ; word_prog : (num # num # 'a wordLang$prog) list
   ; stack_prog : (num # 'a stackLang$prog) list
   ; cur_bm : 'a word list
   ; lab_prog : 'a sec list
   ; target_prog : (word8 list # 'a word list) option
   |>
End

val empty_progs_def = Define `
  empty_progs = <| env_id := (0, 0); source_prog := []; flat_prog := [];
    clos_prog := ([], []); bvl_prog := []; bvi_prog := [];
    data_prog := []; word_prog := []; stack_prog := []; cur_bm := [];
    lab_prog := []; target_prog := SOME ([], []) |>`;

Definition keep_progs_def:
  keep_progs k ps = (case k of T => ps | _ => [])
End

val compile_inc_progs_def = Define`
  compile_inc_progs k c p_tup =
    let (env_id,p) = p_tup in
    let ps = empty_progs with <| env_id := env_id; source_prog := p |> in
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$inc_compile env_id c.source_conf p in
    let ps = ps with <| flat_prog := keep_progs k p |> in
    let c = c with source_conf := c' in
    let p = flat_to_clos_inc_compile p in
    let ps = ps with <| clos_prog := (keep_progs k ## keep_progs k) p |> in
    let (c',p) = clos_to_bvl_compile_inc c.clos_conf p in
    let c = c with clos_conf := c' in
    let ps = ps with <| bvl_prog := keep_progs k p |> in
    let (c', p) = bvl_to_bvi_compile_inc_all c.bvl_conf p in
    let c = c with <| bvl_conf := c' |> in
    let ps = ps with <| bvi_prog := keep_progs k p |> in
    let p = bvi_to_data_compile_prog p in
    let ps = ps with <| data_prog := keep_progs k p |> in
    let asm_c = c.lab_conf.asm_conf in
    let dc = ensure_fp_conf_ok asm_c c.data_conf in
    let p = MAP (compile_part dc) p in
    let reg_count1 = asm_c.reg_count - (5 + LENGTH asm_c.avoid_regs) in
    let p = MAP (\p. full_compile_single asm_c.two_reg_arith reg_count1
        c.word_to_word_conf.reg_alg asm_c (p, NONE)) p in
    let ps = ps with <| word_prog := keep_progs k p |> in
    let bm0 = c.word_conf.bitmaps_length in
    let (p, fs, bm) = compile_word_to_stack reg_count1 p (Nil, bm0) in
    let cur_bm = append (FST bm) in
    let c = c with word_conf := (c.word_conf with bitmaps_length := SND bm) in
    let ps = ps with <| stack_prog := keep_progs k p ; cur_bm := cur_bm |> in
    let reg_count2 = asm_c.reg_count - (3 + LENGTH asm_c.avoid_regs) in
    let p = stack_to_lab$compile_no_stubs
        c.stack_conf.reg_names c.stack_conf.jump asm_c.addr_offset
        reg_count2 p in
    let ps = ps with <| lab_prog := keep_progs k p |> in
    let target = lab_to_target$compile c.lab_conf (p:'a prog) in
    let ps = ps with <| target_prog := OPTION_MAP
        (\(bytes, _). (bytes, cur_bm)) target |> in
    let c = c with lab_conf updated_by (case target of NONE => I
        | SOME (_, c') => K c') in
    (c, ps)`;

(* this type is used to construct the oracle in the eval semantics,
   and must be translated so that its IsTypeRep thm is proven *)
Datatype:
  inc_config =
  <| inc_source_conf : source_to_flat$config
   ; inc_clos_conf : clos_to_bvl$config
   ; inc_bvl_conf : bvl_to_bvi$config
   ; inc_data_conf : data_to_word$config
   ; inc_word_to_word_conf : word_to_word$config
   ; inc_word_conf : word_to_stack$config
   ; inc_stack_conf : stack_to_lab$config
   ; inc_lab_conf : lab_to_target$inc_config
   ; inc_symbols : (mlstring # num # num) list
   ; inc_tap_conf : tap_config
   |>
End

Definition config_to_inc_config_def:
  config_to_inc_config c =
  <| inc_source_conf := c.source_conf
   ; inc_clos_conf := c.clos_conf
   ; inc_bvl_conf := c.bvl_conf
   ; inc_data_conf := c.data_conf
   ; inc_word_to_word_conf := c.word_to_word_conf
   ; inc_word_conf := c.word_conf
   ; inc_stack_conf := c.stack_conf
   ; inc_lab_conf := lab_to_target$config_to_inc_config c.lab_conf
   ; inc_symbols := c.symbols
   ; inc_tap_conf := c.tap_conf
   |>
End

Definition inc_config_to_config_def:
  inc_config_to_config asm_c c =
  <| source_conf := c.inc_source_conf
   ; clos_conf := c.inc_clos_conf
   ; bvl_conf := c.inc_bvl_conf
   ; data_conf := c.inc_data_conf
   ; word_to_word_conf := c.inc_word_to_word_conf
   ; word_conf := c.inc_word_conf
   ; stack_conf := c.inc_stack_conf
   ; lab_conf := lab_to_target$inc_config_to_config asm_c c.inc_lab_conf
   ; symbols := c.inc_symbols
   ; tap_conf := c.inc_tap_conf
   |>
End

val components = theorem "config_component_equality"

Theorem inc_config_to_config_inv:
  asm_c = c.lab_conf.asm_conf ==>
  inc_config_to_config asm_c (config_to_inc_config c) = c
Proof
  simp [config_to_inc_config_def, inc_config_to_config_def, components]
  \\ simp [lab_to_targetTheory.config_to_inc_config_def,
    lab_to_targetTheory.inc_config_to_config_def,
    lab_to_targetTheory.config_component_equality]
QED

val inc_components = theorem "inc_config_component_equality"

Theorem config_to_inc_config_inv:
  config_to_inc_config (inc_config_to_config asm_c c) = c
Proof
  simp [config_to_inc_config_def, inc_config_to_config_def, inc_components]
  \\ simp [lab_to_targetTheory.config_to_inc_config_def,
    lab_to_targetTheory.inc_config_to_config_def,
    lab_to_targetTheory.inc_config_component_equality]
QED

val upper_w2w_def = Define `
  upper_w2w (w:'a word) =
    if dimindex (:'a) = 32 then w2w w << 32 else (w2w w):word64`;

Definition compile_inc_progs_for_eval_def:
  compile_inc_progs_for_eval asm_c x =
  let (env_id, inc_c', decs) = x in
  let c' = inc_config_to_config asm_c inc_c' in
  let (c'', ps) = compile_inc_progs T c' (env_id, decs) in
    OPTION_MAP (\(bs, ws). (config_to_inc_config c'', bs, MAP upper_w2w ws))
        ps.target_prog
End

Theorem to_word_0_invariant:
  (wc.reg_alg = c.word_to_word_conf.reg_alg) ⇒
  ((to_word_0 (c with word_to_word_conf:=wc) p) =
  let (c,p,names) = to_word_0 c p in
    (c with word_to_word_conf:=wc,p,names))
Proof
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def,to_livesets_def,to_word_0_def] >>
  unabbrev_all_tac>>fs[]>>
  rpt(rfs[]>>fs[])
QED

(* used in compilationLib *)
Theorem MAP_ZIP_ZIP:
  ∀n xs ys zs.
    LENGTH xs = n ∧ LENGTH ys = n ∧ LENGTH zs = n ⇒
    MAP f (ZIP (xs, ZIP (ys, zs))) =
    MAP3 (λx (y1,y2,y3,y4) (z1,z2,z3). f (x,(y1,y2,y3,y4),(z1,z2,z3))) xs ys zs
Proof
  Induct \\ fs [LENGTH_NIL,LENGTH_CONS,PULL_EXISTS,FORALL_PROD]
QED

(* used in compilationLib *)
Theorem TAKE_DROP_PAIR_LEMMA:
  LENGTH xs = n ⇒ (TAKE n xs, DROP n xs) = (xs, [])
Proof
  rw []
QED

Theorem compile_inc_progs_for_eval_eq:
  compile_inc_progs_for_eval asm_c' (env_id,inc_c,p) =
    let c = inc_config_to_config asm_c' inc_c in
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$inc_compile env_id c.source_conf p in
    let _ = empty_ffi (strlit "finished: source_to_flat") in
    let c = c with source_conf := c' in
    let p = flat_to_clos_inc_compile p in
    let _ = empty_ffi (strlit "finished: flat_to_clos") in
    let (c',p) = clos_to_bvl_compile_inc c.clos_conf p in
    let _ = empty_ffi (strlit "finished: clos_to_bvl") in
    let c = c with clos_conf := c' in
    let (c', p) = bvl_to_bvi_compile_inc_all c.bvl_conf p in
    let _ = empty_ffi (strlit "finished: bvl_to_bvi") in
    let c = c with <| bvl_conf := c' |> in
    let p = bvi_to_data_compile_prog p in
    let _ = empty_ffi (strlit "finished: bvi_to_data") in
    let asm_c = c.lab_conf.asm_conf in
    let dc = ensure_fp_conf_ok asm_c' c.data_conf in
    let p = MAP (compile_part dc) p in
    let reg_count1 = asm_c'.reg_count - (5 + LENGTH asm_c'.avoid_regs) in
    let p = MAP (\p. full_compile_single_for_eval asm_c'.two_reg_arith reg_count1
        c.word_to_word_conf.reg_alg asm_c' (p, NONE)) p in
    let _ = empty_ffi (strlit "finished: data_to_word") in
    let bm0 = c.word_conf.bitmaps_length in
    let (p, fs, bm) = compile_word_to_stack reg_count1 p (Nil, bm0) in
    let _ = empty_ffi (strlit "finished: word_to_stack") in
    let cur_bm = append (FST bm) in
    let c = c with word_conf := (c.word_conf with bitmaps_length := SND bm) in
    let reg_count2 = asm_c'.reg_count - (3 + LENGTH asm_c'.avoid_regs) in
    let p = stack_to_lab$compile_no_stubs
        c.stack_conf.reg_names c.stack_conf.jump asm_c'.addr_offset
        reg_count2 p in
    let _ = empty_ffi (strlit "finished: stack_to_lab") in
    let target = lab_to_target$compile c.lab_conf (p:'a prog) in
    let _ = empty_ffi (strlit "finished: lab_to_target") in
    let c = c with lab_conf updated_by (case target of NONE => I
                                        | SOME (_, c') => K c') in
      OPTION_MAP (λx. (config_to_inc_config c,FST x,MAP upper_w2w cur_bm)) target
Proof
  fs [compile_inc_progs_for_eval_def,compile_inc_progs_def, full_compile_single_for_eval_eq]
  \\ rpt (pairarg_tac \\ gvs [EVAL “(inc_config_to_config asm_c' inc_c).lab_conf.asm_conf”])
  \\ fs [optionTheory.OPTION_MAP_COMPOSE]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM,FORALL_PROD]
QED

val _ = export_theory();
