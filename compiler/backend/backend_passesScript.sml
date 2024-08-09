(*
  Reformulates compile definition to expose the result of each internal
  compiler pass
*)

open preamble backendTheory presLangTheory

val _ = new_theory"backend_passes";

val _ = set_grammar_ancestry ["backend"];

Datatype:
  any_prog = Source (ast$dec list)
           | Flat (flatLang$dec list)
           | Clos (closLang$exp list) ((num # num # closLang$exp) list)
           | Bvl ((num # num # bvl$exp) list) (mlstring sptree$num_map)
           | Bvi ((num # num # bvi$exp) list) (mlstring sptree$num_map)
           | Data ((num # num # dataLang$prog) list) (mlstring sptree$num_map)
           | Word ((num # num # α wordLang$prog) list) (mlstring sptree$num_map)
           | Stack ((num # α stackLang$prog) list) (mlstring sptree$num_map)
           | Lab (α sec list) (mlstring sptree$num_map)
End

Definition to_flat_all_def:
  to_flat_all (c:'a config) p =
    let ps = [] in
    let ps = ps ++ [(strlit "original source code",Source p)] in
    let p = source_let$compile_decs p in
    let ps = ps ++ [(strlit "after source_let",Source p)] in
    let (c',p) = source_to_flat$compile_prog c.source_conf p in
    let ps = ps ++ [(strlit "after source_to_flat",Flat p)] in
    let p = flat_elim$remove_flat_prog p in
    let ps = ps ++ [(strlit "after remove_flat",Flat p)] in
    let p = MAP (flat_pattern$compile_dec c'.pattern_cfg) p in
    let ps = ps ++ [(strlit "after flat_pattern",Flat p)] in
    let c = c with source_conf := c' in
      ((ps: (mlstring # 'a any_prog) list),c,p)
End

Theorem to_flat_thm:
  SND (to_flat_all c p) = to_flat c p
Proof
  fs [to_flat_all_def,to_flat_def,source_to_sourceTheory.compile_def,
      source_to_flatTheory.compile_prog_def,
      source_to_flatTheory.compile_def,
      source_to_flatTheory.compile_flat_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition to_clos_all_def:
  to_clos_all (c:'a config) p =
    let (ps,c,p) = to_flat_all c p in
    let p = flat_to_clos$compile_prog p in
    let ps = ps ++ [(strlit "after flat_to_clos",Clos p [])] in
      ((ps: (mlstring # 'a any_prog) list),c,p)
End

Theorem to_clos_thm:
  SND (to_clos_all c p) = to_clos c p
Proof
  assume_tac to_flat_thm
  \\ fs [to_clos_all_def,to_clos_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition to_bvl_all_def:
  to_bvl_all (c:'a config) p =
    let (ps,c,es0) = to_clos_all c p in
    let c0 = c.clos_conf in
    let es = clos_mti$compile c0.do_mti c0.max_app es0 in
    let ps = ps ++ [(strlit "after clos_mti",Clos es [])] in
    let loc = c0.next_loc + MAX 1 (LENGTH es) in
    let loc = if loc MOD 2 = 0 then loc else loc + 1 in
    let (n,es) = clos_number$renumber_code_locs_list loc es in
    let ps = ps ++ [(strlit "after clos_number",Clos es [])] in
    let (kc,es) = clos_known$compile c0.known_conf es in
    let ps = ps ++ [(strlit "after clos_known",Clos es [])] in
    let (es,g,aux) = clos_call$compile c0.do_call es in
    let ps = ps ++ [(strlit "after clos_call",Clos es aux)] in
    let prog = chain_exps c0.next_loc es ++ aux in
    let prog = clos_annotate$compile prog in
    let ps = ps ++ [(strlit "after clos_annotate",Clos [] prog)] in
    let c1 = c0 with
         <|start := c0.next_loc; next_loc := n; known_conf := kc;
           call_state := (g,aux)|> in
    let init_stubs = toAList (init_code c1.max_app) in
    let init_globs =
            [(num_stubs c1.max_app − 1,0,
              init_globals c1.max_app (num_stubs c1.max_app + c1.start))] in
    let comp_progs = clos_to_bvl$compile_prog c1.max_app prog in
    let prog' = init_stubs ++ init_globs ++ comp_progs in
    let func_names =
            make_name_alist (MAP FST prog') prog (num_stubs c1.max_app)
              c0.next_loc (LENGTH es0) in
    let ps = ps ++ [(strlit "after clos_to_bvl",Bvl prog' func_names)] in
    let c2 = c1 with start := num_stubs c1.max_app − 1 in
    let p = code_sort prog' in
    let c = c with clos_conf := c2 in
      ((ps: (mlstring # 'a any_prog) list),c,p,func_names)
End

Theorem to_bvl_thm:
  SND (to_bvl_all c p ) = to_bvl c p
Proof
  assume_tac to_clos_thm
  \\ fs [to_bvl_all_def,to_bvl_def,clos_to_bvlTheory.compile_def,
         clos_to_bvlTheory.compile_common_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition to_bvi_all_def:
  to_bvi_all (c:'a config) p =
    let (ps,c,p,names) = to_bvl_all c p in
    let start = c.clos_conf.start in
    let c0 = c.bvl_conf in
    let limit = c0.inline_size_limit in
    let split_seq = c0.split_main_at_seq in
    let cut_size = c0.exp_cut in
    let (inlines,prog1) = bvl_inline$tick_compile_prog limit LN p in
    let prog = MAP (λ(name,arity,exp). (name,arity, HD (remove_ticks [exp]))) prog1 in
    let ps = ps ++ [(strlit "after bvl_inline and remove_ticks",Bvl prog names)] in
    let prog = MAP (λ(name,arity,exp). (name,arity, let_op_sing exp)) prog in
    let ps = ps ++ [(strlit "after let_op_sing",Bvl prog names)] in
    let prog = MAP (λ(name,arity,exp). (name,arity,
                       bvl_handle$compile_any split_seq cut_size arity exp)) prog in
    let ps = ps ++ [(strlit "after bvl_handle",Bvl prog names)] in
    let (loc,code,n1) = bvl_to_bvi$compile_prog start 0 prog in
    let (n2,code') = bvi_tailrec$compile_prog (bvl_num_stubs + 2) code in
    let (s,p,l,n1,n2,names) = (loc,code',inlines,n1,n2,get_names (MAP FST code') names) in
    let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
      word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
      stack_remove$stub_names ())) names in
    let ps = ps ++ [(strlit "after bvl_to_bvi",Bvi code names)] in
    let ps = ps ++ [(strlit "after bvi_tailrec",Bvi code' names)] in
    let c = c with clos_conf updated_by (λc. c with start := s) in
    let c = c with bvl_conf updated_by
      (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
     ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Theorem to_bvi_thm:
  SND (to_bvi_all c p ) = to_bvi c p
Proof
  assume_tac to_bvl_thm
  \\ fs [to_bvi_all_def,to_bvi_def,bvl_to_bviTheory.compile_def,
         bvl_inlineTheory.compile_inc_def,bvl_inlineTheory.compile_prog_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [MAP_MAP_o,o_DEF]
  \\ rpt $ pop_assum mp_tac
  \\ qpat_abbrev_tac ‘f1 = MAP _ prog1’
  \\ qpat_abbrev_tac ‘f2 = MAP _ prog1’
  \\ qsuff_tac ‘f1 = f2’ >- (rw [] \\ gvs [])
  \\ unabbrev_all_tac
  \\ fs [FUN_EQ_THM,FORALL_PROD,MAP_EQ_f]
  \\ gvs [bvl_inlineTheory.optimise_def]
QED

Definition to_data_all_def:
  to_data_all (c:'a config) p =
    let (ps,c,p,names) = to_bvi_all c p in
    let p = MAP (λ(a,n,e). (a,n,FST (compile n (COUNT_LIST n) T [] [e]))) p in
    let ps = ps ++ [(strlit "after bvi_to_data",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,FST (data_live$compile e LN))) p in
    let ps = ps ++ [(strlit "after data_live",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,data_simp$simp e Skip)) p in
    let ps = ps ++ [(strlit "after data_simp",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,data_space$compile e)) p in
    let ps = ps ++ [(strlit "after data_space",Data p names)] in
      ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Theorem to_data_thm:
  SND (to_data_all (c:'a config) p) = to_data c p
Proof
  assume_tac to_bvi_thm
  \\ fs [to_data_all_def,to_data_def,bvi_to_dataTheory.compile_prog_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
  \\ gvs [MAP_EQ_f,FORALL_PROD,bvi_to_dataTheory.compile_part_def,
          bvi_to_dataTheory.compile_exp_def,bvi_to_dataTheory.optimise_def]
QED

Definition to_word_all_def:
  to_word_all (c:'a config) p =
    let (ps,c,p,names) = to_data_all c p in
    let data_conf = c.data_conf in
    let word_conf = c.word_to_word_conf in
    let asm_conf = c.lab_conf.asm_conf in
    let data_conf =
            data_conf with
            <|has_fp_ops := (1 < asm_conf.fp_reg_count);
              has_fp_tern :=
                (asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count)|> in
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) p in
    let ps = ps ++ [(strlit "after data_to_word",Word p names)] in
    let (two_reg_arith,reg_count) =
            (asm_conf.two_reg_arith,
             asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs)) in
    let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
    let p = ZIP (p,n_oracles) in
    let alg = word_conf.reg_alg in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,word_simp$compile_exp prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_simp",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                     inst_select asm_conf (max_var prog + 1) prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_inst",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,full_ssa_cc_trans arg_count prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_ssa",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,word_common_subexp_elim prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_cse",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,copy_prop prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_copy",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,remove_unreach prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_unreach",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,FST (remove_dead prog LN)),col_opt)) p in
    let ps = ps ++ [(strlit "after remove_dead in word_alloc",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                   if two_reg_arith then three_to_two_reg prog else prog),col_opt)) p in
    let ps = ps ++ [(strlit "after three_to_two_reg from word_inst",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                   remove_must_terminate
                     (word_alloc name_num asm_conf alg reg_count prog col_opt)))) p in
    let ps = ps ++ [(strlit "after word_alloc (and remove_must_terminate)",Word p names)] in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
      ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Theorem to_word_thm:
  SND (to_word_all (c:'a config) p) = to_word c p
Proof
  assume_tac to_data_thm
  \\ fs [to_word_all_def,to_word_def,data_to_wordTheory.compile_def,
         word_to_wordTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
  \\ gvs [MAP_EQ_f,FORALL_PROD,word_to_wordTheory.full_compile_single_def,
          word_to_wordTheory.compile_single_def]
QED

Definition to_stack_all_def:
  to_stack_all (c:'a config) p =
    let (ps,c,p,names) = to_word_all c p in
    let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let ps = ps ++ [(strlit "after word_to_stack",Stack p names)] in
    let c = c with word_conf := c' in
      ((ps: (mlstring # 'a any_prog) list),bm,c,p,names)
End

Theorem to_stack_thm:
  SND (to_stack_all (c:'a config) p) = to_stack c p
Proof
  assume_tac to_word_thm
  \\ fs [to_stack_all_def,to_stack_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition to_lab_all_def:
  to_lab_all (c:'a config) p =
    let (ps,bm,c,p,names) = to_stack_all c p in
    let stack_conf = c.stack_conf in
    let data_conf = c.data_conf in
    let max_heap = 2 * max_heap_limit (:'a) c.data_conf - 1 in
    let sp = c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3) in
    let offset = c.lab_conf.asm_conf.addr_offset in
    let prog = stack_rawcall$compile p in
    let ps = ps ++ [(strlit "after stack_rawcall",Stack prog names)] in
    let prog = stack_alloc$compile data_conf prog in
    let ps = ps ++ [(strlit "after stack_alloc",Stack prog names)] in
    let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                 max_heap sp InitGlobals_location prog in
    let ps = ps ++ [(strlit "after stack_remove",Stack prog names)] in
    let prog = stack_names$compile stack_conf.reg_names prog in
    let ps = ps ++ [(strlit "after stack_names",Stack prog names)] in
    let p = MAP prog_to_section prog in
    let ps = ps ++ [(strlit "after stack_to_lab",Lab p names)] in
      ((ps: (mlstring # 'a any_prog) list),bm:'a word list,c,p:'a prog,names)
End

Theorem to_lab_thm:
  SND (to_lab_all (c:'a config) p) = to_lab c p
Proof
  assume_tac to_stack_thm
  \\ fs [to_lab_all_def,to_lab_def,stack_to_labTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition to_target_all_def:
  to_target_all (c:'a config) p =
    let (ps,bm,c,p,names) = to_lab_all c p in
    let p = filter_skip p in
    let ps = ps ++ [(strlit "after filter_skip",Lab p names)] in
    let p = compile_lab c.lab_conf p in
      ((ps: (mlstring # 'a any_prog) list), attach_bitmaps names c bm p)
End

Theorem to_target_thm:
  SND (to_target_all c p) = to_target c p
Proof
  assume_tac to_lab_thm
  \\ fs [to_target_all_def,to_target_def,lab_to_targetTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition from_lab_all_def:
  from_lab_all ps (c:'a config) names p (bm:'a word list) =
    let p = filter_skip p in
    let ps = ps ++ [(strlit "after filter_skip",Lab p names)] in
    let p = compile_lab c.lab_conf p in
      ((ps: (mlstring # 'a any_prog) list), attach_bitmaps names c bm p)
End

Theorem from_lab_thm:
  SND (from_lab_all ps c names p bm) = from_lab c names p bm
Proof
  gvs [from_lab_all_def,from_lab_def,lab_to_targetTheory.compile_def]
QED

Definition from_stack_all_def:
  from_stack_all ps (c:'a config) names p bm =
    let stack_conf = c.stack_conf in
    let data_conf = c.data_conf in
    let max_heap = 2 * max_heap_limit (:'a) c.data_conf - 1 in
    let sp = c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3) in
    let offset = c.lab_conf.asm_conf.addr_offset in
    let prog = stack_rawcall$compile p in
    let ps = ps ++ [(strlit "after stack_rawcall",Stack prog names)] in
    let prog = stack_alloc$compile data_conf prog in
    let ps = ps ++ [(strlit "after stack_alloc",Stack prog names)] in
    let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                 max_heap sp InitGlobals_location prog in
    let ps = ps ++ [(strlit "after stack_remove",Stack prog names)] in
    let prog = stack_names$compile stack_conf.reg_names prog in
    let ps = ps ++ [(strlit "after stack_names",Stack prog names)] in
    let p = MAP prog_to_section prog in
    let ps = ps ++ [(strlit "after stack_to_lab",Lab p names)] in
      from_lab_all ps c names p bm
End

Theorem from_stack_thm:
  SND (from_stack_all ps c names p bm) = from_stack c names p bm
Proof
  gvs [from_stack_all_def,from_stack_def,stack_to_labTheory.compile_def,
       from_lab_thm]
QED

Definition from_word_all_def:
  from_word_all ps (c:'a config) names p =
    let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let ps = ps ++ [(strlit "after word_to_stack",Stack p names)] in
    let c = c with word_conf := c' in
      from_stack_all ps c names p bm
End

Theorem from_word_thm:
  SND (from_word_all ps c names p) = from_word c names p
Proof
  gvs [from_word_all_def,from_word_def,word_to_stackTheory.compile_def]
  \\ pairarg_tac \\ gvs [from_stack_thm]
QED

Definition from_word_0_all_def:
  from_word_0_all ps (c:'a config) names p =
    let word_conf = c.word_to_word_conf in
    let asm_conf = c.lab_conf.asm_conf in
    let (two_reg_arith,reg_count) =
            (asm_conf.two_reg_arith,
             asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs)) in
    let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
    let p = ZIP (p,n_oracles) in
    let alg = word_conf.reg_alg in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,word_simp$compile_exp prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_simp",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                     inst_select asm_conf (max_var prog + 1) prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_inst",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,full_ssa_cc_trans arg_count prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_ssa",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,word_common_subexp_elim prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_cse",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,copy_prop prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_copy",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,remove_unreach prog),col_opt)) p in
    let ps = ps ++ [(strlit "after word_unreach",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,FST (remove_dead prog LN)),col_opt)) p in
    let ps = ps ++ [(strlit "after remove_dead in word_alloc",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                   if two_reg_arith then three_to_two_reg prog else prog),col_opt)) p in
    let ps = ps ++ [(strlit "after three_to_two_reg from word_inst",Word (MAP FST p) names)] in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
                  ((name_num,arg_count,
                   remove_must_terminate
                     (word_alloc name_num asm_conf alg reg_count prog col_opt)))) p in
    let ps = ps ++ [(strlit "after word_alloc (and remove_must_terminate)",Word p names)] in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
      from_word_all ps c names p
End

Theorem from_word_0_thm:
  SND (from_word_0_all ps c names p) = from_word_0 c names p
Proof
  gvs [from_word_0_all_def,from_word_0_def]
  \\ fs [to_word_all_def,to_word_def,data_to_wordTheory.compile_def,
         word_to_wordTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
  \\ gvs [MAP_EQ_f,FORALL_PROD,word_to_wordTheory.full_compile_single_def,
          word_to_wordTheory.compile_single_def,from_word_thm]
  \\ AP_TERM_TAC
  \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
  \\ gvs [MAP_EQ_f,FORALL_PROD,word_to_wordTheory.full_compile_single_def,
          word_to_wordTheory.compile_single_def,from_word_thm]
QED

Definition from_data_all_def:
  from_data_all ps c names p =
    let data_conf = c.data_conf in
    let word_conf = c.word_to_word_conf in
    let asm_conf = c.lab_conf.asm_conf in
    let data_conf =
            data_conf with
            <|has_fp_ops := (1 < asm_conf.fp_reg_count);
              has_fp_tern :=
                (asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count)|> in
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) p in
    let ps = ps ++ [(strlit "after data_to_word",Word p names)] in
      from_word_0_all ps c names p
End

Theorem from_data_thm:
  SND (from_data_all ps c names p) = from_data c names p
Proof
  gvs [from_data_all_def,from_data_def,from_word_0_thm]
  \\ gvs [backendTheory.from_word_0_def]
  \\ gvs [data_to_wordTheory.compile_def]
QED

Theorem to_data_all_from_data_all_correctness:
  to_target_all c p =
    let (ps,c',p,ns) = to_data_all c p in
      from_data_all ps c' ns p
Proof
  gvs [to_target_all_def,to_lab_all_def,to_stack_all_def,to_word_all_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [from_data_all_def,from_word_0_all_def,from_word_all_def,
          from_stack_all_def,from_lab_all_def]
QED

Theorem compile_eq_to_target_all:
  compile c p = SND (to_target_all c p)
Proof
  rewrite_tac [compile_eq_to_target,GSYM to_target_thm]
QED

Theorem number_of_passes:
  LENGTH (FST (to_target_all c p)) = 38
Proof
  fs [to_target_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_lab_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_stack_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_word_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_data_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_bvi_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_bvl_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_clos_all_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [to_flat_all_def] \\ rpt (pairarg_tac \\ gvs [])
QED

Definition any_prog_pp_def:
  any_prog_pp p = case p of
    | Source p => source_to_strs p
    | Flat p => flat_to_strs p
    | Clos decs funs => clos_to_strs (decs,funs)
    | Bvl p names => bvl_to_strs names p
    | Bvi p names => bvi_to_strs names p
    | Data p names => data_to_strs names p
    | Word p names => word_to_strs names p
    | Stack p names => stack_to_strs names p
    | Lab p names => lab_to_strs names p
End

Definition pp_with_title_def:
  pp_with_title pp (title,p) acc =
    Append (List [strlit "# "; title; strlit "\n\n"]) $
    Append (pp p) acc
End

Definition compile_tap_def:
  compile_tap (c:'a config) p =
    if c.tap_conf.explore_flag then
      let (ps,out) = to_target_all c p in
        (out, FOLDR (pp_with_title any_prog_pp) Nil ps)
    else (compile c p, Nil)
End

Theorem compile_alt:
  compile c p = FST (compile_tap c p)
Proof
  rw [compile_tap_def]
  \\ mp_tac compile_eq_to_target_all
  \\ pairarg_tac \\ gvs []
QED

val _ = export_theory();
