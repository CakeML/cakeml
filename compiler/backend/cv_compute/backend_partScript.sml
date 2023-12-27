(*
  Define functions similar to backendTheory, but adapted for cv_compute.
*)

open preamble backendTheory lab_to_targetTheory backend_enc_decTheory;

val _ = new_theory "backend_part";

(*
  TODO:
   - make from_word_0, defined below, return NONE if oracle_colour_ok
     returns NONE inside word_to_word -- this is so that the the
     register allocator implementation is unreachable from these
     definitions
   - improve definitions of from_lab_def and finalise_output_def so
     that config_to_inc_config and inc_config_to_config aren't used;
     this requires defining inc_config versions of lab_to_target
     internals (with asm_conf as first argument as in many functions
     in this script)
*)

(* define compiler in terms of inc_config rather than config *)

Definition to_flat_def:
  to_flat c p =
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$compile c.inc_source_conf p in
    let c = c with inc_source_conf := c' in
      (c,p)
End

Definition to_clos_def:
  to_clos c p =
    let (c,p) = to_flat c p in
    let p = flat_to_clos$compile_prog p in
      (c,p)
End

Definition to_bvl_def:
  to_bvl c p =
    let (c,p) = to_clos c p in
    let (c',p,names) = clos_to_bvl$compile c.inc_clos_conf p in
    let c = c with inc_clos_conf := c' in
      (c,p,names)
End

Definition to_bvi_def:
  to_bvi c p =
    let (c,p,names) = to_bvl c p in
    let (s,p,l,n1,n2,names) =
      bvl_to_bvi$compile c.inc_clos_conf.start c.inc_bvl_conf names p in
    let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
      word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
      stack_remove$stub_names ())) names in
    let c = c with inc_clos_conf updated_by (λc. c with start := s) in
    let c = c with inc_bvl_conf updated_by (λc. c with
                  <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
      (c,p,names)
End

Definition to_data_def:
  to_data c p =
    let (c,p,names) = to_bvi c p in
    let p = bvi_to_data$compile_prog p in
      (c,p,names)
End

Definition to_word_0_def:
  to_word_0 asm_conf c p =
    let (c,p,names) = to_data c p in
    let p = data_to_word$compile_0 c.inc_data_conf asm_conf p in
      (c,p,names)
End

Definition to_livesets_0_def:
  to_livesets_0 asm_conf (c:inc_config,p,names: mlstring num_map) =
  let word_conf = c.inc_word_to_word_conf in
  let alg = word_conf.reg_alg in
  let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith, asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)) in
  let p =
    MAP (λ(name_num,arg_count,prog).
    let prog = word_simp$compile_exp prog in
    let maxv = max_var prog + 1 in
    let inst_prog = inst_select asm_conf maxv prog in
    let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
    let cse_prog = word_common_subexp_elim ssa_prog in
    let rm_prog = FST(remove_dead cse_prog LN) in
    let prog = if two_reg_arith then three_to_two_reg rm_prog
                                else rm_prog in
     (name_num,arg_count,prog)) p in
  let data = MAP (\(name_num,arg_count,prog).
    let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
    (get_clash_tree prog,heu_moves,spillcosts,get_forced asm_conf prog [])) p
  in
    ((reg_count,data),c,names,p)
End

Definition to_livesets_def:
  to_livesets asm_conf c p =
    to_livesets_0 asm_conf (to_word_0 asm_conf c p)
End

Definition finalise_output_def:
  finalise_output NONE = NONE ∧
  finalise_output (SOME (bytes,words:'a word list,c1:'a config)) =
    let c2 = config_to_inc_config c1 in
      SOME (bytes,words,encode_backend_config c2)
End

Definition from_lab_def:
  from_lab (asm_conf :'a asm_config) c names p bm =
    let c0 = inc_config_to_config asm_conf c in
      finalise_output
        (attach_bitmaps names c0 bm (lab_to_target$compile c0.lab_conf p))
End

Definition from_stack_def:
  from_stack (asm_conf :'a asm_config) (c :inc_config) names p bm =
    let p = stack_to_lab$compile
      c.inc_stack_conf c.inc_data_conf (2 * max_heap_limit (:'a) c.inc_data_conf - 1)
      (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs +3))
      (asm_conf.addr_offset) p in
    from_lab asm_conf c names p bm
End

Definition from_word_def:
  from_word (asm_conf :'a asm_config) (c :inc_config) names p =
    let (bm,c',fs,p) = word_to_stack$compile asm_conf p in
    let c = c with inc_word_conf := c' in
      from_stack asm_conf c names p bm
End

Definition from_word_0_def:
  from_word_0 (asm_conf :'a asm_config) (c,p,names) =
    let (col,prog) = word_to_word$compile c.inc_word_to_word_conf asm_conf p in
    let c = c with inc_word_to_word_conf updated_by (λc. c with col_oracle := col) in
      from_word asm_conf c names prog
End

Definition compile_cake_def:
  compile_cake asm_conf c p =
    from_word_0 asm_conf (to_word_0 asm_conf c p)
End

Theorem compile_cake_thm:
  compile_cake asm_conf c p = SOME (bytes,bm,conf_str) ⇒
  ∃c1.
    backend$compile (inc_config_to_config asm_conf c) p = SOME (bytes,bm,c1) ∧
    conf_str = encode_backend_config (config_to_inc_config c1)
Proof
  cheat
QED

val _ = export_theory();
