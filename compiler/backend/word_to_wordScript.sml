(*
  This compiler phase composes the phases internal to wordLang:
      1) Inst select (with a few optimizations);
      2) SSA;
      3) Dead code elim (not written yet);
      4) 3-to-2 regs for certain configs;
      5) reg_alloc;
      6) word_to_stack.
*)
open preamble asmTheory wordLangTheory word_allocTheory word_removeTheory
open word_simpTheory word_cseTheory
local open word_instTheory in (* word-to-word transformations *) end
open mlstringTheory

val _ = new_theory "word_to_word";


(*reg_alg = choice of register allocator*)
val _ = Datatype`config =
  <| reg_alg : num
   ; col_oracle : (num num_map) option list |>`;

val compile_single_def = Define`
  compile_single two_reg_arith reg_count alg c ((name_num:num,arg_count,prog),col_opt) =
  let prog = word_simp$compile_exp prog in
  let maxv = max_var prog + 1 in
  let inst_prog = inst_select c maxv prog in
  let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
  let cse_prog = word_common_subexp_elim ssa_prog in
  let rm_prog = FST(remove_dead cse_prog LN) in
  let prog = if two_reg_arith then three_to_two_reg rm_prog
                              else rm_prog in
  let reg_prog = word_alloc name_num c alg reg_count prog col_opt in
    (name_num,arg_count,reg_prog)`

val full_compile_single_def = Define`
  full_compile_single two_reg_arith reg_count alg c p =
  let (name_num,arg_count,reg_prog) = compile_single two_reg_arith reg_count alg c p in
    (name_num,arg_count,remove_must_terminate reg_prog)`

val next_n_oracle_def = Define`
  next_n_oracle n (col:(num num_map) option list) =
  if n ≤ LENGTH col then
    (TAKE n col, DROP n col)
  else
    (REPLICATE n NONE, [])`

val compile_def = Define `
  compile word_conf (asm_conf:'a asm_config) progs =
    let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith, asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)) in
    let (n_oracles,col) = next_n_oracle (LENGTH progs) word_conf.col_oracle in
    let progs = ZIP (progs,n_oracles) in
    (col,MAP (full_compile_single two_reg_arith reg_count word_conf.reg_alg asm_conf) progs)`

Definition full_compile_single_for_eval_def:
  full_compile_single_for_eval two_reg_arith reg_count alg c p =
    let ((name_num,arg_count,prog),col_opt) = p in
    let prog = word_simp$compile_exp prog in
    let _ = empty_ffi (strlit "finished: word_simp") in
    let maxv = max_var prog + 1 in
    let inst_prog = inst_select c maxv prog in
    let _ = empty_ffi (strlit "finished: word_inst") in
    let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
    let _ = empty_ffi (strlit "finished: word_ssa") in
    let cse_prog = word_common_subexp_elim ssa_prog in
    let _ = empty_ffi (strlit "finished: word_cse") in
    let rm_prog = FST(remove_dead cse_prog LN) in
    let _ = empty_ffi (strlit "finished: word_remove_dead") in
    let prog = if two_reg_arith then three_to_two_reg rm_prog
                                else rm_prog in
    let _ = empty_ffi (strlit "finished: word_two_reg") in
    let reg_prog = word_alloc name_num c alg reg_count prog col_opt in
    let _ = empty_ffi (strlit "finished: word_alloc") in
    let rmt_prog = remove_must_terminate reg_prog in
    let _ = empty_ffi (strlit "finished: word_remove") in
      (name_num,arg_count,rmt_prog)
End

Theorem full_compile_single_for_eval_eq:
  full_compile_single two_reg_arith reg_count alg c p =
  full_compile_single_for_eval two_reg_arith reg_count alg c p
Proof
  rw [full_compile_single_for_eval_def, full_compile_single_def]
  \\ PairCases_on ‘p’ \\ simp [compile_single_def]
QED

Theorem compile_alt:
    compile word_conf (asm_conf:'a asm_config) progs =
    let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith, asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)) in
    let (n_oracles,col) = next_n_oracle (LENGTH progs) word_conf.col_oracle in
    let alg = word_conf.reg_alg in
    let names = MAP (λ(x,y,z). x) progs in
    let args = MAP (λ(x,y,z). y) progs in
    let ps = MAP (\(x,y,z). z) progs in
    let simp_ps = MAP word_simp$compile_exp ps in
    let _ = empty_ffi (strlit "finished: word_simp") in
    let inst_ps = MAP (λp. inst_select asm_conf (max_var p +1) p) simp_ps in
    let _ = empty_ffi (strlit "finished: word_inst") in
    let ssa_ps = MAP2 (λa p. full_ssa_cc_trans a p) args inst_ps in
    let _ = empty_ffi (strlit "finished: word_ssa") in
    let cse_ps = MAP word_common_subexp_elim ssa_ps in
    let _ = empty_ffi (strlit "finished: word_cse") in
    let dead_ps = MAP (\p. FST (remove_dead p LN)) cse_ps in
    let _ = empty_ffi (strlit "finished: word_remove_dead") in
    let two_ps = if two_reg_arith then MAP three_to_two_reg dead_ps else dead_ps in
    let _ = empty_ffi (strlit "finished: word_two_reg") in
    let reg_ps = MAP2 (λc (n,p). word_alloc n asm_conf alg reg_count p c) n_oracles (ZIP(names,two_ps)) in
    let _ = empty_ffi (strlit "finished: word_alloc") in
    let rmt_ps = MAP remove_must_terminate reg_ps in
    let _ = empty_ffi (strlit "finished: word_remove") in
    (col,ZIP(names,ZIP(args,rmt_ps)))
Proof
  fs[compile_def,next_n_oracle_def]>>
  rw[LIST_EQ_REWRITE]>>
  simp[EL_ZIP,EL_MAP,EL_MAP2,full_compile_single_def]>>
  match_mp_tac EQ_SYM>>
  pairarg_tac>>fs[EL_TAKE]>>
  simp[compile_single_def]
QED

val _ = export_theory();
