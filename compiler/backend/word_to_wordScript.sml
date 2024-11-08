(*
  This compiler phase composes the phases internal to wordLang:
      1) word_simp ; 2) inst_select ; 3) SSA ; 4) remove_dead
      5) word_cse ; 6) copy_prop ; 7) three-to-two reg
      8) remove_unreach ; 9) remove_dead ; 10) word_alloc
*)
open preamble asmTheory wordLangTheory word_allocTheory word_removeTheory
open word_simpTheory word_cseTheory word_unreachTheory word_copyTheory word_instTheory
open mlstringTheory;

val _ = new_theory "word_to_word";


(*reg_alg = choice of register allocator*)
Datatype:
  config =
  <| reg_alg : num
   ; col_oracle : (num num_map) option list |>
End

Definition compile_single_def:
  compile_single is_x64 two_reg_arith reg_count alg c ((name_num:num,arg_count,prog),col_opt) =
  let prog = word_simp$compile_exp prog in
  let maxv = max_var prog + 1 in
  let inst_prog = inst_select c maxv prog in
  let ssa_prog = full_ssa_cc_trans is_x64 arg_count inst_prog in
  let rm_ssa_prog = remove_dead_prog ssa_prog in
  let cse_prog = word_common_subexp_elim rm_ssa_prog in
  let cp_prog = copy_prop cse_prog in
  let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
  let unreach_prog = remove_unreach two_prog in
  let rm_prog = remove_dead_prog unreach_prog in
  let reg_prog = word_alloc name_num c alg reg_count rm_prog col_opt in
    (name_num,arg_count,reg_prog)
End

Definition full_compile_single_def:
  full_compile_single is_x64 two_reg_arith reg_count alg c p =
  let (name_num,arg_count,reg_prog) = compile_single is_x64 two_reg_arith reg_count alg c p in
    (name_num,arg_count,remove_must_terminate reg_prog)
End

Definition next_n_oracle_def:
  next_n_oracle n (col:(num num_map) option list) =
  if n ≤ LENGTH col then
    (TAKE n col, DROP n col)
  else
    (REPLICATE n NONE, [])
End

Definition compile_def:
  compile word_conf (asm_conf:'a asm_config) progs =
    let (is_x64,two_reg_arith,reg_count) = (asm_conf.ISA = x86_64, asm_conf.two_reg_arith, asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)) in
    let (n_oracles,col) = next_n_oracle (LENGTH progs) word_conf.col_oracle in
    let progs = ZIP (progs,n_oracles) in
    (col,MAP (full_compile_single is_x64 two_reg_arith reg_count word_conf.reg_alg asm_conf) progs)
End

Definition full_compile_single_for_eval_def:
  full_compile_single_for_eval is_x64 two_reg_arith reg_count alg c p =
    let ((name_num,arg_count,prog),col_opt) = p in
    let prog = word_simp$compile_exp prog in
    let _ = empty_ffi (strlit "finished: word_simp") in
    let maxv = max_var prog + 1 in
    let inst_prog = inst_select c maxv prog in
    let _ = empty_ffi (strlit "finished: word_inst") in
    let ssa_prog = full_ssa_cc_trans is_x64 arg_count inst_prog in
    let _ = empty_ffi (strlit "finished: word_ssa") in
    let rm_ssa_prog = remove_dead_prog ssa_prog in
    let _ = empty_ffi (strlit "finished: word_remove_dead after word_ssa") in
    let cse_prog = word_common_subexp_elim rm_ssa_prog in
    let _ = empty_ffi (strlit "finished: word_cse") in
    let cp_prog = copy_prop cse_prog in
    let _ = empty_ffi (strlit "finished: word_copy") in
    let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
    let _ = empty_ffi (strlit "finished: word_two_reg") in
    let unreach_prog = remove_unreach two_prog in
    let _ = empty_ffi (strlit "finished: word_unreach") in
    let rm_prog = remove_dead_prog unreach_prog in
    let _ = empty_ffi (strlit "finished: word_remove_dead") in
    let reg_prog = word_alloc name_num c alg reg_count rm_prog col_opt in
    let _ = empty_ffi (strlit "finished: word_alloc") in
    let rmt_prog = remove_must_terminate reg_prog in
    let _ = empty_ffi (strlit "finished: word_remove") in
      (name_num,arg_count,rmt_prog)
End

Theorem full_compile_single_for_eval_eq:
  full_compile_single is_x64 two_reg_arith reg_count alg c p =
  full_compile_single_for_eval is_x64 two_reg_arith reg_count alg c p
Proof
  rw [full_compile_single_for_eval_def, full_compile_single_def]
  \\ PairCases_on ‘p’ \\ simp [compile_single_def]
QED

(* TODO: never used?
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
    let rm_ssa_ps = MAP remove_dead_prog ssa_ps in
    let _ = empty_ffi (strlit "finished: word_remove_dead after word_ssa") in
    let cse_ps = MAP word_common_subexp_elim rm_ssa_ps in
    let _ = empty_ffi (strlit "finished: word_cse") in
    let cp_ps = MAP copy_prop cse_ps in
    let _ = empty_ffi (strlit "finished: word_copy") in
    let two_ps = MAP (three_to_two_reg_prog two_reg_arith) cp_ps in
    let _ = empty_ffi (strlit "finished: word_two_reg") in
    let unreach_ps = MAP remove_unreach two_ps in
    let _ = empty_ffi (strlit "finished: word_unreach") in
    let dead_ps = MAP remove_dead_prog unreach_ps in
    let _ = empty_ffi (strlit "finished: word_remove_dead") in
    let reg_ps = MAP2 (λc (n,p). word_alloc n asm_conf alg reg_count p c) n_oracles (ZIP(names,dead_ps)) in
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
*)

val _ = export_theory();
