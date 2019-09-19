(*
  Properties of floating-point value tree semantics
*)

open preamble fpSemTheory fpValTreeTheory semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

val _ = new_theory "fpSemProps";

Theorem fp_opts_mono[local]:
  ! (s1 s2 s3:'a state) n m.
    (! x. s1.fp_opts (n + x) = s2.fp_opts x) /\
    (! x. s2.fp_opts (m + x) = s3.fp_opts x) ==>
    ? k. ! x. s1.fp_opts (k + x) = s3.fp_opts x
Proof
  rpt strip_tac \\ qexists_tac `n+m`
  \\ qpat_x_assum `! x. _ _ = s3.fp_opts _` (qspec_then `x` (fn thm => fs[GSYM thm]))
  \\ qpat_x_assum `! x. _ _ = s2.fp_opts _` (qspec_then `m + x` (fn thm => fs[GSYM thm]))
QED

Theorem fp_opts_add_1[local]:
  ! (s1 s2:'a state) n m.
    (! x. s1.fp_opts (n + x) = s2.fp_opts x) ==>
    ? k. ! x. s1.fp_opts (k + x) = s2.fp_opts (x + 1)
Proof
  rpt strip_tac
  \\ qexists_tac `n+1` \\ fs[]
QED

Theorem evaluate_fp_opts_fixed:
  (! (s:'a state) env e s' r.
    evaluate s env e = (s', r) ==>
    (?n. ! x. s.fp_opts (x + n) = s'.fp_opts x) /\
    s.fp_rws = s'.fp_rws) /\
  (! (s:'a state) env v pes errv s' r.
    evaluate_match s env v pes errv = (s', r) ==>
    (?n. ! x. s.fp_opts (x + n) = s'.fp_opts x) /\
    s.fp_rws = s'.fp_rws)
Proof
  ho_match_mp_tac evaluate_ind \\ rw[]
  \\ rfs[evaluate_def] \\ rveq
  \\ TRY (qexists_tac `0` \\ fs[] \\ NO_TAC)
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs[fix_clock_def])
  \\ rpt strip_tac \\ rveq
  \\ res_tac \\ fs[dec_clock_def, shift_fp_opts_def]
  \\ imp_res_tac fp_opts_mono
  \\ imp_res_tac fp_opts_add_1
  \\ TRY (asm_exists_tac \\ fs[])
  \\ qexists_tac `0` \\ fs[]
QED

Theorem fpOp_determ:
  ! op refs refsN (ffi1 ffi1':'a ffi_state) (ffi2:'b ffi_state) r vl.
    isFpOp op /\
    do_app (refs, ffi1) op vl = SOME ((refsN, ffi1'), r) ==>
    do_app (refs, ffi2) op vl = SOME ((refsN, ffi2), r)
Proof
  rpt strip_tac \\ Cases_on `op` \\ fs[astTheory.isFpOp_def]
  \\ rpt (qpat_x_assum `do_app _ _ _ = _` mp_tac)
  \\ fs[do_app_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
QED

(*
Theorem compress_word_valid:
  ! v.
    isFpWordOp v ==>
    ? w. compress v =  (Rval (Litv (Word64 w)))
Proof
  Induct_on `v` \\ fs[isFpWordOp_def, compress_def] \\ rpt strip_tac
  \\ res_tac \\ fs[]
QED

Theorem compress_bool_valid:
  ! v.
    isFpBoolOp v ==>
    ? b. compress v = (Rval (Boolv b))
Proof
  Induct_on `v` \\ fs[isFpBoolOp_def, compress_def] \\ rpt strip_tac
  \\ imp_res_tac compress_word_valid \\ fs[]
  >- (qexists_tac `fp_pred_comp f0 w` \\ fs[])
  \\ rename [`fp_cmp_comp f1 w1 w2`]
  \\ qexists_tac `fp_cmp_comp f1 w1 w2` \\ fs[]
QED
*)

val _ = export_theory();
