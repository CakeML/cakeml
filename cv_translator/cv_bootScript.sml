(*
  Apply cv translator to bootstrap example from HOL
*)
open HolKernel Parse boolLib bossLib cv_memLib;
open cv_typeTheory cvTheory cv_typeLib cv_repLib wordsLib;
open arithmeticTheory wordsTheory cv_repTheory cv_primTheory cv_transLib;
open codegenTheory source_valuesTheory cv_stdTheory;

val _ = new_theory "cv_boot";

val res = cv_auto_trans even_len_def;
val res = cv_auto_trans c_pops_def;

val res = cv_auto_trans_pre_rec c_exp_def
 (WF_REL_TAC ‘inv_image (measure I LEX measure I)
    (λx. case x of INL (t,l,vs,fs,x) => (cv_sum_depth x, cv$c2n t)
                 | INR (l,vs,fs,xs) => (cv_sum_depth xs, 0))’
  \\ rpt strip_tac
  \\ (Cases_on ‘cv_z’ ORELSE Cases_on ‘cv_zs’) \\ gvs []
  \\ gvs [cvTheory.c2b_def]
  \\ cv_termination_tac \\ gvs [])

Theorem c_exp_pre[cv_pre]:
  (∀a0 a1 a2 a3 a4. c_exp_pre a0 a1 a2 a3 a4 = T) ∧
  (∀a5 a6 a7 a8. c_exps_pre a5 a6 a7 a8 = T)
Proof
  ho_match_mp_tac c_exp_ind
  \\ rpt strip_tac
  \\ rewrite_tac []
  \\ once_rewrite_tac [res]
  \\ simp []
QED

val res = cv_auto_trans codegen_def;
val res = cv_auto_trans compiler_progTheory.compiler_prog_def;

val _ = (max_print_depth := 10);

val res = cv_eval “codegen compiler_prog”;
val res = time EVAL “codegen compiler_prog”;

val _ = export_theory();
