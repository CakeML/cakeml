open HolKernel boolLib bossLib lcsymtacs
open ml_translatorLib ml_hol_kernelTheory holKernelProofTheory
open bigStepTheory
open terminationTheory

val _ = new_theory"ml_hol_init"

val _ = Globals.max_print_depth := 20

val kernel_init_thm = store_thm("kernel_init_thm",
  ``∃refs.
      HOL_STORE (SND (Tmod_state "Kernel" ml_hol_kernel_decls)) refs ∧
      STATE init_ctxt refs``,
  mp_tac (CONJUNCT1 kernel_thm) >>
  simp[Once evaluate_top_cases] >> strip_tac >>
  cheat)

val _ = export_theory()
