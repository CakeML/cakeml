open HolKernel boolLib bossLib lcsymtacs arithmeticTheory

val _ = new_theory"clock"

val _ = new_type("result",0)
val _ = new_type("code",0)
val _ = new_type("exp",0)
val _ = new_constant("compile",``:exp->code``)
val _ = Hol_datatype`clock_result = Complete of result | Timeout`
val _ = new_constant("bc_eval_clock",``:num->code->clock_result->bool``)
val _ = new_constant("bc_eval",``:code->result->bool``)
val _ = new_constant("evaluate_clock",``:num->exp->clock_result->bool``)
val _ = new_constant("evaluate",``:exp->result->bool``)
val _ = new_constant("bc_clock",``:num->num``)

val bc_eval_clock_sound = new_axiom("bc_eval_clock_sound",
  ``∀ck code res. bc_eval_clock ck code (Complete res) ⇒ bc_eval code res``)

val bc_eval_can_be_clocked = new_axiom("bc_eval_can_be_clocked",
  ``∀code res. bc_eval code res ⇒ ∃ck. bc_eval_clock ck code (Complete res)``)

  (*
val bc_eval_clock_total = new_axiom("bc_eval_clock_total",
  ``∀ck code. (∃res. bc_eval_clock ck code (Complete res))
            ∨ (bc_eval_clock ck code Timeout)``)
            *)

val bc_eval_clock_determ = new_axiom("bc_eval_clock_determ",
  ``∀ck code r1 r2. bc_eval_clock ck code r1 ⇒ bc_eval_clock ck code r2 ⇒ (r1 = r2)``)

  (*
val bc_more_time = new_axiom("bc_more_time",
  ``∀ck code res ck'. bc_eval_clock ck code (Complete res) ∧ ck < ck' ⇒ bc_eval_clock ck' code (Complete res)``)
  *)

val bc_less_time = new_axiom("bc_less_time",
  ``∀ck code res ck'. bc_eval_clock ck code Timeout ∧ ck' < ck ⇒ bc_eval_clock ck' code Timeout``)

val compile_correct = new_axiom("compile_correct",
  ``∀ck exp cr. evaluate_clock ck exp cr ⇒ bc_eval_clock (bc_clock ck) (compile exp) cr``)

val bc_clock_unbounded = new_axiom("bc_clock_unbounded",
  ``∀n. ∃m. n ≤ bc_clock m``)

val evaluate_clock_sound = new_axiom("evaluate_clock_sound",
  ``∀ck exp res. evaluate_clock ck exp (Complete res) ⇒ evaluate exp res``)

val evaluate_can_be_clocked = new_axiom("evaluate_can_be_clocked",
  ``∀exp res. evaluate exp res ⇒ ∃ck. evaluate_clock ck exp (Complete res)``)

val evaluate_clock_total = new_axiom("evaluate_clock_total",
  ``∀ck exp. (∃res. evaluate_clock ck exp (Complete res))
           ∨ (evaluate_clock ck exp Timeout)``)

val th1 = store_thm("th1",
  ``∀exp res. evaluate exp res ⇒ bc_eval (compile exp) res``,
  metis_tac[evaluate_can_be_clocked,compile_correct,bc_eval_clock_sound])

  (*
val lem = prove(
  ``∀exp. (∀ck. evaluate_clock ck exp Timeout) ⇒ (∀ck. bc_eval_clock ck (compile exp) Timeout)``,
  rw[] >>
  qspec_then`ck`strip_assume_tac bc_clock_unbounded >>
  spose_not_then strip_assume_tac >>
  `∃res. bc_eval_clock ck (compile exp) (Complete res)` by
    metis_tac[bc_eval_clock_total] >>
  imp_res_tac bc_more_time >>
  first_x_assum(qspec_then`m`strip_assume_tac) >>
  imp_res_tac compile_correct >>
  imp_res_tac bc_eval_clock_determ >>
  fs[])
  *)

val lem = prove(
  ``∀exp. (∀ck. evaluate_clock ck exp Timeout) ⇒ (∀ck. bc_eval_clock ck (compile exp) Timeout)``,
  rw[] >>
  spose_not_then strip_assume_tac >>
  `!ck. bc_eval_clock (bc_clock ck) (compile exp) Timeout` by
    metis_tac[compile_correct] >>
  `?ck'. (ck <= bc_clock ck')` by metis_tac [bc_clock_unbounded] >>
  `!x (y:num). x ≤ y = x < y ∨ (x = y)` by decide_tac >>
  metis_tac [bc_less_time]);

val th2 = store_thm("th2",
  ``∀exp. (!res. ¬evaluate exp res) ⇒ (∀res. ¬bc_eval (compile exp) res)``,
  rw[] >>
  `∀ck. evaluate_clock ck exp Timeout` by (
    metis_tac[evaluate_clock_total,evaluate_clock_sound] ) >>
  imp_res_tac lem >>
  spose_not_then strip_assume_tac >>
  imp_res_tac bc_eval_can_be_clocked >>
  `Complete res = Timeout` by metis_tac[bc_eval_clock_determ] >>
  fs[])

val _ = export_theory()
