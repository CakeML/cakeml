open HolKernel ml_translatorLib recfunsTheory pred_setTheory lcsymtacs

val _ = new_theory "mlrecfun"

(*
fails because of quotient type (and more?)
val res = translate Phi_def
val res = translate normal_orderTheory.bnf_of_def
val res = translate (LIST_CONJ (List.take (CONJUNCTS chap2Theory.bnf_def, 3)))
*)

(*
val recfun2ml = store_thm(
"recfun2ml",
``∀M. ∃cenv env exp cl. evaluate cenv env exp (Rval cl) ∧
  ∀n. ∃env exp. (do_app ARB Opapp cl (Lit (IntLit &n)) = SOME (env,exp)) ∧
      case Phi M n of
      | NONE => e_diverges cenv env exp
      | SOME x => evaluate cenv env exp (Rval (Lit (IntLit &x)))``,
should do this by simulation, hopefully by translating Phi or something equivalent to it
*)

val _ = export_theory ()
