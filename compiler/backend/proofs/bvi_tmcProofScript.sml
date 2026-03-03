(*
  Correctness proof for bvi_tailrec
*)
Theory bvi_tmcProof
Ancestors
  bvi_tmc (* bviProps bviSem *)
Libs
  preamble

Definition code_rel_def:
  code_rel c1 c2 ⇔
    ∀loc arity exp op.
      lookup loc c1 = SOME (arity, exp) ⇒
      ∃n.
        (rewrite_aux loc n arity exp = NONE ⇒
          lookup loc c2 = SOME (arity, exp)) ∧
        (rewrite_aux loc n arity exp = SOME op ⇒
          ∀exp_aux exp_opt.
            compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
              lookup loc c2 = SOME (arity, exp_aux) ∧
              lookup n c2 = SOME (arity + 1, exp_opt))
End

