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

(*
Theorem evaluate_rewrite_tmc:
   ∀xs ^s env1 r t opt s' acc env2 loc ts ty.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel ty opt acc env1 env2 ∧
     state_rel s s' /\
     ty_rel env1 ts ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       ?t'.
       evaluate (xs, env2, s') = (r, t') /\
       state_rel t t' /\
       (opt ⇒
         ∀op n exp arity.
           lookup loc s.code = SOME (arity, exp) ∧
           optimized_code loc arity exp n s'.code op ∧
           op_type op = ty /\
           (∃op1 tt ty r.
             scan_expr ts loc [HD xs] = [(tt, ty, r, SOME op1)] ∧
             ty <> Any /\ op1 <> Noop /\ op_type op1 = op_type op) ⇒
               let (lr, x) = rewrite loc n op acc ts (HD xs) in
                 ?rrr t1 t2.
                 evaluate ([x], env2, s') = (rrr,t1) /\
                 evaluate ([apply_op op (Var acc) (HD xs)],
                   env2, s') = (rrr,t2) /\
                 state_rel t t1 /\
                 state_rel t t2)
Proof
  cheat
QED
*)

Theorem compile_prog_semantics:
   input_condition n prog ∧
   (∀k n cfg prog. co k = ((n,cfg),prog) ⇒ input_condition n prog) ∧
   (∀k. MEM k (MAP FST prog2) ∧ in_ns_2 k ⇒ k < FST(FST (co 0))) ∧
   SND (compile_prog n prog) = prog2 ∧
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start ≠
      ffi$Fail ⇒
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start =
   semantics ffi (fromAList prog2) (state_co compile_prog co) cc start
Proof
  cheat
QED

