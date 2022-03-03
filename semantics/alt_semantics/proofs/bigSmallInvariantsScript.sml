(*
  Invariants used in the proof relating the big-step and small-step
  version of the CakeML source semantics.
*)
open HolKernel Parse boolLib bossLib;
open libTheory namespaceTheory astTheory semanticPrimitivesTheory
     smallStepTheory bigStepTheory;

val _ = numLib.prefer_num();

val _ = new_theory "bigSmallInvariants"

(* ------ Auxiliary relations for proving big/small step equivalence ------ *)

Inductive evaluate_ctxt:
  evaluate_ctxt env s (Craise ()) v (s, Rerr (Rraise v)) ∧

  evaluate_ctxt env s (Chandle () pes) v (s, Rval v) ∧

  (evaluate_list F env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = SOME (env',e) ∧
   evaluate F env' s2 e bv
      ⇒ evaluate_ctxt env s1 (Capp Opapp vs1 () es) v bv) ∧

  (evaluate_list F env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = NONE
      ⇒ evaluate_ctxt env s1 (Capp Opapp vs1 () es) v
          (s2, Rerr (Rabort Rtype_error))) ∧

  (op ≠ Opapp ∧
   evaluate_list F env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
    SOME ((new_refs, new_ffi) ,res)
      ⇒ evaluate_ctxt env s1 (Capp op vs1 () es) v
          (s2 with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (op ≠ Opapp ∧
   evaluate_list F env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs, s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) = NONE
      ⇒ evaluate_ctxt env s1 (Capp op vs1 () es) v
          (s2, Rerr (Rabort Rtype_error))) ∧

  (evaluate_list F env s es (s', Rerr err)
      ⇒ evaluate_ctxt env s (Capp op vs () es) v (s', Rerr err)) ∧

  (do_log lop v e2 = SOME (Exp e') ∧
   evaluate F env s e' bv
      ⇒ evaluate_ctxt env s (Clog lop () e2) v bv) ∧

  (do_log lop v e2 = SOME (Val v')
      ⇒ evaluate_ctxt env s (Clog lop () e2) v (s, Rval v')) ∧


  (do_log lop v e2 = NONE
      ⇒ evaluate_ctxt env s (Clog lop () e2) v (s, Rerr (Rabort Rtype_error))) ∧

  (do_if v e2 e3 = SOME e' ∧
   evaluate F env s e' bv
      ⇒ evaluate_ctxt env s (Cif () e2 e3) v bv) ∧

  (do_if v e2 e3 = NONE
      ⇒ evaluate_ctxt env s (Cif () e2 e3) v (s, Rerr (Rabort Rtype_error))) ∧

  (evaluate_match F env s v pes err_v bv
      ⇒ evaluate_ctxt env s (Cmat () pes err_v) v bv) ∧

  (evaluate_match F env s v pes err_v bv ∧
   can_pmatch_all env.c s.refs (MAP FST pes) v
      ⇒ evaluate_ctxt env s (Cmat_check () pes err_v) v bv) ∧


  (¬can_pmatch_all env.c s.refs (MAP FST pes) v
      ⇒ evaluate_ctxt env s (Cmat_check () pes err_v) v
          (s, Rerr (Rabort Rtype_error))) ∧

  (evaluate F (env with <| v := (nsOptBind n v env.v) |>) s e2 bv
      ⇒ evaluate_ctxt env s (Clet n () e2) v bv) ∧

  (do_con_check env.c cn (LENGTH vs + LENGTH es + 1) ∧
   build_conv env.c cn (REVERSE vs' ++ [v] ++ vs) = SOME v' ∧
   evaluate_list F env s1 es (s2, Rval vs')
      ⇒ evaluate_ctxt env s1 (Ccon cn vs () es) v (s2, Rval v')) ∧

  (¬do_con_check env.c cn (LENGTH vs + LENGTH es + 1)
      ⇒ evaluate_ctxt env s (Ccon cn vs () es) v (s, Rerr (Rabort Rtype_error))) ∧

  (do_con_check env.c cn (LENGTH vs + LENGTH es + 1) ∧
   evaluate_list F env s es (s', Rerr err)
      ⇒ evaluate_ctxt env s (Ccon cn vs () es) v (s', Rerr err)) ∧

  evaluate_ctxt env s (Ctannot () t) v (s, Rval v) ∧

  evaluate_ctxt env s (Clannot () l) v (s, Rval v)
End

Inductive evaluate_ctxts:
  evaluate_ctxts s [] res (s, res) ∧

  (evaluate_ctxt env s1 c v (s2, res) ∧
   evaluate_ctxts s2 cs res bv
      ⇒ evaluate_ctxts s1 ((c,env)::cs) (Rval v) bv) ∧

  (evaluate_ctxts s cs (Rerr err) bv ∧
  ((∀pes. c ≠ Chandle () pes) ∨ (∀v. err ≠ Rraise v))
      ⇒ evaluate_ctxts s ((c,env)::cs) (Rerr err) bv) ∧

  (¬can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts s cs (Rerr (Rabort Rtype_error)) res2
      ⇒ evaluate_ctxts s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2) ∧

  (evaluate_match F env s v pes v (s', res1) ∧
   can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts s' cs res1 res2
      ⇒ evaluate_ctxts s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2)
End

Inductive evaluate_state:
 (evaluate F env <| ffi := ffi; clock := 0; refs := refs; next_type_stamp := 0;
                    next_exn_stamp := 0; eval_state := NONE |> e (st, res) ∧
  evaluate_ctxts st c res bv
      ⇒ evaluate_state (env, (refs, ffi), Exp e, c) bv) ∧

 (evaluate_ctxts <| ffi := ffi; clock := 0; refs := refs; next_type_stamp := 0;
                    next_exn_stamp := 0; eval_state := NONE |> c (Rval v) bv
      ⇒ evaluate_state (env, (refs, ffi), Val v, c) bv)
End

val _ = export_theory()
