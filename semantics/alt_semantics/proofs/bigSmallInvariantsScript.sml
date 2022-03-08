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
  evaluate_ctxt ck env s (Craise ()) v (s, Rerr (Rraise v)) ∧

  evaluate_ctxt ck env s (Chandle () pes) v (s, Rval v) ∧

  (evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = SOME (env',e) ∧
   (ck ⇒ s2.clock ≠ 0) ∧
   evaluate ck env' (if ck then s2 with clock := s2.clock - 1 else s2) e bv
      ⇒ evaluate_ctxt ck env s1 (Capp Opapp vs1 () es) v bv) ∧

  (evaluate_list T env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = SOME (env',e) ∧
   s2.clock = 0
      ⇒ evaluate_ctxt T env s1 (Capp Opapp vs1 () es) v
          (s2, Rerr (Rabort Rtimeout_error))) ∧

  (evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = NONE
      ⇒ evaluate_ctxt ck env s1 (Capp Opapp vs1 () es) v
          (s2, Rerr (Rabort Rtype_error))) ∧

  (op ≠ Opapp ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
    SOME ((new_refs, new_ffi) ,res)
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2 with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (op ≠ Opapp ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs, s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) = NONE
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2, Rerr (Rabort Rtype_error))) ∧

  (evaluate_list ck env s es (s', Rerr err)
      ⇒ evaluate_ctxt ck env s (Capp op vs () es) v (s', Rerr err)) ∧

  (do_log lop v e2 = SOME (Exp e') ∧
   evaluate ck env s e' bv
      ⇒ evaluate_ctxt ck env s (Clog lop () e2) v bv) ∧

  (do_log lop v e2 = SOME (Val v')
      ⇒ evaluate_ctxt ck env s (Clog lop () e2) v (s, Rval v')) ∧


  (do_log lop v e2 = NONE
      ⇒ evaluate_ctxt ck env s (Clog lop () e2) v (s, Rerr (Rabort Rtype_error))) ∧

  (do_if v e2 e3 = SOME e' ∧
   evaluate ck env s e' bv
      ⇒ evaluate_ctxt ck env s (Cif () e2 e3) v bv) ∧

  (do_if v e2 e3 = NONE
      ⇒ evaluate_ctxt ck env s (Cif () e2 e3) v (s, Rerr (Rabort Rtype_error))) ∧

  (evaluate_match ck env s v pes err_v bv
      ⇒ evaluate_ctxt ck env s (Cmat () pes err_v) v bv) ∧

  (evaluate_match ck env s v pes err_v bv ∧
   can_pmatch_all env.c s.refs (MAP FST pes) v
      ⇒ evaluate_ctxt ck env s (Cmat_check () pes err_v) v bv) ∧


  (¬can_pmatch_all env.c s.refs (MAP FST pes) v
      ⇒ evaluate_ctxt ck env s (Cmat_check () pes err_v) v
          (s, Rerr (Rabort Rtype_error))) ∧

  (evaluate ck (env with <| v := (nsOptBind n v env.v) |>) s e2 bv
      ⇒ evaluate_ctxt ck env s (Clet n () e2) v bv) ∧

  (do_con_check env.c cn (LENGTH vs + LENGTH es + 1) ∧
   build_conv env.c cn (REVERSE vs' ++ [v] ++ vs) = SOME v' ∧
   evaluate_list ck env s1 es (s2, Rval vs')
      ⇒ evaluate_ctxt ck env s1 (Ccon cn vs () es) v (s2, Rval v')) ∧

  (¬do_con_check env.c cn (LENGTH vs + LENGTH es + 1)
      ⇒ evaluate_ctxt ck env s (Ccon cn vs () es) v (s, Rerr (Rabort Rtype_error))) ∧

  (do_con_check env.c cn (LENGTH vs + LENGTH es + 1) ∧
   evaluate_list ck env s es (s', Rerr err)
      ⇒ evaluate_ctxt ck env s (Ccon cn vs () es) v (s', Rerr err)) ∧

  evaluate_ctxt ck env s (Ctannot () t) v (s, Rval v) ∧

  evaluate_ctxt ck env s (Clannot () l) v (s, Rval v)
End

Inductive evaluate_ctxts:
  evaluate_ctxts ck s [] res (s, res) ∧

  (evaluate_ctxt ck env s1 c v (s2, res) ∧
   evaluate_ctxts ck s2 cs res bv
      ⇒ evaluate_ctxts ck s1 ((c,env)::cs) (Rval v) bv) ∧

  (evaluate_ctxts ck s cs (Rerr err) bv ∧
  ((∀pes. c ≠ Chandle () pes) ∨ (∀v. err ≠ Rraise v))
      ⇒ evaluate_ctxts ck s ((c,env)::cs) (Rerr err) bv) ∧

  (¬can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts ck s cs (Rerr (Rabort Rtype_error)) res2
      ⇒ evaluate_ctxts ck s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2) ∧

  (evaluate_match ck env s v pes v (s', res1) ∧
   can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts ck s' cs res1 res2
      ⇒ evaluate_ctxts ck s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2)
End

Inductive evaluate_state:
  (evaluate ck env (s:'a state with <| ffi := ffi; refs := refs |>) e (st:'a state, res) ∧
  evaluate_ctxts ck st c res bv
      ⇒ evaluate_state ck (env, (refs, ffi), Exp e, c) bv) ∧

  (evaluate_ctxts ck (s with <| ffi := ffi; refs := refs |>) c (Rval v) bv
      ⇒ evaluate_state ck (env, (refs, ffi), Val v, c) bv)
End

val _ = export_theory()
