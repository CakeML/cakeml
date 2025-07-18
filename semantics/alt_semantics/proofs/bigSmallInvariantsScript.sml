(*
  Invariants used in the proof relating the big-step and small-step
  version of the CakeML source semantics.
*)
open HolKernel Parse boolLib bossLib;
open namespaceTheory astTheory semanticPrimitivesTheory
     smallStepTheory bigStepTheory;

val _ = numLib.temp_prefer_num();

val _ = set_grammar_ancestry ["namespace", "ast", "semanticPrimitives",
                              "smallStep", "bigStep"];

val _ = new_theory "bigSmallInvariants"

(* ------ Auxiliary relations for proving big/small step equivalence ------ *)

Inductive evaluate_ctxt:
  evaluate_ctxt ck env s (Craise ()) v (s, Rerr (Rraise v)) ∧

  evaluate_ctxt ck env s (Chandle () pes) v (s, Rval v) ∧

  (evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = SOME (env',e) ∧
   (ck ⇒ s2.clock ≠ 0) ∧
   (opClass op FunApp) ∧
   evaluate ck env' (if ck then s2 with clock := s2.clock - 1 else s2) e bv
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v bv) ∧

  (evaluate_list T env s1 es (s2, Rval vs2) ∧
   do_opapp (REVERSE vs2 ++ [v] ++ vs1) = SOME (env',e) ∧
   s2.clock = 0 ∧
   (opClass op FunApp)
      ⇒ evaluate_ctxt T env s1 (Capp op vs1 () es) v
          (s2, Rerr (Rabort Rtimeout_error))) ∧

  (evaluate_list ck env s1 es (s2, Rval vs2) ∧
   (do_opapp (REVERSE vs2 ++ [v] ++ vs1) = NONE) ∧
   (opClass op FunApp)
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2, Rerr (Rabort Rtype_error))) ∧

  (opClass op Simple ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
    SOME ((new_refs, new_ffi) ,res)
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2 with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (opClass op Icing ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
   SOME ((new_refs, new_ffi) ,vFp) ∧
   s2.fp_state.canOpt ≠ FPScope fpValTree$Opt ∧
   compress_if_bool op vFp = res
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2 with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (opClass op Icing ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
   SOME ((new_refs, new_ffi) ,vFp) ∧
   s2.fp_state.canOpt = FPScope fpValTree$Opt ∧
   do_fprw vFp (s2.fp_state.opts 0) s2.fp_state.rws = NONE ∧
   compress_if_bool op vFp = res
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          ((shift_fp_opts s2) with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (opClass op Icing ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
   SOME ((new_refs, new_ffi) ,vFp) ∧
   s2.fp_state.canOpt = FPScope fpValTree$Opt ∧
   do_fprw vFp (s2.fp_state.opts 0) s2.fp_state.rws = SOME rOpt ∧
   compress_if_bool op rOpt = res
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          ((shift_fp_opts s2) with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (opClass op Reals ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   do_app (s2.refs,s2.ffi) op (REVERSE vs2 ++ [v] ++ vs1) =
   SOME ((new_refs, new_ffi) ,res) ∧
   s2.fp_state.real_sem
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (s2 with <| ffi := new_ffi; refs := new_refs |>, res)) ∧

  (opClass op Reals ∧
   evaluate_list ck env s1 es (s2, Rval vs2) ∧
   ~s2.fp_state.real_sem
      ⇒ evaluate_ctxt ck env s1 (Capp op vs1 () es) v
          (shift_fp_opts s2, Rerr (Rabort Rtype_error))) ∧

  ((~opClass op FunApp) ∧
   (opClass op Reals ⇒ s2.fp_state.real_sem) ∧
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

  evaluate_ctxt ck env s (Clannot () l) v (s, Rval v) ∧

  (oldSc = Strict ⇒
   evaluate_ctxt ck env s (Coptimise oldSc fpopt ()) v (s with fp_state := s.fp_state with canOpt := oldSc,
                                                     Rval (HD (do_fpoptimise fpopt [v])))) ∧

  (oldSc ≠ Strict ⇒
   evaluate_ctxt ck env s (Coptimise oldSc fpopt ()) v (s with fp_state := s.fp_state with canOpt := oldSc,
                                                     Rval (HD (do_fpoptimise fpopt [v]))))
End

Inductive evaluate_ctxts:
  evaluate_ctxts ck s [] res (s, res) ∧

  (evaluate_ctxt ck env s1 c v (s2, res) ∧
   evaluate_ctxts ck s2 cs res bv
      ⇒ evaluate_ctxts ck s1 ((c,env)::cs) (Rval v) bv) ∧

  (evaluate_ctxts ck s cs (Rerr err) bv ∧
  ((∀pes. c ≠ Chandle () pes) ∨ (∀v. err ≠ Rraise v)) ∧
   (∀ oldSc fpopt. c ≠ Coptimise oldSc fpopt ())
      ⇒ evaluate_ctxts ck s ((c,env)::cs) (Rerr err) bv) ∧

  (evaluate_ctxts ck (s with fp_state := s.fp_state with canOpt := oldSc) cs (Rerr err) bv ⇒
   evaluate_ctxts ck s ((Coptimise oldSc fpopt (),env)::cs) (Rerr err) bv) ∧

  (¬can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts ck s cs (Rerr (Rabort Rtype_error)) res2
      ⇒ evaluate_ctxts ck s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2) ∧

  (evaluate_match ck env s v pes v (s', res1) ∧
   can_pmatch_all env.c s.refs (MAP FST pes) v ∧
   evaluate_ctxts ck s' cs res1 res2
      ⇒ evaluate_ctxts ck s ((Chandle () pes,env)::cs) (Rerr (Rraise v)) res2)
End

Inductive evaluate_state:
  (evaluate ck env (s:'a state with clock := clk) e (st:'a state, res) ∧
  evaluate_ctxts ck st c res bv
      ⇒ evaluate_state ck (env, s, Exp e, c) bv) ∧

  (evaluate_ctxts ck (s with clock := clk) c (Rval v) bv
      ⇒ evaluate_state ck (env, s, Val v, c) bv) ∧

  (evaluate_ctxts ck (s with clock := clk) c (Rerr (Rraise v)) bv
      ⇒ evaluate_state ck (env, s, Exn v, c) bv)
End

Definition lift_dec_result_def:
  lift_dec_result mn (Rval env) = Rval (lift_dec_env mn env) ∧
  lift_dec_result mn (Rerr r) = Rerr r
End

Inductive evaluate_dec_ctxt:
  (evaluate_decs ck (env' +++ env +++ benv) s ds (s',r)
    ⇒ evaluate_dec_ctxt ck benv s (Cdmod mn env ds) env'
        (s', lift_dec_result mn (combine_dec_result (env' +++ env) r))) ∧

  (evaluate_decs ck (env' +++ lenv +++ benv) s lds (ls, Rerr err)
    ⇒ evaluate_dec_ctxt ck benv s (CdlocalL lenv lds gds) env' (ls, Rerr err)) ∧

  (evaluate_decs ck (env' +++ lenv +++ benv) s lds (ls, Rval lenv') ∧
   evaluate_decs ck (lenv' +++ env' +++ lenv +++ benv) ls gds (gs, r)
    ⇒ evaluate_dec_ctxt ck benv s (CdlocalL lenv lds gds) env' (gs, r)) ∧

  (evaluate_decs ck (env' +++ genv +++ lenv +++ benv) s gds (gs, r)
    ⇒ evaluate_dec_ctxt ck benv s (CdlocalG lenv genv gds) env'
        (gs, combine_dec_result (env' +++ genv) r))
End

Inductive evaluate_dec_ctxts:
  evaluate_dec_ctxts ck benv s [] r (s, r) ∧

  (evaluate_dec_ctxt ck (collapse_env benv cs) s1 c env (s2, r) ∧
   evaluate_dec_ctxts ck benv s2 cs r res
    ⇒ evaluate_dec_ctxts ck benv s1 (c::cs) (Rval env) res) ∧

  (evaluate_dec_ctxts ck benv s cs (Rerr err) (s, Rerr err))
End

Inductive evaluate_dec_state:
  (evaluate_dec_ctxts ck benv (st with clock := clk) dcs (Rval env) res
    ⇒ evaluate_dec_state ck benv (st, Env env, dcs) res) ∧

  (evaluate_dec ck (collapse_env benv dcs) (st with clock := clk) d (st',r) ∧
   evaluate_dec_ctxts ck benv st' dcs r res
    ⇒ evaluate_dec_state ck benv (st, Decl d, dcs) res) ∧

  (evaluate_state ck (env, st, ev, cs) (st', Rerr err)
    ⇒ evaluate_dec_state ck benv (st, ExpVal env ev cs locs pat, dcs) (st', Rerr err)) ∧

  (evaluate_state ck (env, st, ev, cs) (st', Rval v) ∧
   (ALL_DISTINCT (pat_bindings pats []) ⇒
      pmatch (collapse_env benv dcs).c st'.refs pats v [] = Match_type_error)
    ⇒ evaluate_dec_state ck benv (st, ExpVal env ev cs locs pats, dcs)
        (st', Rerr (Rabort Rtype_error))) ∧

  (evaluate_state ck (env, st, ev, cs) (st', Rval v) ∧
   ALL_DISTINCT (pat_bindings pats []) ∧
   pmatch (collapse_env benv dcs).c st'.refs pats v [] = No_match
    ⇒ evaluate_dec_state ck benv (st, ExpVal env ev cs locs pats, dcs)
        (st', Rerr (Rraise bind_exn_v))) ∧

  (evaluate_state ck (env, st, ev, cs) (st', Rval v) ∧
   ALL_DISTINCT (pat_bindings pats []) ∧
   pmatch (collapse_env benv dcs).c st'.refs pats v [] = Match new_vals ∧
   evaluate_dec_ctxts ck benv st' dcs
    (Rval <| v := alist_to_ns new_vals; c := nsEmpty |>) res
    ⇒ evaluate_dec_state ck benv (st, ExpVal env ev cs locs pats, dcs) res)
End


val _ = export_theory()
