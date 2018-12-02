(*
  Defines the repeat function and the corresponding lemma used to prove
  non-termination of programs in cf.
*)
open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTacticsLib cfTheory
open std_preludeTheory;

val _ = new_theory "cfDiv";

val _ = ml_translatorLib.translation_extends "std_prelude";

val POSTd_eq = store_thm("POSTd_eq",
  ``$POSTd Q r h <=> ?io1. r = Div io1 /\ Q io1 /\ emp h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
  \\ eq_tac \\ rw []);

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_translatorLib.ml_prog_update (ml_progLib.add_prog tm I) end

val _ = (append_prog o cfTacticsLib.process_topdecs)
  `fun repeat f x = repeat f (f x);`

val st = ml_translatorLib.get_ml_prog_state ();

val repeat_v = fetch "-" "repeat_v_def"

val POSTv_eq = store_thm("POSTv_eq",
  ``$POSTv Q r h <=> ?v. r = Val v /\ Q v h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]);

fun rename_conv s tm =
  let
    val (v,body) = dest_abs tm
  in ALPHA_CONV (mk_var(s,type_of v)) tm end;

val get_index_def = Define `
  get_index st states i = if i = 0:num then (i,st) else
                            (i, states (get_index st states (i-1)))`

val FFI_full_IN_st2heap_IMP = store_thm("FFI_full_IN_st2heap_IMP",
  ``FFI_full io ∈ st2heap p s ==> s.ffi.io_events = io``,
  strip_tac \\ fs [st2heap_def]
  THEN1 fs [store2heap_def,FFI_full_NOT_IN_store2heap_aux]
  \\ Cases_on `p` \\ fs [ffi2heap_def]
  \\ Cases_on `parts_ok s.ffi (q,r)` \\ fs []);

val lprefix_lub_0 = store_thm("lprefix_lub_0",
  ``events 0 ≼ events 1 /\
    lprefix_lub (IMAGE (fromList ∘ events) UNIV) io ==>
    lprefix_lub (IMAGE (λi. fromList (events (i + 1:num))) UNIV) io``,
  rpt strip_tac
  \\ fs [lprefix_lub_def]
  \\ rpt strip_tac
  THEN1
   (qpat_x_assum `!ll. _ ==> LPREFIX ll io` (qspec_then `ll` mp_tac)
    \\ strip_tac \\ first_assum match_mp_tac
    \\ qexists_tac `i + 1` \\ rw [])
  \\ qpat_x_assum `!ub. _ ==> LPREFIX io ub` (qspec_then `ub` mp_tac)
  \\ strip_tac \\ first_assum match_mp_tac
  \\ rpt strip_tac
  \\ reverse (Cases_on `x`)
  THEN1
   (qpat_x_assum `!ll. _ ==> LPREFIX ll ub` (qspec_then `ll` mp_tac)
    \\ strip_tac \\ first_assum match_mp_tac
    \\ qexists_tac `n`
    \\ rw [ADD1])
  \\ rw [] \\ match_mp_tac (GEN_ALL LPREFIX_TRANS)
  \\ qexists_tac `fromList (events 1)`
  \\ strip_tac
  THEN1 rw [LPREFIX_def, from_toList]
  \\ qpat_x_assum `!ll. _ ==> LPREFIX ll ub` (qspec_then `fromList (events 1)` mp_tac)
  \\ rpt strip_tac
  \\ `LPREFIX (fromList (events 1)) ub` by
   (first_assum match_mp_tac
   \\ qexists_tac `0` \\ rw []));

val evaluate_IMP_io_events_mono = prove(
  ``evaluate s e exp = (t,res) ==> io_events_mono s.ffi t.ffi``,
  metis_tac [evaluatePropsTheory.evaluate_io_events_mono,FST]);

val repeat_POSTd = store_thm("repeat_POSTd", (* productive version *)
  ``!p fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p repeat_v [fv; xv] H ($POSTd Q)``,
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [repeat_v,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,terminationTheory.evaluate_def,PULL_EXISTS,
         cfStoreTheory.st2heap_clock]
  \\ `SPLIT3 (st2heap p st) (h_i,h_k,EMPTY)` by fs [SPLIT3_def,SPLIT_def]
  \\ asm_exists_tac \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rpt strip_tac
  \\ rename [`SPLIT (st2heap p st1) (h_j,h_l)`]
  \\ qexists_tac `Div io`
  \\ fs [POSTd_eq] \\ fs [emp_def]
  \\ qexists_tac `UNIV DIFF h_l`
  \\ qexists_tac `UNIV`
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ fs [app_def,app_basic_def,POSTv_eq,PULL_EXISTS]
  \\ fs [evaluate_to_heap_def,PULL_EXISTS,cond_STAR]
  \\ qabbrev_tac `assert_Hs = \i st.
                    ?h_i h_k. SPLIT (st2heap p st) (h_i,h_k) /\ Hs i h_i`
  \\ `!i st0.
        assert_Hs i st0 ==>
        ?env exp ck st1.
          assert_Hs (i+1) st1 /\
          do_opapp [fv; vs i] = SOME (env,exp) /\
          evaluate_ck ck st0 env [exp] = (st1,Rval [vs (i+1)]) /\
          st1.clock = 0` by
   (fs [Abbr`assert_Hs`,PULL_EXISTS] \\ rpt strip_tac
    \\ first_assum drule \\ disch_then drule
    \\ strip_tac \\ fs [ADD1]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_set_clock
    \\ disch_then (qspec_then `0` mp_tac) \\ strip_tac \\ fs []
    \\ qexists_tac `ck1` \\ fs [cfStoreTheory.st2heap_clock]
    \\ rename [`SPLIT3 (st2heap p st4) (h1,h2,h3)`]
    \\ qexists_tac `h1` \\ fs []
    \\ qexists_tac `h2 UNION h3` \\ fs []
    \\ fs [SPLIT3_def,SPLIT_def,IN_DISJOINT,AC UNION_COMM UNION_ASSOC]
    \\ metis_tac [])
  \\ `!x. ?ck st1. let (i,st0) = x in
            assert_Hs i st0 ==>
            ?env exp.
              assert_Hs (i+1) st1 /\
              do_opapp [fv; vs i] = SOME (env,exp) /\
              evaluate_ck ck st0 env [exp] = (st1,Rval [vs (i+1)]) /\
              st1.clock = 0` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ simp [SKOLEM_THM]
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "clocks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "states"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "i"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "st0"))
  \\ strip_tac
  \\ qabbrev_tac `get_i = get_index st1 states`
  \\ qabbrev_tac `cks = clocks o get_i`
  \\ qabbrev_tac `sts = \i.
                    if i = 0 then st1 else states (get_index st1 states (i-1))`
  \\ `∀i.
        ∃env exp.
            do_opapp [fv; vs i] = SOME (env,exp) ∧
            evaluate_ck (cks i) (sts i) env [exp] =
            (sts (i+1),Rval [vs (i + 1)]) ∧
            (sts (i+1)).clock = 0 ∧
            assert_Hs i (sts i) ∧ assert_Hs (i+1) (sts (i+1))` by
    (Induct THEN1
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ `assert_Hs 0 st1` by
         (fs [Abbr`assert_Hs`] \\ asm_exists_tac \\ fs [SEP_IMP_def])
       \\ fs [] \\ once_rewrite_tac [get_index_def] \\ fs []
       \\ first_x_assum drule \\ strip_tac \\ fs [])
     \\ fs [ADD1]
     \\ first_x_assum drule
     \\ strip_tac \\ fs []
     \\ `(states (i + 1,sts (i + 1))) = sts (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `clocks (i + 1,sts (i + 1)) = cks (i+1)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ fs [])
  \\ qexists_tac `\i. sts (i+1)`
  \\ qexists_tac `\i. SUM (GENLIST cks (SUC i)) + 3 * i + 1`
  \\ fs []
  \\ conj_tac
  THEN1 (rewrite_tac [GSYM ADD1,GENLIST] \\ fs [SNOC_APPEND,SUM_APPEND])
  \\ conj_tac
  THEN1
   (`st1 = sts 0` by fs[Abbr`sts`]
    \\ fs [] \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ simp [PULL_FORALL]
    \\ qid_spec_tac `vs`
    \\ qid_spec_tac `cks`
    \\ qid_spec_tac `sts`
    \\ qid_spec_tac `assert_Hs`
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on `i` \\ rw []
    THEN1
     (fs [evaluate_ck_def,terminationTheory.evaluate_def]
      \\ pop_assum (qspec_then `0` strip_assume_tac)
      \\ fs [evaluateTheory.dec_clock_def,namespaceTheory.nsOptBind_def,
             build_rec_env_def]
      \\ simp [do_opapp_def,EVAL ``find_recfun "repeat" [("repeat","f",x)]``]
      \\ drule evaluatePropsTheory.evaluate_add_to_clock
      \\ disch_then (qspec_then `1` mp_tac) \\ fs []
      \\ fs [terminationTheory.evaluate_def]
      \\ fs [state_component_equality])
    \\ first_assum (qspec_then `0` strip_assume_tac)
    \\ simp [evaluate_ck_def,terminationTheory.evaluate_def]
    \\ simp [evaluateTheory.dec_clock_def,namespaceTheory.nsOptBind_def,
             build_rec_env_def] \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_add_to_clock
    \\ once_rewrite_tac [GENLIST_CONS] \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(_ with clock := cks 0 + pppp : num)`
    \\ disch_then (qspec_then `pppp` mp_tac) \\ fs [Abbr `pppp`]
    \\ disch_then kall_tac
    \\ simp [do_opapp_def,EVAL ``find_recfun "repeat" [("repeat","f",x)]``]
    \\ rewrite_tac [MULT_CLAUSES]
    \\ fs []
    \\ first_x_assum (qspecl_then [`assert_Hs o SUC`,
                                   `sts o SUC`,`cks o SUC`,`vs o SUC`] mp_tac)
    \\ impl_tac THEN1
     (fs [ADD1] \\ strip_tac
      \\ first_x_assum (qspec_then `i+1` mp_tac)
      \\ fs [] \\ strip_tac \\ fs [])
    \\ fs [ADD1]
    \\ strip_tac
    \\ once_rewrite_tac [terminationTheory.evaluate_def]
    \\ fs [])
  \\ `!i s. assert_Hs i s ==> s.ffi.io_events = events i` by
     (fs [Abbr`assert_Hs`] \\ rw []
      \\ last_x_assum (qspec_then `i` (mp_tac o ONCE_REWRITE_RULE [STAR_COMM]))
      \\ rw [] \\ fs [one_STAR,SPLIT_def] \\ fs [EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ fs [] \\ metis_tac [])
  \\ `!i. (sts i).ffi.io_events = events i` by metis_tac []
  \\ fs []
  \\ match_mp_tac lprefix_lub_0 \\ fs []
  \\ qpat_x_assum `!i. ?y. _` (qspec_then `0` mp_tac)
  \\ strip_tac
  \\ qpat_x_assum `!i. _` (assume_tac o GSYM) \\ fs []
  \\ fs [evaluate_ck_def]
  \\ imp_res_tac evaluate_IMP_io_events_mono
  \\ fs [evaluatePropsTheory.io_events_mono_def]);

(*

(* example: a simple pure non-terminating loop *)

val _ = (append_prog o cfTacticsLib.process_topdecs) `
  fun loop x = repeat (fn y => y) x`

val st = ml_translatorLib.get_ml_prog_state ();

val loop_spec = store_thm("loop_spec",
  ``!xv.
      app (p:'ffi ffi_proj) ^(fetch_v "loop" st) [xv]
        (one (FFI_full [])) (POSTd io. io = [||])``,
  xcf "loop" st
  \\ xfun_spec `f`
    `!xv.
       app p f [xv]
         (one (FFI_full [])) (POSTv v. cond (v = xv) * one (FFI_full []))`
  THEN1 (strip_tac \\ xapp \\ xvar \\ xsimpl)
  \\ xapp
  \\ qexists_tac `\n. one (FFI_full [])`
  \\ qexists_tac `\n. []`
  \\ qexists_tac `\n. xv`
  \\ qexists_tac `[||]`
  \\ rpt strip_tac \\ xsimpl
  THEN1 (qexists_tac `emp` \\ rw [SEP_CLAUSES])
  \\ rw [lprefix_lub_def]);

(* example: conditional terminating *)

val _ = (append_prog o cfTacticsLib.process_topdecs) `
  exception Terminate
  fun condLoop n = repeat (if n = 0 then raise Terminate else n - 1) n`

val st = ml_translatorLib.get_ml_prog_state ();

val condLoop_spec = store_thm("condLoop_spec",
  ``!n nv.
      INT n nv ==>
      app (p:'ffi ffi_proj) ^(fetch_v "condLoop" st) [nv]
        (one (FFI_full []))
        (POSTed (\e. cond (0 <= n)) (\io. io = [||] /\ n < 0))``,
  cheat);

(* example: the yes program *)

val _ = (append_prog o cfTacticsLib.process_topdecs)
  `fun yes c = repeat (fn c => (putChar c; c)) c;`

val st = ml_translatorLib.get_ml_prog_state ();

val yes_spec = store_thm("yes_spec",
  ``!xv.
      app (p:'ffi ffi_proj) ^(fetch_v "yes" st) [xv]
        emp (POSTd io. T)``,
  xcf "yes" st
  \\ cheat);

*)

val _ = export_theory();
