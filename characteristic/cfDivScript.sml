open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTheory

val _ = new_theory "cfDiv";

val POSTd_eq = store_thm("POSTd_eq",
  ``POSTd Q r h <=> ?io1. r = Div io1 /\ Q io1 /\ emp h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
  \\ eq_tac \\ rw []);

val app_POSTd = store_thm("app_POSTd",
  ``!p f xvs H Q.
      (?io events (Hs: num -> hprop).
        Q io /\
        H ==>> Hs 0 /\
        (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
        (!i. LENGTH (events i) < LENGTH (events (i+1))) /\
        (!i. app p f xvs (Hs (SUC i)) (POSTd Q) ==>
             app p f xvs (Hs i) (POSTd Q)) /\
        (!i. LPREFIX (fromList (events i)) io)) /\
      LENGTH xvs = 1 /\
      IS_SOME (do_opapp [f; HD xvs])
      ==>
      app p f xvs H (POSTd Q)``,
  rw []
  \\ `?v. xvs = [v]` by (Cases_on `xvs` \\ fs []) \\ rveq
  \\ simp [app_def,app_basic_def,POSTd_eq,PULL_EXISTS]
  \\ rw [emp_def]
  \\ fs [IS_SOME_EXISTS]
  \\ rename [`SOME ee`] \\ PairCases_on `ee` \\ fs []
  \\ qexists_tac `UNIV DIFF h_k`
  \\ qexists_tac `UNIV`
  \\ qexists_tac `io` \\ fs []
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ qsuff_tac `!ck. ?st1. evaluate_ck ck st ee0 [ee1] =
                             (st1,Rerr (Rabort Rtimeout_error))`
  THEN1 cheat
  \\ rw []
  \\ cheat);


(* new attempt *)

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_translatorLib.ml_prog_update (ml_progLib.add_prog tm I) end

val _ = (append_prog o cfTacticsLib.process_topdecs)
  `fun repeat f x = repeat f (f x);`

val st = ml_translatorLib.get_ml_prog_state ();

val repeat_v = fetch "-" "repeat_v_def"

val env = repeat_v |> concl |> rand |> rator |> rator |> rand

val repeat_POSTd = store_thm("repeat_POSTd",
  ``!p fv xv H Q.
      (?step P.
         !v events v1 io_events1.
           step v = (v1,io_events1) ==>
           (app p fv [v] (P * one (FFI_full events))
                         (POSTv v'. &(v' = v1) * P *
                                    one (FFI_full (events ++ io_events1)))))
      ==>
      app p repeat_v [fv; xv] H (POSTd Q)``,
  cheat);

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

val repeat_POSTd = store_thm("repeat_POSTd", (* productive version *)
  ``!p fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
         (!n. ?i. n < LENGTH (events i)) /\
         (!i. LPREFIX (fromList (events i)) io) /\ Q io)
      ==>
      app p repeat_v [fv; xv] H (POSTd Q)``,
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
  \\ cheat);

val _ = export_theory();
