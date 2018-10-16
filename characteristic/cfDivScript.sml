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
  get_index hi his hk hks st sts i =
    if i = 0:num then (i,hi,hk,st) else
      let ind = get_index hi his hk hks st sts (i-1) in
        (i, his ind, hks ind, sts ind)`

val repeat_POSTd = store_thm("repeat_POSTd", (* productive version *)
  ``!p fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!n. ?i. n < LENGTH (events i)) /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
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
  \\ fs [ml_translatorTheory.PULL_EXISTS_EXTRA]
  \\ `∀x. ∃env exp h_f h_g ck st''.
            let (i,h_i',h_k',st') = x in
                 SPLIT (st2heap p st') (h_i',h_k') ⇒
                 Hs i h_i' ⇒
                 SPLIT3 (st2heap p st'') (h_f,h_k',h_g) ∧
                 do_opapp [fv; vs i] = SOME (env,exp) ∧ Hs (SUC i) h_f ∧
                 evaluate_ck ck st' env [exp] = (st'',Rval [vs (SUC i)])` by
        fs [FORALL_PROD]
  \\ pop_assum mp_tac
  \\ simp [SKOLEM_THM]
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "envs"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "exps"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "his"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "hks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarararar") (rename_conv "cks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararararar") (rename_conv "sts"))
  \\ strip_tac
  \\ qabbrev_tac `get_i = get_index h_i his h_k hks st sts`
  \\ first_x_assum (qspecl_then
       [`i`,`his (get_i i)`,`hks (get_i i)`,`sts (get_i i)`] (mp_tac o Q.GEN `i`))
  \\ strip_tac
  \\ `∀i. SPLIT (st2heap p (sts (get_i i))) (his (get_i i),hks (get_i i)) /\
          Hs i (his (get_i i))` by cheat
  \\ fs []



  \\ cheat);

val _ = export_theory();
