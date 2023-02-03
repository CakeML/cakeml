(*
  Correctness proof for loop_remove
*)

open preamble loopLangTheory loopSemTheory
     loopPropsTheory loop_removeTheory

local open wordSemTheory in end

val _ = new_theory"loop_removeProof";

Definition has_code_def:
  has_code (n,funs) code =
    EVERY (\(n,p,b). lookup n code = SOME (p,b)) funs
End

Definition state_rel_def:
  state_rel s t <=>
    ∃c. t = s with code := c ∧
        ∀n params body.
          lookup n s.code = SOME (params, body) ⇒
          syntax_ok body ∧
          ∃init. has_code (comp (n,params,body) init) t.code
End

Definition break_ok_def:
  break_ok Fail = T ∧
  break_ok (Call _ _ _ (SOME (_,p,q,_))) = (break_ok p ∧ break_ok q) ∧
  break_ok (Call NONE _ _ _) = T ∧
  break_ok (Seq p q) =
    (break_ok q ∧ every_prog (\r. r ≠ Break ∧ r ≠ Continue) p) ∧
  break_ok (If _ _ _ p q _) = (break_ok p ∧ break_ok q) ∧
  break_ok _ = F
End

Definition breaks_ok_def:
  breaks_ok (p:'a loopLang$prog,q:'a loopLang$prog) <=> break_ok p ∧ break_ok q
End

val goal =
  ``λ(prog, s). ∀res s1 t p.
    evaluate (prog,s) = (res,s1) ∧ state_rel s t ∧ res ≠ SOME Error ∧
    breaks_ok p ⇒
    (syntax_ok prog ⇒
      ∀cont s q s'.
        comp_with_loop p prog cont s = (q,s') ∧
        has_code s' t.code ∧ break_ok cont ⇒
        ∃t1.
         (let result = evaluate (q,t) in
            state_rel s1 t1 ∧ t1.code = t.code ∧
            case res of
            | NONE => result = evaluate (cont,t1)
            | SOME Break => result = evaluate (FST p,t1)
            | SOME Continue => result = evaluate (SND p,t1)
            | _ => result = (res,t1))) ∧
    (no_Loop prog ⇒
        ∃t1.
         (let result = evaluate (comp_no_loop p prog,t) in
            state_rel s1 t1 ∧ t1.code = t.code ∧
            case res of
            | SOME Continue => result = evaluate (SND p,t1)
            | SOME Break => result = evaluate (FST p,t1)
            | _ => result = (res,t1)))``

local
  val ind_thm = loopSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_Skip:
  ^(get_goal "loopLang$Skip") ∧
  ^(get_goal "loopLang$Fail") ∧
  ^(get_goal "loopLang$Tick")
Proof
  fs [syntax_ok_def,comp_no_loop_def,evaluate_def]
  \\ rw [] \\ fs []
  \\ fs [state_rel_def,call_env_def,dec_clock_def]
  \\ rveq \\ fs [state_component_equality]
  \\ rw [] \\ res_tac
QED

Theorem compile_Continue:
  ^(get_goal "loopLang$Continue") ∧
  ^(get_goal "loopLang$Break")
Proof
  fs [syntax_ok_def,comp_no_loop_def,evaluate_def]
  \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem evaluate_break_ok:
  ∀p t res t1. evaluate (p,t) = (res,t1) ∧ break_ok p ⇒ res ≠ NONE
Proof
  ho_match_mp_tac break_ok_ind \\ rw [] \\ fs [break_ok_def]
  \\ fs [evaluate_def] \\ rveq \\ fs []
  \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw [] \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ every_case_tac \\ gvs []
  \\ rename [‘cut_res _ (evaluate (pp,t))’]
  \\ Cases_on ‘evaluate (pp,t)’ \\ fs [cut_res_def,cut_state_def]
  \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ gvs []
QED

Theorem compile_Mark:
  ^(get_goal "syntax_ok (Mark _)")
Proof
  simp_tac std_ss [evaluate_def,syntax_ok_def]
  \\ full_simp_tac std_ss [no_Loop_def,every_prog_def]
  \\ full_simp_tac std_ss [GSYM no_Loop_def,comp_with_loop_def]
  \\ rw [] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on ‘res’ \\ fs [evaluate_def,comp_no_loop_def]
  \\ Cases_on ‘x’ \\ fs [evaluate_def,comp_no_loop_def]
  \\ Cases_on ‘p'’ \\ fs []
  \\ rename [‘_ = evaluate (qq,_)’]
  \\ fs [breaks_ok_def]
  \\ Cases_on ‘evaluate (qq,t1)’ \\ fs [] \\ rw []
  \\ imp_res_tac evaluate_break_ok \\ fs []
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return") ∧
  ^(get_goal "loopLang$Raise")
Proof
  fs [syntax_ok_def,comp_no_loop_def,evaluate_def]
  \\ rw [] \\ fs [CaseEq"option"] \\ rveq \\ fs []
  \\ fs [state_rel_def,call_env_def,state_component_equality]
  \\ metis_tac []
QED

Theorem comp_with_loop_has_code:
  ∀p prog cont s0 q s1 code.
     comp_with_loop p prog cont s0 = (q,s1) ∧ has_code s1 code ⇒ has_code s0 code
Proof
  ho_match_mp_tac comp_with_loop_ind \\ rpt strip_tac
  \\ fs [comp_with_loop_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ res_tac \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on ‘s0’
  \\ fs [store_cont_def]
  \\ rveq \\ fs [] \\ fs [has_code_def]
  \\ fs [CaseEq"option"]
  \\ rveq \\ fs []
  \\ fs [has_code_def]
  \\ PairCases_on ‘v’ \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem helper_call_lemma:
  ∀t live_in:num_set.
    domain live_in ⊆ domain t.locals ⇒
    ∃vals. get_vars (MAP FST (toAList live_in)) t = SOME vals ∧
           LENGTH vals = LENGTH (toAList live_in) ∧
           fromAList (ZIP (MAP FST (toAList live_in),vals)) =
           inter t.locals live_in
Proof
  rw []
  \\ ‘∀i x. MEM (i,x) (toAList live_in) ⇔ lookup i live_in = SOME x’ by fs [MEM_toAList]
  \\ ‘domain live_in = set (MAP FST (toAList live_in))’
       by fs [EXTENSION,domain_lookup,MEM_MAP,EXISTS_PROD]
  \\ fs [spt_eq_thm,wf_inter,wf_fromAList,lookup_fromAList,lookup_inter_alt]
  \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ rename [‘MAP FST xs’]
  \\ Induct_on ‘xs’ \\ fs [get_vars_def,FORALL_PROD]
  \\ rw [] \\ fs [domain_lookup] \\ rw [] \\ fs []
QED

Theorem break_ok_no_Break_Continue:
  ∀p. break_ok p ⇒ every_prog (\r. r ≠ Break ∧ r ≠ Continue) p
Proof
  ho_match_mp_tac break_ok_ind
  \\ fs [break_ok_def,every_prog_def]
QED

Theorem compile_Loop:
  ^(get_goal "loopLang$Loop")
Proof
  fs [no_Loop_def,every_prog_def]
  \\ fs [GSYM no_Loop_def]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
  \\ once_rewrite_tac [evaluate_def]
  \\ reverse TOP_CASE_TAC
  \\ reverse TOP_CASE_TAC
  THEN1
   (strip_tac \\ rveq \\ fs []
    \\ fs [comp_with_loop_def]
    \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def] \\ rveq \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs [evaluate_def]
    \\ ‘s.clock = t.clock’ by fs [state_rel_def] \\ fs []
    \\ ‘s.locals = t.locals’ by fs [state_rel_def] \\ fs []
    \\ drule helper_call_lemma \\ strip_tac \\ fs [find_code_def]
    \\ fs [has_code_def] \\ fs [state_rel_def,state_component_equality]
    \\ rw [] \\ res_tac)
  \\ TOP_CASE_TAC \\ fs [syntax_ok_def] \\ rfs []
  \\ rename [‘evaluate _ = (res1,_)’]
  \\ Cases_on ‘res1’ \\ fs []
  \\ Cases_on ‘x = Error’ \\ fs []
  \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def] \\ rveq \\ fs []
  \\ qpat_x_assum ‘x = Contine ⇒ _’ assume_tac
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ pop_assum (qpat_assum ‘comp_with_loop _ _ _ _ = _’ o mp_then Any mp_tac)
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ ‘state_rel (dec_clock (s with locals := inter s.locals live_in))
                (dec_clock (t with locals := inter t.locals live_in))’ by
        (fs [state_rel_def,dec_clock_def,state_component_equality]
         \\ metis_tac [])
  \\ first_x_assum drule
  \\ simp [dec_clock_def]
  \\ fs [comp_with_loop_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ qmatch_asmsub_abbrev_tac ‘comp_with_loop (cc,new_cont) body Fail s3’
  \\ ‘breaks_ok (cc,new_cont)’ by
    (fs [breaks_ok_def,break_ok_def,Abbr‘new_cont’,Abbr‘cc’]
     \\ Cases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def])
  \\ disch_then drule
  \\ strip_tac
  \\ rfs [GSYM PULL_FORALL]
  \\ qpat_x_assum ‘no_Loop _ ⇒ _’ kall_tac
  \\ pop_assum drule
  \\ impl_tac
  THEN1 (rveq \\ fs [] \\ unabbrev_all_tac \\ fs [break_ok_def] \\ fs [has_code_def])
  \\ strip_tac
  \\ rveq \\ fs []
  \\ fs [Abbr‘new_cont’]
  \\ strip_tac
  \\ fs [has_code_def]
  \\ once_rewrite_tac [evaluate_def]
  \\ fs [find_code_def]
  \\ ‘s.locals = t.locals ∧ s.clock = t.clock’ by fs [state_rel_def] \\ fs []
  \\ drule helper_call_lemma \\ strip_tac \\ fs [dec_clock_def]
  \\ Cases_on ‘x’ \\ fs [] \\ rveq \\ fs []
  THEN1
   (Cases_on ‘domain live_out ⊆ domain r'.locals’ \\ fs []
    \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ ‘r'.locals = t1.locals’ by fs [state_rel_def] \\ fs []
    \\ drule helper_call_lemma \\ strip_tac
    \\ imp_res_tac comp_with_loop_has_code
    \\ fs [has_code_def] \\ pop_assum drule
    \\ strip_tac \\ fs [Abbr‘s3’,has_code_def]
    \\ simp [evaluate_def,find_code_def]
    \\ rename [‘state_rel s3 t3’]
    \\ ‘s3.clock = t3.clock’ by fs [state_rel_def]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    THEN1
     (fs [state_rel_def,state_component_equality] \\ rw [] \\ res_tac)
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,t4)’
    \\ qexists_tac ‘t4’ \\ fs [] \\ rw []
    THEN1
     (fs [Abbr‘t4’,dec_clock_def]
      \\ qpat_x_assum ‘state_rel s3 t3’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [state_rel_def] \\ rw [] \\ fs [state_component_equality]
      \\ rw[] \\ res_tac)
    THEN1 fs [Abbr‘t4’,dec_clock_def]
    \\ Cases_on ‘evaluate (cont,t4)’ \\ fs []
    \\ drule evaluate_no_Break_Continue
    \\ imp_res_tac break_ok_no_Break_Continue \\ fs []
    \\ Cases_on ‘q’ \\ fs []
    \\ imp_res_tac evaluate_break_ok \\ fs []
    \\ Cases_on ‘x’ \\ fs [])
  \\ first_x_assum drule
  \\ impl_tac THEN1 fs []
  \\ strip_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ Cases_on ‘res’ \\ fs []
  THEN1
   (fs [breaks_ok_def]
    \\ Cases_on ‘evaluate (cont,t1')’ \\ fs [] \\ rw []
    \\ drule evaluate_no_Break_Continue
    \\ imp_res_tac break_ok_no_Break_Continue \\ fs []
    \\ imp_res_tac evaluate_break_ok \\ fs []
    \\ every_case_tac \\ fs [])
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘p’ \\ fs []
  \\ rename [‘_ = evaluate (qq,_)’]
  \\ fs [breaks_ok_def]
  \\ Cases_on ‘evaluate (qq,t1')’ \\ fs [] \\ rw []
  \\ drule evaluate_no_Break_Continue
  \\ imp_res_tac break_ok_no_Break_Continue \\ fs []
  \\ imp_res_tac evaluate_break_ok \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem comp_no_loop_no_Break_Continue:
  ∀p prog.
    every_prog (λr. r ≠ Break ∧ r ≠ Continue) (FST p) ∧
    every_prog (λr. r ≠ Break ∧ r ≠ Continue) (SND p) ⇒
    every_prog (λr. r ≠ Break ∧ r ≠ Continue) (comp_no_loop p prog)
Proof
  ho_match_mp_tac comp_no_loop_ind \\ rw [] \\ fs []
  \\ fs [comp_no_loop_def,every_prog_def]
  \\ every_case_tac \\ fs []
QED

Theorem comp_with_loop_break_ok:
  ∀p prog cont s q s1.
    comp_with_loop p prog cont s = (q,s1) ∧ break_ok cont ∧ breaks_ok p ⇒ break_ok q
Proof
  ho_match_mp_tac comp_with_loop_ind \\ rw []
  \\ fs [comp_with_loop_def] \\ rveq \\ fs [break_ok_def]
  \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [break_ok_def]
  \\ TRY (match_mp_tac comp_no_loop_no_Break_Continue \\ fs []
          \\ imp_res_tac break_ok_no_Break_Continue \\ fs [])
  \\ Cases_on ‘s’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [break_ok_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [break_ok_def]
  \\ Cases_on ‘ret’ \\ fs [break_ok_def,every_prog_def]
QED

Theorem state_rel_IMP_get_vars:
  ∀s t args vs. state_rel s t ∧ get_vars args s = SOME vs ⇒ get_vars args t = SOME vs
Proof
  strip_tac \\ strip_tac
  \\ Induct_on ‘args’ \\ fs [get_vars_def] \\ rw [] \\ fs []
  \\ ‘t.locals = s.locals’ by fs [state_rel_def] \\ fs []
  \\ fs [CaseEq"option"] \\ rveq \\ fs []
QED

Triviality case_cut_res:
  cut_res x y = (res,s) ⇒
  ∃part1 part2. cut_res x (part1, part2) = (res,s) ∧ y = (part1, part2)
Proof
  Cases_on ‘y’ \\ fs []
QED

Triviality state_rel_IMP_locals:
  state_rel s t ⇒ s.locals = t.locals
Proof
  fs [state_rel_def] \\ rw [] \\ rveq \\ fs []
QED

Triviality state_rel_IMP_clock:
  state_rel s t ⇒ s.clock = t.clock
Proof
  fs [state_rel_def] \\ rw [] \\ rveq \\ fs []
QED

Theorem compile_Call:
  ^(get_goal "syntax_ok (loopLang$Call _ _ _ _)")
Proof
  fs [no_Loop_def,every_prog_def]
  \\ fs [GSYM no_Loop_def]
  \\ reverse (rpt strip_tac)
  THEN1
   (fs [evaluate_def]
    \\ Cases_on ‘get_vars argvars s’ \\ fs []
    \\ Cases_on ‘find_code dest x s.code’ \\ fs []
    \\ rename [‘_ = SOME tt’] \\ PairCases_on ‘tt’ \\ fs []
    \\ drule state_rel_IMP_get_vars
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ rename [‘_ = SOME (new_env,new_prog)’]
    \\ ‘∃s body n funs.
          find_code dest x t.code = SOME (new_env,body) ∧ syntax_ok new_prog ∧
          comp_with_loop (Fail,Fail) new_prog Fail s = (body,n,funs) ∧
          has_code (n,funs) t.code’ by
      (Cases_on ‘dest’ \\ fs [find_code_def]
       \\ qpat_x_assum ‘_ = (_,_)’ kall_tac
       \\ fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"bool",CaseEq"prod"]
       \\ rveq \\ fs [] \\ fs [state_rel_def] \\ rveq \\ fs []
       \\ first_x_assum drule
       \\ strip_tac \\ fs []
       \\ fs [comp_def] \\ pairarg_tac \\ fs []
       \\ qexists_tac ‘init’ \\ fs [has_code_def])
    \\ simp [comp_no_loop_def,evaluate_def]
    \\ Cases_on ‘ret’ \\ fs []
    THEN1
     (Cases_on ‘handler’ \\ fs []
      \\ ‘t.clock = s.clock’ by fs [state_rel_def] \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
      THEN1
       (fs [state_rel_def,state_component_equality] \\ rw [] \\ res_tac)
      \\ ‘state_rel (dec_clock s with locals := new_env)
                   (dec_clock t with locals := new_env)’ by
        (qpat_x_assum ‘state_rel s t’ mp_tac \\ rpt (pop_assum kall_tac)
         \\ fs [state_rel_def,state_component_equality,dec_clock_def]
         \\ rw [] \\ res_tac)
      \\ ‘breaks_ok (Fail:'a loopLang$prog,Fail:'a loopLang$prog) ∧
          break_ok (Fail:'a loopLang$prog)’ by EVAL_TAC
      \\ fs [CaseEq"prod",CaseEq"result",CaseEq"option"] \\ rveq \\ fs []
      \\ first_x_assum drule \\ disch_then drule \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ disch_then drule \\ fs [dec_clock_def] \\ fs [])
    \\ PairCases_on ‘x'’ \\ fs []
    \\ rename [‘cut_res live_in (NONE,_)’]
    \\ qpat_x_assum ‘_ = (res,s1)’ mp_tac
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC THEN1
     (strip_tac \\ rveq \\ fs []
      \\ fs [cut_res_def,CaseEq"option",CaseEq"prod",cut_state_def] \\ rveq \\ fs []
      \\ fs [CaseEq"bool"] \\ rveq \\ fs []
      \\ ‘s.clock = t.clock ∧ t.locals = s.locals’ by fs [state_rel_def]
      \\ qexists_tac ‘t with locals := LN’ \\ fs []
      \\ fs [state_rel_def,state_component_equality]
      \\ rw [] \\ res_tac \\ fs [])
    \\ fs []
    \\ rename [‘cut_res live_in (NONE,s) = (NONE,r)’]
    \\ qpat_abbrev_tac ‘ttt = _ live_in (NONE,_)’
    \\ ‘∃tr. ttt = (NONE,tr) ∧ state_rel r tr ∧ tr.code = t.code’ by
     (fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool",CaseEq"prod",Abbr‘ttt’]
      \\ rveq \\ fs [state_rel_def,dec_clock_def]
      \\ fs [state_component_equality]
      \\ rpt strip_tac \\ first_x_assum drule \\ simp_tac std_ss [] \\ metis_tac [])
    \\ fs [Abbr‘ttt’]
    \\ TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ last_x_assum (qspecl_then [‘tr with locals := new_env’,‘(Fail,Fail)’] mp_tac)
    \\ impl_tac THEN1
     (fs [breaks_ok_def,break_ok_def]
      \\ reverse conj_tac
      THEN1 (CCONTR_TAC \\ fs [])
      \\ fs [state_rel_def]
      \\ fs [state_component_equality]
      \\ rpt strip_tac \\ first_x_assum drule \\ simp_tac std_ss [] \\ metis_tac [])
    \\ rewrite_tac [GSYM AND_IMP_INTRO]
    \\ disch_then drule
    \\ impl_tac THEN1 fs [break_ok_def]
    \\ strip_tac \\ disch_then kall_tac
    \\ Cases_on ‘q’ \\ fs []
    \\ Cases_on ‘x' = TimeOut’ \\ fs [] THEN1 (rveq \\ fs [])
    \\ Cases_on ‘∃ff. x' = FinalFFI ff’ \\ fs [] THEN1 (rveq \\ fs [] \\ rveq \\ fs [])
    \\ Cases_on ‘handler’ \\ fs [] THEN1
     (Cases_on ‘∃retv. x' = Result retv’ \\ fs [] THEN1
       (rveq \\ fs [] \\ rveq \\ fs [] \\ fs [set_var_def] \\ fs [state_rel_def]
        \\ fs [state_component_equality]
        \\ rpt strip_tac \\ first_x_assum drule \\ simp_tac std_ss [] \\ metis_tac [])
      \\ Cases_on ‘∃exn. x' = Exception exn’ \\ fs [] THEN1
       (rveq \\ fs [] \\ rveq \\ fs [] \\ fs [set_var_def] \\ fs [state_rel_def]
        \\ fs [state_component_equality]
        \\ rpt strip_tac \\ first_x_assum drule \\ simp_tac std_ss [] \\ metis_tac [])
      \\ Cases_on ‘x'’ \\ fs [])
    \\ qabbrev_tac ‘h = x''’ \\ pop_assum kall_tac \\ PairCases_on ‘h’ \\ fs []
    \\ Cases_on ‘∃vret. x' = Result vret’ \\ fs []
    THEN1
     (rveq \\ fs [] \\ drule case_cut_res \\ strip_tac \\ fs []
      \\ rename [‘state_rel r2 t1’]
      \\ qpat_x_assum ‘∀x. _’ mp_tac
      \\ disch_then (qspecl_then [‘set_var x'0 vret (t1 with locals := r.locals)’,‘p’] mp_tac)
      \\ impl_tac THEN1
       (fs [] \\ reverse conj_tac
        THEN1 (CCONTR_TAC \\ fs [cut_res_def])
        \\ fs [set_var_def,state_rel_def] \\ fs [state_component_equality]
        \\ rw [] \\ fs [] \\ res_tac \\ rfs[] \\ asm_exists_tac \\ fs [])
      \\ asm_rewrite_tac [GSYM AND_IMP_INTRO]
      \\ disch_then kall_tac \\ strip_tac
      \\ fs [cut_res_def]
      \\ reverse (Cases_on ‘part1’) \\ fs []
      THEN1
       (Cases_on ‘x'’ \\ rveq \\ fs []
        \\ imp_res_tac state_rel_IMP_locals \\ fs [cut_res_def,set_var_def]
        \\ asm_exists_tac \\ fs []
        \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
        \\ rename [‘cut_res _ (evaluate (r5,t5))’]
        \\ Cases_on ‘evaluate (r5,t5)’
        \\ imp_res_tac evaluate_break_ok \\ fs []
        \\ Cases_on ‘q’ \\ fs [cut_res_def])
      \\ fs [CaseEq"option"] \\ rveq \\ fs []
      \\ fs [cut_state_def,CaseEq"bool"] \\ rveq \\ fs []
      \\ imp_res_tac state_rel_IMP_locals
      \\ imp_res_tac state_rel_IMP_clock \\ fs []
      \\ fs [cut_res_def,cut_state_def]
      \\ fs [set_var_def,dec_clock_def]
      \\ fs [state_rel_def,state_component_equality] \\ rw [] \\ res_tac \\ fs []
      \\ rfs [] \\ asm_exists_tac \\ fs [])
    \\ Cases_on ‘∃vexn. x' = Exception vexn’ \\ fs []
    THEN1
     (rveq \\ fs [] \\ drule case_cut_res \\ strip_tac \\ fs []
      \\ rename [‘evaluate _ = (SOME (Exception vexn),r2)’]
      \\ rename [‘set_var vname vexn (r3 with locals := r.locals)’]
      \\ qpat_x_assum ‘∀x. _’ mp_tac
      \\ rename [‘set_var vname vexn (r2 with locals := r.locals)’]
      \\ disch_then (qspecl_then
           [‘set_var vname vexn (r3 with locals := r.locals)’,‘p’] mp_tac)
      \\ impl_tac THEN1
       (fs [] \\ reverse conj_tac
        THEN1 (CCONTR_TAC \\ fs [cut_res_def])
        \\ fs [set_var_def,state_rel_def] \\ fs [state_component_equality]
        \\ rw [] \\ fs [] \\ res_tac \\ rfs[] \\ asm_exists_tac \\ fs [])
      \\ asm_rewrite_tac [GSYM AND_IMP_INTRO]
      \\ disch_then kall_tac \\ strip_tac
      \\ fs [cut_res_def]
      \\ reverse (Cases_on ‘part1’) \\ fs []
      THEN1
       (Cases_on ‘x'’ \\ rveq \\ fs []
        \\ imp_res_tac state_rel_IMP_locals \\ fs [cut_res_def,set_var_def]
        \\ asm_exists_tac \\ fs []
        \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
        \\ rename [‘cut_res _ (evaluate (r5,_))’]
        \\ Cases_on ‘evaluate (r5,t1)’
        \\ imp_res_tac evaluate_break_ok \\ fs []
        \\ Cases_on ‘q’ \\ fs [cut_res_def])
      \\ fs [CaseEq"option"] \\ rveq \\ fs []
      \\ fs [cut_state_def,CaseEq"bool"] \\ rveq \\ fs []
      \\ imp_res_tac state_rel_IMP_locals
      \\ imp_res_tac state_rel_IMP_clock \\ fs []
      \\ fs [cut_res_def,cut_state_def]
      \\ fs [set_var_def,dec_clock_def]
      \\ fs [state_rel_def,state_component_equality] \\ rw [] \\ res_tac \\ fs []
      \\ rfs [] \\ asm_exists_tac \\ fs [])
    \\ Cases_on ‘x'’ \\ fs [])
  \\ fs [syntax_ok_def]
  \\ Cases_on ‘handler’ \\ fs []
  \\ PairCases_on ‘x’ \\ fs []
  \\ Cases_on ‘ret’
  THEN1 fs [evaluate_def,CaseEq"option",CaseEq"prod"]
  \\ PairCases_on ‘x’ \\ fs []
  \\ fs [evaluate_def]
  \\ Cases_on ‘get_vars argvars s’ \\ fs []
  \\ Cases_on ‘find_code dest x s.code’ \\ fs []
  \\ rename [‘_ = SOME tt’] \\ PairCases_on ‘tt’ \\ fs []
  \\ fs [comp_with_loop_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [CaseEq"prod"]
  \\ rename [‘cut_res x11 (NONE,s) = (vv,s9)’]
  \\ rename [‘_ = SOME (new_env,new_prog)’]
  \\ ‘∃s body n funs.
          find_code dest x t.code = SOME (new_env,body) ∧ syntax_ok new_prog ∧
          comp_with_loop (Fail,Fail) new_prog Fail s = (body,n,funs) ∧
          has_code (n,funs) t.code’ by
      (Cases_on ‘dest’ \\ fs [find_code_def]
       \\ qpat_x_assum ‘_ = (_,_)’ kall_tac
       \\ fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"bool",CaseEq"prod"]
       \\ rveq \\ fs [] \\ fs [state_rel_def] \\ rveq \\ fs []
       \\ first_x_assum drule
       \\ strip_tac \\ fs []
       \\ fs [comp_def] \\ pairarg_tac \\ fs []
       \\ qexists_tac ‘init’ \\ fs [has_code_def])
  \\ reverse (Cases_on ‘vv’) \\ fs [] THEN1
   (imp_res_tac state_rel_IMP_clock \\ fs []
    \\ imp_res_tac state_rel_IMP_locals \\ fs []
    \\ rveq \\ fs [] \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"]
    \\ rveq \\ fs []
    \\ fs [evaluate_def,cut_res_def,cut_state_def]
    \\ drule state_rel_IMP_get_vars
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ fs [state_rel_def,state_component_equality]
    \\ metis_tac [])
  \\ fs [cut_res_def,CaseEq"option",CaseEq"prod",cut_state_def]
  \\ rveq \\ fs []
  \\ imp_res_tac state_rel_IMP_clock \\ fs []
  \\ imp_res_tac state_rel_IMP_locals \\ fs []
  \\ fs [CaseEq"bool",dec_clock_def] \\ rveq \\ fs []
  \\ Cases_on ‘v11 = Error’ \\ fs []
  \\ first_x_assum (qspecl_then
       [‘t with <|locals := new_env; clock := t.clock - 1|>’,‘Fail,Fail’] mp_tac)
  \\ impl_tac THEN1
   (qpat_x_assum ‘state_rel s t’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [breaks_ok_def,break_ok_def,state_rel_def]
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘c’ \\ fs []
    \\ rw [] \\ res_tac)
  \\ strip_tac \\ fs []
  \\ pop_assum kall_tac
  \\ pop_assum drule
  \\ impl_tac THEN1 fs [break_ok_def]
  \\ strip_tac
  \\ qpat_x_assum ‘state_rel s t’ assume_tac
  \\ drule state_rel_IMP_get_vars
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ fs [evaluate_def]
  \\ simp [cut_res_def,cut_state_def,dec_clock_def]
  \\ Cases_on ‘v11’ \\ fs [] \\ rveq \\ fs []
  THEN1
   (Cases_on ‘evaluate (x2,set_var x0' w (st with locals := inter t.locals x11))’ \\ fs []
    \\ rename [‘set_var vvv’]
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ first_x_assum (qspecl_then [
        ‘(set_var vvv w (t1 with locals := inter t.locals x11))’,‘p’] mp_tac)
    \\ impl_tac THEN1
     (fs [set_var_def] \\ qpat_x_assum ‘state_rel st t1’ mp_tac
      \\ rpt (pop_assum kall_tac) \\ fs [state_rel_def] \\ rw [] \\ fs []
      \\ fs [state_component_equality] \\ rw[] \\ res_tac)
    \\ strip_tac \\ fs [] \\ pop_assum kall_tac
    \\ pop_assum drule \\ impl_tac THEN1
     (fs [breaks_ok_def,set_var_def]
      \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def])
    \\ strip_tac
    \\ reverse (Cases_on ‘q’) \\ fs []
    THEN1
     (fs [cut_res_def] \\ rveq \\ fs [] \\ asm_exists_tac \\ fs []
      \\ conj_tac THEN1 fs [set_var_def]
      \\ Cases_on ‘x'’ \\ fs [] \\ rveq \\ fs [cut_res_def]
      \\ Cases_on ‘p’ \\ fs []
      \\ rename [‘_ = evaluate (qq,_)’]
      \\ fs [breaks_ok_def]
      \\ Cases_on ‘evaluate (qq,t1')’ \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_break_ok \\ fs []
      \\ Cases_on ‘q’ \\ fs [cut_res_def])
    \\ fs [cut_res_def,cut_state_def,CaseEq"bool",CaseEq"option"]
    \\ rveq \\ fs []
    THEN1
     (qexists_tac ‘t1' with locals := LN’ \\ fs []
      \\ simp [set_var_def]
      \\ conj_tac THEN1
       (qpat_x_assum ‘state_rel _ _’ mp_tac
        \\ rpt (pop_assum kall_tac) \\ fs [state_rel_def]
        \\ rw [] \\ fs [] \\ fs [state_component_equality]
        \\ rw [] \\ res_tac \\ fs [])
      \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs []
      \\ imp_res_tac comp_with_loop_has_code
      \\ fs [set_var_def,has_code_def,evaluate_def]
      \\ drule helper_call_lemma
      \\ drule state_rel_IMP_get_vars \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac \\ fs []
      \\ imp_res_tac state_rel_IMP_clock
      \\ fs [dec_clock_def,find_code_def,cut_res_def])
    \\ rveq \\ fs [] \\ fs [dec_clock_def]
    \\ qexists_tac ‘(t1' with <|locals := inter r.locals x3; clock := r.clock - 1|>)’
    \\ fs [] \\ simp [set_var_def]
    \\ conj_tac THEN1
     (qpat_x_assum ‘state_rel _ _’ mp_tac \\ rpt (pop_assum kall_tac)
      \\ fs [state_rel_def] \\ rw [] \\ fs [state_component_equality]
      \\ rw [] \\ res_tac \\ fs [])
    \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs []
    \\ imp_res_tac comp_with_loop_has_code
    \\ fs [set_var_def,has_code_def]
    \\ simp [evaluate_def,find_code_def]
    \\ drule helper_call_lemma
    \\ drule state_rel_IMP_get_vars \\ rpt strip_tac
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ imp_res_tac state_rel_IMP_clock \\ fs [dec_clock_def]
    \\ qmatch_goalsub_abbrev_tac ‘_ = xx’ \\ PairCases_on ‘xx’
    \\ fs [] \\ pop_assum (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def] o GSYM)
    \\ pop_assum (assume_tac o GSYM)
    \\ drule evaluate_break_ok \\ fs []
    \\ Cases_on ‘xx0’ \\ fs []
    \\ imp_res_tac break_ok_no_Break_Continue
    \\ imp_res_tac evaluate_no_Break_Continue \\ fs []
    \\ TOP_CASE_TAC \\ fs [cut_res_def])
  THEN1
   (Cases_on ‘evaluate (x1,set_var x0 w (st with locals := inter t.locals x11))’ \\ fs []
    \\ rename [‘set_var vvv’]
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ first_x_assum (qspecl_then [
        ‘(set_var vvv w (t1 with locals := inter t.locals x11))’,‘p’] mp_tac)
    \\ impl_tac THEN1
     (fs [set_var_def] \\ qpat_x_assum ‘state_rel st t1’ mp_tac
      \\ rpt (pop_assum kall_tac) \\ fs [state_rel_def] \\ rw [] \\ fs []
      \\ fs [state_component_equality] \\ rw[] \\ res_tac)
    \\ strip_tac \\ fs [] \\ pop_assum kall_tac
    \\ pop_assum drule \\ impl_tac THEN1
     (fs [breaks_ok_def,set_var_def]
      \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def]
      \\ imp_res_tac comp_with_loop_has_code)
    \\ strip_tac
    \\ reverse (Cases_on ‘q’) \\ fs []
    THEN1
     (fs [cut_res_def] \\ rveq \\ fs [] \\ asm_exists_tac \\ fs []
      \\ conj_tac THEN1 fs [set_var_def]
      \\ Cases_on ‘x'’ \\ fs [] \\ rveq \\ fs [cut_res_def]
      \\ Cases_on ‘p’ \\ fs []
      \\ rename [‘_ = evaluate (qq,_)’]
      \\ fs [breaks_ok_def]
      \\ Cases_on ‘evaluate (qq,t1')’ \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_break_ok \\ fs []
      \\ Cases_on ‘q’ \\ fs [cut_res_def])
    \\ fs [cut_res_def,cut_state_def,CaseEq"bool",CaseEq"option"]
    \\ rveq \\ fs []
    THEN1
     (qexists_tac ‘t1' with locals := LN’ \\ fs []
      \\ simp [set_var_def]
      \\ conj_tac THEN1
       (qpat_x_assum ‘state_rel _ _’ mp_tac
        \\ rpt (pop_assum kall_tac) \\ fs [state_rel_def]
        \\ rw [] \\ fs [] \\ fs [state_component_equality]
        \\ rw [] \\ res_tac \\ fs [])
      \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs []
      \\ imp_res_tac comp_with_loop_has_code
      \\ fs [set_var_def,has_code_def,evaluate_def]
      \\ drule helper_call_lemma
      \\ drule state_rel_IMP_get_vars \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac \\ fs []
      \\ imp_res_tac state_rel_IMP_clock
      \\ fs [dec_clock_def,find_code_def,cut_res_def])
    \\ rveq \\ fs [] \\ fs [dec_clock_def]
    \\ qexists_tac ‘(t1' with <|locals := inter r.locals x3; clock := r.clock - 1|>)’
    \\ fs [] \\ simp [set_var_def]
    \\ conj_tac THEN1
     (qpat_x_assum ‘state_rel _ _’ mp_tac \\ rpt (pop_assum kall_tac)
      \\ fs [state_rel_def] \\ rw [] \\ fs [state_component_equality]
      \\ rw [] \\ res_tac \\ fs [])
    \\ PairCases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs []
    \\ imp_res_tac comp_with_loop_has_code
    \\ fs [set_var_def,has_code_def]
    \\ simp [evaluate_def,find_code_def]
    \\ drule helper_call_lemma
    \\ drule state_rel_IMP_get_vars \\ rpt strip_tac
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ imp_res_tac state_rel_IMP_clock \\ fs [dec_clock_def]
    \\ qmatch_goalsub_abbrev_tac ‘_ = xx’ \\ PairCases_on ‘xx’
    \\ fs [] \\ pop_assum (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def] o GSYM)
    \\ pop_assum (assume_tac o GSYM)
    \\ drule evaluate_break_ok \\ fs []
    \\ Cases_on ‘xx0’ \\ fs []
    \\ imp_res_tac break_ok_no_Break_Continue
    \\ imp_res_tac evaluate_no_Break_Continue \\ fs []
    \\ TOP_CASE_TAC \\ fs [cut_res_def])
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  fs [no_Loop_def,every_prog_def]
  \\ fs [GSYM no_Loop_def]
  \\ reverse (rpt strip_tac)
  \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
  \\ once_rewrite_tac [evaluate_def]
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc"] \\ rw []
    \\ ‘t.locals = s.locals’ by fs [state_rel_def]
    \\ ‘get_var_imm ri t = SOME (Word y)’ by
          (Cases_on ‘ri’ \\ fs [get_var_imm_def])
    \\ simp [comp_no_loop_def,evaluate_def]
    \\ Cases_on ‘evaluate (if word_cmp cmp x y then c1 else c2,s)’ \\ fs []
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ first_x_assum drule \\ disch_then drule
    \\ strip_tac \\ pop_assum mp_tac \\ pop_assum kall_tac
    \\ impl_tac THEN1 (fs [no_Loop_def,every_prog_def] \\ rw [])
    \\ strip_tac \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘evaluate (comp_no_loop p c1,t)’ \\ fs [cut_res_def]
    \\ Cases_on ‘evaluate (comp_no_loop p c2,t)’ \\ fs [cut_res_def]
    \\ reverse (Cases_on ‘q’) \\ fs [] \\ rveq
    THEN1
     (rename [‘_ = (SOME xx,_)’] \\ Cases_on ‘xx’ \\ fs []
      \\ asm_exists_tac \\ fs [cut_res_def]
      \\ TRY (rename [‘(x1,x2) = evaluate _’])
      \\ TRY (qpat_x_assum ‘(x1,x2) = evaluate _’ (assume_tac o GSYM)) \\ fs []
      \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
      \\ imp_res_tac  evaluate_break_ok \\ fs [])
    THEN1
     (rename [‘state_rel s5 t5’]
      \\ fs [cut_state_def,CaseEq"bool",CaseEq"option"] \\ rveq \\ fs []
      \\ fs [dec_clock_def] \\ fs [state_rel_def,state_component_equality]
      \\ rw [] \\ res_tac)
    THEN1
     (rename [‘_ = (SOME xx,_)’] \\ Cases_on ‘xx’ \\ fs []
      \\ asm_exists_tac \\ fs [cut_res_def]
      \\ TRY (rename [‘(x1,x2) = evaluate _’])
      \\ TRY (qpat_x_assum ‘(x1,x2) = evaluate _’ (assume_tac o GSYM)) \\ fs []
      \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
      \\ imp_res_tac  evaluate_break_ok \\ fs [])
    THEN1
     (rename [‘state_rel s5 t5’]
      \\ fs [cut_state_def,CaseEq"bool",CaseEq"option"] \\ rveq \\ fs []
      \\ fs [dec_clock_def] \\ fs [state_rel_def,state_component_equality]
      \\ rw [] \\ res_tac))
  \\ ‘syntax_ok c1 ∧ syntax_ok c2’ by fs [syntax_ok_def]
  \\ fs [CaseEq"option",CaseEq"word_loc"] \\ rw []
  \\ ‘t.locals = s.locals’ by fs [state_rel_def]
  \\ ‘get_var_imm ri t = SOME (Word y)’ by
    (Cases_on ‘ri’ \\ fs [get_var_imm_def])
  \\ fs [comp_with_loop_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ imp_res_tac comp_with_loop_has_code
  \\ Cases_on ‘word_cmp cmp x y’ \\ fs []
  \\ rename [‘cut_res live_out (evaluate (cc,s)) = (res,s1)’]
  THEN
   (Cases_on ‘evaluate (cc,s)’ \\ fs []
    \\ first_x_assum drule
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ disch_then drule \\ simp [GSYM AND_IMP_INTRO]
    \\ disch_then drule \\ fs []
    \\ impl_tac
    THEN1 (Cases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def])
    \\ strip_tac \\ disch_then kall_tac
    \\ fs [evaluate_def]
    \\ rename [‘evaluate (qq,t) = evaluate _’]
    \\ Cases_on ‘evaluate (qq,t)’ \\ fs []
    \\ fs [cut_res_def] \\ reverse (Cases_on ‘q’) \\ fs [] \\ rveq \\ fs []
    THEN1
     (Cases_on ‘x'’ \\ fs [] \\ asm_exists_tac \\ fs []
      \\ TRY (rename [‘(x1,x2) = evaluate _’])
      \\ TRY (qpat_x_assum ‘(x1,x2) = evaluate _’ (assume_tac o GSYM)) \\ fs []
      \\ Cases_on ‘p’ \\ fs [breaks_ok_def]
      \\ imp_res_tac  evaluate_break_ok \\ fs [])
    \\ TRY (rename [‘(x1,x2) = evaluate _’])
    \\ TRY (qpat_x_assum ‘(x1,x2) = evaluate _’ (assume_tac o GSYM)) \\ fs []
    \\ ‘break_ok cont'’ by
      (Cases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [break_ok_def])
    \\ imp_res_tac  evaluate_break_ok \\ fs []
    \\ fs [CaseEq"option",CaseEq"bool",cut_state_def] \\ rveq \\ fs []
    \\ rename [‘state_rel s1 t1’]
    \\ Cases_on ‘s'’ \\ fs [store_cont_def] \\ rveq \\ fs [evaluate_def]
    \\ ‘s1.locals = t1.locals ∧ s1.clock = t1.clock’ by fs [state_rel_def] \\ fs []
    \\ drule helper_call_lemma \\ strip_tac \\ fs [find_code_def]
    \\ rfs [has_code_def] \\ rveq \\ fs [dec_clock_def]
    THEN1 (fs [state_rel_def,state_component_equality] \\ rw [] \\ res_tac)
    \\ qmatch_asmsub_abbrev_tac ‘evaluate (_,t2)’
    \\ qexists_tac ‘t2’ \\ Cases_on ‘evaluate (cont,t2)’
    \\ Cases_on ‘q' = NONE’ \\ rveq \\ rfs []
    \\ Cases_on ‘q'’ \\ fs [] \\ fs [Abbr‘t2’]
    \\ drule evaluate_no_Break_Continue
    \\ imp_res_tac break_ok_no_Break_Continue \\ fs []
    \\ qpat_x_assum ‘state_rel s1 t1’ mp_tac
    \\ Cases_on ‘x'’ \\ fs []
    \\ rpt (pop_assum kall_tac) \\ fs [state_rel_def]
    \\ rpt strip_tac \\ fs [state_component_equality] \\ rw [] \\ res_tac)
QED

Theorem compile_Seq:
  ^(get_goal "syntax_ok (loopLang$Seq _ _)")
Proof
  reverse (rpt strip_tac)
  THEN1
   (fs [comp_no_loop_def,no_Loop_def,every_prog_def]
    \\ fs [GSYM no_Loop_def]
    \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
    \\ simp [Once evaluate_def]
    \\ pairarg_tac \\ fs []
    \\ reverse IF_CASES_TAC
    THEN1
     (strip_tac \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ strip_tac \\ asm_exists_tac \\ fs []
      \\ Cases_on ‘res’ \\ fs []
      \\ Cases_on ‘x’ \\ fs [evaluate_def]
      \\ Cases_on ‘p’ \\ fs []
      \\ rename [‘_ = evaluate (qq,_)’]
      \\ fs [breaks_ok_def]
      \\ Cases_on ‘evaluate (qq,t1)’ \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_break_ok \\ fs [])
    \\ rveq \\ fs [] \\ strip_tac \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ Cases_on ‘res’ \\ fs [evaluate_def])
  \\ fs [syntax_ok_def]
  \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ pairarg_tac \\ fs []
  \\ reverse IF_CASES_TAC
  THEN1
   (strip_tac \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ pop_assum kall_tac
    \\ fs [comp_with_loop_def]
    \\ pairarg_tac \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ impl_tac THEN1 imp_res_tac comp_with_loop_break_ok
    \\ strip_tac \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ Cases_on ‘res’ \\ fs [])
  \\ rveq \\ fs [] \\ strip_tac \\ fs []
  \\ fs [comp_with_loop_def]
  \\ pairarg_tac \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ pop_assum kall_tac
  \\ first_x_assum drule \\ simp []
  \\ impl_tac THEN1 imp_res_tac comp_with_loop_break_ok
  \\ strip_tac \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ pop_assum kall_tac
  \\ first_x_assum drule
  \\ imp_res_tac comp_with_loop_has_code \\ fs []
QED

Theorem eval_lemma:
  ∀s exp w t.
    eval s exp = SOME w ∧ state_rel s t ⇒ eval t exp = SOME w
Proof
  ho_match_mp_tac eval_ind \\ rw [] \\ fs [eval_def]
  \\ fs [state_rel_def] \\ rveq \\ fs []
  \\ fs [CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rveq \\ fs [mem_load_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ qpat_x_assum ‘_ = SOME z’ kall_tac
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘wexps’
  \\ qid_spec_tac ‘ws’
  \\ Induct_on ‘wexps’ \\ fs []
  \\ fs [wordSemTheory.the_words_def,CaseEq"option",CaseEq"word_loc"] \\ rw []
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  fs [syntax_ok_def,no_Loop_def,every_prog_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rw [] \\ fs [comp_no_loop_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ fs [set_var_def]
  \\ imp_res_tac eval_lemma \\ fs []
  \\ fs [state_rel_def]
  \\ fs [state_component_equality]
  \\ rw [] \\ res_tac \\ fs []
  \\ fs [domain_lookup] \\ res_tac
  \\ PairCases_on ‘v’ \\ res_tac \\ fs []
  \\ fs [comp_def,has_code_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [has_code_def]
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
  ^(get_goal "loopLang$StoreByte") ∧
  ^(get_goal "loopLang$LoadByte")
Proof
  fs [syntax_ok_def,no_Loop_def,every_prog_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rw [] \\ fs [comp_no_loop_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ imp_res_tac eval_lemma \\ fs []
  \\ fs [state_rel_def]
  \\ fs [state_component_equality]
  \\ fs [mem_store_def]
  \\ rveq \\ fs []
  \\ rw [] \\ res_tac
  \\ fs [set_var_def]
  \\ res_tac \\ fs []
QED

Theorem compile_SetGlobal:
  ^(get_goal "loopLang$SetGlobal")
Proof
  fs [syntax_ok_def,no_Loop_def,every_prog_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rw [] \\ fs [comp_no_loop_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ fs [set_globals_def]
  \\ imp_res_tac eval_lemma \\ fs []
  \\ fs [state_rel_def]
  \\ fs [state_component_equality]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem compile_FFI:
  ^(get_goal "loopLang$FFI")
Proof
  fs [syntax_ok_def,no_Loop_def,every_prog_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rw [] \\ fs [comp_no_loop_def]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ fs [state_rel_def] \\ rveq \\ fs [] \\ fs [PULL_EXISTS]
  \\ fs [cut_state_def] \\ rveq \\ fs [] \\ fs [PULL_EXISTS]
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ fs [CaseEq"ffi_result"] \\ rveq \\ fs []
  \\ fs [call_env_def]
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Continue,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_SetGlobal, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

Theorem comp_no_loop_no_loop:
  !p prog.
    no_Loops (FST p) ∧ no_Loops (SND p) ⇒
    no_Loops (comp_no_loop p prog)
Proof
  ho_match_mp_tac comp_no_loop_ind >>
  rw [] >>
  fs [comp_no_loop_def, no_Loops_def, no_Loop_def, every_prog_def] >>
  every_case_tac >> fs []
QED

Theorem store_cont_no_loop:
  !l cont s cont' s'.
    store_cont l cont s = (cont',s') ∧
    no_Loops cont ∧
    EVERY (λ(name,params,body). no_Loops body) (SND s) ⇒
    no_Loops cont' ∧ EVERY (λ(name,params,body). no_Loops body) (SND s')
Proof
  rw [] >>
  cases_on ‘s’ >>
  fs [store_cont_def, no_Loops_def, no_Loop_def] >> rveq >>
  fs [every_prog_def]
QED

Theorem comp_with_loop_no_loop:
  !p q cont s body n fs.
    comp_with_loop p q cont s = (body,n,fs) ∧
    no_Loops (FST p) ∧ no_Loops (SND p) ∧ no_Loops cont ∧
    EVERY (λ(name,params,body). no_Loops body) (SND s) ==>
    no_Loops body ∧ EVERY (λ(name,params,body). no_Loops body) fs
Proof
  ho_match_mp_tac comp_with_loop_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >>
  TRY (
    rename [‘Mark’] >>
    fs [comp_with_loop_def] >> rveq >>
    imp_res_tac comp_no_loop_no_loop >>
    fs [no_Loops_def, no_Loop_def, every_prog_def]) >>
  TRY (
    rename [‘Seq’] >>
    strip_tac >>
    fs [comp_with_loop_def, no_Loops_def, no_Loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    Cases_on ‘s'’ >>
    gs [every_prog_def]) >>
  TRY (
    rename [‘If’]  >>
    strip_tac >>
    fs [comp_with_loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    imp_res_tac store_cont_no_loop >>
    fs [] >>
    Cases_on ‘s''’ >>
    gs [no_Loops_def, no_Loop_def, every_prog_def]) >>
  TRY (
    rename [‘Loop’]  >>
    fs [Once comp_with_loop_def] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    strip_tac >> rveq >>
    drule store_cont_no_loop >>
    strip_tac >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    fs [no_Loops_def, no_Loop_def, every_prog_def]) >>
  TRY (
    rename [‘Call’]  >>
    rewrite_tac [comp_with_loop_def] >>
    TOP_CASE_TAC
    >- (
      strip_tac >> rveq >> fs [] >>
      fs [no_Loops_def, no_Loop_def, every_prog_def]) >>
    rpt TOP_CASE_TAC >>
    rewrite_tac [LET_THM] >>
    pairarg_tac >>
    drule store_cont_no_loop >>
    strip_tac >>
    last_x_assum mp_tac >>
    disch_then (qspecl_then [‘(q,q',q'',r)’, ‘q’, ‘SND (q,q',q'',r)’,
                             ‘q'’, ‘SND (q',q'',r)’, ‘q''’, ‘SND (q'',r)’,
                             ‘cont'’, ‘s'’] mp_tac) >>
    rewrite_tac [UNCURRY] >>
    last_x_assum mp_tac >>
    disch_then (qspecl_then [‘(q,q',q'',r)’, ‘q’, ‘SND (q,q',q'',r)’,
                             ‘q'’, ‘SND (q',q'',r)’, ‘q''’, ‘SND (q'',r)’,
                             ‘cont'’, ‘s'’] mp_tac) >>
    rewrite_tac [UNCURRY] >>
    qpat_x_assum ‘store_cont _ _ _ = _’ (mp_tac o GSYM) >>
    rewrite_tac [] >>
    simp [] >>
    strip_tac >>
    pop_assum (mp_tac o GSYM) >>
    simp [] >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    strip_tac >> rveq >>
    gs [no_Loops_def, no_Loop_def, every_prog_def] >>
    cases_on ‘comp_with_loop p q' cont' s'’ >>
    fs [] >>
    cases_on ‘r'’ >> fs [] >>
    cases_on ‘comp_with_loop p q'' cont' (q'³',r'')’ >> fs []) >>
  fs [comp_with_loop_def, no_Loops_def, no_Loop_def] >> fs [] >>
  rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
  fs [every_prog_def]
QED


Theorem comp_all_no_loop:
  !prog l n q r name params body.
    FOLDR comp (n,l) prog = (q,r) ∧
    EVERY (λ(name, params,body). no_Loops body) l /\
    MEM (name, params,body) r ==>
    no_Loops body
Proof
  Induct >> rw [] >>
  fs []
  >- (
   fs [EVERY_MEM, UNCURRY] >>
   res_tac >> fs []) >>
  cases_on ‘h’ >>
  cases_on ‘r'’ >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >> rveq
  >- (
  cases_on ‘FOLDR comp (n,l) prog’ >>
  drule comp_with_loop_no_loop >>
  impl_tac
  >- (
    fs [] >>
    last_x_assum drule >>
    fs [] >>
    strip_tac >>
    fs [EVERY_MEM] >>
    fs [no_Loops_def, no_Loop_def, every_prog_def] >>
    rw [] >> fs [] >>
    cases_on ‘e’ >>
    cases_on ‘r'’ >> res_tac >> fs []) >>
  fs []) >>
  cases_on ‘FOLDR comp (n,l) prog’ >>
  drule comp_with_loop_no_loop >>
  impl_tac
  >- (
    fs [] >>
    last_x_assum drule >>
    fs [] >>
    strip_tac >>
    fs [EVERY_MEM] >>
    fs [no_Loops_def, no_Loop_def, every_prog_def] >>
    rw [] >> fs [] >>
    cases_on ‘e’ >>
    cases_on ‘r'’ >> res_tac >> fs []) >>
  fs [] >>
  strip_tac >>
  fs [EVERY_MEM] >>
  res_tac >> fs []
QED

Theorem comp_prog_no_loops:
  !prog name params body.
    MEM (name,params,body) (comp_prog prog) ==>
    no_Loops body
Proof
  rw [] >>
  fs [comp_prog_def] >>
  qmatch_asmsub_abbrev_tac ‘(n, [])’ >>
  cases_on ‘FOLDR comp (n,[]) prog’ >>
  fs [] >>
  drule comp_all_no_loop >>
  fs [EVERY_DEF] >>
  disch_then drule >>
  fs []
QED

Theorem store_cont_params_distinct:
  !l cont s cont' t.
    store_cont l cont s = (cont',t) ∧
    EVERY (λ(name,params,body). ALL_DISTINCT params) (SND s) ⇒
    EVERY (λ(name,params,body). ALL_DISTINCT params) (SND t)
Proof
  rw [] >>
  cases_on ‘s’ >> cases_on ‘t’ >>
  fs [store_cont_def] >> rveq >>
  fs [EVERY_MEM, ALL_DISTINCT_MAP_FST_toAList]
QED

Theorem comp_with_loop_params_distinct:
  !p q cont s body t.
    comp_with_loop p q cont s = (body,t) ∧
    EVERY (λ(name,params,body). ALL_DISTINCT params) (SND s) ⇒
    EVERY (λ(name,params,body). ALL_DISTINCT params) (SND t)
Proof
  ho_match_mp_tac comp_with_loop_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >>
  TRY (
    rename [‘Seq’] >>
    strip_tac >>
    fs [comp_with_loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    Cases_on ‘s'’ >>
    gs []) >>
  TRY (
    rename [‘If’]  >>
    strip_tac >>
    fs [comp_with_loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    drule store_cont_params_distinct >>
    fs []) >>
  TRY (
    rename [‘Loop’]  >>
    rewrite_tac [comp_with_loop_def] >>
    fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    strip_tac >> rveq >>
    gs [] >>
    drule store_cont_params_distinct >>
    gs [] >>
    strip_tac >> gs [] >>
    fs [ALL_DISTINCT_MAP_FST_toAList]) >>
  TRY (
    rename [‘Call’]  >>
    rewrite_tac [comp_with_loop_def] >>
    every_case_tac >> fs [] >> rveq >>
    rpt (pairarg_tac >> fs []) >> rveq >> gs [] >>
    strip_tac >> rveq >> fs [] >>
    drule store_cont_params_distinct >>
    strip_tac >> gs []) >>
  fs [comp_with_loop_def] >>
  rpt (pairarg_tac >> fs []) >> rveq >> fs []
QED


Theorem first_params_comp_all_distinct:
  !prog l n q r name params.
    FOLDR comp (n,l) prog = (q,r) ∧
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog ∧
    EVERY (λ(name,params,body). ALL_DISTINCT params) l ==>
    EVERY (λ(name,params,body). ALL_DISTINCT params) r
Proof
  Induct >> rw [] >>
  fs [] >>
  PairCases_on ‘h’ >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >> rveq >> gs [] >>
  cases_on ‘FOLDR comp (n,l) prog’ >>
  last_x_assum drule >>
  gs [] >>
  strip_tac >>
  drule comp_with_loop_params_distinct >>
  fs []
QED

Theorem compile_prog_distinct_params:
  !prog name params body.
    MEM (name,params,body) (comp_prog prog) ∧
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog ⇒
    ALL_DISTINCT params
Proof
  rw [] >>
  fs [comp_prog_def] >>
  qmatch_asmsub_abbrev_tac ‘(n, [])’ >>
  cases_on ‘FOLDR comp (n,[]) prog’ >>
  fs [] >>
  drule first_params_comp_all_distinct >>
  fs [] >>
  strip_tac >>
  gs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘(name,params,body)’ mp_tac) >>
  fs []
QED


Definition acc_ok_def:
  acc_ok (n:num,fs) ⇔
  (∀x. MEM x (MAP FST fs) ⇒ x < n) ∧
  ALL_DISTINCT (MAP FST fs)
End

Theorem store_cont_names_distinct:
  !l cont s cont' t.
    store_cont l cont s = (cont',t) ∧
    acc_ok s ⇒
    acc_ok t ∧ FST s ≤ FST t ∧
    (∀x. x < FST s ∧ MEM x (MAP FST (SND t)) ⇒
         MEM x (MAP FST (SND s))) ∧
    (∀x. MEM x (SND s) ⇒ MEM x (SND t))
Proof
  rw [] >>
  cases_on ‘s’ >> cases_on ‘t’ >>
  fs [store_cont_def, acc_ok_def] >> rveq >>
  fs [] >>
  rw [] >> fs [] >>
  res_tac >> fs [] >>
  CCONTR_TAC >> fs [] >>
  res_tac >> fs []
QED

Theorem comp_with_loop_names_distinct:
  !p q cont s body t.
    comp_with_loop p q cont s = (body,t) ∧
    acc_ok s ⇒
    acc_ok t ∧ FST s ≤ FST t ∧
    (∀x. MEM x (MAP FST (SND t)) ∧ x < FST s ⇒
         MEM x (MAP FST (SND s))) ∧
    (∀x. MEM x (SND s) ⇒ MEM x (SND t))
Proof
  ho_match_mp_tac comp_with_loop_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >>
  TRY (
    rename [‘Seq’] >>
    strip_tac >>
    fs [comp_with_loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    Cases_on ‘s'’ >>
    gs []) >>
  TRY (
    rename [‘If’]  >>
    strip_tac >>
    fs [comp_with_loop_def] >> fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    drule store_cont_names_distinct >>
    strip_tac >> gs []) >>
  TRY (
    rename [‘Loop’]  >>
    rewrite_tac [comp_with_loop_def] >>
    fs [] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >>
    strip_tac >> rveq >>
    gs [] >>
    drule store_cont_names_distinct >>
    gs [] >>
    strip_tac >> gs [] >>
    ‘acc_ok (n + 1,funs)’ by (
      fs [acc_ok_def] >>
      rw [] >> gs [] >>
      res_tac >> fs []) >>
    conj_tac
    >- (
      fs [acc_ok_def] >>
      rw [] >> gs [] >>
      CCONTR_TAC >> fs [] >>
      last_x_assum drule >>
      strip_tac >> fs [] >>
      last_x_assum drule >>
      impl_tac >- fs [] >>
      strip_tac >>
      last_x_assum drule >> fs []) >>
    fs [] >>
    rw [] >> gs []) >>
  TRY (
    rename [‘Call’]  >>
    rewrite_tac [comp_with_loop_def] >>
    every_case_tac >> fs [] >> rveq >>
    rpt (pairarg_tac >> fs []) >> rveq >> gs [] >>
    strip_tac >> rveq >> fs [] >>
    drule store_cont_names_distinct >>
    strip_tac >> gs []) >>
  fs [comp_with_loop_def] >>
  rpt (pairarg_tac >> fs []) >> rveq >> fs []
QED

Theorem first_comp_all_distinct:
  !prog n l q r.
    ALL_DISTINCT (MAP FST prog ++ MAP FST l) ∧
    FOLDR comp (n,l) prog = (q,r) ∧
    (!x. MEM x (MAP FST prog) ==> x < n) ∧
    acc_ok (n,l) ⇒
    acc_ok (q,r) ∧ n ≤ q ∧
    (∀x. MEM x (MAP FST r) ∧ x < n ⇒
         MEM x (MAP FST l) ∨ MEM x (MAP FST prog)) ∧
    (∀x. MEM x l ⇒ MEM x r)
Proof
  Induct
  >- (rw [] >> fs []) >>
  rpt gen_tac >>
  strip_tac >> fs [] >>
  PairCases_on ‘h’ >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  gs [] >>
  cases_on ‘FOLDR comp (n,l) prog’ >> fs [] >>
  last_x_assum drule >>
  fs [] >> strip_tac >>
  first_x_assum drule >>
  fs [] >>
  strip_tac >>
  drule comp_with_loop_names_distinct >>
  fs [] >>
  simp [acc_ok_def] >>
  strip_tac >>
  rpt conj_tac
  >- (
   rw [] >> fs [] >>
   last_x_assum (qspec_then ‘h0’ mp_tac) >> fs [])
  >- (
  CCONTR_TAC >> fs [] >>
  last_x_assum (qspec_then ‘h0’ mp_tac) >>
  fs [] >>
  CCONTR_TAC >> fs [] >>
  first_x_assum drule >>
  fs [] >>
  CCONTR_TAC >> fs [] >>
  last_x_assum drule >>
  fs []) >>
  rw [] >>
  fs [] >>
  CCONTR_TAC >> fs [] >>
  last_x_assum (qspec_then ‘x’ mp_tac) >>
  last_x_assum (qspec_then ‘x’ mp_tac) >>
  fs []
QED


Theorem first_comp_prog_all_distinct:
  !prog.
    ALL_DISTINCT (MAP FST prog) ⇒
    ALL_DISTINCT (MAP FST (comp_prog prog))
Proof
  rw [] >>
  fs [comp_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘(n, [])’ >>
  cases_on ‘FOLDR comp (n,[]) prog’ >>
  fs [] >>
  imp_res_tac first_comp_all_distinct >>
  gs [] >>
  fs [acc_ok_def] >>
  qsuff_tac ‘(∀x. MEM x (MAP FST prog) ⇒ x < n)’ >>
  fs [] >>
  rw [] >>
  fs [Abbr ‘n’, MEM_MAP] >>
  cases_on ‘y’ >> fs [] >> rveq >>
  match_mp_tac pan_commonPropsTheory.max_foldr_lt >>
  fs [MEM_MAP] >>
  qexists_tac ‘(q', r')’ >> fs []
QED

Triviality state_rel_imp_code_rel:
  state_rel s t ⇒ ∃c. t = s with code := c
Proof
  rw [state_rel_def] >>
  metis_tac []
QED

val comp_Call =
  compile_correct |> Q.SPEC ‘Call NONE (SOME start) [] NONE’ |>
  REWRITE_RULE [syntax_ok_def]


Theorem state_rel_imp_semantics:
  state_rel s t ∧
  s.code = fromAList loop_code /\
  t.code = fromAList (loop_remove$comp_prog loop_code) /\
  (∃prog. lookup start s.code = SOME ([], prog)) /\
  semantics s start <> Fail ==>
  semantics t start = semantics s start
Proof
  rw [] >>
  drule state_rel_imp_code_rel >>
  strip_tac >> rveq >> fs [] >>
  qpat_x_assum ‘c = fromAList (comp_prog loop_code)’ kall_tac >>
  reverse (Cases_on ‘semantics s start’) >> fs [] >> rveq
  >- (
   (* termination case of original loop program *)
   fs [semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp [] >>
   rw []
   >- (
    (* fail case of loop_remove *)
    last_x_assum (qspec_then ‘k'’ mp_tac) >> simp [] >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    CCONTR_TAC >>
    drule comp_Call >>
    disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                            clock := k'|>’ mp_tac) >>
    disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
    impl_tac
    >- (
     conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
     conj_tac
     >- (
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
     fs [breaks_ok_def, break_ok_def]) >>
    ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
      fs [no_Loop_def, every_prog_def]) >>
    strip_tac >> rfs [] >>
    fs [] >> rveq >> fs [] >>
    fs [comp_no_loop_def] >>
    cases_on ‘q’ >> fs [] >> rveq >>
    cases_on ‘x’ >> fs []) >>
   (* termination/diverging case of loopremove *)
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* termination case of loopremove *)
   >- (
    rw [] >> fs [] >>
    last_x_assum (qspec_then ‘k'’ assume_tac) >>
    cases_on ‘evaluate (Call NONE (SOME start) [] NONE,s with clock := k')’ >> fs [] >>
    drule comp_Call >>
    disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                            clock := k'|>’ mp_tac) >>
    disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
    impl_tac
    >- (
     conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
     conj_tac
     >- (
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
     fs [breaks_ok_def, break_ok_def]) >>
    ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
      fs [no_Loop_def, every_prog_def]) >>
    strip_tac >> rfs [] >>
    fs [] >> rveq >> fs [] >>
    fs [comp_no_loop_def] >>
    cases_on ‘q’ >> fs [] >> rveq >>
    cases_on ‘x’ >> fs [] >> rveq >> fs []
    >- (
     last_x_assum (qspec_then ‘k'’ assume_tac) >>
     rfs [] >>
     fs [] >>
     cases_on ‘r’ >> fs [] >>
     cases_on ‘x’ >> fs []
     >- (
      qpat_x_assum ‘evaluate (_,_) = _’ kall_tac >>
      dxrule evaluate_add_clock_eq >>
      dxrule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘k'’ assume_tac) >>
      disch_then (qspec_then ‘k’ assume_tac) >>
      fs [] >> rveq >> fs [state_rel_def] >>
      rveq >> fs [state_component_equality]) >>
     qpat_x_assum ‘evaluate (_,_) = _’ kall_tac >>
     dxrule evaluate_add_clock_eq >>
     dxrule evaluate_add_clock_eq >>
     disch_then (qspec_then ‘k'’ assume_tac) >>
     disch_then (qspec_then ‘k’ assume_tac) >>
     fs []) >>
    last_x_assum (qspec_then ‘k'’ assume_tac) >>
    rfs [] >>
    fs [] >>
    cases_on ‘r’ >> fs [] >>
    cases_on ‘x’ >> fs []
    >- (
     qpat_x_assum ‘evaluate (_,_) = _’ kall_tac >>
     dxrule evaluate_add_clock_eq >>
     dxrule evaluate_add_clock_eq >>
     disch_then (qspec_then ‘k'’ assume_tac) >>
     disch_then (qspec_then ‘k’ assume_tac) >>
     fs []) >>
    qpat_x_assum ‘evaluate (_,_) = _’ kall_tac >>
    dxrule evaluate_add_clock_eq >>
    dxrule evaluate_add_clock_eq >>
    disch_then (qspec_then ‘k'’ assume_tac) >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    fs [] >> rveq >> fs [state_rel_def] >>
    rveq >> fs [state_component_equality]) >>
   (* diverging case of loopremove *)
   rw [] >> fs [] >>
   last_x_assum (qspec_then ‘k’ assume_tac) >>
   cases_on ‘evaluate (Call NONE (SOME start) [] NONE,s with clock := k)’ >> fs [] >>
   drule comp_Call >>
   disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                           clock := k|>’ mp_tac) >>
   disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
   impl_tac
   >- (
    conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
    conj_tac
    >- (
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    fs [breaks_ok_def, break_ok_def]) >>
   ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
     fs [no_Loop_def, every_prog_def]) >>
   strip_tac >> rfs [] >>
   fs [] >> rveq >> fs [] >>
   fs [comp_no_loop_def] >>
   cases_on ‘q’ >> fs [] >> rveq >>
   cases_on ‘x’ >> fs [] >> rveq >> fs []
   >- (
    qexists_tac ‘k’ >>
    fs []) >>
   last_x_assum (qspec_then ‘k’ assume_tac) >>
   rfs [] >> fs [] >>
   qexists_tac ‘k’ >> fs []) >>
  (* diverging case of orginal program *)
  fs [semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw []
  >- (
   (* fail case of loopremove semantics *)
   fs[] >> rveq >> fs[] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   CCONTR_TAC >>
   drule comp_Call >>
   disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                           clock := k|>’ mp_tac) >>
   disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
   impl_tac
   >- (
    conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
    conj_tac
    >- (
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    fs [breaks_ok_def, break_ok_def]) >>
   ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
     fs [no_Loop_def, every_prog_def]) >>
   strip_tac >> rfs [] >>
   fs [] >> rveq >> fs [] >>
   fs [comp_no_loop_def] >>
   cases_on ‘q’ >> fs [] >> rveq >>
   cases_on ‘x’ >> fs []) >>
  (* termination/diverging case of loopremove *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* termination case of loopremove *)
  >- (
   rw [] >> fs[] >>
   cases_on ‘r’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> (
   last_x_assum (qspec_then ‘k’ mp_tac) >>
   last_x_assum (qspec_then ‘k’ mp_tac) >>
   strip_tac >> rfs [] >> rveq >>
   cases_on ‘evaluate (Call NONE (SOME start) [] NONE,s with clock := k)’ >>
   fs [] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >>
   fs [] >> strip_tac >>
   cases_on ‘q’ >> fs [] >>
   cases_on ‘x’ >> fs [] >>
   drule comp_Call >>
   disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                           clock := k|>’ mp_tac) >>
   disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
   impl_tac
   >- (
    conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
    fs [breaks_ok_def, break_ok_def]) >>
   ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
     fs [no_Loop_def, every_prog_def]) >>
   strip_tac >> rfs [] >>
   fs [] >> rveq >> fs [] >>
   fs [comp_no_loop_def])) >>
  rw [] >>
  qmatch_abbrev_tac ‘build_lprefix_lub l1 = build_lprefix_lub l2’ >>
  ‘(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2’
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac
  >- (
   UNABBREV_ALL_TAC >>
   conj_tac >>
   Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
   REWRITE_TAC[IMAGE_COMPOSE] >>
   match_mp_tac prefix_chain_lprefix_chain >>
   simp[prefix_chain_def,PULL_EXISTS] >>
   qx_genl_tac [‘k1’, ‘k2’] >>
   qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES >>
   simp[LESS_EQ_EXISTS] >>
   rw [] >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               loopPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with
               <|clock := k1; code := fromAList (comp_prog loop_code)|>’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with
               <|clock := k2; code := fromAList (comp_prog loop_code)|>’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with clock := k2’, ‘p’] mp_tac) >>
   fs []) >>
  simp[equiv_lprefix_chain_thm] >>
  fs [Abbr ‘l1’, Abbr ‘l2’]  >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac
  >- (
   qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
   Cases_on`p` >> pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
   drule comp_Call >>
   disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                           clock := k|>’ mp_tac) >>
   disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
   impl_tac
   >- (
    conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
    conj_tac
    >- (
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     last_x_assum (qspec_then ‘k’ mp_tac) >>
     fs []) >>
    fs [breaks_ok_def, break_ok_def]) >>
   ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
     fs [no_Loop_def, every_prog_def]) >>
   strip_tac >> rfs [] >>
   qexists_tac ‘k’ >> simp[] >>
   cases_on ‘q’ >> fs [] >>
   TRY (cases_on ‘x’) >>
   fs [comp_no_loop_def] >>
   fs [state_rel_def] >>
   rveq >> fs [] >>
   fs [evaluate_def]) >>
  cases_on ‘evaluate
            (Call NONE (SOME start) [] NONE,s with clock := k)’ >>
  drule comp_Call >>
  disch_then (qspec_then ‘s with <|code := fromAList (comp_prog loop_code);
                          clock := k|>’ mp_tac) >>
  disch_then (qspec_then ‘(Fail,Fail)’ mp_tac) >>
  impl_tac
  >- (
   conj_tac >- (fs [state_rel_def] >> metis_tac []) >>
   conj_tac
   >- (
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    last_x_assum (qspec_then ‘k’ mp_tac) >>
    fs []) >>
   fs [breaks_ok_def, break_ok_def]) >>
  ‘no_Loop (Call NONE (SOME start) [] NONE)’ by (
    fs [no_Loop_def, every_prog_def]) >>
  strip_tac >> rfs [] >>
  qexists_tac ‘k’ >> simp[] >>
  cases_on ‘q’ >> fs [] >>
  TRY (cases_on ‘x’) >>
  fs [comp_no_loop_def] >>
  fs [state_rel_def] >>
  rveq >> fs [] >>
  fs [evaluate_def]
QED

Theorem comp_comp_with_loop_mem:
  ∀fprog lprog n l q r name params body body' accum t.
    FOLDR comp (n,l) (fprog ++ [(name,params,body)] ++ lprog) = (q,r) ∧
    acc_ok (n,l) ∧
    (∀x. MEM x (MAP FST (fprog ++ [(name,params,body)] ++ lprog)) ⇒ x < n) ∧
    ALL_DISTINCT (MAP FST (fprog ++ [(name,params,body)] ++ lprog) ++ MAP FST l) ∧
    accum = FOLDR comp (n,l) lprog ∧
    comp_with_loop (Fail,Fail) body Fail accum = (body',t) ⇒
    MEM (name,params,body') r ∧
    (∀n' p b. MEM (n',p,b) (SND t) ⇒ MEM (n',p,b) r)
Proof
  Induct >>
  rpt gen_tac >> strip_tac
  >- (fs [comp_def] >>
      pairarg_tac >> fs [] >> rveq >> rgs []) >>
  cases_on ‘FOLDR comp (n,l) (fprog ++ [(name,params,body)] ++ lprog)’ >>
  fs [] >>
  last_x_assum drule >>
  fs [] >>
  strip_tac >>
  last_x_assum assume_tac >>
  PairCases_on ‘h’ >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >>
  rveq >> gs [] >>
  drule comp_with_loop_names_distinct >>
  impl_tac
  >- (
  ‘ALL_DISTINCT (MAP FST (fprog ++ [(name,params,body)] ++ lprog) ++ MAP FST l)’ by fs [] >>
  drule first_comp_all_distinct >>
  fs [] >>
  disch_then (qspecl_then [‘n’, ‘q'’, ‘r'’] mp_tac) >>
  impl_tac
  >- (
    fs [] >>
    rw [] >> gs []) >>
  strip_tac >> rfs []) >>
  strip_tac >>
  res_tac >> gs [] >>
  ‘∀x. (MEM x (MAP FST fprog) ∨ x = name) ∨ MEM x (MAP FST lprog) ⇒
       x < n’ by (rw [] >> gs []) >>
  last_x_assum drule >>
  strip_tac >>
  fs []
QED

Theorem comp_prog_has_code:
  ∀prog name params body.
    ALL_DISTINCT (MAP FST prog) ∧
    MEM (name,params,body) prog ⇒
    ∃init.
      has_code (comp (name,params,body) init)
               (fromAList (comp_prog prog))
Proof
  rw [] >>
  fs [MEM_SPLIT] >>
  rename [‘ prog = fprog ++ [(name,params,body)] ++ lprog’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [ALL_DISTINCT_APPEND] >>
  ‘~MEM (name,params,body) fprog’ by (
    CCONTR_TAC >>
    gs [MEM_MAP] >>
    last_x_assum (qspec_then ‘(name,params,body)’ mp_tac) >>
    fs []) >>
  ‘~MEM (name,params,body) lprog’ by (
    CCONTR_TAC >>
    gs [MEM_MAP] >>
    first_x_assum (qspec_then ‘(name,params,body)’ mp_tac) >>
    fs [] >>
    first_x_assum (qspec_then ‘name’ mp_tac) >>
    fs [] >>
    qexists_tac ‘(name,params,body)’ >> fs []) >>
  qmatch_goalsub_abbrev_tac ‘comp_prog prog’ >>
  fs [loop_removeTheory.comp_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘(nn,[])’ >>
  qexists_tac ‘FOLDR comp (nn, []) lprog’ >>
  qmatch_goalsub_abbrev_tac ‘comp _ accum’ >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >>
  fs [has_code_def] >>
  fs [lookup_fromAList] >>
  conj_asm1_tac
  >- (
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  cases_on ‘FOLDR comp (nn,[]) prog’ >> fs [] >>
  ‘ALL_DISTINCT (MAP FST prog ++
                 MAP FST ([] :(num # num list # α loopLang$prog) list))’ by (
    fs [ALL_DISTINCT_APPEND] >>
    gs [Abbr ‘prog’, ALL_DISTINCT_APPEND] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs []) >>
  drule first_comp_all_distinct >>
  disch_then (qspecl_then [‘nn’, ‘q’, ‘r’] mp_tac) >>
  impl_tac
  >- (
    fs [acc_ok_def] >>
    fs [Abbr ‘nn’] >> rw [] >> gs [] >>
    match_mp_tac pan_commonPropsTheory.max_foldr_lt >>
    fs []) >>
  strip_tac >>
  conj_asm1_tac
  >- fs [acc_ok_def] >>
  fs [Abbr ‘prog’] >>
  drule comp_comp_with_loop_mem >>
  disch_then (qspecl_then [‘body'’, ‘accum’, ‘(n,funs)’] mp_tac) >>
  fs [acc_ok_def] >>
  impl_tac
  >- (
    fs [Abbr ‘nn’] >>
    rw [] >> gs [] >>
    match_mp_tac pan_commonPropsTheory.max_foldr_lt >>
    fs []) >>
  fs []) >>
  fs [EVERY_MEM] >>
  rw [] >>
  pairarg_tac >> fs [] >>
  pop_assum kall_tac >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  cases_on ‘FOLDR comp (nn,[]) prog’ >> fs [] >>
  ‘ALL_DISTINCT (MAP FST prog ++
                 MAP FST ([] :(num # num list # α loopLang$prog) list))’ by (
    fs [ALL_DISTINCT_APPEND] >>
    gs [Abbr ‘prog’, ALL_DISTINCT_APPEND] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs []) >>
  drule first_comp_all_distinct >>
  disch_then (qspecl_then [‘nn’, ‘q’, ‘r’] mp_tac) >>
  impl_tac
  >- (
    fs [acc_ok_def] >>
    fs [Abbr ‘nn’] >> rw [] >> gs [] >>
    match_mp_tac pan_commonPropsTheory.max_foldr_lt >>
    fs []) >>
  strip_tac >>
  conj_asm1_tac
  >- fs [acc_ok_def] >>
  fs [Abbr ‘prog’] >>
  drule comp_comp_with_loop_mem >>
  disch_then (qspecl_then [‘body'’, ‘accum’, ‘(n,funs)’] mp_tac) >>
  fs [acc_ok_def] >>
  impl_tac
  >- (
    fs [Abbr ‘nn’] >>
    rw [] >> gs [] >>
    match_mp_tac pan_commonPropsTheory.max_foldr_lt >>
    fs []) >>
  fs []
QED

(* first_name offset *)

Theorem store_const_lab_min:
  x ≤ FST prog ∧
  EVERY (λp. x ≤ FST p) (SND prog) ∧
  store_cont s cont prog = (cont',prog') ⇒
  x ≤ FST prog' ∧ EVERY (λp. x ≤ FST p) (SND prog')
Proof
  strip_tac>>
  PairCases_on ‘prog’>>
  gs[loop_removeTheory.store_cont_def]>>
  rveq>>
  gs[EVERY_MEM]>>strip_tac>>strip_tac>>rveq>>gs[]
QED

Theorem comp_with_loop_lab_min:
  comp_with_loop p p' cont prog = (q2, s')∧
  x ≤ FST prog ∧
  EVERY (λp. x ≤ FST p) (SND prog) ⇒
  (x ≤ FST s' ∧ EVERY (λp. x ≤ FST p) (SND s'))
Proof
  MAP_EVERY qid_spec_tac [‘s'’, ‘q2’, ‘prog’, ‘cont’, ‘p'’, ‘p’]>>
  recInduct loop_removeTheory.comp_with_loop_ind>>rw[]>>
  qpat_x_assum ‘comp_with_loop _ _ _ _ = _’ mp_tac>>
  rewrite_tac[loop_removeTheory.comp_with_loop_def]>>
  strip_tac>>fs[]>>
  rpt (pairarg_tac>>fs[])
  >- metis_tac[store_const_lab_min]
  >- metis_tac[store_const_lab_min]
  >- (Cases_on ‘handler’>>fs[]>>
      PairCases_on ‘x'’>>fs[]>>
      rpt (pairarg_tac>>fs[])>>
      metis_tac[store_const_lab_min])
  >- (Cases_on ‘handler’>>fs[]>>
      PairCases_on ‘x'’>>fs[]>>
      rpt (pairarg_tac>>fs[])>>
      metis_tac[store_const_lab_min])>>
  rveq>>gs[]>>
  drule_all store_const_lab_min>>
  strip_tac>>gs[]
QED

Theorem FOLDR_min:
  EVERY (λp. x ≤ FST p) prog ∧ prog ≠ [] ⇒
  x ≤ FOLDR MAX 0 (MAP FST prog)
Proof
  Induct_on ‘prog’>>gs[]
QED

Theorem loop_remove_comp_lab_min:
  FOLDR comp (m + 1,[]) prog = (n, prog') ∧
  (prog ≠ [] ⇒ x ≤ m) ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  (prog ≠[] ⇒ x ≤ n) ∧ EVERY (λp. x ≤ FST p) prog'
Proof
  MAP_EVERY qid_spec_tac [‘n’, ‘m’, ‘prog'’, ‘prog’]>>
  Induct>>gs[]>>ntac 5 strip_tac>>
  PairCases_on ‘h’>>gs[loop_removeTheory.comp_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule comp_with_loop_lab_min>>
  disch_then $ qspec_then ‘x’ mp_tac>>
  qmatch_goalsub_abbrev_tac ‘FST xxx’>>
  Cases_on ‘xxx’>>gs[]>>
  first_x_assum $ qspecl_then [‘r’, ‘m’, ‘q’] assume_tac>>
  gs[]>>
  Cases_on ‘prog’>>gs[]
QED

Theorem loop_remove_comp_prog_lab_min:
  comp_prog prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  gs[loop_removeTheory.comp_prog_def]>>strip_tac>>
  qmatch_asmsub_abbrev_tac ‘SND xxx’>>
  Cases_on ‘xxx’>>gs[]>>
  drule loop_remove_comp_lab_min>>
  disch_then $ qspec_then ‘x’ mp_tac>>gs[]>>
  impl_tac >-metis_tac[FOLDR_min]>>rw[]
QED

val _ = export_theory();
