(*
  Correctness proof for wheat_loop
*)

open preamble wheatLangTheory wheatSemTheory
local open wordSemTheory in end

val _ = new_theory"wheat_loopProof";

val _ = set_grammar_ancestry ["wheatSem"];

Definition every_prog_def:
  (every_prog p (Seq p1 p2) <=>
    p (Seq p1 p2) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Loop l1 body l2) <=>
    p (Loop l1 body l2) /\ every_prog p body) /\
  (every_prog p (If x1 x2 x3 p1 p2 l1) <=>
    p (If x1 x2 x3 p1 p2 l1) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Mark p1) <=>
    p (Mark p1) /\ every_prog p p1) /\
  (every_prog p (Call ret dest args handler) <=>
    p (Call ret dest args handler) /\
    (case handler of SOME (n,q,r,l) => every_prog p q ∧ every_prog p r | NONE => T)) /\
  (every_prog p prog <=> p prog)
End

Definition no_Loop_def:
  no_Loop = every_prog (\q. !l1 x l2. q <> Loop l1 x l2)
End

Definition syntax_ok_def:
  (syntax_ok (Seq p1 p2) <=>
    ~(no_Loop (Seq p1 p2)) ∧ syntax_ok p1 /\ syntax_ok p2) /\
  (syntax_ok (Loop l1 body l2) <=>
    syntax_ok body) /\
  (syntax_ok (If x1 x2 x3 p1 p2 l1) <=>
    ~(no_Loop (If x1 x2 x3 p1 p2 l1)) ∧ syntax_ok p1 /\ syntax_ok p2) /\
  (syntax_ok (Mark p1) <=>
    no_Loop p1) /\
  (syntax_ok (Call ret dest args handler) <=>
    ~(no_Loop (Call ret dest args handler)) ∧
    (case handler of SOME (n,q,r,l) => syntax_ok q ∧ syntax_ok r | NONE => F)) /\
  (syntax_ok prog <=> F)
End

Definition mark_all_def:
  (mark_all (Seq p1 p2) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark (Seq p1 p2) else Seq p1 p2, t3)) /\
  (mark_all (Loop l1 body l2) =
     let (body,t1) = mark_all body in
       (Loop l1 body l2, F)) /\
  (mark_all (If x1 x2 x3 p1 p2 l1) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let p3 = If x1 x2 x3 p1 p2 l1 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark p3 else p3, t3)) /\
  (mark_all (Mark p1) = mark_all p1) /\
  (mark_all (Call ret dest args handler) =
     case handler of
     | NONE => (Mark (Call ret dest args handler), T)
     | SOME (n,p1,p2,l) =>
         let (p1,t1) = mark_all p1 in
         let (p2,t2) = mark_all p2 in
         let t3 = (t1 ∧ t2) in
         let p3 = Call ret dest args (SOME (n,p1,p2,l)) in
           (if t3 then Mark p3 else p3, t3)) /\
  (mark_all prog = (Mark prog,T))
End

Theorem evaluate_Loop_body_same:
  (∀(s:('a,'b)state). evaluate (body,s) = evaluate (body',s)) ⇒
  ∀(s:('a,'b)state). evaluate (Loop l1 body l2,s) = evaluate (Loop l1 body' l2,s)
Proof
  rw [] \\ completeInduct_on ‘s.clock’
  \\ rw [] \\ fs [PULL_EXISTS,PULL_FORALL]
  \\ once_rewrite_tac [evaluate_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ first_x_assum match_mp_tac
  \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def]
  \\ rveq \\ fs [dec_clock_def]
  \\ imp_res_tac evaluate_clock \\ fs [dec_clock_def]
QED

Theorem mark_all_syntax_ok:
  ∀prog q b.
     mark_all prog = (q,b) ==>
     b = no_Loop q ∧ syntax_ok q
Proof
  recInduct mark_all_ind \\ rpt conj_tac
  \\ rpt gen_tac \\ strip_tac
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC
    \\ fs [evaluate_def,every_prog_def,no_Loop_def,syntax_ok_def])
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [every_prog_def,no_Loop_def,syntax_ok_def])
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC \\ fs []
    \\ fs [no_Loop_def,every_prog_def,syntax_ok_def])
  THEN1 fs [mark_all_def,syntax_ok_def]
  THEN1
   (fs [mark_all_def] \\ rveq
    \\ every_case_tac \\ fs []
    \\ fs [no_Loop_def,every_prog_def,syntax_ok_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC \\ fs []
    \\ fs [every_prog_def,syntax_ok_def,no_Loop_def])
  \\ fs [mark_all_def] \\ rveq
  \\ fs [every_prog_def,no_Loop_def,syntax_ok_def]
QED

Theorem mark_all_evaluate:
  ∀prog q b.
     mark_all prog = (q,b) ==>
     ∀s. evaluate (prog,s) = evaluate (q,s)
Proof
  recInduct mark_all_ind \\ rpt conj_tac
  \\ rpt gen_tac \\ strip_tac
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC \\ fs [evaluate_def])
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ match_mp_tac evaluate_Loop_body_same \\ fs [])
  THEN1
   (fs [mark_all_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC \\ fs []
    \\ fs [every_prog_def,evaluate_def]
    \\ fs [no_Loop_def,every_prog_def]
    \\ rw [] \\ every_case_tac \\ fs [])
  THEN1 fs [mark_all_def,evaluate_def]
  THEN1
   (fs [mark_all_def] \\ rveq
    \\ every_case_tac \\ fs []
    \\ fs [no_Loop_def,every_prog_def,evaluate_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC \\ fs []
    \\ fs [every_prog_def,evaluate_def])
  \\ fs [mark_all_def] \\ rveq
  \\ simp [evaluate_def]
  \\ fs [every_prog_def,no_Loop_def]
QED

Definition comp_no_loop_def:
  (comp_no_loop p (Seq p1 p2) =
    Seq (comp_no_loop p p1) (comp_no_loop p p2)) /\
  (comp_no_loop p (If x1 x2 x3 p1 p2 l1) =
    If x1 x2 x3 (comp_no_loop p p1) (comp_no_loop p p2) l1) /\
  (comp_no_loop p (Call ret dest args handler) =
    Call ret dest args
      (case handler of
       | SOME (n,q,r,l) => SOME (n, comp_no_loop p q, comp_no_loop p r, l)
       | NONE => NONE)) /\
  (comp_no_loop p Break = FST p) /\
  (comp_no_loop p Continue = SND p) /\
  (comp_no_loop p (Mark prog) = comp_no_loop p prog) /\
  (comp_no_loop p (Loop l1 b l2) = Fail) /\
  (comp_no_loop p prog = prog)
End

Definition store_cont_def:
  store_cont live code (n,funs) =
    let params = MAP FST (toSortedAList live) in
    let funs = (n,params,code) :: funs in
    let cont = Call NONE (SOME n) params NONE in
      (cont:'a wheatLang$prog, (n+1,funs))
End

Definition comp_with_loop_def:
  (comp_with_loop p (Seq p1 p2) cont s =
     let (q2,s) = comp_with_loop p p2 cont s in
       comp_with_loop p p1 q2 s) ∧
  (comp_with_loop p (If x1 x2 x3 p1 p2 l1) cont s =
     let (cont,s) = store_cont l1 cont s in
     let (q1,s) = comp_with_loop p p1 cont s in
     let (q2,s) = comp_with_loop p p2 cont s in
       (If x1 x2 x3 q1 q2 LN,s)) /\
  (comp_with_loop p (Call ret dest args handler) cont s =
     case handler of
     | NONE => (Seq (Call ret dest args NONE) cont,s)
     | SOME (n,q,r,l) =>
         let (cont,s) = store_cont l cont s in
         let (q,s) = comp_with_loop p q cont s in
         let (r,s) = comp_with_loop p r cont s in
           (Call ret dest args (SOME (n,q,r,l)),s)) /\
  (comp_with_loop p Break cont s = (FST p,s)) /\
  (comp_with_loop p Continue cons s = (SND p,s)) /\
  (comp_with_loop p (Mark prog) cont s = (Seq (comp_no_loop p prog) cont,s)) /\
  (comp_with_loop p (Loop live_in body live_out) cont s =
     let (cont,s) = store_cont live_out cont s in
     let params = MAP FST (toSortedAList live_in) in
     let (n,funs) = s in
     let enter = Call NONE (SOME n) params NONE in
     let (body,m,funs) = comp_with_loop (cont,enter) body Fail (n+1,funs) in
     let funs = (n,params,body) :: funs in
       (enter,(m,funs))) ∧
  (comp_with_loop p prog cont s = (Fail,s)) (* impossible case *)
End

Definition comp_def:
  comp (name,params,prog) s =
    let (body,n,funs) = comp_with_loop (Fail,Fail) prog Fail s in
      (n,(name,params,body)::funs)
End

Definition comp_all_def:
  comp_all code =
    let n = FOLDR MAX 0 (MAP FST code) + 1 in
      SND (FOLDR comp (n,[]) code)
End

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
  breaks_ok (p:'a wheatLang$prog,q:'a wheatLang$prog) <=> break_ok p ∧ break_ok q
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
  val ind_thm = wheatSemTheory.evaluate_ind
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
  ^(get_goal "wheatLang$Skip") ∧
  ^(get_goal "wheatLang$Fail") ∧
  ^(get_goal "wheatLang$Tick")
Proof
  fs [syntax_ok_def,comp_no_loop_def,evaluate_def]
  \\ rw [] \\ fs []
  \\ fs [state_rel_def,call_env_def,dec_clock_def]
  \\ rveq \\ fs [state_component_equality]
  \\ rw [] \\ res_tac
QED

Theorem compile_Continue:
  ^(get_goal "wheatLang$Continue") ∧
  ^(get_goal "wheatLang$Break")
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
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ rename [‘evaluate (pp,t)’]
  \\ Cases_on ‘evaluate (pp,t)’ \\ fs [cut_res_def,cut_state_def]
  \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ rfs []
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
  ^(get_goal "wheatLang$Return") ∧
  ^(get_goal "wheatLang$Raise")
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
    ∃vals. get_vars (MAP FST (toSortedAList live_in)) t = SOME vals ∧
           LENGTH vals = LENGTH (toSortedAList live_in) ∧
           fromAList (ZIP (MAP FST (toSortedAList live_in),vals)) =
           inter t.locals live_in
Proof
  rw []
  \\ ‘∀i x. MEM (i,x) (toSortedAList live_in) ⇔ lookup i live_in = SOME x’ by fs [MEM_toSortedAList]
  \\ ‘domain live_in = set (MAP FST (toSortedAList live_in))’
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

Theorem evaluate_no_Break_Continue:
  ∀prog s res t.
    evaluate (prog, s) = (res,t) ∧
    every_prog (\r. r ≠ Break ∧ r ≠ Continue) prog ⇒
    res ≠ SOME Break ∧ res ≠ SOME Continue
Proof
  recInduct evaluate_ind \\ fs [] \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ (rename [‘Loop’] ORELSE
    (fs [evaluate_def,CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"ffi_result"]
     \\ rveq \\ fs []))
  \\ rpt gen_tac \\ TRY strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [every_prog_def]
  \\ fs [CaseEq"bool"] \\ rveq \\ fs []
  THEN1
   (Cases_on ‘word_cmp cmp x y’ \\ fs []
    \\ rename [‘evaluate (xx,s)’] \\ Cases_on ‘evaluate (xx,s)’ \\ fs []
    \\ Cases_on ‘x’ \\ fs [cut_res_def,CaseEq"option",CaseEq"bool"] \\ rveq \\ fs [])
  THEN1
   (qpat_x_assum ‘evaluate _ = _’ mp_tac
    \\ once_rewrite_tac [evaluate_def]
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC \\ fs []
    \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def] \\ rveq \\ fs []
    \\ rw [] \\ fs [CaseEq"option",CaseEq"bool",CaseEq"prod",CaseEq"result"]
    \\ rveq \\ fs [])
  \\ fs [CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
  THEN1
   (fs [CaseEq"bool"] \\ rveq \\ fs []
    \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option"] \\ rveq \\ fs [])
  \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option",cut_res_def]
  \\ rveq \\ fs [] \\ rename [‘cut_res _ xx’] \\ Cases_on ‘xx’ \\ fs []
  \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option",cut_res_def]
  \\ rveq \\ fs []
QED

Theorem compile_Loop:
  ^(get_goal "wheatLang$Loop")
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

Theorem compile_Call:
  ^(get_goal "syntax_ok (wheatLang$Call _ _ _ _)")
Proof
  fs [no_Loop_def,every_prog_def]
  \\ fs [GSYM no_Loop_def]
  \\ reverse (rpt strip_tac)
  THEN1 cheat
  \\ fs [syntax_ok_def]
  \\ Cases_on ‘handler’ \\ fs []
  \\ PairCases_on ‘x’ \\ fs []
  \\ cheat
QED

Theorem compile_If:
  ^(get_goal "wheatLang$If")
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
  ^(get_goal "syntax_ok (wheatLang$Seq _ _)")
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

Theorem compile_Assign:
  ^(get_goal "wheatLang$Assign") ∧
  ^(get_goal "wheatLang$LocValue")
Proof
  cheat
QED

Theorem compile_Store:
  ^(get_goal "wheatLang$Store") ∧
  ^(get_goal "wheatLang$LoadByte")
Proof
  cheat
QED

Theorem compile_StoreGlob:
  ^(get_goal "wheatLang$StoreGlob") ∧
  ^(get_goal "wheatLang$LoadGlob")
Proof
  cheat
QED

Theorem compile_FFI:
  ^(get_goal "wheatLang$FFI")
Proof
  cheat
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Continue,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_StoreGlob, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

val _ = export_theory();
