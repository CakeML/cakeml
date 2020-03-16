(*
  Correctness proof for loop_live
*)

open preamble loopLangTheory loopSemTheory loopPropsTheory
local open wordSemTheory in end

val _ = new_theory"loop_liveProof";

val _ = set_grammar_ancestry ["loopSem","loopProps"];

Theorem size_mk_BN:
  ∀t1 t2. size (mk_BN t1 t2) = size (BN t1 t2)
Proof
  Cases \\ Cases \\ fs [mk_BN_def,size_def]
QED

Theorem size_mk_BS:
  ∀t1 t2 x. size (mk_BS t1 x t2) = size (BS t1 x t2)
Proof
  Cases \\ Cases \\ fs [mk_BS_def,size_def]
QED

Theorem size_inter:
  ∀l1 l2. size (inter l1 l2) <= size l1
Proof
  Induct \\ fs [inter_def]
  \\ Cases_on ‘l2’ \\ fs [size_mk_BN,size_mk_BS]
  \\ rewrite_tac [ADD_ASSOC,DECIDE “m+1≤n+1 ⇔ m ≤ n:num”]
  \\ metis_tac [DECIDE “n1 ≤ m1 ∧ n2 ≤ m2 ⇒ n1+n2 ≤ m1+m2:num ∧  n1+n2 ≤ m1+m2+1”]
QED

Definition vars_of_exp_def:
  vars_of_exp (loopLang$Var v) l = insert v () l ∧
  vars_of_exp (Const _) l = l ∧
  vars_of_exp (Lookup _) l = l ∧
  vars_of_exp (Load a) l = vars_of_exp a l ∧
  vars_of_exp (Op x vs) l = vars_of_exp_list vs l ∧
  vars_of_exp (Shift _ x _) l = vars_of_exp x l ∧
  vars_of_exp_list xs l =
    (case xs of [] => l
     | (x::xs) => vars_of_exp x (vars_of_exp_list xs l))
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (x,_) => exp_size (K 0) x
                                   | INR (x,_) => exp1_size (K 0) x)’
End

Theorem exp_ind = vars_of_exp_ind
  |> Q.SPECL [‘λx l. P x’,‘λx l. Q x’]
  |> SIMP_RULE std_ss []
  |> Q.GENL [‘P’,‘Q’];

(* This optimisation shrinks all cutsets and also deletes assignments
   to unused variables. The Loop case is the interesting one: an
   auxiliary function is used to find a fixed-point. *)

Definition shrink_def:
  (shrink b (Seq p1 p2) l =
     let (p2,l) = shrink b p2 l in
     let (p1,l) = shrink b p1 l in
       (Seq p1 p2, l)) /\
  (shrink b (Loop live_in body live_out) l =
     let l2 = inter live_out l in
       case fixedpoint live_in LN l2 body of
       | SOME (body,l0) =>
           (let l = inter live_in l0 in (Loop l body l2, l))
       | NONE => let (b,_) = shrink (live_in,l2) body l2 in
                   (Loop live_in b l2, live_in)) /\
  (shrink b (If x1 x2 x3 p1 p2 l1) l =
     let l = inter l l1 in
     let (p1,l1) = shrink b p1 l in
     let (p2,l2) = shrink b p2 l in
     let l3 = (case x3 of Reg r => insert r () LN | _ => LN) in
       (If x1 x2 x3 p1 p2 l, insert x2 () (union l3 (union l1 l2)))) /\
  (shrink b (Mark p1) l = shrink b p1 l) /\
  (shrink b Break l = (Break,SND b)) /\
  (shrink b Continue l = (Continue,FST b)) /\
  (shrink b Fail l = (Fail,LN)) /\
  (shrink b Skip l = (Skip,l)) /\
  (shrink b (Return v) l = (Return v, insert v () LN)) /\
  (shrink b (Raise v) l = (Raise v, insert v () LN)) /\
  (shrink b (LocValue n m) l =
     case lookup n l of
     | NONE => (Skip,l)
     | SOME _ => (LocValue n m, delete n l)) ∧
  (shrink b (Assign n x) l =
     case lookup n l of
     | NONE => (Skip,l)
     | SOME _ => (Assign n x, vars_of_exp x (delete n l))) ∧
  (shrink b (Store e n) l =
    (Store e n, vars_of_exp e (insert n () l))) ∧
  (shrink b (SetGlobal name e) l =
    (SetGlobal name e, vars_of_exp e l)) ∧
  (shrink b (Call ret dest args handler) l =
     let a = fromAList (MAP (λx. (x,())) args) in
     case ret of
     | NONE => (Call NONE dest args NONE, union a l)
     | SOME (n,l1) =>
        case handler of
        | NONE => let l3 = (delete n (inter l l1)) in
                    (Call (SOME (n,l3)) dest args NONE, union a l3)
        | SOME (e,h,r,live_out) =>
            let (r,l2) = shrink b r l in
            let (h,l3) = shrink b h l in
            let l1 = inter l1 (union (delete n l2) (delete e l3)) in
              (Call (SOME (n,l1)) dest args (SOME (e,h,r,inter l live_out)),
               union a l1)) ∧
  (shrink b (FFI n r1 r2 r3 r4) l =
    (FFI n r1 r2 r3 r4, insert r1 () (insert r2 () (insert r3 () (insert r4 () l))))) ∧
  (shrink b prog l = (prog,l)) ∧
  (fixedpoint live_in l1 l2 body =
     let (b,l0) = shrink (inter live_in l1,l2) body l2 in
     let l0' = inter live_in l0 in
       if l0' = l1 then (* fixed point found! *) SOME (b,l0) else
       if size l0' ≤ size l1 then (* no progress made, not possible *) NONE else
         fixedpoint live_in l0' l2 body)
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I LEX measure I)
               (λx. case x of
                    | INL (_,c,_) => (prog_size (K 0) c, 0:num, 0)
                    | INR (live_in,l1,l2,body) =>
                        (prog_size (K 0) body, 1, size live_in - size l1))`
  \\ rw [] \\ fs [GSYM NOT_LESS]
  \\ qsuff_tac ‘size l1 < size live_in’ \\ fs []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs [size_inter]
End

Definition comp_def:
  comp prog = FST (shrink (LN,LN) prog LN)
End

Theorem fixedpoint_thm:
  ∀live_in l1 l2 (body:'a loopLang$prog) l0 b.
    fixedpoint live_in l1 l2 body = SOME (b, l0) ⇒
    shrink (inter live_in l0, l2) body l2 = (b, l0)
Proof
  qmatch_abbrev_tac ‘entire_goal’
  \\ qsuff_tac
    ‘(∀b (prog:'a loopLang$prog) l d. shrink b prog l = d ⇒ T) ∧ entire_goal’
  THEN1 fs []
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac shrink_ind \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ once_rewrite_tac [shrink_def]
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ fs [CaseEq"bool"] \\ rw [] \\ fs []
  \\ fs [inter_assoc]
  \\ pop_assum (fn th => rewrite_tac [GSYM th])
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC \\ fs []
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [domain_lookup]
  \\ Cases_on ‘lookup x live_in’ \\ fs []
QED

val goal =
  “λ(prog, s). ∀res s1 p l0 locals prog1 l1.
    evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
    shrink p prog l0 = (prog1,l1) ∧
    subspt (inter s.locals l1) locals ⇒
    ∃new_locals.
      evaluate (prog1,s with locals := locals) =
        (res,s1 with locals := new_locals) ∧
      case res of
      | NONE => subspt (inter s1.locals l0) new_locals
      | SOME Continue => subspt (inter s1.locals (FST p)) new_locals
      | SOME Break => subspt (inter s1.locals (SND p)) new_locals
      | _ => new_locals = s1.locals”

local
  val ind_thm = loopSemTheory.evaluate_ind |> ISPEC goal
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
  fs [shrink_def,evaluate_def] \\ fs [CaseEq"bool"] \\ rw []
  \\ fs [dec_clock_def,state_component_equality]
QED

Theorem compile_Continue:
  ^(get_goal "loopLang$Continue") ∧
  ^(get_goal "loopLang$Break")
Proof
  fs [shrink_def,evaluate_def]
  \\ fs [state_component_equality]
QED

Theorem compile_Mark:
  ^(get_goal "loopLang$Mark")
Proof
  fs [shrink_def,evaluate_def]
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return") ∧
  ^(get_goal "loopLang$Raise")
Proof
  fs [shrink_def,evaluate_def,CaseEq"option"] \\ rw []
  \\ fs [call_env_def] \\ fs [state_component_equality]
  \\ fs [subspt_lookup,lookup_inter_alt]
QED

Theorem compile_Seq:
  ^(get_goal "loopLang$Seq")
Proof
  fs [shrink_def,evaluate_def,CaseEq"option"] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rename [‘_ = (res7,s7)’]
  \\ reverse (Cases_on ‘res7’) \\ fs []
  THEN1
   (rveq \\ fs [] \\ first_x_assum drule
    \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [evaluate_def]
    \\ rveq \\ fs [] \\ fs [state_component_equality])
  \\ first_x_assum drule
  \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [evaluate_def]
QED

Triviality subspt_IMP_domain:
  subspt l1 l2 ⇒ domain l1 SUBSET domain l2
Proof
  fs [subspt_def,SUBSET_DEF]
QED

Theorem compile_Loop:
  ^(get_goal "loopLang$Loop")
Proof
  rpt gen_tac \\ disch_then assume_tac \\ fs [] \\ rpt gen_tac
  \\ once_rewrite_tac [evaluate_def]
  \\ once_rewrite_tac [shrink_def] \\ fs []
  \\ TOP_CASE_TAC
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1
   (fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"] \\ rveq \\ fs []
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ TRY (PairCases_on ‘v’ \\ fs [] \\ rveq \\ fs [])
    \\ once_rewrite_tac [evaluate_def] \\ fs [cut_res_def,cut_state_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt,SUBSET_DEF,domain_lookup]
    \\ res_tac \\ res_tac \\ rfs [])
  \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"prod",CaseEq"bool",dec_clock_def]
  \\ Cases_on ‘evaluate (body,r)’ \\ fs []
  \\ Cases_on ‘q’ THEN1 (rw[] \\ fs []) \\ fs [PULL_EXISTS]
  \\ reverse (Cases_on ‘fixedpoint live_in LN (inter live_out l0) body’) \\ fs []
  THEN1
   (strip_tac \\ rveq \\ fs []
    \\ drule fixedpoint_thm \\ strip_tac
    \\ rename [‘_ = (new_body,new_in)’]
    \\ once_rewrite_tac [evaluate_def]
    \\ fs [cut_res_def,cut_state_def]
    \\ reverse IF_CASES_TAC THEN1
     (qsuff_tac ‘F’ \\ fs [] \\ drule subspt_IMP_domain
      \\ fs [domain_inter,SUBSET_DEF] \\ metis_tac [])
    \\ fs [dec_clock_def]
    \\ Cases_on ‘x = Error’ \\ rveq \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘(_,s6)’
    \\ last_x_assum drule
    \\ disch_then (qspec_then ‘s6.locals’ mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs []
      \\ fs [subspt_lookup,lookup_inter_alt,domain_inter])
    \\ strip_tac \\ fs [Abbr‘s6’]
    \\ Cases_on ‘x’ \\ fs [] \\ rveq \\ fs []
    THEN1
     (Cases_on ‘domain live_out ⊆ domain r'.locals’ \\ fs []
      \\ reverse IF_CASES_TAC \\ fs [] THEN1
       (imp_res_tac subspt_IMP_domain \\ fs [domain_inter,SUBSET_DEF]
        \\ metis_tac [])
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
      \\ fs [state_component_equality]
      \\ fs [subspt_lookup,lookup_inter_alt,domain_inter])
    \\ first_x_assum (qspecl_then [‘p’,‘l0’] mp_tac)
    \\ once_rewrite_tac [shrink_def] \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ Cases_on ‘x = Error’ \\ rveq \\ fs []
  \\ once_rewrite_tac [evaluate_def]
  \\ fs [cut_res_def,cut_state_def]
  \\ reverse IF_CASES_TAC THEN1
   (qsuff_tac ‘F’ \\ fs [] \\ drule subspt_IMP_domain
    \\ fs [domain_inter,SUBSET_DEF] \\ metis_tac [])
  \\ fs [dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘(_,s6)’
  \\ last_x_assum drule
  \\ disch_then (qspec_then ‘s6.locals’ mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt,domain_inter])
  \\ strip_tac \\ fs [Abbr‘s6’]
  \\ Cases_on ‘x’ \\ fs [] \\ rveq \\ fs []
  THEN1
   (Cases_on ‘domain live_out ⊆ domain r'.locals’ \\ fs []
    \\ reverse IF_CASES_TAC \\ fs [] THEN1
     (imp_res_tac subspt_IMP_domain \\ fs [domain_inter,SUBSET_DEF]
      \\ metis_tac [])
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [state_component_equality]
    \\ fs [subspt_lookup,lookup_inter_alt,domain_inter])
  \\ first_x_assum (qspecl_then [‘p’,‘l0’] mp_tac)
  \\ once_rewrite_tac [shrink_def] \\ fs []
QED

Theorem vars_of_exp_acc:
  ∀(exp:'a loopLang$exp) l.
     domain (vars_of_exp exp l) =
     domain (union (vars_of_exp exp LN) l)
Proof
  qsuff_tac ‘
  (∀(exp:'a loopLang$exp) (l:num_set) l.
     domain (vars_of_exp exp l) =
     domain (union (vars_of_exp exp LN) l)) ∧
  (∀(exp:'a loopLang$exp list) (l:num_set) l x.
     domain (vars_of_exp_list exp l) =
     domain (union (vars_of_exp_list exp LN) l))’ THEN1 metis_tac []
  \\ ho_match_mp_tac vars_of_exp_ind \\ rw []
  \\ once_rewrite_tac [vars_of_exp_def]
  THEN1 fs [domain_insert,domain_union,EXTENSION]
  THEN1 fs [domain_insert,domain_union,EXTENSION]
  \\ TRY (rpt (pop_assum (qspec_then ‘l’ mp_tac)) \\ fs [] \\ NO_TAC)
  \\ TRY (rpt (pop_assum (qspec_then ‘l'’ mp_tac)) \\ fs [] \\ NO_TAC)
  \\ Cases_on ‘exp’ \\ fs []
  \\ simp_tac std_ss [domain_union]
  \\ rpt (pop_assum (fn th => once_rewrite_tac [th]))
  \\ simp_tac std_ss [domain_union]
  \\ fs [domain_insert,domain_union,EXTENSION] \\ metis_tac []
QED

Theorem eval_lemma:
  ∀s exp w l.
    eval s exp = SOME w ∧
    subspt (inter s.locals (vars_of_exp exp l)) locals ⇒
    eval (s with locals := locals) exp = SOME w
Proof
  ho_match_mp_tac eval_ind \\ rw [] \\ fs [eval_def]
  THEN1 fs [vars_of_exp_def,subspt_lookup,lookup_inter_alt]
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc",vars_of_exp_def,PULL_EXISTS] \\ rveq
    \\ res_tac \\ fs[] \\ fs [mem_load_def])
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc"] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [vars_of_exp_def]
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘wexps’ \\ fs [] \\ rw []
    \\ fs [wordSemTheory.the_words_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
    \\ rveq \\ fs [] \\ conj_tac
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    THEN1 (fs [Once vars_of_exp_def] \\ metis_tac [])
    \\ pop_assum mp_tac \\ simp [Once vars_of_exp_def]
    \\ rw [] THEN1 metis_tac []
    \\ fs [subspt_lookup,lookup_inter_alt]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [vars_of_exp_acc]
    \\ fs [domain_union])
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc",vars_of_exp_def,PULL_EXISTS] \\ rveq
    \\ res_tac \\ fs[] \\ fs [mem_load_def])
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LoadByte") ∧
  ^(get_goal "loopLang$SetGlobal") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  reverse (rw []) THEN1
   (fs [shrink_def,CaseEq"option"] \\ rveq \\ fs []
    THEN1
     (fs [evaluate_def,CaseEq"bool"] \\ rveq \\ fs [set_var_def]
      \\ fs [state_component_equality]
      \\ ‘~(r IN domain l0)’ by fs [domain_lookup]
      \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
      \\ rw [] \\ fs [])
    \\ fs [evaluate_def,CaseEq"bool"] \\ rveq \\ fs [set_var_def]
    \\ fs [state_component_equality]
    \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert] \\ rw [])
  \\ fs [shrink_def,CaseEq"option"] \\ rveq \\ fs []
  THEN1
   (fs [evaluate_def,CaseEq"option"] \\ rveq \\ fs [PULL_EXISTS,set_global_def]
    \\ fs [state_component_equality]
    \\ drule eval_lemma \\ disch_then drule \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union])
  THEN1
   (fs [evaluate_def,CaseEq"bool"] \\ rveq \\ fs [set_var_def,CaseEq"option"] (*
    \\ fs [state_component_equality] \\ rveq \\ fs []
    \\ ‘~(v IN domain l0)’ by fs [domain_lookup]
    \\ qpat_x_assum ‘insert _ _ _ = _’ (assume_tac o GSYM)
    \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
    \\ rw [] \\ fs [] *))
  THEN1
   (fs [evaluate_def,state_component_equality,CaseEq"option",set_var_def]
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_inter,CaseEq"option"]
    \\ rw [] \\ res_tac
    \\ qpat_x_assum ‘insert _ _ _ = _’ (assume_tac o GSYM)
    \\ fs [lookup_insert,CaseEq"bool"] \\ rveq \\ fs [])
  \\ fs [evaluate_def,CaseEq"option"] \\ rveq \\ fs []
  \\ fs [state_component_equality,set_var_def,PULL_EXISTS]
  \\ qexists_tac ‘w’ \\ fs []
  \\ reverse conj_tac THEN1
   (pop_assum mp_tac
    \\ fs [subspt_lookup,lookup_inter_alt]
    \\ fs [lookup_insert]
    \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union]
    \\ metis_tac [])
  \\ drule eval_lemma
  \\ disch_then drule \\ fs []
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rpt strip_tac \\ fs [] \\ rveq \\ fs []
  \\ Cases_on ‘evaluate (if word_cmp cmp x y then c1 else c2,s)’ \\ fs []
  \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
  \\ fs [shrink_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [evaluate_def]
  \\ ‘lookup r1 locals = SOME (Word x) ∧
      get_var_imm ri (s with locals := locals) = SOME (Word y)’ by
     (Cases_on ‘ri’ \\ fs [subspt_lookup,lookup_inter_alt,domain_union]
      \\ fs [get_var_imm_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘locals’ mp_tac)
  \\ (impl_tac THEN1 fs [subspt_lookup,lookup_inter_alt,domain_union])
  \\ strip_tac \\ fs []
  \\ (reverse (Cases_on ‘q’) \\ fs [cut_res_def]
  THEN1 (Cases_on ‘x'’ \\ fs [] \\ rveq \\ fs [] \\ fs [state_component_equality]))
  \\ fs [cut_state_def,CaseEq"option",CaseEq"bool"]
  \\ rveq \\ fs [] \\ fs [state_component_equality,domain_inter]
  \\ imp_res_tac subspt_IMP_domain
  \\ fs [domain_inter,domain_insert,domain_union,SUBSET_DEF]
  \\ fs [dec_clock_def]
  \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
QED

Theorem compile_Call:
  ^(get_goal "loopLang$Call")
Proof
  rw [] \\ fs [evaluate_def]
  \\ Cases_on ‘get_vars argvars s’ \\ fs []
  \\ Cases_on ‘find_code dest x s.code’ \\ fs []
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ fs []
  \\ ‘set argvars SUBSET domain l1’ by
   (Cases_on ‘ret’ \\ Cases_on ‘handler’ \\ fs [shrink_def,CaseEq"prod"]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs [domain_union,domain_fromAList,MAP_MAP_o,o_DEF,SUBSET_DEF])
  \\ ‘get_vars argvars (s with locals := locals) = SOME x’ by
    (pop_assum mp_tac \\ pop_assum kall_tac
     \\ ntac 2 (pop_assum mp_tac)
     \\ qid_spec_tac ‘x’
     \\ qid_spec_tac ‘argvars’ \\ rpt (pop_assum kall_tac)
     \\ Induct
     \\ fs [get_vars_def,CaseEq"option",PULL_EXISTS,PULL_FORALL]
     \\ rw [] \\ fs [subspt_lookup,lookup_inter_alt])
  \\ Cases_on ‘ret’ \\ fs []
  THEN1
   (Cases_on ‘handler’ \\ fs []
    \\ fs [shrink_def] \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [dec_clock_def] \\ fs [state_component_equality]
    \\ Cases_on ‘res’ \\ fs [] \\ fs [subspt_lookup,lookup_inter_alt]
    \\ Cases_on ‘x'’ \\ fs [] \\ fs [subspt_lookup,lookup_inter_alt])
  \\ rename [‘Call (SOME z)’] \\ PairCases_on ‘z’ \\ fs []
  \\ Cases_on ‘handler’ \\ fs [shrink_def] \\ rveq \\ fs []
  THEN1
   (fs [evaluate_def,cut_res_def,cut_state_def]
    \\ Cases_on ‘domain z1 ⊆ domain s.locals’ \\ fs []
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (imp_res_tac subspt_IMP_domain
      \\ fs [domain_inter,domain_union,domain_delete,SUBSET_DEF]
      \\ pop_assum mp_tac \\ fs [] \\ metis_tac [])
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [dec_clock_def]
    \\ fs [CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
    \\ fs [CaseEq"result"] \\ rveq \\ fs [set_var_def]
    \\ fs [state_component_equality]
    \\ fs [subspt_lookup,lookup_insert,lookup_inter_alt]
    \\ rw [] \\ fs [domain_inter,domain_union]
    \\ CCONTR_TAC \\ fs [])
  \\ PairCases_on ‘x'’ \\ fs []
  \\ fs [evaluate_def,cut_res_def,cut_state_def]
  \\ Cases_on ‘domain z1 ⊆ domain s.locals’ \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [evaluate_def,cut_res_def,cut_state_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1
   (imp_res_tac subspt_IMP_domain
    \\ fs [domain_inter,domain_union,domain_delete,SUBSET_DEF]
    \\ pop_assum mp_tac \\ fs [] \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [dec_clock_def,CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
  \\ qpat_x_assum ‘∀x. _’ kall_tac
  \\ fs [CaseEq"result"] \\ rveq \\ fs []
  \\ rpt (fs [state_component_equality] \\ NO_TAC)
  \\ fs [set_var_def]
  THEN1
   (qmatch_goalsub_abbrev_tac ‘evaluate (r1,st1)’
    \\ Cases_on ‘evaluate
         (x'2,st with locals := insert z0 retv (inter s.locals z1))’ \\ fs []
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then ‘st1.locals’ mp_tac)
    \\ impl_tac THEN1
     (fs [Abbr‘st1’,subspt_lookup,lookup_inter_alt,lookup_insert,
          domain_union,domain_inter] \\ rw [] \\ fs [])
    \\ strip_tac \\ fs []
    \\ unabbrev_all_tac \\ fs []
    \\ reverse (Cases_on ‘q’) \\ fs []
    THEN1
     (Cases_on ‘x'’ \\ fs [cut_res_def,state_component_equality]
      \\ Cases_on ‘res’ \\ fs []
      \\ Cases_on ‘x'’ \\ fs [] \\ fs [subspt_lookup])
    \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"]
    \\ fs [state_component_equality,domain_inter,domain_union,dec_clock_def]
    \\ fs [SUBSET_DEF] \\ rw []
    \\ rpt (qpat_x_assum ‘inter _ _ = _’ (assume_tac o GSYM)) \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
    \\ fs [domain_lookup] \\ res_tac \\ res_tac \\ fs [])
  THEN1
   (qmatch_goalsub_abbrev_tac ‘evaluate (r1,st1)’
    \\ Cases_on ‘evaluate
              (x'1,st with locals := insert x'0 exn (inter s.locals z1))’ \\ fs []
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then ‘st1.locals’ mp_tac)
    \\ impl_tac THEN1
     (fs [Abbr‘st1’,subspt_lookup,lookup_inter_alt,lookup_insert,
          domain_union,domain_inter] \\ rw [] \\ fs [])
    \\ strip_tac \\ fs []
    \\ unabbrev_all_tac \\ fs []
    \\ reverse (Cases_on ‘q’) \\ fs []
    THEN1
     (Cases_on ‘x'’ \\ fs [cut_res_def,state_component_equality]
      \\ Cases_on ‘res’ \\ fs []
      \\ Cases_on ‘x'’ \\ fs [] \\ fs [subspt_lookup])
    \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"]
    \\ fs [state_component_equality,domain_inter,domain_union,dec_clock_def]
    \\ fs [SUBSET_DEF] \\ rw []
    \\ rpt (qpat_x_assum ‘inter _ _ = _’ (assume_tac o GSYM)) \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
    \\ fs [domain_lookup] \\ res_tac \\ res_tac \\ fs [])
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store")
Proof
  rw [] \\ fs [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ fs [mem_store_def] \\ rveq \\ fs []
  \\ simp [state_component_equality]
  \\ drule eval_lemma
  \\ disch_then drule \\ fs []
  \\ fs [subspt_lookup,lookup_inter_alt]
  \\ qpat_x_assum ‘∀x. _’ mp_tac
  \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union]
  \\ strip_tac
  \\ ‘lookup v locals = SOME w’ by metis_tac [] \\ fs []
QED

Theorem compile_FFI:
  ^(get_goal "loopLang$FFI")
Proof
  fs [evaluate_def] \\ rw []
  \\ fs [CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [shrink_def] \\ rveq \\ fs []
  \\ fs [subspt_lookup,evaluate_def,lookup_inter_alt,domain_insert]
  \\ res_tac \\ fs [] \\ fs []
  \\ fs [CaseEq"ffi_result"]
  \\ simp [state_component_equality]
  \\ Cases_on ‘res’ \\ fs []
  \\ fs [SUBSET_DEF,call_env_def]
  \\ rveq \\ fs []
  \\ Cases_on ‘x’ \\ fs []
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Continue,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_Call, compile_Seq, compile_If, compile_FFI, compile_Loop])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

Theorem comp_correct:
  evaluate (prog,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  res ≠ SOME Break ∧
  res ≠ SOME Continue ∧
  res ≠ NONE ⇒
  evaluate (comp prog,s) = (res,s1)
Proof
  strip_tac
  \\ drule compile_correct \\ fs []
  \\ fs [comp_def]
  \\ Cases_on ‘shrink (LN,LN) prog LN’ \\ fs []
  \\ disch_then drule
  \\ disch_then (qspec_then ‘s.locals’ mp_tac)
  \\ impl_tac THEN1 fs [subspt_lookup,lookup_inter_alt]
  \\ strip_tac
  \\ ‘s with locals := s.locals = s’ by fs [state_component_equality] \\ fs []
  \\ fs [state_component_equality]
  \\ Cases_on ‘res’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
QED

val _ = export_theory();
