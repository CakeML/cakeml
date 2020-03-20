(*
  Correctness proof for loop_to_word
*)

open preamble loopLangTheory loopSemTheory loopPropsTheory wordSemTheory wordPropsTheory

val _ = new_theory"loop_to_wordProof";

val _ = set_grammar_ancestry ["loopSem","loopProps","wordSem"];

Definition assigned_vars_def:
  (assigned_vars (Seq p1 p2) l = assigned_vars p1 (assigned_vars p2 l)) ∧
  (assigned_vars Break l = (l:num_set)) ∧
  (assigned_vars Continue l = l) ∧
  (assigned_vars (Loop l1 body l2) l = assigned_vars body l) ∧
  (assigned_vars (If x1 x2 x3 p1 p2 l1) l = assigned_vars p1 (assigned_vars p2 l)) ∧
  (assigned_vars (Mark p1) l = assigned_vars p1 l) /\
  (assigned_vars Tick l = l) /\
  (assigned_vars Skip l = l) /\
  (assigned_vars Fail l = l) /\
  (assigned_vars (Raise v) l = l) /\
  (assigned_vars (Return v) l = l) /\
  (assigned_vars (Call ret dest args handler) l =
       case ret of
       | NONE => l
       | SOME (v,live) =>
         let l = insert v () l in
           case handler of
           | NONE => l
           | SOME (n,p1,p2,l1) =>
               assigned_vars p1 (assigned_vars p2 (insert n () l))) /\
  (assigned_vars (LocValue n m) l = insert n () l) /\
  (assigned_vars (Assign n exp) l = insert n () l) /\
  (assigned_vars (Store exp n) l = l) /\
  (assigned_vars (SetGlobal w exp) l = l) /\
  (assigned_vars (LoadByte n w m) l = insert m () l) /\
  (assigned_vars (StoreByte n w m) l = l) /\
  (assigned_vars (FFI name n1 n2 n3 n4 live) l = l)
End

Theorem assigned_vars_acc:
  ∀p l.
    domain (assigned_vars p l) = domain (assigned_vars p LN) UNION domain l
Proof
  qsuff_tac ‘∀p (l:num_set) l.
    domain (assigned_vars p l) = domain (assigned_vars p LN) UNION domain l’
  THEN1 metis_tac []
  \\ ho_match_mp_tac assigned_vars_ind \\ rw [] \\ fs []
  \\ ntac 4 (once_asm_rewrite_tac [assigned_vars_def])
  \\ simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM]
  \\ every_case_tac
  \\ simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM]
  \\ once_rewrite_tac [INSERT_SING_UNION]
  \\ simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM]
  \\ rpt (pop_assum (fn th => mp_tac (SIMP_RULE std_ss [] th)))
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ disch_then (fn th => ntac 6 (once_rewrite_tac [th]))
  \\ simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM] \\ fs [EXTENSION] \\ metis_tac []
QED

Definition find_var_def:
  find_var ctxt v =
    case lookup v ctxt of
    | NONE => 0
    | SOME n => (n:num)
End

Definition toNumSet_def:
  toNumSet [] = LN ∧
  toNumSet (n::ns) = insert n () (toNumSet ns)
End

Definition fromNumSet_def:
  fromNumSet t = MAP FST (toAList t)
End

Definition mk_new_cutset_def:
  mk_new_cutset ctxt (l:num_set) =
    insert 0 () (toNumSet (MAP (find_var ctxt) (fromNumSet l)))
End

Definition comp_exp_def :
  (comp_exp ctxt (loopLang$Const w) = wordLang$Const w) /\
  (comp_exp ctxt (Var n) = Var (find_var ctxt n)) /\
  (comp_exp ctxt (Lookup m) = Lookup (Temp m)) /\
  (comp_exp ctxt (Load exp) = Load (comp_exp ctxt exp)) /\
  (comp_exp ctxt (Shift s exp n) = Shift s (comp_exp ctxt exp) n) /\
  (comp_exp ctxt (Op op wexps) =
   let wexps = MAP (comp_exp ctxt) wexps in
   Op op wexps)
Termination
  WF_REL_TAC ‘measure (loopLang$exp_size (K 0) o SND)’
  \\ rw []
  \\ rename [‘MEM x xs’]
  \\ Induct_on ‘xs’ \\ fs []
  \\ fs [exp_size_def]
  \\ rw [] \\ fs []
End

Definition comp_def:
  (comp ctxt (Seq p1 p2) l =
    let (p1,l) = comp ctxt p1 l in
    let (p2,l) = comp ctxt p2 l in
      (wordLang$Seq p1 p2,l)) /\
  (comp ctxt Break l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt Continue l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt (Loop l1 body l2) l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt (If x1 x2 x3 p1 p2 l1) l =
    let (p1,l) = comp ctxt p1 l in
    let (p2,l) = comp ctxt p2 l in
      (Seq (If x1 x2 x3 p1 p2) Tick,l)) /\
  (comp ctxt (Mark p1) l = comp ctxt p1 l) /\
  (comp ctxt Tick l = (Tick,l)) /\
  (comp ctxt Skip l = (Skip,l)) /\
  (comp ctxt Fail l = (Skip,l)) /\
  (comp ctxt (Raise v) l = (Raise (find_var ctxt v),l)) /\
  (comp ctxt (Return v) l = (Return 0 (find_var ctxt v),l)) /\
  (comp ctxt (Call ret dest args handler) l =
     let args = MAP (find_var ctxt) args in
       case ret of
       | NONE (* tail-call *) => (wordLang$Call NONE dest (0::args) NONE,l)
       | SOME (v,live) =>
         let v = find_var ctxt v in
         let live = mk_new_cutset ctxt live in
         let new_l = (FST l, SND l+1) in
           case handler of
           | NONE => (wordLang$Call (SOME (v,live,Skip,l)) dest args NONE, new_l)
           | SOME (n,p1,p2,_) =>
              let (p1,l1) = comp ctxt p1 new_l in
              let (p2,l1) = comp ctxt p2 l1 in
              let new_l = (FST l1, SND l1+1) in
                (Seq (Call (SOME (v,live,p2,l)) dest args
                   (SOME (find_var ctxt n,p1,l1))) Tick, new_l)) /\
  (comp ctxt (LocValue n m) l = (LocValue (find_var ctxt n) m,l))  /\
  (comp ctxt (Assign n exp) l = (Assign (find_var ctxt n) (comp_exp ctxt exp),l)) /\
  (comp ctxt (Store exp v) l = (Store (comp_exp ctxt exp) (find_var ctxt v), l)) /\
  (comp ctxt prog l = (Skip,l)) (* TODO *)
End

Definition make_ctxt_def:
  make_ctxt n [] l = l ∧
  make_ctxt n (x::xs) l = make_ctxt (n+2:num) xs (insert x n l)
End

Definition compile_def:
  compile name params body =
    let vs = fromNumSet (difference (assigned_vars body LN) (toNumSet params)) in
    let ctxt = make_ctxt 2 (params ++ vs) LN in
      FST (comp ctxt body (name,2))
End

Definition locals_rel_def:
  locals_rel ctxt l1 l2 ⇔
    INJ (find_var ctxt) (domain ctxt) UNIV ∧
    (∀n m. lookup n ctxt = SOME m ==> m ≠ 0) ∧
    ∀n v. lookup n l1 = SOME v ⇒
          ∃m. lookup n ctxt = SOME m ∧ lookup m l2 = SOME v
End

Definition globals_rel_def:
  globals_rel g1 g2 =
    ∀n v. FLOOKUP g1 n = SOME v ⇒ FLOOKUP g2 (Temp n) = SOME v
End

Definition code_rel_def:
  code_rel s_code t_code =
    ∀name params body.
      lookup name s_code = SOME (params,body) ⇒
      lookup name t_code = SOME (LENGTH params+1, compile name params body) ∧
      no_Loops body ∧ ALL_DISTINCT params
End

Definition state_rel_def:
  state_rel s t <=>
    t.memory = s.memory ∧
    t.mdomain = s.mdomain ∧
    t.clock = s.clock ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    globals_rel s.globals t.store ∧
    code_rel s.code t.code
End

Theorem find_var_neq_0:
  var_name ∈ domain ctxt ∧ locals_rel ctxt l1 l2 ⇒
  find_var ctxt var_name ≠ 0
Proof
  fs [locals_rel_def,find_var_def] \\ rw []
  \\ Cases_on ‘lookup var_name ctxt’ \\ fs []
  \\ fs [domain_lookup] \\ res_tac \\ metis_tac []
QED

Theorem locals_rel_insert:
  locals_rel ctxt l1 l2 ∧ v IN domain ctxt ⇒
  locals_rel ctxt (insert v w l1) (insert (find_var ctxt v) w l2)
Proof
  fs [locals_rel_def,lookup_insert] \\ rw []
  \\ fs [CaseEq"bool"] \\ rveq \\ fs []
  \\ fs [domain_lookup,find_var_def]
  \\ res_tac \\ fs []
  \\ disj2_tac \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [INJ_DEF,domain_lookup]
  \\ first_x_assum (qspecl_then [‘v’,‘n’] mp_tac)
  \\ fs [] \\ fs [find_var_def]
QED

val goal =
  ``λ(prog, s). ∀res s1 t ctxt retv l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
      lookup 0 t.locals = SOME retv ∧ no_Loops prog ∧
      ~ (isWord retv) ∧
      domain (assigned_vars prog LN) ⊆ domain ctxt ⇒
      ∃t1 res1.
         evaluate (FST (comp ctxt prog l),t) = (res1,t1) ∧
         state_rel s1 t1 ∧
         case res of
         | NONE => res1 = NONE ∧ lookup 0 t1.locals = SOME retv ∧
                   locals_rel ctxt s1.locals t1.locals ∧
                   t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME (Result v) => res1 = SOME (Result retv v) ∧
                                     t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | SOME (Exception v) =>
            (res1 ≠ SOME Error ⇒ ∃u1 u2. res1 = SOME (Exception u1 u2)) ∧
            ∀r l1 l2. jump_exc (t1 with <| stack := t.stack;
                                           handler := t.handler |>) = SOME (r,l1,l2) ⇒
                      res1 = SOME (Exception (Loc l1 l2) v) ∧ r = t1
         | _ => F``

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
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ loopLang$Tick")
Proof
  rpt strip_tac
  THEN1 (
   fs [loopSemTheory.evaluate_def,comp_def,wordSemTheory.evaluate_def]
   \\ rveq
   \\ fs [])
  THEN1
   fs [loopSemTheory.evaluate_def,comp_def,wordSemTheory.evaluate_def]
  \\ fs [loopSemTheory.evaluate_def,comp_def,wordSemTheory.evaluate_def]
  \\ Cases_on ‘s.clock = 0’
  \\ fs []
  \\ rveq
  THEN1 (
   IF_CASES_TAC
   \\ fs [flush_state_def,state_rel_def]
   \\ rveq
   \\ fs []
   )
  \\ IF_CASES_TAC
  \\ fs [assigned_vars_def,state_rel_def,
         wordSemTheory.dec_clock_def,loopSemTheory.dec_clock_def]
QED

Theorem compile_Loop:
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  rpt strip_tac
  \\ fs [no_Loops_def,every_prog_def]
  \\ fs [no_Loop_def,every_prog_def]
QED

Theorem compile_Mark:
  ^(get_goal "comp _ (Mark _)")
Proof
  rpt strip_tac
  \\ fs [loopSemTheory.evaluate_def,comp_def,wordSemTheory.evaluate_def,
         no_Loops_def,assigned_vars_def,no_Loop_def,every_prog_def]
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return")
Proof
  rpt strip_tac
  \\ fs [loopSemTheory.evaluate_def,comp_def,wordSemTheory.evaluate_def]
  \\ Cases_on ‘lookup n s.locals’
  \\ fs []
  \\ rveq
  \\ TOP_CASE_TAC \\ fs [find_var_def,locals_rel_def,get_var_def]
  \\ res_tac
  \\ rveq
  \\ TOP_CASE_TAC \\ fs [isWord_def]
  \\ fs [flush_state_def,state_rel_def,loopSemTheory.call_env_def]
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  rpt strip_tac
  \\ fs [loopSemTheory.evaluate_def]
  \\ Cases_on ‘lookup r1 s.locals’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘get_var_imm ri s’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ fs [comp_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [wordSemTheory.evaluate_def]
  \\ pairarg_tac \\ fs []
  \\ fs [get_var_def]
  \\ Cases_on ‘lookup r1 t.locals’ \\ fs []
  THEN1 (
   rveq \\ fs []
   \\ cheat
   )
  \\ Cases_on ‘x’ \\ fs []
  THEN1 (
   Cases_on ‘get_var_imm ri t’ \\ fs []
   THEN1 (
    rveq \\ fs []
    \\ cheat
    )
   \\ cheat
   )
  \\ cheat

 (* \\ qabbrev_tac `resp = evaluate (if word_cmp cmp c c' then c1 else c2,s)`
  \\ PairCases_on ‘resp’ \\ fs [cut_res_def]
  \\ Cases_on ‘resp0 ≠ NONE’ \\ fs [] \\ rveq \\ fs []
  THEN1 (
   first_x_assum (qspecl_then [‘t’,‘ctxt’,‘retv’,‘l’] mp_tac)
   \\ impl_tac \\ fs []
   \\ fs [assigned_vars_def,no_Loops_def,no_Loop_def,every_prog_def]
   \\ cheat
   )
   \\ cheat
  *)
QED

Theorem compile_Seq:
  ^(get_goal "comp _ (loopLang$Seq _ _)")
Proof
  rpt strip_tac
  \\ fs [loopSemTheory.evaluate_def]
  \\ pairarg_tac \\ fs [comp_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [wordSemTheory.evaluate_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum (qspecl_then [‘t’,‘ctxt’,‘retv’,‘l’] mp_tac)
  \\ impl_tac THEN1
   (fs [] \\ conj_tac THEN1 (CCONTR_TAC \\ fs [])
    \\ fs [no_Loops_def,no_Loop_def,every_prog_def]
    \\ qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac
    \\ fs [assigned_vars_def]
    \\ once_rewrite_tac [assigned_vars_acc] \\ fs [])
  \\ fs [] \\ strip_tac
  \\ reverse (Cases_on ‘res'’)
  THEN1
   (fs [] \\ rveq \\ fs [] \\ Cases_on ‘x’ \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  \\ fs [] \\ rveq \\ fs []
  \\ rename [‘state_rel s2 t2’]
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘l'’ mp_tac)
  \\ impl_tac THEN1
   (qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac
    \\ fs [no_Loops_def,no_Loop_def,every_prog_def]
    \\ fs [assigned_vars_def]
    \\ once_rewrite_tac [assigned_vars_acc] \\ fs [])
  \\ fs [] \\ strip_tac \\ fs []
  \\ Cases_on ‘res’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
QED

Theorem lookup_not_NONE :
  ∀ n locals. lookup n locals ≠ NONE ⇒ ∃ v. lookup n locals = SOME v
Proof
  rpt strip_tac
  \\ rename [‘lookup n l’]
  \\ Cases_on ‘l’ \\ fs [lookup_def,miscTheory.IS_SOME_EXISTS]
  \\ fs [CaseEq "bool"]
  \\ Cases_on ‘n’ \\ fs []
  \\ metis_tac [miscTheory.IS_SOME_EXISTS,
                quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
QED

Theorem comp_exp_cc :
! ctxt x s t. state_rel s t /\ locals_rel ctxt s.locals t.locals /\ eval s x <> NONE ⇒
  word_exp t (comp_exp ctxt x) = eval s x
Proof
  ho_match_mp_tac comp_exp_ind \\ rw []
  \\ fs [comp_exp_def,word_exp_def,eval_def]
  THEN1 (
   fs [find_var_def,locals_rel_def]
   \\ drule lookup_not_NONE \\ rw []
   \\ first_x_assum drule
   \\ strip_tac \\ fs []
   )
  THEN1 (
   fs [state_rel_def,globals_rel_def]
   \\ Cases_on ‘FLOOKUP s.globals m’ \\ fs [])
  THEN1 (
   Cases_on ‘eval s x’ \\ fs []
   \\ Cases_on ‘x'’ \\ fs []
   \\ first_x_assum drule \\ fs []
   \\ strip_tac
   \\ fs [state_rel_def,wordSemTheory.mem_load_def,
          loopSemTheory.mem_load_def]
   )
  THEN1 (
   Cases_on ‘eval s' x’ \\ fs []
   \\ Cases_on ‘x'’ \\ fs []
   \\ first_x_assum drule \\ fs []
   )
  \\ Cases_on ‘the_words (MAP (λa. eval s a) wexps)’ \\ fs []
  \\ qsuff_tac ‘the_words (MAP (λa. word_exp t a) (MAP (λa. comp_exp ctxt a) wexps)) = SOME x’
  THEN1 fs []
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘wexps’
  \\ Induct \\ fs []
  \\ fs [the_words_def,CaseEq"option",CaseEq"word_loc",
         PULL_EXISTS,PULL_FORALL]
  \\ rpt strip_tac
  \\ cheat
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  rpt strip_tac
  \\ fs [loopSemTheory.evaluate_def,comp_def,
         wordSemTheory.evaluate_def]
  THEN1 (
   Cases_on ‘eval s exp’ \\ fs []
   \\ rveq \\ fs []
   \\ drule comp_exp_cc
   \\ disch_then drule
   \\ disch_then (qspec_then ‘exp’ mp_tac)
   \\ fs [loopSemTheory.set_var_def,wordSemTheory.set_var_def]
   \\ strip_tac
   \\ fs [state_rel_def]
   \\ CONJ_TAC
   THEN1 (
    fs [lookup_insert,CaseEq "bool",assigned_vars_def]
    \\ imp_res_tac find_var_neq_0 \\ fs []
    )
   \\ match_mp_tac locals_rel_insert
   \\ fs [assigned_vars_def]
   )
  \\ fs [CaseEq "bool"]
  \\ rveq \\ fs []
  \\ fs [state_rel_def,loopSemTheory.set_var_def,
         wordSemTheory.set_var_def]
  \\ rpt strip_tac
  THEN1 (
   fs [code_rel_def,domain_lookup,EXISTS_PROD]
   \\ metis_tac []
   )
  THEN1 (
   fs [lookup_insert,CaseEq "bool",assigned_vars_def]
   \\ imp_res_tac find_var_neq_0 \\ fs []
   )
  \\ match_mp_tac locals_rel_insert
  \\ fs [assigned_vars_def]
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
  ^(get_goal "loopLang$StoreByte")
Proof
 cheat
QED

Theorem compile_LoadByte:
  ^(get_goal "loopLang$LoadByte")
Proof
  cheat
QED

Theorem compile_SetGlobal:
  ^(get_goal "loopLang$SetGlobal")
Proof
  cheat
QED

Theorem compile_FFI:
  ^(get_goal "loopLang$FFI")
Proof
 cheat
QED

Theorem locals_rel_get_var:
  locals_rel ctxt l t.locals ∧ lookup n l = SOME w ⇒
  wordSem$get_var (find_var ctxt n) t = SOME w
Proof
  fs [locals_rel_def] \\ rw[] \\ res_tac
  \\ fs [find_var_def,get_var_def]
QED

Theorem locals_rel_get_vars:
  ∀argvars argvals.
    locals_rel ctxt s.locals t.locals ∧
    loopSem$get_vars argvars s = SOME argvals ⇒
    wordSem$get_vars (MAP (find_var ctxt) argvars) t = SOME argvals ∧
    LENGTH argvals = LENGTH argvars
Proof
  Induct \\ fs [loopSemTheory.get_vars_def,get_vars_def,CaseEq"option"]
  \\ rw [] \\ imp_res_tac locals_rel_get_var \\ fs []
QED

Theorem compile_Raise:
  ^(get_goal "loopLang$Raise")
Proof
  fs [comp_def,loopSemTheory.evaluate_def,CaseEq"option"]
  \\ rw [] \\ fs [evaluate_def]
  \\ imp_res_tac locals_rel_get_var \\ fs []
  \\ Cases_on ‘jump_exc t’ \\ fs []
  THEN1 (fs [jump_exc_def,state_rel_def,loopSemTheory.call_env_def])
  \\ fs [CaseEq"prod",PULL_EXISTS]
  \\ PairCases_on ‘x’ \\ fs [loopSemTheory.call_env_def]
  \\ pop_assum mp_tac
  \\ fs [CaseEq"option",CaseEq"prod",jump_exc_def,CaseEq"stack_frame",CaseEq"list"]
  \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ fs [state_rel_def]
QED

Triviality state_rel_IMP:
  state_rel s t ⇒ t.clock = s.clock
Proof
  fs [state_rel_def]
QED

Theorem set_fromNumSet:
  set (fromNumSet t) = domain t
Proof
  fs [fromNumSet_def,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,domain_lookup]
QED

Theorem domain_toNumSet:
  domain (toNumSet ps) = set ps
Proof
  Induct_on ‘ps’ \\ fs [toNumSet_def]
QED

Theorem domain_make_ctxt:
  ∀n ps l. domain (make_ctxt n ps l) = domain l UNION set ps
Proof
  Induct_on ‘ps’ \\ fs [make_ctxt_def] \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem make_ctxt_inj:
  ∀xs l n. (∀x y v. lookup x l = SOME v ∧ lookup y l = SOME v ⇒ x = y ∧ v < n) ⇒
           (∀x y v. lookup x (make_ctxt n xs l) = SOME v ∧
                    lookup y (make_ctxt n xs l) = SOME v ⇒ x = y)
Proof
  Induct_on ‘xs’ \\ fs [make_ctxt_def] \\ rw []
  \\ first_x_assum (qspecl_then [‘insert h n l’,‘n+2’] mp_tac)
  \\ impl_tac THEN1
   (fs [lookup_insert] \\ rw []
    \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
  \\ metis_tac []
QED

Triviality make_ctxt_APPEND:
  ∀xs ys n l.
    make_ctxt n (xs ++ ys) l =
    make_ctxt (n + 2 * LENGTH xs) ys (make_ctxt n xs l)
Proof
  Induct \\ fs [make_ctxt_def,MULT_CLAUSES]
QED

Triviality make_ctxt_NOT_MEM:
  ∀xs n l x. ~MEM x xs ⇒ lookup x (make_ctxt n xs l) = lookup x l
Proof
  Induct \\ fs [make_ctxt_def,lookup_insert]
QED

Theorem lookup_EL_make_ctxt:
  ∀params k n l.
    k < LENGTH params ∧ ALL_DISTINCT params ⇒
    lookup (EL k params) (make_ctxt n params l) = SOME (2 * k + n)
Proof
  Induct \\ Cases_on ‘k’ \\ fs [] \\ fs [make_ctxt_def,make_ctxt_NOT_MEM]
QED

Theorem lookup_make_ctxt_range:
  ∀xs m l n y.
    lookup n (make_ctxt m xs l) = SOME y ⇒
    lookup n l = SOME y ∨ m ≤ y
Proof
  Induct \\ fs [make_ctxt_def] \\ rw []
  \\ first_x_assum drule
  \\ fs [lookup_insert] \\ rw [] \\ fs []
QED

Theorem locals_rel_make_ctxt:
  ALL_DISTINCT params ∧ DISJOINT (set params) (set xs) ∧
  LENGTH params = LENGTH l ⇒
  locals_rel (make_ctxt 2 (params ++ xs) LN)
    (fromAList (ZIP (params,l))) (fromList2 (retv::l))
Proof
  fs [locals_rel_def] \\ rw []
  THEN1
   (fs [INJ_DEF,find_var_def,domain_lookup] \\ rw [] \\ rfs []
    \\ rveq \\ fs []
    \\ imp_res_tac (MP_CANON make_ctxt_inj) \\ fs [lookup_def])
  THEN1
   (Cases_on ‘lookup n (make_ctxt 2 (params ++ xs) LN)’ \\ simp []
    \\ drule lookup_make_ctxt_range \\ fs [lookup_def])
  \\ fs [lookup_fromAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ rfs [MEM_ZIP]  \\ rveq \\ fs [make_ctxt_APPEND]
  \\ rename [‘k < LENGTH _’]
  \\ ‘k < LENGTH params’ by fs []
  \\ drule EL_MEM \\ strip_tac
  \\ ‘~MEM (EL k params) xs’ by (fs [IN_DISJOINT] \\ metis_tac [])
  \\ fs [make_ctxt_NOT_MEM]
  \\ fs [lookup_EL_make_ctxt]
  \\ fs [lookup_fromList2,EVEN_ADD,EVEN_DOUBLE]
  \\ ‘2 * k + 2 = (SUC k) * 2’ by fs []
  \\ asm_rewrite_tac [MATCH_MP MULT_DIV (DECIDE “0 < 2:num”)]
  \\ fs [lookup_fromList]
QED

Theorem domain_mk_new_cutset_not_empty:
  domain (mk_new_cutset ctxt x1) ≠ ∅
Proof
  fs [mk_new_cutset_def]
QED

Theorem cut_env_mk_new_cutset:
  locals_rel ctxt l1 l2 ∧ domain x1 ⊆ domain l1 ∧ lookup 0 l2 = SOME y ⇒
  ∃env1. cut_env (mk_new_cutset ctxt x1) l2 = SOME env1 ∧
         locals_rel ctxt (inter l1 x1) env1
Proof
  fs [locals_rel_def,SUBSET_DEF,cut_env_def] \\ fs [lookup_inter_alt]
  \\ fs [mk_new_cutset_def,domain_toNumSet,MEM_MAP,set_fromNumSet,PULL_EXISTS]
  \\ fs [DISJ_IMP_THM,PULL_EXISTS]
  \\ strip_tac \\ fs [domain_lookup]
  \\ rw [] \\ res_tac \\ fs [] \\ rveq \\ fs [find_var_def]
  \\ rw [] \\ res_tac \\ fs [] \\ rveq \\ fs [find_var_def]
  \\ disj2_tac \\ qexists_tac ‘n’ \\ fs []
QED

Theorem env_to_list_IMP:
  env_to_list env1 t.permute = (l,permute) ⇒
  domain (fromAList l) = domain env1 ∧
  ∀x. lookup x (fromAList l) = lookup x env1
Proof
  strip_tac \\ drule env_to_list_lookup_equiv
  \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
QED

Theorem cut_env_mk_new_cutset_IMP:
  cut_env (mk_new_cutset ctxt x1) l1 = SOME l2 ⇒
  lookup 0 l2 = lookup 0 l1
Proof
  fs [cut_env_def] \\ rw []
  \\ fs [SUBSET_DEF,mk_new_cutset_def]
  \\ fs [lookup_inter_alt]
QED

Triviality LASTN_ADD_CONS:
  ~(LENGTH xs <= n) ⇒ LASTN (n + 1) (x::xs) = LASTN (n + 1) xs
Proof
  fs [LASTN_CONS]
QED

Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  rw [] \\ qpat_x_assum ‘evaluate _ = (res,_)’ mp_tac
  \\ simp [loopSemTheory.evaluate_def]
  \\ simp [CaseEq"option"]
  \\ strip_tac \\ fs []
  \\ rename [‘find_code _ _ _ = SOME x’]
  \\ PairCases_on ‘x’ \\ fs []
  \\ rename [‘find_code _ _ _ = SOME (new_env,new_code)’]
  \\ ‘~bad_dest_args dest (MAP (find_var ctxt) argvars)’ by
       (pop_assum kall_tac \\ Cases_on ‘dest’ \\ fs [bad_dest_args_def]
        \\ fs [loopSemTheory.find_code_def]
        \\ imp_res_tac locals_rel_get_vars \\ CCONTR_TAC \\ fs [])
  \\ Cases_on ‘ret’ \\ fs []
  THEN1
   (fs [comp_def,evaluate_def]
    \\ imp_res_tac locals_rel_get_vars \\ fs [add_ret_loc_def]
    \\ fs [get_vars_def,get_var_def]
    \\ simp [bad_dest_args_def,call_env_def,dec_clock_def]
    \\ ‘∃args1 prog1 ss1 name1 ctxt1 l1.
         find_code dest (retv::argvals) t.code t.stack_size = SOME (args1,prog1,ss1) ∧
         FST (comp ctxt1 new_code l1) = prog1 ∧
         lookup 0 (fromList2 args1) = SOME retv ∧
         locals_rel ctxt1 new_env (fromList2 args1) ∧ no_Loops new_code ∧
         domain (assigned_vars new_code LN) ⊆ domain ctxt1’ by
      (qpat_x_assum ‘_ = (res,_)’ kall_tac
       \\ Cases_on ‘dest’ \\ fs [loopSemTheory.find_code_def]
       THEN1
        (fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
         \\ rveq \\ fs [code_rel_def,state_rel_def]
         \\ first_x_assum drule \\ strip_tac \\ fs []
         \\ fs [find_code_def]
         \\ ‘∃x l. argvals = SNOC x l’ by metis_tac [SNOC_CASES]
         \\ qpat_x_assum ‘_ = Loc loc 0’ mp_tac
         \\ rveq \\ rewrite_tac [GSYM SNOC,LAST_SNOC,FRONT_SNOC] \\ fs []
         \\ strip_tac \\ rveq \\ fs []
         \\ simp [compile_def]
         \\ qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
         \\ qexists_tac ‘ctxt2’ \\ qexists_tac ‘ll2’ \\ fs []
         \\ conj_tac THEN1 fs [lookup_fromList2,lookup_fromList]
         \\ simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                  domain_difference,domain_toNumSet]
         \\ reverse conj_tac THEN1 fs [SUBSET_DEF]
         \\ match_mp_tac locals_rel_make_ctxt
         \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,
                domain_toNumSet,GSYM IMP_DISJ_THM])
       \\ fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
       \\ rveq \\ fs [code_rel_def,state_rel_def]
       \\ first_x_assum drule \\ strip_tac \\ fs []
       \\ fs [find_code_def]
       \\ simp [compile_def]
       \\ qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       \\ qexists_tac ‘ctxt2’ \\ qexists_tac ‘ll2’ \\ fs []
       \\ conj_tac THEN1 fs [lookup_fromList2,lookup_fromList]
       \\ simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet]
       \\ reverse conj_tac THEN1 fs [SUBSET_DEF]
       \\ match_mp_tac locals_rel_make_ctxt
       \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,
              domain_toNumSet,GSYM IMP_DISJ_THM])
    \\ fs [] \\ imp_res_tac state_rel_IMP
    \\ fs [] \\ IF_CASES_TAC \\ fs []
    THEN1
     (fs [CaseEq"bool"] \\ rveq \\ fs []
      \\ fs [state_rel_def,flush_state_def])
    \\ Cases_on ‘handler = NONE’ \\ fs [] \\ rveq
    \\ Cases_on ‘evaluate (new_code,dec_clock s with locals := new_env)’ \\ fs []
    \\ Cases_on ‘q’ \\ fs []
    \\ Cases_on ‘x = Error’ \\ rveq \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
    \\ first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘retv’,‘l1’] mp_tac)
    \\ impl_tac
    THEN1 (fs [Abbr‘tt’] \\ fs [state_rel_def,loopSemTheory.dec_clock_def])
    \\ strip_tac \\ fs []
    \\ Cases_on ‘x’ \\ fs [] \\ rveq \\ fs []
    THEN1 fs [Abbr‘tt’]
    \\ qexists_tac ‘t1’ \\ fs []
    \\ qexists_tac ‘res1’ \\ fs []
    \\ conj_tac THEN1 (Cases_on ‘res1’ \\ simp [CaseEq"option"] \\ fs [])
    \\ rpt gen_tac \\ strip_tac \\ pop_assum mp_tac
    \\ qunabbrev_tac ‘tt’ \\ fs [])
  \\ fs [comp_def,evaluate_def]
  \\ imp_res_tac locals_rel_get_vars \\ fs [add_ret_loc_def]
  \\ fs [get_vars_def,get_var_def]
  \\ simp [bad_dest_args_def,call_env_def,dec_clock_def]
  \\ PairCases_on ‘x’ \\ PairCases_on ‘l’
  \\ fs [] \\ imp_res_tac state_rel_IMP
  \\ ‘∃args1 prog1 ss1 name1 ctxt1 l2.
         find_code dest (Loc l0 l1::argvals) t.code t.stack_size = SOME (args1,prog1,ss1) ∧
         FST (comp ctxt1 new_code l2) = prog1 ∧
         lookup 0 (fromList2 args1) = SOME (Loc l0 l1) ∧
         locals_rel ctxt1 new_env (fromList2 args1) ∧ no_Loops new_code ∧
         domain (assigned_vars new_code LN) ⊆ domain ctxt1’ by
    (qpat_x_assum ‘_ = (res,_)’ kall_tac
     \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
     \\ Cases_on ‘dest’ \\ fs [loopSemTheory.find_code_def]
     THEN1
      (fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
       \\ rveq \\ fs [code_rel_def,state_rel_def]
       \\ first_x_assum drule \\ strip_tac \\ fs []
       \\ fs [find_code_def]
       \\ ‘∃x l. argvals = SNOC x l’ by metis_tac [SNOC_CASES]
       \\ qpat_x_assum ‘_ = Loc loc 0’ mp_tac
       \\ rveq \\ rewrite_tac [GSYM SNOC,LAST_SNOC,FRONT_SNOC] \\ fs []
       \\ strip_tac \\ rveq \\ fs []
       \\ simp [compile_def]
       \\ qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       \\ qexists_tac ‘ctxt2’ \\ qexists_tac ‘ll2’ \\ fs []
       \\ conj_tac THEN1 fs [lookup_fromList2,lookup_fromList]
       \\ simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet]
       \\ reverse conj_tac THEN1 fs [SUBSET_DEF]
       \\ match_mp_tac locals_rel_make_ctxt
       \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,
              domain_toNumSet,GSYM IMP_DISJ_THM])
     \\ fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
     \\ rveq \\ fs [code_rel_def,state_rel_def]
     \\ first_x_assum drule \\ strip_tac \\ fs []
     \\ fs [find_code_def]
     \\ simp [compile_def]
     \\ qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
     \\ qexists_tac ‘ctxt2’ \\ qexists_tac ‘ll2’ \\ fs []
     \\ conj_tac THEN1 fs [lookup_fromList2,lookup_fromList]
     \\ simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
              domain_difference,domain_toNumSet]
     \\ reverse conj_tac THEN1 fs [SUBSET_DEF]
     \\ match_mp_tac locals_rel_make_ctxt
     \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,
            domain_toNumSet,GSYM IMP_DISJ_THM])
  \\ Cases_on ‘handler’ \\ fs []
  THEN1
   (fs [evaluate_def,add_ret_loc_def,domain_mk_new_cutset_not_empty,cut_res_def]
    \\ fs [loopSemTheory.cut_state_def]
    \\ Cases_on ‘domain x1 ⊆ domain s.locals’ \\ fs []
    \\ qpat_x_assum ‘locals_rel _ s.locals _’ assume_tac
    \\ drule cut_env_mk_new_cutset
    \\ rpt (disch_then drule) \\ strip_tac \\ fs []
    \\ (IF_CASES_TAC \\ fs [] THEN1 (rveq \\ fs [flush_state_def,state_rel_def]))
    \\ fs [CaseEq"prod",CaseEq"option"] \\ fs [] \\ rveq \\ fs []
    \\ rename [‘_ = (SOME res2,st)’]
    \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
    \\ fs [PULL_EXISTS]
    \\ Cases_on ‘res2 = Error’ \\ fs []
    \\ first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘Loc l0 l1’,‘l2’] mp_tac)
    \\ (impl_tac THEN1
         (fs [Abbr‘tt’,call_env_def,push_env_def,isWord_def]
          \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def,state_rel_def]))
    \\ strip_tac \\ fs []
    \\ Cases_on ‘res2’ \\ fs [] \\ rveq \\ fs []
    THEN1
     (fs [Abbr‘tt’,call_env_def,push_env_def,dec_clock_def]
      \\ pairarg_tac \\ fs [pop_env_def,set_var_def]
      \\ imp_res_tac env_to_list_IMP
      \\ fs [loopSemTheory.set_var_def,loopSemTheory.dec_clock_def]
      \\ fs [state_rel_def]
      \\ rename [‘find_var ctxt var_name’]
      \\ ‘var_name IN domain ctxt’ by fs [assigned_vars_def]
      \\ simp [lookup_insert]
      \\ imp_res_tac find_var_neq_0 \\ fs []
      \\ imp_res_tac cut_env_mk_new_cutset_IMP \\ fs []
      \\ match_mp_tac locals_rel_insert \\ fs []
      \\ fs [locals_rel_def])
    \\ qunabbrev_tac ‘tt’
    \\ pop_assum mp_tac
    \\ Cases_on ‘res1’ THEN1 fs []
    \\ disch_then (fn th => assume_tac (REWRITE_RULE [IMP_DISJ_THM] th))
    \\ fs [] \\ Cases_on ‘x’ \\ fs []
    \\ fs [state_rel_def]
    \\ fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs [dec_clock_def]
    \\ fs [jump_exc_def,NOT_LESS]
    \\ Cases_on ‘LENGTH t.stack <= t.handler’ \\ fs [LASTN_ADD_CONS]
    \\ simp [CaseEq"option",CaseEq"prod",CaseEq"bool",set_var_def,CaseEq"list",
             CaseEq"stack_frame"] \\ rw [] \\ fs [])
  \\ PairCases_on ‘x’ \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [evaluate_def,add_ret_loc_def,domain_mk_new_cutset_not_empty,cut_res_def]
  \\ fs [loopSemTheory.cut_state_def]
  \\ Cases_on ‘domain x1 ⊆ domain s.locals’ \\ fs []
  \\ qpat_x_assum ‘locals_rel _ s.locals _’ assume_tac
  \\ drule cut_env_mk_new_cutset
  \\ rpt (disch_then drule) \\ strip_tac \\ fs []
  \\ (IF_CASES_TAC \\ fs [] THEN1 (rveq \\ fs [flush_state_def,state_rel_def]))
  \\ fs [CaseEq"prod",CaseEq"option"] \\ fs [] \\ rveq \\ fs []
  \\ rename [‘_ = (SOME res2,st)’]
  \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
  \\ fs [PULL_EXISTS]
  \\ Cases_on ‘res2 = Error’ \\ fs []
  \\ first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘Loc l0 l1’,‘l2’] mp_tac)
  \\ (impl_tac THEN1
       (fs [Abbr‘tt’] \\ rename [‘SOME (find_var _ _,p1,l8)’]
        \\ PairCases_on ‘l8’ \\ fs [call_env_def,push_env_def,isWord_def]
        \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def,state_rel_def]))
  \\ strip_tac \\ fs []
  \\ Cases_on ‘res2’ \\ fs [] \\ rveq \\ fs []
  \\ fs [loopSemTheory.dec_clock_def]
  THEN1
   (rename [‘loopSem$set_var hvar w _’]
    \\ Cases_on ‘evaluate (x2,set_var hvar w (st with locals := inter s.locals x1))’
    \\ fs []
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ fs [pop_env_def,Abbr‘tt’] \\ fs [call_env_def,push_env_def]
    \\ rename [‘SOME (find_var _ _,p1,l8)’]
    \\ PairCases_on ‘l8’ \\ fs [call_env_def,push_env_def]
    \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def]
    \\ pop_assum mp_tac
    \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def]
    \\ reverse IF_CASES_TAC THEN1 (imp_res_tac env_to_list_IMP \\ fs [])
    \\ strip_tac \\ fs [] \\ pop_assum mp_tac \\ fs [set_var_def]
    \\ fs [cut_res_def]
    \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’ \\ strip_tac
    \\ first_x_assum (qspecl_then [‘tt’,‘ctxt’,‘retv’,‘l1'’] mp_tac)
    \\ impl_tac THEN1
     (fs [loopSemTheory.set_var_def,state_rel_def,Abbr‘tt’]
      \\ qpat_x_assum ‘_ SUBSET domain ctxt’ mp_tac
      \\ simp [assigned_vars_def]
      \\ once_rewrite_tac [assigned_vars_acc]
      \\ once_rewrite_tac [assigned_vars_acc] \\ fs [] \\ strip_tac
      \\ qpat_x_assum ‘no_Loops (Call _ _ _ _)’ mp_tac
      \\ simp [no_Loops_def,every_prog_def,no_Loop_def] \\ strip_tac
      \\ imp_res_tac env_to_list_IMP \\ fs []
      \\ fs [lookup_insert]
      \\ imp_res_tac find_var_neq_0 \\ fs []
      \\ imp_res_tac cut_env_mk_new_cutset_IMP \\ fs []
      \\ match_mp_tac locals_rel_insert \\ fs [locals_rel_def])
    \\ fs [] \\ strip_tac
    \\ Cases_on ‘q’ \\ fs [] \\ rveq \\ fs []
    THEN1
     (rename [‘cut_state names s9’]
      \\ fs [loopSemTheory.cut_state_def]
      \\ Cases_on ‘domain names ⊆ domain s9.locals’ \\ fs []
      \\ imp_res_tac state_rel_IMP \\ fs []
      \\ IF_CASES_TAC
      \\ fs [flush_state_def] \\ rveq \\ fs [] \\ fs [state_rel_def,dec_clock_def]
      \\ fs [loopSemTheory.dec_clock_def,Abbr‘tt’]
      \\ fs [locals_rel_def,lookup_inter_alt])
    \\ Cases_on ‘x’ \\ fs []
    THEN1 fs [Abbr‘tt’]
    \\ pop_assum mp_tac \\ rewrite_tac [IMP_DISJ_THM]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [Abbr‘tt’] \\ metis_tac [])
  THEN1
   (qpat_x_assum ‘∀x. _’ (assume_tac o REWRITE_RULE [IMP_DISJ_THM])
    \\ rename [‘loopSem$set_var hvar w _’]
    \\ Cases_on ‘evaluate (x1',set_var hvar w (st with locals := inter s.locals x1))’
    \\ fs []
    \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
    \\ fs [pop_env_def,Abbr‘tt’] \\ fs [call_env_def,push_env_def]
    \\ rename [‘SOME (find_var _ _,p1,l8)’]
    \\ PairCases_on ‘l8’ \\ fs [call_env_def,push_env_def]
    \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def]
    \\ pop_assum mp_tac
    \\ pairarg_tac \\ fs [dec_clock_def,loopSemTheory.dec_clock_def]
    \\ Cases_on ‘res1’ \\ fs [] \\ rveq \\ fs []
    \\ qpat_x_assum ‘∀x. _’ mp_tac
    \\ simp [jump_exc_def]
    \\ qmatch_goalsub_abbrev_tac ‘LASTN n1 xs1’
    \\ ‘LASTN n1 xs1 = xs1’  by
       (qsuff_tac ‘n1 = LENGTH xs1’ \\ fs [LASTN_LENGTH_ID]
        \\ unabbrev_all_tac \\ fs [])
    \\ fs [] \\ fs [Abbr‘n1’,Abbr‘xs1’] \\ strip_tac \\ rveq \\ fs []
    \\ ‘t1.locals = fromAList l ∧
        t1.stack = t.stack ∧ t1.handler = t.handler’ by fs [state_component_equality]
    \\ reverse IF_CASES_TAC THEN1 (imp_res_tac env_to_list_IMP \\ fs [] \\ rfs [])
    \\ strip_tac \\ fs []
    \\ pop_assum mp_tac \\ fs [set_var_def]
    \\ fs [cut_res_def]
    \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’ \\ strip_tac
    \\ first_x_assum (qspecl_then [‘tt’,‘ctxt’,‘retv’,‘(l0,l1 + 1)’] mp_tac)
    \\ impl_tac THEN1
     (fs [loopSemTheory.set_var_def,state_rel_def,Abbr‘tt’]
      \\ qpat_x_assum ‘_ SUBSET domain ctxt’ mp_tac
      \\ simp [assigned_vars_def]
      \\ once_rewrite_tac [assigned_vars_acc]
      \\ once_rewrite_tac [assigned_vars_acc] \\ fs [] \\ strip_tac
      \\ qpat_x_assum ‘no_Loops (Call _ _ _ _)’ mp_tac
      \\ simp [no_Loops_def,every_prog_def,no_Loop_def] \\ strip_tac
      \\ imp_res_tac env_to_list_IMP \\ fs []
      \\ fs [lookup_insert]
      \\ imp_res_tac find_var_neq_0 \\ fs []
      \\ imp_res_tac cut_env_mk_new_cutset_IMP \\ fs []
      \\ match_mp_tac locals_rel_insert \\ fs [locals_rel_def])
    \\ fs [] \\ strip_tac
    \\ Cases_on ‘q’ \\ fs [] \\ rveq \\ fs []
    THEN1
     (rename [‘cut_state names s9’]
      \\ fs [loopSemTheory.cut_state_def]
      \\ Cases_on ‘domain names ⊆ domain s9.locals’ \\ fs []
      \\ imp_res_tac state_rel_IMP \\ fs []
      \\ IF_CASES_TAC
      \\ fs [flush_state_def] \\ rveq \\ fs [] \\ fs [state_rel_def,dec_clock_def]
      \\ fs [loopSemTheory.dec_clock_def,Abbr‘tt’]
      \\ fs [locals_rel_def,lookup_inter_alt])
    \\ pop_assum (assume_tac o REWRITE_RULE [IMP_DISJ_THM])
    \\ Cases_on ‘x’ \\ fs []
    THEN1 fs [Abbr‘tt’]
    \\ rveq \\ fs []
    \\ pop_assum mp_tac
    \\ fs [Abbr‘tt’,jump_exc_def]
    \\ metis_tac [])
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Raise,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_SetGlobal, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop, compile_LoadByte])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

val _ = export_theory();
