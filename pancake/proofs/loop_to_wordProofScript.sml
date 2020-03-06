(*
  Correctness proof for loop_to_word
*)

open preamble loopLangTheory loopSemTheory loopPropsTheory wordSemTheory

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
  (assigned_vars prog l = l) (* TODO *)
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

Definition mk_new_cutset_def:
  mk_new_cutset ctxt (l:num_set) =
    insert 0 () (fromAList (MAP (λ(n,x). (find_var ctxt n,x)) (toAList l)))
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
                (Seq (Call (SOME (v,live,p1,l)) dest args
                   (SOME (find_var ctxt n,p1,l1))) Tick, new_l)) /\
  (comp ctxt prog l = (Skip,l)) (* TODO *)
End

Definition toNumSet_def:
  toNumSet [] = LN ∧
  toNumSet (n::ns) = insert n () (toNumSet ns)
End

Definition fromNumSet_def:
  fromNumSet t = MAP FST (toAList t)
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
    ∀n v. lookup n l1 = SOME v ⇒
          ∃m. lookup n ctxt = SOME m ∧ lookup m l2 = SOME v ∧ m ≠ 0
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

val goal =
  ``λ(prog, s). ∀res s1 t ctxt retv l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
      lookup 0 t.locals = SOME retv ∧ no_Loops prog ∧
      domain (assigned_vars prog LN) ⊆ domain ctxt ⇒
      ∃t1 res1.
         evaluate (FST (comp ctxt prog l),t) = (res1,t1) ∧
         state_rel s1 t1 ∧
         case res of
         | NONE => res1 = NONE ∧ lookup 0 t1.locals = SOME retv ∧
                   locals_rel ctxt s1.locals t1.locals
         | SOME (Result v) => res1 = SOME (Result retv v)
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | SOME (Exception v) => res1 ≠ NONE ∧
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
  cheat
QED

Theorem compile_Loop:
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  cheat
QED

Theorem compile_Mark:
  ^(get_goal "comp _ (Mark _)")
Proof
  cheat
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return")
Proof
  cheat
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  cheat
QED

Theorem compile_Seq:
  ^(get_goal "comp _ (loopLang$Seq _ _)")
Proof
  cheat
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  cheat
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
  ^(get_goal "loopLang$LoadByte")
Proof
  cheat
QED

Theorem compile_StoreGlob:
  ^(get_goal "loopLang$StoreGlob") ∧
  ^(get_goal "loopLang$LoadGlob")
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
  THEN1 (fs [jump_exc_def])
  \\ fs [CaseEq"prod",PULL_EXISTS]
  \\ PairCases_on ‘x’ \\ fs []
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
         \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,domain_toNumSet,GSYM IMP_DISJ_THM])
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
       \\ fs [IN_DISJOINT,set_fromNumSet,domain_difference,domain_toNumSet,GSYM IMP_DISJ_THM])
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
    \\ qexists_tac ‘t1’ \\ fs []
    \\ qexists_tac ‘res1’ \\ fs []
    \\ conj_tac THEN1 (Cases_on ‘res1’ \\ simp [CaseEq"option"] \\ fs [])
    \\ rpt gen_tac \\ strip_tac \\ pop_assum mp_tac
    \\ qunabbrev_tac ‘tt’ \\ fs [])
  \\ cheat
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Raise,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_StoreGlob, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

val _ = export_theory();
