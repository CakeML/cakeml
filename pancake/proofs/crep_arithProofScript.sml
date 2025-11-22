(*
  Correctness proof for crep_arith pass
*)
Theory crep_arithProof
Ancestors
  crepSem crepProps crep_arith
Libs
  preamble


Theorem dest_const_thm:
  dest_const exp = SOME v ==> exp = Const v
Proof
  Cases_on `exp` \\ fs [dest_const_def]
QED

Theorem eval_mul_const:
  eval s exp = SOME (Word w) ==>
  eval s (mul_const exp c) = SOME (Word (w * c))
Proof
  simp [mul_const_def]
  \\ every_case_tac
  \\ fs [eval_def, crep_op_def]
  \\ imp_res_tac dest_2exp_thm
  \\ simp [wordLangTheory.word_sh_def, wordsTheory.WORD_MUL_LSL]
  \\ CCONTR_TAC \\ fs []
QED

Theorem OPT_MMAP_EQ_SOME_MONO[local]:
  OPT_MMAP f xs = SOME y ==>
  (! x z. MEM x xs ==> f x = SOME z ==> g x = SOME z) ==>
  OPT_MMAP g xs = SOME y
Proof
  rw []
  \\ irule EQ_TRANS
  \\ irule_at Any OPT_MMAP_CONG
  \\ simp []
  \\ qexists_tac `f`
  \\ rw []
  \\ imp_res_tac pan_commonPropsTheory.opt_mmap_mem_func
  \\ res_tac
  \\ fs []
QED

Overload mapc[local] = ``\f s. s with code := FMAP_MAP2 f s.code``

Theorem simp_exp_correct1[local]:
  ! s exp v.
  crepSem$eval s exp <> NONE ==>
  eval (mapc f s) (simp_exp exp) = eval s exp
Proof
  ho_match_mp_tac (name_ind_cases [] eval_ind)
  \\ rw []
  \\ fs [simp_exp_def]
  \\ imp_res_tac (IS_SOME_EXISTS |> REWRITE_RULE [IS_SOME_EQ_NOT_NONE])
  \\ fs [eval_def, CaseEq "option", CaseEq "word_lab"]
  \\ fs [FLOOKUP_FMAP_MAP2, mem_load_def]
  >~ [`Case (Op _ _)`]
  >- (
    qpat_x_assum `word_op _ _ = SOME _` (irule_at Any)
    \\ simp [OPT_MMAP_MAP_o]
    \\ drule_then irule OPT_MMAP_EQ_SOME_MONO
    \\ rw []
  )
  >~ [`Case (Crepop _ _)`]
  >- (
    drule OPT_MMAP_EQ_SOME_MONO
    \\ disch_then (qspec_then `eval (mapc f s) o simp_exp` mp_tac)
    \\ impl_tac \\ rw []
    \\ every_case_tac \\ gs [eval_def, MAP_EQ_CONS]
    \\ gvs [DISJ_IMP_THM, FORALL_AND_THM, OPT_MMAP_MAP_o, combinTheory.o_DEF]
    \\ every_case_tac \\ fs []
    \\ imp_res_tac dest_const_thm
    \\ TRY (irule EQ_TRANS \\ irule_at Any eval_mul_const)
    \\ Cases_on `op` \\ fs [crep_op_def, eval_def]
  )
QED

Theorem simp_exp_correct:
  crepSem$eval s exp = SOME v ==>
  eval (mapc f s) (simp_exp exp) = SOME v
Proof
  rw [simp_exp_correct1]
QED

Overload mapcs[local] = ``mapc (\(s,n,p). (n, simp_prog p))``

Theorem lookup_code[local]:
  lookup_code (FMAP_MAP2 (\(s,n,p). (n, simp_prog p)) c) fname args len =
  OPTION_MAP (simp_prog ## I) (lookup_code c fname args len)
Proof
  simp [lookup_code_def, FLOOKUP_FMAP_MAP2]
  \\ Cases_on `FLOOKUP c fname` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rw []
QED

Theorem sh_mem_op_code[local]:
  sh_mem_op op p addr (mapc f s) =
    (I ## mapc f) (sh_mem_op op p addr s)
Proof
  Cases_on `op` \\ fs [sh_mem_op_def, sh_mem_load_def, sh_mem_store_def]
  \\ every_case_tac \\ fs [set_var_def, empty_locals_def]
QED

Theorem ind_thm[local] = crepSemTheory.evaluate_ind
    |> Q.SPEC `UNCURRY Q`
    |> REWRITE_RULE [UNCURRY_DEF]
    |> Q.GEN `Q`


Theorem simp_prog_correct:
  ! p s r s'.
  crepSem$evaluate (p, s) = (r, s') ==>
  r <> SOME Error ==>
  evaluate (simp_prog p, mapcs s) = (r, mapcs s')
Proof
  ho_match_mp_tac (name_ind_cases [] ind_thm)
  \\ rw [simp_prog_def]
  >~ [`Case (While _ _)`]
  >~ [`Case (Call _ _ _)`]
  >- (
    fs [evaluate_def, UNCURRY_eq_pair, CaseEq "option", CaseEq "word_lab", CaseEq "prod"]
    \\ imp_res_tac simp_exp_correct
    \\ simp [OPT_MMAP_MAP_o]
    \\ drule_then (irule_at Any) OPT_MMAP_EQ_SOME_MONO
    \\ simp [simp_exp_correct, lookup_code]
    \\ fs [AllCaseEqs ()]
    \\ gvs [empty_locals_def, dec_clock_def]
    \\ TRY (rename [`Case (Call (SOME (_, _, handler)) _ _ )`] \\ Cases_on `handler`)
    \\ simp []
    \\ simp [PAIR_FST_SND_EQ]
  )
  >- (
    qpat_x_assum `evaluate _ = _` mp_tac
    \\ ONCE_REWRITE_TAC [evaluate_def]
    \\ strip_tac
    \\ fs [CaseEq "bool", CaseEq "prod", CaseEq "option", dec_clock_def] \\ gs []
    \\ drule_then (irule_at Any) simp_exp_correct
    \\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
    \\ simp [empty_locals_def]
  )
  \\ fs [evaluate_def, AllCaseEqs (), UNCURRY_eq_pair]
  \\ imp_res_tac simp_exp_correct
  \\ gvs [set_globals_def, empty_locals_def, dec_clock_def]
  \\ res_tac
  \\ rw [] \\ fs []
  \\ fs [sh_mem_op_code]
QED

