(*
  Correctness proof for crep_arith pass
*)
Theory crep_arithProof
Ancestors
  wordSem
  crepSem crepProps crep_arith
Libs
  preamble

Theorem dest_2exp_bound:
  dest_2exp n w = SOME m ==> m = n + LOG2 w
Proof
  rw [dest_2exp_def] >> gvs []
QED

Theorem dest_2exp_bound':
  dest_2exp 0 w = SOME m /\ w < 2 ** bits ==> m < bits
Proof
  strip_tac >> imp_res_tac dest_2exp_thm >> gvs [EXP_BASE_LT_MONO]
QED

Theorem dest_const_thm:
  dest_const exp = SOME v ==> exp = Const v
Proof
  Cases_on `exp` \\ fs [dest_const_def]
QED

Theorem eval_mul_const:
  arch_width_bits aw = dimindex(:'a) /\
  eval (s:('a,'ffi) crepSem$state) exp = SOME (Word w) ==>
  eval s (mul_const aw exp c) = SOME (Word (w * i2w c))
Proof
  strip_tac >>
  simp [mul_const_def, GSYM dimword_def,
        GSYM integer_wordTheory.w2n_i2w] >>
  Cases_on ‘(i2w c:'a word) = 0w’ >>
  simp [eval_def, integer_wordTheory.i2w_0] >>
  Cases_on ‘w2n (i2w c:'a word) = 1’ >> simp []
  >- (
    ‘(i2w c:'a word) = 1w’ by metis_tac [n2w_w2n] >>
    simp []) >>
  Cases_on ‘dest_2exp 0 (w2n (i2w c:'a word))’ >>
  fs [eval_def, crep_op_def, OPT_MMAP_def, integer_wordTheory.i2w_pos] >>
  ‘x < dimindex(:'a)’ by
    metis_tac [dest_2exp_bound', w2n_lt, dimword_def] >>
  ‘x < dimword(:'a)’ by metis_tac [LESS_TRANS, dimindex_lt_dimword] >>
  imp_res_tac dest_2exp_thm >>
  ‘(i2w c:'a word) = n2w (2 ** x)’ by metis_tac [n2w_w2n] >>
  simp [LESS_MOD, wordSemTheory.word_sh_def, WORD_MUL_LSL]
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
  ! (s:('a,'ffi) crepSem$state) exp v.
  arch_width_bits aw = dimindex(:'a) /\
  crepSem$eval s exp <> NONE ==>
  eval (mapc f s) (simp_exp aw exp) = eval s exp
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
    \\ disch_then (qspec_then `eval (mapc f s) o simp_exp aw` mp_tac)
    \\ impl_tac \\ rw []
    \\ every_case_tac \\ gs [eval_def, MAP_EQ_CONS]
    \\ gvs [DISJ_IMP_THM, FORALL_AND_THM, OPT_MMAP_MAP_o, combinTheory.o_DEF]
    \\ every_case_tac \\ fs []
    \\ imp_res_tac dest_const_thm
    \\ Cases_on ‘op’
    \\ gvs [crep_op_def, eval_def, GSYM integer_wordTheory.word_i2w_mul]
    \\ irule eval_mul_const \\ simp []
  )
QED





Theorem simp_exp_correct:
  arch_width_bits aw = dimindex(:'a) /\
  crepSem$eval (s:('a,'ffi) crepSem$state) exp = SOME v ==>
  eval (mapc f s) (simp_exp aw exp) = SOME v
Proof
  rw [simp_exp_correct1]
QED

Theorem opt_mmap_simp_exp_correct:
  arch_width_bits aw = dimindex(:'a) /\
  OPT_MMAP (crepSem$eval (s:('a,'ffi) crepSem$state)) es = SOME vs ⇒
  OPT_MMAP (eval (mapc f s)) (MAP (simp_exp aw) es) = SOME vs
Proof
  strip_tac \\ fs[OPT_MMAP_MAP_o]
  \\ qpat_assum `OPT_MMAP _ _ = _` $ REWRITE_TAC o single o GSYM
  \\ irule OPT_MMAP_CONG \\ rw[]
  \\ imp_res_tac pan_commonPropsTheory.opt_mmap_mem_func \\ gvs[simp_exp_correct]
QED

Overload mapcs[local] = ``\aw. mapc (\(s,n,p). (n, simp_prog aw p))``

Theorem lookup_code[local]:
  lookup_code (FMAP_MAP2 (\(s,n,p). (n, simp_prog aw p)) c) fname args len =
  OPTION_MAP (simp_prog aw ## I) (lookup_code c fname args len)
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
  ! p (s:('a,'ffi) crepSem$state) r s'.
  arch_width_bits aw = dimindex(:'a) /\
  crepSem$evaluate (p, s) = (r, s') ==>
  r <> SOME Error ==>
  evaluate (simp_prog aw p, mapcs aw s) = (r, mapcs aw s')
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
    \\ TRY (rename [`Case (Call (SOME (_, handler)) _ _ )`] \\ Cases_on `handler`)
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
  \\ fs [sh_mem_op_code, opt_mmap_simp_exp_correct]
QED
