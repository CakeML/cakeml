(*
  Part of the correctness proof for data_to_word
*)
open preamble dataSemTheory dataPropsTheory copying_gcTheory
     int_bitwiseTheory data_to_word_memoryProofTheory finite_mapTheory
     data_to_wordTheory wordPropsTheory whileTheory
     set_sepTheory semanticsPropsTheory
     helperLib alignmentTheory blastLib word_bignumTheory wordLangTheory
     word_bignumProofTheory gen_gc_partialTheory gc_sharedTheory
     word_gcFunctionsTheory backendPropsTheory
local open gen_gcTheory in end

val _ = new_theory "data_to_word_gcProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = set_grammar_ancestry
  ["dataSem", "wordSem", "data_to_word", "backendProps",
   "data_to_word_memoryProof"
  ];

val shift_def = backend_commonTheory.word_shift_def
val isWord_def = wordSemTheory.isWord_def
val theWord_def = wordSemTheory.theWord_def
val is_fwd_ptr_def = wordSemTheory.is_fwd_ptr_def

Overload lookup[local] = “sptree$lookup”;

val _ = hide "next";

val drule = old_drule

(* TODO: move *)
Type state = ``:('a,'c,'ffi)wordSem$state``

fun op by1 (q,tac) = q by (tac \\ NO_TAC)
infix 8 by1

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

Theorem LESS_EQ_IMP_APPEND_ALT:
   ∀n xs. n ≤ LENGTH xs ⇒ ∃ys zs. xs = ys ++ zs ∧ LENGTH zs = n
Proof
  Induct \\ fs [LENGTH_NIL] \\ Cases_on `xs` \\ fs []
  \\ rw [] \\ res_tac \\ rveq
  \\ Cases_on `ys` \\ fs [] THEN1 (qexists_tac `[]` \\ fs [])
  \\ qexists_tac `BUTLAST (h::h'::t)` \\ fs []
  \\ qexists_tac `LAST (h::h'::t) :: zs` \\ fs []
  \\ fs [APPEND_FRONT_LAST]
QED

Theorem word_asr_dimindex:
   !w:'a word n. dimindex (:'a) <= n ==> (w >> n = w >> (dimindex (:'a) - 1))
Proof
  fs [word_asr_def,fcpTheory.CART_EQ,fcpTheory.FCP_BETA]
  \\ rw [] \\ Cases_on `i` \\ fs [] \\ rw [] \\ fs [word_msb_def]
QED

Theorem WORD_MUL_BIT0:
   !a b. (a * b) ' 0 <=> a ' 0 /\ b ' 0
Proof
  fs [word_mul_def,word_index,bitTheory.BIT0_ODD,ODD_MULT]
  \\ Cases \\ Cases \\ fs [word_index,bitTheory.BIT0_ODD]
QED

Theorem word_lsl_index:
   i < dimindex(:'a) ⇒
    (((w:'a word) << n) ' i ⇔ n ≤ i ∧ w ' (i-n))
Proof
  rw[word_lsl_def,fcpTheory.FCP_BETA]
QED

Theorem word_lsr_index:
   i < dimindex(:'a) ⇒
   (((w:'a word) >>> n) ' i ⇔ i + n < dimindex(:'a) ∧ w ' (i+n))
Proof
  rw[word_lsr_def,fcpTheory.FCP_BETA]
QED

Theorem lsr_lsl:
   ∀w n. aligned n w ⇒ (w >>> n << n = w)
Proof
  simp [aligned_def, alignmentTheory.align_shift]
QED

Theorem word_index_test:
   n < dimindex (:'a) ==> (w ' n <=> ((w && n2w (2 ** n)) <> 0w:'a word))
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
QED

Theorem word_and_one_eq_0_iff: (* same in stack_alloc *)
  !w. ((w && 1w) = 0w) <=> ~(w ' 0)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index]
QED

Theorem word_index_0:
   !w. w ' 0 <=> ~((1w && w) = 0w)
Proof
  metis_tac [word_and_one_eq_0_iff,WORD_AND_COMM]
QED

Theorem ABS_w2n[simp]:
   ABS (&w2n w) = &w2n w
Proof
  rw[integerTheory.INT_ABS_EQ_ID]
QED

Theorem n2mw_w2n:
   ∀w. n2mw (w2n w) = if w = 0w then [] else [w]
Proof
  simp[Once multiwordTheory.n2mw_def]
  \\ gen_tac \\ IF_CASES_TAC \\ fs[]
  \\ Q.ISPEC_THEN`w`mp_tac w2n_lt
  \\ simp[LESS_DIV_EQ_ZERO,multiwordTheory.n2mw_NIL]
QED

Theorem get_var_set_var[simp]:
   get_var n (set_var n w s) = SOME w
Proof
  full_simp_tac(srw_ss())[wordSemTheory.get_var_def,wordSemTheory.set_var_def]
QED

Theorem set_var_set_var[simp]:
   set_var n v (wordSem$set_var n w s) = set_var n v s
Proof
  fs[wordSemTheory.state_component_equality,wordSemTheory.set_var_def,
      insert_shadow]
QED

Theorem toAList_LN[simp]:
   toAList LN = []
Proof
  EVAL_TAC
QED

Theorem adjust_set_LN[simp]:
   adjust_set LN = LN
Proof
  srw_tac[][adjust_set_def,fromAList_def]
QED

Theorem push_env_termdep:
   (push_env y opt t).termdep = t.termdep
Proof
  Cases_on `opt` \\ TRY (PairCases_on `x`)
  \\ fs [wordSemTheory.push_env_def]
  \\ pairarg_tac \\ fs []
QED

Theorem ALOOKUP_SKIP_LEMMA:
   ¬MEM n (MAP FST xs) /\ d = e ==>
    ALOOKUP (xs ++ [(n,d)] ++ ys) n = SOME e
Proof
  full_simp_tac(srw_ss())[ALOOKUP_APPEND] \\ fs[GSYM ALOOKUP_NONE]
QED

Theorem LAST_EQ:
   (LAST (x::xs) = if xs = [] then x else LAST xs) /\
    (FRONT (x::xs) = if xs = [] then [] else x::FRONT xs)
Proof
  Cases_on `xs` \\ full_simp_tac(srw_ss())[]
QED

Theorem LASTN_LIST_REL_LEMMA:
   !xs1 ys1 xs n y ys x P.
      LASTN n xs1 = x::xs /\ LIST_REL P xs1 ys1 ==>
      ?y ys. LASTN n ys1 = y::ys /\ P x y /\ LIST_REL P xs ys
Proof
  Induct \\ Cases_on `ys1` \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ `F` by decide_tac
QED

Theorem LASTN_CONS_IMP_LENGTH:
   !xs n y ys.
      n <= LENGTH xs ==>
      (LASTN n xs = y::ys) ==> LENGTH (y::ys) = n
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT]
  \\ srw_tac[][] THEN1 decide_tac \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
QED

Theorem LASTN_IMP_APPEND:
   !xs n ys.
      n <= LENGTH xs /\ (LASTN n xs = ys) ==>
      ?zs. xs = zs ++ ys /\ LENGTH ys = n
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][] THEN1 decide_tac
  \\ `n <= LENGTH xs` by decide_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xs = zs ++ LASTN n xs` (fn th => simp [Once th])
QED

Theorem NOT_NIL_IMP_LAST:
   !xs x. xs <> [] ==> LAST (x::xs) = LAST xs
Proof
  Cases \\ full_simp_tac(srw_ss())[]
QED

Theorem IS_SOME_IF:
   IS_SOME (if b then x else y) = if b then IS_SOME x else IS_SOME y
Proof
  Cases_on `b` \\ full_simp_tac(srw_ss())[]
QED

Theorem IS_SOME_ALOOKUP_EQ:
   !l x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)
Proof
  Induct \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]
QED

Theorem MEM_IMP_IS_SOME_ALOOKUP:
   !l x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)
Proof
  full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

Theorem SUBSET_INSERT_EQ_SUBSET:
   ~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)
Proof
  full_simp_tac(srw_ss())[EXTENSION]
QED

Theorem EVERY2_IMP_EL:
   !xs ys P n. EVERY2 P xs ys /\ n < LENGTH ys ==> P (EL n xs) (EL n ys)
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
QED

Theorem FST_PAIR_EQ:
   !x v. (FST x,v) = x <=> v = SND x
Proof
  Cases \\ full_simp_tac(srw_ss())[]
QED

Theorem EVERY2_APPEND_IMP:
   !xs1 xs2 zs P.
      EVERY2 P (xs1 ++ xs2) zs ==>
      ?zs1 zs2. zs = zs1 ++ zs2 /\ EVERY2 P xs1 zs1 /\ EVERY2 P xs2 zs2
Proof
  Induct \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`y::zs1`,`zs2`] \\ full_simp_tac(srw_ss())[]
QED

Theorem ZIP_ID:
   !xs. ZIP (MAP FST xs, MAP SND xs) = xs
Proof
  Induct \\ full_simp_tac(srw_ss())[]
QED

Theorem FOLDL_LENGTH_LEMMA:
   !xs k l d q r.
      FOLDL (λ(i,t) a. (i + d,insert i a t)) (k,l) xs = (q,r) ==>
      q = LENGTH xs * d + k
Proof
  Induct \\ fs [FOLDL] \\ rw [] \\ res_tac \\ fs [MULT_CLAUSES]
QED

Theorem fromList_SNOC:
  !xs y. fromList (SNOC y xs) = insert (LENGTH xs) y (fromList xs)
Proof
  fs [fromList_def,FOLDL_APPEND,SNOC_APPEND] \\ rw []
  \\ Cases_on `FOLDL (λ(i,t) a. (i + 1,insert i a t)) (0,LN) xs`
  \\ fs [] \\ imp_res_tac FOLDL_LENGTH_LEMMA \\ fs []
QED

Theorem fromList2_SNOC:
  !xs y. fromList2 (SNOC y xs) = insert (2 * LENGTH xs) y (fromList2 xs)
Proof
  fs [fromList2_def,FOLDL_APPEND,SNOC_APPEND] \\ rw []
  \\ Cases_on `FOLDL (λ(i,t) a. (i + 2,insert i a t)) (0,LN) xs`
  \\ fs [] \\ imp_res_tac FOLDL_LENGTH_LEMMA \\ fs []
QED

(* -- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

Definition join_env_def:
  join_env env vs =
    MAP (\(n,v). (THE (lookup ((n-2) DIV 2) env), v))
      (FILTER (\(n,v). n <> 0 /\ EVEN n) vs)
End

Definition flat_def:
  (flat (Env _ env::xs) (StackFrame _ _ vs _::ys) =
     join_env env vs ++ flat xs ys) /\
  (flat (Exc _ env _::xs) (StackFrame _ _ vs _::ys) =
     join_env env vs ++ flat xs ys) /\
  (flat _ _ = [])
End

Theorem flat_APPEND:
   !xs ys xs1 ys1.
      LENGTH xs = LENGTH ys ==>
      flat (xs ++ xs1) (ys ++ ys1) = flat xs ys ++ flat xs1 ys1
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[flat_def] \\ srw_tac[][]
  \\ Cases_on `h'` \\ Cases_on `h`
  \\ TRY (Cases_on `o'`) \\ full_simp_tac(srw_ss())[flat_def]
QED

Theorem adjust_var_DIV_2:
   (adjust_var n - 2) DIV 2 = n
Proof
  full_simp_tac(srw_ss())[ONCE_REWRITE_RULE[MULT_COMM]adjust_var_def,MULT_DIV]
QED

Theorem adjust_var_DIV_2_ANY:
   (adjust_var n) DIV 2 = n + 1
Proof
  fs [adjust_var_def,ONCE_REWRITE_RULE[MULT_COMM]ADD_DIV_ADD_DIV]
QED

Theorem EVEN_adjust_var:
   EVEN (adjust_var n)
Proof
  full_simp_tac(srw_ss())[adjust_var_def,EVEN_MOD2,
    ONCE_REWRITE_RULE[MULT_COMM]MOD_TIMES]
QED

Theorem adjust_var_eq_numeral[simp]:
   adjust_var n = NUMERAL k <=>
    EVEN (NUMERAL k) /\ NUMERAL k <> 0 /\ n = (NUMERAL k - 2) DIV 2
Proof
  qabbrev_tac `kk = NUMERAL k`
  \\ pop_assum kall_tac
  \\ fs [adjust_var_def] \\ fs [EVEN_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `n+1` \\ fs [])
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ Cases_on `m` \\ fs [ADD1,LEFT_ADD_DISTRIB]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
QED

Theorem adjust_var_NEQ_0[simp]:
   adjust_var n <> 0
Proof
  fs [adjust_var_def]
QED

Theorem adjust_var_NEQ_1:
   adjust_var n <> 1
Proof
  fs []
QED

Theorem adjust_var_NEQ[simp]:
   adjust_var n <> 0 /\
    adjust_var n <> 1 /\
    adjust_var n <> 3 /\
    adjust_var n <> 5 /\
    adjust_var n <> 7 /\
    adjust_var n <> 9 /\
    adjust_var n <> 11 /\
    adjust_var n <> 13
Proof
  fs [adjust_var_NEQ_0]
QED

Theorem unit_opt_eq:
   (x = y:unit option) <=> (IS_SOME x <=> IS_SOME y)
Proof
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]
QED

Theorem adjust_var_11:
   (adjust_var n = adjust_var m) <=> n = m
Proof
  full_simp_tac(srw_ss())[adjust_var_def,EQ_MULT_LCANCEL]
QED

Theorem lookup_adjust_var_adjust_set:
   lookup (adjust_var n) (adjust_set s) = lookup n s
Proof
  simp[lookup_def,adjust_set_def,lookup_fromAList,unit_opt_eq,adjust_var_NEQ_0,
       Excl "fromAList_def"]
  \\ simp[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ simp[MEM_toAList] \\ Cases_on `lookup n s` \\ simp[]
QED

Theorem adjust_var_IN_adjust_set:
   adjust_var n IN domain (adjust_set (s:num_set)) <=> n IN domain s
Proof
  fs [domain_lookup,lookup_adjust_var_adjust_set]
QED

Theorem none_opt_eq:
   ((x = NONE) = (y = NONE)) <=> (IS_SOME x <=> IS_SOME y)
Proof
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]
QED

Theorem lookup_adjust_var_adjust_set_NONE:
   lookup (adjust_var n) (adjust_set s) = NONE <=> lookup n s = NONE
Proof
  simp[lookup_def,adjust_set_def,lookup_fromAList,adjust_var_NEQ_0,none_opt_eq,
       Excl "fromAList_def"]
  \\ simp[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ simp[MEM_toAList] \\ Cases_on `lookup n s` \\ simp[]
QED

Theorem lookup_adjust_var_adjust_set_SOME_UNIT:
   lookup (adjust_var n) (adjust_set s) = SOME () <=> IS_SOME (lookup n s)
Proof
  Cases_on `lookup (adjust_var n) (adjust_set s) = NONE`
  \\ pop_assum (fn th => assume_tac th THEN
       assume_tac (SIMP_RULE std_ss [lookup_adjust_var_adjust_set_NONE] th))
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `lookup n s`
  \\ Cases_on `lookup (adjust_var n) (adjust_set s)` \\ full_simp_tac(srw_ss())[]
QED

Theorem word_ml_inv_lookup:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      (ys ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) /\
    lookup n l1 = SOME x /\
    lookup (adjust_var n) l2 = SOME w ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      (ys ++ [(x,w)] ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs)
Proof
  full_simp_tac(srw_ss())[toAList_def,foldi_def,LET_DEF]
  \\ full_simp_tac(srw_ss())[GSYM toAList_def] \\ srw_tac[][]
  \\ `MEM (x,w) (join_env l1 (toAList (inter l2 (adjust_set l1))))` by
   (full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,lookup_inter]
    \\ qexists_tac `adjust_var n` \\ full_simp_tac(srw_ss())[adjust_var_DIV_2,EVEN_adjust_var]
    \\ full_simp_tac(srw_ss())[adjust_var_NEQ_0] \\ every_case_tac
    \\ full_simp_tac(srw_ss())[lookup_adjust_var_adjust_set_NONE])
  \\ full_simp_tac(srw_ss())[MEM_SPLIT] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[adjust_var_def]
  \\ qpat_x_assum `word_ml_inv yyy limit ts c refs xxx` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem word_ml_inv_get_var_IMP_lemma:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      (join_env ll (toAList (inter t.locals (adjust_set ll)))++envs) /\
    get_var n ll = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      ([(x,w)]++join_env ll
          (toAList (inter t.locals (adjust_set ll)))++envs)
Proof
  srw_tac[][] \\ match_mp_tac (word_ml_inv_lookup
             |> Q.INST [`ys`|->`[]`] |> SIMP_RULE std_ss [APPEND])
  \\ full_simp_tac(srw_ss())[get_var_def,wordSemTheory.get_var_def]
QED

Theorem word_ml_inv_get_var_IMP:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      (join_env s.locals (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      ([(x,w)]++join_env s.locals
          (toAList (inter t.locals (adjust_set s.locals)))++envs)
Proof
  srw_tac[][] \\ match_mp_tac (word_ml_inv_lookup
             |> Q.INST [`ys`|->`[]`] |> SIMP_RULE std_ss [APPEND])
  \\ full_simp_tac(srw_ss())[get_var_def,wordSemTheory.get_var_def]
QED

Theorem word_ml_inv_get_vars_IMP_lemma[allow_rebind] = Q.prove(`
  !n x w envs.
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env ll
           (toAList (inter t.locals (adjust_set ll)))++envs) /\
      get_vars n ll = SOME x /\
      get_vars (MAP adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (ZIP(x,w)++join_env ll
           (toAList (inter t.locals (adjust_set ll)))++envs)`,
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,wordSemTheory.get_vars_def]
  \\ rpt strip_tac
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac word_ml_inv_get_var_IMP_lemma
  \\ Q.MATCH_ASSUM_RENAME_TAC `dataSem$get_var h ll = SOME x7`
  \\ Q.MATCH_ASSUM_RENAME_TAC `_ (adjust_var h) _ = SOME x8`
  \\ `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env ll (toAList (inter t.locals (adjust_set ll))) ++
        (x7,x8)::envs)` by
   (pop_assum mp_tac \\ match_mp_tac word_ml_inv_rearrange
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ res_tac \\ pop_assum (K all_tac) \\ pop_assum mp_tac
  \\ match_mp_tac word_ml_inv_rearrange
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ fs[]) |> SPEC_ALL

Theorem word_ml_inv_get_vars_IMP[allow_rebind] = Q.prove(`
  !n x w envs.
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
      get_vars n s.locals = SOME x /\
      get_vars (MAP adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (ZIP(x,w)++join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs)`,
  metis_tac [word_ml_inv_get_vars_IMP_lemma]) |> SPEC_ALL

Theorem IMP_adjust_var:
   n <> 0 /\ EVEN n ==> adjust_var ((n - 2) DIV 2) = n
Proof
  full_simp_tac(srw_ss())[EVEN_EXISTS] \\ srw_tac[][] \\ Cases_on `m` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ once_rewrite_tac [MULT_COMM] \\ full_simp_tac(srw_ss())[MULT_DIV]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ decide_tac
QED

Theorem unit_some_eq_IS_SOME:
   !x. (x = SOME ()) <=> IS_SOME x
Proof
  Cases \\ full_simp_tac(srw_ss())[]
QED

Theorem IS_SOME_lookup_domain:
  IS_SOME (lookup k m) ⇔ k ∈ domain m
Proof
  simp[optionTheory.IS_SOME_EXISTS, domain_lookup]
QED


Theorem word_ml_inv_insert:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      ([(x,w)]++join_env d (toAList (inter l (adjust_set d)))++xs) ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      (join_env (insert dest x d)
        (toAList (inter (insert (adjust_var dest) w l)
                           (adjust_set (insert dest x d))))++xs)
Proof
  match_mp_tac word_ml_inv_rearrange \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MEM_toAList]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt]
  \\ Cases_on `dest = (p_1 - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[adjust_var_DIV_2]
  \\ imp_res_tac IMP_adjust_var \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[domain_lookup, AllCaseEqs()]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[adjust_var_11]
  \\ full_simp_tac(srw_ss())[]
  \\ disj1_tac \\ disj2_tac \\ qexists_tac `p_1`
  \\ full_simp_tac(srw_ss())[unit_some_eq_IS_SOME]
  \\ full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList] \\ rev_full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_insert]
  \\ gs[IS_SOME_lookup_domain, domain_fromAList, MAP_MAP_o,
        pairTheory.o_UNCURRY_R, combinTheory.o_ABS_R]
  \\ gs[MEM_MAP, EXISTS_PROD, adjust_var_11]
  \\ gs[MEM_toAList, adjust_var_11, lookup_insert]
QED

Theorem one_and_or_1:
   (1w && (w || 1w)) = 1w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem one_and_or_3:
   (3w && (w || 3w)) = 3w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem ODD_not_zero:
   ODD n ==> n2w n <> 0w
Proof
  CCONTR_TAC \\ full_simp_tac std_ss []
  \\ `((n2w n):'a word) ' 0 = (0w:'a word) ' 0` by metis_tac []
  \\ full_simp_tac(srw_ss())[wordsTheory.word_index,bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ full_simp_tac(srw_ss())[dimword_def,bitTheory.ODD_MOD2_LEM]
QED

Theorem three_not_0[simp]:
   3w <> 0w
Proof
  match_mp_tac ODD_not_zero \\ full_simp_tac(srw_ss())[]
QED

val DISJ_EQ_IMP = METIS_PROVE [] ``(~b \/ c) <=> (b ==> c)``

Theorem three_and_shift_2:
   (3w && (w << 2)) = 0w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem shift_to_zero:
   3w >>> 2 = 0w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem shift_around_under_big_shift:
   !w n k. n <= k ==> (w << n >>> n << k = w << k)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem select_shift_out:
   n <> 0 /\ n <= m ==> ((n - 1 -- 0) (w || v << m) = (n - 1 -- 0) w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem shift_length_NOT_ZERO[simp]:
   shift_length conf <> 0
Proof
  full_simp_tac(srw_ss())[shift_length_def] \\ decide_tac
QED

Theorem get_addr_and_1_not_0:
   (1w && get_addr conf k a) <> 0w
Proof
  Cases_on `a` \\ full_simp_tac(srw_ss())[get_addr_def,get_lowerbits_def]
  \\ rewrite_tac [one_and_or_1,GSYM WORD_OR_ASSOC] \\ full_simp_tac(srw_ss())[]
QED

Theorem one_lsr_shift_length:
   1w >>> shift_length conf = 0w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
    [word_index, shift_length_def]
QED

Theorem ptr_to_addr_get_addr:
   k * 2 ** shift_length conf < dimword (:'a) ==>
    ptr_to_addr conf curr (get_addr conf k a) =
    curr + n2w k * bytes_in_word:'a word
Proof
  strip_tac
  \\ full_simp_tac(srw_ss())[ptr_to_addr_def,bytes_in_word_def,WORD_MUL_LSL,get_addr_def]
  \\ simp_tac std_ss [Once WORD_MULT_COMM] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[get_lowerbits_LSL_shift_length,word_mul_n2w]
  \\ once_rewrite_tac [GSYM w2n_11]
  \\ rewrite_tac [w2n_lsr] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[MULT_DIV]
  \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ decide_tac
QED

Theorem is_fws_ptr_OR_3:
   is_fwd_ptr (Word (w << 2)) /\ ~is_fwd_ptr (Word (w || 3w))
Proof
  full_simp_tac(srw_ss())[is_fwd_ptr_def] \\ rewrite_tac [one_and_or_3,three_and_shift_2]
  \\ full_simp_tac(srw_ss())[]
QED

Theorem is_fws_ptr_OR_15:
   ~is_fwd_ptr (Word (w || 15w))
Proof
  full_simp_tac(srw_ss())[is_fwd_ptr_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def]
  \\ qexists_tac `0` \\ fs []
QED

Theorem is_fws_ptr_OR_10111:
   ~is_fwd_ptr (Word (w || 0b10111w))
Proof
  full_simp_tac(srw_ss())[is_fwd_ptr_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def]
  \\ qexists_tac `0` \\ fs []
QED

Theorem is_fws_ptr_OR_7:
   ~is_fwd_ptr (Word (w || 7w))
Proof
  full_simp_tac(srw_ss())[is_fwd_ptr_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def]
  \\ qexists_tac `0` \\ fs []
QED

Theorem select_get_lowerbits:
   (shift_length conf − 1 -- 0) (get_lowerbits conf a) =
   get_lowerbits conf a /\
   (small_shift_length conf − 1 -- 0) (get_lowerbits conf a) =
   get_lowerbits conf a
Proof
  Cases_on `a`
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def,
              small_shift_length_def,shift_length_def]
  \\ eq_tac \\ rw [] \\ fs []
QED

Theorem LE_DIV_LT_IMP:
   n <= l DIV 2 ** m /\ k < n ==> k * 2 ** m < l
Proof
  srw_tac[][] \\ `k < l DIV 2 ** m` by decide_tac
  \\ full_simp_tac(srw_ss())[X_LT_DIV,MULT_CLAUSES,GSYM ADD1]
  \\ Cases_on `2 ** m` \\ full_simp_tac(srw_ss())[]
  \\ decide_tac
QED

Theorem word_bits_eq_slice_shift:
   ((k -- n) w) = (((k '' n) w) >>> n)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
  \\ Cases_on `i + n < dimindex (:'a)`
  \\ fs []
QED

Theorem word_slice_or:
   (k '' n) (w || v) = ((k '' n) w || (k '' n) v)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
  \\ eq_tac
  \\ rw []
  \\ fs []
QED

Theorem word_slice_lsl_eq_0:
   (k '' n) (w << (k + 1)) = 0w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Theorem word_slice_2_3_eq_0:
   (n '' 2) 3w = 0w
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
QED

Definition can_select_def:
  can_select k n w <=> ((k - 1 -- n) (w << n) = w)
End

Theorem read_length_lemma:
   can_select (n+2) 2 (n2w k :'a word) ==>
    (((n + 1 -- 2) (h ≪ (2 + n) || n2w k ≪ 2 || 3w)) = n2w k :'a word)
Proof
  full_simp_tac(srw_ss())[word_bits_eq_slice_shift,word_slice_or,can_select_def,DECIDE ``n+2-1=n+1n``]
  \\ full_simp_tac(srw_ss())[DECIDE ``2+n=n+1+1n``,word_slice_lsl_eq_0,word_slice_2_3_eq_0]
QED

Theorem memcpy_thm:
   !xs a:'a word c b m m1 dm b1 ys frame.
      memcpy (n2w (LENGTH xs):'a word) a b m dm = (b1,m1,c) /\
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:'a) /\
      (frame * word_list a xs * word_list b ys) (fun2set (m,dm)) ==>
      (frame * word_list a xs * word_list b xs) (fun2set (m1,dm)) /\
      b1 = b + n2w (LENGTH xs) * bytes_in_word /\ c
Proof
  Induct_on `xs` \\ Cases_on `ys`
  THEN1 (simp [LENGTH,Once memcpy_def,LENGTH])
  THEN1 (simp [LENGTH,Once memcpy_def,LENGTH])
  THEN1 (rpt strip_tac \\ full_simp_tac(srw_ss())[LENGTH])
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `_ = (b1,m1,c)`  mp_tac
  \\ once_rewrite_tac [memcpy_def]
  \\ asm_rewrite_tac [n2w_11]
  \\ drule LESS_MOD
  \\ simp_tac (srw_ss()) [ADD1,GSYM word_add_n2w]
  \\ pop_assum mp_tac
  \\ simp_tac (srw_ss()) [word_list_def,LET_THM]
  \\ pairarg_tac
  \\ first_x_assum drule
  \\ full_simp_tac(srw_ss())[] \\ NTAC 2 strip_tac
  \\ qpat_x_assum `_ = (b1',m1',c1)` mp_tac
  \\ SEP_W_TAC \\ SEP_F_TAC
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ rpt (disch_then assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ imp_res_tac (DECIDE ``n+1n<k ==> n<k``) \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
QED

Theorem LESS_EQ_IMP_APPEND:
   !n xs. n <= LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH ys = n
Proof
  Induct_on `xs` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[LENGTH_NIL]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ qexists_tac `h::ys` \\ full_simp_tac(srw_ss())[]
QED

Theorem NOT_is_fwd_ptr:
   word_payload addrs ll tag tt1 conf = (h,ts,c5) ==> ~is_fwd_ptr (Word h)
Proof
  Cases_on `tag` \\ fs [word_payload_def] \\ rw [make_byte_header_def]
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,is_fws_ptr_OR_15,
      is_fws_ptr_OR_10111,is_fws_ptr_OR_7,isWord_def,theWord_def,make_header_def,LET_DEF]
QED

Theorem word_gc_move_thm:
   (copying_gc$gc_move (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    (word_heap curr heap conf * word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gc_move conf (word_addr conf x,n2w a,pa,curr,m,dm) =
      (w:'a word_loc,i1,pa1,m1,c1)) /\
    LENGTH xs = n ==>
    ?xs1.
      (word_heap curr heap1 conf *
       word_heap pa h1 conf *
       word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length heap1 = heap_length heap /\
      c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
      pa1 = pa + bytes_in_word * n2w (heap_length h1)
Proof
  reverse (Cases_on `x`) \\ full_simp_tac(srw_ss())[copying_gcTheory.gc_move_def] THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[word_heap_def,SEP_CLAUSES]
    \\ Cases_on `a'` \\ full_simp_tac(srw_ss())[word_addr_def,word_gc_move_def]
    \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def] \\ gvs [])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rename1 `heap_lookup k heap = SOME x`
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[word_gc_move_def,get_addr_and_1_not_0]
  \\ imp_res_tac heap_lookup_LESS
  \\ drule LE_DIV_LT_IMP \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[ptr_to_addr_get_addr,word_heap_def,SEP_CLAUSES]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,word_el_def]
  \\ `small_shift_length conf <= shift_length conf /\
      small_shift_length conf <> 0` by (EVAL_TAC \\ fs [] \\ NO_TAC)
  THEN1
   (helperLib.SEP_R_TAC
    \\ full_simp_tac(srw_ss())[LET_THM,theWord_def,is_fws_ptr_OR_3]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[update_addr_def,shift_to_zero]
    \\ `2 <= shift_length conf` by (fs[shift_length_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[shift_around_under_big_shift]
    \\ full_simp_tac(srw_ss())[get_addr_def,select_shift_out]
    \\ full_simp_tac(srw_ss())[select_get_lowerbits,heap_length_def])
  \\ rename1 `_ = SOME (DataElement addrs ll tt)`
  \\ PairCases_on `tt`
  \\ full_simp_tac(srw_ss())[word_el_def]
  \\ `?h ts c5. word_payload addrs ll tt0 tt1 conf =
         (h:'a word,ts,c5)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac bool_ss [word_list_def]
  \\ SEP_R_TAC
  \\ full_simp_tac bool_ss [GSYM word_list_def]
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,isWord_def,theWord_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
  \\ `~is_fwd_ptr (Word h)` by (imp_res_tac NOT_is_fwd_ptr \\ fs [])
  \\ fs []
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ `n2w (LENGTH ts) + 1w = n2w (LENGTH (Word h::ts)):'a word` by
        full_simp_tac(srw_ss())[LENGTH,ADD1,word_add_n2w]
  \\ full_simp_tac bool_ss []
  \\ drule memcpy_thm
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ full_simp_tac(srw_ss())[gc_forward_ptr_thm] \\ rev_full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def]
  \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
  \\ imp_res_tac word_payload_IMP
  \\ rpt var_eq_tac
  \\ drule LESS_EQ_IMP_APPEND \\ strip_tac
  \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_list_APPEND]
  \\ disch_then (qspec_then `ys` assume_tac)
  \\ SEP_F_TAC
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[ADD1,SUM_APPEND,X_LE_DIV,RIGHT_ADD_DISTRIB]
    \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
    \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[word_addr_def,word_add_n2w,ADD_ASSOC] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
       SEP_CLAUSES,word_el_def,LET_THM]
  \\ full_simp_tac(srw_ss())[word_list_def]
  \\ SEP_W_TAC \\ qexists_tac `zs` \\ full_simp_tac(srw_ss())[]
  \\ reverse conj_tac THEN1
   (full_simp_tac(srw_ss())[update_addr_def,get_addr_def,
       select_shift_out,select_get_lowerbits,ADD1])
  \\ pop_assum mp_tac
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,ADD1]
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ srw_tac[][] \\ qexists_tac `ts`
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
QED

Theorem word_gc_move_roots_thm:
   !x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 w frame.
      (gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      (word_heap curr heap conf * word_list pa xs * frame) (fun2set (m,dm)) /\
      (word_gc_move_roots conf (MAP (word_addr conf) x,n2w a,pa,curr,m,dm) =
        (w:'a word_loc list,i1,pa1,m1,c1)) /\
      LENGTH xs = n ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap pa h1 conf *
         word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        (w = MAP (word_addr conf) x1) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[copying_gcTheory.gc_move_list_def,word_gc_move_roots_def,word_heap_def,SEP_CLAUSES]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[copying_gcTheory.gc_move_list_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT]
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `c'` by imp_res_tac copying_gcTheory.gc_move_list_ok \\ full_simp_tac(srw_ss())[]
  \\ drule (word_gc_move_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = (xs7,xs8,a7,LENGTH xs9,heap7,T)`
  \\ qexists_tac `xs9` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND]
  \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB,heap_length_def,SUM_APPEND,GSYM word_add_n2w]
QED

Theorem word_gc_move_list_thm:
   !x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 frame k k1.
      (copying_gc$gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      (word_gc_move_list conf (k,n2w (LENGTH x),n2w a,pa,curr,m,dm) =
        (k1,i1,pa1,m1,c1)) /\
      (word_heap curr heap conf * word_list pa xs *
       word_list k (MAP (word_addr conf) x) * frame) (fun2set (m,dm)) /\
      LENGTH xs = n /\ LENGTH x < dimword (:'a) ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap (pa:'a word) h1 conf *
         word_list pa1 xs1 *
         word_list k (MAP (word_addr conf) x1) * frame) (fun2set (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        k1 = k + n2w (LENGTH x) * bytes_in_word /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[copying_gcTheory.gc_move_list_def,Once word_gc_move_list_def,word_heap_def,SEP_CLAUSES]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[copying_gcTheory.gc_move_list_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `word_gc_move_list conf _ = _` mp_tac
  \\ simp [Once word_gc_move_list_def,LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,ADD1]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `c'` by imp_res_tac copying_gcTheory.gc_move_list_ok \\ full_simp_tac(srw_ss())[]
  \\ pop_assum kall_tac
  \\ NTAC 2 (pop_assum mp_tac)
  \\ full_simp_tac(srw_ss())[word_list_def] \\ SEP_R_TAC \\ rpt strip_tac
  \\ drule (word_gc_move_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ qpat_x_assum `word_gc_move_list conf _ = _` mp_tac
  \\ SEP_W_TAC \\ strip_tac
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM] \\ full_simp_tac(srw_ss())[]
  \\ disch_then imp_res_tac
  \\ `LENGTH x < dimword (:'a)` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum kall_tac
  \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = (xs7,xs8,a7,LENGTH xs9,heap7,T)`
  \\ qexists_tac `xs9` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND]
  \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB,heap_length_def,
        SUM_APPEND,GSYM word_add_n2w]
QED

Theorem word_payload_swap:
   word_payload l5 (LENGTH l5) tag r conf = (h,MAP (word_addr conf) l5,T) /\
    LENGTH xs' = LENGTH l5 ==>
    word_payload xs' (LENGTH l5) tag r conf = (h,MAP (word_addr conf) xs',T)
Proof
  Cases_on `tag` \\ full_simp_tac(srw_ss())[word_payload_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LENGTH_NIL]
QED

Theorem word_gc_move_loop_thm:
   !h1 h2 a n heap c0 limit h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k.
      (gc_move_loop (h1,h2,a,n,heap,c0,limit) = (h11,a1,n1,heap1,T)) /\ c0 /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
      conf.len_size + 2 < dimindex (:'a) /\
      (word_heap curr heap conf *
       word_heap new (h1 ++ h2) conf *
       word_list (new + n2w (heap_length (h1++h2)) * bytes_in_word) xs * frame)
         (fun2set (m,dm)) /\
      limit - heap_length h1 <= k /\
      limit = heap_length heap /\ good_dimindex (:'a) /\
      (word_gc_move_loop k conf (new + n2w (heap_length h1) * bytes_in_word,n2w a,
           new + n2w (heap_length (h1++h2)) * bytes_in_word,curr,m,dm,T) =
         (i1,pa1,m1,c1)) /\ LENGTH xs = n ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap (new:'a word) h11 conf *
         word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = new + bytes_in_word * n2w (heap_length h11)
Proof
  recInduct gc_move_loop_ind \\ rpt strip_tac
  THEN1
   (full_simp_tac(srw_ss())[gc_move_loop_def] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[]
    \\ pop_assum mp_tac \\ once_rewrite_tac [word_gc_move_loop_def]
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC])
  \\ qpat_x_assum `gc_move_loop _ = _` mp_tac
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac gc_move_loop_ok \\ full_simp_tac(srw_ss())[]
  \\ rename1 `HD h5 = DataElement l5 n5 b5`
  \\ Cases_on `h5` \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `word_gc_move_loop _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gc_move_loop_def]
  \\ IF_CASES_TAC THEN1
   (sg `F`
    \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,
           WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ pop_assum mp_tac
    \\ Q.PAT_ABBREV_TAC `x = bytes_in_word * n2w (SUM (MAP el_length h1))`
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL]
    \\ full_simp_tac(srw_ss())[bytes_in_word_def,word_add_n2w,word_mul_n2w]
    \\ full_simp_tac(srw_ss())[NOT_LESS]
    \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
    \\ qpat_x_assum `_ <= heap_length heap` mp_tac
    \\ qpat_x_assum `heap_length heap * _ < _ ` mp_tac
    \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
    \\ rpt (pop_assum kall_tac) \\ srw_tac[][]
    \\ sg `dimindex (:α) DIV 8 + dimindex (:α) DIV 8 * n5 +
           dimindex (:α) DIV 8 * heap_length h2 < dimword (:α)`
    \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]
    \\ rev_full_simp_tac(srw_ss())[good_dimindex_def,dimword_def] \\ decide_tac)
  \\ Cases_on `b5`
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
       SEP_CLAUSES,STAR_ASSOC,word_el_def]
  \\ qpat_x_assum `_ (fun2set (m,dm))` assume_tac
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pop_assum mp_tac
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac std_ss [word_list_def] \\ SEP_R_TAC
  \\ full_simp_tac(srw_ss())[isWord_def,theWord_def]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ rename1 `word_payload _ _ tag _ conf = _`
  \\ drule word_payload_T_IMP
  \\ impl_tac THEN1 (fs []) \\ strip_tac
  \\ `k <> 0` by
   (fs [heap_length_APPEND,el_length_def,heap_length_def] \\ decide_tac)
  \\ full_simp_tac std_ss []
  \\ Cases_on `word_bit 2 h` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[]
  THEN1
   (full_simp_tac(srw_ss())[copying_gcTheory.gc_move_list_def] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
    \\ qpat_x_assum `!xx. nn` mp_tac
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ ntac 2 strip_tac \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac `xs` \\ qexists_tac `m` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `k - 1` \\ fs [])
  \\ qpat_x_assum `gc_move_list _ = _` mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT] \\ strip_tac
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pop_assum mp_tac
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ ntac 5 var_eq_tac
  \\ drule word_gc_move_list_thm \\ full_simp_tac(srw_ss())[]
  \\ ntac 2 strip_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ disch_then (qspec_then `xs` mp_tac)
  \\ fs [] \\ strip_tac \\ SEP_F_TAC
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[NOT_LESS] \\ qpat_x_assum `_ <= heap_length heap` mp_tac
    \\ qpat_x_assum `heap_length heap <= _ ` mp_tac
    \\ qpat_x_assum `heap_length heap <= _ ` mp_tac
    \\ rpt (pop_assum kall_tac) \\ full_simp_tac(srw_ss())[X_LE_DIV]
    \\ full_simp_tac(srw_ss())[heap_length_APPEND,heap_length_def,el_length_def]
    \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ strip_tac \\ fs []
  \\ ntac 5 var_eq_tac
  \\ `LENGTH xs' = LENGTH l5` by imp_res_tac gc_move_list_IMP_LENGTH
  \\ `word_payload xs' (LENGTH l5) tag r conf =
       (h,MAP (word_addr conf) xs',T)` by
         (match_mp_tac word_payload_swap \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,SEP_CLAUSES]
  \\ qpat_x_assum `_ = (i1,pa1,m1,c1)` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ qexists_tac `xs1'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `m1'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `k-1` \\ fs []
  \\ qpat_x_assum `_ (fun2set (m1',dm))` mp_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,heap_length_def,el_length_def,SUM_APPEND]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,SEP_CLAUSES]
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,word_heap_APPEND]
QED

Theorem word_full_gc_thm:
   (full_gc (roots,heap,limit) = (roots1,heap1,a1,T)) /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    conf.len_size + 2 < dimindex (:'a) /\
    (word_heap (curr:'a word) heap conf *
     word_heap new (heap_expand limit) conf * frame) (fun2set (m,dm)) /\
    limit = heap_length heap /\ good_dimindex (:'a) /\
    (word_full_gc conf (MAP (word_addr conf) roots,new,curr,m,dm) =
       (rs1,i1,pa1,m1,c1)) ==>
    (word_heap new (heap1 ++ heap_expand (limit - a1)) conf *
     word_heap curr (heap_expand limit) conf * frame) (fun2set (m1,dm)) /\
    c1 /\ i1 = n2w a1 /\
    rs1 = MAP (word_addr conf) roots1 /\
    pa1 = new + bytes_in_word * n2w a1
Proof
  strip_tac \\ full_simp_tac(srw_ss())[full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_def,word_el_def]
  \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
  \\ imp_res_tac gc_move_loop_ok \\ full_simp_tac(srw_ss())[]
  \\ drule word_gc_move_roots_thm
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,
       SEP_EXISTS_THM,word_heap_heap_expand]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ full_simp_tac(srw_ss())[word_full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ drule word_gc_move_loop_thm
  \\ full_simp_tac(srw_ss())[heap_length_def]
  \\ once_rewrite_tac [CONJ_COMM] \\ full_simp_tac(srw_ss())[GSYM CONJ_ASSOC]
  \\ `SUM (MAP el_length heap) <= dimword (:'a)` by
   (fs [X_LE_DIV] \\ Cases_on `2n ** shift_length conf` \\ fs [MULT_CLAUSES])
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac \\ SEP_F_TAC
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ strip_tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_heap_expand]
  \\ pop_assum mp_tac
  \\ full_simp_tac(srw_ss())[STAR_ASSOC]
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV) (RATOR_CONV
       (MOVE_OUT_CONV ``word_heap (curr:'a word) (temp:'a ml_heap)``)))
  \\ strip_tac \\ drule word_heap_IMP_word_list_exists
  \\ full_simp_tac(srw_ss())[word_heap_heap_expand]
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ strip_tac
  \\ rename1 `LENGTH ys = heap_length temp`
  \\ qexists_tac `ys` \\ full_simp_tac(srw_ss())[heap_length_def]
  \\ qexists_tac `xs1'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
QED

Theorem LIST_REL_EQ_MAP:
   !vs ws f. LIST_REL (λv w. f v = w) vs ws <=> ws = MAP f vs
Proof
  Induct \\ full_simp_tac(srw_ss())[]
QED

Theorem full_gc_IMP:
   full_gc (xs,heap,limit) = (t,heap2,n,T) ==>
    n <= limit /\ limit = heap_length heap
Proof
  full_simp_tac(srw_ss())[full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem is_ref_header_alt:
   good_dimindex (:'a) ==>
    (is_ref_header (w:'a word) <=> ~(w ' 2) /\ (w ' 3) /\ ~(w ' 4))
Proof
  fs [is_ref_header_def,fcpTheory.CART_EQ,good_dimindex_def] \\ rw []
  \\ fs [word_and_def,word_index,fcpTheory.FCP_BETA]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ TRY (qpat_x_assum `!x._`
       (fn th => qspec_then `2` mp_tac th
                 \\ qspec_then `3` mp_tac th
                 \\ qspec_then `4` mp_tac th ))
  \\ fs [] \\ Cases_on `i = 2`
  \\ fs [] \\ Cases_on `i = 3`
  \\ fs [] \\ Cases_on `i = 4` \\ fs []
QED

Theorem is_ref_header_thm:
   (word_payload addrs ll tt0 tt1 conf = (h,ts,c5)) /\ good_dimindex (:'a) /\
    conf.len_size + 5 <= dimindex (:'a) ==>
    (is_ref_header (h:'a word) ⇔ tt0 = RefTag)
Proof
  Cases_on `tt0` \\ fs [word_payload_def] \\ rw []
  \\ fs [make_header_def,make_byte_header_def,is_ref_header_alt]
  \\ fs [word_or_def,fcpTheory.FCP_BETA,good_dimindex_def,word_lsl_def,word_index]
  \\ rw []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,good_dimindex_def,word_lsl_def,word_index]
QED

Definition is_Ref_def:
  is_Ref is_ref_tag (DataElement xs l r) = is_ref_tag r /\
  is_Ref is_ref_tag _ = F
End

Definition len_inv_def:
  len_inv s <=>
    heap_length s.heap =
    heap_length (s.h1 ++ s.h2) + s.n + heap_length (s.r4 ++ s.r3 ++ s.r2 ++ s.r1)
End

Theorem word_gen_gc_move_thm:
   (gen_gc$gc_move gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_heap curr s.heap conf *
     word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_move conf (word_addr conf x,n2w s.a,pa,
        n2w (s.a+s.n),pa + bytes_in_word * n2w s.n,curr,m,dm) =
      (w:'a word_loc,i1,pa1,ib1,pb1,m1,c1)) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap pa s1.h2 conf *
       word_heap pb1 s1.r4 conf *
       word_list pa1 xs1 *
       frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length s1.heap = heap_length s.heap /\ c1 /\
      (i1 = n2w s1.a) /\
      (ib1 = n2w (s1.a + s1.n)) /\
      s1.n = LENGTH xs1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      pa1 = pa + bytes_in_word * n2w (heap_length s1.h2) /\
      pb1 = pa1 + bytes_in_word * n2w s1.n /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)
Proof
  reverse (Cases_on `x`) \\ fs[gen_gcTheory.gc_move_def] THEN1
   (rw [] \\ full_simp_tac(srw_ss())[word_heap_def,SEP_CLAUSES]
    \\ Cases_on `a` \\ fs [word_addr_def,word_gen_gc_move_def]
    \\ rveq \\ fs [] \\ asm_exists_tac \\ fs [heap_length_def])
  \\ CASE_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `heap_lookup k s.heap = SOME x`
  \\ Cases_on `x` \\ fs[] \\ srw_tac[][] \\ fs[word_addr_def]
  \\ qpat_x_assum `word_gen_gc_move conf _ = _` mp_tac
  \\ full_simp_tac std_ss [word_gen_gc_move_def,get_addr_and_1_not_0]
  \\ imp_res_tac heap_lookup_LESS
  \\ drule LE_DIV_LT_IMP
  \\ impl_tac \\ asm_rewrite_tac [] \\ strip_tac
  \\ asm_simp_tac std_ss [ptr_to_addr_get_addr]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ full_simp_tac std_ss [word_heap_def,SEP_CLAUSES] \\ rveq
  \\ full_simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
       AC WORD_MULT_ASSOC WORD_MULT_COMM]
  \\ `small_shift_length conf <= shift_length conf /\
      small_shift_length conf <> 0` by (EVAL_TAC \\ fs [] \\ NO_TAC)
  THEN1
   (helperLib.SEP_R_TAC
    \\ full_simp_tac(srw_ss())[LET_THM,theWord_def,is_fws_ptr_OR_3]
    \\ rw [] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[update_addr_def,shift_to_zero]
    \\ `2 <= shift_length conf` by (fs[shift_length_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[shift_around_under_big_shift]
    \\ full_simp_tac(srw_ss())[get_addr_def,select_shift_out]
    \\ full_simp_tac(srw_ss())[select_get_lowerbits,heap_length_def,isWord_def])
  \\ rename1 `_ = SOME (DataElement addrs ll tt)`
  \\ PairCases_on `tt`
  \\ full_simp_tac(srw_ss())[word_el_def]
  \\ `?h ts c5. word_payload addrs ll tt0 tt1 conf =
         (h:'a word,ts,c5)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac bool_ss [word_list_def]
  \\ SEP_R_TAC
  \\ full_simp_tac bool_ss [GSYM word_list_def,isWord_def]
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,isWord_def,theWord_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
  \\ `~is_fwd_ptr (Word h)` by (imp_res_tac NOT_is_fwd_ptr \\ fs [])
  \\ asm_rewrite_tac []
  \\ drule is_ref_header_thm
  \\ asm_simp_tac std_ss []
  \\ disch_then kall_tac
  \\ reverse (Cases_on `tt0 = RefTag`) \\ fs []
  THEN1
   (pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ `n2w (LENGTH ts) + 1w = n2w (LENGTH (Word h::ts)):'a word` by
          full_simp_tac(srw_ss())[LENGTH,ADD1,word_add_n2w]
    \\ full_simp_tac bool_ss []
    \\ drule memcpy_thm
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac(srw_ss())[gc_forward_ptr_thm] \\ rev_full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
    \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
    \\ imp_res_tac word_payload_IMP
    \\ rpt var_eq_tac
    \\ qpat_x_assum `LENGTH xs = s.n` (assume_tac o GSYM)
    \\ fs []
    \\ drule LESS_EQ_IMP_APPEND \\ strip_tac
    \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ disch_then (qspec_then `ys` assume_tac)
    \\ SEP_F_TAC
    \\ impl_tac THEN1
     (full_simp_tac(srw_ss())[ADD1,SUM_APPEND,X_LE_DIV,RIGHT_ADD_DISTRIB]
      \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
      \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
    \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[word_addr_def,word_add_n2w,ADD_ASSOC] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
         SEP_CLAUSES,word_el_def,LET_THM]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ SEP_W_TAC \\ qexists_tac `zs` \\ full_simp_tac(srw_ss())[]
    \\ reverse conj_tac THEN1
     (full_simp_tac(srw_ss())[update_addr_def,get_addr_def,
         select_shift_out,select_get_lowerbits,ADD1]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND])
    \\ pop_assum mp_tac
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
    \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,ADD1]
    \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ srw_tac[][] \\ qexists_tac `ts`
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  THEN1
   (rveq
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ `n2w (LENGTH ts) + 1w = n2w (LENGTH (Word h::ts)):'a word` by
          full_simp_tac(srw_ss())[LENGTH,ADD1,word_add_n2w]
    \\ full_simp_tac bool_ss []
    \\ drule memcpy_thm
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac(srw_ss())[gc_forward_ptr_thm] \\ rev_full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
    \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
    \\ imp_res_tac word_payload_IMP
    \\ rpt var_eq_tac
    \\ qpat_x_assum `LENGTH xs = s.n` (assume_tac o GSYM)
    \\ fs []
    \\ drule LESS_EQ_IMP_APPEND_ALT \\ strip_tac
    \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ disch_then (qspec_then `zs` assume_tac)
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,ADD1]
    \\ SEP_F_TAC
    \\ impl_tac THEN1
     (full_simp_tac(srw_ss())[ADD1,SUM_APPEND,X_LE_DIV,RIGHT_ADD_DISTRIB]
      \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
      \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
    \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[word_addr_def,word_add_n2w,ADD_ASSOC] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
         SEP_CLAUSES,word_el_def,LET_THM,is_Ref_def]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ SEP_W_TAC \\ qexists_tac `ys` \\ full_simp_tac(srw_ss())[]
    \\ reverse conj_tac THEN1
     (full_simp_tac(srw_ss())[update_addr_def,get_addr_def,
         select_shift_out,select_get_lowerbits,ADD1]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND])
    \\ pop_assum mp_tac
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
    \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,ADD1]
    \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ srw_tac[][] \\ qexists_tac `ts`
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [WORD_MUL_LSL])
QED

Theorem gc_move_with_NIL:
   !x s y t.
      gen_gc$gc_move gen_conf s x = (y,t) /\ t.ok ==>
      (let (y,s1) = gc_move gen_conf (s with <| h2 := []; r4 := [] |>) x in
        (y,s1 with <| h2 := s.h2 ++ s1.h2; r4 := s1.r4 ++ s.r4 |>)) = (y,t)
Proof
  Cases \\ fs [gen_gcTheory.gc_move_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
QED

Theorem gc_move_with_NIL_LEMMA:
   !x s y t h2 r4 y1 t1.
      gen_gc$gc_move gen_conf s x = (y1,t1) /\ t1.ok ==>
      ?x1 x2.
        t1.h2 = s.h2 ++ x1 /\
        t1.r4 = x2 ++ s.r4 /\
        gen_gc$gc_move gen_conf (s with <| h2 := []; r4 := [] |>) x =
          (y1,t1 with <| h2 := x1; r4 := x2 |>)
Proof
  Cases \\ fs [gen_gcTheory.gc_move_def] \\ rw []
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
QED

val gc_move_list_ok_irr0 = prove(
  ``!x s y1 y2 t1 t2 h2 r4.
      gen_gc$gc_move gen_conf s x = (y1,t1) /\
      gen_gc$gc_move gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2) ==>
      y1 = y2 /\ ?x1 x2. t2 = t1 with <| h2 := x1 ; r4 := x2 |>``,
  Cases \\ fs [gen_gcTheory.gc_move_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []);

Theorem gc_move_list_ok_irr:
   !x s y1 y2 t1 t2 h2 r4.
      gen_gc$gc_move_list gen_conf s x = (y1,t1) /\ t1.ok /\
      gen_gc$gc_move_list gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2) ==>
      t2.ok
Proof
  Induct \\ fs [gen_gcTheory.gc_move_list_def]
  \\ rw [] \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ first_x_assum match_mp_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ qpat_x_assum `_.ok` kall_tac
  \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ metis_tac [gc_move_list_ok_irr0]
QED

Theorem gc_move_list_with_NIL_LEMMA = Q.prove(`
  !x s y t h2 r4 y1 t1.
      gen_gc$gc_move_list gen_conf s x = (y1,t1) /\ t1.ok ==>
      ?x1 x2.
        t1.h2 = s.h2 ++ x1 /\
        t1.r4 = x2 ++ s.r4 /\
        gen_gc$gc_move_list gen_conf (s with <| h2 := []; r4 := [] |>) x =
          (y1,t1 with <| h2 := x1; r4 := x2 |>)`,
  Induct \\ fs [gen_gcTheory.gc_move_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rename1 `gc_move gen_conf s h = (x3,state3)`
  \\ rename1 `_ = (x4,state4)`
  \\ `state3.ok` by imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ drule (SIMP_RULE std_ss [] gc_move_with_NIL_LEMMA) \\ fs []
  \\ strip_tac \\ fs [] \\ rveq
  \\ first_assum drule \\ asm_rewrite_tac []
  \\ `state''.ok` by imp_res_tac gc_move_list_ok_irr
  \\ qpat_x_assum `gc_move_list gen_conf state3 x = _` kall_tac
  \\ first_x_assum drule \\ asm_rewrite_tac []
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]) |> SIMP_RULE std_ss [];

Theorem gc_move_list_with_NIL:
   !x s y t.
      gen_gc$gc_move_list gen_conf s x = (y,t) /\ t.ok ==>
      (let (y,s1) = gc_move_list gen_conf (s with <| h2 := []; r4 := [] |>) x in
        (y,s1 with <| h2 := s.h2 ++ s1.h2; r4 := s1.r4 ++ s.r4 |>)) = (y,t)
Proof
  rw [] \\ drule gc_move_list_with_NIL_LEMMA \\ fs []
  \\ strip_tac \\ fs [] \\ fs [gc_sharedTheory.gc_state_component_equality]
QED

Theorem word_gen_gc_move_roots_thm:
   !x xs x1 w s1 s pb1 pa1 pa m1 m ib1 i1 frame dm curr c1.
    (gen_gc$gc_move_list gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_heap curr s.heap conf *
     word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_move_roots conf (MAP (word_addr conf) x,n2w s.a,pa,
        n2w (s.a+s.n),pa + bytes_in_word * n2w s.n,curr,m,dm) =
      (w:'a word_loc list,i1,pa1,ib1,pb1,m1,c1)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap pa s1.h2 conf *
       word_heap pb1 s1.r4 conf *
       word_list pa1 xs1 *
       frame) (fun2set (m1,dm)) /\
      (w = MAP (word_addr conf) x1) /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ (ib1 = n2w (s1.a + s1.n)) /\ s1.n = LENGTH xs1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      pa1 = pa + bytes_in_word * n2w (heap_length s1.h2) /\
      pb1 = pa1 + bytes_in_word * n2w s1.n /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)
Proof
  Induct
  THEN1
   (fs [gen_gcTheory.gc_move_list_def,word_gen_gc_move_roots_def] \\ rw []
    \\ fs [word_heap_def,SEP_CLAUSES] \\ asm_exists_tac \\ fs [])
  \\ fs [gen_gcTheory.gc_move_list_def,word_gen_gc_move_roots_def]
  \\ rw [] \\ ntac 4 (pairarg_tac \\ fs []) \\ rveq
  \\ fs [MAP]
  \\ drule (GEN_ALL word_gen_gc_move_thm) \\ fs []
  \\ `state'.ok` by imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ rpt (disch_then drule)
  \\ strip_tac \\ rveq \\ fs []
  \\ drule gc_move_list_with_NIL
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ rveq \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ strip_tac \\ SEP_F_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ rename1 `s2.n = LENGTH xs2`
  \\ rfs []
  \\ qexists_tac `xs2` \\ fs []
  \\ fs [word_heap_APPEND]
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Theorem word_gen_gc_move_list_thm = Q.prove(`
  !x xs x1 w s1 s pb1 pa1 pa m1 m ib1 i1 frame dm curr c1 k k1.
    (gen_gc$gc_move_list gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_heap curr s.heap conf * word_list pa xs *
     word_list k (MAP (word_addr conf) x) * frame) (fun2set (m,dm)) /\
    (word_gen_gc_move_list conf (k,n2w (LENGTH x),n2w s.a,pa,
        n2w (s.a+s.n),pa + bytes_in_word * n2w s.n,curr:'a word,m,dm) =
      (k1,i1,pa1,ib1,pb1,m1,c1)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) /\ LENGTH x < dimword (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap pa s1.h2 conf *
       word_heap pb1 s1.r4 conf *
       word_list pa1 xs1 *
       word_list k (MAP (word_addr conf) x1) *
       frame) (fun2set (m1,dm)) /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ (ib1 = n2w (s1.a + s1.n)) /\ s1.n = LENGTH xs1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      k1 = k + n2w (LENGTH x) * bytes_in_word /\
      pa1 = pa + bytes_in_word * n2w (heap_length s1.h2) /\
      pb1 = pa1 + bytes_in_word * n2w s1.n /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)`,
  Induct
  THEN1
   (fs [gen_gcTheory.gc_move_list_def,Once word_gen_gc_move_list_def] \\ rw []
    \\ fs [word_heap_def,SEP_CLAUSES] \\ asm_exists_tac \\ fs [])
  \\ fs [gen_gcTheory.gc_move_list_def]
  \\ once_rewrite_tac [word_gen_gc_move_list_def]
  \\ rpt strip_tac \\ fs []
  \\ rw [] \\ ntac 4 (pairarg_tac \\ fs []) \\ rveq
  \\ fs [ADD1,GSYM word_add_n2w,word_list_def]
  \\ ntac 4 (pop_assum mp_tac) \\ SEP_R_TAC \\ fs []
  \\ rpt strip_tac
  \\ drule (GEN_ALL word_gen_gc_move_thm) \\ fs []
  \\ `state'.ok` by imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ fs [GSYM STAR_ASSOC]
  \\ rpt (disch_then drule)
  \\ fs [word_add_n2w]
  \\ strip_tac \\ rveq \\ fs []
  \\ drule gc_move_list_with_NIL
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ rveq \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ qpat_x_assum `word_gen_gc_move_list conf _ = _` mp_tac
  \\ SEP_W_TAC
  \\ rpt strip_tac
  \\ SEP_F_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ rename1 `s2.n = LENGTH xs2`
  \\ rfs []
  \\ qexists_tac `xs2` \\ fs []
  \\ fs [word_heap_APPEND]
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC]) |> SIMP_RULE std_ss [];

Definition word_heap_parts_def:
  word_heap_parts conf p s xs =
    word_heap p (s.h1 ++ s.h2) conf *
    word_list (p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2))) xs *
    word_heap (p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2) + LENGTH xs))
      (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) conf
End

Theorem gc_move_const:
   !l s xs' s'.
      gen_gc$gc_move gen_conf s l = (xs',s') ==>
      s'.h1 = s.h1 /\ s'.r1 = s.r1 /\ s'.r2 = s.r2 /\ s'.r3 = s.r3
Proof
  Cases \\ fs [gen_gcTheory.gc_move_def] \\ rpt gen_tac
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs []
QED

Theorem gc_move_list_const:
   !l s xs' s'.
      gen_gc$gc_move_list gen_conf s l = (xs',s') ==>
      s'.h1 = s.h1 /\ s'.r1 = s.r1 /\ s'.r2 = s.r2 /\ s'.r3 = s.r3
Proof
  Induct \\ fs [gen_gcTheory.gc_move_list_def]
  \\ rpt gen_tac \\ rpt (pairarg_tac \\ fs [])
  \\ fs [] \\ imp_res_tac gc_move_const \\ res_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
QED

Theorem gc_move_data_const:
   !gen_conf s s'.
      gen_gc$gc_move_data gen_conf s = s' ==>
      s'.r1 = s.r1 /\ s'.r2 = s.r2 /\ s'.r3 = s.r3
Proof
  ho_match_mp_tac gen_gcTheory.gc_move_data_ind
  \\ rpt (gen_tac ORELSE disch_then assume_tac)
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gen_gcTheory.gc_move_data_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TRY (strip_tac \\ rveq \\ fs [] \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs []
  \\ TRY (strip_tac \\ rveq \\ fs [] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rfs [] \\ imp_res_tac gc_move_list_const \\ fs []
QED

Theorem gc_move_refs_const:
   !gen_conf s s'.
      gen_gc$gc_move_refs gen_conf s = s' ==>
      s'.h1 = s.h1
Proof
  ho_match_mp_tac gen_gcTheory.gc_move_refs_ind
  \\ rpt (gen_tac ORELSE disch_then assume_tac)
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gen_gcTheory.gc_move_refs_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ TRY (strip_tac \\ rveq \\ fs [] \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs []
  \\ TRY (strip_tac \\ rveq \\ fs [] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rfs [] \\ imp_res_tac gc_move_list_const \\ fs []
QED

Theorem heap_length_gc_forward_ptr:
   !hs n k a ok heap.
      gc_forward_ptr n hs k a ok = (heap,T) ==>
      heap_length heap = heap_length hs /\ ok
Proof
  Induct \\ once_rewrite_tac [gc_forward_ptr_def] \\ rpt gen_tac
  THEN1 fs []
  \\ IF_CASES_TAC THEN1
   (strip_tac \\ rveq
    \\ qpat_x_assum `!x._` kall_tac
    \\ fs [] \\ rveq
    \\ fs [] \\ fs [heap_length_def,el_length_def,isDataElement_def])
  \\ IF_CASES_TAC THEN1 simp_tac std_ss []
  \\ simp_tac std_ss [LET_THM]
  \\ pairarg_tac \\ asm_rewrite_tac []
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac \\ rveq
  \\ first_x_assum drule \\ rw []
  \\ fs [heap_length_def]
QED

Theorem gc_move_thm:
   !l s l1 s1.
      gen_gc$gc_move gen_conf s l = (l1,s1) /\ s1.ok /\ len_inv s ==>
      len_inv s1
Proof
  Cases \\ fs [gen_gcTheory.gc_move_def] \\ rpt gen_tac
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ CASE_TAC \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ fs [len_inv_def]
  \\ imp_res_tac heap_length_gc_forward_ptr
  \\ fs [heap_length_def,el_length_def,SUM_APPEND]
QED

Theorem gc_move_list_thm:
   !l s l1 s1.
      gen_gc$gc_move_list gen_conf s l = (l1,s1) /\ s1.ok /\ len_inv s ==>
      len_inv s1
Proof
  Induct \\ fs [gen_gcTheory.gc_move_list_def]
  \\ rpt gen_tac \\ rpt (pairarg_tac \\ fs [])
  \\ fs [] \\ imp_res_tac gc_move_const \\ res_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ drule gen_gcTheory.gc_move_list_ok \\ fs [] \\ strip_tac
  \\ imp_res_tac gc_move_thm
  \\ fs []
QED

Theorem word_list_IMP_limit:
   (word_list (curr:'a word) hs * frame) (fun2set (m,dm)) /\
    good_dimindex (:'a) ==>
    LENGTH hs <= dimword (:'a) DIV (dimindex (:α) DIV 8)
Proof
  rw [] \\ CCONTR_TAC
  \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
  \\ fs [GSYM NOT_LESS]
  \\ imp_res_tac LESS_LENGTH
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ rveq \\ fs [word_list_APPEND]
  \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ qmatch_asmsub_abbrev_tac `curr + ww`
  \\ Cases_on `ys1` \\ fs []
  \\ fs [word_list_def]
  \\ `curr <> curr + ww` by SEP_NEQ_TAC
  \\ pop_assum mp_tac \\ fs []
  \\ unabbrev_all_tac
  \\ once_rewrite_tac [GSYM n2w_mod]
  \\ fs [dimword_def]
QED

Theorem word_el_eq_word_list:
   !hs curr frame.
      (word_el (curr:'a word) hs conf * frame) (fun2set (m,dm)) ==>
      ?xs. (word_list curr xs * frame) (fun2set (m,dm)) /\
           el_length hs = LENGTH xs /\
           !frame1 curr1 m1. (word_list curr1 xs * frame1) (fun2set (m1,dm)) ==>
            (word_el curr1 hs conf *frame1) (fun2set (m1,dm))
Proof
  Cases \\ fs [word_el_def,el_length_def,word_list_exists_def]
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  THEN1 (rw [] \\ asm_exists_tac \\ fs [] \\ rpt strip_tac \\ asm_exists_tac \\ fs[])
  THEN1 (rw [] \\ fs [GSYM word_list_def] \\ asm_exists_tac \\ fs[] \\ rpt strip_tac
         \\ qexists_tac `xs` \\ fs[])
  \\ Cases_on `b` \\ fs [word_el_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `q` \\ fs [word_payload_def] \\ rfs [] \\ rveq \\ fs []
QED

Theorem word_heap_eq_word_list_strong:
   !(hs:'a ml_heap) curr frame.
      (word_heap (curr:'a word) (hs:'a ml_heap) conf * frame) (fun2set (m,dm)) ==>
      ?xs. (word_list curr xs * frame) (fun2set (m,dm)) /\
            heap_length hs = LENGTH xs /\
            !curr1 frame1 m1. (word_list curr1 xs * frame1) (fun2set (m1,dm))
              ==> (word_heap curr1 hs conf * frame1) (fun2set (m1,dm))
Proof
  Induct
  >- rw[word_list_def,word_heap_def]
  \\ rw [] \\ fs [word_heap_def] \\ fs [GSYM STAR_ASSOC]
  \\ drule word_el_eq_word_list
  \\ strip_tac \\ pop_assum mp_tac \\ SEP_F_TAC \\ rpt strip_tac
  \\ qexists_tac `xs ++ xs'`
  \\ fs [word_list_APPEND,AC STAR_ASSOC STAR_COMM,heap_length_def] \\ rfs []
  \\ rpt strip_tac
  \\ fs[STAR_ASSOC]
  \\ first_x_assum drule
  \\ strip_tac
  \\ qabbrev_tac `a1 = word_heap (curr + bytes_in_word * n2w (LENGTH xs)) hs conf`
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ fs[STAR_ASSOC] \\ SEP_F_TAC \\ fs[AC STAR_ASSOC STAR_COMM]
QED

Theorem word_heap_eq_word_list:
   !(hs:'a ml_heap) curr frame.
      (word_heap (curr:'a word) (hs:'a ml_heap) conf * frame) (fun2set (m,dm)) ==>
      ?xs. (word_list curr xs * frame) (fun2set (m,dm)) /\
            heap_length hs = LENGTH xs
Proof
  metis_tac [word_heap_eq_word_list_strong]
QED

Theorem word_heap_IMP_limit:
   (word_heap (curr:'a word) (hs:'a ml_heap) conf * frame) (fun2set (m,dm)) /\
    good_dimindex (:'a) ==>
    heap_length hs <= dimword (:'a) DIV (dimindex (:α) DIV 8)
Proof
  rpt strip_tac
  \\ drule word_heap_eq_word_list \\ strip_tac
  \\ drule word_list_IMP_limit \\ fs []
QED

Theorem word_gen_gc_move_refs_thm:
   !k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1 p1.
    (gen_gc$gc_move_refs gen_conf s = s1) /\ s1.ok /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length s.heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_refs conf k
       ((* r2a *) p + bytes_in_word *
          n2w (heap_length (s.h1 ++ s.h2 ++ s.r4 ++ s.r3) + LENGTH xs),
        (* r1a *) p + bytes_in_word *
          n2w (heap_length (s.h1 ++ s.h2 ++ s.r4 ++ s.r3 ++ s.r2) + LENGTH xs),
        n2w s.a,
        (* pa *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2)),
        n2w (s.a+s.n),
        (* pb *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2) + s.n),
        curr:'a word,m,dm) =
      (p1,i1,pa1,ib1,pb1,m1,c1)) /\
    LENGTH s.r2 <= k /\ len_inv s /\
    (word_heap curr s.heap conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\ s1.r3 = [] /\ s1.r2 = [] /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ (ib1 = n2w (s1.a + s1.n)) /\ s1.n = LENGTH xs1 /\
      heap_length s.h2 + s.n + heap_length s.r4 =
      heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      pa1 = p + bytes_in_word * n2w (heap_length (s1.h1 ++ s1.h2)) /\
      pb1 = p + bytes_in_word * n2w (heap_length (s1.h1 ++ s1.h2) + s1.n) /\
      p1 = p + bytes_in_word * n2w (heap_length
              (s.h1 ++ s.h2 ++ s.r4 ++ s.r3 ++ s.r2) + LENGTH xs) /\ len_inv s1 /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)
Proof
  completeInduct_on `k` \\ rpt strip_tac
  \\ fs [PULL_FORALL,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ qpat_x_assum `gc_move_refs gen_conf s = s1` mp_tac
  \\ once_rewrite_tac [gen_gcTheory.gc_move_refs_def]
  \\ CASE_TAC THEN1
   (rw [] \\ fs []
    \\ qpat_x_assum `word_gen_gc_move_refs conf k _ = _` mp_tac
    \\ once_rewrite_tac [word_gen_gc_move_refs_def]
    \\ fs [] \\ strip_tac \\ rveq
    \\ qexists_tac `xs`
    \\ fs [word_heap_parts_def]
    \\ fs [len_inv_def])
  \\ CASE_TAC
  THEN1 (strip_tac \\ rveq \\ fs [])
  THEN1 (strip_tac \\ rveq \\ fs [])
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rename1 `_ = (_,s3)`
  \\ strip_tac
  \\ `s3.ok` by (rveq \\ imp_res_tac gen_gcTheory.gc_move_refs_ok \\ fs [])
  \\ qmatch_asmsub_abbrev_tac `gc_move_refs gen_conf s4`
  \\ rveq
  \\ `len_inv s3` by (imp_res_tac gc_move_list_thm \\ fs [] \\ NO_TAC)
  \\ `s3.h1 = s.h1 /\ s3.r1 = s.r1 /\ s3.r2 = s.r2 /\ s3.r3 = s.r3` by
    (drule gc_move_list_const \\ fs [])
  \\ `len_inv s4` by
    (unabbrev_all_tac
     \\ fs [len_inv_def,heap_length_def,SUM_APPEND,el_length_def] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM STAR_ASSOC]
  \\ drule word_heap_IMP_limit
  \\ full_simp_tac std_ss [STAR_ASSOC] \\ strip_tac
  \\ drule gc_move_list_with_NIL \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ PairCases_on `b`
  \\ rfs [is_Ref_def] \\ rveq
  \\ qpat_x_assum `word_gen_gc_move_refs conf k _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_refs_def]
  \\ IF_CASES_TAC THEN1
   (fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ qsuff_tac `F` \\ fs []
    \\ fs [heap_length_def,el_length_def]
    \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ pop_assum mp_tac \\ fs [bytes_in_word_def,word_mul_n2w]
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac `nn MOD _`
    \\ qsuff_tac `nn < dimword (:α)`
    \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
    \\ rfs [dimword_def]
    \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
  \\ simp [] \\ pop_assum kall_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM heap_length_def]
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ rfs [] \\ rveq
  \\ ntac 4 (pop_assum mp_tac)
  \\ SEP_R_TAC \\ fs [theWord_def,isWord_def]
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_list conf (newp,_)`
  \\ rpt strip_tac
  \\ drule word_gen_gc_move_list_thm \\ fs []
  \\ fs [is_Ref_def]
  \\ strip_tac
  \\ SEP_F_TAC \\ fs [GSYM word_add_n2w]
  \\ impl_tac THEN1
   (rfs [good_dimindex_def] \\ rfs [dimword_def]
    \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
  \\ strip_tac \\ rveq
  \\ qpat_x_assum `s.n = _` (assume_tac o GSYM)
  \\ fs [el_length_def,heap_length_def]
  \\ fs [GSYM heap_length_def] \\ rfs []
  \\ qmatch_asmsub_abbrev_tac `word_gen_gc_move_refs conf _ input1 = _`
  \\ qpat_x_assum `!m:num. _`
       (qspecl_then [`k-1`,`s4`,`m'`,`dm`,`curr`,`xs1`] mp_tac) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_refs conf _ input2 = _`
  \\ `input1 = input2` by
   (unabbrev_all_tac \\ simp_tac std_ss [] \\ rpt strip_tac
    \\ fs [SUM_APPEND,el_length_def]
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ NO_TAC)
  \\ fs []
  \\ disch_then (qspec_then `frame` mp_tac)
  \\ impl_tac THEN1
   (qunabbrev_tac `s4` \\ fs [is_Ref_def]
    \\ ntac 3 (pop_assum kall_tac)
    \\ qpat_x_assum `_ (fun2set (_,dm))` mp_tac
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
    \\ `LENGTH xs' = LENGTH l` by
          (imp_res_tac gen_gcTheory.gc_move_list_length \\ fs [])
    \\ qunabbrev_tac `newp`
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ match_mp_tac (METIS_PROVE [] ``f = g ==> f x ==> g x``)
    \\ fs [AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC))
  \\ strip_tac
  \\ qexists_tac `xs1'` \\ fs []
  \\ qabbrev_tac `s5 = gc_move_refs gen_conf s4`
  \\ qunabbrev_tac `s4` \\ fs [is_Ref_def]
  \\ fs [el_length_def,SUM_APPEND]
  \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
QED

Theorem word_gen_gc_move_data_thm:
   !k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1.
    (gen_gc$gc_move_data gen_conf s = s1) /\ s1.ok /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length s.heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    conf.len_size + 2 < dimindex (:α) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_data conf k
       ((* h2a *) p + bytes_in_word * n2w (heap_length s.h1),
        n2w s.a,
        (* pa *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2)),
        n2w (s.a+s.n),
        (* pb *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2) + s.n),
        curr:'a word,m,dm) =
      (i1,pa1,ib1,pb1,m1,c1)) /\
    heap_length s.h2 + s.n + heap_length s.r4 <= k /\ len_inv s /\
    (word_heap curr s.heap conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\ s1.h2 = [] /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ (ib1 = n2w (s1.a + s1.n)) /\
      s1.n = LENGTH xs1 /\ len_inv s1 /\
      heap_length (s1.h1 ++ s1.h2 ++ s1.r4) + s1.n =
      heap_length (s.h1 ++ s.h2 ++ s.r4) + s.n /\
      pa1 = p + bytes_in_word * n2w (heap_length (s1.h1 ++ s1.h2)) /\
      pb1 = p + bytes_in_word * n2w (heap_length (s1.h1 ++ s1.h2) + s1.n) /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)
Proof
  completeInduct_on `k` \\ rpt strip_tac
  \\ fs [PULL_FORALL,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ qpat_x_assum `gc_move_data gen_conf s = s1` mp_tac
  \\ once_rewrite_tac [gen_gcTheory.gc_move_data_def]
  \\ CASE_TAC THEN1
   (rw [] \\ fs []
    \\ qpat_x_assum `word_gen_gc_move_data conf k _ = _` mp_tac
    \\ once_rewrite_tac [word_gen_gc_move_data_def]
    \\ fs [] \\ strip_tac \\ rveq
    \\ qexists_tac `xs`
    \\ fs [word_heap_parts_def]
    \\ fs [len_inv_def])
  \\ IF_CASES_TAC THEN1 (rw[] \\ fs [])
  \\ CASE_TAC
  THEN1 (strip_tac \\ rveq \\ fs [])
  THEN1 (strip_tac \\ rveq \\ fs [])
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rename1 `_ = (_,s3)`
  \\ strip_tac
  \\ `s3.ok` by (rveq \\ imp_res_tac gen_gcTheory.gc_move_data_ok \\ fs [])
  \\ qmatch_asmsub_abbrev_tac `gc_move_data gen_conf s4`
  \\ rveq
  \\ `len_inv s3` by (imp_res_tac gc_move_list_thm \\ fs [] \\ NO_TAC)
  \\ `s3.h1 = s.h1 /\ s3.r1 = s.r1 /\ s3.r2 = s.r2 /\ s3.r3 = s.r3` by
    (drule gc_move_list_const \\ fs [])
  \\ `len_inv s4` by
    (unabbrev_all_tac
     \\ fs [len_inv_def,heap_length_def,SUM_APPEND,el_length_def]
     \\ drule gc_move_list_with_NIL \\ fs []
     \\ pairarg_tac \\ fs []
     \\ strip_tac \\ rveq \\ fs [SUM_APPEND,el_length_def] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM STAR_ASSOC]
  \\ drule word_heap_IMP_limit
  \\ full_simp_tac std_ss [STAR_ASSOC] \\ strip_tac
  \\ drule gc_move_list_with_NIL \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ PairCases_on `b`
  \\ rfs [is_Ref_def] \\ rveq
  \\ qpat_x_assum `word_gen_gc_move_data conf k _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_data_def]
  \\ IF_CASES_TAC THEN1
   (fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ qsuff_tac `F` \\ fs []
    \\ fs [heap_length_def,el_length_def]
    \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ pop_assum mp_tac \\ fs [bytes_in_word_def,word_mul_n2w]
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac `nn MOD _`
    \\ qsuff_tac `nn < dimword (:α)`
    \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
    \\ rfs [dimword_def]
    \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
  \\ simp [] \\ pop_assum kall_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM heap_length_def]
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def]
  \\ pairarg_tac \\ fs []
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ rfs [] \\ rveq
  \\ ntac 4 (pop_assum mp_tac)
  \\ SEP_R_TAC \\ fs [theWord_def,isWord_def]
  \\ Cases_on `word_bit 2 h` \\ fs []
  THEN1
   (rpt strip_tac \\ rveq
    \\ `l = []` by (imp_res_tac word_payload_T_IMP \\ rfs [] \\ NO_TAC)
    \\ rveq \\ fs [gen_gcTheory.gc_move_list_def] \\ rveq \\ fs []
    \\ qpat_x_assum `word_gen_gc_move_data conf (k − 1) _ = _` kall_tac
    \\ qpat_x_assum `word_gen_gc_move_list conf _ = _` kall_tac
    \\ rfs []
    \\ qpat_x_assum `!m:num. _`
         (qspecl_then [`k-1`,`s4`,`m`,`dm`,`curr`,`xs`] mp_tac) \\ fs []
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
           heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ qmatch_asmsub_abbrev_tac `word_gen_gc_move_data conf _ input1 = _`
    \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_data conf _ input2 = _`
    \\ `input1 = input2` by
     (unabbrev_all_tac \\ simp_tac std_ss [] \\ rpt strip_tac
      \\ fs [SUM_APPEND,el_length_def]
      \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
      \\ imp_res_tac word_payload_T_IMP \\ rfs [] \\ NO_TAC)
    \\ fs []
    \\ disch_then (qspec_then `frame` mp_tac)
    \\ impl_tac THEN1
     (qunabbrev_tac `s4` \\ fs [is_Ref_def]
      \\ qpat_x_assum `_ (fun2set (_,dm))` mp_tac
      \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
      \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
      \\ match_mp_tac (METIS_PROVE [] ``f = g ==> f x ==> g x``)
      \\ fs [AC STAR_ASSOC STAR_COMM,SEP_CLAUSES])
    \\ strip_tac
    \\ qexists_tac `xs1` \\ fs [] \\ rpt strip_tac
    \\ qabbrev_tac `s5 = gc_move_data gen_conf s4`
    \\ qunabbrev_tac `s4`
    \\ fs [el_length_def,SUM_APPEND]
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM)
    \\ pop_assum mp_tac \\ simp_tac std_ss []
    \\ CCONTR_TAC \\ fs [] \\ rfs [])
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_list conf (newp,_)`
  \\ rpt strip_tac \\ rveq
  \\ drule word_gen_gc_move_list_thm \\ fs []
  \\ drule word_payload_T_IMP
  \\ fs [] \\ strip_tac \\ rveq \\ fs []
  \\ fs [is_Ref_def]
  \\ strip_tac
  \\ SEP_F_TAC \\ fs [GSYM word_add_n2w]
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
  \\ impl_tac THEN1
   (rfs [good_dimindex_def] \\ rfs [dimword_def]
    \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
  \\ strip_tac \\ rveq
  \\ qpat_x_assum `s.n = _` (assume_tac o GSYM)
  \\ fs [el_length_def,heap_length_def]
  \\ fs [GSYM heap_length_def] \\ rfs []
  \\ qmatch_asmsub_abbrev_tac `word_gen_gc_move_data conf _ input1 = _`
  \\ qpat_x_assum `!m:num. _`
       (qspecl_then [`k-1`,`s4`,`m''`,`dm`,`curr`,`xs1`] mp_tac) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_data conf _ input2 = _`
  \\ `input1 = input2` by
   (unabbrev_all_tac \\ simp_tac std_ss [] \\ rpt strip_tac
    \\ fs [SUM_APPEND,el_length_def]
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ NO_TAC)
  \\ fs []
  \\ drule (GEN_ALL word_payload_swap)
  \\ drule gen_gcTheory.gc_move_list_length
  \\ strip_tac \\ disch_then drule \\ strip_tac
  \\ disch_then (qspec_then `frame` mp_tac)
  \\ impl_tac THEN1
   (qunabbrev_tac `s4` \\ fs [is_Ref_def]
    \\ qpat_x_assum `_ (fun2set (_,dm))` mp_tac
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
    \\ qunabbrev_tac `newp`
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ fs [AC STAR_ASSOC STAR_COMM,SEP_CLAUSES])
  \\ strip_tac
  \\ qexists_tac `xs1'` \\ fs []
  \\ qabbrev_tac `s5 = gc_move_data gen_conf s4`
  \\ qunabbrev_tac `s4` \\ fs [is_Ref_def]
  \\ fs [el_length_def,SUM_APPEND]
  \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
QED

Theorem LENGTH_LESS_EQ_SUM_el_length:
   !t. LENGTH t <= SUM (MAP el_length t)
Proof
  Induct \\ fs [] \\ Cases \\ fs [el_length_def]
QED

Theorem word_gen_gc_move_loop_thm:
   !k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1.
    (gen_gc$gc_move_loop gen_conf s k = s1) /\ s1.ok /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length s.heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    conf.len_size + 2 < dimindex (:α) /\ s.r3 = [] /\ s.r2 = [] /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_loop conf k
       ((* pax *) p + bytes_in_word * n2w (heap_length s.h1),
        n2w s.a,
        (* pa *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2)),
        n2w (s.a+s.n),
        (* pb *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2) + s.n),
        (* pbx *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2 ++ s.r4) + s.n),
        curr:'a word,m,dm) =
      (i1,pa1,ib1,pb1,m1,c1)) /\ len_inv s /\
    (word_heap curr s.heap conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\
      s1.h2 = [] /\ s1.r4 = [] /\ s1.r3 = [] /\ s1.r2 = [] /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ s1.n = LENGTH xs1 /\ len_inv s1 /\
      pa1 = p + bytes_in_word * n2w (heap_length s1.h1) /\
      pb1 = p + bytes_in_word * n2w (heap_length s1.h1 + s1.n) /\
      (ib1 = n2w (s1.a + s1.n)) /\
      EVERY (is_Ref gen_conf.isRef) s1.r1
Proof
  completeInduct_on `k` \\ rpt strip_tac
  \\ fs [PULL_FORALL,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ qpat_x_assum `gc_move_loop gen_conf s k = s1` mp_tac
  \\ once_rewrite_tac [gen_gcTheory.gc_move_loop_def]
  \\ TOP_CASE_TAC THEN1
   (TOP_CASE_TAC THEN1
     (rw [] \\ qexists_tac `xs` \\ fs []
      \\ pop_assum mp_tac \\ fs [Once word_gen_gc_move_loop_def]
      \\ rw [] \\ fs [])
    \\ strip_tac
    \\ `?s7. gen_gc$gc_move_data gen_conf s = s7` by fs [] \\ fs []
    \\ Cases_on `k = 0` \\ fs [] THEN1 (rveq \\ fs [])
    \\ drule word_gen_gc_move_data_thm
    \\ disch_then (qspecl_then [`dimword (:'a)`,`m`,`dm`,`curr`] mp_tac)
    \\ qpat_x_assum `word_gen_gc_move_loop conf k _ = _` mp_tac
    \\ once_rewrite_tac [word_gen_gc_move_loop_def] \\ fs []
    \\ IF_CASES_TAC THEN1
     (qsuff_tac `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
      \\ fs [heap_length_def,el_length_def]
      \\ fs [bytes_in_word_def,word_mul_n2w]
      \\ fs [RIGHT_ADD_DISTRIB]
      \\ qmatch_goalsub_abbrev_tac `nn MOD _`
      \\ qsuff_tac `nn < dimword (:α)`
      THEN1
       (fs [] \\ Cases_on `h` \\ fs [el_length_def]
        \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
        \\ rfs [dimword_def]
        \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
      \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
      \\ rfs [dimword_def]
      \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
    \\ rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ rveq
    \\ imp_res_tac gen_gcTheory.gc_move_loop_ok \\ fs []
    \\ strip_tac \\ SEP_F_TAC
    \\ impl_tac THEN1
     (fs [] \\ fs [el_length_def,heap_length_def]
      \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
      \\ rfs [dimword_def]
      \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
    \\ strip_tac
    \\ qpat_x_assum `!m:num. _`
         (qspecl_then [`k-1`,`gc_move_data gen_conf s`,
                       `m'`,`dm`,`curr`,`xs1`] mp_tac) \\ fs []
    \\ rveq
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,
           heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ strip_tac \\ SEP_F_TAC
    \\ impl_tac
    THEN1 (fs [] \\ rveq \\ fs [SIMP_RULE std_ss [] gc_move_data_const])
    \\ strip_tac
    \\ asm_exists_tac \\ fs [])
  \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac `gc_move_refs gen_conf s2`
    \\ `?s7. gen_gc$gc_move_refs gen_conf s2 = s7` by fs [] \\ fs []
    \\ Cases_on `k = 0` \\ fs [] THEN1 (rveq \\ fs [])
    \\ drule word_gen_gc_move_refs_thm
    \\ disch_then (qspecl_then [`dimword (:'a)`,`m`,`dm`,`curr`,`xs`] mp_tac)
    \\ qpat_x_assum `word_gen_gc_move_loop conf k _ = _` mp_tac
    \\ once_rewrite_tac [word_gen_gc_move_loop_def] \\ fs []
    \\ IF_CASES_TAC THEN1
     (qsuff_tac `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
      \\ fs [heap_length_def,el_length_def]
      \\ fs [bytes_in_word_def,word_mul_n2w]
      \\ fs [RIGHT_ADD_DISTRIB]
      \\ qmatch_goalsub_abbrev_tac `nn MOD _`
      \\ qsuff_tac `nn < dimword (:α)`
      THEN1
       (fs [] \\ Cases_on `h` \\ fs [el_length_def]
        \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
        \\ rfs [dimword_def]
        \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
      \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
      \\ rfs [dimword_def]
      \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
    \\ rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ rveq
    \\ qunabbrev_tac `s2` \\ fs []
    \\ disch_then (qspec_then `frame` mp_tac)
    \\ impl_tac THEN1
     (imp_res_tac (SIMP_RULE std_ss [] gen_gcTheory.gc_move_loop_ok)
      \\ fs [word_heap_parts_def] \\ rfs []
      \\ fs [len_inv_def] \\ rfs []
      \\ fs [good_dimindex_def,dimword_def,heap_length_def,el_length_def,SUM_APPEND]
      \\ `LENGTH t <= SUM (MAP el_length t)` by fs [LENGTH_LESS_EQ_SUM_el_length]
      \\ rfs [] \\ fs [])
    \\ strip_tac \\ rveq
    \\ qpat_abbrev_tac `s6 = gc_move_refs gen_conf _`
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM)
    \\ fs []
    \\ qpat_x_assum `!m:num. _`
         (qspecl_then [`k-1`,`s6`,`m'`,`dm`,`curr`,`xs1`] mp_tac) \\ fs []
    \\ rveq
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,
           heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ qmatch_goalsub_abbrev_tac `word_gen_gc_move_loop conf _ input2 = _`
    \\ qmatch_asmsub_abbrev_tac `word_gen_gc_move_loop conf _ input1 = _`
    \\ qsuff_tac `input1 = input2`
    THEN1 (strip_tac \\ fs [])
    \\ rfs [] \\ unabbrev_all_tac
    \\ fs [SIMP_RULE std_ss [] gc_move_refs_const]
  \\ rewrite_tac [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL]
  \\ fs [GSYM WORD_LEFT_ADD_DISTRIB,word_add_n2w]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ fs []
  \\ qpat_abbrev_tac `n1 = SUM (MAP _ t)`
  \\ qpat_abbrev_tac `n2 = SUM (MAP _ s.h2)`
  \\ qpat_abbrev_tac `n3 = SUM (MAP _ s.h1)`
  \\ qpat_abbrev_tac `n6 = SUM (MAP _ _.h2)`
  \\ qpat_abbrev_tac `n7 = SUM (MAP _ _.r4)`
  \\ qpat_x_assum `LENGTH xs + n2 = _` (assume_tac o GSYM)
  \\ fs []
QED

Theorem word_gen_gc_thm:
   !m dm curr s1 pb1 pa1 m1 ib1 i1 frame c1 roots heap roots1 roots1' new.
    (gen_gc$gen_gc gen_conf (roots,heap) = (roots1,s1)) /\ s1.ok /\
    (word_gen_gc conf (MAP (word_addr conf) roots,curr,new,
          bytes_in_word * n2w (heap_length heap),m,dm) =
      (roots1',i1,pa1:'a word,ib1,pb1,m1,c1)) /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    conf.len_size + 2 < dimindex (:α) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    conf.len_size + 5 <= dimindex (:'a) /\
    good_dimindex (:'a) /\
    (word_heap curr heap conf *
     word_list_exists new (heap_length heap) *
     frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
    ?xs1.
      (word_heap curr s1.heap conf *
       word_heap_parts conf new s1 xs1 *
       frame) (fun2set (m1,dm)) /\
      s1.h2 = [] /\ s1.r4 = [] /\ s1.r3 = [] /\ s1.r2 = [] /\
      roots1' = MAP (word_addr conf) roots1 /\
      heap_length s1.heap = heap_length heap /\
      c1 /\ (i1 = n2w s1.a) /\ (ib1 = n2w (s1.a + s1.n)) /\
      pa1 = new + bytes_in_word * n2w (heap_length s1.h1) /\
      pb1 = new + bytes_in_word * n2w (heap_length s1.h1 + s1.n) /\
      roots1' = MAP (word_addr conf) roots1 /\
      s1.n = LENGTH xs1 /\ len_inv s1 /\
      EVERY (is_Ref gen_conf.isRef) s1.r1
Proof
  rpt gen_tac \\ once_rewrite_tac [gen_gcTheory.gen_gc_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ fs []
  \\ drule (word_gen_gc_move_loop_thm |> Q.GEN `p`)
  \\ drule word_gen_gc_move_roots_thm
  \\ fs [empty_state_def]
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ strip_tac \\ SEP_F_TAC \\ fs []
  \\ `state'.ok` by (rveq \\ imp_res_tac gen_gcTheory.gc_move_loop_ok)
  \\ imp_res_tac gen_gcTheory.gc_move_list_ok \\ fs []
  \\ pop_assum kall_tac \\ pop_assum (assume_tac o GSYM) \\ fs []
  \\ qpat_x_assum `word_gen_gc conf _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq
  \\ qmatch_asmsub_abbrev_tac `word_gen_gc_move_loop conf n3`
  \\ `heap_length heap < dimword (:α)` by
    (fs [good_dimindex_def,dimword_def] \\ fs [])
  \\ `n3 = heap_length heap /\
      (bytes_in_word * n2w (heap_length heap)) ⋙ shift (:α) =
      n2w (heap_length heap):'a word` by
   (unabbrev_all_tac \\ rewrite_tac [GSYM w2n_11,w2n_n2w,w2n_lsr]
    \\ fs [bytes_in_word_def,w2n_n2w,word_mul_n2w]
    \\ fs [good_dimindex_def,dimword_def,shift_def,
           ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] \\ NO_TAC)
  \\ unabbrev_all_tac \\ fs []
  \\ fs [] \\ strip_tac \\ rveq \\ fs []
  \\ qpat_abbrev_tac `s5 = gc_move_loop gen_conf state' _`
  \\ drule gc_move_list_const \\ strip_tac \\ fs []
  \\ simp [Once word_heap_parts_def]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ disch_then (qspecl_then [`new`,`m'`,`dm`,`curr`] mp_tac)
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,heap_length_APPEND]
  \\ strip_tac \\ SEP_F_TAC
  \\ impl_tac THEN1 fs [len_inv_def]
  \\ strip_tac \\ asm_exists_tac \\ fs []
QED

Theorem gc_forward_ptr_APPEND:
    !h1 n h2 a b ok.
  gc_forward_ptr n (h1 ++ h2) a b ok =
  if n < heap_length h1 then
    (λ(h,ok). (h++h2,ok)) (gc_forward_ptr n h1 a b ok)
  else
    (λ(h,ok). (h1++h,ok)) (gc_forward_ptr (n-heap_length h1) h2 a b ok)
Proof
  Induct
  >- fs[pairTheory.ELIM_UNCURRY]
  >> Cases >> rpt strip_tac >> fs[gc_forward_ptr_def]
  >> fs[el_length_def,heap_length_def]
  >> rw[] >> fs[]
  >> fs[pairTheory.ELIM_UNCURRY]
QED

Theorem heap_split_APPEND:
   heap_split (heap_length h1) (h1 ++ h2) = SOME(h1,h2)
Proof
  Induct_on `h1` >> fs[heap_split_def,heap_length_def]
QED

Theorem heap_split_APPEND':
   heap_split (SUM (MAP el_length h1)) (h1 ++ h2) = SOME(h1,h2)
Proof
  metis_tac[heap_split_APPEND,heap_length_def]
QED

Theorem heap_drop_APPEND:
   heap_drop (heap_length h1) (h1 ++ h2) = h2
Proof
  rw[heap_drop_def,heap_split_APPEND]
QED

Theorem heap_take_APPEND:
   heap_take (heap_length h1) (h1 ++ h2) = h1
Proof
  rw[heap_take_def,heap_split_APPEND]
QED

Theorem heap_drop_0:
   heap_drop 0 h = h
Proof
Cases_on `h` >> fs[heap_drop_def,heap_split_def]
QED

Theorem gc_forward_ptr_heap_split:
   !h1 h2 n h3 l n' b ok ok1 heap a b'.
   (heap_lookup n (h1 ++ h2 ++ h3) = SOME (DataElement l n' b)) /\
   (gc_forward_ptr n (h1 ++ h2 ++ h3) a b' ok = (heap,ok1)) /\
   n >= heap_length h1 /\ n < heap_length(h1 ++ h2)
   ==> heap = h1 ++ heap_take (heap_length h2) (heap_drop (heap_length h1) heap) ++ h3
Proof
  rw[gc_forward_ptr_APPEND] >> ntac 2 (pairarg_tac >> fs[] >> rveq)
  >> drule gc_forward_ptr_heap_length >> strip_tac
  >> ASM_SIMP_TAC std_ss [heap_take_APPEND,heap_drop_APPEND,GSYM APPEND_ASSOC]
QED

Theorem partial_gc_move_heap_split:
   (gen_gc_partial$gc_move conf s x = (x1,s1))
   /\ heap_segment (conf.gen_start,conf.refs_start) s.heap = SOME (h1,h2,h3)
   /\ conf.gen_start <= conf.refs_start
   ==> s1.heap = h1 ++ heap_take (heap_length h2) (heap_drop (heap_length h1) s1.heap) ++ h3
Proof
  Cases_on `x` >> rw[gen_gc_partialTheory.gc_move_def]
  >> fs[]
  >> drule heap_segment_IMP >> strip_tac
  >> fs[] >> rfs[]
  >> qpat_x_assum `_ = s.heap` (assume_tac o GSYM)
  >> qpat_x_assum `_ = conf.gen_start` (assume_tac o GSYM)
  >> fs[]
  >> SIMP_TAC std_ss [GSYM APPEND_ASSOC,heap_take_APPEND,heap_drop_APPEND]
  >> every_case_tac >> fs[] >> rveq >> fs[]
  >> SIMP_TAC std_ss [GSYM APPEND_ASSOC,heap_take_APPEND,heap_drop_APPEND]
  >> pairarg_tac >> fs[] >> rveq >> fs[]
  >> drule gc_forward_ptr_heap_split >> disch_then drule >> fs[]
QED

Theorem partial_gc_move_list_heap_split:
   !x conf s x1 s1 h1 h2 h3.
   (gen_gc_partial$gc_move_list conf s x = (x1,s1))
   /\ heap_segment (conf.gen_start,conf.refs_start) s.heap = SOME (h1,h2,h3)
   /\ conf.gen_start <= conf.refs_start
   ==> s1.heap = h1 ++ heap_take (heap_length h2) (heap_drop (heap_length h1) s1.heap) ++ h3
Proof
  Induct >> rpt strip_tac >> fs[gen_gc_partialTheory.gc_move_list_def]
  >> drule heap_segment_IMP >> strip_tac
  >> rveq >> fs[]
  >> qpat_x_assum `_ = s.heap` (assume_tac o GSYM)
  >> qpat_x_assum `_ = conf.gen_start` (assume_tac o GSYM)
  >> qpat_x_assum `_ = conf.refs_start` (assume_tac o GSYM)
  >- ASM_SIMP_TAC std_ss [heap_take_APPEND,heap_drop_APPEND,GSYM APPEND_ASSOC]
  >> ntac 2 (pairarg_tac >> fs[])
  >> drule partial_gc_move_heap_split >> fs[] >> strip_tac >> rveq >> fs[]
  >> drule gen_gc_partialTheory.gc_move_heap_length >> strip_tac
  >> rfs[] >> fs[]
  >> `heap_segment (conf.gen_start,conf.refs_start) (state'.heap)
      = SOME (h1,heap_take (heap_length h2) (heap_drop (heap_length h1) state'.heap),h3)`
       by(pop_assum mp_tac
          >> qpat_x_assum `state'.heap = _` (fn asm => PURE_ONCE_REWRITE_TAC[asm])
          >> fs[heap_length_APPEND]
          >> disch_then assume_tac
          >> fs[heap_length_APPEND]
          >> SIMP_TAC std_ss [heap_segment_def,heap_length_APPEND,heap_split_APPEND,GSYM APPEND_ASSOC]
          >> fs[]
          >> pop_assum (fn thm => rw[Once thm] >> assume_tac thm)
          >> fs[heap_split_APPEND,heap_drop_APPEND]
          >> SIMP_TAC std_ss [heap_drop_APPEND,GSYM APPEND_ASSOC]
          >> metis_tac[heap_take_APPEND])
  >> first_x_assum drule
  >> fs[]
  >> disch_then (fn thm => rw[Once thm])
  >> qpat_x_assum `heap_length _ = heap_length _` mp_tac
  >> qpat_x_assum `state'.heap = _` (fn asm => PURE_ONCE_REWRITE_TAC[asm])
  >> fs[heap_length_APPEND]
  >> disch_then (fn thm => rw[Once thm] >> assume_tac thm)
  >> SIMP_TAC std_ss [GSYM APPEND_ASSOC,heap_drop_APPEND,heap_take_APPEND]
  >> pop_assum (fn thm => fs[GSYM thm])
QED

Theorem word_gen_gc_partial_move_thm:
   (gen_gc_partial$gc_move gc_conf gcstate x = (x1,gcstate1)) /\
    gcstate.h2 = [] /\ gcstate.r4 = [] /\ gcstate1.ok /\
    gc_conf.limit = heap_length gcstate.heap /\
    good_dimindex (:α) /\
    heap_length gcstate.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    gc_conf.gen_start <= gc_conf.refs_start /\
    gc_conf.refs_start <= heap_length gcstate.heap /\
    (heap_segment (gc_conf.gen_start,gc_conf.refs_start) gcstate.heap = SOME(old,current,refs)) /\
    heap_length gcstate.heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    (word_heap (curr + bytes_in_word * n2w(heap_length old)) current conf * word_list pa xs * frame) (fun2set (m,dm)) /\
    (!t r. (gc_conf.isRef (t,r) <=> t = RefTag)) /\
    (word_gen_gc_partial_move conf (word_addr conf x,n2w gcstate.a,pa,curr,m,dm,
                                    bytes_in_word * n2w gc_conf.gen_start,
                                    bytes_in_word * n2w gc_conf.refs_start) =
      (w:'a word_loc,i1,pa1,m1,c1)) /\
    LENGTH xs = gcstate.n ==>
    ?xs1 current1.
      (word_heap (curr+ bytes_in_word * n2w(heap_length old)) current1 conf *
       word_heap pa gcstate1.h2 conf *
       word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length gcstate1.heap = heap_length gcstate.heap /\
      (heap_segment (gc_conf.gen_start,gc_conf.refs_start) gcstate1.heap = SOME(old,current1,refs)) /\
      c1 /\ (i1 = n2w gcstate1.a) /\ gcstate1.n = LENGTH xs1 /\
      gcstate.n = heap_length gcstate1.h2 + gcstate1.n + heap_length gcstate1.r4 /\
      pa1 = pa + bytes_in_word * n2w (heap_length gcstate1.h2)
Proof
  reverse (Cases_on `x`) \\
  full_simp_tac(srw_ss())[gc_move_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[word_heap_def,SEP_CLAUSES]
    \\ Cases_on `a` \\ full_simp_tac(srw_ss())[word_addr_def,word_gen_gc_partial_move_def]
    \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ rpt strip_tac
  \\ `n < heap_length gcstate.heap`
       by(every_case_tac >> fs[]
          >> qpat_x_assum `(x with ok := y) = z` (assume_tac o GSYM)
          >> fs[])
  \\ `bytes_in_word * n2w n <₊ bytes_in_word * n2w gc_conf.gen_start :'a word
       <=> n < gc_conf.gen_start` by
    (fs[bytes_in_word_def,word_add_n2w,word_mul_n2w,WORD_LO]
     \\ `n * (dimindex (:α) DIV 8) <
         heap_length gcstate.heap * (dimindex (:α) DIV 8)`
          by fs[good_dimindex_def]
     \\ `gc_conf.gen_start * (dimindex (:α) DIV 8) <=
         heap_length gcstate.heap * (dimindex (:α) DIV 8)`
          by fs[good_dimindex_def]
     \\ rw[LESS_MOD] \\ fs[good_dimindex_def])
  \\ `bytes_in_word * n2w gc_conf.refs_start ≤₊ bytes_in_word * n2w n :'a word
      <=> gc_conf.refs_start <= n` by
     (Cases_on `curr`
      \\ fs[bytes_in_word_def,word_add_n2w,word_mul_n2w,WORD_NOT_LOWER_EQUAL,WORD_LO]
      \\ `n * (dimindex (:α) DIV 8) <
          heap_length gcstate.heap * (dimindex (:α) DIV 8)`
           by fs[good_dimindex_def]
      \\ `gc_conf.refs_start * (dimindex (:α) DIV 8) <=
          heap_length gcstate.heap * (dimindex (:α) DIV 8)`
           by fs[good_dimindex_def]
      \\ rw[LESS_MOD]  \\ fs[good_dimindex_def] \\ rfs[] \\ fs[WORD_LS])
  \\ rpt (pop_assum MP_TAC)
  \\ PURE_ONCE_REWRITE_TAC [LET_THM] \\ BETA_TAC
  \\ IF_CASES_TAC THEN1
    (srw_tac[][]
     \\ full_simp_tac(srw_ss())[word_heap_def,SEP_CLAUSES]
     \\ full_simp_tac(srw_ss())[word_addr_def,word_gen_gc_partial_move_def,get_addr_and_1_not_0]
     \\ drule(GEN_ALL LE_DIV_LT_IMP)
     \\ disch_then drule
     \\ rpt strip_tac
     \\ fs [ptr_to_addr_get_addr]
     \\ rpt strip_tac
     \\ qexists_tac `xs`
     \\ fs[word_heap_def,heap_length_def,SEP_CLAUSES,word_addr_def])
  \\ CASE_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `heap_lookup k s.heap = SOME x`
  \\ Cases_on `x` \\ fs[] \\ srw_tac[][] \\ fs[word_addr_def]
  \\ drule heap_segment_IMP \\ fs[] \\ disch_then (assume_tac o GSYM)
  \\ fs[heap_lookup_APPEND,heap_length_APPEND] \\ rfs[heap_lookup_APPEND,heap_length_APPEND]
  \\ qpat_x_assum `word_gen_gc_partial_move conf _ = _` mp_tac
  \\ full_simp_tac std_ss [word_gen_gc_partial_move_def,get_addr_and_1_not_0]
  \\ fs[get_addr_and_1_not_0]
  \\ imp_res_tac heap_lookup_LESS
  \\ drule LE_DIV_LT_IMP
  \\ impl_tac \\ fs[]
  \\ asm_rewrite_tac [] \\ strip_tac
  \\ asm_simp_tac std_ss [ptr_to_addr_get_addr]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ full_simp_tac std_ss [word_heap_def,SEP_CLAUSES] \\ rveq
  \\ full_simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
       AC WORD_MULT_ASSOC WORD_MULT_COMM]
  \\ `small_shift_length conf <= shift_length conf /\
      small_shift_length conf <> 0` by (EVAL_TAC \\ fs [] \\ NO_TAC)
  \\ qpat_x_assum `k − heap_length old = heap_length ha` (assume_tac o GSYM)
  \\ fs[heap_length_APPEND]
  \\ full_simp_tac std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM, GSYM WORD_LEFT_ADD_DISTRIB,
                           word_add_n2w,SUB_LEFT_ADD]
  \\ `(if k ≤ heap_length old then heap_length old else k) = k`
      by rw[]
  \\ fs[]
  THEN1
   (helperLib.SEP_R_TAC
    \\ full_simp_tac(srw_ss())[LET_THM,theWord_def,is_fws_ptr_OR_3]
    \\ rw [] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[update_addr_def,shift_to_zero]
    \\ `2 <= shift_length conf` by (fs[shift_length_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[shift_around_under_big_shift]
    \\ full_simp_tac(srw_ss())[get_addr_def,select_shift_out]
    \\ full_simp_tac(srw_ss())[select_get_lowerbits,heap_length_def,isWord_def]
    \\ fs[]
   )
  \\ rename1 `_ = SOME (DataElement addrs ll tt)`
  \\ PairCases_on `tt`
  \\ full_simp_tac(srw_ss())[word_el_def]
  \\ `?h ts c5. word_payload addrs ll tt0 tt1 conf =
         (h:'a word,ts,c5)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac bool_ss [word_list_def]
  \\ SEP_R_TAC
  \\ full_simp_tac bool_ss [GSYM word_list_def,isWord_def]
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,isWord_def,theWord_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
  \\ `~is_fwd_ptr (Word h)` by (imp_res_tac NOT_is_fwd_ptr \\ fs [])
  \\ asm_rewrite_tac []
  \\ drule is_ref_header_thm
  \\ asm_simp_tac std_ss []
  \\ disch_then kall_tac
  \\ reverse (Cases_on `tt0 = RefTag`) \\ fs []
  THEN1
   (pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ `n2w (LENGTH ts) + 1w = n2w (LENGTH (Word h::ts)):'a word` by
          full_simp_tac(srw_ss())[LENGTH,ADD1,word_add_n2w]
    \\ full_simp_tac bool_ss []
    \\ drule memcpy_thm
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac(srw_ss())[gc_forward_ptr_thm] \\ rev_full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def]
    \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
    \\ imp_res_tac word_payload_IMP
    \\ rpt var_eq_tac
    \\ qpat_x_assum `LENGTH xs = s.n` (assume_tac o GSYM)
    \\ fs []
    \\ drule gc_forward_ptr_ok
    \\ fs[] \\ strip_tac
    \\ drule LESS_EQ_IMP_APPEND \\ strip_tac
    \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ disch_then (qspec_then `ys` assume_tac)
    \\ SEP_F_TAC
    \\ impl_tac THEN1
     (full_simp_tac(srw_ss())[ADD1,SUM_APPEND,X_LE_DIV,RIGHT_ADD_DISTRIB]
      \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
      \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
    \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[word_addr_def,word_add_n2w,ADD_ASSOC] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
         SEP_CLAUSES,word_el_def,LET_THM]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ SEP_W_TAC
    \\ qpat_x_assum `heap_length _ = _ − heap_length _` (assume_tac o GSYM)
    \\ fs[] \\ `k  = heap_length ha + heap_length old` by fs[] \\ rveq \\ fs[]
    \\ `(if heap_length ha + heap_length old ≤ heap_length old then
                LENGTH ts + 1
        else LENGTH ts + (heap_length ha + 1)) = LENGTH ts + (heap_length ha + 1)`
         by (Cases_on `heap_length ha` >> fs[])
    \\ pop_assum (fn thm => fs[thm])
    \\ `gc_forward_ptr (heap_length(old ++ ha))
         ((old ++ ha) ++
          DataElement addrs (LENGTH ts) (tt0,tt1)::(hb ++ refs)) s.a a
         T = ((old ++ ha) ++ ForwardPointer s.a a (LENGTH ts)::(hb++refs),T)`
        by(metis_tac[gc_forward_ptr_thm])
    \\ fs[heap_length_APPEND]
    \\ qexists_tac `zs` \\ qexists_tac `ha++ForwardPointer s.a a (LENGTH ts)::hb` \\ full_simp_tac(srw_ss())[] \\ rveq \\ fs[]
    \\ reverse conj_tac THEN1
     (full_simp_tac(srw_ss())[update_addr_def,get_addr_def,
         select_shift_out,select_get_lowerbits,ADD1]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,heap_length_APPEND]
      \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
      \\ fs[heap_length_def,SUM_APPEND,el_length_def]
      \\ fs[heap_segment_def]
      \\ full_simp_tac std_ss [heap_split_APPEND', GSYM APPEND_ASSOC]
      \\ fs[]
      \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC_CONS]
      \\ `heap_length(ha ++ ForwardPointer s.a a (LENGTH ts)::hb) =
           LENGTH ts + (SUM (MAP el_length ha) + (SUM (MAP el_length hb) +
           (SUM (MAP el_length old) + 1))) − heap_length old`
           by fs[heap_length_def,SUM_APPEND,el_length_def]
      \\ pop_assum (fn asm => rw[GSYM asm])
      \\ fs[heap_split_APPEND])
    \\ fs[word_heap_def,word_heap_APPEND]
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs[word_el_def,word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM,el_length_def]
    \\ qexists_tac `ts`
    \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,heap_length_def,ADD1])
  THEN1
   (rveq
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ rfs[]
    \\ metis_tac[gc_forward_ptr_ok])
QED

Theorem gc_partial_move_ok_irr:
   !x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial$gc_move gen_conf s x = (y1,t1) /\
      gen_gc_partial$gc_move gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2) ==>
      y1 = y2 /\ ?x1 x2. t2 = t1 with <| h2 := x1 ; r4 := x2 |>
Proof
  Cases \\ fs [gen_gc_partialTheory.gc_move_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
QED

Theorem gc_partial_move_ok_before:
   gen_gc_partial$gc_move gen_conf s x = (x1,s1) /\ s1.ok ==> s.ok
Proof
  Induct_on `x` >> rw[gen_gc_partialTheory.gc_move_def]
  >> fs[] >> every_case_tac >> fs[]
  >- (qpat_x_assum `s with ok := F = s1` (assume_tac o GSYM)
      >> fs[])
  >- (qpat_x_assum `s with ok := F = s1` (assume_tac o GSYM)
      >> fs[])
  >> pairarg_tac >> fs[]
  >> qpat_x_assum `_ = s1` (assume_tac o GSYM) >> fs[]
  >> sg `((s.ok ∧ n < heap_length s.heap) ∧ n' + 1 ≤ s.n ∧
        ¬gen_conf.isRef b)` >> fs []
  >> match_mp_tac (GEN_ALL gc_forward_ptr_ok)
  >> qexists_tac `a` >> qexists_tac `s.heap`
  >> qexists_tac `n` >> qexists_tac `s.a` >> qexists_tac `heap`
  >> fs[]
QED

Theorem gc_partial_move_list_ok_before:
   !x s x1 s1. gen_gc_partial$gc_move_list gen_conf s x = (x1,s1) /\ s1.ok ==> s.ok
Proof
  Induct_on `x` >> fs[gc_move_list_def] >> rpt strip_tac
  >> ntac 2 (pairarg_tac >> fs[]) >> metis_tac[gc_partial_move_ok_before]
QED

Theorem gc_partial_move_ref_list_ok_before:
   !x s x1 s1. gen_gc_partial$gc_move_ref_list gen_conf s x = (x1,s1) /\ s1.ok ==> s.ok
Proof
  Induct >> Cases >> fs[gc_move_ref_list_def] >> rpt strip_tac
  >> ntac 2 (pairarg_tac >> fs[]) >> metis_tac[gc_partial_move_list_ok_before]
QED

Theorem gc_partial_move_data_ok_before:
   !gen_conf s s1. gen_gc_partial$gc_move_data gen_conf s = s1 /\ s1.ok ==> s.ok
Proof
  recInduct (fetch "gen_gc_partial" "gc_move_data_ind")
  \\ rw[] \\ pop_assum mp_tac \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (CASE_TAC \\ simp_tac (srw_ss()) [LET_THM])
  \\ pairarg_tac \\ fs [] \\ strip_tac \\ res_tac
  \\ imp_res_tac gc_partial_move_list_ok_before
QED

Theorem gc_partial_move_list_ok_irr:
   !x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial$gc_move_list gen_conf s x = (y1,t1) /\ t1.ok /\
      gen_gc_partial$gc_move_list gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2)
      ==>
      t2.ok
Proof
  Induct \\ fs [gen_gc_partialTheory.gc_move_list_def]
  \\ rw [] \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ drule gc_move_heap_length
  \\ drule gc_move_list_heap_length
  \\ `heap_length((s with <|h2 := h2; r4 := r4|>).heap) = heap_length state'.heap` by metis_tac[gc_move_heap_length]
  \\ `heap_length state'.heap = heap_length state''.heap` by metis_tac[gc_move_list_heap_length]
  \\ rpt DISCH_TAC
  \\ fs[]
  \\ imp_res_tac gc_partial_move_list_ok_before
  \\ first_x_assum match_mp_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ qpat_x_assum `_.ok` kall_tac
  \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ metis_tac [gc_partial_move_ok_irr]
QED

Theorem gc_partial_move_list_ok_irr':
   !x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial$gc_move_list gen_conf s x = (y1,t1) /\
      gen_gc_partial$gc_move_list gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2) ==>
      y1 = y2 /\ ?x1 x2. t2 = t1 with <| h2 := x1 ; r4 := x2 |>
Proof
  Induct \\ fs [gen_gc_partialTheory.gc_move_list_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ drule gc_partial_move_ok_irr \\ disch_then drule
  \\ DISCH_TAC \\ fs[] \\ fs[]
  \\ first_x_assum drule \\ disch_then drule \\ fs[]
QED

Theorem gc_partial_move_ref_list_ok_irr:
   !x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial$gc_move_ref_list gen_conf s x = (y1,t1) /\ t1.ok /\
      gen_gc_partial$gc_move_ref_list gen_conf (s with <| h2 := h2 ; r4 := r4 |>) x = (y2,t2)
      ==>
      t2.ok
Proof
  Induct \\ Cases \\ fs [gen_gc_partialTheory.gc_move_ref_list_def]
  \\ rw [] \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ drule gc_move_list_heap_length
  \\ drule gc_move_ref_list_heap_length
  \\ `heap_length((s with <|h2 := h2; r4 := r4|>).heap) = heap_length state'.heap` by metis_tac[gc_move_list_heap_length]
  \\ `heap_length state'.heap = heap_length state''.heap` by metis_tac[gc_move_ref_list_heap_length]
  \\ rpt DISCH_TAC
  \\ fs[]
  \\ imp_res_tac gc_partial_move_ref_list_ok_before
  \\ first_x_assum match_mp_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ qpat_x_assum `_.ok` kall_tac
  \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ metis_tac [gc_partial_move_list_ok_irr']
QED

Theorem gc_partial_move_with_NIL:
   !x s y t.
      gen_gc_partial$gc_move gen_conf s x = (y,t) /\ t.ok ==>
      (let (y,s1) = gc_move gen_conf (s with <| h2 := []; r4 := [] |>) x in
        (y,s1 with <| h2 := s.h2 ++ s1.h2; r4 := s1.r4 ++ s.r4 |>)) = (y,t)
Proof
  Cases \\ fs [gen_gc_partialTheory.gc_move_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
QED

Theorem gc_partial_move_with_NIL_LEMMA:
   !x s y t h2 r4 y1 t1.
      gen_gc_partial$gc_move gen_conf s x = (y1,t1) /\ t1.ok ==>
      ?x1 x2.
        t1.h2 = s.h2 ++ x1 /\
        t1.r4 = x2 ++ s.r4 /\
        gen_gc_partial$gc_move gen_conf (s with <| h2 := []; r4 := [] |>) x =
          (y1,t1 with <| h2 := x1; r4 := x2 |>)
Proof
  Cases \\ fs [gen_gc_partialTheory.gc_move_def] \\ rw []
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ CASE_TAC
  \\ fs [gc_sharedTheory.gc_state_component_equality]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
QED

Theorem gc_partial_move_list_with_NIL_LEMMA = Q.prove(`
  !x s y t h2 r4 y1 t1.
      gen_gc_partial$gc_move_list gen_conf s x = (y1,t1) /\ t1.ok ==>
      ?x1 x2.
        t1.h2 = s.h2 ++ x1 /\
        t1.r4 = x2 ++ s.r4 /\
        gen_gc_partial$gc_move_list gen_conf (s with <| h2 := []; r4 := [] |>) x =
          (y1,t1 with <| h2 := x1; r4 := x2 |>)`,
  Induct \\ fs [gen_gc_partialTheory.gc_move_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rename1 `gc_move gen_conf s h = (x3,state3)`
  \\ rename1 `_ = (x4,state4)`
  \\ `state3.ok` by imp_res_tac gc_partial_move_list_ok_before
  \\ drule (SIMP_RULE std_ss [] gc_partial_move_with_NIL_LEMMA) \\ fs []
  \\ strip_tac \\ fs [] \\ rveq
  \\ first_assum drule \\ asm_rewrite_tac []
  \\ `state''.ok` by imp_res_tac gc_partial_move_list_ok_irr
  \\ qpat_x_assum `gc_move_list gen_conf state3 x = _` kall_tac
  \\ first_x_assum drule \\ asm_rewrite_tac []
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]) |> SIMP_RULE std_ss [];

Theorem gc_partial_move_list_with_NIL:
   !x s y t.
      gen_gc_partial$gc_move_list gen_conf s x = (y,t) /\ t.ok ==>
      (let (y,s1) = gen_gc_partial$gc_move_list gen_conf (s with <| h2 := []; r4 := [] |>) x in
       (y,s1 with <| h2 := s.h2 ++ s1.h2; r4 := s1.r4 ++ s.r4 |>)) = (y,t)
Proof
  rw [] \\ drule gc_partial_move_list_with_NIL_LEMMA \\ fs []
  \\ strip_tac \\ fs [] \\ fs [gc_sharedTheory.gc_state_component_equality]
QED

Theorem gc_partial_move_ref_list_with_NIL_LEMMA = Q.prove(`
  !x s y t h2 r4 y1 t1.
      gen_gc_partial$gc_move_ref_list gen_conf s x = (y1,t1) /\ t1.ok ==>
      ?x1 x2.
        t1.h2 = s.h2 ++ x1 /\
        t1.r4 = x2 ++ s.r4 /\
        gen_gc_partial$gc_move_ref_list gen_conf (s with <| h2 := []; r4 := [] |>) x =
          (y1,t1 with <| h2 := x1; r4 := x2 |>)`,
  Induct THEN1 fs [gen_gc_partialTheory.gc_move_ref_list_def]
  \\ Cases
  \\ fs [gen_gc_partialTheory.gc_move_ref_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rename1 `gc_move_list gen_conf s h = (x3,state3)`
  \\ rename1 `_ = (x4,state4)`
  \\ `state3.ok` by imp_res_tac gc_partial_move_ref_list_ok_before
  \\ drule (SIMP_RULE std_ss [] gc_partial_move_list_with_NIL_LEMMA) \\ fs []
  \\ strip_tac \\ fs [] \\ rveq
  \\ first_assum drule \\ asm_rewrite_tac []
  \\ `state''.ok` by imp_res_tac gc_partial_move_ref_list_ok_irr
  \\ qpat_x_assum `gc_move_ref_list gen_conf state3 x = _` kall_tac
  \\ first_x_assum drule \\ asm_rewrite_tac []
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [gc_sharedTheory.gc_state_component_equality]) |> SIMP_RULE std_ss [];

Theorem gc_partial_move_ref_list_with_NIL:
   !x s y t.
      gen_gc_partial$gc_move_ref_list gen_conf s x = (y,t) /\ t.ok ==>
      (let (y,s1) = gen_gc_partial$gc_move_ref_list gen_conf (s with <| h2 := []; r4 := [] |>) x in
       (y,s1 with <| h2 := s.h2 ++ s1.h2; r4 := s1.r4 ++ s.r4 |>)) = (y,t)
Proof
  rw [] \\ drule gc_partial_move_ref_list_with_NIL_LEMMA \\ fs []
  \\ strip_tac \\ fs [] \\ fs [gc_sharedTheory.gc_state_component_equality]
QED

Theorem word_gen_gc_partial_move_roots_thm:
   !x xs x1 w s1 s pa1 pa m1 m i1 frame dm curr c1 old current refs.
    (gen_gc_partial$gc_move_list gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    gen_conf.limit = heap_length s.heap /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length s.heap /\
    (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s.heap = SOME(old,current,refs)) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    heap_length s.heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    (word_heap (curr + bytes_in_word * n2w(heap_length old)) current conf * word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_partial_move_roots conf (MAP (word_addr conf) x,n2w s.a,pa,
                                         curr:'a word,m,dm,
                                         bytes_in_word * n2w gen_conf.gen_start,
                                         bytes_in_word * n2w gen_conf.refs_start) =
      (w:'a word_loc list,i1,pa1,m1,c1)) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w(heap_length old)) current1 conf *
       word_heap pa s1.h2 conf *
       word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = MAP (word_addr conf) x1) /\
      heap_length s1.heap = heap_length s.heap /\
      (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(old,current1,refs)) /\
      c1 /\ (i1 = n2w s1.a) /\ s1.n = LENGTH xs1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      pa1 = pa + bytes_in_word * n2w (heap_length s1.h2)
Proof
  Induct
  THEN1
   (fs [gen_gc_partialTheory.gc_move_list_def,Once word_gen_gc_partial_move_roots_def] \\ rw []
    \\ fs [word_heap_def,SEP_CLAUSES] \\ asm_exists_tac \\ fs [])
  \\ fs [gen_gc_partialTheory.gc_move_list_def]
  \\ once_rewrite_tac [word_gen_gc_partial_move_roots_def]
  \\ rpt strip_tac \\ fs []
  \\ rw [] \\ ntac 4 (pairarg_tac \\ fs []) \\ rveq
  \\ fs [ADD1,GSYM word_add_n2w,word_list_def]
  \\ ntac 4 (pop_assum mp_tac) \\ fs []
  \\ rpt strip_tac
  \\ drule (GEN_ALL word_gen_gc_partial_move_thm) \\ fs []
  \\ drule gc_move_heap_length \\ DISCH_TAC \\ fs[]
  \\ drule gc_move_list_heap_length \\ DISCH_TAC \\ fs[]
  \\ `state'.ok` by imp_res_tac gc_partial_move_list_ok_before
  \\ fs [GSYM STAR_ASSOC]
  \\ rpt (disch_then drule)
  \\ fs [word_add_n2w]
  \\ strip_tac \\ rveq \\ fs []
  \\ drule gc_partial_move_list_with_NIL
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ rveq \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ qpat_x_assum `word_gen_gc_partial_move_roots conf _ = _` mp_tac
  \\ SEP_W_TAC
  \\ rpt strip_tac
  \\ SEP_F_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ rename1 `s2.n = LENGTH xs2`
  \\ rfs []
  \\ qexists_tac `xs2` \\ fs []
  \\ fs [word_heap_APPEND]
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ qpat_x_assum `LENGTH xs = s.n` (assume_tac o GSYM)
  \\ fs[]
QED

Theorem word_gen_gc_partial_move_list_thm:
   !x xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs.
    (gen_gc_partial$gc_move_list gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    gen_conf.limit = heap_length s.heap /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length s.heap /\
    (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s.heap = SOME(old,current,refs)) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    heap_length s.heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    (word_heap (curr + bytes_in_word * n2w(heap_length old)) current conf * word_list pa xs *
     word_list k (MAP (word_addr conf) x) * frame) (fun2set (m,dm)) /\
    (word_gen_gc_partial_move_list conf (k,n2w (LENGTH x),n2w s.a,pa,
                                         curr:'a word,m,dm,
                                         bytes_in_word * n2w gen_conf.gen_start,
                                         bytes_in_word * n2w gen_conf.refs_start) =
      (k1,i1,pa1,m1,c1)) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) /\ LENGTH x < dimword (:'a) ==>
    ?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w(heap_length old)) current1 conf *
       word_heap pa s1.h2 conf *
       word_list pa1 xs1 *
       word_list k (MAP (word_addr conf) x1) *
       frame) (fun2set (m1,dm)) /\
      heap_length s1.heap = heap_length s.heap /\
      (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(old,current1,refs)) /\
      c1 /\ (i1 = n2w s1.a) /\ s1.n = LENGTH xs1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
      k1 = k + n2w (LENGTH x) * bytes_in_word /\
      pa1 = pa + bytes_in_word * n2w (heap_length s1.h2)
Proof
  Induct
  THEN1
   (fs [gen_gc_partialTheory.gc_move_list_def,Once word_gen_gc_partial_move_list_def] \\ rw []
    \\ fs [word_heap_def,SEP_CLAUSES] \\ asm_exists_tac \\ fs [])
  \\ fs [gen_gc_partialTheory.gc_move_list_def]
  \\ once_rewrite_tac [word_gen_gc_partial_move_list_def]
  \\ rpt strip_tac \\ fs []
  \\ rw [] \\ ntac 4 (pairarg_tac \\ fs []) \\ rveq
  \\ fs [ADD1,GSYM word_add_n2w,word_list_def]
  \\ ntac 4 (pop_assum mp_tac) \\ SEP_R_TAC \\ fs []
  \\ rpt strip_tac
  \\ drule (GEN_ALL word_gen_gc_partial_move_thm) \\ fs []
  \\ drule gc_move_heap_length \\ DISCH_TAC \\ fs[]
  \\ drule gc_move_list_heap_length \\ DISCH_TAC \\ fs[]
  \\ `state'.ok` by imp_res_tac gc_partial_move_list_ok_before
  \\ fs [GSYM STAR_ASSOC]
  \\ rpt (disch_then drule)
  \\ fs [word_add_n2w]
  \\ strip_tac \\ rveq \\ fs []
  \\ drule gc_partial_move_list_with_NIL
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ rveq \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ qpat_x_assum `word_gen_gc_partial_move_list conf _ = _` mp_tac
  \\ SEP_W_TAC
  \\ rpt strip_tac
  \\ SEP_F_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ rename1 `s2.n = LENGTH xs2`
  \\ rfs []
  \\ qexists_tac `xs2` \\ fs []
  \\ fs [word_heap_APPEND]
  \\ fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ qpat_x_assum `LENGTH xs = s.n` (assume_tac o GSYM)
  \\ fs[]
QED

Theorem gc_partial_move_heap_lengths:
   gen_gc_partial$gc_move gen_conf s x = (x1,s1) /\ s1.ok ==>
    s.n + heap_length s.h2 = s1.n + heap_length s1.h2
Proof
  Cases_on `x` >> rw[gc_move_def]
  >> fs[] >> every_case_tac
  >> fs[]
  >- (qpat_x_assum `_ = s1` (assume_tac o GSYM)
      >> fs[])
  >- (qpat_x_assum `_ = s1` (assume_tac o GSYM)
      >> fs[])
  >> pairarg_tac >> fs[]
  >> qpat_x_assum `_ = s1` (assume_tac o GSYM)
  >> fs[heap_length_APPEND]
  >> fs[heap_length_def,el_length_def]
  >> `(s.ok ∧ n < SUM (MAP el_length s.heap)) ∧ n' + 1 ≤ s.n ∧
       ¬gen_conf.isRef b`
         by(match_mp_tac (GEN_ALL gc_forward_ptr_ok)
            >> qexists_tac `a` >> qexists_tac `s.heap` >> qexists_tac `n`
            >> qexists_tac `s.a` >> qexists_tac `heap` >> fs[])
  >> fs[]
QED

Theorem gc_partial_move_list_heap_lengths:
   !x gen_conf s x1 s1. gen_gc_partial$gc_move_list gen_conf s x = (x1,s1) /\ s1.ok ==>
     s.n + heap_length s.h2 = s1.n + heap_length s1.h2
Proof
  Induct_on `x` >> rw[gen_gc_partialTheory.gc_move_list_def]
  >> ntac 2 (pairarg_tac >> gvs[])
  >> drule_all gc_partial_move_list_ok_before >> rw []
  >> drule_all gc_partial_move_heap_lengths >> rw []
  >> res_tac
QED

Definition partial_len_inv_def:
  partial_len_inv s <=>
    heap_length s.heap =
    heap_length (s.h1 ++ s.h2) + s.n + heap_length (s.r4 ++ s.r3 ++ s.r2 ++ s.r1 ++ s.old)
End

Theorem word_gen_gc_partial_move_data_thm:
   !k s m dm curr xs s1 pa1 m1 i1 frame c1 old current refs.
    (gen_gc_partial$gc_move_data gen_conf s = s1) /\ s1.ok /\
    gen_conf.limit = heap_length s.heap /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length s.heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length s.heap /\
    (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s.heap = SOME(old,current,refs)) /\
    conf.len_size + 2 < dimindex (:α) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    (word_gen_gc_partial_move_data conf k
       ((* h2a *) p + bytes_in_word * n2w (heap_length s.h1),
        n2w s.a,
        (* pa *) p + bytes_in_word * n2w (heap_length (s.h1 ++ s.h2)),
        curr:'a word,m,dm,
        bytes_in_word * n2w gen_conf.gen_start,
        bytes_in_word * n2w gen_conf.refs_start) =
      (i1,pa1,m1,c1)) /\
    heap_length s.h2 + s.n <= k /\ partial_len_inv s /\
    (word_heap (curr + bytes_in_word * n2w(heap_length old)) current conf *
     word_heap p (s.h1 ++ s.h2) conf *
     word_list (p + bytes_in_word * n2w(heap_length(s.h1 ++ s.h2))) xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref gen_conf.isRef) (s.r4 ++ s.r3 ++ s.r2 ++ s.r1) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) ==>
    ?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w(heap_length old)) current1 conf *
       word_heap p (s1.h1 ++ s1.h2) conf *
       word_list (p + bytes_in_word * n2w(heap_length(s1.h1 ++ s1.h2))) xs1 *
       frame) (fun2set (m1,dm)) /\ s1.h2 = [] /\
      heap_length s1.heap = heap_length s.heap /\
      (heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(old,current1,refs)) /\
      c1 /\ (i1 = n2w s1.a) /\
      s1.n = LENGTH xs1 /\ partial_len_inv s1 /\
      heap_length (s1.h1 ++ s1.h2 ++ s1.r4) + s1.n =
      heap_length (s.h1 ++ s.h2 ++ s.r4) + s.n /\
      pa1 = p + bytes_in_word * n2w (heap_length (s1.h1 ++ s1.h2)) /\
      EVERY (is_Ref gen_conf.isRef) (s1.r4 ++ s1.r3 ++ s1.r2 ++ s1.r1)
Proof
  completeInduct_on `k` \\ rpt strip_tac
  \\ fs [PULL_FORALL,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ qpat_x_assum `gc_move_data gen_conf s = s1` mp_tac
  \\ once_rewrite_tac [gen_gc_partialTheory.gc_move_data_def]
  \\ CASE_TAC THEN1
   (rw [] \\ fs []
    \\ qpat_x_assum `word_gen_gc_partial_move_data conf k _ = _` mp_tac
    \\ once_rewrite_tac [word_gen_gc_partial_move_data_def]
    \\ fs [] \\ strip_tac \\ rveq
    \\ qexists_tac `xs`
    \\ fs []
    \\ fs [partial_len_inv_def])
  \\ IF_CASES_TAC THEN1 (rw[] \\ fs [])
  \\ CASE_TAC
  THEN1 (strip_tac \\ rveq \\ fs [])
  THEN1 (strip_tac \\ rveq \\ fs [])
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rename1 `_ = (_,s3)`
  \\ strip_tac
  \\ `s3.ok` by (drule gc_partial_move_data_ok_before >> fs[])
  \\ qmatch_asmsub_abbrev_tac `gc_move_data gen_conf s4`
  \\ rveq
  \\ `s3.h1 = s.h1 /\ s3.r1 = s.r1 /\ s3.r2 = s.r2 /\ s3.r3 = s.r3 /\ s3.r4 = s.r4` by
    (drule gc_move_list_IMP \\ fs [])
  \\ `partial_len_inv s3`
    by(fs [partial_len_inv_def,heap_length_def,SUM_APPEND,el_length_def]
       \\ drule gc_move_list_heap_length \\ disch_then (assume_tac o GSYM)
       \\ fs[heap_length_def,SUM_APPEND,el_length_def]
       \\ `s3.n + SUM(MAP el_length s3.h2) + SUM(MAP el_length s3.old) = n + SUM(MAP el_length t) + SUM(MAP el_length s.old) + s.n + 1` suffices_by fs[]
       \\ drule gc_partial_move_list_heap_lengths
       \\ DISCH_TAC \\ first_x_assum drule \\ disch_then (assume_tac o GSYM)
       \\ fs[heap_length_def,SUM_APPEND,el_length_def]
       \\ metis_tac [gc_move_list_IMP])
  \\ `partial_len_inv s4` by
    (unabbrev_all_tac
     \\ fs [partial_len_inv_def,heap_length_def,SUM_APPEND,el_length_def]
     \\ drule gc_partial_move_list_with_NIL \\ fs []
     \\ pairarg_tac \\ fs []
     \\ strip_tac \\ rveq \\ fs [SUM_APPEND,el_length_def] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM STAR_ASSOC]
  \\ drule word_heap_IMP_limit
  \\ full_simp_tac std_ss [STAR_ASSOC] \\ strip_tac
  \\ drule gc_partial_move_list_with_NIL \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ PairCases_on `b`
  \\ rfs [is_Ref_def] \\ rveq
  \\ qpat_x_assum `word_gen_gc_partial_move_data conf k _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_partial_move_data_def]
  \\ IF_CASES_TAC THEN1
   (fs [heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ qsuff_tac `F` \\ fs []
    \\ fs [heap_length_def,el_length_def]
    \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
    \\ pop_assum mp_tac \\ fs [bytes_in_word_def,word_mul_n2w]
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac `nn MOD _`
    \\ qsuff_tac `nn < dimword (:α)`
    \\ fs [] \\ unabbrev_all_tac \\ rfs [good_dimindex_def]
    \\ rfs [dimword_def] \\ fs[])
  \\ simp [] \\ pop_assum kall_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM heap_length_def]
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def]
  \\ pairarg_tac \\ fs []
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ rfs [] \\ rveq
  \\ ntac 4 (pop_assum mp_tac)
  \\ SEP_R_TAC \\ fs [theWord_def,isWord_def]
  \\ Cases_on `word_bit 2 h` \\ fs []
  THEN1
   (rpt strip_tac \\ rveq
    \\ `l = []` by (imp_res_tac word_payload_T_IMP \\ rfs [] \\ NO_TAC)
    \\ rveq \\ fs [gen_gc_partialTheory.gc_move_list_def] \\ rveq \\ fs []
    \\ qpat_x_assum `word_gen_gc_partial_move_data conf (k − 1) _ = _` kall_tac
    \\ qpat_x_assum `word_gen_gc_partial_move_list conf _ = _` kall_tac
    \\ rfs []
    \\ qpat_x_assum `!m:num. _`
         (qspecl_then [`k-1`,`s4`,`m`,`dm`,`curr`,`xs`] mp_tac) \\ fs []
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
           heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ qmatch_asmsub_abbrev_tac `word_gen_gc_partial_move_data conf _ input1 = _`
    \\ qmatch_goalsub_abbrev_tac `word_gen_gc_partial_move_data conf _ input2 = _`
    \\ `input1 = input2` by
     (unabbrev_all_tac \\ simp_tac std_ss [] \\ rpt strip_tac
      \\ fs [SUM_APPEND,el_length_def]
      \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
      \\ imp_res_tac word_payload_T_IMP \\ rfs [] \\ NO_TAC)
    \\ fs []
    \\ disch_then (qspecl_then [`frame`,`old`,`current`,`refs`] mp_tac)
    \\ impl_tac THEN1
     (qunabbrev_tac `s4` \\ fs [is_Ref_def]
      \\ qpat_x_assum `_ (fun2set (_,dm))` mp_tac
      \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
      \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
      \\ match_mp_tac (METIS_PROVE [] ``f = g ==> f x ==> g x``)
      \\ fs [AC STAR_ASSOC STAR_COMM,SEP_CLAUSES])
    \\ strip_tac
    \\ qexists_tac `xs1` \\ fs [] \\ rpt strip_tac
    \\ qabbrev_tac `s5 = gc_move_data gen_conf s4`
    \\ qunabbrev_tac `s4`
    \\ fs [el_length_def,SUM_APPEND]
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM)
    \\ pop_assum mp_tac \\ simp_tac std_ss []
    \\ CCONTR_TAC \\ fs [] \\ rfs [])
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_partial_move_list conf (newp,_)`
  \\ rpt strip_tac \\ rveq
  \\ drule (GEN_ALL word_gen_gc_partial_move_list_thm) \\ fs []
  \\ drule word_payload_T_IMP
  \\ fs [] \\ strip_tac \\ rveq \\ fs []
  \\ fs [is_Ref_def]
  \\ strip_tac
  \\ SEP_F_TAC \\ fs [GSYM word_add_n2w]
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
            heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
            WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
  \\ impl_tac THEN1
   (rfs [good_dimindex_def] \\ rfs [dimword_def]
    \\ fs [len_inv_def,heap_length_def,el_length_def,SUM_APPEND] \\ rfs [])
  \\ strip_tac \\ rveq
  \\ qpat_x_assum `s.n = _` (assume_tac o GSYM)
  \\ fs [el_length_def,heap_length_def]
  \\ fs [GSYM heap_length_def] \\ rfs []
  \\ qmatch_asmsub_abbrev_tac `word_gen_gc_partial_move_data conf _ input1 = _`
  \\ qpat_x_assum `!m:num. _`
       (qspecl_then [`k-1`,`s4`,`m''`,`dm`,`curr`,`xs1`] mp_tac) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
  \\ qmatch_goalsub_abbrev_tac `word_gen_gc_partial_move_data conf _ input2 = _`
  \\ `input1 = input2` by
   (unabbrev_all_tac \\ simp_tac std_ss [] \\ rpt strip_tac
    \\ fs [SUM_APPEND,el_length_def]
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ NO_TAC)
  \\ fs []
  \\ drule (GEN_ALL word_payload_swap)
  \\ drule gen_gc_partialTheory.gc_move_list_length
  \\ strip_tac \\ disch_then drule \\ strip_tac
  \\ disch_then (qspecl_then [`frame`,`old`,`current1`,`refs`] mp_tac)
  \\ impl_tac THEN1
   (qunabbrev_tac `s4` \\ fs [is_Ref_def]
    \\ qpat_x_assum `_ (fun2set (_,dm))` mp_tac
    \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
    \\ qunabbrev_tac `newp`
    \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
          heap_length_APPEND,word_payload_def,GSYM word_add_n2w,SUM_APPEND,
          WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
    \\ fs [AC STAR_ASSOC STAR_COMM,SEP_CLAUSES])
  \\ strip_tac
  \\ qexists_tac `xs1'` \\ fs []
  \\ qabbrev_tac `s5 = gc_move_data gen_conf s4`
  \\ qunabbrev_tac `s4` \\ fs [is_Ref_def]
  \\ fs [el_length_def,SUM_APPEND]
  \\ qpat_x_assum `_ = s.n` (assume_tac o GSYM) \\ fs []
  \\ fs [word_heap_parts_def,word_heap_APPEND,word_heap_def,word_el_def,
         heap_length_APPEND,word_payload_def,GSYM word_add_n2w,
         WORD_LEFT_ADD_DISTRIB,word_list_def,el_length_def,heap_length_def]
QED


Theorem word_gen_gc_partial_move_ref_list_thm:
   !x ck xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs.
    (gen_gc_partial$gc_move_ref_list gen_conf s x = (x1,s1)) /\ s1.ok /\ s.h2 = [] /\ s.r4 = [] /\
    heap_length x <= ck /\
    gen_conf.limit = heap_length s.heap /\
    heap_length s.heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length s.heap /\
    heap_segment (gen_conf.gen_start,gen_conf.refs_start) s.heap = SOME(old,current,refs) /\
    heap_length x <= heap_length s.heap /\
    EVERY isRef x /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    heap_length s.heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    (word_heap (curr+bytes_in_word * n2w(heap_length old)) current conf * word_list pa xs *
     word_heap k x conf * frame) (fun2set (m,dm)) /\
    (word_gen_gc_partial_move_ref_list ck conf (k,n2w s.a,pa,
                                         curr:'a word,m,dm,T,
                                         bytes_in_word * n2w gen_conf.gen_start,
                                         bytes_in_word * n2w gen_conf.refs_start,
                                         k + bytes_in_word * n2w(heap_length x)) =
      (i1,pa1,m1,c1)) /\
    LENGTH xs = s.n /\ good_dimindex (:'a) /\ LENGTH x < dimword (:'a) ==>
    ?xs1 current1.
      (word_heap (curr+bytes_in_word * n2w(heap_length old)) current1 conf *
       word_heap pa s1.h2 conf *
       word_list pa1 xs1 *
       word_heap k x1 conf *
       frame) (fun2set (m1,dm)) /\
      heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(old,current1,refs) /\
      heap_length s1.heap = heap_length s.heap /\
      c1 /\ (i1 = n2w s1.a) /\ s1.n = LENGTH xs1 /\
      EVERY isRef x1 /\
      s.n = heap_length s1.h2 + s1.n + heap_length s1.r4 /\
  pa1 = pa + bytes_in_word * n2w (heap_length s1.h2)
Proof
  Induct
  THEN1
   (fs [gen_gc_partialTheory.gc_move_ref_list_def,Once word_gen_gc_partial_move_ref_list_def] \\ rw []
      \\ fs [word_heap_def,SEP_CLAUSES,refs_to_addresses_def] \\ asm_exists_tac \\ fs [])
  \\ Cases
  THEN1 fs [gen_gc_partialTheory.gc_move_ref_list_def]
  THEN1 fs [gen_gc_partialTheory.gc_move_ref_list_def]
  \\ fs [gen_gc_partialTheory.gc_move_ref_list_def]
  \\ rpt strip_tac \\ fs []
  \\ qpat_x_assum `word_gen_gc_partial_move_ref_list _ _ _ = _` mp_tac
  \\ simp[Once word_gen_gc_partial_move_ref_list_def]
  \\ rw [] \\ fs[heap_length_def,el_length_def]
  \\ `(n + (SUM (MAP el_length x) + 1)) * (dimindex (:α) DIV 8) < dimword (:α)`
       by (`SUM (MAP el_length s.heap) * (dimindex (:α) DIV 8) < dimword (:α)`
             suffices_by fs[good_dimindex_def,dimword_def]
           >> fs[])
  \\ `k <> k + bytes_in_word * n2w (n + (SUM (MAP el_length x) + 1))`
      by (CCONTR_TAC >> fs[bytes_in_word_def,addressTheory.WORD_EQ_ADD_CANCEL]
          >> fs[bytes_in_word_def,word_add_n2w,word_mul_n2w] >> fs[good_dimindex_def]
          >> rw[] >> rfs[])
  \\ fs[word_heap_def] \\ rfs[]
  \\ PairCases_on `b`
  \\ fs[word_el_def]
  \\ pairarg_tac \\ fs[isRef_def] \\ rveq \\ fs[word_payload_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ rveq \\ fs[word_list_def]
  \\ `m k = Word(make_header conf 2w (LENGTH l))` by SEP_R_TAC
  \\ fs[theWord_def,el_length_def]
  \\ ntac 2 (pairarg_tac \\ fs[])
  \\ drule(GEN_ALL word_gen_gc_partial_move_list_thm)
  \\ `state'.ok` by (imp_res_tac gc_partial_move_ref_list_ok_before \\ fs [])
  \\ fs[heap_length_def]
  \\ disch_then drule
  \\ strip_tac \\ SEP_F_TAC \\ rfs[]
  \\ impl_tac THEN1 (fs[good_dimindex_def,dimword_def] >> rfs[])
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ drule gc_partial_move_ref_list_with_NIL \\ disch_then drule
  \\ fs[] \\ pairarg_tac \\ fs[] \\ strip_tac \\ rveq \\ fs[]
  \\ first_x_assum drule \\ fs[]
  \\ `s1'.ok` by (rveq \\ fs[])
  \\ fs[]
  \\ strip_tac \\ SEP_F_TAC
  \\ fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ `k ∈ dm` by SEP_R_TAC
  \\ fs[isWord_def]
  \\ disch_then (qspec_then `ck-1` mp_tac)
  \\ fs[]
  \\ strip_tac \\ rveq \\ fs[]
  \\ drule gen_gc_partialTheory.gc_move_list_length \\ strip_tac
  \\ fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,SUM_APPEND]
  \\ qexists_tac `xs1'`
  \\ fs[word_heap_APPEND,word_heap_def,word_el_def,el_length_def]
  \\ pairarg_tac \\ fs[] \\ fs[word_list_def]
  \\ fs[word_payload_def] \\ rveq \\ fs[]
  \\ fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,heap_length_def]
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ fs[SEP_CLAUSES]
  \\ fs[isRef_def]
QED

val gc_move_ref_list_IMP = prove (
  ``!conf state refs state1 refs1.
    (gc_move_ref_list conf state refs = (refs1,state1)) ==>
    (state1.old = state.old) /\
    (state1.h1 = state.h1) /\
    (state1.r1 = state.r1) /\
    (state1.r2 = state.r2) /\
    (state1.r3 = state.r3) /\
    (state1.r4 = state.r4) /\
    (heap_length refs = heap_length refs1) /\
    (!ptr.
       isSomeDataElement (heap_lookup ptr refs) ==>
       isSomeDataElement (heap_lookup ptr refs1))
  ``,
  recInduct (fetch "gen_gc_partial" "gc_move_ref_list_ind")
  \\ once_rewrite_tac [gc_move_ref_list_def] \\ fs []
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ rveq
  \\ fs []
  \\ fs [heap_length_def,el_length_def]
  \\ simp [heap_lookup_def]
  \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  >- simp [isSomeDataElement_def]
  \\ IF_CASES_TAC \\ fs [el_length_def]);

Theorem heap_length_LENGTH:
  LENGTH x <= heap_length x
Proof
  Induct_on `x` >- fs[LENGTH]
  >> Cases >> fs[LENGTH,heap_length_def,el_length_def]
QED

Theorem partial_gc_move_ref_list_isRef:
    !refs s refs' state'.
   gen_gc_partial$gc_move_ref_list gen_conf s refs = (refs',state')
   ==> EVERY (is_Ref gen_conf.isRef) refs' = EVERY (is_Ref gen_conf.isRef) refs
Proof
  Induct >- fs[gc_move_ref_list_def]
  >> Cases >> rpt strip_tac
  >> fs[gc_move_ref_list_def]
  >> rveq >> fs[is_Ref_def]
  >> ntac 2 (pairarg_tac >> fs[])
  >> rveq >> fs[is_Ref_def]
  >> metis_tac[]
QED

Theorem EVERY_is_Ref_isRef:
   (∀t r. f (t,r) ⇔ t = RefTag) ==> EVERY (is_Ref f) refs = EVERY isRef refs
Proof
  Induct_on `refs` >- fs[] >> Cases >> rpt strip_tac >> fs[isRef_def,is_Ref_def]
  >> Cases_on `b` >> fs[isRef_def]
QED

Definition ends_with_refs_def:
  ends_with_refs rs heap =
    ?h1 h2. heap_split rs heap = SOME (h1,h2) /\ EVERY isRef h2
End

Theorem word_gen_gc_partial_thm:
   !m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new.
    (gen_gc_partial$partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ s1.ok /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    gen_conf.limit = heap_length heap /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length heap /\
    ends_with_refs gen_conf.refs_start heap /\
    heap_length heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    conf.len_size + 2 < dimindex (:α) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    (word_gen_gc_partial conf (MAP (word_addr conf) roots,curr,new,
                               bytes_in_word * n2w (heap_length heap),m,dm,
                               bytes_in_word * n2w gen_conf.gen_start,
                               bytes_in_word * n2w gen_conf.refs_start
                              ) = (roots1',i1,pa1:'a word,m1,c1)) /\
    (word_heap curr heap conf *
     word_list_exists new (gen_conf.refs_start - gen_conf.gen_start) *
     frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
    ?xs1 current1 refs1.
     (word_heap curr (s1.old ++ current1 ++ s1.r1) conf *
       word_heap new s1.h1 conf *
       word_list (new + bytes_in_word * n2w(heap_length(s1.h1))) xs1 *
       frame) (fun2set (m1,dm)) /\
      s1.h2 = [] /\ s1.r4 = [] /\ s1.r3 = [] /\ s1.r2 = [] /\
      roots1' = MAP (word_addr conf) roots1 /\
      heap_length s1.heap = heap_length heap /\
      heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(s1.old,current1,refs1) /\
      c1 /\ (i1 = n2w s1.a) /\ pa1 = new + bytes_in_word * n2w (heap_length s1.h1) /\
      s1.n = LENGTH xs1 /\ partial_len_inv s1 /\ heap_length s1.h1 <= heap_length current1 /\
      heap_length s1.h1 + LENGTH xs1 + gen_conf.gen_start = gen_conf.refs_start  /\
      EVERY (is_Ref gen_conf.isRef) s1.r1
Proof
  rpt gen_tac \\ once_rewrite_tac [gen_gc_partialTheory.partial_gc_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ fs []
  \\ every_case_tac THEN1 (fs[] \\ rveq \\ fs[])
  \\ ntac 2 (pairarg_tac \\ fs[])
  \\ drule heap_segment_IMP
  \\ drule gc_partial_move_data_ok_before \\ disch_then drule \\ strip_tac
  \\ fs[]
  \\ drule gc_partial_move_ref_list_ok_before \\ disch_then drule \\ strip_tac
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ drule (GEN_ALL word_gen_gc_partial_move_roots_thm)
  \\ fs[empty_state_def]
  \\ rpt(disch_then drule)
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ fs[word_heap_APPEND]
  \\ pop_assum(fn x => ntac 2(assume_tac x))
  \\ strip_tac \\ SEP_F_TAC \\ fs []
  \\ fs[word_gen_gc_partial_def]
  \\ ntac 3 (pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ `((bytes_in_word:'a word) * n2w gen_conf.gen_start) ⋙ shift (:α) =
      n2w gen_conf.gen_start`
      by  (fs[bytes_in_word_mul_eq_shift]
           >> MATCH_MP_TAC lsl_lsr
           >> fs[w2n_n2w]
           >> rw[shift_def]
           >> fs[dimword_def,good_dimindex_def])
  \\ fs[]
  \\ ntac 3 (qpat_x_assum `heap_length _ = _` (mp_tac o GSYM))
  \\ ntac 3 strip_tac
  \\ impl_tac THEN1 fs[heap_length_APPEND]
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ drule gc_partial_move_ref_list_with_NIL
  \\ disch_then drule
  \\ fs[] \\ pairarg_tac \\ fs[] \\ strip_tac
  \\ qpat_x_assum `y = refs'` (fn thm => fs[thm])
  \\ rveq \\ fs[]
  \\ drule (GEN_ALL word_gen_gc_partial_move_ref_list_thm)
  \\ fs[gc_state_component_equality]
  \\ `heap_length r' <= dimword (:'a)` by
     (fs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [] \\ NO_TAC)
  \\ rpt(disch_then drule)
  \\ rfs[]
  \\ `EVERY isRef r'` by
   (qpat_x_assum `ends_with_refs (heap_length (q ++ q')) (q ++ q' ++ r')` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qpat_abbrev_tac `hh = q ++ _`
    \\ fs [ends_with_refs_def,heap_split_APPEND_if,heap_split_0] \\ NO_TAC)
  \\ fs[]
  \\ rpt(disch_then drule)
  \\ strip_tac \\ SEP_F_TAC
  \\ SIMP_TAC std_ss [GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC, word_add_n2w,
                      GSYM heap_length_APPEND]
  \\ rpt(disch_then drule)
  \\ impl_tac THEN1
     (`LENGTH r' <= heap_length r'` by metis_tac [heap_length_LENGTH]
      >> `heap_length r' < dimword(:'a)` suffices_by fs[]
      >> fs[heap_length_APPEND,good_dimindex_def] >> rfs[] >> fs[])
  \\ rpt(disch_then drule)
  \\ strip_tac
  \\ `gc_move_data gen_conf(s1 with <|h2 := state'.h2 ++ s1.h2;
                                      r4 := s1.r4 ++ state'.r4;
                                      r2 := []; r1 := refs'|>) =
      gc_move_data gen_conf(s1 with <|h2 := state'.h2 ++ s1.h2;
                            r4 := s1.r4 ++ state'.r4;
                            r2 := []; r1 := refs'|>)` by fs[]
  \\ drule (gc_move_data_IMP) \\ strip_tac
  \\ drule (GEN_ALL word_gen_gc_partial_move_data_thm)
  \\ rpt(disch_then drule)
  \\ fs[]
  \\ rpt(disch_then drule)
  \\ `s1.h1 = []`
     by (drule gen_gc_partialTheory.gc_move_list_IMP >> drule gc_move_ref_list_IMP >> fs[])
  \\ `s1.r3 = []`
     by (drule gen_gc_partialTheory.gc_move_list_IMP >> drule gc_move_ref_list_IMP >> fs[])
  \\ fs[]
  \\ rpt(disch_then drule)
  \\ rveq \\ fs[]
  \\ fs[heap_length_APPEND]
  \\ fs[partial_len_inv_def,heap_length_APPEND]
  \\ drule gc_move_ref_list_heap_length' \\ strip_tac
  \\ fs[]
  \\ drule gc_move_list_IMP \\ strip_tac
  \\ drule gc_move_ref_list_IMP \\ strip_tac
  \\ fs[word_heap_parts_def]
  \\ fs[word_heap_APPEND]
  \\ rveq \\ fs[heap_length_APPEND]
  \\ strip_tac \\ SEP_F_TAC
  \\ impl_tac THEN1
     (fs[EVERY_is_Ref_isRef]
      \\ fs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
  \\ strip_tac
  \\ fs[] \\ rveq \\ fs[]
  \\ qpat_abbrev_tac `a1 = gc_move_data _ _`
  \\ drule heap_segment_IMP
  \\ disch_then (assume_tac o GSYM)
  \\ fs[heap_length_APPEND,word_heap_APPEND,word_heap_def,SEP_CLAUSES]
  \\ rfs[heap_length_APPEND,word_heap_APPEND]
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ qexists_tac `xs1''` \\ fs[]
  \\ drule partial_gc_move_ref_list_isRef
  \\ fs[EVERY_is_Ref_isRef]
QED

Theorem word_gen_gc_partial_full_thm:
   !m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new.
    (gen_gc_partial$partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ s1.ok /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    ends_with_refs gen_conf.refs_start heap /\
    gen_conf.limit = heap_length heap /\
    gen_conf.gen_start <= gen_conf.refs_start /\
    gen_conf.refs_start <= heap_length heap /\
    heap_length heap * (dimindex (:α) DIV 8) < dimword (:α) /\
    conf.len_size + 2 < dimindex (:α) /\
    (!t r. (gen_conf.isRef (t,r) <=> t = RefTag)) /\
    (word_gen_gc_partial_full conf (MAP (word_addr conf) roots,curr,new,
                               bytes_in_word * n2w (heap_length heap),m,dm,
                               bytes_in_word * n2w gen_conf.gen_start,
                               bytes_in_word * n2w gen_conf.refs_start
                              ) = (roots1',i1,pa1:'a word,m1,c1)) /\
    (word_heap curr heap conf *
     word_list_exists new (heap_length heap) *
     frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
    ?current1 refs1.
      (word_heap curr s1.old conf *
       word_heap (curr + bytes_in_word * n2w (heap_length s1.old)) s1.h1 conf *
       word_list_exists pa1 s1.n *
       word_heap (pa1 + bytes_in_word * n2w s1.n) s1.r1 conf *
       word_list_exists new (heap_length heap) *
       frame) (fun2set (m1,dm)) /\
      s1.h2 = [] /\ s1.r4 = [] /\ s1.r3 = [] /\ s1.r2 = [] /\
      roots1' = MAP (word_addr conf) roots1 /\
      heap_length s1.heap = heap_length heap /\
      heap_segment (gen_conf.gen_start,gen_conf.refs_start) s1.heap = SOME(s1.old,current1,refs1) /\
      c1 /\ (i1 = n2w s1.a) /\ pa1 = curr + bytes_in_word * n2w (heap_length(s1.old ++ s1.h1)) /\
      partial_len_inv s1 /\
      EVERY (is_Ref gen_conf.isRef) s1.r1
Proof
  rpt gen_tac \\ rw[word_gen_gc_partial_full_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs[]
  \\ drule word_gen_gc_partial_thm
  \\ rpt(disch_then drule) \\ fs[]
  \\ rpt(disch_then drule)
  \\ `?xsl. (heap_length heap =  (gen_conf.refs_start - gen_conf.gen_start) + xsl)`
     by (ONCE_REWRITE_TAC [ADD_COMM]
         \\ match_mp_tac (GSYM LESS_EQ_ADD_EXISTS) \\ fs[])
  \\ fs[word_list_exists_ADD]
  \\ strip_tac \\ SEP_F_TAC
  \\ strip_tac \\ fs[]
  \\ fs[word_heap_APPEND] \\ rveq \\ fs[]
  \\ qabbrev_tac `a1 = word_heap (curr + bytes_in_word * n2w (heap_length s1.old)) current1 conf`
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ unabbrev_all_tac
  \\ drule word_heap_eq_word_list \\ strip_tac
  \\ fs[]
  \\ drule LESS_EQ_IMP_APPEND \\ strip_tac \\ rveq \\ fs[]
  \\ fs[word_list_APPEND]
  \\ `(bytes_in_word * n2w (heap_length s1.h1)) ⋙ shift (:α) = (n2w(heap_length s1.h1):'a word)`
      by(REWRITE_TAC [GSYM w2n_11,w2n_lsr] \\ fs[bytes_in_word_def,word_mul_n2w]
         \\ `heap_length s1.h1 * (dimindex (:α) DIV 8) < dimword (:'a)`
             by (fs[good_dimindex_def,dimword_def] \\ rfs[] \\ fs[])
             \\ fs[] \\ fs[good_dimindex_def,dimword_def,shift_def,
                           ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] \\ fs [])
  \\ fs[]
  \\ qabbrev_tac `a1 = word_heap new s1.h1 conf`
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ unabbrev_all_tac
  \\ drule word_heap_eq_word_list_strong \\ strip_tac
  \\ fs[] \\ drule memcpy_thm
  \\ `heap_length s1.old = gen_conf.gen_start`
     by(drule heap_segment_IMP >> fs[])
  \\ fs[]
  \\ strip_tac \\ SEP_F_TAC
  \\ impl_tac THEN1
    (fs [] \\ fs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
  \\ strip_tac
  \\ fs[] \\ fs[heap_length_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ simp[Once word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ qpat_x_assum `_ (fun2set (_,_))` mp_tac
  \\ simp[Once word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ strip_tac
  \\ qexists_tac `xs++xs1++xs'`
  \\ fs[AC STAR_ASSOC STAR_COMM,word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ first_x_assum (qspec_then `curr + bytes_in_word * n2w gen_conf.gen_start` assume_tac)
  \\ SEP_F_TAC
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ qabbrev_tac `a1 = word_list (curr + bytes_in_word * n2w gen_conf.gen_start) xs`
  \\ fs[GSYM(AC STAR_ASSOC STAR_COMM)]
  \\ simp[Once word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ simp[PULL_EXISTS]
  \\ strip_tac
  \\ qexists_tac `zs`
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ rveq \\ fs[]
  \\ fs[AC STAR_ASSOC STAR_COMM]
  \\ `LENGTH zs = LENGTH xs1`
        by(drule heap_segment_IMP >> fs[heap_length_APPEND])
  \\ fs[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]
  \\ qpat_x_assum `_ = gen_conf.refs_start` (assume_tac o GSYM)
  \\ fs[AC STAR_ASSOC STAR_COMM,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem gen_starts_in_store_IMP_SOME_Word:
   gen_starts_in_store c gens x ==> ?w. x = SOME (Word w)
Proof
  Cases_on `x` \\ fs [gen_starts_in_store_def]
  \\ Cases_on `x'` \\ fs [gen_starts_in_store_def]
QED

Theorem glob_real_inv:
  glob_real_inv c other (SOME w)
                        (SOME (glob_real c other w)) ⇔ isWord w
Proof
  Cases_on ‘w’ \\ fs [isWord_def,glob_real_def]
  \\ fs [glob_real_inv_def]
QED

Theorem word_gc_fun_lemma_Simple = Q.prove(`
  abs_ml_inv c (v::MAP FST stack) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
    good_dimindex (:'a) /\
    heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
    LIST_REL (\v w. word_addr c v = w) hs (s ' Globals::MAP SND stack) /\
    full_gc (hs,heap,limit) = (roots2,heap2,heap_length heap2,T) /\
    c.gc_kind = Simple ==>
    let heap1 = heap2 ++ heap_expand (limit - heap_length heap2) in
      ?stack1 m1 s1 a1.
        word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
        heap_in_memory_store heap1 (heap_length heap2)
          (limit - heap_length heap2) 0 gens c s1 m1 dm limit /\
        LIST_REL (λv w. word_addr c v = (w:'a word_loc)) roots2
          (s1 ' Globals::MAP SND (ZIP (MAP FST stack,stack1))) /\
        LENGTH stack1 = LENGTH stack`,
  strip_tac
  \\ rewrite_tac [word_gc_fun_def] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[heap_in_memory_store_def,FLOOKUP_DEF,theWord_def,LET_THM]
  \\ pairarg_tac
  \\ full_simp_tac(srw_ss())[finite_mapTheory.FDOM_FUPDATE_LIST,FUPDATE_LIST,FAPPLY_FUPDATE_THM]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `s ' Globals::MAP SND stack = MAP (word_addr c) (v'::xs)` by
    (full_simp_tac(srw_ss())[LIST_REL_EQ_MAP] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac std_ss [] \\ drule (GEN_ALL word_full_gc_thm)
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule
  \\ disch_then (qspec_then `emp` mp_tac)
  \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
  \\ impl_tac
  THEN1 (imp_res_tac full_gc_IMP \\ fs [])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac full_gc_IMP_LENGTH
  \\ Cases_on `roots2` \\ full_simp_tac(srw_ss())[]
  \\ `LENGTH xs = LENGTH stack` by metis_tac [LENGTH_MAP]
  \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[listTheory.MAP_ZIP]
  \\ full_simp_tac(srw_ss())[LIST_REL_EQ_MAP]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac full_gc_IMP \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[heap_length_APPEND,heap_length_heap_expand]
  \\ `heap_length heap2 + (heap_length heap - heap_length heap2) =
      heap_length heap` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ fs [word_gc_fun_assum_def,isWord_def,glob_real_inv]
  \\ imp_res_tac gen_starts_in_store_IMP_SOME_Word
  \\ CCONTR_TAC \\ fs [] \\ gvs [isWord_def,glob_real_inv_def]
  \\ fs [full_gc_def,copying_gcTheory.gc_move_list_def]
  \\ rpt (pairarg_tac \\ fs []) \\ gvs []
  \\ Cases_on ‘h’ \\ fs [word_addr_def,isWord_def]
  \\ rename [‘Data aa’] \\ Cases_on ‘aa’ \\ fs [word_addr_def,isWord_def]
  \\ fs [word_full_gc_def,word_gc_move_roots_def]
  \\ rpt (pairarg_tac \\ fs []) \\ gvs []
  \\ fs [word_gc_move_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ fs []) \\ gvs []) |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL;

Definition do_partial_def:
  do_partial c s =
    case c.gc_kind of
    | Generational l => word_gen_gc_can_do_partial l s
    | _ => F
End

Theorem heap_segment_IMP_split:
   heap_segment (m,n) heap = SOME (x1,x2,x3) ==>
    heap_split m heap = SOME (x1,x2++x3) /\
    heap_split n heap = SOME (x1++x2,x3)
Proof
  strip_tac \\ drule heap_segment_IMP \\ strip_tac \\ rveq
  \\ rpt strip_tac
  THEN1
   (full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [heap_split_APPEND_if] \\ fs []
    \\ rw [] \\ Cases_on `x2` \\ fs [heap_length_def,el_length_def])
  \\ full_simp_tac std_ss [heap_split_APPEND_if] \\ fs []
QED

Theorem heap_split_IMP_heap_length:
   !heap n h1 h2.
      heap_split n heap = SOME (h1,h2) ==>
      heap_length h1 = n
Proof
  Induct \\ fs [heap_split_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rveq  \\ fs []
  \\ res_tac \\ fs [heap_length_def]
QED

Theorem heap_split_APPEND_EQ:
   !h1 h2 a.
      heap_split a (h1 ++ h2) = SOME (h1,h2) <=>
      a = heap_length h1
Proof
  rw [] \\ eq_tac \\ rw []
  THEN1 (drule heap_split_IMP_heap_length \\ fs [])
  \\ fs [heap_split_APPEND_if]
QED

Theorem heap_split_IMP_APPEND:
   !heap n h1 h2. heap_split n heap = SOME (h1,h2) ==> heap = h1 ++ h2
Proof
  Induct \\ fs[heap_split_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rveq \\ fs [] \\ res_tac
QED

Theorem heap_length_nil:
   heap_length m = 0 <=> m = []
Proof
  Cases_on `m` \\ fs [heap_length_def,el_length_def]
QED

Theorem abs_ml_inv_GenState_IMP_heap_length_FILTER:
   abs_ml_inv c stack refs
        (xs,heap,be,a,sp,sp1,GenState n (t::ts))
        (heap_length heap) tss /\
    c.gc_kind = Generational (y::ys) /\
    heap_split (a+sp+sp1) heap = SOME (h1,h2) ==>
    EVERY isDataElement h2 /\
    heap_length (FILTER isDataElement heap) = a + heap_length h2
Proof
  fs [abs_ml_inv_def,unused_space_inv_def,gc_kind_inv_def]
  \\ strip_tac \\ fs []
  \\ `EVERY isDataElement h2` by
       (fs [EVERY_MEM] \\ Cases \\ strip_tac \\ res_tac \\ fs [isRef_def])
  \\ fs [data_up_to_def]
  \\ Cases_on `sp + sp1 = 0` \\ fs []
  THEN1
   (drule heap_split_IMP_APPEND \\ strip_tac \\ rveq
    \\ fs [FILTER_APPEND]
    \\ fs [GSYM FILTER_EQ_ID,heap_length_APPEND]
    \\ rveq \\ fs [heap_split_APPEND_EQ])
  \\ drule heap_split_heap_split
  \\ qpat_x_assum `heap_split a heap = _` assume_tac
  \\ disch_then drule \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [GSYM FILTER_EQ_ID,heap_length_APPEND,FILTER_APPEND]
  \\ pop_assum kall_tac
  \\ fs [] \\ drule heap_split_IMP_heap_length
  \\ pop_assum mp_tac
  \\ fs [] \\ drule heap_split_IMP_heap_length
  \\ rpt strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ qpat_x_assum `heap_lookup _ _ = _` mp_tac
  \\ simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ simp_tac std_ss [heap_lookup_APPEND]
  \\ reverse (rw []) \\ fs [heap_length_nil]
  \\ Cases_on `m` \\ fs [heap_length_def]
  \\ fs [heap_lookup_def] \\ rveq \\ fs [isDataElement_def]
  \\ fs [SUM_APPEND,el_length_def]
  \\ rfs [] \\ fs [GSYM heap_length_def,heap_length_nil]
QED

val new_trig_ok = prove(
  ``a <=+ (bytes_in_word * n2w n) /\ good_dimindex (:'a) ==>
    a <=+ new_trig (bytes_in_word * (n2w n):'a word) a x``,
  Cases_on `a` \\ fs [new_trig_def] \\ rw []
  \\ fs [WORD_LO,WORD_LS,MIN_DEF]
  \\ rw [] \\ rfs [w2n_lt]);

Theorem byte_aligned_IMP_bytes_in_word:
   byte_aligned w /\ good_dimindex (:'a) ==> ?v. w = bytes_in_word * v:'a word
Proof
  fs [good_dimindex_def] \\ rw []
  \\ fs [bytes_in_word_def,byte_aligned_def]
  \\ fs [aligned_def]
  \\ fs [align_w2n]
  \\ fs [GSYM word_mul_n2w]
  \\ metis_tac []
QED

Theorem MULT_bytes_in_word_LESS_EQ_IMP:
   w2n (k * bytes_in_word:'a word) ≤ w2n (bytes_in_word * n2w n:'a word) /\
    good_dimindex (:'a) ==>
    ?l. k * bytes_in_word = n2w l * bytes_in_word /\ l <= n
Proof
  fs [good_dimindex_def] \\ rw []
  \\ fs [bytes_in_word_def,byte_aligned_def]
  \\ Cases_on `k` \\ fs [word_mul_n2w]
  \\ fs [dimword_def]
  THEN1
   (`0 < 4:num /\ 0 < 1073741824n` by EVAL_TAC
    \\ imp_res_tac (GSYM MOD_COMMON_FACTOR) \\ fs []
    \\ qexists_tac `n' MOD 1073741824`
    \\ `0 < 1073741824n` by EVAL_TAC \\ conj_tac THEN1 fs []
    \\ drule DIVISION
    \\ disch_then (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
    \\ fs [])
  THEN1
   (`0 < 8:num /\ 0 < 2305843009213693952n` by EVAL_TAC
    \\ imp_res_tac (GSYM MOD_COMMON_FACTOR)
    \\ fs []
    \\ qexists_tac `n' MOD 2305843009213693952`
    \\ `0 < 2305843009213693952n` by EVAL_TAC \\ conj_tac THEN1 fs []
    \\ drule DIVISION
    \\ disch_then (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
    \\ fs [])
QED

val new_trig_LESS_EQ = prove(
  ``good_dimindex (:'a) ==>
    ?k. new_trig (bytes_in_word * (n2w n):'a word) a22 a33 =
        bytes_in_word * n2w k /\ k <= n``,
  rw [new_trig_def]
  \\ fs [GSYM NOT_LESS]
  \\ fs [NOT_LESS]
  \\ TRY (qexists_tac `n` \\ fs [] \\ NO_TAC)
  THEN1
   (rw [MIN_DEF] THEN1 (qexists_tac `n` \\ fs []) \\ fs [NOT_LESS]
    \\ `?k. get_gen_size a33 = bytes_in_word * k` by
      (Cases_on `a33` \\ rw [get_gen_size_def] \\ metis_tac [WORD_MULT_COMM])
    \\ fs [] \\ imp_res_tac MULT_bytes_in_word_LESS_EQ_IMP
    \\ qexists_tac `l` \\ fs [])
  \\ imp_res_tac byte_aligned_IMP_bytes_in_word \\ rveq
  \\ imp_res_tac (SIMP_RULE std_ss [Once WORD_MULT_COMM]
        MULT_bytes_in_word_LESS_EQ_IMP)
  \\ fs [] \\ qexists_tac `l` \\ fs []);

Definition alloc_size_def:
  alloc_size k = (if k * (dimindex (:'a) DIV 8) < dimword (:α) then
                    n2w (k * (dimindex (:'a) DIV 8))
                  else (-1w)):'a word
End

Theorem word_gc_fun_lemma = Q.prove(`
  abs_ml_inv c (v::MAP FST stack) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
   good_dimindex (:'a) /\
   heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
   LIST_REL (\v w. word_addr c v = w) hs (s ' Globals::MAP SND stack) /\
   gc_combined (make_gc_conf limit) c.gc_kind
        (hs,heap,gens,a+sp+sp1,do_partial c s) =
     (roots2,heap2,a2,n2,gens2,T) ==>
   ?stack1 m1 s1 a1 k2 k3.
     word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
     heap_in_memory_store heap2 a2 k2 k3 gens2 c s1 m1 dm limit /\ k2 + k3 = n2 /\
     (!l. FLOOKUP s AllocSize = SOME (Word (alloc_size k)) /\
          c.gc_kind = Generational l /\ word_gen_gc_can_do_partial l s ==>
          has_space (Word (alloc_size k:'a word)) <| store := s1 |> = SOME T) /\
     (c.gc_kind = None \/ c.gc_kind = Simple ==> k3 = 0) /\
     (!l k. FLOOKUP s AllocSize = SOME (Word (alloc_size k)) /\
            c.gc_kind = Generational l /\ ~word_gen_gc_can_do_partial l s /\
            k <= n2 ==> k <= k2) /\
     LIST_REL (λv w. word_addr c v = (w:'a word_loc)) roots2
       (s1 ' Globals::MAP SND (ZIP (MAP FST stack,stack1))) /\
     LENGTH stack1 = LENGTH stack`,
  Cases_on `c.gc_kind` \\ fs [do_partial_def]
  THEN1
   (fs [gc_combinedTheory.gc_combined_def]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [word_gc_fun_def,MAP_ZIP]
    \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE,FUPDATE_LIST,
           FAPPLY_FUPDATE_THM,word_gc_fun_assum_def,glob_real_inv_def]
    \\ fs [FLOOKUP_DEF,isWord_def,theWord_def]
    \\ imp_res_tac gen_starts_in_store_IMP_SOME_Word
    \\ CCONTR_TAC \\ fs [] \\ rfs [isWord_def])
  THEN1
   (strip_tac \\ rveq
    \\ drule (GEN_ALL word_gc_fun_lemma_Simple |> SIMP_RULE std_ss [])
    \\ fs [] \\ rpt (disch_then drule \\ fs [])
    \\ fs [gc_combinedTheory.gc_combined_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
    \\ fs [EVAL ``(make_gc_conf limit).limit``,PULL_EXISTS]
    \\ `a' = heap_length heap'` by
     (fs [full_gc_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [])
    \\ fs [] \\ strip_tac \\ fs [])
  \\ fs [gc_combinedTheory.gc_combined_def]
  \\ IF_CASES_TAC THEN1
   (rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [word_gc_fun_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE,FUPDATE_LIST,
           FAPPLY_FUPDATE_THM,word_gc_fun_assum_def]
    \\ fs [FLOOKUP_DEF,isWord_def,theWord_def]
    \\ drule (word_gen_gc_partial_full_thm |> GEN_ALL) \\ fs []
    \\ rfs [theWord_def]
    \\ qpat_x_assum `_ = s ' Globals` (assume_tac o GSYM) \\ fs []
    \\ `heap_length heap = limit` by (fs [abs_ml_inv_def,heap_ok_def] \\ NO_TAC)
    \\ `MAP SND stack = MAP (word_addr c) xs` by
     (qpat_x_assum `LIST_REL _ _ _` mp_tac
      \\ rpt (pop_assum kall_tac) \\ qspec_tac (`stack`,`stack`)
      \\ Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac
      \\ Cases_on `stack` \\ fs [] \\ rveq \\ res_tac \\ fs [] \\ NO_TAC)
    \\ fs [] \\ disch_then drule
    \\ Cases_on `gens`
    \\ fs [make_gc_conf_def,gc_combinedTheory.make_partial_conf_def]
    \\ rename1 `gen_starts_in_store c (GenState _ gen_starts) _`
    \\ imp_res_tac gen_starts_in_store_IMP \\ fs []
    \\ Cases_on `s ' GenStart` \\ fs [isWord_def] \\ rveq
    \\ fs [gen_starts_in_store_def] \\ rfs []
    \\ Cases_on `gen_starts` THEN1
     (sg `F`
      \\ fs [word_gen_gc_can_do_partial_def]
      \\ Cases_on `l` \\ fs [])
    \\ fs [] \\ rveq
    \\ simp [GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
    \\ simp [AND_IMP_INTRO] \\ fs [theWord_def]
    \\ impl_tac THEN1
     (fs [abs_ml_inv_def]
      \\ qpat_x_assum `gc_kind_inv c a sp sp1 _ heap` mp_tac
      \\ fs [gc_kind_inv_def] \\ strip_tac
      \\ fs [ends_with_refs_def,gen_state_ok_def]
      \\ imp_res_tac heap_split_LESS_EQ \\ fs [])
    \\ disch_then drule
    \\ disch_then (qspec_then `emp` mp_tac)
    \\ impl_tac
    THEN1 fs [SEP_CLAUSES,AC STAR_COMM STAR_ASSOC,word_heap_heap_expand]
    \\ strip_tac \\ rveq \\ fs []
    \\ drule (GEN_ALL partial_gc_IMP) \\ fs []
    \\ strip_tac
    \\ Cases_on `roots` \\ fs []
    \\ Cases_on `l` THEN1 (fs[word_gen_gc_can_do_partial_def])
    \\ `LENGTH xs = LENGTH stack` by metis_tac [LENGTH_MAP]
    \\ fs [] \\ fs [heap_length_APPEND]
    \\ rveq \\ fs [heap_length_heap_expand]
    \\ simp_tac std_ss [word_heap_APPEND,word_heap_heap_expand,heap_length_APPEND,
           SEP_CLAUSES,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,
           heap_length_heap_expand]
    \\ fs [word_heap_APPEND,word_heap_heap_expand,heap_length_APPEND,
           SEP_CLAUSES,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,
           heap_length_heap_expand]
    \\ fs [GSYM PULL_EXISTS]
    \\ qmatch_goalsub_rename_tac `s2.old`
    \\ conj_asm1_tac THEN1 fs [glob_real_inv_def,isWord_def]
    \\ ‘isWord (word_addr c h')’ by
     (Cases_on ‘word_addr c v'’ \\ Cases_on ‘word_addr c h'’ \\ fs [isWord_def]
      \\ fs [word_gen_gc_partial_full_def,word_gen_gc_partial_def,
             word_gen_gc_partial_move_roots_def,word_gen_gc_partial_move_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ fs [AllCaseEqs()] \\ gvs [])
    \\ fs [glob_real_inv]
    \\ conj_asm1_tac THEN1
     (qpat_x_assum `word_gen_gc_can_do_partial _ s` mp_tac
      \\ simp [word_gen_gc_can_do_partial_def,theWord_def]
      \\ fs [WORD_LEFT_ADD_DISTRIB] \\ strip_tac
      \\ match_mp_tac WORD_LOWER_EQ_TRANS \\ asm_exists_tac \\ fs []
      \\ qsuff_tac
           `heap_length s2.old + heap_length s2.h1 <= a + sp /\
            sp1 * (dimindex (:'a) DIV 8) < dimword (:'a) /\
            ((sp1 + a + sp) - (heap_length s2.h1 + heap_length s2.old))
              * (dimindex (:'a) DIV 8) < dimword (:'a)`
      THEN1
       (strip_tac
        \\ qsuff_tac
             `bytes_in_word * n2w sp1 <=+
              bytes_in_word * (n2w (sp1 + a + sp) -
                n2w (heap_length s2.h1 + heap_length s2.old)) :'a word`
        THEN1 (fs [n2w_sub] \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
        \\ fs [addressTheory.word_arith_lemma2,bytes_in_word_def]
        \\ fs [word_mul_n2w,WORD_LS])
      \\ `sp1 + a + sp <= heap_length heap` by
       (qpat_x_assum `abs_ml_inv c _ _ _ _ _` mp_tac
        \\ fs [abs_ml_inv_def,unused_space_inv_def] \\ NO_TAC)
      \\ qsuff_tac `heap_length s2.h1 + heap_length s2.old ≤ a + sp`
      THEN1 (fs [good_dimindex_def] \\ rfs [] \\ fs [])
      \\ fs []
      \\ `FILTER isForwardPointer heap = []` by
           (fs [abs_ml_inv_def,heap_ok_def] \\ NO_TAC) \\ fs []
      \\ `EVERY isDataElement s2.old` by
       (qpat_x_assum `abs_ml_inv c _ _ _ _ _` mp_tac
        \\ fs [abs_ml_inv_def,unused_space_inv_def]
        \\ fs [gc_kind_inv_def,gen_state_ok_def,gen_start_ok_def]
        \\ strip_tac \\ fs [heap_segment_def]
        \\ every_case_tac \\ fs [] \\ rveq
        \\ fs [data_up_to_def]
        \\ qpat_x_assum `heap_split a heap = _` assume_tac
        \\ drule heap_split_heap_split
        \\ qpat_x_assum `heap_split (heap_length s2.old) heap = _` assume_tac
        \\ disch_then drule \\ fs [] \\ strip_tac \\ rveq \\ fs [] \\ NO_TAC)
      \\ drule LIST_REL_similar_data_IMP
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ strip_tac \\ fs []
      \\ drule (GEN_ALL abs_ml_inv_GenState_IMP_heap_length_FILTER) \\ fs []
      \\ `heap_split (a+sp+sp1) heap = SOME (s2.old++curr',refs')` by
             (imp_res_tac heap_segment_IMP_split \\ fs [] \\ NO_TAC)
      \\ fs [] \\ strip_tac
      \\ `heap_length (FILTER isDataElement heap) =
          a + heap_length (FILTER isDataElement s2.r1)` by
             (fs [GSYM FILTER_EQ_ID] \\ NO_TAC)
      \\ fs [FILTER_APPEND,heap_length_APPEND]
      \\ fs [GSYM FILTER_EQ_ID])
    \\ qmatch_goalsub_abbrev_tac `nn <= _:num`
    \\ `nn = heap_length heap` by
     (drule heap_segment_IMP \\ fs []
      \\ strip_tac \\ rveq \\ fs [heap_length_APPEND,Abbr `nn`]
      \\ drule LIST_REL_similar_data_IMP
      \\ strip_tac \\ fs [])
    \\ fs []
    \\ qpat_x_assum `_ = a + (sp + sp1)` (assume_tac o GSYM) \\ fs []
    \\ fs [GSYM WORD_LEFT_ADD_DISTRIB,word_add_n2w]
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ qmatch_goalsub_abbrev_tac `new_trig _ a22 a33`
    \\ `?k9. new_trig (bytes_in_word * n2w s2.n) a22 a33 =
             bytes_in_word * n2w k9 /\ k9 <= s2.n` by metis_tac [new_trig_LESS_EQ]
    \\ conj_tac THEN1 (match_mp_tac new_trig_ok \\ fs [])
    \\ conj_tac
    >- (unabbrev_all_tac \\ fs [good_dimindex_def, dimword_def] \\ rfs [] \\ fs [])
    \\ qexists_tac `k9` \\ fs []
    \\ rewrite_tac [CONJ_ASSOC]
    \\ simp [GSYM PULL_EXISTS]
    \\ reverse conj_tac
    THEN1 (fs [MAP_ZIP] \\ qspec_tac (`t'`,`t'`) \\ Induct \\ fs [])
    \\ fs [PULL_EXISTS]
    \\ qexists_tac `s2.n - k9` \\ fs []
    \\ fs [GSYM WORD_LEFT_ADD_DISTRIB,word_add_n2w]
    \\ fs [wordSemTheory.has_space_def,FLOOKUP_DEF,
           FAPPLY_FUPDATE_THM,wordSemTheory.get_store_def]
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ strip_tac \\ fs [theWord_def] \\ rfs [GSYM WORD_LS]
    \\ qpat_x_assum `_ = bytes_in_word * _` (assume_tac o GSYM) \\ fs []
    \\ simp [new_trig_def] \\ rw [] \\ simp [WORD_LS]
    \\ fs [MIN_DEF] \\ rw [WORD_LS,w2n_lt] \\ fs [WORD_LS])
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [word_gc_fun_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE,FUPDATE_LIST,
         FAPPLY_FUPDATE_THM,word_gc_fun_assum_def]
  \\ fs [FLOOKUP_DEF,isWord_def,theWord_def]
  \\ drule (word_gen_gc_thm |> GEN_ALL) \\ fs []
  \\ rfs [theWord_def]
  \\ qpat_x_assum `_ = s ' Globals` (assume_tac o GSYM) \\ fs []
  \\ `heap_length heap = limit` by (fs [abs_ml_inv_def,heap_ok_def] \\ NO_TAC)
  \\ `MAP SND stack = MAP (word_addr c) xs` by
   (qpat_x_assum `LIST_REL _ _ _` mp_tac
    \\ rpt (pop_assum kall_tac) \\ qspec_tac (`stack`,`stack`)
    \\ Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac
    \\ Cases_on `stack` \\ fs [] \\ rveq \\ res_tac \\ fs [] \\ NO_TAC)
  \\ fs [] \\ disch_then drule
  \\ disch_then (qspec_then `emp` mp_tac)
  \\ impl_tac THEN1
    fs [SEP_CLAUSES,AC STAR_COMM STAR_ASSOC,make_gc_conf_def,
        word_heap_heap_expand]
  \\ drule gen_gcTheory.gen_gc_LENGTH \\ strip_tac
  \\ drule gen_gcTheory.gen_gc_a
  \\ impl_tac THEN1 fs [abs_ml_inv_def,make_gc_conf_def]
  \\ fs [] \\ strip_tac
  \\ Cases_on `roots` \\ fs []
  \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac `new_trig _ a22 _`
  \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ `?k9. new_trig (bytes_in_word * n2w (LENGTH xs1)) a22 l =
           bytes_in_word * n2w k9 /\
           k9 <= LENGTH xs1` by metis_tac [new_trig_LESS_EQ]
  \\ rfs [len_inv_def,heap_length_APPEND,heap_length_heap_expand]
  \\ fs [word_heap_parts_def,word_heap_heap_expand,word_heap_APPEND,
         SEP_CLAUSES,heap_length_APPEND,heap_length_heap_expand]
  \\ qexists_tac `k9`
  \\ qexists_tac `LENGTH xs1 - k9` \\ fs []
  \\ fs [GSYM WORD_LEFT_ADD_DISTRIB,word_add_n2w]
  \\ asm_rewrite_tac [ADD_ASSOC,glob_real_inv]
  \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ drule word_heap_eq_word_list \\ strip_tac
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  \\ qexists_tac `xs1` \\ qexists_tac `xs'`
  \\ fs [SEP_CLAUSES,AC STAR_COMM STAR_ASSOC,word_heap_def]
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_LENGTH \\ fs []
  \\ fs [MAP_ZIP] \\ qspec_tac (`t`,`t`) \\ Induct \\ fs []
  \\ imp_res_tac gen_starts_in_store_IMP
  \\ Cases_on `GenStart ∈ FDOM s` \\ fs [isWord_def]
  \\ fs [gen_starts_in_store_def,isWord_def]
  \\ fs [glob_real_inv_def,isWord_def]
  \\ conj_tac
  THEN1
   (fs [word_gen_gc_def,word_gen_gc_move_roots_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ fs [word_gen_gc_move_def,AllCaseEqs()]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rpt (qpat_x_assum ‘Word _ = word_addr _ _’ (assume_tac o GSYM))
    \\ fs [isWord_def])
  \\ conj_tac THEN1 (Cases_on `l` \\ fs [])
  \\ rpt strip_tac \\ fs [theWord_def]
  \\ qpat_x_assum `new_trig _ _ _ = _` mp_tac
  \\ simp [new_trig_def,MIN_DEF]
  \\ Cases_on `k9 = LENGTH xs1` THEN1 fs []
  \\ `((LENGTH xs1) * (dimindex (:α) DIV 8)) < dimword (:α) /\
      (k9 * (dimindex (:α) DIV 8)) < dimword (:α)` by
   (qpat_x_assum `good_dimindex _` assume_tac \\ fs [good_dimindex_def]
    \\ fs [dimword_def])
  \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ `dimindex (:α) DIV 8 <> 0` by (fs [good_dimindex_def] \\ rfs [])
  \\ IF_CASES_TAC THEN1
   (rw [] \\ fs [NOT_LESS]
    \\ Cases_on `alloc_size k = -1w` THEN1
     (fs [Abbr`a22`,wordsTheory.word_2comp_n2w]
      \\ qpat_x_assum `good_dimindex _` assume_tac \\ fs [good_dimindex_def]
      \\ fs [dimword_def])
    \\ qpat_x_assum `w2n a22 <= _` mp_tac
    \\ fs [Abbr`a22`] \\ rw [alloc_size_def] \\ fs [alloc_size_def])
  \\ IF_CASES_TAC THEN1 fs [NOT_LESS]
  \\ reverse IF_CASES_TAC THEN1 fs [NOT_LESS]
  \\ fs [Abbr`a22`]
  \\ Cases_on `alloc_size k = -1w` THEN1
     (fs [wordsTheory.word_2comp_n2w,alloc_size_def]
      \\ qpat_x_assum `good_dimindex _` assume_tac \\ fs [good_dimindex_def]
      \\ fs [dimword_def,CaseEq"bool"] \\ rfs [])
  \\ fs [] \\ rw [alloc_size_def] \\ fs [alloc_size_def]) |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL;

val abs_ml_inv_ADD = prove(
  ``abs_ml_inv c xs refs (ys,heap2,be,a2,k2 + k3,0,gens2) limit ts /\
    c.gc_kind = Generational l ==>
    abs_ml_inv c xs refs (ys,heap2,be,a2,k2,k3,gens2) limit ts``,
  fs [abs_ml_inv_def,gc_kind_inv_def] \\ rw []
  \\ fs [gen_state_ok_def]);

Theorem alloc_size_check:
  w2n (bytes_in_word * n2w k2 :'a word) < w2n (alloc_size k :'a word) ==>
  k2 * (dimindex (:α) DIV 8) < dimword (:α) /\ good_dimindex (:'a) ==>
  k2 < k
Proof
  rw [alloc_size_def,bytes_in_word_def]
  \\ fs [word_mul_n2w]
  \\ fs [NOT_LESS]
  \\ qsuff_tac `0 < dimindex (:α) DIV 8 /\ k2 < k` THEN1 fs []
  \\ rewrite_tac [GSYM LT_MULT_RCANCEL]
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `dimword (:'a)` \\ fs []
QED

Theorem alloc_size_LEQ_IMP:
  alloc_size k ≤₊ bytes_in_word * n2w sp1 :'a word /\
  sp1 * (dimindex (:α) DIV 8) < dimword (:α) /\
  good_dimindex (:'a) ==> k <= sp1
Proof
  rw [alloc_size_def]
  \\ rfs [bytes_in_word_def,word_mul_n2w,wordsTheory.word_ls_n2w] \\ fs []
  \\ fs [good_dimindex_def] \\ fs [dimword_def]
  \\ fs [wordsTheory.word_2comp_n2w,dimword_def]
  \\ fs [wordsTheory.word_ls_n2w,dimword_def]
QED

Theorem word_gc_fun_correct:
   good_dimindex (:'a) /\
    heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
    word_ml_inv (heap:'a ml_heap,be,a,sp,sp1,gens) limit ts c refs ((v,s ' Globals)::stack) ==>
    ?stack1 m1 s1 heap1 a1 sp1 sp2 gens2 v1 xs.
      word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
      heap_in_memory_store heap1 a1 sp1 sp2 gens2 c s1 m1 dm limit /\
      abs_ml_inv c (v::MAP FST (ZIP (MAP FST stack,stack1))) refs
        (v1::xs,heap1,be,a1,sp1,sp2,gens2) limit ts /\
      word_addr c v1 = s1 ' Globals /\
      LIST_REL (λv w. word_addr c v = w) xs
        (MAP SND (ZIP (MAP FST stack,stack1))) /\
      (FLOOKUP s AllocSize = SOME (Word (alloc_size k)) /\
       has_space (Word ((alloc_size k):'a word)) (t with store := s1) = SOME F /\
       c.gc_kind <> None ==>
         sp1 + sp2 < k /\
         all_reachable_from_roots (v1::xs) heap1 /\
         heap_length heap1 = data_length heap1 + sp1 + sp2)
Proof
  full_simp_tac(srw_ss())[word_ml_inv_def]
  \\ srw_tac[][] \\ drule (GEN_ALL gc_combined_thm)
  \\ disch_then (qspec_then `do_partial c s` mp_tac)
  \\ impl_tac THEN1
   (fs [do_partial_def] \\ TOP_CASE_TAC
    \\ Cases_on `l` THEN1 fs [word_gen_gc_can_do_partial_def]
    \\ Cases_on `gens` \\ fs [heap_in_memory_store_def,has_gen_def]
    \\ imp_res_tac gen_starts_in_store_IMP \\ fs []
    \\ fs [gen_starts_in_store_def] \\ Cases_on `l` \\ fs [])
  \\ strip_tac
  \\ drule (GEN_ALL word_gc_fun_lemma |> ONCE_REWRITE_RULE [CONJ_COMM]
             |> REWRITE_RULE [GSYM CONJ_ASSOC]) \\ fs []
  \\ rpt (disch_then drule) \\ strip_tac \\ fs [] \\ rfs []
  \\ pop_assum (qspec_then `k` strip_assume_tac) \\ fs [] \\ rfs []
  \\ fs [PULL_EXISTS]
  \\ rveq \\ Cases_on `c.gc_kind` \\ fs []
  \\ rpt (asm_exists_tac \\ fs [MAP_ZIP] \\ rfs [MAP_ZIP])
  \\ imp_res_tac abs_ml_inv_ADD
  \\ rpt (asm_exists_tac \\ fs [MAP_ZIP] \\ rfs [MAP_ZIP])
  THEN1
   (rename [`c.gc_kind = Simple`] (* asserts that only one case if left *)
    \\ fs [heap_in_memory_store_def]
    \\ fs [abs_ml_inv_def,unused_space_inv_def,wordSemTheory.has_space_def,
           wordSemTheory.get_store_def]
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ fs [GSYM NOT_LESS] \\ rw []
    \\ drule alloc_size_check
    \\ disch_then match_mp_tac \\ fs []
    \\ fs [heap_ok_def] \\ rveq \\ fs [good_dimindex_def]
    \\ rfs [dimword_def])
  \\ rename [`c.gc_kind = Generational l`] (* asserts that only one case if left *)
  \\ reverse (Cases_on `do_partial c s`)
  THEN1
   (fs [heap_in_memory_store_def]
    \\ fs [abs_ml_inv_def,unused_space_inv_def,wordSemTheory.has_space_def,
           wordSemTheory.get_store_def]
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ fs [GSYM NOT_LESS] \\ rw []
    \\ drule alloc_size_check
    \\ impl_tac
    THEN1 (fs [heap_ok_def] \\ rveq \\ fs [good_dimindex_def] \\ rfs [dimword_def])
    \\ fs [NOT_LESS] \\ rw []
    \\ CCONTR_TAC \\ fs [NOT_LESS]
    \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []
    \\ rfs [do_partial_def,word_gen_gc_can_do_partial_def])
  \\ strip_tac \\ qsuff_tac `F` \\ fs []
  \\ Cases_on `word_gen_gc_can_do_partial l s` \\ rw[] \\ fs []
  THEN1 fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def]
  \\ pop_assum mp_tac \\ fs []
  \\ rfs [do_partial_def,word_gen_gc_can_do_partial_def]
QED

(* -------------------------------------------------------
    definition of state relation
   ------------------------------------------------------- *)

Definition code_rel_def:
  code_rel c s_code (t_code: (num # 'a wordLang$prog) num_map) <=>
    domain t_code = domain s_code UNION set (MAP FST (stubs (:'a) c)) /\
    EVERY (\(n,x). lookup n t_code = SOME x) (stubs (:'a) c) /\
    !n arg_count prog.
      (lookup n s_code = SOME (arg_count:num,prog)) ==>
      (lookup n t_code = SOME (arg_count+1,FST (comp c n 2 prog)))
End

Definition stack_rel_def:
  (stack_rel (Env s1 env) (StackFrame s2 ws vs NONE) <=>
     EVERY (\(x1,x2). x1 <> 0 /\ EVEN x1) vs /\ s1 = s2 /\
     EVERY (\(x1,x2). x1 = 0) ws /\
     ALL_DISTINCT (MAP FST vs) /\
     !n. IS_SOME (lookup n env) <=>
         IS_SOME (lookup (adjust_var n) (fromAList vs))) /\
  (stack_rel (Exc s1 env n) (StackFrame s2 ws vs (SOME (x1,x2,x3))) <=>
     stack_rel (Env s1 env) (StackFrame s2 ws vs NONE) /\ (x1 = n)) /\
  (stack_rel _ _ <=> F)
End

Definition the_global_def:
  the_global g = the (Number 0) (OPTION_MAP (RefPtr T) g)
End

Definition contains_loc_def:
  contains_loc (StackFrame _ vs _ _) (l1,l2) = (ALOOKUP vs 0 = SOME (Loc l1 l2))
End

Definition upper_w2w_def:
  upper_w2w (w:'a word) =
    if dimindex (:'a) = 32 then w2w w << 32 else (w2w w):word64
End

Definition code_oracle_rel_def:
  code_oracle_rel c
      (s_compile:'c -> (num # num # dataLang$prog) list ->
                       (word8 list # word64 list # 'c) option)
      s_compile_oracle t_store
      (t_compile:'c -> (num # num # 'a wordLang$prog) list ->
                       (word8 list # 'a word list # 'c) option)
      t_compile_oracle t_code_buffer t_data_buffer <=>
    t_code_buffer.buffer = [] /\
    t_data_buffer.buffer = [] /\
    FLOOKUP t_store CodeBuffer = SOME (Word t_code_buffer.position) /\
    FLOOKUP t_store CodeBufferEnd =
      SOME (Word (t_code_buffer.position + n2w t_code_buffer.space_left)) /\
    FLOOKUP t_store BitmapBuffer = SOME (Word t_data_buffer.position) /\
    FLOOKUP t_store BitmapBufferEnd =
      SOME (Word (t_data_buffer.position +
                  bytes_in_word * n2w t_data_buffer.space_left)) /\
    s_compile = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o t_compile cfg o
                       MAP (compile_part c)) /\
    t_compile_oracle = (I ## MAP (compile_part c)) o s_compile_oracle /\
    (!n. EVERY (\(n,_). data_num_stubs <= n) (SND (s_compile_oracle n)))
End

Theorem code_oracle_rel_NextFree[simp]:
   code_oracle_rel c scc sco (ts |+ (NextFree,x)) tcc tco cb db ⇔
   code_oracle_rel c scc sco ts tcc tco cb db
Proof
  rw[code_oracle_rel_def,FLOOKUP_UPDATE]
QED

Definition limits_inv_def:
  limits_inv (lims:dataSem$limits) heaplength t_stack_limit c_len_size c_has_fp_ops c_has_fp_tern <=>
    lims.stack_limit = t_stack_limit /\
    lims.length_limit = c_len_size /\
    lims.arch_64_bit = (dimindex (:'a) = 64) /\
    heaplength = SOME (Word (bytes_in_word * n2w lims.heap_limit :'a word)) /\
    lims.heap_limit * w2n (bytes_in_word:'a word) < dimword (:'a) /\
    lims.has_fp_ops = c_has_fp_ops /\
    lims.has_fp_tops = c_has_fp_tern
End

val s = ``(s:('c,'ffi) dataSem$state)``

Definition state_rel_thm:
  state_rel c l1 l2 ^s (t:('a,'c,'ffi) wordSem$state) v1 locs <=>
    (* I/O, clock and handler are the same, GC is fixed, code is compiled *)
    (t.ffi = s.ffi) /\
    (t.clock = s.clock) /\
    (t.handler = s.handler) /\
    (t.gc_fun = word_gc_fun c) /\
    code_rel c s.code t.code /\
    code_oracle_rel c s.compile s.compile_oracle t.store
      t.compile t.compile_oracle t.code_buffer t.data_buffer /\
    good_dimindex (:'a) /\
    shift_length c < dimindex (:'a) /\
    IS_SOME s.tstamps /\
    (* the store *)
    EVERY (\n. n IN FDOM t.store) [Globals] /\
    (* every local is represented in word lang *)
    (v1 = [] ==> lookup 0 t.locals = SOME (Loc l1 l2)) /\
    (!n. IS_SOME (lookup n s.locals) ==>
         IS_SOME (lookup (adjust_var n) t.locals)) /\
    (* the stacks contain the same names, have same shape *)
    EVERY2 stack_rel s.stack t.stack /\
    EVERY2 contains_loc t.stack locs /\
    option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size) t.stack_max /\
    option_le t.stack_max s.stack_max /\
    t.stack_size = s.stack_frame_sizes /\
    t.locals_size = s.locals_size /\
    limits_inv s.limits (FLOOKUP t.store HeapLength) t.stack_limit c.len_size c.has_fp_ops c.has_fp_tern /\
    (* there exists some GC-compatible abstraction *)
    memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
      (v1 ++
       join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
       [(the_global s.global,t.store ' Globals)] ++
       flat s.stack t.stack)
End

Theorem state_rel_thm[allow_rebind] =
  state_rel_thm

Theorem state_rel_def[allow_rebind,compute] =
  state_rel_thm |> REWRITE_RULE [memory_rel_def]

Theorem state_rel_with_clock:
   state_rel a b c s1 s2 d e ⇒
   state_rel a b c (s1 with clock := k) (s2 with clock := k) d e
Proof
  srw_tac[][state_rel_def] \\ fs []
QED

(* -------------------------------------------------------
    init
   ------------------------------------------------------- *)

Theorem flat_NIL:
   flat [] xs = []
Proof
  Cases_on `xs` \\ fs [flat_def]
QED

Definition init_store_ok_def:
  init_store_ok c store m (dm:'a word set) code_buffer data_buffer <=>
    ?limit curr.
      limit <= max_heap_limit (:'a) c /\
      FLOOKUP store Globals = SOME (Word 0w) /\
      FLOOKUP store GlobReal = SOME (Word curr) /\
      FLOOKUP store GenStart = SOME (Word 0w) ∧
      FLOOKUP store CurrHeap = SOME (Word curr) ∧
      FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap ∧
      FLOOKUP store NextFree = SOME (Word curr) ∧
      FLOOKUP store EndOfHeap =
        SOME (Word (curr + bytes_in_word * n2w limit)) ∧
      FLOOKUP store TriggerGC =
        SOME (Word (case c.gc_kind of
                    | Generational _ => curr
                    | _ => curr + bytes_in_word * n2w limit)) ∧
      FLOOKUP store HeapLength =
        SOME (Word (bytes_in_word * n2w limit)) ∧
      FLOOKUP store CodeBuffer = SOME (Word code_buffer.position) ∧
      FLOOKUP store CodeBufferEnd =
        SOME (Word (code_buffer.position + n2w code_buffer.space_left)) ∧
      FLOOKUP store BitmapBuffer = SOME (Word data_buffer.position) ∧
      FLOOKUP store BitmapBufferEnd = SOME
        (Word (data_buffer.position +
               bytes_in_word * n2w data_buffer.space_left)) ∧
      code_buffer.buffer = [] /\
      data_buffer.buffer = [] /\
      (word_list_exists curr (limit + limit)) (fun2set (m,dm)) ∧
      byte_aligned curr
End

Theorem state_rel_init:
    t.ffi = ffi ∧ t.handler = 0 ∧ t.gc_fun = word_gc_fun c ∧
    code_rel c code t.code ∧
    code_oracle_rel c cc co t.store
      t.compile t.compile_oracle t.code_buffer t.data_buffer ∧
    good_dimindex (:α) ∧
    lookup 0 t.locals = SOME (Loc l1 l2) ∧
    t.stack = [] /\
    t.stack_max = SOME 1 /\
    t.locals_size = SOME 0 /\
    t.stack_limit = lim.stack_limit /\
    c.len_size = lim.length_limit /\
    c.be = t.be /\
    (lim.arch_64_bit ⇔ dimindex (:α) = 64) /\
    lim.heap_limit * w2n (bytes_in_word:'a word) < dimword (:α) /\
    t.store ' HeapLength = Word (bytes_in_word * n2w lim.heap_limit) /\
    lim.has_fp_ops = c.has_fp_ops /\
    lim.has_fp_tops = c.has_fp_tern /\
    conf_ok (:'a) c /\
    init_store_ok c t.store t.memory t.mdomain t.code_buffer t.data_buffer ==>
    state_rel c l1 l2 (initial_state ffi code co cc T lim t.stack_size t.clock)
                      (t:('a,'c,'ffi) state) [] []
Proof
  simp_tac std_ss [word_list_exists_ADD,conf_ok_def,init_store_ok_def]
  \\ fs [state_rel_thm,dataSemTheory.initial_state_def,
    join_env_def,lookup_def,the_global_def,
    miscTheory.the_def,flat_NIL,FLOOKUP_DEF] \\ strip_tac \\ fs []
  \\ fs [GSYM (EVAL ``(Smallnum 0)``)]
  \\ fs [wordSemTheory.stack_size_def]
  \\ conj_tac THEN1 (fs [limits_inv_def])
  \\ match_mp_tac IMP_memory_rel_Number
  \\ fs [] \\ conj_tac
  THEN1 (EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ qsuff_tac ‘memory_rel c t.be 0 LN 0 t.store t.memory t.mdomain []’
  >- simp []
  \\ fs [memory_rel_def]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ `(limit+3) * (dimindex (:α) DIV 8) + 1 < dimword (:α)` by
   (fs [good_dimindex_def,dimword_def,max_heap_limit_def]
    \\ rfs [shift_def])
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def]
  \\ ‘abs_ml_inv c [] LN
          (([] : 'a word_loc heap_address list),
           heap_expand limit,t.be,0,
           (case c.gc_kind of Generational l => 0 | _ => limit),
           (case c.gc_kind of Generational l => limit | _ => 0),
           GenState 0
             (case c.gc_kind of
              Generational l => MAP (K 0) l | _ => [])) limit 0’ by
   (Cases_on ‘c.gc_kind’
    \\ fs[abs_ml_inv_def,roots_ok_def,heap_ok_def,heap_length_heap_expand,
       unused_space_inv_def,bc_stack_ref_inv_def,FDOM_EQ_EMPTY]
    \\ fs [heap_expand_def,heap_lookup_def]
    \\ rw [] \\ fs [isForwardPointer_def,bc_ref_inv_def,reachable_refs_def,
                    gc_kind_inv_def,data_up_to_def,be_ok_def]
    \\ fs [heap_split_0]
    \\ fs [gen_state_ok_def,EVERY_MAP,gen_start_ok_def,heap_split_0]
    \\ fs [heap_split_def,el_length_def] \\ every_case_tac
    \\ fs [isRef_def,heap_lookup_def])
  \\ pop_assum $ irule_at Any
  \\ CASE_TAC \\ fs []
  \\ fs [heap_in_memory_store_def,heap_length_heap_expand,word_heap_heap_expand]
  \\ fs [glob_real_inv_def]
  \\ fs [FLOOKUP_DEF,EVAL “Smallnum 0”]
  \\ fs [byte_aligned_def,bytes_in_word_def,good_dimindex_def,
         word_mul_n2w]
  \\ simp_tac bool_ss [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``)]
  \\ once_rewrite_tac [MULT_COMM]
  \\ simp_tac bool_ss [aligned_add_pow] \\ rfs []
  \\ fs [gen_starts_in_store_def,max_heap_limit_def]
  \\ Cases \\ fs [] \\ rw[] \\ EVAL_TAC
  \\ Cases_on `l` \\ fs []
QED

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

Theorem adjust_var_NOT_0[simp]:
   adjust_var n <> 0
Proof
  full_simp_tac(srw_ss())[adjust_var_def]
QED

Theorem state_rel_get_var_IMP:
   state_rel c l1 l2 ^s t v1 locs ==>
    (get_var n s.locals = SOME x) ==>
    ?w. get_var (adjust_var n) t = SOME w
Proof
  full_simp_tac(srw_ss())[dataSemTheory.get_var_def,wordSemTheory.get_var_def]
  \\ full_simp_tac(srw_ss())[state_rel_def] \\ rpt strip_tac
  \\ `IS_SOME (lookup n s.locals)` by full_simp_tac(srw_ss())[] \\ res_tac
  \\ Cases_on `lookup (adjust_var n) t.locals` \\ full_simp_tac(srw_ss())[]
QED

Theorem state_rel_get_vars_IMP:
   !n xs.
      state_rel c l1 l2 ^s t [] locs ==>
      (get_vars n s.locals = SOME xs) ==>
      ?ws. get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs = LENGTH ws)
Proof
  Induct \\ full_simp_tac(srw_ss())[dataSemTheory.get_vars_def,wordSemTheory.get_vars_def]
  \\ rpt strip_tac
  \\ Cases_on `get_var h s.locals` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]
QED

Theorem state_rel_0_get_vars_IMP:
   state_rel c l1 l2 ^s t [] locs ==>
    (get_vars n s.locals = SOME xs) ==>
    ?ws. get_vars (0::MAP adjust_var n) t = SOME ((Loc l1 l2)::ws) /\
         (LENGTH xs = LENGTH ws)
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.get_var_def]
QED

Theorem get_var_T_OR_F:
   state_rel c l1 l2 ^s (t:('a,'c,'ffi) state) [] locs /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    18 MOD dimword (:'a) <> 2 MOD dimword (:'a) /\
    ((x = Boolv T) ==> (w = Word 18w)) /\
    ((x = Boolv F) ==> (w = Word 2w))
Proof
  full_simp_tac(srw_ss())[state_rel_def,get_var_def,wordSemTheory.get_var_def]
  \\ strip_tac \\ strip_tac THEN1 (full_simp_tac(srw_ss())[good_dimindex_def] \\ full_simp_tac(srw_ss())[dimword_def])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac (word_ml_inv_lookup |> Q.INST [`ys`|->`[]`]
                    |> SIMP_RULE std_ss [APPEND])
  \\ pop_assum mp_tac
  \\ simp [word_ml_inv_def,toAList_def,foldi_def,word_ml_inv_def,PULL_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ full_simp_tac(srw_ss())[abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[Boolv_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[v_inv_def] \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]
QED

Theorem get_var_isT_OR_isF:
  state_rel c l1 l2 ^s (t:('a,'c,'ffi) state) [] locs /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    18 MOD dimword (:'a) <> 2 MOD dimword (:'a) /\
    ((isBool T x) ==> (w = Word 18w)) /\
    ((isBool F x) ==> (w = Word 2w))
Proof
  full_simp_tac(srw_ss())[state_rel_def,get_var_def,wordSemTheory.get_var_def]
  \\ strip_tac \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[good_dimindex_def]
        \\ full_simp_tac(srw_ss())[dimword_def])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac (word_ml_inv_lookup |> Q.INST [`ys`|->`[]`]
                    |> SIMP_RULE std_ss [APPEND])
  \\ pop_assum mp_tac
  \\ simp [word_ml_inv_def,toAList_def,foldi_def,word_ml_inv_def,PULL_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ full_simp_tac(srw_ss())[abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[isBool_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[v_inv_def]
  \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ Cases_on `x` \\ fs [isBool_def]
  \\ Cases_on `l` \\ fs [isBool_def,v_inv_def,word_addr_def]
  \\ rveq
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]
QED

Definition mk_loc_def:
  mk_loc (SOME (t1,d1,d2)) = Loc d1 d2
End

Theorem cut_env_IMP_cut_env:
   state_rel c l1 l2 ^s t [] locs /\
    dataSem$cut_env r s.locals = SOME x ==>
    ?y. wordSem$cut_env (adjust_sets r) t.locals = SOME y
Proof
  fs[dataSemTheory.cut_env_def,wordSemTheory.cut_env_def,adjust_sets_def,
     wordSemTheory.cut_envs_def,AllCaseEqs(),PULL_EXISTS,
     wordSemTheory.cut_names_def]
  \\ rw [] >- gvs [state_rel_def,domain_lookup]
  \\ gvs [state_rel_def,SUBSET_DEF]
  \\ rpt strip_tac
  \\ gvs [adjust_set_def,domain_fromAList]
  \\ gvs [MEM_MAP,EXISTS_PROD]
  \\ rename [‘adjust_var a ∈ domain t.locals’]
  \\ gvs [MEM_toAList]
  \\ gvs [domain_lookup]
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum $ qspec_then ‘a’ mp_tac \\ gvs []
  \\ Cases_on ‘lookup (adjust_var a) t.locals’ \\ gvs []
QED

Theorem cut_env_IMP_cut_envs:
  wordSem$cut_env t l = SOME y ⇒
  ∃y1 y2. wordSem$cut_envs t l = SOME (y1,y2) ∧ y = union y2 y1
Proof
  gvs [wordSemTheory.cut_env_def,AllCaseEqs()] \\ rw [] \\ gvs []
QED

Theorem set_vars_sing:
  wordSem$set_vars [q] [w] s = set_var q w s
Proof
  gvs [wordSemTheory.set_vars_def,wordSemTheory.set_var_def]
  \\ EVAL_TAC
QED

Theorem jump_exc_call_env:
   wordSem$jump_exc (call_env x y s) =
   jump_exc (s with stack_max :=
               OPTION_MAP2 MAX s.stack_max
                 (OPTION_MAP2 $+ (stack_size s.stack) y))
Proof
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.call_env_def]
QED

Theorem jump_exc_dec_clock:
   mk_loc (wordSem$jump_exc (dec_clock s)) = mk_loc (jump_exc s)
Proof
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def]
  \\ srw_tac[][] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def]
QED

Theorem LASTN_ADD1[allow_rebind] =
  LASTN_LENGTH_ID
  |> Q.SPEC `x::xs` |> SIMP_RULE (srw_ss()) [ADD1]

Theorem jump_exc_push_env_NONE:
  mk_loc (jump_exc (dec_clock s)) =
  mk_loc (jump_exc s) /\
  mk_loc (jump_exc (push_env y NONE s)) =
  mk_loc (jump_exc (s:('a,'c,'ffi) wordSem$state)) /\
  mk_loc (jump_exc (push_env y NONE s with stack_max := m)) =
  mk_loc (jump_exc (s:('a,'c,'ffi) wordSem$state))
Proof
  fs[wordSemTheory.push_env_def,wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list (SND y) s.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Cases_on `s.handler = LENGTH s.stack` \\ full_simp_tac(srw_ss())[LASTN_ADD1]
  \\ Cases_on `~(s.handler < LENGTH s.stack)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  >- gvs []
  \\ `LASTN (s.handler + 1) (StackFrame s.locals_size (toAList (FST y)) q NONE::s.stack) =
      LASTN (s.handler + 1) s.stack` by
    (match_mp_tac LASTN_TL \\ decide_tac)
  \\ every_case_tac \\ srw_tac[][mk_loc_def]
  \\ gvs []
QED

Theorem option_le_stack_size_cons:
  option_le (stack_size ys) (stack_size (y::ys))
Proof
  fs [wordSemTheory.stack_size_def]
  \\ qpat_abbrev_tac `pat = FOLDR _ _ _`
  \\ Cases_on `pat` \\ Cases_on `stack_size_frame y` \\ fs []
QED

Theorem option_le_stack_size_append:
  !xs ys. option_le (stack_size ys) (stack_size (xs ++ ys))
Proof
  Induct \\ fs [] \\ rw []
  \\ match_mp_tac option_le_trans
  \\ pop_assum (assume_tac o SPEC_ALL)
  \\ asm_exists_tac \\ fs []
  \\ fs [option_le_stack_size_cons]
QED

val s1 = mk_var("s1",type_of s);

Triviality is_some_lookup_union:
  IS_SOME (lookup n (union t1 t2)) ⇔
  IS_SOME (lookup n t1) ∨ IS_SOME (lookup n t2)
Proof
  gvs [IS_SOME_EXISTS,lookup_union,AllCaseEqs()]
  \\ Cases_on ‘lookup n t1’ \\ gvs []
QED

Theorem option_le_tl:
  option_le (OPTION_MAP2 $+ (stack_size (StackFrame opt ws vs x::ys)) s) t ⇒
  option_le (OPTION_MAP2 $+ (stack_size ys) opt) t
Proof
  gvs [wordSemTheory.stack_size_def] \\ Cases_on ‘x’
  \\ gvs [wordSemTheory.stack_size_frame_def]
  \\ Cases_on ‘FOLDR (OPTION_MAP2 $+ ∘ stack_size_frame) (SOME 1) ys’ \\ gvs []
  \\ Cases_on ‘opt’ \\ gvs []
  \\ Cases_on ‘s’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
QED

Theorem inter_union_lemma:
  EVERY (λ(x1,x2). x1 = 0) ws ⇒
  inter (union t (fromAList ws)) (adjust_set s) =
  inter t (adjust_set s)
Proof
  gvs [sptreeTheory.inter_eq,lookup_inter_alt]
  \\ rw [] \\ rw [] \\ rw [lookup_union]
  \\ Cases_on ‘lookup x t’ \\ gvs []
  \\ gvs [lookup_fromAList,ALOOKUP_NONE]
  \\ CCONTR_TAC \\ gvs [MEM_MAP,EVERY_MEM,FORALL_PROD]
  \\ PairCases_on ‘y’ \\ gvs []
  \\ res_tac \\ gvs []
  \\ gvs [adjust_set_def]
  \\ gvs [domain_lookup,adjust_set_def,lookup_fromAList]
  \\ dxrule ALOOKUP_MEM
  \\ gvs [MEM_MAP,FORALL_PROD]
QED

Theorem state_rel_pop_env_IMP:
   state_rel c q l ^s1 t1 xs locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 s2 t2 xs ll
Proof
  fs[pop_env_def]
  \\ Cases_on `s1.stack` \\ fs[] \\ Cases_on `h` \\ fs[]
  \\ srw_tac[][] \\ fs[] \\ fs[state_rel_def]
  \\ fs[stack_rel_def,wordSemTheory.pop_env_def]
  \\ gvs []
  \\ rename [‘stack_rel _ stack_frame’] \\ Cases_on ‘stack_frame’ \\ gvs []
  \\ rename [‘stack_rel _ (StackFrame s7 ws vs opt)’]
  \\ Cases_on ‘opt’
  \\ TRY (rename [‘StackFrame _ _ _ (SOME x)’] \\ PairCases_on ‘x’)
  \\ gvs [stack_rel_def]
  \\ rename [‘contains_loc _ ll’] \\ PairCases_on ‘ll’ \\ gvs []
  \\ gvs [contains_loc_def]
  \\ (conj_tac >-
       (gvs [lookup_union,lookup_fromAList,AllCaseEqs(),ALOOKUP_NONE]
        \\ gvs [EVERY_MEM,MEM_MAP,EXISTS_PROD,FORALL_PROD]
        \\ CCONTR_TAC \\ res_tac \\ metis_tac []))
  \\ simp [is_some_lookup_union]
  \\ qpat_assum ‘_ t1.mdomain limit’ $ irule_at Any
  \\ simp []
  \\ drule option_le_tl \\ strip_tac \\ simp []
  \\ rename [‘StackFrame opt’] \\ Cases_on ‘opt’ \\ gvs []
  \\ gvs [inter_union_lemma]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs[flat_def] \\ srw_tac[][] \\ fs[]
  \\ Cases_on `x` \\ fs[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs[MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []
QED

Theorem inter_insert_union:
  inter (insert n x (union t1 t2)) s = inter (union (insert n x t1) t2) s
Proof
  gvs [sptreeTheory.inter_eq,lookup_inter_alt]
  \\ gvs [lookup_insert,lookup_union] \\ rw []
QED

Theorem state_rel_pop_env_set_var_IMP:
   state_rel c q l ^s1 t1 [(a,w)] locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 (set_var q1 a s2) (set_var (adjust_var q1) w t2) [] ll
Proof
  fs[pop_env_def]
  \\ Cases_on `s1.stack` \\ fs[] \\ Cases_on `h` \\ fs[]
  \\ srw_tac[][] \\ fs[] \\ fs[state_rel_def]
  \\ fs[stack_rel_def,wordSemTheory.pop_env_def,set_var_def,wordSemTheory.set_var_def]
  \\ gvs []
  \\ rename [‘stack_rel _ stack_frame’] \\ Cases_on ‘stack_frame’ \\ gvs []
  \\ rename [‘stack_rel _ (StackFrame s7 ws vs opt)’]
  \\ Cases_on ‘opt’
  \\ TRY (rename [‘StackFrame _ _ _ (SOME x)’] \\ PairCases_on ‘x’)
  \\ gvs [stack_rel_def]
  \\ rename [‘contains_loc _ ll’] \\ PairCases_on ‘ll’ \\ gvs []
  \\ gvs [contains_loc_def]
  \\ (conj_tac >-
       (gvs [lookup_union,lookup_fromAList,AllCaseEqs(),ALOOKUP_NONE,lookup_insert]
        \\ gvs [EVERY_MEM,MEM_MAP,EXISTS_PROD,FORALL_PROD]
        \\ CCONTR_TAC \\ res_tac \\ metis_tac []))
  \\ qpat_assum ‘_ t1.mdomain limit’ $ irule_at Any
  \\ simp []
  \\ drule option_le_tl \\ strip_tac \\ simp []
  \\ (conj_tac >-
       (rpt gen_tac \\ rw [lookup_insert] \\ gvs [is_some_lookup_union]))
  \\ fs [inter_union_lemma,inter_insert_union]
  \\ rename [‘StackFrame opt’] \\ Cases_on ‘opt’ \\ gvs []
  \\ `word_ml_inv (heap,t1.be,a',sp,sp1,gens) limit (THE s1.tstamps) c s1.refs
       ((a,w)::(join_env s vs ++
         [(the_global s1.global,t1.store ' Globals)] ++ flat t ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ fs [MEM,flat_def] \\ srw_tac[][] \\ fs [])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ srw_tac[][] \\ fs []
  \\ Cases_on `x` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []
QED

Theorem BUTLASTN_APPEND_LASTN:
  ∀n l. BUTLASTN n l ++ LASTN n l = l
Proof
  fs [LASTN_def,BUTLASTN_def]
  \\ rewrite_tac [GSYM REVERSE_APPEND,TAKE_DROP]
  \\ fs []
QED

Theorem state_rel_jump_exc:
   state_rel c l1 l2 ^s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w /\
    jump_exc s = SOME s1 ==>
    ?t1 d1 d2 l5 l6 ll.
      jump_exc t = SOME (t1,d1,d2) /\
      LASTN (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
      !i. state_rel c l5 l6 (set_var i x s1) (set_var (adjust_var i) w t1) [] ll
Proof
  simp [jump_exc_def,AllCaseEqs()] \\ strip_tac
  \\ gvs [state_rel_def,wordSemTheory.set_var_def,set_var_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule_all word_ml_inv_get_var_IMP \\ strip_tac
  \\ imp_res_tac LASTN_LIST_REL_LEMMA
  \\ gvs [] \\ gvs [wordSemTheory.jump_exc_def]
  \\ simp [AllCaseEqs(),PULL_EXISTS]
  \\ rename [‘stack_rel _ y5’] \\ Cases_on ‘y5’ \\ gvs [stack_rel_def]
  \\ rename [‘stack_rel _ (StackFrame _ _ _ opt)’]
  \\ Cases_on ‘opt’ \\ gvs [stack_rel_def]
  \\ rename [‘stack_rel _ (StackFrame _ _ _ (SOME z))’]
  \\ PairCases_on ‘z’ \\ gvs [stack_rel_def,contains_loc_def,lookup_insert]
  \\ `s.handler + 1 <= LENGTH s.stack` by decide_tac
  \\ imp_res_tac LASTN_CONS_IMP_LENGTH \\ fs [ADD1]
  \\ imp_res_tac EVERY2_LENGTH \\ fs [lookup_insert,adjust_var_11]
  \\ rename [‘contains_loc _ y0’] \\ PairCases_on ‘y0’ \\ gvs []
  \\ gen_tac
  \\ qpat_assum ‘heap_in_memory_store _ _ _ _ _ _ _ _ _ _’ $ irule_at Any
  \\ fs [lookup_union,lookup_fromAList,contains_loc_def]
  \\ ‘ALOOKUP l0 0 = NONE’ by
    (gvs [ALOOKUP_NONE,MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD]
     \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ fs [])
  \\ gvs []
  \\ conj_tac >- (rw [] \\ gvs [IS_SOME_EXISTS])
  \\ conj_tac
  THEN1
   (qmatch_assum_abbrev_tac `LASTN kk t.stack = tts`
    \\ match_mp_tac option_le_trans \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs []
    \\ match_mp_tac option_le_trans \\ once_rewrite_tac [CONJ_COMM]
    \\ qexists_tac `stack_size t.stack`
    \\ conj_tac THEN1
     (Cases_on `s.locals_size` \\ simp [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size t.stack` \\ simp [OPTION_MAP2_DEF])
    \\ match_mp_tac option_le_trans
    \\ qexists_tac `stack_size tts`
    \\ conj_tac THEN1
     (unabbrev_all_tac \\ fs [wordSemTheory.stack_size_def]
      \\ rw [OPTION_MAP2_DEF] \\ fs [wordSemTheory.stack_size_frame_def]
      \\ fs [IS_SOME_EXISTS] \\ fs [])
    \\ `t.stack = BUTLASTN kk t.stack ++ LASTN kk t.stack` by fs [BUTLASTN_APPEND_LASTN]
    \\ pop_assum (fn th => once_rewrite_tac [th]) \\ fs []
    \\ rewrite_tac [option_le_stack_size_append])
  \\ `s.handler + 1 <= LENGTH s.stack /\
      s.handler + 1 <= LENGTH t.stack` by decide_tac
  \\ imp_res_tac LASTN_IMP_APPEND \\ full_simp_tac(srw_ss())[ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[flat_APPEND,flat_def]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ ‘inter (union (fromAList l0) (fromAList l)) (adjust_set e) =
      inter (fromAList l0) (adjust_set e)’ by
    (gvs [sptreeTheory.inter_eq,lookup_inter_alt]
     \\ rw [] \\ gvs [lookup_union,lookup_fromAList]
     \\ CASE_TAC \\ gvs []
     \\ gvs [ALOOKUP_NONE,MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD]
     \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ fs []
     \\ gvs [domain_lookup,adjust_set_def,lookup_fromAList]
     \\ imp_res_tac ALOOKUP_MEM
     \\ gvs [MEM_MAP,EXISTS_PROD])
  \\ gvs []
  \\ `word_ml_inv (heap,t.be,a,sp,sp1,gens) limit (THE s.tstamps) c s.refs
       ((x,w)::(join_env e l0 ++
          (the_global s.global,t.store ' Globals) :: flat xs ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ gvs []
  \\ simp [SF DNF_ss]
  \\ rpt strip_tac
  \\ disj2_tac \\ disj1_tac
  \\ rename [‘MEM t _’] \\ PairCases_on ‘t’
  \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ qpat_x_assum ‘EVEN _’ $ irule_at Any \\ gvs []
  \\ ‘ALOOKUP l p_1 = NONE’ by
    (gvs [ALOOKUP_NONE,MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD]
     \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ fs [])
  \\ gvs [lookup_union,lookup_fromAList]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
QED

Theorem get_vars_IMP_LENGTH:
   !x t s. dataSem$get_vars x s = SOME t ==> LENGTH x = LENGTH t
Proof
  Induct \\ full_simp_tac(srw_ss())[dataSemTheory.get_vars_def] \\ srw_tac[][]
  \\ every_case_tac \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem get_vars_IMP_LENGTH_word:
   !x t s. wordSem$get_vars x s = SOME t ==> LENGTH x = LENGTH t
Proof
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def] \\ srw_tac[][]
  \\ every_case_tac \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem lookup_adjust_var_fromList2:
   lookup (adjust_var n) (fromList2 (w::ws)) = lookup n (fromList ws)
Proof
  simp[lookup_fromList2,EVEN_adjust_var,lookup_fromList, adjust_var_def,
       GSYM ADD1]
QED

Theorem stack_rel_IMP_size_of_stack:
  !xs ys.
    LIST_REL stack_rel xs ys ==>
    stack_size ys = size_of_stack xs
Proof
  Induct \\ Cases_on `ys` \\ fs [wordSemTheory.stack_size_def,size_of_stack_def]
  \\ rw [] \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ Cases_on `h` \\ Cases_on `h'`
  \\ rename [`StackFrame _ _ _ opt`] \\ Cases_on `opt`
  \\ fs [stack_rel_def,size_of_stack_frame_def]
  \\ TRY (PairCases_on `x`)
  \\ EVAL_TAC \\ fs []
  \\ fs [stack_rel_def,size_of_stack_frame_def]
QED

Theorem state_rel_call_env:
    get_vars args ^s.locals = SOME q /\
    get_vars (MAP adjust_var args) (t:('a,'c,'ffi) wordSem$state) = SOME ws /\
    state_rel c l5 l6 s t [] locs ==>
    state_rel c l1 l2 (call_env q ss (dec_clock s))
      (call_env (Loc l1 l2::ws) ss (dec_clock t)) [] locs
Proof
  full_simp_tac(srw_ss())[state_rel_def,call_env_def,wordSemTheory.call_env_def,LET_THM,
      dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def,lookup_adjust_var_fromList2]
  \\ srw_tac[][lookup_fromList2,lookup_fromList] \\ srw_tac[][]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac stack_rel_IMP_size_of_stack \\ fs []
  THEN1
   (Cases_on `s.stack_max` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `ss` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `size_of_stack s.stack` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `t.stack_max` \\ fs [OPTION_MAP2_DEF])
  THEN1
   (Cases_on `s.stack_max` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `ss` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `size_of_stack s.stack` \\ fs [OPTION_MAP2_DEF]
    \\ Cases_on `t.stack_max` \\ fs [OPTION_MAP2_DEF])
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER]
  \\ Cases_on `y` \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt] \\ srw_tac[][MEM_ZIP]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList]
  \\ rpt disj1_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `k < 2 + LENGTH q * 2 /\ 0 < LENGTH q * 2` by
   (rev_full_simp_tac(srw_ss())[] \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    THEN1 (Cases_on `k` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ full_simp_tac(srw_ss())[] \\ qexists_tac `(k - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[DIV_LT_X] \\ srw_tac[][]
  \\ Cases_on `k` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[DECIDE ``SUC (SUC n) = n + 2``]
  \\ simp [MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
  \\ full_simp_tac(srw_ss())[GSYM ADD1,EL]
QED

Theorem data_get_vars_SNOC_IMP = Q.prove(`
  !x2 x. dataSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
                   dataSem$get_var x1 s = SOME y1 /\
                   dataSem$get_vars x2 s = SOME y2`,
  Induct \\ full_simp_tac(srw_ss())[dataSemTheory.get_vars_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
  |> SPEC_ALL;
Theorem data_get_vars_SNOC_IMP[allow_rebind] =
  data_get_vars_SNOC_IMP

Theorem word_get_vars_SNOC_IMP = Q.prove(`
  !x2 x. wordSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
              wordSem$get_var x1 s = SOME y1 /\
              wordSem$get_vars x2 s = SOME y2`,
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
  |> SPEC_ALL;
Theorem word_get_vars_SNOC_IMP[allow_rebind] =
  word_get_vars_SNOC_IMP

Theorem word_ml_inv_CodePtr:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c s.refs ((CodePtr n,v)::xs) ==>
    (v = Loc n 0)
Proof
  full_simp_tac(srw_ss())[word_ml_inv_def,PULL_EXISTS] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ srw_tac[][word_addr_def]
QED

Theorem state_rel_CodePtr:
   state_rel c l1 l2 s t [] locs /\
    get_vars args s.locals = SOME x /\
    get_vars (MAP adjust_var args) t = SOME y /\
    LAST x = CodePtr n /\ x <> [] ==>
    y <> [] /\ LAST y = Loc n 0
Proof
  rpt strip_tac
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ full_simp_tac bool_ss [MAP_SNOC]
  \\ imp_res_tac data_get_vars_SNOC_IMP
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [LAST_SNOC] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_var_IMP \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_ml_inv_CodePtr
QED

Theorem find_code_thm = Q.prove(`
  !s (t:('a,'c,'ffi)wordSem$state).
      state_rel c l1 l2 ^s t [] locs /\
      get_vars args s.locals = SOME x /\
      get_vars (0::MAP adjust_var args) t = SOME (Loc l1 l2::ws) /\
      find_code dest x s.code fs = SOME (q,r,ss) ==>
      ?args1 n1 n2.
        find_code dest (Loc l1 l2::ws) t.code fs = SOME (args1,FST (comp c n1 n2 r),ss) /\
        state_rel c l1 l2 (call_env q ss (dec_clock s))
          (call_env args1 ss (dec_clock t)) [] locs`,
  Cases_on `dest` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ Cases_on `get_var 0 t` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars (MAP adjust_var args) t` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_x_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ rename [`comp c n 2 r`]
  \\ Q.LIST_EXISTS_TAC [`n`,`2`] \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac state_rel_call_env \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac data_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ `get_vars (0::MAP adjust_var x2) t = SOME (Loc l1 l2::y2')` by
        full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ imp_res_tac state_rel_call_env \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL;
Theorem find_code_thm[allow_rebind] =
  find_code_thm

Theorem cut_env_adjust_set_lookup_0:
  cut_envs (adjust_sets r) t.locals = SOME y ⇒
  lookup 0 (FST y) = lookup 0 t.locals
Proof
  gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),adjust_sets_def,
       wordSemTheory.cut_names_def] \\ rw [] \\ gvs []
  \\ gvs [lookup_inter_alt]
QED

Theorem cut_env_IMP_MEM:
   dataSem$cut_env s r = SOME x ==>
    (IS_SOME (lookup n x) <=> IS_SOME (lookup n s))
Proof
  full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem cut_env_IMP_lookup:
   wordSem$cut_env s r = SOME x /\ lookup n x = SOME q ==>
    lookup n r = SOME q
Proof
  gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def,adjust_sets_def]
  \\ gvs [AllCaseEqs()] \\ rw []
  \\ gvs [wordSemTheory.cut_names_def]
  \\ gvs [lookup_union,lookup_inter_alt]
  \\ gvs [AllCaseEqs()] \\ rw []
QED

Theorem cut_env_IMP_lookup_EQ:
   dataSem$cut_env r y = SOME x /\ n IN domain r ==>
    lookup n x = lookup n y
Proof
  fs [dataSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ fs [lookup_inter] \\ every_case_tac \\ fs []
QED

Theorem cut_env_res_IS_SOME_IMP:
   wordSem$cut_envs r x = SOME y /\ IS_SOME (lookup k (SND y)) ==>
    IS_SOME (lookup k x) /\ IS_SOME (lookup k (SND r))
Proof
  gvs [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ rw [IS_SOME_EXISTS] \\ gvs [lookup_inter_alt,AllCaseEqs()]
  \\ gvs [domain_lookup]
QED

Theorem adjust_var_cut_env_IMP_MEM:
   wordSem$cut_envs (adjust_sets s) r = SOME x ==>
    domain (SND x) SUBSET EVEN /\
    (IS_SOME (lookup (adjust_var n) (SND x)) <=> IS_SOME (lookup n s))
Proof
  gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def,adjust_sets_def]
  \\ gvs [AllCaseEqs()] \\ strip_tac
  \\ gvs [wordSemTheory.cut_names_def]
  \\ gvs [lookup_union,lookup_inter_alt]
  \\ gvs [domain_lookup,lookup_adjust_var_adjust_set_SOME_UNIT]
  \\ conj_tac
  >-
   (gvs [SUBSET_DEF,adjust_set_def,domain_lookup,lookup_fromAList]
    \\ rw [] \\ imp_res_tac ALOOKUP_MEM \\ gvs []
    \\ gvs [MEM_MAP,EXISTS_PROD]
    \\ gvs [adjust_var_def,IN_DEF]
    \\ gvs [EVEN_ADD]
    \\ gvs [EVEN_MULT])
  \\ Cases_on ‘lookup n s’ \\ gvs []
  \\ qsuff_tac ‘adjust_var n ∈ domain r’
  >- (rw [domain_lookup] \\ gvs [])
  \\ gvs [SUBSET_DEF]
  \\ first_x_assum irule
  \\ gvs [domain_lookup]
  \\ fs[domain_lookup,lookup_adjust_var_adjust_set_SOME_UNIT] \\ srw_tac[][]
QED

Theorem NOT_0_domain:
   ~(0 IN domain (adjust_set names))
Proof
  full_simp_tac(srw_ss())[domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Theorem cut_envs_SND_nonzero:
  cut_envs (adjust_sets r) l = SOME y ⇒
  lookup 0 (SND y) = NONE
Proof
  rw [wordSemTheory.cut_envs_def,adjust_sets_def,AllCaseEqs()]
  \\ gvs [wordSemTheory.cut_names_def,lookup_inter_alt,NOT_0_domain]
QED

Theorem lookup_adjust_var_after_cut:
  lookup (adjust_var p_1) (SND y) = SOME z1 ∧
  cut_envs x l = SOME y ∧
  lookup (adjust_var p_1) l = SOME z2 ⇒ z1 = z2
Proof
  rw [wordSemTheory.cut_envs_def,adjust_sets_def,AllCaseEqs()]
  \\ gvs [wordSemTheory.cut_names_def,lookup_inter_alt]
QED

val _ = temp_delsimps ["fromAList_def"]

Theorem state_rel_call_env_push_env: (* TODO: tidy up proof *)
   !opt:(num # 'a wordLang$prog # num # num) option.
      state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem$state) [] locs /\
      get_vars args s.locals = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      dataSem$cut_env r s.locals = SOME x /\
      wordSem$cut_envs (adjust_sets r) t.locals = SOME y ==>
      state_rel c q l (call_env xs ss (push_env x (IS_SOME opt) (dec_clock s)))
       (call_env (Loc q l::ws) ss (push_env y opt (dec_clock t))) []
       ((l1,l2)::locs)
Proof
  Cases \\ TRY (PairCases_on `x'`) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def,call_env_def,push_env_def,
         dataSemTheory.dec_clock_def,
         wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,stack_rel_def]
  \\ full_simp_tac(srw_ss())[lookup_adjust_var_fromList2,contains_loc_def]
  \\ strip_tac
  \\ full_simp_tac(srw_ss())[lookup_fromList,lookup_fromAList]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[IS_SOME_IF]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList]
  \\ imp_res_tac env_to_list_lookup_equiv \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_adjust_set_lookup_0 \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_IMP_MEM
  \\ imp_res_tac adjust_var_cut_env_IMP_MEM \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac wordPropsTheory.env_to_list_ALL_DISTINCT \\ full_simp_tac(srw_ss())[]
  \\ ‘EVERY (λ(x1,x2). x1 = 0) (toAList (FST y))’ by
    gvs [wordSemTheory.cut_envs_def,adjust_sets_def,AllCaseEqs(),
         wordSemTheory.cut_names_def,EVERY_MEM,FORALL_PROD,MEM_toAList,
         lookup_inter_alt]
  \\ rpt strip_tac
  \\ TRY
   (imp_res_tac adjust_var_cut_env_IMP_MEM
    \\ full_simp_tac(srw_ss())[domain_lookup,SUBSET_DEF,PULL_EXISTS]
    \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] \\ ntac 3 strip_tac
    \\ res_tac \\ res_tac \\ full_simp_tac(srw_ss())[IN_DEF] \\ srw_tac[][] \\ strip_tac
    \\ imp_res_tac cut_envs_SND_nonzero \\ fs []
    \\ NO_TAC)
  \\ TRY (imp_res_tac stack_rel_IMP_size_of_stack
          \\ fs [wordSemTheory.stack_size_def,wordSemTheory.stack_size_frame_def,
                 size_of_stack_def,size_of_stack_frame_def]
          \\ fs [OPTION_MAP2_DEF] \\ rw []
          \\ fs [IS_SOME_EXISTS] \\ fs [] \\ NO_TAC)
  \\ rewrite_tac [ALOOKUP_toAList]
  \\ imp_res_tac cut_env_adjust_set_lookup_0 \\ full_simp_tac(srw_ss())[]
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ full_simp_tac(srw_ss())[flat_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ TRY (rpt disj1_tac
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
    \\ full_simp_tac(srw_ss())[MEM_toAList] \\ srw_tac[][MEM_ZIP]
    \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList,lookup_inter_alt]
    \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
    \\ full_simp_tac(srw_ss())[DIV_LT_X]
    \\ `k < 2 + LENGTH xs * 2 /\ 0 < LENGTH xs * 2` by
     (rev_full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[]
      THEN1 (Cases_on `k` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ decide_tac)
      \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[] \\ qexists_tac `(k - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[DIV_LT_X]
    \\ Cases_on `k` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[DECIDE ``SUC (SUC n) = n + 2``]
    \\ full_simp_tac(srw_ss())[MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,EL] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ disj1_tac \\ disj2_tac
  \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList] \\ srw_tac[][MEM_ZIP]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList,lookup_inter_alt]
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ qexists_tac `k` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac cut_env_IMP_lookup \\ full_simp_tac(srw_ss())[]
  \\ TRY (AP_TERM_TAC \\ match_mp_tac cut_env_IMP_lookup_EQ) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[domain_lookup]
  \\ imp_res_tac MEM_IMP_IS_SOME_ALOOKUP \\ rev_full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_res_IS_SOME_IMP
  \\ gvs [adjust_sets_def]
  \\ full_simp_tac(srw_ss())[IS_SOME_EXISTS]
  \\ full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList] \\ rev_full_simp_tac(srw_ss())[]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ full_simp_tac(srw_ss())[unit_some_eq_IS_SOME,IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD]
  \\ srw_tac[][adjust_var_11,adjust_var_DIV_2]
  \\ imp_res_tac MEM_toAList \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[dataSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_toAList]
  \\ rpt var_eq_tac
  \\ imp_res_tac lookup_adjust_var_after_cut \\ gvs []
QED

Theorem find_code_thm_ret:
      state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem$state) [] locs /\
      get_vars args s.locals = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      find_code dest xs s.code fs = SOME (ys,prog,ss) /\
      dataSem$cut_env r s.locals = SOME x /\
      wordSem$cut_envs (adjust_sets r) t.locals = SOME y ==>
      ?args1 n1 n2.
        find_code dest (Loc q l::ws) t.code fs = SOME (args1,FST (comp c n1 n2 prog),ss) /\
        state_rel c q l (call_env ys ss (push_env x F (dec_clock s)))
          (call_env args1 ss (push_env y NONE
          (dec_clock t))) [] ((l1,l2)::locs)
Proof
  reverse (Cases_on `dest`) \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_x_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`2`] \\ full_simp_tac(srw_ss())[]
         \\ qspecl_then [`lookup x' fs`,`NONE`] mp_tac
               (Q.GEN `ss` state_rel_call_env_push_env)
         \\ full_simp_tac(srw_ss())[])
  \\ Q.LIST_EXISTS_TAC [`n`,`2`] \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac data_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `NONE`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ full_simp_tac(srw_ss())[] \\ metis_tac []
QED

Theorem find_code_thm_handler:
      state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem$state) [] locs /\
      get_vars args s.locals = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      find_code dest xs s.code fs = SOME (ys,prog,ss) /\
      dataSem$cut_env r s.locals = SOME x /\
      wordSem$cut_envs (adjust_sets r) t.locals = SOME y ==>
      ?args1 n1 n2.
        find_code dest (Loc q l::ws) t.code fs = SOME (args1,FST (comp c n1 n2 prog),ss) /\
        state_rel c q l (call_env ys ss (push_env x T (dec_clock s)))
          (call_env args1 ss (push_env y
             (SOME (adjust_var x0,(prog1:'a wordLang$prog),nn,l + 1))
          (dec_clock t))) [] ((l1,l2)::locs)
Proof
  reverse (Cases_on `dest`) \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_x_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`2`] \\ full_simp_tac(srw_ss())[]
         \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL) \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ Q.LIST_EXISTS_TAC [`n`,`2`] \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac data_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ full_simp_tac(srw_ss())[] \\ metis_tac []
QED

Theorem data_find_code:
   dataSem$find_code dest xs code fs = SOME(ys,prog,ss) ⇒ ¬bad_dest_args dest xs
Proof
  Cases_on`dest`>>
  full_simp_tac(srw_ss())[dataSemTheory.find_code_def,wordSemTheory.bad_dest_args_def]
QED

Theorem s_key_eq_LENGTH:
   !xs ys. s_key_eq xs ys ==> (LENGTH xs = LENGTH ys)
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[s_key_eq_def]
QED

Theorem s_key_eq_LASTN:
   !xs ys n. s_key_eq xs ys ==> s_key_eq (LASTN n xs) (LASTN n ys)
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[s_key_eq_def,LASTN_ALT]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[s_key_eq_def,LASTN_ALT] \\ res_tac
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[] \\ `F` by decide_tac
QED

Theorem evaluate_mk_loc_EQ:
   evaluate (q,t) = (NONE,t1:('a,'b,'c) state) ==>
    mk_loc (jump_exc t1) = ((mk_loc (jump_exc t)):'a word_loc)
Proof
  qspecl_then [`q`,`t`] mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def]
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t.handler + 1` mp_tac)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def,mk_loc_def]
QED

Theorem mk_loc_eq_push_env_exc_Exception:
   evaluate
      (c:'a wordLang$prog, call_env args1 ss
            (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l))
               (dec_clock t))) = (SOME (Exception xx w),(t1:('a,'b,'c) state)) ==>
    mk_loc (jump_exc t1) = mk_loc (jump_exc t) :'a word_loc
Proof
  qspecl_then [`c`,`call_env args1 ss
    (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
       mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][] \\ fs []
  \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ fs[LET_DEF,LASTN_ADD1]
  \\ srw_tac[][] \\ fs [wordSemTheory.jump_exc_def]
  \\ first_assum (qspec_then `t1.stack` mp_tac)
  \\ imp_res_tac s_key_eq_LENGTH \\ fs [] \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t.handler+1` mp_tac) \\ srw_tac[][]
  \\ every_case_tac \\ fs [s_key_eq_def,s_frame_key_eq_def,mk_loc_def]
QED

Theorem evaluate_IMP_domain_EQ:
   evaluate (c,call_env (args1:'a word_loc list) ss
     (push_env y (opt:(num # ('a wordLang$prog) # num # num) option) (dec_clock t))) =
      (SOME (Result ll w),t1) /\ pop_env t1 = SOME t2 ==>
    domain t2.locals = domain (FST y) UNION domain (SND y)
Proof
  qspecl_then [`c`,`call_env args1 ss (push_env y opt (dec_clock t))`] mp_tac
      wordPropsTheory.evaluate_stack_swap \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def]
  \\ Cases_on `opt` \\ full_simp_tac(srw_ss())[] \\ TRY (PairCases_on `x`)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list (SND y) (dec_clock t).permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[s_frame_key_eq_def,domain_fromAList] \\ srw_tac[][]
  \\ qpat_x_assum `xxx = MAP FST l` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList] \\ metis_tac []
QED

Theorem evaluate_IMP_domain_EQ_Exc:
   evaluate (c,call_env args1 ss (push_env y
      (SOME (x0,prog1:'a wordLang$prog,x1,l))
      (dec_clock (t:('a,'b,'c) state)))) = (SOME (Exception ll w),t1) ==>
    domain t1.locals = domain (FST y) UNION domain (SND y)
Proof
  qspecl_then [`c`,`call_env args1 ss
     (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
     mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,LASTN_ADD1] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `t1.stack` mp_tac) \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LASTN \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (qspec_then `t.handler+1` mp_tac) \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[s_frame_key_eq_def,domain_fromAList] \\ srw_tac[][]
  \\ qpat_x_assum `xxx = MAP FST lss` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList] \\ metis_tac []
QED

Theorem mk_loc_jump_exc:
   mk_loc
       (jump_exc
          (call_env args1 ss
             (push_env y (SOME (adjust_var n,prog1,x0,l))
                (dec_clock t)))) = Loc x0 l
Proof
  fs [wordSemTheory.push_env_def,wordSemTheory.call_env_def,wordSemTheory.jump_exc_def]
  \\ Cases_on `env_to_list (SND y) (dec_clock t).permute`
  \\ fs [LET_DEF,LASTN_ADD1,mk_loc_def]
QED

Definition inc_clock_def:
  inc_clock n (t:('a,'c,'ffi) wordSem$state) = t with clock := t.clock + n
End

Theorem inc_clock_0[simp]:
   !t. inc_clock 0 t = t
Proof
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality]
QED

Theorem inc_clock_inc_clock[simp]:
   !t. inc_clock n (inc_clock m t) = inc_clock (n+m) t
Proof
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality,AC ADD_ASSOC ADD_COMM]
QED

Theorem mk_loc_jmup_exc_inc_clock[simp]:
   mk_loc (jump_exc (inc_clock ck t)) = mk_loc (jump_exc t)
Proof
  full_simp_tac(srw_ss())[mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]
QED

Theorem jump_exc_inc_clock_EQ_NONE:
   jump_exc (inc_clock n s) = NONE <=> jump_exc s = NONE
Proof
  full_simp_tac(srw_ss())[mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]
QED

Theorem state_rel_lookup_globals:
   state_rel c l1 l2 s t v1 locs ∧ s.global = SOME g (* ∧
   FLOOKUP s.refs g = SOME (ValueArray gs) *)
   ⇒
   ∃x u.
   FLOOKUP t.store Globals = SOME (Word (get_addr c x u))
Proof
  rw[state_rel_def]
  \\ fs[the_global_def,miscTheory.the_def]
  \\ qmatch_assum_abbrev_tac`word_ml_inv heapp limit stamps c refs _`
  \\ qmatch_asmsub_abbrev_tac`[gg]`
  \\ `∃rest. word_ml_inv heapp limit stamps c refs (gg::rest)`
  by (
    qmatch_asmsub_abbrev_tac`a1 ++ [gg] ++ a2`
    \\ qexists_tac`a1++a2`
    \\ simp[Abbr`heapp`]
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ fs[word_ml_inv_def,Abbr`heapp`]
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[Abbr`gg`,v_inv_def]
  \\ simp[FLOOKUP_DEF]
  \\ first_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ rveq
  \\ simp_tac(srw_ss())[word_addr_def]
  \\ metis_tac[]
QED

Theorem state_rel_cut_env:
   state_rel c l1 l2 s t [] locs /\
    dataSem$cut_env names s.locals = SOME x ==>
    state_rel c l1 l2 (s with locals := x) t [] locs
Proof
  full_simp_tac(srw_ss())[state_rel_def,dataSemTheory.cut_env_def] \\ srw_tac[][]
  THEN1 (full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ rpt disj1_tac
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP]
  \\ Cases_on `y` \\ full_simp_tac(srw_ss())[EXISTS_PROD,MEM_FILTER]
  \\ qexists_tac `q` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (AP_TERM_TAC
    \\ full_simp_tac(srw_ss())[FUN_EQ_THM,lookup_inter_alt,MEM_toAList,domain_lookup]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,domain_lookup] \\ srw_tac[][]
    \\ imp_res_tac IMP_adjust_var
    \\ `lookup (adjust_var ((q - 2) DIV 2))
           (adjust_set (inter s.locals names)) = NONE` by
     (simp [lookup_adjust_var_adjust_set_NONE,lookup_inter_alt]
      \\ full_simp_tac(srw_ss())[domain_lookup]) \\ rev_full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt]
  \\ full_simp_tac(srw_ss())[domain_lookup,unit_some_eq_IS_SOME,adjust_set_def,lookup_fromAList]
  \\ rev_full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP] \\ srw_tac[][]
  \\ Cases_on `y'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt]
QED

Theorem state_rel_get_var_RefPtr:
   state_rel c l1 l2 s t v1 locs ∧
   get_var n s.locals = SOME (RefPtr b p) ⇒
   ∃f u. get_var (adjust_var n) t = SOME (Word (get_addr c (FAPPLY f p) u))
Proof
  rw[]
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs[state_rel_def,wordSemTheory.get_var_def,dataSemTheory.get_var_def]
  \\ full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)]
  \\ drule (GEN_ALL word_ml_inv_lookup)
  \\ disch_then drule
  \\ disch_then drule
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`v1 ++ (rr ++ ls)`
  \\ qmatch_abbrev_tac`P (v1 ++ (rr ++ ls)) ⇒ _`
  \\ strip_tac
  \\ `P (rr ++ v1 ++ ls)`
  by (
    unabbrev_all_tac
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ simp[Abbr`P`,Abbr`rr`,word_ml_inv_def]
  \\ strip_tac \\ rveq
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[v_inv_def]
  \\ simp[word_addr_def]
  \\ metis_tac[]
QED

Theorem state_rel_get_var_Block:
   state_rel c l1 l2 s t v1 locs ∧
   get_var n s.locals = SOME (Block ts tag vs) ⇒
   ∃w. get_var (adjust_var n) t = SOME (Word w)
Proof
  rw[]
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs[state_rel_def,wordSemTheory.get_var_def,dataSemTheory.get_var_def]
  \\ full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)]
  \\ drule (GEN_ALL word_ml_inv_lookup)
  \\ disch_then drule
  \\ disch_then drule
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`v1 ++ (rr ++ ls)`
  \\ qmatch_abbrev_tac`P (v1 ++ (rr ++ ls)) ⇒ _`
  \\ strip_tac
  \\ `P (rr ++ v1 ++ ls)`
  by (
    unabbrev_all_tac
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ simp[Abbr`P`,Abbr`rr`,word_ml_inv_def]
  \\ strip_tac \\ rveq
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[v_inv_def]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ IF_CASES_TAC \\ simp[word_addr_def]
  \\ strip_tac \\ rveq
  \\ simp[word_addr_def]
QED

val s' = mk_var("s'",type_of s);

Theorem state_rel_cut_state_opt_get_var:
   state_rel c l1 l2 ^s t [] locs ∧
   cut_state_opt names_opt s = SOME x ∧
   get_var v x.locals = SOME w ⇒
   ∃s'. state_rel c l1 l2 ^s' t [] locs ∧
        get_var v s'.locals = SOME w
Proof
  rw[cut_state_opt_def]
  \\ every_case_tac \\ fs[] >- metis_tac[]
  \\ fs[cut_state_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac state_rel_cut_env
  \\ metis_tac[]
QED

Theorem jump_exc_push_env_NONE_simp[allow_rebind]:
  (jump_exc (wordSem$dec_clock t) = NONE <=> jump_exc t = NONE) /\
  (jump_exc (wordSem$push_env y NONE t) = NONE <=> jump_exc t = NONE) /\
  (jump_exc (t with stack_max := b) = NONE <=> jump_exc t = NONE)
Proof
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
                          wordSemTheory.dec_clock_def]
  \\ srw_tac[][] THEN1 every_case_tac
  \\ full_simp_tac(srw_ss())[wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Cases_on `t.handler = LENGTH t.stack` \\ full_simp_tac(srw_ss())[LASTN_ADD1]
  \\ Cases_on `~(t.handler < LENGTH t.stack)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ fs [CaseEq"list",CaseEq"stack_frame",CaseEq"option",pair_case_eq]
  \\ `LASTN (t.handler + 1) (StackFrame t.locals_size (toAList (FST y)) q NONE::t.stack) =
      LASTN (t.handler + 1) t.stack` by
    (match_mp_tac LASTN_TL \\ decide_tac) \\ fs []
QED

Theorem s_key_eq_handler_eq_IMP:
   s_key_eq t.stack t1.stack /\ t.handler = t1.handler ==>
    (jump_exc t1 <> NONE <=> jump_exc t <> NONE)
Proof
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def] \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t1.handler < LENGTH t1.stack` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t1.handler + 1` mp_tac)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def]
QED

Theorem eval_NONE_IMP_jump_exc_NONE_EQ:
   wordSem$evaluate (q,t) = (NONE,t1) ==> (jump_exc t1 = NONE <=> jump_exc t = NONE)
Proof
  srw_tac[][] \\ mp_tac (wordPropsTheory.evaluate_stack_swap |> Q.SPECL [`q`,`t`])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ imp_res_tac s_key_eq_handler_eq_IMP \\ metis_tac []
QED

Theorem jump_exc_push_env_SOME:
   jump_exc (push_env y (SOME (x,prog1,l1,l2)) t) <> NONE
Proof
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[LASTN_ADD1]
QED

Theorem eval_push_env_T_Raise_IMP_stack_length:
   evaluate (p,call_env ys ss (push_env x T (dec_clock (s:('c,'ffi)dataSem$state)))) =
       (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack = LENGTH s.stack
Proof
  qspecl_then [`p`,`call_env ys ss (push_env x T (dec_clock s))`]
    mp_tac dataPropsTheory.evaluate_stack_swap
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ fs []
  \\ full_simp_tac(srw_ss())[call_env_def,jump_exc_def,push_env_def,dataSemTheory.dec_clock_def,LASTN_ADD1,LET_THM]
  \\ rveq \\ fs []
QED

Theorem eval_push_env_SOME_exc_IMP_s_key_eq:
   evaluate (p, call_env args1 ss (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))) =
      (SOME (Exception l w),t1) ==>
    s_key_eq t1.stack t.stack /\ t.handler = t1.handler
Proof
  qspecl_then [`p`,`call_env args1 ss (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))`]
    mp_tac wordPropsTheory.evaluate_stack_swap
  \\ srw_tac[][] \\ fs []
  \\ fs [wordSemTheory.call_env_def,wordSemTheory.jump_exc_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def,LASTN_ADD1]
  \\ srw_tac[][] \\ fs []
  \\ Cases_on `env_to_list (SND y) t.permute` \\ fs [LET_DEF,LASTN_ADD1]
  \\ srw_tac[][] \\ fs []
QED

Theorem eval_exc_stack_shorter:
   evaluate (c,call_env ys ss (push_env x F (dec_clock (s:('c,'ffi)dataSem$state)))) =
      (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack < LENGTH s.stack
Proof
  srw_tac[][] \\ qspecl_then [`c`,`call_env ys ss (push_env x F (dec_clock s))`]
             mp_tac dataPropsTheory.evaluate_stack_swap
  \\ full_simp_tac(srw_ss())[] \\ once_rewrite_tac [EQ_SYM_EQ] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[dataSemTheory.jump_exc_def,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
  \\ fs []
  \\ qpat_x_assum `xx = SOME s2` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[ADD1]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `LENGTH (LASTN (s.handler + 1) s.stack)`
  \\ full_simp_tac(srw_ss())[LENGTH_LASTN_LESS]
QED

Theorem NOT_1_domain:
   ~(1 IN domain (adjust_set names))
Proof
  full_simp_tac(srw_ss())[domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Theorem NOT_3_domain:
   ~(3 IN domain (adjust_set names))
Proof
  full_simp_tac(srw_ss())[domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `p_1'` \\ fs []
QED

Theorem NOT_5_domain:
   ~(5 IN domain (adjust_set names))
Proof
  full_simp_tac(srw_ss())[domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `p_1'` \\ fs []  \\ Cases_on `n` \\ fs []
QED

Theorem cut_names_adjust_set_insert_1:
   wordSem$cut_names (adjust_set names) (insert 1 w l) = wordSem$cut_names (adjust_set names) l
Proof
  fs [wordSemTheory.cut_names_def,MATCH_MP SUBSET_INSERT_EQ_SUBSET NOT_1_domain]
  \\ srw_tac[][] \\ fs [lookup_inter,lookup_insert]
  \\ Cases_on `x = 1` \\ fs [] \\ every_case_tac \\ srw_tac[][]
  \\ fs [SIMP_RULE std_ss [domain_lookup] NOT_1_domain]
QED

Theorem cut_names_adjust_set_insert_3:
   wordSem$cut_names (adjust_set names) (insert 3 w l) = wordSem$cut_names (adjust_set names) l
Proof
  fs [wordSemTheory.cut_names_def,MATCH_MP SUBSET_INSERT_EQ_SUBSET NOT_3_domain]
  \\ srw_tac[][] \\ fs [lookup_inter,lookup_insert]
  \\ Cases_on `x = 3` \\ fs [] \\ every_case_tac \\ srw_tac[][]
  \\ fs [SIMP_RULE std_ss [domain_lookup] NOT_3_domain]
QED

Theorem case_EQ_SOME_IFF:
   (case p of NONE => NONE | SOME x => g x) = SOME y <=>
    ?x. p = SOME x /\ g x = SOME y
Proof
  Cases_on `p` \\ full_simp_tac(srw_ss())[]
QED

Theorem state_rel_set_store_AllocSize:
   state_rel c l1 l2 s (set_store AllocSize (Word w) t) v locs =
    state_rel c l1 l2 s t v locs
Proof
  full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.set_store_def]
  \\ eq_tac \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[heap_in_memory_store_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ metis_tac []
QED

Theorem inter_insert:
   inter (insert n x t1) t2 =
    if n IN domain t2 then insert n x (inter t1 t2) else inter t1 t2
Proof
  srw_tac[][] \\ full_simp_tac(srw_ss())[spt_eq_thm,wf_inter,wf_insert,lookup_inter_alt,lookup_insert]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem lookup_0_adjust_set:
   lookup 0 (adjust_set l) = NONE
Proof
  fs[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
QED

Theorem lookup_1_adjust_set:
   lookup 1 (adjust_set l) = NONE
Proof
  full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Theorem lookup_3_adjust_set:
   lookup 3 (adjust_set l) = NONE
Proof
  full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Theorem lookup_5_adjust_set:
   lookup 5 (adjust_set l) = NONE
Proof
  full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Theorem lookup_ODD_adjust_set:
   ODD n ==> lookup n (adjust_set l) = NONE
Proof
  fs[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ CCONTR_TAC \\ fs [] \\ rveq
  \\ fs [EVEN_adjust_var,ODD_EVEN]
QED

Theorem wf_adjust_set:
   wf (adjust_set s)
Proof
  fs [adjust_set_def,wf_fromAList]
QED

Theorem lookup_adjust_set:
   lookup n (adjust_set s) =
   if ODD n \/ n = 0 then NONE else
   if (n - 2) DIV 2 IN domain s then SOME () else NONE
Proof
  IF_CASES_TAC
  >- (gvs [lookup_ODD_adjust_set]
      \\ gvs [adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,EXISTS_PROD])
  \\ Cases_on ‘lookup n (adjust_set s)’ \\ gvs []
  \\ gvs [domain_lookup]
  \\ fs [adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ gvs [MEM_toAList]
  >-
   (Cases_on ‘lookup ((n − 2) DIV 2) s’ \\ gvs []
    \\ first_x_assum $ qspec_then ‘(n − 2) DIV 2’ mp_tac \\ gvs []
    \\ gvs [adjust_var_def,GSYM EVEN_ODD]
    \\ imp_res_tac EVEN_ODD_EXISTS \\ rveq
    \\ Cases_on ‘m’ \\ gvs [] \\ fs [MULT_CLAUSES]
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD,MEM_toAList]
  \\ gvs [adjust_var_def]
QED

Theorem adjust_set_inter:
   adjust_set (inter t1 t2) = inter (adjust_set t1) (adjust_set t2)
Proof
  fs [wf_adjust_set,wf_inter,spt_eq_thm,lookup_inter_alt,domain_lookup]
  \\ gvs [lookup_adjust_set] \\ rw [] \\ gvs []
QED

Theorem state_rel_insert_1:
   state_rel c l1 l2 s (t with locals := insert 1 x t.locals) v locs =
    state_rel c l1 l2 s t v locs
Proof
  fs [state_rel_def] \\ eq_tac \\ srw_tac[][]
  \\ fs [lookup_insert,adjust_var_NEQ_1]
  \\ fs [inter_insert,domain_lookup,lookup_1_adjust_set]
  \\ metis_tac []
QED

Theorem state_rel_insert_3:
   state_rel c l1 l2 s (t with locals := insert 3 x t.locals) v locs =
    state_rel c l1 l2 s t v locs
Proof
  fs [state_rel_def] \\ eq_tac \\ srw_tac[][]
  \\ fs [lookup_insert,adjust_var_NEQ_1]
  \\ asm_exists_tac \\ fs []
  \\ fs [inter_insert,domain_lookup,lookup_3_adjust_set]
QED

Theorem state_rel_insert_7:
   state_rel c l1 l2 s (t with locals := insert 7 x t.locals) v locs =
    state_rel c l1 l2 s t v locs
Proof
  fs [state_rel_def] \\ eq_tac \\ srw_tac[][]
  \\ fs [lookup_insert,adjust_var_NEQ_1]
  \\ asm_exists_tac \\ fs []
  \\ fs [inter_insert,domain_lookup,lookup_ODD_adjust_set]
QED

Theorem state_rel_insert_3_1:
   state_rel c l1 l2 s (t with locals := insert 3 x (insert 1 y t.locals)) v locs =
    state_rel c l1 l2 s t v locs
Proof
  fs [state_rel_def] \\ eq_tac \\ srw_tac[][]
  \\ fs [lookup_insert,adjust_var_NEQ_1]
  \\ asm_exists_tac \\ fs []
  \\ fs [inter_insert,domain_lookup,
        lookup_3_adjust_set,lookup_1_adjust_set]
QED

Theorem state_rel_inc_clock:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ==>
    state_rel c l1 l2 (s with clock := s.clock + 1)
                      (t with clock := t.clock + 1) [] locs
Proof
  fs [state_rel_def] \\ fs [] \\ metis_tac []
QED

Theorem dec_clock_inc_clock:
   (dataSem$dec_clock (s with clock := s.clock + 1) = s) /\
    (wordSem$dec_clock (t with clock := t.clock + 1) = t)
Proof
  fs [dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
  \\ fs [dataSemTheory.state_component_equality]
  \\ fs [wordSemTheory.state_component_equality]
QED

Theorem word_gc_move_IMP_isWord:
   word_gc_move c' (Word c,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1) ==> isWord w1
Proof
  fs [word_gc_move_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ srw_tac[][] \\ fs [isWord_def]
QED

Theorem word_gen_gc_move_IMP_isWord:
   word_gen_gc_move c' (Word c,i,pa,ib,pb,old,m,dm) = (w1,i1,pa1,ib1,pb1,m1,c1) ==>
   isWord w1
Proof
  fs [word_gen_gc_move_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ srw_tac[][] \\ fs [isWord_def]
QED

Theorem word_gen_gc_partial_move_IMP_isWord:
   word_gen_gc_partial_move c' (Word c,i,pa,old,m,dm,gs,rs) = (w1,i1,pa1,m1,c1) ==>
   isWord w1
Proof
  full_simp_tac(srw_ss())[word_gen_gc_partial_move_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]
QED

Definition loc_ok_def[simp]:
  loc_ok (Loc m n) = (n = 0) ∧
  loc_ok _ = T
End

Theorem loc_ok_word_addr:
  loc_ok (word_addr c w)
Proof
  Cases_on ‘w’ \\ gvs [word_addr_def]
  \\ rename [‘Data a’] \\ Cases_on ‘a’
  \\ gvs [word_addr_def]
QED

Triviality word_gc_move_roots_IMP_FILTER0:
  ∀ws i pa old m dm ws2 i2 pa2 m2 c2 c.
    word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                         (FILTER isWord ws2,i2,pa2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gc_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gc_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]
QED

Triviality word_gen_gc_move_roots_IMP_FILTER0:
  ∀ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
    word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
                             (ws2,i2,pa2,ib2,pb2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gen_gc_move_roots c (FILTER isWord ws,i,pa,ib,pb,old,m,dm) =
                             (FILTER isWord ws2,i2,pa2,ib2,pb2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gen_gc_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gen_gc_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]
QED

Theorem word_gen_gc_partial_move_roots_IMP_FILTER:
  ∀ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
    word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
                                     (ws2,i2,pa2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gen_gc_partial_move_roots c (FILTER isWord ws,i,pa,old,m,dm,gs,rs) =
                                     (FILTER isWord ws2,i2,pa2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gen_gc_partial_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gen_gc_partial_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]
QED

val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``

Theorem word_gc_fun_IMP_FILTER:
  word_gc_fun c (xs,m,dm,s) = SOME (stack1,m1,s1) ∧
  EVERY loc_ok xs ⇒
  word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (FILTER isWord stack1,m1,s1)
Proof
  full_simp_tac(srw_ss())[word_gc_fun_def,LET_THM,word_gc_fun_def,
    word_full_gc_def,word_gen_gc_def,word_gen_gc_partial_def,
    word_gen_gc_partial_full_def]
  \\ TOP_CASE_TAC \\ fs []
  THEN1
   (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ drule_all word_gc_move_roots_IMP_FILTER0
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  \\ TOP_CASE_TAC \\ fs []
  THEN1
   (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac word_gen_gc_partial_move_roots_IMP_FILTER
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ fs [])
  THEN1
   (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ drule_all word_gen_gc_move_roots_IMP_FILTER0
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
QED

Definition loc_merge_def:
  (loc_merge [] ys = []) /\
  (loc_merge (Loc l1 l2::xs) ys = Loc l1 l2::loc_merge xs ys) /\
  (loc_merge (Word w::xs) (y::ys) = y::loc_merge xs ys) /\
  (loc_merge (Word w::xs) [] = Word w::xs)
End

Theorem LENGTH_loc_merge:
  ∀xs ys. LENGTH (loc_merge xs ys) = LENGTH xs
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[loc_merge_def]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[loc_merge_def]
  \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[loc_merge_def]
QED

Theorem word_gc_move_roots_IMP_FILTER:
   !ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                           (ws2,i2,pa2,m2,c2) ∧
      EVERY loc_ok ws ==>
      word_gc_move_roots c (ws,i,pa,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,loc_merge_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[isWord_def,loc_merge_def,LET_DEF]
  THEN1
   (full_simp_tac(srw_ss())[word_gc_move_def] \\ srw_tac[][]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ res_tac \\ fs [])
  \\ fs [word_gc_move_roots_def,loc_merge_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [] \\ rveq \\ fs [loc_merge_def]
QED

Theorem word_gen_gc_move_roots_IMP_FILTER:
   !ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
      word_gen_gc_move_roots c (FILTER isWord ws,i,pa,ib,pb,old,m,dm) =
        (ws2,i2,pa2,ib2,pb2,m2,c2) ∧
      EVERY loc_ok ws ==>
      word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,ib2,pb2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,loc_merge_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[isWord_def,loc_merge_def,LET_DEF]
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_move_def] \\ srw_tac[][]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ res_tac \\ fs [])
  \\ fs [word_gen_gc_move_roots_def,loc_merge_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [] \\ rveq \\ fs [loc_merge_def]
QED

Theorem word_gen_gc_partial_move_roots_IMP_FILTER[allow_rebind]:
   !ws i pa old m dm gs rs ws2 i2 pa2 m2 c2 c.
      word_gen_gc_partial_move_roots c (FILTER isWord ws,i,pa,old,m,dm,gs,rs) =
                                       (ws2,i2,pa2,m2,c2) ∧
      EVERY loc_ok ws ==>
      word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
                                       (loc_merge ws ws2,i2,pa2,m2,c2)
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,loc_merge_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[isWord_def,loc_merge_def,LET_DEF]
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_partial_move_def] \\ srw_tac[][]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ res_tac \\ fs [])
  \\ fs [word_gen_gc_partial_move_roots_def,loc_merge_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [] \\ rveq \\ fs [loc_merge_def]
QED

Theorem loc_merge_FILTER_isWord:
   !xs. loc_merge xs (FILTER isWord xs) = xs
Proof
  Induct \\ fs [loc_merge_def] \\ Cases \\ fs [loc_merge_def,isWord_def]
QED

Theorem word_gc_fun_loc_merge:
  word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (ys,m1,s1) ∧
  EVERY loc_ok xs ⇒
  word_gc_fun c (xs,m,dm,s) = SOME (loc_merge xs ys,m1,s1)
Proof
  fs [word_gc_fun_def,LET_THM,word_gc_fun_def,
     word_full_gc_def,word_gen_gc_def,word_gen_gc_partial_def,
     word_gen_gc_partial_full_def]
  \\ TOP_CASE_TAC \\ fs [loc_merge_FILTER_isWord]
  THEN1 (rw [] \\ fs [loc_merge_FILTER_isWord])
  THEN1
   (rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ rpt var_eq_tac \\ fs []
    \\ fs [word_gc_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rpt var_eq_tac \\ fs []
    \\ imp_res_tac word_gc_move_roots_IMP_FILTER
    \\ fs [] \\ srw_tac[][]
    \\ gvs [] \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  THEN1
   (rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ rpt var_eq_tac \\ fs []
    \\ fs [word_gen_gc_partial_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rpt var_eq_tac \\ fs []
    \\ imp_res_tac word_gen_gc_partial_move_roots_IMP_FILTER
    \\ fs [] \\ srw_tac[][]
    \\ gvs []
    \\ rveq \\ fs [])
  THEN1
   (rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ rpt var_eq_tac \\ fs []
    \\ fs [word_gen_gc_move_roots_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rpt var_eq_tac \\ fs []
    \\ imp_res_tac word_gen_gc_move_roots_IMP_FILTER
    \\ fs [] \\ srw_tac[][]
    \\ gvs [])
QED

Theorem word_gc_fun_IMP:
   word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) ==>
    FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
    FLOOKUP s1 Handler = FLOOKUP s Handler /\
    FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
    FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
    FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
    FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd /\
    FLOOKUP s1 (Temp 29w) = FLOOKUP s (Temp 29w) /\
    FLOOKUP s1 HeapLength = FLOOKUP s HeapLength /\
    Globals IN FDOM s1
Proof
  fs[IMP_EQ_DISJ,word_gc_fun_def] \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE]
  \\ TRY TOP_CASE_TAC \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE]
  \\ fs [word_gc_fun_assum_def]
QED

Theorem gc_fun_const_ok_word_gc_fun:
   gc_fun_const_ok (word_gc_fun c)
Proof
  fs [word_simpProofTheory.gc_fun_const_ok_def] \\ rw []
  \\ PairCases_on `x` \\ fs [] \\ PairCases_on `y` \\ fs []
  \\ imp_res_tac word_gc_IMP_EVERY2
  \\ pop_assum mp_tac
  \\ match_mp_tac LIST_REL_mono \\ fs []
QED

Theorem gc_fun_ok_word_gc_fun:
   gc_fun_ok (word_gc_fun c1)
Proof
  fs [gc_fun_ok_def] \\ rpt gen_tac \\ strip_tac
  \\ imp_res_tac word_gc_fun_LENGTH \\ fs []
  \\ imp_res_tac word_gc_fun_IMP
  \\ fs [FLOOKUP_DEF]
  \\ fs [word_gc_fun_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ rpt IF_CASES_TAC \\ fs []
  \\ fs [word_gen_gc_can_do_partial_def]
  \\ fs [DOMSUB_FAPPLY_THM] \\ rveq \\ fs []
  \\ fs [word_gc_fun_assum_def,DOMSUB_FAPPLY_THM]
  \\ fs [fmap_EXT,FUPDATE_LIST,EXTENSION]
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM] \\ rw [] \\ fs []
  \\ eq_tac \\ rw[] \\ fs []
  \\ metis_tac []
QED

Theorem word_gc_fun_APPEND_IMP:
   word_gc_fun c (xs ++ ys,m,dm,s) = SOME (zs,m1,s1) ==>
    ?zs1 zs2. zs = zs1 ++ zs2 /\ LENGTH xs = LENGTH zs1 /\ LENGTH ys = LENGTH zs2
Proof
  srw_tac[][] \\ imp_res_tac word_gc_fun_LENGTH \\ fs [LENGTH_APPEND]
  \\ pop_assum mp_tac \\ pop_assum (K all_tac)
  \\ qspec_tac (`zs`,`zs`) \\ qspec_tac (`ys`,`ys`) \\ qspec_tac (`xs`,`xs`)
  \\ Induct \\ fs [] \\ Cases_on `zs` \\ fs [LENGTH_NIL] \\ srw_tac[][]
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [LENGTH_NIL]
  \\ fs [ADD_CLAUSES] \\ res_tac
  \\ fs [] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ fs []
QED

Theorem IMP_loc_merge_APPEND[allow_rebind] = Q.prove(`
  !ts qs xs ys.
      LENGTH (FILTER isWord ts) = LENGTH qs ==>
      loc_merge (ts ++ xs) (qs ++ ys) = loc_merge ts qs ++ loc_merge xs ys`,
  Induct \\ fs [] THEN1 (fs [LENGTH,loc_merge_def])
  \\ Cases \\ fs [isWord_def,loc_merge_def]
  \\ Cases \\ fs [loc_merge_def]) |> SPEC_ALL

Theorem TAKE_DROP_loc_merge_APPEND:
  TAKE (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = loc_merge (MAP SND q) xs /\
  DROP (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = ys
Proof
  `LENGTH q = LENGTH (loc_merge (MAP SND q) xs)` by fs [LENGTH_loc_merge]
  \\ fs [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
QED

Theorem loc_merge_NIL:
  ∀xs. loc_merge xs [] = xs
Proof
  Induct \\ fs [loc_merge_def] \\ Cases \\ fs [loc_merge_def]
QED

Theorem loc_merge_APPEND:
   !xs1 xs2 ys.
      ?zs1 zs2. loc_merge (xs1 ++ xs2) ys = zs1 ++ zs2 /\
                LENGTH zs1 = LENGTH xs1 /\ LENGTH xs2 = LENGTH xs2 /\
                ?ts. loc_merge xs2 ts = zs2
Proof
  Induct \\ fs [loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] THEN1 (metis_tac [])
  \\ Cases THEN1
   (Cases_on `ys` \\ fs [loc_merge_def] \\ srw_tac[][]
    THEN1 (Q.LIST_EXISTS_TAC [`Word c::xs1`,`xs2`] \\ fs []
           \\ qexists_tac `[]` \\ fs [loc_merge_NIL])
    \\ pop_assum (qspecl_then [`xs2`,`t`] strip_assume_tac)
    \\ fs [] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ fs [] \\ metis_tac [])
  \\ srw_tac[][] \\ fs [loc_merge_def]
  \\ pop_assum (qspecl_then [`xs2`,`ys`] strip_assume_tac)
  \\ fs [] \\ Q.LIST_EXISTS_TAC [`Loc n n0::zs1`,`zs2`] \\ fs [] \\ metis_tac []
QED

Theorem EVERY2_loc_merge:
   !xs ys. EVERY2 (\x y. (isWord y ==> isWord x) /\
                          (~isWord x ==> x = y)) xs (loc_merge xs ys)
Proof
  Induct \\ fs [loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] \\ Cases
  \\ fs [loc_merge_def] \\ Cases_on `ys`
  \\ fs [loc_merge_def,GSYM EVERY2_refl,isWord_def]
QED

Theorem dec_stack_loc_merge_enc_stack:
   !xs ys. ?ss. dec_stack (loc_merge (enc_stack xs) ys) xs = SOME ss
Proof
  Induct
  \\ fs [wordSemTheory.enc_stack_def,loc_merge_def,wordSemTheory.dec_stack_def]
  \\ Cases \\ rename [‘StackFrame _ _ _ opt’] \\ Cases_on ‘opt’ \\ gvs []
  \\ TRY (PairCases_on `x`)
  \\ fs [wordSemTheory.enc_stack_def] \\ srw_tac[][]
  \\ qspecl_then [`MAP SND l0`,`enc_stack xs`,`ys`] mp_tac loc_merge_APPEND
  \\ srw_tac[][] \\ fs [] \\ fs [wordSemTheory.dec_stack_def]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ fs [DROP_LENGTH_APPEND]
  \\ first_assum (qspec_then `ts` strip_assume_tac) \\ fs []
  \\ decide_tac
QED

Theorem ALOOKUP_ZIP:
   !l zs1.
      ALOOKUP l (0:num) = SOME (Loc q r) /\
      LIST_REL (λx y. (isWord y ⇒ isWord x) ∧
        (¬isWord x ⇒ x = y)) (MAP SND l) zs1 ==>
      ALOOKUP (ZIP (MAP FST l,zs1)) 0 = SOME (Loc q r)
Proof
  Induct \\ fs [] \\ Cases \\ fs [ALOOKUP_def,PULL_EXISTS]
  \\ Cases_on `q' = 0` \\ fs [] \\ srw_tac[][] \\ fs [isWord_def] \\ srw_tac[][]
QED

Theorem stack_rel_dec_stack_IMP_stack_rel:
   !xs ys ts stack locs.
      LIST_REL stack_rel ts xs /\ LIST_REL contains_loc xs locs /\
      dec_stack (loc_merge (enc_stack xs) ys) xs = SOME stack ==>
      LIST_REL stack_rel ts stack /\ LIST_REL contains_loc stack locs
Proof
  Induct_on `ts` \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[]
  THEN1 (fs [wordSemTheory.enc_stack_def,loc_merge_def,wordSemTheory.dec_stack_def])
  \\ full_simp_tac(srw_ss())[PULL_EXISTS] \\ srw_tac[][]
  \\ Cases_on ‘h’ \\ rename [‘StackFrame opt l l0 xs’] \\ Cases_on ‘xs’
  \\ TRY (PairCases_on ‘x’) \\ gvs []
  \\ full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def,wordSemTheory.dec_stack_def]
  \\ qspecl_then [`MAP SND l0`,`enc_stack t`,`ys`] mp_tac loc_merge_APPEND
  \\ strip_tac \\ fs []
  \\ ‘DROP (LENGTH l0) (zs1 ++ zs2) = zs2 ∧
      TAKE (LENGTH l0) (zs1 ++ zs2) = zs1’ by
        metis_tac [DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND]
  \\ fs [] \\ ntac 2 $ pop_assum kall_tac \\ gvs []
  \\ gvs [CaseEq "option"]
  \\ last_x_assum drule_all \\ strip_tac \\ fs []
  \\ PairCases_on ‘y’
  \\ gvs [contains_loc_def]
  \\ rename [‘stack_rel hh’] \\ Cases_on ‘hh’
  \\ gvs [stack_rel_def,MAP_ZIP,lookup_fromAList,IS_SOME_ALOOKUP_EQ]
  \\ gvs [EVERY_EL,EL_ZIP,EL_MAP]
  \\ gen_tac \\ disch_tac
  \\ last_x_assum drule
  \\ pairarg_tac \\ gvs []
QED

Theorem join_env_NIL:
   join_env s [] = []
Proof
  full_simp_tac(srw_ss())[join_env_def]
QED

Theorem join_env_CONS:
   join_env s ((n,v)::xs) =
    if n <> 0 /\ EVEN n then
      (THE (lookup ((n - 2) DIV 2) s),v)::join_env s xs
    else join_env s xs
Proof
  full_simp_tac(srw_ss())[join_env_def] \\ srw_tac[][]
QED

Theorem FILTER_enc_stack_lemma:
   !xs ys.
      LIST_REL stack_rel xs ys ==>
      FILTER isWord (MAP SND (flat xs ys)) =
      FILTER isWord (enc_stack ys)
Proof
  Induct \\ Cases_on `ys`
  \\ fs [stack_rel_def,wordSemTheory.enc_stack_def,flat_def]
  \\ Cases \\ Cases_on `h` \\ fs [] \\ Cases_on `o0`
  \\ TRY (PairCases_on `x`) \\ fs [stack_rel_def] \\ srw_tac[][]
  \\ fs [wordSemTheory.enc_stack_def,flat_def,FILTER_APPEND]
  \\ qpat_x_assum `EVERY (\(x1,x2). x1 <> 0 /\ EVEN x1) l0` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ Induct_on `l0` \\ fs [] \\ fs [join_env_NIL]
  \\ Cases \\ fs [join_env_CONS] \\ srw_tac[][]
QED

Theorem stack_rel_simp:
    (stack_rel (Env i s) y <=>
     ?rets vs. stack_rel (Env i s) y /\ (y = StackFrame i rets vs NONE)) /\
    (stack_rel (Exc i s n) y <=>
     ?rets vs x1 x2 x3. stack_rel (Exc i s n) y /\ (y = StackFrame i rets vs (SOME (x1,x2,x3))))
Proof
  Cases_on `y` \\ fs [stack_rel_def] \\ Cases_on `o0`
  \\ fs [stack_rel_def]
  THEN1 metis_tac []
  \\ PairCases_on `x`
  \\ fs [stack_rel_def,CONJ_ASSOC]
  \\ metis_tac []
QED

Theorem join_env_EQ_ZIP:
   !vs s zs1.
      EVERY (\(x1,x2). x1 <> 0 /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 /\
      LIST_REL (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
         (MAP SND (join_env s vs)) zs1 ==>
      join_env s
        (ZIP (MAP FST vs,loc_merge (MAP SND vs) (FILTER isWord zs1))) =
      ZIP (MAP FST (join_env s vs),zs1)
Proof
  Induct \\ simp [join_env_NIL,loc_merge_def] \\ rpt strip_tac
  \\ Cases_on `h` \\ simp [] \\ fs []
  \\ Cases_on `r` \\ fs [isWord_def]
  \\ fs [loc_merge_def] \\ fs [join_env_CONS] \\ gvs [] \\ srw_tac[][]
  \\ fs [] \\ srw_tac[][] \\ gvs [isWord_def] \\ fs []
  \\ Cases_on `y` \\ fs [loc_merge_def,join_env_CONS,isWord_def]
QED

Theorem LENGTH_MAP_SND_join_env_IMP:
   !vs zs1 s.
      LIST_REL (\x y. (isWord x = isWord y) /\ (~isWord x ==> x = y))
        (MAP SND (join_env s vs)) zs1 /\
      EVERY (\(x1,x2). x1 <> 0 /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 ==>
      LENGTH (FILTER isWord (MAP SND vs)) = LENGTH (FILTER isWord zs1)
Proof
  Induct \\ rpt strip_tac THEN1
   (pop_assum mp_tac \\ simp [join_env_NIL]
    \\ Cases_on `zs1` \\ fs [] \\ srw_tac[][])
  \\ Cases_on `h` \\ fs [join_env_CONS] \\ srw_tac[][]
  THEN1 (fs [] \\ gvs [] \\ first_assum match_mp_tac \\ metis_tac[])
  \\ fs [] \\ Cases_on `q <> 0 /\ EVEN q`
  \\ fs [] \\ srw_tac[][] \\ fs [] \\ metis_tac []
QED

Theorem lemma1:
  (y1 = y2) /\ (x1 = x2) ==> (f x1 y1 = f x2 y2)
Proof
  full_simp_tac(srw_ss())[]
QED

Theorem word_gc_fun_EL_lemma[allow_rebind] = Q.prove(`
  !xs ys stack1 m dm st m1 s1 stack.
      LIST_REL stack_rel xs stack /\
      EVERY2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
         (MAP SND (flat xs ys)) stack1 /\
      dec_stack (loc_merge (enc_stack ys) (FILTER isWord stack1)) ys =
        SOME stack /\ LIST_REL stack_rel xs ys ==>
      (flat xs stack =
       ZIP (MAP FST (flat xs ys),stack1))`,
  Induct THEN1 (EVAL_TAC \\ fs [] \\ EVAL_TAC \\ srw_tac[][] \\ srw_tac[][flat_def])
  \\ Cases_on `h` \\ fs [] \\ once_rewrite_tac [stack_rel_simp]
  \\ fs [PULL_EXISTS,stack_rel_def,flat_def,wordSemTheory.enc_stack_def]
  \\ srw_tac[][] \\ imp_res_tac EVERY2_APPEND_IMP \\ srw_tac[][]
  \\ fs [FILTER_APPEND]
  \\ `LENGTH (FILTER isWord (MAP SND vs')) = LENGTH (FILTER isWord zs1)` by
   (imp_res_tac EVERY2_LENGTH \\ fs []
    \\ imp_res_tac LENGTH_MAP_SND_join_env_IMP)
  \\ imp_res_tac IMP_loc_merge_APPEND \\ fs []
  \\ qpat_x_assum `dec_stack xx dd = SOME yy` mp_tac
  \\ fs [wordSemTheory.dec_stack_def]
  \\ fs [TAKE_DROP_loc_merge_APPEND,LENGTH_loc_merge,DECIDE ``~(n+m<n:num)``]
  \\ CASE_TAC \\ srw_tac[][] \\ fs []
  \\ fs [flat_def] \\ imp_res_tac EVERY2_LENGTH \\ fs [GSYM ZIP_APPEND]
  \\ match_mp_tac lemma1
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac \\ fs [])
  \\ TRY (match_mp_tac join_env_EQ_ZIP) \\ fs []) |> SPEC_ALL

Theorem word_ml_inv_cons_snoc:
  word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (x::xs) ⇒
  word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (xs ++ [x])
Proof
  match_mp_tac word_ml_inv_rearrange
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem size_of_cons:
  size_of lims (x::xs) refs seen =
    let (n1,refs1,seen1) = size_of lims xs refs seen in
    let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
      (n1 + n2,refs2,seen2)
Proof
  Cases_on `xs` \\ fs [size_of_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
QED

Theorem size_of_global_to_vs:
  !xs. size_of lims (xs ++ global_to_vs x) refs seen =
       size_of lims (xs ++ [the_global x]) refs seen
Proof
  Induct \\ fs []
  THEN1 (Cases_on `x` \\ fs [the_global_def,global_to_vs_def] \\ EVAL_TAC)
  \\ once_rewrite_tac [size_of_cons] \\ fs []
QED

Theorem toListA_mk:
  toListA a (mk_BN t1 t2) = toListA a (BN t1 t2) /\
  toListA a (mk_BS t1 x t2) = toListA a (BS t1 x t2)
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ rw [mk_BS_def,mk_BN_def]
  \\ fs [toListA_def]
QED

Theorem PERM_toList_delete:
  !k s x.
    lookup k s = SOME x ==>
    PERM (toList s) (x :: toList (delete k s))
Proof
  ho_match_mp_tac lookup_ind
  \\ fs [lookup_def] \\ rw []
  THEN1 (EVAL_TAC \\ fs [])
  \\ fs [delete_def]
  \\ fs [toList_def,toListA_def,toListA_mk]
  \\ once_rewrite_tac [sptreeTheory.toListA_append] \\ fs []
  THEN1
   (once_rewrite_tac [GSYM APPEND]
    \\ rewrite_tac [CONJUNCT1 APPEND]
    \\ match_mp_tac PERM_CONG \\ fs [])
  THEN1
   (match_mp_tac PERM_TRANS
    \\ qexists_tac `toListA [] t1 ++ x::toListA [] (delete ((k - 1) DIV 2) t2)`
    \\ conj_tac THEN1 (match_mp_tac PERM_CONG \\ fs [])
    \\ once_rewrite_tac [PERM_SYM]
    \\ fs [sortingTheory.PERM_TO_APPEND_SIMPS])
  THEN1
   (once_rewrite_tac [PERM_SYM]
    \\ fs [sortingTheory.PERM_TO_APPEND_SIMPS])
  THEN1
   (once_rewrite_tac [GSYM APPEND]
    \\ rewrite_tac [CONJUNCT1 APPEND]
    \\ match_mp_tac PERM_CONG \\ fs [])
  \\ match_mp_tac PERM_TRANS
  \\ qexists_tac `toListA [] t1 ++ a::x::toListA [] (delete ((k - 1) DIV 2) t2)`
  \\ conj_tac THEN1 (match_mp_tac PERM_CONG \\ fs [])
  \\ once_rewrite_tac [PERM_SYM]
  \\ fs [sortingTheory.PERM_TO_APPEND_SIMPS]
  \\ fs [sortingTheory.PERM_CONS_EQ_APPEND]
  \\ qexists_tac `toListA [] t1 ++ [a]`
  \\ qexists_tac `toListA [] (delete ((k - 1) DIV 2) t2)`
  \\ fs [] \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND] \\ fs []
QED

Theorem PERM_lookup_toList_lemma:
  !l s.
    (∀n. IS_SOME (lookup n s) ⇔ IS_SOME (ALOOKUP l (adjust_var n))) /\
    ALL_DISTINCT (MAP FST l) ==>
    PERM (MAP FST
       (MAP (λ(n,v). (THE (lookup ((n - 2) DIV 2) s),v))
          (FILTER (λ(n,v). n ≠ 0 ∧ EVEN n) l))) (toList s)
Proof
  rw [] \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac `s`
  \\ qid_spec_tac `l`
  \\ Induct \\ fs []
  THEN1
   (CCONTR_TAC \\ fs []
    \\ Cases_on `toList s` \\ fs []
    \\ `MEM h (toList s)` by fs []
    \\ imp_res_tac MEM_toList \\ rfs [])
  \\ fs [FORALL_PROD]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC
  THEN1
   (fs [AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ fs [] \\ rw [] \\ fs [EVEN_adjust_var])
  \\ fs []
  \\ imp_res_tac IMP_adjust_var
  \\ first_assum (qspec_then `(p_1 - 2) DIV 2` mp_tac)
  \\ pop_assum mp_tac
  \\ simp_tac std_ss []
  \\ qmatch_goalsub_abbrev_tac `adjust_var k`
  \\ disch_then kall_tac
  \\ simp_tac std_ss [IS_SOME_EXISTS]
  \\ strip_tac \\ fs []
  \\ drule PERM_toList_delete \\ strip_tac
  \\ match_mp_tac PERM_TRANS
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once PERM_SYM]
  \\ asm_exists_tac \\ fs []
  \\ last_x_assum (qspec_then `delete k s` mp_tac)
  \\ impl_tac THEN1
   (fs [lookup_delete] \\ strip_tac \\ IF_CASES_TAC
    THEN1 (fs [Abbr `k`,IMP_adjust_var,ALOOKUP_NONE])
    \\ fs [] \\ rw [] \\ fs [adjust_var_DIV_2,Abbr`k`])
  \\ qmatch_goalsub_abbrev_tac `PERM xs1 _ ==> PERM xs2 _`
  \\ qsuff_tac `xs1 = xs2` \\ fs []
  \\ unabbrev_all_tac
  \\ fs [lookup_delete]
  \\ qpat_x_assum `~(MEM _ _)` mp_tac
  \\ qid_spec_tac `l`
  \\ Induct \\ fs [FORALL_PROD] \\ rw[]
  \\ rw [] \\ qsuff_tac `F` \\ fs []
  \\ imp_res_tac IMP_adjust_var
  \\ qpat_x_assum `p_1 ≠ p_1'` mp_tac \\ fs []
  \\ metis_tac [adjust_var_11]
QED

Theorem flat_PERM_extract_stack:
  !xs ys.
    LIST_REL stack_rel xs ys ==>
    PERM (MAP FST (flat xs ys)) (FLAT (MAP extract_stack xs))
Proof
  Induct \\ Cases_on `ys` \\ fs [flat_def]
  \\ Cases \\ Cases_on `h` \\ fs [stack_rel_def]
  \\ rename [`StackFrame opt _ _ opt2`]
  \\ Cases_on `opt` \\ Cases_on `opt2` \\ fs [stack_rel_def]
  \\ TRY (rename [`StackFrame _ _ _ (SOME xx)`] \\ PairCases_on `xx`
          \\ rename [`Exc opt`] \\ Cases_on `opt` \\ fs [stack_rel_def] \\ rveq)
  \\ rw [] \\  res_tac \\ fs [flat_def]
  \\ match_mp_tac sortingTheory.PERM_CONG \\ fs []
  \\ fs [extract_stack_def,join_env_def]
  \\ fs [lookup_fromAList]
  \\ match_mp_tac PERM_lookup_toList_lemma \\ fs []
QED

Theorem ALL_DISTINCT_data_pointers:
  !heap. ALL_DISTINCT (data_pointers heap)
Proof
  Induct \\ fs [data_pointers_def]
  \\ Cases \\ fs [data_pointers_def] \\ rw []
  \\ fs [MEM_MAP]
  \\ match_mp_tac ALL_DISTINCT_MAP_INJ \\ fs []
QED

Theorem SUM_MAP_lookup_len_LESS_EQ:
  !p1 p2.
    set p1 SUBSET set p2 /\ ALL_DISTINCT p1 ==>
    SUM (MAP (lookup_len heap) p1) <= SUM (MAP (lookup_len heap) p2)
Proof
  Induct \\ fs [] \\ rw []
  \\ qpat_x_assum `MEM _ _` mp_tac
  \\ simp [MEM_SPLIT]
  \\ strip_tac \\ rveq
  \\ fs [MAP_APPEND,SUM_APPEND]
  \\ `set p1 SUBSET set (l1 ++ l2)` by (fs [SUBSET_DEF,MEM_APPEND] \\ metis_tac [])
  \\ res_tac \\ fs [SUM_APPEND]
QED

Theorem set_data_pointers:
  set (data_pointers heap) = {a | isSomeDataElement (heap_lookup a heap)}
Proof
  qid_spec_tac `heap` >>
  ho_match_mp_tac data_pointers_ind >>
  rw[data_pointers_def,heap_lookup_def,isSomeDataElement_def,LIST_TO_SET_MAP,el_length_def] >>
  rw[FUN_EQ_THM] >> rw[EQ_IMP_THM] >>
  fs[] >>
  fs[PULL_EXISTS] >>
  PURE_ONCE_REWRITE_TAC[CONJ_SYM] >> goal_assum drule >> rw[]
QED

Inductive traverse_heap:
  (!heap p1.
     traverse_heap heap p1 [] p1) /\
  (!heap vs1 vs2 vars p1 p2 p3.
     traverse_heap heap p1 vs1 p2 /\
     traverse_heap heap p2 vs2 p3 /\
     set vars = set (vs1 ++ vs2) ==>
     traverse_heap heap p1 vars p3) /\
  (!heap p1 d.
     traverse_heap heap p1 [Data d] p1) /\
  (!heap p1 n t.
     MEM n p1 ==>
     traverse_heap heap p1 [Pointer n t] p1) /\
  (!heap p1 n t p2 xs l d.
     heap_lookup n heap = SOME (DataElement xs l d) /\
     traverse_heap heap (n::p1) xs p2 ==>
     traverse_heap heap p1 [Pointer n t] p2)
End

Triviality size_of_Block:
  size_of lims [Block ts tag vs] refs seen =
  if vs = [] \/ IS_SOME (lookup ts seen) then (0,refs,seen)
  else let (n,refs',seen') = size_of lims vs refs (insert ts () seen)
       in (n + LENGTH vs + 1,refs',seen')
Proof
  Cases_on `vs` \\ fs [size_of_def]
QED

Theorem LENGTH_n2mw_LE_bignum_digits:
  !n m.
    good_dimindex (:'a) /\ n <= m ==>
    LENGTH ((n2mw n) :'a word list) <= bignum_digits (dimindex (:α) = 64) m
Proof
  ho_match_mp_tac multiwordTheory.n2mw_ind \\ rw []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ rw [] \\ fs []
  \\ once_rewrite_tac [bignum_digits_def] \\ fs [ADD1]
  \\ first_x_assum match_mp_tac
  \\ match_mp_tac LESS_EQ_TRANS
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac `m DIV a1`
  \\ qexists_tac `n DIV a1` \\ qunabbrev_tac `a1`
  \\ (conj_tac
      THEN1 (match_mp_tac multiwordTheory.DIV_thm1 \\ fs [good_dimindex_def,dimword_def])
      \\ match_mp_tac arithmeticTheory.DIV_LE_MONOTONE \\ fs [])
QED

Theorem soundness_size_of:
  !lims roots r1 s1 root_vars
   (vars:'a word_loc heap_address list) n2 r2 s2 p1 refs.
    (∀n. reachable_refs root_vars refs n ⇒
         bc_ref_inv c n refs (f,tf,heap,be)) /\
    LIST_REL (λv x. v_inv c v (x,f,tf,heap)) root_vars vars /\
    PERM roots root_vars /\ good_dimindex (:'a) /\
    IMAGE ($' tf) (domain s1) SUBSET set p1 /\
    IMAGE ($' f) (domain refs DIFF domain r1) SUBSET set p1 /\
    FDOM f SUBSET domain refs /\ subspt r1 refs /\
    (lims.arch_64_bit ⇔ dimindex (:α) = 64) /\
    size_of lims roots r1 s1 = (n2,r2,s2) ==>
    ?p2. SUM (MAP (lookup_len heap) p2) <= n2 + SUM (MAP (lookup_len heap) p1) /\
         traverse_heap heap p1 vars p2 /\ subspt r2 refs /\
         IMAGE ($' tf) (domain s2) SUBSET set p2 /\
         IMAGE ($' f) (domain refs DIFF domain r2) SUBSET set p2
Proof
  ho_match_mp_tac size_of_ind \\ rw []
  THEN1 (fs [size_of_def] \\ rveq \\ simp [Once traverse_heap_cases]
         \\ qexists_tac `p1` \\ fs [])
  THEN1
   (pop_assum mp_tac
    \\ simp [size_of_def]
    \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq
    \\ qpat_x_assum `PERM _ _` mp_tac
    \\ once_rewrite_tac [sortingTheory.PERM_CONS_EQ_APPEND]
    \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
    \\ imp_res_tac data_to_word_memoryProofTheory.EVERY2_APPEND_CONS
    \\ fs [] \\ rveq \\ fs []
    \\ last_x_assum assume_tac
    \\ last_x_assum (qspecl_then [`M++N`,`t1++t2`,`p1`,`refs`] mp_tac)
    \\ impl_tac THEN1
     (simp [] \\ rw []
      THEN1 (last_x_assum match_mp_tac
        \\ fs [reachable_refs_def,EXTENSION] \\ metis_tac [])
     \\ metis_tac [LIST_REL_APPEND,LIST_REL_LENGTH])
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`p2`,`refs`,`t`] mp_tac)
    \\ impl_tac THEN1
     (simp [] \\ rw [] \\ last_x_assum match_mp_tac
      \\ fs [reachable_refs_def,EXTENSION] \\ metis_tac [])
    \\ strip_tac
    \\ qexists_tac `p2'` \\ fs []
    \\ match_mp_tac (CONJUNCT2 traverse_heap_rules |> CONJUNCT1)
    \\ asm_exists_tac \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ fs [EXTENSION] \\ metis_tac [])
  THEN1 (* Word case *)
   (fs [size_of_def] \\ rveq
    \\ fs [v_inv_def] \\ rveq \\ fs [Word64Rep_def]
    \\ every_case_tac \\ fs []
    \\ qexists_tac `ptr :: p1`
    \\ fs [lookup_len_def,el_length_def]
    \\ fs [SUBSET_DEF]
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs [])
  THEN1 (* Number case *)
   (fs [] \\ rveq \\ fs [] \\ fs [v_inv_def]
    \\ Cases_on `small_int (:α) i` \\ fs [] \\ rveq \\ fs []
    THEN1
     (qexists_tac `p1` \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
      \\ fs [size_of_def])
    \\ fs [size_of_def] \\ rveq \\ fs [Bignum_def,multiwordTheory.i2mw_def]
    \\ IF_CASES_TAC THEN1
     (qsuff_tac `F` \\ fs [] \\ fs [small_num_def,small_int_def,dimword_def]
      \\ rfs [good_dimindex_def] \\ rfs [] \\ intLib.COOPER_TAC)
    \\ qexists_tac `ptr :: p1` \\ fs []
    \\ fs [lookup_len_def,el_length_def,bignum_size_def,
           LENGTH_n2mw_LE_bignum_digits]
    \\ fs [SUBSET_DEF]
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs [])
  THEN1 (* CodePtr case *)
   (fs [size_of_def] \\ rveq
    \\ fs [v_inv_def] \\ rveq \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
    \\ qexists_tac `p1` \\ fs [])
  THEN1 (* RefPtr case *)
   (fs [size_of_def] \\ rveq
    \\ fs [v_inv_def] \\ rveq \\ fs [CaseEq"option"] \\ rveq \\ fs []
    THEN1
     (qexists_tac `p1` \\ fs [] \\ qsuff_tac `MEM (f ' r) p1`
      THEN1 (once_rewrite_tac [traverse_heap_cases]\\ fs [])
      \\ fs [SUBSET_DEF] \\ first_x_assum match_mp_tac
      \\ qexists_tac `r` \\ fs [] \\ fs [domain_lookup])
    \\ reverse (Cases_on `v`) \\ fs []
    THEN1
     (rveq \\ fs [] \\ fs []
      \\ first_x_assum (qspec_then `r` mp_tac)
      \\ (impl_tac THEN1 fs [reachable_refs_def,get_refs_def])
      \\ fs [bc_ref_inv_def,FLOOKUP_DEF]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ strip_tac
      \\ fs [lookup_delete]
      \\ qexists_tac `f ' r :: p1` \\ fs []
      \\ fs [lookup_len_def,Bytes_def,el_length_def]
      \\ conj_tac THEN1
       (match_mp_tac multiwordTheory.DIV_thm1 \\ fs [good_dimindex_def,arch_size_def])
      \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
      \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
      \\ fs [SUBSET_DEF,PULL_EXISTS] \\ metis_tac [])
    \\ pop_assum mp_tac
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ first_assum (qspec_then `r` mp_tac)
    \\ (impl_tac THEN1 fs [reachable_refs_def,get_refs_def])
    \\ rewrite_tac [bc_ref_inv_def]
    \\ fs [subspt_lookup]
    \\ first_assum drule \\ strip_tac \\ fs []
    \\ fs [FLOOKUP_DEF,RefBlock_def]
    \\ strip_tac
    \\ rename [`LIST_REL _ l1 l2`]
    \\ first_x_assum (qspecl_then [`l2`,`l1`,`f ' r :: p1`,`refs`] mp_tac)
    \\ impl_tac THEN1
     (fs [] \\ drule EVERY2_SWAP \\ fs [lookup_delete,SUBSET_DEF,PULL_EXISTS]
      \\ rw [] \\ fs [] \\ first_x_assum match_mp_tac
      \\ fs [reachable_refs_def,get_refs_def]
      \\ once_rewrite_tac [RTC_CASES1] \\ disj2_tac
      \\ rename [`RTC _ r5 r6`] \\ qexists_tac `r5` \\ fs []
      \\ simp [ref_edge_def,get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
      \\ asm_exists_tac \\ fs [])
    \\ strip_tac \\ qexists_tac `p2` \\ fs []
    \\ rfs [lookup_len_def,el_length_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases]
    \\ rpt disj2_tac \\ fs [])
  THEN1 (* empty Block *)
   (fs [size_of_def] \\ rveq
    \\ fs [v_inv_def] \\ rveq \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases] \\ fs []
    \\ qexists_tac `p1` \\ fs [])
  (* rest is non-empty Block *)
  \\ rename [‘size_of lims [Block ts tag (z0::zs0)]’]
  \\ qmatch_asmsub_abbrev_tac `Block _ _ payload`
  \\ `z0 INSERT set zs0 = set payload /\ payload <> []` by fs [Abbr`payload`]
  \\ fs []
  \\ qpat_x_assum `size_of _ _ _ _ = _` mp_tac
  \\ fs [size_of_Block]
  \\ IF_CASES_TAC
  THEN1
   (strip_tac \\ fs [] \\ rveq \\ fs []
    \\ qexists_tac `p1` \\ fs []
    \\ fs [v_inv_def] \\ rveq \\ fs []
    \\ fs [FLOOKUP_DEF] \\ rveq \\ fs []
    \\ once_rewrite_tac [traverse_heap_cases]
    \\ qsuff_tac `MEM (tf ' ts) p1` \\ fs []
    \\ fs [SUBSET_DEF,PULL_EXISTS]
    \\ first_x_assum match_mp_tac
    \\ fs [domain_lookup,IS_SOME_EXISTS])
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ fs [v_inv_def] \\ rveq \\ fs []
  \\ fs [BlockRep_def]
  \\ first_x_assum (qspecl_then [`payload`,`xs`,`tf ' ts :: p1`,`refs`] mp_tac)
  \\ impl_tac THEN1
   (fs [] \\ reverse conj_tac THEN1 fs [SUBSET_DEF]
    \\ rw [] \\ first_x_assum match_mp_tac
    \\ fs [reachable_refs_def,get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
    \\ asm_exists_tac \\ fs []
    \\ asm_exists_tac \\ fs [])
  \\ strip_tac
  \\ rfs [FLOOKUP_DEF] \\ rveq \\ fs []
  \\ fs [lookup_len_def] \\ rfs [el_length_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [] \\ qexists_tac `p2` \\ simp []
  \\ once_rewrite_tac [traverse_heap_cases]
  \\ ntac 3 (disj2_tac)
  \\ simp []
QED

Theorem traverse_heap_reachable_set_mono:
  !heap1 ps vars ps2. traverse_heap heap1 ps vars ps2 ==>
  set ps SUBSET set ps2
Proof
  ho_match_mp_tac traverse_heap_ind \\ rw []
  \\ metis_tac [SUBSET_TRANS]
QED

Theorem traverse_heap_reachable_aux_vars_gc_edge:
  !heap ps vars ps2. traverse_heap heap ps vars ps2 ==>
  !vars2.
  (!y z. MEM y ps /\ gc_edge heap y z ==>
     MEM z ps \/ (?t. MEM (Pointer z t) (vars ++ vars2))) ==>
  (set ps SUBSET set ps2) /\
  (!y t. MEM (Pointer y t) vars ==>
     MEM y ps2 \/ (?t. MEM (Pointer y t) vars2)) /\
  (!y z. MEM y ps2 /\ gc_edge heap y z ==>
     MEM z ps2 \/ (?t. MEM (Pointer z t) vars2))
Proof
  ho_match_mp_tac traverse_heap_ind \\ simp []
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  >- (
    fs []
    \\ last_x_assum (qspec_then `vars' ++ vars2` mp_tac)
    \\ simp []
    \\ impl_tac >- metis_tac []
    \\ disch_tac
    \\ last_x_assum (qspec_then `vars2` mp_tac)
    \\ impl_tac
    \\ fs [SUBSET_DEF]
    \\ metis_tac []
  )
  >- metis_tac []
  >- (
    fs []
    \\ last_x_assum (qspec_then `vars2` mp_tac)
    \\ fs [gc_edge_def]
    \\ impl_tac
    \\ rw [] \\ rfs []
    \\ metis_tac []
  )
QED

Theorem traverse_heap_reachable_RTC_gc_edge:
  traverse_heap heap [] vars ps2 ==>
  (!p x. RTC (gc_edge heap) p x ==> MEM p ps2 ==> MEM x ps2)
Proof
  disch_tac
  \\ ho_match_mp_tac RTC_INDUCT
  \\ drule traverse_heap_reachable_aux_vars_gc_edge
  \\ disch_then (qspec_then `[]` mp_tac)
  \\ simp []
  \\ metis_tac []
QED

Theorem traverse_heap_reachable:
  traverse_heap heap1 [] vars p2 /\
  reachable_addresses vars heap1 x ==> MEM x p2
Proof
  rw [reachable_addresses_def]
  \\ drule traverse_heap_reachable_aux_vars_gc_edge
  \\ disch_then (qspec_then `[]` mp_tac)
  \\ drule traverse_heap_reachable_RTC_gc_edge
  \\ simp []
  \\ metis_tac []
QED

Triviality stack_rel_imp_subset:
  ∀xs ys.
    LIST_REL stack_rel xs ys ⇒
    set (enc_stack ys) ⊆ set (MAP SND (flat xs ys))
Proof
  Induct \\ gvs [wordSemTheory.enc_stack_def,PULL_EXISTS]
  \\ Cases \\ Cases_on ‘y’ \\ gvs [stack_rel_def]
  \\ rw [] \\ rename [‘StackFrame opt l1 l2 han’]
  \\ Cases_on ‘han’ \\ TRY (PairCases_on ‘x’)
  \\ gvs [wordSemTheory.enc_stack_def,flat_def,stack_rel_def]
  \\ last_x_assum drule \\ strip_tac \\ gvs []
  \\ (qsuff_tac ‘set (MAP SND l2) ⊆ set (MAP SND (join_env s l2))’
      >- gvs [SUBSET_DEF])
  \\ gvs [SUBSET_DEF,join_env_def,MAP_MAP_o,o_DEF]
  \\ gvs [LAMBDA_PROD]
  \\ gvs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
  \\ gvs [MEM_FILTER] \\ metis_tac []
QED

Theorem state_rel_gc:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ==>
    FLOOKUP t.store AllocSize = SOME (Word (alloc_size k)) /\
    s.locals = LN /\
    t.locals = LS (Loc l1 l2) ==>
    ?t2 wl m st w1 w2 stack.
      t.gc_fun (enc_stack t.stack,t.memory,t.mdomain,t.store) =
        SOME (wl,m,st) /\
      dec_stack wl t.stack = SOME stack /\
      FLOOKUP st (Temp 29w) = FLOOKUP t.store (Temp 29w) /\
      FLOOKUP st AllocSize = SOME (Word (alloc_size k)) /\
      (has_space (Word ((alloc_size k):'a word)) (t with <|store := st |>) = SOME F /\
       c.gc_kind <> None ==>
         s.limits.heap_limit < size_of_heap s + k) /\
      state_rel c l1 l2 (s with space := 0)
        (t with <|stack := stack; store := st; memory := m|>) [] locs
Proof
  full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][]
  \\ ‘EVERY loc_ok (MAP SND (flat s.stack t.stack)) ∧
      EVERY loc_ok (enc_stack t.stack)’ by
    (‘word_ml_inv (heap,t.be,a,sp,sp1,gens) limit (THE s.tstamps) c s.refs
      (flat s.stack t.stack)’ by
        (first_x_assum (fn th => mp_tac th \\ match_mp_tac word_ml_inv_rearrange)
         \\ gvs [])
     \\ pop_assum mp_tac
     \\ simp [word_ml_inv_def]
     \\ strip_tac \\ gvs []
     \\ conj_asm1_tac
     >- (gvs [LIST_REL_EL_EQN,EVERY_EL]
         \\ rw [] \\ first_x_assum drule
         \\ disch_then (fn th => simp [GSYM th])
         \\ simp [loc_ok_word_addr])
     \\ qsuff_tac ‘set (enc_stack t.stack) ⊆ set (MAP SND (flat s.stack t.stack))’
     >- gvs [EVERY_MEM,SUBSET_DEF]
     \\ irule stack_rel_imp_subset \\ gvs [])
  \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[lookup_def] \\ srw_tac[][]
  \\ qhdtm_x_assum `word_ml_inv` mp_tac
  \\ Q.PAT_ABBREV_TAC `pat = join_env LN _` \\ srw_tac[][]
  \\ `pat = []` by (UNABBREV_ALL_TAC \\ EVAL_TAC) \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (K all_tac)
  \\ first_assum (fn th1 =>
       first_x_assum (fn th2 =>
         first_x_assum (fn th3 =>
             mp_tac (MATCH_MP word_gc_fun_correct (CONJ th1 (CONJ th2 th3 ))))))
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ drule_all word_gc_fun_IMP_FILTER
  \\ strip_tac
  \\ imp_res_tac FILTER_enc_stack_lemma \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_fun_loc_merge \\ full_simp_tac(srw_ss())[FILTER_APPEND]
  \\ imp_res_tac word_gc_fun_IMP \\ full_simp_tac(srw_ss())[]
  \\ `?stack. dec_stack (loc_merge (enc_stack t.stack) (FILTER isWord stack1))
        t.stack = SOME stack` by metis_tac [dec_stack_loc_merge_enc_stack]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac stack_rel_dec_stack_IMP_stack_rel \\ full_simp_tac(srw_ss())[]
  \\ `flat s.stack stack = ZIP (MAP FST (flat s.stack t.stack),stack1)` by
   (match_mp_tac (GEN_ALL word_gc_fun_EL_lemma)
    \\ imp_res_tac word_gc_IMP_EVERY2
    \\ full_simp_tac(srw_ss())[]
    \\ pop_assum mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ fs [] \\ Cases \\ fs []
    \\ fs [word_simpProofTheory.is_gc_word_const_def,isWord_def])
  \\ pop_assum (assume_tac o GSYM)
  \\ reverse conj_tac THEN1
   (fs [code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ imp_res_tac stack_rel_IMP_size_of_stack \\ fs []
    \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
    \\ `word_ml_inv (heap1,t.be,a1,sp1,sp2,gens2) limit (THE s.tstamps) c
            s.refs ((the_global s.global, s1 ' Globals) ::
                    ZIP (MAP FST (flat s.stack t.stack),stack1))` by
      (fs [word_ml_inv_def] \\ asm_exists_tac \\ fs [])
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][])
  \\ Cases_on `c.gc_kind = Simple` \\ fs []
  THEN1
   (fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def]
    \\ strip_tac \\ fs []
    \\ rename [`c.gc_kind = Simple`] (* only one case left *)
    \\ fs [option_case_eq,CaseEq"word_loc"] \\ rveq \\ fs []
    \\ `s.limits.arch_64_bit ⇔ dimindex (:α) = 64` by
     (fs[limits_inv_def])
    \\ `s.limits.heap_limit = limit` by
     (fs [limits_inv_def,heap_in_memory_store_def]
      \\ rpt (qpat_x_assum `FLOOKUP t.store HeapLength = _` mp_tac)
      \\ fs [] \\ fs [heap_ok_def,word_ml_inv_def,abs_ml_inv_def]
      \\ rveq \\ fs [bytes_in_word_def,word_mul_n2w]
      \\ fs [good_dimindex_def] \\ fs [])
    \\ pop_assum (fn th => fs [th])
    \\ `sp1 + sp2 <= limit` by
     (fs [word_ml_inv_def,abs_ml_inv_def,heap_ok_def] \\ rveq \\ fs []
      \\ fs [unused_space_inv_def])
    \\ qsuff_tac `limit - (sp1 + sp2) <= size_of_heap s` THEN1 fs []
    \\ simp [size_of_heap_def,stack_to_vs_def,toList_def,toListA_def]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ qmatch_asmsub_abbrev_tac `_ root_vars s.refs (vars,_)`
    \\ simp [size_of_global_to_vs]
    \\ qmatch_goalsub_abbrev_tac `size_of _ roots`
    \\ `limit = heap_length heap1` by fs [abs_ml_inv_def,heap_ok_def]
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ `sp2 = 0` by fs [abs_ml_inv_def,gc_kind_inv_def] \\ rveq \\ fs []
    \\ `PERM roots root_vars` by
     (simp [Abbr`roots`,Abbr`root_vars`]
      \\ once_rewrite_tac [PERM_SYM]
      \\ fs [sortingTheory.PERM_TO_APPEND_SIMPS]
      \\ match_mp_tac flat_PERM_extract_stack \\ fs [])
    \\ fs [abs_ml_inv_def]
    \\ qpat_x_assum `bc_stack_ref_inv _ _ _ _ _` assume_tac
    \\ fs [bc_stack_ref_inv_def]
    \\ drule soundness_size_of
    \\ disch_then drule
    \\ `?res. size_of s.limits roots s.refs LN = res` by fs []
    \\ PairCases_on `res` \\ fs []
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ disch_then (qspec_then `[]` mp_tac)
    \\ impl_tac THEN1 simp []
    \\ strip_tac
    \\ match_mp_tac LESS_EQ_TRANS
    \\ once_rewrite_tac [CONJ_COMM] \\ fs [SUM]
    \\ asm_exists_tac \\ fs []
    \\ fs [data_length_def]
    \\ match_mp_tac SUM_MAP_lookup_len_LESS_EQ
    \\ fs [set_data_pointers,ALL_DISTINCT_data_pointers]
    \\ simp [SUBSET_DEF]
    \\ simp [isSomeDataElement_def] \\ rw []
    \\ qpat_x_assum `all_reachable_from_roots _ _` assume_tac
    \\ fs [all_reachable_from_roots_def]
    \\ pop_assum drule \\ simp [Once IN_DEF] \\ strip_tac
    \\ drule (GEN_ALL traverse_heap_reachable)
    \\ disch_then drule \\ simp [])
  \\ fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def]
  \\ strip_tac \\ fs []
  \\ fs [option_case_eq,CaseEq"word_loc"] \\ rveq \\ fs []
  \\ `s.limits.arch_64_bit ⇔ dimindex (:α) = 64` by
   (fs [limits_inv_def])
  \\ `s.limits.heap_limit = limit` by
   (fs [limits_inv_def,heap_in_memory_store_def]
    \\ rpt (qpat_x_assum `FLOOKUP t.store HeapLength = _` mp_tac)
    \\ fs [] \\ fs [heap_ok_def,word_ml_inv_def,abs_ml_inv_def]
    \\ rveq \\ fs [bytes_in_word_def,word_mul_n2w]
    \\ fs [good_dimindex_def] \\ fs [])
  \\ pop_assum (fn th => fs [th])
  \\ `sp1 + sp2 <= limit` by
   (fs [word_ml_inv_def,abs_ml_inv_def,heap_ok_def] \\ rveq \\ fs []
    \\ fs [unused_space_inv_def])
  \\ qsuff_tac `limit - (sp1 + sp2) <= size_of_heap s` THEN1 fs []
  \\ simp [size_of_heap_def,stack_to_vs_def,toList_def,toListA_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ qmatch_asmsub_abbrev_tac `_ root_vars s.refs (vars,_)`
  \\ simp [size_of_global_to_vs]
  \\ qmatch_goalsub_abbrev_tac `size_of _ roots`
  \\ `limit = heap_length heap1` by fs [abs_ml_inv_def,heap_ok_def]
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ `PERM roots root_vars` by
   (simp [Abbr`roots`,Abbr`root_vars`]
    \\ once_rewrite_tac [PERM_SYM]
    \\ fs [sortingTheory.PERM_TO_APPEND_SIMPS]
    \\ match_mp_tac flat_PERM_extract_stack \\ fs [])
  \\ fs [abs_ml_inv_def]
  \\ qpat_x_assum `bc_stack_ref_inv _ _ _ _ _` assume_tac
  \\ fs [bc_stack_ref_inv_def]
  \\ drule soundness_size_of
  \\ disch_then drule
  \\ `?res. size_of s.limits roots s.refs LN = res` by fs []
  \\ PairCases_on `res` \\ fs []
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ disch_then (qspec_then `[]` mp_tac)
  \\ impl_tac THEN1 simp []
  \\ strip_tac
  \\ match_mp_tac LESS_EQ_TRANS
  \\ once_rewrite_tac [CONJ_COMM] \\ fs [SUM]
  \\ asm_exists_tac \\ fs []
  \\ fs [data_length_def]
  \\ match_mp_tac SUM_MAP_lookup_len_LESS_EQ
  \\ fs [set_data_pointers,ALL_DISTINCT_data_pointers]
  \\ simp [SUBSET_DEF]
  \\ simp [isSomeDataElement_def] \\ rw []
  \\ qpat_x_assum `all_reachable_from_roots _ _` assume_tac
  \\ fs [all_reachable_from_roots_def]
  \\ pop_assum drule \\ simp [Once IN_DEF] \\ strip_tac
  \\ drule (GEN_ALL traverse_heap_reachable)
  \\ disch_then drule \\ simp []
QED

Definition cut_locals_def:
  cut_locals names (s:('a,'b)dataSem$state) =
    case dataSem$cut_env names s.locals of
    | SOME env => s with locals := env
    | NONE => s with locals := LN
End

Theorem size_of_heap_call_push_env:
  dataSem$cut_env names s.locals = SOME x ==>
  size_of_heap (call_env [] ss (push_env x F s)) = size_of_heap (s with locals := x)
Proof
  fs [push_env_def,call_env_def,size_of_heap_def,stack_to_vs_def,
      extract_stack_def,EVAL ``toList (fromList []:'a spt)``]
QED

Theorem gc_lemma:
   let t0 = call_env [Loc l1 l2] ss (push_env y
        (NONE:(num # 'a wordLang$prog # num # num) option) t) in
      dataSem$cut_env names (s:('c,'ffi) dataSem$state).locals = SOME x /\
      state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
      FLOOKUP t.store AllocSize = SOME (Word (alloc_size k)) /\
      wordSem$cut_envs (adjust_sets names) t.locals = SOME y ==>
      ?t2 wl m st w1 w2 stack.
        t0.gc_fun (enc_stack t0.stack,t0.memory,t0.mdomain,t0.store) =
          SOME (wl,m,st) /\
        dec_stack wl t0.stack = SOME stack /\
        pop_env (t0 with <|stack := stack; store := st; memory := m|>) = SOME t2 /\
        FLOOKUP t2.store (Temp 29w) = FLOOKUP t.store (Temp 29w) ∧
        FLOOKUP t2.store AllocSize = SOME (Word (alloc_size k)) /\
        (has_space (Word ((alloc_size k):'a word)) t2 = SOME F /\ c.gc_kind <> None ==>
           s.limits.heap_limit < size_of_heap (s with locals := x) + k) /\
        state_rel c l1 l2 (s with <| locals := x; space := 0;
          stack_max := OPTION_MAP2 MAX
          (OPTION_MAP2 MAX s.stack_max
             (size_of_stack (Env s.locals_size x::s.stack)))
          (OPTION_MAP2 $+ (size_of_stack (Env s.locals_size x::s.stack)) ss) |>) t2 [] locs
Proof
  srw_tac[][] \\ fs [LET_DEF]
  \\ Q.UNABBREV_TAC `t0` \\ fs []
  \\ imp_res_tac (state_rel_call_env_push_env
      |> Q.SPEC `NONE` |> Q.INST [`args`|->`[]`] |> GEN_ALL
      |> SIMP_RULE std_ss [MAP,get_vars_def,wordSemTheory.get_vars_def]
      |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
      |> (fn th => MATCH_MP th (UNDISCH state_rel_inc_clock))
      |> SIMP_RULE (srw_ss()) [dec_clock_inc_clock] |> DISCH_ALL)
  \\ fs []
  \\ pop_assum (qspecl_then [`ss`,`l1`,`l2`] mp_tac) \\ srw_tac[][]
  \\ pop_assum (mp_tac o MATCH_MP state_rel_gc)
  \\ impl_tac THEN1
   (fs [wordSemTheory.call_env_def,call_env_def,
        wordSemTheory.push_env_def,fromList_def]
    \\ Cases_on `env_to_list (SND y) t.permute` \\ fs [LET_DEF]
    \\ fs [fromList2_def,Once insert_def])
  \\ srw_tac[][] \\ fs [wordSemTheory.call_env_def]
  \\ pop_assum (mp_tac o MATCH_MP
      (state_rel_pop_env_IMP |> REWRITE_RULE [GSYM AND_IMP_INTRO]
         |> Q.GEN `s2`)) \\ srw_tac[][]
  \\ pop_assum (qspec_then `s with <| locals := x ; space := 0;
       locals_size := s.locals_size ;
       safe_for_space := (s.safe_for_space ∧
         the F
           (OPTION_MAP ($> s.limits.stack_limit)
              (OPTION_MAP2 MAX s.stack_max
                 (size_of_stack (Env s.locals_size x::s.stack)))) ∧
        the F
          (OPTION_MAP ($> s.limits.stack_limit)
             (OPTION_MAP2 MAX
                (OPTION_MAP2 MAX s.stack_max
                   (size_of_stack (Env s.locals_size x::s.stack)))
                (OPTION_MAP2 $+
                   (size_of_stack (Env s.locals_size x::s.stack)) ss)))) ;
       stack_max := OPTION_MAP2 MAX
          (OPTION_MAP2 MAX s.stack_max
             (size_of_stack (Env s.locals_size x::s.stack)))
          (OPTION_MAP2 $+ (size_of_stack (Env s.locals_size x::s.stack)) ss) |>` mp_tac)
  \\ impl_tac THEN1
   (fs[pop_env_def,push_env_def,call_env_def,
      dataSemTheory.state_component_equality,AC CONJ_COMM CONJ_ASSOC])
  \\ srw_tac[][] \\ fs []
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list (SND y) t.permute` \\ fs [LET_DEF]
  \\ every_case_tac \\ fs []
  \\ srw_tac[][] \\ fs []
  \\ fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def]
  \\ drule size_of_heap_call_push_env \\ strip_tac \\ fs []
  \\ `(call_env [] ss (push_env x F s)).limits.heap_limit = s.limits.heap_limit`
        by fs [call_env_def,push_env_def] \\ fs []
  \\ qpat_x_assum `state_rel c l1 l2 _ _ _ _` mp_tac
  \\ simp [state_rel_thm] \\ rpt strip_tac \\ rveq \\ fs []
QED

Theorem gc_add_call_env:
   (case gc (wordSem$push_env y NONE t5) of
     | NONE => (SOME wordSem$Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error, flush_state T s')
                  | SOME s' => f s') = (res,t) ==>
    (case gc (wordSem$call_env [Loc l1 l2] (SOME 0) (push_env y NONE t5)) of
     | NONE => (SOME Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error, flush_state T s')
                  | SOME s' => f s') = (res,t)
Proof
  fs [wordSemTheory.gc_def,wordSemTheory.call_env_def,LET_DEF,
      wordSemTheory.push_env_def,wordSemTheory.flush_state_def]
  \\ Cases_on `env_to_list (SND y) t5.permute` \\ fs [LET_DEF]
  \\ every_case_tac \\ fs []
  \\ srw_tac[][] \\ fs []
  \\ fs [wordSemTheory.pop_env_def]
QED

Theorem has_space_state_rel:
  has_space (Word ((alloc_size k):'a word)) (r:('a,'c,'ffi) state) = SOME T /\
  state_rel c l1 l2 s r [] locs ==>
  state_rel c l1 l2 (s with space := k) r [] locs
Proof
  fs [state_rel_def] \\ srw_tac[][]
  \\ asm_exists_tac \\ fs []
  \\ fs [heap_in_memory_store_def,wordSemTheory.has_space_def,wordSemTheory.get_store_def]
  \\ last_x_assum assume_tac
  \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ gvs [alloc_size_def,bytes_in_word_def]
  \\ `((sp+3) * (dimindex (:'a) DIV 8)) + 1 < dimword (:'a)` by
   (imp_res_tac word_ml_inv_SP_LIMIT
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs [])
  \\ `((sp+3) * (dimindex (:'a) DIV 8)) < dimword (:'a)` by decide_tac
  \\ every_case_tac
  \\ fs [word_mul_n2w]
  \\ gvs [good_dimindex_def,dimword_def,w2n_minus1]
QED

Theorem evaluate_IMP_inc_clock:
   evaluate (q,t) = (NONE,t1) ==>
    evaluate (q,inc_clock ck t) = (NONE,inc_clock ck t1)
Proof
  srw_tac[][inc_clock_def] \\ match_mp_tac evaluate_add_clock
  \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_IMP_inc_clock_Ex:
   evaluate (q,t) = (SOME (Exception x y),t1) ==>
    evaluate (q,inc_clock ck t) = (SOME (Exception x y),inc_clock ck t1)
Proof
  srw_tac[][inc_clock_def] \\ match_mp_tac evaluate_add_clock
  \\ full_simp_tac(srw_ss())[]
QED

Theorem get_var_inc_clock:
   get_var n (inc_clock k s) = get_var n s
Proof
  full_simp_tac(srw_ss())[wordSemTheory.get_var_def,inc_clock_def]
QED

Theorem get_vars_inc_clock:
   get_vars n (inc_clock k s) = get_vars n s
Proof
  Induct_on `n` \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[get_var_inc_clock]
QED

Theorem set_var_inc_clock:
   set_var n x (inc_clock ck t) = inc_clock ck (set_var n x t)
Proof
  full_simp_tac(srw_ss())[wordSemTheory.set_var_def,inc_clock_def]
QED

val do_app = LIST_CONJ [dataSemTheory.do_app_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def,
  dataSemTheory.do_app_aux_def]

Theorem w2n_minus_1_LESS_EQ:
   (w2n (-1w:'a word) <= w2n (w:'a word)) <=> w + 1w = 0w
Proof
  fs [word_2comp_n2w]
  \\ Cases_on `w` \\ fs [word_add_n2w]
  \\ `n + 1 <= dimword (:'a)` by decide_tac
  \\ Cases_on `dimword (:'a) = n + 1` \\ fs []
QED

Theorem bytes_in_word_ADD_1_NOT_ZERO:
   good_dimindex (:'a) ==>
    bytes_in_word * w + 1w <> 0w:'a word
Proof
  rpt strip_tac
  \\ `(bytes_in_word * w + 1w) ' 0 = (0w:'a word) ' 0` by metis_tac []
  \\ fs [WORD_ADD_BIT0,word_index,WORD_MUL_BIT0]
  \\ rfs [bytes_in_word_def,EVAL ``good_dimindex (:α)``,word_index]
  \\ rfs [bytes_in_word_def,EVAL ``good_dimindex (:α)``,word_index]
QED

Theorem option_le_OPTION_MAP2_MAX:
  option_le (OPTION_MAP2 MAX n m) n = option_le m n /\
  option_le (OPTION_MAP2 MAX m n) n = option_le m n
Proof
  Cases_on `m` \\ Cases_on `n` \\ fs []
QED

Theorem alloc_lemma:
   state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem$state) [] locs /\
    dataSem$cut_env names s.locals = SOME x /\
    alloc (alloc_size k) (adjust_sets names) t =
      ((q:'a result option),r) ==>
    (q = SOME NotEnoughSpace ⇒
     r.ffi = s.ffi /\ option_le r.stack_max s.stack_max /\
     (c.gc_kind <> None ==>
       s.limits.heap_limit < size_of_heap (cut_locals names s) + k)) ∧
    (q ≠ SOME NotEnoughSpace ⇒
     state_rel c l1 l2 (s with <|locals := x; space := k|>) r [] locs ∧
     alloc_size k <> -1w:'a word /\
     FLOOKUP r.store (Temp 29w) = FLOOKUP t.store (Temp 29w) /\
     r.code = t.code /\
     r.code_buffer = t.code_buffer /\
     r.data_buffer = t.data_buffer /\
     r.compile_oracle = t.compile_oracle /\
     q = NONE)
Proof
  strip_tac
  \\ full_simp_tac(srw_ss())[wordSemTheory.alloc_def,
       LET_DEF,addressTheory.CONTAINER_def]
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac`push_env _ NONE t5`
  \\ strip_tac
  \\ imp_res_tac cut_env_IMP_cut_env
  \\ imp_res_tac cut_env_IMP_cut_envs
  \\ full_simp_tac(srw_ss())[] \\ rveq
  \\ first_x_assum (assume_tac o HO_MATCH_MP gc_add_call_env)
  \\ `FLOOKUP t5.store AllocSize = SOME (Word (alloc_size k)) /\
      wordSem$cut_envs (adjust_sets names) t5.locals = SOME (y1,y2) /\
      state_rel c l1 l2 s t5 [] locs` by
   (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[state_rel_set_store_AllocSize]
    \\ full_simp_tac(srw_ss())[wordSemTheory.set_store_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,state_rel_insert_1,FLOOKUP_DEF])
  \\ strip_tac
  \\ mp_tac (gc_lemma |> Q.INST [`t`|->`t5`,`ss`|->`SOME 0`,‘y’|->‘(y1,y2)’] |> SIMP_RULE std_ss [LET_DEF])
  \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.gc_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y2 t5.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ `IS_SOME (has_space (Word (alloc_size k):'a word_loc) t2)` by
       full_simp_tac(srw_ss())[wordSemTheory.has_space_def,wordSemTheory.get_store_def,
          state_rel_def,heap_in_memory_store_def]
  \\ `option_le r.stack_max s.stack_max` by
    (`r.stack_max = OPTION_MAP2 MAX t5.stack_max
       (stack_size (StackFrame t5.locals_size (toAList y1) q' NONE::t5.stack))` by
      (imp_res_tac wordPropsTheory.pop_env_const \\ fs []
       \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool"] \\ rveq \\ fs []
       \\ fs [wordSemTheory.flush_state_def])
     \\ qpat_x_assum `state_rel c l1 l2 s t5 [] locs` mp_tac
     \\ simp [state_rel_def]
     \\ fs [wordSemTheory.stack_size_def,wordSemTheory.stack_size_frame_def]
     \\ qpat_abbrev_tac `pat = FOLDR _ _ _` \\ strip_tac
     \\ match_mp_tac option_le_trans
     \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []
     \\ Cases_on `t5.stack_max` \\ fs []
     \\ Cases_on `s.locals_size` \\ fs []
     \\ Cases_on `pat` \\ fs [])
  \\ gvs [wordSemTheory.get_store_def]
  \\ Cases_on `has_space (Word (alloc_size k):'a word_loc) t2`
  \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac has_space_state_rel \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac dataPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
  \\ UNABBREV_ALL_TAC
  \\ full_simp_tac(srw_ss())[wordSemTheory.set_store_def,state_rel_def]
  \\ fs [cut_locals_def]
  \\ qpat_assum `has_space (Word (alloc_size k)) r = SOME T` assume_tac
  THEN1
   (reverse (rpt conj_tac) THEN1 (asm_exists_tac \\ asm_rewrite_tac[])
    THEN1
     (match_mp_tac option_le_trans \\ qexists_tac `t.stack_max`
      \\ fs [option_le_OPTION_MAP2_MAX]
      \\ match_mp_tac option_le_trans \\ ONCE_REWRITE_TAC [CONJ_COMM]
      \\ asm_exists_tac \\ fs []
      \\ rpt (pop_assum kall_tac)
      \\ fs [wordSemTheory.stack_size_def,wordSemTheory.stack_size_frame_def]
      \\ rw [OPTION_MAP2_DEF] \\ fs [IS_SOME_EXISTS] \\ fs [])
    \\ imp_res_tac stack_rel_IMP_size_of_stack
    \\ fs [wordSemTheory.stack_size_def,wordSemTheory.stack_size_frame_def]
    \\ rpt (pop_assum kall_tac)
    \\ rw [OPTION_MAP2_DEF] \\ fs [IS_SOME_EXISTS] \\ fs [])
  \\ simp [FLOOKUP_SIMP]
  \\ CCONTR_TAC \\ fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def]
  \\ fs [AllCaseEqs()]
  \\ rfs [heap_in_memory_store_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ gvs []
  \\ rfs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w,w2n_minus_1_LESS_EQ]
  \\ rfs [bytes_in_word_ADD_1_NOT_ZERO]
QED

Theorem cut_names_adjust_set_insert_ODD:
   ODD n ==> cut_names (adjust_set the_names) (insert n w s) =
             cut_names (adjust_set the_names) s
Proof
  reverse (rw [wordSemTheory.cut_names_def] \\ fs [SUBSET_DEF])
  \\ res_tac \\ fs []
  THEN1 (rveq \\ fs [domain_lookup,lookup_adjust_set]
         \\ every_case_tac \\ fs [])
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ pop_assum mp_tac
  \\ simp [domain_lookup,lookup_adjust_set]
  \\ rw [] \\ fs []
QED

Theorem cut_env_adjust_sets_ODD:
  ODD n ⇒ cut_env (adjust_sets names) (insert n w s) =
          cut_env (adjust_sets names) s
Proof
  gvs [wordSemTheory.cut_env_def,adjust_sets_def]
  \\ gvs [wordSemTheory.cut_envs_def]
  \\ gvs [cut_names_adjust_set_insert_ODD]
  \\ gvs [wordSemTheory.cut_names_def]
  \\ rw [] \\ gvs []
  \\ AP_TERM_TAC
  \\ gvs [lookup_inter_alt]
  \\ gvs [lookup_insert]
  \\ rw [] \\ gvs []
QED

Theorem cut_envs_adjust_sets_ODD:
  ODD n ⇒ cut_envs (adjust_sets names) (insert n w s) =
          cut_envs (adjust_sets names) s
Proof
  gvs [wordSemTheory.cut_envs_def,adjust_sets_def]
  \\ gvs [cut_names_adjust_set_insert_ODD]
  \\ gvs [wordSemTheory.cut_names_def]
  \\ rw [] \\ gvs []
  \\ gvs [lookup_inter_alt]
  \\ gvs [lookup_insert]
  \\ rw [] \\ gvs []
QED

Theorem alloc_locals_insert_1:
  alloc k (adjust_sets names) (t with locals := insert 1 w t.locals) =
  alloc k (adjust_sets names) t
Proof
  gvs [wordSemTheory.alloc_def]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [adjust_sets_def,wordSemTheory.cut_envs_def]
  \\ gvs [cut_names_adjust_set_insert_ODD]
  \\ gvs [wordSemTheory.cut_names_def]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ rw [] \\ gvs [lookup_inter_alt]
  \\ rw [] \\ gvs [lookup_insert]
QED

Theorem evaluate_GiveUp:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ==>
    ?r. evaluate (GiveUp,t) = (SOME NotEnoughSpace,r) /\
        r.ffi = s.ffi /\ t.ffi = s.ffi
Proof
  fs [GiveUp_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ strip_tac
  \\ Cases_on `alloc (-1w) (adjust_sets (LN:num_set)) (set_var 1 (Word (-1w)) t)
                  :'a result option # ('a,'c,'ffi) wordSem$state`
  \\ fs [wordSemTheory.set_var_def,alloc_locals_insert_1]
  \\ `-1w = alloc_size (dimword (:'a)):'a word` by
   (fs [alloc_size_def,state_rel_def]
    \\ fs [good_dimindex_def,dimword_def] \\ rw [])
  \\ pop_assum (fn th => fs [th])
  \\ drule (alloc_lemma |> Q.INST [`names`|->`LN`,`k`|->`dimword(:'a)`] |> GEN_ALL)
  \\ fs [dataSemTheory.cut_env_def,set_var_def]
  \\ Cases_on `q = SOME NotEnoughSpace` \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ rpt var_eq_tac
  \\ fs [state_rel_def]
  \\ fs [word_ml_inv_def,abs_ml_inv_def,unused_space_inv_def,heap_ok_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [] \\ fs []
QED

Theorem insert_insert_3_1:
   insert 3 x (insert 1 y t) = insert 1 y (insert 3 x t)
Proof
  fs [Once insert_insert]
QED

Theorem shift_lsl:
   good_dimindex (:'a) ==> w << shift (:'a) = w * bytes_in_word:'a word
Proof
  rw [good_dimindex_def,shift_def,bytes_in_word_def]
  \\ fs [WORD_MUL_LSL]
QED

val alloc_alt =
  SPEC_ALL alloc_lemma
  |> ConseqConv.WEAKEN_CONSEQ_CONV_RULE
     (ConseqConv.CONSEQ_REWRITE_CONV
        ([],[],[prove(``alloc_size k ≠ -1w ==> T``,fs [])]))
  |> GEN_ALL

Theorem alloc_size_dimword:
   good_dimindex (:'a) ==>
    alloc_size (dimword (:'a)) = -1w:'a word
Proof
  simp[alloc_size_def,EVAL ``good_dimindex (:'a)``] \\ rw [] \\ rpt strip_tac \\
  gs[]
QED

val alloc_fail_lemma = alloc_lemma
  |> Q.INST [`k`|->`dimword (:'a)`]
  |> SIMP_RULE std_ss [UNDISCH alloc_size_dimword]
  |> DISCH_ALL |> MP_CANON
  |> SIMP_RULE std_ss [AC ADD_COMM ADD_ASSOC]

Theorem alloc_fail:
  good_dimindex (:α) ∧ state_rel c l1 l2 ^s t [] locs ∧
  dataSem$cut_env names s.locals = SOME x ∧
  alloc (-1w:'a word) (adjust_sets names) t = (q,r) ⇒
  (q = SOME NotEnoughSpace ⇒ r.ffi = s.ffi ∧ option_le r.stack_max s.stack_max) ∧
  q = SOME NotEnoughSpace
Proof
  metis_tac [alloc_fail_lemma]
QED

Theorem word_exp_rw =
  LIST_CONJ
  [wordSemTheory.word_exp_def,
   wordLangTheory.word_op_def,
   wordLangTheory.word_sh_def,
   wordSemTheory.get_var_def,
   wordSemTheory.get_var_imm_def,
   wordSemTheory.the_words_def,
   wordSemTheory.get_store_def,
   lookup_insert]

Theorem get_var_set_var_thm:
   wordSem$get_var n (set_var m x y) = if n = m then SOME x else get_var n y
Proof
  fs[wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert]
QED

Theorem state_rel_cut_env_cut_env:
   state_rel c l1 l2 s t [] locs /\
    dataSem$cut_env names s.locals = SOME x /\
    wordSem$cut_env (adjust_sets names) t.locals = SOME y ==>
    state_rel c l1 l2 (s with locals := x) (t with locals := y) [] locs
Proof
  rpt strip_tac
  \\ drule (GEN_ALL state_rel_cut_env)
  \\ disch_then drule
  \\ simp [state_rel_thm]
  \\ rw []
  >-
   (gvs [wordSemTheory.cut_env_def,adjust_sets_def,AllCaseEqs()]
    \\ gvs [lookup_union,AllCaseEqs()]
    \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs()]
    \\ gvs [wordSemTheory.cut_names_def,lookup_inter_alt])
  >-
   (gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def,
         adjust_sets_def,AllCaseEqs(),
         dataSemTheory.cut_env_def,wordSemTheory.cut_names_def]
    \\ pop_assum mp_tac
    \\ simp [IS_SOME_EXISTS,GSYM domain_lookup]
    \\ simp [Once $ GSYM adjust_var_IN_adjust_set]
    \\ gvs [SUBSET_DEF])
  \\ fs []
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``x = y ==> f x ==> f y``)
  \\ fs []
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ fs [wordSemTheory.cut_env_def]
  \\ rveq \\ fs [lookup_inter_alt]
  \\ rw []
  \\ fs [dataSemTheory.cut_env_def] \\ rveq \\ fs []
  \\ fs [adjust_set_inter,domain_inter]
  \\ gvs [adjust_sets_def,wordSemTheory.cut_envs_def,AllCaseEqs(),lookup_union,
          lookup_inter_alt,wordSemTheory.cut_names_def,SF CONJ_ss]
  \\ gvs [SUBSET_DEF]
  \\ res_tac \\ gvs [domain_lookup]
  \\ res_tac \\ fs []
QED

Theorem domain_adjust_set_EVEN:
   k IN domain (adjust_set s) ==> EVEN k
Proof
  fs [adjust_set_def,domain_lookup,lookup_fromAList] \\ rw [] \\ fs []
  \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP]
  \\ pairarg_tac \\ fs [EVEN_adjust_var]
QED

Theorem cut_env_adjust_sets_insert_ODD:
  ODD n ⇒
  cut_env (adjust_sets names) (insert n w t) =
  cut_env (adjust_sets names) t
Proof
  strip_tac
  \\ gvs [wordSemTheory.cut_env_def,adjust_sets_def,
       wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ Cases_on ‘n = 0’ \\ gvs []
  \\ ‘inter (insert n w t) (LS ()) = inter t (LS ())’ by
        gvs [lookup_inter_alt,lookup_insert]
  \\ ‘inter (insert n w t) (adjust_set names) =
      inter t (adjust_set names)’ by
       (gvs [lookup_inter_alt,lookup_insert] \\ rw [] \\ gvs []
        \\ imp_res_tac domain_adjust_set_EVEN \\ gvs [EVEN_ODD])
  \\ ‘domain (adjust_set names) ⊆ n INSERT domain t ⇔
      domain (adjust_set names) ⊆ domain t’ by
   (gvs [SUBSET_DEF]
    \\ rw [] \\ eq_tac \\ rw []
    \\ imp_res_tac domain_adjust_set_EVEN \\ gvs [EVEN_ODD]
    \\ res_tac \\ gvs [])
  \\ simp []
QED

Theorem cut_envs_adjust_sets_insert_ODD:
  ODD n ⇒
  cut_envs (adjust_sets names) (insert n w t) =
  cut_envs (adjust_sets names) t
Proof
  strip_tac
  \\ gvs [wordSemTheory.cut_env_def,adjust_sets_def,
       wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ Cases_on ‘n = 0’ \\ gvs []
  \\ ‘inter (insert n w t) (LS ()) = inter t (LS ())’ by
        gvs [lookup_inter_alt,lookup_insert]
  \\ ‘inter (insert n w t) (adjust_set names) =
      inter t (adjust_set names)’ by
       (gvs [lookup_inter_alt,lookup_insert] \\ rw [] \\ gvs []
        \\ imp_res_tac domain_adjust_set_EVEN \\ gvs [EVEN_ODD])
  \\ ‘domain (adjust_set names) ⊆ n INSERT domain t ⇔
      domain (adjust_set names) ⊆ domain t’ by
   (gvs [SUBSET_DEF]
    \\ rw [] \\ eq_tac \\ rw []
    \\ imp_res_tac domain_adjust_set_EVEN \\ gvs [EVEN_ODD]
    \\ res_tac \\ gvs [])
  \\ simp []
QED

Theorem cut_names_insert_1_insert_1:
  wordSem$cut_names (insert 1 () (adjust_set names)) (insert 1 w t) =
  case wordSem$cut_names (adjust_set names) (t:'a num_map) of
  | NONE => NONE
  | SOME e => SOME $ insert 1 w e
Proof
  fs [wordSemTheory.cut_names_def]
  \\ ‘∀t. domain (adjust_set names) ⊆ 1 INSERT domain (t:'a num_map) ⇔
          domain (adjust_set names) ⊆ domain t’ by
    (rw [] \\ eq_tac \\ rw [SUBSET_DEF]
     \\ res_tac \\ gvs [] \\ fs [domain_lookup,lookup_adjust_set])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ gvs [inter_insert]
  \\ gvs [spt_eq_thm,wf_insert,lookup_insert]
  \\ rw [] \\ fs [lookup_inter_alt]
QED

Theorem alloc_store:
  alloc k names t = (NONE,s1) ∧
  t.gc_fun = word_gc_fun c ∧
  FLOOKUP t.store CurrHeap = SOME (Word cu) ∧
  FLOOKUP t.store TriggerGC = SOME (Word end) ∧
  FLOOKUP t.store NextFree = SOME (Word next) ∧
  FLOOKUP t.store HeapLength = SOME (Word heap_length1) ⇒
  ∃end next heap_length1 cu.
    FLOOKUP s1.store CurrHeap = SOME (Word cu) ∧
    FLOOKUP s1.store TriggerGC = SOME (Word end) ∧
    FLOOKUP s1.store NextFree = SOME (Word next) ∧
    FLOOKUP s1.store HeapLength = SOME (Word heap_length1)
Proof
  gvs [wordSemTheory.alloc_def,AllCaseEqs(),wordSemTheory.gc_def]
  \\ rw [] \\ gvs []
  \\ fs [wordSemTheory.set_store_def,wordSemTheory.enc_stack_def,
         wordSemTheory.push_env_def,wordSemTheory.pop_env_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [word_gc_fun_def,AllCaseEqs()]
  \\ Cases_on ‘c.gc_kind’ \\ fs []
  \\ gvs [FUPDATE_LIST,FAPPLY_FUPDATE_THM,FLOOKUP_DEF,word_full_gc_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [FUPDATE_LIST,FAPPLY_FUPDATE_THM,FLOOKUP_DEF,word_full_gc_def]
QED

Triviality alloc_with_locals_1_3:
  alloc k (adjust_sets names)
             (t with locals := insert 1 w1 (insert 3 w2 t.locals)) =
  alloc k (adjust_sets names) t
Proof
  gvs [wordSemTheory.alloc_def]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [adjust_sets_def,wordSemTheory.cut_envs_def]
  \\ gvs [cut_names_adjust_set_insert_ODD]
  \\ gvs [wordSemTheory.cut_names_def]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ rw [] \\ gvs [lookup_inter_alt]
  \\ rw [] \\ gvs [lookup_insert]
QED

Theorem cut_names_imp_wf:
  cut_names s t = SOME x ⇒ wf x
Proof
  rw [wordSemTheory.cut_names_def] \\ rw []
QED

Theorem cut_env_insert_1:
  cut_env (FST (adjust_sets names), insert 1 () (SND (adjust_sets names))) (insert 1 w t) =
  case cut_env (adjust_sets names) t of NONE => NONE | SOME v => SOME (insert 1 w v)
Proof
  gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def,adjust_sets_def]
  \\ ‘cut_names (LS ()) (insert 1 w t) = cut_names (LS ()) t’ by
    (rw [wordSemTheory.cut_names_def]
     \\ rw [lookup_inter_alt] \\ gvs [lookup_insert])
  \\ gvs []
  \\ qsuff_tac ‘cut_names (insert 1 () (adjust_set names)) (insert 1 w t) =
                case cut_names (adjust_set names) t of
                | NONE => NONE
                | SOME r => SOME (insert 1 w r)’ \\ gvs []
  >- (every_case_tac \\ gvs [] \\ rw []
      \\ DEP_REWRITE_TAC [spt_eq_thm]
      \\ gvs [lookup_insert,lookup_union] \\ rw []
      \\ rpt $ irule_at Any wf_insert
      \\ rpt $ irule_at Any wf_union
      \\ imp_res_tac cut_names_imp_wf \\ gvs [])
  \\ gvs [wordSemTheory.cut_names_def]
  \\ ‘domain (adjust_set names) ⊆ 1 INSERT domain t ⇔
      domain (adjust_set names) ⊆ domain t’ by
   (eq_tac \\ gvs [SUBSET_DEF] \\ rw []
    \\ res_tac \\ gvs [NOT_1_domain])
  \\ gvs [] \\ IF_CASES_TAC \\ gvs []
  \\ DEP_REWRITE_TAC [spt_eq_thm]
  \\ gvs [] \\ irule_at Any wf_insert \\ gvs []
  \\ gvs [lookup_inter_alt,lookup_insert]
  \\ strip_tac \\ Cases_on ‘n = 1’ \\ gvs []
QED

Theorem AllocVar_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ∧
    dataSem$cut_env names s.locals = SOME x ∧
    get_var 1 t = SOME (Word w) /\
    evaluate (AllocVar c limit names,t) = (q,r) /\
    limit < dimword (:'a) DIV 8 ==>
    (q = SOME NotEnoughSpace ⇒ r.ffi = s.ffi ∧ option_le r.stack_max s.stack_max ∧
          (c.gc_kind <> None /\ w2n w DIV 4 < limit ⇒
           s.limits.heap_limit < size_of_heap (cut_locals names s) + w2n w DIV 4 + 1)) ∧
    (q ≠ SOME NotEnoughSpace ⇒
      w2n w DIV 4 < limit /\
      state_rel c l1 l2 (s with <|locals := x; space := w2n w DIV 4 + 1|>) r [] locs ∧
      FLOOKUP r.store (Temp 29w) = FLOOKUP t.store (Temp 29w) /\
      r.code = t.code /\
      r.code_buffer = t.code_buffer /\
      r.data_buffer = t.data_buffer /\
      r.compile_oracle = t.compile_oracle /\
      q = NONE)
Proof
  fs [wordSemTheory.evaluate_def,AllocVar_def,list_Seq_def] \\ strip_tac
  \\ `limit < dimword (:'a)` by
        (rfs [EVAL ``good_dimindex (:'a)``,state_rel_def,dimword_def] \\ rfs [])
  \\ `?end next heap_length1 cu.
        FLOOKUP t.store CurrHeap = SOME (Word cu) /\
        FLOOKUP t.store TriggerGC = SOME (Word end) /\
        FLOOKUP t.store NextFree = SOME (Word next) /\
        FLOOKUP t.store HeapLength = SOME (Word heap_length1)` by
          full_simp_tac(srw_ss())[state_rel_def,heap_in_memory_store_def]
  \\ fs [word_exp_rw,get_var_set_var_thm,wordSemTheory.get_store_def] \\ rfs []
  \\ rfs [wordSemTheory.get_var_def]
  \\ `~(2 ≥ dimindex (:α))` by
         fs [state_rel_def,EVAL ``good_dimindex (:α)``,shift_def] \\ fs []
  \\ rfs [word_exp_rw,wordSemTheory.set_var_def,lookup_insert]
  \\ fs [asmTheory.word_cmp_def]
  \\ fs [WORD_LO,w2n_lsr] \\ rfs []
  \\ reverse (Cases_on `w2n w DIV 4 < limit`) \\ fs [] THEN1
   (rfs [word_exp_rw,wordSemTheory.set_var_def,lookup_insert]
    \\ reverse FULL_CASE_TAC
    \\ qpat_assum `state_rel c l1 l2 s t [] locs` mp_tac
    \\ rewrite_tac [state_rel_def] \\ strip_tac
    \\ fs [heap_in_memory_store_def] \\ fs []
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    THEN1
     (rw [] \\ fs [] \\ rfs [] \\ fs [state_rel_def]
      \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
      \\ fs [NOT_LESS,w2n_minus_1_LESS_EQ,bytes_in_word_ADD_1_NOT_ZERO])
    \\ reverse (Cases_on `c.call_empty_ffi`)
    THEN1
     (fs [SilentFFI_def,wordSemTheory.evaluate_def,lookup_insert]
      \\ match_mp_tac (GEN_ALL alloc_fail) \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ asm_exists_tac \\ fs [insert_insert_3_1]
      \\ gvs [alloc_with_locals_1_3]
      \\ pairarg_tac \\ gvs [CaseEq"bool"])
    \\ fs [Once SilentFFI_def,wordSemTheory.evaluate_def]
    \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
           wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
           ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
           wordSemTheory.get_var_def,lookup_insert,list_Seq_def,
           wordSemTheory.the_words_def,wordLangTheory.word_op_def,
           cut_names_adjust_set_insert_ODD,wordSemTheory.get_store_def]
    \\ fs [Q.SPECL [`3`,`1`] insert_insert |> SIMP_RULE std_ss [],
           Q.SPECL [`7`,`1`] insert_insert |> SIMP_RULE std_ss [],
           Q.SPECL [`9`,`1`] insert_insert |> SIMP_RULE std_ss []]
    \\ fs [cut_names_insert_1_insert_1,cut_names_adjust_set_insert_ODD]
    \\ drule (GEN_ALL cut_env_IMP_cut_env)
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
    \\ gvs [cut_env_insert_1,cut_env_adjust_sets_ODD]
    \\ fs [] \\ pairarg_tac \\ fs []
    \\ drule (GEN_ALL state_rel_cut_env)
    \\ disch_then drule \\ strip_tac
    \\ `s.ffi = (s with locals := x).ffi` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ `s.stack_max = (s with locals := x).stack_max` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ `dataSem$cut_env names x = SOME x` by
      (fs [dataSemTheory.cut_env_def] \\ rveq
       \\ fs [lookup_inter_alt,domain_inter])
    \\ drule_all state_rel_cut_env_cut_env
    \\ strip_tac
    \\ drule_at (Pos $ el 2) alloc_fail \\ gvs []
    \\ disch_then drule
    \\ qabbrev_tac ‘t1 = t with locals := union y2 y1’
    \\ ‘t with
        <|locals := insert 1 (Word (-1w)) (union y2 y1);
          memory := t.memory; ffi := s.ffi|> =
        t1 with locals := insert 1 (Word (-1w)) t1.locals’ by
          gvs [Abbr‘t1’,wordSemTheory.state_component_equality]
    \\ gvs [alloc_locals_insert_1]
    \\ strip_tac \\ gvs [])
  \\ qpat_assum `_ = (q,r)` mp_tac
  \\ IF_CASES_TAC THEN1
    (fs [state_rel_def,EVAL ``good_dimindex (:α)``,shift_def])
  \\ pop_assum kall_tac \\ fs [lookup_insert]
  \\ `1w ≪ shift (:α) + w ⋙ 2 ≪ shift (:α) =
      alloc_size (w2n w DIV 4 + 1)` by
   (fs [alloc_size_def] \\ IF_CASES_TAC THEN1
     (sg `w >>> 2 = n2w (w2n w DIV 4)`
      \\ fs [shift_lsl,state_rel_def,bytes_in_word_def,word_add_n2w,word_mul_n2w]
      \\ rewrite_tac [GSYM w2n_11,w2n_lsr] \\ fs [])
    \\ qsuff_tac `(w2n w DIV 4 + 1) * (dimindex (:α) DIV 8) < dimword (:'a)`
    THEN1 fs [] \\ pop_assum kall_tac
    \\ fs [EVAL ``good_dimindex (:'a)``,state_rel_def,dimword_def]
    \\ rfs [] \\ NO_TAC)
  \\ fs []
  \\ reverse IF_CASES_TAC
  THEN1
   (fs [] \\ strip_tac \\ rveq \\ fs []
    \\ fs[state_rel_insert_3_1]
    \\ last_x_assum assume_tac
    \\ drule_all state_rel_cut_env \\ strip_tac
    \\ drule_at Any has_space_state_rel
    \\ gvs [] \\ disch_then irule
    \\ fs [wordSemTheory.has_space_def,wordSemTheory.get_store_def])
  \\ `~(shift (:α) ≥ dimindex (:α))` by
    (fs [good_dimindex_def,shift_def,state_rel_def] \\ fs [])
  \\ fs [lookup_insert]
  \\ reverse (Cases_on `c.call_empty_ffi`)
  THEN1
   (fs [SilentFFI_def,wordSemTheory.evaluate_def,lookup_insert]
    \\ fs [insert_insert_3_1,alloc_with_locals_1_3]
    \\ pairarg_tac \\ gvs []
    \\ ‘res = q ∧ s1 = r’ by gvs [CaseEq"bool"] \\ gvs []
    \\ drule_all alloc_alt \\ gvs [])
  \\ fs [SilentFFI_def,wordSemTheory.evaluate_def,lookup_insert]
  \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
         wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
         ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
         wordSemTheory.get_var_def,lookup_insert,list_Seq_def,
         wordSemTheory.the_words_def,wordLangTheory.word_op_def,
         wordSemTheory.get_store_def]
  \\ fs [Q.SPECL [`3`,`1`] insert_insert |> SIMP_RULE std_ss [],
         Q.SPECL [`7`,`1`] insert_insert |> SIMP_RULE std_ss [],
         Q.SPECL [`9`,`1`] insert_insert |> SIMP_RULE std_ss [],
         cut_env_insert_1,cut_env_adjust_sets_ODD]
  \\ drule_all cut_env_IMP_cut_env
  \\ strip_tac \\ gvs []
  \\ qabbrev_tac ‘t1 = t with locals := y’
  \\ qabbrev_tac ‘nw = alloc_size (w2n w DIV 4 + 1) : 'a word’
  \\ ‘t with
      <|locals := insert 1 (Word nw) y;
        memory := t.memory; ffi := t.ffi|> =
      t1 with locals := insert 1 (Word nw) t1.locals’ by
    gvs [Abbr‘t1’,wordSemTheory.state_component_equality]
  \\ qunabbrev_tac ‘nw’
  \\ gvs [alloc_locals_insert_1]
  \\ fs [cut_locals_def]
  \\ `dataSem$cut_env names x = SOME x` by
    (fs [dataSemTheory.cut_env_def] \\ rveq
     \\ fs [lookup_inter_alt,domain_inter])
  \\ drule_all state_rel_cut_env_cut_env
  \\ strip_tac
  \\ drule alloc_alt \\ gvs []
  \\ disch_then drule
  \\ pairarg_tac \\ gvs []
  \\ disch_then drule
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘res = SOME NotEnoughSpace’ \\ gvs []
  >- gvs [cut_locals_def]
  \\ qpat_assum ‘state_rel c l1 l2 _ _ _ _’ mp_tac
  \\ simp_tac bool_ss [Once state_rel_def]
  \\ strip_tac
  \\ gvs [heap_in_memory_store_def,lookup_insert,
          wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
          ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``]
  \\ gvs [cut_env_adjust_sets_ODD]
  \\ qabbrev_tac ‘s0 = s with <|locals := x; space := w2n w DIV 4 + 1|>’
  \\ `dataSem$cut_env names s0.locals = SOME x` by
    (fs [dataSemTheory.cut_env_def,Abbr‘s0’] \\ rveq
     \\ fs [lookup_inter_alt,domain_inter])
  \\ drule_all cut_env_IMP_cut_env \\ strip_tac \\ gvs []
  \\ drule_all state_rel_cut_env_cut_env
  \\ unabbrev_all_tac
  \\ gvs [] \\ gvs [state_rel_def]
QED

Theorem state_rel_with_clock_0:
   state_rel c r1 r2 s t x locs ==>
    state_rel c r1 r2 (s with space := 0) t x locs
Proof
  fs [state_rel_thm] \\ rw [] \\ fs [memory_rel_def]
  \\ asm_exists_tac \\ fs []
QED

Theorem word_heap_non_empty_limit:
   limit <> 0 ==>
      word_heap other (heap_expand limit) c =
      SEP_EXISTS w1. one (other,w1) *
        word_heap (other + bytes_in_word) (heap_expand (limit - 1)) c
Proof
  Cases_on `limit` \\ fs []
  \\ fs [heap_expand_def,word_heap_def,word_el_def]
  \\ once_rewrite_tac [ADD_COMM]
  \\ fs [word_list_exists_ADD]
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM,FUN_EQ_THM]
  \\ rw [] \\ fs [LENGTH_NIL,LENGTH_EQ_1]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,PULL_EXISTS,word_list_def,
       SEP_CLAUSES,word_list_def,word_heap_def,word_el_def]
  \\ fs [word_list_exists_def]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,PULL_EXISTS,word_list_def,
       SEP_CLAUSES,word_list_def,word_heap_def,word_el_def,SEP_EXISTS_THM]
  \\ metis_tac []
QED

Theorem small_int_0:
   good_dimindex (:'a) ==> small_int (:α) 0
Proof
  fs [good_dimindex_def,small_int_def,dimword_def] \\ rw [] \\ fs []
QED

Theorem state_rel_imp_clock:
   state_rel c l1 l2 s t [] locs ==> s.clock = t.clock
Proof
  fs [state_rel_def]
QED

Theorem get_vars_SOME_IFF_data:
   (get_vars [] t = SOME [] <=> T) /\
    (get_vars (x::xs) t = SOME (y::ys) <=>
     dataSem$get_var x t = SOME y /\
     get_vars xs t = SOME ys)
Proof
  fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem get_vars_SOME_IFF_data_eq:
   ((get_vars [] t = SOME z) <=> (z = [])) /\
    (get_vars (x::xs) t = SOME z <=>
    ?y ys. z = y::ys /\ dataSem$get_var x t = SOME y /\
           get_vars xs t = SOME ys)
Proof
  Cases_on `z` \\ fs [get_vars_SOME_IFF_data]
  \\ fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem get_vars_SOME_IFF:
   (get_vars [] t = SOME [] <=> T) /\
    (get_vars (x::xs) t = SOME (y::ys) <=>
     get_var x t = SOME y /\
     wordSem$get_vars xs t = SOME ys)
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem get_vars_SOME_IFF_eq:
   ((get_vars [] t = SOME z) <=> (z = [])) /\
    (get_vars (x::xs) t = SOME z <=>
    ?y ys. z = y::ys /\ wordSem$get_var x t = SOME y /\
           get_vars xs t = SOME ys)
Proof
  Cases_on `z` \\ fs [get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem memory_rel_get_vars_IMP_lemma:
   memory_rel c be ts refs sp st m dm
     (join_env ll
        (toAList (inter t.locals (adjust_set ll))) ++ envs) ∧
    get_vars n ll = SOME x ∧
    get_vars (MAP adjust_var n) (t:('a,'c,'ffi) wordSem$state) = SOME w ⇒
    memory_rel c be ts refs sp st m dm
      (ZIP (x,w) ++
       join_env ll
         (toAList (inter t.locals (adjust_set ll))) ++ envs)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ rpt_drule word_ml_inv_get_vars_IMP_lemma \\ fs []
QED

Theorem memory_rel_get_vars_IMP:
   memory_rel c be ts s.refs sp st m dm
     (join_env s.locals
        (toAList (inter t.locals (adjust_set s.locals))) ++ envs) ∧
    get_vars n ^s.locals = SOME x ∧
    get_vars (MAP adjust_var n) (t:('a,'c,'ffi) wordSem$state) = SOME w ⇒
    memory_rel c be ts s.refs sp st m dm
      (ZIP (x,w) ++
       join_env s.locals
         (toAList (inter t.locals (adjust_set s.locals))) ++ envs)
Proof
  metis_tac [memory_rel_get_vars_IMP_lemma]
QED

Theorem memory_rel_get_var_IMP =
  memory_rel_get_vars_IMP |> Q.INST [`n`|->`[u]`] |> GEN_ALL
    |> SIMP_RULE std_ss [MAP,get_vars_SOME_IFF_eq,get_vars_SOME_IFF_data_eq,
         PULL_EXISTS,ZIP,APPEND]

Theorem lookup_RefByte_location:
   state_rel c l1 l2 x t [] locs ==>
    lookup RefByte_location t.code = SOME (4,RefByte_code c) /\
    lookup RefArray_location t.code = SOME (3,RefArray_code c) /\
    lookup FromList_location t.code = SOME (4,FromList_code c) /\
    lookup Replicate_location t.code = SOME (5,Replicate_code) /\
    lookup AnyArith_location t.code = SOME (4,AnyArith_code c) /\
    lookup Add_location t.code = SOME (3,Add_code) /\
    lookup Sub_location t.code = SOME (3,Sub_code) /\
    lookup Mul_location t.code = SOME (3,Mul_code) /\
    lookup Div_location t.code = SOME (3,Div_code) /\
    lookup Mod_location t.code = SOME (3,Mod_code)
Proof
  fs [state_rel_def,code_rel_def,stubs_def]
QED

Theorem memory_rel_insert:
   memory_rel c be ts refs sp st m dm
     ([(x,w)] ++ join_env d (toAList (inter l (adjust_set d))) ++ xs) ⇒
    memory_rel c be ts refs sp st m dm
     (join_env (insert dest x d)
        (toAList
           (inter (insert (adjust_var dest) w l)
              (adjust_set (insert dest x d)))) ++ xs)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ match_mp_tac word_ml_inv_insert \\ fs []
QED

Theorem state_rel_IMP_Number_arg:
   state_rel c l1 l2 (call_env xs ss s) (call_env ys ss t) [] locs /\
    n < dimword (:'a) DIV 16 /\ LENGTH ys = LENGTH xs + 1 ==>
    state_rel c l1 l2
      (call_env (xs ++ [Number (& n)]) ss s)
      (call_env (ys ++ [Word (n2w (4 * n):'a word)]) ss t) [] locs
Proof
  fs [state_rel_thm,call_env_def,wordSemTheory.call_env_def] \\ rw []
  THEN1 (Cases_on `ys` \\ fs [lookup_fromList,lookup_fromList2])
  THEN1
   (fs [lookup_fromList,lookup_fromList2,EVEN_adjust_var]
    \\ POP_ASSUM MP_TAC \\ IF_CASES_TAC \\ fs []
    \\ rw [] \\ fs []
    \\ fs [adjust_var_def,adjust_var_DIV_2_ANY])
  \\ fs [fromList2_SNOC,fromList_SNOC,GSYM SNOC_APPEND]
  \\ fs [LEFT_ADD_DISTRIB,GSYM adjust_var_def]
  \\ full_simp_tac std_ss [SNOC_APPEND,GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ simp_tac std_ss [APPEND]
  \\ `n2w (4 * n) = Smallnum (&n)` by
     (fs [good_dimindex_def,dimword_def,Smallnum_def] \\ NO_TAC)
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ full_simp_tac std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ fs [small_int_def,good_dimindex_def]
  \\ rfs [dimword_def]
QED

Theorem state_rel_cut_IMP:
   state_rel c l1 l2 s (t :(α, γ, 'ffi) state) [] locs /\
   cut_state_opt names_opt s = SOME x ==>
   state_rel c l1 l2 x t [] locs
Proof
  Cases_on `names_opt` \\ fs [dataSemTheory.cut_state_opt_def]
  THEN1 (rw [] \\ fs [])
  \\ fs [dataSemTheory.cut_state_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac state_rel_cut_env
QED

Theorem get_vars_1_IMP:
  wordSem$get_vars [x1] s = SOME [v1] ==>
  get_var x1 s = SOME v1
Proof
  fs [wordSemTheory.get_vars_def,AllCaseEqs()]
QED

Theorem get_vars_2_IMP:
   (wordSem$get_vars [x1;x2] s = SOME [v1;v2]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem get_vars_3_IMP:
   (wordSem$get_vars [x1;x2;x3] s = SOME [v1;v2;v3]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2 /\
    get_var x3 s = SOME v3
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem inter_insert_ODD_adjust_set:
   !k. ODD k ==>
      inter (insert (adjust_var dest) w (insert k v s)) (adjust_set t) =
      inter (insert (adjust_var dest) w s) (adjust_set t)
Proof
  fs [spt_eq_thm,wf_inter,lookup_inter_alt,lookup_insert]
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac domain_adjust_set_EVEN \\ fs [EVEN_ODD]
QED

Theorem inter_insert_ODD_adjust_set_alt:
   !k. ODD k ==>
      inter (insert k v s) (adjust_set t) =
      inter s (adjust_set t)
Proof
  fs [spt_eq_thm,wf_inter,lookup_inter_alt,lookup_insert]
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac domain_adjust_set_EVEN \\ fs [EVEN_ODD]
QED

Theorem inter_delete_ODD_adjust_set_alt:
   !k. ODD k ==>
      inter (delete k s) (adjust_set t) =
      inter s (adjust_set t)
Proof
  fs [spt_eq_thm,wf_inter,lookup_inter_alt,lookup_delete]
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac domain_adjust_set_EVEN \\ fs [EVEN_ODD]
QED

Theorem get_vars_termdep[simp]:
   !xs. get_vars xs (t with termdep := t.termdep - 1) = get_vars xs t
Proof
  Induct \\ EVAL_TAC \\ rw [] \\ every_case_tac \\ fs []
QED

Definition join_env_locals_def:
  join_env_locals sl tl =
    join_env sl (toAList (inter tl (adjust_set sl)))
End

Theorem join_env_locals_insert_odd[simp]:
   ODD n ⇒ join_env_locals sl (insert n v ls) = join_env_locals sl ls
Proof
  rw[join_env_locals_def,inter_insert_ODD_adjust_set_alt]
QED

Theorem join_env_locals_insert_dest_odd[simp]:
   ODD n ⇒ join_env_locals sl (insert (adjust_var dest) w (insert n v ls)) = join_env_locals sl (insert (adjust_var dest) w ls)
Proof
  rw[join_env_locals_def,inter_insert_ODD_adjust_set]
QED

Theorem MustTerminate_limit_NOT_0[simp]:
   MustTerminate_limit (:'a) <> 0
Proof
  rewrite_tac [wordSemTheory.MustTerminate_limit_def] \\ fs [dimword_def]
QED

Theorem memory_rel_Temp[simp]:
   memory_rel c be ts refs sp (st |+ (Temp i,w)) m dm vars <=>
    memory_rel c be ts refs sp st m dm vars
Proof
  fs [memory_rel_def,heap_in_memory_store_def,FLOOKUP_UPDATE]
QED

Theorem adjust_var_not_15[simp]:
   adjust_var a2 <> 15
Proof
  metis_tac [EVAL ``EVEN 15``,EVEN_adjust_var]
QED

Theorem get_vars_sing:
   wordSem$get_vars [n] t = SOME x <=> ?x1. get_vars [n] t = SOME [x1] /\ x = [x1]
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs [] \\ EQ_TAC \\ fs []
QED

Theorem word_ml_inv_get_var_IMP[allow_rebind] =
  word_ml_inv_get_vars_IMP
  |> Q.INST [`n`|->`[n1]`,`x`|->`[x1]`] |> GEN_ALL
  |> REWRITE_RULE [get_vars_SOME_IFF,get_vars_SOME_IFF_data,MAP]
  |> SIMP_RULE std_ss [Once get_vars_sing,PULL_EXISTS,get_vars_SOME_IFF,ZIP,APPEND]

val _ = export_theory();
