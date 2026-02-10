(*
   General-purpose word lemmas (bit operations, shifts, alignment,
   bytes_in_memory, good_dimindex, n2w/w2n, etc.)
   used throughout the CakeML development.
*)
Theory wordLemmas
Ancestors
  arithLemmas listLemmas alignment bitstring words
  machine_ieee address[qualified] byte
  list arithmetic rich_list pred_set pair option combin bit
  set_sep
Libs
  boolSimps mp_then dep_rewrite BasicProvers wordsLib
  blastLib[qualified]

val _ = numLib.temp_prefer_num();

(* --- read_bytearray --- *)

Definition read_bytearray_def:
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))
End

Theorem read_bytearray_LENGTH:
   !n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)
Proof
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac
QED

(* --- BIT / LOG2 lemmas --- *)

Theorem BIT_11:
   !n m. (BIT n = BIT m) <=> (n = m)
Proof
  simp[EQ_IMP_THM] >>
  Induct >> simp[BIT0_ODD,FUN_EQ_THM] >- (
    Cases >> simp[] >>
    qexists_tac`1` >> simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  simp[GSYM BIT_DIV2] >>
  Cases >> simp[GSYM BIT_DIV2] >- (
    qexists_tac`1` >>
    simp[BIT_ZERO] >>
    simp[BIT_def,BITS_THM] ) >>
  srw_tac[][] >>
  first_x_assum MATCH_MP_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  first_x_assum(qspec_then`x*2`mp_tac) >>
  simp[arithmeticTheory.MULT_DIV]
QED

Theorem BIT_11_2:
   !n m. (!z. (z < 2 ** (MAX n m)) ==> (BIT n z <=> BIT m z)) <=> (n = m)
Proof
  simp[Once EQ_IMP_THM] >>
  Induct >- (
    simp[] >>
    Cases >> simp[] >>
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  Cases >> simp[] >- (
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  strip_tac >>
  first_x_assum MATCH_MP_TAC >>
  qx_gen_tac`z` >>
  first_x_assum(qspec_then`z*2`mp_tac) >>
  simp[GSYM BIT_DIV2,arithmeticTheory.MULT_DIV] >>
  srw_tac[][] >> first_x_assum MATCH_MP_TAC >>
  full_simp_tac(srw_ss())[arithmeticTheory.MAX_DEF] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  simp[arithmeticTheory.EXP]
QED

Theorem LOG2_TIMES2:
   0 < n ==> (LOG2 (2 * n) = SUC (LOG2 n))
Proof
  srw_tac[][LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1]
QED

Theorem LOG2_TIMES2_1:
   !n. 0 < n ==> (LOG2 (2 * n + 1) = LOG2 (2 * n))
Proof
  srw_tac[][LOG2_def] >>
  MATCH_MP_TAC logrootTheory.LOG_UNIQUE >>
  simp[GSYM LOG2_def,LOG2_TIMES2] >>
  simp[arithmeticTheory.EXP] >>
  conj_tac >- (
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac`2*n` >> simp[] >>
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`2 ** LOG2 n <= X` >- srw_tac[][] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] ) >>
  simp[GSYM arithmeticTheory.ADD1] >>
  match_mp_tac arithmeticTheory.LESS_NOT_SUC >>
  `4:num = 2 * 2` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[Once (GSYM arithmeticTheory.MULT_ASSOC)] >>
  simp[] >>
  conj_asm1_tac >- (
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`X < 2 * 2 ** LOG2 n` >- srw_tac[][] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] >>
    qmatch_abbrev_tac`(a:num) + b < 2 * a` >>
    qsuff_tac`n MOD a < a` >- simp[] >>
    MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
    simp[Abbr`a`] ) >>
  qmatch_abbrev_tac`X <> Y` >>
  qsuff_tac`EVEN X /\ ODD Y` >- metis_tac[arithmeticTheory.EVEN_ODD] >>
  conj_tac >- (
    simp[Abbr`X`,arithmeticTheory.EVEN_EXISTS] >>
    qexists_tac`2 * 2 ** LOG2 n` >>
    simp[] ) >>
  simp[Abbr`Y`,arithmeticTheory.ODD_EXISTS] >>
  metis_tac[]
QED

Theorem C_BIT_11:
   !n m. (!z. (z <= LOG2 (MAX n m)) ==> (BIT z n <=> BIT z m)) <=> (n = m)
Proof
  simp_tac std_ss [Once EQ_IMP_THM] >>
  ho_match_mp_tac binary_induct >>
  simp_tac std_ss [] >>
  conj_tac >- (
    Cases >> simp_tac arith_ss [] >>
    qexists_tac`LOG2 (SUC n)` >>
    simp_tac arith_ss [BIT_LOG2,BIT_ZERO] ) >>
  gen_tac >> strip_tac >>
  simp_tac std_ss [BIT_TIMES2,BIT_TIMES2_1] >>
  srw_tac[][] >- (
    Cases_on`n=0`>>full_simp_tac std_ss []>-(
      Cases_on`m=0`>>full_simp_tac std_ss []>>
      first_x_assum(qspec_then`LOG2 m`mp_tac)>>simp_tac std_ss [BIT_ZERO] >>
      full_simp_tac std_ss [BIT_LOG2]) >>
    `~ODD m` by (
      simp_tac std_ss [SYM BIT0_ODD] >>
      first_x_assum(qspec_then`0`mp_tac) >>
      simp_tac std_ss [] ) >>
    full_simp_tac std_ss [arithmeticTheory.ODD_EVEN] >>
    full_simp_tac std_ss [arithmeticTheory.EVEN_EXISTS] >>
    simp_tac std_ss [arithmeticTheory.EQ_MULT_LCANCEL] >>
    first_x_assum MATCH_MP_TAC >>
    srw_tac[][] >>
    first_x_assum(qspec_then`SUC z`mp_tac) >>
    impl_tac >- (
      full_simp_tac std_ss [arithmeticTheory.MAX_DEF] >>
      srw_tac[][] >> full_simp_tac arith_ss [LOG2_TIMES2] ) >>
    simp_tac std_ss [BIT_TIMES2] ) >>
  Cases_on`n=0`>>full_simp_tac std_ss []>-(
    full_simp_tac std_ss [BIT_ZERO] >>
    Cases_on`m=0`>>full_simp_tac std_ss [BIT_ZERO] >>
    Cases_on`m=1`>>full_simp_tac std_ss []>>
    first_x_assum(qspec_then`LOG2 m`mp_tac) >>
    full_simp_tac std_ss [arithmeticTheory.MAX_DEF,BIT_LOG2] >>
    spose_not_then strip_assume_tac >>
    qspec_then`m`mp_tac logrootTheory.LOG_MOD >>
    full_simp_tac arith_ss [GSYM LOG2_def] ) >>
  `ODD m` by (
    simp_tac std_ss [SYM BIT0_ODD] >>
    first_x_assum(qspec_then`0`mp_tac) >>
    simp_tac std_ss [] ) >>
  full_simp_tac std_ss [arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
  simp_tac std_ss [arithmeticTheory.EQ_MULT_LCANCEL] >>
  first_x_assum MATCH_MP_TAC >>
  srw_tac[][] >>
  first_x_assum(qspec_then`SUC z`mp_tac) >>
  impl_tac >- (
    full_simp_tac std_ss [arithmeticTheory.MAX_DEF] >>
    srw_tac[][] >> full_simp_tac arith_ss [LOG2_TIMES2_1,LOG2_TIMES2] ) >>
  full_simp_tac arith_ss [BIT_TIMES2_1,BIT_TIMES2]
QED

Theorem BIT_num_from_bin_list_leading:
   !l x. EVERY ($> 2) l /\ LENGTH l <= x ==> ~BIT x (num_from_bin_list l)
Proof
  simp[numposrepTheory.num_from_bin_list_def] >>
  srw_tac[][] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH (REVERSE l)` >>
  simp[numposrepTheory.l2n_lt]
QED

(* --- v2w lemmas --- *)

Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w
Proof
EVAL_TAC
QED

Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w
Proof
EVAL_TAC
QED

Theorem v2w_sing:
   v2w [b] = if b then 1w else 0w
Proof
  Cases_on `b` \\ EVAL_TAC
QED

(* --- byte alignment --- *)

Theorem byte_align_extract:
   byte_align (x:word32) = (((31 >< 2) x):word30) @@ (0w:word2)
Proof
  rw[alignmentTheory.byte_align_def]
  \\ rw[alignmentTheory.align_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem byte_align_IN_IMP_IN_range:
   byte_align a IN dm /\
   (dm = { w | low <=+ w /\ w <+ hi }) /\
   byte_aligned low /\ byte_aligned hi ==>
   a IN dm
Proof
  rw[] \\ fs[]
  >- (
    `byte_align a <=+ a` suffices_by metis_tac[WORD_LOWER_EQ_TRANS]
    \\ simp[alignmentTheory.byte_align_def]
    \\ simp[align_ls] )
  \\ Cases_on`byte_aligned a`
    >- metis_tac[alignmentTheory.byte_aligned_def,
                 alignmentTheory.aligned_def,
                 alignmentTheory.byte_align_def]
  \\ match_mp_tac (GEN_ALL aligned_between)
  \\ fs[alignmentTheory.byte_aligned_def]
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
  \\ fs[alignmentTheory.byte_align_def]
QED

(* --- division lemmas --- *)

Theorem MULT_DIV_MULT_LEMMA:
   !m l k. 0 < m /\ 0 < l ==> (m * k) DIV (l * m) = k DIV l
Proof
  rw [] \\ qsuff_tac `k * m DIV (m * l) = k DIV l` THEN1 fs []
  \\ simp [GSYM DIV_DIV_DIV_MULT] \\ simp [MULT_DIV]
QED

Theorem IMP_MULT_DIV_LESS:
   m <> 0 /\ d < k ==> m * (d DIV m) < k
Proof
  strip_tac \\ `0 < m` by decide_tac
  \\ first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] DIVISION))
  \\ disch_then (qspec_then `d` assume_tac)
  \\ decide_tac
QED

Theorem DIV_LESS_DIV:
   n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k
Proof
  strip_tac
  \\ first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] DIVISION))
  \\ disch_then (qspec_then `n` (strip_assume_tac o GSYM))
  \\ first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] DIVISION))
  \\ disch_then (qspec_then `m` (strip_assume_tac o GSYM))
  \\ rfs [] \\ metis_tac [LT_MULT_LCANCEL]
QED

(* --- all_words --- *)

Definition all_words_def:
  (all_words base 0 = {}) /\
  (all_words base (SUC n) = base INSERT (all_words (base + 1w) n))
End

Theorem IN_all_words:
   x IN all_words base n <=> (?i. i < n /\ x = base + n2w i)
Proof
  qid_spec_tac`base`
  \\ Induct_on`n`
  \\ rw[all_words_def, ADD1]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  >- ( qexists_tac`i + 1` \\ simp[GSYM word_add_n2w] )
  \\ Cases_on`i` \\ fs[ADD1]
  \\ disj2_tac
  \\ simp[GSYM word_add_n2w]
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ simp[]
QED

(* --- read_bytearray lemmas --- *)

Theorem read_bytearray_IMP_mem_SOME:
   !p n m ba.
   (read_bytearray p n m = SOME ba) ==>
   !k. k IN all_words p n ==> IS_SOME (m k)
Proof
  Induct_on `n`
  \\ rw[read_bytearray_def,all_words_def]
  \\ fs[CaseEq"option"]
  \\ first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ simp []
QED

Theorem read_bytearray_no_wrap:
   !ptr len.
   IS_SOME (read_bytearray ptr len (m:'a word -> 'b option)) /\
   (!x. IS_SOME (m x) ==> w2n x < dimword(:'a) - 1) /\
   w2n ptr < dimword (:'a)
   ==>
   w2n ptr + len < dimword(:'a)
Proof
  Induct_on`len`
  \\ rw[read_bytearray_def]
  \\ fs[CaseEq"option", IS_SOME_EXISTS, PULL_EXISTS]
  \\ Cases_on`ptr` \\ fs[word_add_n2w, ADD1]
  \\ res_tac \\ fs[] \\ rfs[]
QED

(* --- asm_write_bytearray --- *)

Definition asm_write_bytearray_def:
  (asm_write_bytearray a [] (m:'a word -> word8) = m) /\
  (asm_write_bytearray a (x::xs) m = (a =+ x) (asm_write_bytearray (a+1w) xs m))
End

Theorem mem_eq_imp_asm_write_bytearray_eq:
   !a bs.
    (m1 k = m2 k) ==>
    (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs m2 k)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def]
  \\ rw[APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_unchanged:
   !a bs m z. (x <+ a \/ a + n2w (LENGTH bs) <=+ x) /\
    (w2n a + LENGTH bs < dimword(:'a)) /\ (z = m x)
  ==> (asm_write_bytearray (a:'a word) bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ TRY (
    Cases_on`a` \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
    \\ NO_TAC )
  \\ first_x_assum match_mp_tac
  \\ Cases_on`a`
  \\ Cases_on`x`
  \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
QED

Theorem asm_write_bytearray_id:
   !a bs m.
    (!j. j < LENGTH bs ==> (m (a + n2w j) = EL j bs))
  ==> (asm_write_bytearray (a:'a word) bs m x = m x)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum match_mp_tac
  \\ rw[]
  \\ first_x_assum(qspec_then`SUC j`mp_tac)
  \\ rw[]
  \\ fs[ADD1, GSYM word_add_n2w]
QED

Theorem asm_write_bytearray_unchanged_alt:
   !a bs m z.
      (z = m x) /\ ~(x IN { a + n2w k | k < LENGTH bs }) ==>
      (asm_write_bytearray a bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  THEN1 (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
  \\ first_x_assum match_mp_tac \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then `k + 1` mp_tac)
  \\ fs [GSYM word_add_n2w,ADD1]
QED

Theorem asm_write_bytearray_unchanged_all_words:
   !a bs m z x.
    ~(x IN all_words a (LENGTH bs)) /\ (z = m x) ==>
    (asm_write_bytearray (a:'a word) bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[all_words_def,asm_write_bytearray_def,APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_append:
   !a l1 l2 m.
   w2n a + LENGTH l1 + LENGTH l2 < dimword (:'a) ==>
   (asm_write_bytearray (a:'a word) (l1 ++ l2) m =
    asm_write_bytearray (a + n2w (LENGTH l1)) l2 (asm_write_bytearray a l1 m))
Proof
  Induct_on`l1` \\ rw[asm_write_bytearray_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[]
  >- (
    irule (GSYM asm_write_bytearray_unchanged)
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`a` \\ simp[word_lo_n2w,word_add_n2w,word_ls_n2w]
    \\ fs[] )
  \\ fs[ADD1,GSYM word_add_n2w]
  \\ first_x_assum (qspec_then`a+1w`mp_tac)
  \\ simp[]
  \\ Cases_on`a` \\ fs[word_add_n2w]
  \\ disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ rw[]
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_EL:
   !a bs m x. x < LENGTH bs /\ LENGTH bs < dimword(:'a) ==>
   (asm_write_bytearray (a:'a word) bs m (a + n2w x) = EL x bs)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ Cases_on`x` \\ fs[]
  >- ( fs[addressTheory.WORD_EQ_ADD_CANCEL] )
  \\ first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ simp[ADD1,GSYM word_add_n2w]
  \\ metis_tac[WORD_ADD_ASSOC,WORD_ADD_COMM]
QED

(* --- word comparison lemmas --- *)

Theorem n2w_lt:
   (0w:'a word) < n2w a /\ (0w:'a word) < n2w b /\
   a < dimword (:'a) /\ b < dimword (:'a)
   ==>
   ((n2w a:'a word) < (n2w b:'a word) <=> a < b)
Proof
  simp[word_lt_n2w]
QED

Theorem n2w_le:
   (0w:'a word) < n2w a /\ (0w:'a word) < n2w b /\
   a < dimword (:'a) /\ b < dimword (:'a)
   ==>
   ((n2w a:'a word) <= (n2w b:'a word) <=> a <= b)
Proof
  srw_tac[][WORD_LESS_OR_EQ,LESS_OR_EQ]
  \\ metis_tac[n2w_lt]
QED

Theorem word_lt_0w:
   2 * n < dimword (:'a) ==> ((0w:'a word) < n2w n <=> 0 < n)
Proof
  simp[WORD_LT]
  \\ Cases_on`0 < n` \\ simp[]
  \\ simp[word_msb_n2w_numeric]
  \\ simp[NOT_LESS_EQUAL]
  \\ simp[wordsTheory.INT_MIN_def]
  \\ simp[dimword_def]
  \\ Cases_on`dimindex(:'a)`\\simp[]
  \\ simp[EXP]
QED

Theorem word_sub_lt:
   0w < n /\ 0w < m /\ n <= m ==> m - n < m
Proof
  rpt strip_tac
  \\ Cases_on`m`>>Cases_on`n`
  \\ qpat_x_assum`_ <= _`mp_tac
  \\ asm_simp_tac std_ss [n2w_le]
  \\ simp_tac std_ss [GSYM n2w_sub]
  \\ strip_tac
  \\ qmatch_assum_rename_tac`a:num <= b`
  \\ Cases_on`a=b`>-full_simp_tac(srw_ss())[]
  \\ `a < b` by simp[]
  \\ `0 < a` by (Cases_on`a`\\full_simp_tac(srw_ss())[]\\metis_tac[WORD_LESS_REFL])
  \\ `b - a < b` by simp[]
  \\ Cases_on`0w < n2w (b - a)`
  >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[n2w_lt]
    \\ simp[])
  \\ full_simp_tac(srw_ss())[word_lt_n2w,LET_THM]
QED

(* --- bytes_in_memory --- *)

Definition bytes_in_memory_def:
  (bytes_in_memory a [] m dm <=> T) /\
  (bytes_in_memory a ((x:word8)::xs) m dm <=>
     (m a = x) /\ a IN dm /\ bytes_in_memory (a + 1w) xs m dm)
End

Theorem bytes_in_memory_APPEND:
   !l1 l2 pc mem mem_domain.
      bytes_in_memory pc (l1 ++ l2) mem mem_domain <=>
      bytes_in_memory pc l1 mem mem_domain /\
      bytes_in_memory (pc + n2w (LENGTH l1)) l2 mem mem_domain
Proof
  Induct
  THEN ASM_SIMP_TAC list_ss
         [bytes_in_memory_def, wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w,
          GSYM wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD1]
  THEN DECIDE_TAC
QED

Theorem bytes_in_memory_change_domain:
   !a bs m md1 md2.
    bytes_in_memory a bs m md1 /\
   (!n. n < LENGTH bs /\ a + n2w n IN md1 ==> a + n2w n IN md2)
  ==> bytes_in_memory a bs m md2
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]
QED

Theorem bytes_in_memory_change_mem:
   !a bs m1 m2 md.
    bytes_in_memory a bs m1 md /\
   (!n. n < LENGTH bs ==> (m1 (a + n2w n) = m2 (a + n2w n)))
  ==> bytes_in_memory a bs m2 md
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]
QED

Theorem bytes_in_memory_EL:
   !a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> (m (a + n2w k) = EL k bs)
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ simp[ADD1, GSYM word_add_n2w]
QED

Theorem bytes_in_memory_in_domain:
   !a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> ((a + n2w k) IN md)
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
  \\ simp[ADD1, GSYM word_add_n2w]
QED

(* --- bytes_in_mem --- *)

Definition bytes_in_mem_def:
  (bytes_in_mem a [] m md k <=> T) /\
  (bytes_in_mem a (b::bs) m md k <=>
     a IN md /\ ~(a IN k) /\ (m a = b) /\
     bytes_in_mem (a+1w) bs m md k)
End

Theorem bytes_in_mem_IMP:
   !xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,bytes_in_memory_def]
QED

(* --- set_sep --- *)

Theorem fun2set_disjoint_union:
      DISJOINT d1 d2 /\
  p (fun2set (m,d1)) /\
   q (fun2set (m,d2))
   ==> (p * q) (fun2set (m,d1 UNION d2))
Proof
  rw[set_sepTheory.fun2set_def,set_sepTheory.STAR_def,set_sepTheory.SPLIT_def]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ simp[EXTENSION]
  \\ conj_tac >- metis_tac[]
  \\ fs[IN_DISJOINT,FORALL_PROD]
QED

(* --- WORD_LS_IMP --- *)

Theorem WORD_LS_IMP:
   a <=+ b ==>
    ?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)
Proof
  Cases_on `a` \\ Cases_on `b` \\ fs [WORD_LS]
  \\ fs [markerTheory.Abbrev_def]
  \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ rw [] THEN1
   (rewrite_tac [GSYM word_sub_def]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_SUB])
  \\ Cases_on `w` \\ fs [WORD_LO,word_add_n2w]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename1 `k < m:num` \\ qexists_tac `k - n` \\ fs []
QED

(* --- good_dimindex and get/set_byte --- *)

Definition good_dimindex_def:
  good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64
End

Theorem good_dimindex_get_byte_set_byte:
  good_dimindex (:'a) ==>
    (get_byte a (set_byte (a:'a word) b w be) be = b)
Proof
  strip_tac \\
  match_mp_tac get_byte_set_byte \\
  fs[good_dimindex_def]
QED

Theorem byte_index_LESS_IMP[local]:
  (dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
    byte_index (a:'a word) be < byte_index (a':'a word) be /\ i < 8 ==>
    byte_index a be + i < byte_index a' be /\
    byte_index a be <= i + byte_index a' be /\
    byte_index a be + 8 <= i + byte_index a' be /\
    i + byte_index a' be < byte_index a be + dimindex (:'a)
Proof
  fs [byte_index_def,LET_DEF] \\ Cases_on `be` \\ fs []
  \\ rpt strip_tac \\ rfs [] \\ fs []
  \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ decide_tac
QED

Theorem NOT_w2w_bit[local]:
  8 <= i /\ i < dimindex (:'b) ==> ~((w2w:word8->'b word) w ' i)
Proof
  rpt strip_tac \\ rfs [w2w] \\ decide_tac
QED

val LESS4 = DECIDE ``n < 4 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``
val LESS8 = DECIDE ``n < 8 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                               (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``

Theorem DIV_EQ_DIV_IMP[local]:
  0 < d /\ n <> n' /\ (n DIV d * d = n' DIV d * d) ==> n MOD d <> n' MOD d
Proof
  rpt strip_tac \\ Q.PAT_X_ASSUM `n <> n'` mp_tac \\ fs []
  \\ MP_TAC (Q.SPEC `d` DIVISION) \\ fs []
  \\ rpt strip_tac \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs []
QED

Theorem get_byte_set_byte_diff:
   good_dimindex (:'a) /\ a <> a' /\ (byte_align a = byte_align a') ==>
    (get_byte a (set_byte (a':'a word) b w be) be = get_byte a w be)
Proof
  fs [get_byte_def,set_byte_def,LET_DEF] \\ rpt strip_tac
  \\ `byte_index a be <> byte_index a' be` by
   (fs [good_dimindex_def]
    THENL
     [`w2n a MOD 4 < 4 /\ w2n a' MOD 4 < 4` by fs []
      \\ `w2n a MOD 4 <> w2n a' MOD 4` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 4 * 4 + n MOD 4) < dimword (:'a) /\
            (n' DIV 4 * 4 + n' MOD 4) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<4:num``])
        \\ `(n DIV 4 * 4) < dimword (:'a) /\
            (n' DIV 4 * 4) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs []),
      `w2n a MOD 8 < 8 /\ w2n a' MOD 8 < 8` by fs []
      \\ `w2n a MOD 8 <> w2n a' MOD 8` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 8 * 8 + n MOD 8) < dimword (:'a) /\
            (n' DIV 8 * 8 + n' MOD 8) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<8:num``])
        \\ `(n DIV 8 * 8) < dimword (:'a) /\
            (n' DIV 8 * 8) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs [])]
    \\ full_simp_tac bool_ss [LESS4,LESS8] \\ fs [] \\ rfs []
    \\ fs [byte_index_def,LET_DEF] \\ rw [])
  \\ fs [fcpTheory.CART_EQ,w2w,good_dimindex_def] \\ rpt strip_tac
  \\ `i' < dimindex (:'a)` by decide_tac
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i' + byte_index a be < dimindex (:'a)` by
   (fs [byte_index_def,LET_DEF] \\ rw []
    \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ decide_tac)
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ fs [DECIDE ``m <> n <=> m < n \/ n < m:num``]
  \\ Cases_on `w ' (i' + byte_index a be)` \\ fs []
  \\ imp_res_tac byte_index_LESS_IMP
  \\ fs [w2w] \\ TRY (match_mp_tac NOT_w2w_bit)
  \\ fs [] \\ decide_tac
QED

(* --- size lemmas --- *)

Theorem list_size_pair_size_MAP_FST_SND:
  list_size (pair_size f g) ls =
  list_size f (MAP FST ls) +
  list_size g (MAP SND ls)
Proof
  Induct_on`ls`>>simp[]>>
  Cases>>rw[]
QED

Theorem MEM_list_size:
  MEM x ls ==>
  f x <= list_size f ls
Proof
  Induct_on`ls`>>simp[]>>
  rw[]>>gvs[]
QED

