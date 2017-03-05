open preamble mlstringTheory

val _ = new_theory"mlint";

(* TODO: move *)
val DIV_EQ_0 = Q.store_thm("DIV_EQ_0",
  `1 < b ==> ((n DIV b = 0) = (n < b))`,
  metis_tac[numposrepTheory.DIV_0_IMP_LT,LESS_DIV_EQ_ZERO]);

val n2l_DIV_MOD = Q.store_thm("n2l_DIV_MOD",
  `!b n k. 1 < b /\ 0 < k /\ b ** k <= n ==>
   (n2l b (n MOD (b ** k)) ++ REPLICATE (k - LENGTH (n2l b (n MOD (b ** k)))) 0 ++
    n2l b (n DIV (b ** k)) = n2l b n)`,
  ho_match_mp_tac numposrepTheory.n2l_ind
  \\ rw[]
  \\ Cases_on`b < 2` \\ fs[]
  \\ Cases_on`n < b` \\ fs[]
  >- ( `b <= b ** k` by ( Cases_on`k` \\ fs[EXP] ) \\ fs[] )
  \\ Cases_on`k` \\ fs[EXP]
  \\ fs[GSYM DIV_DIV_DIV_MULT]
  \\ fs[DIV_MOD_MOD_DIV]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ qmatch_assum_rename_tac`b * b ** k <= n`
  \\ Cases_on`k=0` \\ fs[EXP]
  >- (
    rw[Once numposrepTheory.n2l_def,REPLICATE_NIL] \\
    rw[numposrepTheory.LENGTH_n2l])
  \\ simp[Once numposrepTheory.n2l_def]
  \\ simp[MOD_MULT_MOD]
  \\ fs[numposrepTheory.LENGTH_n2l]
  \\ first_x_assum(qspec_then`k`mp_tac)
  \\ impl_tac >- simp[X_LE_DIV]
  \\ disch_then(assume_tac o SYM) \\ simp[]
  \\ rfs[DIV_EQ_0]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- simp[logrootTheory.LOG_DIV,ADD1]
  \\ IF_CASES_TAC \\ fs[]
  >- (
    `0 < b ** k` by simp[] \\
    `0 < b * b ** k` by simp[LESS_MULT2] \\
    fs[MOD_EQ_0_DIVISOR,ZERO_DIV,Once numposrepTheory.n2l_def]
    \\ Cases_on`k` \\ fs[REPLICATE]
    \\ metis_tac[MULT_ASSOC] )
  \\ conj_asm1_tac
  >- (
    qspecl_then[`b ** k`,`b`]mp_tac MOD_MULT_MOD
    \\ simp[]
    \\ disch_then(qspec_then`n`mp_tac)
    \\ simp[LESS_MOD])
  \\ simp[]
  \\ `n MOD b DIV b = 0` by simp[DIV_EQ_0]
  \\ simp[Once numposrepTheory.n2l_def]
  \\ simp[GSYM REPLICATE,ADD1]
  \\ `LOG b (n MOD b) = 0`
  by ( simp[logrootTheory.LOG_EQ_0] )
  \\ simp[]);
(* -- *)

val toChar_def = Define`
  toChar digit = if digit < 10 then CHR (ORD #"0" + digit)
  else CHR (ORD #"A" + digit - 10)`;

val toChar_HEX = Q.store_thm("toChar_HEX",
  `d < 16 ⇒ (toChar d = HEX d)`,
  strip_tac \\ rpt(fs[Once NUMERAL_LESS_THM] >- EVAL_TAC));

(* This should be smaller than the maximum smallint supported by the compiler
(see bvl_to_bviTheory for that. 2**28-1?) Also it must be a power of the radix
*)
val maxSmall_DEC_def = Define`maxSmall_DEC = 100000000n`;
val padLen_DEC_def = Define`
  padLen_DEC = LOG 10 maxSmall_DEC`;
val padLen_DEC_eq = save_thm("padLen_DEC_eq",CONV_RULE(RAND_CONV EVAL)padLen_DEC_def);

(* TODO: this might all be faster (less allocation in particular) using byte
arrays (and therefore not in pure) Without a strcat primitive, though, this way
could still make sense. *)

val zero_pad_def = Define`
  (zero_pad 0 acc = acc) ∧
  (zero_pad (SUC n) acc = zero_pad n (#"0" :: acc))`;

val zero_pad_thm = Q.store_thm("zero_pad_thm",
  `∀n acc. zero_pad n acc = REPLICATE n #"0" ++ acc`,
  Induct \\ rw[GSYM SNOC_REPLICATE,zero_pad_def] \\ EVAL_TAC);

val simple_toChars_def = Define`
  simple_toChars pad i acc =
    if i < 10 then zero_pad (pad-1) (toChar i :: acc)
    else simple_toChars (pad-1) (i DIV 10) (toChar (i MOD 10) :: acc)`;
val simple_toChars_ind = theorem"simple_toChars_ind";

val simple_toChars_thm = Q.store_thm("simple_toChars_thm",
  `∀pad i acc. simple_toChars pad i acc =
    REPLICATE (pad - LENGTH (num_to_dec_string i)) #"0" ++ num_to_dec_string i ++ acc`,
  ho_match_mp_tac simple_toChars_ind \\
  rw[ASCIInumbersTheory.num_to_dec_string_def,
     ASCIInumbersTheory.n2s_def] \\
  rw[Once simple_toChars_def]
  >- ( fs[NUMERAL_LESS_THM,zero_pad_thm] \\ EVAL_TAC )
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS,ADD1]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ match_mp_tac toChar_HEX
  \\ `i MOD 10 < 10` by simp[MOD_LESS]
  \\ rw[]);

val toChars_def = tDefine"toChars"`
  toChars chunk rest acc =
    if rest = 0 then simple_toChars 0 chunk acc
    else if rest < maxSmall_DEC then
      simple_toChars 0 rest
        (simple_toChars padLen_DEC chunk acc)
    else
      toChars (rest MOD maxSmall_DEC) (rest DIV maxSmall_DEC)
        (simple_toChars padLen_DEC chunk acc)`
(wf_rel_tac`measure (FST o SND)`
 \\ rw[maxSmall_DEC_def,DIV_LT_X] \\ fs[maxSmall_DEC_def]);
val toChars_ind = theorem"toChars_ind";

val toChars_thm = Q.store_thm("toChars_thm",
  `∀chunk rest acc. chunk < maxSmall_DEC ⇒
    (toChars chunk rest acc =
      num_to_dec_string (rest * maxSmall_DEC + chunk) ++ acc)`,
  ho_match_mp_tac toChars_ind
  \\ rw[]
  \\ rw[Once toChars_def]
  \\ rw[simple_toChars_thm,REPLICATE]
  \\ TRY (
    qspec_then`maxSmall_DEC`mp_tac DIVISION
    \\ impl_tac >- EVAL_TAC
    \\ disch_then(qspec_then`rest`mp_tac)
    \\ disch_then(CHANGED_TAC o SUBST1_TAC o SYM o ONCE_REWRITE_RULE[MULT_COMM] o CONJUNCT1))
  \\ rw[ASCIInumbersTheory.num_to_dec_string_def,ASCIInumbersTheory.n2s_def]
  \\ qspecl_then[`10`,`chunk + rest * maxSmall_DEC`,`padLen_DEC`]mp_tac n2l_DIV_MOD
  \\ (impl_tac >- ( EVAL_TAC \\ simp[] ))
  \\ disch_then (SUBST1_TAC o SYM)
  \\ `10 ** padLen_DEC = maxSmall_DEC` by EVAL_TAC
  \\ pop_assum (SUBST_ALL_TAC)
  \\ simp[GSYM MAP_REVERSE,REVERSE_REPLICATE,map_replicate]
  \\ qspecl_then[`maxSmall_DEC`,`chunk`]mp_tac DIV_MULT
  \\ simp[]);

val toString_def = Define`
  toString i =
    if 0i ≤ i ∧ i < 10 then
      str (toChar (Num (ABS i)))
    else
      implode ((if i < 0i then "~" else "")++
               (toChars (Num (ABS i) MOD maxSmall_DEC) (Num (ABS i) DIV maxSmall_DEC) ""))`;

val toString_thm = Q.store_thm("toString_thm",
  `toString i = implode ((if i < 0i then "~" else "") ++ num_to_dec_string (Num (ABS i)))`,
  rw[toString_def]
  >- (`F` by intLib.COOPER_TAC)
  >- (
    rw[str_def]
    \\ AP_TERM_TAC
    \\ `Num (ABS i) < 10` by intLib.COOPER_TAC
    \\ simp[toChar_HEX]
    \\ simp[ASCIInumbersTheory.num_to_dec_string_def]
    \\ simp[ASCIInumbersTheory.n2s_def]
    \\ simp[Once numposrepTheory.n2l_def])
  \\ (
    AP_TERM_TAC \\ simp[]
    \\ `0 < maxSmall_DEC` by EVAL_TAC
    \\ simp[toChars_thm]
    \\ qspec_then`maxSmall_DEC`mp_tac DIVISION
    \\ simp[] ));

val _ = export_theory();
