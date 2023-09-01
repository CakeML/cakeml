(*
  A theory about byte-level manipulation of machine words.
*)

open HolKernel boolLib bossLib dep_rewrite Parse
     arithmeticTheory rich_listTheory wordsTheory

val _ = new_theory "byte";

val _ = set_grammar_ancestry ["arithmetic", "list", "words"];
val _ = temp_tight_equality();

(* Get and set bytes in a word *)

Definition byte_index_def:
  byte_index (a:'a word) is_bigendian =
    let d = dimindex (:'a) DIV 8 in
      if is_bigendian then 8 * ((d - 1) - w2n a MOD d) else 8 * (w2n a MOD d)
End

Definition get_byte_def:
  get_byte (a:'a word) (w:'a word) is_bigendian =
    (w2w (w >>> byte_index a is_bigendian)):word8
End

Definition word_slice_alt_def:
  (word_slice_alt h l (w:'a word) :'a word) = FCP i. l <= i /\ i < h /\ w ' i
End

Definition set_byte_def[nocompute]:
  set_byte (a:'a word) (b:word8) (w:'a word) is_bigendian =
    let i = byte_index a is_bigendian in
      (word_slice_alt (dimindex (:'a)) (i + 8) w
       || w2w b << i
       || word_slice_alt i 0 w)
End

Theorem set_byte_32[compute]:
  set_byte a b (w:word32) be =
    let i = byte_index a be in
      if i = 0  then w2w b       || (w && 0xFFFFFF00w) else
      if i = 8  then w2w b << 8  || (w && 0xFFFF00FFw) else
      if i = 16 then w2w b << 16 || (w && 0xFF00FFFFw) else
                     w2w b << 24 || (w && 0x00FFFFFFw)
Proof
  fs [set_byte_def]
  \\ qsuff_tac ‘byte_index a be = 0 ∨
                byte_index a be = 8 ∨
                byte_index a be = 16 ∨
                byte_index a be = 24’
  THEN1 (rw [] \\ fs [word_slice_alt_def] \\ blastLib.BBLAST_TAC)
  \\ fs [byte_index_def]
  \\ ‘w2n a MOD 4 < 4’ by fs [MOD_LESS] \\ rw []
QED

Theorem set_byte_64[compute]:
  set_byte a b (w:word64) be =
    let i = byte_index a be in
      if i = 0  then w2w b       || (w && 0xFFFFFFFFFFFFFF00w) else
      if i = 8  then w2w b << 8  || (w && 0xFFFFFFFFFFFF00FFw) else
      if i = 16 then w2w b << 16 || (w && 0xFFFFFFFFFF00FFFFw) else
      if i = 24 then w2w b << 24 || (w && 0xFFFFFFFF00FFFFFFw) else
      if i = 32 then w2w b << 32 || (w && 0xFFFFFF00FFFFFFFFw) else
      if i = 40 then w2w b << 40 || (w && 0xFFFF00FFFFFFFFFFw) else
      if i = 48 then w2w b << 48 || (w && 0xFF00FFFFFFFFFFFFw) else
                     w2w b << 56 || (w && 0x00FFFFFFFFFFFFFFw)
Proof
  fs [set_byte_def]
  \\ qsuff_tac ‘byte_index a be = 0 ∨
                byte_index a be = 8 ∨
                byte_index a be = 16 ∨
                byte_index a be = 24 ∨
                byte_index a be = 32 ∨
                byte_index a be = 40 ∨
                byte_index a be = 48 ∨
                byte_index a be = 56’
  THEN1 (rw [] \\ fs [word_slice_alt_def] \\ blastLib.BBLAST_TAC)
  \\ fs [byte_index_def]
  \\ ‘w2n a MOD 8 < 8’ by fs [MOD_LESS] \\ rw []
QED

Theorem set_byte_change_a:
  w2n (a:α word) MOD (dimindex(:α) DIV 8) = w2n a' MOD (dimindex(:α) DIV 8) ⇒
    set_byte a b w be = set_byte a' b w be
Proof
  rw[set_byte_def,byte_index_def]
QED

Theorem get_byte_set_byte:
  8 ≤ dimindex(:α) ⇒
  (get_byte a (set_byte (a:'a word) b w be) be = b)
Proof
  fs [get_byte_def,set_byte_def]
  \\ fs [fcpTheory.CART_EQ,w2w] \\ rpt strip_tac
  \\ `i < dimindex (:'a)` by fs[dimindex_8]
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i + byte_index a be < dimindex (:'a)` by (
    fs [byte_index_def,LET_DEF]
    \\ qmatch_goalsub_abbrev_tac`_ MOD dd`
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac`i + 8 * (dd-1)`
    \\ `0 < dd` by fs[Abbr`dd`, X_LT_DIV, NOT_LESS, dimindex_8]
    \\ conj_tac
    >- (
      rw[]
      \\ `w2n a MOD dd < dd` by (match_mp_tac MOD_LESS \\ decide_tac)
      \\ simp[] )
    \\ match_mp_tac LESS_LESS_EQ_TRANS
    \\ qexists_tac`8 * dd`
    \\ simp[LEFT_SUB_DISTRIB]
    \\ fs[dimindex_8]
    \\ qspec_then`8`mp_tac DIVISION
    \\ impl_tac >- simp[]
    \\ disch_then(qspec_then`dimindex(:α)`(SUBST1_TAC o CONJUNCT1))
    \\ simp[] )
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ `~(i + byte_index a be < byte_index a be)` by decide_tac
  \\ fs[dimindex_8]
QED

(* Convert between lists of bytes and words *)

Definition bytes_in_word_def:
  bytes_in_word = n2w (dimindex (:'a) DIV 8):'a word
End

Definition word_of_bytes_def:
  (word_of_bytes be a [] = 0w) /\
  (word_of_bytes be a (b::bs) =
     set_byte a b (word_of_bytes be (a+1w) bs) be)
End

Definition words_of_bytes_def:
  (words_of_bytes be [] = ([]:'a word list)) /\
  (words_of_bytes be bytes =
     let xs = TAKE (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
     let ys = DROP (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
       word_of_bytes be 0w xs :: words_of_bytes be ys)
Termination
  WF_REL_TAC `measure (LENGTH o SND)` \\ fs []
End

Theorem LENGTH_words_of_bytes:
   8 ≤ dimindex(:'a) ⇒
   ∀be ls.
   (LENGTH (words_of_bytes be ls : 'a word list) =
    LENGTH ls DIV (w2n (bytes_in_word : 'a word)) +
    MIN 1 (LENGTH ls MOD (w2n (bytes_in_word : 'a word))))
Proof
  strip_tac
  \\ recInduct words_of_bytes_ind
  \\ `1 ≤ w2n bytes_in_word`
  by (
    simp[bytes_in_word_def,dimword_def]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ rw[DIV_LT_X, X_LT_DIV, X_LE_DIV]
    \\ match_mp_tac LESS_TRANS
    \\ qexists_tac`2 ** dimindex(:'a)`
    \\ simp[X_LT_EXP_X] )
  \\ simp[words_of_bytes_def]
  \\ rw[ADD1]
  \\ `MAX 1 (w2n (bytes_in_word:'a word)) = w2n (bytes_in_word:'a word)`
      by rw[MAX_DEF]
  \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`(m - n) DIV _`
  \\ Cases_on`m < n` \\ fs[]
  >- (
    `m - n = 0` by fs[]
    \\ simp[]
    \\ simp[LESS_DIV_EQ_ZERO]
    \\ rw[MIN_DEF]
    \\ fs[Abbr`m`] )
  \\ simp[SUB_MOD]
  \\ qspec_then`1`(mp_tac o GEN_ALL)(Q.GEN`q`DIV_SUB) \\ fs[]
  \\ disch_then kall_tac
  \\ Cases_on`m MOD n = 0` \\ fs[]
  >- (
    DEP_REWRITE_TAC[SUB_ADD]
    \\ fs[X_LE_DIV] )
  \\ `MIN 1 (m MOD n) = 1` by simp[MIN_DEF]
  \\ fs[]
  \\ `m DIV n - 1 + 1 = m DIV n` suffices_by fs[]
  \\ DEP_REWRITE_TAC[SUB_ADD]
  \\ fs[X_LE_DIV]
QED

Theorem words_of_bytes_append:
   0 < w2n(bytes_in_word:'a word) ⇒
   ∀l1 l2.
   (LENGTH l1 MOD w2n (bytes_in_word:'a word) = 0) ⇒
   (words_of_bytes be (l1 ++ l2) : 'a word list =
    words_of_bytes be l1 ++ words_of_bytes be l2)
Proof
  strip_tac
  \\ gen_tac
  \\ completeInduct_on`LENGTH l1`
  \\ rw[]
  \\ Cases_on`l1` \\ fs[]
  >- EVAL_TAC
  \\ rw[words_of_bytes_def]
  \\ fs[PULL_FORALL]
  >- (
    simp[TAKE_APPEND]
    \\ qmatch_goalsub_abbrev_tac`_ ++ xx`
    \\ `xx = []` suffices_by rw[]
    \\ simp[Abbr`xx`]
    \\ fs[ADD1]
    \\ rfs[MOD_EQ_0_DIVISOR]
    \\ Cases_on`d` \\ fs[] )
  \\ simp[DROP_APPEND]
  \\ qmatch_goalsub_abbrev_tac`_ ++ DROP n l2`
  \\ `n = 0`
  by (
    simp[Abbr`n`]
    \\ rfs[MOD_EQ_0_DIVISOR]
    \\ Cases_on`d` \\ fs[ADD1] )
  \\ simp[]
  \\ first_x_assum irule
  \\ simp[]
  \\ rfs[MOD_EQ_0_DIVISOR, ADD1]
  \\ Cases_on`d` \\ fs[MULT]
  \\ simp[MAX_DEF]
  \\ IF_CASES_TAC \\ fs[NOT_LESS]
  >- metis_tac[]
  \\ Cases_on`w2n (bytes_in_word:'a word)` \\ fs[] \\ rw[]
  \\ Cases_on`n''` \\ fs[] \\ metis_tac []
QED

Theorem words_of_bytes_append_word:
  0 < LENGTH l1 ∧ (LENGTH l1 = w2n (bytes_in_word:'a word)) ⇒
  (words_of_bytes be (l1 ++ l2) = word_of_bytes be (0w:'a word) l1 :: words_of_bytes be l2)
Proof
  rw[]
  \\ Cases_on`l1` \\ rw[words_of_bytes_def] \\ fs[]
  \\ fs[MAX_DEF]
  \\ qabbrev_tac ‘k = w2n (bytes_in_word:'a word)’
  \\ fs[ADD1]
  \\ rw[TAKE_APPEND,DROP_APPEND,DROP_LENGTH_NIL] \\ fs[]
QED

Definition bytes_to_word_def:
  bytes_to_word k a bs w be =
    if k = 0:num then w else
      case bs of
      | [] => w
      | (b::bs) => set_byte a b (bytes_to_word (k-1) (a+1w) bs w be) be
End

Theorem bytes_to_word_eq:
  bytes_to_word 0 a bs w be = w ∧
  bytes_to_word k a [] w be = w ∧
  bytes_to_word (SUC k) a (b::bs) w be =
    set_byte a b (bytes_to_word k (a+1w) bs w be) be
Proof
  rw [] \\ simp [Once bytes_to_word_def]
QED

Theorem word_of_bytes_bytes_to_word:
  ∀be a bs k.
    LENGTH bs ≤ k ⇒
    (word_of_bytes be a bs = bytes_to_word k a bs 0w be)
Proof
  Induct_on`bs`
  >- (
    EVAL_TAC
    \\ Cases_on`k`
    \\ EVAL_TAC
    \\ rw[] )
  \\ rw[word_of_bytes_def]
  \\ Cases_on`k` \\ fs[]
  \\ rw[Once bytes_to_word_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ fs[]
QED

Theorem bytes_to_word_same:
  ∀bw k b1 w be b2.
    (∀n. n < bw ⇒ n < LENGTH b1 ∧ n < LENGTH b2 ∧ EL n b1 = EL n b2)
    ⇒
    (bytes_to_word bw k b1 w be = bytes_to_word bw k b2 w be)
Proof
  ho_match_mp_tac bytes_to_word_ind \\ rw []
  \\ once_rewrite_tac [bytes_to_word_def] \\ rw []
  \\ Cases_on`b1` \\ fs[]
  >- (first_x_assum(qspec_then`0`mp_tac) \\ simp[])
  \\ Cases_on`b2` \\ fs[]
  >- (first_x_assum(qspec_then`0`mp_tac) \\ simp[])
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- simp[]
  \\ simp_tac(srw_ss())[] \\ rw[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ gen_tac \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[]
QED

Definition word_to_bytes_aux_def: (* length, 'a word, endianness *)
  word_to_bytes_aux 0 (w:'a word) be = [] ∧
  word_to_bytes_aux (SUC n) w be =
    (word_to_bytes_aux n w be) ++ [get_byte (n2w n) w be]
End
(* cyclic repeat as get_byte does when length > bytes_in_word for 'a*)

Definition word_to_bytes_def:
  word_to_bytes (w:'a word) be =
  word_to_bytes_aux (dimindex (:'a) DIV 8) w be
End

Theorem LENGTH_word_to_bytes:
  LENGTH (word_to_bytes_aux k (w:'a word) be) = k
Proof
  Induct_on ‘k’>>simp[Once word_to_bytes_aux_def]
QED

Theorem word_to_bytes_EL:
  ∀i. i < k ⇒ EL i (word_to_bytes_aux k (w:'a word) be) = get_byte (n2w i) w be
Proof
  Induct_on ‘k’>>rw[]>>
  once_rewrite_tac[word_to_bytes_aux_def]>>
  simp[Once listTheory.EL_APPEND_EQN]>>
  gs[LENGTH_word_to_bytes]>>
  IF_CASES_TAC>>fs[NOT_LESS]>>
  ‘i = k’ by fs[]>>fs[]
QED

Theorem byte_index_cycle[simp]:
  8 ≤ dimindex (:'a) ⇒
  byte_index (n2w ((w2n (a:'a word)) MOD (dimindex (:'a) DIV 8)):'a word) be = byte_index a be
Proof
  strip_tac>>
  simp[byte_index_def]>>
  ‘0 < dimindex(:'a) DIV 8’
    by (CCONTR_TAC>>fs[NOT_LESS]>>
        fs[DIV_EQ_0])>>
  ‘w2n a MOD (dimindex (:'a) DIV 8) < dimword (:'a)’
    by (irule LESS_EQ_LESS_TRANS>>
        irule_at Any w2n_lt>>
        irule_at Any MOD_LESS_EQ>>fs[])>>
  simp[MOD_MOD]
QED

Theorem get_byte_cycle[simp]:
  8 ≤ dimindex (:'a) ⇒
  get_byte (n2w ((w2n (a:'a word)) MOD (dimindex (:'a) DIV 8)):'a word) w be
  = get_byte a w be
Proof
  rw[get_byte_def]
QED

Theorem set_byte_cycle[simp]:
  8 ≤ dimindex (:'a) ⇒
  set_byte (n2w ((w2n (a:'a word)) MOD (dimindex (:'a) DIV 8)):'a word) b w be
  = set_byte a b w be
Proof
  rw[set_byte_def]
QED

Theorem word_to_bytes_cycle:
  8 ≤ dimindex (:'a) ∧ k < dimword (:'a) ⇒
  (∀i. i < k ⇒
       EL (i MOD (dimindex (:'a) DIV 8)) (word_to_bytes_aux k w be) =
       EL i (word_to_bytes_aux k (w:'a word) be))
Proof
  rpt strip_tac>>
  ‘0 < dimindex (:'a) DIV 8’
  by (irule LESS_LESS_EQ_TRANS>>
      irule_at Any DIV_LE_MONOTONE>>
      first_x_assum $ irule_at Any>>simp[])>>
  ‘i MOD (dimindex (:'a) DIV 8) ≤ i’ by fs[MOD_LESS_EQ]>>
  simp[word_to_bytes_EL]>>
  ‘n2w (i MOD (dimindex (:α) DIV 8)) =
   n2w ((w2n (n2w i:'a word)) MOD (dimindex (:α) DIV 8)):'a word’
    by simp[]>>
  pop_assum (fn h => rewrite_tac[h])>>
  simp[word_to_bytes_EL]
QED

Theorem word_to_byte_aux_1[simp]:
  word_to_bytes_aux 1 (w:'a word) be = [get_byte 0w w be]
Proof
  rewrite_tac[ONE]>>
  rw[word_to_bytes_aux_def]
QED

Theorem TAKE_SNOC_EQ[simp]:
  m ≤ LENGTH ls ⇒ TAKE m (SNOC x ls) = TAKE m ls
Proof
  rw[TAKE_APPEND1]
QED

Theorem word_slice_alt_word_slice:
  h ≤ dimindex (:'a) ⇒
  word_slice_alt (SUC h) l w = word_slice h l (w:'a word)
Proof
  rw[word_slice_alt_def,word_slice_def]>>
  simp[GSYM WORD_EQ]>>rpt strip_tac>>
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]>>
  simp[EQ_IMP_THM]>>rw[]
QED

Theorem word_slice_shift:
  h < dimindex (:'a) ⇒
  word_slice h l (w:'a word) = w ⋙ l ≪ l ≪ (dimindex (:'a) - (SUC h)) ⋙ (dimindex (:'a) - (SUC h))
Proof
  strip_tac>>
  Cases_on ‘l ≤ h’>>fs[NOT_LESS_EQUAL,WORD_SLICE_ZERO]>>
  simp[WORD_SLICE_THM]>>
  simp[word_lsr_n2w,ADD1]>>
  simp[WORD_BITS_LSL]>>
  simp[WORD_BITS_COMP_THM]>>
  simp[MIN_DEF]>>
  rewrite_tac[SUB_RIGHT_ADD]>>
  IF_CASES_TAC>>fs[]
QED

Theorem word_slice_alt_shift:
  h ≤ dimindex (:'a) ⇒
  word_slice_alt h l (w:'a word) = w ⋙ l ≪ l ≪ (dimindex (:'a) - h) ⋙ (dimindex (:'a) - h)
Proof
  strip_tac>>
  Cases_on ‘h’>>fs[]>-
   srw_tac[wordsLib.WORD_BIT_EQ_ss][word_slice_alt_def]>>
  rw[word_slice_alt_word_slice,word_slice_shift]
QED

Theorem byte_index_offset:
  8 ≤ dimindex (:'a) ⇒
  byte_index (a:'a word) be + 8 ≤ dimindex (:'a)
Proof
  strip_tac>>
  ‘0 < dimindex (:'a) DIV 8’ by
    (simp[GSYM NOT_ZERO_LT_ZERO]>>
     strip_tac>>
     ‘dimindex (:'a) < 8’ by
       (irule DIV_0_IMP_LT>>simp[])>>simp[])>>
  assume_tac (Q.SPECL [‘dimindex(:'a)’,‘8’] DA)>>
  fs[]>>
  rw[byte_index_def]>-
   (simp[LEFT_SUB_DISTRIB]>>
    simp[LEFT_ADD_DISTRIB]>>
    rewrite_tac[SUB_PLUS]>>
    irule LESS_EQ_TRANS>>
    qexists_tac ‘8 * (dimindex (:'a) DIV 8)’>>
    simp[]>>
    qpat_x_assum ‘_ = dimindex (:'a)’ $ assume_tac o GSYM>>
    first_assum (fn h => rewrite_tac[h])>>
    fs[GSYM DIV_EQ_0])>>
  irule LESS_EQ_TRANS>>
  qexists_tac ‘8 * ((w2n a MOD (dimindex (:'a) DIV 8)) + 1)’>>
  conj_tac >- simp[LEFT_ADD_DISTRIB]>>
  irule LESS_EQ_TRANS>>
  irule_at Any (iffRL LE_MULT_LCANCEL)>>
  simp[GSYM ADD1]>>simp[GSYM LESS_EQ]>>
  irule_at Any MOD_LESS>>
  simp[]>>
  qpat_x_assum ‘_ = dimindex (:'a)’ $ assume_tac o GSYM>>
  first_assum (fn h => rewrite_tac[h])>>
  simp[]>>
  fs[GSYM DIV_EQ_0]
QED

Theorem DIV_MULT2[simp]:
  ∀n q. 0 < n ⇒q * n DIV n = q
Proof
  rpt strip_tac>>
  drule DIV_MULT>>simp[]
QED

Theorem get_byte_set_byte_irrelevant:
  16 ≤ dimindex (:'a) ∧
  w2n (a:α word) MOD (dimindex(:α) DIV 8) ≠ w2n a' MOD (dimindex(:α) DIV 8) ⇒
  get_byte a' (set_byte a b w be) be = get_byte a' w be
Proof
  strip_tac>>
  rewrite_tac[set_byte_def,get_byte_def]>>
  simp[GSYM WORD_w2w_OVER_BITWISE]>>
  ‘0 < dimindex (:'a) DIV 8’
    by (simp[GSYM NOT_ZERO_LT_ZERO]>>
        strip_tac>>
        ‘dimindex (:'a) < 8’
          by (irule DIV_0_IMP_LT>>simp[])>>simp[])>>
  ‘w2n a' MOD (dimindex (:α) DIV 8) < dimindex (:α) DIV 8’ by
    simp[MOD_LESS]>>
  ‘w2n a MOD (dimindex (:α) DIV 8) < dimindex (:α) DIV 8’ by
    simp[MOD_LESS]>>
  ‘byte_index a be + 8 ≤ dimindex (:'a)’ by fs[byte_index_offset]>>
  ‘byte_index a' be + 8 ≤ dimindex (:'a)’ by fs[byte_index_offset]>>
  simp[word_slice_alt_shift]>>
  simp[w2w_def,w2n_lsr]>>
  simp[WORD_MUL_LSL]>>
  simp[word_mul_n2w]>>
  simp[word_mul_def]>>
  ‘(w2n (w ⋙ (byte_index a be + 8)) * 2 ** (byte_index a be + 8)) < dimword (:α)’ by
    (simp[w2n_lsr]>>
     ‘0:num < 2 ** (byte_index a be + 8)’ by simp[]>>
     drule DA>>disch_then $ qspec_then ‘w2n w’ mp_tac>>strip_tac>>
     simp[]>>rewrite_tac[Once ADD_COMM]>>simp[DIV_MULT]>>
     irule LESS_EQ_LESS_TRANS>>
     irule_at Any w2n_lt>>
     qexists_tac ‘w’>>simp[])>>
  ‘(w2n b * 2 ** byte_index a be) < dimword (:α)’ by
    (irule LESS_LESS_EQ_TRANS>>
     irule_at Any (iffRL LT_MULT_RCANCEL)>>
     irule_at Any w2n_lt>>
     simp[dimword_def]>>
     irule LESS_EQ_TRANS>>
     irule_at Any (iffRL EXP_BASE_LE_MONO)>>
     qexists_tac ‘byte_index a be + 8’>>simp[EXP_ADD])>>
  simp[MOD_LESS]>>
  qmatch_goalsub_abbrev_tac ‘w1 ‖ w2 ‖ w3’>>
  qpat_x_assum ‘_ ≠ _’ mp_tac>>
  simp[NOT_NUM_EQ,GSYM LESS_EQ]>>strip_tac>-
   (‘if be then byte_index a' be < byte_index a be
     else byte_index a be < byte_index a' be’ by rw[byte_index_def]>>
    Cases_on ‘be’>>simp[]>-
     (‘w1 = 0w ∧ w3 = n2w (w2n w DIV 2 ** byte_index a' T) ∧ w2 = 0w’ by
        (conj_tac >-
          (simp[Abbr ‘w1’]>>
           simp[w2n_lsr]>>
           ‘0:num < 2 ** (byte_index a T + 8)’ by simp[ZERO_LT_EXP]>>
           drule DA>>disch_then $ qspec_then ‘w2n w’ mp_tac>>strip_tac>>
           simp[]>>
           rewrite_tac[Once ADD_COMM]>>
           simp[DIV_MULT]>>
           simp[EXP_ADD]>>
           qpat_x_assum ‘if _ then _ else _’ mp_tac>>
           simp[LESS_EQ,ADD1]>>strip_tac>>
           drule LESS_EQUAL_ADD>>strip_tac>>
           simp[EXP_ADD]>>
           ntac 2 (rewrite_tac[Once MULT_ASSOC])>>
           simp[])>>
         ‘byte_index a' T + 8 ≤ byte_index a T’ by
           (simp[byte_index_def]>>
            irule LESS_EQ_TRANS>>
            qexists_tac ‘8 * (dimindex (:α) DIV 8 − (w2n a' MOD (dimindex (:α) DIV 8) + 1) + 1)’>>
            simp[]>>
            rewrite_tac[Once $ GSYM ADD1]>>
            simp[GSYM LESS_EQ]>>
            ‘w2n a' MOD (dimindex (:α) DIV 8) < dimindex (:α) DIV 8’ by
              simp[MOD_LESS]>>
            simp[])>>
         conj_tac >-
          (simp[Abbr ‘w3’]>>
           ‘dimword (:'a) =
            2 ** (dimindex (:α) + byte_index a' T − byte_index a T)
            * 2 ** (byte_index a T - byte_index a' T)’ by
             fs[dimword_def,GSYM EXP_ADD]>>
           pop_assum (fn h => rewrite_tac[h])>>
           ‘0 < 2 ** (byte_index a T - byte_index a' T) ∧
            0 < 2 ** (dimindex (:α) + byte_index a' T − byte_index a T)’ by
             fs[ZERO_LT_EXP]>>
           drule (GSYM DIV_MOD_MOD_DIV)>>
           pop_assum kall_tac>>
           disch_then $ drule>>strip_tac>>
           pop_assum (fn h => rewrite_tac[h])>>
           qmatch_goalsub_abbrev_tac ‘(_ * X) DIV Y’>>
           ‘Y = X * 2 ** byte_index a' T’ by simp[Abbr ‘X’,Abbr ‘Y’,GSYM EXP_ADD]>>
           pop_assum (fn h => rewrite_tac[h])>>
           ‘0 < X ∧ 0 < 2 ** byte_index a' T’ by simp[ZERO_LT_EXP,Abbr ‘X’]>>
           simp[GSYM DIV_DIV_DIV_MULT]>>
           simp[Abbr ‘X’]>>
           drule LESS_EQUAL_ADD>>strip_tac>>
           simp[EXP_ADD]>>
           simp[MOD_MULT_MOD])>>
         simp[Abbr ‘w2’]>>
         drule LESS_EQUAL_ADD>>strip_tac>>
         simp[EXP_ADD]>>
         rewrite_tac[Once MULT_ASSOC]>>
         simp[])>>simp[])>>
    ‘byte_index a F + 8 ≤ byte_index a' F’ by simp[byte_index_def]>>
    ‘w3 = 0w ∧ w1 = n2w (w2n w DIV 2 ** byte_index a' F) ∧ w2 = 0w’ by
      (conj_tac >-
        (simp[Abbr ‘w3’]>>
         qmatch_goalsub_abbrev_tac ‘(_ * X) MOD _ DIV Y’>>
         ‘Y = X * 2 ** byte_index a' F’ by simp[Abbr ‘Y’,Abbr ‘X’,GSYM EXP_ADD]>>
         pop_assum (fn h => rewrite_tac[h])>>
         simp[GSYM DIV_DIV_DIV_MULT,ZERO_LT_EXP,Abbr ‘X’]>>
         ‘dimword (:'a) =
          2 ** (dimindex (:α) − byte_index a F) * 2 ** (byte_index a F)’ by
           fs[dimword_def,GSYM EXP_ADD]>>
         pop_assum (fn h => rewrite_tac[h])>>
         simp[GSYM DIV_MOD_MOD_DIV,ZERO_LT_EXP]>>
         qmatch_goalsub_abbrev_tac ‘X MOD _’>>
         ‘w2n w MOD 2 ** byte_index a F < 2 ** byte_index a' F’ by
           (irule LESS_TRANS>>
            irule_at (Pos hd) MOD_LESS>>
            simp[])>>
         pop_assum mp_tac>>
         DEP_ONCE_REWRITE_TAC[GSYM DIV_EQ_0]>>
         simp[EXP])>>
       conj_tac >-
        (simp[Abbr ‘w1’]>>
         simp[w2n_lsr]>>
         ‘0 < 2 ** (byte_index a F + 8)’ by simp[]>>
         drule DA>>disch_then $ qspec_then ‘w2n w’ mp_tac>>
         strip_tac>>
         simp[]>>
         rewrite_tac[Once ADD_COMM]>>
         simp[DIV_MULT]>>
         drule LESS_EQUAL_ADD>>strip_tac>>
         simp[]>>
         qabbrev_tac ‘X = byte_index a F + 8’>>
         simp[EXP_ADD]>>
         simp[GSYM DIV_DIV_DIV_MULT]>>
         rewrite_tac[Once ADD_COMM]>>
         simp[DIV_MULT])>>
       simp[Abbr ‘w2’]>>
       drule LESS_EQUAL_ADD>>strip_tac>>
       simp[]>>
       simp[EXP_ADD]>>
       rewrite_tac[MULT_ASSOC]>>
       once_rewrite_tac[MULT_COMM]>>
       simp[GSYM DIV_DIV_DIV_MULT]>>
       ‘w2n b DIV 256 = 0’ by
         (simp[DIV_EQ_0]>>
          irule LESS_LESS_EQ_TRANS>>
          irule_at Any w2n_lt>>
          simp[])>>
       simp[])>>simp[])>>
  ‘if be then byte_index a be < byte_index a' be
   else byte_index a' be < byte_index a be’ by rw[byte_index_def]>>
  Cases_on ‘be’>>simp[]>-
   (    
   ‘byte_index a T + 8 ≤ byte_index a' T’ by simp[byte_index_def]>>
   ‘w3 = 0w ∧ w1 = n2w (w2n w DIV 2 ** byte_index a' T) ∧ w2 = 0w’ by
      (conj_tac >-
        (simp[Abbr ‘w3’]>>
         qmatch_goalsub_abbrev_tac ‘(_ * X) MOD _ DIV Y’>>
         ‘Y = X * 2 ** byte_index a' T’ by simp[Abbr ‘Y’,Abbr ‘X’,GSYM EXP_ADD]>>
         pop_assum (fn h => rewrite_tac[h])>>
         simp[GSYM DIV_DIV_DIV_MULT,ZERO_LT_EXP,Abbr ‘X’]>>
         ‘dimword (:'a) =
          2 ** (dimindex (:α) − byte_index a T) * 2 ** (byte_index a T)’ by
           fs[dimword_def,GSYM EXP_ADD]>>
           pop_assum (fn h => rewrite_tac[h])>>
         simp[GSYM DIV_MOD_MOD_DIV,ZERO_LT_EXP]>>
         qmatch_goalsub_abbrev_tac ‘X MOD _’>>
         ‘w2n w MOD 2 ** byte_index a T < 2 ** byte_index a' T’ by
           (irule LESS_TRANS>>
            irule_at (Pos hd) MOD_LESS>>
            simp[])>>
         pop_assum mp_tac>>
         DEP_ONCE_REWRITE_TAC[GSYM DIV_EQ_0]>>
         simp[EXP])>>
       conj_tac >-
        (simp[Abbr ‘w1’]>>
         simp[w2n_lsr]>>
         ‘0 < 2 ** (byte_index a T + 8)’ by simp[]>>
         drule DA>>disch_then $ qspec_then ‘w2n w’ mp_tac>>
         strip_tac>>
         simp[]>>
         rewrite_tac[Once ADD_COMM]>>
         simp[DIV_MULT]>>
         drule LESS_EQUAL_ADD>>strip_tac>>
         simp[]>>
         qabbrev_tac ‘X = byte_index a T + 8’>>
         simp[EXP_ADD]>>
         simp[GSYM DIV_DIV_DIV_MULT]>>
         rewrite_tac[Once ADD_COMM]>>
         simp[DIV_MULT])>>
       simp[Abbr ‘w2’]>>
       drule LESS_EQUAL_ADD>>strip_tac>>
       simp[]>>
       simp[EXP_ADD]>>
       rewrite_tac[MULT_ASSOC]>>
       once_rewrite_tac[MULT_COMM]>>
       simp[GSYM DIV_DIV_DIV_MULT]>>
       ‘w2n b DIV 256 = 0’ by
         (simp[DIV_EQ_0]>>
          irule LESS_LESS_EQ_TRANS>>
          irule_at Any w2n_lt>>
          simp[])>>
       simp[])>>simp[])>>
  ‘w1 = 0w ∧ w3 = n2w (w2n w DIV 2 ** byte_index a' F) ∧ w2 = 0w’ by
        (conj_tac >-
          (simp[Abbr ‘w1’]>>
           simp[w2n_lsr]>>
           ‘0 < 2 ** (byte_index a F + 8)’ by simp[ZERO_LT_EXP]>>
           drule DA>>disch_then $ qspec_then ‘w2n w’ mp_tac>>strip_tac>>
           simp[]>>
           rewrite_tac[Once ADD_COMM]>>
           simp[DIV_MULT]>>
           simp[EXP_ADD]>>
           qpat_x_assum ‘if _ then _ else _’ mp_tac>>
           simp[LESS_EQ,ADD1]>>strip_tac>>
           drule LESS_EQUAL_ADD>>strip_tac>>
           simp[EXP_ADD]>>
           ntac 2 (rewrite_tac[Once MULT_ASSOC])>>
           simp[])>>
         ‘byte_index a' F + 8 ≤ byte_index a F’ by
           (simp[byte_index_def]>>
            irule LESS_EQ_TRANS>>
            qexists_tac ‘8 * (dimindex (:α) DIV 8 − (w2n a' MOD (dimindex (:α) DIV 8) + 1) + 1)’>>
            simp[]>>
            rewrite_tac[Once $ GSYM ADD1]>>
            simp[GSYM LESS_EQ]>>
            ‘w2n a' MOD (dimindex (:α) DIV 8) < dimindex (:α) DIV 8’ by
              simp[MOD_LESS]>>
            simp[])>>
         conj_tac >-
          (simp[Abbr ‘w3’]>>
           ‘dimword (:'a) =
            2 ** (dimindex (:α) + byte_index a' F − byte_index a F)
            * 2 ** (byte_index a F - byte_index a' F)’ by
             fs[dimword_def,GSYM EXP_ADD]>>
           pop_assum (fn h => rewrite_tac[h])>>
           ‘0 < 2 ** (byte_index a F - byte_index a' F) ∧
            0 < 2 ** (dimindex (:α) + byte_index a' F − byte_index a F)’ by
             fs[ZERO_LT_EXP]>>
           simp[GSYM DIV_MOD_MOD_DIV]>>
           qmatch_goalsub_abbrev_tac ‘(_ * X) DIV Y’>>
           ‘Y = X * 2 ** byte_index a' F’ by simp[Abbr ‘X’,Abbr ‘Y’,GSYM EXP_ADD]>>
           pop_assum (fn h => rewrite_tac[h])>>
           ‘0 < X ∧ 0 < 2 ** byte_index a' F’ by simp[ZERO_LT_EXP,Abbr ‘X’]>>
           simp[GSYM DIV_DIV_DIV_MULT]>>
           drule LESS_EQUAL_ADD>>strip_tac>>
           simp[EXP_ADD]>>
           simp[MOD_MULT_MOD])>>
         simp[Abbr ‘w2’]>>
         drule LESS_EQUAL_ADD>>strip_tac>>
         simp[EXP_ADD]>>
         rewrite_tac[Once MULT_ASSOC]>>
         simp[])>>simp[]
QED

Theorem bytes_to_word_word_to_bytes_32:
  LENGTH bs = dimindex (:32) DIV 8 ⇒
  word_to_bytes (word_of_bytes be (0w:word32) bs) be = bs
Proof
  simp[word_to_bytes_def]>>
  rewrite_tac[numLib.num_CONV “4”,numLib.num_CONV “3”,TWO,ONE,
              word_to_bytes_aux_def]>>
  simp[]>>
  Cases_on ‘bs’>>simp[]>>
  rename1 ‘_ ⇒ _ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
(*  ntac 2 (rewrite_tac[Once CONJ_ASSOC]>>
       rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[])>>*)
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[numLib.num_CONV “4”,numLib.num_CONV “3”,TWO,ONE]>>
  fs[]>>strip_tac>>
  simp[word_of_bytes_def,get_byte_set_byte_irrelevant,get_byte_set_byte]
QED

Theorem bytes_to_word_word_to_bytes_64:
  LENGTH bs = dimindex (:64) DIV 8 ⇒
  word_to_bytes (word_of_bytes be (0w:word64) bs) be = bs
Proof
  simp[word_to_bytes_def]>>
  rewrite_tac[numLib.num_CONV “8”,numLib.num_CONV “7”,numLib.num_CONV “6”,
              numLib.num_CONV “5”,numLib.num_CONV “4”,numLib.num_CONV “3”,
              TWO,ONE,word_to_bytes_aux_def]>>
  simp[]>>
  Cases_on ‘bs’>>simp[]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
(*  ntac 8 (rewrite_tac[Once CONJ_ASSOC]>>
       rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[])>>*)
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[Once CONJ_ASSOC]>>
  rename1 ‘_ ∧ _ = bs’>>Cases_on ‘bs’>>simp[]>>
  rewrite_tac[numLib.num_CONV “8”,numLib.num_CONV “7”,numLib.num_CONV “6”,
              numLib.num_CONV “5”,numLib.num_CONV “4”,numLib.num_CONV “3”,
              TWO,ONE]>>
  fs[]>>strip_tac>>
  simp[word_of_bytes_def,get_byte_set_byte_irrelevant,get_byte_set_byte]
QED

val _ = export_theory();
