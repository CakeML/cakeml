(*
  A byte-list mirror of the XOR bitstring operations, which the array
  implementation updates destructively. Each definition here is proved
  equal to its string-based counterpart under
  s ↦ implode (MAP fromByte s).
*)
Theory xor_list
Ancestors
  xor syntax_helper mlstring
Libs
  preamble

(* 1-sided variant of strxor *)
Definition strxor_aux_1_def:
  (strxor_aux_1 cs [] = cs) ∧
  (strxor_aux_1 cs (d::ds) =
    case cs of [] => []
    | (c::cs) => (c ⊕ toByte d) :: strxor_aux_1 cs ds)
End

Theorem strxor_aux_1:
  ∀ds cs.
  LENGTH ds ≤ LENGTH cs ⇒
  strxor_aux_1 cs ds = MAP toByte (strxor_aux (MAP fromByte cs) ds)
Proof
  Induct>>rw[strxor_aux_1_def]>>
  Cases_on`cs`>>fs[]>>
  rw[strxor_aux_def,strxor_aux_1_def,MAP_MAP_o,o_DEF]>>
  fs[charxor_def]
QED

Theorem strxor_aux_1_SNOC:
  ∀ds cs.
  LENGTH ds + 1 ≤ LENGTH cs ⇒
  strxor_aux_1 cs (SNOC d ds) =
  strxor_aux_1 (LUPDATE (EL (LENGTH ds) cs ⊕ toByte d) (LENGTH ds) cs) ds
Proof
  Induct>>rw[strxor_aux_1_def]
  >- (
    TOP_CASE_TAC>>fs[]>>
    EVAL_TAC)>>
  TOP_CASE_TAC>>fs[SNOC_APPEND]>>
  simp[LUPDATE_def]
QED

(* Counts down from n, so that the array version writes in place *)
Definition strxor_aux_c_def:
  strxor_aux_c cs ds n =
  if n = 0 then cs
  else
    let n1 = n - 1 in
    let c = EL n1 cs in
    let d = toByte (strsub ds n1) in
    strxor_aux_c (LUPDATE (c ⊕ d) n1 cs) ds n1
End

Theorem strxor_aux_c:
  ∀cs ds n.
  n ≤ strlen ds ∧ strlen ds ≤ LENGTH cs ⇒
  strxor_aux_c cs ds n =
  strxor_aux_1 cs (TAKE n (explode ds))
Proof
  ho_match_mp_tac strxor_aux_c_ind>>rw[]>>
  simp[Once strxor_aux_c_def]>>rw[]
  >-
    simp[strxor_aux_1_def]>>
  qabbrev_tac`m = n-1`>>
  `n = m + 1` by fs[Abbr`m`]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[TAKE_EL_SNOC]>>
  DEP_REWRITE_TAC[strxor_aux_1_SNOC]>>
  simp[]>>
  Cases_on`ds`>>simp[strsub_def]
QED

Definition strxor_c_def:
  strxor_c s t =
  let lt = strlen t in
  let s =
    if lt ≤ LENGTH s
    then s
    else s ++ REPLICATE (lt - LENGTH s) 0w in
    strxor_aux_c s t lt
End

Theorem strxor_c:
  strxor_c s t =
  MAP toByte (explode (strxor (implode (MAP fromByte s)) t))
Proof
  rw[strxor_c_def,strxor_compute,extend_s_def]>>fs[]
  >- (
    DEP_REWRITE_TAC[strxor_aux_c,strxor_aux_1]>>
    simp[]>>
    Cases_on`t`>>simp[])>>
  DEP_REWRITE_TAC[strxor_aux_c,strxor_aux_1]>>
  simp[]>>
  simp[fromByte_def]>>
  Cases_on`t`>>simp[]
QED

Definition is_emp_xor_list_def:
  is_emp_xor_list (ls:word8 list) =
  EVERY ($= 0w) ls
End

Theorem is_emp_xor_list:
  is_emp_xor_list x =
  is_emp_xor (implode (MAP fromByte x))
Proof
  rw[is_emp_xor_list_def,is_emp_xor_def,EVERY_MAP]>>
  match_mp_tac EVERY_CONG>>rw[]>>
  qmatch_goalsub_rename_tac`fromByte c`>>
  EVAL_TAC>>
  `w2n c < dimword(:8)` by
    metis_tac[w2n_lt]>>
  fs[]
QED

Definition flip_bit_word_def:
  flip_bit_word (w:word8) n =
  let b = ¬ (w ' n) in
  if b then
    w ‖ 1w ≪ n
  else
    w && ¬(1w ≪ n)
End

Theorem flip_bit_word_set_get:
  flip_bit_word w n =
  toByte (set_bit_char (fromByte w) n (¬get_bit_char (fromByte w) n))
Proof
  rw[set_bit_char_def,get_bit_char_def,flip_bit_word_def]
QED

Definition flip_bit_list_def:
  flip_bit_list s n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  let b = flip_bit_word (EL q s) r in
  LUPDATE b q s
End

Theorem flip_bit_list:
  n DIV 8 < LENGTH ls ⇒
  flip_bit_list ls n =
  MAP toByte (explode (flip_bit (implode (MAP fromByte ls)) n))
Proof
  rw[flip_bit_list_def,flip_bit_word_set_get]>>
  rw[LIST_EQ_REWRITE]>>
  simp[EL_MAP,flip_bit_def,set_bit_def,get_bit_def,EL_explode]>>
  simp[set_char_def,get_char_def,strsub_implode]>>
  rw[EL_LUPDATE,EL_MAP]
QED

Definition get_bit_list_def:
  get_bit_list (s:word8 list) n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  EL q s ' r
End

Theorem get_bit_list:
  n DIV 8 < LENGTH ls ⇒
  get_bit_list ls n =
  get_bit (implode (MAP fromByte ls)) n
Proof
  rw[get_bit_list_def,get_bit_def,get_char_def,get_bit_char_def]>>
  simp[strsub_implode,toByte_def,EL_MAP,fromByte_def]
QED

Definition set_bit_word_def:
  set_bit_word (w:word8) n b =
  if b then
    w ‖ 1w ≪ n
  else
    w && ¬(1w ≪ n)
End

Theorem set_bit_word_set_bit:
  set_bit_word w n b =
  toByte (set_bit_char (fromByte w) n b)
Proof
  rw[set_bit_char_def,set_bit_word_def]
QED

Definition set_bit_list_def:
  set_bit_list s n b =
  let q = n DIV 8 in
  let r = n MOD 8 in
  let b = set_bit_word (EL q s) r b in
  LUPDATE b q s
End

Theorem set_bit_list:
  n DIV 8 < LENGTH ls ⇒
  set_bit_list ls n b =
  MAP toByte (explode (set_bit (implode (MAP fromByte ls)) n b))
Proof
  rw[set_bit_list_def,set_bit_word_set_bit,set_bit_def,set_char_def]>>
  rw[LIST_EQ_REWRITE]>>
  simp[EL_MAP]>>
  rw[EL_LUPDATE,EL_MAP,get_char_def,toByte_def,fromByte_def,strsub_implode]
QED

Definition extend_s_list_def:
  extend_s_list s n =
  if n < LENGTH s then s
  else
    s ++ REPLICATE (n - LENGTH s) (0w :word8)
End

Theorem extend_s_list:
  extend_s_list s n =
  MAP toByte (explode (extend_s (implode (MAP fromByte s)) n))
Proof
  rw[extend_s_list_def,extend_s_def]>>fs[MAP_MAP_o,o_DEF]>>
  EVAL_TAC
QED

Theorem implode_REPLICATE_extend_s:
  implode (MAP fromByte (REPLICATE n (0w:word8))) = extend_s «» n
Proof
  rw[extend_s_def,rich_listTheory.map_replicate]>>fs[]>>
  EVAL_TAC
QED

Definition conv_xor_aux_list_def:
  (conv_xor_aux_list s [] = s) ∧
  (conv_xor_aux_list s (x::xs) =
  let v = Num (ABS x) in
  let s = extend_s_list s (v DIV 8 + 1) in
  if x > 0 then
    conv_xor_aux_list (flip_bit_list s v) xs
  else
    conv_xor_aux_list (flip_bit_list (flip_bit_list s v) 0) xs)
End

Theorem conv_xor_aux_list:
  ∀x ls.
  conv_xor_aux_list ls x =
  MAP toByte (explode (conv_xor_aux (implode (MAP fromByte ls)) x))
Proof
  Induct>>rw[conv_xor_aux_def,conv_xor_aux_list_def]
  >-
    simp[MAP_MAP_o,o_DEF]>>
  DEP_REWRITE_TAC[flip_bit_list,extend_s_list]>>
  simp[MAP_MAP_o,o_DEF]>>
  rw[extend_s_def]
QED

(*** Bit n of a byte list, reading 0 past its end, and the operations
  above characterised bit by bit ***)

Definition bit_list_def:
  bit_list (s:word8 list) n ⇔
  n DIV 8 < LENGTH s ∧ get_bit_list s n
End

Theorem bit_list_get_bit:
  bit_list s n = get_bit (implode (MAP fromByte s)) n
Proof
  rw[bit_list_def]>>
  Cases_on`n DIV 8 < LENGTH s`>>simp[get_bit_list]>>
  simp[get_bit_def,get_char_def,get_bit_char_def]>>
  EVAL_TAC>>
  irule wordsTheory.word_0>>simp[]
QED

Theorem bit_list_REPLICATE_0w:
  ¬bit_list (REPLICATE k 0w) n
Proof
  rw[bit_list_def,get_bit_list_def]>>
  Cases_on`n DIV 8 < k`>>simp[EL_REPLICATE,wordsTheory.word_0]
QED

Theorem is_emp_xor_list_bit_list:
  is_emp_xor_list s ⇔ ∀n. ¬bit_list s n
Proof
  rw[is_emp_xor_list_def,bit_list_def,get_bit_list_def,EVERY_EL,EQ_IMP_THM]
  >- (
    Cases_on`n DIV 8 < LENGTH s`>>gvs[]>>
    irule wordsTheory.word_0>>simp[])>>
  rw[fcpTheory.CART_EQ,wordsTheory.word_0]>>
  first_x_assum (qspec_then`n * 8 + i` mp_tac)>>
  simp[arithmeticTheory.DIV_MULT,arithmeticTheory.MOD_MULT]
QED

Theorem strxor_aux_1_EL[local]:
  ∀ds cs i.
  LENGTH ds ≤ LENGTH cs ⇒
  LENGTH (strxor_aux_1 cs ds) = LENGTH cs ∧
  (i < LENGTH cs ⇒
   EL i (strxor_aux_1 cs ds) =
   if i < LENGTH ds then EL i cs ⊕ toByte (EL i ds) else EL i cs)
Proof
  Induct>>rw[strxor_aux_1_def]>>
  Cases_on`cs`>>fs[strxor_aux_1_def]>>
  Cases_on`i`>>fs[]
QED

Theorem bit_list_strxor_c:
  bit_list (strxor_c s t) n ⇔ (bit_list s n ⇎ get_bit t n)
Proof
  Cases_on`t`>>simp[strxor_c_def]>>
  DEP_REWRITE_TAC[strxor_aux_c]>>rw[]>>
  simp[bit_list_def,get_bit_list_def,get_bit_def,get_char_def,
    get_bit_char_def]
  >- (
    qspecl_then[`s'`,`s`,`n DIV 8`] mp_tac strxor_aux_1_EL>>
    rw[]>>Cases_on`n DIV 8 < STRLEN s'`>>
    gvs[wordsTheory.word_xor_def,fcpTheory.FCP_BETA,wordsTheory.word_0,
      toByte_def]
    >- metis_tac[]>>
    Cases_on`n DIV 8 < LENGTH s`>>gvs[])>>
  qspecl_then[`s'`,`s ++ REPLICATE (STRLEN s' − LENGTH s) 0w`,`n DIV 8`]
    mp_tac strxor_aux_1_EL>>
  rw[]>>Cases_on`n DIV 8 < LENGTH s`>>
  gvs[EL_APPEND_EQN,EL_REPLICATE,wordsTheory.word_xor_def,fcpTheory.FCP_BETA,
    wordsTheory.word_0,toByte_def]>>
  metis_tac[]
QED

Theorem flip_bit_word_bit[local]:
  i < 8 ∧ r < 8 ⇒ (flip_bit_word w r ' i ⇔ (w ' i ⇎ i = r))
Proof
  rw[flip_bit_word_def,word_or_def,word_and_def,word_1comp_def,
    word_lsl_def,fcpTheory.FCP_BETA,word_index]>>
  Cases_on`i = r`>>fs[]
QED

Theorem set_bit_word_bit[local]:
  i < 8 ∧ r < 8 ⇒ (set_bit_word w r b ' i ⇔ if i = r then b else w ' i)
Proof
  rw[set_bit_word_def,word_or_def,word_and_def,word_1comp_def,
    word_lsl_def,fcpTheory.FCP_BETA,word_index]>>
  fs[]
QED

Theorem DIV_MOD_8_eq[local]:
  (n DIV 8 = k DIV 8 ∧ n MOD 8 = k MOD 8) ⇔ n = k
Proof
  rw[EQ_IMP_THM]>>
  qspec_then`8` mp_tac arithmeticTheory.DIVISION>>simp[]>>
  metis_tac[]
QED

Theorem bit_list_flip_bit_list:
  k DIV 8 < LENGTH s ⇒
  (bit_list (flip_bit_list s k) n ⇔ (bit_list s n ⇎ n = k))
Proof
  rw[bit_list_def,flip_bit_list_def,get_bit_list_def,EL_LUPDATE]>>
  Cases_on`n DIV 8 = k DIV 8`>>gvs[flip_bit_word_bit]>>
  metis_tac[DIV_MOD_8_eq]
QED

Theorem bit_list_set_bit_list:
  k DIV 8 < LENGTH s ⇒
  (bit_list (set_bit_list s k b) n ⇔ if n = k then b else bit_list s n)
Proof
  rw[bit_list_def,set_bit_list_def,get_bit_list_def,EL_LUPDATE]>>
  Cases_on`n DIV 8 = k DIV 8`>>gvs[set_bit_word_bit]>>
  rw[]>>metis_tac[DIV_MOD_8_eq]
QED

Theorem bit_list_extend_s_list:
  bit_list (extend_s_list s m) n ⇔ bit_list s n
Proof
  rw[extend_s_list_def,bit_list_def,get_bit_list_def,EL_APPEND_EQN,
    EL_REPLICATE]>>
  Cases_on`n DIV 8 < LENGTH s`>>gvs[]>>
  Cases_on`n DIV 8 < m`>>simp[EL_REPLICATE,wordsTheory.word_0]
QED

Theorem LENGTH_extend_s_list:
  ∀s n.
  n ≤ LENGTH (extend_s_list s n) ∧ LENGTH s ≤ LENGTH (extend_s_list s n)
Proof
  rw[extend_s_list_def]
QED

Theorem LENGTH_flip_bit_list[simp]:
  LENGTH (flip_bit_list s n) = LENGTH s
Proof
  rw[flip_bit_list_def]
QED

Theorem bit_list_conv_xor_aux_list:
  ∀xs s.
  bit_list (conv_xor_aux_list s xs) n ⇔
  (bit_list s n ⇎ bit_list (conv_xor_aux_list [] xs) n)
Proof
  Induct
  >- simp[conv_xor_aux_list_def,bit_list_def]>>
  rpt gen_tac>>
  ONCE_REWRITE_TAC[conv_xor_aux_list_def]>>
  simp_tac std_ss [LET_THM]>>
  Cases_on`h > 0`>>
  pop_assum (fn th => REWRITE_TAC[th])>>
  first_assum (fn th => ONCE_REWRITE_TAC[th])>>
  pop_assum kall_tac>>
  qspecl_then[`s`,`Num (ABS h) DIV 8 + 1`] assume_tac LENGTH_extend_s_list>>
  qspecl_then[`[]`,`Num (ABS h) DIV 8 + 1`] assume_tac LENGTH_extend_s_list>>
  gvs[bit_list_flip_bit_list,bit_list_extend_s_list]>>
  `¬bit_list [] n` by simp[bit_list_def]>>
  metis_tac[]
QED
