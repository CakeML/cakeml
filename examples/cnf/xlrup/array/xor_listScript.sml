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
