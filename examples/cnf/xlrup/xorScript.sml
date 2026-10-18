(*
  XOR constraints and their bitstring-based internal representation
*)
Theory xor
Ancestors
  misc cnf ccnf syntax_helper mlstring bitstring[qualified]
Libs
  preamble blastLib

(* XOR constraints are a list of literals required to sum (XOR) to 1 under
  the given assignment. This is the format used by CryptoMiniSat. *)
Type cmsxor = ``:num lit list``;

Definition of_bool_def:
  (of_bool T = (1:num)) ∧
  (of_bool F = 0)
End

Definition sat_cmsxor_def:
  sat_cmsxor w (C:cmsxor) ⇔
    ODD (SUM (MAP (of_bool o satisfies_lit w) C))
End

Overload satisfies_xfml = ``satisfies_fml_gen sat_cmsxor``;

Theorem satisfies_xfml_MEM:
  satisfies_xfml w (set xs) ∧ MEM x xs ⇒ sat_cmsxor w x
Proof
  rw[satisfies_fml_gen_def]
QED

(* Internally, an XOR is represented by a string of bits, where bit 0 is the
  constant summand and bit v is the coefficient of variable v. *)
Type strxor = ``:mlstring``;

(* For fast parsing, XORs are also represented "raw" using int lists *)
Type rawxor = ``:int list``;

(* This outputs bits in the 'bit order', i.e.,
  MSB is first entry of the list*)
Definition char_to_bits_def:
  char_to_bits c =
  REVERSE (w2v ((n2w (ORD c)):word8))
End

Theorem LENGTH_char_to_bits[simp]:
  LENGTH (char_to_bits c) = 8
Proof
  rw[char_to_bits_def]
QED

Definition string_to_bits_def:
  string_to_bits (s:mlstring) =
  FLAT (MAP char_to_bits (explode s))
End

Theorem LENGTH_FLAT_char_to_bits[simp]:
  LENGTH (FLAT (MAP char_to_bits ls)) = 8 * LENGTH ls
Proof
  rw[LENGTH_FLAT,MAP_MAP_o,o_DEF]>>
  qspecl_then [`λx.8`,`ls`,`8`] mp_tac SUM_MAP_K>>
  rw[]
QED

Theorem LENGTH_string_to_bits[simp]:
  LENGTH (string_to_bits s) = 8 * strlen s
Proof
  rw[string_to_bits_def]
QED

Definition sum_bitlist_aux_def:
  sum_bitlist_aux w ls k =
  SUM (MAPi (λn e. of_bool (w (n + k) ∧ e)) ls)
End

Definition sum_bitlist_def:
  sum_bitlist w ls =
  if LENGTH ls = 0 then 0
  else
    of_bool (HD ls) + sum_bitlist_aux w (TL ls) 1
End

Definition isat_strxor_def:
  isat_strxor (w:num assignment) x ⇔
    EVEN (sum_bitlist w (string_to_bits x))
End

(* Get and Set bit in a string
  bits out of bounds default to 0 *)
Definition toByte_def:
  toByte c = (n2w (ORD c)):word8
End

Definition get_bit_char_def:
  get_bit_char c n =
  toByte c ' n
End

Definition get_char_def:
  get_char s n =
  if n < strlen s then
    strsub s n
  else
    CHR 0
End

Definition get_bit_def:
  get_bit s n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  get_bit_char (get_char s q) r
End

Theorem get_bit_char_char_to_bits:
  n < 8 ⇒
  (get_bit_char c n = EL n (char_to_bits c))
Proof
  EVAL_TAC>>
  rw[]>>
  `n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
    n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7` by fs[]>>
  rw[]>>
  blastLib.FULL_BBLAST_TAC
QED

Theorem DIV_SUB_1:
  1 < n ∧ n ≤ m ⇒
  m DIV n = (m − n) DIV n + 1
Proof
  rw[]>>
  DEP_REWRITE_TAC[DIV_SUB |> Q.GEN `q` |> Q.SPEC`1` |> SIMP_RULE std_ss []]>>
  simp[]>>
  Cases_on`m DIV n`>>fs[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[DIV_EQ_0]>>
  fs[]
QED

Theorem EL_FLAT_const:
  ∀ls n.
  k > 1 ∧
  (∀x. MEM x ls ⇒ LENGTH x = k) ∧
  n < LENGTH (FLAT ls) ⇒
  EL n (FLAT ls) =
    EL (n MOD k) (EL (n DIV k) ls)
Proof
  Induct>>rw[EL_APPEND_EQN]
  >-
    fs[LESS_DIV_EQ_ZERO]>>
  gvs[]>>
  simp[EQ_SYM_EQ]>>
  DEP_ONCE_REWRITE_TAC [DIV_SUB_1,SUB_MOD]>>
  simp[GSYM ADD1]
QED

Theorem get_bit_string_to_bits:
  get_bit s n =
  if n < LENGTH (string_to_bits s) then
    EL n (string_to_bits s)
  else F
Proof
  simp[get_bit_def,get_char_def]>>
  DEP_REWRITE_TAC[DIV_LT_X] >> simp[]>>
  reverse(rw[])
  >- (
    EVAL_TAC>>
    match_mp_tac word_0>>
    simp[])>>
  DEP_REWRITE_TAC[get_bit_char_char_to_bits]>>
  simp[string_to_bits_def]>>
  DEP_REWRITE_TAC[EL_FLAT_const |> Q.GEN `k` |> Q.SPEC`8`]>>
  simp[MEM_MAP,PULL_EXISTS]>>
  DEP_REWRITE_TAC[EL_MAP,DIV_LT_X] >> simp[]>>
  Cases_on`s`>>simp[]
QED

Definition fromByte_def:
  fromByte (w:word8) = CHR (w2n w)
End

Theorem fromByte_toByte[simp]:
  fromByte (toByte c) = c
Proof
  EVAL_TAC>>rw[ORD_BOUND]
QED

Theorem toByte_fromByte[simp]:
  toByte (fromByte w) = w
Proof
  EVAL_TAC>>
  `w2n w < dimword(:8)` by
    metis_tac[w2n_lt]>>
  fs[]
QED

Definition set_bit_char_def:
  set_bit_char c n b =
  let w = toByte c in
  if b then
    fromByte (w ‖ (1w:word8 << n))
  else
    fromByte (w && ¬(1w:word8 << n))
End

(* Set the i-th character in a string WITHOUT length extension *)
Definition set_char_def:
  set_char s i c =
  let cs = explode s in
  implode (LUPDATE c i cs)
End

Definition set_bit_def:
  set_bit s n b =
  let q = n DIV 8 in
  let r = n MOD 8 in
  let c = get_char s q in
  set_char s q (set_bit_char c r b)
End

Theorem string_to_bits_strcat[simp]:
  string_to_bits (s1 ^ s2) =
  string_to_bits s1 ++ string_to_bits s2
Proof
  rw[string_to_bits_def]
QED

Theorem char_to_bits_set_bit_char:
  n < 8 ⇒
  char_to_bits (set_bit_char c n b) =
  LUPDATE b n (char_to_bits c)
Proof
  rw[char_to_bits_def,set_bit_char_def,toByte_def,fromByte_def]>>
  rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_REVERSE]>>
  DEP_REWRITE_TAC[bitstringTheory.el_w2v]>>
  `(n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
    n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) ∧
   (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨
    x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7)` by fs[]>>
  simp[]>>
  FULL_BBLAST_TAC
QED

Theorem string_to_bits_set_bit:
  n < LENGTH (string_to_bits s) ⇒
  string_to_bits (set_bit s n b) =
  LUPDATE b n (string_to_bits s)
Proof
  rw[string_to_bits_def,LIST_EQ_REWRITE,set_bit_def,set_char_def]>>
  rw[EL_LUPDATE]>>
  DEP_REWRITE_TAC[EL_FLAT_const |> Q.GEN `k` |> Q.SPEC`8`]>>
  simp[MEM_MAP,MEM_LUPDATE,PULL_EXISTS]>>
  DEP_REWRITE_TAC[EL_MAP,EL_LUPDATE]>>
  simp[]>>
  DEP_REWRITE_TAC[DIV_LT_X] >> simp[]
  >- (
    DEP_REWRITE_TAC[char_to_bits_set_bit_char]>>
    simp[EL_LUPDATE])>>
  rw[]>>
  DEP_REWRITE_TAC[char_to_bits_set_bit_char]>>
  simp[EL_LUPDATE]>>
  rw[]
  >-
    `x = n` by intLib.ARITH_TAC>>
  fs[get_char_def]>>
  DEP_REWRITE_TAC[DIV_LT_X] >> simp[]>>
  Cases_on`s`>>simp[]
QED

Definition flip_bit_def:
  flip_bit s v =
  set_bit s v (¬ get_bit s v)
End

Definition extend_s_def:
  extend_s s n =
  if strlen s < n then
    s ^ (implode (REPLICATE (n - strlen s) (CHR 0)))
  else s
End

Definition conv_xor_aux_def:
  (conv_xor_aux s [] = s) ∧
  (conv_xor_aux s (x::xs) =
  let v = Num (ABS x) in
  let s = extend_s s (v DIV 8 + 1) in
  if x > 0 then
    conv_xor_aux (flip_bit s v) xs
  else
    conv_xor_aux (flip_bit (flip_bit s v) 0) xs)
End

Definition conv_xor_def:
  conv_xor s x = conv_xor_aux s (MAP to_ilit x)
End

Theorem sum_bitlist_aux_cons:
  sum_bitlist_aux w (x::xs) k =
  of_bool (w k ∧ x) + sum_bitlist_aux w xs (k + 1)
Proof
  rw[sum_bitlist_aux_def,o_DEF,ADD1]
QED

Theorem EVEN_of_bool[simp]:
  EVEN (of_bool b) = ¬ b
Proof
  Cases_on`b`>>rw[of_bool_def]
QED

Theorem sum_bitlist_aux_xor:
  ∀xs ys k.
  LENGTH xs = LENGTH ys ==>
  EVEN (sum_bitlist_aux w (MAP2 (λx y. x ⇎ y) xs ys) k) =
  (EVEN (sum_bitlist_aux w xs k) ⇔ EVEN (sum_bitlist_aux w ys k))
Proof
  Induct>>rw[]
  >-
    simp[sum_bitlist_aux_def]>>
  Cases_on`ys`>>fs[o_DEF,ADD1]>>
  simp[sum_bitlist_aux_cons]>>
  first_x_assum(qspecl_then[`t`,`k+1`] mp_tac)>>
  simp[]>>rw[EVEN_ADD]>>
  metis_tac[]
QED

Theorem sum_bitlist_xor:
  LENGTH xs = LENGTH ys ∧
  EVEN (sum_bitlist w xs) ∧
  EVEN (sum_bitlist w ys) ⇒
  EVEN (sum_bitlist w (MAP2 (λx y. x ⇎ y) xs ys))
Proof
  rw[sum_bitlist_def]>>fs[]>>
  Cases_on`xs`>>Cases_on`ys`>>fs[]>>
  fs[EVEN_ADD,sum_bitlist_aux_xor,sum_bitlist_aux_cons]>>
  metis_tac[]
QED

Definition charxor_def:
  charxor c d =
  fromByte (toByte c ⊕ toByte d)
End

Definition strxor_aux_def:
  (strxor_aux [] ds = ds) ∧
  (strxor_aux cs [] = cs) ∧
  (strxor_aux (c::cs) (d::ds) =
    charxor c d :: strxor_aux cs ds)
End

Definition strxor_def:
  strxor (s:strxor) (t:strxor) =
    implode (strxor_aux (explode s) (explode t))
End

Theorem charxor_id[simp]:
  charxor c (CHR 0) = c
Proof
  rw[charxor_def,fromByte_def,toByte_def]>>
  rw[ORD_BOUND]
QED

Theorem strxor_aux_prop:
  ∀cs ds.
  LENGTH ds ≤ LENGTH cs ⇒
  strxor_aux cs ds =
  MAP2 charxor cs (ds ++ REPLICATE (LENGTH cs - LENGTH ds) (CHR 0))
Proof
  ho_match_mp_tac strxor_aux_ind>>rw[]
  >-
    EVAL_TAC
  >- (
    simp[strxor_aux_def]>>
    rw[LIST_EQ_REWRITE,EL_MAP2,EL_REPLICATE])>>
  fs[strxor_aux_def]
QED

Theorem char_to_bits_charxor:
  char_to_bits (charxor c d) =
  MAP2 (λx y. x ⇎ y) (char_to_bits c) (char_to_bits d)
Proof
  rw[charxor_def,char_to_bits_def,toByte_def,fromByte_def,LIST_EQ_REWRITE,EL_REVERSE,EL_MAP2]>>
  DEP_REWRITE_TAC[bitstringTheory.el_w2v]>>
  simp[]>>
  `x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨
    x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7` by fs[]>>
  simp[]>>
  FULL_BBLAST_TAC
QED

Theorem MAP2_charxor:
  ∀cs ds.
  LENGTH cs = LENGTH ds ⇒
  FLAT (MAP char_to_bits (MAP2 charxor cs ds)) =
  MAP2 (λx y. x ⇎ y) (FLAT (MAP char_to_bits cs)) (FLAT (MAP char_to_bits ds))
Proof
  Induct>>rw[]>>
  Cases_on`ds`>>fs[]>>
  DEP_REWRITE_TAC[MAP2_APPEND]>>
  simp[char_to_bits_charxor]
QED

Theorem FLAT_REPLICATE:
  ∀n.
  (∀x. MEM x ls ⇒ x = y) ⇒
  FLAT (REPLICATE n ls) =
  REPLICATE (n * LENGTH ls) y
Proof
  Induct>>rw[] >>
  simp[ADD1,LEFT_ADD_DISTRIB,GSYM REPLICATE_APPEND]>>
  rw[LIST_EQ_REWRITE,EL_REPLICATE]>>
  metis_tac[MEM_EL]
QED

Theorem string_to_bits_extend_s:
  string_to_bits (extend_s s n) =
  string_to_bits s ++ REPLICATE (8 * (n − strlen s)) F
Proof
  rw[extend_s_def,string_to_bits_def]>>
  DEP_REWRITE_TAC[FLAT_REPLICATE |> Q.GEN `y` |> Q.ISPEC`F`]>>
  simp[]>>
  EVAL_TAC
QED

Theorem charxor_comm:
  charxor d c = charxor c d
Proof
  rw[charxor_def]
QED

Theorem strxor_aux_comm:
  ∀s t.
  strxor_aux t s = strxor_aux s t
Proof
  ho_match_mp_tac strxor_aux_ind>>rw[strxor_aux_def]
  >-
    (Cases_on`t`>>simp[strxor_aux_def])>>
  simp[charxor_comm]
QED

Theorem strxor_comm:
  strxor t s = strxor s t
Proof
  rw[strxor_def,strxor_aux_comm]
QED

Theorem charxor_assoc:
  charxor (charxor a b) c =
  charxor a (charxor b c)
Proof
  rw[charxor_def]
QED

Theorem strxor_aux_assoc:
  ∀a c b.
  strxor_aux (strxor_aux a b) c =
  strxor_aux a (strxor_aux b c)
Proof
  ho_match_mp_tac strxor_aux_ind>>rw[strxor_aux_def]
  >-
    (Cases_on`b`>>simp[strxor_aux_def])>>
  Cases_on`b`>>simp[strxor_aux_def]>>
  simp[charxor_assoc]
QED

Theorem strxor_assoc:
  strxor (strxor a b) c =
  strxor a (strxor b c)
Proof
  rw[strxor_def,strxor_aux_assoc]
QED

Theorem strxor_compute:
  strxor s t =
  implode (
    strxor_aux (explode (extend_s s (strlen t))) (explode t))
Proof
  Cases_on`strlen s < strlen t`
  >- (
    simp[strxor_def]>>
    PURE_ONCE_REWRITE_TAC[strxor_aux_comm]>>
    DEP_REWRITE_TAC[strxor_aux_prop]>>simp[extend_s_def])>>
  simp[extend_s_def,strxor_def]
QED

Theorem strxor_prop:
  strlen t ≤ strlen s ⇒
  string_to_bits (strxor s t) =
  MAP2 (λx y. x ⇎ y) (string_to_bits s)
    (string_to_bits (extend_s t (strlen s)))
Proof
  rw[strxor_def]>>
  DEP_ONCE_REWRITE_TAC[strxor_aux_prop]>>
  simp[string_to_bits_extend_s,string_to_bits_def]>>
  DEP_REWRITE_TAC[MAP2_charxor]>>
  simp[]>>
  DEP_REWRITE_TAC[FLAT_REPLICATE |> Q.GEN `y` |> Q.ISPEC`F`]>>
  simp[]>>
  EVAL_TAC
QED

Theorem sum_bitlist_aux_REPLICATE_F:
  ∀k. sum_bitlist_aux w (REPLICATE n F) k = 0
Proof
  Induct_on`n`>>rw[]>>fs[sum_bitlist_aux_def,o_DEF,ADD1,of_bool_def]>>
  first_x_assum(qspec_then`k+1` mp_tac)>>simp[]
QED

Theorem sum_bitlist_aux_APPEND:
  ∀xs k.
  sum_bitlist_aux w (xs ++ ys) k =
  sum_bitlist_aux w xs k +
  sum_bitlist_aux w ys (k + LENGTH xs)
Proof
  simp[sum_bitlist_aux_def]>>
  Induct>>rw[o_DEF,ADD1]>>
  first_x_assum(qspec_then`k+1` mp_tac)>>
  simp[]
QED

Theorem sum_bitlist_REPLICATE_F:
  sum_bitlist w (bs ++ REPLICATE n F) =
  sum_bitlist w bs
Proof
  rw[sum_bitlist_def]
  >-
    (Cases_on`n`>>simp[]>>EVAL_TAC)
  >-
    (Cases_on`n`>>simp[]>>
    metis_tac[sum_bitlist_aux_REPLICATE_F])>>
  Cases_on`bs`>>fs[sum_bitlist_aux_APPEND]>>
  metis_tac[sum_bitlist_aux_REPLICATE_F]
QED

Theorem isat_strxor_extend_s:
  isat_strxor w (extend_s s n) ⇔
  isat_strxor w s
Proof
  rw[isat_strxor_def]>>
  simp[string_to_bits_extend_s,sum_bitlist_REPLICATE_F]
QED

Theorem isat_strxor_strxor:
  isat_strxor w s ∧
  isat_strxor w t ==>
  isat_strxor w (strxor s t)
Proof
  wlog_tac`strlen t ≤ strlen s` [`s`,`t`]
  >-
    simp[Once strxor_comm]>>
  rw[]>>
  rw[isat_strxor_def,strxor_prop]>>
  match_mp_tac sum_bitlist_xor>>
  fs[]>>
  CONJ_TAC >-
    rw[extend_s_def]>>
  simp[GSYM isat_strxor_def]>>
  metis_tac[isat_strxor_extend_s]
QED

Theorem sat_cmsxor_cons[simp]:
  sat_cmsxor w (x :: xs) =
  (satisfies_lit w x ⇎ sat_cmsxor w xs)
Proof
  rw[sat_cmsxor_def]>>
  Cases_on`satisfies_lit w x`>>rw[of_bool_def]>>
  intLib.ARITH_TAC
QED

Theorem LUPDATE_isolate:
  n < LENGTH ls ⇒
  LUPDATE v n ls =
  TAKE n ls ++ [v] ++ DROP (n+1) ls
Proof
  rw[LIST_EQ_REWRITE,EL_LUPDATE]>>
  rw[EL_APPEND_EQN]>>fs[EL_TAKE,EL_DROP]
QED

Theorem SUM_TAKE_DROP:
  SUM ls =
  SUM (TAKE n ls) + SUM (DROP n ls)
Proof
  rw[GSYM SUM_APPEND]
QED

Theorem SUM_DROP:
  SUM (DROP n ls) =
  SUM ls - SUM (TAKE n ls)
Proof
  assume_tac SUM_TAKE_DROP>>
  intLib.ARITH_TAC
QED

Theorem SUM_MEM_bound:
  MEM x ls ⇒ x ≤ SUM ls
Proof
  rw[]>>
  `I x ≤ SUM (MAP I ls)` by
    metis_tac[SUM_MAP_MEM_bound]>>
  fs[]
QED

Theorem SUM_LUPDATE:
  n < LENGTH ls ⇒
  SUM (LUPDATE v n ls) =
  SUM ls - EL n ls + v
Proof
  rw[]>>
  DEP_ONCE_REWRITE_TAC[LUPDATE_isolate]>>
  simp[SUM_APPEND]>>
  `DROP (n+1) ls = DROP 1 (DROP n ls)` by
    simp[DROP_DROP]>>
  pop_assum SUBST_ALL_TAC>>
  simp[Once SUM_DROP]>>
  simp[TAKE1_DROP]>>
  `EL n ls <= SUM (DROP n ls)` by
    (match_mp_tac SUM_MEM_bound>>
    fs[MEM_DROP]>>
    qexists_tac`0`>>simp[])>>
  assume_tac SUM_TAKE_DROP>>
  intLib.ARITH_TAC
QED

Theorem MAPi_LUPDATE:
  MAPi f (LUPDATE v n ls) =
  LUPDATE (f n v) n (MAPi f ls)
Proof
  rw[LIST_EQ_REWRITE,EL_LUPDATE]>>
  rw[]
QED

Theorem sum_bitlist_alt:
  sum_bitlist w ls =
  SUM (MAPi (λn e. of_bool ((n = 0 ∨ w n) ∧ e)) ls)
Proof
  rw[sum_bitlist_def]>>
  Cases_on`ls`>>fs[sum_bitlist_aux_def,o_DEF,ADD1]
QED

Theorem sum_bitlist_LUPDATE:
  n < LENGTH ls ⇒
  sum_bitlist w (LUPDATE b n ls) =
  sum_bitlist w ls - of_bool ((n = 0 ∨ w n) ∧ EL n ls)
    + of_bool ((n = 0 ∨ w n) ∧ b)
Proof
  rw[sum_bitlist_alt,MAPi_LUPDATE,SUM_LUPDATE]
QED

Theorem of_bool_at_least_SUM:
  n < LENGTH ls ⇒
  of_bool ((n = 0 ∨ w n) ∧ EL n ls) ≤ sum_bitlist w ls
Proof
  rw[sum_bitlist_alt]>>
  match_mp_tac SUM_MEM_bound>>
  simp[MEM_MAPi]>>
  metis_tac[]
QED

Theorem isat_strxor_flip_bit:
  n < LENGTH (string_to_bits s) ⇒
  (isat_strxor w (flip_bit s n) ⇔
  (isat_strxor w s ⇔ ¬(n = 0 ∨ w n)))
Proof
  rw[flip_bit_def,isat_strxor_def,string_to_bits_set_bit,sum_bitlist_LUPDATE]>>
  qmatch_goalsub_abbrev_tac`A - B`>>
  `B ≤ A` by (
    unabbrev_all_tac>>
    match_mp_tac of_bool_at_least_SUM>>fs[])>>
  unabbrev_all_tac>>
  Cases_on`n ≠ 0 ∧ ¬w n`>>simp[of_bool_def]>>
  qmatch_goalsub_abbrev_tac`of_bool (A ∧ _)`>>
  `A` by fs[Abbr`A`]>>
  simp[get_bit_string_to_bits]>>
  fs[]>>
  ntac 3 (pop_assum kall_tac)>>
  Cases_on`EL n (string_to_bits s)`>>fs[of_bool_def]>>
  intLib.ARITH_TAC
QED

Theorem strlen_set_bit[simp]:
  strlen (set_bit s n b) = strlen s
Proof
  rw[set_bit_def,set_char_def]
QED

Theorem strlen_flip_bit[simp]:
  strlen (flip_bit s n) = strlen s
Proof
  rw[flip_bit_def,set_bit_def,set_char_def]
QED

Theorem strlen_extend_s:
  a < 8 * strlen (extend_s s (a DIV 8 + 1))
Proof
  simp[extend_s_def]>>
  DEP_REWRITE_TAC[DIV_LT_X] >> simp[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem conv_xor_sound:
  ∀ls s.
  EVERY nz_lit ls ⇒
  (isat_strxor w (conv_xor s ls) ⇔
  ((isat_strxor w s) ⇎ (sat_cmsxor w ls)))
Proof
  Induct>>fs[conv_xor_aux_def,conv_xor_def]>>rw[]
  >-
    simp[sat_cmsxor_def]
  >- (
    reverse(Cases_on`h`>>
      fs[satisfies_lit_def,to_ilit_def])
    >-
      `F` by intLib.ARITH_TAC>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >-
      simp[strlen_extend_s]>>
    simp[isat_strxor_extend_s]>>
    metis_tac[]) >>
  Cases_on`h`>>
  fs[satisfies_lit_def,to_ilit_def]
  >-
    `F` by intLib.ARITH_TAC>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[strlen_extend_s,isat_strxor_extend_s]>>
  CONJ_TAC >-
    rw[extend_s_def]>>
  metis_tac[]
QED

(* The all-zero bitstring represents the trivial XOR 0 = 0 *)
Definition is_emp_xor_def:
  is_emp_xor s =
  EVERY (λc. c = CHR 0) (explode s)
End

Theorem is_emp_xor_eq:
  is_emp_xor x ⇒
  (x = extend_s «» (strlen x))
Proof
  rw[extend_s_def,is_emp_xor_def]>>
  Cases_on`x`>>fs[]>>
  rw[LIST_EQ_REWRITE,EL_REPLICATE]>>
  fs[EVERY_EL]
QED

Theorem isat_strxor_is_emp_xor:
  is_emp_xor x ⇒
  isat_strxor w x
Proof
  rw[]>>drule is_emp_xor_eq>>
  disch_then SUBST_ALL_TAC>>
  simp[isat_strxor_extend_s]>>
  EVAL_TAC
QED

Theorem strxor_aux_empty:
  ∀xs ys.
  EVERY (λc. c = CHR 0) ys ∧
  LENGTH ys ≤ LENGTH xs ⇒
  strxor_aux xs ys = xs
Proof
  ho_match_mp_tac strxor_aux_ind>>rw[strxor_aux_def]
QED

Theorem isat_strxor_add_is_emp_xor:
  is_emp_xor x ⇒
  isat_strxor w (strxor y x) =
  isat_strxor w y
Proof
  rw[strxor_compute]>>
  DEP_REWRITE_TAC[strxor_aux_empty]>>
  simp[isat_strxor_extend_s]>>
  fs[is_emp_xor_def]>>
  rw[extend_s_def]
QED

Theorem charxor_self:
  charxor c c = CHR 0
Proof
  rw[charxor_def,fromByte_def]
QED

Theorem strxor_self:
  is_emp_xor (strxor X X)
Proof
  simp[strxor_def]>>
  DEP_REWRITE_TAC[strxor_aux_prop,is_emp_xor_def]>>
  rw[]>>
  simp[EVERY_MAP,MAP2_MAP,charxor_self]
QED
