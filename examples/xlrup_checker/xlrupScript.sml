(*
   Basic specification of an xlrup checker (minimal optimization)
*)
open preamble miscTheory mlstringTheory cnf_extTheory blastLib sptreeTheory mergesortTheory mlvectorTheory;

val _ = new_theory "xlrup";

(* Internal representations *)
Type cclause = ``:int list``;

Type strxor = ``:mlstring``;
Type rawxor = ``:int list``;

(* The constraint
  \Sum c*X ≥ k,
  together with auxiliary counters UB, LB
  which are required to bound \Sum c*X from above
  and below, respectively (for all assignments).
*)
Type cardc = ``:(num # int vector) # int # int # int``

(* A cardinality constraint and the reification literal on the RHS *)
Type ibnn = ``:cardc # int``;

(* Satisfiability for clauses is defined by interpreting into the
  top-level semantics *)
Definition interp_lit_def:
  interp_lit (l:int) =
  if l > 0 then Pos (Num (ABS l))
  else Neg (Num (ABS l))
End

Definition isat_cclause_def:
  isat_cclause w ls ⇔
  ∃l. MEM l ls ∧ l ≠ 0 ∧ sat_lit w (interp_lit l)
End

Definition isat_fml_gen_def:
  isat_fml_gen sem w fml ⇔
    (∀C. C ∈ fml ⇒ sem w  C)
End

(* Satisfiability for XORs uses a string-based
  internal representation *)

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
  isat_strxor (w:assignment) x =
    EVEN (sum_bitlist w (string_to_bits x))
End

Definition foldli_ons_def:
  foldli_ons f e (off,ns) =
  foldli (λn i acc. f (off+n) i acc) e ns
End

Definition isat_cardc_def:
  isat_cardc (w:assignment) ((ons,k,lb,ub):cardc) ⇔
  k ≤
  foldli_ons (λn i acc. if w n then i + acc else acc) 0i ons
End

Definition isat_ibnn_def:
  isat_ibnn (w:assignment) ((cc,y):ibnn) ⇔
  (isat_cardc w cc ⇔ sat_lit w (interp_lit y))
End

(* offset doesn't actually matter here *)
Definition wf_cardc_def:
  wf_cardc ((ons,k,lb,ub):cardc) ⇔
  lb ≤ foldli_ons
    (λn i acc. if i < 0 then i + acc else acc) 0i ons ∧
  foldli_ons
    (λn i acc. if i > 0 then i + acc else acc) 0i ons ≤ ub
End

Definition wf_ibnn_def:
  wf_ibnn ((cc,y):ibnn) ⇔
  wf_cardc cc
End

Overload isat_cfml = ``isat_fml_gen isat_cclause``;
Overload isat_xfml = ``isat_fml_gen isat_strxor``;
Overload isat_bfml = ``isat_fml_gen isat_ibnn``;

Definition isat_fml_def:
  isat_fml w f (cfml,xfml,bfml) ⇔
  isat_cfml w cfml ∧
  isat_xfml (w o f) xfml ∧
  isat_bfml w bfml
End

(* Connection to the top-level semantics *)
Definition conv_lit_def:
  (conv_lit (Pos n) = (&n):int) ∧
  (conv_lit (Neg n) = -(&n):int)
End

Definition conv_cfml_def:
  conv_cfml cfml = MAP (MAP conv_lit) cfml
End

Theorem interp_lit_conv_lit:
  nz_lit y ⇒
  interp_lit (conv_lit y) = y
Proof
  Cases_on`y`>>
  rw[conv_lit_def,interp_lit_def,var_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem conv_lit_interp_lit:
  conv_lit (interp_lit y) = y
Proof
  rw[interp_lit_def,conv_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem nz_lit_conv_lit:
  nz_lit y ⇒ conv_lit y ≠ 0
Proof
  Cases_on`y`>>rw[conv_lit_def,var_lit_def]
QED

Theorem isat_cclause_MAP_conv_lit:
  EVERY nz_lit C ⇒
  (isat_cclause w (MAP conv_lit C) ⇔
  sat_clause w C)
Proof
  rw[isat_cclause_def,sat_clause_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  metis_tac[interp_lit_conv_lit,nz_lit_conv_lit]
QED

Theorem conv_cfml_sound:
  EVERY (EVERY nz_lit) cfml ⇒
  (isat_cfml w (set (conv_cfml cfml)) ⇔
  (∀C. C ∈ set cfml ⇒ sat_clause w C))
Proof
  rw[isat_fml_gen_def,conv_cfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  simp[GSYM EVERY_MEM]>>
  match_mp_tac EVERY_CONG>>rw[]>>
  irule isat_cclause_MAP_conv_lit>>
  gvs[EVERY_MEM]>>
  metis_tac[]
QED

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
  conv_xor s x = conv_xor_aux s (MAP conv_lit x)
End

Theorem MAPi_MAP:
  ∀xs g.
  MAPi g (MAP f xs) =
  MAPi (λn e. g n (f e)) xs
Proof
  Induct>>rw[o_DEF]
QED

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

(* This is actually fully symmetric, but
  we'll actually always check and
  pad s to the right length if needed *)
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
  (sat_lit w x ⇎ sat_cmsxor w xs)
Proof
  rw[sat_cmsxor_def]>>
  Cases_on`sat_lit w x`>>rw[of_bool_def]>>
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
      fs[sat_lit_def,conv_lit_def,var_lit_def])
    >-
      `F` by intLib.ARITH_TAC>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >-
      simp[strlen_extend_s]>>
    simp[isat_strxor_extend_s]>>
    metis_tac[]) >>
  Cases_on`h`>>
  fs[sat_lit_def,conv_lit_def,var_lit_def]
  >-
    `F` by intLib.ARITH_TAC>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[strlen_extend_s,isat_strxor_extend_s]>>
  CONJ_TAC >-
    rw[extend_s_def]>>
  metis_tac[]
QED

Theorem sum_bitlist_first_bit:
  EVEN (sum_bitlist w (b::REPLICATE n F)) = ¬ b
Proof
  rw[sum_bitlist_def,sum_bitlist_aux_REPLICATE_F]
QED

(* Implementation:
  For fast parsing, XORs are represented "raw" using int lists *)
Datatype:
  xlrup =
  | Del (num list) (* Clauses to delete *)
  | RUP num cclause (num list)
    (* RUP n C hints : derive clause C by RUP using hints *)

  | XOrig num (lit list)
    (* XOrig n C : add XOR C from original at ID n *)
  | XAdd num rawxor (num list) (num list)
    (* Xadd n C hints rhints derive XOR C by adding XORs using
      hints and the rup hints (rhints) *)
  | XDel (num list) (* XORs to delete *)
  | CFromX num cclause (num list)
    (* Derive clause from hint XORs *)
  | XFromC num rawxor (num list)
    (* Derive XOR from hint clauses *)

  | BDel (num list) (* BNN constraints to delete *)
  | CFromB num cclause num (num list)
    (* Derive clause from hint BNN and rup hints *)
End

Definition delete_literals_def:
  delete_literals (C:cclause) (D:cclause) =
  FILTER (λx. ¬MEM x D) C
End

(* Checking for RUP *)
Definition is_rup_def:
  (is_rup fml [] (C:cclause) = F) ∧
  (is_rup fml (i::is) C =
  case lookup i fml of
    NONE => F
  | SOME Ci =>
  case delete_literals Ci C of
    [] => T
  | [l] => is_rup fml is (-l :: C)
  | _ => F)
End

(* Add together xors *)
Definition add_xors_aux_def:
  (add_xors_aux fml [] s = SOME s) ∧
  (add_xors_aux fml (i::is) s =
  case lookup i fml of NONE => NONE
  | SOME x =>
    add_xors_aux fml is (strxor s x))
End

Definition is_emp_xor_def:
  is_emp_xor s =
  EVERY (λc. c = CHR 0) (explode s)
End

(* Unit propagation on an XOR *)
Definition unit_prop_xor_def:
  unit_prop_xor t s l =
  let n = Num (ABS l) in
  case lookup n t of NONE => s
  | SOME n =>
  if n < 8 * strlen s then
    if l > 0 then
      (if get_bit s n then
        flip_bit (set_bit s n F) 0
      else s)
    else set_bit s n F
  else s
End

(* Extracts unit clauses in REVERSE order *)
Definition get_units_def:
  (get_units fml [] cs = SOME cs) ∧
  (get_units fml (i::is) cs =
  case lookup i fml of
  | SOME [l] =>
    get_units fml is (l::cs)
  | _ => NONE)
End

Definition unit_props_xor_def:
  unit_props_xor fml t ls s =
  case get_units fml ls [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor t) s cs)
End

Definition is_xor_def:
  is_xor def fml is cfml cis t s =
  let r = extend_s (strlit "") def in
  case add_xors_aux fml is (strxor r s)
    of NONE => F
  | SOME x =>
    case unit_props_xor cfml t cis x of
      NONE => F
    | SOME y => is_emp_xor y
End

Definition conv_rawxor_def:
  conv_rawxor mv x =
  let s = extend_s (strlit "") (MAX 1 mv)  in
  let s = flip_bit s 0 in
  conv_xor_aux s x
End

Definition strxor_imp_cclause_def:
  strxor_imp_cclause mv s c =
  let t = conv_rawxor mv c in
  is_emp_xor (strxor s t)
End

Definition is_cfromx_def:
  is_cfromx def fml is c =
  let r = extend_s (strlit "") def in
  case add_xors_aux fml is r of NONE => F
  | SOME x =>
    strxor_imp_cclause def x c
End

Definition get_constrs_def:
  (get_constrs fml [] = SOME []) ∧
  (get_constrs fml (i::is) =
    case lookup i fml of
      NONE => NONE
    | SOME Ci =>
      (case get_constrs fml is of NONE => NONE
      | SOME Cs => SOME (Ci::Cs)))
End

Definition clauses_from_rawxor_def:
  (clauses_from_rawxor [] b =
    if b then [[]] else []) ∧
  (clauses_from_rawxor (l::ls) b =
    MAP (λxs. l::xs) (clauses_from_rawxor ls b) ++
    MAP (λxs. (-l:int)::xs) (clauses_from_rawxor ls (~b)))
End

(* clause c implies d *)
Definition imp_cclause_def:
  imp_cclause c d ⇔
  EVERY (λl. MEM l d) c
End

Definition check_rawxor_imp_def:
  check_rawxor_imp ds rx =
  let cs = clauses_from_rawxor rx T in
  EVERY (λc. EXISTS (λd. imp_cclause d c) ds) cs
End

(* Every clause in ds must be in cs *)
Definition is_xfromc_def:
  is_xfromc fml is rx =
  case get_constrs fml is of NONE => F
  | SOME ds =>
    check_rawxor_imp ds rx
End

Definition conv_xor_mv_def:
  conv_xor_mv mv x =
  conv_rawxor mv (MAP conv_lit x)
End

Definition get_name_def:
  get_name (t,n) (v:num) =
  case lookup v t of
    NONE => (n, (insert v n t, n+(1:num)))
  | SOME m => (m, (t,n))
End

Definition ren_int_ls_def:
  (ren_int_ls tn [] (acc:int list) = (REVERSE acc, tn)) ∧
  (ren_int_ls tn (i::is) acc =
    let v = Num (ABS i) in
    let (m,tn) = get_name tn v in
    let vv = if i < (0:int) then -&m else &m in
    ren_int_ls tn is (vv::acc))
End

Definition ren_lit_ls_def:
  (ren_lit_ls tn [] (acc:lit list) = (REVERSE acc, tn)) ∧
  (ren_lit_ls tn (i::is) acc =
    case i of
      Pos v =>
      let (m,tn) = get_name tn v in
        ren_lit_ls tn is (Pos m::acc)
    | Neg v =>
      let (m,tn) = get_name tn v in
        ren_lit_ls tn is (Neg m::acc))
End

Definition lookup_ons_def:
  lookup_ons n (off,ns) =
  if n < off then 0i
  else
  let n = n - off in
    if n < length ns
    then
      sub ns n
    else 0
End

Definition prop_cardc_def:
  (prop_cardc ons k lb ub [] = (k:int,lb:int,ub:int)) ∧
  (prop_cardc ons k lb ub (l::ls) =
    let n = Num (ABS l) in
    let c = lookup_ons n ons in
    if c = 0 then
      prop_cardc ons k lb ub ls
    else
      let k' = if l > 0 then k else k - c in
      if c > 0 then
        prop_cardc ons k' lb (ub - c) ls
      else
        prop_cardc ons k' (lb - c) ub ls)
End

(* Propagate *)
Definition prop_lit_def:
  (prop_lit ny [] = NONE) ∧
  (prop_lit ny (l::ls) =
    if ny = Num (ABS l) then
      SOME (l <= 0)
    else prop_lit ny ls)
End

(* True if given BNN constraint is falsified by
  the propagated literals *)
Definition check_ibnn_def:
  check_ibnn ((ons,k,lb,ub),y) ls = (
  case prop_lit (Num (ABS y)) ls of
    NONE => F
  | SOME b =>
    let b' = (b ⇔ y > 0) in
    let (k,lb,ub) = prop_cardc ons k lb ub ls in
    if b' then
      ub < k
    else
      k ≤ lb)
End

(* TODO: unify the two RUPs with efficient representations
  This version makes sure the propagations are distinct
Definition is_rup2_def:
  (is_rup2 fml [] (C:cclause) = SOME C) ∧
  (is_rup2 fml (i::is) C =
  case lookup i fml of
    NONE => NONE
  | SOME Ci =>
  case delete_literals Ci C of
    [] => NONE
  | [l] =>
    if l = 0 ∨ MEM (Num (ABS l)) (MAP (λl. Num (ABS l)) C)
    then NONE
    else
      is_rup2 fml is (-l :: C)
  | _ => NONE)
End
 *)

Definition mk_strict_aux_def:
  (mk_strict_aux x [] acc = x::acc) ∧
  (mk_strict_aux x (y::ys) acc =
    if x = (y:int) then
      mk_strict_aux x ys acc
    else mk_strict_aux y ys (x::acc))
End

Definition mk_strict_def:
  mk_strict ls =
  case mergesort_tail (\x y. x ≥ y) ls of
    [] => []
  | (x::xs) => mk_strict_aux x xs []
End

Definition is_cfromb_def:
  is_cfromb C cfml bfml ib i0 =
  case lookup ib bfml of NONE => F
  | SOME bnn =>
  case get_units cfml i0 [] of NONE => F
  | SOME cs =>
  let ls = MAP (λl. -l) cs ++ C in
    check_ibnn bnn (mk_strict ls)
End

Definition min_loop_def:
  min_loop [] min k = (min,k:int) ∧
  min_loop (Pos n :: rest) min k = min_loop rest (MIN n min) k ∧
  min_loop (Neg n :: rest) min k = min_loop rest (MIN n min) (k - 1)
End

Definition min_def:
  min (Pos n) rest k = min_loop rest n k ∧
  min (Neg n) rest k = min_loop rest n k
End

Definition to_spt_def:
  to_spt [] min acc = acc ∧
  to_spt ((Pos n) :: rest) min acc =
    (let m = n - min in
       to_spt rest min (case lookup m acc of
        | NONE => insert m 1 acc
        | SOME i => if i = -1 then delete m acc else insert m (i+1) acc)) ∧
  to_spt ((Neg n) :: rest) min acc =
    (let m = n - min in
       to_spt rest min (case lookup m acc of
        | NONE => insert m (-1:int) acc
        | SOME i => if i = 1 then delete m acc else insert m (i-1) acc))
End

Definition lb_ub_spt_def:
  lb_ub_spt LN = (0:int,0:int) ∧
  lb_ub_spt (LS x) = (if x < 0 then (x,0) else (0,x)) ∧
  lb_ub_spt (BN t1 t2) =
    (let (lb1,ub1) = lb_ub_spt t1 in
     let (lb2,ub2) = lb_ub_spt t2 in
       (lb1 + lb2, ub1 + ub2)) ∧
  lb_ub_spt (BS t1 i t2) =
    (let (lb1,ub1) = lb_ub_spt t1 in
     let (lb2,ub2) = lb_ub_spt t2 in
       if i < 0 then
         (lb1 + i + lb2, ub1 + ub2)
       else
         (lb1 + lb2, ub1 + i + ub2))
End

(* TODO: convert a CMS bnn into an ibnn *)
(*
Definition conv_bnn_def:
  conv_bnn (([],k,y):cmsbnn) = (((0:num,LN),& k,0,0), conv_lit y):ibnn ∧
  conv_bnn ((c::cs,k,y)) =
    let (min,new_k) = min c cs (& k) in
    let spt = to_spt (c::cs) min LN in
    let (lb,ub) = lb_ub_spt spt in
      (((min, spt), new_k, lb, ub), conv_lit y)
End
*)

(* note: in CFromX, we remap the clause for checking against XORs but store the original clause  *)
Definition check_xlrup_def:
  check_xlrup xorig xlrup cfml xfml bfml tn def =
  case xlrup of
    Del cl =>
    SOME (FOLDL (\a b. delete b a) cfml cl, xfml, bfml,
      tn, def)
  | RUP n C i0 =>
    if is_rup cfml i0 C then
      SOME (insert n C cfml, xfml, bfml, tn, def)
    else NONE
  | XOrig n rX =>
    if MEM rX xorig
    then
      let (mX,tn) = ren_lit_ls tn rX [] in
      let X = conv_xor_mv def mX in
      SOME (cfml, insert n X xfml, bfml,
        tn, MAX def (strlen X))
    else NONE
  | XAdd n rX i0 i1 =>
    let (mX,tn) = ren_int_ls tn rX [] in
    let X = conv_rawxor def mX in
    if is_xor def xfml i0 cfml i1 (FST tn) X then
      SOME (cfml, insert n X xfml, bfml,
        tn, MAX def (strlen X))
    else NONE
  | XDel xl =>
      SOME (cfml, FOLDL (\a b. delete b a) xfml xl, bfml,
        tn, def)
  | CFromX n C i0 =>
    let (mC,tn) = ren_int_ls tn C [] in
    if is_cfromx def xfml i0 mC then
      SOME (insert n C cfml, xfml, bfml,
        tn, def)
    else NONE
  | XFromC n rX i0 =>
    if is_xfromc cfml i0 rX then
      let (mX,tn) = ren_int_ls tn rX [] in
      let X = conv_rawxor def mX in
      SOME (cfml, insert n X xfml, bfml,
        tn, MAX def (strlen X))
    else NONE
  | BDel bl =>
      SOME (cfml, xfml, FOLDL (\a b. delete b a) bfml bl,
        tn, def)
  | CFromB n C ib i0 =>
    if is_cfromb C cfml bfml ib i0 then
      SOME (insert n C cfml, xfml, bfml,
        tn, def)
    else NONE
End

Definition check_xlrups_def:
  (check_xlrups xorig [] cfml xfml bfml tn def =
    SOME (cfml,xfml,bfml,tn,def)) ∧
  (check_xlrups xorig (x::xs) cfml xfml bfml tn def =
  case check_xlrup xorig x cfml xfml bfml tn def of
    NONE => NONE
  | SOME (cfml',xfml',bfml',tn',def') =>
    check_xlrups xorig xs cfml' xfml' bfml' tn' def')
End

Definition contains_emp_def:
  contains_emp fml =
  let ls = MAP SND (toAList fml) in
  MEM [] ls
End

Definition check_xlrups_unsat_def:
  check_xlrups_unsat xorig xlrups cfml xfml bfml tn def =
  case check_xlrups xorig xlrups cfml xfml bfml tn def of
    NONE => F
  | SOME (cfml',_) => contains_emp cfml'
End

(* Proofs *)
Theorem interp_lit_eq:
  interp_lit x = interp_lit y ⇒
  x = y
Proof
  rw[interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem set_delete_literals:
  set (delete_literals C D)  =
  set C DIFF set D
Proof
  simp[delete_literals_def]>>
  fs[EXTENSION,MEM_MAP]>>
  rw[EQ_IMP_THM]>>
  fs[MEM_FILTER]>>
  metis_tac[interp_lit_eq]
QED

Theorem is_rup_sound:
  ∀is C.
  is_rup fml is C ∧
  isat_cfml w (range fml) ⇒
  isat_cclause w C
Proof
  Induct>>fs[is_rup_def]>>
  ntac 3 strip_tac>>
  every_case_tac>>fs[]>>
  `set x DIFF set C =
   set (delete_literals x C)` by
   metis_tac[set_delete_literals]>>
  gvs[]
  >- (
    fs[isat_fml_gen_def,PULL_EXISTS,range_def]>>
    first_x_assum drule>>
    rw[isat_cclause_def]>>
    first_x_assum (irule_at Any)>>
    rfs[EXTENSION,MEM_MAP]>>
    metis_tac[])
  >- (
    first_x_assum (drule_at Any)>>
    gvs[isat_cclause_def,EXTENSION]>>
    reverse (rw[])
    >- metis_tac[]>>
    fs[isat_fml_gen_def,PULL_EXISTS,range_def]>>
    first_x_assum drule>>
    rw[isat_cclause_def]>>
    Cases_on`MEM l C`
    >- metis_tac[] >>
    first_x_assum (qspec_then`l` mp_tac)>>
    simp[]>>
    rw[]>>
    `h' = 0` by (
      gvs[sat_lit_def,interp_lit_def]>>
      every_case_tac>>gvs[]>>
      intLib.ARITH_TAC))
QED

Theorem add_xors_aux_acc:
  ∀is s t.
  add_xors_aux fml is s = SOME t ⇒
  add_xors_aux fml is (strxor s u) = SOME (strxor t u)
Proof
  Induct>>rw[add_xors_aux_def]>>
  gvs[AllCaseEqs()]>>
  `strxor (strxor s u) x = strxor (strxor s x) u` by
    metis_tac[strxor_comm,strxor_assoc]>>
  pop_assum SUBST_ALL_TAC>>
  simp[]
QED

Theorem add_xors_aux_imp:
  ∀is s.
  isat_xfml w (range fml) ∧
  isat_strxor w s ∧
  add_xors_aux fml is s = SOME t ⇒
  isat_strxor w t
Proof
  Induct>>rw[add_xors_aux_def]>>fs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  first_x_assum (irule_at Any)>>
  match_mp_tac isat_strxor_strxor>>
  simp[]>>
  fs[isat_fml_gen_def,range_def,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem is_emp_xor_eq:
  is_emp_xor x ⇒
  (x = extend_s (strlit "") (strlen x))
Proof
  rw[extend_s_def,is_emp_xor_def]>>
  Cases_on`x`>>fs[implode_def]>>
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

Theorem isat_stxor_add_is_emp_xor:
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

Theorem delete_preserves_isat_fml_gen:
  isat_fml_gen sem w (range C) ⇒
  isat_fml_gen sem w (range (delete n C))
Proof
  rw[isat_fml_gen_def]>>
  fs[range_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

(* TODO: make generic *)
Theorem delete_clauses_sound:
  ∀l fml.
  isat_fml w f (range fml,x) ⇒
  isat_fml w f (range (FOLDL (λa b. delete b a) fml l),x)
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_fml_gen,isat_fml_def,PAIR]
QED

Theorem delete_xors_sound:
  ∀l x.
  isat_fml w f (fml,range x,rest) ⇒
  isat_fml w f (fml, range (FOLDL (λa b. delete b a) x l), rest)
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_fml_gen,isat_fml_def,PAIR]
QED

Theorem delete_bnns_sound:
  ∀l x.
  isat_fml w f (fml,fml',range x) ⇒
  isat_fml w f (fml,fml',range (FOLDL (λa b. delete b a) x l))
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_fml_gen,isat_fml_def,PAIR]
QED

Theorem range_FOLDL_delete_SUBSET:
  ∀l x.
  range (FOLDL (λa b. delete b a) x l) ⊆
  range x
Proof
  Induct>>rw[]>>
  metis_tac[range_delete,SUBSET_TRANS]
QED

Theorem isat_fml_gen_insert:
  isat_fml_gen sem w (range cfml) ∧
  sem w c ⇒
  isat_fml_gen sem w (range (insert n c cfml))
Proof
  rw[isat_fml_gen_def,range_def,lookup_insert]>>
  gvs[AllCaseEqs()]>>
  metis_tac[]
QED

Theorem isat_cclause_cons:
  isat_cclause w (x::xs) ⇔
  x ≠ 0 ∧ sat_lit w (interp_lit x) ∨ isat_cclause w xs
Proof
  rw[isat_cclause_def]>>
  metis_tac[]
QED

Definition wf_clause_def:
  wf_clause (C:cclause) ⇔ ¬ MEM 0 C
End

Definition wf_cfml_def:
  wf_cfml (cfml:int list num_map) ⇔
  ∀C. C ∈ range cfml ⇒ wf_clause C
End

Definition wf_xlrup_def:
  (wf_xlrup (RUP n C i0) = wf_clause C) ∧
  (wf_xlrup (CFromX n C i0) = wf_clause C) ∧
  (wf_xlrup (XFromC n X i0) = wf_clause X) ∧
  (wf_xlrup (XOrig n rX) = EVERY nz_lit rX) ∧
  (wf_xlrup (CFromB n C ib i0) = wf_clause C) ∧
  (wf_xlrup _ = T)
End

Theorem wf_cfml_delete_clauses:
  ∀l fml.
  wf_cfml fml ⇒
  wf_cfml (FOLDL (λa b. delete b a) fml l)
Proof
  simp[FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>first_x_assum drule>>
  rw[wf_cfml_def]>>
  fs[range_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem wf_cfml_insert:
  wf_cfml fml ∧ wf_clause l ⇒
  wf_cfml (insert n l fml)
Proof
  fs[wf_cfml_def]>>rw[]>>
  gvs[range_def,lookup_insert,AllCaseEqs()]>>
  metis_tac[]
QED

Theorem wf_cfml_check_xlrup:
  wf_cfml cfml ∧ wf_xlrup xlrup ∧
  check_xlrup xorig xlrup cfml xfml bfml tn def =
    SOME (cfml',xfml',bfml',tn',def') ⇒
  wf_cfml cfml'
Proof
  rw[check_xlrup_def]>>gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])
  >-
    metis_tac[wf_cfml_delete_clauses]>>
  fs[wf_xlrup_def]>>
  metis_tac[wf_cfml_insert]
QED

Theorem conv_xor_aux_cclause_sound:
  ∀ls s.
  wf_clause ls ∧
  isat_strxor w (conv_xor_aux s ls) ⇒
  ((isat_strxor w s) ∨ (isat_cclause w ls))
Proof
  Induct>>fs[conv_xor_aux_def]>>rw[]
  >- (
    fs[isat_cclause_cons,wf_clause_def]>>
    first_x_assum drule>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >-
      simp[strlen_extend_s]>>
    simp[isat_strxor_extend_s]>>
    `Num (ABS h) ≠ 0` by intLib.ARITH_TAC>>
    fs[sat_lit_def,interp_lit_def]>>
    metis_tac[])>>
  fs[isat_cclause_cons,wf_clause_def]>>
  first_x_assum drule>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[strlen_extend_s,isat_strxor_extend_s]>>
  CONJ_TAC >- (
    assume_tac (strlen_extend_s |> Q.GEN `a` |> Q.SPEC `Num (ABS h)`)>>
    simp[])>>
  `Num (ABS h) ≠ 0` by intLib.ARITH_TAC>>
  fs[sat_lit_def,interp_lit_def]>>
  metis_tac[]
QED

Theorem strxor_imp_cclause_sound:
  wf_clause c ∧
  strxor_imp_cclause mv s c ∧
  isat_strxor w s ⇒
  isat_cclause w c
Proof
  rw[strxor_imp_cclause_def]>>
  drule isat_strxor_is_emp_xor>>
  disch_then (qspec_then `w` assume_tac)>>
  `isat_strxor w (strxor (conv_rawxor mv c) (strxor s s))` by
    metis_tac[isat_strxor_strxor,strxor_assoc,strxor_comm] >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[isat_stxor_add_is_emp_xor]>>simp[strxor_self]>>
  rw[conv_rawxor_def]>>
  drule conv_xor_aux_cclause_sound>>
  disch_then drule>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[isat_strxor_extend_s]>>
  CONJ_TAC>-
    rw[extend_s_def]>>
  EVAL_TAC
QED

Theorem is_cfromx_sound:
  wf_clause C ∧
  isat_xfml w (range fml) ∧
  is_cfromx def fml is C ⇒
  isat_cclause w C
Proof
  rw[is_cfromx_def]>>
  every_case_tac>>fs[]>>
  match_mp_tac (GEN_ALL strxor_imp_cclause_sound)>>
  fs[]>>
  first_x_assum (irule_at Any)>>
  drule add_xors_aux_imp>>
  disch_then match_mp_tac>>
  first_x_assum (irule_at Any)>>
  simp[isat_strxor_extend_s]>>
  EVAL_TAC
QED

Theorem isat_strxor_cnv_xor_to_aux:
  isat_strxor w (conv_xor s (MAP interp_lit ls)) ⇒
  isat_strxor w (conv_xor_aux s ls)
Proof
  rw[conv_xor_def,MAP_MAP_o,o_DEF]>>
  qmatch_asmsub_abbrev_tac`isat_strxor w (conv_xor_aux s rs)`>>
  qsuff_tac `rs = ls`>>
  rw[]>>
  gvs[]>>
  unabbrev_all_tac>>
  simp[MAP_EQ_ID,conv_lit_interp_lit]
QED

Theorem sat_lit_interp_lit_neg:
  h ≠ 0 ⇒
  sat_lit w (interp_lit (-h)) = ¬ sat_lit w (interp_lit h)
Proof
  rw[interp_lit_def,sat_lit_def]>>
  `F` by intLib.ARITH_TAC
QED

Theorem clauses_from_rawxor_sound:
  ∀rx b.
  wf_clause rx ∧
  EVERY (isat_cclause w)
    (clauses_from_rawxor rx b) ⇒
  (sat_cmsxor w (MAP interp_lit rx) ⇔ b)
Proof
  Induct>>rw[clauses_from_rawxor_def]
  >-
    fs[sat_cmsxor_def,isat_cclause_def]
  >-
    fs[sat_cmsxor_def,isat_cclause_def]>>
  gvs[EVERY_MAP,isat_cclause_cons,wf_clause_def]>>
  Cases_on`sat_lit w (interp_lit h)`>>fs[]
  >- (
    gvs[sat_lit_interp_lit_neg]>>
    first_x_assum(qspec_then`~b` mp_tac)>>
    simp[]>>
    metis_tac[ETA_AX])>>
  first_x_assum(qspec_then`b` mp_tac)>>
  metis_tac[ETA_AX]
QED

Theorem imp_cclause_imp:
  imp_cclause c d ∧
  isat_cclause w c ⇒
  isat_cclause w d
Proof
  rw[imp_cclause_def,isat_cclause_def,EVERY_MEM]>>
  metis_tac[]
QED

Theorem isat_fml_gen_get_constrs:
  ∀is xs x.
  isat_fml_gen sem w (range fml) ∧
  get_constrs fml is = SOME xs ∧
  MEM x xs ⇒
  sem w x
Proof
  Induct>>rw[get_constrs_def]>>
  gvs[AllCaseEqs()]>>
  fs[isat_fml_gen_def,range_def]>>
  metis_tac[]
QED

Theorem is_xfromc_sound:
  wf_clause rX ∧
  isat_cfml w (range fml) ∧
  is_xfromc fml is rX ⇒
  sat_cmsxor w (MAP interp_lit rX)
Proof
  rw[is_xfromc_def]>>
  every_case_tac>>
  drule clauses_from_rawxor_sound>>fs[]>>
  disch_then(qspecl_then[`w`,`T`] mp_tac)>>simp[]>>
  disch_then match_mp_tac>>
  fs[check_rawxor_imp_def,EVERY_MEM]>>
  rw[]>>first_x_assum drule>>
  rw[EXISTS_MEM]>>
  metis_tac[isat_fml_gen_get_constrs,imp_cclause_imp]
QED

Definition tn_inv_def:
  tn_inv (t,n) ⇔
    0 < n ∧ ∀i v. lookup i t = SOME v ⇒ v ≠ 0:num ∧ v < n ∧
    (∀n1 n2 k.
       lookup n1 t = SOME k ∧
       lookup n2 t = SOME k ⇒ n1 = n2)
End

Definition restore_fn_def:
  restore_fn ((t,n):num sptree$num_map # num) v =
    case (some k. lookup k t = SOME v) of
    | NONE => 0
    | SOME k => k
End

Definition restore_lit_def:
  restore_lit tn (Pos n) = Pos (restore_fn tn n) ∧
  restore_lit tn (Neg n) = Neg (restore_fn tn n)
End

Definition restore_int_def:
  restore_int tn i =
  if i > 0
  then
    (&restore_fn tn (Num (ABS i))):int
  else
    -&restore_fn tn (Num (ABS i))
End

Definition can_restore_def:
  can_restore (t,_:num) n = (∃k. lookup k t = SOME (n:num))
End

Definition can_restore_lit_def:
  can_restore_lit tn (Pos n) = can_restore tn n ∧
  can_restore_lit tn (Neg n) = can_restore tn n
End

Definition can_restore_int_def:
  can_restore_int tn i = can_restore tn (Num (ABS i))
End

Definition tn_submap_def:
  tn_submap tn tn' ⇔
    (∀k. can_restore tn k ⇒
         can_restore tn' k ∧
         restore_fn tn' k = restore_fn tn k)
End

Definition can_restore_str_def:
  can_restore_str tn (s:mlstring) =
    ∀i. i ≠ 0 ∧ i < LENGTH (string_to_bits s) ∧
        EL i (string_to_bits s) ⇒
        can_restore tn i
End

Theorem tn_submap_refl:
  tn_submap tn tn
Proof
  gvs [tn_submap_def]
QED

Theorem tn_submap_trans:
  tn_submap tn1 tn2 ∧ tn_submap tn2 tn3 ⇒ tn_submap tn1 tn3
Proof
  gvs [tn_submap_def]
QED

Theorem tn_inv_get_name:
  get_name tn n = (m,tn') ∧ tn_inv tn ⇒
  m ≠ 0 ∧
  tn_inv tn' ∧
  can_restore tn' m ∧
  restore_fn tn' m = n ∧
  tn_submap tn tn'
Proof
  PairCases_on ‘tn’
  \\ gvs [get_name_def,AllCaseEqs(),tn_inv_def,tn_submap_def] \\ rw []
  \\ gvs [tn_inv_def,lookup_insert,can_restore_def,tn_submap_def] \\ rw []
  \\ res_tac \\ gvs [restore_fn_def,tn_submap_def,lookup_insert]
  >-
   (CCONTR_TAC
    \\ Cases_on ‘n1 = i’ \\ gvs []
    \\ Cases_on ‘n2 = i’ \\ gvs []
    \\ res_tac \\ gvs [])
  >-
   (CCONTR_TAC
    \\ Cases_on ‘n1 = n’ \\ gvs []
    \\ Cases_on ‘n2 = n’ \\ gvs []
    \\ res_tac \\ gvs [])
  >- metis_tac []
  >- (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
      >- (Cases_on ‘lookup x tn0’ \\ gvs [] \\ res_tac \\ gvs [])
      \\ gvs [AllCaseEqs()] \\ metis_tac [])
  >- (qexists_tac ‘k'’ \\ fs [AllCaseEqs()] \\ CCONTR_TAC \\ gvs [])
  >-
   (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    >- (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
        \\ gvs [AllCaseEqs()] \\ metis_tac [])
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ CCONTR_TAC \\ Cases_on ‘x = n’ \\ gvs [] \\ metis_tac [])
  >- metis_tac []
  >-
    (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
     \\ res_tac \\ gvs [])
  >- metis_tac []
QED

Theorem ren_lit_ls_nz_lit:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ EVERY nz_lit xs ∧
    EVERY nz_lit acc ∧ tn_inv tn ⇒
    EVERY nz_lit ys
Proof
  Induct_on ‘xs’ \\ gvs [ren_lit_ls_def]
  \\ Cases \\ fs [ren_lit_ls_def] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum $ drule_then $ irule \\ gvs []
  \\ drule tn_inv_get_name \\ gvs [var_lit_def]
QED

Theorem ren_lit_ls_tn_inv:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ tn_inv tn ⇒
    tn_inv tn'
Proof
  Induct_on ‘xs’ \\ gvs [ren_lit_ls_def]
  \\ Cases \\ fs [ren_lit_ls_def] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum $ drule_then $ irule \\ gvs []
  \\ drule tn_inv_get_name \\ gvs []
QED

Theorem every_can_restore_lit_submap:
  tn_submap tn tn' ∧
  EVERY (can_restore_lit tn) acc ⇒
  EVERY (can_restore_lit tn') acc
Proof
  Induct_on ‘acc’ \\ fs []
  \\ Cases \\ fs [can_restore_lit_def]
  \\ gvs [tn_submap_def]
QED

Theorem ren_lit_ls_restore_acc:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ tn_inv tn ∧
    EVERY (can_restore_lit tn) acc
    ⇒
    MAP (restore_lit tn') ys = MAP (restore_lit tn') (REVERSE acc) ++ xs ∧
    EVERY (can_restore_lit tn') ys ∧
    tn_submap tn tn'
Proof
  Induct_on ‘xs’
  \\ fs [ren_lit_ls_def,tn_submap_refl]
  \\ Cases \\ gvs [] \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule
  \\ drule_all tn_inv_get_name \\ strip_tac \\ gvs []
  \\ gvs [can_restore_lit_def,restore_lit_def]
  \\ drule_all every_can_restore_lit_submap \\ fs []
  \\ gvs [tn_submap_trans,SF SFY_ss] \\ gvs [tn_submap_def]
QED

Theorem ren_lit_ls_restore:
  ∀tn xs ys tn'.
    ren_lit_ls tn xs [] = (ys,tn') ∧ tn_inv tn ⇒
    MAP (restore_lit tn') ys = xs ∧
    EVERY (can_restore_lit tn') ys ∧
    tn_submap tn tn'
Proof
  rpt gen_tac \\ strip_tac
  \\ drule ren_lit_ls_restore_acc \\ fs []
QED

Theorem ren_int_ls_tn_inv:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ tn_inv tn ⇒
    tn_inv tn'
Proof
  Induct_on ‘xs’ \\ gvs [ren_int_ls_def]
  \\ Cases \\ fs [ren_int_ls_def] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum $ drule_then $ irule \\ gvs []
  \\ drule tn_inv_get_name \\ gvs []
QED

Theorem every_can_restore_int_submap:
  tn_submap tn tn' ∧
  EVERY (can_restore_int tn) acc ⇒
  EVERY (can_restore_int tn') acc
Proof
  Induct_on ‘acc’ \\ fs []
  \\ Cases \\ fs [can_restore_int_def]
  \\ gvs [tn_submap_def]
QED

Theorem restore_int_simps:
  m ≠ 0 ⇒
  restore_int tn (&m) = &restore_fn tn m ∧
  restore_int tn (-&m) = -&restore_fn tn m
Proof
  rw[restore_int_def]>>
  intLib.ARITH_TAC
QED

Theorem ren_int_ls_restore_acc:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ tn_inv tn ∧
    EVERY (can_restore_int tn) acc
    ⇒
    MAP (restore_int tn') ys =
      MAP (restore_int tn') (REVERSE acc) ++ xs ∧
    EVERY (can_restore_int tn') ys ∧
    tn_submap tn tn'
Proof
  Induct_on ‘xs’
  \\ fs [ren_int_ls_def,tn_submap_refl]
  \\ Cases \\ gvs [] \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule
  \\ drule_all tn_inv_get_name
  \\ strip_tac \\ gvs []
  \\ gvs [can_restore_int_def,can_restore_def,restore_fn_def,o_DEF, GSYM EVERY_MAP]
  \\ drule_all every_can_restore_int_submap \\ fs []
  \\ drule restore_int_simps
  \\ gvs [tn_submap_trans,SF SFY_ss] \\ gvs [tn_submap_def]
QED

Theorem ren_int_ls_restore:
  ∀tn xs ys tn'.
    ren_int_ls tn xs [] = (ys,tn') ∧ tn_inv tn ⇒
    MAP (restore_int tn') ys = xs ∧
    EVERY (can_restore_int tn') ys ∧
    tn_submap tn tn'
Proof
  rpt gen_tac \\ strip_tac
  \\ drule ren_int_ls_restore_acc \\ fs []
QED

Theorem ren_int_ls_wf_clause:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ wf_clause xs ∧
    wf_clause acc ∧ tn_inv tn ⇒
    wf_clause ys
Proof
  Induct_on ‘xs’ \\ gvs [ren_int_ls_def,wf_clause_def]
  \\ Cases \\ fs [ren_int_ls_def] \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum $ drule_then $ irule \\ gvs []
  \\ drule tn_inv_get_name \\ gvs []
QED

Theorem can_restore_str_flip_bit_0:
  can_restore_str tn s ⇒
  can_restore_str tn (flip_bit s 0)
Proof
  rw[can_restore_str_def,flip_bit_def]>>
  gvs[string_to_bits_set_bit,EL_LUPDATE]
QED

Theorem can_restore_str_flip_bit:
  n < LENGTH (string_to_bits s) ∧
  can_restore_str tn s ∧
  can_restore tn n ⇒
  can_restore_str tn (flip_bit s n)
Proof
  rw[can_restore_str_def,flip_bit_def]>>
  gvs[string_to_bits_set_bit,EL_LUPDATE]>>
  every_case_tac>>fs[]
QED

Theorem can_restore_str_extend_s:
  can_restore_str tn s ⇒
  can_restore_str tn (extend_s s n)
Proof
  rw[can_restore_str_def,string_to_bits_extend_s,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  qpat_x_assum`EL _ _` mp_tac>>
  DEP_REWRITE_TAC[EL_REPLICATE]>>
  fs[extend_s_def]>>
  every_case_tac>>fs[]
QED

Theorem can_restore_str_conv_xor_aux:
  ∀ls tn s.
  can_restore_str tn s ∧
  EVERY (can_restore tn) (MAP (λl. Num (ABS l)) ls)
  ⇒
  can_restore_str tn (conv_xor_aux s ls)
Proof
  Induct>>rw[conv_xor_aux_def]>>
  first_x_assum match_mp_tac>>simp[]
  >- (
    match_mp_tac can_restore_str_flip_bit>>
    simp[can_restore_str_extend_s,strlen_extend_s])>>
  match_mp_tac can_restore_str_flip_bit_0>>
  match_mp_tac can_restore_str_flip_bit>>
  simp[strlen_extend_s,can_restore_str_extend_s]
QED

Theorem can_restore_str_conv_xor_mv:
  EVERY (can_restore_lit tn) mX ⇒
  can_restore_str tn (conv_xor_mv def mX)
Proof
  rw[conv_xor_mv_def, conv_rawxor_def, conv_xor_def]>>
  match_mp_tac can_restore_str_conv_xor_aux>>
  rw[]
  >- (
    match_mp_tac can_restore_str_flip_bit_0>>
    match_mp_tac can_restore_str_extend_s>>
    EVAL_TAC>>rw[])>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>rw[]>>
  first_x_assum drule>>
  Cases_on`y`>>fs[conv_lit_def,can_restore_lit_def]
QED

Theorem can_restore_str_conv_rawxor:
  EVERY (can_restore tn) (MAP (λl. Num (ABS l)) mX) ⇒
  can_restore_str tn (conv_rawxor def mX)
Proof
  rw[conv_rawxor_def]>>
  match_mp_tac can_restore_str_conv_xor_aux>>
  rw[]>>
  match_mp_tac can_restore_str_flip_bit_0>>
  match_mp_tac can_restore_str_extend_s>>
  EVAL_TAC>>rw[]
QED

Theorem sat_cmsxor_restore_fn:
  sat_cmsxor (w ∘ restore_fn tn) mX = sat_cmsxor w (MAP (restore_lit tn) mX)
Proof
  fs [sat_cmsxor_def,GSYM MAP_MAP_o]
  \\ rpt AP_TERM_TAC
  \\ Induct_on ‘mX’ \\ fs []
  \\ Cases \\ gvs [restore_lit_def,sat_lit_def]
QED

Theorem can_restore_str_submap:
  tn_submap tn tn' ∧ can_restore_str tn s ⇒ can_restore_str tn' s
Proof
  fs [can_restore_str_def,tn_submap_def]
QED

Theorem isat_strxor_restore_str_submap:
  tn_submap tn tn' ∧
  can_restore_str tn C ∧
  isat_strxor (w ∘ restore_fn tn) C ⇒
  isat_strxor (w ∘ restore_fn tn') C
Proof
  gvs [isat_strxor_def,sum_bitlist_alt] \\ rw []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ rewrite_tac [can_restore_str_def]
  \\ qabbrev_tac ‘x = string_to_bits C’
  \\ rw []
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] “b = x ⇒ (b ⇒ x)”)
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ Induct_on ‘x’ using SNOC_INDUCT >- gvs []
  \\ gvs [SNOC_APPEND,indexedListsTheory.MAPi_APPEND]
  \\ rw []
  >-
   (first_x_assum irule \\ rw [] \\ first_x_assum irule \\ fs []
    \\ metis_tac [rich_listTheory.EL_APPEND1])
  \\ first_x_assum $ qspec_then ‘LENGTH x’ mp_tac
  \\ gvs [rich_listTheory.EL_LENGTH_APPEND]
  \\ Cases_on`x`>>simp[]
  \\ gvs [tn_submap_def,SF CONJ_ss]
QED

Theorem isat_xfml_restore_str_submap:
  tn_submap tn tn' ∧
  (∀s. s ∈ range xfml ⇒ can_restore_str tn s) ∧
  isat_xfml (w ∘ restore_fn tn) (range xfml) ⇒
  isat_xfml (w ∘ restore_fn tn') (range xfml)
Proof
  rw[range_def,isat_fml_gen_def]>>
  match_mp_tac isat_strxor_restore_str_submap>>
  metis_tac[]
QED

Theorem unit_prop_xor_sound:
  tn_inv (t,n) ∧
  sat_lit w (interp_lit l) ⇒
  (isat_strxor (w o restore_fn (t,n)) (unit_prop_xor t X l) ⇔
    isat_strxor (w o restore_fn (t,n)) X)
Proof
  rw[unit_prop_xor_def]>>
  TOP_CASE_TAC>>fs[]>>
  `restore_fn (t,n) x = Num (ABS l) ∧ x ≠ 0` by
    (simp[restore_fn_def]>>
    DEEP_INTRO_TAC some_intro>>fs[tn_inv_def]>>
    rw[]>>first_x_assum drule>>
    metis_tac[])>>
  rw[]>>
  gs[interp_lit_def,sat_lit_def]
  >- (
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >- (
      rw[set_bit_def,set_char_def]>>
      intLib.ARITH_TAC)>>
    fs[isat_strxor_def]>>
    DEP_REWRITE_TAC[string_to_bits_set_bit,sum_bitlist_LUPDATE]>>
    fs[get_bit_string_to_bits,of_bool_def]>>
    DEP_REWRITE_TAC [EVEN_SUB]>>
    simp[sum_bitlist_alt]>>
    match_mp_tac SUM_MEM_bound>>
    simp[MEM_MAPi]>>
    asm_exists_tac>>simp[of_bool_def])>>
  fs[isat_strxor_def]>>
  DEP_REWRITE_TAC[string_to_bits_set_bit,sum_bitlist_LUPDATE]>>
  fs[get_bit_string_to_bits,of_bool_def]>>
  `Num (ABS l) ≠ 0` by intLib.ARITH_TAC>>
  simp[of_bool_def]
QED

Theorem get_units_sound:
  ∀ls cs.
  isat_cfml w (range fml) ∧
  EVERY (λl. sat_lit w (interp_lit l)) cs ∧
  get_units fml ls cs = SOME cs' ⇒
  EVERY (λl. sat_lit w (interp_lit l)) cs'
Proof
  Induct>>rw[get_units_def]>>gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  first_x_assum (irule_at Any)>>
  gvs[isat_fml_gen_def,range_def,PULL_EXISTS]>>
  first_x_assum drule>>simp[isat_cclause_def]
QED

Theorem unit_props_xor_sound:
  ∀is X Y.
  tn_inv (t,n) ∧
  isat_cfml w (range fml) ∧
  unit_props_xor fml t is X = SOME Y ⇒
  (isat_strxor (w ∘ restore_fn (t,n)) X ⇔
    isat_strxor (w ∘ restore_fn (t,n)) Y)
Proof
  rw[unit_props_xor_def]>>
  gvs[AllCaseEqs()]>>
  drule get_units_sound>>
  disch_then (drule_at Any)>>
  simp[]>>
  pop_assum kall_tac>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  gvs[EVERY_SNOC,FOLDL_SNOC]>>
  match_mp_tac (GSYM unit_prop_xor_sound)>>
  gvs[]
QED

Theorem is_xor_sound:
  tn_inv tn ∧
  isat_xfml (w ∘ restore_fn tn) (range fml) ∧
  isat_cfml w (range cfml) ∧
  is_xor def fml is cfml cis (FST tn) X ⇒
  isat_strxor (w ∘ restore_fn tn) X
Proof
  rw[is_xor_def]>>
  every_case_tac>>fs[]>>
  drule add_xors_aux_acc>>
  disch_then (qspec_then `strxor (extend_s «» def) X` assume_tac)>>
  drule add_xors_aux_imp>>
  disch_then (drule_at Any)>>
  impl_tac >-
    metis_tac[isat_strxor_is_emp_xor,strxor_self]>>
  `isat_strxor (w ∘ restore_fn tn) x` by
    (Cases_on`tn`>>fs[]>>
    drule_all unit_props_xor_sound>>
    metis_tac[isat_strxor_is_emp_xor])>>
  strip_tac>>
  `is_emp_xor (extend_s «» def)` by
    rw[extend_s_def,is_emp_xor_def]>>
  `isat_strxor (w ∘ restore_fn tn)
    (strxor (strxor x x) (strxor (extend_s «» def) X))` by
    (simp[strxor_assoc]>>
    match_mp_tac isat_strxor_strxor>>simp[])>>
  metis_tac[isat_stxor_add_is_emp_xor,strxor_comm,isat_strxor_extend_s,strxor_self]
QED

Theorem isat_cclause_restore_fn:
  EVERY (can_restore_int tn) mC ∧
  tn_inv tn ∧
  wf_clause (MAP (restore_int tn) mC) ∧
  isat_cclause (w ∘ restore_fn tn) mC ⇒
  isat_cclause w (MAP (restore_int tn) mC)
Proof
  rw[isat_cclause_def,MEM_MAP,PULL_EXISTS]>>
  `∃m. get_name tn m = (Num (ABS l),tn)` by
    (Cases_on`tn`>>
    fs[get_name_def,EVERY_MEM,can_restore_int_def]>>
    first_x_assum drule>>
    rw[can_restore_def]>>simp[]>>
    qexists_tac`k`>>simp[])>>
  drule_all tn_inv_get_name>>
  rw[]>>
  first_assum (irule_at Any)>>
  CONJ_ASM1_TAC
  >- (
    fs[wf_clause_def,EVERY_MEM,MEM_MAP]>>
    metis_tac[])>>
  fs[interp_lit_def,sat_lit_def,restore_int_def]>>rw[]>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Theorem sat_cmsxor_restore_fn_2:
  wf_clause (MAP (restore_int tn) mX) ∧
  sat_cmsxor w (MAP interp_lit (MAP (restore_int tn) mX)) ⇒
  sat_cmsxor (w ∘ restore_fn tn) (MAP interp_lit mX)
Proof
  rw[sat_cmsxor_restore_fn,MAP_MAP_o]>>
  qmatch_asmsub_abbrev_tac`_ w ls1`>>
  qmatch_goalsub_abbrev_tac`_ w ls2`>>
  qsuff_tac `ls1 = ls2`>>rw[]
  >- metis_tac[]>>
  unabbrev_all_tac>>
  simp[MAP_MAP_o,MAP_EQ_f]>>rw[]>>
  rw[interp_lit_def,restore_lit_def,restore_int_def]>>
  gvs[]
  >- intLib.ARITH_TAC>>
  `&restore_fn tn (Num (ABS e)) = 0` by
    (fs[]>>
    intLib.ARITH_TAC)>>
  fs[wf_clause_def,MEM_MAP]>>
  first_x_assum(qspec_then`e` mp_tac)>>
  simp[restore_int_def]
QED

Definition delete_ons_def:
  delete_ons n (off,ns) =
  if n < off then (off,ns)
  else
  let n = n - off in
  if n < length ns then
    (off,update ns n 0i)
  else
    (off,ns)
End

(* We'll reason about this *)
Definition prop_cardc_sem_def:
  (prop_cardc_sem ons k lb ub [] = (ons,k:int,lb:int,ub:int)) ∧
  (prop_cardc_sem ons k lb ub (l::ls) =
    let n = Num (ABS l) in
    let c = lookup_ons n ons in
    let ons' = delete_ons n ons in
    if c = 0 then
      prop_cardc_sem ons' k lb ub ls
    else
      let k' = if l > 0 then k else k - c in
      if c > 0 then
        prop_cardc_sem ons' k' lb (ub - c) ls
      else
        prop_cardc_sem ons' k' (lb - c) ub ls)
End

Theorem lookup_ons_delete_ons:
  lookup_ons n (delete_ons n' t) =
  if n = n' then 0
  else lookup_ons n t
Proof
  Cases_on`t`>>Cases_on`r`>>
  rw[lookup_ons_def,delete_ons_def]>>
  gvs[update_def,length_def,toList_thm,sub_def]>>
  rw[EL_LUPDATE]
QED

Theorem prop_cardc_sem_eq_aux:
  ∀ls ons k lb ub.
  ALL_DISTINCT (MAP (λl. Num (ABS l)) ls) ∧
  (∀n.
    MEM n (MAP (λl. Num (ABS l)) ls) ⇒
    lookup_ons n ons = lookup_ons n ons') ⇒
  SND (prop_cardc_sem ons k lb ub ls) =
  prop_cardc ons' k lb ub ls
Proof
  Induct>>rw[prop_cardc_sem_def,prop_cardc_def]>>
  first_x_assum irule>>
  rw[lookup_ons_delete_ons]
QED

Theorem prop_cardc_sem_eq:
  ALL_DISTINCT (MAP (λl. Num (ABS l)) ls) ⇒
  prop_cardc ons k lb ub ls =
  SND (prop_cardc_sem ons k lb ub ls)
Proof
  metis_tac[prop_cardc_sem_eq_aux]
QED

(*
Theorem iSUM_le:
  (∀x. MEM x ls ⇒ f x ≤ g x)
  ⇒
  iSUM (MAP f ls) ≤ iSUM (MAP g ls)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>
  gvs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem toAList_delete_PERM:
  lookup n t = SOME v ⇒
  PERM (toAList t) ((n,v)::toAList (delete n t))
Proof
  rw[]>>
  irule PERM_ALL_DISTINCT>>
  rw[]
  >- (
    Cases_on`x`>>
    rw[MEM_toAList,lookup_delete]>>
    metis_tac[SOME_11])
  >-
    metis_tac[ALL_DISTINCT_MAP,ALL_DISTINCT_MAP_FST_toAList]
  >-
    simp[MEM_toAList,lookup_delete]
  >-
    metis_tac[ALL_DISTINCT_MAP,ALL_DISTINCT_MAP_FST_toAList]
QED

Theorem iSUM_PERM:
  ∀xs ys.
  PERM xs ys ⇒
  iSUM xs = iSUM ys
Proof
  ho_match_mp_tac PERM_IND>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_as_list_delete_offspt:
  lookup_offspt n ons = SOME c ⇒
  iSUM (MAP f (as_list ons)) =
  iSUM (MAP f (as_list (delete_offspt n ons))) +
  f (n,c)
Proof
  Cases_on`ons`>>
  rw[lookup_offspt_def,as_list_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,delete_offspt_def]>>
  drule toAList_delete_PERM>>
  rw[]>>
  qmatch_goalsub_abbrev_tac`iSUM (MAP ff _)`>>
  drule (PERM_MAP |> INST_TYPE [beta |-> ``:int``])>>
  disch_then (qspec_then `ff` assume_tac)>>
  drule iSUM_PERM>>
  rw[iSUM_def,Abbr`ff`]>>
  intLib.ARITH_TAC
QED
*)

Theorem prop_cardc_sem_isat_cardc:
  ∀ls ons k lb ub.
  prop_cardc_sem ons k lb ub ls = (ons',k',lb',ub') ∧
  (∀l. MEM l ls ⇒ ¬sat_lit w (interp_lit l)) ⇒
  (isat_cardc w (ons,k,lb,ub) ⇔
  isat_cardc w (ons',k',lb',ub'))
Proof
  cheat
  (*
  Induct>>rw[prop_cardc_sem_def]>>
  gvs[AllCaseEqs(),SF DNF_ss]>>
  first_x_assum drule>>
  disch_then (fn th => simp[GSYM th])>>
  gvs[isat_cardc_def]>>rw[]
  >- (
    qmatch_goalsub_abbrev_tac`iSUM (MAP ff _)`>>
    drule (iSUM_as_list_delete_offspt |> INST_TYPE [beta |-> ``:int``])>>
    disch_then(qspec_then`ff` SUBST_ALL_TAC)>>
    gvs[Abbr`ff`,sat_lit_def,interp_lit_def]>>
    intLib.ARITH_TAC)>>
  qmatch_goalsub_abbrev_tac`iSUM (MAP ff _)`>>
  drule (iSUM_as_list_delete_offspt |> INST_TYPE [beta |-> ``:int``])>>
  disch_then(qspec_then`ff` SUBST_ALL_TAC)>>
  gvs[Abbr`ff`,sat_lit_def,interp_lit_def]>>
  intLib.ARITH_TAC *)
QED

Theorem prop_cardc_sem_wf_cardc:
  ∀ls ons k lb ub.
  prop_cardc_sem ons k lb ub ls = (ons',k',lb',ub') ∧
  wf_cardc (ons,k,lb,ub) ⇒
  wf_cardc (ons',k',lb',ub')
Proof
  cheat
  (*
  Induct>>rw[prop_cardc_sem_def]
  >-
    metis_tac[]>>
  gvs[AllCaseEqs(),SF DNF_ss]
  >-
    metis_tac[]>>
  first_x_assum irule>>
  last_x_assum (irule_at Any)>>
  gvs[wf_cardc_def]>>rw[]>>
  qmatch_goalsub_abbrev_tac`iSUM (MAP ff _)`>>
  drule (iSUM_as_list_delete_offspt |> INST_TYPE [beta |-> ``:int``])>>
  disch_then(qspec_then`ff` SUBST_ALL_TAC)>>
  gvs[Abbr`ff`,sat_lit_def,interp_lit_def]>>
  intLib.ARITH_TAC *)
QED

Theorem prop_lit_sat_lit:
  prop_lit n ls = SOME b ∧
  (∀l. MEM l ls ⇒ ¬sat_lit w (interp_lit l)) ⇒
  w n = b
Proof
  Induct_on`ls`>>rw[prop_lit_def]>>
  gvs[SF DNF_ss,sat_lit_def,interp_lit_def,AllCaseEqs(),AllCasePreds()]>>
  intLib.ARITH_TAC
QED

Theorem wf_cardc_ub:
  wf_cardc (x,k,lb,ub) ∧
  ub < k ⇒
  ¬isat_cardc w (x,k,lb,ub)
Proof
  rw[isat_cardc_def,wf_cardc_def]>>
  cheat
  (*
  qmatch_asmsub_abbrev_tac `iSUM (MAP f1 _) ≤ ub`>>
  qmatch_goalsub_abbrev_tac `iSUM (MAP f2 _)`>>
  CCONTR_TAC>>gvs[]>>
  `iSUM (MAP f2 (as_list x)) ≤ iSUM (MAP f1 (as_list x))` by
    (match_mp_tac iSUM_le>>
    rw[Abbr`f1`,Abbr`f2`]>>
    pairarg_tac>>rw[]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC *)
QED

Theorem wf_cardc_lb:
  wf_cardc (x,k,lb,ub) ∧
  k ≤ lb ⇒
  isat_cardc w (x,k,lb,ub)
Proof
  rw[isat_cardc_def,wf_cardc_def]>>
  cheat
  (*qmatch_asmsub_abbrev_tac `lb ≤ iSUM (MAP f1 _)`>>
  qmatch_goalsub_abbrev_tac `iSUM (MAP f2 _)`>>
  CCONTR_TAC>>gvs[]>>
  `iSUM (MAP f1 (as_list x)) ≤ iSUM (MAP f2 (as_list x))` by
    (match_mp_tac iSUM_le>>
    rw[Abbr`f1`,Abbr`f2`]>>
    pairarg_tac>>rw[]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC *)
QED

Theorem check_ibnn_sound:
  check_ibnn bnn ls ∧
  wf_ibnn bnn ∧
  ALL_DISTINCT (MAP (λl. Num (ABS l)) ls) ∧
  (∀l. MEM l ls ⇒ ¬sat_lit w (interp_lit l))
  ⇒
  ¬isat_ibnn w bnn
Proof
  PairCases_on`bnn`>>
  rw[check_ibnn_def]>>
  gvs[AllCasePreds(),wf_ibnn_def]>>
  drule_all prop_lit_sat_lit>>
  strip_tac>>CCONTR_TAC>>gvs[isat_ibnn_def]>>
  drule prop_cardc_sem_eq>>
  strip_tac>>gvs[]>>
  pairarg_tac>>gvs[SND_EQ_EQUIV]
  >- (
    drule_at Any prop_cardc_sem_isat_cardc>>
    disch_then drule>> gvs[]>>
    drule_all prop_cardc_sem_wf_cardc>>strip_tac>>
    rw[sat_lit_def,interp_lit_def]>>
    irule wf_cardc_ub>>
    gvs[])
  >- (
    drule_at Any prop_cardc_sem_isat_cardc>>
    disch_then drule>>
    disch_then (fn th => gvs[th])>>
    `¬sat_lit w (interp_lit bnn5)` by
      (rw[sat_lit_def,interp_lit_def]>>gvs[])>>
    gvs[]>>
    drule_all prop_cardc_sem_wf_cardc>>strip_tac>>
    drule wf_cardc_lb>>
    metis_tac[])
QED

(*
Theorem is_rup2_sound:
  ∀is C.
  wf_clause C ∧
  is_rup2 fml is C = SOME D ∧
  isat_cfml w (range fml) ∧
  ¬ isat_cclause w C ∧
  MEM l D ⇒
  ¬sat_lit w (interp_lit l)
Proof
  Induct>>fs[is_rup2_def]>>rw[]
  >- (
    gvs[isat_cclause_def,wf_clause_def]>>
    metis_tac[])>>
  gvs[AllCaseEqs()]>>
  rename1`delete_literals x C`>>
  first_x_assum irule>>
  first_x_assum (irule_at (Pos last))>>
  rw[]
  >-
    gvs[wf_clause_def]>>
  fs[isat_fml_gen_def,PULL_EXISTS,range_def]>>
  first_x_assum drule>>
  gvs[isat_cclause_cons]>>
  `set x DIFF set C =
   set (delete_literals x C)` by
   metis_tac[set_delete_literals]>>
  gvs[isat_cclause_def]>>rw[]>>
  gvs[EXTENSION]>>
  metis_tac[sat_lit_interp_lit_neg]
QED

Theorem is_rup2_wf:
  ∀i0 C.
  is_rup2 cfml i0 C = SOME ls ∧
  ALL_DISTINCT (MAP (λl. Num (ABS l)) C) ⇒
  ALL_DISTINCT (MAP (λl. Num (ABS l)) ls)
Proof
  Induct>>rw[is_rup2_def]>>gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  first_x_assum (irule_at (Pos last))>>
  gvs[]
QED
*)
Theorem get_units_wf:
  ∀i0 cs.
  wf_cfml cfml ∧
  get_units cfml i0 cs = SOME cs' ∧
  wf_clause cs ⇒
  wf_clause cs'
Proof
  Induct>>rw[get_units_def]>>gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  first_x_assum (irule_at (Pos last))>>
  gvs[wf_clause_def,wf_cfml_def,range_def,PULL_EXISTS]>>
  first_x_assum drule>>
  simp[]
QED

Theorem mk_strict_aux_SORTED:
  ∀ls x acc.
  SORTED (\x y. x ≥ y) (x::ls) ∧
  SORTED $< (x::acc) ⇒
  SORTED $< (mk_strict_aux x ls acc)
Proof
  Induct>>rw[mk_strict_aux_def]>>
  first_x_assum irule>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem mk_strict_SORTED:
  SORTED $< (mk_strict ls)
Proof
  rw[mk_strict_def]>>
  every_case_tac>>gvs[]>>
  irule mk_strict_aux_SORTED>>
  gvs[]>>
  pop_assum sym_sub_tac>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  CONJ_ASM1_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC)>>
  irule mergesort_sorted >>
  simp[]
QED

Theorem mk_strict_aux_MEM:
  ∀ls y acc.
  MEM x (mk_strict_aux y ls acc) ⇔
  x = y ∨ MEM x ls ∨ MEM x acc
Proof
  Induct>>rw[mk_strict_aux_def]>>
  metis_tac[]
QED

Theorem mk_strict_MEM:
  MEM x (mk_strict ls) ⇔ MEM x ls
Proof
  rw[mk_strict_def]>>
  every_case_tac>>gvs[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  (CONJ_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC))
  >- metis_tac[mergesort_mem,MEM]>>
  simp[mk_strict_aux_MEM]>>
  metis_tac[mergesort_mem,MEM]
QED

Theorem not_sat_lit_inj:
  ¬ sat_lit w (interp_lit x) ∧
  ¬ sat_lit w (interp_lit y) ∧
  Num (ABS x) = Num (ABS y) ⇒
  x = y
Proof
  simp[interp_lit_def,sat_lit_def,AllCasePreds()]>>
  rw[]>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem is_cfromb_sound:
  wf_clause C ∧
  wf_cfml cfml ∧
  (∀b. b ∈ range bfml ⇒ wf_ibnn b) ∧
  isat_cfml w (range cfml) ∧
  isat_bfml w (range bfml) ∧
  is_cfromb C cfml bfml ib i0  ⇒
  isat_cclause w C
Proof
  rw[is_cfromb_def]>>
  gvs[AllCasePreds()]>>
  CCONTR_TAC>>
  drule get_units_sound>>
  disch_then (drule_at Any)>>
  strip_tac>>gvs[]>>
  qmatch_asmsub_abbrev_tac`check_ibnn bnn ls`>>
  `SORTED $< ls` by (
    gvs[Abbr`ls`]>>
    metis_tac[mk_strict_SORTED])>>
  `ALL_DISTINCT ls` by (
    irule SORTED_ALL_DISTINCT>>
    first_x_assum (irule_at Any)>>
    simp[irreflexive_def,transitive_def]>>
    intLib.ARITH_TAC)>>
  drule check_ibnn_sound>>
  disch_then(qspec_then`w` mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      gvs[range_def]>>
      metis_tac[])>>
    CONJ_ASM2_TAC >- (
      CCONTR_TAC>>
      gvs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
      rename1`_ ⇎ n1 = n2`>>
      Cases_on`n1 = n2`>>gvs[]>>
      gvs[MEM_EL,PULL_EXISTS]>>
      metis_tac[not_sat_lit_inj])>>
    gvs[MAP_MAP_o,o_DEF,Abbr`ls`,mk_strict_MEM]>>
    gvs[isat_cclause_def,wf_clause_def,EVERY_MEM,MEM_MAP]>>
    rw[]
    >- (
      DEP_REWRITE_TAC[sat_lit_interp_lit_neg]>>
      drule get_units_wf>>
      disch_then drule>>
      simp[wf_clause_def]>>
      metis_tac[])>>
    metis_tac[])>>
  gvs[isat_fml_gen_def,range_def]>>
  metis_tac[]
QED

(* TODO BROKEN BELOW *)
Triviality foldi_cons_lemma:
  ∀t acc k. foldi (λk v a. f v::a) k acc t =
            foldi (λk v a. f v::a) k [] t ++ acc
Proof
  Induct
  \\ rewrite_tac [foldi_def,APPEND]
  \\ rpt (pop_assum (fn th => once_rewrite_tac [th]))
  \\ simp []
QED

Theorem iSUM_append:
  ∀xs ys. iSUM (xs ++ ys) = iSUM xs + iSUM ys
Proof
  Induct \\ gvs [iSUM_def,AC integerTheory.INT_ADD_ASSOC integerTheory.INT_ADD_COMM]
QED

Theorem iSUM_MAP_toAList_EQ_MAP_toList:
  iSUM (MAP (λ(x,y). f y) (toAList t)) = iSUM (MAP f (toList t))
Proof
  gvs [toAList_def]
  \\ gvs [sptreeTheory.MAP_foldi,toList_def]
  \\ qsuff_tac ‘∀t l. iSUM (foldi (λk v a. f v::a) l [] t) = iSUM (MAP f (toList t))’
  >- metis_tac [toList_def]
  \\ Induct
  \\ gvs [foldi_def,toList_def,toListA_def]
  \\ once_rewrite_tac [foldi_cons_lemma]
  \\ once_rewrite_tac [sptreeTheory.toListA_append]
  \\ gvs [iSUM_append,iSUM_def]
  \\ gvs [AC integerTheory.INT_ADD_ASSOC integerTheory.INT_ADD_COMM]
QED

Theorem lb_ub_spt_thm:
  lb_ub_spt s = (iSUM (MAP (λp2. if p2 < 0 then p2 else 0) (toList s)),
                 iSUM (MAP (λp2. if p2 > 0 then p2 else 0) (toList s)))
Proof
  Induct_on ‘s’
  \\ gvs [lb_ub_spt_def,EVAL “toList LN”,iSUM_def,toList_def,toListA_def]
  \\ rw [] \\ once_rewrite_tac [sptreeTheory.toListA_append]
  \\ gvs [GSYM toListA_def,iSUM_append]
  \\ gvs [lb_ub_spt_def,EVAL “toList LN”,iSUM_def,toList_def,toListA_def]
  \\ rw [] \\ intLib.COOPER_TAC
QED

Theorem conv_bnn_sound:
  nz_lit y ∧ EVERY nz_lit C ⇒
  wf_ibnn (conv_bnn (C,k,y)) ∧
  (isat_ibnn w (conv_bnn (C,k,y)) ⇔ sat_cmsbnn w (C,k,y))
Proof
  Cases_on ‘C’ \\ gvs [conv_bnn_def,wf_ibnn_def,wf_cardc_def]
  >- (* C is [] *)
   (gvs [sat_cmsbnn_def,isat_ibnn_def,interp_lit_conv_lit]
    \\ gvs [isat_cardc_def,as_list_def,EVAL “toAList LN”,EVAL “iSUM []”]
    \\ Cases_on ‘k’ \\ gvs [])
  \\ rpt (pairarg_tac \\ gvs [wf_ibnn_def])
  \\ strip_tac
  \\ gvs [sat_cmsbnn_def,isat_ibnn_def,interp_lit_conv_lit]
  \\ irule_at Any (METIS_PROVE [] “x = y ⇒ (x = b ⇔ b = y)”)
  \\ gvs [wf_cardc_def]
  \\ gvs [isat_cardc_def]
  \\ gvs [as_list_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,iSUM_MAP_toAList_EQ_MAP_toList]
  \\ qabbrev_tac ‘s = to_spt (h::t) min' LN’
  \\ gvs [lb_ub_spt_thm]
  \\ cheat
QED

Theorem check_xlrup_sound:
  wf_xlrup xlrup ∧
  wf_cfml cfml ∧
  check_xlrup xorig xlrup cfml xfml bfml tn def =
    SOME (cfml',xfml',bfml',tn',def') ∧ tn_inv tn ∧
  (∀x. MEM x xorig ⇒ sat_cmsxor w x) ∧
  (∀s. s ∈ range xfml ⇒ can_restore_str tn s) ∧
  (∀b. b ∈ range bfml ⇒ wf_ibnn b) ∧
  isat_fml w (restore_fn tn) (range cfml, range xfml, range bfml)
  ⇒
  (∀s. s ∈ range xfml' ⇒ can_restore_str tn' s) ∧
  (∀b. b ∈ range bfml' ⇒ wf_ibnn b) ∧
  isat_fml w (restore_fn tn') (range cfml', range xfml', range bfml')
Proof
  simp[check_xlrup_def]>>strip_tac>>
  gvs[AllCaseEqs()]
  >~ [‘Del’] >- (* deleting clauses by ID *)
    metis_tac[delete_clauses_sound]
  >~ [‘RUP’] >- (
    fs[isat_fml_def]>>
    match_mp_tac isat_fml_gen_insert>>
    simp[]>>
    match_mp_tac (GEN_ALL is_rup_sound)>>gvs[]>>
    asm_exists_tac>>simp[])
  >~ [‘XOrig’] >- (
    pairarg_tac \\ gvs [] \\ res_tac >>
    drule_all ren_lit_ls_restore>> strip_tac>> gvs[]>>
    fs[isat_fml_def,PULL_EXISTS]>>
    conj_tac >- (
      fs[range_def,PULL_EXISTS,lookup_insert]>>
      rw []
      >- (
        match_mp_tac can_restore_str_conv_xor_mv
        \\ metis_tac [can_restore_str_submap])
      \\ metis_tac [can_restore_str_submap])>>
    match_mp_tac isat_fml_gen_insert>>
    CONJ_TAC >-
      metis_tac[isat_xfml_restore_str_submap]>>
    fs[wf_xlrup_def] >>
    rw[conv_xor_mv_def,conv_rawxor_def, GSYM conv_xor_def]>>
    DEP_REWRITE_TAC [conv_xor_sound, isat_strxor_flip_bit] >>
    simp[isat_strxor_extend_s]>>
    drule ren_lit_ls_nz_lit \\ rw []
    >- (EVAL_TAC \\ simp [MAX_DEF]) >>
    simp [isat_strxor_def,string_to_bits_def,sum_bitlist_def,
          sat_cmsxor_restore_fn] >>
    drule_all ren_lit_ls_restore >>
    strip_tac \\ fs [])
  >~ [‘XAdd’] >- (
    pairarg_tac>>gvs[]>>
    fs[isat_fml_def]>>
    drule ren_int_ls_restore >> strip_tac>> gvs[]>>
    CONJ_TAC>- (
      simp[range_def,PULL_EXISTS,lookup_insert]>>
      rw[]
      >- (
        match_mp_tac can_restore_str_conv_rawxor>>
        fs[o_DEF,EVERY_MAP,GSYM can_restore_int_def]>>
        metis_tac[ETA_AX])>>
      fs[range_def]
      \\ metis_tac [can_restore_str_submap])>>
    match_mp_tac isat_fml_gen_insert>>
    CONJ_TAC >-
      metis_tac[isat_xfml_restore_str_submap]>>
    match_mp_tac (GEN_ALL is_xor_sound)>>gvs[]>>
    drule ren_int_ls_tn_inv>>rw[]>>
    metis_tac[isat_xfml_restore_str_submap])
  >~ [‘XDel’] >- (
    CONJ_TAC >-
      metis_tac[range_FOLDL_delete_SUBSET,SUBSET_DEF]>>
    metis_tac[delete_xors_sound])
  >~ [‘CFromX ’] >- (
    fs[isat_fml_def]>>
    pairarg_tac>>gvs[]>>
    drule ren_int_ls_wf_clause>>
    fs[wf_xlrup_def]>>
    impl_tac >- simp[wf_clause_def]>>
    drule ren_int_ls_restore >> strip_tac>> gvs[]>>
    strip_tac>>
    CONJ_TAC >- (
      fs[range_def]
      \\ metis_tac [can_restore_str_submap])>>
    CONJ_ASM2_TAC >- (
      match_mp_tac isat_fml_gen_insert>>
      simp[]>>
      fs[wf_xlrup_def]>>
      drule_at (Pos last) (GEN_ALL is_cfromx_sound)>>
      disch_then (drule_at Any)>>
      simp[]>>
      strip_tac>>
      match_mp_tac isat_cclause_restore_fn>>
      fs[]>>
      metis_tac[ren_int_ls_tn_inv])>>
    metis_tac[isat_xfml_restore_str_submap])
  >~ [‘XFromC’] >- (
    fs[isat_fml_def]>>
    pairarg_tac>>gvs[]>>
    drule ren_int_ls_restore >> strip_tac>> gvs[]>>
    CONJ_TAC >- (
      simp[range_def,PULL_EXISTS,lookup_insert]>>
      rw[]
      >- (
        match_mp_tac can_restore_str_conv_rawxor>>
        fs[o_DEF,EVERY_MAP,GSYM can_restore_int_def]>>
        metis_tac[ETA_AX])>>
      fs[range_def]
      \\ metis_tac [can_restore_str_submap])>>
    match_mp_tac isat_fml_gen_insert>>
    CONJ_TAC >-
      metis_tac[isat_xfml_restore_str_submap]>>
    drule_at (Pos last) is_xfromc_sound >>
    fs[wf_xlrup_def]>>
    disch_then (drule_at Any)>>
    strip_tac>>
    rw[conv_rawxor_def]>>
    match_mp_tac isat_strxor_cnv_xor_to_aux>>
    DEP_REWRITE_TAC[conv_xor_sound]>>
    drule ren_int_ls_wf_clause>> simp[] >>
    impl_tac >- simp[wf_clause_def]>>
    rw[]
    >- (
      fs[wf_clause_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
      rw[var_lit_def,interp_lit_def]
      >- intLib.ARITH_TAC>>
      CCONTR_TAC>>
      fs[]>>
      `y = 0` by intLib.ARITH_TAC>>
      fs[])>>
    fs[sat_cmsxor_restore_fn_2]>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    simp[isat_strxor_extend_s]>>
    CONJ_TAC >-
      (EVAL_TAC>>rw[])>>
    EVAL_TAC)
  >~ [‘BDel’] >- (
    rw[]
    >-
      metis_tac[range_FOLDL_delete_SUBSET,SUBSET_DEF]>>
    metis_tac[delete_bnns_sound])
  >~ [‘CFromB ’] >- (
    fs[isat_fml_def]>>
    match_mp_tac isat_fml_gen_insert>>
    simp[]>>
    fs[wf_xlrup_def]>>
    metis_tac[is_cfromb_sound])
QED

Theorem check_xlrup_tn_inv:
  check_xlrup xorig xlrup cfml xfml bfml tn def =
    SOME (cfml',xfml',bfml',tn',def') ∧ tn_inv tn ⇒
  tn_inv tn'
Proof
  rw[check_xlrup_def]
  \\ gvs[AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  >- (drule ren_lit_ls_tn_inv \\ fs [])
  \\ drule ren_int_ls_tn_inv \\ fs []
QED

(* The main operational theorem about check_xlrups *)
Theorem check_xlrups_sound:
  ∀ls cfml xfml bfml def def' tn tn'.
  EVERY wf_xlrup ls ∧ wf_cfml cfml ∧ tn_inv tn ∧
  check_xlrups xorig ls cfml xfml bfml tn def =
    SOME (cfml', xfml', bfml', tn', def') ∧
  (∀s. s ∈ range xfml ⇒ can_restore_str tn s) ∧
  (∀b. b ∈ range bfml ⇒ wf_ibnn b) ∧
  (∀x. MEM x xorig ⇒ sat_cmsxor w x) ⇒
  (isat_fml w (restore_fn tn) (range cfml, range xfml, range bfml) ⇒
   isat_fml w (restore_fn tn') (range cfml', range xfml', range bfml'))
Proof
  Induct>>simp[check_xlrups_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  rw[]>>
  drule check_xlrup_sound>>
  disch_then drule>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]>>
  drule_all wf_cfml_check_xlrup>>
  drule_all check_xlrup_tn_inv>>
  metis_tac[]
QED

(* Build a sptree from a list *)
Definition build_fml_def:
  (build_fml (id:num) [] = LN) ∧
  (build_fml id (cl::cls) =
    insert id cl (build_fml (id+1) cls))
End

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml n ls) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls)
  else NONE
Proof
  Induct>>rw[build_fml_def,lookup_def,lookup_insert]>>
  `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem range_build_fml:
  ∀ls id. range (build_fml id ls) = set ls
Proof
  Induct>>fs[build_fml_def,range_def,lookup_def]>>
  fs[EXTENSION]>>
  rw[lookup_insert]>>
  rw[EQ_IMP_THM]
  >- (
    every_case_tac>>fs[]>>
    metis_tac[])
  >- metis_tac[] >>
  first_x_assum(qspecl_then[`id+1`,`x`] mp_tac)>>
  rw[]>>
  fs[lookup_build_fml]>>
  qexists_tac`n`>>simp[]
QED

(* Main theorem *)
Theorem check_xlrups_unsat_sound:
  EVERY wf_xlrup xlrups ∧
  EVERY wf_clause cfml ∧
  EVERY wf_ibnn bfml ∧
  check_xlrups_unsat xfml xlrups
    (build_fml cid cfml) LN (build_fml bid bfml) (LN,1) def ⇒
  ¬ ∃w.
    isat_cfml w (set cfml) ∧
    (∀x. MEM x xfml ⇒ sat_cmsxor w x) ∧
    isat_bfml w (set bfml)
Proof
  rw[check_xlrups_unsat_def]>>
  every_case_tac>>fs[]>>
  `¬∃w. isat_cfml w (range q)` by (
    fs[isat_fml_gen_def,contains_emp_def,MEM_MAP]>>
    Cases_on`y`>>fs[MEM_toAList,range_def,PULL_EXISTS]>>
    rw[]>>
    asm_exists_tac>>simp[isat_cclause_def])>>
  fs[]>>
  PairCases_on`r`>>drule check_xlrups_sound>>
  disch_then (drule_at Any)>>
  ‘tn_inv (LN,1)’ by fs [tn_inv_def]>>
  fs[isat_fml_def,range_build_fml,EVERY_MEM,wf_cfml_def]>>
  simp[range_def,isat_fml_gen_def]>>
  metis_tac[]
QED

Definition max_var_xor_def:
  max_var_xor xfml =
  max_list 0 (MAP (λls. max_list 0 (MAP var_lit ls)) xfml)
End

Definition conv_xfml_def:
  conv_xfml mv xfml =
  let s = extend_s (strlit "") (MAX 1 mv) in
  let s = flip_bit s 0 in
  MAP (conv_xor s) xfml
End

Theorem conv_xor_base:
  EVERY nz_lit ls ⇒
 (isat_strxor w (conv_xor (flip_bit (extend_s (strlit "") (MAX 1 n)) 0) ls) ⇔
  sat_cmsxor w ls)
Proof
  rw[conv_xor_sound,isat_strxor_extend_s]>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[isat_strxor_extend_s]>>
  EVAL_TAC>>rw[]
QED

Theorem conv_xfml_sound:
  EVERY (EVERY nz_lit) xfml ⇒
  (isat_xfml w (set (conv_xfml mv xfml)) ⇔
  (∀C. C ∈ set xfml ⇒ sat_cmsxor w C))
Proof
  rw[isat_fml_gen_def,conv_xfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  simp[GSYM EVERY_MEM]>>
  match_mp_tac EVERY_CONG>>rw[]>>
  match_mp_tac conv_xor_base>>
  gvs[EVERY_MEM]>>
  metis_tac[]
QED

Definition conv_bfml_def:
  conv_bfml bfml =
  MAP (conv_bnn) bfml
End

Definition conv_fml_def:
  conv_fml mv (cfml,xfml,bfml) =
  (conv_cfml cfml, conv_xfml xfml, conv_bfml bfml)
End

(* 1-sided variant of strxor *)
Definition strxor_aux_1_def:
  (strxor_aux_1 cs [] = cs) ∧
  (strxor_aux_1 cs (d::ds) =
    case cs of [] => []
    | (c::cs) => (c ⊕ toByte d) :: strxor_aux_1 cs ds)
End

Theorem strxor_aux_1_strxor_aux:
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
  TOP_CASE_TAC>>fs[]>>
  simp[LUPDATE_def]
QED

Definition strxor_aux_c_def:
  strxor_aux_c cs ds n =
  if n = 0 then cs
  else
    let n1 = n - 1 in
    let c = EL n1 cs in
    let d = toByte (strsub ds n1) in
    strxor_aux_c (LUPDATE (c ⊕ d) n1 cs) ds n1
End

Theorem strxor_aux_c_strxor_aux_1:
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

Theorem strxor_aux_c_strxor_aux:
  strxor_c s t =
  MAP toByte (explode (strxor (implode (MAP fromByte s)) t))
Proof
  rw[strxor_c_def,strxor_compute,extend_s_def]>>fs[]
  >- (
    DEP_REWRITE_TAC[strxor_aux_c_strxor_aux_1,strxor_aux_1_strxor_aux]>>
    simp[]>>
    Cases_on`t`>>simp[])>>
  DEP_REWRITE_TAC[strxor_aux_c_strxor_aux_1,strxor_aux_1_strxor_aux]>>
  simp[]>>
  simp[fromByte_def]>>
  Cases_on`t`>>simp[]
QED

Definition add_xors_aux_c_def:
  (add_xors_aux_c fml [] s = SOME s) ∧
  (add_xors_aux_c fml (i::is) s =
  case lookup i fml of NONE => NONE
  | SOME x =>
    add_xors_aux_c fml is (strxor_c s x))
End

(* This is an equivalence ... *)
Theorem add_xors_aux_c_add_xors_aux:
  ∀is s t.
  add_xors_aux_c fml is s = SOME t ⇒
  add_xors_aux fml is
    (implode (MAP fromByte s)) = SOME (implode (MAP fromByte t))
Proof
  Induct>>rw[add_xors_aux_c_def,add_xors_aux_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[strxor_aux_c_strxor_aux,MAP_MAP_o,o_DEF]
QED

val _ = export_theory ();
