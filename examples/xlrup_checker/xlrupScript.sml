(*
   Basic specification of an xlrup checker (minimal optimization)
*)
open preamble miscTheory mlstringTheory cnf_xorTheory blastLib;

val _ = new_theory "xlrup";

(*
TODO list:
1) define the "string" semantics of XORs (supporting overflow bits)
2) define an XOR/add operation on strings (binary version)
2.5) binary addition that is only correct when first string is shorter than second string
3) define the XOR proof step (adds multiple XORs and tests for zero)
4) prove soundness of 3)
5) turn "int list" XOR into string XOR and verify correctness
*)

(* Internal representations *)
Type cclause = ``:int list``;
Type strxor = ``:mlstring``;

Definition values_def:
  values s = {v | ∃n. lookup n s = SOME v}
End

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

Definition isat_cfml_def:
  isat_cfml w cfml ⇔ (∀C. C ∈ cfml ⇒ isat_cclause w C)
End

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
  isat_strxor (w:num assignment) x =
    EVEN (sum_bitlist w (string_to_bits x))
End

Definition isat_xfml_def:
  isat_xfml w xfml ⇔ (∀C. C ∈ xfml ⇒ isat_strxor w C)
End

Definition isat_fml_def:
  isat_fml w (cfml,xfml) ⇔
  isat_cfml w cfml ∧ isat_xfml w xfml
End

Definition isatisfiable_def:
  isatisfiable fml ⇔
  ∃w. isat_fml w fml
End

(* Connection to the top-level semantics *)
Definition conv_lit_def:
  (conv_lit (Pos n) = (&n):int) ∧
  (conv_lit (Neg n) = -(&n):int)
End

Definition conv_cfml_def:
  conv_cfml cfml = MAP (MAP conv_lit) cfml
End

Definition nz_lit_def[simp]:
  (nz_lit (Pos n) <=> n ≠ (0:num)) ∧
  (nz_lit (Neg n) <=> n ≠ 0)
End

Theorem interp_lit_conv_lit:
  nz_lit y ⇒
  interp_lit (conv_lit y) = y
Proof
  Cases_on`y`>>rw[conv_lit_def,interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem nz_lit_conv_lit:
  nz_lit y ⇒ conv_lit y ≠ 0
Proof
  Cases_on`y`>>rw[conv_lit_def]
QED

Theorem issat_cclause_MAP_conv_lit:
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
  rw[isat_cfml_def,conv_cfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  metis_tac[issat_cclause_MAP_conv_lit,EVERY_MEM]
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
  >-
    cheat>>
  rw[]>>
  cheat
QED

Definition flip_bit_def:
  flip_bit s v =
  set_bit s v (¬ get_bit s v)
End

Definition extend_s_def:
  extend_s s n =
  let q = n DIV 8 in
  if q < strlen s then s
  else s ^ (implode (REPLICATE (q + 1 - strlen s) (CHR 0)))
End

Definition conv_xor_aux_def:
  (conv_xor_aux s [] = s) ∧
  (conv_xor_aux s (x::xs) =
  case x of
    Pos v =>
      conv_xor_aux (flip_bit (extend_s s v) v) xs
  | Neg v =>
      conv_xor_aux (flip_bit (flip_bit (extend_s s v) v) 0) xs)
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
  EVEN (sum_bitlist_aux w (MAP (λ(x,y). x ⇎ y) (ZIP (xs,ys))) k) =
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
  EVEN (sum_bitlist w (MAP (λ(x,y). x ⇎ y) (ZIP (xs,ys))))
Proof
  rw[sum_bitlist_def]>>fs[]>>
  Cases_on`xs`>>Cases_on`ys`>>fs[]>>
  fs[EVEN_ADD,sum_bitlist_aux_xor,sum_bitlist_aux_cons]>>
  metis_tac[]
QED

(* TODO: define an XOR function on strings,
  probably padding them to the same length *)
Definition strxor_def:
  strxor (s:strxor) (t:strxor) = (ARB:strxor)
End

(* TODO: this is wrong, zero extension
  needs to pad on the right instead *)
Theorem strxor_prop:
  string_to_bits (strxor s t) =
  bxor (string_to_bits s) (string_to_bits t)
Proof
  cheat
QED

Theorem isat_strxor_strxor:
  isat_strxor w s ∧
  isat_strxor w t ==>
  isat_strxor w (strxor s t)
Proof
  rw[isat_strxor_def,strxor_prop]>>
  fs[bitstringTheory.bxor_def,bitstringTheory.bitwise_def]>>
  match_mp_tac sum_bitlist_xor>>
  fs[]>>
  cheat
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
  string_to_bits s ++ REPLICATE (8 * (n DIV 8 + 1 − strlen s)) F
Proof
  rw[extend_s_def,string_to_bits_def]>>
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

Theorem strlen_extend_s:
  a < 8 * strlen (extend_s s a)
Proof
  simp[extend_s_def]>>
  DEP_REWRITE_TAC[DIV_LT_X] >> simp[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem strlen_flip_bit[simp]:
  strlen (flip_bit s n) = strlen s
Proof
  rw[flip_bit_def,set_bit_def,set_char_def]
QED

Theorem conv_xor_aux_sound:
  ∀ls s.
  EVERY nz_lit ls ⇒
  (isat_strxor w (conv_xor_aux s ls) ⇔
  ((isat_strxor w s) ⇎ (sat_cmsxor w ls)))
Proof
  Induct>>rw[conv_xor_aux_def]
  >-
    simp[sat_cmsxor_def]>>
  TOP_CASE_TAC>>fs[]
  >- (
    simp[sat_lit_def]>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >-
      simp[strlen_extend_s]>>
    simp[isat_strxor_extend_s]>>
    metis_tac[]) >>
  simp[sat_lit_def]>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[strlen_extend_s,isat_strxor_extend_s]>>
  CONJ_TAC >- (
    assume_tac strlen_extend_s>>
    fs[])>>
  metis_tac[]
QED

Theorem sum_bitlist_first_bit:
  EVEN (sum_bitlist w (b::REPLICATE n F)) = ¬ b
Proof
  rw[sum_bitlist_def,sum_bitlist_aux_REPLICATE_F]
QED

(* Implementation *)
Datatype:
  xlrup =
  | Del (num list) (* Clauses to delete *)
  | RUP num cclause (num list)
    (* RUP n C hints : derive clause C by RUP using hints *)
  | XAdd num strxor (num list)
    (* Xadd n C hints derive XOR C by adding XORs using hints *)
  | XDel (num list) (* XORs to delete *)
  | CFromX num cclause (num list)
    (* Derive clause from hint XORs *)
  | XFromC num strxor (num list)
    (* Derive XOR from hint clauses *)
End

val delete_literals_def = Define`
  delete_literals (C:cclause) (D:cclause) =
  FILTER (λx. ¬MEM x D) C`

(*
  Checking for RUP
*)
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

Definition check_xlrup_def:
  check_xlrup xlrup cfml xfml =
  case xlrup of
    Del cl => SOME (FOLDL (\a b. delete b a) cfml cl, xfml)
  | RUP n C i0 =>
    if is_rup cfml i0 C then
      SOME (insert n C cfml, xfml)
    else NONE
  | XDel xl => SOME (cfml, FOLDL (\a b. delete b a) xfml xl)
  | _ => NONE
End

Definition check_xlrups_def:
  (check_xlrups [] cfml xfml = SOME (cfml,xfml)) ∧
  (check_xlrups (x::xs) cfml xfml =
  case check_xlrup x cfml xfml of
    NONE => NONE
  | SOME (cfml',xfml') => check_xlrups xs cfml' xfml')
End

Definition contains_emp_def:
  contains_emp fml =
  let ls = MAP SND (toAList fml) in
  MEM [] ls
End

Definition check_xlrups_unsat_def:
  check_xlrups_unsat xlrups cfml xfml =
  case check_xlrups xlrups cfml xfml of
    NONE => F
  | SOME (cfml',xfml') => contains_emp cfml'
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
  isat_cfml w (values fml) ⇒
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
    fs[isat_cfml_def,PULL_EXISTS,values_def]>>
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
    fs[isat_cfml_def,PULL_EXISTS,values_def]>>
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

Theorem delete_preserves_isat_cfml:
  isat_cfml w (values C) ⇒
  isat_cfml w (values (delete n C))
Proof
  rw[isat_cfml_def]>>
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem delete_preserves_isat_xfml:
  isat_xfml w (values x) ⇒
  isat_xfml w (values (delete n x))
Proof
  rw[isat_xfml_def]>>
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem delete_clauses_sound:
  ∀l fml.
  isat_fml w (values fml,x) ⇒
  isat_fml w (values (FOLDL (λa b. delete b a) fml l),x)
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_cfml,isat_fml_def]
QED

Theorem delete_xors_sound:
  ∀l x.
  isat_fml w (fml,values x) ⇒
  isat_fml w (fml, values (FOLDL (λa b. delete b a) x l))
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_xfml,isat_fml_def]
QED

Theorem isat_cfml_insert:
  isat_cfml w (values cfml) ∧
  isat_cclause w c ⇒
  isat_cfml w (values (insert n c cfml))
Proof
  rw[isat_cfml_def,values_def,lookup_insert]>>
  gvs[AllCaseEqs()]>>
  metis_tac[]
QED

Theorem check_xlrup_sound:
  check_xlrup xlrup cfml xfml = SOME (cfml',xfml') ∧
  isat_fml w (values cfml, values xfml) ⇒
  isat_fml w (values cfml', values xfml')
Proof
  rw[check_xlrup_def]>>
  gvs[AllCaseEqs()]
  >- (* deleting clauses by ID *)
    metis_tac[delete_clauses_sound]
  >- ( (* RUP *)
    fs[isat_fml_def]>>
    match_mp_tac isat_cfml_insert>>
    simp[]>>
    match_mp_tac (GEN_ALL is_rup_sound)>>gvs[]>>
    asm_exists_tac>>simp[])
  >- (* deleting XORs by ID *)
    metis_tac[delete_xors_sound]
QED

(* The main operational theorem about check_xlrups *)
Theorem check_xlrups_sound:
  ∀ls cfml xfml.
  check_xlrups ls cfml xfml = SOME (cfml',xfml') ⇒
  (isat_fml w (values cfml, values xfml) ⇒
   isat_fml w (values cfml', values xfml'))
Proof
  Induct>>simp[check_xlrups_def]>>
  ntac 4 strip_tac>>
  every_case_tac>>fs[]>>
  strip_tac>>
  drule check_xlrup_sound>>
  disch_then drule>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]
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

Theorem values_build_fml:
  ∀ls id. values (build_fml id ls) = set ls
Proof
  Induct>>fs[build_fml_def,values_def,lookup_def]>>
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

Theorem check_xlrups_unsat_sound:
  check_xlrups_unsat xlrups (build_fml cid cfml) (build_fml xid xfml) ⇒
  ¬ isatisfiable (set cfml,set xfml)
Proof
  rw[check_xlrups_unsat_def]>>
  every_case_tac>>fs[]>>
  `¬∃w. isat_cfml w (values q)` by (
    fs[isat_cfml_def,contains_emp_def,MEM_MAP]>>
    Cases_on`y`>>fs[MEM_toAList,values_def,PULL_EXISTS]>>
    rw[]>>
    asm_exists_tac>>simp[isat_cclause_def])>>
  fs[]>>
  drule check_xlrups_sound>>
  fs[isatisfiable_def,isat_fml_def]>>
  metis_tac[values_build_fml]
QED

Definition wf_clause_def:
  wf_clause (C:cclause) ⇔ ¬ MEM 0 C
End

Definition wf_cfml_def:
  wf_cfml cfml ⇔
  ∀C. C ∈ values cfml ⇒ wf_clause C
End

Definition wf_xlrup_def:
  (wf_xlrup (RUP n C i0) = wf_clause C) ∧
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
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem wf_cfml_insert:
  wf_cfml fml ∧ wf_clause l ⇒
  wf_cfml (insert n l fml)
Proof
  fs[wf_cfml_def]>>rw[]>>
  gvs[values_def,lookup_insert,AllCaseEqs()]>>
  metis_tac[]
QED

Theorem wf_cfml_check_xlrup:
  wf_cfml cfml ∧ wf_xlrup xlrup ∧
  check_xlrup xlrup cfml xfml = SOME (cfml',xfml') ⇒
  wf_cfml cfml'
Proof
  rw[check_xlrup_def]>>gvs[AllCaseEqs()]
  >-
    metis_tac[wf_cfml_delete_clauses]
  >- (
    fs[wf_xlrup_def]>>
    metis_tac[wf_cfml_insert])
QED

val _ = export_theory ();
