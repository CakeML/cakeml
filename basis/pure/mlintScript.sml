(*
  Pure functions for the Int module.
*)
open preamble mlstringTheory gcdTheory

val _ = new_theory"mlint";

val toChar_def = Define`
  toChar digit = if digit < 10 then CHR (ORD #"0" + digit)
  else CHR (ORD #"A" + digit - 10)`;

Theorem toChar_HEX:
   d < 16 ⇒ (toChar d = HEX d)
Proof
  strip_tac \\ rpt(fs[Once NUMERAL_LESS_THM] >- EVAL_TAC)
QED

(* decimal encoding is very slightly faster if we avoid dividing large big-ints
   by 10, and instead divide them by a power of 10 that fits in 28 bits *)
Definition exp_for_dec_enc_def:
  exp_for_dec_enc = 8n
End

(* compatibility with previous version*)
Definition padLen_DEC_def:
  padLen_DEC = exp_for_dec_enc
End
Theorem padLen_DEC_eq = EVAL ``padLen_DEC``
Definition maxSmall_DEC_def1:
  maxSmall_DEC = 10n ** exp_for_dec_enc
End
Theorem maxSmall_DEC_def = EVAL ``maxSmall_DEC``

val exp_thm = EVAL ``10n ** exp_for_dec_enc``
val exp_tm = rhs (concl exp_thm)

Definition num_to_rev_chars_def:
  num_to_rev_chars i 0 k = num_to_rev_chars (i DIV ^exp_tm)
        exp_for_dec_enc ((i MOD ^exp_tm) + k) /\
  num_to_rev_chars i (SUC j) k = (if k < 10 /\ i = 0 then [toChar k]
        else toChar (k MOD 10) :: num_to_rev_chars i j (k DIV 10))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I)
    (\(i, j, k). (i * (10 ** j)) + k, exp_for_dec_enc - j)`
  \\ simp [GSYM DIVISION, GSYM exp_thm]
  \\ rw [exp_for_dec_enc_def]
  \\ simp [EXP]
  \\ irule (Q.prove (`a <= d /\ b <= c /\ (a < d \/ b < c) ==> (a : num) + b < c + d`, simp []))
  \\ simp [arithmeticTheory.DIV_LESS_EQ]
  \\ Cases_on `i = 0` \\ fs []
End

Triviality add_lt_divisible_iff:
  y MOD n = 0n ==> (x + y < n <=> x < n /\ y = 0)
Proof
  rw []
  \\ EQ_TAC
  \\ fs []
  \\ CCONTR_TAC \\ fs []
QED

Theorem num_to_rev_chars_thm:
  !i j k. num_to_rev_chars i j k = REVERSE (num_to_dec_string (k + (i * (10 ** j))))
Proof
  ho_match_mp_tac num_to_rev_chars_ind
  \\ simp [GSYM DIVISION, GSYM exp_thm]
  \\ simp [num_to_dec_string_def, n2s_def]
  \\ rw []
  >- simp [num_to_rev_chars_def, GSYM exp_thm]
  \\ REWRITE_TAC [Once numposrepTheory.n2l_def]
  \\ simp [num_to_rev_chars_def, ZERO_EXP, add_lt_divisible_iff]
  \\ simp [arithmeticTheory.ADD_DIV_RWT, EXP]
  \\ simp [arithmeticTheory.MULT_DIV |> REWRITE_RULE [Once MULT_COMM]]
  \\ rw []
  \\ irule toChar_HEX
  \\ simp [Q.SPECL [`i`, `10`] arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Definition int_to_string_def:
  int_to_string neg_char i =
    (if 0i <= i
        then implode (REVERSE (num_to_rev_chars (Num i) 0 0))
        else implode ([neg_char] ++ REVERSE (num_to_rev_chars (Num (ABS i)) 0 0)))
End

Definition toString_def1:
  toString i = int_to_string #"~" i
End

Theorem toString_def = toString_def1 |> REWRITE_RULE [int_to_string_def]

Theorem int_to_string_thm:
  int_to_string neg_char i =
  implode ((if i < 0i then [neg_char] else []) ++ num_to_dec_string (Num (ABS i)))
Proof
  rw[int_to_string_def, num_to_rev_chars_thm, integerTheory.INT_ABS]
  \\ `F` by intLib.COOPER_TAC
QED

Theorem toString_thm:
   toString i = implode ((if i < 0i then "~" else "") ++ num_to_dec_string (Num (ABS i)))
Proof
  simp [toString_def1, int_to_string_thm]
QED

val num_to_str_def = Define `num_to_str (n:num) = toString (&n)`;

Overload toString = ``num_to_str``

Theorem num_to_str_thm:
  num_to_str n = implode (num_to_dec_string n)
Proof
  fs [toString_thm,num_to_str_def]
QED

(* fromString Definitions *)
val fromChar_unsafe_def = Define`
  fromChar_unsafe char = ORD char - ORD #"0"`;

val fromChar_def = Define`
  fromChar char =
    case char of
      | #"0" => SOME 0n
      | #"1" => SOME 1n
      | #"2" => SOME 2n
      | #"3" => SOME 3n
      | #"4" => SOME 4n
      | #"5" => SOME 5n
      | #"6" => SOME 6n
      | #"7" => SOME 7n
      | #"8" => SOME 8n
      | #"9" => SOME 9n
      | _    => NONE`;

(* Equivalence between the safe and unsafe versions of fromChar *)
Theorem fromChar_eq_unsafe:
   ∀char. isDigit char ⇒ fromChar char = SOME (fromChar_unsafe char)
Proof
  Cases_on `char` \\ rw [isDigit_def, fromChar_def, fromChar_unsafe_def]
  \\ rpt (pop_assum (ASSUME_TAC o CONV_RULE (BINOP_CONV (TRY_CONV numLib.num_CONV)))
  \\ fs [LE])
QED

val fromChars_range_unsafe_def = Define`
  fromChars_range_unsafe l 0       str = 0 ∧
  fromChars_range_unsafe l (SUC n) str =
    fromChars_range_unsafe l n str * 10 + fromChar_unsafe (strsub str (l + n))`;

val fromChars_range_def = Define`
  fromChars_range l 0       str = SOME 0 ∧
  fromChars_range l (SUC n) str =
    let rest = OPTION_MAP ($* 10n) (fromChars_range l n str) and
        head = fromChar (strsub str (l + n))
    in OPTION_MAP2 $+ rest head`;

Theorem fromChars_range_eq_unsafe:
   ∀str l r. EVERY isDigit str ∧ l + r <= STRLEN str ⇒
     fromChars_range l r (strlit str) =
     SOME (fromChars_range_unsafe l r (strlit str))
Proof
  Induct_on `r`
  \\ rw [fromChars_range_def
        , fromChars_range_unsafe_def
        , fromChar_eq_unsafe
        , EVERY_EL]
QED

val fromChars_unsafe_def = tDefine "fromChars_unsafe" `
  fromChars_unsafe 0 str = 0n ∧ (* Shouldn't happend *)
  fromChars_unsafe n str =
    if n ≤ padLen_DEC
    then fromChars_range_unsafe 0 n str
    else let n'    = n - padLen_DEC;
             front = fromChars_unsafe n' str * maxSmall_DEC;
             back  = fromChars_range_unsafe n' padLen_DEC str
         in front + back`
(wf_rel_tac `measure FST` \\ rw [padLen_DEC_eq]);
val fromChars_unsafe_ind = theorem"fromChars_unsafe_ind"

val fromChars_def = tDefine "fromChars" `
  fromChars 0 str = SOME 0n ∧ (* Shouldn't happend *)
  fromChars n str =
    if n ≤ padLen_DEC
    then fromChars_range 0 n str
    else let n'    = n - padLen_DEC;
             front = OPTION_MAP ($* maxSmall_DEC) (fromChars n' str);
             back  = fromChars_range n' padLen_DEC str
         in OPTION_MAP2 $+ front back`
(wf_rel_tac `measure FST` \\ rw [padLen_DEC_eq]);
val fromChars_ind = theorem"fromChars_ind"

Theorem fromChars_eq_unsafe:
   ∀n s. EVERY isDigit (explode s) ∧ n ≤ strlen s ⇒
    fromChars n s = SOME (fromChars_unsafe n s)
Proof
  let val tactics = [fromChars_def
                    , fromChars_unsafe_def
                    , fromChars_range_eq_unsafe
                    , strlen_def
                    , explode_def]
  in recInduct fromChars_ind
  \\ CONJ_TAC >- rw tactics
  \\ rw [] \\ Cases_on `str'`
  \\ rw tactics
  \\ fs tactics
  end
QED

val fromString_unsafe_def = Define`
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"~"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str`;

val fromString_def = Define`
  fromString str =
    if strlen str = 0
    then (NONE : int option)
    else if strsub str 0 = #"~" ∨
            strsub str 0 = #"-"
      then OPTION_MAP ($~ o $&)
             (fromChars (strlen str - 1)
                        (substring str 1 (strlen str - 1)))
    else if strsub str 0 = #"+"
      then OPTION_MAP $&
             (fromChars (strlen str - 1)
                        (substring str 1 (strlen str - 1)))
      else OPTION_MAP $& (fromChars (strlen str) str)`;

val fromNatString_def = Define `
  fromNatString str =
    case fromString str of
      NONE => NONE
    | SOME i => if 0 <= i then SOME (Num i) else NONE`;

(* fromString auxiliar lemmas *)
Theorem fromChars_range_unsafe_0_substring_thm:
   ∀m r s. r ≤ m ⇒
    fromChars_range_unsafe 0 r s =
      fromChars_range_unsafe 0 r (substring s 0 m)
Proof
  Induct_on `r` \\ rw [fromChars_range_unsafe_def, strsub_substring_0_thm]
QED

Theorem fromChars_range_unsafe_split:
   ∀m n s. m ≠ 0 ∧ m < n
    ⇒ fromChars_range_unsafe 0 n s =
        10 ** m * fromChars_range_unsafe    0    (n - m) s
        +         fromChars_range_unsafe (n - m)    m    s
Proof
  Induct_on `m`
  >- rw []
  >- (`∀m k w. 10**SUC m*k + 10*w = 10*(10**m*k + w)` by simp [EXP]
      \\ Cases_on `n`
      \\ rw [fromChars_range_unsafe_def]
      \\ Cases_on `m`
      \\ rw [fromChars_range_unsafe_def])
QED

(* fromString proofs *)
Theorem fromChar_unsafe_thm:
   ∀ h. isDigit h ⇒ fromChar_unsafe h = num_from_dec_string [h]
Proof
  let
    val num_conv = ASSUME_TAC o CONV_RULE (BINOP_CONV (TRY_CONV numLib.num_CONV))
  in Cases_on `h`
  \\ rw [isDigit_def]
  \\ rpt (pop_assum num_conv >> fs [LE, fromChar_unsafe_def])
  end
QED

Theorem fromChars_range_unsafe_thm:
   ∀str. EVERY isDigit str ⇒
    fromChars_range_unsafe 0 (STRLEN str) (strlit str) =
      num_from_dec_string str
Proof
  recInduct SNOC_INDUCT
  \\ rw [fromChars_range_unsafe_def
        ,ASCIInumbersTheory.num_from_dec_string_def]
  \\ `isDigit x` by fs [EVERY_SNOC]
  \\ rw [ASCIInumbersTheory.s2n_def
        , numposrepTheory.l2n_def
        , MAP_REVERSE_STEP
        , substring_def
        , MIN_DEF, implode_def
        , EL_LENGTH_SNOC
        , fromChar_unsafe_thm
          |> computeLib.RESTR_EVAL_RULE [``fromChar_unsafe``,``isDigit``]
        , fromChars_range_unsafe_0_substring_thm
          |> SPEC_ALL
          |> INST [``m : num`` |->  ``r : num``]
          |> SIMP_RULE std_ss []
          |> Once
        , SEG_0_SNOC |> SPEC ``LENGTH l``
                     |> SPEC ``l : 'a list``
                     |> SIMP_RULE std_ss [SEG_LENGTH_ID]]
  \\ fs [ASCIInumbersTheory.s2n_def,EVERY_SNOC]
QED

Theorem fromChars_range_unsafe_eq:
   ∀n s. n ≤ (strlen s) ⇒ fromChars_unsafe n s = fromChars_range_unsafe 0 n s
Proof
  recInduct fromChars_unsafe_ind
  \\ rw [fromChars_unsafe_def
        , fromChars_range_unsafe_def
        , padLen_DEC_eq
        , maxSmall_DEC_def
        , fromChars_range_unsafe_split |> SPEC ``8n``
                                       |> SIMP_RULE std_ss []
                                       |> GSYM]
QED

Theorem fromString_unsafe_thm:
   ∀str. (HD str ≠ #"~" ⇒ EVERY isDigit str) ∧
         (HD str = #"~" ⇒ EVERY isDigit (DROP 1 str)) ⇒
         fromString_unsafe (strlit str) =
           if HD str = #"~"
           then ~&num_from_dec_string (DROP 1 str)
           else &num_from_dec_string str
Proof
  rw [fromString_unsafe_def
     , fromChars_range_unsafe_eq
     , fromChars_range_unsafe_thm
     , substring_def, SEG_TAKE_DROP
     , TAKE_LENGTH_ID_rwt
     , fromChars_range_unsafe_thm
       |> ISPEC ``DROP 1 str' : string``
       |> REWRITE_RULE
          [prove(``STRLEN (DROP 1 str') = STRLEN str' - 1``, rw [])]]
  \\ rename1`s ≠ ""` \\ Cases_on `s` \\ fs[]
QED

Theorem fromChars_range_lemma[local] =
  CONJ
   (fromChars_range_unsafe_thm
    |> ISPEC ``DROP 1 str' : string``
    |> REWRITE_RULE [prove(``STRLEN (DROP 1 str') = STRLEN str' - 1``, rw [])])
   (fromChars_range_unsafe_thm
    |> ISPEC “h::t : string”
    |> REWRITE_RULE [prove(``STRLEN (h::t) = SUC (STRLEN t)``, rw [])])

Theorem fromString_thm:
  ∀str.
    str ≠ "" ∧
    (HD str ≠ #"~" ∧ HD str ≠ #"-" ∧ HD str ≠ #"+" ⇒ EVERY isDigit str) ∧
    (HD str = #"~" ∨ HD str = #"-" ∨ HD str = #"+" ⇒ EVERY isDigit (DROP 1 str)) ⇒
      fromString (strlit str) = SOME
        if HD str = #"~" ∨ HD str = #"-"
        then ~&num_from_dec_string (DROP 1 str)
        else if HD str = #"+"
        then &num_from_dec_string (DROP 1 str)
        else &num_from_dec_string str
Proof
  Cases
  \\ rw [fromString_def, fromChars_eq_unsafe, fromChars_range_unsafe_eq,
         fromChars_range_unsafe_thm, substring_def, SEG_TAKE_DROP,
         TAKE_LENGTH_ID_rwt,
         fromChars_range_lemma]
QED

val fromString_eq_unsafe = save_thm("fromString_eq_unsafe",
  fromString_thm |> SIMP_RULE std_ss [GSYM fromString_unsafe_thm]);

Theorem fromString_toString_Num:
   0 ≤ n ⇒ fromString (strlit (num_to_dec_string (Num n))) = SOME n
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[fromString_thm]
  \\ qspec_then`Num n`assume_tac EVERY_isDigit_num_to_dec_string
  \\ Cases_on`num_to_dec_string (Num n)` \\ fs[]
  \\ rw[]
  \\ gs[stringTheory.isDigit_def]
  \\ qpat_x_assum ‘toString _ = _’ (SUBST1_TAC o SYM)
  \\ simp[toNum_toString, integerTheory.INT_OF_NUM]
QED

Triviality fromString_helper:
  HD (toString (i : num)) = c ==> isDigit c
Proof
  qspec_then `i` mp_tac EVERY_isDigit_num_to_dec_string
  \\ Cases_on `toString i : string` \\ fs []
  \\ rw []
  \\ simp []
QED

Theorem fromString_int_to_string[simp]:
   neg_char = #"~" \/ neg_char = #"-" ==>
   fromString (int_to_string neg_char i) = SOME i
Proof
  simp [int_to_string_thm,implode_def]
  \\ disch_tac
  \\ DEP_REWRITE_TAC [fromString_thm]
  \\ rw [EVERY_isDigit_num_to_dec_string, EVERY_DROP]
  \\ gs [ASCIInumbersTheory.toNum_toString]
  \\ simp [Q.prove (`&(Num (ABS i)) = (if i < 0 then (- i) else i)`, intLib.COOPER_TAC)]
  \\ drule_then (mp_tac o CONV_RULE EVAL) fromString_helper
  \\ simp []
QED

Theorem fromString_toString[simp]:
   !i:int. fromString (toString i) = SOME i
Proof
  simp [toString_def1]
QED

Theorem fromNatString_toString[simp]:
   !n:num. fromNatString (toString n) = SOME n
Proof
  fs [num_to_str_def,fromNatString_def]
QED

Theorem fromChar_IS_SOME_IFF:
   IS_SOME (fromChar c) ⇔ isDigit c
Proof
  simp[fromChar_def]
  \\ rpt(IF_CASES_TAC  \\ rveq >- EVAL_TAC)
  \\ rw[]
  \\ EVAL_TAC
  \\ Cases_on`c`
  \\ simp[]
  \\ fs[]
QED

Theorem fromChars_range_IS_SOME_IFF:
   ∀s x y. (x + y ≤ strlen s) ⇒ (IS_SOME (fromChars_range x y s) ⇔ EVERY isDigit (TAKE y (DROP x (explode s))))
Proof
  Induct_on`y`
  \\ rw[fromChars_range_def]
  \\ fs[IS_SOME_EXISTS] \\ rw[]
  \\ fs[PULL_EXISTS]
  \\ fs[EQ_IMP_THM]
  \\ fsrw_tac[DNF_ss][]
  \\ rw[] \\ res_tac
  \\ Cases_on`x < LENGTH (explode s)` \\ fs[DROP_LENGTH_TOO_LONG]
  \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS, LENGTH_TAKE_EQ, EL_TAKE, EL_DROP]
  \\ TRY (
    qx_gen_tac`m`
    \\ strip_tac
    \\ Cases_on`m =y` \\ fs[] \\ rw[]
    \\ Cases_on`s` \\ fs[]
    \\ metis_tac[fromChar_IS_SOME_IFF, IS_SOME_EXISTS, ADD_COMM])
  \\ Cases_on`s` \\ fs[]
  \\ fs[PULL_FORALL]
  \\ first_x_assum(qspecl_then[`strlit s'`,`x`]mp_tac)
  \\ simp[] \\ strip_tac \\ fs[]
  \\ simp[GSYM IS_SOME_EXISTS]
  \\ simp[fromChar_IS_SOME_IFF]
  \\ first_x_assum(qspec_then`y`mp_tac)
  \\ simp[]
QED

Theorem fromChars_IS_SOME_IFF:
   ∀n s. n ≤ strlen s ⇒ (IS_SOME (fromChars n s) ⇔ EVERY isDigit (TAKE n (explode s)))
Proof
  recInduct fromChars_ind
  \\ rw[fromChars_def]
  \\ fs[fromChars_range_IS_SOME_IFF]
  \\ fs[IS_SOME_EXISTS, PULL_EXISTS]
  \\ fs[EQ_IMP_THM] \\ fs[PULL_EXISTS]
  \\ rw[] \\ fs[]
  >- (
    qspecl_then[`str'`,`SUC v2 - padLen_DEC`,`padLen_DEC`]mp_tac fromChars_range_IS_SOME_IFF
    \\ simp[]
    \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_TAKE,EL_DROP]
    \\ rw[]
    \\ Cases_on`n < SUC v2 - padLen_DEC` \\ fs[]
    \\ first_x_assum(qspec_then`n + padLen_DEC - SUC v2`mp_tac)
    \\ simp[] )
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- ( fs[EVERY_MEM, MEM_EL, PULL_EXISTS, LENGTH_TAKE_EQ, EL_TAKE] )
  \\ strip_tac \\ fs[]
  \\ qspecl_then[`str'`,`SUC v2 - padLen_DEC`,`padLen_DEC`]mp_tac fromChars_range_IS_SOME_IFF
  \\ simp[IS_SOME_EXISTS]
  \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS, LENGTH_TAKE_EQ, EL_TAKE, EL_DROP]
QED

Theorem fromString_EQ_NONE:
   ~isDigit c /\ c <> #"+" /\ c <> #"~" /\ c <> #"-" ==>
   fromString (implode (STRING c x)) = NONE
Proof
  rw [fromString_def,implode_def,strsub_def]
  \\ `(SUC (STRLEN x)) <= strlen (strlit (STRING c x))` by fs [strlen_def]
  \\ drule fromChars_IS_SOME_IFF \\ fs [explode_def]
QED

(* this formulation avoids a comparsion using = for better performance *)
val int_cmp_def = Define `
  int_cmp i (j:int) = if i < j then LESS else
                      if j < i then GREATER else EQUAL`

Definition num_gcd_def:
  num_gcd a b = if a = 0n then b else num_gcd (b MOD a) a
End

Theorem num_gcd_eq_gcd:
  num_gcd = gcd
Proof
  simp [FUN_EQ_THM]
  \\ ho_match_mp_tac num_gcd_ind
  \\ rw []
  \\ once_rewrite_tac [GCD_EFFICIENTLY,num_gcd_def]
  \\ rw []
QED

Definition int_gcd_def:
  int_gcd (m:int) (n:int) = & num_gcd (Num (ABS m)) (Num (ABS n)) :int
End

val _ = export_theory();
