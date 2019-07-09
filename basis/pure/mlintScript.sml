(*
  Pure functions for the Int module.
*)
open preamble mlstringTheory

val _ = new_theory"mlint";

val toChar_def = Define`
  toChar digit = if digit < 10 then CHR (ORD #"0" + digit)
  else CHR (ORD #"A" + digit - 10)`;

Theorem toChar_HEX:
   d < 16 ⇒ (toChar d = HEX d)
Proof
  strip_tac \\ rpt(fs[Once NUMERAL_LESS_THM] >- EVAL_TAC)
QED

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

Theorem zero_pad_thm:
   ∀n acc. zero_pad n acc = REPLICATE n #"0" ++ acc
Proof
  Induct \\ rw[GSYM SNOC_REPLICATE,zero_pad_def] \\ EVAL_TAC
QED

val simple_toChars_def = Define`
  simple_toChars pad i acc =
    if i < 10 then zero_pad (pad-1) (toChar i :: acc)
    else simple_toChars (pad-1) (i DIV 10) (toChar (i MOD 10) :: acc)`;
val simple_toChars_ind = theorem"simple_toChars_ind";

Theorem simple_toChars_thm:
   ∀pad i acc. simple_toChars pad i acc =
    REPLICATE (pad - LENGTH (num_to_dec_string i)) #"0" ++ num_to_dec_string i ++ acc
Proof
  ho_match_mp_tac simple_toChars_ind \\
  rw[ASCIInumbersTheory.num_to_dec_string_def,
     ASCIInumbersTheory.n2s_def] \\
  rw[Once simple_toChars_def]
  >- ( fs[NUMERAL_LESS_THM,zero_pad_thm] \\ EVAL_TAC )
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS,ADD1]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ match_mp_tac toChar_HEX
  \\ `i MOD 10 < 10` by simp[MOD_LESS]
  \\ rw[]
QED

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

Theorem toChars_thm:
   ∀chunk rest acc. chunk < maxSmall_DEC ⇒
    (toChars chunk rest acc =
      num_to_dec_string (rest * maxSmall_DEC + chunk) ++ acc)
Proof
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
  \\ simp[]
QED

val toString_def = Define`
  toString i =
    if 0i ≤ i ∧ i < 10 then
      str (toChar (Num (ABS i)))
    else
      implode ((if i < 0i then "~" else "")++
               (toChars (Num (ABS i) MOD maxSmall_DEC) (Num (ABS i) DIV maxSmall_DEC) ""))`;

Theorem toString_thm:
   toString i = implode ((if i < 0i then "~" else "") ++ num_to_dec_string (Num (ABS i)))
Proof
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
    \\ simp[] )
QED

val num_to_str_def = Define `num_to_str (n:num) = toString (&n)`;
val _ = overload_on("toString",``num_to_str``);

val num_to_str_thm = Q.store_thm("num_to_str_thm",
  `num_to_str n = implode (num_to_dec_string n)`,
  fs [toString_thm,num_to_str_def]);

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
    then SOME 0i
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

Theorem fromString_thm:
   ∀str. (HD str ≠ #"~" ∧ HD str ≠ #"-" ∧ HD str ≠ #"+" ⇒ EVERY isDigit str) ∧
         (HD str = #"~" ∨ HD str = #"-" ∨ HD str = #"+" ⇒ EVERY isDigit (DROP 1 str)) ⇒
         fromString (strlit str) = SOME
           if HD str = #"~" ∨ HD str = #"-"
           then ~&num_from_dec_string (DROP 1 str)
           else if HD str = #"+"
           then &num_from_dec_string (DROP 1 str)
           else &num_from_dec_string str
Proof
  rw [fromString_def
     , fromChars_eq_unsafe
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
  \\ TRY ( qhdtm_x_assum`isDigit`mp_tac \\ EVAL_TAC \\ NO_TAC )
  \\ mp_tac ASCIInumbersTheory.num_dec_string
  \\ simp[FUN_EQ_THM]
  \\ disch_then(qspec_then`Num n`mp_tac)
  \\ simp[]
  \\ simp[integerTheory.INT_OF_NUM]
QED

Theorem fromString_toString[simp]:
   !i:int. fromString (toString i) = SOME i
Proof
  rw [toString_thm,implode_def]
  \\ qmatch_goalsub_abbrev_tac `strlit sss`
  \\ qspec_then `sss` mp_tac fromString_thm
  THEN1
   (reverse impl_tac THEN1
     (fs [Abbr`sss`,toString_thm,ASCIInumbersTheory.toNum_toString]
      \\ rw [] \\ last_x_assum mp_tac \\ intLib.COOPER_TAC)
    \\ fs [Abbr `sss`,EVERY_isDigit_num_to_dec_string])
  \\ `HD sss ≠ #"~" ∧ HD sss ≠ #"-" ∧ HD sss ≠ #"+"` by
   (fs [Abbr `sss`]
    \\ qspec_then `Num (ABS i)` mp_tac EVERY_isDigit_num_to_dec_string
    \\ Cases_on `num_to_dec_string (Num (ABS i))`
    \\ fs []
    \\ CCONTR_TAC \\ fs [] \\ rveq  \\ fs [isDigit_def])
  \\ fs [Abbr `sss`,EVERY_isDigit_num_to_dec_string]
  \\ fs [toString_thm,ASCIInumbersTheory.toNum_toString]
  \\ rw [] \\ last_x_assum mp_tac \\ intLib.COOPER_TAC
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

val _ = export_theory();
