(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)

(* Misc. lemmas (without any compiler constants) *)
Theory misc
Ancestors
  arithLemmas listLemmas setLemmas optionLemmas sptreeLemmas wordLemmas
  alignment alist arithmetic blast[qualified] bitstring bag byte
  combin container list pred_set finite_map rich_list llist option
  pair sorting relation toto comparison bit sptree words set_sep
  indexedLists string machine_ieee integer_word address[qualified]
  path[qualified] res_quan[qualified] lprefix_lub[qualified]
Libs
  boolSimps mp_then dep_rewrite wordsLib BasicProvers
  ASCIInumbersLib bagLib[qualified] blastLib[qualified]

val _ = ParseExtras.tight_equality()

(* Total version of THE *)
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End

Definition opt_bind_def:
 opt_bind n v e =
   case n of
   | NONE => e
   | SOME n' => (n',v)::e
End

(* Note: This globally hides constants over the reals that gets imported through machine_ieeeTheory *)

val _ = remove_ovl_mapping "max" {Name="max", Thy="realax"}
val _ = remove_ovl_mapping "min" {Name="min", Thy="realax"}
val _ = remove_ovl_mapping "pos" {Name="pos", Thy="real"}
val _ = remove_ovl_mapping "abs" {Name="abs", Thy="realax"}
val _ = remove_ovl_mapping "inf" {Name="inf", Thy="real"}

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))
val rveq = rpt BasicProvers.VAR_EQ_TAC
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
(* -- *)

val _ = numLib.temp_prefer_num();

(* used elsewhere in cakeml *)
Theorem SUBSET_IMP:
   s SUBSET t ==> (x IN s ==> x IN t)
Proof
  fs[pred_setTheory.SUBSET_DEF]
QED

Theorem times_add_o:
   (λn:num. k * n + x) = ($+ x) o ($* k)
Proof
  rw[FUN_EQ_THM]
QED

Theorem SORTED_inv_image_LESS_PLUS:
   SORTED (inv_image $< (arithmetic$+ k)) = SORTED $<
Proof
  simp[FUN_EQ_THM]
  \\ Induct
  \\ Q.ISPEC_THEN`$+ k`(fn th => simp[MATCH_MP SORTED_EQ th])
      (MATCH_MP transitive_inv_image transitive_LESS)
  \\ simp[MATCH_MP SORTED_EQ transitive_LESS]
QED

Theorem SORTED_GENLIST_TIMES:
   0 < k ⇒ ∀n. SORTED prim_rec$< (GENLIST ($* k) n)
Proof
  strip_tac
  \\ Induct \\ simp[GENLIST,SNOC_APPEND]
  \\ simp[MEM_GENLIST,PULL_EXISTS,SORTED_APPEND]
QED

Definition shift_seq_def:
  shift_seq k s = \i. s (i + k:num)
End

Overload LLOOKUP = ``λl n. oEL n l``

Theorem LLOOKUP_def =
  listTheory.oEL_def
Theorem LLOOKUP_EQ_EL =
  listTheory.oEL_EQ_EL
Theorem LLOOKUP_THM =
  listTheory.oEL_THM
Theorem LLOOKUP_DROP =
  listTheory.oEL_DROP
Theorem LLOOKUP_TAKE_IMP =
  listTheory.oEL_TAKE_E
Theorem LLOOKUP_LUPDATE =
  listTheory.oEL_LUPDATE

(* app_list stuff should be in an app_list theory *)
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End

Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End

Definition append_def:
  append l = append_aux l []
End

Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs
Proof
  Induct \\ metis_tac [APPEND,APPEND_ASSOC,append_aux_def]
QED

Theorem append_thm[simp]:
   append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []
Proof
  fs [append_def,append_aux_def]
  \\ once_rewrite_tac [append_aux_thm] \\ fs []
QED

Definition SmartAppend_def[simp]:
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)
End

Theorem SmartAppend_thm:
   ∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2
Proof
  Cases \\ Cases \\ rw[]
QED

Theorem SmartAppend_Nil:
  SmartAppend l Nil = l ∧
  SmartAppend Nil l = l
Proof
  Cases_on `l` \\ gvs [SmartAppend_def]
QED

Theorem append_SmartAppend[simp]:
   append (SmartAppend l1 l2) = append l1 ++ append l2
Proof
  rw[append_def,SmartAppend_thm,append_aux_def]
  \\ rw[Once append_aux_thm]
QED

Theorem lemmas[local]:
  (2 + 2 * n - 1 = 2 * n + 1:num) /\
    (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'':num) /\
    (2 * m = 2 * n <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)
Proof
  intLib.ARITH_TAC
QED

Definition zlookup_def:
  zlookup m k = case lookup k m of NONE => 0n | SOME k => k
End

Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End

Theorem tlookup_id:
   x ∉ domain names
   ⇒ tlookup names x = x
Proof
  rw[tlookup_def]
  \\ fs[domain_lookup] \\ CASE_TAC \\ fs[]
QED

Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV
Proof
  strip_tac
  \\ match_mp_tac BIJ_support
  \\ qexists_tac`domain names`
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[tlookup_def]
    \\ CASE_TAC \\ fs[domain_lookup])
  \\ `set (toList names) = IMAGE (tlookup names) (domain names)`
  by (
    pop_assum kall_tac
    \\ simp[EXTENSION,tlookup_def,MEM_toList,domain_lookup]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (qexists_tac`k` \\ fs[])
    \\ metis_tac[] )
  \\ match_mp_tac (MP_CANON CARD_IMAGE_ID_BIJ)
  \\ fs[] \\ rw[] \\ fs[EXTENSION]
  \\ metis_tac[]
QED

Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names
Proof
  rw[EQ_IMP_THM,tlookup_bij_suff]
  \\ fs[BIJ_IFF_INV]
  \\ rw[EXTENSION,domain_lookup,MEM_toList]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`k=x` >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ `tlookup names x = x`
    by (
      simp[tlookup_def]
      \\ CASE_TAC \\ fs[] )
    \\ `tlookup names k = x`
    by ( simp[tlookup_def] )
    \\ metis_tac[] )
  \\ Cases_on`x=v` >- metis_tac[]
  \\ spose_not_then strip_assume_tac
  \\ `tlookup names x = v`
  by ( simp[tlookup_def] )
  \\ `∀k. tlookup names k ≠ x`
  by (
    rw[tlookup_def]
    \\ CASE_TAC \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[])
  \\ metis_tac[]
QED

(* should be composition of oEL and as-yet-undefined "THE default" *)
Definition any_el_def:
  (any_el n [] d = d) /\
  (any_el n (x::xs) d = if n = 0 then x else any_el (n-1:num) xs d)
End

Definition update_resize_def:
  update_resize ls default v n =
    if n < LENGTH ls then
      LUPDATE v n ls
    else
      LUPDATE v n (ls ++ REPLICATE (n * 2 + 1 - LENGTH ls) default)
End

Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End

(* move into HOL? *)

Definition word_list_def:
  (word_list a [] = emp) /\
  (word_list a (x::xs) = set_sep$one (a,x) * word_list (a + bytes_in_word) xs)
End

Definition word_list_exists_def:
  word_list_exists a n =
    SEP_EXISTS xs. word_list a xs * cond (LENGTH xs = n)
End

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End

Theorem EVERY_lookup_vars:
   ∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'
Proof
  Induct >> simp[lookup_vars_def, CaseEq"option", CaseEq"bool", PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]
QED

(* TODO - candidate for move to HOL *)
Theorem num_to_hex_string_length_1:
   ∀x. x < 16 ⇒ (LENGTH (num_to_hex_string x) = 1)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC
QED

(* TODO - candidate for move to HOL *)
Theorem num_to_hex_string_length_2:
   ∀x. 16 ≤ x ∧ x < 256 ⇒ (LENGTH (num_to_hex_string x) = 2)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV (RAND_CONV EVAL))
  \\ strip_tac \\ var_eq_tac \\ pop_assum mp_tac
  \\ EVAL_TAC
QED

Theorem num_from_hex_string_length_2:
   num_from_hex_string [d1;d2] < 256
Proof
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`UNHEX d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`UNHEX d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac
QED

Theorem num_from_hex_string_leading_0:
   ∀ls. ls ≠ [] ⇒ (num_from_hex_string (#"0" :: ls) = num_from_hex_string ls)
Proof
  simp[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def]
  \\ ho_match_mp_tac SNOC_INDUCT \\ simp[]
  \\ simp[REVERSE_SNOC]
  \\ simp[numposrepTheory.l2n_def]
  \\ rw[]
  \\ Cases_on`ls` \\ fs[numposrepTheory.l2n_def]
  \\ EVAL_TAC
QED

Theorem num_from_hex_string_length_2_less_16:
   ∀h1 h2. isHexDigit h1 ⇒ num_from_hex_string [h1;h2] < 16 ⇒ h1 = #"0"
Proof
  rw[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ Cases_on`UNHEX h1 MOD 16` \\ fs[]
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ fs[stringTheory.isHexDigit_def]
  \\ Cases_on`h1` \\ fs[]
  >- (
    `MEM (n - 48) (COUNT_LIST (58 - 48))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def])
  >- (
    `MEM (n - 97) (COUNT_LIST (103 - 97))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def]
    \\ `n = 97` by decide_tac
    \\ fs[ASCIInumbersTheory.UNHEX_def] )
  \\ `MEM (n - 65) (COUNT_LIST (71 - 65))` by simp[MEM_COUNT_LIST]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac
  \\ rfs[SUB_RIGHT_EQ]
  \\ fs[ASCIInumbersTheory.UNHEX_def]
  \\ `n = 65` by decide_tac
  \\ fs[ASCIInumbersTheory.UNHEX_def]
QED

Theorem num_from_hex_string_num_to_hex_string[simp]:
   num_from_hex_string (num_to_hex_string n) = n
Proof
  ASCIInumbersTheory.num_hex_string
  |> SIMP_RULE std_ss [combinTheory.o_DEF,FUN_EQ_THM]
  |> MATCH_ACCEPT_TAC
QED

(* n.b. used in hol-reflection *)

Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
Proof
  rw[FLOOKUP_DEF]
QED

Theorem domain_rrestrict_subset:
   domain (rrestrict r s) ⊆ domain r ∩ s
Proof
  rw[set_relationTheory.domain_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[]
QED

Theorem range_rrestrict_subset:
   range (rrestrict r s) ⊆ range r ∩ s
Proof
  rw[set_relationTheory.range_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[]
QED

Theorem GSPEC_o:
   GSPEC f o g = { x | ∃y. (g x, T) = f y }
Proof
  simp[FUN_EQ_THM, GSPECIFICATION]
QED

Theorem any_el_ALT:
   ∀l n d. any_el n l d = if n < LENGTH l then EL n l else d
Proof
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[] \\ rfs[]
QED

Theorem MOD_MINUS:
   0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k) MOD k
Proof
  strip_tac
  \\ mp_tac (wordsTheory.MOD_COMPLEMENT |> Q.SPECL [`k`,`p`,`n MOD (p * k)`])
  \\ impl_tac THEN1 (fs [MOD_LESS,ZERO_LESS_MULT])
  \\ fs [MOD_MULT_MOD]
QED

Definition option_fold_def:
  (option_fold f x NONE = x) ∧
  (option_fold f x (SOME y) = f y x)
End

Theorem ORD_eq_0:
   (ORD c = 0 ⇔ c = CHR 0) ∧ (0 = ORD c ⇔ c = CHR 0)
Proof
  metis_tac[char_BIJ, ORD_CHR, EVAL ``0n < 256``]
QED

Theorem w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]

Theorem CHR_w2n_n2w_ORD:
   (CHR o w2n o (n2w:num->word8) o ORD) = I
Proof
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
QED

Theorem n2w_ORD_CHR_w2n:
   ((n2w:num->word8) o ORD o CHR o w2n) = I
Proof
  rw[w2n_lt_256, o_DEF, ORD_BOUND, ORD_CHR, FUN_EQ_THM]
QED

Theorem CHR_w2n_n2w_ORD_simp[simp]:
   !c. CHR(w2n((n2w:num->word8)(ORD c))) = c
Proof
  metis_tac[CHR_w2n_n2w_ORD,o_THM,I_THM]
QED

Theorem n2w_ORD_CHR_w2n_simp[simp]:
   !w. n2w(ORD(CHR(w2n w))) = (w:word8)
Proof
  metis_tac[n2w_ORD_CHR_w2n,o_THM,I_THM]
QED

Theorem MAP_CHR_w2n_11:
   !ws1 ws2:word8 list.
      MAP (CHR ∘ w2n) ws1 = MAP (CHR ∘ w2n) ws2 <=> ws1 = ws2
Proof
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `ws2` \\ fs [] \\ metis_tac [CHR_11,w2n_lt_256,w2n_11]
QED

Definition shift_left_def:
  shift_left (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_left (a << 32) (n - 32)
  else if n > 16 then shift_left (a << 16) (n - 16)
  else if n > 8 then shift_left (a << 8) (n - 8)
  else shift_left (a << 1) (n - 1)
End

Theorem shift_left_rwt:
   !a n. a << n = shift_left a n
Proof
  completeInduct_on `n`
  \\ rw [Once shift_left_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs []
QED

Definition shift_right_def:
  shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_right (a >>> 32) (n - 32)
  else if n > 16 then shift_right (a >>> 16) (n - 16)
  else if n > 8 then shift_right (a >>> 8) (n - 8)
  else shift_right (a >>> 1) (n - 1)
End

Theorem shift_right_rwt:
   !a n. a >>> n = shift_right a n
Proof
  completeInduct_on `n`
  \\ rw [Once shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs []
QED

Definition arith_shift_right_def:
  arith_shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) /\ ~word_msb a then 0w
  else if (a = -1w) \/ n > dimindex(:'a) /\ word_msb a then -1w
  else if n > 32 then arith_shift_right (a >> 32) (n - 32)
  else if n > 16 then arith_shift_right (a >> 16) (n - 16)
  else if n > 8 then arith_shift_right (a >> 8) (n - 8)
  else arith_shift_right (a >> 1) (n - 1)
End

Theorem arith_shift_right_rwt:
   !a n. a >> n = arith_shift_right a n
Proof
  completeInduct_on `n`
  \\ rw [Once arith_shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX]
QED

Definition any_word64_ror_def:
  any_word64_ror (w:word64) (n:num) =
    if 64 <= n then any_word64_ror w (n - 64) else
    if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
    if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
    if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
    if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
    if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
    if 1 <= n then word_ror w 1 else w
End

Theorem word_ror_eq_any_word64_ror:
   !a n. word_ror a n = any_word64_ror a n
Proof
  completeInduct_on `n`
  \\ rw [Once any_word64_ror_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX]
  THEN1 fs [fcpTheory.CART_EQ,wordsTheory.word_ror_def,arithmeticTheory.SUB_MOD]
  \\ `n = 1 \/ n = 0` by fs [] \\ fs []
QED

Theorem the_nil_eq_cons:
   (the [] x = y::z) ⇔ x = SOME (y ::z)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem n2l_DIV_MOD:
   !b n k. 1 < b /\ 0 < k /\ b ** k <= n ==>
   (n2l b (n MOD (b ** k)) ++ REPLICATE (k - LENGTH (n2l b (n MOD (b ** k)))) 0 ++
    n2l b (n DIV (b ** k)) = n2l b n)
Proof
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
  \\ rewrite_tac[GSYM REPLICATE,ADD1]
  \\ `LOG b (n MOD b) = 0`
  by ( simp[logrootTheory.LOG_EQ_0] )
  \\ simp[]
QED

Theorem the_OPTION_MAP:
     !f d opt.
    f d = d ==>
    the d (OPTION_MAP f opt) = f (the d opt)
Proof
    rw [] >> Cases_on `opt` >> rw [the_def]
QED

Theorem BIJ_UPDATE:
   !f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)
Proof
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []
QED

Theorem INJ_UPDATE:
   INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)
Proof
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []
QED

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)
Theorem subspt_domain_SUBSET:
   subspt t1 t2 ==> domain t1 SUBSET domain t2
Proof
  fs [subspt_def,SUBSET_DEF]
QED

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

(* computes the next position for which P holds *)
Definition Lnext_def:
  Lnext P ll = if eventually P ll then
                        if P ll then 0
                        else SUC(Lnext P (THE (LTL ll)))
                     else ARB
Termination
  exists_tac``\(P,ll') (P',ll).
    ((P = P') /\ eventually P ll /\ eventually P ll' /\
    (LTL ll = SOME ll') /\ ¬ P ll)`` >>
    reverse(rw[relationTheory.WF_DEF,eventually_thm])
  >-(Cases_on`ll` >> fs[])
  >-(Cases_on`ll` >> fs[]) >>
  Cases_on`w` >> rename[`B(P, ll)`] >> rename[`B(P, ll)`] >>
  reverse(Cases_on`eventually P ll`)
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  rpt(LAST_X_ASSUM MP_TAC) >> qid_spec_tac `ll` >>
  HO_MATCH_MP_TAC eventually_ind >> rw[]
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  Cases_on`B(P,ll)` >-(metis_tac[]) >>
  qexists_tac`(P,h:::ll)` >> fs[] >> rw[] >> pairarg_tac >> fs[]
End

Definition Lnext_pos_def:
  Lnext_pos (ll :num llist) = Lnext (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0) ll
End

Theorem option_eq_some =
  LIST_CONJ [
    OPTION_IGNORE_BIND_EQUALS_OPTION,
    OPTION_BIND_EQUALS_OPTION,
    OPTION_CHOICE_EQUALS_OPTION]

Theorem fevery_to_drestrict:
 !P m s.
  FEVERY P m ⇒ FEVERY P (DRESTRICT m s)
Proof
 rw [FEVERY_ALL_FLOOKUP,FLOOKUP_DRESTRICT]
QED

Definition make_even_def:
  make_even n = if EVEN n then n else n+1
End

Theorem EVEN_make_even[simp]:
   EVEN (make_even x)
Proof
  rw[make_even_def, EVEN_ADD]
QED

Theorem FOLDR_FUNPOW:
   FOLDR (λx. f) x ls = FUNPOW f (LENGTH ls) x
Proof
  qid_spec_tac`x`
  \\ Induct_on`ls`
  \\ rw[FUNPOW_SUC]
QED

Theorem toPath_fromList:
   (toPath (x, fromList []) = stopped_at x) ∧
   (toPath (x, fromList ((y,z)::t)) = pcons x y (toPath (z, fromList t)))
Proof
  conj_tac >- EVAL_TAC
  \\ rw[pathTheory.pcons_def, pathTheory.first_def, pathTheory.path_rep_bijections_thm]
QED

Definition steps_def:
  (steps f x [] = []) ∧
  (steps f x (j::js) =
   let y = f x j in
   let tr = steps f y js in
     ((j,y)::tr))
End

Definition steps_rel_def:
  (steps_rel R x [] ⇔ T) ∧
  (steps_rel R x ((j,y)::tr) ⇔
    R x j y ∧
    steps_rel R y tr)
End

val steps_rel_ind = theorem"steps_rel_ind";

Theorem steps_rel_okpath:
   ∀R x tr.
    steps_rel R x tr ⇔ okpath R (toPath (x,fromList tr))
Proof
  recInduct steps_rel_ind
  \\ rewrite_tac[toPath_fromList]
  \\ rw[steps_rel_def, pathTheory.first_def, pathTheory.path_rep_bijections_thm]
QED

Theorem steps_rel_LRC:
    ∀R x tr.
     steps_rel R x tr ⇒
     LRC (λx y. ∃i. R x i y)
       (FRONT(x::(MAP SND tr))) x (LAST (x::(MAP SND tr)))
Proof
  recInduct steps_rel_ind
  \\ rw[steps_rel_def]
  \\ rw[LRC_def, PULL_EXISTS]
  \\ asm_exists_tac \\ rw[]
QED

Theorem LAST_MAP_SND_steps_FOLDL:
   ∀f x ls. LAST (x::(MAP SND (steps f x ls))) = FOLDL f x ls
Proof
  Induct_on`ls` \\ rw[steps_def]
QED

(* Re-export definitions moved to topic libraries so that downstream code
   referencing miscTheory.foo still works. *)
Theorem enumerate_def = listLemmasTheory.enumerate_def
Theorem find_index_def = listLemmasTheory.find_index_def
Theorem anub_def = listLemmasTheory.anub_def
Theorem anub_ind = listLemmasTheory.anub_ind
Theorem anub_all_distinct_keys = listLemmasTheory.anub_all_distinct_keys
Theorem UPDATE_LIST_def = listLemmasTheory.UPDATE_LIST_def
Theorem UPDATE_LIST_THM = listLemmasTheory.UPDATE_LIST_THM
Theorem splitlines_def = listLemmasTheory.splitlines_def
Theorem CONCAT_WITH_def = listLemmasTheory.CONCAT_WITH_def
Theorem CONCAT_WITH_aux_def = listLemmasTheory.CONCAT_WITH_aux_def
Theorem insert_atI_def = listLemmasTheory.insert_atI_def
Theorem is_subseq_def = listLemmasTheory.is_subseq_def
Theorem list_inter_def = listLemmasTheory.list_inter_def
Theorem list_subset_def = listLemmasTheory.list_subset_def
Theorem list_set_eq_def = listLemmasTheory.list_set_eq_def
Theorem MAP3_def[simp] = listLemmasTheory.MAP3_def
Theorem every_zip_split = listLemmasTheory.every_zip_split
Theorem FST_triple = listLemmasTheory.FST_triple
Theorem MAP_EQ_ID = listLemmasTheory.MAP_EQ_ID
Theorem EL_CONS_IF = listLemmasTheory.EL_CONS_IF
Theorem LASTN_LEMMA = listLemmasTheory.LASTN_LEMMA
Theorem LESS_LENGTH = listLemmasTheory.LESS_LENGTH
Theorem UNCURRY_eq_pair = listLemmasTheory.UNCURRY_eq_pair
Theorem ALL_DISTINCT_alist_to_fmap_REVERSE =
  listLemmasTheory.ALL_DISTINCT_alist_to_fmap_REVERSE
Theorem FUPDATE_LIST_alist_to_fmap =
  listLemmasTheory.FUPDATE_LIST_alist_to_fmap
Theorem DISTINCT_FUPDATE_LIST_UNION =
  listLemmasTheory.DISTINCT_FUPDATE_LIST_UNION

Theorem LEAST_thm = arithLemmasTheory.LEAST_thm
Theorem least_from_def = arithLemmasTheory.least_from_def
Theorem least_from_thm = arithLemmasTheory.least_from_thm
Theorem between_def = arithLemmasTheory.between_def

Theorem lookup_any_def = sptreeLemmasTheory.lookup_any_def
Theorem fromList2_def = sptreeLemmasTheory.fromList2_def
Theorem eq_shape_def = sptreeLemmasTheory.eq_shape_def
Theorem copy_shape_def = sptreeLemmasTheory.copy_shape_def
Theorem range_def = sptreeLemmasTheory.range_def
Theorem toAList_domain = sptreeLemmasTheory.toAList_domain
Theorem lookup_zero = sptreeLemmasTheory.lookup_zero
Theorem size_fromAList = sptreeLemmasTheory.size_fromAList

Theorem read_bytearray_def = wordLemmasTheory.read_bytearray_def
Theorem all_words_def = wordLemmasTheory.all_words_def
Theorem asm_write_bytearray_def = wordLemmasTheory.asm_write_bytearray_def
Theorem bytes_in_memory_def = wordLemmasTheory.bytes_in_memory_def
Theorem bytes_in_memory_APPEND = wordLemmasTheory.bytes_in_memory_APPEND
Theorem bytes_in_mem_def = wordLemmasTheory.bytes_in_mem_def
Theorem good_dimindex_def = wordLemmasTheory.good_dimindex_def
Theorem good_dimindex_get_byte_set_byte =
  wordLemmasTheory.good_dimindex_get_byte_set_byte
Theorem get_byte_set_byte_diff = wordLemmasTheory.get_byte_set_byte_diff
Theorem fun2set_disjoint_union = wordLemmasTheory.fun2set_disjoint_union
Theorem v2w_sing = wordLemmasTheory.v2w_sing
