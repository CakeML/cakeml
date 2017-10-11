(*
   Implementation and verification of diff and patch algorithms
*)
open preamble lcsTheory mlintTheory mlstringTheory;

val _ = new_theory "diff";

(* Diff algorithm definition *)

val line_numbers_def = Define `
  (line_numbers l n =
   if LENGTH l <= 1 then
     toString(int_of_num n)
   else
      strcat (toString(int_of_num n)) (strcat(implode ",") (toString(int_of_num (n+LENGTH l)))))`

val acd_def = Define `
  (acd [] [] = #" ")
  /\ (acd l [] = #"d")
  /\ (acd [] l = #"a")
  /\ (acd l l' = #"c")`

val diff_single_header_def = Define `
  (diff_single_header l n l' n' =
   strcat (strcat (line_numbers  l n) (strcat (implode [acd l l']) (line_numbers l' n'))) (strlit "\n"))`

val diff_add_prefix_def = Define `
  diff_add_prefix l h = MAP (strcat h) l `

val diff_single_def = Define `
  diff_single l n l' n' =
    diff_single_header l n l' n'::
    if l = [] then (* add *)
      diff_add_prefix l' (strlit "> ")
    else if l' = [] then (* delete *)
      diff_add_prefix l (strlit "< ")
    else (* change *)
      diff_add_prefix l (strlit "< ")
      ++ (strlit "---\n")::diff_add_prefix l' (strlit "> ")`

val diff_with_lcs_def = Define `
  (diff_with_lcs [] l n l' n' =
      if l = [] /\ l' = [] then
        []
      else
        diff_single l n l' n') /\
  (diff_with_lcs (f::r) l n l' n' =
      let (ll,lr) = SPLITP ($= f) l in
        let (l'l,l'r) = SPLITP ($= f) l' in
          if ll = [] /\ l'l = [] then
            diff_with_lcs r (TL lr) (n+1) (TL l'r) (n+1)
          else
            diff_single ll n l'l n' ++ diff_with_lcs r (TL lr) (n+LENGTH ll+1) (TL l'r) (n'+LENGTH l'l+1))`

val diff_alg_def = Define `
  diff_alg l l' = diff_with_lcs (optimised_lcs l l') l 0 l' 0`

(* Diff algorithm properties *)

val diff_with_lcs_refl = Q.store_thm("diff_with_lcs_refl",
  `!n n'. diff_with_lcs l l n l n' = []`,
  Induct_on `l` >> rw[diff_with_lcs_def,SPLITP]);

val diff_alg_refl = Q.store_thm("diff_alg_refl",
  `diff_alg l l = []`,
  rw[diff_alg_def,lcs_refl',diff_with_lcs_refl,optimised_lcs_refl]);

(* Patch algorithm definition *)

val num_from_string_def = Define `num_from_string s = num_of_int(fromString_unsafe s)`

val string_is_num_def = Define `string_is_num s = EVERY isDigit (explode s)`

val parse_patch_header_def = Define `
    parse_patch_header s =
    case tokens (\x. x = #"a" \/ x = #"d" \/ x = #"c" \/ x = #"\n") s of
      | [l;r] =>
        (case tokens ($= #",") l of
           | [ll;lr] =>
             (if string_is_num ll /\ string_is_num lr then
               case tokens ($= #",") r of
                | [rl;rr] =>
                  if string_is_num rl /\ string_is_num rr then
                    SOME (num_from_string ll,SOME(num_from_string lr),strsub s (strlen l),
                          num_from_string rl,SOME(num_from_string rr))
                  else NONE
                | [r] =>
                  if string_is_num r then
                    SOME (num_from_string ll,SOME(num_from_string lr),strsub s (strlen l),
                          num_from_string r,NONE)
                  else NONE
                | _ => NONE
              else NONE)
           | [l'] =>
             (if string_is_num l' then
               case tokens ($= #",") r of
                | [rl;rr] =>
                  if string_is_num rl /\ string_is_num rr then
                    SOME (num_from_string l',NONE,strsub s (strlen l),
                          num_from_string rl,SOME(num_from_string rr))
                  else NONE
                | [r] =>
                  if string_is_num r then
                    SOME (num_from_string l',NONE,strsub s (strlen l),
                          num_from_string r,NONE)
                  else NONE
                | _ => NONE
              else NONE)
           | _ => NONE)
      | _ => NONE`;

val depatch_line_def = Define `
  depatch_line s =
  if strlen s > 1 then
    if substring s 0 2 = strlit "> " then
      SOME(substring s 2 (strlen s - 2))
    else
      NONE
  else
      NONE`

val depatch_lines_def = Define `
  (depatch_lines [] = SOME []) /\
  (depatch_lines (s::r) =
   case depatch_line s of
       NONE => NONE
     | SOME s' =>
       case depatch_lines r of
           NONE => NONE
         | SOME r' => SOME(s'::r'))`

val patch_aux_def = tDefine "patch_aux" `
 (patch_aux [] file remfl n = SOME file) /\
 (patch_aux (h::patch) file remfl n =
  case parse_patch_header h of
    | NONE => NONE
    | SOME(orig,NONE,#"a",dest,opt) =>
      let dest' = case opt of NONE => dest+1 | SOME dest' => dest' in
        if orig < n \/ remfl < (orig-n) \/ dest' <= dest \/ LENGTH patch < (dest' - dest) then
          NONE
        else
          (case depatch_lines(TAKE (dest'-dest) patch) of
               NONE => NONE
             | SOME p =>
               let lf = TAKE (orig-n) file in
                 let rf = DROP (orig-n) file in
                   (case patch_aux (DROP (dest'-dest) patch) rf (remfl-(orig-n)) orig of
                        SOME rf' => SOME(lf++p++rf')
                      | NONE => NONE))
    | SOME(orig,opt,#"d",dest,NONE) =>
      let orig' = case opt of NONE => orig+1 | SOME orig' => orig' in
        if orig < n \/ orig' < orig \/ remfl < (orig'-n) then
          NONE
        else
          let lf = TAKE (orig-n) file in
            let rf = DROP (orig'-n) file in
              (case patch_aux (DROP (orig'-orig) patch) rf (remfl-(orig'-n)) orig' of
                        SOME rf' => SOME(lf++rf')
                      | NONE => NONE)
    | SOME(orig,opt,#"c",dest,opt') =>
      let orig' = case opt of NONE => orig+1 | SOME orig' => orig' in
        let dest' = case opt' of NONE => dest+1 | SOME dest' => dest' in
          if orig < n \/ orig' < orig \/ remfl < (orig'-n) \/ dest' <= dest \/ LENGTH patch < (dest' - dest) then
            NONE
          else
            let relevant_patch = DROP (1+orig'-orig) patch in
              (case depatch_lines(TAKE (dest'-dest) relevant_patch) of
                   NONE => NONE
                 | SOME p =>
                   let lf = TAKE (orig-n) file in
                     let rf = DROP (orig'-n) file in
                       (case patch_aux (DROP (dest'-dest) relevant_patch) rf (remfl-(orig'-n)) orig' of
                            SOME rf' => SOME(lf++p++rf')
                          | NONE => NONE))
            | SOME _ => NONE
 )`
  (WF_REL_TAC `inv_image $< (LENGTH o FST)` >> fs[]);

val patch_alg_def = Define `
  patch_alg patch file = patch_aux patch file (LENGTH file) 0`



(* Patch cancels diff *)

val string_concat_empty = Q.store_thm("string_concat_empty",
`!s. s ^ strlit "" = s /\ strlit "" ^ s = s`,fs[strcat_thm,implode_explode]);

val tokens_append_strlit = Q.store_thm("tokens_append_strlit",
  `∀P s1 x s2.
   P x ⇒ tokens P (s1 ^ (strlit [x] ^ s2)) = tokens P s1 ++ tokens P s2`,
  rpt strip_tac >> drule tokens_append >> fs[str_def,implode_def]);

val tokens_append_right = Q.store_thm("tokens_append_right_strlit",
  `∀P s x.
   P x ⇒ tokens P (s ^ strlit [x]) = tokens P s`,
  rpt strip_tac >> drule tokens_append_strlit
  >> disch_then (qspecl_then [`s`,`strlit ""`] assume_tac)
  >> fs[string_concat_empty,tokens_def,tokens_aux_def]);

val zero_pad_acc = Q.prove(
`!n acc. STRCAT (zero_pad n "") acc = (zero_pad n acc)`,
  Induct >> PURE_ONCE_REWRITE_TAC [zero_pad_def] >- fs[]
  >> strip_tac >> first_assum(qspec_then `STRING #"0" acc` (assume_tac o GSYM))
  >> fs[]);

val SPLITP_zero_pad = Q.prove(
`!n acc.
  SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
  (zero_pad n acc) =
  let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
    (STRCAT (zero_pad n "") l,r)`,
  Induct >> rpt strip_tac >> fs[zero_pad_def,SPLITP]
  >> pairarg_tac >> fs[zero_pad_acc]
  >> PURE_ONCE_REWRITE_TAC[GSYM zero_pad_acc] >> fs[]);

val simple_toChars_acc = Q.prove(
`!n m acc. STRCAT (simple_toChars m n "") acc = (simple_toChars m n acc)`,
  recInduct COMPLETE_INDUCTION >> rpt strip_tac >> fs[]
  >> PURE_ONCE_REWRITE_TAC[simple_toChars_def]
  >> rw[] >> PURE_ONCE_REWRITE_TAC[GSYM zero_pad_acc]
  >> fs[] >> first_x_assum (qspec_then `n DIV 10` assume_tac) >> rfs[]
  >> first_assum (qspecl_then [`m - 1`,`(STRING (toChar (n MOD 10)) acc)`] (assume_tac o GSYM))
  >> fs[]);

val SPLITP_simple_toChars = Q.prove(
  `!n m acc.
   SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
   (simple_toChars n m acc) =
   let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
     (STRCAT (simple_toChars n m "") l,r)`,
  recInduct simple_toChars_ind >> rpt strip_tac >> fs[SPLITP]
  >> pairarg_tac >> fs[SPLITP] >> PURE_ONCE_REWRITE_TAC[simple_toChars_def]
  >> Cases_on `i < 10` >> fs[SPLITP_zero_pad] >> pairarg_tac >> fs[]
  >> PURE_ONCE_REWRITE_TAC[GSYM zero_pad_acc] >> fs[SPLITP] >> rfs[toChar_def]
  >> PURE_ONCE_REWRITE_TAC[GSYM simple_toChars_acc] >> fs[]
  >> `i MOD 10 + 48 < 58` by intLib.COOPER_TAC >> fs[]);

val toChars_acc = Q.prove(
`!n m acc. STRCAT (toChars m n "") acc = (toChars m n acc)`,
  recInduct COMPLETE_INDUCTION >> rpt strip_tac >> fs[]
  >> PURE_ONCE_REWRITE_TAC[toChars_def]
  >> rw[] >> PURE_ONCE_REWRITE_TAC[GSYM simple_toChars_acc]
  >> fs[] >> PURE_ONCE_REWRITE_TAC[GSYM simple_toChars_acc]
  >> fs[]
  >> first_x_assum (qspec_then `n DIV maxSmall_DEC` assume_tac) >> rfs[maxSmall_DEC_def]
  >> first_assum (qspecl_then [`n MOD maxSmall_DEC`,
                               `STRCAT (simple_toChars padLen_DEC m "") acc`]
                              (assume_tac o GSYM))
  >> fs[maxSmall_DEC_def]);

val SPLITP_toChars = Q.prove(
  `!n m acc.
   SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
   (toChars n m acc) =
   let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
     (STRCAT (toChars n m "") l,r)`,
  recInduct toChars_ind >> rpt strip_tac >> fs[SPLITP]
  >> pairarg_tac >> fs[SPLITP] >> PURE_ONCE_REWRITE_TAC[toChars_def]
  >> rw[] >> fs[SPLITP_simple_toChars] >> PURE_ONCE_REWRITE_TAC[GSYM simple_toChars_acc]
  >> fs[] >> PURE_ONCE_REWRITE_TAC[GSYM toChars_acc] >> fs[]);

val one_to_ten = Q.store_thm("one_to_ten",
  `!P. P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\ (!n. (n:num) >= 10 ==> P n) ==> !n. P n`,
  rpt strip_tac >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC n`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC n)`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC n))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC n)))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC(SUC n))))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC(SUC(SUC n)))))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC(SUC(SUC(SUC n))))))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC n)))))))`
  >> Cases_on `n` >> fs[]
  >> qmatch_goalsub_rename_tac `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC n))))))))`
  >> Cases_on `n` >> fs[]);

val SPLITP_HEX = Q.prove(
`!n. n < 10 ==> SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
     (STRING (HEX n) acc) =
     let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
       (STRING (HEX n) l,r)`,
  recInduct one_to_ten >> rpt strip_tac >> fs[] >> pairarg_tac >> fs[SPLITP]);

val SPLITP_num_toString = Q.prove(
  `!i.
   SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
   (toString (i:num)) = (toString i,[])`,
  recInduct COMPLETE_INDUCTION >> rpt strip_tac
  >> fs[ASCIInumbersTheory.num_to_dec_string_def]
  >> fs[ASCIInumbersTheory.n2s_def]
  >> PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >> rw[] >> fs[SPLITP,SPLITP_HEX]
  >> first_x_assum (qspec_then `n DIV 10` assume_tac) >> rfs[]
  >> fs[SPLITP_APPEND,SPLITP_NIL_SND_EVERY]
  >> `n MOD 10 < 10` by fs[] >> rename [`HEX n`]
  >> pop_assum mp_tac >> rpt(pop_assum kall_tac)
  >> Q.SPEC_TAC (`n`,`n`) >> recInduct one_to_ten >> fs[]);

val SPLITP_int_toString = Q.prove(
  `!i.
   SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
   (toString (i:int)) = (toString i,[])`,
  rpt strip_tac >> fs[integer_wordTheory.toString_def] >> rw[] >> fs[SPLITP,SPLITP_num_toString]);

val TOKENS_tostring = Q.prove(
`TOKENS (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") (toString(n:num)) = [toString n]`,
  Cases_on `toString n` >> fs[TOKENS_def]
  >-
   (pop_assum mp_tac
    >> fs[ASCIInumbersTheory.num_to_dec_string_def]
    >> fs[ASCIInumbersTheory.n2s_def]
    >> PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >> rw[])
  >> qpat_x_assum `_ = STRING _ _` (assume_tac o GSYM) >> fs[]
  >> pairarg_tac >> pop_assum (assume_tac o GSYM)
  >> fs[SPLITP_num_toString,TOKENS_def]
  >> qpat_x_assum `STRING _ _ = _` (assume_tac o GSYM) >> fs[]);

val num_le_10 = Q.prove(
  `!n. 0 ≤ n /\ n < 10 ==> Num n < 10`,
  Cases >> fs[]);

val tokens_toString = Q.prove(
`tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") (toString(n:int)) = [toString n]`,
  fs[Once toString_def] >> fs[TOKENS_eq_tokens_sym]
  >> fs[implode_def,tokens_aux_def,toChar_def,str_def,strlen_def,maxSmall_DEC_def,toChars_thm]
  >> every_case_tac >> fs[explode_thm,TOKENS_def]
  >> TRY(pairarg_tac >> first_x_assum (assume_tac o GSYM)) >> fs[SPLITP] >> rfs[]
  >> fs[SPLITP_num_toString,TOKENS_def,TOKENS_tostring]
  >> TRY(fs[Once toString_def] >> fs[implode_def,tokens_def,tokens_aux_def,toChar_def,str_def,maxSmall_DEC_def,toChars_thm])
  >> fs[GSYM integerTheory.INT_NOT_LT]
  >> fs[integerTheory.INT_NOT_LT]
  >> qpat_assum `0 <= n`
      (fn thm => thm |> REWRITE_RULE[GSYM integerTheory.INT_ABS_EQ_ID] |> assume_tac)
  >> drule num_le_10 >> fs[]);

val tokens_strcat = Q.prove(
`l ≠ [] ==>
(tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
                                   (toString n ^
                                    strlit (STRING (acd l r) "") ^ toString m ^ strlit "\n")
 = [toString n; toString m])`,
  Cases_on `l` >> Cases_on `r` >> fs[acd_def] >>
  fs[tokens_append_strlit,strcat_assoc,tokens_append_right,tokens_toString]);

val tokens_strcat' = Q.prove(
`r ≠ [] ==>
(tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
                                   (toString n ^
                                    strlit (STRING (acd l r) "") ^ toString m ^ strlit "\n")
 = [toString n; toString m])`,
  Cases_on `l` >> Cases_on `r` >> fs[acd_def] >>
  fs[tokens_append_strlit,strcat_assoc,tokens_append_right,tokens_toString]);

val strsub_strcat =
    Q.prove(`!s s'. strsub(s ^ s') (strlen s) = strsub s' 0`,
    Induct >> fs[strcat_thm,implode_def,strsub_def,EL_APPEND_EQN]
    >> Induct >> fs[explode_thm]);

val strsub_nil =
    Q.prove(`!s c. strsub(strlit (STRING c "") ^ s) 0 = c`,
    Induct >> fs[strcat_thm,implode_def,strsub_def]);

val strlen_append =
    Q.prove(`!s s'. strlen(s ^ s') = strlen s + strlen s'`,
    Induct >> strip_tac >> Induct >> strip_tac >> fs[strcat_thm,implode_def]);

val acd_simps =
    Q.prove(`l ≠ [] ==> (acd [] l = #"a" /\ acd l [] = #"d")`,
    Cases_on `l` >> fs[acd_def])

val acd_more_simps =
    Q.prove(`l ≠ [] /\ r ≠ [] ==> (acd l r = #"c")`,
    Cases_on `l` >> Cases_on `r` >> fs[acd_def])

val HEX_isDigit = Q.prove(`!n. n < 10 ==> isDigit(HEX n)`,
  recInduct one_to_ten >> fs[isDigit_def]);

(* TODO: move at least these (and probably others in this file) *)
val toString_isDigit = Q.store_thm("toString_isDigit",
  `!n. EVERY isDigit (toString(n:num))`,
  recInduct COMPLETE_INDUCTION
  >> rpt strip_tac
  >> fs[ASCIInumbersTheory.num_to_dec_string_def]
  >> fs[ASCIInumbersTheory.n2s_def]
  >> PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def]
  >> rw[] >> fs[HEX_isDigit]);

val num_to_dec_string_not_nil = Q.store_thm("num_to_dec_string_not_nil",
  `num_to_dec_string n ≠ []`,
  rw[ASCIInumbersTheory.num_to_dec_string_def]
  \\ rw[ASCIInumbersTheory.n2s_def]
  \\ qspecl_then[`10`,`n`]mp_tac numposrepTheory.LENGTH_n2l
  \\ simp[] \\ rw[] \\ strip_tac \\ fs[]);
(* -- *)

(*`!n. explode (toString n) = toString n`*)
val int_abs_toString_num = Q.store_thm("int_abs_toString_num",
`!n. toString (&n) = toString n`,
  recInduct COMPLETE_INDUCTION >> strip_tac
  >> fs[integer_wordTheory.toString_def]);

val num_from_string_toString_cancel = Q.store_thm("num_from_string_toString_cancel",
  `!n. num_from_string (toString (&n)) = n`,
  rw[num_from_string_def]
  \\ rw[toString_thm]
  \\ rw[implode_def]
  \\ qmatch_goalsub_abbrev_tac`strlit ss`
  \\ `HD ss ≠ #"~" ∧ EVERY isDigit ss`
  by (
    qspec_then`Num(ABS(&n))`mp_tac toString_isDigit
    \\ simp[Abbr`ss`]
    \\ Cases_on`num_to_dec_string (Num(ABS(&n)))` \\ simp[]
    >- fs[num_to_dec_string_not_nil]
    \\ rpt strip_tac \\ fs[]
    \\ qhdtm_x_assum`isDigit`mp_tac \\ EVAL_TAC )
  \\ rw[fromString_unsafe_thm,Abbr`ss`]
  \\ rw[ASCIInumbersTheory.toString_toNum_cancel]
  \\ rw[integerTheory.INT_ABS_NUM]);

val strong_substring_thm = Q.store_thm (
  "strong_substring_thm",
 `!s i j. (i <= strlen s) ==> (substring s i j = implode (SEG (MIN (strlen s - i) j) i (explode s)))`,
  rpt strip_tac
  >> Cases_on `i < strlen s`
  >- metis_tac[substring_thm]
  >> `i = strlen s` by fs[]
  >> fs[] >> rw[substring_def,SEG]);

val substring_adhoc_simps = Q.prove(`!h.
   (substring (strlit "> " ^ h) 0 2 = strlit "> ")
/\ (substring (strlit "> " ^ h) 2 (strlen h) = h)
/\ (substring (strlit "< " ^ h) 0 2 = strlit "< ")
/\ (substring (strlit "< " ^ h) 2 (strlen h) = h)
`,
  Induct >> rpt strip_tac >> fs[strcat_thm,implode_def,strong_substring_thm,strlen_def]
  >> fs[ADD1,MIN_DEF] >> fs[SEG_compute] >> simp_tac pure_ss [ONE,TWO,SEG_SUC_CONS]
  >> fs[SEG_LENGTH_ID])

val depatch_lines_strcat_cancel = Q.prove(
  `!r. depatch_lines (MAP (strcat (strlit "> ")) r) = SOME r`,
  Induct >> fs[depatch_lines_def,depatch_line_def,strlen_append,substring_adhoc_simps])

val depatch_lines_diff_add_prefix_cancel = Q.store_thm("depatch_lines_diff_add_prefix_cancel",
  `!l. depatch_lines (diff_add_prefix l (strlit "> ")) = SOME l`,
  fs[diff_add_prefix_def,depatch_lines_strcat_cancel]);

val patch_aux_nil = Q.prove(`patch_aux [] file remfl n = SOME file`,fs[patch_aux_def]);

val line_numbers_not_empty = Q.prove(
  `!l n . line_numbers l n <> strlit ""`,
  fs[line_numbers_def,toString_def,str_def,implode_def,maxSmall_DEC_def,strcat_thm] >>
  rw[] >> fs[] >> rw[Once toChars_def]
  >> PURE_ONCE_REWRITE_TAC[simple_toChars_def] >> rw[Once zero_pad_def,padLen_DEC_def]
  >> fs[integerTheory.INT_ABS_NUM]
  >> fs[Once(GSYM simple_toChars_acc),Once(GSYM zero_pad_acc),Once(GSYM toChars_acc)]);

val tokens_toString_comma =
    Q.prove(`tokens ($= #",") (toString n) = [toString n]`,
  fs[TOKENS_eq_tokens_sym,toString_thm,explode_implode]
  >> fs[implode_def]
  >> `EVERY isDigit (toString (Num (ABS n)))` by metis_tac[toString_isDigit]
  >> `toString(Num(ABS n)) <> []` by metis_tac[num_to_dec_string_not_nil]
  >> qpat_abbrev_tac `a = toString(Num _)` >> pop_assum kall_tac
  >> `!x. isDigit x ==> (λx. (¬(($= #",") x))) x` by fs[isDigit_def]
  >> drule EVERY_MONOTONIC
  >> strip_tac >> first_x_assum drule >> strip_tac >> drule SPLITP_EVERY
  >> strip_tac >> fs[] >> rw[]
  >- (fs[TOKENS_def] >> pairarg_tac >> pop_assum (assume_tac o GSYM) >> fs[SPLITP,TOKENS_def])
  >> Cases_on `a` >> fs[TOKENS_def])

val tokens_comma_lemma = Q.prove(
  `tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
     (line_numbers l n) = [line_numbers l n]`,
  `EVERY (λx. isDigit x \/ x = #",") (explode(line_numbers l n))`
  by(fs[line_numbers_def] >> rw[]
     >> fs[toString_thm,int_abs_toString_num]
     >> fs[explode_implode,strcat_thm,integerTheory.INT_ABS_NUM]
     >> `!x. isDigit x ==> (\x. isDigit x \/ x = #",") x` by fs[]
     >> drule EVERY_MONOTONIC
     >> strip_tac
     >> qspec_then `&n` assume_tac toString_isDigit
     >> first_assum drule >> fs[]
     >> qspec_then `n + LENGTH l` assume_tac toString_isDigit
     >> first_assum drule >> fs[])
  >> `!x. (\x. isDigit x \/ x = #",") x ==> ($~ ∘ (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")) x` by fs[isDigit_def,GSYM ORD_11]
  >> drule EVERY_MONOTONIC >> strip_tac
  >> first_x_assum drule >> rpt(pop_assum kall_tac) >> strip_tac
  >> qspecl_then [`l`,`n`] assume_tac line_numbers_not_empty
  >> qpat_abbrev_tac `a = line_numbers _ _` >> pop_assum kall_tac
  >> qpat_abbrev_tac `p = (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")` >> pop_assum kall_tac
  >> Induct_on `a` >> rpt strip_tac
  >> fs[explode_thm,TOKENS_eq_tokens_sym,implode_def]
  >> Cases_on `s` >> rpt strip_tac >> fs[TOKENS_def] >> pairarg_tac
  >> pop_assum (assume_tac o GSYM)
  >> fs[SPLITP,isDigit_def,TOKENS_def]
  >> rfs[]
  >> `T ==> (t = t /\ EVERY ($~ ∘ p) t)` by fs[]
  >> pop_assum mp_tac
  >> PURE_REWRITE_TAC [GSYM SPLITP_NIL_SND_EVERY]
  >> fs[TOKENS_def]);

val string_is_num_toString = Q.store_thm("string_is_num_toString",
  `string_is_num (toString (&n))`,
  fs[string_is_num_def,toString_isDigit,int_abs_toString_num,
     toString_thm,num_from_string_toString_cancel,explode_implode]);

val parse_header_cancel = Q.store_thm("parse_header_cancel",
`l <> [] \/ l' <> [] ==>
 (parse_patch_header(diff_single_header l n l' n') =
  SOME(n,if LENGTH l <= 1 then NONE else SOME(n+LENGTH l),
       if l = [] then #"a" else if l' = [] then #"d" else #"c",
       n',if LENGTH l' <= 1 then NONE else SOME(n'+LENGTH l')))`,
  Cases_on `l` >> Cases_on `l'`
  >> fs[diff_single_header_def]
  >> fs[parse_patch_header_def]
  >> rw[]
  >> fs[patch_aux_def,parse_patch_header_def,acd_def,implode_def,tokens_append,tokens_strcat,
       tokens_strcat',GSYM strcat_assoc,tokens_toString_comma,tokens_append_strlit]
  >> fs[tokens_append_strlit,tokens_toString,tokens_append_right,tokens_toString_comma,acd_simps,
        acd_more_simps,strcat_assoc, strsub_strcat,strsub_nil,num_from_string_toString_cancel,
        tokens_comma_lemma]
  >> fs[line_numbers_def]
  >> fs[patch_aux_def,parse_patch_header_def,acd_def,implode_def,tokens_append,tokens_strcat,
        tokens_strcat',GSYM strcat_assoc,tokens_toString_comma,tokens_append_strlit]
  >> fs[tokens_append_strlit,tokens_toString,tokens_append_right,tokens_toString_comma,acd_simps,
        acd_more_simps,strcat_assoc, strsub_strcat,strsub_nil,num_from_string_toString_cancel,
        tokens_comma_lemma,string_is_num_toString]);

val patch_aux_cancel_base_case = Q.prove(
  `patch_aux (diff_with_lcs [] r n r' m) r (LENGTH r) n = SOME r'`,
  fs[diff_with_lcs_def,diff_single_def] >> rw[]
  >> fs[patch_aux_def]
  >> fs[patch_aux_def,parse_header_cancel,
         diff_add_prefix_def,depatch_lines_strcat_cancel,
         GSYM MAP_TAKE,GSYM MAP_DROP,DROP_APPEND,TAKE_APPEND]
  >> rw[]
  >> fs[DROP_LENGTH_TOO_LONG,TAKE_LENGTH_TOO_LONG,patch_aux_def,
        quantHeuristicsTheory.LIST_LENGTH_0,
        DROP_APPEND,depatch_lines_strcat_cancel]
  >> `LENGTH r = 1` by (Cases_on `LENGTH r` >> fs[])
  >> fs[depatch_lines_strcat_cancel]);

val SPLITP_NIL_FST = Q.store_thm("SPLITP_NIL_FST",
  `∀ls P r. SPLITP P ls = ([],r) ⇔ (r = ls ∧ ((ls <> []) ==> P(HD ls)))`,
  Cases >> rpt strip_tac >> fs[SPLITP,EQ_IMP_THM] >> IF_CASES_TAC
  >> strip_tac >> fs[]);

val diff_add_prefix_length = Q.store_thm("diff_add_prefix_length",
`!l s. LENGTH (diff_add_prefix l s) = LENGTH l`,
fs[diff_add_prefix_def]);

val diff_add_prefix_TAKE = Q.store_thm("diff_add_prefix_TAKE",
  `!l n s. TAKE n (diff_add_prefix l s) = diff_add_prefix (TAKE n l) s`,
  fs[diff_add_prefix_def,MAP_TAKE]);

val diff_add_prefix_DROP = Q.store_thm("diff_add_prefix_DROP",
  `!l n s. DROP n (diff_add_prefix l s) = diff_add_prefix (DROP n l) s`,
  fs[diff_add_prefix_def,MAP_DROP]);

val diff_add_prefix_nil = Q.store_thm("diff_add_prefix_nil",
  `!l n s. (diff_add_prefix [] s) = []`,
  fs[diff_add_prefix_def]);

val ONE_MINUS_SUCC = Q.prove(`1 - SUC x = 0`,intLib.COOPER_TAC);

val SUCC_LE_ONE = Q.prove(`(SUC n ≤ 1) = (n = 0)`,intLib.COOPER_TAC);

val patch_aux_keep_init = Q.prove(
`!l p t n t' n h t m.
 lcs l t t' ==>
 patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) (p ++ t) (LENGTH t + LENGTH p) n
 =
 case patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) t (LENGTH t) (n+LENGTH p) of
   SOME r => SOME(p++r)
 | NONE => NONE`,
  Induct_on `l` >> rpt strip_tac
  >- (fs[patch_aux_cancel_base_case]
      >> fs[diff_with_lcs_def,diff_single_def,diff_add_prefix_def] >> rw[]
      >> fs[patch_aux_def,parse_header_cancel] >> rw[]
      >> fs[quantHeuristicsTheory.LIST_LENGTH_0,GSYM MAP_TAKE,GSYM MAP_DROP,
            depatch_lines_strcat_cancel,DROP_LENGTH_NIL,DROP_LENGTH_TOO_LONG,
            TAKE_LENGTH_TOO_LONG,patch_aux_nil,DROP_APPEND,TAKE_APPEND,
            ONE_MINUS_SUCC]
      >> Cases_on `t` >> fs[ONE_MINUS_SUCC])
  >> fs[diff_with_lcs_def]
  >> rpt(pairarg_tac>>fs[]) >> rw[]
  >- (fs[SPLITP_NIL_FST] >> rveq
      >> Cases_on `lr` >> fs[lcs_empty']
      >> Cases_on `l'r` >> fs[lcs_empty']
      >> rveq >> first_assum(qspecl_then [`p++[h]`,`t'`,`n`,`t`,`n`] mp_tac)
      >> first_x_assum(qspecl_then [`[h]`,`t'`,`n+LENGTH p`,`t`,`n+LENGTH p`] mp_tac)
      >> fs[cons_lcs_optimal_substructure]
      >> full_simp_tac pure_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
      >> rpt strip_tac >> fs[] >> TOP_CASE_TAC)
  >> Cases_on `ll` >> Cases_on `l'l`
  >> fs[diff_single_def,patch_aux_def,parse_header_cancel,SPLITP_NIL_FST]
  >> rveq >> fs[]
  >> IF_CASES_TAC >> fs[]
  >> rw[]
  >> fs[TAKE_APPEND,DROP_APPEND,diff_add_prefix_length,diff_add_prefix_TAKE,
        depatch_lines_diff_add_prefix_cancel,ONE_MINUS_SUCC,SUCC_LE_ONE,
        quantHeuristicsTheory.LIST_LENGTH_0,diff_add_prefix_DROP,diff_add_prefix_nil,
        DROP_LENGTH_NIL,DROP_LENGTH_TOO_LONG]
  >> TOP_CASE_TAC >> fs[]);

val patch_aux_keep_init_cons = Q.prove(
  `!l t n t' n h t m.
   lcs l t t' ==>
   patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) (h::t) (SUC (LENGTH t)) n
   =
   case patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) t (LENGTH t) (n+1) of
     SOME r => SOME(h::r)
    | NONE => NONE`,
    rpt strip_tac >> drule patch_aux_keep_init
    >> disch_then (qspecl_then [`[h]`,`n`,`m`] assume_tac) >> fs[ADD1]);

val list_nil_sub_length = Q.prove(`l ≠ [] ==> (1 - LENGTH l = 0)`,
  Cases_on `l` >> fs[])

val list_length_1_lemma = Q.prove(`l ≠ [] /\ LENGTH l <= 1 ==> LENGTH l = 1`,
  Cases_on `LENGTH l` >> fs[])

val minus_add_too_large = Q.prove(`a - ((a:num) + n) = 0`,intLib.COOPER_TAC);

val minus_add_too_large' = Q.prove(`(a + 1) - ((a:num) + 2) = 0`,intLib.COOPER_TAC);

val patch_aux_diff_cancel = Q.store_thm("patch_aux_diff_cancel",
`!l r n r' m z.
lcs l r r' ==>
(patch_aux (diff_with_lcs l r n r' m) r (LENGTH r) n = SOME r')`,
Induct
>> rpt strip_tac
>-fs[patch_aux_cancel_base_case]
>> fs[diff_with_lcs_def,diff_single_def,
      diff_add_prefix_def,num_from_string_def]
>> rpt(pairarg_tac >> fs[])
>> rw[]
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[lcs_empty']
    >> Cases_on `l'r` >> fs[lcs_empty']
    >> rveq >> fs[cons_lcs_optimal_substructure,patch_aux_keep_init_cons])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[lcs_empty']
    >> Cases_on `l'r` >> fs[lcs_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_lcs_optimal_substructure,patch_aux_keep_init_cons]
    >> drule lcs_split_lcs2
    >> fs[SPLITP_EVERY,o_DEF,lcs_empty',SPLITP]
    >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_lcs_optimal_substructure]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[] >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
                  depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND]
    >> drule patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n`,`h`,`m + LENGTH l'l`] assume_tac)
    >> drule SPLITP_JOIN
    >> fs[])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[lcs_empty']
    >> Cases_on `l'r` >> fs[lcs_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_lcs_optimal_substructure,patch_aux_keep_init_cons]
    >> drule lcs_split_lcs
    >> fs[SPLITP_EVERY,o_DEF,lcs_empty',SPLITP]
    >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_lcs_optimal_substructure]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[]
    >> drule SPLITP_JOIN >> strip_tac >> fs[]
    >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
          depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND,list_length_1_lemma,
          minus_add_too_large]
    >> drule patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n + LENGTH ll`,`h`,`m`] mp_tac)
    >> fs[list_length_1_lemma,ADD1])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[lcs_empty']
    >> Cases_on `l'r` >> fs[lcs_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_lcs_optimal_substructure,patch_aux_keep_init_cons]
    >> drule lcs_split_lcs >> strip_tac >> drule lcs_split_lcs2
    >> fs[SPLITP_EVERY,o_DEF,lcs_empty',SPLITP]
    >> drule SPLITP_IMP >> qpat_x_assum `SPLITP _ _ = _ ` mp_tac
    >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_lcs_optimal_substructure]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[]
    >> drule SPLITP_JOIN >> qpat_x_assum `SPLITP _ _ = _` mp_tac
    >> drule SPLITP_JOIN >> ntac 3 strip_tac
    >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
          depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND,list_length_1_lemma,
          minus_add_too_large,TAKE_APPEND,minus_add_too_large',ONE_MINUS_SUCC]
    >> drule patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n + LENGTH ll`,`h`,`m + LENGTH l'l`] mp_tac)
    >> fs[ADD1,list_length_1_lemma]));

val patch_diff_cancel = Q.store_thm("patch_diff_cancel",
  `patch_alg (diff_alg l r) l = SOME r`,
  fs[patch_alg_def,diff_alg_def]
  >> mp_tac (GEN_ALL (INST_TYPE [alpha|->``:mlstring``] optimised_lcs_correct))
  >> disch_then (qspecl_then [`r`,`l`] assume_tac)
  >> fs[patch_aux_diff_cancel]);

(* TODO:
   this property is false as stated; prove some appropriate weakening
val diff_patch_cancel = Q.store_thm("diff_patch_cancel",
  `patch_alg patch l = SOME r ==> diff_alg l r = patch`,
  cheat);
 *)

(* The diff is optimal, in the sense that the number of line changes it
   reports is precisely the number of deviations from the lcs of the
   files. *)

val is_patch_line_def = Define `
  is_patch_line s =
  if strlen s > 1 then
    if substring s 0 2 = strlit "> " then
      T
    else substring s 0 2 = strlit "< "
  else
      F`

val is_patch_line_simps = Q.prove(
  `!r. (FILTER is_patch_line (MAP (strcat (strlit "> ")) r) = (MAP (strcat (strlit "> ")) r))
       /\ (FILTER is_patch_line (MAP (strcat (strlit "< ")) r) = MAP (strcat (strlit "< ")) r)
`,
  Induct_on `r` >> fs[] >> Induct
  >> fs[is_patch_line_def,strlen_def,strcat_thm,implode_def,substring_thm,MIN_DEF]
  >> simp_tac pure_ss [ONE,TWO,SEG] >> fs[]);

val toString_obtain_digits = Q.prove(
  `!n. ?f r. toString (&n) = strlit(f::r) /\ isDigit f /\ EVERY isDigit r`,
  strip_tac >> fs[toString_thm,integerTheory.INT_ABS_NUM,implode_def]
  >> qspec_then `n` assume_tac toString_isDigit
  >> qspec_then `n` assume_tac (GEN_ALL num_to_dec_string_not_nil)
  >> Cases_on `toString n` >> fs[]);

val diff_single_patch_length = Q.prove(
  `!r n r' m. LENGTH (FILTER is_patch_line (diff_single r n r' m)) = LENGTH r + LENGTH r'`,
  rpt strip_tac
  >> fs[diff_single_def,diff_single_header_def,is_patch_line_def,line_numbers_def,
        diff_add_prefix_def,is_patch_line_simps]
  >> qspec_then `n` assume_tac toString_obtain_digits
  >> qspec_then `m` assume_tac toString_obtain_digits
  >> fs[] >> rw[]
  >> fs[is_patch_line_simps,substring_thm,strcat_thm,implode_def,explode_thm,MIN_DEF, isDigit_def]
  >> rfs[] >> full_simp_tac pure_ss [ONE,TWO,SEG] >> fs[FILTER_APPEND,is_patch_line_simps]
  >> fs[is_patch_line_def,substring_thm,implode_def] >> full_simp_tac pure_ss [ONE,TWO,SEG]
  >> fs[]);

val diff_with_lcs_optimal = Q.prove(
  `!l r r' n m. lcs l r r' ==>
    LENGTH(FILTER is_patch_line (diff_with_lcs l r n r' m)) = LENGTH r + LENGTH r' - (2*LENGTH l)`,
  Induct >> fs[diff_with_lcs_def] >> rw[] >> fs[diff_single_patch_length]
  >> ntac 2 (pairarg_tac >> fs[]) >> rw[]
  >> fs[SPLITP_NIL_FST,FILTER_APPEND,diff_single_patch_length] >> rveq
  >- (Cases_on `lr` >> Cases_on `l'r` >> fs[lcs_empty']
      >> rveq >> fs[cons_lcs_optimal_substructure])
  >> drule lcs_split_lcs >> strip_tac >> drule lcs_split_lcs2 >> strip_tac
  >> Cases_on `lr` >> Cases_on `l'r` >> rfs[lcs_empty']
  >> drule SPLITP_IMP
  >> qpat_x_assum `SPLITP _ _ = _` mp_tac >> drule SPLITP_IMP
  >> ntac 3 strip_tac >> fs[] >> rveq
  >> drule SPLITP_JOIN >> qpat_x_assum `SPLITP _ _ = _` mp_tac >> drule SPLITP_IMP
  >> drule SPLITP_JOIN >> rpt strip_tac
  >> fs[cons_lcs_optimal_substructure,MULT_SUC,SUB_LEFT_ADD]
  >> rw[] >> rpt (qpat_x_assum `lcs (_::_) _ _` kall_tac)
  >> drule lcs_max_length >> fs[]);

val diff_optimal = Q.store_thm("diff_optimal",
  `!l r r'. lcs l r r' ==>
   LENGTH(FILTER is_patch_line (diff_alg r r')) = LENGTH r + LENGTH r' - (2*LENGTH l)`,
  rpt strip_tac >> fs[diff_alg_def]
  >> `lcs (optimised_lcs r r') r r'` by(metis_tac[optimised_lcs_correct])
  >> `LENGTH l = LENGTH (optimised_lcs r r')`
       by(fs[lcs_def,common_subsequence_def,is_subsequence_def] >> metis_tac[is_subsequence_length,LESS_EQUAL_ANTISYM])
  >> fs[diff_with_lcs_optimal]);

val _ = export_theory ();
