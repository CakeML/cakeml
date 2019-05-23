(*
   Implementation and verification of diff and patch algorithms
*)

open preamble lcsTheory mlintTheory mlstringTheory;

val _ = new_theory "diff";

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

(* Diff algorithm definition *)

val line_numbers_def = Define `
  (line_numbers l n =
   if LENGTH l <= 1 then
     toString (n:num)
   else
      strcat (toString n) (strcat(implode ",") (toString (n+LENGTH l))))`

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

val diff_alg_offs_def = Define `
  diff_alg_offs l n l' n' = diff_with_lcs (dynamic_lcs l l') l n l' n'`

val diff_alg2_def = Define `
  diff_alg2 l l' =
    let prefix_length = LENGTH(longest_common_prefix l l');
        l = DROP prefix_length l;
        l' = DROP prefix_length l';
        llength = LENGTH l;
        l'length = LENGTH l';
        suffix_length = if llength = l'length then
                          longest_common_suffix_length l l' 0
                        else if llength < l'length then
                          longest_common_suffix_length l (DROP (l'length-llength) l') 0
                        else
                          longest_common_suffix_length (DROP (llength-l'length) l) l' 0;
        l = TAKE (llength - suffix_length) l;
        l' = TAKE (l'length - suffix_length) l'
    in
      diff_with_lcs (dynamic_lcs l l') l prefix_length l' prefix_length`

Theorem diff_alg2_thm:
    diff_alg2 l l' =
    let prefix_length = LENGTH(longest_common_prefix l l');
        l = DROP prefix_length l;
        l' = DROP prefix_length l';
        llength = LENGTH l;
        l'length = LENGTH l';
        suffix_length = LENGTH(longest_common_suffix l l');
        l = TAKE (llength - suffix_length) l;
        l' = TAKE (l'length - suffix_length) l'
    in
      diff_with_lcs (dynamic_lcs l l') l prefix_length l' prefix_length
Proof
  PURE_ONCE_REWRITE_TAC [diff_alg2_def]
  >> ntac 5 (PURE_ONCE_REWRITE_TAC [LET_THM])
  >> ntac 5 (Ho_Rewrite.PURE_ONCE_REWRITE_TAC [BETA_THM])
  >> PURE_ONCE_REWRITE_TAC [longest_common_suffix_length_if]
  >> REFL_TAC
QED

(* Diff algorithm properties *)

Theorem diff_with_lcs_refl:
   !n n'. diff_with_lcs l l n l n' = []
Proof
  Induct_on `l` >> rw[diff_with_lcs_def,SPLITP]
QED

Theorem diff_alg_refl:
   diff_alg l l = []
Proof
  rw[diff_alg_def,lcs_refl',diff_with_lcs_refl,optimised_lcs_refl]
QED

Theorem diff_alg2_refl:
   diff_alg2 l l = []
Proof
  rw[diff_alg2_thm,lcs_refl',diff_with_lcs_refl,dynamic_lcs_refl,
     longest_common_prefix_refl]
QED

(* Patch algorithm definition *)

val parse_patch_header_def = Define `
    parse_patch_header s =
    case tokens (\x. x = #"a" \/ x = #"d" \/ x = #"c" \/ x = #"\n") s of
      | [l;r] =>
        (case tokens ($= #",") l of
           | [ll;lr] =>
             (case (fromNatString ll, fromNatString lr) of
              | (SOME lln, SOME lrn) =>
              (case tokens ($= #",") r of
                | [rl;rr] =>
                  (case (fromNatString rl, fromNatString rr) of
                  | (SOME rln, SOME rrn) =>
                      SOME (lln,SOME(lrn),strsub s (strlen l),
                            rln,SOME(rrn))
                  | _ => NONE)
                | [r] =>
                  (case fromNatString r of
                  | SOME rn =>
                      SOME (lln,SOME(lrn),strsub s (strlen l),rn,NONE)
                  | _ => NONE)
                | _ => NONE)
             | _ => NONE)
           | [l'] =>
             (case fromNatString l' of
              | (SOME l'n) =>
                (case tokens ($= #",") r of
                | [rl;rr] =>
                  (case (fromNatString rl, fromNatString rr) of
                   | (SOME rln, SOME rrn) =>
                       SOME (l'n,NONE,strsub s (strlen l),rln,SOME(rrn))
                   | _ => NONE)
                | [r] =>
                  (case fromNatString r of
                   | (SOME rn) =>
                      SOME (l'n,NONE,strsub s (strlen l),rn,NONE)
                   | _ => NONE)
                | _ => NONE)
              | _ => NONE)
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

val patch_alg_offs_def = Define `
  patch_alg_offs n patch file = patch_aux patch file (LENGTH file) n`

(* Patch cancels diff *)

Theorem string_concat_empty:
 !s. s ^ strlit "" = s /\ strlit "" ^ s = s
Proof
fs[strcat_thm,implode_explode]
QED

Theorem tokens_append_strlit:
   ∀P s1 x s2.
   P x ⇒ tokens P (s1 ^ strlit [x] ^ s2) = tokens P s1 ++ tokens P s2
Proof
  rpt strip_tac >> drule0 tokens_append >> fs[str_def,implode_def]
QED

Theorem tokens_append_right_strlit:
   ∀P s x.
   P x ⇒ tokens P (s ^ strlit [x]) = tokens P s
Proof
  rpt strip_tac >> drule0 tokens_append_strlit
  >> disch_then (qspecl_then [`s`,`strlit ""`] assume_tac)
  >> fs[string_concat_empty,tokens_def,tokens_aux_def]
QED

val zero_pad_acc = Q.prove(
`!n acc. STRCAT (zero_pad n "") acc = (zero_pad n acc)`,
  Induct >> PURE_ONCE_REWRITE_TAC [zero_pad_def] >- fs[]
  >> strip_tac >> first_assum(qspec_then `STRING #"0" acc` (assume_tac o GSYM))
  >> fs[]);

val simple_toChars_acc = Q.prove(
`!n m acc. STRCAT (simple_toChars m n "") acc = (simple_toChars m n acc)`,
  recInduct COMPLETE_INDUCTION >> rpt strip_tac >> fs[]
  >> PURE_ONCE_REWRITE_TAC[simple_toChars_def]
  >> rw[] >> PURE_ONCE_REWRITE_TAC[GSYM zero_pad_acc]
  >> fs[] >> first_x_assum (qspec_then `n DIV 10` assume_tac) >> rfs[]
  >> first_assum (qspecl_then [`m - 1`,`(STRING (toChar (n MOD 10)) acc)`] (assume_tac o GSYM))
  >> fs[]);

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

Theorem one_to_ten:
   !P. P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\ (!n. (n:num) >= 10 ==> P n) ==> !n. P n
Proof
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
  >> Cases_on `n` >> fs[]
QED

val SPLITP_HEX = Q.prove(
`!n. n < 10 ==> SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
     (STRING (HEX n) acc) =
     let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
       (STRING (HEX n) l,r)`,
  recInduct one_to_ten >> rpt strip_tac >> fs[] >> pairarg_tac >> fs[SPLITP]);

val _ = temp_overload_on("ml_num_toString",``mlint$num_to_str``);
val _ = temp_overload_on("hol_int_toString",``integer_word$toString``);
val _ = temp_overload_on("num_toString",``num_to_dec_string``);

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
  Cases_on `num_toString n` >> fs[TOKENS_def]
  >> qpat_x_assum `_ = STRING _ _` (assume_tac o GSYM) >> fs[]
  >> pairarg_tac >> pop_assum (assume_tac o GSYM)
  >> fs[SPLITP_num_toString,TOKENS_def]
  >> qpat_x_assum `STRING _ _ = _` (assume_tac o GSYM) >> fs[]);

val num_le_10 = Q.prove(
  `!n. 0 ≤ n /\ n < 10 ==> Num n < 10`,
  Cases >> fs[]);

val tokens_toString = Q.prove(
`tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") (toString (n:num)) = [toString n]`,
  fs[Once toString_def,num_to_str_def] >> fs[TOKENS_eq_tokens_sym]
  >> fs[implode_def,tokens_aux_def,toChar_def,str_def,strlen_def,maxSmall_DEC_def,toChars_thm]
  >> every_case_tac >> fs[explode_thm,TOKENS_def]
  >> TRY(pairarg_tac >> first_x_assum (assume_tac o GSYM)) >> fs[SPLITP] >> rfs[]
  >> fs[SPLITP_num_toString,TOKENS_def,TOKENS_tostring]
  >> TRY(fs[Once toString_def,num_to_str_def]
         \\ fs[implode_def,tokens_def,tokens_aux_def
              , toChar_def,str_def,maxSmall_DEC_def,toChars_thm]));

val tokens_strcat = Q.prove(
`l ≠ [] ==>
(tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
                                   (toString (n:num) ^
                                    strlit (STRING (acd l r) "") ^ toString (m:num) ^ strlit "\n")
 = [toString n; toString m])`,
  Cases_on `l` >> Cases_on `r` >> fs[acd_def] >>
  fs[tokens_append_strlit,strcat_assoc,tokens_append_right_strlit,tokens_toString]);

val tokens_strcat' = Q.prove(
`r ≠ [] ==>
(tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
                                   (toString (n:num) ^
                                    strlit (STRING (acd l r) "") ^ toString (m:num) ^ strlit "\n")
 = [toString n; toString m])`,
  Cases_on `l` >> Cases_on `r` >> fs[acd_def] >>
  fs[tokens_append_strlit,strcat_assoc,tokens_append_right_strlit,tokens_toString]);

val strsub_strcat =
    Q.prove(`!s s'. strsub(s ^ s') n = if n < strlen s then strsub s n else strsub s' (n - strlen s)`,
    Induct >> simp[strcat_thm,implode_def,strsub_def,EL_APPEND_EQN]
    \\ gen_tac \\ Cases \\ simp[]);

Theorem strsub_str:
   strsub (str c) 0 = c
Proof
  rw[str_def,implode_def,strsub_def]
QED

val acd_simps =
    Q.prove(`l ≠ [] ==> (acd [] l = #"a" /\ acd l [] = #"d")`,
    Cases_on `l` >> fs[acd_def])

val acd_more_simps =
    Q.prove(`l ≠ [] /\ r ≠ [] ==> (acd l r = #"c")`,
    Cases_on `l` >> Cases_on `r` >> fs[acd_def])

val HEX_isDigit = Q.prove(`!n. n < 10 ==> isDigit(HEX n)`,
  recInduct one_to_ten >> fs[isDigit_def]);

(* TODO: move at least these (and probably others in this file) *)
Theorem toString_isDigit:
   !n. EVERY isDigit (toString(n:num))
Proof
  recInduct COMPLETE_INDUCTION
  >> rpt strip_tac
  >> fs[ASCIInumbersTheory.num_to_dec_string_def]
  >> fs[ASCIInumbersTheory.n2s_def]
  >> PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def]
  >> rw[] >> fs[HEX_isDigit]
QED
(* -- *)

(*`!n. explode (toString n) = toString n`*)
Theorem int_abs_toString_num:
 !n. toString (&n) = toString n
Proof
  recInduct COMPLETE_INDUCTION >> strip_tac
  >> fs[integer_wordTheory.toString_def]
QED

val substring_adhoc_simps = Q.prove(`!h.
   (substring (strlit "> " ^ h) 0 2 = strlit "> ")
/\ (substring (strlit "> " ^ h) 2 (strlen h) = h)
/\ (substring (strlit "< " ^ h) 0 2 = strlit "< ")
/\ (substring (strlit "< " ^ h) 2 (strlen h) = h)
`,
  Induct >> rpt strip_tac >> fs[strcat_thm,implode_def,substring_def,strlen_def]
  >> fs[ADD1,MIN_DEF] >> fs[SEG_compute] >> simp_tac pure_ss [ONE,TWO,SEG_SUC_CONS]
  >> fs[SEG_LENGTH_ID])

val depatch_lines_strcat_cancel = Q.prove(
  `!r. depatch_lines (MAP (strcat (strlit "> ")) r) = SOME r`,
  Induct >> fs[depatch_lines_def,depatch_line_def,strlen_strcat,substring_adhoc_simps])

Theorem depatch_lines_diff_add_prefix_cancel:
   depatch_lines (diff_add_prefix l (strlit "> ")) = SOME l
Proof
  fs[diff_add_prefix_def,depatch_lines_strcat_cancel]
QED

val patch_aux_nil = Q.prove(`patch_aux [] file remfl n = SOME file`,fs[patch_aux_def]);

val line_numbers_not_empty = Q.prove(
  `!l n . line_numbers l n <> strlit ""`,
  fs[line_numbers_def,toString_def,num_to_str_def
    , str_def,implode_def,maxSmall_DEC_def,strcat_thm] >>
  rw[] >> fs[] >> rw[Once toChars_def]
  >> PURE_ONCE_REWRITE_TAC[simple_toChars_def] >> rw[Once zero_pad_def,padLen_DEC_def]
  >> fs[Once(GSYM simple_toChars_acc),Once(GSYM zero_pad_acc),Once(GSYM toChars_acc)]);

Theorem tokens_eq_sing:
   !s f. EVERY ($~ o f) (explode s) /\ s <> strlit "" ==> tokens f s = [s]
Proof
  Cases
  \\ fs[TOKENS_eq_tokens_sym,toString_thm,explode_implode,implode_def]
  \\ Cases_on `s'` \\ fs [TOKENS_def] \\ rw []
  \\ fs [o_DEF,SPLITP_EVERY,TOKENS_def]
QED

val tokens_toString_comma =
    Q.prove(`tokens ($= #",") (toString (n:num)) = [toString n]`,
  rw [] \\ match_mp_tac tokens_eq_sing
  \\ fs [num_to_str_thm,implode_def]
  \\ fs [num_to_str_def]
  \\ match_mp_tac (MP_CANON EVERY_MONOTONIC)
  \\ qexists_tac `isDigit`
  \\ fs [EVERY_isDigit_num_to_dec_string] \\ EVAL_TAC);

val tokens_comma_lemma = Q.prove(
  `tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
     (line_numbers l n) = [line_numbers l n]`,
  `EVERY (λx. isDigit x \/ x = #",") (explode(line_numbers l n))`
  by(fs[line_numbers_def] >> rw[]
     \\ fs[toString_thm,num_to_str_def]
     \\ fs[explode_implode,strcat_thm]
     \\ match_mp_tac (MP_CANON EVERY_MONOTONIC)
     \\ qexists_tac `isDigit` \\ fs [toString_isDigit])
  \\ match_mp_tac tokens_eq_sing
  \\ conj_tac THEN1
   (match_mp_tac (MP_CANON EVERY_MONOTONIC)
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [] \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs [isDigit_def])
  \\ rw [line_numbers_def,num_to_str_thm,implode_def]
  \\ fs [strcat_def,concat_def]);

Theorem parse_header_cancel:
 l <> [] \/ l' <> [] ==>
 (parse_patch_header(diff_single_header l n l' n') =
  SOME(n,if LENGTH l <= 1 then NONE else SOME(n+LENGTH l),
       if l = [] then #"a" else if l' = [] then #"d" else #"c",
       n',if LENGTH l' <= 1 then NONE else SOME(n'+LENGTH l')))
Proof
  rw[diff_single_header_def,parse_patch_header_def,
     option_case_eq,list_case_eq,PULL_EXISTS,
     strsub_strcat,tokens_append_right_strlit,GSYM str_def,
     tokens_append,acd_simps,acd_more_simps,tokens_comma_lemma,
     tokens_comma_lemma]
  \\ rw[line_numbers_def,tokens_toString_comma,
        fromNatString_toString,
        GSYM str_def,tokens_append,strsub_str]
QED

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

Theorem SPLITP_NIL_FST:
   ∀ls P r. SPLITP P ls = ([],r) ⇔ (r = ls ∧ ((ls <> []) ==> P(HD ls)))
Proof
  Cases >> rpt strip_tac >> fs[SPLITP,EQ_IMP_THM] >> IF_CASES_TAC
  >> strip_tac >> fs[]
QED

Theorem diff_add_prefix_length:
 !l s. LENGTH (diff_add_prefix l s) = LENGTH l
Proof
fs[diff_add_prefix_def]
QED

Theorem diff_add_prefix_TAKE:
   !l n s. TAKE n (diff_add_prefix l s) = diff_add_prefix (TAKE n l) s
Proof
  fs[diff_add_prefix_def,MAP_TAKE]
QED

Theorem diff_add_prefix_DROP:
   !l n s. DROP n (diff_add_prefix l s) = diff_add_prefix (DROP n l) s
Proof
  fs[diff_add_prefix_def,MAP_DROP]
QED

Theorem diff_add_prefix_nil:
   !s. (diff_add_prefix [] s) = []
Proof
  fs[diff_add_prefix_def]
QED

val ONE_MINUS_SUCC = Q.prove(`1 - SUC x = 0`,intLib.COOPER_TAC);

val SUCC_LE_ONE = Q.prove(`(SUC n ≤ 1) = (n = 0)`,intLib.COOPER_TAC);

val patch_aux_keep_init = Q.prove(
`!l p t n t' m.
 common_subsequence l t t' ==>
 patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) (p ++ t) (LENGTH t + LENGTH p) n
 =
 case patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) t (LENGTH t) (n+LENGTH p) of
   SOME r => SOME(p++r)
 | NONE => NONE`,
  Induct >> rpt strip_tac
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
      >> Cases_on `lr` >> fs[common_subsequence_empty']
      >> Cases_on `l'r` >> fs[common_subsequence_empty']
      >> rveq >> first_assum(qspecl_then [`p++[h]`,`t`,`n`,`t'`,`n`] mp_tac)
      >> first_x_assum(qspecl_then [`[h]`,`t`,`n+LENGTH p`,`t'`,`n+LENGTH p`] mp_tac)
      >> fs[cons_common_subsequence]
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

val patch_aux_keep_init_cons = Q.prove(`
   !l t n t' h m.
   common_subsequence l t t' ==>
   patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) (h::t) (SUC (LENGTH t)) n
   =
   case patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) t (LENGTH t) (n+1) of
     SOME r => SOME(h::r)
    | NONE => NONE`,
    rpt strip_tac >> drule0 patch_aux_keep_init
    >> disch_then (qspecl_then [`[h]`,`n`,`m`] assume_tac) >> fs[ADD1]);

val list_nil_sub_length = Q.prove(`l ≠ [] ==> (1 - LENGTH l = 0)`,
  Cases_on `l` >> fs[])

val list_length_1_lemma = Q.prove(`l ≠ [] /\ LENGTH l <= 1 ==> LENGTH l = 1`,
  Cases_on `LENGTH l` >> fs[])

val minus_add_too_large = Q.prove(`a - ((a:num) + n) = 0`,intLib.COOPER_TAC);

val minus_add_too_large' = Q.prove(`(a + 1) - ((a:num) + 2) = 0`,intLib.COOPER_TAC);

Theorem patch_aux_diff_cancel:
 !l r n r' m.
common_subsequence l r r' ==>
(patch_aux (diff_with_lcs l r n r' m) r (LENGTH r) n = SOME r')
Proof
Induct
>> rpt strip_tac
>-fs[patch_aux_cancel_base_case]
>> fs[diff_with_lcs_def,diff_single_def,
      diff_add_prefix_def]
>> rpt(pairarg_tac >> fs[])
>> rw[]
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[common_subsequence_empty']
    >> Cases_on `l'r` >> fs[common_subsequence_empty']
    >> rveq >> fs[cons_common_subsequence,patch_aux_keep_init_cons])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[common_subsequence_empty']
    >> Cases_on `l'r` >> fs[common_subsequence_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_common_subsequence,patch_aux_keep_init_cons]
    >> drule0 common_subsequence_split_css2
    >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
    >> drule0 SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[] >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
                  depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND]
    >> drule0 patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n`,`h`,`m + LENGTH l'l`] assume_tac)
    >> drule0 SPLITP_JOIN
    >> fs[])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[common_subsequence_empty']
    >> Cases_on `l'r` >> fs[common_subsequence_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_common_subsequence,patch_aux_keep_init_cons]
    >> drule0 common_subsequence_split_css
    >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
    >> drule0 SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[]
    >> drule0 SPLITP_JOIN >> strip_tac >> fs[]
    >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
          depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND,list_length_1_lemma,
          minus_add_too_large]
    >> drule0 patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n + LENGTH ll`,`h`,`m`] mp_tac)
    >> fs[list_length_1_lemma,ADD1])
>- (fs[SPLITP_NIL_FST] >> rveq
    >> Cases_on `lr` >> fs[common_subsequence_empty']
    >> Cases_on `l'r` >> fs[common_subsequence_empty',SPLITP_NIL_SND_EVERY]
    >> rveq
    >> fs[cons_common_subsequence,patch_aux_keep_init_cons]
    >> drule0 common_subsequence_split_css >> strip_tac >> drule0 common_subsequence_split_css2
    >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
    >> drule0 SPLITP_IMP >> qpat_x_assum `SPLITP _ _ = _ ` mp_tac
    >> drule0 SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
    >> fs[patch_aux_def] >> rw[]
    >> fs[parse_header_cancel,TAKE_APPEND]
    >> rw[]
    >> drule0 SPLITP_JOIN >> qpat_x_assum `SPLITP _ _ = _` mp_tac
    >> drule0 SPLITP_JOIN >> ntac 3 strip_tac
    >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
          depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND,list_length_1_lemma,
          minus_add_too_large,TAKE_APPEND,minus_add_too_large',ONE_MINUS_SUCC]
    >> drule0 patch_aux_keep_init_cons
    >> disch_then(qspecl_then [`n + LENGTH ll`,`h`,`m + LENGTH l'l`] mp_tac)
    >> fs[ADD1,list_length_1_lemma])
QED

Theorem patch_diff_cancel:
   patch_alg (diff_alg l r) l = SOME r
Proof
  fs[patch_alg_def,diff_alg_def]
  >> mp_tac (GEN_ALL (INST_TYPE [alpha|->``:mlstring``] optimised_lcs_correct))
  >> disch_then (qspecl_then [`r`,`l`] assume_tac)
  >> fs[patch_aux_diff_cancel,lcs_def]
QED

val headers_within_def = Define `
  headers_within n m l =
    EVERY (OPTION_ALL (λ(n':num,m':num option,c,_,_).
      (n <= n' /\ n' <= m /\ (IS_NONE m' /\ (c = #"d" \/ c = #"c") ==>
       n'+1 <= m) /\
      (IS_SOME m' ==> (n <= THE m' /\ THE m' <= m)))))
         (MAP parse_patch_header l)`

Theorem headers_within_IMP:
   headers_within n m (h::t) /\ parse_patch_header h = SOME(q,NONE,c,tup)
     ==> n <= q /\ q <= m /\ ((c= #"d" \/ c = #"c") ==> q+1 <= m)
Proof
  rpt strip_tac >> fs[headers_within_def] >> rfs[pairTheory.ELIM_UNCURRY]
QED

Theorem headers_within_IMP_SOME:
   headers_within n m (h::t) /\ parse_patch_header h = SOME(q,SOME q',c,tup)
     ==> n <= q /\ q <= m /\ n <= q' /\ q' <= m
Proof
  rpt strip_tac >> fs[headers_within_def] >> rfs[pairTheory.ELIM_UNCURRY]
QED

Theorem headers_within_grow:
   headers_within n' m' l /\ n <= n' /\ m' <= m ==> headers_within n m l
Proof
  Induct_on `l` >> rpt strip_tac >> fs[headers_within_def]
  >> Cases_on `parse_patch_header h` >> fs[pairTheory.ELIM_UNCURRY]
  >> rw[] >> fs[]
QED

Theorem headers_within_append:
   headers_within n m (l++l') = (headers_within n m l /\ headers_within n m l')
Proof
  simp[headers_within_def]
QED

Theorem headers_within_dest_cons:
   headers_within n m (e::l') ==> headers_within n m l'
Proof
  simp[headers_within_def]
QED

(* todo: move to richlist? *)
Theorem EVERY_DROP_T:
   !P l m. EVERY P l ==> EVERY P (DROP m l)
Proof
  Induct_on `l` >> rw[DROP_def]
QED

Theorem headers_within_drop:
   headers_within n m (l) ==> headers_within n m (DROP x l)
Proof
  simp[headers_within_def,MAP_DROP,EVERY_DROP_T]
QED

Theorem fromString_gt:
   fromString (implode (STRING #">" x)) = NONE /\
   fromString (implode (STRING #"<" x)) = NONE
Proof
  rw [] \\ match_mp_tac fromString_EQ_NONE \\ EVAL_TAC
QED

Theorem fromNatString_gt:
   fromNatString (implode (STRING #">" x)) = NONE /\
   fromNatString (implode (STRING #"<" x)) = NONE
Proof
  rw [fromNatString_def,fromString_gt]
QED

val parse_nonheader_lemma = Q.prove(
  `!f r. EVERY (OPTION_ALL f) (MAP parse_patch_header (diff_add_prefix r (strlit "> ")))`,
  strip_tac >> Induct
  >- fs[diff_add_prefix_def]
  >> strip_tac >> Cases_on `h`
  >> fs[parse_patch_header_def,diff_add_prefix_def]
  >> every_case_tac
  >> fs[strcat_def,mlstringTheory.concat_def]
  >> fs[tokens_append_strlit,TOKENS_eq_tokens_sym]
  >> fs[TOKENS_def,pairTheory.ELIM_UNCURRY,SPLITP] >> rveq
  >> fs[explode_implode,TOKENS_def,SPLITP,pairTheory.ELIM_UNCURRY]
  >> rveq
  >> fs[explode_implode,isDigit_def,fromNatString_gt]);

val parse_nonheader_lemma2 = Q.prove(
  `!f r. EVERY (OPTION_ALL f) (MAP parse_patch_header (diff_add_prefix r (strlit "< ")))`,
  strip_tac >> Induct
  >- fs[diff_add_prefix_def]
  >> strip_tac >> Cases_on `h`
  >> fs[parse_patch_header_def,diff_add_prefix_def]
  >> every_case_tac
  >> fs[strcat_def,mlstringTheory.concat_def]
  >> fs[tokens_append_strlit,TOKENS_eq_tokens_sym]
  >> fs[TOKENS_def,pairTheory.ELIM_UNCURRY,SPLITP] >> rveq
  >> fs[explode_implode,TOKENS_def,SPLITP,pairTheory.ELIM_UNCURRY]
  >> rveq
  >> fs[explode_implode,isDigit_def,fromNatString_gt]);

val parse_nonheader_lemma3 = Q.prove(
  `parse_patch_header (strlit "---\n") = NONE`,
  fs[parse_patch_header_def]
  >> every_case_tac
  >> fs[strcat_def,mlstringTheory.concat_def]
  >> fs[tokens_append_strlit,TOKENS_eq_tokens_sym]
  >> fs[TOKENS_def,pairTheory.ELIM_UNCURRY,SPLITP] >> rveq);

Theorem diff_with_lcs_headers_within:
   !l r n r' m. common_subsequence l r r' ==>
    headers_within n (n + LENGTH r) (diff_with_lcs l r n r' m)
Proof
  Induct
  >> rpt strip_tac
  >- (fs[diff_with_lcs_def,headers_within_def,diff_single_def]
      >> rw[] >> fs[parse_header_cancel]
      >> rw[]
      >> TRY(MATCH_ACCEPT_TAC parse_nonheader_lemma)
      >> TRY(MATCH_ACCEPT_TAC parse_nonheader_lemma2)
      >> fs[parse_nonheader_lemma3]
      >> Cases_on `r` >> fs[])
  >> fs[diff_with_lcs_def]
  >> rpt(pairarg_tac >> fs[])
  >> IF_CASES_TAC
  >- (drule0 split_common_subsequence
      >> strip_tac
      >> first_x_assum drule0 >> fs[]
      >> disch_then(qspecl_then [`n+1`,`n+1`] assume_tac)
      >> drule0(GEN_ALL headers_within_grow)
      >> disch_then match_mp_tac
      >> fs[SPLITP_NIL_FST]
      >> Cases_on `r` >> fs[common_subsequence_empty'])
  >> simp[headers_within_append]
  >> strip_tac
  >- (fs[headers_within_def,diff_single_def]
      >> fs[parse_header_cancel]
      >> rw[]
      >> Q.ISPECL_THEN [`($= h)`,`r`] assume_tac (GEN_ALL (GSYM SPLITP_LENGTH))
      >> fs[]
      >> TRY(MATCH_ACCEPT_TAC parse_nonheader_lemma)
      >> TRY(MATCH_ACCEPT_TAC parse_nonheader_lemma2)
      >> fs[parse_nonheader_lemma3] >> rfs[]
      >> drule0 common_subsequence_split >> strip_tac >> fs[] >> rveq >> fs[])
  >> drule0 split_common_subsequence
  >> drule0 common_subsequence_split
  >> drule0 common_subsequence_split2
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[] >> rfs[] >> first_x_assum drule0
  >> disch_then(qspecl_then [`n + (LENGTH ll + 1)`,`m + (LENGTH l'l + 1)`] assume_tac)
  >> drule0(GEN_ALL headers_within_grow)
  >> disch_then match_mp_tac
  >> Q.ISPECL_THEN [`($= h)`,`r`] assume_tac (GEN_ALL (GSYM SPLITP_LENGTH))
  >> fs[]
QED

val highly_specific_implication = Q.prove(
  `¬(q < n + 1) /\ ¬(m < q − n) ==> n + (SUC m) - (q + 1) = (n + m - q)`,
  fs[]);

val highly_specific_implication2 = Q.prove(
  `¬(SUC m < (q+1) − n) ==> n + (SUC m) - (q + 1) = (n + m - q)`,
  fs[]);

Theorem headers_within_cons:
 headers_within (n+1) m p1 /\ m >= n+1 ==>
  patch_alg_offs n p1 (e::l) = OPTION_MAP (CONS e) (patch_alg_offs (n+1) p1 l)
Proof
  Cases_on `p1` >> rpt strip_tac
  >> fs[patch_alg_offs_def,patch_aux_def]
  >> every_case_tac
  >> fs[headers_within_def] >> rfs[]
  >> TRY(drule0(GEN_ALL highly_specific_implication) >> disch_then drule0 >> disch_then (fn x => fs[x]))
  >> TRY(drule0(GEN_ALL highly_specific_implication2) >> disch_then (fn x => fs[x]))
  >> fs[GSYM ADD1]
QED

val IS_SUFFIX_induct_aux =
  Q.prove(`!P l. P [] /\ (!h l. (!sl. IS_SUFFIX l sl ==> P sl) ==> P (h::l)) ==> (!sl. IS_SUFFIX l sl ==> P sl)`,
  strip_tac >> Induct_on `l`
  >> rpt strip_tac
  >> fs[]
  >- (qspec_then `sl` assume_tac SNOC_CASES >> fs[] >> fs[IS_SUFFIX_compute,REVERSE_APPEND])
  >> Cases_on `sl` >> fs[IS_SUFFIX]
  >> Cases_on `IS_SUFFIX l (h'::t)` >> fs[]
  >> fs[IS_SUFFIX_compute]
  >> fs[] >> fs[IS_SUFFIX_compute,REVERSE_APPEND]
  >> FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND, IS_PREFIX_SNOC]
  >> fs[])

Theorem IS_SUFFIX_induct:
   !P. P [] /\ (!h l. (!sl. IS_SUFFIX l sl ==> P sl) ==> P (h::l)) ==> !l. P l
Proof
  metis_tac[IS_SUFFIX_induct_aux,IS_SUFFIX_REFL]
QED

Theorem IS_SUFFIX_DROP:
   !l n. IS_SUFFIX l (DROP n l)
Proof
  Induct >> rpt strip_tac >> rw[DROP_def]
  >> metis_tac[IS_SUFFIX_CONS]
QED

Theorem headers_within_snoc:
 !p1 n l m e. headers_within m (n + LENGTH l) p1 /\ m <= (n + LENGTH l) ==>
  patch_alg_offs n p1 (SNOC e l) = OPTION_MAP (SNOC e) (patch_alg_offs n p1 l)
Proof
  ho_match_mp_tac IS_SUFFIX_induct
  >> rpt strip_tac
  >> fs[patch_alg_offs_def,patch_aux_def]
  >> every_case_tac >> fs[] >> rfs[]
  >> fs[DROP_DROP_T]
  >> TRY(qmatch_goalsub_abbrev_tac `F`
         >> qmatch_asmsub_abbrev_tac `patch_aux (DROP a1 _) _ _ a2`
         >> `IS_SUFFIX p1 (DROP a1 p1)`
               by(MATCH_ACCEPT_TAC IS_SUFFIX_DROP)
         >> first_assum drule0
         >> qunabbrev_tac `a1`
         >> disch_then(qspecl_then [`a2`,`DROP (a2 - n) l`,`m`,`e`] mp_tac)
         >> impl_tac
         >- (qunabbrev_tac `a2`
             >> match_mp_tac(GEN_ALL headers_within_grow)
             >> MAP_EVERY qexists_tac [`m`,`n + LENGTH l`]
             >> fs[]
             >> match_mp_tac headers_within_drop
             >> imp_res_tac headers_within_dest_cons)
         >> fs[]
         >> FULL_SIMP_TAC bool_ss [NOT_LESS, GSYM DROP_SNOC,LE]
         >> fs[ADD1]
         >> fs[SNOC_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG]
         >> rfs[DROP_LENGTH_TOO_LONG]
         >> fs[DROP_def] >> imp_res_tac headers_within_IMP >> fs[]
         >> qunabbrev_tac `a2` >> fs[]
         >> qmatch_asmsub_abbrev_tac `patch_aux _ _ _ a2`
         >> (first_assum drule0
             >> disch_then(qspecl_then [`a2`,`[]`,`m`,`e`] mp_tac)
             >> impl_tac
             >- (match_mp_tac(GEN_ALL headers_within_grow)
                 >> MAP_EVERY qexists_tac [`m`,`n+LENGTH l`]
                 >> qunabbrev_tac `a2` >> fs[]
                 >> match_mp_tac headers_within_drop
                 >> imp_res_tac headers_within_dest_cons)
             >> TRY(
                 `(n + (LENGTH l + 1) − a2) = 0` by(intLib.COOPER_TAC)
                 >> pop_assum(fn x => fs[x])
                 >> `(n + LENGTH l - a2) = 0` by(intLib.COOPER_TAC)
                 >> pop_assum(fn x => fs[x]) >> rveq >> fs[]
                 >> (first_assum drule0
                     >> disch_then(qspecl_then [`a2`,`[]`,`m`,`e`] mp_tac)
                     >> impl_tac
                     >- (match_mp_tac(GEN_ALL headers_within_grow)
                                     >> MAP_EVERY qexists_tac [`m`,`n+LENGTH l`]
                                     >> qunabbrev_tac `a2` >> fs[]
                                     >> match_mp_tac headers_within_drop
                                     >> imp_res_tac headers_within_dest_cons)
                     >> impl_tac >> fs[]
                     >> rpt strip_tac >> fs[]
                     >> imp_res_tac headers_within_IMP_SOME >> fs[] >> NO_TAC))
             >> `n + LENGTH l - a2 = 0` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])
             >> qunabbrev_tac `a2`
             >> `n + LENGTH l - q = 0` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])
             >> imp_res_tac headers_within_IMP >> fs[]
             >> `n + (LENGTH l + 1) - q = 1` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])
             >> imp_res_tac headers_within_IMP
             >> `q - (n + LENGTH l) = 0` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])))
  >> TRY(qmatch_goalsub_abbrev_tac `F`
         >> qmatch_asmsub_abbrev_tac `DROP 1 _`
         >> `IS_SUFFIX p1 (DROP 1 p1)`
               by(MATCH_ACCEPT_TAC IS_SUFFIX_DROP)
         >> first_assum drule0
         >> disch_then(qspecl_then [`q`,`DROP (q - n) l`,`m`,`e`] mp_tac)
         >> impl_tac
         >- (match_mp_tac(GEN_ALL headers_within_grow)
             >> MAP_EVERY qexists_tac [`m`,`n + LENGTH l`]
             >> fs[]
             >> match_mp_tac headers_within_drop
             >> imp_res_tac headers_within_dest_cons)
         >> fs[]
         >> FULL_SIMP_TAC bool_ss [NOT_LESS, GSYM DROP_SNOC,LE]
         >> fs[ADD1]
         >> fs[SNOC_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG]
         >> rfs[DROP_LENGTH_TOO_LONG]
         >> imp_res_tac headers_within_IMP
         >> `q = n + LENGTH l - 1` by intLib.COOPER_TAC
         >> rveq >> fs[]
         >> (first_assum drule0
             >> disch_then(qspecl_then [`q`,`[]`,`m`,`e`] mp_tac)
             >> impl_tac
             >- (match_mp_tac(GEN_ALL headers_within_grow)
                 >> MAP_EVERY qexists_tac [`m`,`n+LENGTH l`]
                 >> fs[]
                 >> match_mp_tac headers_within_drop
                 >> imp_res_tac headers_within_dest_cons)
             >> `n + LENGTH l - (q + 1) = 0` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])
             >> `n + LENGTH l - q = 0` by(intLib.COOPER_TAC)
             >> pop_assum (fn x => fs[x])
             >> imp_res_tac headers_within_IMP >> fs[]))
  >> TRY((qmatch_goalsub_abbrev_tac `TAKE (q − n) (l ⧺ [e]) ⧺ a1 ⧺ a2 = TAKE (q − n) l ⧺ a1 ⧺ a3 ⧺ [e]`
          ORELSE qmatch_goalsub_abbrev_tac `TAKE (q − n) (l ⧺ [e]) ⧺ a1 = TAKE (q − n) l ⧺ a2 ⧺ [e]`)
         >> qmatch_asmsub_abbrev_tac `patch_aux (DROP a4 _) _ _ a5 = _`
         >> imp_res_tac headers_within_IMP >> fs[]
         >> `a5 - n <= LENGTH l` by(unabbrev_all_tac >> intLib.COOPER_TAC)
         >> drule0 TAKE_SNOC
         >> simp[SNOC_APPEND]
         >> disch_then kall_tac
         >> `IS_SUFFIX p1 (DROP a4 p1)` by(MATCH_ACCEPT_TAC IS_SUFFIX_DROP)
         >> first_assum drule0
         >> qunabbrev_tac `a4`
         >> disch_then(qspecl_then [`a5`,`DROP (a5 - n) l`,`m`,`e`] mp_tac)
         >> impl_tac
         >- (qunabbrev_tac `a5`
             >> match_mp_tac (GEN_ALL headers_within_grow)
             >> MAP_EVERY qexists_tac [`m`,`n+LENGTH l`]
             >> fs[]
             >> match_mp_tac headers_within_drop
             >> imp_res_tac headers_within_dest_cons)
         >> fs[ADD1]
         >> `a5 - n <= LENGTH l` by(unabbrev_all_tac >> intLib.COOPER_TAC)
         >> simp[GSYM DROP_SNOC]
         >> qunabbrev_tac `a5`
         >> `q - n <= LENGTH l` by intLib.COOPER_TAC
         >> simp[TAKE_APPEND,SNOC_APPEND,DROP_APPEND]
         >> simp[DROP_def]
         >> fs[SNOC_APPEND,DROP_APPEND,DROP_def] >> NO_TAC)
QED

Theorem headers_within_append1:
 !l' l. headers_within (n+LENGTH l') m p1 /\ m >= n+LENGTH l' ==>
  patch_alg_offs n p1 (l' ++ l) = OPTION_MAP (APPEND l') (patch_alg_offs (n+LENGTH l') p1 l)
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> rpt strip_tac
  >- (fs[] >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ a1` >> Cases_on `a1` >> fs[])
  >> rpt strip_tac
  >> fs[SNOC_APPEND]
  >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  >> drule0(GEN_ALL headers_within_grow)
  >> disch_then(qspecl_then[`n + LENGTH l'`,`m`] assume_tac)
  >> `!opt. OPTION_MAP ($++ (l' ⧺ [x])) opt = OPTION_MAP ($++ l') (OPTION_MAP (CONS x) opt)`
       by(Cases >> fs[])
  >> fs[ADD1]
  >> FULL_SIMP_TAC std_ss [ADD_ASSOC]
  >> pop_assum kall_tac
  >> drule0(GEN_ALL headers_within_cons)
  >> fs[]
QED

Theorem headers_within_append1':
 !l' l. headers_within (LENGTH l) m p1 /\ m >= LENGTH l+LENGTH l' ==>
  patch_alg p1 (l ++ l') = OPTION_MAP (APPEND l) (patch_alg_offs (LENGTH l) p1 l')
Proof
  rpt strip_tac
  >> assume_tac (GEN_ALL headers_within_append1)
  >> pop_assum (qspecl_then [`p1`,`0`,`m`,`l`,`l'`] assume_tac)
  >> fs[patch_alg_def,patch_alg_offs_def]
QED

Theorem headers_within_append2:
 !l' l. headers_within m (n + LENGTH l) p1 /\ m <= n+LENGTH l ==>
  patch_alg_offs n p1 (l ++ l') = OPTION_MAP (combin$C APPEND l') (patch_alg_offs n p1 l)
Proof
  Induct
  >> rpt strip_tac
  >- (fs[] >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ a1` >> Cases_on `a1` >> fs[])
  >> SIMP_TAC bool_ss [Once CONS_APPEND,APPEND_ASSOC]
  >> drule0(GEN_ALL headers_within_grow)
  >> disch_then(qspecl_then[`m`,`n + LENGTH(l ++ [h])`] mp_tac)
  >> impl_tac >> fs[]
  >> strip_tac >> first_x_assum drule0
  >> fs[]
  >> `!opt. OPTION_MAP (combin$C $++ (h::l')) opt = OPTION_MAP (combin$C $++ l') (OPTION_MAP (SNOC h) opt)`
       by(Cases >> fs[] )
       >> fs[ADD1]
  >> pop_assum kall_tac
  >> FULL_SIMP_TAC std_ss [ADD_ASSOC]
  >> fs[GSYM SNOC_APPEND]
  >> drule0(GEN_ALL headers_within_snoc)
  >> fs[]
QED

Theorem longest_common_sandwich:
   !l r. l = longest_common_prefix l r ++
            let l' = DROP (LENGTH(longest_common_prefix l r)) l;
                r' = DROP (LENGTH(longest_common_prefix l r)) r in
              TAKE (LENGTH l' - LENGTH(longest_common_suffix l' r')) l' ++ longest_common_suffix l' r'
Proof
  rpt strip_tac >> fs[]
  >> qspecl_then [`l`,`r`] assume_tac longest_prefix_is_prefix
  >> fs[]
  >> imp_res_tac IS_PREFIX_APPEND
  >> qpat_abbrev_tac `a1 = longest_common_prefix l r`
  >> fs[DROP_APPEND,DROP_LENGTH_NIL]
  >> qspecl_then [`l''`,`l'`] assume_tac longest_suffix_is_suffix
  >> fs[]
  >> imp_res_tac IS_SUFFIX_APPEND
  >> qpat_abbrev_tac `a2 = longest_common_suffix _ _ `
  >> fs[TAKE_APPEND]
QED

Theorem LENGTH_suffix_prefix:
   !l r. LENGTH l >= LENGTH (longest_common_prefix l r)
        + LENGTH
           (longest_common_suffix
            (DROP (LENGTH (longest_common_prefix l r)) l)
            (DROP (LENGTH (longest_common_prefix l r)) r))
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [Once longest_common_sandwich]
  >> rw[SUB_RIGHT_ADD,SUB_LEFT_ADD]
QED

Theorem longest_common_sandwich':
   !l r. r = longest_common_prefix l r ++
            let l' = DROP (LENGTH(longest_common_prefix l r)) l;
                r' = DROP (LENGTH(longest_common_prefix l r)) r in
              TAKE (LENGTH r' - LENGTH(longest_common_suffix l' r')) r' ++ longest_common_suffix l' r'
Proof
  rpt strip_tac >> fs[]
  >> qspecl_then [`l`,`r`] assume_tac longest_prefix_is_prefix
  >> fs[]
  >> imp_res_tac IS_PREFIX_APPEND
  >> qpat_abbrev_tac `a1 = longest_common_prefix l r`
  >> fs[DROP_APPEND,DROP_LENGTH_NIL]
  >> qspecl_then [`l''`,`l'`] assume_tac longest_suffix_is_suffix
  >> fs[]
  >> imp_res_tac IS_SUFFIX_APPEND
  >> qpat_abbrev_tac `a2 = longest_common_suffix _ _ `
  >> fs[TAKE_APPEND]
QED

Theorem LENGTH_suffix_prefix':
   !l r. LENGTH r >= LENGTH (longest_common_prefix l r)
        + LENGTH
           (longest_common_suffix
            (DROP (LENGTH (longest_common_prefix l r)) l)
            (DROP (LENGTH (longest_common_prefix l r)) r))
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [Once longest_common_sandwich']
  >> rw[SUB_RIGHT_ADD,SUB_LEFT_ADD]
QED

Theorem patch_diff2_cancel:
   patch_alg (diff_alg2 l r) l = SOME r
Proof
  fs[diff_alg2_thm]
  >> fs[patch_aux_def]
  >> qmatch_goalsub_abbrev_tac `TAKE (LENGTH _ - (a1 + a2)) _`
  >> qpat_abbrev_tac `a3 = DROP a1 l`
  >> qpat_abbrev_tac `a4 = DROP a1 r`
  >> qpat_abbrev_tac `a5 = TAKE (LENGTH r − (a1 + a2)) a4`
  >> qmatch_goalsub_abbrev_tac `TAKE a6`
  >> fs[patch_alg_def]
  >> Q.ISPECL_THEN [`l`,`r`] assume_tac longest_common_sandwich
  >> pop_assum(fn x => PURE_ONCE_REWRITE_TAC [x])
  >> `lcs (dynamic_lcs (TAKE a6 a3) a5) (TAKE a6 a3) a5` by(MATCH_ACCEPT_TAC dynamic_lcs_correct)
  >> fs[lcs_def]
  >> imp_res_tac diff_with_lcs_headers_within
  >> pop_assum(qspecl_then [`a1`,`a1`] assume_tac)
  >> drule0(GEN_ALL headers_within_grow)
  >> disch_then(qspecl_then [`a1`,`a1 + (LENGTH a3 - a2 + a2)`] mp_tac)
  >> impl_tac >- (unabbrev_all_tac >> fs[])
  >> qunabbrev_tac `a1` >> strip_tac
  >> drule0 headers_within_append1'
  >> disch_then(qspec_then `TAKE (LENGTH a3 − a2) a3 ++ longest_common_suffix a3 a4` mp_tac)
  >> impl_tac >- (unabbrev_all_tac >> fs[])
  >> strip_tac
  >> fs[patch_alg_def]
  >> qunabbrev_tac `a2` >> fs[]
  >> qexists_tac `TAKE (LENGTH a4 − LENGTH (longest_common_suffix a3 a4)) a4 ⧺
                                longest_common_suffix a3 a4`
  >> fs[]
  >> conj_tac
  >- (ntac 2 (pop_assum kall_tac)
      >> drule0 (GEN_ALL(headers_within_append2 |> PURE_ONCE_REWRITE_RULE [ADD_SYM]))
      >> disch_then(qspec_then `longest_common_suffix a3 a4` mp_tac)
      >> impl_tac >- fs[]
      >> strip_tac
      >> `a6 = LENGTH a3 - LENGTH(longest_common_suffix a3 a4)`
           by(unabbrev_all_tac >> fs[])
       >> rveq >> fs[]
       >> drule0 patch_aux_diff_cancel
       >> fs[patch_alg_offs_def]
       >> disch_then kall_tac
       >> unabbrev_all_tac >> fs[])
  >> unabbrev_all_tac
  >> Q.ISPECL_THEN [`l`,`r`] mp_tac (longest_common_sandwich' |> SIMP_RULE std_ss [LET_THM])
  >> rpt(pop_assum kall_tac)
  >> fs[]
QED

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
  >> fs[is_patch_line_def,strlen_def,strcat_thm,implode_def,substring_def,MIN_DEF]
  >> simp_tac pure_ss [ONE,TWO,SEG] >> fs[]);

val toString_obtain_digits = Q.prove(
  `!n. ?f r. toString (n:num) = strlit(f::r) /\ isDigit f /\ EVERY isDigit r`,
  strip_tac >> fs[num_to_str_thm,implode_def]
  >> qspec_then `n` assume_tac toString_isDigit
  >> Cases_on `num_toString n` >> fs[]);

val diff_single_patch_length = Q.prove(
  `!r n r' m. LENGTH (FILTER is_patch_line (diff_single r n r' m)) = LENGTH r + LENGTH r'`,
  rpt strip_tac
  >> fs[diff_single_def,diff_single_header_def,is_patch_line_def,line_numbers_def,
        diff_add_prefix_def,is_patch_line_simps]
  >> qspec_then `n` assume_tac toString_obtain_digits
  >> qspec_then `m` assume_tac toString_obtain_digits
  >> fs[] >> rw[]
  >> fs[is_patch_line_simps,substring_def,strcat_thm,implode_def,explode_thm,MIN_DEF, isDigit_def]
  >> rfs[] >> full_simp_tac pure_ss [ONE,TWO,SEG] >> fs[FILTER_APPEND,is_patch_line_simps]
  >> fs[is_patch_line_def,substring_def,implode_def] >> full_simp_tac pure_ss [ONE,TWO,SEG]
  >> fs[]);

val diff_with_lcs_optimal = Q.prove(
  `!l r r' n m. lcs l r r' ==>
    LENGTH(FILTER is_patch_line (diff_with_lcs l r n r' m)) = LENGTH r + LENGTH r' - (2*LENGTH l)`,
  Induct >> fs[diff_with_lcs_def] >> rw[] >> fs[diff_single_patch_length]
  >> ntac 2 (pairarg_tac >> fs[]) >> rw[]
  >> fs[SPLITP_NIL_FST,FILTER_APPEND,diff_single_patch_length] >> rveq
  >- (Cases_on `lr` >> Cases_on `l'r` >> fs[lcs_empty']
      >> rveq >> fs[cons_lcs_optimal_substructure])
  >> drule0 lcs_split_lcs >> strip_tac >> drule0 lcs_split_lcs2 >> strip_tac
  >> Cases_on `lr` >> Cases_on `l'r` >> rfs[lcs_empty']
  >> drule0 SPLITP_IMP
  >> qpat_x_assum `SPLITP _ _ = _` mp_tac >> drule0 SPLITP_IMP
  >> ntac 3 strip_tac >> fs[] >> rveq
  >> drule0 SPLITP_JOIN >> qpat_x_assum `SPLITP _ _ = _` mp_tac >> drule0 SPLITP_IMP
  >> drule0 SPLITP_JOIN >> rpt strip_tac
  >> fs[cons_lcs_optimal_substructure,MULT_SUC,SUB_LEFT_ADD]
  >> rw[] >> rpt (qpat_x_assum `lcs (_::_) _ _` kall_tac)
  >> drule0 lcs_max_length >> fs[]);

Theorem diff_optimal:
   !l r r'. lcs l r r' ==>
   LENGTH(FILTER is_patch_line (diff_alg r r')) = LENGTH r + LENGTH r' - (2*LENGTH l)
Proof
  rpt strip_tac >> fs[diff_alg_def]
  >> `lcs (optimised_lcs r r') r r'` by(metis_tac[optimised_lcs_correct])
  >> `LENGTH l = LENGTH (optimised_lcs r r')`
       by(fs[lcs_def,common_subsequence_def,is_subsequence_def] >> metis_tac[is_subsequence_length,LESS_EQUAL_ANTISYM])
  >> fs[diff_with_lcs_optimal]
QED

Theorem REVERSE_DROP_REVERSE_TAKE:
   !l n. n <= LENGTH l ==>
  REVERSE((DROP n (REVERSE l))) = TAKE (LENGTH l - n) l
Proof
  Induct >> rpt strip_tac >> fs[DROP_def,DROP_APPEND] >> rw[]
  >> fs[ADD1,NOT_LEQ]
  >> imp_res_tac EQ_LESS_EQ >> fs[]
  >> fs[DROP_LENGTH_TOO_LONG]
QED

Theorem diff2_optimal:
   !l r r'. lcs l r r' ==>
   LENGTH(FILTER is_patch_line (diff_alg2 r r')) = LENGTH r + LENGTH r' - (2*LENGTH l)
Proof
  rpt strip_tac >> fs[diff_alg2_thm]
  >> qmatch_goalsub_abbrev_tac `longest_common_suffix a1 a2`
  >> qmatch_goalsub_abbrev_tac `dynamic_lcs a3 a4`
  >> `lcs (dynamic_lcs a3 a4) a3 a4` by(MATCH_ACCEPT_TAC dynamic_lcs_correct)
  >> `lcs (longest_common_prefix r r' ++ dynamic_lcs a3 a4 ++ longest_common_suffix a1 a2) r r'`
     by(FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,longest_prefix_correct,longest_suffix_correct]
        >> fs[REVERSE_DROP]
        >> `LENGTH (longest_common_suffix a1 a2) <= LENGTH a1`
            by(metis_tac[longest_common_suffix_LENGTH])
        >> `LENGTH (longest_common_suffix a1 a2) <= LENGTH a2`
            by(metis_tac[longest_common_suffix_LENGTH])
        >> simp[REVERSE_DROP_REVERSE_TAKE]
        >> unabbrev_all_tac >> simp[])
  >> `LENGTH l = LENGTH (longest_common_prefix r r' ++ dynamic_lcs a3 a4 ++ longest_common_suffix a1 a2)`
     by(match_mp_tac lcs_length >> metis_tac[])
  >> fs[diff_with_lcs_optimal]
  >> fs[LEFT_ADD_DISTRIB]
  >> `LENGTH a3 = LENGTH r - (LENGTH(longest_common_prefix r r') + LENGTH(longest_common_suffix a1 a2))`
       by(unabbrev_all_tac >> fs[])
  >> `LENGTH a4 = LENGTH r' - (LENGTH(longest_common_prefix r r') + LENGTH(longest_common_suffix a1 a2))`
      by(unabbrev_all_tac >> fs[])
  >> fs[]
  >> Q.ISPECL_THEN [`r`,`r'`] assume_tac longest_common_prefix_LENGTH
  >> Q.ISPECL_THEN [`a1`,`a2`] assume_tac longest_common_suffix_LENGTH
  >> rw[SUB_RIGHT_ADD]
  >> rw[SUB_LEFT_ADD]
  >> qpat_abbrev_tac `a5 = longest_common_prefix r r'`
  >> `LENGTH r' = LENGTH a5 + LENGTH a4 + LENGTH (longest_common_suffix a1 a2)`
     by (PURE_ONCE_REWRITE_TAC[Once longest_common_sandwich]
          >> simp[] >> unabbrev_all_tac >> fs[]
          >> rw[SUB_RIGHT_ADD,SUB_LEFT_ADD] >> fs[] >> rfs[]
          >> Q.ISPECL_THEN [`r'`,`r`] assume_tac LENGTH_suffix_prefix
          >> fs[])
  >> `LENGTH r = LENGTH a5 + LENGTH a3 + LENGTH (longest_common_suffix a1 a2)`
     by (PURE_ONCE_REWRITE_TAC[Once longest_common_sandwich']
          >> simp[] >> unabbrev_all_tac >> fs[]
          >> rw[SUB_RIGHT_ADD,SUB_LEFT_ADD] >> fs[] >> rfs[]
          >> Q.ISPECL_THEN [`l`,`r`] assume_tac LENGTH_suffix_prefix'
          >> fs[])
  >> pop_assum (fn x => PURE_ONCE_REWRITE_TAC[x])
  >> pop_assum (fn x => PURE_ONCE_REWRITE_TAC[x])
  >> fs[]
QED

val _ = export_theory ();
