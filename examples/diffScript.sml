(*
   Implementation and verification of diff and patch algorithms
*)
Theory diff
Ancestors
  lcs mlint mlstring
Libs
  preamble


val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = augment_srw_ss [rewrites [SNOC_APPEND]];

(* Diff algorithm definition *)

Definition line_numbers_def:
  line_numbers l n =
   if LENGTH l <= 1 then
     toString (n:num)
   else
      strcat (toString n) (strcat(implode ",") (toString (n+LENGTH l)))
End

Definition acd_def:
  acd [] [] = #" " ∧
  acd l [] = #"d" ∧
  acd [] l = #"a" ∧
  acd l l' = #"c"
End

Definition diff_single_header_def:
  diff_single_header l n l' n' =
  line_numbers l n ^ implode [acd l l'] ^ line_numbers l' n' ^ «\n»
End


Definition diff_add_prefix_def:
  diff_add_prefix l h = MAP (strcat h) l
End

Definition diff_single_def:
  diff_single l n l' n' =
    diff_single_header l n l' n'::
    if l = [] then (* add *)
      diff_add_prefix l' (strlit "> ")
    else if l' = [] then (* delete *)
      diff_add_prefix l (strlit "< ")
    else (* change *)
      diff_add_prefix l (strlit "< ")
      ++ (strlit "---\n")::diff_add_prefix l' (strlit "> ")
End

Definition diff_with_lcs_def:
  (diff_with_lcs [] l n l' n' =
      if l = [] /\ l' = [] then
        []
      else
        diff_single l n l' n') ∧
  (diff_with_lcs (f::r) l n l' n' =
      let (ll,lr) = SPLITP ($= f) l in
        let (l'l,l'r) = SPLITP ($= f) l' in
          if ll = [] /\ l'l = [] then
            diff_with_lcs r (TL lr) (n+1) (TL l'r) (n+1)
          else
            diff_single ll n l'l n' ++ diff_with_lcs r (TL lr) (n+LENGTH ll+1) (TL l'r) (n'+LENGTH l'l+1))
End

Definition diff_alg_def:
  diff_alg l l' = diff_with_lcs (optimised_lcs l l') l 0 l' 0
End

Definition diff_alg_offs_def:
  diff_alg_offs l n l' n' = diff_with_lcs (dynamic_lcs l l') l n l' n'
End

Definition diff_alg2_def:
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
      diff_with_lcs (dynamic_lcs l l') l prefix_length l' prefix_length
End

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

Triviality diff_with_lcs_refl:
   ∀n n'. diff_with_lcs l l n l n' = []
Proof
  Induct_on ‘l’ >> rw[diff_with_lcs_def,SPLITP]
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

Definition parse_patch_header_def:
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
      | _ => NONE
End

Definition depatch_line_def:
  depatch_line s =
  if strlen s > 1 then
    if substring s 0 2 = strlit "> " then
      SOME(substring s 2 (strlen s - 2))
    else
      NONE
  else
      NONE
End

Definition depatch_lines_def:
  depatch_lines [] = SOME [] ∧
  depatch_lines (s::r) =
   case depatch_line s of
       NONE => NONE
     | SOME s' =>
       case depatch_lines r of
           NONE => NONE
         | SOME r' => SOME(s'::r')
End

Definition patch_aux_def:
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
 )
Termination
  WF_REL_TAC `inv_image $< (LENGTH o FST)` >> fs[]
End

Definition patch_alg_def:
  patch_alg patch file = patch_aux patch file (LENGTH file) 0
End

Definition patch_alg_offs_def:
  patch_alg_offs n patch file = patch_aux patch file (LENGTH file) n
End

(* Patch cancels diff *)

Theorem tokens_append_strlit:
  ∀P s1 x s2. P x ⇒ tokens P (s1 ^ strlit [x] ^ s2) = tokens P s1 ++ tokens P s2
Proof
  rw[] >> drule tokens_append >> rw[str_def,implode_def]
QED

Theorem tokens_append_right_strlit:
  ∀NP s x. P x ⇒ tokens P (s ^ strlit [x]) = tokens P s
Proof
  rw[] >> drule tokens_append_strlit >>
  disch_then $ qspecl_then [`s`,`strlit ""`] mp_tac >>
  rw[tokens_def,tokens_aux_def]
QED

Triviality one_to_ten:
   ∀P. P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\ (∀n. (n:num) >= 10 ==> P n) ==> ∀n. P n
Proof
  ntac 2 strip_tac >>
  rpt(Cases >> simp[] >>
      (fn g as (hs,c) => ID_SPEC_TAC (hd $ free_vars c) g))
QED

Triviality SPLITP_HEX:
  ∀n. n < 10 ==> SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
                        (STRING (HEX n) acc) =
                 let (l,r) = SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") acc in
                   (STRING (HEX n) l,r)
Proof
  recInduct one_to_ten >> fs[ELIM_UNCURRY,SPLITP]
QED

Overload ml_num_toString[local] = ``mlint$num_to_str``
Overload hol_int_toString[local] = ``integer_word$toString``
Overload num_toString[local] = ``num_to_dec_string``

Triviality SPLITP_num_toString:
  ∀i.
  SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
         (toString (i:num)) = (toString i,[])
Proof
  recInduct COMPLETE_INDUCTION >> rpt strip_tac
  >> fs[ASCIInumbersTheory.num_to_dec_string_def]
  >> fs[ASCIInumbersTheory.n2s_def]
  >> PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >> rw[] >> fs[SPLITP,SPLITP_HEX]
  >> first_x_assum (qspec_then `n DIV 10` assume_tac) >> rfs[]
  >> fs[SPLITP_APPEND,SPLITP_NIL_SND_EVERY]
  >> ‘n MOD 10 < 10’ by fs[] >> rename [`HEX n`]
  >> pop_assum mp_tac >> rpt(pop_assum kall_tac)
  >> qid_spec_tac ‘n’
  >> recInduct one_to_ten >> fs[]
QED

Triviality SPLITP_int_toString:
  ∀i. SPLITP (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
             (toString (i:int)) = (toString i,[])
Proof
  rpt strip_tac >> fs[integer_wordTheory.toString_def] >> rw[] >> fs[SPLITP,SPLITP_num_toString]
QED

Triviality TOKENS_tostring:
  TOKENS (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") (toString(n:num)) = [toString n]
Proof
  Cases_on `num_toString n` >> fs[TOKENS_def]
  >> qpat_x_assum `_ = STRING _ _` (assume_tac o GSYM) >> fs[]
  >> pairarg_tac >> pop_assum (assume_tac o GSYM)
  >> fs[SPLITP_num_toString,TOKENS_def]
  >> qpat_x_assum `STRING _ _ = _` (assume_tac o GSYM) >> fs[]
QED

Triviality num_le_10:
  ∀n. 0 ≤ n /\ n < 10 ==> Num n < 10
Proof
  Cases >> fs[]
QED

Triviality tokens_toString:
  tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n") (toString (n:num)) = [toString n]
Proof
  simp [toString_thm, num_to_str_thm, TOKENS_eq_tokens_sym, TOKENS_tostring]
QED

Triviality tokens_strcat:
  l ≠ [] ==>
  (tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
          (toString (n:num) ^
                    strlit (STRING (acd l r) "") ^ toString (m:num) ^ strlit "\n")
   = [toString n; toString m])
Proof
  Cases_on `l` >> Cases_on `r` >> fs[acd_def] >>
  fs[tokens_append_strlit,strcat_assoc,tokens_append_right_strlit,tokens_toString]
QED

Triviality tokens_strcat':
  r ≠ [] ==>
  (tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
          (toString (n:num) ^
                    strlit (STRING (acd l r) "") ^ toString (m:num) ^ strlit "\n")
   = [toString n; toString m])
Proof
  Cases_on `l` >> Cases_on `r` >>
  fs[acd_def,tokens_append_strlit,strcat_assoc,tokens_append_right_strlit,tokens_toString]
QED

Triviality strsub_strcat:
  ∀s s'. strsub(s ^ s') n = if n < strlen s then strsub s n else strsub s' (n - strlen s)
Proof
    Induct >> simp[strcat_thm,implode_def,strsub_def,EL_APPEND_EQN]
    \\ gen_tac \\ Cases \\ simp[]
QED

Triviality strsub_str:
   strsub (str c) 0 = c
Proof
  rw[str_def,implode_def,strsub_def]
QED

Triviality acd_simps:
  (l ≠ [] ⇒ acd [] l = #"a" ∧ acd l [] = #"d") ∧
  (l ≠ [] ∧ r ≠ [] ⇒ acd l r = #"c")
Proof
  strip_tac >> fs[oneline acd_def] >>
  rpt(PURE_TOP_CASE_TAC >> fs[])
QED

Triviality HEX_isDigit:
  !n. n < 10 ==> isDigit(HEX n)
Proof
  recInduct one_to_ten >> fs[isDigit_def]
QED

(* TODO: move at least these (and probably others in this file) *)
Theorem toString_isDigit:
   ∀n. EVERY isDigit (toString(n:num))
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
  ∀n. toString (&n) = toString n
Proof
  recInduct COMPLETE_INDUCTION >> strip_tac
  >> fs[integer_wordTheory.toString_def]
QED

Triviality substring_adhoc_simps:
  ∀h.
   substring (strlit "> " ^ h) 0 2 = strlit "> " ∧
   substring (strlit "> " ^ h) 2 (strlen h) = h ∧
   substring (strlit "< " ^ h) 0 2 = strlit "< " ∧
   substring (strlit "< " ^ h) 2 (strlen h) = h
Proof
  Induct >> rpt strip_tac >> fs[strcat_thm,implode_def,substring_def,strlen_def]
  >> fs[ADD1,MIN_DEF] >> fs[SEG_compute] >> simp_tac pure_ss [ONE,TWO,SEG_SUC_CONS]
  >> fs[SEG_LENGTH_ID]
QED

Triviality depatch_lines_strcat_cancel:
  ∀r. depatch_lines (MAP (strcat (strlit "> ")) r) = SOME r
Proof
  Induct >> fs[depatch_lines_def,depatch_line_def,strlen_strcat,substring_adhoc_simps]
QED

Triviality depatch_lines_diff_add_prefix_cancel:
   depatch_lines (diff_add_prefix l (strlit "> ")) = SOME l
Proof
  fs[diff_add_prefix_def,depatch_lines_strcat_cancel]
QED

Triviality patch_aux_nil:
  patch_aux [] file remfl n = SOME file
Proof
  fs[patch_aux_def]
QED

Triviality line_numbers_not_empty:
  ∀l n . line_numbers l n <> strlit ""
Proof
  fs[line_numbers_def, num_to_str_thm, implode_def]
  \\ rw []
  \\ simp_tac std_ss [GSYM explode_11, explode_strcat]
  \\ simp []
QED

Theorem tokens_eq_sing:
   ∀s f. EVERY ($¬ ∘ f) (explode s) ∧ s <> strlit "" ⇒ tokens f s = [s]
Proof
  Cases
  \\ fs[TOKENS_eq_tokens_sym,toString_thm,explode_implode,implode_def]
  \\ Cases_on `s'` \\ fs [TOKENS_def] \\ rw []
  \\ fs [o_DEF,SPLITP_EVERY,TOKENS_def]
QED

Triviality tokens_toString_comma:
  tokens ($= #",") (toString (n:num)) = [toString n]
Proof
  rw [] \\ match_mp_tac tokens_eq_sing
  \\ fs [num_to_str_thm,implode_def]
  \\ fs [num_to_str_def]
  \\ match_mp_tac (MP_CANON EVERY_MONOTONIC)
  \\ qexists_tac `isDigit`
  \\ fs [EVERY_isDigit_num_to_dec_string] \\ EVAL_TAC
QED

Triviality tokens_comma_lemma:
  tokens (λx. x = #"a" ∨ x = #"d" ∨ x = #"c" ∨ x = #"\n")
     (line_numbers l n) = [line_numbers l n]
Proof
  ‘EVERY (λx. isDigit x ∨ x = #",") (explode(line_numbers l n))’
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
  \\ fs [strcat_def,concat_def]
QED

Triviality parse_header_cancel:
 l ≠ [] ∨ l' ≠ [] ⇒
 parse_patch_header(diff_single_header l n l' n') =
  SOME(n,
       if LENGTH l <= 1 then NONE else SOME(n+LENGTH l),
       if l = [] then
         #"a"
       else if l' = [] then
         #"d"
       else
         #"c",
       n',
       if LENGTH l' <= 1 then
         NONE
       else
         SOME(n'+LENGTH l'))
Proof
  rw[diff_single_header_def,parse_patch_header_def,
     option_case_eq,list_case_eq,PULL_EXISTS,
     strsub_strcat,tokens_append_right_strlit,GSYM str_def,
     tokens_append,acd_simps,tokens_comma_lemma,
     tokens_comma_lemma]
  \\ rw[line_numbers_def,tokens_toString_comma,
        fromNatString_toString,
        GSYM str_def,tokens_append,strsub_str]
QED

Triviality patch_aux_cancel_base_case:
  patch_aux (diff_with_lcs [] r n r' m) r (LENGTH r) n = SOME r'
Proof
  fs[diff_with_lcs_def,diff_single_def] >> rw[]
  >> fs[patch_aux_def]
  >> fs[patch_aux_def,parse_header_cancel,
         diff_add_prefix_def,depatch_lines_strcat_cancel,
         GSYM MAP_TAKE,GSYM MAP_DROP,DROP_APPEND,TAKE_APPEND]
  >> rw[]
  >> fs[DROP_LENGTH_TOO_LONG,TAKE_LENGTH_TOO_LONG,patch_aux_def,
        quantHeuristicsTheory.LIST_LENGTH_0,
        DROP_APPEND,depatch_lines_strcat_cancel]
  >> ‘LENGTH r = 1’ by (Cases_on ‘LENGTH r’ >> fs[])
  >> fs[depatch_lines_strcat_cancel]
QED

Theorem SPLITP_NIL_FST:
   ∀ls P r. SPLITP P ls = ([],r) ⇔ (r = ls ∧ ((ls <> []) ==> P(HD ls)))
Proof
  Cases >> rpt strip_tac >> fs[SPLITP,EQ_IMP_THM] >> IF_CASES_TAC
  >> strip_tac >> fs[]
QED

Theorem diff_add_prefix_length:
  ∀l s. LENGTH (diff_add_prefix l s) = LENGTH l
Proof
  fs[diff_add_prefix_def]
QED

Theorem diff_add_prefix_TAKE:
   ∀l n s. TAKE n (diff_add_prefix l s) = diff_add_prefix (TAKE n l) s
Proof
  fs[diff_add_prefix_def,MAP_TAKE]
QED

Theorem diff_add_prefix_DROP:
   ∀l n s. DROP n (diff_add_prefix l s) = diff_add_prefix (DROP n l) s
Proof
  fs[diff_add_prefix_def,MAP_DROP]
QED

Theorem diff_add_prefix_nil:
  ∀s. (diff_add_prefix [] s) = []
Proof
  fs[diff_add_prefix_def]
QED

Triviality ONE_MINUS_SUCC:
  1 - SUC x = 0
Proof
  intLib.COOPER_TAC
QED

Triviality SUCC_LE_ONE:
  SUC n ≤ 1 ⇔ n = 0
Proof
  intLib.COOPER_TAC
QED

Triviality patch_aux_keep_init:
  ∀l p t n t' m.
  common_subsequence l t t' ==>
  patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) (p ++ t) (LENGTH t + LENGTH p) n
  =
  case patch_aux (diff_with_lcs l t (n + LENGTH p) t' (m + LENGTH p)) t (LENGTH t) (n+LENGTH p) of
    SOME r => SOME(p++r)
  | NONE => NONE
Proof
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
      >> Cases_on `lr` >> gvs[common_subsequence_empty']
      >> Cases_on `l'r` >> gvs[common_subsequence_empty']
      >> first_assum(qspecl_then [`p++[h]`,`t`,`n`,`t'`,`n`] mp_tac)
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
  >> PURE_TOP_CASE_TAC >> fs[]
  >> every_case_tac >> fs []
QED

Triviality patch_aux_keep_init_cons:
  ∀l t n t' h m.
  common_subsequence l t t' ⇒
  patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) (h::t) (SUC (LENGTH t)) n
  =
  case patch_aux (diff_with_lcs l t (n + 1) t' (m + 1)) t (LENGTH t) (n+1) of
    SOME r => SOME(h::r)
  | NONE => NONE
Proof
  rpt strip_tac >> drule patch_aux_keep_init >>
  disch_then $ qspec_then ‘[h]’ assume_tac >> fs[ADD1]
QED

Triviality list_nil_sub_length:
  l ≠ [] ⇒ 1 - LENGTH l = 0
Proof
  Cases_on `l` >> fs[]
QED

Triviality list_length_1_lemma:
  l ≠ [] ∧ LENGTH l <= 1 ⇒ LENGTH l = 1
Proof
  Cases_on `LENGTH l` >> fs[]
QED

Triviality minus_add_too_large:
  a - ((a:num) + n) = 0
Proof
  intLib.COOPER_TAC
QED

Triviality minus_add_too_large':
  (a + 1) - ((a:num) + 2) = 0
Proof
  intLib.COOPER_TAC
QED

Theorem patch_aux_diff_cancel:
 ∀l r n r' m.
  common_subsequence l r r' ==>
  (patch_aux (diff_with_lcs l r n r' m) r (LENGTH r) n = SOME r')
Proof
  Induct
  >> rpt strip_tac
  >- fs[patch_aux_cancel_base_case]
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
      >> drule common_subsequence_split_css2
      >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
      >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
      >> fs[patch_aux_def] >> rw[]
      >> fs[parse_header_cancel,TAKE_APPEND]
      >> rw[] >> fs[quantHeuristicsTheory.LIST_LENGTH_0,TAKE_LENGTH_TOO_LONG,list_nil_sub_length,
                    depatch_lines_strcat_cancel,DROP_LENGTH_TOO_LONG,DROP_APPEND]
      >> drule patch_aux_keep_init_cons
      >> disch_then(qspecl_then [`n`,`h`,`m + LENGTH l'l`] assume_tac)
      >> drule SPLITP_JOIN
      >> fs[])
  >- (fs[SPLITP_NIL_FST] >> rveq
      >> Cases_on `lr` >> fs[common_subsequence_empty']
      >> Cases_on `l'r` >> fs[common_subsequence_empty',SPLITP_NIL_SND_EVERY]
      >> rveq
      >> fs[cons_common_subsequence,patch_aux_keep_init_cons]
      >> drule common_subsequence_split_css
      >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
      >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
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
  >- (qpat_x_assum ‘~(_ ∧ _)’ kall_tac
      >> fs[SPLITP_NIL_FST] >> rveq
      >> Cases_on `lr` >> fs[common_subsequence_empty']
      >> Cases_on `l'r` >> fs[common_subsequence_empty',SPLITP_NIL_SND_EVERY]
      >> rveq
      >> fs[cons_common_subsequence,patch_aux_keep_init_cons]
      >> drule common_subsequence_split_css >> strip_tac >> drule common_subsequence_split_css2
      >> fs[SPLITP_EVERY,o_DEF,common_subsequence_empty',SPLITP]
      >> drule SPLITP_IMP >> qpat_x_assum `SPLITP _ _ = _ ` mp_tac
      >> drule SPLITP_IMP >> rpt strip_tac >> fs[] >> rveq >> fs[cons_common_subsequence]
      >> fs[patch_aux_def] >> rw[]
      >> fs[parse_header_cancel,TAKE_APPEND]
      >> rw[]
      >> drule SPLITP_JOIN >> qpat_x_assum `SPLITP _ _ = _` mp_tac
      >> drule SPLITP_JOIN >> ntac 3 strip_tac
      >> fs []
      >> gvs [DROP_APPEND,DROP_LENGTH_TOO_LONG,TAKE_APPEND,ONE_MINUS_SUCC,TAKE_LENGTH_TOO_LONG]
      >> gvs [CaseEq"option",PULL_EXISTS,depatch_lines_strcat_cancel]
      >> drule patch_aux_keep_init_cons
      >> disch_then(qspecl_then [`n + LENGTH ll`,`h`,`m + LENGTH l'l`] mp_tac)
      >> fs[ADD1,list_length_1_lemma,depatch_lines_strcat_cancel]
      >> disch_then $ rewrite_tac o single o SYM
      >> simp [SUB_PLUS,DECIDE “2 - n - 2:num = 0”])
QED

Theorem patch_diff_cancel:
   patch_alg (diff_alg l r) l = SOME r
Proof
  fs[patch_alg_def,diff_alg_def] >>
  irule patch_aux_diff_cancel >>
  irule $ cj 1 $ iffLR lcs_def >>
  irule optimised_lcs_correct
QED

Definition headers_within_def:
  headers_within n m l =
    EVERY (OPTION_ALL (λ(n':num,m':num option,c,_,_).
      (n <= n' ∧ n' <= m ∧ (IS_NONE m' ∧ (c = #"d" ∨ c = #"c") ⇒
       n'+1 <= m) ∧
      (IS_SOME m' ==> (n ≤ THE m' ∧ THE m' ≤ m)))))
         (MAP parse_patch_header l)
End

Theorem headers_within_IMP:
   headers_within n m (h::t) ∧ parse_patch_header h = SOME(q,NONE,c,tup)
   ⇒ n <= q ∧ q <= m ∧ ((c= #"d" ∨ c = #"c") ⇒ q+1 <= m)
Proof
  rpt strip_tac >> fs[headers_within_def] >> rfs[ELIM_UNCURRY]
QED

Theorem headers_within_IMP_SOME:
   headers_within n m (h::t) ∧ parse_patch_header h = SOME(q,SOME q',c,tup)
   ⇒ n ≤ q ∧ q ≤ m ∧ n ≤ q' ∧ q' ≤ m
Proof
  rpt strip_tac >> fs[headers_within_def] >> rfs[ELIM_UNCURRY]
QED

Theorem headers_within_grow:
   headers_within n' m' l ∧ n ≤ n' ∧ m' ≤ m ⇒ headers_within n m l
Proof
  Induct_on `l` >> rpt strip_tac >> fs[headers_within_def]
  >> Cases_on `parse_patch_header h` >> fs[pairTheory.ELIM_UNCURRY]
  >> rw[] >> fs[]
QED

Theorem headers_within_append:
   headers_within n m (l++l') = (headers_within n m l ∧ headers_within n m l')
Proof
  simp[headers_within_def]
QED

Theorem headers_within_dest_cons:
   headers_within n m (e::l') ⇒ headers_within n m l'
Proof
  simp[headers_within_def]
QED

Theorem headers_within_drop:
   headers_within n m (l) ⇒ headers_within n m (DROP x l)
Proof
  simp[headers_within_def,MAP_DROP,EVERY_DROP]
QED

Theorem fromString_gt:
   fromString (implode (STRING #">" x)) = NONE ∧
   fromString (implode (STRING #"<" x)) = NONE
Proof
  rw [] \\ match_mp_tac fromString_EQ_NONE \\ EVAL_TAC
QED

Theorem fromNatString_gt:
   fromNatString (implode (STRING #">" x)) = NONE ∧
   fromNatString (implode (STRING #"<" x)) = NONE
Proof
  rw [fromNatString_def,fromString_gt]
QED

Triviality parse_nonheader_lemma:
  ∀f r. EVERY (OPTION_ALL f) (MAP parse_patch_header (diff_add_prefix r (strlit "> ")))
Proof
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
  >> fs[explode_implode,isDigit_def,fromNatString_gt]
QED

Triviality parse_nonheader_lemma2:
  ∀f r. EVERY (OPTION_ALL f) (MAP parse_patch_header (diff_add_prefix r (strlit "< ")))
Proof
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
  >> fs[explode_implode,isDigit_def,fromNatString_gt]
QED

Triviality parse_nonheader_lemma3:
  parse_patch_header (strlit "---\n") = NONE
Proof
  fs[parse_patch_header_def]
  >> every_case_tac
  >> fs[strcat_def,mlstringTheory.concat_def]
  >> fs[tokens_append_strlit,TOKENS_eq_tokens_sym]
  >> fs[TOKENS_def,pairTheory.ELIM_UNCURRY,SPLITP] >> rveq
QED

Theorem diff_with_lcs_headers_within:
  ∀l r n r' m.
  common_subsequence l r r' ⇒
  headers_within n (n + LENGTH r) (diff_with_lcs l r n r' m)
Proof
  Induct
  >> rpt strip_tac
  >- (fs[diff_with_lcs_def,headers_within_def,diff_single_def]
      >> rw[] >> fs[parse_header_cancel]
      >> rw[]
      >> fs[parse_nonheader_lemma,parse_nonheader_lemma2,
            parse_nonheader_lemma3]
      >> Cases_on `r` >> fs[])
  >> fs[diff_with_lcs_def]
  >> rpt(pairarg_tac >> fs[])
  >> IF_CASES_TAC
  >- (drule split_common_subsequence
      >> strip_tac
      >> first_x_assum drule >> fs[]
      >> disch_then(qspecl_then [`n+1`,`n+1`] assume_tac)
      >> drule headers_within_grow
      >> disch_then match_mp_tac
      >> fs[SPLITP_NIL_FST]
      >> Cases_on `r` >> fs[common_subsequence_empty'])
  >> simp[headers_within_append]
  >> strip_tac
  >- (fs[headers_within_def,diff_single_def]
      >> fs[parse_header_cancel]
      >> rw[]
      >> fs[parse_nonheader_lemma,parse_nonheader_lemma2,
            parse_nonheader_lemma3]
      >> drule common_subsequence_split >> strip_tac >> gvs[]
      >> imp_res_tac SPLITP_JOIN >> gvs[])
  >> drule split_common_subsequence
  >> drule common_subsequence_split
  >> drule common_subsequence_split2
  >> rpt strip_tac
  >> gvs[] >> first_x_assum drule
  >> disch_then(qspecl_then [`n + (LENGTH ll + 1)`,`m + (LENGTH l'l + 1)`] assume_tac)
  >> drule headers_within_grow
  >> disch_then match_mp_tac
  >> imp_res_tac SPLITP_JOIN >> gvs[]
QED

Theorem headers_within_cons:
 headers_within (n+1) m p1 ∧ m >= n+1 ⇒
  patch_alg_offs n p1 (e::l) = OPTION_MAP (CONS e) (patch_alg_offs (n+1) p1 l)
Proof
  Cases_on `p1` >> rpt strip_tac >>
  gvs[headers_within_def,patch_alg_offs_def,patch_aux_def,
      oneline OPTION_ALL_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[DROP_DROP_T,ADD1]
QED

Theorem IS_SUFFIX_induct:
  ∀P. P [] ∧ (∀h l. (∀sl. IS_SUFFIX l sl ⇒ P sl) ⇒ P (h::l)) ⇒ ∀l. P l
Proof
  rpt strip_tac
  \\ completeInduct_on ‘LENGTH l’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ Cases_on ‘l’ \\ gvs []
  \\ last_x_assum irule \\ rw []
  \\ last_x_assum irule \\ rw []
  \\ gvs [IS_SUFFIX_compute]
  \\ drule IS_PREFIX_LENGTH \\ gvs []
QED

Theorem IS_SUFFIX_DROP:
   !l n. IS_SUFFIX l (DROP n l)
Proof
  Induct >> rpt strip_tac >> rw[DROP_def]
  >> metis_tac[IS_SUFFIX_CONS]
QED

Triviality headers_within_snoc:
  ∀p1 n l m e.
  headers_within m (n + LENGTH l) p1 ∧ m <= (n + LENGTH l) ⇒
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
 ∀l' l. headers_within (n+LENGTH l') m p1 ∧ m >= n+LENGTH l' ⇒
        patch_alg_offs n p1 (l' ++ l) = OPTION_MAP (APPEND l') (patch_alg_offs (n+LENGTH l') p1 l)
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> rpt strip_tac
  >- (fs[] >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ a1` >> Cases_on `a1` >> fs[])
  >> rpt strip_tac
  >> fs[SNOC_APPEND]
  >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  >> drule headers_within_grow
  >> disch_then(qspecl_then[`n + LENGTH l'`,`m`] assume_tac)
  >> `!opt. OPTION_MAP ($++ (l' ⧺ [x])) opt = OPTION_MAP ($++ l') (OPTION_MAP (CONS x) opt)`
       by(Cases >> fs[])
  >> fs[ADD1]
  >> FULL_SIMP_TAC std_ss [ADD_ASSOC]
  >> pop_assum kall_tac
  >> drule headers_within_cons
  >> fs[]
QED

Theorem headers_within_append1':
  ∀l' l.
  headers_within (LENGTH l) m p1 ∧ m >= LENGTH l+LENGTH l' ⇒
  patch_alg p1 (l ++ l') = OPTION_MAP (APPEND l) (patch_alg_offs (LENGTH l) p1 l')
Proof
  rpt strip_tac
  >> assume_tac (GEN_ALL headers_within_append1)
  >> pop_assum (qspecl_then [`p1`,`0`,`m`,`l`,`l'`] assume_tac)
  >> fs[patch_alg_def,patch_alg_offs_def]
QED

Theorem headers_within_append2:
  ∀l' l.
  headers_within m (n + LENGTH l) p1 ∧ m <= n+LENGTH l ⇒
  patch_alg_offs n p1 (l ++ l') = OPTION_MAP (combin$C APPEND l') (patch_alg_offs n p1 l)
Proof
  Induct
  >> rpt strip_tac
  >- (fs[] >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ a1` >> Cases_on `a1` >> fs[])
  >> SIMP_TAC bool_ss [Once CONS_APPEND,APPEND_ASSOC]
  >> drule headers_within_grow
  >> disch_then(qspecl_then[`m`,`n + LENGTH(l ++ [h])`] mp_tac)
  >> impl_tac >> fs[]
  >> strip_tac >> first_x_assum drule
  >> fs[]
  >> `∀opt. OPTION_MAP (combin$C $++ (h::l')) opt = OPTION_MAP (combin$C $++ l') (OPTION_MAP (SNOC h) opt)`
    by(Cases >> fs[] )
  >> fs[ADD1]
  >> pop_assum kall_tac
  >> FULL_SIMP_TAC std_ss [ADD_ASSOC]
  >> drule headers_within_snoc
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
  >> drule headers_within_grow
  >> disch_then(qspecl_then [`a1`,`a1 + (LENGTH a3 - a2 + a2)`] mp_tac)
  >> impl_tac >- (unabbrev_all_tac >> fs[])
  >> qunabbrev_tac `a1` >> strip_tac
  >> drule headers_within_append1'
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
      >> drule (headers_within_append2 |> PURE_ONCE_REWRITE_RULE [ADD_SYM])
      >> disch_then(qspec_then `longest_common_suffix a3 a4` mp_tac)
      >> impl_tac >- fs[]
      >> strip_tac
      >> `a6 = LENGTH a3 - LENGTH(longest_common_suffix a3 a4)`
           by(unabbrev_all_tac >> fs[])
       >> rveq >> fs[]
       >> drule patch_aux_diff_cancel
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

Definition is_patch_line_def:
  is_patch_line s =
  if strlen s > 1 then
    if substring s 0 2 = strlit "> " then
      T
    else substring s 0 2 = strlit "< "
  else
      F
End

Triviality is_patch_line_simps:
  ∀r.
  FILTER is_patch_line (MAP (strcat (strlit "> ")) r) = (MAP (strcat (strlit "> ")) r) ∧
  FILTER is_patch_line (MAP (strcat (strlit "< ")) r) = MAP (strcat (strlit "< ")) r
Proof
  Induct_on `r` >> fs[] >> Induct
  >> fs[is_patch_line_def,strlen_def,strcat_thm,implode_def,substring_def,MIN_DEF]
  >> simp_tac pure_ss [ONE,TWO,SEG] >> fs[]
QED

Triviality toString_obtain_digits:
  ∀n. ∃f r. toString (n:num) = strlit(f::r) ∧ isDigit f ∧ EVERY isDigit r
Proof
  strip_tac >> fs[num_to_str_thm,implode_def]
  >> qspec_then `n` assume_tac toString_isDigit
  >> Cases_on `num_toString n` >> fs[]
QED

Triviality diff_single_patch_length:
  ∀r n r' m. LENGTH (FILTER is_patch_line (diff_single r n r' m)) = LENGTH r + LENGTH r'
Proof
  rpt strip_tac
  >> fs[diff_single_def,diff_single_header_def,is_patch_line_def,line_numbers_def,
        diff_add_prefix_def,is_patch_line_simps]
  >> qspec_then `n` assume_tac toString_obtain_digits
  >> qspec_then `m` assume_tac toString_obtain_digits
  >> fs[] >> rw[]
  >> fs[is_patch_line_simps,substring_def,strcat_thm,implode_def,explode_thm,MIN_DEF, isDigit_def]
  >> rfs[] >> full_simp_tac pure_ss [ONE,TWO,SEG] >> fs[FILTER_APPEND,is_patch_line_simps]
  >> fs[is_patch_line_def,substring_def,implode_def] >> full_simp_tac pure_ss [ONE,TWO,SEG]
  >> fs[]
QED

Triviality diff_with_lcs_optimal:
  ∀l r r' n m.
  lcs l r r' ⇒
  LENGTH(FILTER is_patch_line (diff_with_lcs l r n r' m)) = LENGTH r + LENGTH r' - (2*LENGTH l)
Proof
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
  >> drule lcs_max_length >> fs[]
QED

Theorem diff_optimal:
   !l r r'. lcs l r r' ⇒
   LENGTH(FILTER is_patch_line (diff_alg r r')) = LENGTH r + LENGTH r' - (2*LENGTH l)
Proof
  rpt strip_tac >> fs[diff_alg_def]
  >> `lcs (optimised_lcs r r') r r'` by(metis_tac[optimised_lcs_correct])
  >> `LENGTH l = LENGTH (optimised_lcs r r')`
       by(fs[lcs_def,common_subsequence_def,is_subsequence_def] >> metis_tac[is_subsequence_length,LESS_EQUAL_ANTISYM])
  >> fs[diff_with_lcs_optimal]
QED

Theorem REVERSE_DROP_REVERSE_TAKE:
   !l n. n <= LENGTH l ⇒
  REVERSE((DROP n (REVERSE l))) = TAKE (LENGTH l - n) l
Proof
  Induct >> rpt strip_tac >> fs[DROP_def,DROP_APPEND] >> rw[]
  >> fs[ADD1,NOT_LEQ]
  >> imp_res_tac EQ_LESS_EQ >> fs[]
  >> fs[DROP_LENGTH_TOO_LONG]
QED

Theorem diff2_optimal:
  ∀l r r'.
  lcs l r r' ⇒
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
  >> pop_assum $ PURE_ONCE_REWRITE_TAC o single
  >> pop_assum $ PURE_ONCE_REWRITE_TAC o single
  >> fs[]
QED

