(*
  A high-level specification of words and frequencies
*)

open preamble
     mlstringTheory
     fsFFIPropsTheory

val _ = new_theory"splitwords";

val splitwords_def = Define`
  splitwords s = tokens isSpace s`;
(*
EVAL ``splitwords (strlit"hello there hello how are you one two one two three")``
*)

val splitwords_nil = Q.store_thm("splitwords_nil[simp]",
  `splitwords (implode "") = []`, EVAL_TAC);
val splitwords_nil_lit = Q.store_thm("splitwords_nil_lit[simp]",
  `splitwords (strlit "") = []`, EVAL_TAC);

val splitwords_concat = Q.store_thm("splitwords_concat",
  `isSpace sp ⇒
   splitwords (s1 ^ str sp ^ s2) = splitwords s1 ++ splitwords s2`,
  rw[splitwords_def,mlstringTheory.tokens_append,mlstringTheory.strcat_assoc]);

val splitwords_concat_space = Q.store_thm("splitwords_concat_space",
  `isSpace sp ⇒ splitwords (s1 ^ str sp) = splitwords s1`,
  rw[] \\ qspec_then`implode ""`mp_tac(Q.GEN`s2`splitwords_concat) \\
  fs[mlstringTheory.strcat_thm]);

val splitwords_all_lines = Q.store_thm("splitwords_all_lines",
  `FLAT (MAP splitwords (all_lines fs fname)) =
   splitwords (implode (THE (ALOOKUP fs.files fname)))`,
  `isSpace #"\n"` by EVAL_TAC \\
  rw[all_lines_def,MAP_MAP_o,o_DEF,
     GSYM mlstringTheory.str_def,splitwords_concat_space] \\
  rw[splitwords_def,mlstringTheory.TOKENS_eq_tokens_sym] \\
  srw_tac[ETA_ss][GSYM o_DEF,GSYM MAP_MAP_o] \\
  simp[GSYM MAP_FLAT] \\ AP_TERM_TAC \\
  qspec_tac(`THE (ALOOKUP fs.files fname)`,`ls`) \\
  rw[splitlines_def]
  >- (
    qmatch_asmsub_abbrev_tac`NULL (LAST l)` \\
    Q.ISPEC_THEN`l`mp_tac APPEND_FRONT_LAST \\
    impl_tac >- rw[Abbr`l`] \\
    fs[NULL_EQ] \\ strip_tac \\
    `FLAT (MAP (TOKENS isSpace) (FRONT l)) = FLAT (MAP (TOKENS isSpace) l)` by (
      pop_assum(fn th => CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV(SYM th))))) \\
      simp[] \\ EVAL_TAC ) \\
    simp[Abbr`l`] \\
    match_mp_tac FLAT_MAP_TOKENS_FIELDS \\
    rw[] \\ EVAL_TAC ) \\
  match_mp_tac FLAT_MAP_TOKENS_FIELDS \\
  rw[] \\ EVAL_TAC);

val frequency_def = Define`
  frequency s w = LENGTH (FILTER ($= w) (splitwords s))`;
(*
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"hello")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"one")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"three")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"four")``
*)

val frequency_nil = Q.store_thm("frequency_nil[simp]",
  `frequency (implode "") w = 0`, EVAL_TAC);
val frequency_nil_lit = Q.store_thm("frequency_nil_lit[simp]",
  `frequency (strlit "") w = 0`, EVAL_TAC);

val frequency_concat = Q.store_thm("frequency_concat",
  `isSpace sp ⇒
   frequency (s1 ^ str sp ^ s2) w = frequency s1 w + frequency s2 w`,
  rw[frequency_def,splitwords_concat,FILTER_APPEND]);

val frequency_concat_space = Q.store_thm("frequency_concat_space",
  `isSpace sp ⇒ frequency (s1 ^ str sp) = frequency s1`,
  rw[FUN_EQ_THM,frequency_def,splitwords_concat_space]);

val _ = export_theory();
