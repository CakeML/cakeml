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

Theorem splitwords_nil[simp]:
   splitwords (implode "") = []
Proof
EVAL_TAC
QED
Theorem splitwords_nil_lit[simp]:
   splitwords (strlit "") = []
Proof
EVAL_TAC
QED

Theorem splitwords_concat:
   isSpace sp ⇒
   splitwords (s1 ^ str sp ^ s2) = splitwords s1 ++ splitwords s2
Proof
  rewrite_tac [GSYM strcat_assoc]
  \\ rw[splitwords_def,mlstringTheory.tokens_append,mlstringTheory.strcat_assoc]
QED

Theorem splitwords_concat_space:
   isSpace sp ⇒ splitwords (s1 ^ str sp) = splitwords s1
Proof
  rw[] \\ qspec_then`implode ""`mp_tac(Q.GEN`s2`splitwords_concat) \\
  fs[mlstringTheory.strcat_thm]
QED

Theorem splitwords_lines_of:
   FLAT (MAP splitwords (lines_of content)) =
   splitwords content
Proof
  `isSpace #"\n"` by EVAL_TAC \\
  rw[all_lines_def,lines_of_def,MAP_MAP_o,o_DEF,
     GSYM mlstringTheory.str_def,splitwords_concat_space] \\
  rw[splitwords_def,mlstringTheory.TOKENS_eq_tokens_sym] \\
  srw_tac[ETA_ss][GSYM o_DEF,GSYM MAP_MAP_o] \\
  simp[GSYM MAP_FLAT] \\ AP_TERM_TAC \\
  qmatch_goalsub_rename_tac `splitlines ls` \\
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
  rw[] \\ EVAL_TAC
QED

val frequency_def = Define`
  frequency s w = LENGTH (FILTER ($= w) (splitwords s))`;
(*
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"hello")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"one")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"three")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"four")``
*)

Theorem frequency_nil[simp]:
   frequency (implode "") w = 0
Proof
EVAL_TAC
QED
Theorem frequency_nil_lit[simp]:
   frequency (strlit "") w = 0
Proof
EVAL_TAC
QED

Theorem frequency_concat:
   isSpace sp ⇒
   frequency (s1 ^ str sp ^ s2) w = frequency s1 w + frequency s2 w
Proof
  rw[frequency_def,splitwords_concat,FILTER_APPEND]
QED

Theorem frequency_concat_space:
   isSpace sp ⇒ frequency (s1 ^ str sp) = frequency s1
Proof
  rw[FUN_EQ_THM,frequency_def,splitwords_concat_space]
QED

val _ = export_theory();
