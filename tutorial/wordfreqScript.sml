(*
  Pure functions to be used in a word frequency counting program, backed by the
  balanced binary search tree data structure.
*)

open preamble
     mlstringTheory
     balanced_mapTheory

val _ = new_theory "wordfreq";

val lookup0_def = Define`
  lookup0 w t = case lookup compare w t of NONE => 0n | SOME n => n`;

val insert_word_def = Define`
  insert_word t w =
    insert compare w (lookup0 w t + 1) t`;

val insert_line_def = Define`
  insert_line t s =
     FOLDL insert_word t (tokens isSpace s)`;

(* A high-level specification of words and frequencies *)

val all_words_def = Define`
  all_words s = tokens isSpace s`;
(*
EVAL ``all_words (strlit"hello there hello how are you one two one two three")``
*)
val frequency_def = Define`
  frequency s w = LENGTH (FILTER ($= w) (all_words s))`;
(*
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"hello")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"one")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"three")``
EVAL``frequency (strlit"hello there hello how are you one two one two three") (strlit"four")``
*)

val key_set_compare_unique = Q.store_thm("key_set_compare_unique[simp]",
  `key_set compare k = {k}`,
  rw[key_set_def,EXTENSION] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val lookup0_insert = Q.store_thm("lookup0_insert",
  `invariant compare t ⇒
   lookup0 k (insert compare k' v t) =
   if k = k' then v else lookup0 k t`,
  rw[lookup0_def,lookup_insert,good_cmp_compare] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val insert_line_thm = Q.store_thm("insert_line_thm",
  `invariant compare t ∧
   insert_line t s = t'
   ⇒
   invariant compare t' ∧
   (∀w. lookup0 w t' =
        lookup0 w t + frequency s w)`,
  strip_tac \\ rveq \\
  simp[insert_line_def,all_words_def,frequency_def] \\
  Q.SPEC_TAC(`tokens isSpace s`,`ls`) \\
  ho_match_mp_tac SNOC_INDUCT \\ simp[] \\
  ntac 3 strip_tac \\
  simp[MAP_SNOC,FOLDL_SNOC,insert_word_def] \\
  conj_asm1_tac >- metis_tac[good_cmp_compare,insert_thm] \\
  rw[FILTER_SNOC,lookup0_insert]);

val _ = export_theory();
