(*
  Pure functions to be used in a word frequency counting program, backed by the
  balanced binary search tree data structure.
*)

open preamble
     mlstringTheory
     balanced_mapTheory

val _ = new_theory "wordfreq";

(* TODO: move *)
val lookup_insert = Q.store_thm("lookup_insert",
  `good_cmp cmp ∧ invariant cmp t ⇒
   lookup cmp k (insert cmp k' v t) =
   if cmp k k' = Equal then SOME v else lookup cmp k t`,
  rw[] \\ rw[lookup_thm,insert_thm,FLOOKUP_UPDATE] \\
  metis_tac[key_set_eq,comparisonTheory.cmp_thms]);
(* -- *)

val lookup0_def = Define`
  lookup0 w t = case lookup compare w t of NONE => 0n | SOME n => n`;

val insert_word_def = Define`
  insert_word t w =
    insert compare w (lookup0 w t + 1) t`;

val insert_line_def = Define`
  insert_line t s =
     FOLDL insert_word t (tokens isSpace s)`;

(* TODO: this should go back to mlstringTheory? *)
val good_cmp_compare = Q.store_thm("good_cmp_compare",
  `good_cmp compare`,
  match_mp_tac comparisonTheory.TotOrder_imp_good_cmp \\
  MATCH_ACCEPT_TAC TotOrd_compare);
(* -- *)

val key_set_compare_unique = Q.store_thm("key_set_compare_unique[simp]",
  `key_set compare k = {k}`,
  rw[key_set_def,EXTENSION] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

(* A high-level specification of words and frequencies *)

val all_words_def = Define`
  all_words s = TOKENS isSpace s`;
(*
EVAL ``all_words "hello there hello how are you one two one two three"``
*)
val frequency_def = Define`
  frequency s w = LENGTH (FILTER ($= w) (all_words s))`;
(*
EVAL``frequency "hello there hello how are you one two one two three" "hello"``
EVAL``frequency "hello there hello how are you one two one two three" "one"``
EVAL``frequency "hello there hello how are you one two one two three" "three"``
EVAL``frequency "hello there hello how are you one two one two three" "four"``
*)

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
        lookup0 w t + frequency (explode s) (explode w))`,
  strip_tac \\ rveq \\
  simp[insert_line_def,TOKENS_eq_tokens_sym,all_words_def,frequency_def] \\
  Q.SPEC_TAC(`TOKENS isSpace (explode s)`,`ls`) \\
  ho_match_mp_tac SNOC_INDUCT \\ simp[] \\
  ntac 3 strip_tac \\
  simp[MAP_SNOC,FOLDL_SNOC,insert_word_def] \\
  conj_asm1_tac >- metis_tac[good_cmp_compare,insert_thm] \\
  rw[FILTER_SNOC] \\ rw[mlstringTheory.implode_explode] \\
  rw[lookup0_insert] \\ fs[mlstringTheory.explode_implode]);

val _ = export_theory();
