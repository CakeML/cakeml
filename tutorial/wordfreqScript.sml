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

val lookup0_empty = Q.store_thm("lookup0_empty[simp]",
  `lookup0 w empty = 0`, EVAL_TAC);

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

val all_words_nil = Q.store_thm("all_words_nil[simp]",
  `all_words (implode "") = []`, EVAL_TAC);

val all_words_concat = Q.store_thm("all_words_concat",
  `isSpace sp ⇒
   all_words (s1 ^ str sp ^ s2) = all_words s1 ++ all_words s2`,
  rw[all_words_def,mlstringTheory.tokens_append,mlstringTheory.strcat_assoc]);

val all_words_concat_space = Q.store_thm("all_words_concat_space",
  `isSpace sp ⇒ all_words (s1 ^ str sp) = all_words s1`,
  rw[] \\ qspec_then`implode ""`mp_tac(Q.GEN`s2`all_words_concat) \\
  fs[mlstringTheory.strcat_def]);

val frequency_nil = Q.store_thm("frequency_nil[simp]",
  `frequency (implode "") w = 0`, EVAL_TAC);

val frequency_concat = Q.store_thm("frequency_concat",
  `isSpace sp ⇒
   frequency (s1 ^ str sp ^ s2) w = frequency s1 w + frequency s2 w`,
  rw[frequency_def,all_words_concat,FILTER_APPEND]);

val frequency_concat_space = Q.store_thm("frequency_concat_space",
  `isSpace sp ⇒ frequency (s1 ^ str sp) = frequency s1`,
  rw[FUN_EQ_THM,frequency_def,all_words_concat_space]);

val key_set_compare_unique = Q.store_thm("key_set_compare_unique[simp]",
  `key_set compare k = {k}`,
  rw[key_set_def,EXTENSION] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val IMAGE_key_set_compare_inj = Q.store_thm("IMAGE_key_set_compare_inj[simp]",
  `IMAGE (key_set compare) s1 = IMAGE (key_set compare) s2 ⇔ s1 = s2`,
  rw[EQ_IMP_THM]
  \\ fs[Once EXTENSION]
  \\ fs[EQ_IMP_THM] \\ rw[]
  \\ res_tac \\ fs[]);

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
        lookup0 w t + frequency s w) ∧
   FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ (IMAGE (key_set compare) (set (all_words s)))`,
  strip_tac \\ rveq \\
  simp[insert_line_def,all_words_def,frequency_def] \\
  Q.SPEC_TAC(`tokens isSpace s`,`ls`) \\
  ho_match_mp_tac SNOC_INDUCT \\ simp[] \\
  ntac 3 strip_tac \\
  simp[MAP_SNOC,FOLDL_SNOC,insert_word_def] \\
  rw[good_cmp_compare,insert_thm,FILTER_SNOC,lookup0_insert] \\
  rw[EXTENSION] \\ metis_tac[]);

(* not quite the version we want. see below instead.
val FOLDL_insert_line = Q.store_thm("FOLDL_insert_line",
  `∀ls t t' s.
    invariant compare t ∧ t' = FOLDL insert_line t ls ∧
    s = concat (MAP (λw. strcat w (strlit "\n")) ls)
    ⇒
    invariant compare t' ∧
    (∀w. lookup0 w t' = lookup0 w t + frequency s w) ∧
    FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ IMAGE (key_set compare) (set (all_words s))`,
  Induct \\ simp[mlstringTheory.concat_def] \\ ntac 3 strip_tac \\
  rename1`insert_line t w` \\
  imp_res_tac insert_line_thm \\ fs[] \\
  `strlit "\n" = str #"\n"` by EVAL_TAC \\
  `isSpace #"\n"` by EVAL_TAC \\
  first_x_assum drule \\
  rw[frequency_concat,all_words_concat] \\
  rw[EXTENSION] \\ metis_tac[]);
*)

val FOLDL_insert_line = Q.store_thm("FOLDL_insert_line",
  `∀ls t t' s.
    invariant compare t ∧ t' = FOLDL insert_line t ls ∧
    EVERY (λw. ∃x. w = strcat x (strlit "\n")) ls ∧
    s = concat ls
    ⇒
    invariant compare t' ∧
    (∀w. lookup0 w t' = lookup0 w t + frequency s w) ∧
    FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ IMAGE (key_set compare) (set (all_words s))`,
  Induct \\ simp[mlstringTheory.concat_def] \\ ntac 3 strip_tac \\
  rename1`insert_line t w` \\
  imp_res_tac insert_line_thm \\ fs[] \\
  `strlit "\n" = str #"\n"` by EVAL_TAC \\
  `isSpace #"\n"` by EVAL_TAC \\
  first_x_assum drule \\
  rw[frequency_concat,all_words_concat,frequency_concat_space,all_words_concat_space] \\
  rw[EXTENSION] \\ metis_tac[]);

val _ = export_theory();
