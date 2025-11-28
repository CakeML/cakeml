(*
  Module about the built-in string tyoe.
*)
Theory StringProg
Ancestors
  ml_translator mlstring VectorProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "VectorProg";
val _ = ml_translatorLib.use_string_type false;

val _ = ml_prog_update (open_module "String");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "string" (Atapp [] (Short "string"))`` I);

val _ = trans "sub" mlstringSyntax.strsub_tm;
val _ = trans "implode" mlstringSyntax.implode_tm;
val _ = trans "explode" mlstringSyntax.explode_tm;
val _ = trans "size" mlstringSyntax.strlen_tm;
val _ = trans "concat" mlstringSyntax.concat_tm;
val _ = trans "substring" mlstringSyntax.substring_tm;
val result = translate strcat_def;
val _ = trans "^" mlstringSyntax.strcat_tm;
val _ = trans "=" “((=):mlstring -> mlstring -> bool)”;

val result = translate (extract_def |> REWRITE_RULE [implode_def]);

val extract_side_def = definition"extract_side_def";
val extract_side_thm = Q.prove(
  `!s i opt. extract_side s i opt`,
  rw [extract_side_def, arithmeticTheory.MIN_DEF] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val res = translate (concatWith_aux_def |> REWRITE_RULE [implode_def]);
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["concatWith"];
val result = translate concatWith_def;

val result = translate str_def;

val _ = ml_prog_update open_local_block;
val result = translate translate_aux_def;
val translate_aux_side_def = theorem"translate_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["translate"];
val result = translate translate_def;
val translate_side_def = definition"translate_side_def";

Theorem translate_aux_side_thm[local]:
  !f s n len. n + len = strlen s ==> translate_aux_side f s n len
Proof
  Induct_on `len` \\ rw[Once translate_aux_side_def]
QED

val translate_side_thm = Q.prove (
  `!f s. translate_side f s`,
  rw [translate_side_def, translate_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val r = translate splitl_aux_def;
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["split"];
val r = translate splitl_def;

val _ = ml_prog_update open_local_block;

val res = translate tokens_alt_aux_def;

val tokens_alt_aux_side_def = theorem"tokens_alt_aux_side_def";

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["tokens"];
val result = translate tokens_alt;
val tokens_side_def = definition"tokens_side_def";

Theorem tokens_alt_aux_side_thm[local]:
  !f s i j k. i ≤ j ∧ j ≤ k ∧ k ≤ strlen s ⇒ tokens_alt_aux_side f s i j k
Proof
  ho_match_mp_tac tokens_alt_aux_ind>>
  rw[]>>
  rw [Once tokens_alt_aux_side_def]
QED

val tokens_side_thm = Q.prove (
  `!f s. tokens_side f s`,
  rw [tokens_side_def, tokens_alt_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;

val result = translate fields_alt_aux_def;
val fields_alt_aux_side_def = theorem"fields_alt_aux_side_def";

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["fields"];
val result = translate fields_alt;
val fields_side_def = definition"fields_side_def";

Theorem fields_alt_aux_side_thm[local]:
  !f s i j k. i ≤ j ∧ j ≤ k ∧ k ≤ strlen s ⇒ fields_alt_aux_side f s i j k
Proof
  ho_match_mp_tac fields_alt_aux_ind>>
  rw[]>>
  rw [Once fields_alt_aux_side_def]
QED

val fields_side_thm = Q.prove (
  `!f s. fields_side f s`,
  rw [fields_side_def, fields_alt_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["findi"];
val result = translate str_findi_def;

val _ = ml_prog_update open_local_block;
val result = translate isStringThere_aux_def;
val isStringThere_aux_side_def = theorem"isstringthere_aux_side_def";
val _ = ml_prog_update open_local_in_block;

Theorem isStringThere_aux_side_thm[local]:
  !s1 s2 s1i s2i len.
     s1i + len ≤ strlen s1 ∧ s2i + len <= strlen s2 ==>
     isstringthere_aux_side s1 s2 s1i s2i len
Proof
  Induct_on `len` \\ rw [Once isStringThere_aux_side_def]
QED

val _ = next_ml_names := ["isSubstring"];
val result = translate isSubstring_aux_def;
val isSubstring_aux_side_def = theorem"issubstring_aux_side_def";
Theorem isSubstring_aux_side_thm[local]:
  !s1 s2 lens1 n len.
    (lens1 = strlen s1) ∧ n + len + lens1 ≤ strlen s2 + 1 ==>
    issubstring_aux_side s1 s2 lens1 n len
Proof
  Induct_on `len` >>
  rw [Once isSubstring_aux_side_def] >>
  irule isStringThere_aux_side_thm >> simp[]
QED

val _ = next_ml_names := ["isSubstring"];
val result = translate isSubstring_def;
val isSubstring_side_def = definition"issubstring_side_def";
val isSubstring_side_thm = Q.prove (
  `!s1 s2. issubstring_side s1 s2`,
  rw [isSubstring_side_def, isSubstring_aux_side_thm]) |> update_precondition

val _ = next_ml_names := ["isSuffix"];
val result = translate isSuffix_def;
val isSuffix_side_def = definition"issuffix_side_def";
val isSuffix_thm = Q.prove (
  `!s1 s2. issuffix_side s1 s2`,
  rw[isSuffix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["isPrefix"];
val result = translate isPrefix_def;
val isPrefix_side_def = definition"isprefix_side_def";
val isPrefix_thm = Q.prove (
  `!s1 s2. isprefix_side s1 s2`,
  rw[isPrefix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate compare_aux_def;
val compare_aux_side_def = theorem"compare_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["compare"];
val result = translate compare_def;
val compare_side_def = definition"compare_1_side_def";

Theorem compare_aux_side_thm[local]:
  !s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len
Proof
  Induct_on `len` \\ rw [Once compare_aux_side_def]
QED

val compare_side_thm = Q.prove (
  `!s1 s2. compare_1_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["<"];
val _ = translate mlstring_lt_def;
val _ = next_ml_names := ["<="];
val _ = translate mlstring_le_def;
val _ = next_ml_names := [">="];
val _ = translate mlstring_ge_def;
val _ = next_ml_names := [">"];
val _ = translate mlstring_gt_def;

val _ = ml_prog_update open_local_block;
val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["collate"];
val result = translate collate_def;
val collate_side_def = definition"collate_1_side_def";

Theorem collate_aux_side_thm[local]:
  !f s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> collate_aux_side f s1 s2 ord n len
Proof
  Induct_on `len` \\ rw [Once collate_aux_side_def]
QED

val collate_side_thm = Q.prove (
  `!f s1 s2. collate_1_side f s1 s2`,
  rw [collate_side_def, collate_aux_side_thm] ) |> update_precondition

val _ = translate char_escape_seq_def;
val _ = ml_prog_update open_local_block;
val _ = translate char_escaped_def;
val _ = ml_prog_update open_local_in_block;
val _ = translate escape_str_def;
val _ = translate escape_char_def;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);
