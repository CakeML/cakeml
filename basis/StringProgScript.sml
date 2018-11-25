(*
  Module about the built-in string tyoe.
*)
open preamble
  ml_translatorLib ml_translatorTheory ml_progLib
  mlstringTheory VectorProgTheory basisFunctionsLib

val _ = new_theory"StringProg"

val _ = translation_extends "VectorProg";

val _ = ml_prog_update (open_module "String");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "string" (Atapp [] (Short "string"))`` I);

val _ = trans "sub" `strsub`
val _ = trans "implode" `implode`
val _ = trans "size" `strlen`
val _ = trans "concat" `mlstring$concat`
val _ = trans "substring" `mlstring$substring`
val result = translate strcat_def;
val _ = trans "^" `mlstring$strcat`

val result = translate explode_aux_def;
val result = translate explode_def;

val explode_aux_side_thm = Q.prove(
  `∀s n m. n + m = strlen s ==> explode_aux_side s n m `,
  Induct_on`m` \\ rw[Once (theorem"explode_aux_side_def")]);

val explode_side_thm = Q.prove(
  `explode_side x`,
  rw[definition"explode_side_def",explode_aux_side_thm]) |> update_precondition

val result = translate extract_def;
val extract_side_def = definition"extract_side_def";
val extract_side_thm = Q.prove(
  `!s i opt. extract_side s i opt`,
  rw [extract_side_def, MIN_DEF] ) |> update_precondition

val res = translate concatWith_aux_def;
val _ = next_ml_names := ["concatWith"];
val result = translate concatWith_def;

val result = translate str_def;


val result = translate translate_aux_def;
val translate_aux_side_def = theorem"translate_aux_side_def";
val result = translate translate_def;
val translate_side_def = definition"translate_side_def";

val translate_aux_side_thm = Q.prove (
  `!f s n len. n + len = strlen s ==> translate_aux_side f s n len`,
  Induct_on `len` \\ rw[Once translate_aux_side_def]
);

val translate_side_thm = Q.prove (
  `!f s. translate_side f s`,
  rw [translate_side_def, translate_aux_side_thm] ) |> update_precondition


val r = translate splitl_aux_def;
val r = translate splitl_def;

val res = translate tokens_aux_def;
val tokens_aux_side_def = theorem"tokens_aux_side_def";
val result = translate tokens_def;
val tokens_side_def = definition"tokens_side_def";

val tokens_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> tokens_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once tokens_aux_side_def]
);

val tokens_side_thm = Q.prove (
  `!f s. tokens_side f s`,
  rw [tokens_side_def, tokens_aux_side_thm] ) |> update_precondition



val result = translate fields_aux_def;
val fields_aux_side_def = theorem"fields_aux_side_def";
val result = translate fields_def;
val fields_side_def = definition"fields_side_def";

val fields_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> fields_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once fields_aux_side_def]
);

val fields_side_thm = Q.prove (
  `!f s. fields_side f s`,
  rw [fields_side_def, fields_aux_side_thm] ) |> update_precondition



val result = translate isStringThere_aux_def;
val isStringThere_aux_side_def = theorem"isstringthere_aux_side_def";

val isStringThere_aux_side_thm = Q.prove (
  `!s1 s2 s1i s2i len.
     s1i + len ≤ strlen s1 ∧ s2i + len <= strlen s2 ==>
     isstringthere_aux_side s1 s2 s1i s2i len`,
  Induct_on `len` \\ rw [Once isStringThere_aux_side_def]
);

val _ = next_ml_names := ["isPrefix"];
val result = translate isPrefix_def;
val isPrefix_side_def = definition"isprefix_side_def";
val isPrefix_thm = Q.prove (
  `!s1 s2. isprefix_side s1 s2`,
  rw[isPrefix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["isSuffix"];
val result = translate isSuffix_def;
val isSuffix_side_def = definition"issuffix_side_def";
val isSuffix_thm = Q.prove (
  `!s1 s2. issuffix_side s1 s2`,
  rw[isSuffix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val result = translate isSubstring_aux_def;
val isSubstring_aux_side_def = theorem"issubstring_aux_side_def";
val isSubstring_aux_side_thm = Q.prove (
  `!s1 s2 lens1 n len.
    (lens1 = strlen s1) ∧ n + len + lens1 ≤ strlen s2 + 1 ==>
    issubstring_aux_side s1 s2 lens1 n len`,
  Induct_on `len` >>
  rw [Once isSubstring_aux_side_def] >>
  irule isStringThere_aux_side_thm >> simp[]
);

val _ = next_ml_names := ["isSubstring"];
val result = translate isSubstring_def;
val isSubstring_side_def = definition"issubstring_side_def";
val isSubstring_side_thm = Q.prove (
  `!s1 s2. issubstring_side s1 s2`,
  rw [isSubstring_side_def, isSubstring_aux_side_thm]) |> update_precondition


val result = translate compare_aux_def;
val compare_aux_side_def = theorem"compare_aux_side_def";
val result = translate compare_def;
val compare_side_def = definition"compare_side_def";

val compare_aux_side_thm = Q.prove (
  `!s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once compare_aux_side_def]
);

val compare_side_thm = Q.prove (
  `!s1 s2. compare_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["<"];
val _ = translate mlstring_lt_def;
val _ = next_ml_names := ["<="];
val _ = translate mlstring_le_def;
val _ = next_ml_names := [">="];
val _ = translate mlstring_ge_def;
val _ = next_ml_names := [">"];
val _ = translate mlstring_gt_def;

val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_1_side_def";
val _ = next_ml_names := ["collate"];
val result = translate collate_def;
val collate_side_def = definition"collate_1_side_def";

val collate_aux_side_thm = Q.prove (
  `!f s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> collate_aux_1_side f s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once collate_aux_side_def]
);

val collate_side_thm = Q.prove (
  `!f s1 s2. collate_1_side f s1 s2`,
  rw [collate_side_def, collate_aux_side_thm] ) |> update_precondition

val sigs = module_signatures [
  "sub",
  "implode",
  "size",
  "concat",
  "substring",
  "^",
  "explode",
  "extract",
  "concatWith",
  "str",
  "translate",
  "splitl",
  "tokens",
  "fields",
  "isPrefix",
  "isSuffix",
  "isSubstring",
  "compare",
  "<",
  "<=",
  ">=",
  ">",
  "collate"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory()
