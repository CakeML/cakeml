open preamble ml_translatorLib ml_translatorTheory ml_progLib
    mlvectorTheory ListProgTheory basisFunctionsLib

val _ = new_theory"VectorProg"

val _ = translation_extends "ListProg";

val _ = ml_prog_update (open_module "Vector");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec ``Dtabbrev unknown_loc ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector)`` I);

val _ = trans "fromList" `Vector`
val _ = trans "length" `length`
val _ = trans "sub" `sub`


val _ = next_ml_names := ["tabulate"];
val result = translate tabulate_def;


val result = translate toList_aux_def;

val toList_aux_side_def = theorem"tolist_aux_side_def"

val toList_aux_side_thm = Q.prove(`∀vec n. tolist_aux_side vec n`,
  ho_match_mp_tac toList_aux_ind
  \\ metis_tac[GREATER_EQ,NOT_LESS_EQUAL,toList_aux_side_def])
  |> update_precondition

val _ = next_ml_names := ["toList"];
val result = translate toList_def;


val _ = next_ml_names := ["update"];
val result = translate update_def;


val _ = next_ml_names := ["concat"];
val result = translate concat_def;


val _ = next_ml_names := ["map"];
val result = translate map_def;
val _ = next_ml_names := ["mapi"];
val result = translate mapi_def;



val result = translate foldli_aux_def;
val foldli_aux_side_def = theorem"foldli_aux_1_side_def"
val _ = next_ml_names := ["foldli"];
val result = translate foldli_def;
val foldli_side_def = definition"foldli_1_side_def";

val foldli_aux_side_thm = Q.prove(
  `!f e vec n len. n + len = length (vec) ==> foldli_aux_1_side f e vec n len`,
  Induct_on`len` \\ rw[Once foldli_aux_side_def]
);

val foldli_side_thm = Q.prove(
  `foldli_1_side f e vec`,
  rw[foldli_side_def,foldli_aux_side_thm]) |> update_precondition;




val result = translate foldl_aux_def;
val foldl_aux_side_def = theorem"foldl_aux_side_def"
val _ = next_ml_names := ["foldl"];
val result = translate foldl_def;
val foldl_side_def = definition"foldl_1_side_def";

val foldl_aux_side_thm = Q.prove(
  `!f e vec n len. n + len = length vec ==> foldl_aux_side f e vec n len`,
  Induct_on `len` \\ rw [Once foldl_aux_side_def]
);

val foldl_side_thm = Q.prove(
  `!f e vec. foldl_1_side f e vec`,
  rw [foldl_side_def, foldl_aux_side_thm]) |> update_precondition;



val result = translate foldri_aux_def;
val foldri_aux_side_def = theorem"foldri_aux_side_def";
val _ = next_ml_names := ["foldri"];
val result = translate foldri_def;
val foldri_side_def = definition"foldri_1_side_def";

val foldri_aux_side_thm = Q.prove(
  `!f e vec len. len <= length vec ==> foldri_aux_side f e vec len`,
  Induct_on `len` \\ rw [Once foldri_aux_side_def]
);

val foldri_side_thm = Q.prove(
  `!f e vec. foldri_1_side f e vec`,
  rw [foldri_side_def, foldri_aux_side_thm] ) |> update_precondition



val result = translate foldr_aux_def;
val foldr_aux_side_def = theorem"foldr_aux_side_def";
val _ = next_ml_names := ["foldr"];
val result = translate foldr_def;
val foldr_side_def = definition"foldr_1_side_def";

val foldr_aux_side_thm = Q.prove(
  `!f e vec len. len <= length vec ==> foldr_aux_side f e vec len`,
  Induct_on `len` \\ rw[Once foldr_aux_side_def]
);

val foldr_side_thm = Q.prove(
  `!f e vec. foldr_1_side f e vec`,
  rw [foldr_side_def, foldr_aux_side_thm] ) |> update_precondition


val result = translate findi_aux_def;
val findi_aux_side_def = theorem"findi_aux_side_def"
val result = translate findi_def;
val findi_side_def = definition"findi_side_def"

val findi_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> findi_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once findi_aux_side_def]
);

val findi_side_thm = Q.prove (
  `!f vec. findi_side f vec`,
  rw [findi_side_def, findi_aux_side_thm] ) |> update_precondition



val result = translate find_aux_def;
val find_aux_side_def = theorem"find_aux_side_def"
val _ = next_ml_names := ["find"];
val result = translate find_def;
val find_side_def = definition"find_1_side_def"

val find_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> find_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once find_aux_side_def]
);

val find_side_thm = Q.prove (
  `!f vec. find_1_side f vec`,
  rw [find_side_def, find_aux_side_thm]) |> update_precondition



val result = translate exists_aux_def;
val exists_aux_side_def = theorem"exists_aux_side_def";
val _ = next_ml_names := ["exists"];
val result = translate exists_def;
val exists_side_def = definition"exists_1_side_def";

val exists_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> exists_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once exists_aux_side_def]
);

val exists_side_thm = Q.prove (
  `!f vec. exists_1_side f vec`,
  rw [exists_side_def, exists_aux_side_thm]) |> update_precondition



val result = translate all_aux_def;
val all_aux_side_def = theorem"all_aux_side_def";
val _ = next_ml_names := ["all"];
val result = translate all_def;
val all_side_def = definition"all_1_side_def";

val all_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> all_aux_side f vec n len`,
  Induct_on `len` \\ rw[Once all_aux_side_def]
);

val all_side_thm = Q.prove (
  `!f vec. all_1_side f vec`,
  rw [all_side_def, all_aux_side_thm]) |> update_precondition


val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val _ = next_ml_names := ["collate"];
val result = translate collate_def;
val collate_side_def = definition"collate_1_side_def";

val collate_aux_side_thm = Q.prove (
  `!f vec1 vec2 n ord len. n + len =
    (if length vec1 < length vec2
      then length vec1
    else length vec2) ==>
        collate_aux_side f vec1 vec2 n ord len`,
  Induct_on `len` \\ rw[Once collate_aux_side_def]
);

val collate_side_thm = Q.prove (
  `!f vec1 vec2. collate_1_side f vec1 vec2`,
  rw[collate_side_def, collate_aux_side_thm] ) |> update_precondition

val sigs = module_signatures [
  "fromList",
  "length",
  "sub",
  "tabulate",
  "toList",
  "update",
  "concat",
  "map",
  "mapi",
  "foldli",
  "foldl",
  "foldri",
  "foldr",
  "findi",
  "find",
  "exists",
  "all",
  "collate"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory ()
