open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory lcsTheory diffTheory;

val _ = new_theory "diffProg";

val _ = translation_extends"ioProg";

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

val _ = translate (optimised_lcs_def);

val dynamic_lcs_row_side_def = Q.prove(
`∀h l previous_col previous_row diagonal.
   dynamic_lcs_row_side h l previous_col previous_row diagonal ⇔
   (LENGTH l <= LENGTH previous_row)`,
  Induct_on `l`
  >> rw[Once(fetch "-" "dynamic_lcs_row_side_def")]
  >> Cases_on `previous_row`
  >> fs[] >> metis_tac[]) |> update_precondition;

val dynamic_lcs_rows_side_def = Q.prove(
  `∀l r previous_row.
   dynamic_lcs_rows_side l r previous_row ⇔
   (l = [] \/ LENGTH r <= LENGTH previous_row)`,
  Induct_on `l`
  >> rw[Once(fetch "-" "dynamic_lcs_rows_side_def"),dynamic_lcs_row_side_def,dynamic_lcs_length])
  |> update_precondition;

val dynamic_lcs_side_def = Q.prove(
  `∀l r. dynamic_lcs_side l r ⇔ T`,
  rw[fetch "-" "dynamic_lcs_side_def",dynamic_lcs_rows_side_def,LENGTH_REPLICATE])
  |> update_precondition;

val optimised_lcs_side_def = Q.prove(
  `∀l r. optimised_lcs_side l r ⇔ T`,
  rw[fetch "-" "optimised_lcs_side_def",dynamic_lcs_side_def]) |> update_precondition;

val _ = translate diff_alg_def;

val diff_with_lcs_side_IMP = Q.prove(
  `!l l' n l'' n'.
   lcs l l' l'' ==> diff_with_lcs_side l l' n l'' n'`,
  Induct_on `l`
  >- fs[Once(fetch "-" "diff_with_lcs_side_def")]
  >> PURE_ONCE_REWRITE_TAC [fetch "-" "diff_with_lcs_side_def"]
  >> rpt strip_tac
  >> drule lcs_split
  >> drule lcs_split2  
  >> drule split_lcs_optimal_substructure
  >> rpt strip_tac  
  >> fs[]
  >> rpt(CHANGED_TAC(TRY(qpat_x_assum `a::b = x` (assume_tac o GSYM))))
  >> rfs[]
  >> metis_tac[list_distinct]);

val diff_alg_side_def = Q.prove(`
  !l r. diff_alg_side l r  ⇔ T`,
  rw[fetch "-" "diff_alg_side_def"]
  >> metis_tac[diff_with_lcs_side_IMP,optimised_lcs_correct]) |> update_precondition;

val inputLines = process_topdecs`
  fun inputLines fd =
    let
      fun loop() =
        case inputLine fd of
             NONE => []
           | SOME l => l::loop()
    in
      loop()
    end`

val _ = append_prog inputLines;



val _ = export_theory ();
