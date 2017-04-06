open preamble ml_translatorLib ml_progLib std_preludeTheory
open mllistTheory ml_translatorTheory mloptionProgTheory
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib

(*this library depends on nothing*)
val _ = new_theory"mllistProg"

val _ = translation_extends "mloptionProg"

val _ = ml_prog_update (open_module "List");


val _ = ml_prog_update (add_dec ``Dtabbrev unknown_loc ["'a"] "list" (Tapp [Tvar "'a"] (TC_name (Short "list")))`` I);

val result = translate LENGTH;
(* val result = save_thm("length_v_thm",translate LENGTH); *)

val result = translate HD;
val hd_side_def = Q.prove(
  `!xs. hd_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "hd_side_def"])
  |> update_precondition;

val result = translate tl_def;
val result = next_ml_names := ["TL_hol"];
val result = translate TL;
val tl_1_side_def = Q.prove(
  `!xs. tl_1_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "tl_1_side_def"])
  |> update_precondition;


val result = translate LAST_DEF;


val result = translate getItem_def;


val result = translate (EL |> REWRITE_RULE[GSYM nth_def]);
val nth_side_def = theorem"nth_side_def";

val result = translate (TAKE_def |> REWRITE_RULE[GSYM take_def]);


val result = translate (DROP_def |> REWRITE_RULE[GSYM drop_def]);


val result = next_ml_names := ["concat"];
val result = translate FLAT;


val result = translate MAP;
val result = translate mapi_def;
val result = translate MAPI_thm;


val result = translate mapPartial_def;


val app = process_topdecs`
  fun app f ls = case ls of [] => ()
    | (x::xs) => (f x; app f xs)`;
val _ = ml_prog_update(ml_progLib.add_prog app pick_name)

val st = get_ml_prog_state();

val app_spec = Q.prove(
  `∀l start lv A.
   LIST_TYPE A l lv /\
   (!n xv. n < LENGTH l ∧ A (EL n l) xv ==> app p fv [xv] (eff (start+n)) (POSTv v. &UNIT_TYPE () v * (eff (start+n+1))))
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "app" st) [fv; lv] (eff start)
     (POSTv v. &UNIT_TYPE () v * (eff (start + (LENGTH l))))`,
  Induct \\ rw[LIST_TYPE_def]
  >- ( xcf "app" st \\ xmatch \\ xcon \\ xsimpl )
  \\ xcf "app" st
  \\ xmatch
  \\ xlet`POSTv v. &UNIT_TYPE () v * eff (start+1)`
  >- (
    xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"]))
    \\ qexists_tac`0` \\ xsimpl )
  \\ first_x_assum drule
  \\ disch_then(qspec_then`start+1`mp_tac)
  \\ simp[ADD1]
  \\ impl_tac
  >- (
    rw[]
    \\ first_x_assum(qspec_then`n+1`mp_tac)
    \\ simp[EL_CONS,PRE_SUB1] )
  \\ strip_tac \\ xapp)
|> CONV_RULE SWAP_FORALL_CONV
|> Q.SPEC`0` |> SIMP_RULE(srw_ss())[]
|> Q.GENL[`fv`,`eff`]
|> curry save_thm "app_spec";

val result = translate FIND_thm;


val result = translate FILTER;


val result = translate partition_aux_def;
val result = translate mllistTheory.partition_def;


val result = translate FOLDL;
val result = translate foldli_aux_def;
val result = translate foldli_def;


val result = translate FOLDR;
val result = translate (FOLDRi_def |> REWRITE_RULE[o_DEF]);


val result = translate EXISTS_DEF;


val result = next_ml_names := ["all"];
val result = translate EVERY_DEF;


val result = translate SNOC;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
val result = translate tabulate_def;

val result = translate collate_def;

val result = translate zip_def;


(*Extra translations from std_preludeLib.sml *)
val res = translate LENGTH_AUX_def;
(*val res = translate LENGTH_AUX_THM;*)
val result = translate SUM;
val result = translate UNZIP;
val result = translate PAD_RIGHT;
val result = translate PAD_LEFT;
val result = translate (ALL_DISTINCT |> REWRITE_RULE [MEMBER_INTRO]);
val result = translate isPREFIX;
val result = translate FRONT_DEF;
val result = translate (splitAtPki_def |> REWRITE_RULE [SUC_LEMMA])


val front_side_def = Q.prove(
  `!xs. front_side xs = ~(xs = [])`,
  Induct THEN ONCE_REWRITE_TAC [fetch "-" "front_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

val last_side_def = Q.prove(
  `!xs. last_side xs = ~(xs = [])`,
  Induct THEN ONCE_REWRITE_TAC [fetch "-" "last_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;


val nth_side_def = Q.prove(
  `!n xs. nth_side xs n = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "nth_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

val _ =  ml_prog_update (close_module NONE);
val _ = export_theory()
