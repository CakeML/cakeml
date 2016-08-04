open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open std_preludeTheory;

val _ = new_theory "compiler64Prog"

(* temporary *)
val _ = translation_extends "std_prelude";

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val insts = ref ([]:{redex:hol_type,residue:hol_type}list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> INST_TYPE (!insts)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

(* Attempts at translating bvp_to_word things *)
open data_to_wordTheory

val _ = translate adjust_set_def

(* TODO: Variable length shift: n2w len << l and ||
val _ = translate make_header_def
*)

(*
TODO: Not sure how to translate things that take the 'a as an arg...
val _ = translate (conv64_RHS shift_def)
*)

(* TODO: ¬, --
val _ = translate all_ones_def
*)

open word_simpTheory

(* TODO: This method of forcing defs to be instantiated at :64 isn't very neat. find_def_for_const should instead use some way of finding (and automatically instantiating) type variables that are FCPs *)

val _ = insts:= [alpha |-> ``:64``]
val _ = translate (spec64 Seq_assoc_def)
val _ = translate (spec64 compile_exp_def)

val _ = export_theory();
