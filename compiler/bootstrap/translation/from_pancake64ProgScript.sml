(*
  Translate the pan_to_target part of the 64-bit compiler.
*)

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory std_preludeTheory;
local open backendTheory in end

val _ = new_theory "from_pancake64Prog"

val _ = translation_extends "to_target64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake64Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

  val def = def |> RW (!extra_preprocessing)
                |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

open panLangTheory;

(*
val _ = register_type “:shift”;
*)
(*
Theorem EqualityType_STRING_TYPE:
  EqualityType HOL_STRING_TYPE ⇒ EqualityType STRING_TYPE
Proof
  rw [EqualityType_def] >> rw [STRING_TYPE_def] >> rw [HOL_STRING_TYPE_def]
  >> qsuff_tac “STRING_TYPE x1 v1 ⇒ HOL_STRING_TYPE x1 v1”
QED
val _ = register_type “:sname”;

val _ = register_type “:varname”;

val _ = register_type “:funname”;

val _ = register_type “:eid”;

val _ = register_type “:decname”;
*)
val _ = register_type “:64 panLang$exp”;


Datatype:
  container = Container('a)
End

Datatype:
  thing = Thing(thing container) | NonThing
End

Datatype:
  my_option = MySome('a) | MyNone
End
val _ = register_type “:'a my_option”;

Datatype:
  thing = Thing(thing my_option) | NonThing
End

Datatype:
  thing2 = Thing(thing2 list) | NonThing
End

val _ = register_type “:'a container”;
val _ = register_type “:thing”;
val _ = register_type “:thing2”;
(*
  load "Definition"
*)

val _ = register_type “:64 panLang$prog”;

open pan_simpTheory;

val _ = translate seq_assoc_def;

val _ = translate compile_def;

val _ = translate compile_prog_def;

open pan_to_wordTheory;

val _ = translate $ spec64 compile_prog_def;

open pan_to_targetTheory;

val _ = translate $ spec64 compile_prog_def;
