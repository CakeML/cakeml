open preamble;
open inferTheory inferSoundTheory inferPropsTheory unifyTheory ml_repl_stepTheory;
open ml_translatorTheory sideTheory;

val _ = new_theory "ml_repl_module";

val _ = ml_translatorLib.translation_extends "ml_repl_step";
val _ = ml_translatorLib.update_precondition repl_step_side_thm;

fun add_Ref_NONE_decl name = let
  val decl_assum_x = ml_translatorLib.hol2deep ``(NONE:'a option)``
    |> DISCH_ALL
    |> ml_translatorLib.clean_lookup_cons
    |> Q.INST [`shaddow_env`|->`env`]
    |> REWRITE_RULE []
    |> UNDISCH_ALL
    |> MATCH_MP Eval_IMP_always_evaluates
    |> MATCH_MP always_evaluates_ref
    |> DISCH (ml_translatorLib.get_DeclAssum ())
    |> Q.GENL [`tys`,`env`]
    |> MATCH_MP DeclAssumExists_evaluate
    |> SPEC (stringSyntax.fromMLstring name)
  val tm = (ml_translatorLib.get_DeclAssum ())
  val x = tm |> rator |> rator |> rand
  val y = decl_assum_x |> concl |> rand
  val tm = subst [x|->rand y] tm
  val th = TRUTH |> DISCH tm |> UNDISCH
  val pres = []
  in ml_translatorLib.store_cert th pres decl_assum_x end;

val _ = add_Ref_NONE_decl "input";
val _ = add_Ref_NONE_decl "output";

val add_call_repl_step_decl = let
  val name = "call_repl_step"
  val exp =
    ``App Opassign [Var (Short "output");
        App Opapp [Var (Short "repl_step");
          App Opderef [Var (Short "input")]]]``
  val decl_assum_x = always_evaluates_fn
    |> Q.SPECL [`"u"`,`^exp`,`env`]
    |> DISCH (ml_translatorLib.get_DeclAssum ())
    |> Q.GENL [`tys`,`env`]
    |> MATCH_MP DeclAssumExists_evaluate
    |> SPEC (stringSyntax.fromMLstring name)
  val tm = (ml_translatorLib.get_DeclAssum ())
  val x = tm |> rator |> rator |> rand
  val y = decl_assum_x |> concl |> rand
  val tm = subst [x|->rand y] tm
  val th = TRUTH |> DISCH tm |> UNDISCH
  val pres = []
  in ml_translatorLib.store_cert th pres decl_assum_x end;

val module_thm = let
  val th = ml_translatorLib.finalise_module_translation ()
  val thms = th |> Q.SPEC `NONE` |> CONJUNCTS
  in CONJ (hd thms) (last thms) end;

val _ = save_thm("module_thm", module_thm);

val _ = save_thm("equality_types",
  LIST_CONJ (ml_translatorLib.eq_lemmas()));

val _ = Theory.delete_binding "side_translator_state_thm";

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
