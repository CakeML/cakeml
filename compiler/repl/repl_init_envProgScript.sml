(*
  This file partially instantiates the eval_state and inserts a Denv declaration.
*)
Theory repl_init_envProg
Ancestors
  ml_translator repl_moduleProg
Libs
  preamble ml_translatorLib ml_progLib

val _ = translation_extends "repl_moduleProg";

(* we set the env_id_counter field of the eval_state *)

val _ = ml_prog_update (ml_progLib.set_eval_state
          “EvalDecs (eval_state_var with env_id_counter := (0,0,1))”)

(* we declare a Denv *)

val s = get_ml_prog_state () |> get_state
val env = get_ml_prog_state () |> get_env

Theorem declare_env_thm[local]:
  declare_env_rel ^s ^env
    (^s with eval_state := SOME (EvalDecs (eval_state_var with env_id_counter := (0,1,1))))
    (Env ^env (0,0))
Proof
  fs [semanticPrimitivesTheory.declare_env_def,ml_progTheory.declare_env_rel_def]
QED

val () = ml_prog_update (ml_progLib.add_Denv declare_env_thm "repl_init_env");

