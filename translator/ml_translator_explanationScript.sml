(*
  An explanation of what the translator produces.
*)
open HolKernel Parse boolLib bossLib;

open ml_translatorLib;

val _ = new_theory "ml_translator_explanation";

(* ------------------------------------------------------------------- *
   Function definition
 * ------------------------------------------------------------------- *)

Definition id_def:
  id (x:'a) = x
End

(* ------------------------------------------------------------------- *
   Translation of id function
 * ------------------------------------------------------------------- *)

val id_v_thm = translate id_def;

(* The line above id_v value and proves that id is related to id_v:

    ⊢ (a --> a) id id_v

   This should be understand as saying that id_v behaves as function
   id for any input type a if the output type is the same a.

   The call to translate also adds id_v to the CakeML program that
   the translator is building. *)

(* ------------------------------------------------------------------- *
   Inspecting the accumulated CakeML program
 * ------------------------------------------------------------------- *)

(* The following lines asks the translator for the CakeML program that
   it's building. *)

val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,
                   fetch "-" (current_theory() ^ "_env_def")];

(* When evaluated, the above lines produce a theorem:

   ⊢ Decls (ML_code_env init_env []) (init_state ffi)
       [Dlet unknown_loc (Pvar "id") (Fun "v1" (Var (Short "v1")))]
       (write "id" id_v empty_env) (init_state ffi)

   This should be read as: if evaluation starts from the init_env
   environment and init_state state, then running through the list of
   declarations, in this case only on declaration ‘[Dlet ...]’, then
   the resulting environment update is

        write "id" id_v empty_env

   i.e. an environment where the id_v value has been bound to the name
   "id". This evaluation did not modify the state, which is still
   init_state, as can be seen in the last part of the Decls theorem.

   In the declarations list above, i.e.

       [Dlet unknown_loc (Pvar "id") (Fun "v1" (Var (Short "v1")))]

   one can see the generated code. In concrete syntax, the code is:

       val id = (fn v1 => v1);
*)

val _ = export_theory();
