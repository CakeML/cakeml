(*
 * An example showing how to use the monadic translator to translate monadic
 * doubling functions, including using references (no arrays, no exceptions).
 *)

(* Load the CakeML basic stuff *)
open preamble basisProgTheory

(* The ml_monadBaseLib is necessary to define the references and
 * arrays manipulation functions
 * automatically.
 *)
open ml_monadBaseLib
open ml_monadStoreLib

(*
 * Those libraries are used in the translation
 *)
open ml_monad_translatorLib

(* Gives access to monadic IO functions and EvalM theorems *)
open TextIOProofTheory

(* For generating the CF spec *)
open cfMonadLib

val _ = new_theory "doubleProg"

val _ = translation_extends "basisProg";

(* Use monadic syntax: do x <- f y; ... od *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();

(* Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Some overloadings for the parser *)
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Need to hide "state" because of semanticPrimitives *)
val _ = hide "state";

val _ = (use_full_type_names := false);

(* Create the data type to handle the references and I/O.
 *)
val _ = Datatype `
  state_refs = <| the_num_ref : num |>`;

(* Generate the monadic functions to manipulate the reference(s). *)
val refs_access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_ref_name, get_the_num_ref_def, set_the_num_ref_def)] =
        refs_access_funs;

(*
 * It is now possible to use those functions in new definitions:
 *)

(* A basic double function *)
val double_def = Define `double x = if x = 0n then 0 else
                            double (x - 1) + 2n`;

val double_tail_rec_aux_def = Define `
  double_tail_rec_aux n carry = if n = 0n then carry else
                                  double_tail_rec_aux (n - 1) (carry + 2n)`

val double_tail_rec_def = Define `
  (double_tail_rec x = if x = 0n then 0n else double_tail_rec_aux x 0)`

(* A basic monadic double function using references *)
val double_ref_def = Define `
  double_ref x = dtcase x of 0n    => return 0n
                           | SUC v => do
                                        result <- double_ref v;
                                        return (result + 2)
                                      od
`

(* MONADIC TRANSLATION : initialisation *)
(* Define the initial value for the `the_num` reference *)
val init_num_ref_def = Define `init_num = (0 : num)`;
val refs_init_list = [(the_num_ref_name, init_num_ref_def,
                       get_the_num_ref_def, set_the_num_ref_def)];

(* No arrays *)
val rarrays_init_list = [] :
  (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] :
  (string * (int * thm) * thm * thm * thm * thm * thm) list;

(* Name for the store invariant *)
val store_hprop_name = "STATE_STORE";

(* Data-type used for the state *)
val state_type = ``:state_refs``;

(* No exceptions *)
val exn_ri_def = ml_translatorTheory.UNIT_TYPE_def;
val exn_functions = [] : (thm * thm) list;

(* No additional theories where to look for types *)
val type_theories = [] : string list;

(* We don't want to add more conditions than what the monadic translator
   will automatically generate for the store invariant *)
val store_pinv_opt = NONE : (thm * thm) option;

val extra_hprop = NONE;

(* Initialize the translation *)
val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
                rarrays_init_list
                farrays_init_list
                store_hprop_name
                state_type
                exn_ri_def
                exn_functions
                type_theories
                store_pinv_opt
                extra_hprop;

val double_v = double_def |> translate;

val double_tail_rec_aux_v = double_tail_rec_aux_def |> translate;
val double_tail_rec_v = double_tail_rec_def |> translate;

val double_ref_v = double_ref_def |> m_translate;

val double_ref_thm = save_thm("double_ref_thm",
  cfMonadLib.mk_app_of_ArrowP double_ref_v |> SPEC_ALL);

val _ = export_theory ();
