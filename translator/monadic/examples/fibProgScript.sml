(*
 * An example showing how to use the monadic translator to translate monadic functions
 * using references (no arrays, no exceptions).
 *)

(* Load the CakeML basic stuff *)
open preamble basisProgTheory

(* The ml_monadBaseLib is necessary to define the references and arrays manipulation functions
 * automatically.
 *)
open ml_monadBaseLib
open ml_monadStoreLib

(*
 * Those libraries are used in the translation
 *)
open (* ml_monad_translatorTheory *) ml_monad_translatorLib

val _ = new_theory "fibProg"

val _ = translation_extends "basisProg";

(* Use monadic syntax: do x <- f y; ... od *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();

(* Pattern matching
 * Note that `dtcase` has to be used from now on in the function definitions (and not `case`)
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
  state_refs = <| commandline : mlstring list
                ; stdio : IO_fs |>`;

(* Generate the monadic functions to manipulate the reference(s). *)
val refs_access_funs = define_monad_access_funs (``:state_refs``);
val [(commandline_name, get_commandline_def, set_commandline_def),
     (stdio_name, get_stdio_def, set_stdio_def)] = refs_access_funs;

(* Those functions too can be defined by hand:

val get_the_num_ref_def =
Define `get_the_num_ref = \(state : state_refs). (Success state.the_num, state)`;

val set_the_num_ref_def =
Define `set_the_num_ref n = \(state : state_refs). (Success (), state with the_num := n)`;

val access_funs = [("the_num_ref", get_the_num_ref_def, set_the_num_ref_def)];

*)


(* MONADIC TRANSLATION : initialisation *)
(* Define the initial value for the `the_num` reference *)
val refs_init_list = [] : (string * thm * thm * thm) list;

(* No arrays *)
val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

(* Name for the store invariant *)
val store_hprop_name = "STATE_STORE";

(* Data-type used for the state *)
val state_type = ``:state_refs``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail`;

(* It is necessary to register that type for the CakeML program to be able to use it*)
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";
val exn_ri_def = STATE_EXN_TYPE_def
val exn_functions = define_monad_exception_functions ``:state_exn`` state_type;

(* No additional theories where to look for types *)
val type_theories = [] : string list;

(* We don't want to add more conditions than what the monadic translator will automatically generate for the store invariant *)
val store_pinv_opt = NONE : (thm * thm) option;

val extra_hprop = SOME ``COMMANDLINE s.commandline * STDIO s.stdio``;

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

val _ = overload_on("stdio",``liftM state_refs_stdio stdio_fupd``);
val _ = overload_on("commandline",``liftM state_refs_commandline commandline_fupd``);

val print_def = Define `
  print s = (\fs. (Success (), add_stdout fs s)): (IO_fs, unit, 'a) M`

val print_err_def = Define `
  print_err s = (\fs. (Success (), add_stderr fs s)): (IO_fs, unit, 'a) M`

val name_def = Define `
  name (u:unit) = (\cl. (Success (HD cl), cl)): (mlstring list, mlstring, 'a) M`

val arguments_def = Define `
  arguments (u:unit) = (\cl. (Success (TL cl), cl)): (mlstring list, mlstring list, 'a) M`

val hd_def = Define `
  hd l = dtcase l of [] => raise_Fail | x::l' => return x`;

val str_to_num_def = Define `
  str_to_num (s:mlstring) =
    dtcase mlint$fromString s of
      NONE => raise_Fail
    | SOME i => if i < 0i then raise_Fail else return (Num i)`;

val fiba_def = Define`
  fiba i j n = if n = 0n then (i:num) else fiba j (i+j) (n-1)`;

val num_to_str_def = Define `
  num_to_str (n:num) = mlint$toString (& n)`

val fibm_def = Define`
  fibm () =
    do
      (args:mlstring list) <- commandline (arguments ()) ;
      (a:mlstring) <- hd args ;
      n <- str_to_num a ;
      stdio (print (num_to_str (fiba 0 1 n))) ;
      stdio (print (strlit "\n"))
    od ++ do
            n <- commandline (name ()) ;
            stdio (print_err (strlit"usage: " ^ n ^ strlit" <n>\n"))
          od`

val _ = export_theory ();
