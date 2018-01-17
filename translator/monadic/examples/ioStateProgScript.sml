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

val _ = new_theory "ioStateProg"

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
val _ = Hol_datatype `
  state_refs = <| the_num_ref : num
                ; file_io : IO_fs |>`;

(* Generate the monadic functions to manipulate the reference(s). *)
val refs_access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_ref_name, get_the_num_ref_def, set_the_num_ref_def),
     (file_io_name, get_file_io_def, set_file_io_def)] = refs_access_funs;

val print_def = Define `
  print s = do fs <- get_file_io ; set_file_io (add_stdout fs s) od`

(* Those functions too can be defined by hand:

val get_the_num_ref_def =
Define `get_the_num_ref = \(state : state_refs). (Success state.the_num, state)`;

val set_the_num_ref_def =
Define `set_the_num_ref n = \(state : state_refs). (Success (), state with the_num := n)`;

val access_funs = [("the_num_ref", get_the_num_ref_def, set_the_num_ref_def)];

*)

(*
 * It is now possible to use those functions in new definitions:
 *)

(* A very simple monadic function *)
val simple_fun_def = Define `simple_fun x = return x`;

(* A recursive monadic function *)
val rec_fun_def = Define `rec_fun l = dtcase l of [] => return (0 : num)
					      | x::l' => do x <- rec_fun l'; return (1+x) od`;

(* A monadic function calling other monadic functions *)
val calling_fun_def = Define `calling_fun l = do x <- rec_fun l; simple_fun x od`;

(* A monadic function using the store *)
val store_fun_def = Define `store_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

val io_fun_def = Define `
  io_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

(* Other *)
val if_fun_def = Define `if_fun (x : num) y = if x > y then return T else return F`;

(* ... *)

(* MONADIC TRANSLATION : initialisation *)
(* Define the initial value for the `the_num` reference *)
val init_num_ref_def = Define `init_num = (0 : num)`;
val refs_init_list = [(the_num_ref_name, init_num_ref_def, get_the_num_ref_def, set_the_num_ref_def)];

(* No arrays *)
val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

(* Name for the store invariant *)
val store_hprop_name = "STATE_STORE";

(* Data-type used for the state *)
val state_type = ``:state_refs``;

(* No exceptions *)
val exn_ri_def = ml_translatorTheory.UNIT_TYPE_def;
val exn_functions = [] : (thm * thm) list;

(* No additional theories where to look for types *)
val type_theories = [] : string list;

(* We don't want to add more conditions than what the monadic translator will automatically generate for the store invariant *)
val store_pinv_opt = NONE : (thm * thm) option;

val extra_hprop = SOME ``STDIO s.file_io``;

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

(* The polymorphism of simple_fun is taken into account *)
val simple_fun_v_thm = simple_fun_def |> m_translate;

(* It is of course possible to translate recursive functions *)
val rec_fun_v_thm = rec_fun_def |> m_translate;

(* And others... *)
val calling_fun_v_thm = calling_fun_def |> m_translate;
val store_fun_v_thm = store_fun_def |> m_translate;
val if_fun_v_thm = if_fun_def |> m_translate;

(* ...

m2deep
val tm = ``set_the_num_ref 0 : (state_refs, unit, unit) M``

val EvalM_print = prove(
  ``Eval env exp (STRING_TYPE x) ==>
    EvalM env st (App Opassign [Var (Short "print"); exp])
      (MONAD UNIT_TYPE UNIT_TYPE (print_foo x))
      (STDIO,p:'ffi ffi_proj)``,
  cheat);

val EvalM_print = prove(
  ``Eval env exp (STRING_TYPE x) ==>
    EvalM env st (App Opassign [Var (Short "print"); exp])
      (MONAD UNIT_TYPE UNIT_TYPE (print x))
      ((λs. STDIO s.file_io),p:'ffi ffi_proj)``,
  cheat);

val th = EvalM_print |> UNDISCH;
val tm = th |> concl |> rator |> rand |> rand;

val _ = (access_patterns := (tm,th)::(!access_patterns));

m2deep ``print (strlit "hi") : (state_refs, unit, unit) M``

hol2deep ``strlit "hi"``

*)

val _ = export_theory ();
