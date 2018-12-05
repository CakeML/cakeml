(*
  An example showing how to use the monadic translator to translate
  monadic functions using references (no arrays, no exceptions).
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
open ml_monad_translatorLib

(* For IO: print, arguments, name *)
open TextIOProofTheory CommandLineProofTheory

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

val extra_hprop = SOME ``COMMANDLINE s.commandline * MONAD_IO s.stdio``;

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

(* TODO this seems unnecessary ... *)
(*val _ = bring_to_front_overload "print" {Name="print",Thy="TextIOProof"}*)

val fibm_def = Define`
  fibm () =
    do
      (args:mlstring list) <- commandline (arguments ()) ;
      (a:mlstring) <- hd args ;
      n <- str_to_num a ;
      stdio (print (num_to_str (fiba 0 1 n))) ;
      stdio (print (strlit "\n"))
    od otherwise do
            name <- commandline (name ()) ;
            stdio (print_err (strlit"usage: " ^ name ^ strlit" <n>\n"))
          od`

val IMP_STAR_GC = store_thm("IMP_STAR_GC", (* TODO: move *)
  ``(STAR a x) s /\ (y = GC) ==> (STAR a y) s``,
  fs [set_sepTheory.STAR_def]
  \\ rw[] \\ asm_exists_tac \\ fs []
  \\ EVAL_TAC
  \\ fs [set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac `K T` \\ fs []);

(* TODO move *)
val stdio_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty f)
            (MONAD_IO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty (stdio f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.stdio`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = MONAD_IO st.stdio`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then strip_assume_tac
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.stdio` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"]
  \\ rw []
  \\ first_x_assum (qspec_then `COMMANDLINE st.commandline * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def]
  \\ rw []
  \\ fs [set_sepTheory.STAR_COMM]);

(* TODO move *)
val commandline_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty f)
            (COMMANDLINE,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (commandline f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.commandline`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = COMMANDLINE st.commandline`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then strip_assume_tac
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.commandline` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"]
  \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def]
  \\ rw []);

val EvalM_stdio_print = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE STATE_EXN_TYPE (stdio (print x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print]);

val EvalM_stdio_print_err = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Long "TextIO" (Short "print_err")) = SOME TextIO_print_err_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "print_err")); exp])
      (MONAD UNIT_TYPE STATE_EXN_TYPE (stdio (print_err x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print_err]);

val EvalM_commandline_name = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "name")) =
       SOME CommandLine_name_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "name")); exp])
      (MONAD STRING_TYPE STATE_EXN_TYPE (commandline (name x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_name]);

val EvalM_commandline_arguments = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) STATE_EXN_TYPE (commandline (arguments x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_arguments]);

val _ = add_access_pattern EvalM_stdio_print;
val _ = add_access_pattern EvalM_stdio_print_err;
val _ = add_access_pattern EvalM_commandline_name
val _ = add_access_pattern EvalM_commandline_arguments
val _ = ignore_type ``:IO_fs``;

val res = m_translate hd_def
val res = m_translate str_to_num_def

val str_to_num_side = Q.prove (
  `str_to_num_side st1 v2 <=> T`,
  rw [fetch "-" "str_to_num_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val res = translate num_to_str_def
val res = translate fiba_def

val res = m_translate fibm_def

val _ = export_theory ();
