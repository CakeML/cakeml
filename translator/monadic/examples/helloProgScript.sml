(*
  An example showing how to use the monadic translator to translate
  monadic functions using IO primitives from the basis library.
*)

(* Load the CakeML basic stuff *)
open preamble basisProgTheory

(*
 * Those libraries are used in the translation
 *)
open ml_monad_translatorLib ml_monad_translator_interfaceLib

(* Gives access to monadic IO functions and EvalM theorems *)
open TextIOProofTheory

val _ = new_theory "helloProg"

val _ = translation_extends "basisProg";

(* Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references and I/O. *)
val _ = Datatype `
  state_refs = <| the_num_ref : num
                ; stdio : IO_fs |>`;

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_refs [("the_num_ref", ``0 : num``)] |>
              with_stdio "stdio";


(* A very simple monadic function *)
val simple_fun_def = Define `simple_fun x = return x`;

(* A recursive monadic function *)
val rec_fun_def = Define `
  rec_fun l = dtcase l of []    => return (0 : num)
                        | x::l' => do x <- rec_fun l'; return (1+x) od`;

(* A monadic function calling other monadic functions *)
val calling_fun_def = Define `
  calling_fun l = do x <- rec_fun l; simple_fun x od`;

(* A monadic function using the store *)
val store_fun_def = Define `
  store_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

val io_fun_def = Define `
  io_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

(* Other *)
val if_fun_def = Define `
  if_fun (x : num) y = if x > y then return T else return F`;


(* Initialize the translation *)
val _ = start_translation config;

(* The polymorphism of simple_fun is taken into account *)
val simple_fun_v_thm = simple_fun_def |> m_translate;

(* It is of course possible to translate recursive functions *)
val rec_fun_v_thm = rec_fun_def |> m_translate;

(* And others... *)
val calling_fun_v_thm = calling_fun_def |> m_translate;
val store_fun_v_thm = store_fun_def |> m_translate;
val if_fun_v_thm = if_fun_def |> m_translate;

val _ = overload_on("stdio",``liftM state_refs_stdio stdio_fupd``);

val IMP_STAR_GC = store_thm("IMP_STAR_GC", (* TODO: move *)
  ``(STAR a x) s /\ (y = GC) ==> (STAR a y) s``,
  fs [set_sepTheory.STAR_def]
  \\ rw[] \\ asm_exists_tac \\ fs []
  \\ EVAL_TAC
  \\ fs [set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac `K T` \\ fs []);


val stdio_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD UNIT_TYPE UNIT_TYPE f)
            (MONAD_IO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD UNIT_TYPE UNIT_TYPE (stdio f))
            (STATE_REFS,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.stdio`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_REFS_def"]
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
  \\ fs [fetch "-" "STATE_REFS_def"]
  \\ rw []
  \\ first_x_assum (qspec_then
       `F' * REF_REL NUM the_num_ref st.the_num_ref` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs[ml_monadBaseTheory.liftM_def]
  \\ rw[]);

val EvalM_stdio_print = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE UNIT_TYPE (stdio (print x)))
      (STATE_REFS,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print]);

val _ = add_access_pattern EvalM_stdio_print;
val _ = ignore_type ``:IO_fs``;

val hello_def = Define `
  hello (u:unit) = stdio (print (strlit "Hello")) : (state_refs, unit, unit) M`

val res = m_translate hello_def;

val hello_app_thm = save_thm("hello_app_thm",
  cfMonadLib.mk_app_of_ArrowP res |> SPEC_ALL);

val _ = export_theory ();
