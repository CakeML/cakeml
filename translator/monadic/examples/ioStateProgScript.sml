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
open ml_monad_translatorLib

val _ = new_theory "ioStateProg"

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
  state_refs = <| the_num_ref : num
                ; stdio : IO_fs |>`;

(* Generate the monadic functions to manipulate the reference(s). *)
val refs_access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_ref_name, get_the_num_ref_def, set_the_num_ref_def),
     (stdio_name, get_stdio_def, set_stdio_def)] = refs_access_funs;

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

val extra_hprop = SOME ``STDIO s.stdio``;

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

val print_def = Define `
  print s = (\fs. (Success (), add_stdout fs s)): (IO_fs, unit, unit) M`


open ml_translatorTheory ml_monad_translatorTheory ml_monad_translatorBaseTheory
     bigStepTheory

val st2heap_with_clock = store_thm("st2heap_with_clock[simp]", (* TODO: move *)
  ``st2heap p (s with clock := c) = st2heap p s``,
  fs [cfStoreTheory.st2heap_def]);

val SPLIT3_IMP_STAR_STAR = store_thm("SPLIT3_IMP_STAR_STAR", (* TODO: move *)
  ``!x s1 s2 s3 p1 p2 p3.
      p1 s1 /\ p2 s2 /\ p3 s3 /\ SPLIT3 x (s1,s2,s3) ==> (p1 * p2 * p3) x``,
  fs [set_sepTheory.STAR_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `s1 UNION s2`
  \\ qexists_tac `s3`
  \\ qexists_tac `s1`
  \\ qexists_tac `s2`
  \\ fs [IN_DISJOINT,EXTENSION,IN_UNION,IN_DIFF,set_sepTheory.SPLIT_def,
         cfHeapsBaseTheory.SPLIT3_def]
  \\ metis_tac []);

val GC_T = store_thm("GC_T", (* TODO: move *)
  ``!x. GC x``,
  rw [cfHeapsBaseTheory.GC_def,set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac `K T` \\ fs []);

val st2heap_append_UNION = store_thm("st2heap_new_refs_UNION", (* TODO: move *)
  ``!(st:'ffi semanticPrimitives$state) new_refs p.
      ?x. (st2heap p (st with refs := st.refs ++ new_refs) = st2heap p st UNION x) /\
          DISJOINT (st2heap p st) x``,
  fs [cfAppTheory.st2heap_with_refs_append] \\ rw[]
  \\ `(st with refs := st.refs) = st` by
         fs [semanticPrimitivesTheory.state_component_equality] \\ fs []
  \\ qexists_tac `store2heap_aux (LENGTH st.refs) new_refs DIFF st2heap p st`
  \\ fs [IN_DISJOINT,EXTENSION,IN_UNION,IN_DIFF]
  \\ metis_tac []);

(* TODO statement of theorem *)
val EvalM_print = Q.store_thm("EvalM_print",
  `Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE UNIT_TYPE (print x))
      (STDIO,p:'ffi ffi_proj)`,
  match_mp_tac EvalM_from_app
  \\ qexists_tac `TextIO_print_v` \\ rw []
  \\ fs [print_def]
  \\ metis_tac [TextIOProofTheory.print_spec]);

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
            (STDIO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD UNIT_TYPE UNIT_TYPE (stdio f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.stdio`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = STDIO st.stdio`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  (*\\ qexists_tac `st with stdio := st2`*)
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.stdio` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"]
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
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print]);

val _ = add_access_pattern EvalM_stdio_print;
val _ = ignore_type ``:IO_fs``;

val hello_def = Define `
  hello (u:unit) = stdio (print (strlit "Hello")) : (state_refs, unit, unit) M`

val res = m_translate hello_def;

val hello_app_thm = save_thm("hello_app_thm",
  cfMonadLib.mk_app_of_ArrowP res |> SPEC_ALL);

val _ = export_theory ();
