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

val st2heap_with_clock = store_thm("st2heap_with_clock[simp]",
  ``st2heap p (s with clock := c) = st2heap p s``,
  fs [cfStoreTheory.st2heap_def]);

(* TODO cfAppTheory copy-paste *)
val evaluate_list_SING = Q.prove(
  `bigStep$evaluate_list b env st [exp] (st', Rval [v]) <=>
    bigStep$evaluate b env st exp (st', Rval v)`,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]);

val EvalM_print = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE UNIT_TYPE (print x))
      (STDIO,p:'ffi ffi_proj)``,
  rw [EvalM_def, Eval_def]
  \\ first_x_assum (qspec_then `s.refs++junk` strip_assume_tac)
  \\ drule (GEN_ALL TextIOProofTheory.print_spec)
  \\ simp [cfAppTheory.app_def, cfAppTheory.app_basic_def]
  \\ disch_then (mp_tac o CONV_RULE (RESORT_FORALL_CONV rev))
  \\ fs [REFS_PRED_def, set_sepTheory.STAR_def]
  \\ sg `?hk. SPLIT (st2heap p (s with refs := s.refs ++ junk ++ refs')) (u, hk)`
  >- cheat (* TODO *)
  \\ rpt (disch_then drule) \\ rw []
  \\ fs [cfHeapsBaseTheory.POSTv_def]
  \\ Cases_on `r` \\ fs [set_sepTheory.cond_def]
  \\ rw [Once evaluate_cases, PULL_EXISTS]
  \\ rw [Once (el 2 (CONJUNCTS evaluate_cases)), PULL_EXISTS]
  \\ rw [Once (el 2 (CONJUNCTS evaluate_cases)), PULL_EXISTS]
  \\ rw [Once (el 2 (CONJUNCTS evaluate_cases)), PULL_EXISTS]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `Rval v'` \\ fs [PULL_EXISTS]
  \\ fs [UNIT_TYPE_def]
  \\ rw [MONAD_def, print_def, PULL_EXISTS]
  \\ mp_tac ((Q.SPEC `s with refs := s.refs++junk` o
              CONV_RULE SWAP_FORALL_CONV o GEN_ALL)
             evaluate_empty_state_IMP) \\ fs []
  \\ disch_then drule \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac `do_opapp [a;_]`
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qexists_tac `a` \\ fs [Abbr`a`]
  \\ rw [Once evaluate_cases]
  \\ fs [cfAppTheory.evaluate_ck_def]
  \\ fs [funBigStepEquivTheory.functional_evaluate_list]
  \\ qhdtm_x_assum `evaluate_list` assume_tac
  \\ fs [Once (el 2 (CONJUNCTS evaluate_cases))]
  \\ fs [Once (el 2 (CONJUNCTS evaluate_cases))] \\ rw []
  \\ drule (GEN_ALL cfAppTheory.big_remove_clock) \\ fs []
  \\ disch_then (qspec_then `s.clock` assume_tac) \\ fs []
  \\ qpat_x_assum `evaluate T _ _ _ _` kall_tac
  \\ qmatch_assum_abbrev_tac `_ s3 _ _`
  \\ `s3 = s with refs := s.refs ⧺ junk ⧺ refs'` by
    fs [Abbr`s3`,semanticPrimitivesTheory.state_component_equality]
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ fs [REFS_PRED_FRAME_def]
  \\ simp [Once set_sepTheory.STAR_def,PULL_EXISTS]
  \\ rw []
  (* here we can't prove that u and u' are the same, instead we need
     to have the original theorem and instantiate it again *)
  \\ cheat (* TODO *));

val _ = overload_on("stdio",``liftM state_refs_stdio stdio_fupd``);

val IMP_STAR_GC = store_thm("IMP_STAR_GC",
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
