(*
  The user-friendly interface to the monadic translator
*)

structure ml_monad_translator_interfaceLib :>
            ml_monad_translator_interfaceLib = struct

open preamble ml_monadBaseLib ml_monadStoreLib ml_monad_translatorLib
     ml_translatorLib


(******************************************************************************

  Preamble

******************************************************************************)

(* Add monadic syntax: do x <- f y; ... od *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax()

(* Parser overloadings *)
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Hide "state" due to semanticPrimitives *)
val _ = hide "state";

val _ = (use_full_type_names := false);


(******************************************************************************

  Constants and helper functions

******************************************************************************)

fun toUppers(str) = String.implode (map Char.toUpper (String.explode str));
val unit_ty = type_of ``()``;


datatype translator_mode = GLOBAL | LOCAL;


(******************************************************************************

  Define the state of the translation interface

******************************************************************************)

(* Type definition of the user-visible configuration *)
type config = {
  mode              : translator_mode,
  state_type        : hol_type ref,
  exn_type          : hol_type ref,
  exn_access_funs   : {raise_thm:thm, handle_thm:thm} list ref,
  refs              : {name:string, init:thm, get:thm, set:thm} list ref,
  fixed_arrays      : {name:string, init: int * thm, get:thm, set:thm,
                       len:thm, sub:thm, update:thm} list ref,
  resizeable_arrays : {name:string, init:thm, get:thm, set:thm,
                       len:thm, sub:thm, update:thm, alloc:thm} list ref,
  extra_state_inv   : (thm * thm) option ref
                      (* state_inv_def, state_inv_valid *)
}

(* Local-mode translation base state *)
val local_state_config : config = {
  mode              = LOCAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref [],
  extra_state_inv   = ref NONE
};

(* Global-mode translation base state *)
val global_state_config : config = {
  mode              = GLOBAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref [],
  extra_state_inv   = ref NONE
};

(* Type definition of the internal state *)
type state = {
  state_access_funs         : (string * thm * thm) list ref,
                                (* (name, get, set) *)
  store_invariant_name      : string ref,
  store_exn_invariant_name  : string ref,
  exn_type_def              : thm ref,
  additional_type_theories  : string list ref,
  extra_hprop               : term option ref,
  monad_translation_params  : monadic_translation_parameters option ref,
  store_trans_result        : store_translation_result option ref,
  exn_specs                 : (thm * thm) list ref,
  stdio_name                : string option ref,
  commandline_name          : string option ref
};

(* Initial internal state *)
val internal_state : state = {
  state_access_funs        = ref [],
  store_invariant_name     = ref "STATE_STORE",
  store_exn_invariant_name = ref "STATE_EXN",
  exn_type_def             = ref ml_translatorTheory.UNIT_TYPE_def,
  additional_type_theories = ref [],
  extra_hprop              = ref NONE,
  monad_translation_params = ref NONE,
  store_trans_result       = ref NONE,
  exn_specs                = ref [],
  stdio_name               = ref NONE,
  commandline_name         = ref NONE
};



(******************************************************************************

  Translator config setup functions

******************************************************************************)

(*
 *  Set the state store type, and get monadic access functions
 *)
fun with_state state_type (translator_config : config) =
  let val accessors = define_monad_access_funs state_type
  in
    #state_type translator_config := state_type;
    #store_invariant_name internal_state :=
      (state_type |> dest_type |> fst |> toUppers);
    #state_access_funs internal_state := accessors;
    translator_config
  end;

(*
 *  Register the exception type and return the type definition
 *)
fun register_exception_type exn_type =
  let val exn_name = (exn_type |> dest_type |> fst |> toUppers)
      val exn_type_def_name = exn_name ^ "_TYPE_def"
  in (
    register_type ``:unit``;
    register_type ``:'a # 'b``;
    register_type ``:'a list``;
    register_type ``:'a option``;
    register_exn_type exn_type;
    #store_exn_invariant_name internal_state := exn_name;
    theorem exn_type_def_name
  ) end;

(*
 *  Set the exception type, and get monadic exception functions
 *)
fun with_exception exn_type (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val exn_access_funs = if exn_type = unit_ty then [] else
                    define_monad_exception_functions exn_type state_type
      fun to_named_tuple (raise_thm, handle_thm) =
        {raise_thm=raise_thm, handle_thm=handle_thm}
  in
    #exn_type translator_config := exn_type;
    #exn_access_funs translator_config := map to_named_tuple exn_access_funs;
    #exn_type_def internal_state := (register_exception_type exn_type);
    translator_config
  end;

(*
 *  Mark state fields as references.
 *  Define initial values for them.
 *)
fun mk_ref_init (field_name, init_value) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "ref_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val (_, get, set) = first (fn a => field_name = #1 a)
                            (! (#state_access_funs internal_state) )
      fun to_named_tuple (name, init, get, set) =
        {name=name, init=init, get=get, set=set}
  in (field_name, Define `^init_eq`, get, set) |> to_named_tuple end;

fun with_refs refs (translator_config : config) =
  let val refs_init_list = List.map mk_ref_init refs
  in
    #refs translator_config := refs_init_list;
    translator_config
  end

(*
 *  Mark state fields as fixed arrays.
 *  Define initial values, info, and subscript/update exceptions for them.
 *)
fun mk_farray_init (field_name, init_value, init_info, sub_exn, update_exn) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "farray_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val accessors = first (fn a => field_name = #1 a)
                        (! (#state_access_funs internal_state) )
      val (_, get, set, len, sub, update) =
        define_MFarray_manip_funs [accessors] sub_exn update_exn |> hd
      fun to_named_tuple (name, init, get, set, len, sub, upd) =
        {name=name, init=init, get=get, set=set, len=len, sub=sub, update=upd}
  in (field_name, (init_info : int, Define `^init_eq`),
      get, set, len, sub, update) |> to_named_tuple end;

fun with_fixed_arrays farrays (translator_config : config) =
  let val farrays_init_list = List.map mk_farray_init farrays
  in
    #fixed_arrays translator_config := farrays_init_list;
    translator_config
  end;

(*
 *  Mark state fields as resizeable arrays.
 *  Define initial values, and subscript/update exceptions for them.
 *)
fun mk_rarray_init (field_name, init_value, sub_exn, update_exn) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "rarray_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val accessors = first (fn a => field_name = #1 a)
                        (! (#state_access_funs internal_state) )
      val (_, get, set, len, sub, update, alloc) =
        define_MRarray_manip_funs [accessors] sub_exn update_exn |> hd
      fun to_named_tuple (name, init, get, set, len, sub, upd, alloc) =
        {name=name, init=init, get=get, set=set, len=len,
          sub=sub, update=upd, alloc=alloc}
  in
    (field_name, Define `^init_eq`, get, set, len, sub, update, alloc) |>
    to_named_tuple
  end;

fun with_resizeable_arrays rarrays (translator_config : config) =
  let val rarrays_init_list = List.map mk_rarray_init rarrays
  in
    #resizeable_arrays translator_config := rarrays_init_list;
    translator_config
  end;

(*
 *  Mark state fields as stdio.
 *)

fun with_stdio field_name (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val state_type_name = state_type |> dest_type |> fst
      val state_var = mk_var("s", state_type)
      val stdio_field = (* s.stdio *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE field_name]
      val extra_hprop = ``MONAD_IO ^stdio_field``
  in
    #extra_hprop internal_state := (SOME extra_hprop);
    #stdio_name internal_state := (SOME field_name);
    overload_on (field_name,
      Term [
        QUOTE "liftM ",
        QUOTE (state_type_name ^ "_" ^ field_name ^ " "),
        QUOTE (field_name ^ "_fupd")
      ]);
    print ("Overloaded on: ``" ^ field_name ^ "``.\n");
    translator_config
  end

(*
 *  Mark state fields as stdio and commandline.
 *)
fun with_commandline commandline_name stdio_name (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val state_type_name = state_type |> dest_type |> fst
      val state_var = mk_var("s", state_type)
      val stdio_field = (* s.stdio *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE stdio_name]
      val commandline_field = (* s.commandline *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE commandline_name];
      val extra_hprop =
        ``COMMANDLINE ^(commandline_field) * MONAD_IO ^(stdio_field)``
  in
    #extra_hprop internal_state := (SOME extra_hprop);
    #stdio_name internal_state := (SOME stdio_name);
    #commandline_name internal_state := (SOME commandline_name);
    overload_on (stdio_name,
      Term [
        QUOTE "liftM ",
        QUOTE (state_type_name ^ "_" ^ stdio_name ^ " "),
        QUOTE (stdio_name ^ "_fupd")
      ]);
    overload_on (commandline_name,
      Term [
        QUOTE "liftM ",
        QUOTE (state_type_name ^ "_" ^ commandline_name ^ " "),
        QUOTE (commandline_name ^ "_fupd")
      ]);
    print ("Overloaded on: ``" ^ stdio_name ^ "``, ``" ^
           commandline_name ^ "``.\n");
    translator_config
  end

(*
 * Use a user-defined additional state invariant.
 *)
fun with_state_invariant inv_def inv_valid (translator_config : config) =
  let val extra_state_inv = SOME(inv_def, inv_valid)
  in
    #extra_state_inv translator_config := extra_state_inv;
    translator_config
  end;

(******************************************************************************

  Initialisation and translation functions

******************************************************************************)
(* Convert from named tuple to plain tuple, as ml_monad_translatorLib expects *)
fun from_named_tuple_exn {raise_thm=raise_thm, handle_thm=handle_thm} =
  (raise_thm, handle_thm);
fun from_named_tuple_refs {name=name, init=init, get=get, set=set} =
  (name, init, get, set);
fun from_named_tuple_rarray {name=name, init=init, get=get, set=set,
                             len=len, sub=sub, update=upd, alloc=alloc} =
  (name, init, get, set, len, sub, upd, alloc);
fun from_named_tuple_farray
  {name=name, init=init, get=get, set=set, len=len, sub=sub, update=upd} =
    (name, init, get, set, len, sub, upd);

(* Filter out functions unecessary for LOCAL-mode translation *)
fun extract_refs_manip_funs (name, init, get, set) = (name, get, set);
fun extract_rarrays_manip_funs (name, init, get, set, len, sub, upd, alloc) =
      (name, get, set, len, sub, upd, alloc);
fun extract_farrays_manip_funs (name, init, get, set, len, sub, upd) =
      (name, get, set, len, sub, upd);

local
  val IMP_STAR_GC = Q.prove(
    `(STAR a x) s ∧ (y = GC) ⇒ (STAR a y) s`,
    fs [set_sepTheory.STAR_def] >>
    rw [] >> asm_exists_tac >> fs [] >>
    EVAL_TAC >>
    fs [set_sepTheory.SEP_EXISTS_THM] >>
    qexists_tac `K T` >>
    fs []
  )

in

  fun prove_stdio_commandline_intros stdio_name commandline_name = let
    val stdio = Term [QUOTE stdio_name] |> Term.inst [alpha |-> unit_ty]
    val commandline = Term [QUOTE commandline_name]
    val st_stdio = Term [QUOTE "st.", QUOTE stdio_name]
    val st_commandline = Term [QUOTE "st.", QUOTE commandline_name]
    val store_inv_name = ( !(#store_invariant_name internal_state) )
    val state_predicate = Term [QUOTE store_inv_name]
    val stdio_intro =
      Q.prove(
        ` (∀ st . EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty f) (MONAD_IO, p:'ffi ffi_proj))
        ⇒
          (∀ st . EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty (^stdio f))
              (^state_predicate, p:'ffi ffi_proj))`,

        fs [ml_monad_translatorTheory.EvalM_def] >> rw [] >>
        first_x_assum (qspecl_then [`^st_stdio`,`s`] mp_tac) >>
        impl_tac
        >- (
          fs [ml_monad_translatorBaseTheory.REFS_PRED_def] >>
          fs [fetch "-" (store_inv_name ^ "_def")] >>
          qabbrev_tac `a = MONAD_IO ^st_stdio` >>
          qabbrev_tac `b = GC` >>
          fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM] >>
          last_x_assum mp_tac >>
          metis_tac [IMP_STAR_GC]
        ) >>
        disch_then strip_assume_tac >>
        asm_exists_tac >> fs [] >>
        fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
            semanticPrimitivesTheory.state_component_equality] >>
        rveq >> fs [ml_monad_translatorTheory.MONAD_def] >>
        Cases_on `f ^st_stdio` >> fs [] >>
        EVERY_CASE_TAC >>
        rveq >> fs [] >>
        fs [fetch "-" (store_inv_name ^ "_def")] >>
        rw [] >>
        first_x_assum (qspec_then `COMMANDLINE ^st_commandline * F'` mp_tac) >>
        fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC] >>
        fs [ml_monadBaseTheory.liftM_def] >>
        rw [] >>
        fs [set_sepTheory.STAR_COMM]
      )
    val commandline_intro =
      Q.prove(
        ` (∀st. EvalM ro env st exp
            (MONAD ret_ty exc_ty f) (COMMANDLINE, p:'ffi ffi_proj))
        ⇒
          (∀st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (^commandline f))
              (^state_predicate, p:'ffi ffi_proj))`,
        fs [ml_monad_translatorTheory.EvalM_def] >> rw [] >>
        first_x_assum (qspecl_then [`^st_commandline`,`s`] mp_tac) >>
        impl_tac
        >- (
          fs [ml_monad_translatorBaseTheory.REFS_PRED_def] >>
          fs [fetch "-" (store_inv_name ^ "_def")] >>
          qabbrev_tac `a = COMMANDLINE ^st_commandline` >>
          qabbrev_tac `b = GC` >>
          fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM] >>
          last_x_assum mp_tac >>
          metis_tac [IMP_STAR_GC]
        ) >>
        disch_then strip_assume_tac >>
        asm_exists_tac >> fs [] >>
        fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
            semanticPrimitivesTheory.state_component_equality] >>
        rveq >> fs [ml_monad_translatorTheory.MONAD_def] >>
        Cases_on `f ^st_commandline` >> fs [] >>
        EVERY_CASE_TAC >>
        rveq >> fs [] >>
        fs [fetch "-" (store_inv_name ^ "_def")] >>
        rw [] >>
        first_x_assum (qspec_then `MONAD_IO ^st_stdio * F'` mp_tac) >>
        fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC] >>
        fs [ml_monadBaseTheory.liftM_def] >>
        rw []
      )
  in
    save_thm("stdio_INTRO", stdio_intro);
    save_thm("commandline_INTRO", commandline_intro);
    (stdio_intro, commandline_intro)
  end;

  fun add_stdio_access_patterns stdio_name stdio_intro_thm =
    let val store_inv_name = ( !(#store_invariant_name internal_state) )
        val state_predicate = Term [QUOTE store_inv_name]
        val state_exn_name = ( !(#store_exn_invariant_name internal_state) )
        val state_exn_predicate = Term [QUOTE state_exn_name, QUOTE "_TYPE"]
        val state_exn_ty =
          state_exn_predicate |> type_of |> dest_type |> snd |> hd
        val stdio = Term [QUOTE stdio_name] |>
                    Term.inst [alpha |-> unit_ty, beta |-> state_exn_ty]

        val EvalM_stdio_print =
          Q.prove(
            ` Eval env exp (STRING_TYPE x) ∧
              (nsLookup env.v (Short "print") = SOME TextIO_print_v)
            ⇒
              EvalM F env st (App Opapp [Var (Short "print"); exp])
                (MONAD UNIT_TYPE ^state_exn_predicate (^stdio (print x)))
                (^state_predicate, p:'ffi ffi_proj)`,
            metis_tac [stdio_intro_thm, TextIOProofTheory.EvalM_print]
          )
        val EvalM_stdio_print_err =
          Q.prove(
            ` Eval env exp (STRING_TYPE x) ∧
              (nsLookup env.v (Long "TextIO" (Short "print_err")) =
                SOME TextIO_print_err_v)
            ⇒
              EvalM F env st
                (App Opapp [Var (Long "TextIO" (Short "print_err")); exp])
                (MONAD UNIT_TYPE ^state_exn_predicate (^stdio (print_err x)))
                (^state_predicate, p:'ffi ffi_proj)`,
            metis_tac [stdio_intro_thm, TextIOProofTheory.EvalM_print_err]
          )
    in
      save_thm("EvalM_" ^ stdio_name ^ "_print", EvalM_stdio_print);
      save_thm("EvalM_" ^ stdio_name ^ "_print_err", EvalM_stdio_print_err);
      print("Saved EvalM theorems for "^stdio_name^": print, print_err.\n");
      add_access_pattern EvalM_stdio_print;
      add_access_pattern EvalM_stdio_print_err;
      print("Added access patterns for "^stdio_name^": print, print_err.\n");
      ignore_type ``:IO_fs``
    end

  fun add_commandline_access_patterns commandline_name commandline_intro_thm =
    let val store_inv_name = ( !(#store_invariant_name internal_state) )
        val state_predicate = Term [QUOTE store_inv_name]
        val state_exn_name = ( !(#store_exn_invariant_name internal_state) )
        val state_exn_predicate = Term [QUOTE state_exn_name, QUOTE "_TYPE"]
        val state_exn_ty =
          state_exn_predicate |> type_of |> dest_type |> snd |> hd
        val commandline = Term [QUOTE commandline_name] |>
                          Term.inst [alpha |-> ``:mlstring``,
                                     beta |-> state_exn_ty]
        val commandline_list = Term [QUOTE commandline_name] |>
                               Term.inst [alpha |-> ``:mlstring list``,
                                          beta |-> state_exn_ty]


        val EvalM_commandline_name =
          Q.prove(
            ` Eval env exp (UNIT_TYPE x) ∧
              (nsLookup env.v (Long "CommandLine" (Short "name")) =
                SOME CommandLine_name_v)
            ⇒
              EvalM F env st
                (App Opapp [Var (Long "CommandLine" (Short "name")); exp])
                (MONAD STRING_TYPE ^state_exn_predicate (^commandline
                  (name x : mlstring list ->
                    (mlstring, ^(ty_antiq state_exn_ty)) exc # mlstring list)
                  ))
                (^state_predicate, p:'ffi ffi_proj)`,
            metis_tac [commandline_intro_thm, CommandLineProofTheory.EvalM_name]
          )

        val EvalM_commandline_arguments =
          Q.prove(
            ` Eval env exp (UNIT_TYPE x) ∧
              (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
                SOME CommandLine_arguments_v)
            ⇒
              EvalM F env st
                (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
                (MONAD (LIST_TYPE STRING_TYPE) ^state_exn_predicate
                  (^commandline_list (arguments x : mlstring list ->
                    (mlstring list, ^(ty_antiq state_exn_ty)) exc # mlstring list)
                  ))
                (^state_predicate, p:'ffi ffi_proj)`,
            metis_tac [commandline_intro_thm,
                       CommandLineProofTheory.EvalM_arguments]
          )
    in
      save_thm("EvalM_" ^ commandline_name ^ "_print", EvalM_commandline_name);
      save_thm("EvalM_" ^ commandline_name ^ "_print_err",
               EvalM_commandline_arguments);
      print("Saved EvalM theorems for " ^ commandline_name ^
            ": name, arguments.\n");
      add_access_pattern EvalM_commandline_name;
      add_access_pattern EvalM_commandline_arguments;
      print("Added access patterns for " ^ commandline_name ^
            ": name, arguments.\n")
    end

  fun add_access_patterns () =
    case ( !(#stdio_name internal_state) ) of SOME stdio_name => (
      case ( !(#commandline_name internal_state) ) of
          SOME commandline_name => (* both commandline and stdio *)
            let val (stdio_intro, commandline_intro) =
              prove_stdio_commandline_intros stdio_name commandline_name
            in
              add_stdio_access_patterns stdio_name stdio_intro;
              add_commandline_access_patterns commandline_name commandline_intro
            end
        | NONE => (* only stdio, no commandline TODO *)
          ()
      )

    | NONE => () (* no stdio, so no access patterns *)


end (* end local *)

(* Initialise the translation *)
fun start_translation (translator_config : config) =
  let val c = translator_config
      val s = internal_state in (
  case (#mode translator_config) of
    GLOBAL => let val (monad_trans_params, store_trans_result, exn_specs) =
      start_static_init_fixed_store_translation
          ((!(#refs                     c) ) |> map from_named_tuple_refs)
          ((!(#resizeable_arrays        c) ) |> map from_named_tuple_rarray)
          ((!(#fixed_arrays             c) ) |> map from_named_tuple_farray)
          ( !(#store_invariant_name     s) )
          ( !(#state_type               c) )
          ( !(#exn_type_def             s) )
          ((!(#exn_access_funs          c) ) |> map from_named_tuple_exn)
          ( !(#additional_type_theories s) )
          ( !(#extra_state_inv          c) )
          ( !(#extra_hprop              s) )
        in
          #monad_translation_params s := SOME monad_trans_params;
          #store_trans_result       s := SOME store_trans_result;
          #exn_specs                s := exn_specs;
          add_access_patterns ()
        end
  | LOCAL => let val (monad_trans_params, exn_specs) =
      start_dynamic_init_fixed_store_translation
          ((!(#refs                     c) ) |> map from_named_tuple_refs |>
                                                map extract_refs_manip_funs)
          ((!(#resizeable_arrays        c) ) |> map from_named_tuple_rarray |>
                                                map extract_rarrays_manip_funs)
          ((!(#fixed_arrays             c) ) |> map from_named_tuple_farray |>
                                                map extract_farrays_manip_funs)
          ( !(#store_invariant_name     s) )
          ( !(#state_type               c) )
          ( !(#exn_type_def             s) )
          ((!(#exn_access_funs          c) ) |> map from_named_tuple_exn)
          ( !(#additional_type_theories s) )
          ((!(#extra_state_inv          c) ) |> Option.map fst)
        in
          #monad_translation_params s := SOME monad_trans_params;
          #exn_specs                s := exn_specs
        end
) end;






(* Translation functions from ml_translatorLib *)
val translate = ml_translatorLib.translate;
val translation_extends = ml_translatorLib.translation_extends;
val update_precondition = ml_translatorLib.update_precondition;

(* Translation functions from ml_monad_translatorLib *)
val register_type = ml_monad_translatorLib.register_type;
val m_translate = ml_monad_translatorLib.m_translate;
val m_translate_run = ml_monad_translatorLib.m_translate_run;

(*
 * From ml_translatorLib
 *
 * Resume prior monadic translation.
 * Loads the state specific to the monadic translation from the specified
 * theory, followed by a call to translation_extends from the 'standard'
 * translator (i.e. fetching the rest of the translator state).
 *)
val m_translation_extends = ml_monad_translatorLib.m_translation_extends;

end (* end struct *)
