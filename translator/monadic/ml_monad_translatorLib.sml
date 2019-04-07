(*
  The ML code that implements the main part of the monadic translator.
*)

structure ml_monad_translatorLib :> ml_monad_translatorLib = struct

(******************************************************************************)

open preamble
     astTheory libTheory semanticPrimitivesTheory evaluateTheory
     ml_translatorTheory ml_progTheory ml_progLib
     ml_pmatchTheory ml_monadBaseTheory ml_monad_translatorBaseTheory
     ml_monad_translatorTheory terminationTheory cfTacticsLib
     Net List packLib stringSimps
open ml_monadBaseLib

open ml_monadStoreLib

(******************************************************************************

  Global library variables.

******************************************************************************)
(* TODO add useful debug/info printing *)
val DEBUG = false;
val INFO = true;

fun info_print msg term =
  if INFO then
    print (msg ^ ": " ^ (term_to_string term) ^ "\n" )
  else ();

fun debug_print msg term =
  if DEBUG then
    print (msg ^ ": " ^ (term_to_string term) ^ "\n" )
  else ();

fun debug_print_ty msg typ =
  if DEBUG then
    print (msg ^ ": " ^ (type_to_string typ) ^ "\n" )
  else ();

val _ = (print_asts := true);


(******************************************************************************

  Get constant terms and types from ml_monad_translatorTheory.
  Prevents parsing in the wrong context.

******************************************************************************)

val get_term = let
  val term_list = unpack_list (unpack_pair unpack_string unpack_term)
                  ml_monad_translatorTheory.parsed_terms
  in fn str => (first (fn (name,_) => name = str) term_list) |> snd end;

val get_type = let
  val term_list = unpack_list (unpack_pair unpack_string unpack_type)
                  ml_monad_translatorTheory.parsed_types
  in fn str => (first (fn (name,_) => name = str) term_list) |> snd end;

(* Some constant types *)
val exp_ty = get_type "exp";
val string_ty = get_type "string_ty";
val a_ty = alpha;
val b_ty = beta;
val c_ty = gamma;
val bool_ty = type_of T;
val unit_ty = get_type "unit";
val pair_ty = get_type "pair";
val num_ty = get_type "num";
val venvironment = mk_environment v_ty (* :v sem_env *);
val poly_M_type = get_type "poly_M_type" (* :α -> (β, γ) exc # α *);
val v_bool_ty = get_type "v_bool_ty" (* :v -> bool *);
val hprop_ty = get_type "hprop_ty" (* :hprop = :(heap_part -> bool) -> bool *);
val recclosure_exp_ty = get_type "recclosure_exp_ty";
val exc_ty = get_type "exc_ty";
val v_list_ty = get_type "v_list";
val ffi_ty_var = get_type "ffi";
val register_pure_type_pat = get_type "register_pure_type_pat";

(* Some constant terms *)
val v_env = mk_var("env",venvironment);
val exp_var = mk_var("exp", exp_ty);
val cl_env_tm = mk_var("cl_env",venvironment);
val v_var = mk_var("v",v_ty);
val ArrowM_const = get_term "ArrowM_const";
val Eval_const = get_term "Eval_const";
val EvalM_const = get_term "EvalM_const";
val MONAD_const = get_term "MONAD_const";
val PURE_const = get_term "PURE_const";
val FST_const = get_term "FST_const";
val SND_const = get_term "SND_const";
val LENGTH_const = get_term "LENGTH_const";
val EL_const = get_term "EL_const";
val Fun_const = get_term "Fun_const";
val Var_const = get_term "Var_const";
val Closure_const = get_term "Closure_const";
val failure_pat = get_term "failure_pat";
val Eval_pat = get_term "Eval_pat";
val Eval_pat2 = get_term "Eval_pat2";
val derive_case_EvalM_abs = get_term "derive_case_EvalM_abs";
val Eval_name_RI_abs = get_term "Eval_name_RI_abs";
val write_const = get_term "write_const";
val RARRAY_REL_const = get_term "RARRAY_REL_const";
val ARRAY_REL_const = get_term "ARRAY_REL_const";
val run_const = get_term "run_const";
val EXC_TYPE_aux_const = get_term "EXC_TYPE_aux_const";
val return_pat = get_term "return_pat";
val bind_pat = get_term "bind_pat";
val otherwise_pat = get_term "otherwise_pat";
val if_statement_pat = get_term "if_statement_pat";
val PreImp_EvalM_abs = get_term "PreImp_EvalM_abs";
val ArrowM_ro_tm = mk_comb(ArrowM_const, mk_var("ro", bool_ty));
val ArrowP_PURE_pat = get_term "ArrowP ro PURE";
val ArrowP_EqSt_pat = get_term "ArrowP ro EqSt";
val nsLookup_val_pat = get_term "nsLookup_val_pat"
val EvalM_pat = get_term "EvalM_pat"
val nsLookup_assum = get_term "nsLookup_assum"
val lookup_cons_assum = get_term "lookup_cons_assum"
val eqtype_assum = get_term "eqtype_assum"
val emp_tm = get_term "emp_tm";
val nsLookup_closure_pat = get_term "nsLookup_closure_pat"
val nsLookup_recclosure_pat = get_term "nsLookup_recclosure_pat"
val var_assum = get_term "var_assum"
val nsLookup_assum = get_term "nsLookup_assum"
val lookup_cons_assum = get_term "lookup_cons_assum"
val eqtype_assum = get_term "eqtype_assum"
val Eq_pat = get_term "Eq_pat"
val EqSt_pat = get_term "EqSt_pat"
val PRECONDITION_pat = get_term "PRECONDITION_pat"
val LOOKUP_VAR_pat = get_term "LOOKUP_VAR_pat";
val nsLookup_pat = get_term "nsLookup_pat"
val EVAL_T_F = ml_monad_translatorTheory.EVAL_T_F;
val refs_emp = get_term "refs_emp"

(******************************************************************************

  Copy/paste from other files.

******************************************************************************)

(*
  From ml_translatorLib .
*)

fun MY_MATCH_MP th1 th2 = let
  val tm1 = concl th1 |> dest_imp |> fst
  val tm2 = concl th2
  val (s, i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;

fun rm_fix res = let
    val lemma1 = mk_thm([], ml_translatorLib.get_term "eq remove")
    val lemma2 = mk_thm([], get_term "EqSt remove")
  in
    (QCONV (REWRITE_CONV [lemma1, lemma2]) res |>
      concl |> dest_eq |> snd)
  end;


(******************************************************************************

  Translator config and datatypes.

******************************************************************************)

val translator_state = {
  (* the store predicate *)
  H_def = ref UNIT_TYPE_def,
  default_H = ref refs_emp,
  H = ref refs_emp,

  (* the type of the references object *)
  refs_type = ref unit_ty,

  (* the exception refinement invariant and type *)
  EXN_TYPE_def = ref UNIT_TYPE_def, (* to replace EXN_TYPE_def_ref *)
  EXN_TYPE = ref (get_term "UNIT_TYPE"),
  exn_type = ref unit_ty, (* WHAT IS THE DIFFERENCE BETWEEN THESE LAST TWO? *)
  VALID_STORE_THM = ref (NONE : thm option),
  type_theories = ref ([current_theory(), "ml_translator"] : string list),
  exn_handles = ref ([] : (term * thm) list),
  exn_raises = ref ([] : (term * thm) list),
  exn_functions_defs = ref ([] : (thm * thm) list),
  access_patterns = ref([] : (term * thm) list),
  refs_functions_defs = ref([] : (thm * thm) list),
  rarrays_functions_defs = ref([] : (thm * thm * thm * thm * thm * thm) list),
  farrays_functions_defs = ref([] : (thm * thm * thm * thm * thm) list),

  induction_helper_thms = ref ([] : (string * thm) list),
  (* ^theorems saved in case induction can't be proved, left to aid user *)

  local_environment_var_name = ref "%env",
  num_local_environment_vars = ref 0,

  local_state_init_H = ref false,
    (* ^ to replace dynamic_init_H - does store predicate have free vars?*)
  store_pinv_def = ref (NONE : thm option),
  (* The specifications for dynamically initialized stores *)
  dynamic_v_thms =
    ref (Net.empty : (string * string * term * thm * thm * string option) net),

  (* The environment extension for dynamically initialized stores *)
  dynamic_refs_bindings = ref ([] : (term * term) list),

  (* Abbreviations of the function values in the case of a
     dynamically initialized store*)
  local_code_abbrevs = ref([] : thm list),

  mem_derive_case_ref = ref ([] : (hol_type * thm) list)
}




(******************************************************************************

  Helper functions.

******************************************************************************)

(* This is not used in this file, but is in the signature *)
fun add_access_pattern th =
  let val th' = REWRITE_RULE [GSYM AND_IMP_INTRO] th |> SPEC_ALL |> UNDISCH_ALL
      val tm = th' |> concl |> rator |> rand |> rand
  in
    (#access_patterns translator_state :=
      (tm, th') :: (!(#access_patterns translator_state));
    th)
  end;

fun the opt = valOf opt
              handle _ => failwith("the of NONE");

(* mk_write name v env = ``write ^name ^v ^env`` *)
fun mk_write name v env = ISPECL [name, v, env] write_def
                            |> concl |> rator |> rand;

val my_list_mk_comb = ml_monadBaseLib.my_list_mk_comb;

(*
  ISPECL for terms rather than theorems
  ISPECL_TM [``s1``, ``s2``, ...] ``λ x1 x2 ... . body`` =
                                                    ``body[s1/x1, s2/x2, ...]``
  i.e repeated beta application
*)
fun ISPECL_TM specs tm = let
    val tm' = my_list_mk_comb (tm, specs)
    fun beta_conv (_, acc) = RATOR_CONV acc THENC BETA_CONV
  in tm' |> (foldr beta_conv ALL_CONV specs) |> concl |> rand end;

(* dest_monad_type ``:α -> (β, γ) exc # α`` = (``:α``, ``:β``, ``:γ``) *)
fun dest_monad_type monad_type =
  let val subst = (match_type poly_M_type monad_type) in
    (type_subst subst a_ty, type_subst subst b_ty, type_subst subst c_ty) end;

(* Should be moved somewhere else *)
(* Repeatedly applies destructor f to term tm until no longer possible,
   then returns list of resulting terms *)
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];

val dest_args = snd o strip_comb;

(*
  Converts any theorem into a standard form:
    |- hyp1 ∧ hyp2 ∧ ... ⇒ concl
  If no hypotheses, will produce a theorem of form:
    |- T ⇒ concl
*)
fun disch_asms th =
  let val discharged = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl discharged) then discharged
      else DISCH T discharged
  end;

(*
  Creates a monad type with return type ty, and state/exception types as given
  by the translator_state.
*)

(* some fresh type variables *)
val gen1 = gen_tyvar();
val gen2 = gen_tyvar();
val gen3 = gen_tyvar();

fun M_type ty =
  Type.type_subst [a_ty |-> gen1, b_ty |-> gen2, c_ty |-> gen3] poly_M_type |>
  Type.type_subst [gen1 |-> !(#refs_type translator_state),
                   gen2 |-> ty,
                   gen3 |-> !(#exn_type translator_state)]

(* Some minor functions *)
local
  val {H=H, EXN_TYPE=EXN_TYPE, VALID_STORE_THM=VALID_STORE_THM, ...} =
    translator_state
in
  fun ISPEC_EvalM th = ISPEC (!H) th;
  fun ISPEC_EvalM_EXN_TYPE th = ISPEC (!EXN_TYPE) th;
  fun ISPEC_EvalM_MONAD th = ISPECL[!H, !EXN_TYPE] th;
  fun ISPEC_EvalM_VALID th =
    case (!VALID_STORE_THM) of
      SOME store_th => MP (ISPEC (!H) th) store_th
    | NONE => UNDISCH (ISPEC (!H) th)
end;


(*
  Instantiate ro argument in terms/theorems.
*)
fun INST_ro th =
  if (!(#local_state_init_H translator_state)) then th
  else INST [mk_var("ro",bool)|->F] th;

fun INST_ro_tm tm =
  if (!(#local_state_init_H translator_state)) then tm
  else subst [mk_var("ro",bool)|->F] tm;

(* Functions to manipulate of the current closure environment *)
fun get_curr_prog_state () = let
    val k = ref init_state
  in
    ml_prog_update (fn s => (k := s; s));
    !k
  end;

(*
  Local environment
*)
fun get_curr_env () =
  if !(#local_state_init_H translator_state) then (
    #num_local_environment_vars translator_state :=
      (!(#num_local_environment_vars translator_state)) + 1;
    mk_var(
      (!(#local_environment_var_name translator_state))
      ^(int_to_string (!(#num_local_environment_vars translator_state))),
      venvironment))
  else
    get_env (get_curr_prog_state ());

fun mk_PURE x = Term.inst [b_ty |-> gen1] PURE_const |>
                (fn t => mk_icomb(t, x)) |>
                Term.inst [gen1 |-> !(#refs_type translator_state)]

(* Retrieves the parameters given to Eval or EvalM *)
fun get_Eval_arg e = if same_const (strip_comb e |> fst) Eval_const then
                        e |> rand |> rand
                     else e |> rator |> rand |> rand;
fun get_Eval_env e = if same_const (strip_comb e |> fst) Eval_const then
                        e |> rator |> rator |> rand
                     else e |> rator |> rator |> rator |> rator |> rand;
fun get_Eval_exp e = if same_const (strip_comb e |> fst) Eval_const then
                        e |> rator |> rand
                     else e |> rator |> rator |> rand;
val get_EvalM_state = rand o rator o rator o rator;

fun abbrev_nsLookup_code th = let
  (* Prevent the introduction of abbreviations for already abbreviated code *)
  val th = HYP_CONV_RULE (fn x => true)
    (PURE_REWRITE_CONV
      (List.map GSYM (!(#local_code_abbrevs translator_state)))) th
  val pat1 = nsLookup_closure_pat
  val pat2 = nsLookup_recclosure_pat
  fun can_match_pat tm = can (match_term pat1) tm orelse
                         can (match_term pat2) tm
  val lookup_assums = List.filter can_match_pat (hyp th)
  val get_fun_name =
    stringSyntax.fromHOLstring o rand o rand o rand o rator
  fun get_code tm =
    if can (match_term pat1) tm then (rand o rand o rand) tm
    else (rand o rator o rand o rand) tm
  val name_code_pairs =
    List.map(fn x => (get_fun_name x, get_code x)) lookup_assums |>
    List.filter (not o is_const o snd)

  fun find_abbrev (name, code) = let
    val n = Theory.temp_binding ("[[ " ^ name ^ "_code ]]")
    val code_def = new_definition(n,mk_eq(mk_var(n,type_of code),code))
  in code_def end
  val abbrevs = List.map find_abbrev name_code_pairs
in
  (#local_code_abbrevs translator_state) :=
    List.concat [abbrevs, !(#local_code_abbrevs translator_state)];
  HYP_CONV_RULE (fn x => true) (PURE_REWRITE_CONV (List.map GSYM abbrevs)) th
end;

fun lookup_dynamic_v_thm tm = let
    val matches = Net.match tm (!(#dynamic_v_thms translator_state))
    val (name, ml_name, hol_fun, th, pre_cond, module) =
      first
        (fn (_, _, _, x, _, _) => (concl x |> rator |> rand |> same_const tm))
        matches
    val th = MATCH_MP Eval_Var_Short th
    val v_name = stringSyntax.fromMLstring ml_name
    val th = SPECL [stringSyntax.fromMLstring ml_name, v_env] th |> UNDISCH_ALL
in th end;


(******************************************************************************

  Get refinement invariants from monad and arrow types.

******************************************************************************)

fun get_m_type_inv ty =
  let val RI = get_type_inv (dest_monad_type ty |> #2)
      val MONAD_tm = Term.inst [c_ty |-> gen1] MONAD_const
      val MONAD_comb =
        my_list_mk_comb(MONAD_tm, [RI, !(#EXN_TYPE translator_state)])
  in Term.inst [gen1 |-> !(#refs_type translator_state)] MONAD_comb end

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty
  else let
    val (ty1,ty2) = dom_rng ty
    val i1 = get_arrow_type_inv ty1
      handle HOL_ERR _ => (mk_PURE (get_type_inv ty1))
    val i2 = get_arrow_type_inv ty2
  in my_list_mk_comb (ArrowM_ro_tm, [!(#H translator_state), i1, i2]) end;

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso can get_arrow_type_inv ty then
    ty |> get_arrow_type_inv |> ONCE_REWRITE_CONV [ArrowM_def] |>
    concl |> rand |> rand
  else get_type_inv ty;

fun get_EqSt_var tm =
  if can (match_term ArrowP_PURE_pat) tm then
    get_EqSt_var ((rand o rand) tm)
  else if can (match_term ArrowP_EqSt_pat) tm then
    SOME ((rand o rand o rator) tm)
  else NONE


(******************************************************************************

  Exceptions - prove specifications for exception raise and handle.

******************************************************************************)

local
  (* Prove the specifications for the exception raise *)
  fun prove_raise_spec exn_ri_def EXN_RI_tm (raise_fun_def, cons, stamp) = let
      val fun_tm = concl raise_fun_def |> strip_forall |>
                   snd |> lhs |> strip_comb |> fst
      val exn_param_types = (fst o ml_monadBaseLib.dest_fun_type o type_of) cons
      val refin_invs = List.map smart_get_type_inv exn_param_types

      val cons_name = fst (dest_const cons) |> stringSyntax.fromMLstring

      val raise_fun = raise_fun_def |> concl |> strip_forall |> snd |> lhs
      val E = raise_fun_def |> concl |> strip_forall |> snd |> rhs |> dest_abs
                            |> snd |> dest_pair |> fst |> rand
      val cons_params = strip_comb E |> snd
      val ri_type = mk_type("fun", [v_ty, bool_ty])
      val EVAL_CONDS = List.map mk_comb (zip refin_invs cons_params)
      val EVAL_CONDS = listSyntax.mk_list (EVAL_CONDS, ri_type)
      val arity = List.length cons_params
      val arity_tm = arity |> numSyntax.term_of_int
      val exprs_vars = ml_monadBaseLib.mk_list_vars_same "_expr" exp_ty arity
      val exprs = listSyntax.mk_list (exprs_vars, exp_ty)

      (* Instantiate the raise specification *)
      val cv = mk_var (mk_cons_name cons, astSyntax.str_id_ty)
      val raise_spec = ISPECL [cv, stamp, EXN_RI_tm, EVAL_CONDS,
                               arity_tm, E, exprs, raise_fun] EvalM_raise
      val free_vars = strip_forall (concl raise_spec) |> fst
      val raise_spec = SPEC_ALL raise_spec

      (* Prove the assumptions *)
      (* Exception RI assumption *)
      val take_assumption = fst o dest_imp o concl
      val exn_ri_assum = take_assumption raise_spec
      val num_eq_tm = mk_eq(mk_var("n",num_ty), mk_var("m",num_ty))
      fun case_on_values (asl,w) = let
          val a = List.find (can (match_term num_eq_tm)) asl
          fun get_values_var a =
            if (type_of a) = num_ty
            then get_values_var (rand a)
            else a
          val values_var = get_values_var (lhs (the a))
      in (Cases_on `^values_var` >> FULL_SIMP_TAC list_ss []) (asl,w) end
      handle Match => raise (ERR "prove_raise_spec" "case_on_values failed")
      val prove_exn_ri_assum =
          rpt strip_tac
          \\ ntac arity case_on_values
          \\ TRY case_on_values
          \\ FULL_SIMP_TAC list_ss [LIST_CONJ_def]
          \\ SIMP_TAC list_ss [exn_ri_def]
          \\ instantiate

      val exn_ri_lemma = prove(exn_ri_assum, prove_exn_ri_assum)
      val raise_spec = MP raise_spec exn_ri_lemma

      (* Trivial assumptions *)
      fun prove_assumption th = let
          val a = take_assumption th
          val lemma = SIMP_CONV list_ss [raise_fun_def] a |> EQT_ELIM
      in MP th lemma end
      val raise_spec = prove_assumption raise_spec
                                        |> prove_assumption
                                        |> prove_assumption

      (* Rewrite, generalize *)
      val raise_spec = SIMP_RULE list_ss [LIST_CONJ_def,MAP,ZIP,
                                          GSYM AND_IMP_INTRO] raise_spec
      val raise_spec = GENL free_vars raise_spec
      fun GEN_pair ((x,y),th) = GENL [x,y] th
      val raise_spec =
        List.foldr GEN_pair raise_spec (zip cons_params exprs_vars)

      val thm_name = "EvalM_" ^(dest_const fun_tm |> fst)
      val raise_spec = save_thm(thm_name, raise_spec)
      val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
  in raise_spec end

  (* Prove the specifications for the exception handle *)
  fun prove_handle_spec exn_ri_def EXN_RI_tm (handle_fun_def, cons, stamp) = let
      (* Rename the variables in handle_fun_def *)
      val handle_fun_def = let
          val vars = concl handle_fun_def |> strip_forall |> fst
          val types = List.map type_of vars
          val new_vars = ml_monadBaseLib.mk_list_vars "x" types
      in GENL new_vars (SPECL new_vars handle_fun_def) end
      val handle_fun = concl handle_fun_def |> strip_forall |> snd |> lhs
      val exn_type = type_of EXN_RI_tm |> dest_type |> snd |> List.hd

      val cons_name = fst (dest_const cons) |> stringSyntax.fromMLstring

      (* Instantiate the EvalM specification *)
      val CORRECT_CONS = let
          val case_tm = TypeBase.case_const_of exn_type
                        |> Term.inst [alpha |-> bool_ty]
          val all_cons = TypeBase.constructors_of exn_type
          fun mk_case_bool_fun c = let
            val types = (fst o ml_monadBaseLib.dest_fun_type o type_of) c
            val vars = ml_monadBaseLib.mk_list_vars "e" types
            val bool_tm = if same_const c cons then T else F
            val body = list_mk_abs (vars, bool_tm)
          in body end
          val case_funs = List.map mk_case_bool_fun all_cons
          val e_var = mk_var("e", exn_type)
          val case_tm = list_mk_comb (case_tm, e_var::case_funs)
      in mk_abs(e_var, case_tm) end

      val params_types = (fst o ml_monadBaseLib.dest_fun_type o type_of) cons
      val arity = List.length params_types
      val arity_tm = arity |> numSyntax.term_of_int
      val params_vars = ml_monadBaseLib.mk_list_vars "_x" params_types
      val PARAMS_CONDITIONS = let
          val case_tm = TypeBase.case_const_of exn_type
                        |> Term.inst [alpha |-> bool_ty]
          val all_cons = TypeBase.constructors_of exn_type

          val paramsv_var = mk_var("_paramsv", v_list_ty)

          val LENGTH_cond = Term.inst [alpha |-> v_ty] LENGTH_const
          val LENGTH_cond = mk_eq(mk_comb(LENGTH_cond, paramsv_var),arity_tm)
          fun mk_indices n = let
              fun mk_aux i =
                if i = n then []
                else (numSyntax.term_of_int i)::mk_aux(i+1)
          in mk_aux 0 end
          val indices = mk_indices arity
          val EL_tm = Term.inst [alpha |-> v_ty] EL_const
          fun mk_type_condition (var, i) = let
              val TYPE = get_type_inv (type_of var)
              val getter = list_mk_comb(EL_tm, [i, paramsv_var])
              val tm = list_mk_comb(TYPE, [var,getter])
          in tm end
          val type_conditions =
              List.map mk_type_condition (zip params_vars indices)
          val all_conditions = LENGTH_cond::type_conditions
          val conditions = list_mk mk_conj all_conditions T
          val conditions_fun = list_mk_abs (params_vars, conditions)

          fun mk_case_bool_fun c = let
            val types = (fst o ml_monadBaseLib.dest_fun_type o type_of) c
            val vars = ml_monadBaseLib.mk_list_vars "e" types
            val body =
              if same_const c cons then conditions_fun
                else list_mk_abs(ml_monadBaseLib.mk_list_vars "_x" types, F)
          in body end
          val case_funs = List.map mk_case_bool_fun all_cons
          val e_var = mk_var("_E", exn_type)
          val case_tm = list_mk_comb (case_tm, e_var::case_funs)
      in list_mk_abs([e_var, paramsv_var], case_tm) end

      (* We need to rewrite the handle function in a different
         manner before instantiating the theorem *)
      val (alt_handle_fun, alt_x1, alt_x2) = let
          val x1_var = strip_comb handle_fun |> snd |> List.hd
          val handle_fun_def_rhs = concl handle_fun_def |> strip_forall
                                         |> snd |> rhs
          val (state_var1, case_tm1) = dest_abs handle_fun_def_rhs
          val case_tm0 = dest_comb case_tm1 |> fst
          val (res_var_state_var2, case_tm2) = dest_comb case_tm1
                                               |> snd |> strip_abs
          val (res_var, state_var2) = (el 1 res_var_state_var2,
                                       el 2 res_var_state_var2)
          val case_tm3 = rator case_tm2
          val alt_x2_tm = rand case_tm2
          val (e_var,alt_x2_tm) = dest_abs alt_x2_tm
          val alt_x2_tm = list_mk_abs([e_var,state_var2], alt_x2_tm)
          val alt_x2_type = type_of alt_x2_tm
          val alt_x2_var = mk_var("x2", alt_x2_type)

          val alt_handle_fun = list_mk_comb(alt_x2_var, [e_var,state_var2])
          val alt_handle_fun = mk_abs(e_var,alt_handle_fun)
          val alt_handle_fun = mk_comb(case_tm3, alt_handle_fun)
          val alt_handle_fun =
            list_mk_abs([res_var, state_var2], alt_handle_fun)
          val alt_handle_fun = mk_comb(case_tm0,alt_handle_fun)
          val alt_handle_fun =
            list_mk_abs([x1_var, alt_x2_var, state_var1],alt_handle_fun)
      in (alt_handle_fun, x1_var, alt_x2_tm) end

      (* We also need to rewrite a2 in a different manner *)
      val a2_alt = let
          val state_type = !(#refs_type translator_state)
          val a2_type =
            ml_monadBaseLib.mk_fun_type(state_type::params_types, bool_ty)
          val a2_var = mk_var("a2", a2_type)
          val E_var = mk_var("E", exn_type)
          val case_tm = mk_comb(TypeBase.case_const_of exn_type, E_var)
                               |> Term.inst [alpha |-> bool_ty]
          val consl = TypeBase.constructors_of exn_type
          val state_var = mk_var("st", state_type)
          fun mk_condition c = let
              val types = fst(ml_monadBaseLib.dest_fun_type (type_of c))
              val vars = ml_monadBaseLib.mk_list_vars "e" types
          in if same_const c cons
             then list_mk_abs(vars, list_mk_comb(a2_var, state_var::vars))
             else list_mk_abs(vars, F)
          end
          val conditions = List.map mk_condition consl
          val a2_alt = list_mk_comb(case_tm, conditions)
          val a2_alt = list_mk_abs([state_var, E_var], a2_alt)
      in a2_alt end

      (* Instantiate the specification *)
      val cv = mk_var (mk_cons_name cons, astSyntax.str_id_ty)
      val handle_spec = ISPECL ([cv, stamp, CORRECT_CONS, PARAMS_CONDITIONS,
                                EXN_RI_tm, alt_handle_fun, alt_x1, alt_x2,
                                arity_tm])
                                EvalM_handle

      val ty_subst = match_type
                      (type_of a2_alt)
                      (type_of (handle_spec |> concl |> dest_forall |> fst))
      val a2_alt' = Term.inst ty_subst a2_alt
      val handle_spec = handle_spec |> SPEC a2_alt'

      val free_vars = concl handle_spec |> strip_forall |> fst
      val handle_spec = SPECL free_vars handle_spec

      (* Prove the assumptions *)
      val take_assumption = fst o dest_imp o concl

      (* branch handle *)
      val branch_handle_assum = take_assumption handle_spec

      val case_thms = [
          TypeBase.case_def_of exn_type,
          TypeBase.case_def_of pair_ty,
          TypeBase.case_def_of exc_ty
      ]

      (* set_goal ([], branch_handle_assum) *)
      val prove_branch_handle_assum =
          rpt strip_tac >> FULL_SIMP_TAC bool_ss case_thms
      val branch_handle_lemma = prove(branch_handle_assum,
                                      prove_branch_handle_assum)

      val handle_spec = MP handle_spec branch_handle_lemma

      (* branch let through *)
      val branch_let_through_assum = take_assumption handle_spec
      (* set_goal ([], branch_let_through_assum) *)
      val branch_let_through_lemma = prove(branch_let_through_assum,
          rpt strip_tac
          \\ FULL_SIMP_TAC bool_ss case_thms
          \\ rpt (BasicProvers.PURE_CASE_TAC \\ fs[]))
      val handle_spec = MP handle_spec branch_let_through_lemma

      (* refinement invariant equality *)
      val ref_inv_eq_assum = take_assumption handle_spec
      (* set_goal ([], ref_inv_eq_assum) *)
      val ref_inv_eq_lemma = prove(ref_inv_eq_assum,
          rpt strip_tac
          \\ FULL_SIMP_TAC bool_ss case_thms
          \\ rpt (BasicProvers.PURE_CASE_TAC \\ fs[exn_ri_def]))
      val handle_spec = MP handle_spec ref_inv_eq_lemma

      (* refinement invariant inequality *)
      val ref_inv_ineq_assum = take_assumption handle_spec
      (* set_goal ([], ref_inv_ineq_assum) *)
      val ref_inv_ineq_lemma = prove(ref_inv_ineq_assum,
          BasicProvers.Cases
          \\ rpt strip_tac
          \\ fs[exn_ri_def])
      val handle_spec = MP handle_spec ref_inv_ineq_lemma

      (* Rewrite - replace the variables E and paramsv,
         remove the case expressions making a disjunction on the type of the
         constructor of E *)
      val remove_imp = snd o dest_imp
      val EvalM_assum =
          concl handle_spec |> remove_imp |> remove_imp
                |> remove_imp |> dest_imp |> fst
      (* Eliminate E and paramsv in the assumptions *)
      val EvalM_assum2 = dest_conj EvalM_assum |> snd
      val (vars, EvalM_assum2_body) = strip_forall EvalM_assum2
      val (st_var,E_var,paramsv_var) = (el 1 vars,el 2 vars,el 3 vars)
      val v_vars = ml_monadBaseLib.mk_list_vars_same "v" v_ty arity
      val E_params_vars = ml_monadBaseLib.mk_list_vars "e" params_types
      val params_v_eq = mk_eq(paramsv_var,
                              listSyntax.mk_list (v_vars, v_ty))
      val E_eq = mk_eq(E_var, list_mk_comb(cons, E_params_vars))
      val EvalM_assum2_alt = list_mk_imp ([E_eq, params_v_eq],
                                          EvalM_assum2_body)
      val EvalM_assum2_alt = list_mk_forall (vars@E_params_vars@v_vars,
                                             EvalM_assum2_alt)
      val EvalM_assum2_eq = mk_eq(EvalM_assum2, EvalM_assum2_alt)
      val aquoted_vars = [`^st_var`, `^E_var`, `^paramsv_var`]
      val num_eq_pat = mk_eq(mk_var("n",num_ty),mk_var("m",num_ty))
      fun cases_on_paramsv a =
        if can (match_term num_eq_pat) (concl a) then let
            fun get_last_rand x =
              if can dest_comb x then get_last_rand (rand x) else x
            val paramsv_var = concl a |> lhs |> get_last_rand
        in Cases_on `^paramsv_var` end
        else failwith "cases_on_paramsv"
      val cases_on_paramsv = last_assum cases_on_paramsv
      (* set_goal ([], EvalM_assum2_eq) *)
      val EvalM_assum2_eq_lemma = prove(EvalM_assum2_eq,
        EQ_TAC \\ rpt strip_tac
        >-(last_x_assum(qspecl_then aquoted_vars assume_tac)
           \\ fs[] \\ rw[] \\ fs[])
        \\ last_x_assum(qspecl_then aquoted_vars assume_tac)
        \\ Cases_on `^E_var` \\ fs[]
        (* Cases on paramsv *)
        \\ ntac (arity+1) (cases_on_paramsv \\ fs[]));

      val handle_spec = PURE_REWRITE_RULE[EvalM_assum2_eq_lemma] handle_spec

      (* Eliminate E and paramsv in the generated precondition *)
      val pre =
          concl handle_spec |> remove_imp |> remove_imp
                |> remove_imp |> remove_imp |> dest_imp |> fst
      val (vars, pre_body) = strip_forall pre
      val (st_var, E_var) = (el 1 vars, el 2 vars)
      val (pre1,pre2) = dest_conj pre_body
      val E_with_params = list_mk_comb(cons, E_params_vars)
      val pre2_alt = Term.subst [E_var |-> E_with_params] pre2
      val pre_alt = list_mk_forall(st_var::E_params_vars,
                                   mk_conj(pre1,pre2_alt))
      val pre_eq = mk_eq(pre,pre_alt)
      (* set_goal ([], pre_eq) *)
      fun random_gen_tac th = let
        val (x,_) = dest_forall(concl th)
        val y = genvar (type_of x)
      in ASSUME_TAC(SPEC y th) end
      val pre_eq_lemma = prove(pre_eq,
        EQ_TAC
        >-(rpt strip_tac >> fs[CONTAINER_def]
           \\ `^pre1` by (rpt (first_x_assum random_gen_tac \\ fs[]) \\ fs[])
           \\ fs[])
        \\ rpt strip_tac
        \\ TRY(Cases_on `^E_var`)
        \\ fs[CONTAINER_def])

      val handle_spec = PURE_REWRITE_RULE[pre_eq_lemma] handle_spec

      (* Rewrite *)
      val handle_spec =
          SIMP_RULE list_ss [GSYM handle_fun_def,
                             TypeBase.case_def_of exn_type,
                             GSYM AND_IMP_INTRO] handle_spec
      (* Check *)

      val f = UNDISCH_ALL handle_spec |> concl |> rator |> rand |> rand
      val _ = if f ~~ handle_fun then () else raise (ERR "prove_handle_spec"
                 "Error : the generated spec does not have the proper form")

      (* Generalize *)
      val handle_spec = GENL free_vars handle_spec

      (* Save the theorem *)
      val fun_tm = strip_comb handle_fun |> fst
      val thm_name = "EvalM_" ^(dest_const fun_tm |> fst)
      val handle_spec = save_thm(thm_name, handle_spec)
      val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
  in handle_spec end;

in

  fun add_raise_handle_functions exn_functions exn_ri_def = let
      val (raise_functions, handle_functions) = unzip exn_functions

      (* Extract information from the exception refinement invariant *)
      val exn_ri_cases = CONJUNCTS exn_ri_def
      val EXN_RI_tm =
        List.hd exn_ri_cases |> concl |> strip_forall |>
        snd |> lhs |> rator |> rator
      val exn_ri_pats =
        List.map (rand o rator o lhs o snd o strip_forall o concl) exn_ri_cases
      val exn_ri_cons = List.map (fst o strip_comb) exn_ri_pats
      val exn_ri_params_types =
        List.map (fst o ml_monadBaseLib.dest_fun_type o type_of) exn_ri_cons
      fun safe_register_type ty = if can get_type_inv ty then ()
                                  else register_type ty
      val _ = mapfilter safe_register_type (List.concat exn_ri_params_types)

      val exn_ri_decomposed_rhs =
        List.map ((list_dest dest_conj) o snd o strip_exists o
          rhs o snd o strip_forall o concl) exn_ri_cases
      val exn_ri_deep_cons = List.map (rator o rand o hd) exn_ri_decomposed_rhs

      val exn_ri_stamps =
          List.map (rand o rand o rand) exn_ri_deep_cons
      val exn_info = zip exn_ri_cons exn_ri_stamps
      val exn_type = type_of EXN_RI_tm |> dest_type |> snd |> List.hd

      (* Link the raise definitions with the appropriate information *)
      val raise_funct_pairs =
          List.map (fn x => (x, concl x |> strip_forall |> snd |> rhs
                       |> dest_abs |> snd |> dest_pair |> fst |> rand
                       |> strip_comb |> fst)) raise_functions
      val raise_info =
          List.map (fn(d, tm) => tryfind (fn (x1, x2) =>
                    if same_const x1 tm then (d, x1, x2) else failwith "")
                    exn_info) raise_funct_pairs

      (*
       * Prove the raise specifications
       *)
      val raise_specs =
        List.map (prove_raise_spec exn_ri_def EXN_RI_tm) raise_info

      (* Link the handle definitions with the appropriate information *)
      fun get_handle_cons handle_fun_def =
        let
          val exn_cases = concl handle_fun_def |> strip_forall |> snd |> rhs |>
                          dest_abs |> snd |> rand |> strip_abs |> snd |> rand |>
                          dest_abs |> snd
          val cases_list = strip_comb exn_cases |> snd |> List.tl
          val cases_list = List.map (snd o strip_abs) cases_list
          val cases_cons = TypeBase.constructors_of exn_type
          val cases_pairs = zip cases_cons cases_list
          val handled_cons = the
            (List.find (fn (x, y) => not (can dest_pair y)) cases_pairs)
        in (handle_fun_def, fst handled_cons) end
        handle Bind => failwith "get_handled_cons"

      val handle_funct_pairs = List.map get_handle_cons handle_functions
      val handle_info = List.map (fn(d, tm) =>
             tryfind (fn (x1, x2) =>
                         if same_const x1 tm
                         then (d, x1, x2)
                         else failwith "") exn_info)
                                 handle_funct_pairs

      (*
       * Prove the handle specifications
       *)
      val handle_specs =
        List.map (prove_handle_spec exn_ri_def EXN_RI_tm) handle_info

      (* Store the proved theorems *)
      fun extract_pattern th = let
            val pat = concl th |> strip_forall |> snd |> strip_imp
                            |> snd |> rator |> rand |> rand
        in (pat, th) end

      val {exn_raises=e_raises, exn_handles=e_handles,...} = translator_state
  in
    e_raises := ((List.map extract_pattern raise_specs) @ (!e_raises));
    e_handles := ((List.map extract_pattern handle_specs) @ (!e_handles));
    zip raise_specs handle_specs
  end;

end; (* end local *)


(******************************************************************************

  Translation initialisation

******************************************************************************)

fun compute_dynamic_refs_bindings all_access_specs = let
  val store_vars = FVL [(!(#H translator_state)) |> dest_pair |> fst]
                   empty_varset;
  fun get_dynamic_init_bindings spec = let
    val spec = SPEC_ALL spec |> UNDISCH_ALL
    val pat = nsLookup_val_pat
    val lookup_assums =
      List.filter (can (match_term pat)) (hyp (UNDISCH_ALL spec))
    fun get_name_loc tm = ((rand o rand o rand o rator) tm, (rand o rand) tm)
    val bindings = List.map get_name_loc lookup_assums |>
                   List.filter (fn (x, y) => HOLset.member(store_vars, y))
  in bindings end

    val all_bindings =
      List.concat(List.map get_dynamic_init_bindings all_access_specs)
    val bindings_map =
      List.foldl (fn ((n, v), m) => Redblackmap.insert(m, v, n))
                 (Redblackmap.mkDict Term.compare) all_bindings
    val store_varsl =
      strip_comb ((!(#H translator_state)) |> dest_pair |> fst) |> snd
    val store_varsl = store_varsl |>
      filter (fn t => not (can (match_type ``:'a -> v -> bool``) (type_of t)))
    val final_bindings =
      List.map (fn x => (Redblackmap.find (bindings_map, x), x)) store_varsl
in final_bindings end

(* Initialize the translation by giving values to translator state *)
fun init_translation (monad_translation_params : monadic_translation_parameters)
                     refs_funs_defs
                     rarrays_funs_defs
                     farrays_funs_defs
                     exn_functions
                     store_pred_exists_thm
                     EXN_TYPE_def
                     add_type_theories
                     store_pinv_def_opt =
    let
      val {store_pred_def = store_pred_def,
           refs_specs  = refs_specs,
           rarrays_specs = rarrays_specs,
           farrays_specs = farrays_specs} = monad_translation_params

      (* Access functions for the references and the arrays *)
      val all_refs_specs = List.concat(List.map (fn (x, y) => [x, y]) refs_specs)
      val all_rarrays_specs = List.concat (List.map (fn (x1, x2, x3, x4) =>
                             [x1, x2, x3, x4]) rarrays_specs)
      val all_farrays_specs = List.concat (List.map (fn (x1, x2, x3) =>
                             [x1, x2, x3]) farrays_specs)

      val all_access_specs = all_refs_specs @
                             all_rarrays_specs @
                             all_farrays_specs

      fun get_access_info spec = let
          val pat = concl spec |> strip_forall |> snd |> strip_imp |> snd |>
                      rator |> rand |> rand
          val spec = SPEC_ALL spec |> UNDISCH_ALL
      in (pat, spec) end

      val st = translator_state
    in
      #H_def st := store_pred_def;
      #default_H st := mk_pair(
                      (concl store_pred_def |> strip_forall |>
                        snd |> dest_eq |> fst),
                      get_term "ffi_ffi_proj");
      #H st := (!(#default_H st));
      #local_state_init_H st :=
        (not (List.null (free_vars ((!(#H st)) |> dest_pair |> fst))));
      #refs_type st := (type_of ((!(#H st)) |> dest_pair |> fst)
                              |> dest_type |> snd |> List.hd);
      #EXN_TYPE_def st := EXN_TYPE_def;
      #EXN_TYPE st := (EXN_TYPE_def |> CONJUNCTS |> List.hd |> concl |>
                    strip_forall |> snd |> dest_eq |> fst |> strip_comb |> fst);
      #exn_type st :=
        (type_of (!(#EXN_TYPE st)) |> dest_type |> snd |> List.hd);
      #VALID_STORE_THM st := store_pred_exists_thm;
      #type_theories st :=
        (current_theory() :: (add_type_theories @ ["ml_translator"]));
      #store_pinv_def st := store_pinv_def_opt;

      (* Exceptions *)
      #exn_raises st := [];
      #exn_handles st := [];
      #exn_functions_defs st := exn_functions;

      #access_patterns st := List.map get_access_info all_access_specs;
      #refs_functions_defs st := refs_funs_defs;
      #rarrays_functions_defs st := rarrays_funs_defs;
      #farrays_functions_defs st := farrays_funs_defs;

      (* Data types *)
      #mem_derive_case_ref st := [];

      (* Dynamic specs *)
      #dynamic_v_thms st := Net.empty;

      (* Dynamic init environment *)
      #dynamic_refs_bindings st :=
        (if !(#local_state_init_H st) then
          compute_dynamic_refs_bindings all_access_specs else [])
      (*
      #dynamic_refs_bindings st := final_bindings
      *)
end;

(* user-initialisation functions *)
fun start_static_init_fixed_store_translation refs_init_list
                                              rarrays_init_list
                                              farrays_init_list
                                              store_hprop_name
                                              state_type
                                              exn_ri_def
                                              exn_functions
                                              add_type_theories
                                              store_pinv_opt
                                              extra_hprop =
  let
    val (monad_translation_params, store_trans_result) =
        translate_static_init_fixed_store refs_init_list
                                          rarrays_init_list
                                          farrays_init_list
                                          store_hprop_name
                                          state_type
                                          exn_ri_def
                                          store_pinv_opt
                                          extra_hprop

    val refs_funs_defs = List.map(fn (_, _, x, y) => (x, y)) refs_init_list
    val rarrays_funs_defs =
      List.map (fn (_, _, x1, x2, x3, x4, x5, x6) => (x1, x2, x3, x4, x5, x6))
      rarrays_init_list
    val farrays_funs_defs =
      List.map (fn (_, _, x1, x2, x3, x4, x5) => (x1, x2, x3, x4, x5))
      farrays_init_list

    val store_pinv_def_opt = Option.map fst store_pinv_opt
    val store_pred_exists_thm = SOME (#store_pred_exists_thm store_trans_result)

    val _ = init_translation monad_translation_params
                             refs_funs_defs
                             rarrays_funs_defs
                             farrays_funs_defs
                             exn_functions
                             store_pred_exists_thm
                             exn_ri_def
                             add_type_theories
                             store_pinv_def_opt

    val exn_specs = if List.length exn_functions > 0 then
                        add_raise_handle_functions exn_functions exn_ri_def
                    else []
  in (monad_translation_params, store_trans_result, exn_specs) end

fun start_dynamic_init_fixed_store_translation refs_manip_list
                                               rarrays_manip_list
                                               farrays_manip_list
                                               store_hprop_name
                                               state_type
                                               exn_ri_def
                                               exn_functions
                                               add_type_theories
                                               store_pinv_def_opt =
  let
    val monad_translation_params =
        translate_dynamic_init_fixed_store refs_manip_list
                                           rarrays_manip_list
                                           farrays_manip_list
                                           store_hprop_name
                                           state_type
                                           exn_ri_def
                                           store_pinv_def_opt
    (*
    val monad_translation_params = it
    *)
    val refs_funs_defs = List.map(fn (_, x, y) => (x, y)) refs_manip_list
    val rarrays_funs_defs =
      List.map (fn (_, x1, x2, x3, x4, x5, x6) => (x1, x2, x3, x4, x5, x6))
      rarrays_manip_list
    val farrays_funs_defs =
      List.map (fn (_, x1, x2, x3, x4, x5) => (x1, x2, x3, x4, x5))
      farrays_manip_list
    (*
      val refs_funs_defs = []
      val farrays_funs_defs =
        List.map (fn (_,a,_,b,_,c,d,e) => (a,b,c,d,e)) farrays_manip_list
      val rarrays_funs_defs =
        List.map (fn (_,a,_,b,_,c,d,e,f) => (a,b,c,d,e,f)) rarrays_manip_list


    *)
    val store_pred_exists_thm = NONE
    val _ = init_translation monad_translation_params refs_funs_defs
                             rarrays_funs_defs
                             farrays_funs_defs
                             exn_functions
                             store_pred_exists_thm
                             exn_ri_def
                             add_type_theories
                             store_pinv_def_opt

    val exn_specs = if List.length exn_functions > 0 then
                        add_raise_handle_functions exn_functions exn_ri_def
                    else []
  in (monad_translation_params, exn_specs) end


(******************************************************************************

  m2deep helper functions.

******************************************************************************)

val pmatch_index = ref 1;

(* Adapted from ml_translatorLib *)
val check_inv_fail = ref T;

fun check_inv name tm result =
  let val result = INST_ro result
      val tm2 = get_Eval_arg (concl result)
      val tm2' = if can (match_type (type_of tm2)) (type_of tm) then
                    Term.inst (match_type (type_of tm2) (type_of tm)) tm2
                 else tm2
  in
    if aconv tm2' tm then result
    else (
      check_inv_fail := tm;
      show_types_verbosely := true;
      print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n");
      print_term tm;
      print "\n\nbut derived:\n\n";
      print_term tm2;
      print "\n\n\n";
      show_types_verbosely := false;
      failwith("checkinv")
    ) end;
(* end of adaptation *)

fun inst_ro th1 th2 =
  let val tm1 = th1 |> concl |> dest_args |> hd
      val tm2 = th2 |> concl |> dest_args |> hd
  in
    if is_var tm1 andalso not (is_var tm2) then
        (INST [tm1 |-> tm2] th1, th2)
    else if is_var tm2 andalso not (is_var tm1) then
        (th1, INST [tm2 |-> tm1] th2)
    else (th1, th2)
  end
  handle HOL_ERR _ => (th1, th2)
       | Empty     => (th1, th2);

fun var_hol2deep tm =
  if is_var tm andalso can get_arrow_type_inv (type_of tm) then let
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ISPECL_TM [str,mk_comb(inv,tm)] Eval_name_RI_abs |> ASSUME
    in check_inv "var" tm result end
  else hol2deep tm;

(* raise, handle *)
fun get_pattern patterns tm =
  tryfind (fn(pat, th) =>
    if can (match_term pat) tm then (pat, th)
      else failwith "get_pattern") patterns;

fun inst_EvalM_bind th1 th2 = let
    (* Same as D, but leaves the VALID_REFS_PRED in the assumptions *)
    fun Dfilter th a0 =
      let
        val pat = concl VALID_REFS_PRED_def
                    |> strip_forall |> snd |> dest_eq |> fst
        val hyps = hyp th
        val th = List.foldl (fn (a, th) =>
          if can (match_term pat) a then th
          else if a ~~ a0 then th
            else DISCH a th) th hyps
        val th = PURE_REWRITE_RULE [AND_IMP_INTRO] th
      in if is_imp (concl th) then th else DISCH T th end
    val vs = concl th2 |> dest_imp |> fst
    val v = rand vs
    val z = rator vs |> rand
    val th2' = Dfilter (UNDISCH th2) vs
    val a2 = concl th2' |> dest_imp |> fst
    val a2 = mk_comb(mk_abs(z, a2), z)
    val a2_eq = BETA_CONV a2 |> GSYM
    val th2' = th2' |>
      CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV[a2_eq])) |>
      DISCH vs |> GENL[z, v]
    val x = concl th1 |> rator |> rand |> rand
    val st_var = mk_var("st", !(#refs_type translator_state))
    val n_st = my_list_mk_comb(SND_const, [mk_comb(x,st_var)])
    val th2' = INST [st_var |-> n_st] th2'
    val th1' = disch_asms th1
    val result = MATCH_MP EvalM_bind (CONJ th1' th2')
    val result = UNDISCH result
in result end;


local
  fun derive_case_of ty = let
      (* TODO : clean that *)
      fun smart_full_name_of_type ty =
        let val r = dest_thy_type ty
      in
        if #Tyop r = "cpn" andalso #Thy r = "toto" then ("order", "")
        else (full_name_of_type ty, #Thy r)
      end
      fun get_name ty = let
          val (n, thy) = (smart_full_name_of_type ty)
          val name = (clean_uppercase n) ^ "_TYPE"
          val name_thy = (clean_uppercase thy) ^"_"^name
      in (name, name_thy) end
      val (name, name_thy) =
        if ty <> unit_ty then get_name ty else ("UNIT_TYPE", "UNIT_TYPE")
      val inv_def = tryfind (fn thy_name => fetch thy_name (name ^ "_def"))
                            (!(#type_theories translator_state))
          handle HOL_ERR _ =>
                 tryfind (fn thy_name => fetch thy_name (name_thy ^ "_def"))
                         (!(#type_theories translator_state))
          handle  HOL_ERR _ =>
            let
              val thms = DB.find (name ^ "_def") |> List.map (fst o snd)
              val inv_ty = mk_type("fun", [ty, v_bool_ty])
              fun is_valid th = let
                  val th_body = CONJUNCTS th |> List.hd |> concl |> strip_forall
                                          |> snd |> dest_eq |> fst
                  val ctm = th_body |> strip_comb |> fst
                  val ctm_name = dest_const ctm |> fst
                  val ctm_rator = rator(rator th_body)
              in if ((ctm_name = name) orelse (ctm_name = name_thy)) andalso
                 (can (match_type (type_of ctm_rator)) inv_ty) then th
                 else failwith ""
              end
            in tryfind is_valid thms end
      (* *)
      val case_th = get_nchotomy_of ty
      val pat = Eval_pat
      val pure_tm = case_of ty |> concl
      (* Find a variable for the store invariant *)
      val pure_tm_vars = all_vars pure_tm
      val state_ty = !(#refs_type translator_state)
      val state_ty' =
        type_subst
        (List.map (fn ty => (ty |-> gen_tyvar ())) (type_vars state_ty))
        state_ty
      val H_var =
        mk_var("H",
               mk_prod(mk_type("fun", [state_ty', hprop_ty]),
                       type_of (get_term "ffi_ffi_proj"))) |>
                  variant pure_tm_vars
      (* Convert the Eval predicates to EvalM predicates *)
      fun Eval_to_EvalM tm = let
          val (m,i) = match_term pat tm
          fun M_type' ty = Type.type_subst [a_ty |-> state_ty',
                                   b_ty |-> ty,
                                   c_ty |-> !(#exn_type translator_state)]
                                  poly_M_type
          val res = mk_var("res", M_type' a_ty)
          val st = mk_var("st",state_ty')
          val tm0 = ISPECL_TM [!(#EXN_TYPE translator_state), res, H_var]
                    derive_case_EvalM_abs
          val tm1 = subst m (inst i tm0)
          val ty1 = tm |> rand |> rand |> type_of
          val monad_ret_type = M_type' ty1
          val y1 = tm |> rand |> rand |> inst [ty1 |-> monad_ret_type]
          val y0 = tm1 |> rator |> rand |> rand
        in subst [y0 |-> y1] tm1 end
        handle HOL_ERR _ =>
          if is_comb tm then let
            val (x,y) = dest_comb tm
            in mk_comb(Eval_to_EvalM x, Eval_to_EvalM y) end
          else if is_abs tm then let
            val (x,y) = dest_abs tm
            in mk_abs(x, Eval_to_EvalM y) end
          else tm
      val (x1,x2) = dest_imp pure_tm
      val (x2,x3) = dest_imp x2
      val (x3,x4) = dest_imp x3
      val hyps = list_dest dest_conj x3
      fun map_tl f [] = []
        | map_tl f (x::xs) = x :: List.map f xs
      val z3 = map_tl Eval_to_EvalM hyps |> list_mk_conj
      val z4 = Eval_to_EvalM x4
      val goal = mk_imp(x1,mk_imp(x2,mk_imp(z3,z4)))
      val tys = IMP_EvalM_Mat_cases |> SPEC_ALL |> concl |> rand |> rator
                  |> rator |> rand |> rand |> rand |> type_of |> dest_type |> snd

      fun get_inr_el tm = let
        val exp2 = tm |> rand
        val vars = tm |> rator |> rand |> rand |> rand
        (*val cname = tm |> rator |> rand |> rator |> rand |> rand |> rand*)
        val cvar = tm |> rator |> rand |> rator |> rand |> rand
        val cname = cvar |> dest_var |> fst |> lookup_cons_name |> fst
        val stamp = inv_def |> concl |> find_term
                      (fn tm => aconv (tm |> rator |> rand) cname
                                handle HOL_ERR _ => false)
        in list_mk_pair [cvar, vars, exp2, stamp] end
      val rw1_tm = goal |> rand |> rand |> rand |> rand |> rator
                        |> rator |> rand |> rand
      val y = let
        val xs = List.map get_inr_el (rw1_tm |> listSyntax.dest_list |> fst)
        val xs = listSyntax.mk_list(xs,type_of (hd xs))
        in sumSyntax.mk_inr(xs,hd tys) end
        handle HOL_ERR _ => let
        val exp2 = rw1_tm |> rator |> rand |> rand
        val ys = rw1_tm |> rator |> rand |> rator |> rand |> rand
                        |> listSyntax.dest_list |> fst |> List.map rand
        val x = mk_pair(listSyntax.mk_list(ys,string_ty),exp2)
        in sumSyntax.mk_inl(x,el 2 tys) end
      val f = Mat_cases_def |> CONJUNCT1 |> concl |> dest_eq |> fst |> rator
      val mat_cases = mk_comb(f,y)
      val new_goal = subst [rw1_tm |-> mat_cases] goal
      val x = goal |> rand |> rand |> rator |> rand |> rator |> rand |> rand
                   |> rand |> rator
      val st_var = goal |> rand |> rand |> rand |> rand |> rator
                        |> rator |> rator |> rand
      val Mat_lemma = ISPECL [st_var,x] IMP_EvalM_Mat_cases
      val is_simple_case = name = "PAIR_TYPE" orelse name = "UNIT_TYPE"
      val input_var = goal |> rand |> rand |> rator |> rand |> rator |> rand |> rand
                           |> rand |> rand
      val case_lemma = auto_prove "case-of-proof" (new_goal,
        rpt strip_tac
        \\ match_mp_tac Mat_lemma
        \\ full_simp_tac std_ss [GSYM PULL_FORALL]
        \\ asm_exists_tac
        \\ conj_tac THEN1 asm_rewrite_tac []
        \\ rewrite_tac [sumTheory.sum_case_def]
        \\ CONV_TAC (DEPTH_CONV BETA_CONV)
        \\ rewrite_tac [pair_case_def]
        \\ CONV_TAC (DEPTH_CONV BETA_CONV)
        \\ (if is_simple_case then all_tac else (conj_tac THEN1 EVAL_TAC))
        \\ conj_tac THEN1
         (asm_simp_tac std_ss [good_cons_env_def,EVERY_DEF,LENGTH,
            HD,LET_THM,pat_bindings_def,MAP]
          \\ once_rewrite_tac [GSYM ALL_DISTINCT_REVERSE]
          \\ asm_simp_tac std_ss [REVERSE_DEF,APPEND] \\ EVAL_TAC)
        \\ Cases_on `^input_var` \\ rewrite_tac [inv_def]
        \\ rpt strip_tac \\ rveq
        \\ simp_tac std_ss [v_11,MEM,stamp_11,CONS_11,ZIP,
             ml_translatorTheory.write_list_def,
             stringTheory.CHR_11,LENGTH,NOT_NIL_CONS,NOT_CONS_NIL,PULL_EXISTS]
        \\ simp_tac (srw_ss()) []
        \\ rpt (pop_assum mp_tac) \\ rewrite_tac [TAG_def,CONTAINER_def]
        \\ simp_tac (srw_ss()) []
        \\ rpt strip_tac
        \\ first_x_assum match_mp_tac \\ fs [])
      val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def,Mat_cases_def,MAP]
                         |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
      val case_lemma = GEN H_var case_lemma
    in case_lemma end
    handle HOL_ERR _ =>
    (print ("derive_case_of error: " ^(type_to_string ty) ^ "\n");
     raise (ERR "derive_case_of" ("failed on type : " ^(type_to_string ty))));

  fun get_general_type ty =
    if can dest_type ty andalso not (List.null (snd (dest_type ty))) then let
      val (ty_cons, ty_args) = dest_type ty
      fun generate_varnames c i n =
        if n = 0 then [] else
        if Char.isAlpha c then
          (implode [#"'", c])::(generate_varnames (Char.succ c) i (n-1))
        else
          ("'a"^(Int.toString i))::(generate_varnames c (i+1) (n-1))
      val ty_names = generate_varnames #"a" 1 (List.length ty_args)
      val ty_args_new = List.map mk_vartype ty_names
      (* Don't generalize fcp type arguments *)
      fun undo_fcp_types_rec (x::xs) (y::ys) =
        if is_vartype y andalso fcpSyntax.is_numeric_type x andalso fcpSyntax.dest_int_numeric_type x > 1
        then
          x::(undo_fcp_types_rec xs ys)
        else
          y::(undo_fcp_types_rec xs ys)
      | undo_fcp_types_rec _ _ = []
    in mk_type(ty_cons, undo_fcp_types_rec ty_args ty_args_new) end
    else ty

  fun mem_derive_case_of ty =
    let
      fun lookup x [] = fail()
      | lookup x ((y,z)::ys) = if can (match_type y) x then z else lookup x ys
      val th = lookup ty (!(#mem_derive_case_ref translator_state))
      val H_ty = th |> concl |> dest_forall |> fst |> type_of
      val H_st = (!(#H translator_state))

    in SPEC (H_st |> Term.inst (match_type (type_of H_st) H_ty)) th end
    handle HOL_ERR _ => (let
      val ty = get_general_type ty
      val th = derive_case_of ty
      val H_ty = th |> concl |> dest_forall |> fst |> type_of
      val H_st = (!(#H translator_state))
    in
      (#mem_derive_case_ref translator_state) :=
        (ty,th)::(!(#mem_derive_case_ref translator_state));
      SPEC (H_st |> Term.inst (match_type (type_of H_st) H_ty)) th
    end);
in
  fun inst_case_thm_for tm = let
    val (_,_,names) = TypeBase.dest_case tm
    val names = List.map fst names
    val th =
      mem_derive_case_of ((repeat rator tm) |> type_of |> dom_rng |> fst) |>
      UNDISCH
    val pat = th |> UNDISCH_ALL |> concl |> rator |> rand |> rand
    val (ss,i) = match_term pat tm
    val th = INST ss (INST_TYPE i th)
    val ii = List.map (fn {redex = x, residue = y} => (x,y)) i
    val ss = List.map
      (fn (x,y) => (inst i (smart_get_type_inv x) |-> smart_get_type_inv y)) ii
    val th = INST ss th
    val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
    fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                  handle HOL_ERR _ => []
    val ns = List.map (fn n => (n,args n)) names
    fun rename_var prefix ty v =
      mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
    val ts = find_terms (can (match_term (get_term "CONTAINER"))) (concl th) |>
             List.map (rand o rand) |>
             List.map (fn tm => (tm,
                                 List.map (fn x => (x, rename_var "n" string_ty x,
                                                    rename_var "v" v_ty x))
                                 (dest_args tm handle HOL_ERR _ => [])))
    val ns = List.map (fn (tm,xs) => let
        val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
        in zip aa xs end) ts |> flatten
    val ms = List.map
      (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
    val th = INST ms th
    val ks = List.map
              (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
             List.map
              (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}"))
                ns
    fun rename_bound_conv tm = let
      val (v,x) = dest_abs tm
      val (s,ty) = dest_var v
      val new_s = snd (first (fn (z,_) => z = s) ks)
      in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
    val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
    val th = MP th TRUTH
    val th = INST_ro th
    in th end;
end; (* end local *)

fun m2deep_previously_translated th tm = let
  fun inst_gen_eq_vars th = let
    (* Instantiate the variables in the occurences of Eq *)
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> List.map rand
    val ss = List.map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    (* Instantiate the variable in EqSt *)
    val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
                            |> concl |> rand |> rator |> rand |> rand
    val state_var_opt = get_EqSt_var thc
    val th =
      (case state_var_opt of
          NONE => th
        | SOME v => INST [v |-> genvar(type_of v)] th)
  in th end

  val th = inst_gen_eq_vars th
  val res = th |> UNDISCH_ALL |> concl |> rand
  val inv = smart_get_type_inv (type_of tm) |> INST_ro_tm
  val target = mk_comb(inv,tm)
  val (ss,ii) = match_term res target handle HOL_ERR _ =>
    match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
  val result = INST ss (INST_TYPE ii th)
                    |> MY_MATCH_MP (ISPEC_EvalM Eval_IMP_PURE |> SPEC_ALL)
                    |> REWRITE_RULE [GSYM ArrowM_def]
                    |> INST_ro
in result end

fun inst_EvalM_env v th =
    let val thx = th
      val name = fst (dest_var v)
      val str = stringLib.fromMLstring name
      val inv = smart_get_type_inv (type_of v)
      val tys = Type.match_type (type_of v)
        (type_of inv |> dest_type |> snd |> List.hd)
      val v = Term.inst tys v
      val ri = mk_comb(inv, v)
      val assum = ISPECL_TM [str,ri] Eval_name_RI_abs
      val new_env = mk_write str v_var v_env
      val old_env = new_env |> rand
      fun simp_EvalM_env tm =
        if can (match_term EvalM_pat) tm then
            REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC
            (DEPTH_CONV stringLib.string_EQ_CONV) THENC
            (SIMP_CONV bool_ss [])) tm
        else NO_CONV tm
      val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
                   |> DISCH_ALL |> DISCH assum |> INST_ro
                   |> SIMP_RULE bool_ss []
                   |> INST [old_env|->new_env]
                   |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_var_write]
                   |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
                   |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                   |> SIMP_RULE bool_ss [SafeVar_def]
      val new_assum = fst (dest_imp (concl th))
      (**)
      val th1 = th |>
        UNDISCH |>
        PURE_REWRITE_RULE[AND_IMP_INTRO] |>
        CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV simp_EvalM_env)) |>
        UNDISCH_ALL |>
        CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v)) |>
        DISCH new_assum
  in th1 end

fun apply_EvalM_Fun v th fix = let
  fun inst_new_state_var thms th = let
      val fvs = FVL (List.map (concl o DISCH_ALL) thms) empty_varset
      val current_state_var = UNDISCH_ALL th |> concl |> get_EvalM_state
      val basename = "st"
      fun find_new_state_var i = let
          val name = basename ^(Int.toString i)
          val state_var = mk_var(name, !(#refs_type translator_state))
      in if not (HOLset.member (fvs, state_var))
         then state_var else find_new_state_var (i+1)
      end
      val nstate_var = find_new_state_var 1
      val th = Thm.INST [current_state_var |-> nstate_var] th
  in th end

  val th1 = inst_EvalM_env v th
  val th2 = inst_new_state_var [th1] th1
  val th3 = if fix then MATCH_MP EvalM_Fun_Eq (GEN v_var th2)
                   else MATCH_MP EvalM_Fun (GEN v_var (FORCE_GEN v th2))
in th3 end;

fun apply_EvalM_Recclosure recc fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val FORALL_CONV = RAND_CONV o ABS_CONV
  val is_monad_only = not
    (can (match_term (SPEC_ALL ArrowM_def |> concl |> dest_eq |> fst))
      (concl th |> rator |> rand |> rator))
  val lemma = if is_monad_only
    then ISPECL [!(#H translator_state), recc,fname_str] EvalM_Recclosure_ALT2
          |> UNDISCH
    else ISPECL [!(#H translator_state), recc,fname_str] EvalM_Recclosure_ALT
  val lemma = lemma |> CONV_RULE ((FORALL_CONV o FORALL_CONV o
                           RATOR_CONV o RAND_CONV) EVAL)
  val pat1 = lemma |> concl |>
    find_term (can (match_term (ml_translatorLib.get_term "find_recfun")))
  val lemma = SIMP_RULE std_ss [EVAL pat1] lemma
  val lemma = INST_ro lemma
  val inv = smart_get_type_inv (type_of v)
  val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |>
    rator |> rator |> rator
  val pat = lemma |> concl |> find_term (can (match_term pat))
  val new_env = pat |> rand
  val old_env = v_env
  val tys = Type.match_type (type_of v)
    (type_of inv |> dest_type |> snd |> List.hd)
  val v = Term.inst tys v
  val assum = subst [old_env|->new_env]
              (ISPECL_TM [vname_str,mk_comb(inv,v)] Eval_name_RI_abs)
  val assum = INST_ro_tm assum
  val state_var = UNDISCH_ALL th |> concl |> get_EvalM_state
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum
               |> INST [old_env|->new_env]
               |> SIMP_RULE pure_ss [
                    EvalM_Var_SIMP_ArrowM, Eval_Var_SIMP,
                    lookup_var_write, lookup_cons_write
                  ]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> REWRITE_RULE [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH |> REWRITE_RULE [ASSUME new_assum]
                |> UNDISCH_ALL
                |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                    (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = if not is_monad_only
            then MATCH_MP lemma (Q.INST [`env`|->`cl_env`]
                                        (GENL [state_var, v_var] th1))
    else let
      val assum = DISCH_ALL th1 |> concl |> dest_imp |> fst
      val A = mk_abs(state_var, assum)
      val A_eq = BETA_CONV (mk_comb(A,state_var))
      val th = (Q.INST [`env`|->`cl_env`]
                  (GENL [state_var, v_var] (th1 |> DISCH_ALL))) |>
                SIMP_RULE pure_ss [Once(GSYM A_eq)]
      val th = MATCH_MP (ISPECL [!(#H translator_state), recc,fname_str]
                  EvalM_Recclosure_ALT3 |> SPEC_ALL) th |>
               SIMP_RULE pure_ss [A_eq] |> UNDISCH
      val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
      val th = SIMP_RULE std_ss [EVAL pat1] th
    in th end
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = disch_asms th2 |> REWRITE_RULE [assum]
                  |> SIMP_RULE pure_ss [
                      Eval_Var_SIMP, EvalM_Var_SIMP_ArrowM,
                      lookup_var_write, FOLDR, write_rec_def
                     ]
                  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  |> REWRITE_RULE [
                      Eval_Var_SIMP, EvalM_Var_SIMP_ArrowM,
                      lookup_var_write,FOLDR
                     ]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE [SafeVar_def]
  val lemma = UNDISCH EvalM_Eq_Recclosure |> INST_ro
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    val th9 = INST i (INST_TYPE t lemma)
    val name = lemma_lhs |> inst t |> subst i |> rand |> rand
    in INST [mk_var("name",string_ty)|->name] th9 end
    handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
in th4 end;

fun inst_list_EvalM_env xl th = let
    val vl = List.map (fn x => genvar v_ty) xl
    val xv_pairs = zip xl vl

    fun make_new_env ((x,v),env) = let
        val name = fst (dest_var x)
        val str = stringLib.fromMLstring name
        val new_env = mk_write str v env
    in new_env end
    val old_env =
      (rand o rator o rator o rator o rator o concl o UNDISCH_ALL) th
    val new_env = List.foldl make_new_env v_env xv_pairs

    fun make_inv_assum (x,v) = let
        val inv = get_type_inv (type_of x)
        val assum = list_mk_comb(inv, [x,v])
    in assum end
    val assums = List.map make_inv_assum xv_pairs
    val assums_rws = List.map ASSUME assums

    fun simp_EvalM_env tm =
      if can (match_term EvalM_pat) tm then
          REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP])
          THENC (DEPTH_CONV stringLib.string_EQ_CONV)
          THENC (SIMP_CONV bool_ss [])) tm
      else NO_CONV tm

    fun DISCHL l th = foldl (fn (a, acc) => DISCH a acc) th l

    val th1 = th |> REWRITE_RULE [GSYM SafeVar_def]
                 |> DISCH_ALL
                 |> INST [old_env|->new_env]
                 |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_var_write]
                 |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
                 |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                 |> SIMP_RULE bool_ss [SafeVar_def]
                 |> disch_asms

    val state_var = get_EvalM_state (UNDISCH_ALL th1 |> concl)

    fun UNBETA_CONVL vl tm =
      let val eq = mk_eq(tm, list_mk_comb(list_mk_abs(vl, tm), vl))
    in prove (eq, SIMP_TAC bool_ss []) end

    val th2 = th1 |> PURE_REWRITE_RULE[AND_IMP_INTRO]
                  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                                     (DEPTH_CONV simp_EvalM_env))
                  |> PURE_REWRITE_RULE assums_rws
                  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                                    (UNBETA_CONVL (state_var::xl)))
                  |> CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV o
                                RAND_CONV)
                                    (UNBETA_CONVL xl))
                  |> DISCHL (List.rev assums)
                  |> GENL (state_var::xl@vl)
in th2 end;


(******************************************************************************

  m2deep - translate monadic terms to CakeML deep embeddings.

******************************************************************************)

(* PMATCH *)
fun prove_EvalMPatBind goal = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> get_Eval_arg |> rator
                      |> dest_pabs
  val res = m2deep rhs_tm
  val exp = res |> concl |> get_Eval_exp
  val th = disch_asms res
  (* *)
  val is_var_assum = can (match_term var_assum)
  fun is_lookup_eqtype_assum x =
      can (match_term nsLookup_assum) x
      orelse can (match_term lookup_cons_assum) x
      orelse can (match_term eqtype_assum) x
  val vs = find_terms is_var_assum (concl th)
  val assums = find_terms is_lookup_eqtype_assum (concl th)
  val all_assums = append vs assums
  fun delete_assum tm =
    if tmem tm (all_assums) then
      MATCH_MP ml_monad_translatorTheory.IMP_EQ_T (ASSUME tm)
    else NO_CONV tm
  val th = CONV_RULE ((RATOR_CONV) (DEPTH_CONV delete_assum)) th
  val th = CONV_RULE ((RATOR_CONV) (SIMP_CONV bool_ss [])) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val ws = free_vars vars
  val vs = List.filter (fn tm => not (tmem (rand (rand tm)) ws)) vs |> op_mk_set aconv
  val new_goal = goal |> subst [mk_var("e",exp_ty)|->exp,p2 |-> p]
  val all_assums = (append vs assums) |>
                    List.foldl (fn (x,s) => HOLset.add (s,x)) empty_tmset |>
                    HOLset.listItems
  val num_assums = List.length all_assums
  val new_goal = List.foldr mk_imp new_goal all_assums

  val th = TAC_PROOF (([],new_goal),
    NTAC num_assums STRIP_TAC \\ STRIP_TAC
    (**)
    \\ FULL_SIMP_TAC pure_ss
          [FORALL_PROD, ml_monad_translatorTheory.BETA_PAIR_THM, UNCURRY_DEF]
    \\ CONV_TAC (DEPTH_CONV BETA_CONV)
    \\ REPEAT STRIP_TAC
    (* \\ fs [FORALL_PROD] \\ REPEAT STRIP_TAC *)
    \\ MATCH_MP_TAC (disch_asms res) \\ fs []
    \\ fs [EvalPatBind_def,Pmatch_def]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ NTAC num_assums STRIP_TAC
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL) (* Expand the refin. inv. *)
    \\ STRIP_TAC \\ fs [] \\ rfs []
    \\ fs [Pmatch_def,PMATCH_option_case_rwt,LIST_TYPE_IF_ELIM]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ rpt (CHANGED_TAC (SRW_TAC []
        [Eval_Var_SIMP,Once EvalM_Var_SIMP,lookup_cons_write,lookup_var_write]))
    \\ TRY (first_x_assum match_mp_tac >> METIS_TAC[])
    \\ fs[GSYM FORALL_PROD]
    \\ EVAL_TAC
    \\ fs [])
  in UNDISCH_ALL th end
  handle HOL_ERR e =>
    failwith ("prove_EvalMPatBind failed: (" ^ #message e ^ ")")

and pmatch_m2deep tm = let
  val (x,ts) = dest_pmatch_K_T tm
  val v = genvar (type_of x)
  val x_res = hol2deep x |> disch_asms
  val x_type = type_of x
  val x_inv = get_type_inv x_type
  val pmatch_type = type_of tm
  val pmatch_inv = get_m_type_inv pmatch_type
  val x_exp = x_res |> UNDISCH |> concl |> rator |> rand
  val nil_lemma = EvalM_PMATCH_NIL
                  |> ISPEC_EvalM
                  |> ISPEC pmatch_inv
                  |> ISPEC x_exp
                  |> ISPEC v
                  |> ISPEC x_inv
                  |> INST_ro
  val cons_lemma = EvalM_PMATCH
                   |> ISPEC_EvalM
                   |> ISPEC pmatch_inv
                   |> ISPEC x_inv
                   |> ISPEC x_exp
                   |> ISPEC v
                   |> INST_ro
  fun prove_hyp conv th =
    MP (CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th) TRUTH
  val assm = nil_lemma |> concl |> dest_imp |> fst

  val index_str = Int.toString (!pmatch_index)
  val _ = pmatch_index := (!pmatch_index + 1)
  val n = List.length ts
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) =
        let
          val th = trans xs
          val i_str = Int.toString (n - (List.length xs))
          val _ = print ("pmatch " ^index_str ^ " " ^ i_str  ^ "\n")
          val p = pat |> dest_pabs |> snd |> hol2deep
                      |> concl |> rator |> rand |> to_pattern
          val lemma = cons_lemma |> Q.GEN `pt` |> ISPEC p |> (prove_hyp EVAL) |>
                        Q.GEN `pat` |> ISPEC pat |>
                        prove_hyp (SIMP_CONV (srw_ss()) [FORALL_PROD]) |>
                        UNDISCH
          val th = UNDISCH th |>
                   CONV_RULE ((RATOR_CONV o RAND_CONV) (UNBETA_CONV v)) |>
                   MATCH_MP lemma |> remove_primes
          val goal = fst (dest_imp (concl th))
          val th = MP th (prove_EvalPatRel goal hol2deep) |> remove_primes |>
                   Q.GEN `res` |> ISPEC rhs_tm
          val goal = fst (dest_imp (concl th))
          val th = MATCH_MP th (prove_EvalMPatBind goal) |>
                    remove_primes |>
                    CONV_RULE ((RATOR_CONV o RAND_CONV)
                    (SIMP_CONV std_ss [FORALL_PROD,
                      patternMatchesTheory.PMATCH_ROW_COND_def])) |>
                    DISCH assm
        in th end

  val th = trans ts

  val _ = pmatch_index := (!pmatch_index - 1)
  val th = MY_MATCH_MP th (UNDISCH x_res)
  (* ^ strange bug with MATCH_MP: the side function
       variable is sometimes renamed?? *)
  val th = UNDISCH_ALL th
  in th end handle HOL_ERR e =>
  failwith ("pmatch_m2deep failed (" ^ #message e ^ ")")

and inst_case_thm tm = let
  fun inst_monad_type tm =
    let val ty_subst = Type.match_type poly_M_type (type_of tm)
        val a = Type.type_subst ty_subst a_ty
        val c = Type.type_subst ty_subst c_ty
    in Term.inst [a |-> !(#refs_type translator_state),
                  c |-> !(#exn_type translator_state)] tm
    end
  val tm = if can dest_monad_type (type_of tm) then (inst_monad_type tm) else tm
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take n xs = List.take(xs, n)
  fun simp_env tm =
    if can (match_term EvalM_pat) tm then
        REPEATC (
          (PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC
          (SIMP_CONV list_ss string_rewrites)) tm
    else NO_CONV tm
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = get_Eval_arg y
    val lemma = if can dest_monad_type (type_of z)
                then m2deep z
                else hol2deep z
    val lemma = INST_ro lemma
    val lemma = disch_asms lemma
    val new_env = get_Eval_env y
    val env = v_env
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP] THENC
             ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             REWRITE_CONV [lookup_cons_write,lookup_var_write] THENC
             DEPTH_CONV stringLib.string_EQ_CONV THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = take (length vs div 2) vs
    (*fun LIST_UNBETA_CONV l =
      foldl (fn (x, acc) => UNBETA_CONV x THENC RATOR_CONV (acc)) ALL_CONV l*)
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    (* Clean the environments in the lemma *)
    val lemma = CONV_RULE ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV)
      (DEPTH_CONV simp_env)) lemma
    (* Return *)
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma end
    handle HOL_ERR _ => (print ((term_to_string tm) ^ "\n\n");
      last_fail := tm; fail())
  fun sat_hyps tm =
    if is_conj tm then
      let val (x,y) = dest_conj tm
      in CONJ (sat_hyps x) (sat_hyps y) end
    else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  in th |> UNDISCH_ALL end handle Empty => failwith "empty"


and inst_EvalM_handle EvalM_th tm = let
    val x = tm |> rator |> rand
    val y = tm |> rand
    val (vars, y_body) = strip_abs y
    val thx = m2deep x
    val thy = m2deep y_body

    val thy2 = inst_list_EvalM_env vars thy
    val inv = get_type_inv (#2 (dest_monad_type (type_of x)))

    val var_to_HOL_name = stringLib.fromMLstring o fst o dest_var
    val HOL_names = List.map var_to_HOL_name vars
    val bind_names = listSyntax.mk_list (HOL_names, string_ty)
    val lemma1 = ISPECL [bind_names, inv, !(#H translator_state)] EvalM_th |>
                 SPEC_ALL

    (* Prove the assumptions *)
    fun prove_assumption th = let
        val a = concl th |> dest_imp |> fst
        val a_th = prove(a,EVAL_TAC)
    in MP th a_th end
    val lemma2 = prove_assumption lemma1 |> prove_assumption |> UNDISCH
    val lemma3 = MATCH_MP lemma2 (disch_asms thx)

    (* Match with thy2 *)
    val lemma4 = PURE_REWRITE_RULE [write_list_def] lemma3
    val expr1 = concl lemma4 |> dest_imp |> fst |> strip_forall |> snd
                      |> strip_imp |> snd |> rator |> rand |> rand
    val expr2 = dest_abs expr1 |> snd |> rator
    val eq = mk_eq(expr1, expr2)
    val eq_lemma = prove(eq, irule EQ_EXT \\ rw[])
    val lemma4 = PURE_REWRITE_RULE [eq_lemma] lemma4

    val lemma5 = MY_MATCH_MP lemma4 thy2
            |> CONV_RULE ((RATOR_CONV o RAND_CONV)
               (SIMP_CONV list_ss []))
            |> CONV_RULE ((RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
               (SIMP_CONV list_ss [MAP]))
            |> UNDISCH_ALL
in check_inv "handle" tm lemma5 end

and inst_EvalM_otherwise tm = let
    val x = tm |> rator |> rand
    val y = tm |> rand
    val th1 = m2deep x
    val th2 = m2deep y
    val (th1,th2) = inst_ro th1 th2
  fun simp_EvalM_env tm =
    if can (match_term EvalM_pat) tm then
        REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC
          (DEPTH_CONV stringLib.string_EQ_CONV) THENC (SIMP_CONV bool_ss [])) tm
    else NO_CONV tm
    val th2 = th2 |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
                  |> DISCH_ALL |> Q.INST [`env`|->`write "v" i env`]
                  |> REWRITE_RULE [Eval_Var_SIMP,lookup_cons_write]
                  |> UNDISCH_ALL
                  |> HYP_CONV_RULE (fn x => true) (DEPTH_CONV simp_EvalM_env)
                  |> DISCH_ALL
                  |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE []
                  |> REWRITE_RULE [SafeVar_def] |> disch_asms
    val st2 = concl th2 |> dest_imp |> snd |> get_EvalM_state
    val assums = concl th2 |> dest_imp |> fst
    val assums_eq = mk_comb(mk_abs(st2, assums), st2) |> BETA_CONV
    val th3 = CONV_RULE ((RATOR_CONV o RAND_CONV)
                (PURE_ONCE_REWRITE_CONV [GSYM assums_eq])) th2 |>
              Q.GEN `i` |> GEN st2
    val th4 = CONJ (disch_asms th1) th3
    val result = MATCH_MP (SPEC_ALL EvalM_otherwise) th4 |>
                 CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV)) |>
                 UNDISCH
in result end


(* normal function application *)
and m2deep_normal_fun_app tm = let
    val (f,x) = dest_comb tm
    val thf = m2deep f |>
              (CONV_RULE (
                (RATOR_CONV o RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
                (PURE_REWRITE_CONV [ArrowM_def])))
    val thf = INST_ro thf
    val (thx,is_monad) = (
      (hol2deep x |> HO_MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) |> disch_asms, false)
      handle _ => (disch_asms (m2deep x), true)
    )
    val thx = INST_ro thx
    (* If the argument is monadic, clean it by removing Eq and EqSt*)
    val is_var_assum = can (match_term var_assum)
    fun is_var_lookup_eqtype_assum x =
      can (match_term var_assum) x
      orelse can (match_term nsLookup_assum) x
      orelse can (match_term lookup_cons_assum) x
      orelse can (match_term eqtype_assum) x
    fun force_remove_fix thx =
      let val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
          val xs = List.map rand (find_terms (can (match_term pat)) (concl thx))
          val s = SIMP_RULE std_ss [EvalM_FUN_FORALL_EQ,M_FUN_QUANT_SIMP]
          val thx = List.foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs

          val thx = UNDISCH_ALL thx |> PURE_REWRITE_RULE[ArrowM_def]
          val thc = concl thx |> rator |> rand |> rator |> rand
          val st_opt = get_EqSt_var thc
      in (case st_opt of
             SOME st => HO_MATCH_MP EvalM_FUN_FORALL (GEN st thx)
                                    |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
                                    |> PURE_REWRITE_RULE[GSYM ArrowM_def]
           | NONE => PURE_REWRITE_RULE[GSYM ArrowM_def] thx)
      end
    val assums = find_terms is_var_lookup_eqtype_assum (concl thx)
    fun delete_assums tm =
      if tmem tm assums then
        MATCH_MP ml_monad_translatorTheory.IMP_EQ_T (ASSUME tm)
      else NO_CONV tm
    val thx = CONV_RULE ((RATOR_CONV) (DEPTH_CONV delete_assums)) thx
    val thx = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (SIMP_CONV (srw_ss())
                [CONTAINER_def, ml_translatorTheory.PRECONDITION_def])) thx
    val thx =  MP thx TRUTH
               handle HOL_ERR _ => failwith "normal function application"
    val thx = force_remove_fix thx |> PURE_REWRITE_RULE[ArrowM_def]

    (* Compute the result *)
    val result = HO_MATCH_MP (MATCH_MP EvalM_ArrowM thf
                 |> PURE_REWRITE_RULE[ArrowM_def]) thx
                 handle HOL_ERR _ =>
                 MY_MATCH_MP (MATCH_MP EvalM_ArrowM thf)
                             (MATCH_MP EvalM_Eq thx)
                 handle HOL_ERR _ => let
      val state_var = concl thf |> get_EvalM_state
      val thc = PURE_REWRITE_RULE[ArrowM_def] thf |> concl
                                 |> rator |> rand |> rator |> rand
      val eq_state_var_opt = get_EqSt_var thc
      in case eq_state_var_opt of NONE =>
                                  failwith "m2deep: function application"
         | SOME v => MY_MATCH_MP (MATCH_MP EvalM_ArrowM_EqSt
                                           (INST [v |-> state_var] thf))
                                 (MATCH_MP EvalM_Eq thx)
      end
    val result = PURE_REWRITE_RULE [GSYM ArrowM_def] result
in result end


and m2deep tm =
  (* variable *)
  if is_var tm then let
    val _ = debug_print "is_var" tm
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
              |> ONCE_REWRITE_CONV [ArrowM_def] |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ISPECL_TM [str,mk_ucomb(inv,tm)] Eval_name_RI_abs |> ASSUME
                 |> MY_MATCH_MP (SPEC_ALL (ISPEC_EvalM Eval_IMP_PURE)) |>
                 REWRITE_RULE [GSYM ArrowM_def]
    in check_inv "var" tm result end else
  (* raise *)
  if can (get_pattern (!(#exn_raises translator_state))) tm then let
    val _ = debug_print "raise custom pattern" tm
    val (_, EvalM_th) = get_pattern (!(#exn_raises translator_state)) tm

    (* Get the return type invariant *)
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv (#2 ty)

    (* Apply hol2deep to the parameters given to the raise function *)
    val params = strip_comb tm |> snd
    val params_EvalMs = List.map hol2deep params
    (* Symplify the assumptions *)
    fun simp_asms th = let
        val asms = List.mapPartial (Lib.total DECIDE) (hyp th)
        val th = List.foldl (Lib.uncurry PROVE_HYP) th asms
    in th end
    val params_EvalMs = List.map simp_asms params_EvalMs

    (* Instantiate *)
    fun inst_e_expr (lemma,th) = let
        val e = concl lemma |> rand |> rand
        val expr = concl lemma |> rator |> rand
    in SPECL [e,expr] th end
    val th = List.foldl inst_e_expr EvalM_th params_EvalMs
    val th = ISPECL[inv, !(#H translator_state)] th |> SPEC_ALL |> UNDISCH

    (* MP *)
    val result = List.foldl (fn (lem,th) => MP th lem) th params_EvalMs
    in check_inv "raise custom pattern" tm result end else
  (* handle *)
  if can (get_pattern (!(#exn_handles translator_state))) tm then let
    val _ = debug_print "handle custom pattern" tm
    val (_, EvalM_th) = get_pattern (!(#exn_handles translator_state)) tm
    val result = inst_EvalM_handle EvalM_th tm
    in check_inv "handle custom pattern" tm result end
  (* return *)
  else if can (match_term return_pat) tm then let
    val _ = debug_print "return" tm
    val th = hol2deep (rand tm)
    val result = HO_MATCH_MP (ISPEC_EvalM_MONAD EvalM_return) th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term bind_pat) tm then let
    val _ = debug_print "monad_bind" tm
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val (th1,th2) = inst_ro th1 th2
    val th2 = inst_EvalM_env v th2
    val result = inst_EvalM_bind th1 th2
    in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term otherwise_pat) tm then let
    val _ = debug_print "otherwise" tm
    val result = inst_EvalM_otherwise tm
    in check_inv "otherwise" tm result end else
  (* abs *)
  if is_abs tm then let
    val _ = debug_print "abs" tm
    val (v,x) = dest_abs tm
    val thx = m2deep x
    val result = apply_EvalM_Fun v thx false
    in check_inv "abs" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val _ = debug_print "let expressions" tm
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = m2deep x
    val th2 = inst_EvalM_env v th2
    val th2 = th2 |> GEN v_var
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP (ISPEC_EvalM EvalM_Let) (CONJ th1 th2)
    in check_inv "let" tm result end
  (* data-type pattern-matching *)
  else (
    let val thm = inst_case_thm tm
    in debug_print "data-type pattern-matching" tm; thm end)

  handle HOL_ERR _ =>
  (* previously translated term for dynamic store initialisation *)
  if can lookup_dynamic_v_thm tm then let
    val _ = debug_print "previously translated - dynamic" tm
      val th = lookup_dynamic_v_thm tm |> abbrev_nsLookup_code
      val result = m2deep_previously_translated th tm
    in check_inv "lookup_dynamic_v_thm" tm result end else
  (* previously translated term *)
  if can lookup_v_thm tm then let
    val _ = debug_print "previously translated" tm
      val th = lookup_v_thm tm
      val result = m2deep_previously_translated th tm
    in check_inv "lookup_v_thm" tm result end else
  (* if statements *)
  if can (match_term if_statement_pat) tm then let
    val _ = debug_print "if" tm
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val (th1,th2) = inst_ro th1 th2
    val th = MATCH_MP (ISPEC_EvalM EvalM_If) (LIST_CONJ [disch_asms th0, disch_asms th1, disch_asms th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* access functions *)
  if can (first (fn (pat,_) => can (match_term pat) tm))
    (!(#access_patterns translator_state)) then let
      val _ = debug_print "access function" tm
      val (pat,spec) = first (fn (pat,_) => can (match_term pat) tm)
        (!(#access_patterns translator_state))
      val ii = List.map (fn v => v |-> genvar (type_of v)) (free_vars pat)
      val (pat,spec) = (subst ii pat, INST ii spec)

      (* Substitute the parameters, link the parameters to their expressions *)
      val (tms, _) = match_term pat tm (* the type subst shouldn't be used *)
      val pat = Term.subst tms pat
      val th = Thm.INST tms spec

      fun retrieve_params_exps_pair asm =
        if can (match_term Eval_pat2) asm then let
            val param = rand asm |> rand
            val exp = rator asm |> rand
        in (param, exp) end else failwith "retrieve_params_exps_pair"

      val params_exps_pairs = mapfilter retrieve_params_exps_pair (hyp th)
      val params_exps_map =
        List.foldr (fn ((x, y), d) => Redblackmap.insert (d, x, y))
          (Redblackmap.mkDict Term.compare) params_exps_pairs

      (* Translate the parameters *)
      val args = tms |> List.map (fn {redex = v, residue = x} => x)
      val args_evals = List.map hol2deep args

      (* Substitute the translated expressions of the parameters *)
      val eval_concls = List.map concl args_evals
      fun subst_expr (eval_th, th) = let
        val (param, trans_param) = retrieve_params_exps_pair eval_th
        val expr_var = Redblackmap.find (params_exps_map, param)
        in Thm.INST [expr_var |-> trans_param] th end handle NotFound => th
      val th = List.foldr subst_expr th eval_concls

      (* Remove the Eval assumptions *)
      val result =
        List.foldl (fn (eval_th, th) => MP (DISCH (concl eval_th) th) eval_th)
          th args_evals

    in check_inv "access ref/array" tm result end else
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    val _ = debug_print "recursive pattern" tm
    val (lhs,fname,pre_var) = match_rec_pattern tm
    val (pre_var, pre_var_args) = strip_comb pre_var
    val pre_var = mk_var(dest_var pre_var |> fst,
                  mk_type("fun", [!(#refs_type translator_state),
                    dest_var pre_var |> snd]))
    val state_var = mk_var("st", !(#refs_type translator_state))
    val state_eq_var = genvar(!(#refs_type translator_state))
    val pre_var = list_mk_comb (pre_var, state_eq_var::pre_var_args)
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = stringLib.fromMLstring fname
    fun mk_fix tm =
      let
        val inv_type = type_of tm
        val inv = smart_get_type_inv inv_type
        val eq = ISPECL [inv, tm] Eq_def |> concl |> dest_eq |> fst
      in mk_PURE eq end
    fun mk_fix_st tm =
      let
        val inv_type = type_of tm
        val inv = smart_get_type_inv inv_type
        val eq = ISPECL [inv, tm] Eq_def |> concl |> dest_eq |> fst
        val pure = mk_PURE eq
        val eq_st = ISPECL [pure, state_eq_var] EqSt_def
                           |> concl |> dest_eq |> fst
      in eq_st end
    fun mk_m_arrow x y =
      my_list_mk_comb(ArrowM_ro_tm, [!(#H translator_state),x,y])
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
    val res = mk_m_arrow (mk_fix_st (hd xs)) (get_m_type_inv (type_of tm))
    val inv = mk_inv (tl xs) res
    val ss = fst (match_term lhs tm)
    val tys =
      match_type (type_of f) (type_of inv |> dest_type |> snd |> List.hd)
    val f = Term.inst tys f
    val pre = subst ss pre_var
    val h = ISPECL_TM [pre,str,inv,f,!(#H translator_state)] PreImp_EvalM_abs |>
            ASSUME |> REWRITE_RULE [PreImp_def] |> UNDISCH |> SPEC state_eq_var
    val h = INST [state_eq_var |-> state_var] h
    (*
    val expected_ty = h |> concl |> dest_forall |> fst |> type_of
    val ty_subst = match_type (type_of state_eq_var) expected_ty
    val state_eq_var' = Term.inst ty_subst state_eq_var
    val h = h |> SPEC state_eq_var'
    val state_var' = Term.inst (ty_subst) state_var
    val h = INST [state_eq_var' |-> state_var'] h
    *)
    val ys = List.map (fn tm => MY_MATCH_MP (ISPEC_EvalM Eval_IMP_PURE |>
                                             SPEC_ALL)
                        (MY_MATCH_MP Eval_Eq (var_hol2deep tm))) xs
    (*val ys' = ys |> map (INST_TYPE ty_subst)*)
    fun apply_arrow h [] = INST_ro h
      | apply_arrow h (x::xs) =
          let
            val th = apply_arrow h xs
          in
            MATCH_MP (MATCH_MP (INST_ro EvalM_ArrowM) th) (INST_ro x)
            handle HOL_ERR _ =>
              (MATCH_MP (MATCH_MP (INST_ro EvalM_ArrowM_EqSt) th) (INST_ro x))
          end
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* PMATCH *)
  if is_pmatch tm then let
    val _ = debug_print "PMATCH" tm
    val original_tm = tm
    val lemma = pmatch_preprocess_conv tm
    val tm = lemma |> concl |> rand
    (* HERE *)
    val result = pmatch_m2deep tm |>
                 CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (K (GSYM lemma)))))
    in check_inv "pmatch_m2deep" original_tm result end else
  (* normal function applications *)
  if is_comb tm then let
    val _ = debug_print "normal function application" tm
    val result = m2deep_normal_fun_app tm
    in check_inv "comb" tm result end else
  failwith ("cannot translate: " ^ term_to_string tm);


(******************************************************************************

  m_translate helper functions

******************************************************************************)

fun remove_ArrowM_EqSt th = let
  val st_var = th |> concl |> rator |> rand |> rator |> rator |> rand |> rand
  val th = GEN st_var th |> MATCH_MP ArrowM_EqSt_elim
in th end handle HOL_ERR _ => th;

fun remove_local_code_abbrevs th = let
  val th =
    HYP_CONV_RULE (fn x => true)
      (PURE_REWRITE_CONV (!(#local_code_abbrevs translator_state))) th |>
    CONV_RULE (PURE_REWRITE_CONV (!(#local_code_abbrevs translator_state)))
in th end

fun undef_local_code_abbrevs () =
  let val undef = (delete_const o fst o dest_const o rand o rator o concl)
      val _ = mapfilter undef (!(#local_code_abbrevs translator_state))
  in (#local_code_abbrevs translator_state) := [] end

(* Remove Eq *)
local
  val PURE_ArrowP_Eq_tm = get_term "PURE ArrowP ro eq";
  fun remove_Eq_aux th = let
    val th = REWRITE_RULE [ArrowM_def] th
    val pat = PURE_ArrowP_Eq_tm
    fun dest_EqArrows tm =
      if can (match_term pat) tm then
        (rand o rand o rand o rator o rand) tm ::
          dest_EqArrows ((rand o rand) tm)
      else []
    val rev_params =
      th |> concl |> rator |> rand |> rator |> dest_EqArrows |> List.rev
    fun f (v,th) =
      HO_MATCH_MP EvalM_FUN_FORALL (GEN v th) |>
      SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
    val th = List.foldr f th rev_params handle HOL_ERR _ => th
    val th = REWRITE_RULE [GSYM ArrowM_def] th
  in th end handle HOL_ERR _ => th

  fun remove_EqSt th = let
    val th = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
    val thc = concl th |> rator |> rand |> rator |> rand
    val st_opt = get_EqSt_var thc
  in case st_opt of
     SOME st => HO_MATCH_MP EvalM_FUN_FORALL (GEN st th)
                            |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
                            |> PURE_REWRITE_RULE[GSYM ArrowM_def]
   | NONE => th |> PURE_REWRITE_RULE[GSYM ArrowM_def]
  end handle HOL_ERR _ => th
in
    val remove_Eq = remove_Eq_aux o remove_EqSt
end (* end local *)

local (* ported from ml_translatorLib *)
  fun guess_def_name original_def = let
    val def_tm = concl original_def
    val const_tm = original_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                                |> concl |> dest_eq |> fst |> repeat rator
    val const_name = const_tm |> dest_thy_const |> #Name
    val const_thy = const_tm |> dest_thy_const |> #Thy
    fun try_find_in thys = let
      val xs = DB.match thys def_tm
      val xs = filter (aconv def_tm o concl o fst o snd) xs
      val ((thy,name),_) = first (fn x => Def = (x |> snd |> snd)) xs
                           handle HOL_ERR _ => hd xs handle Empty => fail ()
      in (thy,name) end
    val (thy,name) = try_find_in [const_thy]
                     handle HOL_ERR _ => try_find_in []
                     handle HOL_ERR _ => (const_thy,const_name ^ "_def")
    in if current_theory() = thy then name else thy ^ "Theory." ^ name end

  fun break_lines_at k [] = []
    | break_lines_at k (x::xs) = let
        fun consume ts [] = (ts,[])
          | consume ts (x::xs) =
              if String.size ts + 1 + String.size x <= k then
                consume (ts ^ " " ^ x) xs
              else (ts,x::xs)
        val (line,rest) = consume x xs
        in line :: (break_lines_at k rest) end;

  fun break_line_at k prefix text = let
    val words = String.tokens (fn c => c = #" ") text
    val lines = break_lines_at k words
    in map (fn str => prefix ^ str) lines end;

in

  fun print_unable_to_prove_ind_thm goal original_def ml_name = let
    val name = guess_def_name original_def
    val thy_const = original_def |> SPEC_ALL |> CONJUNCTS |> hd |>
                    SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
                    |> dest_thy_const
    val _ = print ("\nERROR: Unable to prove induction for "^name^"\n")
    val _ = print ("\n")
    val t = (!show_types)
    val _ = (show_types := true)
    val _ = print_term goal
    val _ = (show_types := t)
    val line_length = 53
    val _ = map print (break_line_at line_length "\n  "
      ("This induction goal has been left as an assumption on the theorem "^
       "returned by the translator. You can prove it with something like "^
       "the following before "^(#Name thy_const)^" is used in subsequent "^
       "translations."))
    val _ = print ("\n")
    val _ = print ("\nval res = m_translate "^name^";")
    val _ = print ("\n")
    val _ = print ("\nval ind_lemma = Q.prove(")
    val _ = print ("\n  `^(first is_forall (hyp res))`,")
    val _ = print ("\n  rpt gen_tac")
    val _ = print ("\n  \\\\ strip_tac")
    val _ = print ("\n  \\\\ ho_match_mp_tac (<relevant induction theorem>)")
    val _ = print ("\n  \\\\ rpt strip_tac")
    val _ = print ("\n  \\\\ match_mp_tac <relevant helper theorem>")
    val _ = print ("\n  \\\\ last_x_assum match_mp_tac")
    val _ = print ("\n  \\\\ rpt strip_tac")
    val _ = print ("\n  \\\\ <unfold definitions and finish proof>)")
    val _ = print ("\n  |> update_precondition;")
    val _ = print ("\n")
    val _ = map print (break_line_at line_length "\n  "
      ("The relevant induction theorem will likely be saved in the database " ^
       "as "^(#Name thy_const)^"_ind. Some helper theorems have been saved " ^
       "in the database as "^(#Name thy_const)^"_helper_X."))
    val _ = print ("\n")
    val _ = print ("\n")
    in () end;

end (* end local *)

(* Apply the induction in the case of a recursive function w/o preconditions *)
fun apply_ind thms ind = let
    fun get_goal (fname,ml_fname,def,th,pre) = let
        val th = REWRITE_RULE [CONTAINER_def] th
        val hs = hyp th
        val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
        val state_var = th |> UNDISCH_ALL |> concl |> rator
                           |> rator |> rator |> rand
        val forall_st_tm = mk_forall(state_var, th |> UNDISCH_ALL |> concl)
        val st_eq_tm = REWRITE_RULE [ArrowM_def] th |> UNDISCH_ALL |> concl |>
                       rator |> rand |> rator |> rand |> get_EqSt_var |> the
        val forall_st_tm = mk_forall(st_eq_tm, forall_st_tm)
        val hyp_tm = list_mk_abs(rev rev_params, forall_st_tm)
        val goal = list_mk_forall(rev rev_params, forall_st_tm)
    in (hyp_tm,(th,(hs,goal))) end
    val goals = List.map get_goal thms

    val gs = goals |> List.map (snd o snd o snd) |> list_mk_conj
    val hs = goals |> List.map (fst o snd o snd) |> flatten
                   |> op_mk_set aconv |> list_mk_conj
    val goal = mk_imp(hs,gs)
    val ind_thm = (the ind) |> rename_bound_vars_rule "i"
    val ind_thm = (ISPECL (goals |> List.map fst) ind_thm
                  handle HOL_ERR e => ind_thm) |>
                  CONV_RULE (DEPTH_CONV BETA_CONV)

    fun POP_MP_TACs ([],gg) = ALL_TAC ([],gg)
      | POP_MP_TACs (ws,gg) =
        POP_ASSUM (fn th => (POP_MP_TACs THEN MP_TAC th)) (ws,gg)
    val pres = List.map
      (fn (_,_,_,_,pre) => case pre of SOME x => x | _ => TRUTH) thms


    (*  val lhs = fst o dest_eq;  val rhs = snd o dest_eq; *)
    fun split_ineq_orelse_tac tac (asms,concl) = (asms,concl) |>
    let
        val (asms',concl) = strip_imp concl
        val asms = asms'@asms
        fun is_ineq t = is_neg t andalso is_eq(rand t)
        fun is_disj_of_ineq t = all is_ineq (strip_disj t)
        fun is_all_disj_of_ineq t = is_disj_of_ineq(snd(strip_forall t))
        val var_equalities =
            List.map strip_conj asms
            |> List.concat
            |> List.filter is_eq
            |> List.filter (is_var o lhs)
            |> List.filter (is_var o rhs)
        fun eq_closure l [] = l
          | eq_closure l (f::r) =
            let val (lhs,rhs) = (lhs f, rhs f) in
              if List.exists (fn x => term_eq lhs x) l then
                eq_closure (rhs::l) r
              else if List.exists (fn x => term_eq rhs x) l then
                eq_closure (lhs::l) r
              else
                eq_closure l r
            end
        fun case_split_vars (l,r) =
          if can (match_term r) l then
            match_term r l
            |> fst
            |> List.filter (fn {residue,...} => not(is_var residue))
            |> List.map (fn {redex,...} => redex)
          else if is_comb r andalso
                  not(TypeBase.is_constructor(fst(strip_comb r))) then
            [r]
          else
            []
      in
        case List.find is_all_disj_of_ineq asms of
            NONE => tac
          | SOME asm =>
            let val asm' = snd(strip_forall asm)
                val disjuncts = strip_disj asm'
                val lsrs = List.map (dest_eq o rand) disjuncts
                val vars =
                    List.map case_split_vars lsrs
                    |> List.filter (not o null)
                    |> List.map hd
                    |> op_mk_set aconv
            in
              case vars of
                  [] => tac
                | l => List.foldr
                        (fn (x,t) => Cases_on [ANTIQUOTE x] \\ t) ALL_TAC l
            end
      end

    fun prove_ind_thm goal goals ind_thm =
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ HO_MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ POP_MP_TACs
        \\ SIMP_TAC (srw_ss()) [ADD1,TRUE_def,FALSE_def]
        \\ SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ SIMP_TAC std_ss [GSYM FORALL_PROD]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ HO_MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ fs[NOT_NIL_EQ_LENGTH_NOT_0] (*For arithmetic-based goals*)
        \\ METIS_TAC[])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (HO_MATCH_MP_TAC ind_thm ORELSE
            HO_MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (HO_MATCH_MP_TAC ind_thm ORELSE
            HO_MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC PreImp_IMP
        \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV pres))
        \\ (STRIP_TAC THENL (List.map MATCH_MP_TAC
              (List.map (fst o snd) goals)))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP,PRECONDITION_def]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (mk_imp(hs,ind_thm |> concl |> rand),
        STRIP_TAC
        \\ HO_MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ METIS_TAC [])
      handle HOL_ERR e =>
        auto_prove "ind" (goal,
        STRIP_TAC
        \\ HO_MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ POP_MP_TACs
        \\ SIMP_TAC (srw_ss()) [ADD1,TRUE_def,FALSE_def]
        \\ SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ SIMP_TAC std_ss [GSYM FORALL_PROD]
        \\ rpt(split_ineq_orelse_tac(metis_tac [])))
      handle HOL_ERR e =>
        auto_prove "ind" (goal,
        STRIP_TAC
        \\ HO_MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ last_x_assum match_mp_tac
        \\ fs[st_ex_return_def]
        \\ metis_tac[])

    fun store_helper_theorems fname index [] = ()
      | store_helper_theorems fname index (thm::thms) =
          let val name = (fname ^ "_helper_" ^ int_to_string(index))
          in
            #induction_helper_thms translator_state :=
              (name, thm) :: (!(#induction_helper_thms translator_state));
            store_helper_theorems fname (index + 1) thms
          end

    val lemma = prove_ind_thm goal goals ind_thm
    handle HOL_ERR _ => let
      val (_,ml_name,def,_,_) = hd thms
      val ind_hyp = ind_thm |> UNDISCH_ALL |> hyp |> hd
      val lemma = mk_imp(hs, ind_hyp) |> ASSUME |> UNDISCH_ALL |>
                  HO_MATCH_MP ind_thm |> DISCH hs (* leave goal on assumptions *)
      in
        store_helper_theorems ml_name 0 (List.map (fst o snd) goals);
        print_unable_to_prove_ind_thm (mk_imp (hs, ind_hyp)) def ml_name;
        lemma
      end
    handle _ => let
      val (_,ml_name,def,_,_) = hd thms
      val lemma = ASSUME goal |> UNDISCH_ALL |> DISCH hs
      in
        store_helper_theorems ml_name 0 (List.map (fst o snd) goals);
        print_unable_to_prove_ind_thm goal def ml_name;
        lemma
      end

    val results = UNDISCH lemma |> CONJUNCTS |> List.map SPEC_ALL
    val thms = List.map
      (fn (th, (fname,ml_fname,def,_,pre)) => (fname,ml_fname,def,th,pre))
        (zip results thms)
in thms end;

fun remove_Eq_from_v_thm th = let
  fun try f (x, acc) = f x acc handle HOL_ERR _ => acc
  fun foo v th = th |> GEN v
                |> HO_MATCH_MP FUN_FORALL_INTRO
                |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
                |> PURE_REWRITE_RULE[ArrowM_def]
                |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
                |> PURE_REWRITE_RULE[GSYM ArrowM_def]

  (* Remove EqSt *)
  val tms = find_terms (can (match_term EqSt_pat)) (concl th)
  val vs = tms |> List.map rand
  val th = foldl (try foo) th vs (* should be at most one element in vs *)

  (* Remove Eq *)
  val tms = find_terms (can (match_term Eq_pat)) (concl th)
  val vs = tms |> List.map rand
in foldl (try foo) th vs end;

fun get_manip_functions_defs () = let
    val defs_list =
      List.foldl (fn ((x, y), l) => x::y::l) []
        (!(#exn_functions_defs translator_state))
    val defs_list =
      List.foldl (fn ((x, y), l) => x::y::l) defs_list
        (!(#refs_functions_defs translator_state))
    val defs_list =
      List.foldl (fn ((x1, x2, x3, x4, x5, x6), l) => x1::x2::x3::x4::x5::x6::l)
        defs_list (!(#rarrays_functions_defs translator_state))
    val defs_list =
      List.foldl (fn ((x1, x2, x3, x4, x5), l) => x1::x2::x3::x4::x5::l)
        defs_list (!(#farrays_functions_defs translator_state))
in defs_list end

fun extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th, NONE) else let
    val rw_thms =
      case (!(#store_pinv_def translator_state)) of
          SOME th => th::(get_manip_functions_defs ())
        | NONE => (get_manip_functions_defs ())
    val rw_thms = FALSE_def::TRUE_def::rw_thms
    val c = (REWRITE_CONV [CONTAINER_def, PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def] THENC
             SIMP_CONV (srw_ss()) rw_thms)
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if Teq rhs then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL_PRECONDITION_T] th),NONE)
    else let
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
  in (th, SOME pre_def) end end

fun get_monad_pre_var th lhs fname = let
    val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def] |>
                concl |> rator |> rand |> rator |> rand
  in
    case get_EqSt_var thc of
        NONE => get_pre_var lhs fname
      | SOME state_var => (let
          fun mk_fun_ty (tm, acc) = mk_type("fun", [type_of tm, acc])
          val args = state_var :: (dest_args lhs)
          val ty = List.foldr mk_fun_ty bool args
          val v = mk_var(fname ^ "_side", ty)
        in
          List.foldl (fn (x, y) => mk_comb(y, x)) v args end)
  end;

fun extract_precondition_rec thms = let
  fun rephrase_pre (fname,ml_fname,def,th) = let
    val (lhs,_) = dest_eq (concl def)
    val pre_var = get_monad_pre_var th lhs fname
    val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
    val th = ex_rename_bound_vars_rule th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
    val tm = concl th |> dest_imp |> fst
    val rw0 = ASSUME (ml_translatorLib.get_term "remove lookup_cons")
    val tm0 = QCONV (REWRITE_CONV [rw0]) tm |> concl |> rand
    val rw1 = ASSUME (ml_translatorLib.get_term "precond = T")
    val tm1 = QCONV (REWRITE_CONV [rw1]) tm0 |> concl |> rand
    val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val (tms, tys) = match_term (rand pat) (!(#H translator_state))
    val pat = Term.inst tys pat |> Term.subst tms
    val rw2 = ASSUME (list_mk_forall(free_vars pat,pat))
    val tm2 = QCONV (REWRITE_CONV [rw0,rw2,PreImp_def]) tm |> concl |> rand
  in (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) end
  val thms = List.map rephrase_pre thms

  (* check whether the precondition is T *)
  fun get_subst (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    in pre_v |-> true_pre end
  val ss = List.map get_subst thms
  val rw_thms =
    case (!(#store_pinv_def translator_state)) of
        SOME th => th::(get_manip_functions_defs ())
      | NONE => (get_manip_functions_defs ())
  fun is_true_pre (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) =
    ((tm2 |> subst ss
          |> QCONV (REWRITE_CONV
                ([rw2, PreImp_def, PRECONDITION_def, CONTAINER_def] @ rw_thms))
          |> concl |> rand) |> Teq)
  val no_pre = (not o (List.exists (fn x => not x))) (List.map is_true_pre thms)

  (* if no pre then remove pre_var from thms *)
  in if no_pre then let
    fun remove_pre_var (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
      val th5 = INST ss th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
      in (fname,ml_fname,def,th5,(NONE:thm option)) end
    in List.map remove_pre_var thms end else let

  (* Link the EvalM predicates to their "equivalent" pre vars *)
    fun get_pre_var_EvalM_pair (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
        val EvalM_tm = UNDISCH_ALL th |> concl
        val pre_var =
          get_monad_pre_var th (concl def |> dest_eq |> fst) ml_fname
    in (pre_var, EvalM_tm) end
    val pre_var_EvalM_pairs = List.map get_pre_var_EvalM_pair thms
    (* Those rewrites won't be used for any proof:
       only to generate appropriate terms to define the precondition *)
    val pre_var_EvalM_rws = List.map (fn (x, y) => mk_thm([],
        mk_eq(mk_forall(get_EvalM_state y,y), x))) pre_var_EvalM_pairs

  (* Remove the occurences of PreImp and PreCond *)
  fun replace_EvalM (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val rw1 = mk_thm([], get_term "PreImp simp")
    val rws = rw1::pre_var_EvalM_rws
    val assum = concl th |> dest_imp |> fst
    val st = concl th |> dest_imp |> snd |> get_EvalM_state
    val tm = UNDISCH th |> GEN st |> DISCH assum
                     |> PURE_REWRITE_RULE rws |> concl
  in tm end
  val no_quant_pres = List.map replace_EvalM thms
  (* Define the pre conds *)
  val all_pre_vars = List.map ((repeat rator) o fst) pre_var_EvalM_pairs
  val (all_pres_list, vsl) = List.map (fn tm => let
      val vs = op_set_diff aconv (free_vars tm) all_pre_vars
      val def_tm = list_mk_forall(vs, tm)
    in (def_tm, vs) end) no_quant_pres |> unzip
  val all_pres = list_mk_conj all_pres_list
  val (_,pre_ind,pre_def) = Hol_reln [ANTIQUOTE all_pres]
  (* Clean the pre_cond def *)
  val clean_pre_def =
    pre_def |> PURE_REWRITE_RULE [CONTAINER_def,PRECONDITION_def]
  val name = clean_pre_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
               |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val _ = delete_binding (name ^ "_rules") handle NotFound => ()
  val _ = delete_binding (name ^ "_ind") handle NotFound => ()
  val _ = delete_binding (name ^ "_strongind") handle NotFound => ()
  val _ = delete_binding (name ^ "_cases") handle NotFound => ()
  val _ = save_thm(name ^ "_def", clean_pre_def)
(* For every pre_cond, prove that: pre_cond ==> EvalM ... *)

  fun create_pre_var_EvalM_subst (pre_var_tm, EvalM_tm) = let
    val (pre_var, args) = strip_comb pre_var_tm
    val (pre_var_name, pre_var_type) = dest_var pre_var
    val pre_var = mk_var(pre_var_name ^"'", pre_var_type)
    val st = get_EvalM_state EvalM_tm
    val EvalM_abs = list_mk_abs(args, mk_forall(st,EvalM_tm))
  in (pre_var |-> EvalM_abs) end
  val pre_var_EvalM_subst =
    List.map create_pre_var_EvalM_subst pre_var_EvalM_pairs
  val inst_pre_ind = Thm.INST pre_var_EvalM_subst (SPEC_ALL pre_ind)
                            |> CONV_RULE (DEPTH_CONV BETA_CONV)
  fun create_pre_var_T_subst (pre_var_tm, _) = let
    val (pre_var, args) = strip_comb pre_var_tm
    val TRUE = concl TRUE_def |> rand
    val t_abs = list_mk_abs(args, TRUE)
  in (pre_var |-> t_abs) end
  val pre_var_T_subst = List.map create_pre_var_T_subst pre_var_EvalM_pairs

  fun inst_EvalM_thm (vs, (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2)) = let
    val th1 = Thm.INST pre_var_T_subst th
                       |> CONV_RULE (DEPTH_CONV BETA_CONV)
                       |> PURE_REWRITE_RULE[PreImp_PRECONDITION_T_SIMP]
    val assum = concl th1 |> dest_imp |> fst
    val st = concl th1 |> dest_imp |> snd |> get_EvalM_state
    val th2 = UNDISCH th1 |> GEN st |> DISCH assum
    val th3 = GENL vs th2
  in th3 end
  val EvalM_thms = List.map inst_EvalM_thm (zip vsl thms) |> LIST_CONJ
  val thms2 = MATCH_MP inst_pre_ind EvalM_thms |> CONJUNCTS
  val pre_defs = clean_pre_def |> CONJUNCTS |> List.map SPEC_ALL
  (* clean up *)
  fun clean ((pre,lemma), (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2)) = let
    val th1 = SPEC_ALL lemma
    val assum = concl th1 |> dest_imp |> fst
    val th2 = UNDISCH th1 |> SPEC_ALL |> DISCH assum
    val precond_eq = ISPEC assum PRECONDITION_def
    val th3 = PURE_ONCE_REWRITE_RULE[GSYM precond_eq] th2
  in (fname,ml_fname,def,th3,SOME pre) end
  val thms3 = List.map clean (zip (zip pre_defs thms2) thms)
in thms3 end end
handle HOL_ERR _ => failwith "extract_precondition_rec failed";

(* Adapted from translatorLib *)
fun abbrev_code (fname,ml_fname,def,th,v) = let
  val th = th |> UNDISCH_ALL
  val exp = th |> concl |> rator |> rator |> rand
  val n = Theory.temp_binding ("[[ " ^ fname ^ "_code ]]")
  val code_def = new_definition(n,mk_eq(mk_var(n,type_of exp),exp))
  val th =
    CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (K (GSYM code_def))) th
  in (code_def,(fname,ml_fname,def,th,v)) end
(* End of adaptation from translatorLib *)

(* Some definitions might have polymorphic state and exceptions:
   those types need to be instantiated before translation *)
fun instantiate_monadic_types def = let
  val original_def = def
  (* Retrieve the state and exceptions types *)
  val def = List.hd (CONJUNCTS def)
  val ty = concl def |> strip_forall |> snd |> rhs |> type_of
  val state_ty = dest_type ty |> snd |> List.hd
  val exn_ty = dest_type ty |> snd |> List.last |> dest_type |> snd |>
               List.hd |> dest_type |> snd |> List.last
  (* Instantiate them to the proper types *)
  val def =
    if is_vartype state_ty then
      let
        val def = Thm.INST_TYPE[state_ty |-> !(#refs_type translator_state)]
          original_def
      in
        print "Instantiated polymorphic monadic state\n";
        def
      end
    else original_def

  val def =
    if is_vartype exn_ty then
      let
        val def = Thm.INST_TYPE [exn_ty |-> !(#exn_type translator_state)] def
      in
        print "Instantiated polymorphic monadic exceptions\n";
        def
      end
    else def
in def end;

fun get_monadic_types_inst tm = let
    (* Retrieve the state and exceptions types *)
    val ty = type_of tm
    val state_ty = dest_type ty |> snd |> List.hd
    val exn_ty = dest_type ty |> snd |> List.last |> dest_type |> snd |> List.hd
                             |> dest_type |> snd |> List.last
    (* Instantiate them to the proper types *)
    val tys =
      if is_vartype state_ty then
        [state_ty |-> !(#refs_type translator_state)]
      else []
    val tys =
      if is_vartype exn_ty
        then (exn_ty |-> !(#exn_type translator_state)) :: tys
      else tys
in tys end;


(******************************************************************************

  m_translate_main

******************************************************************************)

fun m_translate_main def =
  (let
    (* Instantiate the monadic type if necessary -
       the state and the exceptions can't be polymorphic *)
    val def = instantiate_monadic_types def

    (* Start the translation *)
    val _ = (#H translator_state) := (!(#default_H translator_state))
    val _ = pmatch_index := 1
    val _ = undef_local_code_abbrevs ()
    val _ = (#induction_helper_thms translator_state := [])
    (* perform preprocessing -- reformulate def, register types *)
    fun register_pure_type ty =
      (* Register a type which is neither the monadic state type nor the exc type *)
      if (!(#refs_type translator_state)) = ty
        orelse can (match_type register_pure_type_pat) ty then ()
      else register_type ty;

    val _ = register_term_types register_pure_type (concl def)
    val (is_rec,defs,ind) = preprocess_def def
    val info = List.map get_info defs
    val msg = comma (List.map (fn (fname,_,_,_,_) => fname) info)
    (* val (fname,ml_fname,lhs,tm,def) = List.hd info *)
    (* derive deep embedding *)

    val _ = print ("Translating " ^ msg ^ "\n")
    val _ = List.map (fn (fname,ml_fname,lhs,_,_) =>
                         install_rec_pattern lhs fname ml_fname) info
    val thms = List.map (fn (fname,ml_fname,lhs,rhs,def) =>
                            (fname,ml_fname,m2deep rhs,def)) info
    val _ = uninstall_rec_patterns ()
    val thms = List.map
      (fn (x0,x1,th,x2) => (x0,x1,instantiate_cons_name th,x2)) thms

    fun optimise_and_abstract (fname,ml_fname,th,def) =
      let
        val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
        val no_params = List.length rev_params = 0
        fun EvalM_P_CONV CONV tm =
          if is_imp tm then (RAND_CONV o RATOR_CONV o RAND_CONV) CONV tm
          else (RATOR_CONV o RAND_CONV) CONV tm

        (* replace rhs with lhs *)
        val th = th |> CONV_RULE
                        (EvalM_P_CONV (REWRITE_CONV [CONTAINER_def] THENC
                                       ONCE_REWRITE_CONV [GSYM def]))
        (* optimised generated code - do nothing *)
        val th = disch_asms th
        val (th,v) = if no_params then (th,T) else let
            val params = (if is_rec then butlast rev_params else rev_params)
            val (x, xs) = (hd params, tl params)
            val v = List.last rev_params
            val th1 = apply_EvalM_Fun x th true
            val th2 = List.foldl (fn (v,th) => apply_EvalM_Fun v th true
                       |> remove_ArrowM_EqSt) th1 xs
            in (th2,v) end handle Empty => (th, List.last rev_params)
      in (fname,ml_fname,def,th,v) end

    val thms = List.map optimise_and_abstract thms
    (* final phase: extract precondition, perform induction, store cert *)

    val (is_fun,results) =
      if not is_rec then
        let
        (* non-recursive case *)
          val _ = length thms = 1 orelse failwith "multiple non-rec definitions"
          val (code_def,(fname,ml_fname,def,th,v)) = abbrev_code (hd thms)
          val fname = get_unique_name fname
          (* remove parameters *)
          val th = DISCH_ALL th |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] |>
                   UNDISCH_ALL
          val th = disch_asms (clean_assumptions (disch_asms th))
          val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
          val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                              (SIMP_CONV std_ss [EVAL_T_F])) th
          val th = clean_assumptions (disch_asms th)
          val (lhs,rhs) = dest_eq (concl def)

          (* Precondition *)
          val pre_var = get_monad_pre_var th lhs fname
          val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
          val (th,pre) = extract_precondition_non_rec th pre_var
          (* Remove Eq *)
          val th = remove_Eq th
          (* simpliy EqualityType *)
          val th = SIMP_EqualityType_ASSUMS th
          (* store for later use *)
          val is_fun = code_def |> SPEC_ALL |> concl |> rand |> strip_comb |>
                       fst |> same_const Fun_const
          val th = PURE_REWRITE_RULE[code_def] th
          val th =
            if is_fun then
              th
              |> INST [v_env |-> cl_env_tm]
              |> PURE_REWRITE_RULE[ArrowM_def, code_def]
              |> MATCH_MP EvalM_Fun_Var_intro
              |> PURE_REWRITE_RULE[GSYM ArrowM_def]
              |> SPEC (stringSyntax.fromMLstring ml_fname)
              |> UNDISCH
              |> remove_local_code_abbrevs
            else let
              val _ = failwith "Monadic translation of constants not supported"
            in th end
          val _ = undef_local_code_abbrevs ()
        in
          (is_fun,[(fname,ml_fname,def,th,pre)])
        end
      else (* recursive case *)
        let
        (* introduce Recclosure *)
          val (code_defs,thms) = let val x = List.map abbrev_code thms
                                 in unzip x end
          (* introduce Recclosure *)
          fun mk_Recclosure_part (fname,ml_fname,def,th,v) =
            let
              val fname = ml_fname |> stringLib.fromMLstring
              val name = v |> dest_var |> fst |> stringLib.fromMLstring
              val body = th |> UNDISCH_ALL |> concl |> rator |> rator |> rand
            in pairSyntax.list_mk_pair[fname,name,body] end
          val parts = List.map mk_Recclosure_part thms
          val recc = listSyntax.mk_list(parts,type_of (hd parts))
          val env2 = mk_var("env2", venvironment)
          val shadow_env = mk_var("shadow_env", venvironment)

          fun move_VALID_REFS_PRED_to_assums th = let
              val pat = concl VALID_REFS_PRED_def |> strip_forall |> snd |>
                        dest_eq |> fst
              val H_var = rand pat
              val (tms, tys) = match_term H_var (!(#H translator_state))
              val pat = Term.inst tys pat |> Term.subst tms
              val a = ASSUME pat
              val th = SIMP_RULE bool_ss [a] th
          in th end;

          fun apply_recc (fname,ml_fname,def,th,v) =
            let
              val th = apply_EvalM_Recclosure recc ml_fname v th
              val th = clean_assumptions th
              val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
              val th = INST [env2|->cl_env_tm,shadow_env|->cl_env_tm] th |>
                       REWRITE_RULE [] |>
                       CONV_RULE ((RATOR_CONV o RAND_CONV)
                         (SIMP_CONV std_ss [EVAL_T_F]))
              val th = clean_assumptions th |>  move_VALID_REFS_PRED_to_assums
            in (fname,ml_fname,def,th) end
          val thms = List.map apply_recc thms

          (* collect precondition *)
          val thms = extract_precondition_rec thms

          (* Apply the induction if necessary:
             recursive functions with no preconditions *)
          val thms = case #5 (hd thms) of
                         SOME _ => thms
                       | NONE => apply_ind thms ind

          (* clean up *)
          fun fix_thm th = th |> remove_Eq |> SIMP_EqualityType_ASSUMS |>
            DISCH_ALL |> REWRITE_RULE ((GSYM AND_IMP_INTRO)::code_defs) |>
            UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> remove_local_code_abbrevs

          fun fix (fname, ml_fname, def, th, pre) =
            (fname, ml_fname, def, fix_thm th, pre)

          val results = List.map fix thms
          val _ = (
            #induction_helper_thms translator_state :=
              List.map ((fn x => x) ## fix_thm)
                (!(#induction_helper_thms translator_state))
            )

          val _ = List.map
            (delete_const o fst o dest_const o fst o dest_eq o concl) code_defs
          val _ = undef_local_code_abbrevs ()
        in (true, results) end

    fun check results =
      let
        val f = LIST_CONJ (List.map #4 results) |> disch_asms |> concl |>
          can (find_term (can (match_term (ml_translatorLib.get_term "WF"))))
      in
        if f then failwith "WF" else (is_rec,is_fun,results)
      end

  in check results end)

  handle UnableToTranslate tm => (
    print "\n\nCannot translate term:  ";
    print_term tm;
    print "\n\nwhich has type:\n\n";
    print_type (type_of tm);
    print "\n\n";
    raise UnableToTranslate tm
  )

  handle e => (
    let val names = def |> SPEC_ALL |> CONJUNCTS |>
                    List.map (fst o dest_const o repeat rator o fst o dest_eq o
                      concl o SPEC_ALL) |> all_distinct
                    handle HOL_ERR _ => ["<unknown name>"]
    in
      print ("Failed translation: " ^ comma names ^ "\n");
      raise e
    end
  )

(******************************************************************************

  m_translate

******************************************************************************)

val unknown_loc = locationTheory.unknown_loc_def |> concl |> dest_eq |> fst;

fun add_dynamic_v_thms (name, ml_name, th, pre_def) = let
    val th = UNDISCH_ALL th
    val thc = concl th
    val hol_fun = thc |> rator |> rand
in
    #dynamic_v_thms translator_state :=
      (Net.insert (hol_fun, (name, ml_name, hol_fun, th, pre_def, NONE))
        (!(#dynamic_v_thms translator_state)));
    print("Added a dynamic specification for "
          ^ (dest_const hol_fun |> fst) ^ "\n");
    if Teq (concl pre_def) then () else
      (print ("\nWARNING: " ^ml_name^" has a precondition.\n\n"))
end;

fun update_local_precondition new_pre = let
  fun update_aux (name,ml_name,tm,th,pre,module) =
    let val th1 = disch_asms th
        val (new_pre,th1) =
          (if is_imp (concl (SPEC_ALL new_pre))
           then (* case: new_pre is an induction theorem *)
             (((MATCH_MP IMP_EQ_T (MP (disch_asms new_pre) TRUTH)
               handle HOL_ERR _ => new_pre)
               |> PURE_REWRITE_RULE [GSYM CONJ_ASSOC]),
              PURE_REWRITE_RULE [GSYM CONJ_ASSOC] th1)
          else (new_pre,th1))
        val th2 = PURE_REWRITE_RULE [new_pre, PRECONDITION_T] th1
    in
      if aconv (concl th1) (concl th2)
      then (name,ml_name,tm,th,pre,module) else
        let val th2 = REWRITE_RULE [] th2
            val th = remove_Eq_from_v_thm th2
            val thm_name = name ^ "_v_thm"
            val _ = print ("Updating " ^ thm_name ^ "\n")
            (* val _ = save_thm(thm_name,th) *)
            val new_pre =
              if can (find_term ml_translatorSyntax.is_PRECONDITION)
                  (concl (SPEC_ALL th))
              then new_pre else TRUTH
            val th = th |> UNDISCH_ALL
         in (name,ml_name,tm,th,new_pre,module) end
    end
  in
    #dynamic_v_thms translator_state :=
      Net.map update_aux (!(#dynamic_v_thms translator_state));
    new_pre
  end

fun m_translate def =
  let
      val (is_rec,is_fun,results) = m_translate_main (* m_translate *) def
  in
    if is_rec then
    let
      val recc = results |> List.map (#4) |> hd |>
        hyp |> first (can (match_term LOOKUP_VAR_pat)) |> rand |> rator |> rand
      val ii = INST [cl_env_tm |-> get_curr_env()]
      val v_names = List.map (fn x => find_const_name (#1 x ^ "_v")) results
      val _ = if not (!(#local_state_init_H translator_state))
              then ml_prog_update (add_Dletrec unknown_loc recc v_names)
              else ()
      val v_defs =
        if not (!(#local_state_init_H translator_state)) then
          List.take(get_curr_v_defs (), length v_names) else []
      val jj = INST
        (if !(#local_state_init_H translator_state) then []
          else [v_env |-> get_curr_env()])
      val lemmas = LOOKUP_VAR_def :: List.map GSYM v_defs

      fun inst_helper_envs (name, th) =
        let val th' = th |> ii |> jj |> disch_asms |> REWRITE_RULE lemmas |>
                      SIMP_RULE std_ss [lookup_var_def] |> clean_assumptions |>
                      DISCH_ALL
        in
          save_thm(name, th');
          print ("Saved theorem ____ :" ^ name ^ "\n");
          (name, th')
        end

      val _ = (
        #induction_helper_thms translator_state :=
          List.map inst_helper_envs (!(#induction_helper_thms translator_state))
        )

      fun inst_envs (fname,ml_fname,def,th,pre) = let
          val th = th |> ii |> jj
          val state_var = concl th |> get_EvalM_state
          val th = GEN state_var th |>
                   (CONV_RULE ((QUANT_CONV o RATOR_CONV o RAND_CONV o
                                RATOR_CONV o RATOR_CONV o RAND_CONV)
                                   (PURE_REWRITE_CONV [ArrowM_def])))
          val th = (MATCH_MP EvalM_Var_ArrowP th
                   handle HOL_ERR _ => MATCH_MP EvalM_Var_ArrowP_EqSt th)
                   |> PURE_REWRITE_RULE [GSYM ArrowM_def]
          val assum = concl th |> dest_imp |> fst
          val v = th |> hyp |> first (can (match_term assum)) |> rand
          val th = INST [rand assum |-> v] th |> UNDISCH
          val th = disch_asms th |> REWRITE_RULE lemmas
                     |> SIMP_RULE std_ss [lookup_var_def]
                     |> clean_assumptions |> UNDISCH_ALL
          val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
          val th =
              if !(#local_state_init_H translator_state) then
                (add_dynamic_v_thms(fname, ml_fname, th, pre_def);
                th)
              else
                (add_v_thms (fname,ml_fname,th,pre_def);
                save_thm(fname ^ "_v_thm", th))
      in th end
      val thms = List.map inst_envs results
    in LIST_CONJ thms end
    else (* not is_rec *) let
      val (fname,ml_fname,def,th,pre) = hd results
    in
      if is_fun then let
        val th = th |> INST [cl_env_tm |-> get_curr_env()]
        val n = ml_fname |> stringSyntax.fromMLstring
        val lookup_var_assum = th |> hyp |>
          first (can (match_term(LOOKUP_VAR_def |> SPEC n |>
            SPEC_ALL |> concl |> lhs)))
        val state_var = concl th |> get_EvalM_state
        val lemma = th |> DISCH lookup_var_assum
                       |> GENL [state_var, v_env]
                       |> MATCH_MP LOOKUP_VAR_EvalM_ArrowM_IMP
                       |> disch_asms |> clean_assumptions |> UNDISCH_ALL
        val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
        val th =
          if !(#local_state_init_H translator_state) then let
              val th = lemma |> Q.INST [`cl_env`|->`^(get_curr_env())`]
                             |> DISCH_ALL
              val _ = add_dynamic_v_thms(fname,ml_fname,th,pre_def)
          in th end
          else let
              val v = lemma |> concl |> rand |> rator |> rand
              val exp = lemma |> concl |> rand |> rand
              val v_name = find_const_name (fname ^ "_v")
              val _ = ml_prog_update (add_Dlet_Fun unknown_loc n v exp
                                                   v_name)
              val v_def = hd (get_curr_v_defs ())
              val v_thm = lemma |>
                          CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def)))
              val _ = add_v_thms (fname,ml_fname,v_thm,pre_def)
          in save_thm(fname ^ "_v_thm",v_thm) end
        in th end
      else (failwith "Monadic translation of constants not supported"; th) end
  end
  handle
    UnableToTranslate tm => (
      print "\n\nml_translate: cannot translate term:  ";
      print_term tm;
      print "\n\nwhich has type:\n\n";
      print_type (type_of tm);
      print "\n\n";
      raise UnableToTranslate tm
    )
  | HOL_ERR err => (
      print "\n\nml_translate: \
        \unexpected error when translating definition:\n\n";
      print_thm def;
      print "\n\n";
      raise (HOL_ERR err)
    )

(******************************************************************************

  m_translate_run

******************************************************************************)

fun compute_env_index env = let
    val env_name = dest_var env |> fst
    val env_index_str = String.extract (
      env_name, String.size (!(#local_environment_var_name translator_state)),
      NONE)
    val index = string_to_int env_index_str
in index end;

fun instantiate_local_environment th = let
    (* Instantiate a new environment -
       we need env to have the proper shape : merge_env ... *)
    val env = concl th |> rator |> rator |> rator |> rator |> rand
    val new_env = get_curr_env()
    val th = Thm.INST [env |-> new_env] th
in th end

fun clean_lookup_assums th = let
    val th = remove_local_code_abbrevs th
    val th = HYP_CONV_RULE (fn x => true)
      (SIMP_CONV list_ss
        (build_rec_env_def :: lookup_var_write :: LOOKUP_ASSUM_SIMP ::
          FOLDR :: string_rewrites)) th
    val th = HYP_CONV_RULE (fn x => true)
      (PURE_REWRITE_CONV (List.map GSYM
        (!(#local_code_abbrevs translator_state)))) th
    val th = MP (DISCH T th ) TRUTH handle HOL_ERR _ => th
in th end

fun create_local_fun_defs th =
  let
    (* Retrieve the lookup assumptions for the functions definitions *)
    val assums =  List.filter (can (match_term nsLookup_pat)) (hyp th)
    fun get_name_expr tm = ((rand o rand o rand o rator)tm,(rand o rand)tm)
    val lookup_info = List.map get_name_expr assums

    (* Remove the variables and the non-monadic functions,
       retrieve the closure environment *)
    val lookup_info = List.filter(fn (x, y) => not(is_var y)) lookup_info

    fun get_clenv_var expr =
      let
        val clenv = rator expr |> rator |> rand
        val _ = if is_var clenv andalso type_of clenv = venvironment then ()
                else failwith "get_env_var"
      in clenv end
    fun get_clenv_index_var (name, expr) =
      let
        val clenv = get_clenv_var expr
        val index = compute_env_index clenv
      in (index, (clenv, name, expr)) end
    val lookup_info = mapfilter get_clenv_index_var lookup_info

    (* Sort the lookup assumptions, eliminate the redundant definitions
       (introduced by the mutually recursive functions *)
    val insert_map = (fn ((i, info),m) => Redblackmap.insert(m, i, info))
    val env_clos_map = Redblackmap.mkDict (Int.compare)
    val env_clos_map = List.foldl insert_map env_clos_map lookup_info
    val defs_info = Redblackmap.listItems env_clos_map
    fun assum_order (i1 : int, _) (i2 : int, _) = i1 > i2
    val defs_info = Lib.sort assum_order defs_info
    val defs_info = List.map #2 defs_info

    (* Create the function definitions (Let expressions) *)
    val current_env = concl th |> rator |> rator |> rator |> rator |> rand
    val all_envs = List.map #1 defs_info
    val last_env = List.last all_envs
    val all_envs = current_env::(List.take(all_envs, List.length all_envs - 1))
    val defs_env_info = zip all_envs defs_info

    (* val (env_var2, (env_var1, name, fexp)) = List.hd defs_env_info *)
    val i = ref (List.length defs_env_info)
    fun print_countdown () = (print ((Int.toString (!i) ^" ")); i := (!i - 1))
    fun create_fun_let ((env_var2, (env_var1, name, fexp)), th) =
      if is_Recclosure fexp then
        let
          (* Print countdown *)
          val _ = print_countdown ()

          (* Build the new environment *)
          val funs = rator fexp |> rand
          val exp = concl th |> rator |> rator |> rand
          val st = get_EvalM_state (concl th)
          val P = th |> concl |> rator |> rand
          val lemma =
            ISPECL [funs, env_var1, exp, st, P,
                    (!(#H translator_state)) |> inst [ffi_ty_var |-> unit_ty]]
              EvalSt_Letrec_Fun

          (* Prove the assumption *)
          val assum = concl lemma |> dest_imp |> fst
          val assum_th =
            ((PURE_REWRITE_CONV (!(#local_code_abbrevs translator_state)))
              THENC EVAL) assum |>
            EQT_ELIM
          val lemma = MP lemma assum_th

          (* Subsitute the new environment *)
          val nenv = concl lemma |> dest_imp |> fst |> rator |> rator
                           |> rator |> rator |> rand
          val lemma = MP lemma (INST [env_var2 |-> nenv] th)

          (* Cleanup *)
          val lemma = clean_lookup_assums lemma
        in lemma end
      else
        let
          (* Closure *)

          (* Print countdown *)
          val _ = print_countdown ()

          (* Build the new environment *)
          val vname = name
          val xv = rator fexp |> rand
          val fexp = rand fexp

          val Closure_exp = list_mk_comb(Closure_const,[env_var1,xv,fexp])
          val nenv = mk_write vname Closure_exp env_var1

          (* Replace the environment and create the Let expression *)
          val th' = Thm.INST [env_var2 |-> nenv] th
          val th' = MATCH_MP EvalSt_Let_Fun th' |> clean_lookup_assums
        in th' end
    val _ = print "Defining local functions: "
    val th = List.foldl create_fun_let th defs_env_info
    val _ = print "\n"
  in th end;

fun gen_name_tac name (g as (asl, w)) = let
    val renamed_w_th = RENAME_VARS_CONV [name] w
in (PURE_ONCE_REWRITE_TAC[renamed_w_th] \\ strip_tac) g end

fun create_local_references init_state th = let
    (* Check that FST and SND are already translated *)
    val _ = if not(can hol2deep FST_const) then translate FST else TRUTH
    val _ = if not(can hol2deep SND_const) then translate SND else TRUTH

    (* *)
    val th = PURE_REWRITE_RULE[!(#H_def translator_state)] th
                              |> PURE_ONCE_REWRITE_RULE[GSYM H_STAR_emp]
                              |> PURE_REWRITE_RULE[GSYM STAR_ASSOC]
    (* Rename the state variable in the heap invariant *)
    val state_var = concl th |> rator |> rator |> rator |> rand
    val state = concl th |> rator |> rand |> rand |> rand
    val monad_state_is_var = is_var state_var
    val th = if monad_state_is_var then let
        val H_eq = ((RATOR_CONV o RAND_CONV) (ALPHA_CONV state_var))
                       (concl th |> rand)
        val th = PURE_ONCE_REWRITE_RULE[H_eq] th
    in th end else th

    val P = concl th |> rator |> rand
    val init_state_type = type_of init_state
    val STATE_RI = get_type_inv init_state_type

    (* Some preliminaries in the case non resizable arrays are used:
       need to establish a link between the accessors of the two state types *)
    val init_state_type = type_of init_state
    val get_access_term = rator o lhs o snd o strip_forall o concl
    val state_accessors_thms = TypeBase.accessors_of (type_of state_var)
    val state_accessors = List.map get_access_term  state_accessors_thms
    val init_state_accessors_thms = TypeBase.accessors_of init_state_type
    val init_state_accessors =
      List.map get_access_term init_state_accessors_thms
    val state_accessors = zip state_accessors init_state_accessors

    fun get_farray_access_fun state_field = let
        val accessor = rator state_field
        fun is_ok (x, _) = same_const x accessor
        val accessor = first is_ok state_accessors |> snd
    in accessor end

    (* Some other facilities *)
    val rewrite_field_access_conv =
        QCONV(SIMP_CONV std_ss (#rewrs (TypeBase.simpls_of init_state_type)))
    fun rewrite_field_access_rule eq =
      (CONV_RULE o RAND_CONV o RAND_CONV)
          (PURE_ONCE_REWRITE_CONV [GSYM eq])
    fun get_field_access_eval_thm tm = let
        val tm_eq = rewrite_field_access_conv tm
        val tm = concl tm_eq |> rhs
        val eval_thm = hol2deep tm |> rewrite_field_access_rule tm_eq
    in eval_thm end

    val loc_info = !(#dynamic_refs_bindings translator_state)

    (* Create the references for the references and the resizable arrays *)

    fun create_local_refs [] th = th
      | create_local_refs ((loc_name, loc)::loc_info) th = let
        val exp = concl th |> rator |> rator |> rand
        val originalH = concl th |> rand
        val (state_var,H_part) = dest_abs (originalH |> dest_pair |> fst)
        val (H_part1, H_part2) = dest_star H_part
        val H_part2 = mk_abs(state_var, H_part2)

        val state_field = rand H_part1
        val get_ref_fun = mk_abs(state_var, state_field)
        val TYPE = get_type_inv (type_of state_field)

        val accessor = get_farray_access_fun state_field
        val Eval_state_field =
            get_field_access_eval_thm (mk_comb (accessor, init_state))

        val get_ref_exp = concl Eval_state_field |> get_Eval_exp
        val st_name = stringLib.fromMLstring (dest_var state_var |> fst)
        val env = concl th |> rator |> rator |> rator |> rator |> rand

        val nenv = mk_write loc_name loc env
        val gen_th = INST[env |-> nenv] th |> clean_lookup_assums |> GEN loc
        val is_rarray = concl th |> rand |> dest_pair |> fst
                             |> dest_abs |> snd |> dest_star
                             |> fst |> strip_comb |> fst
                             |> same_const RARRAY_REL_const
        val is_farray = concl th |> rand |> dest_pair |> fst
                             |> dest_abs |> snd |> dest_star
                             |> fst |> strip_comb |> fst
                             |> same_const ARRAY_REL_const

        val lemma =
        if is_rarray then
            ISPECL[exp, get_ref_fun, loc_name,
                   rand TYPE, st_name, env, H_part2, P, state_var]
                  EvalSt_AllocEmpty |> BETA_RULE |> UNDISCH
         else if is_farray then let
            val ntm =
              my_list_mk_comb(FST_const, [mk_comb(accessor, init_state)])
            val nexp_eval = get_field_access_eval_thm ntm
            val nexp = concl nexp_eval |> rator |> rand
            val n = concl nexp_eval |> rand |> rand

            val xtm =
              my_list_mk_comb(SND_const, [mk_comb(accessor, init_state)])
            val xexp_eval = get_field_access_eval_thm xtm
            val xexp = concl xexp_eval |> rator |> rand
            val (TYPE, x) = concl xexp_eval |> rand |> dest_comb

            val lemma =
              PURE_REWRITE_RULE [GSYM NUM_def, GSYM INT_def] EvalSt_Alloc
            val lemma =
              ISPECL [exp, nexp, n, xexp, x, rator state_field, loc_name,
                      TYPE, env, H_part2, P, state] lemma |> UNDISCH
            val lemma = MATCH_MP (MATCH_MP lemma nexp_eval) xexp_eval
            val lemma = CONV_RULE (DEPTH_CONV BETA_CONV) lemma
            val EQ_pat = EQ_def |> SPEC_ALL |> concl |> dest_eq |> fst
            val EQ_assums = lemma |> hyp |> filter (can (match_term EQ_pat))
            fun remove_EQ_assums [] th = th
              | remove_EQ_assums (goal::goals) th = let
                  val l = auto_prove "EQ_assum" (goal, SIMP_TAC (srw_ss())
                                                        [EQ_def])
                  val th = MP (DISCH (concl l) th) l
                  in remove_EQ_assums goals th end
                  handle HOL_ERR _ => remove_EQ_assums goals th
            val lemma = remove_EQ_assums EQ_assums lemma
        in lemma end
        else MATCH_MP (ISPECL[exp, get_ref_exp, get_ref_fun, loc_name,
                       TYPE, st_name, env, H_part2, P, state]
                       EvalSt_Opref |> BETA_RULE |>
                       PURE_REWRITE_RULE state_accessors_thms) Eval_state_field
        val th = MY_MATCH_MP lemma gen_th
    in create_local_refs loc_info th end

    val th = create_local_refs loc_info th

    (* Transform the EvalSt predicate to an Eval predicate *)
    val th = MATCH_MP EvalSt_to_Eval th
in th end

fun apply_Eval_Fun_Eq ((vname,x), th) = let
    val env = get_Eval_env (concl th)
    val v = genvar v_ty
    val tms = FVL [x,v] empty_varset
    val nenv = mk_write vname v env
    val th = INST [env |-> nenv] th |> clean_lookup_assums
    val A = mk_var("A",mk_type("fun",[type_of x,v_bool_ty]))
    val pat = list_mk_comb(A,[x,v_var])
    val assum = List.filter (can (fn y => Term.raw_match [] tms pat y ([], [])))
      (hyp th) |> hd
    val x = assum |> rator |> rand
    val th = CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV x)) th
             |> DISCH assum |> GEN v
    val th = MATCH_MP Eval_Fun_Eq th
in th end

fun m_translate_run_abstract_parameters th def params_evals = let
    val params_bindings =
      List.map (fn x => (concl x |> rator |> rator |> rand |> rand |> rand,
                         concl x |> rator |> rand |> rand)) params_evals
    val th = PURE_REWRITE_RULE [GSYM def] th
    val th = List.foldr apply_Eval_Fun_Eq th params_bindings

    (* Rewrite the function in the theorem *)
    val f = concl th |> rand |> rand
    val fc = SPEC_ALL def |> concl |> dest_eq |> fst |> strip_comb |> fst
    val f_eq = prove(mk_eq(f,fc),
                     rpt (irule EQ_EXT >> rw[]) >> rw[] >> EVAL_TAC)
    val th = PURE_REWRITE_RULE [f_eq] th
in th end

fun m_translate_run_preprocess_def def = let
    (* Instantiate the monadic state and exceptions if they are polymorphic *)
    val tys = get_monadic_types_inst
      (def |> concl |> strip_forall |> snd |> rhs |> rator |> rand)
    val _ = if List.length tys > 0 then
      print "m_translate_run: instantiated monadic types\n" else ()
    val def = Thm.INST_TYPE tys def
    val _ = undef_local_code_abbrevs ()

    (* preprocessing: register types *)
    val _ = register_term_types register_type (concl def)
in def end

fun m_translate_run def =
  let
    (* Preprocess *)
    val def = m_translate_run_preprocess_def def |> rename_bound_vars_rule "v"

    (* Decompose the definition *)
    val (def_lhs, def_rhs) = concl def |> strip_forall |> snd |> dest_eq

    val fname = repeat rator def_lhs |> dest_const |> fst |> get_unique_name
    val _ = print ("Translating monadic run: " ^ fname ^ "\n")
    val fname_str = stringLib.fromMLstring fname

    val state = rand def_rhs
    val monad_tm = rand (rator def_rhs)
    val run_tm = rator(rator def_rhs)
    val (monad_f, monad_params) = strip_comb monad_tm

    (* Find which run constant is used *)
    val using_monadBase_run = same_const run_tm run_const

    val run_def = if using_monadBase_run then ml_monadBaseTheory.run_def else
      let val run_name = dest_const run_tm |> fst
          val pos_defs = DB.find (run_name ^ "_def") |> List.map (fst o snd)
          fun is_def th =
            let val constant = CONJUNCTS th |> List.hd |> concl |>
                               strip_forall |> snd |> lhs |> strip_comb |> fst
            in same_const run_tm constant end
      in first is_def pos_defs end

    val def =
      if using_monadBase_run then def else PURE_REWRITE_RULE [run_def] def

    (* If non resizable arrays are used, rewrite the expression, and find the
       two different used state expressions *)
    val (state, init_state) =
      if using_monadBase_run then (state, state)
      else let
        val rw_def_rhs = PURE_REWRITE_CONV [run_def] def_rhs |> concl |> rhs
        val init_state = state
        val state = rand rw_def_rhs
      in (state, init_state) end

    (* Construct the Eval predicates for the parameters *)
    fun var_create_Eval tm =
      let
        val (name,ty) = dest_var tm
        val inv = get_type_inv ty
        val str = stringSyntax.fromMLstring name
        val result = ISPECL_TM [str,mk_comb(inv,tm)] Eval_name_RI_abs |> ASSUME
        val result = HO_MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result
        val st = concl result |> get_EvalM_state
        val result = INST [st |-> state] result
        val result =
          INST [(rand o rator o rator o rator o rator o
                 rator o concl o UNDISCH_ALL) result |-> T] result
      in check_inv "var" tm result end
    val params_evals = List.map var_create_Eval monad_params

    (* Get the monadic specification *)
    val _ = (#local_code_abbrevs translator_state) := []
    val monad_th = lookup_dynamic_v_thm monad_f
    fun inst_state_type th =
      let
        val ty = concl th |> dest_forall |> fst |> type_of |> dest_prod
                 |> fst |> dest_type |> snd |> hd
      in INST_TYPE [ty |-> !(#refs_type translator_state)] th end
    val monad_th =
      MATCH_MP (inst_state_type Eval_IMP_PURE_EvalM_T) monad_th
      |> ISPEC (!(#H translator_state))
      |> PURE_REWRITE_RULE[GSYM ArrowM_def]
      |> abbrev_nsLookup_code
    val monad_th = INST [concl monad_th |> get_EvalM_state |-> state] monad_th

    (* Instantiate the ro boolean to T *)
    val ro_var = concl monad_th |> rator |> rand |> strip_comb |> snd |> hd
    val monad_th =
      if is_var ro_var then INST [ro_var |-> T] monad_th
        else monad_th

    fun inst_gen_eq_vars2 st th = let
      (* Instantiate the variables in the occurences of Eq*)
      val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
      val xs = find_terms (can (match_term pat)) (concl th) |> List.map rand
      val ss = List.map (fn v => v |-> genvar(type_of v)) xs
      val th = INST ss th
      (* Instantiate the variable in EqSt *)
      val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
          |> concl |> rator |> rand |> rator |> rand
      val state_var_opt = get_EqSt_var thc
      val th = (
        case state_var_opt of
            NONE => th
          | SOME v => INST [v |-> st] th)
    in th end

    (* Insert the parameters *)
    val monad_th = inst_gen_eq_vars2 state monad_th
                   handle HOL_ERR _ => monad_th
    fun insert_param (x, th) =
      MY_MATCH_MP(MATCH_MP EvalM_ArrowM_EqSt_Eq th) x
      handle HOL_ERR _ => MY_MATCH_MP(MATCH_MP EvalM_ArrowM_Eq th) x
      handle HOL_ERR _ => MY_MATCH_MP(MATCH_MP EvalM_ArrowM th) x
    val monad_th = List.foldl insert_param monad_th params_evals
    val monad_th = monad_th |> INST_TYPE [ffi_ty_var |-> unit_ty]

    (* Add the state parameter Eval assumption *)
    val monad_state_is_var = is_var init_state

    (* Retrieve information about the exc type *)
    val EXC_TYPE_tm = get_type_inv exc_ty |> rator |> rator
    (* TODO: Not sure if this is the right lookup *)
    val EXC_TYPE_def = (if !use_full_type_names then
                        DB.find "ML_MONADBASE_EXC_TYPE_def"
                       else
                        DB.find "EXC_TYPE_def")
                       |> List.hd |> snd |> fst
                       handle Empty =>
                        raise (ERR "m_translate_run" "The `exc` type needs to \
                               \be registered in the current program")
    val EXC_TYPE_stamp = concl EXC_TYPE_def |> list_dest dest_conj |> List.hd
                      |> strip_forall |> snd |> rhs |> strip_exists |> snd
                      |> dest_conj |> fst |> rhs |> rator |> rand |> rand
                      |> rand
    val EXC_TYPE_RW =
      let
        val x = EXC_TYPE_aux_def |> CONJUNCT1 |> SPEC EXC_TYPE_stamp
                |> SPEC_ALL |> concl |> dest_eq |> fst
                |> rator |> rator |> rator |> rator
        val t = fs [FUN_EQ_THM] \\ GEN_TAC \\ GEN_TAC
                   \\ Cases \\ GEN_TAC \\ EVAL_TAC
        val lemma = auto_prove "EXC_TYPE_RW" (mk_eq(x,EXC_TYPE_tm),t)
      in lemma end

    (* Translate the run construct *)
    val env = concl monad_th |> get_Eval_env
    val x = concl monad_th |> get_Eval_arg
    val exp = concl monad_th |> get_Eval_exp
    val MONAD_TYPE = concl monad_th |> rator |> rand |> rator
    val EXN_TYPE = rand MONAD_TYPE
    val TYPE = rator MONAD_TYPE |> rand

    val th = ISPECL [EXC_TYPE_stamp, TYPE, EXN_TYPE, x, exp,
                     (!(#H translator_state)) |> inst [ffi_ty_var |-> unit_ty],
                     state, env]
                    EvalM_to_EvalSt
    val th = PURE_REWRITE_RULE [EXC_TYPE_RW] th

    val th = MATCH_MP th monad_th |> UNDISCH |> UNDISCH

    (* Replace the environment *)
    val th = instantiate_local_environment th

    (* Create the local function definitions *)
    val th = create_local_fun_defs th

    (* Create the store *)
    val th = create_local_references init_state th

    (* Abstract the parameters *)
    val all_params = strip_comb def_lhs |> snd
    val params_evals = List.map var_create_Eval all_params

    val th = m_translate_run_abstract_parameters th def params_evals

    (* Clean up any stray lookup_cons with variables in them *)
    val th = instantiate_cons_name th

    (* Instantiate the environment 0 *)
    val global_env = get_env(get_curr_prog_state())
    val env = concl th |> get_Eval_env
    val th = INST [env |-> global_env] th

    (* clean up the assumptions *)
    fun add_T_imp th =
        if (is_imp o concl) th then th
        else DISCH (concl TRUTH) th
    val th = clean_assumptions (disch_asms th) |> add_T_imp

    (* Introduce the precondition *)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (SIMP_CONV (srw_ss()) [EQ_def,PRECONDITION_def])) (disch_asms th)
    val precond = concl th |> dest_imp |> fst
    val is_precond_T = same_const (concl TRUTH) precond
    val (th,pre) =
      if is_precond_T then (MP th TRUTH, TRUTH)
      else let
        val pre_type = List.foldr (fn (x,y) => x --> y) bool_ty
                      (List.map type_of all_params)
        val extra_free_vars = free_vars precond |>
                              List.filter (fn var => not (tmem var all_params))
        val pre_type = List.foldr (fn (x,y) => x --> y) pre_type
                      (List.map type_of extra_free_vars)
        val pre_var = mk_var(fname ^"_side", pre_type)
        val pre = list_mk_comb (pre_var, extra_free_vars @ all_params)
        val def_tm = mk_eq(pre,precond)
        val pre_def = quietDefine [ANTIQUOTE def_tm]
        val pre_eq = SPEC (SPEC_ALL pre_def |> concl |> lhs)
                     PRECONDITION_def
        val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               ((PURE_REWRITE_CONV [GSYM pre_def]) THENC
                (PURE_ONCE_REWRITE_CONV[GSYM pre_eq]))) th
                            |> UNDISCH
      in (th, pre_def) end

    (* Expand the abbreviated expressions and the handle_mult term *)
    val th = PURE_REWRITE_RULE[handle_mult_def] th
                              |> remove_local_code_abbrevs
    val _ = undef_local_code_abbrevs()

    (* Store the spec *)
    val th = PURE_REWRITE_RULE[Eval_Fun_rw] th
    val v = th |> concl |> rand |> rator |> rand
    val e = th |> concl |> rand |> rand
    val v_name = find_const_name (fname ^ "_v")
    val _ = ml_prog_update (add_Dlet_Fun unknown_loc fname_str v e v_name)
    val s = get_curr_prog_state ()
    val v_def = hd (get_v_defs s)
    val th = th |> REWRITE_RULE [GSYM v_def]
    val th = remove_Eq_from_v_thm th

    (* Store the certificate for later use *)
    val _ = add_v_thms (fname,fname,th,pre)
    val _ = print "Added to v_thms\n"
    val th = save_thm(fname ^ "_v_thm",th)
    val _ = print ("Saved theorem ____ :" ^fname ^ "_v_thm\n")
  in th end


(******************************************************************************

  m_translate_extends - code for resuming a monadic translation.

  Packs all the monadic state into a theorem when the theory is exported.
   The translation can then be resumed by a call to m_translation_extends,
   which acts as a stand-in to translation_extends from the standard translator.

   The following fields are currently *not* saved:
    - local_state_init_H : bool ref,
    - dynamic_v_thms :
        (string * string * term * thm * thm * string option) net ref,
    - local_environment_var_name = string ref,
    - num_local_environment_vars = int ref

  Previously not saved:
    - store_pinv_def : thm option ref,
    - dynamic_v_thms :
        (string * string * term * thm * thm * string option) net ref,
    - dynamic_refs_bindings = (term * term) list ref,
    - local_code_abbrevs = thm list ref,
    - mem_derive_case_ref = (hol_type * thm) list ref
    - local_environment_var_name = string ref,
    - num_local_environment_vars = int ref

******************************************************************************)

local
  (*
    Code for loading and storing the monadic translator state,
    as the things in ml_translatorLib does not include the
    bits and pieces specific to the monadic translator (i.e.
    exceptions, refs, et caetera.

    Installs a hook to fire off on export_theory (like in the standard
    translator) and recursively calls on translation_extends to load all
    the standard translator state as well.
  *)
  val suffix = "_monad_translator_state_thm";
  val st = translator_state;

  fun check_uptodate_term tm =
    if Theory.uptodate_term tm then ()
    else
      let val t = find_term
            (fn tm => is_const tm andalso not (Theory.uptodate_term tm)) tm
      in
        print "\n\nFound out-of-date term: ";
        print_term t;
        print "\n\n"
      end;

  fun pack_translator_state () =
    pack_list I [
      pack_type                                 (!(#refs_type st)),
      pack_type                                 (!(#exn_type st)),
     (pack_option pack_thm)                     (!(#VALID_STORE_THM st)),
      pack_thm                                  (!(#EXN_TYPE_def st)),
      pack_term                                 (!(#EXN_TYPE st)),
     (pack_list pack_string)                    (!(#type_theories st)),
     (pack_list (pack_pair pack_term pack_thm)) (!(#exn_handles st)),
     (pack_list (pack_pair pack_term pack_thm)) (!(#exn_raises st)),
     (pack_list (pack_pair pack_thm pack_thm))  (!(#exn_functions_defs st)),
      pack_term                                 (!(#default_H st)),
      pack_thm                                  (!(#H_def st)),
      pack_term                                 (!(#H st)),
     (pack_list (pack_pair pack_term pack_thm)) (!(#access_patterns st)),
     (pack_list (pack_pair pack_thm pack_thm))  (!(#refs_functions_defs st)),
     (pack_list (pack_6tuple
                 pack_thm pack_thm pack_thm
                 pack_thm pack_thm pack_thm))   (!(#rarrays_functions_defs st)),
     (pack_list (pack_5tuple
                 pack_thm pack_thm pack_thm
                 pack_thm pack_thm))            (!(#farrays_functions_defs st)),
     (pack_option pack_thm)                     (!(#store_pinv_def st)),
     (pack_list
        (pack_pair pack_term pack_term))        (!(#dynamic_refs_bindings st)),
     (pack_list pack_thm)                       (!(#local_code_abbrevs st)),
     (pack_list (pack_pair pack_type pack_thm)  (!(#mem_derive_case_ref st)))
    ]

  fun save_translator_state () =
    let
      val name = Theory.current_theory () ^ suffix
      val name_tm = stringSyntax.fromMLstring name
      val tag_lemma = ISPEC (mk_var("b",bool)) (ISPEC name_tm TAG_def) |> GSYM
      val packed = pack_translator_state()
      val th = PURE_ONCE_REWRITE_RULE [tag_lemma] packed
    in
      check_uptodate_term (concl th);
      save_thm(name, th)
    end

  fun unpack_translator_state th = (
    case (unpack_list I th) of
      [
        refs_type, exn_type, VALID_STORE_THM, EXN_TYPE_def, EXN_TYPE,
        type_theories, exn_handles, exn_raises, exn_functions_defs, default_H,
        H_def, H, access_patterns, refs_functions_defs, rarrays_functions_defs,
        farrays_functions_defs, local_state_init_H, store_pinv_def,
        dynamic_refs_bindings, local_code_abbrevs, mem_derive_case_ref
      ] => let

        (* Need to add the current theory to type_theories or we cannot
           access definitions generated after extending! *)
        val type_theories_unpacked = type_theories |>
                                     (unpack_list unpack_string)

        val curr_thy =
          case List.find (fn thy => thy = current_theory())
                  type_theories_unpacked
          of
              NONE => [current_theory ()]
            | _ => []
      in
        #refs_type st := (refs_type |> unpack_type);
        #exn_type st := (exn_type |> unpack_type);
        #VALID_STORE_THM st := (VALID_STORE_THM |> (unpack_option unpack_thm));
        #EXN_TYPE_def st := (EXN_TYPE_def |> unpack_thm);
        #EXN_TYPE st := (EXN_TYPE |> unpack_term);
        #type_theories st := (type_theories_unpacked @ curr_thy);
        #exn_handles st := (exn_handles |>
                            (unpack_list (unpack_pair unpack_term unpack_thm)));
        #exn_raises st := (exn_raises |>
                            (unpack_list (unpack_pair unpack_term unpack_thm)));
        #exn_functions_defs st := (exn_functions_defs |>
                            (unpack_list (unpack_pair unpack_thm unpack_thm)));
        #default_H st := (default_H |> unpack_term);
        #H_def st := (H_def |> unpack_thm);
        #H st := (H |> unpack_term);
        #access_patterns st := (access_patterns |>
          (unpack_list (unpack_pair unpack_term unpack_thm)));
        #refs_functions_defs st :=
          (refs_functions_defs |>
            (unpack_list (unpack_pair unpack_thm unpack_thm)));
        #rarrays_functions_defs st :=
          (rarrays_functions_defs |>
            (unpack_list (unpack_6tuple unpack_thm unpack_thm unpack_thm
                                        unpack_thm unpack_thm unpack_thm)));
        #farrays_functions_defs st := (farrays_functions_defs |>
            (unpack_list (unpack_5tuple unpack_thm unpack_thm unpack_thm
                                        unpack_thm unpack_thm)));
        #store_pinv_def st := (store_pinv_def |> (unpack_option unpack_thm));
        #dynamic_refs_bindings st := (dynamic_refs_bindings |>
            (unpack_list (unpack_pair unpack_term unpack_term)));
        #local_code_abbrevs st :=
            (local_code_abbrevs |> (unpack_list unpack_thm));
        #mem_derive_case_ref st := (mem_derive_case_ref |>
            (unpack_list (unpack_pair unpack_type unpack_thm)))
      end
  | _ => failwith "Could not load translator state."
  );

  fun load_translator_state name = let
    val translator_state_thm = fetch name (name ^ suffix) |>
                               (PURE_ONCE_REWRITE_RULE [TAG_def])
    in unpack_translator_state translator_state_thm end;

  val finalised = ref false

in

  fun finalise_reset () = (finalised := false)

  fun finalise_translation () =
    if !finalised then () else (
      finalised := true;
      (let val _ = save_translator_state() in () end)
    );
      (* val _ = print_translation_output () *)(* TODO: Would this be useful? *)

  val _ = Theory.register_hook (
    "cakeML.ml_monad_translator",
    (fn TheoryDelta.ExportTheory _ => finalise_translation ()
      | _                          => ())
  );

  fun m_translation_extends name = (
    print ("Loading monadic translator state from: " ^ name ^ "... ");
    load_translator_state name;
    print "Done.\n";
    translation_extends name
  )

end (* end local *)

(******************************************************************************)
end (* end struct *)
