(*
  Automation that derives lemmas about arrays and references for use
  by the monadic translator.
*)
structure ml_monadStoreLib :> ml_monadStoreLib = struct

open preamble ml_translatorTheory ml_pmatchTheory patternMatchesTheory
open astTheory libTheory evaluateTheory semanticPrimitivesTheory
open evaluateTheory ml_progLib ml_progTheory
open packLib
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib
open cfHeapsBaseTheory
open ml_monadBaseTheory ml_monad_translatorBaseTheory ml_monad_translatorTheory ml_monadStoreTheory
open Redblackmap AC_Sort Satisfy
open ml_translatorLib

val filter = List.filter (* reverse masking by Redblackmap's filter *)

(* COPY/PASTE from other manual eval_rel proofs *)
fun derive_eval_thm for_eval v_name e = let
  val env = get_ml_prog_state () |> get_env
  val st = get_ml_prog_state () |> get_state
  val st2 = mk_var ("st2", type_of st)
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, e, st2, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal
    |> (NCONV 50 (SIMP_CONV (srw_ss()) [evaluate_def,ml_progTheory.eval_rel_alt,
            PULL_EXISTS,do_app_def,store_alloc_def,LET_THM]) THENC EVAL)
  val v_thm = prove(mk_imp(lemma |> concl |> rand,goal),
                    rpt strip_tac \\ rveq \\
                    match_mp_tac (#2(EQ_IMP_RULE lemma)) \\
                    simp_tac bool_ss [] \\
                    fs [state_component_equality])
                 |> GEN_ALL |> SIMP_RULE std_ss [GSYM PULL_EXISTS]
                            |> SIMP_RULE std_ss [PULL_EXISTS]
                            |> SIMP_RULE (srw_ss()) [PULL_EXISTS]
                            |> SPEC_ALL
  val v_tm = v_thm |> concl |> rand
  val v_def = define_abbrev for_eval v_name v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end
(* end of COPY/PASTE *)

fun ERR fname msg = mk_HOL_ERR "ml_monadStoreLib" fname msg;

local
  structure Parse = struct
    open Parse
     val (Type,Term) =
         parse_from_grammars ml_monadStoreTheory.ml_monadStore_grammars
  end
  open Parse
  (* Information about the subscript exceptions *)
  val Conv_Subscript = EVAL ``sub_exn_v`` |> concl |> rand
  (* val Stamp_Subscript = Conv_Subscript |> rator |> rand |> rand *)
in

(* Constants *)
val hprop_ty = “:hprop”
val v_ty = “:v”
val ffi_state_ty = “:'ffi semanticPrimitives$state”
val ffi_ffi_proj_ty = “:'ffi ffi_proj”
val lookup_ret_ty = “:num # stamp”

val TRUE = boolSyntax.T
val emp_const = “emp : hprop”
val APPEND_const = “APPEND : α list -> α list -> α list”
val CONS_const = “CONS : α -> α list -> α list”
val REF_const = “REF”
val RARRAY_const = “RARRAY”
val ARRAY_const = “ARRAY”
val SOME_const = “SOME”
val one_const = “1 : num”
val cond_const = “set_sep$cond”
val get_refs_const = “λ(state : 'a semanticPrimitives$state). state.refs”
val opref_expr = “λname. (App Opref [Var (Short name)])”
val empty_v_list = “[] : v list”
val empty_v_store = “[] : v store”
val empty_alpha_list = “[] : α list”
val nsLookup_env_short_term = “λ(env : v sem_env) name. nsLookup env.v (Short name)”
val Conv_Subscript = Conv_Subscript
end (* local *)

fun mk_get_refs state = let
    val ffi_ty = type_of state |> dest_type |> snd |> hd
    val get_refs = inst [alpha |-> ffi_ty] get_refs_const
    val get_refs = mk_comb(get_refs, state) |> BETA_CONV |> concl |> rand
in get_refs end



fun mk_REF_REL TYPE r x =
  ISPECL [TYPE, r, x] REF_REL_def |> concl |> dest_eq |> fst

fun mk_RARRAY_REL TYPE r x =
  ISPECL [TYPE, r, x] RARRAY_REL_def |> concl |> dest_eq |> fst

fun mk_ARRAY_REL TYPE r x =
  ISPECL [TYPE, r, x] ARRAY_REL_def |> concl |> dest_eq |> fst

fun mk_REFS_PRED H refs p s =
  ISPECL [H, p, refs, s] REFS_PRED_def |> concl |> dest_eq |> fst

fun mk_VALID_REFS_PRED H =
  ISPECL [H] VALID_REFS_PRED_def |> concl |> dest_eq |> fst

fun mk_lookup_eq name env type_tm = let
    val lookup_tm = ISPECL [name, env] lookup_cons_def |> concl |> dest_eq |> fst
    val some_tm = mk_comb (inst [alpha |-> lookup_ret_ty] SOME_const, mk_pair(one_const, type_tm))
in mk_eq(lookup_tm, some_tm) end

(******* COPY/PASTE from ml_monadProgScript.sml *****************************************)
(*********** Comes from cfLetAutoLib.sml ***********************************************)
(* [dest_pure_fact]
   Deconstruct a pure fact (a heap predicate of the form &P) *)
val set_sep_cond_tm = cond_const;
fun dest_pure_fact p =
  case (dest_term p) of
  COMB dp =>
    (if same_const set_sep_cond_tm (#1 dp) then (#2 dp)
    else raise (ERR "dest_pure_fact" "Not a pure fact"))
  | _ => raise (ERR "dest_pure_fact" "Not a pure fact");
(***************************************************************************************)

fun PURE_FACTS_FIRST_CONV H =
  let
    val preds = list_dest dest_star H
    val (pfl, hpl) = List.partition (can dest_pure_fact) preds
    val ordered_preds = pfl @ hpl
  in
    if List.null ordered_preds then REFL H
    else
      let
        val H' = List.foldl (fn (x, y) => mk_star(y, x)) (List.hd ordered_preds)
                   (List.tl ordered_preds)
        (* For some strange reason, AC_CONV doesn't work *)
        val H_to_norm = STAR_AC_CONV H
        val norm_to_H' = (SYM(STAR_AC_CONV H') handle UNCHANGED => REFL H')
      in TRANS H_to_norm norm_to_H' end
  end;

val EXTRACT_PURE_FACTS_CONV =
  (RATOR_CONV PURE_FACTS_FIRST_CONV)
  THENC (SIMP_CONV pure_ss [GSYM STAR_ASSOC])
  THENC (SIMP_CONV pure_ss [cfLetAutoTheory.HCOND_EXTRACT])
  THENC (SIMP_CONV pure_ss [STAR_ASSOC]);

val SEPARATE_SEP_EXISTS_CONV = ((SIMP_CONV pure_ss [GSYM STAR_ASSOC, SEP_EXISTS_INWARD]) THENC (SIMP_CONV pure_ss [STAR_ASSOC, SEP_EXISTS_SEPARATE]))

(* TODO: use EXTRACT_PURE_FACT_CONV to rewrite EXTRACT_PURE_FACTS_TAC *)
fun EXTRACT_PURE_FACTS_TAC (g as (asl, w)) =
  let
      fun is_hprop a = ((dest_comb a |> fst |> type_of) = hprop_ty handle HOL_ERR _ => false)
      val hpreds = List.filter is_hprop asl
      val hpreds' = List.map (fst o dest_comb) hpreds
      val hpreds_eqs = List.map (PURE_FACTS_FIRST_CONV) hpreds'
  in
      ((fs hpreds_eqs) >> fs[GSYM STAR_ASSOC] >> fs[cfLetAutoTheory.HCOND_EXTRACT] >> fs[STAR_ASSOC]) g
  end;
(***********************************************************************************************)
(******* End of COPY/PASTE from ml_monadProgScipt.sml *****************************************)

(* Normalize the heap predicate before using the get_heap_constant_thm theorem  *)
fun get_refs_manip_funs (l : (string * thm * thm * thm) list) =
  List.map (fn (x, _, y, z) => (x, y, z)) l;
fun get_rarrays_manip_funs (l : (string * thm * thm * thm * thm * thm * thm * thm) list) =
  List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) l;
fun get_farrays_manip_funs (l : (string * (int * thm) * thm * thm * thm * thm * thm) list) =
  List.map (fn (x1, _, x2, x3, x4, x5, x6) => (x1, x2, x3, x4, x5, x6)) l;

(*

val v_name = name
val value_def = def

*)

fun derive_eval_thm_ALLOCATE_EMPTY_ARRAY v_name value_def = let
    val env = get_env(get_ml_prog_state())
    val s = get_state(get_ml_prog_state())

    val array_v_name = find_const_name (v_name ^ "_v")
    val array_loc_name = find_const_name (v_name ^ "_loc")
    (* val ref_v_name = find_const_name (v_name ^ "_ref_v") *)
    val ref_name = find_const_name (v_name ^ "_ref")

    (* Provisional *)
    val array_v_def = define_abbrev false array_v_name empty_v_list
    val ri = get_type_inv (concl value_def |> rhs |> type_of |> dest_type |> snd |> List.hd)
    val array_v_thm = Q.prove(`LIST_REL ^ri [] []`, rw[])
    val array_v_thm = SIMP_RULE pure_ss [GSYM value_def, GSYM array_v_def] array_v_thm
    (***)

    (* Expand the definitions *)
    val th = SPECL [env, s] ALLOCATE_EMPTY_RARRAY_evaluate
    val th = SIMP_RULE pure_ss [GSYM array_v_def] th
    val res_pair = rand(concl th)
    val res_pair_eq = EVAL res_pair
    val res_pair2 = rand(rator(concl th))
    val res_pair2_eq = EVAL res_pair2
    val th = SIMP_RULE pure_ss [res_pair_eq,res_pair2_eq] th

    (* Abbreviate the array location *)
    val array_loc = concl th |> rator |> rand |> rand |> rator
                    |> rand |> rand |> rand |> listSyntax.dest_cons |> fst
    val array_loc_def = define_abbrev false array_loc_name array_loc
    val th = PURE_REWRITE_RULE [GSYM array_loc_def] th

    (* Abbreviate the reference location *)
    val res = concl th |> rand
    val ref_var = mk_var(ref_name, v_ty)
    val ref_def = Define `^ref_var = ^res`
    val th = SIMP_RULE pure_ss [GSYM ref_def] th
in (array_v_thm, array_loc_def, ref_def, th) end;

fun derive_eval_thm_ALLOCATE_ARRAY name n init_value_def = let
    val init_value_name = concl init_value_def |> lhs |> dest_const |> fst
    val _ = (next_ml_names := init_value_name::(!next_ml_names))
    val init_value_v_thm = translate init_value_def

    val env = get_env(get_ml_prog_state())
    val s = get_state(get_ml_prog_state())

    val lookup_assum = list_mk_comb(nsLookup_env_short_term, [env, stringSyntax.fromMLstring init_value_name]) |> ((RATOR_CONV BETA_CONV) THENC BETA_CONV) |> concl |> rhs
    val lookup_assum = EVAL lookup_assum

    val th = ISPECL [env, s, numSyntax.term_of_int n] ALLOCATE_ARRAY_evaluate |> SPEC_ALL
    val th = MATCH_MP th lookup_assum

    (* Abbreviate the constants and simplify the theorem *)
    val th = CONV_RULE (RAND_CONV computeLib.EVAL_CONV) th
    val array_v = concl th |> rator |> rand |> rator |> rand |> rand |> rand
                           |> listSyntax.dest_cons |> fst |> rand
    val array_v_name = find_const_name (name ^ "_v")
    val array_v_def = define_abbrev false array_v_name array_v
    val th = SIMP_RULE pure_ss [GSYM array_v_def] th

    val array_loc = concl th |> rand
    val array_loc_name = find_const_name (name ^ "_loc")
    val array_loc_def = define_abbrev false array_loc_name array_loc
    val th = SIMP_RULE pure_ss [GSYM array_loc_def] th

    (* Define init_array *)
    val init_name = find_const_name ("init_" ^ name)
    val init_v_th = MATCH_MP (SPEC (numSyntax.term_of_int n) LIST_REL_REPLICATE) init_value_v_thm
    val init_array = concl init_v_th |> rator |> rand
    val array_abbrev = define_abbrev false init_name init_array
    val init_v_th = PURE_REWRITE_RULE
                      [GSYM array_abbrev, GSYM array_v_def] init_v_th
    val _ = save_thm (init_name ^"_v_thm", init_v_th)
    val _ = print ("Saved theorem: " ^init_name ^"_v_thm")
in (init_v_th, array_loc_def, th) end;

fun get_store_pinv_def_opt opt = Option.map fst opt;

(* Create the store for a static initialization *)
fun create_store refs_init_list rarrays_init_list farrays_init_list =
  let
      val initial_state = get_state(get_ml_prog_state())
      val initial_store = EVAL (mk_get_refs initial_state) |> concl |> rhs
      fun mk_opref_expr name =
        mk_comb(opref_expr, name) |> BETA_CONV |> concl |> rand
      (* Allocate the references *)
      fun create_ref (name, def) =
        let
          val value_def = translate def
          val init_name = concl def |> dest_eq |> fst |> dest_const |> fst
          val init_name = stringLib.fromMLstring init_name
          val e = mk_opref_expr init_name
          val eval_thm = REWRITE_RULE [ML_code_env_def]
                                      (derive_eval_thm false name e)
          val _ = ml_prog_update (add_Dlet eval_thm name)
          val ref_def = DB.fetch (current_theory()) (name ^ "_def")
        in
          (value_def, ref_def)
        end
      val ref_name_def_pairs = List.map (fn (n, d, _, _) => (n, d)) refs_init_list
      val refs_trans_results = List.map create_ref ref_name_def_pairs

      (* Allocate the resizable arrays *)
      fun create_rarray (name, def) =
        let
          val init_name = concl def |> lhs |> dest_const |> fst

          val (array_v_def, array_loc_def, ref_def, eval_th) =
            derive_eval_thm_ALLOCATE_EMPTY_ARRAY init_name def
          val _ = ml_prog_update(add_Dlet eval_th name)
        in
          (array_v_def, array_loc_def, ref_def)
        end

      val rarray_name_def_pairs = List.map (fn (n, d, _, _, _, _, _, _) => (n, d)) rarrays_init_list
      val rarrays_trans_results = List.map create_rarray rarray_name_def_pairs

      (* Allocate the fixed size arrays *)
      fun create_farray (name, (n, def)) =
        let
          val (array_v_def, array_loc_def, eval_th) = derive_eval_thm_ALLOCATE_ARRAY name n def
          val _ = ml_prog_update (add_Dlet eval_th name)
        in
          (array_v_def, array_loc_def)
        end

      val farray_name_def_pairs = List.map (fn (n, d, _, _, _, _, _) => (n, d)) farrays_init_list
      val farrays_trans_results = List.map create_farray farray_name_def_pairs

  in
    (initial_store, refs_trans_results, rarrays_trans_results, farrays_trans_results)
  end;

fun find_refs_access_functions refs_init_list =
  let
    fun find_refs_read (name, get_fun, set_fun) =
      let
        val (state, pair) = concl get_fun |> dest_eq |> snd |> dest_abs
        val body = dest_pair pair |> fst |> rand
        val refs_read = mk_abs(state, body)
      in refs_read end

    fun find_refs_write (name, get_fun, set_fun) =
      let
        val (x, body) = concl set_fun |> dest_forall
        val (state, pair) = dest_eq body |> snd |> dest_abs
        val body = dest_pair pair |> snd
        val refs_write = mk_abs(x, mk_abs(state, body))
      in refs_write end

    fun find_read_write (name, get_fun, set_fun) =
      let
        val refs_read = find_refs_read(name, get_fun, set_fun)
        val refs_write = find_refs_write(name, get_fun, set_fun)
      in (name, get_fun, refs_read, set_fun, refs_write) end
  in List.map find_read_write refs_init_list end;

fun find_rarrays_access_functions arrays_init_list =
  let
    fun find_read_write (name, get, set, length, sub, update, alloc) =
      let
        val state = concl get |> rhs |> dest_abs |> fst
        val get_fun = concl get |> rhs |> dest_abs |> snd |> dest_pair |> fst |> rand
        val get_fun = mk_abs(state, get_fun)

        val x = concl set |> dest_forall |> fst
        val set_fun = concl set |> strip_forall |> snd |> rhs
        val state = dest_abs set_fun |> fst
        val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
        val set_fun = mk_abs(x, mk_abs(state, set_fun))
      in (get_fun, set_fun) end

    fun find_add_read_write (name, get, set, length, sub, update, alloc) =
      let
        val (get_fun, set_fun) = find_read_write (name, get, set, length, sub, update, alloc)
      in (name, get, get_fun, set, set_fun, length, sub, update, alloc) end
  in List.map find_add_read_write arrays_init_list end;

fun find_farrays_access_functions arrays_init_list = let
    fun find_read_write (name, get, set, length, sub, update) =
      let
        val state = concl get |> rhs |> dest_abs |> fst
        val get_fun = concl get |> rhs |> dest_abs |> snd |> dest_pair |> fst |> rand
        val get_fun = mk_abs(state, get_fun)

        val x = concl set |> dest_forall |> fst
        val set_fun = concl set |> strip_forall |> snd |> rhs
        val state = dest_abs set_fun |> fst
        val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
        val set_fun = mk_abs(x, mk_abs(state, set_fun))
      in (get_fun, set_fun) end

    fun find_add_read_write (name, get, set, length, sub, update) =
      let
        val (get_fun, set_fun) = find_read_write (name, get, set, length, sub, update)
      in (name, get, get_fun, set, set_fun, length, sub, update) end
  in List.map find_add_read_write arrays_init_list end;

fun create_store_X_hprop refs_manip_list
                         refs_locs
                         rarrays_manip_list
                         rarrays_refs_locs
                         farrays_manip_list
                         farrays_locs
                         state_type
                         store_hprop_name
                         store_pinv_def_opt
                         extra_hprop =
  let
    val state_var = mk_var("state", state_type)
    (* Create the heap predicate for the store *)
    (* REFS *)
    val create_ref_hprop_params = List.map (fn (x, _, y, _, _) => (x, y)) refs_manip_list
    val create_ref_hprop_params = zip create_ref_hprop_params refs_locs
    (* val ((name, get_f), ref_loc) = List.hd create_ref_hprop_params *)
    fun create_ref_hprop ((name, get_f), ref_loc) =
      let
        val ty = dest_abs get_f |> snd |> type_of
        val ref_inv = (get_type_inv ty
                       handle HOL_ERR _ => (register_type ty; get_type_inv ty))
        val get_term = mk_comb (get_f, state_var) |> BETA_CONV |> concl |> dest_eq |> snd

        val hprop = mk_REF_REL ref_inv ref_loc get_term
      in
        hprop
      end
    val refs_hprops = List.map create_ref_hprop create_ref_hprop_params

    (* RARRAYS *)
    val create_rarray_hprop_params =
        List.map (fn (x, _, y, _, _, _, _, _, _) => (x, y)) rarrays_manip_list
    val create_rarray_hprop_params = zip create_rarray_hprop_params rarrays_refs_locs
    (*
      val ((name, get_f), rarray_ref_loc) = hd create_rarray_hprop_params
    *)
    fun create_rarray_hprop ((name, get_f), rarray_ref_loc) =
      let
        val ref_inv = dest_abs get_f |> snd |> type_of |> dest_type |> snd |>
                      List.hd |> get_type_inv
        val ty_subst = match_type (type_of state_var)
                                  (type_of get_f |> dom_rng |> fst)
        val get_term = mk_comb (get_f, Term.inst ty_subst state_var) |>
                       BETA_CONV |> concl |> dest_eq |> snd

        val hprop =
          list_mk_ucomb(``RARRAY_REL``, [ref_inv, rarray_ref_loc, get_term])
      in
        hprop
      end
    val rarrays_hprops = List.map create_rarray_hprop create_rarray_hprop_params

    (* ARRAYS *)
    val create_farray_hprop_params =
        List.map (fn (x, _, y, _, _, _, _, _) => (x, y)) farrays_manip_list
    val create_farray_hprop_params = zip create_farray_hprop_params farrays_locs
    (*
      val ((name, get_f), farray_loc) = hd create_farray_hprop_params
    *)
    fun create_farray_hprop ((name, get_f), farray_loc) =
      let
        val ref_inv = dest_abs get_f |> snd |> type_of |> dest_type |> snd |>
                      List.hd |> get_type_inv
        val ty_subst = match_type (type_of state_var)
                                  (type_of get_f |> dom_rng |> fst)
        val get_term = mk_comb (get_f, Term.inst ty_subst state_var) |>
                       BETA_CONV |> concl |> dest_eq |> snd

        val hprop = list_mk_ucomb(``ARRAY_REL``, [ref_inv, farray_loc, get_term])
      in
        hprop
      end
    val farrays_hprops = List.map create_farray_hprop create_farray_hprop_params

    (* extra hprops e.g. for I/O *)
    val extra_hprops =
      case extra_hprop of NONE => [] | SOME x =>
        let
          val vs = free_vars x
          val _ = length vs = 1 orelse failwith "malformed extra_hprop: must have only one free variable"
        in list_dest dest_star (subst [hd vs |-> state_var] x) end
        handle Empty => []

    (* Conjunct the heap predicates *)
    val store_hprop = list_mk mk_star (refs_hprops @ rarrays_hprops @ farrays_hprops @ extra_hprops) emp_const
    val store_hprop = SIMP_CONV bool_ss [STAR_ASSOC] store_hprop |> concl |> dest_eq |> snd
                      handle UNCHANGED => store_hprop
    val store_hprop = case store_pinv_def_opt of
                        SOME pinv_def =>
                        mk_star(store_hprop,
                                mk_cond(mk_comb( (concl pinv_def |> lhs) , state_var)))
                      | NONE => store_hprop

    val store_hprop_state_vars = free_vars store_hprop |>
                                (filter (fn t => fst (dest_var t) = "state"))
    val store_hprop_state_var = (
      case store_hprop_state_vars of
          [] => state_var
        | (x::_) => x)

    val store_hprop = mk_abs(store_hprop_state_var, store_hprop)

    (* Create the constant for the store predicate *)
    val loc_vars = List.filter is_var (refs_locs @ rarrays_refs_locs @ farrays_locs)
    val num_vars = List.length loc_vars

    val store_hprop_type = (type_of store_hprop_state_var) --> hprop_ty

    fun mk_hprop_type n t = if n = 0 then t else mk_type("fun", [v_ty, mk_hprop_type (n-1) t])
    val store_hprop_type = mk_hprop_type num_vars store_hprop_type

    val free_type_vars = type_vars store_hprop_type
    val tyvars_ref_invs = List.map get_type_inv free_type_vars

    fun mk_fun_type [] ret_ty = ret_ty
      | mk_fun_type (ty::tys) ret_ty =
          ty --> (mk_fun_type tys ret_ty)
    val store_hprop_type =
      mk_fun_type (List.map type_of tyvars_ref_invs) store_hprop_type

    (*
    val store_hprop_type = mk_type("fun", [``:'a -> v -> bool``, store_hprop_type])
    *)
    val store_hprop_var = mk_var(store_hprop_name, store_hprop_type)
    (*
    val store_hprop_var = mk_comb(store_hprop_var, ``a : 'a -> v -> bool``)
    *)
    val store_hprop_var = list_mk_comb(store_hprop_var, tyvars_ref_invs)
    val store_hprop_pred = list_mk_comb (store_hprop_var, loc_vars)
    val store_eq = mk_eq(store_hprop_pred, store_hprop)
    val store_hprop_def = Define `^store_eq`
in
    store_hprop_def
end;

(* Prove that the current store satisfies the built heap predicate *)
local
    fun instantiate_ref_values refs_trans_results
                               rarrays_trans_results
                               farrays_trans_results
                               (g as (asl, w)) =
      let
        val (ref_vars, prop) = strip_exists w
        val props = list_dest dest_conj prop
        val props = List.take (props, List.length props -1)
        val ref_consts_pairs = mapfilter (fn x => (rand x, (rand o rator) x)) props
        val ref_consts_map = Redblackmap.insertList
              (Redblackmap.mkDict Term.compare, ref_consts_pairs)
        val trans_RIs = (List.map fst refs_trans_results) @
                        (List.map (fn (x, _, _) => x) rarrays_trans_results) @
                        (List.map fst farrays_trans_results)
        val value_pairs = List.map (fn ref_v => ((rand o rator o concl) ref_v,
              (rand o concl) ref_v)) trans_RIs
        val value_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, value_pairs)

        val init_vars = List.map (fn x => Redblackmap.find (ref_consts_map, x)) ref_vars
        val instants = List.map (fn x => Redblackmap.find (value_map, x)) init_vars
        val tac = List.foldl (fn (x, tac) => tac THEN (EXISTS_TAC x)) ALL_TAC instants
      in
        tac g
      end

    fun eliminate_PINV store_pinv_info_opt =
      case store_pinv_info_opt of
        SOME (refs_init_list, rarrays_init_list, farrays_init_list, (_, th)) =>
          let
            val th = PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] th
            val init_values = List.map (fn (_, x, _, _) => x) refs_init_list
          in CONJ_TAC >-(fs init_values >> IMP_RES_TAC th >> fs[]) end
      | NONE => ALL_TAC

    fun eliminate_inherited_store_rec remaining_store =
      if same_const remaining_store empty_alpha_list then ALL_TAC
      else
        let
          fun decompose_store remaining_store =
            let
              val (binder, remaining_store') = dest_comb remaining_store
              val (binder, e) = dest_comb binder
            in (binder, remaining_store') end
            handle HOL_ERR _ => (APPEND_const, empty_v_store)

          val (binder, remaining_store') = decompose_store remaining_store
        in
          (*if same_const binder CONS_const then*)
            (*(irule eliminate_store_elem_thm) \\ (eliminate_inherited_store_rec remaining_store')*)
          (*else*)
            (*(irule eliminate_substore_thm) \\ (eliminate_inherited_store_rec remaining_store')*)
          (irule eliminate_store_elem_thm ORELSE irule eliminate_substore_thm)
          \\ eliminate_inherited_store_rec remaining_store'
        end

     (*
       val remaining_store = remaining_store'
     *)

     fun eliminate_inherited_store initial_store = let
       val remaining_store = QCONV(PURE_REWRITE_CONV[GSYM APPEND_ASSOC]) initial_store |> concl |> rhs
     in
       PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
       \\ eliminate_inherited_store_rec remaining_store
       \\ PURE_REWRITE_TAC [APPEND_ASSOC]
     end

     fun check_ref (g as (asl, w)) =
       let
         val hprop = PURE_REWRITE_CONV [GSYM STAR_ASSOC] w
                     |> concl |> rhs |> rator |> rator |> rand
       in
         if same_const REF_const (strip_comb hprop |> fst) then ALL_TAC g
         else FAIL_TAC "Not a ref" g
       end
       handle UNCHANGED => FAIL_TAC "Not a ref" g

     fun check_rarray (g as (asl, w)) =
       let
         val hprop = PURE_REWRITE_CONV [GSYM STAR_ASSOC] w
                     |> concl |> rhs |> rator |> rator |> rand
       in
         if same_const RARRAY_const (strip_comb hprop |> fst) then ALL_TAC g
         else FAIL_TAC "Not a resizable array" g
       end
       handle UNCHANGED => FAIL_TAC "Not a resizable array" g

     fun check_farray (g as (asl, w)) =
       let
         val hprop = PURE_REWRITE_CONV [GSYM STAR_ASSOC] w
                     |> concl |> rhs |> rator |> rator |> rand
       in
         if same_const ARRAY_const (strip_comb hprop |> fst) then ALL_TAC g
         else FAIL_TAC "Not a fixed-size array" g
       end
       handle UNCHANGED => FAIL_TAC "Not a fixed-size array" g
in
  fun prove_valid_store_X_hprop save_th
                                refs_manip_list
                                rarrays_manip_list
                                farrays_manip_list
                                refs_trans_results
                                rarrays_trans_results
                                farrays_trans_results
                                initial_store
                                current_state
                                state_type
                                store_X_hprop_def
                                store_pinv_info_opt =
    let
      val store_hprop_const = concl store_X_hprop_def |> dest_eq |> fst
      val current_store = mk_get_refs current_state
      val store_eval_thm = EVAL current_store

      val refs_get_funs = List.map (fn (_, _, x, _, _) => x) refs_manip_list
      val refs_init_values = List.map (fn (x, _) => concl x |> rator |> rand) refs_trans_results

      val rarrays_get_funs = List.map (fn (_, _, x, _, _, _, _, _, _) => x) rarrays_manip_list
      val rarrays_init_values = List.map (fn (x, _, _) => concl x |> rator |> rand)
                                         rarrays_trans_results

      val farrays_get_funs = List.map (fn (_, _, x, _, _, _, _, _) => x) farrays_manip_list
      val farrays_init_values = List.map (fn (x, _) => concl x |> rator |> rand)
                                         farrays_trans_results

      val state_var = mk_var("state", state_type)
      fun mk_get_eq (f, v) =
        let
          val c = mk_comb(f, state_var)
          val c = (BETA_CONV c |> concl |> rhs handle HOL_ERR _ => c)
          val eq = mk_eq(c, v)
        in eq end
      val hyps = List.map mk_get_eq ((zip refs_get_funs refs_init_values)
                                    @ (zip rarrays_get_funs rarrays_init_values)
                                    @ (zip farrays_get_funs farrays_init_values))
      val hyps = list_mk_conj hyps handle HOL_ERR _ => TRUE

      val tys = match_type (type_of current_state) ffi_state_ty
      val current_state = Term.inst tys current_state

      val p_var = mk_var("p", ffi_ffi_proj_ty);
      val goal = mk_REFS_PRED store_hprop_const state_var p_var current_state
      val goal = list_mk_forall([state_var, p_var], mk_imp(hyps, goal))
      (* set_goal ([], goal) *)

      val solve_first_ref_subheap_tac =
        check_ref
        \\ CONV_TAC ((RAND_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV[append_empty]))
        \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
        \\ irule eliminate_substore_thm
        \\ TRY(irule store2heap_aux_decompose_store1 \\ rpt conj_tac)
        >-(
          REPEAT (irule H_STAR_GC_SAT_IMP)
          \\ PURE_REWRITE_TAC (List.map snd refs_trans_results)
          \\ SIMP_TAC list_ss [store2heap_REF_SAT, SUC_ONE_ADD])

      val solve_first_rarray_subheap_tac =
        check_rarray
        \\ PURE_REWRITE_TAC[APPEND]
        \\ PURE_ONCE_REWRITE_TAC[cons_to_append]
        \\ TRY(irule store2heap_aux_decompose_store1 \\ rpt conj_tac)
        >-(
          REPEAT (irule H_STAR_GC_SAT_IMP)
          \\ PURE_REWRITE_TAC
            (List.concat(List.map (fn (_, x, y) => [x, y])
                                   rarrays_trans_results))
          \\ irule rarray_exact_thm
          \\ SIMP_TAC list_ss [])

      val solve_first_farray_subheap_tac =
        check_farray
        \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
        \\ irule eliminate_substore_thm
        \\ TRY(irule store2heap_aux_decompose_store2 \\ rpt conj_tac)
        >-(
          REPEAT (irule H_STAR_GC_SAT_IMP)
          \\ PURE_REWRITE_TAC (List.concat(List.map (fn (_, x) => [x])
                               farrays_trans_results))
          \\ irule farray_exact_thm
          \\ SIMP_TAC list_ss [])

      val solve_tac =
        ntac 3 STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [REFS_PRED_def, REF_REL_def, RARRAY_REL_def, ARRAY_REL_def, store_X_hprop_def]
        \\ PURE_REWRITE_TAC[EMP_STAR_GC, SAT_GC] (* In case the store is empty *)
        \\ SIMP_TAC bool_ss [SEP_CLAUSES, SEP_EXISTS_THM]
        \\ (CONV_TAC o STRIP_QUANT_CONV) EXTRACT_PURE_FACTS_CONV
        \\ instantiate_ref_values refs_trans_results rarrays_trans_results farrays_trans_results
        \\ SIMP_TAC (bool_ss) ((List.map fst refs_trans_results) @
                              (List.map (fn (x, _, _) => x) rarrays_trans_results) @
                              (List.map fst farrays_trans_results))
        \\ eliminate_PINV store_pinv_info_opt
        \\ SIMP_TAC pure_ss [GSYM STAR_ASSOC]
        \\ PURE_REWRITE_TAC[Once GC_DUPLICATE_0]
        \\ ntac (List.length refs_trans_results + List.length rarrays_trans_results + List.length farrays_trans_results- 1)
          (ONCE_REWRITE_TAC [GC_DUPLICATE_1])
        \\ PURE_REWRITE_TAC[Once GC_DUPLICATE_3]
        \\ irule store2heap_eliminate_ffi_thm
        \\ PURE_REWRITE_TAC [store2heap_def, store_eval_thm]
        \\ eliminate_inherited_store initial_store
        \\ SIMP_TAC list_ss []
        \\ ntac (List.length refs_trans_results) solve_first_ref_subheap_tac
        \\ ntac (List.length rarrays_trans_results) solve_first_rarray_subheap_tac
        \\ ntac (List.length farrays_trans_results) solve_first_farray_subheap_tac
        \\ PURE_REWRITE_TAC[SAT_GC]

      val store_X_hprop_thm = prove(goal, solve_tac)
      val store_X_hprop_thm = PURE_REWRITE_RULE[ConseqConvTheory.IMP_CLAUSES_TX] store_X_hprop_thm

      val thm_name = "INIT_" ^(dest_const store_hprop_const |> fst)
      val store_X_hprop_thm =
        if save_th then save_thm(thm_name, store_X_hprop_thm)
        else store_X_hprop_thm
      val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in
      store_X_hprop_thm
    end
end;

(* Prove the validity theorem for the characteristic heap predicate *)
fun prove_exists_store_X_hprop save_th
                               state_type
                               store_hprop_name
                               valid_store_X_hprop_thm =
  let
    val store_hprop_const = mk_const(store_hprop_name, mk_type("fun", [state_type, hprop_ty]))
    val current_state = get_state(get_ml_prog_state())
    val ty_subst = Type.match_type (type_of current_state) ffi_state_ty
    val current_state = Term.inst ty_subst current_state

    val (vars, hyps) = concl valid_store_X_hprop_thm |> strip_forall

    val (refs_var, ffi_var) = if List.length vars = 2
                              then (hd vars, hd(tl vars))
                              else failwith "prove_exists_store_X_hprop"
    val hyps = dest_imp hyps |> fst handle HOL_ERR _ => TRUE
    val interm_goal = list_mk_exists([refs_var, ffi_var], hyps)
    val interm_solve_tac =  srw_tac[QI_ss][]
    val interm_th = prove(interm_goal, interm_solve_tac)
    (* set_goal([], interm_goal) *)

    val p_var = mk_var("p", ffi_ffi_proj_ty);
    val H_pair = mk_pair (store_hprop_const, p_var)
    val goal = mk_VALID_REFS_PRED H_pair

    (* set_goal([], goal) *)
    val solve_tac =
        PURE_REWRITE_TAC[VALID_REFS_PRED_def]
        \\ STRIP_ASSUME_TAC interm_th
        \\ FIRST[CHANGED_TAC(IMP_RES_TAC valid_store_X_hprop_thm),
                 ASSUME_TAC valid_store_X_hprop_thm] (* if hyps = TRUE *)
        \\ metis_tac[]

    val thm_name = store_hprop_name ^"_EXISTS"
    val exists_store_X_hprop_thm = if save_th then store_thm(thm_name, goal, solve_tac)
                                   else prove(goal, solve_tac)
    val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
in
    exists_store_X_hprop_thm
end;

(* Prove the specifications for the get/set functions *)

local

    fun pick_ref_order loc (t1, t2) = let
        val get_loc = (rand o rator)
        val is_loc1 = can get_loc t1
        val is_loc2 = can get_loc t2
      in if is_loc1 andalso not is_loc2 then LESS
        else if is_loc2 andalso not is_loc1 then GREATER
        else if is_loc1 andalso is_loc2 then
            (if loc ~~ (get_loc t1) then LESS else GREATER)
        else Term.compare(t1, t2)
      end
    fun PICK_REF_CONV loc = AC_Sort.sort{assoc = STAR_ASSOC, comm = STAR_COMM, dest = dest_star, mk = mk_star, cmp = pick_ref_order loc, combine = ALL_CONV, preprocess = ALL_CONV}
    fun pick_pinv_order field_pat (t1, t2) = let
        val is_cond1 = is_cond t1
        val is_cond2 = is_cond t2
        val has_pat = patternMatchesSyntax.has_subterm (aconv field_pat)
      in if is_cond1 andalso has_pat t1 then LESS
         else if is_cond2 andalso has_pat t2 then GREATER
         else Term.compare(t1, t2)
      end
    fun PICK_PINV_CONV field_pat = AC_Sort.sort{assoc = STAR_ASSOC, comm = STAR_COMM, dest = dest_star, mk = mk_star, cmp = pick_pinv_order field_pat, combine = ALL_CONV, preprocess = ALL_CONV}

    fun remove_assumption th = let
        val assum = concl th |> dest_imp |> fst
        val lemma = SIMP_CONV (srw_ss()) [] assum |> EQT_ELIM
    in MP th lemma end

in

fun prove_store_access_specs refs_manip_list
                             rarrays_manip_list
                             farrays_manip_list
                             refs_locs_defs
                             rarrays_refs_locs_defs
                             farrays_locs_defs
                             store_X_hprop_def
                             state_type
                             exn_ri_def
                             store_pinv_def_opt
                             extra_hprop = let
    val exn_ri = CONJUNCTS exn_ri_def |> List.hd |> concl |> strip_forall |> snd
                           |> lhs |> rator |> rator
    val store_pred = concl store_X_hprop_def |> strip_forall |> snd |> dest_eq |> fst
    val exc_type = type_of exn_ri |> dest_type |> snd |> List.hd
    val exc_type_aq = ty_antiq exc_type
    val state_type_aq = ty_antiq state_type
    (*
      val state_type_aq = ty_antiq ``:'a state_refs``
    *)
    val intro_hprop = REWRITE_RULE [GSYM store_X_hprop_def, SEP_CLAUSES]

    fun prove_ref_specs ((name, get_fun_def, read_fun, set_fun_def, write_fun),
                        loc_def) = let
        val name_v = stringLib.fromMLstring name
        val loc = concl loc_def |> lhs
        val TYPE = dest_abs read_fun |> snd |> type_of |> get_type_inv
        val EXN_TYPE = exn_ri
        val get_var = read_fun
        val set_var = write_fun

        (* Decompose the heap invariant *)
        val compos_conv = (PURE_REWRITE_CONV[store_X_hprop_def])
                              THENC (ABS_CONV (PICK_REF_CONV loc))
                              THENC (PURE_REWRITE_CONV[GSYM STAR_ASSOC])

        val H_eq = compos_conv store_pred
        val (state_var, H_part) = concl H_eq |> rhs |> dest_abs
        val H_part = if List.length refs_manip_list + List.length rarrays_manip_list + List.length farrays_manip_list > 1 orelse isSome extra_hprop then
                         mk_abs(state_var, rand H_part)
                     else mk_abs(state_var, emp_const)

        (* If there is a pure heap invariant provided *)
        val (PINV, H_part2) =
            case store_pinv_def_opt of
                SOME store_pinv_def => let
                 val (H_part2, PINV) = (QCONV (PURE_REWRITE_CONV[STAR_ASSOC]) H_part)
                                           |> concl |> rhs |> dest_abs |> snd |> dest_star
                 val H_part2 = mk_abs(state_var, H_part2)
                 val PINV = rand PINV |> rator
             in (PINV, H_part2) end
              | NONE => (mk_abs(state_var, TRUE), H_part)

        fun rewrite_thm th =
          let
            val th = PURE_ONCE_REWRITE_RULE[GSYM loc_def] th
            val th = PURE_REWRITE_RULE[GSYM get_fun_def, GSYM set_fun_def, GSYM STAR_ASSOC] th
            val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
            val th = PURE_REWRITE_RULE[H_STAR_empty, H_STAR_TRUE, GSYM H_eq] th
            val th = PURE_REWRITE_RULE[GSYM get_fun_def, GSYM set_fun_def] th
            val th = PURE_REWRITE_RULE[GSYM H_eq] th
            val th = PURE_REWRITE_RULE[GSYM get_fun_def, GSYM set_fun_def] th
            val th = PURE_REWRITE_RULE[PRECONDITION_T, ConseqConvTheory.IMP_CLAUSES_TX] th
            val hprop = th |> SPEC_ALL |> UNDISCH_ALL
                           |> concl |> rand |> dest_pair |> fst
            val hprop_target = H_eq |> concl |> dest_eq |> fst
            val _ = aconv hprop hprop_target orelse
                    failwith "rewrite_thm in prove_ref_specs"
          in th end

        (* read *)
        val read_spec = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_var] EvalM_read_heap
        val read_spec = rewrite_thm read_spec

        val thm_name = "get_" ^name ^"_thm"
        val _ = save_thm(thm_name, read_spec)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* write *)
        val write_spec = ISPECL[name_v, loc, TYPE, PINV, EXN_TYPE, H_part2, get_var, set_var] EvalM_write_heap
        val write_spec = rewrite_thm write_spec
        val update_conditions = concl write_spec |> strip_forall |> snd |> strip_imp |> fst
        val rw_thms = case store_pinv_def_opt of
                              SOME store_pinv_def => [store_pinv_def]
                            | NONE => []
        val update_conditions = List.take(update_conditions, 2) |> List.map (SIMP_CONV (srw_ss()) rw_thms)
        val write_spec = SIMP_RULE bool_ss update_conditions write_spec

        val thm_name = "set_" ^name ^"_thm"
        val _ = save_thm(thm_name, write_spec)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in (intro_hprop read_spec, intro_hprop write_spec) end

    val refs_access_thms = List.map prove_ref_specs (zip refs_manip_list refs_locs_defs)
    (*
    val ((name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def,
          update_def, alloc_def), loc_def) =
            zip rarrays_manip_list rarrays_refs_locs_defs |> hd
    *)
    (* Resizable arrays *)
    fun prove_rarray_specs ((name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def, update_def, alloc_def), loc_def) = let
        val name_v = stringLib.fromMLstring name
        val loc = concl loc_def |> lhs
        val TYPE =  get_fun |> dest_abs |> snd |> type_of |> dest_type |> snd |> List.hd |> get_type_inv
        val EXN_TYPE = exn_ri
        val get_arr = get_fun
        val set_arr = set_fun
        val sub_exn = concl sub_def |> rhs |> rand
        val update_exn = concl update_def |> rhs |> rand
        val Eval_sub_rexp = hol2deep sub_exn
        val sub_rexp = concl Eval_sub_rexp |> rator |> rand
        val Eval_update_rexp = hol2deep update_exn
        val update_rexp = concl Eval_update_rexp |> rator |> rand

        val compos_conv = (PURE_REWRITE_CONV[store_X_hprop_def])
                              THENC (ABS_CONV (PICK_REF_CONV loc))
                              THENC (PURE_REWRITE_CONV[GSYM STAR_ASSOC])

        val H_eq = compos_conv store_pred
        val (state_var, H_part) = concl H_eq |> rhs |> dest_abs
        val H_part = if List.length refs_manip_list + List.length rarrays_manip_list + List.length farrays_manip_list > 1 then
                         mk_abs(state_var, rand H_part)
                     else mk_abs(state_var, emp_const)

        fun rewrite_thm th = let
            val th = PURE_ONCE_REWRITE_RULE[GSYM loc_def] th
            val th = PURE_REWRITE_RULE[GSYM length_def, GSYM sub_def, GSYM update_def, GSYM alloc_def] th
            val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
            val th = PURE_REWRITE_RULE[GSYM H_eq] th
        in th end

        (* length *)
        val length_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr] EvalM_R_Marray_length
        val length_thm = rewrite_thm length_thm

        val thm_name = name ^"_length_thm"
        val _ = save_thm(thm_name, length_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* sub *)
        (* Test if the sub exception is linked to the CakeML subscript
           exception by the exception refinement invariant *)
        val EXN_TYPE_e_Subscript =
            list_mk_comb(EXN_TYPE,[sub_exn,Conv_Subscript])
        val (subscript_eval, usesSubscript) = let
            val eval_th = EVAL EXN_TYPE_e_Subscript
            val eval_th = EQT_ELIM eval_th
        in (eval_th, true) end
        handle HOL_ERR _ => (TRUTH, false)

        val sub_thm =
          if usesSubscript then let
            val th = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,sub_exn]
                            EvalM_R_Marray_sub_subscript |> SPEC_ALL
            val th = MP th subscript_eval |> UNDISCH |> UNDISCH |> rewrite_thm
          in th end
          else let
            val th = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,sub_exn,sub_rexp]
                            EvalM_R_Marray_sub_handle |> SPEC_ALL
            val th = rewrite_thm th |> UNDISCH |> UNDISCH |> UNDISCH
            val th = MP th Eval_sub_rexp
          in th end

        val thm_name = name ^"_sub_thm"
        val _ = save_thm(thm_name, sub_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* update *)
        (* Test if the update exception is linked to the CakeML subscript
           exception by the exception refinement invariant *)
        val EXN_TYPE_e_Subscript =
            list_mk_comb(EXN_TYPE,[update_exn,Conv_Subscript])
        val (subscript_eval, usesSubscript) = let
            val eval_th = EVAL EXN_TYPE_e_Subscript
            val eval_th = EQT_ELIM eval_th
        in (eval_th, true) end
        handle HOL_ERR _ => (TRUTH, false)

        val set_subst =
          let val set_type = type_of set_arr |> dom_rng |> snd |> dom_rng
          in match_type (snd set_type) (fst set_type) end
        val set_arr' = Term.inst set_subst set_arr

        val update_thm =
          if usesSubscript then let
            val th =
              ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr', update_exn]
                      EvalM_R_Marray_update_subscript
            val th = SPEC_ALL th |> UNDISCH |> UNDISCH
            val th = MP th subscript_eval |> remove_assumption
                        |> remove_assumption |> UNDISCH_ALL
          in rewrite_thm th end
          else let
            val th =
              ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr,
                     update_exn,update_rexp] EvalM_R_Marray_update_handle
            val th = SPEC_ALL th |> UNDISCH |> UNDISCH
            val th = remove_assumption th |> remove_assumption
            val th = UNDISCH th
            val th = MP th Eval_update_rexp |> UNDISCH
          in rewrite_thm th end
        (*
        val update_thm = rewrite_thm th
        *)
        val thm_name = name ^"_update_thm"
        val _ = save_thm(thm_name, update_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* alloc *)
        (*
        val alloc_thm = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr']
                              EvalM_R_Marray_alloc |> SPEC_ALL

        *)
        val alloc_thm = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr']
                              EvalM_R_Marray_alloc |> SPEC_ALL
        val alloc_thm = rewrite_thm alloc_thm |> UNDISCH
        val alloc_thm = remove_assumption alloc_thm |> remove_assumption

        val thm_name = name ^"_alloc_thm"
        val _ = save_thm(thm_name, alloc_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in
        (intro_hprop length_thm,
         intro_hprop sub_thm,
         intro_hprop update_thm,
         intro_hprop alloc_thm)
    end

    val rarrays_access_thms = List.map prove_rarray_specs (zip rarrays_manip_list rarrays_refs_locs_defs)
    (*
      val rarrays_access_thms = [it]
    *)

    (* Fixed-size arrays *)
    (* val (name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def, update_def) = List.hd farrays_manip_list;
       val loc_def = List.hd farrays_locs_defs; *)
    fun prove_farray_specs ((name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def, update_def), loc_def) = let
        val name_v = stringLib.fromMLstring name
        val loc = concl loc_def |> lhs
        val TYPE =  get_fun |> dest_abs |> snd |> type_of |> dest_type |> snd |> List.hd |> get_type_inv
        val EXN_TYPE = exn_ri
        val get_arr = get_fun
        val set_arr = set_fun
        val sub_exn = concl sub_def |> rhs |> rand
        val update_exn = concl update_def |> rhs |> rand
        val Eval_sub_rexp = hol2deep sub_exn
        val sub_rexp = concl Eval_sub_rexp |> rator |> rand
        val Eval_update_rexp = hol2deep update_exn
        val update_rexp = concl Eval_update_rexp |> rator |> rand

        val compos_conv = (PURE_REWRITE_CONV[store_X_hprop_def])
                              THENC (ABS_CONV (PICK_REF_CONV loc))
                              THENC (PURE_REWRITE_CONV[GSYM STAR_ASSOC])

        val H_eq = compos_conv store_pred
        val (state_var, H_part) = concl H_eq |> rhs |> dest_abs
        val H_part = if List.length refs_manip_list + List.length rarrays_manip_list + List.length farrays_manip_list > 1 then
                         mk_abs(state_var, rand H_part)
                     else mk_abs(state_var, emp_const)

        fun rewrite_thm th = let
            val th = PURE_ONCE_REWRITE_RULE[GSYM loc_def] th
            val th = PURE_REWRITE_RULE[GSYM length_def, GSYM sub_def, GSYM update_def] th
            val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
            val th = PURE_REWRITE_RULE[GSYM H_eq] th
        in th end

        (* length *)
        val length_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr] EvalM_F_Marray_length
        val length_thm = rewrite_thm length_thm

        val thm_name = name ^"_length_thm"
        val _ = save_thm(thm_name, length_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* sub *)
        (* Test if the sub exception is linked to the CakeML subscript
           exception by the exception refinement invariant *)
        val EXN_TYPE_e_Subscript =
            list_mk_comb(EXN_TYPE,[sub_exn,Conv_Subscript])
        val (subscript_eval, usesSubscript) = let
            val eval_th = EVAL EXN_TYPE_e_Subscript
            val eval_th = EQT_ELIM eval_th
        in (eval_th, true) end
        handle HOL_ERR _ => (TRUTH, false)

        val sub_thm =
          if usesSubscript then let
            val th = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,sub_exn]
                            EvalM_F_Marray_sub_subscript |> SPEC_ALL
            val th = MP th subscript_eval |> UNDISCH |> UNDISCH |> rewrite_thm
          in th end
          else let
            val th = ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,sub_exn,sub_rexp]
                            EvalM_F_Marray_sub_handle |> SPEC_ALL
            val th = rewrite_thm th |> UNDISCH |> UNDISCH |> UNDISCH
            val th = MP th Eval_sub_rexp
          in th end

        val thm_name = name ^"_sub_thm"
        val _ = save_thm(thm_name, sub_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

        (* update *)
        (* Test if the update exception is linked to the CakeML subscript
           exception by the exception refinement invariant *)
        val EXN_TYPE_e_Subscript =
            list_mk_comb(EXN_TYPE,[update_exn,Conv_Subscript])
        val (subscript_eval, usesSubscript) = let
            val eval_th = EVAL EXN_TYPE_e_Subscript
            val eval_th = EQT_ELIM eval_th
        in (eval_th, true) end
        handle HOL_ERR _ => (TRUTH, false)

        val update_thm =
          if usesSubscript then let
            val th =
              ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr,update_exn]
                      EvalM_F_Marray_update_subscript
            val th = SPEC_ALL th |> UNDISCH |> UNDISCH
            val th = MP th subscript_eval |> remove_assumption
                        |> remove_assumption |> UNDISCH_ALL
          in rewrite_thm th end
          else let
            val th =
              ISPECL[name_v,loc,TYPE,EXN_TYPE,H_part,get_arr,set_arr,
                     update_exn,update_rexp] EvalM_F_Marray_update_handle
            val th = SPEC_ALL th |> UNDISCH |> UNDISCH
            val th = remove_assumption th |> remove_assumption
            val th = UNDISCH th
            val th = MP th Eval_update_rexp |> UNDISCH
          in rewrite_thm th end

        val thm_name = name ^"_update_thm"
        val _ = save_thm(thm_name, update_thm)
        val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in
        (intro_hprop length_thm,
         intro_hprop sub_thm,
         intro_hprop update_thm)
    end

    val farrays_access_thms = List.map prove_farray_specs (zip farrays_manip_list farrays_locs_defs)

in
    (refs_access_thms, rarrays_access_thms, farrays_access_thms)
end

end

fun create_locs_variables refs_manip_list
                          rarrays_manip_list
                          farrays_manip_list =
  let
    val refs_names = List.map (fn (n, _, _) => n) refs_manip_list
    val refs_locs_names = List.map (fn x => "init_"^x) refs_names
    val refs_locs_vars = List.map (fn x => mk_var(x, v_ty)) refs_locs_names

    val rarrays_names = List.map (fn (n, _, _, _, _, _, _) => n) rarrays_manip_list
    val rarrays_locs_names = List.map (fn x => "init_" ^x) rarrays_names
    val rarrays_locs_vars = List.map (fn x => mk_var(x, v_ty)) rarrays_locs_names

    val farrays_names = List.map (fn (n, _, _, _, _, _) => n) farrays_manip_list
    val farrays_locs_names = List.map (fn x => "init_" ^x) farrays_names
    val farrays_locs_vars = List.map (fn x => mk_var(x, v_ty)) farrays_locs_names
in (refs_locs_vars, rarrays_locs_vars, farrays_locs_vars) end

type monadic_translation_parameters =
    {store_pred_def : thm,
     refs_specs : (thm * thm) list,
     rarrays_specs : (thm * thm * thm * thm) list,
     farrays_specs : (thm * thm * thm) list};

fun translate_dynamic_init_fixed_store refs_manip_list
                                       rarrays_manip_list
                                       farrays_manip_list
                                       store_hprop_name
                                       state_type
                                       exn_ri_def
                                       store_pinv_def_opt =
  let
    (* Create the store predicate *)
    val (refs_locs, rarrays_refs_locs, farrays_locs) =
      create_locs_variables refs_manip_list
                            rarrays_manip_list
                            farrays_manip_list

    val refs_manip_list = find_refs_access_functions refs_manip_list
    val rarrays_manip_list = find_rarrays_access_functions rarrays_manip_list
    val farrays_manip_list = find_farrays_access_functions farrays_manip_list
    val extra_hprop = NONE
    (*
      val refs_manip_list = []
    *)
    val store_X_hprop_def = create_store_X_hprop refs_manip_list
                                                 refs_locs
                                                 rarrays_manip_list
                                                 rarrays_refs_locs
                                                 farrays_manip_list
                                                 farrays_locs
                                                 state_type
                                                 store_hprop_name
                                                 store_pinv_def_opt
                                                 extra_hprop
    (*
      val store_X_hprop_def = store_hprop_def
    *)

    (* Prove the store access specifications *)
    (* Create dummy rewriting rules for the locations *)
    val refs_locs_defs = List.map REFL refs_locs
    val rarrays_refs_locs_defs = List.map REFL rarrays_refs_locs
    val farrays_locs_defs = List.map REFL farrays_locs

    (* Prove the access specifications *)
    (*
    val (refs_access_thms, rarrays_access_thms, farrays_access_thms) = it
    *)
    val (refs_access_thms, rarrays_access_thms, farrays_access_thms) =
      prove_store_access_specs refs_manip_list
                               rarrays_manip_list
                               farrays_manip_list
                               refs_locs_defs
                               rarrays_refs_locs_defs
                               farrays_locs_defs
                               store_X_hprop_def
                               state_type
                               exn_ri_def
                               store_pinv_def_opt
                               extra_hprop
in
    {store_pred_def = store_X_hprop_def,
     refs_specs = refs_access_thms,
     rarrays_specs = rarrays_access_thms,
     farrays_specs = farrays_access_thms} : monadic_translation_parameters
end;

type store_translation_result =
    {refs_init_values : thm list,
     refs_locations  : thm list,
     rarrays_init_values : thm list,
     farrays_init_values : thm list,
     rarrays_locations : thm list,
     farrays_locations : thm list,
     store_pred_validity : thm,
     store_pred_exists_thm : thm};

fun translate_static_init_fixed_store refs_init_list rarrays_init_list farrays_init_list store_hprop_name state_type exn_ri_def store_pinv_opt extra_hprop =
  let
    (* Create the store *)
    val (initial_store,
         refs_trans_results,
         rarrays_trans_results,
         farrays_trans_results) =
      create_store refs_init_list rarrays_init_list farrays_init_list

    (* Create the store predicate *)
    val refs_manip_list =
      get_refs_manip_funs refs_init_list |> find_refs_access_functions
    val rarrays_manip_list =
      get_rarrays_manip_funs rarrays_init_list |> find_rarrays_access_functions
    val farrays_manip_list =
      get_farrays_manip_funs farrays_init_list |> find_farrays_access_functions

    val refs_locs_defs = List.map snd refs_trans_results
    val rarrays_refs_locs_defs = List.map #3 rarrays_trans_results
    val farrays_locs_defs = List.map snd farrays_trans_results
    val refs_locs = List.map (lhs o concl) refs_locs_defs
    val rarrays_refs_locs = List.map (lhs o concl) rarrays_refs_locs_defs
    val farrays_locs = List.map (lhs o concl) farrays_locs_defs

    val store_pinv_def_opt = get_store_pinv_def_opt store_pinv_opt

    val store_X_hprop_def =
      create_store_X_hprop refs_manip_list
                           refs_locs
                           rarrays_manip_list
                           rarrays_refs_locs
                           farrays_manip_list
                           farrays_locs
                           state_type
                           store_hprop_name
                           store_pinv_def_opt
                           extra_hprop

    (* Prove the access specifications *)
    val (refs_access_thms, rarrays_access_thms, farrays_access_thms) =
      prove_store_access_specs refs_manip_list
                               rarrays_manip_list
                               farrays_manip_list
                               refs_locs_defs
                               rarrays_refs_locs_defs
                               farrays_locs_defs
                               store_X_hprop_def
                               state_type
                               exn_ri_def
                               store_pinv_def_opt
                               extra_hprop

    (* Prove the validity and existential theorems *)
    val current_state = get_state(get_ml_prog_state())
    val store_pinv_info_opt =
      case store_pinv_opt of
        SOME x => SOME (refs_init_list, rarrays_init_list, rarrays_init_list, x)
      | NONE => NONE

    val valid_store_X_hprop_thm =
      if isSome extra_hprop then TRUTH else
      prove_valid_store_X_hprop true
                                refs_manip_list
                                rarrays_manip_list
                                farrays_manip_list
                                refs_trans_results
                                rarrays_trans_results
                                farrays_trans_results
                                initial_store
                                current_state
                                state_type
                                store_X_hprop_def
                                store_pinv_info_opt

    val exists_store_X_hprop_thm =
      if isSome extra_hprop then TRUTH else
      prove_exists_store_X_hprop true
                                 state_type
                                 store_hprop_name
                                 valid_store_X_hprop_thm

    (* Return *)
    val (refs_values, refs_locs) = unzip refs_trans_results
    val (rarrays_values, rarrays_locs) = unzip (List.map (fn (x, _, y) => (x, y)) rarrays_trans_results)
    val (farrays_values, farrays_locs) = unzip farrays_trans_results
  in
    ({store_pred_def = store_X_hprop_def,
     refs_specs = refs_access_thms,
     rarrays_specs = rarrays_access_thms,
     farrays_specs = farrays_access_thms} : monadic_translation_parameters,

    {refs_init_values = refs_values,
     refs_locations = refs_locs,
     rarrays_init_values = rarrays_values,
     rarrays_locations = rarrays_locs,
     farrays_init_values = farrays_values,
     farrays_locations = farrays_locs,
     store_pred_validity = valid_store_X_hprop_thm,
     store_pred_exists_thm = exists_store_X_hprop_thm} : store_translation_result)
  end;

end
