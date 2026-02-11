(*
  The HOL to CakeML translator itself.
  The main entry point is the translate function.
*)
structure ml_translatorLib :> ml_translatorLib =
struct

open HolKernel boolLib bossLib BasicProvers;

open astTheory semanticPrimitivesTheory namespaceTheory;
open evaluateTheory astSyntax semanticPrimitivesSyntax;
local open stringLib in end
open ml_translatorTheory ml_translatorSyntax intLib;
open arithmeticTheory listTheory combinTheory pairTheory pairLib;
open integerTheory intLib ml_optimiseTheory ml_pmatchTheory;
open mlstringLib mlstringSyntax mlvectorSyntax packLib ml_progTheory ml_progLib
local open integer_wordSyntax permLib comparisonTheory in end

val ERR = mk_HOL_ERR "ml_translatorLib";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

local

  structure Parse = struct
    open Parse
     val (Type,Term) =
         parse_from_grammars $ valOf $ grammarDB {thyname="ml_translator"}
  end
  open Parse
  val prim_exn_list = let
    val tm = primSemEnvTheory.prim_sem_env_eq |> concl |> rand |> rand |> rand
    val (xs,ty) = ``^tm.c`` |> SIMP_CONV (srw_ss()) []
                     |> concl |> rand |> rator |> rand |> listSyntax.dest_list
    val ys = filter (semanticPrimitivesSyntax.is_ExnStamp o rand o rand) xs
  in listSyntax.mk_list(ys, ty) end

  val term_alist =
   [("find_recfun",``find_recfun name funs : ('a # 'b) option``),
     ("eq type",``EqualityType (a:'a->v->bool)``),
     ("lookup_cons",``lookup_cons s e = SOME x``),
     ("nsLookup",``nsLookup (e:('a,'b,v) namespace) s = SOME (x:v)``),
         (*TODO: Should this be e or e.v?*)
     ("eq remove",``!b x. Eq b x = (b:'a->v->bool)``),
     ("map pat",``MAP (f:'a->'b)``),
     ("filter pat",``FILTER (f:'a->bool)``),
     ("every pat",``EVERY (f:'a->bool)``),
     ("exists pat",``EXISTS (f:'a->bool)``),
     ("n = 0",``(n = (0:num))``),
     ("0 = n",``(0 = (n:num))``),
     ("bind",``(Con(SOME(Short«Bind»)) [])``),
     ("eq arrow",“ml_translator$Arrow (Eq (a:'a->v->bool) x) (b:'b->v->bool)”),
     ("arrow eq",``Arrow (Eq a (x:'a)) (b:'b->v->bool)``),
     ("precond = T",``!b. PRECONDITION b = T``),
     ("WF",``WF:('a -> 'a -> bool) -> bool``),
     ("COND",``COND:bool -> 'a -> 'a -> 'a``),
     ("not eq",``~(x = y:'a)``),
     ("lookup_cons eq",``lookup_cons n env = x``),
     ("Eval Var",``Eval env (Var n) (a (y:'a))``),
     ("PMATCH_ROW",``(PMATCH_ROW f1 f2):('a -> 'c) -> 'b -> 'c option``),
     ("PMATCH_ROW_T",``(PMATCH_ROW (f1:'a->'b) (K T) f3):'b -> 'c option``),
     ("PMATCH",``PMATCH x (l :('a -> 'b option) list)``),
     ("evaluate_pat",``evaluate (_ : α semanticPrimitives$state) _ _``),
     ("PreImp_Eval",``PreImp _ (Eval _ _ _)``),
     ("nsLookup_pat",``nsLookup (env:(α,β,γ) namespace) name``),
     ("pmatch_eq_Match_type_error",``pmatch _ _ _ _ _ = Match_type_error``),
     ("auto eq proof 1",``!x1:α x2:β x3:γ x4:δ. bbb``),
     ("auto eq proof 2",``!x1:α x2:β. bbb ==> bbbb``),
     ("remove lookup_cons",``!x1 x2 x3. (lookup_cons x1 x2 = SOME x3) = T``),
     ("no_closure_pat",``!(x:α) v. p x v ==> no_closures v``),
     ("types_match_pat",``!x1:α v1 x2:α v2. p x1 v1 /\ p x2 v2 ==> types_match v1 v2``),
     ("prim_exn_list",prim_exn_list),
     ("list-type-char",``LIST_TYPE CHAR``),
     ("OPTION_TYPE_SIMP",``!OPTION_TYPE x. CONTAINER OPTION_TYPE
              (\y v. if x = SOME y then p y v else ARB) x =
           (OPTION_TYPE (p:('a -> v -> bool)) x):v->bool``)]
in

  val get_term = fn s => assoc s term_alist
end (* local *)
fun primCases_on tm = Cases_on [ANTIQUOTE tm]

fun print_time s f x = f x
(*
let
  val () = print "Starting "
  val () = print s
  val () = print "...\n"
  val r = time f x
  val () = print s
  val () = print " done\n"
in r end
*)

exception UnableToTranslate of term;
exception UnsupportedType of hol_type;
exception NotFoundVThm of term;

(* non-persistent state *)

local
  val use_string_type_ref = ref false;
  val use_sub_check_ref = ref false; (* whether to default to checked num - *)
  val finalise_function = ref (I:unit -> unit);
in
  fun use_string_type b =
    (use_string_type_ref := b;
     if b then print "Translator now treats `char list` as a CakeML string.\n"
     else print "Translator now treats `char list` as a list of characters in CakeML.\n");
  fun use_hol_string_type () = !use_string_type_ref
  fun use_sub_check b =
    (use_sub_check_ref := b;
     if b then print "Translator now uses checked subtraction on num.\n"
     else print "Translator now generates side conditions for subtraction on num.\n");
  fun sub_check () = !use_sub_check_ref
  fun add_finalise_function f = let
    val old_f = !finalise_function
    in (finalise_function := (fn () => (old_f (); f ()))) end
  fun run_finalise_function () = (!finalise_function) ()
end


(* / non-persistent state *)


(* code for managing state of certificate theorems *)

fun MY_MP name th1 th2 =
  MP th1 th2 handle e =>
    let
      val _ = print ("\n\n "^name^" MP th1 th2 failed, th1 is:\n\n")
      val _ = print_thm th1
      val _ = print "\n\nth2 is:\n\n"
      val _ = print_thm th2
      val _ = print "\n\n"
    in raise e end

fun reraise fname message r = raise (ERR fname (message ^ ": " ^ message_of r))

fun auto_prove_asms name ((asms,goal),tac) = let
  val (rest,validation) = tac (asms,goal)
    handle HOL_ERR r => reraise "auto_prove_asms" "tactic failure" r
  in if length rest = 0 then validation [] else let
  in failwith ("auto_prove_asms failed for " ^ name) end end

fun auto_prove proof_name (goal,tac:tactic) = let
  val (rest,validation) = tac ([],goal)
    handle HOL_ERR r => reraise "auto_prove" "tactic failure" r
      | Empty => raise (ERR "auto_prove" "tactic raised Empty")
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

val unknown_loc = prim_mk_const {Name = "unknown_loc" , Thy = "location"}
val word8 = wordsSyntax.mk_int_word_type 8
val word = wordsSyntax.mk_word_type alpha
val venvironment = mk_environment v_ty
val empty_dec_list = listSyntax.mk_nil astSyntax.dec_ty;
val Dtype_x = astSyntax.mk_Dtype
                (unknown_loc,
                 mk_var("x",#1(dom_rng(#2(dom_rng(type_of astSyntax.Dtype_tm))))));
val Dletrec_funs = astSyntax.mk_Dletrec
                    (unknown_loc,
                     mk_var("funs",#1(dom_rng(#2(dom_rng(type_of astSyntax.Dletrec_tm))))));
val Dexn_n_l =
  let val args = tl(#1(boolSyntax.strip_fun(type_of astSyntax.Dexn_tm))) in
    astSyntax.mk_Dexn (unknown_loc,mk_var("n",el 1 args), mk_var("l",el 2 args))
  end
val Dlet_v_x =
  let val args = tl(#1(boolSyntax.strip_fun(type_of astSyntax.Dlet_tm))) in
    astSyntax.mk_Dlet (unknown_loc,mk_var("v",el 1 args), mk_var("x",el 2 args))
  end
fun Dtype ls = astSyntax.mk_Dtype
                (unknown_loc,
                listSyntax.mk_list(ls,listSyntax.dest_list_type
                                        (#1(dom_rng(#2(dom_rng(type_of astSyntax.Dtype_tm)))))))
fun Dtabbrev name ty = astSyntax.mk_Dtabbrev
                (unknown_loc,listSyntax.mk_nil mlstringSyntax.mlstring_ty, name, ty)

fun Atapp ls x = astSyntax.mk_Atapp(listSyntax.mk_list(ls,astSyntax.ast_t_ty),x)
fun mk_store_v ty = mk_thy_type{Thy="semanticPrimitives",Tyop="store_v",Args=[ty]}
val v_store_v = mk_store_v v_ty
val refs_ty = listSyntax.mk_list_type v_store_v
val refs = mk_var("refs",refs_ty)
val refs' = mk_var("refs'",refs_ty)
val v = mk_var("v",v_ty)
val env_tm = mk_var("env",venvironment)
val cl_env_tm = mk_var("cl_env",venvironment)
val state_refs_tm = prim_mk_const{Name=TypeBasePure.mk_recordtype_fieldsel {fieldname="refs",tyname="state"},Thy="semanticPrimitives"}
fun mk_tid name =
  optionSyntax.mk_some
    (astSyntax.mk_Short
      (mlstringSyntax.mk_mlstring name))
val true_tid = mk_tid "true"
val false_tid = mk_tid "false"
val true_exp_tm = (Eval_Val_BOOL_TRUE |> concl |> rator |> rand)
val false_exp_tm = (Eval_Val_BOOL_FALSE |> concl |> rator |> rand)

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

fun is_const_str str = can prim_mk_const {Thy=current_theory(), Name=str};

fun find_const_name str = let
  fun aux n = let
    val s = str ^ "_" ^ int_to_string n
    in if is_const_str s then aux (n+1) else s end
  in if is_const_str str then aux 0 else str end

fun remove_Eq_from_v_thm th = let
  val pat = get_term "arrow eq"
  val tms = find_terms (can (match_term pat)) (concl th)
  val vs = tms |> map (rand o rand o rator)
  fun try_each f [] th = th
    | try_each f (x::xs) th = try_each f xs (f x th handle HOL_ERR _ => th)
  fun foo v th = let
    val th = th |> GEN v
                |> HO_MATCH_MP FUN_FORALL_INTRO
                |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
    in th end
  in try_each foo vs th end

fun normalise_assums th =
  th |> DISCH_ALL |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL

(* new state *)

val clean_on_exit = ref false;

(* make the qualified identifier for some item, where "base" is its base name
   (parameter of Short) in its local scope, mods is the module scope it was
   defined in, and curr_mods is the current module scope. *)
fun mk_qualified_relative_name curr_mods mods base = let
    val base_nm = astSyntax.mk_Short base
    fun drop_same (x :: xs) (y :: ys) = if x = y then drop_same xs ys
        else (x :: xs)
      | drop_same xs _ = xs
    val rel_mods = drop_same mods curr_mods
    val mks = mlstringSyntax.mk_mlstring
    fun mk_name [] b = b
      | mk_name (m :: ms) b = astSyntax.mk_Long (mks m, mk_name ms b)
  in mk_name rel_mods base_nm end

local
  val v_thms = ref ([] : (string (* name: "name" *) *
                          string (* ML name: "mlname" *) *
                          term (* HOL term: name *) *
                          thm (* certificate:
                                  (concrete mode)
                                    |- A name name_v
                                  (abstract mode)
                                    |- Eval env (Var (Short "mlname")) (A name) (inside module, or no module)
                                    |- Eval env (Var (Long "modname" "mlname")) (A name) (after module) *) *
                          thm (* precond definition: |- T or |- name_side ... = ... or user-provided *) *
                          string list (* module scope *)) list);
  val eval_thms = ref ([] : (string (* name *) *
                            term (* HOL term *) *
                            thm (* certificate: Eval env exp (P tm) *)) list);
  val prog_state = ref ml_progLib.init_state;
  val cons_name_state = ref ([] : (string  *       (* %%thy%%type%%ctor *)
                                  (term *         (* constructor name  *)
                                   string list) (* module scope *)) list);
  val type_mod_state = ref ([] : (string * (* type name *)
                                  string list (* module scope *)) list);
in
  fun get_ml_name (_:string,nm:string,_:term,_:thm,_:thm,_:string list) = nm
  fun get_const (_:string,_:string,tm:term,_:thm,_:thm,_:string list) = tm
  fun get_cert (_:string,_:string,_:term,th:thm,_:thm,_:string list) = th
  fun get_pre (_:string,_:string,_:term,_:thm,th:thm,_:string list) = th
  fun get_v_thms () = !v_thms
  fun v_thms_reset () =
    (v_thms := [];
     eval_thms := [];
     prog_state := ml_progLib.init_state);
  fun ml_prog_update f = (prog_state := f (!prog_state));
  fun get_ml_prog_state () = (!prog_state)
  fun get_curr_env () = get_env (!prog_state);
  fun get_curr_state () = get_state (!prog_state);
  fun get_curr_v_defs () = get_v_defs (!prog_state);
  fun get_curr_modules () = get_open_modules (!prog_state);
  fun add_v_thms (name,ml_name,th,pre_def) = let
    val thc = th |> concl
    val (tm,th) =
      if is_Eval thc then
        (thc |> rand |> rand,
         normalise_assums th)
      else (thc |> rator |> rand,th)
    val modules = get_curr_modules ()
    val _ = if Teq (concl pre_def) then () else
            (print ("\nWARNING: " ^ml_name^" has a precondition.\n\n"))
    in (v_thms := (name,ml_name,tm,th,pre_def,modules) :: (!v_thms)) end;
  fun filter_v_thms f = let
    val xs = (!v_thms)
    val ys = filter f xs
    val _ = (v_thms := ys)
    in length xs - length ys end
  (* if the order didn't matter...
  fun replace_v_thm c th = let
    val (found_v_thms,left_v_thms) = partition (same_const c o get_const) (!v_thms)
    val (name,ml_name,_,_,pre,m) = hd found_v_thms
  in v_thms := (name,ml_name,c,th,pre,m) :: left_v_thms end
  *)
  fun replace_v_thm c th = let
    fun f [] = failwith "replace_v_thm: not found"
      | f ((name,ml_name,c',th',pre,m)::vths) =
        if same_const c c' then ((name,ml_name,c,th,pre,m)::vths)
        else (name,ml_name,c',th',pre,m)::f vths
    in v_thms := f (!v_thms) end
  fun add_user_proved_v_thm th = let
    val th = UNDISCH_ALL th
    val v = th |> concl |> rand
    val _ = (type_of v = v_ty) orelse failwith("add_user_proved_v_thm not a v thm")
    val tm = th |> concl |> rator |> rand
    val (name,ml_name,_,_,_,module_name) = first (fn (name,ml_name,tm,th,_,_) =>
          aconv (th |> concl |> rand) v) (!v_thms)
    in ((v_thms := (name,ml_name,tm,th,TRUTH,module_name) :: (!v_thms)); th) end;
  fun get_bare_v_thm const = first (can (C match_term const) o get_const) (!v_thms)
  fun get_qualified_name mods base = mk_qualified_relative_name
    (get_curr_modules ()) mods base
  fun lookup_v_thm const = let
    val (name,ml_name,c,th,pre,m) = get_bare_v_thm const
    val th = th |> SPEC_ALL |> UNDISCH_ALL
    val iden = get_qualified_name m (mlstringSyntax.mk_mlstring ml_name)
    val th = MATCH_MP Eval_Var_general th
        |> SPEC iden |> UNDISCH_ALL
    in th end
  fun lookup_abs_v_thm const =
    let
      val (name,ml_name,c,th,pre,m) = get_bare_v_thm const
      val cth = concl th
      val _ = is_Eval cth orelse raise NotFoundVThm const
      val tm =
        let
          val precond = first is_PRECONDITION (hyp th)
        in
          th |> DISCH precond |> concl
          |> curry list_mk_forall (free_vars precond)
        end handle HOL_ERR _ => th |> concl
      val code = rand(rator cth)
      val tm =
        if is_Var code then tm else
          (* TODO: mk_Long depending on m *)
          subst [code |-> mk_Var(mk_Short (mlstringSyntax.mk_mlstring ml_name))] tm
    in
      ASSUME tm |> SPEC_ALL |> UNDISCH_ALL
    end handle e as HOL_ERR holerr =>
      if top_function_of holerr = "first" then
         raise NotFoundVThm const
      else raise e
  fun lookup_eval_thm const = let
    val (name,c,th) = (first (fn c => can (match_term (#2 c)) const) (!eval_thms))
    in th |> SPEC_ALL |> UNDISCH_ALL end
  fun update_precondition new_pre = let
    fun update_aux (name,ml_name,tm,th,pre,module) = let
      val th1 = D th
      val (new_pre,th1) =
        (if is_imp (concl (SPEC_ALL new_pre))
         then (* case: new_pre is an induction theorem *)
           (((MATCH_MP IMP_EQ_T (MP (D new_pre) TRUTH)
             handle HOL_ERR _ => new_pre)
             |> PURE_REWRITE_RULE [GSYM CONJ_ASSOC]),
            PURE_REWRITE_RULE [GSYM CONJ_ASSOC] th1)
        else (new_pre,th1))
      val th2 = PURE_REWRITE_RULE [new_pre,PRECONDITION_T] th1
      in if aconv (concl th1) (concl th2)
         then (name,ml_name,tm,th,pre,module) else
           let
             val th2 = REWRITE_RULE [] th2
             val th = remove_Eq_from_v_thm th2
             val thm_name = name ^ "_v_thm"
             val _ = print ("Updating " ^ thm_name ^ "\n")
             val _ = allowing_rebind save_thm(thm_name,th)
             val new_pre = if can (find_term is_PRECONDITION) (concl (SPEC_ALL th))
                           then new_pre else TRUTH
             val th = th |> UNDISCH_ALL
           in (name,ml_name,tm,th,new_pre,module) end
      end
    val _ = (v_thms := map update_aux (!v_thms))
    in new_pre end
  fun add_eval_thm th = let
    val tm = concl (th |> SPEC_ALL |> UNDISCH_ALL)
    val const = tm |> rand |> rand
    val n = term_to_string const
    val _ = (eval_thms := (n,const,th)::(!eval_thms))
    in th end;
  fun check_no_ind_assum tm th = let
    val hs = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
                |> UNDISCH_ALL |> hyp
    in if can (first is_forall) hs then let
         val str = "User must prove skipped induction theorem for " ^
                   term_to_string tm
         in print ("\nERROR: " ^ str ^ "\n\n") ; failwith str end
       else ()
    end
  fun pack_v_thms () = let
    fun check_no_ind_assum_in_v (_,_,tm,th,_,_) = check_no_ind_assum tm th
    val _ = map check_no_ind_assum_in_v (!v_thms)
    val pack_vs = pack_list (pack_6tuple pack_string pack_string pack_term
                             pack_thm pack_thm (pack_list pack_string))
    val pack_evals = pack_list (pack_triple pack_string pack_term pack_thm)
    val cleaner = if !clean_on_exit then ml_progLib.clean_state else I
    in pack_triple pack_vs pack_evals pack_ml_prog_state
         (!v_thms,!eval_thms, cleaner (!prog_state)) end
  fun unpack_v_thms th = let
    val unpack_vs = unpack_list (unpack_6tuple unpack_string unpack_string unpack_term
                                 unpack_thm unpack_thm (unpack_list unpack_string))
    val unpack_evals = unpack_list (unpack_triple
                          unpack_string unpack_term unpack_thm)
    val (x1,x2,x3) = unpack_triple unpack_vs unpack_evals unpack_ml_prog_state th
    val _ = v_thms := x1
    val _ = eval_thms := x2
    val _ = prog_state := x3
    in () end
  fun pack_cons_names () =
    let
      val pack_ns =
        pack_pair pack_string (pack_pair pack_term (pack_list pack_string))
    in
      pack_list pack_ns (!cons_name_state)
    end
  fun pack_type_mods () =
    let
      val pack_ns = pack_pair pack_string (pack_list pack_string)
    in
      pack_list pack_ns (!type_mod_state)
    end
  fun unpack_type_mods th =
    let
      val unpack_ns = unpack_pair unpack_string (unpack_list unpack_string)
      val tyms = unpack_list unpack_ns th
    in
      type_mod_state := tyms
    end
  fun unpack_cons_names th =
    let
      val unpack_ns =
        unpack_pair unpack_string
                    (unpack_pair unpack_term (unpack_list unpack_string))
      val tyns = unpack_list unpack_ns th
    in
      cons_name_state := tyns
    end
  fun get_names() = map (#2) (!v_thms)
  fun get_v_thms_ref() = v_thms (* for the monadic translator *)
  fun get_type_mods () = !type_mod_state
  fun type_mods_reset () = type_mod_state := []
  fun lookup_type_mod tyname =
    SOME (Lib.assoc tyname (!type_mod_state))
    handle HOL_ERR _ => NONE
  (* TODO not sure we'll ever encounter duplicate type names - they should
   *      be entered with their full name. *)
  fun enter_type_mod tyname =
    let
      val mods = get_curr_modules ()
      val _ = lookup_type_mod tyname = NONE orelse
              failwith ("duplicate type: " ^ tyname)
    in
      case mods of
        [] => ()
      | _ => type_mod_state := (tyname,mods)::(!type_mod_state)
    end
  fun get_cons_names () = !cons_name_state
  fun cons_names_reset () = cons_name_state := []
  fun mk_cons_name tm =
    let
      val (_, ty) = strip_fun (type_of tm)
      val info = Option.valOf (TypeBase.fetch ty)
      val (thyn, tyn) = TypeBasePure.ty_name_of info
      val name = term_to_string tm
    in
      (* separating with underscores is more prone to name clashes *)
      String.concat ["%%", thyn, "%%", tyn, "%%", name, "%%"]
    end
  fun lookup_cons_name key = Lib.assoc key (!cons_name_state)
  fun enter_cons_name (tm, v_tm) =
    let
      val key   = mk_cons_name tm
      val mods = get_curr_modules ()
      val (v_tm', mods') = lookup_cons_name key
                            handle HOL_ERR _ => (v_tm, mods)
    in
      if aconv v_tm' v_tm andalso mods = mods' then
        key before cons_name_state := (key, (v_tm, mods)) :: (!cons_name_state)
      else
        raise ERR "enter_cons_name"
                ("already entered with different value: " ^ term_to_string v_tm)
    end
end

(*
 * Returns the 'full' identifier for the type. What this is depends on where the
 * type was registered. For types that are not in scope (i.e. outside of the
 * current module) we give a Long name, otherwise the name is short.
 *)
fun full_id n =
  case lookup_type_mod (mlstringSyntax.dest_mlstring n) of
    NONE => astSyntax.mk_Short n
  | SOME type_mod => get_qualified_name type_mod n;

(* code for managing type information *)

fun get_ty_case_const ty = let
  val th = TypeBase.case_def_of ty
  val case_const = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                      |> concl |> dest_eq |> fst |> repeat rator
  in case_const end

fun name_of_type ty = let
  val case_const = get_ty_case_const ty
  val name = case_const |> dest_const |> fst |> explode |> rev
                        |> funpow 5 tl |> rev |> implode
  in name end;

val basic_theories =
   ["alist", "arithmetic", "bag", "bitstring", "bit", "bool",
    "combin", "container", "divides", "fcp", "finite_map", "float",
    "fmaptree", "frac", "gcdset", "gcd", "ind_type", "integer_word",
    "integer", "integral", "list", "llist", "marker", "machine_ieee",
    "measure", "numeral_bit", "numeral", "numpair", "numposrep", "num",
    "one", "operator", "option", "pair", "path", "patricia_casts",
    "patricia", "poly", "poset", "powser", "pred_set", "prelim",
    "prim_rec", "quote", "quotient_list", "quotient_option",
    "quotient_pair", "quotient_pred_set", "quotient_sum", "quotient",
    "rat", "real_sigma", "realax", "real", "relation", "res_quan",
    "rich_list", "ringNorm", "ring", "sat", "semi_ring", "seq",
    "set_relation", "sorting", "state_option", "state_transformer",
    "string_num", "string", "sum_num", "sum", "topology", "transc",
    "update", "util_prob", "while", "words"]

val use_full_type_names = ref true;

fun full_name_of_type ty =
  if !use_full_type_names then let
    val case_const = get_ty_case_const ty
    val thy_name = case_const |> dest_thy_const |> #Thy
    val thy_name = if mem thy_name basic_theories then "" else thy_name ^ "_"
    in thy_name ^ name_of_type ty end
  else name_of_type ty;

(* ty must be a word type and dim ≤ 64 *)
fun word_ty_ok ty =
  if wordsSyntax.is_word_type ty then
    let val fcp_dim = wordsSyntax.dest_word_type ty in
      if fcpSyntax.is_numeric_type fcp_dim then
        let val dim = fcpSyntax.dest_int_numeric_type fcp_dim in
          dim <= 64
        end
      else
        false
    end
  else false;

val mlstring_ty = mlstringTheory.implode_def |> concl |> rand
  |> type_of |> dest_type |> snd |> last;

local
  val prim_exn_list = get_term "prim_exn_list"
  val xs = listSyntax.dest_list prim_exn_list |> fst
  val ys = map dest_pair xs |>
           map (fn (x,y) => (mlstringSyntax.dest_mlstring x,
                             numSyntax.int_of_term (y |> rator |> rand), y))
in
  fun get_primitive_exception name = let
    val (_,arity,value) = first (fn (n,_,_) => n = name) ys
    in (arity,value) end
  fun is_primitive_exception name = can get_primitive_exception name
end;

val float64_ty = mk_thy_type{Args = [fcpSyntax.mk_int_numeric_type 52,
                                     fcpSyntax.mk_int_numeric_type 11],
                             Thy = "binary_ieee",
                             Tyop = "float"}

val default_eq_lemmas = CONJUNCTS EqualityType_NUM_BOOL
    @ CONJUNCTS IsTypeRep_NUM_BOOL
    @ [IsTypeRep_PAIR, IsTypeRep_LIST, IsTypeRep_VECTOR]

local
  val type_mappings = ref ([]:(hol_type * hol_type) list)
  val other_types = ref ([]:(hol_type * term) list)
  val preprocessor_rws = ref ([]:thm list)
  val type_memory = ref ([]:(hol_type * thm * (term * thm) list * thm) list)
  val deferred_dprogs = ref ([]:term list)
  val all_eq_lemmas = ref default_eq_lemmas
in
  fun type_reset () =
    (type_mappings := [];
     other_types := [];
     preprocessor_rws := [];
     type_memory := [];
     deferred_dprogs := [];
     all_eq_lemmas := default_eq_lemmas)
  fun dest_fun_type ty = let
    val (name,args) = dest_type ty
    in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end
  fun find_type_mapping ty =
    first (fn (t,_) => can (match_type t) ty) (!type_mappings)
  fun free_typevars ty =
    if can dest_vartype ty then [ty] else let
    val (name,tt) = dest_type ty
    in Lib.flatten (map free_typevars tt) end
    handle HOL_ERR _ => []
  fun add_new_type_mapping ty target_ty =
    (type_mappings := (ty,target_ty) :: (!type_mappings))
  fun string_tl s = s |> explode |> tl |> implode
  fun prim_type name = Atapp [] (astSyntax.mk_Short(mlstringSyntax.mk_mlstring name))
  val bool_ast_t = prim_type "bool"
  val int_ast_t = prim_type "int"
  val char_ast_t = prim_type "char"
  val word8_ast_t = prim_type "word8"
  val word64_ast_t = prim_type "word64"
  val string_ast_t = prim_type "string"
  val double_ast_t = prim_type "double"

  val one_ast_t = mk_Attup(listSyntax.mk_list([],ast_t_ty))
  fun type2t ty =
    if ty = bool then bool_ast_t else
    if word_ty_ok ty then
      (*dim ≤ 64 guaranteeed*)
      let val dim = (fcpSyntax.dest_int_numeric_type o wordsSyntax.dest_word_type) ty in
        if dim <= 8 then word8_ast_t else word64_ast_t
      end else
    if ty = intSyntax.int_ty then int_ast_t else
    if ty = numSyntax.num then int_ast_t else
    if ty = stringSyntax.char_ty then char_ast_t else
    if ty = oneSyntax.one_ty then one_ast_t else
    if use_hol_string_type() andalso ty = stringSyntax.string_ty then string_ast_t else
    if ty = mlstring_ty then string_ast_t else
    if ty = float64_ty then double_ast_t else
    if can dest_vartype ty then
      astSyntax.mk_Atvar(mlstringSyntax.mk_mlstring (dest_vartype ty))
    else let
      val (lhs,rhs) = find_type_mapping ty
      val i = match_type lhs ty
      val xs = free_typevars rhs
      val i = filter (fn {redex = a, residue = _} => mem a xs) i
      val tm = type2t rhs
      val s = map (fn {redex = a, residue = b} => type2t a |-> type2t b) i
      in subst s tm end handle HOL_ERR _ =>
    let
      val (x,tt) = dest_type ty
      val name = if x = "fun" then "fun" else
                 if x = "prod" then "prod" else
                   full_name_of_type ty
      val tt = map type2t tt
      val name_tm = mlstringSyntax.mk_mlstring name
      in if name = "fun"  then mk_Atfun(el 1 tt, el 2 tt) else
         if name = "prod" then mk_Attup(listSyntax.mk_list(tt,astSyntax.ast_t_ty)) else
         if name = "list" then Atapp tt (astSyntax.mk_Short(name_tm))
                          else Atapp tt (full_id name_tm) end
  val HOL_STRING_TYPE =
    HOL_STRING_TYPE_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun inst_type_inv (ty,inv) ty0 = let
    val i = match_type ty ty0
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in subst ss (inst i inv) end
  and list_inst_type_inv ty0 [] = fail()
    | list_inst_type_inv ty0 ((ty,inv)::xs) =
        inst_type_inv (ty,inv) ty0 handle HOL_ERR _ =>
        list_inst_type_inv ty0 xs
  and get_type_inv ty =
    if is_vartype ty then let
      val name = dest_vartype ty |> explode |> tl |> implode
      in mk_var(name,ty --> (v_ty --> bool)) end else
    if can dest_fun_type ty then let
      val (t1,t2) = dest_fun_type ty
      in mk_Arrow(get_type_inv t1,get_type_inv t2)
      end else
    if ty = bool then BOOL else
    if wordsSyntax.is_word_type ty andalso word_ty_ok ty then
      let val dim = wordsSyntax.dest_word_type ty in
        inst [alpha|->dim] WORD
      end else
    if ty = numSyntax.num then NUM else
    if ty = intSyntax.int_ty then ml_translatorSyntax.INT else
    if ty = stringSyntax.char_ty then CHAR else
    if use_hol_string_type() andalso ty = stringSyntax.string_ty then HOL_STRING_TYPE else
    if ty = mlstringSyntax.mlstring_ty then STRING_TYPE else
    if ty = float64_ty then FLOAT64 else
    if is_vector_type ty then let
      val inv = get_type_inv (dest_vector_type ty)
      in VECTOR_TYPE_def |> ISPEC inv |> SPEC_ALL
         |> concl |> dest_eq |> fst |> rator |> rator end
    else
      list_inst_type_inv ty (!other_types)
      handle HOL_ERR _ => raise UnsupportedType ty
  fun new_type_inv ty inv = (other_types := (ty,inv) :: (!other_types))
  fun add_type_inv tm target_ty = let
    val ty = fst (dest_fun_type (type_of tm))
    val _ = add_new_type_mapping ty target_ty
    in new_type_inv ty tm end
  fun add_deferred_dprog dprog =
    if listSyntax.is_nil dprog then ()
    else deferred_dprogs := dprog::(!deferred_dprogs)
  fun pop_deferred_dprogs () =
    List.rev (!deferred_dprogs) before deferred_dprogs := []
  fun get_user_supplied_types () = map fst (!other_types)
  fun add_eq_lemma eq_lemma =
    if Teq (concl eq_lemma) then () else
      (all_eq_lemmas := eq_lemma :: (!all_eq_lemmas))
  fun add_type_thms (rws1,rws2,res,tr_lemmas) = let
    val _ = map (fn (ty,eq_lemma,inv_def,conses,case_lemma,ts) => add_eq_lemma eq_lemma) res
    val _ = map add_eq_lemma tr_lemmas
    val _ = (type_memory := map (fn (ty,eq_lemma,inv_def,conses,case_lemma,ts) => (ty,inv_def,conses,case_lemma)) res @ (!type_memory))
    val _ = (preprocessor_rws := rws2 @ (!preprocessor_rws))
    in () end
  fun ignore_type ty = (type_memory := (ty,TRUTH,[],TRUTH) :: (!type_memory));
  fun lookup_type_thms ty = first (fn (ty1,_,_,_) => can (match_type ty1) ty) (!type_memory)
  fun eq_lemmas () = (!all_eq_lemmas)
  fun get_preprocessor_rws () = (!preprocessor_rws)
  (* store/load to/from a single thm *)
  fun pack_types () =
    pack_6tuple
      (pack_list (pack_pair pack_type pack_type))
      (pack_list (pack_pair pack_type pack_term))
      (pack_list pack_thm)
      (pack_list (pack_4tuple pack_type pack_thm (pack_list (pack_pair pack_term pack_thm)) pack_thm))
      (pack_list pack_term)
      (pack_list pack_thm)
        ((!type_mappings), (!other_types), (!preprocessor_rws),
         (!type_memory), (!deferred_dprogs), (!all_eq_lemmas))
  fun unpack_types th = let
    val (t1,t2,t3,t4,t5,t6) = unpack_6tuple
      (unpack_list (unpack_pair unpack_type unpack_type))
      (unpack_list (unpack_pair unpack_type unpack_term))
      (unpack_list unpack_thm)
      (unpack_list (unpack_4tuple unpack_type unpack_thm (unpack_list (unpack_pair unpack_term unpack_thm)) unpack_thm))
      (unpack_list unpack_term)
      (unpack_list unpack_thm) th
    val _ = (type_mappings := t1)
    val _ = (other_types := t2)
    val _ = (preprocessor_rws := t3)
    val _ = (type_memory := t4)
    val _ = (deferred_dprogs := t5)
    val _ = (all_eq_lemmas := t6)
    in () end
end


(* misc *)

fun clean_lowercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [c] else
            if #"A" <= c andalso c <= #"Z" then implode [chr (ord c + 32)] else
            if #"0" <= c andalso c <= #"9" then implode [c] else
            if c = #"," then "pair" else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

fun clean_uppercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [chr (ord c - 32)] else
            if #"A" <= c andalso c <= #"Z" then implode [c] else
            if #"0" <= c andalso c <= #"9" then implode [c] else
            if c = #"," then "PAIR" else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

val sml_keywords_and_predefined = ["o", "+", "-", "*", "div", "mod",
  "<", ">", "<=", ">=", "ref", "and", "andalso", "case", "datatype",
  "else", "end", "eqtype", "exception", "fn", "fun", "handle", "if",
  "in", "include", "let", "local", "of", "op", "open", "orelse",
  "raise", "rec", "sharing", "sig", "signature", "struct",
  "structure", "then", "type", "val", "where", "while", "with",
  "withtype"]

fun get_unique_name str = let
  val names = get_names() @ sml_keywords_and_predefined
  fun find_name str n = let
    val new_name = str ^ "_" ^ (int_to_string n)
    in if mem new_name names then find_name str (n+1) else new_name end
  fun find_new_name str =
    if mem str names then find_name str 1 else str
  val initial_name = clean_lowercase str
  val initial_name = if size initial_name = 0 then "f" else initial_name
  in find_new_name initial_name end

fun dest_args tm =
  let val (x,y) = dest_comb tm in dest_args x @ [y] end
  handle HOL_ERR _ => []

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

val quietDefine = (* quiet version of Define -- by Anthony Fox *)
  Lib.with_flag (Feedback.emit_WARNING, false) $
  Lib.with_flag (Feedback.emit_ERR, false) $
  Lib.with_flag (Feedback.emit_MESG, false) $
  Feedback.trace ("Definition.auto Defn.tgoal", 0) $
  allowing_rebind $
    TotalDefn.Define

(* printing output e.g. SML syntax *)

val print_asts = ref false;

local
  val base_filename = ref "";
  val prelude_decl_count = ref 0;
  datatype print_item = Translation of string * thm | InvDef of thm
  val print_items = ref ([]:print_item list)
  val prelude_name = ref (NONE: string option);
in
  fun add_print_item i = (print_items := i :: (!print_items))
  val files = ["_ml.txt","_hol.txt","_thm.txt","_ast.txt"]
  fun check_suffix suffix = mem suffix files orelse failwith("bad file suffix")
  fun clear_file suffix = if (!base_filename) = "" then () else let
    val _ = check_suffix suffix
    val t = TextIO.openOut((!base_filename) ^ suffix)
    val _ = TextIO.closeOut(t)
    in () end
  fun get_filename () =
    if not (!print_asts) then "" else
    if !base_filename = "" then let
      val name = current_theory()
      val _ = (base_filename := name)
      val _ = map clear_file files
      in name end
    else !base_filename
  fun append_to_file suffix strs = if get_filename() = "" then () else let
    val _ = check_suffix suffix
    val t = TextIO.openAppend(get_filename() ^ suffix)
    val _ = map (fn s => TextIO.output(t,s)) strs
    val _ = TextIO.closeOut(t)
    in () end
  fun print_decls_aux xs suffix f =
    map (fn tm => append_to_file suffix (f tm)) xs
  fun drop n [] = [] | drop n xs = if n = 0 then xs else drop (n-1) (tl xs)
  fun print_str str = str
  fun print_prelude_comment suffix =
    case !prelude_name of
      NONE => ()
    | SOME name => append_to_file suffix ["\n(* This code extends '"^name^"'. *)\n"]
  fun print_decls () = ();
  fun print_item _ = ()
  fun print_decl_abbrev () = ()
  fun print_prelude_name () = ()
  fun print_reset () =
    (base_filename := "";
     prelude_decl_count := 0;
     print_items := [];
     prelude_name := NONE)
  fun init_printer name = let
    val _ = map clear_file files
    val _ = (prelude_name := SOME name)
    val _ = (prelude_decl_count := (length []))
    in () end
  fun print_translation_output () =
    (print_prelude_name (); map print_item (rev (!print_items));
     print_decl_abbrev (); print_decls ());
  fun print_fname fname def = add_print_item (Translation (fname,def));
  fun print_inv_def inv_def = add_print_item (InvDef inv_def);
end


(* timing output *)

val trace_timing_to = ref (NONE : string option)

fun timing_message msg = case ! trace_timing_to of
  SOME fname => let
    val f = TextIO.openAppend fname
  in TextIO.output (f, "  ++ " ^ msg ^ "\n");
    TextIO.closeOut f
  end | NONE => ()

fun start_timing nm = case ! trace_timing_to of
  SOME fname => let
    val time = Portable.timestamp ()
    val f = TextIO.openAppend fname
    val time_s = Portable.time_to_string time
  in TextIO.output (f, time_s ^ ": began " ^ nm ^ "\n");
    TextIO.closeOut f;
    SOME (fname, nm, time)
  end | NONE => NONE

fun end_timing t = case t of
  SOME (fname, nm, start_time) => let
    val time = Portable.timestamp ()
    val f = TextIO.openAppend fname
    val time_s = Portable.time_to_string time
    val dur_s = Portable.time_to_string (time - start_time)
  in TextIO.output (f, time_s ^ ": finished " ^ nm ^ "\n");
    TextIO.output (f, "  -- duration of " ^ nm ^ ": " ^ dur_s ^ "\n");
    TextIO.closeOut f
  end | NONE => ()

fun do_timing nm f x = let
    val start = start_timing nm
    val r = f x
  in end_timing start; r end

(* code for loading and storing translations into a single thm *)

fun check_uptodate_term t =
  if ThyDataSexp.uptodate t then () else (* let
    val t = find_term (fn tm => is_const tm
      andalso not (Theory.uptodate_term tm)) tm
    val _ = print "\n\nFound out-of-date term: "
    val _ = print_term t
    val _ = print "\n\n"
    in () *)
  raise mk_HOL_ERR "ml_translatorLib" "pack_state" "Out of date junk"




local
  val {export,segment_data,set} = ThyDataSexp.new {
    thydataty = "foo",
    merge = fn {old, new} => new,
    load = fn _ => (), other_tds = fn (t,_) => SOME t}
  fun pack_state () = let
    val p1 = pack_types()
    val p2 = pack_v_thms()
    val p3 = pack_cons_names()
    val p4 = pack_type_mods()
    val p = pack_4tuple I I I I (p1,p2,p3,p4)
    val _ = check_uptodate_term p
    in export p end
  fun unpack_state data = let
    val (p1,p2,p3,p4) = unpack_4tuple I I I I data
    val _ = unpack_types p1
    val _ = unpack_v_thms p2
    val _ = unpack_cons_names p3
    val _ = unpack_type_mods p4
    in () end;
  val finalised = ref false
in
  fun finalise_reset () = (finalised := false)
  fun finalise_translation () =
    if !finalised then () else let
      val _ = (finalised := true)
      val _ = run_finalise_function ()
      val _ = pack_state ()
      val _ = print_translation_output ()
      in () end
  fun translation_extends name = let
    val _ = print ("Loading translation: " ^ name ^ " ... ")
    val _ =
        case segment_data {thyname=name} of
            NONE => raise mk_HOL_ERR "ml_translatorLib" "translation_extends"
                          ("No translator data in theory " ^ name)
          | SOME data => unpack_state data
    val _ = init_printer name
    val _ = print ("done.\n")
    in () end;
  val _ = Theory.register_hook(
            "CakeML.ml_translator",
            (fn TheoryDelta.ExportTheory _ => finalise_translation() | _ => ()))

end

(* support for user-defined data-types *)

fun type_of_cases_const ty = let
  val th = TypeBase.case_def_of ty
    handle HOL_ERR e => raise ERR "type_of_cases_const" (String.concat["For ",Parse.type_to_string ty,"\n",Feedback.format_ERR e])
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> repeat rator |> type_of
  in ty end

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun get_nchotomy_of ty = let (* ensures that good variables names are used *)
  val case_th = TypeBase.nchotomy_of ty
  val ty0 = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
  val case_th = INST_TYPE (match_type ty0 ty) case_th
  val xs = map rand (find_terms is_eq (concl case_th))
  val x_var = mk_var("x",ty)
  fun mk_lines [] = []
    | mk_lines (x::xs) = let
    val k = length xs + 1
    fun rename [] = []
      | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                     int_to_string (length xs + 1)
                          in (x,mk_var("x" ^ n, type_of x),
                                mk_var("v" ^ n,v_ty)) end :: rename xs
    val vars = rev (rename (free_vars x))
    val new_x = subst (map (fn (x,y,z) => x |-> y) vars) x
    val tm = list_mk_exists(rev (free_vars new_x), mk_eq(x_var,new_x))
    in tm :: mk_lines xs end
  val goal = mk_forall(x_var,list_mk_disj (rev (mk_lines xs)))
  val lemma = auto_prove "get_nchotomy_of" (goal,
    STRIP_TAC \\ STRIP_ASSUME_TAC (ISPEC x_var case_th)
    \\ FULL_SIMP_TAC (srw_ss()) [])
  in lemma end

fun find_mutrec_types ty = let (* e.g. input ``:v`` gives [``:exp``,``:v``]  *)
  fun is_pair_ty ty = fst (dest_type ty) = "prod"
  val xs = TypeBase.axiom_of ty |> SPEC_ALL  |> concl |> strip_exists |> #1 |> map (#1 o dest_fun_type o type_of) |> (fn ls => filter (fn ty => intersect ((#2 o dest_type) ty) ls = []) ls)
  in if is_pair_ty ty then [ty] else if length xs = 0 then [ty] else xs end

(*

val type_name = name
val const_name = (repeat rator x |> dest_const |> fst)

*)

(*
  input: ``lookup_cons specific_name env_const = NONE``
  output: |- lookup_cons specific_name env_const = NONE <=> T
      or: |- lookup_cons specific_name env_const = NONE <=> F
  input: ``lookup_cons specific_name env_const = SOME stamp``
  output: |- lookup_cons specific_name env_const = SOME stamp <=> T
      or: |- lookup_cons specific_name env_const = SOME stamp <=> F
*)
val prove_lookup_cons_eq_fail = ref T;
(*
  val tm = !prove_lookup_cons_eq_fail
*)
fun prove_lookup_cons_eq tm =
  let
    val res = (* TODO: remove the SIMP_CONV and tidy up *)
      tm |> (REWRITE_CONV [lookup_cons_def]
             THENC TOP_DEPTH_CONV nsLookup_conv THENC EVAL
             THENC SIMP_CONV (srw_ss())
               [optionTheory.OPTION_CHOICE_EQ_NONE,empty_env_def]
             THENC EVAL THENC nsLookup_conv THENC EVAL)
    val c = res |> concl |> rand
    val _ = not (null (free_vars tm)) orelse aconv c T orelse aconv c F orelse
              raise ERR "prove_lookup_cons_eq" "prove_lookup_cons_eq failed to reduce to F or T"
  in res end
  handle e => (prove_lookup_cons_eq_fail := tm; print_term tm; raise e);

fun tag_name type_name const_name =
  if (type_name = "LIST_TYPE") andalso (const_name = "NIL") then "nil" else
  if (type_name = "LIST_TYPE") andalso (const_name = "CONS") then "::" else
  let
    val x = clean_lowercase type_name
    val y = clean_lowercase const_name
    fun upper_case_hd s =
      clean_uppercase (implode [hd (explode s)]) ^ implode (tl (explode s))
    val name = if y = "" then upper_case_hd x else upper_case_hd y
    val write_cons_pat =
      write_cons_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
    fun is_taken_name name =
      let
        val x =
          lookup_cons_def
          |> SPEC (mk_Short (mlstringSyntax.mk_mlstring name))
          |> SPEC (get_curr_env ()) |> concl |> dest_eq |> fst
        val n = optionSyntax.mk_none(type_of x |> dest_type |> snd |> hd)
        val tm = mk_eq(x,n)
        val lemma = prove_lookup_cons_eq tm
      in aconv (lemma |> concl |> rand) F end
    fun find_unique name n =
      if not (is_taken_name name) then name else let
        val new_name = name ^ "_" ^ int_to_string n
        in if not (is_taken_name new_name) then new_name else
           find_unique name (n+1) end
    in find_unique name 1 end;

val last_def_fail = ref T

fun derive_record_specific_thms ty = let
  val ty_name = name_of_type ty
  val access_funs =
    TypeBase.accessors_of ty
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
  val update_funs =
    TypeBase.updates_of ty
    |> map (rator o rator o fst o dest_eq o concl o SPEC_ALL)
  val thy_name = access_funs |> hd |>dest_thy_const |> #Thy
  val tm =
    DB.fetch thy_name (ty_name ^ "_11")
    |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_eq |> fst
  val xs = dest_args tm
  val c = repeat rator tm
  val case_tm =
    DB.fetch thy_name (ty_name ^ "_case_cong")
    |> SPEC_ALL |> UNDISCH_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun prove_accessor_eq (a,x) = let
    val v = mk_var("v",type_of tm)
    val f = foldr (fn (v,tm) => mk_abs(v,tm)) x xs
    val ty1 = case_tm |> type_of |> dest_type |> snd |> el 2
                                 |> dest_type |> snd |> hd
    val i = match_type ty1 (type_of f)
    val rhs = mk_comb(mk_comb(inst i case_tm,v),f)
    val lhs = mk_comb(a,v)
    val goal = mk_forall(v,mk_eq(lhs,rhs))
    val lemma = auto_prove "prove_accessor_eq" (goal,Cases THEN SRW_TAC [] [])
    in lemma end
  val a_lemmas = map prove_accessor_eq (zip access_funs xs)
  fun prove_updates_eq (a,x) = let
    val v = mk_var("v",type_of tm)
    val (t,ti) = type_of a |> dom_rng
    val ti = dom_rng ti |> #2
    val g = mk_var("g",t)
    val s = match_type (type_of tm) ti
    val tmi = Term.inst s tm
    val xi = Term.inst s x
    val f = foldr mk_abs (subst [xi|->mk_comb(g,x)] tmi) xs
    val ty1 = case_tm |> type_of |> dest_type |> snd |> el 2
                                 |> dest_type |> snd |> hd
    val i = match_type ty1 (type_of f)
    val rhs = mk_comb(mk_comb(inst i case_tm,v),f)
    val lhs = mk_comb(mk_comb(a,g),v)
    val goal = mk_forall(v,mk_forall(g,mk_eq(lhs,rhs)))
    val tac = Cases THEN SRW_TAC [] [DB.fetch thy_name (ty_name ^ "_fn_updates")]
    in auto_prove "prove_updates_eq" (goal,tac) end
  val b_lemmas = map prove_updates_eq (zip update_funs xs)
  val rtype = type_of tm
  val {Args,Thy,Tyop} = dest_thy_type rtype
  fun new_rtype() = let
    val Args = List.tabulate (length Args,fn _ => gen_tyvar())
    in mk_thy_type{Args=Args,Thy=Thy,Tyop=Tyop} end
  fun foldthis ((fupd,var),(rtype,y)) =
    let
      val (fty,updty) = fupd |> type_of |> dom_rng
      val (r1,r2) = dom_rng updty
      val s = match_type updty (rtype --> new_rtype())
              handle HOL_ERR _ => match_type updty (rtype --> rtype)
      val ifupd = inst s fupd
      val (g1,g2) = dom_rng (type_subst s fty)
      val (x,_) = dest_var var
      val x = mk_var(x,g2)
      val k = combinSyntax.mk_K_1 (x,g1)
    in (type_subst s r2,mk_comb(mk_comb(ifupd,k),y)) end
  val arb = mk_arb (new_rtype())
  val (_,tm2) = foldr foldthis (type_of arb,arb) (zip update_funs xs)
  val s = match_type (type_of tm2) rtype
  val tm2 = inst s tm2
  val goal = mk_eq(tm2,tm)
  val rw_lemma = auto_prove "rw_lemma" (goal,SRW_TAC []
    [DB.fetch thy_name (ty_name ^ "_component_equality")])
  val rw_lemmas =
    if length(TypeBase.fields_of ty) > 1
    then CONJ (DB.fetch thy_name (ty_name ^ "_fupdcanon")) rw_lemma
    else rw_lemma
  in (a_lemmas @ b_lemmas, [rw_lemmas]) end;

fun rename_bound_vars_rule prefix th = let
  val i = ref 0
  fun next_name orig = let
    val n = (i:= !i+1; prefix ^ int_to_string (!i))
    in if String.isSubstring " " orig then n else n ^ "_" ^ orig ^ "_" end
  fun next_var v = let
    val (name, ty) = dest_var v
    in mk_var(next_name name, ty) end
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix prefix (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end;

fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];

(*
  val ty = ``:'a + 'b``
  val tys = find_mutrec_types ty
  val is_exn_type = false
*)

fun tys_is_pair_type tys =
  (case tys of [ty] => can pairSyntax.dest_prod ty | _ => false)
fun tys_is_list_type tys =
  (case tys of [ty] => listSyntax.is_list_type ty | _ => false)
fun tys_is_unit_type tys =
  (case tys of [ty] => ty = oneSyntax.one_ty | _ => false)
fun tys_is_order_type tys =
  (case tys of [ty] => let val r = dest_thy_type ty in #Thy r = "toto" andalso #Tyop r = "cpn" end | _ => false)
val unit_tyname = mlstringSyntax.mk_mlstring "unit"
val order_tyname = mlstringSyntax.mk_mlstring "order"

fun guess_const_def tm = let
    val stuff = dest_thy_const tm
  in DB.fetch (#Thy stuff) (#Name stuff ^ "_def") end

val mlstring_EQ_CONV = REWR_CONV mlstringTheory.mlstring_11 THENC stringLib.string_EQ_CONV

local
fun mlstr_dest tm = mlstringSyntax.dest_mlstring tm |> explode |> map ord
in
val mlstr_all_distinct_conv = let open permLib comparisonTheory
  in ALL_DISTINCT_CONV (MATCH_MP good_cmp_Less_irrefl_trans mlstringTheory.good_cmp_compare)
    (fn x => fn y => list_compare Int.compare (mlstr_dest x, mlstr_dest y) = LESS)
    EVAL
  end
end
val num_all_distinct_conv = let open permLib comparisonTheory numSyntax
  in ALL_DISTINCT_CONV (MATCH_MP good_cmp_Less_irrefl_trans num_cmp_good)
    (fn x => fn y => int_of_term x < int_of_term y) EVAL
  end

fun get_type_n2typ_onto_thm typ = let
    val n2typ = TypeBase.simpls_of typ |> #rewrs
        |> List.mapPartial (total (fst o dest_eq o hd o strip_conj o concl))
        |> map (fst o strip_comb) |> filter is_const
        |> filter (String.isPrefix "num2" o fst o dest_const) |> hd
    val details = dest_thy_const n2typ
  in DB.fetch (#Thy details) (#Name details ^ "_ONTO") end

fun EqualityType_via_n2typ is_exn_type typ = let
    val TY = get_type_inv typ
    val ONTO_thm = get_type_n2typ_onto_thm typ
    val _ = print "Doing EqualityType proof via ONTO thm:"
    val _ = print_thm ONTO_thm
    val _ = print "\n"
    val eq_thm = if is_exn_type then EqualityType_from_ONTO_Exn
        else EqualityType_from_ONTO
    val thm = MATCH_MP eq_thm ONTO_thm |> ISPEC TY
    val genlist_tm = find_term listSyntax.is_genlist (concl thm)
    val genlist_eq = EVAL genlist_tm
    val stamps = concl genlist_eq |> rhs
      |> listSyntax.dest_list |> fst
      |> map (snd o dest_eq o snd o dest_abs)
      |> map (optionSyntax.dest_some o hd o snd o strip_comb)
    val stamp_list = map (hd o snd o strip_comb) stamps
      |> (fn xs => listSyntax.mk_list (xs, type_of (hd xs)))
    val thm2 = SPEC stamp_list thm
        |> (if is_exn_type then I else SPEC (rand (hd stamps)))
        |> CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV genlist_eq))
        |> CONV_RULE (DEPTH_CONV mlstr_all_distinct_conv)
        |> CONV_RULE (DEPTH_CONV num_all_distinct_conv)
  in SIMP_RULE list_ss [FUN_EQ_THM] thm2 end

fun matching_induction_of typ = let
    val ind = TypeBase.induction_of typ
    val ind_c = concl ind |> strip_forall |> snd |> dest_imp |> snd
    val var_tys = strip_conj ind_c |> map (type_of o fst o dest_forall)
    val matches = mapfilter (fn vty => match_type vty typ) var_tys
  in case matches of
      [] => failwith ("matching_induction_of: " ^ type_to_string typ)
    | _ => INST_TYPE (hd matches) ind
  end

val EqualityType_at = prim_mk_const{Thy="ml_translator",Name="EqualityType_at"}

fun mk_EqualityType_ind typ = let
    val ind = matching_induction_of typ
    val (ind_p, ind_c) = concl ind |> strip_forall |> snd |> dest_imp
    val proof_tys = strip_conj ind_c |> map (type_of o fst o dest_forall)
    val assum_tys = find_terms is_forall ind_p
        |> map (type_of o fst o dest_forall)
    val ex_assum_tys = subtract assum_tys proof_tys |> mk_set
    val ty_inv_defs = map get_type_inv proof_tys
        |> map (fst o strip_comb)
        |> filter is_const
        |> HOLset.fromList Term.compare |> HOLset.listItems
        |> map guess_const_def
    val ss = list_ss ++ simpLib.type_ssfrag v_ty ++ optionSimps.OPTION_ss
        ++ simpLib.type_ssfrag (pairSyntax.mk_prod (alpha, beta))
        ++ simpLib.type_ssfrag stamp_ty ++ stringSimps.STRING_ss
        ++ BasicProvers.thy_ssfrag "mlstring" ++ simpLib.type_ssfrag mlstringSyntax.mlstring_ty
    fun adj tm = if not (is_Conv tm) then snd (strip_comb tm)
        else dest_Conv tm |> snd |> listSyntax.dest_list |> fst
    fun inst_eq_at x ys = let
        val thm1 = GEN_ALL EqualityType_at_eq_Case_rearranged
            |> ISPECL [x, get_type_inv (type_of x)]
        val thm2 = ASSUME (lhs (concl thm1)) |> REWRITE_RULE [thm1, markerTheory.Case_def]
      in thm2 |> SPECL ys |> DISCH_ALL end
    fun insts [] oths = ALL_TAC
      | insts (x :: xs) oths = mp_tac (inst_eq_at x (map hd oths)) \\ insts xs (map tl oths)
    val fiddle_case_tac = FIRST_X_ASSUM (fn thm => let
        val xs = markerSyntax.dest_Case (concl thm) |> pairSyntax.spine_pair
        val ys = map adj xs
      in insts (hd ys) (tl ys) end)
    val gl = map (ml_translatorSyntax.mk_EqualityType o get_type_inv) proof_tys
        |> list_mk_conj
    val assums = map (ml_translatorSyntax.mk_EqualityType o get_type_inv) ex_assum_tys
    val prop = mk_imp (list_mk_conj (T :: assums), gl)
    val thm = prove (prop,
        disch_tac
        \\ REWRITE_TAC [EqualityType_eq_at]
        \\ ho_match_mp_tac ind
        \\ rpt strip_tac
        \\ REWRITE_TAC [EqualityType_at_eq_Case_rearranged]
        \\ Cases
        \\ simp_tac ss (ty_inv_defs @ [PULL_EXISTS, types_match_def,
            semanticPrimitivesTheory.ctor_same_type_def,
            semanticPrimitivesTheory.lit_same_type_def,
            semanticPrimitivesTheory.same_type_def, no_closures_def])
        \\ TRY (simp_tac (bool_ss ++ simpLib.type_ssfrag typ) [] \\ NO_TAC)
        \\ rpt (gen_tac ORELSE disch_tac)
        \\ full_simp_tac ss []
        \\ rpt fiddle_case_tac
        \\ full_simp_tac ss [EqualityType_eq_at, markerTheory.Case_def]
        \\ simp_tac (bool_ss ++ simpLib.type_ssfrag typ) []
    )
  in (assums, thm) end
  handle
        (e as HOL_ERR _) => (Raise (wrap_exn "ml_translatorLib" "mk_EqualityType_ind" e))
      | Empty => (Raise (ERR "mk_EqualityType_ind" "Empty raised"));

fun mk_EqualityType_thm is_exn_type typ = let
    val final_goal = ml_translatorSyntax.mk_EqualityType (get_type_inv typ)
    val _ = print "Attempting proof of: "
    val _ = print_term final_goal
    val (assums, thm) = if can get_type_n2typ_onto_thm typ
          then ([], EqualityType_via_n2typ is_exn_type typ)
          else mk_EqualityType_ind typ
  in
    prove (list_mk_imp (assums, final_goal),
        rpt strip_tac \\ mp_tac thm \\ asm_simp_tac bool_ss [])
    before print ".. done EqualityType proof.\n"
  end handle Option.Option =>
    (print ".. cannot do EqualityType proof.\n"; TRUTH)
           | HOL_ERR _ =>
    (print ".. cannot do EqualityType proof.\n"; TRUTH)

fun fetch_v_fun_ex extra_tms extra_thms ty = case assoc1 ty extra_tms of
    SOME (_, v_fun) => (v_fun, [])
  | NONE => if is_vartype ty then let
    val s = dest_vartype ty
  in (mk_var ("t_" ^ s ^ "_v", ty --> v_ty), []) end
  else let
    val inv = get_type_inv ty
    val inv_head = fst (strip_comb inv)
    (* this special case solves the issue with HOL_STRING_TYPE *)
    val (_, tys) = if is_const inv then ("s", []) else dest_type ty
    val f_opts = extra_thms @ eq_lemmas ()
        |> map (fn t => ((snd o strip_imp o concl) t, t))
        |> mapfilter (apfst ml_translatorSyntax.dest_IsTypeRep)
        |> filter (same_const inv_head o fst o strip_comb o snd o fst)
        |> map (apfst (fst o strip_comb o fst))
        |> HOLset.fromList (pair_compare (Term.compare, K EQUAL)) |> HOLset.listItems
    val (f, arg_tys, thms) = case f_opts of
      [] => (DUMMY_TYPE_REP_v, [], [])
    | [(f, th)] => (f, tys , [th])
    | _ => failwith ("fetch_v_fun_ex: multiple options for " ^ type_to_string ty)
    val rec_xs = map (fetch_v_fun_ex extra_tms extra_thms) arg_tys
    val arg_funs = map fst rec_xs
    val f_arg = strip_fun (type_of f) |> fst |> List.last
    val m = match_type f_arg ty
  in (list_mk_comb (inst m f, arg_funs), thms @ List.concat (map snd rec_xs)) end

fun mk_v_app extras v = mk_comb (fetch_v_fun_ex extras [] (type_of v) |> fst, v);

val fetch_v_fun = fetch_v_fun_ex [] []

(* define a type->v function from the type's induction rule and type_inv *)
fun define_v_fun ty = let
    val main_ty = ty
    val ind = matching_induction_of ty
    val args = concl ind |> strip_forall |> snd |> dest_imp |> snd
        |> strip_conj |> map (fst o dest_forall)
    val param_tys = type_vars_in_term (concl ind) |> map (fst o fetch_v_fun)
    val ty_inv_defs = map (get_type_inv o type_of) args
        |> map (fst o strip_comb)
        |> filter is_const
        |> HOLset.fromList Term.compare |> HOLset.listItems
        |> map guess_const_def
    fun name ty = get_type_inv ty |> strip_comb |> fst |> dest_const |> fst
        |> Portable.replace_string {from = "_TYPE", to = "_v"}
    fun is_aux ty = exists (not o is_vartype) (snd (dest_type ty))
    fun aux_name i ty = if is_aux ty then name main_ty ^ "_aux_" ^ Int.toString i
        else name ty
    val ops = mapi (fn i => fn v => list_mk_comb (mk_var (aux_name i (type_of v),
        foldr (fn (h, t) => type_of h --> t) (type_of v --> v_ty) param_tys), param_tys)) args
    val op_tups = map (fn t => (fst (dom_rng (type_of t)), t)) ops
    val cases = concl ind |> strip_forall |> snd |> dest_imp |> fst
        |> strip_conj
        |> map (rand o snd o strip_forall o snd o strip_imp o snd o strip_forall)
    val inv_def_eqs = map (strip_conj o concl) ty_inv_defs |> List.concat
    fun case_eqn t = let
        val (c, xs) = strip_comb t
        val eq = first (can (find_term (same_const c)) o lhs o snd o strip_forall) inv_def_eqs
        val conv = find_term (is_Conv) eq
        val stamp = fst (dest_Conv conv)
      in mk_eq (mk_v_app op_tups t, mk_Conv (stamp,
            listSyntax.mk_list (map (mk_v_app op_tups) xs, v_ty))) end
    val def = map case_eqn cases |> list_mk_conj
    val def_name = (hd ops |> strip_comb |> fst |> dest_var |> fst) ^ "_def"
    val def_thm = new_recursive_definition
        {name = def_name, rec_axiom = TypeBase.axiom_of ty, def=def}
    val const_ops = def_thm |> concl |> strip_conj
        |> map (rator o fst o dest_eq o snd o strip_forall)
        |> HOLset.fromList Term.compare |> HOLset.listItems
    val const_op_tups = map (fn t => (fst (dom_rng (type_of t)), t))
        (const_ops @ param_tys)
    fun mk_is_tr ty = mk_IsTypeRep (fst (fetch_v_fun_ex const_op_tups [] ty), get_type_inv ty)
    val arg_tys = map type_of args
    val all_tys = map (find_terms is_var) cases
        |> List.concat |> map type_of
        |> HOLset.fromList Type.compare |> HOLset.listItems
    val other_tys = subtract all_tys arg_tys
    val prop = map (mk_is_tr o type_of) args |> list_mk_conj
    val asms = T :: map mk_is_tr other_tys |> list_mk_conj
    val thm = prove (mk_imp (asms, prop),
        REWRITE_TAC [IsTypeRep_def]
        \\ TRY disch_tac \\ ho_match_mp_tac ind
        \\ asm_simp_tac (list_ss ++ simpLib.type_ssfrag v_ty)
            ([def_thm] @ ty_inv_defs)
    )
  in filter (not o is_aux) (map type_of args)
        |> map (fn ty => mk_imp (asms, mk_is_tr ty))
        |> map (fn gl => prove (gl, disch_tac \\ mp_tac thm \\ asm_simp_tac bool_ss []))
  end

fun define_type_reps [] = []
  | define_type_reps (ty :: tys) = let
    val reps = define_type_reps tys
    val more = case fetch_v_fun_ex [] reps ty of
        (_, []) => define_v_fun ty
      | _ => []
  in more @ reps end;

fun EqualityType_cc dir tm = let
    val lemmas = map (REWRITE_RULE [AND_IMP_INTRO]) (eq_lemmas ())
    val cc = ConseqConv.CONSEQ_REWRITE_CONV (lemmas, [], [])
  in cc dir tm end

fun EqualityType_rule prems ty = let
    val mk = ml_translatorSyntax.mk_EqualityType o get_type_inv
    val goal = if null prems then mk ty
        else mk_imp (list_mk_conj (map mk prems), mk ty)
  in prove (goal,
    ConseqConv.CONSEQ_CONV_TAC EqualityType_cc \\ full_simp_tac bool_ss [])
  end

(* remove some known-true preconditions of proven eq-lemmas *)
fun EqualityType_cc_conv tm = let
    val th = EqualityType_cc ConseqConv.CONSEQ_CONV_STRENGTHEN_direction tm
  in if same_const T (fst (dest_imp (concl th)))
    then prove (mk_eq (tm, T), mp_tac th \\ simp_tac bool_ss [])
    else raise UNCHANGED
  end

fun simp_eq_lemma th = if not (is_imp (concl th)) then th
  else let
    val conv = Conv.EVERY_CONJ_CONV (TRY_CONV EqualityType_cc_conv)
  in CONV_RULE (RATOR_CONV (RAND_CONV conv)) th end

fun define_ref_inv is_exn_type tys = let
  val is_pair_type = tys_is_pair_type tys
  val is_list_type = tys_is_list_type tys
  val is_unit_type = tys_is_unit_type tys
  val is_order_type = tys_is_order_type tys
  fun smart_full_name_of_type ty =
    if is_unit_type then "unit" else
    if is_order_type then "order" else
      full_name_of_type ty
  fun get_name ty = clean_uppercase (smart_full_name_of_type ty) ^ "_TYPE"
  val names = map get_name tys
  val name = hd names
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val cases_thms = map (SPEC_ALL o get_nchotomy_of) tys |> LIST_CONJ
                   |> rename_bound_vars_rule "x_" |> CONJUNCTS
  val all = zip names (zip tys cases_thms) |> map (fn (x,(y,z)) => (x,y,z))
  val tmp_v_var = genvar v_ty
  val real_v_var = mk_var("v",v_ty)
  fun mk_lhs (name,ty,case_th) = let
    val xs = map rand (find_terms is_eq (concl case_th))
    val ty = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
    val vars = type_vars ty
    val ss = map get_type_inv vars
    val input = mk_var("input",ty)
    val ml_ty_name = smart_full_name_of_type ty
    val def_name = mk_var(name,list_mk_type (ss @ [input]) (v_ty --> bool))
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) def_name (ss @ [input,tmp_v_var])
    in (ml_ty_name,xs,ty,lhs,input) end
  val ys = map mk_lhs all
  fun reg_type (_,_,ty,lhs,_) = new_type_inv ty (rator (rator lhs));
  val _ = map reg_type ys
  val opt_extra_rw = let
    val OPTION_TYPE = get_type_inv (type_of (optionSyntax.mk_none alpha)) |> rator
    val goal = get_term "OPTION_TYPE_SIMP" |> ASSUME |> ISPEC OPTION_TYPE |> concl
    val OPTION_TYPE_SIMP = auto_prove "OPTION_TYPE_SIMP" (goal,
      Cases \\ fs [CONTAINER_def,FUN_EQ_THM] \\ EVAL_TAC \\ simp [])
      |> Q.SPECL [`x`] |> SIMP_RULE std_ss [] |> GSYM
    in [OPTION_TYPE_SIMP] end handle HOL_ERR _ => []
  val rw_lemmas = LIST_CONJ ([LIST_TYPE_SIMP,PAIR_TYPE_SIMP] @ opt_extra_rw)
  val stamp = if is_exn_type then get_next_exn_stamp (get_ml_prog_state ())
                             else get_next_type_stamp (get_ml_prog_state ())
  fun get_def_tm () = let
    fun mk_lines ml_ty_name lhs ty [] input stamp = []
      | mk_lines ml_ty_name lhs ty (x::xs) input stamp = let
      val k = length xs + 1
      val cons_name = (repeat rator x |> dest_const |> fst)
      val tag = if is_exn_type andalso is_primitive_exception cons_name
                then cons_name
                else tag_name name cons_name
      fun rename [] = []
        | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                       int_to_string (length xs + 1)
                           in (x,mk_var("v" ^ n,v_ty)) end :: rename xs
      val vars = rev (rename (free_vars x))
      val ty_list = mk_type("list",[ty])
      val list_ty = (ty --> v_ty --> bool) --> listSyntax.mk_list_type(ty) --> v_ty --> bool
      fun find_inv tm =
          (mk_comb(get_type_inv (type_of tm),tm))
      val ys = map (fn (y,z) => mk_comb(find_inv y,z)) vars
      val tm = if List.null ys then T else list_mk_conj ys
      val str = mlstringSyntax.mk_mlstring tag
      val str_ty_name = mlstringSyntax.mk_mlstring
            (if is_exn_type then tag else ml_ty_name)
      val vs = listSyntax.mk_list(map (fn (_,z) => z) vars,v_ty)
      fun attach_name tag tm = let
        val (x,y) = dest_comb tm
        in mk_comb(x,combinSyntax.mk_K(y,mlstringSyntax.mk_mlstring tag)) end
      val tag_tm = if is_exn_type then
                     (if is_primitive_exception tag then
                        let
                          val (arity,value) = get_primitive_exception tag
                        in if length vars = arity
                           then rand value |> attach_name tag |> optionSyntax.mk_some
                           else failwith ("Incorrect arity for primitive exn: " ^ tag)
                        end
                      else
                        semanticPrimitivesSyntax.mk_ExnStamp (numSyntax.term_of_int stamp)
                          |> attach_name tag |> optionSyntax.mk_some)
                   else
                     semanticPrimitivesSyntax.mk_TypeStamp
                       (str,numSyntax.term_of_int stamp) |> optionSyntax.mk_some
      val tm = mk_conj(mk_eq(tmp_v_var,
                             mk_Conv(tag_tm, vs)),tm)
      val tm = list_mk_exists (map (fn (_,z) => z) vars, tm)
      val tm = subst [input |-> x] (mk_eq(lhs,tm))
      (* val vs = filter (fn x => x <> def_name) (free_vars tm) *)
      val ws = free_vars x
      in tm :: mk_lines ml_ty_name lhs ty xs input
                 (if is_exn_type andalso not (is_primitive_exception tag)
                  then stamp+1 else stamp) end
(*
val (ml_ty_name,x::xs,ty,lhs,input) = hd ys
*)
    fun mk_all_lines [] stamp = []
      | mk_all_lines ((ml_ty_name,xs,ty,lhs,input)::ys) stamp =
          mk_lines ml_ty_name lhs ty xs input stamp @
          mk_all_lines ys (if is_exn_type then stamp+length xs else stamp+1)
    val zs = mk_all_lines ys stamp
    val def_tm = list_mk_conj zs
    val def_tm = QCONV (REWRITE_CONV [rw_lemmas]) def_tm |> concl |> rand
    in def_tm end
  val size_def = snd (TypeBase.size_of (hd tys))
  fun right_list_dest f tm =
    let val (x,y) = f tm
    in (right_list_dest f y) @ [x] end handle HOL_ERR _ => [tm]
  fun build_measure [] = fail()
    | build_measure [ty] = let
        val x = fst (TypeBase.size_of ty)
        (* Check the number of fcp vars -- not sure if this works for more than one *)
        val count_fcp = (length o (filter fcpSyntax.is_numeric_type) o snd o dest_type) ty
        val xs = tl (tl (right_list_dest dest_fun_type (type_of x)))
        val s = (x |> dest_const |> fst)
        val s1 = foldr (fn (_,s) => s ^ " (K 0)") s xs
        val s2 = foldr (fn (_,s) => s ^ " o SND") " o FST" (List.drop (xs,count_fcp))
        in s1 ^ s2  end
    | build_measure (t1::t2::ts) = let
        val s1 = build_measure [t1]
        val s2 = build_measure (t2::ts)
        in "\\x. sum_CASE x ("^s1^") ("^s2^")" end
  val MEM_pat = MEM |> CONJUNCT2 |> SPEC_ALL |> concl |> rand |> rand
  val tac =
    (WF_REL_TAC [QUOTE ("measure (" ^ build_measure tys ^ ")")]
     \\ REPEAT STRIP_TAC
     (*TODO: \\ IMP_RES_TAC v_size_lemmas*)
     \\ TRY DECIDE_TAC
     \\ TRY (PAT_X_ASSUM MEM_pat (fn th =>
              ASSUME_TAC th THEN Induct_on [ANTIQUOTE (rand (rand (concl th)))]))
     \\ FULL_SIMP_TAC std_ss [MEM,FORALL_PROD,size_def] \\ REPEAT STRIP_TAC
     \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC)
(*
  Define [ANTIQUOTE def_tm]
*)
  val inv_def = if is_list_type then LIST_TYPE_def else
                if is_pair_type then PAIR_TYPE_def else
                if is_unit_type then UNIT_TYPE_def else
                 (tDefine name [ANTIQUOTE (get_def_tm ())] tac (*handle HOL_ERR _ =>
                  let
                    val d = Defn.mk_defn name (get_def_tm ())
                    val (def,ind) = Defn.tprove(d,tac)
                  in
                    def
                  end *))
  val clean_rule = CONV_RULE (DEPTH_CONV (fn tm =>
                   if not (is_abs tm) then NO_CONV tm else
                   if fst (dest_abs tm) ~~ tmp_v_var then ALPHA_CONV real_v_var tm
                   else NO_CONV tm))
  val inv_def = inv_def |> clean_rule
  val inv_def = CONV_RULE (DEPTH_CONV ETA_CONV) inv_def
  val inv_def = REWRITE_RULE [GSYM rw_lemmas] inv_def
  val _ = if is_list_type then inv_def else
          if is_pair_type then inv_def else
          if is_unit_type then inv_def else
            allowing_rebind save_thm(name ^ "_def[compute]",inv_def |> REWRITE_RULE [K_THM])
  val ind = fetch "-" (name ^ "_ind") |> clean_rule
            handle HOL_ERR _ => TypeBase.induction_of (hd tys) |> clean_rule
(*
  val inv_def = tDefine name [ANTIQUOTE def_tm] ALL_TAC
*)
  fun has_arg_with_type ty line =
    ((line |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rand |> type_of) = ty)
  val inv_defs = map (fn ty => (ty,LIST_CONJ (filter (has_arg_with_type ty)
                                     (CONJUNCTS inv_def)))) tys
  (* register the new type invariants *)
  fun sub lhs th = subst [(lhs |> repeat rator) |->
    (th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
        |> concl |> dest_eq |> fst |> repeat rator)] lhs
  val ys2 = map (fn ((_,th),(ml_ty_name,xs,ty,lhs,input)) =>
                   (ml_ty_name,xs,ty,sub lhs th,input)) (zip inv_defs ys)
  val _ = map reg_type ys2
  (* equality type and type rep *)
  val eq_lemmas = (map (fn ty => (ty, mk_EqualityType_thm is_exn_type ty
        |> simp_eq_lemma)) tys)
  val res = map (fn ((th,inv_def),(_,eq_lemma)) => (th,inv_def,eq_lemma))
                (zip inv_defs eq_lemmas)
  val type_rep_lemmas = filter (not o same_const T o concl o snd) eq_lemmas
      |> map fst |> define_type_reps |> map simp_eq_lemma
  in (name,res,type_rep_lemmas) end
  handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "define_ref_inv" e);

fun domain ty = ty |> dest_fun_type |> fst;
fun codomain ty = ty |> dest_fun_type |> snd;

val (FILTER_ASSUM_TAC : (term -> bool) -> tactic) = let
  fun sing f [x] = f x
    | sing f _ = raise ERR "sing" "Bind Error"
  fun add_assum (x,th) = UNDISCH (DISCH x th)
  fun f p (asl,w) =
    ([(filter p asl,w)], sing (fn th =>
           (foldr add_assum th (filter (not o p) asl))))
  in f end;

(*
val ty = ``:lit``; derive_thms_for_type false ty
val ty = ``:unit``; derive_thms_for_type false ty
val ty = ``:'a list``; derive_thms_for_type false ty
val ty = ``:'a # 'b``; derive_thms_for_type false ty
val ty = ``:num option``; derive_thms_for_type false ty
val ty = ``:'a + num``; derive_thms_for_type false ty
val is_exn_type = false;
val _ = Datatype `my_exn_type = MyExn | Chr | MyOtherExn | Bind | Subscript`
val ty = ``:my_exn_type``
val is_exn_type = true
val res = derive_thms_for_type is_exn_type ty
*)

fun avoid_v_subst ty = let
  val tyargs = (ty::find_mutrec_types ty) |> map type_vars |> List.concat |> map dest_vartype
  fun prime_v v =
    if exists (curry op = v) tyargs then
      prime_v (v^"w")
    else
      v
  in
    if exists (curry op = "'v") tyargs then
      [mk_vartype "'v" |-> mk_vartype(prime_v "'w")]
    else
      []
  end;

fun derive_thms_for_type is_exn_type ty = let

  val start = start_timing "derive_thms_for_type"
  val tsubst = avoid_v_subst ty;
  val ty = type_subst tsubst ty;
  val is_word_type = wordsSyntax.is_word_type ty
  val (_,tyargs) = dest_type ty
  val (ty_pre,ret_ty_pre) = dest_fun_type (type_subst tsubst (type_of_cases_const ty))
  val (_,gen_tyargs) = dest_type ty_pre
  fun inst_fcp_types_rec (x::xs) (y::ys) ty =
    if is_vartype y andalso fcpSyntax.is_numeric_type x andalso fcpSyntax.dest_int_numeric_type x > 1
    then
      type_subst [y|->x] (inst_fcp_types_rec xs ys ty)
    else
      inst_fcp_types_rec xs ys ty
  |   inst_fcp_types_rec _ _ ty = ty
  (* Do not generalize fcp types *)
  val inst_fcp_types = inst_fcp_types_rec tyargs gen_tyargs
  val ty = inst_fcp_types ty_pre
  val ret_ty = inst_fcp_types ret_ty_pre
  val is_record = 0 < length(TypeBase.fields_of ty)
  val tys_pre = find_mutrec_types ty |> map (type_subst tsubst)
  val tys = map inst_fcp_types tys_pre
  val is_pair_type = tys_is_pair_type tys
  val is_list_type = tys_is_list_type tys
  val is_unit_type = tys_is_unit_type tys
  val is_order_type = tys_is_order_type tys
  val _ = map (fn ty => print ("Adding type " ^ type_to_string ty ^ "\n")) tys
  (* look up case theorems *)
  val case_thms = map (fn ty => (ty, get_nchotomy_of ty)) tys
  (* define coupling invariant for data refinement and prove EqualityType lemmas *)
  val (name,inv_defs,tr_lemmas) = define_ref_inv is_exn_type tys
  val _ = map (fn (_,inv_def,_) => print_inv_def inv_def) inv_defs
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  (* define a CakeML datatype declaration *)
  val (dtype,dtype_list) =
    if name = "UNIT_TYPE" then
      (Dtabbrev (mlstringSyntax.mk_mlstring "unit")
         (mk_Attup(listSyntax.mk_list([],astSyntax.ast_t_ty))),
       listSyntax.mk_nil(alpha)) else
    if name = "PAIR_TYPE" then (Dtype [],listSyntax.mk_nil(alpha)) else let
(*
val th = inv_defs |> map #2 |> hd
*)
    fun extract_dtype_part th = let
      val xs = CONJUNCTS th |> map (dest_eq o concl o SPEC_ALL)
      val ys = xs |>  map (fn (x,y) => (x |> rator |> rand,
                                        y |> list_dest dest_exists |> last
                                          |> list_dest dest_conj |> hd
                                          |> rand |> rator |> rand |> rand))
      (* TODO: assumes single level module only *)
      val tyname =
        if is_order_type then order_tyname else
        if is_unit_type then unit_tyname else
          ys |> hd |> fst |> type_of |> type2t |> rand
             |> repeat (snd o dest_Long) |> rand
      val ys = map (fn (x,y) => (if is_exn_type then y |> rand  |> rand
                                 else y |> rator |> rand,
                                 x |> dest_args |> map (type2t o type_of))) ys
      fun mk_line (x,y) = pairSyntax.mk_pair(x,
                           listSyntax.mk_list(y,astSyntax.ast_t_ty))
      val lines = listSyntax.mk_list(map mk_line ys,
                                     pairSyntax.mk_prod(mlstringSyntax.mlstring_ty,
                                                        listSyntax.mk_list_type(astSyntax.ast_t_ty)))
      fun string_tl s = s |> explode |> tl |> implode
      val ts = th |> concl |> list_dest dest_conj |> hd
                  |> list_dest dest_forall |> last |> dest_eq |> fst
                  |> rator |> rand |> type_of |> dest_type |> snd
                  |> filter (not o fcpSyntax.is_numeric_type)
                  |> map (mlstringSyntax.mk_mlstring o (* string_tl o *) dest_vartype)
      val ts_tm = listSyntax.mk_list(ts,mlstringSyntax.mlstring_ty)
      val dtype = pairSyntax.list_mk_pair[ts_tm,tyname,lines]
      in dtype end
    val dtype_parts = inv_defs |> map #2 |> map extract_dtype_part
    val dtype_list = listSyntax.mk_list(dtype_parts,type_of (hd dtype_parts))
    in (astSyntax.mk_Dtype (unknown_loc,dtype_list),dtype_list) end
  fun is_prim_Dexn tm =
    is_primitive_exception (tm |> rator |> rand |> mlstringSyntax.dest_mlstring)
  val dexn_list = if not is_exn_type then []
                  else dtype |> rand |> rator |> rand |> rand |> rand
                             |> listSyntax.dest_list |> fst
                             |> map pairSyntax.dest_pair
                             |> map (fn (x,y) => astSyntax.mk_Dexn (unknown_loc,x,y))
                             |> filter (not o is_prim_Dexn)
  (* cons assumption *)
  fun mk_assum tm =
    if not is_exn_type then let
      val x = find_term is_TypeStamp (rhs tm)
      val (n,k) = dest_TypeStamp x
      val l = tm |> dest_eq |> fst |> rator |> rand |> list_dest dest_comb
                 |> tl |> length |> numSyntax.term_of_int
      val ctor = tm |> dest_eq |> fst |> rator |> rand |> repeat rator
      val cv = mk_var (enter_cons_name (ctor, n), ml_str_id_ty)
      in mk_eq(mk_lookup_cons(cv, env_tm),
               optionSyntax.mk_some(mk_pair(l,x))) end
    else let
      val x = find_term is_ExnStamp tm
      val n = dest_ExnStamp x
      val l = tm |> dest_eq |> fst |> rator |> rand |> list_dest dest_comb
                 |> tl |> length |> numSyntax.term_of_int
      val ctor = tm |> dest_eq |> fst |> rator |> rand |> repeat rator
      val cv = mk_var (enter_cons_name (ctor, rand n), ml_str_id_ty)
      in mk_eq(mk_lookup_cons(cv, env_tm),
               optionSyntax.mk_some(mk_pair(l,mk_ExnStamp (rand (rator n))))) end
  handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "mk_assum" e)

  val type_assum = if name = "PAIR_TYPE" orelse name = "UNIT_TYPE" then T
      else inv_defs |> map (fn (_,x,_) => CONJUNCTS x) |> Lib.flatten
               |> map (concl o SPEC_ALL)
               |> map mk_assum |> list_mk_conj
(*
  val ((ty,case_th),(_,inv_def,eq_lemma)) = hd (zip case_thms inv_defs)
  val inv_lhs = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                        |> concl |> dest_eq |> fst
  val x = inv_lhs |> rator |> rand
  val input = mk_var("input",type_of x)
  val inv_lhs = subst [x|->input] inv_lhs
*)
  (* prove lemma for case_of *)
  fun prove_case_of_lemma (ty,case_th,inv_lhs,inv_def) = let
    val start = start_timing ("prove_case_of_lemma for "
        ^ Parse.type_to_string ty)
    val cases_th = TypeBase.case_def_of ty |> INST_TYPE tsubst
    val (x1,x2) = cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
                           |> dest_eq
    val case_const = x1 |> repeat rator
    val ty1 = case_const |> type_of |> domain
    val ty2 = x2 |> type_of
    val cases_th = INST_TYPE [ty2 |-> mk_vartype "'return_type"] cases_th
                   |> INST_TYPE (match_type ty1 ty)
    fun replace_match_exp f tm = let
      val (x,y) = dest_comb tm
      in if is_const x then mk_comb(x,f y) else mk_comb(replace_match_exp f x,y) end
    val cases_tm =
      cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
               |> dest_eq |> fst |> replace_match_exp (fn tm => mk_arb (type_of tm))
    fun rename [] = []
      | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                         in (x,mk_var(k,type_of x)) :: rename xs end
    val vs = rev (rename (free_vars cases_tm))
    val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
    val exp = cases_tm |> replace_match_exp (fn tm => mk_var ("x",type_of tm))
    val input_var = filter (fn x => not (tmem x (free_vars cases_tm))) (free_vars exp) |> hd
    val ret_ty = type_of exp
    val xs = rev (map rand (find_terms is_eq (concl case_th)))
    fun add_nums [] = []
      | add_nums (x::xs) = (x,length xs+1) :: add_nums xs
    val ys = rev (add_nums (rev (zip (map snd vs) xs)))
    fun str_tl s = implode (tl (explode s))
    fun list_app x [] = x
      | list_app x (y::ys) = list_app (mk_comb(x,y)) ys
    val start_mk_vars = start_timing "mk_vars"
    fun mk_vars ((f,tm),n) = let
      val xs = rev (free_vars tm)
      val fxs = list_app f xs
      val pxs = list_app (mk_var("b" ^ int_to_string n,list_mk_type xs bool)) xs
      val xs = map (fn x => let val s = str_tl (fst (dest_var x)) in
                            (x,mk_var("n" ^ s,mlstringSyntax.mlstring_ty),
                               mk_var("v" ^ s,v_ty)) end) xs
      val exp = mk_var("exp" ^ int_to_string n, astSyntax.exp_ty)
      in (n,f,fxs,pxs,tm,exp,xs) end
    val ts = map mk_vars ys
    val _ = end_timing start_mk_vars
    (* patterns *)
(*
val (n,f,fxs,pxs,tm,exp,xs) = el 1 ts
*)
    val Mat_cases = Mat_cases_def |> SPEC_ALL |> concl |> rand
                    |> dest_eq |> fst |> repeat rator
    val patterns =
      if name = "PAIR_TYPE" orelse name = "UNIT_TYPE" then let
        val (n,f,fxs,pxs,tm,exp,xs) = hd ts
        val (inl,x) = Mat_cases_def |> SPEC_ALL |> concl |> dest_conj |> fst
                                    |> rator |> rand |> rand |> dest_comb
        val vars = listSyntax.mk_list(map (fn (x,n,v) => n) xs,mlstringSyntax.mlstring_ty)
        in mk_comb(Mat_cases,mk_comb(inl,mk_pair(vars,exp))) end
      else (* not pair or unit *) let
        val stamps = type_assum |> list_dest dest_conj |> map dest_eq
        fun get_stamp str =
          snd (first (fn (tm,_) => can (find_term (aconv str)) tm) stamps)
          |> rand |> rand
        val patterns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
          (*
          val cons_name = (repeat rator tm |> dest_const |> fst)
          val str = if is_exn_type andalso is_primitive_exception cons_name
                    then cons_name
                    else tag_name name cons_name
          val str = stringSyntax.fromMLstring str
          *)
          val cons_name = repeat rator tm
          val kv = mk_var (mk_cons_name cons_name, ml_str_id_ty)
          val vars = listSyntax.mk_list(map (fn (x,n,v) => n) xs,mlstringSyntax.mlstring_ty)
          in list_mk_pair([kv,vars,exp,get_stamp kv]) end) ts
        val (inr,x) = Mat_cases_def |> SPEC_ALL |> concl |> rand
                                    |> rator |> rand |> rand |> dest_comb
        val xty = type_of x |> dest_type |> snd |> hd
        in mk_comb(Mat_cases,mk_comb(inr,listSyntax.mk_list(patterns,xty))) end
    val ret_inv = get_type_inv ret_ty
    val exp_var = mk_var("exp", astSyntax.exp_ty)
    val result = mk_Eval(env_tm,
                         astSyntax.mk_Mat(exp_var, patterns),
                         mk_comb(ret_inv,exp))
    (* assums *)
    val vs = map (fn (n,f,fxs,pxs,tm,exp,xs) => map (fn (x,_,_) => x) xs) ts |> flatten
    val b0 = mk_var("b0",bool)
    val tm = b0::map (fn (n,f,fxs,pxs,tm,exp,xs) => mk_imp(mk_CONTAINER(mk_eq(input_var,tm)),pxs)) ts
             |> list_mk_conj
    val tm = list_mk_forall(vs,tm)
    val result = mk_imp(mk_TAG (oneSyntax.one_tm, tm),result)
    (* tags *)
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    fun mk_hyp (n,f,fxs,pxs,tm,exp,xs) = let
      val env = foldr (fn ((x,n,v),y) => mk_write(n,v,y)) env_tm (rev xs)
      val tm = map (fn (x,n,v) => mk_comb(find_inv x,v)) xs @ [pxs]
      val tm = if List.null tm then T else list_mk_conj tm
      val tm = mk_imp(tm,mk_Eval (env, exp, mk_comb(ret_inv,fxs)))
      val vs = map (fn (x,_,_) => x) xs @ map (fn (_,_,v) => v) xs
      val tm = list_mk_forall(vs,tm)
      val n = numSyntax.term_of_int n
      val tm = mk_TAG(n,tm)
      in tm end;
    (* all_distincts *)
    fun mk_alld (n,f,fxs,pxs,tm,exp,xs) = let
      val tt = listSyntax.mk_list(map (fn (_,x,_) => x) xs,mlstringSyntax.mlstring_ty)
      val tt = listSyntax.mk_all_distinct tt
      in tt end
    val tt = list_mk_conj(map mk_alld ts) handle HOL_ERR _ => T
    (* goal *)
    val hyps = map mk_hyp ts
    val x = mk_comb(rator (rator inv_lhs),input_var)
    val ev = mk_Eval(env_tm,exp_var,x)
    val hyp0 = mk_TAG(numSyntax.zero_tm, mk_imp(b0, ev))
    val hyps = list_mk_conj(hyp0::hyps)
    val goal = mk_imp(type_assum,mk_imp(tt,mk_imp(hyps,result)))
    val Mat_lemma = ISPEC (rator x) IMP_Eval_Mat_cases |> SPEC input_var
    val is_simple_case = name = "PAIR_TYPE" orelse name = "UNIT_TYPE"
(*
  set_goal([],goal)
*)
    val case_lemma = auto_prove "case-of-proof" (goal,
      rpt strip_tac
      \\ match_mp_tac Mat_lemma
      \\ conj_tac THEN1
       (pop_assum mp_tac
        \\ PAT_X_ASSUM hyp0 mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp_tac std_ss [TAG_def])
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
      \\ simp_tac std_ss [mlstringTheory.mlstring_11,v_11,MEM,stamp_11,CONS_11,ZIP,write_list_def,
           stringTheory.CHR_11,LENGTH,NOT_NIL_CONS,NOT_CONS_NIL,PULL_EXISTS]
      \\ simp_tac (srw_ss()) [cases_th]
      \\ rpt (pop_assum mp_tac) \\ rewrite_tac [TAG_def,CONTAINER_def]
      \\ rpt strip_tac
      \\ first_x_assum match_mp_tac \\ fs [])
    val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def,Mat_cases_def,MAP]
                       |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
    val _ = end_timing start
    in (case_lemma,ts) end
    handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "prove_case_of_lemma" e);
(*
val (n,f,fxs,pxs,tm,exp,xs) = hd ts
val (n,f,fxs,pxs,tm,exp,xs) = el 2 ts
*)
  (* prove lemmas for constructors *)

  val ps_ty = Eval_Con_NONE |> SPEC_ALL
                            |> concl |> rand |> rator |> rand |> rand
                            |> rand |> type_of |> dest_type |> snd |> hd
  fun derive_cons ty inv_lhs inv_def (n,f,fxs,pxs,tm,exp,xs) = let
    val pat = tm
    fun str_tl s = implode (tl (explode s))
    val exps = map (fn (x,_,_) => (x,mk_var("exp" ^ str_tl (fst (dest_var x)), astSyntax.exp_ty))) xs
    val tag =
      if is_pair tm then
        "prod"
      else if oneSyntax.is_one tm then
        "()"
      else
        inv_def
        |> CONJUNCTS |> map (concl o SPEC_ALL)
        |> first (can (match_term tm) o rand o rator o fst o dest_eq)
        |> dest_eq |> fst |> rator |> rand |> repeat rator
        |> mk_cons_name
    val str =
      (tag |> lookup_cons_name |> fst
       handle HOL_ERR _ => stringLib.fromMLstring tag)
    val exps_tm = listSyntax.mk_list(map snd exps,astSyntax.exp_ty)
    val inv = inv_lhs |> rator |> rator
    val cv = mk_var (tag, ml_str_id_ty)
    val the_tag_name =
      if name = "PAIR_TYPE" then
        optionSyntax.mk_none(astSyntax.ml_str_id_ty)
      else if name = "UNIT_TYPE" then
        optionSyntax.mk_none(astSyntax.ml_str_id_ty)
      else
        optionSyntax.mk_some(cv)
      (* else optionSyntax.mk_some(full_id str) *)
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    val ps = listSyntax.mk_list(
               map (fn (x,exp) => mk_pair(find_inv x, exp)) exps,ps_ty)
    val result = mk_Eval(env_tm,
                         astSyntax.mk_Con(the_tag_name, exps_tm),
                         mk_comb(inv,tm))
    val tms = map (fn (x,exp) => mk_Eval(env_tm,
                                         exp,
                                         find_inv x)) exps
    val tm = if List.null tms then T else list_mk_conj tms
    val cons_assum = type_assum
                     |> list_dest dest_conj
                     |> filter (fn tm => aconv
                           (tm |> rator |> rand |> rator |> rand) cv)
                     |> list_mk_conj
                     handle HOL_ERR _ => T
    val goal = mk_imp(cons_assum,mk_imp(tm,result))
    val lenxs = length xs
    val Eval_Con_lemma = (if name = "PAIR_TYPE" orelse name = "UNIT_TYPE"
                          then Eval_Con_NONE else Eval_Con)
                         |> SPEC ps |> REWRITE_RULE [MAP,SND]
    (* set_goal([],goal) *)
    val lemma = auto_prove "Eval_Con" (goal,
      rpt strip_tac \\ match_mp_tac Eval_Con_lemma
      \\ asm_simp_tac std_ss [LENGTH]
      \\ conj_tac THEN1 asm_simp_tac std_ss [EVERY_DEF]
      \\ simp [PULL_EXISTS]
      \\ simp_tac std_ss [inv_def] \\ simp [])
    in (pat,lemma) end
    handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "derive_cons" e);
(*
  val ((ty,case_th),(_,inv_def,eq_lemma)) = hd (zip case_thms inv_defs)
*)
  (* call the two functions above for each type *)
  fun make_calls ((ty,case_th),(_,inv_def,eq_lemma)) = let
    val inv_lhs = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                          |> concl |> dest_eq |> fst
    val x = inv_lhs |> rator |> rand
    val input = mk_var("input",type_of x)
    val inv_lhs = subst [x|->input] inv_lhs
    val (case_lemma,ts) = prove_case_of_lemma (ty,case_th,inv_lhs,inv_def)
    val conses = print_time "conses" (map (derive_cons ty inv_lhs inv_def)) ts
    in (ty,eq_lemma,inv_def,conses,case_lemma,ts) end

  val res = map make_calls (zip case_thms inv_defs)
(*
  val dexn = hd dexn_list
*)
  val (rws1,rws2) = if not is_record then ([],[])
                    else derive_record_specific_thms (hd tys)
  val dprog =
    let
      val decs =
        (if mem name ["LIST_TYPE","PAIR_TYPE"] then []
         else if is_exn_type then dexn_list
         else [dtype])
    in
      listSyntax.mk_list(decs,dec_ty)
    end

  (* register type to belong to current module if all went well *)
  val name = ty |> full_name_of_type
  val add_str = "Adding type " ^ type_to_string ty
  val comma = concat o commafy
  val _ = case get_curr_modules () of
      [] => print (add_str ^ ".\n")
    | [m] => print (add_str ^ " to module " ^ m ^ ".\n")
    | ms => print (add_str ^ " to nested modules [" ^ comma ms ^ "].\n")
  val _ = enter_type_mod name
  val _ = end_timing start

  in (rws1,rws2,res,tr_lemmas,dprog) end
  handle (e as HOL_ERR _) =>
  raise wrap_exn "ml_translatorLib" "derive_thms_for_type" e;

local
  val translator = ref (fn th => I (th:thm))
  fun do_translate th = (!translator) th
  fun store_dprog abstract_mode dprog =
    (* if abstract_mode then add_deferred_dprog dprog else *)
    ml_prog_update (add_prog dprog I)
  fun add_type abstract_mode ty = let
    val start = start_timing ("adding type " ^ Parse.type_to_string ty)
    val fcps = ((filter fcpSyntax.is_numeric_type) o snd o dest_type) ty
    val (rws1,rws2,res,tr_lemmas,dprog) = derive_thms_for_type false ty
    val (rws1,rws2) =
      if length fcps > 0 then
        let val insts = INST_TYPE [alpha|-> hd fcps,beta |-> hd fcps] in
          (map insts rws1,map insts rws2)
        end
      else (rws1,rws2)
    val _ = store_dprog abstract_mode dprog
    val _ = add_type_thms (rws1,rws2,res,tr_lemmas)
    val _ = map do_translate rws1
    val _ = end_timing start
    in res end
    handle (e as HOL_ERR _) =>
    raise wrap_exn "ml_translatorLib" "add_type" e
  fun lookup_add_type abstract_mode ty =
    lookup_type_thms ty handle HOL_ERR _ => (add_type abstract_mode ty; lookup_type_thms ty)
  fun conses_of ty = let
    val (ty,inv_def,conses,case_lemma) = lookup_type_thms ty
    in conses end
in
  fun set_translator t = (translator := t)
  fun register_type_main abstract_mode ty =
    (lookup_add_type abstract_mode ty; ())
    handle UnsupportedType ty1 =>
      (register_type_main abstract_mode ty1;
       register_type_main abstract_mode ty)
  val register_type = allowing_rebind (register_type_main false)
  val abs_register_type = allowing_rebind (register_type_main true)
  fun cons_for tm = let
    val ty = type_of tm
    val conses = conses_of ty
    val (pat,th) = first (fn (x,th) => can (match_term x) tm) conses
    val i = snd (match_term pat tm)
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in INST ss (INST_TYPE i th) end
    handle HOL_ERR _ => raise (ERR "cons_for" "Not a constructor for a registered type.")
  fun case_of ty = let
    val (ty,inv_def,conses,case_lemma) = lookup_type_thms ty
    in (case_lemma) end
  fun store_eq_thm th = (add_eq_lemma th; th)
  fun register_exn_type_main abstract_mode ty = let
    val start = start_timing ("adding exn type " ^ Parse.type_to_string ty)
    val (rws1,rws2,res,tr_lemmas,dprog) = derive_thms_for_type true ty
    val _ = store_dprog abstract_mode dprog
    val _ = do_timing "add_type_thms" add_type_thms (rws1,rws2,res,tr_lemmas)
    val _ = do_timing "map do_translate rws1" (map do_translate) rws1
    val _ = end_timing start
    in () end
  val register_exn_type = register_exn_type_main false
  val abs_register_exn_type = register_exn_type_main true
end

fun register_term_types register_type tm = let
  fun every_term f tm =
    ((if is_abs tm then every_term f (snd (dest_abs tm))
      else if is_comb tm then (every_term f (rand tm); every_term f (rator tm))
      else ()); f tm)
  val special_types = [numSyntax.num,intSyntax.int_ty,bool,stringSyntax.char_ty,
                       mlstringSyntax.mlstring_ty,mk_vector_type alpha,
                       wordsSyntax.mk_word_type alpha, float64_ty]
                      @ get_user_supplied_types ()
  fun ignore_type ty =
    if can (first (fn ty1 => can (match_type ty1) ty)) special_types then true else
    if not (can dest_type ty) then true else
    if can (dest_fun_type) ty then true else
    if fcpSyntax.is_numeric_type ty andalso fcpSyntax.dest_int_numeric_type ty > 1 then true else false
  fun typeops ty = let
    val (tname,targs) = dest_type ty
    in ty :: flatten (map typeops targs) end
    handle HOL_ERR _ => []
  fun register_term_type tm = let
    val tys = typeops (type_of tm) |> filter (not o ignore_type)
    val _ = map register_type tys
    in () end
  in every_term register_term_type tm end;

(* tests:
register_type ``:'a list``;
register_type ``:'a # 'b``;
register_type ``:'a + num``;
register_type ``:num option``;
register_type ``:unit``;
*)

fun inst_cons_thm tm hol2deep = let
  val th = cons_for tm |> UNDISCH
  val res = th |> UNDISCH_ALL |> concl |> rand |> rand
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val xs = args res
  val ss = fst (match_term res tm)
  val ys = map (fn x => remove_primes (hol2deep (subst ss x))) xs
  val ys =
    let
      val refs = th |> concl |> dest_imp |> fst |> list_dest dest_conj |> map rand
      fun insert_HOL_STRING (y,r) =
        if can (match_term r) (rand (concl y)) then y else
          let val res = MATCH_MP Eval_HOL_STRING_INTRO y
              val _ = print "Warning: automatically added string IMPLODE "
              val _ = print "due to HOL_STRING_TYPE\n"
          in res end
    in map insert_HOL_STRING (zip ys refs) end handle HOL_ERR _ => ys
  val th1 = if length ys = 0 then TRUTH else LIST_CONJ ys
  in MATCH_MP th (UNDISCH_ALL th1)
     handle HOL_ERR _ =>
       if use_hol_string_type () andalso stringSyntax.is_string tm
       then raise failwith "string cons"
       else raise UnableToTranslate tm end

val inst_case_thm_for_fail = ref T;
val tm = !inst_case_thm_for_fail

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = case_of ((repeat rator tm) |> type_of |> domain) |> UNDISCH
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  fun rename_var prefix ty v =
    mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
  val ts = find_terms (can (match_term (mk_CONTAINER (mk_var("b", bool))))) (concl th)
           |> map (rand o rand)
           |> map (fn tm => (tm,map (fn x => (x,rename_var "n" mlstringSyntax.mlstring_ty x,
                                                rename_var "v" v_ty x))
                    (dest_args tm handle HOL_ERR _ => [])))
  val ns = map (fn (tm,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> flatten
  val ms = map (fn (b,(x,n,v)) => n |-> mlstringSyntax.mk_mlstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns
  fun rename_bound_conv tm = let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
    val new_s = snd (first (fn (z,_) => z = s) ks)
    in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = MP th TRUTH
  in th end handle (e as HOL_ERR _) => (inst_case_thm_for_fail := tm; raise e);

val last_fail = ref T;
(*
  val tm = !last_fail
  val tm = hyps
  val tm = y
*)

fun inst_case_thm tm hol2deep = let
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = y |> rand |> rand
    val lemma = hol2deep z
    val lemma = D lemma
    val new_env = y |> rator |> rator |> rand
    val lemma = INST [env_tm|->new_env] lemma
                |> PURE_REWRITE_RULE [lookup_cons_write]
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP,
                 lookup_var_write] THENC
             DEPTH_CONV (mlstring_EQ_CONV) THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = List.take(vs, length vs div 2)
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma |> remove_primes end
      handle (e as HOL_ERR _) => (print_term tm; last_fail := tm; raise e)
           | UnableToTranslate t => (last_fail := tm; raise UnableToTranslate t)
  fun sat_hyps tm = if is_conj tm then let
    val (x,y) = dest_conj tm
    in CONJ (sat_hyps x) (sat_hyps y) end else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  val th = th |> UNDISCH_ALL
  in th end;

fun SIMP_EqualityType_ASSUMS th = let
  val lemmas = eq_lemmas () |> map (UNDISCH_ALL o RW [GSYM AND_IMP_INTRO])
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val xs = map (fn th => (concl th,th)) lemmas
  fun find_match [] tm = fail()
    | find_match ((pat,th1)::xs) tm = let
        val (ss,i) = match_term pat tm
        in INST ss (INST_TYPE i th1) end
        handle HOL_ERR _ => find_match xs tm
  fun remove_one th = let
    val hs = hyp th
    val tm = first (can (find_match xs)) hs
    val lemma = find_match xs tm
    val th = MP (DISCH tm th) lemma
    in remove_one th end handle HOL_ERR _ => th
  in remove_one th end;

(* PMATCH translation *)

val () = computeLib.add_funs [pat_bindings_def]

local
  val pat = get_term "PMATCH_ROW"
  fun K_T_CONV tm =
    if not (can (match_term pat) tm) then NO_CONV tm else
    if aconv (snd (dest_pabs (rand tm))) T then let
      val t = combinSyntax.mk_K(T,fst (dest_pabs (rand tm))) |> rator
      val goal = mk_eq(rand tm,t)
      val lemma = auto_prove "PMATCH_ROW_K_T_INTRO_CONV" (goal,fs [FUN_EQ_THM,FORALL_PROD])
      in (RAND_CONV (fn tm => lemma)) tm end
    else NO_CONV tm
in
  val PMATCH_ROW_K_T_INTRO_CONV = DEPTH_CONV K_T_CONV
end;

local
  val pmatch_pat = get_term "PMATCH"
  val pmatch_row_pat = get_term "PMATCH_ROW_T"
in
  fun dest_pmatch_row_K_T tm =
    if can (match_term pmatch_row_pat) tm then let
      val (ixy,z) = dest_comb tm
      val (ix,y) = dest_comb ixy
      val (i,x) = dest_comb ix
      in (x,z) end
    else failwith "not a PMATCH_ROW with K T"
  fun dest_pmatch_K_T tm =
    if can (match_term pmatch_pat) tm then let
      val (xy,z) = dest_comb tm
      val (x,y) = dest_comb xy
      in (y,map dest_pmatch_row_K_T (fst (listSyntax.dest_list z))) end
    else failwith "not a PMATCH"
  val is_pmatch = can (match_term pmatch_pat)
end

val lookup_cons_pat = get_term "lookup_cons eq"
val prove_EvalPatRel_fail = ref T;
val goal = !prove_EvalPatRel_fail;

fun prove_EvalPatRel goal hol2deep = let
  val asms =
    goal |> rand |> dest_pabs |> snd |> hol2deep |> hyp
         |> filter (can (match_term lookup_cons_pat))
  val pat = get_term "not eq"
  fun badtype ty = Lib.mem ty [listSyntax.mk_list_type alpha,numSyntax.num, mlstringSyntax.mlstring_ty]
  fun tac (hs,gg) = let
    val find_neg = find_term (fn tm => can (match_term pat) tm andalso
                                       not(badtype(type_of(boolSyntax.rhs(dest_neg tm)))))
    val tm = find_neg (first (can find_neg) hs)
    in (primCases_on (tm |> rand |> rand) \\ fs []) (hs,gg) end
  fun tac2 (asms,concl) =
    (let
        val pmatch_asm = can (match_term (get_term "pmatch_eq_Match_type_error"))
        val v = List.find pmatch_asm asms |> valOf |> lhs |> rator |> rand
        val asm = List.find
                      (fn asm =>
                          (asm |> free_vars |> List.exists (term_eq v))
                          andalso
                          not(is_eq asm)
                      )
                      asms |> valOf
        val vname = asm |> rator |> rand |> dest_var |> fst
        val {Name,Thy,Ty} = asm |> strip_comb |> fst |> dest_thy_const
        val thm = fetch Thy (Name^"_def")
    in
        Cases_on [QUOTE vname]
                 >> rfs [thm]
                 >> rfs []
                 >> rfs [pmatch_def,same_ctor_def,id_to_n_def]
    end (asms,concl)) handle Option.Option =>
    raise(ERR "tac2" "No matching assumption found")
  (*
    set_goal(asms,goal)
  *)
  val th = auto_prove_asms "prove_EvalPatRel" ((asms,goal),
    simp[EvalPatRel_def,EXISTS_PROD] >>
    SRW_TAC [] [] \\ fs [] >>
    POP_ASSUM MP_TAC >>
    REPEAT tac
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
    \\ REPEAT STRIP_TAC \\ fs [] >>
    fs[Once evaluate_def] >>
    fs[(*lookup_cons_thm*) lookup_cons_def] >>
    simp[LIST_TYPE_def,pmatch_def,same_type_def,
         same_ctor_def,id_to_n_def,EXISTS_PROD,
         pat_bindings_def,lit_same_type_def] >>
    fs[Once evaluate_def] >>
    rw[] >> simp[Once evaluate_def] >>
    fs [build_conv_def,do_con_check_def] >>
    fs[LIST_TYPE_def,pmatch_def,same_type_def,
         same_ctor_def,id_to_n_def,EXISTS_PROD,
         pat_bindings_def,lit_same_type_def] >>
    fs [Once evaluate_def] >> every_case_tac >>
    rpt (CHANGED_TAC
          (rpt (CHANGED_TAC
                 (every_case_tac >> TRY(fs[] >> NO_TAC) >> tac2)) >>
                  fs [same_type_def,CaseEq"match_result",pmatch_def,
                      lit_same_type_def,CaseEq"bool",INT_def,NUM_def,CHAR_def,STRING_TYPE_def,explode_eq,eq_explode] >>
                  rpt var_eq_tac)))
  in th end handle HOL_ERR e =>
  (prove_EvalPatRel_fail := goal;
   failwith "prove_EvalPatRel failed");

val prove_EvalPatBind_fail = ref T;
val goal = !prove_EvalPatBind_fail;

fun prove_EvalPatBind goal hol2deep = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> rand |> rand |> rator
                      |> dest_pabs
  val res = hol2deep rhs_tm
  val exp = res |> concl |> rator |> rand
  val th = D res
  val var_assum = get_term "Eval Var"
  val is_var_assum = can (match_term var_assum)
  val vs = find_terms is_var_assum (concl th |> rator)
  val vs' = filter (is_var o rand o rand) vs
  fun delete_var tm =
    if tmem tm vs' then MATCH_MP IMP_EQ_T (ASSUME tm) else NO_CONV tm
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV delete_var)) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val ws = free_vars vars
  val vs = filter (fn tm => not (tmem (rand (rand tm)) ws)) vs' |> op_mk_set aconv
  val new_goal = goal |> subst [mk_var("e",astSyntax.exp_ty)|->exp,p2 |-> p]
  val new_goal = foldr mk_imp new_goal vs
  val OPTION_TYPE_SIMP = let
    val OPTION_TYPE = get_type_inv (type_of (optionSyntax.mk_none alpha)) |> rator
    val goal = get_term "OPTION_TYPE_SIMP" |> ASSUME |> ISPEC OPTION_TYPE |> concl
    val OPTION_TYPE_SIMP = auto_prove "OPTION_TYPE_SIMP" (goal,
      Cases \\ fs [CONTAINER_def,FUN_EQ_THM] \\ EVAL_TAC \\ simp [])
      |> Q.SPECL [`x`] |> SIMP_RULE std_ss [] |> GSYM
    in OPTION_TYPE_SIMP end handle HOL_ERR _ => TRUTH
  fun tac (asms,goal) = let
    fun is_TYPE tm = let
      val (args,ret) = strip_fun(type_of tm)
    in not(null args) andalso ret = type_of T andalso last args = v_ty end
    fun types tm = let
      val (rator,rands) = strip_comb tm
    in
      if is_TYPE rator then
          rator :: List.concat(map types rands)
      else []
    end
    val relevant_asms = List.filter (is_TYPE o fst o strip_comb) asms
    val consts = map types relevant_asms |> List.concat |> filter is_const |> map dest_thy_const
    val thms = map (fn {Name,Thy,Ty} => [fetch Thy (Name^"_def")] handle _ => []) consts |> List.concat
  in
    REPEAT (POP_ASSUM MP_TAC)
    \\ NTAC (length vs) STRIP_TAC
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
    \\ REWRITE_TAC [GSYM PAIR_TYPE_SIMP, GSYM LIST_TYPE_SIMP, GSYM OPTION_TYPE_SIMP]
    \\ Ho_Rewrite.REWRITE_TAC [GSYM LIST_TYPE_SIMP']
    \\ REWRITE_TAC ([GSYM PAIR_TYPE_SIMP, GSYM LIST_TYPE_SIMP, GSYM OPTION_TYPE_SIMP]
                      |> map (REWRITE_RULE [CONTAINER_def]))
    \\ Ho_Rewrite.REWRITE_TAC ([GSYM LIST_TYPE_SIMP'] |> map (REWRITE_RULE [CONTAINER_def]))
    \\ fsrw_tac[]([Pmatch_def,PMATCH_option_case_rwt,LIST_TYPE_def,PAIR_TYPE_def]@thms)
    \\ TRY STRIP_TAC \\ fsrw_tac[][] \\ rev_full_simp_tac(srw_ss())[]
    \\ fsrw_tac[]([Pmatch_def,PMATCH_option_case_rwt,LIST_TYPE_def,PAIR_TYPE_def]@thms)
  end (asms,goal)
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) (eq_lemmas())
  fun tac2 (asms,concl) = (asms,concl) |>
    (if is_PRECONDITION concl then
      METIS_TAC []
    else if is_EqualityType concl then
      ACCEPT_TAC (find_equality_type_thm (rand concl))
    else if can(match_term (get_term "PreImp_Eval")) concl then
      METIS_TAC [CONTAINER_def]
    else ALL_TAC)
  fun tac3 (asms,concl) = (asms,concl) |>
    (if is_exists concl andalso
        can (match_term (get_term "evaluate_pat")) (snd(dest_abs(rand concl)))
     then
       fs[Once evaluate_def,Once Eval_def,INT_def]
       >> EVAL_TAC
     else ALL_TAC)
  (*
    set_goal([],new_goal)
  *)
  val th = auto_prove "prove_EvalPatBind" (new_goal,
    NTAC (length vs) STRIP_TAC \\ STRIP_TAC
    \\ full_simp_tac std_ss [FORALL_PROD] \\ REPEAT STRIP_TAC
    \\ (MATCH_MP_TAC (D res) ORELSE
        MATCH_MP_TAC (D(res |> SIMP_RULE (std_ss) [FORALL_PROD])))
    \\ fsrw_tac[][]
    \\ fsrw_tac[][EvalPatBind_def,Pmatch_def]
    \\ tac
    \\ BasicProvers.EVERY_CASE_TAC \\ fsrw_tac[][]
    \\ rpt(CHANGED_TAC(SRW_TAC [] [Eval_Var_SIMP,
             lookup_cons_write,lookup_var_write]))
    \\ TRY (first_x_assum match_mp_tac >> METIS_TAC[])
    \\ TRY tac3
    \\ fsrw_tac[][GSYM FORALL_PROD,(*lookup_var_id_def,*)lookup_cons_def,LIST_TYPE_IF_ELIM]
    \\ TRY tac2 \\ TRY (fs[CONTAINER_def] >> NO_TAC)
    \\ TRY (EVAL_TAC >> NO_TAC)
    \\ metis_tac [CONTAINER_def])
  in UNDISCH_ALL th end handle HOL_ERR e =>
  (prove_EvalPatBind_fail := goal;
   failwith "prove_EvalPatBind failed");

fun to_pattern tm =
  if astSyntax.is_Var tm then
    mk_Pvar(rand (rand tm))
  else if astSyntax.is_Con tm then
    let
      val (_,xs) = strip_comb tm
      val name = el 1 xs
      val args = el 2 xs
      val (args,_) = listSyntax.dest_list args
      val args = listSyntax.mk_list(map to_pattern args,pat_ty)
    in
      astSyntax.mk_Pcon(name, args)
    end
  else if is_Lit tm then mk_Plit (rand tm)
  (* can use this for translating pmatch pattern matches of Booleans
     but it requires assuming "true" and "false" are bound correctly
     in the constructor environment. this assumption probably needs to be added
     manually as necessary to asms in prove_EvalPatRel.
     (alternatively, hol2deep could translate T and F directly under that assumption?)
  else if aconv tm true_exp_tm then
    astSyntax.mk_Pcon(true_tid,listSyntax.mk_nil pat_ty)
  else if aconv tm false_exp_tm then
    astSyntax.mk_Pcon(false_tid,listSyntax.mk_nil pat_ty)
  *)
  else tm

val pmatch_hol2deep_fail = ref T;
val tm = !pmatch_hol2deep_fail;

fun pmatch_hol2deep tm hol2deep = let
  val (x,ts) = dest_pmatch_K_T tm
  val v = genvar (type_of x)
  val x_res = hol2deep x |> D
  val x_type = type_of x
  val x_inv = get_type_inv x_type
  val pmatch_type = type_of tm
  val pmatch_inv = get_type_inv pmatch_type
  val x_exp = x_res |> UNDISCH |> concl |> rator |> rand
  val nil_lemma = Eval_PMATCH_NIL
                  |> ISPECL [pmatch_inv,x_exp,v,x_inv]
  val cons_lemma = Eval_PMATCH
                   |> ISPECL [pmatch_inv,x_inv,x_exp,v]
  fun prove_hyp conv th =
    MP (CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th) TRUTH
  val assm = nil_lemma |> concl |> dest_imp |> fst
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    (*
    val ((pat,rhs_tm)::xs) = List.drop(ts,3)
    *)
    val th = trans xs
    val p = pat |> dest_pabs |> snd |> hol2deep
                |> concl |> rator |> rand |> to_pattern
    val lemma = cons_lemma |> GEN (mk_var("p",pat_ty)) |> ISPEC p
    val lemma = prove_hyp EVAL lemma
    val pat_var = lemma |> concl |> free_vars
                        |> first (fn v => fst (dest_var v) = "pat")
    val lemma = lemma |> GEN pat_var |> ISPEC pat
    val lemma = prove_hyp (SIMP_CONV (srw_ss()) [FORALL_PROD]) lemma
    val lemma = UNDISCH lemma
    val th0 = UNDISCH th |> CONJUNCT1
    val th = UNDISCH th |> CONJUNCT2
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) (UNBETA_CONV v))
    val th = MATCH_MP lemma th
    val th = remove_primes th
    val goal = fst (dest_imp (concl th))
    val th = MP th (prove_EvalPatRel goal hol2deep)
    val th = remove_primes th
    val res_var = th |> concl |> free_vars
                     |> first (fn v => fst (dest_var v) = "res")
    val th = th |> GEN res_var |> ISPEC rhs_tm
    val goal = fst (dest_imp (concl th))
    val th = MATCH_MP th (prove_EvalPatBind goal hol2deep)
    val th = remove_primes th
    val th = MP th th0
    val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV)
          (SIMP_CONV std_ss [FORALL_PROD,PMATCH_SIMP,
              patternMatchesTheory.PMATCH_ROW_COND_def])) th
    val th = DISCH assm th
    in th end
  val th = trans ts
  val th = MATCH_MP th (x_res |> UNDISCH)
  val th = UNDISCH_ALL (th |> CONJUNCT2)
  in th end handle HOL_ERR e =>
  (pmatch_hol2deep_fail := tm;
   failwith ("pmatch_hol2deep failed (" ^ message_of e ^ ")"));

local
  (* list_conv: applies c to every xi in a term such as [x1;x2;x3;x4] *)
  fun list_conv c tm =
    if listSyntax.is_cons tm then
      ((RATOR_CONV o RAND_CONV) c THENC
       RAND_CONV (list_conv c)) tm
    else if listSyntax.is_nil tm then ALL_CONV tm
    else NO_CONV tm
  (* K_T_intro_conv: attempts to reduce the term to K T *)
  fun K_T_intro_conv tm = let
    val goal = combinSyntax.mk_K(T,fst (dest_pabs tm)) |> rator
    val goal = mk_eq(tm,goal)
    val lemma = auto_prove "K_T_intro_conv" (goal, fs [FUN_EQ_THM,FORALL_PROD,TRUE_def])
    in lemma end handle HOL_ERR _ => NO_CONV tm
  val BINOP1_CONV = RATOR_CONV o RAND_CONV
  (* pabs_intro_conv: \x. case x of (x,y,z) => ... ---> \(x,y,z). ... *)
  fun pabs_intro_conv tm =
    (ABS_CONV (REWR_CONV ml_translatorTheory.pair_CASE_UNCURRY
     THENC (BINOP1_CONV (ABS_CONV pabs_intro_conv))) THENC ETA_CONV) tm
    handle HOL_ERR _ => ALL_CONV tm
  fun fix_pmatch_row_names tm = let
    val (x,y) = dest_pmatch_row_K_T tm
    val (x1,x2) = dest_pabs x
    val (y1,y2) = dest_pabs y
    val i = fst (match_term x1 y1)
    val goal = mk_eq(x,mk_pabs(y1,subst i x2))
    val lemma = auto_prove "fix_pmatch_row_names" (goal, fs [FUN_EQ_THM,FORALL_PROD])
    in ((RATOR_CONV o RATOR_CONV o RAND_CONV) (K lemma)) tm end
    handle HOL_ERR _ => (print_term tm; NO_CONV tm)
  fun pmatch_row_preprocess_conv tm =
    ((RATOR_CONV o RAND_CONV) K_T_intro_conv THENC
     RAND_CONV pabs_intro_conv THENC
     (RATOR_CONV o RATOR_CONV o RAND_CONV) pabs_intro_conv THENC
     fix_pmatch_row_names) tm
in
  fun pmatch_preprocess_conv tm =
    QCONV (RAND_CONV (list_conv pmatch_row_preprocess_conv)) tm
    handle HOL_ERR _ => failwith "pmatch_preprocess_conv failed"
end

(* The preprocessor -- returns (def,ind). Here def is the original
   definition stated as a single line:

     foo v1 v2 v3 ... vN = RHS

   where vi are variables. The second return value is an option type:
   if NONE then foo is not recursive, if SOME th then th is an
   induction theorem that matches the structure of foo. *)

fun pattern_complete def vs = let
  val lines = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
                  |> map (fst o dest_eq o concl)
  val const = hd lines |> repeat rator
  val ws = map (fn v => (v,genvar (type_of v))) vs
  val tm = foldl (fn (x,y) => mk_comb(y,snd x)) const ws
  fun tt line = let
    val i = fst (match_term tm line)
    val x = list_mk_exists(rev (free_vars line),
              list_mk_conj (map (fn v => mk_eq(snd v,subst i (snd v))) ws))
    in x end
  val pat_tm = list_mk_disj (map tt lines)
  val pat_tm = subst (map (fn (y,x) => x |-> y) ws) pat_tm
  val pre_tm = mk_PRECONDITION pat_tm
  in pre_tm end

fun single_line_def def = let
  val lhs = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                |> concl |> dest_eq |> fst
  val const = lhs |> repeat rator
  in if List.null (filter (not o is_var) (dest_args lhs)) then (def,NONE) else let
  val name = const |> dest_const |> fst
  val thy = #Thy (dest_thy_const const)
  val rw = fetch thy (name ^ "_curried_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_curried_DEF")
           handle HOL_ERR _ => let
           val arg = mk_var("x",const |> type_of |> dest_type |> snd |> hd)
           in REFL (mk_comb(const,arg)) end
  val tpc = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rator
  val args = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val tp = fetch thy (name ^ "_tupled_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_tupled_primitive_DEF")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_DEF")
  val (v,tm) = tp |> concl |> rand |> rand |> dest_abs
  val goal = mk_eq(mk_comb(tpc,args),mk_comb(subst [v|->tpc] tm,args))
  val pre_tm =
    if not (can (find_term is_arb) tm) then T else let
      val vs = rw |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_args
      val pre_tm = pattern_complete def vs
      in pre_tm end
  val goal = mk_imp(pre_tm,goal)
  val lemma = auto_prove "single_line_def-1" (goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,GSYM rw]
    \\ REPEAT STRIP_TAC
    \\ CONV_TAC (BINOP_CONV (REWR_CONV (GSYM CONTAINER_def)))
    \\ SRW_TAC [] []
    \\ BasicProvers.EVERY_CASE_TAC
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    \\ SRW_TAC [] []
    \\ POP_ASSUM MP_TAC \\ REWRITE_TAC [PRECONDITION_def])
  val lemma = lemma |> RW [] |> UNDISCH_ALL
  val new_def =
    rw |> SPEC_ALL |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [lemma]))
       |> CONV_RULE (RAND_CONV BETA_CONV)
       |> REWRITE_RULE [I_THM]
       |> ONCE_REWRITE_RULE [GSYM rw]
  in (new_def,NONE) end handle HOL_ERR _ => let
  val v = mk_var("generated_definition",mk_type("fun",[oneSyntax.one_ty,type_of const]))
  val lemma  = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val def_tm = (subst [const|->mk_comb(v,oneSyntax.one_tm)] (concl lemma))
  val _ = Pmatch.with_classic_heuristic quietDefine [ANTIQUOTE def_tm]
(*
  val qDefine = TotalDefn.qDefine "generated_definition[notuserdef]"
  val _ = Pmatch.with_classic_heuristic qDefine [ANTIQUOTE def_tm]
*)
  fun find_def name =
    Theory.current_definitions ()
    |> first (fn (s,_) => s = name) |> snd
  val ind = fetch "-" "generated_definition_ind"
  val _ = (delete_const "generated_definition" handle HOL_ERR e => ())
  val _ = (Theory.delete_binding "generated_definition_def" handle HOL_ERR e => ())
  val _ = (Theory.delete_binding "generated_definition_ind" handle HOL_ERR e => ())
  val tys = ind |> concl |> dest_forall |> fst |> type_of |> dest_type |> snd
  val vv = mk_var("very unlikely name",el 2 tys)
  val ind = ind |> SPEC (mk_abs(mk_var("x",hd tys),vv))
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss []))
                |> GEN vv
  val lemma = DefnBase.one_line_ify NONE def
  in (lemma,SOME ind) end end
  handle HOL_ERR _ => failwith("Preprocessor failed: unable to reduce definition to single line.")

fun remove_pair_abs def = let
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val def = SPEC_ALL def
  fun delete_pair_arg def = let
    val (lhs,rhs) = def |> concl |> dest_eq
    val xs = args lhs
    val p = first pairSyntax.is_pair xs
    val v = hd (rev (free_vars p)) |> dest_var |> fst
    val v = mk_var(v,type_of p)
    val goal = mk_eq(subst [p|->v] lhs,mk_comb(pairSyntax.mk_pabs(p,rhs),v))
    val lemma = auto_prove "delete_pair_arg" (goal,
      SPEC_TAC (v,v) \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
      \\ SIMP_TAC std_ss [Once def]);
    in delete_pair_arg lemma end handle HOL_ERR _ => def
  val def = delete_pair_arg def
  val def' = CONV_RULE (RAND_CONV (REWRITE_CONV [UNCURRY_SIMP] THENC
               (DEPTH_CONV PairRules.PBETA_CONV))) def
  in if Teq (concl def') then def else def' end

fun is_rec_def def = let
  val thms = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
  val const = hd thms |> concl |> dest_eq |> fst |> repeat rator
  val rhss = thms |> map (snd o dest_eq o concl)
  in can (first (can (find_term (aconv const)))) rhss end

fun is_NONE NONE = true | is_NONE _ = false

local
  val preferred = ref ([]:string list);
in
  fun add_preferred_thy thy_name = (preferred := thy_name::(!preferred))
  fun fetch_from_thy thy name = let
    fun aux [] name = failwith ("cannot find theorem: " ^ name)
      | aux (thy::ts) name = fetch thy name handle HOL_ERR _ => aux ts name
    in aux ((!preferred) @ [thy]) name end
end

fun find_ind_thm def = let
  val const = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator
  val r = dest_thy_const const
  val ind = fetch_from_thy (#Thy r) ((#Name r) ^ "_trans_ind")
            handle HOL_ERR _ =>
            fetch_from_thy (#Thy r) ((#Name r) ^ "_ind")
            handle HOL_ERR _ =>
            fetch_from_thy (#Thy r) ((#Name r) ^ "_IND")
            handle HOL_ERR _ =>
            fetch_from_thy (#Thy r) ("ConstMult_ind")
            handle HOL_ERR _ => TRUTH
  in ind end

fun split_let_and_conv tm = let
  val (xs,b) = pairSyntax.dest_anylet tm
  val _ = 1 < length xs orelse fail()
  val _ = map (fn (x,y) => if is_var x then () else fail()) xs
  val ys = map (fn (x,y) => (x,genvar(type_of x),y)) xs
  val b2 = subst (map (fn (x,y,_) => x |-> y) ys) b
  val tm2 = foldr (fn ((x,y,z),b) => pairSyntax.mk_anylet([(y,z)],b)) b2 ys
  val goal = mk_eq(tm,tm2)
  val lemma = auto_prove"split_let_and_conv" (goal, REWRITE_TAC [LET_THM] (* potentially bad *)
                          THEN CONV_TAC (DEPTH_CONV BETA_CONV)
                          THEN REWRITE_TAC [])
  in lemma end handle HOL_ERR _ => NO_CONV tm;

fun mk_fun_type ty1 ty2 = mk_type("fun",[ty1,ty2])

fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

fun get_induction_for_def def = let
  val names = def |> SPEC_ALL |> CONJUNCTS |> map (fn x => x |>SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator |> dest_thy_const) |> mk_set
  fun get_ind [] = raise ERR "get_ind" "Bind Error"
    | get_ind [res] =
      (fetch_from_thy (#Thy res) ((#Name res) ^ "_trans_ind") handle HOL_ERR _ =>
       (fetch_from_thy (#Thy res) ((#Name res) ^ "_ind") handle HOL_ERR _ =>
        (fetch_from_thy (#Thy res) ((#Name res) ^ "_IND"))))
    | get_ind (res::ths) = (get_ind [res]) handle HOL_ERR _ => get_ind ths
  in
    get_ind names
  end handle HOL_ERR _ => let
  fun mk_arg_vars xs = let
    fun mk_name n x =
      "v" ^ int_to_string n ^ "_" ^ fst (dest_var x) ^ "_"
      handle HOL_ERR _ => "v" ^ int_to_string n
    fun aux [] = []
      | aux (x::xs) = mk_var(mk_name (length xs + 1) x, type_of x) :: aux xs
    in (rev o aux o rev) xs end
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = strip_comb lhs
    val vargs = mk_arg_vars args
    val args = pairSyntax.list_mk_pair args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> op_mk_set aconv
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => aconv c x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun split_at P [] = fail()
    | split_at P (x::xs) = if P x then ([],x,xs) else let
        val (x1,y1,z1) = split_at P xs
        in (x::x1,y1,z1) end
  fun find_pat_match (_,args,pats) = let
    val pat = hd pats |> fst
    val vs = pairSyntax.list_mk_pair args
    val ss = fst (match_term vs pat)
    val xs = map (subst ss) args
    in (split_at (not o is_var) xs) end
  val xs = map find_pat_match cs
  val ty = map (fn (_,x,_) => type_of x) xs |> hd
  val raw_ind = TypeBase.induction_of ty
  fun my_mk_var ty = mk_var("pat_var", ty)
  val index = ref 0
  fun goal_step (xs,t,ys) = let
    val v = my_mk_var (type_of t)
    val args = xs @ [v] @ ys
    val P = mk_var("P" ^ (int_to_string (!index)) ,
              list_mk_fun_type ((map type_of args) @ [bool]))
    val _ = (index := (!index) + 1)
    val prop = list_mk_comb(P,args)
    val goal = list_mk_forall(args,prop)
    val step = mk_abs(v,list_mk_forall(xs @ ys,prop))
    in (P,(goal,step)) end
  val res = map goal_step xs
  fun ISPEC_LIST [] th = th
    | ISPEC_LIST (x::xs) th = ISPEC_LIST xs (ISPEC x th)
  val ind = ISPEC_LIST (map (snd o snd) res) raw_ind
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val goal1 = ind |> concl |> dest_imp |> snd
  val goal2 = list_mk_conj (map (fst o snd) res)
  val goal = mk_imp(goal1,goal2)
  val lemma = auto_prove "get_induction_for" (goal, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
  val ind = MP lemma (ind |> UNDISCH_ALL) |> DISCH_ALL
            |> GENL (map fst res)
  in ind end handle HOL_ERR _ =>
  failwith "unable to construct induction theorem from TypeBase info"

fun mutual_to_single_line_def def = let
  (* get induction theorem *)
  val ind = get_induction_for_def def
  (* collapse to one line per function *)
  fun mk_arg_vars xs = let
    fun mk_name n x =
      "v" ^ int_to_string n ^ "_" ^ fst (dest_var x) ^ "_"
      handle HOL_ERR _ => "v" ^ int_to_string n
    fun aux [] = []
      | aux (x::xs) = mk_var(mk_name (length xs + 1) x, type_of x) :: aux xs
    in (rev o aux o rev) xs end
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = strip_comb lhs
    val vargs = mk_arg_vars args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> op_mk_set aconv
  (* val _ = 1 < length cnames orelse failwith "not mutually recursive" *)
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => aconv c x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun goal_line (c,_,[(args,body)]) = let
        val gg = mk_eq(list_mk_comb(c,args),body)
        in (list_mk_abs(args,gg),gg) end
    | goal_line (c,args,pats) = let
    fun transpose [] = []
      | transpose ([]::xs) = []
      | transpose xs = map hd xs :: transpose (map tl xs)
    val us = transpose (map fst pats) |> map (op_mk_set aconv)
    val ts = zip us args |> map (fn (x,y) => length x > 1)
    val pats = map (fn (ps,body) =>
      (pairSyntax.list_mk_pair (map snd (filter fst (zip ts ps))),body)) pats
    val rhs = TypeBase.mk_pattern_fn pats
    val rhs_x = filter fst (zip ts args) |> map snd |> pairSyntax.list_mk_pair
    val rhs = mk_comb(rhs,rhs_x)
    val ss = filter (not o fst) (zip ts (zip us args)) |> map snd
             |> map (fn (x,y) => y |-> hd x)
    val args = map (subst ss) args
    val gg = mk_eq(list_mk_comb(c,args),rhs)
    in (list_mk_abs(args,gg),gg) end
  val gs = map goal_line cs
  val target = map snd gs |> list_mk_conj
  in if concl def ~~ target then (def |> CONJUNCTS,SOME ind) else let
  val goals = map fst gs
  val lemma = ISPECL goals ind
  val goal = lemma |> concl |> dest_imp |> fst
  val _ = if can (find_term is_arb) (concl def) then true else
            not (can (find_term is_arb) goal) orelse
            failwith "mutual_to_single_line_def: requires precondition"
  val lemma1 = auto_prove "mutual_to_single_line_def" (goal,
    REPEAT STRIP_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV [def]))
    THEN SIMP_TAC (srw_ss()) [])
  val def2 = MP lemma lemma1
             |> CONV_RULE (DEPTH_CONV BETA_CONV)
             |> CONJUNCTS |> map SPEC_ALL
  in (def2,SOME ind) end end handle HOL_ERR _ => let
  val (def,ind) = single_line_def def
  in ([def],ind) end

val builtin_terops =
  [Eval_substring,
   Eval_FLOAT_FMA]
  |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator |> rator |> rator, th))

val builtin_binops =
  [Eval_NUM_ADD,
   Eval_NUM_SUB,
   Eval_NUM_SUB_check,
   Eval_NUM_MULT,
   Eval_NUM_DIV,
   Eval_NUM_MOD,
   Eval_NUM_LESS,
   Eval_NUM_LESS_EQ,
   Eval_NUM_GREATER,
   Eval_NUM_GREATER_EQ,
   Eval_NUM_EQ,
   Eval_BOOL_EQ,
   Eval_char_lt,
   Eval_char_le,
   Eval_char_gt,
   Eval_char_ge,
   Eval_char_eq,
   Eval_str_eq,
   Eval_INT_ADD,
   Eval_INT_SUB,
   Eval_INT_MULT,
   Eval_INT_DIV,
   Eval_INT_MOD,
   Eval_INT_EQ,
   Eval_INT_LESS,
   Eval_INT_LESS_EQ,
   Eval_INT_GREATER,
   Eval_INT_GREATER_EQ,
   Eval_FLOAT_ADD,
   Eval_FLOAT_SUB,
   Eval_FLOAT_MULT,
   Eval_FLOAT_DIV,
   Eval_FLOAT_LESS,
   Eval_FLOAT_LESS_EQ,
   Eval_FLOAT_GREATER,
   Eval_FLOAT_GREATER_EQ,
   Eval_FLOAT_EQ,
   Eval_force_gc_to_run,
   Eval_force_unit_type,
   Eval_strsub,
   Eval_ListAppend,
   Eval_sub,
   Eval_sub_unsafe,
   Eval_Implies,
   Eval_pure_seq]
 |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator |> rator, th))

val builtin_monops =
  [Eval_implode,
   Eval_explode,
   Eval_strlen,
   Eval_concat,
   Eval_Bool_Not,
   Eval_int_negate,
   Eval_length,
   Eval_vector,
   Eval_int_of_num,
   Eval_num_of_int,
   Eval_FLOAT_ABS,
   Eval_FLOAT_SQRT,
   Eval_FLOAT_NEG,
   Eval_FP_fromWord,
   Eval_FP_toWord,
   Eval_empty_ffi,
   Eval_force_out_of_memory_error,
   Eval_char_to_word8,
   Eval_word8_to_char,
   Eval_Chr,
   Eval_Ord]
  |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator, th))

val builtin_hol_string_binops =
  [Eval_HOL_STRING_EL,
   Eval_HOL_STRING_CONS,
   Eval_HOL_STRING_APPEND]
  |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator |> rator, th))

val builtin_hol_string_monops =
  [Eval_HOL_STRING_LENGTH,
   Eval_HOL_STRING_IMPLODE,
   Eval_HOL_STRING_EXPLODE,
   Eval_HOL_STRING_HD,
   Eval_HOL_STRING_FLAT,
   Eval_implode_nop,
   Eval_HOL_STRING_explode]
  |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator, th))

val builtin_sub_check =
  [Eval_NUM_SUB_check']
 |> map (fn th =>
      (th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rand |> rand |> rator |> rator, th))

val AUTO_ETA_EXPAND_CONV = let (* K ($=) --> K (\x y. x = y) *)
  val must_eta_expand_ops =
    map fst builtin_terops @
    map fst builtin_binops @
    map fst builtin_sub_check @
    map fst builtin_monops @
    map fst builtin_hol_string_binops @
    map fst builtin_hol_string_monops
  fun must_eta_expand tm =
    TypeBase.is_constructor tm orelse
    tmem tm must_eta_expand_ops orelse
    can (match_term boolSyntax.equality) tm
  fun full_arg_num tm = let
    fun n ty = n (snd (dest_fun_type ty)) + 1 handle HOL_ERR _ => 0
    in n (type_of tm) end
  fun FULL_ETA_CONV tm = let
    val v = genvar (fst (dest_fun_type (type_of tm)))
    val lemma = ETA_CONV (mk_abs(v,mk_comb(tm,v)))
    in ((K (SYM lemma)) THENC ABS_CONV (FULL_ETA_CONV)) tm end
    handle HOL_ERR _ => ALL_CONV tm
  fun aux n tm =
    if is_const tm then
      if n < full_arg_num tm andalso must_eta_expand tm
      then FULL_ETA_CONV tm
      else ALL_CONV tm
    else if is_comb tm then let
      val (f,x) = dest_comb tm
      in (RATOR_CONV (aux (n+1)) THENC RAND_CONV (aux 0)) tm end
    else if is_abs tm then let
      val (v,body) = dest_abs tm
      in (ABS_CONV (aux 0)) tm end
    else if is_var tm then ALL_CONV tm
    else fail()
  in aux 0 end

fun force_eqns def = let
  fun f th = if is_eq (concl (SPEC_ALL th)) then th else
               GEN_ALL (MATCH_MP IMP_EQ_F (SPEC_ALL th)) handle HOL_ERR _ =>
               GEN_ALL (MATCH_MP IMP_EQ_T (SPEC_ALL th))
  in LIST_CONJ (map f (CONJUNCTS (SPEC_ALL def))) end

val use_mem_intro = ref false;

fun preprocess_def def = let
  val def = force_eqns def
  val is_rec = is_rec_def def
  val (defs,ind) = mutual_to_single_line_def def
  fun rephrase_def def = let
    val def = PURE_ONCE_REWRITE_RULE [GSYM TRUE_def, GSYM FALSE_def] def
    val def = remove_pair_abs def |> SPEC_ALL
    val def = rename_bound_vars_rule " variable " (GEN_ALL def) |> SPEC_ALL
    val def = CONV_RULE (DEPTH_CONV split_let_and_conv) def
    val def = if def |> SPEC_ALL |> concl |> dest_eq |> fst |> is_const
              then SPEC_ALL (RW1 [FUN_EQ_THM] def) else def
    val def = CONV_RULE (DEPTH_CONV mlstringLib.mlstring_case_conv) def
    val def = PURE_REWRITE_RULE ([ADD1,boolTheory.literal_case_DEF,
                num_case_thm] @ get_preprocessor_rws()) def
    val def = CONV_RULE (AUTO_ETA_EXPAND_CONV THENC REDEPTH_CONV BETA_CONV) def
    val def = rename_bound_vars_rule "v" (GEN_ALL def) |> SPEC_ALL
    in def end;
  val defs = map rephrase_def defs
  val ind = if is_rec andalso is_NONE ind then SOME (find_ind_thm (hd defs)) else ind
  (* TODO: This performs e.g.special <| |> rewrites that are also applied to defs in the rephrase step to the induction theorem so that they match up *)
  fun rephrase_ind th = let
    val th = PURE_REWRITE_RULE ([ADD1,boolTheory.literal_case_DEF,
                num_case_thm] @ get_preprocessor_rws()) th
    in th end;
  val ind = case ind of SOME ind => SOME (rephrase_ind ind) | NONE => ind
  fun option_apply f NONE = NONE | option_apply f (SOME x) = SOME (f x)
  val mem_intro_rule = PURE_REWRITE_RULE [MEMBER_INTRO]
  val (defs,ind) = if not (!use_mem_intro) then (defs,ind) else
                     (map mem_intro_rule defs, option_apply mem_intro_rule ind)
  in (is_rec,defs,ind) end;


(* definition of the main work horse: hol2deep: term -> thm *)

fun dest_builtin_terop tm = let
  val (pxx,r3) = dest_comb tm
  val (px,r2) = dest_comb pxx
  val (p,r1) = dest_comb px
  val (x,th) = first (fn (x,_) => can (match_term x) p) builtin_terops
  val (ss,ii) = match_term x p
  val th = INST ss (INST_TYPE ii th)
  in (p,r1,r2,r3,th) end handle HOL_ERR _ => failwith("Not a builtin operator")

fun dest_builtin_binop tm = let
  val (px,r2) = dest_comb tm
  val (p,r1) = dest_comb px
  val thms =
    (if sub_check () then builtin_sub_check else []) @
    (if use_hol_string_type () then builtin_hol_string_binops else []) @ builtin_binops
  val (x,th) = first (fn (x,_) => can (match_term x) p) thms
  val (ss,ii) = match_term x p
  val th = INST ss (INST_TYPE ii th)
  in (p,r1,r2,th) end handle HOL_ERR _ => failwith("Not a builtin operator")

fun dest_builtin_monop tm = let
  val (p,r) = dest_comb tm
  val thms = (if use_hol_string_type () then builtin_hol_string_monops else [])
             @ builtin_monops
  val (x,th) = first (fn (x,_) => can (match_term x) p) thms
  val (ss,ii) = match_term x p
  val th = INST ss (INST_TYPE ii th)
  in (p,r,th) end handle HOL_ERR _ => failwith("Not a builtin operator")

fun inst_Eval_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = mlstringSyntax.mk_mlstring name
  val inv = get_type_inv (type_of v)
  val assum = mk_Eval(env_tm,
                      astSyntax.mk_Var(astSyntax.mk_Short(str)),
                        mk_comb(inv, v))
  val new_env = mk_write(str,mk_var("v",v_ty),env_tm)
  val old_env = new_env |> rand
  val c = SIMP_CONV bool_ss [Eval_Var_SIMP,lookup_var_write]
                           (* TODO lift out *)
          THENC DEPTH_CONV (mlstring_EQ_CONV)
          THENC REWRITE_CONV []
  val c = (RATOR_CONV o RAND_CONV) c THENC
          (RAND_CONV o RATOR_CONV o RAND_CONV) c
  val c1 = ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [ASSUME assum]))
  val th = thx |> D |> CONV_RULE c1 |> DISCH assum
               |> INST [old_env|->new_env]
               |> PURE_REWRITE_RULE [lookup_cons_write,lookup_var_write,nsLookup_write]
               |> CONV_RULE c
  val new_assum = fst (dest_imp (concl th))
  val th1 = th |> UNDISCH_ALL
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

fun FORCE_GEN v th1 = GEN v th1 handle HOL_ERR _ => let
  val hs = hyp th1
  val xs = filter (fn tm => tmem v (free_vars tm)) hs
  val th2 =  DISCH T th1
  val th3 = foldr (fn (tm,th) => ONCE_REWRITE_RULE [AND_IMP_INTRO] (DISCH tm th)) th2 xs
  val th4 = GEN v th3
  val th4 = HO_MATCH_MP PUSH_FORALL_INTO_IMP th4
  in UNDISCH th4 end

(*
  val (v,x) = dest_abs tm
  val th = hol2deep x
  val th = inst_Eval_env v th
*)

val apply_Eval_Fun_fail = (ref (T,TRUTH,true));
val (v, th, fix) = !apply_Eval_Fun_fail;

fun apply_Eval_Fun v th fix = let
  val th1 = inst_Eval_env v th
  val th2 = if fix then MATCH_MP Eval_Fun_Eq (GEN (mk_var("v",v_ty)) th1)
                   else MATCH_MP Eval_Fun (GEN (mk_var("v",v_ty)) (FORCE_GEN v th1))
  in th2 end handle (e as HOL_ERR _) =>
    (apply_Eval_Fun_fail := (v, th, fix);
    raise (wrap_exn "ml_translatorLib" "apply_Eval_Fun" e));

fun apply_Eval_Recclosure recc fname v th = let
  val vname = fst (dest_var v)
  val vname_str = mlstringSyntax.mk_mlstring vname
  val fname_str = mlstringSyntax.mk_mlstring fname
  val FORALL_CONV = RAND_CONV o ABS_CONV
  val lemma = ISPECL [recc,fname_str] Eval_Recclosure_ALT
              |> CONV_RULE ((FORALL_CONV o FORALL_CONV o
                             RATOR_CONV o RAND_CONV) EVAL)
  val pat = lemma |> concl |> find_term (can (match_term (get_term "find_recfun")))
  val lemma = SIMP_RULE std_ss [EVAL pat] lemma
  val inv = get_type_inv (type_of v)
  val pat = Eval_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rator
  val pat = lemma |> concl |> find_term (can (match_term pat))
  val new_env = pat |> rand
  val assum_eval = mk_Eval(env_tm,
                           astSyntax.mk_Var(astSyntax.mk_Short(vname_str)),
                           mk_comb(inv, v))
  val assum = subst [env_tm|->new_env] assum_eval
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum (* |> SIMP_RULE bool_ss [] *)
               |> INST [env_tm|->new_env]
               |> PURE_REWRITE_RULE [Eval_Var_SIMP,
                                     lookup_var_write,lookup_cons_write]
               |> CONV_RULE (DEPTH_CONV (mlstring_EQ_CONV))
               |> REWRITE_RULE [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH |> REWRITE_RULE [ASSUME new_assum]
                |> UNDISCH_ALL
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP lemma (INST [env_tm|->cl_env_tm] (GEN (mk_var("v",v_ty)) th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
                  |> REWRITE_RULE [Eval_Var_SIMP,
                       lookup_var_write,FOLDR,write_rec_def]
                  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  |> REWRITE_RULE [Eval_Var_SIMP,lookup_var_write,FOLDR]
                  |> CONV_RULE (DEPTH_CONV (mlstring_EQ_CONV))
                  |> REWRITE_RULE [SafeVar_def]
  val lemma = Eval_Eq_Recclosure |> UNDISCH
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    val th9 = INST i (INST_TYPE t lemma)
    val name = lemma_lhs |> inst t |> subst i |> rand |> rand
    in INST [mk_var("name",mlstringSyntax.mlstring_ty)|->name] th9 end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end

fun move_Eval_conv tm =
  let
    val (_,tm1) = strip_forall tm
    val tm2 = #2 (dest_imp tm1) handle HOL_ERR _ => tm1
  in
    if is_Eval tm2 then
      MATCH_MP IMP_EQ_T (ASSUME tm)
    else NO_CONV tm
  end

(*
val th = D res
val be_quiet = true
*)

fun clean_assumptions_aux be_quiet th = let
  val start = start_timing "clean assumptions"
  val lhs1 = get_term "nsLookup_pat"
  val pattern1 = mk_eq(lhs1,mk_var("_",type_of lhs1))
  val lhs2 = lookup_cons_def (*lookup_cons_thm*) |> SPEC_ALL |> concl |> dest_eq |> fst
  val pattern2 = mk_eq(lhs2,mk_var("_",type_of lhs2))
  val lookup_assums = find_terms (fn tm => can (match_term pattern1) tm
                                    orelse can (match_term pattern2) tm) (concl th)
  val lemmas = map prove_lookup_cons_eq lookup_assums
               |> filter (fn th => th |> concl |> rand |> is_const)
  val _ = case List.find (fn l => Feq (l |> concl |> rand)) lemmas of
      NONE => ()
    | SOME t => ((if be_quiet then () else
                    (print "clean_assumptions: false assumption\n\n";
                     print_thm t; print "\n\n")) ;
                 failwith ("clean_assumptions: false" ^ Parse.thm_to_string t))
  val th = REWRITE_RULE lemmas th
  (* lift EqualityType assumptions out *)
  val pattern = get_term "eq type"
  val eq_assums = find_terms (can (match_term pattern)) (concl th)
  val th = REWRITE_RULE (map ASSUME eq_assums) th
  (* lift lookup_cons out *)
  val pattern = get_term "lookup_cons"
  val lookup_cons_assums = find_terms (can (match_term pattern)) (concl th)
  val th = REWRITE_RULE (map ASSUME lookup_cons_assums) th
  (* lift nsLookup out *)
  val pattern = get_term "nsLookup"
  val nsLookup_assums = find_terms (can (match_term pattern)) (concl th)
  val th = REWRITE_RULE (map ASSUME nsLookup_assums) th
  (* lift Eval out *)
  val th1 = th |> REWRITE_RULE [GSYM PreImpEval_def]
  val th2 = CONV_RULE (QCONV (LAND_CONV (ONCE_DEPTH_CONV move_Eval_conv))) th1
  val th = REWRITE_RULE [PreImpEval_def] th2
  val _ = end_timing start
  in th end;

fun clean_assumptions th = clean_assumptions_aux false th;
fun clean_assumptions_quietly th = clean_assumptions_aux true th;

fun get_pre_var lhs fname = let
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val args = dest_args lhs
  val ty = list_mk_type args bool
  val v = mk_var(fname ^ "_side",ty)
  in (foldl (fn (x,y) => mk_comb(y,x)) v args) end

local
  val rec_patterns = ref ([]:(term * string * string) list);
in
  fun install_rec_pattern lhs fname ml_fname =
    (rec_patterns := (lhs,fname,ml_fname)::(!rec_patterns))
  fun uninstall_rec_patterns () = (rec_patterns := [])
  fun match_rec_pattern tm = let
    val pats = (!rec_patterns)
    val (lhs,fname,ml_fname) = first (fn (pat,_,_) => can (match_term pat) tm) pats
    in (lhs,ml_fname,get_pre_var lhs fname) end
  fun get_rec_patterns () = (!rec_patterns)
end

val check_inv_fail = ref T;

fun check_inv name tm result = let
  val tm2 = result |> concl |> rand |> rand
  in if aconv tm2 tm then result else let
    val _ = (check_inv_fail := tm)
    val _ = (show_types_verbosely := true)
    val _ = print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    val _ = (show_types_verbosely := false)
    in failwith("checkinv") end end

fun MY_MATCH_MP th1 th2 = let
  val tm1 = fst (dest_imp (concl th1))
  val tm2 = concl th2
  val (s,i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;

fun force_remove_fix thx = let
  val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val xs = map rand (find_terms (can (match_term pat)) (concl thx))
  val s = SIMP_RULE std_ss [Eval_FUN_FORALL_EQ,FUN_QUANT_SIMP]
  val thx = foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs
  in thx end;

fun rm_fix res = let
  val lemma = mk_thm([],get_term "eq remove")
  val tm2 = QCONV (REWRITE_CONV [lemma]) res |> concl |> dest_eq |> snd
  in tm2 end

val MAP_pattern = get_term "map pat"
val FILTER_pattern = get_term "filter pat"
val EVERY_pattern = get_term "every pat"
val EXISTS_pattern = get_term "exists pat"
val is_precond = is_PRECONDITION

local
  val ty = word8
in
  fun is_word8_literal tm =
    if type_of tm = ty
    then numSyntax.is_numeral (rand tm)
    else false
end

fun is_word_literal tm =
  if wordsSyntax.is_word_type (type_of tm) andalso
     wordsSyntax.is_n2w tm
  then numSyntax.is_numeral (rand tm)
  else false

val Num_ABS_pat = Eval_Num_ABS |> concl |> rand |> rand |> rand

val int_of_num_o_pat = Eval_int_of_num_o |> concl |> rand |> rand |> rand
val o_int_of_num_pat = Eval_o_int_of_num |> concl |> rand |> rand |> rand

fun dest_word_binop tm =
  if wordsSyntax.is_word_and tm then Eval_word_and else
  if wordsSyntax.is_word_add tm then Eval_word_add else
  if wordsSyntax.is_word_or  tm then Eval_word_or  else
  if wordsSyntax.is_word_xor tm then Eval_word_xor else
  if wordsSyntax.is_word_sub tm then Eval_word_sub else
  if wordsSyntax.is_word_lo tm  then Eval_word_lo else
  if wordsSyntax.is_word_ls tm  then Eval_word_ls else
  if wordsSyntax.is_word_hi tm  then Eval_word_hi else
  if wordsSyntax.is_word_hs tm  then Eval_word_hs else
  if is_eq tm                   then Eval_word_eq else
    failwith("not a word binop")

fun dest_word_shift tm =
  if wordsSyntax.is_word_lsl tm then Eval_word_lsl else
  if wordsSyntax.is_word_lsr tm then Eval_word_lsr else
  if wordsSyntax.is_word_asr tm then Eval_word_asr else
  if wordsSyntax.is_word_ror tm then Eval_word_ror else
    failwith("not a word shift")

(* CakeML signature generation and manipulation *)
val generate_sigs = ref false;

fun sig_of_mlname name = definition (ml_progLib.pick_name name ^ "_sig") |> concl |> rhs;

fun module_signatures names = T
  (* failwith "module signatures are currently not supported" *)
  (* listSyntax.mk_list(map sig_of_mlname names, spec_ty); *)

fun sig_of_const cake_name tm = T
  (* failwith "module signatures are currently not supported" *)
  (* mk_Sval (stringSyntax.fromMLstring (ml_progLib.pick_name cake_name), type2t (type_of tm)); *)

fun generate_sig_thms results = let
  fun const_from_def th = th |> concl |> strip_conj |> hd |> strip_forall |> #2
                             |> dest_eq |> #1 |> strip_comb |> #1;

  fun mk_sig_thm sval = TRUTH
  (* failwith "module signatures are currently not supported" *)
  (* let
    val cake_name = dest_Sval sval |> #1 |> fromHOLstring;
    val sig_const_nm = cake_name ^ "_sig";
    val sig_const_tm = mk_var(sig_const_nm, spec_ty);

    val def = Definition.new_definition(sig_const_nm, mk_eq(sig_const_tm, sval));
    in def end *)

  val signatures = map (fn (_, ml_fname, def, _, _) => sig_of_const ml_fname (const_from_def def))
                       results;

  in map mk_sig_thm signatures
end

(*
val tm = rhs
val tm = rhs_tm
val tm = ``case v3 of (v2,v1) => QSORT v7 v2 ++ [v6] ++ QSORT v7 v1``
val tm = sortingTheory.PARTITION_DEF |> SPEC_ALL |> concl |> rhs
val tm = def |> SPEC_ALL |> concl |> rand
*)

val float64_ty = mk_thy_type{
      Args = [
          fcpSyntax.mk_numeric_type (Arbnum.fromInt 52),
          fcpSyntax.mk_numeric_type (Arbnum.fromInt 11)
      ],
      Thy = "binary_ieee",
      Tyop = "float"
    }

(* slightly more generous than binary_ieeeSyntax.dest_floating_point which
   insists on the record fields in the exp-sign-signif order *)
fun is_float_literal tm =
    let val (ty, alist) = TypeBase.dest_record tm
        val _ = ty = float64_ty orelse raise ERR "" ""
        val _ = Listsort.sort String.compare (map #1 alist) =
                ["Exponent", "Sign", "Significand"] orelse raise ERR "" ""
    in
      List.all (wordsSyntax.is_word_literal o #2) alist
    end handle HOL_ERR _ => false

fun hol2deep tm =
  (* variables *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_type_inv ty
    val str = mlstringSyntax.mk_mlstring name
    val result = ASSUME (mk_Eval(env_tm,
                       astSyntax.mk_Var(astSyntax.mk_Short(str)),
                       mk_comb(inv,tm)))
    in check_inv "var" tm result end else
  (* constants *)
  if tm ~~ oneSyntax.one_tm then Eval_Val_UNIT else
  if numSyntax.is_numeral tm then SPEC tm Eval_Val_NUM else
  if intSyntax.is_int_literal tm then SPEC tm Eval_Val_INT else
  if is_word_literal tm andalso word_ty_ok (type_of tm) then let
    val dim = wordsSyntax.dim_of tm
    val result = SPEC tm (INST_TYPE [alpha|->dim] Eval_Val_WORD)
                 |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
                 |> (fn th => MP th TRUTH)
                 |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
    in check_inv "word_literal" tm result end else
  if stringSyntax.is_char_literal tm then SPEC tm Eval_Val_CHAR else
  if is_float_literal tm then
    let
      val th0 = SPEC tm Eval_Val_FLOAT64
    in
      CONV_RULE
        (LAND_CONV
           (RAND_CONV
              (RAND_CONV (REWR_CONV machine_ieeeTheory.float_to_fp64_def THENC
                          EVAL))))
        th0
    end else
  if mlstringSyntax.is_mlstring_literal tm then
    SPEC tm Eval_Val_STRING else
  if use_hol_string_type () andalso can stringSyntax.fromHOLstring tm then
    SPEC tm Eval_HOL_STRING_LITERAL else
  if (Teq tm) then Eval_Val_BOOL_T else
  if (Feq tm) then Eval_Val_BOOL_F else
  if (tm ~~ TRUE) then Eval_Val_BOOL_TRUE else
  if (tm ~~ FALSE) then Eval_Val_BOOL_FALSE else
  (* data-type constructor *)
  inst_cons_thm tm hol2deep handle HOL_ERR _ =>
  (* data-type pattern-matching *)
  inst_case_thm tm hol2deep handle HOL_ERR _ =>
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    val (lhs,fname,pre_var) = match_rec_pattern tm
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = mlstringSyntax.mk_mlstring fname
    fun mk_fix tm = let
      val inv = get_type_inv (type_of tm)
      in mk_Eq(inv,tm) end
    fun mk_arrow x y = mk_Arrow(x,y)
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val pre = subst ss pre_var
    val pre_imp = mk_PreImp(pre, mk_Eval(env_tm,
                                         astSyntax.mk_Var(astSyntax.mk_Short(str)),
                                         mk_comb(inv,f)))
    val h = ASSUME pre_imp
            |> RW [PreImp_def] |> UNDISCH
    val ys = map (fn tm => MATCH_MP Eval_Eq (hol2deep tm)) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP Eval_Arrow (apply_arrow hyp xs)) x
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* previously translated term *)
  let
    val th = lookup_abs_v_thm tm
    val _ = check_no_ind_assum tm th
    val inv = get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val res = th |> UNDISCH_ALL |> concl |> rand
    val (ss,ii) = match_term res target handle HOL_ERR _ =>
                  match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
    val result = INST ss (INST_TYPE ii th)
  in check_inv "lookup_abs_v_thm" tm result end handle NotFoundVThm _ =>
  (* previously translated term *)
  if can lookup_v_thm tm then let
    val th = lookup_v_thm tm
    val _ = check_no_ind_assum tm th
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> map rand
    val ss = map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    val res = th |> UNDISCH_ALL |> concl |> rand
    val inv = get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term res target handle HOL_ERR _ =>
                  match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ =>
                  let
                    val new_target = subst [HOL_STRING_TYPE |-> get_term "list-type-char"] target
                  in
                    match_term res new_target
                  end handle HOL_ERR _ => ([],[])
    val result = INST ss (INST_TYPE ii th)
    in check_inv "lookup_v_thm" tm result end else
  (* previously translated term *)
  if can lookup_eval_thm tm then let
    val th = lookup_eval_thm tm
    val inv = hol2deep (mk_var("v",type_of tm)) |> concl |> rand |> rator
    val pat = th |> concl |> rand |> rator
    val (ss,ii) = match_term pat inv
    val result = INST ss (INST_TYPE ii th)
    in check_inv "lookup_eval_thm" tm result end else
  (* built-in ternary operations *)
  if can dest_builtin_terop tm then let
    val (p,x1,x2,x3,lemma) = dest_builtin_terop tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th3 = hol2deep x3
    val result = MATCH_MP (MATCH_MP (MATCH_MP lemma th1) (UNDISCH_ALL th2)) (UNDISCH_ALL th3) |> UNDISCH_ALL
    in check_inv "terop" tm result end else
  (* equality: n = 0 *)
  if can (match_term (get_term "n = 0")) tm then let
    val x1 = fst (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_NUM_EQ_0 th1
    in check_inv "num_eq_0" tm result end else
  (* equality: 0 = n *)
  if can (match_term (get_term "0 = n")) tm then let
    val x1 = snd (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP (GSYM Eval_NUM_EQ_0) th1
    in check_inv "0_eq_num" tm result end else
  (* built-in binary operations *)
  if can dest_builtin_binop tm then let
    val (p,x1,x2,lemma) = dest_builtin_binop tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP (MATCH_MP lemma th1) (UNDISCH_ALL th2) |> UNDISCH_ALL
    in check_inv "binop" tm result end else
  (* built-in unary operations *)
  if can dest_builtin_monop tm then let
    val (p,x1,lemma) = dest_builtin_monop tm
    val th1 = hol2deep x1
    val result = MATCH_MP lemma th1 |> UNDISCH_ALL
    in check_inv "monop" tm result end else
  (* equality (but not word equality) *)
  if is_eq tm andalso not (word_ty_ok (type_of (rand tm))) then let
    val (x1,x2) = dest_eq tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP Eval_Equality (CONJ th1 th2) |> UNDISCH
    in check_inv "equal" tm result end else
  (* and, or *)
  if is_conj tm then let
    val (x1,x2) = dest_conj tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th = MATCH_MP Eval_And (LIST_CONJ [D th1, D th2])
    val result = UNDISCH th
    in check_inv "and" tm result end else
  if is_disj tm then let
    val (x1,x2) = dest_disj tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th = MATCH_MP Eval_Or (LIST_CONJ [D th1, D th2])
    val result = UNDISCH th
    in check_inv "or" tm result end else
  (* if statements *)
  if is_cond tm then
    if is_precond (tm |> rator |> rator |> rand) then let
      val (x1,x2,x3) = dest_cond tm
      val th2 = hol2deep x2
      val lemma = IF_TAKEN |> SPEC x1 |> ISPEC x2 |> SPEC x3 |> UNDISCH |> SYM
      val result = th2 |> CONV_RULE ((RAND_CONV o RAND_CONV) (K lemma))
      in check_inv "if" tm result end
    else let
      val (x1,x2,x3) = dest_cond tm
      val th1 = hol2deep x1
      val th2 = hol2deep x2
      val th3 = hol2deep x3
      val th = MATCH_MP Eval_If (LIST_CONJ [D th1, D th2, D th3])
      val result = UNDISCH th
      in check_inv "if" tm result end else
  (* Num (ABS i) *)
  if can (match_term Num_ABS_pat) tm then let
    val x1 = tm |> rand |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_Num_ABS th1
    in check_inv "num_abs" tm result end else
  (* Num i *)
  if intSyntax.is_Num tm then let
    val x1 = tm |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_Num th1 |> UNDISCH_ALL
    in check_inv "num" tm result end else
  (* n2w 'a word for known 'a *)
  if wordsSyntax.is_n2w tm andalso word_ty_ok (type_of tm) then let
    val dim = wordsSyntax.dim_of tm
    val th1 = hol2deep (rand tm)
    val result = MATCH_MP (INST_TYPE [alpha|->dim] Eval_n2w
                           |> CONV_RULE wordsLib.WORD_CONV) th1
    in check_inv "n2w" tm result end else
  (* i2w 'a word for known 'a *)
  if integer_wordSyntax.is_i2w tm andalso word_ty_ok (type_of tm) then let
    val dim = wordsSyntax.dim_of tm
    val th1 = hol2deep (rand tm)
    val result = MATCH_MP (INST_TYPE [alpha|->dim] Eval_i2w
                           |> CONV_RULE wordsLib.WORD_CONV) th1
    in check_inv "i2w" tm result end else
  (* w2n 'a word for known 'a *)
  if wordsSyntax.is_w2n tm andalso word_ty_ok (type_of (rand tm)) then let
    val x1 = tm |> rand
    val dim = wordsSyntax.dim_of x1
    val th1 = hol2deep x1
    (* th1 should have instantiated 'a already *)
    val result = MATCH_MP Eval_w2n th1 |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
    in check_inv "w2n" tm result end else
  (* w2i 'a word for known 'a *)
  if integer_wordSyntax.is_w2i tm andalso word_ty_ok (type_of (rand tm)) then let
    val x1 = tm |> rand
    val dim = wordsSyntax.dim_of x1
    val th1 = hol2deep x1
    (* th1 should have instantiated 'a already *)
    val result = MATCH_MP Eval_w2i th1 |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
    in check_inv "w2i" tm result end else
  (* w2w 'a word for known 'a *)
  if wordsSyntax.is_w2w tm andalso word_ty_ok (type_of (rand tm))
                           andalso word_ty_ok (type_of tm) then let
    val x1 = tm |> rand
    val dim1 = wordsSyntax.dim_of tm
    val dim2 = wordsSyntax.dim_of x1
    val th1 = hol2deep x1
    val lemma = INST_TYPE [alpha|->dim1,beta|->dim2]Eval_w2w
    val h = lemma |> concl |> dest_imp |> fst
    val h_thm = EVAL h
    val lemma = REWRITE_RULE [h_thm] lemma
    val _ = Teq (rand (concl h_thm)) orelse failwith "false pre for w2w"
    val result =
        MATCH_MP (lemma |> SIMP_RULE std_ss [LET_THM]
                        |> CONV_RULE (RAND_CONV (RATOR_CONV wordsLib.WORD_CONV)))
          (hol2deep x1)
    in check_inv "w2w" tm result end else
  (* word_add, _and, _or, _xor, _sub *)
  if can dest_word_binop tm andalso word_ty_ok (type_of (rand tm)) then let
    val lemma = dest_word_binop tm
    val th1 = hol2deep (tm |> rator |> rand)
    val th2 = hol2deep (tm |> rand)
    val result = MATCH_MP lemma (CONJ th1 th2)
                |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
    in check_inv "word_binop" tm result end else
  (* word_lsl, _lsr, _asr *)
  if can dest_word_shift tm andalso word_ty_ok (type_of tm) then let
    val n = tm |> rand
    val _ = numSyntax.is_numeral n orelse
            failwith "2nd arg to word shifts must be numeral constant"
    val lemma = dest_word_shift tm |> SPEC n |> SIMP_RULE std_ss [LET_THM]
    val th1 = hol2deep (tm |> rator |> rand)
    val result = MATCH_MP lemma th1
                   |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
                   |> REWRITE_RULE []
                   |> CONV_RULE (RATOR_CONV wordsLib.WORD_CONV)
    in check_inv "word_shift" tm result end else
  (* $& o f *)
  if can (match_term int_of_num_o_pat) tm then let
    val x1 = tm |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_int_of_num_o th1
    in check_inv "int_of_num_o" tm result end else
  (* f o $& *)
  if can (match_term o_int_of_num_pat) tm then let
    val x1 = tm |> rator |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_o_int_of_num th1
    in check_inv "o_int_of_num" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = hol2deep x
    val th2 = inst_Eval_env v th2
    val th2 = th2 |> GEN (mk_var("v",v_ty))
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP Eval_Let (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* special pattern *) let
    fun pat_match pat tm = (match_term pat tm; rator pat)
    val r = pat_match MAP_pattern tm handle HOL_ERR _ =>
            pat_match EVERY_pattern tm handle HOL_ERR _ =>
            pat_match EXISTS_pattern tm handle HOL_ERR _ =>
          (* pat_match FILTER_pattern tm handle HOL_ERR _ => *) fail()
    val (m,f) = dest_comb tm
    val th_m = hol2deep r
    val (v,x) = dest_abs f
    val th_f = hol2deep x
    val th_f = apply_Eval_Fun v th_f true
    val thi = th_f |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN v
    val thi = HO_MATCH_MP Eq_IMP_And thi
    val thi = MATCH_MP (MATCH_MP Eval_Arrow th_m) thi
    val thi = RW [LIST_TYPE_And] thi
    val thi = MATCH_MP And_IMP_Eq thi
    val thi = SIMP_RULE std_ss [EVERY_MEM_CONTAINER] thi
    val result = thi |> UNDISCH_ALL
    in check_inv "map" tm result end handle HOL_ERR _ =>
  (* PMATCH *)
  if is_pmatch tm then let
   (*
     val tm = def |> SPEC_ALL |> concl |> rand
   *)
    val original_tm = tm
    val lemma = pmatch_preprocess_conv tm
    val tm = lemma |> concl |> rand
    val result = pmatch_hol2deep tm hol2deep
    val result = result |> CONV_RULE (RAND_CONV (RAND_CONV (K (GSYM lemma))))
    in check_inv "pmatch_hol2deep" original_tm result end else
  (* normal function applications *)
  if is_comb tm then let
    val (f,x) = dest_comb tm
    val thf = hol2deep f |> remove_primes
    val thx = hol2deep x |> remove_primes
    val thx = force_remove_fix thx
    val result = MATCH_MP (MATCH_MP Eval_Arrow thf) thx handle HOL_ERR _ =>
                 MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx)
                 handle HOL_ERR e =>
                   let (* patch up difference between HOL_STRING_TYPE and LIST_TYPE CHAR *)
                     val thx' = MATCH_MP Eval_HOL_STRING_DEST thx
                     val res = MATCH_MP (MATCH_MP Eval_Arrow thf) thx' handle HOL_ERR _ =>
                               MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx')
                     val _ = print "Warning: automatically added string EXPLODE "
                     val _ = print "due to HOL_STRING_TYPE\n"
                   in res end handle HOL_ERR _ => raise (HOL_ERR e)
    in check_inv "comb" tm result end else
  (* lambda applications *)
  if is_abs tm then let
    val (v,x) = dest_abs tm
    val thx = hol2deep x
    val result = apply_Eval_Fun v thx false
    in check_inv "abs" tm result end else
  if is_arb tm then let
    val inv = get_type_inv (type_of tm)
    val goal = mk_imp(mk_PRECONDITION F,
                      mk_Eval(env_tm,
                              astSyntax.mk_Raise(get_term "bind"),
                              mk_comb(inv,tm)))
    val result = auto_prove"hol2deep"(goal,SIMP_TAC std_ss [PRECONDITION_def]) |> UNDISCH
    in check_inv "arb" tm result end
  else raise (UnableToTranslate tm)

fun hol2val tm = let
  val th_rhs = hol2deep tm
  val res = mk_comb(rand (concl th_rhs),mk_var("v",v_ty))
            |> EVAL |> SIMP_RULE std_ss [] |> concl |> rand |> rand
  in res end;

(* collect precondition *)

fun every [] = true
  | every (x::xs) = x andalso every xs

fun clean_precondition pre_def = let
  val th = SIMP_RULE (srw_ss()) [] pre_def
  val th = REWRITE_RULE [CONTAINER_def] th
  val th = rename_bound_vars_rule "v" (GEN_ALL th) |> SPEC_ALL
  in th end;

fun ex_rename_bound_vars_rule th = let
  val i = ref 0
  fun next_name orig = let
    val n = (i:= !i+1; "x" ^ int_to_string (!i))
    in if String.isSubstring " " orig then n else n ^ "_" ^ orig ^ "_" end
  fun next_var v = let
    val (name, ty) = dest_var v
    in mk_var(next_name name, ty) end
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix "x" (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end

fun extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th,NONE) else let
    val c = (REWRITE_CONV [CONTAINER_def,PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def] THENC
             SIMP_CONV (srw_ss()++ARITH_ss) [FALSE_def,TRUE_def])
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if Teq rhs then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL (mk_PRECONDITION T)] th),NONE)
    else let
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
    in (th,SOME pre_def) end end

fun derive_split tm =
  if can (match_term (PRE_IMP |> concl |> rand)) tm then let
    val m = fst (match_term (PRE_IMP |> concl |> rand) tm)
    in INST m PRE_IMP end else
  if can (match_term (PreImp_IMP_T |> concl |> rand)) tm then let
    val m = fst (match_term (PreImp_IMP_T |> concl |> rand) tm)
    in INST m PreImp_IMP_T end else
  if is_conj tm then let
    val (x1,x2) = dest_conj tm
    in MATCH_MP CONJ_IMP (CONJ (derive_split x1) (derive_split x2)) end else
  if is_imp tm then let
    val (x1,x2) = dest_imp tm
    val th1 = REFL x1
    val th2 = derive_split x2
    in MATCH_MP IMP_SPLIT (CONJ th1 th2) end else
  if is_forall tm then let
    val (v,body) = dest_forall tm
    val th = derive_split body
    val th = CONV_RULE (RAND_CONV (UNBETA_CONV v) THENC
               (RATOR_CONV o RAND_CONV) (BINOP_CONV (UNBETA_CONV v))) th
    in MATCH_MP FORALL_SPLIT (GEN v th) end else
  SPEC tm DEFAULT_IMP

fun extract_precondition_rec thms = let
(*
  val (fname,ml_fname,def,th) = hd thms
*)
  fun rephrase_pre (fname,ml_fname,def,th) = let
    val (lhs,_) = dest_eq (concl def)
    val pre_var = get_pre_var lhs fname
    val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
    val th = ex_rename_bound_vars_rule th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
    val tm = concl th |> dest_imp |> fst
    val rw0 = ASSUME (get_term "remove lookup_cons")
    val tm0 = QCONV (REWRITE_CONV [rw0]) tm |> concl |> rand
    val rw1 = ASSUME (get_term "precond = T")
    val tm1 = QCONV (REWRITE_CONV [rw1]) tm0 |> concl |> rand
    val pat = Eval_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val rw2 = ASSUME (list_mk_forall(free_vars pat,pat))
    val tm2 = QCONV (REWRITE_CONV [rw0,rw2,PreImp_def]) tm |> concl |> rand
    in (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) end
  val thms = map rephrase_pre thms
(*
val (fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  (* check whether the precondition is T *)
  fun get_subst (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    in pre_v |-> true_pre end
  val ss = map get_subst thms
  fun is_true_pre (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) =
    (Teq
     (tm2 |> subst ss
          |> QCONV (REWRITE_CONV [rw2,PreImp_def,PRECONDITION_def,CONTAINER_def] THENC SIMP_CONV (srw_ss()++ARITH_ss) [FALSE_def,TRUE_def])
          |> concl |> rand))
  val no_pre = every (map is_true_pre thms)

  (* if no pre then remove pre_var from thms *)
  in if no_pre then let
    fun remove_pre_var (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) =
    let
      val th5 = INST ss th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))

      in (fname,ml_fname,def,th5,NONE) end
    in map remove_pre_var thms end else let

(*
  val (fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  fun separate_pre (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val lemma = derive_split (th |> concl |> dest_imp |> fst)
    val lemma = MATCH_MP combine_lemma (CONJ lemma th)
                |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                     (PURE_REWRITE_CONV [PRECONDITION_def]))
    in (fname,ml_fname,def,lemma,pre_var) end;
  val thms2 = map separate_pre thms
  val all_pre_vars = map (fn (fname,ml_fname,def,lemma,pre_var) =>
                            repeat rator pre_var) thms2
(*
val (fname,def,lemma,pre_var) = hd thms2
*)
  val all_pres = map (fn (fname,ml_fname,def,lemma,pre_var) => let
    val tm = lemma |> concl |> dest_imp |> fst
    val vs = op_set_diff aconv (free_vars tm) all_pre_vars
    val ws = tl (list_dest dest_comb pre_var)
    val ws = ws @ op_set_diff aconv vs ws
    in list_mk_forall(ws,mk_imp(tm,pre_var)) end) thms2
    |> list_mk_conj
  val (_,_,pre_def) = Hol_reln [ANTIQUOTE all_pres]
  val clean_pre_def = pre_def |> PURE_REWRITE_RULE [CONTAINER_def]
  val name = clean_pre_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
               |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val _ = delete_binding (name ^ "_rules") handle NotFound => ()
  val _ = delete_binding (name ^ "_ind") handle NotFound => ()
  val _ = delete_binding (name ^ "_strongind") handle NotFound => ()
  val _ = delete_binding (name ^ "_cases") handle NotFound => ()
  val _ = allowing_rebind save_thm(name ^ "_def", clean_pre_def)
  val pre_defs = pre_def |> CONJUNCTS |> map SPEC_ALL
  val thms3 = zip pre_defs thms2
  fun get_sub (pre,(fname,ml_fname,def,lemma,pre_var)) = let
    val x = pre_var |> repeat rator
    val y = pre |> concl |> dest_eq |> fst |> repeat rator
    in x |-> y end
  val ss = map get_sub thms3
  val pat = get_term "eq arrow"
  fun list_dest_Eq_Arrow tm =
    if can (match_term pat) tm then
      (tm |> rator |> rand |> rand) :: list_dest_Eq_Arrow (rand tm)
    else []
(*
val (pre,(fname,def,lemma,pre_var)) = hd thms3
*)
  fun compact_pre (pre,(fname,ml_fname,def,lemma,pre_var)) = let
    val vs = pre |> concl |> dest_eq |> fst |> list_dest dest_comb |> tl
    val ws = lemma |> UNDISCH_ALL |> concl |> rand |> rator |> list_dest_Eq_Arrow
    val i = map (fn (x,y) => x |-> y) (zip vs ws) handle HOL_ERR _ => []
    val c = (RATOR_CONV o RAND_CONV) (REWR_CONV (SYM (INST i pre)))
    val lemma = lemma |> INST ss |> CONV_RULE c
                      |> MATCH_MP IMP_PreImp_LEMMA
    val pre = pre |> PURE_REWRITE_RULE [CONTAINER_def]
    in (fname,ml_fname,def,lemma,SOME pre) end
  val thms4 = map compact_pre thms3
  in thms4 end end


(* main translation routines *)

val use_long_names = ref false;
val pick_name = ref (fn (c:term) => (fail(); ""));
val next_ml_names = ref (tl [""]);

fun get_next_ml_name default_name = let
  val xs = !next_ml_names
  in if xs = [] then default_name else
       (next_ml_names := tl xs; hd xs) end

fun get_info def = let
  val (lhs,rhs) = dest_eq (concl def)
  val c = repeat rator lhs
  val name = c |> dest_const |> fst
  val name = if !use_long_names then
               #Thy (dest_thy_const c) ^ "_" ^ name
             else name
  val fname = get_unique_name ((!pick_name) c handle HOL_ERR _ => name)
  in (fname,get_next_ml_name fname,lhs,rhs,def) end;

fun comma [] = ""
  | comma [x] = x
  | comma (x::xs) = x ^ ", " ^ comma xs

fun remove_Eq th = let
  val pat = get_term "arrow eq"
  fun dest_EqArrows tm =
    if can (match_term pat) tm
    then (rand o rand o rator) tm :: dest_EqArrows (rand tm)
    else []
  val rev_params = th |> concl |> rand |> rator |> dest_EqArrows |> rev
  fun f (v,th) =
    HO_MATCH_MP Eval_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  in foldr f th rev_params end handle HOL_ERR _ => th

fun rev_param_list tm =
  if is_comb tm then rand tm :: rev_param_list (rator tm) else []

val EVAL_T_F = LIST_CONJ [EVAL (mk_CONTAINER TRUE), EVAL (mk_CONTAINER FALSE)]

fun reset_translation () =
  (v_thms_reset();
   type_reset();
   type_mods_reset();
   cons_names_reset();
   print_reset();
   finalise_reset());

fun abbrev_code (fname,ml_fname,def,th,v) = let
  val th = th |> UNDISCH_ALL
  val exp = th |> concl |> rator |> rand
  val n = Theory.temp_binding ("____" ^ fname ^ "_code____")
  val code_def = Definition.new_definition(n,mk_eq(mk_var(n,type_of exp),exp))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (K (GSYM code_def))) th
  in (code_def,(fname,ml_fname,def,th,v)) end

val find_def_for_const =
  ref ((fn const => raise UnableToTranslate const) : term -> thm);

val last_const = ref T;

fun find_def_for_const_wrapper tm = let
    val _ = last_const := tm;
    val _ = is_const tm orelse raise (UnableToTranslate tm)
    val msg = "find_def_for_const: " ^ fst (dest_const tm)
    val def = do_timing msg (! find_def_for_const) tm
    val _ = can (find_term (same_const tm)) (concl def)
        orelse failwith ("find_def_for_const_wrapper: bad def: " ^
            fst (dest_const tm))
  in def end

fun force_thm_the (SOME x) = x | force_thm_the NONE = TRUTH

fun the (SOME x) = x | the _ = failwith("the of NONE")

fun prove_ind_thm ind ind_thm_goal =
(*
set_goal([],ind_thm_goal)
*)
  auto_prove "prove_ind_thm" (ind_thm_goal,
    rpt gen_tac
    \\ rewrite_tac [TRUE_def,FALSE_def]
    \\ rpt (disch_then strip_assume_tac)
    \\ simp_tac std_ss [FORALL_PROD,SUC_SUB1_LEMMA]
    \\ match_mp_tac (the ind)
    \\ rewrite_tac [UNCURRY_SIMP]
    \\ rpt strip_tac
    \\ last_x_assum match_mp_tac
    \\ rpt strip_tac
    \\ fs []
    \\ rpt var_eq_tac
    \\ fs [ADD1,UNCURRY_SIMP])
  handle HOL_ERR _ =>
  auto_prove "prove_ind_thm" (ind_thm_goal,
    rpt gen_tac
    \\ rewrite_tac [TRUE_def,FALSE_def]
    \\ rpt (disch_then strip_assume_tac)
    \\ simp_tac std_ss [FORALL_PROD,SUC_SUB1_LEMMA]
    \\ match_mp_tac (the ind)
    \\ rewrite_tac [UNCURRY_SIMP]
    \\ rpt strip_tac
    \\ last_x_assum match_mp_tac
    \\ rpt strip_tac
    \\ fs []
    \\ fs [FORALL_PROD]
    \\ imp_res_tac LENGTH_EQ_SUC_IMP
    \\ rpt var_eq_tac
    \\ fs [ADD1,UNCURRY_SIMP]
    \\ metis_tac []);

fun get_ind_thm_goal goals =
  let
    fun gen_ind_var_names [x] = ["P"]
      | gen_ind_var_names xs =
          List.tabulate (length xs,fn n => "P" ^ Int.toString n)
    val ind_vars = gen_ind_var_names goals
    fun make_pat (name,(t,_)) = let
      val p = mk_var(name,type_of t)
      val xs = list_dest dest_abs t
      val res = list_mk_comb(p,butlast xs)
      in (last xs, res) end
    fun replace_pat pat x tm = let
      val i = fst (match_term pat tm)
      in SOME (subst i x) end handle HOL_ERR _ => NONE;
    fun replace_pat_list [] tm = tm
      | replace_pat_list ((pat,x)::rest) tm =
          case replace_pat pat x tm of
            SOME x => x
          | NONE => replace_pat_list rest tm;
    fun rec_replace_pat_list xs tm =
      if is_comb tm then
        let val (x,y) = dest_comb tm
        in mk_comb(rec_replace_pat_list xs x, rec_replace_pat_list xs y)
           |> replace_pat_list xs end
      else if is_abs tm then
        let val (x,y) = dest_abs tm
        in mk_abs(x, rec_replace_pat_list xs y)
           |> replace_pat_list xs end
      else
        replace_pat_list xs tm
        handle HOL_ERR _ => tm
    val pats = map make_pat (zip ind_vars goals)
    (* val ((_,p),(x,(tt,_))) = hd (zip pats goals) *)
    val pss =
      map (fn ((_,p),(x,(tt,_))) =>
          (list_mk_forall (butlast (list_dest dest_abs x),p),
           list_mk_forall (butlast (list_dest dest_abs x),
            rec_replace_pat_list pats (concl tt)))) (zip pats goals)
    val ps = map fst pss |>
      map (hd o list_dest dest_comb o last o list_dest dest_forall)
    fun remove_pres tm =
      if is_forall tm then let
        val (v,tm) = dest_forall tm
        in mk_forall (v,remove_pres tm) end
      else if is_CONTAINER tm then rand tm
      else if is_neg tm andalso is_CONTAINER (rand tm) then
        mk_neg(rand (rand tm))
      else if is_conj tm then let
        val (x,y) = dest_conj tm
        in mk_conj (remove_pres x, remove_pres y) end
      else if is_imp tm then let
        val (x,y) = dest_imp tm
        in mk_imp (remove_pres x, remove_pres y) end
      else if is_var (repeat rator tm) then tm else T
    val ind_thm_goal =
      list_mk_forall(ps,
         mk_imp(remove_pres (list_mk_conj(map snd pss)),
                list_mk_conj(map fst pss)))
      |> QCONV (REWRITE_CONV [CONTAINER_def]) |> concl |> rand
  in ind_thm_goal end;

fun get_custom_ind_with_pre ind ind_thm_goal =
  if (* checks that the conclusion of the ind thm has an implication *)
     (the ind |> SPEC_ALL |> UNDISCH |> CONJUNCTS
              |> hd |> SPEC_ALL |> concl |> is_imp)
  then
    let
      val tmg = butlast (list_dest dest_forall (concl (the ind)))
      val tmi = butlast (list_dest dest_forall ind_thm_goal)
      val (s,i) = match_term (list_mk_pair tmg) (list_mk_pair tmi)
      val new_concl = subst s (inst i (last (list_dest dest_forall (concl (the ind)))))
                      |> dest_imp |> snd
      val old_hyp = last (list_dest dest_forall ind_thm_goal) |> dest_imp |> fst
      val ind_thm_goal = list_mk_forall (tmi,mk_imp(old_hyp, new_concl))
    in ind_thm_goal end
  else ind_thm_goal

fun guess_def_name original_def = let
  val def_tm = concl original_def
  val const_tm = original_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                              |> concl |> dest_eq |> fst |> repeat rator
  val const_name = const_tm |> dest_thy_const |> #Name
  val const_thy = const_tm |> dest_thy_const |> #Thy
  fun try_find_in thys = let
    val xs = DB.match thys def_tm
    val xs = filter (aconv def_tm o concl o #1 o snd) xs
    val ((thy,name),_) = first (fn x => Def = (x |> snd |> #2)) xs
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
            if size ts + 1 + size x <= k then
              consume (ts ^ " " ^ x) xs
            else (ts,x::xs)
      val (line,rest) = consume x xs
      in line :: break_lines_at k rest end;

fun break_line_at k prefix text = let
  val words = String.tokens (fn c => c = #" ") text
  val lines = break_lines_at k words
  in map (fn str => prefix ^ str) lines end;

fun print_unable_to_prove_ind_thm ind_goal_def original_def ml_name = let
  val name = guess_def_name original_def
  val thy_const = original_def |> SPEC_ALL |> CONJUNCTS |> hd |>
                  SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
                  |> dest_thy_const
  val _ = print ("\nERROR: Unable to prove induction for "^name^".")
  val _ = print ("\n")
  val ind_name = ind_goal_def |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val line_length = 53
  val _ = map print (break_line_at line_length "\n  "
    ("This induction goal has been left as an assumption on the theorem "^
     "returned by the translator. You can prove it with something like "^
     "the following before "^(#Name thy_const)^" is used in subsequent "^
     "translations."))
  val _ = print ("\n")
  val _ = print ("\nval res = translate_no_ind "^name^";")
  val _ = print ("\n")
  val _ = print ("\nTheorem " ^ ind_name ^ "[local]:")
  val _ = print ("\n  " ^ ind_name)
  val _ = print ("\nProof")
  val _ = print ("\n  once_rewrite_tac [fetch \"-\" \"" ^ ind_name ^ "_def\"]")
  val _ = print ("\n  \\\\ rpt gen_tac")
  val _ = print ("\n  \\\\ rpt (disch_then strip_assume_tac)")
  val _ = print ("\n  \\\\ match_mp_tac (latest_ind ())")
  val _ = print ("\n  \\\\ rpt strip_tac")
  val _ = print ("\n  \\\\ last_x_assum match_mp_tac")
  val _ = print ("\n  \\\\ rpt strip_tac")
  val _ = print ("\n  \\\\ gvs [FORALL_PROD]")
  val _ = print ("\nQED")
  val _ = print ("\n")
  val _ = print ("\nval _ = " ^ ind_name ^ " |> update_precondition;")
  val _ = print ("\n")
  val _ = map print (break_line_at line_length "\n  "
    ("Here `translate_no_ind` does the same as `translate` " ^
     "except it does not attempt the induction proof."))
  val _ = print ("\n")
  val _ = print ("\n")
  in () end;

datatype options = NoInd;
val options = ([]:options list);

local
  val latest_ind_thm = ref (NONE: thm option)
in
  fun set_latest_ind ind = (latest_ind_thm := ind);
  fun latest_ind () =
    case !latest_ind_thm of SOME th => th | _ => failwith "latest_ind";
end;

(* Instantiate constructor variables with their actual names. Names are
 * constructed differently depending on whether types originate in a module
 * which is not the one where translation currently takes place *)
fun instantiate_cons_name th =
  let
    val hyps = fst (dest_thm th)
    val lcons_tm =
      lookup_cons_def
      |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
    val is_lcons = can (match_term lcons_tm o repeat rator o fst o dest_eq)
    fun get_lcons (tm,acc) =
      if is_lcons tm then
        HOLset.add(acc, tm)
      else if can dest_comb tm then
        get_lcons (rand tm, get_lcons (rator tm, acc))
      else if can dest_abs tm then
        get_lcons (snd (dest_abs tm), acc)
      else
        acc
    val lcs = List.foldl get_lcons Term.empty_tmset hyps
    val vars = List.filter (can dest_var)
                           (List.map (rand o rator o fst o dest_eq)
                                     (HOLset.listItems lcs))
    fun inst_var tm =
      let
        val (nm, mods) = lookup_cons_name (fst (dest_var tm))
      in
        get_qualified_name mods nm
      end
    val tyis = List.map (fn tm => (tm |-> inst_var tm)) vars
  in
    INST tyis th
  end

(* assumes ind_goal is fst (dest_imp (concl th1)),
   packages it up as a constant and moves out it to assumptions *)
fun hide_ind_goal_rule name th1 =
  let
    val name_ind = name ^ "_ind"
    val ind_goal = th1 |> concl |> dest_imp |> fst
    fun mk_itself a = mk_type("itself",[a])
    val tys = type_vars_in_term ind_goal
    val vs = map mk_itself tys
    val ty = foldr (uncurry mk_fun_type) bool vs
    val args = map (curry mk_const "the_value") vs
    val lhs_ = foldl (fn (x,y) => mk_comb(y,x)) (mk_var(name_ind,ty)) args
    val def_tm = mk_eq(lhs_,ind_goal)
    val def_thm = zDefine [ANTIQUOTE def_tm]
  in
      ((th1 |> CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV (GSYM def_thm)))
            |> UNDISCH),
       def_thm)
  end

(*

val _ = (next_ml_names := ["+","+","+","+","+"]);

val def = Define `foo n = if n = 0 then 0:num else foo (n-1n)`

val def = listTheory.APPEND;
val def = sortingTheory.PART_DEF;
val def = mlstringTheory.explode_aux_def;

val def = Define `
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:int))`


val word64_msb_thm = Q.prove(
  `!w. word_msb (w:word64) =
         ((w && 0x8000000000000000w) = 0x8000000000000000w)`,
  blastLib.BBLAST_TAC);

val res = translate word64_msb_thm;

val def = (miscTheory.arith_shift_right_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [wordsTheory.dimindex_64]
                     |> CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV));

*)

fun translate_main options translate register_type def = (let

  val start = start_timing "translate_main"
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* preprocessing: reformulate def, read off info and register types *)
  val prep_start = start_timing "preprocessing+registering"
  val _ = register_term_types register_type (concl def)
  val (is_rec,defs,ind) = preprocess_def def
  (* this is usually a no-op, but preprocess_def might have introduced pairs *)
  val _ = register_term_types register_type (concl (LIST_CONJ defs))
  val _ = end_timing prep_start
  val info = map get_info defs
  val msg = comma (map (fn (fname,_,_,_,_) => fname) info)
  val _ = timing_message ("fnames: " ^ msg)
  (* derive deep embedding *)
  fun compute_deep_embedding info = let
    val _ = map (fn (fname,ml_fname,lhs,_,_) =>
                   install_rec_pattern lhs fname ml_fname) info
    val thms = map (fn (fname,ml_fname,lhs,rhs,def) =>
                      (fname,ml_fname,hol2deep rhs,def)) info
    val _ = uninstall_rec_patterns ()
    in thms end
  fun loop info =
    compute_deep_embedding info
    handle UnableToTranslate tm => let
      val _ = translate (find_def_for_const_wrapper tm)
      in loop info end

(*
val _ = map (fn (fname,ml_name,lhs,_,_) => install_rec_pattern lhs fname) info
val (fname,ml_name,lhs,rhs,def) = el 1 info
can (find_term is_arb) (rhs |> rand |> rator)
*)
  val thms = do_timing "doing loop" loop info
  val thms = do_timing "instantiating cons names"
    (map (fn (x0,x1,th,x2) => (x0,x1,instantiate_cons_name th,x2))) thms

  val _ = print ("Translating " ^ msg ^ "\n")
  (* postprocess raw certificates *)
(*
val (fname,ml_fname,th,def) = hd thms
*)
  fun optimise_and_abstract (fname,ml_fname,th,def) = let
    (* replace rhs with lhs *)
    val th = th |> CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def]))
    (* optimise generated code *)
    val th = MATCH_MP Eval_OPTIMISE (UNDISCH_ALL th)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th |> D
    (* abstract parameters *)
    val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
    val (th,v) = if (length rev_params = 0) then (th,T) else
                   (foldr (fn (v,th) => apply_Eval_Fun v th true) th
                      (rev (if is_rec then butlast rev_params else rev_params)),
                    last rev_params)
    in (fname,ml_fname,def,th,v) end
    handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "optimise_and_abstract" e)
  val thms = do_timing "optimise+abstract" (map optimise_and_abstract) thms
  (* final phase: extract precondition, perform induction, store cert *)
  val start_fin = start_timing "translate_main final phase"

  val (is_fun,results) = if not is_rec then let
    (* non-recursive case *)
    val _ = length thms = 1 orelse failwith "multiple non-rec definitions"
    val (code_def,(fname,ml_fname,def,th,v)) = abbrev_code (hd thms)
    val fname = get_unique_name fname
    (* remove parameters *)
    val th = D (clean_assumptions (D th))
    val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                        (SIMP_CONV std_ss [EVAL (mk_CONTAINER TRUE),
                                           EVAL (mk_CONTAINER FALSE)])) th
    val th = clean_assumptions (D th)
    val (lhs,rhs) = dest_eq (concl def)
    val pre_var = get_pre_var lhs fname
    val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
    val (th,pre) = extract_precondition_non_rec th pre_var
    val th = remove_Eq th
    (* simpliy EqualityType *)
    val th = SIMP_EqualityType_ASSUMS th
    (* store for later use *)
    val is_fun = code_def |> SPEC_ALL |> concl |> rand |> is_Fun
    val th = PURE_REWRITE_RULE[code_def] th
    val th =
      if is_fun then
        th
        |> INST [env_tm |-> cl_env_tm]
        |> MATCH_MP Eval_Fun_Var_intro
        |> SPEC (mlstringSyntax.mk_mlstring ml_fname)
        |> UNDISCH
      else th
    in
      (is_fun,[(fname,ml_fname,def,th,pre)])
    end
    else (* is_rec *) let

    (* abbreviate code *)
    val (code_defs,thms) = let val x = map abbrev_code thms
                           in (map fst x, map snd x) end
    (* introduce Recclosure *)
    fun mk_Recclosure_part (fname,ml_fname,def,th,v) = let
      val fname = ml_fname |> mlstringSyntax.mk_mlstring
      val name = v |> dest_var |> fst |> mlstringSyntax.mk_mlstring
      val body = th |> UNDISCH_ALL |> concl |> rator |> rand
      in pairSyntax.list_mk_pair[fname,name,body] end
    val parts = map mk_Recclosure_part thms
    val recc = listSyntax.mk_list(parts,type_of (hd parts))
(*
val (fname,ml_fname,def,th,v) = hd thms
*)
    val env2 = mk_var("env2", venvironment)
    val shadow_env = mk_var("shadow_env", venvironment)
    fun apply_recc (fname,ml_fname,def,th,v) = let
      val th = apply_Eval_Recclosure recc ml_fname v th
      val th = clean_assumptions th
      val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
      val th = INST [env2|->cl_env_tm,shadow_env|->cl_env_tm] th |> RW []
               |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [EVAL_T_F]))
      val th = clean_assumptions th
      in (fname,ml_fname,def,th) end
    val thms = map apply_recc thms

    (* collect precondition *)
    val thms = extract_precondition_rec thms

    (* construct ind goal *)
    fun get_goal (fname,ml_fname,def,th,pre) = let
      val th = REWRITE_RULE [] th
      val hs = hyp th
      val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
      val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
      val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
      in (hyp_tm,(th,(hs,goal))) end
    val goals = map get_goal thms

    (* generate ind theorem statement *)
    val ind_thm_goal = let
      val ind_thm_goal = get_ind_thm_goal goals
      in get_custom_ind_with_pre ind ind_thm_goal end

    (* instantiate ind thm *)
    val custom_ind_thm = ASSUME ind_thm_goal
    val lemma = SPECL (map fst goals) custom_ind_thm
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
      |> REWRITE_RULE [CONTAINER_def]
    val lemma1 = CONV_RULE (DEPTH_CONV BETA_CONV) (LIST_CONJ
      (map (fn (x,(tt,_)) => GENL (butlast (list_dest dest_abs x)) tt) goals))
      |> REWRITE_RULE [CONTAINER_def]
    val g0 = concl lemma1
    val g1 = fst (dest_imp (concl lemma))
    val lemma1 = if aconv g0 g1 then lemma1 else let
      val gs = mk_imp (g0,g1)
      val pre_defs = thms |> map (fn x => case (#5 x) of NONE => TRUTH | SOME t => t)
      val lem = auto_prove "unroll_pre_in_ind" (gs,
        rpt strip_tac
        \\ TRY (match_mp_tac PreImp_LEMMA
                \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV pre_defs))
                \\ strip_tac)
        \\ last_x_assum match_mp_tac
        \\ rewrite_tac [CONTAINER_def]
        \\ rpt strip_tac
        \\ TRY (
          TRY (last_x_assum match_mp_tac)
          \\ asm_rewrite_tac [] \\ res_tac
          \\ fs [] \\ NO_TAC)
        \\ gvs[])
      in MP lem lemma1 end
    val th = MP lemma lemma1

    (* attempt to prove induction assumption *)
    val _ = set_latest_ind ind
    val th = if mem NoInd options then let
               val name = thms |> hd |> #1
               val th1 = DISCH ind_thm_goal th
               in fst (hide_ind_goal_rule name th1) end
             else (MP (DISCH ind_thm_goal th) (prove_ind_thm ind ind_thm_goal)
                   handle HOL_ERR _ => let
                     val (_,ml_name,_,_,_) = hd thms
                     val name = thms |> hd |> #1
                     val th1 = DISCH ind_thm_goal th
                     val (th2,ind_goal_def) = hide_ind_goal_rule name th1
                     in (print_unable_to_prove_ind_thm ind_goal_def original_def ml_name;
                         th2)
                   end)

    val results = th |> CONJUNCTS |> map SPEC_ALL
(*
val (th,(fname,ml_fname,def,_,pre)) = hd (zip results thms)
*)
    (* clean up *)
    fun fix (th,(fname,ml_fname,def,_,pre)) = let
      val th = let
        val thi = MATCH_MP IMP_PreImp_THM th
        val thi = CONV_RULE ((RATOR_CONV o RAND_CONV)
                    (ONCE_REWRITE_CONV [force_thm_the pre] THENC
                     SIMP_CONV std_ss [PRECONDITION_def])) thi
        val thi = MP thi TRUTH
        in thi end handle HOL_ERR _ => th
      val th = RW [PreImp_def] th |> UNDISCH_ALL
      val th = remove_Eq th
      val th = SIMP_EqualityType_ASSUMS th
      val th = th |> DISCH_ALL |> REWRITE_RULE ((GSYM AND_IMP_INTRO)::code_defs) |> UNDISCH_ALL
      in (fname,ml_fname,def,th,pre) end
    val results = map fix (zip results thms)
    val _ = map (delete_const o fst o dest_const o fst o dest_eq o concl) code_defs
  in (true,results) end

  val _ = end_timing start_fin

  fun check results = let
    val th = LIST_CONJ (map #4 results)
    val f = can (find_term (can (match_term (get_term "WF")))) (th |> D |> concl)
    in if f then failwith "WF" else (is_rec,is_fun,results) end
  in check results end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end)
  handle e => let
   fun get_name clause = if is_const clause then fst (dest_const clause)
    else if is_var clause then "var:" ^ fst (dest_var clause)
    else if is_eq clause then get_name (lhs clause)
    else get_name (rator clause)
   val names =
     def |> SPEC_ALL |> CONJUNCTS |> map (get_name o concl)
         |> mk_set handle HOL_ERR _ => ["<unknown name>"]
   val _ = print ("Failed translation: " ^ comma names ^ "\n")
   in Portable.reraise e end
  handle (e as HOL_ERR _) => raise (wrap_exn "ml_translatorLib" "translate_main" e)

(*
val def = Define `d = [5:num]`
val options = tl [NoInd]
val options = [NoInd]
*)

fun translate_options options def =
  let
    val start = start_timing "translation"

    val (is_rec,is_fun,results) =
      translate_main options (translate_options options) register_type def

    val () =
      if !generate_sigs then
        let val _ = do_timing "generate_sig_thms" generate_sig_thms results
        in () end
      else ()
  in
    if is_rec then
    let
      val start_rec = start_timing "processing rec case"
      val recc = results |> map (fn (fname,_,def,th,pre) => th) |> hd |> hyp
        |> first (can (find_term (aconv Recclosure_tm)))
        |> rand |> rator |> rand
      val ii = INST [cl_env_tm |-> get_curr_env()]
      val v_names = map (fn x => find_const_name (#1 x ^ "_v")) results
      val _ = ml_prog_update (add_Dletrec unknown_loc recc v_names)
      val v_defs = List.take(get_curr_v_defs (), length v_names)
      val jj = INST [env_tm |-> get_curr_env()]
  (*
      val (fname,ml_fname,def,th,pre) = hd results
  *)
      fun inst_envs (fname,ml_fname,def,th,pre) = let
        val lemmas = LOOKUP_VAR_def :: map GSYM v_defs
        val th = th |> ii |> jj |> D |> REWRITE_RULE lemmas
                    |> SIMP_RULE std_ss [Eval_Var]
                    |> SIMP_RULE std_ss [lookup_var_def]
                    |> clean_assumptions |> UNDISCH_ALL
        val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
        val _ = add_v_thms (fname,ml_fname,th,pre_def)
        in allowing_rebind save_thm(fname ^ "_v_thm", th) end
      val v_thm = map inst_envs results |> LIST_CONJ
      val v_thm = v_thm |> DISCH_ALL
                  |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]
                  |> UNDISCH_ALL
      val _ = (end_timing start_rec; end_timing start)
      in v_thm end
    else (* not is_rec *)
    let
      val (fname,ml_fname,def,th,pre) = hd results
    in
      if is_fun then let
        val start_fun = start_timing "processing fun case"
        val th = th |> INST [cl_env_tm |-> get_curr_env()]
        val n = ml_fname |> mlstringSyntax.mk_mlstring
        val lookup_var_assum = th |> hyp
          |> first (can (match_term(LOOKUP_VAR_def |> SPEC n |> SPEC_ALL |> concl |> lhs)))
        val lemma = th |> DISCH lookup_var_assum
                       |> GEN env_tm
                       |> MATCH_MP Eval_Var_LOOKUP_VAR_elim
                       |> D |> clean_assumptions |> UNDISCH_ALL
        val v = lemma |> concl |> rand |> rator |> rand
        val exp = lemma |> concl |> rand |> rand
        val v_name = find_const_name (fname ^ "_v")
        val _ = ml_prog_update (add_Dlet_Fun unknown_loc n v exp v_name)
        val v_def = hd (get_curr_v_defs ())
        val v_thm = lemma |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def)))
        val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
        val _ = add_v_thms (fname,ml_fname,v_thm,pre_def)
        val _ = (end_timing start_fun; end_timing start)
        in allowing_rebind save_thm(fname ^ "_v_thm",v_thm) end
      else let (* not is_fun *)

        val start_v = start_timing "processing val case"
        val th = th |> INST [env_tm |-> get_curr_env()]
        val th = UNDISCH_ALL (clean_assumptions (D th))
        val curr_state = get_curr_state()
        val curr_refs =
          mk_icomb(state_refs_tm,curr_state)
        val curr_refs_eq = EVAL curr_refs
        val vs = free_vars (concl th)
        fun aux (v,th) = let
          val (ss,ii) = match_term v UNIT_TYPE
          in INST ss (INST_TYPE ii th) end
        val th1 = foldl aux th vs
        val lemma =
          Eval_constant
          |> ISPEC curr_refs
          |> PURE_REWRITE_RULE[curr_refs_eq]
          |> C MATCH_MP th1
          |> D |> SIMP_RULE std_ss [PULL_EXISTS_EXTRA]
        val v_name = find_const_name (fname ^ "_v")
        val refs_name = find_const_name (fname  ^ "_refs")
        val v_thm_temp = new_specification("temp",[v_name,refs_name],
                           lemma |> SIMP_RULE std_ss [PULL_EXISTS_EXTRA])
                         |> PURE_REWRITE_RULE [PRECONDITION_def] |> UNDISCH_ALL
        val ref_def = CONJUNCT2 v_thm_temp
        val _ = let
          val c = SIMP_CONV std_ss [EVERY_DEF,MAP,SND,no_change_refs_def] THENC EVAL
          val ref_def_lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) c) ref_def
          val ref_def = MP ref_def_lemma TRUTH
          in allowing_rebind save_thm(refs_name ^ "_def", ref_def) end
          handle HOL_ERR _ => TRUTH
        val v_thm_temp = CONJUNCT1 v_thm_temp
        val _ = delete_binding "temp"
        val v_thm = MATCH_MP Eval_evaluate_IMP (CONJ th v_thm_temp)
                    |> SIMP_EqualityType_ASSUMS |> UNDISCH_ALL
        val eval_thm = v_thm_temp |> PURE_REWRITE_RULE[GSYM curr_refs_eq]
                       |> MATCH_MP evaluate_empty_state_IMP
        val var_str = ml_fname
        val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
        val _ = ml_prog_update (add_Dlet eval_thm var_str)
        val _ = add_v_thms (fname,var_str,v_thm,pre_def)
        val v_thm = v_thm |> DISCH_ALL
                    |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]
                    |> UNDISCH_ALL
        val _ = (end_timing start_v; end_timing start)
        in allowing_rebind save_thm(fname ^ "_v_thm",v_thm) end end
  end

val translate = translate_options [];
val translate_no_ind = translate_options [NoInd];

fun abs_translate_options options def =
  let
    val (is_rec,is_fun,results) =
        translate_main options (abs_translate_options options) abs_register_type def
    (*
      val (fname,ml_fname,def,th,preopt) = hd results
    *)
    fun mapthis (fname,ml_fname,def,th,preopt) =
    let
      val pre = case preopt of NONE => TRUTH | SOME pre_def => pre_def
      val () = add_v_thms (fname,ml_fname,th,pre)
    in
      th
    end
  in
    LIST_CONJ (map mapthis results)
  end

val abs_translate = abs_translate_options [];
val abs_translate_no_ind = abs_translate_options [NoInd];

val _ = set_translator translate;

(* TODO: make desired a more efficient datastructure *)
fun get_desired_v_thms desired [] acc = acc
  | get_desired_v_thms desired (vth::vths) acc =
    let
      val (found,desired) = List.partition (same_const (get_const vth)) desired
    in
      if List.null found
      then get_desired_v_thms desired vths acc
      else
      let
        val hyps = hyp (get_cert vth)
        val deps =
          List.mapPartial (total (rand o rand o assert is_Eval)) hyps
        val deps2 =
          List.mapPartial (total (rand o rand o assert is_Eval o rand o #2 o strip_forall)) hyps
      in
        get_desired_v_thms (desired @ deps @ deps2) vths (vth::acc)
      end
    end

fun prove_Eval_assumptions th =
  let
    val eval_assums = filter (can (find_term is_Eval)) (hyp th)
    (* val tm = el 1 eval_assums *)
    fun prove_Eval_assum tm =
      let
        val th1 =
          (ONCE_DEPTH_CONV(REWR_CONV Eval_Var_nsLookup THENC nsLookup_conv)) tm
        val const =
          th1 |> concl |> rand |> strip_forall |> #2 |> repeat (#2 o dest_imp) |> rator |> rand
        val cert = get_cert (get_bare_v_thm const)
        val cert' = D cert |> MATCH_MP EQ_COND_INTRO
      in ONCE_REWRITE_RULE[cert'] th1 |> SIMP_RULE bool_ss [] end
    fun foldthis (tm,th) = PROVE_HYP (prove_Eval_assum tm) th
  in
    foldl foldthis th eval_assums
  end

(* TODO: consolidate with concrete-mode translate? *)
fun add_dec_for_v_thm ((fname,ml_fname,tm,cert,pre,mn),state) =
  let
    val vname = assert is_Var (cert |> concl |> rator |> rand) |> rand |> rand
    val LOOKUP_VAR_pat = LOOKUP_VAR_def |> SPEC vname |> SPEC_ALL |> concl |> lhs
    val cert = cert |> DISCH_ALL |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
    val lookup_var_hyp = first (can (match_term LOOKUP_VAR_pat)) (hyp cert)
    val v = rand lookup_var_hyp
  in
    if is_Recclosure v
    then
      let
        val recc = v |> rator |> rand
        val recc_names = recc |> listSyntax.dest_list |> #1
                              |> map (#1 o pairSyntax.dest_pair)
        val previous_v =
          lookup_var_def
          |> ISPECL [el 1 recc_names, get_env state]
          |> concl |> lhs |> EVAL
          |> concl |> rhs
        val already_defined = optionSyntax.is_some previous_v
        val cl_env =
          if already_defined
          then
              Lib.first
                (same_const (optionSyntax.dest_some previous_v) o lhs o concl)
                (get_v_defs state)
              |> concl |> rhs |> funpow 2 rator |> rand
          else get_env state
        val state' =
          if already_defined then state else
          let
            val v_names =
              map (fn x => find_const_name (mlstringSyntax.dest_mlstring x ^ "_v"))
                  recc_names
          in add_Dletrec unknown_loc recc v_names state end
        val lemmas = LOOKUP_VAR_def :: map GSYM (get_v_defs state')
        val th = cert
                  |> INST[cl_env_tm |-> cl_env, env_tm |-> get_env state']
                  |> prove_Eval_assumptions
                  |> D |> REWRITE_RULE lemmas
                  |> SIMP_RULE std_ss [Eval_Var]
                  |> SIMP_RULE std_ss [lookup_var_def]
                  |> clean_assumptions |> UNDISCH_ALL
        val _ = replace_v_thm tm th
        val _ = allowing_rebind save_thm(fname ^ "_v_thm", th)
      in state' end
    else if is_Closure v
    then
      let
        val cl_env = get_env state
        val th = cert |> DISCH lookup_var_hyp
                 |> GEN env_tm
                 |> MATCH_MP Eval_Var_LOOKUP_VAR_elim
        val v_name = find_const_name (fname ^ "_v")
        val (_,x,exp) = dest_Closure v
        val state' = add_Dlet_Fun unknown_loc (mlstringSyntax.mk_mlstring ml_fname) x exp v_name state
        val lemmas = LOOKUP_VAR_def :: map GSYM (get_v_defs state')
        val th = cert
                  |> INST[cl_env_tm |-> cl_env, env_tm |-> get_env state']
                  |> prove_Eval_assumptions
                  |> D |> REWRITE_RULE lemmas
                  |> SIMP_RULE std_ss [Eval_Var]
                  |> SIMP_RULE std_ss [lookup_var_def]
                  |> clean_assumptions |> UNDISCH_ALL
        val _ = replace_v_thm tm th
        val _ = save_thm(fname ^ "_v_thm", th)
      in state' end
    else failwith "bad v_thm"
  end
  handle HOL_ERR _ =>
  let
    val code = concl cert |> rator |> rand
    val curr_state = get_state state
    val curr_env = get_env state
    val curr_refs = mk_icomb(state_refs_tm,curr_state)
    val curr_refs_eq = EVAL curr_refs
    val th = cert |> INST[env_tm |-> curr_env]
             |> prove_Eval_assumptions
             |> D |> clean_assumptions
             |> UNDISCH_ALL
    val lemma =
      Eval_constant
      |> ISPEC curr_refs
      |> PURE_REWRITE_RULE[curr_refs_eq]
      |> C MATCH_MP th
      |> D |> SIMP_RULE std_ss [PULL_EXISTS_EXTRA]
    val v_name = find_const_name (fname ^ "_v")
    val refs_name = find_const_name (fname  ^ "_refs")
    val v_thm_temp = new_specification("temp",[v_name,refs_name],lemma) |> UNDISCH_ALL
    val _ = delete_binding "temp"
    val v_thm = MATCH_MP Eval_evaluate_IMP (CONJ th v_thm_temp)
                |> SIMP_EqualityType_ASSUMS |> UNDISCH_ALL
    val eval_thm =
      v_thm_temp
      |> PURE_REWRITE_RULE[GSYM curr_refs_eq]
      |> MATCH_MP evaluate_empty_state_IMP
    val state' = add_Dlet eval_thm ml_fname state
    val _ = replace_v_thm tm v_thm
    val _ = allowing_rebind save_thm(fname ^ "_v_thm", v_thm)
  in state' end

fun concretise_main desired_tms = let
  val desired_v_thms =
    case desired_tms of
      NONE => List.rev (get_v_thms())
    | SOME tms => get_desired_v_thms tms (get_v_thms()) []
  val dprogs = pop_deferred_dprogs ()
  in
    ml_prog_update (C (foldl (uncurry (C ml_progLib.add_prog I))) dprogs);
    ml_prog_update (C (foldl add_dec_for_v_thm) desired_v_thms)
  end

fun concretise tms = concretise_main (SOME tms)
fun concretise_all () = concretise_main NONE

(*
val _ = show_assums := true

val () = reset_translation();
val _ = Datatype`num_or_list = Num num | List ('a list)`;
val len_def = Define`len (Num n) = n ∧ len (List ls) = LENGTH ls`;
val res = abs_register_type``:'a num_or_list``;
val res = abs_translate LENGTH;
val res = abs_translate APPEND;
val res = abs_translate len_def;
val test_def = Define`test = len (List [3n])`;
val res = abs_translate test_def;

val res = concretise [``test``]
val thm = get_thm (get_ml_prog_state())

val () = reset_translation();
val even_def = Define`
  (even 0n = T) /\ (even (SUC n) = odd n) /\
  (odd 0 = F) /\ (odd (SUC n) = even n)`;
val res = abs_translate even_def;
val res = abs_translate sortingTheory.PART_DEF
val res = abs_translate sortingTheory.PARTITION_DEF
val res = abs_translate APPEND
val res = abs_translate MAP
val res = abs_translate LENGTH
val res = abs_translate sortingTheory.QSORT_DEF
val res = abs_translate HD;
val qsort_test_def = Define`qsort_test = (even (HD (QSORT (\x y. x <= y) [1n;3;2])) ∧ odd 1n)`
val res = abs_translate qsort_test_def;

(* TODO: better support for preconditions with mutual recursion: the
   preconditions should only apply to the function they are about *)
(*
val even_def = Define`
  (even 0n = T) /\ (even (SUC n) = odd n) /\
  (odd 0 = ARB) /\ (odd (SUC n) = even n)`;
val res = abs_translate even_def;
*)
(*
val even_def = Define`
  (even n = case n of 0 => T | SUC n => odd n) /\
  (odd n = case n of SUC n => even n)`;
val res = abs_translate even_def;
*)
(*
val even_def = Define`
  (even n = case n of 0 => T | SUC n => odd n) /\
  (odd n = case n of 0 => 0 = n DIV n | SUC n => even n)`;
val res = abs_translate even_def;
*)

1. put in deferred_dprogs (after filtering? in reverse order?)
2. do add_dec_for_v_thm for each desired_v_thms

val test_def = Define`test = 3n`;
val res = abs_translate test_def;
val test2_def= Define`test2 = test + test`;
val res = abs_translate test2_def;

val _ = Datatype`foo = NF | CO num foo`
val res = abs_register_type``:foo``
val lenfoo_def = Define`lenfoo NF = 0 /\ lenfoo (CO _ ls) = 1 + lenfoo ls`
val res = abs_translate lenfoo_def
get_thm (!prog_state)

n.b.
  The concrete mode (translate, register_type, register_exn_type) is only here
  temporarily for backwards compatibility.
  It should be replaced by the abstract mode (abs_translate, abs_register_type,
  abs_register_exn_type) plus the linearisation phase.

TODO:
  - add support for modules

val state = get_ml_prog_state()
val (fname,ml_fname,tm,cert,pre,mn) = el 8 desired_v_thms
val state' = add_dec_for_v_thm (el 8 desired_v_thms,state)
val state = state'

*)

(*
  val xs = get_v_thms ()
  val (_,_,c_tm,_,_,_) = hd (tl (get_v_thms ()))
*)
fun clean_v_thms () = let
  val inst_env = INST [env_tm |-> get_curr_env()]
  fun can_lookup_constant (_,_,c_tm,_,_,_) =
    ((can clean_assumptions_quietly (D (inst_env (lookup_v_thm c_tm))))
     handle Interrupt => raise Interrupt | _ => false)
  val delete_count = filter_v_thms can_lookup_constant
  in if delete_count < 1 then () else
       print ("Removed " ^ int_to_string delete_count ^
              " unreachable v thms from translator's state.\n") end;
val _ = add_finalise_function clean_v_thms;

(*
val name = "hello"
val tm = ``1:num``
*)
fun declare_new_ref name tm = let
  val init_val_th = hol2deep tm
  val ml_thm = get_ml_prog_state ()
                 |> ml_progLib.clean_state
                 |> ml_progLib.get_thm
  val state_tm = ml_thm |> concl |> rand
  val env_tm = MATCH_MP ML_code_Dlet_var ml_thm
    |> REWRITE_RULE [ML_code_env_def]
    |> SPEC_ALL |> concl |> rand |> rator |> rand |> rand
  val env_var = init_val_th |> concl |> rator |> rator |> rand
  val init_val_th1 = INST [env_var|->env_tm] init_val_th |> D |> clean_assumptions
  val _ = MP (D init_val_th1) TRUTH handle HOL_ERR _ =>
          failwith "translate_new_ref failed: translation of init value has preconditions"
  val th = MATCH_MP new_ref_thm init_val_th1
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = MP th TRUTH handle HOL_ERR _ =>
          failwith "translate_new_ref failed: init value not simple enough to prove no refs changed during evaluation of init value"
  val lemma = ISPEC state_tm (Q.GEN `s` evaluate_empty_state_IMP)
  val s_refs_pat =  evaluate_empty_state_IMP |> concl |> rand |> rator |> rand
      |> rator |> rand |> rand |> rator |> rand
  val tm = find_term (can (match_term s_refs_pat)) (concl lemma)
  val rw_lemma = EVAL tm
  val lemma1 = PURE_REWRITE_RULE [rw_lemma] lemma
  val th = th |> SPEC (rw_lemma |> concl |> rand)
  val res = new_specification(name ^ "_def",[name ^ "_init_val",name ^ "_loc"],th)
  val eval_rel_thm = CONJUNCT1 res
  val v_def = CONJUNCT2 res
  val th = MATCH_MP lemma1 eval_rel_thm |> PURE_REWRITE_RULE [APPEND]
  (* add_Dlet th name (get_ml_prog_state ()) *)
  val _ = ml_prog_update (add_Dlet th name)
  in allowing_rebind save_thm(name ^ "_def",v_def) end

end
