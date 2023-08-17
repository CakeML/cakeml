(*
  Apply the monadic translator to the overloading Candle kernel to
  generate the deeply embedded CakeML code for the kernel. As a side
  effect, the monadic translator proves certificate theorems that
  state a formal connection between the generated code and the input
  HOL functions.
*)
open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory evaluateTheory semanticPrimitivesTheory
open ml_progLib ml_progTheory evaluateTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib
open holKernelTheory holKernelProofTheory
open basisProgTheory
open holAxiomsSyntaxTheory (* for setting up the context *)
local open holKernelPmatchTheory in end

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "ml_hol_kernel_funsProg";
val _ = translation_extends "basisProg"

val _ = (use_full_type_names := false);

val _ = hide "abs";

val _ = ml_prog_update (open_module "Kernel");

Type state = ``:'ffi semanticPrimitives$state``

(* construct type refinement invariants *)

val _ = register_type ``:type``;

(* check ``:type`` is known to be an EqualityType *)
val EqualityType_TYPE = EqualityType_rule [] ``:type``;

val _ = register_type ``:term``;
val _ = register_exn_type ``:hol_exn``;
val _ = register_type ``:thm``;
val _ = register_type ``:update``;
val _ = register_type ``:ext_step``;
val HOL_EXN_TYPE_def = theorem"HOL_EXN_TYPE_def";

val _ = ml_prog_update open_local_block;

(* Initialize the translation *)

val init_type_constants_def = Define `
  init_type_constants = [(strlit"bool",0); (strlit"fun",2:num)]`;

val init_term_constants_def = Define `
  init_term_constants = [(strlit"=",
    Tyapp (strlit"fun")
      [Tyvar (strlit"A");
       Tyapp (strlit"fun")
         [Tyvar (strlit"A");
          Tyapp (strlit"bool") []]])]`;

val init_axioms_def = Define `
  init_axioms = []:thm list`;

val init_context_def = Define `
  init_context = ^(rhs(concl(holSyntaxTheory.init_ctxt_def)))`;

val refs_init_list = [
  ("the_type_constants", init_type_constants_def, get_the_type_constants_def,
  set_the_type_constants_def),
  ("the_term_constants", init_term_constants_def, get_the_term_constants_def,
  set_the_term_constants_def),
  ("the_axioms", init_axioms_def, get_the_axioms_def, set_the_axioms_def),
  ("the_context", init_context_def, get_the_context_def, set_the_context_def)
];

val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

val raise_functions = [raise_Fail_def, raise_Clash_def];
val handle_functions = [handle_Fail_def, handle_Clash_def];
val exn_functions = zip raise_functions handle_functions;

val store_hprop_name = "HOL_STORE";
val state_type = ``:hol_refs``
val exn_ri_def = HOL_EXN_TYPE_def

val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
                                              rarrays_init_list
                                              farrays_init_list
                                              store_hprop_name
                                              state_type
                                              exn_ri_def
                                              exn_functions
                                              []
                                              NONE
                                              NONE;

(* mechanism for adding type checking annotations *)

val pure_seq_intro = prove(“x = y ⇒ ∀z. x = pure_seq z y”, fs [pure_seq_def]);

fun mlstring_check s = “mlstring$strlen ^s”
fun type_check ty = “case ^ty of Tyvar _ => () | _ => abc” |> subst [“abc:unit”|->“()”]
fun term_check tm = “case ^tm of Const _ _ => () | _ => abc” |> subst [“abc:unit”|->“()”]

val t1 = type_check “t1:type”
val t2 = type_check “t2:type”
val tm = term_check “tm:term”
val tm' = term_check “tm':term”

Definition check_ty_def:
  check_ty [] = () ∧
  check_ty (t1::l) = pure_seq ^t1 (check_ty l)
End

Definition check_tm_def:
  check_tm [] = () ∧
  check_tm (tm::l) = pure_seq ^tm (check_tm l)
End

Definition check_ty_ty_def:
  check_ty_ty [] = () ∧
  check_ty_ty ((t1,t2)::l) = pure_seq ^t1 (pure_seq ^t2 (check_ty_ty l))
End

Definition check_tm_tm_def:
  check_tm_tm [] = () ∧
  check_tm_tm ((tm,tm')::l) = pure_seq ^tm (pure_seq ^tm' (check_tm_tm l))
End

fun ty_list_check ty = “check_ty ^ty”;
fun tm_list_check tm = “check_tm ^tm”;
fun ty_ty_list_check tyty = “check_ty_ty ^tyty”;
fun tm_tm_list_check tmtm = “check_tm_tm ^tmtm”;

fun guess_check tm =
  if type_of tm = “:mlstring” then mlstring_check else
  if type_of tm = “:type” then type_check else
  if type_of tm = “:term” then term_check else
  if type_of tm = “:type list” then ty_list_check else
  if type_of tm = “:term list” then tm_list_check else
  if type_of tm = “:(type # type) list” then ty_ty_list_check else
  if type_of tm = “:(term # term) list” then tm_tm_list_check else fail()

fun add_type_check v f def = let
  val def = SPEC_ALL def
  val tm = f v
  in MATCH_MP pure_seq_intro def |> ISPEC tm end

fun check [] def = SPEC_ALL def
  | check (v::vs) def =
    let
      val def = check vs def
      val tm = Parse.parse_in_context (free_vars (concl def)) v
      val f = guess_check tm
      val def = add_type_check tm f def
    in def end

val res = translate check_ty_def;
val res = translate check_tm_def;
val res = translate check_ty_ty_def;
val res = translate check_tm_tm_def;

(**************************************************************************************************)
(**************************************************************************************************)
(* --- perform translation --- *)

(* TODO: want builtin support for these *)
(*
val res = translate mlstringTheory.explode_aux_def;
val res = translate mlstringTheory.explode_def;
val explode_aux_side_thm = Q.prove(
  `∀s n m. n + m = strlen s ==> explode_aux_side s n m `,
  Induct_on`m` \\ rw[Once (theorem"explode_aux_side_def")]);
val explode_side_thm = Q.prove(
  `explode_side x`,
  rw[definition"explode_side_def",explode_aux_side_thm])
  |> update_precondition
val res = translate mlstringTheory.strcat_def;
*) (* TODO temporary *)

val res = translate stringTheory.string_lt_def
val res = translate stringTheory.string_le_def
val res = translate totoTheory.TO_of_LinearOrder

(* -- *)
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holSyntaxExtraTheory.itlist_def;
val res = translate holSyntaxExtraTheory.union_def;

val _ = ml_prog_update open_local_in_block;

val res = translate (check [‘v’] mk_vartype_def);
val res = translate (check [‘t’] is_type_def);
val res = translate (check [‘t’] is_vartype_def);

val _ = ml_prog_update open_local_block;

val res = translate rev_assocd_def;

Definition call_type_subst_def[simp]:
  call_type_subst i ty = holKernel$type_subst i ty
End
val _ = (next_ml_names := ["type_subst_aux"]);
val res = translate holKernelTheory.type_subst_def;
val _ = (next_ml_names := ["type_subst"]);

val _ = ml_prog_update open_local_in_block;

val res = translate (check [‘i’,‘ty’] call_type_subst_def);

val _ = ml_prog_update open_local_block;

val res = translate alphavars_def;
val res = translate holKernelPmatchTheory.raconv_def;

Theorem raconv_side = Q.prove(`
  !x y z. raconv_side x y z`,
  ho_match_mp_tac holKernelTheory.raconv_ind
  \\ ntac 4 (rw [Once (fetch "-" "raconv_side_def")]))
  |> update_precondition;

val res = translate (check [‘tm1’,‘tm2’] aconv_def);

val _ = ml_prog_update open_local_in_block;

val res = translate (check [‘x’] holKernelPmatchTheory.is_var_def);
val res = translate (check [‘x’] holKernelPmatchTheory.is_const_def);
val res = translate (check [‘x’] holKernelPmatchTheory.is_abs_def);
val res = translate (check [‘x’] holKernelPmatchTheory.is_comb_def);
val res = translate (check [‘v’,‘ty’] mk_var_def);

val _ = ml_prog_update open_local_block;

Definition call_frees_def[simp]:
  call_frees tm = holSyntaxExtra$frees tm
End
val _ = (next_ml_names := ["frees_aux"]);
val res = translate holSyntaxExtraTheory.frees_def;
val _ = (next_ml_names := ["frees"]);

Definition call_freesin_def[simp]:
  call_freesin acc tm = freesin acc tm
End
val _ = (next_ml_names := ["freesin_aux"]);
val res = translate (freesin_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = (next_ml_names := ["freesin"]);

Definition call_vfree_in_def[simp]:
  call_vfree_in v tm = vfree_in v tm
End
val _ = (next_ml_names := ["vfree_in_aux"]);
val res = translate holKernelPmatchTheory.vfree_in_def;
val _ = (next_ml_names := ["vfree_in"]);

Definition call_tyvars_def[simp]:
  call_tyvars x = holKernel$tyvars x
End
val _ = (next_ml_names := ["tyvars_aux"]);
val res = translate holKernelTheory.tyvars_def;
val _ = (next_ml_names := ["tyvars"]);

Definition call_type_vars_in_term_def[simp]:
  call_type_vars_in_term tm = type_vars_in_term tm
End
val _ = (next_ml_names := ["type_vars_in_term_aux"]);
val res = translate type_vars_in_term_def;
val _ = (next_ml_names := ["type_vars_in_term"]);

Definition call_variant_def[simp]:
  call_variant avoid v = variant avoid v
End
val _ = (next_ml_names := ["variant_aux"]);
val res = translate holSyntaxExtraTheory.variant_def;
val _ = (next_ml_names := ["variant"]);

val res = translate vsubst_aux_def;

val _ = ml_prog_update open_local_in_block;

val res = translate (check [‘v’,‘tm’] call_vfree_in_def);
val res = translate (check [‘acc’,‘tm’] call_freesin_def);
val res = translate (check [‘tm’] call_frees_def);
val res = translate (check [‘tml’] freesl_def);
val res = translate (check [‘x’] call_tyvars_def);
val res = translate (check [‘tm’] call_type_vars_in_term_def);
val res = translate (check [‘avoid’,‘v’] call_variant_def);

val _ = ml_prog_update open_local_block;

val res = translate (check [‘tm’ ]holKernelPmatchTheory.is_eq_def);

val _ = ml_prog_update open_local_in_block;

val res = translate dest_thm_def;
val res = translate hyp_def;
val res = translate concl_def;

val _ = ml_prog_update open_local_block;

val type_compare_def = tDefine "type_compare" `
  (type_compare t1 t2 =
     case (t1,t2) of
     | (Tyvar x1,Tyvar x2) => mlstring$compare x1 x2
     | (Tyvar x1,Tyapp _ _) => Less
     | (Tyapp x1 a1,Tyvar _) => Greater
     | (Tyapp x1 a1,Tyapp x2 a2) =>
         case mlstring$compare x1 x2 of
         | Equal => type_list_compare a1 a2
         | other => other) /\
  (type_list_compare ts1 ts2 =
     case (ts1,ts2) of
     | ([],[]) => Equal
     | ([],t2::ts2) => Less
     | (t1::ts1,[]) => Greater
     | (t1::ts1,t2::ts2) =>
         (case type_compare t1 t2 of
          | Equal => type_list_compare ts1 ts2
          | other => other))`
  (WF_REL_TAC `measure (\x. case x of
                  INR (x,_) => type1_size x
                | INL (x,_) => type_size x)`)

val type_cmp_thm = Q.prove(
  `(type_cmp = type_compare) /\
    (list_cmp type_cmp = type_list_compare)`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "type_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.type_cmp_thm]
  \\ ONCE_REWRITE_TAC [type_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def,ternaryComparisonsTheory.list_compare_def])
  |> CONJUNCT1;

val _ = add_preferred_thy "-";
val _ = save_thm("type_cmp_ind",
          (fetch "-" "type_compare_ind") |> RW [GSYM type_cmp_thm]);
val res = translate (type_compare_def |> RW [GSYM type_cmp_thm]);

val term_compare_def = Define `
  term_compare t1 t2 =
     case (t1,t2) of
       (Var x1 ty1,Var x2 ty2) =>
         (case mlstring$compare x1 x2 of
            Less => Less
          | Equal => type_cmp ty1 ty2
          | Greater => Greater)
     | (Var x1 ty1,Const v52 v53) => Less
     | (Var x1 ty1,Comb v54 v55) => Less
     | (Var x1 ty1,Abs v56 v57) => Less
     | (Const x1' ty1',Var v66 v67) => Greater
     | (Const x1' ty1',Const x2' ty2') =>
         (case mlstring$compare x1' x2' of
            Less => Less
          | Equal => type_cmp ty1' ty2'
          | Greater => Greater)
     | (Const x1' ty1',Comb v70 v71) => Less
     | (Const x1' ty1',Abs v72 v73) => Less
     | (Comb s1 t1,Var v82 v83) => Greater
     | (Comb s1 t1,Const v84 v85) => Greater
     | (Comb s1 t1,Comb s2 t2) =>
         (case term_compare s1 s2 of
            Less => Less
          | Equal => term_compare t1 t2
          | Greater => Greater)
     | (Comb s1 t1,Abs v88 v89) => Less
     | (Abs s1' t1',Var v98 v99) => Greater
     | (Abs s1' t1',Const v100 v101) => Greater
     | (Abs s1' t1',Comb v102 v103) => Greater
     | (Abs s1' t1',Abs s2' t2') =>
         case term_compare s1' s2' of
           Less => Less
         | Equal => term_compare t1' t2'
         | Greater => Greater`;

val term_cmp_thm = Q.prove(
  `term_cmp = term_compare`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "term_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.term_cmp_thm]
  \\ ONCE_REWRITE_TAC [term_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def])

val _ = add_preferred_thy "-";
val _ = save_thm("term_cmp_ind",
          (fetch "-" "term_compare_ind") |> RW [GSYM term_cmp_thm]);
val res = translate (term_compare_def |> RW [GSYM term_cmp_thm]);

val res = translate (check [‘ty’] holKernelPmatchTheory.codomain_def);
val res = translate holSyntaxTheory.typeof_def;
val res = translate holSyntaxTheory.ordav_def;
val res = translate holSyntaxTheory.orda_def;
val res = translate holSyntaxTheory.term_remove_def;
val res = translate holSyntaxTheory.term_union_def;

val def = try_def |> m_translate;
val def = holKernelTheory.assoc_def  (* rec *) |> m_translate;
val def = holKernelTheory.map_def    (* rec *) |> m_translate;
val def = holKernelTheory.forall_def (* rec *) |> m_translate;

val _ = ml_prog_update open_local_in_block;

val def = dest_type_def |> check [‘t’] |> m_translate;
val def = dest_vartype_def |> check [‘t’] |> m_translate;
val def = holKernelPmatchTheory.dest_var_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.dest_const_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.dest_comb_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.dest_abs_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.rator_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.rand_def |> check [‘tm’] |> m_translate;
val def = holKernelPmatchTheory.dest_eq_def |> check [‘tm’] |> m_translate;

val def = holKernelPmatchTheory.mk_abs_def |> check [‘bvar’,‘bod’] |> m_translate;
val def = get_type_arity_def |> check [‘s’] |> m_translate;
val def = mk_type_def |> check [‘tyop’,‘args’] |> m_translate;

val _ = ml_prog_update open_local_block;

val def = mk_fun_ty_def |> check [‘ty1’,‘ty2’] |> m_translate;

Definition call_type_of_def[simp]:
  call_type_of tm = type_of tm
End
val _ = (next_ml_names := ["type_of_aux"]);
val def = holKernelPmatchTheory.type_of_def |> m_translate; (* PMATCH *)
val _ = (next_ml_names := ["type_of"]);

val def = can_def |> m_translate;
val def = image_def |> m_translate;

val _ = ml_prog_update open_local_in_block;

val res = m_translate (check [‘tm’] call_type_of_def);
val def = get_const_type_def |> check [‘s’] |> m_translate;
val def = holKernelPmatchTheory.mk_comb_def |> check [‘f’,‘a’] |> m_translate;
val def = mk_const_def |> Q.SPEC ‘n’ |> check [‘n’,‘theta’] |> m_translate;

val _ = ml_prog_update open_local_block;

val fdM_def = new_definition("fdM_def",``fdM = first_dup``)
val fdM_intro = SYM fdM_def
val fdM_ind = save_thm("fdM_ind",REWRITE_RULE[MEMBER_INTRO]first_dup_ind)
val fdM_eqs = REWRITE_RULE[MEMBER_INTRO,fdM_intro]first_dup_def
val def = fdM_eqs |> translate
val def = REWRITE_RULE[fdM_intro]add_constants_def |> m_translate
val def = add_def_def |> m_translate

val _ = ml_prog_update open_local_in_block;

val def = new_constant_def |> Q.SPEC ‘n’ |> check [‘n’,‘ty’] |> m_translate

val _ = ml_prog_update open_local_block;

val def = add_type_def |> m_translate

Definition call_new_type_def[simp]:
  call_new_type (n:mlstring, arity:int) =
    if 0 ≤ arity then new_type (n, Num (ABS arity))
    else raise_Fail (strlit "negative arity")
End

val _ = next_ml_names := ["new_type_num"];
val def = new_type_def |> m_translate

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["new_type"];
val def = call_new_type_def |> check [‘n’] |> m_translate

val _ = next_ml_names := ["EQ_MP", "ASSUME"];
val def = holKernelPmatchTheory.EQ_MP_def |> m_translate
val def = ASSUME_def |> check [‘tm’] |> m_translate

val def = new_axiom_def |> check [‘tm’] |> m_translate
val def = vsubst_def |> check [‘theta’,‘tm’] |> m_translate

val _ = ml_prog_update open_local_block;

val def = inst_aux_def (* rec *) |> m_translate

val _ = ml_prog_update open_local_in_block;

val def = inst_def |> check [‘tyin’,‘tm’] |> m_translate

val _ = ml_prog_update open_local_block;

val def = mk_eq_def |> check [‘l’,‘r’] |> m_translate

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names :=
  ["REFL", "TRANS", "MK_COMB", "ABS", "BETA"];
val def = REFL_def |> check [‘tm’] |> m_translate
val def = holKernelPmatchTheory.TRANS_def |> m_translate

val MK_COMB_lemma = prove(
  ``MK_COMB x = case x of (Sequent asl1 c1,Sequent asl2 c2) =>
                  MK_COMB (Sequent asl1 c1,Sequent asl2 c2)``,
  every_case_tac)
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [holKernelPmatchTheory.MK_COMB_def]));
val def = MK_COMB_lemma |> m_translate
val def = holKernelPmatchTheory.ABS_def |> check [‘v’] |> m_translate
val def = holKernelPmatchTheory.BETA_def |> check [‘tm’] |> m_translate

val _ = next_ml_names := ["DEDUCT_ANTISYM_RULE"];
val def = DEDUCT_ANTISYM_RULE_def |> m_translate
val def = new_specification_def |> m_translate
val def = new_basic_definition_def |> check [‘tm’] |> m_translate

val def = holSyntaxExtraTheory.instance_subst_def |> PURE_REWRITE_RULE [MEM_EXISTS] |> translate_no_ind

Triviality instance_subst_ind:
  instance_subst_ind
Proof
  rewrite_tac [fetch "-" "instance_subst_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ ho_match_mp_tac holSyntaxExtraTheory.instance_subst_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, GSYM MEM_EXISTS, EVERY_MEM]
QED

val _ = instance_subst_ind |> update_precondition;

val def = holSyntaxTheory.is_reserved_name_def |> translate
val def = check_overloads_def |> m_translate

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``
Overload failwith[local] = ``raise_Fail``

val def = holSyntaxTheory.wellformed_compute_def |> translate

Theorem wellformed_compute_side_thm[local]:
  wellformed_compute_side x
Proof
  qid_spec_tac ‘x’ >>
  ho_match_mp_tac holSyntaxTheory.wellformed_compute_ind >>
  rpt strip_tac >>
  rw[Once(fetch "-" "wellformed_compute_side_def")]
QED

val _ = update_precondition wellformed_compute_side_thm

Definition allTypes_ty_def:
  allTypes_ty = allTypes'
End

Triviality allTypes'_eqn:
  allTypes' ty =
    case ty of
      Tyapp s tys =>
        (^(holSyntaxTheory.allTypes'_defn |> cj 1 |> concl |> strip_forall |> snd |> rhs))
    | Tyvar n => (^(holSyntaxTheory.allTypes'_defn |> cj 2 |> concl |> strip_forall |> snd |> rhs))
Proof
  PURE_TOP_CASE_TAC >> rw[allTypes_ty_def,holSyntaxTheory.allTypes'_defn]
QED

Theorem allTypes_ty_eqn =
  allTypes_ty_def
  |> PURE_REWRITE_RULE [FUN_EQ_THM,Once allTypes'_eqn]
  |> PURE_REWRITE_RULE [GSYM allTypes_ty_def]

Theorem allTypes_ty_ind =
  holSyntaxTheory.allTypes'_defn_ind

val def = allTypes_ty_eqn |> translate
val def = holSyntaxTheory.allTypes_def
          |> REWRITE_RULE[GSYM allTypes_ty_def]
          |> translate

Triviality allCInsts_eqn =
  holSyntaxTheory.allCInsts_def
  |> SIMP_RULE std_ss [holSyntaxTheory.builtin_const_def,
                       holSyntaxTheory.init_ctxt_def,FILTER,
                       holSyntaxTheory.update_case_def,MEM,
                       holSyntaxTheory.update_11,holSyntaxTheory.type_11,
                       holSyntaxExtraTheory.instance_subst_completeness,
                       quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]

val def = allCInsts_eqn |> translate

(* MAP Tyvar (MAP implode (QSORT string_le (MAP explode (type_vars_in_term P)))) *)

val def = REPLICATE |> translate

val def = holSyntaxTheory.dependency_compute_def
          |> PURE_REWRITE_RULE[GSYM QSORT_type_vars_in_term,GSYM allTypes_ty_def]
          |> translate

val def = list_max_def |> translate

(*Theorem list_max_strlen_lemma:
  list_max (MAP strlen (tyvars ty)) = list_max (MAP strlen (type_vars_in_term ty))
Proof
QED*)

(*val def = FOLDL |> translate*)

Triviality lambda_lemma:
  (λx y. (λ(a,b) c. P a b c) y x) = λc (a,b). P a b c
Proof
  rw[ELIM_UNCURRY]
QED

Definition normalise_tyvars_subst_alt_def:
  (normalise_tyvars_subst_alt (Tyvar v) n n0 subst chr =
        (let
           varname n = Tyvar (implode (REPLICATE n chr))
         in
           if strlen v < n0 ∧ ¬EXISTS ($= (Tyvar v)) (MAP SND subst) then
             (SUC n,(varname n,Tyvar v)::subst)
           else (n,subst))) ∧
  (normalise_tyvars_subst_alt (Tyapp v tys) n n0 subst chr =
    normalise_tyvars_subst_alt_list tys n n0 subst chr) ∧
  (normalise_tyvars_subst_alt_list [] n n0 subst chr = (n,subst)) ∧
  (normalise_tyvars_subst_alt_list (ty::tys) n n0 subst chr =
    let (n,subst) = normalise_tyvars_subst_alt ty n n0 subst chr
    in
      normalise_tyvars_subst_alt_list tys n n0 subst chr)
End

Theorem normalise_tyvars_subst_alt_eqn:
  ∀ty n n0 subst chr.
  normalise_tyvars_subst_alt ty n n0 subst chr = normalise_tyvars_subst ty n n0 subst chr
Proof
  ho_match_mp_tac holSyntaxExtraTheory.normalise_tyvars_subst_ind >>
  rw[normalise_tyvars_subst_alt_def,holSyntaxExtraTheory.normalise_tyvars_subst_def] >>
  gvs[mlstringTheory.implode_def] >>
  gvs[EVERY_MEM,EXISTS_MEM] >>
  MAP_EVERY qid_spec_tac [‘n’,‘subst’] >>
  Induct_on ‘tys’ >>
  rw[normalise_tyvars_subst_alt_def] >>
  rw[ELIM_UNCURRY]
QED

val def = normalise_tyvars_subst_alt_def
          |> translate

val def = holSyntaxExtraTheory.normalise_tyvars_rec_def
          |> PURE_REWRITE_RULE [GSYM call_tyvars_def,GSYM tyvars_EQ_thm,
                                GSYM normalise_tyvars_subst_alt_eqn,
                                GSYM holKernelProofTheory.type_subst]
          |> translate

val def = holSyntaxExtraTheory.unify_types_def
          |> PURE_REWRITE_RULE [GSYM call_tyvars_def,GSYM tyvars_EQ_thm,
                                GSYM normalise_tyvars_subst_alt_eqn,
                                MEM_EXISTS,
                                PURE_REWRITE_RULE[GSYM FUN_EQ_THM] (GSYM (cj 1 holKernelProofTheory.type_subst))]
          |> translate_no_ind

Triviality unify_types_ind:
  unify_types_ind
Proof
  rewrite_tac [fetch "-" "unify_types_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (holSyntaxExtraTheory.unify_types_ind)
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [EVERY_MEM,holKernelProofTheory.tyvars_EQ_thm,
          PURE_REWRITE_RULE[GSYM FUN_EQ_THM] (GSYM (cj 1 holKernelProofTheory.type_subst))]
QED

val _ = unify_types_ind |> update_precondition;

val def = holSyntaxExtraTheory.unify_def
          |> PURE_REWRITE_RULE [
              PURE_REWRITE_RULE[GSYM FUN_EQ_THM] (GSYM (cj 1 holKernelProofTheory.type_subst))
            ]
          |> translate

val def = holSyntaxExtraTheory.orth_ctxt_compute_def
          |> PURE_REWRITE_RULE[holSyntaxLibTheory.mlstring_sort_def,
                               GSYM QSORT_type_vars_in_term]
          |> translate

val def = holSyntaxCyclicityTheory.unify_LR_def |> translate

Definition is_tyvar_def:
  (is_tyvar(Tyvar x) = T) ∧ (is_tyvar(Tyapp _ _) = F)
End

Theorem is_tyvar_intro:
  (∃x. ty = Tyvar x) ⇔ is_tyvar ty
Proof
  Cases_on ‘ty’ >> rw[is_tyvar_def]
QED

val def = is_tyvar_def |> translate

Theorem fv_alt =
  holSyntaxTheory.FV_def
  |> PURE_ONCE_REWRITE_RULE[Q.ISPEC ‘holSyntax$tyvars’ (GSYM ETA_THM)]
  |> PURE_ONCE_REWRITE_RULE[Q.ISPEC ‘holSyntax$tvars’ (GSYM ETA_THM)]
(*  |> PURE_REWRITE_RULE[GSYM holKernelProofTheory.tyvars_EQ_thm]*)

Definition fv_alt_def:
  fv_alt p = case p of INL x => holKernel$tyvars x | INR x => type_vars_in_term x
End

val def = fv_alt_def |> translate

Theorem invertible_on_alt =
  holSyntaxCyclicityTheory.invertible_on_eq'
  |> SIMP_RULE std_ss [GSYM EVERY_MEM,is_tyvar_intro,
                       GSYM AND_IMP_INTRO, GSYM PULL_FORALL,
                       GSYM (cj 1 holKernelProofTheory.type_subst)
                      ]

val def = invertible_on_alt |> translate

Theorem invertible_on_FV_eq:
  invertible_on x (FV p) = invertible_on x (fv_alt p)
Proof
  rw[holSyntaxCyclicityTheory.invertible_on_eq',EQ_IMP_THM,holSyntaxTheory.FV_def,fv_alt_def] >>
  PURE_FULL_CASE_TAC >> gvs[MEM_type_vars_in_term,tyvars_EQ_thm]
QED

val def = holSyntaxCyclicityTheory.composable_one_def
          |> PURE_REWRITE_RULE[invertible_on_FV_eq]
          |> translate

val def = lr_type_subst_def |> m_translate

val def = composable_step_compute_def |> m_translate

val def = holSyntaxCyclicityTheory.instance_LR_compute_def |> translate

val def = holSyntaxCyclicityTheory.is_instance_LR_compute_def |> translate

val def = dep_step_compute_def |> m_translate

val _ = Q.prove(
  ‘∀dep l res s. dep_step_compute_side s dep l res’,
  Induct_on ‘l’ >> rw[Once $ fetch "-" "dep_step_compute_side_def"] >>
  gvs[GSYM LENGTH_NOT_NULL,quantHeuristicsTheory.LIST_LENGTH_1]) |> update_precondition

val def = dep_steps_compute_def |> m_translate

val def = new_overloading_specification_def |> m_translate

val _ = next_ml_names := ["INST_TYPE", "INST"];
val def = (INST_TYPE_def |> SIMP_RULE std_ss [LET_DEF]) |> check [‘theta’] |> m_translate
val def = (INST_def |> SIMP_RULE std_ss [LET_DEF]) |> check [‘theta’] |> m_translate
val def = new_basic_type_definition_def |> check [‘tyname’,‘absname’,‘repname’]  |> m_translate

val _ = ml_prog_update open_local_block;

val def = list_to_hypset_def |> translate

val _ = ml_prog_update open_local_in_block;

val def = m_translate axioms_def;
val def = m_translate types_def;
val def = m_translate constants_def;

(* The kernel module is closed in subsequent script files:
   ml_hol_kernelProgScript.sml and candle_kernelProgScript.sml *)

val _ = Globals.max_print_depth := 10;
val _ = print_asts := false;

val _ = export_theory();
