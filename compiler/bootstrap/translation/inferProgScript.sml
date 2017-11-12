open preamble
     parserProgTheory inferTheory
     semanticPrimitivesTheory inferPropsTheory
     ml_translatorTheory
open ml_monadBaseTheory ml_monad_translatorLib

val _ = new_theory "inferProg"

val _ = translation_extends "parserProg";

val _ = hide "state";

(* translator setup *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = register_type ``:lexer_fun$symbol``;

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.store_thm("NOT_NIL_AND_LEMMA",
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy "infer" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* monadic translator setup *)
val _ = register_type ``:locs``;
val _ = register_exn_type ``:infer_exn``;
val _ = register_type ``:infer_t``;
val INFER_EXN_TYPE_def = theorem"INFER_EXN_TYPE_def";

val exn_functions = [(raise_Exc_def, handle_Exc_def)];
val _ = temp_overload_on ("failwith", ``raise_Exc``);

val refs_manip_list = [("next_uvar", get_next_uvar_def, set_next_uvar_def),
		      ("subst", get_subst_def, set_subst_def)];

val store_hprop_name = "INFER_STATE_STORE";
val state_type = ``:infer_st``;

val arrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val add_type_theories = ["to_dataProg","lexerProg","parserProg"] : string list;
val exn_ri_def = INFER_EXN_TYPE_def;

val store_pinv_def_opt = NONE : thm option;

val (monad_parameters, exn_specs) =
    start_dynamic_init_fixed_store_translation refs_manip_list
					       arrays_manip_list
					       store_hprop_name
					       state_type
					       exn_ri_def
					       exn_functions
					       add_type_theories
                                               store_pinv_def_opt;



(* type inference: t_walkstar and t_unify *)

val PRECONDITION_INTRO = Q.prove(
  `(b ==> (x = y)) ==> (x = if PRECONDITION b then y else x)`,
  Cases_on `b` THEN SIMP_TAC std_ss [PRECONDITION_def]);

val t_vwalk_ind = Q.store_thm("t_vwalk_ind",
  `!P.
      (!s v.
        (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = Infer_Tuvar u ==> P s u) ==>
        P s v) ==>
      (!s v. t_wfs s ==> P s v)`,
  NTAC 3 STRIP_TAC
  THEN Cases_on `t_wfs s` THEN FULL_SIMP_TAC std_ss []
  THEN HO_MATCH_MP_TAC (unifyTheory.t_vwalk_ind |> Q.SPEC `P (s:num |-> infer_t)`
       |> DISCH_ALL |> RW [AND_IMP_INTRO])
  THEN FULL_SIMP_TAC std_ss []);

val _ = translate
  (unifyTheory.t_vwalk_eqn
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
    |> MATCH_MP PRECONDITION_INTRO);

val t_vwalk_side_def = Q.store_thm("t_vwalk_side_def",
  `!s v. t_vwalk_side s v <=> t_wfs s`,
  STRIP_TAC THEN reverse (Cases_on `t_wfs s`) THEN FULL_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [fetch "-" "t_vwalk_side_def"]
         THEN FULL_SIMP_TAC std_ss [])
  THEN STRIP_TAC THEN POP_ASSUM (fn th => MP_TAC th THEN MP_TAC th)
  THEN Q.SPEC_TAC (`v`,`v`) THEN Q.SPEC_TAC (`s`,`s`)
  THEN HO_MATCH_MP_TAC t_vwalk_ind
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [fetch "-" "t_vwalk_side_def"]
  THEN FULL_SIMP_TAC std_ss [PULL_FORALL])
  |> update_precondition;

val _ = translate unifyTheory.t_walk_eqn;

val t_walkstar_ind = Q.store_thm("t_walkstar_ind",
  `!P.
      (!s t.
         (!ts tc0 a. t_walk s t = Infer_Tapp ts tc0 /\ MEM a ts ==> P s a) ==>
         P s t) ==>
      !s t. t_wfs s ==> P s t`,
  METIS_TAC [unifyTheory.t_walkstar_ind]);

val expand_lemma = Q.prove(
  `t_walkstar s = \x. t_walkstar s x`,
  SIMP_TAC std_ss [FUN_EQ_THM]);

val _ = translate
  (unifyTheory.t_walkstar_eqn
    |> RW1 [expand_lemma] |> SIMP_RULE std_ss [PULL_FORALL]
    |> SPEC_ALL |> MATCH_MP PRECONDITION_INTRO)

val t_walkstar_side_def = Q.store_thm("t_walkstar_side_def",
  `!s v. t_walkstar_side s v <=> t_wfs s`,
  STRIP_TAC THEN reverse (Cases_on `t_wfs s`) THEN FULL_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [fetch "-" "t_walkstar_side_def"]
         THEN FULL_SIMP_TAC std_ss [])
  THEN STRIP_TAC THEN POP_ASSUM (fn th => MP_TAC th THEN MP_TAC th)
  THEN Q.SPEC_TAC (`v`,`v`) THEN Q.SPEC_TAC (`s`,`s`)
  THEN HO_MATCH_MP_TAC t_walkstar_ind THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [fetch "-" "t_walkstar_side_def"]
  THEN FULL_SIMP_TAC std_ss [fetch "-" "t_walk_side_def"]
  THEN METIS_TAC [])
  |> update_precondition;

val t_oc_ind = Q.store_thm("t_oc_ind",
  `!P.
      (!s t v.
        (!ts tt a. t_walk s t = Infer_Tapp ts tt /\ MEM a ts ==> P s a v) ==>
        P s t v) ==>
      (!s t v. t_wfs s ==> P (s:num |-> infer_t) (t:infer_t) (v:num))`,
  REPEAT STRIP_TAC THEN Q.SPEC_TAC (`t`,`t`)
  THEN IMP_RES_TAC unifyTheory.t_walkstar_ind
  THEN POP_ASSUM HO_MATCH_MP_TAC THEN METIS_TAC []);

val EXISTS_LEMMA = Q.prove(
  `!xs P. EXISTS P xs = EXISTS I (MAP P xs)`,
  Induct THEN SRW_TAC [] []);

val _ = translate
  (unifyTheory.t_oc_eqn
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
    |> RW1 [EXISTS_LEMMA] |> MATCH_MP PRECONDITION_INTRO)

val t_oc_side_lemma = Q.prove(
  `!s t v. t_wfs s ==> t_wfs s ==> t_oc_side s t v`,
  HO_MATCH_MP_TAC t_oc_ind THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN ONCE_REWRITE_TAC [fetch "-" "t_oc_side_def"]
  THEN ASM_SIMP_TAC std_ss [fetch "-" "t_walk_side_def",PULL_FORALL]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val t_oc_side_def = Q.store_thm("t_oc_side_def",
  `!s t v. t_oc_side s t v <=> t_wfs s`,
  STRIP_TAC THEN Cases_on `t_wfs s`
  THEN FULL_SIMP_TAC std_ss [t_oc_side_lemma]
  THEN ONCE_REWRITE_TAC [fetch "-" "t_oc_side_def"]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val _ = translate unifyTheory.t_ext_s_check_eqn;

val t_unify_lemma = Q.prove(
  `t_wfs s ==>
    (t_unify s t1 t2 =
       case (t_walk s t1,t_walk s t2) of
       | (Infer_Tvar_db n1,Infer_Tvar_db n2) =>
           if n1 = n2 then SOME s else NONE
       | (Infer_Tvar_db n1,Infer_Tapp v23 v24) => NONE
       | (Infer_Tvar_db n1,Infer_Tuvar v25) =>
           t_ext_s_check s v25 (Infer_Tvar_db n1)
       | (Infer_Tapp ts1 tc1,Infer_Tvar_db v30) => NONE
       | (Infer_Tapp ts1 tc1,Infer_Tapp ts2 tc2) =>
           if tc1 = tc2 then ts_unify s ts1 ts2 else NONE
       | (Infer_Tapp ts1 tc1,Infer_Tuvar v33) =>
           t_ext_s_check s v33 (Infer_Tapp ts1 tc1)
       | (Infer_Tuvar v1,Infer_Tvar_db v42) =>
           t_ext_s_check s v1 (Infer_Tvar_db v42)
       | (Infer_Tuvar v1,Infer_Tapp v43 v44) =>
           t_ext_s_check s v1 (Infer_Tapp v43 v44)
       | (Infer_Tuvar v1,Infer_Tuvar v2) =>
           SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2))) /\
    (ts_unify s ts1 ts2 =
       case (ts1,ts2) of
       | ([],[]) => SOME s
       | (t1::ts1,t2::ts2) => (case t_unify s t1 t2 of
                               | NONE => NONE
                               | SOME s' => ts_unify s' ts1 ts2)
       | _ => NONE)`,
  REPEAT STRIP_TAC
  THEN1 ASM_SIMP_TAC std_ss [unifyTheory.t_unify_eqn]
  THEN Cases_on `ts1` THEN Cases_on `ts2`
  THEN ASM_SIMP_TAC (srw_ss()) [unifyTheory.ts_unify_def])
  |> UNDISCH |> CONJUNCTS
  |> map (MATCH_MP PRECONDITION_INTRO o DISCH_ALL) |> LIST_CONJ

val _ = translate t_unify_lemma

val t_unify_side_rw = fetch "-" "t_unify_side_def"

val t_unify_side_lemma = Q.prove(
  `(!s t v. t_wfs s ==> t_wfs s ==> t_unify_side s t v) /\
    (!s ts v. t_wfs s ==> t_wfs s ==> ts_unify_side s ts v)`,
  HO_MATCH_MP_TAC unifyTheory.t_unify_ind THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN ONCE_REWRITE_TAC [fetch "-" "t_unify_side_def"]
  THEN ASM_SIMP_TAC std_ss [fetch "-" "t_walk_side_def",
         fetch "-" "t_ext_s_check_side_def", PULL_FORALL]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []
  THEN METIS_TAC [unifyTheory.t_unify_unifier]) |> SIMP_RULE std_ss [];

val t_unify_side_def = Q.store_thm("t_unify_side_def",
  `!s t v. t_unify_side s t v <=> t_wfs s`,
  STRIP_TAC THEN Cases_on `t_wfs s`
  THEN FULL_SIMP_TAC std_ss [t_unify_side_lemma]
  THEN ONCE_REWRITE_TAC [t_unify_side_rw]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val ts_unify_side_def = Q.store_thm("ts_unify_side_def",
  `!s t v. ts_unify_side s t v <=> t_wfs s`,
  STRIP_TAC THEN Cases_on `t_wfs s`
  THEN FULL_SIMP_TAC std_ss [t_unify_side_lemma]
  THEN ONCE_REWRITE_TAC [t_unify_side_rw]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val _ = save_thm("anub_ind",REWRITE_RULE[MEMBER_INTRO]miscTheory.anub_ind)
val _ = translate (REWRITE_RULE[MEMBER_INTRO] miscTheory.anub_def)

val _ = (extra_preprocessing :=
  [MEMBER_INTRO, MAP, OPTION_BIND_THM, guard_def]);

val _ = translate (def_of_const ``id_to_string``)
val _ = m_translate (def_of_const ``lookup_st_ex``)
val _ = m_translate (def_of_const ``fresh_uvar``)
val _ = m_translate (def_of_const ``n_fresh_uvar``)
val _ = translate (def_of_const ``init_infer_state``)
val _ = m_translate (def_of_const ``infer$init_state``)
val _ = translate (def_of_const ``infer_deBruijn_subst``)
val _ = translate (def_of_const ``generalise``)
val _ = translate (def_of_const ``infer_type_subst``)

val _ = translate rich_listTheory.COUNT_LIST_AUX_def
val _ = translate rich_listTheory.COUNT_LIST_compute

val pair_abs_hack = Q.prove(
  `(\(v2:string,v1:infer_t). (v2,0,v1)) =
    (\v3. case v3 of (v2,v1) => (v2,0:num,v1))`,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM,FORALL_PROD]);

fun fix_infer_induction_thm def = let
  val const = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator
  val cname = const |> dest_const |> fst
  val ind_name = cname ^ "_ind"
  val ind = fetch "infer" ind_name
  val s_var = mk_var("state", ``: (num |-> infer_t) infer_st``)
  val cs = ind |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> map concl
               |> map (fn tm => let val xs = list_dest dest_forall tm
                                    val vs = butlast xs
                                    val body = repeat rator (last xs)
                                    in (vs,body) end)
  fun list_dest_fun_type ty = let
    val (ty1,ty2) = dest_fun_type ty
    in ty1 :: list_dest_fun_type ty2 end handle HOL_ERR _ => [ty]
  fun new_P_inst (vs,P) = let
    val (Pname,ty) = dest_var P
    val tys = list_dest_fun_type ty
    val tys1 = butlast tys @ [type_of s_var, last tys]
    val Pnew = mk_var(Pname,list_mk_fun_type tys1)
    val tm = mk_forall(s_var,list_mk_comb(Pnew,vs @ [s_var]))
    in (Pnew,list_mk_abs(vs,tm)) end
  val ps = map new_P_inst cs
  val ind = ind |> SPECL (map snd ps) |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> GENL (map fst ps) |> PURE_REWRITE_RULE [pair_abs_hack]
  val _ = print ("Improved induction theorem: " ^ ind_name ^ "\n")
  val _ = save_thm(ind_name,ind)
  in () end handle HOL_ERR _ => ();

val if_apply = Q.prove(
  `!b. (if b then x1 else x2) x = if b then x1 x else x2 x`,
  Cases THEN SRW_TAC [] []);

val option_case_apply = Q.prove(
  `!oo. option_CASE oo x1 x2 x = option_CASE oo (x1 x) (\y. x2 y x)`,
  Cases THEN SRW_TAC [] []);

val pr_CASE = Q.prove(
  `pair_CASE (x,y) f = f x y`,
  SRW_TAC [] []);

val op_apply = Q.prove(
  `!op. (ast$op_CASE op x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38) y =
         (ast$op_CASE op
            (* Opn 1 *)
            (\z. x1 z y)
            (* Opb 1 *)
            (\z. x2 z y)
            (* Opw 2 *)
            (\z1 z2. x3 z1 z2 y)
            (* Shift 3 *)
            (\z1 z2 z3. x4 z1 z2 z3 y)
            (* Equality 0 *)
            (x5 y)
            (* FP_cmp 1 *)
            (\z. x6 z y)
            (* FP_uop 1 *)
            (\z. x7 z y)
            (* FP_bop 1 *)
            (\z. x8 z y)
            (* Opapp 0 *)
            (x9 y)
            (* Opassign 0 *)
            (x10 y)
            (* Opref 0 *)
            (x11 y)
            (* Opderef 0 *)
            (x12 y)
            (* Aw8alloc *)
            (x13 y)
            (* Aw8sub *)
            (x14 y)
            (* Aw8length*)
            (x15 y)
            (* Aw8update *)
            (x16 y)
            (* WfI 1 *)
            (\z. x17 z y)
            (* WtI 1 *)
            (\z. x18 z y)
            (* CopyStrStr *)
            (x19 y)
            (* CopyStrAw8 *)
            (x20 y)
            (* CopyAw8Str *)
            (x21 y)
            (* CopyAw8Aw8 *)
            (x22 y)
            (* Ord *)
            (x23 y)
            (* Chr *)
            (x24 y)
            (* Chopb 1 *)
            (\z. x25 z y)
            (* Implode *)
            (x26 y)
            (* Strsub*)
            (x27 y)
            (* Strlen *)
            (x28 y)
            (* Strcat *)
            (x29 y)
            (* Vfromlist *)
            (x30 y)
            (* Vsub *)
            (x31 y)
            (* Vlength *)
            (x32 y)
            (* Aalloc *)
            (x33 y)
            (* AallocEmpty *)
            (x34 y)
            (* Asub *)
            (x35 y)
            (* Alength*)
            (x36 y)
            (* Aupdate *)
            (x37 y)
            (* FFI *)
            (\z. x38 z y))`,
  Cases THEN SRW_TAC [] []);

val list_apply = Q.prove(
  `!op. (list_CASE op x1 x2) y =
         (list_CASE op (x1 y) (\z1 z2. x2 z1 z2 y))`,
  Cases THEN SRW_TAC [] []);

(* TODO: duplicated from ml_translatorLib, should go elsewhere*)
fun list_conv c tm =
  if listSyntax.is_cons tm then
    ((RATOR_CONV o RAND_CONV) c THENC
     RAND_CONV (list_conv c)) tm
  else if listSyntax.is_nil tm then ALL_CONV tm
  else NO_CONV tm

val monad_rewrites = [st_ex_bind_def, st_ex_return_def, get_subst_def, set_subst_def, get_next_uvar_def, set_next_uvar_def, raise_Exc_def];
val simp_monad = fs monad_rewrites;

val _ = m_translate (def_of_const ``apply_subst``);
val _ = m_translate (def_of_const ``apply_subst_list``);
val _ = translate (def_of_const ``tc_to_string``);

val tc_to_string_side_thm = Q.store_thm ("tc_to_string_side_thm",
  `!x. tc_to_string_side x`,
  rw [definition"tc_to_string_side_def"] >>
  Cases_on `x` >>
  rw []) |> update_precondition;

val _ = translate infer_tTheory.inf_type_to_string_pmatch;

val inf_type_to_string_side_thm  = Q.store_thm ("inf_type_to_string_side_thm",
  `(!x. inf_type_to_string_side x) ∧
   (!xs. inf_types_to_string_side xs)`,
  ho_match_mp_tac infer_tTheory.inf_type_to_string_ind >>
  rw [] >>
  rw [Once (theorem "inf_type_to_string_side_def")]) |> update_precondition;

val _ = m_translate (def_of_const ``add_constraint``);

val add_constraint_side_def = definition"add_constraint_side_def"

val _ = m_translate (def_of_const ``add_constraints``);

val add_constraint_side_thm = Q.store_thm("add_constraint_side_thm",
  `∀l x y z. t_wfs z.subst ⇒ add_constraint_side z l x y`,
  rw[add_constraint_side_def]);

val add_constraints_side_thm = Q.store_thm("add_constraints_side_thm",
  `∀l x y z. t_wfs z.subst ⇒ add_constraints_side z l x y`,
  recInduct add_constraints_ind
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[PRECONDITION_def,add_constraint_side_def]
  \\ first_x_assum match_mp_tac
  \\ fs[add_constraint_def]
  \\ simp_monad
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[unifyTheory.t_unify_wfs]);

val def = def_of_const ``constrain_op``
val _ = translate (def_of_const ``TC_word``)
val _ = m_translate (def_of_const ``constrain_op``);
val _ = m_translate (def_of_const ``t_to_freevars``);

val MAP_type_name_subst = prove(
  ``MAP (type_name_subst tenvT) ts =
    MAP (\x. type_name_subst tenvT x) ts``,
  CONV_TAC (DEPTH_CONV ETA_CONV) \\ simp []);

val lemma = prove(
  ``MAP (\(x,y). foo x y) = MAP (\z. foo (FST z) (SND z))``,
  AP_TERM_TAC \\ fs [FUN_EQ_THM,FORALL_PROD]);

val _ = translate (typeSystemTheory.build_ctor_tenv_def
		   |> REWRITE_RULE [MAP_type_name_subst]
  	           |> SIMP_RULE std_ss [lemma]);

val EVERY_INTRO = Q.prove(
  `(!x::set s. P x) = EVERY P s`,
  SIMP_TAC std_ss [res_quanTheory.RES_FORALL,EVERY_MEM]);

val EVERY_EQ_EVERY = Q.prove(
  `!xs. EVERY P xs = EVERY I (MAP P xs)`,
  Induct THEN SRW_TAC [] []);

val _ = translate (def_of_const ``check_freevars``
                   |> RW1 [EVERY_EQ_EVERY])

val _ = translate (def_of_const ``check_dup_ctors``
                   |> SIMP_RULE std_ss [EVERY_INTRO,LET_DEF])

val _ = translate (def_of_const ``check_ctor_tenv``)

val _ = translate (def_of_const ``is_value``
            |> RW1 [prove(``~b <=> (b = F)``,SIMP_TAC std_ss [])]
            |> RW1 [EVERY_EQ_EVERY])

val _ = translate (def_of_const ``tid_exn_to_tc``) (* added *)

val _ = m_translate (def_of_const ``infer_p``)

val infer_p_side_def = theorem"infer_p_side_def";

val n_fresh_uvar_success = Q.prove(
  `!n st vs st'. ~(n_fresh_uvar n st = (Failure vs,st'))`,
  Induct >>
  rw[Once n_fresh_uvar_def] >>
  fs[fresh_uvar_def] >>
  simp_monad >>
  every_case_tac >>
  metis_tac[]);

val n_fresh_uvar_subst = Q.prove(
  `!n st. (SND (n_fresh_uvar n st)).subst = st.subst`,
  Induct >>
  rw[Once n_fresh_uvar_def] >>
  simp_monad >>
  fs[fresh_uvar_def] >>
  simp_monad >>
  Cases_on `n` >>
  fs[Once n_fresh_uvar_def, fresh_uvar_def] >>
  simp_monad >>
  every_case_tac >>
  fs[success_eqns,n_fresh_uvar_success]);

val infer_p_side_thm = Q.store_thm ("infer_p_side_thm",
  `(!l cenv p st. t_wfs st.subst ⇒ infer_p_side st l cenv p) ∧
   (!l cenv ps st. t_wfs st.subst ⇒ infer_ps_side st l cenv ps)`,
  ho_match_mp_tac infer_p_ind >>
  rw [] >>
  rw [Once infer_p_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [add_constraint_side_def] >>
  fs [lookup_st_ex_def,PRECONDITION_def] >> simp_monad >>
  TRY(qmatch_goalsub_rename_tac`FST pp` >> PairCases_on`pp`) >> fs[] >>
  TRY(match_mp_tac add_constraints_side_thm >> fs[]) >>
  every_case_tac >> fs[] >> rw[] >>
  fs[n_fresh_uvar_subst] >>
  metis_tac[infer_p_wfs,PAIR]);

val _ = translate namespaceTheory.nsOptBind_def

val _ = m_translate (def_of_const ``infer_e``)

(* open to_dataProg for the AST_* definitions *)
open to_dataProgTheory

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_BOOL = find_equality_type_thm``BOOL``
val EqualityType_WORD = find_equality_type_thm``WORD``

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val EqualityType_AST_LIT_TYPE = find_equality_type_thm``AST_LIT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,
                       EqualityType_INT,EqualityType_BOOL,EqualityType_WORD]

(* (string,string) id*)
val EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR = find_equality_type_thm``NAMESPACE_ID_TYPE m n`` |> Q.GEN`m` |> Q.ISPEC`LIST_TYPE CHAR` |> Q.GEN`n` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]

val EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`NAMESPACE_ID_TYPE (LIST_TYPE CHAR) (LIST_TYPE CHAR)`
  |> SIMP_RULE std_ss [EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR]

val EqualityType_AST_TCTOR_TYPE = find_equality_type_thm``AST_TCTOR_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR]

val AST_T_TYPE_no_closures = Q.prove(
  `∀a b. AST_T_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >- (
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_1`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR]);
val _ = print "Proved AST_T_TYPE_no_closures\n";

val AST_T_TYPE_types_match = Q.prove(
  `∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >> rw[] >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    reverse conj_tac >- METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def] >> rw[] >>
    pop_assum kall_tac >>
    qhdtm_x_assum`AST_TCTOR_TYPE`kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,ctor_same_type_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[LIST_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_def] ))
val _ = print "Proved AST_T_TYPE_types_match\n";

val AST_T_TYPE_11 = Q.prove(
  `∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS] >> rw[] >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    `x_3 = t ⇔ v3_2 = v3_2'` by METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def] >> rw[] >>
    rpt(qhdtm_x_assum`AST_TCTOR_TYPE`kall_tac) >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[LIST_TYPE_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_def] ))
val _ = print "Proved AST_T_TYPE_11\n";

val EqualityType_AST_T_TYPE = Q.prove(
  `EqualityType AST_T_TYPE`,
  simp[EqualityType_def] >>
  METIS_TAC[AST_T_TYPE_no_closures,AST_T_TYPE_types_match,AST_T_TYPE_11])
  |> store_eq_thm
val _ = print "Proved EqualityType_AST_T_TYPE\n";

val AST_PAT_TYPE_no_closures = Q.prove(
  `∀a b. AST_PAT_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  TRY (
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v4_2`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,
            EqualityType_AST_T_TYPE,
            EqualityType_LIST_TYPE_CHAR])
val _ = print "Proved AST_PAT_TYPE_no_closures\n";

val AST_PAT_TYPE_types_match = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def,types_match_def,ctor_same_type_def] >> rw[] >>
  TRY (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v4_2`,`v4_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,ctor_same_type_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[types_match_def,ctor_same_type_def] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_T_TYPE])
val _ = print "Proved AST_PAT_TYPE_types_match\n";

val AST_PAT_TYPE_11 = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def] >> rw[] >-
  ( METIS_TAC[EqualityType_def,EqualityType_AST_T_TYPE] )
  >- (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    `x_4 = o' ⇔ v4_1 = v4_1'` by METIS_TAC[EqualityType_def, EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR] >>
    simp[] >>
    ntac 3 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v4_2`,`v4_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR])
val _ = print "Proved AST_PAT_TYPE_11\n";

val EqualityType_AST_PAT_TYPE = Q.prove(
  `EqualityType AST_PAT_TYPE`,
  METIS_TAC[EqualityType_def,AST_PAT_TYPE_no_closures,AST_PAT_TYPE_types_match,AST_PAT_TYPE_11])
  |> store_eq_thm
val _ = print "Proved EqualityType_AST_PAT_TYPE\n";

val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPW_TYPE = find_equality_type_thm``AST_OPW_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_WORD_SIZE_TYPE = find_equality_type_thm``AST_WORD_SIZE_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_SHIFT_TYPE = find_equality_type_thm``AST_SHIFT_TYPE`` |> SIMP_RULE std_ss []

val EqualityType_FPSEM_FP_BOP_TYPE = find_equality_type_thm ``FPSEM_FP_BOP_TYPE``
val EqualityType_FPSEM_FP_UOP_TYPE = find_equality_type_thm ``FPSEM_FP_UOP_TYPE``
val EqualityType_FPSEM_FP_CMP_TYPE = find_equality_type_thm ``FPSEM_FP_CMP_TYPE``

val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,
                       EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE,
                       EqualityType_AST_OPW_TYPE,
                       EqualityType_AST_WORD_SIZE_TYPE,EqualityType_AST_SHIFT_TYPE,
                       EqualityType_LIST_TYPE_CHAR,
                       EqualityType_FPSEM_FP_BOP_TYPE,
                       EqualityType_FPSEM_FP_UOP_TYPE,
                       EqualityType_FPSEM_FP_CMP_TYPE
                       ]

val EqualityType_AST_LOP_TYPE = find_equality_type_thm``AST_LOP_TYPE``
  |> SIMP_RULE std_ss []

val EqualityType_OPTION_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]

val EqualityType_LOCATION_LOCN_TYPE = find_equality_type_thm ``LOCATION_LOCN_TYPE`` |> SIMP_RULE std_ss [EqualityType_NUM]

val EqualityType_LOCATION_LOCS_TYPE = find_equality_type_thm ``LOCATION_LOCS_TYPE`` |> SIMP_RULE std_ss [EqualityType_LOCATION_LOCN_TYPE]

val EqualityType_PAIR_TYPE = find_equality_type_thm ``PAIR_TYPE a b``

val AST_EXP_TYPE_no_closures = Q.prove(
  `∀a b. AST_EXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    TRY(SIMP_RULE std_ss [EqualityType_def] EqualityType_LIST_TYPE_CHAR |> CONJUNCT1 |> MATCH_ACCEPT_TAC)>>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LOCATION_LOCS_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE,
            EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE])
val _ = print "AST_EXP_TYPE_no_closures\n";

val AST_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_EXP_TYPE_def,types_match_def,ctor_same_type_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[PAIR_TYPE_def,PULL_EXISTS] >>
    rw[types_match_def,ctor_same_type_def] >>
    fs[FORALL_PROD] >>
    PROVE_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE,
            EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE,
            EqualityType_LOCATION_LOCS_TYPE])
val _ = print "Proved AST_EXP_TYPE_types_match\n";

val AST_EXP_TYPE_11 = with_flag (metisTools.limit,{infs=SOME 1,time=NONE}) Q.prove(
  `∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_EXP_TYPE_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    REWRITE_TAC[AND_IMP_INTRO] >>
    last_x_assum mp_tac >>
    MATCH_MP_TAC SWAP_IMP >>
    REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    TRY(
      qmatch_assum_rename_tac`_ a1 b1` >>
      qpat_x_assum`R a1 b1`mp_tac >>
      qmatch_assum_rename_tac`_ a2 b2` >>
      strip_tac >>
      `a2 = a1 ⇔ b2 = b1` by
        METIS_TAC[EqualityType_def,EqualityType_AST_OP_TYPE,
                  EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR] >>
      simp[] ) >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[PAIR_TYPE_def,PULL_EXISTS] >>
    rw[] >> fs[FORALL_PROD] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    TRY(impl_tac >- metis_tac[]) >>
    metis_tac[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE,
            EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE,
            EqualityType_LOCATION_LOCS_TYPE])
val _ = print "Proved AST_EXP_TYPE_11\n";

val EqualityType_AST_EXP_TYPE = Q.prove(
  `EqualityType AST_EXP_TYPE`,
  METIS_TAC[EqualityType_def,AST_EXP_TYPE_no_closures,AST_EXP_TYPE_types_match,AST_EXP_TYPE_11])
  |> store_eq_thm
val _ = print "Proved EqualityType_AST_EXP_TYPE\n";

val apply_subst_list_side_def = definition"apply_subst_list_side_def";
val apply_subst_side_def = definition"apply_subst_side_def";
val constrain_op_side_def = definition"constrain_op_side_def";
val infer_e_side_def = theorem"infer_e_side_def";

val FST_TO_PAIR = Q.prove(
 `FST x = Success y ==> ?st2. x = (Success y, st2)`,
 rw[] >> Cases_on `x` >> fs[])

val FST_TO_PAIR_TAC =
    first_x_assum (fn x => MATCH_MP FST_TO_PAIR x |> ASSUME_TAC)

val n_fresh_uvar_subst_imp = Q.prove(
  `!n st. n_fresh_uvar n st = (x, st2) ==> st2.subst = st.subst`,
  Induct >>
  rw[Once n_fresh_uvar_def] >>
  simp_monad >>
  fs[fresh_uvar_def] >>
  simp_monad >>
  Cases_on `n` >>
  fs[Once n_fresh_uvar_def, fresh_uvar_def] >>
  simp_monad >>
  every_case_tac >>
  fs[success_eqns,n_fresh_uvar_success,infer_st_component_equality]);

val apply_infer_e_wfs = FIRST (List.map (fn x => drule x >> rw[]) (CONJUNCTS infer_e_wfs))

val add_constraints_t_wfs = Q.prove(
 `!x1 x2 l st1 st2. t_wfs st1.subst ==>
  add_constraints l x1 x2 st1 = (Success (), st2) ==>
  t_wfs st2.subst`,
  Induct
  >-(Cases >> rw[Once add_constraints_def] >> simp_monad) >>
  strip_tac >>
  Cases >-(rw[Once add_constraints_def] >> simp_monad) >>
  rw[Once add_constraints_def,add_constraint_def] >> simp_monad >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
  imp_res_tac unifyTheory.t_unify_wfs >>
  `t_wfs (st1 with subst := x).subst` by fs[] >>
  last_x_assum imp_res_tac)  

val infer_e_side_thm = Q.store_thm ("infer_e_side_thm",
  `(!l menv e st. t_wfs st.subst ⇒ infer_e_side st l menv e) /\
   (!l menv es st. t_wfs st.subst ⇒ infer_es_side st l menv es) /\
   (!l menv pes t1 t2 st. t_wfs st.subst ⇒ infer_pes_side st l menv pes t1 t2) /\
   (!l menv funs st. t_wfs st.subst ⇒ infer_funs_side st l menv funs)`,
  ho_match_mp_tac infer_e_ind >>
  rw [] >>
  rw [Once infer_e_side_def] >>
  TRY (irule add_constraint_side_thm) >>
  TRY (irule add_constraints_side_thm) >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [constrain_op_side_def, apply_subst_side_def, apply_subst_list_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rpt (FST_TO_PAIR_TAC >> simp_monad >> rw[]) >>
  fs[lookup_st_ex_def,fresh_uvar_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp_monad >> rw[] >>
  TRY(apply_infer_e_wfs) >> fs[add_constraint_def] >>
  imp_res_tac n_fresh_uvar_subst_imp >> rw[] >> simp_monad >>
  BasicProvers.EVERY_CASE_TAC >> simp_monad >> rw[] >>
  TRY (irule add_constraint_side_thm) >>
  TRY (irule add_constraints_side_thm) >>
  fs[] >>
  imp_res_tac unifyTheory.t_unify_wfs >>
  rw [] >> fs[] >>
  imp_res_tac infer_e_wfs >>
  imp_res_tac unifyTheory.t_unify_wfs >>
  imp_res_tac infer_p_side_thm >>
  imp_res_tac infer_p_wfs >>
  fs[] >|
  [`t_wfs st2''.subst` by fs[] \\ fs[]
   \\ imp_res_tac add_constraints_t_wfs \\ fs[],
   `t_wfs (st2' with subst := x).subst` by fs[]
   \\ fs[LAMBDA_PROD]])

val _ = translate (def_of_const ``empty_inf_decls``)
val _ = translate (def_of_const ``nsSing``)
val _ = translate (def_of_const ``check_exn_tenv``)

val _ = m_translate (def_of_const ``infer_d``)
val _ = print "Translated infer_d\n";

val infer_d_side_def = definition"infer_d_side_def";

val generalise_list_length = Q.prove (
  `!min start s x.
    LENGTH x = LENGTH (SND (SND (generalise_list min start s (MAP f (MAP SND x)))))`,
  induct_on `x` >>
  srw_tac[] [generalise_def] >>
  srw_tac[] [] >>
  metis_tac [SND]);

val irule_infer_e_side_thm = FIRST (List.map irule (CONJUNCTS infer_e_side_thm))
val irule_infer_p_side_thm = FIRST (List.map irule (CONJUNCTS infer_p_side_thm))
val irule_infer_e_wfs = FIRST (List.map irule (CONJUNCTS infer_e_wfs))

val t_wfs_FEMPTY = Q.prove(
  `t_wfs FEMPTY`,
  rw[unifyTheory.t_wfs_def, substTheory.wfs_def, relationTheory.WF_DEF]
  \\ rw[substTheory.vR_def]
  \\ metis_tac[]);

val infer_d_side_thm = Q.store_thm ("infer_d_side_thm",
  `!mn decls env d st. infer_d_side mn decls env d st`,
  rw [infer_d_side_def] >>
  TRY(Cases_on `st` \\ fs[]) >>
  rpt (FST_TO_PAIR_TAC >> simp_monad >> rw[]) >> simp_monad >>
  fs [init_state_def,success_eqns,inferTheory.init_state_def] >>
  simp_monad >> rw [apply_subst_list_side_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp_monad >> rw[] >>
  fs[infer_st_component_equality] >>
  TRY(FIRST[irule_infer_e_side_thm,
	    irule_infer_p_side_thm,
	    irule add_constraint_side_thm,
	    irule add_constraints_side_thm,
	    irule add_constraints_side_thm]) >>
  fs[infer_st_component_equality,n_fresh_uvar_subst,t_wfs_FEMPTY] >>
  imp_res_tac pure_add_constraints_wfs >>
  imp_res_tac infer_e_wfs >>
  imp_res_tac infer_p_wfs >>
  imp_res_tac unifyTheory.t_unify_wfs >>
  fs[infer_st_component_equality,n_fresh_uvar_subst,t_wfs_FEMPTY]);

val _ = infer_d_side_thm |> SPEC_ALL |> EQT_INTRO |> update_precondition

val _ = translate (def_of_const ``extend_dec_ienv``);
val _ = translate (def_of_const ``append_decls``);

val _ = m_translate (def_of_const ``infer_ds``);
val _ = print "Translated infer_ds\n";

val infer_ds_side_thm = Q.store_thm ("infer_ds_side_thm",
  `!mn decls env ds st. infer_ds_side st mn decls env ds`,
  Induct_on`ds`>>fs[Once (fetch "-" "infer_ds_side_def"),FORALL_PROD]>>rw[]>>
  Cases_on`ds`>>fs[]>>
  rpt (FST_TO_PAIR_TAC >> simp_monad >> rw[]) >> simp_monad >>
  rw[Once (fetch "-" "infer_ds_side_def"),FORALL_PROD])
  |> update_precondition

val MEM_anub = prove(``
  ∀e1M ls k v1.
  MEM (k,v1) (anub e1M ls) ⇒
  MEM (k,v1) e1M``,
  ho_match_mp_tac anub_ind>>rw[anub_def]>>metis_tac[]);

val nsSub_translate_def = tDefine "nsSub_translate"
  `nsSub_translate path R b1 b2 ⇔
   case b1 of (Bind e1V e1M) => case b2 of (Bind e2V e2M) =>
     EVERY (λ(k,v1).
       case ALOOKUP e2V k of
         NONE => F
       | SOME v2 => R (mk_id (REVERSE path) k) v1 v2) (anub e1V []) ∧
     EVERY (λ(k,v1).
       case ALOOKUP e2M k of
         NONE => F
       | SOME v2 => nsSub_translate (k::path) R v1 v2) (anub e1M [])`
  (wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0) (\x.0) (\x.0) env)`
   >> rw[]
   >> imp_res_tac MEM_anub >> last_x_assum kall_tac
   >> Induct_on `e1M`
   >> rw [namespaceTheory.namespace_size_def]
   >> fs [namespaceTheory.namespace_size_def]);

val ALOOKUP_MEM_anub = prove(
  ``∀ls acc k v.
    MEM (k,v) (anub ls acc) ⇔
    (ALOOKUP ls k = SOME v ∧ ¬MEM k acc)``,
    ho_match_mp_tac anub_ind>>rw[anub_def]>>IF_CASES_TAC>>fs[]>>
    metis_tac[]);

val MEM_ALOOKUP = prove(``
  ∀ls k. MEM k (MAP FST ls) ⇒ ∃v. ALOOKUP ls k = SOME v``,
  Induct>>fs[MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]>>rw[]>>
  metis_tac[]);

val nsSub_thm = prove(``
  ∀ls R e1 e2. nsSub_compute ls R e1 e2 ⇔ nsSub_translate ls R e1 e2``,
  ho_match_mp_tac (fetch "-" "nsSub_translate_ind")>>
  rw[]>>
  simp[Once nsSub_translate_def]>> every_case_tac>>
  simp[namespacePropsTheory.nsSub_compute_def]>>
  fs[PULL_FORALL,namespacePropsTheory.alistSub_def]>>
  fs[namespacePropsTheory.alist_rel_restr_thm]>> eq_tac>>rw[]
  >-
    (match_mp_tac EVERY_anub_suff>>rw[]>>every_case_tac>>
    imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS]>>
    res_tac>>fs[]>>rfs[])
  >-
    (match_mp_tac EVERY_anub_suff>>rw[]>>every_case_tac>>
    imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS]>>
    res_tac>>fs[]>>rfs[]>>
    fs[ALOOKUP_MEM_anub]>>
    metis_tac[])
  >>
    (fs[ALOOKUP_MEM_anub,EVERY_MEM,FORALL_PROD]>>
    imp_res_tac MEM_ALOOKUP>>fs[]>>
    res_tac>>fs[]>>every_case_tac>>fs[]))

val _ = translate (def_of_const ``nub``)

val _ = m_translate (def_of_const ``check_specs``)
val _ = print "Translated check_specs\n";

val check_specs_side_def = theorem"check_specs_side_def";

val check_specs_side_thm = Q.store_thm ("check_specs_side_thm",
  `!a b c d e st. check_specs_side st a b c d e`,
  ho_match_mp_tac check_specs_ind >>
  rw[] >>
  rw [Once check_specs_side_def, rich_listTheory.LENGTH_COUNT_LIST] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  rpt (FST_TO_PAIR_TAC >> simp_monad >> rw[])
  >-(
      qmatch_goalsub_abbrev_tac `nsAppend B C`>>
      qmatch_goalsub_abbrev_tac`check_specs_side st a (nsAppend B C) (c with inf_defined_types := A ++ _) _ _`>>
      first_x_assum(qspecl_then[`nsAppend B C`,`A`,`B`,`st`] assume_tac)>>
      qmatch_asmsub_abbrev_tac `check_specs_side _ _ _ _ G1 _`>>
      qmatch_goalsub_abbrev_tac `check_specs_side _ _ _ _ G2 _`>>
      `G1 = G2` by fs[markerTheory.Abbrev_def,inf_env_component_equality]>>
      rw[]) >>
  qpat_x_assum `~A` (fn x => fs[x]));

val _ = check_specs_side_thm |> SPEC_ALL |> EQT_INTRO |> update_precondition

val _ = m_translate (def_of_const ``check_tscheme_inst_aux``)
val _ = m_translate_run  (def_of_const ``run_check_tscheme_inst_aux``)
val _ = translate (def_of_const ``check_tscheme_inst``)

val check_tscheme_inst_aux_side_def = fetch "-" "check_tscheme_inst_aux_side_def"
val run_check_tscheme_inst_aux_side_def = fetch "-" "run_check_tscheme_inst_aux_side_def"
val check_tscheme_inst_side_def = fetch "-" "check_tscheme_inst_side_def"

val n_fresh_uvar_wfs = prove(``
  ∀n r a r'.
    t_wfs r.subst ∧ n_fresh_uvar n r = (Success a,r') ⇒ t_wfs r'.subst``,
  ho_match_mp_tac n_fresh_uvar_ind>> rw[]>>
  pop_assum mp_tac >> simp[Once n_fresh_uvar_def]>> simp_monad >>
  IF_CASES_TAC>>fs[st_ex_return_def,st_ex_bind_def,fresh_uvar_def]>>every_case_tac>>rw[]>>
  fs[]>>
  first_assum match_mp_tac>>fs[]>>
  fs[get_next_uvar_def,set_next_uvar_def] >> rw[] >>
  qexists_tac`r with next_uvar := r.next_uvar +1`>>
  fs[]);

val check_tscheme_inst_side = prove(``
  ∀a b c. check_tscheme_inst_side a b c``,
  rw[check_tscheme_inst_side_def,run_check_tscheme_inst_aux_side_def]>>
  rw[check_tscheme_inst_aux_side_def,add_constraint_side_def,init_state_def]>>
  rpt (FST_TO_PAIR_TAC >> simp_monad >> rw[])>>
  imp_res_tac n_fresh_uvar_wfs>>
  pop_assum match_mp_tac>>
  EVAL_TAC>>fs[unifyTheory.t_wfs_def])|> update_precondition

val _ = translate (check_weak_ienv_def |> SIMP_RULE std_ss [nsSub_thm])

val _ = translate (def_of_const ``check_weak_decls``)
val _ = m_translate (def_of_const ``check_signature``)
val _ = print "Translated check_signature\n";

val check_signature_side = prove(``
  ∀a b c d e f g. check_signature_side a b c d e f g``,
  Cases_on`f`>>rw[fetch"-""check_signature_side_def"]
  >-(Cases_on `g`>>fs[])>>
  rw[]) |> update_precondition

val _ = translate (def_of_const ``ienvLift``)
val _ = m_translate (def_of_const ``infer_top``)
val _ = m_translate (def_of_const ``infer_prog``)
val _ = print "Translated infer_prog\n";

val infer_prog_side = prove(``
  ∀a b c d. infer_prog_side a b c d ⇔ T``,
  Induct_on`d`>>fs[Once (fetch "-" "infer_prog_side_def"),FORALL_PROD]>>rw[]>>
  Cases_on`d`>>fs[]>>rw[Once (fetch "-" "infer_prog_side_def")])
 |> update_precondition

val _ = m_translate (def_of_const ``infertype_prog_aux``)
val _ = m_translate_run (def_of_const ``infertype_prog``);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
