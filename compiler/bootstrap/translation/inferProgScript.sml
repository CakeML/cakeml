open preamble parserProgTheory
     reg_allocProgTheory inferTheory
     ml_translatorLib ml_translatorTheory
     semanticPrimitivesTheory inferPropsTheory

val _ = new_theory "inferProg"

val _ = translation_extends "reg_allocProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "inferProg");

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
  [MEMBER_INTRO, MAP, OPTION_BIND_THM, inferTheory.st_ex_bind_def,
   inferTheory.st_ex_return_def, failwith_def, guard_def, read_def, write_def]);

val _ = translate (def_of_const ``id_to_string``)
val _ = translate (def_of_const ``lookup_st_ex``)
val _ = translate (def_of_const ``fresh_uvar``)
val _ = translate (def_of_const ``n_fresh_uvar``)
val _ = translate (def_of_const ``init_infer_state``)
val _ = translate (def_of_const ``infer$init_state``)
val _ = translate (def_of_const ``get_next_uvar``)
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
  `!op. (ast$op_CASE op x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40) y =
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
            (* ListAppend *)
            (x38 y)
            (* ConfigGC *)
            (x39 y)
            (* FFI *)
            (\z. x40 z y))`,
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

(* TODO: is it really necessary to prove this four times? *)
val pmatch_row_lemmas =
    map
      (fn goal =>
          Q.prove(goal,
                  Cases_on `(∃v. f v = t ∧ g v)`
                  >> rw[patternMatchesTheory.PMATCH_def,
                        patternMatchesTheory.PMATCH_ROW_def,
                        patternMatchesTheory.PMATCH_ROW_COND_def,
                        some_def,pairTheory.ELIM_UNCURRY]))
      [`PMATCH t ((PMATCH_ROW f g (λt x. h t x)) ::r') x
          = PMATCH t ((PMATCH_ROW f g (λt. h t x))::r)
       ⇔ (∃v. f v = t ∧ g v)
          ∨ (PMATCH t r' x = PMATCH t r)`,
       `PMATCH t ((PMATCH_ROW f g (λ(t,t') x. h t t' x)) ::r') x
          = PMATCH t ((PMATCH_ROW f g (λ(t,t'). h t t' x))::r)
       ⇔ (∃v. f v = t ∧ g v)
          ∨ (PMATCH t r' x = PMATCH t r)`,
       `PMATCH t ((PMATCH_ROW f g (λ(t,t',t'') x. h t t' t'' x)) ::r') x
          = PMATCH t ((PMATCH_ROW f g (λ(t,t',t''). h t t' t'' x))::r)
       ⇔ (∃v. f v = t ∧ g v)
          ∨ (PMATCH t r' x = PMATCH t r)`,
       `PMATCH t ((PMATCH_ROW f g (λ(t,t',t'',t''') x. h t t' t'' t''' x)) ::r') x
          = PMATCH t ((PMATCH_ROW f g (λ(t,t',t'',t'''). h t t' t'' t''' x))::r)
       ⇔ (∃v. f v = t ∧ g v)
          ∨ (PMATCH t r' x = PMATCH t r)`,
       `PMATCH t ((PMATCH_ROW f g (λ(t,t',t'',t''',t'''') x. h t t' t'' t''' t'''' x)) ::r') x
          = PMATCH t ((PMATCH_ROW f g (λ(t,t',t'',t''',t''''). h t t' t'' t''' t'''' x))::r)
       ⇔ (∃v. f v = t ∧ g v)
          ∨ (PMATCH t r' x = PMATCH t r)`
      ]

(* Attempts to convert (pmatch) expressions of the form

     (case x of
       p1 => λ v1. b1 v1
     | p2 => λ v2. b2 v2
     | ....) a

into

     case x of
       p1 => b1 a
     | p2 => b2 a
     | ....
 *)
fun pmatch_app_distrib_conv tm =
  let
    fun mk_pmatch_beta tm =
    let
      val (pm_exp,arg) = dest_comb tm
      val (pmatch,pml) = dest_comb pm_exp
      val (rows,row_type) = listSyntax.dest_list pml
      fun gify arg row =
        let
          val (pmatch_row,[pat,guard,body]) = strip_comb row
          val (binders,term) = dest_pabs body
        in
          Term(`PMATCH_ROW ` @ map ANTIQUOTE [pat,guard,mk_pabs(binders,beta_conv(mk_comb(term,arg)))])
        end
      val new_rows = map (gify arg) rows
      val new_row_type = type_of(hd new_rows)
      val new_list = listSyntax.mk_list(map (gify arg) rows, new_row_type)
    in
      mk_eq(tm,
            Term(`PMATCH` @ [ANTIQUOTE(rand pmatch),ANTIQUOTE(new_list)]))
    end
    val g = mk_pmatch_beta tm
  in
    prove(g,
      CONV_TAC(Ho_Rewrite.PURE_REWRITE_CONV pmatch_row_lemmas) >> rw[pairTheory.ELIM_UNCURRY])
  end

fun full_infer_def aggressive const = let
  val def = if aggressive then
              def_of_const const
              |> RW1 [FUN_EQ_THM]
              |> RW [op_apply,if_apply,option_case_apply,pr_CASE]
              |> SIMP_RULE (std_ss) [op_apply,if_apply,
                   option_case_apply,list_apply]
            else
              def_of_const const
              |> RW1 [FUN_EQ_THM]
              |> RW [op_apply,if_apply,option_case_apply]
              |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  val def = let
    val s_var = mk_var("state", ``: (num |-> infer_t) infer_st``)
    val s = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                |> dest_eq |> fst |> rand |> type_of
    val def = INST_TYPE (match_type s (type_of s_var)) def
    in def end handle HOL_ERR _ => def
  val () = fix_infer_induction_thm def
  in def end

val infer_def = full_infer_def false;
val aggr_infer_def = full_infer_def true;

val _ = translate (infer_def ``apply_subst``);
val _ = fetch "-" "apply_subst_side_def" |> update_precondition;

val _ = translate (infer_def ``apply_subst_list``);
val _ = fetch "-" "apply_subst_list_side_def" |> update_precondition;

val _ = translate infer_tTheory.inf_type_to_string_def;

val _ = translate (infer_def ``add_constraint``);

val add_constraint_side_def = definition"add_constraint_side_def"

val _ = translate (infer_def ``add_constraints``);

val add_constraint_side_thm = Q.store_thm("add_constraint_side_thm",
  `∀l x y z. t_wfs z.subst ⇒ add_constraint_side l x y z`,
  rw[add_constraint_side_def]);

val add_constraints_side_thm = Q.store_thm("add_constraints_side_thm",
  `∀l x y z. t_wfs z.subst ⇒ add_constraints_side l x y z`,
  recInduct add_constraints_ind
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[add_constraint_side_def]
  \\ first_x_assum match_mp_tac
  \\ fs[add_constraint_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[unifyTheory.t_unify_wfs]);

val def = infer_def ``constrain_op``
(*
  val tm = def |> SPEC_ALL |> concl |> rand
*)

val r = translate
  (def |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV pmatch_app_distrib_conv)));

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

val _ = translate (infer_def ``check_freevars``
                   |> RW1 [EVERY_EQ_EVERY])

val _ = translate (infer_def ``check_dup_ctors``
                   |> SIMP_RULE std_ss [EVERY_INTRO,LET_DEF])

val _ = translate (infer_def ``check_ctor_tenv``)

val _ = translate (infer_def ``is_value``
            |> RW1 [prove(``~b <=> (b = F)``,SIMP_TAC std_ss [])]
            |> RW1 [EVERY_EQ_EVERY])

val infer_p_lemma = infer_def ``infer_p``

val inter_p_lemma1 = prove(
  ``(infer_p l ienv p x =
       case p of (Plit (Char s)) => infer_p l ienv (Plit (Char s)) x
               | pat => infer_p l ienv pat x) /\
    (infer_ps l ienv ps x =
       case ps of [] => infer_ps l ienv [] x
               | pat => infer_ps l ienv pat x)``,
  every_case_tac \\ fs [])
  |> REWRITE_RULE [infer_p_lemma];

val x_var = inter_p_lemma1 |> CONJUNCT1 |> concl |> dest_eq |> fst |> rand

val infer_p_ind = save_thm("infer_p_ind",
  inferTheory.infer_p_ind
  |> Q.SPEC `\v1 v2 v3. !^x_var. P0 v1 v2 v3 ^x_var`
  |> Q.SPEC `\v1 v2 v3. !^x_var. P1 v1 v2 v3 ^x_var`
  |> Q.GENL [`P0`,`P1`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV));

val res = translate inter_p_lemma1;

val infer_p_side_def = theorem"infer_p_side_def";

val infer_p_side_thm = Q.store_thm ("infer_p_side_thm",
  `(!l cenv p st. t_wfs st.subst ⇒ infer_p_side l cenv p st) ∧
   (!l cenv ps st. t_wfs st.subst ⇒ infer_ps_side l cenv ps st)`,
  ho_match_mp_tac infer_p_ind >>
  rw [] >>
  rw [Once infer_p_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [add_constraint_side_def] >>
  TRY(qmatch_goalsub_rename_tac`FST pp` >> PairCases_on`pp`) >> fs[] >>
  TRY(match_mp_tac add_constraints_side_thm >> fs[]) >>
  every_case_tac >> fs[] >> rw[] >>
  metis_tac[infer_p_wfs,PAIR]);

val infer_e_lemma = infer_def ``infer_e``;

val inter_e_lemma1 = prove(
  ``(infer_e l ienv x y =
       case x of (Lit (Char c)) => infer_e l ienv (Lit (Char c)) y
               | pat => infer_e l ienv pat y) /\
    (infer_es l ienv ps y =
       case ps of [] => infer_es l ienv [] y
               | pat => infer_es l ienv pat y) /\
    (infer_pes l ienv pes z1 z2 tt =
       case pes of [] => infer_pes l ienv [] z1 z2 tt
                | ((x1,x2)::xs) => infer_pes l ienv ((x1,x2)::xs) z1 z2 tt) /\
    (infer_funs l ienv funs y =
       case funs of [] => infer_funs l ienv [] y
               | ((x1,x2,x3)::xs) => infer_funs l ienv ((x1,x2,x3)::xs) y)``,
  every_case_tac \\ fs [])
  |> REWRITE_RULE [infer_e_lemma];

val infer_e_ind = save_thm("infer_e_ind",
  inferTheory.infer_e_ind
  |> Q.SPEC `\v1 v2 v3. !^x_var. P0 v1 v2 v3 ^x_var`
  |> Q.SPEC `\v1 v2 v3. !^x_var. P1 v1 v2 v3 ^x_var`
  |> Q.SPEC `\v1 v2 v3 v4 v5. !^x_var. P2 v1 v2 v3 v4 v5 ^x_var`
  |> Q.SPEC `\v1 v2 v3. !^x_var. P3 v1 v2 v3 ^x_var`
  |> Q.GENL [`P0`,`P1`,`P2`,`P3`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV));

val res = translate inter_e_lemma1;

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
val EqaulityType_LIST_TYPE = find_equality_type_thm``LIST_TYPE a``
val EqaulityType_OPTION_TYPE = find_equality_type_thm``OPTION_TYPE a``

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

val AST_AST_T_TYPE_no_closures = Q.prove(
  `∀a b. AST_AST_T_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_AST_T_TYPE_ind >>
  simp[AST_AST_T_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >>
  TRY (
    qpat_x_assum `LIST_TYPE _ _ _` mp_tac >>
    qpat_x_assum `!x. _` mp_tac >>
    rename [`LIST_TYPE AST_AST_T_TYPE xs v`] >>
    rpt (pop_assum kall_tac) >>
    map_every qid_spec_tac[`v`,`xs`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR]);

val AST_AST_T_TYPE_types_match = Q.prove(
  `∀a b c d. AST_AST_T_TYPE a b ∧ AST_AST_T_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_AST_T_TYPE_ind >>
  simp[AST_AST_T_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >> rw[]
  THEN1 (
    Cases_on`c`>>fs[AST_AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    reverse conj_tac >-
      METIS_TAC[EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
                EqualityType_def] >>
    rw[] >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    rename [`LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _`] >>
    map_every qid_spec_tac[`v1`,`v2`,`ys`,`xs`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS]
    THEN1 (Cases >> fs [LIST_TYPE_def,types_match_def,
                        ctor_same_type_def,PULL_EXISTS]) >>
    rw[] >> Cases_on`ys`>>fs[LIST_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[] )
  THEN1 (
    Cases_on`c`>>fs[AST_AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    rename [`LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _`] >>
    map_every qid_spec_tac[`v1`,`v2`,`ys`,`xs`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS]
    THEN1 (Cases >> fs [LIST_TYPE_def,types_match_def,
                        ctor_same_type_def,PULL_EXISTS]) >>
    rw[] >> Cases_on`ys`>>fs[LIST_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[AST_AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`c`>>fs[AST_AST_T_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_def]));
val _ = print "Proved AST_AST_T_TYPE_types_match\n";

val AST_AST_T_TYPE_11 = Q.prove(
  `∀a b c d. AST_AST_T_TYPE a b ∧ AST_AST_T_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_AST_T_TYPE_ind >>
  simp[AST_AST_T_TYPE_def,PULL_EXISTS] >> rw[]
  THEN1
   (Cases_on`c`>>fs[AST_AST_T_TYPE_def] >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    rename [`LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _`] >>
    rpt strip_tac >>
    qsuff_tac `xs = ys <=> v1 = v2`
    THEN1 (METIS_TAC[EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
             EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR]) >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    map_every qid_spec_tac[`v1`,`v2`,`ys`,`xs`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    Cases_on `ys` >> fs [LIST_TYPE_def,PULL_EXISTS] >>
    metis_tac [])
  THEN1
   (Cases_on`c`>>fs[AST_AST_T_TYPE_def] >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    rename [`LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _`] >>
    rpt strip_tac >>
    qsuff_tac `xs = ys <=> v1 = v2`
    THEN1 (METIS_TAC[EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
             EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR]) >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    map_every qid_spec_tac[`v1`,`v2`,`ys`,`xs`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    Cases_on `ys` >> fs [LIST_TYPE_def,PULL_EXISTS] >>
    metis_tac [])
  THEN1
   (Cases_on`c`>>fs[AST_AST_T_TYPE_def] >> metis_tac [])
  THEN1
   (Cases_on`c`>>fs[AST_AST_T_TYPE_def] >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    metis_tac [EqualityType_def,EqualityType_LIST_TYPE_CHAR]));
val _ = print "Proved AST_AST_T_TYPE_11\n";

val EqualityType_AST_AST_T_TYPE = Q.prove(
  `EqualityType AST_AST_T_TYPE`,
  simp[EqualityType_def] >>
  METIS_TAC[AST_AST_T_TYPE_no_closures,AST_AST_T_TYPE_types_match,AST_AST_T_TYPE_11])
  |> store_eq_thm
val _ = print "Proved EqualityType_AST_AST_T_TYPE\n";

val AST_PAT_TYPE_no_closures = Q.prove(
  `∀a b. AST_PAT_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  TRY (
    pop_assum mp_tac >>
    qmatch_rename_tac `LIST_TYPE _ xs v ==> _` >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v`,`xs`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS,AST_AST_T_TYPE_def] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,
            EqualityType_AST_AST_T_TYPE,
            EqualityType_LIST_TYPE_CHAR])
val _ = print "Proved AST_PAT_TYPE_no_closures\n";

val AST_PAT_TYPE_types_match = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def,types_match_def,ctor_same_type_def] >> rw[] >>
  res_tac >>
  TRY (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    qmatch_rename_tac `LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _` >>
    qpat_x_assum `!x. _` mp_tac >>
    rpt (pop_assum kall_tac) >>
    map_every qid_spec_tac[`v1`,`ys`,`v2`,`xs`] >>
    Induct_on `ys` \\ Cases_on `xs` \\ fs [LIST_TYPE_def,PULL_EXISTS]
    \\ fs [types_match_def,ctor_same_type_def]
    \\ metis_tac []) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
            EqualityType_AST_AST_T_TYPE,EqaulityType_LIST_TYPE])
val _ = print "Proved AST_PAT_TYPE_types_match\n";

val AST_PAT_TYPE_11 = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def] >> rw[] >-
  ( METIS_TAC[EqualityType_def,EqualityType_AST_AST_T_TYPE] )
  >- (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    qmatch_rename_tac `LIST_TYPE _ xs v1 ==> LIST_TYPE _ ys v2 ==> _` >>
    rpt strip_tac >>
    qsuff_tac `xs = ys <=> v1 = v2`
    THEN1 (METIS_TAC[EqualityType_NAMESPACE_ID_TYPE_LIST_TYPE_CHAR_LIST_TYPE_CHAR,
             EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR,
             EqaulityType_OPTION_TYPE]) >>
    rpt (qpat_x_assum `LIST_TYPE _ _ _` mp_tac) >>
    qpat_x_assum `!x. _` mp_tac >>
    map_every qid_spec_tac[`v1`,`v2`,`ys`,`xs`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    Cases_on `ys` >> fs [LIST_TYPE_def,PULL_EXISTS] >>
    metis_tac []) >>
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
            EqualityType_AST_LIT_TYPE,EqualityType_AST_AST_T_TYPE,
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
            EqualityType_AST_LIT_TYPE,EqualityType_AST_AST_T_TYPE,
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
            EqualityType_AST_LIT_TYPE,EqualityType_AST_AST_T_TYPE,
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
val infer_e_side_def = theorem"infer_e_side_def"
  |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL

val infer_e_side_thm = Q.store_thm ("infer_e_side_thm",
  `(!l menv e st. t_wfs st.subst ⇒ infer_e_side l menv e st) /\
   (!l menv es st. t_wfs st.subst ⇒ infer_es_side l menv es st) /\
   (!l menv pes t1 t2 st. t_wfs st.subst ⇒ infer_pes_side l menv pes t1 t2 st) /\
   (!l menv funs st. t_wfs st.subst ⇒ infer_funs_side l menv funs st)`,
  ho_match_mp_tac infer_e_ind >>
  rw [] >>
  rw [Once infer_e_side_def] >>
  TRY (irule add_constraint_side_thm) >>
  TRY (irule add_constraints_side_thm) >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [constrain_op_side_def, apply_subst_side_def, apply_subst_list_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  TRY (irule add_constraint_side_thm) >>
  TRY (irule add_constraints_side_thm) >>
  TRY (imp_res_tac infer_e_wfs >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       rw [] >>
       NO_TAC)
  THEN1 (every_case_tac \\ fs[] \\ imp_res_tac infer_e_wfs >>
         imp_res_tac unifyTheory.t_unify_wfs >>
         imp_res_tac pure_add_constraints_wfs >>
         rw [])
  THEN1 (first_x_assum match_mp_tac
         \\ match_mp_tac pure_add_constraints_wfs
         \\ asm_exists_tac \\ rw[]
         \\ imp_res_tac infer_e_wfs \\ fs[])
  THEN1 (metis_tac [infer_p_side_thm])
  THEN1 (fs [bool_case_eq] \\ rveq >>
         PairCases_on `x26` >>
         imp_res_tac infer_p_wfs >>
         fs [])
  THEN1 (fs [bool_case_eq] \\ rveq >> fs [pair_abs_hack] >>
         first_x_assum match_mp_tac \\ fs [] >>
         PairCases_on `x26` >> fs [] >>
         imp_res_tac infer_p_wfs >>
         imp_res_tac unifyTheory.t_unify_wfs >> fs [])
  THEN1 (fs [bool_case_eq] \\ rveq >> fs [pair_abs_hack] >>
         PairCases_on `x26` >> fs [] >>
         imp_res_tac infer_p_wfs >>
         imp_res_tac infer_e_wfs >>
         imp_res_tac unifyTheory.t_unify_wfs >> fs [])
  THEN1 (fs [bool_case_eq] \\ rveq >> fs [pair_abs_hack] >>
         PairCases_on `x26` >> fs [] >>
         imp_res_tac infer_p_wfs >>
         imp_res_tac infer_e_wfs >>
         imp_res_tac unifyTheory.t_unify_wfs >> fs []));

val _ = translate (infer_def ``infer_d``)
val _ = print "Translated infer_d\n";

val infer_d_side_def = fetch "-" "infer_d_side_def";

val generalise_list_length = Q.prove (
  `!min start s x.
    LENGTH x = LENGTH (SND (SND (generalise_list min start s (MAP f (MAP SND x)))))`,
  induct_on `x` >>
  srw_tac[] [generalise_def] >>
  srw_tac[] [] >>
  metis_tac [SND]);

val gen_d_ind_def = tDefine "gen_d_ind" `
  (gen_d_ind (Dmod n ds) = gen_ds_ind ds) /\
  (gen_d_ind _ = T) /\
  (gen_ds_ind [] = T) /\
  (gen_ds_ind (x::xs) = (gen_d_ind x /\ gen_ds_ind xs))`
  (WF_REL_TAC `measure (\x. case x of INL d => dec_size d
                                    | INR ds => dec1_size ds)`)

val infer_d_side_thm = Q.store_thm ("infer_d_side_thm",
  `(!d ienv s. t_wfs s.subst ==> infer_d_side ienv d s) /\
   (!ds ienv s. t_wfs s.subst ==> infer_ds_side ienv ds s)`,
  ho_match_mp_tac (fetch "-" "gen_d_ind_ind")
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac >>
  once_rewrite_tac [infer_d_side_def] >> rw [] >>
  fs [init_state_def, success_eqns] >>
  rw [apply_subst_list_side_def] >>
  TRY (irule add_constraint_side_thm) >>
  `t_wfs (init_infer_state s).subst`
            by rw [init_infer_state_def, unifyTheory.t_wfs_def] >>
  imp_res_tac infer_e_side_thm >>
  imp_res_tac infer_p_side_thm >>
  imp_res_tac infer_p_wfs >>
  imp_res_tac infer_e_wfs >>
  TRY (fs [] \\ NO_TAC) >>
  fs [bool_case_eq] \\ rveq
  THEN1 (imp_res_tac infer_p_side_thm \\ fs [])
  THEN1 metis_tac [infer_p_wfs,PAIR,infer_p_wfs,infer_e_wfs,unifyTheory.t_unify_wfs]
  THEN1 metis_tac [infer_p_wfs,PAIR,infer_p_wfs,infer_e_wfs,unifyTheory.t_unify_wfs]
  THEN1 (irule (infer_e_side_thm |> CONJUNCTS |> last) \\ fs [])
  THEN1 (match_mp_tac add_constraints_side_thm \\ fs [])
  THEN1 (match_mp_tac pure_add_constraints_wfs \\ asm_exists_tac \\ fs [])
  \\ first_x_assum match_mp_tac \\ metis_tac [infer_d_wfs]);

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

val res = translate infertype_prog_def;

val infertype_prog_side_thm = store_thm("infertype_prog_side_thm",
  ``infertype_prog_side x y``,
  fs [fetch "-" "infertype_prog_side_def"]
  \\ match_mp_tac (CONJUNCT2 infer_d_side_thm) \\ fs [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
