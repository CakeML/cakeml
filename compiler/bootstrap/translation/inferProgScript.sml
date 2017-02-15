open preamble
     parserProgTheory inferTheory
     ml_translatorLib ml_translatorTheory
     semanticPrimitivesTheory inferPropsTheory

val _ = new_theory "inferProg"

val _ = translation_extends "parserProg";

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
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* TODO:
   these things are a discrepancy between HOL's standard libraries and
   mllist. probably the compiler should be using the mllist versions? *)

val res = translate ZIP;
val res = translate EL;

val zip_1_side_def = theorem"zip_1_side_def";

val zip_1_side_thm = Q.prove(
  `∀p. zip_1_side p ⇔ LENGTH (FST p) = LENGTH (SND p)`,
  gen_tac \\ PairCases_on`p`
  \\ qid_spec_tac`p1` \\ Induct_on`p0`
  \\ rw[Once zip_1_side_def,LENGTH_NIL_SYM]
  \\ Cases_on`p1` \\ fs[]) |> update_precondition;

val el_side_def = Q.prove(
  `!n xs. el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "el_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;
(* -- *)

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
  [MEMBER_INTRO, MAP, OPTION_BIND_THM, st_ex_bind_def,
   st_ex_return_def, failwith_def, guard_def, read_def, write_def]);

val _ = translate (def_of_const``lookup_st_ex``)
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
  `!op. (ast$op_CASE op x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29) y =
         (ast$op_CASE op
            (\z. x1 z y)
            (\z. x2 z y)
            (\z1 z2. x3 z1 z2 y)
            (\z1 z2 z3. x4 z1 z2 z3 y)
            (x5 y) (x6 y) (x7 y) (x8 y) (x9 y) (x10 y) (x11 y) (x12 y) (x13 y)
            (\z. x14 z y) (\z. x15 z y)
            (x16 y) (x17 y)
            (\z. x18 z y)
            (x19 y) (x20 y) (x21 y) (x22 y) (x23 y) (x24 y) (x25 y) (x26 y) (x27 y) (x28 y)
            (\z. x29 z y))`,
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
val _ = translate (infer_def ``apply_subst_list``);
val _ = translate (infer_def ``add_constraint``);

val add_constraint_side_def = definition"add_constraint_side_def"

val _ = translate (infer_def ``add_constraints``);

val add_constraints_side_thm = Q.store_thm("add_constraints_side_thm",
  `∀x y z. t_wfs z.subst ⇒ add_constraints_side x y z`,
  recInduct add_constraints_ind
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[Once(theorem"add_constraints_side_def")]
  \\ rw[add_constraint_side_def]
  \\ first_x_assum match_mp_tac
  \\ fs[add_constraint_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[unifyTheory.t_unify_wfs]);
    
val _ = translate (infer_def ``constrain_op``
                   |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV pmatch_app_distrib_conv)));

val _ = translate (infer_def ``t_to_freevars``);

val _ = translate (typeSystemTheory.build_ctor_tenv_def
                   |> CONV_RULE(((STRIP_QUANT_CONV o funpow 3 RAND_CONV o
                                  funpow 2 (LAND_CONV o PairRules.PABS_CONV) o
                                  funpow 2 RAND_CONV o funpow 2 LAND_CONV)
                                 (ONCE_REWRITE_CONV [GSYM ETA_AX]))))

val type_name_subst_side_def = theorem"type_name_subst_side_def";

val type_name_subst_side_thm = Q.store_thm("type_name_subst_side_thm",
  `∀a b. check_type_names a b
    ⇒ type_name_subst_side a b`,
  ho_match_mp_tac terminationTheory.type_name_subst_ind >>
  rw[Once type_name_subst_side_def] >>
  rw[Once type_name_subst_side_def] >>
  fs[terminationTheory.check_type_names_def,EVERY_MEM])

val build_ctor_tenv_side_def = definition"build_ctor_tenv_side_def";

val build_ctor_tenv_side_thm = Q.store_thm("build_ctor_tenv_side_thm",
  `∀x y z. check_ctor_tenv x y z ⇒ build_ctor_tenv_side x y z`,
  rw[build_ctor_tenv_side_def] >>
  fs[typeSystemTheory.check_ctor_tenv_def] >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  last_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  match_mp_tac type_name_subst_side_thm >>
  pop_assum ACCEPT_TAC);

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

val _ = translate (infer_def ``infer_p``)

val infer_p_side_def = theorem"infer_p_side_def";

val infer_p_side_thm = Q.store_thm ("infer_p_side_thm",
  `(!cenv p st. t_wfs st.subst ⇒ infer_p_side cenv p st) ∧
   (!cenv ps st. t_wfs st.subst ⇒ infer_ps_side cenv ps st)`,
  ho_match_mp_tac infer_p_ind >>
  rw [] >>
  rw [Once infer_p_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [add_constraint_side_def] >>
  TRY(qmatch_goalsub_rename_tac`FST pp` >> PairCases_on`pp`) >> fs[] >>
  TRY(match_mp_tac add_constraints_side_thm >> fs[]) >>
  every_case_tac >> fs[] >>
  metis_tac[infer_p_wfs,PAIR,type_name_subst_side_thm]);

val _ = translate (infer_def ``infer_e``)

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

val EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``AST_ID_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]

val EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`AST_ID_TYPE (LIST_TYPE CHAR)`
  |> SIMP_RULE std_ss [EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR]

val EqualityType_AST_TCTOR_TYPE = find_equality_type_thm``AST_TCTOR_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR]

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
  METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR])

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

val EqualityType_AST_T_TYPE = Q.prove(
  `EqualityType AST_T_TYPE`,
  simp[EqualityType_def] >>
  METIS_TAC[AST_T_TYPE_no_closures,AST_T_TYPE_types_match,AST_T_TYPE_11])
  |> store_eq_thm

val AST_PAT_TYPE_no_closures = Q.prove(
  `∀a b. AST_PAT_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  TRY (
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,
            EqualityType_AST_T_TYPE,
            EqualityType_LIST_TYPE_CHAR])

val AST_PAT_TYPE_types_match = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def,types_match_def,ctor_same_type_def] >> rw[] >>
  TRY (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,ctor_same_type_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[types_match_def,ctor_same_type_def] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_AST_T_TYPE])

val AST_PAT_TYPE_11 = Q.prove(
  `∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def] >> rw[] >-
  ( METIS_TAC[EqualityType_def,EqualityType_AST_T_TYPE] )
  >- (
    rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    `x_4 = o' ⇔ v3_1 = v3_1'` by METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
    simp[] >>
    ntac 3 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR])

val EqualityType_AST_PAT_TYPE = Q.prove(
  `EqualityType AST_PAT_TYPE`,
  METIS_TAC[EqualityType_def,AST_PAT_TYPE_no_closures,AST_PAT_TYPE_types_match,AST_PAT_TYPE_11])
  |> store_eq_thm

val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPW_TYPE = find_equality_type_thm``AST_OPW_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_WORD_SIZE_TYPE = find_equality_type_thm``AST_WORD_SIZE_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_SHIFT_TYPE = find_equality_type_thm``AST_SHIFT_TYPE`` |> SIMP_RULE std_ss []

val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,
                       EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE,EqualityType_AST_OPW_TYPE,
                       EqualityType_AST_WORD_SIZE_TYPE,EqualityType_AST_SHIFT_TYPE,
                       EqualityType_LIST_TYPE_CHAR]

val EqualityType_AST_LOP_TYPE = find_equality_type_thm``AST_LOP_TYPE``
  |> SIMP_RULE std_ss []

val EqualityType_OPTION_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]

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
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE])

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
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE])

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
                  EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
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
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,EqualityType_AST_T_TYPE])

val EqualityType_AST_EXP_TYPE = Q.prove(
  `EqualityType AST_EXP_TYPE`,
  METIS_TAC[EqualityType_def,AST_EXP_TYPE_no_closures,AST_EXP_TYPE_types_match,AST_EXP_TYPE_11])
  |> store_eq_thm

val apply_subst_list_side_def = definition"apply_subst_list_side_def";
val apply_subst_side_def = definition"apply_subst_side_def";
val constrain_op_side_def = definition"constrain_op_side_def";
val infer_e_side_def = theorem"infer_e_side_def";
    
val infer_e_side_thm = Q.store_thm ("infer_e_side_thm",
  `(!menv e st. t_wfs st.subst ⇒ infer_e_side menv e st) /\
   (!menv es st. t_wfs st.subst ⇒ infer_es_side menv es st) /\
   (!menv pes t1 t2 st. t_wfs st.subst ⇒ infer_pes_side menv pes t1 t2 st) /\
   (!menv funs st. t_wfs st.subst ⇒ infer_funs_side menv funs st)`,
  ho_match_mp_tac infer_e_ind >>
  rw [] >>
  rw [Once infer_e_side_def, add_constraint_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  rw [constrain_op_side_def, add_constraint_side_def,
      apply_subst_side_def, apply_subst_list_side_def] >>
  fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
  TRY (imp_res_tac infer_e_wfs >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       rw [] >>
       NO_TAC) >|
  [match_mp_tac add_constraints_side_thm >>
       rw [] >>
       prove_tac [infer_e_wfs],
   match_mp_tac add_constraints_side_thm >>
       rw [] >>
       imp_res_tac infer_e_wfs >>
       fs [],
   imp_res_tac infer_e_wfs >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       imp_res_tac pure_add_constraints_wfs >>
       rw [],
   every_case_tac \\ fs[] \\ metis_tac[infer_e_wfs],
   every_case_tac \\ fs[type_name_subst_side_thm],
   prove_tac [infer_p_side_thm],
   every_case_tac >>
       fs [] >>
       PairCases_on `x25` >>
       imp_res_tac infer_p_wfs >>
       fs [],
   every_case_tac >>
       fs [] >>
       PairCases_on `x25` >> fs[LAMBDA_PROD] >>
       imp_res_tac infer_p_wfs >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       fs [],
   every_case_tac >>
       fs [] >>
       imp_res_tac infer_e_wfs >>
       fs [] >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       PairCases_on `x25` >>
       imp_res_tac infer_p_wfs >>
       fs [],
   every_case_tac >>
       fs [] >>
       qpat_assum `!st. t_wfs st.subst ⇒ infer_pes_side _ _ _ _ st` match_mp_tac >>
       fs [] >>
       imp_res_tac infer_e_wfs >>
       fs [] >>
       imp_res_tac unifyTheory.t_unify_wfs >>
       PairCases_on `x25` >>
       imp_res_tac infer_p_wfs >>
       fs []]);

val _ = translate (infer_def ``infer_d``)

val infer_d_side_def = definition"infer_d_side_def";

val generalise_list_length = Q.prove (
  `!min start s x.
    LENGTH x = LENGTH (SND (SND (generalise_list min start s (MAP f (MAP SND x)))))`,
  induct_on `x` >>
  srw_tac[] [generalise_def] >>
  srw_tac[] [] >>
  metis_tac [SND]);

val infer_d_side_thm = Q.store_thm ("infer_d_side_thm",
  `!mn decls env d st. infer_d_side mn decls env d st`,
  rw [infer_d_side_def] >>
  fs [init_state_def, success_eqns] >>
  rw [add_constraint_side_def, apply_subst_list_side_def] >>
  `t_wfs init_infer_state.subst`
            by rw [init_infer_state_def, unifyTheory.t_wfs_def] >|
  [match_mp_tac (hd (CONJUNCTS infer_e_side_thm)) >>
       rw [],
   match_mp_tac (hd (CONJUNCTS infer_p_side_thm)) >>
       rw [] >>
       imp_res_tac infer_e_wfs >>
       fs [],
   every_case_tac >>
       fs [] >>
       imp_res_tac infer_e_wfs >>
       fs [] >>
       PairCases_on `v20` >>
       imp_res_tac infer_p_wfs >>
       fs [] >>
       prove_tac [],
   every_case_tac >>
       fs [] >>
       imp_res_tac infer_e_wfs >>
       fs [] >>
       PairCases_on `v20` >>
       imp_res_tac infer_p_wfs >>
       fs [] >>
       prove_tac [unifyTheory.t_unify_wfs],
   metis_tac [generalise_list_length],
   match_mp_tac (List.nth (CONJUNCTS infer_e_side_thm, 3)) >>
       rw [],
   match_mp_tac add_constraints_side_thm >>
       rw [] >>
       imp_res_tac infer_e_wfs >>
       fs [],
   imp_res_tac pure_add_constraints_wfs >>
       imp_res_tac infer_e_wfs >>
       fs [],
   match_mp_tac build_ctor_tenv_side_thm >>
   last_x_assum mp_tac >> rw[],
   match_mp_tac type_name_subst_side_thm>> every_case_tac>>fs[],
   match_mp_tac type_name_subst_side_thm>> every_case_tac>>fs[EVERY_MEM]
   ]);

val _ = infer_d_side_thm |> SPEC_ALL |> EQT_INTRO |> update_precondition

val _ = translate (infer_def ``infer_ds``)
val _ = translate (infer_def ``check_weakE``)

val check_weake_side_def = theorem"check_weake_side_def";

val check_weake_side_thm = Q.store_thm ("check_weake_side_thm",
  `!env specs st. check_weake_side env specs st`,
  induct_on `specs` >>
  rw [] >>
  rw [add_constraint_side_def, Once check_weake_side_def] >>
  fs [success_eqns, init_state_def] >>
  rw [] >>
  fs [init_infer_state_def, unifyTheory.t_wfs_def]);

val _ = check_weake_side_thm |> SPEC_ALL |> EQT_INTRO |> update_precondition

val _ = translate (infer_def ``check_specs``)

val check_specs_side_def = theorem"check_specs_side_def";

val check_specs_side_thm = Q.store_thm ("check_specs_side_thm",
  `!mn decls z y cenv env specs st. check_specs_side mn decls z y cenv env specs st`,
  (check_specs_ind |> SPEC_ALL |> UNDISCH |> Q.SPEC`v`
    |> SIMP_RULE std_ss [GSYM FORALL_PROD] |> Q.GEN`v` |> DISCH_ALL
    |> Q.GEN`P` |> ho_match_mp_tac) >>
  rw [] >>
  rw [Once check_specs_side_def, rich_listTheory.LENGTH_COUNT_LIST] >>
  TRY (match_mp_tac build_ctor_tenv_side_thm >>rw[])>>
  TRY (match_mp_tac type_name_subst_side_thm>>every_case_tac>>fs[EVERY_MEM])>>
  fsrw_tac[boolSimps.ETA_ss][]);

val _ = check_specs_side_thm |> SPEC_ALL |> EQT_INTRO |> update_precondition

val _ = translate (infer_def ``check_signature``)

val _ = translate (infer_def ``infer_top``)

val infer_prog_def = Q.prove(`
  (∀idecls ienv x.
      infer_prog idecls ienv [] x =
      (Success (empty_inf_decls,(FEMPTY,FEMPTY),FEMPTY,([],[]),[]),x)) ∧
   ∀idecls ienv top ds x.
     infer_prog idecls ienv (top::ds) x =
     case infer_top idecls ienv top x of
       (Success y,s) =>
         (case
            infer_prog (append_decls (FST y) idecls)
              (ienv with <|inf_t := merge_mod_env (FST (SND y)) ienv.inf_t;
                inf_c :=
                  merge_alist_mod_env (FST (SND (SND (SND y))))
                    ienv.inf_c;
                inf_v := SND (SND (SND (SND y))) ++ ienv.inf_v;
                inf_m := FST (SND (SND y)) ⊌ ienv.inf_m|>) ds s
          of
            (Success y',s) =>
              (Success
                 (append_decls (FST y') (FST y),
                  merge_mod_env (FST (SND y')) (FST (SND y)),
                  FST (SND (SND y')) ⊌ FST (SND (SND y)),
                  merge_alist_mod_env (FST (SND (SND (SND y'))))
                    (FST (SND (SND (SND y)))),
                  SND (SND (SND (SND y'))) ++ SND (SND (SND (SND y)))),
               s)
          | (Failure e,s) => (Failure e,s))
     | (Failure e,s) => (Failure e,s)`,
     rw[infer_prog_def]>>EVAL_TAC>>
     BasicProvers.EVERY_CASE_TAC>>PairCases_on`a`>>
     fs[]>>
     PairCases_on`a'`>>fs[]);

(* translating infer ``infer_prog`` doesn't work, maybe because
  there is an explicit record not written as an update inside
*)
val _ = translate infer_prog_def;

val _ = translate (infer_def ``infertype_prog``);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
