(*
  Defines the repeat function and the corresponding lemma used to prove
  non-termination of programs in cf.
*)
open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTacticsLib cfTheory
open std_preludeTheory;

val _ = new_theory "cfDiv";

val _ = ml_translatorLib.translation_extends "std_prelude";

val POSTd_eq = store_thm("POSTd_eq",
  ``$POSTd Q r h <=> ?io1. r = Div io1 /\ Q io1 /\ emp h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
  \\ eq_tac \\ rw []);

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_translatorLib.ml_prog_update (ml_progLib.add_prog tm I) end

val tailrec_clos = cfTacticsLib.process_topdecs `
  fun tailrec f x =
    case f x of
      Inl x => tailrec f x
    | Inr y => y;
  ` |> rator |> rand |> rand

val tailrec_body = tailrec_clos |> rator |> rand |> rand |> rand |> rand

val mk_inl_def = Define `mk_inl e =
  Let (SOME "x") e (Con(SOME(Short "Inl")) [Var(Short "x")])`

val mk_inr_def = Define `mk_inr e =
  Let (SOME "x") e (Con(SOME(Short "Inr")) [Var(Short "x")])`

val dest_opapp_exp_size = Q.store_thm("dest_opapp_exp_size",
  `!tm f arg. dest_opapp tm = SOME(f,arg)
   ==> exps_size arg < exp_size tm`,
  ho_match_mp_tac cfNormaliseTheory.dest_opapp_ind
  >> rw[cfNormaliseTheory.dest_opapp_def]
  >> every_case_tac >> fs[]
  >> rveq
  >> fs[terminationTheory.size_abbrevs,astTheory.exp_size_def]
  >> first_x_assum dxrule
  >> fs[REWRITE_RULE [terminationTheory.size_abbrevs] terminationTheory.exps_size_thm,
        SUM_APPEND]);

val mk_single_app_def = tDefine "mk_single_app"
  `(mk_single_app fname allow_fname (Raise e) =
    do
      e <- mk_single_app fname F e;
      SOME(Raise e)
    od) /\
   (mk_single_app fname allow_fname (Handle e pes) =
    do
      e <- mk_single_app fname F e;
      pes <- mk_single_appps fname allow_fname pes;
      if allow_fname then
        SOME(Handle (mk_inr e) pes)
      else
        SOME(Handle e pes)
    od) /\
   (mk_single_app fname allow_fname (Lit l) =
    if allow_fname then
      SOME(mk_inr(Lit l))
    else
      SOME(Lit l)) /\
   (mk_single_app fname allow_fname (Con c es) =
    do
      es <- mk_single_apps fname F es;
      if allow_fname then
        SOME(mk_inr(Con c es))
      else
        SOME(Con c es)
    od
   ) /\
   (mk_single_app fname allow_fname (Var(Short v)) =
    if SOME v = fname then
      NONE
    else if allow_fname then
      SOME(mk_inr(Var(Short v)))
    else
      SOME(Var(Short v))
   ) /\
   (mk_single_app fname allow_fname (Var v) =
    if allow_fname then
      SOME(mk_inr(Var v))
    else
      SOME(Var v)
   ) /\
   (mk_single_app fname allow_fname (Fun x e) =
    let fname' = if SOME x = fname then
                   NONE
                 else
                   fname
    in
    do
      e <- mk_single_app fname' F e;
      if allow_fname then
        SOME(mk_inr(Fun x e))
      else
        SOME(Fun x e)
    od
   ) /\
   (mk_single_app fname allow_fname (Log lop e1 e2) =
    do
      e1 <- mk_single_app fname F e1;
      e2 <- mk_single_app fname F e2;
      if allow_fname then
        SOME(mk_inr(Log lop e1 e2))
      else
        SOME(Log lop e1 e2)
    od
   ) /\
   (mk_single_app fname allow_fname (If e1 e2 e3) =
    do
      e1 <- mk_single_app fname F e1;
      e2 <- mk_single_app fname allow_fname e2;
      e3 <- mk_single_app fname allow_fname e3;
      SOME(If e1 e2 e3)
    od
   ) /\
   (mk_single_app fname allow_fname (Mat e pes) =
    do
      e <- mk_single_app fname F e;
      pes <- mk_single_appps fname allow_fname pes;
      SOME(Mat e pes)
    od
   ) /\
   (mk_single_app fname allow_fname (Tannot e ty) =
    do
      e <- mk_single_app fname allow_fname e;
      SOME(Tannot e ty)
    od
   ) /\
   (mk_single_app fname allow_fname (Lannot e l) =
    do
      e <- mk_single_app fname allow_fname e;
      SOME(Lannot e l)
    od
   ) /\
   (mk_single_app fname allow_fname (Let NONE e1 e2) =
    do
      e1 <- mk_single_app fname F e1;
      e2 <- mk_single_app fname allow_fname e2;
      SOME(Let NONE e1 e2)
    od) /\
   (mk_single_app fname allow_fname (Let (SOME x) e1 e2) =
    let fname' =
        if SOME x = fname then
          NONE
        else fname
    in
    do
      e1 <- mk_single_app fname F e1;
      e2 <- mk_single_app fname' allow_fname e2;
      SOME(Let (SOME x) e1 e2)
    od) /\
   (mk_single_app fname allow_fname (Letrec recfuns e) =
    let fname' = if EXISTS ($= fname o SOME) (MAP FST recfuns)
                 then NONE else fname
    in
    do
      recfuns <- mk_single_appr fname' F recfuns;
      e <- mk_single_app fname' allow_fname e;
      SOME(Letrec recfuns e)
    od) /\
   (mk_single_app fname allow_fname (App op es) =
      (case dest_opapp (App op es) of
         SOME(Var(Short f),[arg]) =>
           if SOME f = fname then
             if allow_fname then
               do
                 arg <- mk_single_app fname F arg;
                 SOME(mk_inl arg)
               od
             else NONE
           else
             do
               arg <- mk_single_app fname F arg;
               if allow_fname then
                 SOME(mk_inr(App op [Var(Short f); arg]))
               else
                 SOME(App op [Var(Short f); arg])
             od
       | _ =>
         do
           es <- mk_single_apps fname F es;
           if allow_fname then
             SOME(mk_inr(App op es))
           else
             SOME(App op es)
         od
      )
   ) /\
   (mk_single_apps fname allow_fname (e::es) =
    do
      e <- mk_single_app fname allow_fname e;
      es <- mk_single_apps fname allow_fname es;
      SOME(e::es)
    od) /\
   (mk_single_apps fname allow_fname [] =
    SOME []) /\
   (mk_single_appps fname allow_fname ((p,e)::pes) =
    let fname' = if EXISTS ($= fname o SOME) (pat_bindings p [])
                 then NONE
                 else fname
    in
    do
      e <- mk_single_app fname' allow_fname e;
      pes <- mk_single_appps fname allow_fname pes;
      SOME((p,e)::pes)
    od) /\
   (mk_single_appps fname allow_fname [] =
    SOME []) /\
   (mk_single_appr fname allow_fname ((f,x,e)::recfuns) =
    let fname' = if SOME x = fname then NONE else fname
    in
    do
      e <- mk_single_app fname allow_fname e;
      recfun <- mk_single_appr fname allow_fname recfuns;
      SOME((f,x,e)::recfuns)
    od) /\
   (mk_single_appr fname allow_fname [] =
    SOME [])`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (t,x,e) => exp_size e
                                        | INR (INL (t,x,es)) => exps_size es
                                        | INR (INR (INL (t,x,pes))) => pes_size pes
                                        | INR (INR (INR (t,x,recfuns))) => funs_size recfuns)` >>
   srw_tac [ARITH_ss] [terminationTheory.size_abbrevs, astTheory.exp_size_def] >>
   imp_res_tac dest_opapp_exp_size >>
   fs[terminationTheory.size_abbrevs,astTheory.exp_size_def]);

val mk_single_app_ind = fetch "-" "mk_single_app_ind"

val mk_stepfun_closure_def = Define
  `(mk_stepfun_closure env fname farg fbody =
    do
     gbody <- mk_single_app (SOME fname) T fbody;
     SOME(let benv = build_rec_env [(fname,farg,fbody)] env env.v
          in Closure (env with v := benv) farg gbody)
    od) /\ mk_stepfun_closure _ _ _ _ = NONE`

val mk_tailrec_closure_def = Define
  `(mk_tailrec_closure (Recclosure env [(fname,farg,fbody)] name2) =
    do
     gclosure <- mk_stepfun_closure  env fname farg fbody;
     SOME(Closure (env with <| v :=
            (nsBind fname gclosure env.v) |>) farg
          (App Opapp
               [App Opapp
                  [Letrec ^tailrec_clos (Var(Short "tailrec"));
                   Var(Short fname)];
                Var(Short farg)]
          )
         )
    od) /\ mk_tailrec_closure _ = NONE`

val dest_opapp_eq_nil_IMP = Q.store_thm("dest_opapp_eq_nil_IMP",
  `dest_opapp(exp) = SOME(f,[])
   ==> F`,
  Cases_on `exp` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  rename1 `App op exps` >>
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[] >> strip_tac);

val dest_opapp_eq_single_IMP = Q.store_thm("dest_opapp_eq_single_IMP",
  `dest_opapp(App op exps) = SOME(f,[arg])
   ==> op = Opapp /\ exps = [f;arg]`,
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[] >> strip_tac >>
  rveq >> rename1 `dest_opapp exp` >>
  Cases_on `exp` >> fs[cfNormaliseTheory.dest_opapp_def] >>
  rename1 `App op exps` >>
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[]);

val mk_single_app_F_unchanged_gen = Q.prove(
  `(!fname allow_fname e e'. mk_single_app fname allow_fname e = SOME e'
               /\ allow_fname = F ==> e = e') /\
   (!fname allow_fname es es'. mk_single_apps fname allow_fname es = SOME es'
               /\ allow_fname = F ==> es = es') /\
   (!fname allow_fname pes pes'. mk_single_appps fname allow_fname pes = SOME pes'
                /\ allow_fname = F ==> pes = pes') /\
   (!fname allow_fname recfuns recfuns'. mk_single_appr fname allow_fname recfuns = SOME recfuns'
                /\ allow_fname = F ==> recfuns = recfuns')
  `,
  ho_match_mp_tac mk_single_app_ind >>
  rw[mk_single_app_def] >> fs[] >>
  every_case_tac >> fs[] >> rfs[] >>
  first_x_assum drule >> simp[] >>
  imp_res_tac dest_opapp_eq_single_IMP >>
  fs[]);

val mk_single_app_F_unchanged = save_thm("mk_single_app_F_unchanged",
  SIMP_RULE std_ss [] mk_single_app_F_unchanged_gen);

val mk_inr_res_def = Define `
  (mk_inr_res(Rval vs) =
   Rval(MAP (λv. Conv (SOME (TypeStamp "Inr" 4)) [v]) vs)
  ) /\
  (mk_inr_res res = res)`

val mk_inl_res_def = Define `
  (mk_inl_res(Rval vs) =
   Rval(MAP (λv. Conv (SOME (TypeStamp "Inl" 4)) [v]) vs)
  ) /\
  (mk_inl_res res = res)`

val dest_inr_v_def = Define `
  (dest_inr_v (Conv (SOME (TypeStamp txt n)) [v]) =
   if txt = "Inr" /\ n = 4 then
     SOME v
   else
     NONE) /\
  (dest_inr_v _ = NONE)`

val dest_inl_v_def = Define `
  (dest_inl_v (Conv (SOME (TypeStamp txt n)) [v]) =
   if txt = "Inl" /\ n = 4 then
     SOME v
   else
     NONE) /\
  (dest_inl_v _ = NONE)`

val dest_inr_v_IMP = Q.store_thm("dest_inr_v_IMP",
  `!e1 v. dest_inr_v e1 = SOME v ==> e1 = Conv (SOME (TypeStamp "Inr" 4)) [v]`,
  ho_match_mp_tac (fetch "-" "dest_inr_v_ind") >>
  rw[dest_inr_v_def]);

val dest_inl_v_IMP = Q.store_thm("dest_inl_v_IMP",
  `!e1 v. dest_inl_v e1 = SOME v ==> e1 = Conv (SOME (TypeStamp "Inl" 4)) [v]`,
  ho_match_mp_tac (fetch "-" "dest_inl_v_ind") >>
  rw[dest_inl_v_def]);

val evaluate_inl = Q.store_thm("evaluate_inl",
    `do_con_check env.c (SOME (Short "Inl")) 1 = T /\
    (!v. build_conv env.c (SOME (Short "Inl")) [v] =
           SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
    ==> evaluate st env [mk_inl e] =
        case evaluate st env [e] of
            (st,Rval v) => (st,mk_inl_res(Rval v))
          | (st,rerr) => (st,rerr)`,
    rw[terminationTheory.evaluate_def,mk_inl_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute,mk_inl_res_def] >>
    ntac 2(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]);

val build_conv_check_IMP_nsLookup = Q.prove(
  `!env const v consname stamp n.
  (∀v. build_conv env (SOME const) [v] =
   SOME (Conv (SOME stamp) [v])) /\
  do_con_check env (SOME const) n
  ==> nsLookup env const = SOME(n,stamp)
  `,
  rw[semanticPrimitivesTheory.build_conv_def,semanticPrimitivesTheory.do_con_check_def,
     namespaceTheory.nsLookup_def] >>
  every_case_tac >> fs[]);

val evaluate_IMP_inl = Q.store_thm("evaluate_IMP_inl",
    `do_con_check env.c (SOME (Short "Inl")) 1 = T /\
    (!v. build_conv env.c (SOME (Short "Inl")) [v] =
           SOME(Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
    evaluate st env [e] = (st',res)
    ==> evaluate st env [mk_inl e] = (st',mk_inl_res res)`,
    rw[terminationTheory.evaluate_def,mk_inl_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute] >>
    PURE_TOP_CASE_TAC >> fs[mk_inl_res_def] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]);

val evaluate_inr = Q.store_thm("evaluate_inr",
    `do_con_check env.c (SOME (Short "Inr")) 1 = T /\
    (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    ==> evaluate st env [mk_inr e] =
        case evaluate st env [e] of
            (st,Rval v) => (st,mk_inr_res(Rval v))
          | (st,rerr) => (st,rerr)`,
    rw[terminationTheory.evaluate_def,mk_inr_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute,mk_inr_res_def] >>
    ntac 2(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]);

val st = ``st:'ffi semanticPrimitives$state``

val evaluate_IMP_inr = Q.store_thm("evaluate_IMP_inr",
    `do_con_check env.c (SOME (Short "Inr")) 1 = T /\
    (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
    evaluate ^st env [e] = (st',res)
    ==> evaluate st env [mk_inr e] = (st',mk_inr_res res)`,
    rw[terminationTheory.evaluate_def,mk_inr_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute] >>
    PURE_TOP_CASE_TAC >> fs[mk_inr_res_def] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]);

val mk_single_app_NONE_evaluate = Q.prove(
  `(!^st env es es'. mk_single_apps NONE T es = SOME es'
    /\ do_con_check env.c (SOME (Short "Inr")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    ==> evaluate st env es'
        = case evaluate st env es of
           (st',res) => (st', mk_inr_res res)
   ) /\
   (!^st env v pes err_v pes'. mk_single_appps NONE T pes = SOME pes'
    /\ do_con_check env.c (SOME (Short "Inr")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    ==> evaluate_match st env v pes' err_v
        = case evaluate_match st env v pes err_v of
           (st',res) => (st', mk_inr_res res)
   )
   `,
  ho_match_mp_tac terminationTheory.evaluate_ind >> rpt strip_tac >> PURE_TOP_CASE_TAC
  (* Nil *)
  >- (fs[mk_single_app_def] >> rveq >> fs[terminationTheory.evaluate_def,mk_inr_res_def])
  (* Sequence *)
  >- (fs[Once terminationTheory.evaluate_def,mk_single_app_def] >>
      rveq >> every_case_tac >>
      fs[] >> rveq >> fs[PULL_EXISTS] >>
      rpt(first_x_assum drule) >> rpt(disch_then drule) >> rpt strip_tac >>
      simp[Once terminationTheory.evaluate_def] >>
      fs[mk_inr_res_def] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1])
  (* Lit *)
  >- (fs[mk_single_app_def] >> rveq >> fs[evaluate_IMP_inr])
  (* Raise *)
  >- (fs[mk_single_app_def] >> rveq >> fs[evaluate_IMP_inr] >> fs[terminationTheory.evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[] >> rveq >> fs[mk_inr_res_def])
  (* Handle *)
  >- (fs[mk_single_app_def] >> rveq >> fs[Once terminationTheory.evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[] >> rveq >>
      rfs[evaluate_inr] >> fs[mk_inr_res_def] >>
      rveq >> fs[])
  (* Con *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[evaluate_IMP_inr])
  (* Var*)
  >- (rename1 `Var n` >> Cases_on `n` >>
      fs[mk_single_app_def] >> rveq >>
      fs[evaluate_IMP_inr])
  (* Fun *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[evaluate_IMP_inr])
  (* App *)
  >- (fs[mk_single_app_def] >>
      reverse(Cases_on `op = Opapp`)
      >- (Cases_on `op` >>
          rveq >> fs[cfNormaliseTheory.dest_opapp_def] >>
          rveq >> simp[evaluate_IMP_inr] >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          simp[] >> every_case_tac >> fs[mk_inr_res_def] >>
          rfs[] >>  imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          rfs[] >> fs[evaluate_IMP_inr]
         ) >>
      rveq >>
      Cases_on `es`
      >- (fs[cfNormaliseTheory.dest_opapp_def] >>
          rveq >> simp[evaluate_IMP_inr] >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          simp[] >> every_case_tac >> fs[mk_inr_res_def] >>
          rfs[] >>  imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          rfs[] >> fs[evaluate_IMP_inr]) >>
      rename1 `dest_opapp (App Opapp (exp::exps))` >>
      reverse(Cases_on `exps`)
      >- (fs[cfNormaliseTheory.dest_opapp_def] >>
          simp[] >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
          fs[mk_single_app_def] >> rveq >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          fs[evaluate_IMP_inr] >>
          fs[mk_inr_def] >>
          simp[] >> simp[terminationTheory.evaluate_def] >>
          PURE_TOP_CASE_TAC >> fs[mk_inr_res_def] >>
          rfs[] >>  imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          rfs[] >>
          imp_res_tac dest_opapp_eq_nil_IMP) >>
      fs[cfNormaliseTheory.dest_opapp_def] >>
      rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[evaluate_IMP_inr])
  (* Log *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[evaluate_IMP_inr])
  (* If *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once terminationTheory.evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[semanticPrimitivesTheory.do_if_def] >>
      rw[] >> fs[] >>
      rveq >> fs[mk_inr_res_def])
  (* Mat *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once terminationTheory.evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[])
  (* Let *)
  >- (rename1 `Let xo` >> Cases_on `xo` >>
      fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once terminationTheory.evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[] >> rveq >> fs[mk_inr_res_def])
  (* Letrec *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once terminationTheory.evaluate_def] >>
      rw[] >> fs[] >> rveq >> fs[mk_inr_res_def])
  (* Tannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once terminationTheory.evaluate_def])
  (* Lannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once terminationTheory.evaluate_def])
  (* Pmatch empty row *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[terminationTheory.evaluate_def] >> rveq >>
      fs[mk_inr_res_def])
  (* Pmatch cons *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once terminationTheory.evaluate_def] >> rveq >>
      reverse IF_CASES_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[] >> TOP_CASE_TAC >>
      fs[] >> rveq >> fs[mk_inr_res_def])
  );

val mk_single_app_NONE_evaluate_single = Q.prove(
  `(!^st env e e'. mk_single_app NONE T e = SOME e'
    /\ do_con_check env.c (SOME (Short "Inr")) 1
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    ==> evaluate st env [e']
        = case evaluate st env [e] of
           (st',res) => (st', mk_inr_res res)
   )`,
  rpt strip_tac >>
  match_mp_tac(CONJUNCT1 mk_single_app_NONE_evaluate) >>
  simp[mk_single_app_def]);

val nsLookup_build_rec_env_fresh = Q.prove(
 `!funs env env' fname.
  EVERY (λx. fname ≠ x) (MAP FST funs)
  ==>
  nsLookup(build_rec_env funs env' env.v) (Short fname) =
  nsLookup env.v (Short fname)`,
  `∀(funs:(string # string # exp) list) funs' env env' fname.
   EVERY (λx. fname ≠ x) (MAP FST funs) ⇒
   nsLookup
   (FOLDR (λ(f,x,e) env''. nsBind f (Recclosure env' (funs':(string # string # exp) list) f) env'')
          env.v funs) (Short fname) = nsLookup env.v (Short fname)`
    suffices_by rw[semanticPrimitivesTheory.build_rec_env_def] >>
  Induct >> rw[semanticPrimitivesTheory.build_rec_env_def] >>
  fs[ELIM_UNCURRY]);

val nsLookup_alist_to_ns_fresh = Q.prove(
 `!l fname.
  EVERY (λx. fname ≠ x) (MAP FST l)
  ==>
  nsLookup(alist_to_ns l) (Short fname) = NONE`,
  fs[namespaceTheory.alist_to_ns_def,namespaceTheory.nsLookup_def,ALOOKUP_NONE,EVERY_MEM]);

val partially_evaluates_to_def = Define `
partially_evaluates_to fv env st [] = T /\
partially_evaluates_to fv env st ((e1,e2)::r) =
  case evaluate st env [e1] of
    (st',Rval v1) =>
      (?v. dest_inr_v(HD v1) = SOME v /\ evaluate st env [e2] = (st',Rval [v]) /\
           partially_evaluates_to fv env st' r)
      \/
      (?v st'' res. dest_inl_v(HD v1) = SOME v /\ evaluate st env [e2] = (st'',res) /\
          case do_opapp [fv;v] of
            SOME(env',e3) =>
               if st'.clock = 0 then st'' = st' /\ res = Rerr(Rabort(Rtimeout_error))
               else
                 evaluate (dec_clock st') env' [e3] = (st'',res) /\
                 (case res of Rval _ =>
                    partially_evaluates_to fv env st'' r
                  | _ => T)
          | NONE => res = Rerr (Rabort Rtype_error))
   | (st',rerr) => evaluate st env [e2] = (st',rerr)
`

val partially_evaluates_to_match_def = Define `
partially_evaluates_to_match fv mv err_v env st (pr1,pr2) =
  case evaluate_match st env mv pr1 err_v of
    (st',Rval v1) =>
      (?v. dest_inr_v(HD v1) = SOME v /\ evaluate_match st env mv pr2 err_v = (st',Rval [v]))
      \/
      (?v st'' res. dest_inl_v(HD v1) = SOME v /\ evaluate_match st env mv pr2 err_v = (st'',res) /\
          case do_opapp [fv;v] of
              SOME(env',e3) =>
                if st'.clock = 0 then (st'' = st' /\ res = Rerr(Rabort(Rtimeout_error)))
                else
                   evaluate (dec_clock st') env' [e3] = (st'',res)
            | NONE => res = Rerr (Rabort Rtype_error))
   | (st',rerr) => evaluate_match st env mv pr2 err_v = (st',rerr)
`

val mk_single_app_evaluate = Q.prove(
  `(!^st env es es' fname fv. mk_single_apps (SOME fname) T es = SOME es'
    /\ do_con_check env.c (SOME (Short "Inr")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    /\ do_con_check env.c (SOME (Short "Inl")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inl")) [v] =
           SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to fv env st (ZIP(es',es))
   ) /\
   (!^st env v pes err_v pes' fname fv. mk_single_appps (SOME fname) T pes = SOME pes'
    /\ do_con_check env.c (SOME (Short "Inr")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    /\ do_con_check env.c (SOME (Short "Inl")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inl")) [v] =
           SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to_match fv v err_v env st (pes',pes)
   )
   `,
  ho_match_mp_tac terminationTheory.evaluate_ind >> rpt strip_tac
  (* Nil *)
  >- (fs[mk_single_app_def] >> rveq >> fs[partially_evaluates_to_def])
  (* Sequence *)
  >- (fs[mk_single_app_def] >>
      rveq >> fs[partially_evaluates_to_def,ZIP] >>
      TOP_CASE_TAC >> TOP_CASE_TAC >>
      fs[PULL_EXISTS] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      rfs[partially_evaluates_to_def]
      >- (first_x_assum drule >> rpt(disch_then drule) >> fs[]) >>
      disj2_tac >>
      ntac 4 (TOP_CASE_TAC >> fs[]) >> metis_tac[])
  (* Lit *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def,evaluate_inr] >>
      fs[terminationTheory.evaluate_def,mk_inr_res_def,dest_inr_v_def])
  (* Raise *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def,terminationTheory.evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[])
  (* Handle *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once terminationTheory.evaluate_def] >>
      fs[evaluate_inr] >>
      every_case_tac >> fs[PULL_EXISTS] >> rveq >>
      fs[mk_inr_res_def] >> rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      fs[dest_inr_v_def] >>
      fs[terminationTheory.evaluate_def] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      rfs[partially_evaluates_to_match_def] >>
      every_case_tac >> fs[])
  (* Con *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[partially_evaluates_to_def] >>
      fs[evaluate_inr] >>
      every_case_tac >> fs[] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      fs[mk_inr_res_def] >> rveq >> fs[dest_inr_v_def])
  (* Var*)
  >- (rename1 `Var n` >> Cases_on `n` >>
      fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def] >>
      fs[evaluate_inr] >>
      every_case_tac >> fs[] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      fs[mk_inr_res_def] >> rveq >> fs[dest_inr_v_def])
  (* Fun *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def,evaluate_inr] >>
      simp[terminationTheory.evaluate_def,mk_inr_res_def,dest_inr_v_def])
  (* App *)
  >- (fs[mk_single_app_def] >>
      reverse(Cases_on `op = Opapp`)
      >- (Cases_on `op` >>
          rveq >> fs[cfNormaliseTheory.dest_opapp_def] >>
          rveq >> simp[evaluate_inr,partially_evaluates_to_def] >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          simp[] >> every_case_tac >> fs[mk_inr_res_def] >>
          rfs[] >>  imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          rfs[] >> fs[dest_inr_v_def]) >>
      rveq >>
      Cases_on `es`
      >- (fs[cfNormaliseTheory.dest_opapp_def] >>
          rveq >> simp[partially_evaluates_to_def,evaluate_inr] >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          simp[] >> every_case_tac >> fs[mk_inr_res_def] >>
          rfs[] >>  imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          rfs[] >> fs[dest_inr_v_def]) >>
      rename1 `dest_opapp (App Opapp (exp::exps))` >>
      reverse(Cases_on `exps`)
      >- (fs[cfNormaliseTheory.dest_opapp_def] >>
          simp[] >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
          fs[mk_single_app_def] >> rveq >>
          imp_res_tac mk_single_app_F_unchanged >> rveq >>
          TRY(qmatch_goalsub_abbrev_tac `Letrec l e` >>
              Cases_on `EXISTS ($= (SOME fname) ∘ SOME) (MAP FST l)` >>
              FULL_SIMP_TAC std_ss [] >>
              imp_res_tac mk_single_app_F_unchanged >> rveq >>
              fs[partially_evaluates_to_def,evaluate_inr,evaluate_inl] >>
              rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
              imp_res_tac evaluatePropsTheory.evaluate_length >>
              fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
              fs[mk_inr_res_def] >> rveq >> fs[dest_inr_v_def]) >>
          TRY(qmatch_goalsub_abbrev_tac `mk_inr` >>
              fs[partially_evaluates_to_def,evaluate_inr,evaluate_inl] >>
              rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
              imp_res_tac evaluatePropsTheory.evaluate_length >>
              fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
              fs[mk_inr_res_def] >> rveq >> fs[dest_inr_v_def] >>
              imp_res_tac dest_opapp_eq_nil_IMP) >>
          imp_res_tac dest_opapp_eq_nil_IMP  >>
          fs[partially_evaluates_to_def,evaluate_inl] >>
          fs[terminationTheory.evaluate_def] >>
          rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
          imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          fs[mk_inl_res_def] >> rveq >>
          fs[dest_inl_v_def,dest_inr_v_def] >>
          qmatch_goalsub_abbrev_tac `a1 = _` >>
          MAP_EVERY qexists_tac [`FST a1`,`SND a1`] >>
          simp[] >> PURE_TOP_CASE_TAC >> simp[]) >>
      fs[cfNormaliseTheory.dest_opapp_def] >>
      rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def,evaluate_inr] >>
      simp[terminationTheory.evaluate_def] >>
      every_case_tac >> fs[mk_inr_res_def] >>
      rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
      fs[dest_inr_v_def])
  (* Log *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def,evaluate_inr] >>
      every_case_tac >> fs[mk_inr_res_def] >> rfs[] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
      rfs[dest_inr_v_def])
  (* If *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def] >>
      fs[terminationTheory.evaluate_def,semanticPrimitivesTheory.do_if_def] >>
      Cases_on `evaluate st env [e1]` >> rename1 `(_,result)` >>
      reverse(Cases_on `result`) >- fs[] >>
      rw[] >> fs[] >> rfs[] >>
      rfs[partially_evaluates_to_def,PULL_EXISTS] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac))
  (* Mat *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def] >>
      Cases_on `evaluate st env [e]` >> rename1 `(_,result)` >>
      reverse(Cases_on `result`) >- fs[terminationTheory.evaluate_def] >>
      fs[terminationTheory.evaluate_def,partially_evaluates_to_match_def,PULL_EXISTS] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      rpt(TOP_CASE_TAC >> fs[] >> rveq))
  (* Let *)
  >- (rename1 `Let xo` >> Cases_on `xo` >>
      fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[partially_evaluates_to_def,PULL_EXISTS] >>
      fs[terminationTheory.evaluate_def,namespaceTheory.nsOptBind_def] >>
      Cases_on `evaluate st env [e1]` >> rename1 `(_,result)` >>
      reverse(Cases_on `result`) >- fs[terminationTheory.evaluate_def] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      fs[] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      Cases_on `x = fname` >> fs[] >> rveq >> fs[ml_progTheory.nsLookup_nsBind_compute] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      fs[] >>
      drule mk_single_app_NONE_evaluate_single >>
      qmatch_goalsub_abbrev_tac `evaluate a1 a2` >>
      disch_then(qspecl_then [`a1`,`a2`] mp_tac) >>
      unabbrev_all_tac >>
      simp[] >> disch_then kall_tac >>
      every_case_tac >> fs[mk_inr_res_def] >>
      rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >> fs[dest_inr_v_def])
  (* Letrec *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      PURE_FULL_CASE_TAC >> FULL_SIMP_TAC std_ss [] >>
      fs[partially_evaluates_to_def,terminationTheory.evaluate_def] >>
      rw[] >> fs[PULL_EXISTS] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      rfs[o_DEF,nsLookup_build_rec_env_fresh,partially_evaluates_to_def] >>
      drule mk_single_app_NONE_evaluate_single >>
      qmatch_goalsub_abbrev_tac `evaluate a1 a2` >>
      disch_then(qspecl_then [`a1`,`a2`] mp_tac) >>
      unabbrev_all_tac >>
      simp[] >> disch_then kall_tac >>
      every_case_tac >> fs[mk_inr_res_def] >>
      rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >> fs[dest_inr_v_def])
  (* Tannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[PULL_EXISTS] >> first_x_assum drule >>
      rpt(disch_then drule) >>
      simp[partially_evaluates_to_def,terminationTheory.evaluate_def])
  (* Lannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[PULL_EXISTS] >> first_x_assum drule >>
      rpt(disch_then drule) >>
      simp[partially_evaluates_to_def,terminationTheory.evaluate_def])
  (* Pmatch empty row *)
  >- (fs[mk_single_app_def] >> rveq >>
      simp[partially_evaluates_to_match_def,terminationTheory.evaluate_def])
  (* Pmatch cons *)
  >- (fs[mk_single_app_def] >> rveq >>
      PURE_FULL_CASE_TAC >> FULL_SIMP_TAC std_ss [] >>
      fs[partially_evaluates_to_match_def,terminationTheory.evaluate_def] >>
      rw[] >>
      fs[PULL_EXISTS] >>
      Cases_on `pmatch env.c st.refs p v []` >> fs[] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> strip_tac) >>
      rfs[o_DEF,partially_evaluates_to_def] >>
      fs[ml_progTheory.nsLookup_nsAppend_Short] >>
      imp_res_tac semanticPrimitivesPropsTheory.pmatch_extend >> rveq >>
      rfs[] >>
      qpat_x_assum `MAP _ _ = pat_bindings _ _` (assume_tac o GSYM) >>
      fs[] >> rfs[nsLookup_alist_to_ns_fresh] >>
      TRY(qmatch_asmsub_abbrev_tac `mk_single_app (SOME _) T e = SOME ea`
          >> every_case_tac >> fs[] >> every_case_tac >> fs[]) >>
      drule mk_single_app_NONE_evaluate_single >>
      qmatch_goalsub_abbrev_tac `evaluate a1 a2` >>
      disch_then(qspecl_then [`a1`,`a2`] mp_tac) >>
      unabbrev_all_tac >>
      simp[] >> disch_then kall_tac >>
      every_case_tac >> fs[mk_inr_res_def] >>
      rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      qmatch_asmsub_abbrev_tac `evaluate _ _ _ = (_,result)` >>
      Cases_on `result` >> fs[mk_inr_res_def] >> rveq >> fs[dest_inr_v_def] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >> fs[dest_inr_v_def])
    );

val mk_single_app_evaluate_single = Q.store_thm("mk_single_app_evaluate_single",
  `!^st env e e' fname fv. mk_single_app (SOME fname) T e = SOME e'
    /\ do_con_check env.c (SOME (Short "Inr")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
    /\ do_con_check env.c (SOME (Short "Inl")) 1 = T
    /\ (!v. build_conv env.c (SOME (Short "Inl")) [v] =
           SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to fv env st [(e',e)]`,
  rpt strip_tac >>
  `mk_single_apps (SOME fname) T [e] = SOME [e']` by simp[mk_single_app_def] >>
  drule(CONJUNCT1 mk_single_app_evaluate) >>
  rpt(disch_then drule) >> simp[]);

val evaluate_tailrec_ind_lemma = Q.prove(
  `!ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short "Inr")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inr")) [v] =
        SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
   do_con_check env.c (SOME (Short "Inl")) 1 /\
   res <> Rerr(Rabort(Rtimeout_error)) /\
   (∀v.
        build_conv env.c (SOME (Short "Inl")) [v] =
        SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
   fname <> farg /\
   evaluate_ck ck ^st
     (env with
      v :=
        nsBind "x" v
          (nsBind "f"
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^tailrec_clos
                (env with
                 v :=
                   nsBind farg x
                     (nsBind fname
                        (Closure
                           (env with
                            v :=
                              nsBind fname
                                (Recclosure env [(fname,farg,fbody)] fname)
                                env.v) farg gbody) env.v))
                env')))
     [^tailrec_body] = (st',res) ==>
   ∃ck'.
       evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st' with clock := ck',res)`,
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  rw[] >> pop_assum mp_tac >>
  simp[Once terminationTheory.evaluate_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  rw[] >> pop_assum mp_tac >>
  drule mk_single_app_evaluate_single >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  disch_then(qspecl_then [`ast`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[ml_progTheory.nsLookup_nsBind_compute] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,partially_evaluates_to_def] >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  Cases_on `evaluate ast aenv [gbody]` >>
  rename1 `(_,result)` >>
  reverse(Cases_on `result`) >-
    ((* Rerror *)
     fs[] >> rpt strip_tac >>
     qexists_tac `st'.clock + 1` >>
     simp[Abbr`ast`] >>
     drule evaluatePropsTheory.evaluate_add_to_clock >>
     rveq >> simp[] >> disch_then(qspec_then `1` mp_tac) >>
     simp[]) >>
  simp[] >>
  strip_tac >-
    ((* Rval([Inr v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >>
      imp_res_tac dest_inr_v_IMP >>
      fs[] >> rveq >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      rpt strip_tac >>
      rveq >>
      qexists_tac `q.clock + 1` >>
      simp[Abbr `ast`] >>
      drule evaluatePropsTheory.evaluate_add_to_clock >>
      rveq >> simp[] >> disch_then(qspec_then `1` mp_tac) >>
      simp[]
    ) >-
    ((* Rval([Inl v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >>
      imp_res_tac dest_inl_v_IMP >>
      fs[] >> rveq >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[terminationTheory.evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      rw[] >> pop_assum mp_tac >>
      simp[evaluateTheory.dec_clock_def] >>
      rw[] >> pop_assum mp_tac >>
      fs[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac
        `evaluate
           (ast with clock := _)
           (aenv with
             v := nsBind _ argv
                   (nsBind _ funv (build_rec_env _ (_ with v := nsBind _ argx _) aenv'))
           )` >>
      strip_tac >>
      first_x_assum(qspec_then `ast.clock - 2` mp_tac) >>
      impl_tac >-
        (unabbrev_all_tac >>
         imp_res_tac terminationTheory.evaluate_clock >>
         fs[]) >>
      rpt(disch_then drule) >>
      unabbrev_all_tac >>
      disch_then drule >>
      strip_tac >>
      drule evaluatePropsTheory.evaluate_add_to_clock >>
      simp[] >>
      disch_then(qspec_then `1` assume_tac) >>
      fs[evaluateTheory.dec_clock_def] >>
      rveq >>
      rpt(dxrule evaluatePropsTheory.evaluate_add_to_clock >>
        simp[] >>
        disch_then(qspec_then `1` mp_tac) >>
        fs[] >>
        rveq) >>
      rpt strip_tac >>
      fs[semanticPrimitivesTheory.state_component_equality])
  );

val evaluate_tailrec_lemma = Q.prove(
 `!ck fbody gbody env ^st farg x fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short "Inr")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inr")) [v] =
        SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
   do_con_check env.c (SOME (Short "Inl")) 1 /\
   res <> Rerr(Rabort(Rtimeout_error)) /\
   (∀v.
        build_conv env.c (SOME (Short "Inl")) [v] =
        SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
   fname <> farg /\
   evaluate_ck ck ^st
      (env with
            v :=
              nsBind farg x
                (nsBind fname
                   (Closure
                      (env with
                       v := build_rec_env [(fname,farg,fbody)] env env.v)
                      farg gbody) env.v))
    [App Opapp
        [App Opapp
           [Letrec ^tailrec_clos (Var(Short "tailrec"));
            Var(Short fname)]; Var (Short farg)]] = (st',res) ==>
    ∃ck'.evaluate_ck ck ^st
         (env with
          v := nsBind farg x (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st' with clock := ck',res)`,
  rpt strip_tac >>
  fs[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  rw[] >> pop_assum mp_tac >>
  simp[Once terminationTheory.evaluate_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  rw[] >> pop_assum mp_tac >>
  strip_tac >>
  drule evaluate_tailrec_ind_lemma >>
  rpt(disch_then drule) >>
  simp[evaluate_ck_def,semanticPrimitivesTheory.build_rec_env_def] >>
  disch_then drule >>
  strip_tac >>
  drule evaluatePropsTheory.evaluate_add_to_clock >>
  simp[] >>
  disch_then(qspec_then `2` mp_tac) >>
  simp[semanticPrimitivesTheory.state_component_equality]);

val mk_single_app_unroll_lemma = Q.prove(
  `!fname fbody gbody ^st st' ck1 env farg ck2 x v.
    mk_single_app (SOME fname) T fbody = SOME gbody /\
    evaluate (^st with clock := ck1)
               (env with
                v :=
                  nsBind farg x
                    (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                       env.v)) [gbody] =
             (st' with clock := 0,mk_inl_res(Rval [v])) /\
    do_con_check env.c (SOME (Short "Inr")) 1 /\
    (∀v.
      build_conv env.c (SOME (Short "Inr")) [v] =
     SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
    do_con_check env.c (SOME (Short "Inl")) 1 /\
    (∀v.
      build_conv env.c (SOME (Short "Inl")) [v] =
     SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
    fname ≠ farg
    ==>
    evaluate (^st with clock := ck1 + ck2 + 1)
             (env with
                  v :=
              nsBind farg x
                     (nsBind fname (Recclosure env [(fname,farg,fbody)] fname) env.v))
             [fbody] =
   evaluate (st' with clock := ck2)
            (env with
                 v :=
             nsBind farg v
                    (nsBind fname (Recclosure env [(fname,farg,fbody)] fname) env.v))
            [fbody]`,
  rpt strip_tac >>
  drule mk_single_app_evaluate_single >>
  disch_then(qspecl_then [`st with clock := ck1 + ck2 + 1`,
    `env with v := nsBind farg x
              (nsBind fname (Recclosure env [(fname,farg,fbody)] fname) env.v)`] mp_tac) >>
  simp[partially_evaluates_to_def] >>
  drule evaluatePropsTheory.evaluate_add_to_clock >>
  simp[mk_inl_res_def] >>
  disch_then(qspec_then `ck2 + 1` mp_tac) >>
  simp[dest_inr_v_def,dest_inl_v_def,evaluateTheory.dec_clock_def,do_opapp_def,
       Once find_recfun_def] >>
  rpt strip_tac >>
  simp[] >> fs[build_rec_env_def]);

val evaluate_tailrec_diverge_lemma = Q.prove(
  `!ck fbody gbody env env' ^st farg x v fname.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short "Inr")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inr")) [v] =
        SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
   do_con_check env.c (SOME (Short "Inl")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inl")) [v] =
        SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
   fname <> farg /\
   (!ck. ?st'. evaluate_ck ck ^st
     (env with
      v :=
        nsBind "x" v
          (nsBind "f"
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^tailrec_clos
                (env with
                 v :=
                   nsBind farg x
                     (nsBind fname
                        (Closure
                           (env with
                            v :=
                              nsBind fname
                                (Recclosure env [(fname,farg,fbody)] fname)
                                env.v) farg gbody) env.v))
                env')))
     [^tailrec_body] = (st',Rerr(Rabort(Rtimeout_error)))) ==>
   ?st'.
       evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort(Rtimeout_error)))`,
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[GSYM LEFT_EXISTS_IMP_THM] >>
  Q.REFINE_EXISTS_TAC `SUC ck'` >>
  simp[evaluateTheory.dec_clock_def] >>
  reverse(Cases_on `?ck'.
    SND(evaluate (st with clock := ck')
                 (env with
                  v :=
                    nsBind farg v
                      (nsBind fname
                         (Recclosure env [(fname,farg,fbody)] fname) env.v))
                 [gbody]) <> Rerr(Rabort(Rtimeout_error))`) >-
    (fs[] >>
     first_x_assum(qspec_then `ck` assume_tac) >>
     Cases_on `evaluate (st with clock := ck)
              (env with
               v :=
                 nsBind farg v
                   (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                      env.v)) [gbody]` >>
     fs[] >> rveq >>
     drule mk_single_app_evaluate_single >>
     disch_then(qspecl_then [`st with clock := ck`,`env with v :=
              nsBind farg v
                (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                   env.v)`] mp_tac) >>
     simp[partially_evaluates_to_def]) >-
    (fs[] >>
     Cases_on `evaluate (st with clock := ck')
              (env with
               v :=
                 nsBind farg v
                   (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                      env.v)) [gbody]` >>
     fs[] >>
     drule evaluatePropsTheory.evaluate_set_clock >>
     simp[] >> disch_then(qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >>
     drule evaluatePropsTheory.evaluate_add_to_clock >>
     simp[] >> strip_tac >>
     Q.REFINE_EXISTS_TAC `ck1 + extra` >>
     simp[] >> first_x_assum kall_tac >>
     PURE_TOP_CASE_TAC >> fs[] >> rveq >>
     fs[LEFT_EXISTS_IMP_THM] >>
     drule mk_single_app_evaluate_single >>
     disch_then(qspecl_then [`st with clock := ck1`,`env with v :=
              nsBind farg v
                (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                   env.v)`] mp_tac) >>
     simp[partially_evaluates_to_def] >>
     strip_tac >-
       ((* Inr *)
        imp_res_tac evaluatePropsTheory.evaluate_length >>
        fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
        rveq >> fs[] >>
        imp_res_tac dest_inr_v_IMP >> rveq >>
        imp_res_tac build_conv_check_IMP_nsLookup >>
        simp[terminationTheory.evaluate_def,namespaceTheory.nsOptBind_def,
             astTheory.pat_bindings_def,terminationTheory.pmatch_def,
             semanticPrimitivesTheory.same_type_def,
             semanticPrimitivesTheory.same_ctor_def]) >-
       ((* Inl *)
        fs[semanticPrimitivesTheory.do_opapp_def,
           semanticPrimitivesTheory.find_recfun_def] >>
        rveq >>
        reverse(Cases_on `ck1 < ck`) >-
          (disch_then kall_tac >>
           spose_not_then strip_assume_tac >>
           fs[NOT_LESS,LESS_EQ_EXISTS] >>
           rename1 `ck1 = ck + ck2` >>
           Cases_on `evaluate (st with clock := ck)
               (env with
                v :=
                  nsBind farg v
                    (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                       env.v)) [fbody]` >>
           drule evaluatePropsTheory.evaluate_add_to_clock >>
           disch_then(qspec_then `ck2` mp_tac) >>
           impl_tac >- fs[CLOSED_PAIR_EQ] >>
           fs[]) >>
        imp_res_tac dest_inl_v_IMP >>
        imp_res_tac evaluatePropsTheory.evaluate_length >>
        fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
        rveq >> fs[] >> rveq >>
        ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
        simp[namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute] >>
        simp[Once terminationTheory.evaluate_def] >>
        imp_res_tac build_conv_check_IMP_nsLookup >>
        simp[astTheory.pat_bindings_def,terminationTheory.pmatch_def,
             semanticPrimitivesTheory.same_type_def,
             semanticPrimitivesTheory.same_ctor_def] >>
        ntac 7 (simp[Once terminationTheory.evaluate_def]) >>
        simp[do_opapp_def,Once find_recfun_def] >>
        simp[GSYM LEFT_EXISTS_IMP_THM] >>
        Q.REFINE_EXISTS_TAC `extra + 2` >>
        simp[LEFT_EXISTS_IMP_THM] >>
        simp[evaluateTheory.dec_clock_def] >>
        simp[Once terminationTheory.evaluate_def] >>
        fs[do_opapp_def] >>
        qmatch_goalsub_abbrev_tac
          `evaluate
            (ast with clock := _)
            (aenv with
              v := nsBind _ argv
                    (nsBind _ funv (build_rec_env _ (_ with v := nsBind _ argx _) aenv'))
            )` >>
        fs[LESS_EQ,LESS_EQ_EXISTS] >>
        rename1 `ck = ck2 + SUC ck1` >>
        fs[ADD1] >>
        drule mk_single_app_unroll_lemma >>
        simp[mk_inl_res_def] >>
        disch_then drule >>
        simp[] >>
        disch_then kall_tac >>
        strip_tac >>
        last_x_assum(qspec_then `ck2` mp_tac) >>
        impl_tac >- metis_tac[ADD_SYM,ADD_ASSOC] >>
        disch_then drule >>
        disch_then(qspecl_then [`aenv`,`aenv'`,`ast`,`farg`,`argx`,`argv`] mp_tac) >>
        simp[] >> simp[build_rec_env_def])
    )
  );

val evaluate_tailrec_div_ind_lemma = Q.prove(
  `!ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short "Inr")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inr")) [v] =
        SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
   do_con_check env.c (SOME (Short "Inl")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inl")) [v] =
        SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
   fname <> farg /\
   ck > 0 /\
   evaluate_ck ck ^st
     (env with
      v :=
        nsBind "x" v
          (nsBind "f"
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^tailrec_clos
                (env with
                 v :=
                   nsBind farg x
                     (nsBind fname
                        (Closure
                           (env with
                            v :=
                              nsBind fname
                                (Recclosure env [(fname,farg,fbody)] fname)
                                env.v) farg gbody) env.v))
                env')))
     [^tailrec_body] = (st',Rerr(Rabort(Rtimeout_error))) ==>
   ∃ck'.
       evaluate_ck ck' ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort(Rtimeout_error)))`,
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  drule mk_single_app_evaluate_single >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  disch_then(qspecl_then [`ast`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[ml_progTheory.nsLookup_nsBind_compute] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,partially_evaluates_to_def] >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  Cases_on `evaluate ast aenv [gbody]` >>
  rename1 `(_,result)` >>
  reverse(Cases_on `result`) >-
    ((* Rerror *)
     fs[] >> rpt strip_tac >> rveq >>
     qexists_tac `ast.clock` >>
     simp[Abbr`ast`]) >>
  simp[] >>
  strip_tac >-
    ((* Rval([Inr v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >>
      imp_res_tac dest_inr_v_IMP >>
      fs[] >> rveq >>
      ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[Once terminationTheory.evaluate_def]
    ) >-
    ((* Rval([Inl v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >>
      imp_res_tac dest_inl_v_IMP >>
      fs[] >> rveq >>
      ntac 2(simp[Once terminationTheory.evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[terminationTheory.evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      IF_CASES_TAC >-
        (strip_tac >> fs[Abbr `ast`,do_opapp_def,Once find_recfun_def] >>
         asm_exists_tac >> simp[]) >>
      simp[Once terminationTheory.evaluate_def] >>
      qpat_x_assum `evaluate _ _ [gbody] = _` assume_tac >>
      drule evaluatePropsTheory.evaluate_set_clock >>
      simp[] >>
      disch_then(qspec_then `0` strip_assume_tac) >>
      drule mk_single_app_evaluate_single >>
      disch_then(qspecl_then [`ast with clock := ck1`,`aenv`] mp_tac) >>
      unabbrev_all_tac >> simp[] >>
      simp[semanticPrimitivesTheory.build_rec_env_def,partially_evaluates_to_def] >>
      fs[dest_inr_v_def] >>
      simp[do_opapp_def,Once find_recfun_def] >> strip_tac >>
      IF_CASES_TAC >-
        (fs[evaluateTheory.dec_clock_def] >>
         strip_tac >> rveq >>
         qexists_tac `ck1` >>
         simp[semanticPrimitivesTheory.state_component_equality]) >>
      simp[evaluateTheory.dec_clock_def] >>
      qmatch_goalsub_abbrev_tac `_ with clock := ack` >>
      Cases_on `ack = 0` >-
        (rveq >> simp[terminationTheory.evaluate_def,do_opapp_def] >>
         strip_tac >> rveq >> qexists_tac `ck1` >>
         simp[semanticPrimitivesTheory.state_component_equality]) >>
      `ack < ck`
        by(imp_res_tac terminationTheory.evaluate_clock >> fs[Abbr `ack`]) >>
      strip_tac >>
      drule mk_single_app_unroll_lemma >> simp[mk_inl_res_def] >>
      disch_then drule >>
      simp[] >>
      strip_tac >>
      Q.REFINE_EXISTS_TAC `ck1 + (more_clock + 1)` >>
      simp[] >> pop_assum kall_tac >>
      first_x_assum drule >>
      disch_then drule >>
      simp[build_rec_env_def] >>
      disch_then match_mp_tac >>
      simp[] >>
      asm_exists_tac >> first_x_assum ACCEPT_TAC)
  );

val evaluate_tailrec_div_ind_lemma2 = Q.prove(
  `!ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short "Inr")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inr")) [v] =
        SOME (Conv (SOME (TypeStamp "Inr" 4)) [v])) /\
   do_con_check env.c (SOME (Short "Inl")) 1 /\
   (∀v.
        build_conv env.c (SOME (Short "Inl")) [v] =
        SOME (Conv (SOME (TypeStamp "Inl" 4)) [v])) /\
   fname <> farg /\
   evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort(Rtimeout_error))) ==>
   ?ck. evaluate_ck ck ^st
     (env with
      v :=
        nsBind "x" v
          (nsBind "f"
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^tailrec_clos
                (env with
                 v :=
                   nsBind farg x
                     (nsBind fname
                        (Closure
                           (env with
                            v :=
                              nsBind fname
                                (Recclosure env [(fname,farg,fbody)] fname)
                                env.v) farg gbody) env.v))
                env')))
     [^tailrec_body] = (st',Rerr(Rabort(Rtimeout_error)))`,
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  Q.REFINE_EXISTS_TAC `ck' + 1` >>
  ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  pop_assum mp_tac >>
  drule mk_single_app_evaluate_single >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  disch_then(qspecl_then [`ast`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[ml_progTheory.nsLookup_nsBind_compute] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,partially_evaluates_to_def] >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  Cases_on `evaluate ast aenv [gbody]` >>
  rename1 `(_,result)` >>
  reverse(Cases_on `result`) >-
    ((* Rerror *)
     fs[] >> rpt strip_tac >> rveq >>
     qexists_tac `ast.clock` >>
     simp[Abbr`ast`]) >>
  simp[] >>
  strip_tac >-
    ((* Rval([Inr v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1]) >-
    ((* Rval([Inl v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >> strip_tac >>
      rveq >>
      imp_res_tac dest_inl_v_IMP >>
      fs[] >> rveq >>
      qpat_x_assum `evaluate _ _ [gbody] = _` assume_tac >>
      drule evaluatePropsTheory.evaluate_set_clock >>
      disch_then(qspec_then `0` mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      Q.REFINE_EXISTS_TAC `ck1 + extra` >>
      qunabbrev_tac `ast` >>
      drule evaluatePropsTheory.evaluate_add_to_clock >>
      simp[] >> disch_then kall_tac >>
      ntac 2(simp[Once terminationTheory.evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      fs[do_opapp_def,Once find_recfun_def] >>
      qhdtm_x_assum `COND` mp_tac >>
      IF_CASES_TAC >-
        (strip_tac >> rveq >> qexists_tac `0` >>
         simp[terminationTheory.evaluate_def,do_opapp_def,Once find_recfun_def,
              semanticPrimitivesTheory.state_component_equality]) >>
      strip_tac >>
      Q.REFINE_EXISTS_TAC `extra + 2` >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[terminationTheory.pmatch_def] >>
      simp[terminationTheory.evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[evaluateTheory.dec_clock_def] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      fs[evaluateTheory.dec_clock_def] >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac terminationTheory.evaluate_clock >> fs[])
  );

val lprefix_mono_lprefix = Q.prove(
 `!f i k.
 (!i. LPREFIX (f i) (f(i + 1)))
 ==> LPREFIX (f i) (f(i + (k:num)))
 `,
 rw[] >> Induct_on `k` >> fs[] >>
 first_x_assum(qspec_then `i + k` assume_tac) >>
 fs[ADD1] >>
 metis_tac[LPREFIX_TRANS]);

val gify = Q.prove(
 `!g n.
 (!i. g i < g (i +1))
 ==> ?k (i:num). g i = (n:num) + k
 `,
 rpt strip_tac >>
 `n <= g n`
   by(Induct_on `n` >> simp[] >>
      qpat_x_assum `!i. _ < _` (qspec_then `n` mp_tac) >>
      simp[] >> strip_tac >>
      fs[LESS_EQ,LESS_EQ_EXISTS,ADD1] >>
      metis_tac[ADD_ASSOC]) >>
 fs[LESS_EQ_EXISTS] >>
 metis_tac[ADD_SYM]);

val lprefix_lub_skip = Q.store_thm("lprefix_lub_skip",
 `(!i. LPREFIX (f i) (f(i + 1))) /\
  (!i. g i < g(i+1)) /\
  lprefix_lub (IMAGE (\i. f (g i)) 𝕌(:num)) l
  ==>
  lprefix_lub (IMAGE (\i. f i) 𝕌(:num)) l
 `,
 rw[lprefix_lubTheory.lprefix_lub_def]
 >- (drule gify >>
     disch_then(qspec_then `i` strip_assume_tac) >>
     drule lprefix_mono_lprefix >>
     disch_then(qspecl_then [`i`,`k`] assume_tac) >>
     match_mp_tac(GEN_ALL LPREFIX_TRANS) >> asm_exists_tac >> simp[] >>
     metis_tac[]) >>
 last_x_assum match_mp_tac >>
 rpt strip_tac >>
 first_x_assum match_mp_tac >> metis_tac[]);

val lprefix_lub_unskip = Q.store_thm("lprefix_lub_unskip",
 `(!i. LPREFIX (f i) (f(i + 1))) /\
  (!i. g i < g(i+1)) /\
  lprefix_lub (IMAGE (\i. f i) 𝕌(:num)) l
  ==>
  lprefix_lub (IMAGE (\i. f (g i)) 𝕌(:num)) l
 `,
 rw[lprefix_lubTheory.lprefix_lub_def] >- metis_tac[] >>
 last_x_assum match_mp_tac >> rpt strip_tac >> rveq >>
 drule gify >>
 disch_then(qspec_then `i` strip_assume_tac) >>
 drule lprefix_mono_lprefix >>
 disch_then(qspecl_then [`i`,`k`] assume_tac) >>
 match_mp_tac(GEN_ALL LPREFIX_TRANS) >> asm_exists_tac >> simp[] >>
 metis_tac[]);

val mk_tailrec_closure_sound_basic = Q.store_thm("mk_tailrec_closure_sound_basic",
  `!fv env . mk_tailrec_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
   /\ do_con_check env.c (SOME (Short "Inr")) 1
   /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
   /\ do_con_check env.c (SOME (Short "Inl")) 1
   /\ (!v. build_conv env.c (SOME (Short "Inl")) [v] =
          SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
   /\ fname <> farg
   /\ app_basic (p:'ffi ffi_proj) fv x H Q
   ==> app_basic p (Recclosure env [(fname,farg,fbody)] fname) x H Q`,
  rw[mk_tailrec_closure_def,mk_stepfun_closure_def,app_basic_def] >>
  first_x_assum drule >>
  disch_then drule >>
  strip_tac >>
  asm_exists_tac >> fs[semanticPrimitivesTheory.do_opapp_def] >>
  simp[semanticPrimitivesTheory.find_recfun_def] >>
  asm_exists_tac >>
  simp[] >> rveq >> Cases_on `r` >>
  fs[evaluate_to_heap_def] >>
  TRY(
    rename1 `lprefix_lub` >>
    conj_asm1_tac >-
      (strip_tac >>
       qpat_x_assum `!ck. ?st. _` mp_tac >>
       simp[GSYM LEFT_EXISTS_IMP_THM] >>
       Q.REFINE_EXISTS_TAC `ck1 + 2` >>
       simp[LEFT_EXISTS_IMP_THM] >>
       simp[evaluate_ck_def] >>
       ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
       simp[build_rec_env_def,ml_progTheory.nsLookup_nsBind_compute,do_opapp_def,
            Once find_recfun_def] >>
       simp[Once evaluateTheory.dec_clock_def] >>
       simp[Once terminationTheory.evaluate_def] >>
       simp[evaluateTheory.dec_clock_def] >>
       strip_tac >>
       match_mp_tac (SIMP_RULE (srw_ss())
                       [semanticPrimitivesTheory.build_rec_env_def,
                        evaluate_ck_def]
                       evaluate_tailrec_diverge_lemma) >>
       asm_exists_tac >> simp[] >>
       asm_exists_tac >> simp[]) >-
      (qmatch_asmsub_abbrev_tac `lprefix_lub (IMAGE f _)` >>
       `!i. LPREFIX(f i) (f (i + 1))`
         by(rw[Abbr`f`,LPREFIX_fromList,from_toList] >>
            simp[evaluate_ck_def] >>
            `st with clock := i + 1 = (st with clock := i) with clock := (st with clock := i).clock + 1`
              by(simp[semanticPrimitivesTheory.state_component_equality]) >>
            metis_tac[evaluatePropsTheory.io_events_mono_def,
                      evaluatePropsTheory.evaluate_add_to_clock_io_events_mono]) >>
       drule(GEN_ALL lprefix_lub_unskip) >>
       simp[SimpR ``$==>``, lprefix_lub_def] >>
       strip_tac >>
       conj_tac >-
         (pop_assum(qspecl_then [`l`,`\ck. ck + 2`] mp_tac) >>
          simp[] >>
          impl_tac >- simp[ETA_THM] >>
          qhdtm_x_assum `lprefix_lub` kall_tac >> strip_tac >>
          qunabbrev_tac `f` >>
          rpt strip_tac >>
          fs[lprefix_lub_def] >>
          first_x_assum match_mp_tac >>
          rveq >>
          qmatch_goalsub_abbrev_tac `evaluate_ck ck ast aenv aexp` >>
          Cases_on `evaluate_ck ck ast aenv aexp` >>
          simp[evaluate_ck_def] >>
          ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
          simp[semanticPrimitivesTheory.build_rec_env_def,
               do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
          simp[Once terminationTheory.evaluate_def] >>
          drule evaluate_tailrec_div_ind_lemma2 >>
          rpt(disch_then drule) >>
          disch_then(qspec_then `ck` mp_tac) >> simp[Abbr `aexp`] >>
          unabbrev_all_tac >>
          qpat_x_assum `!ck. ?st. evaluate_ck _ _ _ _ = _`(qspec_then `ck` assume_tac) >>
          fs[] >> rveq >> disch_then drule >>
          simp[evaluate_ck_def,build_rec_env_def] >>
          metis_tac[FST]) >-
         (pop_assum(qspecl_then [`l`,`\ck. ck + 3`] mp_tac) >>
          simp[] >>
          impl_tac >- simp[ETA_THM] >>
          qhdtm_x_assum `lprefix_lub` kall_tac >> strip_tac >>
          qunabbrev_tac `f` >>
          fs[lprefix_lub_def] >>
          rpt strip_tac >> last_x_assum match_mp_tac >>
          rpt strip_tac >> first_x_assum match_mp_tac >>
          rveq >>
          qmatch_goalsub_abbrev_tac `evaluate_ck (ck + 3) ast aenv aexp` >>
          Cases_on `evaluate_ck (ck + 3) ast aenv aexp` >>
          qpat_assum `!ck. ?st'. evaluate_ck ck ast aenv aexp = _`
            (qspec_then `ck + 3` strip_assume_tac) >>
          fs[] >> rveq >>
          pop_assum mp_tac >> unabbrev_all_tac >>
          simp[evaluate_ck_def] >>
          ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
          simp[semanticPrimitivesTheory.build_rec_env_def,
               do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
          simp[Once terminationTheory.evaluate_def] >>
          strip_tac >>
          drule evaluate_tailrec_div_ind_lemma >>
          rpt(disch_then drule) >>
          disch_then(qspec_then `i + 1` mp_tac) >> simp[] >>
          simp[build_rec_env_def] >>
          simp[evaluate_ck_def] >>
          disch_then drule >>
          strip_tac >>
          rename1 `evaluate (_ with clock := newclock)` >>
          qexists_tac `newclock` >>
          simp[])
      )
    ) >>
  qexists_tac `ck` >>
  Q.REFINE_EXISTS_TAC `st' with clock := _` >>
  fs[cfStoreTheory.st2heap_def] >>
  match_mp_tac evaluate_tailrec_lemma >>
  simp[]);

val mk_tailrec_closure_sound = Q.store_thm("mk_tailrec_closure_sound",
  `!fv env . mk_tailrec_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
   /\ do_con_check env.c (SOME (Short "Inr")) 1
   /\ (!v. build_conv env.c (SOME (Short "Inr")) [v] =
           SOME(Conv (SOME (TypeStamp "Inr" 4)) [v]))
   /\ do_con_check env.c (SOME (Short "Inl")) 1
   /\ (!v. build_conv env.c (SOME (Short "Inl")) [v] =
          SOME(Conv (SOME (TypeStamp "Inl" 4)) [v]))
   /\ fname <> farg
   /\ app p fv [x] H Q
   ==> app p (Recclosure env [(fname,farg,fbody)] fname) [x] H Q`,
  metis_tac[mk_tailrec_closure_sound_basic,app_def]);

val some_tailrec_clos_def = Define `
  some_tailrec_clos env = Recclosure env ^tailrec_clos "tailrec"`;

val POSTv_eq = store_thm("POSTv_eq",
  ``$POSTv Q r h <=> ?v. r = Val v /\ Q v h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]);

fun rename_conv s tm =
  let
    val (v,body) = dest_abs tm
  in ALPHA_CONV (mk_var(s,type_of v)) tm end;

val get_index_def = Define `
  get_index st states i = if i = 0:num then (i,st) else
                            (i, states (get_index st states (i-1)))`

val FFI_full_IN_st2heap_IMP = store_thm("FFI_full_IN_st2heap_IMP",
  ``FFI_full io ∈ st2heap p s ==> s.ffi.io_events = io``,
  strip_tac \\ fs [st2heap_def]
  THEN1 fs [store2heap_def,FFI_full_NOT_IN_store2heap_aux]
  \\ Cases_on `p` \\ fs [ffi2heap_def]
  \\ Cases_on `parts_ok s.ffi (q,r)` \\ fs []);

val let_a = tailrec_clos |> rator |> rand |> rand |> rand |> rand

val evaluate_ck_timeout_error_IMP = store_thm("evaluate_ck_timeout_error_IMP",
  ``evaluate_ck ck st env exps = (st1,Rerr (Rabort Rtimeout_error)) /\
    ck0 <= ck ==>
    ?st2. evaluate_ck ck0 st env exps = (st2,Rerr (Rabort Rtimeout_error))``,
  rw [] \\ CCONTR_TAC \\ fs []
  \\ fs [evaluate_ck_def]
  \\ Cases_on `evaluate (st with clock := ck0) env exps` \\ fs []
  \\ drule evaluatePropsTheory.evaluate_add_to_clock \\ fs []
  \\ qexists_tac `ck-ck0` \\ fs []);

val lprefix_mono_lprefix = Q.prove(
  `!f i k.
  (!i. LPREFIX (f i) (f(i + 1)))
  ==> LPREFIX (f i) (f(i + (k:num)))
  `,
  rw[] >> Induct_on `k` >> fs[] >>
  first_x_assum(qspec_then `i + k` assume_tac) >>
  fs[ADD1] >>
  metis_tac[LPREFIX_TRANS]);

val gify = Q.prove(
  `!g n.
  (!i. g i < g (i +1))
  ==> ?k (i:num). g i = (n:num) + k
  `,
  rpt strip_tac >>
  `n <= g n`
    by(Induct_on `n` >> simp[] >>
       qpat_x_assum `!i. _ < _` (qspec_then `n` mp_tac) >>
       simp[] >> strip_tac >>
       fs[LESS_EQ,LESS_EQ_EXISTS,ADD1] >>
       metis_tac[ADD_ASSOC]) >>
  fs[LESS_EQ_EXISTS] >>
  metis_tac[ADD_SYM]);

val lprefix_lub_skip = Q.store_thm("lprefix_lub_skip",
  `(!i. LPREFIX (f i) (f(i + 1))) /\
   (!i. g i < g(i+1)) /\
   lprefix_lub (IMAGE (\i. f (g i)) (UNIV:num set)) l
   ==>
   lprefix_lub (IMAGE (\i. f i) (UNIV:num set)) l
  `,
  rw[lprefix_lubTheory.lprefix_lub_def]
  >- (drule gify >>
      disch_then(qspec_then `i` strip_assume_tac) >>
      drule lprefix_mono_lprefix >>
      disch_then(qspecl_then [`i`,`k`] assume_tac) >>
      match_mp_tac(GEN_ALL LPREFIX_TRANS) >> asm_exists_tac >> simp[] >>
      metis_tac[]) >>
  last_x_assum match_mp_tac >>
  rpt strip_tac >>
  first_x_assum match_mp_tac >> metis_tac[]);

val SUM_GENLIST_SUC = Q.store_thm("SUM_GENLIST_SUC",
  `SUM (GENLIST f (SUC n)) = f n + SUM (GENLIST f n)`,
  fs [GENLIST,SNOC_APPEND,SUM_APPEND]);

val SUM_GENLIST_LESS_EQ = Q.store_thm("SUM_GENLIST_LESS_EQ",
  `!n m f. n <= m ==> SUM (GENLIST f n) <= SUM (GENLIST f m)`,
  Induct \\ Cases_on `m` \\ fs [GENLIST_CONS]);

val tailrec_POSTd = store_thm("tailrec_POSTd",
  ``!p env fv xv H Q.
      nsLookup env.c (Short "Inl") = SOME (1,inl) /\
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
               (POSTv v'. &(v' = Conv (SOME inl) [vs (SUC i)]) *
                          Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p (some_tailrec_clos env) [fv; xv] H ($POSTd Q)``,
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [some_tailrec_clos_def,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,terminationTheory.evaluate_def,PULL_EXISTS,
         cfStoreTheory.st2heap_clock]
  \\ `SPLIT3 (st2heap p st) (h_i,h_k,EMPTY)` by fs [SPLIT3_def,SPLIT_def]
  \\ asm_exists_tac \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rpt strip_tac
  \\ rename [`SPLIT (st2heap p st1) (h_j,h_l)`]
  \\ qexists_tac `Div io`
  \\ fs [POSTd_eq] \\ fs [emp_def]
  \\ qexists_tac `UNIV DIFF h_l`
  \\ qexists_tac `UNIV`
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ fs [app_def,app_basic_def,POSTv_eq,PULL_EXISTS]
  \\ fs [evaluate_to_heap_def,PULL_EXISTS,cond_STAR]
  \\ qabbrev_tac `assert_Hs = \i st.
                    ?h_i h_k. SPLIT (st2heap p st) (h_i,h_k) /\ Hs i h_i`
  \\ `!i st0.
        assert_Hs i st0 ==>
        ?env exp ck st1.
          assert_Hs (i+1) st1 /\
          do_opapp [fv; vs i] = SOME (env,exp) /\
          evaluate_ck ck st0 env [exp] = (st1,Rval [Conv (SOME inl) [vs (i+1)]]) /\
          st1.clock = 0` by
   (fs [Abbr`assert_Hs`,PULL_EXISTS] \\ rpt strip_tac
    \\ first_assum drule \\ disch_then drule
    \\ strip_tac \\ fs [ADD1]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_set_clock
    \\ disch_then (qspec_then `0` mp_tac) \\ strip_tac \\ fs []
    \\ qexists_tac `ck1` \\ fs [cfStoreTheory.st2heap_clock]
    \\ rename [`SPLIT3 (st2heap p st4) (h1,h2,h3)`]
    \\ qexists_tac `h1` \\ fs []
    \\ qexists_tac `h2 UNION h3` \\ fs []
    \\ fs [SPLIT3_def,SPLIT_def,IN_DISJOINT,AC UNION_COMM UNION_ASSOC]
    \\ metis_tac [])
  \\ `!x. ?ck st1. let (i,st0) = x in
            assert_Hs i st0 ==>
            ?env exp.
              assert_Hs (i+1) st1 /\
              do_opapp [fv; vs i] = SOME (env,exp) /\
              evaluate_ck ck st0 env [exp] = (st1,Rval [Conv (SOME inl) [vs (i+1)]]) /\
              st1.clock = 0` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [SKOLEM_THM]))
  \\ simp []
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "clocks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "states"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "i"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "st0"))
  \\ strip_tac
  \\ qabbrev_tac `get_i = get_index st1 states`
  \\ qabbrev_tac `cks = clocks o get_i`
  \\ qabbrev_tac `sts = \i.
                    if i = 0 then st1 else states (get_index st1 states (i-1))`
  \\ `∀i.
        ∃env exp.
            do_opapp [fv; vs i] = SOME (env,exp) ∧
            evaluate_ck (cks i) (sts i) env [exp] =
            (sts (i+1),Rval [Conv (SOME inl) [vs (i + 1)]]) ∧
            (sts (i+1)).clock = 0 ∧
            assert_Hs i (sts i) ∧ assert_Hs (i+1) (sts (i+1))` by
    (Induct THEN1
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ `assert_Hs 0 st1` by
         (fs [Abbr`assert_Hs`] \\ asm_exists_tac \\ fs [SEP_IMP_def])
       \\ fs [] \\ once_rewrite_tac [get_index_def] \\ fs []
       \\ first_x_assum drule \\ strip_tac \\ fs [])
     \\ fs [ADD1]
     \\ first_x_assum drule
     \\ strip_tac \\ fs []
     \\ `(states (i + 1,sts (i + 1))) = sts (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `clocks (i + 1,sts (i + 1)) = cks (i+1)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ fs [])
  \\ qabbrev_tac `cks_sum = \i. SUM (GENLIST cks i) + 3 * i`
  \\ qabbrev_tac `nth_env = \i. (env with
               v :=
                 nsBind "x" (vs i)
                   (nsBind "f" fv
                      (build_rec_env ^tailrec_clos env env.v)))`
  \\ `(env with v :=
                 nsBind "x" (vs 0)
                   (nsBind "f" fv
                      (build_rec_env ^tailrec_clos env env.v))) = nth_env 0`
        by fs [Abbr `nth_env`] \\ fs [] \\ pop_assum kall_tac
  \\ qabbrev_tac `body = ^let_a`
  \\ `(∀i n.
         i <= n ==>
         ∃st'.
            evaluate_ck (cks_sum n - cks_sum i) (sts i) (nth_env i) [body] =
              (st',Rerr (Rabort Rtimeout_error)) /\
            st'.ffi.io_events = events n)` by
   (completeInduct_on `n-i:num` \\ rw []
    \\ fs [PULL_FORALL] \\ Cases_on `n = i` \\ fs [] \\ rveq
    THEN1
     (simp [Once terminationTheory.evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once terminationTheory.evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once terminationTheory.evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ metis_tac [])
    \\ simp [Once terminationTheory.evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once terminationTheory.evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ qpat_x_assum `!i. ?x. _`(qspec_then `i` mp_tac) \\ rw [] \\ fs []
    \\ `cks_sum i + 3 + cks i <= cks_sum n` by
     (fs [Abbr`cks_sum`]
      \\ `SUC i <= n` by fs []
      \\ pop_assum mp_tac
      \\ simp [Once LESS_EQ_EXISTS] \\ rw [ADD1,LEFT_ADD_DISTRIB] \\ fs []
      \\ qsuff_tac `SUM (GENLIST cks i) + cks i <= SUM (GENLIST cks (i + (p' + 1)))`
      THEN1 fs [] \\ fs [GSYM SUM_GENLIST_SUC]
      \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
    \\ simp [evaluateTheory.dec_clock_def,namespaceTheory.nsOptBind_def]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `(cks_sum n − (cks_sum i + 1)) - cks i` mp_tac)
    \\ `cks_sum n − (cks_sum i + 1) − cks i + cks i =
        cks_sum n − (cks_sum i + 1)` by fs [] \\ fs []
    \\ disch_then kall_tac
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ fs [astTheory.pat_bindings_def]
    \\ fs [terminationTheory.pmatch_def,same_ctor_def,same_type_def]
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ simp [Once terminationTheory.evaluate_def]
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once terminationTheory.evaluate_def]
    \\ fs [evaluateTheory.dec_clock_def]
    \\ `(cks i + (cks_sum i + 3)) = cks_sum (i+1)` by
     (fs [Abbr`cks_sum`,GSYM ADD1] \\ fs [GENLIST]
      \\ fs [SNOC_APPEND,SUM_APPEND])
    \\ fs [AND_IMP_INTRO,build_rec_env_def])
  \\ pop_assum (qspec_then `0` mp_tac)
  \\ fs [Abbr `sts`] \\ strip_tac
  \\ `cks_sum 0 = 0` by fs [Abbr `cks_sum`] \\ fs []
  \\ conj_tac
  THEN1
   (rw [] \\ first_assum (qspec_then `ck` mp_tac)
    \\ strip_tac \\ imp_res_tac evaluate_ck_timeout_error_IMP
    \\ pop_assum match_mp_tac
    \\ unabbrev_all_tac \\ fs [GENLIST_CONS])
  \\ ho_match_mp_tac (GEN_ALL lprefix_lub_skip)
  \\ qexists_tac `cks_sum`
  \\ fs [llistTheory.LPREFIX_fromList,llistTheory.from_toList]
  \\ rw []
  THEN1
   (fs [evaluate_ck_def]
    \\ qspecl_then [`st1 with clock := ck`,`nth_env 0`,`[body]`,`1`] mp_tac
         (evaluatePropsTheory.evaluate_add_to_clock_io_events_mono
          |> CONJUNCT1 |> INST_TYPE [``:'ffi``|->``:'a``])
    \\ fs [evaluatePropsTheory.io_events_mono_def])
  THEN1
   (fs [Abbr`cks_sum`]
    \\ qsuff_tac `SUM (GENLIST cks ck) <= SUM (GENLIST cks (ck + 1))` THEN1 fs []
    \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
  \\ qpat_x_assum `lprefix_lub _ io` mp_tac
  \\ match_mp_tac (METIS_PROVE []
       ``x = y ==> lprefix_lub (IMAGE x u) io ==> lprefix_lub (IMAGE y u) io``)
  \\ fs [FUN_EQ_THM] \\ rw [] \\ AP_TERM_TAC
  \\ first_x_assum (qspec_then `ck` strip_assume_tac) \\ fs []);

val app_opapp_intro = Q.store_thm("app_opapp_intro",
  `!body f args env x arg1v fv argsv H P.
  dest_opapp body = SOME(f,args) /\
  (!st:'ffi semanticPrimitives$state. evaluate st (env with v := nsBind x arg1v env.v) (f::args) = (st,Rval (fv::argsv))) /\
  app p fv argsv H P
  ==>
  app (p:'ffi ffi_proj)
      (Closure env x body) [arg1v] H P`,
  cheat);

val _ = (append_prog o cfTacticsLib.process_topdecs)
  `fun repeat f x = repeat f (f x);`

val st = ml_translatorLib.get_ml_prog_state ();

val repeat_v = fetch "-" "repeat_v_def"

val evaluate_IMP_io_events_mono = prove(
  ``evaluate s e exp = (t,res) ==> io_events_mono s.ffi t.ffi``,
  metis_tac [evaluatePropsTheory.evaluate_io_events_mono,FST]);

val repeat_POSTd = store_thm("repeat_POSTd",
  ``!p fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p repeat_v [fv; xv] H ($POSTd Q)``,
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [repeat_v,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,terminationTheory.evaluate_def,PULL_EXISTS,
         cfStoreTheory.st2heap_clock]
  \\ `SPLIT3 (st2heap p st) (h_i,h_k,EMPTY)` by fs [SPLIT3_def,SPLIT_def]
  \\ asm_exists_tac \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rpt strip_tac
  \\ rename [`SPLIT (st2heap p st1) (h_j,h_l)`]
  \\ qexists_tac `Div io`
  \\ fs [POSTd_eq] \\ fs [emp_def]
  \\ qexists_tac `UNIV DIFF h_l`
  \\ qexists_tac `UNIV`
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ fs [app_def,app_basic_def,POSTv_eq,PULL_EXISTS]
  \\ fs [evaluate_to_heap_def,PULL_EXISTS,cond_STAR]
  \\ qabbrev_tac `assert_Hs = \i st.
                    ?h_i h_k. SPLIT (st2heap p st) (h_i,h_k) /\ Hs i h_i`
  \\ `!i st0.
        assert_Hs i st0 ==>
        ?env exp ck st1.
          assert_Hs (i+1) st1 /\
          do_opapp [fv; vs i] = SOME (env,exp) /\
          evaluate_ck ck st0 env [exp] = (st1,Rval [vs (i+1)]) /\
          st1.clock = 0` by
   (fs [Abbr`assert_Hs`,PULL_EXISTS] \\ rpt strip_tac
    \\ first_assum drule \\ disch_then drule
    \\ strip_tac \\ fs [ADD1]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_set_clock
    \\ disch_then (qspec_then `0` mp_tac) \\ strip_tac \\ fs []
    \\ qexists_tac `ck1` \\ fs [cfStoreTheory.st2heap_clock]
    \\ rename [`SPLIT3 (st2heap p st4) (h1,h2,h3)`]
    \\ qexists_tac `h1` \\ fs []
    \\ qexists_tac `h2 UNION h3` \\ fs []
    \\ fs [SPLIT3_def,SPLIT_def,IN_DISJOINT,AC UNION_COMM UNION_ASSOC]
    \\ metis_tac [])
  \\ `!x. ?ck st1. let (i,st0) = x in
            assert_Hs i st0 ==>
            ?env exp.
              assert_Hs (i+1) st1 /\
              do_opapp [fv; vs i] = SOME (env,exp) /\
              evaluate_ck ck st0 env [exp] = (st1,Rval [vs (i+1)]) /\
              st1.clock = 0` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [SKOLEM_THM]))
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "clocks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "states"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "i"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "st0"))
  \\ strip_tac
  \\ qabbrev_tac `get_i = get_index st1 states`
  \\ qabbrev_tac `cks = clocks o get_i`
  \\ qabbrev_tac `sts = \i.
                    if i = 0 then st1 else states (get_index st1 states (i-1))`
  \\ `∀i.
        ∃env exp.
            do_opapp [fv; vs i] = SOME (env,exp) ∧
            evaluate_ck (cks i) (sts i) env [exp] =
            (sts (i+1),Rval [vs (i + 1)]) ∧
            (sts (i+1)).clock = 0 ∧
            assert_Hs i (sts i) ∧ assert_Hs (i+1) (sts (i+1))` by
    (Induct THEN1
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ `assert_Hs 0 st1` by
         (fs [Abbr`assert_Hs`] \\ asm_exists_tac \\ fs [SEP_IMP_def])
       \\ fs [] \\ once_rewrite_tac [get_index_def] \\ fs []
       \\ first_x_assum drule \\ strip_tac \\ fs [])
     \\ fs [ADD1]
     \\ first_x_assum drule
     \\ strip_tac \\ fs []
     \\ `(states (i + 1,sts (i + 1))) = sts (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `clocks (i + 1,sts (i + 1)) = cks (i+1)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ fs [])
  \\ qabbrev_tac `cks_sum = \i. SUM (GENLIST cks i) + 3 * i`
  \\ qpat_abbrev_tac `the_env = nsBind "f" fv _`
  \\ qpat_abbrev_tac `other_env = merge_env _ _`
  \\ qabbrev_tac `nth_env = \i. (other_env with v := nsBind "x" (vs i) the_env)`
  \\ `(other_env with v := nsBind "x" (vs 0) the_env) = nth_env 0`
        by fs [Abbr`nth_env`] \\ fs []
  \\ pop_assum kall_tac
  \\ fs [Abbr`the_env`,Abbr`other_env`]
  \\ qpat_abbrev_tac `body = Let _ _ _`
  \\ `(∀i n.
         i <= n ==>
         ∃st'.
            evaluate_ck (cks_sum n - cks_sum i) (sts i) (nth_env i) [body] =
              (st',Rerr (Rabort Rtimeout_error)) /\
            st'.ffi.io_events = events n)` by
   (completeInduct_on `n-i:num` \\ rw []
    \\ fs [PULL_FORALL] \\ Cases_on `n = i` \\ fs [] \\ rveq
    THEN1
     (simp [Once terminationTheory.evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once terminationTheory.evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once terminationTheory.evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ metis_tac [])
    \\ simp [Once terminationTheory.evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once terminationTheory.evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ qpat_x_assum `!i. ?x. _`(qspec_then `i` mp_tac) \\ rw [] \\ fs []
    \\ `cks_sum i + 3 + cks i <= cks_sum n` by
     (fs [Abbr`cks_sum`]
      \\ `SUC i <= n` by fs []
      \\ pop_assum mp_tac
      \\ simp [Once LESS_EQ_EXISTS] \\ rw [ADD1,LEFT_ADD_DISTRIB] \\ fs []
      \\ qsuff_tac `SUM (GENLIST cks i) + cks i <= SUM (GENLIST cks (i + (p' + 1)))`
      THEN1 fs [] \\ fs [GSYM SUM_GENLIST_SUC]
      \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
    \\ simp [evaluateTheory.dec_clock_def,namespaceTheory.nsOptBind_def]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `(cks_sum n − (cks_sum i + 1)) - cks i` mp_tac)
    \\ `cks_sum n − (cks_sum i + 1) − cks i + cks i =
        cks_sum n − (cks_sum i + 1)` by fs [] \\ fs []
    \\ disch_then kall_tac
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ ntac 3 (simp [Once terminationTheory.evaluate_def])
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once terminationTheory.evaluate_def]
    \\ fs [evaluateTheory.dec_clock_def]
    \\ `(cks i + (cks_sum i + 3)) = cks_sum (i+1)` by
     (fs [Abbr`cks_sum`,GSYM ADD1] \\ fs [GENLIST]
      \\ fs [SNOC_APPEND,SUM_APPEND])
    \\ fs [AND_IMP_INTRO,build_rec_env_def])
  \\ pop_assum (qspec_then `0` mp_tac)
  \\ fs [Abbr `sts`] \\ strip_tac
  \\ `cks_sum 0 = 0` by fs [Abbr `cks_sum`] \\ fs []
  \\ conj_tac
  THEN1
   (rw [] \\ first_assum (qspec_then `ck` mp_tac)
    \\ strip_tac \\ imp_res_tac evaluate_ck_timeout_error_IMP
    \\ pop_assum match_mp_tac
    \\ unabbrev_all_tac \\ fs [GENLIST_CONS])
  \\ ho_match_mp_tac (GEN_ALL lprefix_lub_skip)
  \\ qexists_tac `cks_sum`
  \\ fs [llistTheory.LPREFIX_fromList,llistTheory.from_toList]
  \\ rw []
  THEN1
   (fs [evaluate_ck_def]
    \\ qspecl_then [`st1 with clock := ck`,`nth_env 0`,`[body]`,`1`] mp_tac
         (evaluatePropsTheory.evaluate_add_to_clock_io_events_mono
          |> CONJUNCT1 |> INST_TYPE [``:'ffi``|->``:'a``])
    \\ fs [evaluatePropsTheory.io_events_mono_def])
  THEN1
   (fs [Abbr`cks_sum`]
    \\ qsuff_tac `SUM (GENLIST cks ck) <= SUM (GENLIST cks (ck + 1))` THEN1 fs []
    \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
  \\ qpat_x_assum `lprefix_lub _ io` mp_tac
  \\ match_mp_tac (METIS_PROVE []
       ``x = y ==> lprefix_lub (IMAGE x u) io ==> lprefix_lub (IMAGE y u) io``)
  \\ fs [FUN_EQ_THM] \\ rw [] \\ AP_TERM_TAC
  \\ first_x_assum (qspec_then `ck` strip_assume_tac) \\ fs []);

val repeat_POSTe = store_thm("repeat_POSTe",
  ``!p fv xv H Q.
      (?Hs vs j.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. i < j ==>
            app p fv [vs i] (Hs i)
                            (POSTv v. &(v = vs (SUC i)) * Hs (SUC i))) /\
         app p fv [vs j] (Hs j) ($POSTe Q))
      ==>
      app p repeat_v [fv; xv] H ($POSTe Q)``,
  rpt strip_tac
  \\ `!i. i <= j ==> app p repeat_v [fv; vs i] (Hs i) ($POSTe Q)` by (
    rpt strip_tac
    \\ Induct_on `j - i`
    THEN1 (
      xcf "repeat" st
      \\ `i = j` by decide_tac \\ rveq
      \\ xlet `$POSTe Q` THEN1 xapp
      \\ xsimpl)
    \\ xcf "repeat" st
    \\ `i < j` by decide_tac
    \\ xlet `POSTv v. &(v = vs (SUC i)) * Hs (SUC i)`
    THEN1 (
      `app p fv [vs i] (Hs i) (POSTv v. &(v = vs (SUC i)) * Hs (SUC i))`
        by (first_assum irule \\ rw [])
      \\ xapp)
    \\ rveq
    \\ `app p repeat_v [fv; vs (SUC i)] (Hs (SUC i)) ($POSTe Q)`
         by (first_assum irule \\ qexists_tac `j` \\ rw [])
    \\ xapp)
  \\ `app p repeat_v [fv; vs 0] (Hs 0) ($POSTe Q)`
       by (first_assum irule \\ rw [])
  \\ rveq \\ xapp
  \\ qexists_tac `emp`
  \\ xsimpl);

val _ = export_theory();
