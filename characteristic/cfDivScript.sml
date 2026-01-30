(*
  Defines the repeat function and the corresponding lemma used to prove
  non-termination of programs in cf.
*)
Theory cfDiv
Ancestors
  set_sep ml_translator ml_translator semanticPrimitives
  cfHeapsBase cfHeaps cfStore cfNormalise cfApp evaluate cf
  std_prelude
Libs
  preamble helperLib cfHeapsBaseLib cfTacticsBaseLib cfTacticsLib

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = ml_translatorLib.translation_extends "std_prelude";

(* Make sure we are using the option monad even in the presence of other
   monads *)
val _ = monadsyntax.temp_enable_monadsyntax ();
val _ = monadsyntax.temp_enable_monad "option";

(* -- general set up -- *)

val st = ``st:'ffi semanticPrimitives$state``

Theorem POSTd_eq:
  $POSTd Q r h <=> ?io1. r = Div io1 /\ Q io1 /\ emp h
Proof
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
  \\ eq_tac \\ rw []
QED

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_translatorLib.ml_prog_update (ml_progLib.add_prog tm I) end

Theorem dest_opapp_exp_size:
  !tm f arg. dest_opapp tm = SOME(f,arg)
   ==> list_size exp_size arg < exp_size tm
Proof
  ho_match_mp_tac cfNormaliseTheory.dest_opapp_ind
  >> rw[cfNormaliseTheory.dest_opapp_def]
  >> every_case_tac
  >> gvs [list_size_append]
QED

Theorem dest_opapp_eq_nil_IMP:
  dest_opapp(exp) = SOME(f,[])
   ==> F
Proof
  Cases_on `exp` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  rename1 `App op exps` >>
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[] >> strip_tac
QED

Theorem dest_opapp_eq_single_IMP:
  dest_opapp(App op exps) = SOME(f,[arg])
   ==> op = Opapp /\ exps = [f;arg]
Proof
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[] >> strip_tac >>
  rveq >> rename1 `dest_opapp exp` >>
  Cases_on `exp` >> fs[cfNormaliseTheory.dest_opapp_def] >>
  rename1 `App op exps` >>
  Cases_on `op` >> Cases_on `exps` >>
  fs[cfNormaliseTheory.dest_opapp_def] >>
  every_case_tac >> fs[]
QED

Theorem nsLookup_build_rec_env_fresh:
  !funs env env' fname.
    EVERY (λx. fname ≠ x) (MAP FST funs)
    ==>
    nsLookup(build_rec_env funs env' env.v) (Short fname) =
    nsLookup env.v (Short fname)
Proof
  `∀(funs:(mlstring # mlstring # exp) list) funs' env env' fname.
   EVERY (λx. fname ≠ x) (MAP FST funs) ⇒
   nsLookup
   (FOLDR (λ(f,x,e) env''. nsBind f (Recclosure env' (funs':(mlstring # mlstring # exp) list) f) env'')
          env.v funs) (Short fname) = nsLookup env.v (Short fname)`
    suffices_by rw[semanticPrimitivesTheory.build_rec_env_def] >>
  Induct >> rw[semanticPrimitivesTheory.build_rec_env_def] >>
  fs[ELIM_UNCURRY]
QED

Theorem nsLookup_alist_to_ns_fresh:
  !l fname.
    EVERY (λx. fname ≠ x) (MAP FST l)
    ==>
    nsLookup(alist_to_ns l) (Short fname) = NONE
Proof
  fs[namespaceTheory.alist_to_ns_def,namespaceTheory.nsLookup_def,
     ALOOKUP_NONE,EVERY_MEM]
QED


(* -- tailrec -- *)

val tailrec_clos = process_topdecs `
  fun tailrec f x =
    case f x of
      Inl x => tailrec f x
    | Inr y => y;
  ` |> rator |> rand |> rand

val tailrec_body = tailrec_clos |> rator |> rand |> rand |> rand |> rand

Definition mk_inl_def:
  mk_inl e =
  Let (SOME «x») e (Con(SOME(Short «Inl»)) [Var(Short «x»)])
End

Definition mk_inr_def:
  mk_inr e =
  Let (SOME «x») e (Con(SOME(Short «Inr»)) [Var(Short «x»)])
End

Definition mk_single_app_def:
   (mk_single_app fname allow_fname (Raise e) =
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
    SOME [])
Termination
  WF_REL_TAC `inv_image $< (\x. case x of INL (t,x,e) => exp_size e
   | INR (INL (t,x,es)) => list_size exp_size es
   | INR (INR (INL (t,x,pes))) =>
       list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR (t,x,funs))) =>
       list_size (pair_size mlstring_size
                  (pair_size mlstring_size exp_size)) funs)`
  \\ rw[]
  \\ gvs [Once (dest_opapp_def |> DefnBase.one_line_ify NONE)]
  \\ gvs [AllCaseEqs()]
End

val mk_single_app_ind = fetch "-" "mk_single_app_ind"

Definition mk_stepfun_closure_def:
  (mk_stepfun_closure env fname farg fbody =
    do
     gbody <- mk_single_app (SOME fname) T fbody;
     SOME(let benv = build_rec_env [(fname,farg,fbody)] env env.v
          in Closure (env with v := benv) farg gbody)
    od) /\ mk_stepfun_closure _ _ _ _ = NONE
End

Definition mk_tailrec_closure_def:
  (mk_tailrec_closure (Recclosure env [(fname,farg,fbody)] name2) =
    do
     gclosure <- mk_stepfun_closure  env fname farg fbody;
     SOME(Closure (env with <| v :=
            (nsBind fname gclosure env.v) |>) farg
          (App Opapp
               [App Opapp
                  [Letrec ^tailrec_clos (Var(Short «tailrec»));
                   Var(Short fname)];
                Var(Short farg)]
          )
         )
    od) /\ mk_tailrec_closure _ = NONE
End

Theorem mk_single_app_F_unchanged_gen[local]:
  (!fname allow_fname e e'. mk_single_app fname allow_fname e = SOME e'
               /\ allow_fname = F ==> e = e') /\
   (!fname allow_fname es es'. mk_single_apps fname allow_fname es = SOME es'
               /\ allow_fname = F ==> es = es') /\
   (!fname allow_fname pes pes'. mk_single_appps fname allow_fname pes = SOME pes'
                /\ allow_fname = F ==> pes = pes') /\
   (!fname allow_fname recfuns recfuns'. mk_single_appr fname allow_fname recfuns = SOME recfuns'
                /\ allow_fname = F ==> recfuns = recfuns')
Proof
  ho_match_mp_tac mk_single_app_ind >>
  rw[mk_single_app_def] >> fs[] >>
  every_case_tac >> fs[] >> rfs[] >>
  first_x_assum drule >> simp[] >>
  imp_res_tac dest_opapp_eq_single_IMP >>
  fs[]
QED

Theorem mk_single_app_F_unchanged =
  SIMP_RULE std_ss [] mk_single_app_F_unchanged_gen

Definition mk_inr_res_def:
  (mk_inr_res(Rval vs) =
   Rval(MAP (λv. Conv (SOME (TypeStamp «Inr» 4)) [v]) vs)
  ) /\
  (mk_inr_res res = res)
End

Definition mk_inl_res_def:
  (mk_inl_res(Rval vs) =
   Rval(MAP (λv. Conv (SOME (TypeStamp «Inl» 4)) [v]) vs)
  ) /\
  (mk_inl_res res = res)
End

Definition dest_inr_v_def:
  (dest_inr_v (Conv (SOME (TypeStamp txt n)) [v]) =
   if txt = «Inr» /\ n = 4 then
     SOME v
   else
     NONE) /\
  (dest_inr_v _ = NONE)
End

Definition dest_inl_v_def:
  (dest_inl_v (Conv (SOME (TypeStamp txt n)) [v]) =
   if txt = «Inl» /\ n = 4 then
     SOME v
   else
     NONE) /\
  (dest_inl_v _ = NONE)
End

Theorem dest_inr_v_IMP:
  !e1 v. dest_inr_v e1 = SOME v ==> e1 = Conv (SOME (TypeStamp «Inr» 4)) [v]
Proof
  ho_match_mp_tac (fetch "-" "dest_inr_v_ind") >>
  rw[dest_inr_v_def]
QED

Theorem dest_inl_v_IMP:
  !e1 v. dest_inl_v e1 = SOME v ==> e1 = Conv (SOME (TypeStamp «Inl» 4)) [v]
Proof
  ho_match_mp_tac (fetch "-" "dest_inl_v_ind") >>
  rw[dest_inl_v_def]
QED

Theorem evaluate_inl:
    do_con_check env.c (SOME (Short «Inl»)) 1 = T /\
    (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
    ==> evaluate st env [mk_inl e] =
        case evaluate st env [e] of
            (st,Rval v) => (st,mk_inl_res(Rval v))
          | (st,rerr) => (st,rerr)
Proof
    rw[evaluate_def,mk_inl_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute,mk_inl_res_def] >>
    ntac 2(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]
QED

Theorem build_conv_check_IMP_nsLookup[local]:
  !env const v consname stamp n.
  (∀v. build_conv env (SOME const) [v] =
   SOME (Conv (SOME stamp) [v])) /\
  do_con_check env (SOME const) n
  ==> nsLookup env const = SOME(n,stamp)
Proof
  rw[semanticPrimitivesTheory.build_conv_def,semanticPrimitivesTheory.do_con_check_def,
     namespaceTheory.nsLookup_def] >>
  every_case_tac >> fs[]
QED

Theorem evaluate_IMP_inl:
    do_con_check env.c (SOME (Short «Inl»)) 1 = T /\
    (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
    evaluate st env [e] = (st',res)
    ==> evaluate st env [mk_inl e] = (st',mk_inl_res res)
Proof
    rw[evaluate_def,mk_inl_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute] >>
    PURE_TOP_CASE_TAC >> fs[mk_inl_res_def] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]
QED

Theorem evaluate_inr:
    do_con_check env.c (SOME (Short «Inr»)) 1 = T /\
    (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    ==> evaluate st env [mk_inr e] =
        case evaluate st env [e] of
            (st,Rval v) => (st,mk_inr_res(Rval v))
          | (st,rerr) => (st,rerr)
Proof
    rw[evaluate_def,mk_inr_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute,mk_inr_res_def] >>
    ntac 2(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]
QED

Theorem evaluate_IMP_inr:
    do_con_check env.c (SOME (Short «Inr»)) 1 = T /\
    (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
    evaluate ^st env [e] = (st',res)
    ==> evaluate st env [mk_inr e] = (st',mk_inr_res res)
Proof
    rw[evaluate_def,mk_inr_def,namespaceTheory.nsOptBind_def,
       ml_progTheory.nsLookup_nsBind_compute] >>
    PURE_TOP_CASE_TAC >> fs[mk_inr_res_def] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >>
    fs[quantHeuristicsTheory.LIST_LENGTH_1]
QED

Theorem mk_single_appps_MAP_FST:
  !pes x b pes'.
    mk_single_appps x b pes = SOME pes' ==>
    MAP FST pes = MAP FST pes'
Proof
  Induct \\ fs [mk_single_app_def,FORALL_PROD]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

Theorem mk_single_app_NONE_evaluate[local]:
  (!^st env es es'. mk_single_apps NONE T es = SOME es'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    ==> evaluate st env es'
        = case evaluate st env es of
           (st',res) => (st', mk_inr_res res)
   ) /\
   (!^st env v pes err_v pes'. mk_single_appps NONE T pes = SOME pes'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    ==> evaluate_match st env v pes' err_v
        = case evaluate_match st env v pes err_v of
           (st',res) => (st', mk_inr_res res)
   )
Proof
  ho_match_mp_tac evaluate_ind >> rpt strip_tac >> PURE_TOP_CASE_TAC
  (* Nil *)
  >- (fs[mk_single_app_def] >> rveq >> fs[evaluate_def,mk_inr_res_def])
  (* Sequence *)
  >- (fs[Once evaluate_def,mk_single_app_def] >>
      rveq >> every_case_tac >>
      fs[] >> rveq >> fs[PULL_EXISTS] >>
      rpt(first_x_assum drule) >> rpt(disch_then drule) >> rpt strip_tac >>
      simp[Once evaluate_def] >>
      fs[mk_inr_res_def] >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1])
  (* Lit *)
  >- (fs[mk_single_app_def] >> rveq >> fs[evaluate_IMP_inr])
  (* Raise *)
  >- (fs[mk_single_app_def] >> rveq >> fs[evaluate_IMP_inr] >> fs[evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[] >> rveq >> fs[mk_inr_res_def])
  (* Handle *)
  >- (fs[mk_single_app_def] >> rveq >> fs[Once evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[] >> rveq >>
      rfs[evaluate_inr] >> fs[mk_inr_res_def] >>
      rveq >> fs[] >> imp_res_tac mk_single_appps_MAP_FST >> fs [])
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
          simp[] >> simp[evaluate_def] >>
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
      fs[Once evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[semanticPrimitivesTheory.do_if_def] >>
      rw[] >> fs[] >>
      rveq >> fs[mk_inr_res_def])
  (* Mat *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs [pair_case_eq, CaseEq"result",CaseEq"bool"] >>
      imp_res_tac mk_single_appps_MAP_FST >> fs [] >>
      rveq >> fs[mk_inr_res_def])
  (* Let *)
  >- (rename1 `Let xo` >> Cases_on `xo` >>
      fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once evaluate_def] >>
      TOP_CASE_TAC >> reverse TOP_CASE_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[] >> rveq >> fs[mk_inr_res_def])
  (* Letrec *)
  >- (fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once evaluate_def] >>
      rw[] >> fs[] >> rveq >> fs[mk_inr_res_def])
  (* Tannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once evaluate_def])
  (* Lannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once evaluate_def])
  (* Pmatch empty row *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[evaluate_def] >> rveq >>
      fs[mk_inr_res_def])
  (* Pmatch cons *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[Once evaluate_def] >> rveq >>
      reverse IF_CASES_TAC >-
        (fs[] >> rveq >> fs[mk_inr_res_def]) >>
      fs[] >> rveq >> fs[mk_inr_res_def] >>
      TOP_CASE_TAC >> gs[] >> rveq >> fs[mk_inr_res_def])
QED

Theorem mk_single_app_NONE_evaluate_single[local]:
  (!^st env e e'. mk_single_app NONE T e = SOME e'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    ==> evaluate st env [e']
        = case evaluate st env [e] of
           (st',res) => (st', mk_inr_res res)
   )
Proof
  rpt strip_tac >>
  match_mp_tac(CONJUNCT1 mk_single_app_NONE_evaluate) >>
  simp[mk_single_app_def]
QED

Definition partially_evaluates_to_def:
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
End

Definition partially_evaluates_to_match_def:
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
End

Theorem mk_single_app_evaluate[local]:
  (!^st env es es' fname fv. mk_single_apps (SOME fname) T es = SOME es'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    /\ do_con_check env.c (SOME (Short «Inl»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to fv env st (ZIP(es',es))
   ) /\
   (!^st env v pes err_v pes' fname fv. mk_single_appps (SOME fname) T pes = SOME pes'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    /\ do_con_check env.c (SOME (Short «Inl»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to_match fv v err_v env st (pes',pes)
   )
Proof
  ho_match_mp_tac evaluate_ind >> rpt strip_tac
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
      fs[evaluate_def,mk_inr_res_def,dest_inr_v_def])
  (* Raise *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def,evaluate_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      every_case_tac >> fs[])
  (* Handle *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[partially_evaluates_to_def] >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[Once evaluate_def] >>
      fs[evaluate_inr] >>
      every_case_tac >> fs[PULL_EXISTS] >> rveq >>
      imp_res_tac mk_single_appps_MAP_FST >>
      fs[mk_inr_res_def] >> rveq >>
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      fs[dest_inr_v_def] >>
      fs[evaluate_def] >>
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
      simp[evaluate_def,mk_inr_res_def,dest_inr_v_def])
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
          fs[evaluate_def] >>
          rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
          imp_res_tac evaluatePropsTheory.evaluate_length >>
          fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >>
          fs[mk_inl_res_def] >> rveq >>
          fs[dest_inl_v_def,dest_inr_v_def] >>
          fs[astTheory.getOpClass_def] >>
          qmatch_goalsub_abbrev_tac `a1 = _` >>
          MAP_EVERY qexists_tac [`FST a1`,`SND a1`] >>
          simp[] >> PURE_TOP_CASE_TAC >> simp[]) >>
      fs[cfNormaliseTheory.dest_opapp_def] >>
      rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      simp[partially_evaluates_to_def,evaluate_inr] >>
      simp[evaluate_def] >>
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
      fs[evaluate_def,semanticPrimitivesTheory.do_if_def] >>
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
      reverse(Cases_on `result`) >- fs[evaluate_def] >>
      fs[evaluate_def,partially_evaluates_to_match_def,PULL_EXISTS] >>
      imp_res_tac mk_single_appps_MAP_FST >>
      IF_CASES_TAC >> fs [] >>
      rpt(first_x_assum drule >> rpt(disch_then drule) >> rpt strip_tac) >>
      rpt(TOP_CASE_TAC >> fs[] >> rveq))
  (* Let *)
  >- (rename1 `Let xo` >> Cases_on `xo` >>
      fs[mk_single_app_def] >> rveq >>
      imp_res_tac mk_single_app_F_unchanged >> rveq >>
      fs[partially_evaluates_to_def,PULL_EXISTS] >>
      fs[evaluate_def,namespaceTheory.nsOptBind_def] >>
      Cases_on `evaluate st env [e1]` >> rename1 `(_,result)` >>
      reverse(Cases_on `result`) >- fs[evaluate_def] >>
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
      fs[partially_evaluates_to_def,evaluate_def] >>
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
      simp[partially_evaluates_to_def,evaluate_def])
  (* Lannot *)
  >- (fs[mk_single_app_def] >> rveq >>
      fs[PULL_EXISTS] >> first_x_assum drule >>
      rpt(disch_then drule) >>
      simp[partially_evaluates_to_def,evaluate_def])
  (* Pmatch empty row *)
  >- (fs[mk_single_app_def] >> rveq >>
      simp[partially_evaluates_to_match_def,evaluate_def])
  (* Pmatch cons *)
  >- (fs[mk_single_app_def] >> rveq >>
      PURE_FULL_CASE_TAC >> FULL_SIMP_TAC std_ss [] >>
      fs[partially_evaluates_to_match_def,evaluate_def] >>
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
QED

Theorem mk_single_app_evaluate_single:
  !^st env e e' fname fv. mk_single_app (SOME fname) T e = SOME e'
    /\ do_con_check env.c (SOME (Short «Inr»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
    /\ do_con_check env.c (SOME (Short «Inl»)) 1 = T
    /\ (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
    /\ nsLookup env.v (Short fname) = SOME fv
    ==> partially_evaluates_to fv env st [(e',e)]
Proof
  rpt strip_tac >>
  `mk_single_apps (SOME fname) T [e] = SOME [e']` by simp[mk_single_app_def] >>
  drule(CONJUNCT1 mk_single_app_evaluate) >>
  rpt(disch_then drule) >> simp[]
QED

Theorem evaluate_tailrec_ind_lemma[local]:
  !ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short «Inr»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inr»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
   do_con_check env.c (SOME (Short «Inl»)) 1 /\
   res <> Rerr(Rabort(Rtimeout_error)) /\
   (∀v.
        build_conv env.c (SOME (Short «Inl»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
   fname <> farg /\
   evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
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
         [fbody] = (st' with clock := ck',res)
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  rw[] >> pop_assum mp_tac >>
  simp[Once evaluate_def] >>
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
      simp[Once evaluate_def] >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp [can_pmatch_all_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      simp[Once evaluate_def] >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      simp[Once evaluate_def] >>
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
      simp[Once evaluate_def] >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp [can_pmatch_all_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      simp[evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      simp[Once evaluate_def] >>
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
         imp_res_tac evaluate_clock >>
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
QED

Theorem evaluate_tailrec_lemma[local]:
  !ck fbody gbody env ^st farg x fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short «Inr»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inr»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
   do_con_check env.c (SOME (Short «Inl»)) 1 /\
   res <> Rerr(Rabort(Rtimeout_error)) /\
   (∀v.
        build_conv env.c (SOME (Short «Inl»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
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
           [Letrec ^tailrec_clos (Var(Short «tailrec»));
            Var(Short fname)]; Var (Short farg)]] = (st',res) ==>
    ∃ck'.evaluate_ck ck ^st
         (env with
          v := nsBind farg x (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st' with clock := ck',res)
Proof
  rpt strip_tac >>
  fs[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 8 (simp[Once evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  rw[] >> pop_assum mp_tac >>
  simp[Once evaluate_def] >>
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
  simp[semanticPrimitivesTheory.state_component_equality]
QED

Theorem mk_single_app_unroll_lemma[local]:
  !fname fbody gbody ^st st' ck1 env farg ck2 x v.
    mk_single_app (SOME fname) T fbody = SOME gbody /\
    evaluate (^st with clock := ck1)
               (env with
                v :=
                  nsBind farg x
                    (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                       env.v)) [gbody] =
             (st' with clock := 0,mk_inl_res(Rval [v])) /\
    do_con_check env.c (SOME (Short «Inr»)) 1 /\
    (∀v.
      build_conv env.c (SOME (Short «Inr»)) [v] =
     SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
    do_con_check env.c (SOME (Short «Inl»)) 1 /\
    (∀v.
      build_conv env.c (SOME (Short «Inl»)) [v] =
     SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
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
            [fbody]
Proof
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
  simp[] >> fs[build_rec_env_def]
QED

Theorem evaluate_tailrec_diverge_lemma[local]:
  !ck fbody gbody env env' ^st farg x v fname.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short «Inr»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inr»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
   do_con_check env.c (SOME (Short «Inl»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inl»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
   fname <> farg /\
   (!ck. ?st'. evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
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
         [fbody] = (st',Rerr(Rabort(Rtimeout_error)))
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once evaluate_def]) >>
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
        simp[evaluate_def,namespaceTheory.nsOptBind_def,
             astTheory.pat_bindings_def,semanticPrimitivesTheory.pmatch_def,
             semanticPrimitivesTheory.same_type_def,can_pmatch_all_def,
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
        ntac 2 (simp[Once evaluate_def]) >>
        simp[namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute] >>
        simp[Once evaluate_def] >>
        imp_res_tac build_conv_check_IMP_nsLookup >>
        simp[astTheory.pat_bindings_def,semanticPrimitivesTheory.pmatch_def,
             semanticPrimitivesTheory.same_type_def,can_pmatch_all_def,
             semanticPrimitivesTheory.same_ctor_def] >>
        ntac 7 (simp[Once evaluate_def]) >>
        simp[do_opapp_def,Once find_recfun_def] >>
        simp[GSYM LEFT_EXISTS_IMP_THM] >>
        Q.REFINE_EXISTS_TAC `extra + 2` >>
        simp[LEFT_EXISTS_IMP_THM] >>
        simp[evaluateTheory.dec_clock_def] >>
        simp[Once evaluate_def] >>
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
QED

Theorem evaluate_tailrec_div_ind_lemma[local]:
  !ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short «Inr»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inr»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
   do_con_check env.c (SOME (Short «Inl»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inl»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
   fname <> farg /\
   ck > 0 /\
   evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
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
         [fbody] = (st',Rerr(Rabort(Rtimeout_error)))
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once evaluate_def]) >>
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
      ntac 2 (simp[Once evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def] >>
      simp[Once evaluate_def]
    ) >-
    ((* Rval([Inl v]) *)
      imp_res_tac evaluatePropsTheory.evaluate_length >>
      fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >>
      imp_res_tac dest_inl_v_IMP >>
      fs[] >> rveq >>
      ntac 2(simp[Once evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def] >>
      simp[evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      IF_CASES_TAC >-
        (strip_tac >> fs[Abbr `ast`,do_opapp_def,Once find_recfun_def] >>
         asm_exists_tac >> simp[]) >>
      simp[Once evaluate_def] >>
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
        (rveq >> simp[evaluate_def,do_opapp_def] >>
         strip_tac >> rveq >> qexists_tac `ck1` >>
         simp[semanticPrimitivesTheory.state_component_equality]) >>
      `ack < ck`
        by(imp_res_tac evaluate_clock >> fs[Abbr `ack`]) >>
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
QED

Theorem evaluate_tailrec_div_ind_lemma2[local]:
  !ck fbody gbody env env' ^st farg x v fname st' res.
   mk_single_app (SOME fname) T fbody = SOME gbody /\
   do_con_check env.c (SOME (Short «Inr»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inr»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) /\
   do_con_check env.c (SOME (Short «Inl»)) 1 /\
   (∀v.
        build_conv env.c (SOME (Short «Inl»)) [v] =
        SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) /\
   fname <> farg /\
   evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort(Rtimeout_error))) ==>
   ?ck. evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
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
     [^tailrec_body] = (st',Rerr(Rabort(Rtimeout_error)))
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  Q.REFINE_EXISTS_TAC `ck' + 1` >>
  ntac 5 (simp[Once evaluate_def]) >>
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
      ntac 2(simp[Once evaluate_def]) >>
      simp[namespaceTheory.nsOptBind_def] >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def] >>
      imp_res_tac build_conv_check_IMP_nsLookup >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
      fs[do_opapp_def,Once find_recfun_def] >>
      qhdtm_x_assum `COND` mp_tac >>
      IF_CASES_TAC >-
        (strip_tac >> rveq >> qexists_tac `0` >>
         simp[evaluate_def,do_opapp_def,Once find_recfun_def,
              semanticPrimitivesTheory.state_component_equality]) >>
      strip_tac >>
      Q.REFINE_EXISTS_TAC `extra + 2` >>
      simp[Once evaluate_def] >>
      simp[astTheory.pat_bindings_def] >>
      simp[semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def] >>
      simp[evaluate_def] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      simp[Once evaluate_def] >>
      simp[evaluateTheory.dec_clock_def] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      fs[evaluateTheory.dec_clock_def] >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac evaluate_clock >> fs[])
QED

Theorem lprefix_mono_lprefix[local]:
  !f i k.
 (!i. LPREFIX (f i) (f(i + 1)))
 ==> LPREFIX (f i) (f(i + (k:num)))
Proof
  rw[] >> Induct_on `k` >> fs[] >>
 first_x_assum(qspec_then `i + k` assume_tac) >>
 fs[ADD1] >>
 metis_tac[LPREFIX_TRANS]
QED

Theorem gify[local]:
  !g n.
 (!i. g i < g (i +1))
 ==> ?k (i:num). g i = (n:num) + k
Proof
  rpt strip_tac >>
 `n <= g n`
   by(Induct_on `n` >> simp[] >>
      qpat_x_assum `!i. _ < _` (qspec_then `n` mp_tac) >>
      simp[] >> strip_tac >>
      fs[LESS_EQ,LESS_EQ_EXISTS,ADD1] >>
      metis_tac[ADD_ASSOC]) >>
 fs[LESS_EQ_EXISTS] >>
 metis_tac[ADD_SYM]
QED

Theorem lprefix_lub_unskip:
  (!i. LPREFIX (f i) (f(i + 1))) /\
  (!i. g i < g(i+1)) /\
  lprefix_lub (IMAGE (\i. f i) (UNIV:num set)) l
  ==>
  lprefix_lub (IMAGE (\i. f (g i)) (UNIV:num set)) l
Proof
 rw[lprefix_lubTheory.lprefix_lub_def] >- metis_tac[] >>
 last_x_assum match_mp_tac >> rpt strip_tac >> rveq >>
 drule gify >>
 disch_then(qspec_then `i` strip_assume_tac) >>
 drule lprefix_mono_lprefix >>
 disch_then(qspecl_then [`i`,`k`] assume_tac) >>
 match_mp_tac(GEN_ALL LPREFIX_TRANS) >> asm_exists_tac >> simp[] >>
 metis_tac[]
QED

Theorem mk_tailrec_closure_sound_basic:
   !fv env . mk_tailrec_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
   /\ do_con_check env.c (SOME (Short «Inr»)) 1
   /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
   /\ do_con_check env.c (SOME (Short «Inl»)) 1
   /\ (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
          SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
   /\ fname <> farg
   /\ app_basic (p:'ffi ffi_proj) fv x H Q
   ==> app_basic p (Recclosure env [(fname,farg,fbody)] fname) x H Q
Proof
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
       ntac 8 (simp[Once evaluate_def]) >>
       simp[build_rec_env_def,ml_progTheory.nsLookup_nsBind_compute,do_opapp_def,
            Once find_recfun_def] >>
       simp[Once evaluateTheory.dec_clock_def] >>
       simp[Once evaluate_def] >>
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
          ntac 8 (simp[Once evaluate_def]) >>
          simp[semanticPrimitivesTheory.build_rec_env_def,
               do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
          simp[Once evaluate_def] >>
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
          ntac 8 (simp[Once evaluate_def]) >>
          simp[semanticPrimitivesTheory.build_rec_env_def,
               do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
          simp[Once evaluate_def] >>
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
  simp[]
QED

Theorem mk_tailrec_closure_sound:
   !fv env . mk_tailrec_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
   /\ do_con_check env.c (SOME (Short «Inr»)) 1
   /\ (!v. build_conv env.c (SOME (Short «Inr»)) [v] =
           SOME(Conv (SOME (TypeStamp «Inr» 4)) [v]))
   /\ do_con_check env.c (SOME (Short «Inl»)) 1
   /\ (!v. build_conv env.c (SOME (Short «Inl»)) [v] =
          SOME(Conv (SOME (TypeStamp «Inl» 4)) [v]))
   /\ fname <> farg
   /\ app p fv [x] H Q
   ==> app p (Recclosure env [(fname,farg,fbody)] fname) [x] H Q
Proof
  metis_tac[mk_tailrec_closure_sound_basic,app_def]
QED

Definition some_tailrec_clos_def:
  some_tailrec_clos env = Recclosure env ^tailrec_clos «tailrec»
End

Theorem POSTv_eq:
  $POSTv Q r h <=> ?v. r = Val v /\ Q v h
Proof
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
QED

fun rename_conv s tm =
  let
    val (v,body) = dest_abs tm
  in ALPHA_CONV (mk_var(s,type_of v)) tm end;

Definition get_index_def:
  get_index st states i = if i = 0:num then (i,st) else
                            (i, states (get_index st states (i-1)))
End

Theorem FFI_full_IN_st2heap_IMP:
  FFI_full io ∈ st2heap p s ==> s.ffi.io_events = io
Proof
  strip_tac \\ fs [st2heap_def]
  THEN1 fs [store2heap_def,FFI_full_NOT_IN_store2heap_aux]
  \\ Cases_on `p` \\ fs [ffi2heap_def]
  \\ Cases_on `parts_ok s.ffi (q,r)` \\ fs []
QED

val let_a = tailrec_clos |> rator |> rand |> rand |> rand |> rand

Theorem evaluate_ck_timeout_error_IMP:
    evaluate_ck ck st env exps = (st1,Rerr (Rabort Rtimeout_error)) /\
    ck0 <= ck ==>
    ?st2. evaluate_ck ck0 st env exps = (st2,Rerr (Rabort Rtimeout_error))
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ fs [evaluate_ck_def]
  \\ Cases_on `evaluate (st with clock := ck0) env exps` \\ fs []
  \\ drule evaluatePropsTheory.evaluate_add_to_clock \\ fs []
  \\ qexists_tac `ck-ck0` \\ fs []
QED

Theorem lprefix_mono_lprefix[local]:
  !f i k.
  (!i. LPREFIX (f i) (f(i + 1)))
  ==> LPREFIX (f i) (f(i + (k:num)))
Proof
  rw[] >> Induct_on `k` >> fs[] >>
  first_x_assum(qspec_then `i + k` assume_tac) >>
  fs[ADD1] >>
  metis_tac[LPREFIX_TRANS]
QED

Theorem gify[local]:
  !g n.
  (!i. g i < g (i +1))
  ==> ?k (i:num). g i = (n:num) + k
Proof
  rpt strip_tac >>
  `n <= g n`
    by(Induct_on `n` >> simp[] >>
       qpat_x_assum `!i. _ < _` (qspec_then `n` mp_tac) >>
       simp[] >> strip_tac >>
       fs[LESS_EQ,LESS_EQ_EXISTS,ADD1] >>
       metis_tac[ADD_ASSOC]) >>
  fs[LESS_EQ_EXISTS] >>
  metis_tac[ADD_SYM]
QED

Theorem lprefix_lub_skip:
   (!i. LPREFIX (f i) (f(i + 1))) /\
   (!i. g i < g(i+1)) /\
   lprefix_lub (IMAGE (\i. f (g i)) (UNIV:num set)) l
   ==>
   lprefix_lub (IMAGE (\i. f i) (UNIV:num set)) l
Proof
  rw[lprefix_lubTheory.lprefix_lub_def]
  >- (drule gify >>
      disch_then(qspec_then `i` strip_assume_tac) >>
      drule lprefix_mono_lprefix >>
      disch_then(qspecl_then [`i`,`k`] assume_tac) >>
      match_mp_tac(GEN_ALL LPREFIX_TRANS) >> asm_exists_tac >> simp[] >>
      metis_tac[]) >>
  last_x_assum match_mp_tac >>
  rpt strip_tac >>
  first_x_assum match_mp_tac >> metis_tac[]
QED

Theorem SUM_GENLIST_SUC:
  SUM (GENLIST f (SUC n)) = f n + SUM (GENLIST f n)
Proof
  fs [GENLIST,SNOC_APPEND,SUM_APPEND]
QED

Theorem SUM_GENLIST_LESS_EQ:
  !n m f. n <= m ==> SUM (GENLIST f n) <= SUM (GENLIST f m)
Proof
  Induct \\ Cases_on `m` \\ fs [GENLIST_CONS]
QED

Theorem tailrec_POSTd:
    !p env fv xv H Q.
      nsLookup env.c (Short «Inr») = SOME (1,inr) /\ same_type inr inl /\
      nsLookup env.c (Short «Inl») = SOME (1,inl) /\ inr <> inl /\
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
      app p (some_tailrec_clos env) [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [some_tailrec_clos_def,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,evaluate_def,PULL_EXISTS,
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
                 nsBind «x» (vs i)
                   (nsBind «f» fv
                      (build_rec_env ^tailrec_clos env env.v)))`
  \\ `(env with v :=
                 nsBind «x» (vs 0)
                   (nsBind «f» fv
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
     (simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ metis_tac [])
    \\ simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once evaluate_def])
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
    \\ ntac 3 (simp [Once evaluate_def])
    \\ fs [astTheory.pat_bindings_def]
    \\ fs [semanticPrimitivesTheory.pmatch_def,can_pmatch_all_def,same_ctor_def,same_type_def]
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ ntac 3 (simp [Once evaluate_def])
    \\ simp [Once evaluate_def]
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once evaluate_def]
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
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `ck` strip_assume_tac) \\ fs []
QED

Theorem app_opapp_intro:
  !body f args env x arg1v fv argsv arg1 arg2 arg1v' arg2v H P.
  (!st:'ffi semanticPrimitives$state.
    evaluate st (env with v := nsBind x arg1v env.v) [f] = (st,Rval [fv])) /\
  (!st:'ffi semanticPrimitives$state.
    evaluate st (env with v := nsBind x arg1v env.v) [arg1] = (st,Rval [arg1v'])) /\
  (!st:'ffi semanticPrimitives$state.
    evaluate st (env with v := nsBind x arg1v env.v) [arg2] = (st,Rval [arg2v])) /\
  app p fv [arg1v';arg2v] H P
  ==>
  app (p:'ffi ffi_proj)
      (Closure env x (App Opapp [App Opapp [f; arg1]; arg2])) [arg1v] H P
Proof
  rpt strip_tac >>
  fs[cfAppTheory.app_def,cfAppTheory.app_basic_def] >>
  rw[] >> rename1 `SPLIT(st2heap p st) (h_i,h_k)` >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  simp[do_opapp_def] >>
  fs[POSTv_def,POST_def] >>
  every_case_tac >> fs[SEP_CLAUSES,set_sepTheory.SEP_F_def] >>
  fs[SEP_EXISTS_THM,cond_STAR] >>
  fs[evaluate_to_heap_def] >> rveq >>
  imp_res_tac SPLIT_of_SPLIT3_2u3 >>
  first_x_assum drule >>
  disch_then drule >> strip_tac >>
  every_case_tac >> fs[] >>
  TRY(
    rename1 `lprefix_lub` >>
    rename1 `SPLIT3 heap (h1,h2 ∪ h3,h4)` >>
    `SPLIT3 heap (h1,h2,h3 ∪ h4)`
      by(fs[SPLIT3_def] >> rveq >> fs[] >> metis_tac[DISJOINT_SYM,UNION_COMM,UNION_ASSOC]) >>
    asm_exists_tac >> fs[] >>
    asm_exists_tac >> fs[] >>
    conj_tac >-
      (fs[evaluate_ck_def,evaluate_def] >>
       rw[evaluateTheory.dec_clock_def] >>
       drule evaluatePropsTheory.evaluate_set_clock >>
       disch_then(qspec_then `0` mp_tac) >>
       simp[] >> strip_tac >>
       rename1 `evaluate (_ with clock := ck2)` >>
       Cases_on `ck2 < ck1` >-
         (drule evaluatePropsTheory.evaluate_minimal_clock >>
          disch_then(qspec_then `ck2` mp_tac) >>
          simp[] >> strip_tac >> simp[]) >>
       fs[LESS_EQ] >> fs[LESS_EQ_EXISTS] >>
       drule evaluatePropsTheory.evaluate_add_to_clock >> simp[] >>
       disch_then kall_tac >> rw[]) >>
    ho_match_mp_tac(GEN_ALL lprefix_lub_skip) >>
    fs[evaluate_ck_def] >>
    drule evaluatePropsTheory.evaluate_set_clock >>
    disch_then(qspec_then `0` mp_tac) >>
    simp[] >>
    strip_tac >>
    rename1 `evaluate (_ with clock := ack1)` >>
    qexists_tac `$+ (ack1 + 2)` >>
    conj_tac >-
      (rw[evaluate_ck_def,LPREFIX_fromList,from_toList] >>
       qmatch_goalsub_abbrev_tac `evaluate a1 a2 a3` >>
       Q.ISPECL_THEN
         [`a1`,`a2`,`a3`]
         assume_tac
         (CONJUNCT1 evaluatePropsTheory.evaluate_add_to_clock_io_events_mono) >>
       fs[evaluatePropsTheory.io_events_mono_def,Abbr `a1`]) >>
    conj_tac >- simp[] >>
    fs[evaluate_def,evaluateTheory.dec_clock_def] >>
    drule evaluatePropsTheory.evaluate_add_to_clock >>
    fs[]) >>
  rename1 `SPLIT3 heap (h1,h2 ∪ h3,h4)` >>
  `SPLIT3 heap (h1,h2,h3 ∪ h4)`
    by(fs[SPLIT3_def] >> rveq >> fs[] >> metis_tac[DISJOINT_SYM,UNION_COMM,UNION_ASSOC]) >>
  asm_exists_tac >> fs[] >>
  asm_exists_tac >> fs[] >>
  simp[evaluate_ck_def,evaluate_def] >>
  Q.REFINE_EXISTS_TAC `SUC _` >>
  simp[evaluateTheory.dec_clock_def] >>
  rename1 `evaluate_ck ck1 _ _ [exp] = _` >>
  fs[evaluate_ck_def] >>
  qpat_x_assum `evaluate (_ with clock := ck1) _ [exp] = _` assume_tac >>
  drule evaluatePropsTheory.evaluate_set_clock >>
  disch_then(qspec_then `0` mp_tac) >> simp[] >>
  strip_tac >>
  rename1 `evaluate (_ with clock := ck2) _ [exp] = _` >>
  drule evaluatePropsTheory.evaluate_add_to_clock >>
  simp[] >> strip_tac >>
  Q.REFINE_EXISTS_TAC `ck2 + extra` >>
  simp[] >>
  Q.REFINE_EXISTS_TAC `SUC _` >>
  simp[] >>
  metis_tac[]
QED

Theorem IMP_app_POSTd_old:
    mk_stepfun_closure env fname farg fbody = SOME stepv /\
    nsLookup env.c (Short «Inr») = SOME (1,TypeStamp «Inr» 4) /\
    nsLookup env.c (Short «Inl») = SOME (1,TypeStamp «Inl» 4) /\
    do_con_check env.c (SOME (Short «Inr»)) 1 ∧
    (∀v. build_conv env.c (SOME (Short «Inr»)) [v] =
         SOME (Conv (SOME (TypeStamp «Inr» 4)) [v])) ∧
    do_con_check env.c (SOME (Short «Inl»)) 1 ∧
    (∀v. build_conv env.c (SOME (Short «Inl»)) [v] =
         SOME (Conv (SOME (TypeStamp «Inl» 4)) [v])) ∧ fname ≠ farg ∧
    (∃Hs events vs io.
         vs 0 = xv ∧ H ==>> Hs 0 * one (FFI_full (events 0)) ∧
         (∀i.
              app p stepv [vs i] (Hs i * one (FFI_full (events i)))
                (POSTv v'.
                     &(v' = Conv (SOME (TypeStamp «Inl» 4))
                              [vs (SUC i)]) *
                   Hs (SUC i) * one (FFI_full (events (SUC i))))) ∧
         lprefix_lub (IMAGE (fromList ∘ events) univ(:num)) io ∧ Q io) ⇒
    app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)
Proof
  strip_tac
  \\ match_mp_tac mk_tailrec_closure_sound \\ fs []
  \\ fs [mk_tailrec_closure_def]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ match_mp_tac app_opapp_intro
  \\ fs [evaluate_def,build_rec_env_def]
  \\ fs [GSYM some_tailrec_clos_def]
  \\ match_mp_tac (GEN_ALL tailrec_POSTd) \\ fs [same_type_def]
  \\ qexists_tac `\i. Hs i * one (FFI_full (events i))`
  \\ qexists_tac `events`
  \\ qexists_tac `vs`
  \\ qexists_tac `io`
  \\ fs [] \\ conj_tac
  THEN1 (rw [] \\ qexists_tac `Hs i` \\ fs [])
  \\ rw [] \\ fs [STAR_ASSOC]
QED


(* -- repeat -- *)

val repeat_clos = process_topdecs `
  fun repeat f x = repeat f (f x);
  ` |> rator |> rand |> rand;

val repeat_body = repeat_clos |> rator |> rand |> rand |> rand |> rand

Definition cause_type_error_def:
  cause_type_error = App (FromTo CharT IntT) [Lit(IntLit 0)]
End

Theorem evaluate[simp]:
  evaluate s env [cause_type_error] = (s,Rerr (Rabort Rtype_error))
Proof
  fs [evaluate_def,cause_type_error_def,check_type_def,
      semanticPrimitivesTheory.do_opapp_def,semanticPrimitivesTheory.do_app_def]
QED

Definition then_tyerr_def:
  then_tyerr e =
  Let NONE e cause_type_error
End

Definition make_single_app_def:
   (make_single_app fname allow_fname (Raise e) =
    do
      e <- make_single_app fname F e;
      SOME(Raise e)
    od) /\
   (make_single_app fname allow_fname (Handle e pes) =
    do
      e <- make_single_app fname F e;
      pes <- make_single_appps fname allow_fname pes;
      if allow_fname then
        SOME(Handle (then_tyerr e) pes)
      else
        SOME(Handle e pes)
    od) /\
   (make_single_app fname allow_fname (Lit l) =
    if allow_fname then
      SOME(then_tyerr(Lit l))
    else
      SOME(Lit l)) /\
   (make_single_app fname allow_fname (Con c es) =
    do
      es <- make_single_apps fname es;
      if allow_fname then
        SOME(then_tyerr(Con c es))
      else
        SOME(Con c es)
    od
   ) /\
   (make_single_app fname allow_fname (Var(Short v)) =
    if SOME v = fname then
      NONE
    else if allow_fname then
      SOME(then_tyerr(Var(Short v)))
    else
      SOME(Var(Short v))
   ) /\
   (make_single_app fname allow_fname (Var v) =
    if allow_fname then
      SOME(then_tyerr(Var v))
    else
      SOME(Var v)
   ) /\
   (make_single_app fname allow_fname (Fun x e) =
    let fname' = if SOME x = fname then
                   NONE
                 else
                   fname
    in
    do
      e <- make_single_app fname' F e;
      if allow_fname then
        SOME(then_tyerr(Fun x e))
      else
        SOME(Fun x e)
    od
   ) /\
   (make_single_app fname allow_fname (Log lop e1 e2) =
    do
      e1 <- make_single_app fname F e1;
      e2 <- make_single_app fname F e2;
      if allow_fname then
        SOME(then_tyerr(Log lop e1 e2))
      else
        SOME(Log lop e1 e2)
    od
   ) /\
   (make_single_app fname allow_fname (If e1 e2 e3) =
    do
      e1 <- make_single_app fname F e1;
      e2 <- make_single_app fname allow_fname e2;
      e3 <- make_single_app fname allow_fname e3;
      SOME(If e1 e2 e3)
    od
   ) /\
   (make_single_app fname allow_fname (Mat e pes) =
    do
      e <- make_single_app fname F e;
      pes <- make_single_appps fname allow_fname pes;
      SOME(Mat e pes)
    od
   ) /\
   (make_single_app fname allow_fname (Tannot e ty) =
    do
      e <- make_single_app fname allow_fname e;
      SOME(Tannot e ty)
    od
   ) /\
   (make_single_app fname allow_fname (Lannot e l) =
    do
      e <- make_single_app fname allow_fname e;
      SOME(Lannot e l)
    od
   ) /\
   (make_single_app fname allow_fname (Let NONE e1 e2) =
    do
      e1 <- make_single_app fname F e1;
      e2 <- make_single_app fname allow_fname e2;
      SOME(Let NONE e1 e2)
    od) /\
   (make_single_app fname allow_fname (Let (SOME x) e1 e2) =
    let fname' =
        if SOME x = fname then
          NONE
        else fname
    in
    do
      e1 <- make_single_app fname F e1;
      e2 <- make_single_app fname' allow_fname e2;
      SOME(Let (SOME x) e1 e2)
    od) /\
   (make_single_app fname allow_fname (Letrec recfuns e) =
    let fname' = if EXISTS ($= fname o SOME) (MAP FST recfuns)
                 then NONE else fname
    in
    do
      recfuns <- make_single_appr fname' recfuns;
      e <- make_single_app fname' allow_fname e;
      SOME(Letrec recfuns e)
    od) /\
   (make_single_app fname allow_fname (App op es) =
      (case dest_opapp (App op es) of
         SOME(Var(Short f),[arg]) =>
           if SOME f = fname then
             if allow_fname then
               do
                 arg <- make_single_app fname F arg;
                 SOME arg
               od
             else NONE
           else
             do
               arg <- make_single_app fname F arg;
               if allow_fname then
                 SOME(then_tyerr(App op [Var(Short f); arg]))
               else
                 SOME(App op [Var(Short f); arg])
             od
       | _ =>
         do
           es <- make_single_apps fname es;
           if allow_fname then
             SOME(then_tyerr(App op es))
           else
             SOME(App op es)
         od
      )
   ) /\
   (make_single_apps fname (e::es) =
    do
      e <- make_single_app fname F e;
      es <- make_single_apps fname es;
      SOME(e::es)
    od) /\
   (make_single_apps fname [] = SOME []) /\
   (make_single_appps fname allow_fname ((p,e)::pes) =
    let fname' = if EXISTS ($= fname o SOME) (pat_bindings p [])
                 then NONE
                 else fname
    in
    do
      e <- make_single_app fname' allow_fname e;
      pes <- make_single_appps fname allow_fname pes;
      SOME((p,e)::pes)
    od) /\
   (make_single_appps fname allow_fname [] =
    SOME []) /\
   (make_single_appr fname ((f,x,e)::recfuns) =
    let fname' = if SOME x = fname then NONE else fname
    in
    do
      e <- make_single_app fname F e;
      recfun <- make_single_appr fname recfuns;
      SOME((f,x,e)::recfuns)
    od) /\
   (make_single_appr fname [] = SOME [])
Termination
  WF_REL_TAC `inv_image $< (\x. case x of
                                 | INL (t,x,e) => exp_size e
                                 | INR (INL (t,es)) => list_size exp_size es
                                 | INR (INR (INL (t,x,pes))) =>
                                     list_size (pair_size pat_size exp_size) pes
                                 | INR (INR (INR (t,funs))) =>
       list_size (pair_size mlstring_size
                  (pair_size mlstring_size exp_size)) funs)`
  \\ rw []
  \\ gvs [Once (dest_opapp_def |> DefnBase.one_line_ify NONE)]
  \\ gvs [AllCaseEqs()]
End

val make_single_app_ind = fetch "-" "make_single_app_ind"

Definition make_stepfun_closure_def:
  make_stepfun_closure env fname farg fbody =
    do
     gbody <- make_single_app (SOME fname) T fbody;
     SOME(let benv = build_rec_env [(fname,farg,fbody)] env env.v
          in Closure (env with v := benv) farg gbody)
    od
End

Definition make_repeat_closure_def:
  (make_repeat_closure (Recclosure env [(fname,farg,fbody)] name2) =
    do
     gclosure <- make_stepfun_closure  env fname farg fbody;
     SOME(Closure (env with <| v :=
            (nsBind fname gclosure env.v) |>) farg
          (App Opapp
               [App Opapp
                  [Letrec ^repeat_clos (Var(Short «repeat»));
                   Var(Short fname)];
                Var(Short farg)]
          )
         )
    od) /\ make_repeat_closure _ = NONE
End

Theorem make_single_app_F_unchanged_gen[local]:
  (!fname allow_fname e e'. make_single_app fname allow_fname e = SOME e'
               /\ allow_fname = F ==> e = e') /\
   (!fname es es'. make_single_apps fname es = SOME es'
               ==> es = es') /\
   (!fname allow_fname pes pes'. make_single_appps fname allow_fname pes = SOME pes'
               /\ allow_fname = F ==> pes = pes') /\
   (!fname recfuns recfuns'. make_single_appr fname recfuns = SOME recfuns'
               ==> recfuns = recfuns')
Proof
  ho_match_mp_tac make_single_app_ind >>
  rw[make_single_app_def] >> fs[] >>
  every_case_tac >> fs[] >> rfs[] >>
  first_x_assum drule >> simp[] >>
  imp_res_tac dest_opapp_eq_single_IMP >>
  fs[]
QED

Theorem make_single_app_F_unchanged =
  SIMP_RULE std_ss [] make_single_app_F_unchanged_gen

Definition mk_tyerr_res_def:
  mk_tyerr_res (Rerr e) = Rerr e /\
  mk_tyerr_res r = Rerr (Rabort Rtype_error)
End

Theorem evaluate_then_tyerr[simp]:
  evaluate st env [then_tyerr e] =
  case evaluate st env [e] of (st,res) => (st,mk_tyerr_res res)
Proof
  fs[evaluate_def,then_tyerr_def]
  \\ every_case_tac \\ fs [mk_tyerr_res_def]
QED

Theorem dest_opapp_not_NIL[simp]:
  dest_opapp f <> SOME (x,[])
Proof
  Cases_on `f` \\ fs [dest_opapp_def]
  \\ rename [`App op`] \\ Cases_on `op` \\ fs [dest_opapp_def]
  \\ fs [list_case_eq,option_case_eq,pair_case_eq]
QED

Theorem make_single_appps_MAP_FST:
  !pes x b pes'.
    make_single_appps x b pes = SOME pes' ==>
    MAP FST pes = MAP FST pes'
Proof
  Induct \\ fs [make_single_app_def,FORALL_PROD]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

Theorem make_single_app_NONE_evaluate:
   (!fname allow_fname e e' ^st env.
      make_single_app fname allow_fname e = SOME e' /\ allow_fname
      /\ fname = NONE
      ==> evaluate st env [e']
                = case evaluate st env [e] of
                  (st',res) => (st', mk_tyerr_res res)) /\
   (!fname es es'.
      make_single_apps fname es = SOME es'
      ==> T) /\
   (!fname allow_fname pes pes' ^st env v err_v.
      make_single_appps fname allow_fname pes = SOME pes' /\ allow_fname
      /\ fname = NONE
      ==> evaluate_match st env v pes' err_v
                = case evaluate_match st env v pes err_v of
                  (st',res) => (st', mk_tyerr_res res)) /\
   (!fname recfuns recfuns'.
      make_single_appr fname recfuns = SOME recfuns'
      ==> T)
Proof
  ho_match_mp_tac make_single_app_ind
  \\ rpt conj_tac \\ simp []
  \\ TRY (
    rw[make_single_app_def] \\ fs []
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs []
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ NO_TAC)
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Raise e2`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs []
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Handle _ _`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def] \\ rveq
    \\ imp_res_tac make_single_appps_MAP_FST \\ fs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`If _ _ _`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def] \\ rveq
    \\ rfs []
    \\ fs [do_if_def,bool_case_eq] \\ fs [] \\ rveq
    \\ rename [`evaluate st2`]
    \\ first_x_assum (qspecl_then [`st2`,`env`] strip_assume_tac)
    \\ first_x_assum (qspecl_then [`st2`,`env`] strip_assume_tac)
    \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Mat _ _`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def] \\ rveq
    \\ imp_res_tac make_single_appps_MAP_FST \\ fs []
    \\ rename [`evaluate_match st2`]
    \\ first_x_assum (qspecl_then [`st2`,`env`,`HD a`,`bind_exn_v`] strip_assume_tac)
    \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Let NONE _ _`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def] \\ rveq
    \\ pop_assum kall_tac
    \\ rename [`evaluate st2`]
    \\ fs [namespaceTheory.nsOptBind_def]
    \\ first_x_assum (qspecl_then [`st2`,`env`] strip_assume_tac)
    \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Let (SOME _) _ _`]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def] \\ rveq
    \\ pop_assum kall_tac
    \\ rename [`evaluate st2`]
    \\ fs [namespaceTheory.nsOptBind_def]
    \\ first_x_assum (qspecl_then
         [`st2`,`env with v := nsBind x (HD a) env.v`] strip_assume_tac)
    \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Letrec _ _`]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ CASE_TAC \\ fs [mk_tyerr_res_def] \\ rveq \\ fs [])
  THEN1
   (rw [] \\ rename [`App _ _`]
    \\ Cases_on `dest_opapp (App op es)`
    THEN1
     (fs [make_single_app_def] \\ rveq \\ fs []
      \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq)
      \\ Cases_on `?f a. x = (Var(Short f),[a])`
    \\ fs [] \\ rveq \\ fs [make_single_app_def] \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    THEN1
     (qsuff_tac `es = [Var (Short f); a]` \\ fs []
      \\ Cases_on `op` \\ fs [dest_opapp_def,list_case_eq,option_case_eq]
      \\ fs [pair_case_eq] \\ rveq \\ fs [])
    \\ Cases_on `x` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ Cases_on `i` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [list_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq)
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`(p,_)::_`]
    \\ CASE_TAC \\ fs []
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def]
    \\ CASE_TAC \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def]
    \\ CASE_TAC \\ fs [] \\ rveq \\ fs [mk_tyerr_res_def])
  \\ fs[evaluate_def,mk_tyerr_res_def,make_single_app_def]
QED

val make_single_app_NONE_evaluate_exp =
  make_single_app_NONE_evaluate |> CONJUNCT1 |> SIMP_RULE std_ss [];

Definition part_evaluates_to_def:
  part_evaluates_to fv env st (e1,e2) =
    case evaluate st env [e1] of
      (st',Rval v1) =>
        (?st'' res. evaluate st env [e2] = (st'',res) /\
            case do_opapp [fv; HD v1] of
              SOME(env',e3) =>
                 if st'.clock = 0 then st'' = st' /\ res = Rerr(Rabort(Rtimeout_error))
                 else
                   evaluate (dec_clock st') env' [e3] = (st'',res)
            | NONE => res = Rerr (Rabort Rtype_error))
     | (st',Rerr (Rabort Rtype_error)) =>
         (?res. evaluate st env [e2] = (st',res))
     | (st',Rerr err) => evaluate st env [e2] = (st',Rerr err)
End

Definition part_evaluates_to_match_def:
  part_evaluates_to_match fv mv err_v env st (pr1,pr2) =
    case evaluate_match st env mv pr1 err_v of
      (st',Rval v1) =>
        (?st'' res. evaluate_match st env mv pr2 err_v = (st'',res) /\
            case do_opapp [fv; HD v1] of
                SOME(env',e3) =>
                  if st'.clock = 0 then
                    (st'' = st' /\ res = Rerr(Rabort(Rtimeout_error)))
                  else
                    evaluate (dec_clock st') env' [e3] = (st'',res)
              | NONE => res = Rerr (Rabort Rtype_error))
     | (st',Rerr (Rabort Rtype_error)) =>
         (?res. evaluate_match st env mv pr2 err_v = (st',res))
     | (st',Rerr err) => evaluate_match st env mv pr2 err_v = (st',Rerr err)
End

Theorem make_single_app_SOME_evaluate:
   (!fname allow_fname e e' ^st env f fv.
      make_single_app fname allow_fname e = SOME e' /\ allow_fname
      /\ fname = SOME f /\ nsLookup env.v (Short f) = SOME fv
      ==> part_evaluates_to fv env st (e',e)) /\
   (!fname es es'.
      make_single_apps fname es = SOME es'
      ==> T) /\
   (!fname allow_fname pes pes' ^st env v err_v f fv.
      make_single_appps fname allow_fname pes = SOME pes' /\ allow_fname
      /\ fname = SOME f /\ nsLookup env.v (Short f) = SOME fv
      ==> part_evaluates_to_match fv v err_v env st (pes',pes)) /\
   (!fname recfuns recfuns'.
      make_single_appr fname recfuns = SOME recfuns'
      ==> T)
Proof
  ho_match_mp_tac make_single_app_ind
  \\ rpt conj_tac \\ simp []
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Raise e2`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ fs []
    \\ fs [part_evaluates_to_def]
    \\ CASE_TAC \\ fs []
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ every_case_tac \\ fs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Handle _ _`]
    \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ CASE_TAC \\ fs []
    \\ Cases_on `r` \\ fs [mk_tyerr_res_def] \\ rfs []
    \\ reverse CASE_TAC \\ fs []
    THEN1 (every_case_tac \\ fs [])
    \\ imp_res_tac make_single_appps_MAP_FST \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum drule
    \\ rename [`evaluate_match st2`]
    \\ disch_then (qspecl_then [`st2`,`a`,`a`] strip_assume_tac)
    \\ fs [part_evaluates_to_match_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Lit _`]
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Con _ _`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ IF_CASES_TAC \\ fs [mk_tyerr_res_def]
    \\ CASE_TAC \\ fs []
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def]
    THEN1 (every_case_tac \\ fs [])
    \\ CASE_TAC \\ fs [mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Var _`]
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Var _`]
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Fun _ _`]
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Log _ _ _`]
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ CASE_TAC \\ fs []
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def]
    THEN1 (every_case_tac \\ fs [])
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ reverse CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ Cases_on `r` \\ fs [mk_tyerr_res_def]
    \\ every_case_tac \\ fs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`If _ _ _`] \\ rfs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ res_tac
    \\ CASE_TAC \\ fs []
    \\ reverse (Cases_on `r`) \\ fs []
    THEN1 (every_case_tac \\ fs [])
    \\ fs [do_if_def]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Mat _ _`]
    \\ rveq \\ fs [] \\ rfs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ res_tac
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ CASE_TAC \\ fs []
    \\ reverse (Cases_on `r`) \\ fs [mk_tyerr_res_def] \\ rfs []
    THEN1 (every_case_tac \\ fs [])
    \\ imp_res_tac make_single_appps_MAP_FST \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ rename [`evaluate_match st2`]
    \\ reverse CASE_TAC \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`st2`,`HD a`,`bind_exn_v`] strip_assume_tac)
    \\ fs [part_evaluates_to_match_def] \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Tannot _ _`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Lannot _ _`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Let NONE _`]
    \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ rfs []
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ CASE_TAC \\ fs []
    \\ reverse (Cases_on `r`) \\ fs [mk_tyerr_res_def] \\ rfs []
    THEN1 (every_case_tac \\ fs [])
    \\ rename [`evaluate st2`]
    \\ fs [namespaceTheory.nsOptBind_def]
    \\ first_x_assum (qspecl_then [`st2`,`env`,`fv`] strip_assume_tac) \\ rfs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Let (SOME _) _`]
    \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ rfs []
    \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    \\ CASE_TAC \\ fs []
    THEN1
     (reverse (Cases_on `r`) \\ fs [mk_tyerr_res_def] \\ rfs []
      THEN1 (every_case_tac \\ fs [])
      \\ rename [`evaluate st2`]
      \\ fs [namespaceTheory.nsOptBind_def]
      \\ drule make_single_app_NONE_evaluate_exp \\ fs []
      \\ CASE_TAC \\ Cases_on `r` \\ fs [mk_tyerr_res_def]
      \\ rename [`Rerr err`]
      \\ every_case_tac \\ fs [])
    THEN1
     (reverse (Cases_on `r`) \\ fs [mk_tyerr_res_def] \\ rfs []
      THEN1 (every_case_tac \\ fs [])
      \\ rename [`evaluate st2`]
      \\ fs [namespaceTheory.nsOptBind_def]))
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`Letrec _`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ rfs []
    \\ rveq \\ fs [] \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    THEN1
     (IF_CASES_TAC \\ fs []
      \\ drule make_single_app_NONE_evaluate_exp \\ fs []
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ Cases_on `r` \\ fs [mk_tyerr_res_def]
      \\ every_case_tac \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate st env1`
    \\ first_x_assum (qspecl_then [`st`,`env1`,`fv`] mp_tac)
    \\ reverse impl_tac THEN1 fs []
    \\ fs [Abbr`env1`]
    \\ qpat_x_assum `_ = SOME fv` (fn th => fs [GSYM th])
    \\ match_mp_tac nsLookup_build_rec_env_fresh
    \\ last_x_assum mp_tac
    \\ qid_spec_tac `recfuns` \\ Induct \\ fs [])
  THEN1
   (rw [] \\ rename [`App _ _`]
    \\ Cases_on `dest_opapp (App op es)`
    THEN1
     (fs [make_single_app_def] \\ rveq \\ fs []
      \\ fs [part_evaluates_to_def] \\ CASE_TAC \\ fs []
      \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
      \\ Cases_on `r` \\ fs [mk_tyerr_res_def]
      \\ every_case_tac \\ fs [])
    \\ Cases_on `?a fn. x = (Var (Short fn),[a])`
    THEN1
     (fs [] \\ rveq \\ fs [make_single_app_def] \\ rveq \\ fs []
      \\ Cases_on `op` \\ fs [dest_opapp_def,list_case_eq,option_case_eq,pair_case_eq]
      \\ rveq \\ fs [] \\ Cases_on `fn = f` \\ fs []
      \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
      THEN1
       (fs [part_evaluates_to_def]
        \\ fs[evaluate_def,mk_tyerr_res_def]
        \\ CASE_TAC \\ fs []
        \\ reverse (Cases_on `r`) \\ fs []
        THEN1 (every_case_tac \\ fs [])
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs []
        \\ metis_tac [PAIR])
      \\ fs [part_evaluates_to_def]
      \\ fs[evaluate_def,mk_tyerr_res_def]
      \\ Cases_on `evaluate st env [a]` \\ fs []
      \\ reverse (Cases_on `r`) \\ fs [mk_tyerr_res_def]
      THEN1 (every_case_tac \\ fs [])
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ CASE_TAC \\ fs [mk_tyerr_res_def]
      \\ rename [`mk_tyerr_res r2`] \\ Cases_on `r2` \\ fs [mk_tyerr_res_def]
      \\ every_case_tac \\ fs [])
    \\ fs [] \\ rveq \\ fs [make_single_app_def] \\ rveq \\ fs []
    \\ PairCases_on `x` \\ Cases_on `x0` \\ fs []
    \\ rveq \\ fs []
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq
    \\ fs [part_evaluates_to_def]
    \\ CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ CASE_TAC \\ fs [mk_tyerr_res_def]
    \\ TRY
     (Cases_on `i` \\ fs [list_case_eq]
      \\ rveq \\ fs [pair_case_eq]
      \\ rveq \\ fs [pair_case_eq])
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ fs []
    \\ fs [pair_case_eq] \\ rveq \\ fs []
    \\ rename [`mk_tyerr_res r2`] \\ Cases_on `r2` \\ fs [mk_tyerr_res_def]
    \\ every_case_tac \\ fs [])
  THEN1
   (rw[make_single_app_def] \\ fs [] \\ rename [`(p,_)::_`]
    \\ imp_res_tac make_single_app_F_unchanged \\ fs [] \\ rveq \\ rfs []
    \\ rveq \\ fs [] \\ fs [part_evaluates_to_def]
    \\ fs[evaluate_def,mk_tyerr_res_def]
    THEN1
     (drule make_single_app_NONE_evaluate_exp
      \\ simp [part_evaluates_to_match_def,evaluate_def]
      \\ reverse IF_CASES_TAC \\ fs []
      \\ reverse CASE_TAC \\ fs []
      THEN1
       (CASE_TAC \\ fs [mk_tyerr_res_def]
        \\ Cases_on `r` \\ fs [mk_tyerr_res_def]
        \\ every_case_tac \\ fs [])
      \\ res_tac \\ fs [part_evaluates_to_match_def])
    \\ last_x_assum drule \\ strip_tac
    \\ simp [part_evaluates_to_match_def,evaluate_def]
    \\ reverse IF_CASES_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    THEN1 (fs [part_evaluates_to_match_def,evaluate_def])
    \\ qmatch_goalsub_abbrev_tac `evaluate st env1`
    \\ last_x_assum (qspecl_then [`st`,`env1`,`fv`] mp_tac)
    \\ reverse impl_tac THEN1 fs []
    \\ fs [Abbr`env1`]
    \\ fs [ml_progTheory.nsLookup_nsAppend_Short,option_case_eq]
    \\ disj1_tac
    \\ match_mp_tac nsLookup_alist_to_ns_fresh
    \\ imp_res_tac semanticPrimitivesPropsTheory.pmatch_extend
    \\ rveq \\ fs []
    \\ last_x_assum mp_tac
    \\ qspec_tac (`pat_bindings p []`,`xs`)
    \\ Induct \\ fs [])
  \\ fs [make_single_app_def,part_evaluates_to_match_def]
  \\ fs[evaluate_def,mk_tyerr_res_def]
QED

val make_single_app_SOME_evaluate_exp =
  make_single_app_SOME_evaluate |> CONJUNCT1 |> SIMP_RULE std_ss [];

Theorem make_single_app_unroll_lemma[local]:
  !fname fbody gbody ^st st' ck1 env farg ck2 x v.
    make_single_app (SOME fname) T fbody = SOME gbody /\
    evaluate (^st with clock := ck1)
               (env with
                v :=
                  nsBind farg x
                    (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                       env.v)) [gbody] =
             (st' with clock := 0,Rval [v]) /\
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
            [fbody]
Proof
  rpt strip_tac >>
  drule make_single_app_SOME_evaluate_exp >>
  disch_then(qspecl_then [`st with clock := ck1 + ck2 + 1`,
    `env with v := nsBind farg x
       (nsBind fname (Recclosure env [(fname,farg,fbody)] fname) env.v)`] mp_tac) >>
  simp[part_evaluates_to_def] >>
  drule evaluatePropsTheory.evaluate_add_to_clock >>
  disch_then(qspec_then `ck2 + 1` mp_tac) >>
  simp[evaluateTheory.dec_clock_def,do_opapp_def,
       Once find_recfun_def] >>
  rpt strip_tac >>
  simp[] >> fs[build_rec_env_def]
QED

Theorem evaluate_repeat_diverge_lemma[local]:
  !ck fbody gbody env env' ^st farg x v fname.
   make_single_app (SOME fname) T fbody = SOME gbody /\
   fname <> farg /\
   (!ck. ?st'. evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^repeat_clos
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
     [^repeat_body] = (st',Rerr(Rabort Rtimeout_error))) ==>
   ?st' res2.
       evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort Rtimeout_error))
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once evaluate_def]) >>
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
                 [gbody]) <> Rerr(Rabort(Rtimeout_error))`)
  THEN1
    (fs[] >>
     first_x_assum(qspec_then `ck` assume_tac) >>
     Cases_on `evaluate (st with clock := ck)
              (env with
               v :=
                 nsBind farg v
                   (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                      env.v)) [gbody]` >>
     fs[] >> rveq >>
     drule make_single_app_SOME_evaluate_exp >>
     disch_then(qspecl_then [`st with clock := ck`,`env with v :=
              nsBind farg v
                (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                   env.v)`] mp_tac) >>
     fs [] >> simp[part_evaluates_to_def]) >>
   fs[] >>
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
   drule make_single_app_SOME_evaluate_exp >>
   disch_then(qspecl_then [`st with clock := ck1`,`env with v :=
            nsBind farg v
              (nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                 env.v)`] mp_tac) >> fs [] >>
   simp[part_evaluates_to_def] >>
   strip_tac >>
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
   imp_res_tac evaluatePropsTheory.evaluate_length >>
   fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
   rveq >> fs[] >> rveq >>
   ntac 2 (simp[Once evaluate_def]) >>
   simp[namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute] >>
   simp[Once evaluate_def] >>
   imp_res_tac build_conv_check_IMP_nsLookup >>
   simp[astTheory.pat_bindings_def,semanticPrimitivesTheory.pmatch_def,
        semanticPrimitivesTheory.same_type_def,
        semanticPrimitivesTheory.same_ctor_def] >>
   ntac 4 (simp[Once evaluate_def]) >>
   simp[do_opapp_def,Once find_recfun_def] >>
   simp[GSYM LEFT_EXISTS_IMP_THM] >>
   Q.REFINE_EXISTS_TAC `extra + 2` >>
   simp[LEFT_EXISTS_IMP_THM] >>
   simp[evaluateTheory.dec_clock_def] >>
   simp[Once evaluate_def] >>
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
   drule make_single_app_unroll_lemma >>
   disch_then drule >>
   simp[] >>
   disch_then kall_tac >>
   strip_tac >>
   last_x_assum(qspec_then `ck2` mp_tac) >>
   impl_tac >- metis_tac[ADD_SYM,ADD_ASSOC] >>
   disch_then drule >>
   disch_then(qspecl_then [`aenv`,`aenv'`,`ast`,`farg`,`argx`,`argv`] mp_tac) >>
   simp[] >> simp[build_rec_env_def]
QED

Theorem evaluate_repeat_div_ind_lemma[local]:
  !ck fbody gbody env env' ^st farg x v fname st' res.
   make_single_app (SOME fname) T fbody = SOME gbody /\
   fname <> farg /\
   ck > 0 /\
   evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^repeat_clos
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
     [^repeat_body] = (st',Rerr(Rabort(Rtimeout_error))) ==>
   ∃ck'.
       evaluate_ck ck' ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort Rtimeout_error))
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  pop_assum mp_tac >>
  ntac 5 (simp[Once evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  drule make_single_app_SOME_evaluate_exp >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  disch_then(qspecl_then [`ast`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[ml_progTheory.nsLookup_nsBind_compute] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,part_evaluates_to_def] >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  Cases_on `evaluate ast aenv [gbody]` >>
  reverse(Cases_on `r`) >-
    ((* Rerror *)
     fs[] >> rpt strip_tac >> rveq >>
     qexists_tac `ast.clock` >>
     simp[Abbr`ast`] \\ fs []) >>
  fs [] >> simp[] >>
  strip_tac >>
  imp_res_tac evaluatePropsTheory.evaluate_length >>
  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
  rveq >>
  fs[] >> rveq >>
  ntac 2(simp[Once evaluate_def]) >>
  simp[namespaceTheory.nsOptBind_def] >>
  simp[Once evaluate_def] >>
  simp[astTheory.pat_bindings_def] >>
  simp[semanticPrimitivesTheory.pmatch_def] >>
  imp_res_tac build_conv_check_IMP_nsLookup >>
  simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def] >>
  simp[Once evaluate_def] >>
  simp[astTheory.pat_bindings_def] >>
  simp[semanticPrimitivesTheory.pmatch_def] >>
  simp[evaluate_def] >>
  simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
  IF_CASES_TAC >-
    (strip_tac >> fs[Abbr `ast`,do_opapp_def,Once find_recfun_def] >>
     asm_exists_tac >> simp[]) >>
  simp[Once evaluate_def] >>
  qpat_x_assum `evaluate _ _ [gbody] = _` assume_tac >>
  drule evaluatePropsTheory.evaluate_set_clock >>
  simp[] >>
  disch_then(qspec_then `0` strip_assume_tac) >>
  drule make_single_app_SOME_evaluate_exp >>
  disch_then(qspecl_then [`ast with clock := ck1`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,part_evaluates_to_def] >>
  simp[do_opapp_def,Once find_recfun_def] >> strip_tac >>
  rfs [] >>
  IF_CASES_TAC >-
    (fs[evaluateTheory.dec_clock_def] >>
     strip_tac >> rveq >>
     qexists_tac `ck1` >>
     simp[semanticPrimitivesTheory.state_component_equality]) >>
  simp[evaluateTheory.dec_clock_def] >>
  qmatch_goalsub_abbrev_tac `_ with clock := ack` >>
  Cases_on `ack = 0` >-
    (rveq >> simp[evaluate_def,do_opapp_def] >>
     strip_tac >> rveq >> qexists_tac `ck1` >>
     simp[semanticPrimitivesTheory.state_component_equality]) >>
  `ack < ck`
    by(imp_res_tac evaluate_clock >> fs[Abbr `ack`]) >>
  strip_tac >>
  drule make_single_app_unroll_lemma >> simp[] >>
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
  asm_exists_tac >> first_x_assum ACCEPT_TAC
QED

Theorem evaluate_repeat_div_ind_lemma2[local]:
  !ck fbody gbody env env' ^st farg x v fname st' res.
   make_single_app (SOME fname) T fbody = SOME gbody /\
   fname <> farg /\
   evaluate_ck ck ^st
         (env with
          v := nsBind farg v (build_rec_env [(fname,farg,fbody)] env env.v))
         [fbody] = (st',Rerr(Rabort(Rtimeout_error))) ==>
   ?ck res2. evaluate_ck ck ^st
     (env with
      v :=
        nsBind «x» v
          (nsBind «f»
             (Closure
                (env with
                 v :=
                   nsBind fname (Recclosure env [(fname,farg,fbody)] fname)
                     env.v) farg gbody)
             (build_rec_env
                ^repeat_clos
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
     [^repeat_body] = (st',Rerr(Rabort res2)) /\
     (res2 <> Rtimeout_error ==> res2 = Rtype_error)
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[evaluate_ck_def] >>
  Q.REFINE_EXISTS_TAC `ck' + 1` >>
  ntac 5 (simp[Once evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,semanticPrimitivesTheory.do_opapp_def,
       Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[evaluateTheory.dec_clock_def] >>
  pop_assum mp_tac >>
  drule make_single_app_SOME_evaluate_exp >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  disch_then(qspecl_then [`ast`,`aenv`] mp_tac) >>
  unabbrev_all_tac >> simp[ml_progTheory.nsLookup_nsBind_compute] >>
  simp[semanticPrimitivesTheory.build_rec_env_def,part_evaluates_to_def] >>
  qmatch_goalsub_abbrev_tac `evaluate ast aenv` >>
  ntac 2 strip_tac >> fs [] >>
  Cases_on `evaluate ast aenv [gbody]` >> fs [] >>
  reverse(Cases_on `r`) >-
    ((* Rerror *)
     fs[] >> rpt strip_tac >> rveq >>
     qexists_tac `ast.clock` >>
     simp[Abbr`ast`] >>
     Cases_on `e` >> fs [] >>
     Cases_on `a` >> fs []) >>
  fs [] >>
  imp_res_tac evaluatePropsTheory.evaluate_length >>
  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
  rveq >>
  qpat_x_assum `evaluate _ _ [gbody] = _` assume_tac >>
  drule evaluatePropsTheory.evaluate_set_clock >>
  disch_then(qspec_then `0` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  Q.REFINE_EXISTS_TAC `ck1 + extra` >>
  qunabbrev_tac `ast` >>
  drule evaluatePropsTheory.evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  ntac 2(simp[Once evaluate_def]) >>
  simp[namespaceTheory.nsOptBind_def] >>
  simp[Once evaluate_def] >>
  Q.REFINE_EXISTS_TAC `extra + 2` >>
  simp[Once evaluate_def] >>
  simp[evaluate_def] >>
  simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[Once evaluate_def] >>
  simp[evaluateTheory.dec_clock_def] >> fs [] >>
  fs [EVAL ``do_opapp [Recclosure env [(fname,farg,fbody)] fname; e1]``] >>
  Cases_on `q.clock = 0` \\ fs [] \\ rveq \\ fs [] >-
   (qexists_tac `0` \\ fs []
    \\ ntac 5 (simp[Once evaluate_def])
    \\ fs [do_opapp_def,evaluateTheory.dec_clock_def]
    \\ fs [state_component_equality]) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  fs[evaluateTheory.dec_clock_def,build_rec_env_def] >>
  HINT_EXISTS_TAC >> simp[] >>
  imp_res_tac evaluate_clock >> fs[]
QED

Theorem make_repeat_closure_sound_basic:
   !fv env .
     make_repeat_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
     /\ fname <> farg
     /\ app_basic (p:'ffi ffi_proj) fv x H ($POSTd Q)
     ==> app_basic p (Recclosure env [(fname,farg,fbody)] fname) x H ($POSTd Q)
Proof
  rw[make_repeat_closure_def,make_stepfun_closure_def,app_basic_def] >>
  first_x_assum drule >>
  disch_then drule >>
  strip_tac >>
  asm_exists_tac >> fs[semanticPrimitivesTheory.do_opapp_def] >>
  simp[semanticPrimitivesTheory.find_recfun_def] >>
  asm_exists_tac >>
  asm_exists_tac >>
  simp[] >> rveq >> Cases_on `r` >>
  fs [POSTd_def,cond_def] >> rveq \\ fs [] >>
  fs[evaluate_to_heap_def] >>
  rename1 `lprefix_lub` >>
  conj_asm1_tac >-
    (strip_tac >>
     qpat_x_assum `!ck. ?st. _` mp_tac >>
     simp[GSYM LEFT_EXISTS_IMP_THM] >>
     Q.REFINE_EXISTS_TAC `ck1 + 2` >>
     simp[LEFT_EXISTS_IMP_THM] >>
     simp[evaluate_ck_def] >>
     ntac 8 (simp[Once evaluate_def]) >>
     simp[build_rec_env_def,ml_progTheory.nsLookup_nsBind_compute,do_opapp_def,
          Once find_recfun_def] >>
     simp[Once evaluateTheory.dec_clock_def] >>
     simp[Once evaluate_def] >>
     simp[evaluateTheory.dec_clock_def] >>
     strip_tac >>
     match_mp_tac (SIMP_RULE (srw_ss())
                     [semanticPrimitivesTheory.build_rec_env_def,
                      evaluate_ck_def]
                     evaluate_repeat_diverge_lemma) >>
     asm_exists_tac >> simp[] >>
     metis_tac []) >>
  qmatch_asmsub_abbrev_tac `lprefix_lub (IMAGE f _)` >>
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
     ntac 8 (simp[Once evaluate_def]) >>
     simp[semanticPrimitivesTheory.build_rec_env_def,
          do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
     simp[Once evaluate_def] >>
     drule evaluate_repeat_div_ind_lemma2 >>
     rpt(disch_then drule) >>
     disch_then(qspec_then `ck` mp_tac) >> simp[Abbr `aexp`] >>
     unabbrev_all_tac >>
     qpat_x_assum `!ck. ?st. evaluate_ck _ _ _ _ = _`(qspec_then `ck` assume_tac) >>
     fs[] >> rveq >> disch_then drule >>
     simp[evaluate_ck_def,build_rec_env_def] >>
     metis_tac[FST]) >>
  pop_assum(qspecl_then [`l`,`\ck. ck + 3`] mp_tac) >>
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
  ntac 8 (simp[Once evaluate_def]) >>
  simp[semanticPrimitivesTheory.build_rec_env_def,
       do_opapp_def, Once find_recfun_def,evaluateTheory.dec_clock_def] >>
  simp[Once evaluate_def] >>
  strip_tac >>
  drule evaluate_repeat_div_ind_lemma >>
  rpt(disch_then drule) >>
  disch_then(qspec_then `i + 1` mp_tac) >> simp[] >>
  simp[build_rec_env_def] >>
  simp[evaluate_ck_def] >>
  disch_then drule >>
  strip_tac >>
  rename1 `evaluate (_ with clock := newclock)` >>
  qexists_tac `newclock` >>
  simp[]
QED

Theorem make_repeat_closure_sound:
  !fv env .
    make_repeat_closure(Recclosure env [(fname,farg,fbody)] fname) = SOME fv
    /\ fname <> farg
    /\ app p fv [x] H ($POSTd Q)
    ==> app p (Recclosure env [(fname,farg,fbody)] fname) [x] H ($POSTd Q)
Proof
  metis_tac[make_repeat_closure_sound_basic,app_def]
QED

Definition some_repeat_clos_def:
  some_repeat_clos env = Recclosure env ^repeat_clos «repeat»
End

fun rename_conv s tm =
  let
    val (v,body) = dest_abs tm
  in ALPHA_CONV (mk_var(s,type_of v)) tm end;

val let_a = repeat_clos |> rator |> rand |> rand |> rand |> rand

Theorem repeat_POSTd0:
    !p env fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p (some_repeat_clos env) [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [some_repeat_clos_def,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,evaluate_def,PULL_EXISTS,
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
  \\ qabbrev_tac `nth_env = \i. (env with
               v :=
                 nsBind «x» (vs i)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v)))`
  \\ `(env with v :=
                 nsBind «x» (vs 0)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v))) = nth_env 0`
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
     (simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ metis_tac [])
    \\ simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once evaluate_def])
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
    \\ ntac 3 (simp [Once evaluate_def])
    \\ fs [astTheory.pat_bindings_def]
    \\ fs [semanticPrimitivesTheory.pmatch_def,same_ctor_def,same_type_def]
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ ntac 3 (simp [Once evaluate_def])
    \\ simp [Once evaluate_def]
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once evaluate_def]
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
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `ck` strip_assume_tac) \\ fs []
QED

Theorem IMP_app_POSTd:
    make_stepfun_closure env fname farg fbody = SOME stepv /\
    fname ≠ farg ∧
    (∃Hs events vs io.
         vs 0 = xv ∧ H ==>> Hs 0 * one (FFI_full (events 0)) ∧
         (∀i.
              app p stepv [vs i] (Hs i * one (FFI_full (events i)))
                (POSTv v'. &(v' = vs (SUC i)) *
                           Hs (SUC i) * one (FFI_full (events (SUC i))))) ∧
         lprefix_lub (IMAGE (fromList ∘ events) univ(:num)) io ∧ Q io) ⇒
    app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)
Proof
  strip_tac
  \\ match_mp_tac make_repeat_closure_sound \\ fs []
  \\ fs [make_repeat_closure_def]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ match_mp_tac app_opapp_intro
  \\ fs [evaluate_def,build_rec_env_def]
  \\ fs [GSYM some_repeat_clos_def]
  \\ match_mp_tac (GEN_ALL repeat_POSTd0) \\ fs []
  \\ qexists_tac `\i. Hs i * one (FFI_full (events i))`
  \\ qexists_tac `events`
  \\ qexists_tac `vs`
  \\ qexists_tac `io`
  \\ fs [] \\ conj_tac
  THEN1 (rw [] \\ qexists_tac `Hs i` \\ fs [])
  \\ rw [] \\ fs [STAR_ASSOC]
QED

(* -- FFI_part -- *)

Definition limited_parts_def:
  limited_parts ns ((proj,parts):'ffi ffi_proj) <=>
    ns = FLAT (MAP FST parts)
End

Theorem FFI_part_IN_st2heap_IMP:
  FFI_part s u ns events ∈ st2heap p st ==>
  FILTER (ffi_has_index_in ns) st.ffi.io_events = events
Proof
  strip_tac \\ fs [st2heap_def]
  THEN1 fs [store2heap_def, FFI_part_NOT_IN_store2heap_aux]
  \\ Cases_on `p` \\ fs [ffi2heap_def]
  \\ Cases_on `parts_ok st.ffi (q,r)` \\ fs []
QED

Theorem limited_FFI_part_IN_st2heap_IMP:
  limited_parts ns p ==>
  FFI_part s u ns events ∈ st2heap p st ==>
  st.ffi.io_events = events
Proof
  rpt (strip_tac)
  \\ fs [st2heap_def]
  THEN1 fs [store2heap_def, FFI_part_NOT_IN_store2heap_aux]
  \\ Cases_on `p` \\ fs [ffi2heap_def]
  \\ Cases_on `parts_ok st.ffi (q,r)` \\ fs []
  \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) EQ_SYM_EQ)
  \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) FILTER_EQ_ID)
  \\ fs [parts_ok_def, limited_parts_def]
QED

Theorem repeat_POSTd_one_FFI_part:
    !p env fv xv H Q ns.
      limited_parts ns p /\
      (?Hs events vs ss u io.
         vs 0 xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_part (ss i) u ns (events i))) /\
         (!i xv. vs i xv ==>
            (app p fv [xv] (Hs i)
                             (POSTv v'. &(vs (SUC i) v') * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p (some_repeat_clos env) [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [some_repeat_clos_def,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,evaluate_def,PULL_EXISTS,
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
  \\ `!i xv st0.
        assert_Hs i st0 /\ vs i xv ==>
        ?env exp ck st1 xv'.
          assert_Hs (i+1) st1 /\
          do_opapp [fv; xv] = SOME (env,exp) /\
          evaluate_ck ck st0 env [exp] = (st1,Rval [xv']) /\
          vs (i+1) xv' /\
          st1.clock = 0` by
   (fs [Abbr`assert_Hs`,PULL_EXISTS] \\ rpt strip_tac
    \\ first_assum drule \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac \\ fs [ADD1]
    \\ drule SPLIT_of_SPLIT3_2u3
    \\ strip_tac
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `st'' with clock := 0`
    \\ simp[st2heap_clock]
    \\ asm_exists_tac \\ simp[]
    \\ PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_set_clock
    \\ disch_then (qspec_then `0` mp_tac) \\ strip_tac \\ fs []
    \\ qexists_tac `ck1` \\ fs [cfStoreTheory.st2heap_clock])
  \\ `!x. ?ck st1 xv'. let (i,st0,xv) = x in
            assert_Hs i st0 /\ vs i xv ==>
            ?env exp.
              assert_Hs (i+1) st1 /\
              do_opapp [fv; xv] = SOME (env,exp) /\
              evaluate_ck ck st0 env [exp] = (st1,Rval [xv']) /\
              vs (i+1) xv' /\
              st1.clock = 0` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [SKOLEM_THM]))
  \\ simp []
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "clocks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "states"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "values"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "i"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarararar") (rename_conv "st0"))
  \\ strip_tac
  \\ qabbrev_tac `svpairs = (\x. states x, values x)`
  \\ qabbrev_tac `get_i = get_index (st1,xv) svpairs`
  \\ qabbrev_tac `cks = clocks o get_i`
  \\ qabbrev_tac `sts = \i.
                    if i = 0 then st1 else states (get_index (st1,xv) svpairs (i-1))`
  \\ qabbrev_tac `vls = \i.
                    if i = 0 then xv else values (get_index (st1,xv) svpairs (i-1))`
  \\ `∀i.
        ∃env exp.
            do_opapp [fv; vls i] = SOME (env,exp) ∧
            evaluate_ck (cks i) (sts i) env [exp] =
            (sts (i+1),Rval [vls (i + 1)]) ∧
            (sts (i+1)).clock = 0 ∧
            assert_Hs i (sts i) ∧ assert_Hs (i+1) (sts (i+1)) /\
            vs (i+1) (vls (i+1))` by
    (Induct THEN1
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`, Abbr`svpairs`,Abbr`vls`]
       \\ `assert_Hs 0 st1` by
         (fs [Abbr`assert_Hs`] \\ asm_exists_tac \\ fs [SEP_IMP_def])
       \\ `vs 0 xv` by simp[]
       \\ fs [] \\ once_rewrite_tac [get_index_def] \\ fs []
       \\ first_x_assum drule \\ disch_then drule \\ strip_tac \\ fs []
      )
     \\ fs [ADD1]
     \\ first_x_assum drule \\ disch_then drule
     \\ strip_tac \\ fs []
     \\ `(states (i + 1,sts (i + 1),vls(i+1))) = sts (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `(values (i + 1,sts (i + 1),vls(i+1))) = vls (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `clocks (i + 1,sts (i + 1),vls(i+1)) = cks (i+1)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ fs [])
  \\ qabbrev_tac `cks_sum = \i. SUM (GENLIST cks i) + 3 * i`
  \\ qabbrev_tac `nth_env = \i. (env with
               v :=
                 nsBind «x» (vls i)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v)))`
  \\ `(env with v :=
                 nsBind «x» (vls 0)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v))) = nth_env 0`
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
     (simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ irule limited_FFI_part_IN_st2heap_IMP
      \\ MAP_EVERY qexists_tac [`ns`, `p`, `ss i`, `u`]
      \\ metis_tac [])
    \\ simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once evaluate_def])
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
    \\ ntac 3 (simp [Once evaluate_def])
    \\ fs [astTheory.pat_bindings_def]
    \\ fs [semanticPrimitivesTheory.pmatch_def,same_ctor_def,same_type_def]
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ ntac 3 (simp [Once evaluate_def])
    \\ simp [Once evaluate_def]
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once evaluate_def]
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
    \\ `ck <= cks_sum ck` by(unabbrev_all_tac >> fs[])
    \\ first_x_assum drule
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
    \\ fs [Abbr `nth_env`,Abbr`vls`,evaluatePropsTheory.io_events_mono_def])
  THEN1
   (fs [Abbr`cks_sum`]
    \\ qsuff_tac `SUM (GENLIST cks ck) <= SUM (GENLIST cks (ck + 1))` THEN1 fs []
    \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
  \\ qpat_x_assum `lprefix_lub _ io` mp_tac
  \\ match_mp_tac (METIS_PROVE []
       ``x = y ==> lprefix_lub (IMAGE x u) io ==> lprefix_lub (IMAGE y u) io``)
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `ck` strip_assume_tac)
  \\ unabbrev_all_tac \\ fs[]
QED

Theorem IMP_app_POSTd_one_FFI_part:
    make_stepfun_closure env fname farg fbody = SOME stepv /\
    fname ≠ farg ∧
    limited_parts ns p ∧
    (∃Hs events vs ss u io.
         vs 0 xv ∧ H ==>> Hs 0 * one (FFI_part (ss 0) u ns (events 0)) ∧
         (∀i xv'.
              vs i xv' ==>
              app p stepv [xv'] (Hs i * one (FFI_part (ss i) u ns (events i)))
                (POSTv v'. &(vs (SUC i) v') *
                           Hs (SUC i) * one (FFI_part (ss (SUC i)) u ns (events (SUC i))))) ∧
         lprefix_lub (IMAGE (fromList ∘ events) univ(:num)) io ∧ Q io) ⇒
    app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)
Proof
  strip_tac
  \\ match_mp_tac make_repeat_closure_sound \\ fs []
  \\ fs [make_repeat_closure_def]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ match_mp_tac app_opapp_intro
  \\ fs [evaluate_def,build_rec_env_def]
  \\ fs [GSYM some_repeat_clos_def]
  \\ match_mp_tac (GEN_ALL repeat_POSTd_one_FFI_part) \\ fs []
  \\ qexists_tac `ns` \\ fs []
  \\ qexists_tac `\i. Hs i * one (FFI_part (ss i) u ns (events i))`
  \\ MAP_EVERY qexists_tac [`events`, `vs`, `ss`, `u`, `io`]
  \\ fs [] \\ conj_tac
  THEN1 (rw [] \\ qexists_tac `Hs i` \\ fs [])
  \\ rw [] \\ fs [STAR_ASSOC]
QED

(* -- old repeat approach -- *)

val _ = (append_prog o process_topdecs)
  `fun repeat f x = repeat f (f x);`

val st = ml_translatorLib.get_ml_prog_state ();

val repeat_v = fetch "-" "repeat_v_def"

Theorem evaluate_IMP_io_events_mono[local]:
    evaluate s e exp = (t,res) ==> io_events_mono s.ffi t.ffi
Proof
  metis_tac [evaluatePropsTheory.evaluate_io_events_mono,FST]
QED

Theorem repeat_POSTd:
    !p fv xv H Q.
      (?Hs events vs io.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         Q io)
      ==>
      app p repeat_v [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [repeat_v,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,evaluate_def,PULL_EXISTS,
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
  \\ qpat_abbrev_tac `the_env = nsBind «f» fv _`
  \\ qpat_abbrev_tac `other_env = merge_env _ _`
  \\ qabbrev_tac `nth_env = \i. (other_env with v := nsBind «x» (vs i) the_env)`
  \\ `(other_env with v := nsBind «x» (vs 0) the_env) = nth_env 0`
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
     (simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ match_mp_tac FFI_full_IN_st2heap_IMP \\ metis_tac [])
    \\ simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once evaluate_def])
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
    \\ ntac 3 (simp [Once evaluate_def])
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ ntac 3 (simp [Once evaluate_def])
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once evaluate_def]
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
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `ck` strip_assume_tac) \\ fs []
QED

Theorem repeat_POSTe:
  !(p: 'ffi ffi_proj) fv xv H Q.
    (?Hs vs j.
        vs 0 = xv /\ H ==>> Hs 0 /\
        (!i. i < j ==>
          app p fv [vs i] (Hs i) (POSTv v. &(v = vs (SUC i)) * Hs (SUC i))) /\
        app p fv [vs j] (Hs j) ($POSTe Q)) ==>
          app p repeat_v [fv; xv] H ($POSTe Q)
Proof
  rpt strip_tac
  \\ `!i. i <= j ==> app p repeat_v [fv; vs i] (Hs i) ($POSTe Q)` by (
    rpt strip_tac
    \\ Induct_on `j - i`
    THEN1 (
      rpt strip_tac
      \\ xcf "repeat" st
      \\ `i = j` by decide_tac \\ rveq
      \\ xlet `$POSTe Q` THEN1 xapp
      \\ xsimpl)
    \\ rpt strip_tac
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
  \\ xsimpl
QED

(* TODO: up-to techniques duplicated from divTheory; should go elsewhere (llistTheory?)
         other stuff can probably be moved to llistTheory, various other cf theories,
         evaluateProps etc.
*)
Inductive llist_upto:
  (llist_upto R x x) /\
  (R x y ==> llist_upto R x y) /\
  (llist_upto R x y /\ llist_upto R y z ==> llist_upto R x z) /\
  (llist_upto R x y ==> llist_upto R (LAPPEND z x) (LAPPEND z y))
End

val [llist_upto_eq,llist_upto_rel,llist_upto_trans,llist_upto_context] =
  llist_upto_rules |> SPEC_ALL |> CONJUNCTS |> map GEN_ALL
  |> curry (ListPair.map save_thm)
    ["llist_upto_eq","llist_upto_rel",
     "llist_upto_trans","llist_upto_context"]

Theorem LLIST_BISIM_UPTO:
  ∀ll1 ll2 R.
    R ll1 ll2 ∧
    (∀ll3 ll4.
      R ll3 ll4 ⇒
      ll3 = [||] ∧ ll4 = [||] ∨
      LHD ll3 = LHD ll4 ∧
      llist_upto R (THE (LTL ll3)) (THE (LTL ll4)))
  ==> ll1 = ll2
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[LLIST_BISIMULATION]
  >> qexists_tac `llist_upto R`
  >> conj_tac >- rw[llist_upto_rules]
  >> ho_match_mp_tac llist_upto_ind
  >> rpt conj_tac
  >- rw[llist_upto_rules]
  >- first_x_assum ACCEPT_TAC
  >- (rw[]
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac >- simp[]
      >> metis_tac[llist_upto_rules])
  >- (rw[llist_upto_rules]
      >> Cases_on `ll3 = [||]`
      >- (Cases_on `ll4` >> fs[llist_upto_rules])
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac
      >- (Cases_on `z` >> simp[])
      >> Cases_on `z` >- simp[]
      >> simp[]
      >> Cases_on `ll3` >> Cases_on `ll4`
      >> fs[] >> rveq
      >> CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM(CONJUNCT1 LAPPEND)]))))
      >> CONV_TAC(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM(CONJUNCT1 LAPPEND)])))))
      >> PURE_ONCE_REWRITE_TAC[GSYM(CONJUNCT2 LAPPEND)]
      >> simp[GSYM LAPPEND_ASSOC]
      >> metis_tac[llist_upto_rules])
QED


Theorem LFLATTEN_fromList: !l.
  LFLATTEN(fromList(MAP fromList l)) = fromList(FLAT l)
Proof
  Induct >> rw[LAPPEND_fromList]
QED

Theorem parts_ok_remove_events:
  parts_ok st.ffi (q,r)
  ==> parts_ok (st.ffi with io_events := []) (q,r)
Proof
  rw[parts_ok_def] >> metis_tac[]
QED

Theorem evaluate_ck_history_irrelevance:
  (!(st:'ffi semanticPrimitives$state) env ck exp st' res l. evaluate_ck ck (st with ffi := st.ffi with io_events := l) env exp = (st',res)
  ==> evaluate_ck ck st env exp = (st' with ffi := st'.ffi with io_events := st.ffi.io_events ++ DROP (LENGTH l) st'.ffi.io_events, res))
Proof
  rw[evaluate_ck_def] >>
  imp_res_tac evaluatePropsTheory.evaluate_history_irrelevance >>
  fs [rich_listTheory.DROP_APPEND2] >>
  first_x_assum (fn t => simp [GSYM t] \\ AP_THM_TAC) >>
  rpt AP_THM_TAC >>
  AP_TERM_TAC >>
  simp [semanticPrimitivesTheory.state_component_equality,
    ffiTheory.ffi_state_component_equality]
QED

Theorem remove_events_IMAGE:
parts_ok st.ffi p ==>
st2heap p (st with ffi := st.ffi with io_events := []) =
IMAGE (\x. case x of FFI_part s u ns l => FFI_part s u ns []
                   | _ => x) (st2heap p st)
Proof
  Cases_on `p` >>
  rw[st2heap_def,FUN_EQ_THM,EQ_IMP_THM,ffi2heap_def] >> fs[parts_ok_remove_events] >-
    (qexists_tac `x` >> every_case_tac >> fs[FFI_part_NOT_IN_store2heap]) >-
    (qexists_tac `FFI_split` >> simp[]) >-
    (qexists_tac `FFI_part s u ns (FILTER (ffi_has_index_in ns) st.ffi.io_events)` >> every_case_tac >> fs[] >> rveq >> fs[]) >-
    (every_case_tac >> fs[FFI_part_NOT_IN_store2heap])
QED

Theorem parts_ok_swap_events:
  parts_ok st.ffi p /\
  EVERY (ffi_has_index_in (FLAT (MAP FST (SND p)))) es ==>
  parts_ok (st.ffi with io_events := es) p
Proof
  Cases_on `p` >> rw[parts_ok_def] >> metis_tac[]
QED

Theorem FFI_part_has_index_in:
  FFI_part s u ns es ∈ st2heap p st'
  ==>
  EVERY (ffi_has_index_in (FLAT (MAP FST (SND p)))) es
Proof
  Cases_on `p` >>
  rw[st2heap_def,ffi2heap_def,FFI_part_NOT_IN_store2heap] >>
  fs[parts_ok_def] >>
  metis_tac[EVERY_FILTER_IMP]
QED

Theorem remove_events_IMAGE2:
parts_ok st.ffi p /\
parts_ok (st.ffi with io_events := es) p
==>
st2heap p (st with ffi := st.ffi with io_events := es) =
IMAGE (\x. case x of FFI_part s u ns l => FFI_part s u ns (FILTER (ffi_has_index_in ns) es)
                   | _ => x) (st2heap p st)
Proof
  Cases_on `p` >>
  rw[st2heap_def,FUN_EQ_THM,EQ_IMP_THM,ffi2heap_def] >> fs[parts_ok_remove_events] >-
    (qexists_tac `x` >> every_case_tac >> fs[FFI_part_NOT_IN_store2heap]) >-
    (qexists_tac `FFI_split` >> simp[]) >-
    (qexists_tac `FFI_part s u ns (FILTER (ffi_has_index_in ns) st.ffi.io_events)` >> every_case_tac >> fs[] >> rveq >> fs[]) >-
    (every_case_tac >> fs[FFI_part_NOT_IN_store2heap])
QED

(* TODO: move every_LNTH *)
Theorem every_LNTH:
  !P ll. every P ll <=> !n e. LNTH n ll = SOME e ==> P e
Proof
  fs [every_def,exists_LNTH] \\ metis_tac []
QED

Theorem LNTH_LUNFOLD_SOME:
  !n f g x.
   LNTH n (LUNFOLD (\x. SOME(f x, g x)) x) =
   SOME(g(FUNPOW f n x))
Proof
 Induct >>
 simp[LNTH_LUNFOLD,FUNPOW]
QED

Theorem every_LGENLIST[local]:
  every P (LGENLIST f NONE)
  = !x. P(f x)
Proof
  rw[every_LNTH,LNTH_LGENLIST,EQ_IMP_THM]
QED

Theorem LFLATTEN_LAPPEND_fromList:
  !l1 ll2.
  LFLATTEN(LAPPEND (fromList l1) ll2) = LAPPEND (LFLATTEN(fromList l1)) (LFLATTEN ll2)
Proof
  Induct >>
  rw[LAPPEND_ASSOC]
QED

Theorem LGENLIST_NONE_UNFOLD:
  LGENLIST f NONE = f 0:::LGENLIST(f o $+ 1) NONE
Proof
  rw[LGENLIST_def,Once LUNFOLD,LUNFOLD_BISIMULATION]
  \\ qexists_tac `\x y. x = y + 1`
  \\ simp[]
QED

Theorem LAPPEND_fromList_EQ: !l ll ll'.
  LAPPEND (fromList l) ll = LAPPEND (fromList l) ll'
  ==> ll = ll'
Proof
  Induct >> rw[]
QED

Theorem LFLATTEN_NOT_NIL_IMP:
  LFLATTEN ll <> [||]
  ==>
  ?n ll2. LNTH n ll = SOME ll2 /\ ll2 <> [||]
Proof
 rw[LFLATTEN_EQ_NIL,every_LNTH] >> metis_tac[]
QED

Theorem LFINITE_LFLATTEN_LGENERATE:
  LFINITE(LFLATTEN(LGENLIST f NONE))
  ==>
  ?n. LFLATTEN(LGENLIST (f o $+ n) NONE) = [||]
Proof
  rpt strip_tac
  \\ dxrule_then strip_assume_tac LFINITE_HAS_LENGTH
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [`f`,`n`]
  \\ ho_match_mp_tac COMPLETE_INDUCTION
  \\ Cases >-
    (rw[] \\ qexists_tac `0` \\ simp[])
  \\ rw[]
  \\ `LFLATTEN(LGENLIST f NONE) <> [||]` by(CCONTR_TAC >> fs[])
  \\ dxrule LFLATTEN_NOT_NIL_IMP
  \\ disch_then(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[WhileTheory.LEAST_EXISTS])
  \\ qmatch_asmsub_abbrev_tac `LNTH a1`
  \\ Q.ISPECL_THEN [`a1`,`f`] assume_tac (GEN_ALL LGENLIST_CHUNK_GENLIST)
  \\ fs[]
  \\ fs[LFLATTEN_LAPPEND_fromList]
  \\ `GENLIST f a1 = REPLICATE a1 [||]`
    by(match_mp_tac LIST_EQ
       \\ rw[EL_REPLICATE]
       \\ first_x_assum drule
       \\ simp[LNTH_LAPPEND,LNTH_fromList])
  \\ fs[LNTH_LAPPEND]
  \\ `LFLATTEN (fromList (REPLICATE a1 [||])) = [||]`
      by(rw[LFLATTEN_EQ_NIL,every_LNTH,LNTH_fromList,EL_REPLICATE])
  \\ fs[]
  \\ qpat_x_assum `LLENGTH _ = SOME _`
       (mp_tac o ONCE_REWRITE_RULE [LGENLIST_NONE_UNFOLD])
  \\ fs[LLENGTH_LGENLIST]
  \\ fs[]
  \\ rw[LLENGTH_APPEND]
  \\ fs[LNTH_LGENLIST]
  \\ imp_res_tac LFINITE_LLENGTH
  \\ rename1 `LLENGTH (f a1) = SOME m`
  \\ `m > 0` by(Cases_on `f a1` >> fs[])
  \\ fs[]
  \\ last_x_assum(qspec_then `n` mp_tac)
  \\ impl_tac >- fs[]
  \\ disch_then drule
  \\ rw[]
  \\ rename1 `f o $+a o $+b o $+c`
  \\ qexists_tac `a + b + c`
  \\ fs[o_DEF]
QED

Theorem list_length_eq[local]:
  l1 = l2 ==> LENGTH l1 = LENGTH l2
Proof
  simp[]
QED

Theorem list_length_eq2[local]:
  l1 = l2 ==> LENGTH(FLAT(MAP FST l1)) = LENGTH(FLAT(MAP FST l2))
Proof
  simp[]
QED

Theorem MEM_FLAT_MAP_FST_SING:
  MEM (FLAT (MAP FST r),u) r
  /\
  ALL_DISTINCT(FLAT (MAP FST r))
  /\
  MEM (ns, u') r
  /\
  ns <> []
  ==>
  ns = FLAT(MAP FST r) /\ u' = u
Proof
  strip_tac >>
  Cases_on `r` >> fs[] >> rveq >> fs[] >>
  Cases_on `FLAT (MAP FST t)` >> fs[FLAT_EQ_NIL,EVERY_MAP] >>
  imp_res_tac EVERY_MEM >> fs[] >>
  TRY(qpat_x_assum `_ = h` (assume_tac o CONV_RULE(RHS_CONV(PURE_ONCE_REWRITE_CONV[GSYM PAIR])))) >>
  fs[] >-
  (fs[MEM_APPEND] >>
   fs[MEM_SPLIT] >> rveq >> fs[FLAT_APPEND] >>
   fs[APPEND_EQ_CONS] >> rveq >> fs[] >>
   imp_res_tac list_length_eq >> fs[]) >>
  fs[MEM_APPEND] >>
  fs[MEM_SPLIT] >> rveq >> fs[FLAT_APPEND] >>
  qpat_x_assum `_ = _::_` (strip_assume_tac o REWRITE_RULE [APPEND_EQ_CONS]) >>
  fs[] >> rveq >> fs[] >>
  qpat_x_assum `_ ++ _ = _ ++ _` (strip_assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID]) >>
  rveq >> fs[] >>
  TRY(
    qpat_x_assum `_ ++ _ = _ ++ _` (strip_assume_tac o REWRITE_RULE
                                    [CONV_RULE(LHS_CONV SYM_CONV) APPEND_EQ_APPEND_MID]) >>
    rveq >> fs[] >> rveq >> fs[] >>
    imp_res_tac list_length_eq2 >> fs[] >>
    qpat_x_assum `_::_ = _ ++ _` (strip_assume_tac o REWRITE_RULE
                                      [CONV_RULE(LHS_CONV SYM_CONV) APPEND_EQ_SING]) >>
    rveq >> fs[] >> rveq >> fs[] >>
    NO_TAC) >>
  imp_res_tac list_length_eq >> fs[ADD1] >>
  `LENGTH ns = 0` by intLib.COOPER_TAC >>
  fs[quantHeuristicsTheory.LIST_LENGTH_0]
QED

Theorem limited_parts_unique_part:
  limited_parts ns p /\
  FFI_part s u ns events ∈ st2heap p st /\
  FFI_part s' u' ns' events' ∈ st2heap p st
  ==>
  s = s' /\ u = u' /\ ns = ns' /\ events = events'
Proof
  strip_tac >>
  Cases_on `p` >> fs[st2heap_def,limited_parts_def] >>
  fs[FFI_part_NOT_IN_store2heap,ffi2heap_def] >>
  PURE_FULL_CASE_TAC >> fs[] >> rveq >>
  fs[parts_ok_def] >>
  conj_asm2_tac >- (fs[] >> rveq >> fs[] >> Cases_on `FLAT (MAP FST r)` >> fs[]) >>
  metis_tac[MEM_FLAT_MAP_FST_SING]
QED

Theorem IMAGE_purge_parts_no_parts:
  (!s u ns es. FFI_part s u ns es ∉ h)
  ==>
  IMAGE
      (λx.
           case x of
             Mem v7 v8 => x
           | FFI_split => x
           | FFI_part s u ns l => FFI_part s u ns []
           | FFI_full v13 => x) h = h
Proof
  simp[IN_DEF,FUN_EQ_THM] >> strip_tac >> Cases >> fs[] >>
  rw[EQ_IMP_THM] >> rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
  qmatch_asmsub_abbrev_tac `h a1` >>
  qexists_tac `a1` >> simp[Abbr `a1`]
QED

Theorem IMAGE_purge_parts_no_parts2:
  (!s u ns es. FFI_part s u ns es ∉ h)
  ==>
  IMAGE
      (λx.
           case x of
             Mem v7 v8 => x
           | FFI_split => x
           | FFI_part s u ns l => FFI_part s u ns (f ns)
           | FFI_full v13 => x) h = h
Proof
  simp[IN_DEF,FUN_EQ_THM] >> strip_tac >> Cases >> fs[] >>
  rw[EQ_IMP_THM] >> rpt(PURE_FULL_CASE_TAC >> rveq >> fs[]) >>
  qmatch_asmsub_abbrev_tac `h a1` >>
  qexists_tac `a1` >> simp[Abbr `a1`]
QED

Theorem LFLATTEN_fromList_REPLICATE_LNIL:
  LFLATTEN (fromList (REPLICATE a1 [||])) = [||]
Proof
  rw[LFLATTEN_EQ_NIL,every_LNTH,LNTH_fromList,EL_REPLICATE]
QED

Theorem repeat_POSTd_one_FFI_part_FLATTEN:
    !p env fv xv H Q ns.
      limited_parts ns p /\
      (?Hs events vs ss u io.
         vs 0 xv /\ H ==>> Hs 0 * one (FFI_part (ss 0) u ns (events 0)) /\
         (!i xv. vs i xv ==>
            (app p fv [xv] (Hs i * one (FFI_part (ss i) u ns []))
                             (POSTv v'. &(vs (SUC i) v') * Hs (SUC i)
                              * one (FFI_part (ss(SUC i)) u ns (events(SUC i)))))) /\
         Q(LFLATTEN(LGENLIST (fromList o events) NONE)))
      ==>
      app p (some_repeat_clos env) [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ match_mp_tac(GEN_ALL repeat_POSTd_one_FFI_part)
  \\ asm_exists_tac \\ simp[]
  \\ asm_exists_tac \\ simp[]
  \\ qexists_tac
       `\n. Hs n *
              one (FFI_part (ss n) u ns (FLAT(GENLIST events (SUC n))))`
  \\ simp[]
  \\ qexists_tac `\n. FLAT(GENLIST events (SUC n))`
  \\ qexists_tac `ss`
  \\ qexists_tac `u`
  \\ qexists_tac `LFLATTEN (LGENLIST (fromList o events) NONE)`
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >-
    (rw[] \\ first_x_assum drule \\
     fs[app_def,app_basic_def,evaluate_to_heap_def] \\
     rw[] \\
     fs[STAR_def,one_def] \\
     `parts_ok st.ffi p`
       by(Cases_on `p` >> CCONTR_TAC >>
          fs[SPLIT_def,st2heap_def] >>
          rveq >> fs[ffi2heap_def] >>
          fs[UNION_DEF,FUN_EQ_THM,EQ_IMP_THM,DISJ_IMP_THM] >>
          metis_tac[FFI_part_NOT_IN_store2heap]) \\
     rename1 `SPLIT h_i (u1, _)` \\
     qabbrev_tac `h_i' = FFI_part (ss i) u ns [] INSERT u1` \\
     first_x_assum(qspecl_then [`h_i'`,`h_k`,`st with ffi := st.ffi with io_events := []`] mp_tac) \\
     impl_keep_tac >-
       (fs[Abbr `h_i'`,SPLIT_SING_2] >>
        fs[remove_events_IMAGE,SPLIT_def] >>
        qpat_x_assum `_ = st2heap _ _` (assume_tac o GSYM) >>
        fs[] >>
        reverse conj_tac >-
          (CCONTR_TAC >> fs[] >>
           `FFI_part (ss i) u ns [] ∈ st2heap p st` by metis_tac[IN_UNION] >>
           `FFI_part (ss i) u ns (FLAT (GENLIST events (SUC i))) ∈ st2heap p st`
             by metis_tac[IN_UNION,IN_INSERT] >>
           imp_res_tac limited_parts_unique_part >> fs[]) >>
        qmatch_goalsub_abbrev_tac `(_ INSERT a1) ∪ a2 = (_ INSERT a3) ∪ a4` >>
        `a3 = a1 /\ a4 = a2` suffices_by simp[] >>
        conj_tac >> unabbrev_all_tac >> match_mp_tac IMAGE_purge_parts_no_parts >>
        rw[] >> spose_not_then strip_assume_tac >>
        metis_tac[IN_UNION,IN_INSERT,limited_parts_unique_part]) >>
     simp[PULL_EXISTS] >> disch_then(qspec_then `u1` mp_tac) >>
     impl_keep_tac >-
       (simp[] >>
        fs[SPLIT_SING_2] >> fs[SPLIT_def] >>
        metis_tac[IN_UNION,IN_INSERT,limited_parts_unique_part]) >>
     strip_tac >>
     fs[] >> qexists_tac `r` >>
     Cases_on `r` >> fs[cond_def,SPLIT_emp1] >>
     rveq >>
     rename1 `SPLIT h_f (u2, _)` \\
     qabbrev_tac `h_f' = FFI_part (ss (SUC i)) u ns (FLAT (GENLIST events (SUC (SUC i)))) INSERT u2` \\
     `SPLIT3 (st2heap p (st' with ffi := st'.ffi
                             with io_events := FLAT (GENLIST events (SUC(SUC i))))) (h_f',h_k,h_g)`
       by(qmatch_goalsub_abbrev_tac `st2heap _ st2` >>
          `parts_ok st'.ffi p`
            by(Cases_on `p` >> CCONTR_TAC >>
               fs[SPLIT3_def,SPLIT_def,st2heap_def] >>
               rveq >> fs[ffi2heap_def] >>
               fs[UNION_DEF,FUN_EQ_THM,EQ_IMP_THM,DISJ_IMP_THM] >>
               metis_tac[FFI_part_NOT_IN_store2heap]) >>
          drule(GEN_ALL remove_events_IMAGE2) >>
          `FFI_part (ss (SUC i)) u ns (events (SUC i)) ∈ st2heap p st'`
            by metis_tac[IN_UNION,IN_INSERT,SPLIT_def,SPLIT3_def] >>
          `FFI_part (ss i) u ns (FLAT (GENLIST events (SUC i))) ∈ st2heap p st`
            by metis_tac[IN_UNION,IN_INSERT,SPLIT_def,SPLIT3_def] >>
          `parts_ok st2.ffi p`
           by(simp[Abbr `st2`] >>
              match_mp_tac parts_ok_swap_events >>
              simp[] >>
              imp_res_tac limited_FFI_part_IN_st2heap_IMP >>
              imp_res_tac FFI_part_has_index_in >>
              simp[Once GENLIST,SNOC_APPEND]) >>
          imp_res_tac FFI_part_has_index_in >>
          qunabbrev_tac `st2` >> fs[] >> disch_then drule >>
          disch_then kall_tac >>
          fs[SPLIT_def,SPLIT3_def,Abbr `h_f'`] >> rveq >> fs[] >>
          qpat_x_assum `_ = st2heap _ _` (assume_tac o GSYM) >>
          fs[] >>
          reverse conj_tac >-
            (conj_tac >> CCONTR_TAC >> fs[] >>
             metis_tac[IN_UNION,IN_INSERT,limited_parts_unique_part]) >>
          PURE_ONCE_REWRITE_TAC[GENLIST] >>
          `ns = FLAT(MAP FST(SND p))` by(Cases_on `p` >> fs[limited_parts_def]) >>
          fs[EVERY_FILTER,SNOC_APPEND,FILTER_APPEND] >>
          fs[GSYM FILTER_EQ_ID] >>
          qmatch_goalsub_abbrev_tac `(_ INSERT a1) ∪ a2 ∪ a3 = a4 ∪ _ ∪ a5 ∪ a6` >>
          `a4 = a1 /\ a5 = a2 /\ a6 = a3`
            suffices_by(simp[IN_DEF,UNION_DEF,INSERT_DEF,FUN_EQ_THM] >>
                        rveq >> metis_tac[]) >>
          unabbrev_all_tac >> rpt conj_tac >> ho_match_mp_tac IMAGE_purge_parts_no_parts2 >>
          rw[] >> spose_not_then strip_assume_tac >>
          metis_tac[IN_UNION,IN_INSERT,limited_parts_unique_part]) >>
     asm_exists_tac >>
     simp[] >>
     conj_tac >-
       (unabbrev_all_tac >> fs[SPLIT_SING_2] >>
        qexists_tac `u2` >> fs[] >>
        fs[SPLIT_def,SPLIT3_def] >>
        metis_tac[IN_UNION,IN_INSERT,limited_parts_unique_part]) >>
     drule(GEN_ALL evaluate_ck_history_irrelevance) >>
     strip_tac >> asm_exists_tac >>
     simp[] >>
     `FFI_part (ss (SUC i)) u ns (events (SUC i)) ∈ st2heap p st'`
       by metis_tac[IN_UNION,IN_INSERT,SPLIT_def,SPLIT3_def] >>
     `FFI_part (ss i) u ns (FLAT (GENLIST events (SUC i))) ∈ st2heap p st`
       by metis_tac[IN_UNION,IN_INSERT,SPLIT_def,SPLIT3_def] >>
     simp[Once GENLIST,SNOC_APPEND] >>
     imp_res_tac limited_FFI_part_IN_st2heap_IMP >> simp[])
  \\ reverse conj_tac >- simp []
  \\ rw[lprefix_lub_def] >-
    (rw[LPREFIX_APPEND]
     \\ Q.ISPECL_THEN [`SUC x`,`llist$fromList o events`]
                      mp_tac
                      (GEN_ALL LGENLIST_CHUNK_GENLIST)
     \\ disch_then (fn thm => simp[thm])
     \\ simp[LFLATTEN_LAPPEND_fromList,GSYM MAP_GENLIST,LFLATTEN_fromList]
     \\ metis_tac[])
  \\ fs[PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac `LPREFIX ll1 ll2`
  \\ Cases_on `LFINITE ll1` >-
   (unabbrev_all_tac
    \\ imp_res_tac LFINITE_LFLATTEN_LGENERATE
    \\ Q.ISPECL_THEN [`n`,`llist$fromList o events`] assume_tac
            (GEN_ALL LGENLIST_CHUNK_GENLIST)
    \\ fs[LFLATTEN_LAPPEND_fromList,LAPPEND_NIL_2ND]
    \\ fs[GSYM MAP_GENLIST,LFLATTEN_fromList]
    \\ Cases_on `n` >> fs[])
  \\ `ll1 = ll2` suffices_by simp[]
  \\ unabbrev_all_tac
  \\ match_mp_tac LLIST_BISIM_UPTO
  \\ qexists_tac`\ll1 ll2. ?n.
    ll1 = LFLATTEN (LGENLIST (fromList o events o $+ n) NONE) /\
    ~LFINITE ll1 /\
    (!x. LPREFIX(fromList(FLAT (GENLIST (events o $+ n) (SUC x)))) ll2)`
  \\ conj_tac >-
    (rw[] >> qexists_tac `0` >> rw[o_DEF] >> metis_tac[])
  \\ rpt(pop_assum kall_tac)
  \\ rw[]
  \\ Cases_on `every ($= [||]) (LGENLIST (fromList ∘ events ∘ $+ n) NONE)` >-
    (fs[Once LFLATTEN])
  \\ match_mp_tac OR_INTRO_THM2
  \\ pop_assum(assume_tac o Ho_Rewrite.REWRITE_RULE [every_LGENLIST,o_DEF,NOT_FORALL_THM])
  \\ pop_assum(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[WhileTheory.LEAST_EXISTS])
  \\ fs[CONV_RULE(LHS_CONV SYM_CONV) fromList_EQ_LNIL]
  \\ qspecl_then [`LEAST x. events (n + x) <> []`,`fromList o events o $+ n`] mp_tac
      (LGENLIST_CHUNK_GENLIST
       |> GEN_ALL
       |> INST_TYPE [alpha|->``:io_event llist``])
  \\ disch_then(fn thm => simp[thm])
  \\ simp[LFLATTEN_LAPPEND_fromList]
  \\ simp[Once LGENLIST_NONE_UNFOLD]
  \\ simp[GSYM LAPPEND_ASSOC]
  \\ Cases_on `events(n + LEAST x. events(n + x) <> [])` >> fs[]
  \\ simp[Once(GSYM MAP_GENLIST),LFLATTEN_fromList]
  \\ qmatch_goalsub_abbrev_tac `GENLIST a1 a2`
  \\ `GENLIST a1 a2 = REPLICATE a2 []`
    by(unabbrev_all_tac >>
       match_mp_tac LIST_EQ >>
       rw[EL_REPLICATE])
  \\ last_assum(qspec_then `a2` assume_tac)
  \\ rfs[GENLIST,LPREFIX_APPEND,SNOC_APPEND,FLAT_REPLICATE_NIL]
  \\ conj_tac >- (unabbrev_all_tac \\ fs[])
  \\ simp[GSYM MAP_GENLIST,LFLATTEN_fromList,FLAT_REPLICATE_NIL]
  \\ rfs [LFLATTEN_fromList_REPLICATE_LNIL]
  \\ CONV_TAC(RATOR_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV[LGENLIST_NONE_UNFOLD])))
  \\ simp[]
  \\ unabbrev_all_tac \\ simp[]
  \\ fs[]
  \\ match_mp_tac llist_upto_context
  \\ match_mp_tac llist_upto_rel
  \\ rw[]
  \\ qexists_tac `n + (LEAST x. events (n + x) <> []) + 1`
  \\ simp[o_DEF]
  \\ conj_tac >-
    (qpat_x_assum `~LFINITE _` mp_tac >>
     Q.ISPECL_THEN
       [`SUC(LEAST x. events(n + x) <> [])`,`llist$fromList o events o $+ n`]
       mp_tac
       (GEN_ALL LGENLIST_CHUNK_GENLIST) >>
     simp[Once(GSYM MAP_GENLIST)] >>
     simp[LFLATTEN_LAPPEND_fromList,LFINITE_APPEND,LFLATTEN_fromList,LFINITE_fromList] >>
     simp[o_DEF,ADD1])
  \\ rw[]
  \\ fs[GSYM MAP_GENLIST]
  \\ last_assum(qspec_then `x + SUC(LEAST x. events(n + x) <> [])` strip_assume_tac)
  \\ rfs[GENLIST,SNOC_APPEND,FLAT_REPLICATE_NIL]
  \\ rfs[GENLIST_APPEND,GENLIST,SNOC_APPEND,FLAT_REPLICATE_NIL]
  \\ fs[GSYM LAPPEND_fromList,LAPPEND_ASSOC]
  \\ imp_res_tac LAPPEND_fromList_EQ
  \\ rveq
  \\ fs[ADD1]
  \\ Ho_Rewrite.PURE_ONCE_REWRITE_TAC[prove(``$+ n = \x. n + x:num``,rw[FUN_EQ_THM])]
  \\ simp[]
  \\ metis_tac[]
QED

Theorem LFLATTEN_LGENLIST_REPEAT:
  LFLATTEN(LGENLIST (\x. fromList l) NONE) = LREPEAT l
Proof
  Cases_on `l = []` >-
    (rw[Once LFLATTEN,every_LNTH,LNTH_LGENLIST]) >-
    (match_mp_tac LLIST_BISIM_UPTO
     \\ qexists_tac `\ll1 ll2. ?n.
                      ll1 = LFLATTEN(LGENLIST (\x. fromList l) NONE) /\
                      ll2 = LREPEAT l`
     \\ conj_tac >- (fs[] >> qexists_tac `0` >> fs[])
     \\ rw[]
     \\ Cases_on `l` \\ fs[]
     >- fs[Once LGENLIST_NONE_UNFOLD, Once LREPEAT_thm]
     \\ CONV_TAC(RATOR_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])))
     \\ fs[] \\ match_mp_tac llist_upto_context
     \\ match_mp_tac llist_upto_rel \\ simp[o_DEF])
QED

Theorem IMP_app_POSTd_one_FFI_part_FLATTEN:
    make_stepfun_closure env fname farg fbody = SOME stepv /\
    fname ≠ farg ∧
    limited_parts ns p /\
    (?Hs events vs ss u io.
       vs 0 xv /\ H ==>> Hs 0 * one (FFI_part (ss 0) u ns (events 0)) /\
       (!i xv. vs i xv ==>
          (app p stepv [xv] (Hs i * one (FFI_part (ss i) u ns []))
                           (POSTv v'. &(vs (SUC i) v') * Hs (SUC i)
                            * one (FFI_part (ss(SUC i)) u ns (events(SUC i)))))) /\
       Q(LFLATTEN(LGENLIST (fromList o events) NONE)))
      ==>
    app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)
Proof
  strip_tac
  \\ match_mp_tac make_repeat_closure_sound \\ fs []
  \\ fs [make_repeat_closure_def]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ match_mp_tac app_opapp_intro
  \\ fs [evaluate_def,semanticPrimitivesTheory.build_rec_env_def]
  \\ fs [GSYM some_repeat_clos_def]
  \\ match_mp_tac (GEN_ALL repeat_POSTd_one_FFI_part_FLATTEN) \\ fs []
  \\ qexists_tac `ns` \\ fs []
  \\ asm_exists_tac \\ fs[] \\ asm_exists_tac \\ fs[]
QED
