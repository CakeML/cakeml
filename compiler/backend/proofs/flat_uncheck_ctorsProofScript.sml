(*
  Correctness proof for uncheck_ctors
*)
open preamble;
open flatLangTheory flatSemTheory flatPropsTheory flat_uncheck_ctorsTheory;

val _ = new_theory "flat_uncheck_ctorsProof";

val _ = set_grammar_ancestry ["misc","flatProps","flat_uncheck_ctors"];

Theorem pat_bindings_compile_pat[simp]:
 !(p:flatLang$pat) vars. pat_bindings (compile_pat p) vars = pat_bindings p vars
Proof
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def, pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [pat_bindings_def,astTheory.pat_bindings_def, PULL_FORALL]
QED

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!lit.
    v_rel (flatSem$Litv lit) (flatSem$Litv lit)) ∧
  (!cn vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (flatSem$Conv cn vs) (flatSem$Conv (SOME (the (0,NONE) cn)) vs')) ∧
  (!env x e env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (flatSem$Closure env x e) (flatSem$Closure env' x (HD (compile [e])))) ∧
  (!env funs x env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (Recclosure env funs x)
      (Recclosure env' (MAP (\(f,x,e). (f, x, HD (compile [e]))) funs) x)) ∧
  (!loc.
    v_rel (Loc loc) (Loc loc)) ∧
  (!vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (Vectorv vs) (Vectorv vs'))`;

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    s.clock = s'.clock ∧
    LIST_REL (sv_rel v_rel) s.refs s'.refs ∧
    s.ffi = s'.ffi ∧
    LIST_REL (OPTION_REL v_rel) s.globals s'.globals
    ⇒
    s_rel s s')`;

val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  (!env env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env.v env'.v ∧
    env.exh_pat = env'.exh_pat ∧
    env.check_ctor ∧
    ~env'.check_ctor
    ⇒
    env_rel env env')`;

val alookup_env_rel = Q.prove (
  `!env env' n x.
    env_rel env env' ∧
    ALOOKUP env.v n = SOME x
    ⇒
    ∃x'. v_rel x x' ∧ ALOOKUP env'.v n = SOME x'`,
  strip_tac >>
  Induct_on `env.v` >>
  rw [env_rel_cases]
  >- metis_tac [ALOOKUP_def, NOT_SOME_NONE] >>
  qpat_x_assum `_::_ = _.v` (assume_tac o GSYM) >>
  fs [LIST_REL_CONS1, ALOOKUP_def] >>
  rename1 `ALOOKUP (p::_) _ = SOME _` >>
  Cases_on `p` >>
  fs [ALOOKUP_def] >>
  rename1 `ALOOKUP (p::_) _ = SOME _` >>
  Cases_on `p` >>
  fs [ALOOKUP_def] >>
  rw [] >>
  rw [] >>
  fs [] >>
  first_x_assum (qspec_then `env with v := v` mp_tac) >>
  rw [] >>
  first_x_assum (qspec_then `env' with v := t'` mp_tac) >>
  rw [env_rel_cases]);

Theorem v_rel_bool[simp]:
   !v b. v_rel (Boolv b) v ⇔ v = Boolv b
Proof
  rw [Once v_rel_cases, Boolv_def, libTheory.the_def]
QED

val lemma = Q.prove (
  `(\(x,y,z). x) = FST`,
  rw [FUN_EQ_THM] >>
  pairarg_tac >>
  fs []);

val do_opapp_correct = Q.prove (
  `∀vs vs'.
     LIST_REL v_rel vs vs'
     ⇒
     (flatSem$do_opapp vs = NONE ⇒ do_opapp vs' = NONE) ∧
     (!env e.
       do_opapp vs = SOME (env,e) ⇒
       ∃env'. LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env' ∧
              do_opapp vs' = SOME (env', HD (compile [e])))`,
  rw [do_opapp_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  TRY (fs [Once v_rel_cases] >> NO_TAC) >>
  qpat_x_assum `v_rel (Recclosure _ _ _) _` mp_tac >>
  simp [Once v_rel_cases] >>
  CCONTR_TAC >>
  fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw [] >>
  fs [semanticPrimitivesPropsTheory.find_recfun_ALOOKUP, ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >>
  fs [MEM_MAP, lemma, FORALL_PROD] >>
  TRY (pairarg_tac >> fs []) >>
  rw [] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  fs [] >>
  rw []
  >- metis_tac [FST]
  >- metis_tac [FST] >>
  fs [build_rec_env_merge, LIST_REL_APPEND_EQ] >>
  fs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  qpat_x_assum`¬_`mp_tac
  \\ simp[Once v_rel_cases]
  \\ simp[LIST_REL_EL_EQN,UNCURRY]);

val s_rel_store_assign = Q.prove (
  `s_rel s1 s1' ∧
   v_rel v v' ∧
   store_assign l (Refv v) s1.refs = SOME v1 ⇒
   ∃v1'. store_assign l (Refv v') s1'.refs = SOME v1' ∧
         s_rel (s1 with refs := v1) (s1' with refs := v1')`,
  rw [semanticPrimitivesTheory.store_assign_def, s_rel_cases]
  >- metis_tac [LIST_REL_LENGTH] >>
  fs [semanticPrimitivesTheory.store_v_same_type_def, LIST_REL_EL_EQN, EL_LUPDATE] >>
  rw[] \\ every_case_tac >> fs [] >> rw [] >>
  res_tac >>
  fs[semanticPrimitivesPropsTheory.sv_rel_cases] >>
  rw [] >>
  fs []);

val s_rel_store_alloc = Q.prove (
  `s_rel s1 s1' ∧
   v_rel v v' ∧
   store_alloc (Refv v) s1.refs = (s,n) ⇒
   ∃s'. store_alloc (Refv v') s1'.refs = (s',n) ∧
           s_rel (s1 with refs := s) (s1' with refs := s')`,
  rw [semanticPrimitivesTheory.store_alloc_def, s_rel_cases]
  \\ fs[LIST_REL_EL_EQN]);

val sv_rel_store_alloc = Q.prove (
  `s_rel s1 s1' ∧
   sv_rel v_rel sv sv' ∧
   store_alloc sv s1.refs = (s,n) ⇒
   ∃s' n'. store_alloc sv' s1'.refs = (s',n')`,
  rw [semanticPrimitivesPropsTheory.sv_rel_cases, semanticPrimitivesTheory.store_alloc_def, s_rel_cases]);

val s_rel_store_lookup = Q.prove (
  `s_rel s1 s1' ∧
   store_lookup n s1.refs = SOME sv ⇒
   ∃sv'. store_lookup n s1'.refs = SOME sv' ∧ sv_rel v_rel sv sv'`,
  rw [semanticPrimitivesTheory.store_lookup_def, s_rel_cases] >>
  fs [LIST_REL_EL_EQN] >>
  res_tac >>
  fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
  fs []);

Theorem v_rel_eqn[simp]:
  (!lit v. v_rel (flatSem$Litv lit) v ⇔ v = Litv lit) ∧
  (!lit v. v_rel v (flatSem$Litv lit) ⇔ v = Litv lit) ∧
  (v_rel (Conv NONE []) (Conv (SOME (0,NONE)) [])) ∧
  (v_rel subscript_exn_v subscript_exn_v) ∧
  (v_rel bind_exn_v bind_exn_v) ∧
  (!loc l. v_rel (Loc loc) l ⇔ l = Loc loc) ∧
  (!loc l. v_rel l (Loc loc) ⇔ l = Loc loc) ∧
  (!vs v. v_rel (Vectorv vs) v ⇔ ∃vs'. v = Vectorv vs' ∧ LIST_REL v_rel vs vs') ∧
  (!vs v. v_rel v (Vectorv vs) ⇔ ∃vs'. v = Vectorv vs' ∧ LIST_REL v_rel vs' vs)
Proof
  rw [flatSemTheory.subscript_exn_v_def, flatSemTheory.bind_exn_v_def] >>
  ONCE_REWRITE_TAC [v_rel_cases] >>
  rw [libTheory.the_def]
QED

Theorem do_eq_correct:
   (∀a c b d e.
    v_rel a b ∧ v_rel c d ∧
    do_eq a c = Eq_val e ⇒
    do_eq b d = Eq_val e) ∧
   (∀a c b d e.
    LIST_REL v_rel a b ∧ LIST_REL v_rel c d ∧
    do_eq_list a c = Eq_val e ⇒
    do_eq_list b d = Eq_val e)
Proof
  ho_match_mp_tac do_eq_ind
  \\ rw[do_eq_def] \\ fs[do_eq_def] \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[case_eq_thms, bool_case_eq] \\ rw[] \\ fs[]
  \\ fs[Once v_rel_cases, do_eq_def]
  \\ rw[]
  \\ Cases_on`cn1` \\ TRY(Cases_on`cn2`) \\ fs[libTheory.the_def, ctor_same_type_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[] \\ rfs[]
QED

Theorem v_to_char_list_v_rel:
   ∀x y ls. v_rel x y ∧ v_to_char_list x = SOME ls ⇒ v_to_char_list y = SOME ls
Proof
  recInduct v_to_char_list_ind
  \\ rw[v_to_char_list_def]
  >- fs[Once v_rel_cases, v_to_char_list_def, libTheory.the_def]
  \\ qhdtm_x_assum`v_rel`mp_tac
  \\ rw[Once v_rel_cases, v_to_char_list_def, libTheory.the_def]
  \\ rw[v_to_char_list_def]
  \\ fs[case_eq_thms]
  \\ metis_tac[]
QED

Theorem v_to_list_v_rel:
   ∀x y ls. v_rel x y ∧ v_to_list x = SOME ls ⇒ ∃ls'. v_to_list y = SOME ls' ∧ LIST_REL v_rel ls ls'
Proof
  recInduct v_to_list_ind
  \\ rw[v_to_list_def]
  \\ qhdtm_x_assum`v_rel`mp_tac
  \\ rw[Once v_rel_cases, v_to_list_def, libTheory.the_def]
  \\ rw[ v_to_list_def]
  \\ fs[case_eq_thms]
  \\ rw[PULL_EXISTS]
QED

Theorem vs_to_string_v_rel:
   ∀vs ws str. LIST_REL v_rel vs ws ∧ vs_to_string vs = SOME str ⇒ vs_to_string ws = SOME str
Proof
  recInduct vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ rw[vs_to_string_def]
  \\ fs[case_eq_thms] \\ rw[]
QED

Theorem v_rel_list_to_v:
   ∀x y. LIST_REL v_rel x y ⇒ v_rel (list_to_v x) (list_to_v y)
Proof
  Induct \\ rw[list_to_v_def]
  \\ rw[Once v_rel_cases, libTheory.the_def]
  \\ fs[PULL_EXISTS, list_to_v_def]
QED

val do_app_correct = Q.prove (
  `∀s1 s1' s2 op vs vs' r.
     LIST_REL v_rel vs vs' ∧
     s_rel s1 s1' ∧
     do_app T s1 op vs = SOME (s2,r) ⇒
     ∃r' s2'. do_app F s1' op vs' = SOME (s2', r') ∧
              s_rel s2 s2' ∧
              result_rel v_rel v_rel r r'`,
  rw [do_app_cases] >>
  fs [] >>
  rw [] >>
  TRY (
    qmatch_rename_tac`v_rel _ _`
    \\ EVAL_TAC
    \\ rw[Once v_rel_cases]
    \\ EVAL_TAC
    \\ rw[] \\ NO_TAC )
  \\ fs [PULL_EXISTS] >>
  TRY (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    NO_TAC)
  >> TRY ( fsrw_tac[DNF_ss][] >> fs[LIST_REL_EL_EQN] >> NO_TAC)
  >- (imp_res_tac do_eq_correct \\ fs[])
  >- metis_tac [s_rel_store_assign]
  >- metis_tac [semanticPrimitivesPropsTheory.sv_rel_cases, s_rel_store_alloc]
  >- (
    fs[semanticPrimitivesTheory.store_alloc_def, s_rel_cases]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][] >>
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] )
  >- (
    fsrw_tac[DNF_ss][] >>
    imp_res_tac s_rel_store_lookup >>
    fs[semanticPrimitivesTheory.store_assign_def] >> rw[] >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    fs [s_rel_cases] >>
    fs[EVERY2_LUPDATE_same] >>
    fs[LIST_REL_EL_EQN, semanticPrimitivesTheory.store_lookup_def] >>
    EVAL_TAC)
  >- (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    fsrw_tac[DNF_ss][] )
  >- (
    fs[semanticPrimitivesTheory.store_lookup_def,
       semanticPrimitivesTheory.store_assign_def,
       s_rel_cases]
    \\ fs[LIST_REL_EL_EQN,EL_LUPDATE]
    \\ res_tac
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases] \\ fs[]
    \\ rw[semanticPrimitivesTheory.store_v_same_type_def, EL_LUPDATE])
  >- (
    fs[semanticPrimitivesTheory.store_lookup_def,
       semanticPrimitivesTheory.store_assign_def,
       s_rel_cases]
    \\ fs[LIST_REL_EL_EQN,EL_LUPDATE]
    \\ res_tac
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases] \\ fs[]
    \\ rw[semanticPrimitivesTheory.store_v_same_type_def, EL_LUPDATE]
  )
  >- metis_tac[v_to_char_list_v_rel]
  >- (
    imp_res_tac v_to_list_v_rel
    \\ fs[] \\ rw[]
    \\ metis_tac[vs_to_string_v_rel])
  >- metis_tac[v_to_list_v_rel]
  >- (
    fs[semanticPrimitivesTheory.store_alloc_def]
    \\ fs[s_rel_cases]
    \\ rw[LIST_REL_REPLICATE_same]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_assign_def]
    \\ fs[s_rel_cases]
    \\ rw[EVERY2_LUPDATE_same]
    \\ fs[LIST_REL_EL_EQN]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rfs[semanticPrimitivesTheory.store_v_same_type_def] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    imp_res_tac v_to_list_v_rel
    \\ fs[] \\ rw[]
    \\ match_mp_tac v_rel_list_to_v
    \\ fs[EVERY2_APPEND_suff])
  >- (
    fs[semanticPrimitivesTheory.store_lookup_def, s_rel_cases,
       semanticPrimitivesTheory.store_assign_def, LIST_REL_EL_EQN]
    \\ rw[EL_LUPDATE]
    \\ res_tac
    \\ qpat_x_assum`EL _ _ = _`assume_tac
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ rfs[]
    \\ rw[] )
  >- (
    imp_res_tac s_rel_store_lookup
    \\ fs[s_rel_cases]
    \\ rveq \\ fs[]
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ rfs[])
  >- (
    fs[s_rel_cases]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[LIST_REL_REPLICATE_same, OPTREL_def] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] \\ fs[]));

Theorem pmatch_correct:
   (∀env1 refs1 p v1 acc1 env2 refs2 v2 acc2.
    env_rel env1 env2 ∧
    LIST_REL (sv_rel v_rel) refs1 refs2 ∧
    v_rel v1 v2 ∧
    LIST_REL v_rel (MAP SND acc1) (MAP SND acc2) ∧
    MAP FST acc1 = MAP FST acc2 ∧
    pmatch env1 refs1 p v1 acc1 ≠ Match_type_error
    ⇒
    case pmatch env1 refs1 p v1 acc1 of
    | Match res1 => ∃res2.
        pmatch env2 refs2 (compile_pat p) v2 acc2 = Match res2 ∧
        LIST_REL v_rel (MAP SND res1) (MAP SND res2) ∧
        MAP FST res1 = MAP FST res2
    | r => pmatch env2 refs2 (compile_pat p) v2 acc2 = r) ∧
   (∀env1 refs1 p v1 acc1 env2 refs2 v2 acc2.
    env_rel env1 env2 ∧
    LIST_REL (sv_rel v_rel) refs1 refs2 ∧
    LIST_REL v_rel v1 v2 ∧
    LIST_REL v_rel (MAP SND acc1) (MAP SND acc2) ∧
    MAP FST acc1 = MAP FST acc2 ∧
    pmatch_list env1 refs1 p v1 acc1 ≠ Match_type_error
    ⇒
    case pmatch_list env1 refs1 p v1 acc1 of
    | Match res1 => ∃res2.
        pmatch_list env2 refs2 (MAP compile_pat p) v2 acc2 = Match res2 ∧
        LIST_REL v_rel (MAP SND res1) (MAP SND res2) ∧
        MAP FST res1 = MAP FST res2
    | r => pmatch_list env2 refs2 (MAP compile_pat p) v2 acc2 = r)
Proof
  ho_match_mp_tac pmatch_ind
  \\ rw[pmatch_def, compile_pat_def, libTheory.the_def]
  \\ TRY (
    qpat_x_assum`v_rel (Conv _ _) _`mp_tac
    \\ rw[Once v_rel_cases, libTheory.the_def] )
  >- (
    fs[pmatch_def, env_rel_cases] \\ rfs[]
    \\ fs[flatSemTheory.same_ctor_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] >>
    simp [ETA_THM])
  >- (
    fs[pmatch_def, env_rel_cases] \\ rfs[]
    \\ fs[flatSemTheory.same_ctor_def]
    \\ rename1`ctor_same_type (SOME c1) (SOME c2)`
    \\ Cases_on`c1` \\ Cases_on `c2`
    \\ fs[flatSemTheory.ctor_same_type_def]
    \\ rw[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    every_case_tac >>
    fs [pmatch_def] >>
    rw [ETA_THM] >>
    fs [env_rel_cases, same_ctor_def] >>
    metis_tac [LIST_REL_LENGTH])
  >- (
    fs[case_eq_thms]
    \\ Cases_on`store_lookup lnum refs1` \\ fs[]
    \\ Cases_on`x` \\ fs[]
    \\ `∃b. store_lookup lnum refs2 = SOME (Refv b) ∧ v_rel a b`
    by (
      fs[semanticPrimitivesTheory.store_lookup_def, LIST_REL_EL_EQN]
      \\ metis_tac[semanticPrimitivesPropsTheory.sv_rel_cases,
                   semanticPrimitivesTheory.store_v_distinct,
                   semanticPrimitivesTheory.store_v_11] )
    \\ simp[] )
  >- (
    pop_assum mp_tac
    \\ TOP_CASE_TAC \\ fs[pmatch_def]
    \\ strip_tac \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ res_tac \\ fs[] )
QED

val compile_exp_correct = Q.prove (
  `(∀env (s : 'a flatSem$state) es s' r s1 env'.
    evaluate env s es = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) v_rel r r1 ∧
      s_rel s' s1' ∧
      evaluate env' s1 (compile es) = (s1', r1)) ∧
   (∀env (s : 'a flatSem$state) v pes err_v s' r s1 env' err_v1 v1.
    evaluate_match env s v pes err_v = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1 ∧
    v_rel v v1 ∧
    v_rel err_v err_v1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) v_rel r r1 ∧
      s_rel s' s1' ∧
      evaluate_match env' s1 v1 (MAP (λ(p,e'). (compile_pat p,HD (compile [e']))) pes) err_v1 = (s1', r1))`,
  ho_match_mp_tac evaluate_ind >>
  rw [evaluate_def, compile_def] >>
  rw [] >>
  TRY (fs [env_rel_cases] >> NO_TAC) >>
  TRY (split_pair_case_tac >> rw []) >>
  TRY (split_pair_case_tac >> rw [])
  >- (
    every_case_tac >>
    fs [] >>
    rw [PULL_EXISTS] >>
    rfs [] >>
    rw [evaluate_append] >>
    res_tac >>
    rw [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    res_tac >>
    fs [])
  >- (
    every_case_tac >>
    fs [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    res_tac >>
    fs [] >>
    rw [] >>
    rfs [])
  >- (
    fs [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    fs [] >>
    rename [`evaluate env s [e] = (s1, r)`] >>
    Cases_on `r` >>
    fs [] >>
    rw []
    >- (
      res_tac >>
      rw [] >>
      fs [] >>
      rw []) >>
    Cases_on `e''` >>
    rw [] >>
    fs [] >>
    rfs [] >>
    rw [] >>
    fs [] >>
    rfs []
    >- (
      first_x_assum drule >>
      disch_then drule >>
      rw [] >>
      first_x_assum drule >>
      disch_then drule >>
      disch_then drule >>
      disch_then drule >>
      rw [])
    >- (
      first_x_assum drule >>
      disch_then drule >>
      rw []))
  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [compile_reverse] >>
    rw [] >>
    simp [Once v_rel_cases, libTheory.the_def])
  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [compile_reverse] >>
    rw [] >>
    simp [Once v_rel_cases, libTheory.the_def])
 >- (
    every_case_tac >>
    fs [LIST_REL_def] >>
    metis_tac [alookup_env_rel, NOT_SOME_NONE, SOME_11])
  >- (
    simp [Once v_rel_cases] >>
    fs [env_rel_cases])
  >- (
    fs [] >>
    rename [`evaluate _ _ _ = (s', r')`,
            `evaluate env1 _ (REVERSE (compile _)) = (s1', r1')`] >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    fs []
    >- (
      Cases_on `op = Opapp` >>
      fs []
      >- (
        rename1 `do_opapp (REVERSE vs)` >>
        Cases_on `do_opapp (REVERSE vs)` >>
        fs [] >>
        rw [] >>
        split_pair_case_tac >>
        fs [] >>
        res_tac >>
        fs [] >>
        rw [] >>
        Cases_on `s'.clock = 0` >>
        fs [compile_reverse] >>
        rw [] >>
        `LIST_REL v_rel (REVERSE vs) (REVERSE v')` by metis_tac [EVERY2_REVERSE] >>
        imp_res_tac do_opapp_correct >>
        rw []
        >- fs [s_rel_cases]
        >- fs [s_rel_cases]
        >- fs [s_rel_cases] >>
        `env_rel (env with v := env') (env1 with v := env'')` by fs [env_rel_cases] >>
        `s_rel (dec_clock s') (dec_clock s1')` by fs [dec_clock_def,s_rel_cases] >>
        res_tac >>
        rw [] >>
        metis_tac [HD, compile_sing])
      >- (
        first_x_assum drule
        \\ disch_then drule
        \\ strip_tac
        \\ rveq \\ fs[]
        \\ qpat_x_assum`_ = (_, r)`mp_tac
        \\ TOP_CASE_TAC \\ strip_tac \\ fs[pair_case_eq]
        \\ imp_res_tac EVERY2_REVERSE
        \\ drule do_app_correct
        \\ disch_then drule
        \\ rveq
        \\ fs[env_rel_cases] \\ rfs[]
        \\ disch_then drule
        \\ strip_tac
        \\ goal_assum (first_assum o mp_then Any mp_tac)
        \\ fs[compile_reverse]
        \\ rveq \\ fs[]))
    >- (
      res_tac >>
      fs [compile_reverse] >>
      rw []))
  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw []
    >- (
      imp_res_tac evaluate_sing >>
      rw [] >>
      fs [] >>
      rename1 `do_if v e2 e3` >>
      Cases_on `do_if v e2 e3` >>
      fs [] >>
      first_x_assum drule >>
      disch_then drule >>
      rw [] >>
      fs [] >>
      `?e'. compile [e1] = [e']` by metis_tac [compile_sing] >>
      fs [] >>
      rw [] >>
      fs [do_if_def] >>
      Cases_on `v = Boolv T` >>
      fs [v_rel_bool]
      >- metis_tac [compile_sing, HD] >>
      rfs [v_rel_bool] >>
      metis_tac [compile_sing, HD])
    >- (
      `?e'. compile [e1] = [e']` by metis_tac [compile_sing] >>
      res_tac >>
      fs [] >>
      rw [] >>
      rfs []))
  >- (
    every_case_tac >>
    fs [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    res_tac >>
    fs [] >>
    rw [] >>
    rfs [] >>
    metis_tac[v_rel_eqn] )
  >- (
    reverse(fsrw_tac[DNF_ss][case_eq_thms, compile_HD_sing] \\ rveq \\ fs[])
    \\ first_x_assum drule \\ disch_then drule
    \\ strip_tac \\ fs[] \\ rveq
    >- metis_tac[]
    \\ fs[]
    \\ first_x_assum match_mp_tac
    \\ fs[env_rel_cases, libTheory.opt_bind_def]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac evaluate_sing \\ fs[] )
  >- (
    fs[compile_HD_sing]
    \\ first_x_assum match_mp_tac
    \\ fs[env_rel_cases]
    \\ fs[build_rec_env_merge]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[MAP_MAP_o, o_DEF, UNCURRY, EVERY2_MAP]
    \\ simp[Once v_rel_cases]
    \\ fs[EVERY2_refl] )
  >- fs[MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
  >- (
    drule(CONJUNCT1 pmatch_correct)
    \\ qpat_assum`s_rel _ _`(strip_assume_tac o SIMP_RULE std_ss [s_rel_cases])
    \\ disch_then drule
    \\ disch_then(qspecl_then[`p`,`v`,`[]`]mp_tac)
    \\ disch_then drule \\ fs[]
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rfs[]
    \\ fs[compile_HD_sing]
    \\ first_x_assum match_mp_tac
    \\ fs[env_rel_cases]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[]
    \\ fs[LIST_REL_EL_EQN,Once LIST_EQ_REWRITE,UNCURRY,EL_MAP]));

val dec_res_rel_def = Define `
  (dec_res_rel NONE NONE <=> T) /\
  (dec_res_rel (SOME r1) (SOME r2) <=>
     result_rel (LIST_REL v_rel) v_rel (Rerr r1) (Rerr r2)) /\
  (dec_res_rel _ _ <=> F)`;

Theorem dec_res_rel_thms[simp]:
   (!r. dec_res_rel NONE r <=> r = NONE) /\
   (!r. dec_res_rel r NONE <=> r = NONE) /\
   (!e r. dec_res_rel (SOME e) r <=>
      ?e1. r = SOME e1 /\
           result_rel (LIST_REL v_rel) v_rel (Rerr e) (Rerr e1)) /\
   (!e r. dec_res_rel r (SOME e) <=>
      ?e1. r = SOME e1 /\
           result_rel (LIST_REL v_rel) v_rel (Rerr e1) (Rerr e))
Proof
  rw [] \\ Cases_on `r` \\ rw [dec_res_rel_def]
QED

Theorem compile_dec_correct:
   ∀env (s : 'a flatSem$state) d s' r s1 env'.
    evaluate_dec env s d = (s',c,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      dec_res_rel r r1 ∧
      s_rel s' s1' ∧
      evaluate_decs env' s1 (compile_decs [d]) = (s1', {}, r1)
Proof
  Cases_on `d` >>
  simp [evaluate_decs_def, evaluate_dec_def, compile_decs_def] >>
  rpt gen_tac
  >- (
    ntac 2 TOP_CASE_TAC >>
    fs []
    >| [TOP_CASE_TAC, all_tac] >>
    rw [] >>
    drule (List.nth (CONJUNCTS compile_exp_correct, 0)) >>
    rw [] >>
    `env_rel (env with v := []) (env' with v := [])` by fs [env_rel_cases] >>
    first_x_assum drule >>
    disch_then drule >>
    rw [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    fs [] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    fs [Once v_rel_cases, libTheory.the_def] >>
    rw [] >>
    fs [Unitv_def, env_rel_cases] >>
    rw [] >>
    fs [] >>
    rfs [libTheory.the_def]) >>
  rw [] >>
  rw []
QED

val lemma = Q.prove (
  `!x. (x with c updated_by $UNION ∅) = x`,
  rw [environment_component_equality]);

Theorem compile_decs_correct:
   ∀env (s : 'a flatSem$state) ds s' r s1 env' c.
    evaluate_decs env s ds = (s',c,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      dec_res_rel r r1 ∧
      s_rel s' s1' ∧
      evaluate_decs env' s1 (compile_decs ds) = (s1', {}, r1)
Proof
  Induct_on `ds` >>
  rw [evaluate_decs_def, compile_decs_def] >>
  rw [] >>
  split_pair_case_tac >>
  fs [] >>
  drule compile_dec_correct >>
  every_case_tac >>
  fs []
  >- (
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    `env_rel (env with c updated_by $UNION new_ctors)
        (env' with c updated_by $UNION {})`
    by fs [env_rel_cases] >>
    first_x_assum drule >>
    simp [] >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    qexists_tac `s1'` >>
    qexists_tac `r1` >>
    rw [] >>
    Cases_on `h` >>
    fs [compile_decs_def, evaluate_decs_def] >>
    every_case_tac >>
    fs [lemma] >>
    rw [])
  >- (
    rveq >>
    fs [] >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    qexists_tac `s1''` >>
    qexists_tac `SOME e1` >>
    rw [] >>
    Cases_on `h` >>
    fs [compile_decs_def, evaluate_decs_def] >>
    every_case_tac >>
    fs [])
QED

Theorem compile_decs_eval_sim:
   eval_sim
     (ffi:'ffi ffi$ffi_state) T T ds1 T F
     (compile_decs ds1)
     (\p1 p2. p2 = compile_decs p1) F
Proof
  rw [eval_sim_def]
  \\ qexists_tac `0`
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ drule compile_decs_correct >>
  simp [] >>
  disch_then (qspecl_then [`initial_state ffi k`,
               ` <| v := []; c := initial_ctors; exh_pat := T; check_ctor := F |>`]
               mp_tac) >>
  impl_tac
  >- fs [initial_env_def, env_rel_cases, initial_state_def, s_rel_cases]
  \\ rw [initial_env_def] >>
  rw [] >>
  fs [s_rel_cases]
QED ;

val compile_decs_semantics = save_thm ("compile_decs_semantics",
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           compile_decs_eval_sim
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO]);

(* syntactic results *)

Theorem compile_elist_globals_eq_empty:
   !es. elist_globals es = {||} ==> elist_globals (compile es) = {||}
Proof
  ho_match_mp_tac compile_ind
  \\ rw [compile_def]
  \\ TRY
    (rename1 `HD (compile [e])`
     \\ qspec_then `e` assume_tac compile_sing \\ fs [] \\ fs [])
  \\ fs [MAP_MAP_o, o_DEF, UNCURRY, elist_globals_append]
  \\ TRY
   (map_every (fn tm => qspec_then tm assume_tac compile_sing) [`e1`,`e2`,`e3`]
    \\ fs [] \\ fs []
    \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ pop_assum mp_tac
  \\ rename1 `elist_globals (MAP _ xs)`
  \\ Induct_on `xs` \\ fs [FORALL_PROD] \\ rw []
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
  \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION] \\ rw []
  \\ rename1 `HD (compile [e])`
  \\ qspec_then `e` assume_tac compile_sing \\ fs [] \\ fs []
QED

Theorem compile_set_globals_eq_empty:
   set_globals e = {||} ==> set_globals (HD (compile [e])) = {||}
Proof
  qspec_then`[e]`mp_tac compile_elist_globals_eq_empty
  \\ rw[] \\ fs[] \\ Cases_on `compile [e]` \\ fs []
QED

Theorem compile_esgc_free:
   !es. EVERY esgc_free es ==> EVERY esgc_free (compile es)
Proof
  ho_match_mp_tac compile_ind
  \\ rw [compile_def]
  \\ fs [compile_set_globals_eq_empty]
  \\ TRY
    (rename1 `compile [e]`
     \\ qspec_then `e` assume_tac compile_sing \\ fs [] \\ fs [])
  \\ fs [EVERY_MAP, EVERY_MEM, FORALL_PROD, elist_globals_eq_empty]
  \\ fs [MEM_MAP, MAP_MAP_o, PULL_EXISTS, FORALL_PROD]
  \\ rw []
  \\ TRY(
    match_mp_tac compile_set_globals_eq_empty
    \\ res_tac )
  \\ rename1 `HD (compile [p])`
   \\ qspec_then `p` assume_tac compile_sing \\ fs [] \\ fs []
  \\ res_tac \\ fs []
QED

Theorem compile_decs_esgc_free:
   ∀ds. EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds)) ⇒
        EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (flat_uncheck_ctors$compile_decs ds)))
Proof
  Induct \\ simp[flat_uncheck_ctorsTheory.compile_decs_def]
  \\ Cases \\ simp[] \\ rw[] \\ fs[flat_uncheck_ctorsTheory.compile_decs_def]
  \\ qspec_then`[e]`mp_tac compile_esgc_free
  \\ strip_assume_tac (SPEC_ALL flat_uncheck_ctorsTheory.compile_sing)
  \\ rw[]
QED

Theorem compile_sub_bag:
   !es. (elist_globals (compile es)) ≤ (elist_globals es)
Proof
  ho_match_mp_tac compile_ind
  \\ rw [compile_def]
  \\ TRY
    (rename1 `compile [e]`
     \\ qspec_then `e` assume_tac compile_sing \\ fs [] \\ fs [])
  \\ TRY
   (map_every (fn tm => qspec_then tm assume_tac compile_sing) [`e1`,`e2`,`e3`]
    \\ fs [] \\ fs []
    \\ fs [SUB_BAG_UNION]
    \\ NO_TAC)
  \\ fs [SUB_BAG_UNION, elist_globals_append] \\ rfs []
  \\ fs [MAP_MAP_o, UNCURRY, o_DEF] \\ fs [LAMBDA_PROD]
  \\ (FIRST
    (map (fn th => match_mp_tac (MP_CANON th) \\ conj_tac >- simp[])
         (CONJUNCTS SUB_BAG_UNION)))
  \\  rename1 `elist_globals (MAP _ xs)`
  \\ ntac 2 (pop_assum kall_tac)
  \\ pop_assum mp_tac
  \\ Induct_on `xs` \\ fs [FORALL_PROD] \\ rw []
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
  \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION] \\ rw []
  \\ rename1 `HD (compile [e])`
  \\ qspec_then `e` assume_tac compile_sing \\ fs [] \\ fs []
  \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION]
QED

Theorem compile_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals es)
   ==>
   BAG_ALL_DISTINCT (elist_globals (compile es))
Proof
  metis_tac [compile_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED

Theorem compile_decs_sub_bag:
   (elist_globals (MAP dest_Dlet (FILTER is_Dlet (flat_uncheck_ctors$compile_decs ds)))) ≤ (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
Proof
  Induct_on`ds` \\ rw [flat_uncheck_ctorsTheory.compile_decs_def]
  \\ fs [UNCURRY] \\ rw []
  \\ Cases_on `h` \\ fs [flat_uncheck_ctorsTheory.compile_decs_def]
  \\ qspec_then `e` assume_tac flat_uncheck_ctorsTheory.compile_sing \\ fs []
  \\ `elist_globals [e2] <= elist_globals [e]`
    by metis_tac [compile_sub_bag]
  \\ fs [SUB_BAG_UNION]
QED

Theorem compile_decs_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))) ⇒
   BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet (flat_uncheck_ctors$compile_decs ds))))
Proof
  metis_tac [compile_decs_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED

val _ = export_theory ();
