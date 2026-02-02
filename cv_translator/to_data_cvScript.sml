(*
  Translation of the to_data compiler function.
*)
Theory to_data_cv[no_sig_docs]
Ancestors
  cv_std basis_cv backend backend_asm unify_cv infer_cv
Libs
  preamble cv_transLib

val _ = cv_memLib.use_long_names := true;

Theorem list_mem[local,cv_inline] = listTheory.MEM;

(* source_let *)

val _ = cv_trans source_letTheory.dest_Letrec_def;
val _ = cv_trans source_letTheory.dest_Let_def;
val _ = cv_trans source_letTheory.lift_let_def;
val _ = cv_trans source_letTheory.lift_lets_def;

val pre = cv_trans_pre "" source_letTheory.compile_decs_def;
Theorem source_let_compile_decs_pre[cv_pre]:
  ∀v. source_let_compile_decs_pre v
Proof
  ho_match_mp_tac source_letTheory.compile_decs_ind
  \\ rw [] \\ simp [Once pre]
QED

(* source_to_source *)

val _ = cv_trans source_to_sourceTheory.compile_def;

(* source_to_flat *)
val _ = cv_auto_trans namespaceTheory.nsEmpty_def;
val _ = cv_auto_trans namespaceTheory.nsLookup_def;
val _ = cv_auto_trans source_to_flatTheory.empty_env_def;
val _ = cv_trans flatLangTheory.pat_bindings_def;
val _ = cv_trans astTheory.pat_bindings_def;
val _ = cv_trans OPTION_JOIN_DEF;
val _ = cv_trans source_to_flatTheory.type_group_id_type_def;

Definition compile_pat_alt_def:
  (compile_pat_alt env (ast$Pvar v) = flatLang$Pvar v) ∧
  (compile_pat_alt env Pany = Pany) ∧
  (compile_pat_alt env (Plit l) = Plit l) ∧
  (compile_pat_alt env (ast$Pcon id ps) =
    flatLang$Pcon
      (OPTION_JOIN (OPTION_MAP (nsLookup env.c) id))
      (compile_pats_alt env ps)) ∧
  (compile_pat_alt env (Pref p) = Pref (compile_pat_alt env p)) ∧
  (compile_pat_alt env (Pas p i) = Pas (compile_pat_alt env p) i) ∧
  (compile_pat_alt env (Ptannot p t) = compile_pat_alt env p) ∧
  (compile_pats_alt env [] = []) ∧
  (compile_pats_alt env (p::ps) = compile_pat_alt env p::compile_pats_alt env ps)
End

val _ = cv_auto_trans (compile_pat_alt_def |> PURE_REWRITE_RULE [oneline OPTION_MAP_DEF,o_THM]);

Theorem compile_pat_alt_thm:
  (∀v env. compile_pat_alt env v = compile_pat env v) ∧
  (∀v env. compile_pats_alt env v = MAP (compile_pat env) v)
Proof
  Induct >> rw[compile_pat_alt_def,source_to_flatTheory.compile_pat_def] >> metis_tac[]
QED

val _ = cv_trans $ GSYM $ cj 1 compile_pat_alt_thm;

val pre = cv_auto_trans_pre ""
             (source_to_flatTheory.compile_exp_def
                |> PURE_REWRITE_RULE [oneline OPTION_MAP_DEF,o_THM]
                |> measure_args [2,2,2,2]);

Theorem source_to_flat_compile_exp_pre[cv_pre,local]:
  (∀t env v. source_to_flat_compile_exp_pre t env v) ∧
  (∀t env v. source_to_flat_compile_exps_pre t env v) ∧
  (∀t env v. source_to_flat_compile_pes_pre t env v) ∧
  (∀t env v. source_to_flat_compile_funs_pre t env v)
Proof
  ho_match_mp_tac source_to_flatTheory.compile_exp_ind >>
  rw[] >>
  rw[Once pre] >>
  PURE_TOP_CASE_TAC >> gvs[source_to_flatTheory.environment_fn_updates]
QED

Definition make_varls_alt_def:
  (make_varls_alt idx [] = Con None NONE []) ∧
  (make_varls_alt idx [x] = App None (GlobalVarInit idx) [Var_local None x]) ∧
  (make_varls_alt idx (x::xs) =
      Let None NONE (App None (GlobalVarInit idx) [Var_local None x])
        (make_varls_alt (idx + 1) xs):flatLang$exp)
End

val _ = cv_trans make_varls_alt_def

Theorem make_varls_alt_thm:
  ∀n tra idx xs. make_varls n tra idx xs = make_varls_alt idx xs
Proof
  ho_match_mp_tac source_to_flatTheory.make_varls_ind >>
  rw[source_to_flatTheory.make_varls_def,make_varls_alt_def]
QED

val _ = cv_trans make_varls_alt_thm

Theorem list_size_mono:
  (∀x. m x ≤ m' x) ⇒ list_size m xs ≤ list_size m' xs
Proof
  strip_tac >> Induct_on ‘xs’ >> rw[list_size_def] >>
  irule LESS_EQ_LESS_EQ_MONO >>
  rw[]
QED

Definition nsMap_alt_def:
  nsMap_alt data (Bind v m) = Bind (MAP (λ(n,x). (n,(x,data))) v) (nsMap_alts data m) ∧
  nsMap_alts data [] = [] ∧
  nsMap_alts data ((x,y)::xs) = (x,nsMap_alt data y)::nsMap_alts data xs
End

Theorem nsMap_alt_thm:
  (∀data b. nsMap_alt (data:'d) (b:('a,'b,'c) namespace) = nsMap (λtag. (tag, data)) b) ∧
  (∀data xs. nsMap_alts (data:'d) (xs:('a # ('a,'b,'c) namespace) list) = (MAP (λ(mn,e). (mn,nsMap (λtag. (tag, data)) e)) $ xs))
Proof
  ho_match_mp_tac nsMap_alt_ind >>
  rw[nsMap_alt_def,namespaceTheory.nsMap_def]
QED

val _ = cv_auto_trans nsMap_alt_def;

val _ = cv_auto_trans (source_to_flatTheory.alloc_tags_def
                         |> PURE_ONCE_REWRITE_RULE[GSYM nsMap_alt_thm])

Definition compile_decs_alt_def:
  (compile_dec_alt (t:mlstring list) n next env envs (ast$Dlet locs p e) =
     let n' = n + 4 in
     let xs = REVERSE (pat_bindings p []) in
     let e' = compile_exp (xs++t) env e in
     let l = LENGTH xs in
     let n'' = n' + l in
       (n'', (next with vidx := next.vidx + l),
        <| v := alist_to_ns (alloc_defs n' next.vidx xs); c := nsEmpty |>,
        envs,
        [flatLang$Dlet (Mat None e'
          [(compile_pat env p, make_varls 0 None next.vidx xs)])])) ∧
  (compile_dec_alt t n next env envs (ast$Dletrec locs funs) =
     let fun_names = MAP FST funs in
     let new_env = nsBindList (MAP (\x. (x, Local None x)) fun_names) env.v in
     let flat_funs = compile_funs t (env with v := new_env) funs in
     let n' = n + 1 in
     let env' = <| v := alist_to_ns (alloc_defs n' next.vidx (REVERSE fun_names));
                   c := nsEmpty |> in
       (n' + LENGTH funs, (next with vidx := next.vidx + LENGTH funs),
        env', envs,
        [flatLang$Dlet (flatLang$Letrec (join_all_names t) flat_funs
           (make_varls 0 None next.vidx (REVERSE fun_names)))])) /\
  (compile_dec_alt t n next env envs (Dtype locs type_def) =
    let new_env = MAPi (\tid (_,_,constrs). alloc_tags (next.tidx + tid) constrs) type_def in
     (n, (next with tidx := next.tidx + LENGTH type_def),
      <| v := nsEmpty;
         c := FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty new_env |>,
      envs,[])) ∧
  (compile_dec_alt _ n next env envs (Dtabbrev locs tvs tn t) =
     (n, next, empty_env, envs, [])) ∧
  (compile_dec_alt t n next env envs (Dexn locs cn ts) =
     (n, (next with eidx := next.eidx + 1),
      <| v := nsEmpty; c := nsSing cn (next.eidx, NONE) |>,
      envs,[])) ∧
  (compile_dec_alt t n next env envs (Dmod mn ds) =
     let (n', next', new_env, envs', ds') = compile_decs_alt (mn::t) n next env envs ds in
       (n', next', (lift_env mn new_env), envs', ds')) ∧
  (compile_dec_alt t n next env envs (Dlocal lds ds) =
     let (n', next1, new_env1, envs', lds') = compile_decs_alt t n next env envs lds in
     let (n'', next2, new_env2, envs'', ds') = compile_decs_alt t n' next1
        (extend_env new_env1 env) envs' ds
     in (n'', next2, new_env2, envs'', lds'++ds')) ∧
  (compile_dec_alt t n next env envs (Denv nenv) =
     (n + 1, next with vidx := next.vidx + 1,
        <| v := nsBind nenv (Glob None next.vidx) nsEmpty; c := nsEmpty |>,
        envs with <| next := envs.next + 1;
            envs := insert envs.next env envs.envs |>,
        [flatLang$Dlet (App None (GlobalVarInit next.vidx)
            [env_id_tuple envs.generation envs.next])])) ∧
  (compile_decs_alt t n next env envs [] =
    (n, next, empty_env, envs, [])) ∧
  (compile_decs_alt t n next env envs (d::ds) =
     let (n', next1, new_env1, envs1, d') = compile_dec_alt t n next env envs d in
     let (n'', next2, new_env2, envs2, ds') =
       compile_decs_alt t n' next1 (extend_env new_env1 env) envs1 ds
     in
       (n'', next2, extend_env new_env2 new_env1, envs2, d'++ds'))
End

Theorem compile_decs_cons:
  compile_decs t n next env envs (d::ds) =
     let (n', next1, new_env1, envs1, d') = compile_decs t n next env envs [d] in
     let (n'', next2, new_env2, envs2, ds') =
       compile_decs t n' next1 (extend_env new_env1 env) envs1 ds
     in
       (n'', next2, extend_env new_env2 new_env1, envs2, d'++ds')
Proof
  rw[Once $ oneline source_to_flatTheory.compile_decs_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[source_to_flatTheory.compile_decs_def]) >>
  gvs[source_to_flatTheory.extend_env_def,source_to_flatTheory.empty_env_def,
      UNCURRY_eq_pair,PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac ‘$= a1’ >> PairCases_on ‘a1’ >>
  pop_assum $ assume_tac o GSYM >>
  gvs[markerTheory.Abbrev_def] >>
  rw[source_to_flatTheory.environment_component_equality] >>
  qmatch_goalsub_abbrev_tac ‘$= a1’ >> PairCases_on ‘a1’ >>
  pop_assum $ assume_tac o GSYM >>
  gvs[markerTheory.Abbrev_def] >>
  rw[source_to_flatTheory.environment_component_equality]
QED

Theorem compile_decs_thm:
  ∀t n next env envs xs.
  compile_decs t n next env envs xs = compile_decs_alt t n next env envs xs
Proof
  ho_match_mp_tac source_to_flatTheory.compile_decs_ind >>
  PURE_ONCE_REWRITE_TAC[compile_decs_cons] >>
  rw[source_to_flatTheory.compile_decs_def,compile_decs_alt_def,source_to_flatTheory.extend_env_def,source_to_flatTheory.empty_env_def,UNCURRY_eq_pair,PULL_EXISTS,source_to_flatTheory.lift_env_def]
  >- metis_tac[FST,SND,PAIR]
  >- metis_tac[FST,SND,PAIR] >>
  res_tac >>
  simp[compile_decs_cons,UNCURRY_eq_pair,PULL_EXISTS,source_to_flatTheory.extend_env_def]
QED

val _ = cv_auto_trans (measure_args [5,5] compile_decs_alt_def)

val _ = cv_trans compile_decs_thm

val _ = cv_auto_trans source_to_flatTheory.compile_prog_def

(* flat_pattern *)

Definition compile_pat_bindings_clocked_def:
  compile_pat_bindings_clocked _ _ _ [] exp = (LN, exp) /\
  compile_pat_bindings_clocked 0 _ _ m  exp = (LN, exp) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pany, _, _) :: m) exp =
    compile_pat_bindings_clocked ck t i m exp /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pvar s, k, x) :: m) exp = (
    let (spt, exp2) = compile_pat_bindings_clocked ck t i m exp in
    (insert k () spt, Let t (SOME s) x exp2)) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Plit _, _, _) :: m) exp =
    compile_pat_bindings_clocked ck t i m exp /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pcon _ ps, k, x) :: m) exp = (
    let j_nms = MAP (\(j, p). let k = i + 1 + j in
        let nm = enc_num_to_name k in
        ((j, nm), (p, k, Var_local t nm))) (enumerate 0 ps) in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2 + LENGTH ps)
        (MAP SND j_nms ++ m) exp in
    let j_nms_used = FILTER (\(_, (_, k, _)). IS_SOME (lookup k spt)) j_nms in
    let exp3 = FOLDR (\((j, nm), _) exp.
        flatLang$Let t (SOME nm) (App t (El j) [x]) exp) exp2 j_nms_used in
    let spt2 = if NULL j_nms_used then spt else insert k () spt in
    (spt2, exp3)) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pas p v, k, x) :: m) exp = (
    let nm = enc_num_to_name (i + 1) in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2)
                      ((p, i + 1, Var_local t nm) :: m) exp in
    (insert k () spt, Let t (SOME v) x
                            (Let t (SOME nm) (Var_local t v) exp2))) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pref p, k, x) :: m) exp = (
    let nm = enc_num_to_name (i + 1) in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2)
        ((p, i + 1, Var_local t nm) :: m) exp in
    (insert k () spt, Let t (SOME nm) (App t (El 0) [x]) exp2))
End

val pre = cv_auto_trans_pre "" (compile_pat_bindings_clocked_def
                               |> PURE_REWRITE_RULE[ELIM_UNCURRY])

Theorem compile_pat_bindings_clocked_pre[cv_pre,local]:
  ∀v0 v1 v2 v exp. compile_pat_bindings_clocked_pre v0 v1 v2 v exp
Proof
  ho_match_mp_tac compile_pat_bindings_clocked_ind >>
  rw[] >>
  rw[Once $ fetch "-" "compile_pat_bindings_clocked_pre_cases"] >>
  gvs[ELIM_UNCURRY]
QED

(* TODO: Maybe move to HOL? *)
Theorem list_size_SUM:
  list_size f ls =
  LENGTH ls + SUM (MAP f ls)
Proof
  Induct_on `ls`>>rw[]
QED

Theorem compile_pat_bindings_thm:
  ∀n t i m exp.
  SUM (MAP (pat_size o FST) m) + LENGTH m ≤ n ⇒
  compile_pat_bindings_clocked n t i m exp = compile_pat_bindings t i m exp
Proof
  ho_match_mp_tac compile_pat_bindings_clocked_ind >>
  rw[compile_pat_bindings_clocked_def,flat_patternTheory.compile_pat_bindings_def,
     UNCURRY_eq_pair,PULL_EXISTS
    ]
  >- metis_tac[FST,SND,PAIR]
  >> (PRED_ASSUM is_imp mp_tac >>
      impl_tac
      >- (gvs[list_size_SUM,SUM_APPEND,
              LENGTH_enumerate, MAP_enumerate_MAPi, flat_patternTheory.MAPi_eq_MAP,
              ADD1,o_DEF,MAP_MAP_o]) >>
      strip_tac >>
      gvs[] >>
      metis_tac[FST,SND,PAIR])
QED

Theorem compile_pat_bindings_clocked_eq:
  compile_pat_bindings t i m exp = compile_pat_bindings_clocked (SUM (MAP (pat_size o FST) m) + LENGTH m) t i m exp
Proof
 irule $ GSYM compile_pat_bindings_thm >> rw[]
QED

val _ = cv_auto_trans_pre "" flatLangTheory.pat_size_def

Theorem flatLang_pat_size_pre[cv_pre]:
  (∀v. flatLang_pat_size_pre v) ∧
  (∀v. flatLang_pat1_size_pre v)
Proof
  Induct >> rw[Once $ fetch "-" "flatLang_pat_size_pre_cases"]
QED

val _ = cv_auto_trans compile_pat_bindings_clocked_eq

Definition naive_pattern_match_clocked_def:
  naive_pattern_match_clocked 0 t xs = Bool t T /\
  naive_pattern_match_clocked (SUC ck) t [] = Bool t T /\
  naive_pattern_match_clocked (SUC ck) t ((flatLang$Pany, _) :: mats) = naive_pattern_match_clocked ck t mats
  /\
  naive_pattern_match_clocked (SUC ck) t ((Pvar _, _) :: mats) = naive_pattern_match_clocked ck t mats /\
  naive_pattern_match_clocked (SUC ck) t ((Plit l, v) :: mats) = SmartIf t
    (App t Equality [v; Lit t l]) (naive_pattern_match_clocked ck t mats) (Bool t F) /\
  naive_pattern_match_clocked (SUC ck) t ((Pcon NONE ps, v) :: mats) =
    naive_pattern_match_clocked ck t (MAPi (\i p. (p, App t (El i) [v])) ps ++ mats) /\
  naive_pattern_match_clocked (SUC ck) t ((Pas p i, v) :: mats) =
    naive_pattern_match_clocked ck t ((p, v) :: mats) /\
  naive_pattern_match_clocked (SUC ck) t ((Pcon (SOME stmp) ps, v) :: mats) =
    SmartIf t (App t (TagLenEq (FST stmp) (LENGTH ps)) [v])
      (naive_pattern_match_clocked ck t (MAPi (\i p. (p, App t (El i) [v])) ps ++ mats))
      (Bool t F)
  /\
  naive_pattern_match_clocked (SUC ck) t ((Pref p, v) :: mats) =
    naive_pattern_match_clocked ck t ((p, App t (El 0) [v]) :: mats)
End

val pre = cv_auto_trans_pre "" naive_pattern_match_clocked_def

Theorem naive_pattern_match_clocked_pre[cv_pre]:
  ∀v0 t v. naive_pattern_match_clocked_pre v0 t v
Proof
  ho_match_mp_tac naive_pattern_match_clocked_ind >>
  rw[] >> rw[Once $ fetch "-" "naive_pattern_match_clocked_pre_cases"] >>
  gvs[MAPi_eq_list_mapi]
QED

Theorem naive_pattern_match_clocked_thm:
  ∀ck t xs. SUM (MAP (pat_size o FST) xs) + LENGTH xs ≤ ck ⇒
  naive_pattern_match_clocked ck t xs = naive_pattern_match t xs
Proof
  ho_match_mp_tac naive_pattern_match_clocked_ind >>
  rw[naive_pattern_match_clocked_def,flat_patternTheory.naive_pattern_match_def] >>
  (PRED_ASSUM is_imp mp_tac >>
   impl_tac
   >- (gvs[list_size_SUM,SUM_APPEND,
           LENGTH_enumerate, MAP_enumerate_MAPi, flat_patternTheory.MAPi_eq_MAP,
           ADD1,o_DEF,MAP_MAP_o]) >>
   strip_tac >>
   gvs[] >>
   metis_tac[FST,SND,PAIR])
QED

Theorem naive_pattern_matched_clocked_eq:
  naive_pattern_match t xs = naive_pattern_match_clocked (SUM (MAP (pat_size o FST) xs) + LENGTH xs) t xs
Proof
  irule $ GSYM naive_pattern_match_clocked_thm >> rw[]
QED

val _ = cv_auto_trans naive_pattern_matched_clocked_eq

Definition encode_pat_alt_def:
  encode_pat_alt (flatLang$Pany) = pattern_semantics$Any /\
  encode_pat_alt (Plit l) = Lit l /\
  encode_pat_alt (Pvar _) = Any /\
  encode_pat_alt (flatLang$Pcon stmp ps) = Cons
    (case stmp of NONE => NONE | SOME (i, NONE) => SOME (i, NONE)
        | SOME (i, SOME (ty, ctors)) => SOME (i, SOME ctors))
    (encode_pats_alt ps) /\
  encode_pat_alt (Pas p v) = encode_pat_alt p /\
  encode_pat_alt (Pref p) = Ref (encode_pat_alt p) ∧
  encode_pats_alt [] = [] ∧
  encode_pats_alt (x::xs) = encode_pat_alt x::encode_pats_alt xs
End

Theorem encode_pat_alt_thm:
  (∀p. encode_pat_alt p = encode_pat p) ∧
  (∀ps. encode_pats_alt ps = MAP encode_pat ps)
Proof
  Induct >>
  rw[encode_pat_alt_def,flat_patternTheory.encode_pat_def] >>
  metis_tac[]
QED

val _ = cv_auto_trans encode_pat_alt_def

val _ = cv_trans $ GSYM $ cj 1 encode_pat_alt_thm

Definition exh_pat_alt_def:
  exh_pat_alt Any = T /\
  exh_pat_alt (Or p1 p2) = (exh_pat_alt p1 \/ exh_pat_alt p2) /\
  exh_pat_alt (Cons NONE ps) = exh_pats_alt ps /\
  exh_pat_alt _ = F ∧
  exh_pats_alt [] = T ∧
  exh_pats_alt (x::xs) = (exh_pat_alt x ∧ exh_pats_alt xs)
End

val _ = cv_trans exh_pat_alt_def

Theorem exh_pat_alt_thm:
  (∀p. exh_pat_alt p = exh_pat p) ∧
  (∀ps. exh_pats_alt ps = EVERY exh_pat ps)
Proof
  Induct >>
  rw[exh_pat_alt_def,pattern_compTheory.exh_pat_def] >>
  rename1 ‘Cons cc’ >> Cases_on ‘cc’ >>
  rw[exh_pat_alt_def,pattern_compTheory.exh_pat_def] >>
  metis_tac[]
QED

val _ = cv_trans $ GSYM $ cj 1 exh_pat_alt_thm

Definition sib_exists_alt_def:
  sib_exists_alt [] t l = F ∧
  sib_exists_alt ((Cons (SOME (t1,_)) ps) :: xs) t l =
    (if (t = t1 ∧ l = LENGTH ps) then T else sib_exists_alt xs t l) ∧
  sib_exists_alt _ _ _ = F
End

val _ = cv_trans sib_exists_alt_def

Theorem sib_exists_alt_thm:
  ∀xs tl. sib_exists xs tl = sib_exists_alt xs (FST tl) (SND tl)
Proof
  simp[FORALL_PROD] >>
  recInduct sib_exists_alt_ind >>
  rw[sib_exists_alt_def,pattern_compTheory.sib_exists_def] >>
  metis_tac[]
QED

val _ = cv_trans sib_exists_alt_thm

val _ = cv_auto_trans pattern_compTheory.exh_rows_def

val _ = cv_auto_trans pattern_compTheory.pat_to_guard_def

val _ = cv_auto_trans flat_patternTheory.compile_pats_def

val _ = cv_trans_rec flat_patternTheory.sum_string_ords_def
  (wf_rel_tac ‘measure $ λ(x,y). cv_size(cv_mlstring_strlen y) - cv_size x’ >>
   cv_termination_tac >>
   gvs[cvTheory.c2b_def,oneline cvTheory.cv_lt_def0,AllCaseEqs(),
       oneline cvTheory.b2c_def])

val pre = cv_trans_pre "" flat_patternTheory.dec_name_to_num_def

Theorem flat_pattern_dec_name_to_num_pre[cv_pre]:
  ∀name. flat_pattern_dec_name_to_num_pre name
Proof
  rw[fetch "-" "flat_pattern_dec_name_to_num_pre_cases"] >>
  Cases_on ‘name’ >> gvs[]
QED

Definition compile_exp_alt_def:
  (compile_exp_alt cfg (Var_local t vid) =
    (dec_name_to_num vid, F, Var_local t vid)) /\
  (compile_exp_alt cfg (Raise t x) =
    let (i, sg, y) = compile_exp_alt cfg x in
    (i, sg, Raise t y)) /\
  (compile_exp_alt cfg (Handle t x ps) =
    let (i, sgx, y) = compile_exp_alt cfg x in
    let (j, sgp, ps2) = compile_match_alt cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k in
    let v = Var_local t nm in
    let r = Raise t v in
    let exp = compile_pats cfg sgp t k v r ps2 in
    (k, sgx \/ sgp, Handle t y [(Pvar nm, exp)])) /\
  (compile_exp_alt cfg (Con t ts xs) =
    let (i, sg, ys) = compile_exp_alts_alt cfg (REVERSE xs) in
    (i, sg, Con t ts (REVERSE ys))) /\
  (compile_exp_alt cfg (Fun t vs x) =
    let (i, sg, y) = compile_exp_alt cfg x in
    (i, sg, Fun t vs y)) /\
  (compile_exp_alt cfg (App t op xs) =
    let (i, sg, ys) = compile_exp_alts_alt cfg (REVERSE xs) in
    (i, sg \/ op_sets_globals op, App t op (REVERSE ys))) /\
  (compile_exp_alt cfg (Mat t x ps) =
    let (i, sgx, y) = compile_exp_alt cfg x in
    let (j, sgp, ps2) = compile_match_alt cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k in
    let v = Var_local t nm in
    let r = Raise t (Con t (SOME (bind_tag, NONE)) []) in
    let exp = compile_pats cfg sgp t k v r ps2 in
    (k, sgx \/ sgp, Let t (SOME nm) y exp)) /\
  (compile_exp_alt cfg (Let t v x1 x2) =
    let (i, sg1, y1) = compile_exp_alt cfg x1 in
    let (j, sg2, y2) = compile_exp_alt cfg x2 in
    let k = (case v of NONE => 0 | SOME vid => dec_name_to_num vid) in
    (MAX i (MAX j k), sg1 \/ sg2, Let t v y1 y2)) /\
  (compile_exp_alt cfg (flatLang$Letrec t fs x) =
    let ys = compile_letexps_alt cfg fs in
    let (i, sgx, y) = compile_exp_alt cfg x in
    let j = MAX_LIST (MAP (\(_,_,(j,_,_)). j) ys) in
    let sgfs = EXISTS (\(_,_,(_,sg,_)). sg) ys in
    let fs2 = MAP (\(a, b, (_, _, exp)). (a, b, exp)) ys in
    (MAX i j, sgfs \/ sgx, flatLang$Letrec t fs2 y)) /\
  (compile_exp_alt cfg (If t x1 x2 x3) =
    let (i, sg1, y1) = compile_exp_alt cfg x1 in
    let (j, sg2, y2) = compile_exp_alt cfg x2 in
    let (k, sg3, y3) = compile_exp_alt cfg x3 in
    (MAX i (MAX j k), sg1 \/ sg2 \/ sg3, SmartIf t y1 y2 y3)) /\
  (compile_exp_alt cfg exp = (0, F, exp)) /\
  (compile_exp_alts_alt cfg [] = (0, F, [])) /\
  (compile_exp_alts_alt cfg (x::xs) =
    let (i, sgx, y) = compile_exp_alt cfg x in
    let (j, sgy, ys) = compile_exp_alts_alt cfg xs in
    (MAX i j, sgx \/ sgy, y :: ys)) /\
  (compile_letexps_alt cfg [] = []) ∧
  (compile_letexps_alt cfg ((a,b,c)::xs) =
   (a,b,compile_exp_alt cfg c)::compile_letexps_alt cfg xs) ∧
  (compile_match_alt cfg [] = (0, F, [])) /\
  (compile_match_alt cfg ((p, x)::ps) =
    let (i, sgx, y) = compile_exp_alt cfg x in
    let j = max_dec_name (pat_bindings p []) in
    let (k, sgp, ps2) = compile_match_alt cfg ps in
    (MAX i (MAX j k), sgx \/ sgp, ((p, y) :: ps2)))
End

(* TODO: move *)
Theorem cv_REV_size:
  ∀x acc. cv_size(cv_REV x acc) ≤ cv_size x + cv_size acc
Proof
  Induct_on ‘x’ >>
  rw[] >>
  rw[Once cv_stdTheory.cv_REV_def] >>
  irule LESS_EQ_TRANS >>
  first_x_assum $ irule_at $ Pos hd >>
  rw[]
QED

(* TODO: move *)
Theorem cv_REVERSE_size:
  ∀x. cv_size(cv_REVERSE x) ≤ cv_size x
Proof
  simp[cv_REVERSE_def] >>
  Cases
  >- (rw[Once cv_REV_def]) >>
  irule_at (Pos hd) LESS_EQ_TRANS >>
  irule_at (Pos hd) cv_REV_size >>
  simp[]
QED

val pre = cv_auto_trans_pre_rec "" compile_exp_alt_def
  (WF_REL_TAC `measure (\x. case x of INL (_, x) => cv_size x
                                   | INR (INL (_, xs)) => cv_size xs
                                   | INR (INR (INL (_, ps))) => cv_size ps
                                   | INR (INR (INR (_, ps))) => cv_size ps)` >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_REVERSE_size >>
   rw[])

Theorem compile_exp_alt_pre[cv_pre]:
  (∀cfg v. compile_exp_alt_pre cfg v) ∧
  (∀cfg v. compile_exp_alts_alt_pre cfg v) ∧
  (∀cfg v. compile_letexps_alt_pre cfg v) ∧
  (∀cfg v. compile_match_alt_pre cfg v)
Proof
  ho_match_mp_tac compile_exp_alt_ind >>
  rw[] >>
  rw[Once $ fetch "-" "compile_exp_alt_pre_cases"]
QED

Theorem compile_exp_alt_thm:
  (∀cfg exp. compile_exp_alt cfg exp = compile_exp cfg exp) ∧
  (∀cfg xs. compile_exp_alts_alt cfg xs = compile_exps cfg xs) /\
  (∀cfg xs. compile_letexps_alt cfg xs = MAP (λ(x,y,z). (x,y,compile_exp cfg z)) xs) ∧
  (∀cfg xs. compile_match_alt cfg xs = compile_match cfg xs)
Proof
  ho_match_mp_tac compile_exp_alt_ind >>
  rw[compile_exp_alt_def,flat_patternTheory.compile_exp_def] >>
  rpt(pairarg_tac >> gvs[])
QED

val _ = cv_trans $ GSYM $ cj 1 compile_exp_alt_thm

val _ = cv_trans flat_patternTheory.compile_dec_def

(* flat_elim *)

val _ = cv_auto_trans_pre "" flat_elimTheory.has_Eval_def;

Theorem flat_elim_has_Eval_pre[cv_pre]:
  (∀v. flat_elim_has_Eval_pre v) ∧
  (∀v. flat_elim_has_Eval_list_pre v) ∧
  (∀v. flat_elim_has_Eval_pats_pre v) ∧
  (∀v. flat_elim_has_Eval_funs_pre v)
Proof
  ho_match_mp_tac flat_elimTheory.has_Eval_ind >>
  rw[] >> rw[Once $ fetch "-" "flat_elim_has_Eval_pre_cases"]
QED

Theorem cv_size_map_snd:
  ∀z. cv_size(cv_map_snd z) ≤ cv_size z
Proof
  Induct >> rw[] >>
  rw[Once cv_stdTheory.cv_map_snd_def] >>
  Cases_on ‘z’ >> rw[]
QED

val pre = cv_auto_trans_pre_rec "" (flat_elimTheory.find_loc_def |> PURE_REWRITE_RULE[o_DEF,GSYM MAP_MAP_o])
  (WF_REL_TAC `measure (λ e . case e of
                              | INL x => cv_size x
                              | INR y => cv_size y)` >>
   cv_termination_tac
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[]))
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[]))
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[])))

Theorem flat_elim_find_loc_pre[cv_pre]:
  (∀v. flat_elim_find_loc_pre v) ∧
  (∀v. flat_elim_find_locL_pre v)
Proof
  ho_match_mp_tac flat_elimTheory.find_loc_ind >>
  rw[] >> rw[Once $ fetch "-" "flat_elim_find_loc_pre_cases"] >>
  rw[MAP_MAP_o]
QED

val pre = cv_auto_trans_pre_rec "" (flat_elimTheory.find_lookups_def |> PURE_REWRITE_RULE[GSYM MAP_MAP_o,o_THM])
  (WF_REL_TAC `measure (λ e . case e of
                              | INL x => cv_size x
                              | INR y => cv_size y)` >>
   cv_termination_tac
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[]))
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[]))
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_size_map_snd >>
       rw[oneline cvTheory.cv_snd_def] >>
       rpt(PURE_FULL_CASE_TAC >> gvs[])))

Theorem flat_elim_find_lookups_pre[cv_pre]:
  (∀v. flat_elim_find_lookups_pre v) ∧
  (∀v. flat_elim_find_lookupsL_pre v)
Proof
  ho_match_mp_tac flat_elimTheory.find_lookups_ind >>
  rw[] >> rw[Once pre] >> gvs[GSYM MAP_MAP_o]
QED

val _ = cv_auto_trans flat_elimTheory.total_pat_def;

Definition is_pure_alt_def:
    (is_pure_alt (Handle t e pes) = is_pure_alt e) ∧
    (is_pure_alt (Lit t l) = T) ∧
    (is_pure_alt (Con t id_option es) = is_pure_alts es) ∧
    (is_pure_alt (Var_local t str) = T) ∧
    (is_pure_alt (Fun t name body) = T) ∧
    (is_pure_alt (App t (GlobalVarInit g) es) = is_pure_alts es) ∧
    (is_pure_alt (If t e1 e2 e3) = (is_pure_alt e1 ∧ is_pure_alt e2 ∧ is_pure_alt e3)) ∧
    (is_pure_alt (Mat t e1 pes) =
      (is_pure_alt e1 ∧ is_pure_alts (MAP SND pes) ∧ EXISTS total_pat (MAP FST pes))) ∧
    (is_pure_alt (Let t opt e1 e2) = (is_pure_alt e1 ∧ is_pure_alt e2)) ∧
    (is_pure_alt (Letrec t funs e) = is_pure_alt e) ∧
    (is_pure_alt _ = F) ∧
    (is_pure_alts [] = T) ∧
    (is_pure_alts (x::xs) = (is_pure_alt x ∧ is_pure_alts xs))
Termination
  WF_REL_TAC `measure (λ e . sum_CASE e exp_size $ list_size exp_size)` >>
  rw[list_size_pair_size_MAP_FST_SND]
End

val pre = cv_auto_trans_pre_rec "" is_pure_alt_def
  (WF_REL_TAC `measure (λ e . sum_CASE e cv_size cv_size)` >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem is_pure_alt_pre[cv_pre]:
  (∀v. is_pure_alt_pre v) ∧
  (∀v. is_pure_alts_pre v)
Proof
  ho_match_mp_tac is_pure_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem is_pure_alt_thm:
  (∀v. is_pure_alt v = is_pure v) ∧
  (∀v. is_pure_alts v = EVERY is_pure v)
Proof
  ho_match_mp_tac is_pure_alt_ind >>
  rw[is_pure_alt_def,flat_elimTheory.is_pure_def] >>
  metis_tac[]
QED

val _ = cv_trans $ GSYM $ cj 1 is_pure_alt_thm

Definition is_hidden_alt_def:
    (is_hidden_alt (Raise t e) = is_hidden_alt e) ∧
    (is_hidden_alt (Handle t e pes) = F) ∧
    (is_hidden_alt (Lit t l) = T) ∧
    (is_hidden_alt (Con t id_option es) = is_hidden_alts es) ∧
    (is_hidden_alt (Var_local t str) = T) ∧
    (is_hidden_alt (Fun t name body) = T) ∧
    (is_hidden_alt (App t Opapp l) = F) ∧
    (is_hidden_alt (App t (GlobalVarInit g) [e]) = is_hidden_alt e) ∧
    (is_hidden_alt (App t (GlobalVarLookup g) [e]) = F) ∧
    (is_hidden_alt (If t e1 e2 e3) = (is_hidden_alt e1 ∧ is_hidden_alt e2 ∧ is_hidden_alt e3)) ∧
    (is_hidden_alt (Mat t e1 [p,e2]) = (is_hidden_alt e1 ∧ is_hidden_alt e2)) ∧
    (is_hidden_alt (Let t opt e1 e2) = (is_hidden_alt e1 ∧ is_hidden_alt e2)) ∧
    (is_hidden_alt (Letrec t funs e) = is_hidden_alt e) ∧
    (is_hidden_alt _ = F) ∧
    (is_hidden_alts [] = T) ∧
    (is_hidden_alts (x::xs) = (is_hidden_alt x ∧ is_hidden_alts xs))
End

val pre = cv_trans_pre "" is_hidden_alt_def

Theorem is_hidden_alt_pre[cv_pre]:
  (∀v. is_hidden_alt_pre v) ∧
  (∀v. is_hidden_alts_pre v)
Proof
  ho_match_mp_tac is_hidden_alt_ind >>
  rw[] >> rw[Once $ fetch "-" "is_hidden_alt_pre_cases"]
QED

Theorem is_hidden_alt_thm:
  (∀v. is_hidden_alt v = is_hidden v) ∧
  (∀v. is_hidden_alts v = EVERY is_hidden v)
Proof
  ho_match_mp_tac is_hidden_alt_ind >>
  rw[is_hidden_alt_def,flat_elimTheory.is_hidden_def] >>
  metis_tac[]
QED

val _ = cv_trans $ GSYM $ cj 1 is_hidden_alt_thm

Definition spt_fold_union_def:
  (spt_fold_union acc LN = acc) ∧
  (spt_fold_union acc (LS a) = sptree$union a acc) ∧
  (spt_fold_union acc (BN t1 t2) = spt_fold_union (spt_fold_union acc t1) t2) ∧
  (spt_fold_union acc (BS t1 a t2) = spt_fold_union (union a $ spt_fold_union acc t1) t2)
End

Theorem spt_fold_union_thm:
  ∀acc t. spt_fold_union acc t = spt_fold union acc t
Proof
  Induct_on ‘t’ >> rw[spt_fold_def,spt_fold_union_def]
QED

val _ = cv_trans spt_fold_union_def

val pre = cv_auto_trans_pre "" (spt_closureTheory.closure_spt_def |> PURE_REWRITE_RULE[GSYM spt_fold_union_thm])

Theorem spt_closure_closure_spt_pre[cv_pre]:
  ∀reachable tree. spt_closure_closure_spt_pre reachable tree
Proof
  ho_match_mp_tac spt_closureTheory.closure_spt_ind >>
  rw[] >> rw[Once pre] >>
  gvs[spt_fold_union_thm]
QED

val _ = cv_auto_trans flat_elimTheory.remove_flat_prog_def;

val _ = cv_auto_trans backend_asmTheory.to_flat_def;

(* flat_to_clos *)

val _ = cv_auto_trans flat_to_closTheory.compile_op_def

Theorem list_size_thm:
  list_size f xs = LENGTH xs + SUM(MAP f xs)
Proof
  Induct_on ‘xs’ >> gvs[list_size_def]
QED

Definition flat_to_clos_compile_alt_def:
  (flat_to_clos_compile_alts m [] = []) /\
  (flat_to_clos_compile_alts m (x::xs) = flat_to_clos_compile_alt m x :: flat_to_clos_compile_alts m xs) /\
  (flat_to_clos_compile_alt m (flatLang$Raise t e) = (closLang$Raise t (flat_to_clos_compile_alt m (e)))) /\
  (flat_to_clos_compile_alt m (Lit t l) = (compile_lit t l)) /\
  (flat_to_clos_compile_alt m (Var_local t v) = (Var t (findi (SOME v) m))) /\
  (flat_to_clos_compile_alt m (Con t n es) =
     let tag = (case n of SOME (t,_) => t | _ => 0) in
       (SmartCons t tag (flat_to_clos_compile_alts m (REVERSE es)))) /\
  (flat_to_clos_compile_alt m (App t op es) =
     case dest_nop op es of
     | SOME e => flat_to_clos_compile_alt m e
     | NONE => (compile_op t op (flat_to_clos_compile_alts m (REVERSE es)))) /\
  (flat_to_clos_compile_alt m (Fun t v e) =
     (Fn t NONE NONE 1 (flat_to_clos_compile_alt (SOME v::m) (e)))) /\
  (flat_to_clos_compile_alt m (If t x1 x2 x3) =
     (If t (flat_to_clos_compile_alt m (x1))
           (flat_to_clos_compile_alt m (x2))
           (flat_to_clos_compile_alt m (x3)))) /\
  (flat_to_clos_compile_alt m (Let t vo e1 e2) =
     (Let t [flat_to_clos_compile_alt m (e1)] (flat_to_clos_compile_alt (vo::m) (e2)))) /\
  (flat_to_clos_compile_alt m (Mat t e pes) = (Op t (IntOp (Const 0)) [])) /\
  (flat_to_clos_compile_alt m (Handle t e pes) =
     case dest_pat pes of
     | SOME (v,h) => (Handle t (flat_to_clos_compile_alt m (e)) (flat_to_clos_compile_alt (SOME v::m) (h)))
     | _ => flat_to_clos_compile_alt m (e)) /\
  (flat_to_clos_compile_alt m (Letrec t funs e) =
     let new_m = MAP (\n. SOME (FST n)) funs ++ m in
       (Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
          (flat_to_clos_compile_lets_alt new_m funs)
          (flat_to_clos_compile_alt new_m (e)))) ∧
  (flat_to_clos_compile_lets_alt m [] = []) /\
  (flat_to_clos_compile_lets_alt m ((f,v,x)::xs) = (1, flat_to_clos_compile_alt (SOME v :: m) x) :: flat_to_clos_compile_lets_alt m xs)
Termination
  WF_REL_TAC ‘measure $ λx.
             case x of
               INL (m, e) => list_size exp_size e
             | INR (INL (m,e)) => exp_size e
             | INR (INR (m,e)) => list_size (exp_size o SND o SND) e’ >>
  rw[list_size_pair_size_MAP_FST_SND] >>
  gvs[oneline flat_to_closTheory.dest_pat_def,AllCaseEqs(),
      oneline flat_to_closTheory.dest_nop_def,
      MAP_REVERSE,SUM_REVERSE,SUM_APPEND
     ]
End

val _ = cv_auto_trans flat_to_closTheory.dest_nop_def
val _ = cv_auto_trans flat_to_closTheory.dest_pat_def

val pre = cv_auto_trans_pre_rec "" flat_to_clos_compile_alt_def
  (wf_rel_tac ‘measure $ λx.
                           case x of
                             INL (m, e) => cv_size e
                           | INR (INL (m,e)) => cv_size e
                           | INR (INR (m,e)) => cv_size e’ >>
   cv_termination_tac
   >~ [‘cv_REVERSE’]
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_REVERSE_size >>
       rw[])
   >~ [‘cv_REVERSE’]
   >- (irule LESS_EQ_LESS_TRANS >>
       irule_at (Pos last) cv_REVERSE_size >>
       rw[]) >>
   gvs[fetch "-" "cv_flat_to_clos_dest_nop_def",
       fetch "-" "cv_flat_to_clos_dest_pat_def",
       AllCaseEqs()] >>
   simp[oneline cvTheory.cv_snd_def, oneline cvTheory.cv_fst_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem flat_to_clos_compile_alts_pre[cv_pre]:
  (∀m v. flat_to_clos_compile_alts_pre m v) ∧
  (∀m v. flat_to_clos_compile_alt_pre m v) ∧
  (∀m v. flat_to_clos_compile_lets_alt_pre m v)
Proof
  ho_match_mp_tac flat_to_clos_compile_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem flat_to_clos_compile_alt_thm:
  (∀m xs. flat_to_clos_compile_alts m xs = compile m xs) ∧
  (∀m x. flat_to_clos_compile_alt m x = HD(compile m [x])) ∧
  (∀m xs. flat_to_clos_compile_lets_alt m xs =
         (MAP ( \ (f,v,x). (1, HD (compile (SOME v :: m) [x]))) xs))
Proof
  ho_match_mp_tac flat_to_clos_compile_alt_ind >>
  rw[flat_to_clos_compile_alt_def,flat_to_closTheory.compile_def]
  >- (Cases_on ‘xs’ >>
      gvs[flat_to_closTheory.compile_def,flat_to_closTheory.LENGTH_compile]) >>
  rpt(PURE_TOP_CASE_TAC >> gvs[])
QED

val _ = cv_trans $ GSYM $ cj 1 flat_to_clos_compile_alt_thm

val pre = cv_auto_trans_pre_rec "" closLangTheory.has_install_def
  (wf_rel_tac ‘measure $ λx. sum_CASE x cv_size cv_size’ >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem closLang_has_install_pre[cv_pre]:
  (∀v. closLang_has_install_pre v) ∧
  (∀v. closLang_has_install_list_pre v)
Proof
  ho_match_mp_tac closLangTheory.has_install_ind >>
  rw[] >> rw[Once pre]
QED

val _ = cv_auto_trans flat_to_closTheory.compile_prog_def

(* to_clos *)

val _ = cv_trans backend_asmTheory.to_clos_def

(* clos_mti *)

val _ = cv_trans (clos_mtiTheory.collect_args_def |> measure_args [2])

val _ = cv_trans (clos_mtiTheory.collect_apps_def |> measure_args [2])

Definition intro_multi_alt_def:
  (intro_multi_alt 0 max_app exp = (Var (SourceLoc 0 0 0 0) 0)) ∧
  (intro_multi_alt (SUC ck) max_app (closLang$Var t n) = (Var t n)) ∧
  (intro_multi_alt (SUC ck) max_app (If t e1 e2 e3) =
   (If t ((intro_multi_alt ck max_app (e1)))
         ((intro_multi_alt ck max_app (e2)))
         ((intro_multi_alt ck max_app (e3))))) ∧
  (intro_multi_alt (SUC ck) max_app (Let t es e) =
    (Let t (intro_multis_alt ck max_app es) ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Raise t e) =
    (Raise t ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Handle t e1 e2) =
    (Handle t ((intro_multi_alt ck max_app (e1))) ((intro_multi_alt ck max_app (e2))))) ∧
  (intro_multi_alt (SUC ck) max_app (Tick t e) =
    (Tick t ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Call t ticks n es) =
    (Call t ticks n (intro_multis_alt ck max_app es))) ∧
  (intro_multi_alt (SUC ck) max_app (App t NONE e es) =
    let (es', e') = collect_apps max_app es e in
      (App t NONE ((intro_multi_alt ck max_app (e'))) (intro_multis_alt ck max_app es'))) ∧
  (intro_multi_alt (SUC ck) max_app (App t (SOME l) e es) =
    (App t (SOME l) ((intro_multi_alt ck max_app (e))) (intro_multis_alt ck max_app es))) ∧
  (intro_multi_alt (SUC ck) max_app (Fn t NONE NONE num_args e) =
    let (num_args', e') = collect_args max_app num_args e in
      (Fn t NONE NONE num_args' ((intro_multi_alt ck max_app (e'))))) ∧
  (intro_multi_alt (SUC ck) max_app (Fn t loc fvs num_args e) =
      (Fn t loc fvs num_args ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Letrec t NONE NONE funs e) =
    (Letrec t NONE NONE (intro_multi_collect_alt ck max_app funs)
            ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Letrec t (SOME loc) fvs funs e) =
     (Letrec t (SOME loc) fvs funs ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Letrec t NONE (SOME fvs) funs e) =
     (Letrec t NONE (SOME fvs) funs ((intro_multi_alt ck max_app (e))))) ∧
  (intro_multi_alt (SUC ck) max_app (Op t op es) =
    (Op t op (intro_multis_alt ck max_app es))) ∧
  (intro_multis_alt 0 max_app _ = []) ∧
  (intro_multis_alt (SUC ck) max_app [] = []) ∧
  (intro_multis_alt (SUC ck) max_app (e1::es) =
    intro_multi_alt ck max_app e1 :: intro_multis_alt ck max_app es) ∧
  (intro_multi_collect_alt 0 max_app _ = []) ∧
  (intro_multi_collect_alt (SUC ck) max_app [] = []) ∧
  (intro_multi_collect_alt (SUC ck) max_app ((num_args,e)::fs) =
   let (num_args',e') = collect_args max_app num_args e in
     ((num_args', intro_multi_alt ck max_app e') :: intro_multi_collect_alt ck max_app fs))
Termination
  WF_REL_TAC `measure $ λx. case x of
                            | INL(n,_,_) => n
                            | INR(INL(n,_,_)) => n
                            | INR(INR(n,_,_)) => n`
End

Definition exp_size_alt_def:
  exp_size_alt (closLang$Var x y) = 1:num ∧
  exp_size_alt (If a b c d) = 1 + exp_size_alt b + exp_size_alt c + exp_size_alt d ∧
  exp_size_alt (Let a es e) = 1 + exp_size_alt e + exp_sizes_alt es ∧
  exp_size_alt (Handle a0 a1 a2) = 1 + exp_size_alt a1 + exp_size_alt a2 ∧
  exp_size_alt (Raise a0 a1) = 1 + exp_size_alt a1 ∧
  exp_size_alt (Tick a0 a1) = 1 + exp_size_alt a1 ∧
  exp_size_alt (Call a0 a1 a2 a3) = 1 + exp_sizes_alt a3 ∧
  exp_size_alt (App a0 a1 a2 a3) = 1 + exp_size_alt a2 + exp_sizes_alt a3 ∧
  exp_size_alt (Fn a0 a1 a2 a3 a4) = 1 + exp_size_alt a4 ∧
  exp_size_alt (Letrec a0 a1 a2 a3 a4) = 1 + exp_sizes_alt (MAP SND a3) + exp_size_alt a4 ∧
  exp_size_alt (Op a0 a1 a2) = 1 + exp_sizes_alt a2 ∧
  exp_sizes_alt [] = 0 ∧
  exp_sizes_alt (x::xs) = 1 + exp_size_alt x + exp_sizes_alt xs
Termination
  WF_REL_TAC `measure $ λx. case x of
                              INL e => exp_size e
                            | INR es => list_size exp_size es` >>
  rw[list_size_pair_size_MAP_FST_SND]
End

val pre = cv_auto_trans_pre_rec "" exp_size_alt_def
  (WF_REL_TAC `measure $ λx. case x of
                              INL e => cv_size e
                            | INR es => cv_size es` >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem exp_size_alt_pre[cv_pre]:
  (∀v. exp_size_alt_pre v) ∧
  (∀v. exp_sizes_alt_pre v)
Proof
  ho_match_mp_tac exp_size_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem exp_sizes_alt_cons:
  exp_sizes_alt (x::xs) = 1 + exp_size_alt x + exp_sizes_alt xs
Proof
  Cases_on ‘xs’ >> rw[exp_size_alt_def]
QED

Theorem exp_sizes_alt_append:
  ∀xs ys. exp_sizes_alt (xs ++ ys) = exp_sizes_alt xs + exp_sizes_alt ys
Proof
  Induct_on ‘xs’ >> rw[exp_sizes_alt_cons] >> rw[exp_size_alt_def]
QED

val pre = cv_auto_trans_pre "" intro_multi_alt_def

Theorem intro_multi_alt_pre[cv_pre]:
  (∀v0 max_app v. intro_multi_alt_pre v0 max_app v) ∧
  (∀v0 max_app v. intro_multis_alt_pre v0 max_app v) ∧
  (∀v0 max_app v. intro_multi_collect_alt_pre v0 max_app v)
Proof
  ho_match_mp_tac intro_multi_alt_ind >>
  rw[] >>
  rw[Once pre]
QED

Theorem exp_size_alt_pos[simp]:
  ∀e. exp_size_alt e = 0 ⇔ F
Proof
  Cases >> rw[exp_size_alt_def]
QED

Theorem exp_sizes_alt_pos[simp]:
  ∀es. exp_sizes_alt es = 0 ⇔ es = []
Proof
  Cases >> rw[exp_size_alt_def]
QED

Theorem collect_apps_size_alt:
  ∀max_app args e args' e'.
    collect_apps max_app args e = (args',e') ⇒
    exp_size_alt e' ≤ exp_size_alt e
Proof
  recInduct clos_mtiTheory.collect_apps_ind >>
  rw[exp_size_alt_def,clos_mtiTheory.collect_apps_def] >>
  gvs[exp_size_alt_def]
QED

Theorem collect_apps_sizes_alt:
  ∀max_app args e args' e'.
    collect_apps max_app args e = (args',e') ⇒
    exp_size_alt e' + exp_sizes_alt args' ≤ exp_size_alt e + exp_sizes_alt args
Proof
  recInduct clos_mtiTheory.collect_apps_ind >>
  rw[exp_size_alt_def,clos_mtiTheory.collect_apps_def] >>
  gvs[exp_size_alt_def,exp_sizes_alt_append]
QED

Theorem collect_args_size_alt:
  ∀max_app args e args' e'.
    collect_args max_app args e = (args',e') ⇒
    exp_size_alt e' ≤ exp_size_alt e
Proof
  recInduct clos_mtiTheory.collect_args_ind >>
  rw[exp_size_alt_def,clos_mtiTheory.collect_args_def] >>
  gvs[exp_size_alt_def]
QED

Theorem intro_multi_cons:
  ∀e es. intro_multi max_app (e::es) = HD(intro_multi max_app [e])::intro_multi max_app es
Proof
  Induct_on ‘es’ >> gvs[clos_mtiTheory.intro_multi_def,clos_mtiTheory.intro_multi_length]
QED

Theorem intro_multi_thm:
  (∀ck max_app e. exp_size_alt e ≤ ck ⇒ intro_multi_alt ck max_app e = HD(intro_multi max_app [e])) ∧
  (∀ck max_app es. exp_sizes_alt es ≤ ck ⇒ intro_multis_alt ck max_app es = intro_multi max_app es) ∧
  (∀ck max_app es. exp_sizes_alt(MAP SND es) ≤ ck ⇒ intro_multi_collect_alt ck max_app es =
                                           MAP (\(num_args, e).
                                                              let (num_args', e') = collect_args max_app num_args e in
                                                                (num_args', HD (intro_multi max_app [e'])))
                                               es)
Proof
  ho_match_mp_tac intro_multi_alt_ind >>
  rw[exp_size_alt_def,intro_multi_alt_def,clos_mtiTheory.intro_multi_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  imp_res_tac collect_args_size_alt >>
  imp_res_tac collect_apps_sizes_alt >>
  gvs[] >>
  CONV_TAC $ RHS_CONV $ PURE_ONCE_REWRITE_CONV [intro_multi_cons] >>
  gvs[]
QED

Theorem intro_multi_alt_eq:
  intro_multi max_app es = intro_multis_alt (exp_sizes_alt es) max_app es
Proof
  irule $ GSYM $ cj 2 intro_multi_thm >>
  rw[]
QED

val _ = cv_trans intro_multi_alt_eq

val _ = cv_trans clos_mtiTheory.compile_def

(* clos_number *)

val pre = cv_trans_pre_rec "" clos_numberTheory.renumber_code_locs_def
  (wf_rel_tac ‘measure $ λx. sum_CASE x (cv_size o SND) (cv_size o SND)’ >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem clos_number_renumber_code_locs_list_pre[cv_pre]:
  (∀n v. clos_number_renumber_code_locs_list_pre n v) ∧
  (∀n v. clos_number_renumber_code_locs_pre n v)
Proof
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind >>
  rw[] >> rw[Once pre]
QED

(* clos_known *)

Definition get_size_sc_aux_alt_def:
  (get_size_sc_aux_alt n (Var t v) = n - 1) /\
  (get_size_sc_aux_alt n (If t x1 x2 x3) =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alt n x1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alt n x2 in if n = 0 then 0 else
       get_size_sc_aux_alt n x3) /\
  (get_size_sc_aux_alt n (Let t xs x2) =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alts n xs in if n = 0 then 0 else
       get_size_sc_aux_alt n x2) /\
  (get_size_sc_aux_alt n (Raise t x1) =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux_alt n x1) /\
  (get_size_sc_aux_alt n (Handle t x1 x2) =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alt n x1 in if n = 0 then 0 else
       get_size_sc_aux_alt n x2) /\
  (get_size_sc_aux_alt n (Op t op xs) =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux_alts n xs) /\
  (get_size_sc_aux_alt n (Tick t x) = get_size_sc_aux_alt n x) /\
  (get_size_sc_aux_alt n (Call t ticks dest xs) =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux_alts n xs) /\
  (get_size_sc_aux_alt n (Fn t loc_opt ws_opt num_args x1) =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux_alt n x1) /\
  (get_size_sc_aux_alt n (Letrec t loc_opt ws_opt fns x1) =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alts n (MAP SND fns) in if n = 0 then 0 else
       get_size_sc_aux_alt n x1) /\
  (get_size_sc_aux_alt n (App t loc_opt x1 xs) =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux_alt n x1 in if n = 0 then 0 else
       get_size_sc_aux_alts n xs) ∧
  (get_size_sc_aux_alts n [] = n) /\
  (get_size_sc_aux_alts n (x::xs) =
     if n = 0n then n else
       let n = get_size_sc_aux_alt n x in if n = 0 then n else
         get_size_sc_aux_alts n xs)
Termination
  WF_REL_TAC `measure $ λx. sum_CASE x (exp_size o SND) (list_size exp_size o SND)`
  \\ rw[list_size_pair_size_MAP_FST_SND]
End

val pre = cv_auto_trans_pre_rec "" get_size_sc_aux_alt_def
  (WF_REL_TAC `measure $ λx. sum_CASE x (cv_size o SND) (cv_size o SND)` >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem get_size_sc_aux_alt_pre[cv_pre]:
  (∀n v. get_size_sc_aux_alt_pre n v) ∧
  (∀n v. get_size_sc_aux_alts_pre n v)
Proof
  ho_match_mp_tac get_size_sc_aux_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem get_size_aux_sc_alt_thm:
  (∀n v. get_size_sc_aux_alt n v = get_size_sc_aux n [v]) ∧
  (∀n vs. get_size_sc_aux_alts n vs = get_size_sc_aux n vs)
Proof
  ho_match_mp_tac get_size_sc_aux_alt_ind >>
  rw[get_size_sc_aux_alt_def,clos_knownTheory.get_size_sc_aux_def] >>
  gvs[]
  >- gvs[clos_knownTheory.get_size_sc_aux_correct] >>
  Cases_on ‘vs’ >> gvs[clos_knownTheory.get_size_sc_aux_def]
QED

val _ = cv_trans $ GSYM $ cj 2 get_size_aux_sc_alt_thm

val _ = cv_trans $ GSYM $ cj 2 get_size_aux_sc_alt_thm

val _ = cv_trans clos_knownTheory.get_size_sc_def

Definition free_alt_def:
  (free_alt (closLang$Var t v) = ((closLang$Var t v), db_vars$Var v)) /\
  (free_alt (If t x1 x2 x3) =
     let (c1,l1) = free_alt (x1) in
     let (c2,l2) = free_alt (x2) in
     let (c3,l3) = free_alt (x3) in
       ((If t ( c1) ( c2) ( c3)),mk_Union l1 (mk_Union l2 l3))) /\
  (free_alt (Let t xs x2) =
     let (c1,l1) = free_alts xs in
     let (c2,l2) = free_alt (x2) in
       ((Let t c1 ( c2)),mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (free_alt (Raise t x1) =
     let (c1,l1) = free_alt (x1) in
       ((Raise t ( c1)),l1)) /\
  (free_alt (Tick t x1) =
     let (c1,l1) = free_alt (x1) in
       ((Tick t ( c1)),l1)) /\
  (free_alt (Op t op xs) =
     let (c1,l1) = free_alts xs in
       ((Op t op c1),l1)) /\
  (free_alt (App t loc_opt x1 xs2) =
     let (c1,l1) = free_alt (x1) in
     let (c2,l2) = free_alts xs2 in
       ((App t loc_opt ( c1) c2),mk_Union l1 l2)) /\
  (free_alt (Fn t loc _ num_args x1) =
     let (c1,l1) = free_alt (x1) in
     let l2 = Shift num_args l1 in
       ((Fn t loc (SOME (vars_to_list l2)) num_args ( c1)),l2)) /\
  (free_alt (Letrec t loc _ fns x1) =
     let m = LENGTH fns in
     let res = free_let_alts m fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
     let (c2,l2) = free_alt (x1) in
       ((Letrec t loc (SOME (vars_to_list l1)) c1 ( c2)),
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (free_alt (Handle t x1 x2) =
     let (c1,l1) = free_alt (x1) in
     let (c2,l2) = free_alt (x2) in
       ((Handle t ( c1) ( c2)),mk_Union l1 (Shift 1 l2))) /\
  (free_alt (Call t ticks dest xs) =
     let (c1,l1) = free_alts xs in
       ((Call t ticks dest c1),l1)) ∧
  (free_alts [] = ([],Empty)) /\
  (free_alts ((x:closLang$exp)::xs) =
     let (c1,l1) = free_alt x in
     let (c2,l2) = free_alts xs in
       (c1::c2,mk_Union l1 l2)) ∧
  (free_let_alts m [] = []) /\
  (free_let_alts m ((n,x)::xs) =
   let (c,l) = free_alt (x)
   in
     ((n, c),Shift (n + m) l)::free_let_alts m xs)
Termination
  WF_REL_TAC `measure $ λa. case a of
                            | INL x => closLang$exp_size x
                            | INR(INL xs) => list_size exp_size xs
                            | INR(INR(_,xs)) => list_size exp_size (MAP SND xs)` >>
  rw[list_size_pair_size_MAP_FST_SND]
End

val pre = cv_auto_trans_pre "" (free_alt_def |> measure_args [0,0,1])

Theorem free_alt_pre[cv_pre]:
  (∀v. free_alt_pre v) ∧
  (∀v. free_alts_pre v) ∧
  (∀m v. free_let_alts_pre m v)
Proof
  ho_match_mp_tac free_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem free_LENGTH_LEMMA[local]:
  !xs ys s1. free xs = (ys,s1) ⇒ LENGTH xs = LENGTH ys
Proof
  recInduct clos_knownTheory.free_ind \\ rpt strip_tac
  \\ gvs [clos_knownTheory.free_def,UNCURRY_eq_pair]
QED

Theorem free_alt_thm:
  (∀v. free_alt v = (λ(x,y). (HD x, y)) $ free [v]) ∧
  (∀v. free_alts v = free v) ∧
  (∀m v. free_let_alts m v =
         MAP (\(n,x). let (c,l) = free [x] in
                        ((n,HD c),Shift (n + m) l)) v)
Proof
  ho_match_mp_tac free_alt_ind >>
  rw[free_alt_def,clos_knownTheory.free_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  imp_res_tac free_LENGTH_LEMMA >>
  gvs[LENGTH_EQ_1] >>
  rename1 ‘free (_::xx)’ >> Cases_on ‘xx’ >> gvs[] >>
  gvs[clos_knownTheory.free_def]
QED

val _ = cv_trans $ GSYM $ cj 2 free_alt_thm

val _ = cv_auto_trans clos_knownTheory.closed_def

Definition contains_closures_alt_def:
  (contains_closures_alt (closLang$Var t v) = F) /\
  (contains_closures_alt (If t x1 x2 x3) =
     if contains_closures_alt (x1) then T else
     if contains_closures_alt (x2) then T else
       contains_closures_alt (x3)) /\
  (contains_closures_alt (Let t xs x2) =
     if contains_closures_alts xs then T else
       contains_closures_alt (x2)) /\
  (contains_closures_alt (Raise t x1) = contains_closures_alt (x1)) /\
  (contains_closures_alt (Handle t x1 x2) =
     if contains_closures_alt (x1) then T else
       contains_closures_alt (x2)) /\
  (contains_closures_alt (Op t op xs) = contains_closures_alts xs) /\
  (contains_closures_alt (Tick t x) = contains_closures_alt (x)) /\
  (contains_closures_alt (Call t ticks dest xs) = contains_closures_alts xs) /\
  (contains_closures_alt (Fn t loc_opt ws_opt num_args x1) = T) /\
  (contains_closures_alt (Letrec t loc_opt ws_opt fns x1) = T) /\
  (contains_closures_alt (App t loc_opt x1 xs) =
     if contains_closures_alt (x1) then T else
       contains_closures_alts xs) ∧
  (contains_closures_alts [] = F) /\
  (contains_closures_alts (x::xs) =
    if contains_closures_alt x then T else
      contains_closures_alts xs)
End

val pre = cv_auto_trans_pre "" contains_closures_alt_def

Theorem contains_closures_alt_pre[cv_pre]:
  (∀v. contains_closures_alt_pre v) ∧
  (∀v. contains_closures_alts_pre v)
Proof
  Induct >> rw[] >> rw[Once pre]
QED

Theorem contains_closures_cons:
  ∀v vs. contains_closures(v::vs) = (contains_closures [v] ∨ contains_closures vs)
Proof
  Induct_on ‘vs’ >>
  gvs[clos_knownTheory.contains_closures_def]
QED

Theorem contains_closures_alt_thm:
  (∀v. contains_closures_alt v = contains_closures [v]) ∧
  (∀v. contains_closures_alts v = contains_closures v)
Proof
  Induct >> rw[contains_closures_alt_def,clos_knownTheory.contains_closures_def] >>
  metis_tac[contains_closures_cons]
QED

val _ = cv_trans $ GSYM $ cj 2 contains_closures_alt_thm

Definition merge_alt_def:
  (merge_alt Impossible y = y) ∧
  (merge_alt x Impossible = x) ∧
  (merge_alt (Tuple tg1 xs) (Tuple tg2 ys) =
     if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then Tuple tg1 (merge_alts xs ys)
     else Other) ∧
  (merge_alt (ClosNoInline m1 n1) (ClosNoInline m2 n2) =
     if m1 = m2 ∧ n1 = n2
       then ClosNoInline m1 n1 else Other) ∧
  (merge_alt (Clos m1 n1 e1 s1) (Clos m2 n2 e2 s2) =
     if m1 = m2 ∧ n1 = n2 /\ e1 = e2 /\ s1 = s2
       then Clos m1 n1 e1 s1 else Other) ∧
  (merge_alt (Int i) (Int j) = if i = j then Int i else Other) ∧
  (merge_alt _ _ = Other) ∧
  (merge_alts (x::xs) (y::ys) =
   merge_alt x y::merge_alts xs ys) ∧
  (merge_alts _ _ = [])
End

val pre = cv_auto_trans_pre "" merge_alt_def

Theorem merge_alt_pre[cv_pre]:
  (∀v0 v. merge_alt_pre v0 v) ∧
  (∀v0 v. merge_alts_pre v0 v)
Proof
  ho_match_mp_tac merge_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem merge_alt_thm:
  (∀v0 v. merge_alt v0 v = merge v0 v) ∧
  (∀v0 v. merge_alts v0 v = MAP2 merge v0 v)
Proof
  ho_match_mp_tac merge_alt_ind >>
  rw[merge_alt_def,clos_knownTheory.merge_def]
QED

val _ = cv_trans $ GSYM $ cj 1 merge_alt_thm

val pre = cv_trans_pre "" clos_knownTheory.known_op_def

Theorem clos_known_known_op_pre[cv_pre]:
  ∀v as g. clos_known_known_op_pre v as g
Proof
  ho_match_mp_tac clos_knownTheory.known_op_ind >>
  rw[] >> rw[Once pre] >>
  intLib.COOPER_TAC
QED

val _ = cv_trans clos_knownTheory.clos_approx_def

val _ = cv_trans clos_knownTheory.clos_gen_noinline_def

val _ = cv_trans clos_knownTheory.isGlobal_def

val _ = cv_trans clos_knownTheory.gO_destApx_def

val _ = cv_trans clos_knownTheory.mk_Ticks_def

Definition pure_alt_def:
  (pure_alt (Var _ _) ⇔ T)
    ∧
  (pure_alt (If _ e1 e2 e3) ⇔ pure_alt e1 ∧ pure_alt e2 ∧ pure_alt e3)
    ∧
  (pure_alt (Let _ es e2) ⇔ pure_alts es ∧ pure_alt e2)
    ∧
  (pure_alt (Raise _ _) ⇔ F)
    ∧
  (pure_alt (Handle _ e1 e2) ⇔ pure_alt e1)
    ∧
  (pure_alt (Tick _ _) ⇔ F)
    ∧
  (pure_alt (Call _ _ _ _) ⇔ F)
    ∧
  (pure_alt (App _ _ _ _) ⇔ F)
    ∧
  (pure_alt (Fn _ _ _ _ _) ⇔ T)
    ∧
  (pure_alt (Letrec _ _ _ _ x) ⇔ pure_alt x)
    ∧
  (pure_alt (Op _ opn es) ⇔ pure_alts es ∧ pure_op opn)
    ∧
  (pure_alts [] = T)
    ∧
  (pure_alts (x::xs) ⇔ pure_alt x ∧ pure_alts xs)
End

val pre = cv_auto_trans_pre "" pure_alt_def

Theorem pure_alt_pre[cv_pre]:
  (∀v. pure_alt_pre v) ∧
  (∀v. pure_alts_pre v)
Proof
  Induct >>
  rw[] >> rw[Once pre]
QED

Theorem pure_alt_thm:
  (∀v. pure_alt v = pure v) ∧
  (∀v. pure_alts v = EVERY pure v)
Proof
  Induct >> rw[pure_alt_def,closLangTheory.pure_def] >>
  metis_tac[]
QED

val _ = cv_trans $ GSYM $ cj 1 pure_alt_thm

Definition decide_inline_alt_def:
  decide_inline_alt c fapx app_lopt app_arity =
    case fapx of
      | ClosNoInline loc arity =>
          if app_lopt = NONE /\ app_arity = arity
            then inlD_Annotate loc
            else inlD_Nothing
      | Clos loc arity body body_size =>
          if app_lopt = NONE /\ app_arity = arity then
            (if body_size < c * (1 + app_arity) /\
                ~contains_closures [body] /\
                closed (Fn (strlit "") NONE NONE app_arity body)
                (* Consider moving these checks to the point where Clos approximations
                   are created, and bake them into the val_approx_val relation. *)
               then inlD_LetInline body
               else inlD_Annotate loc)
          else inlD_Nothing
      | _ => inlD_Nothing
End

val _ = cv_auto_trans decide_inline_alt_def

Theorem decide_inline_alt_thm:
  decide_inline c fapx app_lopt app_arity = decide_inline_alt c.inline_factor fapx app_lopt app_arity
Proof
  rw[clos_knownTheory.decide_inline_def,decide_inline_alt_def]
QED

Theorem decide_inline_alt_LetInline:
   !c fapx lopt arity body.
     decide_inline_alt c fapx lopt arity = inlD_LetInline body ==> 0 < c
Proof
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_alt_def, bool_case_eq]
  \\ spose_not_then assume_tac \\ fs []
QED

Definition known_alt_def:
  (known_alt inl_factor inl_max (Var t v) vs g =
     (((Var t v,any_el v vs Other)),g)) /\
  (known_alt inl_factor inl_max (If t x1 x2 x3) vs g =
     let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
     let (ea2,g) = known_alt inl_factor inl_max (x2) vs g in
     let (ea3,g) = known_alt inl_factor inl_max (x3) vs g in
     let (e1,a1) = ea1 in
     let (e2,a2) = ea2 in
     let (e3,a3) = ea3 in
       (((If t e1 e2 e3), merge a2 a3),g)) /\
  (known_alt inl_factor inl_max (Let t xs x2) vs g =
     let (ea1,g) = known_alts inl_factor inl_max xs vs g in
     let (ea2,g) = known_alt inl_factor inl_max (x2) (MAP SND ea1 ++ vs) g in
     let (e2,a2) = ea2 in
       (((Let t (MAP FST ea1) e2, a2)),g)) /\
  (known_alt inl_factor inl_max (Raise t x1) vs g =
     let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
     let (e1,a1) = ea1 in
       (((Raise t e1,Impossible)),g)) /\
  (known_alt inl_factor inl_max (Tick t x1) vs g =
     let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
     let (e1,a1) = ea1 in
       (((Tick t e1,a1)),g)) /\
  (known_alt inl_factor inl_max (Handle t x1 x2) vs g =
     let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
     let (ea2,g) = known_alt inl_factor inl_max (x2) (Other::vs) g in
     let (e1,a1) = ea1 in
     let (e2,a2) = ea2 in
       (((Handle t e1 e2,merge a1 a2)),g)) /\
  (known_alt inl_factor inl_max (Call t ticks dest xs) vs g =
     let (ea1,g) = known_alts inl_factor inl_max xs vs g in
       (((Call t ticks dest (MAP FST ea1),Other)),g)) /\
  (known_alt inl_factor inl_max (Op t op xs) vs g =
     let (ea1,g) = known_alts inl_factor inl_max xs vs g in
     let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
     let e =
         (if isGlobal op then
           case gO_destApx a of
             | gO_None => SmartOp t op (MAP FST ea1)
             | gO_Int i => Op t (IntOp (Const i)) (MAP FST ea1)
             | gO_NullTuple tag => Op t (BlockOp (Cons tag)) (MAP FST ea1)
          else SmartOp t op (MAP FST ea1))
     in
       (((e,a)),g)) /\
  (known_alt inl_factor inl_max (App t loc_opt x xs) vs g =
     let (ea2,g) = known_alts inl_factor inl_max xs vs g in
     let (ea1,g) = known_alt inl_factor inl_max (x) vs g in
     let (e1,a1) = ea1
     in
       case decide_inline_alt inl_factor a1 loc_opt (LENGTH xs) of
         | inlD_Nothing => (((App t loc_opt e1 (MAP FST ea2), Other)), g)
         | inlD_Annotate new_loc => (((App t (SOME new_loc) e1 (MAP FST ea2), Other)), g)
         | inlD_LetInline body =>
             let (eabody,_) = known_alt (inl_factor DIV 2) inl_max (body) (MAP SND ea2) g in
             let (ebody, abody) = eabody in
               if pure x then
                 (* We don't have to evaluate x *)
                 (((Let (t§0) (MAP FST ea2)
                              (mk_Ticks t 1 (LENGTH xs) ebody), abody)), g)
               else
                 (* We need to evaluate x for its side-effects,
                    but we must do so after evaluating the args. *)
                 (((Let (t§0) (SNOC e1 (MAP FST ea2))
                              (mk_Ticks t 1 (LENGTH xs) ebody), abody)), g)) /\
  (known_alt inl_factor inl_max (Fn t loc_opt ws_opt num_args x1) vs g =
     let (ea1,g) = known_alt inl_factor inl_max (x1) (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = ea1 in
       (((Fn t loc_opt NONE num_args body,
          case loc_opt of
            | SOME loc => clos_approx inl_max loc num_args x1
            | NONE => Other)), g)) /\
  (known_alt inl_factor inl_max (Letrec t loc_opt _ fns x1) vs g =
     let clos = case loc_opt of
                   NONE => REPLICATE (LENGTH fns) Other
                |  SOME loc => clos_gen_noinline loc 0 fns in
     (* The following ignores SetGlobal within fns, but it shouldn't
        appear there, and missing it just means this opt will do less. *)
     let new_fns = known_let_alts clos vs inl_factor inl_max g fns in
     let (ea1,g) = known_alt inl_factor inl_max (x1) (clos ++ vs) g in
     let (e1,a1) = ea1 in
       (((Letrec t loc_opt NONE new_fns e1,a1)),g)) ∧
  (known_alts inl_factor inl_max [] vs (g:val_approx spt) = ([],g)) /\
  (known_alts inl_factor inl_max ((x:closLang$exp)::xs) vs g =
     let (eas1,g) = known_alt inl_factor inl_max (x) vs g in
     let (eas2,g) = known_alts inl_factor inl_max (xs) vs g in
       (eas1::eas2,g)) ∧
  (known_let_alts _ _ _ _ _ [] = []) ∧
  (known_let_alts clos vs inl_factor inl_max g ((num_args,x)::xs) =
   let
     new_vs = REPLICATE num_args Other ++ clos ++ vs;
     res = known_alt inl_factor inl_max x new_vs g
   in
     (num_args,FST (FST res))::known_let_alts clos vs inl_factor inl_max g xs)
Termination
  wf_rel_tac `inv_image (measure I LEX measure I)
                        (λx. case x of
                               INL (c,_,x,vs,g) => (c, closLang$exp_size x)
                             | INR(INL (c,_,xs,vs,g)) => (c, list_size closLang$exp_size xs)
                             | INR(INR (clos,vs,c,_,g,xs)) => (c, list_size (pair_size (λx. x) exp_size) xs))`
  \\ rw[clos_knownTheory.dec_inline_factor_def]
  \\ imp_res_tac decide_inline_alt_LetInline \\ fs []
End

val pre = cv_auto_trans_pre_rec "" clos_opTheory.lift_exps_def
  (fn x =>
     (wf_rel_tac ‘measure $ λx. cv_size(FST x)’ >>
      cv_termination_tac >>
      gvs[fetch "-" "cv_dest_Op_dest_Cons_def",AllCaseEqs(),
          cvTheory.c2b_def,cvTheory.cv_lt_def0,
          cvTheory.b2c_if,
          oneline cvTheory.cv_ispair_def,
          fetch "-" "cv_clos_op_dest_Cons_def"
         ] >>
      gvs[oneline cvTheory.cv_fst_def,
          oneline cvTheory.cv_snd_def,
          AllCaseEqs()])
     x)

Theorem clos_op_lift_exps_pre[cv_pre]:
  ∀v n binds. clos_op_lift_exps_pre v n binds
Proof
  ho_match_mp_tac clos_opTheory.lift_exps_ind >>
  rw[] >> rw[Once pre]
QED

Definition eq_pure_list_alt:
  eq_pure_list_alt (SUC ck) [(x,y)] =
   (case eq_direct x y of
    | SOME z => List [z]
    | NONE =>
      case dest_Op dest_Cons x, dest_Op dest_Cons y of
      | (NONE, NONE) => List [Op None (BlockOp Equal) [x;y]]
      | (SOME (t1,xs), SOME (t2,ys)) =>
           if t1 ≠ t2 ∨ LENGTH xs ≠ LENGTH ys then List [MakeBool F]
           else eq_pure_list_alt ck (ZIP (REVERSE xs, REVERSE ys))
      | (SOME (t1,xs), NONE) =>
           Append (List [Op None (BlockOp (TagLenEq t1 (LENGTH xs))) [y]])
                  (eq_pure_list_alt ck (MAPi (λi x. (x, Op None (BlockOp (ElemAt i)) [y])) (REVERSE xs)))
      | (NONE, SOME (t1,ys)) => eq_pure_list_alt ck [(y,x)]) ∧
  eq_pure_list_alt (SUC ck) (xy::xys) = Append (eq_pure_list_alt ck [xy]) (eq_pure_list_alt ck xys) ∧
  eq_pure_list_alt _ _ = Nil
End

val _ = cv_auto_trans_pre "" eq_pure_list_alt

Theorem eq_pure_list_alt_pre[cv_pre]:
  ∀v0 v. eq_pure_list_alt_pre v0 v
Proof
  ho_match_mp_tac eq_pure_list_alt_ind >> rw[] >>
  rw[Once $ fetch "-" "eq_pure_list_alt_pre_cases"] >>
  rw[] >>
  gvs[cv_stdTheory.MAPi_eq_list_mapi]
QED

Theorem SUM_MAP_const[local] =
  SUM_MAP_PLUS
        |> CONV_RULE SWAP_FORALL_CONV
        |> Q.SPEC ‘K x’
        |> SIMP_RULE std_ss [MAP_K_REPLICATE,SUM_REPLICATE];

Theorem eq_pure_list_alt_thm:
  ∀ck xs. SUM (MAP (λ(x,y). 1 + cons_measure x + cons_measure y +
                             if cons_measure x < cons_measure y then 1 else 0) xs) ≤ ck ⇒ eq_pure_list_alt ck xs = eq_pure_list xs
Proof
  recInduct eq_pure_list_alt_ind >> rpt strip_tac >>
  gvs[] >>
  rw[eq_pure_list_alt,Once clos_opTheory.eq_pure_list_def] >>
  rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >> gvs[GSYM cv_stdTheory.MAPi_eq_list_mapi]) >>
  imp_res_tac clos_opTheory.cons_measure_lemma >>
  gvs[UNCURRY_eq_pair] >>
  rpt(pairarg_tac >> gvs[])
  >- (first_x_assum irule >>
      gvs[o_DEF] >>
      gvs[clos_opTheory.cons_measure_lemma,MAP_REVERSE,SUM_REVERSE,SUM_MAP_const])
  >- (first_x_assum irule >>
      gvs[GSYM REVERSE_ZIP,MAP_REVERSE,SUM_REVERSE] >>
      rename1 ‘ZIP (xs, ys)’ >>
      qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
      irule LESS_EQ_TRANS >>
      Q.SUBGOAL_THEN
        ‘SUM (MAP f (ZIP (xs, ys)))
         ≤ SUM(MAP (λx. cons_measure x + 1) xs) + SUM(MAP (λx. cons_measure x + 1) ys)’
        $ irule_at $ Pos hd >>
      unabbrev_all_tac
      >- (qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac >>
          rpt $ pop_assum kall_tac >>
          MAP_EVERY qid_spec_tac [‘ys’,‘xs’] >>
          Induct >>
          Cases_on ‘ys’ >>
          rw[] >>
          first_x_assum drule >>
          gvs[]) >>
      gvs[SUM_MAP_const])
  >- (first_x_assum irule >>
      gvs[GSYM REVERSE_ZIP,MAP_REVERSE,SUM_REVERSE] >>
      rename1 ‘ZIP (xs, ys)’ >>
      qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
      irule LESS_EQ_TRANS >>
      Q.SUBGOAL_THEN
        ‘SUM (MAP f (ZIP (xs, ys)))
         ≤ SUM(MAP (λx. cons_measure x + 1) xs) + SUM(MAP (λx. cons_measure x + 1) ys)’
        $ irule_at $ Pos hd >>
      unabbrev_all_tac
      >- (qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac >>
          rpt $ pop_assum kall_tac >>
          MAP_EVERY qid_spec_tac [‘ys’,‘xs’] >>
          Induct >>
          Cases_on ‘ys’ >>
          rw[] >>
          first_x_assum drule >>
          gvs[]) >>
      gvs[SUM_MAP_const])
QED

Theorem eq_pure_list_alt_eq:
  ∀xs. eq_pure_list xs = eq_pure_list_alt
                         (SUM (MAP (λ(x,y). 1 + cons_measure x + cons_measure y +
                                            if cons_measure x < cons_measure y then 1 else 0) xs)) xs
Proof
  strip_tac >> irule $ GSYM eq_pure_list_alt_thm >> rw[]
QED

Definition cons_measure_alt_def:
  cons_measure_alt x =
  (case dest_Op dest_Cons x of
   | NONE => 0
   | SOME (_,xs) => cons_measures_alt xs + LENGTH xs + 1) ∧
  cons_measures_alt [] = 0 ∧
  cons_measures_alt (x::xs) = cons_measure_alt x + cons_measures_alt xs
Termination
  WF_REL_TAC ‘measure $ λx. sum_CASE x exp_size (list_size exp_size)’ >>
  gvs[oneline clos_opTheory.dest_Op_def,AllCaseEqs(),PULL_EXISTS,
      oneline clos_opTheory.dest_Cons_def]
End

val pre = cv_trans_pre_rec "" cons_measure_alt_def
  (wf_rel_tac ‘measure $ λx. sum_CASE x cv_size cv_size’ >>
   cv_termination_tac >>
   gvs[fetch "-" "cv_dest_Op_dest_Cons_def",AllCaseEqs(),
       cvTheory.c2b_def,cvTheory.cv_lt_def0,
       cvTheory.b2c_if,
       oneline cvTheory.cv_ispair_def,
       fetch "-" "cv_clos_op_dest_Cons_def"
      ] >>
   gvs[oneline cvTheory.cv_fst_def,
       oneline cvTheory.cv_snd_def,
       AllCaseEqs()])

Theorem cons_measure_alt_pre[cv_pre]:
  (∀x. cons_measure_alt_pre x) ∧
  (∀v. cons_measures_alt_pre v)
Proof
  ho_match_mp_tac cons_measure_alt_ind >>
  rw[] >> rw[Once pre]
QED

Theorem cons_measure_pmatch_elim[local] = clos_opTheory.cons_measure_def
                                        |> CONV_RULE $ QUANT_CONV $ RHS_CONV $ patternMatchesLib.PMATCH_ELIM_CONV;

Theorem cons_measure_alt_thm:
  (∀x. cons_measure_alt x = cons_measure x) ∧
  (∀v. cons_measures_alt v = SUM(MAP cons_measure v))
Proof
  reverse Induct >> rw[] >>
  PURE_ONCE_REWRITE_TAC [cons_measure_pmatch_elim, cons_measure_alt_def]
  >- (gvs[] >> rw[Once cons_measure_pmatch_elim]) >>
  gvs[oneline clos_opTheory.dest_Op_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

val _ = cv_auto_trans $ GSYM $ cj 1 cons_measure_alt_thm

val _ = cv_auto_trans (eq_pure_list_alt_eq |> PURE_REWRITE_RULE  [GSYM cons_measure_alt_thm])

val _ = cv_auto_trans clos_opTheory.int_op_def;

Theorem cv_mul_zero:
  cv_mul (cv$Num 0) x = cv$Num 0
Proof
  Cases_on ‘x’ \\ gvs []
QED

Theorem cv_lt_zero:
  cv_lt x (cv$Num 0) = cv$Num 0
Proof
  Cases_on ‘x’ \\ gvs []
QED

Theorem cv_lt_eq_SUC[local]:
  cv_lt x y = cv$Num(SUC k) ⇔
  k = 0 ∧ ∃n m. x = cv$Num n ∧ y = cv$Num m ∧ n < m
Proof
  Cases_on ‘x’ >> gvs[cvTheory.cv_lt_def0] >>
  PURE_TOP_CASE_TAC >> gvs[oneline cvTheory.b2c_def] >>
  rw[]
QED

(* why doesn't online cvTheory.cv_mul_def achieve this?*)
Theorem cv_mul_oneline:
  cv_mul x y =
  case (x,y) of
    (cv$Num m, cv$Num n) => cv$Num(m*n)
  | _ => cv$Num 0
Proof
  Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[]
QED

Theorem cv_add_oneline:
  cv_add x y =
  case (x,y) of
    (cv$Num m, cv$Num n) => cv$Num(m+n)
  | (cv$Num m, _) => cv$Num m
  | (_, cv$Num n) => cv$Num n
  | _ => cv$Num 0
Proof
  Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[]
QED

val pre = cv_auto_trans_pre_rec "" known_alt_def
  (wf_rel_tac `inv_image (measure I LEX measure I)
              (λx. case x of
                     INL (c,_,x,vs,g) => (cv_size c, cv_size x)
                   | INR(INL (c,_,xs,vs,g)) => (cv_size c, cv_size xs)
                   | INR(INR (clos,vs,c,_,g,xs)) => (cv_size c, cv_size xs))` >>
   cv_termination_tac >>
   gvs[cvTheory.c2b_def,oneline cvTheory.cv_ispair_def,AllCaseEqs(),
       fetch "-" "cv_decide_inline_alt_def",
       cvTheory.cv_eq_def,
       cvTheory.cv_lt_def0,
       oneline cvTheory.b2c_def
      ] >>
   simp[oneline cvTheory.cv_snd_def, oneline cvTheory.cv_fst_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
   gvs[cv_mul_zero, cv_lt_zero,cv_lt_eq_SUC] >>
   gvs[cv_mul_oneline,AllCaseEqs(),cv_add_oneline]
   >- intLib.COOPER_TAC >>
   rename1 ‘m DIV 2’ >>
   ‘m ≠ 0’ by(strip_tac >> gvs[]) >>
   gvs[])

Theorem known_alt_pre[cv_pre]:
  (∀inl_factor inl_max v vs g. known_alt_pre inl_factor inl_max v vs g) ∧
  (∀inl_factor inl_max v vs g. known_alts_pre inl_factor inl_max v vs g) ∧
  (∀v1 v2 v3 v4 v5 v. known_let_alts_pre v1 v2 v3 v4 v5 v)
Proof
  ho_match_mp_tac known_alt_ind >> rw[] >> rw[Once pre]
QED

Theorem known_alt_thm:
  (∀inf inm v vs g c.
    inf = c.inline_factor ∧ inm = c.inline_max_body_size ⇒
    known_alt c.inline_factor c.inline_max_body_size v vs g =
    (λ(x,y). (HD x, y)) (known c [v] vs g)) ∧
  (∀inf inm v vs g c.
    inf = c.inline_factor ∧ inm = c.inline_max_body_size ⇒
    known_alts c.inline_factor c.inline_max_body_size v vs g =
    known c v vs g) ∧
  (∀clos vs inf inm g fns c.
    inf = c.inline_factor ∧ inm = c.inline_max_body_size ⇒
    known_let_alts clos vs c.inline_factor c.inline_max_body_size g fns =
    MAP (λ(num_args,x).
           let new_vs = REPLICATE num_args Other ++ clos ++ vs in
             let res = known c [x] new_vs g in
               (num_args,FST (HD (FST res)))) fns)
Proof
  ho_match_mp_tac known_alt_ind >>
  rw[known_alt_def,clos_knownTheory.known_def] >>
  rpt(pairarg_tac ORELSE IF_CASES_TAC  ORELSE PURE_FULL_CASE_TAC >> gvs[decide_inline_alt_thm])
  >- (imp_res_tac clos_knownTheory.known_sing_EQ_E >> gvs[] >>
      gvs[UNCURRY_eq_pair,PULL_EXISTS,PULL_FORALL] >>
      gvs[clos_knownTheory.dec_inline_factor_def] >>
      rpt $ first_x_assum $ qspec_then ‘c with inline_factor := c.inline_factor DIV 2’ strip_assume_tac >> gvs[])
  >- (imp_res_tac clos_knownTheory.known_sing_EQ_E >> gvs[] >>
      gvs[UNCURRY_eq_pair,PULL_EXISTS,PULL_FORALL] >>
      gvs[clos_knownTheory.dec_inline_factor_def] >>
      rpt $ first_x_assum $ qspec_then ‘c with inline_factor := c.inline_factor DIV 2’ strip_assume_tac >> gvs[])
  >- (imp_res_tac clos_knownTheory.known_sing_EQ_E >> gvs[] >>
      gvs[UNCURRY_eq_pair,PULL_EXISTS,PULL_FORALL] >>
      gvs[clos_knownTheory.dec_inline_factor_def] >>
      imp_res_tac clos_knownTheory.known_LENGTH_EQ_E >>
      rename1 ‘known _ (_::vvs)’ >>
      Cases_on ‘vvs’ >>
      gvs[clos_knownTheory.known_def])
QED

val _ = cv_auto_trans $
  resolve_then.gen_resolve_then Any EQ_REFL (cj 2 known_alt_thm)
  (fn thm => resolve_then.gen_resolve_then Any EQ_REFL thm GSYM)

val pre = cv_auto_trans_pre "" (clos_fvsTheory.remove_fvs_sing_def |> measure_args [1,1,2])

Theorem clos_fvs_remove_fvs_sing_pre[cv_pre]:
  (∀fvs v. clos_fvs_remove_fvs_sing_pre fvs v) ∧
  (∀fvs v. clos_fvs_remove_fvs_list_pre fvs v) ∧
  (∀m fvs v. clos_fvs_remove_fvs_let_pre m fvs v)
Proof
  ho_match_mp_tac clos_fvsTheory.remove_fvs_sing_ind >> rw[] >> rw[Once pre]
QED

val _ = cv_trans $ cj 2 clos_fvsTheory.remove_fvs_sing_eq

val _ = cv_auto_trans clos_fvsTheory.compile_def

val pre = cv_auto_trans_pre "" clos_ticksTheory.remove_ticks_sing_def

Theorem clos_ticks_remove_ticks_sing_pre[cv_pre]:
  (∀v. clos_ticks_remove_ticks_sing_pre v) ∧
  (∀v. clos_ticks_remove_ticks_list_pre v) ∧
  (∀v. clos_ticks_remove_ticks_let_pre v)
Proof
  ho_match_mp_tac clos_ticksTheory.remove_ticks_sing_ind >> rw[] >> rw[Once pre]
QED

val _ = cv_trans $ cj 2 clos_ticksTheory.remove_ticks_sing_eq

val pre = cv_auto_trans_pre "" clos_letopTheory.let_op_sing_def

Theorem clos_letop_let_op_sing_pre[cv_pre]:
  (∀v. clos_letop_let_op_sing_pre v) ∧
  (∀v. clos_letop_let_op_list_pre v) ∧
  (∀v. clos_letop_let_op_let_pre v)
Proof
  ho_match_mp_tac clos_letopTheory.let_op_sing_ind >>
  rw[] >> rw[Once pre]
QED

val _ = cv_trans $ cj 2 clos_letopTheory.let_op_sing_eq

val _ = cv_trans clos_knownTheory.compile_def

(* clos_call *)

(* TODO: free_def is duplicated between clos_known and clos_call; it
   should probably be moved to a common ancestor theory *)
Theorem free_eq_free:
  ∀xs. clos_known$free xs = clos_call$free xs
Proof
  recInduct clos_knownTheory.free_ind >>
  rw[clos_knownTheory.free_def,clos_callTheory.free_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  rpt conj_tac
  >- (ntac 2 AP_TERM_TAC >>
      rw[MAP_MAP_o] >>
      rw[MAP_EQ_f] >>
      rpt(pairarg_tac >> gvs[]) >>
      res_tac >> gvs[])
  >- (rw[MAP_MAP_o] >>
      rw[MAP_EQ_f] >>
      rpt(pairarg_tac >> gvs[]) >>
      res_tac >> gvs[])
  >- (AP_THM_TAC >>
      ntac 2 AP_TERM_TAC >>
      rw[MAP_MAP_o] >>
      rw[MAP_EQ_f] >>
      rpt(pairarg_tac >> gvs[]) >>
      res_tac >> gvs[])
QED

val _ = cv_trans $ GSYM free_eq_free

val pre = cv_auto_trans_pre_rec "" (clos_callTheory.calls_sing_def |> PURE_REWRITE_RULE [LIST_REL_EVERY_ZIP])
  (wf_rel_tac `measure $ λx. case x of INL (e,_) => cv_size e
                                    | INR (es,_) => cv_size es` >>
   cv_termination_tac >>
   irule LESS_EQ_LESS_TRANS >>
   irule_at (Pos last) cv_size_map_snd >>
   rw[oneline cvTheory.cv_snd_def] >>
   rpt(PURE_FULL_CASE_TAC >> gvs[]))

Theorem clos_call_calls_sing_pre[cv_pre]:
  (∀v g. clos_call_calls_sing_pre v g) ∧
  (∀v g. clos_call_calls_sing_list_pre v g)
Proof
  ho_match_mp_tac clos_callTheory.calls_sing_ind >>
  rw[] >> rw[Once pre] >> gvs[]
  >- (first_x_assum match_mp_tac >>
      gvs[LIST_REL_EVERY_ZIP] >>
      gvs[EVERY_MEM] >>
      rw[] >>
      res_tac >>
      rpt(pairarg_tac >> fs[])) >>
  first_x_assum match_mp_tac >>
  gvs[LIST_REL_EVERY_ZIP] >>
  rw[] >> res_tac >>
  fs[EXISTS_MEM] >>
  first_x_assum $ irule_at $ Pos hd >>
  rpt(pairarg_tac >> fs[])
QED

val _ = cv_trans $ cj 2 clos_callTheory.calls_sing_eq

val _ = cv_trans clos_callTheory.compile_def

(* clos_annotate *)

val pre = cv_auto_trans_pre "" (clos_annotateTheory.shift_sing_def |> measure_args [0,0,3]);
Theorem clos_annotate_shift_sing_pre[cv_pre]:
  (∀v m l i. clos_annotate_shift_sing_pre v m l i) ∧
  (∀v m l i. clos_annotate_shift_list_pre v m l i) ∧
  (∀fns_len k new_i v. clos_annotate_shift_letrec_pre fns_len k new_i v)
Proof
  ho_match_mp_tac clos_annotateTheory.shift_sing_ind
  \\ rpt strip_tac \\ simp [Once pre] \\ gvs []
QED

val pre = cv_auto_trans_pre "" (clos_annotateTheory.alt_free_sing_def |> measure_args [0,0,1]);
Theorem clos_annotate_alt_free_sing_pre[cv_pre]:
  (∀v. clos_annotate_alt_free_sing_pre v) ∧
  (∀v. clos_annotate_alt_free_list_pre v) ∧
  (∀m v. clos_annotate_alt_free_letrec_pre m v)
Proof
  ho_match_mp_tac clos_annotateTheory.alt_free_sing_ind
  \\ rpt strip_tac \\ simp [Once pre] \\ gvs []
QED

val _ = cv_trans clos_annotateTheory.annotate_sing_def;
val _ = cv_auto_trans clos_annotateTheory.compile_eq;

(* compile_common from clos_to_bvl *)

val _ = cv_trans clos_to_bvlTheory.chain_exps_def;
val _ = cv_auto_trans clos_to_bvlTheory.compile_common_def;

(* bvl_jump *)

Theorem cv_LENGTH_right_depth:
  cv_LENGTH cv_xs = cv$Num (cv_right_depth cv_xs)
Proof
  gvs [cv_LENGTH_def]
  \\ qsuff_tac ‘∀v n. cv_LEN v (cv$Num n) = cv$Num (cv_right_depth v + n)’
  \\ gvs [] \\ Induct
  \\ simp [cv_right_depth_def,Once cv_LEN_def]
QED

Theorem cv_right_depth_cv_TAKE:
  ∀cv_xs n.
    n ≤ cv_right_depth cv_xs ⇒
    cv_right_depth (cv_TAKE (cv$Num n) cv_xs) = n
Proof
  Induct \\ simp [cv_right_depth_def,Once cv_TAKE_def]
  \\ Cases \\ gvs [cv_right_depth_def]
QED

Theorem cv_right_depth_cv_DROP:
  ∀cv_xs n.
    n ≤ cv_right_depth cv_xs ⇒
    cv_right_depth (cv_DROP (cv$Num n) cv_xs) = cv_right_depth cv_xs - n
Proof
  Induct \\ simp [cv_right_depth_def,Once cv_DROP_def]
  \\ Cases \\ gvs [cv_right_depth_def]
QED

val _ = cv_auto_trans_rec bvl_jumpTheory.JumpList_def
   (WF_REL_TAC ‘measure $ cv_right_depth o SND’
    \\ rpt strip_tac
    \\ Cases_on ‘cv_LENGTH cv_xs’ \\ gvs []
    \\ Cases_on ‘m = 0’ \\ gvs []
    \\ Cases_on ‘m = 1’ \\ gvs [cv_LENGTH_right_depth]
    \\ DEP_REWRITE_TAC [cv_right_depth_cv_TAKE,cv_right_depth_cv_DROP]
    \\ gvs [DIV_LE_X,DIV_LT_X,X_LT_DIV]);

(* clos_to_bvl *)

val _ = cv_auto_trans clos_to_bvlTheory.init_globals_def;
val _ = cv_auto_trans clos_to_bvlTheory.init_code_def;

Theorem cv_size_cv_map_snd_le:
  ∀xs. cv_size (cv_map_snd xs) ≤ cv_size xs
Proof
  Induct
  \\ simp [Once cv_map_snd_def]
  \\ Cases_on ‘xs’ \\ gvs []
QED

val pre = cv_auto_trans_pre_rec "" clos_to_bvlTheory.get_src_names_sing_def
  (WF_REL_TAC ‘measure $ λx. case x of
                | INL (e,_) => cv_size e
                | INR (e,_) => cv_size e’
   \\ cv_termination_tac
   \\ irule LESS_EQ_LESS_TRANS
   \\ irule_at Any cv_size_cv_map_snd_le \\ gvs []);

Theorem clos_to_bvl_get_src_names_sing_pre[cv_pre,local]:
  (∀v l. clos_to_bvl_get_src_names_sing_pre v l) ∧
  (∀v l. clos_to_bvl_get_src_names_list_pre v l)
Proof
  ho_match_mp_tac clos_to_bvlTheory.get_src_names_sing_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans (clos_to_bvlTheory.get_src_names_sing_eq |> CONJUNCT2);

val _ = cv_auto_trans clos_to_bvlTheory.make_name_alist_eq;

val pre = cv_auto_trans_pre "" clos_to_bvlTheory.recc_Lets_def;
Theorem clos_to_bvl_recc_Lets_pre[cv_pre]:
  ∀n nargs k rest.
    clos_to_bvl_recc_Lets_pre n nargs k rest ⇔ k ≤ LENGTH nargs
Proof
  Induct_on ‘k’ \\ gvs [] \\ simp [Once pre] \\ Cases \\ gvs []
QED

val _ = cv_trans clos_to_bvlTheory.recc_Let0_def;

val pre = cv_auto_trans_pre "" clos_to_bvlTheory.build_recc_lets_def;
Theorem clos_to_bvl_build_recc_lets_pre[cv_pre]:
  ∀nargs vs n1 fns_l c3.
    clos_to_bvl_build_recc_lets_pre nargs vs n1 fns_l c3
    ⇔
    nargs ≠ [] ∧ fns_l ≤ LENGTH nargs
Proof
  gvs [pre] \\ Cases using SNOC_CASES \\ gvs [REVERSE_SNOC]
QED

val _ = cv_auto_trans clos_to_bvlTheory.add_parts_def;

val pre = cv_auto_trans_pre_rec "" clos_to_bvlTheory.compile_exp_sing_def
  (WF_REL_TAC ‘measure $ λx. case x of
                             | INL (_,e,_) => cv_size e
                             | INR (_,e,_) => cv_size e’
   \\ cv_termination_tac
   \\ irule LESS_EQ_LESS_TRANS
   \\ irule_at Any cv_size_cv_map_snd_le \\ gvs []);

Theorem clos_to_bvl_compile_exp_sing_pre[cv_pre]:
  (∀max_app v aux. clos_to_bvl_compile_exp_sing_pre max_app v aux) ∧
  (∀max_app v aux. clos_to_bvl_compile_exp_list_pre max_app v aux)
Proof
  ho_match_mp_tac clos_to_bvlTheory.compile_exp_sing_ind
  \\ rpt strip_tac \\ simp [Once pre]
  \\ rpt strip_tac \\ gvs [cv_stdTheory.genlist_eq_GENLIST]
QED

val _ = cv_auto_trans clos_to_bvlTheory.compile_prog_eq;

val _ = cv_trans clos_to_bvlTheory.code_split_def;

val _ = cv_trans_rec clos_to_bvlTheory.code_merge_def
  (WF_REL_TAC ‘measure $ λ(x,y). cv_size x + cv_size y’
   \\ cv_termination_tac) ;

Theorem cv_clos_to_bvl_code_split_imp:
  ∀x y z r1 r2.
    cv_clos_to_bvl_code_split x y z = cv$Pair r1 r2 ∧
    cv_size y ≠ 0  ∧ cv_size z ≠ 0 ⇒
    cv_size r1 < cv_size x + cv_size y + cv_size z ∧
    cv_size r2 < cv_size x + cv_size y + cv_size z
Proof
  Induct
  \\ simp [Once $ fetch "-" "cv_clos_to_bvl_code_split_def"]
  \\ rw [] \\ res_tac \\ gvs []
QED

val pre = cv_trans_pre_rec "" clos_to_bvlTheory.code_sort_def
  (WF_REL_TAC ‘measure cv_size’
   \\ cv_termination_tac
   \\ imp_res_tac cv_clos_to_bvl_code_split_imp \\ gvs []);

Theorem clos_to_bvl_code_sort_pre[cv_pre]:
  ∀v. clos_to_bvl_code_sort_pre v
Proof
  ho_match_mp_tac clos_to_bvlTheory.code_sort_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans clos_to_bvlTheory.compile_def;

(* to_bvl *)

val _ = cv_auto_trans backend_asmTheory.to_bvl_def;

(* bvl_const *)

(* Bring everything from bvl to the front -- everything because this file is
   too big for me to try everything separately. *)
val bvl_names =
  ["Var", "If", "Let", "Raise", "Handle", "Tick", "Force", "Call", "Op", "Bool",
   "mk_tick"];
val _ = app (fn name =>
  temp_bring_to_front_overload name {Name=name, Thy="bvl"}) bvl_names;

Definition mk_add_const_def:
  mk_add_const = λx1 c2.
            if c2 = 0 then x1 else Op (IntOp Add) [x1; Op (IntOp (Const c2)) []]
End

Definition mk_add_def:
  mk_add = λx1 x2.
  (let
     default = Op (IntOp Add) [x1; x2]
   in
     case dest_simple x2 of
       NONE =>
         (case case_op_const x1 of
            NONE => default
          | SOME v5 =>
            case case_op_const x2 of
              NONE => default
            | SOME (op2,x21,n22) =>
              case v5 of
                (op1,x11,n12) =>
                  if op1 = IntOp Add ∧ op2 = IntOp Add then
                    mk_add_const (Op (IntOp Add) [x11; x21]) (n22 + n12)
                  else if op1 = IntOp Add ∧ op2 = IntOp Sub then
                    Op (IntOp Sub)
                      [Op (IntOp Sub) [x11; x21];
                       Op (IntOp (Const (n22 + n12))) []]
                  else if op1 = IntOp Sub ∧ op2 = IntOp Add then
                    mk_add_const (Op (IntOp Sub) [x11; x21]) (n22 + n12)
                  else default)
     | SOME n2 =>
       case case_op_const x1 of
         NONE =>
           (case dest_simple x1 of
              NONE => mk_add_const x1 n2
            | SOME n1 => Op (IntOp (Const (n2 + n1))) [])
       | SOME (IntOp Add,x11,n12) => mk_add_const x11 (n2 + n12)
       | SOME (IntOp Sub,x11,n12) =>
         Op (IntOp Sub) [x11; Op (IntOp (Const (n2 + n12))) []]
       | SOME (op,x11,n12) => default)
End

Definition mk_sub_def:
  mk_sub = λx1 x2.
  (let
     default = Op (IntOp Sub) [x1; x2]
   in
     case dest_simple x2 of
       NONE =>
         (case case_op_const x1 of
            NONE => default
          | SOME v5 =>
            case case_op_const x2 of
              NONE => default
            | SOME (op2,x21,n22) =>
              case v5 of
                (op1,x11,n12) =>
                  if op1 = IntOp Add ∧ op2 = IntOp Add then
                    Op (IntOp Add)
                      [Op (IntOp Sub) [x11; x21];
                       Op (IntOp (Const (n22 − n12))) []]
                  else if op1 = IntOp Add ∧ op2 = IntOp Sub then
                    Op (IntOp Sub)
                      [Op (IntOp Add) [x11; x21];
                       Op (IntOp (Const (n22 − n12))) []]
                  else if op1 = IntOp Sub ∧ op2 = IntOp Add then
                    mk_add_const (Op (IntOp Add) [x11; x21]) (n22 − n12)
                  else default)
     | SOME n2 =>
       case case_op_const x1 of
         NONE =>
           (case dest_simple x1 of
              NONE => default
            | SOME n1 => Op (IntOp (Const (n2 − n1))) [])
       | SOME (IntOp Add,x11,n12) =>
         Op (IntOp Sub) [x11; Op (IntOp (Const (n2 − n12))) []]
       | SOME (IntOp Sub,x11,n12) => mk_add_const x11 (n2 − n12)
       | SOME (op,x11,n12) => default)
End

Definition mk_mul_def:
  mk_mul = λx1 x2.
  (let
     default = Op (IntOp Mult) [x1; x2]
   in
     case dest_simple x2 of
       NONE =>
         (case case_op_const x1 of
            NONE => default
          | SOME v5 =>
            case case_op_const x2 of
              NONE => default
            | SOME (op2,x21,n22) =>
              case v5 of
                (op1,x11,n12) =>
                  if op1 = IntOp Mult ∧ op2 = IntOp Mult then
                    Op (IntOp Mult)
                      [Op (IntOp (Const (n22 * n12))) [];
                       Op (IntOp Mult) [x11; x21]]
                  else default)
     | SOME n2 =>
       case case_op_const x1 of
         NONE =>
           (case dest_simple x1 of
              NONE =>
                if n2 = 1 then x1
                else if n2 = -1 then
                  (let
                     default = Op (IntOp Sub) [x1; Op (IntOp (Const 0)) []]
                   in
                     case case_op_const x1 of
                       NONE =>
                         (case dest_simple x1 of
                            NONE => default
                          | SOME n1 => Op (IntOp (Const (-n1))) [])
                     | SOME (IntOp Add,x11,n12) =>
                       Op (IntOp Sub) [x11; Op (IntOp (Const (-n12))) []]
                     | SOME (IntOp Sub,x11,n12) =>
                       mk_add_const x11 (-n12)
                     | SOME (op,x11,n12) => default)
                else default
            | SOME n1 => Op (IntOp (Const (n2 * n1))) [])
       | SOME (IntOp Mult,x11,n12) =>
         Op (IntOp Mult) [x11; Op (IntOp (Const (n2 * n12))) []]
       | SOME (op,x11,n12) => default)
End

Theorem SmartOp2_eq = bvl_constTheory.SmartOp2_def
  |> SRULE [GSYM mk_add_const_def]
  |> SRULE [Once LET_THM]
  |> SRULE [GSYM mk_add_def]
  |> SRULE [Once LET_THM]
  |> SRULE [GSYM mk_sub_def]
  |> SRULE [Once LET_THM]
  |> SRULE [GSYM mk_mul_def]
  |> SRULE [Once LET_THM];

val _ = cv_auto_trans bvl_constTheory.dest_simple_def;
val _ = cv_trans (mk_add_const_def |> SRULE [FUN_EQ_THM]);
val _ = cv_auto_trans (mk_add_def |> SRULE [FUN_EQ_THM]);
val _ = cv_trans (mk_sub_def |> SRULE [FUN_EQ_THM]);
val _ = cv_trans (mk_mul_def |> SRULE [FUN_EQ_THM]);
val _ = cv_auto_trans SmartOp2_eq;

val pre = cv_auto_trans_pre "" bvl_constTheory.compile_sing_def;
Theorem bvl_const_compile_sing_pre[cv_pre]:
  (∀v env. bvl_const_compile_sing_pre env v) ∧
  (∀v env. bvl_const_compile_list_pre env v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_constTheory.compile_exp_eq;

(* bvl_handle *)

val _ = cv_trans bvl_handleTheory.SmartLet_def;
val _ = cv_auto_trans bvl_handleTheory.LetLet_def;
val _ = cv_auto_trans bvl_handleTheory.OptionalLetLet_sing_def;

val pre = cv_auto_trans_pre "" (bvl_handleTheory.compile_sing_def |> measure_args [2,2]);
Theorem bvl_handle_compile_sing_pre[cv_pre,local]:
  (∀v l n. bvl_handle_compile_sing_pre l n v) ∧
  (∀v l n. bvl_handle_compile_list_pre l n v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans bvl_handleTheory.can_raise_def;
val _ = cv_trans bvl_handleTheory.dest_handle_If_def;
val _ = cv_trans bvl_handleTheory.dest_handle_Let_def;

val pre = cv_auto_trans_pre "" (bvl_handleTheory.handle_adj_vars_def |> measure_args [2,2]);
Theorem bvl_handle_handle_adj_vars_pre[cv_pre]:
  (∀v l d. bvl_handle_handle_adj_vars_pre l d v) ∧
  (∀v l d. bvl_handle_handle_adj_vars1_pre l d v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre_rec "" bvl_handleTheory.handle_simp_def
  (WF_REL_TAC ‘measure $ λx. case x of
                             | INL e => cv_size e
                             | INR (INL e) => cv_size e
                             | INR (INR (e1,e2,_)) => cv_size e1 + cv_size e2 + 1’
   \\ cv_termination_tac
   \\ TRY (Cases_on ‘z’ \\ gvs [] \\ NO_TAC)
   \\ gvs [fetch "-" "cv_bvl_handle_dest_handle_If_def",AllCaseEqs()]
   \\ gvs [fetch "-" "cv_bvl_handle_dest_handle_Let_def",AllCaseEqs()]
   \\ cv_termination_tac);

Theorem bvl_handle_handle_simp_pre[cv_pre]:
  (∀v. bvl_handle_handle_simp_pre v) ∧
  (∀v. bvl_handle_handle_simp_list_pre v) ∧
  (∀x1 x2 l. bvl_handle_make_handle_pre x1 x2 l)
Proof
  ho_match_mp_tac bvl_handleTheory.handle_simp_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_handleTheory.compile_exp_eq;
val _ = bvl_handleTheory.dest_Seq_def |> CONJUNCT2 |> oneline |> cv_trans;

val pre = cv_auto_trans_pre_rec "" bvl_handleTheory.compile_seqs_def
  (WF_REL_TAC ‘measure $ λ(_,e,_). cv_size e’
   \\ cv_termination_tac
   \\ gvs [fetch "-" "cv_bvl_handle_dest_Seq_def",AllCaseEqs()]
   \\ cv_termination_tac);

Theorem bvl_handle_compile_seqs_pre[cv_pre]:
  ∀cut_size e acc. bvl_handle_compile_seqs_pre cut_size e acc
Proof
  ho_match_mp_tac bvl_handleTheory.compile_seqs_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_handleTheory.compile_any_def;

(* bvl_inline *)

val _ = cv_auto_trans (bvl_inlineTheory.tick_inline_sing_def |> measure_args [1,1]);

val pre = cv_auto_trans_pre "" (bvl_inlineTheory.is_small_sing_def |> measure_args [1,1]);
Theorem bvl_inline_is_small_sing_pre[cv_pre,local]:
  (∀v n. bvl_inline_is_small_sing_pre n v) ∧
  (∀v n. bvl_inline_is_small_list_pre n v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans bvl_inlineTheory.is_small_eq;

val pre = cv_auto_trans_pre "" (bvl_inlineTheory.is_rec_sing_def |> measure_args [1,1]);
Theorem bvl_inline_is_rec_sing_pre[cv_pre,local]:
  (∀v n. bvl_inline_is_rec_sing_pre n v) ∧
  (∀v n. bvl_inline_is_rec_list_pre n v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans bvl_inlineTheory.must_inline_eq;

val pre = cv_auto_trans_pre "" bvl_inlineTheory.tick_inline_all_eq;
Theorem bvl_inline_tick_inline_all_pre[cv_pre,local]:
  ∀v limit cs aux. bvl_inline_tick_inline_all_pre limit cs v aux
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val pre = cv_trans bvl_inlineTheory.tick_compile_prog_def;

val pre = cv_auto_trans_pre "" bvl_inlineTheory.let_op_one_def;
Theorem bvl_inline_let_op_one_pre[cv_pre,local]:
  (∀v. bvl_inline_let_op_one_pre v) ∧
  (∀v. bvl_inline_let_op_list_pre v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_inlineTheory.let_op_sing_eq;

val pre = cv_auto_trans_pre "" bvl_inlineTheory.remove_ticks_sing_def;
Theorem bvl_inline_remove_ticks_sing_pre[cv_pre,local]:
  (∀v. bvl_inline_remove_ticks_sing_pre v) ∧
  (∀v. bvl_inline_remove_ticks_list_pre v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_inlineTheory.optimise_eq;
val _ = cv_auto_trans bvl_inlineTheory.compile_inc_def;
val _ = cv_trans bvl_inlineTheory.compile_prog_def;

(* bvi_tailrec *)

val _ = cv_trans (bvi_tailrecTheory.is_rec_def |> measure_args [1]);
val _ = cv_auto_trans bvi_tailrecTheory.let_wrap_def;

Theorem term_ok_int_eq[local]:
  term_ok_int ts expr ⇔
  case expr of
  | Var i => if i < LENGTH ts then EL i ts = Int else F
  | Op op xs =>
     (if xs = [] ∧ is_const op then T else
        case xs of
        | [x;y] => is_arith op ∧ term_ok_int ts x ∧ term_ok_int ts y
        | _ => F)
  | _ => F
Proof
  simp [Once bvi_tailrecTheory.term_ok_int_def]
  \\ Cases_on ‘expr’ \\ gvs []
  \\ gvs [bvi_tailrecTheory.get_bin_args_def]
  \\ Cases_on ‘l’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
  \\ Cases_on ‘t'’ \\ gvs []
QED

val pre = cv_auto_trans_pre "" term_ok_int_eq;
Theorem bvi_tailrec_term_ok_int_pre[cv_pre,local]:
  ∀ts expr. bvi_tailrec_term_ok_int_pre ts expr
Proof
  ho_match_mp_tac bvi_tailrecTheory.term_ok_int_ind
  \\ rw [] \\ simp [Once pre] \\ rw []
  \\ gvs [bvi_tailrecTheory.get_bin_args_def]
QED

val _ = cv_trans bvi_tailrecTheory.get_bin_args_def;

Theorem cv_bvi_tailrec_get_bin_args_lemma[local]:
  cv_bvi_tailrec_get_bin_args (cv$Pair t v) = cv$Pair x (cv$Pair y z) ⇒
  cv_size y ≤ cv_size v ∧
  cv_size z ≤ cv_size v
Proof
  gvs [fetch "-" "cv_bvi_tailrec_get_bin_args_def",AllCaseEqs()]
  \\ cv_termination_tac
QED

val pre = cv_auto_trans_pre_rec "" bvi_tailrecTheory.term_ok_any_def
  (WF_REL_TAC ‘measure $ λ(_,_,e). cv_size e’
   \\ cv_termination_tac
   \\ Cases_on ‘z’ \\ gvs []
   \\ imp_res_tac cv_bvi_tailrec_get_bin_args_lemma
   \\ gvs []);

Theorem bvi_tailrec_term_ok_any_pre[cv_pre]:
  ∀ts list v. bvi_tailrec_term_ok_any_pre ts list v
Proof
  ho_match_mp_tac bvi_tailrecTheory.term_ok_any_ind
  \\ rpt strip_tac \\ simp [Once pre]
  \\ rpt strip_tac \\ gvs []
QED

val pre = cv_auto_trans_pre "" bvi_tailrecTheory.scan_expr_sing_def;
Theorem bvi_tailrec_scan_expr_sing_pre[cv_pre]:
  (∀v ts loc. bvi_tailrec_scan_expr_sing_pre ts loc v) ∧
  (∀v ts loc. bvi_tailrec_scan_expr_list_pre ts loc v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre "" bvi_tailrecTheory.rewrite_eq;
Theorem bvi_tailrec_rewrite_pre[cv_pre]:
  ∀loc next opr acc ts v. bvi_tailrec_rewrite_pre loc next opr acc ts v
Proof
  ho_match_mp_tac bvi_tailrecTheory.rewrite_ind
  \\ rpt strip_tac \\ simp [Once pre]
  \\ rpt strip_tac \\ gvs [bvi_tailrecTheory.scan_expr_eq]
QED

val pre = cv_auto_trans_pre "" bvi_tailrecTheory.has_rec_sing_def;
Theorem bvi_tailrec_has_rec_sing_pre[cv_pre]:
  (∀v loc. bvi_tailrec_has_rec_sing_pre loc v) ∧
  (∀v loc. bvi_tailrec_has_rec_list_pre loc v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans bvi_tailrecTheory.check_exp_eq;
val _ = cv_auto_trans bvi_tailrecTheory.compile_exp_def;

val pre = cv_auto_trans_pre "" bvi_tailrecTheory.compile_prog_def;
Theorem bvi_tailrec_compile_prog_pre[cv_pre]:
  ∀next v. bvi_tailrec_compile_prog_pre next v
Proof
  ho_match_mp_tac bvi_tailrecTheory.compile_prog_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

(* bvi_let *)

Theorem cv_size_LAST:
  ∀g. cv_size (cv_LAST g) ≤ cv_size g
Proof
  Induct \\ simp [Once cv_LAST_def] \\ rw []
QED

Theorem cv_size_FRONT:
  ∀g. cv_size (cv_FRONT g) ≤ cv_size g
Proof
  Induct \\ simp [Once cv_FRONT_def] \\ rw []
QED

val pre = cv_auto_trans_pre_rec "" bvi_letTheory.compile_sing_def
  (WF_REL_TAC ‘measure $ λx. case x of
                             | INL (_,_,e) => cv_size e
                             | INR (_,_,e) => cv_size e’
   \\ cv_termination_tac
   \\ gvs [cv_LENGTH_right_depth]
   \\ Cases_on ‘z’ \\ gvs [cv_right_depth_def]
   \\ irule LESS_EQ_LESS_TRANS
   \\ (irule_at Any cv_size_FRONT ORELSE
       irule_at Any cv_size_LAST)
   \\ gvs []);

Theorem bvi_let_compile_sing_pre[cv_pre]:
  (∀env d v. bvi_let_compile_sing_pre env d v) ∧
  (∀env d v. bvi_let_compile_list_pre env d v)
Proof
  ho_match_mp_tac bvi_letTheory.compile_sing_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvi_letTheory.compile_exp_eq;

(* bvl_to_bvi *)

val _ = cv_auto_trans bvl_to_bviTheory.get_names_def;
val _ = cv_auto_trans bvl_to_bviTheory.stubs_def;
val _ = cv_trans bvl_to_bviTheory.destLet_def;

val cv_bvl_to_bvi_destLet_def = fetch "-" "cv_bvl_to_bvi_destLet_def";

Theorem destLet_lemma[local]:
  cv_bvl_to_bvi_destLet (cv_fst z) = cv$Pair x1 x2 ⇒
  cv_size x1 ≤ cv_size z ∧
  cv_size x2 ≤ cv_size z
Proof
  Cases_on ‘z’ \\ gvs [cv_bvl_to_bvi_destLet_def]
  \\ rename [‘_ ≤ cv_size g1 + (cv_size g2 + 1)’]
  \\ Cases_on ‘g1’ \\ gvs []
  \\ Cases_on ‘g’ \\ gvs [AllCaseEqs()] \\ rw []
  \\ Cases_on ‘g'’ \\ gvs []
QED

Theorem destLet_lemma2[local]:
  cv_bvl_to_bvi_destLet (cv_snd z) = cv$Pair x1 x2 ⇒
  cv_size x1 ≤ cv_size z ∧
  cv_size x2 ≤ cv_size z
Proof
  Cases_on ‘z’ \\ gvs [cv_bvl_to_bvi_destLet_def]
  \\ rename [‘_ ≤ cv_size g1 + (cv_size g2 + 1)’]
  \\ Cases_on ‘g2’ \\ gvs []
  \\ Cases_on ‘g’ \\ gvs [AllCaseEqs()] \\ rw []
  \\ Cases_on ‘g'’ \\ gvs []
QED

val pre = cv_auto_trans_pre_rec "" bvl_to_bviTheory.compile_exps_sing_def
  (WF_REL_TAC ‘measure $ λx. case x of
                             | INL (_,e) => cv_size e
                             | INR (_,e) => cv_size e’
   \\ cv_termination_tac
   \\ imp_res_tac destLet_lemma
   \\ imp_res_tac destLet_lemma2
   \\ gvs []);

Theorem bvl_to_bvi_compile_exps_sing_pre[cv_pre]:
  (∀n v. bvl_to_bvi_compile_exps_sing_pre n v) ∧
  (∀n v. bvl_to_bvi_compile_exps_list_pre n v)
Proof
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_sing_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans bvl_to_bviTheory.compile_single_eq;

val pre = cv_trans_pre "" bvl_to_bviTheory.global_count_sing_def;
Theorem bvl_to_bvi_global_count_sing_pre[cv_pre]:
  (∀v. bvl_to_bvi_global_count_sing_pre v) ∧
  (∀v. bvl_to_bvi_global_count_list_pre v)
Proof
  Induct \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans bvl_to_bviTheory.compile_prog_eq;
val _ = cv_auto_trans bvl_to_bviTheory.compile_def;

(* to_bvi *)

val _ = cv_auto_trans backend_asmTheory.to_bvi_def;

(* to_data *)

Definition num_size_acc_def:
  num_size_acc n acc =
    if n < 2 ** 32 then acc + 2:num else num_size_acc (n DIV 2 ** 32) (acc + 1)
End

Theorem num_size_eq_acc:
  num_size n = num_size_acc n 0
Proof
  qsuff_tac ‘∀n acc. num_size_acc n acc = num_size n + acc’ \\ gvs []
  \\ ho_match_mp_tac data_spaceTheory.num_size_ind \\ rw []
  \\ once_rewrite_tac [data_spaceTheory.num_size_def, num_size_acc_def]
  \\ rw [] \\ gvs []
QED

val _ = cv_trans num_size_acc_def;
val _ = cv_trans num_size_eq_acc;

val pre = cv_auto_trans_pre "" data_liveTheory.compile_def;
Theorem data_live_compile_pre[cv_pre,local]:
  ∀v live. data_live_compile_pre v live
Proof
  ho_match_mp_tac data_liveTheory.compile_ind \\ rw [] \\ simp [Once pre]
QED

val _ = cv_auto_trans bvi_to_dataTheory.optimise_def;
val _ = cv_auto_trans bvi_to_dataTheory.op_requires_names_eqn;

val pre = cv_auto_trans_pre "" (bvi_to_dataTheory.compile_sing_def |> measure_args [4,3]);
Theorem bvi_to_data_compile_sing_pre[cv_pre,local]:
  (∀n env tail live v. bvi_to_data_compile_sing_pre n env tail live v) ∧
  (∀n env live v. bvi_to_data_compile_list_pre n env live v)
Proof
  ho_match_mp_tac bvi_to_dataTheory.compile_sing_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_auto_trans rich_listTheory.COUNT_LIST_GENLIST;
val _ = cv_trans bvi_to_dataTheory.compile_exp_eq;
val _ = cv_auto_trans bvi_to_dataTheory.compile_prog_def;
val _ = cv_trans to_data_def;

val _ = cv_trans backend_asmTheory.to_flat_all_def;
val _ = cv_trans backend_asmTheory.to_clos_all_def;
val _ = cv_trans backend_asmTheory.to_bvl_all_def;
val _ = cv_auto_trans (backend_asmTheory.to_bvi_all_def
                         |> REWRITE_RULE [bvl_inlineTheory.remove_ticks_sing,HD]);

Theorem bvi_to_data_compile_sing[local]:
  FST (bvi_to_data$compile n env t l [x]) = FST (compile_sing n env t l x)
Proof
  ‘∃y. compile_sing n env t l x = y’ by gvs []
  \\ PairCases_on ‘y’ \\ gvs []
  \\ imp_res_tac bvi_to_dataTheory.compile_sing_eq \\ gvs []
QED

val _ = cv_auto_trans (to_data_all_def |> REWRITE_RULE [bvi_to_data_compile_sing]);

(* Explorer *)

val _ = cv_trans_pre "" jsonLangTheory.num_to_hex_digit_def;

Theorem jsonLang_num_to_hex_digit_pre[cv_pre]:
  ∀n. jsonLang_num_to_hex_digit_pre n
Proof
  rw[fetch "-" "jsonLang_num_to_hex_digit_pre_cases"]
QED

val pre = cv_trans_pre_rec "" presLangTheory.num_to_hex_def
  (WF_REL_TAC ‘measure cv_size’
   \\ cv_termination_tac
   \\ Cases_on`cv_n`
   \\ gvs[cvTheory.cv_div_def,cvTheory.c2b_def]
   \\ intLib.ARITH_TAC);

Theorem presLang_num_to_hex_pre[cv_pre]:
  ∀n. presLang_num_to_hex_pre n
Proof
  completeInduct_on`n`>>
  rw[Once pre]
QED

val _ = cv_auto_trans presLangTheory.ast_t_to_display_def;

val _ = cv_auto_trans presLangTheory.pat_to_display_def;

val pre = cv_auto_trans_pre "" presLangTheory.exp_to_display_def;

Theorem presLang_exp_to_display_pre[cv_pre]:
  (∀c. presLang_exp_to_display_pre c) ∧
  (∀v. presLang_exp_to_display_list_pre v) ∧
  (∀v. presLang_pat_exp_to_display_list_pre v) ∧
  (∀v. presLang_fun_to_display_list_pre v)
Proof
  ho_match_mp_tac presLangTheory.exp_to_display_ind>>
  rw[] \\ simp[Once pre]
QED

val _ = cv_auto_trans presLangTheory.source_to_display_dec_def;

val _ = cv_auto_trans presLangTheory.flat_pat_to_display_def;

val pre = cv_auto_trans_pre "" presLangTheory.flat_to_display_def;

Theorem presLang_flat_to_display_pre[cv_pre]:
  (∀v. presLang_flat_to_display_pre v) ∧
  (∀v. presLang_flat_to_display_list_pre v) ∧
  (∀v. presLang_pat_flat_to_display_list_pre v) ∧
  (∀v. presLang_fun_flat_to_display_list_pre v)
Proof
  ho_match_mp_tac presLangTheory.flat_to_display_ind >>
  rw[] \\ simp[Once pre]
QED

val _ = cv_auto_trans displayLangTheory.display_to_str_tree_def;

val pre = cv_trans_pre_rec "" presLangTheory.num_to_varn_aux_def
  (WF_REL_TAC ‘measure cv_size’
   \\ cv_termination_tac
   \\ Cases_on`cv_n`
   \\ gvs[cvTheory.cv_div_def,cvTheory.c2b_def]
   \\ intLib.ARITH_TAC);

Theorem presLang_num_to_varn_aux_pre[cv_pre]:
  ∀n. presLang_num_to_varn_aux_pre n
Proof
  completeInduct_on`n`>>
  rw[Once pre]
  >- (
    first_x_assum match_mp_tac>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

val _ = cv_auto_trans presLangTheory.num_to_varn_def;

val pre = cv_trans_pre_rec "" presLangTheory.num_to_varn_list_def
  (WF_REL_TAC ‘measure (cv_size o SND)’
   \\ cv_termination_tac
   \\ Cases_on`cv_n`
   \\ gvs[cvTheory.cv_div_def,cvTheory.c2b_def]);

Theorem presLang_num_to_varn_list_pre[cv_pre]:
  ∀ls n. presLang_num_to_varn_list_pre ls n
Proof
  completeInduct_on`n`>>
  rw[Once pre]
QED

val _ = cv_auto_trans presLangTheory.const_to_display_def;

val pre = cv_auto_trans_pre "" (presLangTheory.clos_to_display_def |> measure_args [2,2,3,4]);

Theorem presLang_clos_to_display_pre[cv_pre]:
  (∀ns h v. presLang_clos_to_display_pre ns h v) ∧
  (∀ns h v. presLang_clos_to_display_list_pre ns h v) ∧
  (∀ns h i v. presLang_clos_to_display_lets_pre ns h i v) ∧
  (∀ns h i len v. presLang_clos_to_display_letrecs_pre ns h i len v)
Proof
  ho_match_mp_tac presLangTheory.clos_to_display_ind \\
  rw[] \\ simp[Once pre]
QED

val pre = cv_auto_trans_pre "" (presLangTheory.bvl_to_display_def |> measure_args [2,2,3]);

Theorem presLang_bvl_to_display_pre[cv_pre]:
  (∀ns h v. presLang_bvl_to_display_pre ns h v) ∧
  (∀ns h v. presLang_bvl_to_display_list_pre ns h v) ∧
  (∀ns h i v. presLang_bvl_to_display_lets_pre ns h i v)
Proof
  ho_match_mp_tac presLangTheory.bvl_to_display_ind \\
  rw[] \\ simp[Once pre]
QED

val pre = cv_auto_trans_pre "" (presLangTheory.bvi_to_display_def |> measure_args [2,2,3]);

Theorem presLang_bvi_to_display_pre[cv_pre]:
  (∀ns h v. presLang_bvi_to_display_pre ns h v) ∧
  (∀ns h v. presLang_bvi_to_display_list_pre ns h v) ∧
  (∀ns h i v. presLang_bvi_to_display_lets_pre ns h i v)
Proof
  ho_match_mp_tac presLangTheory.bvi_to_display_ind \\
  rw[] \\ simp[Once pre]
QED

val _ = cv_auto_trans (presLangTheory.data_prog_to_display_def |> measure_args [0,0]);

val _ = cv_auto_trans presLangTheory.word_exp_to_display_def;

val _ = cv_auto_trans presLangTheory.word_prog_to_display_def;

val _ = cv_auto_trans presLangTheory.stack_prog_to_display_def;
