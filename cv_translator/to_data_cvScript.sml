(*
  Translation of the to_data compiler function.
*)
open preamble cv_transLib cv_stdTheory;
open backendTheory backend_asmTheory;

val _ = new_theory "to_data_cv";

val _ = cv_memLib.use_long_names := true;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;
val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans miscTheory.list_max_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

(* source_let *)

val _ = cv_trans source_letTheory.dest_Letrec_def;
val _ = cv_trans source_letTheory.dest_Let_def;
val _ = cv_trans source_letTheory.lift_let_def;
val _ = cv_trans source_letTheory.lift_lets_def;
val _ = cv_trans source_letTheory.compile_decs_def;

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

val pre = cv_auto_trans_pre
          (source_to_flatTheory.compile_exp_def
             |> PURE_REWRITE_RULE [oneline OPTION_MAP_DEF,o_THM]);

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
Termination
  wf_rel_tac ‘measure $ λx.
                case x of
                  INL (f,y) => namespace_size (K 0) (K 0) (K 0) y
                | INR (f,xs) => list_size (namespace_size (K 0) (K 0) (K 0) o SND) xs’ >>
  rw[namespaceTheory.namespace_size_eq] >>
  qmatch_goalsub_abbrev_tac ‘a1 < a2 + _’ >>
  ‘a1 ≤ a2’ suffices_by rw[] >>
  unabbrev_all_tac >>
  irule list_size_mono >>
  Cases >>
  rw[basicSizeTheory.pair_size_def]
End

Theorem nsMap_alt_thm:
  (∀data b. nsMap_alt (data:'d) (b:('a,'b,'c) namespace) = nsMap (λtag. (tag, data)) b) ∧
  (∀data xs. nsMap_alts (data:'d) (xs:('a # ('a,'b,'c) namespace) list) = (MAP (λ(mn,e). (mn,nsMap (λtag. (tag, data)) e)) $ xs))
Proof
  ho_match_mp_tac nsMap_alt_ind >>
  rw[nsMap_alt_def,namespaceTheory.nsMap_def]
QED

val _ = cv_auto_trans nsMap_alt_def;

val _ = cv_auto_trans (source_to_flatTheory.alloc_tags_def |> PURE_ONCE_REWRITE_RULE[GSYM nsMap_alt_thm])

Definition compile_decs_alt_def:
  (compile_dec_alt (t:string list) n next env envs (ast$Dlet locs p e) =
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
      envs,
      MAPi (λi (ns,cids). flatLang$Dtype (next.tidx + i) cids) new_env)) ∧
  (compile_dec_alt _ n next env envs (Dtabbrev locs tvs tn t) =
     (n, next, empty_env, envs, [])) ∧
  (compile_dec_alt t n next env envs (Dexn locs cn ts) =
     (n, (next with eidx := next.eidx + 1),
      <| v := nsEmpty; c := nsSing cn (next.eidx, NONE) |>,
      envs,
      [Dexn next.eidx (LENGTH ts)])) ∧
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

val _ = cv_auto_trans compile_decs_alt_def

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
        let nm = enc_num_to_name k [] in
        ((j, nm), (p, k, Var_local t nm))) (enumerate 0 ps) in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2 + LENGTH ps)
        (MAP SND j_nms ++ m) exp in
    let j_nms_used = FILTER (\(_, (_, k, _)). IS_SOME (lookup k spt)) j_nms in
    let exp3 = FOLDR (\((j, nm), _) exp.
        flatLang$Let t (SOME nm) (App t (El j) [x]) exp) exp2 j_nms_used in
    let spt2 = if NULL j_nms_used then spt else insert k () spt in
    (spt2, exp3)) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pas p v, k, x) :: m) exp = (
    let nm = enc_num_to_name (i + 1) [] in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2)
                      ((p, i + 1, Var_local t nm) :: m) exp in
    (insert k () spt, Let t (SOME v) x
                            (Let t (SOME nm) (Var_local t v) exp2))) /\
  compile_pat_bindings_clocked (SUC ck) t i ((Pref p, k, x) :: m) exp = (
    let nm = enc_num_to_name (i + 1) [] in
    let (spt, exp2) = compile_pat_bindings_clocked ck t (i + 2)
        ((p, i + 1, Var_local t nm) :: m) exp in
    (insert k () spt, Let t (SOME nm) (App t (El 0) [x]) exp2))
End

val pre = cv_auto_trans_pre (compile_pat_bindings_clocked_def |> PURE_REWRITE_RULE[ELIM_UNCURRY])

Theorem compile_pat_bindings_clocked_pre[cv_pre,local]:
  ∀v0 v1 v2 v exp. compile_pat_bindings_clocked_pre v0 v1 v2 v exp
Proof
  ho_match_mp_tac compile_pat_bindings_clocked_ind >>
  rw[] >>
  rw[Once $ fetch "-" "compile_pat_bindings_clocked_pre_cases"] >>
  gvs[ELIM_UNCURRY]
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
      >- (gvs[flatLangTheory.pat_size_def,SUM_APPEND, flat_patternTheory.pat1_size,
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

val _ = cv_auto_trans_pre flatLangTheory.pat_size_def

Theorem flatLang_pat_size_pre[cv_pre]:
  (∀v. flatLang_pat_size_pre v) ∧
  (∀v. flatLang_pat1_size_pre v)
Proof
  Induct >> rw[Once $ fetch "-" "flatLang_pat_size_pre_cases"]
QED

val _ = cv_auto_trans compile_pat_bindings_clocked_eq

val _ = cv_auto_trans flat_patternTheory.compile_pats_def

Theorem to_data_fake:
  backend_asm$to_data c p = (c,[],LN)
Proof
  cheat
QED

val _ = cv_trans to_data_fake;

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
