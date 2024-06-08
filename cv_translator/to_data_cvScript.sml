(*
  Translation of the to_data compiler function.
*)
open preamble cv_transLib cv_stdTheory;
open backendTheory backend_asmTheory;

val _ = new_theory "to_data_cv";

val _ = cv_memLib.use_long_names := true;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.SmartAppend_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;
val _ = cv_trans mlstringTheory.implode_def;
val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans mlstringTheory.strcat_thm;
val _ = cv_trans mlstringTheory.str_def;
val _ = cv_trans miscTheory.list_max_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

val toChar_pre = cv_trans_pre mlintTheory.toChar_def
val num_to_chars_pre = cv_auto_trans_pre mlintTheory.num_to_chars_def;

Theorem IMP_toChar_pre:
  n < 16 ⇒ mlint_toChar_pre n
Proof
  gvs [toChar_pre]
QED

Theorem num_to_chars_pre[cv_pre,local]:
  ∀a0 a1 a2 a3. mlint_num_to_chars_pre a0 a1 a2 a3
Proof
  ho_match_mp_tac mlintTheory.num_to_chars_ind \\ rw []
  \\ rw [] \\ simp [Once num_to_chars_pre]
  \\ once_rewrite_tac [toChar_pre] \\ gvs [] \\ rw []
  \\ ‘k MOD 10 < 10’ by gvs [] \\ simp []
QED

Triviality Num_ABS:
  Num (ABS i) = Num i
Proof
  Cases_on ‘i’ \\ gvs []
QED

val _ = cv_trans (mlintTheory.toString_def |> SRULE [Num_ABS]);
val _ = cv_trans mlintTheory.num_to_str_def;

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

val pre = cv_auto_trans_pre naive_pattern_match_clocked_def

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
   >- (gvs[flatLangTheory.pat_size_def,SUM_APPEND, flat_patternTheory.pat1_size,
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
Termination
  wf_rel_tac ‘measure $ λx. sum_CASE x pat_size (list_size pat_size)’
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
  (wf_rel_tac ‘measure $ λ(x,y). cv_size(cv_LENGTH y) - cv_size x’ >>
   cv_termination_tac >>
   gvs[cvTheory.c2b_def,oneline cvTheory.cv_lt_def0,AllCaseEqs(),
       oneline cvTheory.b2c_def])

val pre = cv_trans_pre flat_patternTheory.dec_name_to_num_def

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
    let nm = enc_num_to_name k [] in
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
    let nm = enc_num_to_name k [] in
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
    let j = list_max (MAP (\(_,_,(j,_,_)). j) ys) in
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
Termination
  WF_REL_TAC `measure (\x. case x of INL (_, x) => exp_size x
    | INR (INL (_, xs)) => exp6_size xs
    | INR (INR (INL (_, ps))) => exp1_size ps
    | INR (INR (INR (_, ps))) => exp3_size ps)`
  \\ rw [flatLangTheory.exp_size_def]
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

val pre = cv_auto_trans_pre_rec compile_exp_alt_def
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

val _ = cv_auto_trans_pre flat_elimTheory.has_Eval_def;

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

val pre = cv_auto_trans_pre_rec (flat_elimTheory.find_loc_def |> PURE_REWRITE_RULE[o_DEF,GSYM MAP_MAP_o])
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

val pre = cv_auto_trans_pre_rec (flat_elimTheory.find_lookups_def |> PURE_REWRITE_RULE[GSYM MAP_MAP_o,o_THM])
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
  rw[flatLangTheory.exp3_size] >>
  ‘list_size exp_size (MAP SND pes) ≤ LENGTH pes + (SUM (MAP exp5_size pes))’
    suffices_by gvs[] >>
  Induct_on ‘pes’ >>
  rw[list_size_def,ADD1] >>
  rename1 ‘SND xx’ >> Cases_on ‘xx’ >> rw[flatLangTheory.exp_size_def]
End

val pre = cv_auto_trans_pre_rec is_pure_alt_def
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
Termination
  WF_REL_TAC `measure (λ e . sum_CASE e exp_size (list_size exp_size))`
End

val pre = cv_trans_pre is_hidden_alt_def

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

val pre = cv_auto_trans_pre (spt_closureTheory.closure_spt_def |> PURE_REWRITE_RULE[GSYM spt_fold_union_thm])

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
     (Fn (mlstring$implode t) NONE NONE 1 (flat_to_clos_compile_alt (SOME v::m) (e)))) /\
  (flat_to_clos_compile_alt m (If t x1 x2 x3) =
     (If t (flat_to_clos_compile_alt m (x1))
           (flat_to_clos_compile_alt m (x2))
           (flat_to_clos_compile_alt m (x3)))) /\
  (flat_to_clos_compile_alt m (Let t vo e1 e2) =
     (Let t [flat_to_clos_compile_alt m (e1)] (flat_to_clos_compile_alt (vo::m) (e2)))) /\
  (flat_to_clos_compile_alt m (Mat t e pes) = (Op t (Const 0) [])) /\
  (flat_to_clos_compile_alt m (Handle t e pes) =
     case dest_pat pes of
     | SOME (v,h) => (Handle t (flat_to_clos_compile_alt m (e)) (flat_to_clos_compile_alt (SOME v::m) (h)))
     | _ => flat_to_clos_compile_alt m (e)) /\
  (flat_to_clos_compile_alt m (Letrec t funs e) =
     let new_m = MAP (\n. SOME (FST n)) funs ++ m in
       (Letrec (MAP (\n. join_strings (mlstring$implode t) (mlstring$implode (FST n))) funs) NONE NONE
          (flat_to_clos_compile_lets_alt new_m funs)
          (flat_to_clos_compile_alt new_m (e)))) ∧
  (flat_to_clos_compile_lets_alt m [] = []) /\
  (flat_to_clos_compile_lets_alt m ((f,v,x)::xs) = (1, flat_to_clos_compile_alt (SOME v :: m) x) :: flat_to_clos_compile_lets_alt m xs)
Termination
  wf_rel_tac ‘measure $ λx.
             case x of
               INL (m, e) => list_size exp_size e
             | INR (INL (m,e)) => exp_size e
             | INR (INR (m,e)) => list_size (exp_size o SND o SND) e’ >>
  rw[flatLangTheory.exp1_size,flatLangTheory.exp6_size,
     list_size_thm
    ] >>
  gvs[oneline flat_to_closTheory.dest_pat_def,AllCaseEqs(),
      oneline flat_to_closTheory.dest_nop_def,
      flatLangTheory.op_size_def,
      MAP_REVERSE,SUM_REVERSE,SUM_APPEND,
      flatLangTheory.exp_size_def
     ] >>
  qmatch_goalsub_abbrev_tac ‘SUM (MAP a1 funs)’ >>
  ‘SUM(MAP a1 funs) ≤ SUM (MAP exp2_size funs)’
    suffices_by gvs[] >>
  unabbrev_all_tac >>
  irule SUM_MAP_same_LE >>
  simp[EVERY_MEM,FORALL_PROD] >>
  rw[flatLangTheory.exp_size_def]
End

val _ = cv_auto_trans flat_to_closTheory.dest_nop_def
val _ = cv_auto_trans flat_to_closTheory.dest_pat_def

val pre = cv_auto_trans_pre_rec flat_to_clos_compile_alt_def
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

val pre = cv_auto_trans_pre_rec closLangTheory.has_install_def
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

val _ = cv_trans clos_mtiTheory.collect_args_def

val _ = cv_trans clos_mtiTheory.collect_apps_def

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
                              INL(n,_,_) => n
                            |  INR(INL(n,_,_)) => n
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
                            | INR es => exp3_size es` >>
  rpt strip_tac >>
  sg ‘∀x. closLang$exp3_size(MAP SND x) ≤ exp1_size x’
  >- (Induct
      >- rw[closLangTheory.exp_size_def] >>
      Cases >> rw[closLangTheory.exp_size_def]) >>
  irule LESS_EQ_LESS_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  rw[]
End

val pre = cv_auto_trans_pre_rec exp_size_alt_def
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

val pre = cv_auto_trans_pre intro_multi_alt_def

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

Theorem to_data_fake:
  backend_asm$to_data c p = (c,[(InitGlobals_location,0,Skip)],LN)
Proof
  cheat
QED

val _ = cv_auto_trans to_data_fake;

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
