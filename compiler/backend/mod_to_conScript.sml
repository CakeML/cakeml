open preamble modLangTheory conLangTheory
open backend_commonTheory

(* The translator to conLang keeps a mapping (tag_env) of each constructor to
 * its arity, tag, and type. Tags need only be unique for each arity-type pair,
 * and are reused as much as possible otherwise.
 *
 * The expressions include the unary operation for initialising the global
 * store, even though it can't be used until decLang. However, including it here
 * means that the conLang->decLang translation can just be (\x.x). Also
 * includes the expression for extending the global store.
 *)

val _ = new_theory"mod_to_con"
val _ = set_grammar_ancestry ["backend_common", "modLang", "conLang",
                              "semanticPrimitives" (* for TypeId *)]

(* for each constructor, its arity, tag, and type *)
val _ = type_abbrev( "flat_tag_env" , ``:conN |-> (num # num # tid_or_exn)``);
val _ = type_abbrev( "tag_env" , ``:(modN, flat_tag_env) fmap # flat_tag_env``);

val _ = Define `
  lookup_tag_flat cn (ftagenv:flat_tag_env) =
  (case FLOOKUP ftagenv cn of
   | NONE => NONE
   | SOME (a,n,t) => SOME (n,t))`;

val lookup_tag_env_def = Define `
  lookup_tag_env id ((mtagenv,tagenv):tag_env) =
    case id of
    | NONE => NONE
    | SOME (Short x) => lookup_tag_flat x tagenv
    | SOME (Long x y) =>
      (case FLOOKUP mtagenv x of
       | NONE => NONE
       | SOME tagenv => lookup_tag_flat y tagenv)`;

val lookup_tag_env_NONE = Q.store_thm("lookup_tag_env_NONE[simp]",
  `lookup_tag_env NONE tagenv = NONE`,
  PairCases_on `tagenv` >>
  rw [lookup_tag_env_def]);

val compile_pat_def = tDefine"compile_pat" (`
  (compile_pat tagenv (Pcon con_id ps) =
    (Pcon (lookup_tag_env con_id tagenv) (MAP (compile_pat tagenv) ps)))
  ∧
  (compile_pat tagenv (Ptannot p t) = compile_pat tagenv p)`
  ||> otherwise_homomorphic)
  (WF_REL_TAC `inv_image $< (\(x,p). pat_size p)` >>
   srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
   Induct_on `ps` >>
   srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
   srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
   res_tac >>
   decide_tac);

val compile_exp_def = tDefine"compile_exp" (`
  (compile_exp tagenv ((Con cn es):modLang$exp) =
   (Con (lookup_tag_env cn tagenv) (compile_exps tagenv es)):conLang$exp)
  ∧
  (compile_exp tagenv (App op es) =
   App (Op op) (compile_exps tagenv es))
  ∧
  (compile_exp tagenv (If e1 e2 e3) =
   Mat (compile_exp tagenv e1)
     [(Pcon(SOME(true_tag,TypeId(Short"bool")))[],compile_exp tagenv e2);
      (Pcon(SOME(false_tag,TypeId(Short"bool")))[],compile_exp tagenv e3)])
  ∧
  (compile_exps tagenv (e::es) =
   compile_exp tagenv e :: compile_exps tagenv es)
  ∧
  (compile_pes tagenv ((p,e)::pes) =
   (compile_pat tagenv p, compile_exp tagenv e) :: compile_pes tagenv pes)
  ∧
  (compile_funs tagenv ((f:tvarN,x:tvarN,e)::funs) =
   (f,x,compile_exp tagenv e) :: compile_funs tagenv funs)`
  ||> otherwise_homomorphic)
  (WF_REL_TAC `inv_image $< (\x. case x of INL (x,e) => exp_size e
                                         | INR (INL (x,es)) => exp6_size es
                                         | INR (INR (INL (x,pes))) => exp3_size pes
                                         | INR (INR (INR (x,funs))) => exp1_size funs)`);

val compile_exps_map = Q.store_thm("compile_exps_map",
  `!tagenv es.
    compile_exps tagenv es = MAP (compile_exp tagenv) es`,
  Induct_on `es` >>
  rw [compile_exp_def]);

val compile_funs_map = Q.store_thm("compile_funs_map",
  `!funs.
    compile_funs cenv funs = MAP (\(f,x,e). (f,x,compile_exp cenv e)) funs`,
   induct_on `funs` >>
   rw [compile_exp_def] >>
   PairCases_on `h` >>
   rw [compile_exp_def]);

(* next exception tag (arity-indexed),
 * current tag env,
 * current exh_ctors_env,
 * accumulator (for use on module exit) *)
val _ = type_abbrev( "tagenv_state", ``:num spt # tag_env # exh_ctors_env``);
val _ = type_abbrev( "tagenv_state_acc", ``:tagenv_state # flat_tag_env``);

val _ = Define `
  get_tagenv (((next,tagenv,exh),acc):tagenv_state_acc) = tagenv`;

val _ = Define `
  get_exh ((next,tagenv,exh):tagenv_state) = exh`;

val _ = Define `
  insert_tag_env cn tag ((mtagenv,ftagenv):tag_env) =
    (mtagenv,ftagenv |+ (cn, tag))`;

val _ = Define `
  alloc_tag tn cn arity (((next,tagenv,exh),acc):tagenv_state_acc) =
  (case tn of
   | TypeExn _ =>
     let tag = (case lookup arity next of
                | NONE => 0
                | SOME n => n)
     in
       ((insert arity (tag+1) next,
         insert_tag_env cn (arity,tag,tn) tagenv,
         exh),
        acc |+ (cn, (arity,tag,tn)))
   | TypeId tid =>
     let (tag,exh) =
       (case FLOOKUP exh tid of
        | NONE => (0, exh |+ (tid, insert arity 1 LN))
        | SOME m => (case lookup arity m of
                     | NONE => (0, exh |+ (tid, insert arity 1 m))
                     | SOME t => (t, exh |+ (tid, insert arity (t+1) m))))
     in
       ((next,
         insert_tag_env cn (arity,tag,tn) tagenv,
         exh),
        acc |+ (cn, (arity,tag,tn))))`;

val _ = Define `
  (alloc_tags mn st [] = st)
  ∧
  (alloc_tags mn st ((tvs,tn,constrs)::types) =
   let st' =
     FOLDL (λst' (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn (LENGTH ts) st') st constrs
   in
     alloc_tags mn st' types)`;

val _ = Define `
  (compile_decs st [] = (st,[]))
  ∧
  (compile_decs st (d::ds) =
   (case d of
    | Dlet n e =>
      let (st', ds') = compile_decs st ds in
        (st', (Dlet n (compile_exp (get_tagenv st) e)::ds'))
    | Dletrec funs =>
      let (st', ds') = (compile_decs st ds) in
        (st', (Dletrec (compile_funs (get_tagenv st) funs)::ds'))
    | Dtype mn type_def =>
      let st'' = (alloc_tags mn st type_def) in
      let (st',ds') = (compile_decs st'' ds) in
        (st', ds')
    | Dexn mn cn ts =>
      let (st', ds') = (compile_decs (alloc_tag (TypeExn (mk_id mn cn)) cn (LENGTH ts) st) ds) in
        (st', ds')))`;

val _ = Define `
  mod_tagenv mn l ((mtagenv,tagenv):tag_env) =
  (case mn of
   | NONE =>    (mtagenv,            l ⊌ tagenv)
   | SOME mn => (mtagenv |+ (mn, l), tagenv))`;

val _ = Define `
  compile_prompt tagenv_st prompt =
  (case prompt of
   Prompt mn ds =>
     let (((next',tagenv',exh'),acc'), ds') = compile_decs (tagenv_st,FEMPTY) ds in
       ((next',mod_tagenv mn acc' (get_tagenv (tagenv_st,acc')),exh'), Prompt ds'))`;

val _ = Define `
  (compile_prog st [] = (st, []))
  ∧
  (compile_prog st (p::ps) =
   let (st',p') = compile_prompt st p in
   let (st'',ps') = compile_prog st' ps in
   (st'',(p'::ps')))`;

val _ = Datatype`
  config = <| next_exception : num spt
            ; tag_env : tag_env
            ; exh_ctors_env : exh_ctors_env
            |>`;

val empty_config_def = Define`
  empty_config = <| next_exception := LN
                  ; tag_env := (FEMPTY,FEMPTY)
                  ; exh_ctors_env := FEMPTY |>`;

val compile_def = Define`
  compile c p =
  let ((n,t,e),p) =
    compile_prog (c.next_exception, c.tag_env, c.exh_ctors_env) p in
  (<| next_exception := n; tag_env := t; exh_ctors_env := e|>, p)`;

val _ = export_theory()
