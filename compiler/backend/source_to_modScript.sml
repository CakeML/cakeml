open preamble astTheory terminationTheory modLangTheory;

val _ = numLib.prefer_num();

val _ = new_theory"source_to_mod";

(*
 * The translator to modLang keeps two mappings, one mapping module paths to
 * indices into the genv, and the other mapping module paths to constructor ids.
 * All variable references are replaced with global references to the genv index
 * if they are in the mappings. This includes top-level letrec names which are
 * all put into the mapping before translating any of the let rec functions.
 * This enables the semantics of let rec to just create Closures rather than
 * Recclosures.
 *)

(* The traces start at 2 because this expression is called only from within
 * compile_exp, where `mk_cons t 1` has been used. *)
val Bool_def = Define `
 Bool t b =
  let (t1, t2, t3) = (mk_cons t 2, mk_cons t 3, mk_cons t 4) in
   (modLang$App t1 (Opb (if b then Leq else Lt)) [Lit t2 (IntLit 0); Lit t3 (IntLit 0)])`;

val _ = Datatype `
  environment =
    <| c : (modN, conN, ctor_id#type_id) namespace;
       v : (modN, varN, exp) namespace; |>`;

(*
 * EXPLORER: No patterna propagates here. compile_pat just calls itself until
 * the trace is discared.
 *)
val compile_pat_def = tDefine "compile_pat" `
  (compile_pat env (ast$Pvar v) = modLang$Pvar v) ∧
  (compile_pat env Pany = Pany) ∧
  (compile_pat env (Plit l) = Plit l) ∧
  (compile_pat env (ast$Pcon id ps) =
    modLang$Pcon
      (OPTION_JOIN (OPTION_MAP (nsLookup env.c) id))
      (MAP (compile_pat env) ps)) ∧
  (compile_pat env (Pref p) = Pref (compile_pat env p)) ∧
  (compile_pat env (Ptannot p t) = compile_pat env p)`
  (WF_REL_TAC `measure (pat_size o SND)` >>
   rw [] >>
   Induct_on `ps` >>
   rw [astTheory.pat_size_def]
   >- decide_tac >>
   res_tac >>
   decide_tac);

val pat_tups_def = Define`
  (pat_tups t [] = []) ∧
  (pat_tups t (x::xs) =
   let t' = mk_cons t ((LENGTH xs) + 1) in
     (x, Var_local t' x)::pat_tups t xs)`;

val astOp_to_modOp_def = Define `
  astOp_to_modOp (op : ast$op) : modLang$op =
  case op of
    Opn opn => modLang$Opn opn
  | Opb opb => modLang$Opb opb
  | Opw word_size opw => modLang$Opw word_size opw
  | Shift word_size shift num => modLang$Shift word_size shift num
  | FP_cmp cmp => modLang$FP_cmp cmp
  | FP_uop uop => modLang$FP_uop uop
  | FP_bop bop => modLang$FP_bop bop
  | Equality => modLang$Equality
  | Opapp => modLang$Opapp
  | Opassign => modLang$Opassign
  | Opref => modLang$Opref
  | Opderef => modLang$Opderef
  | Aw8alloc => modLang$Aw8alloc
  | Aw8sub => modLang$Aw8sub
  | Aw8length => modLang$Aw8length
  | Aw8update => modLang$Aw8update
  | WordFromInt word_size => modLang$WordFromInt word_size
  | WordToInt word_size => modLang$WordToInt word_size
  | CopyStrStr => modLang$CopyStrStr
  | CopyStrAw8 => modLang$CopyStrAw8
  | CopyAw8Str => modLang$CopyAw8Str
  | CopyAw8Aw8 => modLang$CopyAw8Aw8
  | Ord => modLang$Ord
  | Chr => modLang$Chr
  | Chopb opb => modLang$Chopb opb
  | Implode => modLang$Implode
  | Strsub => modLang$Strsub
  | Strlen => modLang$Strlen
  | Strcat => modLang$Strcat
  | VfromList => modLang$VfromList
  | Vsub => modLang$Vsub
  | Vlength => modLang$Vlength
  | Aalloc => modLang$Aalloc
  | Asub => modLang$Asub
  | Alength => modLang$Alength
  | Aupdate => modLang$Aupdate
  | FFI string => modLang$FFI string`;

(* The traces are passed along without being split for most expressions, since we
 * expect Lannots to appear around every expression. *)

val compile_exp_def = tDefine"compile_exp"`
  (compile_exp t (env:environment) (Raise e) =
    Raise t (compile_exp t env e)) ∧
  (compile_exp t env (Handle e pes) =
    Handle t (compile_exp t env e) (compile_pes t env pes)) ∧
  (compile_exp t env (ast$Lit l) = modLang$Lit t l) ∧
  (compile_exp t env (Con cn es) =
    Con t (OPTION_JOIN (OPTION_MAP (nsLookup env.c) cn))
          (compile_exps t env es)) ∧
  (compile_exp t env (Var x) =
    case nsLookup env.v x of
    | NONE => Var_local t "" (* Can't happen *)
    | SOME x => x) ∧
  (compile_exp t env (Fun x e) =
    let (t1, t2) = (mk_cons t 1, mk_cons t 2) in
      Fun t1 x (compile_exp t (env with v := nsBind x (Var_local t2 x) env.v) e)) ∧
  (compile_exp t env (ast$App op es) =
    if op = AallocEmpty then
      FOLDR (Let t NONE) (modLang$App t Aalloc [Lit t (IntLit (&0)); Lit t (IntLit (&0))])
        (REVERSE (compile_exps t env es))
    else
      modLang$App t (astOp_to_modOp op) (compile_exps t env es)) ∧
  (compile_exp t env (Log lop e1 e2) =
    let t' = mk_cons t 1 in
      case lop of
      | And =>
        If t'
           (compile_exp t env e1)
           (compile_exp t env e2)
           (Bool t F)
      | Or =>
        If t'
           (compile_exp t env e1)
           (Bool t T)
           (compile_exp t env e2)) ∧
  (compile_exp t env (If e1 e2 e3) =
    If t
       (compile_exp t env e1)
       (compile_exp t env e2)
       (compile_exp t env e3)) ∧
  (compile_exp t env (Mat e pes) =
    Mat t (compile_exp t env e) (compile_pes t env pes)) ∧
  (compile_exp t env (Let (SOME x) e1 e2) =
    let (t1, t2) = (mk_cons t 1, mk_cons t 2) in
      Let t1 (SOME x) (compile_exp t env e1)
        (compile_exp t (env with v := nsBind x (Var_local t2 x) env.v) e2)) ∧
  (compile_exp t env (Let NONE e1 e2) =
    Let t NONE (compile_exp t env e1) (compile_exp t env e2)) ∧
  (compile_exp t env (ast$Letrec funs e) =
    let fun_names = MAP FST funs in
    let new_env = nsBindList (MAP (\x. (x, Var_local t x)) fun_names) env.v in
      modLang$Letrec t (compile_funs t (env with v := new_env) funs)
               (compile_exp t (env with v := new_env) e)) ∧
  (compile_exp t env (Tannot e _) = compile_exp t env e) ∧
  (* When encountering a Lannot, we update the trace we are passing *)
  (compile_exp t env (Lannot e (Locs st en)) =
    let t' = if t = None then t else SourceLoc st.row st.col en.row en.col in
      compile_exp t' env e) ∧
  (compile_exps t env [] = []) ∧
  (compile_exps t env (e::es) =
     compile_exp t env e :: compile_exps t env es) ∧
  (compile_pes t env [] = []) ∧
  (compile_pes t env ((p,e)::pes) =
    let pbs = pat_bindings p [] in
    let pts = pat_tups t pbs in
    (compile_pat env p, compile_exp t (env with v := nsBindList pts env.v) e)
    :: compile_pes t env pes) ∧
  (compile_funs t env [] = []) ∧
  (compile_funs t env ((f,x,e)::funs) =
    (f,x,compile_exp t (env with v := nsBind x (Var_local t x) env.v) e) ::
    compile_funs t env funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (t,x,e) => exp_size e
                                        | INR (INL (t,x,es)) => exps_size es
                                        | INR (INR (INL (t,x,pes))) => pes_size pes
                                        | INR (INR (INR (t,x,funs))) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
val compile_exps_append = Q.store_thm("compile_exps_append",
  `!env es es'.
    compile_exps t env (es ++ es') =
    compile_exps t env es ++ compile_exps t env es'`,
  Induct_on `es` >>
  fs [compile_exp_def]);

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
val compile_exps_reverse = Q.store_thm("compile_exps_reverse",
  `!env es.
    compile_exps t env (REVERSE es) = REVERSE (compile_exps t env es)`,
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]);

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
val compile_funs_map = Q.store_thm("compile_funs_map",
  `!env funs.
    compile_funs t env funs =
      MAP (\(f,x,e). (f,x,compile_exp t (env with v := nsBind x (Var_local t x) env.v) e)) funs`,
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]);

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
val compile_funs_dom = Q.store_thm("compile_funs_dom",
  `!funs.
    (MAP (λ(x,y,z). x) funs)
    =
    (MAP (λ(x,y,z). x) (compile_funs t env funs))`,
   induct_on `funs` >>
   rw [compile_exp_def] >>
   PairCases_on `h` >>
   rw [compile_exp_def]);

(* We use om_tra as a basis trace for all orphan traces created here. *)
val om_tra_def = Define`
  om_tra = Cons orphan_trace 1`;

val alloc_defs_def = Define `
  (alloc_defs n next [] = []) ∧
  (alloc_defs n next (x::xs) =
    (x, Var_global (Cons om_tra n) next) :: alloc_defs (n + 1) (next + 1) xs)`;

val fst_alloc_defs = Q.store_thm("fst_alloc_defs",
  `!n next l. MAP FST (alloc_defs n next l) = l`,
  induct_on `l` >>
  rw [alloc_defs_def]);

val alloc_defs_append = Q.store_thm("alloc_defs_append",
  `!m n l1 l2. alloc_defs m n (l1++l2) = alloc_defs m n l1 ++ alloc_defs (m + LENGTH l1) (n + LENGTH l1) l2`,
  induct_on `l1` >>
  srw_tac [ARITH_ss] [alloc_defs_def, arithmeticTheory.ADD1]);

val make_varls_def = Define`
  (make_varls n t [] = [])
  /\
  (make_varls n t (x::xs) =
    let t' = Cons t n in
      Var_local t' x :: make_varls (n+1) t xs)`;

val empty_env_def = Define `
  empty_env = <| v := nsEmpty; c := nsEmpty |>`;

val extend_env_def = Define `
  extend_env e1 e2 =
    <| v := nsAppend e1.v e2.v; c := nsAppend e1.c e2.c |>`;

val lift_env_def = Define `
  lift_env mn e = <| v := nsLift mn e.v; c := nsLift mn e.c |>`;

val _ = Datatype `
  next_indices = <| vidx : num; tidx : num; eidx : num |>`;

val _ = Define `
  lookup_inc i t =
    case sptree$lookup i t of
    | NONE => (0, sptree$insert i 1 t)
    | SOME n => (n, sptree$insert i (n+1) t)`;

val alloc_tags = Define `
  (alloc_tags tid cids [] = (nsEmpty, cids)) ∧
  (alloc_tags tid cids ((cn, ts) :: ctors) =
    let (tag, new_cids) = lookup_inc (LENGTH ts) cids in
    let (ns, new_cids') = alloc_tags tid new_cids ctors in
      (nsBind cn (tag, SOME tid) ns, new_cids'))`;

val compile_decs_def = tDefine "compile_decs" `
  (compile_decs n next env [ast$Dlet locs p e] =
     let (n', t1, t2, t3, t4) = (n + 4, Cons om_tra n, Cons om_tra (n + 1), Cons om_tra (n + 2), Cons om_tra (n + 3)) in
     let e' = compile_exp t1 env e in
     let xs = REVERSE (pat_bindings p []) in
     let l = LENGTH xs in
     let n'' = n' + l in
       (n'', (next with vidx := next.vidx + l),
        <| v := alist_to_ns (alloc_defs n' next.vidx xs); c := nsEmpty |>,
        [modLang$Dlet l (Mat t2 e'
          [(compile_pat env p, Con t3 NONE (make_varls 0 t4 xs))])])) ∧
  (compile_decs n next env [ast$Dletrec locs [(f,x,e)]] =
     (* TODO: The tracing stuff is copy/pasted. Don't know if it's right *)
     let (n', t1, t2, t3, t4) = (n + 4, Cons om_tra n, Cons om_tra (n + 1), Cons om_tra (n + 2), Cons om_tra (n + 3)) in
     let e' = compile_exp t1 env (ast$Letrec [(f,x,e)] (ast$Var (mk_id [] f))) in
       (n' + 1, (next with vidx := next.vidx + 1),
        <| v := alist_to_ns (alloc_defs n' next.vidx [f]); c := nsEmpty |>,
        [modLang$Dlet 1 (Con t4 NONE [e'])])) ∧
  (compile_decs n next env [ast$Dletrec locs funs] =
     let fun_names = REVERSE (MAP FST funs) in
     let env' = <| v := alist_to_ns (alloc_defs n next.vidx fun_names); c := nsEmpty |> in
       (n+2, (next with vidx := next.vidx + LENGTH fun_names), env',
        [Dletrec (compile_funs (Cons om_tra (n+1)) (extend_env env' env) (REVERSE funs))])) ∧
  (compile_decs n next env [Dtype locs type_def] =
    let new_env = MAPi (\tid (_,_,constrs). alloc_tags (next.tidx + tid) LN constrs) type_def in
     (n, (next with tidx := next.tidx + LENGTH type_def),
      <| v := nsEmpty;
         c := FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty new_env |>,
      MAP (λ(ns,cids). Dtype (sptree$toList cids)) new_env)) ∧
  (compile_decs n next env [Dtabbrev locs tvs tn t] =
     (n, next, empty_env, [])) ∧
  (compile_decs n next env [Dexn locs cn ts] =
     (n, (next with eidx := next.eidx + 1),
      <| v := nsEmpty; c := nsSing cn (next.eidx, NONE) |>, [Dexn (LENGTH ts)])) ∧
  (compile_decs n next env [Dmod mn ds] =
     let (n', next', new_env, ds') = compile_decs n next env ds in
       (n', next', (lift_env mn new_env), ds')) ∧
  (compile_decs n next env [] =
    (n, next, empty_env, [])) ∧
  (compile_decs n next env (d::ds) =
     let (n', next1, new_env1, d') = compile_decs n next env [d] in
     let (n'', next2, new_env2, ds') =
       compile_decs n' next1 (extend_env new_env1 env) ds
     in
       (n'', next2, extend_env new_env2 new_env1, d'++ds'))`
 (wf_rel_tac `measure (list_size ast$dec_size o SND o SND o SND)` >>
  rw [] >>
  Induct_on `ds` >>
  rw [astTheory.dec_size_def, list_size_def]);

val _ = Datatype`
  config = <| next : next_indices
            ; mod_env : environment
            |>`;

val empty_config_def = Define`
  empty_config =
    <| next := <| vidx := 0; tidx := 0; eidx := 0 |>; mod_env := empty_env |>`;

val compile_def = Define`
  compile c p =
    let (_,_,e,p') = compile_decs 1 c.next c.mod_env p in
    (c with mod_env := e, p')`;

val _ = export_theory();
