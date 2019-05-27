(*
  This is the compiler phase that translates the CakeML source
  language into flatLang.

  The translator to flatLang keeps two mappings, one mapping module
  paths to indices into the genv, and the other mapping module paths
  to constructor ids.  All variable references are replaced with
  global references to the genv index if they are in the
  mappings. This includes top-level letrec names which are all put
  into the mapping before translating any of the let rec functions.
  This enables the semantics of let rec to just create Closures rather
  than Recclosures.
*)
open preamble astTheory terminationTheory flatLangTheory;
open flat_elimTheory flat_exh_matchTheory flat_uncheck_ctorsTheory
     flat_reorder_matchTheory

val _ = numLib.prefer_num();

val _ = new_theory"source_to_flat";

val _ = Datatype `
  environment =
    <| c : (modN, conN, ctor_id#type_id) namespace;
       v : (modN, varN, exp) namespace; |>`;

(*
 * EXPLORER: No patterna propagates here. compile_pat just calls itself until
 * the trace is discared.
 *)
val compile_pat_def = tDefine "compile_pat" `
  (compile_pat env (ast$Pvar v) = flatLang$Pvar v) ∧
  (compile_pat env Pany = Pany) ∧
  (compile_pat env (Plit l) = Plit l) ∧
  (compile_pat env (ast$Pcon id ps) =
    flatLang$Pcon
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

val astOp_to_flatOp_def = Define `
  astOp_to_flatOp (op : ast$op) : flatLang$op =
  case op of
    Opn opn => flatLang$Opn opn
  | Opb opb => flatLang$Opb opb
  | Opw word_size opw => flatLang$Opw word_size opw
  | Shift word_size shift num => flatLang$Shift word_size shift num
  | FP_cmp cmp => flatLang$FP_cmp cmp
  | FP_uop uop => flatLang$FP_uop uop
  | FP_bop bop => flatLang$FP_bop bop
  | FP_top top => flatLang$FP_top top
  | Equality => flatLang$Equality
  | Opapp => flatLang$Opapp
  | Opassign => flatLang$Opassign
  | Opref => flatLang$Opref
  | Opderef => flatLang$Opderef
  | Aw8alloc => flatLang$Aw8alloc
  | Aw8sub => flatLang$Aw8sub
  | Aw8length => flatLang$Aw8length
  | Aw8update => flatLang$Aw8update
  | WordFromInt word_size => flatLang$WordFromInt word_size
  | WordToInt word_size => flatLang$WordToInt word_size
  | CopyStrStr => flatLang$CopyStrStr
  | CopyStrAw8 => flatLang$CopyStrAw8
  | CopyAw8Str => flatLang$CopyAw8Str
  | CopyAw8Aw8 => flatLang$CopyAw8Aw8
  | Ord => flatLang$Ord
  | Chr => flatLang$Chr
  | Chopb opb => flatLang$Chopb opb
  | Implode => flatLang$Implode
  | Strsub => flatLang$Strsub
  | Strlen => flatLang$Strlen
  | Strcat => flatLang$Strcat
  | VfromList => flatLang$VfromList
  | Vsub => flatLang$Vsub
  | Vlength => flatLang$Vlength
  | Aalloc => flatLang$Aalloc
  | Asub => flatLang$Asub
  | Alength => flatLang$Alength
  | Aupdate => flatLang$Aupdate
  | ListAppend => flatLang$ListAppend
  | ConfigGC => flatLang$ConfigGC
  | FFI string => flatLang$FFI string
  (* default element *)
  | _ => flatLang$ConfigGC`;

(* The traces are passed along without being split for most expressions, since we
 * expect Lannots to appear around every expression. *)

val compile_exp_def = tDefine"compile_exp"`
  (compile_exp t (env:environment) (Raise e) =
    Raise t (compile_exp t env e)) ∧
  (compile_exp t env (Handle e pes) =
    Handle t (compile_exp t env e) (compile_pes t env pes)) ∧
  (compile_exp t env (ast$Lit l) = flatLang$Lit t l) ∧
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
      FOLDR (Let t NONE) (flatLang$App t Aalloc [Lit t (IntLit (&0)); Lit t (IntLit (&0))])
        (REVERSE (compile_exps t env es))
    else
      flatLang$App t (astOp_to_flatOp op) (compile_exps t env es)) ∧
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
      flatLang$Letrec t (compile_funs t (env with v := new_env) funs)
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
Theorem compile_exps_append:
   !env es es'.
    compile_exps t env (es ++ es') =
    compile_exps t env es ++ compile_exps t env es'
Proof
  Induct_on `es` >>
  fs [compile_exp_def]
QED

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
Theorem compile_exps_reverse:
   !env es.
    compile_exps t env (REVERSE es) = REVERSE (compile_exps t env es)
Proof
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]
QED

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
Theorem compile_funs_map:
   !env funs.
    compile_funs t env funs =
      MAP (\(f,x,e). (f,x,compile_exp t (env with v := nsBind x (Var_local t x) env.v) e)) funs
Proof
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]
QED

(*
 * EXPLORER: Again, the `t` is for position information.
 *)
Theorem compile_funs_dom:
   !funs.
    (MAP (λ(x,y,z). x) funs)
    =
    (MAP (λ(x,y,z). x) (compile_funs t env funs))
Proof
   induct_on `funs` >>
   rw [compile_exp_def] >>
   PairCases_on `h` >>
   rw [compile_exp_def]
QED

(* We use om_tra as a basis trace for all orphan traces created here. *)
val om_tra_def = Define`
  om_tra = Cons orphan_trace 1`;

val alloc_defs_def = Define `
  (alloc_defs n next [] = []) ∧
  (alloc_defs n next (x::xs) =
    (x, App (Cons om_tra n) (GlobalVarLookup next) []) :: alloc_defs (n + 1) (next + 1) xs)`;

Theorem fst_alloc_defs:
   !n next l. MAP FST (alloc_defs n next l) = l
Proof
  induct_on `l` >>
  rw [alloc_defs_def]
QED

Theorem alloc_defs_append:
   !m n l1 l2. alloc_defs m n (l1++l2) = alloc_defs m n l1 ++ alloc_defs (m + LENGTH l1) (n + LENGTH l1) l2
Proof
  induct_on `l1` >>
  srw_tac [ARITH_ss] [alloc_defs_def, arithmeticTheory.ADD1]
QED

val make_varls_def = Define`
  (make_varls n t idx [] = Con t NONE []) ∧
  (make_varls n t idx [x] = App t (GlobalVarInit idx) [Var_local t x])
  /\
  (make_varls n t idx (x::xs) =
    let t' = Cons t n in
      Let t' NONE (App t' (GlobalVarInit idx) [Var_local t' x])
        (make_varls (n+1) t (idx + 1) xs))`;

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
        [flatLang$Dlet (Mat t2 e'
          [(compile_pat env p, make_varls 0 t4 next.vidx xs)])])) ∧
  (compile_decs n next env [ast$Dletrec locs [(f,x,e)]] =
     (* TODO: The tracing stuff is copy/pasted. Don't know if it's right *)
     let (n', t1, t2, t3, t4) = (n + 4, Cons om_tra n, Cons om_tra (n + 1), Cons om_tra (n + 2), Cons om_tra (n + 3)) in
     let e' = compile_exp t1 env (ast$Letrec [(f,x,e)] (ast$Var (mk_id [] f))) in
       (n' + 1, (next with vidx := next.vidx + 1),
        <| v := alist_to_ns (alloc_defs n' next.vidx [f]); c := nsEmpty |>,
        [flatLang$Dlet (App t4 (GlobalVarInit next.vidx) [e'])])) ∧
  (compile_decs n next env [ast$Dletrec locs funs] =
     (* TODO: The tracing stuff is copy/pasted. Don't know if it's right *)
     let (n', t1, t2, t3, t4) = (n + 4, Cons om_tra n, Cons om_tra (n + 1), Cons om_tra (n + 2), Cons om_tra (n + 3)) in
     let fun_names = REVERSE (MAP FST funs) in
     let env' = <| v := alist_to_ns (alloc_defs n next.vidx fun_names); c := nsEmpty |> in
       (n+2, (next with vidx := next.vidx + LENGTH fun_names), env',
        (MAPi (\i (f,x,e). (Dlet (App t4 (GlobalVarInit (next.vidx + i)) [flatLang$Fun t4 x e])))
              (compile_funs (Cons om_tra (n+1)) (extend_env env' env) (REVERSE funs))))) ∧
  (compile_decs n next env [Dtype locs type_def] =
    let new_env = MAPi (\tid (_,_,constrs). alloc_tags (next.tidx + tid) LN constrs) type_def in
     (n, (next with tidx := next.tidx + LENGTH type_def),
      <| v := nsEmpty;
         c := FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty new_env |>,
      MAPi (λi (ns,cids). flatLang$Dtype (next.tidx + i) cids) new_env)) ∧
  (compile_decs n next env [Dtabbrev locs tvs tn t] =
     (n, next, empty_env, [])) ∧
  (compile_decs n next env [Dexn locs cn ts] =
     (n, (next with eidx := next.eidx + 1),
      <| v := nsEmpty; c := nsSing cn (next.eidx, NONE) |>, [Dexn next.eidx (LENGTH ts)])) ∧
  (compile_decs n next env [Dmod mn ds] =
     let (n', next', new_env, ds') = compile_decs n next env ds in
       (n', next', (lift_env mn new_env), ds')) ∧
  (compile_decs n next env [Dlocal lds ds] =
     let (n', next1, new_env1, lds') = compile_decs n next env lds in
     let (n'', next2, new_env2, ds') = compile_decs n' next1
        (extend_env new_env1 env) ds
     in (n'', next2, new_env2, lds'++ds')) ∧
  (compile_decs n next env [] =
    (n, next, empty_env, [])) ∧
  (compile_decs n next env (d::ds) =
     let (n', next1, new_env1, d') = compile_decs n next env [d] in
     let (n'', next2, new_env2, ds') =
       compile_decs n' next1 (extend_env new_env1 env) ds
     in
       (n'', next2, extend_env new_env2 new_env1, d'++ds'))`
 (wf_rel_tac `measure (list_size ast$dec_size o SND o SND o SND)`
  >> rw [dec1_size_eq]);

val _ = Datatype`
  config = <| next : next_indices
            ; mod_env : environment
            |>`;

val empty_config_def = Define`
  empty_config =
    <| next := <| vidx := 0; tidx := 0; eidx := 0 |>; mod_env := empty_env |>`;

val compile_flat_def = Define `
  compile_flat = flat_reorder_match$compile_decs
               o flat_uncheck_ctors$compile_decs
               o flat_elim$remove_flat_prog
               o SND o flat_exh_match$compile`;

val glob_alloc_def = Define `
  glob_alloc next c =
    Dlet
      (Let om_tra NONE
        (App om_tra
          (GlobalVarAlloc (next.vidx - c.next.vidx)) [])
        (flatLang$Con om_tra NONE []))`;

val compile_prog_def = Define`
  compile_prog c p =
    let (_,next,e,p') = compile_decs 1n c.next c.mod_env p in
    (<| next := next; mod_env := e |>, glob_alloc next c :: p')`;

val compile_def = Define `
  compile c p =
    let (c', p') = compile_prog c p in
    (c', compile_flat p')`;

val _ = export_theory();
