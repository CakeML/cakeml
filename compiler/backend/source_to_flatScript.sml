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
open flat_elimTheory flat_patternTheory;


val _ = new_theory"source_to_flat";
val _ = set_grammar_ancestry ["ast", "flatLang", "termination"];
val _ = numLib.prefer_num();
val _ = temp_tight_equality ();

val _ = Datatype `
  var_name = Glob tra num | Local tra string`

Datatype:
  environment =
    <| c : (modN, conN, ctor_id#type_group_id) namespace;
       v : (modN, varN, var_name) namespace; |>
End

Datatype:
  environment_generation_store =
    <| next : num;
       generation : num;
       envs : environment sptree$num_map |>
End

Datatype:
  environment_store =
    <| next : num;
       env_gens : (environment sptree$num_map) sptree$num_map |>
End

val compile_var_def = Define `
  compile_var t (Glob _ i) = App t (GlobalVarLookup i) [] /\
  compile_var t (Local _ s) = Var_local t s`;

Theorem ast_pat1_size:
  ast$pat1_size xs = LENGTH xs + SUM (MAP pat_size xs)
Proof
  Induct_on `xs` \\ simp [astTheory.pat_size_def]
QED

Definition compile_pat_def:
  (compile_pat env (ast$Pvar v) = flatLang$Pvar v) ∧
  (compile_pat env Pany = Pany) ∧
  (compile_pat env (Plit l) = Plit l) ∧
  (compile_pat env (ast$Pcon id ps) =
    flatLang$Pcon
      (OPTION_JOIN (OPTION_MAP (nsLookup env.c) id))
      (MAP (compile_pat env) ps)) ∧
  (compile_pat env (Pref p) = Pref (compile_pat env p)) ∧
  (compile_pat env (Ptannot p t) = compile_pat env p)
Termination
  WF_REL_TAC `measure (pat_size o SND)` >>
  rw [ast_pat1_size] >>
  fs [MEM_SPLIT, SUM_APPEND]
End

val pat_tups_def = Define`
  (pat_tups t [] = []) ∧
  (pat_tups t (x::xs) =
   let t' = mk_cons t ((LENGTH xs) + 1) in
     (x, Local t' x)::pat_tups t xs)`;

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
  | FP_top t_op => flatLang$FP_top t_op
  | Equality => flatLang$Equality
  | Opapp => flatLang$Opapp
  | Opassign => flatLang$Opassign
  | Opref => flatLang$Opref
  | Opderef => flatLang$El 0
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
  | Explode => flatLang$Explode
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
  | Asub_unsafe => flatLang$Asub_unsafe
  | Aupdate_unsafe => flatLang$Aupdate_unsafe
  | Aw8sub_unsafe => flatLang$Aw8sub_unsafe
  | Aw8update_unsafe => flatLang$Aw8update_unsafe
  | ListAppend => flatLang$ListAppend
  | ConfigGC => flatLang$ConfigGC
  | FFI string => flatLang$FFI string
  | Eval => Eval
  (* default element *)
  | _ => flatLang$ConfigGC`;

Definition type_group_id_type_def:
  type_group_id_type NONE = NONE /\
  type_group_id_type (SOME (cn, NONE)) = SOME (cn, NONE) /\
  type_group_id_type (SOME (cn, (SOME (ty_id, ctors)))) = SOME (cn, SOME ty_id)
End

Theorem type_group_id_type_MAP:
  type_group_id_type = OPTION_MAP (I ## OPTION_MAP FST)
Proof
  simp [FUN_EQ_THM]
  \\ ho_match_mp_tac type_group_id_type_ind
  \\ simp [type_group_id_type_def]
QED

Definition str_sep_def:
  str_sep = "_"
End

Definition join_all_names_aux_def:
  join_all_names_aux [] ys = ys ∧
  join_all_names_aux (x::xs) ys =
    case ys of [] => join_all_names_aux xs (x::ys)
    | _ => join_all_names_aux xs (x::str_sep::ys)
End

Definition join_all_names_def:
  join_all_names xs =
    case xs of
    | [x] => x
    | _ => FLAT (join_all_names_aux xs [])
End

val compile_exp_def = tDefine"compile_exp"`
  (compile_exp (t:string list) (env:environment) (Raise e) =
    Raise None (compile_exp t env e)) ∧
  (compile_exp t env (Handle e pes) =
    Handle None (compile_exp t env e) (compile_pes t env pes)) ∧
  (compile_exp t env (ast$Lit l) = flatLang$Lit None l) ∧
  (compile_exp t env (Con cn es) =
    Con None (OPTION_JOIN (OPTION_MAP (type_group_id_type o nsLookup env.c) cn))
          (compile_exps t env es)) ∧
  (compile_exp t env (Var x) =
    case nsLookup env.v x of
    | NONE => Var_local None "" (* Can't happen *)
    | SOME x => compile_var None x) ∧
  (compile_exp t env (Fun x e) =
    Fun (join_all_names t) x
      (compile_exp t (env with v := nsBind x (Local None x) env.v) e)) ∧
  (compile_exp t env (ast$App op es) =
    if op = AallocEmpty then
      FOLDR (Let None NONE) (flatLang$App None Aalloc [Lit None (IntLit (&0));
                                                       Lit None (IntLit (&0))])
        (REVERSE (compile_exps t env es))
    else
    (if op = Eval then
      Let None NONE (flatLang$App None Eval (compile_exps t env es))
        (Let None (SOME "r") (flatLang$App None (GlobalVarLookup 0) [])
          (App None (El 0) [Var_local None "r"]))
    else
      flatLang$App None (astOp_to_flatOp op) (compile_exps t env es))) ∧
  (compile_exp t env (Log lop e1 e2) =
      case lop of
      | And =>
        If None
           (compile_exp t env e1)
           (compile_exp t env e2)
           (Bool None F)
      | Or =>
        If None
           (compile_exp t env e1)
           (Bool None T)
           (compile_exp t env e2)) ∧
  (compile_exp t env (If e1 e2 e3) =
    If None
       (compile_exp t env e1)
       (compile_exp t env e2)
       (compile_exp t env e3)) ∧
  (compile_exp t env (Mat e pes) =
    Mat None (compile_exp t env e) (compile_pes t env pes)) ∧
  (compile_exp t env (Let (SOME x) e1 e2) =
      Let None (SOME x) (compile_exp (x::t) env e1)
        (compile_exp t (env with v := nsBind x (Local None x) env.v) e2)) ∧
  (compile_exp t env (Let NONE e1 e2) =
    Let None NONE (compile_exp t env e1) (compile_exp t env e2)) ∧
  (compile_exp t env (ast$Letrec funs e) =
    let fun_names = MAP FST funs in
    let new_env = nsBindList (MAP (\x. (x, Local None x)) fun_names) env.v in
      flatLang$Letrec (join_all_names t) (compile_funs t (env with v := new_env) funs)
               (compile_exp t (env with v := new_env) e)) ∧
  (compile_exp t env (Tannot e _) = compile_exp t env e) ∧
  (* When encountering a Lannot, we update the trace we are passing *)
  (compile_exp t env (Lannot e (Locs st en)) = compile_exp t env e) ∧
  (compile_exps t env [] = []) ∧
  (compile_exps t env (e::es) =
     compile_exp t env e :: compile_exps t env es) ∧
  (compile_pes t env [] = []) ∧
  (compile_pes t env ((p,e)::pes) =
    let pbs = pat_bindings p [] in
    let pts = pat_tups None pbs in
    (compile_pat env p, compile_exp t (env with v := nsBindList pts env.v) e)
    :: compile_pes t env pes) ∧
  (compile_funs t env [] = []) ∧
  (compile_funs t env ((f,x,e)::funs) =
    (f,x,compile_exp (f::t) (env with v := nsBind x (Local None x) env.v) e) ::
    compile_funs t env funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (t,x,e) => exp_size e
                                        | INR (INL (t,x,es)) => exps_size es
                                        | INR (INR (INL (t,x,pes))) => pes_size pes
                                        | INR (INR (INR (t,x,funs))) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);

Theorem compile_exps_append:
   !env es es'.
    compile_exps t env (es ++ es') =
    compile_exps t env es ++ compile_exps t env es'
Proof
  Induct_on `es` >>
  fs [compile_exp_def]
QED

Theorem compile_exps_reverse:
   !env es.
    compile_exps t env (REVERSE es) = REVERSE (compile_exps t env es)
Proof
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]
QED

Theorem compile_funs_map:
   !env funs.
    compile_funs t env funs =
      MAP (\(f,x,e). (f,x,compile_exp
        (f::t) (env with v := nsBind x (Local None x) env.v) e)) funs
Proof
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]
QED

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

val om_tra_def = Define`
  om_tra = Cons orphan_trace 1`;

val alloc_defs_def = Define `
  (alloc_defs n next [] = []) ∧
  (alloc_defs n next (x::xs) =
    (x, Glob om_tra next) :: alloc_defs (n + 1) (next + 1) xs)`;

Theorem fst_alloc_defs:
   !n next l. MAP FST (alloc_defs n next l) = l
Proof
  induct_on `l` >>
  rw [alloc_defs_def]
QED

Theorem alloc_defs_append:
   !m n l1 l2.
     alloc_defs m n (l1++l2) =
     alloc_defs m n l1 ++ alloc_defs (m + LENGTH l1) (n + LENGTH l1) l2
Proof
  induct_on `l1` >>
  srw_tac [ARITH_ss] [alloc_defs_def, arithmeticTheory.ADD1]
QED

val make_varls_def = Define`
  (make_varls n t idx [] = Con None NONE []) ∧
  (make_varls n t idx [x] = App None (GlobalVarInit idx) [Var_local None x])
  /\
  (make_varls n (t:tra) idx (x::xs) =
      Let None NONE (App None (GlobalVarInit idx) [Var_local None x])
        (make_varls (n+1) None (idx + 1) xs):flatLang$exp)`;

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

Definition alloc_tags1_def:
  (alloc_tags1 [] = (nsEmpty, LN, [])) ∧
  (alloc_tags1 ((cn, ts) :: ctors) =
    let (ns, cids, tag_list) = alloc_tags1 ctors in
    let arity = LENGTH ts in
    let (tag, new_cids) = lookup_inc arity cids in
      (nsBind cn tag ns, new_cids, (tag, arity) :: tag_list))
End

Definition alloc_tags_def:
  alloc_tags tid ctors =
    let (con_ns, cid_spt, tag_list) = alloc_tags1 ctors in
    (nsMap (\tag. (tag, SOME (tid, tag_list))) con_ns, cid_spt)
End

Definition env_id_tuple_def:
  env_id_tuple gen id = Con None NONE
    [Lit None (IntLit (& gen)); Lit None (IntLit (& id))]
End

val compile_decs_def = tDefine "compile_decs" `
  (compile_decs (t:string list) n next env envs [ast$Dlet locs p e] =
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
  (compile_decs t n next env envs [ast$Dletrec locs funs] =
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
  (compile_decs t n next env envs [Dtype locs type_def] =
    let new_env = MAPi (\tid (_,_,constrs). alloc_tags (next.tidx + tid) constrs) type_def in
     (n, (next with tidx := next.tidx + LENGTH type_def),
      <| v := nsEmpty;
         c := FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty new_env |>,
      envs,
      MAPi (λi (ns,cids). flatLang$Dtype (next.tidx + i) cids) new_env)) ∧
  (compile_decs _ n next env envs [Dtabbrev locs tvs tn t] =
     (n, next, empty_env, envs, [])) ∧
  (compile_decs t n next env envs [Dexn locs cn ts] =
     (n, (next with eidx := next.eidx + 1),
      <| v := nsEmpty; c := nsSing cn (next.eidx, NONE) |>,
      envs,
      [Dexn next.eidx (LENGTH ts)])) ∧
  (compile_decs t n next env envs [Dmod mn ds] =
     let (n', next', new_env, envs', ds') = compile_decs (mn::t) n next env envs ds in
       (n', next', (lift_env mn new_env), envs', ds')) ∧
  (compile_decs t n next env envs [Dlocal lds ds] =
     let (n', next1, new_env1, envs', lds') = compile_decs t n next env envs lds in
     let (n'', next2, new_env2, envs'', ds') = compile_decs t n' next1
        (extend_env new_env1 env) envs' ds
     in (n'', next2, new_env2, envs'', lds'++ds')) ∧
  (compile_decs t n next env envs [Denv nenv] =
     (n + 1, next with vidx := next.vidx + 1,
        <| v := nsBind nenv (Glob None next.vidx) nsEmpty; c := nsEmpty |>,
        envs with <| next := envs.next + 1;
            envs := insert envs.next env envs.envs |>,
        [flatLang$Dlet (App None (GlobalVarInit next.vidx)
            [env_id_tuple envs.generation envs.next])])) ∧
  (compile_decs t n next env envs [] =
    (n, next, empty_env, envs, [])) ∧
  (compile_decs t n next env envs (d::ds) =
     let (n', next1, new_env1, envs1, d') = compile_decs t n next env envs [d] in
     let (n'', next2, new_env2, envs2, ds') =
       compile_decs t n' next1 (extend_env new_env1 env) envs1 ds
     in
       (n'', next2, extend_env new_env2 new_env1, envs2, d'++ds'))`
 (wf_rel_tac `measure (list_size ast$dec_size o SND o SND o SND o SND o SND)`
  >> rw [dec1_size_eq]);

val _ = Datatype`
  config = <| next : next_indices
            ; mod_env : environment
            ; pattern_cfg : flat_pattern$config
            ; envs : environment_store
            |>`;

val empty_config_def = Define`
  empty_config =
    <| next := <| vidx := 0; tidx := 0; eidx := 0 |>;
        mod_env := empty_env;
        pattern_cfg := flat_pattern$init_config (K 0);
        envs := <| next := 0; env_gens := LN |>
    |>`;

val compile_flat_def = Define `
  compile_flat pcfg = MAP (flat_pattern$compile_dec pcfg)
    o flat_elim$remove_flat_prog`;

val glob_alloc_def = Define `
  glob_alloc next c =
    Dlet
      (Let om_tra NONE
        (App om_tra
          (GlobalVarAlloc (next.vidx - c.next.vidx)) [])
        (flatLang$Con om_tra NONE []))`;

Definition alloc_env_ref_def:
  alloc_env_ref = Dlet (App None (GlobalVarInit 0)
    [App None Opref [Con None NONE []]])
End

val compile_prog_def = Define`
  compile_prog c p =
    let next = c.next with <| vidx := c.next.vidx + 1 |> in
    let envs = <| next := 0; generation := c.envs.next; envs := LN |> in
    let (_,next,e,gen,p') = compile_decs [] 1n next c.mod_env envs p in
    let envs2 = <| next := c.envs.next + 1;
        env_gens := insert c.envs.next gen.envs c.envs.env_gens |> in
    (c with <| next := next; envs := envs2 |>,
        glob_alloc next c :: alloc_env_ref :: p')`;

Definition lookup_env_id_def:
  lookup_env_id env_id envs = case lookup (FST env_id) envs.env_gens of
  | NONE => empty_env
  | SOME gen => (case lookup (SND env_id) gen of
    | NONE => empty_env
    | SOME env => env
  )
End

val store_env_id_def = Define`
  store_env_id gen id =
    Dlet (Let None (SOME "r") (flatLang$App None (GlobalVarLookup 0) [])
        (App None Opassign [Var_local None "r"; env_id_tuple gen id]))`;

val inc_compile_prog_def = Define`
  inc_compile_prog env_id c p =
    let env = lookup_env_id env_id c.envs in
    let envs = <| next := 0; generation := c.envs.next; envs := LN |> in
    let (_,next,e,gen,p') = compile_decs [] 1n c.next env envs p in
    let gen_envs = insert gen.next (extend_env e env) gen.envs in
    let envs2 = <| next := c.envs.next + 1;
        env_gens := insert c.envs.next gen_envs c.envs.env_gens |> in
    (c with <| next := next; envs := envs2 |>,
        glob_alloc next c :: p' ++ [store_env_id gen.generation gen.next])`;

val compile_def = Define `
  compile c p =
    let (c', p') = compile_prog c p in
    let p' = compile_flat c'.pattern_cfg p' in
    (c', p')`;

val inc_compile_def = Define `
  inc_compile env_id c p =
    let (c', p') = inc_compile_prog env_id c p in
    let p' = compile_flat c'.pattern_cfg p' in
    (c', p')`;

val _ = export_theory();
