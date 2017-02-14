open preamble astTheory terminationTheory modLangTheory;

val _ = numLib.prefer_num();

val _ = new_theory"source_to_mod";

(*
 * The translator to modLang keeps two mappings, one mapping module paths to
 * indices into the genv, and the other mapping top-level non-module bindings
 * to genv indices. All variable references are replaced with global references
 * to the genv index if they are in the mappings. This includes top-level
 * letrec names which are all put into the mapping before translating any of
 * the let rec functions. This enables the semantics of let rec to just create
 * Closures rather than Recclosures.
 *)

val Bool_def = Define `
 Bool t b = (App t (Opb (if b then Leq else Lt)) [Lit t (IntLit 0); Lit t (IntLit 0)])`;

(*
 * EXPLORER: No patterna propagates here. compile_pat just calls itself until the trace is
 * discared.
 *)
val compile_pat_def = tDefine "compile_pat" `
  (compile_pat (ast$Pvar v) = ast$Pvar v) ∧
  (compile_pat (Plit l) = Plit l) ∧
  (compile_pat (Pcon id ps) = Pcon id (MAP compile_pat ps)) ∧
  (compile_pat (Pref p) = Pref (compile_pat p)) ∧
  (compile_pat (Ptannot p t) = compile_pat p)`
  (WF_REL_TAC `measure pat_size` >>
   rw [] >>
   Induct_on `ps` >>
   rw [pat_size_def]
   >- decide_tac >>
   res_tac >>
   decide_tac);

val compile_exp_def = tDefine"compile_exp"`
  (compile_exp t env (Raise e) =
    Raise t (compile_exp t env e))
  ∧
  (compile_exp t env (Handle e pes) =
    Handle t (compile_exp t env e) (compile_pes t env pes))
  ∧
  (compile_exp t env (ast$Lit l) = modLang$Lit t l)
  ∧
  (compile_exp t env (Con cn es) = Con t cn (compile_exps t env es))
  ∧
  (compile_exp t env (Var x) =
    case nsLookup env x of
    | NONE => Var_local t "" (* Can't happen *)
    | SOME x => x)
  ∧
  (compile_exp t env (Fun x e) =
    Fun t x (compile_exp t (nsBind x (Var_local t x) env) e))
  ∧
  (compile_exp t env (App op es) =
    App t op (compile_exps t env es))
  ∧
  (compile_exp t env (Log lop e1 e2) =
    case lop of
    | And =>
      If t
         (compile_exp t env e1)
         (compile_exp t env e2)
         (Bool t F)
    | Or =>
      If t
         (compile_exp t env e1)
         (Bool t T)
         (compile_exp t env e2))
  ∧
  (compile_exp t env (If e1 e2 e3) =
    If t
       (compile_exp t env e1)
       (compile_exp t env e2)
       (compile_exp t env e3))
  ∧
  (compile_exp t env (Mat e pes) =
    Mat t (compile_exp t env e) (compile_pes t env pes))
  ∧
  (compile_exp t env (Let (SOME x) e1 e2) =
    Let t (SOME x) (compile_exp t env e1) (compile_exp t (nsBind x (Var_local t x) env) e2))
  ∧
  (compile_exp t env (Let NONE e1 e2) =
    Let t NONE (compile_exp t env e1) (compile_exp t env e2))
  ∧
  (compile_exp t env (Letrec funs e) =
    let fun_names = MAP FST funs in
    let new_env = nsBindList (MAP (\x. (x, Var_local t x)) fun_names) env in
      Letrec t (compile_funs t new_env funs) (compile_exp t new_env e))
  ∧
  (compile_exp t env (Tannot e _) = compile_exp t env e)
  ∧
  (compile_exp t env (Lannot e l) =
    case l of
       | locn l1 l2 l3 => compile_exp (Cons (Cons (Cons Empty l3) l2) l1) env e)
  ∧
  (compile_exps t env [] = [])
  ∧
  (compile_exps t env (e::es) =
     compile_exp t env e :: compile_exps t env es)
  ∧
  (compile_pes t env [] = [])
  ∧
  (compile_pes t env ((p,e)::pes) =
    (compile_pat p, compile_exp t (nsBindList (MAP (\x. (x, Var_local t x)) (pat_bindings p [])) env) e)
    :: compile_pes t env pes)
  ∧
  (compile_funs t env [] = [])
  ∧
  (compile_funs t env ((f,x,e)::funs) =
    (f,x,compile_exp t (nsBind x (Var_local t x) env) e) :: compile_funs t env funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (t,x,e) => exp_size e
                                        | INR (INL (t,x,es)) => exps_size es
                                        | INR (INR (INL (t,x,pes))) => pes_size pes
                                        | INR (INR (INR (t,x,funs))) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);

val compile_exps_append = Q.store_thm("compile_exps_append",
  `!env es es'.
    compile_exps t env (es ++ es') =
    compile_exps t env es ++ compile_exps t env es'`,
  Induct_on `es` >>
  fs [compile_exp_def]);

val compile_exps_reverse = Q.store_thm("compile_exps_reverse",
  `!env es.
    compile_exps t env (REVERSE es) = REVERSE (compile_exps t env es)`,
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]);

val compile_funs_map = Q.store_thm("compile_funs_map",
  `!env funs.
    compile_funs t env funs = MAP (\(f,x,e). (f,x,compile_exp t (nsBind x (Var_local
    t x) env) e)) funs`,
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]);

val compile_funs_dom = Q.store_thm("compile_funs_dom",
  `!funs.
    (MAP (λ(x,y,z). x) funs)
    =
    (MAP (λ(x,y,z). x) (compile_funs t env funs))`,
   induct_on `funs` >>
   rw [compile_exp_def] >>
   PairCases_on `h` >>
   rw [compile_exp_def]);

val alloc_defs_def = Define `
  (alloc_defs next [] = []) ∧
  (alloc_defs next (x::xs) =
    (x, Var_global Empty next) :: alloc_defs (next + 1) xs)`;

val fst_alloc_defs = Q.store_thm("fst_alloc_defs",
  `!next l. MAP FST (alloc_defs next l) = l`,
  induct_on `l` >>
  rw [alloc_defs_def]);

val alloc_defs_append = Q.store_thm("alloc_defs_append",
  `!n l1 l2. alloc_defs n (l1++l2) = alloc_defs n l1 ++ alloc_defs (n + LENGTH l1) l2`,
  induct_on `l1` >>
  srw_tac [ARITH_ss] [alloc_defs_def, arithmeticTheory.ADD1]);

val compile_dec_def = Define `
 (compile_dec next mn env d =
  case d of
   | Dlet p e =>
       let e' = compile_exp Empty env e in
       let xs = REVERSE (pat_bindings p []) in
       let l = LENGTH xs in
         (next + l,
          alist_to_ns (alloc_defs next xs),
          Dlet l (Mat Empty e' [(compile_pat p, Con Empty NONE (MAP (Var_local Empty) xs))]))
   | Dletrec funs =>
       let fun_names = REVERSE (MAP FST funs) in
       let env' = alist_to_ns (alloc_defs next fun_names) in
         (next + LENGTH fun_names,
          env',
          Dletrec (compile_funs Empty (nsAppend env' env) (REVERSE funs)))
   | Dtype type_def =>
       (next, nsEmpty, Dtype mn type_def)
   | Dtabbrev tvs tn t =>
       (next, nsEmpty, Dtype mn [])
   | Dexn cn ts =>
       (next, nsEmpty, Dexn mn cn ts))`;

val compile_decs_def = Define`
  (compile_decs next mn env [] = (next, nsEmpty, [])) ∧
  (compile_decs next mn env (d::ds) =
   let (next1, new_env1, d') = compile_dec next mn env d in
   let (next2, new_env2, ds') =
     compile_decs next1 mn (nsAppend new_env1 env) ds
   in
     (next2, nsAppend new_env2 new_env1, d'::ds'))`;

val compile_top_def = Define `
  compile_top next env top =
   case top of
    | Tdec d =>
      let (next', new_env, d') = (compile_dec next [] env d) in
        (next', nsAppend new_env env, Prompt NONE [d'])
    | Tmod mn specs ds =>
      let (next', new_env, ds') = (compile_decs next [mn] env ds) in
        (next', nsAppend (nsLift mn new_env) env, Prompt (SOME mn) ds')`;

val compile_prog_def = Define `
  (compile_prog next env [] = (next, env, [])) ∧
  (compile_prog next env (p::ps) =
   let (next', env',p') = compile_top next env p in
   let (next'',env'',ps') = compile_prog next' env' ps in
     (next'',env'',(p'::ps')))`;

val _ = Datatype`
  config = <| next_global : num
            ; mod_env : (modN,varN,modLang$exp) namespace
            |>`;

val empty_config_def = Define`
  empty_config = <| next_global := 0; mod_env := nsEmpty |>`;

val compile_def = Define`
  compile c p =
    let (_,e,p') = compile_prog c.next_global c.mod_env p in
    (c with mod_env := e, p')`;

val _ = export_theory();
