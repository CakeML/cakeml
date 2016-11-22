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
 Bool b = (App (Opb (if b then Leq else Lt)) [Lit (IntLit 0); Lit (IntLit 0)])`;

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
  (compile_exp env (Raise e) =
    Raise (compile_exp env e))
  ∧
  (compile_exp env (Handle e pes) =
    Handle (compile_exp env e) (compile_pes env pes))
  ∧
  (compile_exp env (ast$Lit l) = modLang$Lit l)
  ∧
  (compile_exp env (Con cn es) = Con cn (compile_exps env es))
  ∧
  (compile_exp env (Var x) =
    case nsLookup env x of
    | NONE => Var_local "" (* Can't happen *)
    | SOME x => x)
  ∧
  (compile_exp env (Fun x e) =
    Fun x (compile_exp (nsBind x (Var_local x) env) e))
  ∧
  (compile_exp env (App op es) =
    App op (compile_exps env es))
  ∧
  (compile_exp env (Log lop e1 e2) =
    case lop of
    | And =>
      If (compile_exp env e1)
         (compile_exp env e2)
         (Bool F)
    | Or =>
      If (compile_exp env e1)
         (Bool T)
         (compile_exp env e2))
  ∧
  (compile_exp env (If e1 e2 e3) =
    If (compile_exp env e1)
       (compile_exp env e2)
       (compile_exp env e3))
  ∧
  (compile_exp env (Mat e pes) =
    Mat (compile_exp env e) (compile_pes env pes))
  ∧
  (compile_exp env (Let (SOME x) e1 e2) =
    Let (SOME x) (compile_exp env e1) (compile_exp (nsBind x (Var_local x) env) e2))
  ∧
  (compile_exp env (Let NONE e1 e2) =
    Let NONE (compile_exp env e1) (compile_exp env e2))
  ∧
  (compile_exp env (Letrec funs e) =
    let fun_names = MAP FST funs in
    let new_env = nsBindList (MAP (\x. (x, Var_local x)) fun_names) env in
      Letrec (compile_funs new_env funs) (compile_exp new_env e))
  ∧
  (compile_exp env (Tannot e t) = compile_exp env e)
  ∧
  (compile_exps env [] = [])
  ∧
  (compile_exps env (e::es) =
     compile_exp env e :: compile_exps env es)
  ∧
  (compile_pes env [] = [])
  ∧
  (compile_pes env ((p,e)::pes) =
    (compile_pat p, compile_exp (nsBindList (MAP (\x. (x, Var_local x)) (pat_bindings p [])) env) e)
    :: compile_pes env pes)
  ∧
  (compile_funs env [] = [])
  ∧
  (compile_funs env ((f,x,e)::funs) =
    (f,x,compile_exp (nsBind x (Var_local x) env) e) :: compile_funs env funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (x,e) => exp_size e
                                        | INR (INL (x,es)) => exps_size es
                                        | INR (INR (INL (x,pes))) => pes_size pes
                                        | INR (INR (INR (x,funs))) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);

val compile_exps_append = Q.store_thm("compile_exps_append",
  `!env es es'.
    compile_exps env (es ++ es') =
    compile_exps env es ++ compile_exps env es'`,
  Induct_on `es` >>
  fs [compile_exp_def]);

val compile_exps_reverse = Q.store_thm("compile_exps_reverse",
  `!env es.
    compile_exps env (REVERSE es) = REVERSE (compile_exps env es)`,
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]);

val compile_funs_map = Q.store_thm("compile_funs_map",
  `!env funs.
    compile_funs env funs = MAP (\(f,x,e). (f,x,compile_exp (nsBind x (Var_local x) env) e)) funs`,
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]);

val compile_funs_dom = Q.store_thm("compile_funs_dom",
  `!funs.
    (MAP (λ(x,y,z). x) funs)
    =
    (MAP (λ(x,y,z). x) (compile_funs env funs))`,
   induct_on `funs` >>
   rw [compile_exp_def] >>
   PairCases_on `h` >>
   rw [compile_exp_def]);

val alloc_defs_def = Define `
  (alloc_defs next [] = []) ∧
  (alloc_defs next (x::xs) =
    (x,next) :: alloc_defs (next + 1) xs)`;

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
       let e' = compile_exp env e in
       let xs = REVERSE (pat_bindings p []) in
       let l = LENGTH xs in
         (next + l,
          alloc_defs next xs,
          Dlet l (Mat e' [(compile_pat p, Con NONE (MAP Var_local xs))]))
   | Dletrec funs =>
       let fun_names = REVERSE (MAP FST funs) in
       let env' = alloc_defs next fun_names in
         (next + LENGTH fun_names,
          env',
          Dletrec (compile_funs (FOLDL (λenv (k,v). nsBind k (Var_global v) env) env env') (REVERSE funs)))
   | Dtype type_def =>
       (next, [], Dtype mn type_def)
   | Dtabbrev tvs tn t =>
       (next, [], Dtype mn [])
   | Dexn cn ts =>
       (next, [], Dexn mn cn ts))`;

val compile_decs_def = Define`
  (compile_decs next mn env [] = (next, [], [])) ∧
  (compile_decs next mn env (d::ds) =
   let (next1, new_env1, d') = compile_dec next mn env d in
   let (next2, new_env2, ds') =
     compile_decs next1 mn (FOLDL (λenv (k,v). nsBind k (Var_global v) env) env new_env1) ds
   in
     (next2, (new_env1 ++ new_env2), (d'::ds')))`;

val compile_top_def = Define `
  compile_top next env top =
   case top of
    | Tdec d =>
      let (next', new_env, d') = (compile_dec next [] env d) in
        (next', FOLDL (λenv (k,v). nsBind k (Var_global v) env) env new_env, Prompt [d'])
    | Tmod mn specs ds =>
      let (next', new_env, ds') = (compile_decs next [mn] env ds) in
        (next', nsAppend (nsLift mn (FOLDL (λenv (k,v). nsBind k (Var_global v) env) nsEmpty new_env)) env, Prompt ds')`;

val compile_prog_def = Define `
  (compile_prog next env [] = (next, env, [])) ∧
  (compile_prog next env (p::ps) =
   let (next', env',p') = compile_top next env p in
   let (next'',env'',ps') = compile_prog next' env' ps in
     (next'',env'',(p'::ps')))`;

val _ = Datatype`
  config = <| next_global : num
            ; mod_env : (modN,varN,exp) namespace
            |>`;

val empty_config_def = Define`
  empty_config = <| next_global := 0; mod_env := nsEmpty |>`;

val compile_def = Define`
  compile c p =
    let (_,e,p') = compile_prog c.next_global c.mod_env p in
    (c with mod_env := e, p')`;

val _ = export_theory();
