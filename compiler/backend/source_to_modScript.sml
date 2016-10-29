open preamble astTheory terminationTheory modLangTheory

val _ = numLib.prefer_num()

val _ = new_theory"source_to_mod"

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
  (compile_exp menv env (Raise e) =
    Raise (compile_exp menv env e))
  ∧
  (compile_exp menv env (Handle e pes) =
    Handle (compile_exp menv env e) (compile_pes menv env pes))
  ∧
  (compile_exp menv env (ast$Lit l) = modLang$Lit l)
  ∧
  (compile_exp menv env (Con cn es) = Con cn (compile_exps menv env es))
  ∧
  (compile_exp menv env (Var (Short x)) =
    case FLOOKUP env x of
     | NONE => Var_local x
     | SOME n => Var_global n)
  ∧
  (compile_exp menv env (Var (Long mn x)) =
    case FLOOKUP menv mn of
    | NONE => Var_global 0 (* Can't happen *)
    | SOME env' =>
      (case FLOOKUP env' x of
       | NONE => Var_global 0 (* Can't happen *)
       | SOME n => Var_global n))
  ∧
  (compile_exp menv env (Fun x e) =
    Fun x (compile_exp menv (env \\ x) e))
  ∧
  (compile_exp menv env (App op es) =
    App op (compile_exps menv env es))
  ∧
  (compile_exp menv env (Log lop e1 e2) =
    case lop of
    | And =>
      If (compile_exp menv env e1)
         (compile_exp menv env e2)
         (Bool F)
    | Or =>
      If (compile_exp menv env e1)
         (Bool T)
         (compile_exp menv env e2))
  ∧
  (compile_exp menv env (If e1 e2 e3) =
    If (compile_exp menv env e1)
       (compile_exp menv env e2)
       (compile_exp menv env e3))
  ∧
  (compile_exp menv env (Mat e pes) =
    Mat (compile_exp menv env e) (compile_pes menv env pes))
  ∧
  (compile_exp menv env (Let (SOME x) e1 e2) =
    Let (SOME x) (compile_exp menv env e1) (compile_exp menv (env \\ x) e2))
  ∧
  (compile_exp menv env (Let NONE e1 e2) =
    Let NONE (compile_exp menv env e1) (compile_exp menv env e2))
  ∧
  (compile_exp menv env (Letrec funs e) =
    let fun_names = MAP FST funs in
      Letrec (compile_funs menv (FOLDR (λk m. m \\ k) env fun_names) funs)
             (compile_exp menv (FOLDR (λk m. m \\ k) env fun_names) e))
  ∧
  (compile_exp menv env (Tannot e t) = compile_exp menv env e)
  ∧
  (compile_exps menv env [] = [])
  ∧
  (compile_exps menv env (e::es) =
     compile_exp menv env e :: compile_exps menv env es)
  ∧
  (compile_pes menv env [] = [])
  ∧
  (compile_pes menv env ((p,e)::pes) =
    (compile_pat p, compile_exp menv (FOLDR (λk m. m \\ k) env (pat_bindings p [])) e)
    :: compile_pes menv env pes)
  ∧
  (compile_funs menv env [] = [])
  ∧
  (compile_funs menv env ((f,x,e)::funs) =
    (f,x,compile_exp menv (env \\ x) e) :: compile_funs menv env funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);

val compile_exps_append = Q.store_thm("compile_exps_append",
  `!mods tops es es'.
    compile_exps mods tops (es ++ es') =
    compile_exps mods tops es ++ compile_exps mods tops es'`,
  Induct_on `es` >>
  fs [compile_exp_def]);

val compile_exps_reverse = Q.store_thm("compile_exps_reverse",
  `!mods tops es.
    compile_exps mods tops (REVERSE es) = REVERSE (compile_exps mods tops es)`,
  Induct_on `es` >>
  rw [compile_exp_def, compile_exps_append]);

val compile_funs_map = Q.store_thm("compile_funs_map",
  `!mods tops funs.
    compile_funs mods tops funs = MAP (\(f,x,e). (f,x,compile_exp mods (tops\\x) e)) funs`,
  induct_on `funs` >>
  rw [compile_exp_def] >>
  PairCases_on `h` >>
  rw [compile_exp_def]);

val compile_funs_dom = Q.store_thm("compile_funs_dom",
  `!funs.
    (MAP (λ(x,y,z). x) funs)
    =
    (MAP (λ(x,y,z). x) (compile_funs mods tops funs))`,
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
 (compile_dec next mn menv env d =
  case d of
   | Dlet p e =>
       let e' = compile_exp menv env e in
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
          Dletrec (compile_funs menv (FOLDL (λenv (k,v). env |+ (k, v)) env env') (REVERSE funs)))
   | Dtype type_def =>
       (next, [], Dtype mn type_def)
   | Dtabbrev tvs tn t =>
       (next, [], Dtype mn [])
   | Dexn cn ts =>
       (next, [], Dexn mn cn ts))`;

val compile_decs_def = Define`
  (compile_decs next mn menv env [] = (next, [], [])) ∧
  (compile_decs next mn menv env (d::ds) =
   let (next1, new_env1, d') = compile_dec next mn menv env d in
   let (next2, new_env2, ds') =
     compile_decs next1 mn menv (FOLDL (λenv (k,v). env |+ (k, v)) env new_env1) ds
   in
     (next2, (new_env1 ++ new_env2), (d'::ds')))`;

val compile_top_def = Define `
  (compile_top next menv env top =
   case top of
    | Tdec d =>
      let (next', new_env, d') = (compile_dec next NONE menv env d) in
        (next', menv, FOLDL (λenv (k,v). env |+ (k, v)) env new_env, Prompt NONE [d'])
    | Tmod mn specs ds =>
      let (next', new_env, ds') = (compile_decs next (SOME mn) menv env ds) in
        (next',menv |+ (mn, (FOLDL (λenv (k,v). env |+ (k, v)) FEMPTY new_env)), env, Prompt (SOME mn) ds'))`;

val compile_prog_def = Define `
  (compile_prog next menv env [] = (next, menv, env, [])) ∧
  (compile_prog next menv env (p::ps) =
   let (next', menv', env',p') = compile_top next menv env p in
   let (next'', menv'', env'',ps') = compile_prog next' menv' env' ps in
     (next'',menv'',env'',(p'::ps')))`;

val _ = Datatype`
  config = <| next_global : num
            ; mod_env : (string,num) mod_env
            |>`;

val empty_config_def = Define`
  empty_config = <| next_global := 0; mod_env := (FEMPTY,FEMPTY) |>`;

val compile_def = Define`
  compile c p =
    let (menv,env) = c.mod_env in
    let (_,m,e,p') = compile_prog c.next_global menv env p in
    (c with mod_env := (m,e), p')`;

val _ = export_theory()
