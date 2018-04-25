open preamble flatLangTheory flat_reorder_matchTheory backend_commonTheory

val _ = numLib.prefer_num()

val _ = new_theory"flat_exh_match"

val _ = tDefine "is_unconditional" `
  is_unconditional p ⇔
    case p of
      Pcon NONE ps => EVERY is_unconditional ps
    | Pvar _       => T
    | Pany         => T
    | Pref p       => is_unconditional p
    | _            => F`
  (WF_REL_TAC `measure pat_size` >> gen_tac >>
   Induct_on`ps` >> simp[pat_size_def] >>
   rw[] >> res_tac >> simp[pat_size_def]);

val _ = Define `
  (get_tags [] acc = SOME acc) ∧
  (get_tags (p::ps) acc =
     case p of
       Pcon (SOME (tag,t)) pats =>
           if EVERY is_unconditional pats then
             let a = LENGTH pats in
             (case lookup a acc of
                SOME tags => get_tags ps (insert a (delete tag tags) acc)
              | _ => NONE)
           else NONE
     | _ => NONE)`;

val _ = Define `
  exhaustive_match ctors ps ⇔
    EXISTS is_unconditional ps ∨
    case ps of
      Pcon (SOME (tag,t)) pats :: _ =>
        EVERY is_unconditional pats  /\
        (case FLOOKUP ctors t of
          NONE => F
        | SOME tags =>
            (case get_tags ps (map (\n. fromList (GENLIST (K ()) n)) tags) of
               NONE => F
             | SOME result => EVERY isEmpty (toList result)))
    | _ => F`

val add_default_def = Define `
  add_default tra is_handle is_exhaustive pes =
    if is_exhaustive then
      pes
    else if is_handle then
      pes ++
        [(Pvar "x",
          Raise (mk_cons tra 1) (Var_local (mk_cons tra 2) "x"))]
    else
      pes ++
        [(Pany,
          Raise (mk_cons tra 1) (Con (mk_cons tra 2)
            (SOME (bind_tag, NONE)) []))]`;

val e2sz_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine"e2sz"`
  (e2sz (Raise _ e) = e2sz e + 1) ∧
  (e2sz (Letrec _ funs e) = e2sz e + f2sz funs + 1) ∧
  (e2sz (Mat _ e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (Handle _ e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (App _ op es) = l2sz es + 1) ∧
  (e2sz (Let _ x e1 e2) = e2sz e1 + e2sz e2 + 1) ∧
  (e2sz (Fun _ x e) = e2sz e + 1) ∧
  (e2sz (Con _ t es) = l2sz es + 1) ∧
  (e2sz _ = (0:num)) ∧
  (l2sz [] = 0) ∧
  (l2sz (e::es) = e2sz e + l2sz es + 1) ∧
  (p2sz [] = 0) ∧
  (p2sz ((p,e)::pes) = e2sz e + p2sz pes + 1) ∧
  (f2sz [] = 0) ∧
  (f2sz ((f,x,e)::funs) = e2sz e + f2sz funs + 1)`)
  (WF_REL_TAC`inv_image $< (\x. case x of
    | INL (e) => exp_size e
    | INR (INL (es)) => exp6_size es
    | INR (INR (INL (pes))) => exp3_size pes
    | INR (INR (INR (funs))) => exp1_size funs)`)

val compile_exps_def = tDefine "compile_exps" `
  (compile_exps ctors [] = []) /\
  (compile_exps ctors (x::y::xs) =
    HD (compile_exps ctors [x]) :: compile_exps ctors (y::xs)) /\
  (compile_exps ctors [Raise t x] =
    let y = HD (compile_exps ctors [x]) in
      [Raise t y]) /\
  (compile_exps ctors [Handle t x ps] =
    let y   = HD (compile_exps ctors [x]) in
    let ps1 = add_default t T (exhaustive_match ctors (MAP FST ps)) ps in
    let ps2 = MAP (\(p,e). (p, HD (compile_exps ctors [e]))) ps1 in
      [Handle t y ps2]) /\
  (compile_exps ctors [Con t ts xs] = [Con t ts (compile_exps ctors xs)]) /\
  (compile_exps ctors [Fun t vs x] =
    let y = HD (compile_exps ctors [x]) in
      [Fun t vs y]) /\
  (compile_exps ctors [App t op xs] =
    let ys = compile_exps ctors xs in
      [App t op ys]) /\
  (compile_exps ctors [Mat t x ps] =
    let y   = HD (compile_exps ctors [x]) in
    let ps1 = add_default t F (exhaustive_match ctors (MAP FST ps)) ps in
    let ps2 = MAP (\(p,e). (p, HD (compile_exps ctors [e]))) ps1 in
      [Mat t y ps2]) /\
  (compile_exps ctors [Let t v x1 x2] =
    let y1 = HD (compile_exps ctors [x1]) in
    let y2 = HD (compile_exps ctors [x2]) in
      [Let t v y1 y2]) /\
  (compile_exps ctors [Letrec t fs x] =
    let fs1 = MAP (\(a,b,c). (a, b, HD (compile_exps ctors [c]))) fs in
    let y   = HD (compile_exps ctors [x]) in
      [Letrec t fs1 y]) /\
  (compile_exps ctors [expr] = [expr])`
  (WF_REL_TAC `measure (l2sz o SND)` \\ rw [add_default_def] \\ fs [e2sz_def]
  \\ pop_assum mp_tac
  \\ TRY (pop_assum kall_tac)
  >-
   (map_every qid_spec_tac [`a`,`b`,`c`,`fs`]
    \\ Induct \\ rw [] \\ fs [e2sz_def]
    \\ PairCases_on `h`
    \\ res_tac \\ fs [e2sz_def])
  \\ map_every qid_spec_tac [`p`,`e`,`ps`]
  \\ Induct \\ rw [] \\ fs [exp_size_def]
  \\ TRY (PairCases_on `h`)
  \\ res_tac \\ fs [e2sz_def]);

val _ = map delete_const ["e2sz","p2sz","l2sz","f2sz","e2sz_UNION"]
val _ = delete_binding "e2sz_ind"

val compile_exps_LENGTH = Q.store_thm("compile_exps_LENGTH",
  `!ctors xs. LENGTH (compile_exps ctors xs) = LENGTH xs`,
  ho_match_mp_tac (theorem "compile_exps_ind") \\ rw [compile_exps_def]);

val compile_exps_SING = Q.store_thm("compile_exps_SING[simp]",
  `compile_exps ctors [x] <> []`,
  strip_tac \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [compile_exps_LENGTH]);

val compile_exp_def = Define `
  compile_exp ctors exp = HD (compile_exps ctors [exp])`;

val compile_decs_def = Define `
  (compile_decs ctors []         = (ctors, [])) /\
  (compile_decs ctors (x::y::xs) =
     let (ctor1, z1) = compile_decs ctors [x] in
     let (ctor2, zs) = compile_decs ctor1 (y::xs) in
       (ctor2, z1++zs)) /\
  (compile_decs ctors [Dlet exp] =
    (ctors, [Dlet (compile_exp ctors exp)])) /\
  (compile_decs ctors [Dtype tid anum] =
    (ctors |+ (SOME tid, anum), [Dtype tid anum])) /\
  (compile_decs ctors [Dexn eid arity] =
    let ctor1 =
      case FLOOKUP ctors NONE of
        NONE      => ctors |+ (NONE, insert arity 1 LN)
      | SOME exns =>
          case lookup arity exns of
            NONE   => ctors |+ (NONE, insert arity 1 exns)
          | SOME n => ctors |+ (NONE, insert arity (n+1) exns) in
      (ctor1, [Dexn eid arity]))`

val compile_def = Define`
  compile = compile_decs FEMPTY`;

val _ = export_theory()

