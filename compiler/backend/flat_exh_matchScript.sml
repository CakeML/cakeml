(*
  This compiler phase ensures that all pattern matches are exhaustive.
*)
open preamble flatLangTheory backend_commonTheory

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

(* The map for datatype tags is arity |-> count. *)
val _ = Define `
  (get_dty_tags []      dtys = SOME dtys) ∧
  (get_dty_tags (p::ps) dtys =
     case p of
       Pcon (SOME (cid, SOME _)) pats =>
           if EVERY is_unconditional pats then
             let arity = LENGTH pats in
               (case lookup arity dtys of
                 SOME tags =>
                     get_dty_tags ps (insert arity (delete cid tags) dtys)
               | _ => NONE)
           else NONE
     | _ => NONE)`;

val _ = Define `
  exhaustive_match ctors ps ⇔
    EXISTS is_unconditional ps ∨
    case ps of
      Pcon (SOME (tag, SOME tyid)) pats :: _ =>
          EVERY is_unconditional pats  /\
          (case FLOOKUP ctors tyid of
            NONE      => F
          | SOME dtys =>
              let tags = map (\n. fromList (GENLIST (K ()) n)) dtys in
                (case get_dty_tags ps tags of
                  NONE     => F
                | SOME res => EVERY isEmpty (toList res)))
    | _ => F`

val add_default_def = Define `
  add_default t is_hdl is_exh ps =
    if is_exh then
      ps
    else if is_hdl then
      ps ++ [(Pvar "x", Raise (t § 1) (Var_local (t § 2) "x"))]
    else
      ps ++ [(Pany, Raise (t § 1) (Con (t § 2) (SOME (bind_tag, NONE)) []))]`;

val e2sz_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine"e2sz"`
  (e2sz (Raise _ e) = e2sz e + 1) ∧
  (e2sz (Letrec _ funs e) = e2sz e + f2sz funs + 1) ∧
  (e2sz (Mat _ e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (Handle _ e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (App _ op es) = l2sz es + 1) ∧
  (e2sz (Let _ x e1 e2) = e2sz e1 + e2sz e2 + 1) ∧
  (e2sz (If _ x1 x2 x3) = e2sz x1 + e2sz x2 + e2sz x3 + 1) /\
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
  (compile_exps ctors [If t x1 x2 x3] =
    let y1 = HD (compile_exps ctors [x1]) in
    let y2 = HD (compile_exps ctors [x2]) in
    let y3 = HD (compile_exps ctors [x3]) in
      [If t y1 y2 y3]) /\
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

Theorem compile_exps_LENGTH:
   !ctors xs. LENGTH (compile_exps ctors xs) = LENGTH xs
Proof
  ho_match_mp_tac (theorem "compile_exps_ind") \\ rw [compile_exps_def]
QED

Theorem compile_exps_SING[simp]:
   compile_exps ctors [x] <> []
Proof
  strip_tac \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [compile_exps_LENGTH]
QED

val compile_exp_def = Define `
  compile_exp ctors exp = HD (compile_exps ctors [exp])`;

val compile_dec_def = Define `
  (compile_dec ctors (Dlet exp) = (ctors, Dlet (compile_exp ctors exp))) /\
  (compile_dec ctors (Dtype tid amap) =
     (ctors |+ (tid, amap), Dtype tid amap)) /\
  (compile_dec ctors dec = (ctors, dec))`

val compile_decs_def = Define `
  (compile_decs ctors [] = (ctors, [])) /\
  (compile_decs ctors (d::ds) =
    let (ctor1, e)  = compile_dec  ctors d  in
    let (ctor2, es) = compile_decs ctor1 ds in
      (ctor2, e::es))`;

(* Only care about type declarations, not exceptions *)
val init_ctors_def = Define `
  init_ctors =
    FEMPTY |++
      [ (0 (* bool_id *), insert 0 2 LN)
      ; (1 (* list_id *), insert 0 1 (insert 2 1 LN)) ]`;

val compile_def = Define`
  compile = compile_decs init_ctors`;

val _ = export_theory()
