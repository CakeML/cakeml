open preamble flatLangTheory flat_reorder_matchTheory
open backend_commonTheory

val _ = numLib.prefer_num()

val _ = new_theory"flat_exh_match"

(*
(* The translation only detects the following patterns:
 *   - A single variable, (), or ref variable
 *   - A list of patterns, each of which is a constructor applied to variables.
 *)

val _ = tDefine"is_unconditional"`
  is_unconditional p ⇔
  case p of
  | conLang$Pvar _ => T
  | conLang$Pany => T
  | Pcon NONE ps => EVERY is_unconditional ps
  | Pref p => is_unconditional p
  | _ => F`
  (WF_REL_TAC`measure pat_size` >> gen_tac >>
   Induct_on`ps` >> simp[conLangTheory.pat_size_def] >>
   rw[] >> res_tac >> simp[conLangTheory.pat_size_def]);

val _ = Define `
  (get_tags [] acc = SOME acc)
  ∧
  (get_tags (p::ps) acc =
   case p of
   | Pcon (SOME (tag,_)) ps' =>
     if EVERY is_unconditional ps' then
       let a = (LENGTH ps') in
       (case lookup a acc of
        | SOME tags =>
            get_tags ps (insert a (delete tag tags) acc)
        | NONE => NONE)
     else NONE
   | _ => NONE)`;

val _ = Define `
  (exhaustive_match exh ps ⇔
   EXISTS is_unconditional ps ∨
   (case ps of
    | Pcon (SOME (tag,TypeStamp t)) ps'::_ =>
      EVERY is_unconditional ps' ∧
      (case FLOOKUP exh t of
       | NONE => F
       | SOME tags =>
         (case get_tags ps (map (λn. fromList (GENLIST (K ()) n)) tags) of
          | NONE => F
          | SOME result => EVERY isEmpty (toList result)))
    | _ => F))`;

val add_default_def = Define `
  (add_default tra is_handle is_exh (pes:(conLang$pat#conLang$exp)list) =
   if is_exh then
     pes
   else if is_handle then
     pes ++ [(Pvar "x", Raise (mk_cons tra 1) (Var_local (mk_cons tra 2) "x"))]
   else
     pes ++ [(Pany, Raise (mk_cons tra 1) (Con (mk_cons tra 2) (SOME (bind_tag, (TypeId (Short "option")))) []))])`;

val _ = tDefine"compile_pat"`
  (compile_pat (Pvar x) = Pvar x)
  ∧
  (compile_pat Pany = Pany)
  ∧
  (compile_pat (Plit l) = Plit l)
  ∧
  (compile_pat (Pcon NONE ps) =
   Pcon tuple_tag (MAP compile_pat ps))
  ∧
  (compile_pat (Pcon (SOME (tag,_)) ps) =
   Pcon tag (MAP compile_pat ps))
  ∧
  (compile_pat (Pref p) =
   Pref (compile_pat p))`
  (WF_REL_TAC `measure pat_size` >>
   srw_tac [ARITH_ss] [conLangTheory.pat_size_def] >>
   Induct_on `ps` >>
   srw_tac [ARITH_ss] [conLangTheory.pat_size_def] >>
   srw_tac [ARITH_ss] [conLangTheory.pat_size_def] >>
   res_tac >>
   decide_tac);

val e2sz_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine"e2sz"`
  (e2sz (conLang$Raise _ e) = e2sz e + 1) ∧
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

val p2sz_append = Q.prove(
  `∀p1 p2. p2sz (p1++p2) = p2sz p1 + p2sz p2`,
  Induct >> simp[e2sz_def] >>
  Cases >> simp[e2sz_def])

val compile_exp_def = tDefine"compile_exp"`
  (compile_exp exh (Raise t e) =
   Raise t (compile_exp exh e))
  ∧
  (compile_exp exh (Handle t e pes) =
   Handle t (compile_exp exh e)
     (compile_pes exh (add_default t T (exhaustive_match exh (MAP FST pes)) pes)))
  ∧
  (compile_exp exh (Lit t l) =
   Lit t l)
  ∧
  (compile_exp exh (Con t NONE es) =
   Con t tuple_tag (compile_exps exh es))
  ∧
  (compile_exp exh (Con t (SOME (tag,_)) es) =
   Con t tag (compile_exps exh es))
  ∧
  (compile_exp exh (Var_local t x) =
   Var_local t x)
  ∧
  (compile_exp exh (Var_global t x) =
   Var_global t x)
  ∧
  (compile_exp exh (Fun t x e) =
   Fun t x (compile_exp exh e))
  ∧
  (compile_exp exh (App t op es) =
   App t op (compile_exps exh es))
  ∧
  (compile_exp exh (Mat t e pes) =
   Mat t (compile_exp exh e)
     (compile_pes exh (add_default t F (exhaustive_match exh (MAP FST pes)) pes)))
  ∧
  (compile_exp exh (Let t x e1 e2) =
   Let t x (compile_exp exh e1) (compile_exp exh e2))
  ∧
  (compile_exp exh (Letrec t funs e) =
   Letrec t (compile_funs exh funs)
     (compile_exp exh e))
  ∧
  (compile_exp exh (Extend_global t n) =
   Extend_global t n)
  ∧
  (compile_exps exh [] = [])
  ∧
  (compile_exps exh (e::es) =
   compile_exp exh e :: compile_exps exh es)
  ∧
  (compile_pes exh [] = [])
  ∧
  (compile_pes exh ((p,e)::pes) =
   (compile_pat p, compile_exp exh e) :: compile_pes exh pes)
  ∧
  (compile_funs exh [] = [])
  ∧
  (compile_funs exh ((f,x,e)::funs) =
   (f,x,compile_exp exh e) :: compile_funs exh funs)`
  (WF_REL_TAC `inv_image $< (\x. case x of
     | INL (_,e) => e2sz e
     | INR (INL (_,es)) => l2sz es
     | INR (INR (INL (_,pes))) => p2sz pes
     | INR (INR (INR (_,funs))) => f2sz funs)` >>
   simp[e2sz_def] >>
   rw[add_default_def] >>
   simp[p2sz_append,e2sz_def])

val _ = map delete_const ["e2sz","p2sz","l2sz","f2sz","e2sz_UNION"]
val _ = delete_binding "e2sz_ind"

val compile_funs_map = Q.store_thm("compile_funs_map",
  `compile_funs exh ls = MAP (λ(x,y,z). (x,y,compile_exp exh z)) ls`,
  Induct_on`ls`>>simp[compile_exp_def]>>qx_gen_tac`p`>>PairCases_on`p`>>simp[compile_exp_def]);

val compile_exps_map = Q.store_thm ("compile_exps_map",
  `!exh es. compile_exps exh es = MAP (compile_exp exh) es`,
  Induct_on `es` >>
  rw [compile_exp_def]);

val compile_def = Define`
  compile exh e = HD (exh_reorder$compile [dec_to_exh$compile_exp exh e])`;
  *)
val _ = export_theory()
