(*
  This phase performs pattern-match compilation.
*)
open preamble flatLangTheory patLangTheory
open backend_commonTheory

val _ = new_theory"flat_to_pat"
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val Bool_def = Define `
  Bool t b = Con t (if b then true_tag else false_tag) []`;
val Bool_eqns = save_thm("Bool_eqns[simp]",
  [``Bool t T``,``Bool t F``]
  |> List.map (SIMP_CONV(std_ss)[Bool_def])
  |> LIST_CONJ)

val isBool_def = Define`
  isBool b e =
  dtcase e of Con _ t [] => (b ⇒ t = true_tag) ∧ (¬b ⇒ t = false_tag) | _ => F`;
val _ = export_rewrites["isBool_def"];

Theorem isBool_pmatch:
   isBool b e =
   case e of Con _ t [] => (b ⇒ t = true_tag) ∧ (¬b ⇒ t = false_tag) | _ => F
Proof
  CONV_TAC (RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) \\
  CASE_TAC \\ simp[]
QED

val sIf_def = Define `
  sIf tra e1 e2 e3 =
  if isBool T e2 ∧ isBool F e3
    then e1
  else
    (dtcase e1 of
     | Con _ t [] => if t = true_tag then e2 else e3
     | _ => If tra e1 e2 e3)`;

Theorem sIf_pmatch:
  !e1 e2 e3.
  sIf t e1 e2 e3 =
  if isBool T e2 ∧ isBool F e3
    then e1
  else
    (case e1 of
     | Con _ t [] => if t = true_tag then e2 else e3
     | _ => If t e1 e2 e3)
Proof
  rpt strip_tac
  >> every_case_tac
  >- fs[sIf_def]
  >- (CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >> fs[sIf_def])
QED

val _ = Define `
  pure_op_op op ⇔
    (op <> Opref) ∧
    (op <> Opapp) ∧
    (op <> Opassign) ∧
    (op <> Aw8update) ∧
    (op <> Aw8alloc) ∧
    (op <> Aw8sub) ∧
    (op <> Vsub) ∧
    (op <> Strsub) ∧
    (op <> CopyStrStr) ∧
    (op <> CopyStrAw8) ∧
    (op <> CopyAw8Str) ∧
    (op <> CopyAw8Aw8) ∧
    (op <> Chr) ∧
    (op <> Aupdate) ∧
    (op <> Aalloc) ∧
    (op <> Asub) ∧
    (op <> (Opn Divide)) ∧
    (op <> (Opn Modulo)) ∧
    (!n. op <> (GlobalVarAlloc n)) ∧
    (!n. op <> (GlobalVarInit n)) ∧
    (!n. op <> FFI n)`;

val _ = Define `
  (pure_op (Op op) ⇔ pure_op_op op)
  ∧
  (pure_op (Tag_eq _ _) ⇔ T)
  ∧
  (pure_op (El _) ⇔ T)
  ∧
  (pure_op _ ⇔ F)`;

val pure_def = Define `
  (pure (Raise _ _) ⇔ F)
  ∧
  (pure (Handle _ e1 _) ⇔ pure e1)
  ∧
  (pure (Lit _ _) ⇔ T)
  ∧
  (pure (Con _ _ es) ⇔ pure_list es)
  ∧
  (pure (Var_local _ _) ⇔ T)
  ∧
  (pure (Fun _ _) ⇔ T)
  ∧
  (pure (App _ op es) ⇔ pure_list es ∧ pure_op op)
  ∧
  (pure (If _ e1 e2 e3) ⇔ pure e1 ∧ pure e2 ∧ pure e3)
  ∧
  (pure (Let _ e1 e2) ⇔ pure e1 ∧ pure e2)
  ∧
  (pure (Seq _ e1 e2) ⇔ pure e1 ∧ pure e2)
  ∧
  (pure (Letrec _ _ e) ⇔ pure e)
  ∧
  (pure_list [] ⇔ T)
  ∧
  (pure_list (e::es) ⇔ pure e ∧ pure_list es)`;

Theorem pure_list_EVERY:
   ∀ls. pure_list ls ⇔ EVERY pure ls
Proof
  Induct >> simp[pure_def]
QED
val _ = export_rewrites["pure_list_EVERY"]

val ground_def = Define `
  (ground n (Raise _ e) ⇔ ground n e)
  ∧
  (ground n (Handle _ e1 e2) ⇔ ground n e1 ∧ ground (n+1) e2)
  ∧
  (ground _ (Lit _ _) ⇔ T)
  ∧
  (ground n (Con _ _ es) ⇔ ground_list n es)
  ∧
  (ground n (Var_local _ k) ⇔ k < n)
  ∧
  (ground _ (Fun _ _) ⇔ F)
  ∧
  (ground n (App _ _ es) ⇔ ground_list n es)
  ∧
  (ground n (If _ e1 e2 e3) ⇔ ground n e1 ∧ ground n e2 ∧ ground n e3)
  ∧
  (ground n (Let _ e1 e2) ⇔ ground n e1 ∧ ground (n+1) e2)
  ∧
  (ground n (Seq _ e1 e2) ⇔ ground n e1 ∧ ground n e2)
  ∧
  (ground _ (Letrec _ _ _) ⇔ F)
  ∧
  (ground_list _ [] ⇔ T)
  ∧
  (ground_list n (e::es) ⇔ ground n e ∧ ground_list n es)`;

val _ = export_rewrites["pure_op_op_def","pure_op_def","pure_def","ground_def"];

Theorem ground_list_EVERY:
   ∀n ls. ground_list n ls ⇔ EVERY (ground n) ls
Proof
  gen_tac >> Induct >> simp[]
QED
val _ = export_rewrites["ground_list_EVERY"]

Theorem pure_op_op_eqn:
    pure_op_op op =
  dtcase op of
    Opref => F
  | Opapp => F
  | Opassign => F
  | Aw8update => F
  | Aw8alloc => F
  | Aw8sub => F
  | Vsub => F
  | Strsub => F
  | CopyStrStr => F
  | CopyStrAw8 => F
  | CopyAw8Str => F
  | CopyAw8Aw8 => F
  | Chr => F
  | Aupdate => F
  | Aalloc => F
  | Asub => F
  | Opn Divide => F
  | Opn Modulo => F
  | GlobalVarAlloc _ => F
  | GlobalVarInit _ => F
  | FFI _ => F
  | _ => T
Proof
  Cases_on`op`>>fs[]>>
  Cases_on`o'`>>fs[]
QED

Theorem pure_op_op_pmatch:
    pure_op_op op =
  case op of
    Opref => F
  | Opapp => F
  | Opassign => F
  | Aw8update => F
  | Aw8alloc => F
  | Aw8sub => F
  | Vsub => F
  | Strsub => F
  | CopyStrStr => F
  | CopyStrAw8 => F
  | CopyAw8Str => F
  | CopyAw8Aw8 => F
  | Chr => F
  | Aupdate => F
  | Aalloc => F
  | Asub => F
  | Opn Divide => F
  | Opn Modulo => F
  | GlobalVarAlloc _ => F
  | GlobalVarInit _ => F
  | FFI _ => F
  | _ => T
Proof
  PURE_ONCE_REWRITE_TAC [pure_op_op_eqn]
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> REFL_TAC
QED

val sLet_def = Define `
  sLet t e1 e2 =
  dtcase e2 of
     | Var_local _ 0 => e1
     | _ =>
         if ground 0 e2 then
           if pure e1 then e2
           else Seq t e1 e2
         else Let t e1 e2`;

Theorem sLet_pmatch:
   sLet t e1 e2 =
   case e2 of
     | Var_local _ 0 => e1
     | _ =>
         if ground 0 e2 then
           if pure e1 then e2
           else Seq t e1 e2
         else Let t e1 e2
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) \\
  CASE_TAC \\ rw[sLet_def]
QED

(* bind elements 0..k of the variable n in reverse order above e (first element
 * becomes most recently bound) *)
val _ = Define`
  (Let_Els _ _ 0 e = e)
  ∧
  (Let_Els t n k e =
   sLet (mk_cons t 1) (App (mk_cons t 2) (El (k-1)) [Var_local (mk_cons t 3) n])
     (Let_Els (mk_cons t 4) (n+1) (k-1) e))`;

(* return an expression that evaluates to whether the pattern matches the most
 * recently bound variable *)
val _ = tDefine"compile_pat"`
  (compile_pat t (Pvar _) =
   Bool t T)
  ∧
  (compile_pat t Pany =
   Bool t T)
  ∧
  (compile_pat t (Plit l) =
   App (mk_cons t 1) (Op Equality) [Var_local (mk_cons t 2) 0; Lit (mk_cons t 3) l])
  ∧
  (compile_pat t (Pcon NONE _) =
   Bool t F) (* should not happen *)
  ∧
  (compile_pat t (Pcon (SOME (tag,_)) []) =
   App (mk_cons t 1) (Tag_eq tag 0) [Var_local (mk_cons t 2) 0])
  ∧
  (compile_pat t (Pcon (SOME (tag,_)) ps) =
   sIf (mk_cons t 1) (App (mk_cons t 2) (Tag_eq tag (LENGTH ps)) [Var_local (mk_cons t 3) 0])
     (Let_Els (mk_cons t 4) 0 (LENGTH ps) (compile_pats (mk_cons t 5) 0 ps))
     (Bool (mk_cons t 6) F))
  ∧
  (compile_pat t (Pref p) =
   sLet (mk_cons t 1) (App (mk_cons t 2) (Op Opderef) [Var_local (mk_cons t 3) 0])
     (compile_pat (mk_cons t 4) p))
  ∧
(* return an expression that evaluates to whether all the m patterns match the
 * m most recently bound variables; n counts 0..m *)
  (compile_pats t _ [] = Bool t T)
  ∧
  (compile_pats t n (p::ps) =
   sIf (mk_cons t 1) (sLet (mk_cons t 2) (Var_local (mk_cons t 3) n)
   (compile_pat (mk_cons t 4) p)) (compile_pats (mk_cons t 5) (n+1) ps) (Bool (mk_cons t 6) F))`
  (WF_REL_TAC `inv_image $< (\x. dtcase x of INL (_,p) => pat_size p
                                           | INR (_,n,ps) => pat1_size ps)`);

(* given a pattern in a context of bound variables where the most recently
 * bound variable is the value to be matched, return a function that binds new
 * variables (including all the pattern variables) over an expression and the
 * new context of bound variables for the expression as well as the number of
 * newly bound variables *)
val _ = tDefine"compile_row"`
  (compile_row _ (NONE::bvs) (Pvar x) = ((SOME x::bvs), 0, I))
  ∧
  (compile_row _ bvs Pany = (bvs, 0, I))
  ∧
  (compile_row _ bvs (Plit _) = (bvs, 0, I))
  ∧
  (compile_row t bvs (Pcon _ ps) = compile_cols t bvs 0 0 ps)
  ∧
  (compile_row t bvs (Pref p) =
   let (bvs,m,f) = (compile_row (mk_cons t 1) (NONE::bvs) p) in
   (bvs,(1+m), (λe. sLet (mk_cons t 2) (App (mk_cons t 3) (Op Opderef) [Var_local (mk_cons t 4) 0]) (f e)))) ∧
  (compile_row _ bvs _ = (bvs, 0, I)) (* should not happen *)
  ∧
  (compile_cols _ bvs _ _ [] = (bvs, 0, I))
  ∧
  (compile_cols t bvs n k (p::ps) =
   let (bvs,m,f) = compile_row (mk_cons t 1) (NONE::bvs) p in
   let (bvs,ms,fs) = compile_cols (mk_cons t 2) bvs ((n+1)+m) (k+1) ps in
   (bvs,(1+m)+ms,
    (λe. sLet (mk_cons t 3) (App (mk_cons t 4) (El k) [Var_local (mk_cons t 5) n]) (f (fs e)))))`
  (WF_REL_TAC `inv_image $< (\x. dtcase x of INL (_,bvs,p) => pat_size p
                                           | INR (_,bvs,n,k,ps) => pat1_size ps)`);

(* translate under a context of bound variables *)
(* compile_pes assumes the value being matched is most recently bound *)
val compile_exp_def = tDefine"compile_exp" `
  (compile_exp bvs (Raise t e) = Raise t (compile_exp bvs e))
  ∧
  (compile_exp bvs (Handle t e1 pes) =
   Handle (mk_cons t 1) (compile_exp bvs e1) (compile_pes (mk_cons t 2) (NONE::bvs) pes))
  ∧
  (compile_exp _ (Lit t l) = Lit t l)
  ∧
  (compile_exp bvs (If t e1 e2 e3) =
   sIf t (compile_exp bvs e1) (compile_exp bvs e2) (compile_exp bvs e3))
  ∧
  (compile_exp bvs (Con t NONE _) = Lit t (IntLit 0) (* should not happen *))
  ∧
  (compile_exp bvs (Con t (SOME (tag,_)) es) = Con t tag (compile_exps bvs es))
  ∧
  (compile_exp bvs (Var_local t x) =
   (dtcase find_index (SOME x) bvs 0 of
    | SOME k => Var_local t k
    | NONE => Lit t (IntLit 0) (* should not happen *)))
  ∧
  (compile_exp bvs (Fun t x e) = Fun t (compile_exp (SOME x::bvs) e))
  ∧
  (compile_exp bvs (App t op es) = App t (Op op) (compile_exps bvs es))
  ∧
  (compile_exp bvs (Mat t e pes) =
   sLet (mk_cons t 1) (compile_exp bvs e) (compile_pes (mk_cons t 2) (NONE::bvs) pes))
  ∧
  (compile_exp bvs (Let t (SOME x) e1 e2) =
   sLet t (compile_exp bvs e1) (compile_exp (SOME x::bvs) e2))
  ∧
  (compile_exp bvs (Let t NONE e1 e2) =
   Seq t (compile_exp bvs e1) (compile_exp bvs e2))
  ∧
  (compile_exp bvs (Letrec t funs e) =
   let bvs = (MAP (SOME o FST) funs) ++ bvs in
   Letrec t (compile_funs bvs funs) (compile_exp bvs e))
  ∧
  (compile_exps _ [] = [])
  ∧
  (compile_exps bvs (e::es) =
   compile_exp bvs e :: compile_exps bvs es)
  ∧
  (compile_funs _ [] = [])
  ∧
  (compile_funs bvs ((_,x,e)::funs) =
   compile_exp (SOME x::bvs) e :: compile_funs bvs funs)
  ∧
  (compile_pes tra bvs [(p,e)] =
   (dtcase compile_row tra bvs p of (bvs,_,f) => f (compile_exp bvs e)))
  ∧
  (compile_pes tra bvs ((p,e)::pes) =
   sIf (mk_cons tra 1) (compile_pat (mk_cons tra 2) p)
     (dtcase compile_row (mk_cons tra 3) bvs p of (bvs,_,f) => f (compile_exp bvs e) )
     (compile_pes (mk_cons tra 4) bvs pes))
  ∧
  (compile_pes t _ _ = Lit t (IntLit 0))`
  (WF_REL_TAC `inv_image $< (\x. dtcase x of INL (bvs,e) => exp_size e
                                         | INR (INL (bvs,es)) => exp6_size es
                                         | INR (INR (INL (bvs,funs))) => exp1_size funs
                                         | INR (INR (INR (_,bvs,pes))) =>
                                             exp3_size pes)`);
val _ = export_rewrites["compile_exp_def"];

val compile_def = Define`
  compile [] = [] ∧
  compile ((Dlet exp)::decs) =
    compile_exp [] exp :: compile decs ∧
  compile (_::decs) = compile decs`;

Theorem compile_funs_map:
   ∀funs bvs. compile_funs bvs funs = MAP (λ(f,x,e). compile_exp (SOME x::bvs) e) funs
Proof
  Induct>>simp[pairTheory.FORALL_PROD]
QED

Theorem compile_exps_map:
   ∀es. compile_exps a es = MAP (compile_exp a) es
Proof
  Induct >> simp[compile_exp_def]
QED

Theorem compile_exps_reverse:
   compile_exps a (REVERSE ls) = REVERSE (compile_exps a ls)
Proof
  rw[compile_exps_map,rich_listTheory.MAP_REVERSE]
QED

val _ = export_theory()
