open HolKernel boolLib bossLib lcsymtacs listTheory sholSyntaxTheory modelSetTheory
val _ = numLib.prefer_num()
val _ = new_theory"sholSemantics"

val _ = Parse.add_infix("=++",320,Parse.NONASSOC)

val UPDATE_LIST_def = xDefine"UPDATE_LIST"`
  (([] =++ ys) = I) ∧
  ((xs =++ []) = I) ∧
  (((x::xs) =++ (y::ys)) = (x =+ y) o (xs =++ ys) )`

val term_allsize_def = tDefine"term_allsize"`
  term_allsize (Var n ty) = 1 + type_allsize ty ∧
  term_allsize (Const n ty Prim) = 1 + type_allsize ty ∧
  term_allsize (Const n ty (Defined r)) = 1 + type_allsize ty + term_allsize r ∧
  term_allsize (Const n ty (Tyabs op p)) = 1 + type_allsize ty + term_allsize p ∧
  term_allsize (Const n ty (Tyrep op p)) = 1 + type_allsize ty + term_allsize p ∧
  term_allsize (Comb t1 t2) = 1 + term_allsize t1 + term_allsize t2 ∧
  term_allsize (Abs n ty t) = 1 + type_allsize ty + term_allsize t ∧
  type_allsize (Tyvar s) = 1 ∧
  type_allsize (Tyapp (Typrim n a) ts) = 1 + list_size type_allsize ts ∧
  type_allsize (Tyapp (Tydefined n p) ts) = 1 + term_allsize p + list_size type_allsize ts`
(WF_REL_TAC`inv_image (<) (λx. case x of INR ty => type_size ty | INL tm => term_size tm)` >>
 simp[] >> conj_tac >> Induct_on `ts` >> simp[term_size_def] >>
 rw[] >> simp[] >>
 TRY(first_x_assum(qspecl_then[`a`,`n`,`a'`]mp_tac)>>simp[])>>
 first_x_assum(qspecl_then[`p`,`n`,`a`]mp_tac)>>simp[])

val semantics_def = tDefine "semantics"`
  (typeset σ τ (Tyvar s) = τ s) ∧
  (typeset σ τ (Tyapp (Typrim n a) ts) =
    case (n,a,ts) of
    | ("bool",0,[]) => boolset
    | ("->",2,[x;y]) => funspace (typeset σ τ x) (typeset σ τ y)
    (* ind and unknown primitive type operators interpreted as ind *)
    | _ => indset) ∧
  (typeset σ τ (Tyapp (Tydefined n p) ts) =
    if LENGTH ts = LENGTH (tvars p) then
      let τ' = (tvars p =++ (MAP (typeset σ τ) ts)) τ in
    (typeset σ τ' (domain(typeof p)) suchthat holds (semantics σ τ' p))
    (* bad type application interpreted as ind *)
    else indset) ∧

  (semantics σ τ (Var n ty) = σ(n,ty)) ∧
  (semantics σ τ (Const n ty Prim) =
    if n = "=" ∧ ∃a. ty = Fun a (Fun a Bool) then
      let a = domain ty in
        abstract (typeset σ τ a) (typeset σ τ (Fun a Bool))
          (λx. abstract (typeset σ τ a) (typeset σ τ Bool)
                        (λy. boolean (x = y)))
    else
    if n = "@" ∧ ∃a. ty = Fun (Fun a Bool) a then
      let a = codomain ty in
        abstract (typeset σ τ (Fun a Bool)) (typeset σ τ a)
                 (λp. let s = ((typeset σ τ a) suchthat (holds p)) in
                        ch (if ∃x. x <: s then s
                            else typeset σ τ a))
    (* unknown primitive constants interpreted as variables with the same name *)
    else σ(n,ty)) ∧
  (semantics σ τ (Const n ty (Defined r)) =
    semantics σ τ r) ∧
  (semantics σ τ (Const n ty (Tyabs op p)) =
    (* TODO *) ARB) ∧
  (semantics σ τ (Const n ty (Tyrep op p)) =
    (* TODO *) ARB) ∧
  (semantics σ τ (Comb s t) =
     apply (semantics σ τ s) (semantics σ τ t)) ∧
  (semantics σ τ (Abs n ty t) =
     abstract (typeset σ τ ty) (typeset σ τ (typeof t))
       (λx. semantics (((n,ty) =+ x) σ) τ t))`
(WF_REL_TAC`inv_image (<)
  (λx. case x of
       | INL (σ,τ,ty) => type_allsize ty
       | INR (σ,τ,tm) => term_allsize tm)` >>
  simp[term_allsize_def,list_size_def] >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  simp[term_allsize_def,list_size_def] >>
  cheat (* probably false... *))

val _ = export_theory()
