(*
  Defines the HOL inference system extended with the little theories
  module system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory holSyntaxTheory errorMonadTheory

val _ = new_theory "littleTheoriesSyntax"

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

Datatype: ethy = <| tms: mlstring |-> type;
                    tys: mlstring |-> num;
                    axs: term set;
                    etms: mlstring |-> type;
                    etys: mlstring |-> num;
                    eaxs: term set |>
End

Definition ctys_def:
  ctys thy = thy.tys ⊌ thy.etys
End

val _ = add_record_field ("ctys", “ctys”)

Definition ctms_def:
  ctms thy = thy.tms ⊌ thy.etms
End

val _ = add_record_field ("ctms", “ctms”)

Definition sigof'_def:
  sigof' thy = (thy.tys, thy.tms)
End

val _ = add_record_field ("sig", “sigof'”)

(* Standard signature includes the minimal type operators and constants *)

(* term_ok' has to check if types are valid through both the
types and eliminable types *)
Definition term_ok'_def:
  (term_ok' thy' (Var x ty) ⇔ type_ok thy'.ctys ty) ∧
  (term_ok' thy' (Const name ty) ⇔
     ∃ty0. FLOOKUP thy'.ctms name = SOME ty0 ∧
           type_ok thy'.ctys ty ∧
           is_instance ty0 ty) ∧
  (term_ok' thy' (Comb tm1 tm2) ⇔
     term_ok' thy' tm1 ∧
     term_ok' thy' tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok' thy' (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok thy'.ctys ty ∧
       term_ok' thy' tm)
End

Definition theory_ok'_def:
  theory_ok' (thy:ethy) ⇔
    (∀ty. ty ∈ FRANGE thy.tms ⇒ type_ok thy.tys ty) ∧
    (∀ty. ty ∈ FRANGE thy.etms ⇒ type_ok thy.ctys ty) ∧
    DISJOINT (FDOM thy.tys) (FDOM thy.etys) ∧
    DISJOINT (FDOM thy.tms) (FDOM thy.etms) ∧
    (∀p. p ∈ thy.axs ⇒ term_ok thy.sig p ∧ p has_type Bool) ∧
    (∀p. p ∈ thy.eaxs ⇒
         term_ok' thy p ∧ p has_type Bool) ∧
    is_std_sig thy.sig
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-'",450,Parse.NONASSOC)

Definition ty_esubst_def:
  (ty_esubst _ (Tyvar n) = Tyvar n) ∧
  (ty_esubst σ (Tyapp n []) =
   case FLOOKUP (FST σ) n of
   | NONE => Tyapp n []
   | SOME ty => ty) ∧
  (ty_esubst σ (Tyapp n ts) = Tyapp n (MAP (ty_esubst σ) ts))
Termination
  WF_REL_TAC ‘measure (type_size o SND)’ >> rw[] >> simp[]
  >> rename [‘MEM ty tys’] >> Induct_on ‘tys’ >> simp[] >> rw[]
  >> gvs[type_size_def]
End

Definition try_def:
  try (return v) f = return v ∧
  try (error e) f = f e
End

Definition tm_names_def[simp]:
  tm_names (Var n _) = [n] ∧
  tm_names (Const _ _) = [] ∧
  tm_names (Comb t1 t2) = tm_names t1 ++ tm_names t2 ∧
  tm_names (Abs v body) = tm_names v ++ tm_names body (* should this include v *)
End

Definition nvar_aux:
  nvar_aux nms n = if MEM n nms
                   then nvar_aux nms (n ^ implode "'")
                   else n
Termination
  WF_REL_TAC ‘measure (λ(nms, n). LENGTH (FILTER (λe. strlen n <= strlen e) nms))’
  >> Induct_on ‘nms’ >> rw[] >> gvs[]
  >- (irule $ DECIDE “x ≤ y ⇒ x < SUC y” >> irule LENGTH_FILTER_LEQ_MONO
      >> simp[])
  >> ‘strlen n = strlen h’ by simp[] >> gvs[] >> first_x_assum drule >> simp[]
End

Definition NVARIANT:
  NVARIANT n tm = nvar_aux (tm_names tm) n
End

(* analog of INST_CORE *)
Definition esubst_ty0_def:
  (esubst_ty0 env σ (Var n ty) =
   let
     tm = Var n ty;
     tm' = Var n (ty_esubst σ ty)
   in if REV_ASSOCD tm' env tm = tm then
        return tm'
      else error tm') ∧
  (esubst_ty0 env σ (Const n ty) =
   return $ Const n (ty_esubst σ ty)) ∧
  (esubst_ty0 env σ (Comb t1 t2) =
   do
     t1' <- esubst_ty0 env σ t1;
     t2' <- esubst_ty0 env σ t2;
     return $ Comb t1' t2'
   od) ∧
  (esubst_ty0 env σ (Abs v body) =
   let
     (n, ty) = dest_var v;
     ty' = ty_esubst σ ty;
     v' = Var n ty'
   in try
      do
        body' <- esubst_ty0 ((v, v')::env) σ body;
        return $ Abs v' body'
      od
      (λbad_v.
         if bad_v ≠ v' then
           error bad_v
         else
           do
             body1 <- esubst_ty0 [] σ body;
             n' <<- NVARIANT n body1;
             body' <<- VSUBST [(Var n' ty, Var n ty)] body;
             env'' <<- (Var n' ty, Var n' ty')::env;
             body'' <- esubst_ty0 env'' σ body';
             return $ Abs (Var n' ty') body''
           od))
Termination
  WF_REL_TAC ‘measure (sizeof o SND o SND)’ >> simp[SIZEOF_VSUBST]
End

Definition esubst_ty_def:
  esubst_ty σ tm = case esubst_ty0 [] σ tm of
                   | return v => v
                   | error e => ARB (* see esubst_ty0_always_returns *)
End 

Definition esubst_tm_def:
  esubst_tm σ (Var n ty) = Var n ty ∧
  esubst_tm σ (Abs v t) = Abs v (esubst_tm σ t) ∧
  esubst_tm σ (Comb t1 t2) = Comb (esubst_tm σ t1) (esubst_tm σ t2) ∧
  esubst_tm σ (Const n ty) = case FLOOKUP (SND σ) n of
                             | NONE => Const n ty
                             | SOME tm => tm
End

Definition esubst_def:
  esubst σ tm = esubst_tm σ (esubst_ty σ tm)
End

Theorem REV_ASSOCD_NEQ_DEFAULT:
  REV_ASSOCD t2 σ d ≠ d ⇒
  ∃t1. MEM (t1, t2) σ ∧ t1 ≠ d
Proof
  Induct_on ‘σ’ >> rw[REV_ASSOCD_def] >> Cases_on ‘h’ >> gvs[]
  >> dsimp[] >> metis_tac[]
QED

Theorem try_eq_error:
  try m f = error e ⇔ ∃e1. m = error e1 ∧ f e1 = error e
Proof
  Cases_on ‘m’ >> rw[EQ_IMP_THM, try_def]
QED

Theorem try_eq_return:
  try m f = return v ⇔ m = return v ∨ ∃e. m = error e ∧ f e = return v
Proof
  Cases_on ‘m’ >> rw[EQ_IMP_THM, try_def]
QED

Theorem term_ok_rev_assocd:
  term_ok sig (REV_ASSOCD t1 env t2) ⇔
  (∃p t s. env = p ++ [(t, t1)] ++ s ∧ (∀e d. MEM (e, d) p ⇒ d ≠ t1)
           ∧ term_ok sig t)
  ∨ (∀e d. MEM (e, d) env ⇒ d ≠ t1) ∧ term_ok sig t2
Proof
  Induct_on ‘env’ >> rw[REV_ASSOCD_def]
  >> rename [‘h::env = _ ++ _ ++ _’] >> Cases_on ‘h’ >> gvs[]
  >- (iff_tac >> strip_tac
      >- (DISJ1_TAC >> qexists ‘[]’ >> simp[])
      >- (Cases_on ‘p’ >> gvs[])
      >- (metis_tac[]))
  >- (rw[EQ_IMP_THM] >> simp[FORALL_AND_THM]
      >- (qexistsl [‘(q,r)::p’] >> simp[])
      >- (Cases_on ‘p’ >> gvs[] >> metis_tac[]))
QED

Theorem has_type_var[simp] = hd (CONJUNCTS has_type_rules)
Theorem has_type_const[simp] = hd $ tl (CONJUNCTS has_type_rules)

Theorem term_ok_imp_welltyped:
  term_ok sig tm ⇒ welltyped tm
Proof
  Induct_on ‘tm’ >> rw[welltyped_def]
  >- (qexists ‘t’ >> rw[has_type_rules])
  >- (qexists ‘t’ >> rw[has_type_rules])
  >- (gvs[term_ok_def, welltyped_def] >> metis_tac[])
  >- (gvs[term_ok_def, welltyped_def] >> metis_tac[has_type_rules])
QED

Definition vsubst_tys_ok_def:
  vsubst_tys_ok ilist =
  (∀s s'. MEM (s',s) ilist ⇒
          ∃x ty. (s = Var x ty) ∧ s' has_type ty)
End

Theorem rev_assocd_neq_mem:
  REV_ASSOCD x l d ≠ d ⇒ MEM (REV_ASSOCD x l d, x) l
Proof
  metis_tac[REV_ASSOCD_MEM]
QED

Theorem neq_error:
  (∀e. x ≠ error e) ⇔ ∃v. x = return v
Proof
  Cases_on ‘x’ >> rw[]
QED

Theorem vsubst_has_type:
  ∀ilist. t has_type τ ∧ vsubst_tys_ok ilist ⇒ (VSUBST ilist t) has_type τ
Proof
  Induct_on ‘_ has_type _’ >> rw[]
  >> gvs[VSUBST_def]
  >- (gvs[vsubst_tys_ok_def]
      >> Cases_on ‘REV_ASSOCD (Var n τ) ilist (Var n τ) = Var n τ’
      >- rw[has_type_rules]
      >- (drule_then assume_tac rev_assocd_neq_mem
          >> first_x_assum drule >> rw[]))
  >- metis_tac[has_type_rules]
  >> rw[]
  >> (irule (last $ CONJUNCTS has_type_rules) >> first_x_assum irule
      >> gvs[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM,
             MEM_FILTER, has_type_rules])
QED

Theorem welltyped_comb_vsubst:
  welltyped (Comb x y) ∧ vsubst_tys_ok lst
  ⇒ welltyped (Comb (VSUBST lst x) (VSUBST lst y))
Proof
  rw[welltyped_def] >> drule_all vsubst_has_type >> rw[VSUBST_def]
  >> metis_tac[]
QED

Theorem vsubst_tys_ok_cons[simp]:
  vsubst_tys_ok (x::xs) ⇔
    vsubst_tys_ok xs ∧ ∃n ty s'. x = (s', Var n ty) ∧ s' has_type ty
Proof
  rw[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM, EQ_IMP_THM]
  >> Cases_on ‘x’ >> gvs[]
QED

Theorem vsubst_tys_ok_filter[simp]:
  vsubst_tys_ok lst ⇒ vsubst_tys_ok (FILTER P lst)
Proof
  rw[vsubst_tys_ok_def, MEM_FILTER]
QED

Theorem term_ok_vsubst:
  ∀x lst.
    EVERY (λp. term_ok sig (FST p)) lst ∧ term_ok sig x ∧ vsubst_tys_ok lst
    ⇒ term_ok sig (VSUBST lst x)
Proof
  Induct_on ‘x’ >> rw[VSUBST_def, term_ok_def, term_ok_rev_assocd, EVERY_MEM]
  >- (Cases_on ‘∀e. ¬MEM (e,Var m t) lst’ >> rw[]
      >> qabbrev_tac
         ‘i = LEAST j. j < LENGTH lst ∧ SND (EL j lst) = Var m t’
      >> qexists ‘TAKE i lst’ >> CONV_TAC SWAP_EXISTS_CONV
      >> qexists ‘DROP (i+1) lst’ >> simp[Abbr ‘i’]
      >> numLib.LEAST_ELIM_TAC >> CONJ_TAC
      >- (gvs[MEM_EL] >> metis_tac[SND])
      >- (rw[] >> qexists ‘FST (EL n lst)’
          >> reverse $ rw[]
          >- (metis_tac[MEM_EL])
          >- (rw[MEM_EL] >> strip_tac >> gvs[EL_TAKE]
              >> metis_tac[SND])
          >- (qspecl_then [‘n’, ‘lst’] assume_tac TAKE_DROP
              >> ‘[(FST (EL n lst),Var m t)] ++ DROP (n + 1) lst
                  = DROP n lst’
                suffices_by simp[GSYM APPEND_ASSOC,
                                 Excl "APPEND_ASSOC"]
              >> simp[DROP_BY_DROP_SUC, ADD1]
              >> metis_tac[PAIR])))
  >- (gvs[GSYM EVERY_MEM] >> rpt $ first_x_assum drule >> rw[]
      >> gvs[term_ok_def] >> dxrule term_ok_imp_welltyped
         >> dxrule term_ok_imp_welltyped >> rw[welltyped_comb_vsubst])
  >- (rw[term_ok_def] >> first_x_assum irule >> rw[]
      >- rw[term_ok_def]
      >> gvs[EVERY_MEM, MEM_FILTER])
  >> first_x_assum irule >> rw[EVERY_MEM, MEM_FILTER]
QED

Theorem vsubst_tys_ok_nil[simp]:
  vsubst_tys_ok []
Proof
  rw[vsubst_tys_ok_def]
QED

Theorem NVSUBST_nil[simp]:
  ∀tm. VSUBST [] tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, REV_ASSOCD_def]
QED

Theorem term_ok_vsubst_variant:
  ∀tm x1 x2 ty.
       term_ok sig tm
       ∧ type_ok (tysof sig) ty
       ⇒ term_ok sig (VSUBST [(Var x1 ty,
                               Var x2 ty)] tm)
Proof
  Induct_on ‘tm’
  >> rw[esubst_ty0_def, REV_ASSOCD_def, VSUBST_def, term_ok_def]
  >> rw[welltyped_comb_vsubst, term_ok_def, NVSUBST_nil]
  >> (irule term_ok_vsubst >> rw[vsubst_tys_ok_def, term_ok_def])
QED

Theorem term_var_ok:
  ∀n sig ty. type_ok (tysof sig) ty ⇒ term_ok sig (Var n ty)
Proof
  rw[term_ok_def]
QED

Theorem bind_return_comb:
  ∀a b q. (do
            a' <- a;
            b' <- b;
            return (Comb a' b')
          od = return q)
          ⇒ ∃x y. a = return x ∧ b = return y ∧ q = Comb x y
Proof
  Cases_on ‘a’
  >> Cases_on ‘b’
  >> gvs[bind_EQ_error]
QED

Theorem bind_return_comb_alt:
  ∀a v b b'.
    a = return a' ∧ b = return b' ∧ q = Comb a' b'
    ⇒ (do
             a' <- a;
             b' <- b;
             return (Comb a' b')
           od = return q)
Proof
  Cases_on ‘a’
  >> Cases_on ‘b’
  >> gvs[bind_EQ_error]
QED

Theorem bind_error_comb:
  ∀a b e.
    (do
      a' <- a;
      b' <- b;
      return (Comb a' b')
    od = error e)
    ⇒ a = error e ∨ b = error e
Proof
  Cases_on ‘a’
  >> Cases_on ‘b’
  >> gvs[bind_EQ_error]
QED

Theorem esubst_ty0_error_comb:
  esubst_ty0 env σ (Comb t1 t2) = error e
  ⇒ esubst_ty0 env σ t1 = error e
    ∨ esubst_ty0 env σ t2 = error e
Proof
  rw[esubst_ty0_def] >> drule bind_error_comb >> rw[]
QED

Theorem esubst_ty0_return_comb:
  esubst_ty0 env σ (Comb t1 t2) = return v
  ⇒ ∃v1 v2. esubst_ty0 env σ t1 = return v1
            ∧ esubst_ty0 env σ t2 = return v2
            ∧ v = Comb v1 v2
Proof
  rw[esubst_ty0_def] >> Cases_on ‘esubst_ty0 env σ t1’
  >> Cases_on ‘esubst_ty0 env σ t2’ >> rw[] >> gvs[bind_EQ_error]
QED

Theorem VFREE_IN_VSUBST:
  ∀tm ilist.
    term_ok sig tm
    ∧ (∀v1 v2. MEM (v1, v2) ilist ⇒
               ∃n1 t1 n2 t2. v1 = Var n1 t1 ∧ v2 = Var n2 t2 ∧ v1 ≠ v)
    ∧ VFREE_IN v (VSUBST ilist tm) ⇒ VFREE_IN v tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, VFREE_IN_def, term_ok_def]
  >- (Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’ >> gvs[]
      >> drule rev_assocd_neq_mem >> rw[]
      >> first_x_assum drule >> rw[] >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> strip_tac >> gvs[] >> first_x_assum drule >> rw[])
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> first_x_assum irule >> first_assum $ irule_at Any
      >> simp[MEM_FILTER] >> rw[] >> gvs[])
  >- (gvs[EVERY_MEM, MEM_FILTER, FORALL_PROD] >> first_x_assum irule
      >> first_x_assum $ irule_at Any >> simp[MEM_FILTER])
QED

Definition env_ok_def:
  env_ok env =
  (∀v1 v2. MEM (v1, v2) env
            ⇒ ∃n t1 t2. v1 = Var n t1 ∧ v2 = Var n t2)
End

Theorem env_ok_ext:
  ∀env x t1 t2.
    env_ok env
    ⇒ env_ok ((Var x t1, Var x t2)::env)
Proof
  rw[env_ok_def] >> metis_tac[]
QED

Theorem env_ok_nil[simp]:
  env_ok []
Proof
  rw[env_ok_def]
QED

Theorem VFREE_IN_tm_names:
  ∀tm n ty. VFREE_IN (Var n ty) tm ⇒ MEM n (tm_names tm)
Proof
  Induct_on ‘tm’ >> simp[VFREE_IN_def] >> metis_tac[]
QED

Theorem nvar_aux_never_mem:
  ∀nms n. ¬MEM (nvar_aux nms n) nms
Proof
  recInduct nvar_aux_ind >> rw[] >> simp[Once nvar_aux] >> rw[]
QED

Theorem NVARIANT_THM:
  ∀ty t n. ¬VFREE_IN (Var (NVARIANT n t) ty) t
Proof
  metis_tac[VFREE_IN_tm_names, nvar_aux_never_mem, NVARIANT]
QED

Theorem NVARIANT_NAMES_THM:
  ∀tm n. ¬MEM (NVARIANT n tm) (tm_names tm)
Proof
  metis_tac[nvar_aux_never_mem, NVARIANT]
QED

Definition FVs_def[simp]:
  FVs (Var n ty) = {(n, ty)} ∧
  FVs (Const _ _) = {} ∧
  FVs (Comb t1 t2) = FVs t1 ∪ FVs t2 ∧
  FVs (Abs v body) = FVs body DIFF FVs v
End

Theorem FVs_VFREE_in:
  ∀tm n ty.
    term_ok sig tm ⇒
    (VFREE_IN (Var n ty) tm ⇔ (n, ty) ∈ FVs tm)
Proof
  Induct_on ‘tm’ >> rw[VFREE_IN_def, FVs_def, term_ok_def]
  >> gvs[term_ok_def, FVs_def] >> metis_tac[]
QED

Definition free_names:
  free_names tm = { n | ∃ty. (n, ty) ∈ FVs tm }
End

Theorem free_names_var[simp]:
  free_names (Var n ty) = {n}
Proof
  rw[free_names]
QED

Theorem sublist_map:
  ∀xs. (∀x. MEM x xs ⇒ MEM x ys) ⇒ (∀x. MEM x (MAP f xs) ⇒ MEM x (MAP f ys))
Proof
  Induct_on ‘xs’ >> rw[] >> rw[MEM_MAP_f]
QED

Theorem exists_free_in_ilist:
  ∀ilist x ty tm'.
    EXISTS (λ(s', s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s tm') ilist
    ∧ (∀p. MEM p ilist ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1, Var n2 t2))
    ⇒ (x, ty) ∈ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))
Proof
  rw[EXISTS_MEM, MEM_MAP]
  >> first_x_assum $ drule_then assume_tac
  >> first_x_assum $ irule_at Any >> gvs[]
QED

Theorem fvs_vsubst:
  ∀tm ilist.
    term_ok sig tm
    ∧ (∀p. MEM p ilist ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1, Var n2 t2))
    ⇒ FVs (VSUBST ilist tm) ⊆ FVs tm ∪ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))
Proof
  Induct_on ‘tm’ >> simp[VSUBST_def, FVs_def, term_ok_def]
  >- (rpt gen_tac >> Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’
      >- simp[FVs_def]
      >- (drule rev_assocd_neq_mem >> simp[Once MEM_SPLIT_APPEND_first]
          >> rw[] >> qabbrev_tac ‘V = REV_ASSOCD (Var m t) ilist (Var m t)’
          >> rw[] >> SET_TAC[]))
  >- ASM_SET_TAC[]
  >> rw[AllCaseEqs(), PULL_EXISTS]
  >> gvs[]
  >> qabbrev_tac ‘nv = VARIANT (VSUBST (FILTER (λ(s',s). s ≠ Var x ty) ilist)
                                       tm') (explode x) ty’
  >> qabbrev_tac ‘ilist' = FILTER (λ(s',s). s ≠ Var x ty) ilist’
  >> qabbrev_tac ‘subst_tm = VSUBST ((Var nv ty,Var x ty)::ilist') tm'’
  >> first_assum $ qspec_then ‘(Var nv ty, Var x ty)::ilist'’ assume_tac
  >> ‘∀p. p = (Var nv ty,Var x ty) ∨ MEM p ilist'
          ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1,Var n2 t2)’
    by metis_tac[MEM_FILTER, Abbr‘ilist'’]
  >> gvs[]
  >> first_x_assum drule >> rw[]
  >> ‘∀p. MEM p (MAP (λp. FVs (FST p)) ilist')
          ⇒ MEM p (MAP (λp. FVs (FST p)) ilist)’
    by metis_tac[MEM_FILTER, sublist_map]
  >> ‘BIGUNION (set (MAP (λp. FVs (FST p)) ilist'))
      ⊆ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))’
    by ASM_SET_TAC[SUBSET_BIGUNION]
  >> qabbrev_tac ‘target_vars = BIGUNION (set (MAP (λp. FVs (FST p)) ilist))’
  >> qabbrev_tac ‘target_vars' = BIGUNION (set (MAP (λp. FVs (FST p)) ilist'))’
  >> ‘∀p. MEM p ilist' ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1,Var n2 t2)’ by metis_tac[]
  >- (Cases_on ‘(x, ty) ∈ target_vars’
      >- ASM_SET_TAC[]
      >> drule_all exists_free_in_ilist
      >> strip_tac
      >> ASM_SET_TAC[])
  >> ASM_SET_TAC[]
QED

Theorem variant_name_self:
  ∀tm x ty.
    ¬VFREE_IN (Var x ty) tm
    ⇒ VARIANT tm (explode x) ty = x
Proof
  rw[VARIANT_def]
  >> qspecl_then [‘tm’, ‘explode x’, ‘ty’] assume_tac VARIANT_PRIMES_def >> gvs[]
  >> first_x_assum $ qspec_then ‘0’ assume_tac >> gvs[]
QED

Theorem rev_assocd_default_cases:
  ∀x l d. REV_ASSOCD x l d = d ⇒ MEM (d, x) l ∨ ¬∃y. MEM (y, x) l
Proof
  Induct_on ‘l’ >> rw[REV_ASSOCD_def] >> Cases_on ‘h’ >> gvs[]
QED

Theorem NVARIANT_esubst_ty0:
  ∀tm subst_tm n ty.
    (∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm))
    ∧ term_ok sig tm
    ⇒ ¬VFREE_IN (Var (NVARIANT n subst_tm) ty) tm
Proof
  rw[]
  >> qspecl_then [‘subst_tm’, ‘n’] assume_tac NVARIANT_NAMES_THM
  (*>> first_x_assum $ CONV_TAC CONTRAPOS_CONV*)
  >> ‘¬MEM (NVARIANT n subst_tm) (tm_names tm)’ by metis_tac[]
  >> ‘∀tm n ty. ¬MEM n (tm_names tm) ⇒ ¬VFREE_IN (Var n ty) tm’ suffices_by metis_tac[]
  >> rw[]
  >> Induct_on ‘tm'’
  >> rw[VFREE_IN_def, tm_names_def]
QED

Theorem NVARIANT_esubst_ty0_alt:
  ∀tm subst_tm n ty.
    (∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm))
    ∧ term_ok sig tm
    ⇒ (NVARIANT n subst_tm, ty) ∉ FVs tm
Proof
  metis_tac[NVARIANT_esubst_ty0, FVs_VFREE_in]
QED

fun rC q = rename [q] >> Cases_on q >> simp[]

Theorem rev_assocd_different_default:
  ∀l k d1 d2.
    REV_ASSOCD k l d1 = d1
    ∧ REV_ASSOCD k l d2 = d2
    ∧ d1 ≠ d2
    ⇒ ∀v. ¬MEM (v, k) l
Proof
  Induct_on ‘l’ >> rw[]
  >> rename [‘h::t’] >> Cases_on ‘h’
  >> gvs[REV_ASSOCD_def, AllCaseEqs()]
  >> first_x_assum drule_all
  >> rpt strip_tac
  >> gvs[]
QED

Theorem REV_ASSOCD_EQ_DEFAULT_i = REV_ASSOCD_NEQ_DEFAULT |> CONV_RULE CONTRAPOS_CONV |> SRULE[]

Theorem VSUBST_NOT_FREE:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v k. MEM (v, k) ilist ⇒ ∃n ty. k = Var n ty ∧ (n, ty) ∉ FVs tm) ⇒
    VSUBST ilist tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, term_ok_def]
  >- (irule REV_ASSOCD_EQ_DEFAULT_i >> metis_tac[TypeBase.one_one_of “:term”])
  >- metis_tac[]
  >- metis_tac[]
  >> gvs[]
  >- (gvs[EXISTS_MEM, MEM_FILTER, FVs_VFREE_in, SF SFY_ss]
      >> Cases_on ‘e’ >> gvs[] >> rename [‘MEM (v, k) ilist’]
      >> first_assum drule >> rw[]
      >> gvs[FVs_VFREE_in, SF SFY_ss])
  >> first_x_assum irule
  >> simp[MEM_FILTER]
  >> metis_tac[]
QED

Theorem free_names_comb[simp]:
  ∀t1 t2. free_names (Comb t1 t2) = free_names t1 ∪ free_names t2
Proof
  simp[free_names] >> SET_TAC[]
QED

Definition alist_to_fm_def[simp]:
  alist_to_fm [] = FEMPTY ∧
  alist_to_fm ((v, k)::rest) = alist_to_fm rest |+ (k, v)
End

Definition VSUBSTfm:
  (VSUBSTfm fm (Var x ty) = case FLOOKUP fm (Var x ty) of
                             NONE => Var x ty
                            | SOME t => t) ∧
  (VSUBSTfm fm (Const x ty) = Const x ty) ∧
  (VSUBSTfm fm (Comb t1 t2) = Comb (VSUBSTfm fm t1) (VSUBSTfm fm t2)) ∧
  (VSUBSTfm fm (Abs v t) = let
                             fm' = fm \\ v;
                             t' = VSUBSTfm fm' t
                           in if ∃k w. FLOOKUP fm' k = SOME w ∧ VFREE_IN v w ∧ VFREE_IN k t
                              then (let
                                      (x,ty) = dest_var v;
                                      z = Var (VARIANT t' (explode x) ty) ty;
                                      fm'' = fm' |+ (v, z)
                                    in
                                      Abs z (VSUBSTfm fm'' t))
                              else Abs v t')
End

Theorem alist_to_fm_FILTER:
  ∀ilist k.
    alist_to_fm (FILTER (λ(s',s). s ≠ k) ilist) = alist_to_fm ilist \\ k
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD]
  >> rw[] >> simp[DOMSUB_FUPDATE_NEQ]
QED


Theorem FLOOKUP_alist_to_fm_NONE:
  ∀ilist k. FLOOKUP (alist_to_fm ilist) k = NONE ⇒ REV_ASSOCD k ilist d = d
Proof
  Induct_on ‘ilist’
  >> simp[alist_to_fm_def, REV_ASSOCD_def, FORALL_PROD, FLOOKUP_SIMP, AllCaseEqs()]
QED

Theorem ALL_DISTINCT_MAP_SND:
  ∀ilist v k.
    ALL_DISTINCT (MAP SND ilist) ∧
    MEM (v, k) ilist ⇒
    FLOOKUP (alist_to_fm ilist) k = SOME v
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD, MEM_MAP]
  >> rw[FLOOKUP_SIMP]
  >- metis_tac[]
QED

Theorem FLOOKUP_alist_to_fm_MEM:
  ∀ilist v k.
    FLOOKUP (alist_to_fm ilist) k = SOME v ⇒
    MEM (v, k) ilist
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD, MEM_MAP, FLOOKUP_SIMP] >> rw[]
QED

Theorem VSUBST_VSUBSTfm:
  ∀tm ilist.
    ALL_DISTINCT (MAP SND ilist) ∧
    term_ok sig tm ⇒
    VSUBST ilist tm = VSUBSTfm (alist_to_fm ilist) tm
Proof
  Induct_on ‘tm’ >> simp[VSUBST_def, VSUBSTfm, term_ok_def]
  >- (simp[AllCaseEqs(), FLOOKUP_alist_to_fm_NONE, SF CONJ_ss]
      >> rw[] >> Cases_on ‘FLOOKUP (alist_to_fm ilist) (Var m t)’ >> rw[]
      >> Induct_on ‘ilist’
      >> simp[alist_to_fm_def, REV_ASSOCD_def, FORALL_PROD, FLOOKUP_SIMP, AllCaseEqs()]
      >> metis_tac[])
  >> gvs[MEM_FILTER, EXISTS_MEM, EXISTS_PROD, PULL_EXISTS, alist_to_fm_FILTER,
                     FILTER_ALL_DISTINCT, MAP_SND_FILTER_NEQ]
  >> simp[DOMSUB_FLOOKUP_THM] >> rw[] >> gvs[]
  >- (drule_all_then assume_tac ALL_DISTINCT_MAP_SND
      >> first_x_assum drule >> simp[])
  >- (drule_all_then assume_tac ALL_DISTINCT_MAP_SND
      >> first_x_assum drule >> simp[])
  >> drule_then assume_tac FLOOKUP_alist_to_fm_MEM
  >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem exists_free_in_fm_map:
  ∀tm fm x ty.
    term_ok sig tm ∧
    (∃k v. FLOOKUP fm k = SOME v ∧ VFREE_IN (Var x ty) v ∧ VFREE_IN k tm) ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FDOM fm ⇒ ∃n ty. v = Var n ty) ⇒
    (x, ty) ∈ BIGUNION { FVs t | ∃n ty'. (n, ty') ∈ FVs tm ∧ FLOOKUP fm (Var n ty') = SOME t }
Proof
  rw[FDOM_FLOOKUP, FRANGE_FLOOKUP]
  >> first_x_assum $ qspec_then ‘k’ assume_tac
  >> first_x_assum $ qspec_then ‘v’ assume_tac
  >> gvs[PULL_EXISTS]
  >> first_x_assum $ qspec_then ‘Var n ty'’ assume_tac
  >> rw[]
  >> qexists ‘Var x ty’
  >> rw[FVs_def]
  >> qexistsl [‘n’, ‘ty'’]
  >> rw[FVs_def, FVs_VFREE_in]
  >> metis_tac[FVs_VFREE_in, VFREE_IN_def]
QED
        
Theorem VSUBSTfm_FVs:
  ∀tm fm.
    term_ok sig tm ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FDOM fm ⇒ ∃n ty. v = Var n ty) ⇒
    FVs (VSUBSTfm fm tm) =
    (FVs tm DIFF { (n, ty) | Var n ty ∈ FDOM fm })
    ∪ BIGUNION { FVs t | ∃n ty. (n, ty) ∈ FVs tm ∧ FLOOKUP fm (Var n ty) = SOME t }
Proof
  Induct_on ‘tm’ >> simp[VSUBSTfm, FVs_def, term_ok_def]
  >- (rpt gen_tac
      >> Cases_on ‘FLOOKUP fm (Var m t)’
      >> gvs[FDOM_FLOOKUP]
      >> SET_TAC[])
  >- SET_TAC[]
  >> rw[] >> gvs[term_ok_def]
  >- (qabbrev_tac ‘Xv = VARIANT (VSUBSTfm (fm \\ Var x ty) tm') (explode x) ty’
      >> first_x_assum $ qspec_then ‘fm |+ (Var x ty,Var Xv ty)’ assume_tac
      >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                     assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
      >> gvs[PULL_EXISTS, FORALL_AND_THM, DISJ_IMP_THM]
      >> ‘{(n, ty') | n = x ∧ ty' = ty ∨ Var n ty' ∈ FDOM fm} =
                                         {x, ty} ∪ {(n, ty')
                                             | Var n ty' ∈ FDOM fm}’
        by SET_TAC[]
      >> rw[DIFF_UNION]
      >> Cases_on ‘(Xv, ty) ∈ FVs tm' DIFF {(x,ty)}
                   DIFF {(n,ty') | Var n ty' ∈ FDOM fm}’
      >- cheat
      >> ASM_SET_TAC[])
p  >> cheat
QED

Theorem FVs_VSUBST_CASES:
  ∀tm x ty1 a b ty.
    term_ok sig tm ⇒
    ((x, ty1) ∈ FVs (VSUBST [(Var a ty, Var b ty)] tm) ⇔
       (x = a ∧ ty1 = ty ∧ (b, ty) ∈ FVs tm) ∨
       ((x, ty1) ∈ FVs tm ∧ (x ≠ b ∨ ty1 ≠ ty)))
Proof
  simp[VSUBST_VSUBSTfm, SF SFY_ss, VSUBSTfm_FVs, PULL_EXISTS, FLOOKUP_SIMP]
  >> metis_tac[]
QED

Theorem FVs_VSUBST_PRESERVED_VAR:
  ∀tm n n1 n2 ty ty1.
    term_ok sig tm ∧
    (n, ty) ∈ FVs tm ∧
    ty ≠ ty1 ⇒
    (n, ty) ∈ FVs (VSUBST [(Var n2 ty1, Var n1 ty1)] tm)
Proof
  metis_tac[FVs_VSUBST_CASES]
QED

Theorem FVs_VSUBST_SUBSTITUTED_VAR:
  ∀tm n oldN ty.
    term_ok sig tm ∧
    (n, ty) ∈ FVs tm ⇒
    (n, ty) ∈ FVs (VSUBST [(Var n ty, Var oldN ty)] tm)
Proof
  metis_tac[FVs_VSUBST_CASES]
QED

Theorem FVs_in_tm_names:
  ∀tm n ty. (n, ty) ∈ FVs tm ⇒ MEM n (tm_names tm)
Proof
  cheat
QED

Theorem tm_names_vsubst:
  ∀tm n m ty1 ty2. 
    (n, ty1) ∈ FVs tm ∧
    ty1 ≠ ty2 ∧
    MEM n (tm_names tm) ⇒
    MEM n (tm_names (VSUBST [(Var m ty2, Var n ty2)] tm))
Proof
  cheat
QED

Theorem tm_names_unrelated_vsubst:
  ∀tm subst_tm ilist.
    term_ok sig tm ∧
    (∀v. v ∈ ilist ⇒ ∃x ty. v = (Var (NVARIANT x subst_tm) ty, Var x ty)) ∧ 
    MEM n (tm_names tm) ∧ 
    n ≠ NVARIANT x subst_tm ⇒
    MEM n (tm_names (VSUBST ilist [(Var (NVARIANT x subst_tm) ty, Var x ty)] tm))
Proof
  rw[term_ok_def] >> Cases_on ‘n = x’
  >- cheat
  >> Induct_on ‘tm’
  >> rw[tm_names_def, VSUBST_def, REV_ASSOCD_def, term_ok_def]
  >- (rpt $ first_x_assum drule >> simp[])
  >- (rpt $ first_x_assum drule >> simp[])
  >> gvs[]
  >> Cases_on ‘n =
               VARIANT (VSUBST [(Var (NVARIANT x subst_tm) ty,Var x ty)] tm')
                       (explode (NVARIANT x subst_tm)) ty’
  >> rw[]
  >> cheat
QED
        
Theorem esubst_ty0_impossible1:
  ∀env σ tm.
    (∀k v. MEM (v, k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    term_ok sig tm ⇒
    (∀e. esubst_ty0 env σ tm = error e ⇒
       ∃n typ1 typ2.
         (n, typ1) ∈ FVs tm ∧
         ty_esubst σ typ1 = ty_esubst σ typ2 ∧
         typ1 ≠ typ2 ∧
         REV_ASSOCD (Var n (ty_esubst σ typ1)) env (Var n typ1) = Var n typ2 ∧
         e = Var n (ty_esubst σ typ1)) ∧
    (∀n typ1 typ2.
       (n, typ1) ∈ FVs tm ∧
       ty_esubst σ typ1 = ty_esubst σ typ2 ∧
       typ1 ≠ typ2 ∧
       REV_ASSOCD (Var n (ty_esubst σ typ1)) env (Var n typ1) = Var n typ2
       ⇒ ∃e. esubst_ty0 env σ tm = error e) ∧
    (∀subst_tm. esubst_ty0 env σ tm = return subst_tm ⇒
                ∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm)) 
Proof
  recInduct esubst_ty0_ind >> REWRITE_TAC[esubst_ty0_def] >> rpt strip_tac
  >- (gvs[AllCaseEqs()]
      >> drule rev_assocd_neq_mem >> rw[]
      >> first_x_assum drule >> rw[]
      >> metis_tac[])
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> metis_tac[TypeBase.nchotomy_of “:(α, β) error”])
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> metis_tac[TypeBase.nchotomy_of “:(α, β) error”])
  >- gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >- (gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def, AllCaseEqs()]
          >> first_assum $ irule_at (Pat ‘_ ∈ FVs body’)
          >> simp[] >> rpt strip_tac >> gvs[])
      >- gvs[REV_ASSOCD_def]
      >> gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def, AllCaseEqs(), neq_error]
      >> gvs[term_ok_vsubst_variant]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac
      >> gvs[]
      >> metis_tac[FVs_VSUBST_CASES, NVARIANT_esubst_ty0_alt])
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> gvs[DISJ_IMP_THM, term_ok_vsubst_variant]
      >> gvs[neq_error, REV_ASSOCD_def, term_ok_vsubst_variant,
             PULL_EXISTS, DISJ_IMP_THM, AllCaseEqs(), term_ok_def]
      >> rename [‘esubst_ty0 [] σ body = return subst_tm’]
      >> last_x_assum $ qspec_then ‘subst_tm’ assume_tac
      >> Cases_on ‘n = x’
      >- (Cases_on ‘ty_esubst σ ty = ty_esubst σ typ1’
          >> metis_tac[FVs_VSUBST_PRESERVED_VAR, NVARIANT_esubst_ty0_alt])
      >> gvs[]
      >> metis_tac[FVs_VSUBST_CASES, NVARIANT_esubst_ty0_alt])
  >> gvs[term_ok_def]
  >> gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs(),
         try_eq_return]
  >> gvs[DISJ_IMP_THM, term_ok_vsubst_variant]
  >> gvs[neq_error, REV_ASSOCD_def, term_ok_vsubst_variant,
         PULL_EXISTS, DISJ_IMP_THM, AllCaseEqs(), term_ok_def]
  >- (rC ‘n = NVARIANT n body1’ >> rw[]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac >> rw[]
      >> drule FVs_in_tm_names >> rw[]
      >> first_x_assum $ irule_at Any
      >> drule_all tm_names_vsubst
      >> metis_tac[])
  >- (rC ‘n = NVARIANT x body1’ >> rw[]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac >> rw[]
      >> gvs[term_ok_vsubst_variant]
      >> first_x_assum drule >> rw[]
      >> first_x_assum irule
      >> irule tm_names_unrelated_vsubst
      >> rw[])
QED

Theorem esubst_ty0_always_returns:
  ∀σ tm.
    term_ok sig tm ⇒
    ∃v. esubst_ty0 [] σ tm = return v
Proof
  rpt gen_tac
  >> qspec_then ‘[]’ assume_tac esubst_ty0_impossible1
  >> gvs[REV_ASSOCD_def, neq_error]
QED

Inductive proves':
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok thy.ctys ty ∧
   (thy, es, h) |-' l === r
   ⇒ (thy, es, h) |-' (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok' thy ∧ p has_type Bool ∧ term_ok' thy p
   ⇒ (thy, {}, [p]) |-' p)

[~BETA:]
  (theory_ok' thy ∧ type_ok thy.ctys ty
   ∧ term_ok' thy t
   ⇒ (thy, {}, []) |-' Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, es1, h1) |-' c1 ∧
   (thy, es2, h2) |-' c2
   ⇒ (thy, es1 ∪ es2, term_union (term_remove c2 h1)
                                 (term_remove c1 h2))
     |-' c1 === c2)

[~EQ_MP:]
  ((thy, es1, h1) |-' p === q ∧
   (thy, es2, h2) |-' p' ∧ ACONV p p'
   ⇒ (thy, es1 ∪ es2, term_union h1 h2) |-' q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
           ∃x ty. (s = Var x ty) ∧ s' has_type ty
                  ∧ term_ok' thy s') ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (VSUBST ilist) h) |-' VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok thy.ctys) (MAP FST tyin)) ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (INST tyin) h) |-' INST tyin c)

[~MK_COMB:]
  ((thy, es1, h1) |-' l1 === r1 ∧
   (thy, es2, h2) |-' l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, es1 ∪ es2, term_union h1 h2) |-' Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok' thy ∧ term_ok' thy t
   ⇒ (thy, {}, []) |-' t === t)

[~axioms:]
  (theory_ok' thy ∧ c ∈ thy.axs
   ⇒ (thy, {}, []) |-' c)

[~elim_discharge:]
  ((thy, es1, []) |-' c1 ∧ (thy, es2, h2) |-' c2
   ⇒ (thy, (es2 DIFF {c1}) ∪ es1, h2) |-' c2)

[~elim_inst:]
  ((thy, es, h) |-' c
   ∧ (∀p. p ∈ es ⇒ term_ok thy.sig (esubst σ p) ∧ (esubst σ p) has_type Bool)
   ∧ (∀p. MEM p h ⇒ term_ok thy.sig (esubst σ p) ∧ (esubst σ p) has_type Bool)
   ∧ (esubst σ c) has_type Bool
   ∧ term_ok thy.sig (esubst σ c)
   ⇒ (thy, IMAGE (esubst σ) es, MAP (esubst σ) h) |-' esubst σ c)

[~elim_axioms:]
  (theory_ok' thy ∧ c ∈ thy.eaxs
   ⇒ (thy, {c}, []) |-' c)
End

Definition lift_thy_def:
  lift_thy (thy:thy) = <| tms := tmsof thy;
                          tys := tysof thy;
                          etms := FEMPTY;
                          etys := FEMPTY;
                          axs := axsof thy;
                          eaxs := {} |>
End

Theorem tmsof_lift_thy[simp]:
  (lift_thy thy).tms = tmsof thy
Proof
  simp[lift_thy_def]
QED

Theorem tysof_lift_thy[simp]:
  (lift_thy thy).tys = tysof thy
Proof
  simp[lift_thy_def]
QED

Theorem axsof_lift_thy[simp]:
  (lift_thy thy).axs = axsof thy
Proof
  simp[lift_thy_def]
QED

Theorem eaxsof_lift_thy[simp]:
  (lift_thy thy).eaxs = {}
Proof
  simp[lift_thy_def]
QED

Theorem etmsof_lift_thy[simp]:
  (lift_thy thy).etms = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem etysof_lift_thy[simp]:
  (lift_thy thy).etys = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem sigof_lift_thy[simp]:
  (lift_thy thy).sig = sigof thy
Proof
  simp[lift_thy_def, sigof'_def]
QED

Theorem ctys_lift_thy[simp]:
  (lift_thy thy).ctys = tysof thy
Proof
  simp[lift_thy_def, ctys_def]
QED

Theorem ctms_lift_thy[simp]:
  (lift_thy thy).ctms = tmsof thy
Proof
  simp[lift_thy_def, ctms_def]
QED

Theorem theory_ok'_lift_thy[simp]:
  theory_ok' (lift_thy thy) ⇔ theory_ok thy
Proof
  rw[theory_ok_def, theory_ok'_def, lift_thy_def]
QED

Theorem term_ok'_lift_thy[simp]:
  term_ok' (lift_thy thy) tm ⇔ term_ok (sigof thy) tm
Proof
  Induct_on ‘tm’
  >> rw[term_ok_def, term_ok'_def, lift_thy_def]
QED

Theorem proves_imp_proves':
  ∀h. (thy, h) |- c ⇒ (lift_thy thy, {}, h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> rw[])
  >- (irule proves'_ASSUME >> rw[])
  >- (irule proves'_BETA >> rw[])
  >- (dxrule_all_then (ACCEPT_TAC o SRULE[]) proves'_DEDUCT_ANTISYM)
  >- (dxrule_all proves'_EQ_MP >> rw[])
  >- (irule proves'_INST >> rw[])
  >- (irule proves'_INST_TYPE >> rw[])
  >- (dxrule_all proves'_MK_COMB >> rw[])
  >- (irule proves'_REFL >> rw[])
  >- (irule proves'_axioms >> rw[])
QED

Theorem type_ind =
        TypeBase.induction_of``:holSyntax$type``
          |> Q.SPECL[`P`,`EVERY P`]
          |> SIMP_RULE std_ss [EVERY_DEF]
          |> UNDISCH_ALL
          |> CONJUNCT1
          |> DISCH_ALL
          |> Q.GEN`P`

Theorem proves_theory_ok:
  ∀thy h c. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem proves_theory_ok_ext:
  theory_ok thy1 ∧ (thy2, h) |- c ∧ sigof thy1 = sigof thy2
  ⇒ theory_ok (sigof thy1, axsof thy1 DIFF {c1} ∪ axsof thy2)
Proof
  rw[] >> drule proves_theory_ok >> gvs[theory_ok_def] >> metis_tac[]
QED

Theorem proves_imp_theory_ok:
  ∀thy h. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem axiom_weakening:
  ∀A B h. ((sig, A), h) |- c
          ∧ (∀p. p ∈ B ⇒ term_ok sig p ∧ p has_type Bool)
          ∧ A ⊆ B
          ⇒ ((sig, B), h) |- c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[] >> gvs[])
  >- (irule proves_ASSUME >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_BETA >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> metis_tac[])
  >- (irule proves_INST >> rw[] >> gvs[])
  >- (irule proves_INST_TYPE >> rw[] >> gvs[])
  >- (irule proves_MK_COMB >> rw[] >> gvs[])
  >- (irule proves_REFL >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def])
  >- (irule proves_axioms >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def, SUBSET_DEF])
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h2 c1 c2.
    (thy2, h2) |- c2 ∧ (thy1, []) |- c1
    ∧ sigof thy1 = sigof thy2
    ⇒ ((sigof thy1, (axsof thy2 DIFF {c1}) UNION axsof thy1), h2) |- c2
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_BETA >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> rw[] >> metis_tac[])
  >- (irule proves_INST >> rw[])
  >- (irule proves_INST_TYPE >> rw[])
  >- (irule proves_MK_COMB >> rw[])
  >- (irule proves_REFL >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (Cases_on ‘c1 = c2’
      >- (rw[] >> irule axiom_weakening >> rw[]
          >> gvs[theory_ok_def] >> drule proves_imp_theory_ok >> rw[theory_ok_def]
          >> qexists ‘axsof thy1’ >> rw[] >> Cases_on ‘thy1’ >> gvs[])
      >- (irule proves_axioms >> rw[] >> metis_tac[proves_theory_ok_ext]))
QED

Definition drop_thy:
  (drop_thy used_eaxs thy'):thy = ((thy'.ctys, thy'.ctms), thy'.axs UNION used_eaxs)
End

Theorem sigof_drop_thy[simp]:
  sigof (drop_thy es thy) = (thy.ctys, thy.ctms)
Proof
  rw[drop_thy]
QED

Theorem axsof_drop_thy:
  thy.axs ⊆ axsof (drop_thy es thy)
Proof
  rw[drop_thy]
QED

Theorem type_ok_weakening:
  ∀ty. type_ok ts1 ty ⇒ type_ok (ts1 ⊌ ts2) ty
Proof
  Induct_on ‘ty’ using type_ind >> gvs[type_ok_def, FLOOKUP_FUNION, EVERY_MEM]
QED

Theorem term_ok_weakening:
  ∀tm. term_ok (tys, tms) tm ⇒ term_ok (tys ⊌ tys1, tms ⊌ tms1) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok_def, type_ok_weakening]
  >> qexists ‘ty0’ >> rw[FLOOKUP_FUNION, type_ok_weakening] >> metis_tac[]
QED

Theorem is_std_sig_funion:
  is_std_sig (tys, tms) ⇒ is_std_sig (tys ⊌ tys1, tms ⊌ tms1)
Proof
  rw[is_std_sig_def, FLOOKUP_FUNION]
QED

Theorem theory_ok_drop_thy:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok thy.sig a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
QED

Theorem term_ok'_imp_term_ok:
  term_ok' thy c ⇒ term_ok (thy.ctys, thy.ctms) c
Proof
  Induct_on ‘c’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem term_ok_imp_term_ok':
  term_ok (thy.ctys, thy.ctms) c ⇒ term_ok' thy c
Proof
  Induct_on ‘c’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem theory_ok_drop_thy_alt:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok' thy a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
  >> metis_tac[term_ok'_imp_term_ok, ctys_def, ctms_def]
QED

Theorem proves_imp_theory_ok':
  ∀thy h es c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED

Theorem thy_axs_diff:
  c ∉ a ⇒
  a ∪ (b DIFF {c} ∪ d) = ((a ∪ b) DIFF {c}) ∪ (a ∪ d)
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
QED

Theorem thy_axs_diff_alt:
  c ∈ a ⇒
  a ∪ (b DIFF {c} ∪ d) = a ∪ b ∪ d
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
QED

Theorem proves'_imp_theory_ok:
  ∀thy es h c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED

Theorem term_ok_term_ok'_weakening:
  term_ok thy.sig p ⇒ term_ok' thy p
Proof
  rw[] >> irule term_ok_imp_term_ok'
  >> gvs[sigof'_def, ctms_def, ctys_def, term_ok_weakening]
QED

Theorem used_eaxs_ok:
  ∀thy' used_eaxs h c.
    (thy', used_eaxs, h) |-' c
    ⇒ ∀e. e ∈ used_eaxs ⇒ term_ok' thy' e ∧ e has_type Bool
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[] >> gvs[theory_ok'_def, term_ok_term_ok'_weakening]
QED

Definition esubsts_ok_def:
  esubsts_ok σ = T
End

Theorem esubst_ty_ok_tys:
  ∀a b. esubsts_ok σ ⇒ esubst_ty σ (a === b) = (esubst_ty σ a) === (esubst_ty σ b)
Proof
  cheat
QED
        
Theorem esubst_equation[simp]:
  ∀a b.
    esubsts_ok σ ⇒
    esubst σ (a === b) = esubst σ a === esubst σ b
Proof
  rw[esubst_def, esubst_tm_def]
  >> drule esubst_ty_ok_tys >> gvs[equation_def] >> metis_tac[]
QED

Theorem proves_substitutable:
  ∀sig h c.
    ((sig, axs ∪ es), h) |- c ∧
    theory_ok (sig, axs ∪ IMAGE (esubst σ) es) ∧
    (∀p. p ∈ es ⇒
         term_ok sig (esubst σ p) ∧
         esubst σ p has_type Bool) ∧
    (∀p. MEM p h ⇒
         term_ok sig (esubst σ p) ∧
         esubst σ p has_type Bool) ∧
    esubst σ c has_type Bool ∧ term_ok sig (esubst σ c) ⇒
    ((sig, axs ∪ IMAGE (esubst σ) es), MAP (esubst σ) h) |- esubst σ c
Proof
  Induct_on ‘$|-’ >> rw[esubst_def, esubst_equation]
  >- (irule proves_ABS >> rw[] >> cheat)
  >- (irule proves_ASSUME >> rw[])
  >- (irule proves_BETA >> rw[] >> cheat)
  >- (irule proves_DEDUCT_ANTISYM >> rw[] >> cheat)
  >- (irule proves_EQ_MP >> qexistsl [‘p’, ‘c’] >> rw[] >> cheat)
  >- (cheat >> irule proves_INST)
  >- (cheat >> irule proves_INST_TYPE)
  >- (irule proves_MK_COMB >> rw[] >> cheat)
  >- (irule proves_axioms >> rw[] >> gvs[] >> cheat)
  >- (irule proves_axioms >> rw[] >> gvs[]
      >- cheat
      >- metis_tac[])
QED

Theorem drop_thy_weakening:
  (drop_thy B thy', h) |- c ∧ B ⊆ A
  ∧ (∀ax. ax ∈ A ⇒ term_ok (thy'.ctys, thy'.ctms) ax ∧ ax has_type Bool)
  ⇒ (drop_thy A thy', h) |- c
Proof
  rw[drop_thy] >> irule axiom_weakening >> rw[]
  >> drule proves_imp_theory_ok >> rw[theory_ok_def, ctms_def, ctys_def]
  >> gvs[ctys_def, ctms_def] >> first_assum $ irule_at Any >> ASM_SET_TAC[]
QED

Theorem proves'_imp_proves:
  ∀thy' c h used_eaxs.
    (thy', used_eaxs, h) |-' c ⇒ (drop_thy used_eaxs thy', h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_BETA >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_DEDUCT_ANTISYM
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_EQ_MP
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST_TYPE >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_MK_COMB >> rw[]
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_REFL >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_axioms >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok]
      >> metis_tac[axsof_drop_thy, SUBSET_DEF])
  >- (Cases_on ‘c ∈ thy.axs’ >> gvs[drop_thy]
      >- (rw[thy_axs_diff_alt, UNION_COMM] >> irule axiom_weakening
          >> drule proves'_imp_theory_ok >> rw[]
          >> gvs[theory_ok'_def, used_eaxs_ok, term_ok'_imp_term_ok, term_ok_term_ok'_weakening]
          >> rpt $ dxrule used_eaxs_ok >> rw[term_ok'_imp_term_ok]
          >> qexists ‘thy.axs ∪ es2’ >> rw[] >> SET_TAC[])
      >- (rw[thy_axs_diff]
          >> qspecl_then [‘((thy.ctys, thy.ctms), thy.axs ∪ es1)’,
                          ‘((thy.ctys, thy.ctms), thy.axs ∪ es2)’,
                          ‘h2’, ‘c’, ‘c'’]
                         assume_tac axioms_eliminable
          >> gvs[]))
  >- (gvs[drop_thy] >> irule proves_substitutable >> rw[] >> gvs[EVERY_MEM]
      >> metis_tac[sigof'_def, ctys_def, ctms_def, term_ok_weakening])
  >- (irule proves_axioms >> rw[]
      >- (irule theory_ok_drop_thy_alt >> gvs[theory_ok'_def])
      >> rw[drop_thy])
QED

(* A context is a sequence of updates *)

Datatype:
  update'
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec ((mlstring # term) list) term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn mlstring term mlstring mlstring
  (* NewType name arity *)
  | NewType mlstring num
  (* NewEliminableType name arity *)
  | NewEliminableType mlstring num
  (* NewConst name type *)
  | NewConst mlstring type
  (* NewEliminableConst name type *)
  | NewEliminableConst mlstring type
  (* NewAxiom proposition *)
  | NewAxiom term
  (* NewEliminableAxiom proposition *)
  | NewEliminableAxiom term
End

(* Projecting out pieces of the context *)

(* Types and constants introduced by an update *)
Definition types_of_upd_def:
  (types_of_upd' (ConstSpec _ _) = []) ∧
  (types_of_upd' (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd' (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd' _ = [])
End

Definition consts_of_upd_def:
  (consts_of_upd' (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd' (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd' (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd' _ = [])
End

Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)``
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)``
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``

(* From this we can recover a signature *)
Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
Definition axexts_of_upd_def:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End

Definition conexts_of_upd_def:
  (conexts_of_upd (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var (strlit "a") abs_type in
    let r = Var (strlit "r") rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd _ = [])
End

Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)``
Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)``

Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd``
Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)``
Overload axsof = ``λctxt. set (axiom_list ctxt)``

val _ = export_rewrites["types_of_upd_def","consts_of_upd_def","axexts_of_upd_def"]

(* Now we can recover the theory associated with a context *)
Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)``

(* Principles for extending the context *)

val _ = Parse.add_infix("updates",450,Parse.NONASSOC)

val _ = hide "abs";

Inductive updates':
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop
   ⇒ (NewAxiom prop) updates' ctxt) ∧

  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates' ctxt) ∧

  (* new_specification *)
  ((thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
   EVERY
     (λt. CLOSED t ∧
          (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
     (MAP SND eqs) ∧
   (∀x ty. VFREE_IN (Var x ty) prop ⇒
             MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
   (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
   ALL_DISTINCT (MAP FST eqs)
   ⇒ (ConstSpec eqs prop) updates' ctxt) ∧

  (* new_type *)
  (name ∉ (FDOM (tysof ctxt))
   ⇒ (NewType name arity) updates' ctxt) ∧

  (* new_type_definition *)
  (((thyof ctxt, empty_elims), [], []) |- Comb pred witness ∧
   CLOSED pred ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates' ctxt)
End

Definition extends'_def:
  extends' ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates' ctxt1)
End
val _ = Parse.add_infix("extends'",450,Parse.NONASSOC)

(* Initial theory context *)

Definition init_ctxt_def:
  init_ctxt = [NewConst (strlit "=") (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
              ;NewType (strlit "bool") 0
              ;NewType (strlit "fun") 2]
End

val _ = export_theory()
