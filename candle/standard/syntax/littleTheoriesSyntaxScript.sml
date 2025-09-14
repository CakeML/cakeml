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

Definition esubst_sig_def:
  esubst_sig σ (tys, tms) = (tys, ty_esubst σ o_f tms)
End

Definition try_def:
  try (return v) f = return v ∧
  try (error e) f = f e
End

Definition tm_names_def[simp]:
  tm_names (Var n _) = [n] ∧
  tm_names (Const _ _) = [] ∧
  tm_names (Comb t1 t2) = tm_names t1 ++ tm_names t2 ∧
  tm_names (Abs v body) = tm_names v ++ tm_names body
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
  NVARIANT n avds tm = nvar_aux (tm_names tm ++ avds) n
End

(* analog of INST_CORE *)
Definition esubst_ty0_def:
  (esubst_ty0 env (σ:(mlstring |-> type) # (mlstring |-> term)) avds (Var n ty) =
   let
     tm = Var n ty;
     tm' = Var n (ty_esubst σ ty)
   in if REV_ASSOCD tm' env tm = tm then
        return tm'
      else error tm') ∧
  (esubst_ty0 env σ avds (Const n ty) =
   return $ Const n (ty_esubst σ ty)) ∧
  (esubst_ty0 env σ avds (Comb t1 t2) =
   do
     t1' <- esubst_ty0 env σ avds t1;
     t2' <- esubst_ty0 env σ avds t2;
     return $ Comb t1' t2'
   od) ∧
  (esubst_ty0 env σ avds (Abs v body) =
   let
     (n, ty) = dest_var v;
     ty' = ty_esubst σ ty;
     v' = Var n ty'
   in try
      do
        body' <- esubst_ty0 ((v, v')::env) σ avds body;
        return $ Abs v' body'
      od
      (λbad_v.
         if bad_v ≠ v' then
           error bad_v
         else
           do
             body1 <- esubst_ty0 [] σ avds body;
             n' <<- NVARIANT n avds body1;
             body' <<- VSUBST [(Var n' ty, Var n ty)] body;
             env'' <<- (Var n' ty, Var n' ty')::env;
             body'' <- esubst_ty0 env'' σ avds body';
             return $ Abs (Var n' ty') body''
           od))
Termination
  WF_REL_TAC ‘measure (sizeof o SND o SND o SND)’ >> simp[SIZEOF_VSUBST]
End

Definition esubst_ty_def:
  esubst_ty σ avds tm =
  case esubst_ty0 [] σ avds tm of
  | return v => v
  | error e => ARB (* see esubst_ty0_always_returns *)
End

Definition esubst_tm_def:
  esubst_tm (σ:(mlstring |-> type) # (mlstring |-> term)) (Var n ty) = Var n ty ∧
  esubst_tm σ (Abs v t) = Abs v (esubst_tm σ t) ∧
  esubst_tm σ (Comb t1 t2) = Comb (esubst_tm σ t1) (esubst_tm σ t2) ∧
  esubst_tm σ (Const n ty) = case FLOOKUP (SND σ) n of
                             | NONE => Const n ty
                             | SOME tm => tm
End

Definition esubst_def:
  esubst σ avds tm = esubst_tm σ (esubst_ty σ avds tm)
End

Definition vsubst_tys_ok_def:
  vsubst_tys_ok ilist =
  (∀s s'. MEM (s',s) ilist ⇒
          ∃x ty. (s = Var x ty) ∧ s' has_type ty)
End

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

Definition FVs_def[simp]:
  FVs (Var n ty) = {(n, ty)} ∧
  FVs (Const _ _) = {} ∧
  FVs (Comb t1 t2) = FVs t1 ∪ FVs t2 ∧
  FVs (Abs v body) = FVs body DIFF FVs v
End

Definition free_names:
  free_names tm = { n | ∃ty. (n, ty) ∈ FVs tm }
End

Theorem free_names_var[simp]:
  free_names (Var n ty) = {n}
Proof
  rw[free_names]
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

Overload is_monomorphic = “λty. tyvars ty = []”

Type SIG = “:((mlstring |-> num) # (mlstring |-> type))”

Definition esubsts_ok_def:
  esubsts_ok (sig:SIG) (σ, θ) ⇔
    strlit "=" ∉ FDOM θ ∧
    strlit "bool" ∉ FDOM σ ∧
    (∀tyn typ. FLOOKUP (tysof sig) tyn = SOME 0 ∧
               FLOOKUP σ tyn = SOME typ ⇒
               is_monomorphic ty) ∧
    (∀tmnm. tmnm ∈ FDOM θ ⇒
            ∃ty. FLOOKUP (tmsof sig) tmnm = SOME ty ∧
                 is_monomorphic ty ∧
                 typeof (θ ' tmnm) = ty_esubst (σ, θ) ty) ∧
    (∀ty. ty ∈ FRANGE σ ⇒ type_ok (tysof sig) ty) ∧
    (∀tm. tm ∈ FRANGE θ ⇒ term_ok sig tm)
End

(* Standard signature includes the minimal type operators and constants *)
Theorem esubst_sig_is_std_sig:
  esubsts_ok sig σ ∧ is_std_sig sig ⇒ is_std_sig (esubst_sig σ sig)
Proof
  Cases_on ‘σ’ >> rename [‘(σ, θ)’]
  >> Cases_on ‘sig’ >> rename [‘(tys, tms)’]
  >> rw[esubsts_ok_def, esubst_sig_def, is_std_sig_def]
  >> rw[FLOOKUP_o_f, ty_esubst_def] >> CASE_TAC
  >> metis_tac[FDOM_FLOOKUP]
QED

Definition esubsts_total_def:
  esubsts_total (thy:ethy) (σ, θ) ⇔
    (∀tyn. tyn ∈ FDOM σ ⇔ tyn ∈ FDOM thy.etys) ∧
    (∀tmn. tmn ∈ FDOM θ ⇔ tmn ∈ FDOM thy.etms)
End

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
  ((thy, es, h) |-' c ∧
   theory_ok' thy ∧
   esubsts_ok (thy.ctys, thy.ctms) σ ∧
   esubsts_total thy σ
   ⇒ (thy, IMAGE (esubst σ []) es, term_image (esubst σ []) h) |-'
     esubst σ (FLAT (MAP tm_names h)) c)

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

val _ = temp_set_fixity "|n-" (Infix(NONASSOC, 450));

Inductive nproves:
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (tysof thy) ty ∧
   (thy, h, n) |n- l === r
   ⇒ (thy, h, n + 1) |n- (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, [p], 0) |n- p)

[~BETA:]
  (theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, [], 0) |n- Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, h1, n) |n- c1 ∧
   (thy, h2, m) |n- c2
   ⇒ (thy, term_union (term_remove c2 h1)
                      (term_remove c1 h2),
      n + m + 1)
   |n- c1 === c2)

[~EQ_MP:]
  ((thy, h1, n) |n- p === q ∧
   (thy, h2, m) |n- p' ∧ ACONV p p'
   ⇒ (thy, term_union h1 h2, n + m + 1) |n- q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, h, n) |n- c
   ⇒ (thy, term_image (VSUBST ilist) h, n + 1) |n- VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, h, n) |n- c
   ⇒ (thy, term_image (INST tyin) h, n + 1) |n- INST tyin c)

[~MK_COMB:]
  ((thy, h1, n) |n- l1 === r1 ∧
   (thy, h2, m) |n- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, term_union h1 h2, n + m + 1) |n- Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok thy ∧ term_ok (sigof thy) t
   ⇒ (thy, [], 0) |n- t === t)

[~axioms:]
  (theory_ok thy ∧ c ∈ (axsof thy)
   ⇒ (thy, [], 0:num) |n- c)
End


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
Definition types_of_upd'_def:
  (types_of_upd' (ConstSpec _ _) = []) ∧
  (types_of_upd' (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd' (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd' (NewEliminableType name arity) = []) (* not here *) ∧
  (types_of_upd' _ = [])
End

Definition consts_of_upd'_def:
  (consts_of_upd' (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd' (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd' (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd' (NewEliminableConst name type) = []) (* not here *) ∧
  (consts_of_upd' _ = [])
End

Overload type_list = ``λctxt. FLAT (MAP types_of_upd' ctxt)``
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd' ctxt)``
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
Definition axexts_of_upd'_def:
  axexts_of_upd' (NewAxiom prop) = [prop] ∧
  axexts_of_upd' (NewEliminableAxiom prop) = [prop] ∧
  axexts_of_upd' _ = []
End

Definition conexts_of_upd'_def:
  (conexts_of_upd' (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd' (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var (strlit "a") abs_type in
    let r = Var (strlit "r") rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd' (NewEliminableAxiom prop) = []) ∧
  (conexts_of_upd' _ = [])
End

Overload axexts' = ``λctxt. FLAT (MAP axexts_of_upd' ctxt)``
Overload conexts' = ``λctxt. FLAT (MAP conexts_of_upd' ctxt)``

Overload axioms_of_upd' = ``λupd. axexts_of_upd' upd ++ conexts_of_upd' upd``
Overload axiom_list' = ``λctxt. FLAT (MAP axioms_of_upd' ctxt)``
Overload axsof' = ``λctxt. set (axiom_list' ctxt)``

val _ = export_rewrites["types_of_upd'_def","consts_of_upd'_def","axexts_of_upd'_def"]

(* Now we can recover the entire e-theory record from a context *)
Overload ethyof = “(λ(ctxt:update' list). <| tms := tmsof ctxt;
                              tys := tysof ctxt;
                              etms := FEMPTY;
                              etys := FEMPTY;
                              axs := axsof' ctxt;
                              eaxs := {} |>):update' list -> ethy”

(* Principles for extending the context *)

val _ = Parse.add_infix("updates'",450,Parse.NONASSOC)

val _ = hide "abs";

Inductive updates':
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok' (ethyof ctxt) prop
   ⇒ (NewAxiom prop) updates' ctxt) ∧

  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates' ctxt) ∧

  (* new_specification *)
  ((ethyof ctxt, {}, MAP (λ(s,t). Var s (typeof t) === t) eqs) |-' prop ∧
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
  ((ethyof ctxt, {}, []) |-' Comb pred witness ∧
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
