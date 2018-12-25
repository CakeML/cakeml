(*
  Utility funcitons for manipulating AST values
*)
open preamble astTheory

val _ = new_theory "astUtils"

val _ = set_grammar_ancestry ["ast"]

val _ = temp_tight_equality()

val remove_lannots_def = tDefine "remove_lannots" ‘
  remove_lannots (App opn args) = App opn (MAP remove_lannots args) ∧
  remove_lannots (Con nm args) = Con nm (MAP remove_lannots args) ∧
  remove_lannots (Fun v body) = Fun v (remove_lannots body) ∧
  remove_lannots (Handle e handlers) =
    Handle (remove_lannots e) (MAP (λ(p,e). (p, remove_lannots e)) handlers) ∧
  remove_lannots (If gd th el) =
    If (remove_lannots gd) (remove_lannots th) (remove_lannots el) ∧
  remove_lannots (Lannot e _) = remove_lannots e ∧
  remove_lannots (Let vopt e1 e2) =
    Let vopt (remove_lannots e1) (remove_lannots e2) ∧
  remove_lannots (Letrec binds body) =
    Letrec (MAP (λ(s1,s2,e). (s1,s2,remove_lannots e)) binds)
           (remove_lannots body) ∧
  remove_lannots (Lit l) = Lit l ∧
  remove_lannots (Log lop e1 e2) =
    Log lop (remove_lannots e1) (remove_lannots e2) ∧
  remove_lannots (Mat gd binds) =
    Mat (remove_lannots gd) (MAP (λ(p,e). (p, remove_lannots e)) binds) ∧
  remove_lannots (Raise e) = Raise (remove_lannots e) ∧
  remove_lannots (Tannot e ty) = Tannot (remove_lannots e) ty ∧
  remove_lannots (Var v) = Var v
’ (WF_REL_TAC ‘measure exp_size’ >> simp[exp_size_def] >> rpt conj_tac
   >- (Induct_on ‘binds’ >> simp[exp_size_def, DISJ_IMP_THM, FORALL_AND_THM] >>
       rpt strip_tac >> res_tac >> pop_assum (qspec_then ‘body’ mp_tac) >>
       simp[])
   >- (Induct_on ‘handlers’ >> dsimp[exp_size_def] >> rw[] >> res_tac >>
       rename [‘exp_size E + 2’] >> pop_assum (qspec_then ‘E’ mp_tac) >>
       simp[])
   >- (Induct_on ‘binds’ >> dsimp[exp_size_def] >> rw[] >> res_tac >>
       rename [‘exp_size GD + 2’] >> pop_assum (qspec_then ‘GD’ mp_tac) >>
       simp[])
   >- (Induct_on ‘args’ >> dsimp[exp_size_def] >> rw[] >> res_tac >>
       rename [‘op_size OPN’] >> pop_assum (qspec_then ‘OPN’ mp_tac) >>
       DECIDE_TAC)
   >- (Induct_on ‘args’ >> dsimp[exp_size_def] >> rw[] >> res_tac >>
       rename [‘option_size _ NM’] >> pop_assum (qspec_then ‘NM’ mp_tac) >>
       DECIDE_TAC));

val remove_decl_lannots_def = tDefine "remove_decl_lannots" ‘
  remove_decl_lannots (Dexn l s tys) = Dexn l s tys ∧
  remove_decl_lannots (Dlet l p e) = Dlet l p (remove_lannots e) ∧
  remove_decl_lannots (Dletrec l binds) =
    Dletrec l (MAP (I ## I ## remove_lannots) binds) ∧
  remove_decl_lannots (Dlocal ds1 ds2) =
    Dlocal (MAP remove_decl_lannots ds1) (MAP remove_decl_lannots ds2) ∧
  remove_decl_lannots (Dmod snm ds) = Dmod snm (MAP remove_decl_lannots ds) ∧
  remove_decl_lannots (Dtype l tyi) = Dtype l tyi ∧
  remove_decl_lannots (Dtabbrev l vs opnm ty) = Dtabbrev l vs opnm ty
’ (WF_REL_TAC ‘measure dec_size’ >> rw[] >> rename [‘MEM _ xs’] >>
   Induct_on ‘xs’ >> dsimp[dec_size_def] >> rw[] >> res_tac >> simp[]);

val _ = export_theory();
