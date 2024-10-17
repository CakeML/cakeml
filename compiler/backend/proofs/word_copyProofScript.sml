(*
  Correctness proof for word_copy
*)
open preamble word_copyTheory wordPropsTheory wordSemTheory;

val _ = new_theory "word_copyProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_copy"];

Definition CPstate_inv_def:
  CPstate_inv cs = (
   (* cs.next is a fresh class *)
   (∀v c. lookup v cs.to_eq = SOME c ⇒ c < cs.next) ∧
   (∀c. c ∈ domain cs.from_eq ⇒ c < cs.next) ∧
   (* if representative of equiv class c is var v,
      then class of v is c *)
   (∀c v. lookup c cs.from_eq = SOME v ⇒
     lookup v cs.to_eq = SOME c)
  )
End
(* As a corollary, different classes have different representatives:
   (∀c c'. c < c' ⇒ c' < cs.next ⇒ lookup c cs.from_eq ≠ lookup c' cs.from_eq))
*)

Theorem empty_eq_inv:
  CPstate_inv empty_eq
Proof
  rw[CPstate_inv_def,empty_eq_def]
QED

Theorem remove_eq_inv:
  ∀cs v. CPstate_inv cs ⇒
  CPstate_inv (remove_eq cs v)
Proof
  rw[remove_eq_def]>>
  Cases_on‘lookup v cs.to_eq’>>
  rw[empty_eq_inv]
QED

Theorem remove_eqs_inv:
  ∀vv cs. CPstate_inv cs ⇒
    CPstate_inv (remove_eqs cs vv)
Proof
  Induct>>
  rw[remove_eqs_def,remove_eq_inv]
QED

Theorem set_eq_inv:
  CPstate_inv cs ∧
  lookup t cs.to_eq = NONE ⇒
  CPstate_inv (set_eq cs t s)
Proof
  rw[]>>
  ‘∀c. lookup c cs.from_eq ≠ SOME t’ by (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rw[set_eq_def]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>
  rw[]>>fs[]
  >~[`lookup s cs.to_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>simp[]
    >- (
      first_x_assum drule>>
      simp[])
    >- (
      first_x_assum drule>>
      simp[])
    >- metis_tac[NOT_SOME_NONE])
  >~[`lookup c_s cs.from_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>simp[]
    >- (
      first_x_assum drule>>
      simp[])
    >- (
      first_x_assum drule>>
      simp[])
    >-
      metis_tac[SOME_11,NOT_SOME_NONE])
  >~[`lookup s cs.to_eq = SOME c_s`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[])
QED

(*
Theorem set_eq_inv:
  ∀cs t s.
    CPstate_inv cs ∧
    lookup t cs.to_eq = NONE ⇒
    CPstate_inv (set_eq cs t s)
Proof
  rpt strip_tac>>
  ‘∀c. c<cs.next ⇒ lookup c cs.from_eq ≠ SOME t’ by (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rw[set_eq_def]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>
  fs[]
  >~[`lookup s cs.to_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]
    >- (
      first_x_assum drule>>
      simp[])>>
    ‘c<cs.next’ by decide_tac>>
    metis_tac[NOT_NONE_SOME])
  >~[`lookup s cs.to_eq = SOME c_s`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[])
QED
*)

Theorem merge_eqs_inv:
  CPstate_inv cs1 ∧
  CPstate_inv cs2 ⇒
  CPstate_inv (merge_eqs cs1 cs2)
Proof
  rw[]>>
  simp[merge_eqs_def,CPstate_inv_def]>>
  CONJ_TAC >- (
    (* invariant 1 works *)
    rw[lookup_inter_eq]>>gvs[AllCaseEqs()]>>
    metis_tac[CPstate_inv_def] ) >>
  CONJ_TAC >- (
    (* invariant 2 works *)
    simp[domain_lookup,lookup_inter_eq,AllCaseEqs()]>>
    rw[]>>metis_tac[CPstate_inv_def]
  )>>
  rw[lookup_inter_eq,AllCaseEqs()]>>
  metis_tac[CPstate_inv_def]
QED

(* XXX: get rid of this *)
Theorem same_classD_old:
  CPstate_inv cs ∧
  lookup_eq cs x = lookup_eq cs y ⇒
  x = y ∨
  (∃c.
    lookup x cs.to_eq = SOME c ∧
    lookup y cs.to_eq = SOME c)
Proof
  rw[lookup_eq_def,AllCaseEqs()]
  >- (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])
  >- (
    fs[CPstate_inv_def]>>
    first_x_assum drule>>
    rw[])>>
  Cases_on`lookup y cs.to_eq`>>gvs[]
  >- (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rename1`lookup y _ = SOME cy`>>
  Cases_on`lookup cy cs.from_eq`>>gvs[]
  >- (
    fs[CPstate_inv_def]>>
    first_x_assum drule>>
    rw[])>>
  fs[CPstate_inv_def]>>
  metis_tac[SOME_11]
QED

Theorem same_classD:
  CPstate_inv cs ∧
  lookup_eq cs x = lookup_eq cs y ⇒
  x = y ∨ (x ≠ y ∧
  ∃c rep.
    lookup x cs.to_eq = SOME c ∧
    lookup y cs.to_eq = SOME c ∧
    lookup c cs.from_eq = SOME rep)
Proof
  rw[]>>
  Cases_on‘x=y’>-(DISJ1_TAC>>pop_assum ACCEPT_TAC)>>
  DISJ2_TAC>>
  CONJ_TAC>-pop_assum ACCEPT_TAC>>
  drule_all same_classD_old>>
  rw[]>>
  qexists_tac‘c’>>
  gvs[lookup_eq_def]>>
  Cases_on‘lookup c cs.from_eq’>>gvs[]
QED

Theorem lookup_eqI:
  ∀cs r v.
  (r=v ∧ lookup v cs.to_eq = NONE) ∨ (∃c. lookup v cs.to_eq = SOME c ∧ lookup c cs.from_eq = SOME r) ⇒
  lookup_eq cs v = r
Proof
  rw[lookup_eq_def]>>every_case_tac>>rw[]
QED

Definition both_alloc_vars_def:
  both_alloc_vars (t,s) = (is_alloc_var t ∧ is_alloc_var s)
End

Theorem lookup_eq_set_eq_not_alloc_var:
  ¬ both_alloc_vars (t,s) ⇒
  lookup_eq (set_eq cs t s) v =
  lookup_eq cs v
Proof
  rw[set_eq_def,both_alloc_vars_def]
QED

(* t := s *)
Theorem lookup_eq_set_eq_is_alloc_var1:
  CPstate_inv cs ∧
  both_alloc_vars (t,s) ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq cs s = lookup_eq cs v ⇒
  lookup_eq (set_eq cs t s) v = t
Proof
  rw[both_alloc_vars_def]>>
  drule_all same_classD>>
  rw[]
  >- (
    simp[lookup_eq_def,set_eq_def]>>
    Cases_on‘lookup s cs.to_eq’>>rw[lookup_insert])
  >- (
    irule lookup_eqI>>
    rw[set_eq_def,lookup_insert]>>
    rw[]>>
    `F` by gvs[CPstate_inv_def,lookup_eq_def])
QED

Theorem lookup_eq_set_eq_is_alloc_var2:
  CPstate_inv cs ∧
  both_alloc_vars (t,s) ⇒
  lookup t cs.to_eq = NONE ⇒
  v ≠ t ⇒
  lookup_eq cs s ≠ lookup_eq cs v ⇒
  lookup_eq (set_eq cs t s) v = lookup_eq cs v
Proof
  rw[set_eq_def,CPstate_inv_def,both_alloc_vars_def]>>
  ‘v≠s’by metis_tac[]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>simp[lookup_eq_def,set_eq_def,lookup_insert]
  >-(
    namedCases_on‘lookup v cs.to_eq’["","c"]>>simp[]>>
    ‘c<cs.next’by metis_tac[]>>simp[]
  )
  >-(
    namedCases_on‘lookup c_s cs.from_eq’["","s_rep"]>>namedCases_on‘lookup v cs.to_eq’["","c"]>>simp[lookup_insert]
    >-(
      Cases_on‘c=cs.next’>>simp[]
      >-(‘c<cs.next’by metis_tac[]>>decide_tac)
    )
    >-(Cases_on‘c=c_s’>>simp[]>>gvs[lookup_eq_def])
  )
QED

Theorem lookup_eq_set_eq_t:
  CPstate_inv cs ∧
  both_alloc_vars (t,s) ⇒
  lookup_eq (set_eq cs t s) t = t
Proof
  simp[lookup_eq_def,set_eq_def,both_alloc_vars_def]>>
  every_case_tac>>gvs[lookup_insert]
QED

Theorem lookup_eq_set_eq_s:
  CPstate_inv cs ∧
  both_alloc_vars (t,s) ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq (set_eq cs t s) s = t
Proof
  Cases_on‘s=t’>-rw[lookup_eq_set_eq_t]>-rw[lookup_eq_set_eq_is_alloc_var1]
QED

Theorem lookup_eq_set_eqD:
  CPstate_inv cs ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq (set_eq cs t s) v = r ⇒
  (r=t ⇒ v=t ∨ lookup_eq cs v = lookup_eq cs s) ∧
  (r≠t ⇒ r = lookup_eq cs v)
Proof
  Cases_on‘both_alloc_vars (t,s)’
  >-(
    rpt strip_tac
    >-(
      Cases_on‘v=t’>-decide_tac
      >-(
        DISJ2_TAC>>
        CCONTR_TAC>>
        ‘t = lookup_eq cs v’
          by metis_tac[lookup_eq_set_eq_is_alloc_var2]>>
        (* t = lookup_eq cs v, v≠t, hence lookup t cs.eq ≠ NONE *)
        pop_assum mp_tac>>
        simp[lookup_eq_def]>>every_case_tac>>
        metis_tac[CPstate_inv_def,NOT_NONE_SOME]
      )
    )
    >-metis_tac[lookup_eq_set_eq_t,lookup_eq_set_eq_is_alloc_var1,lookup_eq_set_eq_is_alloc_var2]
  )
  >-(
    ‘lookup_eq (set_eq cs t s) v = lookup_eq cs v’
      by metis_tac[lookup_eq_set_eq_not_alloc_var]>>
    rw[]>>
    DISJ1_TAC>>
    fs[CPstate_inv_def,lookup_eq_def]>>
    every_case_tac>>
    metis_tac[NOT_NONE_SOME]
  )
QED

Definition CPstate_models_def:
  CPstate_models cs S ⇔ ∀v c vrep.
    lookup v cs.to_eq = SOME c ⇒
    lookup c cs.from_eq = SOME vrep ⇒
    lookup v S.locals = lookup vrep S.locals
End

Theorem CPstate_model:
  CPstate_models cs st ⇒
  lookup v st.locals = lookup (lookup_eq cs v) st.locals
Proof
  rw[CPstate_models_def,lookup_eq_def]>>every_case_tac>>rw[]
QED

Theorem CPstate_modelsI:
  CPstate_inv cs ⇒
  (∀x y. lookup_eq cs x = lookup_eq cs y ⇒ lookup x st.locals = lookup y st.locals) ⇒
  CPstate_models cs st
Proof
  rw[CPstate_inv_def,CPstate_models_def]>>
  qpat_x_assum‘∀x y. _ ⇒ lookup x st.locals = lookup y st.locals’irule>>
  rw[lookup_eq_def]>>TOP_CASE_TAC>>TOP_CASE_TAC>>
  metis_tac[domain_lookup,NOT_NONE_SOME,SOME_11]
QED

Theorem CPstate_modelsD:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  ∀x y. lookup_eq cs x = lookup_eq cs y ⇒ lookup x st.locals = lookup y st.locals
Proof
  rw[CPstate_models_def]>>metis_tac[same_classD]
QED

Theorem remove_eq_model:
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) st
Proof
  rw[remove_eq_def]>>
  TOP_CASE_TAC>>rw[empty_eq_def,CPstate_models_def]
QED

Theorem remove_eq_model_insert':
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  (st':('a,'b,'c)wordSem$state).locals = insert t val (st:('a,'b,'c)wordSem$state).locals ⇒
  CPstate_models (remove_eq cs t) st'
Proof
  rw[remove_eq_def]>>
  TOP_CASE_TAC>>rw[empty_eq_def,CPstate_models_def]>>
  rw[lookup_insert]>-metis_tac[NOT_NONE_SOME]>-(
    fs[CPstate_inv_def]>>metis_tac[NOT_NONE_SOME]
  )>>
  ‘lookup_eq cs v = lookup_eq cs vrep’ by (
    rw[lookup_eq_def]>>TOP_CASE_TAC>>TOP_CASE_TAC>>
    metis_tac[CPstate_inv_def,SOME_11]
  )>>
  metis_tac[CPstate_modelsD]
QED
(*
Theorem remove_eq_model_insert'1:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  st' = st with locals := insert t val st.locals ⇒
  CPstate_models (remove_eq cs t) st'
Proof
  rw[]
  >>irule remove_eq_model_insert'
  >>rw[]>>metis_tac[]
QED
*)

Theorem remove_eq_model_insert:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) (st with locals := insert t val st.locals)
Proof
  rw[]
  >>irule remove_eq_model_insert'
  >>rw[]
  >>metis_tac[]
QED

Theorem remove_eq_model_set_var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) (set_var t val st)
Proof
  rw[set_var_def]
  >>irule remove_eq_model_insert'
  >>rw[]
  >>metis_tac[]
QED

Theorem CPstate_models_same_locals:
  CPstate_models cs st ⇒
  st'.locals = st.locals ⇒
  CPstate_models cs st'
Proof
  rw[CPstate_models_def]
QED

Theorem set_fp_var_model:
  CPstate_models cs st ⇒
  CPstate_models cs (set_fp_var t val st)
Proof
  DISCH_TAC
  >>irule CPstate_models_same_locals
  >>rw[set_fp_var_def]
  >>metis_tac[]
QED

Theorem memory_model:
  CPstate_models cs st ⇒
  CPstate_models cs (st with memory := m)
Proof
  DISCH_TAC
  >>irule CPstate_models_same_locals
  >>rw[]>>metis_tac[]
QED

Theorem lookup_eq_remove_eq_t:
  CPstate_inv cs ⇒
  lookup_eq (remove_eq cs t) x = t ⇒ x=t
Proof
  rw[remove_eq_def,lookup_eq_def]>>
  Cases_on‘lookup t cs.to_eq’>>fs[empty_eq_def]>>
  namedCases_on‘lookup x cs.to_eq’["","c"]>>
  namedCases_on‘lookup c cs.from_eq’["","c_rep"]>>gvs[]>>
  metis_tac[CPstate_inv_def,NOT_NONE_SOME]
QED

Theorem copy_prop_move_model_aux:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  both_alloc_vars (t,s) ⇒
  lookup s st.locals = SOME sval ⇒
  CPstate_inv (set_eq (remove_eq cs t) t s) ∧
  CPstate_models (set_eq (remove_eq cs t) t s) (st with locals := insert t sval st.locals)
Proof
  rpt DISCH_TAC>>
  ‘CPstate_inv (remove_eq cs t)’ by metis_tac[remove_eq_inv]>>
  ‘CPstate_inv (set_eq (remove_eq cs t) t s)’
  by (
    irule set_eq_inv>>
    rw[remove_eq_def]>>
    TOP_CASE_TAC>>rw[empty_eq_def]
  )>>
  CONJ_TAC>-pop_assum ACCEPT_TAC>>
  (* CPstate_inv was easy. Now prove CPstate_models *)
  irule CPstate_modelsI>>
  rw[]>>
  ‘lookup t (remove_eq cs t).to_eq = NONE’ by (
    rw[remove_eq_def]>>
    Cases_on‘lookup t cs.to_eq’>>rw[empty_eq_def]
  )>>
  Cases_on‘t=x∧t=y’>-rw[lookup_eq_set_eq_t,lookup_insert]>>
  Cases_on‘t≠x∧t≠y’>-(
    qpat_x_assum‘¬(t=x∧t=y)’kall_tac>>
    rw[lookup_insert]>>
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) x’>>
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’>>
    metis_tac[lookup_eq_set_eq_is_alloc_var1,lookup_eq_set_eq_is_alloc_var2,
      lookup_eq_set_eqD,remove_eq_model,CPstate_modelsD]
  )>>
  wlog_tac‘t=x∧t≠y’[‘x’,‘y’]>-metis_tac[]>>
  rw[lookup_eq_set_eq_t]>-(
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’
    >-(
      rw[lookup_insert]>>
      metis_tac[lookup_eq_set_eq_is_alloc_var1,remove_eq_model,CPstate_modelsD]
    )
    >-(
      rw[lookup_insert]>>
      gvs[lookup_eq_set_eq_t]>>
      metis_tac[lookup_eq_set_eq_is_alloc_var2,lookup_eq_remove_eq_t]
    )
  )
QED

(*
theorem copy_prop_prog_correct:
  assumes cs: "CPstate_inv cs" "CPstate_models cs st"
  shows
    "exec_prog (fst (copy_prop_prog p cs)) st = exec_prog p st ∧
     CPstate_inv (snd (copy_prop_prog p cs)) ∧
     CPstate_models (snd (copy_prop_prog p cs)) (exec_prog p st)"
*)

Theorem lookup_eq_idempotent:
  CPstate_inv cs ⇒
  lookup_eq cs (lookup_eq cs x) = lookup_eq cs x
Proof
  rw[CPstate_inv_def]>>
  ‘∀rep. rep = lookup_eq cs x ⇒ lookup_eq cs rep = rep’ suffices_by metis_tac[]>>
  rw[lookup_eq_def]>>
  every_case_tac>>metis_tac[CPstate_inv_def,NOT_NONE_SOME,SOME_11]
QED

Theorem CPstate_modelsD_get_var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  get_var (lookup_eq cs x) st = get_var x st
Proof
  rw[get_var_def]>>
  metis_tac[CPstate_modelsD,lookup_eq_idempotent]
QED

Theorem CPstate_modelsD_Var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  word_exp st (Var (lookup_eq cs x)) = word_exp st (Var x)
Proof
  rw[word_exp_def]>>
  metis_tac[CPstate_modelsD,lookup_eq_idempotent]
QED

Theorem CPstate_modelsD_lookup_eq_imm:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  word_exp st (case lookup_eq_imm cs x of Reg r => Var r | Imm w => Const w) =
  word_exp st (case x of Reg r => Var r | Imm w => Const w)
Proof
  Cases_on‘x’>>
  rw[lookup_eq_imm_def,word_exp_def]>>
  metis_tac[CPstate_modelsD,lookup_eq_idempotent]
QED

Theorem MAP_get_var_eqD:
  MAP (λx. get_var x st) xx = MAP (λx. get_var x st) yy ⇒
  get_vars xx st = get_vars yy st
Proof
  qid_spec_tac‘yy’>>
  Induct_on‘xx’>>rw[]>>
  Cases_on‘yy’>-fs[]>>
  rename[‘get_vars (x::xx) st = get_vars (y::yy) st’]>>
  ‘get_var x st = get_var y st’ by fs[]>>
  ‘get_vars xx st = get_vars yy st’ by (first_assum irule>>fs[])>>
  rw[get_vars_def]
QED

Theorem copy_prop_move_eval_aux1:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  ∀moves' cs'.
  copy_prop_move moves cs = (moves', cs') ⇒
  MAP (λx. get_var x st) (MAP SND moves') = MAP (λx. get_var x st) (MAP SND moves)
Proof
  Induct_on‘moves’>>rw[copy_prop_move_def](* NIL case solved *)>>
  (* CONS case *)
  pop_assum mp_tac>>
  namedCases_on‘h’["t s"]>>
  rw[evaluate_def,copy_prop_move_def]>>
  pairarg_tac>>
  gvs[]>>
  simp[get_var_def]>>
  ‘lookup_eq cs (lookup_eq cs s) = lookup_eq cs s’
    by metis_tac[lookup_eq_idempotent]>>
  metis_tac[CPstate_modelsD]
QED

Theorem copy_prop_move_eval_aux2:
  MAP FST moves1 = MAP FST moves2 ⇒
  get_vars (MAP SND moves1) st = get_vars (MAP SND moves2) st ⇒
  evaluate (Move pri moves1, st) = evaluate (Move pri moves2, st)
Proof
  rw[evaluate_def]
QED

Theorem copy_prop_move_eval_aux3:
  ∀moves' cs'.
  copy_prop_move moves cs = (moves', cs') ⇒
  MAP FST moves' = MAP FST moves
Proof
  Induct_on‘moves’>>rw[copy_prop_move_def]>>
  namedCases_on‘h’["t s"]>>
  Cases_on‘moves'’>>(
    fs[copy_prop_move_def]>>
    pairarg_tac>>gvs[]
  )
QED

Theorem copy_prop_move_eval:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  copy_prop_move moves cs = (moves', cs') ⇒
  evaluate (Move pri moves, st) = (err, st') ⇒
  evaluate (Move pri moves', st) = (err, st')
Proof
  rpt strip_tac
  >>drule_then assume_tac copy_prop_move_eval_aux3
  >>drule_all_then assume_tac copy_prop_move_eval_aux1
  >>dxrule_then assume_tac MAP_get_var_eqD
  >>metis_tac[copy_prop_move_eval_aux2]
QED

Theorem lookup_alist_insert_same:
  s ∉ set tt ⇒
  lookup s (alist_insert tt values locals) = lookup s locals
Proof
  qid_spec_tac‘values’>>Induct_on‘tt’>-rw[alist_insert_def]>>
  Cases_on‘values’>>rw[alist_insert_def,lookup_insert]
QED

Theorem copy_prop_move_inv:
  CPstate_inv cs ⇒
  copy_prop_move moves cs = (moves', cs') ⇒
  CPstate_inv cs'
Proof
  qid_spec_tac‘cs'’>>qid_spec_tac‘moves'’>>
  Induct_on‘moves’>>fs[copy_prop_move_def]>>
  rw[]>>
  PairCases_on‘h’>>
  fs[copy_prop_move_def]>>
  pairarg_tac>>gvs[]>>
  irule set_eq_inv>>
  conj_tac>-metis_tac[remove_eq_inv]>>
  rw[remove_eq_def]>>TOP_CASE_TAC>>rw[empty_eq_def]
QED

Theorem copy_prop_inst_inv:
  CPstate_inv cs ⇒
  copy_prop_inst ins cs = (prog', cs') ⇒
  CPstate_inv cs'
Proof
  ‘∀ins cs prog' cs'.
   CPstate_inv cs ⇒
   copy_prop_inst ins cs = (prog', cs') ⇒
   CPstate_inv cs'’ suffices_by metis_tac[]
  >>ho_match_mp_tac copy_prop_inst_ind
  >>rw[copy_prop_inst_def]>>metis_tac[remove_eq_inv,remove_eqs_inv]
QED

Theorem copy_prop_prog_inv:
  CPstate_inv cs ⇒
  copy_prop_prog prog cs = (prog', cs') ⇒
  CPstate_inv cs'
Proof
  ‘∀prog cs prog' cs'.
   CPstate_inv cs ⇒
   copy_prop_prog prog cs = (prog', cs') ⇒
   CPstate_inv cs'’ suffices_by metis_tac[]
  >>ho_match_mp_tac copy_prop_prog_ind
  >>rw[copy_prop_prog_def]>>rpt(pairarg_tac>>fs[])>>TRY(metis_tac[empty_eq_inv,remove_eq_inv,remove_eqs_inv])
  >-metis_tac[copy_prop_move_inv]
  >-metis_tac[copy_prop_inst_inv]
  >-metis_tac[merge_eqs_inv]
  >-(Cases_on‘exp’>>fs[])
QED

Theorem get_vars_LENGTH:
  get_vars xx st = SOME values ⇒ LENGTH values = LENGTH xx
Proof
  qid_spec_tac‘values’>>Induct_on‘xx’>>rw[get_vars_def]>>
  Cases_on‘get_var h st’>>fs[]>>
  Cases_on‘get_vars xx st’>>fs[]>>
  rw[]
QED

(* unused *)
(*
Theorem lookup_alist_insert_same:
  ¬MEM k kk ⇒
  LENGTH vv = LENGTH kk ⇒
  lookup k (alist_insert kk vv m) = lookup k m
Proof
  qid_spec_tac‘vv’>>
  Induct_on‘kk’>-rw[alist_insert_def]>>
  Cases_on‘vv’>>rw[alist_insert_def,lookup_insert]
QED
*)

Theorem empty_eq_model:
  CPstate_models empty_eq st
Proof
  rw[CPstate_models_def,empty_eq_def]
QED

Theorem copy_prop_move_model:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  set (MAP FST moves) ∩ set (MAP SND moves) = ∅ ⇒
  copy_prop_move moves cs = (moves',cs') ⇒
  get_vars (MAP SND moves) st = SOME values ⇒
  CPstate_models cs' (set_vars (MAP FST moves) values st)
Proof
  qid_spec_tac‘moves'’>>qid_spec_tac‘cs'’>>qid_spec_tac‘values’>>
  Induct_on‘moves’>-(
    rw[set_vars_def,alist_insert_def]>>
    fs[copy_prop_move_def]>>
    ‘st with locals := st.locals = st’ by simp[state_component_equality]>>
    fs[]
  )
  >-(
    namedCases_on‘values’["","val values"]>-(
      simp[]>>metis_tac[get_vars_LENGTH,LENGTH_MAP,LENGTH,SUC_NOT]
    )>>
    fs[set_vars_def]>>
    rw[alist_insert_def]>>
    rename[‘copy_prop_move (m::moves) cs = _’]>>
    namedCases_on‘m’["t s"]>>
    ‘moves' = (t, lookup_eq cs s) :: FST (copy_prop_move moves cs) ∧
     cs' = set_eq (remove_eq (SND (copy_prop_move moves cs)) t) t s’
      by (fs[copy_prop_move_def]>>pairarg_tac>>gvs[])>>
    qpat_x_assum‘copy_prop_move (m::moves) cs = _’kall_tac>>
    ‘get_var s st = SOME val ∧ get_vars (MAP SND moves) st = SOME values'’
      by (Cases_on‘get_var s st’>>Cases_on‘get_vars (MAP SND moves) st’>>fs[get_vars_def])>>
    qpat_x_assum‘get_vars (_::_) _ = _’kall_tac>>
    ‘CPstate_models (SND (copy_prop_move moves cs)) (st with locals := alist_insert (MAP FST moves) values' st.locals)’ by (
      ‘set (MAP FST moves) ∩ set (MAP SND moves) = {}’
        by (qpat_x_assum‘_∩_={}’mp_tac>>simp[]>>SET_TAC[])>>
      metis_tac[PAIR]
    )>>
    simp[]>>
    Cases_on‘both_alloc_vars (t,s)’>~[‘¬both_alloc_vars (t,s)’]>-(
      fs[both_alloc_vars_def]>>
      simp[set_eq_def]>>
      ‘CPstate_models (remove_eq (SND (copy_prop_move moves cs)) t)
          ((st with locals := alist_insert (MAP FST moves) values' st.locals) with
           locals :=
             insert t val (st with locals := alist_insert (MAP FST moves) values' st.locals).locals)’ suffices_by simp[state_fupdfupds]>>
      irule remove_eq_model_insert>>
      metis_tac[copy_prop_move_inv,PAIR]
    )
    >-(
      ‘CPstate_models (set_eq (remove_eq (SND (copy_prop_move moves cs)) t) t s)
          ((st with locals := alist_insert (MAP FST moves) values' st.locals) with
           locals :=
             insert t val (st with locals := alist_insert (MAP FST moves) values' st.locals).locals)’ suffices_by simp[state_fupdfupds]>>
   ‘lookup s (st with locals := alist_insert (MAP FST moves) values' st.locals).locals = SOME val’ by (
        ‘¬MEM s (MAP FST moves)’ by (qpat_x_assum‘_∩_={}’mp_tac>>simp[]>>SET_TAC[])>>
        simp[lookup_alist_insert_same]
        >-fs[get_var_def]
      )>>
      metis_tac[copy_prop_move_model_aux,copy_prop_move_inv,PAIR]
    )
  )
QED

(*
Theorem copy_prop_move_correct_aux4:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  set (MAP FST moves) ∩ set (MAP SND moves) = {} ⇒
  copy_prop_move moves cs = (moves', cs') ⇒
  FST (evaluate (Move pri moves, st)) = NONE ⇒
  CPstate_inv cs' ∧ CPstate_models cs' (SND (evaluate (Move pri moves, st)))
Proof
  Cases_on‘get_vars (MAP SND moves) st’>>rw[evaluate_def]>>fs[]
  >-metis_tac[copy_prop_move_inv]
  >-metis_tac[copy_prop_move_model]
QED
*)

Theorem EVERY_NOT_MEM_D:
  EVERY (λt. ¬MEM t ss) tt ⇒ set tt ∩ set ss = {}
Proof
  Induct_on‘tt’>>rw[INSERT_INTER]
QED

Theorem copy_prop_move_correct:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  copy_prop_prog (Move pri moves) cs = (prog', cs') ⇒
  evaluate (Move pri moves, st) = (err, st') ⇒
  evaluate (prog', st) = (err, st') ∧
  (err = NONE ⇒ CPstate_inv cs' ∧ CPstate_models cs' st')
Proof
  Cases_on‘ALL_DISTINCT (MAP FST moves)’
  >-(
    rw[copy_prop_prog_def]
    >-(
      pairarg_tac>>fs[]
      >>metis_tac[copy_prop_move_eval]
    )
    >-(
      pairarg_tac>>fs[]
      >>metis_tac[copy_prop_move_inv]
    )
    >-(
      pairarg_tac>>fs[]
      >>qpat_x_assum‘evaluate _ = _’mp_tac>>simp[evaluate_def]
      >>every_case_tac
      >>dxrule EVERY_NOT_MEM_D
      >>metis_tac[copy_prop_move_model]
    )
    >-irule empty_eq_inv
    >-irule empty_eq_model
  )
  >-(
    Cases_on‘EVERY (λt. ¬MEM t (MAP SND moves)) (MAP FST moves)’
    >>simp[copy_prop_prog_def]
    >>rpt disch_tac
    >-(
      pairarg_tac>>fs[]
      >>conj_tac
      >-metis_tac[copy_prop_move_eval]
      >-gvs[evaluate_def]
    )
    >-gvs[evaluate_def]
  )
QED

Theorem word_exp_cong_Var:
  get_var x' st = get_var x st ⇒
  word_exp st (Var x') = word_exp st (Var x)
Proof
  rw[word_exp_def,get_var_def]
QED

Theorem word_exp_cong_Load:
  word_exp st addr' = word_exp st addr ⇒
  word_exp st (Load addr') = word_exp st (Load addr)
Proof
  rw[word_exp_def]
QED

Theorem word_exp_cong_Op:
  MAP (word_exp st) aa' = MAP (word_exp st) aa ⇒
  word_exp st (Op op aa') = word_exp st (Op op aa)
Proof
  qid_spec_tac‘aa'’>>Induct_on‘aa’>>rw[word_exp_def,the_words_def]>>
  Cases_on‘aa'’>>gvs[]>>
  rw[the_words_def]>>
  every_case_tac>>gvs[SF ETA_ss]
QED

Theorem word_exp_cong_Shift:
  word_exp st e' = word_exp st e ⇒
  word_exp st (Shift sh e' n) = word_exp st (Shift sh e n)
Proof
  rw[word_exp_def]
QED

(* "inst" is constant wordSem$inst *)
Theorem copy_prop_inst_eval:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  (prog', cs') = copy_prop_inst ins cs ⇒
  evaluate (prog', st) = evaluate (Inst ins, st)
Proof
  qid_spec_tac‘prog'’>>qid_spec_tac‘cs'’
  >>Cases_on‘ins’>>rw[]
  >-(
    (* Skip *)
    fs[evaluate_def,inst_def,copy_prop_inst_def]
  )
  >-(
    (* Const *)
    fs[evaluate_def,inst_def,copy_prop_inst_def]
  )
  >-(
    (* Arith *)
    Cases_on‘a’>>fs[evaluate_def,inst_def,copy_prop_inst_def]
    (* 7 subgoals *)
    >-(
      rw[assign_def]>>
(* Slow.
      metis_tac[CPstate_modelsD_Var,CPstate_modelsD_lookup_eq_imm,word_exp_cong_Op,MAP]
*)
      ‘word_exp st (Op b
         [Var (lookup_eq cs n0);
          case lookup_eq_imm cs r of
            Reg r3 => Var r3
          | Imm w => Const w]) =
       word_exp st (Op b
         [Var n0; case r of Reg r3 => Var r3 | Imm w => Const w])’
        suffices_by simp[]>>
      irule word_exp_cong_Op>>
      simp[]>>
      metis_tac[CPstate_modelsD_Var,CPstate_modelsD_lookup_eq_imm]
    )
    >-(
      rw[assign_def]>>
      metis_tac[CPstate_modelsD_Var,word_exp_cong_Shift]
    )
    >-(
      ‘get_vars [lookup_eq cs n1; lookup_eq cs n0] st = get_vars [n1; n0] st’ suffices_by simp[]>>
      irule MAP_get_var_eqD>>
      simp[]>>
      metis_tac[CPstate_modelsD_get_var]
    )
    >-(
      ‘get_vars [lookup_eq cs n1; lookup_eq cs n2; lookup_eq cs n3] st =
       get_vars [n1; n2; n3] st’ suffices_by simp[]>>
      irule MAP_get_var_eqD>>
      simp[]>>
      metis_tac[CPstate_modelsD_get_var]
    )
    >-(
      ‘get_vars [lookup_eq cs n0; lookup_eq cs n1; n2] st =
       get_vars [n0; n1; n2] st’ suffices_by simp[]>>
      irule MAP_get_var_eqD>>
      simp[]>>
      metis_tac[CPstate_modelsD_get_var]
    )
    >-(
      ‘get_vars [lookup_eq cs n0; lookup_eq cs n1] st =
       get_vars [n0; n1] st’ suffices_by simp[]>>
      irule MAP_get_var_eqD>>
      simp[]>>
      metis_tac[CPstate_modelsD_get_var]
    )
    >-(
      ‘get_vars [lookup_eq cs n0; lookup_eq cs n1] st =
       get_vars [n0; n1] st’ suffices_by simp[]>>
      irule MAP_get_var_eqD>>
      simp[]>>
      metis_tac[CPstate_modelsD_get_var]
    )
  )
  >-(
    (* Mem *)
    Cases_on‘a’>>Cases_on‘m’>>
    fs[evaluate_def,inst_def,copy_prop_inst_def]
    >-(
      ‘word_exp st (Op Add [Var (lookup_eq cs n'); Const c]) =
       word_exp st (Op Add [Var n'; Const c])’ suffices_by simp[]>>
      irule word_exp_cong_Op>>
      simp[]>>
      metis_tac[CPstate_modelsD_Var]
    )
    >-(
      ‘word_exp st (Op Add [Var (lookup_eq cs n'); Const c]) =
       word_exp st (Op Add [Var n'; Const c])’ suffices_by simp[]>>
      irule word_exp_cong_Op>>
      simp[]>>
      metis_tac[CPstate_modelsD_Var]
    )
    >-(
      ‘get_var (lookup_eq cs n) st = get_var n st’
        by metis_tac[CPstate_modelsD_get_var]>>
      ‘word_exp st (Op Add [Var (lookup_eq cs n'); Const c]) =
       word_exp st (Op Add [Var n'; Const c])’ suffices_by simp[]>>
      irule word_exp_cong_Op>>
      simp[]>>
      metis_tac[CPstate_modelsD_Var]
    )
    >-(
      ‘get_var (lookup_eq cs n) st = get_var n st’
        by metis_tac[CPstate_modelsD_get_var]>>
      ‘word_exp st (Op Add [Var (lookup_eq cs n'); Const c]) =
       word_exp st (Op Add [Var n'; Const c])’ suffices_by simp[]>>
      irule word_exp_cong_Op>>
      simp[]>>
      metis_tac[CPstate_modelsD_Var]
    )
  )
  >-(
    (* FP *)
    Cases_on‘f’>>fs[evaluate_def,inst_def,copy_prop_inst_def]>>
    drule_all CPstate_modelsD_get_var>>rw[]
  )
QED

Theorem remove_eq_comm:
  remove_eq (remove_eq cs x) y = remove_eq (remove_eq cs y) x
Proof
  rw[remove_eq_def]>>every_case_tac
QED

Theorem copy_prop_inst_correct:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  (prog', cs') = copy_prop_inst ins cs ⇒
  evaluate (Inst ins, st) = (err, st') ⇒
  evaluate (prog', st) = (err, st') ∧
  (err = NONE ⇒ CPstate_inv cs' ∧ CPstate_models cs' st')
Proof
  rw[]
  >-metis_tac[copy_prop_inst_eval]
  >-metis_tac[copy_prop_inst_inv]
  >-(
    (* CPstate_models *)
    Cases_on‘ins’>>fs[copy_prop_inst_def,evaluate_def,inst_def,assign_def]
    >-(
      (* Const *)
      every_case_tac
      >>fs[copy_prop_inst_def]
      >>metis_tac[remove_eq_model_set_var]
    )
    >-(
      (* Arith *)
      full_case_tac
      >~[‘LongDiv’]
      >-(
        every_case_tac
        >>fs[copy_prop_inst_def,remove_eqs_def]
        >>rw[Once remove_eq_comm]
        >>metis_tac[remove_eq_inv,remove_eq_model_set_var]
      )
      >>every_case_tac
      >>fs[copy_prop_inst_def,remove_eqs_def]
      >>metis_tac[remove_eq_inv,remove_eq_model_set_var]
    )
    >-(
      (* Mem *)
      every_case_tac
      >>fs[copy_prop_inst_def,mem_store_def,mem_store_byte_aux_def]
      >>metis_tac[remove_eq_model_set_var,memory_model]
    )
    >-(
      (* FP *)
      every_case_tac
      >>fs[copy_prop_inst_def,remove_eqs_def]
      >>metis_tac[remove_eq_inv,remove_eq_model_set_var,remove_eq_model,set_fp_var_model]
    )
  )
QED



Theorem copy_prop_correct:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  (prog', cs') = copy_prop_prog prog cs ⇒
  CPstate_inv cs' ∧
  CPstate_models cs' (SND (evaluate (prog, st))) ∧
  evaluate (prog', st) = evaluate (prog, st)
Proof
  qid_spec_tac‘cs’>>qid_spec_tac‘st’>>
  qid_spec_tac‘prog'’>>qid_spec_tac‘prog’>>
  Induct (* 23 subgoals *)
  >-rw[evaluate_def,copy_prop_prog_def]
  >-(
    qx_gen_tac‘pri’>>qx_gen_tac‘moves’>>rw[]
    >-cheat(*inv*)
    >-(
      fs[copy_prop_prog_def]>>
      pairarg_tac>>gvs[]>>
      rename[‘_=(moves',cs')’]>>
      rw[evaluate_def]
    )
    >-(
      fs[copy_prop_prog_def]>>
      pairarg_tac>>gvs[]>>
      metis_tac[copy_prop_move_correct]
    )
  )
QED

(* TODO: insert an induction over copy_prop_prog *)

(* Main semantics result *)
Theorem evaluate_copy_prop:
  evaluate (copy_prop e, s) = evaluate (e, s)
Proof
  cheat
QED

(* Bunch of syntactic results for integration into compiler *)

(* Leave these things for now *)

val _ = export_theory();
