(*
  Correctness proof for word_copy
*)
Theory word_copyProof
Libs
  preamble
Ancestors
  wordLang[qualified] wordSem wordProps word_copy wordConvs

val s = ``s:('a,'c,'ffi) wordSem$state``

Definition CPstate_inv_def:
  CPstate_inv cs = (
   (* cs.next is a fresh class *)
   (∀v c. lookup v cs.to_eq = SOME c ⇒ c < cs.next) ∧
   (∀c. c ∈ domain cs.from_eq ⇒ c < cs.next) ∧
   (∀s c. ALOOKUP cs.store_to_eq s = SOME c ⇒ c < cs.next) ∧
   (* if representative of equiv class c is var v,
      then class of v is c *)
   (∀c v. lookup c cs.from_eq = SOME v ⇒
     lookup v cs.to_eq = SOME c)
  )
End

(* As a corollary, different classes have different representatives *)
(* unused *)
Theorem unique_rep[local]:
  CPstate_inv cs ⇒
  c ∈ domain cs.from_eq ∧
  c'∈ domain cs.from_eq ∧
  c ≠ c' ⇒
  lookup c cs.from_eq ≠ lookup c' cs.from_eq
Proof
  rw[CPstate_inv_def]>>metis_tac[domain_lookup,SOME_11]
QED

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

Theorem n_lt_n1[local]:
  n:num < n + 1 ∧
  (x:num < y ∧ y < z ⇒ x < z)
Proof
  rw[]
QED

Theorem set_eq_inv:
  CPstate_inv cs ∧
  lookup t cs.to_eq = NONE ⇒
  CPstate_inv (set_eq cs t s)
Proof
  rw[set_eq_def]>>
  TOP_CASE_TAC>>
  ( (* two subgoals *)
    gvs[AllCaseEqs(),CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[n_lt_n1,option_CLAUSES])
QED

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
  CONJ_TAC >- (
    rw[]>>
    drule ALOOKUP_MEM>>rw[MEM_FILTER]>>
    fs[merge_eqs_def,CPstate_inv_def]>>
    metis_tac[]
  )>>
  rw[lookup_inter_eq,AllCaseEqs()]>>
  metis_tac[CPstate_inv_def]
QED

Theorem set_store_eq_inv:
  CPstate_inv cs ⇒
  CPstate_inv (set_store_eq cs name e)
Proof
  rw[set_store_eq_def]
  >- (
    TOP_CASE_TAC>>
    gvs[AllCaseEqs(),CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[n_lt_n1,option_CLAUSES])>>
  fs[empty_eq_inv]
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
  Cases_on‘x=y’>-metis_tac[]
  >>fs[lookup_eq_def]
  >>every_case_tac>>gvs[CPstate_inv_def]
  >>metis_tac[NOT_NONE_SOME,SOME_11]
QED

Theorem same_classD':
  CPstate_inv cs ∧
  lookup_store_eq cs x = SOME (lookup_eq cs y) ⇒
  ∃c rep.
    ALOOKUP cs.store_to_eq x = SOME c ∧
    lookup y cs.to_eq = SOME c ∧
    lookup c cs.from_eq = SOME rep
Proof
  fs[lookup_store_eq_def,lookup_eq_def,AllCaseEqs()]>>
  rw[]>>gvs[CPstate_inv_def]>>
  metis_tac[NOT_NONE_SOME,SOME_11]
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
  rw[set_eq_def,CPstate_inv_def,both_alloc_vars_def]
  >>TOP_CASE_TAC
  >-(
    rw[lookup_eq_def,lookup_insert]
    >>TOP_CASE_TAC
    >>qpat_x_assum‘∀v c. lookup v cs.to_eq = SOME c ⇒ c < cs.next’drule
    >>rw[]
  )
  >-(
    every_case_tac>>gvs[]
    (*>>rename[‘lookup s cs.to_eq = SOME c_s’]*)
    >>rw[lookup_eq_def,lookup_insert]
    >>TOP_CASE_TAC
    (*>>rename[‘lookup v cs.to_eq = SOME c_v’]*)
    >>every_case_tac>>gvs[]
    (*>>rename[‘lookup c_s cs.from_eq = SOME s_rep’]*)
    >>fs[lookup_eq_def]>>every_case_tac>>fs[]
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
  CPstate_models cs S ⇔
  (∀v c vrep.
    lookup v cs.to_eq = SOME c ⇒
    lookup c cs.from_eq = SOME vrep ⇒
    lookup v S.locals = lookup vrep S.locals) ∧
  (∀s c vrep.
    ALOOKUP cs.store_to_eq s = SOME c ⇒
    lookup c cs.from_eq = SOME vrep ⇒
    FLOOKUP S.store s = lookup vrep S.locals)
End

Theorem CPstate_models_with_const[simp]:
  CPstate_models cs (s with locals_size := ls) = (CPstate_models cs s) /\
  CPstate_models cs (s with fp_regs := fp) = CPstate_models cs s /\
  CPstate_models cs (s with stack := xs) = CPstate_models cs s /\
  CPstate_models cs (s with stack_limit := sl) = CPstate_models cs s /\
  CPstate_models cs (s with stack_max := sm) = CPstate_models cs s /\
  CPstate_models cs (s with stack_size := ssize) = CPstate_models cs s /\
  CPstate_models cs (s with memory := m) = CPstate_models cs s /\
  CPstate_models cs (s with mdomain := md) = CPstate_models cs s /\
  CPstate_models cs (s with sh_mdomain := smd) = CPstate_models cs s /\
  CPstate_models cs (s with permute := p) = CPstate_models cs s /\
  CPstate_models cs (s with compile := c) = CPstate_models cs s /\
  CPstate_models cs (s with compile_oracle := co) = CPstate_models cs s /\
  CPstate_models cs (s with code_buffer := cb) = CPstate_models cs s /\
  CPstate_models cs (s with data_buffer := db) = CPstate_models cs s /\
  CPstate_models cs (s with gc_fun := g) = CPstate_models cs s /\
  CPstate_models cs (s with handler := hd) = CPstate_models cs s /\
  CPstate_models cs (s with clock := clk) = CPstate_models cs s /\
  CPstate_models cs (s with termdep := tdep) = CPstate_models cs s /\
  CPstate_models cs (s with code := cd) = CPstate_models cs s /\
  CPstate_models cs (s with be := b) = CPstate_models cs s /\
  CPstate_models cs (s with ffi := ffi) = CPstate_models cs s
Proof
  fs[CPstate_models_def]
QED

Theorem CPstate_model:
  CPstate_models cs st ⇒
  lookup (lookup_eq cs v) st.locals =
  lookup v st.locals
Proof
  rw[CPstate_models_def,lookup_eq_def]>>every_case_tac>>rw[]
QED

Theorem CPstate_modelsI:
  CPstate_inv cs ∧
  (∀x y.
    lookup_eq cs x = lookup_eq cs y ⇒
    lookup x st.locals = lookup y st.locals) ∧
  (∀x y.
    lookup_store_eq cs x = SOME (lookup_eq cs y) ⇒
    FLOOKUP st.store x = lookup y st.locals) ⇒
  CPstate_models cs st
Proof
  rw[CPstate_inv_def,CPstate_models_def]
  >- (
    first_x_assum irule >>
    rw[lookup_eq_def] >> TOP_CASE_TAC >> TOP_CASE_TAC >>
    metis_tac[domain_lookup,NOT_NONE_SOME,SOME_11]) >>
  first_x_assum irule>>
  rw[lookup_store_eq_def,lookup_eq_def]>>
  TOP_CASE_TAC >> TOP_CASE_TAC >>
  metis_tac[domain_lookup,NOT_NONE_SOME,SOME_11]
QED

Theorem CPstate_modelsD:
  CPstate_inv cs ∧
  CPstate_models cs st ⇒
  (∀x y.
    lookup_eq cs x = lookup_eq cs y ⇒
    lookup x st.locals = lookup y st.locals) ∧
  (∀x y.
    lookup_store_eq cs x = SOME (lookup_eq cs y) ⇒
    FLOOKUP st.store x = lookup y st.locals)
Proof
  rw[CPstate_models_def]
  >- metis_tac[same_classD]
  >- metis_tac[same_classD']
QED

Theorem remove_eq_model:
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) st
Proof
  rw[remove_eq_def]>>
  TOP_CASE_TAC>>rw[empty_eq_def,CPstate_models_def]
QED

Theorem remove_eq_model_insert':
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  (st':('a,'b,'c)wordSem$state).locals =
    insert t val (st:('a,'b,'c)wordSem$state).locals ∧
  st'.store = st.store ⇒
  CPstate_models (remove_eq cs t) st'
Proof
  rw[remove_eq_def]>>
  reverse TOP_CASE_TAC
  >- simp[empty_eq_def,CPstate_models_def]>>
  gvs[CPstate_models_def]>>
  rw[lookup_insert]>>
  fs[CPstate_inv_def]>>
  metis_tac[NOT_SOME_NONE]
QED

Theorem remove_eq_model_insert:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t)
  (st with locals := insert t val st.locals)
Proof
  rw[]>>
  irule remove_eq_model_insert'>>
  rw[]>>metis_tac[]
QED

Theorem remove_eq_model_set_var:
  CPstate_inv cs ∧
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) (set_var t val st)
Proof
  rw[set_var_def]
  >>irule remove_eq_model_insert'
  >>rw[]
  >>metis_tac[]
QED

Theorem CPstate_models_same:
  CPstate_models cs st ∧
  st'.locals = st.locals ∧
  st'.store = st.store ⇒
  CPstate_models cs st'
Proof
  rw[CPstate_models_def]
QED

Theorem set_fp_var_model:
  CPstate_models cs st ⇒
  CPstate_models cs (set_fp_var t val st)
Proof
  DISCH_TAC
  >>irule CPstate_models_same
  >>rw[set_fp_var_def]
  >>metis_tac[]
QED

Theorem merge_eqs_model1:
  CPstate_models cs1 st ⇒
  CPstate_models (merge_eqs cs1 cs2) st
Proof
  gvs[merge_eqs_def,CPstate_models_def,lookup_inter_eq,AllCaseEqs()]>>
  rw[]>>drule ALOOKUP_MEM>>
  fs[MEM_FILTER]>>rw[]
QED

Theorem merge_eqs_model2:
  CPstate_models cs2 st ⇒
  CPstate_models (merge_eqs cs1 cs2) st
Proof
  gvs[merge_eqs_def,CPstate_models_def,lookup_inter_eq,AllCaseEqs()]>>
  rw[]>>drule ALOOKUP_MEM>>
  fs[MEM_FILTER]>>rw[]
QED

Theorem set_eq_store_to_eq[simp]:
  (set_eq cs t s).store_to_eq = cs.store_to_eq
Proof
  rw[set_eq_def]>>every_case_tac>>rw[]
QED

Theorem lookup_eq_remove_eq_t:
  CPstate_inv cs ∧
  lookup_eq (remove_eq cs t) x = t ⇒
  x = t
Proof
  rw[remove_eq_def,lookup_eq_def]>>
  Cases_on‘lookup t cs.to_eq’>>fs[empty_eq_def]>>
  namedCases_on‘lookup x cs.to_eq’["","c"]>>
  namedCases_on‘lookup c cs.from_eq’["","c_rep"]>>gvs[]>>
  metis_tac[CPstate_inv_def,NOT_NONE_SOME]
QED

Theorem lookup_store_eq_set_eqD:
  CPstate_inv cs ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_store_eq (set_eq cs t s) v = SOME r ⇒
  (r=t ⇒ lookup_store_eq cs v = SOME (lookup_eq cs s)) ∧
  (r≠t ⇒ lookup_store_eq cs v = SOME r)
Proof
  Cases_on‘both_alloc_vars (t,s)’>>rw[]>>
  gvs[lookup_store_eq_def,AllCaseEqs()]>>
  gvs[set_eq_def,both_alloc_vars_def]>>
  every_case_tac>>
  gvs[lookup_insert,AllCaseEqs(),lookup_eq_def,CPstate_inv_def]>>
  rpt(first_x_assum drule)>>gvs[]>>
  every_case_tac>>gvs[]
QED

Theorem copy_prop_move_model_aux:
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  both_alloc_vars (t,s) ∧
  lookup s st.locals = SOME sval ⇒
  CPstate_models (set_eq (remove_eq cs t) t s) (st with locals := insert t sval st.locals)
Proof
  strip_tac>>
  ‘CPstate_inv (remove_eq cs t)’ by metis_tac[remove_eq_inv]>>
  ‘CPstate_inv (set_eq (remove_eq cs t) t s)’
  by (
    irule set_eq_inv>>
    rw[remove_eq_def]>>
    TOP_CASE_TAC>>rw[empty_eq_def]
  )>>
  ‘lookup t (remove_eq cs t).to_eq = NONE’ by (
    rw[remove_eq_def]>>
    Cases_on‘lookup t cs.to_eq’>>rw[empty_eq_def])>>
  (* CPstate_inv was easy. Now prove CPstate_models *)
  irule CPstate_modelsI>>
  rw[]
  >- (
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
    rw[lookup_eq_set_eq_t]
    >-(
      Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’
      >-(
        rw[lookup_insert]>>
        metis_tac[lookup_eq_set_eq_is_alloc_var1,remove_eq_model,CPstate_modelsD]
      )
      >-(
        rw[lookup_insert]>>
        gvs[lookup_eq_set_eq_t] >>
        metis_tac[lookup_eq_set_eq_is_alloc_var2,lookup_eq_remove_eq_t]
      )
    )
  )
  >- (
    rw[lookup_insert]>>gvs[]
    >- (
      gs[lookup_eq_set_eq_t]>>
      drule_at (Pos last) lookup_store_eq_set_eqD>> simp[]>>
      metis_tac[remove_eq_model,CPstate_modelsD]) >>
    Cases_on‘lookup_store_eq (remove_eq cs t) x = SOME (lookup_eq (remove_eq cs t) s)’>>
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’>>
    metis_tac[lookup_eq_set_eq_is_alloc_var1,lookup_eq_set_eq_is_alloc_var2,
        lookup_store_eq_set_eqD,lookup_eq_set_eqD,remove_eq_model,CPstate_modelsD])
QED

Theorem set_eq_remove_eq_models:
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  lookup s st.locals = SOME sval ⇒
  CPstate_models (set_eq (remove_eq cs t) t s) (st with locals := insert t sval st.locals)
Proof
  Cases_on`both_alloc_vars (t,s)`
  >-
    metis_tac[copy_prop_move_model_aux]>>
  fs[both_alloc_vars_def]>>
  simp[set_eq_def]>>
  metis_tac[remove_eq_inv,remove_eq_model_insert]
QED

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
  CPstate_inv cs /\
  CPstate_models cs st ⇒
  get_var (lookup_eq cs x) st = get_var x st
Proof
  rw[get_var_def]>>
  imp_res_tac CPstate_modelsD >>
  imp_res_tac lookup_eq_idempotent >>
  metis_tac[]
QED

Theorem CPstate_modelsD_get_vars:
  CPstate_inv cs /\
  CPstate_models cs st ⇒
  get_vars (MAP (lookup_eq cs) xs) st = get_vars xs st
Proof
  Induct_on `xs` >> rw[get_vars_def] >>
  DEP_REWRITE_TAC[CPstate_modelsD_get_var] >>
  fs[]
QED

Theorem CPstate_modelsD_get_var_imm:
  CPstate_inv cs /\
  CPstate_models cs st ⇒
  get_var_imm (lookup_eq_imm cs x) st = get_var_imm x st
Proof
  rw[lookup_eq_imm_def]>>CASE_TAC>>rw[get_var_imm_def]
  >>metis_tac[CPstate_modelsD_get_var]
QED

Theorem CPstate_modelsD_Var:
  CPstate_inv cs /\
  CPstate_models cs st ⇒
  word_exp st (Var (lookup_eq cs x)) = word_exp st (Var x)
Proof
  rw[word_exp_def]>>
  metis_tac[CPstate_modelsD_get_var]
QED

Theorem CPstate_modelsD_lookup_eq_imm:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  word_exp st (case lookup_eq_imm cs x of Reg r => Var r | Imm w => Const w) =
  word_exp st (case x of Reg r => Var r | Imm w => Const w)
Proof
  Cases_on‘x’>>
  rw[lookup_eq_imm_def,word_exp_def]>>
  metis_tac[CPstate_modelsD_get_var]
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

Theorem copy_prop_move_get_vars:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  copy_prop_move moves cs = (moves', cs') ⇒
  get_vars (MAP SND moves') st = get_vars (MAP SND moves) st
Proof
  rw[]
  >>dxrule_all copy_prop_move_eval_aux1
  >>metis_tac[MAP_get_var_eqD]
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
  CPstate_inv cs ∧
  copy_prop_prog prog cs = (prog', cs') ⇒
  CPstate_inv cs'
Proof
  map_every qid_spec_tac [`cs'`,`prog'`,`cs`,`prog`]>>
  ho_match_mp_tac copy_prop_prog_ind>>
  rw[copy_prop_prog_def]>>
  rpt(pairarg_tac>>gvs[])>>
  fs[empty_eq_inv,remove_eq_inv,remove_eqs_inv]
  >- metis_tac[copy_prop_move_inv]
  >- metis_tac[copy_prop_inst_inv]
  >- metis_tac[merge_eqs_inv]
  >- (
    gvs[AllCaseEqs(),empty_eq_inv,set_store_eq_inv]
  )
  >- (
    gvs[AllCaseEqs(),UNCURRY_EQ,remove_eq_inv]>>
    metis_tac[copy_prop_move_inv])
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
      simp[]>>metis_tac[get_vars_length_lemma,LENGTH_MAP,LENGTH,SUC_NOT]
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
    ‘CPstate_models (set_eq (remove_eq (SND (copy_prop_move moves cs)) t) t s)
        ((st with locals := alist_insert (MAP FST moves) values' st.locals) with
         locals :=
           insert t val (st with locals := alist_insert (MAP FST moves) values' st.locals).locals)’
      suffices_by simp[state_fupdfupds]>>
    ‘lookup s (st with locals := alist_insert (MAP FST moves) values' st.locals).locals = SOME val’ by (
        ‘¬MEM s (MAP FST moves)’ by (qpat_x_assum‘_∩_={}’mp_tac>>simp[]>>SET_TAC[])>>
        simp[lookup_alist_insert_same]
        >-fs[get_var_def]
      )>>
    metis_tac[set_eq_remove_eq_models,copy_prop_move_inv,PAIR]
  )
QED

Theorem EVERY_NOT_MEM_D:
  EVERY (λt. ¬MEM t ss) tt ⇒ set tt ∩ set ss = {}
Proof
  Induct_on‘tt’>>rw[INSERT_INTER]
QED

Theorem copy_prop_move_correct:
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  copy_prop_prog (Move pri moves) cs = (prog', cs') ∧
  evaluate (Move pri moves, st) = (err, st') ⇒
  evaluate (prog', st) = (err, st') ∧
  (err = NONE ⇒ CPstate_models cs' st')
Proof
  rw[copy_prop_prog_def]>>
  gvs[UNCURRY_EQ]
  >- (
    fs[evaluate_def]
    >> full_case_tac
    >> ‘get_vars (MAP SND xs') st = get_vars (MAP SND moves) st’ by metis_tac[copy_prop_move_get_vars]
    >> gvs[AllCaseEqs()]
    >> metis_tac[copy_prop_move_eval_aux3]
  )
  >-(
    fs[evaluate_def]
    >>full_case_tac>>full_case_tac>>fs[]
    >>dxrule EVERY_NOT_MEM_D
    >>metis_tac[copy_prop_move_model]
  )
  >- metis_tac[empty_eq_model]
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

fun word_exp_cong_tac (asl,c) =
  let
    val (t,_) = dest_eq c
    val (r, d) = strip_comb t
    val (rname, _) = dest_const r
    val tac = case rname of
      "get_var" =>
      metis_tac[CPstate_modelsD_get_var]
    | "get_vars" =>
      irule MAP_get_var_eqD>>simp[]
      >>metis_tac[CPstate_modelsD_get_var]
    | "word_exp" =>
      let
        val (exp_rator, _) = strip_comb $ el 2 d
        val (exp_rator_name, exp_rator_ty) = dest_const exp_rator
        fun use_cong cong = irule cong>>rw[]
      in
        case exp_rator_name of
          "Op" => use_cong word_exp_cong_Op
        | "Shift" => use_cong word_exp_cong_Shift
        | "Load" => use_cong word_exp_cong_Load
        | "Var" => use_cong word_exp_cong_Var
        | "reg_imm_CASE" =>
          metis_tac[CPstate_modelsD_lookup_eq_imm]
(*
          let
            val (xty,_) = dom_rng exp_rator_ty
            val case_rand = ISPEC (mk_comb (r, el 1 d)) $ TypeBase.case_rand_of xty
          in
            rw[case_rand]
          end
*)
      end
    | _ =>
      if TypeBase.is_case t then
        (* use appropriate case_cong *)
        let
          val cong = TypeBase.case_cong_of (#1(dom_rng(type_of r)))
        in
          irule cong>>rw[]
        end
      else NO_TAC
  in
    tac (asl,c)
  end;

(* "inst" is constant wordSem$inst *)
Theorem copy_prop_inst_eval:
  ∀ins cs st prog' cs'.
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  (prog', cs') = copy_prop_inst ins cs ⇒
  evaluate (prog', st) = evaluate (Inst ins, st)
Proof
  recInduct copy_prop_inst_ind
  >>rw[evaluate_def,inst_def,copy_prop_inst_def,assign_def]
  >>rpt word_exp_cong_tac
QED

Theorem remove_eq_comm:
  remove_eq (remove_eq cs x) y = remove_eq (remove_eq cs y) x
Proof
  rw[remove_eq_def]>>every_case_tac
QED

Theorem copy_prop_inst_correct:
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  copy_prop_inst ins cs = (prog', cs') ∧
  evaluate (Inst ins, st) = (err, st') ⇒
  evaluate (prog', st) = (err, st') ∧
  (err = NONE ⇒ CPstate_models cs' st')
Proof
  rw[]
  >- metis_tac[copy_prop_inst_eval]
  >- (
    (* CPstate_models *)
    Cases_on‘ins’
    >> gvs[copy_prop_inst_def,evaluate_def,inst_def,assign_def,mem_store_def,remove_eqs_def,AllCaseEqs()]
    >> rpt(pairarg_tac>>fs[])
    >> metis_tac[remove_eq_inv,remove_eq_model_set_var,remove_eq_model,set_fp_var_model]
  )
QED

Theorem remove_eq_model_unset_var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) (unset_var t st)
Proof
  rw[unset_var_def,remove_eq_def,CPstate_models_def,lookup_delete,empty_eq_def]
  >>every_case_tac>>fs[]
  >>fs[CPstate_inv_def]>>metis_tac[NOT_NONE_SOME]
QED

(*
Theorem remove_eq_model_sh_mem_set_var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  sh_mem_set_var x t st = (err, st') ⇒
  CPstate_models (remove_eq cs t) st'
Proof
  namedCases_on‘x’["","fr"]>-
  (rw[sh_mem_set_var_def]>>
  irule remove_eq_model >>
  first_x_assum (irule_at Any))
  >> Cases_on‘fr’ >> rw[sh_mem_set_var_def]
  >-(fs[] >> metis_tac[remove_eq_model_set_var])
  >-(fs[flush_state_def] >> fs[] >> fs[CPstate_models_def])
QED
*)

Theorem CPstate_modelsD_copy_prop_share:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  word_exp st (copy_prop_share e cs) = word_exp st e
Proof
  rw[copy_prop_share_def]
  >>every_case_tac
  >>metis_tac[CPstate_modelsD_Var,word_exp_cong_Op,MAP]
QED

Theorem lookup_store_eq_SOME:
  CPstate_models cs st ∧
  lookup_store_eq cs s = SOME v ⇒
  FLOOKUP st.store s = lookup v st.locals
Proof
  rw[]>>
  gvs[CPstate_models_def,lookup_store_eq_def,AllCaseEqs()]
QED

Theorem lookup_remove_eq[simp]:
  lookup n (remove_eq cs n).to_eq = NONE
Proof
  rw[remove_eq_def]>>
  every_case_tac>>fs[empty_eq_def]
QED

Theorem lookup_eq_set_store_eq:
  CPstate_inv cs ∧
  is_alloc_var x ⇒
  lookup_eq (set_store_eq cs s x) y =
  lookup_eq cs y
Proof
  rw[set_store_eq_def,lookup_eq_def]>>
  every_case_tac>>gvs[lookup_insert,AllCaseEqs()]>>
  gvs[CPstate_inv_def]>>
  rpt(first_x_assum drule)>>gs[]
QED

Theorem lookup_store_eq_set_store_eq_1:
  CPstate_inv cs ∧
  is_alloc_var x ∧
  lookup_store_eq (set_store_eq cs s x) s = SOME y ⇒
  lookup_eq cs x = lookup_eq cs y
Proof
  rw[set_store_eq_def,lookup_store_eq_def,lookup_eq_def]>>
  every_case_tac>>gvs[lookup_insert,AllCaseEqs()]>>
  gvs[CPstate_inv_def,domain_lookup,PULL_EXISTS]>>
  res_tac>>gvs[]
QED

Theorem lookup_store_eq_set_store_eq_2:
  CPstate_inv cs ∧
  is_alloc_var x ∧
  s ≠ t ∧
  lookup_store_eq (set_store_eq cs s x) t = SOME y ⇒
  lookup_store_eq cs t = SOME y
Proof
  rw[set_store_eq_def,lookup_store_eq_def]>>
  every_case_tac>>gvs[lookup_insert,AllCaseEqs()]>>
  gvs[CPstate_inv_def,domain_lookup,PULL_EXISTS]>>
  rpt(first_x_assum drule)>>gs[]>>rw[]>>gvs[]
QED

Theorem set_store_eq_model_set_store:
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  get_var n st = SOME w ⇒
  CPstate_models (set_store_eq cs s n) (set_store s w st)
Proof
  rw[]>>
  reverse (Cases_on`is_alloc_var n`)
  >- (
    simp[set_store_eq_def]>>
    metis_tac[empty_eq_model])>>
  irule CPstate_modelsI>>
  simp[Once CONJ_ASSOC]>>
  reverse CONJ_ASM2_TAC >- simp[set_store_eq_inv]>>
  gvs[lookup_eq_set_store_eq,get_var_def]>>
  rw[]
  >- metis_tac[CPstate_modelsD]>>
  simp[set_store_def,FLOOKUP_UPDATE]>>rw[]
  >- (
    drule_all lookup_store_eq_set_store_eq_1>>
    simp[lookup_eq_idempotent]>>
    metis_tac[CPstate_modelsD])>>
  metis_tac[lookup_store_eq_set_store_eq_2,CPstate_modelsD]
QED

Theorem copy_prop_correct:
  ∀prog cs st prog' cs' err st'.
  CPstate_inv cs ∧
  CPstate_models cs st ∧
  copy_prop_prog prog cs = (prog', cs') ∧
  err ≠ SOME Error ∧
  evaluate (prog, st) = (err, st') ⇒
  evaluate (prog', st) = (err, st') ∧
  (err = NONE ⇒ CPstate_models cs' st')
Proof
  Induct (* 23 subgoals *)
  >~ [`Skip`]
  >- fs[evaluate_def,copy_prop_prog_def]
  >~ [`Move`]
  >-
    metis_tac[copy_prop_move_correct]
  >~ [`Inst`]
  >- (
    rw[copy_prop_prog_def]>>
    metis_tac[copy_prop_inst_correct]
  )
  >~ [`Assign`]
  >- (
    rw[copy_prop_prog_def]>>
    fs[evaluate_def]>>
    metis_tac[empty_eq_model])
  >~ [`Get`]
  >- (
    rpt gen_tac>> strip_tac>>
    gvs[copy_prop_prog_def,CaseEq "option"]
    >- (
      gvs[evaluate_def,AllCaseEqs()]>>
      metis_tac[remove_eq_model_set_var])>>
    reverse (gvs[AllCaseEqs(),UNCURRY_EQ])
    >- ( (* v = n, Skip case *)
      drule_all lookup_store_eq_SOME>>
      gvs[evaluate_def,get_store_def,AllCaseEqs(),set_var_def]>>
      strip_tac>>
      `lookup n st.locals = SOME x` by gvs[]>>
      drule insert_unchanged>>
      simp[state_component_equality]>>
      rw[]>>
      `st with locals := st.locals = st` by simp[state_component_equality]>>
      simp[])>>
    (* v ≠ n, Move case *)
    drule_all lookup_store_eq_SOME>>
    gvs[get_store_def,AllCaseEqs(),copy_prop_move_def,evaluate_def]>>
    strip_tac>>
    CONJ_TAC
    >- (
      qexists_tac `[x]`>>
      Cases_on `lookup v st.locals`>>fs[]>>
      imp_res_tac CPstate_model>>gvs[get_vars_def,get_var_def,set_vars_def,alist_insert_def,set_var_def])>>
    `set_var n x st = st with locals := insert n x st.locals` by rw[set_var_def]>>
    pop_assum SUBST_ALL_TAC>>
    irule set_eq_remove_eq_models>>
    gvs[get_var_def]>>Cases_on `lookup v st.locals`>>fs[])
  >~[`Set`]
  >- (
    rw[copy_prop_prog_def,evaluate_def]
    >> gvs[AllCaseEqs(),evaluate_def]
    >> simp[set_store_eq_inv,empty_eq_model]
    >> fs[word_exp_def, CPstate_modelsD_get_var]
    >> metis_tac[set_store_eq_model_set_store])
  >~[`Store`]
  >-(
    rw[copy_prop_prog_def,evaluate_def]
    >> gvs[AllCaseEqs(),evaluate_def,empty_eq_model])
  >~[`MustTerminate`]
  >-(
    rw[copy_prop_prog_def,evaluate_def]
    >> gvs[AllCaseEqs(),evaluate_def]
    >> rpt(pairarg_tac>>fs[])
    >> rw[evaluate_def]
    >> drule_all copy_prop_prog_inv >> strip_tac
    >-(
      Cases_on `res = SOME TimeOut` >> gvs[]>>
      `CPstate_models cs (st with <|clock := MustTerminate_limit (:α); termdep := st.termdep − 1|>)` by (
        qpat_x_assum`CPstate_models cs st`mp_tac>>
        rw[state_component_equality,CPstate_models_def])>>
      first_x_assum (qspecl_then [`cs`,`st with <|clock := MustTerminate_limit (:α); termdep := st.termdep - 1|>`,`p1'`,`cs'`,`err`,`s1`] mp_tac)>>
      simp[]>>strip_tac>>simp[]
    )
    >-(
      `res <> SOME TimeOut` by (CCONTR_TAC >> gvs[])>> gvs[]>>
      `CPstate_models cs (st with <|clock := MustTerminate_limit (:α); termdep := st.termdep − 1|>)` by (
        qpat_x_assum `CPstate_models cs st` mp_tac>>
        rw[state_component_equality,CPstate_models_def])>>
      first_x_assum (qspecl_then [`cs`,`st with <|clock := MustTerminate_limit (:α); termdep := st.termdep - 1|>`,`p1'`,`cs'`,`NONE`,`s1`] mp_tac)>>
      simp[]
    )
  )
  >~[`Call`]
  >-(
    rw[copy_prop_prog_def]>>fs[evaluate_def]
    >>metis_tac[empty_eq_model]
  )
  >~[‘Seq’]
  >-(
    rpt GEN_TAC
    >> rename1 `evaluate (Seq p1 p2, st) = (err,st')`
    >> simp[evaluate_def,copy_prop_prog_def]
    >> rpt(pairarg_tac>>fs[])
    >> Cases_on `res`
    >> simp[evaluate_def, copy_prop_prog_def]
    >> strip_tac
    >- (
      qpat_x_assum `!cs st prog' cs' err st'. _ /\ _ /\ copy_prop_prog p1 _ = _ /\ _ ==> _`
        (qspecl_then [`cs`,`st`,`q1`,`cs''`,`NONE`,`s1`] mp_tac)>>simp[]>>strip_tac>>
      `CPstate_inv cs''` by metis_tac[copy_prop_prog_inv]>>
      qpat_x_assum `!cs st prog' cs' err st'. _ /\ _ /\ copy_prop_prog p2 _ = _ /\ _ ==> _`
        (qspecl_then [`cs''`,`s1`,`q2`,`cs'`,`err`,`st'`] mp_tac)>>
      gvs[evaluate_def]
      )
    >- (
      qpat_x_assum `!cs st prog' cs' err st'. _ /\ _ /\ copy_prop_prog p1 _ = _ /\ _ ==> _`
        (qspecl_then [`cs`,`st`,`q1`,`cs''`,`SOME x`,`s1`] mp_tac)>>
      gvs[evaluate_def]
      )
    )
  >~[‘If’]
  >-(
    rpt GEN_TAC
    >> rename1 `evaluate (If c n r p1 p2, st) = (err,st')`
    >> strip_tac
    >> `get_var (lookup_eq cs n) st = get_var n st` by metis_tac[CPstate_modelsD_get_var]
    >> `get_var_imm (lookup_eq_imm cs r) st = get_var_imm r st` by metis_tac[CPstate_modelsD_get_var_imm]
    >> gvs[evaluate_def,copy_prop_prog_def]
    >> rpt(pairarg_tac >> fs[])
    >> gvs[AllCaseEqs(),evaluate_def]
    >> metis_tac[merge_eqs_model1,merge_eqs_model2]
    )
  >~[`Alloc`]
  >-(
    rw[copy_prop_prog_def]>>fs[evaluate_def]
    >> metis_tac[empty_eq_model]
  )
  >~[`StoreConsts`]
  >- (
    rw[copy_prop_prog_def]>>
    fs[evaluate_def,remove_eqs_def]>>
    gvs[AllCaseEqs()]>>
    simp[Once remove_eq_comm]>>
    irule remove_eq_model_set_var>>
    conj_tac>- metis_tac[remove_eq_inv]>>
    irule remove_eq_model_set_var>>
    conj_tac>-metis_tac[remove_eq_inv]>>
    simp[Once remove_eq_comm]>>
    irule remove_eq_model_unset_var>>
    conj_tac>-metis_tac[remove_eq_inv]>>
    irule remove_eq_model_unset_var>>
    conj_tac>-metis_tac[remove_eq_inv]>>
    fs[]
  )
  >~[`Raise`]
  >- (
    rw[copy_prop_prog_def]>>
    gvs[evaluate_def]
    >> fs[CPstate_modelsD_get_var]
    >> gvs[AllCaseEqs()])
  >~[`Return`]
  >- (
    rw[copy_prop_prog_def]>>
    gvs[evaluate_def]
    >> fs[CPstate_modelsD_get_var,CPstate_modelsD_get_vars]
    >> gvs[AllCaseEqs()]
  )
  >~[`Tick`]
  >- (
    rw[copy_prop_prog_def,evaluate_def]>>
    fs[dec_clock_def,CPstate_models_def]
  )
  >~[`OpCurrHeap`]
  >-(
    rw[copy_prop_prog_def]>>
    fs[evaluate_def]
    >- (
      gvs[AllCaseEqs(),remove_eq_model_set_var])
    >-(
      pop_assum sym_sub_tac>>
      irule option_case_cong>> simp[]>>
      irule word_exp_cong_Op>>
      gvs[CPstate_modelsD_Var])
    >- (gvs[AllCaseEqs()]>>metis_tac[remove_eq_model_set_var]))
  >~[`LocValue`]
  >-(
    rw[copy_prop_prog_def]>>
    gvs[evaluate_def,AllCaseEqs()]>>
    metis_tac[remove_eq_model_set_var]
  )
  >~[`Install`]
  >- (
    rw[copy_prop_prog_def]>>
    fs[evaluate_def]>>
    metis_tac[empty_eq_model]
  )
  >~[`CodeBufferWrite`]
  >- (
    rpt gen_tac >> strip_tac>>
    gvs[copy_prop_prog_def,evaluate_def] >>
    fs[CPstate_modelsD_get_var,CPstate_modelsD_get_vars] >>
    gvs[AllCaseEqs()])
  >~[`DataBufferWrite`]
  >- (
    rpt gen_tac >> strip_tac>>
    gvs[copy_prop_prog_def,evaluate_def] >>
    fs[CPstate_modelsD_get_var,CPstate_modelsD_get_vars] >>
    gvs[AllCaseEqs()])
  >~[`FFI`]
  >- (
    rw[copy_prop_prog_def]>>
    fs[evaluate_def]>>
    metis_tac[empty_eq_model]
  )
  >~[`ShareInst`]
  >- (
    rw[copy_prop_prog_def]
    >> fs[evaluate_def,CPstate_modelsD_copy_prop_share]
    >> gvs[AllCaseEqs()]
    >> gvs[oneline share_inst_def,AllCaseEqs(),oneline sh_mem_set_var_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store16_def,sh_mem_store32_def]
    >> simp[remove_eq_model_set_var,remove_eq_model])
QED

(* Main semantics result *)
Theorem evaluate_copy_prop:
  FST (evaluate (e, s)) ≠ SOME Error ⇒
  evaluate (copy_prop e, s) = evaluate (e, s)
Proof
  rw[copy_prop_def]
  >>Cases_on `evaluate (e,s)` >> Cases_on `copy_prop_prog e empty_eq` >> fs[]
  >>metis_tac[copy_prop_correct,empty_eq_inv,empty_eq_model,PAIR]
QED
