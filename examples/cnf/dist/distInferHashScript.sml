(*
    Abstract specification including fingerprinting and an attacker
 *)
Theory distInferHash
Ancestors
  finite_map list pred_set relation string
Libs
  bossLib

Datatype:
  message =
  String string
  | Num num
  | Hash 'key message
  | Clause 'fact
  | Tuple message message

End

Datatype:
  aknowledge = <|
    keys  : 'key set;
    msgs  : ('fact,'key) message set;
    facts : 'fact set
  |>
End

Inductive ainfer:
[~refl:]
  ∀msg. ainfer msg msg
[~tuple1:]
  ∀msg1 msg1' msg2.
    ainfer msg1 msg1' ⇒ ainfer (Tuple msg1 msg2) msg1'
[~tuple2:]
  ∀msg1 msg2 msg2'.
    ainfer msg2 msg2' ⇒ ainfer (Tuple msg1 msg2) msg2'
End

Inductive makeMsg:
[~string:]
  ∀knowledge s. makeMsg knowledge (String s)
[~num:]
  ∀knowledge n. makeMsg knowledge (Num n)
[~clause:]
  ∀knowledge f. makeMsg knowledge (Clause f)
[~tuple:]
  ∀knowledge msg1 msg2.
    makeMsg knowledge msg1 ∧ makeMsg knowledge msg2 ⇒
    makeMsg knowledge (Tuple msg1 msg2)
[~replay:]
  ∀knowledge msg.
    msg ∈ knowledge.msgs ∧ ainfer msg msg'  ⇒ makeMsg knowledge msg'
[~hash:]
  ∀knowledge key msg.
    key ∈ knowledge.keys ∧ makeMsg knowledge msg ⇒ makeMsg knowledge (Hash key msg)
End

Datatype:
  lknowledge = <|
    keys  : 'key set;
    clauses : num |-> 'fact set;
    msgs : ('fact,'key) message set
  |>
End

Datatype:
  state = <| attacker : ('fact,'key) aknowledge;
             procs    : num |-> ('fact, 'key) lknowledge;
             problems : num |-> 'fact set
           |>
End

Definition IFact_def:
  IFact id cl = Tuple (Num id) (Clause cl)
End

Definition Delete_def:
  Delete cl = Tuple (String "delete") (Clause cl)
End

Definition Import_def:
  Import id cl k =
  let msg = Tuple (Num id) (Clause cl) in
    Tuple (String "import")
          (Tuple msg (Hash k msg))
End

Definition Produce_def:
  Produce id cl k =
  let msg = Tuple (Num id) (Clause cl) in
    Tuple (String "produce")
          (Tuple msg (Hash k msg))
End

Inductive step:
[~receive:]
  ∀st id lst msg.
    FLOOKUP st.procs id = SOME lst ∧
    makeMsg st.attacker msg ⇒
    step infer
         st
         (st with procs := st.procs
                             |+ (id, lst with msgs := msg INSERT lst.msgs))
[~delete:]
  ∀st id lst cid facts f.
    FLOOKUP st.procs id = SOME lst ∧
    FLOOKUP lst.clauses cid = SOME facts ∧
    Delete f ∈ lst.msgs ⇒
    step infer
         st
         (st with procs := st.procs |+ (id,
                                        lst with
                                            <| msgs := lst.msgs DELETE Delete f;
                                               clauses := lst.clauses |+ (cid,facts DELETE f)
                                            |>))
[~produce:]
  ∀st id lst cid facts fact k.
    FLOOKUP st.procs id = SOME lst ∧
    FLOOKUP lst.clauses cid = SOME facts ∧
    infer facts fact ∧
    k ∈ lst.keys
    ⇒
    step infer
         st
         (st with <|procs := st.procs |+ (id,
                                          lst with
                                              clauses := lst.clauses |+ (cid,fact INSERT facts));
                    attacker := st.attacker with
                                  msgs := (Produce cid fact k)
                                          INSERT
                                          st.attacker.msgs |>)
[~import:]
  ∀st id lst cid facts f.
    FLOOKUP st.procs id = SOME lst ∧
    FLOOKUP lst.clauses cid = SOME facts ∧
    Delete f ∈ lst.msgs ⇒
    step infer
         st
         (st with procs := st.procs |+ (id,
                                        lst with
                                            <| msgs := lst.msgs DELETE Delete f;
                                               clauses := lst.clauses |+ (cid,facts DELETE f)
                                            |>))
[~init:]
  n ∉ FDOM st.problems ∧
  procs ⊆ FDOM st.procs ∧
  procs' = FMAP_MAP2
           (λ(id,lst).
              if id ∈ procs then
                lst with clauses := lst.clauses |+ (n,facts)
              else
                lst)
           st.procs ∧
  FINITE facts
  ⇒
  step infer st
       (st with <| problems := st.problems |+ (n,facts);
                   procs := procs' |>)
End

(* Everyone holds at most finitely many facts *)
Definition finite_facts_def:
  finite_facts st ⇔
  (∀n facts. FLOOKUP st.problems n = SOME facts ⇒ FINITE facts) ∧
  (∀n id lst facts.
     FLOOKUP st.procs id = SOME lst ∧ FLOOKUP lst.clauses n = SOME facts ⇒
     FINITE facts)
End

(* The nodes' keys are not compromised *)
Definition disjoint_keys_def:
  disjoint_keys st ⇔
  DISJOINT st.attacker.keys
           (BIGUNION(IMAGE lknowledge_keys (FRANGE st.procs)))
End

(* All of the attacker's hashed facts (with keys other than the attackers')
   are entailed *)
Definition attacker_facts_ok_def:
  attacker_facts_ok infer st ⇔
    ∀k id f.
      k ∉ st.attacker.keys ∧
      makeMsg st.attacker (Hash k (IFact id f)) ⇒
      ∃facts. FLOOKUP st.problems id = SOME facts ∧
              infer facts f
End

(* All of the participants' local facts are entailed *)
Definition local_facts_ok_def:
  local_facts_ok infer st ⇔
    ∀id lst facts n.
     FLOOKUP st.procs id = SOME lst ∧
     FLOOKUP lst.clauses n = SOME facts ⇒
     ∃ofacts.
       FLOOKUP st.problems n = SOME ofacts ∧
       ∀fact. fact ∈ facts ⇒ infer ofacts fact
End

(* If an incoming message has a fact hashed with a key that
   the attacker does not know, it is entailed *)
Definition incoming_messages_ok_def:
  incoming_messages_ok infer st ⇔
    ∀id lst msg k n f.
     FLOOKUP st.procs id = SOME lst ∧
     msg ∈ lst.msgs ∧
     ainfer msg (Hash k (IFact n f)) ∧
     k ∉ st.attacker.keys ⇒
     ∃ofacts.
       FLOOKUP st.problems n = SOME ofacts ∧
       infer ofacts f
End

Definition step_inv_def:
  step_inv infer st ⇔
    disjoint_keys st ∧
    finite_facts st ∧
    attacker_facts_ok infer st ∧
    local_facts_ok infer st ∧
    incoming_messages_ok infer st
End

(* TODO: copypaste from distInfer *)
Definition cut_elimination_def:
  cut_elimination infer ⇔
    (∀facts facts' fact fact'.
       infer facts fact ∧ infer (fact INSERT facts') fact' ⇒
       infer (facts ∪ facts') fact')
End

Definition assumption_def:
  assumption infer ⇔ (∀fact. infer {fact} fact)
End

Definition monotonic_def:
  monotonic infer ⇔
    (∀facts facts' fact.
       infer facts fact ⇒ infer (facts ∪ facts') fact)
End

Theorem cut_elim_lemma1:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧
    infer (oprems ∪ facts) fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[] >> gvs[IN_DEF] >>
  first_x_assum irule >>
  gvs[monotonic_def] >>
  first_x_assum rev_dxrule >>
  strip_tac >>
  gvs[cut_elimination_def] >>
  first_x_assum $ qspecl_then [‘oprems ∪ facts’,‘oprems ∪ facts’] assume_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_x_assum $ irule_at $ Pos last >>
  pop_assum mp_tac >>
  match_mp_tac EQ_IMPLIES >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[SET_EQ_SUBSET,SUBSET_DEF]
QED

Theorem cut_elim_lemma2:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧ infer facts fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[]
  >- (gvs[monotonic_def] >> res_tac >> fs[]) >>
  gvs[IN_DEF] >>
  irule cut_elim_lemma1 >>
  gvs[] >>
  first_assum $ irule_at $ Pos hd >>
  gvs[cut_elimination_def] >>
  first_assum $ rev_drule_then drule >>
  strip_tac
QED

Theorem step_disjoint_keys:
  step infer st st' ∧
  disjoint_keys st ⇒
  disjoint_keys st'
Proof
  Induct_on ‘step’ >>
  rw[disjoint_keys_def,IMAGE_FRANGE, SF DNF_ss,FRANGE_FLOOKUP,
     FLOOKUP_FMAP_MAP2,
     FLOOKUP_UPDATE, AllCaseEqs()] >>
  res_tac
QED

Theorem step_finite_facts:
  step infer st st' ∧
  finite_facts st ⇒
  finite_facts st'
Proof
  Induct_on ‘step’ >>
  rw[finite_facts_def,SF DNF_ss,FRANGE_FLOOKUP,
     FLOOKUP_FMAP_MAP2,
     FLOOKUP_UPDATE, AllCaseEqs()] >>
  res_tac
QED

Theorem DISJOINTD2[local]:
  x ∈ Q ∧ DISJOINT P Q ⇒ x ∉ P
Proof
  metis_tac[IN_DISJOINT]
QED

Theorem ainfer_trans:
  ∀msg msg' msg''. ainfer msg msg' ∧ ainfer msg' msg'' ⇒ ainfer msg msg''
Proof
  Induct_on ‘ainfer’ >>
  rw[] >>
  metis_tac[ainfer_rules]
QED

Theorem makeMsg_ainfer:
  makeMsg st msg ∧ ainfer msg msg' ⇒ makeMsg st msg'
Proof
  Induct_on ‘makeMsg’ >>
  rw[]
  >- (gvs[Once ainfer_cases] >>
      irule makeMsg_string)
  >- (gvs[Once ainfer_cases] >>
      irule makeMsg_num)
  >- (gvs[Once ainfer_cases] >>
      irule makeMsg_clause)
  >- (pop_assum mp_tac >> rw[Once ainfer_cases] >>
      metis_tac[makeMsg_tuple])
  >- metis_tac[ainfer_trans,makeMsg_replay] >>
  pop_assum mp_tac >> rw[Once ainfer_cases] >>
  metis_tac[makeMsg_cases]
QED

Theorem step_incoming_messages_ok:
  step infer st st' ∧
  attacker_facts_ok infer st ∧
  incoming_messages_ok infer st ⇒
  incoming_messages_ok infer st'
Proof
  Induct_on ‘step’ >> rpt conj_tac
  >~ [‘FMAP_MAP2’] (* init *)
  >- (rw[incoming_messages_ok_def,
         TO_FLOOKUP,
         FLOOKUP_FMAP_MAP2
         ] >>
      BasicProvers.PURE_FULL_CASE_TAC >>
      gvs[] >>
      res_tac >>
      gvs[] >>
      Cases_on ‘n = n'’ >> gvs[FLOOKUP_UPDATE]) >>
  rw[IMAGE_FRANGE,
     incoming_messages_ok_def,attacker_facts_ok_def,SF DNF_ss,FRANGE_FLOOKUP,
     FLOOKUP_FMAP_MAP2,
     FLOOKUP_UPDATE, AllCaseEqs()] >>
  gvs[] >>
  metis_tac[makeMsg_ainfer]
QED

Theorem step_local_facts_ok:
  step infer st st' ∧
  incoming_messages_ok infer st ∧
  local_facts_ok infer st ∧
  finite_facts st ∧
  cut_elimination infer ∧ monotonic infer ∧ assumption infer ⇒
  local_facts_ok infer st'
Proof
  Induct_on ‘step’ >> rpt conj_tac
  >~ [‘Produce’]
  >- (rw[local_facts_ok_def,SF DNF_ss,FRANGE_FLOOKUP,
         FLOOKUP_UPDATE, AllCaseEqs()] >>
      first_assum $ drule_then drule >>
      strip_tac >>
      gvs[] >>
      conj_tac
      >- (irule cut_elim_lemma2 >>
          simp[] >>
          last_assum $ irule_at $ Pat ‘infer _ _’ >>
          gvs[finite_facts_def,SUBSET_DEF] >>
          metis_tac[IN_DEF]) >>
      metis_tac[])
  >~ [‘FMAP_MAP2’] (* init *)
  >- (rw[local_facts_ok_def,finite_facts_def,
         TO_FLOOKUP,
         FLOOKUP_FMAP_MAP2
         ] >>
      BasicProvers.PURE_FULL_CASE_TAC >>
      gvs[] >>
      res_tac >>
      gvs[] >>
      Cases_on ‘n = n'’ >> gvs[FLOOKUP_UPDATE] >>
      gvs[assumption_def,SUBSET_DEF,monotonic_def,IN_DEF] >>
      rpt strip_tac >>
      rename [‘_ _ fact’] >>
      qpat_x_assum ‘∀fact. infer {_} _’ $ qspec_then ‘fact’ assume_tac >>
      qpat_x_assum ‘∀fact facts' fact. _’ drule >>
      disch_then $ qspec_then ‘facts’ mp_tac >>
      match_mp_tac EQ_IMPLIES >>
      AP_THM_TAC >> AP_TERM_TAC >>
      rw[SET_EQ_SUBSET,SUBSET_DEF,IN_DEF]) >>
  rw[IMAGE_FRANGE,
     incoming_messages_ok_def,local_facts_ok_def,SF DNF_ss,FRANGE_FLOOKUP,
     FLOOKUP_FMAP_MAP2,
     FLOOKUP_UPDATE, AllCaseEqs()] >>
  gvs[] >>
  res_tac >>
  gvs[] >>
  metis_tac[makeMsg_ainfer]
QED

Theorem makeMsg_hash_lemma:
  ∀st k msg.
  makeMsg st (Hash k msg) ⇒
  (k ∈ st.keys) ∨ (∃msg'. msg' ∈ st.msgs ∧ ainfer msg' (Hash k msg))
Proof
  Induct_on ‘makeMsg’ >>
  simp[PULL_FORALL] >>
  rw[] >>
  metis_tac[]
QED

Theorem step_attacker_facts_ok_lem[local]:
  step infer st st' ∧
  attacker_facts_ok infer st ∧
  local_facts_ok infer st ∧
  disjoint_keys st ∧
  finite_facts st ∧
  cut_elimination infer ∧ monotonic infer ⇒
  attacker_facts_ok infer st'
Proof
  Induct_on ‘step’ >> rpt conj_tac
  >~ [‘Produce’]
  >- (rw[attacker_facts_ok_def,local_facts_ok_def] >>
      imp_res_tac makeMsg_hash_lemma >> gvs[]
      >- (pop_assum mp_tac >>
          simp[Produce_def] >>
          ntac 7 $ simp[Once ainfer_cases] >>
          simp[IFact_def] >>
          strip_tac >>
          gvs[] >>
          res_tac >>
          gvs[] >>
          irule cut_elim_lemma2 >>
          simp[] >>
          last_assum $ irule_at $ Pat ‘infer _ _’ >>
          gvs[finite_facts_def] >>
          res_tac >> gvs[] >>
          gvs[SUBSET_DEF,IN_DEF]) >>
      last_x_assum irule >>
      first_assum $ irule_at $ Pos hd >>
      metis_tac[makeMsg_replay])
  >~ [‘FMAP_MAP2’] (* init *)
  >- (rw[attacker_facts_ok_def,local_facts_ok_def] >>
      res_tac >>
      gvs[TO_FLOOKUP] >>
      Cases_on ‘id = n’ >> gvs[] >>
      gvs[FLOOKUP_UPDATE]) >>
  rw[IMAGE_FRANGE,
     attacker_facts_ok_def,local_facts_ok_def,SF DNF_ss,FRANGE_FLOOKUP,
     FLOOKUP_FMAP_MAP2,
     FLOOKUP_UPDATE, AllCaseEqs()] >>
  gvs[] >>
  res_tac >>
  gvs[] >>
  metis_tac[makeMsg_ainfer]
QED

Theorem step_attacker_facts_ok:
  step infer st st' ∧
  step_inv infer st ∧
  cut_elimination infer ∧ monotonic infer ∧ assumption infer
  ⇒
  step_inv infer st'
Proof
  rw[step_inv_def] >>
  metis_tac[step_disjoint_keys,
            step_finite_facts,
            step_attacker_facts_ok_lem,
            step_local_facts_ok,
            step_incoming_messages_ok
           ]
QED
