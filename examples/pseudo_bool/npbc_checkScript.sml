(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble npbcTheory mlstringTheory mlintTheory;

val _ = new_theory "npbc_check";

val _ = numLib.prefer_num();

(* TODO: move *)
Theorem lookup_spt_size:
  ∀n x a. lookup n x = SOME a ⇒ ∀f. f a < spt_size f x
Proof
  recInduct lookup_ind \\ rw []
  \\ gvs [lookup_def,spt_size_def,AllCaseEqs()]
  \\ first_x_assum (qspec_then ‘f’ assume_tac) \\ fs []
QED

Theorem MEM_list_size:
  ∀xs x. MEM x xs ⇒ ∀f. f x < list_size f xs
Proof
  Induct \\ fs [list_size_def] \\ rw [] \\ fs [] \\ res_tac
  \\ first_x_assum (qspec_then ‘f’ assume_tac) \\ fs []
QED

(* pbp = pseudo-boolean proof format
  Below, nums represent ConstraintIds, which are 1-indexed (although 0s internally work fine)
*)

(* A constraint to be added by a cutting planes proof *)
Datatype:
  constr =
  | Id num              (* Constraints can refer to earlier IDs *)
  | Add constr constr   (* Add two constraints *)
  | Mul constr num      (* Multiply by a constant factor *)
  | Div constr num      (* Divide by a constant factor *)
  | Sat constr          (* Saturation *)
  | Lit (num lit)       (* Literal axiom lit ≥ 0 *)
  | Weak constr var     (* Addition of literal axioms until "var" disappears *)
End

(* Steps that preserve logical implication *)
Datatype:
  lstep =
  | Contradiction num (* Id representing a contradiction *)
  | Delete (num list) (* Ids to delete *)
  | Cutting constr    (* Adds a constraint using cutting planes, written in reverse polish notation *)
  | Con npbc (lstep list) (* Prove constraint by contradiction *)
  | Check num npbc    (* Debugging / other steps are parsed as no ops *)
  | NoOp              (* Other steps are parsed as no ops *)
End

Definition lstep_ok_def[simp]:
  (lstep_ok (Con n pfs) ⇔
    compact n ∧ (EVERY lstep_ok pfs)) ∧
  (lstep_ok _ ⇔ T)
Termination
  WF_REL_TAC ‘measure lstep_size’ \\ rw []
End

(*
  The type of PB formulas represented as a finite map
  num -> pbc
*)
Type pbf = ``:npbc spt``;

Definition check_cutting_def:
  (check_cutting fml (Id n) = lookup n fml) ∧
  (check_cutting fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting fml c1) (check_cutting fml c2)) ∧
  (check_cutting fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting fml c)) ∧
  (check_cutting fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_cutting fml c)
    else NONE) ∧
  (check_cutting fml (Sat c) =
    OPTION_MAP saturate (check_cutting fml c)) ∧
  (check_cutting fml (Lit (Pos v)) = SOME ([(1,v)],0)) ∧
  (check_cutting fml (Lit (Neg v)) = SOME ([(-1,v)],0)) ∧
  (check_cutting fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting fml c))
End

(* The result of a checking step is either:
  Fail        : proof step failed
  Unsat num   : unsatisfiability proved, continue with next ID
  Cont 'a num : continue with state 'a and next ID
*)
Datatype:
  pbpres = Unsat num | Fail | Cont 'a num
End

Definition check_lstep_def:
  (check_lstep lstep (core:num_set) (fml:pbf) (id:num) =
  case lstep of
    Contradiction n =>
    (case lookup n fml of
      NONE => Fail
    | SOME c =>
      if check_contradiction c
      then Unsat id
      else Fail)
  | Check n c =>
    if lookup n fml = SOME c
    then Cont fml id
    else Fail
  | NoOp => Cont fml id
  | Delete ls =>
    if EVERY (λid. lookup id core = NONE) ls
    then Cont (FOLDL (λa b. delete b a) fml ls) id
    else Fail
  | Cutting constr =>
    (case check_cutting fml constr of
      NONE => Fail
    | SOME c => Cont (insert id c fml) (id+1))
  | Con c pf =>
    let fml_not_c = insert id (not c) fml in
    (case check_lsteps pf core fml_not_c (id+1) of
      Unsat id' => Cont (insert id' c fml) (id'+1)
    | _ => Fail)) ∧
  (check_lsteps [] core fml id = Cont fml id) ∧
  (check_lsteps (step::steps) core fml id =
    case check_lstep step core fml id of
      Cont fml' id' => check_lsteps steps core fml' id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST) )’
End

Theorem check_cutting_correct:
  ∀fml n c w.
  check_cutting fml n = SOME c ∧ satisfies w (range fml) ⇒
  satisfies_npbc w c
Proof
  Induct_on`n`>>rw[check_cutting_def]
  >- (
    (*Id case*)
    fs[satisfies_def,range_def]>>metis_tac[])
  >- (
    (* add case *)
    match_mp_tac add_thm>>
    metis_tac[])
 >- (
    (* multiply case *)
    match_mp_tac multiply_thm>>
    metis_tac[])
  >- (
    (* divide case *)
    match_mp_tac divide_thm>>
    metis_tac[])
  >- (
    (* saturate case *)
    match_mp_tac saturate_thm>>
    metis_tac[])
  >- (
    (* literal case *)
    Cases_on`l`>>fs[check_cutting_def]>>rveq>>
    EVAL_TAC)
  >- (
    (* weaken case *)
    match_mp_tac weaken_thm>>
    metis_tac[])
QED

Theorem check_cutting_compact:
  ∀n c.
  (∀c. c ∈ range fml ⇒ compact c) ∧
  check_cutting fml n = SOME c ⇒
  compact c
Proof
  Induct_on`n`>>rw[check_cutting_def]
  >- (
    (*Id case*)
    fs[range_def]>>metis_tac[])
  >- (
    (* add case *)
    metis_tac[compact_add])
 >- (
    (* multiply case *)
    metis_tac[compact_multiply])
  >- (
    metis_tac[compact_divide])
  >- (
    metis_tac[compact_saturate])
  >- (
    (* literal case *)
    Cases_on`l`>>fs[check_cutting_def]>>rveq>>
    EVAL_TAC)
  >- (
    (* weaken case *)
    metis_tac[compact_weaken])
QED

Definition id_ok_def:
  id_ok fml id = ∀n. id ≤ n ⇒ n ∉ domain fml
End

Theorem sat_implies_refl[simp]:
  fml ⊨ fml
Proof
  rw[sat_implies_def]
QED

Theorem range_FOLDL_delete:
  ∀ls v.
  range (FOLDL (λa b. delete b a) v ls) ⊆ range v
Proof
  Induct>>rw[]>>
  first_x_assum (qspec_then`delete h v` mp_tac)>>rw[]>>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>>simp[]>>
  simp[range_delete]
QED

Theorem sat_implies_subset:
  s ⊆ t ⇒
  t ⊨ s
Proof
  rw[sat_implies_def,satisfies_def,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem satisfiable_subset:
  satisfiable t ∧ s ⊆ t ⇒
  satisfiable s
Proof
  rw[satisfiable_def,SUBSET_DEF,satisfies_def]>>
  metis_tac[]
QED

Theorem id_ok_insert_1:
  id_ok fml id ⇒
  id_ok (insert id c fml) (id+1)
Proof
  rw[id_ok_def]
QED

Theorem inter_insert_NOTIN:
  id ∉ domain core ⇒
  inter (insert id x fml) core =
  inter fml core
Proof
  rw[inter_def,lookup_inter,lookup_insert,domain_lookup]>>
  every_case_tac>>fs[]
QED

Theorem domain_FOLDL_delete:
  ∀ls v.
  domain (FOLDL (λa b. delete b a) v ls) =
    (domain v) DIFF set ls
Proof
  Induct>>rw[]>>
  simp[DIFF_INSERT]
QED

Theorem id_ok_FOLDL_delete:
  ∀l fml.
  id_ok fml id ⇒
  id_ok (FOLDL (λa b. delete b a) fml l) id
Proof
  Induct \\ fs[] \\ rw[]
  \\ first_x_assum irule
  \\ fs [id_ok_def,domain_delete]
QED

Theorem lookup_inter_FOLDL_delete:
  ∀l fml.
  EVERY (λid. lookup id core = NONE) l ⇒
  lookup x (inter (FOLDL (λa b. delete b a) fml l) core) =
  lookup x (inter fml core)
Proof
  Induct>>rw[]>>
  simp[lookup_inter,lookup_delete]>>
  every_case_tac>>fs[]
QED

Theorem check_lstep_correct:
  (∀step core fml id.
     id_ok fml id ∧ domain core ⊆ domain fml ⇒
     case check_lstep step core fml id of
     | Cont fml' id' =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         domain core ⊆ domain fml' ∧
         inter fml' core = inter fml core ∧
         range fml ⊨ range fml'
     | Unsat id' =>
         id ≤ id' ∧
         ¬ satisfiable (range fml)
     | Fail => T) ∧
  (∀steps core fml id.
     id_ok fml id ∧ domain core ⊆ domain fml ⇒
     case check_lsteps steps core fml id of
     | Cont fml' id' =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         domain core ⊆ domain fml' ∧
         inter fml' core = inter fml core ∧
         range fml ⊨ range fml'
     | Unsat id' =>
         id ≤ id' ∧
          ¬ satisfiable (range fml)
     | Fail => T)
Proof
  ho_match_mp_tac check_lstep_ind \\
  reverse (rpt strip_tac)
  >- (
    simp[Once check_lstep_def]>>
    every_case_tac>>gs[]>>
    metis_tac[sat_implies_def,satisfiable_def])
  >- simp[Once check_lstep_def]
  \\ Cases_on ‘∃n. step = Contradiction n’
  THEN1 (
    rw[check_lstep_def] \\ every_case_tac \\ fs [] >>
    rw[satisfiable_def,range_def,satisfies_def]>>
    drule check_contradiction_unsat>>
    metis_tac[])
  \\ Cases_on ‘∃n c. step = Check n c’
  THEN1
   (rw[check_lstep_def] \\ every_case_tac \\ fs [] \\ metis_tac[sat_implies_refl])
  \\ Cases_on ‘∃n. step = Delete n’
  THEN1 (
    rw[check_lstep_def] \\ every_case_tac \\ rw []
    >- metis_tac[id_ok_FOLDL_delete]
    >- (
      fs[domain_FOLDL_delete,SUBSET_DEF]>>
      rw[]>>first_x_assum drule>>
      fs[EVERY_MEM,domain_lookup]>>
      metis_tac[option_CLAUSES])
    >- metis_tac[lookup_inter_FOLDL_delete]>>
    match_mp_tac sat_implies_subset>>
    fs[range_FOLDL_delete])
  \\ Cases_on ‘step = NoOp’ >- simp[check_lstep_def]
  \\ Cases_on ‘∃c. step = Cutting c’
  THEN1 (
    rw[check_lstep_def] \\ every_case_tac \\ rw []
    >- fs [id_ok_def]
    >- fs[SUBSET_DEF]
    >- (
      DEP_REWRITE_TAC[inter_insert_NOTIN]>>
      fs[id_ok_def,SUBSET_DEF]>>
      last_x_assum(qspec_then`id` assume_tac)>>fs[]>>
      metis_tac[])>>
    drule check_cutting_correct>>
    fs[satisfiable_def,satisfies_def]>>
    ‘id ∉ domain fml’ by fs [id_ok_def]  >>
    simp[sat_implies_def,satisfies_def]>>
    fs [range_insert,SUBSET_DEF]>>
    metis_tac[] )
  (* Proof by contradiction *)
  \\ Cases_on ‘∃c steps. step = Con c steps’
  THEN1 (
    fs[check_lstep_def]
    \\ every_case_tac \\ gs[id_ok_insert_1]
    \\ fs[SUBSET_DEF]
    \\ `id_ok fml n` by fs[id_ok_def]
    \\ fs[sat_implies_def,satisfies_def]
    \\ `n ∉ domain fml’ by fs [id_ok_def]
    \\ simp[id_ok_insert_1, range_insert]
    \\ CONJ_TAC >- (
      DEP_REWRITE_TAC[inter_insert_NOTIN]>>
      fs[id_ok_def,SUBSET_DEF]>>
      last_x_assum(qspec_then`id` assume_tac)>>fs[]>>
      metis_tac[])
    \\ fs[satisfiable_def,range_insert,id_ok_def,not_thm]
    \\ metis_tac[satisfies_def])
  THEN1 (
    rw[Once check_lstep_def]
    \\ every_case_tac \\ gvs [])
QED

Theorem check_lstep_compact:
  (∀step core fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ lstep_ok step ∧
     check_lstep step core fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀steps core fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ EVERY lstep_ok steps ∧
     check_lsteps steps core fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c))
Proof
  ho_match_mp_tac check_lstep_ind \\ reverse (rw [])
  >- (
    qpat_x_assum`_ = Cont _ _` mp_tac>>
    simp[Once check_lstep_def]>>
    every_case_tac>>fs[])
  >- fs[Once check_lstep_def]>>
  Cases_on`step`>>fs[check_lstep_def]>>
  every_case_tac>>rw[]
  >- metis_tac[range_FOLDL_delete,SUBSET_DEF]
  >- (drule range_insert_2>>rw[]>>
      metis_tac[check_cutting_compact])
  \\ imp_res_tac range_insert_2 \\ gvs []
QED

Type subst = ``:(bool + num lit) num_map``;

(* Steps that preserve satisfiability *)
Datatype:
  sstep =
  | Lstep lstep (* Id representing a contradiction *)
  | Red npbc subst
    (( (num + unit) option,lstep list) alist)
    (* Ordered list of proofs for subgoals
      NONE -> global subproof steps
      SOME () -> the (currently) unique specific subgoal for Red
      SOME n -> the subgoal for constraint id n
    *)
End

(* Apply a substitution where needed *)
Definition extract_clauses_def:
  (extract_clauses f def fml [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses f def fml (cpf::pfs) acc =
    case cpf of
      (NONE,pf) => extract_clauses f def fml pfs ((NONE,pf)::acc)
    | (SOME (INL n),pf) =>
      (case lookup n fml of
        NONE => NONE
      | SOME c => extract_clauses f def fml pfs ((SOME (subst f c),pf)::acc))
    | (SOME (INR u),pf) =>
      extract_clauses f def fml pfs ((SOME (subst f def),pf)::acc))
End

Theorem extract_clauses_MAP_SND:
  ∀f def fml pfs acc res.
  extract_clauses f def fml pfs acc = SOME res ⇒
  MAP SND res =  REVERSE (MAP SND acc) ++ MAP SND pfs
Proof
  Induct_on`pfs`>>rw[extract_clauses_def] >> simp[MAP_REVERSE]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  rw[]
QED

(* TODO: could use Cont to return fml if needed...
  But I think we just throw away the fml even for dominance *)
Definition check_red_def:
  (check_red [] core fml id = SOME id) ∧
  (check_red ((copt,pf)::pfs) core fml id =
    case copt of
      NONE => (* no clause given *)
      (case check_lsteps pf core fml id of
        Cont fml' id' => check_red pfs core fml' id'
      | res => NONE)
    | SOME c =>
      (let cfml = insert id (not c) fml in
      case check_lsteps pf core cfml (id+1) of
        Unsat id' => check_red pfs core fml id'
      | res => NONE))
End

Definition subst_fun_def:
  subst_fun (s:subst) n = lookup n s
End

Definition map_opt_def:
  map_opt f LN = LN ∧
  map_opt f (LS x) = (case f x of NONE => LN | SOME a => LS a) ∧
  map_opt f (BN t1 t2) = mk_BN (map_opt f t1) (map_opt f t2) ∧
  map_opt f (BS t1 x t2) =
    case f x of
    | NONE => mk_BN (map_opt f t1) (map_opt f t2)
    | SOME a => mk_BS (map_opt f t1) a (map_opt f t2)
End

Definition check_sstep_def:
  (check_sstep sstep core (fml:pbf) (id:num) =
  case sstep of
    Lstep lstep =>
    check_lstep lstep core fml id
  | Red c s pfs =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      case extract_clauses w c fml pfs [] of
        NONE => Fail
      | SOME cpfs =>
      (case check_red cpfs core fml_not_c (id+1) of
        SOME id' =>
        let goals = MAP FST (toAList (map_opt (subst_opt w) fml)) in
        let pids = MAP FST pfs in (* optimize and change later *)
          if MEM (SOME (INR ())) pids ∧
            EVERY (λid. MEM (SOME (INL id)) pids) goals then
            Cont (insert id' c fml) (id'+1)
          else Fail
      | _ => Fail) ))
End

Theorem sat_implies_transitive:
  fml ⊨ fml' ∧ fml' ⊨ fml'' ⇒
  fml ⊨ fml''
Proof
  rw[sat_implies_def]
QED

Theorem unsat_iff_implies:
  ¬satisfiable (not x INSERT fml) ⇔ fml ⊨ {x}
Proof
  fs [sat_implies_def,satisfiable_def,not_thm]
  \\ metis_tac []
QED

Theorem check_red_correct:
  ∀pfs core fml id.
    id_ok fml id ∧ domain core ⊆ domain fml ⇒
    case check_red pfs core fml id of
      SOME id' =>
       id ≤ id' ∧
       EVERY (λ(copt,pf).
         case copt of
           NONE => T
         | SOME c => range fml ⊨ {c}
       ) pfs
    | NONE => T
Proof
  Induct>-rw[check_red_def]>>
  Cases>>rw[check_red_def]>>
  Cases_on`q`>>fs[]
  >- (
    every_case_tac>>fs[]>>
    drule (CONJUNCT2 check_lstep_correct)>>
    disch_then (qspecl_then[`r`,`core`] assume_tac)>>
    gs[]>>
    first_x_assum drule>>simp[]>>
    disch_then drule>>
    rw[]>>
    pop_assum mp_tac>>
    match_mp_tac MONO_EVERY>>
    Cases>>simp[]>>every_case_tac>>
    metis_tac[sat_implies_transitive])>>
  every_case_tac>>fs[]>>
  `id_ok (insert id (not x) fml) (id + 1)` by
    fs[id_ok_def]>>
  drule (CONJUNCT2 check_lstep_correct)>>
  disch_then (qspecl_then[`r`,`core`] assume_tac)>>
  gs[SUBSET_DEF]>>
  `id_ok fml n` by
    fs[id_ok_def]>>
  first_x_assum drule>>
  disch_then drule>>
  simp[]>>
  gs[range_insert,id_ok_def,unsat_iff_implies]
QED

Theorem implies_explode:
  a ⊨ s ⇔ ∀c. c ∈ s ⇒ a ⊨ {c}
Proof
  fs [sat_implies_def,satisfies_def]
  \\ metis_tac []
QED

Theorem extract_clauses_MEM_acc:
  ∀s def fml pfs acc res c pf.
  extract_clauses s def fml pfs acc = SOME res ∧
  MEM (SOME c,pf) acc ⇒
  MEM (SOME c,pf) res
Proof
  Induct_on`pfs`>>fs[extract_clauses_def]>>rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem extract_clauses_MEM_INL:
  ∀s fml pfs acc res id pf.
  extract_clauses s def fml pfs acc = SOME res ∧
  MEM (SOME (INL id), pf) pfs ⇒
  ∃c.
    lookup id fml = SOME c ∧
    MEM (SOME (subst s c),pf) res
Proof
  Induct_on`pfs`>>rw[extract_clauses_def]>>fs[]>>
  every_case_tac>>fs[]
  >- (
    drule extract_clauses_MEM_acc>>
    simp[]) >>
  metis_tac[]
QED

Theorem extract_clauses_MEM_INR:
  ∀s fml pfs acc res pf.
  extract_clauses s def fml pfs acc = SOME res ∧
  MEM (SOME (INR u), pf) pfs ⇒
  MEM (SOME (subst s def),pf) res
Proof
  Induct_on`pfs`>>rw[extract_clauses_def]>>fs[]>>
  every_case_tac>>fs[]
  >- (
    drule extract_clauses_MEM_acc>>
    simp[]) >>
  metis_tac[]
QED

Theorem lookup_mk_BS:
  lookup i (mk_BS t1 a t2) = lookup i (BS t1 a t2)
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ fs [mk_BS_def,lookup_def]
QED

Theorem lookup_map_opt:
  ∀n t f.
    lookup n (map_opt f t) =
    case lookup n t of
    | NONE => NONE
    | SOME x => f x
Proof
  recInduct lookup_ind \\ fs [map_opt_def,lookup_def] \\ rw []
  \\ rpt (fs [lookup_def,lookup_mk_BN,lookup_mk_BS] \\ CASE_TAC)
QED

Theorem check_sstep_correct:
  ∀step core fml id.
  id_ok fml id ∧ domain core ⊆ domain fml ⇒
  case check_sstep step core fml id of
  | Cont fml' id' =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      domain core ⊆ domain fml' ∧
      inter fml' core = inter fml core ∧
      (satisfiable (range fml) ⇒ satisfiable (range fml'))
  | Unsat id' =>
      id ≤ id' ∧
       ¬ satisfiable (range fml)
  | Fail => T
Proof
  Cases>>rw[check_sstep_def]
  >- (
    drule (CONJUNCT1 check_lstep_correct)>>
    disch_then(qspecl_then [`l`,`core`] assume_tac)>>
    every_case_tac>>fs[]>>
    fs[satisfiable_def,sat_implies_def]>>
    metis_tac[])
  >- ( (* Red *)
    every_case_tac>>
    gs[id_ok_insert_1]>>
    `id_ok (insert id (not p) fml) (id + 1)` by
      fs[id_ok_def]>>
    drule check_red_correct>>
    disch_then(qspecl_then [`x`,`core`] assume_tac)>>
    gs[SUBSET_DEF]>>
    CONJ_TAC>-
      gvs[id_ok_def,SUBSET_DEF]>>
    CONJ_TAC>- (
      DEP_REWRITE_TAC[inter_insert_NOTIN]>>
      fs[id_ok_def]>>
      last_x_assum(qspec_then`id` assume_tac)>>
      fs[]>>
      metis_tac[])>>
    rename1`insert id' c fml`>>
    qsuff_tac ‘c redundant_wrt (range fml)’
    >- (
      fs [redundant_wrt_def] \\ rw []
      \\ irule satisfiable_subset
      \\ pop_assum $ irule_at Any
      \\ rw [SUBSET_DEF] \\ imp_res_tac range_insert_2 \\ fs [])
    \\ rw[substitution_redundancy]
    \\ qexists_tac ‘subst_fun s’ \\ fs []
    \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]
    \\ `id ∉ domain fml` by fs[id_ok_def]
    \\ fs[range_insert]
    \\ simp [Once implies_explode] \\ reverse (rw [])
    THEN1 (
      drule extract_clauses_MEM_INR
      \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ first_x_assum drule
      \\ simp[]
      \\ fs[lookup_insert]
      \\ simp[Once INSERT_SING_UNION,UNION_COMM])
    \\ gvs [GSYM unsat_iff_implies]
    \\ pop_assum mp_tac
    \\ simp [Once range_def] \\ rw []
    \\ rename [‘lookup a fml = SOME xx’]
    \\ fs [MEM_toAList,lookup_map_opt,CaseEq"option",PULL_EXISTS]
    \\ last_x_assum drule
    \\ Cases_on ‘subst_opt (subst_fun s) xx’ \\ fs []
    THEN1
     (imp_res_tac subst_opt_NONE
      \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
      \\ fs [satisfies_def,range_def,PULL_EXISTS]
      \\ metis_tac[])
    \\ Cases_on`x'` \\ fs[]
    \\ strip_tac
    \\ drule extract_clauses_MEM_INL
    \\ disch_then drule
    \\ strip_tac
    \\ first_x_assum drule
    \\ gvs[]
    \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
QED

Definition sstep_ok_def[simp]:
  (sstep_ok (Lstep l) ⇔ lstep_ok l) ∧
  (sstep_ok (Red n _ pfs) ⇔
    compact n)
  (* TODO: should this be added?
  it checks that the subproofs are compact...
  ∧ EVERY (EVERY lstep_ok) (MAP SND pfs)) *)
End

Theorem check_sstep_compact:
  ∀sstep core fml id fml' id'.
  (∀c. c ∈ range fml ⇒ compact c) ∧ sstep_ok sstep ∧
  check_sstep sstep core fml id = Cont fml' id' ⇒
  (∀c. c ∈ range fml' ⇒ compact c)
Proof
  Cases>>rw[]>>fs[check_sstep_def]
  >-
    metis_tac[check_lstep_compact] >>
  every_case_tac>>gvs[]>>
  drule range_insert_2>>rw[]>>
  metis_tac[]
QED

(* Top-level unsat checkers and optimality checkers
  ...
*)
Definition check_ssteps_def:
  (check_ssteps [] core fml id = Cont fml id) ∧
  (check_ssteps (s::ss) core fml id =
    case check_sstep s core fml id of
      Cont fml' id' => check_ssteps ss core fml' id'
    | res => res)
End

Theorem check_ssteps_correct:
  ∀ss core fml id.
  id_ok fml id ∧ domain core ⊆ domain fml ⇒
  case check_ssteps ss core fml id of
  | Cont fml' id' =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      domain core ⊆ domain fml' ∧
      inter fml' core = inter fml core ∧
      (satisfiable (range fml) ⇒ satisfiable (range fml'))
  | Unsat id' =>
     id ≤ id' ∧
      ¬ satisfiable (range fml)
  | Fail => T
Proof
  Induct>>rw[check_ssteps_def]>>
  drule check_sstep_correct>>
  disch_then(qspecl_then [`h`,`core`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  rw[]>>
  first_x_assum drule>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]>>
  rw[]>>
  fs[npbcTheory.satisfiable_def]
QED

(* Top-level steps that manipulate the core *)
Datatype:
  cstep =
  | Transfer (num list) (* Ids to move into core *)
  | CheckedDelete (num list) ((num,sstep list) alist)
    (* Checked deletion with proofs *)
  | Sstep sstep
End

Definition coref_def:
  coref (core:num_set) fml =
    mapi (λk v.
      case lookup k fml of NONE => ([],0):npbc | SOME res => res) core
End

Definition check_del_def:
  (check_del [] cf id = SOME id) ∧
  (check_del ((n,pf)::pfs) cf id =
    case lookup n cf of
      NONE => NONE
    | SOME c =>
      (let ncf = delete n cf in
      let cfml = insert id (not c) ncf in
      case check_ssteps pf LN cfml (id+1) of
        Unsat id' => check_del pfs ncf id'
      | res => NONE))
End

Definition hide_def:
  hide x = x
End

Theorem range_delete_IN:
  lookup n f = SOME c ∧ c' ∈ range f ⇒
  c = c' ∨ c' ∈ range (delete n f)
Proof
  rw[range_def,lookup_delete]>>
  Cases_on `n' = n`>>fs[]>>
  metis_tac[]
QED

Theorem check_del_correct:
  ∀pfs cf id id'.
  id_ok cf id ∧
  check_del pfs cf id = SOME id' ⇒
    hide (id ≤ id' ∧
    set (MAP FST pfs) ⊆ domain cf ∧
    (satisfiable
      (range (FOLDL (λa b. delete b a) cf (MAP FST pfs))) ⇒
    satisfiable (range cf)))
Proof
  ho_match_mp_tac check_del_ind>>
  rw[check_del_def]
  >-
    simp[hide_def]>>
  every_case_tac>>gs[]>>
  `id_ok (delete n cf) id` by fs[id_ok_def]>>
  drule id_ok_insert_1>>
  disch_then (qspec_then `not x` assume_tac)>>
  drule check_ssteps_correct>>
  disch_then (qspecl_then [`pf`,`LN`] assume_tac)>>
  gs[]>>
  qpat_x_assum`_ ⇒ _` mp_tac>>
  impl_tac >-
    fs[id_ok_def]>>
  simp[hide_def]>> strip_tac >>
  CONJ_TAC >-
    fs[domain_lookup,SUBSET_DEF]>>
  strip_tac>>
  fs[satisfiable_def]>>
  qexists_tac`w`>>fs[satisfies_def]>>
  qpat_x_assum`!w. ∃c. _` mp_tac>>
  DEP_REWRITE_TAC[range_insert]>>
  CONJ_TAC >-
    fs[domain_delete,id_ok_def]>>
  rw[]>>
  drule range_delete_IN>>
  disch_then drule>>
  metis_tac[not_thm]
QED

Definition check_cstep_def:
  (check_cstep cstep core (fml:pbf) (id:num) =
  case cstep of
    Transfer ls =>
    if EVERY (λid. lookup id fml ≠ NONE) ls
    then Cont (FOLDL (λa b. insert b () a) core ls, fml) id
    else Fail
  | CheckedDelete ls pfs =>
    let cdel = FILTER (λid. lookup id core ≠ NONE) ls in
    if cdel = [] then
      Cont (core, FOLDL (λa b. delete b a) fml ls) id
    else (
      let cf = coref core fml in
      case check_del pfs cf id of NONE => Fail
      | SOME id' =>
      let pids = MAP FST pfs in (* optimize and change later *)
      if EVERY (λid. MEM id pids) cdel then
        Cont (FOLDL (λa b. delete b a) core cdel,
              FOLDL (λa b. delete b a) fml ls) id'
      else Fail)
  | Sstep sstep =>
    (case check_sstep sstep core fml id of
      Cont fml' id' => Cont (core,fml') id'
    | Unsat id => Unsat id
    | Fail => Fail)
  )
End

(* TODO: Update for objective rule *)
Definition valid_conf_def:
  valid_conf core fml ⇔
  domain core ⊆ domain fml ∧
  ∀w.
    satisfies w (range (coref core fml)) ⇒
    ∃w'. satisfies w' (range fml)
End

Theorem domain_coref:
  domain (coref core fml) =
  domain core
Proof
  rw[coref_def]
QED

Theorem range_coref_SUBSET:
  domain core ⊆ domain fml ⇒
  range (coref core fml) ⊆ range fml
Proof
  rw[coref_def,SUBSET_DEF,range_def]>>
  fs[lookup_mapi,domain_lookup]>>
  first_x_assum drule>>
  rw[]>>
  fs[]>>
  metis_tac[]
QED

Theorem range_coref_insert:
  lookup h fml = SOME c ⇒
  range (coref (insert h () core) fml) =
  c INSERT range (coref core fml)
Proof
  rw[coref_def]>>
  fs[range_def]>>
  rw[EXTENSION,EQ_IMP_THM]>>
  fs[lookup_mapi]>>rw[]>>
  fs[lookup_insert]
  >- (
    every_case_tac>>fs[]>>
    DISJ2_TAC>>
    first_x_assum (irule_at Any)>>
    simp[])
  >-
    (qexists_tac`h`>>simp[])
  >>
    qexists_tac`n`>>simp[]
QED

Theorem range_coref_FOLDL_insert:
  ∀l core.
  EVERY (λid. lookup id fml ≠ NONE) l ⇒
  range (coref (FOLDL (λa b. insert b () a) core l) fml) =
  set (MAP (λid. THE (lookup id fml)) l) ∪ range (coref core fml)
Proof
  Induct>>rw[]>>fs[]>>
  `?c. lookup h fml = SOME c` by
    metis_tac[option_CLAUSES]>>
  DEP_REWRITE_TAC[range_coref_insert]>>
  simp[]>>
  simp[EXTENSION]>>
  metis_tac[]
QED

Theorem range_coref_cong:
  (∀x. lookup x (inter a core) = lookup x (inter fml core))
  ⇒
  range (coref core fml) = range (coref core a)
Proof
  rw[range_def,coref_def,lookup_mapi,EXTENSION,EQ_IMP_THM]>>
  asm_exists_tac>>simp[]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  gs[lookup_inter]>>
  rpt(TOP_CASE_TAC>>fs[])
QED

Theorem range_coref_delete:
  h ∉ domain core ⇒
  range (coref core (delete h fml)) =
  range (coref core fml)
Proof
  rw[coref_def]>>
  fs[range_def]>>
  rw[EXTENSION,EQ_IMP_THM]>>
  fs[lookup_mapi]>>rw[]>>
  fs[lookup_delete]>>
  asm_exists_tac>>fs[domain_lookup]>>
  IF_CASES_TAC>>fs[]
QED

Theorem range_coref_FOLDL_delete:
  ∀l fml.
  domain core ⊆ domain fml DIFF set l ⇒
  range (coref core (FOLDL (λa b. delete b a) fml l)) =
  range (coref core fml)
Proof
  Induct>>rw[]>>fs[DIFF_INSERT]>>
  match_mp_tac range_coref_delete>>
  fs[SUBSET_DEF]>>
  metis_tac[]
QED

Theorem valid_conf_FOLDL_delete:
  valid_conf core fml ∧
  EVERY (λid. id ∉ domain core) l ⇒
  valid_conf core (FOLDL (λa b. delete b a) fml l)
Proof
  strip_tac>>
  fs[valid_conf_def,domain_FOLDL_delete]>>
  CONJ_ASM1_TAC >- (
    fs[SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM,domain_lookup]>>
    metis_tac[option_CLAUSES])>>
  DEP_REWRITE_TAC [range_coref_FOLDL_delete]>>
  simp[]>>
  rw[]>>first_x_assum drule>>
  rw[]>>
  qexists_tac`w'`>>
  fs[satisfies_def]>>
  metis_tac[range_FOLDL_delete,SUBSET_DEF]
QED

Theorem valid_conf_del_core:
  valid_conf core fml ∧
  domain coreS ⊆ domain core ∧
  (satisfiable (range (coref coreS fml)) ⇒
  satisfiable (range (coref core fml)))
  ⇒
  valid_conf coreS fml
Proof
  rw[valid_conf_def]
  >- fs[SUBSET_DEF]>>
  first_x_assum match_mp_tac>>
  fs[satisfiable_def]>>
  first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem satisfies_SUBSET:
  Y ⊆ X ⇒
  (satisfies w X ⇒ satisfies w Y)
Proof
  rw[satisfies_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem satisfiable_SUBSET:
  Y ⊆ X ⇒
  (satisfiable X ⇒ satisfiable Y)
Proof
  rw[satisfiable_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem delete_coref:
  delete h (coref core fml) =
  coref (delete h core) fml
Proof
  rw[coref_def]>>
  DEP_REWRITE_TAC[spt_eq_thm]>>
  simp[lookup_delete,lookup_mapi]>>rw[]>>
  fs[wf_mapi]>>
  match_mp_tac wf_delete>>
  fs[wf_mapi]
QED

Theorem range_FOLDL_delete_coref:
  ∀ls core.
  range (FOLDL (\a b. delete b a) (coref core fml) ls) =
  range (coref (FOLDL (\a b. delete b a) core ls) fml)
Proof
  Induct>>rw[]>>
  simp[delete_coref]
QED

Theorem range_coref_SUBSET_core:
  domain core ⊆ domain core' ⇒
  range (coref core fml) ⊆
  range (coref core' fml)
Proof
  rw[coref_def,SUBSET_DEF,range_def]>>
  fs[lookup_mapi,domain_lookup]>>
  first_x_assum drule>>
  rw[]>>
  metis_tac[]
QED

Theorem check_cstep_correct:
  ∀cstep core fml id.
  id_ok fml id ∧
  valid_conf core fml ⇒
  case check_cstep cstep core fml id of
  | Cont (core',fml') id' =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      valid_conf core' fml' ∧
      (satisfiable (range (coref core fml)) ⇔
       satisfiable (range (coref core' fml')))
  | Unsat id' =>
      id ≤ id' ∧
       ¬ satisfiable (range fml)
  | Fail => T
Proof
  Cases>>fs[check_cstep_def]
  >- (
    (* Transfer *)
    ntac 4 strip_tac>>
    IF_CASES_TAC>>fs[valid_conf_def]>>
    simp[GSYM CONJ_ASSOC]>>
    CONJ_TAC
    >- (
      pop_assum mp_tac>>
      Induct_on`l`>>simp[domain_lookup]>>
      metis_tac[option_CLAUSES])>>
    DEP_REWRITE_TAC[range_coref_FOLDL_insert]>>
    fs[satisfiable_def]>>
    CONJ_TAC >-
      metis_tac[]>>
    simp[EQ_IMP_THM]>>
    reverse CONJ_TAC>-
      metis_tac[]>>
    strip_tac>>first_x_assum drule>>
    rw[]>>
    drule range_coref_SUBSET>>
    rw[]>>fs[SUBSET_DEF,satisfies_def]>>
    qexists_tac`w'`>>
    fs[MEM_MAP,EVERY_MEM]>>rw[]>>
    first_x_assum drule>>
    fs[range_def]>>
    metis_tac[option_CLAUSES])
  >- (
    (* CheckedDelete *)
    ntac 4 strip_tac>>
    IF_CASES_TAC >- (
      (* Simple case *)
      simp[]>>
      CONJ_TAC >- metis_tac[id_ok_FOLDL_delete] >>
      CONJ_TAC >- (
        match_mp_tac valid_conf_FOLDL_delete>>
        fs[FILTER_EQ_NIL,EVERY_MEM,domain_lookup] )>>
      AP_TERM_TAC>>
      match_mp_tac range_coref_cong>>
      strip_tac>>
      match_mp_tac lookup_inter_FOLDL_delete>>
      fs[FILTER_EQ_NIL])>>
    (* Actual checked deletion *)
    every_case_tac>>simp[]>>
    `id_ok (coref core fml) id` by (
      fs[id_ok_def,domain_coref,valid_conf_def]>>
      metis_tac[SUBSET_DEF])>>
    drule check_del_correct>>
    disch_then drule>>
    strip_tac>>fs[hide_def,range_FOLDL_delete_coref]>>
    CONJ_TAC >- (
      `id_ok fml x` by fs[id_ok_def]>>
      metis_tac[id_ok_FOLDL_delete]) >>
    qmatch_goalsub_abbrev_tac`_ ⇔ satisfiable (range (coref coreS _))`>>
    qmatch_asmsub_abbrev_tac`range (coref coreT _)`>>
    `satisfiable (range (coref coreS fml)) ⇒
     satisfiable (range (coref coreT fml))` by
      (unabbrev_all_tac>>
      match_mp_tac satisfiable_SUBSET>>
      match_mp_tac range_coref_SUBSET_core>>
      simp[domain_FOLDL_delete,SUBSET_DEF]>>
      fs[FILTER_EQ_NIL,EVERY_MEM,MEM_FILTER,MEM_MAP,domain_lookup]>>
      metis_tac[option_CLAUSES])>>
    CONJ_TAC >- (
      fs[Abbr`coreS`]>>
      match_mp_tac valid_conf_FOLDL_delete >>
      simp[domain_FOLDL_delete]>>
      reverse CONJ_TAC >- (
        fs[MEM_FILTER,domain_lookup,FILTER_EQ_NIL,EVERY_MEM])>>
      match_mp_tac valid_conf_del_core>>
      fs[domain_FOLDL_delete])>>
    `satisfiable (range (coref core fml)) ⇔
     satisfiable (range (coref coreS fml))` by (
      fs[EQ_IMP_THM,satisfiable_def]>>
      rw[]>>
      qexists_tac`w`>>pop_assum mp_tac>>
      match_mp_tac satisfies_SUBSET>>
      unabbrev_all_tac>>
      match_mp_tac range_coref_SUBSET_core>>
      simp[domain_FOLDL_delete] )>>
    simp[]>>
    AP_TERM_TAC>>
    match_mp_tac range_coref_cong>>
    strip_tac>>
    match_mp_tac lookup_inter_FOLDL_delete>>
    simp[EVERY_MEM,Abbr`coreS`,lookup_NONE_domain,domain_FOLDL_delete,MEM_FILTER])
  >- (
    (* Sstep *)
    ntac 4 strip_tac>>
    drule check_sstep_correct>>
    fs[valid_conf_def]>>
    disch_then drule>>
    disch_then (qspec_then`s` mp_tac)>>
    TOP_CASE_TAC>>fs[]>>
    strip_tac>>
    imp_res_tac range_coref_SUBSET>>
    drule range_coref_cong>>
    rw[]>>gs[]>>
    fs[satisfiable_def,SUBSET_DEF,satisfies_def]>>
    metis_tac[])
QED

Definition build_fml_def:
  (build_fml (id:num) [] = LN) ∧
  (build_fml id (cl::cls) =
    insert id cl (build_fml (id+1) cls))
End

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml n ls) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls)
  else NONE
Proof
  Induct>>rw[build_fml_def,lookup_def,lookup_insert]>>
  `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem domain_build_fml:
  ∀ls id.
  domain (build_fml id ls) = {i | id ≤ i ∧ i < id + LENGTH ls}
Proof
  Induct>>rw[build_fml_def,EXTENSION]
QED

Theorem range_build_fml:
  ∀ls id. range (build_fml id ls) = set ls
Proof
  Induct>>fs[build_fml_def,range_def,lookup_def]>>
  fs[EXTENSION]>>
  rw[lookup_insert]>>
  rw[EQ_IMP_THM]
  >- (
    every_case_tac>>fs[]>>
    metis_tac[])
  >- metis_tac[] >>
  first_x_assum(qspecl_then[`id+1`,`x`] mp_tac)>>
  rw[]>>
  fs[lookup_build_fml]>>
  qexists_tac`n`>>simp[]
QED

val _ = export_theory ();
