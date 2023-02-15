(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble npbcTheory mlstringTheory mlintTheory;

val _ = new_theory "npbc_check";

val _ = numLib.prefer_num();

(* Proof steps are classified in a hierachy of three descending levels

  "Core" steps csteps
    |
    |--> "SAT" steps ssteps
            |
            |--> "Logical" steps lsteps

  lstep: These steps preserve logical implication for F = C U D
         Includes cutting planes and contradiction proof steps
         Deletions allowed in D only

  sstep: These steps preserve satisfiability of F = C U D
         Includes redundancy, and redundancy subproofs can only use lsteps

  cstep: These steps manipulate the core
         Includes objective updates, core transfer, checked deletion, dominance (TODO)
*)

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
  | Delete (num list) (* Ids to delete *)
  | Cutting constr    (* Adds a constraint using cutting planes, written in reverse polish notation *)
  | Con npbc (lstep list) num
    (* Prove constraint by contradiction, indicated by the id *)
  | Check num npbc
    (* Debugging / other steps are parsed as no ops *)
  | NoOp              (* Other steps are parsed as no ops *)
End

Definition lstep_ok_def[simp]:
  (lstep_ok (Con c pfs n) ⇔
    compact c ∧ (EVERY lstep_ok pfs)) ∧
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

Definition check_contradiction_fml_def:
  check_contradiction_fml fml n =
  (case lookup n fml of
      NONE => F
    | SOME c =>
      check_contradiction c)
End

Definition check_lstep_def:
  (check_lstep lstep (core:num_set) (fml:pbf) (id:num) =
  case lstep of
  | Check n c =>
    if lookup n fml = SOME c
    then SOME (fml,id)
    else NONE
  | NoOp => SOME(fml,id)
  | Delete ls =>
    if EVERY (λid. lookup id core = NONE) ls
    then SOME (FOLDL (λa b. delete b a) fml ls, id)
    else NONE
  | Cutting constr =>
    (case check_cutting fml constr of
      NONE => NONE
    | SOME c => SOME (insert id c fml,id+1))
  | Con c pf n =>
    let fml_not_c = insert id (not c) fml in
    (case check_lsteps pf core fml_not_c (id+1) of
      SOME (fml',id') =>
      if check_contradiction_fml fml' n
      then SOME (insert id' c fml,id'+1)
      else NONE
    | _ => NONE)) ∧
  (check_lsteps [] core fml id = SOME (fml,id)) ∧
  (check_lsteps (step::steps) core fml id =
    case check_lstep step core fml id of
      SOME(fml',id') => check_lsteps steps core fml' id'
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

Theorem check_contradiction_fml_unsat:
  check_contradiction_fml fml n ⇒
  unsatisfiable (range fml)
Proof
  rw[check_contradiction_fml_def]>>
  every_case_tac>>fs[]>>
  drule check_contradiction_unsat>>
  rw[unsatisfiable_def,satisfiable_def,range_def,satisfies_def]>>
  metis_tac[]
QED

Theorem check_lstep_correct:
  (∀step core fml id.
     id_ok fml id ∧ domain core ⊆ domain fml ⇒
     case check_lstep step core fml id of
       SOME (fml',id') =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         domain core ⊆ domain fml' ∧
         inter fml' core = inter fml core ∧
         range fml ⊨ range fml'
     | NONE => T) ∧
  (∀steps core fml id.
     id_ok fml id ∧ domain core ⊆ domain fml ⇒
     case check_lsteps steps core fml id of
     | SOME (fml',id') =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         domain core ⊆ domain fml' ∧
         inter fml' core = inter fml core ∧
         range fml ⊨ range fml'
     | NONE => T)
Proof
  ho_match_mp_tac check_lstep_ind \\
  reverse (rpt strip_tac)
  >- (
    simp[Once check_lstep_def]>>
    every_case_tac>>gs[]>>
    metis_tac[sat_implies_def,satisfiable_def])
  >- simp[Once check_lstep_def]
  \\ Cases_on ‘∃n c. step = Check n c’
  >- (
    rw[check_lstep_def] \\ every_case_tac \\ fs [] \\ metis_tac[sat_implies_refl])
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
  \\ Cases_on ‘∃c steps n. step = Con c steps n’
  THEN1 (
    fs[check_lstep_def]
    \\ every_case_tac \\ gs[id_ok_insert_1]
    \\ fs[SUBSET_DEF]
    \\ CONJ_TAC >-
      fs[id_ok_def]
    \\ `r ∉ domain fml’ by fs [id_ok_def]
    \\ CONJ_TAC >- (
      DEP_REWRITE_TAC[inter_insert_NOTIN]>>
      fs[id_ok_def,SUBSET_DEF]>>
      last_x_assum(qspec_then`id` assume_tac)>>fs[]>>
      metis_tac[])
    \\ drule check_contradiction_fml_unsat
    \\ rw[] \\ fs[unsatisfiable_def,sat_implies_def]
    \\ fs[range_insert,id_ok_def,not_thm,PULL_FORALL]
    \\ metis_tac[satisfies_def,satisfiable_def])
  THEN1 (
    rw[Once check_lstep_def]
    \\ every_case_tac \\ gvs [])
QED

Theorem check_lstep_compact:
  (∀step core fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ lstep_ok step ∧
     check_lstep step core fml id = SOME(fml',id') ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀steps core fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ EVERY lstep_ok steps ∧
     check_lsteps steps core fml id = SOME(fml',id') ⇒
     (∀c. c ∈ range fml' ⇒ compact c))
Proof
  ho_match_mp_tac check_lstep_ind \\ reverse (rw [])
  >- (
    qpat_x_assum`_ = SOME _` mp_tac>>
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
    (( ((num + num) # num) option, (lstep list)) alist)
End

(* The list of subgoals for redundancy
  numbered #0 ... *)
Definition red_subgoals_def:
  red_subgoals ord s def obj =
  let c0 = subst s def in (**)
  let cobj =
    case obj of NONE => []
    | SOME l => [[not (obj_constraint s l)]] in
  [not c0]::(MAP (λc. [not c]) (dom_subst s ord)) ++ cobj
End

(* Apply a substitution where needed *)
Definition extract_clauses_def:
  (extract_clauses f fml rsubs [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses f fml rsubs (cpf::pfs) acc =
    case cpf of
      (NONE,pf) => extract_clauses f fml rsubs pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
      (case lookup n fml of
        NONE => NONE
      | SOME c =>
        extract_clauses f fml rsubs pfs
          ((SOME ([not (subst f c)],i),pf)::acc))
    | (SOME (INR u,i),pf) =>
      if u < LENGTH rsubs then
        extract_clauses f fml rsubs pfs ((SOME (EL u rsubs,i),pf)::acc)
      else
        NONE)
End

Theorem extract_clauses_MAP_SND:
  ∀f fml rsubs pfs acc res.
  extract_clauses f fml rsubs pfs acc = SOME res ⇒
  MAP SND res =  REVERSE (MAP SND acc) ++ MAP SND pfs
Proof
  Induct_on`pfs`>>rw[extract_clauses_def] >> simp[MAP_REVERSE]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  rw[]
QED

Definition list_insert_def:
  (list_insert [] id fml = (id,fml)) ∧
  (list_insert (c::cs) id fml =
    list_insert cs (id+1) (insert id c fml))
End

(* Check a list of subproofs *)
Definition check_subproofs_def:
  (check_subproofs [] core fml id = SOME id) ∧
  (check_subproofs ((cnopt,pf)::pfs) core fml id =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps pf core fml id of
        SOME (fml',id') => check_subproofs pfs core fml' id'
      | res => NONE)
    | SOME (cs,n) =>
      (let (cid,cfml) = list_insert cs id fml in
      case check_lsteps pf core cfml cid of
        SOME(fml',id') =>
        if check_contradiction_fml fml' n
        then check_subproofs pfs core fml id'
        else NONE
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

(* Extract the ids which are proved by a list of proofs*)
Definition extract_pids_def:
  (extract_pids [] = []) ∧
  (extract_pids (cpf::pfs) =
  case FST cpf of
    NONE => extract_pids pfs
  | SOME (i,n) => i::extract_pids pfs)
End

(* TODO: Figure out exactly
  when we need to account for skipped subproofs *)
Definition check_sstep_def:
  (check_sstep sstep ord obj core (fml:pbf) (id:num) =
  case sstep of
    Lstep lstep =>
    check_lstep lstep core fml id
  | Red c s pfs =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      let rsubs = red_subgoals ord w c obj in
      case extract_clauses w fml rsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs core fml_not_c (id+1) of
        SOME id' =>
        let goals = MAP FST (toAList (map_opt (subst_opt w) fml)) in
        let pids = extract_pids pfs in
          if
            EVERY (λid. MEM (INR id) pids) (COUNT_LIST (LENGTH rsubs)) ∧

            EVERY (λid. MEM (INL id) pids) goals
          then
            SOME (insert id' c fml,id'+1)
          else NONE
      | _ => NONE) ))
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

Theorem id_ok_list_insert:
  ∀xs id fml id' fml'.
  list_insert xs id fml = (id',fml') ∧
  id_ok fml id ⇒
  id ≤ id' ∧
  id_ok fml' id' ∧
  range fml' = set xs ∪ range fml ∧
  domain fml ⊆ domain fml'
Proof
  Induct>>rw[list_insert_def]>>fs[]>>
  first_x_assum drule>>simp[id_ok_insert_1]>>
  rw[]>>
  DEP_REWRITE_TAC[range_insert]>>
  fs[id_ok_def]>>
  simp[EXTENSION]>>
  metis_tac[]
QED

Theorem check_subproofs_correct:
  ∀pfs core fml id.
  id_ok fml id ∧ domain core ⊆ domain fml ⇒
  case check_subproofs pfs core fml id of
    SOME id' =>
     id ≤ id' ∧
     EVERY (λ(cnopt,pf).
       case cnopt of
         NONE => T
       | SOME (cs,n) =>
        unsatisfiable (range fml ∪ set cs)
     ) pfs
  | NONE => T
Proof
  Induct>- rw[check_subproofs_def]>>
  Cases>>rw[check_subproofs_def]>>
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
    simp[FORALL_PROD]>>
    rw[]>>
    every_case_tac>>
    fs[unsatisfiable_def,sat_implies_def,satisfiable_def]>>
    metis_tac[])>>
  every_case_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  every_case_tac>>fs[]>>
  drule_all id_ok_list_insert>>
  strip_tac>>
  drule (CONJUNCT2 check_lstep_correct)>>
  disch_then (qspecl_then[`r`,`core`] assume_tac)>>
  gs[SUBSET_DEF]>>
  rename1 `cid ≤ n`>>
  `id_ok fml n` by (
    fs[id_ok_def,SUBSET_DEF])>>
  first_x_assum drule>>
  disch_then drule>>
  simp[]>>
  gs[range_insert,id_ok_def,unsat_iff_implies]>>
  rw[]>>
  drule check_contradiction_fml_unsat>>
  fs[unsatisfiable_def,sat_implies_def,satisfiable_def]>>
  metis_tac[]
QED

Theorem implies_explode:
  a ⊨ s ⇔ ∀c. c ∈ s ⇒ a ⊨ {c}
Proof
  fs [sat_implies_def,satisfies_def]
  \\ metis_tac []
QED

Theorem extract_clauses_MEM_acc:
  ∀s fml sg pfs acc res c pf.
  extract_clauses s fml sg pfs acc = SOME res ∧
  MEM (SOME c,pf) acc ⇒
  MEM (SOME c,pf) res
Proof
  Induct_on`pfs`>>fs[extract_clauses_def]>>rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem extract_clauses_MEM_INL:
  ∀s fml sg pfs acc res id pf n.
  extract_clauses s fml sg pfs acc = SOME res ∧
  MEM (SOME (INL id,n), pf) pfs ⇒
  ∃c.
    lookup id fml = SOME c ∧
    MEM (SOME ([not (subst s c)],n),pf) res
Proof
  Induct_on`pfs`>>rw[extract_clauses_def]>>fs[]>>
  every_case_tac>>fs[]
  >- (
    drule extract_clauses_MEM_acc>>
    simp[]) >>
  metis_tac[]
QED

Theorem extract_clauses_MEM_INR:
  ∀s fml sg pfs acc res id pf n.
  extract_clauses s fml sg pfs acc = SOME res ∧
  MEM (SOME (INR id,n), pf) pfs ⇒
  id < LENGTH sg ∧
  MEM (SOME (EL id sg,n),pf) res
Proof
  Induct_on`pfs`>>rw[extract_clauses_def]>>fs[]>>
  every_case_tac>>fs[]
  >- (
    drule extract_clauses_MEM_acc>>
    disch_then match_mp_tac>>
    simp[])>>
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

(* < on natural numbers, treating NONE as infinity *)
Definition opt_lt_def:
  (opt_lt NONE _ ⇔ F) ∧
  (opt_lt (SOME _) NONE <=> T) ∧
  (opt_lt (SOME x) (SOME y) ⇔ x < y)
End

Definition opt_le_def:
  (opt_le x y ⇔ x = y ∨ opt_lt x y)
End

Theorem satisfies_SUBSET:
  Y ⊆ X ⇒
  (satisfies w X ⇒ satisfies w Y)
Proof
  rw[satisfies_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem sat_obj_po_fml_SUBSET:
  sat_obj_po ord obj a y ∧
  x ⊆ y ⇒
  sat_obj_po ord obj a x
Proof
  rw[sat_obj_po_def]>>
  first_x_assum drule>>
  rw[]>>
  drule_all satisfies_SUBSET>>
  rw[]>>
  asm_exists_tac >> simp[]
QED

Theorem MEM_extract_pids:
  ∀ls i.
  MEM i (extract_pids ls) ⇒
  ∃n pf.
  MEM (SOME (i,n),pf) ls
Proof
  Induct>>rw[extract_pids_def]>>
  Cases_on`h`>>fs[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem sat_implies_EL:
  C ⊨ set ls ⇔
  ∀n. n < LENGTH ls ⇒
  C ⊨ {EL n ls}
Proof
  rw[sat_implies_def,satisfies_def]>>
  metis_tac[MEM_EL]
QED

Theorem unsatisfiable_not_sat_implies:
  unsatisfiable(fml ∪ {not c}) ⇒
  fml ⊨ {c}
Proof
  rw[sat_implies_def,unsatisfiable_def,satisfiable_def]>>
  metis_tac[not_thm]
QED

Theorem check_sstep_correct:
  ∀step ord obj core fml id.
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  domain core ⊆ domain fml ⇒
  case check_sstep step ord obj core fml id of
  | SOME (fml',id') =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      domain core ⊆ domain fml' ∧
      inter fml' core = inter fml core ∧
      sat_obj_po ord obj (range fml) (range fml')
  | NONE => T
Proof
  Cases>>rw[check_sstep_def]
  >- (
    drule (CONJUNCT1 check_lstep_correct)>>
    disch_then(qspecl_then [`l`,`core`] assume_tac)>>
    every_case_tac>>fs[]>>
    gs[satisfiable_def,sat_implies_def,sat_obj_po_def]>>
    rw[]>>
    first_x_assum drule>>
    rw[]>>
    asm_exists_tac>>simp[]>>
    Cases_on`ord`>>
    fs[]>>
    metis_tac[good_spo_def,reflexive_def,reflexive_po_of_spo,PAIR])
  >- ( (* Red *)
    every_case_tac>>
    gs[id_ok_insert_1]>>
    `id_ok (insert id (not p) fml) (id + 1)` by
      fs[id_ok_def]>>
    drule check_subproofs_correct>>
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
    qsuff_tac ‘redundant_wrt_obj_po (range fml) ord obj c’
    >- (
      fs [redundant_wrt_obj_po_def] \\ rw []
      \\ irule sat_obj_po_fml_SUBSET
      \\ pop_assum $ irule_at Any
      \\ rw [SUBSET_DEF] \\ imp_res_tac range_insert_2 \\ fs [])
    \\ match_mp_tac (GEN_ALL substitution_redundancy_obj_po)
    \\ simp[]
    \\ qexists_tac ‘subst_fun s’ \\ fs []
    \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]
    \\ `id ∉ domain fml` by fs[id_ok_def]
    \\ fs[range_insert]
    \\ simp [Once implies_explode]
    \\ qpat_x_assum`!x. _ ⇒ _ ∈ domain fml` kall_tac
    \\ gvs[red_subgoals_def,MEM_COUNT_LIST,ADD1]
    \\ reverse (rw [])
    >- (
      (* dominance *)
      rw[sat_implies_EL]>>
      last_x_assum(qspec_then`SUC n` assume_tac)>>
      gvs[]>>
      drule MEM_extract_pids>>
      rw[]
      \\ drule extract_clauses_MEM_INR
      \\ disch_then drule
      \\ fs[EL]
      \\ DEP_REWRITE_TAC [EL_APPEND_EQN] \\ simp[]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ gs[EL_MAP]
      \\ drule unsatisfiable_not_sat_implies
      \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
    >- (
      (* objective *)
      Cases_on`obj`>>
      last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun s) ord))` assume_tac)>>
      fs[]>>
      drule MEM_extract_pids>>
      rw[]
      \\ drule extract_clauses_MEM_INR
      \\ disch_then drule
      \\ fs[EL]
      \\ DEP_REWRITE_TAC [EL_APPEND2]
      \\ simp[]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ gs[]
      \\ drule unsatisfiable_not_sat_implies
      \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
    >- (
      (* redundancy #0 *)
      last_x_assum(qspec_then`0` assume_tac)>>
      fs[]>>
      drule MEM_extract_pids>>
      rw[]
      \\ drule extract_clauses_MEM_INR
      \\ disch_then drule
      \\ fs[]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ fs[]
      \\ drule unsatisfiable_not_sat_implies
      \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
    (* rest of redundancy *)
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
    \\ rename1`yy = (_,_)`
    \\ Cases_on`yy` \\ fs[]
    \\ strip_tac
    \\ drule MEM_extract_pids \\ strip_tac
    \\ drule extract_clauses_MEM_INL
    \\ disch_then drule
    \\ strip_tac
    \\ first_x_assum drule
    \\ gvs[unsatisfiable_def]
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
  ∀sstep ord obj core fml id fml' id'.
  (∀c. c ∈ range fml ⇒ compact c) ∧ sstep_ok sstep ∧
  check_sstep sstep ord obj core fml id = SOME(fml',id') ⇒
  (∀c. c ∈ range fml' ⇒ compact c)
Proof
  Cases>>rw[]>>fs[check_sstep_def]
  >-
    metis_tac[check_lstep_compact] >>
  every_case_tac>>gvs[]>>
  drule range_insert_2>>rw[]>>
  metis_tac[]
QED

(*
  Top-level unsat checkers and optimality checkers
  ...
*)
Definition check_ssteps_def:
  (check_ssteps [] ord obj core fml id = SOME(fml,id)) ∧
  (check_ssteps (s::ss) ord obj core fml id =
    case check_sstep s ord obj core fml id of
      SOME(fml',id') => check_ssteps ss ord obj core fml' id'
    | NONE => NONE)
End

Theorem sat_obj_po_refl:
  OPTION_ALL good_spo ord ⇒
  sat_obj_po ord obj f f
Proof
  rw[sat_obj_po_def]>>
  qexists_tac`w`>>
  simp[opt_le_def]>>
  Cases_on`ord`>>gs[good_spo_def]>>
  metis_tac[reflexive_def,reflexive_po_of_spo,PAIR]
QED

Theorem opt_lt_trans:
  opt_lt x y ∧
  opt_lt y z ⇒
  opt_lt x z
Proof
  Cases_on`x`>>
  Cases_on`y`>>
  Cases_on`z`>>
  rw[opt_lt_def]
QED

Theorem opt_le_trans:
  opt_le x y ∧
  opt_le y z ⇒
  opt_le x z
Proof
  rw[opt_le_def]>>
  fs[]>>
  metis_tac[opt_lt_trans]
QED

Theorem sat_obj_po_trans:
  OPTION_ALL good_spo ord ⇒
  sat_obj_po ord obj x y ∧
  sat_obj_po ord obj y z ⇒
  sat_obj_po ord obj x z
Proof
  rw[sat_obj_po_def]>>
  first_x_assum drule>>
  rw[]>>
  first_x_assum drule>>
  rw[]>>
  asm_exists_tac>>
  fs[]>>
  Cases_on`ord`>>fs[good_spo_def]>>
  metis_tac[transitive_def]
QED

Theorem check_ssteps_correct:
  ∀ss ord obj core fml id.
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  domain core ⊆ domain fml ⇒
  case check_ssteps ss ord obj core fml id of
  | SOME(fml',id') =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      domain core ⊆ domain fml' ∧
      inter fml' core = inter fml core ∧
      sat_obj_po ord obj (range fml) (range fml')
  | Fail => T
Proof
  Induct>>rw[check_ssteps_def,sat_obj_po_refl]>>
  drule check_sstep_correct>>
  rpt (disch_then drule)>>
  disch_then(qspecl_then [`h`,`obj`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  rw[]>>
  first_x_assum drule>>
  rpt(disch_then drule)>>
  disch_then(qspec_then`obj` mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  rw[]>>
  metis_tac[sat_obj_po_trans]
QED

(* Top-level steps that manipulate the core *)
Datatype:
  cstep =
  | Dom npbc subst
    (( ((num + num) # num) option, (lstep list)) alist)
    (* Ordered list of proofs for subgoals,
      interpreted like Redundancy *)
  | Transfer (num list) (* Ids to move into core *)
  | CheckedDelete (num list) ((num,sstep list) alist)
    (* Checked deletion with proofs *)
  | Sstep sstep
  | Obj (bool spt)
End

(* There are many variants of checked deletions possible:

Suppose we delete D1 D2

* Current option:
1) Check C \ D1 |- E (satisfiability implies)
   where C is core (can not be deleted)
  and D1 ∈ E as the last ID.
  Then check C \ {D1,D2} |- ...

2) Check C \ {D1,D2} |- E (satisfiability implies)
  and D1,D2 ∈ E (by search)

3) Check C \ D1 U not D1 |- F (etc.)
  This is not good
*)
Definition check_del_def:
  (check_del [] ord obj c cf id = SOME id) ∧
  (check_del ((n,pf)::pfs) ord obj c cf id =
    case lookup n cf of
      NONE => NONE
    | SOME cl =>
      (let nc = delete n c in
      let ncf = delete n cf in
      case check_ssteps pf ord obj nc ncf id of
        SOME(ncf',id') =>
        if lookup (id'-1) ncf' = SOME cl
        then check_del pfs ord obj nc ncf id'
        else NONE
      | res => NONE))
End

Definition hide_def:
  hide x = x
End

Theorem range_delete_IN:
  c' ∈ range f ∧
  lookup n f = SOME c ⇒
  c = c' ∨ c' ∈ range (delete n f)
Proof
  rw[range_def,lookup_delete]>>
  Cases_on `n' = n`>>fs[]>>
  metis_tac[]
QED

Theorem check_del_correct:
  ∀pfs ord obj c cf id id'.
  id_ok cf id ∧
  OPTION_ALL good_spo ord ∧
  domain c = domain cf ∧
  check_del pfs ord obj c cf id = SOME id' ⇒
    hide (id ≤ id' ∧
    set (MAP FST pfs) ⊆ domain cf ∧
    sat_obj_po ord obj
      (range (FOLDL (λa b. delete b a) cf (MAP FST pfs)))
      (range cf))
Proof
  ho_match_mp_tac check_del_ind>>
  rw[check_del_def]
  >-
    simp[hide_def,sat_obj_po_refl]>>
  every_case_tac>>gs[]>>
  `id_ok (delete n cf) id` by fs[id_ok_def]>>
  drule check_ssteps_correct>>
  disch_then drule>>
  disch_then (qspecl_then [`pf`,`obj`,`delete n c`] assume_tac)>>
  gs[]>>
  qpat_x_assum`_ ⇒ _` mp_tac>>
  impl_tac >-
    fs[id_ok_def]>>
  simp[hide_def]>> strip_tac >>
  CONJ_TAC >-
    fs[domain_lookup,SUBSET_DEF]>>
  drule sat_obj_po_trans>>
  disch_then match_mp_tac>>
  asm_exists_tac>>
  simp[]>>
  match_mp_tac (GEN_ALL sat_obj_po_fml_SUBSET)>>
  asm_exists_tac>>
  fs[SUBSET_DEF]>>rw[]>>
  drule range_delete_IN>>
  disch_then drule>>
  rw[]
  >- (fs[range_def]>>metis_tac[])>>
  fs[range_def,domain_lookup,PULL_EXISTS,lookup_delete]>>
  first_x_assum drule_all>>
  strip_tac>>
  rename1`lookup xxx a = _`>>
  last_x_assum(qspec_then`xxx` assume_tac)>>
  gs[lookup_inter,lookup_delete]>>
  `xxx ∈ domain c` by metis_tac[domain_lookup]>>
  gs[domain_lookup]>>
  metis_tac[]
QED

Definition check_obj_def:
  check_obj obj bound wm coref =
  let w = (λn.
    case lookup n wm of NONE => F | SOME b => b) in
  let new = eval_obj obj w in
  let cs = MAP SND (toAList coref) in
  if opt_lt (SOME new) bound ∧
    EVERY (satisfies_npbc w) cs
  then
    SOME new
  else NONE
End

(* For a bound b, the model improving constraint is
  f ≤ b-1 = f < b = not (f ≥ b)
*)
Definition model_improving_def:
  model_improving fopt v =
  case fopt of
    SOME f =>
       not ((f,v):npbc)
  | _ =>
       not (([],v):npbc)
End

(* The formula represented by the core *)
Definition coref_def:
  coref (core:num_set) fml =
    mapi (λk v.
      case lookup k fml of NONE => ([],0):npbc | SOME res => res) core
End

(* The list of subgoals for dominance
  numbered #0 ... *)
Definition neg_dom_subst_def:
  (neg_dom_subst w ((f,us,vs),xs) =
  let ww = (λn.
      case ALOOKUP (ZIP (vs,xs)) n of
        SOME v =>
          (case w v of NONE => SOME (INR (Pos v)) | r => r)
      | NONE => ALOOKUP (ZIP (us, MAP (INR o Pos) xs)) n) in
  MAP (subst ww) f)
End

Definition dom_subgoals_def:
  dom_subgoals spo s def obj =
  let cobj =
    case obj of NONE => []
    | SOME l => [[not (obj_constraint s l)]] in
  let negord = neg_dom_subst s spo in
  (MAP (λc. [not c]) (dom_subst s (SOME spo))) ++ negord :: cobj
End

Definition check_cstep_def:
  (check_cstep cstep chk ord obj bound core (fml:pbf) (id:num) =
  case cstep of
  | Dom c s pfs =>
    (case ord of NONE => NONE
    | SOME spo =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      let dsubs = dom_subgoals spo w c obj in
      case extract_clauses w fml dsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs core fml_not_c (id+1) of
        SOME id' =>
        let cf = coref core fml in
        let goals = MAP FST (toAList (map_opt (subst_opt w) cf)) in
        let pids = extract_pids pfs in
          if
            EVERY (λid. MEM (INR id) pids) (COUNT_LIST (LENGTH dsubs)) ∧

            EVERY (λid. MEM (INL id) pids) goals
          then
            SOME (core, insert id' c fml, bound, id'+1)
          else NONE
      | _ => NONE) ))
  | Transfer ls =>
    if EVERY (λid. lookup id fml ≠ NONE) ls
    then SOME (FOLDL (λa b. insert b () a) core ls, fml, bound,id)
    else NONE
  | CheckedDelete ls pfs =>
    if EVERY (λid. lookup id core ≠ NONE) ls then
      if chk then
        (let cf = coref core fml in
        case check_del pfs ord obj core cf id of NONE => NONE
        | SOME id' =>
        let pids = MAP FST pfs in (* optimize and change later *)
        if EVERY (λid. MEM id pids) ls then
          SOME (FOLDL (λa b. delete b a) core ls,
                FOLDL (λa b. delete b a) fml ls, bound, id')
        else
          NONE)
      else
        (* All ids are in core*)
        if difference fml core = LN then
          SOME (FOLDL (λa b. delete b a) core ls,
                FOLDL (λa b. delete b a) fml ls, bound, id)
        else NONE
    else
      NONE
  | Sstep sstep =>
    (case check_sstep sstep ord obj core fml id of
      SOME(fml',id') => SOME (core,fml',bound,id')
    | NONE => NONE)
  | Obj w =>
    (case check_obj obj bound w (coref core fml) of
      NONE => NONE
    | SOME new =>
      let c = model_improving obj new in
      SOME (
        insert id () core,
        insert id c fml,SOME new,id+1)))
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

Theorem range_coref_insert_2:
  h ∉ domain fml ∧ domain core ⊆ domain fml ⇒
  range (coref (insert h () core) (insert h c fml)) =
  c INSERT range (coref core fml)
Proof
  DEP_REWRITE_TAC [range_coref_insert]>>
  simp[lookup_insert]>>
  rw[]>>AP_TERM_TAC>>
  match_mp_tac range_coref_cong>>
  fs[lookup_inter,lookup_insert]>>
  rw[]>>
  fs[domain_lookup,SUBSET_DEF]>>
  every_case_tac>>fs[]>>
  metis_tac[option_CLAUSES]
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

Theorem range_coref_insert_notin:
  n ∉ domain core ⇒
  range (coref core (insert n c fml)) =
  range (coref core fml)
Proof
  rw[coref_def]>>
  fs[range_def]>>
  rw[EXTENSION,EQ_IMP_THM]>>
  fs[lookup_mapi]>>rw[]>>
  fs[domain_lookup]>>
  `n ≠ n'` by metis_tac[]>>
  simp[lookup_insert]
  >- (
    every_case_tac>>fs[]>>
    first_x_assum (irule_at Any)>>
    simp[])
  >-
    (asm_exists_tac>>simp[])
QED

(* TODO: we need to update this later
  But for now, "no order" is treated as the universal relation
*)
Definition valid_conf_def:
  valid_conf ord obj core fml ⇔
  domain core ⊆ domain fml ∧
  sat_obj_po ord obj
    (range (coref core fml)) (range fml)
End

Theorem valid_conf_FOLDL_delete:
  valid_conf ord obj core fml ∧
  EVERY (λid. id ∉ domain core) l ⇒
  valid_conf ord obj core (FOLDL (λa b. delete b a) fml l)
Proof
  strip_tac>>
  fs[valid_conf_def,domain_FOLDL_delete]>>
  CONJ_ASM1_TAC >- (
    fs[SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM,domain_lookup]>>
    metis_tac[option_CLAUSES])>>
  DEP_REWRITE_TAC [range_coref_FOLDL_delete]>>
  fs[sat_obj_po_def]>>
  rw[]>>first_x_assum drule>>
  rw[]>>
  qexists_tac`w'`>>
  fs[satisfies_def]>>
  metis_tac[range_FOLDL_delete,SUBSET_DEF]
QED

Theorem valid_conf_del_core:
  OPTION_ALL good_spo ord ∧
  valid_conf ord obj core fml ∧
  domain coreS ⊆ domain core ∧
  sat_obj_po ord obj (range (coref coreS fml)) (range (coref core fml))
  ⇒
  valid_conf ord obj coreS fml
Proof
  rw[valid_conf_def]
  >- fs[SUBSET_DEF]>>
  metis_tac[sat_obj_po_trans]
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

(* An assignment satisfying C with objective value ≤ v *)
Definition sat_obj_le_def:
  sat_obj_le fopt v C ⇔
  ∃w.
    satisfies w C ∧
    eval_obj fopt w ≤ v
End

Definition imp_obj_def:
  imp_obj fopt v C1 C2 ⇔
  (sat_obj_le fopt v C1 ⇒ sat_obj_le fopt v C2)
End

Definition equi_obj_def:
  equi_obj chk fopt bound C1 C2 ⇔
  ∀v. opt_lt (SOME v) bound ⇒
    imp_obj fopt v C1 C2 ∧
    (chk ⇒ imp_obj fopt v C2 C1)
End

Theorem equi_obj_refl:
  x = y ⇒
  equi_obj chk obj bound x y
Proof
  rw[equi_obj_def,imp_obj_def]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem opt_lt_irref:
  ¬ (opt_lt x x)
Proof
  Cases_on`x`>>
  rw[opt_lt_def]
QED

Theorem range_toAList:
  range t = set (MAP SND (toAList t))
Proof
  rw[range_def,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList]
QED

Theorem sat_obj_po_SUBSET:
  OPTION_ALL good_spo ord ∧
  b ⊆ a ⇒
  sat_obj_po ord obj a b
Proof
  rw[sat_obj_po_def]>>
  imp_res_tac satisfies_SUBSET>>
  asm_exists_tac >> simp[]>>
  Cases_on`ord`>>fs[good_spo_def]>>
  metis_tac[reflexive_def,reflexive_po_of_spo,PAIR]
QED

Theorem sat_obj_po_equi_obj:
  sat_obj_po ord obj A B ∧
  A ⊆ B ⇒
  equi_obj chk obj b A B
Proof
  rw[equi_obj_def,imp_obj_def,sat_obj_le_def,sat_obj_po_def]
  >- (
    first_x_assum drule>>
    rw[]>>
    asm_exists_tac>>simp[])>>
  qexists_tac`w`>>
  fs[satisfies_def,SUBSET_DEF]
QED

Theorem equi_obj_sym:
  equi_obj T obj b A B ⇔
  equi_obj T obj b B A
Proof
  rw[equi_obj_def]>>
  metis_tac[]
QED

Theorem satisfies_npbc_model_improving:
  satisfies_npbc w (model_improving obj ov) ⇔
  eval_obj obj w < ov
Proof
  fs[model_improving_def,eval_obj_def]>>
  every_case_tac>>
  rw[not_thm,satisfies_npbc_def]
QED

Theorem lookup_coref:
  domain core ⊆ domain fml ∧
  lookup x (coref core fml) = SOME y ⇒
  lookup x fml = SOME y
Proof
  rw[coref_def,lookup_mapi]>>
  every_case_tac>>fs[domain_lookup,SUBSET_DEF]>>
  metis_tac[option_CLAUSES]
QED

Theorem trivial_valid_conf:
  OPTION_ALL good_spo ord ∧
  domain core = domain fml ⇒
  valid_conf ord obj core fml
Proof
  rw[valid_conf_def]>>
  `range (coref core fml) = range fml` by (
    rw[coref_def,range_def,EXTENSION,lookup_mapi]>>
    fs[EXTENSION,domain_lookup,PULL_EXISTS]>>
    rw[]>>eq_tac>>rw[]>>
    qexists_tac`n`>>simp[])>>
  metis_tac[sat_obj_po_refl]
QED

Theorem toAList_empty_difference:
  domain a ⊆ domain b
  ⇒
  toAList (difference a b) = []
Proof
  CCONTR_TAC>>
  fs[]>>
  Cases_on`toAList (difference a b)`>>fs[]>>
  `MEM h (toAList (difference a b))` by fs[]>>
  Cases_on`h`>>fs[MEM_toAList,lookup_difference]>>
  fs[SUBSET_DEF,domain_lookup]>>
  metis_tac[option_CLAUSES]
QED

Theorem check_cstep_correct:
  ∀cstep chk ord obj bound core fml id.
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  valid_conf ord obj core fml ⇒
  case check_cstep cstep chk ord obj bound core fml id of
  | SOME (core',fml',bound',id') =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      valid_conf ord obj core' fml' ∧
      opt_le bound' bound ∧
      (opt_lt bound' bound ⇒
        sat_obj_le obj (THE bound') (range (coref core fml))) ∧
      equi_obj chk obj bound'
        (range (coref core fml))
        (range (coref core' fml'))
  | NONE => T
Proof
  Cases>>fs[check_cstep_def]
  >- ( (* Dominance *)
    ntac 8 strip_tac>>
    Cases_on`ord`>>fs[]>>
    every_case_tac>>simp[]>>
    `id_ok (insert id (not p) fml) (id + 1)` by
      fs[id_ok_def]>>
    drule check_subproofs_correct>>
    rename1`check_subproofs pfs core`>>
    disch_then(qspecl_then [`pfs`,`core`] mp_tac)>>
    impl_tac >- (
      gs[valid_conf_def,SUBSET_DEF])>>
    strip_tac>>gs[]>>
    rename1`insert cc p fml`>>
    CONJ_TAC>-
      gvs[id_ok_def,SUBSET_DEF]>>
    fs[valid_conf_def]>>
    DEP_REWRITE_TAC [range_coref_insert_notin]>>
    CONJ_TAC>- (
      fs[valid_conf_def,id_ok_def,SUBSET_DEF]>>
      `id ≤ cc` by fs[]>>
      metis_tac[])>>
    simp[opt_le_def,opt_lt_irref,equi_obj_refl]>>
    CONJ_TAC >-
      fs[SUBSET_DEF]>>
    simp[sat_obj_po_def]>>
    DEP_REWRITE_TAC[range_insert]>>
    CONJ_TAC >- fs[id_ok_def]>>
    simp[satisfies_simp]>>
    simp[GSYM CONJ_ASSOC]>>
    PairCases_on`x`>>
    match_mp_tac (GEN_ALL good_spo_dominance)>>
    simp[]>>
    qexists_tac ‘subst_fun s’>>fs[]>>
    CONJ_TAC >-
      metis_tac[range_coref_SUBSET]>>
    CONJ_TAC >-
      fs[sat_obj_po_def]>>
    `id ∉ domain fml` by fs[id_ok_def]>>
    fs[range_insert]>>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>
    gvs[dom_subgoals_def,MEM_COUNT_LIST,ADD1]>>
    CONJ_TAC >- (
      (* core constraints*)
      rw[sat_implies_def,range_def,satisfies_def]
      \\ gs[PULL_EXISTS]
      \\ rename [‘lookup a _ = SOME xx’]
      \\ fs [MEM_toAList,lookup_map_opt,CaseEq"option",PULL_EXISTS]
      \\ drule_all lookup_coref
      \\ strip_tac
      \\ last_x_assum drule
      \\ Cases_on ‘subst_opt (subst_fun s) xx’ \\ fs []
      THEN1 (
        imp_res_tac subst_opt_NONE
        \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
        \\ fs [satisfies_def,range_def,PULL_EXISTS]
        \\ metis_tac[])
      \\ rename1`yy = (_,_)`
      \\ Cases_on`yy` \\ fs[]
      \\ strip_tac
      \\ drule MEM_extract_pids \\ strip_tac
      \\ drule extract_clauses_MEM_INL
      \\ disch_then drule
      \\ strip_tac
      \\ last_x_assum drule
      \\ gvs[unsatisfiable_def,satisfiable_def,satisfies_def]
      \\ fs[not_thm,range_def]
      \\ metis_tac[])>>
    CONJ_TAC >- (
      (* order constraints *)
      simp[GSYM LIST_TO_SET_MAP]>>
      rw[sat_implies_EL,EL_MAP]>>
      last_x_assum(qspec_then`n` assume_tac)>>
      gvs[dom_subst_def]>>
      drule MEM_extract_pids>>
      rw[]>>
      drule extract_clauses_MEM_INR>>
      disch_then drule>>
      fs[EL_MAP]>>
      DEP_REWRITE_TAC [EL_APPEND_EQN] >> simp[]>>
      simp[EL_MAP]>>
      rw[]>>
      first_x_assum drule >> strip_tac>>
      gs[]>>
      drule unsatisfiable_not_sat_implies>>
      simp[]>>
      metis_tac[INSERT_SING_UNION,UNION_COMM])>>
    CONJ_TAC >- (
      (* negated order constraint *)
      last_x_assum(qspec_then`LENGTH (dom_subst (subst_fun s) (SOME ((x0,x1,x2),x3)))` assume_tac)>>
      gs[ADD1]>>
      drule MEM_extract_pids>>
      rw[]
      \\ drule extract_clauses_MEM_INR
      \\ disch_then drule
      \\ fs[]
      \\ DEP_REWRITE_TAC [EL_APPEND2]
      \\ simp[]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ gs[neg_dom_subst_def]
      \\ metis_tac[INSERT_SING_UNION,UNION_COMM,LIST_TO_SET_MAP])>>
    (* objective constraint *)
    Cases_on`obj`>>
    simp[]>>
    last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun s) (SOME ((x0,x1,x2),x3))))` assume_tac)>>
    gs[ADD1]>>
    drule MEM_extract_pids>>
    rw[]
    \\ drule extract_clauses_MEM_INR
    \\ disch_then drule
    \\ fs[]
    \\ DEP_REWRITE_TAC [EL_APPEND2]
    \\ simp[]
    \\ rw[]
    \\ first_x_assum drule \\ strip_tac
    \\ gs[]
    \\ drule unsatisfiable_not_sat_implies
    \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
  >- (
    (* Transfer *)
    ntac 8 strip_tac>>
    IF_CASES_TAC>>fs[valid_conf_def]>>
    simp[GSYM CONJ_ASSOC]>>
    CONJ_TAC
    >- (
      pop_assum mp_tac>>
      Induct_on`l`>>simp[domain_lookup]>>
      metis_tac[option_CLAUSES])>>
    DEP_REWRITE_TAC[range_coref_FOLDL_insert]>>
    fs[opt_le_def]>>
    CONJ_TAC >- (
      drule (GEN_ALL sat_obj_po_trans)>>
      disch_then match_mp_tac>>
      first_x_assum (irule_at Any)>>
      fs[sat_obj_po_def]>>
      rw[]>>
      asm_exists_tac>>simp[]>>
      Cases_on`ord`>>fs[good_spo_def]>>
      metis_tac[reflexive_def,reflexive_po_of_spo,PAIR])>>
    CONJ_TAC >-
      simp[opt_lt_irref]>>
    simp[equi_obj_def]>>
    fs[sat_obj_po_def]>>rw[]
    >- (
      simp[imp_obj_def]>>rw[sat_obj_le_def]>>
      first_x_assum drule>>
      drule range_coref_SUBSET>>
      rw[]>>fs[SUBSET_DEF,satisfies_def]>>
      qexists_tac`w'`>>
      fs[MEM_MAP,EVERY_MEM]>>rw[]
      >- (
        first_x_assum drule>>
        fs[range_def]>>
        metis_tac[option_CLAUSES])>>
      metis_tac[opt_le_trans])>>
    simp[imp_obj_def,sat_obj_le_def]>>
    metis_tac[])
  >- ( (* CheckedDelete *)
    ntac 8 strip_tac>>
    IF_CASES_TAC >> simp[]>>
    reverse IF_CASES_TAC >> simp[]
    >- (
      (* Unchecked deletion *)
      IF_CASES_TAC>>simp[]>>
      simp[opt_le_def,opt_lt_irref]>>
      CONJ_TAC >- metis_tac[id_ok_FOLDL_delete] >>
      CONJ_TAC >- (
        match_mp_tac trivial_valid_conf>>
        simp[domain_FOLDL_delete]>>
        fs[valid_conf_def]>>
        drule difference_sub>>
        fs[SUBSET_DEF,EXTENSION]>>
        metis_tac[])>>
      simp[equi_obj_def]>>
      cheat)>>
    (* Actual checked deletion *)
    every_case_tac>>simp[]>>
    `id_ok (coref core fml) id` by (
      fs[id_ok_def,domain_coref,valid_conf_def]>>
      metis_tac[SUBSET_DEF])>>
    drule check_del_correct>>
    disch_then (drule_at Any)>>
    simp[domain_coref]>>
    strip_tac>>fs[hide_def,range_FOLDL_delete_coref]>>
    CONJ_TAC >- (
      `id_ok fml x` by fs[id_ok_def]>>
      metis_tac[id_ok_FOLDL_delete]) >>
    simp[opt_lt_irref,opt_le_def]>>
    qmatch_goalsub_abbrev_tac`equi_obj _ _ _ _ (range (coref coreS _)) `>>
    qmatch_asmsub_abbrev_tac`range (coref coreT _)`>>
    `sat_obj_po ord obj
      (range (coref coreS fml))
      (range (coref coreT fml))` by (
      unabbrev_all_tac>>
      match_mp_tac sat_obj_po_SUBSET>>
      simp[]>>
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
      fs[domain_FOLDL_delete,Abbr`coreT`]>>
      metis_tac[sat_obj_po_trans])>>
    `equi_obj T obj bound
      (range (coref coreS fml))
      (range (coref core fml))` by (
      match_mp_tac sat_obj_po_equi_obj>>
      CONJ_TAC >-
        metis_tac[sat_obj_po_trans]>>
      unabbrev_all_tac>>
      match_mp_tac range_coref_SUBSET_core>>
      simp[domain_FOLDL_delete] )>>
    PURE_REWRITE_TAC [Once equi_obj_sym]>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`_ _ _ A _ ⇒ _ _ _ B _`>>
    qsuff_tac`A = B` >> fs[]>>
    unabbrev_all_tac>>
    match_mp_tac range_coref_cong>>
    strip_tac>>
    match_mp_tac lookup_inter_FOLDL_delete>>
    simp[EVERY_MEM,lookup_NONE_domain,domain_FOLDL_delete,MEM_FILTER])
  >- (
    (* Sstep *)
    ntac 7 strip_tac>>
    drule check_sstep_correct>>
    fs[valid_conf_def]>>
    ntac 2 (disch_then drule)>>
    disch_then (qspecl_then [`s`,`obj`] mp_tac)>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    strip_tac>>
    drule range_coref_cong>>
    simp[equi_obj_refl,opt_le_def,opt_lt_irref]>>
    imp_res_tac range_coref_SUBSET>>
    metis_tac[sat_obj_po_trans])
  >- (
    (* Obj *)
    ntac 7 strip_tac>>
    simp[check_obj_def]>>
    IF_CASES_TAC>>fs[opt_le_def]>>
    qmatch_goalsub_abbrev_tac`model_improving obj ov`>>
    CONJ_TAC >- fs[id_ok_def]>>
    CONJ_TAC >- (
      fs[valid_conf_def]>>rw[]
      >-
        fs[SUBSET_DEF]>>
      fs[sat_obj_po_def]>>rw[]>>
      `id ∉ domain fml` by fs[id_ok_def]>>
      drule_all range_coref_insert_2>>
      rw[]>>gs[]>>
      first_x_assum drule>>
      rw[]>>
      qexists_tac`w'`>>simp[range_insert]>>
      fs[satisfies_npbc_model_improving])>>
    CONJ_TAC
    >- (
      simp[sat_obj_le_def]>>
      qmatch_asmsub_abbrev_tac`eval_obj obj w`>>
      qexists_tac`w`>>simp[opt_le_def]>>
      fs[range_toAList,satisfies_def,EVERY_MEM])>>
    `id ∉ domain fml` by fs[id_ok_def]>>
    fs[valid_conf_def]>>
    drule_all range_coref_insert_2>>
    rw[]>>
    simp[equi_obj_def,imp_obj_def]>>
    rw[]
    >- (
      fs[sat_obj_le_def,satisfies_npbc_model_improving,opt_lt_def]>>
      first_assum (irule_at Any)>>
      fs[])>>
    fs[sat_obj_le_def]>>
    metis_tac[]
  )
QED

(* TODO: update below *)
Definition check_csteps_def:
  (check_csteps [] obj bound core fml id = SOME (core,fml,bound,id)) ∧
  (check_csteps (s::ss) obj bound core fml id =
    case check_cstep s obj bound core fml id of
      SOME (core',fml',bound',id') =>
      check_csteps ss obj bound' core' fml' id'
    | NONE => NONE)
End

Theorem opt_lt_le:
  opt_le a b ∧ opt_lt b c ∨
  opt_lt a b ∧ opt_le b c ⇒
  opt_lt a c
Proof
  rw[opt_le_def]>>
  metis_tac[opt_lt_trans]
QED

Theorem equi_obj_le:
  opt_le a b ∧
  equi_obj obj b A B ⇒
  equi_obj obj a A B
Proof
  rw[equi_obj_def]>>
  metis_tac[opt_lt_le]
QED

Theorem equi_obj_trans:
  equi_obj obj b A B ∧
  equi_obj obj b B C ⇒
  equi_obj obj b A C
Proof
  rw[equi_obj_def,imp_obj_def]
QED

Theorem check_csteps_correct:
  ∀csteps obj bound core fml id core' fml' bound' id'.
  id_ok fml id ∧
  valid_conf obj core fml ∧
  check_csteps csteps obj bound core fml id =
    SOME(core',fml',bound',id') ⇒
    hide (id ≤ id' ∧
    id_ok fml' id' ∧
    valid_conf obj core' fml' ∧
    opt_le bound' bound ∧
    (opt_lt bound' bound ⇒
      sat_obj_le obj (THE bound') (range (coref core fml))) ∧
    equi_obj obj bound'
      (range (coref core fml))
      (range (coref core' fml')))
Proof
  Induct>>rw[check_csteps_def]
  >-
    rw[hide_def,opt_le_def,opt_lt_irref,equi_obj_refl]>>
  every_case_tac>>fs[]>>
  drule check_cstep_correct>>
  disch_then drule>>
  disch_then(qspecl_then [`h`,`bound`] mp_tac)>>
  simp[]>>rw[]>>
  first_x_assum drule>>
  disch_then drule>>
  disch_then drule>>
  strip_tac>>fs[hide_def]>>
  CONJ_TAC >-
    metis_tac[opt_le_trans]>>
  CONJ_TAC >- (
    rw[]>>
    rename1`opt_le A B`>>
    qpat_x_assum`opt_le A B` mp_tac>>simp[opt_le_def]>>
    strip_tac
    >-
      fs[equi_obj_def]>>
    first_x_assum drule>>
    qpat_x_assum`equi_obj _ _ _ _ ` kall_tac>>
    fs[equi_obj_def,imp_obj_def]>>
    `opt_lt (SOME (THE A)) B` by
      (Cases_on`A`>>fs[opt_lt_def])>>
    fs[])>>
  metis_tac[equi_obj_trans,equi_obj_le]
QED

(* Sanity checking *)
Theorem valid_conf_setup:
  valid_conf obj (map (λv. ()) fml) fml
Proof
  fs[valid_conf_def,coref_def,range_def,lookup_mapi,lookup_map]>>
  fs[PULL_EXISTS]>>
  qmatch_goalsub_abbrev_tac`_ _ A B`>>
  qsuff_tac `A = B`>>fs[sat_obj_refl]>>
  unabbrev_all_tac>>
  rw[EXTENSION,EQ_IMP_THM]>>
  qexists_tac`n`>>simp[]
QED

Theorem opt_le_exists:
  ∃v.
  opt_lt (SOME v) NONE ∧
  eval_obj obj w ≤ v
Proof
  rw[eval_obj_def]>>
  every_case_tac>>fs[opt_le_def,opt_lt_def]>>
  qexists_tac`SUM (MAP (eval_term w) x)`>>
  fs[]
QED

Theorem equi_obj_NONE:
  equi_obj b obj NONE C1 C2 ⇒
  (satisfiable C1 ⇒ satisfiable C2) ∧
  (b ⇒ (satisfiable C2 ⇒ satisfiable C1))
Proof
  rw[equi_obj_def,imp_obj_def,sat_obj_le_def]>>
  fs[satisfiable_def]>>
  metis_tac[opt_le_exists]
QED

Theorem equi_obj_SOME_bound:
  equi_obj obj (SOME v) C1 C2 ∧
  unsatisfiable C2 ⇒
  ∀w. satisfies w C1 ⇒
    eval_obj obj w ≥ v
Proof
  rw[equi_obj_def,unsatisfiable_def,satisfiable_def]>>
  CCONTR_TAC>>
  `eval_obj obj w < v` by
    fs[]>>
  first_x_assum(qspec_then`eval_obj obj w` mp_tac)>>
  impl_tac >-
    rw[opt_lt_def]>>
  strip_tac>>
  fs[imp_obj_def,sat_obj_le_def]>>
  metis_tac[LESS_EQ_REFL]
QED

Theorem optimal_SELECT:
  satisfies w f ⇒
  optimal (@w. optimal w f obj) f obj
Proof
  rw[]>>
  drule optimal_exists>>
  disch_then (qspec_then`obj` assume_tac)>>
  fs[GSYM SELECT_THM]
QED

Theorem optimal_val_eq:
  sat_obj_le obj x f ∧
  (∀w. satisfies w f ⇒ eval_obj obj w ≥ x) ⇒
  optimal_val f obj = SOME x
Proof
  rw[optimal_val_def,satisfiable_def,sat_obj_le_def]
  >-
    metis_tac[]>>
  drule optimal_SELECT  >>
  disch_then(qspec_then`obj` assume_tac)>>
  rename1`eval_obj obj ww = _`>>
  fs[optimal_def]>>
  res_tac>>
  fs[]
QED

(* In the current setup, the
  o rule can log a solution with no objective
  In that case, the formula is satisfiable
*)
Theorem check_csteps_optimal:
  ∀csteps obj bound core fml id core' fml' bound' id'.
  id_ok fml id ∧
  valid_conf obj core fml ∧
  check_csteps csteps obj NONE core fml id =
    SOME (core',fml',bound',id') ∧
  unsatisfiable (range fml') ⇒
  optimal_val (range (coref core fml)) obj = bound'
Proof
  rw[unsatisfiable_def,satisfiable_def]>>
  imp_res_tac check_csteps_correct>>
  fs[hide_def]>>
  Cases_on`bound'`>>rw[]
  >- (
    drule equi_obj_NONE>>
    fs[optimal_val_def,satisfiable_def,valid_conf_def,sat_obj_def]>>
    metis_tac[])>>
  gs[opt_lt_def]>>
  match_mp_tac optimal_val_eq>>fs[]>>
  match_mp_tac (GEN_ALL equi_obj_SOME_bound)>>
  asm_exists_tac>>
  fs[unsatisfiable_def,valid_conf_def,satisfiable_def]>>
  fs[sat_obj_def]>>
  metis_tac[]
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
