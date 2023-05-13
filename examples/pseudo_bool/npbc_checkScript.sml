(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble npbcTheory mlstringTheory mlintTheory mlvectorTheory;

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
  sptree$lookup x (inter (FOLDL (λa b. delete b a) fml l) core) =
  sptree$lookup x (inter fml core)
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
    \\ ‘r ∉ domain fml’ by fs [id_ok_def]
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

Type subst = ``:(bool + num lit) option vector``;

(* Steps that preserve satisfiability *)
Datatype:
  sstep =
  | Lstep lstep (* Id representing a contradiction *)
  | Red npbc subst (( ((num + num) # num) option, (lstep list)) alist) (num option)
  (* the alist represents a subproof
    NONE -> top level step
    SOME (INL n,id) -> database proofgoals, contradiction at id
    SOME (INR n,id) -> # proofgoals, contradiction at id *)
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
  (check_subproofs [] core fml id = SOME (fml,id)) ∧
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
  subst_fun (s:subst) n =
  if n < length s then
    sub s n
  else NONE
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

(* Extract the INL and INR
  ids which were proved by a list of proofs *)
Definition extract_pids_def:
  (extract_pids [] l r = (l,r)) ∧
  (extract_pids (cpf::pfs) l r =
  case FST cpf of
    NONE => extract_pids pfs l r
  | SOME (i,n) =>
    (case i of
      INL i => extract_pids pfs (insert i () l) r
    | INR i => extract_pids pfs l (insert i () r)))
End

Definition list_pair_eq_def:
  list_pair_eq xs ys =
    case xs of
    | [] => (case ys of [] => T | _ => F)
    | (x1,x2)::xs => (case ys of
                      | [] => F
                      | ((y1,y2)::ys) =>
                        if x1 = y1 ∧ x2 = y2 then list_pair_eq xs ys else F)
End

Definition equal_constraint_def:
  equal_constraint (x2,x3) ((y2,y3):(int # num) list # num) ⇔
    if x3 = y3 then
      list_pair_eq x2 y2
    else F
End

Definition mem_constraint_def:
  mem_constraint (c:(int # num) list # num) [] = F ∧
  mem_constraint c (x::xs) =
    if equal_constraint c x then T else mem_constraint c xs
End

(* Partition the formula goals into proved and non-proved
  For each non-proved goal, check if
  1) it was already in the formula
  2) it was already proved by another proofgoal (excluding #)
*)
Definition split_goals_def:
  split_goals (fml:npbc num_map) (proved:num_set) (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). sptree$lookup i proved ≠ NONE) goals in
  let proved = MAP SND lp in
  let f = range fml in
  EVERY (λ(i,c). c ∈ f ∨ mem_constraint c proved) lf
End

Triviality list_pair_eq_thm:
  ∀xs ys. list_pair_eq xs ys ⇔ xs = ys
Proof
  Induct \\ rw []
  \\ Cases_on ‘ys’
  \\ simp [Once list_pair_eq_def]
  \\ PairCases_on ‘h’ \\ gvs []
  \\ CASE_TAC \\ fs []
QED

Theorem mem_constraint_thm:
  ∀xs c. mem_constraint c xs = MEM c xs
Proof
  Induct \\ fs [mem_constraint_def] \\ rw []
  \\ qsuff_tac ‘equal_constraint c h ⇔ c = h’ >- fs []
  \\ PairCases_on ‘c’
  \\ PairCases_on ‘h’
  \\ fs [equal_constraint_def,list_pair_eq_thm]
  \\ rw [] \\ eq_tac \\ rw []
QED

Definition check_red_def:
  check_red ord obj core fml id c s pfs idopt =
  (let fml_not_c = insert id (not c) fml in
    let w = subst_fun s in
    let rsubs = red_subgoals ord w c obj in
    case extract_clauses w fml rsubs pfs [] of
      NONE => NONE
    | SOME cpfs =>
    (case check_subproofs cpfs core fml_not_c (id+1) of
      NONE => NONE
    | SOME (fml',id') =>
      let chk =
        (case idopt of NONE =>
          (let goals = toAList (map_opt (subst_opt w) fml) in
          let (l,r) = extract_pids pfs LN LN in
            split_goals fml l goals ∧
            EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs)))
        | SOME cid =>
          check_contradiction_fml fml' cid) in
      if chk then
        SOME id'
      else NONE) )
End

Definition check_sstep_def:
  (check_sstep sstep ord obj core (fml:pbf) (id:num) =
  case sstep of
    Lstep lstep =>
    check_lstep lstep core fml id
  | Red c s pfs idopt =>
    (case check_red ord obj core fml id c s pfs idopt of
      SOME id' => SOME (insert id' c fml,id'+1)
    | NONE => NONE))
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
    SOME (fml',id') =>
     id ≤ id' ∧
     range fml ⊨ range fml' ∧
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
    rw[]
    >-
      metis_tac[sat_implies_def]>>
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
  sptree$lookup i (mk_BS t1 a t2) = lookup i (BS t1 a t2)
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

(* < on ints , treating NONE as infinity *)
Definition opt_lt_def:
  (opt_lt NONE _ ⇔ F) ∧
  (opt_lt (SOME _) NONE <=> T) ∧
  (opt_lt (SOME x) (SOME y) ⇔ x < (y:int))
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

Theorem lookup_extract_pids_l:
  ∀ls accl accr l r.
  extract_pids ls accl accr = (l,r) ∧
  lookup i l ≠ NONE ⇒
  lookup i accl ≠ NONE ∨
  ∃n pf.
    MEM (SOME (INL i,n),pf) ls
Proof
  Induct>>rw[extract_pids_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>rw[lookup_insert]>>
  metis_tac[PAIR]
QED

Theorem lookup_extract_pids_r:
  ∀ls accl accr l r.
  extract_pids ls accl accr = (l,r) ∧
  lookup i r ≠ NONE ⇒
  lookup i accr ≠ NONE ∨
  ∃n pf.
    MEM (SOME (INR i,n),pf) ls
Proof
  Induct>>rw[extract_pids_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>rw[lookup_insert]>>
  metis_tac[PAIR]
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

Theorem split_goals_checked:
  split_goals fml proved goals ∧
  MEM (n,yy) goals ⇒
  yy ∈ range fml ∨
  ∃i.
    lookup i proved ≠ NONE ∧
    MEM (i,yy) goals
Proof
  rw[split_goals_def,mem_constraint_thm]>>
  pairarg_tac>>fs[PARTITION_DEF]>>
  pop_assum (ASSUME_TAC o SYM)>>
  drule PARTs_HAVE_PROP>>
  drule PART_MEM>>rw[]>>
  last_x_assum(qspec_then`(n,yy)` assume_tac)>>gvs[]>>
  first_x_assum drule>>
  rw[]
  >- metis_tac[]>>
  fs[EVERY_MEM]>>
  last_x_assum drule>>rw[MEM_MAP]
  >-
    metis_tac[]
  >- (
    first_x_assum drule>>rw[]>>
    pairarg_tac>>gvs[]>>
    metis_tac[])
QED

Theorem sat_obj_po_insert_contr:
  id ∉ domain fml ∧
  unsatisfiable (range fml ∪ {not c}) ⇒
  sat_obj_po ord obj (range fml) (c INSERT range fml)
Proof
  rw[sat_obj_po_def,unsatisfiable_def,satisfiable_def]>>
  first_assum (irule_at Any)>>
  rw[]
  >-
    metis_tac[not_thm]>>
  Cases_on`ord`>>
  fs[]>>
  metis_tac[reflexive_def,reflexive_po_of_spo,PAIR]
QED

Theorem check_red_correct:
  id_ok fml id ∧ domain core ⊆ domain fml ∧
  OPTION_ALL good_spo ord ∧
  check_red ord obj core fml id c s pfs idopt = SOME id' ⇒
  id ≤ id' ∧
  sat_obj_po ord obj (range fml) (c INSERT range fml)
Proof
  simp[check_red_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  `id_ok (insert id (not c) fml) (id+1)` by
    gs[id_ok_def]>>
  drule check_subproofs_correct>>
  rename1`check_subproofs pffs`>>
  disch_then(qspecl_then [`pffs`,`core`] assume_tac)>>
  gvs[SUBSET_DEF]>>
  reverse every_case_tac
  >- (
    match_mp_tac sat_obj_po_insert_contr>>fs[id_ok_def]>>
    drule check_contradiction_fml_unsat>>
    gs[sat_implies_def,satisfiable_def,unsatisfiable_def,range_insert]>>
    metis_tac[])>>
  qsuff_tac ‘redundant_wrt_obj_po (range fml) ord obj c’
  >- (
    fs [redundant_wrt_obj_po_def] \\ rw []
    \\ irule sat_obj_po_fml_SUBSET
    \\ pop_assum $ irule_at Any
    \\ rw [SUBSET_DEF] \\ imp_res_tac range_insert_2 \\ fs [])
  \\ pairarg_tac \\ fs[]
  \\ match_mp_tac (GEN_ALL substitution_redundancy_obj_po)
  \\ simp[]
  \\ qexists_tac ‘subst_fun s’ \\ fs []
  \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]
  \\ `id ∉ domain fml` by fs[id_ok_def]
  \\ simp [Once implies_explode]
  \\ qpat_x_assum`!x. _ ⇒ _ ∈ domain fml` kall_tac
  \\ gvs[red_subgoals_def,MEM_COUNT_LIST,ADD1]
  \\ reverse (rw [])
  >- (
    (* dominance *)
    rw[sat_implies_EL]>>
    last_x_assum(qspec_then`SUC n` assume_tac)>>
    gvs[]>>
    drule_all lookup_extract_pids_r>> rw[]
    \\ drule extract_clauses_MEM_INR
    \\ disch_then drule
    \\ fs[EL]
    \\ DEP_REWRITE_TAC [EL_APPEND_EQN] \\ simp[]
    \\ rw[]
    \\ first_x_assum drule \\ strip_tac
    \\ gs[EL_MAP]
    \\ drule unsatisfiable_not_sat_implies
    \\ simp[range_insert]
    \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
  >- (
    (* objective *)
    Cases_on`obj`>>
    last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun s) ord))` assume_tac)>>
    fs[]>>
    drule_all lookup_extract_pids_r>>rw[]
    \\ drule extract_clauses_MEM_INR
    \\ disch_then drule
    \\ fs[EL]
    \\ DEP_REWRITE_TAC [EL_APPEND2]
    \\ simp[]
    \\ rw[]
    \\ first_x_assum drule \\ strip_tac
    \\ gs[]
    \\ drule unsatisfiable_not_sat_implies
    \\ simp[range_insert]
    \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
  >- (
    (* redundancy #0 *)
    last_x_assum(qspec_then`0` assume_tac)>>
    fs[]>>
    drule_all lookup_extract_pids_r>>rw[]
    \\ drule extract_clauses_MEM_INR
    \\ disch_then drule
    \\ fs[]
    \\ rw[]
    \\ first_x_assum drule \\ strip_tac
    \\ fs[]
    \\ drule unsatisfiable_not_sat_implies
    \\ simp[range_insert]
    \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
  (* rest of redundancy *)
  \\ gvs [GSYM unsat_iff_implies]
  \\ pop_assum mp_tac
  \\ simp [Once range_def] \\ rw []
  \\ rename [‘lookup a fml = SOME xx’]
  \\ Cases_on ‘subst_opt (subst_fun s) xx’ \\ fs []
  THEN1
   (imp_res_tac subst_opt_NONE
    \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
    \\ fs [satisfies_def,range_def,PULL_EXISTS]
    \\ metis_tac[])
  \\ rename1`subst_opt _ _ = SOME yy`
  \\ `MEM (a,yy) (toAList (map_opt (subst_opt (subst_fun s)) fml))` by
    simp[MEM_toAList,lookup_map_opt]
  \\ drule_all split_goals_checked \\ rw[]
  >- (
    fs[satisfiable_def,not_thm,satisfies_def]>>
    metis_tac[subst_opt_SOME])
  \\ drule_all lookup_extract_pids_l>>rw[]
  \\ drule extract_clauses_MEM_INL
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ gvs[unsatisfiable_def, MEM_toAList,lookup_map_opt]
  \\ simp[range_insert]
  \\ metis_tac[INSERT_SING_UNION,UNION_COMM,subst_opt_SOME]
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
    TOP_CASE_TAC>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    rw[]>>
    TOP_CASE_TAC>>gvs[]>>
    drule_all check_red_correct>>
    simp[]>>
    strip_tac>>
    CONJ_TAC >-
      fs[id_ok_def]>>
    CONJ_TAC>-
      gvs[id_ok_def,SUBSET_DEF]>>
    CONJ_TAC>- (
      DEP_REWRITE_TAC[inter_insert_NOTIN]>>
      fs[id_ok_def]>>
      last_x_assum(qspec_then`x'` assume_tac)>>
      fs[SUBSET_DEF]>>
      metis_tac[])>>
    DEP_REWRITE_TAC[range_insert]>>
    fs[id_ok_def])
QED

Definition sstep_ok_def[simp]:
  (sstep_ok (Lstep l) ⇔ lstep_ok l) ∧
  (sstep_ok (Red n _ pfs idopt) ⇔
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
  rw[opt_lt_def]>>
  intLib.ARITH_TAC
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
  simp[]>>
  reverse CONJ_TAC >-
    metis_tac[integerTheory.INT_LE_TRANS]>>
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
  | Dom npbc subst (( ((num + num) # num) option, (lstep list)) alist) (num option)
  | LoadOrder mlstring (num list)
  | UnloadOrder
  | StoreOrder mlstring (npbc list # var list # var list)
      (var list)
      (( ((num + num) # num) option, (lstep list)) alist)
  | Transfer (num list) (* Ids to move into core *)
  | CheckedDelete num
      subst
      (( ((num + num) # num) option, (lstep list)) alist)
      (num option)
  | UncheckedDelete (num list)
  | Sstep sstep
  | Obj (bool spt)
  | ChangeObj ((int # var) list # int) num num
    (* Change the objective using the two constraint IDs *)
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
*)

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

Definition nn_int_def:
  nn_int i = if i < 0 then 0:num else Num i
End

(* For a bound b, the model improving constraint is
  f ≤ b-1 = f < b = not (f ≥ b)
*)
Definition model_improving_def:
  model_improving fopt (v:int) =
  case fopt of
    SOME (f,c) =>
       not ((f,nn_int(v-c)):npbc)
  | _ =>
       not (([],nn_int v):npbc)
End

Theorem satisfies_npbc_model_improving:
  satisfies_npbc w (model_improving obj ov) ⇔
  eval_obj obj w < ov
Proof
  fs[model_improving_def,eval_obj_def]>>
  every_case_tac>>
  rw[not_thm,satisfies_npbc_def,nn_int_def]>>
  intLib.ARITH_TAC
QED

Definition coref_def:
  coref (core:num_set) fml =
  inter fml core
End

(* The list of subgoals for dominance
  numbered #0 ... *)
Definition neg_dom_subst_def:
  (neg_dom_subst w ((f,us,vs),xs) =
  let us_xs = list_list_insert us xs in
  let vs_xs = list_list_insert vs xs in
  let ww = (λn.
    case lookup n vs_xs of
      SOME v =>
        (case w v of NONE => SOME (INR (Pos v)) | r => r)
    | NONE =>
        (case lookup n us_xs of
         | SOME v => SOME (INR (Pos v))
         | NONE => NONE)) in
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

(* the substituted LHS and RHS for transitivity *)
Definition trans_subst_def:
  (trans_subst (f,us,vs) ws =
  let us_vs = list_list_insert us vs in
  let vs_ws = list_list_insert vs ws in
  let lsubst =
    (λn. case lookup n us_vs of
         | SOME x => SOME (INR (Pos x))
         | NONE => case lookup n vs_ws of
                   | SOME x => SOME (INR (Pos x))
                   | NONE => NONE) in
  let lhs = f ++ MAP (subst lsubst) f in
  let rsubst =
    (λn. case lookup n vs_ws of
         | SOME x => SOME (INR (Pos x))
         | NONE => NONE) in
  let rhs = MAP (subst rsubst) f in
  (lhs,rhs))
End

Definition check_good_ord_def:
  check_good_ord (f,us,vs) ⇔
  LENGTH us = LENGTH vs ∧
  let uvs = us ++ vs in
  ALL_DISTINCT uvs ∧
  EVERY (λx. MEM x uvs) (FLAT (MAP (MAP SND o FST) f))
End

Theorem check_good_ord_good_ord:
  check_good_ord ord ⇒
  good_ord ord
Proof
  PairCases_on`ord`>>EVAL_TAC>>
  simp[EVERY_MEM,MEM_FLAT,SUBSET_DEF,PULL_EXISTS,FORALL_PROD,npbc_vars_def,MEM_MAP]>>rw[]>>
  metis_tac[]
QED

Definition check_transitivity_def:
  check_transitivity ord ws pfs =
  let (lhs,rhs) = trans_subst ord ws in
  let fml = build_fml 1 lhs in
  let id = LENGTH lhs + 1 in
  let dsubs = MAP (λc. [not c]) rhs in
  case extract_clauses (λn. NONE) LN dsubs pfs [] of
    NONE => F
  | SOME cpfs =>
  (case check_subproofs cpfs LN fml id of
    SOME (fml',id') =>
    let (l,r) = extract_pids pfs LN LN in
       EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH dsubs))
  | _ => F)
End

Definition check_ws_def:
  check_ws (f,us,vs) ws ⇔
  LENGTH us = LENGTH ws ∧
  ALL_DISTINCT ws ∧
  EVERY (λy. ¬ MEM y us ∧ ¬ MEM y vs) ws
End

(* f + c ≤ f' + c' <--> f' + f ≥ *)
Definition model_bounding_def:
  model_bounding (f,c:int) (f',c':int) =
  let (add,n) = add_lists f' (MAP (λ(c,l). (-c,l)) f) in
    (add,
      nn_int(&SUM (MAP (λi. Num (ABS (FST i))) f) - &n + c - c'))
End

Theorem ge_nn_int:
  n ≥ nn_int i ⇔
  &n ≥ i
Proof
  rw[nn_int_def]>>
  intLib.ARITH_TAC
QED

Theorem satisfies_npbc_model_bounding:
  satisfies_npbc w (model_bounding fc fc') ⇔
  eval_obj (SOME fc) w <=
  eval_obj (SOME fc') w
Proof
  Cases_on`fc`>>rename1`SOME (f,c)`>>
  Cases_on`fc'`>>rename1`_ ≤ eval_obj (SOME (f',c')) _`>>
  fs[model_bounding_def,eval_obj_def]>>
  rpt(pairarg_tac>>fs[])>>
  simp[satisfies_npbc_def,add_ge]>>
  drule add_lists_thm >>
  disch_then(qspec_then`w` assume_tac)>>
  fs[not_lhs,ge_nn_int]>>
  `SUM (MAP (eval_term w) f') +
  SUM (MAP (λi. Num (ABS (FST i))) f) =
  SUM (MAP (eval_term w) f) + (n + SUM (MAP (eval_term w) add'))` by
    (pop_assum sym_sub_tac>>
    DEP_REWRITE_TAC[ADD_SUB]>>
    simp[]>>
    CONJ_ASM1_TAC>-
      metis_tac[ABS_coeff_ge]>>
    simp[])>>
  intLib.ARITH_TAC
QED

Theorem imp_model_bounding:
  imp c (model_bounding fc fc') ∧
  satisfies_npbc w c ⇒
  eval_obj (SOME fc) w ≤ eval_obj (SOME fc') w
Proof
  rw[]>>
  imp_res_tac imp_thm>>
  fs[satisfies_npbc_model_bounding]
QED

Definition check_change_obj_def:
  check_change_obj fml core chk obj ord fc' n1 n2 ⇔
  case obj of NONE => F
  | SOME fc =>
    case (lookup n1 fml, lookup n2 fml) of
      (SOME c1, SOME c2) =>
      (chk ∨ IS_SOME ord ⇒ lookup n1 core = SOME ()) ∧
      imp c1 (model_bounding fc fc') ∧
      imp c2 (model_bounding fc' fc)
    | _ => F
End

(* TODO: make chk toggle-able? *)
Definition check_cstep_def:
  (check_cstep cstep
    (fml:pbf) (id:num) core
    chk obj (bound:int option)
    ord orders =
  case cstep of
  | Dom c s pfs idopt =>
    (case ord of NONE => NONE
    | SOME spo =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      let dsubs = dom_subgoals spo w c obj in
      case extract_clauses w fml dsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs core fml_not_c (id+1) of
        NONE => NONE
      | SOME (fml',id') =>
        let check =
          (case idopt of NONE =>
            let cf = coref core fml in
            let goals = toAList (map_opt (subst_opt w) cf) in
            let (l,r) = extract_pids pfs LN LN in
              split_goals fml l goals ∧
              EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH dsubs))
          | SOME cid =>
            check_contradiction_fml fml' cid) in
        if check then
          SOME (insert id' c fml, id'+1, core, chk, obj, bound, ord, orders)
        else NONE )))
  | LoadOrder name xs =>
      (case ALOOKUP orders name of NONE => NONE
      | SOME ord' =>
        if LENGTH xs = LENGTH (FST (SND ord')) then
          SOME (fml, id,
            fromAList (MAP (λ(x,y). (x,())) (toAList fml)),
            chk, obj, bound, SOME (ord',xs) , orders)
        else NONE)
  | UnloadOrder =>
    (case ord of NONE => NONE
    | SOME spo =>
        SOME (fml, id, core, chk, obj, bound, NONE, orders))
  | StoreOrder name spo ws pfs =>
    if check_good_ord spo ∧ check_ws spo ws ∧
      check_transitivity spo ws pfs then
      SOME (fml, id, core, chk, obj, bound, ord, (name,spo)::orders)
    else
      NONE
  | Transfer ls =>
    if EVERY (λid. lookup id fml ≠ NONE) ls
    then SOME (fml, id,
               FOLDL (λa b. insert b () a) core ls,
               chk, obj, bound, ord, orders)
    else NONE
  | CheckedDelete n s pfs idopt => (
    case lookup n fml of
      NONE => NONE
    | SOME c =>
      if lookup n core = SOME ()
      then
        (let nc = delete n core in
        let ncf = coref nc fml in
        case check_red ord obj nc ncf id c s pfs idopt of
          SOME id' =>
          SOME (delete n fml, id', nc,
                chk, obj, bound, ord, orders)
        | NONE => NONE)
      else NONE)
  | UncheckedDelete ls =>
      (* Either no order or all ids are in core *)
      if ord = NONE ∨ domain fml ⊆ domain core then
          SOME (FOLDL (λa b. delete b a) fml ls, id,
                FOLDL (λa b. delete b a) core ls,
                F, obj, bound, ord, orders)
      else NONE
  | Sstep sstep =>
    (case check_sstep sstep ord obj core fml id of
      SOME(fml',id') =>
        SOME (fml',id',core,chk,obj,bound,ord, orders)
    | NONE => NONE)
  | Obj w =>
    (case check_obj obj bound w (coref core fml) of
      NONE => NONE
    | SOME new =>
      let c = model_improving obj new in
      SOME (
        insert id c fml,id+1,
        insert id () core,
        chk, obj, SOME new, ord, orders))
  | ChangeObj fc' n1 n2 =>
    if check_change_obj fml core chk obj ord fc' n1 n2 then
      SOME (
      fml, id, core, chk, SOME fc', bound, ord, orders)
    else NONE
  )
End

Definition valid_conf_def:
  valid_conf ord obj core fml ⇔
  domain core ⊆ domain fml ∧
  (IS_SOME ord ⇒
    sat_obj_po ord obj
      (range (coref core fml)) (range fml))
End

Theorem range_coref_delete:
  h ∉ domain core ⇒
  range (coref core (delete h fml)) =
  range (coref core fml)
Proof
  rw[coref_def]>>
  fs[range_def]>>
  rw[EXTENSION,EQ_IMP_THM]>>
  fs[lookup_inter]>>rw[]>>
  fs[lookup_delete]>>
  every_case_tac>>gvs[AllCaseEqs(),domain_lookup]>>
  metis_tac[]
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
  valid_conf ord obj core fml ∧
  EVERY (λid. id ∉ domain core) l ⇒
  valid_conf ord obj core (FOLDL (λa b. delete b a) fml l)
Proof
  strip_tac>>
  fs[valid_conf_def,domain_FOLDL_delete]>>
  CONJ_ASM1_TAC >- (
    fs[SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM,domain_lookup]>>
    metis_tac[option_CLAUSES])>>
  rw[]>>gs[]>>
  DEP_REWRITE_TAC [range_coref_FOLDL_delete]>>
  fs[sat_obj_po_def]>>
  rw[]>>first_x_assum drule>>
  rw[]>>
  qexists_tac`w'`>>
  fs[satisfies_def]>>
  metis_tac[range_FOLDL_delete,SUBSET_DEF]
QED

Theorem valid_conf_delete:
  valid_conf ord obj core fml ∧
  id ∉ domain core ⇒
  valid_conf ord obj core (delete id fml)
Proof
  rw[]>>drule valid_conf_FOLDL_delete>>
  disch_then(qspec_then`[id]` mp_tac)>>simp[]
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
  simp[lookup_delete,lookup_inter]>>rw[]>>
  fs[AllCaseEqs()]
  >- (
    match_mp_tac wf_delete>>
    simp[])>>
  metis_tac[option_CLAUSES]
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
  gvs[lookup_inter,domain_lookup,AllCaseEqs()]>>
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
  imp_obj v fopt1 C1 fopt2 C2 ⇔
  (sat_obj_le fopt1 v C1 ⇒ sat_obj_le fopt2 v C2)
End

Definition bimp_obj_def:
  bimp_obj bound fopt1 C1 fopt2 C2 ⇔
  ∀v. opt_lt (SOME v) bound ⇒
    imp_obj v fopt1 C1 fopt2 C2
End

Definition good_ord_t_def:
  good_ord_t ord ⇔
  ∀xs.
  LENGTH xs = LENGTH (FST (SND ord)) ⇒
  good_spo (ord,xs)
End

Theorem opt_lt_irref[simp]:
  ¬ (opt_lt x x)
Proof
  Cases_on`x`>>
  rw[opt_lt_def]
QED

Theorem opt_le_refl[simp]:
  (opt_le x x)
Proof
  rw[opt_le_def]
QED

Theorem bimp_obj_refl[simp]:
  bimp_obj bound obj X obj X
Proof
  rw[bimp_obj_def,imp_obj_def]
QED

Theorem sat_obj_po_bimp_obj:
  sat_obj_po ord obj A B ⇒
  bimp_obj bound obj A obj B
Proof
  rw[sat_obj_po_def,bimp_obj_def,imp_obj_def,sat_obj_le_def]>>
  first_x_assum drule>>
  rw[]>>
  asm_exists_tac>>
  simp[]>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

Theorem sat_obj_po_more:
  sat_obj_po ord obj A B ∧ A ⊆ C ⇒
  sat_obj_po ord obj C B
Proof
  rw[sat_obj_po_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem coref_fromAList_fml:
  range (coref (fromAList (MAP (λ(x,y). (x,())) (toAList fml))) fml) =
  range fml
Proof
  simp[range_def,lookup_inter,coref_def,lookup_fromAList,ALOOKUP_MAP,EXTENSION,ALOOKUP_toAList]>>
  rw[]>>eq_tac>>rw[]>>simp[PULL_EXISTS]>>
  fs[AllCaseEqs()]>>
  metis_tac[]
QED

Theorem imp_obj_SUBSET:
  B ⊆ A ⇒
  imp_obj v obj A obj B
Proof
  rw[imp_obj_def,sat_obj_le_def]>>
  first_x_assum (irule_at Any)>>
  metis_tac[satisfies_SUBSET]
QED

Theorem bimp_obj_SUBSET:
  B ⊆ A ⇒
  bimp_obj bound obj A obj B
Proof
  rw[bimp_obj_def]>>
  metis_tac[imp_obj_SUBSET]
QED

Theorem range_toAList:
  range t = set (MAP SND (toAList t))
Proof
  rw[range_def,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList]
QED

Theorem id_ok_build_fml:
  ∀ls n.
  n + LENGTH ls ≤ id ⇒
  id_ok (build_fml n ls) id
Proof
  Induct>>rw[]>>fs[build_fml_def,id_ok_def]
QED

Triviality subst_eta:
  subst f = subst (λx. f x)
Proof
  fs [SF ETA_ss]
QED

Theorem trivial_valid_conf:
  OPTION_ALL good_spo ord ∧
  domain core = domain fml ⇒
  valid_conf ord obj core fml
Proof
  rw[valid_conf_def]>>
  `range (coref core fml) = range fml` by (
    rw[coref_def,range_def,EXTENSION,lookup_inter]>>
    fs[EXTENSION,domain_lookup,PULL_EXISTS,AllCaseEqs()]>>
    rw[]>>eq_tac>>rw[]>>gvs[]>>
    metis_tac[])>>
  metis_tac[sat_obj_po_refl]
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

Theorem lookup_coref_1:
  lookup x (coref core fml) = SOME y ⇒
  lookup x fml = SOME y
Proof
  simp[coref_def,lookup_inter,domain_lookup,SUBSET_DEF,AllCaseEqs()]
QED

Theorem lookup_coref_2:
  lookup x fml = SOME z ∧
  lookup x core = SOME () ⇒
  lookup x (coref core fml) = SOME z
Proof
  simp[coref_def,lookup_inter,domain_lookup,SUBSET_DEF,AllCaseEqs()]
QED

Theorem range_coref_insert_notin:
  n ∉ domain core ⇒
  range (coref core (insert n c fml)) =
  range (coref core fml)
Proof
  rw[coref_def]>>
  fs[range_def]>>
  rw[EXTENSION,EQ_IMP_THM]>>
  fs[domain_lookup,lookup_inter,lookup_insert,AllCaseEqs()]>>rw[]>>
  metis_tac[]
QED

Theorem range_coref_SUBSET:
  domain core ⊆ domain fml ⇒
  range (coref core fml) ⊆ range fml
Proof
  rw[range_def,SUBSET_DEF]>>
  metis_tac[lookup_coref_1]
QED

Theorem range_coref_insert:
  lookup h fml = SOME c ⇒
  range (coref (insert h () core) fml) =
  c INSERT range (coref core fml)
Proof
  rw[coref_def,range_def,EXTENSION,lookup_inter,lookup_insert,AllCaseEqs()]>>
  rw[EQ_IMP_THM]>>fs[]>>
  metis_tac[]
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

Theorem domain_coref:
  domain (coref core fml) =
  domain core ∩ domain fml
Proof
  rw[coref_def,INTER_COMM]
QED

Theorem range_coref_cong:
  (∀x. sptree$lookup x (inter a core) = lookup x (inter fml core))
  ⇒
  range (coref core fml) = range (coref core a)
Proof
  rw[range_def,coref_def,EXTENSION,EQ_IMP_THM]
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

Theorem check_cstep_correct:
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  EVERY (good_ord_t o SND) orders ∧
  valid_conf ord obj core fml ⇒
  case check_cstep cstep fml id core chk obj bound ord orders of
  | SOME (fml',id',core',chk',obj',bound',ord',orders') =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      valid_conf ord' obj' core' fml' ∧
      opt_le bound' bound ∧
      (opt_lt bound' bound ⇒
        sat_obj_le obj (THE bound') (range (coref core fml))) ∧
      bimp_obj bound'
        obj (range fml) obj' (range fml') ∧
      (chk' ⇒
      bimp_obj bound'
        obj' (range (coref core' fml'))
        obj (range (coref core fml))) ∧
      (chk' ⇒ chk) ∧
      OPTION_ALL good_spo ord' ∧
      EVERY (good_ord_t o SND) orders'
  | NONE => T
Proof
  Cases_on`cstep`>>
  fs[check_cstep_def]
  >- ( (* Dominance *)
    Cases_on`ord`>>fs[]>>
    TOP_CASE_TAC>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    rw[]>>gvs[]>>
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
    simp[opt_le_def,GSYM CONJ_ASSOC]>>
    CONJ_TAC >-
      fs[SUBSET_DEF]>>
    CONJ_ASM1_TAC>- (
      reverse (every_case_tac)
      >- (
        `sat_obj_po (SOME x) obj (range fml) (range (insert cc p fml))` by (
        DEP_REWRITE_TAC[range_insert]>>
        CONJ_TAC >- fs[id_ok_def]>>
        match_mp_tac sat_obj_po_insert_contr>>fs[id_ok_def]>>
        drule check_contradiction_fml_unsat>>
        gs[sat_implies_def,satisfiable_def,unsatisfiable_def,range_insert]>>
        metis_tac[])>>
        metis_tac[OPTION_ALL_def,sat_obj_po_trans])>>
      pairarg_tac>>fs[]>>
      simp[sat_obj_po_def]>>
      DEP_REWRITE_TAC[range_insert]>>
      CONJ_TAC >- fs[id_ok_def]>>
      simp[satisfies_simp]>>
      simp[GSYM CONJ_ASSOC]>>
      PairCases_on`x`>>
      match_mp_tac (GEN_ALL good_spo_dominance)>>
      simp[]>>
      qexists_tac ‘subst_fun v’>>fs[]>>
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
        \\ drule_all lookup_coref_1
        \\ strip_tac
        \\ Cases_on ‘subst_opt (subst_fun v) xx’ \\ fs []
        THEN1 (
          imp_res_tac subst_opt_NONE
          \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
          \\ fs [satisfies_def,range_def,PULL_EXISTS]
          \\ metis_tac[])
        \\ rename1`subst_opt _ _ = SOME yy`
        \\ `MEM (a,yy) (toAList (map_opt (subst_opt (subst_fun v)) (coref core fml)))` by simp[MEM_toAList,lookup_map_opt]
        \\ drule_all split_goals_checked \\ rw[]
        >- (
          fs[satisfiable_def,not_thm,satisfies_def]>>
          fs[range_def]>>
          metis_tac[subst_opt_SOME])
        \\ drule_all lookup_extract_pids_l>>rw[]
        \\ drule extract_clauses_MEM_INL
        \\ disch_then drule
        \\ strip_tac
        \\ last_x_assum drule
        \\ gvs[unsatisfiable_def,satisfiable_def, MEM_toAList,lookup_map_opt,AllCaseEqs(),satisfies_def]
        \\ fs[not_thm,range_def,PULL_EXISTS]
        \\ drule_all lookup_coref_1 \\ rw[]
        \\ `subst (subst_fun v) c = subst (subst_fun v) xx` by
          metis_tac[subst_opt_SOME,lookup_coref_1]
        \\ metis_tac[])>>
      CONJ_TAC >- (
        (* order constraints *)
        simp[GSYM LIST_TO_SET_MAP]>>
        rw[sat_implies_EL,EL_MAP]>>
        last_x_assum(qspec_then`n` assume_tac)>>
        gvs[dom_subst_def]>>
        drule_all lookup_extract_pids_r>>
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
        simp[lookup_list_list_insert,ALOOKUP_ZIP_MAP]>>
        metis_tac[INSERT_SING_UNION,UNION_COMM])>>
      CONJ_TAC >- (
        (* negated order constraint *)
        last_x_assum(qspec_then`LENGTH (dom_subst (subst_fun v) (SOME ((x0,x1,x2),x3)))` assume_tac)>>
        gs[ADD1]>>
        drule_all lookup_extract_pids_r>>
        simp[]>> rw[]
        \\ drule extract_clauses_MEM_INR
        \\ disch_then drule
        \\ fs[]
        \\ DEP_REWRITE_TAC [EL_APPEND2]
        \\ simp[]
        \\ rw[]
        \\ first_x_assum drule \\ strip_tac
        \\ gs[neg_dom_subst_def,lookup_list_list_insert,ALOOKUP_ZIP_MAP]
        \\ metis_tac[INSERT_SING_UNION,UNION_COMM,LIST_TO_SET_MAP])>>
      (* objective constraint *)
      Cases_on`obj`>>
      simp[]>>
      last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun v) (SOME ((x0,x1,x2),x3))))` assume_tac)>>
      gs[ADD1]>>
      drule_all lookup_extract_pids_r>>
      simp[]>>rw[]
      \\ drule extract_clauses_MEM_INR
      \\ disch_then drule
      \\ fs[]
      \\ DEP_REWRITE_TAC [EL_APPEND2]
      \\ simp[]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ gs[]
      \\ drule unsatisfiable_not_sat_implies
      \\ metis_tac[INSERT_SING_UNION,UNION_COMM])>>
    match_mp_tac (GEN_ALL sat_obj_po_bimp_obj)>>
    qexists_tac`SOME x`>>
    drule sat_obj_po_more>>
    disch_then match_mp_tac>>
    metis_tac[range_coref_SUBSET])
  >- ( (* LoadOrder *)
    every_case_tac>>
    simp[]>>
    drule ALOOKUP_MEM>>
    fs[EVERY_MEM,Once FORALL_PROD]>>
    strip_tac>>
    strip_tac>>
    first_x_assum drule>>
    simp[good_ord_t_def]>>strip_tac>>
    fs[valid_conf_def]>>
    simp[coref_fromAList_fml,sat_obj_po_refl]>>
    CONJ_TAC>- (
      simp[domain_fromAList,SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,MEM_toAList]>>
      simp[domain_lookup])>>
    rw[]>>match_mp_tac bimp_obj_SUBSET>>
    metis_tac[range_coref_SUBSET])
  >- ( (* UnloadOrder *)
    rw[]>>
    every_case_tac>>
    fs[valid_conf_def,opt_le_def,bimp_obj_refl])
  >- ( (* StoreOrder *)
    rw[]>>fs[opt_le_def,bimp_obj_refl]>>
    rw[good_ord_t_def,good_spo_def]
    >-
      metis_tac[check_good_ord_good_ord]>>
    PairCases_on`p`>>
    match_mp_tac (transitive_po_of_spo |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
    gvs[check_transitivity_def,check_ws_def]>>
    rename1`ALL_DISTINCT ws`>>
    qexists_tac`ws`>>fs[EVERY_MEM]>>
    rw[]
    >-
      metis_tac[check_good_ord_good_ord]>>
    fs[trans_subst_def,lookup_list_list_insert]>>
    every_case_tac>>fs[]>>
    qmatch_asmsub_abbrev_tac`check_subproofs _ coree fmll idd`>>
    `id_ok fmll idd ∧ domain coree ⊆ domain fmll` by
      (unabbrev_all_tac>>simp[]>>
      match_mp_tac id_ok_build_fml>>
      simp[])>>
    drule check_subproofs_correct>>
    disch_then drule>>
    disch_then (qspec_then`x` mp_tac)>>simp[]>>
    TOP_CASE_TAC>>
    rw[]>>
    simp[GSYM LIST_TO_SET_MAP]>>
    rw[sat_implies_EL]>>
    fs[MEM_COUNT_LIST]>>
    pairarg_tac>>gs[]>>
    first_x_assum drule>>
    rw[]>>
    drule_all lookup_extract_pids_r>>
    simp[Abbr`coree`]>>
    rw[]>>
    drule extract_clauses_MEM_INR>>
    disch_then drule>>
    simp[EL_MAP]>>
    rw[]>>
    fs[EVERY_MEM]>>
    first_x_assum drule>>
    simp[]>>rw[]>>
    drule unsatisfiable_not_sat_implies>>
    simp[range_build_fml,Abbr`fmll`] >>
    once_rewrite_tac [subst_eta] >> fs [] >>
    gvs [ALOOKUP_APPEND,ALOOKUP_ZIP_MAP] >>
    qmatch_goalsub_abbrev_tac ‘subst f1’ >> strip_tac >>
    qmatch_goalsub_abbrev_tac ‘subst f2’ >>
    qsuff_tac ‘f1 = f2’ >- (rw [] >> gvs []) >>
    unabbrev_all_tac >>
    fs [FUN_EQ_THM] >> rw [] >>
    ntac 4 (CASE_TAC >> fs []))
  >- (
    (* Transfer *)
    strip_tac>>
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
      rw[]>>gs[]>>
      drule (GEN_ALL sat_obj_po_trans)>>
      disch_then match_mp_tac>>
      first_x_assum (irule_at Any)>>
      fs[sat_obj_po_def]>>
      rw[]>>
      asm_exists_tac>>simp[]>>
      Cases_on`ord`>>fs[good_spo_def]>>
      metis_tac[reflexive_def,reflexive_po_of_spo,PAIR])>>
    rw[]>>
    rw[bimp_obj_def,imp_obj_def]>>
    fs[sat_obj_po_def]>>rw[]
    >- (
      fs[sat_obj_le_def]>>
      first_x_assum (irule_at Any)>>
      simp[]))
  >- ( (* CheckedDelete *)
    rw[]>>
    every_case_tac>>fs[]>>
    `id_ok (coref (delete n core) fml) id` by
      (fs[id_ok_def,domain_coref,valid_conf_def]>>
      metis_tac[SUBSET_DEF])>>
    `domain (delete n core) ⊆ domain (coref (delete n core) fml)` by
      fs[domain_delete,domain_coref,valid_conf_def,SUBSET_DEF]>>
    drule_all check_red_correct>>
    simp[]>>strip_tac>>
    CONJ_TAC >-
      fs[id_ok_def]>>
    `x INSERT range (coref (delete n core) fml) = range (coref core fml)` by (
      fs[GSYM delete_coref]>>
      rw[EXTENSION,EQ_IMP_THM]
      >- (
        rw[range_def]>>
        metis_tac[lookup_coref_2])
      >- (
        fs[range_def,lookup_delete]>>
        metis_tac[])>>
      simp[EQ_SYM_EQ]>>
      match_mp_tac range_delete_IN>>
      fs[]>>
      metis_tac[lookup_coref_2])>>
    pop_assum SUBST_ALL_TAC>>
    CONJ_TAC >-(
      match_mp_tac valid_conf_delete>>
      simp[]>>
      match_mp_tac (GEN_ALL valid_conf_del_core)>>
      simp[]>>asm_exists_tac>>
      simp[]>>
      metis_tac[delete_coref])>>
    CONJ_TAC >- (
      match_mp_tac bimp_obj_SUBSET>>
      fs[range_delete])>>
    rw[]>>
    match_mp_tac sat_obj_po_bimp_obj>>
    fs[delete_coref]>>
    DEP_REWRITE_TAC[range_coref_delete]>>
    simp[])
  >- ( (* UncheckedDelete *)
    strip_tac>>
    IF_CASES_TAC >> simp[]>>
    CONJ_TAC >- metis_tac[id_ok_FOLDL_delete] >>
    CONJ_TAC >- (
      fs[]
      >- (
        simp[valid_conf_def]>>
        simp[domain_FOLDL_delete]>>
        fs[valid_conf_def]>>
        fs[SUBSET_DEF,EXTENSION])>>
      match_mp_tac trivial_valid_conf>>
      simp[domain_FOLDL_delete]>>
      fs[valid_conf_def]>>
      fs[SUBSET_DEF,EXTENSION]>>
      metis_tac[])>>
    simp[bimp_obj_def]>>rw[]>>
    match_mp_tac imp_obj_SUBSET>>
    simp[range_FOLDL_delete]   )
  >- (
    (* Sstep *)
    strip_tac>>
    drule check_sstep_correct>>
    fs[valid_conf_def]>>
    ntac 2 (disch_then drule)>>
    disch_then (qspecl_then [`s`,`obj`] mp_tac)>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    strip_tac>>
    drule range_coref_cong>>
    simp[bimp_obj_refl,opt_le_def]>>
    rw[]
    >- (
      imp_res_tac range_coref_SUBSET>>
      metis_tac[sat_obj_po_trans])
    >- (
      match_mp_tac sat_obj_po_bimp_obj>>
      simp[]))
  >- (
    (* Obj *)
    strip_tac>>
    simp[check_obj_def]>>
    IF_CASES_TAC>>fs[opt_le_def]>>
    qmatch_goalsub_abbrev_tac`model_improving obj ov`>>
    CONJ_TAC >- fs[id_ok_def]>>
    CONJ_TAC >- (
      fs[valid_conf_def]>>rw[]
      >- fs[SUBSET_DEF]>>
      fs[sat_obj_po_def]>>rw[]>>
      `id ∉ domain fml` by fs[id_ok_def]>>
      drule_all range_coref_insert_2>>
      rw[]>>gs[]>>
      first_x_assum drule>>
      rw[]>>
      qexists_tac`w'`>>simp[range_insert]>>
      fs[satisfies_npbc_model_improving]>>
      intLib.ARITH_TAC)>>
    CONJ_TAC
    >- (
      simp[sat_obj_le_def]>>
      qmatch_asmsub_abbrev_tac`eval_obj obj w`>>
      qexists_tac`w`>>simp[opt_le_def]>>
      fs[range_toAList,satisfies_def,EVERY_MEM])>>
    CONJ_TAC >- (
      `id ∉ domain fml` by fs[id_ok_def]>>
      simp[bimp_obj_def,imp_obj_def]>>
      rw[]>>
      fs[sat_obj_le_def,satisfies_npbc_model_improving,opt_lt_def]>>
      simp[range_insert]>>
      fs[sat_obj_le_def,satisfies_npbc_model_improving,opt_lt_def]>>
      first_assum (irule_at Any)>>
      fs[]>>
      intLib.ARITH_TAC)>>
    rw[]>>
    match_mp_tac bimp_obj_SUBSET>>
    DEP_REWRITE_TAC[range_coref_insert_2]>>
    fs[SUBSET_DEF,id_ok_def,valid_conf_def])
  >- ( (* ChangeObj *)
    strip_tac>>simp[]>>
    IF_CASES_TAC>>fs[check_change_obj_def]>>
    every_case_tac>>fs[]>>
    drule imp_model_bounding>>
    qpat_x_assum`imp _ _` mp_tac>>
    drule imp_model_bounding>>
    ntac 3 strip_tac>>
    CONJ_TAC >- (
      fs[valid_conf_def,sat_obj_po_def]>>strip_tac>>gs[]>>
      rw[]>>first_x_assum drule>>rw[]>>
      asm_exists_tac>>simp[]>>
      fs[satisfies_def,range_def]>>
      first_x_assum(qspec_then`w'` mp_tac)>>
      impl_tac >-
        metis_tac[]>>
      last_x_assum(qspec_then`w` mp_tac)>>
      impl_tac >- (
        first_x_assum match_mp_tac>>
        metis_tac[lookup_coref_2])>>
      intLib.ARITH_TAC)>>
    CONJ_TAC >- (
      rw[bimp_obj_def,imp_obj_def,sat_obj_le_def]>>
      asm_exists_tac>>simp[]>>
      first_x_assum(qspec_then`w` mp_tac)>>
      fs[satisfies_def,range_def]>>
      impl_tac >-
        metis_tac[]>>
      intLib.ARITH_TAC)>>
    fs[valid_conf_def]>>
    rw[bimp_obj_def,imp_obj_def,sat_obj_le_def]>>
    asm_exists_tac>>simp[]>>
    last_x_assum(qspec_then`w` mp_tac)>>
    fs[satisfies_def,range_def]>>
    impl_tac >- (
      first_x_assum match_mp_tac>>
      metis_tac[lookup_coref_2])>>
    intLib.ARITH_TAC)
QED

Definition check_csteps_def:
  (check_csteps [] fml id core chk obj bound ord orders =
    SOME (fml,id,core,chk,obj,bound,ord,orders)) ∧
  (check_csteps (s::ss) fml id core chk obj bound ord orders =
    case check_cstep s fml id core chk obj bound ord orders of
      SOME (fml',id',core',chk',obj',bound',ord',orders') =>
      check_csteps ss fml' id' core'
        chk' obj' bound' ord' orders'
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

Theorem bimp_obj_le:
  opt_le a b ∧
  bimp_obj b obj A obj' B ⇒
  bimp_obj a obj A obj' B
Proof
  rw[bimp_obj_def]>>
  metis_tac[opt_lt_le]
QED

Theorem bimp_obj_trans:
  bimp_obj b obj A obj' B ∧
  bimp_obj b obj' B obj'' C ⇒
  bimp_obj b obj A obj'' C
Proof
  rw[bimp_obj_def,imp_obj_def]
QED

Theorem check_csteps_correct:
  ∀csteps fml id core chk obj bound ord orders
    fml' id' core' chk' obj' bound' ord' orders'.
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  EVERY (good_ord_t ∘ SND) orders ∧
  valid_conf ord obj core fml ∧
  check_csteps csteps fml id core chk obj bound ord orders =
    SOME(fml',id',core',chk',obj',bound',ord',orders') ⇒
    hide (
    id ≤ id' ∧
    id_ok fml' id' ∧
    valid_conf ord' obj' core' fml' ∧
    opt_le bound' bound ∧
    (chk' ∧ opt_lt bound' bound ⇒
      sat_obj_le obj (THE bound') (range (coref core fml))) ∧
    bimp_obj bound'
      obj (range fml) obj' (range fml') ∧
    (chk' ⇒ bimp_obj bound'
        obj' (range (coref core' fml'))
        obj (range (coref core fml))) ∧
    (chk' ⇒ chk) ∧
    OPTION_ALL good_spo ord' ∧
    EVERY (good_ord_t o SND) orders' )
Proof
  Induct
  >- (
    rw[check_csteps_def]>>
    rw[hide_def,opt_le_def,bimp_obj_refl])>>
  rw[]>>
  fs[check_csteps_def]>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]>>
  strip_tac>>
  drule check_cstep_correct>>
  rpt (disch_then drule)>>
  disch_then(qspecl_then [`h`,`chk`,`bound`] mp_tac)>>
  simp[]>>
  strip_tac>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  strip_tac>>fs[hide_def]>>
  CONJ_TAC >-
    metis_tac[opt_le_trans]>>
  CONJ_TAC >- (
    rw[]>>
    rename1`opt_le A B`>>
    qpat_x_assum`opt_le A B` mp_tac>>simp[opt_le_def]>>
    strip_tac
    >-
      fs[bimp_obj_def]>>
    gs[]>>
    fs[bimp_obj_def,imp_obj_def]>>
    `opt_lt (SOME (THE A)) B` by
      (Cases_on`A`>>fs[opt_lt_def])>>
    fs[])>>
  rw[]>>fs[]>>
  metis_tac[bimp_obj_trans,bimp_obj_le]
QED

(* Sanity checking *)
Theorem valid_conf_setup:
  valid_conf NONE obj (map (λv. ()) fml) fml
Proof
  fs[valid_conf_def]
QED

Theorem opt_le_exists:
  ∃v.
  opt_lt (SOME v) NONE ∧
  eval_obj obj w ≤ v
Proof
  rw[eval_obj_def]>>
  every_case_tac>>fs[opt_le_def,opt_lt_def]>>
  metis_tac[integerTheory.INT_LE_REFL]
QED

Theorem bimp_obj_NONE:
  bimp_obj NONE obj1 C1 obj2 C2 ⇒
  (satisfiable C1 ⇒ satisfiable C2)
Proof
  rw[bimp_obj_def,imp_obj_def,sat_obj_le_def]>>
  fs[satisfiable_def]>>
  metis_tac[opt_le_exists]
QED

Theorem bimp_obj_SOME_bound:
  bimp_obj (SOME v) obj1 C1 obj2 C2 ∧
  unsatisfiable C2 ⇒
  ∀w. satisfies w C1 ⇒ eval_obj obj1 w ≥ v
Proof
  rw[bimp_obj_def,unsatisfiable_def,satisfiable_def]>>
  CCONTR_TAC>>
  `eval_obj obj1 w < v` by
    intLib.ARITH_TAC>>
  first_x_assum(qspec_then`eval_obj obj1 w` mp_tac)>>
  impl_tac >-
    rw[opt_lt_def]>>
  strip_tac>>
  fs[imp_obj_def,sat_obj_le_def]>>
  metis_tac[integerTheory.INT_LE_REFL]
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

Theorem optimal_val_le:
  (∀w. satisfies w f ⇒ eval_obj obj w ≥ x) ⇒
  opt_le (SOME x) (optimal_val f obj)
Proof
  rw[optimal_val_def,satisfiable_def,sat_obj_le_def,opt_le_def,opt_lt_def]>>
  drule optimal_SELECT  >>
  disch_then(qspec_then`obj` assume_tac)>>
  rename1`eval_obj obj ww = _`>>
  fs[optimal_def]>>
  res_tac>>
  fs[]>>
  intLib.ARITH_TAC
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
  intLib.ARITH_TAC
QED

Theorem range_coref_map_fml:
  range (coref (map (λv. ()) fml) fml) = range fml
Proof
  simp[range_def,lookup_inter,coref_def,lookup_map,EXTENSION,AllCaseEqs()]>>
  metis_tac[]
QED

(* In the current setup, the
  o rule can log a solution with no objective
  In that case, the formula is satisfiable *)
Theorem check_csteps_optimal:
  id_ok fml id ∧
  check_csteps csteps
    fml id (map (λv. ()) fml) chk obj NONE NONE [] =
    SOME (fml',id',core',chk',obj',bound',ord',orders') ∧
  unsatisfiable (range fml') ⇒
  case bound' of
    NONE =>
    optimal_val (range fml) obj = NONE
  | SOME v =>
    opt_le (SOME v) (optimal_val (range fml) obj) ∧
    (chk' ⇒ optimal_val (range fml) obj = SOME v)
Proof
  rw[unsatisfiable_def,satisfiable_def]>>
  drule check_csteps_correct>>
  disch_then (drule_at Any)>>
  simp[valid_conf_setup]>>
  rw[hide_def]>>
  Cases_on`bound'`>>rw[]
  >- (
    drule bimp_obj_NONE>>
    fs[optimal_val_def,satisfiable_def,valid_conf_def,sat_obj_def])
  >- (
    gs[opt_lt_def]>>
    match_mp_tac optimal_val_le>>fs[]>>
    match_mp_tac (GEN_ALL bimp_obj_SOME_bound)>>
    asm_exists_tac>>
    fs[unsatisfiable_def,valid_conf_def,satisfiable_def])
  >- (
    match_mp_tac optimal_val_eq>>fs[opt_lt_def]>>
    fs[range_coref_map_fml]>>
    match_mp_tac (GEN_ALL bimp_obj_SOME_bound)>>
    asm_exists_tac>>
    fs[unsatisfiable_def,valid_conf_def,satisfiable_def])
QED

val _ = export_theory ();
