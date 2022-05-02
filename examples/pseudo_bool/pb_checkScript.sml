(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble pb_constraintTheory mlstringTheory mlintTheory;

val _ = new_theory "pb_check";

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
  | Lit int num         (* Literal axiom lit ≥ 0 *)
  | Weak constr var     (* Addition of literal axioms until "var" disappears *)
End

Type subst = ``:(bool + lit) num_map``;

Datatype:
  pbpstep =
  | Contradiction num (* Id representing a contradiction *)
  | Delete (num list) (* Ids to to delete *)
  | Cutting constr    (* Adds a constraint using cutting planes, written in reverse polish notation *)
  | Con npbc (pbpstep list) (* Prove constraint by contradiction *)
  | Red npbc subst (( (num + unit) option,pbpstep list) alist) (* Redundancy step: for simplicity, the first subgoal is stored as SOME 0 *)
  | Check num npbc    (* Debugging / other steps are parsed as no ops *)
  | NoOp              (* Debugging / other steps are parsed as no ops *)
End

Definition pbpstep_ok_def[simp]:
  (pbpstep_ok (Con n pfs) ⇔
    compact n ∧ (EVERY pbpstep_ok pfs)) ∧
  (pbpstep_ok (Red n _ pfs) ⇔
    compact n ∧ EVERY (EVERY pbpstep_ok) (MAP SND pfs)) ∧
  (pbpstep_ok _ ⇔ T)
Termination
  WF_REL_TAC ‘measure pbpstep_size’ \\ rw []
  \\ gvs [fetch "-" "pbpstep_size_eq"] \\ rw []
  \\ imp_res_tac MEM_list_size
  \\ pop_assum (qspec_then`list_size pbpstep_size` mp_tac)
  \\ pop_assum (qspec_then`pbpstep_size` assume_tac)
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`_ < _ + (ls2 + _)`
  \\ qmatch_asmsub_abbrev_tac`_ < ls1`
  \\ `ls1 <= ls2` by (
    unabbrev_all_tac
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on`pfs` \\ simp[FORALL_PROD]
    \\ rw[] \\ EVAL_TAC
    \\ fs[])
  \\ fs[]
End

(*
  The type of PB formulas represented as a finite map
  num -> pbc
*)
Type pbf = ``:npbc spt``;
Type pbp = ``:pbpstep list``;

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
  (check_cutting fml (Lit l) = SOME (PBC [(1,l)] 0)) ∧
  (check_cutting fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting fml c))
End

(* A simple datatype for checking pbp
  The result is either:
  Unsat num    : unsatisfiability proved, continue with next ID
  Fail         : proof step failed (more errors can be added in imperative part)
  Cont 'a num : continue with state 'a and next ID (input formula is sat equiv to the pbv)
*)
Datatype:
  pbpres = Unsat num | Fail | Cont 'a num
End

Definition subst_fun_def:
  subst_fun (s:subst) n = lookup n s
End

Definition is_pol_con_def[simp]:
  is_pol_con (Cutting _) = T ∧
  is_pol_con (Contradiction _) = T ∧
  is_pol_con (Con _ _) = T ∧
  is_pol_con (Check _ _) = T ∧
  is_pol_con _ = F
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

Definition fold_opt_def:
  (fold_opt f i [] = SOME i) ∧
  (fold_opt f i (x::xs) =
    case f i x of NONE => NONE
    | SOME id' => fold_opt f id' xs)
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

Definition check_pbpstep_def:
  (check_pbpstep (step:pbpstep) (fml:pbf) (id:num) =
  case step of
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
  | Delete ls => Cont (FOLDL (λa b. delete b a) fml ls) id
  | Cutting constr =>
    (case check_cutting fml constr of
      NONE => Fail
    | SOME c => Cont (insert id c fml) (id+1))
  | Con c pf =>
    let fml_not_c = insert id (not c) fml in
    (case check_pbpsteps pf fml_not_c (id+1) of
      Unsat id' => Cont (insert id' c fml) (id'+1)
    | _ => Fail)
  | Red c s pfs =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      case extract_clauses w c fml pfs [] of
        NONE => Fail
      | SOME cpfs =>
      (case check_redundancy cpfs fml_not_c (id+1) of
        Cont fml' id' =>
        let goals = MAP FST (toAList (map_opt (subst_opt w) fml)) in
        let pids = MAP FST pfs in (* optimize and change later *)
          if MEM (SOME (INR ())) pids ∧
            EVERY (λid. MEM (SOME (INL id)) pids) goals then
            Cont (insert id' c fml) (id'+1)
          else Fail
      | _ => Fail) )) ∧
  (check_pbpsteps [] fml id = Cont fml id) ∧
  (check_pbpsteps (step::steps) fml id =
    case check_pbpstep step fml id of
      Cont fml' id' => check_pbpsteps steps fml' id'
    | res => res) ∧
  (check_redundancy [] fml id = Cont fml id) ∧
  (check_redundancy ((copt,pf)::pfs) fml id =
    case copt of
      NONE => (* no clause given *)
      (if ~EVERY is_pol_con pf then Fail else
      case check_pbpsteps pf fml id of
        Cont fml' id' => check_redundancy pfs fml' id'
      | res => Fail)
    | SOME c =>
      let cfml = insert id (not c) fml in
      case check_pbpsteps pf cfml (id+1) of
        Unsat id' => check_redundancy pfs fml id'
      | res => Fail)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_size o FST)
    (sum_size (list_size pbpstep_size o FST)
    (list_size (list_size pbpstep_size) o MAP SND o FST)))’
  \\ fs [fetch "-" "pbpstep_size_eq"] \\ rw []
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  \\ drule extract_clauses_MAP_SND
  \\ simp[] \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`ls1 < _ + (ls2 + _)`
  \\ `ls1 <= ls2` by (
    unabbrev_all_tac
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on`pfs` \\ simp[FORALL_PROD]
    \\ rw[] \\ EVAL_TAC
    \\ fs[])
  \\ simp[]
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
    EVAL_TAC)
  >- (
    (* weaken case *)
    metis_tac[compact_weaken])
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

Theorem satisfiable_subset:
  satisfiable t ∧ s ⊆ t ⇒
  satisfiable s
Proof
  rw[satisfiable_def,SUBSET_DEF,satisfies_def]>>
  metis_tac[]
QED

Theorem implies_explode:
  a ⊨ s ⇔ ∀c. c ∈ s ⇒ a ⊨ {c}
Proof
  fs [sat_implies_def,satisfies_def]
  \\ metis_tac []
QED

Theorem unsat_iff_implies:
  ¬satisfiable (not x INSERT fml) ⇔ fml ⊨ {x}
Proof
  fs [sat_implies_def,satisfiable_def,not_thm]
  \\ metis_tac []
QED

Definition id_ok_def:
  id_ok fml id = ∀n. id ≤ n ⇒ n ∉ domain fml
End

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

Theorem id_ok_insert_1:
  id_ok fml id ⇒
  id_ok (insert id c fml) (id+1)
Proof
  rw[id_ok_def]
QED

Theorem unsat_satisfies_insert:
  n ∉ domain fml ∧
  id ∉ domain fml ∧
  ¬satisfiable (range (insert n (not c) fml)) ⇒
  range fml ⊨  range (insert id c fml)
Proof
  fs[Once implies_explode,range_insert] \\ rw[]
  \\ gs[range_insert,unsat_iff_implies]
  \\ fs[sat_implies_def,satisfies_def]
QED

Theorem sat_implies_transitive:
  fml ⊨ fml' ∧ fml' ⊨ fml'' ⇒
  fml ⊨ fml''
Proof
  rw[sat_implies_def]
QED

Theorem sat_implies_refl:
  fml ⊨ fml
Proof
  rw[sat_implies_def]
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

Theorem check_pbpstep_correct:
  (∀step fml id.
     id_ok fml id ⇒
     case check_pbpstep step fml id of
     | Cont fml' id' =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         (satisfiable (range fml) ⇒ satisfiable (range fml')) ∧
         (is_pol_con step ⇒ range fml ⊨ range fml')
     | Unsat id' =>
        id ≤ id' ∧
         ¬ satisfiable (range fml)
     | Fail => T) ∧
  (∀steps fml id.
     id_ok fml id ⇒
     case check_pbpsteps steps fml id of
     | Cont fml' id' =>
        id ≤ id' ∧
         id_ok fml' id' ∧
         (satisfiable (range fml) ⇒ satisfiable (range fml')) ∧
         (EVERY is_pol_con steps ⇒ range fml ⊨ range fml')
     | Unsat id' =>
        id ≤ id' ∧
         ¬ satisfiable (range fml)
     | Fail => T) ∧
  (∀pfs fml id.
     id_ok fml id ⇒
     case check_redundancy pfs fml id of
     | Cont fml' id' =>
        id ≤ id' ∧
        id_ok fml' id' ∧
        (satisfiable (range fml) ⇒ satisfiable (range fml')) ∧
        EVERY (λ(copt,pf).
          case copt of
            NONE => T
          | SOME c => range fml ⊨ {c}
        ) pfs
     | _ => T)
Proof
  ho_match_mp_tac check_pbpstep_ind \\ reverse (rpt strip_tac)
  >- (
    simp[Once check_pbpstep_def]>>
    Cases_on`copt`>>fs[]
    >- (
      IF_CASES_TAC >- fs[]>>
      qmatch_goalsub_abbrev_tac`check_pbpsteps stepss _ _`>>
      Cases_on`check_pbpsteps stepss fml id` >> fs[]>>
      gs[o_DEF,ETA_AX]>>rw[]>>
      TOP_CASE_TAC>>fs[]>>
      fs[EVERY_MEM]>>
      rw[]>>first_x_assum drule>>
      pairarg_tac>>simp[]>>
      every_case_tac>>fs[]>>
      metis_tac[sat_implies_transitive])>>
    every_case_tac>>fs[]>>
    gs[id_ok_insert_1]>>
    qpat_x_assum`_ ⇒ _` mp_tac >>
    impl_tac >- fs[id_ok_def]>>
    rw[]>>
    `id ∉ domain fml` by fs[id_ok_def]>>
    fs[range_insert,id_ok_def]>>
    metis_tac[unsat_iff_implies])
  >- simp[check_pbpstep_def]
  >- (
    rw[Once check_pbpstep_def]
    \\ every_case_tac \\ gvs []
    \\ metis_tac[sat_implies_transitive])
  >- (rw[Once check_pbpstep_def] >> metis_tac[sat_implies_refl])
  \\ Cases_on ‘∃n. step = Contradiction n’
  THEN1 (
    rw[check_pbpstep_def] \\ every_case_tac \\ fs [] >>
    rw[satisfiable_def,range_def,satisfies_def]>>
    drule check_contradiction_unsat>>
    metis_tac[])
  \\ Cases_on ‘∃n c. step = Check n c’
  THEN1
   (rw[check_pbpstep_def] \\ every_case_tac \\ fs [] \\ metis_tac[sat_implies_refl])
  \\ Cases_on ‘∃n. step = Delete n’
  THEN1 (
    rw[check_pbpstep_def] \\ every_case_tac \\ rw []
    THEN1
     (pop_assum mp_tac
      \\ qid_spec_tac ‘fml’ \\ Induct_on ‘l’ \\ fs []
      \\ rw [] \\ first_x_assum irule \\ fs [id_ok_def,domain_delete]) >>
    drule satisfiable_subset>>
    disch_then match_mp_tac>>
    fs[range_FOLDL_delete])
  \\ Cases_on ‘step = NoOp’ >- simp[check_pbpstep_def]
  \\ Cases_on ‘∃c. step = Cutting c’
  THEN1 (
    rw[check_pbpstep_def] \\ every_case_tac \\ rw []
    THEN1 fs [id_ok_def] >>
    drule check_cutting_correct>>
    fs[satisfiable_def,satisfies_def]>>
    ‘id ∉ domain fml’ by fs [id_ok_def]  >>
    fs [range_insert]
    >- metis_tac []>>
    simp[sat_implies_def,satisfies_def])
  (* Proof by contradiction *)
  \\ Cases_on ‘∃c steps. step = Con c steps’
  THEN1 (
    fs[check_pbpstep_def]
    \\ every_case_tac \\ gs[id_ok_insert_1]
    \\ `id_ok fml n` by fs[id_ok_def]
    \\ simp[id_ok_insert_1]
    \\ conj_asm2_tac
    >- (
      fs[satisfiable_def,sat_implies_def]>>
      metis_tac[])
    \\ match_mp_tac (GEN_ALL unsat_satisfies_insert)
    \\ first_x_assum (irule_at Any)
    \\ fs[id_ok_def])
  (* Red steps *)
  \\ ‘∃c s pfs. step = Red c s pfs’ by (Cases_on ‘step’ \\ fs [])
  \\ gvs []
  \\ simp[check_pbpstep_def]
  \\ every_case_tac
  \\ gs[id_ok_insert_1]
  \\ CONJ_TAC >- gvs[id_ok_def]>>
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
  \\ strip_tac
  \\  drule extract_clauses_MEM_INL
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ fs[]
  \\ metis_tac[INSERT_SING_UNION,UNION_COMM]
QED

Theorem check_pbpstep_compact:
  (∀step fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ pbpstep_ok step ∧
     check_pbpstep step fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀steps fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ EVERY pbpstep_ok steps ∧
     check_pbpsteps steps fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀pfs fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧
     EVERY (EVERY pbpstep_ok) (MAP SND pfs) ∧
     check_redundancy pfs fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c))
Proof
  ho_match_mp_tac check_pbpstep_ind \\ reverse (rw [])
  >- (
    gs[Once check_pbpstep_def,AllCaseEqs()]>>
    gs[o_DEF,ETA_AX])
  >- fs[Once check_pbpstep_def]
  THEN1
   (ntac 2 (pop_assum mp_tac)
    \\ simp [Once check_pbpstep_def,AllCaseEqs()]
    \\ rw [] \\ fs [])
  THEN1 (fs [Once check_pbpstep_def,AllCaseEqs()]) >>
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>rw[]
  >- metis_tac[range_FOLDL_delete,SUBSET_DEF]
  >- (drule range_insert_2>>rw[]>>
      metis_tac[check_cutting_compact])
  \\ imp_res_tac range_insert_2 \\ gvs []
QED

(*
  Parse an OPB file as an unnormalized formula
  For now, use the standard format where variables are named x1,...,xn
*)

(* TODO: copied from lpr_parsing *)
(* Everything recognized as a "blank" *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_def:
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

(* OPB parser
  Parses a literal xi, ~xi
  Note: for now, only handle default "xi" var names
*)

Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" /\ strsub s 1 = #"x" then
    OPTION_MAP Neg (mlint$fromNatString (substring s 2 (strlen s - 2)))
  else if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    OPTION_MAP Pos (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

(*
  EVAL ``parse_lit (strlit "x1")``
  EVAL ``parse_lit (strlit "~x1234")``
*)

(* Parse the LHS of a constraint and returns the remainder of the line *)
Definition parse_constraint_LHS_def:
  (parse_constraint_LHS (INR n::INL v::rest) acc =
    case parse_lit v of NONE => (INR n::INL v::rest,REVERSE acc)
    | SOME lit => parse_constraint_LHS rest ((n,lit)::acc)) ∧
  (parse_constraint_LHS ls acc = (ls,REVERSE acc))
End

(* strip ; from the end of a number *)
Definition strip_terminator_def:
  strip_terminator s =
  if strlen s ≥ 1 ∧ strsub s (strlen s - 1) = #";"
  then mlint$fromString (substring s 0 (strlen s - 1))
  else NONE
End

Definition parse_constraint_def:
  parse_constraint line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  let cmpdeg =
    (case rest of
      [INL cmp; INR deg; INL term] =>
        if term ≠ str #";" then NONE else SOME(cmp,deg)
    | [INL cmp; INL degterm] =>
      (case strip_terminator degterm of NONE => NONE
      | SOME deg => SOME(cmp,deg))
    | _ => NONE) in
  case cmpdeg of NONE => NONE
  | SOME (cmp, deg) =>
    if cmp = implode ">=" then
      SOME (GreaterEqual lhs deg)
    else if cmp = implode "=" then
      SOME (Equal lhs deg)
    else NONE
End

(* EVAL ``parse_constraint (toks (strlit "2 ~x1 1 ~x3 >= 1;"))``; *)

Definition parse_constraints_def:
  (parse_constraints [] acc = SOME (REVERSE acc)) ∧
  (parse_constraints (s::ss) acc =
    case parse_constraint s of
      NONE => NONE
    | SOME pbc => parse_constraints ss (pbc::acc))
End

Definition nocomment_line_def:
  (nocomment_line (INL c::cs) =
    (strlen c < 1 ∨ strsub c 0 ≠ #"*")) ∧
  (nocomment_line _ = T)
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  (* TODO: parse the header line ? *)
  parse_constraints nocomments []
End

(* Parse a list of strings in pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(*
  Parsing a proof file
*)

(* The stack is formed from constraints, where factors and variables are
  also encoded using Id *)
Definition parse_cutting_def:
  (parse_cutting (x::xs) stack =
  case x of INR n =>
    if n ≥ 0 then
      parse_cutting xs (Id (Num n) :: stack)
    else NONE
  | INL s =>
  if s = str #"+" then
    (case stack of
      a::b::rest => parse_cutting xs (Add b a::rest)
    | _ => NONE)
  else if s = str #"*" then
    (case stack of
      Id a::b::rest => parse_cutting xs (Mul b a::rest)
    | _ => NONE)
  else if s = str #"d" then
    (case stack of
      Id a::b::rest => parse_cutting xs (Div b a::rest)
    | _ => NONE)
  else if s = str #"s" then
    (case stack of
      a::rest => parse_cutting xs (Sat a::rest)
    | _ => NONE)
  else if s = str #"w" then
    (case stack of
      Lit (Pos v)::a::rest => parse_cutting xs (Weak a v::rest)
    | _ => NONE)
  else
    case parse_lit s of SOME l => parse_cutting xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_cutting [] [c] = SOME c) ∧
  (parse_cutting [] _ = NONE)
End

Definition strip_numbers_def:
  (strip_numbers [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_numbers xs (Num n::acc)
    else NONE
  | INL _ => NONE)
End

Definition parse_var_def:
  parse_var v =
  case parse_lit v of SOME (Pos n) => SOME n | _ => NONE
End

(* Parse a substitution {var -> lit} *)
Definition parse_subst_def:
  (parse_subst (INL v :: INL arr :: r ::rest) acc =
  if arr = strlit "->" then
    case parse_var v of
      NONE => ([],LN)
    | SOME v =>
    (case r of
        INR r =>
          if r = 0:int then parse_subst rest (insert v (INL F) acc)
          else if r = 1 then parse_subst rest (insert v (INL T) acc)
          else ([],LN)
      | INL r =>
          (case parse_lit r of NONE => ([],LN)
          | SOME l => parse_subst rest (insert v (INR l) acc)))
  else ([],LN)) ∧
  (parse_subst ls acc = (ls, acc))
End

Definition parse_constraint_npbc_def:
  parse_constraint_npbc line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  (case rest of (INL cmp :: INR deg :: INL term :: rest) =>
    if term = str #";" ∧ cmp = strlit">=" then
      SOME (pbc_to_npbc (GreaterEqual lhs deg),rest)
    else
      NONE
  | _ => NONE)
End

Definition parse_red_header_def:
  parse_red_header line =
  case parse_constraint_npbc line of
    SOME (constr,rest) =>
      (case parse_subst rest LN of (rest,ss) =>
       (case rest of
        [INL term; INL beg] =>
          if term = strlit";" ∧ beg = strlit"begin" then
            SOME (constr,ss)
          else NONE
      | _ => NONE))
  | _ => NONE
End

Definition parse_subgoal_num_def:
  parse_subgoal_num line =
  case line of
    [INR n] => if n>=0 then SOME (INL (Num n)) else NONE
  | [INL s] =>
     if s = strlit "#1"
     then SOME (INR ())
     else NONE
  | _ => NONE
End

(* Parse a single line *)
Definition parse_pbpstep_def:
  (parse_pbpstep s =
    case s of [] => NONE
    | (r::rs) =>
      if r = INL (strlit "c") then
        (case rs of
          [INR id] =>
          if id ≥ 0 then SOME (INL (Contradiction (Num id)))
          else NONE
        | _ => NONE)
      else if r = INL (strlit "d") then
        (case strip_numbers rs [] of NONE => NONE
        | SOME n => SOME (INL (Delete n)))
      else if r = INL (strlit "pol") then
        (case parse_cutting rs [] of NONE => NONE
        | SOME p => SOME (INL (Cutting p)))
      else if r = INL (strlit "e") then
        (case rs of
          INR id::rest =>
          if id ≥ 0 then
            (case parse_constraint_npbc rest of
              SOME (c,[]) => SOME (INL (Check (Num id) c))
            | _ => NONE)
          else NONE
        | _ => NONE)
      else if r = INL (strlit "f") then SOME (INL NoOp)
      else if r = INL (strlit "red") then
        case parse_red_header rs of NONE => NONE
        | SOME (c,s) =>
          SOME (INR (c,s))
      else NONE)
End

Definition parse_pbpsteps_aux_def:
  parse_pbpsteps_aux c s pf =
    if s = LN then
       case pf of [] => SOME (Con c [])
       | [(NONE,p)] => SOME (Con c p)
       | _ => NONE
    else SOME (Red c s pf)
End

Definition parse_redundancy_header_def:
  (parse_redundancy_header [] = NONE) ∧
  (parse_redundancy_header (r::rs) =
    if r = INL (strlit"end") then SOME (INL ())
    else
    if r = INL (strlit"proofgoal") then
       case parse_subgoal_num rs of NONE => NONE
       | SOME ind => SOME (INR ind)
    else NONE)
End

Definition mk_acc_def:
  mk_acc pf (acc:(( (num + unit) option,pbpstep list) alist)) = if pf = [] then acc else (NONE,pf)::acc
End

Definition check_head_def:
  check_head (h:(mlstring + int) list ) = (h = [INL (strlit"end")])
End

Definition parse_pbpsteps_def:
  (parse_pbpsteps ([]:(mlstring + int) list list) acc = NONE) ∧
  (parse_pbpsteps (s::ss) acc =
    case parse_pbpstep s of NONE => SOME (REVERSE acc, s, ss)
    | SOME (INL step) => parse_pbpsteps ss (step::acc)
    | SOME (INR (c,s)) =>
      case parse_redundancy ss [] of
        NONE => NONE
      | SOME (pf,rest) =>
        if LENGTH rest < LENGTH ss then
          case parse_pbpsteps_aux c s pf of
            NONE => NONE
          | SOME step => parse_pbpsteps rest (step :: acc)
        else NONE) ∧
  (parse_redundancy ss (acc:(( (num + unit) option,pbpstep list) alist)) =
    case parse_pbpsteps ss [] of
      NONE => NONE
    | SOME (pf,s,rest) =>
      if LENGTH rest < LENGTH ss then
        let acc' = mk_acc pf acc in
        (case parse_redundancy_header s of
          NONE => NONE
        | SOME (INL u) => SOME (REVERSE acc', rest)
        | SOME (INR ind) =>
            case parse_pbpsteps rest [] of
              NONE => NONE
            | SOME (pf,h,rest2) =>
              if LENGTH rest2 < LENGTH ss then
                (if check_head h then
                    parse_redundancy rest2 ((SOME ind,pf)::acc')
                  else NONE)
              else NONE )
      else NONE )
Termination
  WF_REL_TAC `measure (sum_size (λx. 2 * (LENGTH o FST) x) (λx. 1 + 2 * (LENGTH o FST) x) )’
  \\ rw[] \\ fs[]
End

Theorem parse_pbpsteps_LENGTH:
  (∀ss acc pf s rest.
  parse_pbpsteps ss acc = SOME (pf,s,rest) ⇒ LENGTH rest < LENGTH ss) ∧
  (∀ss acc pf rest.
  parse_redundancy ss acc = SOME (pf,rest) ⇒
    LENGTH rest < LENGTH ss)
Proof
  ho_match_mp_tac parse_pbpsteps_ind>>
  rw[]
  >- fs[parse_pbpsteps_def]
  >- (
    pop_assum mp_tac>>
    simp[Once parse_pbpsteps_def]>>
    every_case_tac>>fs[]>>fs[]>>rw[]>>
    fs[ADD1] )
  >- (
    pop_assum mp_tac>>
    simp[Once parse_pbpsteps_def]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-(rw[]>>fs[])>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    rw[]>>fs[]>>rfs[])
QED

Theorem parse_pbpsteps_thm:
  (∀acc. parse_pbpsteps ([]:(mlstring + int) list list) acc = NONE) ∧
  (∀s ss acc.
    parse_pbpsteps (s::ss) acc =
    case parse_pbpstep s of NONE => SOME (REVERSE acc, s, ss)
    | SOME (INL step) => parse_pbpsteps ss (step::acc)
    | SOME (INR (c,s)) =>
      case parse_redundancy ss [] of
        NONE => NONE
      | SOME (pf,rest) =>
        case parse_pbpsteps_aux c s pf of
          NONE => NONE
        | SOME step => parse_pbpsteps rest (step :: acc)) ∧
  (∀ss acc.
    parse_redundancy ss (acc:(( (num + unit) option,pbpstep list) alist)) =
    case parse_pbpsteps ss [] of
      NONE => NONE
    | SOME (pf,s,rest) =>
      let acc' = mk_acc pf acc in
      (case parse_redundancy_header s of
        NONE => NONE
      | SOME (INL u) => SOME (REVERSE acc', rest)
      | SOME (INR ind) =>
          case parse_pbpsteps rest [] of
            NONE => NONE
          | SOME (pf,h,rest2) =>
              (if check_head h then
                  parse_redundancy rest2 ((SOME ind,pf)::acc')
                else NONE)))
Proof
  rw[]
  >-
    simp[Once parse_pbpsteps_def]
  >- (
    simp[Once parse_pbpsteps_def]>>
    every_case_tac>>fs[]>>
    imp_res_tac parse_pbpsteps_LENGTH)
  >- (
    simp[Once parse_pbpsteps_def]>>
    every_case_tac>>fs[]>>
    imp_res_tac parse_pbpsteps_LENGTH>>
    fs[])
QED

(* Parse 1 top level step *)
Definition parse_top_def:
  (parse_top [] = SOME NONE) ∧
  (parse_top (s::ss) =
    case parse_pbpstep s of NONE => NONE
    | SOME (INL step) => SOME (SOME (step,ss))
    | SOME (INR (c,s)) =>
      case parse_redundancy ss [] of
        NONE => NONE
      | SOME (pf,rest) =>
        case parse_pbpsteps_aux c s pf of
          NONE => NONE
        | SOME step => SOME (SOME (step,rest)))
End

Definition parse_tops_def:
  (parse_tops ss =
    case parse_top ss of NONE => NONE
    | SOME NONE => SOME []
    | SOME (SOME (step,rest)) =>
      case parse_tops rest of NONE => NONE
      | SOME sts => SOME (step::sts))
Termination
  WF_REL_TAC `measure (LENGTH)`>>
  Cases>>rw[parse_top_def]>>
  every_case_tac>>fs[]>>
  fs[]>>rw[]>>rveq>>
  imp_res_tac parse_pbpsteps_LENGTH>>
  fs[]
End

val headertrm = rconc (EVAL``toks (strlit"pseudo-Boolean proof version 1.2")``);

Definition parse_header_line_def:
  parse_header_line s = (s = ^headertrm)
End

val fromString_unsafe_def = Define`
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"~" ∨
            strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str`;

val tokenize_fast_def = Define`
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else
  let c = ORD (strsub s 0) in
  if 48 ≤ c ∧ c ≤ 57
  then INR (fromString_unsafe s)
  else INL s`

(* Parse the tokenized pbf file *)
Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
    if parse_header_line s then
      parse_tops ss
    else NONE
  | [] => NONE
End

(* Parse a list of strings in pbf format *)
Definition parse_pbp_def:
  parse_pbp strs = parse_pbp_toks (MAP toks strs)
End

(* build an sptree for the PBF from an initial ID *)
Definition build_fml_def:
  (build_fml (id:num) [] acc = (acc,id)) ∧
  (build_fml id (s::ss) acc =
    build_fml (id+1) ss (insert id s acc))
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 1.2")``);

Definition parse_header_line_fast_def:
  parse_header_line_fast s = (s = ^headertrm)
End

(*
val pbpraw = ``[
strlit"  e 679 1 x121 1 ~x127 1 ~x134 1 x144 1 ~x153 1 ~x154 1 x159 1 x165 >= 1 ;"
]``;

EVAL``(MAP toks_fast ^(pbpraw))``

*)

val _ = export_theory ();
