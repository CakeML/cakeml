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

Type subst = ``:(bool + num lit) num_map``;

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
  \\ qmatch_goalsub_abbrev_tac`_ < _ + (_ + (ls2 + _))`
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
  (check_cutting fml (Lit (Pos v)) = SOME ([(1,v)],0)) ∧
  (check_cutting fml (Lit (Neg v)) = SOME ([(-1,v)],0)) ∧
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
  \\ qmatch_goalsub_abbrev_tac`ls1 < _ + (_ + (ls2 + _))`
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
  \\ cheat
  (* TODO: something broken below
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
  \\  drule extract_clauses_MEM_INR
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ fs[]
  \\ metis_tac[INSERT_SING_UNION,UNION_COMM] *)
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

val _ = export_theory ();
