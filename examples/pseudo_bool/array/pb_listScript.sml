(*
  Refine PB proof checker to use arrays
*)
open preamble basis pb_checkTheory;

val _ = new_theory "pb_list"

Definition list_lookup_def:
  list_lookup ls default k =
  if k < LENGTH ls then EL k ls
  else default
End

(* This version directly sets the size to double the input + 1 *)
Definition resize_update_list_def:
  resize_update_list ls default v n =
  if n < LENGTH ls
  then
    LUPDATE v n ls
  else
    LUPDATE v n (ls ++ REPLICATE (n * 2 + 1 - LENGTH ls) default)
End

Definition check_cutting_list_def:
  (check_cutting_list (fml: npbc option list) (Id n) =
    list_lookup fml NONE n) ∧
  (check_cutting_list fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting_list fml c1) (check_cutting_list fml c2)) ∧
  (check_cutting_list fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting_list fml c)) ∧
  (check_cutting_list fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_cutting_list fml c)
    else NONE) ∧
  (check_cutting_list fml (Sat c) =
    OPTION_MAP saturate (check_cutting_list fml c)) ∧
  (check_cutting_list fml (Lit l) = SOME (PBC [(1,l)] 0)) ∧
  (check_cutting_list fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting_list fml c))
End

val list_delete_list_def = Define`
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))`

(* ensure list remains ≥ sorted -- common case: will always just insert at the front *)
val sorted_insert_def = Define`
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))`

Definition rollback_def:
  rollback fml id_start id_end =
  list_delete_list
    (MAP ($+id_start) (COUNT_LIST (id_end-id_start))) fml
End

(*
  fml is represented by an array [...], where fml[i] is the i-th constraint
    when fml[i]=NONE (or i is out of range)
    that means there is no constraint at that index
  inds is a list of indexes (sorted in descending order)
*)
Definition check_pbpstep_list_def:
  (check_pbpstep_list (step:pbpstep) (fml: npbc option list) (inds:num list) (id:num) =
  case step of
    Contradiction n =>
      (case list_lookup fml NONE n of
        NONE => (Fail, fml, inds)
      | SOME c =>
        if check_contradiction c
        then (Unsat id, fml, inds)
        else (Fail, fml, inds))
  | Check n c =>
    if list_lookup fml NONE n = SOME c
    then (Cont () id, fml, inds)
    else (Fail, fml, inds)
  | NoOp => (Cont () id, fml, inds)
  | Delete ls =>
      (Cont () id,list_delete_list ls fml, inds)
  | Cutting constr =>
    (case check_cutting_list fml constr of
      NONE => (Fail, fml, inds)
    | SOME c =>
      (Cont () (id+1), (resize_update_list fml NONE (SOME c) id), sorted_insert id inds))
  | Con c pf =>
    let fml_not_c = resize_update_list fml NONE (SOME (not c)) id in
    (case check_pbpsteps_list pf fml_not_c inds (id+1) of
      (Unsat id' ,fml',inds') =>
        let rfml = rollback fml id id' in
        (* TODO: rfml may be a subset of fml because there might have been deletions *)
        (Cont () (id'+1), (resize_update_list rfml NONE (SOME c) id'), sorted_insert id' inds')
    | (_,fml',inds') => (Fail,fml',inds')) ) ∧
  (check_pbpsteps_list [] fml inds id = (Cont () id, fml, inds)) ∧
  (check_pbpsteps_list (step::steps) fml inds id =
    case check_pbpstep_list step fml inds id of
      (Cont () id', fml', inds') =>
        check_pbpsteps_list steps fml' inds' id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_size o FST)
    (list_size pbpstep_size o FST))’
  \\ fs [pbpstep_size_eq] \\ rw []
End
(* TODO:
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
  (check_redundancy [] fml id = Cont fml id) ∧
  (check_redundancy ((copt,pf)::pfs) fml id =
    case copt of
      NONE => (* no clause given *)
      (if ~EVERY is_pol_con pf then Fail else
      case check_pbpsteps_list pf fml id of
        Cont fml' id' => check_redundancy pfs fml' id'
      | res => Fail)
    | SOME c =>
      let cfml = insert id (not c) fml in
      case check_pbpsteps_list pf cfml (id+1) of
        Unsat id' => check_redundancy pfs fml id'
      | res => Fail)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_list_size o FST)
    (sum_size (list_size pbpstep_list_size o FST)
    (list_size (list_size pbpstep_list_size) o MAP SND o FST)))’
  \\ fs [fetch "-" "pbpstep_list_size_eq"] \\ rw []
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
 *)

(* prove that check_pbpstep_list implements check_pbpstep *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x. list_lookup fmlls NONE x = lookup x fml
End

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list fmlls p = check_cutting fml p
Proof
  Induct>>rw[check_cutting_list_def,check_cutting_def]>>
  fs[fml_rel_def]
QED

val _ = export_theory();
