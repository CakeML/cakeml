(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble npbcTheory mlstringTheory mlintTheory mlvectorTheory spt_to_vecTheory mergesortTheory;

val _ = new_theory "npbc_check";

val _ = numLib.temp_prefer_num();

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
         Includes objective updates, core transfer, checked deletion, dominance
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
  | Lit (num lit)       (* Literal axiom lit ≥ 0 (superseded by triv but used in parsing) *)
  | Weak constr (var list)     (* Addition of literal axioms until "var" disappears *)
  | Triv ((num # num lit) app_list) (* Literal axiom corresponds to [1,l] ≥ 0 *)
End

(* Steps that preserve logical implication *)
Datatype:
  lstep =
  | Delete (num list) (* Ids to delete *)
  | Cutting constr    (* Adds a constraint using cutting planes, written in reverse polish notation *)
  | Rup npbc (num list) (* Add a constraint by RUP *)
  | Con npbc (lstep list) num
    (* Prove constraint by contradiction, indicated by the id *)
  | Check num npbc
    (* Debugging / other steps are parsed as no ops *)
  | NoOp              (* Other steps are parsed as no ops *)
End

Definition lstep_ok_def[simp]:
  (lstep_ok (Con c pfs n) ⇔
    compact c ∧ (EVERY lstep_ok pfs)) ∧
  (lstep_ok (Rup c ls) ⇔ compact c) ∧
  (lstep_ok _ ⇔ T)
Termination
  WF_REL_TAC ‘measure lstep_size’ \\ rw []
End

(*
  The type of PB formulas represented as a finite map
  num -> pbc
*)
Type pbf = ``:(npbc # bool) spt``;

(* b = T forces all operations to respect/use the core directly *)
Definition lookup_core_only_def:
  lookup_core_only b fml n =
  case lookup n fml of
    NONE => NONE
  | SOME (x,b') =>
    if ¬b ∨ b' then SOME x
    else NONE
End

Definition map_app_list_def:
  (map_app_list f (List ls) = List (MAP f ls)) ∧
  (map_app_list f (Append l r) = Append (map_app_list f l) (map_app_list f r)) ∧
  (map_app_list f Nil = Nil)
End

Definition mul_triv_def:
  mul_triv ls k = map_app_list (λ(x:num,y). (x * k,y) ) ls
End

Definition fuse_weaken_def:
  (fuse_weaken vs (Weak c rs) = Weak c (vs ++ rs)) ∧
  (fuse_weaken vs p = Weak p vs)
End

Definition to_triv_def:
  (to_triv (Add l r) =
    let ll = to_triv l in
    let rr = to_triv r in
    case (ll,rr) of
      (Triv lt, Triv rt) => Triv (SmartAppend lt rt)
    | (Triv lt, Add re (Triv rt)) => Add re (Triv (SmartAppend lt rt))
    | (Add le (Triv lt), Triv rt) => Add le (Triv (SmartAppend lt rt))
    | (Add le (Triv lt), Add re (Triv rt)) => Add (Add le re) (Triv (SmartAppend lt rt))
    | _ => Add ll rr) ∧
  (to_triv (Mul c k) =
    let cc = to_triv c in
    case cc of
      Triv ls => Triv (mul_triv ls k)
    | _ => Mul cc k) ∧
  (to_triv (Div c k) = Div (to_triv c) k) ∧
  (to_triv (Sat c) = Sat (to_triv c)) ∧
  (to_triv (Weak c vs) = fuse_weaken vs (to_triv c)) ∧
  (to_triv (Lit l) = Triv (List [(1,l)])) ∧
  (to_triv c = c)
End

Definition sing_lit_def:
  sing_lit (k:num,l) =
  case l of Pos v => (&k:int,v)
  | Neg v => (-&k:int,v)
End

Definition clean_triv_def:
  clean_triv ls =
    FOLDR (λpc1 c2.
      npbc$add ([pc1],0) c2) ([],0)
      (FILTER (λh. FST h ≠ 0)
      (mergesort_tail (λx y. SND x ≤ SND y)
        (MAP sing_lit (append ls))))
End

Definition weaken_sorted_def:
  weaken_sorted c vs =
  weaken c (mergesort_tail (λx y. x ≤ y) vs)
End

Definition check_cutting_def:
  (check_cutting b (fml:pbf) (Id n) =
    lookup_core_only b fml n) ∧
  (check_cutting b fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting b fml c1) (check_cutting b fml c2)) ∧
  (check_cutting b fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting b fml c)) ∧
  (check_cutting b fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_cutting b fml c)
    else NONE) ∧
  (check_cutting b fml (Sat c) =
    OPTION_MAP saturate (check_cutting b fml c)) ∧
  (check_cutting b fml (Lit (Pos v)) = SOME ([(1,v)],0)) ∧
  (check_cutting b fml (Lit (Neg v)) = SOME ([(-1,v)],0)) ∧
  (check_cutting b fml (Triv ls) = SOME (clean_triv ls)) ∧
  (check_cutting b fml (Weak c var) =
    OPTION_MAP (λc. weaken_sorted c var) (check_cutting b fml c))
End

Definition check_contradiction_fml_def:
  check_contradiction_fml b (fml:pbf) n =
  case lookup_core_only b fml n of
    NONE => F
  | SOME c =>
    check_contradiction c
End

(* Insertion into derived set, unless we're in core only mode *)
Definition insert_fml_def:
  insert_fml b fml id c =
    (insert id (c,b) fml,
    id+1)
End

Definition rup_pass1_def:
  rup_pass1 assg [] acc ys = (acc,ys) ∧
  rup_pass1 assg ((i:int,n:num)::xs) acc ys =
    let k = Num (ABS i) in
      case FLOOKUP assg n of
      | NONE   => rup_pass1 assg xs (acc + k) ((k,i,n)::ys)
      | SOME T => rup_pass1 assg xs (if i < 0 then acc else acc + k) ys
      | SOME F => rup_pass1 assg xs (if i < 0 then acc + k else acc) ys
End

Definition rup_pass2_def:
  rup_pass2 assg max [] l = SOME assg ∧
  rup_pass2 assg max ((k:num,i:int,n:num)::ys) l =
    if max < l + k then
      rup_pass2 (assg |+ (n,0 ≤ i)) max ys l
    else
      rup_pass2 assg max ys l
End

(* Reduce c according to the assignment,
  return NONE if it gives a contradiction
  otherwise return the updated assignment using units in (ls,n) *)
Definition update_assg_def:
  update_assg assg (ls,n) do_check =
    let (max,ls1) = rup_pass1 assg ls 0 [] in
      if max < n ∧ do_check then NONE else
        rup_pass2 assg max ls1 n
End

(* Here, assg could be a finite map of variables to T/F
  assg' should be assg updated with all units under assg
  id = 0 is special for nc
*)
Definition get_rup_constraint_def:
  get_rup_constraint b fml n nc =
  if n = 0 then SOME nc
  else
    lookup_core_only b fml n
End

Definition check_rup_def:
  (check_rup b nc fml (assg: num |-> bool) [] = F) ∧
  (check_rup b nc fml assg (n::ns) =
  case get_rup_constraint b fml n nc of
    NONE => F
  | SOME c =>
    case update_assg assg c (NULL ns) of
    | NONE       => T
    | SOME assg' => check_rup b nc fml assg' ns)
End

Definition check_lstep_def:
  (check_lstep lstep b (fml:pbf) (id:num) =
  case lstep of
  | Delete ls =>
    if EVERY (λid. lookup_core_only T fml id = NONE) ls
    then SOME (FOLDL (λa b. delete b a) fml ls,id)
    else NONE
  | Cutting constr =>
    (case check_cutting b fml (to_triv constr) of
      NONE => NONE
    | SOME c =>
      SOME (insert_fml b fml id c))
  | Rup c ls =>
    if check_rup b (not c) fml FEMPTY ls then
      SOME (insert_fml b fml id c)
    else NONE
  | Con c pf n =>
    let (fml_not_c,id1) = insert_fml b fml id (not c) in
    (case check_lsteps pf b fml_not_c id1 of
      SOME (fml',id') =>
      if check_contradiction_fml b fml' n
      then SOME (insert_fml b fml id' c)
      else NONE
    | _ => NONE)
  | Check n c =>
    (case lookup n fml of NONE => NONE
    | SOME (c',b) =>
      if c = c' then SOME(fml,id)
      else NONE)
  | NoOp => SOME(fml,id)) ∧
  (check_lsteps [] b fml id = SOME (fml,id)) ∧
  (check_lsteps (step::steps) b fml id =
    case check_lstep step b fml id of
      SOME(fml',id') =>
        check_lsteps steps b fml' id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST) )’
End

Theorem satisfies_SUBSET:
  Y ⊆ X ⇒
  (satisfies w X ⇒ satisfies w Y)
Proof
  rw[satisfies_def]>>
  metis_tac[SUBSET_DEF]
QED

Definition core_only_fml_def:
  core_only_fml b fml =
  if b then
    {v | ∃n. lookup n fml = SOME(v,b)}
  else
    {v | ∃n b. lookup n fml = SOME(v,b)}
End

Theorem FOLDR_add_sound:
  ∀ls c.
  satisfies_npbc w c ⇒
  satisfies_npbc w (FOLDR (λpc1 c2. add ([pc1],0) c2) c ls)
Proof
  Induct>>
  rw[]>>
  match_mp_tac add_thm>>
  simp[satisfies_npbc_def]
QED

Theorem clean_triv_thm:
  satisfies_npbc w (clean_triv ls)
Proof
  rw[clean_triv_def]>>
  irule FOLDR_add_sound>>
  simp[satisfies_npbc_def]
QED

Theorem check_cutting_correct:
  ∀fml n c w.
  check_cutting b fml n = SOME c ∧
  satisfies w (core_only_fml b fml) ⇒
  satisfies_npbc w c
Proof
  Induct_on`n`>>rw[check_cutting_def]
  >- (
    (*Id case*)
    fs[lookup_core_only_def,core_only_fml_def]>>
    every_case_tac>>
    fs[satisfies_def,satisfies_npbc_def,range_def,PULL_EXISTS]>>
    metis_tac[])
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
    simp[weaken_sorted_def]>>
    match_mp_tac weaken_thm>>
    metis_tac[])
  >-
    metis_tac[clean_triv_thm]
QED

Theorem FOLDR_add_compact:
  ∀ls c.
  compact c ∧ EVERY (λh. FST h ≠ 0) ls ⇒
  compact (FOLDR (λpc1 c2. add ([pc1],0) c2) c ls)
Proof
  Induct>>
  rw[]>>
  match_mp_tac compact_add>>
  simp[]
QED

Theorem clean_triv_compact:
  compact (clean_triv ls)
Proof
  rw[clean_triv_def]>>
  irule FOLDR_add_compact>>
  simp[EVERY_FILTER]
QED

Theorem check_cutting_compact:
  ∀n c.
  (∀c. c ∈ core_only_fml b fml ⇒ compact c) ∧
  check_cutting b fml n = SOME c ⇒
  compact c
Proof
  Induct_on`n`>>rw[check_cutting_def]
  >- (
    (*Id case*)
    fs[core_only_fml_def,lookup_core_only_def]>>
    every_case_tac>>gvs[]>>
    metis_tac[])
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
    simp[weaken_sorted_def]>>
    metis_tac[compact_weaken])
  >-
    metis_tac[clean_triv_compact]
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

Theorem lookup_FOLDL_delete:
  ∀ls v.
  lookup n (FOLDL (λa b. delete b a) v ls) =
  if MEM n ls then NONE else lookup n v
Proof
  Induct>>rw[]>>
  first_x_assum (qspec_then`delete h v` mp_tac)>>rw[]>>
  fs[lookup_delete]
QED

Theorem check_contradiction_fml_unsat:
  check_contradiction_fml b fml n ⇒
  unsatisfiable (core_only_fml b fml)
Proof
  rw[check_contradiction_fml_def,core_only_fml_def,lookup_core_only_def]>>
  every_case_tac>>fs[]>>
  drule check_contradiction_unsat>>
  rw[unsatisfiable_def,satisfiable_def,range_def,satisfies_def]>>
  metis_tac[]
QED

Theorem core_only_fml_insert:
  id ∉ domain fml ⇒
  core_only_fml b (insert id (c,b) fml) =
  c INSERT core_only_fml b fml
Proof
  rw[core_only_fml_def,EXTENSION,lookup_insert]>>
  eq_tac>>rw[]>>
  every_case_tac>>fs[domain_lookup]>>
  metis_tac[]
QED

Definition agree_assg_def:
  agree_assg assg w ⇔
  ∀x b.
    FLOOKUP assg x = SOME b ⇒
    w x = b
End

Theorem rup_pass1_thm:
  ∀assg xs acc ys acc1 ys1 w.
    rup_pass1 assg xs acc ys = (acc1,ys1) ∧ agree_assg assg w ⇒
    SUM (MAP (eval_term w) xs) + acc ≤ acc1 ∧
    (∀n i k. MEM (n,i,k) ys1 ⇒ MEM (n,i,k) ys ∨ n = Num (ABS i)) ∧
    ∃xs1.
      SUM (MAP (eval_term w) xs1) + lslack (MAP SND ys1) + acc ≤ acc1 + lslack (MAP SND ys) ∧
      SUM (MAP (eval_term w) xs) + SUM (MAP (eval_term w) (MAP SND ys)) =
      SUM (MAP (eval_term w) xs1) + SUM (MAP (eval_term w) (MAP SND ys1))
Proof
  Induct_on ‘xs’ \\ fs [rup_pass1_def]
  >- (rw [] \\ qexists_tac ‘[]’ \\ gvs [])
  \\ PairCases \\ fs [rup_pass1_def]
  \\ rpt gen_tac \\ gvs [AllCaseEqs()] \\ strip_tac \\ gvs []
  >- (last_x_assum dxrule_all \\ fs [lslack_def] \\ strip_tac \\ gvs []
      \\ conj_tac >- (Cases_on ‘w h1’ \\ gvs [] \\ metis_tac [])
      \\ conj_tac >- metis_tac []
      \\ qexists_tac ‘xs1’ \\ gvs [])
  \\ last_x_assum drule_all \\ strip_tac \\ fs []
  \\ gvs [agree_assg_def] \\ res_tac \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  >- (qexists_tac ‘xs1’ \\ gvs [])
  >- (qexists_tac ‘(h0,h1)::xs1’ \\ gvs [])
  >- (qexists_tac ‘(h0,h1)::xs1’ \\ gvs [])
  >- (qexists_tac ‘xs1’ \\ gvs [])
QED

Theorem rup_pass2_thm:
  ∀assg d1 slack ls1 d hc.
    agree_assg assg w ∧
    c1 ≤ d + SUM (MAP (eval_term w) (MAP SND ls1)) ∧
    d + lslack (MAP SND ls1) ≤ max ∧
    (∀n i k. MEM (n,i,k) ls1 ⇒ n = Num (ABS i)) ∧
    rup_pass2 assg max ls1 c1 = SOME assg1
    ⇒
    agree_assg assg1 w
Proof
  Induct_on ‘ls1’ \\ fs [rup_pass2_def] \\ PairCases
  \\ gvs [rup_pass2_def] \\ rpt gen_tac \\ strip_tac
  \\ qabbrev_tac ‘x = if h1 < 0 then 1 − b2n (w h2) else b2n (w h2)’
  \\ ‘x ≤ 1’ by (rw [Abbr‘x’] \\ Cases_on ‘w h2’ \\ gvs [])
  \\ reverse (Cases_on ‘max < c1 + h0’) \\ gvs []
  \\ last_x_assum irule \\ fs []
  \\ gvs [SF DNF_ss,SF SFY_ss]
  \\ fs [lslack_def] \\ fs [GSYM lslack_def]
  \\ qexists_tac ‘d + Num (ABS h1)’ \\ gvs []
  \\ ‘c1 ≤ d + (Num (ABS h1) + SUM (MAP (eval_term w) (MAP SND ls1)))’ by
    (Cases_on ‘x’ \\ gvs [ADD1] \\ Cases_on ‘n’ \\ gvs []) \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd \\ fs []
  \\ gvs [agree_assg_def,FLOOKUP_SIMP] \\ rw [] \\ gvs []
  \\ rpt $ qpat_x_assum ‘∀x._’ kall_tac
  \\ dxrule_all LESS_EQ_LESS_TRANS \\ strip_tac
  \\ ‘d + lslack (MAP SND ls1) < c1’ by gvs []
  \\ Cases_on ‘x = 1’ >- (Cases_on ‘w h2’ \\ gvs [AllCaseEqs()] \\ intLib.COOPER_TAC)
  \\ ‘x = 0’ by gvs [] \\ gvs []
  \\ ‘SUM (MAP (eval_term w) (MAP SND ls1)) ≤ lslack (MAP SND ls1)’ by fs [lslack_thm]
  \\ gvs []
QED

Theorem update_assg_NONE:
  update_assg assg c flag = NONE ⇒
  ∀w. agree_assg assg w ⇒
    ¬ satisfies_npbc w c
Proof
  PairCases_on ‘c’
  \\ rw[update_assg_def]
  \\ pairarg_tac \\ gvs []
  \\ drule_all rup_pass1_thm \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ gvs [satisfies_npbc_def,GREATER_EQ,GSYM NOT_LESS]
  \\ CCONTR_TAC \\ gvs [lslack_def]
  \\ qsuff_tac
     ‘∀assg m ls1 c1. rup_pass2 assg m ls1 c1 ≠ NONE’
  >- (strip_tac \\ gvs [])
  \\ rpt $ pop_assum kall_tac
  \\ Induct_on ‘ls1’ \\ gvs [rup_pass2_def]
  \\ gvs [FORALL_PROD]
  \\ gvs [rup_pass2_def] \\ rw []
QED

Theorem update_assg_SOME:
  update_assg assg c flag = SOME assg' ⇒
  ∀w. agree_assg assg w ∧ satisfies_npbc w c ⇒
      agree_assg assg' w
Proof
  PairCases_on ‘c’
  \\ rw[update_assg_def]
  \\ pairarg_tac \\ gvs []
  \\ drule_all rup_pass1_thm \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ gvs [satisfies_npbc_def,GREATER_EQ,EVAL “lslack []”]
  \\ irule rup_pass2_thm
  \\ last_x_assum $ irule_at Any
  \\ gvs [SF SFY_ss]
QED

Theorem check_rup_unsat:
  ∀ns assg.
  check_rup b nc fml assg ns ∧
  agree_assg assg w ⇒
  ¬(satisfies_npbc w nc ∧
   satisfies w (core_only_fml b fml))
Proof
  Induct>>rw[check_rup_def]>>
  gvs[get_rup_constraint_def,AllCasePreds(),AllCaseEqs()]
  >- (
    drule update_assg_NONE>>
    disch_then drule>>
    fs[lookup_core_only_def,core_only_fml_def]>>
    every_case_tac>>fs[satisfies_def,PULL_EXISTS]>>
    metis_tac[])
  >- (
    drule update_assg_SOME>>
    disch_then drule>>
    Cases_on`satisfies_npbc w x`>>rw[]
    >-
      metis_tac[]>>
    fs[lookup_core_only_def,core_only_fml_def]>>
    every_case_tac>>fs[satisfies_def,PULL_EXISTS]>>
    metis_tac[])
  >- (
    drule update_assg_NONE>>
    disch_then drule>>
    fs[lookup_core_only_def,core_only_fml_def]>>
    every_case_tac>>fs[satisfies_def,PULL_EXISTS]>>
    metis_tac[])
  >- (
    drule update_assg_SOME>>
    disch_then drule>>
    Cases_on`satisfies_npbc w c`>>rw[]
    >-
      metis_tac[]>>
    fs[lookup_core_only_def,core_only_fml_def]>>
    every_case_tac>>fs[satisfies_def,PULL_EXISTS]>>
    metis_tac[])
QED

(* if b = F, then the core should be untouched,
  otherwise the core can grow *)
Theorem check_lstep_correct:
  (∀step b fml id.
     id_ok fml id ⇒
     case check_lstep step b fml id of
       SOME (fml',id') =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         (∀n x.
          (lookup n fml = SOME (x,T) ⇒
            lookup n fml' = SOME (x,T))) ∧
         (¬b ⇒
         (∀n x.
          (lookup n fml' = SOME (x,T) ⇒
            lookup n fml = SOME (x,T)))) ∧
         (core_only_fml b fml) ⊨ (core_only_fml b fml')
     | NONE => T) ∧
  (∀steps b fml id.
     id_ok fml id ⇒
     case check_lsteps steps b fml id of
     | SOME (fml',id') =>
         id ≤ id' ∧
         id_ok fml' id' ∧
         (∀n x.
          lookup n fml = SOME (x,T) ⇒
            lookup n fml' = SOME (x,T)) ∧
         (¬b ⇒
         (∀n x.
          (lookup n fml' = SOME (x,T) ⇒
            lookup n fml = SOME (x,T)))) ∧
         (core_only_fml b fml) ⊨ (core_only_fml b fml')
     | NONE => T)
Proof
  ho_match_mp_tac check_lstep_ind \\
  reverse (rpt strip_tac)
  >- (
    simp[Once check_lstep_def]>>
    every_case_tac>>gs[]>>
    fs[sat_implies_def,satisfiable_def]>>
    metis_tac[])
  >- simp[Once check_lstep_def]
  \\ Cases_on ‘∃n c. step = Check n c’
  >- (
    rw[check_lstep_def] \\ every_case_tac \\ fs [] \\ metis_tac[sat_implies_refl])
  \\ Cases_on ‘∃n. step = Delete n’
  THEN1 (
    simp[check_lstep_def] \\
    Cases_on`step` \\  fs[] \\
    every_case_tac \\ rw []
    >- metis_tac[id_ok_FOLDL_delete]
    >- (
      fs[lookup_FOLDL_delete,EVERY_MEM,lookup_core_only_def,AllCaseEqs()]>>
      metis_tac[option_CLAUSES,PAIR,SND])
    >- fs[lookup_FOLDL_delete]
    >- (
      match_mp_tac sat_implies_subset>>
      simp[core_only_fml_def,SUBSET_DEF]>>rw[]>>
      fs[lookup_FOLDL_delete]>>
      metis_tac[]))
  \\ Cases_on ‘step = NoOp’ >- simp[check_lstep_def]
  \\ Cases_on ‘∃c. step = Cutting c’
  THEN1 (
    simp[check_lstep_def] \\
    Cases_on`step` \\  fs[] \\
    every_case_tac \\ simp [] \\
    gvs[insert_fml_def]>>
    drule check_cutting_correct>>
    DEP_REWRITE_TAC[core_only_fml_insert] >> fs[id_ok_def]>>
    rw[]>>fs[sat_implies_def,core_only_fml_def]
    >- (
      rw[lookup_insert]>>fs[]>>
      first_x_assum(qspec_then`id` mp_tac)>>
      fs[domain_lookup])>>
    gvs[lookup_insert,AllCaseEqs()])
  \\ Cases_on `∃c ls. step = Rup c ls`
  THEN1 (
    fs[check_lstep_def] \\
    every_case_tac \\
    gvs[insert_fml_def]
    \\ CONJ_TAC >- fs[id_ok_def]
    \\ CONJ_TAC >- (
      rw[lookup_insert]>>fs[id_ok_def]>>
      last_x_assum(qspec_then`id` mp_tac)>>simp[]>>
      metis_tac[domain_lookup])
    \\ CONJ_TAC >- (
      rw[]>>gvs[lookup_insert,AllCaseEqs()])
    \\ drule check_rup_unsat
    \\ simp[agree_assg_def]
    \\ rw[] \\ fs[sat_implies_def]
    \\ rw[]
    \\ gvs[id_ok_def,core_only_fml_insert]
    \\ metis_tac[not_thm])
  (* Proof by contradiction *)
  \\ Cases_on ‘∃c steps n. step = Con c steps n’
  THEN1 (
    gvs[check_lstep_def,insert_fml_def]
    \\ last_x_assum mp_tac
    \\ impl_tac >- (
      fs[id_ok_def,SUBSET_DEF]>>rw[]>>
      metis_tac[])
    \\ TOP_CASE_TAC \\ gvs[AllCaseEqs()]
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac
    \\ rpt(TOP_CASE_TAC \\ fs[])
    \\ gvs[]
    \\ CONJ_TAC >- fs[id_ok_def]
    \\ CONJ_TAC >- (
      rw[lookup_insert]>>fs[id_ok_def]>>
      last_x_assum(qspec_then`n'` mp_tac)>>simp[]>>
      metis_tac[domain_lookup])
    \\ CONJ_TAC >- (
      rw[]>>gvs[lookup_insert,AllCaseEqs()])
    \\ drule check_contradiction_fml_unsat
    \\ rw[] \\ fs[unsatisfiable_def,sat_implies_def]
    \\ rw[]
    \\ gvs[id_ok_def,core_only_fml_insert]
    \\ CCONTR_TAC \\ fs[GSYM not_thm]
    \\ first_x_assum(qspec_then`w` mp_tac)
    \\ impl_tac >- metis_tac[not_thm]
    \\ metis_tac[satisfies_def,satisfiable_def])
  THEN1 (
    rw[Once check_lstep_def]
    \\ every_case_tac \\ gvs [])
QED

(* TODO
Theorem check_lstep_compact:
  (∀step b core fml id fml' core' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ lstep_ok step ∧
     check_lstep step b core fml id = SOME(fml',core',id') ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀steps b core fml id fml' core' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ EVERY lstep_ok steps ∧
     check_lsteps steps b core fml id = SOME(fml',core',id') ⇒
     (∀c. c ∈ range fml' ⇒ compact c))
Proof
  ho_match_mp_tac check_lstep_ind
  \\ rpt strip_tac
  >- (
    Cases_on`step`>>fs[check_lstep_def]
    >- metis_tac[range_FOLDL_delete,SUBSET_DEF]
    >- (
      gvs[insert_fml_def,AllCaseEqs()]>>
      drule range_insert_2>>rw[]>>
      metis_tac[check_cutting_compact])
    \\ gvs[AllCaseEqs(),insert_fml_def]
    \\ imp_res_tac range_insert_2 \\ gvs [] )
  >- fs[Once check_lstep_def]
  >- (
    qpat_x_assum`_ = SOME _` mp_tac>>
    simp[Once check_lstep_def]>>
    every_case_tac>>fs[])
QED
*)

Type subst_raw = ``:(num , bool + num lit) alist``;

(* Steps that preserve satisfiability modulo
  a preserved set of variables *)
Datatype:
  sstep =
  | Lstep lstep (* Id representing a contradiction *)
  | Red npbc subst_raw
      (( ((num + num) # num) option, (lstep list)) alist)
      (num option)
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
  (extract_clauses f b fml rsubs [] acc =
    SOME (REVERSE acc)) ∧
  (extract_clauses f b fml rsubs (cpf::pfs) acc =
    case cpf of
      (NONE,pf) =>
      extract_clauses f b fml rsubs pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
      (case lookup_core_only b fml n of
        NONE => NONE
      | SOME c =>
        extract_clauses f b fml rsubs pfs
          ((SOME ([not (subst f c)],i),pf)::acc))
    | (SOME (INR u,i),pf) =>
      if u < LENGTH rsubs then
        extract_clauses f b fml rsubs pfs ((SOME (EL u rsubs,i),pf)::acc)
      else
        NONE)
End

Theorem extract_clauses_MAP_SND:
  ∀f b fml rsubs pfs acc res.
  extract_clauses f b fml rsubs pfs acc = SOME res ⇒
  MAP SND res =  REVERSE (MAP SND acc) ++ MAP SND pfs
Proof
  Induct_on`pfs`>>rw[extract_clauses_def] >> simp[MAP_REVERSE]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  rw[]
QED

Definition list_insert_fml_def:
  (list_insert_fml b fml id [] =
    (fml,id)) ∧
  (list_insert_fml b fml id (c::cs) =
    case insert_fml b fml id c of
    (fml',id') =>
    list_insert_fml b fml' id' cs)
End

(* Check a list of subproofs *)
Definition check_subproofs_def:
  (check_subproofs [] b fml id = SOME (fml,id)) ∧
  (check_subproofs ((cnopt,pf)::pfs) b fml id =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps pf b fml id of
        SOME (fml',id') =>
          check_subproofs pfs b fml' id'
      | res => NONE)
    | SOME (cs,n) =>
      (let (cfml,cid) = list_insert_fml b fml id cs in
      case check_lsteps pf b cfml cid of
        SOME(fml',id') =>
        if check_contradiction_fml b fml' n
        then check_subproofs pfs b fml id'
        else NONE
      | res => NONE))
End

Type subst = ``:(num # (bool + num lit)) + (bool + num lit) option vector``;

Definition subst_fun_def:
  subst_fun (s:subst) n =
  case s of
    INL (m,v) => if n = m then SOME v else NONE
  | INR s =>
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

(* Checking triviality for a negated target c *)
Definition check_triv_def:
  check_triv extra nc =
  (check_contradiction (add extra nc) ∨
  check_contradiction nc)
End

(* Partition the formula goals into proved and non-proved
  For each non-proved goal, check if
  0) it is implied by extra (= ¬ C) or trivial
  1) it was already in the formula
  2) it was already proved by another proofgoal (excluding #)
*)
Definition split_goals_def:
  split_goals (fml:npbc num_map)
    (extra:npbc) (proved:num_set)
    (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). sptree$lookup i proved ≠ NONE) goals in
  let proved = MAP SND lp in
  let f = range fml in
  EVERY (λ(i,c). c ∈ f ∨ check_triv extra (not c) ∨ mem_constraint c proved) lf
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

(* The core formula, not executable *)
Definition mk_core_fml_def:
  mk_core_fml b fml =
  map_opt (λ(x,b').
    if b ⇒ b' then SOME x else NONE) fml
End

Definition mk_subst_def:
  (mk_subst [(n,v)] = INL (n,v)) ∧
  (mk_subst xs = INR (spt_to_vec (fromAList xs)))
End

Definition check_hash_triv_def:
  check_hash_triv extra ncs =
    EXISTS (check_triv extra) ncs
End

(* pres : num_set -- forces all LHS of the
  substitution to not contain pres *)
Definition check_pres_def:
  check_pres pres s =
  case pres of NONE => T
  | SOME pres => EVERY (λx. lookup (FST x) pres = NONE) s
End

(* The tcb flag indicates we're in to-core mode
  where it is guaranteed that the core formula implies derived *)
Definition check_red_def:
  check_red pres ord obj b tcb fml id c s pfs idopt =
  if check_pres pres s then
    ( let nc = not c in
      let (fml_not_c,id1) = insert_fml b fml id (not c) in
      let s = mk_subst s in
      let w = subst_fun s in
      let rsubs = red_subgoals ord w c obj in
      case extract_clauses w b fml rsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs b fml_not_c id1 of
        NONE => NONE
      | SOME (fml',id') =>
        let chk =
          (case idopt of NONE =>
            (
            let gfml = mk_core_fml (b ∨ tcb) fml in
            let goals = toAList (map_opt (subst_opt w) gfml) in
            let (l,r) = extract_pids pfs LN LN in
              split_goals gfml nc l goals ∧
              EVERY (λ(id,cs).
                lookup id r ≠ NONE ∨
                check_hash_triv nc cs
                )
                (enumerate 0 rsubs))
          | SOME cid =>
            check_contradiction_fml b fml' cid) in
        if chk then
          SOME id'
        else NONE) )
  else NONE
End

Definition check_sstep_def:
  check_sstep sstep (pres : num_set option) ord obj tcb
    (fml:pbf) (id:num) =
  case sstep of
    Lstep lstep => check_lstep lstep F fml id
  | Red c s pfs idopt =>
    case check_red pres ord obj F tcb fml id c s pfs idopt of
      SOME id' => SOME (insert_fml tcb fml id' c)
    | NONE => NONE
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

Theorem list_insert_fml_ok:
  ∀xs fml id fml' id'.
  list_insert_fml b fml id xs = (fml',id') ∧
  id_ok fml id ⇒
  id ≤ id' ∧
  id_ok fml' id' ∧
  core_only_fml b fml' =
    set xs ∪ (core_only_fml b fml)
Proof
  Induct>>simp[list_insert_fml_def]>>
  ntac 6 strip_tac>>
  gvs[AllCaseEqs(),insert_fml_def]>>
  simp[]>>
  first_x_assum drule>>
  impl_tac >-
    fs[id_ok_def]>>
  rw[]>>
  DEP_REWRITE_TAC[core_only_fml_insert]>>
  fs[id_ok_def]>>
  simp[EXTENSION]>>
  metis_tac[]
QED

Theorem check_subproofs_correct:
  ∀pfs b fml id.
  id_ok fml id ⇒
  case check_subproofs pfs b fml id of
    SOME (fml',id') =>
     id ≤ id' ∧
     (core_only_fml b fml) ⊨ (core_only_fml b fml') ∧
     EVERY (λ(cnopt,pf).
       case cnopt of
         NONE => T
       | SOME (cs,n) =>
        unsatisfiable (core_only_fml b fml ∪ set cs)
     ) pfs
  | NONE => T
Proof
  Induct>-
    rw[check_subproofs_def]>>
  Cases>>rw[check_subproofs_def]>>
  Cases_on`q`>>fs[]
  >- (
    every_case_tac>>fs[]>>
    drule (CONJUNCT2 check_lstep_correct)>>
    disch_then (qspecl_then[`r`,`b`] assume_tac)>>
    gs[]>>
    first_x_assum drule>>simp[]>>
    disch_then(qspec_then`b` mp_tac)>> simp[]>>
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
  drule_all list_insert_fml_ok>>
  strip_tac>>
  drule (CONJUNCT2 check_lstep_correct)>>
  disch_then (qspecl_then[`r`,`b`] assume_tac)>>
  gs[SUBSET_DEF]>>
  rename1 `cid ≤ n`>>
  `id_ok fml n` by (
    fs[id_ok_def,SUBSET_DEF])>>
  first_x_assum drule>>
  disch_then(qspec_then`b` mp_tac)>> simp[]>>
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
  ∀s b fml sg pfs acc res c pf.
  extract_clauses s b fml sg pfs acc = SOME res ∧
  MEM (SOME c,pf) acc ⇒
  MEM (SOME c,pf) res
Proof
  Induct_on`pfs`>>fs[extract_clauses_def]>>rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

(*
Theorem lookup_core_only_fml:
  core_only b core id ⇒
  lookup id (core_only_fml b core fml) =
  lookup id fml
Proof
  rw[core_only_def,core_only_fml_def,coref_def]>>
  simp[lookup_inter_alt,domain_lookup]
QED
*)

Theorem extract_clauses_MEM_INL:
  ∀s b fml sg pfs acc res id pf n.
  extract_clauses s b fml sg pfs acc = SOME res ∧
  MEM (SOME (INL id,n), pf) pfs ⇒
  ∃c.
    lookup_core_only b fml id = SOME c ∧
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
  ∀s b fml sg pfs acc res id pf n.
  extract_clauses s b fml sg pfs acc = SOME res ∧
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

Theorem sat_obj_po_fml_SUBSET:
  sat_obj_po pres ord obj a y ∧
  x ⊆ y ⇒
  sat_obj_po pres ord obj a x
Proof
  rw[sat_obj_po_def]>>
  first_x_assum drule>>
  rw[]>>
  drule_all satisfies_SUBSET>>
  rw[]>>
  metis_tac[]
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
  split_goals fml e proved goals ∧
  MEM (n,yy) goals ⇒
  yy ∈ range fml ∨ check_triv e (not yy) ∨
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
  >-
    metis_tac[]
  >- (
    first_x_assum drule>>rw[]>>
    pairarg_tac>>gvs[]>>
    metis_tac[])
QED

Theorem sat_obj_po_insert_contr:
  unsatisfiable (rf ∪ {not c}) ∧
  (ord ≠ NONE ⇒ reflexive (po_of_spo (THE ord)))
  ⇒
  sat_obj_po pres ord obj rf (c INSERT rf)
Proof
  rw[sat_obj_po_def,unsatisfiable_def,satisfiable_def]>>
  first_assum (irule_at Any)>>
  rw[]
  >-
    metis_tac[not_thm]>>
  Cases_on`ord`>>
  fs[]>>
  metis_tac[reflexive_def,PAIR]
QED

Theorem range_mk_core_fml:
  range (mk_core_fml b fml) =
  core_only_fml b fml
Proof
  rw[mk_core_fml_def,core_only_fml_def,range_def,EXTENSION]>>
  fs[lookup_map_opt]>>eq_tac>>rw[]>>gvs[AllCaseEqs()]>>
  qexists_tac`n`>> fs[]>>
  pairarg_tac>>fs[]
QED

Theorem lookup_mk_core_fml:
  lookup i (mk_core_fml b fml) =
  lookup_core_only b fml i
Proof
  rw[mk_core_fml_def,lookup_core_only_def,lookup_map_opt]>>
  every_case_tac>>simp[]>>
  metis_tac[]
QED

Theorem sat_implies_INSERT:
  f ⊨ g ⇒
  (p INSERT f) ⊨ (p INSERT g)
Proof
  rw[sat_implies_def]
QED

Theorem sat_implies_union_right:
  f ⊨ g ⇒
  (f ∪ s) ⊨ (g ∪ s)
Proof
  rw[sat_implies_def]
QED

Theorem sat_implies_tcb:
  (tcb ⇒ core_only_fml T fml ⊨ core_only_fml b fml) ⇒
  core_only_fml (b ∨ tcb) fml ⊨ core_only_fml b fml
Proof
  rw[sat_implies_def]>>
  Cases_on`tcb`>>fs[]>>
  Cases_on`b`>>
  metis_tac[]
QED

Theorem in_core_only_fml_or_left:
  x ∈ core_only_fml (b ∨ tcb) fml ⇒
  x ∈ core_only_fml b fml
Proof
  rw[core_only_fml_def]>>
  metis_tac[]
QED

Theorem lookup_mk_core_fml_inj:
  lookup i (mk_core_fml b fml) = SOME c ∧
  lookup i (mk_core_fml b' fml) = SOME c' ⇒
  c = c'
Proof
  rw[lookup_mk_core_fml,lookup_core_only_def]>>
  gvs[AllCaseEqs()]
QED

Theorem MEM_enumerate_index:
  ∀k xs.
  MEM (i,e) (enumerate k xs) ⇒
  ∃j. j < LENGTH xs ∧ i = k + j
Proof
  Induct_on`xs`>>rw[miscTheory.enumerate_def]
  >- intLib.ARITH_TAC>>
  first_x_assum drule>>
  rw[]
  >- intLib.ARITH_TAC
QED

Theorem MEM_enumerate_iff:
  MEM ie (enumerate 0 xs) ⇔
  ∃i e. ie = (i,e) ∧ i < LENGTH xs ∧ EL i xs = e
Proof
  Cases_on`ie`>>
  rename1`MEM (i,e) _ `>>
  Cases_on`i < LENGTH xs`>>fs[MEM_enumerate]
  >- metis_tac[]>>
  CCONTR_TAC>>fs[]>>
  drule MEM_enumerate_index>>
  rw[]
QED

Theorem check_triv_unsatisfiable:
  check_triv extra nc ⇒
  unsatisfiable (fml ∪ {extra} ∪ {nc})
Proof
  rw[check_triv_def]>>
  drule check_contradiction_unsat>>
  rw[unsatisfiable_def,satisfiable_def]>>
  metis_tac[add_thm]
QED

Theorem check_triv_unsatisfiable_2:
  check_triv extra nc ∧
  extra ∈ fml ∧ nc ∈ fml
  ⇒
  unsatisfiable fml
Proof
  rw[check_triv_def]>>
  drule check_contradiction_unsat>>
  rw[unsatisfiable_def,satisfiable_def,satisfies_def]>>
  metis_tac[add_thm]
QED

Theorem check_pres_subst_fun:
  ∀s.
  check_pres pres s ⇒
  (∀x. x ∈ pres_set_spt pres ⇒
    subst_fun (mk_subst s) x = NONE)
Proof
  Cases_on`pres`>>
  gvs[check_pres_def,pres_set_spt_def]>>
  ho_match_mp_tac mk_subst_ind>>
  rw[pres_set_spt_def,mk_subst_def,subst_fun_def,check_pres_def,domain_lookup]
  >-
    (pop_assum mp_tac>>EVAL_TAC)>>
  qmatch_goalsub_abbrev_tac`sub vv yy`>>
  `vec_lookup vv yy = NONE` by
    (gvs[Abbr`vv`,Abbr`yy`,vec_lookup_num_man_to_vec,lookup_fromAList,ALOOKUP_NONE,EVERY_MEM,MEM_MAP]>>
    metis_tac[NOT_SOME_NONE])>>
  gvs[vec_lookup_def]
QED

Theorem check_red_correct:
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  (tcb ⇒ core_only_fml T fml ⊨ core_only_fml b fml) ∧
  check_red (pres: num_set option) ord obj b tcb fml id
    c s pfs idopt = SOME id' ⇒
  id ≤ id' ∧
  case idopt of
    SOME u =>
    (core_only_fml (b ∨ tcb) fml) ⊨ {c}
  | NONE =>
    sat_obj_po (pres_set_spt pres) ord obj
      (core_only_fml (b ∨ tcb) fml)
      (c INSERT (core_only_fml (b ∨ tcb) fml))
Proof
  simp[check_red_def]>>
  pairarg_tac>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  `id_ok fml_not_c id1 ∧ id ≤ id1` by
    gvs[insert_fml_def,id_ok_def]>>
  drule check_subproofs_correct>>
  `core_only_fml b fml_not_c =
    not c INSERT (core_only_fml b fml)` by (
    gvs[insert_fml_def]>>
    DEP_REWRITE_TAC[core_only_fml_insert]>>
    fs[id_ok_def])>>
  disch_then(qspecl_then [`x`,`b`] mp_tac)>>
  gvs[]>>
  reverse EVERY_CASE_TAC>>rw[]
  >- (
    drule check_contradiction_fml_unsat>>
    gs[sat_implies_def,satisfiable_def,unsatisfiable_def,range_insert]>>
    gvs[insert_fml_def,not_thm]>>
    Cases_on`tcb`>>fs[]
    >- (* tcb = T *)
      (Cases_on`b`>>fs[]>>
      metis_tac[])
    >-
      metis_tac[])>>
  qsuff_tac ‘redundant_wrt_obj_po (core_only_fml (b ∨ tcb) fml) (pres_set_spt pres) ord obj c’
  >- (
    fs [redundant_wrt_obj_po_def] \\ rw []
    \\ irule sat_obj_po_fml_SUBSET
    \\ pop_assum $ irule_at Any
    \\ rw [SUBSET_DEF] \\ imp_res_tac range_insert_2 \\ fs [])
  \\ pairarg_tac \\ fs[]
  \\ match_mp_tac (GEN_ALL substitution_redundancy_obj_po)
  \\ simp[]
  \\ qexists_tac ‘subst_fun (mk_subst s)’ \\ fs []
  \\ CONJ_TAC >-
    metis_tac[check_pres_subst_fun]
  \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]
  \\ `id ∉ domain fml` by fs[id_ok_def]
  \\
    `(core_only_fml (b ∨ tcb) fml ∪ {not c}) ⊨
    (core_only_fml b fml ∪ {not c})` by
    metis_tac[sat_implies_tcb,sat_implies_union_right]
  \\ drule sat_implies_transitive
  \\ disch_then (fn th => DEP_REWRITE_TAC[th])
  \\ simp [Once implies_explode]
  \\ gvs[red_subgoals_def,MEM_enumerate_iff,ADD1,AND_IMP_INTRO,PULL_EXISTS]
  \\ reverse (rw [])
  >- (
    (* dominance *)
    rw[sat_implies_EL]>>
    last_x_assum(qspec_then`SUC n` mp_tac)>>
    gvs[]>>
    PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
    strip_tac
    >- (
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
      fs[check_hash_triv_def]
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
      \\ simp[EL_MAP]
      \\ strip_tac
      \\ match_mp_tac unsatisfiable_not_sat_implies
      \\ metis_tac[check_triv_unsatisfiable]) )
  >- (
    (* objective *)
    Cases_on`obj`>> gvs[]>>
    last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun (mk_subst s)) ord))` mp_tac)>>
    gvs[]>>
    PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
    strip_tac
    >- (
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
      fs[check_hash_triv_def]
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
      \\ simp[EL_MAP]
      \\ strip_tac
      \\ match_mp_tac unsatisfiable_not_sat_implies
      \\ metis_tac[check_triv_unsatisfiable])
    )
  >- (
    (* redundancy #0 *)
    last_x_assum(qspec_then`0` mp_tac)>>
    gvs[]>>
    PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
    strip_tac
    >- (
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
    >- (
      fs[check_hash_triv_def]
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
      \\ simp[EL_MAP]
      \\ strip_tac
      \\ match_mp_tac unsatisfiable_not_sat_implies
      \\ metis_tac[check_triv_unsatisfiable]))
  (* rest of redundancy *)
  \\ gvs [GSYM unsat_iff_implies]
  \\ Cases_on ‘subst_opt (subst_fun (mk_subst s)) x'’ \\ fs []
  >- (
    imp_res_tac subst_opt_NONE
    \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
    \\ fs [satisfies_def,range_def,PULL_EXISTS]
    \\ metis_tac[in_core_only_fml_or_left])
  \\ fs[GSYM range_mk_core_fml]
  \\ qpat_x_assum`_ ∈ range _` mp_tac
  \\ simp[Once range_def]
  \\ strip_tac
  \\ rename1`lookup nn _ = SOME xx`
  \\ rename1`subst_opt _ _ = SOME yy`
  \\ `MEM (nn,yy) (toAList (map_opt (subst_opt (subst_fun (mk_subst s)))
      (mk_core_fml (b ∨ tcb) fml)))` by
     simp[MEM_toAList,lookup_map_opt]
  \\ drule_all split_goals_checked \\ rw[]
  >- (
    fs[satisfiable_def,not_thm,satisfies_def]>>
    drule subst_opt_SOME >>
    simp[]>>
    metis_tac[range_mk_core_fml,in_core_only_fml_or_left])
  >- (
    drule check_triv_unsatisfiable>>
    fs[unsatisfiable_def,satisfiable_def,not_thm,satisfies_def]>>
    drule subst_opt_SOME >>
    metis_tac[not_thm,imp_thm,in_core_only_fml_or_left])
  \\ drule_all lookup_extract_pids_l>>rw[]
  \\ drule extract_clauses_MEM_INL
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ gvs[unsatisfiable_def, MEM_toAList,lookup_map_opt,AllCaseEqs()]
  \\ fs[GSYM lookup_mk_core_fml]
  \\ metis_tac[INSERT_SING_UNION,UNION_COMM,subst_opt_SOME,lookup_mk_core_fml_inj]
QED

Theorem core_only_fml_T_cong:
  (∀n x. lookup n fml = SOME (x,T) ⇔ lookup n fml' = SOME (x,T))
  ⇒
  core_only_fml T fml = core_only_fml T fml'
Proof
  rw[core_only_fml_def,EXTENSION,EQ_IMP_THM]>>
  metis_tac[]
QED

Theorem sat_obj_po_refl:
  OPTION_ALL good_spo ord ⇒
  sat_obj_po pres ord obj f f
Proof
  rw[sat_obj_po_def]>>
  qexists_tac`w`>>
  simp[opt_le_def]>>
  Cases_on`ord`>>gs[good_spo_def]>>
  metis_tac[reflexive_def,reflexive_po_of_spo,PAIR]
QED

Theorem core_only_fml_T_insert_F:
  n ∉ domain fml ⇒
  core_only_fml T (insert n (c,F) fml) =
  core_only_fml T fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[domain_lookup]>>
  metis_tac[]
QED

Theorem core_only_fml_T_insert_T:
  n ∉ domain fml ⇒
  core_only_fml T (insert n (c,T) fml) =
  c INSERT core_only_fml T fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[domain_lookup]>>
  metis_tac[]
QED

Theorem core_only_fml_T_insert_b:
  n ∉ domain fml ⇒
  core_only_fml T (insert n (c,b) fml) =
  if b then c INSERT core_only_fml T fml else core_only_fml T fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[domain_lookup]>>
  metis_tac[]
QED

Theorem core_only_fml_F_insert_b:
  n ∉ domain fml ⇒
  core_only_fml F (insert n (c,b) fml) =
  c INSERT core_only_fml F fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[domain_lookup]>>
  metis_tac[]
QED

Theorem core_only_fml_T_SUBSET_F:
  core_only_fml T fml ⊆
  core_only_fml F fml
Proof
  rw[core_only_fml_def,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem sat_obj_po_SUBSET:
  OPTION_ALL good_spo ord ∧
  b ⊆ a ⇒
  sat_obj_po pres ord obj a b
Proof
  rw[sat_obj_po_def]>>
  imp_res_tac satisfies_SUBSET>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  Cases_on`ord`>>fs[good_spo_def]>>
  metis_tac[reflexive_def,reflexive_po_of_spo,PAIR]
QED

Theorem check_sstep_correct:
  ∀step pres ord obj fml id.
  id_ok fml id ∧
  OPTION_ALL good_spo ord ∧
  (tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ⇒
  case check_sstep step pres ord obj tcb fml id of
  | SOME (fml',id') =>
      id ≤ id' ∧
      id_ok fml' id' ∧
      sat_obj_po (pres_set_spt pres) ord obj
        (core_only_fml F fml)
        (core_only_fml F fml') ∧
      sat_obj_po (pres_set_spt pres) ord obj
        (core_only_fml T fml')
        (core_only_fml T fml) ∧
      (tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml')
  | NONE => T
Proof
  Cases>>rw[check_sstep_def]
  >- (
    drule (CONJUNCT1 check_lstep_correct)>>
    disch_then(qspecl_then [`l`,`F`] assume_tac)>>
    every_case_tac>>fs[]>>
    rename1`_ = SOME (fml',_)`>>
    `core_only_fml T fml = core_only_fml T fml'` by
      metis_tac[core_only_fml_T_cong]>>
    CONJ_TAC >- (
      gvs[satisfiable_def,sat_implies_def,sat_obj_po_def,core_only_fml_def]>>
      rw[]>>fs[]>>
      first_x_assum drule>>
      rw[]>>
      first_x_assum (irule_at Any)>> simp[]>>
      Cases_on`ord`>>
      fs[]>>
      metis_tac[good_spo_def,reflexive_def,reflexive_po_of_spo,PAIR])>>
    CONJ_TAC >-
      metis_tac[sat_obj_po_refl]>>
    rw[]>>fs[]>>
    gvs[satisfiable_def,sat_implies_def,sat_obj_po_def,core_only_fml_def]>>
    first_x_assum match_mp_tac>>
    first_x_assum match_mp_tac>>
    pop_assum mp_tac>> match_mp_tac satisfies_SUBSET>>
    fs[SUBSET_DEF]>>
    metis_tac[])
  >- ( (* Red *)
    every_case_tac>>gvs[]>>
    drule_all check_red_correct>>
    strip_tac>>
    gvs[insert_fml_def]>>
    DEP_REWRITE_TAC[core_only_fml_F_insert_b,core_only_fml_T_insert_b]>>
    fs[id_ok_def]>>
    CONJ_TAC >- (
      every_case_tac>>
      gvs[satisfiable_def,sat_implies_def,sat_obj_po_def]>>
      Cases_on`tcb`>>fs[]
      >-
        metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F]
      >- (
        rw[]>>qexists_tac`w`>>fs[]>>
        Cases_on`ord`>>
        fs[]>>
        metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,good_spo_def,reflexive_def,reflexive_po_of_spo,PAIR])
      >- (
        rw[]>>qexists_tac`w`>>fs[]>>
        Cases_on`ord`>>
        fs[]>>
        metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,good_spo_def,reflexive_def,reflexive_po_of_spo,PAIR]))>>
    CONJ_TAC >- (
      match_mp_tac sat_obj_po_SUBSET>>
      rw[SUBSET_DEF])>>
    rw[]>>fs[]>>
    metis_tac[sat_implies_INSERT])
QED

(*
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
  >- (
    pairarg_tac>>fs[]>>
    metis_tac[check_lstep_compact]) >>
  every_case_tac>>gvs[]>>
  drule range_insert_2>>rw[]>>
  metis_tac[]
QED
*)

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
  sat_obj_po pres ord obj x y ∧
  sat_obj_po pres ord obj y z ⇒
  sat_obj_po pres ord obj x z
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

Type subproof =
  ``:(((num + num) # num) option, lstep list) alist``;

Type assg_raw = ``:((num # bool) list)``;

Datatype:
  cstep =
  (* Derivation steps *)
  | Dom npbc subst_raw subproof (num option)
  | Sstep sstep

  (* Deletion steps *)
  | CheckedDelete num subst_raw subproof (num option)
  | UncheckedDelete (num list)
  | Transfer (num list) (* Move to core *)

  (* Configuration steps *)
  | StrengthenToCore bool
  | LoadOrder mlstring (num list)
  | UnloadOrder
  | StoreOrder mlstring (npbc list # var list # var list)
      (var list)
      (* transitivity proof *)
      subproof
      (* reflexivity proof *)
      subproof

  (* Objective steps *)
  | Obj assg_raw bool (int option)
  | ChangeObj bool ((int # var) list # int)
      (* sub proof*)
      subproof
    (* the bool indicates T (new) or F (diff) mode *)
  | CheckObj ((int # var) list # int)

  (* Preserved set step b=T is add, b=F is remove *)
  | ChangePres bool var npbc subproof
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

Definition to_flat_d_def:
  to_flat_d d n l acc =
    case l of
    | [] => REVERSE acc
    | ((m,x)::xs) => to_flat_d d (m+1) xs (x :: prepend (m-n) d acc)
End

Definition mk_obj_vec_def:
  mk_obj_vec (wm:((num # bool) list)) =
    let wms = mergesort_tail (λx y. FST x ≤ FST y) wm in
    Vector (to_flat_d F 0 wms [])
End

Definition vec_lookup_d_def:
  vec_lookup_d d vec n =
    if n < length vec then sub vec n else d
End

Definition check_obj_def:
  check_obj obj wm cs bopt =
  let wv = mk_obj_vec wm in
  let w = vec_lookup_d F wv in
  let new = eval_obj obj w in
  if
    EVERY (satisfies_npbc w) cs
  then
    case bopt of NONE => SOME new
    | SOME b =>
      if b = new then SOME new else NONE
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

(* non-core *)
Definition build_fml_def:
  (build_fml b (id:num) [] = LN) ∧
  (build_fml b id (cl::cls) =
    insert id (cl,b) (build_fml b (id+1) cls))
End

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml b n ls) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls,b)
  else NONE
Proof
  Induct>>rw[build_fml_def,lookup_def,lookup_insert]>>
  `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem domain_build_fml:
  ∀ls id.
  domain (build_fml b id ls) = {i | id ≤ i ∧ i < id + LENGTH ls}
Proof
  Induct>>rw[build_fml_def,EXTENSION]
QED

Theorem range_build_fml:
  ∀ls id.
    range (build_fml b id ls) = set (MAP (λc. (c,b)) ls)
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

(* Can be generalized if needed *)
Theorem core_only_fml_build_fml:
  ∀ls id.
  core_only_fml b (build_fml b id ls) = set ls
Proof
  Induct>>fs[build_fml_def,core_only_fml_def]>>
  fs[EXTENSION]>>
  rw[lookup_insert]>>
  (* 2 subgoals *)
  (rw[EQ_IMP_THM]>>gvs[]
  >- (
    every_case_tac>>fs[]>>
    metis_tac[])
  >- (
    every_case_tac>>fs[]>>
    metis_tac[])>>
  first_x_assum(qspecl_then[`id+1`,`x`] mp_tac)>>
  rw[]>>
  fs[lookup_build_fml]>>
  qexists_tac`n`>>simp[])
QED

(* the substituted RHS for reflexivity *)
Definition refl_subst_def:
  (refl_subst (f,us,vs) =
  let vs_us = list_list_insert vs us in
  let rsubst =
    (λn. case lookup n vs_us of
         | SOME x => SOME (INR (Pos x))
         | NONE => NONE) in
  let rhs = MAP (subst rsubst) f in
  rhs)
End

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

Definition check_reflexivity_def:
  check_reflexivity ord pfs id =
  let rhs = refl_subst ord in
  let fml = LN in
  let dsubs = MAP (λc. [not c]) rhs in
  case extract_clauses (λn. NONE) F LN dsubs pfs [] of
    NONE => F
  | SOME cpfs =>
  (case check_subproofs cpfs F fml id of
    SOME (fml',id') =>
    let (l,r) = extract_pids pfs LN LN in
       EVERY (λ(id,cs).
              lookup id r ≠ NONE ∨
              EXISTS check_contradiction cs
              )
              (enumerate 0 dsubs)
  | _ => F)
End

Definition check_transitivity_def:
  check_transitivity ord ws pfs =
  let (lhs,rhs) = trans_subst ord ws in
  let fml = build_fml F 1 lhs in
  let id = LENGTH lhs + 1 in
  let dsubs = MAP (λc. [not c]) rhs in
  case extract_clauses (λn. NONE) F LN dsubs pfs [] of
    NONE => NONE
  | SOME cpfs =>
  (case check_subproofs cpfs F fml id of
    SOME (fml',id') =>
    let (l,r) = extract_pids pfs LN LN in
    if
       EVERY (λ(id,cs).
              lookup id r ≠ NONE ∨
              EXISTS check_contradiction cs
              )
              (enumerate 0 dsubs)
    then SOME id'
    else NONE
  | _ => NONE)
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

Definition change_obj_subgoals_def:
  change_obj_subgoals fc fc' =
  let nmb1 = [not(model_bounding fc fc')] in
  let nmb2 = [not(model_bounding fc' fc)] in
  [nmb1; nmb2]
End

(* A simple equality test on objectives *)
Definition eq_obj_def:
  eq_obj fc fc' =
  (check_contradiction (not(model_bounding fc fc')) ∧
  check_contradiction (not(model_bounding fc' fc)))
End

Definition add_obj_def:
  add_obj (f,c:int) (f',c':int) =
  let (add,n) = add_lists f f' in
    (add, &n + c + c')
End

Theorem add_id[simp]:
  add ([],0) c = c
Proof
  Cases_on`c`>>EVAL_TAC>>
  Cases_on`q`>>EVAL_TAC
QED

Theorem check_contradiction_not_model_bounding:
  check_contradiction (not (model_bounding fc fc')) ⇒
  eval_obj (SOME fc) w ≤ eval_obj (SOME fc') w
Proof
  rw[]>>
  `imp ([],0) (model_bounding fc fc')` by
    fs[imp_def,add_def]>>
  drule imp_model_bounding>>
  simp[satisfies_npbc_def]
QED

Theorem eq_obj_eval_obj:
  eq_obj fc fc' ⇒
  eval_obj (SOME fc) w = eval_obj (SOME fc') w
Proof
  rw[eq_obj_def]>>
  imp_res_tac check_contradiction_not_model_bounding>>
  first_x_assum(qspec_then`w` assume_tac)>>
  first_x_assum(qspec_then`w` assume_tac)>>
  intLib.ARITH_TAC
QED

Theorem add_obj_eval_obj:
  eval_obj (SOME (add_obj fc fc')) w =
  eval_obj (SOME fc) w + eval_obj (SOME fc') w
Proof
  Cases_on`fc`>>
  Cases_on`fc'`>>
  rw[add_obj_def]>>
  pairarg_tac>>fs[]>>
  drule add_lists_thm>>
  disch_then(qspec_then`w` assume_tac)>>
  simp[eval_obj_def]>>
  intLib.ARITH_TAC
QED

Definition mk_diff_obj_def:
  mk_diff_obj b fc fc' =
  if b then fc' else add_obj fc fc'
End

Definition mk_tar_obj_def:
  mk_tar_obj b fc =
  (if b then fc else ([],0:int))
End

Definition check_change_obj_def:
  check_change_obj b fml id obj fc' pfs ⇔
  case obj of NONE => NONE
  | SOME fc =>
    ( let csubs = change_obj_subgoals
        (mk_tar_obj b fc) fc' in
      case extract_clauses (λx. NONE) T fml csubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs T fml id of
        NONE => NONE
      | SOME (fml',id') =>
        let (l,r) = extract_pids pfs LN LN in
        if
          EVERY (λ(id,cs).
              lookup id r ≠ NONE ∨
              EXISTS check_contradiction cs
              )
              (enumerate 0 csubs)
        then
          let fc'' = mk_diff_obj b fc fc' in
          SOME (fc'',id')
        else NONE))
End

Definition check_eq_obj_def:
  check_eq_obj obj fc' =
  case obj of NONE => F
  | SOME fc =>
    eq_obj fc fc'
End

Definition update_bound_def:
  update_bound chk bound dbound new =
  let dbound =
    if opt_lt (SOME new) dbound then
      SOME new else dbound in
  let bound =
    if chk ∧ opt_lt (SOME new) bound then
      SOME new else bound in
  (bound,dbound)
End

Definition do_transfer_def:
  (do_transfer fml [] = SOME fml) ∧
  (do_transfer fml (id::is) =
  case lookup id fml of NONE => NONE
  | SOME (c,_) =>
    do_transfer (insert id (c,T) fml) is)
End

Definition all_core_def:
  all_core fml =
  EVERY (λ(n,(c,b)). b) (toAList fml)
End

Definition v_iff_npbc_def:
  v_iff_npbc v c ⇔
  (* v ⇒ c *)
   (add ([(1,v)],1) (not c),
  (* c ⇒ v *)
    add c ([(-1,v)],1))
End

(* this equation is annoying when unfolded *)
Definition v_iff_npbc_sem_def:
  v_iff_npbc_sem v c w =
  (w v ⇔ satisfies_npbc w c)
End

Theorem satisfies_npbc_v_iff_npbc:
  v_iff_npbc v c = (vc,cv) ∧
  ¬ satisfies_npbc w vc ∧
  ¬ satisfies_npbc w cv
  ⇒
  v_iff_npbc_sem v c w
Proof
  rw[v_iff_npbc_sem_def,v_iff_npbc_def]>>gvs[not_thm]>>
  Cases_on`w v`>> gvs[]
  >- (
    `satisfies_npbc w ([(1,v)],1)` by
      simp[satisfies_npbc_def]>>
    CCONTR_TAC>>
    gvs[GSYM not_thm]>>
    metis_tac[add_thm,not_thm])>>
  `satisfies_npbc w ([(-1,v)],1)` by
    simp[satisfies_npbc_def]>>
  CCONTR_TAC>>
  gvs[GSYM not_thm]>>
  metis_tac[add_thm,not_thm]
QED

Definition change_pres_subgoals_def:
  change_pres_subgoals v c =
  let (vc,cv) = v_iff_npbc v c in
  [[vc]; [cv]]
End

Definition pres_only_def:
  pres_only (l,n) pres v ⇔
  EVERY (\(c,vv). lookup vv pres = SOME () ∧ vv ≠ v) l
End

Definition update_pres_def:
  update_pres b (v:num) pres =
    if b then insert v () pres else delete v pres
End

Definition check_change_pres_def:
  check_change_pres b fml id pres v c pfs ⇔
  case pres of NONE => NONE
  | SOME pres =>
    if pres_only c pres v then
    ( let csubs = change_pres_subgoals v c in
      case extract_clauses (λx. NONE) T fml csubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs T fml id of
        NONE => NONE
      | SOME (fml',id') =>
        let (l,r) = extract_pids pfs LN LN in
        if
          EVERY (λ(id,cs).
              lookup id r ≠ NONE ∨
              EXISTS check_contradiction cs
              )
              (enumerate 0 csubs)
        then
          SOME (update_pres b v pres,id')
        else NONE))
    else NONE
End

Datatype:
  proof_conf =
    <|
       id : num (* The next global ID *)
     ; chk : bool (* the checked deletion flag *)
     ; tcb : bool (* the strengthen-to-core flag *)
     ; pres : num_set option (* the preserved set *)
     ; obj : ((int # num) list # int) option (* the objective *)
     ; bound : int option  (* bound on obj *)
     ; dbound : int option (* bound on obj for unchecked del *)
     ; ord : spo option
     ; orders : (mlstring # (npbc list # var list # var list)) list
    |>
End

Definition check_tcb_idopt_def:
  check_tcb_idopt tcb idopt ⇔ tcb ⇒ idopt ≠ NONE
End

Definition check_cstep_def:
  (check_cstep cstep
    (fml:pbf)
    (pc : proof_conf) =
  case cstep of
  | Dom c s pfs idopt =>
    (case pc.ord of
      NONE => NONE
    | SOME spo =>
    if check_pres pc.pres s then
    ( let nc = not c in
      let (fml_not_c,id1) = insert_fml F fml pc.id (not c) in
      let s = mk_subst s in
      let w = subst_fun s in
      let dsubs = dom_subgoals spo w c pc.obj in
      case extract_clauses w F fml dsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs cpfs F fml_not_c id1 of
        NONE => NONE
      | SOME (fml',id') =>
        let check =
          (case idopt of NONE =>
            let cf = mk_core_fml T fml in
            let goals = toAList (map_opt (subst_opt w) cf) in
            let (l,r) = extract_pids pfs LN LN in
            let gfml = mk_core_fml F fml in
              split_goals gfml nc l goals ∧
              EVERY (λ(id,cs).
                lookup id r ≠ NONE ∨
                check_hash_triv nc cs
              )
              (enumerate 0 dsubs)
          | SOME cid =>
            check_contradiction_fml F fml' cid) in
        if check then
          SOME (insert id' (c,pc.tcb) fml, pc with id := id'+1)
        else NONE ))
    else NONE)
  | Sstep sstep =>
    (case check_sstep sstep pc.pres pc.ord pc.obj pc.tcb fml pc.id of
      SOME(fml',id') =>
        SOME (fml', pc with id := id')
    | NONE => NONE)
  | CheckedDelete n s pfs idopt =>
    if check_tcb_idopt pc.tcb idopt then
      (case lookup_core_only T fml n of
        NONE => NONE
      | SOME c =>
        (let nfml = delete n fml in
        case check_red pc.pres pc.ord pc.obj T pc.tcb nfml
          pc.id c s pfs idopt of
          SOME id' =>
          SOME (nfml,
          pc with <| id := id' |>)
        | NONE => NONE))
    else NONE
  | UncheckedDelete ls =>
      (* Either no order or all ids are in core *)
      if ¬pc.tcb ∧ pc.ord = NONE ∨
         all_core fml then
          SOME (FOLDL (λa b. delete b a) fml ls,
            pc with chk := F)
      else NONE
  | Transfer ls =>
    (case do_transfer fml ls of
      NONE => NONE
    | SOME fml' => SOME (fml', pc))
  | StrengthenToCore b =>
    SOME (
      if b then map (λ(c,b). (c,T)) fml else fml,
      pc with tcb := b)
  | LoadOrder name xs =>
      (case ALOOKUP pc.orders name of
        NONE => NONE
      | SOME ord' =>
        if LENGTH xs = LENGTH (FST (SND ord')) then
          SOME (
            map (λ(c,b). (c,T)) fml,
            pc with ord := SOME (ord',xs))
        else NONE)
  | UnloadOrder =>
    (case pc.ord of
      NONE => NONE
    | SOME spo =>
      SOME (fml, pc with ord := NONE))
  | StoreOrder name spo ws pfsr pfst =>
    if check_good_ord spo ∧ check_ws spo ws
    then
      case check_transitivity spo ws pfst of NONE => NONE
      | SOME id =>
        if check_reflexivity spo pfsr id then
          SOME (fml, pc with orders := (name,spo)::pc.orders)
        else NONE
    else
      NONE
  | Obj w mi bopt =>
    (case check_obj pc.obj w
      (MAP SND (toAList (mk_core_fml T fml))) bopt of
      NONE => NONE
    | SOME new =>
      let (bound',dbound') =
        update_bound pc.chk pc.bound pc.dbound new in
      if mi then
        let c = model_improving pc.obj new in
        SOME (
          insert pc.id (c,T) fml,
          pc with
          <| id := pc.id+1;
             bound := bound';
             dbound := dbound' |>)
      else
        SOME (fml,
          pc with
          <| bound := bound';
             dbound := dbound' |>))
  | ChangeObj b fc' pfs =>
    (case check_change_obj b fml pc.id pc.obj fc' pfs of
      NONE => NONE
    | SOME (fc',id') =>
      SOME (fml, pc with <| id := id'; obj := SOME fc' |>))
  | CheckObj fc' =>
    if check_eq_obj pc.obj fc'
    then SOME (fml,pc)
    else NONE
  | ChangePres b v c pfs =>
    (case check_change_pres b fml pc.id pc.pres v c pfs of
      NONE => NONE
    | SOME (pres',id') =>
      SOME (fml, pc with <| id := id'; pres := SOME pres' |>)
    )
  )
End

Definition valid_req_def:
  valid_req chk ord = (chk ∨ IS_SOME ord)
End

Definition valid_conf_def:
  valid_conf chk pres ord obj tcb fml ⇔
  (tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ∧
  (valid_req chk ord ⇒
    sat_obj_po (pres_set_spt pres) ord obj
      (core_only_fml T fml)
      (core_only_fml F fml))
End

Theorem satisfiable_SUBSET:
  Y ⊆ X ⇒
  (satisfiable X ⇒ satisfiable Y)
Proof
  rw[satisfiable_def]>>
  metis_tac[satisfies_SUBSET]
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

(* Redundant, but in various cases, we can drop
  from bimp_pres_obj to use this as it is simpler *)
Definition bimp_obj_def:
  bimp_obj bound fopt1 C1 fopt2 C2 ⇔
  ∀v. opt_lt (SOME v) bound ⇒
    imp_obj v fopt1 C1 fopt2 C2
End

Definition bimp_pres_obj_def:
  bimp_pres_obj bound pres1 fopt1 C1 pres2 fopt2 C2 ⇔
  ∀v. opt_lt (SOME v) bound ⇒
    ∃f.
    (
    INJ f
    (proj_pres pres1
      {w | satisfies w C1 ∧ eval_obj fopt1 w ≤ v})
    (proj_pres pres2
      {w' | satisfies w' C2 ∧ eval_obj fopt2 w' ≤ v})
    )
End

Theorem bimp_pres_obj_bimp_obj:
  bimp_pres_obj bound pres1 fopt1 C1 pres2 fopt2 C2 ⇒
  bimp_obj bound fopt1 C1 fopt2 C2
Proof
  rw[bimp_pres_obj_def,bimp_obj_def]>>
  first_x_assum drule>>rw[]>>
  rw[imp_obj_def,sat_obj_le_def]>>
  `∃pw. pw ∈ proj_pres pres1
    {w | satisfies w C1 ∧ eval_obj fopt1 w ≤ v}` by
    (simp[pbcTheory.proj_pres_def]>>
    metis_tac[])>>
  gvs[INJ_DEF]>>
  last_x_assum drule>>
  simp[pbcTheory.proj_pres_def]>>
  rw[]>>
  metis_tac[]
QED

Theorem bimp_obj_bimp_pres_obj_empty:
  bimp_obj bound fopt1 C1 fopt2 C2 ⇒
  bimp_pres_obj bound {} fopt1 C1 {} fopt2 C2
Proof
  rw[bimp_pres_obj_def,bimp_obj_def]>>
  first_x_assum drule>>
  rw[imp_obj_def,sat_obj_le_def]>>
  gvs[PULL_EXISTS]>>
  qexists_tac`I`>>
  rw[INJ_DEF,pbcTheory.proj_pres_def]>>
  metis_tac[]
QED

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

Theorem bimp_pres_obj_refl[simp]:
  bimp_pres_obj bound pres obj X pres obj X
Proof
  rw[bimp_pres_obj_def]>>
  qexists_tac`I`>>
  rw[INJ_DEF,pbcTheory.proj_pres_def]
QED

Theorem sat_obj_po_bimp_obj:
  sat_obj_po pres ord obj A B ⇒
  bimp_obj bound obj A obj B
Proof
  rw[sat_obj_po_def,bimp_obj_def,imp_obj_def,sat_obj_le_def]>>
  first_x_assum drule>>
  rw[]>>
  asm_exists_tac>>
  simp[]>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

Theorem sat_obj_po_bimp_pres_obj:
  sat_obj_po pres ord obj A B ⇒
  bimp_pres_obj bound pres obj A pres obj B
Proof
  rw[sat_obj_po_def,bimp_pres_obj_def]>>
  qexists_tac`I`>>
  rw[INJ_DEF,pbcTheory.proj_pres_def]>>
  first_x_assum drule>>rw[]>>
  first_x_assum (irule_at Any)>>simp[]>>
  CONJ_TAC >- (
    rw[EXTENSION]>>
    metis_tac[IN_DEF])>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

Theorem sat_obj_po_more:
  sat_obj_po pres ord obj A B ∧ A ⊆ C ⇒
  sat_obj_po pres ord obj C B
Proof
  rw[sat_obj_po_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem sat_obj_po_more_2:
  sat_obj_po pres ord obj A B ∧ C ⊨ A ⇒
  sat_obj_po pres ord obj C B
Proof
  rw[sat_obj_po_def,sat_implies_def]
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

Theorem bimp_pres_obj_SUBSET:
  B ⊆ A ⇒
  bimp_pres_obj bound pres obj A pres obj B
Proof
  rw[bimp_pres_obj_def]>>
  qexists_tac`I`>>
  rw[INJ_DEF,pbcTheory.proj_pres_def]>>
  first_x_assum (irule_at Any)>>simp[]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem range_toAList:
  range t = set (MAP SND (toAList t))
Proof
  rw[range_def,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList]
QED

Theorem id_ok_build_fml:
  ∀ls n.
  n + LENGTH ls ≤ id ⇒
  id_ok (build_fml b n ls) id
Proof
  Induct>>rw[]>>fs[build_fml_def,id_ok_def]
QED

Triviality subst_eta:
  subst f = subst (λx. f x)
Proof
  fs [SF ETA_ss]
QED

Theorem all_core_core_only_fml_eq:
  all_core fml ⇒
  core_only_fml T fml = core_only_fml F fml
Proof
  rw[all_core_def,core_only_fml_def,EVERY_MEM]>>
  fs[FORALL_PROD,MEM_toAList,EXTENSION]>>
  rw[]>>eq_tac>>rw[]
  >-
    metis_tac[]>>
  first_x_assum drule>>rw[]>>
  metis_tac[]
QED

Theorem all_core_valid_conf:
  OPTION_ALL good_spo ord ∧
  all_core fml ⇒
  valid_conf chk pres ord obj tcb fml
Proof
  rw[valid_conf_def]>>
  fs[all_core_core_only_fml_eq]>>
  metis_tac[sat_obj_po_refl]
QED

Theorem check_obj_imp:
  check_obj obj s ls b = SOME v ⇒
  ∃w.
  satisfies w (set ls) ∧
  eval_obj obj w = v
Proof
  rw[check_obj_def,AllCaseEqs()]>>
  fs[satisfies_def,EVERY_MEM]>>
  asm_exists_tac>>rw[]
QED

Theorem core_only_fml_T_insert_T_same:
  lookup n fml = SOME (c,b) ⇒
  core_only_fml T (insert n (c,T) fml) =
  c INSERT core_only_fml T fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[]
  >- metis_tac[]
  >- metis_tac[]>>
  qexists_tac`n'`>>rw[]>>fs[]
QED

Theorem core_only_fml_F_insert_b_same:
  lookup n fml = SOME (c,bb) ⇒
  core_only_fml F (insert n (c,b) fml) =
  c INSERT core_only_fml F fml
Proof
  rw[core_only_fml_def,lookup_insert,EXTENSION,EQ_IMP_THM]>>
  every_case_tac>>fs[]
  >- metis_tac[]
  >- metis_tac[]>>
  qexists_tac`n'`>>rw[]>>fs[]
QED

Theorem lookup_core_only_T_imp_F:
  lookup_core_only T fml i = SOME c ⇒
  lookup_core_only F fml i = SOME c
Proof
  rw[lookup_core_only_def,AllCaseEqs()]
QED

Theorem id_ok_map:
  id_ok fml id ⇒
  id_ok (map f fml) id
Proof
  rw[id_ok_def]
QED

Theorem pres_set_spt_SOME[simp]:
  pres_set_spt (SOME pres) = domain pres
Proof
  EVAL_TAC
QED

Theorem domain_update_pres:
  domain (update_pres b v pres) =
  if b then v INSERT domain pres else domain pres DELETE v
Proof
  rw[update_pres_def]
QED

Theorem pres_only_dependency:
  pres_only c pres v ∧
  (∀x. x ∈ domain pres ∧ x ≠ v ⇒ (w x ⇔ w' x)) ⇒
  satisfies_npbc w c = satisfies_npbc w' c
Proof
  Cases_on`c`>>rw[pres_only_def,satisfies_npbc_def]>>
  `SUM (MAP (eval_term w) q) =
   SUM (MAP (eval_term w') q)` by
    (Induct_on`q`>>gvs[]>>rw[]>>
    pairarg_tac>>gvs[domain_lookup])>>
  simp[]
QED

(* We only prove one direction, but converse works too.
  It is important that the equivalence is proved over core *)
Theorem valid_conf_update_pres:
  pres_only c pres v ∧
  (∀w.
      satisfies w (core_only_fml T fml) ⇒
      v_iff_npbc_sem v c w) ∧
  valid_conf chk (SOME pres) ord obj tcb fml ⇒
  valid_conf chk (SOME (update_pres b v pres)) ord obj tcb fml
Proof
  rw[valid_conf_def,sat_obj_po_def]>>gvs[]>>
  first_x_assum drule>>rw[]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  rw[domain_update_pres]
  >- (
    `satisfies w' (core_only_fml T fml)` by
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F]>>
    metis_tac[pres_only_dependency,v_iff_npbc_sem_def])
  >-
    metis_tac[]
QED

(* from pre-updated to updated *)
Theorem bimp_pres_obj_update_pres_1:
  pres_only c pres v ∧
  (∀w.
      satisfies w (core_only_fml T fml) ⇒
      v_iff_npbc_sem v c w) ⇒
  bimp_pres_obj dbound
    (domain pres) obj
    (core_only_fml F fml)
    (domain (update_pres b v pres)) obj
    (core_only_fml F fml)
Proof
  rw[bimp_pres_obj_def]>>
  gvs[pbcTheory.proj_pres_def,domain_update_pres]>>
  drule pres_only_dependency>>rw[]
  >- ( (* insertion: the injection maps v to its definition *)
    qexists_tac
      `λw x. if x = v then satisfies_npbc w c else w x` >>
    rw[INJ_DEF]
    >- (
      first_x_assum (irule_at Any)>>
      simp[EXTENSION]>>rw[]>>
      rename1`satisfies w _`>>
      last_x_assum(qspec_then`w` mp_tac)>>
      impl_tac >-
        metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F]>>
      simp[v_iff_npbc_sem_def,IN_DEF])
    >- (
      gvs[EXTENSION]>>
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,v_iff_npbc_sem_def,IN_DEF]))
  >- ( (* deletion: The injection drops v *)
    qexists_tac`λw x. if x = v then F else w x`>>
    rw[INJ_DEF]
    >- (
      first_x_assum (irule_at Any)>>
      simp[EXTENSION]>>rw[]>>
      metis_tac[])
    >- (
      gvs[EXTENSION]>>
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,v_iff_npbc_sem_def,IN_DEF]))
QED

(* from updated to pre-updated *)
Theorem bimp_pres_obj_update_pres_2:
  pres_only c pres v ∧
  (∀w.
      satisfies w (core_only_fml T fml) ⇒
      v_iff_npbc_sem v c w) ⇒
  bimp_pres_obj dbound
    (domain (update_pres b v pres)) obj
    (core_only_fml T fml)
    (domain pres) obj
    (core_only_fml T fml)
Proof
  rw[bimp_pres_obj_def]>>
  gvs[pbcTheory.proj_pres_def,domain_update_pres]>>
  drule pres_only_dependency>>rw[]
  >- ( (* reversed insertion: The injection drops v *)
    Cases_on`v ∈ domain pres`
    >- (
      `v INSERT domain pres = domain pres` by
        (fs[EXTENSION]>>metis_tac[])>>
      qexists_tac`I`>>simp[INJ_DEF])>>
    qexists_tac`λw x. if x = v then F else w x`>>
    rw[INJ_DEF]
    >- (
      first_x_assum (irule_at Any)>>
      simp[EXTENSION]>>rw[]>>
      metis_tac[])
    >- (
      gvs[EXTENSION]>>
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,v_iff_npbc_sem_def,IN_DEF]))
  >- ( (* reversed deletion: maps v to its definition *)
    reverse (Cases_on`v ∈ domain pres`)
    >- (
      `domain pres DELETE v = domain pres` by
        (fs[EXTENSION]>>metis_tac[])>>
      qexists_tac`I`>>simp[INJ_DEF])>>
    qexists_tac
      `λw x. if x = v then satisfies_npbc w c else w x` >>
    rw[INJ_DEF]
    >- (
      first_x_assum (irule_at Any)>>
      simp[EXTENSION]>>rw[]>>
      rename1`satisfies w _`>>
      last_x_assum(qspec_then`w` mp_tac)>>
      impl_tac >-
        metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F]>>
      simp[v_iff_npbc_sem_def,IN_DEF])
    >- (
      gvs[EXTENSION]>>
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F,v_iff_npbc_sem_def,IN_DEF]))
QED

Theorem proj_pres_SUBSET:
  x ⊆ y ⇒
  proj_pres p x ⊆ proj_pres p y
Proof
  rw[pbcTheory.proj_pres_def]
QED

Theorem check_cstep_correct:
  id_ok fml pc.id ∧
  OPTION_ALL good_spo pc.ord ∧
  EVERY (good_ord_t o SND) pc.orders ∧
  valid_conf pc.chk pc.pres pc.ord pc.obj pc.tcb fml ⇒
  case check_cstep cstep fml pc of NONE => T
  | SOME (fml',pc') =>
      pc.id ≤ pc'.id ∧
      id_ok fml' pc'.id ∧
      valid_conf pc'.chk pc'.pres pc'.ord pc'.obj pc'.tcb fml' ∧
      opt_le pc'.bound pc.bound ∧
      opt_le pc'.dbound pc.dbound ∧
      (opt_lt pc'.bound pc.bound ⇒
        sat_obj_le pc.obj
          (THE pc'.bound) (core_only_fml T fml)) ∧
      bimp_pres_obj pc'.dbound
        (pres_set_spt pc.pres)
          pc.obj  (core_only_fml F fml)
        (pres_set_spt pc'.pres)
          pc'.obj (core_only_fml F fml') ∧
      (pc'.chk ⇒
        bimp_pres_obj pc'.bound
        (pres_set_spt pc'.pres)
          pc'.obj (core_only_fml T fml')
        (pres_set_spt pc.pres)
          pc.obj (core_only_fml T fml)) ∧
      (pc'.chk ⇒ pc.chk) ∧ (¬pc'.chk ⇒ pc.bound = pc'.bound) ∧
      OPTION_ALL good_spo pc'.ord ∧
      EVERY (good_ord_t o SND) pc'.orders
Proof
  Cases_on`cstep`>>
  fs[check_cstep_def]
  >- ( (* Dominance *)
    Cases_on`pc.ord`>>fs[]>>
    pairarg_tac>>gvs[]>>
    TOP_CASE_TAC>>
    pop_assum mp_tac>>
    IF_CASES_TAC>>gvs[]>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>
    rw[]>>
    gvs[insert_fml_def]>>
    `id_ok (insert pc.id (not p,F) fml) (pc.id + 1)` by
      fs[id_ok_def]>>
    drule check_subproofs_correct>>
    rename1`check_subproofs pfs _ _`>>
    disch_then(qspecl_then [`pfs`,`F`] mp_tac)>>
    gs[]>> strip_tac>>
    rename1`insert cc (p,_) fml`>>
    CONJ_TAC>-
      gvs[id_ok_def,SUBSET_DEF]>>
    fs[valid_conf_def,valid_req_def]>>
    simp[opt_le_def,GSYM CONJ_ASSOC]>>
    CONJ_TAC >- (
      rw[]>>fs[]>>
      DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_F_insert_b]>>
      fs[id_ok_def]>>
      metis_tac[sat_implies_INSERT])>>
    `sat_obj_po (pres_set_spt pc.pres) (SOME x) pc.obj
      (core_only_fml T fml)
      (core_only_fml F (insert cc (p,F) fml))` by (
      reverse (every_case_tac)
      >- (
        `sat_obj_po (pres_set_spt pc.pres) (SOME x) pc.obj
          (core_only_fml F fml)
          (core_only_fml F (insert cc (p,F) fml))` by (
          DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
          CONJ_TAC >- fs[id_ok_def]>>
          match_mp_tac sat_obj_po_insert_contr>>
          fs[id_ok_def,good_spo_def]>>
          drule check_contradiction_fml_unsat>>
          qpat_x_assum`sat_implies _ _` mp_tac>>
          DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
          simp[]>>
          fs[core_only_fml_def]>>
          gs[sat_implies_def,satisfiable_def,unsatisfiable_def]>>
          metis_tac[])>>
        metis_tac[OPTION_ALL_def,sat_obj_po_trans])>>
      pairarg_tac>>fs[]>>
      simp[sat_obj_po_def]>>
      DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
      CONJ_TAC >- fs[id_ok_def]>>
      simp[satisfies_simp]>>
      simp[GSYM CONJ_ASSOC]>>
      PairCases_on`x`>>
      match_mp_tac (GEN_ALL good_spo_dominance)>>
      simp[]>>
      qexists_tac ‘subst_fun (mk_subst l)’>>fs[]>>
      CONJ_TAC >-
        metis_tac[check_pres_subst_fun]>>
      CONJ_TAC >-
        metis_tac[core_only_fml_T_SUBSET_F]>>
      CONJ_TAC >-
        gvs[sat_obj_po_def]>>
      `pc.id ∉ domain fml` by fs[id_ok_def]>>
      fs[core_only_fml_F_insert_b]>>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>
      gvs[dom_subgoals_def,MEM_enumerate_iff,ADD1,AND_IMP_INTRO,PULL_EXISTS]>>
      CONJ_TAC >- (
        (* core constraints*)
        rw[sat_implies_def,satisfies_def]
        \\ gs[PULL_EXISTS,GSYM range_mk_core_fml,range_def,lookup_mk_core_fml]
        \\ Cases_on ‘subst_opt (subst_fun (mk_subst l)) x’ \\ fs []
        THEN1 (
          imp_res_tac subst_opt_NONE
          \\ gvs[lookup_core_only_def,AllCaseEqs()]
          \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
          \\ fs [satisfies_def,range_def,PULL_EXISTS]
          \\ metis_tac[])
        \\ rename1`subst_opt _ _ = SOME yy`
        \\ `MEM (n,yy) (toAList (map_opt (subst_opt (subst_fun (mk_subst l)))
            (mk_core_fml T fml)))` by
            simp[MEM_toAList,lookup_map_opt,lookup_mk_core_fml,lookup_core_only_def]
        \\ drule_all split_goals_checked \\ rw[]
        >- (
          fs[satisfiable_def,not_thm,satisfies_def,range_mk_core_fml]>>
          fs[core_only_fml_def,lookup_core_only_def,AllCaseEqs(),PULL_EXISTS]>>
          drule subst_opt_SOME >>
          rw[]>> metis_tac[not_thm])
        >- (
          drule check_triv_unsatisfiable>>
          disch_then(qspec_then`{}` mp_tac)>>
          fs[unsatisfiable_def,satisfiable_def,not_thm,satisfies_def]>>
          drule subst_opt_SOME >>
          fs[range_def]>>
          rw[]>>
          metis_tac[not_thm,imp_thm])
        \\ drule_all lookup_extract_pids_l>>rw[]
        \\ drule_all extract_clauses_MEM_INL
        \\ strip_tac
        \\ last_x_assum drule
        \\ gvs[unsatisfiable_def,satisfiable_def, MEM_toAList,lookup_map_opt,AllCaseEqs(),satisfies_def,core_only_fml_def]
        \\ fs[not_thm,range_def,PULL_EXISTS]
        \\ rw[]
        \\ first_x_assum(qspec_then`w` mp_tac) \\ simp[]
        \\ strip_tac
        >- (
          fs[lookup_core_only_def,AllCaseEqs(),PULL_EXISTS]>>
          metis_tac[])
        \\ rename1`lookup i _ = SOME xxx`
        \\ `xxx = c` by (
          gvs[lookup_mk_core_fml]>>
          drule lookup_core_only_T_imp_F>>
          rw[])
        \\ `subst (subst_fun (mk_subst l)) c =
            subst (subst_fun (mk_subst l)) x` by
          metis_tac[subst_opt_SOME]
        \\ metis_tac[])>>
      CONJ_TAC >- (
        (* order constraints *)
        fs[core_only_fml_def]>>
        simp[GSYM LIST_TO_SET_MAP]>>
        rw[sat_implies_EL,EL_MAP]>>
        last_x_assum(qspec_then`n` mp_tac)>>
        gvs[dom_subst_def]>>
        PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
        strip_tac
        >- (
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
          simp[range_insert]>>
          metis_tac[INSERT_SING_UNION,UNION_COMM])
        >- (
          fs[check_hash_triv_def]
          \\ pop_assum mp_tac
          \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
          \\ simp[EL_MAP]
          \\ simp[lookup_list_list_insert,ALOOKUP_ZIP_MAP]
          \\ strip_tac
          \\ match_mp_tac unsatisfiable_not_sat_implies
          \\ metis_tac[check_triv_unsatisfiable])
      )>>
      CONJ_TAC >- (
        (* negated order constraint *)
        fs[core_only_fml_def]>>
        last_x_assum(qspec_then`LENGTH (dom_subst (subst_fun (mk_subst l)) (SOME ((x0,x1,x2),x3)))` mp_tac)>>
        gs[ADD1]>>
        PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
        strip_tac
        >- (
          drule_all lookup_extract_pids_r>>
          simp[]>> rw[]
          \\ drule extract_clauses_MEM_INR
          \\ disch_then drule
          \\ fs[]
          \\ DEP_REWRITE_TAC [EL_APPEND2]
          \\ simp[]
          \\ rw[]
          \\ first_x_assum drule \\ strip_tac
          \\ gs[neg_dom_subst_def,lookup_list_list_insert,ALOOKUP_ZIP_MAP,range_insert]
          \\ metis_tac[INSERT_SING_UNION,UNION_COMM,LIST_TO_SET_MAP])
        >- (
          fs[check_hash_triv_def]
          \\ pop_assum mp_tac
          \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
          \\ gs[neg_dom_subst_def,lookup_list_list_insert,ALOOKUP_ZIP_MAP,range_insert,EXISTS_MEM,MEM_MAP]
          \\ strip_tac \\ rw[]
          \\ drule check_triv_unsatisfiable_2
          \\ disch_then match_mp_tac
          \\ simp[])
        )>>
      (* objective constraint *)
      fs[core_only_fml_def]>>
      Cases_on`pc.obj`>>
      simp[]>>
      last_x_assum(qspec_then`SUC(LENGTH (dom_subst (subst_fun (mk_subst l)) (SOME ((x0,x1,x2),x3))))` mp_tac)>>
      gs[ADD1]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>>rw[]
        \\ drule extract_clauses_MEM_INR
        \\ disch_then drule
        \\ fs[]
        \\ DEP_REWRITE_TAC [EL_APPEND2]
        \\ simp[]
        \\ rw[]
        \\ first_x_assum drule \\ strip_tac
        \\ gs[range_insert]
        \\ drule unsatisfiable_not_sat_implies
        \\ metis_tac[INSERT_SING_UNION,UNION_COMM])
      >- (
          fs[check_hash_triv_def]
          \\ pop_assum mp_tac
          \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
          \\ simp[EL_MAP]
          \\ simp[lookup_list_list_insert,ALOOKUP_ZIP_MAP]
          \\ strip_tac
          \\ match_mp_tac unsatisfiable_not_sat_implies
          \\ metis_tac[check_triv_unsatisfiable])
      )>>
    CONJ_TAC >- (
      pop_assum mp_tac>>
      DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
      fs[id_ok_def]>>
      strip_tac>>drule sat_obj_po_more>>
      disch_then match_mp_tac>>
      Cases_on`pc.tcb`>> simp[]>>
      DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_T_insert_F]>>
      fs[id_ok_def]>>
      simp[SUBSET_DEF])>>
    CONJ_TAC >- (
      match_mp_tac (GEN_ALL sat_obj_po_bimp_pres_obj)>>
      qexists_tac`SOME x`>>
      `core_only_fml F (insert cc (p,F) fml) =
        core_only_fml F (insert cc (p,pc.tcb) fml)` by
        (Cases_on`pc.tcb`>> simp[]>>
        DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
        fs[id_ok_def])>>
      fs[]>>
      drule sat_obj_po_more>>
      simp[pres_set_spt_def]>>
      disch_then match_mp_tac>>
      metis_tac[core_only_fml_T_SUBSET_F])>>
    rw[]>>match_mp_tac bimp_pres_obj_SUBSET>>
    Cases_on`pc.tcb`>> simp[]>>
    DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_T_insert_F]>>
    fs[id_ok_def,SUBSET_DEF] )
  >- ( (* Sstep *)
    rw[]>>
    drule check_sstep_correct>>
    fs[valid_conf_def]>>
    disch_then drule>>
    disch_then drule>>
    disch_then (qspecl_then [`s`,`pc.pres`,`pc.obj`] mp_tac)>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    strip_tac>>
    rw[]>>gvs[pres_set_spt_def]>>
    metis_tac[sat_obj_po_trans,sat_obj_po_bimp_pres_obj])
  >- ( (* CheckedDelete *)
    rw[]>>
    every_case_tac>>fs[]>>
    `id_ok (delete n fml) pc.id` by
      (fs[id_ok_def]>>
      metis_tac[SUBSET_DEF])>>
    fs[valid_conf_def]>>
    drule check_red_correct>>
    rpt (disch_then (drule_at Any))>>
    impl_tac>-
      simp[sat_implies_refl]>>
    simp[]>>strip_tac>>
    CONJ_TAC >-
      fs[id_ok_def]>>
    `x INSERT core_only_fml T (delete n fml) =
      core_only_fml T fml` by
      (simp[core_only_fml_def,EXTENSION]>>
      rw[EQ_IMP_THM]
      >- (
        fs[lookup_core_only_def,AllCaseEqs()]>>
        metis_tac[])
      >- (
        fs[lookup_delete]>>
        metis_tac[])>>
      fs[lookup_core_only_def,AllCaseEqs(),lookup_delete]>>
      Cases_on`n=n'`>>fs[]>>
      metis_tac[])>>
    `sat_obj_po (pres_set_spt pc.pres) pc.ord pc.obj
      (core_only_fml T (delete n fml))
      (core_only_fml T fml)` by (
      every_case_tac>>gvs[]>>
      match_mp_tac (GEN_ALL sat_obj_po_more_2)>>
      qexists_tac`core_only_fml T fml`>>
      simp[sat_obj_po_refl]>>
      gvs[sat_implies_def]>>
      qpat_x_assum`_ = core_only_fml _ _` sym_sub_tac>>
      simp[])>>
    CONJ_TAC >-(
      rw[]>>gvs[]
      >- (
        fs[check_tcb_idopt_def]>>
        every_case_tac>> fs[sat_implies_def]>>
        rw[]>>
        qpat_x_assum`_ = core_only_fml _ _` sym_sub_tac>>
        fs[]>>
        `satisfies w (core_only_fml F fml)` by
          metis_tac[]>>
        pop_assum mp_tac>>
        match_mp_tac satisfies_SUBSET>>
        fs[core_only_fml_def,lookup_delete,SUBSET_DEF]>>
        metis_tac[])>>
      drule sat_obj_po_trans>>
      disch_then drule_all>>
      strip_tac>>
      drule sat_obj_po_trans>>
      disch_then match_mp_tac>>
      pop_assum (irule_at Any)>>
      match_mp_tac sat_obj_po_SUBSET>>
      fs[core_only_fml_def,lookup_delete,SUBSET_DEF]>>
      metis_tac[])>>
    CONJ_TAC >- (
      match_mp_tac bimp_pres_obj_SUBSET>>
      fs[core_only_fml_def,lookup_delete,SUBSET_DEF]>>
      metis_tac[])>>
    rw[]>>
    gvs[pres_set_spt_def]>>
    metis_tac[sat_obj_po_bimp_pres_obj])
  >- ( (* UncheckedDelete *)
    strip_tac>>
    IF_CASES_TAC >> simp[]>>
    CONJ_TAC >- metis_tac[id_ok_FOLDL_delete] >>
    CONJ_TAC >- (
      fs[]
      >- fs[valid_req_def,valid_conf_def]>>
      match_mp_tac all_core_valid_conf>>
      fs[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD]>>
      rw[lookup_FOLDL_delete]>>
      metis_tac[])>>
    match_mp_tac bimp_pres_obj_SUBSET>>
    rw[core_only_fml_def,SUBSET_DEF]>>
    fs[lookup_FOLDL_delete]>>
    metis_tac[])
  >- (
    (* Transfer *)
    strip_tac>>
    every_case_tac>>simp[]>>
    rpt (pop_assum mp_tac)>>
    qid_spec_tac`fml`>>
    qid_spec_tac`x`>>
    Induct_on`l`>>simp[do_transfer_def]>>
    ntac 7 strip_tac>>
    gvs[AllCaseEqs()]>>
    strip_tac>>
    first_x_assum (drule_at (Pos last))>>
    impl_tac >- (
      CONJ_TAC >- (
        fs[id_ok_def,domain_lookup,lookup_insert]>>rw[]>>
        metis_tac[])>>
      fs[valid_conf_def]>>
      DEP_REWRITE_TAC[GEN_ALL core_only_fml_T_insert_T_same,GEN_ALL core_only_fml_F_insert_b_same]>>
      simp[]>>
      CONJ_TAC >-
        metis_tac[sat_implies_INSERT]>>
      fs[sat_obj_po_def]>>
      rw[]>>gvs[]>>
      first_x_assum drule>>
      rw[]>>
      first_x_assum (irule_at Any)>> simp[]>>
      fs[satisfies_def,core_only_fml_def]>>
      metis_tac[])>>
    rw[]>>fs[bimp_pres_obj_def]>>
    gvs[core_only_fml_F_insert_b_same,core_only_fml_T_insert_T_same,PULL_EXISTS]>>
    rw[]>>first_x_assum drule
    >- (
      rw[]>>irule_at Any INJ_SUBSET>>
      pop_assum (irule_at Any)>>
      simp[]>>
      match_mp_tac proj_pres_SUBSET>>
      simp[SUBSET_DEF]>>
      fs[core_only_fml_def,satisfies_def]>>
      metis_tac[])
    >- (
      rw[]>>irule_at Any INJ_SUBSET>>
      pop_assum (irule_at Any)>>
      simp[]>>
      match_mp_tac proj_pres_SUBSET>>
      simp[SUBSET_DEF]))
  >- ( (* Strengthen-to-core *)
    strip_tac>>
    reverse IF_CASES_TAC>>
    fs[valid_conf_def,id_ok_map]>>
    `∀b.
      core_only_fml b (map (λ(c,b). (c,T)) fml) =
      core_only_fml F fml` by (
      simp[core_only_fml_def,lookup_map,EXTENSION,EQ_IMP_THM,EXISTS_PROD]>>rw[]>>
      metis_tac[PAIR])>>
    simp[sat_obj_po_refl]>>
    rw[]>>match_mp_tac bimp_pres_obj_SUBSET>>
    metis_tac[core_only_fml_T_SUBSET_F])
  >- ( (* LoadOrder *)
    every_case_tac>>
    simp[]>>
    drule ALOOKUP_MEM>>
    fs[EVERY_MEM,Once FORALL_PROD]>>
    strip_tac>>
    strip_tac>>
    first_x_assum drule>>
    simp[good_ord_t_def]>>strip_tac>>
    fs[valid_conf_def,id_ok_map]>>
    `∀b.
      core_only_fml b (map (λ(c,b). (c,T)) fml) =
      core_only_fml F fml` by
      (simp[core_only_fml_def,lookup_map,EXTENSION,EQ_IMP_THM,EXISTS_PROD]>>rw[]>>
      metis_tac[PAIR])>>
    simp[sat_obj_po_refl]>>
    rw[]>>
    match_mp_tac bimp_pres_obj_SUBSET>>
    metis_tac[core_only_fml_T_SUBSET_F])
  >- ( (* UnloadOrder *)
    rw[]>>
    every_case_tac>>
    fs[]>>
    fs[valid_conf_def,opt_le_def,valid_req_def]>>
    gvs[sat_obj_po_def]>>rw[]>>
    metis_tac[])
  >- ( (* StoreOrder *)
    rw[]>>fs[opt_le_def,bimp_obj_refl]>>
    every_case_tac>>fs[]>>
    rw[good_ord_t_def,good_spo_def]
    >-
      metis_tac[check_good_ord_good_ord]
    >- ( (* reflexivity *)
      PairCases_on`p`>>
      match_mp_tac (reflexive_po_of_spo |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
      gvs[check_reflexivity_def]>>
      every_case_tac>>fs[]>>
      pairarg_tac>>fs[]>>
      rw[]
      >-
        metis_tac[check_good_ord_good_ord]>>
      fs[refl_subst_def,lookup_list_list_insert]>>
      every_case_tac>>fs[]>>
      qmatch_asmsub_abbrev_tac`check_subproofs xx _ fmll idd`>>
      `id_ok fmll idd` by
        (unabbrev_all_tac>>simp[]>>
        fs[id_ok_def])>>
      drule check_subproofs_correct>>
      disch_then (qspecl_then[`xx`,`F`] mp_tac)>>simp[]>>
      every_case_tac>>
      rw[]>>
      simp[GSYM LIST_TO_SET_MAP]>>
      rw[sat_implies_EL]>>
      fs[EVERY_MEM,MEM_enumerate_iff,PULL_EXISTS]>>
      first_x_assum drule>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>>
        rw[]>>
        drule extract_clauses_MEM_INR>>
        disch_then drule>>
        simp[EL_MAP]>>
        rw[]>>
        first_x_assum drule>>
        simp[]>>rw[]>>
        drule unsatisfiable_not_sat_implies>>
        simp[core_only_fml_def,Abbr`fmll`] >>
        once_rewrite_tac [subst_eta] >> fs [] >>
        gvs [ALOOKUP_APPEND,ALOOKUP_ZIP_MAP])
      >- (
        gvs[EL_MAP]>>
        match_mp_tac unsatisfiable_not_sat_implies>>
        simp[]>>
        drule check_contradiction_unsat>>
        simp[unsatisfiable_def,satisfiable_def]>>
        once_rewrite_tac [subst_eta] >> fs [] >>
        rw[ALOOKUP_ZIP_MAP] )
      )>>
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
    qmatch_asmsub_abbrev_tac`check_subproofs xx _ fmll idd`>>
    `id_ok fmll idd` by
      (unabbrev_all_tac>>simp[]>>
      match_mp_tac id_ok_build_fml>>
      simp[])>>
    drule check_subproofs_correct>>
    disch_then (qspecl_then[`xx`,`F`] mp_tac)>>simp[]>>
    every_case_tac>>
    rw[]>>
    simp[GSYM LIST_TO_SET_MAP]>>
    rw[sat_implies_EL]>>
    fs[MEM_enumerate_iff]>>
    pairarg_tac>>gs[PULL_EXISTS]>>
    first_x_assum drule>>
    PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
    strip_tac
    >- (
      rw[]>>
      drule_all lookup_extract_pids_r>>
      simp[]>>
      rw[]>>
      drule extract_clauses_MEM_INR>>
      disch_then drule>>
      simp[EL_MAP]>>
      rw[]>>
      fs[EVERY_MEM]>>
      first_x_assum drule>>
      simp[]>>rw[]>>
      drule unsatisfiable_not_sat_implies>>
      simp[core_only_fml_build_fml,Abbr`fmll`] >>
      once_rewrite_tac [subst_eta] >> fs [] >>
      gvs [ALOOKUP_APPEND,ALOOKUP_ZIP_MAP] >>
      qmatch_goalsub_abbrev_tac ‘subst f1’ >> strip_tac >>
      qmatch_goalsub_abbrev_tac ‘subst f2’ >>
      qsuff_tac ‘f1 = f2’ >-
        (rw [] >> gvs []) >>
      unabbrev_all_tac >>
      fs [FUN_EQ_THM] >> rw [] >>
      ntac 4 (CASE_TAC >> fs []) )
    >- (
      gvs[EL_MAP]>>
      match_mp_tac unsatisfiable_not_sat_implies>>
      simp[]>>
      drule check_contradiction_unsat>>
      simp[unsatisfiable_def,satisfiable_def]>>
      once_rewrite_tac [subst_eta] >> fs [] >>
      rw[ALOOKUP_ZIP_MAP] ) )
  >- ( (* Obj *)
    strip_tac>>
    every_case_tac>>simp[]
    >- (
      (* Adding model improving *)
      gvs[update_bound_def]>>
      `pc.id ∉ domain fml` by fs[id_ok_def]>>
      CONJ_TAC >- fs[id_ok_def]>>
      CONJ_TAC >- (
        fs[valid_conf_def]>>
        DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_F_insert_b]>>
        simp[]>>
        CONJ_TAC >-
          metis_tac[sat_implies_INSERT]>>
        rw[]>>
        DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_F_insert_b]>>
        fs[sat_obj_po_def]>>rw[]>>
        first_x_assum drule>>
        rw[]>>
        qexists_tac`w'`>>simp[range_insert]>>
        fs[satisfies_npbc_model_improving]>>
        intLib.ARITH_TAC)>>
      CONJ_TAC >- rw[opt_le_def]>>
      CONJ_TAC >- rw[opt_le_def]>>
      CONJ_TAC >- (
        rw[]>>
        drule check_obj_imp>>rw[]>>
        fs[GSYM range_mk_core_fml,range_toAList,sat_obj_le_def]>>
        asm_exists_tac>>
        simp[]) >>
      CONJ_TAC>- (
        reverse IF_CASES_TAC>>simp[]
        >- (
          simp[core_only_fml_F_insert_b,bimp_pres_obj_def]>>
          rw[]>>
          qexists_tac`I`>>
          simp[INJ_DEF,satisfies_npbc_model_improving]>>
          Cases_on`pc.dbound`>>fs[opt_lt_def]>>
          rw[pbcTheory.proj_pres_def]>>
          first_assum (irule_at Any)>>simp[]>>
          intLib.ARITH_TAC)>>
        simp[core_only_fml_F_insert_b]>>
        fs[bimp_pres_obj_def]>>
        rw[]>>
        qexists_tac`I`>>
        simp[INJ_DEF,satisfies_npbc_model_improving]>>
        Cases_on`pc.dbound`>>fs[opt_lt_def]>>
        rw[pbcTheory.proj_pres_def]>>
        first_assum (irule_at Any)>>simp[]>>
        intLib.ARITH_TAC)>>
      strip_tac>>
      match_mp_tac bimp_pres_obj_SUBSET>>
      DEP_REWRITE_TAC[core_only_fml_T_insert_T]>>
      fs[SUBSET_DEF])>>
    gvs[update_bound_def]>>
    IF_CASES_TAC>>simp[opt_le_def,sat_obj_le_def]>>
    drule check_obj_imp>>rw[]>>
    fs[GSYM range_mk_core_fml,range_toAList]>>
    asm_exists_tac>>
    simp[])
  >- (
    (* ChangeObj *)
    strip_tac>>
    simp[check_change_obj_def,insert_fml_def]>>
    every_case_tac>>fs[]>>
    pairarg_tac>>gvs[]>>
    drule check_subproofs_correct>>
    rename1`check_subproofs pfs`>>
    disch_then(qspecl_then[`pfs`,`T`] mp_tac)>>simp[]>>
    strip_tac>>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>
    gvs[change_obj_subgoals_def,MEM_enumerate_iff,ADD1,PULL_EXISTS]>>
    qmatch_asmsub_abbrev_tac`model_bounding fnew fold`>>
    `unsatisfiable (core_only_fml T fml ∪ {not (model_bounding fnew fold)})` by (
      first_x_assum(qspec_then`0` mp_tac)>>
      simp[]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>> strip_tac>>
        drule_all extract_clauses_MEM_INR>>
        simp[]>>
        strip_tac>>
        first_x_assum drule>>simp[])
      >- (
        drule check_contradiction_unsat>>
        simp[unsatisfiable_def,satisfiable_def]
      ))>>
    `unsatisfiable (core_only_fml T fml ∪ {not (model_bounding fold fnew)})` by (
      first_x_assum(qspec_then`1` mp_tac)>>
      simp[]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>> strip_tac>>
        drule_all extract_clauses_MEM_INR>>
        simp[]>>
        strip_tac>>
        first_x_assum drule>>simp[])
      >- (
        drule check_contradiction_unsat>>
        simp[unsatisfiable_def,satisfiable_def]
      ))>>

    `∀w.
      satisfies w (core_only_fml T fml) ⇒
      eval_obj (SOME fold) w =
      eval_obj (SOME fnew) w` by
      (
      fs[unsatisfiable_def,satisfiable_def,satisfies_npbc_model_bounding,not_thm]>>
      rw[]>>gvs[]>>
      ntac 2 (first_x_assum (qspec_then `w` mp_tac))>>simp[]>>
      intLib.ARITH_TAC)>>

    qmatch_goalsub_abbrev_tac`SOME fupd`>>
    `∀w.
      satisfies w (core_only_fml T fml) ⇒
      eval_obj (SOME x) w =
      eval_obj (SOME fupd) w` by
      (unabbrev_all_tac>>gvs[mk_diff_obj_def,mk_tar_obj_def]>>
      rw[]>>first_x_assum drule>>
      rw[]>>
      simp[add_obj_eval_obj]>>
      EVAL_TAC)>>
    gvs[]>>
    CONJ_TAC >-
      fs[id_ok_def]>>
    CONJ_TAC >- (
      fs[sat_implies_def,valid_conf_def,sat_obj_po_def]>>
      strip_tac>>gs[]>>
      rw[]>>
      last_x_assum drule>>
      rw[]>>
      asm_exists_tac>>simp[]>>
      first_x_assum(qspec_then`w'` mp_tac)>>
      impl_tac >- (
        fs[core_only_fml_def,satisfies_def]>>
        metis_tac[])>>
      intLib.ARITH_TAC)>>
    CONJ_TAC >- (
      rw[bimp_pres_obj_def]>>
      qexists_tac`I`>>rw[INJ_DEF,pbcTheory.proj_pres_def]>>
      first_assum (irule_at Any)>> simp[]>>
      fs[satisfies_def,core_only_fml_def]>>
      metis_tac[])>>
    rw[bimp_pres_obj_def]>>
    qexists_tac`I`>>rw[INJ_DEF,pbcTheory.proj_pres_def]>>
    first_assum (irule_at Any)>> simp[])
  >-
    (every_case_tac>>rw[])
  >- (
    (* ChangePres *)
    rw[]>>
    simp[check_change_pres_def,AllCasePreds()]>>
    every_case_tac>>
    fs[]>>
    pairarg_tac>>gvs[]>>
    drule check_subproofs_correct>>
    rename1`check_subproofs pfs`>>
    disch_then(qspecl_then[`pfs`,`T`] mp_tac)>>simp[]>>
    strip_tac>>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>
    gvs[change_pres_subgoals_def,MEM_enumerate_iff,ADD1,PULL_EXISTS]>>
    pairarg_tac>>gvs[]>>
    rename1`v_iff_npbc v c = (vc,cv)`>>
    `unsatisfiable (core_only_fml T fml ∪ {vc})` by (
      first_x_assum(qspec_then`0` mp_tac)>>
      simp[]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>> strip_tac>>
        drule_all extract_clauses_MEM_INR>>
        simp[]>>
        strip_tac>>
        first_x_assum drule>>simp[])
      >- (
        drule check_contradiction_unsat>>
        simp[unsatisfiable_def,satisfiable_def]
      ))>>
    `unsatisfiable (core_only_fml T fml ∪ {cv})` by (
      first_x_assum(qspec_then`1` mp_tac)>>
      simp[]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_pids_r>>
        simp[]>> strip_tac>>
        drule_all extract_clauses_MEM_INR>>
        simp[]>>
        strip_tac>>
        first_x_assum drule>>simp[])
      >- (
        drule check_contradiction_unsat>>
        simp[unsatisfiable_def,satisfiable_def]
      ))>>

    `∀w.
      satisfies w (core_only_fml T fml) ⇒
      v_iff_npbc_sem v c w` by (
      fs[unsatisfiable_def,satisfiable_def]>>
      rw[]>>gvs[]>>
      drule satisfies_npbc_v_iff_npbc>>
      disch_then match_mp_tac>>
      metis_tac[]) >>

    CONJ_TAC >-
      fs[id_ok_def]>>

    CONJ_TAC >- metis_tac[valid_conf_update_pres]>>

    CONJ_TAC >- metis_tac[bimp_pres_obj_update_pres_1]>>
    metis_tac[bimp_pres_obj_update_pres_2] )
QED

Definition check_csteps_def:
  (check_csteps [] fml pc = SOME (fml,pc)) ∧
  (check_csteps (s::ss) fml pc =
    case check_cstep s fml pc of
    SOME (fml',pc') =>
    check_csteps ss fml' pc'
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

Theorem bimp_pres_obj_le:
  opt_le a b ∧
  bimp_pres_obj b pres obj A pres' obj' B ⇒
  bimp_pres_obj a pres obj A pres' obj' B
Proof
  rw[bimp_pres_obj_def]>>
  metis_tac[opt_lt_le]
QED

Theorem bimp_obj_trans:
  bimp_obj b obj A obj' B ∧
  bimp_obj b obj' B obj'' C ⇒
  bimp_obj b obj A obj'' C
Proof
  rw[bimp_obj_def,imp_obj_def]
QED

Theorem bimp_pres_obj_trans:
  bimp_pres_obj b pres obj A pres' obj' B ∧
  bimp_pres_obj b pres' obj' B pres'' obj'' C ⇒
  bimp_pres_obj b pres obj A pres'' obj'' C
Proof
  rw[bimp_pres_obj_def]>>
  first_x_assum drule>>
  first_x_assum drule>>
  rw[]>>
  metis_tac[INJ_COMPOSE]
QED

Theorem check_csteps_correct:
  ∀csteps fml pc fml' pc'.
  id_ok fml pc.id ∧
  OPTION_ALL good_spo pc.ord ∧
  EVERY (good_ord_t ∘ SND) pc.orders ∧
  valid_conf pc.chk pc.pres pc.ord pc.obj pc.tcb fml ∧
  check_csteps csteps fml pc = SOME(fml',pc') ⇒
    hide (
    pc.id ≤ pc'.id ∧
    id_ok fml' pc'.id ∧
    valid_conf pc'.chk pc'.pres pc'.ord pc'.obj pc'.tcb fml' ∧
    opt_le pc'.bound pc.bound ∧
    opt_le pc'.dbound pc.dbound ∧
    (opt_lt pc'.bound pc.bound ⇒
      sat_obj_le pc.obj (THE pc'.bound) (core_only_fml T fml)) ∧
    (bimp_pres_obj pc'.dbound
      (pres_set_spt pc.pres)
        pc.obj (core_only_fml F fml)
      (pres_set_spt pc'.pres)
        pc'.obj (core_only_fml F fml')) ∧
    (pc'.chk ⇒ bimp_pres_obj pc'.bound
        (pres_set_spt pc'.pres)
          pc'.obj (core_only_fml T fml')
        (pres_set_spt pc.pres)
          pc.obj (core_only_fml T fml)) ∧
    (pc'.chk ⇒ pc.chk) ∧ (¬pc.chk ⇒ pc.bound = pc'.bound) ∧
    OPTION_ALL good_spo pc'.ord ∧
    EVERY (good_ord_t o SND) pc'.orders )
Proof
  Induct
  >- (
    rw[check_csteps_def]>>
    rw[hide_def,opt_le_def])>>
  rw[]>>
  gvs[AllCaseEqs(),check_csteps_def]>>
  drule check_cstep_correct>>
  rpt (disch_then drule)>>
  disch_then(qspec_then `h` mp_tac)>>
  simp[]>>
  strip_tac>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  strip_tac>>fs[hide_def]>>
  CONJ_TAC >-
    metis_tac[opt_le_trans]>>
  CONJ_TAC >-
    metis_tac[opt_le_trans]>>
  CONJ_TAC >- (
    rw[]>>
    qpat_x_assum`opt_le pc'.bound pc''.bound` mp_tac>>
    simp[opt_le_def]>>
    strip_tac>>fs[]>>
    `opt_lt (SOME (THE pc'.bound)) pc''.bound` by
      (Cases_on`pc'.bound`>>fs[opt_lt_def])>>
    Cases_on`pc'.chk`>>fs[]>>
    Cases_on`pc''.chk`>>fs[]>>
    gvs[]>>imp_res_tac bimp_pres_obj_bimp_obj>>
    fs[bimp_obj_def,imp_obj_def]>>
    gvs[]>>
    fs[])>>
  rw[]>>fs[]>>
  metis_tac[bimp_pres_obj_trans,bimp_pres_obj_le]
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

Theorem bimp_pres_obj_NONE:
  bimp_pres_obj NONE pres1 obj1 C1 pres2 obj2 C2 ⇒
  (satisfiable C1 ⇒ satisfiable C2)
Proof
  rw[bimp_pres_obj_def,opt_lt_def,satisfiable_def]>>
  first_x_assum(qspec_then`eval_obj obj1 w` assume_tac)>>
  gvs[INJ_DEF]>>
  pop_assum kall_tac>>
  gvs[pbcTheory.proj_pres_def,PULL_EXISTS]>>
  metis_tac[integerTheory.INT_LE_REFL]
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

(*
Theorem range_coref_map_fml:
  range (coref (map (λv. ()) fml) fml) = range fml
Proof
  simp[range_def,lookup_inter,coref_def,lookup_map,EXTENSION,AllCaseEqs()]>>
  metis_tac[]
QED
*)

(* In the current setup, the
  o rule can log a solution with no objective
  In that case, the formula is satisfiable
Theorem check_csteps_optimal:
  id_ok fml id ∧
  check_csteps csteps
    fml id (map (λv. ()) fml) chk obj NONE NONE [] =
    SOME (fml',id',chk',obj',bound',ord',orders') ∧
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
 *)

(* Checking conclusions with hints given *)
Datatype:
  hconcl =
  | HNoConcl
  | HDSat (assg_raw option)
  | HDUnsat num
  | HOBounds (int option) (int option) num (assg_raw option)
End

Definition check_implies_fml_def:
  check_implies_fml fml n c =
  (case lookup n fml of
      NONE => F
    | SOME (ci,b) =>
      imp ci c)
End

(* if lower bound is infinity, must prove infeasibility *)
Definition lower_bound_def:
  lower_bound obj lb =
    let ob = case obj of NONE => ([],0) | SOME fc => fc in
    model_bounding ([],lb) ob
End

(* fml, obj are the original formula (as a list) and objective
  all the '-ed variables are after checking *)
Definition check_hconcl_def:
  (check_hconcl fml obj fml' obj' bound' dbound' HNoConcl = T) ∧
  (check_hconcl fml obj fml' obj' bound' dbound' (HDSat wopt) =
    case wopt of
      NONE =>
      (* Claiming SAT without witness needs
        at least one checked sol step *)
      bound' ≠ NONE
    | SOME wm =>
      (* Otherwise, use the witness *)
      check_obj obj wm fml NONE ≠ NONE) ∧
  (check_hconcl fml obj fml' obj' bound' dbound' (HDUnsat n) =
    (* Claiming UNSAT requires contradiction
      derived in the final formula *)
    (dbound' = NONE ∧ check_contradiction_fml F fml' n)) ∧
  (check_hconcl fml obj fml' obj' bound' dbound'
    (HOBounds lbi ubi n wopt) =
    (
    ((* Lower bound claimed must be at most the
      best bound seen in sol steps *)
    opt_le lbi dbound' ∧
    (* And the lower bound must be syntactically implied *)
    case lbi of
      NONE => check_contradiction_fml F fml' n
    | SOME lb => check_implies_fml fml' n (lower_bound obj' lb)) ∧
    (
    (* Claiming upper bound is similar to claiming SAT *)
    case wopt of
      NONE => opt_le bound' ubi
    | SOME wm =>
      opt_le (check_obj obj wm fml NONE) ubi)))
End

Definition hconcl_concl_def:
  (hconcl_concl HNoConcl = NoConcl) ∧
  (hconcl_concl (HDSat _) = DSat) ∧
  (hconcl_concl (HDUnsat _) = DUnsat) ∧
  (hconcl_concl (HOBounds lbi ubi _ _) = OBounds lbi ubi)
End

Definition init_conf_def:
  init_conf id chk pres obj =
  <|
       id := id
     ; chk := chk
     ; tcb := F
     ; obj := obj
     ; pres := pres
     ; bound := NONE
     ; dbound := NONE
     ; ord := NONE
     ; orders := []
    |>
End

Theorem check_csteps_check_hconcl:
  id_ok fml id ∧
  check_csteps csteps
    fml (init_conf id chk pres obj) =
    SOME (fml',pc') ∧
  all_core fml ∧
  set fmlls = core_only_fml T fml ∧
  check_hconcl fmlls obj fml' pc'.obj pc'.bound pc'.dbound hconcl ⇒
  sem_concl (set fmlls) obj (hconcl_concl hconcl)
Proof
  rw[]>>
  drule_at Any check_csteps_correct>>
  DEP_ONCE_REWRITE_TAC[all_core_valid_conf]>>
  simp[init_conf_def]>>
  rw[hide_def]>>
  Cases_on`hconcl`>>
  fs[hconcl_concl_def,sem_concl_def,check_hconcl_def]
  >- ( (* HDSat *)
    Cases_on`o'`>>gvs[]
    >- (
      Cases_on`pc'.bound`>>
      fs[opt_lt_def,sat_obj_le_def,valid_conf_def,opt_le_def]>>
      simp[satisfiable_def]>>
      metis_tac[])>>
    Cases_on`check_obj obj x fmlls NONE`>>gvs[]>>
    drule check_obj_imp>>
    rw[satisfiable_def]>>
    metis_tac[])
  >- ( (* HDUnsat *)
    drule check_contradiction_fml_unsat>>
    gvs[]>>
    drule bimp_pres_obj_NONE>>
    rw[]>>
    fs[all_core_core_only_fml_eq,unsatisfiable_def])
  >- ( (* HOBound *)
    CONJ_TAC >- (
      qpat_x_assum`_ o1 _ _` kall_tac>>
      fs[check_implies_fml_def]>>every_case_tac>>
      fs[lower_bound_def]
      >- (
        Cases_on`pc'.dbound`>>fs[opt_le_def,opt_lt_def]>>
        drule check_contradiction_fml_unsat>>
        gvs[]>>
        drule bimp_pres_obj_NONE>>
        fs[all_core_core_only_fml_eq,unsatisfiable_def]>>
        metis_tac[])>>
      imp_res_tac bimp_pres_obj_bimp_obj>>
      fs[bimp_obj_def,imp_obj_def]>>rw[]>>
      qpat_x_assum`opt_le _ pc'.dbound` mp_tac>>
      rw[]>>
      CCONTR_TAC>>fs[]>>
      last_x_assum(qspec_then`eval_obj obj w` mp_tac)>>
      impl_tac >- (
        Cases_on`pc'.dbound`>>
        fs[opt_lt_def]>>
        pop_assum kall_tac>>
        ntac 2(pop_assum mp_tac)>>
        rpt(pop_assum kall_tac)>>
        simp[opt_le_def,opt_lt_def]>>
        intLib.ARITH_TAC)>>
      impl_tac>- (
        simp[sat_obj_le_def]>>
        qexists_tac`w`>>gvs[all_core_core_only_fml_eq])>>
      strip_tac>>fs[sat_obj_le_def,satisfies_def,range_def]>>
      drule imp_thm>>
      disch_then(qspec_then `w'` mp_tac)>>
      impl_tac>- (
        first_x_assum match_mp_tac>>
        fs[core_only_fml_def]>>
        metis_tac[])>>
      fs[satisfies_npbc_model_bounding]>>
      qmatch_goalsub_abbrev_tac`~(_ ≤ b)`>>
      simp[eval_obj_def]>>
      `b = eval_obj pc'.obj w'` by
        (fs[Abbr`b`]>>
        TOP_CASE_TAC>>simp[eval_obj_def])>>
      rw[]>>
      qpat_x_assum`~(_ ≤ _)` mp_tac>>
      qpat_x_assum`(_ ≤ (_:int))` mp_tac>>
      rpt (pop_assum kall_tac)>>
      intLib.ARITH_TAC)>>
    qpat_x_assum`_ o' _ _` kall_tac>>
    EVERY_CASE_TAC>>gvs[]
    >- (
      Cases_on`pc'.bound`>-
        fs[opt_lt_def,opt_le_def]>>
      gvs[sat_obj_le_def,opt_lt_def,all_core_core_only_fml_eq]>>
      asm_exists_tac>>
      gvs[opt_le_def,opt_lt_def]>>
      intLib.ARITH_TAC)>>
    pop_assum mp_tac>>
    Cases_on`check_obj obj x' fmlls NONE`>>
    simp[opt_le_def,opt_lt_def]>>
    drule check_obj_imp>>
    strip_tac>>
    gvs[all_core_core_only_fml_eq]>>
    rw[]>>asm_exists_tac>>simp[])
QED

(* Every constraint in fml' is in fml *)
Definition fml_include_def:
  fml_include fml fml' =
  EVERY (λc. MEM c fml) fml'
End

Theorem fml_include_satisfies:
  fml_include fml fml' ∧
  satisfies w (set fml) ⇒
  satisfies w (set fml')
Proof
  rw[fml_include_def,EVERY_MEM,satisfies_def]
QED

Definition opt_eq_obj_def:
  (opt_eq_obj (SOME fc) (SOME fc') ⇔ eq_obj fc fc') ∧
  (opt_eq_obj _ _ = F)
End

Definition opt_eq_pres_def:
  (opt_eq_pres (SOME pres) (SOME pres') ⇔ pres = pres') ∧
  (opt_eq_pres _ _ = F)
End

Definition opt_eq_obj_opt_def:
  (opt_eq_obj_opt (SOME fc) (SOME fc') ⇔ eq_obj fc fc') ∧
  (opt_eq_obj_opt NONE NONE = T) ∧
  (opt_eq_obj_opt _ _ = F)
End

Definition check_output_def:
  (check_output fml (pres:num_set option) obj bound dbound chk
    fml' (pres':num_set option) obj' NoOutput = T) ∧
  (check_output fml pres obj bound dbound chk
    fml' pres' obj' Derivable =
    let cls =
      (MAP SND (toAList (mk_core_fml T fml))) in
      dbound = NONE ∧ fml_include cls fml') ∧
  (check_output fml pres obj bound dbound chk
    fml' pres' obj' Equisatisfiable =
    let cls =
      (MAP SND (toAList (mk_core_fml T fml))) in
      dbound = NONE ∧ bound = NONE ∧
      chk ∧
      fml_include cls fml' ∧
      fml_include fml' cls) ∧
  (check_output fml pres obj bound dbound chk
    fml' pres' obj' Equioptimal =
    let cls =
      (MAP SND (toAList (mk_core_fml T fml))) in
      chk ∧ opt_le bound dbound ∧
      fml_include cls fml' ∧
      fml_include fml' cls ∧
      opt_eq_obj obj obj') ∧
  (check_output fml pres obj bound dbound chk
    fml' pres' obj' Equisolvable =
    let cls =
      (MAP SND (toAList (mk_core_fml T fml))) in
      chk ∧ opt_le bound dbound ∧
      fml_include cls fml' ∧
      fml_include fml' cls ∧
      opt_eq_obj_opt obj obj' ∧
      opt_eq_pres pres pres')
End

Theorem valid_conf_proj_pres_eq:
  valid_conf T pres ord obj tcb fml ⇒
  proj_pres (pres_set_spt pres)
    {w | satisfies w (core_only_fml T fml) ∧ eval_obj obj w ≤ v} =
  proj_pres (pres_set_spt pres)
    {w | satisfies w (core_only_fml F fml) ∧ eval_obj obj w ≤ v}
Proof
  rw[valid_conf_def,valid_req_def,sat_obj_po_def,pbcTheory.proj_pres_def,EXTENSION,EQ_IMP_THM,pres_set_spt_def]
  >- (
    first_x_assum drule>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    metis_tac[integerTheory.INT_LE_TRANS,IN_DEF])
  >- (
    `satisfies w (core_only_fml T fml)` by
      metis_tac[satisfies_SUBSET,core_only_fml_T_SUBSET_F]>>
    metis_tac[integerTheory.INT_LE_TRANS])
QED

Theorem BIJ_INJ_INJ:
  INJ f s t ∧ INJ g t s ⇒
  ∃h. BIJ h s t
Proof
  Cases_on`t = {}`
  >-
    rw[INJ_DEF]>>
  rw[]>>irule_at Any BIJ_INJ_SURJ>>
  drule inj_surj>>rw[]>>
  metis_tac[]
QED

Theorem check_csteps_check_output:
  id_ok fml id ∧
  check_csteps csteps
    fml (init_conf id chk pres obj) = SOME (fml',pc') ∧
  all_core fml ∧
  check_output fml' pc'.pres pc'.obj pc'.bound pc'.dbound pc'.chk fmlt prest objt output ⇒
  sem_output
    (core_only_fml T fml) obj
      (pres_set_spt pres) pc'.bound
    (set fmlt) objt
      (pres_set_spt prest) output
Proof
  rw[]>>
  drule_at Any check_csteps_correct>>
  DEP_ONCE_REWRITE_TAC[all_core_valid_conf]>>
  simp[init_conf_def]>>
  rw[hide_def]>>
  Cases_on`output`>>
  fs[sem_output_def,check_output_def]
  >- ( (* Derivable *)
    rw[satisfiable_def]>>
    drule fml_include_satisfies>>
    disch_then (irule_at Any)>>
    drule all_core_core_only_fml_eq>>rw[]>>
    imp_res_tac bimp_pres_obj_bimp_obj>>
    gvs[bimp_obj_def,opt_lt_def,imp_obj_def,sat_obj_le_def,PULL_EXISTS]>>
    first_x_assum drule>>
    disch_then(qspec_then`eval_obj obj w` assume_tac)>>fs[]>>
    simp[GSYM range_toAList,range_mk_core_fml]>>
    fs[range_def,core_only_fml_def,satisfies_def]>>
    metis_tac[])
  >- (  (* Equisatisfiable *)
    eq_tac>>rw[satisfiable_def]
    >- (
      imp_res_tac bimp_pres_obj_bimp_obj>>
      qpat_x_assum`fml_include _ fmlt` assume_tac>>
      drule fml_include_satisfies>>
      disch_then (irule_at Any)>>
      drule all_core_core_only_fml_eq>>rw[]>>
      gvs[bimp_obj_def,opt_lt_def,imp_obj_def,sat_obj_le_def,PULL_EXISTS]>>
      first_x_assum drule>>
      disch_then(qspec_then`eval_obj obj w` assume_tac)>>fs[]>>
      simp[GSYM range_toAList,range_mk_core_fml]>>
      fs[range_def,core_only_fml_def,satisfies_def]>>
      metis_tac[])>>
    drule_all fml_include_satisfies>>
    simp[GSYM range_toAList,range_mk_core_fml]>>
    gvs[]>>
    imp_res_tac bimp_pres_obj_bimp_obj>>
    gvs[bimp_obj_def,opt_lt_def,imp_obj_def,sat_obj_le_def,PULL_EXISTS]>>
    strip_tac>>first_x_assum drule>>
    disch_then(qspec_then`eval_obj pc'.obj w` assume_tac)>>fs[]>>
    metis_tac[])
  >- (  (* Equioptimal *)
    rw[]>>
    `∀w. eval_obj pc'.obj w = eval_obj objt w` by
      (Cases_on`pc'.obj`>>Cases_on`objt`>>
      gvs[opt_eq_obj_def]>>
      drule eq_obj_eval_obj>>
      simp[])>>
    drule all_core_core_only_fml_eq>>rw[]>>
    `opt_lt (SOME v) pc'.bound` by
      (Cases_on`pc'.bound`>>fs[opt_lt_def])>>
    eq_tac>>rw[]
    >- (
      imp_res_tac bimp_pres_obj_bimp_obj>>
      gvs[bimp_obj_def,opt_lt_def,imp_obj_def,sat_obj_le_def,PULL_EXISTS]>>
      `opt_le (SOME (eval_obj obj w)) (SOME v)` by
        (simp[opt_le_def,opt_lt_def]>>
        metis_tac[integerTheory.INT_LE_LT])>>
      `opt_lt (SOME (eval_obj obj w)) pc'.dbound` by
        metis_tac[opt_lt_le]>>
      last_x_assum drule>>
      disch_then drule>>rw[]>>
      qexists_tac`w'`>>
      reverse CONJ_TAC >-
        metis_tac[integerTheory.INT_LE_TRANS]>>
      qpat_x_assum`fml_include _ fmlt` assume_tac>>
      drule fml_include_satisfies>>
      disch_then (irule_at Any)>>
      simp[GSYM range_toAList,range_mk_core_fml]>>
      fs[range_def,core_only_fml_def,satisfies_def]>>
      metis_tac[])>>
    drule_all fml_include_satisfies>>
    simp[GSYM range_toAList,range_mk_core_fml]>>
    gvs[]>>
    imp_res_tac bimp_pres_obj_bimp_obj>>
    gvs[bimp_obj_def,opt_lt_def,imp_obj_def,sat_obj_le_def,PULL_EXISTS]>>
    strip_tac>>first_x_assum drule_all>>
    metis_tac[])
  >- ( (* Equisolvable *)
    rw[]>>
    `∀w. eval_obj pc'.obj w = eval_obj objt w` by (
      Cases_on`pc'.obj`>>Cases_on`objt`>>
      gvs[opt_eq_obj_opt_def]>>
      drule eq_obj_eval_obj>>
      simp[])>>
    drule all_core_core_only_fml_eq>>rw[]>>
    `opt_lt (SOME v) pc'.bound` by
      (Cases_on`pc'.bound`>>fs[opt_lt_def])>>
    `opt_lt (SOME v) pc'.dbound` by
       metis_tac[opt_lt_le]>>
    `proj_pres (pres_set_spt pc'.pres)
      {w | satisfies w (core_only_fml T fml') ∧ eval_obj objt w ≤ v} =
     proj_pres (pres_set_spt pc'.pres)
      {w' | satisfies w' (set fmlt) ∧ eval_obj objt w' ≤ v}`
      by (
      pop_assum kall_tac>>
      simp[EXTENSION]>>
      gvs[pbcTheory.proj_pres_def]>>
      rw[EQ_IMP_THM]
      >- (
        irule_at Any (GEN_ALL fml_include_satisfies)>>
        first_x_assum (irule_at Any)>>
        first_x_assum (irule_at Any)>> simp[]>>
        simp[GSYM range_toAList,range_mk_core_fml])>>
      drule_all fml_include_satisfies>>
      simp[GSYM range_toAList,range_mk_core_fml]>>
      rw[]>>
      metis_tac[])>>
    gvs[]>>
    imp_res_tac bimp_pres_obj_bimp_obj>>
    gvs[bimp_pres_obj_def]>>
    rpt(first_x_assum drule)>>
    rw[]>>
    drule valid_conf_proj_pres_eq>>rw[]>>
    `pres_set_spt pc'.pres = pres_set_spt prest` by
      (Cases_on`pc'.pres`>>
      Cases_on`prest`>>
      gvs[opt_eq_pres_def])>>
    metis_tac[BIJ_INJ_INJ])
QED

(* EXPERIMENTAL UNUSED
Definition spt_of_list_def:
  spt_of_list c = add_spt (LN,0) c
End

Definition spt_of_lit_def:
  (spt_of_lit (Pos v) = add_spt (LN,0) ([(1,v)],0)) ∧
  (spt_of_lit (Neg v) = add_spt (LN,0) ([(-1,v)],0))
End

Definition check_cutting_spt_def:
  (check_cutting_spt fml (Id n) =
    OPTION_MAP spt_of_list (lookup n fml)) ∧
  (check_cutting_spt fml (Add c1 c2) =
    OPTION_MAP2
      add_spt
      (check_cutting_spt fml c1)
      (check_cutting fml c2)) ∧
  (check_cutting_spt fml (Mul c k) =
       OPTION_MAP (λc. multiply_spt c k)
        (check_cutting_spt fml c)) ∧
  (check_cutting_spt fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide_spt c k) (check_cutting_spt fml c)
    else NONE) ∧
  (check_cutting_spt fml (Sat c) =
    OPTION_MAP saturate_spt (check_cutting_spt fml c)) ∧
  (check_cutting_spt fml (Weak c var) =
    OPTION_MAP (λc. weaken_spt c var) (check_cutting_spt fml c)) ∧
  (check_cutting_spt fml (Lit l) = SOME (spt_of_lit l))
End

Definition constraint_of_spt_def:
  constraint_of_spt (t,n) =
  let ls = toSortedAList t in
    (MAP (λ(v,c). (c,v)) ls,n)
End
*)

val _ = export_theory ();
