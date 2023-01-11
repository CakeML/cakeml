(*
  Formalisation of a syntax and semantics for MILP
*)
open preamble RatProgTheory sptree_unionWithTheory;

val _ = new_theory "milp";

val _ = numLib.prefer_num();

(* x |-> r *)
Type lin_term = ``: real num_map``;

Definition eval_real_term_def:
  eval_real_term w (x,r:real) = (r * w x):real
End

Definition rSUM_def:
  (rSUM [] = 0:real) ∧
  (rSUM (x::xs) = x + rSUM xs)
End

Definition eval_lhs_def:
  eval_lhs w lhs =
    let xs = toAList lhs in
    rSUM (MAP (eval_real_term w) xs)
End

(*
  Constraints have the form:
  c_i l_i ≥ n
  c_i l_i = n
  c_i l_i ≤ n
*)
Datatype:
  linop = Equal | GreaterEqual | LessEqual
End

(* A linear constraint *)
Type milc = ``:(linop # lin_term # real)``

Definition do_op_def[simp]:
  (do_op Equal (l:real) (r:real) ⇔ l = r) ∧
  (do_op GreaterEqual l r ⇔ l ≥ r) ∧
  (do_op LessEqual l r ⇔ l ≤ r)
End

(* satisfaction of a mixed integer linear constraint *)
Definition satisfies_milc_def:
  (satisfies_milc w (lop,lhs,n) ⇔
    do_op lop (eval_lhs w lhs) n)
End

(* satisfaction of an MILP *)
Definition satisfies_def:
  satisfies w intv milp ⇔
  (∀v. v ∈ intv ⇒ is_int (w v)) ∧
  (∀c. c ∈ milp ⇒ satisfies_milc w c)
End

Datatype:
  result = Infeasible | Range (real option) (real option)
End

(* The assignment w gives an optimal value for min/max problem *)
Definition optimal_def:
  (optimal intv milp min obj w ⇔
  satisfies w intv milp ∧
  ∀w'.
    satisfies w' intv milp ⇒
    (min ⇒ eval_lhs w obj ≤ eval_lhs w' obj) ∧
    (¬min ⇒ eval_lhs w' obj ≤ eval_lhs w obj)
  )
End

(*
  intv: set of integer variables
  milp: the MILP constraints
  min: boolean flag, true to minimize obj (or maximize if false)
  obj: objective linear term
*)
Definition rtp_def:
  (rtp intv milp min obj Infeasible ⇔
    ∀w. ¬satisfies w intv milp) ∧
  (rtp intv milp min obj (Range lb ub) ⇔
    (* Satisfiable *)
    (∃w. satisfies w intv milp) ∧
    ∀w. optimal intv milp min obj w ⇒
      (case lb of NONE => T | SOME lb => lb ≤ eval_lhs w obj) ∧
      (case ub of NONE => T | SOME ub => eval_lhs w obj ≤ ub))
End

(* Implication constraints *)
Definition satisfies_imp_milc_def:
  satisfies_imp_milc w assms milc ⇔
  ((∀c. c ∈ assms ⇒ satisfies_milc w c) ⇒ satisfies_milc w milc)
End

Definition satisfies_imp_milp_def:
  satisfies_imp_milp w imilp ⇔
  ∀i c. (i,c) ∈ imilp ⇒ satisfies_imp_milc w i c
End

(* Syntactic stuff *)

(* check a partial solution *)
Definition check_dom_def:
  check_dom (intv:num_set) (sol:real num_map) ⇔
  let ls = toAList sol in
  EVERY (λ(k,v). lookup k intv = SOME () ⇒ is_int v) ls
End

Definition mk_sol_def:
  mk_sol sol x =
  case lookup x sol of NONE => 0 | SOME r => (r:real)
End

Definition check_milp_def:
  check_milp milp sol =
  let solc = mk_sol sol in
  EVERY (satisfies_milc solc) milp
End

Definition check_obj_def:
  check_obj obj r sol =
  let solc = mk_sol sol in
  eval_lhs solc obj = r
End

Definition check_sol_def:
  check_sol intv milp obj r (sol: real num_map) ⇔
  check_dom intv sol ∧
  check_milp milp sol ∧
  check_obj obj r sol
End

(* Syntactic formulae are given by a sptree of implication
  constraints with type (milc list, milc)
  TODO: add support for deletion *)
Datatype:
  vipr = Assum milc
  | Lin milc ((num,real) alist)
  | Round milc ((num,real) alist)
End

(* Check that a given LHS is int valued *)
Definition int_valued_def:
  int_valued intv lhs ⇔
  let xs = toAList lhs in
  EVERY (λ(x,r). IS_SOME (lookup x intv) ∧ is_int r) xs
End

Definition round_milc_def:
  round_milc intv (lop,lhs,n) =
  if int_valued intv lhs then
    case lop of
      GreaterEqual => SOME (lop,lhs,real_of_int (INT_CEILING n))
    | LessEqual => SOME (lop,lhs,real_of_int (INT_FLOOR n))
    | _ => NONE
  else NONE
End

Definition absurdity_def:
  absurdity ((lop,xs,n):milc) ⇔
  xs = LN ∧
  case lop of
    GreaterEqual => n > 0
  | LessEqual => n < 0
  | Equal => n ≠ 0
End

Theorem absurdity_unsat:
  absurdity milc ⇒
  ¬satisfies_milc w milc
Proof
  PairCases_on`milc`>>
  simp[absurdity_def,satisfies_milc_def,eval_lhs_def]>>
  EVAL_TAC>>
  every_case_tac>>fs[do_op_def,realaxTheory.real_ge]>>
  PURE_REWRITE_TAC[realaxTheory.REAL_NOT_LE]>>
  fs[realaxTheory.real_gt]
QED

(* c1 dominates c2 *)
Definition dominates_def:
  dominates (lop1,xs1,n1) (lop2,xs2,n2) ⇔
  absurdity (lop1,xs1,n1) ∨
  xs1 = xs2 ∧
  case lop2 of
    GreaterEqual =>
    (lop1 = GreaterEqual ∨ lop1 = Equal) ∧ n1 ≥ n2
  | LessEqual =>
    (lop1 = LessEqual ∨ lop1 = Equal) ∧ n1 ≤ n2
  | Equal =>
    lop1 = Equal ∧ n1 = n2
End

Theorem dominates_imp:
  dominates milc1 milc2 ∧
  satisfies_milc w milc1 ⇒
  satisfies_milc w milc2
Proof
  PairCases_on`milc1`>>
  PairCases_on`milc2`>>
  rw[dominates_def]
  >-
    metis_tac[absurdity_unsat]>>
  every_case_tac>>fs[satisfies_milc_def]>>rw[]>>
  fs[do_op_def]>>
  metis_tac[realTheory.REAL_LE_TRANS,realaxTheory.real_ge]
QED

Definition add_r_def:
  add_r r v v' =
  let s = v + r *v in if s = 0:real then NONE else SOME s
End

Definition add_def:
  add (lhs,n) (r:real) (lhs',n') =
  (unionWith (add_r r) lhs lhs', n + r * n')
End

Definition slop_def:
  (slop Equal = 0:real) ∧
  (slop GreaterEqual = 1) ∧
  (slop LessEqual = -1)
End

Definition compat_def:
  (compat GreaterEqual lop r ⇔ r * slop lop ≥ 0) ∧
  (compat Equal lop r ⇔ r * slop lop = 0) ∧
  (compat LessEqual lop r ⇔ r * slop lop ≤ 0)
End

(* NOTE: This currently adds back to front.
  The linear combination must be compatible with the final lop *)
Definition lin_comb_def:
  (lin_comb lop [] = SOME (LN,0)) ∧
  (lin_comb lop (((lop',c),r)::xs) =
    case lin_comb lop xs of
    NONE => NONE
  | SOME ys =>
    if compat lop lop' r then
      SOME (add ys r c)
    else NONE
  )
End

(* TODO seems nasty, maybe avoid toAList *)
Theorem eval_lhs_unionWith:
  eval_lhs w
  (unionWith (add_r r) lhs lhs') =
  eval_lhs w lhs + r * eval_lhs w lhs'
Proof
  rw[eval_lhs_def]>>
  cheat
QED

Theorem mul_neg_le[simp]:
  (r * -1 ≤ 0:real ⇔ 0 ≤ r) ∧
  (0 ≤ r * -1 ⇔ r ≤ 0)
Proof
  simp[realTheory.REAL_MUL_SIGN]
QED

Theorem compat_add_sound:
  satisfies_milc w (lop,x) ∧
  satisfies_milc w (lop',y) ∧
  compat lop lop' r ⇒
  satisfies_milc w (lop,add x r y)
Proof
  Cases_on`lop`>>Cases_on`lop'`>>
  Cases_on`x`>>Cases_on`y`>>rw[]>>
  fs[compat_def,satisfies_milc_def,slop_def,add_def]>>
  fs[eval_lhs_unionWith,realaxTheory.real_ge]>>
  metis_tac[realTheory.REAL_LE_LMUL1,realTheory.REAL_LE_ADD2,realTheory.REAL_LE_LMUL_NEG_IMP]
QED

Theorem lin_comb_sound:
  ∀xs ys.
  lin_comb lop xs = SOME ys ∧
  EVERY (satisfies_milc w) (MAP FST xs) ⇒
  satisfies_milc w (lop,ys)
Proof
  Induct>>rw[lin_comb_def]
  >- (
    Cases_on`lop`>>rw[satisfies_milc_def]>>
    EVAL_TAC>>
    simp[realTheory.REAL_LE_REFL,realaxTheory.real_ge])>>
  PairCases_on`h`>>
  fs[lin_comb_def]>>
  every_case_tac>>fs[]>>
  metis_tac[compat_add_sound]
QED

(* TODO: change to accumulator and union assms instead *)
Definition lookup_all_lhs_def:
  (lookup_all_lhs fml [] = SOME ([],[])) ∧
  (lookup_all_lhs fml ((i,r)::xs) =
  case lookup_all_lhs fml xs of NONE => NONE
  | SOME (assms,ys) =>
    case lookup i fml of NONE => NONE
    | SOME (assm,y) => SOME (assm ++ assms,(y,r)::ys))
End

Definition do_lin_def:
  do_lin fml lop lhs =
  case lookup_all_lhs fml lhs of NONE => NONE
  | SOME (assms,xs) =>
    case lin_comb lop xs of NONE => NONE
    | SOME res => SOME (assms,(lop,res))
End

Definition check_vipr_def:
  (check_vipr intv fml id (Assum milc) =
    SOME (insert id ([id],milc) fml, id+1)) ∧
  (check_vipr intv fml id (Lin milc lhs) =
    case do_lin fml (FST milc) lhs of NONE => NONE
    | SOME res =>
      SOME (insert id res fml, id+1)) ∧
  (check_vipr intv fml id (Round milc lhs) =
    case do_lin fml (FST milc) lhs of NONE => NONE
    | SOME (assms,milc) =>
      case round_milc intv milc of NONE => NONE
      | SOME milc' =>
      SOME (insert id (assms,milc') fml, id+1))
End

Theorem is_int_add_mul:
  is_int x ∧ is_int y ⇒
  is_int (x + y) ∧
  is_int (x * y)
Proof
  fs[intrealTheory.is_int_def]>>
  rw[]>>
  qpat_x_assum`_ = _` SUBST_ALL_TAC>>
  qpat_x_assum`_ = _` SUBST_ALL_TAC>>
  simp[intrealTheory.INT_FLOOR_SUM]>>
  simp[INT_FLOOR_real_of_int]>>
  simp[realTheory.REAL_ADD_COMM]>>
  REWRITE_TAC[GSYM intrealTheory.real_of_int_mul]>>
  simp[intrealTheory.INT_FLOOR]
QED

Theorem int_valued_is_int:
  (∀v. v ∈ domain intv ⇒ is_int (w v)) ∧
  int_valued intv milc
  ⇒
  is_int (eval_lhs w milc)
Proof
  rw[int_valued_def,eval_lhs_def]>>
  rename1`is_int (rSUM (MAP _ ls))`>>
  Induct_on`ls`>>fs[rSUM_def]
  >-
    EVAL_TAC>>
  rw[]>>fs[]>>
  Cases_on`h`>>
  fs[eval_real_term_def,domain_lookup,IS_SOME_EXISTS,PULL_EXISTS]>>
  first_x_assum drule>>
  rw[]>>
  metis_tac[is_int_add_mul]
QED

Theorem le_real_of_int:
  r ≤ real_of_int i ⇒
  INT_CEILING r ≤ i
Proof
  rw[]>>
  CCONTR_TAC>>fs[integerTheory.INT_NOT_LE]>>
  `real_of_int (INT_CEILING r - 1) < r` by
    metis_tac[intrealTheory.INT_CEILING]>>
  `real_of_int (⌈r⌉ − 1) < real_of_int i` by
    metis_tac[realaxTheory.REAL_LTE_TRANS]>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem round_up:
  is_int r ∧
  r ≥ f ⇒ r ≥ real_of_int (INT_CEILING f)
Proof
  rw[]>>
  fs[intrealTheory.is_int_def]>>
  fs[realaxTheory.real_ge]>>
  `INT_CEILING f ≤ INT_FLOOR r` by metis_tac[le_real_of_int]>>
  `real_of_int (INT_FLOOR r) ≤ r` by
    metis_tac[intrealTheory.INT_FLOOR_BOUNDS]>>
  metis_tac[intrealTheory.real_of_int_le,realaxTheory.REAL_LE_TRANS]
QED

Theorem real_of_int_le:
  real_of_int i ≤ r ⇒
  i ≤ INT_FLOOR r
Proof
  rw[]>>
  CCONTR_TAC>>
  fs[integerTheory.INT_NOT_LE]>>
  `r < real_of_int (INT_FLOOR r + 1)` by
    metis_tac[intrealTheory.INT_FLOOR]>>
  `real_of_int i < real_of_int (INT_FLOOR r + 1)` by
    metis_tac[realaxTheory.REAL_LET_TRANS]>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem round_down:
  is_int r ∧
  r ≤ f ⇒ r ≤ real_of_int (INT_FLOOR f)
Proof
  rw[]>>
  fs[intrealTheory.is_int_def]>>
  `INT_FLOOR r ≤ INT_FLOOR f` by metis_tac[real_of_int_le]>>
  metis_tac[intrealTheory.real_of_int_le,realaxTheory.REAL_LE_TRANS]
QED

Theorem round_milc_sound:
  (∀v. v ∈ domain intv ⇒ is_int (w v)) ∧
  satisfies_milc w milc ∧
  round_milc intv milc = SOME milc'
  ⇒
  satisfies_milc w milc'
Proof
  PairCases_on`milc`>>fs[round_milc_def]>>
  TOP_CASE_TAC>>rw[]>>
  fs[satisfies_milc_def]
  >- (
    match_mp_tac round_up>>
    fs[]>>
    metis_tac[int_valued_is_int])>>
  match_mp_tac round_down>>
  fs[]>>
  metis_tac[int_valued_is_int]
QED

(* Lookup the assumptions corresponding to the list of indices *)
Definition get_assms_def:
  get_assms (fml: (num list # milc) num_map) (ls,c) =
  (set (MAP (λid. SND (THE (lookup id fml))) ls),c)
End

Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End

Theorem range_delete:
  range (delete h v) ⊆ range v
Proof
  simp[range_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem range_insert:
  n ∉ domain fml ⇒
  range (insert n l fml) = l INSERT range fml
Proof
  rw[range_def,EXTENSION,lookup_insert,domain_lookup]>>
  metis_tac[SOME_11]
QED

Theorem range_insert_2:
  C ∈ range (insert n l fml) ⇒ C ∈ range fml ∨ C = l
Proof
  fs[range_def,lookup_insert]>>
  rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem range_insert_SUBSET:
  range (insert n l fml) ⊆ l INSERT range fml
Proof
  rw[SUBSET_DEF]>>
  metis_tac[range_insert_2]
QED

(* The only allowed assumptions must be "self-loops" *)
Definition is_assm_def:
  is_assm fml id ⇔
  case lookup id fml of
    NONE => F
  | SOME (assms,c) => assms = [id]
End

Definition good_fml_def:
  good_fml fml ⇔
  ∀asmc.
    asmc ∈ range fml ⇒
    EVERY (is_assm fml) (FST asmc)
End

Definition id_ok_def:
  id_ok fml id ⇔
  ∀n. id ≤ n ⇒ n ∉ domain fml
End

Theorem satisfies_imp_milp_insert:
  satisfies_imp_milp w
  (IMAGE (get_assms fml) (range fml)) ∧
  id_ok fml id ∧
  good_fml fml ∧
  ((∀id'.
  MEM id' (FST x) ⇒
  satisfies_milc w (SND (THE (lookup id' (insert id x fml))))) ⇒
  satisfies_milc w (SND x))
  ⇒
  satisfies_imp_milp w
  (IMAGE (get_assms (insert id x fml)) (range (insert id x fml)))
Proof
  fs[satisfies_imp_milp_def,id_ok_def,PULL_EXISTS]>>
  rw[]>>
  rename1`y ∈ _`>>
  Cases_on`y`>>fs[get_assms_def]>>rw[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [range_insert]>>
  fs[]>>rw[]
  >-
    (fs[satisfies_imp_milc_def,MEM_MAP,PULL_EXISTS])
  >- (
    first_x_assum (drule_at Any)>>
    simp[get_assms_def]>>rw[]>>
    fs[satisfies_imp_milc_def,MEM_MAP,lookup_insert,PULL_EXISTS]>>
    rw[]>>
    first_x_assum match_mp_tac>>
    rw[]>>
    fs[good_fml_def]>>
    first_x_assum drule>>rw[]>>
    first_x_assum drule>>
    fs[EVERY_MEM]>>rw[]>>
    first_x_assum drule>>
    fs[is_assm_def]>>
    every_case_tac>>fs[domain_lookup]>>
    last_x_assum(qspec_then`id` assume_tac)>>fs[])
QED

(* check the main body of a VIPR proof *)
Theorem check_vipr_sound:
  check_vipr intv fml id vipr = SOME (fml',id') ∧
  id_ok fml id ∧
  good_fml fml ∧
  (∀v. v ∈ domain intv ⇒ is_int (w v)) ∧
  satisfies_imp_milp w (IMAGE (get_assms fml) (range fml)) ⇒
  satisfies_imp_milp w (IMAGE (get_assms fml') (range fml'))
Proof
  Cases_on`vipr`>>rw[check_vipr_def]
  >- (
    match_mp_tac satisfies_imp_milp_insert>>
    simp[])
  >- (
    every_case_tac>>fs[]>>
    rw[]>>
    match_mp_tac satisfies_imp_milp_insert>>
    rw[]>>
    fs[do_lin_def]>>every_case_tac>>fs[]>>
    rw[]>>
    match_mp_tac lin_comb_sound>>
    asm_exists_tac>>fs[]>>
    (* TODO: prove stuff about combining implications *)
    cheat)
  >- (
    every_case_tac>>fs[]>>
    rw[]>>
    cheat)
QED

val _ = export_theory();
