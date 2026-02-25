(*
  Add individual upper and lower bounds for each number variable
*)
Theory numBoolRange
Ancestors
  misc cnf boolExpToCnf numBoolExp numBoolExtended
Libs
  preamble


(* ----------------- Datatypes ----------------------------- *)

Datatype:
  numBoolRange =
  | RTrue
  | RFalse
  | RBoolVar num
  | RNot numBoolRange
  | RAnd numBoolRange numBoolRange
  | ROr numBoolRange numBoolRange
  | RImpl numBoolRange numBoolRange
  | RIff numBoolRange numBoolRange
  | RAdd numVar numVar numVar   (* x + y = z *)
  | REq numVar numVar           (* x = y *)
  | RNeq numVar numVar          (* x ≠ y *)
  | RLt numVar numVar           (* x < y *)
  | RLeq numVar numVar          (* x ≤ y *)
  | RGt numVar numVar           (* x > y *)
  | RGeq numVar numVar          (* x ≥ y *)
  | REqConst numVar num         (* x = n *)
  | RNeqConst numVar num        (* x ≠ n *)
  | RLtConst numVar num         (* x < n *)
  | RLeqConst numVar num        (* x ≤ n *)
  | RGtConst numVar num         (* x > n *)
  | RGeqConst numVar num        (* x ≥ n *)
  | RConstEq num numVar         (* n = x *)
  | RConstNeq num numVar        (* n ≠ x *)
  | RConstLt num numVar         (* n < x *)
  | RConstLeq num numVar        (* n ≤ x *)
  | RConstGt num numVar         (* n > x *)
  | RConstGeq num numVar        (* n ≥ x *)
End

(* (x, (min, max)) ⇒ x ∈ [min, max] *)
Type rangeList = “: (numVar # (num # num)) list”;


(* ----------------- Well formed ----------------------------- *)

Definition rangeList_ok_def:
  rangeList_ok (l:rangeList) =
  ALL_DISTINCT (MAP FST l)
End

Definition exp_rangeList_ok_def:
  exp_rangeList_ok (l:rangeList) RTrue = T ∧
  exp_rangeList_ok l RFalse = T ∧
  exp_rangeList_ok l (RBoolVar b) = T ∧
  exp_rangeList_ok l (RNot e) = exp_rangeList_ok l e ∧
  exp_rangeList_ok l (RAnd e1 e2) =
  (exp_rangeList_ok l e1 ∧ exp_rangeList_ok l e2) ∧
  exp_rangeList_ok l (ROr e1 e2) =
  (exp_rangeList_ok l e1 ∧ exp_rangeList_ok l e2) ∧
  exp_rangeList_ok l (RImpl e1 e2) =
  (exp_rangeList_ok l e1 ∧ exp_rangeList_ok l e2) ∧
  exp_rangeList_ok l (RIff e1 e2) =
  (exp_rangeList_ok l e1 ∧ exp_rangeList_ok l e2) ∧
  exp_rangeList_ok l (RAdd x y z) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l) ∧ MEM z (MAP FST l)) ∧
  exp_rangeList_ok l (REq x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (RNeq x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (RLt x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (RLeq x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (RGt x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (RGeq x y) =
  (MEM x (MAP FST l) ∧ MEM y (MAP FST l)) ∧
  exp_rangeList_ok l (REqConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RNeqConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RLtConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RLeqConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RGtConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RGeqConst x n) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstEq n x) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstNeq n x) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstLt n x) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstLeq n x) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstGt n x) = MEM x (MAP FST l) ∧
  exp_rangeList_ok l (RConstGeq n x) = MEM x (MAP FST l)
End

Definition numVarAssignment_range_ok_def:
  numVarAssignment_range_ok (w':numVarAssignment) (l:rangeList) =
  EVERY (λ (x, (min, max)). min ≤ w' x ∧ w' x ≤ max) l
End

(* ----------------- Getting varList ----------------------------- *)

Definition get_first_non_boolVar_num_def:
  get_first_non_boolVar_num RTrue = 1 ∧
  get_first_non_boolVar_num RFalse = 1 ∧
  get_first_non_boolVar_num (RBoolVar b) = b + 1 ∧
  get_first_non_boolVar_num (RNot e) = get_first_non_boolVar_num e ∧
  get_first_non_boolVar_num (RAnd e1 e2) =
  MAX (get_first_non_boolVar_num e1) (get_first_non_boolVar_num e2) ∧
  get_first_non_boolVar_num (ROr e1 e2) =
  MAX (get_first_non_boolVar_num e1) (get_first_non_boolVar_num e2) ∧
  get_first_non_boolVar_num (RImpl e1 e2) =
  MAX (get_first_non_boolVar_num e1) (get_first_non_boolVar_num e2) ∧
  get_first_non_boolVar_num (RIff e1 e2) =
  MAX (get_first_non_boolVar_num e1) (get_first_non_boolVar_num e2) ∧
  get_first_non_boolVar_num _ = 1
End

Definition get_boolVar_list_def:
  get_boolVar_list exp =
  let bool_num = get_first_non_boolVar_num exp in
      GENLIST (λx. x + 1) (bool_num - 1)
End


(* ----------------- Evaluation ----------------------------- *)

Definition eval_numBoolRange_def:
  eval_numBoolRange w w' RTrue = T ∧
  eval_numBoolRange w w' RFalse = F ∧
  eval_numBoolRange w w' (RBoolVar b) = w b ∧
  eval_numBoolRange w w' (RNot e) = ¬eval_numBoolRange w w' e ∧
  eval_numBoolRange w w' (RAnd e1 e2) =
  (eval_numBoolRange w w' e1 ∧ eval_numBoolRange w w' e2) ∧
  eval_numBoolRange w w' (ROr e1 e2) =
  (eval_numBoolRange w w' e1 ∨ eval_numBoolRange w w' e2) ∧
  eval_numBoolRange w w' (RImpl e1 e2) =
  (eval_numBoolRange w w' e1 ⇒ eval_numBoolRange w w' e2) ∧
  eval_numBoolRange w w' (RIff e1 e2) =
  (eval_numBoolRange w w' e1 ⇔ eval_numBoolRange w w' e2) ∧
  eval_numBoolRange w w' (RAdd x y z) = (w' x + w' y = w' z) ∧
  eval_numBoolRange w w' (REq x y) = (w' x = w' y) ∧
  eval_numBoolRange w w' (RNeq x y) = (w' x ≠ w' y) ∧
  eval_numBoolRange w w' (RLt x y) = (w' x < w' y) ∧
  eval_numBoolRange w w' (RLeq x y) = (w' x ≤ w' y) ∧
  eval_numBoolRange w w' (RGt x y) = (w' x > w' y) ∧
  eval_numBoolRange w w' (RGeq x y) = (w' x ≥ w' y) ∧
  eval_numBoolRange w w' (REqConst x n) = (w' x = n) ∧
  eval_numBoolRange w w' (RNeqConst x n) = (w' x ≠ n) ∧
  eval_numBoolRange w w' (RLtConst x n) = (w' x < n) ∧
  eval_numBoolRange w w' (RLeqConst x n) = (w' x ≤ n) ∧
  eval_numBoolRange w w' (RGtConst x n) = (w' x > n) ∧
  eval_numBoolRange w w' (RGeqConst x n) = (w' x ≥ n) ∧
  eval_numBoolRange w w' (RConstEq n x) = (n = w' x) ∧
  eval_numBoolRange w w' (RConstNeq n x) = (n ≠ w' x) ∧
  eval_numBoolRange w w' (RConstLt n x) = (n < w' x) ∧
  eval_numBoolRange w w' (RConstLeq n x) = (n ≤ w' x) ∧
  eval_numBoolRange w w' (RConstGt n x) = (n > w' x) ∧
  eval_numBoolRange w w' (RConstGeq n x) = (n ≥ w' x)
End

Definition within_range_def:
  within_range l (w':num->num) =
    ∀v m n. MEM (v,m,n) l ⇒ m ≤ w' v ∧ w' v ≤ n
End

Definition unsat_numBoolRange_def:
  unsat_numBoolRange l e =
    ∀w w'. within_range l w' ⇒ ¬eval_numBoolRange w w' e
End

(* ----------------- Encoding ----------------------------- *)

Definition equation_to_numBoolExtended_def:
  equation_to_numBoolExtended RTrue = ETrue ∧
  equation_to_numBoolExtended RFalse = EFalse ∧
  equation_to_numBoolExtended (RBoolVar b) = (EBoolVar b) ∧
  equation_to_numBoolExtended (RNot e) = ENot (equation_to_numBoolExtended e) ∧
  equation_to_numBoolExtended (RAnd e1 e2) =
  EAnd (equation_to_numBoolExtended e1) (equation_to_numBoolExtended e2) ∧
  equation_to_numBoolExtended (ROr e1 e2) =
  EOr (equation_to_numBoolExtended e1) (equation_to_numBoolExtended e2) ∧
  equation_to_numBoolExtended (RImpl e1 e2) =
  EImpl (equation_to_numBoolExtended e1) (equation_to_numBoolExtended e2) ∧
  equation_to_numBoolExtended (RIff e1 e2) =
  EIff (equation_to_numBoolExtended e1) (equation_to_numBoolExtended e2) ∧
  equation_to_numBoolExtended (RAdd x y z) = EAdd x y z ∧
  equation_to_numBoolExtended (REq x y) = EEq x y ∧
  equation_to_numBoolExtended (RNeq x y) = ENeq x y ∧
  equation_to_numBoolExtended (RLt x y) = ELt x y ∧
  equation_to_numBoolExtended (RLeq x y) = ELeq x y ∧
  equation_to_numBoolExtended (RGt x y) = EGt x y ∧
  equation_to_numBoolExtended (RGeq x y) = EGeq x y ∧
  equation_to_numBoolExtended (REqConst x n) = EEqConst x n ∧
  equation_to_numBoolExtended (RNeqConst x n) = ENeqConst x n ∧
  equation_to_numBoolExtended (RLtConst x n) = ELtConst x n ∧
  equation_to_numBoolExtended (RLeqConst x n) = ELeqConst x n ∧
  equation_to_numBoolExtended (RGtConst x n) = EGtConst x n ∧
  equation_to_numBoolExtended (RGeqConst x n) = EGeqConst x n ∧
  equation_to_numBoolExtended (RConstEq n x) = EConstEq n x ∧
  equation_to_numBoolExtended (RConstNeq n x) = EConstNeq n x ∧
  equation_to_numBoolExtended (RConstLt n x) = EConstLt n x ∧
  equation_to_numBoolExtended (RConstLeq n x) = EConstLeq n x ∧
  equation_to_numBoolExtended (RConstGt n x) = EConstGt n x ∧
  equation_to_numBoolExtended (RConstGeq n x) = EConstGeq n x
End

Definition ranges_to_numBoolExtended_def:
  ranges_to_numBoolExtended [] = ETrue ∧
  ranges_to_numBoolExtended ((x, (min, max))::l) =
  EAnd
  (EAnd (EConstLeq min x) (ELeqConst x max))
  (ranges_to_numBoolExtended l)
End

Definition numBoolRange_to_numBoolExtended_def:
  numBoolRange_to_numBoolExtended (l:rangeList) e =
  EAnd (equation_to_numBoolExtended e) (ranges_to_numBoolExtended l)
End

Definition get_highest_max_def:
  get_highest_max [] = 0 ∧
  get_highest_max ((x, (min, max))::l) = MAX max (get_highest_max l)
End

Definition rangeList_to_numVarList_def:
  rangeList_to_numVarList (l:rangeList) =
  (MAP FST l, get_highest_max l)
End

Definition numBoolRange_to_cnf_def:
  numBoolRange_to_cnf (l:rangeList) e =
  numBoolExtended_to_cnf
  (rangeList_to_numVarList l)
  (numBoolRange_to_numBoolExtended l e)
End

Definition encode_assignment_numBoolRange_def:
  encode_assignment_numBoolRange w w' l e =
  encode_assignment_numBoolExtended
  w w' (rangeList_to_numVarList l) (numBoolRange_to_numBoolExtended l e)
End

Definition assignment_to_numVarAssignment_numBoolRange_def:
  assignment_to_numVarAssignment_numBoolRange w l e =
  assignment_to_numVarAssignment_numBoolExtended
  w (rangeList_to_numVarList l) (numBoolRange_to_numBoolExtended l e)
End


(* ----------------- Theorems ----------------------------- *)

Theorem ranges_encoded_ok:
  ∀ l w w'.
    numVarAssignment_range_ok w' l ⇒
    eval_numBoolExtended w w' (ranges_to_numBoolExtended l)
Proof
  Induct >> rw[ranges_to_numBoolExtended_def, eval_numBoolExtended_def]
  >> Cases_on ‘h’
  >> Cases_on ‘r’
  >> gs[ranges_to_numBoolExtended_def, numVarAssignment_range_ok_def,
        eval_numBoolExtended_def]
QED

Theorem numBoolRange_to_numBoolExtended_preserves_sat:
  ∀ e l w w'.
    rangeList_ok l ∧
    exp_rangeList_ok l e ∧
    numVarAssignment_range_ok w' l ⇒
    (eval_numBoolRange w w' e ⇔
       eval_numBoolExtended w w' (numBoolRange_to_numBoolExtended l e))
Proof
  Induct >> rw[]
  >> (gs[eval_numBoolRange_def, numBoolRange_to_numBoolExtended_def,
         equation_to_numBoolExtended_def, eval_numBoolExtended_def,
         ranges_encoded_ok, exp_rangeList_ok_def]
      >> metis_tac[])
QED

Theorem rangeList_encoded_ok:
  ∀ l.
    rangeList_ok l ⇒
    numVarList_ok (rangeList_to_numVarList l)
Proof
  Induct
  >> rw[rangeList_ok_def, rangeList_to_numVarList_def, numVarList_ok_def]
QED

Theorem all_variables_in_list_ok:
  ∀ l l' k.
    (∀ x. MEM x (MAP FST l) ⇒ MEM x (MAP FST l')) ⇒
    extended_numVarList_ok
    (MAP FST l', k)
    (ranges_to_numBoolExtended l)
Proof
  Induct
  >- rw[ranges_to_numBoolExtended_def, extended_numVarList_ok_def]
  >> Cases_on ‘h’
  >> Cases_on ‘r’
  >> rw[ranges_to_numBoolExtended_def, extended_numVarList_ok_def]
QED

Theorem exp_rangeList_encoded_ok:
  ∀ e l.
    exp_rangeList_ok l e ⇒
    extended_numVarList_ok
    (rangeList_to_numVarList l)
    (numBoolRange_to_numBoolExtended l e)
Proof
  Induct >> rw[]
  >> gs[exp_rangeList_ok_def, numBoolRange_to_numBoolExtended_def,
        equation_to_numBoolExtended_def, rangeList_to_numVarList_def,
        extended_numVarList_ok_def, all_variables_in_list_ok]
QED

Theorem smaller_or_equal_highest:
  ∀ l x min max w'.
    w' x ≤ max ⇒
    w' x ≤ get_highest_max ((x, min, max)::l)
Proof
  Induct >> gs[get_highest_max_def]
QED

Theorem get_highest_mem:
  ∀ l max.
    get_highest_max l = max ⇒
    (∀m. MEM m (MAP (SND o SND) l) ⇒ m ≤ max)
Proof
  Induct >> rw[]
  >- (Cases_on ‘h’ >> gs[]
      >> Cases_on ‘r’ >> gs[]
      >> rw[get_highest_max_def])
  >> Cases_on ‘h’ >> gs[]
  >> Cases_on ‘r’ >> gs[]
  >> rw[get_highest_max_def]
QED

Theorem smaller_than_highest:
  ∀ l x min max w'.
    get_highest_max ((x,min,max)::l) = max ∧
    EVERY (λ(x,min,max). min ≤ w' x ∧ w' x ≤ max) l ⇒
    EVERY (λx. w' x ≤ max) (MAP FST l)
Proof
  Induct >> rw[]
  >- (Cases_on ‘h’ >> gs[]
      >> Cases_on ‘r’ >> gs[]
      >> qspecl_then [‘(x,min,max)::(q,q',r')::l’, ‘max’]
                     assume_tac get_highest_mem
      >> gs[]
      >> first_x_assum (qspecl_then [‘r'’] assume_tac)
      >> gs[])
  >> last_x_assum irule
  >> rw[]
  >> qexists_tac ‘min’
  >> qexists_tac ‘x’
  >> Cases_on‘h’
  >> Cases_on‘r’
  >> gvs[MAX_DEF, get_highest_max_def]
QED

Theorem first_not_highest:
  ∀ l x min max.
    get_highest_max ((x,min,max)::l) ≠ max ⇒
    (get_highest_max ((x,min,max)::l) = get_highest_max l)
Proof
  gvs[MAX_DEF, get_highest_max_def]
QED

Theorem numVarAssignment_encoded_ok:
  ∀ l w'.
    numVarAssignment_range_ok w' l ⇒
    minimal_numVarAssignment_ok w' (rangeList_to_numVarList l)
Proof
  gs[rangeList_to_numVarList_def]
  >> gs[numVarAssignment_range_ok_def]
  >> gs[minimal_numVarAssignment_ok_def]
  >> Induct >> rw[]
  >- (Cases_on ‘h’
      >> Cases_on ‘r’
      >> gs[]
      >> gs[smaller_or_equal_highest])
  >> Cases_on ‘h ’
  >> Cases_on ‘r’
  >> gs[]
  >> Cases_on ‘get_highest_max ((q,q',r')::l) = r'’ >> gs[]
  >- metis_tac[smaller_than_highest]
  >> gs[first_not_highest]
QED

Definition numBoolRange_to_assignment_def:
  numBoolRange_to_assignment w w' l e =
  numBoolExtended_to_assignment
  w w' (rangeList_to_numVarList l) (numBoolRange_to_numBoolExtended l e)
End

Theorem numBoolRange_to_cnf_preserves_sat:
  ∀ e l w w'.
    rangeList_ok l ∧
    exp_rangeList_ok l e ∧
    numVarAssignment_range_ok w' l ⇒
    (eval_numBoolRange w w' e ⇔
       eval_cnf
       (numBoolRange_to_assignment w w' l e)
       (numBoolRange_to_cnf l e))
Proof
  rw[]
  >> imp_res_tac numBoolRange_to_numBoolExtended_preserves_sat >> gs[]
  >> rw[numBoolRange_to_cnf_def, numBoolRange_to_assignment_def]
  >> imp_res_tac rangeList_encoded_ok
  >> imp_res_tac exp_rangeList_encoded_ok
  >> imp_res_tac numVarAssignment_encoded_ok
  >> metis_tac[numBoolExtended_to_cnf_preserves_sat]
QED

Definition to_numRange_assignment_def:
  to_numRange_assignment l e w =
    to_numExtended_assignment (rangeList_to_numVarList l)
      (numBoolRange_to_numBoolExtended l e) w
End

Theorem numBoolRange_to_cnf_imp_sat:
  rangeList_ok l ∧
  exp_rangeList_ok l e ∧
  eval_cnf w (numBoolRange_to_cnf l e) ⇒
  eval_numBoolRange w (to_numRange_assignment l e w) e ∧
  within_range l (to_numRange_assignment l e w)
Proof
  strip_tac
  \\ imp_res_tac rangeList_encoded_ok
  \\ imp_res_tac exp_rangeList_encoded_ok
  \\ fs [numBoolRange_to_cnf_def]
  \\ drule_all numBoolExtended_to_cnf_imp_sat
  \\ fs [to_numRange_assignment_def]
  \\ match_mp_tac (METIS_PROVE [] “(b ⇒ (c = b) ∧ d) ⇒ b ⇒ c ∧ d”)
  \\ strip_tac
  \\ ‘numVarAssignment_range_ok
          (to_numExtended_assignment (rangeList_to_numVarList l)
             (numBoolRange_to_numBoolExtended l e) w) l’ by
   (fs [numBoolRange_to_numBoolExtended_def,
           eval_numBoolExtended_def]
    \\ rename [‘numVarAssignment_range_ok w' _’]
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘l’
    \\ Induct
    \\ fs [numVarAssignment_range_ok_def,FORALL_PROD,
           ranges_to_numBoolExtended_def,eval_numBoolExtended_def])
  \\ conj_tac
  THEN1 (irule numBoolRange_to_numBoolExtended_preserves_sat \\ fs [])
  \\ fs [numVarAssignment_range_ok_def, within_range_def,EVERY_MEM,FORALL_PROD]
  \\ fs [numVarAssignment_range_ok_def, within_range_def,EVERY_MEM,FORALL_PROD]
QED

Theorem numBoolRange_to_cnf_preserves_unsat:
  rangeList_ok l ∧ exp_rangeList_ok l e ⇒
  (unsat_numBoolRange l e ⇔
   unsat_cnf (numBoolRange_to_cnf l e))
Proof
  strip_tac
  \\ imp_res_tac rangeList_encoded_ok
  \\ imp_res_tac exp_rangeList_encoded_ok
  \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (fs [unsat_cnf_def] \\ rpt strip_tac
    \\ drule_all numBoolRange_to_cnf_imp_sat \\ strip_tac
    \\ fs [unsat_numBoolRange_def]
    \\ first_x_assum drule
    \\ strip_tac \\ gvs [])
  \\ fs [numBoolRange_to_cnf_def]
  \\ drule_all (GSYM numBoolExtended_to_cnf_preserves_unsat)
  \\ strip_tac \\ fs []
  \\ pop_assum kall_tac
  \\ fs [rangeList_to_numVarList_def]
  \\ fs [unsat_numBoolExtended_def,unsat_numBoolRange_def]
  \\ fs [within_range_def]
  \\ rw [] \\ strip_tac
  \\ drule numBoolRange_to_numBoolExtended_preserves_sat
  \\ disch_then drule
  \\ qabbrev_tac ‘fix = λ(w:num->num) v. MIN (get_highest_max l) (w v)’
  \\ ‘∀v n m. MEM (v,n,m) l ⇒ m ≤ get_highest_max l’ by
    (qid_spec_tac ‘l’ \\ Induct \\ fs [FORALL_PROD] \\ rw [] \\ fs [get_highest_max_def]
     \\ res_tac \\ fs [])
  \\ ‘eval_numBoolRange w (fix w') e’ by
   (fs [Abbr‘fix’]
    \\ qpat_x_assum ‘eval_numBoolRange w w' e’ mp_tac
    \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ b ⇒ c”)
    \\ qpat_x_assum ‘exp_rangeList_ok l e’ mp_tac
    \\ qabbrev_tac ‘k = get_highest_max l’
    \\ ‘∀v m n. MEM (v,m,n) l ⇒ MIN k (w' v) = w' v ∧ w' v ≤ k’ by
      (rw [] \\ res_tac \\ gvs [MIN_DEF])
    \\ qid_spec_tac ‘e’ \\ Induct
    \\ fs [eval_numBoolRange_def,exp_rangeList_ok_def]
    \\ rpt strip_tac
    \\ fs [MEM_MAP,EXISTS_PROD]
    \\ res_tac \\ fs [])
  \\ disch_then (qspecl_then [‘w’,‘fix w'’] mp_tac)
  \\ impl_tac
  THEN1
   (fs [numVarAssignment_range_ok_def,EVERY_MEM,FORALL_PROD,Abbr‘fix’]
    \\ rw [] \\ res_tac \\ fs []
    \\ match_mp_tac LESS_EQ_TRANS \\ first_x_assum $ irule_at Any
    \\ match_mp_tac LESS_EQ_TRANS \\ first_x_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘l’ \\ Induct
    \\ fs [FORALL_PROD] \\ rw []
    \\ fs [get_highest_max_def])
  \\ strip_tac \\ gvs []
  \\ first_x_assum (qspecl_then [‘w’,‘fix w'’] mp_tac)
  \\ fs [] \\ fs [Abbr‘fix’]
QED



(*

Theorem numBoolRange_to_cnf_preserves_sat:
  ∀ e l w w'.
    rangeList_ok l ∧
    exp_rangeList_ok l e ∧
    numVarAssignment_range_ok w' l ⇒
    (eval_numBoolRange w w' e ⇔
       eval_cnf
       (encode_assignment_numBoolRange w w' l e)
       (numBoolRange_to_cnf l e))
Proof
  rw[]
  >> qspecl_then [‘e’, ‘l’, ‘w’, ‘w'’]
                 assume_tac numBoolRange_to_numBoolExtended_preserves_sat
  >> gs[encode_assignment_numBoolRange_def, numBoolRange_to_cnf_def]
  >> qspecl_then [‘numBoolRange_to_numBoolExtended l e’,
                  ‘w’, ‘w'’, ‘rangeList_to_numVarList l’]
                 assume_tac numBoolExtended_to_cnf_preserves_sat
  >> first_x_assum irule
  >> rw[rangeList_encoded_ok, exp_rangeList_encoded_ok,
        numVarAssignment_encoded_ok]
QED


(* ------------------ Theroems about assignment ---------------------- *)

Theorem mem_rangeList_numVarList:
  ∀ l x.
    MEM x (MAP FST l) ⇒
    MEM x (FST (rangeList_to_numVarList l))
Proof
  Induct >> rw[]
  >> Cases_on ‘h’
  >> rw[rangeList_to_numVarList_def]
QED

Theorem assignment_to_numVarAssignment_numBoolRange_ok:
  ∀ e l w w' x.
    rangeList_ok l ∧
    exp_rangeList_ok l e ∧
    numVarAssignment_range_ok w' l ∧
    MEM x (MAP FST l) ⇒
    w' x =
    assignment_to_numVarAssignment_numBoolRange
    (encode_assignment_numBoolRange w w' l e)
    l e x
Proof
  rw[encode_assignment_numBoolRange_def,
     assignment_to_numVarAssignment_numBoolRange_def]
  >> irule assignment_to_numVarAssignment_numBoolExtended_ok
  >> rw[rangeList_encoded_ok, mem_rangeList_numVarList,
        exp_rangeList_encoded_ok, numVarAssignment_encoded_ok]
QED

*)

