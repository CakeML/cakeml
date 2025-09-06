(*
  Extend numBoolExp with more functionality
*)
Theory numBoolExtended
Ancestors
  misc boolExpToCnf numBoolExp cnf
Libs
  preamble


(* -------------------------------- Datatypes ------------------------------- *)

Datatype:
  numBoolExtended =
  | ETrue
  | EFalse
  | EBoolVar num
  | ENot numBoolExtended
  | EAnd numBoolExtended numBoolExtended
  | EOr numBoolExtended numBoolExtended
  | EImpl numBoolExtended numBoolExtended
  | EIff numBoolExtended numBoolExtended
  | EAdd numVar numVar numVar   (* x + y = z *)
  | EEq numVar numVar           (* x = y *)
  | ENeq numVar numVar          (* x ≠ y *)
  | ELt numVar numVar           (* x < y *)
  | ELeq numVar numVar          (* x ≤ y *)
  | EGt numVar numVar           (* x > y *)
  | EGeq numVar numVar          (* x ≥ y *)
  | EEqConst numVar num         (* x = n *)
  | ENeqConst numVar num        (* x ≠ n *)
  | ELtConst numVar num         (* x < n *)
  | ELeqConst numVar num        (* x ≤ n *)
  | EGtConst numVar num         (* x > n *)
  | EGeqConst numVar num        (* x ≥ n *)
  | EConstEq num numVar         (* n = x *)
  | EConstNeq num numVar        (* n ≠ x *)
  | EConstLt num numVar         (* n < x *)
  | EConstLeq num numVar        (* n ≤ x *)
  | EConstGt num numVar         (* n > x *)
  | EConstGeq num numVar        (* n ≥ x *)
End


(* --------------------------- Creating varList ------------------------------- *)

Definition create_numVarList_numBoolExtended_inner_def:
  create_numVarList_numBoolExtended_inner l ETrue = l ∧
  create_numVarList_numBoolExtended_inner l EFalse = l ∧
  create_numVarList_numBoolExtended_inner l (EBoolVar b) = l ∧
  create_numVarList_numBoolExtended_inner l (ENot e) =
  create_numVarList_numBoolExtended_inner l e ∧
  create_numVarList_numBoolExtended_inner l (EAnd e1 e2) =
  nub (create_numVarList_numBoolExtended_inner l e1 ++
       create_numVarList_numBoolExtended_inner l e2) ∧
  create_numVarList_numBoolExtended_inner l (EOr e1 e2) =
  nub (create_numVarList_numBoolExtended_inner l e1 ++
       create_numVarList_numBoolExtended_inner l e2) ∧
  create_numVarList_numBoolExtended_inner l (EImpl e1 e2) =
  nub (create_numVarList_numBoolExtended_inner l e1 ++
       create_numVarList_numBoolExtended_inner l e2) ∧
  create_numVarList_numBoolExtended_inner l (EIff e1 e2) =
  nub (create_numVarList_numBoolExtended_inner l e1 ++
       create_numVarList_numBoolExtended_inner l e2) ∧
  create_numVarList_numBoolExtended_inner l (EAdd x y z) =
  add_numVar_to_list x (add_numVar_to_list y (add_numVar_to_list z l)) ∧
  create_numVarList_numBoolExtended_inner l (EEq x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (ENeq x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (ELt x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (ELeq x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (EGt x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (EGeq x y) =
  add_numVar_to_list x (add_numVar_to_list y l) ∧
  create_numVarList_numBoolExtended_inner l (EEqConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (ENeqConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (ELtConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (ELeqConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EGtConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EGeqConst x n) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstEq n x) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstNeq n x) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstLt n x) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstLeq n x) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstGt n x) =
  add_numVar_to_list x l ∧
  create_numVarList_numBoolExtended_inner l (EConstGeq n x) =
  add_numVar_to_list x l
End

Definition create_numVarList_numBoolExtended_def:
  create_numVarList_numBoolExtended k e =
  (create_numVarList_numBoolExtended_inner [] e, k)
End


(* ---------------------------- Well formed ------------------------------- *)

Definition extended_numVarList_ok_def:
  extended_numVarList_ok (l:numVarList) ETrue = T ∧
  extended_numVarList_ok l EFalse = T ∧
  extended_numVarList_ok l (EBoolVar b) = T ∧
  extended_numVarList_ok l (ENot e) =
  extended_numVarList_ok l e ∧
  extended_numVarList_ok l (EAnd e1 e2) =
  (extended_numVarList_ok l e1 ∧
   extended_numVarList_ok l e2) ∧
  extended_numVarList_ok l (EOr e1 e2) =
  (extended_numVarList_ok l e1 ∧
   extended_numVarList_ok l e2) ∧
  extended_numVarList_ok l (EImpl e1 e2) =
  (extended_numVarList_ok l e1 ∧
   extended_numVarList_ok l e2) ∧
  extended_numVarList_ok l (EIff e1 e2) =
  (extended_numVarList_ok l e1 ∧
   extended_numVarList_ok l e2) ∧
  extended_numVarList_ok l (EAdd x y z) =
  (MEM x (FST l) ∧ MEM y (FST l) ∧ MEM z (FST l)) ∧
  extended_numVarList_ok l (EEq x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (ENeq x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (ELt x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (ELeq x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (EGt x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (EGeq x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  extended_numVarList_ok l (EEqConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (ENeqConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (ELtConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (ELeqConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EGtConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EGeqConst x n) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstEq n x) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstNeq n x) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstLt n x) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstLeq n x) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstGt n x) = (MEM x (FST l)) ∧
  extended_numVarList_ok l (EConstGeq n x) = (MEM x (FST l))
End

(* -------------------------------- Evaluation ------------------------------- *)

Definition eval_numBoolExtended_def:
  eval_numBoolExtended (w:assignment) (w':numVarAssignment) ETrue = T ∧
  eval_numBoolExtended w w' EFalse = F ∧
  eval_numBoolExtended w w' (EBoolVar b) = w b ∧
  eval_numBoolExtended w w' (ENot e) = ¬eval_numBoolExtended w w' e ∧
  eval_numBoolExtended w w' (EAnd e1 e2) =
  (eval_numBoolExtended w w' e1 ∧ eval_numBoolExtended w w' e2) ∧
  eval_numBoolExtended w w' (EOr e1 e2) =
  (eval_numBoolExtended w w' e1 ∨ eval_numBoolExtended w w' e2) ∧
  eval_numBoolExtended w w' (EImpl e1 e2) =
  (eval_numBoolExtended w w' e1 ⇒ eval_numBoolExtended w w' e2) ∧
  eval_numBoolExtended w w' (EIff e1 e2) =
  (eval_numBoolExtended w w' e1 ⇔ eval_numBoolExtended w w' e2) ∧
  eval_numBoolExtended w w' (EAdd x y z) = (w' x + w' y = w' z) ∧
  eval_numBoolExtended w w' (EEq x y) = (w' x = w' y) ∧
  eval_numBoolExtended w w' (ENeq x y) = (w' x ≠ w' y) ∧
  eval_numBoolExtended w w' (ELt x y) = (w' x < w' y) ∧
  eval_numBoolExtended w w' (ELeq x y) = (w' x ≤ w' y) ∧
  eval_numBoolExtended w w' (EGt x y) = (w' x > w' y) ∧
  eval_numBoolExtended w w' (EGeq x y) = (w' x ≥ w' y) ∧
  eval_numBoolExtended w w' (EEqConst x n) = (w' x = n) ∧
  eval_numBoolExtended w w' (ENeqConst x n) = (w' x ≠ n) ∧
  eval_numBoolExtended w w' (ELtConst x n) = (w' x < n) ∧
  eval_numBoolExtended w w' (ELeqConst x n) = (w' x ≤ n) ∧
  eval_numBoolExtended w w' (EGtConst x n) = (w' x > n) ∧
  eval_numBoolExtended w w' (EGeqConst x n) = (w' x ≥ n) ∧
  eval_numBoolExtended w w' (EConstEq n x) = (n = w' x) ∧
  eval_numBoolExtended w w' (EConstNeq n x) = (n ≠ w' x) ∧
  eval_numBoolExtended w w' (EConstLt n x) = (n < w' x) ∧
  eval_numBoolExtended w w' (EConstLeq n x) = (n ≤ w' x) ∧
  eval_numBoolExtended w w' (EConstGt n x) = (n > w' x) ∧
  eval_numBoolExtended w w' (EConstGeq n x) = (n ≥ w' x)
End

Definition unsat_numBoolExtended_def:
  unsat_numBoolExtended lim b = ∀w w'. (∀n. w' n ≤ lim) ⇒ ¬ eval_numBoolExtended w w' b
End

(* --------------------------- Encoding ------------------------------- *)

Definition numBoolExtended_to_numBoolExp_def:
  numBoolExtended_to_numBoolExp ETrue = NTrue ∧
  numBoolExtended_to_numBoolExp EFalse = NFalse ∧
  numBoolExtended_to_numBoolExp (EBoolVar b) = NBoolVar b ∧
  numBoolExtended_to_numBoolExp (ENot e) =
  NNot (numBoolExtended_to_numBoolExp e) ∧
  numBoolExtended_to_numBoolExp (EAnd e1 e2) =
  NAnd (numBoolExtended_to_numBoolExp e1) (numBoolExtended_to_numBoolExp e2) ∧
  numBoolExtended_to_numBoolExp (EOr e1 e2) =
  NOr (numBoolExtended_to_numBoolExp e1) (numBoolExtended_to_numBoolExp e2) ∧
  numBoolExtended_to_numBoolExp (EImpl e1 e2) =
  NImpl (numBoolExtended_to_numBoolExp e1) (numBoolExtended_to_numBoolExp e2) ∧
  numBoolExtended_to_numBoolExp (EIff e1 e2) =
  NIff (numBoolExtended_to_numBoolExp e1) (numBoolExtended_to_numBoolExp e2) ∧
  numBoolExtended_to_numBoolExp (EAdd x y z) = NAdd x y z ∧
  numBoolExtended_to_numBoolExp (EEq x y) =
  NAnd (NLeq x y) (NLeq y x) ∧
  numBoolExtended_to_numBoolExp (ENeq x y) =
  NNot (NAnd (NLeq x y) (NLeq y x)) ∧
  numBoolExtended_to_numBoolExp (ELt x y) =
  NNot (NLeq y x) ∧
  numBoolExtended_to_numBoolExp (ELeq x y) = NLeq x y ∧
  numBoolExtended_to_numBoolExp (EGt x y) =
  NNot (NLeq x y) ∧
  numBoolExtended_to_numBoolExp (EGeq x y) = NLeq y x ∧
  numBoolExtended_to_numBoolExp (EEqConst x n) = NEqConst x n ∧
  numBoolExtended_to_numBoolExp (ENeqConst x n) = NNot (NEqConst x n) ∧
  numBoolExtended_to_numBoolExp (ELtConst x n) =
  (if n = 0 then NFalse else NLeqConst x (n - 1)) ∧
  numBoolExtended_to_numBoolExp (ELeqConst x n) = NLeqConst x n ∧
  numBoolExtended_to_numBoolExp (EGtConst x n) = NNot (NLeqConst x n) ∧
  numBoolExtended_to_numBoolExp (EGeqConst x n) =
  (if n = 0 then NTrue else NNot (NLeqConst x (n - 1))) ∧
  numBoolExtended_to_numBoolExp (EConstEq n x) = NEqConst x n ∧
  numBoolExtended_to_numBoolExp (EConstNeq n x) = NNot (NEqConst x n) ∧
  numBoolExtended_to_numBoolExp (EConstLt n x) = NNot (NLeqConst x n) ∧
  numBoolExtended_to_numBoolExp (EConstLeq n x) =
  (if n = 0 then NTrue else NNot (NLeqConst x (n - 1))) ∧
  numBoolExtended_to_numBoolExp (EConstGt n x) =
  (if n = 0 then NFalse else NLeqConst x (n - 1)) ∧
  numBoolExtended_to_numBoolExp (EConstGeq n x) = NLeqConst x n
End

Definition encode_assignment_numBoolExtended_def:
  encode_assignment_numBoolExtended w w' l e =
  let e' = numBoolExtended_to_numBoolExp e in
    minimal_encode_assignment w w' l e'
End

Definition assignment_to_numVarAssignment_numBoolExtended_def:
  assignment_to_numVarAssignment_numBoolExtended
  (w:assignment) (l:numVarList) (e:numBoolExtended) =
  let e' = numBoolExtended_to_numBoolExp e in
    minimal_assignment_to_numVarAssignment w l e'
End


(* ---------------------------- Theorems ------------------------------- *)

Theorem numBoolExtended_to_numBoolExp_preserves_sat:
  ∀ e w w'.
    eval_numBoolExtended w w' e =
    eval_numBoolExp w w' (numBoolExtended_to_numBoolExp e)
Proof
  Induct
  >> rw[eval_numBoolExtended_def, numBoolExtended_to_numBoolExp_def,
        eval_numBoolExp_def]
QED

Theorem numVarList_ok_lemma:
  ∀ e l.
    extended_numVarList_ok l e ⇒
    exp_numVarList_ok l (numBoolExtended_to_numBoolExp e)
Proof
  Induct >> rw[numBoolExtended_to_numBoolExp_def, exp_numVarList_ok_def]
  >> gs[extended_numVarList_ok_def]
QED

Definition numBoolExtended_to_cnf_def:
  numBoolExtended_to_cnf l e =
  let e' = numBoolExtended_to_numBoolExp e in
    numBool_to_cnf l e'
End

Definition numBoolExtended_to_assignment_def:
  numBoolExtended_to_assignment w w' l e =
  numBoolExp_to_assignment w w' l (numBoolExtended_to_numBoolExp e)
End

Theorem numBoolExtended_to_cnf_preserves_sat:
  ∀ e vList w w'.
    numVarList_ok vList ∧
    extended_numVarList_ok  vList e ∧
    minimal_numVarAssignment_ok w' vList ⇒
    (eval_numBoolExtended w w' e ⇔
       eval_cnf
       (numBoolExtended_to_assignment w w' vList e)
       (numBoolExtended_to_cnf vList e))
Proof
  rw[numBoolExtended_to_numBoolExp_preserves_sat, numBoolExtended_to_cnf_def,
     numBoolExtended_to_assignment_def]
  >> metis_tac[numBool_to_cnf_preserves_sat, numVarList_ok_lemma]
QED

Definition to_numExtended_assignment_def:
  to_numExtended_assignment vList e w =
    to_numExp_assignment (numBoolExtended_to_numBoolExp e) vList w
End

Theorem numBoolExtended_to_cnf_imp_sat:
  numVarList_ok vList ∧
  extended_numVarList_ok vList e ∧
  eval_cnf w (numBoolExtended_to_cnf vList e) ⇒
  eval_numBoolExtended w (to_numExtended_assignment vList e w) e
Proof
  rw [numBoolExtended_to_cnf_def,
      extended_numVarList_ok_def]
  \\ imp_res_tac numVarList_ok_lemma
  \\ drule_all numBool_to_cnf_imp_sat
  \\ fs [numBoolExtended_to_numBoolExp_preserves_sat,to_numExtended_assignment_def]
QED

Theorem numBoolExtended_to_cnf_preserves_unsat:
  numVarList_ok vList ∧ extended_numVarList_ok vList e ⇒
  (unsat_numBoolExtended (SND vList) e ⇔
   unsat_cnf (numBoolExtended_to_cnf vList e))
Proof
  rw [numBoolExtended_to_cnf_def]
  \\ imp_res_tac numVarList_ok_lemma
  \\ fs [GSYM numBool_to_cnf_preserves_unsat]
  \\ fs [unsat_numBoolExp_def,unsat_numBoolExtended_def]
  \\ fs [numBoolExtended_to_numBoolExp_preserves_sat]
QED

(*

Theorem numBoolExtended_to_cnf_preserves_sat:
  ∀ e w w' l.
    numVarList_ok l ∧
    extended_numVarList_ok l e ∧
    minimal_numVarAssignment_ok w' l ⇒
    eval_numBoolExtended w w' e =
    eval_cnf
    (encode_assignment_numBoolExtended w w' l e)
    (numBoolExtended_to_cnf l e)
Proof
  rw[numBoolExtended_to_cnf_def]
  >> rw[encode_assignment_numBoolExtended_def]
  >> rw[numBoolExtended_to_numBoolExp_preserves_sat]
  >> qspecl_then [‘w’, ‘w'’, ‘numBoolExtended_to_numBoolExp e’, ‘l’]
                 assume_tac minimal_numBool_to_cnf_preserves_sat
  >> gs[]
  >> first_x_assum irule
  >> gs[numVarList_ok_lemma]
QED

(* ------------------------ Assignment theorems ------------------------- *)

Theorem assignment_to_numVarAssignment_numBoolExtended_ok:
  ∀ e l w w' x.
    numVarList_ok l ∧
    extended_numVarList_ok l e ∧
    minimal_numVarAssignment_ok w' l ∧
    MEM x (FST l) ⇒
    w' x =
    assignment_to_numVarAssignment_numBoolExtended
    (encode_assignment_numBoolExtended w w' l e)
    l e x
Proof
  rw[encode_assignment_numBoolExtended_def,
     assignment_to_numVarAssignment_numBoolExtended_def]
  >> irule minimal_assignment_encoding_ok
  >> rw[numVarList_ok_lemma]
QED

*)

