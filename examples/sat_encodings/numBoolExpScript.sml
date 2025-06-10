(*
  Encode natural numbers to Booleans using order encoding
*)

open preamble miscTheory quantifierExpTheory arithmeticTheory;
open orderEncodingBoolTheory boolExpToCnfTheory cnfTheory;

val _ = new_theory "numBoolExp";

(* ----------------------------- Types ------------------------------------ *)

Type numVar = “:num”;
Type numVarAssignment = “:numVar -> num”;

(* numVarList is created from the expression,
   but the global upper bound is provided by the user *)
(* (numVar list # global upper bound) *)
Type numVarList = “:(numVar list) # num”;

(* numVarMap is created in the encoding process *)
(* (numVar # list of (bv, v).
   Ex for (x, [..., (bv, v), ...]), bv corrresponds to x ≤ v  *)
Type numVarMap = “:(numVar # ((num # num) list)) list”;

Datatype:
  numBoolExp =
  | NTrue
  | NFalse
  | NBoolVar num
  | NNot numBoolExp
  | NAnd numBoolExp numBoolExp
  | NOr numBoolExp numBoolExp
  | NImpl numBoolExp numBoolExp
  | NIff numBoolExp numBoolExp
  | NAdd numVar numVar numVar   (* x + y = z *)
  | NLeq numVar numVar          (* x ≤ y *)
  | NEqConst numVar num         (* x = n *)
  | NLeqConst numVar num        (* x ≤ n *)
End


(* -------------------- Create numVarList -------------------------- *)

Definition add_numVar_to_list_def:
  add_numVar_to_list nv l =
  if (MEM nv l) then l
  else (nv::l)
End

Definition create_numVarList_inner_def:
  create_numVarList_inner (l:(numVar list)) NTrue = l ∧
  create_numVarList_inner l NFalse = l ∧
  create_numVarList_inner l (NBoolVar n) = l ∧
  create_numVarList_inner l (NNot e) = create_numVarList_inner l e ∧
  create_numVarList_inner l (NAnd e1 e2) =
  nub (create_numVarList_inner l e1 ++ create_numVarList_inner l e2) ∧
  create_numVarList_inner l (NOr e1 e2) =
  nub (create_numVarList_inner l e1 ++ create_numVarList_inner l e2) ∧
  create_numVarList_inner l (NImpl e1 e2) =
  nub (create_numVarList_inner l e1 ++ create_numVarList_inner l e2) ∧
  create_numVarList_inner l (NIff e1 e2) =
  nub (create_numVarList_inner l e1 ++ create_numVarList_inner l e2) ∧
  create_numVarList_inner l (NAdd nv1 nv2 nv3) =
  (add_numVar_to_list nv3
   (add_numVar_to_list nv2 (add_numVar_to_list nv1 l))) ∧
  create_numVarList_inner l (NLeq nv1 nv2) =
  (add_numVar_to_list nv2 (add_numVar_to_list nv1 l)) ∧
  create_numVarList_inner l (NEqConst nv n) = (add_numVar_to_list nv l) ∧
  create_numVarList_inner l (NLeqConst nv n) = (add_numVar_to_list nv l)
End

Definition create_numVarList_def:
  create_numVarList k e = (create_numVarList_inner [] e, k)
End


(* ------------------------- Creating varMap ----------------------------- *)

Definition get_fresh_boolVar_def:
  get_fresh_boolVar NTrue = 1 ∧
  get_fresh_boolVar NFalse = 1 ∧
  get_fresh_boolVar (NBoolVar b) = b + 1 ∧
  get_fresh_boolVar (NNot e) = get_fresh_boolVar e ∧
  get_fresh_boolVar (NAnd e1 e2) =
  MAX (get_fresh_boolVar e1) (get_fresh_boolVar e2) ∧
  get_fresh_boolVar (NOr e1 e2) =
  MAX (get_fresh_boolVar e1) (get_fresh_boolVar e2) ∧
  get_fresh_boolVar (NImpl e1 e2) =
  MAX (get_fresh_boolVar e1) (get_fresh_boolVar e2) ∧
  get_fresh_boolVar (NIff e1 e2) =
  MAX (get_fresh_boolVar e1) (get_fresh_boolVar e2) ∧
  get_fresh_boolVar (NAdd _ _ _) = 1 ∧
  get_fresh_boolVar (NLeq _ _) = 1 ∧
  get_fresh_boolVar (NEqConst _ _) = 1 ∧
  get_fresh_boolVar (NLeqConst _ _) = 1
End

Definition create_numVarMap_inner_def:
  create_numVarMap_inner next len ([]:num list) = [] ∧
  create_numVarMap_inner next len (x::vList) =
  let b_list = GENLIST (λ n. (next + n, n)) (SUC len) in
    let element = (x, b_list) in
          element::(create_numVarMap_inner (next + SUC len) len vList)
End

Definition create_numVarMap_def:
  create_numVarMap (e:numBoolExp) (vList:numVarList) =
  create_numVarMap_inner (get_fresh_boolVar e) (SND vList) (FST vList)
End


(* -------------------------- Well formed ----------------------------- *)

Definition numVarList_ok_def:
  numVarList_ok (l:numVarList) ⇔
    ALL_DISTINCT (FST l)
End

Definition exp_numVarList_ok_def:
  exp_numVarList_ok (l:numVarList) NTrue = T ∧
  exp_numVarList_ok l NFalse = T ∧
  exp_numVarList_ok l (NBoolVar _) = T ∧
  exp_numVarList_ok l (NNot e) = exp_numVarList_ok l e ∧
  exp_numVarList_ok l (NAnd e1 e2) =
  (exp_numVarList_ok l e1 ∧ exp_numVarList_ok l e2) ∧
  exp_numVarList_ok l (NOr e1 e2) =
  (exp_numVarList_ok l e1 ∧ exp_numVarList_ok l e2) ∧
  exp_numVarList_ok l (NImpl e1 e2) =
  (exp_numVarList_ok l e1 ∧ exp_numVarList_ok l e2) ∧
  exp_numVarList_ok l (NIff e1 e2) =
  (exp_numVarList_ok l e1 ∧ exp_numVarList_ok l e2) ∧
  exp_numVarList_ok l (NAdd x y z) =
  (MEM x (FST l) ∧ MEM y (FST l) ∧ MEM z (FST l)) ∧
  exp_numVarList_ok l (NLeq x y) = (MEM x (FST l) ∧ MEM y (FST l)) ∧
  exp_numVarList_ok l (NEqConst x n) = MEM x (FST l) ∧
  exp_numVarList_ok l (NLeqConst x n) = MEM x (FST l)
End

Definition all_the_same_length_def:
  all_the_same_length vMap ⇔ ∃n. EVERY (λ(_,l). LENGTH l = n) vMap
End

Definition numVarMap_ok_def:
  numVarMap_ok (vMap:numVarMap) ⇔
    ALL_DISTINCT (MAP FST vMap) ∧
    EVERY (λ (_, l). l ≠ []) vMap ∧
    all_the_same_length vMap ∧
    ALL_DISTINCT (MAP FST (FLAT (MAP SND vMap))) ∧
    EVERY (λ l. MAP SND l = GENLIST I (LENGTH l)) (MAP SND vMap)
End

Definition exp_numVarMap_ok_def:
  exp_numVarMap_ok (vMap:numVarMap) NTrue = T ∧
  exp_numVarMap_ok vMap NFalse = T ∧
  exp_numVarMap_ok vMap (NBoolVar b) =
  ¬ MEM b (MAP FST (FLAT (MAP SND vMap))) ∧
  exp_numVarMap_ok vMap (NNot e) = exp_numVarMap_ok vMap e ∧
  exp_numVarMap_ok vMap (NAnd e1 e2) =
  (exp_numVarMap_ok vMap e1 ∧ exp_numVarMap_ok vMap e2) ∧
  exp_numVarMap_ok vMap (NOr e1 e2) =
  (exp_numVarMap_ok vMap e1 ∧ exp_numVarMap_ok vMap e2) ∧
  exp_numVarMap_ok vMap (NImpl e1 e2) =
  (exp_numVarMap_ok vMap e1 ∧ exp_numVarMap_ok vMap e2) ∧
  exp_numVarMap_ok vMap (NIff e1 e2) =
  (exp_numVarMap_ok vMap e1 ∧ exp_numVarMap_ok vMap e2) ∧
  exp_numVarMap_ok vMap (NAdd x y z) =
  (MEM x (MAP FST vMap) ∧ MEM y (MAP FST vMap) ∧ MEM z (MAP FST vMap)) ∧
  exp_numVarMap_ok vMap (NLeq x y) =
  (MEM x (MAP FST vMap) ∧ MEM y (MAP FST vMap)) ∧
  exp_numVarMap_ok vMap (NEqConst x n) = MEM x (MAP FST vMap) ∧
  exp_numVarMap_ok vMap (NLeqConst x n) = MEM x (MAP FST vMap)
End

Definition numVarAssignment_ok_def:
  numVarAssignment_ok (w':numVarAssignment) (vMap:numVarMap) ⇔
    EVERY (λ(x, bvs). (w' x) < (LENGTH bvs)) vMap
End

Definition minimal_numVarAssignment_ok_def:
  minimal_numVarAssignment_ok (w':numVarAssignment) (l:numVarList) =
  EVERY (λ x. w' x ≤ SND l) (FST l)
End


(* ------------------------ Satisfiability ----------------------------- *)

Definition eval_numBoolExp_def:
  eval_numBoolExp (w:assignment) (w':numVarAssignment) NTrue = T ∧
  eval_numBoolExp w w' NFalse = F ∧
  eval_numBoolExp w w' (NBoolVar b) = w b ∧
  eval_numBoolExp w w' (NNot e) = ¬ eval_numBoolExp w w' e ∧
  eval_numBoolExp w w' (NAnd e1 e2) =
  (eval_numBoolExp w w' e1 ∧ eval_numBoolExp w w' e2) ∧
  eval_numBoolExp w w' (NOr e1 e2) =
  (eval_numBoolExp w w' e1 ∨ eval_numBoolExp w w' e2) ∧
  eval_numBoolExp w w' (NImpl e1 e2) =
  (eval_numBoolExp w w' e1 ⇒ eval_numBoolExp w w' e2) ∧
  eval_numBoolExp w w' (NIff e1 e2) =
  (eval_numBoolExp w w' e1 ⇔ eval_numBoolExp w w' e2) ∧
  eval_numBoolExp w w' (NAdd x y z) = (w' x + w' y = w' z) ∧
  eval_numBoolExp w w' (NLeq x y) = (w' x ≤ w' y) ∧
  eval_numBoolExp w w' (NEqConst x n) = (w' x = n) ∧
  eval_numBoolExp w w' (NLeqConst x n) = (w' x ≤ n)
End

Definition unsat_numBoolExp_def:
  unsat_numBoolExp lim b =
    ∀w w'. (∀n. w' n ≤ lim) ⇒ ¬ eval_numBoolExp w w' b
End

(* ----------------------- Encoding ---------------------------------- *)

Definition vMap_to_orderBool_def:
  vMap_to_orderBool [] = [] ∧
  vMap_to_orderBool ((bv, v)::l) = (OLit (INL bv))::(vMap_to_orderBool l)
End

Definition encode_combinations_def:
  encode_combinations [] _ = OFalse ∧
  encode_combinations (bx::bxs) bys =
  if bys = []
  then OFalse
  else OOr
       (OAnd bx (LAST bys))
       (encode_combinations bxs (FRONT bys))
End

Definition encode_add_def:
  encode_add _ _ [] = OTrue ∧
  encode_add bxs bys (bz::bzs) =
  OAnd
  (OIff bz (encode_combinations bxs bys))
  (encode_add (TL bxs) (TL bys) bzs)
End

Definition encode_leq_def:
  encode_leq [] = OTrue ∧
  encode_leq ((bx, by)::l) =
  OAnd
  (OImpl by bx)
  (encode_leq l)
End

Definition encode_eqConst_def:
  encode_eqConst n bvs =
  if LENGTH bvs ≤ n
  then OFalse
  else if n = 0
  then HD bvs
  else OAnd
       (ONot (EL (n - 1) bvs))
       (EL n bvs)
End

Definition encode_leqConst_def:
  encode_leqConst n bvs =
  if LENGTH bvs ≤ n
  then OTrue
  else EL n bvs
End

Definition numBoolExp_to_orderBool_def:
  (numBoolExp_to_orderBool (vMap: numVarMap) NTrue = OTrue) ∧
  (numBoolExp_to_orderBool vMap NFalse = OFalse) ∧
  (numBoolExp_to_orderBool vMap (NBoolVar x) = (OLit (INL x))) ∧
  (numBoolExp_to_orderBool vMap (NNot b) =
   (ONot (numBoolExp_to_orderBool vMap b))) ∧
  (numBoolExp_to_orderBool vMap (NAnd b1 b2) =
   (OAnd
    (numBoolExp_to_orderBool vMap b1)
    (numBoolExp_to_orderBool vMap b2))) ∧
  (numBoolExp_to_orderBool vMap (NOr b1 b2) =
   (OOr
    (numBoolExp_to_orderBool vMap b1)
    (numBoolExp_to_orderBool vMap b2))) ∧
  (numBoolExp_to_orderBool vMap (NImpl b1 b2) =
   (OImpl
    (numBoolExp_to_orderBool vMap b1)
    (numBoolExp_to_orderBool vMap b2))) ∧
  (numBoolExp_to_orderBool vMap (NIff b1 b2) =
   (OIff
    (numBoolExp_to_orderBool vMap b1)
    (numBoolExp_to_orderBool vMap b2))) ∧
  (numBoolExp_to_orderBool vMap (NAdd x y z) =
   case (ALOOKUP vMap x, ALOOKUP vMap y, ALOOKUP vMap z) of
   | (SOME bxs, SOME bys, SOME bzs) =>
       encode_add (REVERSE (vMap_to_orderBool bxs))
                  (REVERSE (vMap_to_orderBool bys))
                  (REVERSE (vMap_to_orderBool bzs))
   | (_, _, _) => OFalse) ∧
  (numBoolExp_to_orderBool vMap (NLeq x y) =
   case (ALOOKUP vMap x, ALOOKUP vMap y) of
   | (SOME bxs, SOME bys) =>
       encode_leq (ZIP (vMap_to_orderBool bxs, vMap_to_orderBool bys))
   | (_, _) => OFalse) ∧
  (numBoolExp_to_orderBool vMap (NEqConst x n) =
   case ALOOKUP vMap x of
   | SOME bxs => encode_eqConst n (vMap_to_orderBool bxs)
   | NONE => OFalse) ∧
  (numBoolExp_to_orderBool vMap (NLeqConst x n) =
   case ALOOKUP vMap x of
   | SOME bxs => encode_leqConst n (vMap_to_orderBool bxs)
   | NONE => OFalse)
End

Definition encode_axioms_def:
  encode_axioms ([]:numVarMap) = OTrue ∧
  encode_axioms ((_, bvs)::vMap) =
  OAnd (OOrderAxiom (MAP FST bvs)) (encode_axioms vMap)
End

Definition numBool_to_orderBool_def:
  numBool_to_orderBool (l:numVarList) (e:numBoolExp) =
  let vMap = create_numVarMap e l in
    OAnd
    (numBoolExp_to_orderBool vMap e)
    (encode_axioms vMap)
End

Definition numBool_to_cnf_def:
  numBool_to_cnf l exp = orderBool_to_cnf (numBool_to_orderBool l exp)
End

Definition invert_numVarMap_def:
  invert_numVarMap (vMap:numVarMap) =
  FLAT (MAP (λ (x, bvs).
               MAP (λ (bv, value). (bv, (x, value))) bvs)
        vMap)
End


(* ------------------- Encode assignment -------------------------- *)

Definition encode_assignment_def:
  encode_assignment
  (w:assignment) (w':numVarAssignment) (vMap:numVarMap) (bv:num) =
  case ALOOKUP (invert_numVarMap vMap) bv of
  | NONE => w bv
  | SOME (x, v) => w' x ≤ v
End

Definition minimal_encode_assignment_def:
  minimal_encode_assignment
  (w:assignment) (w':numVarAssignment)
  (vList:numVarList) (e:numBoolExp) (bv:num) =
  let vMap = create_numVarMap e vList in
    encode_assignment w w' vMap bv
End

Definition find_value_def:
  find_value (w:assignment) ([]:(num # num) list) = 0 ∧
  find_value w ((bv, v)::bvs) =
  if w bv
  then v
  else find_value w bvs
End

Definition assignment_to_numVarAssignment_def:
  assignment_to_numVarAssignment (w:assignment) (vMap:numVarMap) (x:numVar) =
  case ALOOKUP vMap x of
  | NONE => (0:num)
  | SOME bvs => find_value w bvs
End

Definition minimal_assignment_to_numVarAssignment_def:
  minimal_assignment_to_numVarAssignment
  (w:assignment) (vList:numVarList) (e:numBoolExp) (x:numVar) =
  let vMap = create_numVarMap e vList in
    assignment_to_numVarAssignment w vMap x
End

(* ----------------------- Lemmas ---------------------------------- *)

Theorem not_mem_bvs_lemma:
  ∀ bvs n x.
    ¬MEM n (MAP FST bvs) ⇒
    ALOOKUP (MAP (λ(bv,value). (bv,x,value)) bvs) n = NONE
Proof
  Induct
  >> rw[]
  >> Cases_on‘h’
  >> gvs[]
QED

Theorem boolVar_not_in_vMap_lemma:
  ∀ vMap n.
    exp_numVarMap_ok vMap (NBoolVar n) ⇒
    ALOOKUP (invert_numVarMap vMap) n = NONE
Proof
  Induct
  >- rw[invert_numVarMap_def]
  >> rw[]
  >> gs[invert_numVarMap_def, ALOOKUP_APPEND, exp_numVarMap_ok_def]
  >> Cases_on ‘h’
  >> gs[SND]
  >> Cases_on ‘ALOOKUP (MAP (λ(bv,value). (bv,q,value)) r) n’
  >- gs[]
  >> gs[not_mem_bvs_lemma]
QED

Theorem vMap_mem_lemma:
  ∀ vMap x.
    ALL_DISTINCT (MAP FST vMap) ∧
    MEM x (MAP FST vMap) ⇒
    ALOOKUP vMap x ≠ NONE
Proof
  Induct
  >- gvs[]
  >> Cases_on‘h’
  >> rw[] >> metis_tac[]
QED

Theorem vMap_no_empty_lists_lemma:
  ∀ vMap x.
    numVarMap_ok vMap ⇒
    ALOOKUP vMap x ≠ SOME []
Proof
  Induct
  >- gvs[]
  >> Cases_on‘h’
  >> gvs[numVarMap_ok_def]
  >> rw[]
  >> gvs[all_the_same_length_def]
  >> gvs[ALL_DISTINCT_APPEND]
  >> metis_tac[]
QED

Theorem vMap_orderBool_same_size_lemma:
  ∀bvs.
    LENGTH (vMap_to_orderBool bvs) = (LENGTH bvs)
Proof
  Induct
  >> gvs[vMap_to_orderBool_def]
  >> Cases_on‘h’
  >> gvs[vMap_to_orderBool_def]
QED

Theorem bvs_not_empty_lemma:
  ∀ bvs x w'.
    w' x < LENGTH bvs ⇒
    bvs ≠ []
Proof
  Induct >> rw[]
QED

Theorem bvs_not_empty_2_lemma:
  ∀ bvs x vMap w'.
    numVarMap_ok vMap ∧
    MEM x (MAP FST vMap) ∧
    ALOOKUP vMap x = SOME bvs ∧
    EVERY (λ(x,bvs). w' x < LENGTH bvs) vMap ⇒
    bvs ≠ []
Proof
  rw[numVarMap_ok_def, bvs_not_empty_lemma]
  >> Induct_on‘bvs’
  >> gvs[numVarMap_ok_def, bvs_not_empty_lemma, vMap_no_empty_lists_lemma]
QED

Theorem alookup_el_lemma:
  ∀ vMap bvs x bv v.
    numVarMap_ok vMap ∧
    ALOOKUP vMap x = SOME bvs ∧
    MEM (bv, v) bvs ⇒
    ALOOKUP (invert_numVarMap vMap) bv = SOME (x, v)
Proof
  rw[]
  >> gs[numVarMap_ok_def, invert_numVarMap_def]
  >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> ‘MEM (x, bvs) vMap’ by gvs[ALOOKUP_MEM]
  >> last_x_assum (qspecl_then [‘bvs’, ‘x’] assume_tac)
  >> irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM
  >> gs [MEM_FLAT, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >> gs [ELIM_UNCURRY]
  >> rw [MEM_MAP, PULL_EXISTS, EXISTS_PROD]
  >> drule ALOOKUP_MEM
  >> gvs[]
  >> metis_tac[]
QED

Theorem vMap_length_equal_2_lemma:
  ∀ vMap x y bxs bys.
    all_the_same_length vMap ∧
    ALOOKUP vMap x = SOME bxs ∧
    ALOOKUP vMap y = SOME bys ⇒
    LENGTH bxs = LENGTH bys
Proof
  rw[]
  >> gvs[all_the_same_length_def]
  >> gvs[ELIM_UNCURRY]
  >> gvs[EVERY_MEM]
  >> gvs[FORALL_PROD]
  >> ‘MEM (x, bxs) vMap’ by gvs[ALOOKUP_MEM]
  >> ‘MEM (y, bys) vMap’ by gvs[ALOOKUP_MEM]
  >> metis_tac[]
QED

Theorem values_equal_lemma:
  ∀ vMap x xs bx vx t y ys by vy t'.
    numVarMap_ok vMap ∧
    ALOOKUP vMap x = SOME (xs ++ (bx, vx)::t) ∧
    ALOOKUP vMap y = SOME (ys ++ (by, vy)::t') ∧
    LENGTH t = LENGTH t' ⇒
    vx = vy
Proof
  rw[]
  >> gvs[numVarMap_ok_def]
  >> ‘LENGTH (xs ++ (bx,vx)::t) = LENGTH (ys ++ (by,vy)::t')’
    by metis_tac[vMap_length_equal_2_lemma]
  >> ‘LENGTH xs = LENGTH ys’ by gvs[]
  >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> ‘MEM (x, (xs ++ (bx,vx)::t)) vMap’ by gs[ALOOKUP_MEM]
  >> ‘MEM (y, (ys ++ (by,vy)::t')) vMap’ by gs[ALOOKUP_MEM]
  >> last_assum (qspecl_then [‘xs ++ (bx,vx)::t’, ‘x’] assume_tac)
  >> last_x_assum (qspecl_then [‘ys ++ (by,vy)::t'’, ‘y’] assume_tac)
  >> gs[]
  >> ‘MAP SND xs ++ [vx] ++ MAP SND t = MAP SND ys ++ [vy] ++ MAP SND t'’
    by gs[]
  >> gs[APPEND_LENGTH_EQ]
QED

Theorem length_equal_lemma:
  ∀ vMap x xs q n.
    numVarMap_ok vMap ∧
    MEM (x,xs ++ [(q,n)]) vMap ⇒
    n = LENGTH xs
Proof
  rw[]
  >> gs[numVarMap_ok_def, all_the_same_length_def]
  >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> last_x_assum (qspecl_then [‘(xs ++ [(q,n)])’, ‘x’] assume_tac)
  >> ‘GENLIST I (LENGTH xs + 1) = GENLIST I (SUC (LENGTH xs))’ by gs[ADD1]
  >> gs[GENLIST]
QED

Theorem el_genlist_lemma:
  ∀ bvs n q r.
    n < LENGTH bvs ∧
    EL n bvs = (q,r) ∧
    MAP SND bvs = GENLIST I (LENGTH bvs) ⇒
    n = r
Proof
  rw[]
  >> Induct_on ‘REVERSE bvs’ >> rw[]
  >> gs[GSYM SWAP_REVERSE_SYM]
  >> qpat_x_assum ‘REVERSE _ ++ _ = _’ (assume_tac o GSYM)
  >> gs[]
  >> gs[GSYM ADD1]
  >> gs[GENLIST]
  >> Cases_on ‘n < LENGTH v’
  >- gs[EL_APPEND_EQN]
  >> gs[]
  >> ‘n = LENGTH v’ by gs[]
  >> ‘EL (LENGTH v) (REVERSE v ++ [h]) = (q ,r)’ by metis_tac[]
  >> gs[EL_APPEND_EQN]
QED

Theorem value_smaller_lemma:
  ∀ xs h' h bvs.
    MAP SND xs ++ [SND h'; SND h] ++ MAP SND bvs =
    GENLIST I (LENGTH xs + (SUC (LENGTH bvs) + 1)) ⇒
    SND h' < SND h
Proof
  rw[]
  >> gs[GSYM ADD1, GSYM ADD_SUC, GENLIST]
  >> Induct_on ‘REVERSE bvs’ >> rw[]
  >> gs[GSYM SWAP_REVERSE_SYM]
  >> qpat_x_assum ‘REVERSE _ ++ _ = _’ (assume_tac o GSYM)
  >> gs[GSYM ADD1, GSYM ADD_SUC, GENLIST]
QED

Theorem all_alookup:
  ∀ xs x w' vMap.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME xs ⇒
    EVERY (λ (bx, vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) xs
Proof
  gs[EVERY_MEM, FORALL_PROD]
  >> rw[]
  >> metis_tac[alookup_el_lemma]
QED

Theorem alookup_el_length:
  ∀ xs xs' x q r vMap w'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (xs' ++ (q,r)::xs) ⇒
    r = LENGTH xs'
Proof
  rw[]
  >> gvs[numVarMap_ok_def, numVarAssignment_ok_def]
  >> rgs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> ‘MEM (x, (xs' ++ (q,r)::xs)) vMap’ by gs[ALOOKUP_MEM]
  >> last_x_assum (qspecl_then [‘x’, ‘xs' ++ (q,r)::xs’] assume_tac)
  >> first_x_assum (qspecl_then [‘xs' ++ (q,r)::xs’, ‘x’] assume_tac)
  >> gvs[GENLIST_APPEND, APPEND_EQ_CONS, APPEND_11_LENGTH, GENLIST]
  >> rgs[GSYM ADD1]
  >> ‘lt ++ [r] = SNOC r lt’ by gvs[]
  >> ‘LENGTH (MAP SND xs') = (LENGTH (0::lt))’ by metis_tac[]
  >> ‘LENGTH xs' = SUC (LENGTH lt)’ by rgs[]
  >> gvs[GENLIST]
QED

Definition bv_to_orderBool_def:
  bv_to_orderBool (bv, v) = OLit (INL bv)
End

Theorem vMap_to_orderBool_el_flip:
  ∀ bvs n bv.
    n < LENGTH (vMap_to_orderBool bvs) ⇒
    EL n (vMap_to_orderBool bvs) =
       bv_to_orderBool (EL n bvs)
Proof
  Induct
  >- rw[vMap_to_orderBool_def]
  >> rw[]
  >> Cases_on ‘h’
  >> gs[vMap_to_orderBool_def]
  >> Cases_on ‘n = 0’
  >- gs[bv_to_orderBool_def]
  >> gs[]
  >> last_x_assum (qspecl_then [‘PRE n’] mp_tac)
  >> rw[]
  >> gvs[EL_CONS]
QED


(* -------------- Theorems about axioms always true -------------------- *)

Theorem next_bv_true:
  ∀ vMap bvs x xs h' h w w'.
    numVarMap_ok vMap ∧
    MEM (x,xs ++ h'::h::bvs) vMap ∧
    MAP SND xs ++ [SND h'; SND h] ++ MAP SND bvs =
    GENLIST I (LENGTH xs + (SUC (LENGTH bvs) + 1)) ∧
    w' x < LENGTH xs + SUC (SUC (LENGTH bvs)) ∧
    encode_assignment w w' vMap (FST h') ⇒
    encode_assignment w w' vMap (FST h)
Proof
  rw[]
  >> gs[encode_assignment_def]
  >> qspecl_then [‘vMap’, ‘xs ++ h'::h::bvs’, ‘x’, ‘FST h’, ‘SND h’]
                 assume_tac alookup_el_lemma
  >> qspecl_then [‘vMap’, ‘xs ++ h'::h::bvs’, ‘x’, ‘FST h'’, ‘SND h'’]
                 assume_tac alookup_el_lemma
  >> gs[numVarMap_ok_def, MEM_ALOOKUP]
  >> qspecl_then [‘xs’, ‘h'’, ‘h’, ‘bvs’] assume_tac value_smaller_lemma
  >> gs[]
QED

Theorem every_bv_true:
  ∀ bvs xs h x vMap w w'.
    numVarMap_ok vMap ∧
    MEM (x,xs ++ h::bvs) vMap ∧
    MAP SND xs ++ [SND h] ++ MAP SND bvs =
    GENLIST I (LENGTH bvs + (LENGTH xs + 1)) ∧
    w' x < LENGTH xs + SUC (LENGTH bvs) ∧
    encode_assignment w w' vMap (FST h) ⇒
    EVERY (encode_assignment w w' vMap) (MAP FST bvs)
Proof
  Induct
  >- rw[]
  >> rw[]
  >- metis_tac[next_bv_true]
  >> Cases_on ‘encode_assignment w w' vMap (FST h)’
  >- (last_x_assum
      (qspecl_then [‘xs ++ [h']’, ‘h’, ‘x’, ‘vMap’, ‘w’, ‘w'’] assume_tac)
      >> gs[ADD1]
      >> metis_tac[APPEND_ASSOC, CONS_APPEND])
  >> metis_tac[next_bv_true]
QED

Theorem eval_orderAxiom_one_variable:
  ∀ bvs xs x vMap w w'.
    numVarMap_ok vMap ∧
    MEM (x, xs ++ bvs) vMap ∧
    MAP SND (xs ++ bvs) = GENLIST I (LENGTH (xs ++ bvs)) ∧
    w' x < LENGTH (xs ++ bvs) ∧
    bvs ≠ [] ⇒
    eval_orderAxiom (encode_assignment w w' vMap) (MAP FST bvs)
Proof
  Induct
  >- rw[eval_orderAxiom_def]
  >> rw[]
  >> rw[eval_orderAxiom_def]
  >- (irule every_bv_true
      >> metis_tac[])
  >> Cases_on ‘bvs = []’ >> gs[eval_orderAxiom_def]
  >- (gs[encode_assignment_def]
      >> qspecl_then [‘vMap’, ‘xs ++ [h]’, ‘x’, ‘FST h’, ‘SND h’]
                     assume_tac alookup_el_lemma
      >> gs[numVarMap_ok_def]
      >> gs[MEM_ALOOKUP]
      >> ‘GENLIST I (LENGTH xs + 1) = GENLIST I (SUC (LENGTH xs))’ by gs[ADD1]
      >> gs[]
      >> gs[GENLIST])
  >> last_x_assum
     (qspecl_then [‘xs ++ [h]’, ‘x’, ‘vMap’, ‘w’, ‘w'’] assume_tac)
  >> gs[]
  >> metis_tac[APPEND_ASSOC, CONS_APPEND]
QED

Theorem axioms_always_true_2:
  ∀ xs vMap w w'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    EVERY (λ x. MEM x vMap) xs ⇒
    eval_orderBool
    (encode_assignment w w' vMap)
    (encode_axioms xs)
Proof
  Induct
  >- gs[encode_axioms_def, eval_orderBool_def]
  >> rw[]
  >> PairCases_on ‘h’
  >> gs[encode_axioms_def, eval_orderBool_def]
  >> gs[numVarMap_ok_def, numVarAssignment_ok_def]
  >> last_x_assum kall_tac
  >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> first_assum drule
  >> last_assum drule
  >> strip_tac
  >> strip_tac
  >> qspecl_then [‘h1’, ‘[]’, ‘h0’, ‘vMap’, ‘w’, ‘w'’]
                 assume_tac eval_orderAxiom_one_variable
  >> gs[numVarMap_ok_def, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> qpat_x_assum ‘∀ p_1. ¬MEM _ _’ (qspecl_then [‘h0’] assume_tac)
  >> metis_tac[]
QED

Theorem axioms_always_true:
  ∀ vMap w w'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ⇒
    eval_orderBool
    (encode_assignment w w' vMap)
    (encode_axioms vMap)
Proof
  rw[]
  >> irule axioms_always_true_2
  >> rw[EVERY_MEM]
QED


(* ----------------- Theorems about LeqConst ------------------------- *)

Theorem leqConst_preserves_sat:
  ∀ bvs vMap x n w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NLeqConst x n) ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME bvs ⇒
    (w' x ≤ n ⇔
       eval_orderBool
       (encode_assignment w w' vMap)
       (encode_leqConst n (vMap_to_orderBool bvs)))
Proof
  rw[encode_leqConst_def]
  >- (gs[eval_orderBool_def, numVarAssignment_ok_def, EVERY_MEM, FORALL_PROD]
      >> last_x_assum (qspecl_then [‘x’, ‘bvs’] assume_tac)
      >> gs[ALOOKUP_MEM, vMap_orderBool_same_size_lemma])
  >> rw[vMap_to_orderBool_el_flip]
  >> Cases_on ‘EL n bvs’
  >> rw[bv_to_orderBool_def, eval_orderBool_def, eval_literal_def,
        encode_assignment_def]
  >> qspecl_then [‘vMap’, ‘bvs’, ‘x’, ‘q’, ‘r’] assume_tac alookup_el_lemma
  >> ‘n < LENGTH bvs’ by gs[vMap_orderBool_same_size_lemma]
  >> ‘MEM (q, r) bvs’ by metis_tac[EL_MEM]
  >> rgs[numVarMap_ok_def, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> last_x_assum (qspecl_then [‘bvs’, ‘x’] assume_tac)
  >> rgs[ALOOKUP_MEM]
  >> metis_tac[el_genlist_lemma]
QED


(* ----------------- Theorems about EqConst ------------------------- *)

Theorem x_less_than_suc_n:
  ∀bvs vMap n x w'.
  LENGTH bvs = SUC n ∧
  ALOOKUP vMap x = SOME bvs ∧
  EVERY (λ(x,bvs). w' x < LENGTH bvs) vMap ⇒
  w' x < SUC n
Proof
  Induct_on‘vMap’
  >- gvs[]
  >> Cases_on‘h’
  >> rw[]
  >> gvs[]
QED

Theorem list_shorter_than_value_lemma:
  ∀vMap bvs n x w'.
    (numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NEqConst x n) ∧
    EVERY (λ(x,bvs). w' x < LENGTH bvs) vMap ∧
    ALOOKUP vMap x = SOME bvs) ∧
    LENGTH (vMap_to_orderBool bvs) ≤ n ⇒
    w' x < n
Proof
  rw[vMap_orderBool_same_size_lemma]
  >> Induct_on‘n’
  >- (rw[]
      >> gvs[exp_numVarMap_ok_def]
      >> metis_tac[bvs_not_empty_2_lemma])
  >> gvs[numVarMap_ok_def, exp_numVarMap_ok_def]
  >> rw[]
  >> gvs[]
  >> Cases_on‘LENGTH bvs ≤ n’
  >- gvs[]
  >> gvs[]
  >> ‘(LENGTH bvs = SUC n)’ by gvs[]
  >> metis_tac[x_less_than_suc_n]
QED

Theorem eqConst_preserves_sat:
  ∀ bvs vMap x (n:num) w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NEqConst x n) ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME bvs ⇒
    (w' x = n ⇔
       eval_orderBool
       (encode_assignment w w' vMap)
       (encode_eqConst n (vMap_to_orderBool bvs)))
Proof
  rw[encode_eqConst_def, eval_orderBool_def]
  >- (qspecl_then [‘vMap’, ‘bvs’, ‘n’, ‘x’, ‘w'’]
      assume_tac list_shorter_than_value_lemma
      >> gs[numVarAssignment_ok_def])
  >- (Cases_on ‘bvs’
      >- gs[vMap_to_orderBool_def]
      >> Cases_on ‘h’
      >> rw[vMap_to_orderBool_def, eval_orderBool_def,
            eval_literal_def, encode_assignment_def]
      >> qspecl_then [‘vMap’, ‘(q, r)::t’, ‘x’, ‘q’, ‘r’]
                     mp_tac alookup_el_lemma
      >> rw[]
      >> gs[numVarMap_ok_def]
      >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      >> ‘MEM (x, ((q,r)::t)) vMap’ by gs[ALOOKUP_MEM]
      >> last_x_assum (qspecl_then [‘((q,r)::t)’, ‘x’] assume_tac)
      >> gs[GENLIST_CONS])
  >> gs[vMap_to_orderBool_el_flip, vMap_orderBool_same_size_lemma,
        numVarMap_ok_def]
  >> Cases_on ‘EL n bvs’
  >> Cases_on ‘EL (n − 1) bvs’
  >> gs[bv_to_orderBool_def, eval_orderBool_def, eval_literal_def,
        encode_assignment_def, numVarMap_ok_def]
  >> ‘MEM (x, bvs) vMap’ by gvs[ALOOKUP_MEM]
  >> qspecl_then [‘vMap’, ‘bvs’, ‘x’, ‘q’, ‘r’] assume_tac alookup_el_lemma
  >> qspecl_then [‘vMap’, ‘bvs’, ‘x’, ‘q'’, ‘r'’] assume_tac alookup_el_lemma
  >> ‘n < LENGTH bvs’ by gs[]
  >> ‘MEM (q, r) bvs’ by metis_tac[EL_MEM]
  >> ‘(n - 1) < LENGTH bvs’ by gs[]
  >> ‘MEM (q', r') bvs’ by metis_tac[EL_MEM]
  >> gs[numVarMap_ok_def]
  >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> last_x_assum (qspecl_then [‘bvs’, ‘x’] assume_tac)
  >> gs[]
  >> qspecl_then [‘bvs’, ‘n’, ‘q’, ‘r’] assume_tac el_genlist_lemma
  >> qspecl_then [‘bvs’, ‘n-1’, ‘q'’, ‘r'’] assume_tac el_genlist_lemma
  >> gs[]
QED


(* ------------------- Theorems about NLeq ------------------------------ *)

Theorem list_rel_implies_inequality:
  ∀ xs ys xs' ys' x y w' vMap.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    xs ≠ [] ∧
    LENGTH xs = LENGTH ys ∧
    LENGTH xs' = LENGTH ys' ∧
    ALOOKUP vMap x = SOME (xs' ++ xs) ∧
    ALOOKUP vMap y = SOME (ys' ++ ys) ∧
    (¬(w' y < LENGTH ys')) ∧
    LIST_REL (λ(bvx,vx) (bvy,vy). w' y ≤ vy ⇒ w' x ≤ vx)
             (xs' ++ xs) (ys' ++ ys) ⇒
    w' x ≤ w' y
Proof
  Induct >> rw[]
  >> Cases_on ‘ys’ >> gs[]
  >> last_x_assum
     (qspecl_then [‘t’, ‘xs' ++ [h]’, ‘ys' ++ [h']’, ‘x’, ‘y’, ‘w'’, ‘vMap’]
      assume_tac)
  >> gs[]
  >> Cases_on ‘xs = []’ >> gs[]
  >- (Cases_on ‘h’
      >> Cases_on ‘h'’
      >> gs[]
      >> gs[numVarAssignment_ok_def]
      >> gs[EVERY_MEM]
      >> gs[FORALL_PROD]
      >> last_assum (qspecl_then [‘x’, ‘xs' ++ [(q,r)]’] assume_tac)
      >> last_x_assum (qspecl_then [‘y’, ‘ys' ++ [(q',r')]’] assume_tac)
      >> gs[ALOOKUP_MEM])
  >> Cases_on ‘¬(w' y < LENGTH ys' + 1)’ >> gs[]
  >- metis_tac[CONS_APPEND, APPEND_ASSOC]
  >> gs[LIST_REL_EL_EQN]
  >> Cases_on ‘h’
  >> Cases_on ‘h'’
  >> gs[]
  >> qspecl_then [‘vMap’, ‘x’, ‘xs'’, ‘q’, ‘r’, ‘xs’, ‘y’,
                  ‘ys'’, ‘q'’, ‘r'’, ‘t’]
                 assume_tac values_equal_lemma
  >> gs[]
  >> first_x_assum (qspecl_then [‘LENGTH ys'’] assume_tac)
  >> gs[]
  >> gs[EL_APPEND_EQN]
  >> qspecl_then [‘t’, ‘ys'’, ‘y’, ‘q'’, ‘r'’, ‘vMap’, ‘w'’]
                 assume_tac alookup_el_length
  >> gs[]
QED

Theorem leq_const_highest_value_lemma:
  ∀ (w':numVarAssignment) x y n vMap xs ys q q'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (xs ++ (q, n)::[]) ∧
    ALOOKUP vMap y = SOME (ys ++ (q', n)::[]) ∧
    LIST_REL (λ(bvx,vx) (bvy,vy). w' y ≤ vy ⇒ w' x ≤ vx) xs ys ⇒
    (w' x ≤ w' y ⇔
      (w' y ≤ n ⇒ w' x ≤ n))
Proof
  rw[]
  >> eq_tac >> rw[]
  >> Cases_on ‘w' x = n’
  >- (Cases_on ‘w' y = n’ >> gs[]
      >> gs[numVarMap_ok_def]
      >> gs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
      >> gs[FORALL_PROD]
      >> last_assum (qspecl_then [‘x’, ‘xs ++ [(q,n)]’] assume_tac)
      >> last_x_assum (qspecl_then [‘y’, ‘ys ++ [(q',n)]’] assume_tac)
      >> gs[GSYM ADD1, GENLIST]
      >> gs[ALOOKUP_MEM]
      >> Cases_on ‘xs’ using SNOC_CASES >> gs[]
      >> Cases_on ‘ys’ using SNOC_CASES >> gs[]
      >> Cases_on ‘x'’
      >> Cases_on ‘x''’
      >> gs[GSYM ADD1, GENLIST, SNOC_APPEND])
  >> Cases_on ‘w' y = n’ >> gs[]
  >> qspecl_then [‘xs ++ [(q,n)]’, ‘ys ++ [(q',n)]’, ‘[]’, ‘[]’,
                  ‘x’, ‘y’, ‘w'’, ‘vMap’]
                 assume_tac list_rel_implies_inequality
  >> gs[]
  >> qspecl_then [‘vMap’, ‘x’, ‘y’, ‘xs ++ [(q,n)]’, ‘ys ++ [(q',n)]’]
                 assume_tac vMap_length_equal_2_lemma
  >> gs[numVarMap_ok_def]
QED

Theorem zip_bvs_not_empty_lemma:
  ∀ x y.
    LENGTH x = LENGTH y ∧
    x ≠ [] ⇒
    ZIP (vMap_to_orderBool x, vMap_to_orderBool y) ≠ []
Proof
  Induct
  >- gs[]
  >> Induct_on‘y’
  >- gs[]
  >> rw[]
  >> Cases_on‘h’
  >> Cases_on‘h'’
  >> rw[vMap_to_orderBool_def, ZIP_def]
QED

Theorem zip_empty_lemma:
  ∀ t t'.
    LENGTH t = LENGTH t' ∧
    ZIP (vMap_to_orderBool t,vMap_to_orderBool t') = [] ⇒
    t = [] ∧ t' = []
Proof
  rw[]
  >> Cases_on ‘t’ >> Cases_on ‘t'’ >> gvs[]
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> gvs[vMap_to_orderBool_def]
QED

Theorem lEq_preserves_sat:
  ∀ bvs bxs xs bys ys x y vMap w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NLeq x y) ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (xs ++ bxs) ∧
    ALOOKUP vMap y = SOME (ys ++ bys) ∧
    LENGTH bxs = LENGTH bys ∧
    bvs = ZIP (vMap_to_orderBool bxs, vMap_to_orderBool bys) ∧
    bvs ≠ [] ∧
    LIST_REL (λ (bvx, vx) (bvy, vy). w' y ≤ vy ⇒ w' x ≤ vx) xs ys
    ⇒
    (w' x ≤ w' y ⇔
       eval_orderBool
       (encode_assignment w w' vMap)
       (encode_leq bvs))
Proof
  Induct
  >- rw[encode_leq_def, eval_orderBool_def]
  >> rw[]
  >> Cases_on ‘h’
  >> Cases_on ‘bxs’
  >- gs[vMap_to_orderBool_def]
  >> Cases_on ‘bys’ >> gs[]
  >> Cases_on ‘h’
  >> Cases_on ‘h'’
  >> gs[vMap_to_orderBool_def]
  >> rw[encode_leq_def]
  >> rw[eval_orderBool_def]
  >> rw[eval_literal_def]
  >> rw[encode_assignment_def]
  >> qspecl_then [‘vMap’, ‘xs ++ (q',r')::t’, ‘x’, ‘q'’, ‘r'’]
                 assume_tac alookup_el_lemma
  >> qspecl_then [‘vMap’, ‘ys ++ (q'',r'')::t'’, ‘y’, ‘q''’, ‘r''’]
                 assume_tac alookup_el_lemma
  >> gs[]
  >> qspecl_then
     [‘vMap’, ‘x’, ‘xs’, ‘q'’, ‘r'’, ‘t’, ‘y’, ‘ys’, ‘q''’, ‘r''’, ‘t'’]
     assume_tac values_equal_lemma
  >> gs[]
  >> last_x_assum
     (qspecl_then
      [‘t’, ‘xs ++ [(q', r')]’, ‘t'’, ‘ys ++ [(q'', r'')]’,
       ‘x’, ‘y’, ‘vMap’, ‘w’, ‘w'’]
      assume_tac)
  >> gs[]
  >> Cases_on ‘ZIP (vMap_to_orderBool t,vMap_to_orderBool t') = []’ >> gs[]
  >- (rw[encode_leq_def, eval_orderBool_def]
      >> qspecl_then
         [‘w'’, ‘x’, ‘y’, ‘r'’, ‘vMap’, ‘xs’, ‘ys’, ‘q'’, ‘q''’]
         assume_tac leq_const_highest_value_lemma
      >> gs[]
      >> metis_tac[zip_empty_lemma])
  >> gs[]
  >> Cases_on ‘w' y ≤ r'' ⇒ w' x ≤ r''’
  >- gs[]
  >> gs[]
QED


(* ------------------- Theorems about NAdd ------------------------------ *)

Theorem vMap_to_orderBool_append:
  ∀ l q r.
    vMap_to_orderBool (l ++ [(q,r)]) =
    vMap_to_orderBool l ++ vMap_to_orderBool [(q,r)]
Proof
  Induct
  >> gvs[vMap_to_orderBool_def]
  >> rw[]
  >> first_x_assum (qspecl_then [‘q’, ‘r’] assume_tac)
  >> Cases_on‘h’
  >> gvs[vMap_to_orderBool_def, PAIR]
QED

Theorem vMap_to_orderBool_reverse_append:
  ∀ l q r.
  vMap_to_orderBool (REVERSE l ++ [(q,r)]) =
    (vMap_to_orderBool (REVERSE l) ++
    vMap_to_orderBool [(q, r)])
Proof
  gvs[vMap_to_orderBool_append]
QED

Theorem reverse_vMap_to_orderBool_flip:
  ∀ l.
    REVERSE (vMap_to_orderBool l) = vMap_to_orderBool (REVERSE l)
Proof
  Induct
  >- gs[SWAP_REVERSE_SYM, vMap_to_orderBool_def]
  >> gs[SWAP_REVERSE_SYM]
  >> Cases_on‘h’
  >> gs[vMap_to_orderBool_def]
  >> gvs[vMap_to_orderBool_reverse_append, vMap_to_orderBool_def]
QED

Theorem vMap_orderBool_snoc_lemma:
  ∀l x0 x1.
  vMap_to_orderBool (SNOC (x0,x1) l) =
  SNOC (OLit (INL x0)) (vMap_to_orderBool l)
Proof
  Induct
  >> gs[vMap_to_orderBool_def]
  >> Cases_on‘h’
  >> gs[vMap_to_orderBool_def]
QED

Definition bool_comb_def:
  bool_comb w xs ys =
  EXISTS (λ ((bx, vx), (by, vy)). w bx ∧ w by)
         (ZIP (xs, (REVERSE ys)))
End

Definition bool_combs_def:
  bool_combs w xs ys [] = T ∧
  bool_combs w xs ys ((bz, vz)::bzs) =
  ((w bz ⇔
   bool_comb w xs ys) ∧
   bool_combs w (TL xs) (TL ys) bzs)
End

Theorem eval_orderBool_lemma:
  ∀ (xs: (num # num) list) (ys: (num # num) list) w.
  LENGTH xs = LENGTH ys ⇒
  eval_orderBool
  w (encode_combinations
     (vMap_to_orderBool xs) (vMap_to_orderBool ys)) =
  bool_comb w xs ys
Proof
  Induct
  >- gvs[encode_combinations_def, vMap_to_orderBool_def,
         eval_orderBool_def, bool_comb_def]
  >> rw[]
  >> Cases_on ‘ys’ using SNOC_CASES
  >- gvs[]
  >> PairCases_on ‘h’
  >> PairCases_on ‘x’
  >> Cases_on ‘vMap_to_orderBool (l ++ [(x0,x1)]) = []’
  >- (‘LENGTH (vMap_to_orderBool (l ++ [(x0,x1)])) = LENGTH (l ++ [(x0,x1)])’
        by gvs[vMap_orderBool_same_size_lemma]
      >> gvs[])
  >> gvs[vMap_to_orderBool_def, encode_combinations_def, bool_comb_def]
  >> gvs[vMap_orderBool_snoc_lemma]
  >> gvs[eval_orderBool_def, eval_literal_def, REVERSE_SNOC]
QED

Theorem eval_orderBool_encode_add_lemma:
  ∀ (zs: (num # num) list) (xs: (num # num) list) (ys: (num # num) list) w.
    LENGTH xs = LENGTH ys ∧
    LENGTH zs = LENGTH xs ⇒
    eval_orderBool
    w (encode_add
       (vMap_to_orderBool xs) (vMap_to_orderBool ys) (vMap_to_orderBool zs)) =
    bool_combs w xs ys zs
Proof
  Induct
  >> gvs[vMap_to_orderBool_def, bool_combs_def,
         encode_add_def, eval_orderBool_def]
  >> Cases_on ‘xs’ >> Cases_on ‘ys’ >> gvs[]
  >> gvs[vMap_to_orderBool_def, bool_combs_def,
         encode_add_def, eval_orderBool_def]
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> gvs[]
  >> gvs[vMap_to_orderBool_def, bool_combs_def,
         encode_add_def, eval_orderBool_def]
  >> gvs[eval_orderBool_lemma, eval_literal_def]
  >> rw[]
  >> qspecl_then [‘(q,r)::t’, ‘(q',r')::t'’, ‘w’]
                 assume_tac eval_orderBool_lemma
  >> gvs[vMap_to_orderBool_def]
QED

Theorem all_numBools_false:
  ∀ bzs vMap w w' z n.
    w' z ≥ LENGTH bzs + n ∧
    MAP SND bzs = GENLIST (λ x. n + x) (LENGTH bzs) ∧
    EVERY (λ(bx,vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (z,vx)) bzs ⇒
    EVERY (λ (bz, vz). ((encode_assignment w w' vMap) bz ⇔ F)) bzs
Proof
  Induct
  >> gvs[]
  >> rw[]
  >- (Cases_on‘h’
      >> rw[]
      >> gvs[encode_assignment_def, GENLIST_CONS])
  >> gvs[GENLIST_CONS]
  >> last_x_assum
     (qspecl_then [‘vMap’, ‘w’, ‘w'’, ‘z’, ‘SUC (SND h)’] assume_tac)
  >> gvs[]
  >> gs[GENLIST_FUN_EQ]
QED

Theorem mem_first_zip:
  ∀ t t' p_1 p_2 p_1' p_2'.
  MEM ((p_1,p_2),p_1',p_2') (ZIP (t,t')) ⇒ MEM (p_1, p_2) t
Proof
  Induct
  >> Cases_on‘t'’
  >> gvs[ZIP_def]
  >> rw[]
  >> last_x_assum
     (qspecl_then [‘t''’, ‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
  >> gvs[]
QED

Theorem mem_first_zip_2:
  ∀t p_1 p_2 p_1' p_2' q ys vMap w w'.
    LENGTH ys = SUC (LENGTH t) ∧
    MEM ((p_1,p_2),p_1',p_2') (ZIP ((q,LENGTH t)::t,REVERSE ys)) ∧
    (MEM (p_1,p_2) t ⇒ ¬encode_assignment w w' vMap p_1) ∧
    ¬encode_assignment w w' vMap q ⇒
    ¬encode_assignment w w' vMap p_1
Proof
  rw[]
  >> Cases_on‘REVERSE ys’
  >> gvs[ZIP_def, REVERSE_DEF, APPEND]
  >> metis_tac[mem_first_zip]
QED

Theorem x_all_false:
  ∀t ys h w w' vMap x y.
  EVERY (λ(bx,vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) t ∧
  (λ(bx,vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) h ∧
  EVERY (λ(by,vy). ALOOKUP (invert_numVarMap vMap) by = SOME (y,vy)) ys ∧
  SND h = LENGTH t ∧
  MAP SND (REVERSE ys) = GENLIST I (LENGTH t) ++ [LENGTH t] ∧
  MAP SND (REVERSE t) = GENLIST I (LENGTH t) ∧
  LENGTH ys = SUC (LENGTH t) ∧
  ¬(w' x < SUC (LENGTH t)) ⇒
  ¬bool_comb (encode_assignment w w' vMap) (h::t) ys
Proof
  rw[]
  >> qspecl_then [‘REVERSE (h::t)’, ‘vMap’, ‘w’, ‘w'’, ‘x’, ‘0’]
                 assume_tac all_numBools_false
  >> gvs[EVERY_REVERSE, GENLIST, GSYM ADD1]
  >> ‘GENLIST I (LENGTH t) = GENLIST (λx'. x') (LENGTH t)’ by metis_tac[]
  >> gvs[bool_comb_def]
  >> gvs[o_DEF]
  >> gvs[EVERY_MEM, FORALL_PROD, MEM_MAP]
  >> rw[]
  >> Cases_on ‘h’
  >> first_x_assum (qspecl_then [‘p_1’, ‘p_2’] assume_tac)
  >> gvs[]
  >> metis_tac[mem_first_zip_2]
QED

Theorem bool_comb_not_true:
  ∀ xs l x w w' vMap.
    xs ≠ [] ∧
    ¬(w' x < LENGTH xs) ∧
    MAP SND (REVERSE xs) = GENLIST I (LENGTH xs) ∧
    (∀p_1 p_2. MEM (p_1,p_2) xs ⇒
               ALOOKUP (invert_numVarMap vMap) p_1 = SOME (x,p_2)) ⇒
    (∀p_1 p_2 p_1' p_2'.
       MEM ((p_1,p_2),p_1',p_2') (ZIP (xs,REVERSE l)) ⇒
       ¬(case ALOOKUP (invert_numVarMap vMap) p_1 of
           NONE => w p_1
         | SOME (x,v) => w' x ≤ v) ∨
       ¬case ALOOKUP (invert_numVarMap vMap) p_1' of
       NONE => w p_1'
     | SOME (x,v) => w' x ≤ v)
Proof
  Induct >> rw[]
  >> Cases_on ‘l’ using SNOC_CASES
  >- gs[ZIP_def]
  >> gs[REVERSE_SNOC]
  >- (Cases_on ‘h’
      >> gs[]
      >> last_x_assum (qspecl_then [‘q’, ‘r’] assume_tac)
      >> gs[]
      >> gs[GENLIST])
  >> last_x_assum (qspecl_then [‘l'’, ‘x’, ‘w’, ‘w'’, ‘vMap’] assume_tac)
  >> gs[]
  >> gs[GENLIST]
  >> Cases_on ‘xs = []’ >> gs[]
  >- gs[ZIP_def]
  >> metis_tac[]
QED

Theorem bool_comb_meaning:
  ∀ xs ys x y n w w' vMap.
    EVERY (λ (bx, vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) xs ∧
    EVERY (λ (by, vy). ALOOKUP (invert_numVarMap vMap) by = SOME (y,vy)) ys ∧
    MAP SND (REVERSE xs) = GENLIST I (LENGTH xs) ∧
    MAP SND (REVERSE ys) = GENLIST (λ x. x + n) (LENGTH ys) ∧
    xs ≠ [] ∧
    w' x < LENGTH xs ∧
    LENGTH ys = LENGTH xs ⇒
    (bool_comb (encode_assignment w w' vMap) xs ys ⇔
     w' x + w' y ≤ SND (HD xs) + n)
Proof
  Induct >> rw[]
  >> Cases_on ‘ys’ using SNOC_CASES >> rw[]
  >- gs[]
  >> gs[bool_comb_def]
  >> gs[REVERSE_SNOC]
  >> Cases_on ‘h’
  >> Cases_on ‘x'’
  >> gs[]
  >> gs[EVERY_SNOC]
  >> gs[GENLIST]
  >> gs[GSYM ADD1, GENLIST_CONS]
  >> last_x_assum
     (qspecl_then [‘l’, ‘x’, ‘y’, ‘n + 1’, ‘w’, ‘w'’, ‘vMap’] assume_tac)
  >> gs[]
  >> Cases_on ‘xs = []’ >> gs[]
  >- (gs[ZIP_def]
      >> gs[encode_assignment_def])
  >> gs[encode_assignment_def]
  >> Cases_on ‘w' y ≤ n’ >> gs[]
  >> Cases_on ‘w' x < LENGTH xs’ >> gs[]
  >- (Cases_on ‘xs’ >> gs[]
      >> gs[GENLIST]
      >> gs[GSYM ADD1]
      >> metis_tac[])
  >> ‘w' x = LENGTH xs’ by gs[]
  >> gs[EVERY_MEM]
  >> gs[FORALL_PROD]
  >> qspecl_then [‘xs’, ‘l’, ‘x’, ‘w’, ‘w'’, ‘vMap’]
                 assume_tac bool_comb_not_true
  >> gs[]
QED

Theorem bool_comb_meaning_2:
  ∀ xs ys x y w w' vMap.
    EVERY (λ (bx, vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) xs ∧
    EVERY (λ (by, vy). ALOOKUP (invert_numVarMap vMap) by = SOME (y,vy)) ys ∧
    MAP SND (REVERSE xs) = GENLIST I (LENGTH xs) ∧
    MAP SND (REVERSE ys) = GENLIST I (LENGTH ys) ∧
    xs ≠ [] ∧
    LENGTH ys = LENGTH xs ⇒
    (bool_comb (encode_assignment w w' vMap) xs ys ⇔
     w' x + w' y ≤ SND (HD xs))
Proof
  rw[]
  >> Cases_on ‘w' x < LENGTH xs’
  >- (qsuff_tac ‘bool_comb (encode_assignment w w' vMap) xs ys ⇔
                   w' x + w' y ≤ SND (HD xs) + 0’
      >- gvs[]
      >> irule bool_comb_meaning
      >> gvs[]
      >> metis_tac[])
  >> Cases_on ‘xs’
  >- gvs[GENLIST]
  >> gvs[GENLIST]
  >> metis_tac[x_all_false]
QED

Theorem add_eq_lemma:
  ∀(a: num) b c k.
    a < k ∧ b < k ∧ c < k ⇒
    (a + b = c ⇔ ∀n. n < k ⇒ (a + b ≤ n ⇔ c ≤ n))
Proof
  rw[]
  >> Cases_on ‘c = a + b’ >> gvs[]
  >> ‘c < a + b ∨ a + b < c’ by gvs[]
  >> fs [] >> gvs []
  >- (qexists_tac ‘c’ >> gvs [])
  >- (qexists_tac ‘a+b’ >> gvs [])
QED

Theorem suc_p_k_lemma:
  (∀n. n < SUC k ⇒ p n) ⇔
    p k ∧ (∀n. n < k ⇒ p n)
Proof
  eq_tac >> rw[]
  >> Cases_on ‘n < k’ >> gvs[]
  >> ‘n = k’ by gvs[]
  >> metis_tac[]
QED

Theorem bool_combs_meaning:
  ∀ zs xs ys vMap w w' x y z.
    EVERY (λ (bx, vx). ALOOKUP (invert_numVarMap vMap) bx = SOME (x,vx)) xs ∧
    EVERY (λ (by, vy). ALOOKUP (invert_numVarMap vMap) by = SOME (y,vy)) ys ∧
    EVERY (λ (bz, vz). ALOOKUP (invert_numVarMap vMap) bz = SOME (z,vz)) zs ∧
    MAP SND (REVERSE xs) = GENLIST I (LENGTH xs) ∧
    MAP SND (REVERSE ys) = GENLIST I (LENGTH ys) ∧
    MAP SND (REVERSE zs) = GENLIST I (LENGTH zs) ∧
    LENGTH ys = LENGTH xs ∧
    LENGTH zs = LENGTH xs ⇒
    (bool_combs (encode_assignment w w' vMap) xs ys zs ⇔
    (∀n. n < (LENGTH zs) ⇒ (w' x + w' y ≤ n ⇔ w' z ≤ n)))
Proof
  Induct >- gvs[bool_combs_def]
  >> Cases_on ‘xs’ >> gvs[]
  >> Cases_on ‘ys’ >> gvs[]
  >> rw[]
  >> Cases_on ‘h’
  >> Cases_on ‘h'’
  >> Cases_on ‘h''’
  >> gvs[bool_combs_def]
  >> gvs[suc_p_k_lemma]
  >> irule (METIS_PROVE [] “a = b ∧ c = d ⇒ (a ∧ c ⇔ b ∧ d)”)
  >> rw[]
  >- (qspecl_then [‘(q,r)::t’, ‘(q',r')::t'’, ‘x’, ‘y’, ‘w’, ‘w'’, ‘vMap’]
      mp_tac bool_comb_meaning_2
      >> impl_tac >- gvs[]
      >> rw[encode_assignment_def]
      >> gvs[GENLIST])
  >> last_x_assum irule
  >> gvs[GENLIST]
QED

Theorem genlist_lemma:
  ∀ vMap x t xs.
    numVarMap_ok vMap ∧
    ALOOKUP vMap x = SOME (REVERSE t ++ xs) ⇒
    MAP SND (REVERSE t) = GENLIST (λ x'. x') (LENGTH t)
Proof
  rw[]
  >> gvs[numVarMap_ok_def, EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS]
  >> ‘MEM (x, (REVERSE t ++ xs)) vMap’ by gvs[ALOOKUP_MEM]
  >> first_x_assum (qspecl_then [‘(REVERSE t ++ xs)’,‘x’] assume_tac)
  >> gvs[]
  >> ‘GENLIST I (LENGTH t + (LENGTH xs)) =
      GENLIST I ((LENGTH xs) + LENGTH t)’ by gvs[]
  >> gvs[GENLIST_APPEND, APPEND_EQ_CONS, APPEND_11_LENGTH]
  >> metis_tac[]
QED

Theorem add_preserves_sat_2:
  ∀ bzs bys bxs xs ys zs x y z vMap w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NAdd x y z) ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (REVERSE bxs ++ xs) ∧
    ALOOKUP vMap y = SOME (REVERSE bys ++ ys) ∧
    ALOOKUP vMap z = SOME (REVERSE bzs ++ zs) ∧
    LENGTH bxs = LENGTH bzs ∧
    LENGTH bys = LENGTH bzs ∧
    w' x < LENGTH bxs ∧
    w' y < LENGTH bys ∧
    w' z < LENGTH bzs ∧
    bool_combs
    (encode_assignment w w' vMap)
    (REVERSE xs ++ bxs) (REVERSE ys ++ bys) (REVERSE zs) ⇒
    (w' x + w' y = w' z ⇔
       eval_orderBool
       (encode_assignment w w' vMap)
       (encode_add
        (vMap_to_orderBool bxs)
        (vMap_to_orderBool bys)
        (vMap_to_orderBool bzs)))
Proof
  gvs[eval_orderBool_encode_add_lemma]
  >> rw[]
  >> qspecl_then [‘bzs’, ‘bxs’, ‘bys’, ‘vMap’, ‘w’, ‘w'’, ‘x’, ‘y’, ‘z’]
                 assume_tac bool_combs_meaning
  >> qspecl_then [‘REVERSE bzs ++ zs’, ‘z’, ‘w'’, ‘vMap’]
                 assume_tac all_alookup
  >> qspecl_then [‘REVERSE bxs ++ xs’, ‘x’, ‘w'’, ‘vMap’]
                 assume_tac all_alookup
  >> qspecl_then [‘REVERSE bys ++ ys’, ‘y’, ‘w'’, ‘vMap’]
                 assume_tac all_alookup
  >> gs[EVERY_REVERSE]
  >> qspecl_then [‘vMap’, ‘x’, ‘bxs’, ‘xs’] assume_tac genlist_lemma
  >> qspecl_then [‘vMap’, ‘y’, ‘bys’, ‘ys’] assume_tac genlist_lemma
  >> qspecl_then [‘vMap’, ‘z’, ‘bzs’, ‘zs’] assume_tac genlist_lemma
  >> gvs[]
  >> qspecl_then [‘w' x’, ‘w' y’, ‘w' z’, ‘LENGTH bzs’]
                 assume_tac add_eq_lemma
  >> gvs[]
  >> metis_tac[]
QED

Theorem add_preserves_sat:
  ∀ bxs bys bzs x y z vMap w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap (NAdd x y z) ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME bxs ∧
    ALOOKUP vMap y = SOME bys ∧
    ALOOKUP vMap z = SOME bzs ⇒
    (w' x + w' y = w' z ⇔
       eval_orderBool
       (encode_assignment w w' vMap)
       (encode_add
        (REVERSE (vMap_to_orderBool bxs))
        (REVERSE (vMap_to_orderBool bys))
        (REVERSE (vMap_to_orderBool bzs))))
Proof
  rw[]
  >> qspecl_then [‘REVERSE bzs’, ‘REVERSE bys’, ‘REVERSE bxs’,
                  ‘[]’, ‘[]’, ‘[]’, ‘x’, ‘y’, ‘z’, ‘vMap’, ‘w’, ‘w'’]
                 mp_tac add_preserves_sat_2
  >> rw[]
  >> qspecl_then [‘vMap’, ‘z’] assume_tac vMap_no_empty_lists_lemma
  >> gs[]
  >> qspecl_then [‘vMap’, ‘x’, ‘z’, ‘bxs’, ‘bzs’]
                 assume_tac vMap_length_equal_2_lemma
  >> qspecl_then [‘vMap’, ‘y’, ‘z’, ‘bys’, ‘bzs’]
                 assume_tac vMap_length_equal_2_lemma
  >> gs[numVarMap_ok_def]
  >> gs[bool_combs_def]
  >> rw[reverse_vMap_to_orderBool_flip]
  >> gs[numVarAssignment_ok_def]
  >> gs[EVERY_MEM, FORALL_PROD]
  >> metis_tac[ALOOKUP_MEM]
QED


(* -------------- Theorems about numVarMap_created_ok ----------------------- *)

Theorem map_fst_equal_vList_vMap:
  ∀ (l:num list) next len.
    l = MAP FST (create_numVarMap_inner next len l)
Proof
  Induct >> rw[create_numVarMap_inner_def]
QED

Theorem all_variables_distinct:
  ∀ l k e.
    numVarList_ok (l, k) ∧
    exp_numVarList_ok (l, k) e ⇒
    ALL_DISTINCT (MAP FST (create_numVarMap e (l, k)))
Proof
  Induct >> rw[create_numVarMap_def, create_numVarMap_inner_def]
  >> gs[numVarList_ok_def]
  >> metis_tac[map_fst_equal_vList_vMap]
QED

Theorem empty_lists_different_bvs:
  ∀ l next next' len.
    EVERY (λ(_,l). l ≠ []) (create_numVarMap_inner next len l) ⇒
    EVERY (λ(_,l). l ≠ []) (create_numVarMap_inner next' len l)
Proof
  Induct >> rw[create_numVarMap_inner_def]
  >- rw[GENLIST]
  >> metis_tac[]
QED

Theorem no_empty_bvs:
  ∀ l k e.
    numVarList_ok (l, k) ⇒
    EVERY (λ(_,l). l ≠ []) (create_numVarMap e (l, k))
Proof
  Induct >> gs[create_numVarMap_def, create_numVarMap_inner_def]
  >> rw[]
  >- rw[GENLIST]
  >> gs[numVarList_ok_def]
  >> metis_tac[empty_lists_different_bvs]
QED

Theorem length_equal_different_bvs:
  ∀ l k next next'.
    EVERY (λ(_,bvs). LENGTH bvs = SUC k) (create_numVarMap_inner next k l) ⇒
    EVERY (λ(_,bvs). LENGTH bvs = SUC k) (create_numVarMap_inner next' k l)
Proof
  Induct
  >- rw[create_numVarMap_inner_def]
  >> rw[create_numVarMap_inner_def]
  >> metis_tac[]
QED

Theorem length_k:
  ∀ l k e.
    EVERY (λ(_, bvs). LENGTH bvs = SUC k) (create_numVarMap e (l, k))
Proof
  Induct
  >- rw[create_numVarMap_def, create_numVarMap_inner_def]
  >> rw[]
  >> gs[create_numVarMap_def, create_numVarMap_inner_def]
  >> metis_tac[length_equal_different_bvs]
QED

Theorem vMap_all_same_length:
  ∀ l k e.
    numVarList_ok (l, k) ∧
    exp_numVarList_ok (l, k) e ⇒
    all_the_same_length (create_numVarMap e (l, k))
Proof
  rw[all_the_same_length_def]
  >> metis_tac[length_k]
QED

Theorem all_distinct_boolVars_first_numVar:
  ∀ k m.
    ALL_DISTINCT (MAP FST (GENLIST (λn. (n + m, n)) (SUC k)))
Proof
  Induct >> rw[]
  >> gs[GENLIST, MAP_SNOC, ALL_DISTINCT_SNOC, MAP_GENLIST, MEM_GENLIST]
QED

Theorem not_mem_boolVars:
  ∀ l k next' e m.
    MEM e (MAP FST (GENLIST (λn. (n + next',n)) (SUC k))) ⇒
    ¬MEM e (MAP FST (FLAT (MAP SND (create_numVarMap_inner (next' + m + SUC k) k l))))
Proof
  Induct
  >- rw[create_numVarMap_inner_def]
  >> rw[create_numVarMap_inner_def, MAP_GENLIST]
  >- gs[MEM_GENLIST]
  >> last_x_assum (qspecl_then [‘k’, ‘next'’, ‘e’, ‘m + SUC k’] mp_tac)
  >> gs[MAP_GENLIST]
QED

Theorem all_distinct_boolVars_different_next:
  ∀ l k next next'.
    ALL_DISTINCT (MAP FST (FLAT (MAP SND (create_numVarMap_inner next k l)))) ⇒
    ALL_DISTINCT (MAP FST (FLAT (MAP SND (create_numVarMap_inner next' k l))))
Proof
  Induct >> gs[create_numVarMap_inner_def]
  >> rw[ALL_DISTINCT_APPEND]
  >- rw[all_distinct_boolVars_first_numVar]
  >- metis_tac[]
  >> qspecl_then [‘l’, ‘k’, ‘next'’, ‘e’, ‘0’] assume_tac not_mem_boolVars
  >> gs[]
QED

Theorem all_distinct_boolVars:
  ∀ l k e.
    ALL_DISTINCT (MAP FST (FLAT (MAP SND (create_numVarMap e (l, k)))))
Proof
  Induct >> gs[create_numVarMap_def, create_numVarMap_inner_def]
  >> rw[ALL_DISTINCT_APPEND]
  >- rw[all_distinct_boolVars_first_numVar]
  >- metis_tac[all_distinct_boolVars_different_next]
  >> qspecl_then [‘l’, ‘k’, ‘get_fresh_boolVar e’, ‘e'’, ‘0’]
                 mp_tac not_mem_boolVars
  >> rw[]
QED

Theorem all_values_correct_2:
  ∀ l k next.
    EVERY (λl. MAP SND l = GENLIST I (LENGTH l))
          (MAP SND (create_numVarMap_inner next k l))
Proof
  Induct >> rw[create_numVarMap_inner_def]
  >> Induct_on ‘k’ >> gs[GENLIST]
QED

Theorem all_values_correct:
  ∀ l k e.
    numVarList_ok (l, k) ∧
    exp_numVarList_ok (l, k) e ⇒
    EVERY (λl. MAP SND l = GENLIST I (LENGTH l))
          (MAP SND (create_numVarMap e (l, k)))
Proof
  rw[create_numVarMap_def, all_values_correct_2]
QED

Theorem not_mem_genlist:
  ∀ k m n.
    ¬MEM n (MAP FST (GENLIST (λn'. (m + (n + (n' + 1)), n')) k))
Proof
  Induct >> rw[GENLIST, MAP_SNOC]
QED

Theorem not_mem_vMap:
  ∀ l k n m.
    ¬MEM n (MAP FST (FLAT (MAP SND (create_numVarMap_inner (n + m + 1) k l))))
Proof
  Induct >> rw[create_numVarMap_inner_def]
  >- rw[not_mem_genlist]
  >> pop_assum (qspecl_then [‘k’, ‘n’, ‘m + SUC k’] assume_tac)
  >> gs[]
QED

Theorem mem_numVarList_implies_mem_numVarMap:
  ∀ l n n' k.
    MEM n l ⇒
    MEM n (MAP FST (create_numVarMap_inner n' k l))
Proof
  Induct >> rw[]
  >> rw[create_numVarMap_inner_def]
QED

Theorem varMap_ok_greater_boolVars:
  ∀ e n k l.
    exp_numVarList_ok (l,k) e ∧
    get_fresh_boolVar e < n ⇒
    exp_numVarMap_ok (create_numVarMap_inner n k l) e
Proof
  Induct >> rw[exp_numVarMap_ok_def, get_fresh_boolVar_def,
               exp_numVarList_ok_def]
  >- (qspecl_then [‘l’, ‘k’, ‘n’, ‘n' - n - 1’] assume_tac not_mem_vMap
      >> gs[])
  >> rw[mem_numVarList_implies_mem_numVarMap]
QED

Theorem mem_fst_numVarMap_different_bvs:
  ∀ l k m m' n.
    MEM n (MAP FST (create_numVarMap_inner m k l)) ⇒
    MEM n (MAP FST (create_numVarMap_inner m' k l))
Proof
  Induct
  >- rw[create_numVarMap_inner_def]
  >> rw[create_numVarMap_inner_def]
  >> metis_tac[]
QED

Theorem exp_numVarMap_max_boolVar:
  ∀ e n k l.
    exp_numVarList_ok (l,k) e ∧
    exp_numVarMap_ok
    (create_numVarMap_inner (get_fresh_boolVar e) k l) e ⇒
    exp_numVarMap_ok
    (create_numVarMap_inner (MAX (get_fresh_boolVar e) n) k l) e
Proof
  Induct >> gs[exp_numVarMap_ok_def, get_fresh_boolVar_def]
  >- (rw[]
      >> Cases_on ‘n + 1 > n'’ >> rw[MAX_DEF]
      >> qspecl_then [‘l’, ‘k’, ‘n’, ‘n' - n - 1’] assume_tac not_mem_vMap
      >> gs[])
  >- rw[MAX_DEF, exp_numVarList_ok_def]
  >> TRY (rw[MAX_DEF, exp_numVarList_ok_def]
          >> rw[varMap_ok_greater_boolVars]
          >> NO_TAC)
  >> (rw[]
      >> metis_tac[mem_fst_numVarMap_different_bvs])
QED

Theorem exp_numVarMap_created_ok:
  ∀ e l k.
    numVarList_ok (l, k) ∧
    exp_numVarList_ok (l, k) e ⇒
    exp_numVarMap_ok (create_numVarMap e (l, k)) e
Proof
  Induct >> gs[exp_numVarMap_ok_def, create_numVarMap_def,
               create_numVarMap_inner_def,
               get_fresh_boolVar_def, exp_numVarList_ok_def]
  >- (rw[]
      >> qspecl_then [‘l’, ‘k’, ‘n’, ‘0’] assume_tac not_mem_vMap
      >> gs[])
  >- metis_tac[exp_numVarMap_max_boolVar, MAX_COMM]
  >- metis_tac[exp_numVarMap_max_boolVar, MAX_COMM]
  >- metis_tac[exp_numVarMap_max_boolVar, MAX_COMM]
  >- metis_tac[exp_numVarMap_max_boolVar, MAX_COMM]
  >> rw[mem_numVarList_implies_mem_numVarMap]
QED

Theorem numVarMap_created_ok:
  ∀ e l vMap.
    numVarList_ok l ∧
    exp_numVarList_ok l e ∧
    vMap = create_numVarMap e l ⇒
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap e
Proof
  Cases_on ‘l’
  >> rw[numVarMap_ok_def]
  >- rw[all_variables_distinct]
  >- rw[no_empty_bvs]
  >- rw[vMap_all_same_length]
  >- rw[all_distinct_boolVars]
  >- rw[all_values_correct]
  >> rw[exp_numVarMap_created_ok]
QED

(* ------------- Theorems about numVarList created ok ------------------- *)

Theorem numVarList_ok_lemma:
  ∀e n l.
    ALL_DISTINCT l ⇒
    numVarList_ok (create_numVarList_inner l e,n)
Proof
  Induct
  >> rw[create_numVarList_inner_def, numVarList_ok_def, add_numVar_to_list_def]
  >> gs[numVarList_ok_def]
QED

Theorem exp_numVarList_ok_lemma:
  ∀ e e' n l.
    (∀ x. MEM x (create_numVarList_inner l e) ⇒
          MEM x (create_numVarList_inner l e')) ⇒
    exp_numVarList_ok (create_numVarList_inner l e', n) e
Proof
  Induct
  >> TRY(rw[exp_numVarList_ok_def, create_numVarList_inner_def]
         >> NO_TAC)
  >> (gs[exp_numVarList_ok_def, create_numVarList_inner_def,
         add_numVar_to_list_def]
      >> rw[]
      >> last_x_assum irule
      >> rw[]
      >> gs[])
QED

Theorem numVarList_created_ok:
  ∀e l n.
    (l = create_numVarList n e) ⇒
    (numVarList_ok l ∧
     exp_numVarList_ok l e)
Proof
  rw[]
  >- (qspecl_then [‘e’, ‘n’, ‘[]’] assume_tac numVarList_ok_lemma
      >> gs[create_numVarList_def])
  >> qspecl_then [‘e’, ‘e’, ‘n’, ‘[]’] assume_tac exp_numVarList_ok_lemma
  >> gs[create_numVarList_def]
QED


(* ----------------------- Theorems ---------------------------------- *)


Theorem numBoolExp_to_orderBool_preserves_sat:
  ∀ e vMap w w'.
    numVarMap_ok vMap ∧
    exp_numVarMap_ok vMap e ∧
    numVarAssignment_ok w' vMap ⇒
    eval_numBoolExp w w' e =
    eval_orderBool
    (encode_assignment w w' vMap)
    (numBoolExp_to_orderBool vMap e)
Proof
  Induct
  >> TRY (gs[eval_numBoolExp_def, numBoolExp_to_orderBool_def,
             eval_orderBool_def, eval_literal_def,
             encode_assignment_def, boolVar_not_in_vMap_lemma,
             exp_numVarMap_ok_def]
          >> metis_tac[]
          >> NO_TAC)
  (* NAdd *)
  >- (rw[numBoolExp_to_orderBool_def]
      >> gs[exp_numVarMap_ok_def]
      >> gs[numVarMap_ok_def]
      >> Cases_on ‘ALOOKUP vMap n’
      >- gs[vMap_mem_lemma]
      >> Cases_on ‘ALOOKUP vMap n0’
      >- gs[vMap_mem_lemma]
      >> Cases_on ‘ALOOKUP vMap n1’
      >- gs[vMap_mem_lemma]
      >> gs[]
      >> rw[eval_numBoolExp_def]
      >> irule add_preserves_sat
      >> rw[numVarMap_ok_def, exp_numVarMap_ok_def])
  (* NLeq *)
  >- (rw[eval_numBoolExp_def, numBoolExp_to_orderBool_def]
      >> Cases_on ‘ALOOKUP vMap n’
      >- gs[numVarMap_ok_def, exp_numVarMap_ok_def, vMap_mem_lemma]
      >> Cases_on ‘ALOOKUP vMap n0’
      >- gs[numVarMap_ok_def, exp_numVarMap_ok_def, vMap_mem_lemma]
      >> rw[]
      >> qspecl_then
         [‘ZIP (vMap_to_orderBool x, vMap_to_orderBool x')’, ‘x’,
          ‘[]’, ‘x'’, ‘[]’, ‘n’, ‘n0’, ‘vMap’, ‘w’, ‘w'’]
         mp_tac lEq_preserves_sat
      >> gs[]
      >> gs[numVarMap_ok_def]
      >> qspecl_then [‘vMap’, ‘n’, ‘n0’, ‘x’, ‘x'’]
                     assume_tac vMap_length_equal_2_lemma
      >> gs[]
      >> qspecl_then [‘vMap’, ‘n’] assume_tac vMap_no_empty_lists_lemma
      >> gs[numVarMap_ok_def]
      >> gs[zip_bvs_not_empty_lemma])
  (* NEqConst *)
  >- (rw[numBoolExp_to_orderBool_def, exp_numVarMap_ok_def, numVarMap_ok_def,
         eval_numBoolExp_def]
      >> Cases_on ‘ALOOKUP vMap n’
      >- gs[vMap_mem_lemma]
      >> gs[]
      >> qspecl_then [‘x’, ‘vMap’, ‘n’, ‘n0’, ‘w’, ‘w'’]
                     assume_tac eqConst_preserves_sat
      >> gvs[numVarMap_ok_def, exp_numVarMap_ok_def])
  (* NLeqConst *)
  >> rw[numBoolExp_to_orderBool_def, eval_numBoolExp_def]
  >> Cases_on ‘ALOOKUP vMap n’
  >- gs[vMap_mem_lemma, numVarMap_ok_def, exp_numVarMap_ok_def]
  >> gs[leqConst_preserves_sat]
QED

Theorem numBool_to_orderBool_preserves_sat:
  ∀ e w w' l.
    numVarList_ok l ∧
    exp_numVarList_ok l e ∧
    numVarAssignment_ok w' (create_numVarMap e l) ⇒
    eval_numBoolExp w w' e =
    eval_orderBool
    (encode_assignment w w' (create_numVarMap e l))
    (numBool_to_orderBool l e)
Proof
  rw[numBool_to_orderBool_def, eval_orderBool_def]
  >> qspecl_then [‘e’, ‘l’, ‘create_numVarMap e l’]
                 assume_tac numVarMap_created_ok
  >> gs[axioms_always_true, numBoolExp_to_orderBool_preserves_sat]
QED

Definition numBoolExp_to_assignment_def:
  numBoolExp_to_assignment
  (w:assignment) (w':numVarAssignment) (vList:numVarList) (e:numBoolExp) =
  orderBool_to_assignment
  (minimal_encode_assignment w w' vList e)
  (numBool_to_orderBool vList e)
End

Theorem all_values_ok_different_fresh_bv:
  ∀ vList k w' next next'.
    EVERY (λ(x,bvs). w' x < LENGTH bvs) (create_numVarMap_inner next k vList) =
    EVERY (λ(x,bvs). w' x < LENGTH bvs) (create_numVarMap_inner next' k vList)
Proof
  Induct >> rw[create_numVarMap_inner_def]
  >> metis_tac[]
QED

Theorem minimal_numVarAssignment_equal:
  ∀ w' e l.
    minimal_numVarAssignment_ok w' l ⇔
      numVarAssignment_ok w' (create_numVarMap e l)
Proof
  rw[minimal_numVarAssignment_ok_def]
  >> Cases_on ‘l’
  >> gs[]
  >> Induct_on ‘q’
  >- rw[create_numVarMap_def, create_numVarMap_inner_def,
        numVarAssignment_ok_def]
  >> rw[]
  >> gs[create_numVarMap_def, create_numVarMap_inner_def,
        numVarAssignment_ok_def]
  >> qspecl_then
     [‘q’, ‘r’, ‘w'’, ‘get_fresh_boolVar e’, ‘SUC r + get_fresh_boolVar e’]
     assume_tac all_values_ok_different_fresh_bv
  >> gs[LESS_EQ_IFF_LESS_SUC]
QED

Theorem numBool_to_cnf_preserves_sat:
  ∀ e vList w w'.
    numVarList_ok vList ∧
    exp_numVarList_ok vList e ∧
    minimal_numVarAssignment_ok w' vList ⇒
    (eval_numBoolExp w w' e ⇔
       eval_cnf
       (numBoolExp_to_assignment w w' vList e)
       (numBool_to_cnf vList e))
Proof
  rw[]
  >> imp_res_tac minimal_numVarAssignment_equal
  >> first_x_assum (qspecl_then [‘e’] assume_tac)
  >> qspecl_then [‘e’, ‘w’, ‘w'’, ‘vList’] assume_tac
                 numBool_to_orderBool_preserves_sat >> gs[]
  >> rw[numBool_to_cnf_def, numBoolExp_to_assignment_def,
        orderBool_to_cnf_preserves_sat]
  >> metis_tac[minimal_encode_assignment_def]
QED

Theorem imp_find_value_lt:
  ∀xs. EVERY (λ(k,m). m < n) xs ∧ n ≠ 0 ⇒
       find_value w xs < n
Proof
  Induct \\ fs [find_value_def, FORALL_PROD] \\ rw []
QED

Theorem find_value_le_lemma:
  ∀n m p_2.
    n < LENGTH p_2 ∧ EL n p_2 = (x,m) ∧ w x ∧
    (∀i. i ≤ n ⇒ ∃y k. EL i p_2 = (y,k) ∧ k ≤ m) ⇒
    find_value w p_2 ≤ m
Proof
  Induct_on ‘p_2’ \\ fs [] \\ strip_tac
  \\ PairCases_on ‘h’ \\ fs [find_value_def]
  \\ Cases \\ fs [] \\ rw []
  THEN1 (first_x_assum (qspec_then ‘0’ mp_tac) \\ fs [])
  \\ first_x_assum irule \\ fs []
  \\ first_x_assum (irule_at (Pos last)) \\ rw []
  \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ fs []
QED

Theorem MEM_encode_axioms:
  eval_orderBool w (encode_axioms vMap) ∧ MEM (p_1,p_2) vMap ⇒
  eval_orderAxiom w (MAP FST p_2)
Proof
  Induct_on ‘vMap’ \\ fs [FORALL_PROD] \\ rw []
  \\ fs [encode_axioms_def,eval_orderBool_def]
QED

Theorem find_value_append_lemma:
  eval_orderAxiom w (MAP FST ys1 ++ x::MAP FST t) ∧ ¬w x ⇒
  find_value w (ys1 ++ (x,m)::t) = find_value w t ∧
  eval_orderAxiom w (MAP FST t)
Proof
  Induct_on ‘ys1’ \\ fs [] \\ rw []
  \\ gvs [find_value_def,eval_orderAxiom_def]
  \\ PairCases_on ‘h’ \\ gvs [find_value_def]
QED

Theorem encode_assignment_cancel:
  numVarMap_ok vMap ∧ exp_numVarMap_ok vMap e ∧
  eval_orderBool w (encode_axioms vMap) ⇒
  encode_assignment w
    (assignment_to_numVarAssignment w vMap) vMap = w
Proof
  fs [encode_assignment_def,FUN_EQ_THM]
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [invert_numVarMap_def]
  \\ gvs [MEM_FLAT,MEM_MAP,EXISTS_PROD]
  \\ fs [assignment_to_numVarAssignment_def]
  \\ fs [numVarMap_ok_def]
  \\ drule_all ALOOKUP_ALL_DISTINCT_MEM
  \\ rw []
  \\ ‘MAP SND p_2 = GENLIST I (LENGTH p_2)’ by
   (fs [EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ first_x_assum irule \\ metis_tac [])
  \\ drule_at Any el_genlist_lemma
  \\ qpat_x_assum ‘MEM (x,r) p_2’ mp_tac
  \\ simp [MEM_EL] \\ rw []
  \\ qpat_x_assum ‘_  = EL n p_2’ (assume_tac o GSYM)
  \\ first_x_assum drule \\ gvs []
  \\ rw [] \\ gvs []
  \\ ‘p_2 ≠ []’ by (strip_tac \\ gvs [])
  \\ ‘∀i. i ≤ n ⇒ ∃y k. EL i p_2 = (y,k) ∧ k ≤ n’ by
        (rw [] \\ drule_at (Pos last) el_genlist_lemma
         \\ Cases_on ‘EL i p_2’ \\ fs []
         \\ ‘i < LENGTH p_2’ by fs []
         \\ disch_then drule \\ fs [])
  \\ Cases_on ‘w x’ \\ fs []
  THEN1 (drule_all find_value_le_lemma \\ fs [])
  \\ fs [GSYM NOT_LESS]
  \\ drule_all MEM_encode_axioms
  \\ fs [NOT_LESS]
  \\ ‘∀i. n < i ∧ i < LENGTH p_2 ⇒ ∃y k. EL i p_2 = (y,k) ∧ n < k’ by
        (rw [] \\ drule_at (Pos last) el_genlist_lemma
         \\ Cases_on ‘EL i p_2’ \\ fs []
         \\ ‘i < LENGTH p_2’ by fs []
         \\ disch_then drule \\ fs [])
  \\ ‘n ≤ LENGTH p_2’ by fs []
  \\ drule LESS_EQ_LENGTH
  \\ rfs [] \\ strip_tac \\ gvs []
  \\ ‘~NULL ys2’ by (Cases_on ‘ys2’ \\ fs [])
  \\ gvs [EL_LENGTH_APPEND]
  \\ Cases_on ‘ys2’ \\ gvs []
  \\ strip_tac
  \\ drule_all find_value_append_lemma \\ rw []
  \\ ‘EVERY (λ(y,k). LENGTH ys1 < k) t’ by
   (fs [EVERY_EL,FORALL_PROD] \\ rw []
    \\ qpat_x_assum ‘∀x._’ kall_tac
    \\ first_x_assum (qspec_then ‘LENGTH ys1 + SUC n’ mp_tac)
    \\ fs [] \\ fs [EL_APPEND2] \\ rw [] \\ fs [])
  \\ fs [GSYM PULL_FORALL]
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac ‘t’ \\ Induct \\ fs [eval_orderAxiom_def]
  \\ fs [FORALL_PROD,find_value_def] \\ rw []
QED

Definition to_numExp_assignment_def:
  to_numExp_assignment e vList w =
    assignment_to_numVarAssignment w (create_numVarMap e vList)
End

Theorem numBool_to_cnf_imp_sat:
  numVarList_ok vList ∧
  exp_numVarList_ok vList e ⇒
  eval_cnf w (numBool_to_cnf vList e) ⇒
  eval_numBoolExp w (to_numExp_assignment e vList w) e
Proof
  rw [numBool_to_cnf_def, numBool_to_orderBool_def, to_numExp_assignment_def]
  \\ drule orderBool_to_cnf_imp_sat \\ strip_tac
  \\ fs [eval_orderBool_def]
  \\ drule numBool_to_orderBool_preserves_sat
  \\ disch_then drule
  \\ qsuff_tac
     ‘numVarAssignment_ok (assignment_to_numVarAssignment w
        (create_numVarMap e vList)) (create_numVarMap e vList) ∧
      encode_assignment w
        (assignment_to_numVarAssignment w (create_numVarMap e vList))
        (create_numVarMap e vList) = w’
  THEN1 (strip_tac \\ disch_then drule \\ fs []
         \\ fs [numBool_to_orderBool_def,eval_orderBool_def])
  \\ reverse (rw [])
  THEN1
   (drule_all (SIMP_RULE std_ss [] numVarMap_created_ok) \\ rw []
    \\ irule encode_assignment_cancel
    \\ fs [] \\ metis_tac [])
  \\ rw [numVarAssignment_ok_def,EVERY_MEM,FORALL_PROD]
  \\ fs [assignment_to_numVarAssignment_def]
  \\ drule_all (SIMP_RULE std_ss [] numVarMap_created_ok)
  \\ fs [numVarMap_ok_def] \\ strip_tac
  \\ drule_all ALOOKUP_ALL_DISTINCT_MEM \\ rw []
  \\ irule imp_find_value_lt
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ first_x_assum drule
  \\ rw [] THEN1 (CCONTR_TAC \\ fs [])
  \\ drule_at Any el_genlist_lemma
  \\ pop_assum mp_tac
  \\ simp [MEM_EL] \\ rw []
  \\ first_x_assum drule \\ fs []
  \\ pop_assum (assume_tac o GSYM) \\ fs []
QED

Theorem imp_find_value_leq:
  ∀xs. EVERY (λ(k,m). m ≤ n) xs ⇒ find_value w xs ≤ n
Proof
  Induct \\ fs [find_value_def, FORALL_PROD] \\ rw []
QED

Theorem numBool_to_cnf_preserves_unsat:
  numVarList_ok vList ∧ exp_numVarList_ok vList e ⇒
  (unsat_numBoolExp (SND vList) e ⇔
   unsat_cnf (numBool_to_cnf vList e))
Proof
  rw [] \\ eq_tac \\ rw [unsat_numBoolExp_def,unsat_cnf_def] \\ strip_tac
  THEN1
   (drule numBool_to_cnf_imp_sat
    \\ disch_then drule
    \\ disch_then drule
    \\ fs [] \\ CCONTR_TAC \\ fs [to_numExp_assignment_def]
    \\ first_x_assum (qspec_then ‘w’ mp_tac) \\ fs []
    \\ first_x_assum $ irule_at Any
    \\ fs [assignment_to_numVarAssignment_def] \\ rw []
    \\ CASE_TAC \\ fs [create_numVarMap_def]
    \\ Cases_on ‘vList’ \\ fs []
    \\ pop_assum mp_tac
    \\ qspec_tac (‘get_fresh_boolVar e’,‘nn’)
    \\ qid_spec_tac ‘q’
    \\ Induct \\ fs [create_numVarMap_inner_def]
    \\ rw [] \\ res_tac \\ fs []
    \\ irule imp_find_value_leq \\ fs [EVERY_GENLIST])
  \\ drule numBool_to_cnf_preserves_sat
  \\ disch_then drule
  \\ ‘minimal_numVarAssignment_ok w' vList’ by fs [minimal_numVarAssignment_ok_def]
  \\ disch_then drule
  \\ strip_tac \\ gvs []
QED

(*

Theorem numBool_to_cnf_preserves_sat:
  ∀ w w' e l.
    numVarList_ok l ∧
    exp_numVarList_ok l e ∧
    numVarAssignment_ok w' (create_numVarMap e l) ⇒
    eval_numBoolExp w w' e =
    eval_cnf (encode_assignment w w' (create_numVarMap e l))
             (numBool_to_cnf l e)
Proof
  metis_tac[numBool_to_cnf_def ,numBool_to_orderBool_preserves_sat,
            orderBool_to_cnf_preserves_sat]
QED


(* -------------------------- Minimal numBool_to_cnf --------------------------

Theorem minimal_numBool_to_cnf_preserves_sat:
  ∀ w w' e l.
    numVarList_ok l ∧
    exp_numVarList_ok l e ∧
    minimal_numVarAssignment_ok w' l ⇒
    eval_numBoolExp w w' e =
    eval_cnf
    (minimal_encode_assignment w w' l e)
    (numBool_to_cnf l e)
Proof
  rw[]
  >> qspecl_then [‘w’, ‘w'’, ‘e’, ‘l’]
                 assume_tac numBool_to_cnf_preserves_sat
  >> qspecl_then [‘w'’, ‘e’, ‘l’] assume_tac minimal_numVarAssignment_equal
  >> metis_tac[minimal_encode_assignment_def]
QED


(* ---------------- Assignment encoding ok ------------------------------- *)

Theorem genlist_lemma_2:
  ∀ xs x y ys n.
    xs ++ [x; y] ++ ys =
    GENLIST (λ x. x + n) (LENGTH xs + LENGTH ys + 1 + 1) ⇒
    SUC x = y
Proof
  Induct
  >- (rw[GSYM ADD1]
      >> gs[GENLIST_CONS])
  >> rw[GSYM ADD1]
  >> last_x_assum irule
  >> qexists_tac ‘SUC n’
  >> qexists_tac ‘ys’
  >> rw[]
  >> pop_assum mp_tac
  >> rw[Once GENLIST_CONS]
  >> ‘SUC (LENGTH ys + SUC (LENGTH xs)) = LENGTH xs + (LENGTH ys + 2)’ by gs[]
  >> gs[ADD1, o_DEF]
QED

Theorem encode_assignment_meaning:
  ∀ xs xs' q r bvs x vMap w w'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (xs' ++ xs ++ (q,r)::bvs) ∧
    EVERY ($¬ ∘ encode_assignment w w' vMap) (MAP FST xs) ∧
    EVERY (λ (bv, v). ¬(w' x ≤ v)) xs' ∧
    encode_assignment w w' vMap q ⇒
    w' x = r
Proof
  Induct >> rw[]
  >- (gs[encode_assignment_def]
      >> qspecl_then [‘xs' ++ (q,r)::bvs’, ‘x’, ‘w'’, ‘vMap’]
                     assume_tac all_alookup
      >> gs[]
      >> gs[numVarMap_ok_def]
      >> gs[EVERY_MEM]
      >> gs[MEM_MAP]
      >> gs[PULL_EXISTS]
      >> gs[FORALL_PROD]
      >> last_x_assum (qspecl_then [‘x’, ‘xs' ++ (q,r)::bvs’] assume_tac)
      >> gs[ALOOKUP_MEM]
      >> Cases_on ‘xs'’ using SNOC_CASES >> gs[]
      >- (gs[GSYM ADD1]
          >> gs[GENLIST_CONS])
      >> Cases_on ‘x'’ >> gs[]
      >> last_x_assum (qspecl_then [‘q'’, ‘r'’] assume_tac)
      >> gs[]
      >> qspecl_then [‘MAP SND l’, ‘r'’, ‘r’, ‘MAP SND bvs’, ‘0’]
                     assume_tac genlist_lemma_2
      >> gs[]
      >> ‘GENLIST I (LENGTH bvs + (LENGTH l + 2)) =
          GENLIST (λx'. x') (LENGTH bvs + (LENGTH l + 2))’ by metis_tac[]
      >> gs[])
  >> last_x_assum irule
  >> qexists_tac ‘bvs’
  >> qexists_tac ‘q’
  >> qexists_tac ‘vMap’
  >> qexists_tac ‘w’
  >> qexists_tac ‘xs' ++ [h]’
  >> rw[]
  >> Cases_on ‘h’ >> gs[]
  >> gs[encode_assignment_def]
  >> qspecl_then [‘xs' ++ (q',r')::xs ++ (q,r)::bvs’, ‘x’, ‘w'’, ‘vMap’]
                 assume_tac all_alookup
  >> gs[]
QED

Theorem find_value_correct:
  ∀ bvs xs x vMap w w'.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    ALOOKUP vMap x = SOME (xs ++ bvs) ∧
    bvs ≠ [] ∧
    ¬ EXISTS (encode_assignment w w' vMap) (MAP FST xs) ⇒
    w' x = find_value (encode_assignment w w' vMap) bvs
Proof
  Induct >> rw[]
  >> Cases_on ‘h’
  >> rw[find_value_def]
  >- (last_x_assum kall_tac
      >> irule encode_assignment_meaning
      >> qexists_tac ‘bvs’
      >> qexists_tac ‘q’
      >> qexists_tac ‘vMap’
      >> qexists_tac ‘w’
      >> qexists_tac ‘xs’
      >> qexists_tac ‘[]’
      >> gs[])
  >> last_x_assum irule
  >> rw[]
  >> Cases_on ‘bvs = []’ >> gs[]
  >> gs[encode_assignment_def]
  >> qspecl_then [‘xs ++ (q,r)::bvs’, ‘x’, ‘w'’, ‘vMap’] assume_tac all_alookup
  >> gs[]
  >> gs[numVarAssignment_ok_def]
  >> gs[EVERY_MEM]
  >> gs[FORALL_PROD]
  >> last_x_assum (qspecl_then [‘x’, ‘xs ++ [q,r]’] assume_tac)
  >> gs[ALOOKUP_MEM]
  >> qspecl_then [‘vMap’, ‘x’, ‘xs’, ‘q’, ‘r’] assume_tac length_equal_lemma
  >> gs[ALOOKUP_MEM]
QED

Theorem assignment_encoding_ok:
  ∀ vMap w w' x.
    numVarMap_ok vMap ∧
    numVarAssignment_ok w' vMap ∧
    MEM x (MAP FST vMap) ⇒
    w' x =
    assignment_to_numVarAssignment
    (encode_assignment w w' vMap)
    vMap x
Proof
  rw[assignment_to_numVarAssignment_def]
  >> gs[numVarMap_ok_def]
  >> gs[MEM_MAP]
  >> Cases_on ‘y’
  >> gs[MEM_ALOOKUP]
  >> irule find_value_correct
  >> rw[numVarMap_ok_def]
  >> gs[EVERY_MEM, FORALL_PROD]
  >> metis_tac[ALOOKUP_MEM]
QED

Theorem mem_vList_vMap_lemma_2:
  ∀ l next len x.
    MEM x l ⇔
      MEM x (MAP FST (create_numVarMap_inner next len l))
Proof
  Induct >> rw[create_numVarMap_inner_def]
  >> metis_tac[]
QED

Theorem mem_vList_vMap_lemma:
  ∀ vList e x.
    MEM x (FST vList) ⇔
      MEM x (MAP FST (create_numVarMap e vList))
Proof
  Cases_on ‘vList’
  >> rw[create_numVarMap_def, mem_vList_vMap_lemma_2]
QED

Theorem minimal_assignment_encoding_ok:
  ∀ e vList w w' x.
    numVarList_ok vList ∧
    exp_numVarList_ok vList e ∧
    minimal_numVarAssignment_ok w' vList ∧
    MEM x (FST vList) ⇒
    w' x =
    minimal_assignment_to_numVarAssignment
    (minimal_encode_assignment w w' vList e)
    vList e x
Proof
  rw[minimal_assignment_to_numVarAssignment_def]
  >> qspecl_then [‘create_numVarMap e vList’, ‘w’, ‘w'’, ‘x’]
                 assume_tac assignment_encoding_ok
  >> qspecl_then [‘e’, ‘vList’, ‘create_numVarMap e vList’]
                 assume_tac numVarMap_created_ok
  >> qspecl_then [‘vList’, ‘e’, ‘x’] assume_tac mem_vList_vMap_lemma
  >> metis_tac[minimal_numVarAssignment_equal, minimal_encode_assignment_def]
QED

*) *)

val _ = export_theory();
