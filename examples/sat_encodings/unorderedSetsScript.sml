(*
  Encode unordered sets to natural numbers
*)
Theory unorderedSets
Ancestors
  misc mlint cnf boolExpToCnf quantifierExp numBoolRange
Libs
  preamble


(* ------------------- Types ---------------------------------- *)

Type element = “:string”;
Type constant = “:element”;
Type unorderedSet = “:element list”;
Type setName = “:string”;
Type elementVar = “:num”;
Type varInSet = “:(elementVar # setName)”;

Type boolVar = “:num”;

Type setList = “:(setName # unorderedSet) list”;
Type elementVarAssignment = “:elementVar -> element”;
Type varList = “:varInSet list”

Datatype:
  equation =
  | EqTrue
  | EqFalse
  | EqBoolVar boolVar
  | EqVarCon varInSet constant
  | EqVarVar varInSet varInSet
  | EqNot equation
  | EqAnd equation equation
  | EqOr equation equation
  | EqImpl equation equation
  | EqIff equation equation
End

(* ------------------ Create varList ---------------------------------- *)

Definition get_varList_inner_def:
  get_varList_inner l EqTrue = l ∧
  get_varList_inner l EqFalse = l ∧
  get_varList_inner l (EqBoolVar bv) = l ∧
  get_varList_inner l (EqVarCon v c) = nub (v::l) ∧
  get_varList_inner l (EqVarVar v1 v2) = nub (v1::v2::l) ∧
  get_varList_inner l (EqNot eq) = get_varList_inner l eq ∧
  get_varList_inner l (EqAnd e1 e2) =
  nub (get_varList_inner l e1 ++ get_varList_inner l e2) ∧
  get_varList_inner l (EqOr e1 e2) =
  nub (get_varList_inner l e1 ++ get_varList_inner l e2) ∧
  get_varList_inner l (EqImpl e1 e2) =
  nub (get_varList_inner l e1 ++ get_varList_inner l e2) ∧
  get_varList_inner l (EqIff e1 e2) =
  nub (get_varList_inner l e1 ++ get_varList_inner l e2)
End

Definition get_varList_def:
  get_varList e = get_varList_inner [] e
End


(* ------------------ Well formed ---------------------------------- *)

Definition setList_ok_def:
  setList_ok (l:setList) ⇔
    ALL_DISTINCT (MAP FST l) ∧
    EVERY ((λ x. x ≠ []) o SND) l ∧
    EVERY (ALL_DISTINCT o SND) l
End

Definition eq_setList_ok_def:
  eq_setList_ok (l:setList) EqTrue = T ∧
  eq_setList_ok l EqFalse = T ∧
  eq_setList_ok l (EqBoolVar bv) = T ∧
  eq_setList_ok l (EqVarCon p c) =
  (case ALOOKUP l (SND p) of
   | NONE => F
   | SOME ss => MEM c ss) ∧
  eq_setList_ok l (EqVarVar v1 v2) =
  ((SND v1) = (SND v2) ∧ MEM (SND v1) (MAP FST l)) ∧
  eq_setList_ok l (EqNot eq) = eq_setList_ok l eq ∧
  eq_setList_ok l (EqAnd eq1 eq2) =
  (eq_setList_ok l eq1 ∧ eq_setList_ok l eq2) ∧
  eq_setList_ok l (EqOr eq1 eq2) =
  (eq_setList_ok l eq1 ∧ eq_setList_ok l eq2) ∧
  eq_setList_ok l (EqImpl eq1 eq2) =
  (eq_setList_ok l eq1 ∧ eq_setList_ok l eq2) ∧
  eq_setList_ok l (EqIff eq1 eq2) =
  (eq_setList_ok l eq1 ∧ eq_setList_ok l eq2)
End

Definition eq_var_value_mem_def:
  eq_var_value_mem (w':elementVarAssignment) (l:setList) v =
  (case ALOOKUP l (SND v) of
   | SOME ss => MEM (w' (FST v)) ss
   | NONE => F)
End

Definition eq_elementVarAssignment_ok_def:
  eq_elementVarAssignment_ok
  (w': elementVarAssignment) (l:setList) EqTrue = T ∧
  eq_elementVarAssignment_ok w' l EqFalse = T ∧
  eq_elementVarAssignment_ok w' l (EqBoolVar bv) = T ∧
  eq_elementVarAssignment_ok w' l (EqVarCon v c) = eq_var_value_mem w' l v ∧
  eq_elementVarAssignment_ok w' l (EqVarVar v1 v2) =
  (eq_var_value_mem w' l v1 ∧ eq_var_value_mem w' l v2) ∧
  eq_elementVarAssignment_ok w' l (EqNot eq) =
  eq_elementVarAssignment_ok w' l eq ∧
  eq_elementVarAssignment_ok w' l (EqAnd eq1 eq2) =
  (eq_elementVarAssignment_ok w' l eq1 ∧ eq_elementVarAssignment_ok w' l eq2) ∧
  eq_elementVarAssignment_ok w' l (EqOr eq1 eq2) =
  (eq_elementVarAssignment_ok w' l eq1 ∧ eq_elementVarAssignment_ok w' l eq2) ∧
  eq_elementVarAssignment_ok w' l (EqImpl eq1 eq2) =
  (eq_elementVarAssignment_ok w' l eq1 ∧ eq_elementVarAssignment_ok w' l eq2) ∧
  eq_elementVarAssignment_ok w' l (EqIff eq1 eq2) =
  (eq_elementVarAssignment_ok w' l eq1 ∧ eq_elementVarAssignment_ok w' l eq2)
End

Definition equation_ok_def:
  equation_ok e = ALL_DISTINCT (MAP FST (get_varList e))
End

Definition varList_ok_def:
  varList_ok (vList:varList) = ALL_DISTINCT (MAP FST vList)
End

Definition eq_varList_ok_def:
  eq_varList_ok (vList:varList) EqTrue = T ∧
  eq_varList_ok vList EqFalse = T ∧
  eq_varList_ok vList (EqBoolVar _) = T ∧
  eq_varList_ok vList (EqVarCon v c) = MEM v vList ∧
  eq_varList_ok vList (EqVarVar v1 v2) = (MEM v1 vList ∧ MEM v2 vList) ∧
  eq_varList_ok vList (EqNot e) = eq_varList_ok vList e ∧
  eq_varList_ok vList (EqAnd e1 e2) =
  (eq_varList_ok vList e1 ∧ eq_varList_ok vList e2) ∧
  eq_varList_ok vList (EqOr e1 e2) =
  (eq_varList_ok vList e1 ∧ eq_varList_ok vList e2) ∧
  eq_varList_ok vList (EqImpl e1 e2) =
  (eq_varList_ok vList e1 ∧ eq_varList_ok vList e2) ∧
  eq_varList_ok vList (EqIff e1 e2) =
  (eq_varList_ok vList e1 ∧ eq_varList_ok vList e2)
End

Definition varList_elementVarAssignment_ok_def:
  varList_elementVarAssignment_ok
  (w':elementVarAssignment) (l:setList) (vList:varList) =
  EVERY (eq_var_value_mem w' l) vList
End

(* ----------------------- Satisfiability --------------------------- *)

Definition eval_equation_def:
  (eval_equation (w:assignment) (w':elementVarAssignment) EqTrue = T) ∧
  (eval_equation w w' EqFalse = F) ∧
  (eval_equation w w' (EqBoolVar bv) = w bv) ∧
  (eval_equation w w' (EqVarCon evn c) = (w' (FST evn) = c)) ∧
  (eval_equation w w' (EqVarVar evn1 evn2) =
   (w' (FST evn1) = w' (FST evn2))) ∧
  (eval_equation w w' (EqNot eq) = ¬ (eval_equation w w' eq)) ∧
  (eval_equation w w' (EqAnd eq1 eq2) =
   ((eval_equation w w' eq1) ∧ (eval_equation w w' eq2))) ∧
  (eval_equation w w' (EqOr eq1 eq2) =
   ((eval_equation w w' eq1) ∨ (eval_equation w w' eq2))) ∧
  (eval_equation w w' (EqImpl eq1 eq2) =
   ((eval_equation w w' eq1) ⇒ (eval_equation w w' eq2))) ∧
  (eval_equation w w' (EqIff eq1 eq2) =
   ((eval_equation w w' eq1) ⇔ (eval_equation w w' eq2)))
End


(* --------------------- Encoding -------------------------------- *)

Definition encode_constant_def:
  encode_constant l sName c =
  case ALOOKUP l sName of
  | SOME list => findi c list
  | NONE => 0
End

Definition equation_to_numBoolRange_def:
  equation_to_numBoolRange (l:setList) EqTrue = RTrue ∧
  equation_to_numBoolRange l EqFalse = RFalse ∧
  equation_to_numBoolRange l (EqBoolVar bv) = RBoolVar bv ∧
  equation_to_numBoolRange l (EqVarCon v c) =
  REqConst (FST v) (encode_constant l (SND v) c) ∧
  equation_to_numBoolRange l (EqVarVar v1 v2) = REq (FST v1) (FST v2) ∧
  equation_to_numBoolRange l (EqNot eq) =
  RNot (equation_to_numBoolRange l eq) ∧
  equation_to_numBoolRange l (EqAnd eq1 eq2) =
  RAnd (equation_to_numBoolRange l eq1) (equation_to_numBoolRange l eq2) ∧
  equation_to_numBoolRange l (EqOr eq1 eq2) =
  ROr (equation_to_numBoolRange l eq1) (equation_to_numBoolRange l eq2) ∧
  equation_to_numBoolRange l (EqImpl eq1 eq2) =
  RImpl (equation_to_numBoolRange l eq1) (equation_to_numBoolRange l eq2) ∧
  equation_to_numBoolRange l (EqIff eq1 eq2) =
  RIff (equation_to_numBoolRange l eq1) (equation_to_numBoolRange l eq2)
End

Definition get_setName_def:
  get_setName varList x =
  case ALOOKUP varList x of
  | SOME sName => sName
  | NONE => ""
End

Definition elementVarAssignment_to_numVarAssignment_inner_def:
  elementVarAssignment_to_numVarAssignment_inner
  (w':elementVarAssignment) (l:setList) (vList:varList) (x:num) =
    let sName = get_setName vList x in
      case ALOOKUP l sName of
      | SOME list => findi (w' x) list
      | NONE => 0
End

Definition elementVarAssignment_to_numVarAssignment_def:
  elementVarAssignment_to_numVarAssignment
  (w':elementVarAssignment) (l:setList) e (x:num) =
  elementVarAssignment_to_numVarAssignment_inner w' l (get_varList e) x
End

Definition get_max_def:
  get_max (l:setList) sName =
  case ALOOKUP l sName of
  | SOME list => (LENGTH list) - 1
  | NONE => 0
End

Definition equation_to_rangeList_inner_def:
  equation_to_rangeList_inner (l:setList) [] = [] ∧
  equation_to_rangeList_inner l ((x, sName)::varList) =
  (x, ((0:num), get_max l sName))::equation_to_rangeList_inner l varList
End

Definition equation_to_rangeList_def:
  equation_to_rangeList e l =
  equation_to_rangeList_inner l (get_varList e)
End

Definition equation_to_cnf_def:
  equation_to_cnf (l:setList) e =
  numBoolRange_to_cnf
  (equation_to_rangeList e l)
  (equation_to_numBoolRange l e)
End

Definition encode_assignment_unorderedSet_def:
  encode_assignment_unorderedSet w w' l e =
    numBoolRange_to_assignment w
    (elementVarAssignment_to_numVarAssignment w' l e)
    (equation_to_rangeList_inner l (get_varList e))
    (equation_to_numBoolRange l e)
End

Definition numVarAssignment_to_elementVarAssignment_inner_def:
  numVarAssignment_to_elementVarAssignment_inner
  (w:numVarAssignment) (l:setList) (vList:varList) x =
  case ALOOKUP vList x of
  | NONE => ""
  | SOME sName =>
      case ALOOKUP l sName of
      | NONE => ""
      | SOME ss =>
          case oEL (w x) ss of
          | NONE => ""
          | SOME s => s
End

Definition numVarAssignment_to_elementVarAssignment_def:
  numVarAssignment_to_elementVarAssignment
  (w:numVarAssignment) (l:setList) (e:equation) x =
  numVarAssignment_to_elementVarAssignment_inner w l (get_varList e) x
End

Definition assignment_to_elementVarAssignment_def:
  assignment_to_elementVarAssignment w l e =
  let w' = assignment_to_numVarAssignment_numBoolRange
           w (equation_to_rangeList e l) (equation_to_numBoolRange l e) in
    numVarAssignment_to_elementVarAssignment w' l e
End


(* --------------------- Theorems -------------------------------- *)

Theorem findi_same_2:
  ∀ x q s r l w'.
    ALL_DISTINCT x ∧
    ¬MEM (r,[]) l ∧
    w' q ≠ s ∧
    MEM s x ∧
    MEM (w' q) x ∧
    ALL_DISTINCT (MAP FST l) ⇒
    findi (w' q) x = findi s x ⇒ w' q = s
Proof
  Induct >> gvs[]
  >> rw[]
  >> gvs[findi_def]
  >> rw[]
  >> first_x_assum irule
  >> rw[]
  >> qexists_tac ‘l’
  >> qexists_tac ‘r’
  >> gvs[]
QED

Theorem findi_same:
  ∀l s x q w' r.
    setList_ok l ∧
    MEM s x ∧
    MEM (w' q) x ∧
    ALOOKUP l r = SOME x ⇒
    (w' q = s ⇔ findi (w' q) x = findi s x)
Proof
  rw[setList_ok_def]
  >> eq_tac
  >- metis_tac[findi_def]
  >> gvs[o_DEF, EVERY_MEM, FORALL_PROD]
  >> ‘MEM (r, x) l’ by gvs[ALOOKUP_MEM]
  >> first_x_assum (qspecl_then [‘r’, ‘x’] assume_tac)
  >> first_x_assum (qspecl_then [‘r’] assume_tac)
  >> metis_tac[findi_same_2]
QED

Theorem equation_to_numBoolRange_preserves_sat_2:
  ∀ e l vList w w'.
    setList_ok l ∧
    eq_setList_ok l e ∧
    eq_elementVarAssignment_ok w' l e ∧
    varList_ok vList ∧
    eq_varList_ok vList e ⇒
    (eval_equation w w' e ⇔
       eval_numBoolRange
       w
       (elementVarAssignment_to_numVarAssignment_inner w' l vList)
       (equation_to_numBoolRange l e))
Proof
  Induct >> rw[]
  >> TRY(rw[eval_equation_def, equation_to_numBoolRange_def,
            eval_numBoolRange_def]
         >> NO_TAC)
  >- (gs[eval_equation_def, equation_to_numBoolRange_def,
         eval_numBoolRange_def, encode_constant_def,
         elementVarAssignment_to_numVarAssignment_inner_def,
         get_setName_def, eq_varList_ok_def, varList_ok_def]
      >> Cases_on ‘p’
      >> gs[MEM_ALOOKUP, eq_setList_ok_def, eq_elementVarAssignment_ok_def,
            eq_var_value_mem_def]
      >> Cases_on ‘ALOOKUP l r’ >> gs[]
      >> metis_tac[findi_same])
  >- (gs[eval_equation_def, equation_to_numBoolRange_def,
         eval_numBoolRange_def, encode_constant_def,
         elementVarAssignment_to_numVarAssignment_inner_def,
         get_setName_def, eq_varList_ok_def, varList_ok_def]
      >> Cases_on ‘p’
      >> Cases_on ‘p0’
      >> gs[MEM_ALOOKUP, eq_setList_ok_def, eq_elementVarAssignment_ok_def,
            eq_var_value_mem_def]
      >> Cases_on ‘ALOOKUP l r'’ >> gs[]
      >> metis_tac[findi_same])
  >> (gs[eval_equation_def, equation_to_numBoolRange_def,
         eval_numBoolRange_def, eq_setList_ok_def,
         eq_elementVarAssignment_ok_def, eq_varList_ok_def]
      >> metis_tac[])
QED

Theorem varList_ok_lemma:
  ∀ e.
    equation_ok e ⇒
    varList_ok (get_varList e)
Proof
  rw[equation_ok_def, varList_ok_def]
QED

Theorem eq_varList_ok_lemma_2:
  ∀ e l l'.
    (∀ x. MEM x l ⇒ MEM x l') ∧
    eq_varList_ok l e ⇒
    eq_varList_ok l' e
Proof
  Induct >> rw[eq_varList_ok_def]
  >> metis_tac[]
QED

Theorem eq_varList_ok_lemma:
  ∀ e.
    eq_varList_ok (get_varList e) e
Proof
  Induct >> gs[get_varList_def, get_varList_inner_def, eq_varList_ok_def]
  >> (rw[]
      >- (irule eq_varList_ok_lemma_2
          >> qexists_tac ‘get_varList_inner [] e’
          >> gs[])
      >> irule eq_varList_ok_lemma_2
      >> qexists_tac ‘get_varList_inner [] e'’
      >> gs[])
QED

Theorem equation_to_numBoolRange_preserves_sat:
  ∀ e l w w'.
    setList_ok l ∧
    eq_setList_ok l e ∧
    eq_elementVarAssignment_ok w' l e ∧
    equation_ok e ⇒
    (eval_equation w w' e ⇔
       eval_numBoolRange
       w
       (elementVarAssignment_to_numVarAssignment w' l e)
       (equation_to_numBoolRange l e))
Proof
  rw[]
  >> qspecl_then [‘e’, ‘l’, ‘get_varList e’, ‘w’, ‘w'’]
                 assume_tac equation_to_numBoolRange_preserves_sat_2
  >> gs[varList_ok_lemma, eq_varList_ok_lemma]
  >> metis_tac[elementVarAssignment_to_numVarAssignment_def]
QED

Theorem variables_same_varList_rangeList:
  ∀ vList l x.
    MEM x (MAP FST vList) ⇔
      MEM x (MAP FST (equation_to_rangeList_inner l vList))
Proof
  Induct
  >- rw[equation_to_rangeList_inner_def]
  >> Cases_on ‘h’
  >> rw[equation_to_rangeList_inner_def]
  >> metis_tac[]
QED

Theorem map_fst_vList_same:
  ∀ vList l.
    (MAP FST vList) = (MAP FST (equation_to_rangeList_inner l vList))
Proof
  Induct
  >> rw[equation_to_rangeList_inner_def]
  >> Cases_on‘h’
  >> gvs[equation_to_rangeList_inner_def]
QED

Theorem rangeList_ok_lemma:
  ∀ vList l a.
    varList_ok vList ⇒
    rangeList_ok (equation_to_rangeList_inner l vList)
Proof
  rw[varList_ok_def, rangeList_ok_def]
  >> metis_tac[map_fst_vList_same]
QED

Theorem exp_rangeList_ok_lemma:
  ∀ e l vList.
    setList_ok l ∧
    eq_setList_ok l e ∧
    eq_varList_ok vList e ⇒
    exp_rangeList_ok
    (equation_to_rangeList_inner l vList)
    (equation_to_numBoolRange l e)
Proof
  Induct >> rw[]
  >> TRY (gs[equation_to_numBoolRange_def, exp_rangeList_ok_def]
          >> NO_TAC)
  >- (gs[equation_to_numBoolRange_def]
      >> gs[exp_rangeList_ok_def]
      >> gs[eq_varList_ok_def]
      >> Cases_on ‘p’ >> gs[]
      >> qspecl_then [‘vList’, ‘l’, ‘q’]
                     assume_tac variables_same_varList_rangeList
      >> qspecl_then [‘FST’, ‘vList’, ‘(q,r)’] assume_tac MEM_MAP_f
      >> gs[])
  >- (gs[equation_to_numBoolRange_def]
      >> gs[exp_rangeList_ok_def]
      >> gs[eq_varList_ok_def]
      >> Cases_on ‘p0’
      >> Cases_on ‘p’
      >> qspecl_then [‘vList’, ‘l’, ‘q’]
                     assume_tac variables_same_varList_rangeList
      >> qspecl_then [‘FST’, ‘vList’, ‘(q,r)’] assume_tac MEM_MAP_f
      >> gs[]
      >> qspecl_then [‘vList’, ‘l’, ‘q'’]
                     assume_tac variables_same_varList_rangeList
      >> qspecl_then [‘FST’, ‘vList’, ‘(q',r')’] assume_tac MEM_MAP_f
      >> gs[])
  >> gs[equation_to_numBoolRange_def, exp_rangeList_ok_def,
        eq_setList_ok_def, eq_varList_ok_def]
QED

Theorem numVarAssignment_range_ok_lemma_3:
  ∀ vList vList' l q r w'.
    ALL_DISTINCT (MAP FST vList) ∧
    ¬MEM q (MAP FST vList) ∧
    numVarAssignment_range_ok
    (elementVarAssignment_to_numVarAssignment_inner w' l (vList' ++ vList))
    (equation_to_rangeList_inner l vList) ⇒
    numVarAssignment_range_ok
    (elementVarAssignment_to_numVarAssignment_inner
     w' l ((q,r)::(vList' ++ vList)))
    (equation_to_rangeList_inner l vList)
Proof
  Induct >> rw[]
  >- rw[equation_to_rangeList_inner_def, numVarAssignment_range_ok_def]
  >> Cases_on ‘h’
  >> gs[equation_to_rangeList_inner_def, numVarAssignment_range_ok_def]
  >> rw[]
  >- (last_x_assum kall_tac
      >> gs[elementVarAssignment_to_numVarAssignment_inner_def,
            get_setName_def])
  >> last_x_assum
     (qspecl_then [‘vList' ++ [(q', r')]’, ‘l’, ‘q’, ‘r’, ‘w'’] assume_tac)
  >> gs[]
  >> metis_tac[APPEND_ASSOC, CONS_APPEND]
QED

Theorem numVarAssignment_range_ok_lemma_2:
  ∀ vList e l w w'.
    setList_ok l ∧
    eq_setList_ok l e ∧
    varList_elementVarAssignment_ok w' l vList ∧
    varList_ok vList ⇒
    numVarAssignment_range_ok
    (elementVarAssignment_to_numVarAssignment_inner w' l vList)
    (equation_to_rangeList_inner l vList)
Proof
  Induct
  >- rw[equation_to_rangeList_inner_def, numVarAssignment_range_ok_def]
  >> rw[]
  >> Cases_on ‘h’
  >> gs[equation_to_rangeList_inner_def, numVarAssignment_range_ok_def]
  >> rw[]
  >- (last_x_assum kall_tac
      >> gs[elementVarAssignment_to_numVarAssignment_inner_def,
            get_setName_def, varList_elementVarAssignment_ok_def,
            eq_var_value_mem_def]
      >> Cases_on ‘ALOOKUP l r’ >> gs[]
      >> gs[get_max_def]
      >> drule MEM_findi
      >> gs[])
  >> gs[varList_elementVarAssignment_ok_def, varList_ok_def]
  >> last_x_assum (qspecl_then [‘e’, ‘l’, ‘w'’] assume_tac)
  >> qspecl_then [‘vList’, ‘[]’, ‘l’, ‘q’, ‘r’, ‘w'’]
                 assume_tac numVarAssignment_range_ok_lemma_3
  >> gs[numVarAssignment_range_ok_def]
QED

Theorem varList_elementVarAssignment_ok_lemma:
  ∀ e l w'.
    eq_elementVarAssignment_ok w' l e ⇒
    varList_elementVarAssignment_ok w' l (get_varList e)
Proof
  Induct >> rw[]
  >> TRY (gs[get_varList_def, get_varList_inner_def,
             varList_elementVarAssignment_ok_def, nub_def,
             eq_elementVarAssignment_ok_def]
          >> NO_TAC)
  >- (Cases_on ‘p0 = p’
      >> gs[get_varList_def, get_varList_inner_def, nub_def,
            varList_elementVarAssignment_ok_def,
            eq_elementVarAssignment_ok_def])
  >> (gs[get_varList_def, get_varList_inner_def,
         eq_elementVarAssignment_ok_def,
         varList_elementVarAssignment_ok_def, EVERY_MEM]
      >> metis_tac[])
QED

Theorem numVarAssignment_range_ok_lemma:
  ∀ e l w'.
    setList_ok l ∧
    eq_setList_ok l e ∧
    equation_ok e ∧
    eq_elementVarAssignment_ok w' l e ⇒
    numVarAssignment_range_ok
    (elementVarAssignment_to_numVarAssignment w' l e)
    (equation_to_rangeList_inner l (get_varList e))
Proof
  rw[]
  >> qspecl_then [‘get_varList e’, ‘e’, ‘l’, ‘w’, ‘w'’]
                 assume_tac numVarAssignment_range_ok_lemma_2
  >> gs[varList_ok_lemma, eq_varList_ok_lemma, numVarAssignment_range_ok_def,
        varList_elementVarAssignment_ok_lemma]
  >> metis_tac[elementVarAssignment_to_numVarAssignment_def]
QED

Theorem equation_to_cnf_preserves_sat:
  ∀ e l w w'.
    setList_ok l ∧
    eq_setList_ok l e ∧
    eq_elementVarAssignment_ok w' l e ∧
    equation_ok e ⇒
    (eval_equation w w' e ⇔
       eval_cnf
       (encode_assignment_unorderedSet w w' l e)
       (equation_to_cnf l e))
Proof
  rw[]
  >> qspecl_then [‘e’, ‘l’, ‘w’, ‘w'’]
                 assume_tac equation_to_numBoolRange_preserves_sat
  >> gs[]
  >> rw[equation_to_cnf_def]
  >> rw[(*encode_assignment_unorderedSet_def*)]
  >> rw[equation_to_rangeList_def]
  >> qspecl_then
     [‘equation_to_numBoolRange l e’,
      ‘equation_to_rangeList_inner l (get_varList e)’, ‘w’,
      ‘elementVarAssignment_to_numVarAssignment w' l e’]
     mp_tac numBoolRange_to_cnf_preserves_sat
  >> impl_tac >> gs[]
  >> rw[]
  >- gs[varList_ok_lemma, rangeList_ok_lemma]
  >- gs[eq_varList_ok_lemma, exp_rangeList_ok_lemma]
  >> gs[numVarAssignment_range_ok_lemma, encode_assignment_unorderedSet_def]
QED

