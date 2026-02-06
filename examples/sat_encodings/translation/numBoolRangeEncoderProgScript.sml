(*
  Encoding program for the numBoolRange datatype
*)
Theory numBoolRangeEncoderProg
Ancestors
  misc set_sep list cnf boolExpToCnf quantifierExp
  orderEncodingBool numBoolExp numBoolExtended numBoolRange
  (* for parsing: *) parsing source_values mlstring
  toCnfHelper sat_encodersProg
Libs
  preamble basis


val _ = translation_extends "sat_encodersProg";

val _ = show_assums := true;

Definition from_v_to_num_def:
  from_v_to_num (Num n) = n ∧
  from_v_to_num (Pair _ _) = 0
End

Definition from_v_to_numBoolRange_def:
  from_v_to_numBoolRange (Num n) = (RBoolVar n) ∧
  from_v_to_numBoolRange (Pair v1 v2) =
  if v1 = Name "and" then
    (RAnd (from_v_to_numBoolRange (head v2)) (from_v_to_numBoolRange (head (tail v2))))
  else if v1 = Name "or" then
    (ROr (from_v_to_numBoolRange (head v2)) (from_v_to_numBoolRange (head (tail v2))))
  else if v1 = Name "not" then
    (RNot (from_v_to_numBoolRange (head v2)))
  else if v1 = Name "impl" then
    (RImpl (from_v_to_numBoolRange (head v2)) (from_v_to_numBoolRange (head (tail v2))))
  else if v1 = Name "iff" then
    (RIff (from_v_to_numBoolRange (head v2)) (from_v_to_numBoolRange (head (tail v2))))
  else if v1 = Name "add" then
    (RAdd (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2)))
     (from_v_to_num (head (tail (tail v2)))))
  else if v1 = Name "eq" then
    (REq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "neq" then
    (RNeq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "lt" then
    (RLt (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "leq" then
    (RLeq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "gt" then
    (RGt (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "geq" then
    (RGeq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "eqConst" then
    (REqConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "neqConst" then
    (RNeqConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "ltConst" then
    (RLtConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "leqConst" then
    (RLeqConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "gtConst" then
    (RGtConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "geqConst" then
    (RGeqConst (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constEq" then
    (RConstEq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constNeq" then
    (RConstNeq (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constLt" then
    (RConstLt (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constLeq" then
    (RConstLeq  (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constGt" then
    (RConstGt (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else if v1 = Name "constGeq" then
    (RConstGeq  (from_v_to_num (head v2))
     (from_v_to_num (head (tail v2))))
  else (RBoolVar 0)
Termination
  WF_REL_TAC ‘measure v_size’ \\ rpt strip_tac
  \\ rpt (goal_term (fn tm => tmCases_on (find_term is_var (rator tm)) [] \\ fs []))
End

Definition from_v_to_rangeList_inner_def:
  from_v_to_rangeList_inner (Pair (Num x) (Pair (Num min) (Pair (Num max) (_)))) =
  (x, (min, max)) ∧
  from_v_to_rangeList_inner _ = (0, (0, 0))
End

Definition from_v_to_rangeList_def:
  from_v_to_rangeList rangelist = ((MAP from_v_to_rangeList_inner (v2list rangelist)):rangeList)
End

Definition parse_to_numBoolRange_def:
  parse_to_numBoolRange s =
      (from_v_to_numBoolRange (head s), (from_v_to_rangeList(tail s)))
End

Definition sat_to_assignment_def:
  sat_to_assignment w' [] = w' ∧
  sat_to_assignment w' (l::ls) = case l of
              | (Pair _ _) => sat_to_assignment w' ls
              | (Num n) => sat_to_assignment w'⦇n ↦ T⦈ ls
End

Definition numVarAssignment_to_output_def:
  numVarAssignment_to_output (w':numVarAssignment) [] = List [] ∧
  numVarAssignment_to_output w' (rangeListVariable::rangeList) =
  Append (List [num_to_str (FST rangeListVariable); strlit " = " ;num_to_str (w' (FST rangeListVariable)); strlit "\n"])
         (numVarAssignment_to_output w' rangeList)
End

Definition bool_to_str_def:
  bool_to_str T = strlit "T" ∧
  bool_to_str F = strlit "F"
End

Definition assignment_to_output_def:
  assignment_to_output (w:assignment) [] = List [] ∧
  assignment_to_output w (boolVar::boolVarList) = Append
    (List [num_to_str (boolVar); strlit " = ";
           bool_to_str (w boolVar) ; strlit "\n"])
   (assignment_to_output w boolVarList)
End

Definition main_function2_def:
  main_function2 v_exp sat sat_exists =
  let numBoolRange = parse_to_numBoolRange v_exp in
    case (rangeList_ok (SND numBoolRange)) of
    | F => (List [strlit "Invalid rangeList input"])
    | T =>
        case (exp_rangeList_ok
              (SND numBoolRange) (FST numBoolRange)) of
        | F => (List [strlit "Invalid expression and rangeList"])
        | T =>
            let cnf_exp =
                (numBoolRange_to_cnf
                 (SND numBoolRange) (FST numBoolRange)) in
              let (max_var, clauses) =
                  get_max_var_and_clauses cnf_exp in
                if sat_exists then
                  let w = (sat_to_assignment (λ _. F) (v2list sat)) in
                  let w' =
      (assignment_to_numVarAssignment_numBoolRange w
       (SND numBoolRange)
       (FST numBoolRange))
   in if numVarAssignment_range_ok w' (SND numBoolRange) then
        Append (assignment_to_output w (get_boolVar_list (FST numBoolRange))) (numVarAssignment_to_output w' (SND numBoolRange))
      else List [strlit "Invalid numVarAssignment"]
      else
          Append
          (List [strlit "p cnf  "; num_to_str (max_var); strlit " "; num_to_str clauses; strlit "\n"])
          (cnf_to_output cnf_exp)
End

Definition main_function_def:
  main_function (s:mlstring) =
  let v_exp = from_str (explode s) in
    case v_exp of
    | (Pair _ (Pair (Pair (Num 7561588) _) _)) =>
        main_function2 (head v_exp) (tail (head(tail v_exp))) T
    | _ => main_function2 v_exp (Num 0) F
End

val res = translate from_v_to_rangeList_inner_def;
val res = translate from_v_to_num_def;
val res = translate from_v_to_rangeList_def;
val res = translate from_v_to_numBoolRange_def;

val res = translate parse_to_numBoolRange_def;
val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;

val res = translate sat_to_assignment_def;
val res = translate bool_to_str_def;
val res = translate assignment_to_output_def;
val res = translate numVarAssignment_to_output_def;
val res = translate boolExp_to_constFree_def;
val res = translate get_fresh_name_constFree_def;

val res = translate main_function2_def;
val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring app_list”
        orelse failwith "The main_function has the wrong type.";

Quote main = cakeml:
  print_app_list (main_function (TextIO.inputAll (TextIO.openStdIn ())));
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition numBoolRange_encoder_prog_def:
  numBoolRange_encoder_prog = ^prog
End
