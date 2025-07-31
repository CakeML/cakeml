(*
  Definition of CNF
*)
Theory cnf
Ancestors
  misc ASCIInumbers
Libs
  preamble


(* ----------------------- Types --------------------------------------- *)

Type name = “:num”;
Type literal = “:(name + name)”;

Type assignment = “:name -> bool”;

Datatype:
  clause =
    ClauseEmpty (* False *)
  | ClauseLit literal
  | ClauseOr clause clause
End

Datatype:
  cnf =
    CnfEmpty (* True *)
  | CnfClause clause
  | CnfAnd cnf cnf
End

(* ----------------------- Satisfiability ------------------------------ *)

Definition eval_literal_def:
  eval_literal (w: assignment) l =
  case l of
    INL x => w x
  | INR x => ¬ w x
End

Definition eval_clause_def:
  (eval_clause (w: assignment) ClauseEmpty = F) ∧
  (eval_clause w (ClauseLit l) =
   eval_literal w l) ∧
  (eval_clause w (ClauseOr c1 c2) =
   (eval_clause w c1 ∨ eval_clause w c2))
End

Definition eval_cnf_def:
  (eval_cnf (w: assignment) CnfEmpty = T) ∧
  (eval_cnf w (CnfClause c) = eval_clause w c) ∧
  (eval_cnf w (CnfAnd cnf1 cnf2) =
   (eval_cnf w cnf1 ∧ eval_cnf w cnf2))
End

Definition unsat_cnf_def:
  unsat_cnf c = ∀w. ¬ eval_cnf w c
End


(* --------------------- Pretty printing ------------------------- *)

Definition lit_to_str_def:
  lit_to_str (INL l) = "b" ++ num_to_dec_string l ∧
  lit_to_str (INR l) = "~b" ++ num_to_dec_string l
End

Definition clause_to_str_def:
  clause_to_str ClauseEmpty = "False" ∧
  clause_to_str (ClauseLit l) = lit_to_str l ∧
  clause_to_str (ClauseOr b1 b2) =
  clause_to_str b1 ++ " \\/ " ++ clause_to_str b2
End

Definition cnf_to_str_def:
  cnf_to_str CnfEmpty = "True" ∧
  cnf_to_str (CnfClause c) = clause_to_str c ∧
  cnf_to_str (CnfAnd b1 b2) =
  let b1_str =
      case b1 of
        (CnfClause (ClauseOr _ _)) => "(" ++ cnf_to_str b1 ++ ")"
      | _ => cnf_to_str b1
  in let b2_str =
         case b2 of
           (CnfClause (ClauseOr _ _)) => "(" ++ cnf_to_str b2 ++ ")"
         | _ => cnf_to_str b2
     in b1_str ++ " /\\ " ++ b2_str
End

Theorem example1 =
        EVAL “cnf_to_str
              (boolExp_to_cnf
               (And
                (Not (And
                      (Lit (INL 2))
                      (Lit (INR 1))))
                (Or
                 (Lit (INL 0))
                 (Lit (INR 1)))))”;

Theorem example2 =
        EVAL “cnf_to_str
              (boolExp_to_cnf
               (And
                (Lit (INL 0))
                (And
                 (Lit (INL 2))
                 (And
                  (Lit (INR 1))
                  (Lit (INR 3))))))”;

Theorem example3 =
        EVAL “(boolExp_to_cnf
               (Or
                (Lit (INL 0))
                (Or
                 (Lit (INL 2))
                 (Or
                  (Lit (INR 1))
                  (Lit (INR 3))))))”;


(* --------------------- Functions ------------------------- *)

Definition negate_literal_def:
  negate_literal l =
  case l of
    INL x => INR x
  | INR x => INL x
End

