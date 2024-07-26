(*
  Definitions to convert Dafny's AST into CakeML's AST.
*)

open preamble
open result_monadTheory
open astTheory semanticPrimitivesTheory (* CakeML AST *)
open dafny_astTheory

open alistTheory

val _ = new_theory "dafny_to_cakeml";

(* TODO Check if we can reduce the number of generated cases *)

Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload None = “Con (SOME (Short "None")) []”

Definition from_string_def:
  from_string s =
  case (fromString (implode s)) of
  | SOME i =>
      return i
  | NONE =>
      fail ("Could not convert into int: " ++ s)
End

(* TODO? Move to dafny_ast *)
Definition dest_Name_def:
  dest_Name (Name s) = s
End

Definition from_literal_def:
  from_literal (l: dafny_ast$literal) =
   case l of
   | BoolLiteral T =>
       return True
   | BoolLiteral F =>
       return False
   | IntLiteral s (Primitive Int) =>
       do
         i <- from_string s;
         return (Lit (IntLit i))
       od
   | IntLiteral _ _ =>
       fail "IntLiteral _ _: Unclear how to handle"
   (* TODO Look into Rat module in basis *)
   | DecLiteral s1 s2 typ =>
       fail "DecLiteral s1 s2 typ: TODO"
   (* TODO String/Char support incomplete or incorrect - see
      to_dafny_astScript for more details *)
   | StringLiteral s verbatim =>
       return (Lit (StrLit s))
   | CharLiteral ch =>
       return (Lit (Char ch))
   | CharLiteralUTF16 n =>
       fail "CharLiteralUTF16 n: Unsupported"
   (* Encode a nullable type as ((a' ref) option) *)
   | Null typ =>
       return None
End

Definition dafny_type_of_def:
  dafny_type_of (e: dafny_ast$expression) (env: ((name, type) alist)) =
  case e of
  | Expression_Ident n =>
      case ALOOKUP env n of
      | SOME t => return t
      | NONE => fail ("dafny_type_of: Unknown Name" ++ (dest_Name n))
  | _ => fail "dafny_type_of: Unsupported expression"
End

Definition from_expression_def:
  (from_expression (e: dafny_ast$expression) (env: ((name, type) alist)) =
   case e of
   | Literal l =>
       from_literal l
   | Expression_Ident (Name n) =>
       return (App Opderef [Var (Short n)])
   | BinOp bop e1 e2 =>
       from_binOp bop e1 e2 env
   | _ => fail "from_expression: Unsupported expression") ∧
  (from_binOp (bop: dafny_ast$binOp) (e1: dafny_ast$expression)
              (e2: dafny_ast$expression) (env: ((name, type) alist)) =
   case bop of
   | Concat =>
       do
         (* TODO if this is repeated, pull out of case *)
         e1_t <- dafny_type_of e1 env;
         e2_t <- dafny_type_of e2 env;
         if (e1_t = (Primitive String) ∧ e1_t = e2_t)
         then
           do
             cml_e1 <- from_expression e1 env;
             cml_e2 <- from_expression e2 env;
             (* TODO place this kind of pattern into a helper *)
             return (App Opapp
                         [App Opapp [Var (Long "String" (Short "strcat"));
                                     cml_e1];
                          cml_e2])
           od
       else
         fail "from_binOp: Unsupported bop"
       od
   | _ => fail "from_binOp: TODO")
Termination
  cheat
End


(* TODO At the moment this is similar to from_InitVal. Merge in the future? *)
Definition arb_value_def:
  arb_value (t: dafny_ast$type) =
  (case t of
   | Primitive String => return (Lit (StrLit ""))
   | _ => fail "arb_value_def: Unsupported type")
End

Definition from_InitVal_def:
  from_InitVal (InitializationValue t) =
  (case t of
   | Primitive String => return (Lit (StrLit ""))
   | _ => fail "from_InitVal: Unsupported type") ∧
  from_InitVal _ = fail "from_InitVal: Unexpected case"
End

(* An independent statement must not depend on statements outside of it *)
(* TODO Fill out cases properly; wildcard means that I did not explicitly
   consider it yet *)
Definition is_indep_stmt_def:
  is_indep_stmt (s: dafny_ast$statement) =
  case s of
  | DeclareVar _ _ _=> F
  | Assign _ _ => T
  | Print _ => T
  | _ => F
End

Definition from_ident_def:
  from_ident (Ident n) = Var (Short (dest_Name n))
End

Definition from_assignLhs_def:
  from_assignLhs (lhs: dafny_ast$assignLhs) =
  case lhs of
  | AssignLhs_Ident id => return (from_ident id)
  | _ => fail "from_assignLhs: Unsupported"
End

Definition from_indep_stmt_def:
  from_indep_stmt (s: dafny_ast$statement) (env: ((name, type) alist)) =
  (case s of
  | Assign lhs e =>
      do
        cml_lhs <- from_assignLhs lhs;
        cml_rhs <- from_expression e env;
        return (App Opassign [cml_lhs; cml_rhs])
      od
  | Print e =>
      do
        cml_e <- from_expression e env;
        return (App Opapp [Var (Short "print"); cml_e])
      od
  | _ => fail "from_indep_stmt_def: Unsupported or not independent statement")
End

(* TODO move this to dafny_ast? *)
Definition is_DeclareVar_def:
  is_DeclareVar s =
  case s of
  | DeclareVar _ _ _ => T
  | _ => F
End

(* TODO move this to dafny_ast? *)
Definition dest_DeclareVar_def:
  dest_DeclareVar s =
  case s of
  | DeclareVar n t e_opt => return (n, t, e_opt)
  | _ => fail "dest_DeclareVar: Not a DeclareVar"
End

(* TODO move this to result_monad? *)
Definition dest_SOME_def:
  dest_SOME (SOME x) = return x ∧
  dest_SOME NONE = fail "dest_SOME: Not a SOME"
End

(* TODO is_<constructor> calls could maybe be replaced using monad choice *)
(* At the moment we assume that only statements can change env *)
Definition from_stmts_def:
  (from_stmts ([]: (dafny_ast$statement list))
              (env: ((name, type) alist)) =
   fail "from_stmts: List of statements must not be empty") ∧
  (from_stmts [s] env =
   if s = EarlyReturn then
     (* TODO Handle EarlyReturn properly *)
     fail "from_stmts: Cannot convert single EarlyReturn"
   else if is_indep_stmt s then
     do
       cml_e <- from_indep_stmt s env;
       return (cml_e, env)
     od
   else
     fail ("from_stmts: " ++
           "Cannot convert single non-self-contained statement")) ∧
  (from_stmts (s1::s2::rest) env =
   if s1 = EarlyReturn then
     (* TODO Handle EarlyReturn properly *)
     fail ("from_stmts: " ++
           "TODO EarlyReturn can only appear at the end of a " ++
           "non-singleton list.")
   else if is_indep_stmt s1 then
     if (s2 = EarlyReturn ∧ rest = []) then
       do
         cml_e <- from_indep_stmt s1 env;
         return (cml_e, env)
       od
     else
       do
         e1 <- from_indep_stmt s1 env;
         (e2, env') <- from_stmts (s2::rest) env;
         return ((Let NONE e1 e2), env')
       od
   else if is_DeclareVar s1 then
     do
       (n, t, e_opt) <- dest_DeclareVar s1;
       n_str <<- dest_Name n;

       iv_e <- if e_opt = NONE then arb_value t
               else do e <- dest_SOME e_opt; from_InitVal e od;
       (in_e, env') <- from_stmts (s2::rest) ((n, t)::env);
       return ((Let (SOME n_str) ((App Opref [iv_e])) in_e), env')
     od
   else
     fail "from_stmts: Unsupported statement")
End

Definition compile_def:
  compile p =
  do
    (* TODO Assume that we only have a main function *)
    if (LENGTH p ≠ 2) then
      fail "Program should have exactly 2 modules"
    else
      do
        (* TODO Ignore first module which contains definitions for nat and tuples for now *)
        case (EL 1 p) of
        | Module _ _ (SOME [ModuleItem_Class (Class _ _ _ _ _ [ClassItem_Method m] _)]) =>
            (case m of
            | Method _ _ _ _ _ _ body _ _ =>
                do
                  (main_stmts, _) <- from_stmts body [];
                  return ([Dletrec (Locs (POSN 0 15) (POSN 0 50))
                                   [("Main","",
                                     Mat (Var (Short ""))
                                         [(Pcon NONE [],
                                           main_stmts)])];
                           Dlet (Locs (POSN 0 52) (POSN 0 66)) Pany
                                (Let (SOME " v0") (Con NONE [])
                                     (App Opapp [Var (Short "Main"); Var (Short " v0")]))])
                od
            | _ => fail "Unexpected something")
        | _ => fail "Unexpected ModuleItem"
      od
  od
End

(* Unpacks the AST from M. If the process failed, create a program that prints
   the error. *)
Definition unpack_def:
  unpack m =
  case m of
  | INR d =>
      d
  | INL s =>
      [Dlet (Locs (POSN 0 14) UNKNOWNpt) (Pvar "it")
       (App Opapp [Var (Short "print"); Lit (StrLit s)])]
End

(* Testing *)
open dafny_sexpTheory
open sexp_to_dafnyTheory
open fromSexpTheory simpleSexpParseTheory
open TextIO
val _ = astPP.enable_astPP();

val inStream = TextIO.openIn "./tests/string_concat.sexp";
val fileContent = TextIO.inputAll inStream;
val _ = TextIO.closeIn inStream;
val fileContent_tm = stringSyntax.fromMLstring fileContent;

val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand;
val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand;
val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand;
val cakeml_r = EVAL “(compile ^dafny_r)” |> concl |> rhs |> rand;

val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^cakeml_r)))”
                   |> concl |> rhs |> rand;
val cml_sexp_str_r = stringSyntax.fromHOLstring cml_sexp_r;
val outFile = TextIO.openOut "./tests/string_concat.cml.sexp";
val _ = TextIO.output (outFile, cml_sexp_str_r);
val _ = TextIO.closeOut outFile

val _ = export_theory();
