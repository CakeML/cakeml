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
(* TODO Add missing wildcard for function that are defined using pattern matching
 (even if all cases seem to be covered) *)

Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload None = “Con (SOME (Short "None")) []”
Overload Unit = “Con NONE []”

Definition from_string_def:
  from_string s =
  case (fromString (implode s)) of
  | SOME i =>
      return i
  | NONE =>
      fail ("Could not convert into int: " ++ s)
End

Definition cml_ref_def:
  cml_ref n val_e in_e = (Let (SOME n) ((App Opref [val_e])) in_e)
End

Definition cml_fapp_aux_def:
  cml_fapp_aux fun_name [] = App Opapp [fun_name; Unit] ∧
  cml_fapp_aux fun_name (e::rest) =
  if rest = [] then (App Opapp [fun_name; e])
  else
    let inner_app = cml_fapp_aux fun_name rest in
      (App Opapp [inner_app; e])
End

Definition cml_fapp_def:
  cml_fapp fun_name args = cml_fapp_aux fun_name (REVERSE args)
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
      | NONE => fail ("dafny_type_of: Unknown Name " ++ (dest_Name n))
  | _ => fail "dafny_type_of: Unsupported expression"
End

Definition from_expression_def:
  (from_expression (env: ((name, type) alist)) (e: dafny_ast$expression) =
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
             cml_e1 <- from_expression env e1;
             cml_e2 <- from_expression env e2;
             return (cml_fapp (Var (Long "String" (Short "strcat")))
                              [cml_e1; cml_e2])
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
  | Call _ _ _ _ _ => T
  | Print _ => T
  | _ => F
End

Definition from_name_def:
  from_name n = Var (Short (dest_Name n))
End

Definition from_ident_def:
  from_ident (Ident n) = from_name n
End

Definition from_callName_def:
  (from_callName (CallName nam onType sig) =
   if onType ≠ NONE then
     fail "from_callName: non-empty onType currently unsupported"
   (* TODO Confirm that we can ignore the call signature *)
   (* else if sig ≠ CallSignature [] then *)
   (*   fail "from_callName: non_empty callSignature currently unsupported" *)
   else
     return (from_name nam)) ∧
  (from_callName _ = fail ("from_callName: " ++
                           "Passed callName currently unsupported"))
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
        cml_rhs <- from_expression env e;
        return (App Opassign [cml_lhs; cml_rhs])
      od
  | Call on call_nam typeArgs args outs =>
      do
        if on ≠ (Companion [Ident (Name "_module");
                            Ident (Name "__default")]) then
          fail "from_indep_stmt: (Call) Unsupported on expression"
        else if typeArgs ≠ [] then
          fail "from_indep_stmt: (Call) type arguments currently unsupported"
        else if outs ≠ NONE then
          fail "from_indep_stmt: (Call) Return values currently unsupported"
        else
          do
            fun_name <- from_callName call_nam;
            cml_args <- result_mmap (from_expression env) args;
            return (cml_fapp fun_name cml_args)
          od
      od
  | Print e =>
      do
        cml_e <- from_expression env e;
        return (cml_fapp (Var (Short "print")) [cml_e])
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
       return (cml_ref n_str iv_e in_e, env')
     od
   else
     fail "from_stmts: Unsupported statement")
End

Definition varN_from_formal_def:
  (varN_from_formal (Formal n _ attrs) =
   if attrs ≠ [] then
     fail "param_from_formals: Attributes currently unsupported"
   else
     return (dest_Name n)) ∧
  (varN_from_formal _ = fail "varN_from_formal: Unreachable")
End

Definition internal_varN_from_formal_def:
  internal_varN_from_formal fo =
  do
    n <- varN_from_formal fo;
    (* TODO Find better way to generate internal names *)
    return (n ++ "_CML_param")
  od
End

Definition param_defs_from_formals_def:
  (param_defs_from_formals ([]: (dafny_ast$formal list)) x =
   fail "param_defs_from_formals: No parameters to define") ∧
  (param_defs_from_formals (fo::rest) x =
   do
     param_name <- internal_varN_from_formal fo;
     param_exp <- if rest = [] then return x
                  else param_defs_from_formals rest x;
     return (Fun param_name param_exp)
   od)
End

Definition declare_init_param_refs_def:
  declare_init_param_refs [] in_exp =
  fail ("declare_init_param_refs: Nothing to declare and initialize") ∧
  (declare_init_param_refs (fo::rest) in_exp =
   do
     ref_name <- varN_from_formal fo;
     ref_value_name <- internal_varN_from_formal fo;
     if rest = [] then
       return (cml_ref ref_name (Var (Short ref_value_name)) in_exp)
     else
       do
         next_declare <- declare_init_param_refs rest in_exp;
         return (cml_ref ref_name (Var (Short ref_value_name)) next_declare)
       od
   od)
End

Definition method_preamble_from_formal_def:
  method_preamble_from_formal [] =
  do
    param <<- "";
    (* Encodes a function without parameters as foo () = ... *)
    preamble <<- λx. (return (Mat (Var (Short "")) [(Pcon NONE [], x)]));
    return (param, preamble)
  od ∧
  method_preamble_from_formal (fo::rest) =
  do
    param <- internal_varN_from_formal fo;
    if rest = [] then
      do
        preamble <<- λx. (declare_init_param_refs [fo] x);
        return (param, preamble)
      od
    else
      do
        preamble <<- (λx.
                         do
                           inner_exp <- declare_init_param_refs (fo::rest) x;
                           (* Adds rest of parameters as
                            * (Fun foo_CML_param <initialize refs>) *)
                           param_defs_from_formals rest inner_exp
                         od);
        return (param, preamble)
      od
  od
End

Definition initial_type_env_def:
  initial_type_env [] = return [] ∧
  initial_type_env ((Formal n t attrs)::rest) =
  if attrs ≠ [] then
    fail "initial_type_env: Attributes unsupported"
  else
    do
      rest' <- initial_type_env rest;
      return ((n, t)::rest')
    od
End

Definition from_method_def:
  from_method (Method isStatic hasBody overridingPath nam
                      typeParams params body outTypes outVars) =
  if isStatic = F then
    fail "from_method: non-static methods currently unsupported"
  else if hasBody = F then
    fail "from_method: Method must have a body"
  else if overridingPath ≠ NONE then
    fail "from_method: Overriding methods currently unsupported"
  else if typeParams ≠ [] then
    fail "from_method: Type parameters for methods currently unsupported"
  else if outTypes ≠ [] then
    fail "from_method: Methods with return values currently unsupported"
  else if outVars = NONE then
    fail "from_method: NONE for outVars is unexpected"
  else if outVars ≠ SOME [] then
    fail "from_method: Methods with return values currently unsupported"
  else
    do
      fun_name <<- dest_Name nam;
      (cml_param, preamble) <- method_preamble_from_formal params;
      env <- initial_type_env params;
      (cml_body, _) <- from_stmts body env;
      cml_body <- preamble cml_body;
      return (fun_name, cml_param, cml_body)
    od
End

Definition from_classItem_def:
  from_classItem (ClassItem_Method m) = from_method m
End

Definition compile_def:
  (compile ([mod1; mod2]: dafny_ast$module list) =
   (* TODO Don't ignore first module which contains definitions for nat
        and tuples for now *)
   (* TODO Properly handle module (containing main) *)
   case mod2 of
   | Module _ _ (SOME [ModuleItem_Class (Class _ _ _ _ _ cis _)]) =>
       do
         fun_defs <- result_mmap from_classItem cis;
         (* TODO Look at how PureCake detangles Dletrecs
          * Having one big Dletrec probably does not result in a performance
          * penalty unless functions are used in a higher order way *)
         fun_defs <<- [(Dletrec unknown_loc fun_defs)];
         return (fun_defs ++ [Dlet unknown_loc Pany
                                   (cml_fapp (Var (Short "Main")) [Unit])])
       od
   | _ => fail "Unexpected ModuleItem") ∧
  compile _ = fail "compile: Program does not contain exactly two modules"
End

(* Unpacks the AST from M. If the process failed, create a program that prints
   the error. *)
Definition unpack_def:
  unpack m =
  case m of
  | INR d =>
      d
  | INL s =>
      [Dlet unknown_loc Pany
            (cml_fapp (Var (Short "print")) [Lit (StrLit s)])]
End

(* Testing *)
open dafny_sexpTheory
open sexp_to_dafnyTheory
open fromSexpTheory simpleSexpParseTheory
open TextIO
(* val _ = astPP.disable_astPP(); *)
val _ = astPP.enable_astPP();

val inStream = TextIO.openIn "./tests/method_call_with_args.sexp";
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
val outFile = TextIO.openOut "./tests/method_call_with_args.cml.sexp";
val _ = TextIO.output (outFile, cml_sexp_str_r);
val _ = TextIO.closeOut outFile

val _ = export_theory();
