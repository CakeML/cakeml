(*
  Definitions to convert Dafny's AST into CakeML's AST.
*)

open preamble
open result_monadTheory
open astTheory semanticPrimitivesTheory (* CakeML AST *)
open dafny_astTheory

val _ = new_theory "dafny_to_cakeml";

(* TODO Add type annotations? *)

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

Definition gen_literal_def:
  gen_literal l =
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
   (* TODO Unclear how to handle this case
      Rust: https://github.com/dafny-lang/dafny/blob/ddea4d4f0f3e3c84276bf2dcf2b3f91e82f373cf/Source/DafnyCore/Backends/Rust/Dafny-compiler-rust.dfy#L3829-L3832*)
   | IntLiteral _ _ =>
       fail "IntLiteral _ _: Unclear how to handle"
   (* TODO Look into Rat module in basis *)
   | DecLiteral s1 s2 typ =>
       fail "DecLiteral s1 s2 typ: TODO"
   (* FIXME String/Char support incomplete or incorrect - see
      toDafnyAstScript for more details *)
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

Definition gen_expression_def:
  (gen_expression e =
   case e of
   | Literal l =>
       gen_literal l
   | _ => fail "gen_expression_def: TODO")
End

Definition gen_statement_def:
  (gen_statement stmt =
   case stmt of
   | Print e =>
       do
         cml_e <- gen_expression e;
         return (App Opapp [Var (Short "print"); cml_e])
       od
   | _ => fail "TODO: gen_statement")
End

Definition compile_def:
  compile p =
  do
    (* FIXME: Assume that we only have a main function *)
    if (LENGTH p ≠ 2) then
      fail "Program should have exactly 2 modules"
    else
      do
        (* FIXME Ignore first module which contains definitions for nat and tuples for now *)
        case (EL 1 p) of
        | Module _ _ (SOME [ModuleItem_Class (Class _ _ _ _ _ [ClassItem_Method m] _)]) =>
            (case m of
            | Method _ _ _ _ _ _ [stmt; earlyret] _ _ =>
                do
                  main_stmt <- gen_statement stmt;
                  return ([Dletrec (Locs (POSN 0 15) (POSN 0 50))
                                   [("Main","",
                                     Mat (Var (Short ""))
                                         [(Pcon NONE [],
                                           main_stmt)])];
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

val _ = export_theory();
