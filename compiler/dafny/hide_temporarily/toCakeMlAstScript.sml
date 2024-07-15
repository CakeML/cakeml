(*
  Definitions to convert Dafny's AST into CakeML's AST.

  TODO: Rename to dafny_to_cakeml
*)

open preamble dafny_utilTheory
(* CakeML AST *)
open astTheory semanticPrimitivesTheory
open dafnyAstTheory
open mlintTheory

val _ = new_theory "toCakeMlAst";

(* TODO Remove after done with testing *)
open toDafnyAstTheory

(* local *)
(* open pegLib simpleSexpPEGTheory pegexecTheory *)

(* Definition get_sexp_def: *)
(*   get_sexp (Success _ se _) = se *)
(* End *)
(*   val ds = derive_compset_distincts ``:sexpNT`` *)
(*   val {lookups,...} = derive_lookup_ths {pegth = sexpPEG_def, ntty = ``:sexpNT``, *)
(*                                    simp = SIMP_CONV (srw_ss())} *)
(*   val _ = computeLib.add_funs (ds::lookups) *)
(*   val _ = let *)
(*     open computeLib *)
(*   in *)
(*     set_skip the_compset ``evalcase_CASE`` (SOME 1); *)
(*     set_skip the_compset ``option_CASE`` (SOME 1); *)
(*     set_skip the_compset ``COND`` (SOME 1) *)
(*   end *)
(* in *)
(* fun parse_sexp s = let *)
(*   val str_t = stringSyntax.fromMLstring s *)
(*   val th = EVAL ``get_sexp (destResult (peg_exec sexpPEG *)
(*                      (pnt sxnt_sexp) *)
(*                      (MAPi (λi c. *)
(*                                (c, *)
(*                                 Locs (POSN 1 (i + 1)) (POSN 1 (i + 1)))) *)
(*                       ^str_t) *)
(*                      [] NONE [] done failed))`` *)
(* in *)
(*   (rhs (concl th)) *)
(* end *)
(* end *)

(* val test_string = "(Program ((Module.Module (Name.Name \"_System\") () (Some ((ModuleItem.Newtype (Newtype.Newtype (Name.Name \"nat\") () (Type.Primitive (Primitive.Int)) (NewtypeRange.NoRange) () (None) ((Attribute.Attribute \"axiom\" ())))) (ModuleItem.Datatype (Datatype.Datatype (Name.Name \"Tuple2\") (Ident.Ident (Name.Name \"_System\")) ((TypeArgDecl.TypeArgDecl (Ident.Ident (Name.Name \"T0\")) ()) (TypeArgDecl.TypeArgDecl (Ident.Ident (Name.Name \"T1\")) ())) ((DatatypeCtor.DatatypeCtor (Name.Name \"___hMake2\") ((DatatypeDtor.DatatypeDtor (Formal.Formal (Name.Name \"_0\") (Type.TypeArg (Ident.Ident (Name.Name \"T0\"))) ()) (Some \"_0\")) (DatatypeDtor.DatatypeDtor (Formal.Formal (Name.Name \"_1\") (Type.TypeArg (Ident.Ident (Name.Name \"T1\"))) ()) (Some \"_1\"))) true)) () false ())) (ModuleItem.Datatype (Datatype.Datatype (Name.Name \"Tuple0\") (Ident.Ident (Name.Name \"_System\")) () ((DatatypeCtor.DatatypeCtor (Name.Name \"___hMake0\") () false)) () false ()))))) (Module.Module (Name.Name \"_module\") () (Some ((ModuleItem.Class (Class.Class (Name.Name \"__default\") (Ident.Ident (Name.Name \"_module\")) () () () ((ClassItem.Method (Method.Method true true (None) (Name.Name \"Main\") () () ((Statement.Print (Expression.Literal (Literal.StringLiteral \"Hello, World\" false))) (Statement.EarlyReturn)) () (Some ())))) ())))))))"; *)


(* val test_dast = rhs (concl (EVAL “THE (sexp_program ^(parse_sexp test_string))”)); *)

Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload None = “Con (SOME (Short "None")) []”


Definition from_string_def:
  from_string s =
  case (mlint$fromString (implode s)) of
  | SOME i =>
      return i
  | NONE =>
      fail ("Could not convert into int: " ++ s)
End

Definition gen_literal_def:
  gen_literal (l: dafnyAst$literal): (ast$exp M) =
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
  (gen_expression (e: dafnyAst$expression): (ast$exp M) =
   case e of
   | Literal l =>
       gen_literal l
   | _ => fail "gen_expression_def: TODO")
End

Definition gen_statement_def:
  (gen_statement (stmt: dafnyAst$statement): (ast$exp M) =
   case stmt of
   | Print e =>
       do
         cml_e <- gen_expression e;
         return (App Opapp [Var (Short "print"); cml_e])
       od
   | _ => fail "TODO: gen_statement")
End

Definition compile_def:
  compile (p: (module list)) : (dec list) M =
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
  unpack (m : (dec list) M) : (dec list) =
  case m of
  | INL d =>
      d
  | INR s =>
      [Dlet (Locs (POSN 0 14) UNKNOWNpt) (Pvar "it")
       (App Opapp [Var (Short "print"); Lit (StrLit s)])]
End

(* val test = EVAL “unpack (compile [Module (Name "_System") [] *)
(*                                  (SOME *)
(*                                   [ModuleItem_Newtype *)
(*                                    (Newtype (Name "nat") [] (Primitive Int) NoRange [] NONE *)
(*                                             [Attribute "axiom" []]); *)
(*                                    ModuleItem_Datatype *)
(*                                    (Datatype (Name "Tuple2") (Ident (Name "_System")) *)
(*                                              [TypeArgDecl (Ident (Name "T0")) []; *)
(*                                               TypeArgDecl (Ident (Name "T1")) []] *)
(*                                              [DatatypeCtor (Name "___hMake2") *)
(*                                                            [DatatypeDtor *)
(*                                                             (Formal (Name "_0") (TypeArg (Ident (Name "T0"))) []) *)
(*                                                             (SOME "_0"); *)
(*                                                             DatatypeDtor *)
(*                                                             (Formal (Name "_1") (TypeArg (Ident (Name "T1"))) []) *)
(*                                                             (SOME "_1")] T] [] F []); *)
(*                                    ModuleItem_Datatype *)
(*                                    (Datatype (Name "Tuple0") (Ident (Name "_System")) [] *)
(*                                              [DatatypeCtor (Name "___hMake0") [] F] [] F [])]); *)
(*                           Module (Name "_module") [] *)
(*                                  (SOME *)
(*                                   [ModuleItem_Class *)
(*                                    (Class (Name "__default") (Ident (Name "_module")) [] [] [] *)
(*                                           [ClassItem_Method *)
(*                                    (Method T T NONE (Name "Main") [] [] *)
(*                                            [Print (Literal (StringLiteral "Hello, World" F)); *)
(*                                             EarlyReturn] [] (SOME []))] [])])])”; *)

(* val test = EVAL “gen_literal (BoolLiteral F)”; *)
(* val test = EVAL “gen_literal (BoolLiteral T)”; *)
(* val test = EVAL “gen_literal (IntLiteral "42" (Primitive Int))”; *)
(* val test = EVAL “gen_literal (DecLiteral "42" "100" (Primitive Real))”; *)
(* val test = EVAL “gen_literal (Null *)
(*                               (Nullable *)
(*                                (Path *)
(*                                 [Ident (Name "_System"); *)
(*                                  Ident (Name "object")] [] *)
(*                                 (ResolvedType_Newtype *)
(*                                  (Passthrough *)
(*                                   "<b>Unsupported: <i>Traits</i></b>") *)
(*                                  NoRange T []))))”; *)
(* val test = EVAL “gen_literal (CharLiteral #"E")”; *)
(* val test = EVAL “gen_literal (StringLiteral "cake" F)”; *)

val _ = export_theory();
