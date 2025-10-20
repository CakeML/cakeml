(*
  Abstract Syntax Tree for a subset of Dafny.
*)
Theory dafny_ast
Ancestors
  mlstring
Libs
  preamble


Datatype:
  type =
  | BoolT
  | IntT
  | StrT
  | ArrT type
End

Datatype:
  un_op = Not
End

Datatype:
  bin_op = Lt | Le | Ge | Eq | Neq | Sub | Add | Mul | And | Or | Imp | Div | Mod
End

Datatype:
  lit =
  | BoolL bool
  | IntL int
  | StrL mlstring
End

Datatype:
  exp =
  | Lit lit
  | Var mlstring
  (* Exp_If test thn els *)
  | Exp_If exp exp exp
  | UnOp un_op exp
  | BinOp bin_op exp exp
  (* ArrLen arr *)
  | ArrLen exp
  (* ArrSel arr idx *)
  | ArrSel exp exp
  (* FunCall name args *)
  | FunCall mlstring (exp list)
  (* Forall var term *)
  | Forall (mlstring # type) exp
  | Old exp
  | OldHeap exp
  (* Let [(name, rhs)] body *)
  | Let ((mlstring # exp) list) exp
  (* ForallHeap mods term *)
  | ForallHeap (exp list) exp
  (* Prev, PrevHeap, SetPrev used in VCG output *)
  | Prev exp
  | PrevHeap exp
  | SetPrev exp
End

Overload If = “Exp_If”

Datatype:
  lhs_exp =
  | VarLhs mlstring
  (* ArrSelLhs arr idx *)
  | ArrSelLhs exp exp
End

(* https://dafny.org/dafny/DafnyRef/DafnyRef#sec-rhs-expression
   Our definition of rhs_exp does not quite match the one described in the
   reference, as method calls appear to be special (since they may result in
   multiple values) *)
Datatype:
  rhs_exp =
  | ExpRhs exp
  (* ArrAlloc length init_value type *)
  | ArrAlloc exp exp type
End

Datatype:
  statement =
  | Skip
  | Assert exp
  | Then statement statement
  | If exp statement statement
  (* Dec local scope
     - scope also contains possible assignments *)
  | Dec (mlstring # type) statement
  | Assign ((lhs_exp # rhs_exp) list)
  (* While guard invariants decreases mod body *)
  | While exp (exp list) (exp list) (exp list) statement
  | Print exp type
  (* MetCall lhss name args
     - Results of a method call must always be bound to something, hence lhss *)
  | MetCall (lhs_exp list) mlstring (exp list)
  | Return
End

Datatype:
  member_decl =
  (* Method name ins req ens reads
            decreases outs mod body *)
  | Method mlstring ((mlstring # type) list) (exp list) (exp list) (exp list)
           (exp list) ((mlstring # type) list) (exp list) statement
  (* Function name ins result_type req reads
              decreases body *)
  | Function mlstring ((mlstring # type) list) type (exp list) (exp list)
             (exp list) exp
End

Definition member_name_def[simp]:
  member_name (Method name _ _ _ _ _ _ _ _) = name ∧
  member_name (Function name _ _ _ _ _ _) = name
End

Definition get_param_names_def[simp]:
  get_param_names (Method _ ins _ _ _ _ outs _ _) =
    MAP FST ins ++ MAP FST outs ∧
  get_param_names (Function _ ins _ _ _ _ _) = MAP FST ins
End

Datatype:
  (* For now, we only consider programs with a single module that use the
     default class *)
  program = Program (member_decl list)
End
