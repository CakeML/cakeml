(*
  The tokens CakeML concrete syntax.
  Some tokens are from Standard ML and not used in CakeML.
*)
open HolKernel Parse boolLib bossLib;

local open integerTheory stringTheory in end;
val _ = new_theory "tokens"
val _ = set_grammar_ancestry ["integer", "string"];

Datatype:
  path = Mod string path | End
End

Datatype:
  token =
    WhitespaceT num | NewlineT | LexErrorT
  | HashT | LparT | RparT | StarT | CommaT | ArrowT | DotsT | ColonT | SealT
  | SemicolonT | EqualsT | DarrowT | LbrackT | RbrackT | UnderbarT | LbraceT
  | BarT | RbraceT | AndT | AndalsoT | AsT | CaseT | DatatypeT
  | ElseT | EndT | EqtypeT | ExceptionT | FnT | FunT | HandleT | IfT
  | InT | IncludeT | LetT | LocalT | OfT | OpT
  | OpenT | OrelseT | RaiseT | RecT | SharingT | SigT | SignatureT | StructT
  | StructureT | ThenT | TypeT | ValT | WhereT | WhileT | WithT | WithtypeT
  | IntT int
  | HexintT string
  | WordT num
  | RealT string
  | StringT string
  | CharT char
  | TyvarT string
  | AlphaT string
  | SymbolT string
  | LongidT path string
  | FFIT string
  | REPLIDT string
End

val _ = export_theory()
