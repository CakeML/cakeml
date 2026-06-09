(*
  The tokens CakeML concrete syntax.
  Some tokens are from Standard ML and not used in CakeML.
*)
Theory tokens
Ancestors[qualified]
  integer mlstring

Datatype:
  path = Mod mlstring path | End
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
  | HexintT mlstring
  | WordT num
  | RealT mlstring
  | StringT mlstring
  | CharT char
  | TyvarT mlstring
  | AlphaT mlstring
  | SymbolT mlstring
  | LongidT path mlstring
  | FFIT mlstring
  | REPLIDT mlstring
End
