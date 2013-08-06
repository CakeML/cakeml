module Tokens where

data Token =
    WhitespaceT Integer | NewlineT | LexErrorT
  | HashT | LparT | RparT | StarT | CommaT | ArrowT | DotsT | ColonT | SealT
  | SemicolonT | EqualsT | DarrowT | LbrackT | RbrackT | UnderbarT | LbraceT
  | BarT | RbraceT | AbstypeT | AndT | AndalsoT | AsT | CaseT | DatatypeT | DoT
  | ElseT | EndT | EqtypeT | ExceptionT | FnT | FunT | FunctorT | HandleT | IfT
  | InT | IncludeT | InfixT | InfixrT | LetT | LocalT | NonfixT | OfT | OpT
  | OpenT | OrelseT | RaiseT | RecT | SharingT | SigT | SignatureT | StructT
  | StructureT | ThenT | TypeT | ValT | WhereT | WhileT | WithT | WithtypeT
  | ZeroT
  | DigitT String
  | NumericT String
  | IntT Integer
  | HexintT String
  | WordT String
  | HexwordT String
  | RealT String
  | StringT String
  | CharT String
  | TyvarT String
  | AlphaT String
  | SymbolT String
  | LongidT String String
  deriving (Eq,Show)
-- TODO improve Show
