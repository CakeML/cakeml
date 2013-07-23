module Lex where
import Data.List as List
import Data.Char as Char
import Tokens
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Char

single_char_symbol = oneOf "()[];,_"

-- TODO: symbol_char seems too permissive
symbol_char = oneOf "!\"#$%&'*+-/:<=>?@\\^`{|}~"

string_char =
  (try (string "\\\\") >> return '\\')
  <|>
  (try (string "\\\"") >> return '"')
  <|>
  (try (string "\\n") >> return '\n')
  <|>
  (try (string "\\t") >> return '\t')
  <|>
  noneOf ['\\', '\n', '"']

skip_comment d =
  (try (string "(*") >> skip_comment (d + 1))
  <|>
  (try (string "*)") >> (if d == 0 then return () else skip_comment (d - 1)))
  <|>
  (anyChar >> skip_comment d)

alpha_ident =
  do c <- letter;
     s <- many (alphaNum <|> oneOf "'_");
     return (c:s)

ident = alpha_ident <|> many1 symbol_char

next_token =
  (space >> next_token) 
  <|>
  do digits <- many1 digit;
     return (IntT (read digits))
  <|>
  do id1 <- alpha_ident;
     option (get_token_alpha id1) (char '.' >> do id2 <- ident; return (LongidT id1 id2))
  <|>
  do char '\'';
     tvar <- many1 alphaNum;
     return (TyvarT ('\'':tvar))
  <|>
  fmap StringT (between (char '"') (char '"') (many string_char))
  <|>
  (try (string "*)") >> fail "stray \"*)\"")
  <|>
  (try (string "(*") >> skip_comment 0 >> next_token)
  <|>
  fmap (\c -> get_token_sym [c]) single_char_symbol
  <|>
  do id1 <- many1 symbol_char ;
     option (get_token_sym id1) (char '.' >> do id2 <- ident; return (LongidT id1 id2))

get_token_sym s =
  if s == "#" then HashT else
  if s == "(" then LparT else
  if s == ")" then RparT else
  if s == "*" then StarT else
  if s == "," then CommaT else
  if s == "->" then ArrowT else
  if s == "..." then DotsT else -- TODO, can't ever get this because . is not a symbol_char
  if s == ":" then ColonT else
  if s == ":>" then SealT else
  if s == ";" then SemicolonT else
  if s == "=" then EqualsT else
  if s == "=>" then DarrowT else
  if s == "[" then LbrackT else
  if s == "]" then RbrackT else
  if s == "_" then UnderbarT else
  if s == "{" then LbraceT else
  if s == "}" then RbraceT else
  if s == "|" then BarT else
  SymbolT s

get_token_alpha s =
  if s == "abstype" then AbstypeT else
  if s == "and" then AndT else
  if s == "andalso" then AndalsoT else
  if s == "as" then AsT else
  if s == "case" then CaseT else
  if s == "datatype" then DatatypeT else
  if s == "do" then DoT else
  if s == "else" then ElseT else
  if s == "end" then EndT else
  if s == "eqtype" then EqtypeT else
  if s == "exception" then ExceptionT else
  if s == "fn" then FnT else
  if s == "fun" then FunT else
  if s == "functor" then FunctorT else
  if s == "handle" then HandleT else
  if s == "if" then IfT else
  if s == "in" then InT else
  if s == "include" then IncludeT else
  if s == "infix" then InfixT else
  if s == "infixr" then InfixrT else
  if s == "let" then LetT else
  if s == "local" then LocalT else
  if s == "nonfix" then NonfixT else
  if s == "of" then OfT else
  if s == "op" then OpT else
  if s == "open" then OpenT else
  if s == "orelse" then OrelseT else
  if s == "raise" then RaiseT else
  if s == "rec" then RecT else
  if s == "sharing" then SharingT else
  if s == "sig" then SigT else
  if s == "signature" then SignatureT else
  if s == "struct" then StructT else
  if s == "structure" then StructureT else
  if s == "then" then ThenT else
  if s == "type" then TypeT else
  if s == "val" then ValT else
  if s == "where" then WhereT else
  if s == "while" then WhileT else
  if s == "with" then WithT else
  if s == "withtype" then WithtypeT else
  AlphaT s

data Semihider = SH_END | SH_PAR

lex_aux acc stk =
  do pos <- getPosition;
     token <- next_token;
     if token == SemicolonT && List.null stk then 
        return (List.reverse ((token,pos):acc))
     else
       let new_acc = (token,pos):acc in
         if token == LetT then lex_aux new_acc (SH_END:stk)
         else if token == StructT then lex_aux new_acc (SH_END:stk)
         else if token == SigT then lex_aux new_acc (SH_END:stk)
         else if token == LparT then lex_aux new_acc (SH_PAR:stk)
         else if token == EndT then
           case stk of
             SH_END : stk' -> lex_aux new_acc stk'
             _ -> fail "stray \"end\"" 
         else if token == RparT then
           case stk of
             SH_PAR : stk' -> lex_aux new_acc stk'
             _ -> fail "stray \")\""
         else lex_aux new_acc stk

lex_until_toplevel_semicolon :: String -> SourcePos -> Either ParseError ([(Token, SourcePos)], String, SourcePos)
lex_until_toplevel_semicolon input pos = 
  parse (do setPosition pos;
            toks <- lex_aux [] [];
            pos <- getPosition;
            rest <- getInput;
            return (toks, rest, pos))
         (sourceName pos)
         input
