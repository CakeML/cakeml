module Lex where
import Data.List as List
import Data.Char as Char
import Tokens


data Symbol = 
    StringS String
  | NumberS Integer
  | OtherS String
  | ErrorS

read_while p "" s = (List.reverse s,"")
read_while p (c:cs) s =
  if p c then read_while p cs (c : s)
         else (List.reverse s, c:cs)

is_single_char_symbol c = c `elem` "()[];,_"

isSymbol c = not (isSpace c) && not (isDigit c) && not (isAlpha c) &&
             not (is_single_char_symbol c) && Char.ord ' ' < Char.ord c && c /= '.'

read_string str s =
  if List.null str then (ErrorS,"") else
  if List.head str == '"' then (StringS s,List.tail str) else
  if List.head str == '\n' then (ErrorS,List.tail str) else
  if List.head str /= '\\' then read_string (List.tail str) (s ++ [List.head str]) else
    case List.tail str of
      '\\':cs -> read_string cs (s ++ "\\")
      '"':cs -> read_string cs (s ++ "\"")
      'n':cs -> read_string cs (s ++ "\n")
      't':cs -> read_string cs (s ++ "\t")
      _ -> (ErrorS,List.tail str)

skip_comment "" d = Nothing
skip_comment [x] d = Nothing
skip_comment (x:y:xs) d =
     if [x,y] == "(*" then skip_comment xs (d+1) else
     if [x,y] == "*)" then (if d == 0 then Just xs else skip_comment xs (d-1))
     else skip_comment (y:xs) d

isAlphaNumPrime c = Char.isAlphaNum c || c == '\'' || c == '_' 

moduleRead initP c s =
  let (n,rest) = read_while initP s [c]
  in
    case rest of
      [] -> (OtherS n, rest)
      [h] -> if h == '.' then (ErrorS, [])
             else (OtherS n, rest)
      h1:h2:rest' ->
        if h1 == '.' then
          let nextP = if isAlpha h2 then Just isAlphaNumPrime
                      else if Lex.isSymbol h2 then Just Lex.isSymbol
                      else Nothing
          in
            case nextP of
              Nothing -> (ErrorS, rest')
              Just p ->
                let (n2, rest'') = read_while p rest' [h2]
                in
                  (OtherS (n ++ "." ++ n2), rest'')
        else (OtherS n, rest)

next_sym "" = Nothing
next_sym (c:str) =
  if isSpace c then
    next_sym str
  else if isDigit c then
    let (n,rest) = read_while isDigit str [] in
      Just (NumberS (read (c:n)), rest)
  else if isAlpha c then
    let (n,rest) = moduleRead isAlphaNumPrime c str in
      Just (n, rest)
  else if c == '\'' then
    let (n,rest) = read_while Char.isAlphaNum str [c] in
      Just (OtherS n, rest)
  else if c == '"' then
    let (t,rest) = read_string str "" in
      Just (t, rest)
  else if List.isPrefixOf "*)" (c:str) then
    Just (ErrorS, List.tail str)
  else if List.isPrefixOf "(*" (c:str) then
    case skip_comment (List.tail str) 0 of
      Nothing -> Just (ErrorS, "")
      Just rest -> next_sym rest
  else if is_single_char_symbol c then
    Just (OtherS [c], str)
  else if Lex.isSymbol c then
    let (n,rest) = moduleRead Lex.isSymbol c str in
      Just (n, rest)
  else 
    Just (ErrorS, str)

splitAtP p [] k = k [] []
splitAtP p (h:t) k = if p h then k [] (h:t)
                     else splitAtP p t (\p -> k (h:p))

moduleSplit s =
  splitAtP (\c -> c == '.') s
           (\p sfx ->
             case sfx of
               [] -> if isAlpha (List.head s) then AlphaT s
                     else SymbolT s
               [_] -> LexErrorT
               _:t -> if '.' `elem` t then LexErrorT
                       else LongidT p t)

get_token s =
  if s == "#" then HashT else
  if s == "(" then LparT else
  if s == ")" then RparT else
  if s == "*" then StarT else
  if s == "," then CommaT else
  if s == "->" then ArrowT else
  if s == "..." then DotsT else
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
  if List.head s == '\'' then TyvarT s else
  moduleSplit s

token_of_sym s =
  case s of
    ErrorS    -> LexErrorT
    StringS s -> StringT s
    NumberS n -> IntT n
    OtherS s  -> get_token s

next_token input =
  case next_sym input of
    Nothing -> Nothing
    Just (sym, rest_of_input) -> Just (token_of_sym sym, rest_of_input)

data Semihider = SH_END | SH_PAR

lex_aux acc error stk input =
  case next_token input of
    Nothing -> Nothing
    Just (token, rest) ->
      if token == SemicolonT && (List.null stk || error) then 
        Just (List.reverse (token:acc), rest)
      else
        let new_acc = (token:acc) in
          if error then lex_aux new_acc error stk rest
          else if token == LetT then lex_aux new_acc False (SH_END:stk) rest
          else if token == StructT then lex_aux new_acc False (SH_END:stk) rest
          else if token == SigT then lex_aux new_acc False (SH_END:stk) rest
          else if token == LparT then lex_aux new_acc False (SH_PAR:stk) rest
          else if token == EndT then
            case stk of
              SH_END : stk' -> lex_aux new_acc False stk' rest
              _ -> lex_aux new_acc True [] rest
          else if token == RparT then
            case stk of
              SH_PAR : stk' -> lex_aux new_acc False stk' rest
              _ -> lex_aux new_acc True [] rest
          else lex_aux new_acc False stk rest

lex_until_toplevel_semicolon input = lex_aux [] False [] input
