module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast as Ast
import Typecheck --(inferTop, TypeState, empty_decls, inferProg, merge_types)
import Text.Parsec.Pos (initialPos)
import Data.Char (isSpace)
import Data.Map as Map
--import Interp
import InitialProgram
import ToOCaml (progToOCaml)
import ToSML (progToSML)
import Text.PrettyPrint
import System.Console.GetOpt
import Control.Monad

data Error = 
    LexError String
  | ParseError String
  | TypeError String
  | RuntimeError String

instance Show Main.Error where
  show (LexError s) = "Lex error:\n  " ++ s
  show (ParseError s) = "Parse error:\n  " ++ s
  show (TypeError s) = "Type error:\n  " ++ s
  show (RuntimeError s) = "Uncaught exception:\n  " ++ s

getLexError :: Either Parsec.ParseError a -> Either Main.Error a
getLexError (Left e) = Left (LexError (show e))
getLexError (Right e) = Right e

getParseError :: Either Parsec.ParseError a -> Either Main.Error a
getParseError (Left e) = Left (ParseError (show e))
getParseError (Right e) = Right e

getTypeError :: Either (SourcePos,String) x -> Either Main.Error x
getTypeError (Left (pos,e)) = Left (TypeError (show pos ++ "\n" ++ e))
getTypeError (Right e) = Right e

type MainState = (String, SourcePos, TypeState)

checkOne :: MainState -> Either Main.Error (MainState, Maybe (String, Top))
checkOne (input, pos, tenvs) =
  do (toks,rest,pos') <- getLexError (lex_until_toplevel_semicolon input pos);
     if toks == [] then
       return ((rest, pos', tenvs), Nothing) 
     else
       do ast <- getParseError (parseTop toks);
          tenvs' <- getTypeError (inferTop tenvs ast);
	  return ((rest, pos', merge_types tenvs' tenvs), Just (show tenvs', ast))

isFinished (input,_,_) = List.all isSpace input

data CmdOpt = 
    OCaml
  | SML
  | Types
  | Help
  deriving Eq

checkAll :: [CmdOpt] -> MainState -> Prog -> IO Prog
checkAll cmd s acc =
  if isFinished s then
    return acc
  else
    case checkOne s of
      Left err -> putStrLn (show err) >> return []
      Right (res,Nothing) -> return acc
      Right (res,Just (output,ast)) -> 
        if List.elem Types cmd then
          putStrLn output >> checkAll cmd res (ast:acc)
        else
          checkAll cmd res (ast:acc)

init_tenv :: TypeState
init_tenv = 
  case inferProg (TypeState empty_decls Map.empty Map.empty Map.empty Map.empty) (prim_types_program ++ basis_program) of
    Left err -> error (show err ++ " in basis program.")
    Right x -> x

options = [Option ['o'] ["ocaml"] (NoArg OCaml) "Print OCaml",
           Option ['s'] ["sml"] (NoArg SML) "Print SML",
           Option ['t'] ["types"] (NoArg Types) "Print types",
           Option ['h'] ["help"] (NoArg Help) "Display help"]

-- definitions from the initial program that shouldn't be made in OCaml
isBadOCaml (Tdec (Dtype [(_, name,_)])) =
  List.elem (show name) ["bool","list"]
isBadOCaml (Tdec (Dlet (Pvar n) _ _)) =
  show n == "~"
isBadOCaml _ = False

-- definitions from the initial program that shouldn't be made in SML
isBadSML (Tdec (Dtype [(_, name,_)])) =
  List.elem (show name) ["bool","list"]
isBadSML (Tdec (Dlet (Pvar name) _ _)) =
  List.elem (show name) ["ref", "="]
isBadSML _ = False

main = 
  do args <- getArgs;
     let (opts, nonOpts, errors) = getOpt Permute options args;
     if List.elem Help opts || errors /= [] || List.length nonOpts /= 1 then
       putStr (usageInfo "Unverified CakeML front-end and translator: \nUsage: cakeml [-oth] file" options)
     else 
       do unless (List.length nonOpts == 1) 
               (error "Command-line error: must have exactly 1 non-optional argument: the CakeML source file to process")
          let name = List.head nonOpts;
          input <- readFile name;
	  prog <- checkAll opts (input, initialPos name, init_tenv) [];
          if List.elem OCaml opts then
            putStrLn (render (progToOCaml (List.filter (not . isBadOCaml) (prim_types_program ++ basis_program) ++ List.reverse prog)))
          else
            return ();
          if List.elem SML opts then
            putStrLn (render (progToSML (List.filter (not . isBadSML) (prim_types_program ++ basis_program) ++ List.reverse prog)))
          else
            return ();
           

     {-

merge3 (x',y',z') (x,y,z) =
  (Map.union x' x, Map.union y' y, Map.union z' z)

type MainState = (String, SourcePos, Ast.Tdef_env, Ast.Ctor_env, (TenvM,TenvC,Tenv), Store, (EnvM, EnvC, EnvE))

runOne :: MainState -> Either Main.Error (MainState, String)
runOne (input, pos, tdef_env, ctor_env, tenvs, store, envs) =
  do (toks,rest,pos') <- getLexError (lex_until_toplevel_semicolon input pos);
     ast <- getParseError (parseTop toks);
     let (tdef_env', ctor_env', ast') = elab_top tdef_env ctor_env ast;
     tenvs' <- getTypeError (inferTop tenvs ast');
     let (menv,cenv,env) = envs;
     let (store', cenv', res) = run_eval_top menv cenv store env ast';
     case res of 
       Rval (menv',env') -> 
         return ((rest, pos',
		  merge tdef_env' tdef_env, 
		  merge ctor_env' ctor_env,
		  merge3 tenvs' tenvs,
		  store',
		  merge3 (menv',cenv',env') envs),
		 show env')
       Rerr err -> Left (RuntimeError (show err))

isFinished (input,_,_,_,_,_,_) = List.all isSpace input

runAll :: MainState -> IO ()
runAll s =
  if isFinished s then
    return ()
  else
    case runOne s of
      Left err -> putStrLn (show err)
      Right (res,output) -> putStrLn output >> runAll res

main = 
  do args <- getArgs;
     let name = List.head args;
     input <- readFile name;
     runAll (input, initialPos name, init_elab_env, Map.empty, (Map.empty,Typecheck.init_tenvC,init_type_env), [], (Map.empty, Interp.init_envC, init_env));

-}
