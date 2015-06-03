module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast as Ast
import Typecheck (inferTop, Decls, TenvT, TenvM, TenvC, Tenv, append_decls, empty_decls, inferProg)
import Text.Parsec.Pos (initialPos)
import Data.Char (isSpace)
import Data.Map as Map
--import Interp
import InitialProgram

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

merge_types (decls',tenvT',menv',cenv',env') (decls,tenvT,menv,cenv,env) =
  (append_decls decls' decls, Map.union tenvT' tenvT, Map.union menv' menv, Map.union cenv' cenv, Map.union env' env)

type MainState = (String, SourcePos, (Decls,TenvT,TenvM,TenvC,Tenv))

checkOne :: MainState -> Either Main.Error (MainState, String)
checkOne (input, pos, tenvs) =
  do (toks,rest,pos') <- getLexError (lex_until_toplevel_semicolon input pos);
     ast <- getParseError (parseTop toks);
     tenvs' <- getTypeError (inferTop tenvs ast);
     return ((rest, pos', merge_types tenvs' tenvs), show tenvs')

isFinished (input,_,_) = List.all isSpace input

checkAll :: MainState -> IO ()
checkAll s =
  if isFinished s then
    return ()
  else
    case checkOne s of
      Left err -> putStrLn (show err)
      Right (res,output) -> putStrLn output >> checkAll res

init_tenv = 
  case inferProg (empty_decls, Map.empty, Map.empty, Map.empty, Map.empty) (prim_types_program ++ basis_program) of
    Left err -> error "Bad basis"
    Right x -> x

main = 
  do args <- getArgs;
     let name = List.head args;
     input <- readFile name;
     checkAll (input, initialPos name, init_tenv)

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
