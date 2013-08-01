module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast (elab_top, init_elab_env)
import Ast as Ast
import Typecheck (inferTop, TenvM, TenvC, Tenv, init_type_env, init_tenvC)
import Text.Parsec.Pos (initialPos)
import Data.Char (isSpace)
import Interp

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

merge3 (x',y',z') (x,y,z) =
  (merge x' x, merge y' y, merge z' z)

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
     runAll (input, initialPos name, init_elab_env, Ast.emp, (Ast.emp,Typecheck.init_tenvC,init_type_env), [], (Ast.emp, Interp.init_envC, init_env));
