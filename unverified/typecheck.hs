{-
 - Unlike the verified type inferencer, we go top down only unifying at the
 - leaves of the AST.  This helps the error messages a bit and means that we
 - only have to have source location information at the leaves.  So instead of
 - infer_e returning a type, it takes an extra argument that is the type that
 - the expression should have.
 -}


module Typecheck where
import Control.Monad.State.Lazy as State
import Data.Map as Map
import Data.List as List
import Ast
import Unify
import Text.Parsec.Pos (initialPos, SourcePos)
import Data.Maybe

data Infer_st = Infer_st { next_uvar :: Uvar, subst :: Subst }
type M_st_ex = State.StateT Infer_st (Either (SourcePos, String))

typeError :: SourcePos -> String -> M_st_ex a
typeError pos str = lift (Left (pos,str))

lookup_st_ex :: (HasPos k, Show k, Ord k) => k -> Ast.Env k v -> M_st_ex v
lookup_st_ex k env =
  case Ast.lookup k env of
    Nothing -> typeError (getPos k) ("unbound identifier: " ++ (show k))
    Just v -> return v 

type Tenv = Env VarN (Integer, Infer_t)
type TenvM = Env ModN Tenv
type TenvC = Env (Id ConN) ([TvarN], [T], Id TypeN)

fresh_uvar :: M_st_ex Infer_t
fresh_uvar =
  do n <- gets next_uvar;
     modify (\x -> x { next_uvar = n + 1 });
     return (Infer_Tuvar n)

n_fresh_uvar :: Integral a => a -> M_st_ex [Infer_t]
n_fresh_uvar n =
  if n == 0 then
    return []
  else
    do v <- fresh_uvar;
       vs <- n_fresh_uvar (n - 1);
       return (v:vs)

init_infer_state :: Infer_st
init_infer_state = Infer_st { next_uvar = 0, subst = Map.empty }

add_constraint :: SourcePos -> Infer_t -> Infer_t -> M_st_ex ()
add_constraint pos t1 t2 =
  do s <- gets subst;
     case t_unify s t1 t2 of
       Nothing -> typeError pos ("expected type: " ++ show t2 ++ "\nhad type: " ++ show t1)
       Just s -> do modify (\x -> x { subst = s });
                    return ()

get_next_uvar :: M_st_ex Uvar
get_next_uvar =
  do n <- gets next_uvar;
     return n

apply_subst :: Infer_t -> M_st_ex Infer_t
apply_subst t =
  do s <- gets subst;
     return (t_walkstar s t)

apply_subst_list :: [Infer_t] -> M_st_ex [Infer_t]
apply_subst_list ts =
  do s <- gets subst;
     return (List.map (t_walkstar s) ts)

generalise :: Uvar -> Integer -> Map.Map Uvar Integer -> Infer_t -> (Integer, Map.Map Uvar Integer, Infer_t)
generalise m n s (Infer_Tapp ts tc) =
  let (num_gen, s', ts') = generalise_list m n s ts in
    (num_gen, s', Infer_Tapp ts' tc)
generalise m n s (Infer_Tuvar uv) =
  case Map.lookup uv s of
    Just n -> (0, s, Infer_Tvar_db n)
    Nothing ->
      if m <= uv then
        (1, Map.insert uv n s, Infer_Tvar_db n)
      else
        (0, s, Infer_Tuvar uv)
generalise m n s (Infer_Tvar_db k) =
    (0, s, Infer_Tvar_db k)
generalise_list m n s [] = 
  (0,s,[])
generalise_list m n s (t:ts) =
  let (num_gen, s', t') = generalise m n s t in
  let (num_gen', s'', ts') = generalise_list m (num_gen + n) s' ts in
    (num_gen+num_gen', s'', t':ts')

infer_type_subst :: Env TvarN Infer_t -> T -> Infer_t
infer_type_subst s (Tvar tv) =
  case Ast.lookup tv s of 
    Just t -> t
    Nothing -> Infer_Tvar_db 0 -- should not happen
infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n
infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (List.map (infer_type_subst s) ts) tn

infer_deBruijn_subst :: [Infer_t] -> Infer_t -> Infer_t
infer_deBruijn_subst s (Infer_Tvar_db n) =
  if n < toInteger (List.length s) then
    s `genericIndex` n
  else 
    Infer_Tvar_db (n - toInteger (List.length s)) -- should not happen
infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (List.map (infer_deBruijn_subst s) ts) tn
infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n

infer_p :: TenvC -> Pat -> Infer_t -> M_st_ex [(VarN,Infer_t)]
infer_p cenv (Pvar n) t =
  return [(n,t)]
infer_p cenv (Plit (Bool b) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_bool) t;
     return []
infer_p cenv (Plit (IntLit i) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_int) t;
     return []
infer_p cenv (Plit Unit pos) t =
  do add_constraint pos (Infer_Tapp [] TC_unit) t;
     return []
infer_p cenv (Pcon cn_opt ps pos) t =
  case cn_opt of 
      Nothing ->
        do ts <- n_fresh_uvar (List.length ps);
           add_constraint pos (Infer_Tapp ts TC_tup) t;
           infer_ps cenv ps ts;
      Just cn ->
        do (tvs',ts,tn) <- lookup_st_ex cn cenv;
           ts' <- n_fresh_uvar (List.length tvs');
           add_constraint pos (Infer_Tapp ts' (TC_name tn)) t;
           infer_ps cenv ps (List.map (infer_type_subst (listToEnv (List.zip tvs' ts'))) ts)
infer_p cenv (Pref p pos) t =
  do t1 <- fresh_uvar;
     add_constraint pos (Infer_Tapp [t1] TC_ref) t;
     tenv <- infer_p cenv p t1;
     return tenv
infer_ps cenv [] [] =
  return []
infer_ps cenv (p:ps) (t:ts) =
  do tenv <- infer_p cenv p t;
     tenv' <- infer_ps cenv ps ts;
     return (tenv'++tenv)

constrain_uop :: Uop -> Infer_t -> M_st_ex Infer_t
constrain_uop uop t =
  case uop of
    Opderef -> return (Infer_Tapp [t] TC_ref)
    Opref pos ->
      do uvar <- fresh_uvar;
         add_constraint pos (Infer_Tapp [uvar] TC_ref) t;
         return uvar

constrain_op :: Op -> Infer_t -> M_st_ex (Infer_t,Infer_t)
constrain_op op t =
  case op of
    Opn opn pos ->
      do add_constraint pos (Infer_Tapp [] TC_int) t;
         return (Infer_Tapp [] TC_int,Infer_Tapp [] TC_int)
    Opb opb pos -> 
      do add_constraint pos (Infer_Tapp [] TC_bool) t;
         return (Infer_Tapp [] TC_int, Infer_Tapp [] TC_int)
    Equality pos ->
      do add_constraint pos (Infer_Tapp [] TC_bool) t;
         t1 <- fresh_uvar;
         return (t1,t1)
    Opapp ->
      do uvar <- fresh_uvar;
         return (Infer_Tapp [uvar,t] TC_fn, uvar)
    Opassign pos ->
      do add_constraint pos (Infer_Tapp [] TC_unit) t;
         t2 <- fresh_uvar;
         return (Infer_Tapp [t2] TC_ref, t2)

ensureDistinct msg select l =
  case getDup (List.map select l) of
    Nothing -> return ()
    Just x -> typeError (getPos x) ("duplicate " ++ msg ++ ": " ++ show x)

infer_e :: TenvM -> TenvC -> Tenv -> Exp -> Infer_t -> M_st_ex ()
infer_e menv cenv env (Raise err) t =
  return ()
infer_e menv cenv env (Handle e1 x e2) t =
  do infer_e menv cenv env e1 t;
     infer_e menv cenv (Ast.bind x (0,Infer_Tapp [] TC_int) env) e2 t
infer_e menv cenv tenv (Lit (Bool b) pos) t =
  add_constraint pos (Infer_Tapp [] TC_bool) t
infer_e menv cenv tenv (Lit (IntLit i) pos) t =
  add_constraint pos (Infer_Tapp [] TC_int) t
infer_e menv cenv tenv (Lit Unit pos) t =
  add_constraint pos (Infer_Tapp [] TC_unit) t
infer_e menv cenv env (Var (Short n)) t =
  do (tvs,t') <- lookup_st_ex n env;
     uvs <- n_fresh_uvar tvs;
     add_constraint (getPos n) (infer_deBruijn_subst uvs t') t
infer_e menv cenv env (Var (Long mn n)) t =
  do env' <- lookup_st_ex mn menv;
     (tvs,t') <- lookup_st_ex n env';
     uvs <- n_fresh_uvar tvs;
     add_constraint (getPos n) (infer_deBruijn_subst uvs t') t
infer_e menv cenv env (Con cn_opt es pos) t =
  case cn_opt of
    Nothing ->
      do ts <- n_fresh_uvar (List.length es);
         add_constraint pos (Infer_Tapp ts TC_tup) t;
         infer_es menv cenv env es ts
    Just cn ->
       do (tvs',ts,tn) <- lookup_st_ex cn cenv;
          ts' <- n_fresh_uvar (List.length tvs');
          add_constraint pos (Infer_Tapp ts' (TC_name tn)) t;
          infer_es menv cenv env es (List.map (infer_type_subst (listToEnv (List.zip tvs' ts'))) ts)
infer_e menv cenv env (Fun x e pos) t =
  do t1 <- fresh_uvar;
     t2 <- fresh_uvar;
     add_constraint pos (Infer_Tapp [t1,t2] TC_fn) t
     infer_e menv cenv (bind x (0,t1) env) e t2;
infer_e menv cenv env (Uapp uop e) t =
  do t' <- constrain_uop uop t;
     infer_e menv cenv env e t'
infer_e menv cenv env (App op e1 e2) t =
  do (t1,t2) <- constrain_op op t
     infer_e menv cenv env e1 t1;
     infer_e menv cenv env e2 t2
infer_e menv cenv env (Log log e1 e2) t =
  do add_constraint (getPos log) (Infer_Tapp [] TC_bool) t;
     infer_e menv cenv env e1 (Infer_Tapp [] TC_bool);
     infer_e menv cenv env e2 (Infer_Tapp [] TC_bool)
infer_e menv cenv env (If e1 e2 e3) t =
  do infer_e menv cenv env e1 (Infer_Tapp [] TC_bool);
     infer_e menv cenv env e2 t;
     infer_e menv cenv env e3 t
infer_e menv cenv env (Mat e pes) t =
  if List.null pes then
    error "Empty pattern match"
  else
    do t' <- fresh_uvar;
       infer_e menv cenv env e t';
       infer_pes menv cenv env pes t' t
infer_e menv cenv env (Let x e1 e2) t =
  do t1 <- fresh_uvar;
     infer_e menv cenv env e1 t1;
     infer_e menv cenv (bind x (0,t1) env) e2 t
infer_e menv cenv env (Letrec funs e) t =
  do ensureDistinct "function name" (\(x,y,z) -> x) funs;
     uvars <- n_fresh_uvar (List.length funs);
     env' <- return (merge (listToEnv (List.map (\((f,x,e), uvar) -> (f,(0,uvar))) (List.zip funs uvars))) env);
     infer_funs menv cenv env' funs uvars;
     infer_e menv cenv env' e t
infer_es menv cenv env [] [] =
  return ()
infer_es menv cenv env (e:es) (t:ts) =
  do infer_e menv cenv env e t;
     infer_es menv cenv env es ts
infer_pes menv cenv env [] t1 t2 =
   return ()
infer_pes menv cenv env ((p,e):pes) t1 t2 =
  do env' <- infer_p cenv p t1;
     ensureDistinct "pattern variable" fst env';
     infer_e menv cenv (merge (listToEnv (List.map (\(n,t) -> (n,(0,t))) env')) env) e t2;
     infer_pes menv cenv env pes t1 t2
infer_funs menv cenv env [] [] = return ()
infer_funs menv cenv env ((f, x, e):funs) (t:ts) =
  do t1 <- fresh_uvar;
     t2 <- fresh_uvar;
     add_constraint (getPos f) (Infer_Tapp [t1,t2] TC_fn) t;
     infer_e menv cenv (bind x (0,t1) env) e t2;
     infer_funs menv cenv env funs ts

init_state :: M_st_ex ()
init_state = 
  do put init_infer_state;
     return ()

is_value :: Exp -> Bool
is_value (Lit _ _) = True
is_value (Con _ es _) = List.all is_value es
is_value (Var _) = True
is_value (Fun _ _ _) = True
is_value _ = False

check_freevars :: Integer -> [TvarN] -> T -> Bool
check_freevars dbmax tvs (Tvar tv) =
  tv `elem` tvs
check_freevars dbmax tvs (Tapp ts tn) =
  List.all (check_freevars dbmax tvs) ts
check_freevars dbmax tvs (Tvar_db n) = n < dbmax

check_ctor_tenv :: Maybe ModN -> TenvC -> [([TvarN], TypeN, [(ConN, [T])])] -> Bool
check_ctor_tenv mn tenvC tds =
  check_dup_ctors mn tenvC tds &&
  List.all
    (\(tvs,tn,ctors) ->
       isNothing (getDup tvs) &&
       List.all
         (\(cn,ts) -> (List.all (check_freevars 0 tvs) ts))
         ctors)
    tds &&
  isNothing (getDup (List.map (\(_,tn,_) -> tn) tds)) &&
  List.all
    (\(tvs,tn,ctors) ->
       envAll (\_ (_,_,tn') -> mk_id mn tn /= tn') tenvC)
    tds

build_ctor_tenv :: Maybe ModN -> [([TvarN], TypeN, [(ConN, [T])])] -> TenvC
build_ctor_tenv mn tds =
  listToEnv
    (List.concat
      (List.map
         (\(tvs,tn,ctors) ->
            List.map (\(cn,ts) -> (mk_id mn cn,(tvs,ts, mk_id mn tn))) ctors)
         tds))

infer_d :: Maybe ModN -> TenvM -> TenvC -> Tenv -> Dec -> M_st_ex (TenvC, Tenv)
infer_d mn menv cenv env (Dlet p e) = 
  do init_state;
     n <- get_next_uvar;
     t <- fresh_uvar;
     infer_e menv cenv env e t;
     env' <- infer_p cenv p t;
     ensureDistinct "pattern variable" fst env';
     ts <- apply_subst_list (List.map (\(x,y) -> y) env');
     let (num_tvs, s, ts') = generalise_list n 0 Map.empty ts;
     unless (num_tvs == 0 || is_value e) 
            (fail "Value restriction violated");
     return (emp, listToEnv (List.zip (List.map (\(x,y) -> x) env') (List.map (\t -> (num_tvs, t)) ts')))
infer_d mn menv cenv env (Dletrec funs) =
  do ensureDistinct "function name" (\(x,y,z) -> x) funs;
     init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (List.length funs);
     let env' = merge (listToEnv (List.map (\((f,x,e), uvar) -> (f,(0,uvar))) (List.zip funs uvars))) env;
     infer_funs menv cenv env' funs uvars;
     ts <- apply_subst_list uvars;
     let (num_gen,s,ts') = generalise_list next 0 Map.empty ts;
     return (emp, listToEnv (List.map (\((f,x,e), t) -> (f,(num_gen,t))) (List.zip funs ts')))
infer_d mn menv cenv env (Dtype tdecs) =
  if check_ctor_tenv mn cenv tdecs then
    return (build_ctor_tenv mn tdecs, emp)
  else
    fail "Bad type definition"

infer_ds :: Maybe ModN -> TenvM -> TenvC -> Tenv -> Decs -> M_st_ex (TenvC, Tenv)
infer_ds mn menv cenv env [] =
  return (emp,emp)
infer_ds mn menv cenv env (d:ds) =
  do (cenv',env') <- infer_d mn menv cenv env d;
     (cenv'',env'') <- infer_ds mn menv (merge cenv' cenv) (merge env' env) ds;
     return (merge cenv'' cenv', merge env'' env')

t_to_freevars :: T -> M_st_ex [TvarN]
t_to_freevars (Tvar tn) = 
  return [tn]
t_to_freevars (Tvar_db _) = 
  error "deBruijn index in type definition"
t_to_freevars (Tapp ts tc) =
  ts_to_freevars ts

ts_to_freevars :: [T] -> M_st_ex [TvarN]
ts_to_freevars [] = return []
ts_to_freevars (t:ts) =
  do fvs1 <- t_to_freevars t;
     fvs2 <- ts_to_freevars ts;
     return (fvs1++fvs2)

check_specs :: Maybe ModN -> TenvC -> Tenv -> Specs -> M_st_ex (TenvC, Tenv)
check_specs mn cenv env [] =
  return (cenv,env)
check_specs mn cenv env (Sval x t:specs) =
  do fvs <- t_to_freevars t;
     fvs' <- return (nub fvs);
     check_specs mn cenv (bind x (toInteger (List.length fvs'), 
                          infer_type_subst (listToEnv (List.zip fvs' (List.map Infer_Tvar_db [0..toInteger (List.length fvs')]))) t) env) specs
check_specs mn cenv env (Stype td : specs) =
  do unless (check_ctor_tenv mn cenv td) (fail "Bad type definition");
     check_specs mn (merge (build_ctor_tenv mn td) cenv) env specs
check_specs mn cenv env (Stype_opq tvs tn : specs) =
  do unless (envAll (\_ (x,y,tn') -> mk_id mn tn /= tn') cenv) (fail "Duplicate type definition");
     ensureDistinct "type variable" (\x -> x) tvs;
     check_specs mn cenv env specs

check_weakC :: TenvC -> TenvC -> Bool
check_weakC cenv_impl cenv_spec =
  envAll (\cn (tvs_spec, ts_spec, tn_spec) ->
            case Ast.lookup cn cenv_impl of
               Nothing -> False
               Just (tvs_impl,ts_impl,tn_impl) ->
                  (tn_spec == tn_impl) &&
                  (tvs_spec == tvs_impl) &&
                  (ts_spec == ts_impl))
         cenv_spec

check_weakE :: Tenv -> Tenv -> M_st_ex ()
check_weakE env_impl env_spec =
  mapM_ 
    (\(n, (tvs_spec, t_spec)) ->
       case Ast.lookup n env_impl of
         Nothing -> fail "Signature mismatch"
         Just (tvs_impl,t_impl) ->
             do init_state;
                uvs <- n_fresh_uvar tvs_impl;
	        let t = (infer_deBruijn_subst uvs t_impl);
                add_constraint (getPos n) t_spec t)
    (envToList env_spec)
    
check_signature :: Maybe ModN -> TenvC -> Tenv -> Maybe Specs -> M_st_ex (TenvC, Tenv)
check_signature mn cenv env Nothing = 
  return (cenv, env)
check_signature mn cenv env (Just specs) =
  do (cenv', env') <- check_specs mn emp emp specs;
     unless (check_weakC cenv cenv') (fail "Signature mismatch");
     check_weakE env env';
     return (cenv',env')

infer_top :: TenvM -> TenvC -> Tenv -> Top -> M_st_ex (TenvM, TenvC, Tenv)
infer_top menv cenv env (Tdec d) =
  do (cenv',env') <- infer_d Nothing menv cenv env d;
     return (emp, cenv', env')
infer_top menv cenv env (Tmod mn spec ds1) =
  do when (mn `envElem` menv) (fail ("Duplicate module: " ++ show mn));
     (cenv',env') <- infer_ds (Just mn) menv cenv env ds1;
     (cenv'',env'') <- check_signature (Just mn) cenv' env' spec;
     return (bind mn env'' emp, cenv'', emp)

infer_prog :: TenvM -> TenvC -> Tenv -> Prog -> M_st_ex (TenvM, TenvC, Tenv)
infer_prog menv cenv env [] = return (emp,emp,emp)
infer_prog menv cenv env (top:ds) =
  do (menv',cenv',env') <- infer_top menv cenv env top;
     (menv'', cenv'', env'') <- infer_prog menv (merge cenv' cenv) (merge env' env) ds;
     return (merge menv'' menv', merge cenv'' cenv', merge env'' env')

infer_Tfn t1 t2 = Infer_Tapp [t1,t2] TC_fn
infer_Tint = Infer_Tapp [] TC_int
infer_Tbool = Infer_Tapp [] TC_bool
infer_Tunit = Infer_Tapp [] TC_unit
infer_Tref t = Infer_Tapp [t] TC_ref

dummy_pos = initialPos "initial_env"

init_type_env =
  listToEnv
    (List.map (\(x,y) -> (VarN x Typecheck.dummy_pos,y))
      [("+", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tint))),
       ("-", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tint))),
       ("*", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tint))),
       ("div", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tint))),
       ("mod", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tint))),
       ("<", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tbool))),
       (">", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tbool))),
       ("<=", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tbool))),
       (">=", (0, infer_Tfn infer_Tint (infer_Tfn infer_Tint infer_Tbool))),
       ("=", (1, infer_Tfn (Infer_Tvar_db 0) (infer_Tfn (Infer_Tvar_db 0) infer_Tbool))),
       (":=", (1, infer_Tfn (infer_Tref (Infer_Tvar_db 0)) (infer_Tfn (Infer_Tvar_db 0) infer_Tunit))),
       ("~", (0, infer_Tfn infer_Tint infer_Tint)),
       ("!", (1, infer_Tfn (infer_Tref (Infer_Tvar_db 0)) (Infer_Tvar_db 0))),
       ("ref", (1, infer_Tfn (Infer_Tvar_db 0) (infer_Tref (Infer_Tvar_db 0))))])

inferTop :: (TenvM,TenvC,Tenv) -> Top -> Either (SourcePos,String) (TenvM, TenvC, Tenv)
inferTop (menv,cenv,env) top =
  evalStateT (infer_top menv cenv env top) init_infer_state
