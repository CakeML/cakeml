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
import Data.Set as Set
import Ast
import Unify
import Text.Parsec.Pos (initialPos, SourcePos)
import Data.Maybe
import Parse

getDup :: (Eq a, Ord a) => [a] -> Maybe a
getDup ls = check (sort ls)
  where check [] = Nothing
        check [x] = Nothing
        check (x:y:zs) = if x == y then Just x else check (y:zs)

envAll :: (k -> v -> Bool) -> Map k v -> Bool
envAll f m = List.all (\(x,y) -> f x y) (Map.assocs m)

data Infer_st = Infer_st { next_uvar :: Uvar, subst :: Subst }
type M_st_ex = State.StateT Infer_st (Either (SourcePos, String))

typeError :: SourcePos -> String -> M_st_ex a
typeError pos str = lift (Left (pos,str))

lookup_st_ex :: (HasPos k, Show k, Ord k) => k -> Map.Map k v -> M_st_ex v
lookup_st_ex k env =
  case Map.lookup k env of
    Nothing -> typeError (getPos k) ("unbound identifier: " ++ (show k))
    Just v -> return v 

data Tid_or_exn =
    TypeId (Id TypeN)
  | TypeExn (Id ConN)

instance Show Tid_or_exn where
  show (TypeId tid) = show tid
  show (TypeExn cid) = show cid

type Tenv = Map VarN (Integer, Infer_t)
type TenvM = Map ModN (Map VarN (Integer, Infer_t))
type TenvC = Map (Id ConN) ([TvarN], [T], Tid_or_exn)
type TenvT = Map (Id TypeN) ([TvarN], T)

type Decls = (Set ModN, Set (Id TypeN), Set (Id ConN))
empty_decls = (Set.empty,Set.empty,Set.empty)

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

infer_type_subst :: Map TvarN Infer_t -> T -> Infer_t
infer_type_subst s (Tvar tv) =
  case Map.lookup tv s of 
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

tid_exn_to_tc :: Tid_or_exn -> Tc
tid_exn_to_tc (TypeId tid) = TC_name tid
tid_exn_to_tc (TypeExn _) = TC_exn

infer_p :: TenvC -> Pat -> Infer_t -> M_st_ex [(VarN,Infer_t)]
infer_p cenv (Pvar n) t =
  return [(n,t)]
infer_p cenv (Plit (IntLit i) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_int) t;
     return []
infer_p cenv (Plit (Char s) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_char) t;
     return []
infer_p cenv (Plit (StrLit s) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_string) t;
     return []
infer_p cenv (Plit (Word8 w) pos) t =
  do add_constraint pos (Infer_Tapp [] TC_word8) t;
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
           add_constraint pos (Infer_Tapp ts' (tid_exn_to_tc tn)) t;
           infer_ps cenv ps (List.map (infer_type_subst (Map.fromList (List.zip tvs' ts'))) ts)
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

bool_type = (Infer_Tapp [] (TC_name (Short (TypeN "bool" dummy_pos))))

constrain_op :: Op -> Infer_t -> M_st_ex [Infer_t]
constrain_op op t =
  case op of
    Opn opn pos ->
      do add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [] TC_int, Infer_Tapp [] TC_int]
    Opb opb pos -> 
      do add_constraint pos bool_type t;
         return [Infer_Tapp [] TC_int, Infer_Tapp [] TC_int]
    Equality pos ->
      do add_constraint pos bool_type t;
         t1 <- fresh_uvar;
         return [t1, t1]
    Opapp ->
      do uvar <- fresh_uvar;
         return [Infer_Tapp [uvar,t] TC_fn, uvar]
    Opassign pos ->
      do add_constraint pos (Infer_Tapp [] TC_tup) t;
         t2 <- fresh_uvar;
         return [Infer_Tapp [t2] TC_ref, t2]
    Opref pos ->
      do uvar <- fresh_uvar;
         add_constraint pos (Infer_Tapp [uvar] TC_ref) t;
         return [uvar]
    Opderef pos -> return [Infer_Tapp [t] TC_ref]
    Aw8alloc pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_word8array) t;
         return [Infer_Tapp [] TC_int, Infer_Tapp [] TC_word8]
    Aw8sub pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_word8) t;
         return [Infer_Tapp [] TC_word8array, Infer_Tapp [] TC_int]
    Aw8length pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [] TC_word8array]
    Aw8update pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_tup) t
         return [Infer_Tapp [] TC_word8array, Infer_Tapp [] TC_int, Infer_Tapp [] TC_word8]
    Chr pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_char) t;
         return [Infer_Tapp [] TC_int]
    Ord pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [] TC_char]
    Chopb opb pos -> 
      do add_constraint pos bool_type t;
         return [Infer_Tapp [] TC_char, Infer_Tapp [] TC_char]
    Explode pos ->
      do () <- add_constraint pos (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short (TypeN "list" dummy_pos)))) t;
         return [Infer_Tapp [] TC_string]
    Implode pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_string) t;
         return [Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short (TypeN "list" dummy_pos)))]
    Strlen pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [] TC_string]
    VfromList pos ->
      do uvar <- fresh_uvar;
         () <- add_constraint pos (Infer_Tapp [uvar] TC_vector) t;
         return [Infer_Tapp [uvar] (TC_name (Short (TypeN "list" dummy_pos)))]
    Vsub pos ->
      return [Infer_Tapp [t] TC_vector, Infer_Tapp [] TC_int]
    Vlength pos ->
      do uvar <- fresh_uvar;
         () <- add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [uvar] TC_vector]
    Aalloc pos ->
      do uvar <- fresh_uvar;
         () <- add_constraint pos (Infer_Tapp [uvar] TC_array) t;
         return [Infer_Tapp [] TC_int, uvar]
    Asub pos ->
      return [Infer_Tapp [t] TC_vector, Infer_Tapp [] TC_int]
    Alength pos ->
      do uvar <- fresh_uvar;
         () <- add_constraint pos (Infer_Tapp [] TC_int) t;
         return [Infer_Tapp [uvar] TC_array]
    Aupdate pos ->
      do uvar <- fresh_uvar;
         () <- add_constraint pos (Infer_Tapp [] TC_tup) t
         return [Infer_Tapp [uvar] TC_array, Infer_Tapp [] TC_int, uvar]
    FFI n pos ->
      do () <- add_constraint pos (Infer_Tapp [] TC_tup) t;
         return [Infer_Tapp [] TC_word8array]

ensureDistinct msg select l =
  case getDup (List.map select l) of
    Nothing -> return ()
    Just x -> typeError (getPos x) ("duplicate " ++ msg ++ ": " ++ show x)

infer_Texn = Infer_Tapp [] TC_exn

infer_e :: TenvM -> TenvC -> Tenv -> Exp -> Infer_t -> M_st_ex ()
infer_e menv cenv env (Raise e) t =
  do infer_e menv cenv env e infer_Texn;
     return ()
infer_e menv cenv env (Handle e1 []) t =
  error "Impossible empty handler"
infer_e menv cenv env (Handle e1 pes) t =
  do infer_e menv cenv env e1 t;
     infer_pes menv cenv env pes infer_Texn t
infer_e menv cenv tenv (Lit (IntLit i) pos) t =
  add_constraint pos (Infer_Tapp [] TC_int) t
infer_e menv cenv tenv (Lit (Char c) pos) t =
  add_constraint pos (Infer_Tapp [] TC_char) t
infer_e menv cenv tenv (Lit (StrLit s) pos) t =
  add_constraint pos (Infer_Tapp [] TC_string) t
infer_e menv cenv tenv (Lit (Word8 w) pos) t =
  add_constraint pos (Infer_Tapp [] TC_word8) t
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
          add_constraint pos (Infer_Tapp ts' (tid_exn_to_tc tn)) t;
          infer_es menv cenv env es (List.map (infer_type_subst (Map.fromList (List.zip tvs' ts'))) ts)
infer_e menv cenv env (Fun x e pos) t =
  do t1 <- fresh_uvar;
     t2 <- fresh_uvar;
     add_constraint pos (Infer_Tapp [t1,t2] TC_fn) t
     infer_e menv cenv (Map.insert x (0,t1) env) e t2;
infer_e menv cenv env (App op es) t =
  do ts <- constrain_op op t;
     infer_es menv cenv env es ts
infer_e menv cenv env (Log log e1 e2) t =
  do add_constraint (getPos log) bool_type t;
     infer_e menv cenv env e1 bool_type;
     infer_e menv cenv env e2 bool_type
infer_e menv cenv env (If e1 e2 e3) t =
  do infer_e menv cenv env e1 bool_type;
     infer_e menv cenv env e2 t;
     infer_e menv cenv env e3 t
infer_e menv cenv env (Mat e pes) t =
  if List.null pes then
    error "Empty pattern match"
  else
    do t' <- fresh_uvar;
       infer_e menv cenv env e t';
       infer_pes menv cenv env pes t' t
infer_e menv cenv env (Let (Just x) e1 e2) t =
  do t1 <- fresh_uvar;
     infer_e menv cenv env e1 t1;
     infer_e menv cenv (Map.insert x (0,t1) env) e2 t
infer_e menv cenv env (Let Nothing e1 e2) t =
  do t1 <- fresh_uvar;
     infer_e menv cenv env e1 t1;
     infer_e menv cenv env e2 t
infer_e menv cenv env (Letrec funs e) t =
  do ensureDistinct "function name" (\(x,y,z) -> x) funs;
     uvars <- n_fresh_uvar (List.length funs);
     env' <- return (Map.union (Map.fromList (List.map (\((f,x,e), uvar) -> (f,(0,uvar))) (List.zip funs uvars))) env);
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
     infer_e menv cenv (Map.union (Map.fromList (List.map (\(n,t) -> (n,(0,t))) env')) env) e t2;
     infer_pes menv cenv env pes t1 t2
infer_funs menv cenv env [] [] = return ()
infer_funs menv cenv env ((f, x, e):funs) (t:ts) =
  do t1 <- fresh_uvar;
     t2 <- fresh_uvar;
     add_constraint (getPos f) (Infer_Tapp [t1,t2] TC_fn) t;
     infer_e menv cenv (Map.insert x (0,t1) env) e t2;
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

check_freevars :: Integer -> [TvarN] -> T -> M_st_ex ()
check_freevars dbmax tvs (Tvar tv) =
  unless (tv `elem` tvs) (typeError (getPos tv) ("free type variable: " ++ show tv))
check_freevars dbmax tvs (Tapp ts tn) =
  mapM_ (check_freevars dbmax tvs) ts
check_freevars dbmax tvs (Tvar_db n) = 
  unless (n < dbmax) (error "deBruijn type variable in input")

check_dup_ctors :: Maybe ModN -> [([TvarN], TypeN, [(ConN, [T])])] -> M_st_ex ()
check_dup_ctors mn_opt tds =
  ensureDistinct "constructor" (\x -> x) (List.foldr (\(tvs, tn, condefs) x2 -> List.foldr (\(n, ts) x2 -> n : x2) x2 condefs) [] tds)

check_type_names :: TenvT -> T -> M_st_ex ()
check_type_names tenvT (Tvar tv) =
  return ()
check_type_names tenvT (Tapp ts (TC_name tn)) =
  do (tvs,t) <- lookup_st_ex tn tenvT; 
     unless (List.length tvs == List.length ts) (typeError (getPos tn) ("type constructor " ++ show tn ++ " expected " ++ show (List.length tvs) ++ " arguments, given " ++ show (List.length ts)));
     mapM_ (check_type_names tenvT) ts
check_type_names tenvT (Tapp ts _) =
  return ()
check_type_names tenvT (Tvar_db n) =
  return ()

type_subst :: Map TvarN T -> T -> T
type_subst s (Tvar tv) =
  case Map.lookup tv s of
    Nothing -> Tvar tv
    Just t -> t
type_subst s (Tapp ts tn) =
  Tapp (List.map (type_subst s) ts) tn
type_subst s (Tvar_db n) = Tvar_db n

type_name_subst :: TenvT -> T -> T
type_name_subst tenvT (Tvar tv) = 
  Tvar tv
type_name_subst tenvT (Tapp ts tc) =
  let args = List.map (type_name_subst tenvT) ts in
    case tc of
      TC_name tn ->
          case Map.lookup tn tenvT of
            Just (tvs, t) -> type_subst (Map.fromList (List.zip tvs args)) t
            Nothing -> Tapp args tc
      _ -> Tapp args tc
type_name_subst tenvT (Tvar_db n) = Tvar_db n


check_ctor_tenv :: Maybe ModN -> TenvT -> [([TvarN], TypeN, [(ConN, [T])])] -> M_st_ex ()
check_ctor_tenv mn tenvT tds =
  do check_dup_ctors mn tds;
     mapM_ (\(tvs,tn,ctors) ->
	      do ensureDistinct "type variable" (\x->x) tvs;
	         mapM_ (\(cn,ts) -> mapM_ (check_freevars 0 tvs) ts >> mapM_ (check_type_names tenvT) ts) ctors)
	   tds;
     ensureDistinct "type name" (\(_,tn,_) -> tn) tds;

build_ctor_tenv :: Maybe ModN -> TenvT -> [([TvarN], TypeN, [(ConN, [T])])] -> TenvC
build_ctor_tenv mn tenvT tds =
  Map.fromList
    (List.concat
      (List.map
         (\(tvs,tn,ctors) ->
            List.map (\(cn,ts) -> (Short cn,(tvs,List.map (type_name_subst tenvT) ts, TypeId (mk_id mn tn)))) ctors)
         tds))

infer_d :: Maybe ModN -> Decls -> TenvT -> TenvM -> TenvC -> Tenv -> Dec -> M_st_ex (Decls,TenvT,TenvC,Tenv)
infer_d mn decls tenvT menv cenv env (Dlet p e pos) = 
  do init_state;
     n <- get_next_uvar;
     t <- fresh_uvar;
     infer_e menv cenv env e t;
     env' <- infer_p cenv p t;
     ensureDistinct "pattern variable" fst env';
     ts <- apply_subst_list (List.map (\(x,y) -> y) env');
     let (num_tvs, s, ts') = generalise_list n 0 Map.empty ts;
     unless (num_tvs == 0 || is_value e) 
            (typeError pos "Value restriction violated");
     return (empty_decls,Map.empty, Map.empty, Map.fromList (List.zip (List.map (\(x,y) -> x) env') (List.map (\t -> (num_tvs, t)) ts')))
infer_d mn decls tenvT menv cenv env (Dletrec funs) =
  do ensureDistinct "function name" (\(x,y,z) -> x) funs;
     init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (List.length funs);
     let env' = Map.union (Map.fromList (List.map (\((f,x,e), uvar) -> (f,(0,uvar))) (List.zip funs uvars))) env;
     infer_funs menv cenv env' funs uvars;
     ts <- apply_subst_list uvars;
     let (num_gen,s,ts') = generalise_list next 0 Map.empty ts;
     return (empty_decls,Map.empty, Map.empty, Map.fromList (List.map (\((f,x,e), t) -> (f,(num_gen,t))) (List.zip funs ts')))
infer_d mn (mdecls,tdecls,edecls) tenvT menv cenv env (Dtype tdecs) =
  do new_tenvT <- return (Map.fromList (List.map (\(tvs,tn,ctors) -> (Short tn, (tvs, Tapp (List.map Tvar tvs) (TC_name (mk_id mn tn))))) tdecs));
     tenvT' <- return (Map.union new_tenvT tenvT);
     check_ctor_tenv mn tenvT' tdecs; 
     new_tdecls <- return (List.map (\(tvs,tn,ctors) -> mk_id mn tn) tdecs);
     mapM_ (\new_id -> if Set.member new_id tdecls then typeError (getPos new_id) ("Dulicate type definition of: " ++ show new_id) else return ()) new_tdecls;
     return ((Set.empty,Set.fromList new_tdecls,Set.empty), new_tenvT, build_ctor_tenv mn tenvT' tdecs, Map.empty)
infer_d mn (mdecls,tdecls,edecls) tenvT menv cenv env (Dtabbrev tvs tn t) =
  do ensureDistinct "type variable" (\x->x) tvs;
     check_freevars 0 tvs t;
     check_type_names tenvT t;
     return (empty_decls, Map.insert (Short tn) (tvs,type_name_subst tenvT t) Map.empty, Map.empty, Map.empty)
infer_d mn (mdecls,tdecls,edecls) tenvT menv cenv env (Dexn cn ts) =
  do mapM_ (check_freevars 0 []) ts;
     mapM_ (check_type_names tenvT) ts;
     when (Set.member (mk_id mn cn) edecls) (typeError (getPos cn) ("Duplicate exception definition of" ++ show cn));
     return ((Set.empty,Set.empty,Set.singleton (mk_id mn cn)),
              Map.empty, 
              Map.insert (Short cn) ([], List.map (\x -> type_name_subst tenvT x) ts, TypeExn (mk_id mn cn)) Map.empty,
	      Map.empty)


append_decls (m1,t1,e1) (m2,t2,e2) = (Set.union m1 m2, Set.union t1 t2, Set.union e1 e2)

infer_ds :: Maybe ModN -> Decls -> TenvT -> TenvM -> TenvC -> Tenv -> Decs -> M_st_ex (Decls,TenvT,TenvC,Tenv)
infer_ds mn decls tenvT menv cenv env [] =
  return (empty_decls,Map.empty, Map.empty, Map.empty)
infer_ds mn decls tenvT menv cenv env (d:ds) =
  do (decls',tenvT',cenv',env') <- infer_d mn decls tenvT menv cenv env d;
     (decls'',tenvT'',cenv'',env'') <- infer_ds mn (append_decls decls' decls) (Map.union tenvT' tenvT) menv (Map.union cenv' cenv) (Map.union env' env) ds;
     return (append_decls decls'' decls', Map.union tenvT'' tenvT', Map.union cenv'' cenv', Map.union env'' env')

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

{- TODO
check_specs :: Maybe ModN -> TenvC -> Tenv -> Specs -> M_st_ex (TenvC, Tenv)
check_specs mn cenv env [] =
  return (cenv,env)
check_specs mn cenv env (Sval x t:specs) =
  do fvs <- t_to_freevars t;
     fvs' <- return (nub fvs);
     check_specs mn cenv (Map.insert x (toInteger (List.length fvs'), 
                          infer_type_subst (Map.fromList (List.zip fvs' (List.map Infer_Tvar_db [0..toInteger (List.length fvs')]))) t) env) specs
check_specs mn cenv env (Stype td : specs) =
  do check_ctor_tenv mn cenv td;
     check_specs mn (Map.union (build_ctor_tenv mn td) cenv) env specs
check_specs mn cenv env (Sexn cn ts : specs) =
  if isJust (Map.lookup (mk_id mn cn) cenv) then
    typeError (getPos cn) ("duplicate constructor: " ++ show (mk_id mn cn))
  else 
    do mapM_ (check_freevars 0 []) ts;
       check_specs mn (Map.insert (mk_id mn cn) ([], ts, TypeExn) cenv) env specs
check_specs mn cenv env (Stype_opq tvs tn : specs) =
  do mapM_ (\(_, (x,y,tn')) -> 
              unless (TypeId (mk_id mn tn) /= tn') 
                     (typeError (getPos tn) ("duplicate type definition: " ++ show (mk_id mn tn)))) 
          (Map.assocs cenv);
     ensureDistinct "type variable" (\x -> x) tvs;
     check_specs mn cenv env specs

check_weakC :: TenvC -> TenvC -> M_st_ex ()
check_weakC cenv_impl cenv_spec =
  mapM_ (\(cn, (tvs_spec, ts_spec, tn_spec)) ->
            case Map.lookup cn cenv_impl of
               Nothing -> typeError (getPos cn) ("Missing implementation of " ++ show cn)
               Just (tvs_impl,ts_impl,tn_impl) ->
                  unless (tn_spec == tn_impl && tvs_spec == tvs_impl && ts_spec == ts_impl) 
                         (typeError (getPos cn) "datatype specification and implementation differ"))
        (Map.assocs cenv_spec)

check_weakE :: Tenv -> Tenv -> M_st_ex ()
check_weakE env_impl env_spec =
  mapM_ 
    (\(n, (tvs_spec, t_spec)) ->
       case Map.lookup n env_impl of
         Nothing -> typeError (getPos n) ("Missing implementation of " ++ show n)
         Just (tvs_impl,t_impl) ->
             do init_state;
                uvs <- n_fresh_uvar tvs_impl;
	        let t = (infer_deBruijn_subst uvs t_impl);
                add_constraint (getPos n) t t_spec)
    (Map.assocs env_spec)
-}

check_signature :: Maybe ModN -> TenvT -> Decls -> Decls -> TenvT -> TenvC -> Tenv -> Maybe Specs -> M_st_ex (Decls, TenvT, TenvC, Tenv)
check_signature mn tenvT init_decls decls tenvT' cenv env Nothing = 
  return (decls, tenvT', cenv, env)
check_signature mn tenvT init_decls decls tenvT' cenv env (Just specs) =
  error "Signatures not yet supported in unverified front end"
{-
  do (cenv', env') <- check_specs mn Map.empty Map.empty specs;
     check_weakC cenv cenv';
     check_weakE env env';
     return (cenv',env')
-}

data TypeState = TypeState Decls TenvT TenvM TenvC Tenv

showMap :: (Show k, Show v) => Map k v -> String
showMap m =
  show l
  where l = Map.toList m

instance Show TypeState where
  show (TypeState decls tenvT tenvM tenvC tenv) =
    showMap tenvT ++ showMap tenvM ++ showMap tenvC ++ showMap tenv

merge_types :: TypeState -> TypeState -> TypeState
merge_types (TypeState decls' tenvT' menv' cenv' env') (TypeState decls tenvT menv cenv env) =
  TypeState (append_decls decls' decls) (Map.union tenvT' tenvT) (Map.union menv' menv)
            (Map.union cenv' cenv) (Map.union env' env)

infer_top :: Decls -> TenvT -> TenvM -> TenvC -> Tenv -> Top -> M_st_ex TypeState
infer_top decls tenvT menv cenv env (Tdec d) =
  do (decls',tenvT',cenv',env') <- infer_d Nothing decls tenvT menv cenv env d;
     return (TypeState decls' tenvT' Map.empty cenv' env')
infer_top (mdecls,tdecls,edecls) tenvT menv cenv env (Tmod mn spec ds1) =
  do when (mn `Map.member` menv) (typeError (getPos mn) ("Duplicate module: " ++ show mn));
     (decls',tenvT',cenv',env') <- infer_ds (Just mn) (mdecls,tdecls,edecls) tenvT menv cenv env ds1;
     ((mdecls'',tdecls'',edecls''),tenvT'',cenv'',env'') <-
          check_signature (Just mn) tenvT (mdecls,tdecls,edecls) decls' tenvT' cenv' env' spec;
     return (TypeState (Set.insert mn mdecls'',tdecls'',edecls'')
                       (addMod mn tenvT'')
		       (Map.singleton mn env'')
		       (addMod mn cenv'')
		       Map.empty)
        where addMod m env =
                Map.fromList (List.map (\(k, v) -> (fixKey k, v)) (Map.assocs env))
              fixKey (Short k) = Long mn k
              fixKey (Long mn k) = error "internal error"


infer_prog :: Decls -> TenvT -> TenvM -> TenvC -> Tenv -> Prog -> M_st_ex TypeState
infer_prog decls tenvT menv cenv env [] = 
  return (TypeState empty_decls Map.empty Map.empty Map.empty Map.empty)
infer_prog decls tenvT menv cenv env (top:ds) =
  do (TypeState decls' tenvT' menv' cenv' env') <- infer_top decls tenvT menv cenv env top;
     (TypeState decls'' tenvT'' menv''  cenv''  env'') <- 
         infer_prog (append_decls decls' decls) (Map.union tenvT' tenvT) (Map.union menv' menv) (Map.union cenv' cenv) (Map.union env' env) ds;
     return (TypeState (append_decls decls'' decls') (Map.union tenvT'' tenvT')
                       (Map.union menv'' menv') (Map.union cenv'' cenv') (Map.union env'' env'))


inferTop :: TypeState -> Top -> Either (SourcePos,String) TypeState
inferTop (TypeState decls tenvT menv cenv env) top =
  evalStateT (infer_top decls tenvT menv cenv env top) init_infer_state

inferProg :: TypeState -> Prog -> Either (SourcePos,String) TypeState
inferProg (TypeState decls tenvT menv cenv env) top =
  evalStateT (infer_prog decls tenvT menv cenv env top) init_infer_state
