module Interp where
import Control.Monad.State.Lazy
import Data.Maybe
import Data.List as List
import Ast

data V =
    Litv Lit
  | Conv (Maybe (Id ConN)) [V]
  | Closure (Env VarN V) VarN Exp
  | Recclosure (Env VarN V) [(VarN, VarN, Exp)] VarN
  | Loc Int

data Error_result =
    Rtype_error
  | Rraise Error

data Result a =
    Rval a
  | Rerr Error_result

type Store = [V]

empty_store :: Store
empty_store = []

store_lookup :: Int -> Store -> Maybe V
store_lookup l st =
  if l < List.length st then
    Just (st !! l)
  else
    Nothing

store_alloc :: V -> Store -> (Store, Int)
store_alloc v st =
  (st ++ [v], List.length st)

store_assign :: Int -> V -> Store -> Maybe Store
store_assign n v st =
  if n < List.length st then
    let l = List.drop n st in 
    Just (List.take n st ++ v : List.tail l)
  else
    Nothing

type EnvC = Env (Id ConN) (Integer, Id TypeN)

type EnvE = Env VarN V

type EnvM = Env ModN EnvE

instance Monad Result where
  return v = Rval v
  (>>=) v f =
    case v of
      Rval v -> f v
      Rerr e -> Rerr e

newtype ResultT m a = ResultT (m (Result a))

instance MonadTrans ResultT where
  lift r = return r

type M_st_ex = ResultT (State Store)

raise :: Error_result -> M_st_ex a
raise err = lift (Rerr err)

lit_same_type :: Lit -> Lit -> Bool
lit_same_type l1 l2 =
  case (l1,l2) of
      (IntLit _, IntLit _) -> True
      (Bool _, Bool _) -> True
      (Unit, Unit) -> True
      _ -> False

data Match_result =
    No_match
  | Match_type_error
  | Match EnvE

pmatch :: EnvC -> Store -> Pat -> V -> EnvE -> Match_result
pmatch envC s (Pvar x) v' env = Match (bind x v' env)
pmatch envC s (Plit l _) (Litv l') env =
  if l == l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error
pmatch envC s (Pcon (Just n) ps _) (Conv (Just n') vs) env =
  case (Ast.lookup n envC, Ast.lookup n' envC) of
      (Just (l, t), Just (l', t')) ->
        if t == t' && (toInteger (List.length ps) == l) && (toInteger (List.length vs) == l') then
          if n == n' then
            pmatch_list envC s ps vs env
          else
            No_match
        else
          Match_type_error
      (_, _) -> Match_type_error
pmatch envC s (Pcon Nothing ps _) (Conv Nothing vs) env =
  if List.length ps == List.length vs then
    pmatch_list envC s ps vs env
  else
    Match_type_error
pmatch envC s (Pref p _) (Loc lnum) env =
  case store_lookup lnum s of
      Just v -> pmatch envC s p v env
      Nothing -> Match_type_error
pmatch envC _ _ _ env = Match_type_error
pmatch_list envC s [] [] env = Match env
pmatch_list envC s (p:ps) (v:vs) env =
  case pmatch envC s p v env of
      No_match -> No_match
      Match_type_error -> Match_type_error
      Match env' -> pmatch_list envC s ps vs env'
pmatch_list envC s _ _ env = Match_type_error

do_con_check :: EnvC -> Maybe (Id ConN) -> Integer -> M_st_ex ()
do_con_check cenv n_opt l =
  case n_opt of
      Nothing -> return ()
      Just n ->
        case Ast.lookup n cenv of
            Nothing -> raise Rtype_error
            Just (l',ns) -> 
              if l == l' then
                return ()
	      else
                raise Rtype_error

lookup_var_id :: Id VarN -> EnvM -> EnvE -> Maybe V
lookup_var_id id menv envE =
  case id of
      Short x -> Ast.lookup x envE
      Long x y ->
        case Ast.lookup x menv of
            Nothing -> Nothing
            Just env -> Ast.lookup y env

do_uapp :: Store -> Uop -> V -> Maybe (Store, V)
do_uapp s uop v =
  case uop of
      Opderef ->
        case v of
            Loc n ->
              case store_lookup n s of
                  Just v -> Just (s,v)
                  Nothing -> Nothing
            _ -> Nothing
      Opref _ ->
        let (s',n) = store_alloc v s in
          Just (s', Loc n)

data Eq_result = 
    Eq_val Bool
  | Eq_closure
  | Eq_type_error

do_eq :: V -> V -> Eq_result
do_eq (Litv l1) (Litv l2) = Eq_val (l1 == l2)
do_eq (Loc l1) (Loc l2) = Eq_val (l1 == l2)
do_eq (Conv cn1 vs1) (Conv cn2 vs2) =
  if cn1 == cn2 && List.length vs1 == List.length vs2 then
    do_eq_list vs1 vs2
  else
    Eq_val False
do_eq (Closure _ _ _) (Closure _ _ _) = Eq_closure
do_eq (Closure _ _ _) (Recclosure _ _ _) = Eq_closure
do_eq (Recclosure _ _ _) (Closure _ _ _) = Eq_closure
do_eq (Recclosure _ _ _) (Recclosure _ _ _) = Eq_closure
do_eq _ _ = Eq_type_error
do_eq_list [] [] = Eq_val True
do_eq_list (v1:vs1) (v2:vs2) = 
  case do_eq v1 v2 of
      Eq_closure -> Eq_closure
      Eq_type_error -> Eq_type_error
      Eq_val r -> 
        if not r then
          Eq_val False
        else
          do_eq_list vs1 vs2
do_eq_list _ _ = Eq_val False

find_recfun :: VarN -> [(VarN, VarN, Exp)] -> Maybe (VarN, Exp)
find_recfun n funs =
  case funs of
      [] -> Nothing
      (f,x,e) : funs ->
        if f == n then
          Just (x,e)
        else
          find_recfun n funs

build_rec_env :: [(VarN, VarN, Exp)] -> EnvE -> EnvE -> EnvE
build_rec_env funs cl_env add_to_env =
  List.foldr
    (\(f,x,e) env' -> bind f (Recclosure cl_env funs f) env')
    add_to_env
    funs

do_app :: Store -> EnvE -> Op -> V -> V -> Maybe (Store, EnvE, Exp)
do_app s env' op v1 v2 =
  case (op, v1, v2) of
      (Opapp, Closure env n e, v) ->
        Just (s, bind n v env, e)
      (Opapp, Recclosure env funs n, v) ->
        case find_recfun n funs of
            Just (n,e) -> Just (s, bind n v (build_rec_env funs env env), e)
            Nothing -> Nothing
      (Opn op pos, Litv (IntLit n1), Litv (IntLit n2)) ->
        if (op == Divide || op == Modulo) && n2 == 0 then
          Just (s, env', Raise Div_error)
        else
          Just (s, env',Lit (IntLit (opn_lookup op n1 n2)) pos)
      (Opb op pos, Litv (IntLit n1), Litv (IntLit n2)) ->
        Just (s, env', Lit (Bool (opb_lookup op n1 n2)) pos)
      (Equality pos, v1, v2) ->
        case do_eq v1 v2 of
            Eq_type_error -> Nothing
            Eq_closure -> Just (s, env', Raise Eq_error)
            Eq_val b -> Just (s, env', Lit (Bool b) pos)
      (Opassign pos, (Loc lnum), v) ->
        case store_assign lnum v s of
          Just st -> Just (st, env', Lit Unit pos)
          Nothing -> Nothing
      _ -> Nothing

do_log :: Lop -> V -> Exp -> Maybe Exp
do_log l v e =
  case (l, v) of
      (And pos, Litv (Bool True)) -> Just e
      (Or pos, Litv (Bool False)) -> Just e
      (lop, Litv (Bool b)) -> Just (Lit (Bool b) (getPos lop))
      _ -> Nothing

do_if :: V -> Exp -> Exp -> Maybe Exp
do_if v e1 e2 =
  case v of
      Litv (Bool True) -> Just e1
      Litv (Bool False) -> Just e2
      _ -> Nothing

do_handle :: EnvM -> EnvC -> EnvE -> VarN -> Exp -> Result V -> M_st_ex V
do_handle menv cenv env var e res =
  case res of
    Rerr (Rraise (Int_error i)) -> run_eval menv cenv (bind var (Litv (IntLit i)) env) e
    _ -> lift res

run_eval :: EnvM -> EnvC -> EnvE -> Exp -> M_st_ex V
run_eval menv cenv env (Lit l pos) = 
  return (Litv l)
run_eval menv cenv env (Raise err) =
  raise (Rraise err)
run_eval menv cenv env (Handle e1 var e2) =
  run_eval menv cenv env e1 >>= do_handle menv cenv env var e2
run_eval menv cenv env (Con cn es pos) =
  do do_con_check cenv cn (toInteger (List.length es));
     vs <- run_eval_list menv cenv env es;
     return (Conv cn vs)
run_eval menv cenv env (Var n) =
  case lookup_var_id n menv env of
     Nothing -> raise Rtype_error
     Just v -> return v
run_eval menv cenv env (Fun n e pos) =
   return (Closure env n e)
run_eval menv cenv env (Uapp uop e) =
  do v <- run_eval menv cenv env e;
     st <- get;
     case do_uapp st uop v of
          Nothing -> raise Rtype_error
          Just (st',v) -> 
            do put st';
               return v 
run_eval menv cenv env (App op e1 e2) =
   do v1 <- run_eval menv cenv env e1;
      v2 <- run_eval menv cenv env e2;
      st <- get;
      case do_app st env op v1 v2 of
           Nothing -> raise Rtype_error
           Just (st', env', e3) ->
             do put st';
                run_eval menv cenv env' e3
run_eval menv cenv env (Log lop e1 e2) =
   do v1 <- run_eval menv cenv env e1;
      case do_log lop v1 e2 of
           Nothing -> raise Rtype_error
           Just e' -> run_eval menv cenv env e'
run_eval menv cenv env (If e1 e2 e3) =
   do v1 <- run_eval menv cenv env e1;
      case do_if v1 e2 e3 of
           Nothing -> raise Rtype_error
           Just e' -> run_eval menv cenv env e'
run_eval menv cenv env (Mat e pes) =
   do v <- run_eval menv cenv env e;
      run_eval_match menv cenv env v pes
run_eval menv cenv env (Let x e1 e2) =
   do v1 <- run_eval menv cenv env e1;
      run_eval menv cenv (bind x v1 env) e2
run_eval menv cenv env (Letrec funs e) =
   if isNothing (getDup (List.map (\(x,y,z) -> x) funs)) then
     run_eval menv cenv (build_rec_env funs env env) e
   else
     raise Rtype_error
run_eval_list menv cenv env [] =
   return []
run_eval_list menv cenv env (e:es) =
   do v <- run_eval menv cenv env e;
      vs <- run_eval_list menv cenv env es;
      return (v:vs)
run_eval_match menv cenv env v [] =
   raise (Rraise Bind_error)
run_eval_match menv cenv env v ((p,e):pes) =
   do st <- get;
      if isNothing (getDup (pat_bindings p [])) then
        case pmatch cenv st p v env of
             Match_type_error -> raise Rtype_error
             No_match -> run_eval_match menv cenv env v pes
             Match env' -> run_eval menv cenv env' e
      else
        raise Rtype_error
     
{-
val run_eval_dec_def = Define `
(run_eval_dec mn menv cenv st env (Dlet p e) =
  if ALL_DISTINCT (pat_bindings p []) then
    case run_eval menv cenv env e st of
       | (st', Rval v) =>
           (case pmatch cenv (SND st') p v emp of
              | Match env' => (st', Rval (emp, env'))
              | No_match => (st', Rerr (Rraise Bind_error))
              | Match_type_error => (st', Rerr Rtype_error))
       | (st', Rerr e) => (st', Rerr e)
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn menv cenv st env (Dletrec funs) =
  if ALL_DISTINCT (MAP FST funs) then
    (st, Rval (emp, build_rec_env funs env emp))
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn menv cenv st env (Dtype tds) =
  if check_dup_ctors mn cenv tds then
    (st, Rval (build_tdefs mn tds, emp))
  else
    (st, Rerr Rtype_error))`;

val run_eval_decs_def = Define `
(run_eval_decs mn menv cenv st env [] = (st, emp, Rval emp)) ∧
(run_eval_decs mn menv cenv st env (d::ds) =
  case run_eval_dec mn menv cenv st env d of
      (st', Rval (cenv',env')) =>
         (case run_eval_decs mn menv (merge cenv' cenv) st' (merge env' env) ds of
               (st'', cenv'', r) =>
                 (st'', merge cenv'' cenv', combine_dec_result env' r))
    | (st',Rerr err) => (st',emp,Rerr err))`;

val run_eval_top_def = Define `
(run_eval_top menv cenv st env (Tdec d) = 
  case run_eval_dec Nothing menv cenv st env d of
       (st', Rval (cenv', env')) => (st', cenv', Rval (emp, env'))
     | (st', Rerr err) => (st', emp, Rerr err)) ∧
(run_eval_top menv cenv st env (Tmod mn specs ds) =
  if ~MEM mn (MAP FST menv) then
    case run_eval_decs (Just mn) menv cenv st env ds of
         (st', cenv', Rval env') => (st', cenv', (Rval ([(mn, env')], emp)))
       | (st', cenv', Rerr err) => (st', cenv', Rerr err)
  else
    (st, emp, Rerr Rtype_error))`;

val run_eval_prog_def = Define `
(run_eval_prog menv cenv st env [] = (st, emp, Rval (emp, emp))) ∧
(run_eval_prog menv cenv st env (top::prog) =
  case run_eval_top menv cenv st env top of
       (st', cenv', Rval (menv', env')) =>
          (case run_eval_prog (merge menv' menv) (merge cenv' cenv) st' (merge env' env) prog of
              | (st'', cenv'', Rval (menv'', env'')) =>
                  (st'', merge cenv'' cenv', Rval (merge menv'' menv', merge env'' env'))
              | (st'', cenv'', Rerr err) => (st'', merge cenv'' cenv', Rerr err))
     | (st', cenv', Rerr err) => (st', cenv', Rerr err))`;

val run_eval_dec_spec = Q.store_thm ("run_eval_dec_spec",
`!mn menv cenv st env d st' r.
  (run_eval_dec mn menv cenv st env d = (st', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_dec mn menv cenv (SND st) env d (SND st', r)`,
 cases_on `d` >>
 rw [evaluate_dec_cases, run_eval_dec_def, fst_lem] >>
 every_case_tac >>
 fs [GSYM evaluate_run_eval] >>
 rw [] >>
 metis_tac [big_clocked_unclocked_equiv, clocked_min_counter, SND, pair_CASES, result_distinct, result_11]);

val run_eval_decs_spec = Q.store_thm ("run_eval_decs_spec",
`!mn menv cenv st env ds st' cenv' r.
  (run_eval_decs mn menv cenv st env ds = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_decs mn menv cenv (SND st) env ds (SND st', cenv', r)`,
 induct_on `ds` >>
 rw [Once evaluate_decs_cases] >>
 fs [run_eval_decs_def] >>
 every_case_tac >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] 
 >- (cases_on `r'''` >>
     fs [combine_dec_result_def, LibTheory.merge_def] >>
     every_case_tac >>
     fs [] >|
     [MAP_EVERY qexists_tac [`SND q`, `q'''`, `q'`, `r'`, `Rval a`] >>
          rw [],
      disj2_tac >>
          MAP_EVERY qexists_tac [`SND q`, `q'''`, `q'`, `r'`, `Rerr e`] >>
          rw []] >>
     NO_TAC) 
 >- metis_tac []);

val run_eval_top_spec = Q.store_thm ("run_eval_top_spec",
`!menv cenv st env top st' cenv' r.
  (run_eval_top menv cenv st env top = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_top menv cenv (SND st) env top (SND st', cenv', r)`,
 cases_on `top` >>
 rw [evaluate_top_cases, run_eval_top_def]  >>
 every_case_tac >>
 imp_res_tac run_eval_decs_spec >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] >>
 metis_tac []);

val run_eval_prog_spec = Q.store_thm ("run_eval_prog_spec",
`!menv cenv st env prog st' cenv' r.
  (run_eval_prog menv cenv st env prog = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_prog menv cenv (SND st) env prog (SND st', cenv', r)`,
 induct_on `prog` >>
 rw [run_eval_prog_def, Once evaluate_prog_cases] >>
 every_case_tac >>
 imp_res_tac run_eval_top_spec >>
 fs [] >>
 rw []
 >- (MAP_EVERY qexists_tac [`SND q`, `q''`, `q'`, `q''''`, `r'`, `Rval (q''''', r'')`] >>
     rw [combine_mod_result_def] >>
     NO_TAC) 
 >- (disj1_tac >>
     MAP_EVERY qexists_tac [`SND q`, `q''`, `q'`, `q''''`, `r'`, `Rerr e`] >>
     rw [combine_mod_result_def] >>
     NO_TAC));
-}

