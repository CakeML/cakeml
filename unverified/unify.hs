module Unify where
import Data.Map as Map
import Data.List as List
import Ast as Ast

type Uvar = Integer

data Infer_t = 
    Infer_Tvar_db Integer
  | Infer_Tapp [Infer_t] Ast.Tc
  | Infer_Tuvar Uvar

type Subst = Map.Map Uvar Infer_t

t_vwalk :: Subst -> Uvar -> Infer_t
t_vwalk s v =
  case Map.lookup v s of
    Nothing -> Infer_Tuvar v
    Just (Infer_Tuvar u) -> t_vwalk s u
    Just (Infer_Tapp ts tc') -> Infer_Tapp ts tc'
    Just (Infer_Tvar_db n) -> Infer_Tvar_db n

t_walk :: Subst -> Infer_t -> Infer_t
t_walk s (Infer_Tuvar v) = t_vwalk s v
t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc
t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n

t_oc :: Subst -> Infer_t -> Uvar -> Bool
t_oc s t v =
  case t_walk s t of
    Infer_Tuvar u -> v == u
    Infer_Tapp ts tc' -> List.any (\t -> t_oc s t v) ts
    Infer_Tvar_db n -> False

t_ext_s_check :: Subst -> Uvar -> Infer_t -> Maybe Subst
t_ext_s_check s v t = if t_oc s t v then Nothing else Just (Map.insert v t s)

t_unify :: Subst -> Infer_t -> Infer_t -> Maybe Subst
t_unify s t1 t2 =
  case (t_walk s t1, t_walk s t2) of
    (Infer_Tuvar v1, Infer_Tuvar v2) ->
       Just (if v1 == v2 then s else Map.insert v1 (Infer_Tuvar v2) s)
    (Infer_Tuvar v1, t2) -> t_ext_s_check s v1 t2
    (t1, Infer_Tuvar v2) -> t_ext_s_check s v2 t1
    (Infer_Tapp ts1 tc1, Infer_Tapp ts2 tc2) ->
      if tc1 == tc2 then
        ts_unify s ts1 ts2
      else
        Nothing
    (Infer_Tvar_db n1, Infer_Tvar_db n2) ->
      if n1 == n2 then 
        Just s 
      else
        Nothing
    _ -> Nothing

ts_unify :: Subst -> [Infer_t] -> [Infer_t] -> Maybe Subst
ts_unify s [] [] = Just s
ts_unify s (t1:ts1) (t2:ts2) =
  case t_unify s t1 t2 of
    Nothing -> Nothing
    Just s' -> ts_unify s' ts1 ts2
ts_unify s _ _ = Nothing

apply_subst_t :: Subst -> Infer_t -> Infer_t
apply_subst_t s (Infer_Tuvar n) =
  case Map.lookup n s of
    Nothing -> Infer_Tuvar n
    Just t -> t
apply_subst_t s (Infer_Tapp ts tc) =
  Infer_Tapp (List.map (apply_subst_t s) ts) tc
apply_subst_t s (Infer_Tvar_db n) = 
  Infer_Tvar_db n

t_walkstar :: Subst -> Infer_t -> Infer_t
t_walkstar s t =
  case t_walk s t of
    Infer_Tuvar v -> Infer_Tuvar v
    Infer_Tapp ts tc0 -> Infer_Tapp (List.map (t_walkstar s) ts) tc0
    Infer_Tvar_db n -> Infer_Tvar_db n
