open preamble miscTheory astTheory typeSystemTheory;
open infer_tTheory unifyTheory;
open stringTheory monadsyntax;

val _ = new_theory "infer";

val (inf_type_to_string_def,inf_type_to_string_ind) = Defn.tprove_no_defn((inf_type_to_string_def,inf_type_to_string_ind),
(WF_REL_TAC `measure (\x. case x of INL x => infer_t_size x | INR x => infer_t1_size x)`));
val _ = save_thm("inf_type_to_string_def",inf_type_to_string_def);
val _ = save_thm("inf_type_to_string_ind",inf_type_to_string_ind);
val _ = computeLib.add_persistent_funs ["inf_type_to_string_def"];

val list_subset_def = Define `
list_subset l1 l2 = EVERY (\x. MEM x l2) l1`;

(*  The inferencer uses a state monad internally to keep track of unifications at the expressions level *)

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Hol_datatype `
  exc = Success of 'a | Failure of 'b`;

val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val st_ex_bind_def = Define `
(st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    case x s of
      (Success y,s) => f y s
    | (Failure e,s) => (Failure e,s)`;

val st_ex_return_def = Define `
(st_ex_return (*: α -> (β, α, γ) M*)) x =
  λs. (Success x, s)`;

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val failwith_def = Define `
(failwith : α -> (β, γ, α) M) msg = (\s. (Failure msg, s))`;

val guard_def = Define `
guard P msg = if P then return () else failwith msg`;

val read_def = Define `
(read : (α, α, β) M) =
  \s. (Success s, s)`;

val write_def = Define `
(write : α -> (α, unit, β) M) v =
  \s. (Success (), v)`;

val id_to_string_def = Define `
(id_to_string (Short x) = x) ∧
(id_to_string (Long x y) = x ++ "." ++ y)`;

val lookup_st_ex_def = Define `
(lookup_st_ex pr x [] = failwith ("failed lookup: " ++ pr x)) ∧
(lookup_st_ex pr x ((y,v)::e) =
  if x = y then
    return v
  else
    lookup_st_ex pr x e)`;

val flookup_st_ex = Define `
flookup_st_ex pr x m =
  case FLOOKUP m x of
     | NONE => failwith ("failed lookup: " ++ pr x)
     | SOME v => return v`;

val _ = Hol_datatype `
infer_st = <| next_uvar : num;
              subst : 'a |>`;

val fresh_uvar_def = Define `
(fresh_uvar : ('b infer_st, infer_t, α) M) =
  \s. (Success (Infer_Tuvar s.next_uvar), s with <| next_uvar := s.next_uvar + 1 |>)`;

val n_fresh_uvar_def = Define  `
n_fresh_uvar (n:num) =
  if n = 0 then
    return []
  else
    do v <- fresh_uvar;
       vs <- n_fresh_uvar (n - 1);
       return (v::vs)
    od`;

val init_infer_state_def = Define `
  (init_infer_state : (num |-> infer_t) infer_st) = <| next_uvar := 0; subst := FEMPTY |>`;

val init_state_def = Define `
init_state =
  \st.
    (Success (), init_infer_state)`;

val add_constraint_def = Define `
add_constraint t1 t2 =
  \st.
    case t_unify st.subst t1 t2 of
      | NONE =>
          (Failure "Type mismatch", st)
      | SOME s =>
          (Success (), st with <| subst := s |>)`;

val add_constraints_def = Define `
(add_constraints [] [] =
  return ()) ∧
(add_constraints (t1::ts1) (t2::ts2) =
  do () <- add_constraint t1 t2;
     () <- add_constraints ts1 ts2;
     return ()
  od) ∧
(add_constraints _ _ =
  failwith "Bad call to add_constraints")`;

val get_next_uvar_def = Define `
get_next_uvar =
  \st. (Success st.next_uvar, st)`;

val apply_subst_def = Define `
apply_subst t =
  do st <- read;
     return (t_walkstar st.subst t)
  od`;

val apply_subst_list_def = Define `
apply_subst_list ts =
  do st <- read;
     return (MAP (t_walkstar st.subst) ts)
  od`;

(* We use a state argument for the inferencer's typing environment. This corresponds to the type system's typing environment
  The module and variable environment's types differ slightly.
*)

val _ = Hol_datatype `
 inf_environment =
  <| inf_m : modN |-> (varN, num # infer_t) alist
   ; inf_c : tenv_ctor
   ; inf_v : (varN, num # infer_t) alist
   ; inf_t : tenv_tabbrev
   |>`;

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised, the generalised type, and a substitution
 * that describes the generalisation *)
val generalise_def = Define `
(generalise m n s (Infer_Tapp ts tc) =
  let (num_gen, s', ts') = generalise_list m n s ts in
    (num_gen, s', Infer_Tapp ts' tc)) ∧
(generalise m n s (Infer_Tuvar uv) =
  case FLOOKUP s uv of
    | SOME n => (0, s, Infer_Tvar_db n)
    | NONE =>
        if m ≤ uv then
          (1, s|+(uv,n), Infer_Tvar_db n)
        else
          (0, s, Infer_Tuvar uv)) ∧
(generalise m n s (Infer_Tvar_db k) =
    (0, s, Infer_Tvar_db k)) ∧
(generalise_list m n s [] =
  (0,s,[])) ∧
(generalise_list m n s (t::ts) =
  let (num_gen, s', t') = generalise m n s t in
  let (num_gen', s'', ts') = generalise_list m (num_gen + n) s' ts in
    (num_gen+num_gen', s'', t'::ts'))`;

val infer_type_subst_def = tDefine "infer_type_subst" `
(infer_type_subst s (Tvar tv) =
  case ALOOKUP s tv of
   | SOME t => t
   | NONE => Infer_Tvar_db 0) ∧ (* should not happen *)
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (MAP (infer_type_subst s) ts) tn)`
(WF_REL_TAC `measure (t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val infer_deBruijn_subst_def = tDefine "infer_deBruijn_subst" `
(infer_deBruijn_subst s (Infer_Tvar_db n) =
  if n < LENGTH s then
    EL n s
  else
    (* should not happen *)
    Infer_Tvar_db (n - LENGTH s)) ∧
(infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val lookup_tenvC_st_ex_def = Define `
(lookup_tenvC_st_ex (Short cn) (cenvm, cenv) =
  lookup_st_ex (\x.x) cn cenv) ∧
(lookup_tenvC_st_ex (Long mn cn) (cenvm, cenv) =
  do cenv' <- lookup_st_ex (\x. id_to_string (Long x cn)) mn cenvm;
     lookup_st_ex (\x. id_to_string (Long mn x)) cn cenv'
  od)`;

(* This definition relies on the fact that for now, there isn't any *)
(* type variables in type annotations. *)
val tannot_to_infer_t_def = Define `
(tannot_to_infer_t (Tapp l c) = Infer_Tapp (tannots_to_infer_t l) c) ∧
(tannots_to_infer_t [] = []) ∧
(tannots_to_infer_t (t :: ts) = tannot_to_infer_t t :: tannots_to_infer_t ts)
`

val infer_p_def = tDefine "infer_p" `
(infer_p cenv (Pvar n) =
  do t <- fresh_uvar;
     return (t, [(n,t)])
  od) ∧
(infer_p cenv (Plit (IntLit i)) =
  return (Infer_Tapp [] TC_int, [])) ∧
(infer_p cenv (Plit (Char s)) =
  return (Infer_Tapp [] TC_char, [])) ∧
(infer_p cenv (Plit (StrLit s)) =
  return (Infer_Tapp [] TC_string, [])) ∧
(infer_p cenv (Plit (Word8 w)) =
  return (Infer_Tapp [] TC_word8, [])) ∧
(infer_p cenv (Plit (Word64 w)) =
  return (Infer_Tapp [] TC_word64, [])) ∧
(infer_p cenv (Pcon cn_opt ps) =
  case cn_opt of
    | NONE =>
        do (ts,tenv) <- infer_ps cenv ps;
           return (Infer_Tapp ts TC_tup, tenv)
        od
    | SOME cn =>
        do (tvs',ts,tn) <- lookup_tenvC_st_ex cn cenv;
           (ts'',tenv) <- infer_ps cenv ps;
           ts' <- n_fresh_uvar (LENGTH tvs');
           () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
           return (Infer_Tapp ts' (tid_exn_to_tc tn), tenv)
        od) ∧
(infer_p cenv (Pref p) =
  do (t,tenv) <- infer_p cenv p;
    return (Infer_Tapp [t] TC_ref, tenv)
  od) ∧
(infer_p cenv (Ptannot p t) =
 do (t',tenv) <- infer_p cenv p;
    () <- add_constraint t' (tannot_to_infer_t t);
    return (t', tenv)
 od) ∧
(infer_ps cenv [] =
  return ([], [])) ∧
(infer_ps cenv (p::ps) =
  do (t, tenv) <- infer_p cenv p;
     (ts, tenv') <- infer_ps cenv ps;
     return (t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. case x of INL (_,p) => pat_size p
                                  | INR (_,ps) => pat1_size ps)` >>
 rw []);

val infer_p_ind = fetch "-" "infer_p_ind"

val constrain_op_def = Define `
constrain_op op ts =
  case (op,ts) of
   | (Opn opn, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_int)
       od
   | (Opb opb, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Opw wz opw, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] (TC_word wz));
          () <- add_constraint t2 (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] (TC_word wz))
       od
   | (Shift wz sh n, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] (TC_word wz))
       od
   | (Equality, [t1;t2]) =>
       do () <- add_constraint t1 t2;
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Opapp, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t1 (Infer_Tapp [t2;uvar] TC_fn);
          return uvar
       od
   | (Opassign, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [t2] TC_ref);
          return (Infer_Tapp [] TC_tup)
       od
   | (Opref, [t]) => return (Infer_Tapp [t] TC_ref)
   | (Opderef, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] TC_ref);
          return uvar
       od
    | (Aw8alloc, [t1;t2]) =>
        do () <- add_constraint t1 (Infer_Tapp [] TC_int);
           () <- add_constraint t2 (Infer_Tapp [] TC_word8);
           return (Infer_Tapp [] TC_word8array)
        od
    | (Aw8sub, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_word8array);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_word8)
        od
    | (Aw8length, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_word8array);
          return (Infer_Tapp [] TC_int)
        od
    | (Aw8update, [t1;t2;t3]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_word8array);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          () <- add_constraint t3 (Infer_Tapp [] TC_word8);
          return (Infer_Tapp [] TC_tup)
        od
   | (WordFromInt wz, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] (TC_word wz))
       od
   | (WordToInt wz, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] TC_int)
       od
   | (Chr, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_char)
       od
   | (Ord, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_char);
          return (Infer_Tapp [] TC_int)
       od
   | (Chopb opb, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_char);
          () <- add_constraint t2 (Infer_Tapp [] TC_char);
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Explode, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_string);
          return (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short "list")))
       od
   | (Implode, [t]) =>
       do () <- add_constraint t (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short "list")));
          return (Infer_Tapp [] TC_string)
       od
   | (Strlen, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_string);
          return (Infer_Tapp [] TC_int)
       od
   | (VfromList, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] (TC_name (Short "list")));
          return (Infer_Tapp [uvar] TC_vector)
       od
   | (Vsub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t1 (Infer_Tapp [uvar] TC_vector);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return uvar
       od
   | (Vlength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] TC_vector);
          return (Infer_Tapp [] TC_int)
       od
   | (Aalloc, [t1;t2]) =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [t2] TC_array)
       od
   | (Asub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t1 (Infer_Tapp [uvar] TC_array);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return uvar
       od
   | (Alength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] TC_array);
          return (Infer_Tapp [] TC_int)
       od
   | (Aupdate, [t1;t2;t3]) =>
       do () <- add_constraint t1 (Infer_Tapp [t3] TC_array);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_tup)
       od
   | (FFI n, [t]) =>
       do () <- add_constraint t (Infer_Tapp [] TC_word8array);
          return (Infer_Tapp [] TC_tup)
       od
   | _ => failwith "Wrong number of arguments to primitive"`;

val infer_e_def = tDefine "infer_e" `
(infer_e ienv (Raise e) =
  do t2 <- infer_e ienv e;
     () <- add_constraint t2 (Infer_Tapp [] TC_exn);
     t1 <- fresh_uvar;
     return t1
  od) ∧
(infer_e ienv (Handle e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do t1 <- infer_e ienv e;
       () <- infer_pes ienv pes (Infer_Tapp [] TC_exn) t1;
       return t1
    od) ∧
(infer_e ienv (Lit (IntLit i)) =
  return (Infer_Tapp [] TC_int)) ∧
(infer_e ienv (Lit (Char c)) =
  return (Infer_Tapp [] TC_char)) ∧
(infer_e ienv (Lit (StrLit s)) =
  return (Infer_Tapp [] TC_string)) ∧
(infer_e ienv (Lit (Word8 w)) =
  return (Infer_Tapp [] TC_word8)) ∧
(infer_e ienv (Lit (Word64 w)) =
  return (Infer_Tapp [] TC_word64)) ∧
(infer_e ienv (Var (Short n)) =
  do (tvs,t) <- lookup_st_ex (\x.x) n ienv.inf_v;
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e ienv (Var (Long mn n)) =
  do venv <- flookup_st_ex (\x. id_to_string (Long x n)) mn ienv.inf_m;
     (tvs,t) <- lookup_st_ex (\x. id_to_string (Long mn x)) n venv;
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e ienv (Con cn_opt es) =
  case cn_opt of
      NONE =>
       do ts <- infer_es ienv es;
          return (Infer_Tapp ts TC_tup)
       od
    | SOME cn =>
       do (tvs',ts,tn) <- lookup_tenvC_st_ex cn ienv.inf_c;
          ts'' <- infer_es ienv es;
          ts' <- n_fresh_uvar (LENGTH tvs');
          () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
          return (Infer_Tapp ts' (tid_exn_to_tc tn))
       od) ∧
(infer_e ienv (Fun x e) =
  do t1 <- fresh_uvar;
     t2 <- infer_e (ienv with inf_v:=((x,(0,t1))::ienv.inf_v)) e;
     return (Infer_Tapp [t1;t2] TC_fn)
  od) ∧
(infer_e ienv (App op es) =
  do ts <- infer_es ienv es;
     t <- constrain_op op ts;
     return t
  od) ∧
(infer_e ienv (Log log e1 e2) =
  do t1 <- infer_e ienv e1;
     t2 <- infer_e ienv e2;
     () <- add_constraint t1 (Infer_Tapp [] (TC_name (Short "bool")));
     () <- add_constraint t2 (Infer_Tapp [] (TC_name (Short "bool")));
     return (Infer_Tapp [] (TC_name (Short "bool")))
  od) ∧
(infer_e ienv (If e1 e2 e3) =
  do t1 <- infer_e ienv e1;
     () <- add_constraint t1 (Infer_Tapp [] (TC_name (Short "bool")));
     t2 <- infer_e ienv e2;
     t3 <- infer_e ienv e3;
     () <- add_constraint t2 t3;
     return t2
  od) ∧
(infer_e ienv (Mat e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do t1 <- infer_e ienv e;
       t2 <- fresh_uvar;
       () <- infer_pes ienv pes t1 t2;
       return t2
  od) ∧
(infer_e ienv (Let x e1 e2) =
(* Don't do polymorphism for non-top-level lets
  if is_value e1 then
    do n <- get_next_uvar;
       t1 <- infer_e ienv e1;
       t1' <- apply_subst t1;
       (num_gen,s,t1'') <- return (generalise n 0 FEMPTY t1');
       t2 <- infer_e (ienv with inf_v:=(bind x (num_gen,t1'') ienv.inf_v)) e2;
       return t2
    od
  else
    *)
    do t1 <- infer_e ienv e1;
       t2 <- infer_e (ienv with inf_v:=opt_bind x (0,t1) ienv.inf_v) e2;
       return t2
    od) ∧
(* Don't do polymorphism for non-top-level let recs
(infer_e ienv (Letrec funs e) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name variable";
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
     funs_ts <- infer_funs (ienv with inf_v := env') funs;
     () <- add_constraints uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     env'' <- return (merge (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts') env);
     t <- infer_e (ienv with inf_v := env'') e;
     return t
  od) ∧
  *)
(infer_e ienv (Letrec funs e) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name";
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars ++ ienv.inf_v);
     funs_ts <- infer_funs (ienv with inf_v:=env') funs;
     () <- add_constraints uvars funs_ts;
     t <- infer_e (ienv with inf_v:=env') e;
     return t
  od) ∧
(infer_e ienv (Tannot e t) =
  do t' <- infer_e ienv e;
     () <- guard (check_freevars 0 [] t) "Free variable in type annotation";
     () <- add_constraint t' (infer_type_subst [] (type_name_subst ienv.inf_t t));
     return t'
   od) ∧
(infer_es ienv [] =
  return []) ∧
(infer_es ienv (e::es) =
  do t <- infer_e ienv e;
     ts <- infer_es ienv es;
     return (t::ts)
  od) ∧
(infer_pes ienv [] t1 t2 =
   return ()) ∧
(infer_pes ienv ((p,e)::pes) t1 t2 =
  do (t1', env') <- infer_p ienv.inf_c p;
     () <- guard (ALL_DISTINCT (MAP FST env')) "Duplicate pattern variable";
     () <- add_constraint t1 t1';
     t2' <- infer_e (ienv with inf_v := (MAP (\(n,t). (n,(0,t))) env' ++ ienv.inf_v)) e;
     () <- add_constraint t2 t2';
     () <- infer_pes ienv pes t1 t2;
     return ()
  od) ∧
(infer_funs ienv [] = return []) ∧
(infer_funs ienv ((f, x, e)::funs) =
  do uvar <- fresh_uvar;
     t <- infer_e (ienv with inf_v:=((x,(0,uvar))::ienv.inf_v)) e;
     ts <- infer_funs ienv funs;
     return (Infer_Tapp [uvar;t] TC_fn::ts)
  od)`
(WF_REL_TAC `measure (\x. case x of | INL (_,e) => exp_size e
                                    | INR (INL (_,es)) => exp6_size es
                                    | INR (INR (INL (_,pes,_,_))) => exp3_size pes
                                    | INR (INR (INR (_,funs))) => exp1_size funs)` >>
 rw []);

(* The final part of the inferencer state that appears at the decls level (and above) are the declared names. The only difference from the type system is that we use lists instead of sets *)

val _ = Hol_datatype `
 inf_decls =
  <| inf_defined_mods : modN list;
     inf_defined_types : (typeN id) list;
     inf_defined_exns : (conN id) list|>`;

val empty_inf_decls = Define `
 (empty_inf_decls = (<|inf_defined_mods := []; inf_defined_types := []; inf_defined_exns := []|>))`;

val infer_d_def = Define `
(infer_d mn idecls ienv (Dlet p e) =
  do () <- init_state;
     n <- get_next_uvar;
     t1 <- infer_e ienv e;
     (t2,env') <- infer_p ienv.inf_c p;
     () <- guard (ALL_DISTINCT (MAP FST env')) "Duplicate pattern variable";
     () <- add_constraint t1 t2;
     ts <- apply_subst_list (MAP SND env');
     (num_tvs, s, ts') <- return (generalise_list n 0 FEMPTY ts);
     () <- guard (num_tvs = 0 ∨ is_value e) "Value restriction violated";
     return (empty_inf_decls, FEMPTY, [], ZIP (MAP FST env', MAP (\t. (num_tvs, t)) ts'))
  od) ∧
(infer_d mn idecls ienv (Dletrec funs) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name";
     () <- init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars ++ ienv.inf_v);
     funs_ts <- infer_funs (ienv with inf_v:= env') funs;
     () <- add_constraints uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     return (empty_inf_decls,FEMPTY, [], list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts')
  od) ∧
(infer_d mn idecls ienv (Dtype tdefs) =
  do inf_t' <- return (FEMPTY |++ (MAP (λ(tvs,tn,ctors). (tn, (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))))) tdefs));
     inf_t'' <- return (merge_mod_env (FEMPTY,inf_t') ienv.inf_t);
     () <- guard (check_ctor_tenv mn inf_t'' tdefs) "Bad type definition";
     new_tdecls <- return (MAP (\(tvs,tn,ctors). mk_id mn tn) tdefs);
     () <- guard (EVERY (\new_id. ~MEM new_id idecls.inf_defined_types) new_tdecls) "Duplicate type definition";
     return (empty_inf_decls with inf_defined_types := new_tdecls,inf_t', build_ctor_tenv mn inf_t'' tdefs, [])
  od) ∧
(infer_d mn idecls ienv (Dtabbrev tvs tn t) =
  do () <- guard (ALL_DISTINCT tvs) "Duplicate type variables";
     () <- guard (check_freevars 0 tvs t ∧ check_type_names ienv.inf_t t) "Bad type definition";
     return (empty_inf_decls, FEMPTY |+ (tn, (tvs,type_name_subst ienv.inf_t t)), [], [])
  od) ∧
(infer_d mn idecls ienv (Dexn cn ts) =
  do () <- guard (check_exn_tenv mn cn ts ∧ EVERY (check_type_names ienv.inf_t) ts ) "Bad exception definition";
     () <- guard (~MEM (mk_id mn cn) idecls.inf_defined_exns) "Duplicate exception definition";
     return (empty_inf_decls with inf_defined_exns:=[mk_id mn cn], FEMPTY, [(cn, ([], MAP (\x. type_name_subst ienv.inf_t x) ts, TypeExn (mk_id mn cn)))], [])
  od)`;

val append_decls_def = Define `
append_decls idecls1 idecls2 =
  <|inf_defined_mods := idecls1.inf_defined_mods ++ idecls2.inf_defined_mods ;
    inf_defined_types := idecls1.inf_defined_types ++ idecls2.inf_defined_types ;
    inf_defined_exns := idecls1.inf_defined_exns ++ idecls2.inf_defined_exns|>`;

val infer_ds_def = Define `
(infer_ds mn idecls ienv [] =
  return (empty_inf_decls, FEMPTY, [],[])) ∧
(infer_ds mn idecls ienv (d::ds) =
  do
    (decls',tenvT',cenv',env') <- infer_d mn idecls ienv d;
    (decls'',tenvT'',cenv'',env'') <- infer_ds mn (append_decls decls' idecls)
    (ienv with
      <|inf_t:=(merge_mod_env (FEMPTY,tenvT') ienv.inf_t);
        inf_c:=(merge_alist_mod_env ([],cenv') ienv.inf_c);
        inf_v:=(env' ++ ienv.inf_v)|>) ds;
    return (append_decls decls'' decls', FUNION tenvT'' tenvT', cenv'' ++ cenv', env'' ++ env')
  od)`;

val t_to_freevars_def = Define `
(t_to_freevars (Tvar tn) =
  return [tn]) ∧
(t_to_freevars (Tvar_db _) =
  failwith "deBruijn index in type definition") ∧
(t_to_freevars (Tapp ts tc) =
  ts_to_freevars ts) ∧
(ts_to_freevars [] = return []) ∧
(ts_to_freevars (t::ts) =
  do fvs1 <- t_to_freevars t;
     fvs2 <- ts_to_freevars ts;
     return (fvs1++fvs2)
  od)`;

val check_specs_def = Define `
(check_specs mn tenvT idecls tenvT' cenv env [] =
  return (idecls,tenvT',cenv,env)) ∧
(check_specs mn tenvT idecls tenvT' cenv env (Sval x t::specs) =
  do fvs <- t_to_freevars t;
     fvs' <- return (nub fvs);
     () <- guard (check_type_names tenvT t) "Bad type annotation";
     check_specs mn tenvT idecls tenvT' cenv ((x, (LENGTH fvs', infer_type_subst (ZIP (fvs', MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) (type_name_subst tenvT t))) :: env) specs
  od) ∧
(check_specs mn tenvT idecls tenvT' cenv env (Stype tdefs :: specs) =
  do new_tenvT <- return (FEMPTY |++ MAP (λ(tvs,tn,ctors). (tn, (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))))) tdefs);
     tenvT'' <- return (merge_mod_env (FEMPTY,new_tenvT) tenvT);
     () <- guard (check_ctor_tenv mn tenvT'' tdefs) "Bad type definition";
     new_tdecls <- return (MAP (\(tvs,tn,ctors). mk_id mn tn) tdefs);
     check_specs mn (merge_mod_env (FEMPTY,new_tenvT) tenvT) (idecls with <|inf_defined_types:=new_tdecls++idecls.inf_defined_types|>) (FUNION new_tenvT tenvT') (build_ctor_tenv mn tenvT'' tdefs ++ cenv) env specs
  od) ∧
(check_specs mn tenvT idecls tenvT' cenv env (Stabbrev tvs tn t :: specs) =
  do () <- guard (ALL_DISTINCT tvs) "Duplicate type variables";
     () <- guard (check_freevars 0 tvs t ∧ check_type_names tenvT t) "Bad type definition";
     new_tenvT <- return (tn, (tvs,type_name_subst tenvT t));
     check_specs mn (merge_mod_env (FEMPTY,FEMPTY |+ new_tenvT) tenvT) idecls (tenvT' |+ new_tenvT) cenv env specs
  od) ∧
(check_specs mn tenvT idecls tenvT' cenv env (Sexn cn ts :: specs) =
  do () <- guard (check_exn_tenv mn cn ts ∧ EVERY (check_type_names tenvT) ts) "Bad exception definition";
     check_specs mn tenvT (idecls with <|inf_defined_exns:=mk_id mn cn::idecls.inf_defined_exns|>) tenvT' ((cn, ([], MAP (\x. type_name_subst tenvT x) ts, TypeExn (mk_id mn cn))) :: cenv) env specs
  od) ∧
(check_specs mn tenvT idecls tenvT' cenv env (Stype_opq tvs tn :: specs) =
  do () <- guard (ALL_DISTINCT tvs) "Duplicate type variables";
     new_tenvT <- return (tn, (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))));
     check_specs mn (merge_mod_env (FEMPTY,FEMPTY |+ new_tenvT) tenvT) (idecls with <|inf_defined_types:=mk_id mn tn::idecls.inf_defined_types|>) (tenvT' |+ new_tenvT) cenv env specs
  od)`;

val check_flat_weakC_def = Define `
(check_flat_weakC cenv_impl cenv_spec =
  EVERY (\(cn, (tvs_spec, ts_spec, tn_spec)).
            case ALOOKUP cenv_impl cn of
              | NONE => F
              | SOME (tvs_impl,ts_impl,tn_impl) =>
                  (tn_spec = tn_impl) ∧
                  (tvs_spec = tvs_impl) ∧
                  (ts_spec = ts_impl))
        cenv_spec)`;

val check_flat_weakT_def = Define `
(check_flat_weakT mn tenvT_impl tenvT_spec =
  FEVERY (\(tn, (tvs_spec, t_spec)).
            case FLOOKUP tenvT_impl tn of
              | NONE => F
              | SOME (tvs_impl,t_impl) =>
                  (tvs_spec = tvs_impl) ∧
                  ((t_spec = t_impl) ∨
                   t_spec = Tapp (MAP Tvar tvs_spec) (TC_name (mk_id mn tn))))
        tenvT_spec)`;

val check_weakE_def = Define `
(check_weakE env_impl [] = return ()) ∧
(check_weakE env_impl ((n, (tvs_spec, t_spec)) :: env_spec) =
  case ALOOKUP env_impl n of
    | NONE => failwith "Signature mismatch"
    | SOME (tvs_impl,t_impl) =>
        do () <- init_state;
           uvs <- n_fresh_uvar tvs_impl;
           t <- return (infer_deBruijn_subst uvs t_impl);
           () <- add_constraint t_spec t;
           check_weakE env_impl env_spec
        od)`;

val check_weak_decls_def = Define `
check_weak_decls decls_impl decls_spec ⇔
  decls_spec.inf_defined_mods = decls_impl.inf_defined_mods ∧
  list_subset decls_spec.inf_defined_types decls_impl.inf_defined_types ∧
  list_subset decls_spec.inf_defined_exns decls_impl.inf_defined_exns`;

val check_signature_def = Define `
(check_signature mn tenvT init_decls decls1 tenvT' cenv env NONE =
  return (decls1, tenvT', cenv, env)) ∧
(check_signature mn tenvT init_decls decls1 tenvT' cenv env (SOME specs) =
  do (decls', tenvT'', cenv', env') <- check_specs mn tenvT empty_inf_decls FEMPTY [] [] specs;
     () <- guard (check_flat_weakT mn tenvT' tenvT'') "Signature mismatch";
     () <- guard (check_flat_weakC cenv (anub cenv' [])) "Signature mismatch";
     () <- check_weakE env (anub env' []);
     () <- guard (check_weak_decls decls1 decls') "Signature mismatch";
     return (decls',tenvT'',cenv',env')
  od)`;

val infer_top_def = Define `
(infer_top idecls ienv (Tdec d) =
  do
    (decls',tenvT',cenv',env') <- infer_d NONE idecls ienv d;
    return (decls',(FEMPTY,tenvT'),FEMPTY,([],cenv'), env')
  od) ∧
(infer_top idecls ienv (Tmod mn spec ds1) =
  do
    () <- guard (~MEM mn idecls.inf_defined_mods) ("Duplicate module: " ++ mn);
    (decls',tenvT',cenv',env') <- infer_ds (SOME mn) idecls ienv ds1;
    (new_decls,tenvT'',cenv'',env'')
        <- check_signature (SOME mn) ienv.inf_t idecls decls' tenvT' cenv' env' spec;
    return (new_decls with inf_defined_mods := mn :: new_decls.inf_defined_mods,
            (FEMPTY |+ (mn,tenvT''),FEMPTY),
            FEMPTY |+ (mn,env''),
            ([(mn,cenv'')],[]),
            [])
  od)`;

val infer_prog_def = Define `
(infer_prog idecls ienv [] =
  return (empty_inf_decls,(FEMPTY,FEMPTY),FEMPTY,([],[]),[])) ∧
(infer_prog idecls ienv (top::ds) =
  do
    (decls',tenvT',menv',cenv',env') <- infer_top idecls ienv top;
    (decls'', tenvT'', menv'', cenv'', env'') <- infer_prog (append_decls decls' idecls)
      <|inf_t:=(merge_mod_env tenvT' ienv.inf_t);
        inf_c:=(merge_alist_mod_env cenv' ienv.inf_c);
        inf_v:=(env' ++ ienv.inf_v);
        inf_m:=FUNION menv' ienv.inf_m|> ds;
    return (append_decls decls'' decls',
            merge_mod_env tenvT'' tenvT',
            FUNION menv'' menv',
            merge_alist_mod_env cenv'' cenv',
            env'' ++ env')
  od)`;

val _ = Datatype`
  inferencer_config =
  <| inf_decls : inf_decls
   ; inf_env   : inf_environment|>`

val init_env_def = Define`
   init_env = <|inf_t := (FEMPTY,FEMPTY); inf_m := FEMPTY ; inf_c := ([],[]) ; inf_v := [] |> `;

val init_config_def = Define`
  init_config =
  <| inf_decls := empty_inf_decls
   ; inf_env := init_env|>`

val infertype_prog_def = Define`
  infertype_prog c prog =
    case FST (infer_prog c.inf_decls c.inf_env prog init_infer_state) of
    | Success (new_decls, new_t, new_m, new_c, new_v) =>
        SOME ( <| inf_decls := append_decls new_decls c.inf_decls
                ; inf_env :=
                  <|inf_t:=(merge_mod_env new_t c.inf_env.inf_t);
                    inf_c:=(merge_alist_mod_env new_c c.inf_env.inf_c);
                    inf_v:=(new_v ++ c.inf_env.inf_v);
                    inf_m:=FUNION new_m c.inf_env.inf_m|>
                |>)
    | _ => NONE`;

val Infer_Tfn_def = Define `
Infer_Tfn t1 t2 = Infer_Tapp [t1;t2] TC_fn`;

val Infer_Tint = Define `
Infer_Tint = Infer_Tapp [] TC_int`;

val Infer_Tbool = Define `
Infer_Tbool = Infer_Tapp [] (TC_name (Short "bool"))`;

val Infer_Tunit = Define `
Infer_Tunit = Infer_Tapp [] TC_tup`;

val Infer_Tref = Define `
Infer_Tref t = Infer_Tapp [t] TC_ref`;

(* The following aren't needed to run the inferencer, but are useful in the proofs
 * about it *)

val infer_deBruijn_inc_def = tDefine "infer_deBruijn_inc" `
(infer_deBruijn_inc n (Infer_Tvar_db m) =
  Infer_Tvar_db (m + n)) ∧
(infer_deBruijn_inc n (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) ∧
(infer_deBruijn_inc n (Infer_Tuvar m) =
  Infer_Tuvar m)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val infer_subst_def = tDefine "infer_subst" `
(infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n) ∧
(infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst s) ts) tc) ∧
(infer_subst s (Infer_Tuvar n) =
  case FLOOKUP s n of
      NONE => Infer_Tuvar n
    | SOME m => Infer_Tvar_db m)`
(wf_rel_tac `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 srw_tac[ARITH_ss] [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val pure_add_constraints_def = Define `
(pure_add_constraints s [] s' = (s = s')) ∧
(pure_add_constraints s1 ((t1,t2)::rest) s' =
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s')`;

val check_t_def = tDefine "check_t" `
(check_t n uvars (Infer_Tuvar v) = (v ∈ uvars)) ∧
(check_t n uvars (Infer_Tvar_db n') =
  (n' < n)) ∧
(check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars) ts)`
(WF_REL_TAC `measure (infer_t_size o SND o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val check_env_def = Define `
check_env uvars env =
  EVERY (\(x, (tvs,t)). check_t tvs uvars t) env`;

val check_menv_def = Define `
check_menv menv =
  FEVERY (\(mn,env). EVERY (\(x, (tvs,t)). check_t tvs {} t) env) menv`;

val check_flat_cenv_def = Define `
check_flat_cenv cenv =
  EVERY (\(cn,(tvs,ts,t)). EVERY (check_freevars 0 tvs) ts) cenv`;

val check_cenv_def = Define `
check_cenv (mcenv, cenv) ⇔
  EVERY (\(cn,cenv'). check_flat_cenv cenv') mcenv ∧
  check_flat_cenv cenv`;

val check_s_def = Define `
check_s tvs uvs s =
  !uv. uv ∈ FDOM s ⇒ check_t tvs uvs (s ' uv)`;

(* Adding the constraints extra_constraints moves the constraint set from s1 to
 * s2, and s2 is required to be complete in that it assigns to (at least) all
 * the uvars ≤ next_uvar, and when we apply it to any uvar, we get back a type
 * without any uvars in it. *)
val sub_completion_def = Define `
sub_completion tvs next_uvar s1 extra_constraints s2 =
  (pure_add_constraints s1 extra_constraints s2 ∧
   (count next_uvar SUBSET FDOM s2) ∧
   (!uv. uv ∈ FDOM s2 ⇒ check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv))))`;

val _ = export_theory ();
