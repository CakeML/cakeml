(*
  Definition of CakeML's type inferencer.
*)
Theory infer
Ancestors
  misc ast namespace typeSystem namespaceProps infer_t unify
  string primTypes
Libs
  preamble

val _ = monadsyntax.temp_add_monadsyntax()
val _ = patternMatchesSyntax.temp_enable_pmatch();

(*  The inferencer uses a state monad internally to keep track of unifications at the expressions level *)

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

Datatype:
  exc = Success 'a | Failure 'b
End

Type err_var = (type_of ``primTypes$prim_tenv.t``)

Datatype:
  loc_err_info = <| loc : locs option ;
                    err : err_var |>
End

Type M = ``:'a -> ('b, 'c) exc # 'a``

Definition st_ex_bind_def:
  (st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    case x s of
      (Success y,s) => f y s
    | (Failure x,s) => (Failure x,s)
End

Definition st_ex_return_def:
  (st_ex_return (*: α -> (β, α, γ) M*)) x =
    λs. (Success x, s)
End

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``

Definition failwith_def:
  (failwith : loc_err_info -> α -> (β, γ, (locs option # α)) M) l msg =
    (\s. (Failure (l.loc, msg), s))
End

Definition guard_def:
  guard P l msg = if P then return () else failwith l msg
End

Definition read_def:
  (read : (α, α, β) M) =
  \s. (Success s, s)
End

Definition write_def:
  (write : α -> (α, unit, β) M) v =
  \s. (Success (), v)
End

Definition lookup_st_ex_def:
  lookup_st_ex l err id ienv st =
    case nsLookup ienv id of
    | NONE => (Failure (l.loc, concat [«Undefined »; err; «: »; id_to_string id]), st)
    | SOME v => (Success v, st)
End

Datatype:
  infer_st = <| next_uvar : num;
                subst : type_ident |-> infer_t ;
                next_id : num;
              |>
End

Definition fresh_uvar_def:
  (fresh_uvar : (infer_st, infer_t, α) M) =
  \s. (Success (Infer_Tuvar s.next_uvar), s with <| next_uvar := s.next_uvar + 1 |>)
End

Definition n_fresh_uvar_def:
  n_fresh_uvar (n:num) =
  if n = 0 then
    return []
  else
    do v <- fresh_uvar;
       vs <- n_fresh_uvar (n - 1);
       return (v::vs)
    od
End

Definition n_fresh_id_def:
  n_fresh_id n =
  λs.
  (Success (GENLIST (λx. s.next_id+x) n), s with next_id := s.next_id+n)
End

(* Doesn't reset the ID component *)
Definition init_infer_state_def:
  init_infer_state st = st with <| next_uvar := 0; subst := FEMPTY |>
End

Definition init_state_def:
  init_state =
  \st.
    (Success (), init_infer_state st)
End

Definition add_constraint_def:
  add_constraint (l : loc_err_info) t1 t2 =
  \st.
    case t_unify st.subst t1 t2 of
      | NONE =>
          (Failure (l.loc, concat [«Type mismatch between »;
                                   inf_type_to_string l.err
                                         (t_walkstar st.subst t1);
                                   « and »;
                                   inf_type_to_string l.err
                                         (t_walkstar st.subst t2)]), st)
      | SOME s =>
          (Success (), st with <| subst := s |>)
End

Definition add_constraints_def:
(add_constraints l [] [] =
  return ()) ∧
(add_constraints l (t1::ts1) (t2::ts2) =
  do () <- add_constraint l t1 t2;
     () <- add_constraints l ts1 ts2;
     return ()
  od) ∧
(add_constraints l _ _ =
  failwith l («Internal error: Bad call to add_constraints»))
End

Definition get_next_uvar_def:
get_next_uvar =
  \st. (Success st.next_uvar, st)
End

Definition apply_subst_def:
apply_subst t =
  do st <- read;
     return (t_walkstar st.subst t)
  od
End

Definition apply_subst_list_def:
apply_subst_list ts =
  do st <- read;
     return (MAP (t_walkstar st.subst) ts)
  od
End

(* We use a state argument for the inferencer's typing environment. This corresponds to the type system's typing environment
  The module and variable environment's types differ slightly.
*)

Datatype:
  inf_env =
  <| inf_v : (modN, varN, num # infer_t) namespace
   ; inf_c : tenv_ctor
   ; inf_t : tenv_abbrev
   |>
End

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised, the generalised type, and a substitution
 * that describes the generalisation *)
Definition generalise_def:
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
    (num_gen+num_gen', s'', t'::ts'))
End

Definition infer_type_subst_def:
(infer_type_subst s (Tvar tv) =
  case ALOOKUP s tv of
   | SOME t => t
   | NONE => Infer_Tvar_db 0) ∧ (* should not happen *)
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (infer_type_subst_list s ts) tn) ∧
(infer_type_subst_list s [] = []) ∧
(infer_type_subst_list s (x::xs) =
  infer_type_subst s x :: infer_type_subst_list s xs)
End

Theorem infer_type_subst_alt:
(infer_type_subst s (Tvar tv) =
  case ALOOKUP s tv of
   | SOME t => t
   | NONE => Infer_Tvar_db 0) ∧ (* should not happen *)
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (MAP (infer_type_subst s) ts) tn)
Proof
  rewrite_tac [infer_type_subst_def]
  \\ Induct_on ‘ts’ \\ gvs [infer_type_subst_def]
QED

Definition infer_deBruijn_subst_def:
(infer_deBruijn_subst s (Infer_Tvar_db n) =
  if n < LENGTH s then
    EL n s
  else
    (* should not happen *)
    Infer_Tvar_db (n - LENGTH s)) ∧
(infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (infer_deBruijn_subst_list s ts) tn) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n) ∧
(infer_deBruijn_subst_list s [] = []) ∧
(infer_deBruijn_subst_list s (t::ts) =
  infer_deBruijn_subst s t :: infer_deBruijn_subst_list s ts)
End

Theorem infer_deBruijn_subst_alt:
(infer_deBruijn_subst s (Infer_Tvar_db n) =
  if n < LENGTH s then
    EL n s
  else
    (* should not happen *)
    Infer_Tvar_db (n - LENGTH s)) ∧
(infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n)
Proof
  rewrite_tac [infer_deBruijn_subst_def]
  \\ Induct_on ‘ts’ \\ gvs [infer_deBruijn_subst_def]
QED

Definition type_name_check_subst_def:
  (type_name_check_subst l err_string_f tenvT fvs (Atvar tv) =
    do
      guard (MEM tv fvs) l (err_string_f tv);
      return (Tvar tv)
    od) ∧
  (type_name_check_subst l f tenvT fvs (Attup ts) =
    do
      ts' <- type_name_check_subst_list l f tenvT fvs ts;
      return (Ttup ts')
    od) ∧
  (type_name_check_subst l f tenvT fvs (Atfun t1 t2) =
    do
      t1' <- type_name_check_subst l f tenvT fvs t1;
      t2' <- type_name_check_subst l f tenvT fvs t2;
      return (Tfn t1' t2');
    od) ∧
  (type_name_check_subst l f tenvT fvs (Atapp ts tc) =
    do
      ts' <- type_name_check_subst_list l f tenvT fvs ts;
      (tvs', t') <- lookup_st_ex l «type constructor» tc tenvT;
      guard (LENGTH tvs' = LENGTH ts) l
                 (concat [«Type constructor »; id_to_string tc; « given »;
                          toString (&LENGTH ts); « arguments, but expected »;
                          toString (&LENGTH tvs')]);
      return (type_subst (alist_to_fmap (ZIP (tvs', ts'))) t');
    od) ∧
  (type_name_check_subst_list l f tenvT fvs [] = return []) ∧
  (type_name_check_subst_list l f tenvT fvs (t::ts) =
    do
      t' <- type_name_check_subst l f tenvT fvs t;
      ts' <- type_name_check_subst_list l f tenvT fvs ts;
      return (t'::ts');
    od)
End

Theorem bind_guard:
  st_ex_bind (guard b l x) g =
  λs. if b then g () s else (Failure (l.loc,x),s)
Proof
  rw [st_ex_bind_def,FUN_EQ_THM,guard_def,st_ex_return_def,failwith_def]
QED

Theorem st_ex_bind_pair:
  monad_bind x f =
  (λs.
     case x s of
     | (Success (y,z),s) => f (y,z) s
     | (Failure x,s) => (Failure x,s))
Proof
  gvs [st_ex_bind_def,FUN_EQ_THM]
  \\ rw [] \\ Cases_on ‘x s’ \\ gvs []
  \\ Cases_on ‘q’ \\ gvs [] \\ PairCases_on ‘a’ \\ gvs []
QED

Theorem st_ex_bind_triple:
  monad_bind x f =
  (λs.
     case x s of
     | (Success (y,z,q),s) => f (y,z,q) s
     | (Failure x,s) => (Failure x,s))
Proof
  gvs [st_ex_bind_def,FUN_EQ_THM]
  \\ rw [] \\ Cases_on ‘x s’ \\ gvs []
  \\ Cases_on ‘q’ \\ gvs [] \\ PairCases_on ‘a’ \\ gvs []
QED

val type_name_check_subst_alt =
  type_name_check_subst_def
  |> SRULE [bind_guard]
  |> SRULE [st_ex_bind_pair]
  |> SRULE [st_ex_bind_def,lookup_st_ex_def,st_ex_return_def];

Definition type_name_check_sub_def:
   (type_name_check_sub l tenvT fvs (Atvar tv) =
        (λs. if MEM tv fvs then (Success (Tvar tv),s)
             else (Failure (l.loc,INR tv),s))) ∧
   (type_name_check_sub l tenvT fvs (Attup ts) =
        (λs. case type_name_check_sub_list l tenvT fvs ts s of
               (Success ts',s) => (Success (Ttup ts'),s)
             | (Failure x,s) => (Failure x,s))) ∧
   (type_name_check_sub l tenvT fvs (Atfun t1 t2) =
        (λs. case type_name_check_sub l tenvT fvs t1 s of
               (Success t1',s) =>
                 (case type_name_check_sub l tenvT fvs t2 s of
                    (Success t2',s) => (Success (Tfn t1' t2'),s)
                  | (Failure x,s) => (Failure x,s))
             | (Failure x,s) => (Failure x,s))) ∧
   (type_name_check_sub l tenvT fvs (Atapp ts tc) =
        (λs. case type_name_check_sub_list l tenvT fvs ts s of
               (Success ts',s) =>
                 (case
                    case nsLookup tenvT tc of
                      NONE =>
                        (Failure
                           (l.loc, INL $
                            concat
                              [«Undefined »;
                               «type constructor»; «: »;
                               id_to_string tc]),s)
                    | SOME v => (Success v,s)
                  of
                    (Success (y,z),s) =>
                      if LENGTH y = LENGTH ts then
                        (Success (type_subst (alist_to_fmap (ZIP (y,ts'))) z),
                         s)
                      else
                        (Failure
                           (l.loc, INL $
                            concat
                              [«Type constructor »; id_to_string tc;
                               « given »; toString (LENGTH ts);
                               « arguments, but expected »;
                               toString (LENGTH y)]),s)
                  | (Failure x,s) => (Failure x,s))
             | (Failure x,s) => (Failure x,s))) ∧
   (type_name_check_sub_list l tenvT fvs [] = (λs. (Success [],s))) ∧
   (type_name_check_sub_list l tenvT fvs (t::ts) =
       (λs. case type_name_check_sub l tenvT fvs t s of
              (Success t',s) =>
                (case type_name_check_sub_list l tenvT fvs ts s of
                   (Success ts',s) => (Success (t'::ts'),s)
                 | (Failure x,s) => (Failure x,s))
            | (Failure x,s) => (Failure x,s)))
End

Theorem to_type_name_check_sub:
  (∀t l f tenvT fvs.
     type_name_check_subst l f tenvT fvs t =
     λs:'a. case type_name_check_sub l tenvT fvs t s of
         | (Failure (x,INR r),s) => (Failure (x,f r),s)
         | (Failure (x,INL r),s) => (Failure (x,r),s)
         | (Success y,s) => (Success y,s)) ∧
  (∀t l f tenvT fvs.
     type_name_check_subst_list l f tenvT fvs t =
     λs:'a. case type_name_check_sub_list l tenvT fvs t s of
         | (Failure (x,INR r),s) => (Failure (x,f r),s)
         | (Failure (x,INL r),s) => (Failure (x,r),s)
         | (Success y,s) => (Success y,s))
Proof
  ho_match_mp_tac ast_t_induction \\ rpt strip_tac
  \\ simp [type_name_check_subst_alt,type_name_check_sub_def,FUN_EQ_THM]
  \\ rw []
  >-
   (Cases_on ‘type_name_check_sub l tenvT fvs t s’ \\ gvs []
    \\ Cases_on ‘q’ \\ gvs []
    \\ Cases_on ‘type_name_check_sub l tenvT fvs t' r’ \\ gvs []
    \\ rpt (TOP_CASE_TAC \\ gvs [AllCaseEqs()])
    \\ gvs [AllCaseEqs()])
  >-
   (Cases_on ‘type_name_check_sub_list l tenvT fvs t s’ \\ gvs []
    \\ Cases_on ‘q’ \\ gvs []
    \\ rpt (TOP_CASE_TAC \\ gvs [AllCaseEqs()])
    \\ gvs [AllCaseEqs()])
  >-
   (Cases_on ‘type_name_check_sub_list l tenvT fvs t s’ \\ gvs []
    \\ Cases_on ‘q’ \\ gvs []
    \\ rpt (TOP_CASE_TAC \\ gvs [])
    \\ rpt (FULL_CASE_TAC \\ gvs []))
  \\ rpt (FULL_CASE_TAC \\ gvs [])
QED

Theorem bind_type_name_check_subst:
  (st_ex_bind (type_name_check_subst l f tenvT fvs t) g =
   λs:'a. case type_name_check_sub l tenvT fvs t s of
          | (Failure (x,INR r),s) => (Failure (x,f r),s)
          | (Failure (x,INL r),s) => (Failure (x,r),s)
          | (Success y,s) => g y s) ∧
  (st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) gs =
   λs:'a. case type_name_check_sub_list l tenvT fvs ts s of
          | (Failure (x,INR r),s) => (Failure (x,f r),s)
          | (Failure (x,INL r),s) => (Failure (x,r),s)
          | (Success y,s) => gs y s)
Proof
  rw [to_type_name_check_sub,st_ex_bind_def,FUN_EQ_THM]
  \\ rpt (FULL_CASE_TAC \\ gvs [])
QED

Definition find_dup_def:
  find_dup [] = NONE ∧
  find_dup (x::xs) = if MEM x xs then SOME x else find_dup xs
End

Definition check_dups_def:
  (check_dups l f [] = return ()) ∧
  (check_dups l f (h::t) =
     if MEM h t then
       failwith l (f h)
     else
       check_dups l f t)
End

Theorem check_dups_eq_find_dup:
  ∀xs.
    st_ex_bind (check_dups l f xs) g =
    λs. case find_dup xs of
        | NONE => g () s
        | SOME x => (Failure (l.loc, f x), s)
Proof
  Induct
  \\ simp [check_dups_def,st_ex_return_def,find_dup_def]
  >- gvs [st_ex_bind_def]
  \\ rw [failwith_def]
  \\ gvs [st_ex_bind_def]
QED

Definition check_ctor_types_def:
  (check_ctor_types l tenvT tvs [] = return ()) ∧
  (check_ctor_types l tenvT tvs ((cn,ts)::ctors) =
    do
      type_name_check_subst_list l
            (\tv. concat [«Unbound type variable »; tv;
                          « in type definition with constructor »; cn])
            tenvT tvs ts;
      check_ctor_types l tenvT tvs ctors
    od)
End

Theorem check_ctor_types_expand = check_ctor_types_def
  |> SRULE [bind_type_name_check_subst,FUN_EQ_THM,st_ex_return_def];

Definition check_ctors_def:
  (check_ctors l tenvT [] = return ()) ∧
  (check_ctors l tenvT ((tvs,tn,ctors)::tds) =
    do
      check_dups l
                 (\n. concat [«Duplicate constructor »; n;
                              « in the definition of type »; tn])
                 (MAP FST ctors);
      check_dups l
                 (\n. concat [«Duplicate type variable binding »; n;
                              « in the definition of type »; tn])
                 tvs;
      check_ctor_types l tenvT tvs ctors;
      check_ctors l tenvT tds;
    od)
End

Theorem check_ctors_expand = check_ctors_def
  |> SRULE [check_dups_eq_find_dup,FUN_EQ_THM,st_ex_bind_def,st_ex_return_def];

Definition check_type_definition_def:
  check_type_definition l tenvT tds =
    do
      check_dups l
                 (\n. concat [«Duplicate type constructor »; n;
                              « in a mutually recursive type definition»])
                 (MAP (FST o SND) tds);
      check_ctors l tenvT tds;
    od
End

Theorem check_type_definition_expand = check_type_definition_def
  |> SRULE [check_dups_eq_find_dup,FUN_EQ_THM,st_ex_bind_def,st_ex_return_def];

Definition infer_p_def:
  (infer_p l ienv (Pvar n) =
    do t <- fresh_uvar;
       return (t, [(n,t)])
    od) ∧
  (infer_p l ienv Pany =
    do t <- fresh_uvar;
       return (t, [])
    od) ∧
  (infer_p l ienv (Plit (IntLit i)) =
    return (Infer_Tapp [] Tint_num, [])) ∧
  (infer_p l ienv (Plit (Char s)) =
    return (Infer_Tapp [] Tchar_num, [])) ∧
  (infer_p l ienv (Plit (StrLit s)) =
    return (Infer_Tapp [] Tstring_num, [])) ∧
  (infer_p l ienv (Plit (Word8 w)) =
    return (Infer_Tapp [] Tword8_num, [])) ∧
  (infer_p l ienv (Plit (Word64 w)) =
    return (Infer_Tapp [] Tword64_num, [])) ∧
  (infer_p l ienv (Plit (Float64 f)) =
    failwith l «Floats cannot be used in patterns» ) ∧
  (infer_p l ienv (Pcon cn_opt ps) =
    case cn_opt of
      | NONE =>
          do (ts,tenv) <- infer_ps l ienv ps;
             return (Infer_Tapp ts Ttup_num, tenv)
          od
      | SOME cn =>
          do (tvs',ts,tn) <- lookup_st_ex l «constructor» cn ienv.inf_c;
             (ts'',tenv) <- infer_ps l ienv ps;
             ts' <- n_fresh_uvar (LENGTH tvs');
             guard (LENGTH ts'' = LENGTH ts) l
                   (concat [«Constructor »; id_to_string cn; « given »;
                            toString (&LENGTH ts''); « arguments, but expected »;
                            toString (&LENGTH ts)]);
             () <- add_constraints l ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
             return (Infer_Tapp ts' tn, tenv)
          od) ∧
  (infer_p l ienv (Pref p) =
    do (t,tenv) <- infer_p l ienv p;
      return (Infer_Tapp [t] Tref_num, tenv)
    od) ∧
  (infer_p l ienv (Pas p v) =
    do (t,tenv) <- infer_p l ienv p;
      return (t, tenv++[(v,t)])
    od) ∧
  (infer_p l ienv (Ptannot p t) =
   do (t',tenv) <- infer_p l ienv p;
      t'' <- type_name_check_subst l
              (\tv. concat [«Type variable »; tv; « found in type annotation. »;
                            «Type variables are not supported in type annotations.»])
              ienv.inf_t [] t;
      () <- add_constraint l t' (infer_type_subst [] t'');
      return (t', tenv)
   od) ∧
  (infer_ps l ienv [] =
    return ([], [])) ∧
  (infer_ps l ienv (p::ps) =
    do (t, tenv) <- infer_p l ienv p;
       (ts, tenv') <- infer_ps l ienv ps;
       return (t::ts, tenv'++tenv)
    od)
End

Theorem option_case_rand:
  (case x of NONE => y | SOME a => f a) s =
  (case x of NONE => y s | SOME a => f a s)
Proof
  Cases_on ‘x’ \\ gvs []
QED

Theorem infer_p_expand = infer_p_def
  |> SRULE [check_dups_eq_find_dup,bind_guard,bind_type_name_check_subst]
  |> SRULE [st_ex_bind_triple]
  |> SRULE [st_ex_bind_pair]
  |> SRULE [st_ex_bind_def,FUN_EQ_THM,st_ex_return_def,
            failwith_def,option_case_rand];

Definition word_tc_def:
  (word_tc W8 = Tword8_num) ∧
  (word_tc W64 = Tword64_num)
End

Definition op_to_string_def:
  (op_to_string (Shift _ _ _) = («Shift», 1)) ∧
  (op_to_string Equality = («Equality», 2)) ∧
  (op_to_string (Arith a ty) =
     («Arith»,
      case supported_arith a ty of SOME n => (n:num) | NONE => 0n)) ∧
  (op_to_string (FromTo _ _) = («FromTo», 1)) ∧
  (op_to_string (Test _ _) = («Test», 2)) ∧
  (op_to_string Opapp = («Opapp», 2)) ∧
  (op_to_string Opassign = («Opassign», 2)) ∧
  (op_to_string Opref = («Opref», 1)) ∧
  (op_to_string Opderef = («Opderef», 1)) ∧
  (op_to_string Aw8alloc = («Aw8alloc», 2)) ∧
  (op_to_string Aw8sub = («Aw8sub», 2)) ∧
  (op_to_string Aw8length = («Aw8length», 1)) ∧
  (op_to_string Aw8update = («Aw8update», 3)) ∧
  (op_to_string Aw8sub_unsafe = («Aw8sub_unsafe», 2)) ∧
  (op_to_string Aw8update_unsafe = («Aw8update_unsafe», 3)) ∧
  (op_to_string XorAw8Str_unsafe = («XorAw8Str_unsafe», 2)) ∧
  (op_to_string CopyStrStr = («CopyStrStr», 3)) ∧
  (op_to_string CopyStrAw8 = («CopyStrAw8», 5)) ∧
  (op_to_string CopyAw8Str = («CopyAw8Str», 3)) ∧
  (op_to_string CopyAw8Aw8 = («CopyAw8Aw8», 5)) ∧
  (op_to_string Strsub = («Strsub», 2)) ∧
  (op_to_string Implode = («Implode», 1)) ∧
  (op_to_string Explode = («Explode», 1)) ∧
  (op_to_string Strlen = («Strlen», 1)) ∧
  (op_to_string Strcat = («Strcat», 1)) ∧
  (op_to_string VfromList = («VfromList», 1)) ∧
  (op_to_string Vsub = («Vsub», 2)) ∧
  (op_to_string Vsub_unsafe = («Vsub_unsafe», 2)) ∧
  (op_to_string Vlength = («Vlength», 1)) ∧
  (op_to_string Aalloc = («Aalloc», 2)) ∧
  (op_to_string AallocEmpty = («AallocEmpty», 1)) ∧
  (op_to_string AallocFixed = («AallocFixed», 1)) ∧
  (op_to_string Asub = («Asub», 2)) ∧
  (op_to_string Alength = («Alength», 1)) ∧
  (op_to_string Aupdate = («Aupdate», 3)) ∧
  (op_to_string Asub_unsafe = («Asub_unsafe», 2)) ∧
  (op_to_string Aupdate_unsafe = («Aupdate_unsafe», 3)) ∧
  (op_to_string ConfigGC = («ConfigGC», 2)) ∧
  (op_to_string Eval = («Eval», 6)) ∧
  (op_to_string Env_id = («Env_id», 1)) ∧
  (op_to_string ListAppend = («ListAppend», 2)) ∧
  (op_to_string (FFI _) = («FFI», 2)) ∧
  (op_to_string (ThunkOp ForceThunk) = («ForceThunk», 1)) ∧
  (op_to_string (ThunkOp (AllocThunk _)) = («AllocThunk», 1)) ∧
  (op_to_string (ThunkOp (UpdateThunk _)) = («UpdateThunk», 2))
End

Overload Tem[local,inferior] = ``Infer_Tapp []``

Definition t_num_of_def[simp]:
  t_num_of BoolT       = Tbool_num   ∧
  t_num_of IntT        = Tint_num    ∧
  t_num_of CharT       = Tchar_num   ∧
  t_num_of StrT        = Tstring_num ∧
  t_num_of (WordT W8)  = Tword8_num  ∧
  t_num_of (WordT W64) = Tword64_num ∧
  t_num_of Float64T    = Tdouble_num
End

Definition op_simple_constraints_def:
op_simple_constraints op =
  case op of
   | Arith a ty => (case supported_arith a ty of
                    | NONE => (F, [], Tem Tbool_num)
                    | SOME arity =>
                       (T, REPLICATE arity (Tem (t_num_of ty)), Tem (t_num_of ty)))
   | FromTo ty1 ty2 => (supported_conversion ty1 ty2,
                        [Tem (t_num_of ty1)],
                        Tem (t_num_of ty2))
   | Test test ty => (supported_test test ty,
                      [Tem (t_num_of ty); Tem (t_num_of ty)],
                      Tem Tbool_num)
   | Shift wz _ _ => (T, [Tem (word_tc wz)], Tem (word_tc wz))
   | Aw8alloc => (T, [Tem Tint_num; Tem Tword8_num], Tem Tword8array_num)
   | Aw8sub => (T, [Tem Tword8array_num; Tem Tint_num], Tem Tword8_num)
   | Aw8length => (T, [Tem Tword8array_num], Tem Tint_num)
   | Aw8update => (T, [Tem Tword8array_num; Tem Tint_num; Tem Tword8_num],
        Tem Ttup_num)
   | CopyStrStr => (T, [Tem Tstring_num; Tem Tint_num; Tem Tint_num],
        Tem Tstring_num)
   | CopyStrAw8 => (T, [Tem Tstring_num; Tem Tint_num; Tem Tint_num;
            Tem Tword8array_num; Tem Tint_num], Tem Ttup_num)
   | CopyAw8Str => (T, [Tem Tword8array_num; Tem Tint_num; Tem Tint_num],
        Tem Tstring_num)
   | CopyAw8Aw8 => (T, [Tem Tword8array_num; Tem Tint_num; Tem Tint_num;
            Tem Tword8array_num; Tem Tint_num], Tem Ttup_num)
   | Strsub => (T, [Tem Tstring_num; Tem Tint_num], Tem Tchar_num)
   | Strlen => (T, [Tem Tstring_num], Tem Tint_num)
   | ConfigGC => (T, [Tem Tint_num; Tem Tint_num], Tem Ttup_num)
   | FFI _ => (T, [Tem Tstring_num; Tem Tword8array_num], Tem Ttup_num)
   | Implode => (T, [Infer_Tapp [Infer_Tapp [] Tchar_num] Tlist_num],
        Tem Tstring_num)
   | Explode => (T, [Tem Tstring_num], Infer_Tapp [Tem Tchar_num] Tlist_num)
   | Strcat => (T, [Infer_Tapp [Tem Tstring_num] Tlist_num], Tem Tstring_num)
   | _ => (F, [], Tem Tbool_num)
End

Definition op_n_args_msg_def:
  op_n_args_msg op n =
    let (ops, args) = op_to_string op in
    concat [«Primitive »; ops; « given »;
        toString (& n); « arguments, but expects »;
        toString (& args)]
End

Definition constrain_op_def[nocompute]:
constrain_op l op ts s =
  let (simple, op_arg_ts, op_ret_t) = op_simple_constraints op in
  if simple then
    if LENGTH ts <> LENGTH op_arg_ts
    then failwith l (op_n_args_msg op (LENGTH ts)) s
    else do () <- add_constraints l ts (MAP I op_arg_ts);
      return op_ret_t
    od s
  else pmatch (op,ts) of
   | (Equality, [t1;t2]) =>
       do () <- add_constraint l t1 t2;
          return (Infer_Tapp [] Tbool_num)
       od s
   | (Opapp, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [t2;uvar] Tfn_num);
          return uvar
       od s
   | (Opassign, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [t2] Tref_num);
          return (Infer_Tapp [] Ttup_num)
       od s
   | (Opref, [t]) => return (Infer_Tapp [t] Tref_num) s
   | (Opderef, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] Tref_num);
          return uvar
       od s
   | (VfromList, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] Tlist_num);
          return (Infer_Tapp [uvar] Tvector_num)
       od s
   | (Vsub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [uvar] Tvector_num);
          () <- add_constraint l t2 (Infer_Tapp [] Tint_num);
          return uvar
       od s
   | (Vlength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] Tvector_num);
          return (Infer_Tapp [] Tint_num)
       od s
   | (Aalloc, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] Tint_num);
          return (Infer_Tapp [t2] Tarray_num)
       od s
   | (AallocEmpty, [t1]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [] Ttup_num);
          return (Infer_Tapp [uvar] Tarray_num)
       od s
   | (Asub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [uvar] Tarray_num);
          () <- add_constraint l t2 (Infer_Tapp [] Tint_num);
          return uvar
       od s
   | (Alength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] Tarray_num);
          return (Infer_Tapp [] Tint_num)
       od s
   | (Aupdate, [t1;t2;t3]) =>
       do () <- add_constraint l t1 (Infer_Tapp [t3] Tarray_num);
          () <- add_constraint l t2 (Infer_Tapp [] Tint_num);
          return (Infer_Tapp [] Ttup_num)
       od s
   | (ListAppend, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [uvar] Tlist_num);
          () <- add_constraint l t2 (Infer_Tapp [uvar] Tlist_num);
          return (Infer_Tapp [uvar] Tlist_num)
       od s
   | (Vsub_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (Asub_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (Aupdate_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (Aw8sub_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (Aw8update_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (XorAw8Str_unsafe, _) => failwith l («Unsafe ops do not have a type») s
   | (AallocFixed, _) => failwith l («Unsafe ops do not have a type»)  s(* not actually unsafe *)
   | (Eval, _) => failwith l («Unsafe ops do not have a type») s
   | (Env_id, _) => failwith l («Unsafe ops do not have a type») s
   | (ThunkOp _, _) => failwith l («Thunk ops do not have a type») s
   | (Arith _ _, _) => failwith l («Type mismatch») s
   | (FromTo _ _, _) => failwith l («Type mismatch») s
   | (Test _ _, _) => failwith l («Type mismatch») s
   | _ => failwith l (op_n_args_msg op (LENGTH ts)) s
End

Theorem constrain_op_case_def[compute] = CONV_RULE
  (TOP_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) constrain_op_def;

Theorem constrain_op_expand = constrain_op_case_def
  |> SRULE [st_ex_bind_def,st_ex_return_def];

Theorem st_ex_bind_failure:
  st_ex_bind f g s = (Failure r, s') <=>
  (f s = (Failure r, s') \/
    (?x st. f s = (Success x, st) /\ g x st = (Failure r, s')))
Proof
  simp [st_ex_bind_def]
  \\ every_case_tac
QED

Theorem constrain_op_error_msg_sanity:
  ∀l op args s l' s' msg.
    LENGTH args = SND (op_to_string op) ∧
    constrain_op l op args s = (Failure (l',msg), s')
    ⇒
    IS_PREFIX (explode msg) "Type mismatch" ∨
    IS_PREFIX (explode msg) "Unsafe" ∨
    IS_PREFIX (explode msg) "Thunk"
Proof
  rpt strip_tac >>
  qmatch_abbrev_tac `IS_PREFIX _ m1 \/ IS_PREFIX _ m2 \/ IS_PREFIX _ m3` >>
  Cases_on ‘∃a ty. op = Arith a ty’ >-
   (gvs []
    \\ fs [constrain_op_def]
    \\ pairarg_tac \\ fs []
    \\ gvs [op_to_string_def]
    \\ gvs [AllCaseEqs(),op_simple_constraints_def,op_to_string_def]
    \\ gvs [failwith_def, st_ex_bind_failure, st_ex_return_def]
    \\ Cases_on ‘ty’ \\ gvs[supported_arith_def] \\ TRY (Cases_on ‘a:arith’)
    \\ gvs [supported_arith_def, LENGTH_EQ_NUM_compute,
            add_constraints_def, add_constraint_def,
            st_ex_bind_failure, st_ex_return_def, option_case_eq]
    \\ unabbrev_all_tac \\ fs [mlstringTheory.concat_thm]) >>
  cases_on `op` >>
  fs [op_to_string_def, constrain_op_case_def, op_simple_constraints_def] >>
  gvs [LENGTH_EQ_NUM_compute] >>
  rfs [] >>
  fs [add_constraints_def, add_constraint_def, fresh_uvar_def,
      st_ex_bind_failure, st_ex_return_def, option_case_eq] >>
  rw [] >>
  fs [mlstringTheory.concat_thm] >>
  fs [failwith_def] >> rw [] >> fs [] >>
  unabbrev_all_tac >> fs [] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> gvs [] >>
  fs [add_constraints_def, add_constraint_def, fresh_uvar_def,
      st_ex_bind_failure, st_ex_return_def, option_case_eq] >>
  fs [mlstringTheory.concat_thm] >>
  fs [failwith_def] >> rw [] >> fs [] >>
  unabbrev_all_tac >> fs []
QED

Definition infer_e_def:
  (infer_e l ienv (Raise e) =
    do t2 <- infer_e l ienv e;
       () <- add_constraint l t2 (Infer_Tapp [] Texn_num);
       t1 <- fresh_uvar;
       return t1
    od) ∧
  (infer_e l ienv (Handle e pes) =
    if pes = [] then
      failwith l («No patterns in handle»)
    else
      do t1 <- infer_e l ienv e;
         () <- infer_pes l ienv pes (Infer_Tapp [] Texn_num) t1;
         return t1
      od) ∧
  (infer_e l ienv (Lit (IntLit i)) =
    return (Infer_Tapp [] Tint_num)) ∧
  (infer_e l ienv (Lit (Char c)) =
    return (Infer_Tapp [] Tchar_num)) ∧
  (infer_e l ienv (Lit (StrLit s)) =
    return (Infer_Tapp [] Tstring_num)) ∧
  (infer_e l ienv (Lit (Word8 w)) =
    return (Infer_Tapp [] Tword8_num)) ∧
  (infer_e l ienv (Lit (Word64 _)) =
    return (Infer_Tapp [] Tword64_num)) ∧
  (infer_e l ienv (Lit (Float64 _)) =
    return (Infer_Tapp [] Tdouble_num)) ∧
  (infer_e l ienv (Var id) =
    do (tvs,t) <- lookup_st_ex l «variable» id ienv.inf_v;
       uvs <- n_fresh_uvar tvs;
       return (infer_deBruijn_subst uvs t)
    od) ∧
  (infer_e l ienv (Con cn_opt es) =
    case cn_opt of
        NONE =>
         do ts <- infer_es l ienv es;
            return (Infer_Tapp ts Ttup_num)
         od
      | SOME cn =>
         do (tvs',ts,tn) <- lookup_st_ex l «constructor» cn ienv.inf_c;
            ts'' <- infer_es l ienv es;
            ts' <- n_fresh_uvar (LENGTH tvs');
             guard (LENGTH ts'' = LENGTH ts) l
                   (concat [«Constructor »; id_to_string cn; « given »;
                            toString (&LENGTH ts''); « arguments, but expected »;
                            toString (&LENGTH ts)]);
            () <- add_constraints l ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
            return (Infer_Tapp ts' tn)
         od) ∧
  (infer_e l ienv (Fun x e) =
    do t1 <- fresh_uvar;
       t2 <- infer_e l (ienv with inf_v := nsBind x (0,t1) ienv.inf_v) e;
       return (Infer_Tapp [t1;t2] Tfn_num)
    od) ∧
  (infer_e l ienv (App op es) =
    do ts <- infer_es l ienv es;
       t <- constrain_op l op ts;
       return t
    od) ∧
  (infer_e l ienv (Log log e1 e2) =
    do t1 <- infer_e l ienv e1;
       t2 <- infer_e l ienv e2;
       () <- add_constraint l t1 (Infer_Tapp [] Tbool_num);
       () <- add_constraint l t2 (Infer_Tapp [] Tbool_num);
       return (Infer_Tapp [] Tbool_num)
    od) ∧
  (infer_e l ienv (If e1 e2 e3) =
    do t1 <- infer_e l ienv e1;
       () <- add_constraint l t1 (Infer_Tapp [] Tbool_num);
       t2 <- infer_e l ienv e2;
       t3 <- infer_e l ienv e3;
       () <- add_constraint l t2 t3;
       return t2
    od) ∧
  (infer_e l ienv (Mat e pes) =
    if pes = [] then
      failwith l («No patterns in case»)
    else
      do t1 <- infer_e l ienv e;
         t2 <- fresh_uvar;
         () <- infer_pes l ienv pes t1 t2;
         return t2
    od) ∧
  (infer_e l ienv (Let x e1 e2) =
  (* Don't do polymorphism for non-top-level lets
    if is_value e1 then
      do n <- get_next_uvar;
         t1 <- infer_e l ienv e1;
         t1' <- apply_subst t1;
         (num_gen,s,t1'') <- return (generalise n 0 FEMPTY t1');
         t2 <- infer_e l (ienv with inf_v:=(bind x (num_gen,t1'') ienv.inf_v)) e2;
         return t2
      od
    else
      *)
      do t1 <- infer_e l ienv e1;
         t2 <- infer_e l (ienv with inf_v := nsOptBind x (0,t1) ienv.inf_v) e2;
         return t2
      od) ∧
  (* Don't do polymorphism for non-top-level let recs
  (infer_e l ienv (Letrec funs e) =
    do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name variable";
       next <- get_next_uvar;
       uvars <- n_fresh_uvar (LENGTH funs);
       env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
       funs_ts <- infer_funs l (ienv with inf_v := env') funs;
       () <- add_constraints l uvars funs_ts;
       ts <- apply_subst_list uvars;
       (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
       env'' <- return (merge (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts') env);
       t <- infer_e l (ienv with inf_v := env'') e;
       return t
    od) ∧
    *)
  (infer_e l ienv (Letrec funs e) =
    do
      check_dups l (\n. concat [«Duplicate function name »; n;
                                « in mutually recursive function definition»])
                   (MAP FST funs);
       uvars <- n_fresh_uvar (LENGTH funs);
       env' <- return (nsAppend (alist_to_ns (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) ienv.inf_v);
       funs_ts <- infer_funs l (ienv with inf_v:=env') funs;
       () <- add_constraints l uvars funs_ts;
       t <- infer_e l (ienv with inf_v:=env') e;
       return t
    od) ∧
  (infer_e l ienv (Tannot e t) =
    do t' <- infer_e l ienv e ;
       t'' <- type_name_check_subst l
              (\tv. concat [«Type variable »; tv; « found in type annotation. »;
                            «Type variables are not supported in type annotations.»])
              ienv.inf_t [] t;
       () <- add_constraint l t' (infer_type_subst [] t'');
       return t'
     od) ∧
  (infer_e l ienv (Lannot e new_l) =
    infer_e (l with loc := SOME new_l) ienv e) ∧
  (infer_es l ienv [] =
    return []) ∧
  (infer_es l ienv (e::es) =
    do t <- infer_e l ienv e;
       ts <- infer_es l ienv es;
       return (t::ts)
    od) ∧
  (infer_pes l ienv [] t1 t2 =
     return ()) ∧
  (infer_pes l ienv ((p,e)::pes) t1 t2 =
    do (t1', env') <- infer_p l ienv p;
      check_dups l (\n. concat [«Duplicate variable »; n; « in pattern»])
                (MAP FST env');
       () <- add_constraint l t1 t1' ;
       t2' <- infer_e l (ienv with inf_v := nsAppend (alist_to_ns (MAP (\(n,t). (n,(0,t))) env')) ienv.inf_v) e;
       () <- add_constraint l t2 t2';
       () <- infer_pes l ienv pes t1 t2;
       return ()
    od) ∧
  (infer_funs l ienv [] = return []) ∧
  (infer_funs l ienv ((f, x, e)::funs) =
    do uvar <- fresh_uvar;
       t <- infer_e l (ienv with inf_v := nsBind x (0,uvar) ienv.inf_v) e;
       ts <- infer_funs l ienv funs;
       return (Infer_Tapp [uvar;t] Tfn_num::ts)
    od)
Termination
  WF_REL_TAC ‘measure (\x. case x of
  | INL (_,_,e) => exp_size e
  | INR (INL (_,_,es)) => list_size exp_size es
  | INR (INR (INL (_,_,pes,_,_))) => list_size (pair_size pat_size exp_size) pes
  | INR (INR (INR (_,_,funs))) =>
    list_size (pair_size mlstring_size
         (pair_size mlstring_size exp_size)) funs)’ >>
  rw []
End

Theorem FUN_EQ_THM_state[local]:
  f = g ⇔ ∀s. f s = g s
Proof
  gvs [FUN_EQ_THM]
QED

Theorem infer_e_expand = infer_e_def
  |> SRULE [check_dups_eq_find_dup,bind_guard,bind_type_name_check_subst]
  |> SRULE [st_ex_bind_triple]
  |> SRULE [st_ex_bind_pair]
  |> SRULE [st_ex_bind_def,FUN_EQ_THM_state,st_ex_return_def,
            failwith_def,option_case_rand,COND_RATOR];

Definition extend_dec_ienv_def:
  extend_dec_ienv ienv' ienv =
     <| inf_v := nsAppend ienv'.inf_v ienv.inf_v;
        inf_c := nsAppend ienv'.inf_c ienv.inf_c;
        inf_t := nsAppend ienv'.inf_t ienv.inf_t |>
End

Definition lift_ienv_def:
  lift_ienv mn ienv =
    <| inf_v := nsLift mn ienv.inf_v;
       inf_c := nsLift mn ienv.inf_c;
       inf_t := nsLift mn ienv.inf_t |>
End

Definition infer_d_def:
(infer_d ienv (Dlet locs p e) =
  do () <- init_state;
     n <- get_next_uvar;
     t1 <- infer_e <| loc := SOME locs; err := ienv.inf_t |> ienv e;
     (t2,env') <- infer_p <| loc := SOME locs; err := ienv.inf_t |> ienv p;
     check_dups <| loc := SOME locs; err := ienv.inf_t |>
                   (\n. concat [«Duplicate variable »; n;
                                « in the left-hand side of a definition»])
                (MAP FST env');
     () <- add_constraint <| loc := SOME locs; err := ienv.inf_t |> t1 t2;
     ts <- apply_subst_list (MAP SND env');
     (num_tvs, s, ts') <- return (generalise_list n 0 FEMPTY ts);
     () <- guard (num_tvs = 0 ∨ is_value e) <| loc := SOME locs; err := ienv.inf_t |>
                 («Value restriction violated»);
     return <| inf_v := alist_to_ns (ZIP (MAP FST env', MAP (\t. (num_tvs, t)) ts'));
               inf_c := nsEmpty;
               inf_t := nsEmpty |>
  od) ∧
(infer_d ienv (Dletrec locs funs) =
  do
    check_dups <| loc := SOME locs; err := ienv.inf_t |>
       (\n. concat [«Duplicate function name »; n;
            « a mutually recursive function definition»])
               (MAP FST funs);
     () <- init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (nsAppend (alist_to_ns (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) ienv.inf_v);
     funs_ts <- infer_funs <| loc := SOME locs; err := ienv.inf_t |>
                           (ienv with inf_v:= env') funs;
     () <- add_constraints <| loc := SOME locs; err := ienv.inf_t |> uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     return <| inf_v := alist_to_ns (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts');
               inf_c := nsEmpty;
               inf_t := nsEmpty |>
  od) ∧
(infer_d ienv (Dtype locs tdefs) =
  do
     tids <- n_fresh_id (LENGTH tdefs);
     ienvT1 <- return (alist_to_ns (MAP2 (\ (tvs,tn,ctors) i . (tn, (tvs, Tapp (MAP Tvar tvs) i))) tdefs tids));
     ienvT2 <- return (nsAppend ienvT1 ienv.inf_t);
     check_type_definition <| loc := SOME locs; err := ienv.inf_t |> ienvT2 tdefs;
     return <| inf_v := nsEmpty;
               inf_c := build_ctor_tenv ienvT2 tdefs tids;
               inf_t := ienvT1 |>
  od) ∧
(infer_d ienv (Dtabbrev locs tvs tn t) =
  do
    check_dups <| loc := SOME locs; err := ienv.inf_t |>
       (\n. concat [«Duplicate type variable bindings for »;
                    n; « in type abbreviation »;
                    tn])
              tvs;
     t' <- type_name_check_subst <| loc := SOME locs; err := ienv.inf_t |>
            (\tv. concat [«Unbound type variable »; tv; « in type abbreviation »; tn])
            ienv.inf_t tvs t;
     return <| inf_v := nsEmpty;
               inf_c := nsEmpty;
               inf_t := nsSing tn (tvs,t') |>
  od) ∧
(infer_d ienv (Dexn locs cn ts) =
  do
    ts' <- type_name_check_subst_list <| loc := SOME locs; err := ienv.inf_t |>
            (\tv. concat [«Type variable »; tv; « found in declaration of exception »; cn;
                          «. Type variables are not allowed in exception declarations.»])
            ienv.inf_t [] ts;
    return <| inf_v := nsEmpty;
              inf_c := nsSing cn ([], ts', Texn_num);
              inf_t := nsEmpty |>
  od) ∧
(infer_d ienv (Denv n) =
  failwith <| loc := NONE; err := ienv.inf_t |>
    («Env declaration (Denv) is not supported.»)) ∧
(infer_d ienv (Dmod mn ds) =
  do ienv' <- infer_ds ienv ds;
     return (lift_ienv mn ienv')
  od) ∧
(infer_d ienv (Dlocal lds ds) =
  do ienv' <- infer_ds ienv lds;
    infer_ds (extend_dec_ienv ienv' ienv) ds
  od) ∧
(infer_ds ienv [] =
  return <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>) ∧
(infer_ds ienv (d::ds) =
  do
    ienv' <- infer_d ienv d;
    ienv'' <- infer_ds (extend_dec_ienv ienv' ienv) ds;
    return (extend_dec_ienv ienv'' ienv')
  od)
End

Theorem infer_d_expand = infer_d_def
  |> SRULE [check_dups_eq_find_dup,bind_guard,bind_type_name_check_subst]
  |> SRULE [st_ex_bind_triple]
  |> SRULE [st_ex_bind_pair]
  |> SRULE [st_ex_bind_def,FUN_EQ_THM,st_ex_return_def,
            failwith_def,option_case_rand];

(* The starting Id should be greater than Tlist_num :: (Tbool_num :: prim_type_nums) *)
Definition start_type_id_def:
  start_type_id =
    ^(EVAL``(FOLDR MAX 0 (Tlist_num :: (Tbool_num :: prim_type_nums)))+1`` |> rconc)
End

Definition infertype_prog_def:
  infertype_prog ienv prog =
    case FST (infer_ds ienv prog (init_infer_state <| next_uvar := 0; subst := FEMPTY; next_id := start_type_id |>)) of
    | Success new_ienv => Success (extend_dec_ienv new_ienv ienv)
    | Failure x => Failure x
End

Definition infertype_prog_inc_def:
  infertype_prog_inc (ienv, next_id) prog =
  case infer_ds ienv prog (init_infer_state <| next_id := next_id |>) of
    (Success new_ienv, st) =>
    (Success (extend_dec_ienv new_ienv ienv, st.next_id))
  | (Failure x, _) => Failure x
End

Definition init_config_def:
  init_config : inf_env =
    <| inf_c := primTypes$prim_tenv.c;
       inf_v := nsEmpty;
       inf_t := primTypes$prim_tenv.t|>
End

(* The following aren't needed to run the inferencer, but are useful in the proofs
 * about it *)

Definition infer_deBruijn_inc_def:
  (infer_deBruijn_inc n (Infer_Tvar_db m) =
    Infer_Tvar_db (m + n)) ∧
  (infer_deBruijn_inc n (Infer_Tapp ts tn) =
    Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) ∧
  (infer_deBruijn_inc n (Infer_Tuvar m) =
    Infer_Tuvar m)
End

Definition infer_subst_def:
  (infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n) ∧
  (infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst s) ts) tc) ∧
  (infer_subst s (Infer_Tuvar n) =
    case FLOOKUP s n of
        NONE => Infer_Tuvar n
      | SOME m => Infer_Tvar_db m)
End

Definition pure_add_constraints_def:
(pure_add_constraints s [] s' = (s = s')) ∧
(pure_add_constraints s1 ((t1,t2)::rest) s' =
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s')
End

Definition check_t_def:
  (check_t n uvars (Infer_Tuvar v) = (v ∈ uvars)) ∧
  (check_t n uvars (Infer_Tvar_db n') =
    (n' < n)) ∧
  (check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars) ts)
End

Definition ienv_val_ok_def:
ienv_val_ok uvars env =
  nsAll (\x (tvs,t). check_t tvs uvars t) env
End

Definition check_s_def:
check_s tvs uvs s =
  !uv. uv ∈ FDOM s ⇒ check_t tvs uvs (s ' uv)
End

(* Adding the constraints extra_constraints moves the constraint set from s1 to
 * s2, and s2 is required to be complete in that it assigns to (at least) all
 * the uvars ≤ next_uvar, and when we apply it to any uvar, we get back a type
 * without any uvars in it. *)
Definition sub_completion_def:
sub_completion tvs next_uvar s1 extra_constraints s2 =
  (pure_add_constraints s1 extra_constraints s2 ∧
   (count next_uvar SUBSET FDOM s2) ∧
   (!uv. uv ∈ FDOM s2 ⇒ check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv))))
End

(* printing of types *)

Definition alist_nub_def:
  alist_nub [] = [] /\
  alist_nub ((x,y)::xs) = (x,y) :: alist_nub (FILTER (\t. x <> FST t) xs)
Termination
  WF_REL_TAC `measure LENGTH` \\ fs [LESS_EQ,LENGTH_FILTER_LEQ]
End

Definition ns_nub_def:
  ns_nub (Bind xs ys) = Bind (alist_nub xs) (alist_nub (inner_ns_nubs ys)) ∧
  inner_ns_nubs [] = [] ∧
  inner_ns_nubs ((x,y)::tl) = (x, ns_nub y)::inner_ns_nubs tl
End

Definition ns_to_alist_def:
  (ns_to_alist (Bind [] []) = []) /\
  (ns_to_alist (Bind [] ((n,x)::ms)) =
    MAP (\(x,y). (n ^ «.» ^ x,y)) (ns_to_alist x) ++
    ns_to_alist (Bind [] ms)) /\
  (ns_to_alist (Bind ((s,x)::xs) m) = (s,x) :: ns_to_alist (Bind xs m))
End

Definition inf_env_to_types_string_def:
  inf_env_to_types_string s =
    let l = ns_to_alist (ns_nub s.inf_v) in
    let xs = MAP (\(n,_,t). concat [n; «: »;
                                    inf_type_to_string s.inf_t t;
                                    «\n»;]) l in
      (* sort mlstring_le *) REVERSE xs
End
