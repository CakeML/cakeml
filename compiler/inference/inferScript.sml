open preamble miscTheory astTheory namespaceTheory typeSystemTheory;
open namespacePropsTheory;
open infer_tTheory unifyTheory;
open stringTheory ;
open primTypesTheory;


val _ = new_theory "infer";
val _ = monadsyntax.temp_add_monadsyntax()
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(*  The inferencer uses a state monad internally to keep track of unifications at the expressions level *)

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Datatype `
  exc = Success 'a | Failure 'b`;

val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val st_ex_bind_def = Define `
(st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    dtcase x s of
      (Success y,s) => f y s
    | (Failure x,s) => (Failure x,s)`;

val st_ex_return_def = Define `
(st_ex_return (*: α -> (β, α, γ) M*)) x =
  λs. (Success x, s)`;

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val failwith_def = Define `
(failwith : locs option -> α -> (β, γ, (locs option # α)) M) l msg = (\s. (Failure (l, msg), s))`;

val guard_def = Define `
guard P l msg = if P then return () else failwith l msg`;

val read_def = Define `
(read : (α, α, β) M) =
  \s. (Success s, s)`;

val write_def = Define `
(write : α -> (α, unit, β) M) v =
  \s. (Success (), v)`;

val lookup_st_ex_def = Define `
  lookup_st_ex l id ienv st =
    dtcase nsLookup ienv id of
    | NONE => (Failure (l, concat [implode "Undefined variable: "; id_to_string id]), st)
    | SOME v => (Success v, st)`;

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
add_constraint (l : locs option) t1 t2 =
  \st.
    dtcase t_unify st.subst t1 t2 of
      | NONE =>
          (Failure (l, concat [implode "Type mismatch between ";
                               inf_type_to_string (t_walkstar st.subst t1);
                               implode " and ";
                               inf_type_to_string (t_walkstar st.subst t2)]), st)
      | SOME s =>
          (Success (), st with <| subst := s |>)`;

val add_constraints_def = Define `
(add_constraints l [] [] =
  return ()) ∧
(add_constraints l (t1::ts1) (t2::ts2) =
  do () <- add_constraint l t1 t2;
     () <- add_constraints l ts1 ts2;
     return ()
  od) ∧
(add_constraints l _ _ =
  failwith l (implode "Internal error: Bad call to add_constraints"))`;

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
 inf_env =
  <| inf_v : (modN, varN, num # infer_t) namespace
   ; inf_c : tenv_ctor
   ; inf_t : tenv_abbrev
   |>`;

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised, the generalised type, and a substitution
 * that describes the generalisation *)
val generalise_def = Define `
(generalise m n s (Infer_Tapp ts tc) =
  let (num_gen, s', ts') = generalise_list m n s ts in
    (num_gen, s', Infer_Tapp ts' tc)) ∧
(generalise m n s (Infer_Tuvar uv) =
  dtcase FLOOKUP s uv of
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
  dtcase ALOOKUP s tv of
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

val infer_p_def = tDefine "infer_p" `
(infer_p l ienv (Pvar n) =
  do t <- fresh_uvar;
     return (t, [(n,t)])
  od) ∧
(infer_p l ienv Pany =
  do t <- fresh_uvar;
     return (t, [])
  od) ∧
(infer_p l ienv (Plit (IntLit i)) =
  return (Infer_Tapp [] TC_int, [])) ∧
(infer_p l ienv (Plit (Char s)) =
  return (Infer_Tapp [] TC_char, [])) ∧
(infer_p l ienv (Plit (StrLit s)) =
  return (Infer_Tapp [] TC_string, [])) ∧
(infer_p l ienv (Plit (Word8 w)) =
  return (Infer_Tapp [] TC_word8, [])) ∧
(infer_p l ienv (Plit (Word64 w)) =
  return (Infer_Tapp [] TC_word64, [])) ∧
(infer_p l ienv (Pcon cn_opt ps) =
  dtcase cn_opt of
    | NONE =>
        do (ts,tenv) <- infer_ps l ienv ps;
           return (Infer_Tapp ts TC_tup, tenv)
        od
    | SOME cn =>
        do (tvs',ts,tn) <- lookup_st_ex l cn ienv.inf_c;
           (ts'',tenv) <- infer_ps l ienv ps;
           ts' <- n_fresh_uvar (LENGTH tvs');
           guard (LENGTH ts'' = LENGTH ts) l
                 (concat [implode "Constructor "; id_to_string cn; implode " given ";
                          toString (&LENGTH ts''); implode " arguments, but expected ";
                          toString (&LENGTH ts)]);
           () <- add_constraints l ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
           return (Infer_Tapp ts' (tid_exn_to_tc tn), tenv)
        od) ∧
(infer_p l ienv (Pref p) =
  do (t,tenv) <- infer_p l ienv p;
    return (Infer_Tapp [t] TC_ref, tenv)
  od) ∧
(infer_p l ienv (Ptannot p t) =
 do (t',tenv) <- infer_p l ienv p;
    () <- guard (check_freevars 0 [] t ∧ check_type_names ienv.inf_t t) l (implode "Bad type annotation");
    () <- add_constraint l t' (infer_type_subst [] (type_name_subst ienv.inf_t t));
    return (t', tenv)
 od) ∧
(infer_ps l ienv [] =
  return ([], [])) ∧
(infer_ps l ienv (p::ps) =
  do (t, tenv) <- infer_p l ienv p;
     (ts, tenv') <- infer_ps l ienv ps;
     return (t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. dtcase x of INL (_,_,p) => pat_size p
                                  | INR (_,_,ps) => pat1_size ps)` >>
 rw []);

val infer_p_ind = fetch "-" "infer_p_ind";

val constrain_op_quotation = `
constrain_op l op ts =
  dtcase (op,ts) of
   | (Opn opn, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_int);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_int)
       od
   | (Opb opb, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_int);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Opw wz opw, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] (TC_word wz));
          () <- add_constraint l t2 (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] (TC_word wz))
       od
   | (FP_bop bop, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] (TC_word W64));
          () <- add_constraint l t2 (Infer_Tapp [] (TC_word W64));
          return (Infer_Tapp [] (TC_word W64))
       od
   | (FP_uop uop, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] (TC_word W64));
          return (Infer_Tapp [] (TC_word W64))
       od
   | (FP_cmp cmp, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] (TC_word W64));
          () <- add_constraint l t2 (Infer_Tapp [] (TC_word W64));
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Shift wz sh n, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] (TC_word wz))
       od
   | (Equality, [t1;t2]) =>
       do () <- add_constraint l t1 t2;
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Opapp, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [t2;uvar] TC_fn);
          return uvar
       od
   | (Opassign, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [t2] TC_ref);
          return (Infer_Tapp [] TC_tup)
       od
   | (Opref, [t]) => return (Infer_Tapp [t] TC_ref)
   | (Opderef, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] TC_ref);
          return uvar
       od
    | (Aw8alloc, [t1;t2]) =>
        do () <- add_constraint l t1 (Infer_Tapp [] TC_int);
           () <- add_constraint l t2 (Infer_Tapp [] TC_word8);
           return (Infer_Tapp [] TC_word8array)
        od
    | (Aw8sub, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_word8array);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_word8)
        od
    | (Aw8length, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] TC_word8array);
          return (Infer_Tapp [] TC_int)
        od
    | (Aw8update, [t1;t2;t3]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_word8array);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          () <- add_constraint l t3 (Infer_Tapp [] TC_word8);
          return (Infer_Tapp [] TC_tup)
        od
   | (WordFromInt wz, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] (TC_word wz))
       od
   | (WordToInt wz, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] (TC_word wz));
          return (Infer_Tapp [] TC_int)
       od
   | (CopyStrStr, [t1;t2;t3]) =>
       do
         () <- add_constraint l t1 (Infer_Tapp [] TC_string);
         () <- add_constraint l t2 (Infer_Tapp [] TC_int);
         () <- add_constraint l t3 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_string)
        od
   | (CopyStrAw8, [t1;t2;t3;t4;t5]) =>
       do
         () <- add_constraint l t1 (Infer_Tapp [] TC_string);
         () <- add_constraint l t2 (Infer_Tapp [] TC_int);
         () <- add_constraint l t3 (Infer_Tapp [] TC_int);
         () <- add_constraint l t4 (Infer_Tapp [] TC_word8array);
         () <- add_constraint l t5 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_tup)
        od
   | (CopyAw8Str, [t1;t2;t3]) =>
       do
         () <- add_constraint l t1 (Infer_Tapp [] TC_word8array);
         () <- add_constraint l t2 (Infer_Tapp [] TC_int);
         () <- add_constraint l t3 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_string)
        od
   | (CopyAw8Aw8, [t1;t2;t3;t4;t5]) =>
       do
         () <- add_constraint l t1 (Infer_Tapp [] TC_word8array);
         () <- add_constraint l t2 (Infer_Tapp [] TC_int);
         () <- add_constraint l t3 (Infer_Tapp [] TC_int);
         () <- add_constraint l t4 (Infer_Tapp [] TC_word8array);
         () <- add_constraint l t5 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_tup)
        od
   | (Chr, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_char)
       od
   | (Ord, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] TC_char);
          return (Infer_Tapp [] TC_int)
       od
   | (Chopb opb, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_char);
          () <- add_constraint l t2 (Infer_Tapp [] TC_char);
          return (Infer_Tapp [] (TC_name (Short "bool")))
       od
   | (Strsub, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_string);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_char)
       od
   | (Implode, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short "list")));
          return (Infer_Tapp [] TC_string)
       od
   | (Strlen, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [] TC_string);
          return (Infer_Tapp [] TC_int)
       od
   | (Strcat, [t]) =>
       do () <- add_constraint l t (Infer_Tapp [Infer_Tapp [] TC_string] (TC_name (Short "list")));
          return (Infer_Tapp [] TC_string)
        od
   | (VfromList, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] (TC_name (Short "list")));
          return (Infer_Tapp [uvar] TC_vector)
       od
   | (Vsub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [uvar] TC_vector);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return uvar
       od
   | (Vlength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] TC_vector);
          return (Infer_Tapp [] TC_int)
       od
   | (Aalloc, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [t2] TC_array)
       od
   | (AallocEmpty, [t1]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [] TC_tup);
          return (Infer_Tapp [uvar] TC_array)
       od
   | (Asub, [t1;t2]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t1 (Infer_Tapp [uvar] TC_array);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return uvar
       od
   | (Alength, [t]) =>
       do uvar <- fresh_uvar;
          () <- add_constraint l t (Infer_Tapp [uvar] TC_array);
          return (Infer_Tapp [] TC_int)
       od
   | (Aupdate, [t1;t2;t3]) =>
       do () <- add_constraint l t1 (Infer_Tapp [t3] TC_array);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_tup)
       od
   | (ConfigGC, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_int);
          () <- add_constraint l t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_tup)
       od
   | (FFI n, [t1;t2]) =>
       do () <- add_constraint l t1 (Infer_Tapp [] TC_string);
          () <- add_constraint l t2 (Infer_Tapp [] TC_word8array);
          return (Infer_Tapp [] TC_tup)
       od
   | _ => failwith l (implode "Wrong number of arguments to primitive")`;

val constrain_op_def = Define constrain_op_quotation

val constrain_op_pmatch = Q.store_thm("constrain_op_pmatch",`∀op ts.` @
  (constrain_op_quotation |>
   map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
       | aq => aq)),
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[constrain_op_def])

val infer_e_def = tDefine "infer_e" `
(infer_e l ienv (Raise e) =
  do t2 <- infer_e l ienv e;
     () <- add_constraint l t2 (Infer_Tapp [] TC_exn);
     t1 <- fresh_uvar;
     return t1
  od) ∧
(infer_e l ienv (Handle e pes) =
  if pes = [] then
    failwith l (implode "Empty pattern match")
  else
    do t1 <- infer_e l ienv e;
       () <- infer_pes l ienv pes (Infer_Tapp [] TC_exn) t1;
       return t1
    od) ∧
(infer_e l ienv (Lit (IntLit i)) =
  return (Infer_Tapp [] TC_int)) ∧
(infer_e l ienv (Lit (Char c)) =
  return (Infer_Tapp [] TC_char)) ∧
(infer_e l ienv (Lit (StrLit s)) =
  return (Infer_Tapp [] TC_string)) ∧
(infer_e l ienv (Lit (Word8 w)) =
  return (Infer_Tapp [] TC_word8)) ∧
(infer_e l ienv (Lit (Word64 w)) =
  return (Infer_Tapp [] TC_word64)) ∧
(infer_e l ienv (Var id) =
  do (tvs,t) <- lookup_st_ex l id ienv.inf_v;
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e l ienv (Con cn_opt es) =
  dtcase cn_opt of
      NONE =>
       do ts <- infer_es l ienv es;
          return (Infer_Tapp ts TC_tup)
       od
    | SOME cn =>
       do (tvs',ts,tn) <- lookup_st_ex l cn ienv.inf_c;
          ts'' <- infer_es l ienv es;
          ts' <- n_fresh_uvar (LENGTH tvs');
           guard (LENGTH ts'' = LENGTH ts) l
                 (concat [implode "Constructor "; id_to_string cn; implode " given ";
                          toString (&LENGTH ts''); implode " arguments, but expected ";
                          toString (&LENGTH ts)]);
          () <- add_constraints l ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
          return (Infer_Tapp ts' (tid_exn_to_tc tn))
       od) ∧
(infer_e l ienv (Fun x e) =
  do t1 <- fresh_uvar;
     t2 <- infer_e l (ienv with inf_v := nsBind x (0,t1) ienv.inf_v) e;
     return (Infer_Tapp [t1;t2] TC_fn)
  od) ∧
(infer_e l ienv (App op es) =
  do ts <- infer_es l ienv es;
     t <- constrain_op l op ts;
     return t
  od) ∧
(infer_e l ienv (Log log e1 e2) =
  do t1 <- infer_e l ienv e1;
     t2 <- infer_e l ienv e2;
     () <- add_constraint l t1 (Infer_Tapp [] (TC_name (Short "bool")));
     () <- add_constraint l t2 (Infer_Tapp [] (TC_name (Short "bool")));
     return (Infer_Tapp [] (TC_name (Short "bool")))
  od) ∧
(infer_e l ienv (If e1 e2 e3) =
  do t1 <- infer_e l ienv e1;
     () <- add_constraint l t1 (Infer_Tapp [] (TC_name (Short "bool")));
     t2 <- infer_e l ienv e2;
     t3 <- infer_e l ienv e3;
     () <- add_constraint l t2 t3;
     return t2
  od) ∧
(infer_e l ienv (Mat e pes) =
  if pes = [] then
    failwith l (implode "Empty pattern match")
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
  do () <- guard (ALL_DISTINCT (MAP FST funs)) l (implode "Duplicate function name");
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (nsAppend (alist_to_ns (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) ienv.inf_v);
     funs_ts <- infer_funs l (ienv with inf_v:=env') funs;
     () <- add_constraints l uvars funs_ts;
     t <- infer_e l (ienv with inf_v:=env') e;
     return t
  od) ∧
(infer_e l ienv (Tannot e t) =
  do t' <- infer_e l ienv e;
     () <- guard (check_freevars 0 [] t ∧ check_type_names ienv.inf_t t) l (implode "Bad type annotation");
     () <- add_constraint l t' (infer_type_subst [] (type_name_subst ienv.inf_t t));
     return t'
   od) ∧
(infer_e _ ienv (Lannot e l) =
  infer_e (SOME l) ienv e) ∧
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
     () <- guard (ALL_DISTINCT (MAP FST env')) l (implode "Duplicate pattern variable");
     () <- add_constraint l t1 t1';
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
     return (Infer_Tapp [uvar;t] TC_fn::ts)
  od)`
(WF_REL_TAC `measure (\x. dtcase x of | INL (_,_,e) => exp_size e
                                    | INR (INL (_,_,es)) => exp6_size es
                                    | INR (INR (INL (_,_,pes,_,_))) => exp3_size pes
                                    | INR (INR (INR (_,_,funs))) => exp1_size funs)` >>
 rw []);

(* The final part of the inferencer state that appears at the decls level (and
 * above) are the declared names. The only difference from the type system is
 * that we use lists instead of sets *)

val _ = Hol_datatype `
 inf_decls =
  <| inf_defined_mods : modN list list;
     inf_defined_types : ((modN, typeN) id) list;
     inf_defined_exns : ((modN, conN) id) list|>`;

val empty_inf_decls = Define `
 (empty_inf_decls = (<|inf_defined_mods := []; inf_defined_types := []; inf_defined_exns := []|>))`;

val infer_d_def = Define `
(infer_d mn idecls ienv (Dlet locs p e) =
  do () <- init_state;
     n <- get_next_uvar;
     t1 <- infer_e (SOME locs) ienv e;
     (t2,env') <- infer_p (SOME locs) ienv p;
     () <- guard (ALL_DISTINCT (MAP FST env')) (SOME locs) (implode "Duplicate pattern variable");
     () <- add_constraint (SOME locs) t1 t2;
     ts <- apply_subst_list (MAP SND env');
     (num_tvs, s, ts') <- return (generalise_list n 0 FEMPTY ts);
     () <- guard (num_tvs = 0 ∨ is_value e) (SOME locs) (implode "Value restriction violated");
     return (empty_inf_decls,
             <| inf_v := alist_to_ns (ZIP (MAP FST env', MAP (\t. (num_tvs, t)) ts'));
                inf_c := nsEmpty;
                inf_t := nsEmpty |>)
  od) ∧
(infer_d mn idecls ienv (Dletrec locs funs) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) (SOME locs) (implode "Duplicate function name");
     () <- init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (nsAppend (alist_to_ns (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) ienv.inf_v);
     funs_ts <- infer_funs (SOME locs) (ienv with inf_v:= env') funs;
     () <- add_constraints (SOME locs) uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     return (empty_inf_decls,
             <| inf_v := alist_to_ns (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts');
                inf_c := nsEmpty;
                inf_t := nsEmpty |>)
  od) ∧
(infer_d mn idecls ienv (Dtype locs tdefs) =
  do ienvT1 <- return (alist_to_ns (MAP (λ(tvs,tn,ctors). (tn, (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))))) tdefs));
     ienvT2 <- return (nsAppend ienvT1 ienv.inf_t);
     () <- guard (check_ctor_tenv ienvT2 tdefs) (SOME locs) (implode "Bad type definition");
     new_tdecls <- return (MAP (\(tvs,tn,ctors). mk_id mn tn) tdefs);
     () <- guard (EVERY (\new_id. ~MEM new_id idecls.inf_defined_types)
     new_tdecls) (SOME locs) (implode "Duplicate type definition");
     return (empty_inf_decls with inf_defined_types := new_tdecls,
             <| inf_v := nsEmpty;
                inf_c := build_ctor_tenv mn ienvT2 tdefs;
                inf_t := ienvT1 |>)
  od) ∧
(infer_d mn idecls ienv (Dtabbrev locs tvs tn t) =
  do () <- guard (ALL_DISTINCT tvs) (SOME locs) (implode "Duplicate type variables");
     () <- guard (check_freevars 0 tvs t ∧ check_type_names ienv.inf_t t) (SOME locs)
                 (implode "Bad type definition");
     return (empty_inf_decls,
             <| inf_v := nsEmpty;
                inf_c := nsEmpty;
                inf_t := nsSing tn (tvs,type_name_subst ienv.inf_t t) |>)
  od) ∧
(infer_d mn idecls ienv (Dexn locs cn ts) =
  do () <- guard (check_exn_tenv mn cn ts ∧ EVERY (check_type_names ienv.inf_t) ts ) (SOME locs)
                 (implode "Bad exception definition");
     () <- guard (~MEM (mk_id mn cn) idecls.inf_defined_exns) (SOME locs)
                 (implode "Duplicate exception definition");
     return (empty_inf_decls with inf_defined_exns:=[mk_id mn cn],
             <| inf_v := nsEmpty;
                inf_c := nsSing cn ([], MAP (\x. type_name_subst ienv.inf_t x) ts, TypeExn (mk_id mn cn));
                inf_t := nsEmpty |>)
  od)`;

val append_decls_def = Define `
append_decls idecls1 idecls2 =
  <|inf_defined_mods := idecls1.inf_defined_mods ++ idecls2.inf_defined_mods ;
    inf_defined_types := idecls1.inf_defined_types ++ idecls2.inf_defined_types ;
    inf_defined_exns := idecls1.inf_defined_exns ++ idecls2.inf_defined_exns|>`;

val extend_dec_ienv_def = Define `
  extend_dec_ienv ienv' ienv =
     <| inf_v := nsAppend ienv'.inf_v ienv.inf_v;
        inf_c := nsAppend ienv'.inf_c ienv.inf_c;
        inf_t := nsAppend ienv'.inf_t ienv.inf_t |>`;

val infer_ds_def = Define `
(infer_ds mn idecls ienv [] =
  return (empty_inf_decls, <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>)) ∧
(infer_ds mn idecls ienv (d::ds) =
  do
    (idecls',ienv') <- infer_d mn idecls ienv d;
    (idecls'',ienv'') <- infer_ds mn (append_decls idecls' idecls) (extend_dec_ienv ienv' ienv) ds;
    return (append_decls idecls'' idecls', extend_dec_ienv ienv'' ienv')
  od)`;

val t_to_freevars_def = Define `
(t_to_freevars (Tvar tn) =
  return [tn]) ∧
(t_to_freevars (Tvar_db _) =
  failwith NONE (implode "deBruijn index in type definition")) ∧
(t_to_freevars (Tapp ts tc) =
  ts_to_freevars ts) ∧
(ts_to_freevars [] = return []) ∧
(ts_to_freevars (t::ts) =
  do fvs1 <- t_to_freevars t;
     fvs2 <- ts_to_freevars ts;
     return (fvs1++fvs2)
  od)`;

val check_specs_def = Define `
(check_specs mn tenvT idecls ienv [] =
  return (idecls,ienv)) ∧
(check_specs mn tenvT idecls ienv (Sval x t::specs) =
  do fvs <- t_to_freevars t;
     fvs' <- return (nub fvs);
     () <- guard (check_type_names tenvT t) NONE (implode "Bad type annotation");
     check_specs mn tenvT idecls
       (ienv with inf_v := nsBind x (LENGTH fvs', infer_type_subst (ZIP (fvs', MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs'))))
                                                     (type_name_subst tenvT t))
                              ienv.inf_v)
        specs
  od) ∧
(check_specs mn tenvT idecls ienv (Stype tdefs :: specs) =
  do new_tenvT <- return (alist_to_ns (MAP (λ(tvs,tn,ctors). (tn, (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))))) tdefs));
     tenvT' <- return (nsAppend new_tenvT tenvT);
     () <- guard (check_ctor_tenv tenvT' tdefs) NONE (implode "Bad type definition");
     new_tdecls <- return (MAP (\(tvs,tn,ctors). mk_id mn tn) tdefs);
     check_specs mn tenvT' (idecls with <|inf_defined_types:=new_tdecls++idecls.inf_defined_types|>)
       <| inf_v := ienv.inf_v;
          inf_c := nsAppend (build_ctor_tenv mn tenvT' tdefs) ienv.inf_c;
          inf_t := (nsAppend new_tenvT ienv.inf_t) |>
       specs
  od) ∧
(check_specs mn tenvT idecls ienv (Stabbrev tvs tn t :: specs) =
  do () <- guard (ALL_DISTINCT tvs) NONE (implode "Duplicate type variables");
     () <- guard (check_freevars 0 tvs t ∧ check_type_names tenvT t) NONE (implode "Bad type definition");
     new_tenvT <- return (nsSing tn (tvs,type_name_subst tenvT t));
     check_specs mn (nsAppend new_tenvT tenvT) idecls (ienv with inf_t := nsAppend new_tenvT ienv.inf_t) specs
  od) ∧
(check_specs mn tenvT idecls ienv (Sexn cn ts :: specs) =
  do () <- guard (check_exn_tenv mn cn ts ∧ EVERY (check_type_names tenvT) ts) NONE
                 (implode "Bad exception definition");
     check_specs mn tenvT (idecls with <|inf_defined_exns:=mk_id mn cn::idecls.inf_defined_exns|>)
       (ienv with inf_c := nsBind cn ([], MAP (\x. type_name_subst tenvT x) ts, TypeExn (mk_id mn cn)) ienv.inf_c) specs
  od) ∧
(check_specs mn tenvT idecls ienv (Stype_opq tvs tn :: specs) =
  do () <- guard (ALL_DISTINCT tvs) NONE (implode "Duplicate type variables");
     new_tenvT <- return (nsSing tn (tvs, Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))));
     check_specs mn (nsAppend new_tenvT tenvT) (idecls with <|inf_defined_types:=mk_id mn tn::idecls.inf_defined_types|>)
       (ienv with inf_t := nsAppend new_tenvT ienv.inf_t) specs
  od)`;

val check_weak_decls_def = Define `
check_weak_decls decls_impl decls_spec ⇔
  list_set_eq decls_spec.inf_defined_mods decls_impl.inf_defined_mods ∧
  list_subset decls_spec.inf_defined_types decls_impl.inf_defined_types ∧
  list_subset decls_spec.inf_defined_exns decls_impl.inf_defined_exns`;

val check_tscheme_inst_def = Define `
  check_tscheme_inst _ (tvs_spec, t_spec) (tvs_impl, t_impl) ⇔
    let M =
    do () <- init_state;
       uvs <- n_fresh_uvar tvs_impl;
       t <- return (infer_deBruijn_subst uvs t_impl);
       () <- add_constraint NONE t_spec t
    od
    in
    dtcase M init_infer_state of
    | (Success _, _) => T
    | (Failure _, _) => F `;

val check_weak_ienv_def = Define `
  check_weak_ienv ienv_impl ienv_spec ⇔
    nsSub_compute [] check_tscheme_inst ienv_spec.inf_v ienv_impl.inf_v ∧
    nsSub_compute [] (λ_ x y. x = y) ienv_spec.inf_c ienv_impl.inf_c ∧
    nsSub_compute [] weak_tenvT ienv_spec.inf_t ienv_impl.inf_t`;

val check_signature_def = Define `
(check_signature mn tenvT init_decls decls1 ienv NONE =
  return (decls1, ienv)) ∧
(check_signature mn tenvT init_decls decls1 ienv (SOME specs) =
  do (decls', ienv') <- check_specs mn tenvT empty_inf_decls <|inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |> specs;
     () <- guard (check_weak_ienv ienv ienv') NONE (implode "Signature mismatch");
     () <- guard (check_weak_decls decls1 decls') NONE (implode "Signature mismatch");
     return (decls',ienv')
  od)`;

val ienvLift_def = Define `
  ienvLift mn ienv =
    <|inf_v := nsLift mn ienv.inf_v; inf_c := nsLift mn ienv.inf_c; inf_t := nsLift mn ienv.inf_t|>`;

val infer_top_def = Define `
(infer_top idecls ienv (Tdec d) =
  do
    (decls',ienv') <- infer_d [] idecls ienv d;
    return (decls', ienv')
  od) ∧
(infer_top idecls ienv (Tmod mn spec ds1) =
  do
    () <- guard (~MEM [mn] idecls.inf_defined_mods) NONE (concat [implode "Duplicate module: "; implode mn]);
    (decls',ienv') <- infer_ds [mn] idecls ienv ds1;
    (new_decls,ienv'') <- check_signature [mn] ienv.inf_t idecls decls' ienv' spec;
    return (new_decls with inf_defined_mods := [mn] :: new_decls.inf_defined_mods, ienvLift mn ienv'')
  od)`;

val infer_prog_def = Define `
(infer_prog idecls ienv [] =
  return (empty_inf_decls, <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>)) ∧
(infer_prog idecls ienv (top::tops) =
  do
    (idecls',ienv') <- infer_top idecls ienv top;
    (idecls'', ienv'') <- infer_prog (append_decls idecls' idecls) (extend_dec_ienv ienv' ienv) tops;
    return (append_decls idecls'' idecls', extend_dec_ienv ienv'' ienv')
  od)`;

val _ = Datatype`
  inferencer_config =
  <| inf_decls : inf_decls
   ; inf_env   : inf_env|>`

val infertype_prog_def = Define`
  infertype_prog c prog =
    dtcase FST (infer_prog c.inf_decls c.inf_env prog init_infer_state) of
    | Success (new_decls, new_ienv) =>
        Success ( <| inf_decls := append_decls new_decls c.inf_decls
                ; inf_env := extend_dec_ienv new_ienv c.inf_env |>)
    | Failure x => Failure x`;

val conf = ``<| inf_decls := empty_inf_decls ; inf_env := (<|inf_v := nsEmpty; inf_c := nsEmpty ; inf_t := nsEmpty |>)|>``

val init_config = Define`
  init_config = ^(EVAL ``infertype_prog ^(conf) prim_types_program``
                 |> concl |> rand |> rand)`

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
  dtcase FLOOKUP s n of
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

val ienv_val_ok_def = Define `
ienv_val_ok uvars env =
  nsAll (\x (tvs,t). check_t tvs uvars t) env`;

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
