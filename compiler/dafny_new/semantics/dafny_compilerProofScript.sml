(*
  Correctness proof for the Dafny to CakeML compiler.
*)

open preamble
open astTheory
open semanticPrimitivesTheory
open evaluateTheory
open evaluatePropsTheory
open dafny_semanticPrimitivesTheory
open dafny_evaluateTheory
open namespaceTheory
open mlstringTheory
open integerTheory
open mlintTheory

(* TODO Remove unused definition / trivialities *)

(* For compiler definitions *)
open result_monadTheory

val _ = new_theory "dafny_compilerProof";

(* ************************************************************************** *)
(* TODO Move definitions back to dafny_to_cakeml at the end *)

Overload Unit = “Con NONE []”
Overload False = “Con (SOME (Short "False")) []”
Overload True = “Con (SOME (Short "True")) []”
Overload Tuple = “λes. Con NONE es”

(* Converts a HOL list of CakeML expressions into a CakeML list. *)
Definition cml_list_def:
  (cml_list [] = Con (SOME (Short "[]")) []) ∧
  (cml_list (x::rest) =
   Con (SOME (Short "::")) [x; cml_list rest])
End

Definition init_value_def:
  init_value t =
  (case t of
   | BoolT => False
   | IntT => Lit (IntLit 0)
   | StrT => Lit (StrLit "")
   | ArrT _ => Tuple [Lit (IntLit 0); App AallocEmpty [Unit]])
End

Definition cml_new_refs_in_def:
  cml_new_refs_in nts cml_e =
  (case nts of
   | [] => cml_e
   | ((n,t)::nts) =>
     Let (SOME (explode n))
         (App Opref [init_value t]) (cml_new_refs_in nts cml_e))
End

(* Generates fn i₀ => fn i₁ => ... => body from ins *)
Definition cml_fun_aux_def:
  cml_fun_aux ins body =
  (case ins of
   | [] => body
   | (i::ins) => Fun i (cml_fun_aux ins body))
End

(* Deals with the fact that the first (optional) parameter is treated
   differently when defining functions with Dletrec *)
Definition cml_fun_def:
  cml_fun ins body =
  (case ins of
   | [] => ("", body)
   | [i] => (i, body)
   | (i::ins) => (i, cml_fun_aux ins body))
End

(* Generates strings of the form  0,  1, etc., to be used for matching tuples *)
Definition cml_tup_vname_def:
  cml_tup_vname (idx : num) = explode (« » ^ (num_to_str idx))
End

(* Generates code of the form: case cml_te of ( 0,  1, ...) => cml_e *)
Definition cml_tup_case_def:
  cml_tup_case len cml_te cml_e =
  let tup_pvars = GENLIST (λn. Pvar (cml_tup_vname n)) len in
    Mat cml_te [Pcon NONE tup_pvars, cml_e]
End

Definition cml_tup_select_def:
  cml_tup_select len cml_te (idx: num) =
  cml_tup_case len cml_te (Var (Short (cml_tup_vname idx)))
End

(* We model Dafny's arrays as a tuple: (length, array). This is closer to what
   we need, if we support multi-dimensional arrays. Why? In Dafny, it is
   possible to have arrays where some dimensions have length zero. At the same
   time, it is always possible to ask the length of all dimensions. Hence,
   we cannot just index to the appropriate dimension, and then use Array.length
   - we might get blocked by a dimension with length zero on the way. *)

Definition cml_alloc_arr_def:
  cml_alloc_arr len init = Tuple [len; App Aalloc [len; init]]
End

Definition cml_get_arr_dim_def:
  cml_get_arr_dim cml_e = cml_tup_select 2 cml_e 0
End

Definition cml_get_arr_data_def:
  cml_get_arr_data cml_e = cml_tup_select 2 cml_e 1
End

Definition apps_def:
  apps f [] = f ∧
  apps f (x::xs) = apps (App Opapp [f; x]) xs
End

Definition cml_apps_def:
  cml_apps id [] = App Opapp [id; Unit] ∧
  cml_apps id args = apps id args
End

(* Definition cml_fapp_aux_def: *)
(*   cml_fapp_aux id [] = App Opapp [id; Unit] ∧ *)
(*   cml_fapp_aux id [cml_e] = App Opapp [id; cml_e] ∧ *)
(*   cml_fapp_aux id (cml_e::rest) = App Opapp [id; cml_e] *)
(* End *)

(* Creates nested lets. *)
Definition cml_lets_def:
  cml_lets (lhs::lhss) (cml_rhs::cml_rhss) cml_e =
  do
    rest <- cml_lets lhss cml_rhss cml_e;
    return (Let (SOME lhs) cml_rhs rest)
  od ∧
  cml_lets [] [] cml_e = return cml_e ∧
  cml_lets _ _ _ = fail «cml_lets: Length mismatch»
End

(* Definition cml_bind_def: *)
(*   cml_bind ns cml_rhss cml_e = *)
(*     Mat (Tuple (REVERSE cml_rhss)) [(Pcon NONE (MAP Pvar (REVERSE ns)), cml_e)] *)
(* End *)

Definition cml_fapp_def:
  cml_fapp mns n cml_es = cml_apps (Var (mk_id mns n)) cml_es
End

Definition cml_read_var_def:
  cml_read_var v = App Opderef [Var (Short (explode v))]
End

Definition from_un_op_def:
  from_un_op Not cml_e = If cml_e False True
End

Definition from_bin_op_def:
  from_bin_op Lt cml_e₀ cml_e₁ =
    App (Opb Lt) [cml_e₀; cml_e₁] ∧
  from_bin_op Le cml_e₀ cml_e₁ =
    App (Opb Leq) [cml_e₀; cml_e₁] ∧
  from_bin_op Ge cml_e₀ cml_e₁ =
    App (Opb Geq) [cml_e₀; cml_e₁] ∧
  from_bin_op Eq cml_e₀ cml_e₁ =
    App Equality [cml_e₀; cml_e₁] ∧
  from_bin_op Neq cml_e₀ cml_e₁ =
  (* Make sure that cml_e₁ is evaluated before the rest of the computation as
     the semantics demand *)
  (let n_e₁ = " r" in
     Let (SOME n_e₁) cml_e₁
         (If (App Equality [cml_e₀; Var (Short n_e₁)]) False True)) ∧
  from_bin_op Sub cml_e₀ cml_e₁ =
    App (Opn Minus) [cml_e₀; cml_e₁] ∧
  from_bin_op Add cml_e₀ cml_e₁ =
    App (Opn Plus) [cml_e₀; cml_e₁] ∧
  from_bin_op Mul cml_e₀ cml_e₁ =
    App (Opn Times) [cml_e₀; cml_e₁] ∧
  from_bin_op And cml_e₀ cml_e₁ =
    Log And cml_e₀ cml_e₁ ∧
  from_bin_op Or cml_e₀ cml_e₁ =
    Log Or cml_e₀ cml_e₁ ∧
  from_bin_op Imp cml_e₀ cml_e₁ =
    If cml_e₀ cml_e₁ True ∧
  from_bin_op Div cml_e₀ cml_e₁ =
  (* Make sure that cml_e₁ is evaluated before the rest of the computation as
     the semantics demand *)
  let n_e₁ = " r" in
  (* See HOL's EDIV_DEF: if 0 < j then i div j else ~(i div ~j) *)
  let neg_cml_e₁ = App (Opn Minus) [Lit (IntLit 0); Var (Short n_e₁)] in
    Let (SOME n_e₁) cml_e₁
        (If (App (Opb Lt) [Lit (IntLit 0); Var (Short n_e₁)])
            (App (Opn Divide) [cml_e₀; Var (Short n_e₁)])
            (App (Opn Minus)
                 [Lit (IntLit 0); App (Opn Divide) [cml_e₀; neg_cml_e₁]]))
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | (Neq, _, _) => bin_op_size Neq + 1
                           | (Imp, _, _) => bin_op_size Imp + 1
                           | (bop, _, _) => bin_op_size bop)’
End

Definition from_lit_def:
  from_lit (BoolL b) = (if b then True else False) ∧
  from_lit (IntL i) = Lit (IntLit i) ∧
  from_lit (StrL s) = Lit (StrLit (explode s))
End

Definition gen_arg_names_def:
  gen_arg_names args =
    GENLIST (λn. "a" ++ (explode (num_to_str n))) (LENGTH args)
End

Definition from_exp_def:
  from_exp (Lit l) = return (from_lit l) ∧
  from_exp (Var v) = return (cml_read_var v) ∧
  from_exp (If tst thn els) =
  do
    cml_tst <- from_exp tst;
    cml_thn <- from_exp thn;
    cml_els <- from_exp els;
    return (If cml_tst cml_thn cml_els)
  od ∧
  from_exp (UnOp uop e) =
  do
    cml_e <- from_exp e;
    return (from_un_op uop cml_e)
  od ∧
  from_exp (BinOp bop e₀ e₁) =
  do
    cml_e₀ <- from_exp e₀;
    cml_e₁ <- from_exp e₁;
    (* Force left-to-right evaluation order *)
    n_e₀ <<- " l";
    return (Let (SOME n_e₀) cml_e₀
             (from_bin_op bop (Var (Short n_e₀)) cml_e₁))
  od ∧
  from_exp (ArrLen arr) =
  do
    cml_arr <- from_exp arr;
    return (cml_get_arr_dim cml_arr)
  od ∧
  from_exp (ArrSel arr idx) =
  do
    cml_arr <- from_exp arr;
    cml_idx <- from_exp idx;
    (* Force left-to-right evaluation order *)
    n_arr <<- " arr";
    return (Let (SOME n_arr) cml_arr
                (App Asub [cml_get_arr_data (Var (Short n_arr)); cml_idx]))
  od ∧
  from_exp (FunCall n args) =
  do
    cml_args <- map_from_exp args;
    (* A Dafny function `foo a b c` is compiled to `dfy_foo c b a` to enforce
       left-to-right evaluation order (since CakeML evaluate right to left).
       This shouldn't be a problem, as Dafny does not support partial
       application without defining a new function/lambda. *)
    return (cml_fapp [] ("dfy_" ++ (explode n)) (REVERSE cml_args))
  od ∧
  from_exp (Forall _ _) = fail «from_exp:Forall: Unsupported» ∧
  map_from_exp [] = return [] ∧
  map_from_exp (e::es) =
  do
    cml_e <- from_exp e;
    cml_es <- map_from_exp es;
    return (cml_e::cml_es)
  od
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL e => exp_size e
                           | INR es => list_size exp_size es)’
End

Definition map_from_exp_tup_def:
  map_from_exp_tup [] = return [] ∧
  map_from_exp_tup ((e, x)::rest) =
  do
    cml_e <- from_exp e;
    cml_rest <- map_from_exp_tup rest;
    return ((cml_e, x)::cml_rest)
  od
End

Definition from_rhs_exp_def:
  from_rhs_exp re =
  (case re of
   | ExpRhs e => from_exp e
   | ArrAlloc len init =>
     do
       cml_len <- from_exp len;
       cml_init <- from_exp init;
       return (cml_alloc_arr cml_len cml_init)
     od)
End

Definition assign_def:
  assign lhs cml_rhs =
  (case lhs of
   | VarLhs v =>
       return (App Opassign [Var (Short (explode v)); cml_rhs])
   | ArrSelLhs arr idx =>
     do
       cml_idx <- from_exp idx;
       cml_arr <- from_exp arr;
       cml_arr <<- cml_get_arr_data cml_arr;
       return (App Aupdate [cml_arr; cml_idx; cml_rhs])
     od)
End

Definition assign_mult_def:
  assign_mult (lhs::lhss) (cml_rhs::cml_rhss) =
  do
    cml_assign <- assign lhs cml_rhs;
    rest <- assign_mult lhss cml_rhss;
    return (Let NONE cml_assign rest)
  od ∧
  assign_mult [] [] = return Unit ∧
  assign_mult _ _ = fail «assign_mult: Length mismatch»
End

Definition cml_tmp_vname_def:
  cml_tmp_vname idx = explode («_tmp» ^ (num_to_str idx))
End

Definition par_assign_def:
  par_assign lhss cml_rhss =
  do
    (* To properly implement parallel assign, we first need to evaluate all
       rhss, store them in temporary variables, and then assign those to lhss.
       Otherwise, assignments like a, b := b, a + b may not be dealt with
       properly. *)
    tmp_ns <<- GENLIST (λn. cml_tmp_vname n) (LENGTH cml_rhss);
    tmp_vars <<- MAP (Var ∘ Short) tmp_ns;
    cml_assign <- assign_mult lhss tmp_vars;
    cml_lets tmp_ns cml_rhss cml_assign
  od
End

Definition to_string_def:
  to_string cml_e t =
  (case t of
   | BoolT => return (cml_fapp ["Dafny"] "bool_to_string" [cml_e])
   | IntT => return (cml_fapp ["Dafny"] "int_to_string" [cml_e])
   | StrT => return (cml_e)
   | _ => fail «to_string: Unsupported»)
End

Definition from_statement_def:
  (* lvl keeps track of nested while loops to generate new unique names *)
  from_statement stmt (lvl: num) =
  (case stmt of
   | Skip => return Unit
   | Assert _ => return Unit
   | Then stmt₁ stmt₂ =>
     do
       cml_stmt₁ <- from_statement stmt₁ lvl;
       cml_stmt₂ <- from_statement stmt₂ lvl;
       return (Let NONE cml_stmt₁ cml_stmt₂)
     od
   | If tst thn els =>
     do
       cml_tst <- from_exp tst;
       cml_thn <- from_statement thn lvl;
       cml_els <- from_statement els lvl;
       return (If cml_tst cml_thn cml_els)
     od
   | Dec lcl scope =>
     do
       cml_scope <- from_statement scope lvl;
       return (cml_new_refs_in [lcl] cml_scope)
     od
   | Assign lhss rhss =>
     do
       cml_rhss <- result_mmap from_rhs_exp rhss;
       par_assign lhss cml_rhss
     od
   | While grd _ _ _ body =>
     do
       cml_grd <- from_exp grd;
       cml_body <- from_statement body (lvl + 1);
       loop_name <<- explode («while» ^ (num_to_str lvl));
       run_loop <<- cml_fapp [] loop_name [Unit];
       (* Example (see The Definition of Standard ML, Appendix A):
          let val rec while0 = fn () =>
            if cml_grd then (cml_body; while0()) else ()
          in
            while0()
          end *)
       return (Letrec [(loop_name, "",
                        If cml_grd (Let NONE cml_body run_loop) Unit)]
                        run_loop)
     od
   | Print ets =>
     do
       cml_ets <- map_from_exp_tup ets;
       cml_strs <- result_mmap (λ(e,t). to_string e t) cml_ets;
       cml_str <<- cml_fapp ["String"] "concat" [cml_list cml_strs];
       return (cml_fapp [] "print" [cml_str])
     od
   | MetCall lhss n args =>
     do
       cml_args <- map_from_exp args;
       cml_call <<- cml_fapp [] (explode n) cml_args;
       (* Method returns a tuple of size outs_len, so we use case and assign
          each component to the corresponding left-hand side. *)
       outs_len <<- LENGTH lhss;
       outs <<- GENLIST (λn. Var (Short (cml_tup_vname n))) outs_len;
       cml_assign <- par_assign lhss outs;
       return (cml_tup_case outs_len cml_call cml_assign);
     od
   | Return => return (Raise (Con (SOME (mk_id ["Dafny"] "Return")) [])))
End

(* The members are going to have parameters with the names in ins_ns prefixed
   with _. These are then assigned to references to names without the
   underscore. This way, we can keep the Var implementation the same for
   mutable and immutable variables. *)
(* TODO Optimize above by adding mutability information, and then using
   references only for mutable variables? *)

Definition set_up_cml_fun_def:
  set_up_cml_fun n ins cml_body =
  do
    in_ref_ns <<- MAP FST ins;
    in_param_ns <<- MAP (strcat «_») in_ref_ns;
    init_ins <- par_assign (MAP VarLhs in_ref_ns)
                           (MAP (Var ∘ Short ∘ explode) in_param_ns);
    cml_body <<- Let NONE init_ins cml_body;
    cml_body <<- cml_new_refs_in ins cml_body;
    (cml_param, cml_body) <<-
      cml_fun (REVERSE (MAP explode in_param_ns)) cml_body;
    return ("dfy_" ++ explode n, cml_param, cml_body)
  od
End

Definition from_member_decl_def:
  from_member_decl mem : (string # string # ast$exp) result =
  (case mem of
   (* Constructing methods and functions from bottom to top *)
   | Method n ins _ _ _ _ outs _ body =>
     do
       cml_body <- from_statement body 0;
       (* Method returns a tuple containing the value of the out variables *)
       out_ns <<- MAP FST outs;
       cml_tup <<- Tuple (MAP cml_read_var out_ns);
       cml_body <<- Handle cml_body
                [(Pcon (SOME (mk_id ["Dafny"] "Return")) [], cml_tup)];
       cml_body <<- cml_new_refs_in outs cml_body;
       set_up_cml_fun n ins cml_body
     od
   | Function n ins _ _ _ _ body =>
     do cml_body <- from_exp body; set_up_cml_fun n ins cml_body od)
End

(* ************************************************************************** *)

Type dfy_state[pp] = “:dafny_semanticPrimitives$state”
Type dfy_env[pp] = “:dafny_semanticPrimitives$sem_env”
Type dfy_exp[pp] = “:dafny_ast$exp”
Type dfy_exp_res[pp] = “:'a dafny_semanticPrimitives$exp_result”

Type cml_state[pp] = “:'ffi semanticPrimitives$state”
Type cml_env[pp] = “:v semanticPrimitives$sem_env”
Type cml_exp[pp] = “:ast$exp”
Type cml_res[pp] = “:(v list, v) semanticPrimitives$result”

Definition is_fresh_def:
  is_fresh name = isPrefix «v» name
End

(* NOTE If we have multiple of these, can abstract aways into a function that
   takes a predicate, and walks the AST *)
Definition is_fresh_exp_def[simp]:
  (is_fresh_exp (Lit _) ⇔ T) ∧
  (is_fresh_exp (Var name) ⇔ is_fresh name) ∧
  (is_fresh_exp (If tst thn els) ⇔
     is_fresh_exp tst ∧ is_fresh_exp thn ∧ is_fresh_exp els) ∧
  (is_fresh_exp (UnOp _ e) ⇔ is_fresh_exp e) ∧
  (is_fresh_exp (BinOp _ e₀ e₁) ⇔
     is_fresh_exp e₀ ∧ is_fresh_exp e₁) ∧
  (is_fresh_exp (ArrLen arr) ⇔ is_fresh_exp arr) ∧
  (is_fresh_exp (ArrSel arr idx) ⇔
     is_fresh_exp arr ∧ is_fresh_exp idx) ∧
  (is_fresh_exp (FunCall name es) ⇔
     is_fresh name ∧ EVERY (λe. is_fresh_exp e) es) ∧
  (is_fresh_exp (Forall (name, _) term) ⇔
     is_fresh name ∧ is_fresh_exp term)
Termination
  wf_rel_tac ‘measure $ exp_size’
End

Definition is_fresh_member_def[simp]:
  (* TODO Implement is_fresh_stmt, and then fix Methods *)
  (is_fresh_member (Method _ ins req ens rds decrs outs mods body) ⇔ ARB) ∧
  (is_fresh_member (Function _ ins _ reqs rds decrs body) ⇔
     EVERY (λn. is_fresh n) (MAP FST ins) ∧
     EVERY (λe. is_fresh_exp e) reqs ∧ EVERY (λe. is_fresh_exp e) rds ∧
     EVERY (λe. is_fresh_exp e) decrs ∧ is_fresh_exp body)
End

Definition has_basic_cons_def:
  has_basic_cons env ⇔
    nsLookup env.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env.c (Short "False") = SOME (0, TypeStamp "False" 0)
End

Definition dest_program_def:
  dest_program (Program members) = members
End

Inductive callable_rel:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_basic_cons env ⇒
  callable_rel prog name (Recclosure env cml_funs ("dfy_" ++ (explode name)))
End

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    has_basic_cons env_cml ∧
    ∀name member.
      get_member name env_dfy.prog = SOME member ⇒
      is_fresh_member member ∧
      ∃reclos.
        nsLookup env_cml.v (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
        callable_rel env_dfy.prog name reclos
End

Inductive val_rel:
[~bool:]
  val_rel m (BoolV b) (Boolv b)
[~int:]
  val_rel m (IntV i) (Litv (IntLit i))
[~str:]
  val_rel m (StrV s) (Litv (StrLit (explode s)))
[~arr:]
  len' = &len ∧ FLOOKUP m loc = SOME loc' ⇒
  val_rel m (ArrV len loc) (Conv NONE [Litv (IntLit (len')); Loc T loc'])
End

Theorem val_rel_simp[simp] = LIST_CONJ $
  map (SCONV [val_rel_cases]) [“val_rel m (BoolV b) v”,
                               “val_rel m (IntV i) v”,
                               “val_rel m (StrV s) v”,
                               “val_rel m (ArrV len loc) v”];

Definition array_rel_def:
  array_rel m s_heap c_store ⇔
  INJ (λx. m ' x) (FDOM m) 𝕌(:num) ∧
  ∀loc vs.
    LLOOKUP s_heap loc = SOME (HArr vs) ⇒
    ∃loc' vs'.
      FLOOKUP m loc = SOME loc' ∧
      store_lookup loc' c_store = SOME (Varray vs') ∧
      LIST_REL (val_rel m) vs vs'
End

Definition locals_rel_def:
  locals_rel m (l: mlstring |-> num) s_locals t_refs (env_cml: cml_env) ⇔
    INJ (λx. l ' x) (FDOM l) 𝕌(:num) ∧
    ∀var dfy_v.
      (* SOME dfy_v means that the local was initialized *)
      read_local s_locals var = (SOME dfy_v) ⇒
      (* TODO Do we need to add is_fresh somewhere here? *)
      ∃loc cml_v.
        FLOOKUP l var = SOME loc ∧
        (* locals map to references in CakeML *)
        store_lookup loc t_refs = SOME (Refv cml_v) ∧
        val_rel m dfy_v cml_v ∧
        nsLookup env_cml.v (Short (explode var)) = SOME (Loc T loc)
End

(* TODO *)
Definition print_rel_def:
  print_rel _ _ = ARB
End

Definition state_rel_def:
  state_rel m l s t env_cml ⇔
    s.clock = t.clock ∧
    array_rel m s.heap t.refs ∧
    locals_rel m l s.locals t.refs env_cml ∧
    print_rel s.output t.ffi.io_events
End

Definition exp_res_rel_def[simp]:
  (exp_res_rel m (Rval dfy_v) (Rval [cml_v]) ⇔ val_rel m dfy_v cml_v) ∧
  (exp_res_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_res_rel _ _ _ ⇔ F)
End

Definition exp_ress_rel_def[simp]:
  (exp_ress_rel m (Rval dfy_vs) (Rval cml_vs) ⇔
     LIST_REL (val_rel m) dfy_vs cml_vs) ∧
  (exp_ress_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_ress_rel _ _ _ ⇔ F)
End

Triviality read_local_some_imp:
  read_local s.locals name = SOME dfy_v ∧
  ¬(isPrefix « » name) ∧
  state_rel m l s t env_cml ⇒
  ∃loc cml_v.
    FLOOKUP l name = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    val_rel m dfy_v cml_v ∧
    nsLookup env_cml.v (Short (explode name)) = SOME (Loc T loc)
Proof
  gvs [state_rel_def, locals_rel_def]
QED

(* TODO Is defining these + manually using drule really the way one does
   this? *)
Triviality exp_res_rel_rval:
  exp_res_rel m (Rval dfy_v) r_cml ⇒ ∃cml_v. r_cml = Rval [cml_v]
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘vs’ ["", "v rest"] \\ gvs []
  \\ Cases_on ‘rest’ \\ gvs []
QED

Triviality exp_res_rel_rerr:
  exp_res_rel m (Rerr dfy_err) r_cml ⇒
  dfy_err = Rtimeout_error ∧ r_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Triviality exp_ress_rel_rerr:
  exp_ress_rel m (Rerr dfy_err) rs_cml ⇒
  dfy_err = Rtimeout_error ∧ rs_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Triviality exp_ress_rel_rval:
  exp_ress_rel m (Rval dfy_vs) rs_cml ⇒
  ∃cml_vs. rs_cml = Rval cml_vs ∧ LIST_REL (val_rel m) dfy_vs cml_vs
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
QED

(* TODO Is there a better way to write these nsLookup lemmas? Maybe in a more
     general form? *)
Triviality nslookup_nsoptbind[simp]:
  nsLookup (nsOptBind (SOME n) v env) (Short n) = SOME v
Proof
  Cases_on ‘env’ \\ gvs [nsOptBind_def, nsBind_def, nsLookup_def]
QED

Triviality neq_nslookup_nsoptbind[simp]:
  n ≠ n' ⇒
  nsLookup (nsOptBind (SOME n') v env) (Short n) =
  nsLookup env (Short n)
Proof
  Cases_on ‘env’ \\ gvs [nsOptBind_def, nsBind_def, nsLookup_def]
QED

(* TODO Move to mlstring? *)
(* Triviality isprefix_isprefix: *)
(*   isPrefix s₁ s₂ ⇔ explode s₁ ≼ explode s₂ *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Triviality prefix_space_imp: *)
(*   ¬isPrefix « » n ∧ " " ≼ n' ⇒ n' ≠ explode n *)
(* Proof *)
(*   rpt strip_tac \\ gvs [isprefix_isprefix] *)
(* QED *)

(* Triviality state_rel_env_push_internal: *)
(*   " " ≼ n ∧ state_rel m l s t env ⇒ *)
(*   state_rel m l s t (env with v := nsOptBind (SOME n) v env.v) *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Triviality state_rel_env_pop_internal: *)
(*   " " ≼ n ∧ *)
(*   state_rel m l s t (env with v := nsOptBind (SOME n) v env.v) ⇒ *)
(*   state_rel m l s t env *)
(* Proof *)
(*   cheat *)
(* QED *)

Triviality with_same_refs_ffi[simp]:
  t with <| refs := t.refs; ffi := t.ffi |> = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

(* Triviality state_rel_flookup_m: *)
(*   state_rel m l s t env_cml ∧ *)
(*   FLOOKUP m dfy_loc = SOME cml_loc ∧ *)
(*   FLOOKUP m dfy_loc' = SOME cml_loc' ⇒ *)
(*   ((cml_loc' = cml_loc) ⇔ (dfy_loc' = dfy_loc)) *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Triviality state_rel_llookup: *)
(*   state_rel m l s t env_cml ∧ *)
(*   LLOOKUP s.heap dfy_loc = SOME (HArr dfy_arr) ∧ *)
(*   FLOOKUP m dfy_loc = SOME cml_loc ⇒ *)
(*   ∃cml_arr. *)
(*     store_lookup cml_loc t.refs = SOME (Varray cml_arr) ∧ *)
(*     LIST_REL (val_rel m) dfy_arr cml_arr *)
(* Proof *)
(*   cheat *)
(* QED *)

(* TODO Upstream to HOL? *)
(* Triviality LIST_REL_EL: *)
(*   LIST_REL R l1 l2 ⇔ (∀i. i < LENGTH l1 ⇒ R (EL i l1) (EL i l2)) *)
(* Proof *)
(*   cheat *)
(* QED *)

Triviality get_member_some_fun_name:
  get_member n p = SOME (Function n' ins res_t reqs rds decrs body) ⇒
  n' = n
Proof
  namedCases_on ‘p’ ["members"] \\ Induct_on ‘members’
  \\ gvs [get_member_def, get_member_aux_def]
  \\ qx_gen_tac ‘member’ \\ rpt strip_tac
  \\ namedCases_on ‘member’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = n’ \\ gvs []
QED

Triviality find_recfun_some_aux:
  ∀name members member cml_funs.
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    ∃cml_param cml_body.
      from_member_decl member =
        INR ("dfy_" ++ explode name, cml_param, cml_body) ∧
      find_recfun ("dfy_" ++ explode name) cml_funs =
        SOME (cml_param, cml_body)
Proof
  Induct_on ‘members’ \\ gvs [get_member_aux_def]
  \\ qx_genl_tac [‘member’, ‘name’] \\ rpt strip_tac
  \\ namedCases_on ‘member’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = name’ \\ gvs []
  \\ gvs [result_mmap_def, from_member_decl_def,
          set_up_cml_fun_def, oneline bind_def, CaseEq "sum"]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ simp [Once find_recfun_def]
QED

Triviality find_recfun_some:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ⇒
  ∃cml_param cml_body.
    from_member_decl member =
      INR ("dfy_" ++ explode name, cml_param, cml_body) ∧
    find_recfun ("dfy_" ++ explode name) cml_funs =
      SOME (cml_param, cml_body)
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all find_recfun_some_aux \\ gvs []
QED

Triviality callable_rel_inversion:
  callable_rel prog name reclos ⇒
  ∃env cml_funs member.
    reclos = (Recclosure env cml_funs ("dfy_" ++ (explode name))) ∧
    get_member name prog = SOME member ∧
    result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
    ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
    has_basic_cons env
Proof
   rpt strip_tac \\ gvs [callable_rel_cases, SF SFY_ss]
QED

Triviality nsLookup_nsBind:
  nsLookup (nsBind k x b) (Short k) = SOME x
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Triviality nsLookup_nsBind_neq:
  k' ≠ k ⇒ nsLookup (nsBind k' x b) (Short k) = nsLookup b (Short k)
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Triviality nslookup_build_rec_env_some_aux:
  ∀name members member cml_funs' cml_funs env.
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    nsLookup
      (FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env cml_funs' f) env')
             env.v cml_funs)
      (Short ("dfy_" ++ (explode name))) =
    SOME (Recclosure env cml_funs' ("dfy_" ++ (explode name)))
Proof
  Induct_on ‘members’ \\ gvs [get_member_aux_def]
  \\ qx_genl_tac [‘member'’, ‘name’] \\ rpt strip_tac
  \\ namedCases_on ‘member'’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = name’ \\ gvs []
  \\ gvs [result_mmap_def, from_member_decl_def, set_up_cml_fun_def,
          oneline bind_def, CaseEq "sum"]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [build_rec_env_def, nsLookup_nsBind, nsLookup_nsBind_neq]
QED

Triviality nslookup_build_rec_env_some:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_basic_cons env ⇒
  ∃reclos.
    nsLookup
      (nsBind "" (Conv NONE []) (build_rec_env cml_funs env env.v))
      (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
    callable_rel prog name reclos ∧
    reclos = Recclosure env cml_funs ("dfy_" ++ (explode name))
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [build_rec_env_def, nsLookup_nsBind_neq]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all nslookup_build_rec_env_some_aux
  \\ disch_then $ qspecl_then [‘cml_funs’, ‘env’] mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ gvs [callable_rel_cases]
  \\ qexists ‘member’ \\ gvs [get_member_def, dest_program_def]
QED

Definition refv_same_rel_def[simp]:
  (refv_same_rel [] ys ⇔ T) ∧
  (refv_same_rel ((Refv v)::xs) (y::ys) ⇔
     (y = Refv v) ∧ (refv_same_rel xs ys)) ∧
  (refv_same_rel ((Varray vs)::xs) (y::ys) ⇔
     (refv_same_rel xs ys)) ∧
  (refv_same_rel _ _ ⇔ F)
End

Triviality refv_same_rel_len:
  ∀xs ys. refv_same_rel xs ys ⇒ LENGTH xs ≤ LENGTH ys
Proof
  Induct_on ‘xs’ \\ gvs []
  \\ qx_genl_tac [‘hd’, ‘ys’]
  \\ Cases_on ‘ys’ \\ gvs []
  \\ rpt strip_tac
  \\ Cases_on ‘hd’ \\ gvs []
QED

Triviality refv_same_rel_store_lookup:
  ∀xs ys loc v.
    refv_same_rel xs ys ∧
    store_lookup loc xs = SOME (Refv v) ⇒
    store_lookup loc ys = SOME (Refv v)
Proof
  ho_match_mp_tac refv_same_rel_ind
  \\ rpt strip_tac
  \\ gvs [refv_same_rel_def, store_lookup_def, AllCaseEqs()]
  \\ Cases_on ‘loc’ \\ gvs []
QED

Triviality state_rel_restore_locals:
  state_rel m l s t env ∧
  state_rel m l s' t' env' ∧
  refv_same_rel t.refs t'.refs ⇒
  state_rel m l (restore_locals s' s.locals) t' env
Proof
  rpt strip_tac
  \\ gvs [restore_locals_def, state_rel_def]
  \\ rpt $ qpat_x_assum ‘_ = _’ kall_tac
  \\ rpt $ qpat_x_assum ‘print_rel _ _’ kall_tac
  \\ gvs [locals_rel_def] \\ rpt strip_tac
  \\ last_x_assum drule \\ rpt strip_tac
  \\ pop_assum $ irule_at Any \\ gvs []
  \\ pop_assum $ irule_at Any
  \\ drule_all refv_same_rel_store_lookup \\ gvs []
QED

Triviality gen_arg_names_len[simp]:
  LENGTH (gen_arg_names xs) = LENGTH xs
Proof
  cheat
QED

Triviality pmatch_list_map_pvar:
  LENGTH xs = LENGTH ys ⇒
  pmatch_list cs refs (MAP Pvar xs) ys acc = Match (ZIP (xs, ys) ++ acc)
Proof
  cheat
QED

Triviality nsAppend_empty[simp]:
  nsAppend (Bind [] []) b = b
Proof
  Cases_on ‘b’ \\ gvs [nsAppend_def]
QED

Triviality with_same_v[simp]:
  (env with v := env.v) = env
Proof
  gvs [semanticPrimitivesTheory.sem_env_component_equality]
QED

Triviality with_same_clock[simp]:
  (t: 'ffi cml_state) with clock := t.clock = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality env_rel_nsLookup:
  env_rel env_dfy env_cml ∧
  get_member name env_dfy.prog = SOME member ⇒
  is_fresh_member member ∧
  ∃reclos.
    nsLookup env_cml.v (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
    callable_rel env_dfy.prog name reclos
Proof
  rpt strip_tac \\ gvs [env_rel_def] \\ res_tac
QED

Triviality map_from_exp_empty[simp]:
  map_from_exp [] = INR []
Proof
  gvs [from_exp_def]
QED

Triviality map_from_exp_not_empty:
  map_from_exp es = INR cml_es ∧ es ≠ []⇒ cml_es ≠ []
Proof
  rpt strip_tac
  \\ Cases_on ‘es’
  \\ gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
QED

Triviality cml_apps_apps:
  xs ≠ [] ⇒ cml_apps id xs = apps id xs
Proof
  Cases_on ‘xs’ \\ gvs [cml_apps_def]
QED

Triviality apps_reverse_concat:
  ∀id es e.
    apps id (REVERSE es ++ [e]) = App Opapp [apps id (REVERSE es); e]
Proof
  Induct_on ‘es’ using SNOC_INDUCT \\ gvs [apps_def, REVERSE_SNOC]
QED

Definition apply_aux_def:
  apply_aux env e args =
  case (e, args) of
  | (Fun n e', arg::args') =>
      apply_aux (env with v := nsBind n arg env.v) e' args'
  | (e, []) => SOME (env, e)
  | _ => NONE
End

Triviality apply_aux_empty[simp]:
  apply_aux env e [] = SOME (env, e)
Proof
  gvs [apply_aux_def]
QED

Definition apply_def:
  apply v (arg::args) =
  (case do_opapp [v; arg] of
   | NONE => NONE
   | SOME (env, e) => apply_aux env e args) ∧
  apply _ [] = NONE
End

Definition count_params_aux_def:
  count_params_aux (Fun n e) = 1 + count_params_aux e ∧
  count_params_aux _ = 0n
End

Definition count_params_def:
  count_params v =
  (case do_opapp [v; ARB] of
   | NONE => NONE
   | SOME (_, e) => SOME (1 + count_params_aux e))
End

Definition member_get_ins_def:
  member_get_ins (Method _ ins _ _ _ _ _ _ _) = ins ∧
  member_get_ins (Function _ ins _ _ _ _ _) = ins
End

Triviality count_params_aux_some:
  ∀e args env.
    LENGTH args ≤ count_params_aux e ⇒
    ∃env' e'. apply_aux env e args = SOME (env', e')
Proof
  Induct_on ‘e’ \\ rpt strip_tac
  \\ gvs [count_params_aux_def]
  \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
  \\ simp [Once apply_aux_def]
QED

Triviality count_params_apply_some:
  count_params v = SOME cnt ∧ args ≠ [] ∧ LENGTH args ≤ cnt ⇒
  ∃env e. apply v args = SOME (env, e)
Proof
  rpt strip_tac
  \\ gvs [count_params_def, AllCaseEqs()]
  \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
  \\ gvs [apply_def, do_opapp_def, ADD1, AllCaseEqs()]
  \\ irule count_params_aux_some \\ gvs []
QED

Triviality from_member_decl_count_params_aux:
  from_member_decl member = INR (name, cml_param, cml_body) ⇒
  LENGTH (member_get_ins member) ≤ count_params_aux cml_body + 1
Proof
  rpt strip_tac
  \\ namedCases_on ‘member’ ["_ ins _ _ _ _ _ _ _", "_ ins _ _ _ _ _"]
  \\ gvs [from_member_decl_def, set_up_cml_fun_def, member_get_ins_def,
          oneline bind_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs []
  (* TODO Probably do case distinctions on ins twice, and then maybe
     have a helper lemma mentioning cml_fun *)
QED

Triviality callable_rel_count_params:
  get_member name prog = SOME member ∧
  callable_rel prog name reclos ⇒
  count_params reclos = SOME (LENGTH (member_get_ins member))
Proof
  rpt strip_tac
  \\ gvs [callable_rel_cases]
  \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
  \\ gvs [count_params_def, do_opapp_def]
  \\ irule from_member_decl_count_params_aux \\ gvs []
QED

Triviality apply_append_none:
  apply v args₀ = NONE ⇒ apply v (args₀ ++ args₁) = NONE
Proof
  cheat
QED

(* TODO If general enough, move to evaluateProps *)
Triviality evaluate_apps:
  ∀(s: 'ffi cml_state) env args s₁ r f.
    evaluate s env args = (s₁, r) ∧ args ≠ [] ⇒
    evaluate s env [apps f (REVERSE args)] =
    case r of
    | Rerr err => (s₁, Rerr err)
    | Rval arg_vs =>
      (case evaluate s₁ env [f] of
       | (s₂, Rerr err) => (s₂, Rerr err)
       | (s₂, Rval f_v) =>
         (case apply (HD f_v) (REVERSE arg_vs) of
          | NONE => (s₂, Rerr (Rabort Rtype_error))
          | SOME (call_env, call_e) =>
              if s₂.clock = 0 then
                (s₂, Rerr (Rabort Rtimeout_error))
              else
                evaluate (dec_clock s₂) call_env [call_e]))
Proof
  Induct_on ‘args’ \\ gvs []
  \\ qx_gen_tac ‘arg’ \\ rpt strip_tac
  \\ pop_assum mp_tac \\ simp [Once evaluate_cons] \\ strip_tac
  \\ gvs [apps_reverse_concat, evaluate_def]
  \\ namedCases_on ‘evaluate s env [arg]’ ["s₁' r'"] \\ gvs []
  \\ namedCases_on ‘r'’ ["arg_v", "err"] \\ gvs []
  \\ namedCases_on ‘evaluate s₁' env args’ ["s₂' r'"] \\ gvs []
  \\ reverse $ namedCases_on ‘r'’ ["arg_vs'", "err"] \\ gvs []
  >- (Cases_on ‘args = []’ \\ gvs []
      \\ last_x_assum drule
      \\ disch_then $ qspec_then ‘f’ assume_tac \\ gvs [])
  \\ Cases_on ‘args = []’ \\ gvs []
  >- (gvs [apps_def]
      \\ namedCases_on ‘evaluate s₁ env [f]’ ["s₂ r"] \\ gvs []
      \\ namedCases_on ‘r’ ["f_v", "err"] \\ gvs []
      \\ imp_res_tac evaluate_sing
      \\ gvs [apply_def, apply_aux_def]
      \\ rename [‘do_opapp [f_v; arg_v]’]
      \\ namedCases_on ‘do_opapp [f_v; arg_v]’ ["", "r"] \\ gvs []
      \\ namedCases_on ‘r’ ["env' e"] \\ gvs [])
  \\ last_x_assum drule
  \\ disch_then $ qspec_then ‘f’ assume_tac \\ gvs []
  \\ namedCases_on ‘evaluate s₁ env [f]’ ["s₂ r"] \\ gvs []
  \\ namedCases_on ‘r’ ["f_v", "err"] \\ gvs []
  \\ namedCases_on ‘apply (HD f_v) (REVERSE arg_vs')’ ["", "r"] \\ gvs []
  >- (gvs [REVERSE_APPEND]
      \\ drule apply_append_none
      \\ disch_then $ qspec_then ‘REVERSE arg_v’ assume_tac \\ gvs [])
  \\ namedCases_on ‘r’ ["env' e"] \\ gvs []
  \\ Cases_on ‘s₂.clock = 0’ \\ gvs []
  \\ cheat
QED

Theorem correct_from_exp:
  (∀s env_dfy e_dfy s' r_dfy (t: 'ffi cml_state) env_cml e_cml m l.
     evaluate_exp s env_dfy e_dfy = (s', r_dfy) ∧
     from_exp e_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ is_fresh_exp e_dfy ∧
     r_dfy ≠ Rerr Rtype_error
     ⇒ ∃ck (t': 'ffi cml_state) r_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
           (t', r_cml) ∧
         refv_same_rel t.refs t'.refs ∧ state_rel m l s' t' env_cml ∧
         exp_res_rel m r_dfy r_cml) ∧
  (∀s env_dfy es_dfy s' rs_dfy (t: 'ffi cml_state) env_cml es_cml m l.
     evaluate_exps s env_dfy es_dfy = (s', rs_dfy) ∧
     map_from_exp es_dfy = INR es_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ EVERY (λe. is_fresh_exp e) es_dfy ∧
     rs_dfy ≠ Rerr Rtype_error
     ⇒ ∃ck (t': 'ffi cml_state) rs_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml es_cml =
           (t', rs_cml) ∧
         refv_same_rel t.refs t'.refs ∧ state_rel m l s' t' env_cml ∧
         exp_ress_rel m rs_dfy rs_cml)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘FunCall name args’] >-
   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env_dfy.prog’ ["", "member"] \\ gvs []
    \\ Cases_on ‘member’ \\ gvs []
    \\ rename [‘Function name ins res_t _ _ _ body’]
    \\ drule get_member_some_fun_name \\ rpt strip_tac \\ gvs []
    \\ drule_all env_rel_nsLookup \\ rpt strip_tac
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ qabbrev_tac ‘fname = "dfy_" ++ (explode name)’ \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁,_)’]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (drule exp_ress_rel_rerr \\ rpt strip_tac \\ gvs []
        \\ qexists ‘ck’
        \\ Cases_on ‘args = []’ \\ gvs []
        \\ drule_all map_from_exp_not_empty \\ strip_tac
        \\ ‘REVERSE cml_args ≠ []’ by gvs []
        \\ drule cml_apps_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []
        \\ drule_all evaluate_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs [])
    \\ drule exp_ress_rel_rval \\ rpt strip_tac \\ gvs []
    \\ namedCases_on
         ‘set_up_call s₁ (MAP FST ins) in_vs []’ ["", "r"] \\ gvs []
    \\ gvs [set_up_call_def, safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (qexists ‘ck’
        \\ Cases_on ‘args = []’ \\ gvs []
        >- (gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
                 do_opapp_def]
            \\ gvs [callable_rel_cases]
            \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
            \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def] \\ gvs []
            \\ gvs [restore_locals_def])
        \\ drule_all map_from_exp_not_empty \\ strip_tac
        \\ ‘REVERSE cml_args ≠ []’ by gvs []
        \\ drule cml_apps_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []
        \\ drule_all evaluate_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []
        \\ gvs [evaluate_def]
       )

    (****)

    \\ drule_all env_rel_nsLookup \\ rpt strip_tac
    \\ gvs [callable_rel_cases]
    \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ qabbrev_tac ‘fname = "dfy_" ++ (explode name)’ \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁,_)’]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (drule exp_ress_rel_rerr \\ rpt strip_tac \\ gvs []
        \\ qexists ‘ck’
        \\ Cases_on ‘args = []’ \\ gvs []
        \\ drule_all map_from_exp_not_empty \\ strip_tac
        \\ ‘REVERSE cml_args ≠ []’ by gvs []
        \\ drule cml_apps_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []
        \\ drule_all evaluate_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs [])
    \\ drule exp_ress_rel_rval \\ rpt strip_tac \\ gvs []
    \\ namedCases_on
         ‘set_up_call s₁ (MAP FST ins) in_vs []’ ["", "r"] \\ gvs []
    \\ gvs [set_up_call_def, safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (qexists ‘ck’
        \\ Cases_on ‘args = []’ \\ gvs []
        >- (gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
                 do_opapp_def]
            \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def] \\ gvs []
            \\ gvs [restore_locals_def])
        \\ drule_all map_from_exp_not_empty \\ strip_tac
        \\ ‘REVERSE cml_args ≠ []’ by gvs []
        \\ drule cml_apps_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []
        \\ drule_all evaluate_apps
        \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs []

        \\ gvs [evaluate_def]

        \\ namedCases_on ‘evaluate t₁ env_cml [Var (Short fname)]’ ["t₂ r"]
        \\ gvs []
        \\ reverse $ namedCases_on ‘r’ ["f_v", "err"] \\ gvs []
        >- gvs [evaluate_def]
        \\ namedCases_on ‘apply (HD f_v) (REVERSE cml_vs)’ ["", "r"] \\ gvs []
        )
    \\ namedCases_on
       ‘evaluate_exp
          (dec_clock
            (s₁ with locals := REVERSE (ZIP (MAP FST ins,MAP SOME in_vs))))
          env_dfy body’ ["s₃ r"] \\ gvs []



    \\ ‘LENGTH cml_args = LENGTH cml_vs’ by cheat \\ gvs []
    \\ gvs [cml_bind_def, evaluate_def, do_con_check_def, build_conv_def]
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (qexists ‘ck’
        \\ gvs [can_pmatch_all_def, pmatch_def]
        \\ DEP_REWRITE_TAC [pmatch_list_map_pvar] \\ gvs []
        \\ reverse $ IF_CASES_TAC
        >- cheat
        \\ Cases_on ‘args = []’ \\ gvs []
        >- (gvs [evaluate_exp_def, from_exp_def]
            \\ gvs [gen_arg_names_def, alist_to_ns_def, cml_apps_def,
                    evaluate_def, do_con_check_def, build_conv_def]
            \\ gvs [do_opapp_def, callable_rel_cases]
            \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def]
            \\ gvs [restore_locals_def])
        \\ cheat  (* TODO: s₁.clock = 0 ∧ args ≠ []*))
    \\ namedCases_on
       ‘evaluate_exp
          (dec_clock
            (s₁ with locals := REVERSE (ZIP (MAP FST ins,MAP SOME in_vs))))
          env_dfy body’ ["s₃ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ gvs [from_member_decl_def, oneline bind_def, CaseEq "sum"]
    \\ Cases_on ‘args = []’ \\ gvs []
    >- (last_x_assum $
          qspecl_then
            [‘t’,
             ‘(env with
                 v := nsBind "" (Conv NONE [])
                        (build_rec_env cml_funs env env.v))’,
             ‘m’, ‘l’] mp_tac
        \\ impl_tac
        >- cheat
        \\ strip_tac
        \\ rename [‘_ with clock := ck' + _’]

        \\ drule evaluate_add_to_clock
        \\ disch_then $ qspec_then ‘ck’ assume_tac

        \\ rev_drule evaluate_add_to_clock
        \\ disch_then $ qspec_then ‘ck'’ assume_tac

        \\ qexists ‘ck + ck'’ \\ gvs []
        \\ gvs [can_pmatch_all_def, pmatch_def]
        \\ DEP_REWRITE_TAC [pmatch_list_map_pvar] \\ gvs []
        \\ reverse $ IF_CASES_TAC
        >- cheat
        \\ gvs [Once from_exp_def]
        \\ ‘cml_args = []’ by gvs [from_exp_def]

        \\ gvs [gen_arg_names_def, cml_apps_def, evaluate_def, do_con_check_def,
                build_conv_def, do_opapp_def]
        \\ IF_CASES_TAC >- gvs [state_rel_def]
        \\ gvs [set_up_cml_fun_def, par_assign_def, assign_mult_def,
                cml_lets_def, cml_fun_def, cml_new_refs_in_def,
                oneline bind_def, CaseEq "sum"]
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, nsOptBind_def]
        )


    \\ rename [‘_ with clock := ck + _’] \\ qexists ‘ck’
    \\ gvs [cml_bind_def, evaluate_def, do_con_check_def, build_conv_def]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (drule exp_ress_rel_rerr \\ rpt strip_tac \\ gvs [])
    \\ drule exp_ress_rel_rval \\ rpt strip_tac \\ gvs []
    \\ gvs [can_pmatch_all_def, pmatch_def]
    \\ ‘LENGTH cml_args = LENGTH cml_vs’ by cheat \\ gvs []
    \\ DEP_REWRITE_TAC [pmatch_list_map_pvar] \\ gvs []
    \\ reverse $ IF_CASES_TAC
    >- cheat
    \\ Cases_on ‘args = []’ \\ gvs []
    >- (gvs [evaluate_exp_def, from_exp_def]
        \\ gvs [gen_arg_names_def, alist_to_ns_def, cml_apps_def,
                evaluate_def, do_con_check_def, build_conv_def]
        \\ namedCases_on
           ‘set_up_call s (MAP FST ins) [] []’ ["", "old_locals s₂"]
        \\ gvs [set_up_call_def, safe_zip_def]
        \\ Cases_on ‘ins = []’ \\ gvs []
        \\ ‘ck = 0’ by gvs [state_rel_def] \\ gvs []
        \\ ‘t.clock = s.clock’ by gvs [state_rel_def] \\ gvs []
        \\ Cases_on ‘s.clock = 0’ \\ gvs []
        \\ drule_all env_rel_nsLookup \\ rpt strip_tac \\ gvs []
        \\ gvs [do_opapp_def, callable_rel_cases]
        \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
        >- gvs [restore_locals_def]
        \\ namedCases_on
             ‘evaluate_exp (dec_clock (s with locals := [])) env_dfy body’
             ["s₃ r"]
        \\ gvs []
        \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
        \\ gvs [from_member_decl_def, set_up_cml_fun_def, cml_fun_def,
                cml_new_refs_in_def, par_assign_def, assign_mult_def,
                cml_lets_def, oneline bind_def, CaseEq "sum"]
        \\ rename [‘Recclosure basic_env _ _’]
        \\ last_x_assum $
             qspecl_then
             [‘dec_clock t’,
                ‘basic_env with
                 v :=
                   nsBind "" (Conv NONE [])
                     (build_rec_env cml_funs basic_env basic_env.v)’,
                ‘m’, ‘l’]
               mp_tac
        \\ impl_tac
        >- (gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def,
                 locals_rel_def, read_local_def, nsLookup_def]
            \\ gvs [env_rel_def] \\ rpt strip_tac
            >- gvs [has_basic_cons_def]
            >- res_tac
            \\ drule_all nslookup_build_rec_env_some
            \\ rpt strip_tac \\ gvs [])
        \\ rpt strip_tac \\ gvs []

        \\ gvs [evaluateTheory.dec_clock_def]


    \\ Induct_on ‘args’ \\ rpt strip_tac \\ gvs []
    >- (gvs [evaluate_exp_def, from_exp_def]
        \\ gvs [gen_arg_names_def, cml_lets_def]
        \\ namedCases_on
           ‘set_up_call s (MAP FST ins) [] []’ ["", "old_locals s₂"]
        \\ gvs [set_up_call_def, safe_zip_def]
        \\ Cases_on ‘ins = []’ \\ gvs []
        \\ ‘t.clock = s.clock’ by gvs [state_rel_def]
        \\ Cases_on ‘s.clock = 0’ \\ gvs []
        >- (gvs [cml_fapp_def, cml_fapp_aux_def, mk_id_def]
            \\ gvs [evaluate_def, do_con_check_def, build_conv_def]
            \\ gvs [env_rel_def]
            \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
            \\ gvs [do_opapp_def, callable_rel_cases]
            \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
            \\ gvs [restore_locals_def])
        \\ gvs [cml_fapp_def, cml_fapp_aux_def, mk_id_def]
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def]
        \\ gvs [env_rel_def]
        \\ first_assum drule_all \\ rpt strip_tac \\ gvs []
        \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
        \\ gvs [do_opapp_def]
        \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []

        \\ gvs [from_member_decl_def, oneline bind_def, set_up_cml_fun_def,
                cml_fun_def, cml_new_refs_in_def, par_assign_def,
                assign_mult_def, cml_lets_def, CaseEq "sum"]
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, nsOptBind_def]

        \\ rename [‘Recclosure basic_env _ _’]

        >- (gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def,
                 locals_rel_def, read_local_def, nsLookup_def]
            \\ rpt strip_tac \\ gvs []
            >- gvs [has_basic_cons_def]
            >- res_tac
            \\ drule_all nslookup_build_rec_env_some
            \\ rpt strip_tac \\ gvs [])
        \\ rpt strip_tac \\ gvs []
        \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
        \\ gvs [evaluateTheory.dec_clock_def]
        \\ drule_all state_rel_restore_locals \\ gvs [])


    \\ rename [‘map_from_exp (arg::args') = _’]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
        \\ gvs [gen_arg_names_def, cml_fapp_def, cml_fapp_aux_def])

    \\ gvs [from_exp_def, oneline bind_def, CaseEq "sum"]


   )


  \\ cheat
  (* >~ [‘Forall var term’] >- *)
  (*  (gvs [from_exp_def]) *)
  (* >~ [‘Lit l’] >- *)
  (*  (Cases_on ‘l’ *)
  (*   \\ gvs [from_exp_def, from_lit_def, evaluate_def, do_con_check_def, *)
  (*           env_rel_def, build_conv_def, exp_res_rel_def, evaluate_exp_def, *)
  (*           val_rel_cases, Boolv_def, bool_type_num_def, AllCaseEqs()]) *)
  (* >~ [‘Var name’] >- *)
  (*  (gvs [evaluate_exp_def, AllCaseEqs()] *)
  (*   \\ drule_all read_local_some_imp \\ rpt strip_tac *)
  (*   \\ gvs [from_exp_def, cml_read_var_def] *)
  (*   \\ gvs [evaluate_def, do_app_def, state_rel_def]) *)
  (* >~ [‘If grd thn els’] >- *)
  (*  (reverse $ *)
  (*     gvs [evaluate_exp_def, from_exp_def, oneline bind_def, AllCaseEqs()] *)
  (*   \\ first_x_assum drule_all \\ rpt strip_tac *)
  (*   >- (gvs [evaluate_def] \\ TOP_CASE_TAC \\ gvs []) *)
  (*   \\ rename [‘do_cond v _ _ = SOME _’] \\ Cases_on ‘v’ *)
  (*   \\ gvs [do_cond_def] *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [val_rel_cases] *)
  (*   \\ gvs [evaluate_def, do_if_def] *)
  (*   \\ rename [‘Boolv b’] \\ Cases_on ‘b’ *)
  (*   \\ gvs [Boolv_def]) *)
  (* >~ [‘UnOp uop e’] >- *)
  (*  (reverse $ *)
  (*     gvs [evaluate_exp_def, from_exp_def, oneline bind_def, *)
  (*          oneline from_un_op_def, AllCaseEqs()] *)
  (*   \\ first_x_assum drule_all \\ rpt strip_tac *)
  (*   >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ gvs [evaluate_def]) *)
  (*   \\ gvs [oneline do_uop_def, AllCaseEqs()] *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [val_rel_cases] *)
  (*   \\ gvs [evaluate_def, do_if_def] *)
  (*   \\ rename [‘Boolv b’] \\ Cases_on ‘b’ *)
  (*   \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def, *)
  (*           val_rel_cases, Boolv_def, bool_type_num_def]) *)
  (* >~ [‘BinOp bop e₀ e₁’] >- *)
  (*  (gvs [from_exp_def, oneline bind_def, AllCaseEqs()] *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env_dfy e₀’ ["s₁ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘evaluate _ _ _ = (t₁, _)’] *)
  (*   \\ gvs [evaluate_def] *)
  (*   \\ reverse $ Cases_on ‘r’ \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ gvs []) *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘val_rel _ dfy_v₀ cml_v₀’] *)
  (*   \\ Cases_on ‘do_sc bop dfy_v₀’ \\ gvs [] *)
  (*   >- (* Short-circuiting *) *)
  (*    (gvs [oneline do_sc_def, val_rel_cases, evaluate_def, from_bin_op_def, *)
  (*          do_log_def, Boolv_def, do_if_def, do_con_check_def, env_rel_def, *)
  (*          build_conv_def, bool_type_num_def, AllCaseEqs()]) *)
  (*   \\ namedCases_on ‘evaluate_exp s₁ env_dfy e₁’ ["s₂ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ ‘" " ≼ " l"’ by gvs []  \\ drule_all state_rel_env_push_internal *)
  (*   \\ disch_then $ qspec_then ‘cml_v₀’ assume_tac *)
  (*   \\ last_x_assum drule *)
  (*   \\ impl_tac >- gvs [env_rel_def] *)
  (*   \\ rpt strip_tac *)
  (*   \\ drule_all state_rel_env_pop_internal \\ rpt strip_tac \\ gvs [] *)
  (*   \\ reverse $ Cases_on ‘r’ \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ Cases_on ‘bop’ *)
  (*       \\ gvs [oneline do_sc_def, val_rel_cases, from_bin_op_def, *)
  (*               evaluate_def, do_log_def, do_if_def, AllCaseEqs()]) *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘val_rel _ dfy_v₁ cml_v₁’] *)
  (*   \\ Cases_on ‘do_bop bop dfy_v₀ dfy_v₁’ \\ gvs [] *)
  (*   \\ Cases_on ‘bop = Div’ \\ gvs [] >- *)
  (*    (gvs [do_bop_def, AllCaseEqs()] *)
  (*     \\ gvs [from_bin_op_def, EDIV_DEF] *)
  (*     \\ gvs [evaluate_def, do_app_def, do_if_def, opb_lookup_def] *)
  (*     \\ Cases_on ‘0 < i₁’ *)
  (*     \\ gvs [evaluate_def, do_app_def, opn_lookup_def, Boolv_def]) *)
  (*   \\ Cases_on ‘bop = Eq’ \\ gvs [] >- *)
  (*    (gvs [do_bop_def] *)
  (*     \\ gvs [from_bin_op_def] *)
  (*     \\ gvs [evaluate_def, do_app_def] *)
  (*     \\ namedCases_on ‘dfy_v₀’ ["i", "b", "str", "len dfy_loc"] \\ gvs [] *)
  (*     \\ namedCases_on ‘dfy_v₁’ ["i'", "b'", "str'", "len' dfy_loc'"] \\ gvs [] *)
  (*     >~ [‘do_eq (Boolv _) (Boolv _)’] >- *)
  (*      (Cases_on ‘b’ \\ Cases_on ‘b'’ *)
  (*       \\ gvs [do_eq_def, lit_same_type_def, Boolv_def, ctor_same_type_def, *)
  (*               same_type_def]) *)
  (*     >~ [‘do_eq (Conv _ _) (Conv _ _)’] >- *)
  (*      (drule state_rel_flookup_m *)
  (*       \\ disch_then drule \\ disch_then rev_drule \\ rpt strip_tac *)
  (*       \\ gvs [do_eq_def, lit_same_type_def] *)
  (*       \\ Cases_on ‘len = len'’ \\ gvs [] *)
  (*       \\ Cases_on ‘dfy_loc = dfy_loc'’ \\ gvs []) *)
  (*     \\ gvs [do_eq_def, lit_same_type_def]) *)
  (*   \\ Cases_on ‘bop = Neq’ \\ gvs [] >- *)
  (*    (gvs [do_bop_def] *)
  (*     \\ gvs [from_bin_op_def] *)
  (*     \\ gvs [evaluate_def, do_app_def] *)
  (*     \\ namedCases_on *)
  (*          ‘dfy_v₀’ ["i", "b", "dfy_str", "len dfy_loc"] \\ gvs [] *)
  (*     \\ namedCases_on *)
  (*          ‘dfy_v₁’ ["i'", "b'", "dfy_str'", "len' dfy_loc'"] \\ gvs [] *)
  (*     >~ [‘do_eq (Boolv _) (Boolv _)’] >- *)
  (*      (Cases_on ‘b’ \\ Cases_on ‘b'’ *)
  (*       \\ gvs [evaluate_def, do_eq_def, lit_same_type_def, Boolv_def, *)
  (*               ctor_same_type_def, same_type_def, do_if_def, do_con_check_def, *)
  (*               build_conv_def, env_rel_def, bool_type_num_def]) *)
  (*     >~ [‘do_eq (Conv _ _) (Conv _ _)’] >- *)
  (*      (drule state_rel_flookup_m *)
  (*       \\ disch_then drule \\ disch_then rev_drule \\ rpt strip_tac *)
  (*       \\ gvs [do_eq_def, lit_same_type_def] *)
  (*       \\ Cases_on ‘len = len'’ \\ gvs [] *)
  (*       \\ Cases_on ‘dfy_loc = dfy_loc'’ *)
  (*       \\ gvs [do_if_def, evaluate_def, do_con_check_def, env_rel_def, *)
  (*               build_conv_def, Boolv_def, bool_type_num_def]) *)
  (*     >~ [‘do_eq (Litv (IntLit _)) (Litv (IntLit _))’] >- *)
  (*      (gvs [do_eq_def, lit_same_type_def, do_if_def] *)
  (*       \\ Cases_on ‘i' = i’ *)
  (*       \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def, *)
  (*               Boolv_def, bool_type_num_def]) *)
  (*     >~ [‘do_eq (Litv (StrLit _)) (Litv (StrLit _))’] >- *)
  (*      (gvs [do_eq_def, lit_same_type_def, do_if_def] *)
  (*       \\ Cases_on ‘dfy_str = dfy_str'’ *)
  (*       \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def, *)
  (*               Boolv_def, bool_type_num_def])) *)
  (*     \\ gvs [oneline do_bop_def, do_sc_def, AllCaseEqs()] *)
  (*     \\ gvs [from_bin_op_def] *)
  (*     \\ gvs [evaluate_def, do_app_def, opb_lookup_def, opn_lookup_def, *)
  (*             do_log_def, do_if_def]) *)
  (* >~ [‘ArrLen arr’] >- *)
  (*  (gvs [from_exp_def, oneline bind_def, AllCaseEqs()] *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ last_x_assum drule_all \\ rpt strip_tac *)
  (*   \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr *)
  (*       \\ gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def, *)
  (*               evaluate_def]) *)
  (*   \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs [] *)
  (*   \\ gvs [oneline get_array_len_def, AllCaseEqs()] *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def] *)
  (*   \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, pat_bindings_def, *)
  (*           cml_tup_vname_def, num_to_str_11] *)
  (*   \\ Cases_on ‘env_cml.v’ *)
  (*   \\ gvs [alist_to_ns_def, nsAppend_def, nsLookup_def, num_to_str_11]) *)
  (* >~ [‘ArrSel arr idx’] >- *)
  (*  (gvs [from_exp_def, oneline bind_def, AllCaseEqs()] *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ first_x_assum drule_all \\ rpt strip_tac *)
  (*   \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ gvs [] *)
  (*       \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def] *)
  (*       \\ gvs [evaluate_def]) *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ gvs [evaluate_def] *)
  (*   \\ rename [‘val_rel _ dfy_arr cml_arr’] *)
  (*   \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ ‘" " ≼ " arr"’ by gvs []  \\ drule_all state_rel_env_push_internal *)
  (*   \\ disch_then $ qspec_then ‘cml_arr’ assume_tac *)
  (*   \\ last_x_assum drule *)
  (*   \\ impl_tac >- gvs [env_rel_def] *)
  (*   \\ rpt strip_tac *)
  (*   \\ drule_all state_rel_env_pop_internal \\ rpt strip_tac \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["idx_v",  "err"] \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr \\ gvs []) *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ namedCases_on ‘index_array s₂ dfy_arr idx_v’ ["", "elem"] \\ gvs [] *)
  (*   \\ gvs [oneline index_array_def, oneline val_to_num_def, CaseEq "value", *)
  (*           CaseEq "option", CaseEq "heap_value"] *)
  (*   \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def] *)
  (*   \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, cml_tup_vname_def, *)
  (*           pat_bindings_def, num_to_str_11] *)
  (*   \\ Cases_on ‘env_cml.v’ \\ gvs [] *)
  (*   \\ gvs [nsOptBind_def, nsBind_def, alist_to_ns_def, nsAppend_def, *)
  (*           nsLookup_def] *)
  (*   \\ gvs [do_app_def] *)
  (*   \\ drule_all state_rel_llookup \\ rpt strip_tac \\ gvs [] *)
  (*   \\ gvs [INT_ABS] *)
  (*   \\ drule LIST_REL_LENGTH \\ rpt strip_tac *)
  (*   \\ gvs [LLOOKUP_EQ_EL, LIST_REL_EL]) *)
  (* >~ [‘map_from_exp []’] >- *)
  (*  (gvs [from_exp_def, evaluate_exp_def, evaluate_def]) *)
  (* >~ [‘map_from_exp (e::es)’] >- *)
  (*  (gvs [from_exp_def, oneline bind_def, AllCaseEqs()] *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["cml_e",  "err"] \\ gvs [] *)
  (*   >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ gvs [] *)
  (*       \\ rename [‘_::cml_es’] *)
  (*       \\ Cases_on ‘cml_es’ \\ gvs [evaluate_def]) *)
  (*   \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [] *)
  (*   \\ namedCases_on ‘es’ ["", "e' es"] \\ gvs [] *)
  (*   >- (gvs [evaluate_exp_def, from_exp_def]) *)
  (*   \\ namedCases_on ‘evaluate_exps s₁ env_dfy (e'::es')’ ["s₂ r"] \\ gvs [] *)
  (*   \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs [] *)
  (*   \\ gvs [from_exp_def, oneline bind_def, CaseEq "sum"] *)
  (*   \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ reverse $ Cases_on ‘r’ \\ gvs [] *)
  (*   >- (drule exp_ress_rel_rerr \\ rpt strip_tac \\ gvs [evaluate_def]) *)
  (*   \\ drule exp_ress_rel_rval \\ rpt strip_tac \\ gvs [evaluate_def]) *)
QED

val _ = export_theory ();
