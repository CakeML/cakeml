(*
  Correctness proof for the Dafny to CakeML compiler.
*)

open preamble
open astTheory
open semanticPrimitivesTheory
open evaluateTheory
open evaluatePropsTheory
open evaluate_appsTheory
open dafny_semanticPrimitivesTheory
open dafny_evaluateTheory
open dafny_evaluatePropsTheory
open namespaceTheory
open namespacePropsTheory
open mlstringTheory
open integerTheory
open mlintTheory

(* TODO Remove unused definition / trivialities *)
(* TODO Should we simplify print to just be `Print exp type`? *)

(* TODO Remove this when we move out the compiler *)
(* For compiler definitions *)
open result_monadTheory

val _ = new_theory "dafny_compilerProof";
val _ = set_grammar_ancestry
          ["ast", "semanticPrimitives", "evaluate", "evaluateProps",
           "evaluate_apps", "dafny_semanticPrimitives", "dafny_evaluate",
           "namespace", "namespaceProps", "mlstring", "integer", "mlint",
           (* TODO Remove this when we move out the compiler *)
           "result_monad"];

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

(* Creates new references initialized with 0. *)
(* Note that we will use these for references of all types. It doesn't matter
   that this does not type check, as we are proving correctness anyway. *)
Definition cml_new_refs_def:
  cml_new_refs [] cml_e = cml_e ∧
  cml_new_refs (n::ns) cml_e =
    Let (SOME n) (App Opref [Lit (IntLit 0)]) (cml_new_refs ns cml_e)
End

(* Deals with the fact that the first (optional) parameter is treated
   differently when defining functions with Dletrec *)
Definition cml_fun_def:
  cml_fun ins body =
  (case ins of
   | [] => ("", body)
   | (i::ins) => (i, Funs ins body))
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

Definition cml_apps_def:
  cml_apps id [] = App Opapp [id; Unit] ∧
  cml_apps id args = apps id args
End

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

Definition cml_fapp_def:
  cml_fapp mns n cml_es = cml_apps (Var (mk_id mns n)) cml_es
End

Definition cml_read_var_def:
  cml_read_var v = App Opderef [Var (Short v)]
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
  from_exp (Var v) = return (cml_read_var (explode v)) ∧
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

Definition from_stmt_def:
  (* lvl keeps track of nested while loops to generate new unique names *)
  from_stmt Skip (lvl: num) = return Unit ∧
  from_stmt (Assert _) _ = return Unit ∧
  from_stmt (Then stmt₁ stmt₂) lvl =
  do
    cml_stmt₁ <- from_stmt stmt₁ lvl;
    cml_stmt₂ <- from_stmt stmt₂ lvl;
    return (Let NONE cml_stmt₁ cml_stmt₂)
  od ∧
  from_stmt (If tst thn els) lvl =
  do
    cml_tst <- from_exp tst;
    cml_thn <- from_stmt thn lvl;
    cml_els <- from_stmt els lvl;
    return (If cml_tst cml_thn cml_els)
  od ∧
  from_stmt (Dec (n, _) scope) lvl =
  do
    cml_scope <- from_stmt scope lvl;
    return (cml_new_refs [explode n] cml_scope)
  od ∧
  from_stmt (Assign lhss rhss) _ =
  do
    cml_rhss <- result_mmap from_rhs_exp rhss;
    par_assign lhss cml_rhss
  od ∧
  from_stmt (While grd _ _ _ body) lvl =
  do
    cml_grd <- from_exp grd;
    cml_body <- from_stmt body (lvl + 1);
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
  od ∧
  from_stmt (Print ets) _ =
  do
    cml_ets <- map_from_exp_tup ets;
    cml_strs <- result_mmap (λ(e,t). to_string e t) cml_ets;
    cml_str <<- cml_fapp ["String"] "concat" [cml_list cml_strs];
    return (cml_fapp [] "print" [cml_str])
  od ∧
  from_stmt (MetCall lhss n args) _ =
  do
    cml_args <- map_from_exp args;
    cml_call <<- cml_fapp [] (explode n) cml_args;
    (* Method returns a tuple of size outs_len, so we use case and assign
       each component to the corresponding left-hand side. *)
    outs_len <<- LENGTH lhss;
    outs <<- GENLIST (λn. Var (Short (cml_tup_vname n))) outs_len;
    cml_assign <- par_assign lhss outs;
    return (cml_tup_case outs_len cml_call cml_assign);
  od ∧
  from_stmt Return _ =
    return (Raise (Con (SOME (mk_id ["Dafny"] "Return")) []))
End

(* Shadows the parameters with references with the same name (and value). *)
Definition set_up_in_refs_def:
  set_up_in_refs [] cml_e = cml_e ∧
  set_up_in_refs (n::ns) cml_e =
    Let (SOME n) (Var (Short n)) (set_up_in_refs ns cml_e)
End

(* Sets up the in parameters. *)
Definition set_up_cml_fun_def:
  set_up_cml_fun n ins cml_body =
  (* Reversing the parameters is an easy way to get left-to-right evaluation
     on them *)
    let in_ns = REVERSE (MAP (explode ∘ FST) ins) in
    let cml_body = set_up_in_refs in_ns cml_body in
    let (cml_param, cml_body) = cml_fun in_ns cml_body in
      (* Prepending functions with "dfy_" avoids naming issues. *)
      ("dfy_" ++ (explode n), cml_param, cml_body)
End

Definition from_member_decl_def:
  from_member_decl mem : (string # string # ast$exp) result =
  case mem of
  (* Constructing methods and functions from bottom to top *)
  | Method n ins _ _ _ _ outs _ body =>
    do
      cml_body <- from_stmt body 0;
      (* Method returns a tuple containing the value of the out variables *)
      out_ns <<- MAP (explode ∘ FST) outs;
      cml_tup <<- Tuple (MAP cml_read_var out_ns);
      cml_body <<-
        Handle cml_body
          [(Pcon (SOME (mk_id ["Dafny"] "Return")) [], cml_tup)];
      cml_body <<- cml_new_refs out_ns cml_body;
      return (set_up_cml_fun n ins cml_body)
    od
  | Function n ins _ _ _ _ body =>
    do
      cml_body <- from_exp body;
      return (set_up_cml_fun n ins cml_body)
    od
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

(* Returns whether the name comes from the freshen pass. *)
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

Definition is_fresh_lhs_exp[simp]:
  (is_fresh_lhs_exp (VarLhs name) ⇔ is_fresh name) ∧
  (is_fresh_lhs_exp (ArrSelLhs arr idx) ⇔
     is_fresh_exp arr ∧ is_fresh_exp idx)
End

Definition is_fresh_rhs_exp[simp]:
  (is_fresh_rhs_exp (ExpRhs e) ⇔ is_fresh_exp e) ∧
  (is_fresh_rhs_exp (ArrAlloc len init_e) ⇔
     is_fresh_exp len ∧ is_fresh_exp init_e)
End

Definition is_fresh_stmt_def[simp]:
  (is_fresh_stmt Skip ⇔ T) ∧
  (is_fresh_stmt (Assert e) ⇔ is_fresh_exp e) ∧
  (is_fresh_stmt (Then stmt₀ stmt₁) ⇔
     is_fresh_stmt stmt₀ ∧ is_fresh_stmt stmt₁) ∧
  (is_fresh_stmt (If cnd thn els) ⇔
     is_fresh_exp cnd ∧ is_fresh_stmt thn ∧ is_fresh_stmt els) ∧
  (is_fresh_stmt (Dec (n, _) scope) ⇔
     is_fresh n ∧ is_fresh_stmt scope) ∧
  (is_fresh_stmt (Assign lhss rhss) ⇔
     EVERY (λlhs. is_fresh_lhs_exp lhs) lhss ∧
     EVERY (λrhs. is_fresh_rhs_exp rhs) rhss) ∧
  (is_fresh_stmt (While grd invs decrs mods body) ⇔
     is_fresh_exp grd ∧
     EVERY (λe. is_fresh_exp e) invs ∧
     EVERY (λe. is_fresh_exp e) decrs ∧
     EVERY (λe. is_fresh_exp e) mods ∧
     is_fresh_stmt body) ∧
  (* TODO Skipped Print for now *)
  (is_fresh_stmt (MetCall lhss _ args) ⇔
     EVERY (λlhs. is_fresh_lhs_exp lhs) lhss ∧
     EVERY (λe. is_fresh_exp e) args) ∧
  (is_fresh_stmt Return ⇔ T)
End

Definition is_fresh_member_def[simp]:
  (is_fresh_member (Method _ ins reqs ens rds decrs outs mods body) ⇔
     EVERY (λn. is_fresh n) (MAP FST ins) ∧
     EVERY (λe. is_fresh_exp e) reqs ∧
     EVERY (λe. is_fresh_exp e) ens ∧
     EVERY (λe. is_fresh_exp e) rds ∧
     EVERY (λe. is_fresh_exp e) decrs ∧
     EVERY (λn. is_fresh n) (MAP FST outs) ∧
     is_fresh_stmt body) ∧
  (is_fresh_member (Function _ ins _ reqs rds decrs body) ⇔
     EVERY (λn. is_fresh n) (MAP FST ins) ∧
     EVERY (λe. is_fresh_exp e) reqs ∧ EVERY (λe. is_fresh_exp e) rds ∧
     EVERY (λe. is_fresh_exp e) decrs ∧ is_fresh_exp body)
End

Definition ret_stamp_def:
  ret_stamp = ExnStamp 67  (* TODO Check *)
End

Definition is_ret_exn_def[simp]:
  is_ret_exn val ⇔ val = Conv (SOME ret_stamp) []
End

Definition has_basic_cons_def:
  has_basic_cons env ⇔
    nsLookup env.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env.c (Short "False") = SOME (0, TypeStamp "False" 0) ∧
    nsLookup env.c (Long "Dafny" (Short "Return")) = SOME (0, ret_stamp)
End

(* TODO Move to dafny_ast? *)
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
    env_dfy.is_running ∧
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
      read_local s_locals var = (SOME dfy_v) ∧
      is_fresh var ⇒
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

Triviality exp_res_rel_rval[simp]:
  exp_res_rel m (Rval dfy_v) r_cml ⇔
    ∃cml_v. r_cml = Rval [cml_v] ∧ val_rel m dfy_v cml_v
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘vs’ ["", "v rest"] \\ gvs []
  \\ Cases_on ‘rest’ \\ gvs []
QED

Triviality exp_res_rel_rerr[simp]:
  exp_res_rel m (Rerr dfy_err) r_cml ⇔
  dfy_err = Rtimeout_error ∧ r_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Definition exp_ress_rel_def[simp]:
  (exp_ress_rel m (Rval dfy_vs) (Rval cml_vs) ⇔
     LIST_REL (val_rel m) dfy_vs cml_vs) ∧
  (exp_ress_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_ress_rel _ _ _ ⇔ F)
End

Triviality exp_ress_rel_rerr[simp]:
  exp_ress_rel m (Rerr dfy_err) rs_cml ⇔
  dfy_err = Rtimeout_error ∧ rs_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Triviality exp_ress_rel_rval[simp]:
  exp_ress_rel m (Rval dfy_vs) rs_cml ⇔
  ∃cml_vs. rs_cml = Rval cml_vs ∧ LIST_REL (val_rel m) dfy_vs cml_vs
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
QED

Definition stmt_res_rel_def[simp]:
  (stmt_res_rel Rcont (Rval _) ⇔ T) ∧
  (stmt_res_rel (Rstop Sret) (Rerr (Rraise val)) ⇔ is_ret_exn val) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout_error))
     (Rerr (Rabort Rtimeout_error)) ⇔ T) ∧
  (stmt_res_rel _ _ ⇔ F)
End

Triviality stmt_res_rel_simp[simp]:
  (stmt_res_rel Rcont r_cml ⇔
     ∃vs. r_cml = Rval vs) ∧
  (stmt_res_rel (Rstop Sret) r_cml ⇔
     ∃v. r_cml = Rerr (Rraise v) ∧ is_ret_exn v) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout_error)) r_cml ⇔
     r_cml = (Rerr (Rabort Rtimeout_error)))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["exn", "abrt"] \\ gvs []
  \\ Cases_on ‘abrt’ \\ gvs []
QED

Triviality read_local_some_imp:
  read_local s.locals name = SOME dfy_v ∧
  state_rel m l s (t: 'ffi cml_state) env_cml ∧
  is_fresh name ⇒
  ∃loc cml_v.
    FLOOKUP l name = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    val_rel m dfy_v cml_v ∧
    nsLookup env_cml.v (Short (explode name)) = SOME (Loc T loc)
Proof
  gvs [state_rel_def, locals_rel_def]
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
Triviality isprefix_isprefix:
  isPrefix s₁ s₂ ⇔ explode s₁ ≼ explode s₂
Proof
  cheat
QED

Triviality is_fresh_neq[simp]:
  is_fresh n ∧ ¬is_fresh n' ⇒ n ≠ n'
Proof
  rpt strip_tac \\ gvs [is_fresh_def]
QED

(* TODO Should push and pop be conditional rewrites instead? *)
Triviality state_rel_env_push_not_fresh:
  state_rel m l s (t: 'ffi cml_state) env ∧ ¬(is_fresh n) ⇒
  state_rel m l s t (env with v := nsOptBind (SOME (explode n)) v env.v)
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Triviality state_rel_env_pop_not_fresh:
  ¬(is_fresh n) ∧
  state_rel m l s (t: 'ffi cml_state)
    (env with v := nsOptBind (SOME (explode n)) v env.v) ⇒
  state_rel m l s t env
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Triviality with_same_refs_ffi[simp]:
  (t: 'ffi cml_state) with <| refs := t.refs; ffi := t.ffi |> = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality with_same_ffi[simp]:
  (t: 'ffi cml_state) with <| clock := c; refs := r; ffi := t.ffi |> =
  t with <| clock := c; refs := r |>
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality state_rel_llookup:
  state_rel m l s t env_cml ∧
  LLOOKUP s.heap dfy_loc = SOME (HArr dfy_arr) ∧
  FLOOKUP m dfy_loc = SOME cml_loc ⇒
  ∃cml_arr.
    store_lookup cml_loc t.refs = SOME (Varray cml_arr) ∧
    LIST_REL (val_rel m) dfy_arr cml_arr
Proof
  rpt strip_tac
  \\ gvs [state_rel_def, array_rel_def]
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
QED

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

(* TODO Can we do this without manually unfolding? *)
Triviality nslookup_build_rec_env_reclos_aux:
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

Triviality nslookup_build_rec_env_reclos:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_basic_cons env ⇒
  ∃reclos.
    nsLookup
      (build_rec_env cml_funs env env.v)
      (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
    callable_rel prog name reclos ∧
    reclos = Recclosure env cml_funs ("dfy_" ++ (explode name))
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [build_rec_env_def]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all nslookup_build_rec_env_reclos_aux
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
  (refv_same_rel ((W8array ws)::xs) (y::ys) ⇔
     (refv_same_rel xs ys)) ∧
  (refv_same_rel _ _ ⇔ F)
End

Triviality refv_same_rel_same_state_aux:
  ∀s_refs. refv_same_rel s_refs s_refs
Proof
  Induct_on ‘s_refs’ \\ gvs []
  \\ qx_gen_tac ‘hd’
  \\ Cases_on ‘hd’ \\ gvs []
QED

Triviality refv_same_rel_same_state[simp]:
  refv_same_rel s.refs s.refs
Proof
  qspec_then ‘s.refs’ mp_tac refv_same_rel_same_state_aux \\ gvs []
QED

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

Triviality state_rel_locals_rel:
  locals_rel m l s.locals (t: 'ffi cml_state).refs env ∧
  refv_same_rel t.refs (t': 'ffi cml_state).refs ⇒
  locals_rel m l s.locals t'.refs env
Proof
  gvs [locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule \\ gvs []
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’]
  \\ drule refv_same_rel_store_lookup \\ gvs []
QED

Triviality state_rel_restore_locals:
  state_rel m l s (t: 'ffi cml_state) env ∧
  state_rel m l s' (t': 'ffi cml_state) env' ∧
  refv_same_rel t.refs t'.refs ⇒
  state_rel m l (restore_locals s' s.locals) t' env
Proof
  rpt strip_tac
  \\ gvs [restore_locals_def, state_rel_def]
  \\ irule state_rel_locals_rel
  \\ gvs [SF SFY_ss]
QED

Triviality gen_arg_names_len[simp]:
  LENGTH (gen_arg_names xs) = LENGTH xs
Proof
  gvs [gen_arg_names_def]
QED

(* TODO Check if needed; add to namespaceTheory? *)
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
  ∀xs id. xs ≠ [] ⇒ cml_apps id xs = apps id xs
Proof
  Cases_on ‘xs’ \\ gvs [cml_apps_def]
QED

Triviality apps_reverse_concat:
  ∀id es e.
    apps id (REVERSE es ++ [e]) = App Opapp [apps id (REVERSE es); e]
Proof
  Induct_on ‘es’ using SNOC_INDUCT \\ gvs [apps_def, REVERSE_SNOC]
QED

Definition member_get_ins_def[simp]:
  member_get_ins (Method _ ins _ _ _ _ _ _ _) = ins ∧
  member_get_ins (Function _ ins _ _ _ _ _) = ins
End

Triviality map_from_exp_len:
  ∀es cml_es. map_from_exp es = INR cml_es ⇒ LENGTH cml_es = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
QED

Triviality evaluate_exps_length:
  ∀s env es s' vs.
    evaluate_exps s env es = (s', Rval vs) ⇒ LENGTH vs = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
  \\ res_tac
QED

Definition enumerate_from_def:
  enumerate_from offset ns = MAPi (λi n. (n, offset + i)) ns
End

Definition add_refs_to_env_def:
  add_refs_to_env env_v ns offset =
    nsAppend
      (alist_to_ns (MAP (λ(n, i). (n, Loc T i)) (enumerate_from offset ns)))
      env_v
End

Definition mk_locals_map_def:
  mk_locals_map (ns: mlstring list) offset =
    alist_to_fmap (enumerate_from offset ns)
End

Triviality inj_mk_locals_map:
  INJ (λx. mk_locals_map ns offset ' x) (FDOM (mk_locals_map ns offset))
    𝕌(:num)
Proof
  cheat
QED

(* Triviality add_refs_to_env_nsbind: *)
(*   add_refs_to_env (nsBind n v nspc) ns offset = *)
(*   add_refs_to_env nspc (n::ns) offset *)
(* Proof *)
(*   cheat *)
(* QED *)

Triviality evaluate_set_up_in_refs:
  ∀params vs s env body.
    LIST_REL (λn v. nsLookup env.v (Short n) = SOME v) params vs ⇒
    evaluate (s: 'ffi cml_state) env [set_up_in_refs params body] =
    evaluate
      (s with refs := s.refs ++ (MAP Refv vs))
      (env with v := add_refs_to_env env.v params (LENGTH s.refs))
      [body]
Proof
  cheat
  (* Induct_on ‘params’ \\ rpt strip_tac *)
  (* >- (‘s with refs := s.refs = s’ by *)
  (*       gvs [semanticPrimitivesTheory.state_component_equality] *)
  (*     \\ gvs [set_up_in_refs_def, add_refs_to_env_def, enumerate_from_def]) *)
  (* \\ gvs [set_up_in_refs_def, evaluate_def] *)
  (* \\ rename [‘LIST_REL _ params' vs'’, ‘nsLookup _ (Short n) = SOME v’] *)
  (* \\ last_x_assum $ *)
  (*      qspecl_then *)
  (*        [‘vs'’, ‘s’, ‘env with v := nsOptBind (SOME n) v env.v’, ‘body’] *)
  (*        mp_tac *)
  (* \\ impl_tac >- cheat *)
  (* \\ strip_tac *)
  (* \\ gvs [nsOptBind_def, add_refs_to_env_nsbind] *)
QED

Triviality refv_same_rel_append_imp:
  ∀xs ys zs.
    refv_same_rel (xs ++ ys) zs ⇒ refv_same_rel xs zs
Proof
  Induct_on ‘xs’ \\ gvs []
  \\ qx_gen_tac ‘x’ \\ rpt strip_tac
  \\ namedCases_on ‘zs’ ["", "z zs'"] \\ gvs []
  \\ Cases_on ‘x’ \\ Cases_on ‘z’ \\ gvs []
  \\ res_tac
QED

Triviality refv_same_rel_trans:
  ∀xs ys zs.
    refv_same_rel xs ys ∧ refv_same_rel ys zs ⇒ refv_same_rel xs zs
Proof
  ho_match_mp_tac refv_same_rel_ind \\ rpt strip_tac
  \\ gvs []
  \\ Cases_on ‘zs’ \\ gvs []
  \\ rename [‘refv_same_rel (y::ys) (z::zs)’]
  \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs []
QED

Triviality nslookup_nsappend_alist_neq:
  EVERY (λy. y ≠ x) (MAP FST ys) ⇒
  nsLookup (nsAppend (alist_to_ns ys) ns) (Short x) = nsLookup ns (Short x)
Proof
  cheat
QED

Triviality nslookup_add_refs_to_env_neq:
  EVERY (λn. n ≠ x) ns ⇒
  nsLookup (add_refs_to_env env_v ns offset) (Short x) =
  nsLookup env_v (Short x)
Proof
  cheat
QED

Triviality store_lookup_append:
  store_lookup l st = SOME v ⇒ store_lookup l (st ++ st') = SOME v
Proof
  rpt strip_tac \\ gvs [store_lookup_def, rich_listTheory.EL_APPEND1]
QED

Triviality array_rel_append:
  array_rel m s_heap t_heap ⇒
  array_rel m s_heap (t_heap ++ xs)
Proof
  gvs [array_rel_def]
  \\ rpt strip_tac
  \\ last_x_assum drule \\ rpt strip_tac
  \\ drule store_lookup_append
  \\ disch_then $ qspec_then ‘xs’ assume_tac
  \\ gvs []
QED

Triviality read_local_reverse_eq:
  ALL_DISTINCT (MAP FST l) ⇒ read_local (REVERSE l) var = read_local l var
Proof
  rpt strip_tac
  \\ drule alookup_distinct_reverse
  \\ disch_then $ qspec_then ‘var’ assume_tac
  \\ gvs [read_local_def]
QED

Triviality read_local_EL:
  ∀(ns: mlstring list) (vs: value list) var val.
    read_local (ZIP (ns, MAP SOME vs)) var = SOME val ∧
    ALL_DISTINCT ns ∧ LENGTH vs = LENGTH ns ⇒
    ∃i. var = EL i ns ∧ val = EL i vs ∧ i < LENGTH ns
Proof
  rpt strip_tac
  \\ gvs [read_local_def, AllCaseEqs()]
  \\ drule ALOOKUP_find_index_SOME \\ rpt strip_tac
  \\ qexists ‘i’
  \\ gvs [EL_ZIP, find_index_ALL_DISTINCT_EL_eq, EL_MAP, MAP_ZIP]
QED

Triviality ALOOKUP_enumerate_from:
  ∀i xs offset.
    ALL_DISTINCT xs ∧
    i < LENGTH xs ⇒
    ALOOKUP (enumerate_from offset (REVERSE xs)) (EL i xs) = SOME (i + offset)
Proof
  cheat
QED

Triviality nsLookup_add_refs_to_env:
  ALL_DISTINCT ns ∧
  i < LENGTH ns ⇒
  nsLookup
    (add_refs_to_env env.v (REVERSE (MAP explode ns)) offset)
    (Short (explode (EL i ns))) =
  SOME (Loc T (i + offset))
Proof
  rpt strip_tac
  \\ gvs [add_refs_to_env_def]
  \\ gvs [nsLookup_nsAppend_some]
  \\ disj1_tac
  \\ gvs [nsLookup_alist_to_ns_some]
  \\ gvs [ALOOKUP_MAP]
  \\ gvs [ALOOKUP_enumerate_from, GSYM EL_MAP]
QED

Triviality FLOOKUP_mk_locals_map:
  FLOOKUP (mk_locals_map ns offset) (EL i ns) = SOME (i + offset)
Proof
  cheat
QED

Triviality LIST_REL_store_lookup:
  LIST_REL (val_rel m) in_vs cml_vs ⇒
  store_lookup (i + LENGTH s.refs) (s.refs ++ MAP Refv cml_vs) =
  SOME (Refv (EL i cml_vs)) ∧ val_rel m (EL i in_vs) (EL i cml_vs)
Proof
  cheat
QED

Triviality flookup_mk_locals_map:
  ∀(s: 'ffi cml_state) env ins in_vs var dfy_v m cml_vs.
    read_local (ZIP (MAP FST ins, MAP SOME in_vs)) var = SOME dfy_v ∧
    LIST_REL (val_rel m) in_vs cml_vs ∧
    ALL_DISTINCT (MAP FST ins) ∧
    LENGTH in_vs = LENGTH ins ⇒
    ∃loc cml_v.
      nsLookup
        (add_refs_to_env env.v (REVERSE (MAP (explode ∘ FST) ins))
           (LENGTH s.refs))
        (Short (explode var)) = SOME (Loc T loc) ∧
      FLOOKUP (mk_locals_map (MAP FST ins) (LENGTH s.refs)) var = SOME loc ∧
      store_lookup loc (s.refs ++ MAP Refv cml_vs) = SOME (Refv cml_v) ∧
      val_rel m dfy_v cml_v
Proof
  rpt strip_tac
  \\ drule_then assume_tac read_local_EL \\ gvs []
  \\ qexistsl [‘LENGTH s.refs + i’, ‘EL i cml_vs’]
  \\ gvs [GSYM MAP_MAP_o]
  \\ irule_at Any nsLookup_add_refs_to_env \\ gvs []
  \\ irule_at Any FLOOKUP_mk_locals_map \\ gvs []
  \\ irule LIST_REL_store_lookup \\ gvs []
QED

Triviality is_fresh_not_dfy:
  EVERY (λn. is_fresh n) ns ⇒
  ∀sfx. EVERY (λn. n ≠ "dfy_" ++ (explode sfx)) (MAP explode ns)
Proof
  cheat
QED

Triviality EVERY_TL:
  EVERY P xs ∧ xs ≠ [] ⇒ EVERY P (TL xs)
Proof
  Cases_on ‘xs’ \\ gvs []
QED

(* TODO Is this useful to be in namespaceTheory? *)
Triviality nsappend_alist_to_ns_nsbind:
  nsAppend (alist_to_ns (ZIP (ns, vs))) (nsBind n v env) =
  nsAppend (alist_to_ns (ZIP (SNOC n ns, SNOC v vs))) env
Proof
  cheat
QED

Triviality list_rel_nslookup_nsappend:
  ALL_DISTINCT ns ⇒
  LIST_REL
    (λn v.
       nsLookup
         (nsAppend (alist_to_ns (ZIP (REVERSE ns, vs))) env_v)
         (Short n) =
       SOME v)
    params cml_vs
Proof
  cheat
QED

(* TODO Is this a good way to write this?/Upstream to HOL *)
Triviality SNOC_HD_REVERSE_TL:
  xs ≠ [] ⇒ SNOC (HD xs) (REVERSE (TL xs)) = REVERSE xs
Proof
  rpt strip_tac
  \\ ‘(HD xs)::(TL xs) = xs’ by gvs []
  \\ asm_rewrite_tac [GSYM (cj 2 REVERSE_SNOC_DEF)]
QED

(* TODO Should we upstream this to HOL? *)
Triviality INJ_FLOOKUP_IMP:
  INJ (λx. m ' x) (FDOM m) 𝕌(:β) ⇒
  ∀x y. FLOOKUP m x = FLOOKUP m y ⇔ x = y
Proof
  cheat
QED

Triviality state_rel_array_loc_INJ:
  state_rel m l s (t: 'ffi cml_state) env_cml ⇒
  INJ (λx. m ' x) (FDOM m) 𝕌(:num)
Proof
  gvs [state_rel_def, array_rel_def]
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
    \\ drule map_from_exp_len \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁,_)’]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (* Evaluating arguments failed *)
     (qexists ‘ck’
      \\ Cases_on ‘cml_args = []’ \\ gvs []
      \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
      \\ drule_all evaluate_apps_Rerr
      \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs [])
    \\ drule evaluate_exps_length \\ rpt strip_tac \\ gvs []
    \\ namedCases_on
         ‘set_up_call s₁ (MAP FST ins) in_vs []’ ["", "r"] \\ gvs []
    \\ gvs [set_up_call_def, safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (* Dafny semantics ran out of ticks *)
     (qexists ‘ck’ \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
      >- (gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
               do_opapp_def, callable_rel_cases]
          \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
          \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def] \\ gvs []
          \\ gvs [restore_locals_def])
      \\ Cases_on ‘cml_args = []’ \\ gvs []
      \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
      (* Preparing ns for evaluate_apps *)
      \\ qabbrev_tac ‘params = REVERSE (MAP (explode ∘ FST) ins)’
      \\ ‘LENGTH params = LENGTH ins’ by (unabbrev_all_tac \\ gvs [])
      \\ ‘SUC (LENGTH (TL params)) = LENGTH ins’ by (Cases_on ‘params’ \\ gvs [])
      (* Preparing clos_v for evaluate_apps *)
      \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
      (* Preparing env1 for evaluate_apps *)
      \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
      \\ qabbrev_tac
         ‘call_env =
            env with v :=
              nsBind cml_param (LAST cml_vs) (build_rec_env cml_funs env env.v)’
      (* Preparing e for evaluate_apps *)
      \\ gvs [from_member_decl_def, set_up_cml_fun_def, oneline bind_def,
              CaseEq "sum"]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ qabbrev_tac ‘call_body = set_up_in_refs params cml_body'’
      (* Instantiating evaluate_apps *)
      \\ drule evaluate_apps
      \\ disch_then $ qspec_then ‘TL params’ mp_tac \\ gvs []
      \\ disch_then $ drule
      \\ disch_then $ qspecl_then [‘call_env’, ‘call_body’] mp_tac
      \\ impl_tac >- gvs [do_opapp_def, cml_fun_def, MAP_MAP_o, AllCaseEqs()]
      \\ rpt strip_tac \\ gvs []
      \\ pop_assum $ kall_tac
      (* Finished instantiating evaluate_apps *)
      \\ ‘t₁.clock = s₁.clock’ by gvs [state_rel_def] \\ gvs []
      \\ gvs [restore_locals_def, state_rel_def])
    \\ qabbrev_tac ‘dfy_locals = REVERSE (ZIP (MAP FST ins, MAP SOME in_vs))’
    \\ namedCases_on
         ‘evaluate_exp (dec_clock (s₁ with locals := dfy_locals)) env_dfy body’
         ["s₂ r"]
    \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    (* Show how compiling the function body succeeds *)
    \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
    \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ gvs [from_member_decl_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
    >-
     (gvs [evaluate_exp_def]
      \\ ‘ck = 0’ by gvs [state_rel_def] \\ gvs []
      \\ ‘t.clock ≠ 0’ by gvs [state_rel_def] \\ gvs []
      \\ last_x_assum $
           qspecl_then
             [‘dec_clock t’,
              ‘env with v :=
                 nsBind "" (Conv NONE []) (build_rec_env cml_funs env env.v)’,
              ‘m’, ‘l’]
             mp_tac
      \\ impl_tac
      >-
       (unabbrev_all_tac
        \\ gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def,
                locals_rel_def, read_local_def, env_rel_def]
        \\ rpt strip_tac
        >- gvs [has_basic_cons_def]
        >- res_tac
        >- (drule_all nslookup_build_rec_env_reclos \\ gvs []))
      \\ rpt strip_tac
      \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = _’]
      \\ qexists ‘ck'’
      \\ gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
              do_opapp_def]
      \\ gvs [set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def]
      \\ gvs [evaluate_def, do_con_check_def, build_conv_def, nsOptBind_def,
              evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r’ \\ gvs []
      \\ drule_all state_rel_restore_locals \\ gvs [])
    (* Evaluating (non-empty) args succeeded *)
    \\ Cases_on ‘cml_args = []’ \\ gvs []
    \\ Cases_on ‘cml_vs = []’ \\ gvs []
    \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
    (* TODO Maybe we should case distinction on args earlier? *)
    (* Preparing ns for evaluate_apps *)
    \\ qabbrev_tac ‘params = REVERSE (MAP (explode ∘ FST) ins)’
    \\ ‘LENGTH params = LENGTH ins’ by (unabbrev_all_tac \\ gvs [])
    \\ ‘SUC (LENGTH (TL params)) = LENGTH ins’ by (Cases_on ‘params’ \\ gvs [])
    \\ ‘LENGTH cml_vs = LENGTH cml_args’ by
      (drule (cj 1 evaluate_length) \\ gvs [])
    \\ ‘LENGTH (REVERSE (TL params)) = LENGTH (FRONT cml_vs)’ by
      (Cases_on ‘cml_vs = []’ \\ gvs [FRONT_LENGTH])
    (* Preparing clos_v for evaluate_apps *)
    \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
    (* Preparing env1 for evaluate_apps *)
    \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ qabbrev_tac
       ‘call_env =
          env with v :=
            nsBind cml_param (LAST cml_vs) (build_rec_env cml_funs env env.v)’
    (* Preparing e for evaluate_apps *)
    \\ gvs [from_member_decl_def, set_up_cml_fun_def, oneline bind_def,
            CaseEq "sum"]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ qabbrev_tac ‘call_body = set_up_in_refs params cml_body'’
    (* Instantiating IH *)
    \\ qabbrev_tac
         ‘call_env₁ =
            call_env with v :=
              nsAppend
                (alist_to_ns (ZIP (REVERSE (TL params), FRONT cml_vs)))
                call_env.v’
    \\ qabbrev_tac
         ‘call_env₂ =
            call_env₁ with v :=
              add_refs_to_env call_env₁.v params (LENGTH t₁.refs)’
    \\ last_x_assum $
         qspecl_then
           [‘dec_clock (t₁ with refs := t₁.refs ++ MAP Refv cml_vs)’,
            ‘call_env₂’,
            ‘m’,
            ‘mk_locals_map (MAP FST ins) (LENGTH t₁.refs)’]
           mp_tac
    \\ impl_tac
    >- (rpt strip_tac
        >- (gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def]
            \\ irule_at Any array_rel_append \\ gvs []
            \\ gvs [locals_rel_def]
            \\ irule_at Any inj_mk_locals_map
            \\ rpt strip_tac
            \\ gvs [Abbr ‘dfy_locals’]
            \\ ‘ALL_DISTINCT (MAP FST (ZIP (MAP FST ins, MAP SOME in_vs)))’
              by gvs [MAP_ZIP]
            \\ drule read_local_reverse_eq
            \\ disch_then $ qspec_then ‘var’ assume_tac
            \\ gvs []
            (* Delete rewriting assumptions we just made *)
            \\ ntac 2 (pop_assum $ kall_tac)
            \\ drule flookup_mk_locals_map
            \\ disch_then drule \\ gvs []
            \\ disch_then $ qspecl_then [‘t₁’, ‘call_env₁’] mp_tac
            \\ rpt strip_tac \\ gvs [Abbr ‘call_env₂’, Abbr ‘params’])
        \\ gvs [env_rel_def] \\ rpt strip_tac
        >- (unabbrev_all_tac \\ gvs [has_basic_cons_def])
        >- res_tac
        \\ rename [‘get_member name' _ = SOME _’]
        \\ ‘EVERY (λn. n ≠ STRCAT "dfy_" (explode name')) params’ by
          (drule is_fresh_not_dfy
           \\ disch_then $ qspec_then ‘name'’ assume_tac
           \\ gvs [Abbr ‘params’, MAP_MAP_o])
        \\ gvs [Abbr ‘call_env₂’]
        \\ DEP_REWRITE_TAC [nslookup_add_refs_to_env_neq]
        \\ gvs [Abbr ‘call_env₁’]
        \\ DEP_REWRITE_TAC [nslookup_nsappend_alist_neq]
        \\ gvs [MAP_ZIP]
        \\ strip_tac >-
         (irule EVERY_TL \\ Cases_on ‘params = []’ \\ gvs [])
        \\ gvs [Abbr ‘call_env’]
        \\ DEP_REWRITE_TAC [nsLookup_nsBind_neq]
        \\ strip_tac >- (Cases_on ‘params’ \\ gvs [cml_fun_def])
        \\ drule_all nslookup_build_rec_env_reclos \\ gvs [])
    \\ rpt strip_tac
    (* Fixing clocks *)
    \\ ‘t₁.clock ≠ 0’ by gvs [state_rel_def]
    \\ qexists ‘ck + ck' + LENGTH ins - 1’
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck' + LENGTH ins - 1’ assume_tac
    \\ gvs []
    (* Instantiating evaluate_apps *)
    \\ drule evaluate_apps
    \\ disch_then $ qspec_then ‘TL params’ mp_tac \\ gvs []
    \\ disch_then $ drule
    \\ disch_then $ qspecl_then [‘call_env’, ‘call_body’] mp_tac
    \\ impl_tac >- gvs [do_opapp_def, cml_fun_def, MAP_MAP_o, AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ pop_assum $ kall_tac
    (* Finished instantiating evaluate_apps *)
    \\ ‘cml_param = HD params’ by (Cases_on ‘params’ \\ gvs [cml_fun_def])
    \\ gvs [evaluateTheory.dec_clock_def]
    \\ gvs [Abbr ‘call_body’]
    \\ ‘LIST_REL (λn v. nsLookup call_env₁.v (Short n) = SOME v) params cml_vs’ by
      (gvs [Abbr ‘call_env₁’, Abbr ‘call_env’]
       \\ DEP_REWRITE_TAC [nsappend_alist_to_ns_nsbind]
       \\ Cases_on ‘params = []’ \\ gvs []
       \\ gvs [SNOC_LAST_FRONT, REVERSE_TL, SNOC_HD_REVERSE_TL]
       \\ irule list_rel_nslookup_nsappend
       \\ gvs [Abbr ‘params’, GSYM MAP_MAP_o])
    \\ drule evaluate_set_up_in_refs
    \\ disch_then $
         qspecl_then
           [‘t₁ with clock := ck' + t₁.clock - 1’, ‘cml_body'’] assume_tac
    \\ gvs []
    \\ irule_at Any refv_same_rel_trans
    \\ qexists ‘t₁.refs’ \\ gvs []
    \\ ‘refv_same_rel t₁.refs t''.refs’ by
      (irule_at Any refv_same_rel_append_imp
       \\ qexists ‘MAP Refv cml_vs’ \\ gvs [])
    \\ namedCases_on ‘r’ ["", "v err"] \\ gvs []
    \\ gvs [state_rel_def, restore_locals_def]
    \\ irule state_rel_locals_rel
    \\ gvs [SF SFY_ss])
  >~ [‘Forall var term’] >-
   (gvs [from_exp_def])
  >~ [‘Lit l’] >-
   (qexists ‘0’
    \\ Cases_on ‘l’
    \\ gvs [evaluate_exp_def, from_lit_def, from_exp_def, evaluate_def]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’
    \\ gvs [evaluate_def, do_con_check_def, env_rel_def, has_basic_cons_def,
            build_conv_def, Boolv_def, bool_type_num_def])
  >~ [‘Var name’] >-
   (qexists ‘0’
    \\ gvs [evaluate_exp_def, CaseEq "option"]
    \\ drule_all read_local_some_imp \\ rpt strip_tac
    \\ gvs [from_exp_def, cml_read_var_def]
    \\ gvs [evaluate_def, do_app_def, state_rel_def])
  >~ [‘If grd thn els’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy grd’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["grd_v", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [])
    \\ namedCases_on ‘do_cond grd_v thn els’ ["", "branch"] \\ gvs []
    \\ gvs [oneline do_cond_def, CaseEq "value"]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ gvs [do_if_def]
    \\ irule refv_same_rel_trans \\ gvs [SF SFY_ss])
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ qexists ‘ck’
    \\ Cases_on ‘uop’ \\ gvs [from_un_op_def, evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ gvs [do_uop_def, CaseEqs ["value", "option"]]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ gvs [do_if_def, evaluate_def, do_con_check_def, build_conv_def,
            env_rel_def, has_basic_cons_def, Boolv_def, bool_type_num_def])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e₀’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁, _)’]
    \\ gvs [evaluate_def]
    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >- (qexists ‘ck’ \\ gvs [])
    \\ rename [‘val_rel _ dfy_v₀ cml_v₀’]
    \\ Cases_on ‘do_sc bop dfy_v₀’ \\ gvs []
    >- (* Short-circuiting *)
     (qexists ‘ck’
      \\ gvs [oneline do_sc_def, val_rel_cases, evaluate_def, from_bin_op_def,
              do_log_def, Boolv_def, do_if_def, do_con_check_def, env_rel_def,
              build_conv_def, bool_type_num_def, env_rel_def,
              has_basic_cons_def, AllCaseEqs()])
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy e₁’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ ‘¬is_fresh « l»’ by gvs [is_fresh_def, isprefix_isprefix]
    \\ drule_all state_rel_env_push_not_fresh
    \\ disch_then $ qspec_then ‘cml_v₀’ assume_tac
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_basic_cons_def] \\ rpt strip_tac \\ res_tac)
    \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ ‘refv_same_rel t.refs t₂.refs’ by
      (irule refv_same_rel_trans \\ gvs [SF SFY_ss])
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ drule state_rel_env_pop_not_fresh \\ gvs []
    \\ disch_then $ drule \\ rpt strip_tac \\ gvs []
    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >- (Cases_on ‘bop’
        \\ gvs [oneline do_sc_def, val_rel_cases, from_bin_op_def,
                evaluate_def, do_log_def, do_if_def, AllCaseEqs()])
    \\ rename [‘val_rel _ dfy_v₁ cml_v₁’]
    \\ Cases_on ‘do_bop bop dfy_v₀ dfy_v₁’ \\ gvs []
    \\ Cases_on ‘bop = Div’ \\ gvs [] >-
     (gvs [do_bop_def, AllCaseEqs()]
      \\ gvs [from_bin_op_def, EDIV_DEF]
      \\ gvs [evaluate_def, do_app_def, do_if_def, opb_lookup_def]
      \\ Cases_on ‘0 < i₁’
      \\ gvs [evaluate_def, do_app_def, opn_lookup_def, Boolv_def])
    \\ Cases_on ‘bop = Eq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on ‘dfy_v₀’ ["i", "b", "str", "len dfy_loc"] \\ gvs []
      \\ namedCases_on ‘dfy_v₁’ ["i'", "b'", "str'", "len' dfy_loc'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [do_eq_def, lit_same_type_def, Boolv_def, ctor_same_type_def,
                same_type_def])
      >~ [‘do_eq (Conv _ _) (Conv _ _)’] >-
       (drule_all state_rel_array_loc_INJ \\ rpt strip_tac
        \\ drule (INST_TYPE [“:α” |-> “:num”, “:β” |-> “:num”] INJ_FLOOKUP_IMP)
        \\ disch_then $ qspecl_then [‘dfy_loc’, ‘dfy_loc'’] assume_tac
        \\ gvs [do_eq_def, lit_same_type_def]
        \\ Cases_on ‘len = len'’ \\ gvs []
        \\ Cases_on ‘dfy_loc = dfy_loc'’ \\ gvs [])
      \\ gvs [do_eq_def, lit_same_type_def])
    \\ Cases_on ‘bop = Neq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on
           ‘dfy_v₀’ ["i", "b", "dfy_str", "len dfy_loc"] \\ gvs []
      \\ namedCases_on
           ‘dfy_v₁’ ["i'", "b'", "dfy_str'", "len' dfy_loc'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [evaluate_def, do_eq_def, lit_same_type_def, Boolv_def,
                ctor_same_type_def, same_type_def, do_if_def, do_con_check_def,
                build_conv_def, env_rel_def, has_basic_cons_def,
                bool_type_num_def])
      >~ [‘do_eq (Conv _ _) (Conv _ _)’] >-
       (drule_all state_rel_array_loc_INJ \\ rpt strip_tac
        \\ drule (INST_TYPE [“:α” |-> “:num”, “:β” |-> “:num”] INJ_FLOOKUP_IMP)
        \\ disch_then $ qspecl_then [‘dfy_loc’, ‘dfy_loc'’] assume_tac
        \\ gvs [do_eq_def, lit_same_type_def]
        \\ Cases_on ‘len = len'’ \\ gvs []
        \\ Cases_on ‘dfy_loc = dfy_loc'’
        \\ gvs [do_if_def, evaluate_def, do_con_check_def, env_rel_def,
                build_conv_def, Boolv_def, bool_type_num_def,
                has_basic_cons_def])
      >~ [‘do_eq (Litv (IntLit _)) (Litv (IntLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘i' = i’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_basic_cons_def])
      >~ [‘do_eq (Litv (StrLit _)) (Litv (StrLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘dfy_str = dfy_str'’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_basic_cons_def]))
      \\ gvs [oneline do_bop_def, do_sc_def, AllCaseEqs()]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def, opb_lookup_def, opn_lookup_def,
              do_log_def, do_if_def])
  >~ [‘ArrLen arr’] >-
   (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ qexists ‘ck’
    \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs []
    >- (gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def,
             evaluate_def])
    \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs []
    \\ gvs [oneline get_array_len_def, AllCaseEqs()]
    \\ gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def]
    \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, pat_bindings_def,
            cml_tup_vname_def, num_to_str_11]
    \\ Cases_on ‘env_cml.v’
    \\ gvs [alist_to_ns_def, nsAppend_def, nsLookup_def, num_to_str_11])
  >~ [‘ArrSel arr idx’] >-
   (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs []
    >- (qexists ‘ck’
        \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
        \\ gvs [evaluate_def])
    \\ gvs [evaluate_def]
    \\ rename [‘val_rel _ dfy_arr cml_arr’]
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ ‘¬is_fresh « arr»’ by gvs [is_fresh_def, isprefix_isprefix]
    \\ drule_all state_rel_env_push_not_fresh \\ gvs []
    \\ disch_then $ qspec_then ‘cml_arr’ assume_tac \\ gvs []
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_basic_cons_def] \\ rpt strip_tac \\ res_tac)
    \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ drule state_rel_env_pop_not_fresh \\ gvs []
    \\ disch_then $ drule
    \\ rpt strip_tac \\ gvs []
    \\ ‘refv_same_rel t.refs t₂.refs’ by
      (irule refv_same_rel_trans \\ gvs [SF SFY_ss])
    \\ reverse $ namedCases_on ‘r’ ["idx_v",  "err"] \\ gvs []
    \\ namedCases_on ‘index_array s₂ dfy_arr idx_v’ ["", "elem"] \\ gvs []
    \\ gvs [oneline index_array_def, oneline val_to_num_def, CaseEq "value",
            CaseEq "option", CaseEq "heap_value"]
    \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
    \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, cml_tup_vname_def,
            pat_bindings_def, num_to_str_11]
    \\ Cases_on ‘env_cml.v’ \\ gvs []
    \\ gvs [nsOptBind_def, nsBind_def, alist_to_ns_def, nsAppend_def,
            nsLookup_def]
    \\ gvs [do_app_def]
    \\ drule_all state_rel_llookup \\ rpt strip_tac \\ gvs []
    \\ gvs [INT_ABS]
    \\ drule LIST_REL_LENGTH \\ rpt strip_tac
    \\ gvs [LLOOKUP_EQ_EL, LIST_REL_EL_EQN])
  >~ [‘map_from_exp []’] >-
   (qexists ‘0’ \\ gvs [from_exp_def, evaluate_exp_def, evaluate_def])
  >~ [‘map_from_exp (e::es)’] >-
   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ reverse $ namedCases_on ‘r’ ["cml_e",  "err"] \\ gvs []
    >- (qexists ‘ck’
        \\ rename [‘_::cml_es’]
        \\ Cases_on ‘cml_es’ \\ gvs [evaluate_def])
    \\ namedCases_on ‘es’ ["", "e' es"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [evaluate_exp_def, from_exp_def])
    \\ namedCases_on ‘evaluate_exps s₁ env_dfy (e'::es')’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ ‘refv_same_rel t.refs t₂.refs’ by
      (irule refv_same_rel_trans \\ gvs [SF SFY_ss])
    \\ reverse $ Cases_on ‘r’ \\ gvs [evaluate_def])
QED

Theorem correct_from_stmt:
  ∀s env_dfy stmt_dfy s' r_dfy lvl (t: 'ffi cml_state) env_cml e_cml m l.
    evaluate_stmt s env_dfy stmt_dfy = (s', r_dfy) ∧
    from_stmt stmt_dfy lvl = INR e_cml ∧ state_rel m l s t env_cml ∧
    env_rel env_dfy env_cml ∧ is_fresh_stmt stmt_dfy ∧
    r_dfy ≠ Rstop (Serr Rtype_error)
    ⇒ ∃ck (t': 'ffi cml_state) m' r_cml.
        evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
        (t', r_cml) ∧
        refv_same_rel t.refs t'.refs ∧ state_rel m' l s' t' env_cml ∧
        m ⊑ m' ∧ stmt_res_rel r_dfy r_cml
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, evaluate_def, do_con_check_def,
         build_conv_def]
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, evaluate_def, do_con_check_def,
         build_conv_def]
    \\ ‘env_dfy.is_running’ by gvs [env_rel_def] \\ gvs []
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_stmt s env_dfy stmt₁’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
    \\ first_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def, nsOptBind_def]
    \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs []
        \\ namedCases_on ‘stp’ ["", "err"] \\ gvs [SF SFY_ss]
        \\ Cases_on ‘err’ \\ gvs [SF SFY_ss])
    \\ last_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₂’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ qexists ‘ck' + ck’ \\ gvs []
    \\ irule_at Any refv_same_rel_trans
    \\ qexistsl [‘t₁.refs’, ‘m₂’] \\ gvs []
    \\ irule_at Any SUBMAP_TRANS \\ gvs [SF SFY_ss])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy tst’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [] \\ qexists ‘m’ \\ gvs [])
    \\ namedCases_on ‘do_cond tst_v thn els’ ["", "branch"] \\ gvs []
    \\ gvs [oneline do_cond_def, CaseEq "value"]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ last_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ qexists ‘ck' + ck’ \\ gvs []
    \\ gvs [do_if_def]
    \\ irule_at Any refv_same_rel_trans
    \\ qexistsl [‘t₁.refs’, ‘m₁’] \\ gvs [])
  >~ [‘Return’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, mk_id_def, evaluate_def,
         do_con_check_def, env_rel_def, has_basic_cons_def, build_conv_def]
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Assign lhss rhss’] >-
   (cheat)
  >~ [‘Dec local scope’] >-
   cheat
   (* (namedCases_on ‘local’ ["n ty"] \\ gvs [] *)
   (*  \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs []) *)
   (*  \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"] *)
   (*  \\ rename [‘evaluate_stmt _ _ _ = (s₂, r)’] *)
   (*  \\ ‘r_dfy = r’ by gvs [AllCaseEqs()] \\ gvs [] *)
   (*  \\ qspecl_then [‘s’, ‘n’] assume_tac declare_local_len_inc *)
   (*  \\ drule evaluate_stmt_len_locals \\ rpt strip_tac \\ gvs [] *)
   (*  \\ gvs [pop_local_def] *)
   (*  \\ namedCases_on ‘s₂.locals’ ["", "cur prev"] \\ gvs [] *)
   (*  (* \\ ‘0 < LENGTH s₂.locals’ by gvs [] *) *)
   (*  (* \\ drule locals_not_empty_pop_locals_some *) *)
   (*  (* \\ disch_then $ qx_choose_then ‘s₃’ assume_tac \\ gvs [] *) *)
   (*  \\ last_x_assum drule *)
   (*  \\ disch_then $ *)
   (*       qspecl_then *)
   (*         [‘t with refs := t.refs ++ [Refv (Litv (IntLit 0))]’, *)
   (*          ‘env_cml with v := *)
   (*             nsOptBind (SOME (explode n)) (Loc T (LENGTH t.refs)) env_cml.v’, *)
   (*          ‘m’, *)
   (*          ‘l |+ (n, (LENGTH t.refs))’] *)
   (*         mp_tac *)
   (*  \\ impl_tac >- cheat *)
   (*  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₂’, ‘m₁’] mp_tac *)
   (*  \\ rpt strip_tac \\ gvs [] *)
   (*  \\ qexists ‘ck’ *)
   (*  \\ gvs [cml_new_refs_def] *)
   (*  \\ gvs [evaluate_def, do_app_def, store_alloc_def] *)
   (*  \\ drule refv_same_rel_append_imp \\ rpt strip_tac \\ gvs [] *)
   (*  \\ qexists ‘m₁’ \\ gvs [] *)
   (*  \\ gvs [state_rel_def] *)
   (*  \\ gvs [locals_rel_def] *)
  (*  \\ rpt strip_tac) *)
  >~ [‘While grd _ _ _ body’] >-
   (cheat)
  \\ cheat
QED

val _ = export_theory ();
