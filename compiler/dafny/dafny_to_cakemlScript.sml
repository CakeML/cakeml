(*
  Defines the translation of Dafny's to CakeML's AST.
*)

open preamble
open dafny_astTheory
open astTheory  (* CakeML AST *)
open extension_astTheory
open mlintTheory  (* num_to_str *)
open result_monadTheory

val _ = new_theory "dafny_to_cakeml";

(* TODO Remove mk_id; unnecessary *)

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

(* S = "Smart" in the sense that it doesn't create singleton tuples. *)
Definition Stuple_def:
  Stuple [e] = e ∧
  Stuple es = Tuple es
End

Definition Pstuple_def:
  Pstuple [pvar] = pvar ∧
  Pstuple pvars = Pcon NONE pvars
End

(* Generates code of the form: case cml_te of ( 0,  1, ...) => cml_e *)
Definition cml_tup_case_def:
  cml_tup_case len cml_te cml_e =
  let tup_pvars = GENLIST (λn. Pvar (cml_tup_vname n)) len in
    Mat cml_te [Pstuple tup_pvars, cml_e]
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
  cml_alloc_arr len init =
  let len_n = " len" in
    Let (SOME len_n) len
        (Tuple [Var (Short len_n); App Aalloc [Var (Short len_n); init]])
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
  from_rhs_exp (ExpRhs e) = from_exp e ∧
  from_rhs_exp (ArrAlloc len init) =
  do
    cml_len <- from_exp len;
    cml_init <- from_exp init;
    return (cml_alloc_arr cml_len cml_init)
  od
End

Definition cml_tmp_vname_def:
  cml_tmp_vname idx = explode («_tmp» ^ (num_to_str idx))
End

Definition assign_single_def:
  (assign_single (VarLhs v) cml_rhs =
     return (App Opassign [Var (Short (explode v)); cml_rhs])) ∧
  (assign_single (ArrSelLhs arr idx) cml_rhs =
   do
     cml_arr <- from_exp arr;
     cml_idx <- from_exp idx;
     (* Force left-to-right evaluation order *)
     n_arr <<- " arr";
     return (Let (SOME n_arr) cml_arr
                 (App Aupdate [cml_get_arr_data (Var (Short n_arr));
                               cml_idx; cml_rhs]))
   od)
End

Definition par_assign_def:
  par_assign lhss rhss =
  do
    vars <<- GENLIST (λn. cml_tup_vname n) (LENGTH rhss);
    ass <- if LENGTH lhss = LENGTH rhss
           then result_mmap2 assign_single lhss (MAP (Var ∘ Short) vars)
           else return [];
    return (Mat (Stuple (REVERSE rhss))
                [Pstuple (MAP Pvar (REVERSE vars)), Seqs ass])
  od
End

Definition to_string_def:
  (to_string cml_e BoolT =
     return (If cml_e (Lit (StrLit "True")) (Lit (StrLit "False")))) ∧
  (* TODO Is this the best way to print an integer? *)
  (to_string cml_e IntT =
     return (cml_fapp ["Int"] "int_to_string" [Lit (Char #"-"); cml_e])) ∧
  (to_string cml_e StrT = return cml_e) ∧
  (to_string cml_e _ = fail «to_string: Unsupported»)
End

Definition loop_name_def:
  loop_name lvl = explode (« w» ^ (num_to_str lvl))
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
  from_stmt (Assign ass) _ =
  do
    cml_rhss <- result_mmap from_rhs_exp (MAP SND ass);
    par_assign (MAP FST ass) cml_rhss
  od ∧
  from_stmt (While grd _ _ _ body) lvl =
  do
    cml_grd <- from_exp grd;
    cml_body <- from_stmt body (lvl + 1);
    run_loop <<- cml_fapp [] (loop_name lvl) [Unit];
     (* Example (see The Definition of Standard ML, Appendix A):
        let val rec w0 = fn () =>
          if cml_grd then (cml_body; w0()) else ()
        in
          w0()
        end *)
    return (Letrec [(loop_name lvl, "",
                     If cml_grd (Let NONE cml_body run_loop) Unit)]
                   run_loop)
  od ∧
  from_stmt (Print e t) _ =
  do
    cml_e <- from_exp e;
    cml_str <- to_string cml_e t;
    (* TODO Is this the best way to print a string? *)
    return (cml_fapp [] "print" [cml_str])
  od ∧
  from_stmt (MetCall lhss n args) _ =
  do
    cml_args <- map_from_exp args;
    cml_call <<- cml_fapp [] ("dfy_" ++ (explode n)) (REVERSE cml_args);
    (* Method returns a tuple of size outs_len, so we use case and assign
       each component to the corresponding left-hand side. *)
    outs_len <<- LENGTH lhss;
    outs <<- GENLIST (λn. Var (Short (cml_tup_vname n))) outs_len;
    cml_assign <- par_assign lhss outs;
    return (cml_tup_case outs_len cml_call cml_assign);
  od ∧
  from_stmt Return _ =
    return (Raise (Con (SOME (mk_id [] "Return")) []))
End

(* Shadows the parameters with references with the same name (and value). *)
Definition set_up_in_refs_def:
  set_up_in_refs [] cml_e = cml_e ∧
  set_up_in_refs (n::ns) cml_e =
    Let (SOME n) (App Opref [Var (Short n)]) (set_up_in_refs ns cml_e)
End

(* Sets up the in parameters. *)
Definition set_up_cml_fun_def:
  set_up_cml_fun n ins cml_body =
    let in_ns = MAP (explode ∘ FST) ins in
    let cml_body = set_up_in_refs in_ns cml_body in
    (* Reversing the parameters is an easy way to get left-to-right evaluation
       on them *)
    let (cml_param, cml_body) = cml_fun (REVERSE in_ns) cml_body in
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
      cml_tup <<- Stuple (MAP cml_read_var out_ns);
      cml_body <<-
        Handle cml_body
          [(Pcon (SOME (mk_id [] "Return")) [], cml_tup)];
      cml_body <<- cml_new_refs out_ns cml_body;
      return (set_up_cml_fun n ins cml_body)
    od
  | Function n ins _ _ _ _ body =>
    do
      cml_body <- from_exp body;
      return (set_up_cml_fun n ins cml_body)
    od
End

(* TODO from_program in ProofScript *)


(* Testing *)
(* open dafny_sexpTheory *)
(* open sexp_to_dafnyTheory *)
(* open TextIO *)
(* open dafny_transformTheory *)

(* val _ = astPP.disable_astPP(); *)
(* val _ = astPP.enable_astPP(); *)

(* val inStream = TextIO.openIn "./tests/output/binary_search.dfy.sexp" *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)

(* val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand; *)
(* val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand; *)
(* val dafny_r = EVAL “(to_program ^parse_r)” |> concl |> rhs |> rand; *)
(* val fresh_vars_r = EVAL “(use_fresh_vars ^dafny_r)” |> concl |> rhs; *)
(* val cakeml_r = EVAL “(from_program ^fresh_vars_r)” |> concl |> rhs |> rand; *)

val _ = export_theory ();
