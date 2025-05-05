(*
  Defines the translation of Dafny's to CakeML's AST.
*)

open preamble
open cfTacticsLib  (* process_topdecs *)
open dafny_astTheory
open astTheory  (* CakeML AST *)
open mlintTheory  (* num_to_str *)
open result_monadTheory

val _ = new_theory "dafny_to_cakeml";

(* Helpers to generate CakeML *)

(* Shortcuts to some constructors *)
Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload Unit = “Con NONE []”
Overload Tuple = “λes. Con NONE es”
Overload None = “Con (SOME (Short "None")) []”
Overload Some = “λe. Con (SOME (Short "Some")) [e]”

(* Converts a HOL list of CakeML expressions into a CakeML list. *)
Definition cml_list_def:
  (cml_list [] = Con (SOME (Short "[]")) []) ∧
  (cml_list (x::rest) =
   Con (SOME (Short "::")) [x; cml_list rest])
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

Definition cml_fapp_aux_def:
  cml_fapp_aux id cml_es =
  (case cml_es of
   | [] => App Opapp [id; Unit]
   | [cml_e] => App Opapp [id; cml_e]
   | (cml_e::rest) => App Opapp [(cml_fapp_aux id rest); cml_e])
End

Definition cml_fapp_def:
  cml_fapp mns n cml_es = cml_fapp_aux (Var (mk_id mns n)) (REVERSE cml_es)
End

Definition cml_read_var_def:
  cml_read_var v = App Opderef [Var (Short (explode v))]
End

(* Generates strings of the form _0, _1, etc., to be used for matching tuples *)
Definition cml_tup_vname_def:
  cml_tup_vname (idx : num) = explode («_» ^ (num_to_str idx))
End

(* Generates code of the form: case cml_te of (_0, _1, ...) => cml_e *)
Definition cml_tup_case_def:
  cml_tup_case len cml_te cml_e =
  let tup_pvars = GENLIST (λn. Pvar (cml_tup_vname n)) len in
    Mat cml_te [Pcon NONE tup_pvars, cml_e]
End

(* Returns the tuple content at idx via pattern matching. *)
Definition cml_tup_select_def:
  cml_tup_select len cml_te (idx: num) =
  cml_tup_case len cml_te (Var (Short (cml_tup_vname idx)))
End

Definition cml_init_value_def:
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

(* Dafny to CakeML definitions *)

Definition from_lit_def:
  from_lit l =
  (case l of
   | BoolL b => if b then True else False
   | IntL i => Lit (IntLit i)
   | StrL s => Lit (StrLit (explode s)))
End

Definition from_un_op_def:
  from_un_op uop cml_e =
  (case uop of
   | Not => cml_fapp [] "not" [cml_e])
End

Definition from_bin_op_def:
  from_bin_op bop cml_e₀ cml_e₁ =
  (case bop of
   | Lt => App (Opb Lt) [cml_e₀; cml_e₁]
   | Le => App (Opb Leq) [cml_e₀; cml_e₁]
   | Ge => App (Opb Geq) [cml_e₀; cml_e₁]
   | Eq => App Equality [cml_e₀; cml_e₁]
   | Neq => (let eq = from_bin_op Eq cml_e₀ cml_e₁ in from_un_op Not eq)
   | Sub => App (Opn Minus) [cml_e₀; cml_e₁]
   | Add => App (Opn Plus) [cml_e₀; cml_e₁]
   | Mul => App (Opn Times) [cml_e₀; cml_e₁]
   | And => Log And cml_e₀ cml_e₁
   | Or => Log Or cml_e₀ cml_e₁
   | Imp =>
     (let not_e₀ = from_un_op Not cml_e₀ in from_bin_op Or not_e₀ cml_e₁)
   | Div => cml_fapp ["Dafny"] "ediv" [cml_e₀; cml_e₁])
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | (Neq, _, _) => bin_op_size Neq + 1
                           | (Imp, _, _) => bin_op_size Imp + 1
                           | (bop, _, _) => bin_op_size bop)’
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

Definition cml_arr_sel_def:
  cml_arr_sel cml_arr cml_idx = App Asub [cml_get_arr_data cml_arr; cml_idx]
End

Definition from_exp_def:
  from_exp e =
  (case e of
   | Lit l => return (from_lit l)
   | Var v => return (cml_read_var v)
   | If tst thn els =>
     do
       cml_tst <- from_exp tst;
       cml_thn <- from_exp thn;
       cml_els <- from_exp els;
       return (If cml_tst cml_thn cml_els)
     od
   | UnOp uop e =>
     do
       cml_e <- from_exp e;
       return (from_un_op uop cml_e)
     od
   | BinOp bop e₀ e₁ =>
     do
       cml_e₀ <- from_exp e₀;
       cml_e₁ <- from_exp e₁;
       return (from_bin_op bop cml_e₀ cml_e₁)
     od
   | ArrLen arr =>
     do
       cml_arr <- from_exp arr;
       return (cml_get_arr_dim cml_arr)
     od
   | ArrSel arr idx =>
     do
       cml_arr <- from_exp arr;
       cml_idx <- from_exp idx;
       return (cml_arr_sel cml_arr cml_idx)
     od
   | FunCall n args =>
     do
       cml_args <- map_from_exp args;
       return (cml_fapp [] (explode n) cml_args)
     od
   | Forall _ _ => fail «from_exp:Forall: Unsupported») ∧
  map_from_exp es =
  (case es of
   | [] => return []
   | (e::es) =>
     do
       cml_e <- from_exp e;
       cml_es <- map_from_exp es;
       return (cml_e::cml_es)
     od)
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
    (cml_param, cml_body) <<- cml_fun (MAP explode in_param_ns) cml_body;
    return (explode n, cml_param, cml_body)
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

(* Defines the Dafny module containing the Dafny runtime *)
Quote dafny_module = process_topdecs:
  structure Dafny =
  struct

  exception Return;

  (* Adapted from ABS and ediv from HOL's integerTheory *)
  fun abs n = if n < 0 then ~n else n;

  fun ediv i j = if 0 < j then i div j else ~(i div ~j);

  (* to_string functions *)
  fun bool_to_string b = if b then "True" else "False";

  fun int_to_string i = Int.int_to_string #"-" i;

  end
End

Definition from_program_def:
  from_program (Program mems) : (dec list) result =
  do
    cml_funs <- result_mmap from_member_decl mems;
    (* TODO Optimize this by only putting mutually recursive functions
       together *)
    cml_funs <<- Dletrec unknown_loc cml_funs;
    (* NOTE For now, we assume the every program has a method called Main that
       is not mutually recursive with anything else, takes no arguments, and
       returns nothing. *)
    cml_main <<- Dlet unknown_loc Pany (cml_fapp [] "Main" [Unit]);
    return (^dafny_module ++ [cml_funs; cml_main])
  od
End

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
