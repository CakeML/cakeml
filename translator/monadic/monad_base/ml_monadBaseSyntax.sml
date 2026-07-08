(*
  ML functions for manipulating HOL terms and types involving the
  state-and-exception monad defined in ml_monadBase.
*)
structure ml_monadBaseSyntax :> ml_monadBaseSyntax = struct
  open HolKernel boolLib pairSyntax ml_monadBaseTheory;
  val s1 = HolKernel.syntax_fns1 "ml_monadBase"
  val s2 = HolKernel.syntax_fns2 "ml_monadBase"
  val s3 = HolKernel.syntax_fns3 "ml_monadBase"
  (* types *)
  fun mk_exc_ty (a, b) =
    mk_thy_type{Thy="ml_monadBase",Tyop="exc",Args=[a,b]};
  val exc_ty = mk_exc_ty(alpha, beta);
  fun mk_M_ty (a, b, c) =
    a --> mk_prod(mk_exc_ty(b, c), a);
  val M_ty = mk_M_ty(alpha, beta, gamma);
  (* exc constructors *)
  val (M_success_tm, mk_M_success, dest_M_success, is_M_success) =
    s1 "M_success";
  val (M_failure_tm, mk_M_failure, dest_M_failure, is_M_failure) =
    s1 "M_failure";
  (* monad operations *)
  val (st_ex_bind_tm, mk_st_ex_bind, dest_st_ex_bind, is_st_ex_bind) =
    s2 "st_ex_bind";
  val (st_ex_ignore_bind_tm, mk_st_ex_ignore_bind, dest_st_ex_ignore_bind,
       is_st_ex_ignore_bind) =
    s2 "st_ex_ignore_bind";
  val (st_ex_return_tm, mk_st_ex_return, dest_st_ex_return,
       is_st_ex_return) =
    s1 "st_ex_return";
  val (otherwise_tm, mk_otherwise, dest_otherwise, is_otherwise) =
    s2 "otherwise";
  val (run_tm, mk_run, dest_run, is_run) =
    s2 "run";
  (* array operations *)
  val (Marray_length_tm, mk_Marray_length, dest_Marray_length,
       is_Marray_length) =
    s1 "Marray_length";
  val (Marray_sub_tm, mk_Marray_sub, dest_Marray_sub, is_Marray_sub) =
    s3 "Marray_sub";
  val (Marray_alloc_tm, mk_Marray_alloc, dest_Marray_alloc,
       is_Marray_alloc) =
    s3 "Marray_alloc";
  (* Marray_update has 5 args — no syntax_fns5, so just provide the constant *)
  val Marray_update_tm =
    prim_mk_const{Thy="ml_monadBase",Name="Marray_update"};
end
