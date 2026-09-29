(*
  Module for converts between AST and s-expressions.
*)
Theory AstSexpProg
Ancestors
  words (* dimword{8,64} *)
  ast_sexp
  ml_translator
  SexpProg
Libs
  preamble
  ml_translatorLib  (* translation_extends, register_type, .. *)
  ml_progLib  (* open_module, open_local_block, .. *)

val _ = translation_extends "SexpProg"

Theorem option_case_guard[local]:
  (case OPTION_GUARD b of NONE => n | SOME x => s x) =
  (if b then s () else n)
Proof
  Cases_on ‘b’ >> simp [OPTION_GUARD_def]
QED

val apply_rewrites =
  SIMP_RULE std_ss [
    OPTION_BIND_eq_case,
    OPTION_IGNORE_BIND_def,
    option_case_guard,
    UNCURRY_SIMP, dimword_8, dimword_64
  ]

val _ = register_type “:ast$dec”

val _ = ml_prog_update $ open_module "AstSexp"

val r = translate ast_sexpTheory.from_option_def
val r = translate ast_sexpTheory.from_int_pair_def
val r = translate ast_sexpTheory.from_id_def
val r = translate ast_sexpTheory.from_lit_def
val r = translate ast_sexpTheory.from_shift_def
val r = translate ast_sexpTheory.from_arith_def
val r = translate ast_sexpTheory.from_word_size_def
val r = translate ast_sexpTheory.from_thunk_mode_def
val r = translate ast_sexpTheory.from_thunk_op_def
val r = translate ast_sexpTheory.from_opb_def
val r = translate ast_sexpTheory.from_test_def
val r = translate ast_sexpTheory.from_prim_type_def
val r = translate ast_sexpTheory.from_op_def

val r = translate ast_sexpTheory.from_ast_t_def
val r = translate ast_sexpTheory.from_pat_def
val r = translate ast_sexpTheory.from_lop_def
val r = translate ast_sexpTheory.from_locs_def
val r = translate ast_sexpTheory.from_exp_def
val r = translate ast_sexpTheory.from_ctor_def
val r = translate ast_sexpTheory.from_tdef_def
val r = translate ast_sexpTheory.from_type_def_def
val r = translate ast_sexpTheory.from_dec_def
val r = translate ast_sexpTheory.from_dec_list_def

val r = translate ast_sexpTheory.dest_atom_def
val r = translate ast_sexpTheory.dest_expr_def

val r = translate listTheory.EL
Theorem el_side[local]:
  ∀n xs. el_side n xs ⇔ n < LENGTH xs
Proof
  Induct >> Cases
  >> once_rewrite_tac [fetch "-" "el_side_def"]
  >> fs [CONTAINER_def]
QED
val _ = el_side |> update_precondition

val r = translate (ast_sexpTheory.to_int_pair_def |> apply_rewrites)
val r = translate ast_sexpTheory.dest_tagged_def
val r = translate (ast_sexpTheory.to_option_def |> apply_rewrites)

val r = translate (ast_sexpTheory.to_id_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_lit_def |> apply_rewrites)
val r = translate ast_sexpTheory.to_shift_def
val r = translate (ast_sexpTheory.to_arith_def |> apply_rewrites)
val r = translate ast_sexpTheory.to_word_size_def
val r = translate ast_sexpTheory.to_thunk_mode_def
val r = translate (ast_sexpTheory.to_thunk_op_def |> apply_rewrites)
val r = translate ast_sexpTheory.to_opb_def
val r = translate (ast_sexpTheory.to_test_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_prim_type_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_op_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_ast_t_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_pat_def |> apply_rewrites)
val r = translate ast_sexpTheory.to_lop_def
val r = translate (ast_sexpTheory.to_locs_def |> apply_rewrites)

val r = translate (listTheory.OPT_MMAP_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_exp_def |> apply_rewrites)  (* a bit slow *)
val r = translate (ast_sexpTheory.to_ctor_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_tdef_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_type_def_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_dec_def |> apply_rewrites)
val r = translate (ast_sexpTheory.to_dec_list_def |> apply_rewrites)
