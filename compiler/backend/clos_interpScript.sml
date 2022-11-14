(*
  Implementation of interpreter for closLang expressions written in closLang.
*)
open preamble closLangTheory backend_commonTheory;

val _ = new_theory "clos_interp";

val _ = set_grammar_ancestry ["closLang", "backend_common"];

Definition clos_interpreter_def:
  clos_interpreter = Op None (Cons 0) [] (* TODO: implement *)
End

Definition compile_init_def:
  compile_init b =
    Let None [Op None AllocGlobal [];
              if b then
                Fn (mlstring$strlit "clos_interpreter") NONE NONE 1 clos_interpreter
              else
                Op None (Cons 0) []]
      (Op None (SetGlobal 0) [Var None 1])
End

Definition attach_interpreter_def:
  attach_interpreter xs =
    compile_init (has_install_list xs) :: xs
End

Definition insert_interp_def:
  insert_interp xs = (xs : closLang$exp list)
End

(*

Definition compile_inc_def:
  ...
End

*)

val _ = export_theory();
