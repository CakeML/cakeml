(*
 * Definition of the Dafny to CakeML compiler.
 *)

open preamble

open result_monadTheory
open dafny_sexpTheory sexp_to_dafnyTheory dafny_to_cakemlTheory
open fromSexpTheory simpleSexpParseTheory

val _ = new_theory "dafny_compiler";

(* Wrapper to deal with the differt uses of monads *)
Definition sexp_program_m_def:
  sexp_program_m se =
  (case sexp_program se of
   | NONE => fail "sexp_program failed"
   | SOME x => return x)
End

(* Given a string containing containing the Dafny program as an S-Expression,
 * returns a string containing the corresponding CakeML program as an
 * S-Expression. *)
Definition dfy_to_cml_def:
  dfy_to_cml (dfy: string) =
  do
    dfy <- lex dfy;
    dfy <- parse dfy;
    dfy <- sexp_program_m dfy;
    compile dfy
  od
End

(* Converts the monad with the CakeML AST into a string with its S-Expression.
 * Errors are converted into a simple CakeML program which prints the error. *)
Definition cmlm_to_str_def:
  cmlm_to_str cml =
  print_sexp (listsexp (MAP decsexp (unpack cml)))
End

Definition main_function_def:
  main_function (input: mlstring): mlstring =
  implode (cmlm_to_str (dfy_to_cml (explode input)))
End

val _ = export_theory();
