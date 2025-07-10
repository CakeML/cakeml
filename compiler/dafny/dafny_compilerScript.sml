(*
  Definition of the Dafny to CakeML compiler.
*)

open preamble
open result_monadTheory
open dafny_sexpTheory
open sexp_to_dafnyTheory
open dafny_to_cakemlTheory
open dafny_freshenTheory
open fromSexpTheory
open simpleSexpParseTheory

val _ = new_theory "dafny_compiler";

(* Trusted frontend *)
Definition frontend_def:
  frontend (dfy_sexp: string) =
  do
    dfy_sexp <- lex dfy_sexp;
    dfy_sexp <- parse dfy_sexp;
    to_program dfy_sexp
  od
End

Definition compile_def:
  compile dfy = from_program (freshen_program dfy)
End

Definition dfy_to_cml_def:
  dfy_to_cml (dfy_sexp: string) =
  do
    dfy <- frontend dfy_sexp;
    compile dfy
  od
End

(* If compilation failed, outputs a program that prints the error message in
   the result monad. *)
Definition unpack_def:
  unpack m =
  (case m of
   | INR d => d
   | INL s =>
     [Dlet unknown_loc Pany (cml_fapp [] "print" [Lit (StrLit (explode s))])])
End

(* Converts the monad with the CakeML AST into a string with its S-Expression.
 * Errors are converted into a simple CakeML program which prints the error. *)
Definition cmlm_to_str_def:
  cmlm_to_str cmlm =
  let
    cml = unpack cmlm;
    cml_sexp = listsexp (MAP decsexp cml);
  in
    print_sexp cml_sexp
End

Definition main_function_def:
  main_function (input: mlstring): mlstring =
  let
    input = explode input;
    cmlm = dfy_to_cml input;
    cml_str = cmlm_to_str cmlm;
  in
    implode cml_str
End

val _ = export_theory ();
