(*
  Some tests for the pancake lexer.
*)
open ASCIInumbersLib intLib;
open preamble;
open panLexerTheory;

val _ = new_theory "panLexerTests";

fun run_test test expected =
  let val result = EVAL (Term`MAP FST (pancake_lex ^test)`) |> concl |> rhs;
      val ok = term_eq expected result
  in
    if ok then
      term_to_string test ^ " >> " ^ term_to_string result
    else
      raise (Fail ("Failed lexer test: " ^ term_to_string test ^ "\n" ^ term_to_string result))
  end


val test1 = run_test ``"a"`` ``[IdentT "a"]``;

val test2 = run_test ``"+"`` ``[PlusT]``; (* SymbolT "+" *)

val test3 = run_test ``"a+b"`` ``[IdentT "a"; PlusT; IdentT "b"]``;

val test4 = run_test ``"false"`` ``[FalseT]``; (* LexErrorT *)

val test4 = run_test ``"true"`` ``[TrueT]``; (* LexErrorT *)

val _ = export_theory ();
