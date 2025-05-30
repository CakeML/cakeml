(*
  Some tests for the compiler's lexer.
*)
open ASCIInumbersLib intLib;
open preamble;
open lexer_funTheory lexer_implTheory;

val _ = new_theory "lexerTests";

fun run_test test expected =
  let val result = EVAL (Term`MAP FST (lexer_fun ^test)`) |> concl |> rhs;
      val ok = term_eq expected result
  in
    if ok then
      ()
    else
      raise (Fail ("Failed lexer test: " ^ term_to_string test ^ "\n" ^ term_to_string result))
  end


val test1 = run_test ``"a"`` ``[AlphaT "a"]``;

val test2 = run_test ``"+"`` ``[SymbolT "+"]``;

val test3 = run_test ``"a+b"`` ``[AlphaT "a"; SymbolT "+"; AlphaT "b"]``;

val test4 = run_test ``"a_'_3''"`` ``[AlphaT "a_'_3''"]``;

val test5 = run_test ``"a_'_3''||bg+++l"`` ``[AlphaT "a_'_3''"; SymbolT "||"; AlphaT "bg"; SymbolT "+++"; AlphaT "l"]``;

val test6 = run_test ``"a_1'.b_2'"`` ``[LongidT (Mod "a_1'" End) "b_2'"]``;

val test7 = run_test ``"a1_'.++"`` ``[LongidT (Mod "a1_'" End) "++"]``;

val test10 = run_test ``"a.b.c"`` ``[LongidT (Mod "a" (Mod "b" End)) "c"]``

val test11 = run_test ``"a{"`` ``[AlphaT "a"; LbraceT]``

val test12 = run_test ``"1"`` ``[IntT 1]``

val test13 = run_test ``"~1~1a~12"`` ``[IntT ~1; IntT ~1; AlphaT "a"; IntT ~12]``

val test14 = run_test ``"'"`` ``[TyvarT "'"]``;

val test15 = run_test ``"+'4a--"`` ``[SymbolT "+"; TyvarT "'4a"; SymbolT "--"]``;

val test16 = run_test ``"l'4a--"`` ``[AlphaT "l'4a"; SymbolT "--"]``;

val test17 = run_test ``"++a.b%$"`` ``[SymbolT "++"; LongidT (Mod "a" End) "b"; SymbolT "%$"]``;

val test19 = run_test ``"~55+~4"`` ``[IntT ~55; SymbolT "+~"; IntT 4]``;

val test20 = run_test ``"a."`` ``[LexErrorT]``;

val test21 = run_test “"\"1a\\001\\nb\""” “[StringT "1a\001\nb"]”

val test22 = run_test “"\"\\a\\b\\r\""” “[StringT "\a\b\r"]”

val test23 = run_test “"#\"\\n\""” “[CharT #"\n"]”

val _ = export_theory ();
