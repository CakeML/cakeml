open preamble;
open lexer_funTheory;

val _ = new_theory "lexerTests";

fun run_test test expected = 
  let val result = EVAL (Term`lexer_fun ^test`) |> concl |> rhs;
      val ok = term_eq expected result
  in
    if ok then
      ()
    else
      raise (Fail ("Failed lexer test: " ^ term_to_string result))
  end


val test1 = run_test ``"a"`` ``[AlphaT "a"]``;

val test2 = run_test ``"+"`` ``[SymbolT "+"]``;

val test3 = run_test ``"a+b"`` ``[AlphaT "a"; SymbolT "+"; AlphaT "b"]``;

val test4 = run_test ``"a_'_3''"`` ``[AlphaT "a_'_3''"]``;

val test5 = run_test ``"a_'_3''||bg+++l"`` ``[AlphaT "a_'_3''"; SymbolT "||"; AlphaT "bg"; SymbolT "+++"; AlphaT "l"]``;

val test6 = run_test ``"a_1'.b_2'"`` ``[LongidT "a_1'" "b_2'"]``;

val test7 = run_test ``"a1_'.++"`` ``[LongidT "a1_'" "++"]``; (* Fails *)

val test8 = run_test ``"++.a1"`` ``[LongidT "++" "a1"]``; (* Fails *)

val test9 = run_test ``"++.--"`` ``[LongidT "++" "--"]``;

val test10 = run_test ``"a.b.c"`` ``[LexErrorT]``

val test11 = run_test ``"a{"`` ``[AlphaT "a"; LbraceT]``

val test12 = run_test ``"1"`` ``[IntT 1]`` (* Fails *)

val test13 = run_test ``"~1~1a~12"`` ``[IntT ~1; IntT ~1; AlphaT "a"; IntT ~12]`` (* Fails *)

val test14 = run_test ``"'"`` ``[TyvarT "'"]``;

val test15 = run_test ``"+'4a--"`` ``[SymbolT "+"; TyvarT "'4a"; SymbolT "--"]``;

val test16 = run_test ``"l'4a--"`` ``[AlphaT "l'4a"; SymbolT "--"]``;

val test17 = run_test ``"++a.b%$"`` ``[SymbolT "++"; LongidT "a" "b"; SymbolT "%$"]``;

val test18 = run_test ``"a++.%$b"`` ``[AlphaT "a"; LongidT "++" "%$"; AlphaT "b"]``;

val test19 = run_test ``"~55+~4"`` ``[IntT ~55; SymbolT "+~"; IntT 4]`` (* Fails *)

val test20 = run_test ``"a.b!!!.="`` ``[LongidT "a" "b"; LongidT "!!!" "="]``

val _ = export_theory ();
