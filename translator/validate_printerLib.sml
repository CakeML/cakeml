open intLib listSyntax optionSyntax;
open mmlParseTheory lexer_implTheory Print_astTheory ElabTheory;
open terminationTheory Print_astTerminationTheory;
open std_preludeTheory;

val _ = computeLib.add_funs [tree_to_list_def, tok_list_to_string_def];
val _ = computeLib.add_funs [elab_p_def, elab_e_def];

fun test_printer d =
let val str = (rhs o concl o EVAL) ``dec_to_sml_string ^d``;
    val toks = (rhs o concl o EVAL) ``(option_map FST o lex_until_toplevel_semicolon) ^str``;
    val ast1 = (rhs o concl o EVAL) ``(OPTION_JOIN o option_map parse_top) ^toks``;
    val ast2 = (rhs o concl o EVAL) ``(option_map (SND o SND o elab_top [] [])) ^ast1``;
    val res = if is_some ast2 then term_eq (snd (dest_comb (dest_some ast2))) d else false
in
  res
end

fun validate_print d =
  EVAL ``let d = ^d in
         case ((option_map (SND o SND o elab_top [] [])) o
               (OPTION_JOIN o option_map parse_top) o
               (option_map FST o lex_until_toplevel_semicolon) o
               dec_to_sml_string)
              d of
          SOME (Tdec d') => d' = d | NONE => F``;

val std_prelude_asts =
  (fst o strip_cons o rhs o concl) std_prelude_decls

val x = ref 0;
List.app (fn d => let val res = test_printer d in
                    ((if not res then
                        print "error: "
                      else
                        ());
                     print ((Int.toString (!x)) ^ "\n");
                     x := (!x) + 1)
                  end)
         std_prelude_asts;

(*

    val d = List.nth (std_prelude_asts,45)

0
1
2
3
4
5
6
7
8
9
10
error: 11
12
13
14
15
error: 16
17
18
19
error: 20
error: 21
error: 22
error: 23
24
25
26
27
28
error: 29
error: 30
error: 31
32
33
34
35
error: 36
37
38
error: 39
error: 40
41
42
43
error: 44
error: 45
error: 46
error: 47
error: 48
error: 49
error: 50
51
error: 52
error: 53
error: 54
55
56
57
error: 58
error: 59
error: 60
error: 61
error: 62
error: 63
error: 64
error: 65
error: 66
error: 67
error: 68
error: 69
error: 70
error: 71
72
73
74


^CException- Interrupt raised
*) 
