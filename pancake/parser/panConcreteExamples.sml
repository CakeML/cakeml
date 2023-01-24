open HolKernel Parse boolLib bossLib stringLib numLib intLib;
open preamble panPtreeConversionTheory;

val _ = new_theory "panConcreteExamples";

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
end

fun lex_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “pancake_lex ^code”
end

fun parse_tree_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse (pancake_lex ^code)”
end

(** Copied from panPtreeConversion *)
fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_to_ast ^code”
  end

(** Examples can be written using quoted strings and passed to the ML
    function parse_pancake. *)

(** Pancake programs consist of a sequence of blocks of statements. *)

(** Blocks: Declarations, Conditionals (If-Then-Else), Loops (While) *)

(** Conditionals: An if-block without an alternative. The bodies of the
    conditional are Pancake programs (in this case a single assignment
    statement). NB: Statements end with a semi-colon, blocks do not. *)
val ex1 = ‘if 2 >= 1 { x = 2; }’;

val treeEx1 = parse_pancake ex1;

(** We also have a selection of boolean operators and we can call
    functions. A struct value encloses expressions within chevrons
    (‘<>’). *)
val ex2 = ‘if b & (a ^ c) & d {
             foo(1, <2, 3>);
           } else {
             goo(4, 5, 6);
           }’;

val treeEx2 = parse_pancake ex2;

(** We also have a selection of boolean operators and
    a ‘return’ statement. *)
(** FIXME: Add ‘true’ and ‘false’ to EBaseNT *)
val ex3 = ‘if b & (a ^ c) & d { return true; } else { return false; }’;

val treeEx3 = parse_pancake ex3;

(** Loops: standard looping construct. *)

val ex4 = ‘while b | c {
             if x >= 5 {
               break;
             } else {
               strb y, 8; // store byte
               #foo(x y k z); // ffi function call with pointer args
               x = x + 1;
             }
           }’;

val treeEx4 = parse_pancake ex4;

(** Declarations: intended semantics is the variable is in-scope
    in the body. *)

val ex5 = ‘var b = 5 {
             b = b + 1;
             if b >= 5 {
               raise Err 5;
             }
           }’;

val treeEx5 = parse_pancake ex5;

(** Statments. *)

(** We can assign boolean expressions to variables. *)
(** FIXME: Does not parse correctly. *)
(** Expected: Xor (And b a) (And c d) *)
val exN = ‘x = b & a ^ c & d;’;

val treeExN = parse_pancake exN;

val _ = export_theory();
