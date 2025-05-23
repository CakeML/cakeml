(**
 * Pancake concrete syntax examples
 * 9th May 2023: Updated with function declarations
 * March 2024: Updated with shared memory instructions
 *)
open HolKernel Parse boolLib bossLib stringLib numLib intLib;
open preamble panPtreeConversionTheory;
open helperLib;

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
    EVAL “parse_topdecs_to_ast ^code”
  end

val check_success = assert $ sumSyntax.is_inl o rhs o concl
val check_failure = assert $ sumSyntax.is_inr o rhs o concl

(** Examples can be written using quoted strings and passed to the ML
    function parse_pancake. *)

(** Pancake programs consist of a sequence of function declarations. *)

(** The body of each function consists of a sequence of blocks. *)

(** Blocks: Declarations, Conditionals (If-Then-Else), Loops (While) *)

(** Conditionals: An if-block without an alternative. The bodies of the
    conditional are Pancake programs (in this case a single assignment
    statement). NB: Statements end with a semi-colon, blocks do not. *)

(** Disclaimer: the next several examples (1-8) exist to showcase the syntax for certain
    language constructs and may not form well-behaved Pancake programs in practice:
    ex. missing variable declarations, lack of return statements, etc.*)
val ex1 = ‘
  fun cond() {
    if 2 >= 1 { x = 2; }
  }’;

val treeEx1 = check_success $ parse_pancake ex1;

(** We also have a selection of boolean operators and we can call
    functions. A struct value encloses expressions within chevrons
    (‘<>’). *)
val ex2 = ‘
  fun main() {
    if !b & (a ^ c) & d {
      return foo(1, <2, 3>);
        } else {
      return goo(4, 5, 6);
    }
  }’;

val treeEx2 = check_success $ parse_pancake ex2;

(** Logical operators (as opposed to bitwise operators) are && and || *)
val ex2_and_a_half = ‘
  fun main() {
    return(a && b && c || a || b ^ d);
  }’;

val treeEx2_and_a_half = check_success $ parse_pancake ex2_and_a_half;


(** We also have a selection of boolean operators and
    a ‘return’ statement. NOTE: all Pancake functions should end with a return statement.*)

val ex3 = ‘
  fun boolfun() {
    if b & (a ^ c) & d { return true; }
    else { return false; }
  }’;

val treeEx3 = check_success $ parse_pancake ex3;

(** Bool operators have higher precedence than comparators, so z is always 1*)
val ex3_and_a_half = ‘
  fun cmps () {
    var x = 2;
    var y = 3;
    var z = (x & y != 0);
    z = ((x & y) != 0);
    z = (y & x != 0);
    z = ((y & x) != 0);
}’;

val treeEx3_and_a_half = check_success $ parse_pancake ex3_and_a_half;


(** Loops: standard looping construct. *)

val ex4 = ‘
  fun loopy() {
    while b | c {
      if x >= 5 {
        break;
      } else {
        st8 y, 8; // store byte
        @foo(x,y,k,z); // ffi function call with pointer args
        x = x + 1;
        y = x + 1;
      }
    }
  }’;

val treeEx4 = check_success $ parse_pancake ex4;

val ex4' = ‘
  fun loopy() {
    while b | c {
      if x >= 5 {
        break;
      } else {
        st32 y, 8; // store byte
        @foo(x,y,k,z); // ffi function call with pointer args
        x = x + 1;
        y = x + 1;
      }
    }
  }’;

val treeEx4' = check_success $ parse_pancake ex4';

(** Declarations: intended semantics is the variable scope extends as
    far left as possible. *)

val ex5 = ‘
  fun foo () {
    var b = 5;
    b = b + 1;
    if b >= 5 {
      raise Err 5;
    }
  }’;

val treeEx5 = check_success $ parse_pancake ex5;

(** Scope can be indicated with curly brackets *)

val ex6 = ‘
  fun foo () {
    {var b = 5;
     b = b + 1;};
     if b >= 5 {
       raise Err 5;
     }
  }’;

val treeEx6 = check_success $ parse_pancake ex6;

(* Load data of a fixed shape. The below example loads a triple where
   the first two components are single words, and the third is a tuple
   of words.
 *)
val ex7 = ‘
  fun loader() {
    x = lds {1,1,2} y;
  }’;

val treeEx7 = check_success $ parse_pancake ex7;

(* These can be nested arbitrarily deep *)
val ex7_and_a_half = ‘
  fun loader() {
    x = lds {3,1,{1,{2,1}}} y;
  }’;

val treeEx7_and_a_half = check_success $ parse_pancake ex7_and_a_half;

(* Note that {1} and 1 are distinct shapes *)
val ex7_and_three_quarters = ‘
  fun loader() {
    x = lds {1,{1}} y;
  }’;

val treeEx7_and_three_quarters = check_success $ parse_pancake ex7_and_three_quarters;

(* Comparison operators. Only two of these exist in the concrete syntax,
   so the parser may rotate them. This shouldn't matter since expressions
   are pure.
 *)
val ex8 = ‘
  fun cmps () {
    x = a < b;
    x = b > a;
    x = b >= a;
    x = a <= b;
    x = a != b;
    x = a <+ b;
    x = b >+ a;
    x = b >=+ a;
    x = a <=+ b;
  }’;

val treeEx8 = check_success $ parse_tree_pancake ex8;

val treeEx8 = check_success $ parse_pancake ex8;

(* Multiplication *)

val ex8_and_a_half = ‘
  fun mul() {
    x = a * b;
    x = a * b * c;
    x =  (a + b) * c;
    x = a + b * c;
    x = a * b + c;
   }’;

val treeEx8_and_a_half = check_success $ parse_pancake ex8_and_a_half;

(** Small test modelled after the minimal working example. *)
val ex9 = ‘
 fun testfun() {
   var a = @base;
   var b = 8;
   var c = @base + 16;
   var d = 1;
   @out_morefun(a,b,c,d);
   st @base, ic;
   return 0;
 }’;

val treeEx10 = check_success $ parse_pancake ex9;

(** Function call syntax. *)

(** Function call with arguments. *)

val argument_call = ‘
  fun main() {
    var x = 0;
    var r = 0;
    r = g(x);
    return r;
  }

  fun g(1 v, 1 u) {
    return v + u + 1;
  }’;

val arg_call_tree = check_success $ parse_tree_pancake argument_call;

val arg_call_parse = check_success $ parse_pancake argument_call;

(** Various kinds of function calls.

    A function call immediately underneath a return is parsed as a tail call.
    Tail calls overwrite the caller's stack frame with the callee's and
    thereby prevent stack explosions.
 **)
val ret_call = ‘
  fun main() {
    var r = 0;
    r = g(); // This is an assigning call (but could be optimised to a tail call)
    return r;
  }

  fun f() {
    var 1 r = g(); // Function calls can be used to initialise variables,
                   // but the expected shape of the return value must be declared
    return r;
  }

  fun g() {
    g(); // This is a stand-alone call
    return g(); // This is a tail call
  }’;

val ret_call_parse_tree = check_success $ parse_tree_pancake ret_call;

val ret_call_parse = check_success $ parse_pancake ret_call;

(** Shapes and Structs. *)
val struct_access = ‘
  fun g() {
    var v = < 0, 1, 2 >;
    var w = < 9, 9 >.2;

    return v.1;
  }’;

val struct_access_parse_tree = check_success $ parse_tree_pancake struct_access;

val struct_access_parse = check_success $ parse_pancake struct_access;


(* Writing ‘n’ for a shape is convenient syntax which is equivalent to ‘{1,1,...,1}’
   where ‘1’ occurs ‘n’ times. In abstract syntax: ‘Cons [One; One; ... ; One]’ *)
val struct_arguments = ‘
  fun g() {
    var v = < 0, 1, < 2, 3, 4 > >;
    var r = 0;
    r = f(v);
    r = l(v);

    var w = < 9, 9 >;
    r = h(w);

    var u = < < 1, 2>,
              1,
              < < 3, 4 > >
            >;
    r = k(u);


    return 0;
  }

  fun f({1,1,3} x) {
    return x.2.1;
  }

  fun l({1,1,{1,1,1}} x) {
    return x.2.1;
  }

  fun k({2,1,{2}} x) {
    return x.2.0.0;
  }

  fun h(2 x) {
    return x.0;
  }’;

val struct_argument_parse_tree =  parse_tree_pancake $ struct_arguments;

val struct_argument_parse =  parse_pancake $ struct_arguments;

val locmem_ex = ‘
  fun test_locmem() {
    var v = 12;
    st 1000, 1 + 1; // store 1 + 1 (ie 2) at local memory address 1000
    st8 1000 + 4, v; // store byte from variable v (12) to local memory address 1004
    st32 1000 + 4, v; // store word32 from variable v (12) to local memory address 1004
    v = lds 1 1000 + 8; // load word from local address 1008 and assign to variable v
    v = ld8 1000 + 4 * 3; // load byte from local address 1012 and assign to variable v
    v = ld32 1000 + 4 * 3; // load word32 from local address 1012 and assign to variable v
  }’;

val locmem_ex_parse =  check_success $ parse_pancake locmem_ex;

val shmem_ex = ‘
  fun test_shmem() {
    var v = 12;
    !st8 1000, v; // store byte from variable v (12) to shared memory address 1000
    !st32 1000, v; // store 32 bits from variable v (12) to shared memory address 1000
    !stw 1004, 1+1; // store 1+1 (aka 2) to shared memory address 1004
    !ld8 v, 1000 + 12; // load byte stored in shared memory address 1012 to v
    !ld32 v, 1000 + 12; // load 32 bits from shared memory address 1012 to v
    !ldw v, 1000 + 12 * 2; // load word stored in shared memory address 1024 to v
  }’;

val shmem_ex_parse =  check_success $ parse_pancake shmem_ex;

val comment_ex =
 ‘/* this /* non-recursive block comment
   */
  // and these single-line comments
  fun main() { //should not interfer with parsing
    return /* nor shoud this */ 1;
  }
 ’

val comment_ex_parse = check_success $ parse_pancake comment_ex

val error_line_ex1 =
 ‘/* this
  nasty /* non recursive /*
  block comment
  */
  // and these
  // single-line comments
  fun fun main() { //should not interfer with error line reporting
    return /* nor should this */ 1;
  }
 ’

val error_line_ex1_parse = check_failure $ parse_pancake error_line_ex1

val error_line_ex2 =
 ‘/* this
  nasty /* non recursive /*
  block comment
  */
  // and these
  // single-line comments
  fun main() { //should not interfer with error line reporting
    return val /* nor should this */ 1;
  }
 ’

val error_line_ex2_parse = check_failure $ parse_pancake error_line_ex2

(* Exporting a function, that is, making a function callable for external entry into Pancake,
   uses the `export` keyword. Functions without this keyword are not callable in this way *)
val entry_fun =
 ‘
  export fun f() {
    // this function can be called externally
    return 1;
  }

  fun g() {
    // this function cannot
    return 2;
  }
 ’

val entry_fun_parse =  check_success $ parse_pancake entry_fun;

(* Empty function body *)
val empty_body =
 ‘
  fun f() {}

  fun g(1 x) {}
  ’

val empty_body_parse = check_success $ parse_pancake empty_body;

(* Various kinds of empty blocks *)
val empty_blocks =
 ‘
  fun f() { while(1) {} }

  fun g() { if(1) {} else {} }

  fun h() { if(1) {} else { x = 5; } }

  fun i() { if(1) {} }

  fun j() { if(1) { x = 5; } else { } }
  ’

val empty_blocks_parse = check_success $ parse_pancake empty_blocks;

(* Various kinds of global variables *)
val globals1 =
 ‘
  var 1 x = 1+1;
  ’

val globals1_parse = check_success $ parse_pancake globals1;

val globals2 =
 ‘
  var 1 x = 1+1;

  fun f() { x = x + 1; return x; }

  var 1 y = x+1;
  ’

val globals2_parse = check_success $ parse_pancake globals2;

val globals3 =
 ‘
  var 1 x = 0;

  fun f(1 y) { x = y + 1; var x = 5; return x; }
  ’

val globals3_parse = check_success $ parse_pancake globals3;

(* Using the annotation comment syntax. *)
val annot_fun =
  `
  /* this is a function with an annot-comment in it */
  /@ and also an annot-comment before it @/
  fun f () {
    var x = 1;
    var y = 2;
    /@ good place to check y - x == 1 @/
    var z = x + y;
    return z;
  }
  `

val annot_fun_parse = check_success $ parse_pancake annot_fun;
val annot_fun_tree = check_success $ parse_tree_pancake annot_fun;
val annot_fun_lex = lex_pancake annot_fun;
val annots = annot_fun_lex |> concl |> rhs |> listSyntax.dest_list |> fst
  |> filter (can (find_term (can (match_term ``AnnotCommentT``))))
val has_annot = assert (not o null) annots;

val _ = export_theory();
