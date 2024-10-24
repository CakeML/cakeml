(*
  Random crap.
*)

open preamble panPtreeConversionTheory panScopeTheory boolLib bossLib stringLib numLib intLib (*compilerTheory*);
open helperLib Parse;
val _ = new_theory "playground";

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
    EVAL “parse_funs_to_ast ^code”
  end

fun lex_pancake_from_file path =
  let
    val is = TextIO.openIn path;
    val contents = TextIO.inputAll is;
    val _ = TextIO.closeIn is;
  in
    EVAL “pancake_lex ^(fromMLstring contents)”
  end

fun parse_tree_pancake_from_file path =
  let
    val is = TextIO.openIn path;
    val contents = TextIO.inputAll is;
    val _ = TextIO.closeIn is;
  in
    EVAL “parse (pancake_lex ^(fromMLstring contents))”
  end

fun parse_pancake_from_file path =
  let
    val is = TextIO.openIn path;
    val contents = TextIO.inputAll is;
    val _ = TextIO.closeIn is;
  in
    EVAL “parse_funs_to_ast ^(fromMLstring contents)”
  end

(* fun compile_pancake_from_file path =
  let
    val is = TextIO.openIn path;
    val contents = TextIO.inputAll is;
    val _ = TextIO.closeIn is;
  in
    EVAL “compile_pancake x64_backend_config ^(fromMLstring contents)”
end *)

val check_success = assert $ sumSyntax.is_inl o rhs o concl
val check_failure = assert $ sumSyntax.is_inr o rhs o concl

val my_program = parse_pancake ‘fun main() { return 1 + 1; }’ |> concl |> rhs |> rand

val my_check = EVAL “scope_check ^my_program” |> concl |> rhs

val my_program2 = parse_pancake ‘fun main() {return y; }’ |> concl |> rhs |> rand

val my_check2 = EVAL “scope_check ^my_program2” |> concl |> rhs

val my_program3 = parse_pancake_from_file "test.🥞" |> concl |> rhs |> rand

val my_check3 = EVAL “scope_check ^my_program3” |> concl |> rhs

val bad_program =
  “[(«f»,F,[],
      Seq (Annot «location» «(568:11 568:18)»)
        (Return (Op Xor [Const 1w])));
     («g»,F,[],
      Seq (Annot «location» «(571:11 571:18)»)
        (Return (Panop Mul [Const 1w])));
     («h»,F,[],
      Seq (Annot «location» «(574:11 574:18)»)
        (Return (Op Sub [Const 1w])));
     («i»,F,[],
      Seq (Annot «location» «(571:11 571:18)»)
        (Return (Panop Mul [Const 1w; Const 1w; Const 1w])));
     («j»,F,([]:(mlstring # shape) list),
      Seq (Annot «location» «(574:11 574:18)»)
        (Return (Op Sub [Const 1w; Const 1w; Const 1w])))]”

val bad_check = EVAL “scope_check ^bad_program” |> concl |> rhs

val _ = export_theory();
