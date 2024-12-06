(**
 * Pancake static checking examples/unit tests
 *)
open HolKernel Parse boolLib bossLib stringLib numLib intLib
open errorLogMonadTheory;
open preamble panPtreeConversionTheory panStaticTheory;
open helperLib;

val _ = new_theory "panStaticExamples";


(* Following copied from panConcreteExamples*)

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
end

(** Copied from panPtreeConversion *)
fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_funs_to_ast ^code”
  end

(* All examples should parse *)
val check_parse_success = assert $ sumSyntax.is_inl o rhs o concl


(*
  Static checker output takes the form:
  (unit + staterr) # (staterr list)
  via the errorLog monad
*)

fun static_check_pancake parsed =
  let
    val ast = parsed |> concl |> rhs |> rand
  in
    EVAL “static_check ^ast”
  end

fun is_static_success tm =
  let
    val (res,_) = pairSyntax.dest_pair tm
    val {Name = name, Thy = thy, ...} = rator res |> dest_thy_const
    val {Name = name', Thy = thy', ...} = dest_thy_const “emret”
  in
    name = name' andalso thy = thy'
  end

val check_static_success = assert $ is_static_success o rhs o concl

fun is_static_failure tm =
  let
    val (res,_) = pairSyntax.dest_pair tm
    val {Name = name, Thy = thy, ...} = rator res |> dest_thy_const
    val {Name = name', Thy = thy', ...} = dest_thy_const “errorMonad$error”
  in
    name = name' andalso thy = thy'
  end

val check_static_failure = assert $ is_static_failure o rhs o concl

fun is_static_has_warnings tm =
  let
    val (_,warns) = pairSyntax.dest_pair tm
  in
    listSyntax.is_cons warns
  end

val check_static_has_warnings = assert $ is_static_has_warnings o rhs o concl

fun is_static_no_warnings tm =
  let
    val (_,warns) = pairSyntax.dest_pair tm
  in
    listSyntax.is_nil warns
  end

val check_static_no_warnings = assert $ is_static_no_warnings o rhs o concl


(* General checks
  - Errors:
    - Exported main function
    - Exported function with >4 arguments
    - Missing function exit (return, tail call, etc)
    - Loop exit outside loop (break, continue)
    - Function parameter names not distinct
    - Incorrect number of Op arguments (impossible from parser)
  - Warnings:
    - Unreachable statements (after function exit, after loop exit)
    - Base-calculated address in shared memory operation
    - Non-base -calculated address in local memory operation
*)


(*
  Scope checks
  - Errors:
    - Undefined/out-of-scope functions
    - Undefined/out-of-scope variables
    - Redefined functions
  - Warnings:
    - Redefined variables
*)


(* Shape checks - TODO*)

val ex8 = ‘
  fun a () {
    var x = 0;
    return 1;
    skip;
  }
  ’;

val treeEx8 = check_parse_success $ parse_pancake ex8;
val staticEx8 = check_static_success $ static_check_pancake treeEx8;
(* val staticEx8 = check_static_failure $ static_check_pancake treeEx8; *)
(* val warnsEx8 = check_static_no_warnings $ static_check_pancake treeEx8; *)
val warnsEx8 = check_static_has_warnings $ static_check_pancake treeEx8;


val _ = export_theory();
