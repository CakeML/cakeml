(**
 * Pancake static checking examples/unit tests/sanity checks
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


(* #!TEMP *)
(* val ex_ = ;

val parse_ =
  check_parse_success $ parse_pancake ex_;

val static_ =
  check_static_success $ static_check_pancake parse_;
  (* check_static_failure $ static_check_pancake parse_; *)

val warns_ =
  (* check_static_no_warnings $ static_check_pancake parse_; *)
  check_static_has_warnings $ static_check_pancake parse_; *)



(* General checks *)

(* Error: Main function parameters *)

val ex_arg_main = `
  fun main (1 a) {
    return 1;
  }
`;

val parse_arg_main =
  check_parse_success $ parse_pancake ex_arg_main;

val static_arg_main =
  check_static_failure $ static_check_pancake parse_arg_main;

val warns_arg_main =
  check_static_no_warnings $ static_check_pancake parse_arg_main;


(* Error: Exported main function *)

val ex_export_main = `
  export fun main () {
    return 1;
  }
`;

val parse_export_main =
  check_parse_success $ parse_pancake ex_export_main;

val static_export_main =
  check_static_failure $ static_check_pancake parse_export_main;

val warns_export_main =
  check_static_no_warnings $ static_check_pancake parse_export_main;


(* Error: Exported function with >4 arguments *)

val ex_export_4_arg = `
  export fun f (1 a, 1 b, 1 c, 1 d, 1 e) {
    return 1;
  }
`;

val parse_export_4_arg =
  check_parse_success $ parse_pancake ex_export_4_arg;

val static_export_4_arg =
  check_static_failure $ static_check_pancake parse_export_4_arg;

val warns_ =
  check_static_no_warnings $ static_check_pancake parse_export_4_arg;


(* Error: Missing function exit (return, tail call, etc) *)

val ex_empty_fun = `
  fun f () {}
`;

val parse_empty_fun =
  check_parse_success $ parse_pancake ex_empty_fun;

val static_empty_fun =
  check_static_failure $ static_check_pancake parse_empty_fun;

val warns_empty_fun =
  check_static_no_warnings $ static_check_pancake parse_empty_fun;


val ex_no_ret_fun = `
  fun f () {
    var x = 0;
    x = 1;
  }
`;

val parse_no_ret_fun =
  check_parse_success $ parse_pancake ex_no_ret_fun;

val static_no_ret_fun =
  check_static_failure $ static_check_pancake parse_no_ret_fun;

val warns_no_ret_fun =
  check_static_no_warnings $ static_check_pancake parse_no_ret_fun;


val ex_while_ret_fun = `
  fun f () {
    while (1) {
      return 1;
    }
  }
`;

val parse_while_ret_fun =
  check_parse_success $ parse_pancake ex_while_ret_fun;

val static_while_ret_fun =
  check_static_failure $ static_check_pancake parse_while_ret_fun;

val warns_while_ret_fun =
  check_static_no_warnings $ static_check_pancake parse_while_ret_fun;


val ex_half_if_ret_fun = `
  fun f () {
    var x = 0;
    if true {
      return 1;
    } else {
      x = 1;
    }
  }
`;

val parse_half_if_ret_fun =
  check_parse_success $ parse_pancake ex_half_if_ret_fun;

val static_half_if_ret_fun =
  check_static_failure $ static_check_pancake parse_half_if_ret_fun;

val warns_half_if_ret_fun =
  check_static_no_warnings $ static_check_pancake parse_half_if_ret_fun;


val ex_full_if_ret_fun = `
  fun g () {
    if true {
      return 1;
    } else {
      return 1;
    }
  }
`;

val parse_full_if_ret_fun =
  check_parse_success $ parse_pancake ex_full_if_ret_fun;

val static_full_if_ret_fun =
  check_static_success $ static_check_pancake parse_full_if_ret_fun;

val warns_full_if_ret_fun =
  check_static_no_warnings $ static_check_pancake parse_full_if_ret_fun;


(* Error: Loop exit outside loop (break, continue) *)

val ex_rogue_break = `
  fun f () {
    break;
    return 1;
  }
`;

val parse_rogue_break =
  check_parse_success $ parse_pancake ex_rogue_break;

val static_rogue_break =
  check_static_failure $ static_check_pancake parse_rogue_break;

val warns_rogue_break =
  check_static_no_warnings $ static_check_pancake parse_rogue_break;


val ex_rogue_continue = `
  fun f () {
    continue;
    return 1;
  }
`;

val parse_rogue_continue =
  check_parse_success $ parse_pancake ex_rogue_continue;

val static_rogue_continue =
  check_static_failure $ static_check_pancake parse_rogue_continue;

val warns_rogue_continue =
  check_static_no_warnings $ static_check_pancake parse_rogue_continue;


(* Error: Function parameter names not distinct *)

val ex_repeat_params = `
  fun f (1 a, 1 b, 1 c, 1 a) {
    return 1;
  }
`;

val parse_repeat_params =
  check_parse_success $ parse_pancake ex_repeat_params;

val static_repeat_params =
  check_static_failure $ static_check_pancake parse_repeat_params;

val warns_repeat_params =
  check_static_no_warnings $ static_check_pancake parse_repeat_params;


(* Error: Incorrect number of Op arguments (impossible from parser) *)

val parse_missing_arg_binop = ``
  [(«f»,F,([]:(mlstring # shape) list),
    Seq (Annot «location» «(0:0 0:0)»)
    (Return (Op Xor [Const 1w])))]
``;

val static_missing_arg_binop =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_binop”;

val warns_missing_arg_binop =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_binop”;


val parse_missing_arg_panop = ``
  [(«f»,F,([]:(mlstring # shape) list),
    Seq (Annot «location» «(0:0 0:0)»)
    (Return (Panop Mul [Const 1w])))]
``;

val static_missing_arg_panop =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_panop”;

val warns_missing_arg_panop =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_panop”;


val parse_missing_arg_sub = ``
  [(«f»,F,([]:(mlstring # shape) list),
    Seq (Annot «location» «(0:0 0:0)»)
    (Return (Op Sub [Const 1w])))]
``;

val static_missing_arg_sub =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_sub”;

val warns_missing_arg_sub =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_sub”;


val parse_extra_arg_panop = ``
  [(«f»,F,([]:(mlstring # shape) list),
    Seq (Annot «location» «(0:0 0:0)»)
    (Return (Panop Mul [Const 1w; Const 1w; Const 1w])))]
``;

val static_extra_arg_panop =
  check_static_failure $ EVAL “static_check ^parse_extra_arg_panop”;

val warns_extra_arg_panop =
  check_static_no_warnings $ EVAL “static_check ^parse_extra_arg_panop”;


val parse_extra_arg_sub = ``
  [(«f»,F,([]:(mlstring # shape) list),
    Seq (Annot «location» «(0:0 0:0)»)
    (Return (Op Sub [Const 1w; Const 1w; Const 1w])))]
``;

val static_extra_arg_sub =
  check_static_failure $ EVAL “static_check ^parse_extra_arg_sub”;

val warns_extra_arg_sub =
  check_static_no_warnings $ EVAL “static_check ^parse_extra_arg_sub”;


(* Warning: Unreachable statements (after function exit, after loop exit) *)

val ex_stmt_after_ret = `
  fun f () {
    return 1;
    skip;
  }
`;

val parse_stmt_after_ret =
  check_parse_success $ parse_pancake ex_stmt_after_ret;

val static_stmt_after_ret =
  check_static_success $ static_check_pancake parse_stmt_after_ret;

val warns_stmt_after_ret =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_ret;


val ex_stmt_after_retcall = `
  fun f () {
    return f();
    skip;
  }
`;

val parse_stmt_after_retcall =
  check_parse_success $ parse_pancake ex_stmt_after_retcall;

val static_stmt_after_retcall =
  check_static_success $ static_check_pancake parse_stmt_after_retcall;

val warns_stmt_after_retcall =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_retcall;


val ex_stmt_after_raise = `
  fun f () {
    raise Err 1;
    skip;
  }
`;

val parse_stmt_after_raise =
  check_parse_success $ parse_pancake ex_stmt_after_raise;

val static_stmt_after_raise =
  check_static_success $ static_check_pancake parse_stmt_after_raise;

val warns_stmt_after_raise =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_raise;


val ex_annot_after_ret = `
  fun j () {
    return 1;
    /*@ annot @*/
  }
`;

val parse_annot_after_ret =
  check_parse_success $ parse_pancake ex_annot_after_ret;

val static_annot_after_ret =
  check_static_success $ static_check_pancake parse_annot_after_ret;

val warns_annot_after_ret =
  check_static_no_warnings $ static_check_pancake parse_annot_after_ret;


val ex_stmt_after_annot_after_ret = `
  fun k () {
    return 1;
    /*@ annot @*/
    skip;
  }
`;

val parse_stmt_after_annot_after_ret =
  check_parse_success $ parse_pancake ex_stmt_after_annot_after_ret;

val static_stmt_after_annot_after_ret =
  check_static_success $ static_check_pancake parse_stmt_after_annot_after_ret;

val warns_stmt_after_annot_after_ret =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_annot_after_ret;


val ex_stmt_after_inner_ret = `
  fun f () {
    {
      var x = 12;
      return x;
    };
    skip;
  }
`;

val parse_stmt_after_inner_ret =
  check_parse_success $ parse_pancake ex_stmt_after_inner_ret;

val static_stmt_after_inner_ret =
  check_static_success $ static_check_pancake parse_stmt_after_inner_ret;

val warns_stmt_after_inner_ret =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_inner_ret;


val ex_stmt_after_always_ret = `
  fun f () {
    if true {
      return 1;
    } else {
      return 1;
    }
    skip;
  }
`;

val parse_stmt_after_always_ret =
  check_parse_success $ parse_pancake ex_stmt_after_always_ret;

val static_stmt_after_always_ret =
  check_static_success $ static_check_pancake parse_stmt_after_always_ret;

val warns_stmt_after_always_ret =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_always_ret;


val ex_stmt_after_maybe_ret = `
  fun f () {
    if true {
      return 1;
    } else {
      skip;
    }
    return 1;
  }
`;

val parse_stmt_after_maybe_ret =
  check_parse_success $ parse_pancake ex_stmt_after_maybe_ret;

val static_stmt_after_maybe_ret =
  check_static_success $ static_check_pancake parse_stmt_after_maybe_ret;

val warns_stmt_after_maybe_ret =
  check_static_no_warnings $ static_check_pancake parse_stmt_after_maybe_ret;


val ex_maybe_stmt_after_always_ret = `
  fun f () {
    if true {
      return 1;
      skip;
    } else {
      return 1;
    }
  }
`;

val parse_stmt_after_inner_ret =
  check_parse_success $ parse_pancake ex_stmt_after_inner_ret;

val static_stmt_after_inner_ret =
  check_static_success $ static_check_pancake parse_stmt_after_inner_ret;

val warns_stmt_after_inner_ret =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_inner_ret;


val ex_stmt_after_loop_ret = `
  fun f () {
    while (1) {
      return 1;
    }
    return 1;
  }
`;

val parse_stmt_after_loop_ret =
  check_parse_success $ parse_pancake ex_stmt_after_loop_ret;

val static_stmt_after_loop_ret =
  check_static_success $ static_check_pancake parse_stmt_after_loop_ret;

val warns_stmt_after_loop_ret =
  check_static_no_warnings $ static_check_pancake parse_stmt_after_loop_ret;


val ex_stmt_after_brk = `
  fun f () {
    while (1) {
      break;
      skip;
    }
    return 1;
  }
`;

val parse_stmt_after_brk =
  check_parse_success $ parse_pancake ex_stmt_after_brk;

val static_stmt_after_brk =
  check_static_success $ static_check_pancake parse_stmt_after_brk;

val warns_stmt_after_brk =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_brk;


val ex_stmt_after_cont = `
  fun f () {
    while (1) {
      continue;
      skip;
    }
    return 1;
  }
`;

val parse_stmt_after_cont =
  check_parse_success $ parse_pancake ex_stmt_after_cont;

val static_stmt_after_cont =
  check_static_success $ static_check_pancake parse_stmt_after_cont;

val warns_stmt_after_cont =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_cont;


val ex_stmt_after_inner_brk = `
  fun f () {
    while (1) {
      {
        var x = 0;
        break;
      };
      skip;
    }
    return 1;
  }
`;

val parse_stmt_after_inner_brk =
  check_parse_success $ parse_pancake ex_stmt_after_inner_brk;

val static_stmt_after_inner_brk =
  check_static_success $ static_check_pancake parse_stmt_after_inner_brk;

val warns_stmt_after_inner_brk =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_inner_brk;


val ex_stmt_after_always_brk = `
  fun f () {
    while (1) {
      if true {
        break;
      } else {
        break;
      }
      skip;
    }
    return 1;
  }
`;

val parse_stmt_after_always_brk =
  check_parse_success $ parse_pancake ex_stmt_after_always_brk;

val static_stmt_after_always_brk =
  check_static_success $ static_check_pancake parse_stmt_after_always_brk;

val warns_stmt_after_always_brk =
  check_static_has_warnings $ static_check_pancake parse_stmt_after_always_brk;


val ex_stmt_after_maybe_brk = `
  fun f () {
    while (1) {
      if true {
        break;
      } else {
        skip;
      }
      break;
    }
    return 1;
  }
`;

val parse_stmt_after_maybe_brk =
  check_parse_success $ parse_pancake ex_stmt_after_maybe_brk;

val static_stmt_after_maybe_brk =
  check_static_success $ static_check_pancake parse_stmt_after_maybe_brk;

val warns_stmt_after_maybe_brk =
  check_static_no_warnings $ static_check_pancake parse_stmt_after_maybe_brk;


val ex_maybe_stmt_after_always_brk = `
  fun f () {
    while (1) {
      if true {
        break;
        skip;
      } else {
        break;
      }
    }
    return 1;
  }
`;

val parse_maybe_stmt_after_always_brk =
  check_parse_success $ parse_pancake ex_maybe_stmt_after_always_brk;

val static_maybe_stmt_after_always_brk =
  check_static_success $ static_check_pancake parse_maybe_stmt_after_always_brk;

val warns_maybe_stmt_after_always_brk =
  check_static_has_warnings $ static_check_pancake parse_maybe_stmt_after_always_brk;


(* Warning: Base-calculated address in shared memory operation #!TODO *)
`
  fun a () {
    var y = lds 1 0;
    y = ld8 0;
    st 0, y;
    st8 0, y;

    return 1;
  }
`
`
  fun b () {
    var y = lds 1 @base;
    y = ld8 @base;
    st @base, y;
    st8 @base, y;

    return 1;
  }
`


(* Warning: Non-base -calculated address in local memory operation #!TODO *)
`
  fun a () {
    var y = 0;
    !ldw y, 0;
    !stw 0, y;

    return 1;
  }
`
`
  fun b () {
    var y = 0;
    !ldw y, @base;
    !stw @base, y;

    return 1;
  }
`

`
  fun c () {
    var x = 0 + 1;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = @base + 1;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = @base + @base;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun d () {
    var 1 x = foo();

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = foo();

    y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun e (1 a) {

    var y = lds 1 a;
    y = ld8 a;
    st a, y;
    st8 a, y;

    y = lds 1 y;
    y = ld8 y;
    st y, y;
    st8 y, y;
    !ldw y, y;
    !stw y, y;

    !ldw y, a;
    !stw a, y;

    y = ld8 y;
    st y, y;
    st8 y, y;
    !ldw y, y;
    !stw y, y;

    return 1;
  }
`
`
  fun f () {
    var x = 0;
    if (1) {
      x = x + 1;
    } else {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun g () {
    var x = 0;
    if (1) {
      x = x + @base;
    } else {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun h () {
    var x = 0;
    if (1) {
      x = x + @base;
    } else {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = x + 1;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = x + @base;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    x = x + 1;

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun i () {
    var x = 0;
    if (1) {
      x = 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun j () {
    var x = 0;
    if (1) {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun k () {
    var x = @base;
    if (1) {
      x = x + 1;
    } else {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun l () {
    var x = @base;
    if (1) {
      x = x + @base;
    } else {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun m () {
    var x = @base;
    if (1) {
      x = x + @base;
    } else {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun n () {
    var x = @base;
    if (1) {
      x = 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun o () {
    var x = @base;
    if (1) {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun p () {
    var x = 0;
    while (1) {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun q () {
    var x = 0;
    while (1) {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun r () {
    var x = @base;
    while (1) {
      x = x + 1;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun s () {
    var x = @base;
    while (1) {
      x = x + @base;
    }

    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun t () {
    var x = @base;
    
    {
      var x = 1;
      
      var y = lds 1 x;
      y = ld8 x;
      st x, y;
      st8 x, y;
      !ldw y, x;
      !stw x, y;
    };
    
    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun u () {
    var x = @base;
    
    while (1) {
      var x = 1;
      
      var y = lds 1 x;
      y = ld8 x;
      st x, y;
      st8 x, y;
      !ldw y, x;
      !stw x, y;
    }
    
    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun v (1 a) {
    var x = @base;
    
    if (1) {
      var x = 1;
      
      var y = lds 1 x;
      y = ld8 x;
      st x, y;
      st8 x, y;
      !ldw y, x;
      !stw x, y;
    } else {
      var x = a;
      
      var y = lds 1 x;
      y = ld8 x;
      st x, y;
      st8 x, y;
      !ldw y, x;
      !stw x, y;
    }
    
    var y = lds 1 x;
    y = ld8 x;
    st x, y;
    st8 x, y;
    !ldw y, x;
    !stw x, y;

    return 1;
  }
`
`
  fun foo () {
    return 1;
  }
`

(* #!REF *)

(* Scope checks *)


(* Error: Undefined/out-of-scope functions *)

val ex_undefined_fun = `
  fun f () {
    foo();
    return 1;
  }
`;

val parse_undefined_fun =
  check_parse_success $ parse_pancake ex_undefined_fun;

val static_undefined_fun =
  check_static_failure $ static_check_pancake parse_undefined_fun;

val warns_undefined_fun =
  check_static_no_warnings $ static_check_pancake parse_undefined_fun;


(* Error: Undefined/out-of-scope variables *)

val ex_undefined_var = `
  fun f () {
    return x;
  }
`;

val parse_undefined_var =
  check_parse_success $ parse_pancake ex_undefined_var;

val static_undefined_var =
  check_static_failure $ static_check_pancake parse_undefined_var;

val warns_undefined_var =
  check_static_no_warnings $ static_check_pancake parse_undefined_var;


(* Error: Redefined functions *)

val ex_redefined_fun = `
  fun f () {
    return 1;
  }
  fun f () {
    return 1;
  }
`;

val parse_redefined_fun =
  check_parse_success $ parse_pancake ex_redefined_fun;

val static_redefined_fun =
  check_static_failure $ static_check_pancake parse_redefined_fun;

val warns_redefined_fun =
  check_static_no_warnings $ static_check_pancake parse_redefined_fun;


(* Warning: Redefined variables *)

val ex_redefined_var_dec_dec = `
  fun f () {
    var x = 0;
    var x = 0;
    return 1;
  }
`;

val parse_redefined_var =
  check_parse_success $ parse_pancake ex_redefined_var;

val static_redefined_var =
  check_static_success $ static_check_pancake parse_redefined_var;

val warns_redefined_var =
  check_static_has_warnings $ static_check_pancake parse_redefined_var;


val ex_redefined_var_dec_deccall = `
  fun f () {
    var x = 0;
    var 1 x = f();
    return 1;
  }
`;

val parse_redefined_var_dec_deccall =
  check_parse_success $ parse_pancake ex_redefined_var_dec_deccall;

val static_redefined_var_dec_deccall =
  check_static_success $ static_check_pancake parse_redefined_var_dec_deccall;

val warns_redefined_var_dec_deccall =
  check_static_has_warnings $ static_check_pancake parse_redefined_var_dec_deccall;


val ex_redefined_var_deccall_dec = `
  fun f () {
    var 1 x = f();
    var x = 0;
    return 1;
  }
`;

val parse_redefined_var_deccall_dec =
  check_parse_success $ parse_pancake ex_redefined_var_deccall_dec;

val static_redefined_var_deccall_dec =
  check_static_success $ static_check_pancake parse_redefined_var_deccall_dec;

val warns_redefined_var_deccall_dec =
  check_static_has_warnings $ static_check_pancake parse_redefined_var_deccall_dec;


val ex_redefined_var_deccall_deccall = `
  fun f () {
    var 1 x = f();
    var 1 x = f();
    return 1;
  }
`;

val parse_redefined_var_deccall_deccall =
  check_parse_success $ parse_pancake ex_redefined_var_deccall_deccall;

val static_redefined_var_deccall_deccall =
  check_static_success $ static_check_pancake parse_redefined_var_deccall_deccall;

val warns_redefined_var_deccall_deccall =
  check_static_has_warnings $ static_check_pancake parse_redefined_var_deccall_deccall;



(* Shape checks - TODO*)


val _ = export_theory();
