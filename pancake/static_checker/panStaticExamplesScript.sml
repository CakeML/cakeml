(**
 * Some simple static checking examples/unit tests/sanity checks for Pancake
 * Inspect interactive output manually for more detailed checking
 *)

Theory panStaticExamples
Ancestors
  errorLogMonad panPtreeConversion panStatic
Libs
(* uncomment for EVAL monitoring: *)
  stringLib numLib intLib preamble helperLib (* computeLib *)

(* uncomment for EVAL monitoring: *)
(*
val [static_check] = decls "static_check";
val [static_check_decls] = decls "static_check_decls";
val [static_check_progs] = decls "static_check_progs";
computeLib.monitoring := SOME (fn t => same_const static_check t orelse same_const static_check_decls t orelse same_const static_check_progs t);
*)


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
    EVAL “parse_topdecs_to_ast ^code”
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


(*
TEMPLATE:

val ex_ = ;

val parse_ =
  check_parse_success $ parse_pancake ex_;

val static_ =
  check_static_success $ static_check_pancake parse_;
  (* check_static_failure $ static_check_pancake parse_; *)

val warns_ =
  check_static_no_warnings $ static_check_pancake parse_;
  (* check_static_has_warnings $ static_check_pancake parse_; *)

*)


(* General checks *)

(* Error: Main function parameters *)

val ex_arg_main = `
  fun 1 main (1 a) {
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
  export fun 1 main () {
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
  export fun 1 f (1 a, 1 b, 1 c, 1 d, 1 e) {
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
  fun 1 f () {}
`;

val parse_empty_fun =
  check_parse_success $ parse_pancake ex_empty_fun;

val static_empty_fun =
  check_static_failure $ static_check_pancake parse_empty_fun;

val warns_empty_fun =
  check_static_no_warnings $ static_check_pancake parse_empty_fun;


val ex_no_ret_fun = `
  fun 1 f () {
    var 1 x = 0;
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
  fun 1 f () {
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
  fun 1 f () {
    var 1 x = 0;
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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


(* Error: Incorrect number of function arguments *)

val ex_func_correct_num_args = `
  fun 1 f () {
    g(1, 2, 3);
    return 1;
  }
  fun 1 g (1 a, 1 b, 1 c) {
    return 1;
  }
`;

val parse_func_correct_num_args =
  check_parse_success $ parse_pancake ex_func_correct_num_args;

val static_func_correct_num_args =
  check_static_success $ static_check_pancake parse_func_correct_num_args;

val warns_func_correct_num_args =
  check_static_no_warnings $ static_check_pancake parse_func_correct_num_args;


val ex_func_no_args = `
  fun 1 f () {
    g();
    return 1;
  }
  fun 1 g (1 a, 1 b, 1 c) {
    return 1;
  }
`;

val parse_func_no_args =
  check_parse_success $ parse_pancake ex_func_no_args;

val static_func_no_args =
  check_static_failure $ static_check_pancake parse_func_no_args;

val warns_func_no_args =
  check_static_no_warnings $ static_check_pancake parse_func_no_args;


val ex_func_missing_args = `
  fun 1 f () {
    g(1);
    return 1;
  }
  fun 1 g (1 a, 1 b, 1 c) {
    return 1;
  }
`;

val parse_func_missing_args =
  check_parse_success $ parse_pancake ex_func_missing_args;

val static_func_missing_args =
  check_static_failure $ static_check_pancake parse_func_missing_args;

val warns_func_missing_args =
  check_static_no_warnings $ static_check_pancake parse_func_missing_args;


val ex_func_extra_args = `
  fun 1 f () {
    g(1, 2, 3, 4);
    return 1;
  }
  fun 1 g (1 a, 1 b, 1 c) {
    return 1;
  }
`;

val parse_func_extra_args =
  check_parse_success $ parse_pancake ex_func_extra_args;

val static_func_extra_args =
  check_static_failure $ static_check_pancake parse_func_extra_args;

val warns_func_extra_args =
  check_static_no_warnings $ static_check_pancake parse_func_extra_args;


(* Error: Incorrect number of Op arguments (impossible from parser) *)

val parse_missing_arg_binop = ``
  [Function
     <| name   := «f»
      ; export := F
      ; params := []
      ; body := Seq (Annot «location» «(0:0 0:0)»)
                    (Return (Op Xor [Const 1w]))
      ; return := One
      |>
  ]
``;

val static_missing_arg_binop =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_binop”;

val warns_missing_arg_binop =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_binop”;


val parse_missing_arg_panop = ``
  [Function
     <| name   := «f»
      ; export := F
      ; params := []
      ; body := Seq (Annot «location» «(0:0 0:0)»)
                    (Return (Panop Mul [Const 1w]))
      ; return := One
      |>
  ]
``;

val static_missing_arg_panop =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_panop”;

val warns_missing_arg_panop =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_panop”;


val parse_missing_arg_sub = ``
  [Function
     <| name   := «f»
      ; export := F
      ; params := []
      ; body := Seq (Annot «location» «(0:0 0:0)»)
                    (Return (Op Sub [Const 1w]))
      ; return := One
      |>
  ]
``;

val static_missing_arg_sub =
  check_static_failure $ EVAL “static_check ^parse_missing_arg_sub”;

val warns_missing_arg_sub =
  check_static_no_warnings $ EVAL “static_check ^parse_missing_arg_sub”;


val parse_extra_arg_panop = ``
  [Function
     <| name   := «f»
      ; export := F
      ; params := []
      ; body := Seq (Annot «location» «(0:0 0:0)»)
                    (Return (Panop Mul [Const 1w; Const 1w; Const 1w]))
      ; return := One
      |>
  ]
``;

val static_extra_arg_panop =
  check_static_failure $ EVAL “static_check ^parse_extra_arg_panop”;

val warns_extra_arg_panop =
  check_static_no_warnings $ EVAL “static_check ^parse_extra_arg_panop”;


val parse_extra_arg_sub = ``
  [Function
     <| name   := «f»
      ; export := F
      ; params := []
      ; body := Seq (Annot «location» «(0:0 0:0)»)
                    (Return (Op Sub [Const 1w; Const 1w; Const 1w]))
      ; return := One
      |>
  ]
``;

val static_extra_arg_sub =
  check_static_failure $ EVAL “static_check ^parse_extra_arg_sub”;

val warns_extra_arg_sub =
  check_static_no_warnings $ EVAL “static_check ^parse_extra_arg_sub”;


(* Warning: Unreachable statements (after function exit, after loop exit) *)

val ex_stmt_after_ret = `
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
    return 1;
    /@ annot @/
  }
`;

val parse_annot_after_ret =
  check_parse_success $ parse_pancake ex_annot_after_ret;

val static_annot_after_ret =
  check_static_success $ static_check_pancake parse_annot_after_ret;

val warns_annot_after_ret =
  check_static_no_warnings $ static_check_pancake parse_annot_after_ret;


val ex_stmt_after_annot_after_ret = `
  fun 1 f () {
    return 1;
    /@ annot @/
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
  fun 1 f () {
    {
      var 1 x = 12;
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
    while (1) {
      {
        var 1 x = 0;
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
  fun 1 f () {
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
  fun 1 f () {
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
  fun 1 f () {
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


(* Warning: Non-base-calculated address in local memory operation *)

val ex_local_word_notbased = `
  fun 1 f () {
    var 1 x = lds 1 0;
    st 0, x;

    return 1;
  }
`;

val parse_local_word_notbased =
  check_parse_success $ parse_pancake ex_local_word_notbased;

val static_local_word_notbased =
  check_static_success $ static_check_pancake parse_local_word_notbased;

val warns_local_word_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_notbased;


val ex_local_byte_notbased = `
  fun 1 f () {
    var 1 x = ld8 0;
    st8 0, x;

    return 1;
  }
`;

val parse_local_byte_notbased =
  check_parse_success $ parse_pancake ex_local_byte_notbased;

val static_local_byte_notbased =
  check_static_success $ static_check_pancake parse_local_byte_notbased;

val warns_local_byte_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_byte_notbased;


val ex_local_word_based = `
  fun 1 f () {
    var 1 x = lds 1 @base;
    st @base, x;

    return 1;
  }
`;

val parse_local_word_based =
  check_parse_success $ parse_pancake ex_local_word_based;

val static_local_word_based =
  check_static_success $ static_check_pancake parse_local_word_based;

val warns_local_word_based =
  check_static_no_warnings $ static_check_pancake parse_local_word_based;


val ex_local_byte_based = `
  fun 1 f () {
    var 1 x = ld8 @base;
    st8 @base, x;

    return 1;
  }
`;

val parse_local_byte_based =
  check_parse_success $ parse_pancake ex_local_byte_based;

val static_local_byte_based =
  check_static_success $ static_check_pancake parse_local_byte_based;

val warns_local_byte_based =
  check_static_no_warnings $ static_check_pancake parse_local_byte_based;


(* notbased field *)
val ex_local_word_field_notbased = `
  fun 1 f () {
    var 2 x = <0, 0>;
    var 1 y = lds 1 x.0;
    st x.0, y;

    return 1;
  }
`;

val parse_local_word_field_notbased =
  check_parse_success $ parse_pancake ex_local_word_field_notbased;

val static_local_word_field_notbased =
  check_static_success $ static_check_pancake parse_local_word_field_notbased;

val warns_local_word_field_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_field_notbased;


(* based field *)
val ex_local_word_field_based = `
  fun 1 f () {
    var 2 x = <@base, 0>;
    var 1 y = lds 1 x.0;
    st x.0, y;

    return 1;
  }
`;

val parse_local_word_field_based =
  check_parse_success $ parse_pancake ex_local_word_field_based;

val static_local_word_field_based =
  check_static_success $ static_check_pancake parse_local_word_field_based;

val warns_local_word_field_based =
  check_static_no_warnings $ static_check_pancake parse_local_word_field_based;


val ex_local_word_arg = `
  fun 1 f (1 a) {
    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_arg =
  check_parse_success $ parse_pancake ex_local_word_arg;

val static_local_word_arg =
  check_static_success $ static_check_pancake parse_local_word_arg;

val warns_local_word_arg =
  check_static_no_warnings $ static_check_pancake parse_local_word_arg;


val ex_local_word_local = `
  fun 1 f () {
    var 1 a = (lds 1 @base);

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_local =
  check_parse_success $ parse_pancake ex_local_word_local;

val static_local_word_local =
  check_static_success $ static_check_pancake parse_local_word_local;

val warns_local_word_local =
  check_static_no_warnings $ static_check_pancake parse_local_word_local;


val ex_local_word_shared = `
  fun 1 f () {
    var 1 a = 0;
    !ldw a, 0;

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_shared =
  check_parse_success $ parse_pancake ex_local_word_shared;

val static_local_word_shared =
  check_static_success $ static_check_pancake parse_local_word_shared;

val warns_local_word_shared =
  check_static_no_warnings $ static_check_pancake parse_local_word_shared;


val ex_local_word_always_based = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = @base;
    } else {
      a = @base;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_always_based =
  check_parse_success $ parse_pancake ex_local_word_always_based;

val static_local_word_always_based =
  check_static_success $ static_check_pancake parse_local_word_always_based;

val warns_local_word_always_based =
  check_static_no_warnings $ static_check_pancake parse_local_word_always_based;


val ex_local_word_else_based = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = 0;
    } else {
      a = @base;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_else_based =
  check_parse_success $ parse_pancake ex_local_word_else_based;

val static_local_word_else_based =
  check_static_success $ static_check_pancake parse_local_word_else_based;

val warns_local_word_else_based =
  check_static_has_warnings $ static_check_pancake parse_local_word_else_based;


val ex_local_word_based_while_based = `
  fun 1 f () {
    var 1 a = @base;
    while (1) {
      a = @base;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_based_while_based =
  check_parse_success $ parse_pancake ex_local_word_based_while_based;

val static_local_word_based_while_based =
  check_static_success $ static_check_pancake parse_local_word_based_while_based;

val warns_local_word_based_while_based =
  check_static_no_warnings $ static_check_pancake parse_local_word_based_while_based;


val ex_local_word_notbased_while_based = `
  fun 1 f () {
    var 1 a = 0;
    while (1) {
      a = @base;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_notbased_while_based =
  check_parse_success $ parse_pancake ex_local_word_notbased_while_based;

val static_local_word_notbased_while_based =
  check_static_success $ static_check_pancake parse_local_word_notbased_while_based;

val warns_local_word_notbased_while_based =
  check_static_has_warnings $ static_check_pancake parse_local_word_notbased_while_based;


val ex_local_word_always_notbased = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = 0;
    } else {
      a = 0;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_always_notbased =
  check_parse_success $ parse_pancake ex_local_word_always_notbased;

val static_local_word_always_notbased =
  check_static_success $ static_check_pancake parse_local_word_always_notbased;

val warns_local_word_always_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_always_notbased;


val ex_local_word_else_notbased = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = @base;
    } else {
      a = 0;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_else_notbased =
  check_parse_success $ parse_pancake ex_local_word_else_notbased;

val static_local_word_else_notbased =
  check_static_success $ static_check_pancake parse_local_word_else_notbased;

val warns_local_word_else_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_else_notbased;


val ex_local_word_notbased_while_notbased = `
  fun 1 f () {
    var 1 a = 0;
    while (1) {
      a = 0;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_notbased_while_notbased =
  check_parse_success $ parse_pancake ex_local_word_notbased_while_notbased;

val static_local_word_notbased_while_notbased =
  check_static_success $ static_check_pancake parse_local_word_notbased_while_notbased;

val warns_local_word_notbased_while_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_notbased_while_notbased;


val ex_local_word_based_while_notbased = `
  fun 1 f () {
    var 1 a = @base;
    while (1) {
      a = 0;
    }

    var 1 x = lds 1 a;
    st a, x;

    return 1;
  }
`;

val parse_local_word_based_while_notbased =
  check_parse_success $ parse_pancake ex_local_word_based_while_notbased;

val static_local_word_based_while_notbased =
  check_static_success $ static_check_pancake parse_local_word_based_while_notbased;

val warns_local_word_based_while_notbased =
  check_static_has_warnings $ static_check_pancake parse_local_word_based_while_notbased;


(* Warning: Base-calculated address in shared memory operation *)

val ex_shared_word_notbased = `
  fun 1 f () {
    var 1 x = 0;
    !ldw x, 0;
    !stw 0, x;

    return 1;
  }
`;

val parse_shared_word_notbased =
  check_parse_success $ parse_pancake ex_shared_word_notbased;

val static_shared_word_notbased =
  check_static_success $ static_check_pancake parse_shared_word_notbased;

val warns_shared_word_notbased =
  check_static_no_warnings $ static_check_pancake parse_shared_word_notbased;



val ex_shared_word_based = `
  fun 1 f () {
    var 1 x = 0;
    !ldw x, @base;
    !stw @base, x;

    return 1;
  }
`;

val parse_shared_word_based =
  check_parse_success $ parse_pancake ex_shared_word_based;

val static_shared_word_based =
  check_static_success $ static_check_pancake parse_shared_word_based;

val warns_shared_word_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_based;


(* notbased field *)
val ex_shared_word_field_notbased = `
  fun 1 f () {
    var 2 x = <0, 0>;
    var 1 y = 0;
    !ldw y, x.0;
    !stw x.0, y;

    return 1;
  }
`;

val parse_shared_word_field_notbased =
  check_parse_success $ parse_pancake ex_shared_word_field_notbased;

val static_shared_word_field_notbased =
  check_static_success $ static_check_pancake parse_shared_word_field_notbased;

val warns_shared_word_field_notbased =
  check_static_no_warnings $ static_check_pancake parse_shared_word_field_notbased;


(* based field *)
val ex_shared_word_field_based = `
  fun 1 f () {
    var 2 x = <@base, 0>;
    var 1 y = 0;
    !ldw y, x.0;
    !stw x.0, y;

    return 1;
  }
`;

val parse_shared_word_field_based =
  check_parse_success $ parse_pancake ex_shared_word_field_based;

val static_shared_word_field_based =
  check_static_success $ static_check_pancake parse_shared_word_field_based;

val warns_local_word_field_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_field_based;


val ex_shared_word_arg = `
  fun 1 f (1 a) {
    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_arg =
  check_parse_success $ parse_pancake ex_shared_word_arg;

val static_shared_word_arg =
  check_static_success $ static_check_pancake parse_shared_word_arg;

val warns_shared_word_arg =
  check_static_no_warnings $ static_check_pancake parse_shared_word_arg;


val ex_shared_word_local = `
  fun 1 f () {
    var 1 a = (lds 1 @base);

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_local =
  check_parse_success $ parse_pancake ex_shared_word_local;

val static_shared_word_local =
  check_static_success $ static_check_pancake parse_shared_word_local;

val warns_shared_word_local =
  check_static_no_warnings $ static_check_pancake parse_shared_word_local;


val ex_shared_word_shared = `
  fun 1 f () {
    var 1 a = 0;
    !ldw a, 0;

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_shared =
  check_parse_success $ parse_pancake ex_shared_word_shared;

val static_shared_word_shared =
  check_static_success $ static_check_pancake parse_shared_word_shared;

val warns_shared_word_shared =
  check_static_no_warnings $ static_check_pancake parse_shared_word_shared;


val ex_shared_word_always_based = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = @base;
    } else {
      a = @base;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_always_based =
  check_parse_success $ parse_pancake ex_shared_word_always_based;

val static_shared_word_always_based =
  check_static_success $ static_check_pancake parse_shared_word_always_based;

val warns_shared_word_always_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_always_based;


val ex_shared_word_else_based = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = 0;
    } else {
      a = @base;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_else_based =
  check_parse_success $ parse_pancake ex_shared_word_else_based;

val static_shared_word_else_based =
  check_static_success $ static_check_pancake parse_shared_word_else_based;

val warns_shared_word_else_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_else_based;


val ex_shared_word_based_while_based = `
  fun 1 f () {
    var 1 a = @base;
    while (1) {
      a = @base;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_based_while_based =
  check_parse_success $ parse_pancake ex_shared_word_based_while_based;

val static_shared_word_based_while_based =
  check_static_success $ static_check_pancake parse_shared_word_based_while_based;

val warns_shared_word_based_while_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_based_while_based;


val ex_shared_word_notbased_while_based = `
  fun 1 f () {
    var 1 a = 0;
    while (1) {
      a = @base;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_notbased_while_based =
  check_parse_success $ parse_pancake ex_shared_word_notbased_while_based;

val static_shared_word_notbased_while_based =
  check_static_success $ static_check_pancake parse_shared_word_notbased_while_based;

val warns_shared_word_notbased_while_based =
  check_static_has_warnings $ static_check_pancake parse_shared_word_notbased_while_based;


val ex_shared_word_always_notbased = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = 0;
    } else {
      a = 0;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_always_notbased =
  check_parse_success $ parse_pancake ex_shared_word_always_notbased;

val static_shared_word_always_notbased =
  check_static_success $ static_check_pancake parse_shared_word_always_notbased;

val warns_shared_word_always_notbased =
  check_static_no_warnings $ static_check_pancake parse_shared_word_always_notbased;


val ex_shared_word_else_notbased = `
  fun 1 f () {
    var 1 a = 0;
    if (1) {
      a = @base;
    } else {
      a = 0;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_else_notbased =
  check_parse_success $ parse_pancake ex_shared_word_else_notbased;

val static_shared_word_else_notbased =
  check_static_success $ static_check_pancake parse_shared_word_else_notbased;

val warns_shared_word_else_notbased =
  check_static_has_warnings $ static_check_pancake parse_shared_word_else_notbased;


val ex_shared_word_notbased_while_notbased = `
  fun 1 f () {
    var 1 a = 0;
    while (1) {
      a = 0;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_notbased_while_notbased =
  check_parse_success $ parse_pancake ex_shared_word_notbased_while_notbased;

val static_shared_word_notbased_while_notbased =
  check_static_success $ static_check_pancake parse_shared_word_notbased_while_notbased;

val warns_shared_word_notbased_while_notbased =
  check_static_no_warnings $ static_check_pancake parse_shared_word_notbased_while_notbased;


val ex_shared_word_based_while_notbased = `
  fun 1 f () {
    var 1 a = @base;
    while (1) {
      a = 0;
    }

    var 1 x = 0;
    !ldw x, a;
    !stw a, x;

    return 1;
  }
`;

val parse_shared_word_based_while_notbased =
  check_parse_success $ parse_pancake ex_shared_word_based_while_notbased;

val static_shared_word_based_while_notbased =
  check_static_success $ static_check_pancake parse_shared_word_based_while_notbased;

val warns_shared_word_based_while_notbased =
  check_static_has_warnings $ static_check_pancake parse_shared_word_based_while_notbased


(* Scope checks *)

(* Error: Undefined/out-of-scope functions *)

val ex_undefined_fun_standalone = `
  fun 1 f () {
    foo();
    return 1;
  }
`;

val parse_undefined_fun_standalone =
  check_parse_success $ parse_pancake ex_undefined_fun_standalone;

val static_undefined_fun_standalone =
  check_static_failure $ static_check_pancake parse_undefined_fun_standalone;

val warns_undefined_fun_standalone =
  check_static_no_warnings $ static_check_pancake parse_undefined_fun_standalone;


val ex_undefined_fun_dec = `
  fun 1 f () {
    var 1 x = foo();
    return 1;
  }
`;

val parse_undefined_fun_dec =
  check_parse_success $ parse_pancake ex_undefined_fun_dec;

val static_undefined_fun_dec =
  check_static_failure $ static_check_pancake parse_undefined_fun_dec;

val warns_undefined_fun_dec =
  check_static_no_warnings $ static_check_pancake parse_undefined_fun_dec;


val ex_undefined_fun_assign = `
  fun 1 f () {
    var 1 x = 1;
    x = foo();
    return 1;
  }
`;

val parse_undefined_fun_assign =
  check_parse_success $ parse_pancake ex_undefined_fun_assign;

val static_undefined_fun_assign =
  check_static_failure $ static_check_pancake parse_undefined_fun_assign;

val warns_undefined_fun_assign =
  check_static_no_warnings $ static_check_pancake parse_undefined_fun_assign;


val ex_undefined_fun_tail = `
  fun 1 f () {
    return foo();
  }
`;

val parse_undefined_fun_tail =
  check_parse_success $ parse_pancake ex_undefined_fun_tail;

val static_undefined_fun_tail =
  check_static_failure $ static_check_pancake parse_undefined_fun_tail;

val warns_undefined_fun_tail =
  check_static_no_warnings $ static_check_pancake parse_undefined_fun_tail;


(* Error: Undefined/out-of-scope struct names *)

val ex_undefined_struct_field = `
  struct first_struct {
    second_struct s
  }

  struct second_struct {
    1 x
  }
`;

val parse_undefined_struct_field =
  check_parse_success $ parse_pancake ex_undefined_struct_field;

val static_undefined_struct_field =
  check_static_failure $ static_check_pancake parse_undefined_struct_field;

val warns_undefined_struct_field =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_field;


val ex_defined_struct_field = `
  struct first_struct {
    1 x
  }

  struct second_struct {
    first_struct s
  }
`;

val parse_defined_struct_field =
  check_parse_success $ parse_pancake ex_defined_struct_field;

val static_defined_struct_field =
  check_static_success $ static_check_pancake parse_defined_struct_field;

val warns_defined_struct_field =
  check_static_no_warnings $ static_check_pancake parse_defined_struct_field;


val ex_undefined_struct_param = `
  fun 1 f (my_struct a) {
    return 1;
  }
`;

val parse_undefined_struct_param =
  check_parse_success $ parse_pancake ex_undefined_struct_param;

val static_undefined_struct_param =
  check_static_failure $ static_check_pancake parse_undefined_struct_param;

val warns_undefined_struct_param =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_param;


val ex_undefined_struct_return = `
  fun my_struct f (1 a) {
    return 1;
  }
`;

val parse_undefined_struct_return =
  check_parse_success $ parse_pancake ex_undefined_struct_return;

val static_undefined_struct_return =
  check_static_failure $ static_check_pancake parse_undefined_struct_return;

val warns_undefined_struct_return =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_return;


val ex_undefined_struct_local = `
  fun 1 f (1 a) {
    var my_struct x = 1;
    return 1;
  }
`;

val parse_undefined_struct_local =
  check_parse_success $ parse_pancake ex_undefined_struct_local;

val static_undefined_struct_local =
  check_static_failure $ static_check_pancake parse_undefined_struct_local;

val warns_undefined_struct_local =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_local;


val ex_undefined_struct_global = `
  var my_struct x = 1;
`;

val parse_undefined_struct_global =
  check_parse_success $ parse_pancake ex_undefined_struct_global;

val static_undefined_struct_global =
  check_static_failure $ static_check_pancake parse_undefined_struct_global;

val warns_undefined_struct_global =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_global;


val ex_undefined_struct_load = `
  fun 1 f (1 a) {
    return lds my_struct @base;
  }
`;

val parse_undefined_struct_load =
  check_parse_success $ parse_pancake ex_undefined_struct_load;

val static_undefined_struct_load =
  check_static_failure $ static_check_pancake parse_undefined_struct_load;

val warns_undefined_struct_load =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_load;


val ex_undefined_struct_constant = `
  fun 1 f (1 a) {
    return my_struct <value = 1>;
  }
`;

val parse_undefined_struct_constant =
  check_parse_success $ parse_pancake ex_undefined_struct_constant;

val static_undefined_struct_constant =
  check_static_failure $ static_check_pancake parse_undefined_struct_constant;

val warns_undefined_struct_constant =
  check_static_no_warnings $ static_check_pancake parse_undefined_struct_constant;


val ex_func_global_order = `
  var my_struct x = my_struct <value = 1>;

  fun my_struct f (my_struct a) {
    var my_struct y = x;
    y = lds my_struct @base;
    return a;
  }

  struct my_struct {
    1 value
  }
`;

val parse_func_global_order =
  check_parse_success $ parse_pancake ex_func_global_order;

val static_func_global_order =
  check_static_success $ static_check_pancake parse_func_global_order;

val warns_func_global_order =
  check_static_no_warnings $ static_check_pancake parse_func_global_order;


(* Error: Undefined/out-of-scope variables *)

val ex_undefined_var = `
  fun 1 f () {
    return x;
  }
`;

val parse_undefined_var =
  check_parse_success $ parse_pancake ex_undefined_var;

val static_undefined_var =
  check_static_failure $ static_check_pancake parse_undefined_var;

val warns_undefined_var =
  check_static_no_warnings $ static_check_pancake parse_undefined_var;


val ex_self_referential_global = `
  var 1 x = x;
`;

val parse_self_referential_global =
  check_parse_success $ parse_pancake ex_self_referential_global;

val static_self_referential_global =
  check_static_failure $ static_check_pancake parse_self_referential_global;

val warns_self_referential_global =
  check_static_no_warnings $ static_check_pancake parse_self_referential_global;


val ex_well_scoped_globals = `
  var 1 x = 1;
  var 1 y = x;
  var 1 z = x + y;
`;

val parse_well_scoped_globals =
  check_parse_success $ parse_pancake ex_well_scoped_globals;

val static_well_scoped_globals =
  check_static_success $ static_check_pancake parse_well_scoped_globals;

val warns_well_scoped_globals =
  check_static_no_warnings $ static_check_pancake parse_well_scoped_globals;


val ex_global_function_order = `
  fun 1 f() { return x; }
  var 1 x = 1;
`;

val parse_global_function_order =
  check_parse_success $ parse_pancake ex_global_function_order;

val static_global_function_order =
  check_static_success $ static_check_pancake parse_global_function_order;

val warns_global_function_order =
  check_static_no_warnings $ static_check_pancake parse_global_function_order;


(* Error: Redefined functions *)

val ex_redefined_fun = `
  fun 1 f () {
    return 1;
  }
  fun 1 f () {
    return 1;
  }
`;

val parse_redefined_fun =
  check_parse_success $ parse_pancake ex_redefined_fun;

val static_redefined_fun =
  check_static_failure $ static_check_pancake parse_redefined_fun;

val warns_redefined_fun =
  check_static_no_warnings $ static_check_pancake parse_redefined_fun;


(* Error: Redefined function parameter names *)

val ex_repeat_params = `
  fun 1 f (1 a, 1 b, 1 c, 1 a) {
    return 1;
  }
`;

val parse_repeat_params =
  check_parse_success $ parse_pancake ex_repeat_params;

val static_repeat_params =
  check_static_failure $ static_check_pancake parse_repeat_params;

val warns_repeat_params =
  check_static_no_warnings $ static_check_pancake parse_repeat_params;


(* Error: Redefined struct names *)

val ex_redefined_struct = `
  struct my_struct {
    1 value
  }

  struct my_struct {
    1 other_value
  }
`;

val parse_redefined_struct =
  check_parse_success $ parse_pancake ex_redefined_struct;

val static_redefined_struct =
  check_static_failure $ static_check_pancake parse_redefined_struct;

val warns_redefined_struct =
  check_static_no_warnings $ static_check_pancake parse_redefined_struct;


(* Error: Redefined struct field names *)

val ex_repeat_field = `
  struct my_struct {
    1 value,
    1 other_value,
    1 value
  }
`;

val parse_repeat_field =
  check_parse_success $ parse_pancake ex_repeat_field;

val static_repeat_field =
  check_static_failure $ static_check_pancake parse_repeat_field;

val warns_repeat_field =
  check_static_no_warnings $ static_check_pancake parse_repeat_field;


(* Warning: Redefined variables *)

val ex_redefined_var_dec_dec = `
  fun 1 f () {
    var 1 x = 0;
    var 1 x = 0;
    return 1;
  }
`;

val parse_redefined_var_dec_dec =
  check_parse_success $ parse_pancake ex_redefined_var_dec_dec;

val static_redefined_var_dec_dec =
  check_static_success $ static_check_pancake parse_redefined_var_dec_dec;

val warns_redefined_var_dec_dec =
  check_static_has_warnings $ static_check_pancake parse_redefined_var_dec_dec;


val ex_redefined_var_dec_deccall = `
  fun 1 f () {
    var 1 x = 0;
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
  fun 1 f () {
    var 1 x = f();
    var 1 x = 0;
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
  fun 1 f () {
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


val ex_redefined_global_var = `
  var 1 x = 1;
  var 1 x = 1;
`;

val parse_redefined_global_var =
  check_parse_success $ parse_pancake ex_redefined_global_var;

val static_redefined_global_var =
  check_static_success $ static_check_pancake parse_redefined_global_var;

val warns_redefined_global_var =
  check_static_has_warnings $ static_check_pancake parse_redefined_global_var;


val ex_redefined_global_var_locally = `
  var 1 x = 1;
  fun 1 f() {
    var 1 x = 1;
    return x;
  }
`;

val parse_redefined_global_var_locally =
  check_parse_success $ parse_pancake ex_redefined_global_var_locally;

val static_redefined_global_var_locally =
  check_static_success $ static_check_pancake parse_redefined_global_var_locally;

val warns_redefined_global_var_locally =
  check_static_has_warnings $ static_check_pancake parse_redefined_global_var_locally;


val ex_redefined_global_var_deccall = `
  var 1 x = 1;
  fun 1 f() {
    var 1 x = f();
    return x;
  }
`;

val parse_redefined_global_var_deccall =
  check_parse_success $ parse_pancake ex_redefined_global_var_deccall;

val static_redefined_global_var_deccall =
  check_static_success $ static_check_pancake parse_redefined_global_var_deccall;

val warns_redefined_global_var_deccall =
  check_static_has_warnings $ static_check_pancake parse_redefined_global_var_deccall;


(* Shape checks *)


(* Error: Mismatched variable declarations *)

val ex_local_decl_word_match = `
  fun 1 f () {
    var 1 x = 1;
    return 1;
  }
`;

val parse_local_decl_word_match =
  check_parse_success $ parse_pancake ex_local_decl_word_match;

val static_local_decl_word_match =
  check_static_success $ static_check_pancake parse_local_decl_word_match;

val warns_local_decl_word_match =
  check_static_no_warnings $ static_check_pancake parse_local_decl_word_match;


val ex_local_decl_word_mismatch_1 = `
  fun 1 f () {
    var 1 x = <1>;
    return 1;
  }
`;

val parse_local_decl_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_decl_word_mismatch_1;

val static_local_decl_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_decl_word_mismatch_1;

val warns_local_decl_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_word_mismatch_1;


val ex_local_decl_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_decl_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_decl_word_mismatch_2;

val static_local_decl_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_decl_word_mismatch_2;

val warns_local_decl_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_word_mismatch_2;


val ex_local_decl_rstruct_match = `
  fun 1 f () {
    var {1} x = <1>;
    return 1;
  }
`;

val parse_local_decl_rstruct_match =
  check_parse_success $ parse_pancake ex_local_decl_rstruct_match;

val static_local_decl_rstruct_match =
  check_static_success $ static_check_pancake parse_local_decl_rstruct_match;

val warns_local_decl_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_decl_rstruct_match;


val ex_local_decl_rstruct_mismatch_1 = `
  fun 1 f () {
    var {1} x = 1;
    return 1;
  }
`;

val parse_local_decl_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_decl_rstruct_mismatch_1;

val static_local_decl_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_decl_rstruct_mismatch_1;

val warns_local_decl_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_rstruct_mismatch_1;


val ex_local_decl_rstruct_mismatch_2 = `
  fun 1 f () {
    var {1} x = <1, 1>;
    return 1;
  }
`;

val parse_local_decl_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_decl_rstruct_mismatch_2;

val static_local_decl_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_decl_rstruct_mismatch_2;

val warns_local_decl_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_rstruct_mismatch_2;


val ex_local_decl_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var {1} x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_decl_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_decl_rstruct_mismatch_3;

val static_local_decl_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_decl_rstruct_mismatch_3;

val warns_local_decl_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_rstruct_mismatch_3;


val ex_local_decl_nstruct_match = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_decl_nstruct_match =
  check_parse_success $ parse_pancake ex_local_decl_nstruct_match;

val static_local_decl_nstruct_match =
  check_static_success $ static_check_pancake parse_local_decl_nstruct_match;

val warns_local_decl_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_decl_nstruct_match;


val ex_local_decl_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = 1;
    return 1;
  }
`;

val parse_local_decl_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_decl_nstruct_mismatch_1;

val static_local_decl_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_decl_nstruct_mismatch_1;

val warns_local_decl_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_nstruct_mismatch_1;


val ex_local_decl_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = <1>;
    return 1;
  }
`;

val parse_local_decl_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_decl_nstruct_mismatch_2;

val static_local_decl_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_decl_nstruct_mismatch_2;

val warns_local_decl_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_nstruct_mismatch_2;


val ex_local_decl_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = My_Struct <value = 1>;
    return 1;
  }
`;

val parse_local_decl_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_decl_nstruct_mismatch_3;

val static_local_decl_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_decl_nstruct_mismatch_3;

val warns_local_decl_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_nstruct_mismatch_3;


val ex_global_decl_word_match = `
  var 1 x = 1;
`;

val parse_global_decl_word_match =
  check_parse_success $ parse_pancake ex_global_decl_word_match;

val static_global_decl_word_match =
  check_static_success $ static_check_pancake parse_global_decl_word_match;

val warns_global_decl_word_match =
  check_static_no_warnings $ static_check_pancake parse_global_decl_word_match;


val ex_global_decl_word_mismatch_1 = `
  var 1 x = <1>;
`;

val parse_global_decl_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_global_decl_word_mismatch_1;

val static_global_decl_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_global_decl_word_mismatch_1;

val warns_global_decl_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_word_mismatch_1;


val ex_global_decl_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  var 1 x = my_struct <value = 1>;
`;

val parse_global_decl_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_global_decl_word_mismatch_2;

val static_global_decl_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_global_decl_word_mismatch_2;

val warns_global_decl_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_word_mismatch_2;


val ex_global_decl_rstruct_match = `
  var {1} x = <1>;
`;

val parse_global_decl_rstruct_match =
  check_parse_success $ parse_pancake ex_global_decl_rstruct_match;

val static_global_decl_rstruct_match =
  check_static_success $ static_check_pancake parse_global_decl_rstruct_match;

val warns_global_decl_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_global_decl_rstruct_match;


val ex_global_decl_rstruct_mismatch_1 = `
  var {1} x = 1;
`;

val parse_global_decl_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_global_decl_rstruct_mismatch_1;

val static_global_decl_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_global_decl_rstruct_mismatch_1;

val warns_global_decl_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_rstruct_mismatch_1;


val ex_global_decl_rstruct_mismatch_2 = `
  var {1} x = <1, 1>;
`;

val parse_global_decl_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_global_decl_rstruct_mismatch_2;

val static_global_decl_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_global_decl_rstruct_mismatch_2;

val warns_global_decl_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_rstruct_mismatch_2;


val ex_global_decl_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  var {1} x = my_struct <value = 1>;
`;

val parse_global_decl_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_global_decl_rstruct_mismatch_3;

val static_global_decl_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_global_decl_rstruct_mismatch_3;

val warns_global_decl_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_rstruct_mismatch_3;


val ex_global_decl_nstruct_match = `
  struct my_struct {
    1 value
  }

  var my_struct x = my_struct <value = 1>;
`;

val parse_global_decl_nstruct_match =
  check_parse_success $ parse_pancake ex_global_decl_nstruct_match;

val static_global_decl_nstruct_match =
  check_static_success $ static_check_pancake parse_global_decl_nstruct_match;

val warns_global_decl_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_global_decl_nstruct_match;


val ex_global_decl_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  var my_struct x = 1;
`;

val parse_global_decl_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_global_decl_nstruct_mismatch_1;

val static_global_decl_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_global_decl_nstruct_mismatch_1;

val warns_global_decl_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_nstruct_mismatch_1;


val ex_global_decl_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  var my_struct x = <1>;
`;

val parse_global_decl_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_global_decl_nstruct_mismatch_2;

val static_global_decl_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_global_decl_nstruct_mismatch_2;

val warns_global_decl_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_nstruct_mismatch_2;


val ex_global_decl_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  var my_struct x = My_Struct <value = 1>;
`;

val parse_global_decl_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_global_decl_nstruct_mismatch_3;

val static_global_decl_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_global_decl_nstruct_mismatch_3;

val warns_global_decl_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_nstruct_mismatch_3;


(* Error: Mismatched variable assignments *)

val ex_local_asgn_word_match = `
  fun 1 f () {
    var 1 x = 0;
    x = 1;
    return 1;
  }
`;

val parse_local_asgn_word_match =
  check_parse_success $ parse_pancake ex_local_asgn_word_match;

val static_local_asgn_word_match =
  check_static_success $ static_check_pancake parse_local_asgn_word_match;

val warns_local_asgn_word_match =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_word_match;


val ex_local_asgn_word_mismatch_1 = `
  fun 1 f () {
    var 1 x = 0;
    x = <1>;
    return 1;
  }
`;

val parse_local_asgn_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_asgn_word_mismatch_1;

val static_local_asgn_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_asgn_word_mismatch_1;

val warns_local_asgn_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_word_mismatch_1;


val ex_local_asgn_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 0;
    x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_asgn_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_asgn_word_mismatch_2;

val static_local_asgn_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_asgn_word_mismatch_2;

val warns_local_asgn_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_word_mismatch_2;


val ex_local_asgn_rstruct_match = `
  fun 1 f () {
    var {1} x = <0>;
    x = <1>;
    return 1;
  }
`;

val parse_local_asgn_rstruct_match =
  check_parse_success $ parse_pancake ex_local_asgn_rstruct_match;

val static_local_asgn_rstruct_match =
  check_static_success $ static_check_pancake parse_local_asgn_rstruct_match;

val warns_local_asgn_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_rstruct_match;


val ex_local_asgn_rstruct_mismatch_1 = `
  fun 1 f () {
    var {1} x = <0>;
    x = 1;
    return 1;
  }
`;

val parse_local_asgn_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_asgn_rstruct_mismatch_1;

val static_local_asgn_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_asgn_rstruct_mismatch_1;

val warns_local_asgn_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_rstruct_mismatch_1;


val ex_local_asgn_rstruct_mismatch_2 = `
  fun 1 f () {
    var {1} x = <0>;
    x = <1, 1>;
    return 1;
  }
`;

val parse_local_asgn_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_asgn_rstruct_mismatch_2;

val static_local_asgn_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_asgn_rstruct_mismatch_2;

val warns_local_asgn_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_rstruct_mismatch_2;


val ex_local_asgn_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var {1} x = <0>;
    x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_asgn_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_asgn_rstruct_mismatch_3;

val static_local_asgn_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_asgn_rstruct_mismatch_3;

val warns_local_asgn_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_rstruct_mismatch_3;


val ex_local_asgn_nstruct_match = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct < value = 0 >;
    x = my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_asgn_nstruct_match =
  check_parse_success $ parse_pancake ex_local_asgn_nstruct_match;

val static_local_asgn_nstruct_match =
  check_static_success $ static_check_pancake parse_local_asgn_nstruct_match;

val warns_local_asgn_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_nstruct_match;


val ex_local_asgn_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct < value = 0 >;
    x = 1;
    return 1;
  }
`;

val parse_local_asgn_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_asgn_nstruct_mismatch_1;

val static_local_asgn_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_asgn_nstruct_mismatch_1;

val warns_local_asgn_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_nstruct_mismatch_1;


val ex_local_asgn_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct < value = 0 >;
    x = <1>;
    return 1;
  }
`;

val parse_local_asgn_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_asgn_nstruct_mismatch_2;

val static_local_asgn_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_asgn_nstruct_mismatch_2;

val warns_local_asgn_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_nstruct_mismatch_2;


val ex_local_asgn_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct < value = 0 >;
    x = My_Struct <value = 1>;
    return 1;
  }
`;

val parse_local_asgn_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_asgn_nstruct_mismatch_3;

val static_local_asgn_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_asgn_nstruct_mismatch_3;

val warns_local_asgn_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_nstruct_mismatch_3;


(* Error: Mismatched function arguments *)

val ex_func_arg_word_match = `
  fun 1 f () {
    g(1, 1);
    return 1;
  }
  fun 1 g (1 a, 1 b) {
    return 1;
  }
`;

val parse_func_arg_word_match =
  check_parse_success $ parse_pancake ex_func_arg_word_match;

val static_func_arg_word_match =
  check_static_success $ static_check_pancake parse_func_arg_word_match;

val warns_func_arg_word_match =
  check_static_no_warnings $ static_check_pancake parse_func_arg_word_match;


val ex_func_arg_word_mismatch_1 = `
  fun 1 f () {
    g(1, <1>);
    return 1;
  }
  fun 1 g (1 a, 1 b) {
    return 1;
  }
`;

val parse_func_arg_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_arg_word_mismatch_1;

val static_func_arg_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_arg_word_mismatch_1;

val warns_func_arg_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_word_mismatch_1;


val ex_func_arg_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    g(1, my_struct <value = 1>);
    return 1;
  }
  fun 1 g (1 a, 1 b) {
    return 1;
  }
`;

val parse_func_arg_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_arg_word_mismatch_2;

val static_func_arg_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_arg_word_mismatch_2;

val warns_func_arg_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_word_mismatch_2;


val ex_func_arg_rstruct_match = `
  fun 1 f () {
    g(1, <1>);
    return 1;
  }
  fun 1 g (1 a, {1} b) {
    return 1;
  }
`;

val parse_func_arg_rstruct_match =
  check_parse_success $ parse_pancake ex_func_arg_rstruct_match;

val static_func_arg_rstruct_match =
  check_static_success $ static_check_pancake parse_func_arg_rstruct_match;

val warns_func_arg_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_func_arg_rstruct_match;


val ex_func_arg_rstruct_mismatch_1 = `
  fun 1 f () {
    g(1, 1);
    return 1;
  }
  fun 1 g (1 a, {1} b) {
    return 1;
  }
`;

val parse_func_arg_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_arg_rstruct_mismatch_1;

val static_func_arg_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_arg_rstruct_mismatch_1;

val warns_func_arg_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_rstruct_mismatch_1;


val ex_func_arg_rstruct_mismatch_2 = `
  fun 1 f () {
    g(1, <1, 1>);
    return 1;
  }
  fun 1 g (1 a, {1} b) {
    return 1;
  }
`;

val parse_func_arg_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_arg_rstruct_mismatch_2;

val static_func_arg_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_arg_rstruct_mismatch_2;

val warns_func_arg_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_rstruct_mismatch_2;


val ex_func_arg_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    g(1, my_struct <value = 1>);
    return 1;
  }
  fun 1 g (1 a, {1} b) {
    return 1;
  }
`;

val parse_func_arg_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_func_arg_rstruct_mismatch_3;

val static_func_arg_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_func_arg_rstruct_mismatch_3;

val warns_func_arg_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_rstruct_mismatch_3;


val ex_func_arg_nstruct_match = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    g(1, my_struct <value = 1>);
    return 1;
  }
  fun 1 g (1 a, my_struct b) {
    return 1;
  }
`;

val parse_func_arg_nstruct_match =
  check_parse_success $ parse_pancake ex_func_arg_nstruct_match;

val static_func_arg_nstruct_match =
  check_static_success $ static_check_pancake parse_func_arg_nstruct_match;

val warns_func_arg_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_func_arg_nstruct_match;


val ex_func_arg_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    g(1, 1);
    return 1;
  }
  fun 1 g (1 a, my_struct b) {
    return 1;
  }
`;

val parse_func_arg_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_arg_nstruct_mismatch_1;

val static_func_arg_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_arg_nstruct_mismatch_1;

val warns_func_arg_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_nstruct_mismatch_1;


val ex_func_arg_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    g(1, <1>);
    return 1;
  }
  fun 1 g (1 a, my_struct b) {
    return 1;
  }
`;

val parse_func_arg_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_arg_nstruct_mismatch_2;

val static_func_arg_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_arg_nstruct_mismatch_2;

val warns_func_arg_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_nstruct_mismatch_2;


val ex_func_arg_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    g(1, My_Struct <value = 1>);
    return 1;
  }
  fun 1 g (1 a, my_struct b) {
    return 1;
  }
`;

val parse_func_arg_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_func_arg_nstruct_mismatch_3;

val static_func_arg_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_func_arg_nstruct_mismatch_3;

val warns_func_arg_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_nstruct_mismatch_3;


(* Error: Mismatched function returns *)

val ex_func_ret_word_match = `
  fun 1 f () {
    return 1;
  }
`;

val parse_func_ret_word_match =
  check_parse_success $ parse_pancake ex_func_ret_word_match;

val static_func_ret_word_match =
  check_static_success $ static_check_pancake parse_func_ret_word_match;

val warns_func_ret_word_match =
  check_static_no_warnings $ static_check_pancake parse_func_ret_word_match;


val ex_func_ret_word_mismatch_1 = `
  fun 1 f () {
    return <1>;
  }
`;

val parse_func_ret_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_ret_word_mismatch_1;

val static_func_ret_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_ret_word_mismatch_1;

val warns_func_ret_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_word_mismatch_1;


val ex_func_ret_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1>;
  }
`;

val parse_func_ret_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_ret_word_mismatch_2;

val static_func_ret_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_ret_word_mismatch_2;

val warns_func_ret_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_word_mismatch_2;


val ex_func_ret_rstruct_match = `
  fun {1} f () {
    return <1>;
  }
`;

val parse_func_ret_rstruct_match =
  check_parse_success $ parse_pancake ex_func_ret_rstruct_match;

val static_func_ret_rstruct_match =
  check_static_success $ static_check_pancake parse_func_ret_rstruct_match;

val warns_func_ret_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_func_ret_rstruct_match;


val ex_func_ret_rstruct_mismatch_1 = `
  fun {1} f () {
    return 1;
  }
`;

val parse_func_ret_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_ret_rstruct_mismatch_1;

val static_func_ret_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_ret_rstruct_mismatch_1;

val warns_func_ret_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_rstruct_mismatch_1;


val ex_func_ret_rstruct_mismatch_2 = `
  fun {1} f () {
    return <1, 1>;
  }
`;

val parse_func_ret_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_ret_rstruct_mismatch_2;

val static_func_ret_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_ret_rstruct_mismatch_2;

val warns_func_ret_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_rstruct_mismatch_2;


val ex_func_ret_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  fun {1} f () {
    return my_struct <value = 1>;
  }
`;

val parse_func_ret_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_func_ret_rstruct_mismatch_3;

val static_func_ret_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_func_ret_rstruct_mismatch_3;

val warns_func_ret_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_rstruct_mismatch_3;


val ex_func_ret_nstruct_match = `
  struct my_struct {
    1 value
  }

  fun my_struct f () {
    return my_struct <value = 1>;
  }
`;

val parse_func_ret_nstruct_match =
  check_parse_success $ parse_pancake ex_func_ret_nstruct_match;

val static_func_ret_nstruct_match =
  check_static_success $ static_check_pancake parse_func_ret_nstruct_match;

val warns_func_ret_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_func_ret_nstruct_match;


val ex_func_ret_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  fun my_struct f () {
    return 1;
  }
`;

val parse_func_ret_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_ret_nstruct_mismatch_1;

val static_func_ret_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_ret_nstruct_mismatch_1;

val warns_func_ret_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_nstruct_mismatch_1;


val ex_func_ret_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun my_struct f () {
    return <1>;
  }
`;

val parse_func_ret_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_ret_nstruct_mismatch_2;

val static_func_ret_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_ret_nstruct_mismatch_2;

val warns_func_ret_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_nstruct_mismatch_2;


val ex_func_ret_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun my_struct f () {
    return My_Struct <value = 1>;
  }
`;

val parse_func_ret_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_func_ret_nstruct_mismatch_3;

val static_func_ret_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_func_ret_nstruct_mismatch_3;

val warns_func_ret_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_nstruct_mismatch_3;


(* Error: Mismatched struct fields *)

val ex_field_val_word_match = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <x = 1, y = 1>;
`;

val parse_field_val_word_match =
  check_parse_success $ parse_pancake ex_field_val_word_match;

val static_field_val_word_match =
  check_static_success $ static_check_pancake parse_field_val_word_match;

val warns_field_val_word_match =
  check_static_no_warnings $ static_check_pancake parse_field_val_word_match;


val ex_field_val_word_mismatch_1 = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <x = 1, y = <1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_field_val_word_mismatch_1;

val static_field_val_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_field_val_word_mismatch_1;

val warns_field_val_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_field_val_word_mismatch_1;


val ex_field_val_word_mismatch_2 = `
  struct my_struct {
    1 x,
    1 y
  }
  
  struct other_struct {
    1 value
  }

  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_field_val_word_mismatch_2;

val static_field_val_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_field_val_word_mismatch_2;

val warns_field_val_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_field_val_word_mismatch_2;


val ex_field_val_rstruct_match = `
  struct my_struct {
    1 x,
    {1} y
  }

  var my_struct s = my_struct <x = 1, y = <1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_rstruct_match =
  check_parse_success $ parse_pancake ex_field_val_rstruct_match;

val static_field_val_rstruct_match =
  check_static_success $ static_check_pancake parse_field_val_rstruct_match;

val warns_field_val_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_field_val_rstruct_match;


val ex_field_val_rstruct_mismatch_1 = `
  struct my_struct {
    1 x,
    {1} y
  }

  var my_struct s = my_struct <x = 1, y = 1>;
`;

val parse_field_val_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_field_val_rstruct_mismatch_1;

val static_field_val_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_field_val_rstruct_mismatch_1;

val warns_field_val_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_field_val_rstruct_mismatch_1;


val ex_field_val_rstruct_mismatch_2 = `
  struct my_struct {
    1 x,
    {1} y
  }

  var my_struct s = my_struct <x = 1, y = <1, 1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_field_val_rstruct_mismatch_2;

val static_field_val_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_field_val_rstruct_mismatch_2;

val warns_field_val_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_field_val_rstruct_mismatch_2;


val ex_field_val_rstruct_mismatch_3 = `
  struct my_struct {
    1 x,
    {1} y
  }

  struct other_struct {
    1 value
  }

  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_field_val_rstruct_mismatch_3;

val static_field_val_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_field_val_rstruct_mismatch_3;

val warns_field_val_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_field_val_rstruct_mismatch_3;


val ex_field_val_nstruct_match = `
  struct your_struct {
    1 value
  }

  struct my_struct {
    1 x,
    your_struct y
  }

  var my_struct s = my_struct <x = 1, y = your_struct <value = 1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_nstruct_match =
  check_parse_success $ parse_pancake ex_field_val_nstruct_match;

val static_field_val_nstruct_match =
  check_static_success $ static_check_pancake parse_field_val_nstruct_match;

val warns_field_val_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_field_val_nstruct_match;


val ex_field_val_nstruct_mismatch_1 = `
  struct your_struct {
    1 value
  }

  struct my_struct {
    1 x,
    your_struct y
  }

  var my_struct s = my_struct <x = 1, y = 1>;
`;

val parse_field_val_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_field_val_nstruct_mismatch_1;

val static_field_val_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_field_val_nstruct_mismatch_1;

val warns_field_val_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_field_val_nstruct_mismatch_1;


val ex_field_val_nstruct_mismatch_2 = `
  struct your_struct {
    1 value
  }

  struct my_struct {
    1 x,
    your_struct y
  }

  var my_struct s = my_struct <x = 1, y = <1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_field_val_nstruct_mismatch_2;

val static_field_val_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_field_val_nstruct_mismatch_2;

val warns_field_val_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_field_val_nstruct_mismatch_2;


val ex_field_val_nstruct_mismatch_3 = `
  struct your_struct {
    1 value
  }

  struct my_struct {
    1 x,
    your_struct y
  }

  struct other_struct {
    1 value
  }

  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_field_val_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_field_val_nstruct_mismatch_3;

val static_field_val_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_field_val_nstruct_mismatch_3;

val warns_field_val_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_field_val_nstruct_mismatch_3;


(* Error: Incorrect number of struct field values *)

val ex_struct_field_missing = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <x = 1>;
`;

val parse_struct_field_missing =
  check_parse_success $ parse_pancake ex_struct_field_missing;

val static_struct_field_missing =
  check_static_failure $ static_check_pancake parse_struct_field_missing;

val warns_struct_field_missing =
  check_static_no_warnings $ static_check_pancake parse_struct_field_missing;


val ex_struct_field_extra = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <x = 1, y = 1, z = 1>;
`;

val parse_struct_field_extra =
  check_parse_success $ parse_pancake ex_struct_field_extra;

val static_struct_field_extra =
  check_static_failure $ static_check_pancake parse_struct_field_extra;

val warns_struct_field_extra =
  check_static_no_warnings $ static_check_pancake parse_struct_field_extra;


val ex_struct_field_duplicate = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <x = 1, y = 1, x = 1>;
`;

val parse_struct_field_duplicate =
  check_parse_success $ parse_pancake ex_struct_field_duplicate;

val static_struct_field_duplicate =
  check_static_failure $ static_check_pancake parse_struct_field_duplicate;

val warns_struct_field_duplicate =
  check_static_no_warnings $ static_check_pancake parse_struct_field_duplicate;


val ex_struct_field_reordered = `
  struct my_struct {
    1 x,
    1 y
  }

  var my_struct s = my_struct <y = 1, x = 1>;
`;

val parse_struct_field_reordered =
  check_parse_success $ parse_pancake ex_struct_field_reordered;

val static_struct_field_reordered =
  check_static_success $ static_check_pancake parse_struct_field_reordered;

val warns_struct_field_reordered =
  check_static_no_warnings $ static_check_pancake parse_struct_field_reordered;


(* Error: Mismatched source/destination for memory operations *)

val ex_local_lds_word_match = `
  fun 1 f () {
    var 1 x = lds 1 @base;
    return 1;
  }
`;

val parse_local_lds_word_match =
  check_parse_success $ parse_pancake ex_local_lds_word_match;

val static_local_lds_word_match =
  check_static_success $ static_check_pancake parse_local_lds_word_match;

val warns_local_lds_word_match =
  check_static_no_warnings $ static_check_pancake parse_local_lds_word_match;


val ex_local_lds_word_mismatch_1 = `
  fun 1 f () {
    var {1} x = lds 1 @base;
    return 1;
  }
`;

val parse_local_lds_word_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_lds_word_mismatch_1;

val static_local_lds_word_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_lds_word_mismatch_1;

val warns_local_lds_word_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_word_mismatch_1;


val ex_local_lds_word_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = lds 1 @base;
    return 1;
  }
`;

val parse_local_lds_word_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_lds_word_mismatch_2;

val static_local_lds_word_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_lds_word_mismatch_2;

val warns_local_lds_word_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_word_mismatch_2;


val ex_local_lds_rstruct_match = `
  fun 1 f () {
    var {1} x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_rstruct_match =
  check_parse_success $ parse_pancake ex_local_lds_rstruct_match;

val static_local_lds_rstruct_match =
  check_static_success $ static_check_pancake parse_local_lds_rstruct_match;

val warns_local_lds_rstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_lds_rstruct_match;


val ex_local_lds_rstruct_mismatch_1 = `
  fun 1 f () {
    var 1 x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_rstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_lds_rstruct_mismatch_1;

val static_local_lds_rstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_lds_rstruct_mismatch_1;

val warns_local_lds_rstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_rstruct_mismatch_1;


val ex_local_lds_rstruct_mismatch_2 = `
  fun 1 f () {
    var 2 x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_rstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_lds_rstruct_mismatch_2;

val static_local_lds_rstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_lds_rstruct_mismatch_2;

val warns_local_lds_rstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_rstruct_mismatch_2;


val ex_local_lds_rstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_rstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_lds_rstruct_mismatch_3;

val static_local_lds_rstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_lds_rstruct_mismatch_3;

val warns_local_lds_rstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_rstruct_mismatch_3;


val ex_local_lds_nstruct_match = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = lds my_struct @base;
    return 1;
  }
`;

val parse_local_lds_nstruct_match =
  check_parse_success $ parse_pancake ex_local_lds_nstruct_match;

val static_local_lds_nstruct_match =
  check_static_success $ static_check_pancake parse_local_lds_nstruct_match;

val warns_local_lds_nstruct_match =
  check_static_no_warnings $ static_check_pancake parse_local_lds_nstruct_match;


val ex_local_lds_nstruct_mismatch_1 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = lds my_struct @base;
    return 1;
  }
`;

val parse_local_lds_nstruct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_lds_nstruct_mismatch_1;

val static_local_lds_nstruct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_lds_nstruct_mismatch_1;

val warns_local_lds_nstruct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_nstruct_mismatch_1;


val ex_local_lds_nstruct_mismatch_2 = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var {1} x = lds my_struct @base;
    return 1;
  }
`;

val parse_local_lds_nstruct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_lds_nstruct_mismatch_2;

val static_local_lds_nstruct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_lds_nstruct_mismatch_2;

val warns_local_lds_nstruct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_nstruct_mismatch_2;


val ex_local_lds_nstruct_mismatch_3 = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    var My_Struct x = lds my_struct @base;
    return 1;
  }
`;

val parse_local_lds_nstruct_mismatch_3 =
  check_parse_success $ parse_pancake ex_local_lds_nstruct_mismatch_3;

val static_local_lds_nstruct_mismatch_3 =
  check_static_failure $ static_check_pancake parse_local_lds_nstruct_mismatch_3;

val warns_local_lds_nstruct_mismatch_3 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_nstruct_mismatch_3;


val ex_local_ld8_word_dest = `
  fun 1 f () {
    var 1 x = ld8 @base;
    return 1;
  }
`;

val parse_local_ld8_word_dest =
  check_parse_success $ parse_pancake ex_local_ld8_word_dest;

val static_local_ld8_word_dest =
  check_static_success $ static_check_pancake parse_local_ld8_word_dest;

val warns_local_ld8_word_dest =
  check_static_no_warnings $ static_check_pancake parse_local_ld8_word_dest;


val ex_local_ld8_rstruct_dest = `
  fun 1 f () {
    var {1} x = ld8 @base;
    return 1;
  }
`;

val parse_local_ld8_rstruct_dest =
  check_parse_success $ parse_pancake ex_local_ld8_rstruct_dest;

val static_local_ld8_rstruct_dest =
  check_static_failure $ static_check_pancake parse_local_ld8_rstruct_dest;

val warns_local_ld8_rstruct_dest =
  check_static_no_warnings $ static_check_pancake parse_local_ld8_rstruct_dest;


val ex_local_ld8_nstruct_dest = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = ld8 @base;
    return 1;
  }
`;

val parse_local_ld8_nstruct_dest =
  check_parse_success $ parse_pancake ex_local_ld8_nstruct_dest;

val static_local_ld8_nstruct_dest =
  check_static_failure $ static_check_pancake parse_local_ld8_nstruct_dest;

val warns_local_ld8_nstruct_dest =
  check_static_no_warnings $ static_check_pancake parse_local_ld8_nstruct_dest;


val ex_shared_ldw_word_dest = `
  fun 1 f () {
    var 1 x = 1;
    !ldw x, 0;
    return 1;
  }
`;

val parse_shared_ldw_word_dest =
  check_parse_success $ parse_pancake ex_shared_ldw_word_dest;

val static_shared_ldw_word_dest =
  check_static_success $ static_check_pancake parse_shared_ldw_word_dest;

val warns_shared_ldw_word_dest =
  check_static_no_warnings $ static_check_pancake parse_shared_ldw_word_dest;


val ex_shared_ldw_rstruct_dest = `
  fun 1 f () {
    var {1} x = <1>;
    !ldw x, 0;
    return 1;
  }
`;

val parse_shared_ldw_rstruct_dest =
  check_parse_success $ parse_pancake ex_shared_ldw_rstruct_dest;

val static_shared_ldw_rstruct_dest =
  check_static_failure $ static_check_pancake parse_shared_ldw_rstruct_dest;

val warns_shared_ldw_rstruct_dest =
  check_static_no_warnings $ static_check_pancake parse_shared_ldw_rstruct_dest;


val ex_shared_ldw_nstruct_dest = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 1>;
    !ldw x, 0;
    return 1;
  }
`;

val parse_shared_ldw_nstruct_dest =
  check_parse_success $ parse_pancake ex_shared_ldw_nstruct_dest;

val static_shared_ldw_nstruct_dest =
  check_static_failure $ static_check_pancake parse_shared_ldw_nstruct_dest;

val warns_shared_ldw_nstruct_dest =
  check_static_no_warnings $ static_check_pancake parse_shared_ldw_nstruct_dest;


val ex_shared_stw_word_src = `
  fun 1 f () {
    var 1 x = 1;
    !stw 0, x;
    return 1;
  }
`;

val parse_shared_stw_word_src =
  check_parse_success $ parse_pancake ex_shared_stw_word_src;

val static_shared_stw_word_src =
  check_static_success $ static_check_pancake parse_shared_stw_word_src;

val warns_shared_stw_word_src =
  check_static_no_warnings $ static_check_pancake parse_shared_stw_word_src;


val ex_shared_stw_rstruct_src = `
  fun 1 f () {
    var {1} x = <1>;
    !stw 0, x;
    return 1;
  }
`;

val parse_shared_stw_rstruct_src =
  check_parse_success $ parse_pancake ex_shared_stw_rstruct_src;

val static_shared_stw_rstruct_src =
  check_static_failure $ static_check_pancake parse_shared_stw_rstruct_src;

val warns_shared_stw_rstruct_src =
  check_static_no_warnings $ static_check_pancake parse_shared_stw_rstruct_src;


val ex_shared_stw_nstruct_src = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 1>;
    !stw 0, x;
    return 1;
  }
`;

val parse_shared_stw_nstruct_src =
  check_parse_success $ parse_pancake ex_shared_stw_nstruct_src;

val static_shared_stw_nstruct_src =
  check_static_failure $ static_check_pancake parse_shared_stw_nstruct_src;

val warns_shared_stw_nstruct_src =
  check_static_no_warnings $ static_check_pancake parse_shared_stw_nstruct_src;


(* Error: Non-word main function return declarations *)

val ex_main_rstruct_ret = `
  fun {1} main () {
    return <1>;
  }
`;

val parse_main_rstruct_ret =
  check_parse_success $ parse_pancake ex_main_rstruct_ret;

val static_main_rstruct_ret =
  check_static_failure $ static_check_pancake parse_main_rstruct_ret;

val warns_main_rstruct_ret =
  check_static_no_warnings $ static_check_pancake parse_main_rstruct_ret;


val ex_main_nstruct_ret = `
  struct my_struct {
    1 value
  }

  fun my_struct main () {
    return my_struct <value = 1>;
  }
`;

val parse_main_nstruct_ret =
  check_parse_success $ parse_pancake ex_main_nstruct_ret;

val static_main_nstruct_ret =
  check_static_failure $ static_check_pancake parse_main_nstruct_ret;

val warns_main_nstruct_ret =
  check_static_no_warnings $ static_check_pancake parse_main_nstruct_ret;


(* Error: Non-word FFI arguments *)

val ex_ffi_rstruct_lit_arg = `
  fun 1 f () {
    @g(1, 2, 3, <4>);
    return 1;
  }
`;

val parse_ffi_rstruct_lit_arg =
  check_parse_success $ parse_pancake ex_ffi_rstruct_lit_arg;

val static_ffi_rstruct_lit_arg =
  check_static_failure $ static_check_pancake parse_ffi_rstruct_lit_arg;

val warns_ffi_rstruct_lit_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_rstruct_lit_arg;


val ex_ffi_rstruct_var_arg = `
  fun 1 f () {
    var {1} x = <0>;
    @g(1, x, 3, 4);
    return 1;
  }
`;

val parse_ffi_rstruct_var_arg =
  check_parse_success $ parse_pancake ex_ffi_rstruct_var_arg;

val static_ffi_rstruct_var_arg =
  check_static_failure $ static_check_pancake parse_ffi_rstruct_var_arg;

val warns_ffi_rstruct_var_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_rstruct_var_arg;


val ex_ffi_nstruct_lit_arg = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    @g(1, 2, 3, my_struct <value = 4>);
    return 1;
  }
`;

val parse_ffi_nstruct_lit_arg =
  check_parse_success $ parse_pancake ex_ffi_nstruct_lit_arg;

val static_ffi_nstruct_lit_arg =
  check_static_failure $ static_check_pancake parse_ffi_nstruct_lit_arg;

val warns_ffi_nstruct_lit_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_nstruct_lit_arg;


val ex_ffi_nstruct_var_arg = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 0>;
    @g(1, x, 3, 4);
    return 1;
  }
`;

val parse_ffi_nstruct_var_arg =
  check_parse_success $ parse_pancake ex_ffi_nstruct_var_arg;

val static_ffi_nstruct_var_arg =
  check_static_failure $ static_check_pancake parse_ffi_rstruct_var_arg;

val warns_ffi_nstruct_var_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_nstruct_var_arg;


(* Error: Non-word exported argument declarations *)

val ex_export_rstruct_arg = `
  export fun 1 f ({1} a) {
    return 1;
  }
`;

val parse_export_rstruct_arg =
  check_parse_success $ parse_pancake ex_export_rstruct_arg;

val static_export_rstruct_arg =
  check_static_failure $ static_check_pancake parse_export_rstruct_arg;

val warns_export_rstruct_arg =
  check_static_no_warnings $ static_check_pancake parse_export_rstruct_arg;


val ex_export_nstruct_arg = `
  struct my_struct {
    1 value
  }

  export fun 1 f (my_struct a) {
    return 1;
  }
`;

val parse_export_nstruct_arg =
  check_parse_success $ parse_pancake ex_export_nstruct_arg;

val static_export_nstruct_arg =
  check_static_failure $ static_check_pancake parse_export_nstruct_arg;

val warns_export_nstruct_arg =
  check_static_no_warnings $ static_check_pancake parse_export_nstruct_arg;


(* Error: Non-word exported return declarations *)

val ex_export_rstruct_ret = `
  export fun {1} f () {
    return <1>;
  }
`;

val parse_export_rstruct_ret =
  check_parse_success $ parse_pancake ex_export_rstruct_ret;

val static_export_rstruct_ret =
  check_static_failure $ static_check_pancake parse_export_rstruct_ret;

val warns_export_rstruct_ret =
  check_static_no_warnings $ static_check_pancake parse_export_rstruct_ret;


val ex_export_nstruct_ret = `
  struct my_struct {
    1 value
  }

  export fun my_struct f () {
    return my_struct <value = 1>;
  }
`;

val parse_export_nstruct_ret =
  check_parse_success $ parse_pancake ex_export_nstruct_ret;

val static_export_nstruct_ret =
  check_static_failure $ static_check_pancake parse_export_nstruct_ret;

val warns_export_nstruct_ret =
  check_static_no_warnings $ static_check_pancake parse_export_nstruct_ret;


(* Error: Non-word addresses for memory operations *)

val ex_local_load_rstruct_addr = `
  fun 1 f () {
    var 1 x = lds 1 <1>;
    return 1;
  }
`;

val parse_local_load_rstruct_addr =
  check_parse_success $ parse_pancake ex_local_load_rstruct_addr;

val static_local_load_rstruct_addr =
  check_static_failure $ static_check_pancake parse_local_load_rstruct_addr;

val warns_local_load_rstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_load_rstruct_addr;


val ex_local_load_nstruct_addr = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = lds 1 my_struct <value = 1>;
    return 1;
  }
`;

val parse_local_load_nstruct_addr =
  check_parse_success $ parse_pancake ex_local_load_nstruct_addr;

val static_local_load_nstruct_addr =
  check_static_failure $ static_check_pancake parse_local_load_nstruct_addr;

val warns_local_load_nstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_load_nstruct_addr;


val ex_local_store_rstruct_addr = `
  fun 1 f () {
    var 1 x = 1;
    st <1>, x;
    return 1;
  }
`;

val parse_local_store_rstruct_addr =
  check_parse_success $ parse_pancake ex_local_store_rstruct_addr;

val static_local_store_rstruct_addr =
  check_static_failure $ static_check_pancake parse_local_store_rstruct_addr;

val warns_local_store_rstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_store_rstruct_addr;


val ex_local_store_nstruct_addr = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 1;
    st my_struct <value = 1>, x;
    return 1;
  }
`;

val parse_local_store_nstruct_addr =
  check_parse_success $ parse_pancake ex_local_store_nstruct_addr;

val static_local_store_nstruct_addr =
  check_static_failure $ static_check_pancake parse_local_store_nstruct_addr;

val warns_local_store_nstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_store_nstruct_addr;


val ex_shared_load_rstruct_addr = `
  fun 1 f () {
    var 1 x = 1;
    !ldw x, <1>;
    return 1;
  }
`;

val parse_shared_load_rstruct_addr =
  check_parse_success $ parse_pancake ex_shared_load_rstruct_addr;

val static_shared_load_rstruct_addr =
  check_static_failure $ static_check_pancake parse_shared_load_rstruct_addr;

val warns_shared_load_rstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_load_rstruct_addr;


val ex_shared_load_nstruct_addr = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 1;
    !ldw x, my_struct <value = 1>;
    return 1;
  }
`;

val parse_shared_load_nstruct_addr =
  check_parse_success $ parse_pancake ex_shared_load_nstruct_addr;

val static_shared_load_nstruct_addr =
  check_static_failure $ static_check_pancake parse_shared_load_nstruct_addr;

val warns_shared_load_nstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_load_nstruct_addr;


val ex_shared_store_rstruct_addr = `
  fun 1 f () {
    var 1 x = 1;
    !stw <1>, x;
    return 1;
  }
`;

val parse_shared_store_rstruct_addr =
  check_parse_success $ parse_pancake ex_shared_store_rstruct_addr;

val static_shared_store_rstruct_addr =
  check_static_failure $ static_check_pancake parse_shared_store_rstruct_addr;

val warns_shared_store_rstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_store_rstruct_addr;


val ex_shared_store_nstruct_addr = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 1;
    !stw my_struct <value = 1>, x;
    return 1;
  }
`;

val parse_shared_store_nstruct_addr =
  check_parse_success $ parse_pancake ex_shared_store_nstruct_addr;

val static_shared_store_nstruct_addr =
  check_static_failure $ static_check_pancake parse_shared_store_nstruct_addr;

val warns_shared_store_nstruct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_store_nstruct_addr;


(* Error: Non-word/mismatched operator operands *)

val ex_add_one_rstruct_operand = `
  fun 1 f () {
    return 1 + <2>;
  }
`;

val parse_add_one_rstruct_operand =
  check_parse_success $ parse_pancake ex_add_one_rstruct_operand;

val static_add_one_rstruct_operand =
  check_static_failure $ static_check_pancake parse_add_one_rstruct_operand;

val warns_add_one_rstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_add_one_rstruct_operand;


val ex_add_all_rstruct_operands = `
  fun 1 f () {
    return <1> + <2, 3>;
  }
`;

val parse_add_all_rstruct_operands =
  check_parse_success $ parse_pancake ex_add_all_rstruct_operands;

val static_add_all_rstruct_operands =
  check_static_failure $ static_check_pancake parse_add_all_rstruct_operands;

val warns_add_all_rstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_add_all_rstruct_operands;


val ex_add_one_nstruct_operand = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return 1 + my_struct <value = 2>;
  }
`;

val parse_add_one_nstruct_operand =
  check_parse_success $ parse_pancake ex_add_one_nstruct_operand;

val static_add_one_nstruct_operand =
  check_static_failure $ static_check_pancake parse_add_one_nstruct_operand;

val warns_add_one_nstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_add_one_nstruct_operand;


val ex_add_all_nstruct_operands = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> + My_Struct <value = 3>;
  }
`;

val parse_add_all_nstruct_operands =
  check_parse_success $ parse_pancake ex_add_all_nstruct_operands;

val static_add_all_nstruct_operands =
  check_static_failure $ static_check_pancake parse_add_all_nstruct_operands;

val warns_add_all_nstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_add_all_nstruct_operands;


val ex_add_both_struct_operands = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> + <2, 3>;
  }
`;

val parse_add_both_struct_operands =
  check_parse_success $ parse_pancake ex_add_both_struct_operands;

val static_add_both_struct_operands =
  check_static_failure $ static_check_pancake parse_add_both_struct_operands;

val warns_add_both_struct_operands =
  check_static_no_warnings $ static_check_pancake parse_add_both_struct_operands;


val ex_mult_one_rstruct_operand = `
  fun 1 f () {
    return 1 * <2>;
  }
`;

val parse_mult_one_rstruct_operand =
  check_parse_success $ parse_pancake ex_mult_one_rstruct_operand;

val static_mult_one_rstruct_operand =
  check_static_failure $ static_check_pancake parse_mult_one_rstruct_operand;

val warns_mult_one_rstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_mult_one_rstruct_operand;


val ex_mult_all_rstruct_operands = `
  fun 1 f () {
    return <1> * <2, 3>;
  }
`;

val parse_mult_all_rstruct_operands =
  check_parse_success $ parse_pancake ex_mult_all_rstruct_operands;

val static_mult_all_rstruct_operands =
  check_static_failure $ static_check_pancake parse_mult_all_rstruct_operands;

val warns_mult_all_rstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_mult_all_rstruct_operands;


val ex_mult_one_nstruct_operand = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return 1 * my_struct <value = 2>;
  }
`;

val parse_mult_one_nstruct_operand =
  check_parse_success $ parse_pancake ex_mult_one_nstruct_operand;

val static_mult_one_nstruct_operand =
  check_static_failure $ static_check_pancake parse_mult_one_nstruct_operand;

val warns_mult_one_nstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_mult_one_nstruct_operand;


val ex_mult_all_nstruct_operands = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> * My_Struct <value = 3>;
  }
`;

val parse_mult_all_nstruct_operands =
  check_parse_success $ parse_pancake ex_mult_all_nstruct_operands;

val static_mult_all_nstruct_operands =
  check_static_failure $ static_check_pancake parse_mult_all_nstruct_operands;

val warns_mult_all_nstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_mult_all_nstruct_operands;


val ex_mult_both_struct_operands = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> * <2, 3>;
  }
`;

val parse_mult_both_struct_operands =
  check_parse_success $ parse_pancake ex_mult_both_struct_operands;

val static_mult_both_struct_operands =
  check_static_failure $ static_check_pancake parse_mult_both_struct_operands;

val warns_mult_both_struct_operands =
  check_static_no_warnings $ static_check_pancake parse_mult_both_struct_operands;


val ex_shift_rstruct_operand = `
  fun 1 f () {
    return <1> << 2;
  }
`;

val parse_shift_rstruct_operand =
  check_parse_success $ parse_pancake ex_shift_rstruct_operand;

val static_shift_rstruct_operand =
  check_static_failure $ static_check_pancake parse_shift_rstruct_operand;

val warns_shift_rstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_shift_rstruct_operand;


val ex_shift_nstruct_operand = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> << 2;
  }
`;

val parse_shift_nstruct_operand =
  check_parse_success $ parse_pancake ex_shift_nstruct_operand;

val static_shift_nstruct_operand =
  check_static_failure $ static_check_pancake parse_shift_nstruct_operand;

val warns_shift_nstruct_operand =
  check_static_no_warnings $ static_check_pancake parse_shift_nstruct_operand;


val ex_cmp_word_rstruct_operands = `
  fun 1 f () {
    return 0 == <1>;
  }
`;

val parse_cmp_word_rstruct_operands =
  check_parse_success $ parse_pancake ex_cmp_word_rstruct_operands;

val static_cmp_word_rstruct_operands =
  check_static_failure $ static_check_pancake parse_cmp_word_rstruct_operands;

val warns_cmp_word_rstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_word_rstruct_operands;


val ex_cmp_word_nstruct_operands = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return 0 == my_struct <value = 1>;
  }
`;

val parse_cmp_word_nstruct_operands =
  check_parse_success $ parse_pancake ex_cmp_word_nstruct_operands;

val static_cmp_word_nstruct_operands =
  check_static_failure $ static_check_pancake parse_cmp_word_nstruct_operands;

val warns_cmp_word_nstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_word_nstruct_operands;


val ex_cmp_rstruct_nstruct_operands = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    return <1> == my_struct <value = 1>;
  }
`;

val parse_cmp_rstruct_nstruct_operands =
  check_parse_success $ parse_pancake ex_cmp_rstruct_nstruct_operands;

val static_cmp_rstruct_nstruct_operands =
  check_static_failure $ static_check_pancake parse_cmp_rstruct_nstruct_operands;

val warns_cmp_rstruct_nstruct_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_rstruct_nstruct_operands;


val ex_cmp_diff_rstructs_operands = `
  fun 1 f () {
    return <1> == <2, 3>;
  }
`;

val parse_cmp_diff_rstructs_operands =
  check_parse_success $ parse_pancake ex_cmp_diff_rstructs_operands;

val static_cmp_diff_rstructs_operands =
  check_static_failure $ static_check_pancake parse_cmp_diff_rstructs_operands;

val warns_cmp_diff_rstructs_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_diff_rstructs_operands;


val ex_cmp_diff_nstructs_operands = `
  struct my_struct {
    1 value
  }

  struct My_Struct {
    1 value
  }

  fun 1 f () {
    return my_struct <value = 1> == My_Struct <value = 1>;
  }
`;

val parse_cmp_diff_nstructs_operands =
  check_parse_success $ parse_pancake ex_cmp_diff_nstructs_operands;

val static_cmp_diff_nstructs_operands =
  check_static_failure $ static_check_pancake parse_cmp_diff_nstructs_operands;

val warns_cmp_diff_nstructs_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_diff_nstructs_operands;


(* Error: Non-word condition expressions *)

val ex_if_cond_rstruct = `
  fun 1 f () {
    if <1> {
      skip;
    }
    return 1;
  }
`;

val parse_if_cond_rstruct =
  check_parse_success $ parse_pancake ex_if_cond_rstruct;

val static_if_cond_rstruct =
  check_static_failure $ static_check_pancake parse_if_cond_rstruct;

val warns_if_cond_rstruct =
  check_static_no_warnings $ static_check_pancake parse_if_cond_rstruct;


val ex_if_cond_nstruct = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    if my_struct <value = 1> {
      skip;
    }
    return 1;
  }
`;

val parse_if_cond_nstruct =
  check_parse_success $ parse_pancake ex_if_cond_nstruct;

val static_if_cond_nstruct =
  check_static_failure $ static_check_pancake parse_if_cond_nstruct;

val warns_if_cond_nstruct =
  check_static_no_warnings $ static_check_pancake parse_if_cond_nstruct;


val ex_while_cond_rstruct = `
  fun 1 f () {
    while <1> {
      skip;
    }
    return 1;
  }
`;

val parse_while_cond_rstruct =
  check_parse_success $ parse_pancake ex_while_cond_rstruct;

val static_while_cond_rstruct =
  check_static_failure $ static_check_pancake parse_while_cond_rstruct;

val warns_while_cond_rstruct =
  check_static_no_warnings $ static_check_pancake parse_while_cond_rstruct;


val ex_while_cond_nstruct = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    while my_struct <value = 1> {
      skip;
    }
    return 1;
  }
`;

val parse_while_cond_nstruct =
  check_parse_success $ parse_pancake ex_while_cond_nstruct;

val static_while_cond_nstruct =
  check_static_failure $ static_check_pancake parse_while_cond_nstruct;

val warns_while_cond_nstruct =
  check_static_no_warnings $ static_check_pancake parse_while_cond_nstruct;


(* Error: Invalid field index *)

val ex_valid_rstruct_lit_index = `
  fun 1 f () {
    var 1 x = <0>.0;
    return 1;
  }
`;

val parse_valid_rstruct_lit_index =
  check_parse_success $ parse_pancake ex_valid_rstruct_lit_index;

val static_valid_rstruct_lit_index =
  check_static_success $ static_check_pancake parse_valid_rstruct_lit_index;

val warns_valid_rstruct_lit_index =
  check_static_no_warnings $ static_check_pancake parse_valid_rstruct_lit_index;


val ex_valid_rstruct_var_index = `
  fun 1 f () {
    var {1} x = <0>;
    var 1 y = x.0;
    return 1;
  }
`;

val parse_valid_rstruct_var_index =
  check_parse_success $ parse_pancake ex_valid_rstruct_var_index;

val static_valid_rstruct_var_index =
  check_static_success $ static_check_pancake parse_valid_rstruct_var_index;

val warns_valid_rstruct_var_index =
  check_static_no_warnings $ static_check_pancake parse_valid_rstruct_var_index;


val ex_invalid_rstruct_lit_index = `
  fun 1 f () {
    var 1 x = <0>.5;
    return 1;
  }
`;

val parse_invalid_rstruct_lit_index =
  check_parse_success $ parse_pancake ex_invalid_rstruct_lit_index;

val static_invalid_rstruct_lit_index =
  check_static_failure $ static_check_pancake parse_invalid_rstruct_lit_index;

val warns_invalid_rstruct_lit_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_rstruct_lit_index;


val ex_invalid_rstruct_var_index = `
  fun 1 f () {
    var {1} x = <0>;
    var 1 y = x.5;
    return 1;
  }
`;

val parse_invalid_rstruct_var_index =
  check_parse_success $ parse_pancake ex_invalid_rstruct_var_index;

val static_invalid_rstruct_var_index =
  check_static_failure $ static_check_pancake parse_invalid_rstruct_var_index;

val warns_invalid_rstruct_var_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_rstruct_var_index;


val ex_invalid_word_lit_index = `
  fun 1 f () {
    var 1 x = 0.5;
    return 1;
  }
`;

val parse_invalid_word_lit_index =
  check_parse_success $ parse_pancake ex_invalid_word_lit_index;

val static_invalid_word_lit_index =
  check_static_failure $ static_check_pancake parse_invalid_word_lit_index;

val warns_invalid_word_lit_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_word_lit_index;


val ex_invalid_word_var_index = `
  fun 1 f () {
    var 1 x = 0;
    var 1 y = x.5;
    return 1;
  }
`;

val parse_invalid_word_var_index =
  check_parse_success $ parse_pancake ex_invalid_word_var_index;

val static_invalid_word_var_index =
  check_static_failure $ static_check_pancake parse_invalid_word_var_index;

val warns_invalid_word_var_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_word_var_index;


val ex_invalid_nstruct_lit_index = `
  struct my_struct {
    1 value0,
    1 value1,
    1 value2,
    1 value3,
    1 value4,
    1 value5
  }

  fun 1 f () {
    var my_struct x = my_struct <
      value0 = 1,
      value1 = 1,
      value2 = 1,
      value3 = 1,
      value4 = 1,
      value5 = 1
    >.5;
    return 1;
  }
`;

val parse_invalid_nstruct_lit_index =
  check_parse_success $ parse_pancake ex_invalid_nstruct_lit_index;

val static_invalid_nstruct_lit_index =
  check_static_failure $ static_check_pancake parse_invalid_nstruct_lit_index;

val warns_invalid_nstruct_lit_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_nstruct_lit_index;


val ex_invalid_nstruct_var_index = `
  struct my_struct {
    1 value0,
    1 value1,
    1 value2,
    1 value3,
    1 value4,
    1 value5
  }

  fun 1 f () {
    var my_struct x = my_struct <
      value0 = 1,
      value1 = 1,
      value2 = 1,
      value3 = 1,
      value4 = 1,
      value5 = 1
    >;
    var 1 y = x.5;
    return 1;
  }
`;

val parse_invalid_nstruct_var_index =
  check_parse_success $ parse_pancake ex_invalid_nstruct_var_index;

val static_invalid_nstruct_var_index =
  check_static_failure $ static_check_pancake parse_invalid_nstruct_var_index;

val warns_invalid_nstruct_var_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_nstruct_var_index;


(* Error: Invalid field name *)

val ex_valid_nstruct_lit_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = my_struct <value = 0>.value;
    return 1;
  }
`;

val parse_valid_nstruct_lit_field =
  check_parse_success $ parse_pancake ex_valid_nstruct_lit_field;

val static_valid_nstruct_lit_field =
  check_static_success $ static_check_pancake parse_valid_nstruct_lit_field;

val warns_valid_nstruct_lit_field =
  check_static_no_warnings $ static_check_pancake parse_valid_nstruct_lit_field;


val ex_valid_nstruct_var_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 0>;
    var 1 y = x.value;
    return 1;
  }
`;

val parse_valid_nstruct_var_field =
  check_parse_success $ parse_pancake ex_valid_nstruct_var_field;

val static_valid_nstruct_var_field =
  check_static_success $ static_check_pancake parse_valid_nstruct_var_field;

val warns_valid_nstruct_var_field =
  check_static_no_warnings $ static_check_pancake parse_valid_nstruct_var_field;


val ex_invalid_rstruct_lit_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = <0>.value;
    return 1;
  }
`;

val parse_invalid_rstruct_lit_field =
  check_parse_success $ parse_pancake ex_invalid_rstruct_lit_field;

val static_invalid_rstruct_lit_field =
  check_static_failure $ static_check_pancake parse_invalid_rstruct_lit_field;

val warns_invalid_rstruct_lit_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_rstruct_lit_field;


val ex_invalid_rstruct_var_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var {1} x = <0>;
    var 1 y = x.value;
    return 1;
  }
`;

val parse_invalid_rstruct_var_field =
  check_parse_success $ parse_pancake ex_invalid_rstruct_var_field;

val static_invalid_rstruct_var_field =
  check_static_failure $ static_check_pancake parse_invalid_rstruct_var_field;

val warns_invalid_rstruct_var_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_rstruct_var_field;


val ex_invalid_word_lit_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 0.value;
    return 1;
  }
`;

val parse_invalid_word_lit_field =
  check_parse_success $ parse_pancake ex_invalid_word_lit_field;

val static_invalid_word_lit_field =
  check_static_failure $ static_check_pancake parse_invalid_word_lit_field;

val warns_invalid_word_lit_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_word_lit_field;


val ex_invalid_word_var_field = `
  struct my_struct {
    1 value
  }

  fun 1 f () {
    var 1 x = 0;
    var 1 y = x.value;
    return 1;
  }
`;

val parse_invalid_word_var_field =
  check_parse_success $ parse_pancake ex_invalid_word_var_field;

val static_invalid_word_var_field =
  check_static_failure $ static_check_pancake parse_invalid_word_var_field;

val warns_invalid_word_var_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_word_var_field;


val ex_invalid_nstruct_lit_field = `
  struct my_struct {
    1 value
  }

  struct your_struct {
    1 Value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 1>.Value;
    return 1;
  }
`;

val parse_invalid_nstruct_lit_field =
  check_parse_success $ parse_pancake ex_invalid_nstruct_lit_field;

val static_invalid_nstruct_lit_field =
  check_static_failure $ static_check_pancake parse_invalid_nstruct_lit_field;

val warns_invalid_nstruct_lit_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_nstruct_lit_field;


val ex_invalid_nstruct_var_field = `
  struct my_struct {
    1 value
  }

  struct your_struct {
    1 Value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = 1>;
    var 1 y = x.Value;
    return 1;
  }
`;

val parse_invalid_nstruct_var_field =
  check_parse_success $ parse_pancake ex_invalid_nstruct_var_field;

val static_invalid_nstruct_var_field =
  check_static_failure $ static_check_pancake parse_invalid_nstruct_var_field;

val warns_invalid_nstruct_var_field =
  check_static_no_warnings $ static_check_pancake parse_invalid_nstruct_var_field;


(* Error: Returned shape size >32 words
return size (all in one, split across multiple) *)

val ex_big_rstruct_var = `
  fun 1 f () {
    var 33 x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;
    return 1;
  }
`;

val parse_big_rstruct_var =
  check_parse_success $ parse_pancake ex_big_rstruct_var;

val static_big_rstruct_var =
  check_static_success $ static_check_pancake parse_big_rstruct_var;

val warns_big_rstruct_var =
  check_static_no_warnings $ static_check_pancake parse_big_rstruct_var;


val ex_big_nstruct_var = `
  struct my_struct {
    33 value
  }

  fun 1 f () {
    var my_struct x = my_struct <value = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;
    return 1;
  }
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_big_nstruct_var =
  check_parse_success $ parse_pancake ex_big_nstruct_var;

val static_big_nstruct_var =
  check_static_success $ static_check_pancake parse_big_nstruct_var;

val warns_big_nstruct_var =
  check_static_no_warnings $ static_check_pancake parse_big_nstruct_var;


val ex_big_nstruct_split_var = `
  struct my_struct {
    11 x,
    22 y
  }

  fun 1 f () {
    var my_struct x = my_struct <x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>, y = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;
    return 1;
  }
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_big_nstruct_split_var =
  check_parse_success $ parse_pancake ex_big_nstruct_split_var;

val static_big_nstruct_split_var =
  check_static_success $ static_check_pancake parse_big_nstruct_split_var;

val warns_big_nstruct_split_var =
  check_static_no_warnings $ static_check_pancake parse_big_nstruct_split_var;


val ex_big_rstruct_func_ret = `
  fun 33 f () {
    return <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;
  }
`;

val parse_big_rstruct_func_ret =
  check_parse_success $ parse_pancake ex_big_rstruct_func_ret;

val static_big_rstruct_func_ret =
  check_static_failure $ static_check_pancake parse_big_rstruct_func_ret;

val warns_big_rstruct_func_ret =
  check_static_no_warnings $ static_check_pancake parse_big_rstruct_func_ret;


val ex_big_nstruct_func_ret = `
  struct my_struct {
    33 value
  }

  fun my_struct f () {
    return my_struct <value = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;
  }
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_big_nstruct_func_ret =
  check_parse_success $ parse_pancake ex_big_nstruct_func_ret;

val static_big_nstruct_func_ret =
  check_static_failure $ static_check_pancake parse_big_nstruct_func_ret;

val warns_big_nstruct_func_ret =
  check_static_no_warnings $ static_check_pancake parse_big_nstruct_func_ret;


val ex_big_nstruct_split_func_ret = `
  struct my_struct {
    11 x,
    22 y
  }

  fun my_struct f () {
    return my_struct <x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>, y = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;
  }
`;
(* Note: This example uses whitespace to get around the nested struct/shift operator parsing issue *)

val parse_big_nstruct_split_func_ret =
  check_parse_success $ parse_pancake ex_big_nstruct_split_func_ret;

val static_big_nstruct_split_func_ret =
  check_static_failure $ static_check_pancake parse_big_nstruct_split_func_ret;

val warns_big_nstruct_split_func_ret =
  check_static_no_warnings $ static_check_pancake parse_big_nstruct_split_func_ret;


(* Misc: Default shape behaviour *)

val ex_default_all_good = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_all_good =
  check_parse_success $ parse_pancake ex_default_all_good;

val static_default_all_good =
  check_static_success $ static_check_pancake parse_default_all_good;

val warns_default_all_good =
  check_static_no_warnings $ static_check_pancake parse_default_all_good;


val ex_default_bad_rstruct_local_decl = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = <0>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_local_decl =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_local_decl;

val static_default_bad_rstruct_local_decl =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_local_decl;

val warns_default_bad_rstruct_local_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_local_decl;


val ex_default_bad_rstruct_global_decl = `
  struct my_struct {
    value
  }
  var n = <1>;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_global_decl =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_global_decl;

val static_default_bad_rstruct_global_decl =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_global_decl;

val warns_default_bad_rstruct_global_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_global_decl;


val ex_default_bad_rstruct_local_deccall = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = bar();
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
  fun {1} bar() {
    return <0>;
  }
`;

val parse_default_bad_rstruct_local_deccall =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_local_deccall;

val static_default_bad_rstruct_local_deccall =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_local_deccall;

val warns_default_bad_rstruct_local_deccall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_local_deccall;


val ex_default_bad_rstruct_local_assign = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = <1>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_local_assign =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_local_assign;

val static_default_bad_rstruct_local_assign =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_local_assign;

val warns_default_bad_rstruct_local_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_local_assign;


val ex_default_bad_rstruct_global_assign = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    n = <1>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_global_assign =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_global_assign;

val static_default_bad_rstruct_global_assign =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_global_assign;

val warns_default_bad_rstruct_global_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_global_assign;


val ex_default_bad_rstruct_local_assigncall = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = bar();
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
  fun {1} bar() {
    return <0>;
  }
`;

val parse_default_bad_rstruct_local_assigncall =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_local_assigncall;

val static_default_bad_rstruct_local_assigncall =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_local_assigncall;

val warns_default_bad_rstruct_local_assigncall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_local_assigncall;


val ex_default_bad_rstruct_arg = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = foo(<0>);
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_arg =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_arg;

val static_default_bad_rstruct_arg =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_arg;

val warns_default_bad_rstruct_arg =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_arg;


val ex_default_bad_rstruct_return = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = 2>;
    return <n + a + x>;
  }
`;

val parse_default_bad_rstruct_return =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_return;

val static_default_bad_rstruct_return =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_return;

val warns_default_bad_rstruct_return =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_return;


val ex_default_bad_rstruct_field = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = <2> >;
    return n + a + x;
  }
`;

val parse_default_bad_rstruct_field =
  check_parse_success $ parse_pancake ex_default_bad_rstruct_field;

val static_default_bad_rstruct_field =
  check_static_failure $ static_check_pancake parse_default_bad_rstruct_field;

val warns_default_bad_rstruct_field =
  check_static_no_warnings $ static_check_pancake parse_default_bad_rstruct_field;


val ex_default_bad_nstruct_local_decl = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = my_struct <value = 0>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_local_decl =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_local_decl;

val static_default_bad_nstruct_local_decl =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_local_decl;

val warns_default_bad_nstruct_local_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_local_decl;


val ex_default_bad_nstruct_global_decl = `
  struct my_struct {
    value
  }
  var n = my_struct <value = 1>;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_global_decl =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_global_decl;

val static_default_bad_nstruct_global_decl =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_global_decl;

val warns_default_bad_nstruct_global_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_global_decl;


val ex_default_bad_nstruct_local_deccall = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = bar();
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
  fun my_struct bar() {
    return my_struct <value = 0>;
  }
`;

val parse_default_bad_nstruct_local_deccall =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_local_deccall;

val static_default_bad_nstruct_local_deccall =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_local_deccall;

val warns_default_bad_nstruct_local_deccall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_local_deccall;


val ex_default_bad_nstruct_local_assign = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = my_struct <value = 1>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_local_assign =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_local_assign;

val static_default_bad_nstruct_local_assign =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_local_assign;

val warns_default_bad_nstruct_local_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_local_assign;


val ex_default_bad_nstruct_global_assign = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    n = my_struct <value = 1>;
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_global_assign =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_global_assign;

val static_default_bad_nstruct_global_assign =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_global_assign;

val warns_default_bad_nstruct_global_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_global_assign;


val ex_default_bad_nstruct_local_assigncall = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = bar();
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
  fun my_struct bar() {
    return my_struct <value = 0>;
  }
`;

val parse_default_bad_nstruct_local_assigncall =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_local_assigncall;

val static_default_bad_nstruct_local_assigncall =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_local_assigncall;

val warns_default_bad_nstruct_local_assigncall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_local_assigncall;


val ex_default_bad_nstruct_arg = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = foo(my_struct <value = 0>);
    var my_struct y = my_struct <value = 2>;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_arg =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_arg;

val static_default_bad_nstruct_arg =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_arg;

val warns_default_bad_nstruct_arg =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_arg;


val ex_default_bad_nstruct_return = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = 2>;
    return my_struct <value = n + a + x>;
  }
`;

val parse_default_bad_nstruct_return =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_return;

val static_default_bad_nstruct_return =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_return;

val warns_default_bad_nstruct_return =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_return;


val ex_default_bad_nstruct_field = `
  struct my_struct {
    value
  }
  var n = 1;
  fun foo(a) {
    var x = 0;
    var my_struct y = my_struct <value = my_struct <value = 2> >;
    return n + a + x;
  }
`;

val parse_default_bad_nstruct_field =
  check_parse_success $ parse_pancake ex_default_bad_nstruct_field;

val static_default_bad_nstruct_field =
  check_static_failure $ static_check_pancake parse_default_bad_nstruct_field;

val warns_default_bad_nstruct_field =
  check_static_no_warnings $ static_check_pancake parse_default_bad_nstruct_field;
