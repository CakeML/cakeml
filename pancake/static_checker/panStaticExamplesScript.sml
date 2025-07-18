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

(* Add LIST_REL/EVERY2 to the compset *)
val _ = computeLib.add_thms [LIST_REL_def] the_compset;


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


(* Error: Function parameter names not distinct *)

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

val ex_undefined_fun = `
  fun 1 f () {
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


val ex_local_decl_word_mismatch = `
  fun 1 f () {
    var 1 x = <1>;
    return 1;
  }
`;

val parse_local_decl_word_mismatch =
  check_parse_success $ parse_pancake ex_local_decl_word_mismatch;

val static_local_decl_word_mismatch =
  check_static_failure $ static_check_pancake parse_local_decl_word_mismatch;

val warns_local_decl_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_local_decl_word_mismatch;


val ex_local_decl_struct_match = `
  fun 1 f () {
    var {1} x = <1>;
    return 1;
  }
`;

val parse_local_decl_struct_match =
  check_parse_success $ parse_pancake ex_local_decl_struct_match;

val static_local_decl_struct_match =
  check_static_success $ static_check_pancake parse_local_decl_struct_match;

val warns_local_decl_struct_match =
  check_static_no_warnings $ static_check_pancake parse_local_decl_struct_match;


val ex_local_decl_struct_mismatch_1 = `
  fun 1 f () {
    var {1} x = 1;
    return 1;
  }
`;

val parse_local_decl_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_decl_struct_mismatch_1;

val static_local_decl_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_decl_struct_mismatch_1;

val warns_local_decl_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_struct_mismatch_1;


val ex_local_decl_struct_mismatch_2 = `
  fun 1 f () {
    var {1} x = <1, 1>;
    return 1;
  }
`;

val parse_local_decl_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_decl_struct_mismatch_2;

val static_local_decl_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_decl_struct_mismatch_2;

val warns_local_decl_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_decl_struct_mismatch_2;


val ex_global_decl_word_match = `
  var 1 x = 1;
`;

val parse_global_decl_word_match =
  check_parse_success $ parse_pancake ex_global_decl_word_match;

val static_global_decl_word_match =
  check_static_success $ static_check_pancake parse_global_decl_word_match;

val warns_global_decl_word_match =
  check_static_no_warnings $ static_check_pancake parse_global_decl_word_match;


val ex_global_decl_word_mismatch = `
  var 1 x = <1>;
`;

val parse_global_decl_word_mismatch =
  check_parse_success $ parse_pancake ex_global_decl_word_mismatch;

val static_global_decl_word_mismatch =
  check_static_failure $ static_check_pancake parse_global_decl_word_mismatch;

val warns_global_decl_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_global_decl_word_mismatch;


val ex_global_decl_struct_match = `
  var {1} x = <1>;
`;

val parse_global_decl_struct_match =
  check_parse_success $ parse_pancake ex_global_decl_struct_match;

val static_global_decl_struct_match =
  check_static_success $ static_check_pancake parse_global_decl_struct_match;

val warns_global_decl_struct_match =
  check_static_no_warnings $ static_check_pancake parse_global_decl_struct_match;


val ex_global_decl_struct_mismatch_1 = `
  var {1} x = 1;
`;

val parse_global_decl_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_global_decl_struct_mismatch_1;

val static_global_decl_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_global_decl_struct_mismatch_1;

val warns_global_decl_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_struct_mismatch_1;


val ex_global_decl_struct_mismatch_2 = `
  var {1} x = <1, 1>;
`;

val parse_global_decl_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_global_decl_struct_mismatch_2;

val static_global_decl_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_global_decl_struct_mismatch_2;

val warns_global_decl_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_global_decl_struct_mismatch_2;


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


val ex_local_asgn_word_mismatch = `
  fun 1 f () {
    var 1 x = 0;
    x = <1>;
    return 1;
  }
`;

val parse_local_asgn_word_mismatch =
  check_parse_success $ parse_pancake ex_local_asgn_word_mismatch;

val static_local_asgn_word_mismatch =
  check_static_failure $ static_check_pancake parse_local_asgn_word_mismatch;

val warns_local_asgn_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_word_mismatch;


val ex_local_asgn_struct_match = `
  fun 1 f () {
    var {1} x = <0>;
    x = <1>;
    return 1;
  }
`;

val parse_local_asgn_struct_match =
  check_parse_success $ parse_pancake ex_local_asgn_struct_match;

val static_local_asgn_struct_match =
  check_static_success $ static_check_pancake parse_local_asgn_struct_match;

val warns_local_asgn_struct_match =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_struct_match;


val ex_local_asgn_struct_mismatch_1 = `
  fun 1 f () {
    var {1} x = <0>;
    x = 1;
    return 1;
  }
`;

val parse_local_asgn_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_asgn_struct_mismatch_1;

val static_local_asgn_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_asgn_struct_mismatch_1;

val warns_local_asgn_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_struct_mismatch_1;


val ex_local_asgn_struct_mismatch_2 = `
  fun 1 f () {
    var {1} x = <0>;
    x = <1, 1>;
    return 1;
  }
`;

val parse_local_asgn_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_asgn_struct_mismatch_2;

val static_local_asgn_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_asgn_struct_mismatch_2;

val warns_local_asgn_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_asgn_struct_mismatch_2;


(* Error: Mismatched function arguments *)

val ex_func_arg_word_match = `
  fun 1 f () {
    g(1);
    return 1;
  }
  fun 1 g (1 a) {
    return 1;
  }
`;

val parse_func_arg_word_match =
  check_parse_success $ parse_pancake ex_func_arg_word_match;

val static_func_arg_word_match =
  check_static_success $ static_check_pancake parse_func_arg_word_match;

val warns_func_arg_word_match =
  check_static_no_warnings $ static_check_pancake parse_func_arg_word_match;


val ex_func_arg_word_mismatch = `
  fun 1 f () {
    g(<1>);
    return 1;
  }
  fun 1 g (1 a) {
    return 1;
  }
`;

val parse_func_arg_word_mismatch =
  check_parse_success $ parse_pancake ex_func_arg_word_mismatch;

val static_func_arg_word_mismatch =
  check_static_failure $ static_check_pancake parse_func_arg_word_mismatch;

val warns_func_arg_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_func_arg_word_mismatch;


val ex_func_arg_struct_match = `
  fun 1 f () {
    g(<1>);
    return 1;
  }
  fun 1 g ({1} a) {
    return 1;
  }
`;

val parse_func_arg_struct_match =
  check_parse_success $ parse_pancake ex_func_arg_struct_match;

val static_func_arg_struct_match =
  check_static_success $ static_check_pancake parse_func_arg_struct_match;

val warns_func_arg_struct_match =
  check_static_no_warnings $ static_check_pancake parse_func_arg_struct_match;


val ex_func_arg_struct_mismatch_1 = `
  fun 1 f () {
    g(1);
    return 1;
  }
  fun 1 g ({1} a) {
    return 1;
  }
`;

val parse_func_arg_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_arg_struct_mismatch_1;

val static_func_arg_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_arg_struct_mismatch_1;

val warns_func_arg_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_struct_mismatch_1;


val ex_func_arg_struct_mismatch_2 = `
  fun 1 f () {
    g(<1, 1>);
    return 1;
  }
  fun 1 g ({1} a) {
    return 1;
  }
`;

val parse_func_arg_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_arg_struct_mismatch_2;

val static_func_arg_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_arg_struct_mismatch_2;

val warns_func_arg_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_arg_struct_mismatch_2;


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


val ex_func_ret_word_mismatch = `
  fun 1 f () {
    return <1>;
  }
`;

val parse_func_ret_word_mismatch =
  check_parse_success $ parse_pancake ex_func_ret_word_mismatch;

val static_func_ret_word_mismatch =
  check_static_failure $ static_check_pancake parse_func_ret_word_mismatch;

val warns_func_ret_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_func_ret_word_mismatch;


val ex_func_ret_struct_match = `
  fun {1} f () {
    return <1>;
  }
`;

val parse_func_ret_struct_match =
  check_parse_success $ parse_pancake ex_func_ret_struct_match;

val static_func_ret_struct_match =
  check_static_success $ static_check_pancake parse_func_ret_struct_match;

val warns_func_ret_struct_match =
  check_static_no_warnings $ static_check_pancake parse_func_ret_struct_match;


val ex_func_ret_struct_mismatch_1 = `
  fun {1} f () {
    return 1;
  }
`;

val parse_func_ret_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_func_ret_struct_mismatch_1;

val static_func_ret_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_func_ret_struct_mismatch_1;

val warns_func_ret_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_struct_mismatch_1;


val ex_func_ret_struct_mismatch_2 = `
  fun {1} f () {
    return <1, 1>;
  }
`;

val parse_func_ret_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_func_ret_struct_mismatch_2;

val static_func_ret_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_func_ret_struct_mismatch_2;

val warns_func_ret_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_func_ret_struct_mismatch_2;


(* Error: Non-word main function return declarations *)

val ex_main_struct_ret = `
  fun {1} main () {
    return <1>;
  }
`;

val parse_main_struct_ret =
  check_parse_success $ parse_pancake ex_main_struct_ret;

val static_main_struct_ret =
  check_static_failure $ static_check_pancake parse_main_struct_ret;

val warns_main_struct_ret =
  check_static_no_warnings $ static_check_pancake parse_main_struct_ret;


(* Error: Non-word FFI arguments *)

val ex_ffi_struct_lit_arg = `
  fun 1 f () {
    @g(1, 2, 3, <4>);
    return 1;
  }
`;

val parse_ffi_struct_lit_arg =
  check_parse_success $ parse_pancake ex_ffi_struct_lit_arg;

val static_ffi_struct_lit_arg =
  check_static_failure $ static_check_pancake parse_ffi_struct_lit_arg;

val warns_ffi_struct_lit_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_struct_lit_arg;


val ex_ffi_struct_var_arg = `
  fun 1 f () {
    var {1} x = <0>;
    @g(1, x, 3, 4);
    return 1;
  }
`;

val parse_ffi_struct_var_arg =
  check_parse_success $ parse_pancake ex_ffi_struct_var_arg;

val static_ffi_struct_var_arg =
  check_static_failure $ static_check_pancake parse_ffi_struct_var_arg;

val warns_ffi_struct_var_arg =
  check_static_no_warnings $ static_check_pancake parse_ffi_struct_var_arg;


(* Error: Non-word exported argument declarations *)

val ex_export_struct_arg = `
  export fun 1 f ({1} a) {
    return 1;
  }
`;

val parse_export_struct_arg =
  check_parse_success $ parse_pancake ex_export_struct_arg;

val static_export_struct_arg =
  check_static_failure $ static_check_pancake parse_export_struct_arg;

val warns_export_struct_arg =
  check_static_no_warnings $ static_check_pancake parse_export_struct_arg;


(* Error: Non-word exported return declarations *)

val ex_export_struct_ret = `
  export fun {1} f () {
    return <1>;
  }
`;

val parse_export_struct_ret =
  check_parse_success $ parse_pancake ex_export_struct_ret;

val static_export_struct_ret =
  check_static_failure $ static_check_pancake parse_export_struct_ret;

val warns_export_struct_ret =
  check_static_no_warnings $ static_check_pancake parse_export_struct_ret;


(* Error: Invalid field index *)

val ex_valid_struct_lit_index = `
  fun 1 f () {
    var 1 x = <0>.0;
    return 1;
  }
`;

val parse_valid_struct_lit_index =
  check_parse_success $ parse_pancake ex_valid_struct_lit_index;

val static_valid_struct_lit_index =
  check_static_success $ static_check_pancake parse_valid_struct_lit_index;

val warns_valid_struct_lit_index =
  check_static_no_warnings $ static_check_pancake parse_valid_struct_lit_index;


val ex_valid_struct_var_index = `
  fun 1 f () {
    var {1} x = <0>;
    var 1 y = x.0;
    return 1;
  }
`;

val parse_valid_struct_var_index =
  check_parse_success $ parse_pancake ex_valid_struct_var_index;

val static_valid_struct_var_index =
  check_static_success $ static_check_pancake parse_valid_struct_var_index;

val warns_valid_struct_var_index =
  check_static_no_warnings $ static_check_pancake parse_valid_struct_var_index;


val ex_invalid_struct_lit_index = `
  fun 1 f () {
    var 1 x = <0>.5;
    return 1;
  }
`;

val parse_invalid_struct_lit_index =
  check_parse_success $ parse_pancake ex_invalid_struct_lit_index;

val static_invalid_struct_lit_index =
  check_static_failure $ static_check_pancake parse_invalid_struct_lit_index;

val warns_invalid_struct_lit_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_struct_lit_index;


val ex_invalid_struct_var_index = `
  fun 1 f () {
    var {1} x = <0>;
    var 1 y = x.5;
    return 1;
  }
`;

val parse_invalid_struct_var_index =
  check_parse_success $ parse_pancake ex_invalid_struct_var_index;

val static_invalid_struct_var_index =
  check_static_failure $ static_check_pancake parse_invalid_struct_var_index;

val warns_invalid_struct_var_index =
  check_static_no_warnings $ static_check_pancake parse_invalid_struct_var_index;


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


(* Error: Non-word addresses for memory operations *)

val ex_local_load_struct_addr = `
  fun 1 f () {
    var 1 x = lds 1 <1>;
    return 1;
  }
`;

val parse_local_load_struct_addr =
  check_parse_success $ parse_pancake ex_local_load_struct_addr;

val static_local_load_struct_addr =
  check_static_failure $ static_check_pancake parse_local_load_struct_addr;

val warns_local_load_struct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_load_struct_addr;


val ex_local_store_struct_addr = `
  fun 1 f () {
    var 1 x = 1;
    st <1>, x;
    return 1;
  }
`;

val parse_local_store_struct_addr =
  check_parse_success $ parse_pancake ex_local_store_struct_addr;

val static_local_store_struct_addr =
  check_static_failure $ static_check_pancake parse_local_store_struct_addr;

val warns_local_store_struct_addr =
  check_static_no_warnings $ static_check_pancake parse_local_store_struct_addr;


val ex_shared_load_struct_addr = `
  fun 1 f () {
    var 1 x = 1;
    !ldw x, <1>;
    return 1;
  }
`;

val parse_shared_load_struct_addr =
  check_parse_success $ parse_pancake ex_shared_load_struct_addr;

val static_shared_load_struct_addr =
  check_static_failure $ static_check_pancake parse_shared_load_struct_addr;

val warns_shared_load_struct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_load_struct_addr;


val ex_shared_store_struct_addr = `
  fun 1 f () {
    var 1 x = 1;
    !stw <1>, x;
    return 1;
  }
`;

val parse_shared_store_struct_addr =
  check_parse_success $ parse_pancake ex_shared_store_struct_addr;

val static_shared_store_struct_addr =
  check_static_failure $ static_check_pancake parse_shared_store_struct_addr;

val warns_shared_store_struct_addr =
  check_static_no_warnings $ static_check_pancake parse_shared_store_struct_addr;


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


val ex_local_lds_word_mismatch = `
  fun 1 f () {
    var {1} x = lds 1 @base;
    return 1;
  }
`;

val parse_local_lds_word_mismatch =
  check_parse_success $ parse_pancake ex_local_lds_word_mismatch;

val static_local_lds_word_mismatch =
  check_static_failure $ static_check_pancake parse_local_lds_word_mismatch;

val warns_local_lds_word_mismatch =
  check_static_no_warnings $ static_check_pancake parse_local_lds_word_mismatch;


val ex_local_lds_struct_match = `
  fun 1 f () {
    var {1} x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_struct_match =
  check_parse_success $ parse_pancake ex_local_lds_struct_match;

val static_local_lds_struct_match =
  check_static_success $ static_check_pancake parse_local_lds_struct_match;

val warns_local_lds_struct_match =
  check_static_no_warnings $ static_check_pancake parse_local_lds_struct_match;


val ex_local_lds_struct_mismatch_1 = `
  fun 1 f () {
    var 1 x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_struct_mismatch_1 =
  check_parse_success $ parse_pancake ex_local_lds_struct_mismatch_1;

val static_local_lds_struct_mismatch_1 =
  check_static_failure $ static_check_pancake parse_local_lds_struct_mismatch_1;

val warns_local_lds_struct_mismatch_1 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_struct_mismatch_1;


val ex_local_lds_struct_mismatch_2 = `
  fun 1 f () {
    var 2 x = lds {1} @base;
    return 1;
  }
`;

val parse_local_lds_struct_mismatch_2 =
  check_parse_success $ parse_pancake ex_local_lds_struct_mismatch_2;

val static_local_lds_struct_mismatch_2 =
  check_static_failure $ static_check_pancake parse_local_lds_struct_mismatch_2;

val warns_local_lds_struct_mismatch_2 =
  check_static_no_warnings $ static_check_pancake parse_local_lds_struct_mismatch_2;


val ex_local_ld8_struct_dest = `
  fun 1 f () {
    var {1} x = ld8 @base;
    return 1;
  }
`;

val parse_local_ld8_struct_dest =
  check_parse_success $ parse_pancake ex_local_ld8_struct_dest;

val static_local_ld8_struct_dest =
  check_static_failure $ static_check_pancake parse_local_ld8_struct_dest;

val warns_local_ld8_struct_dest =
  check_static_no_warnings $ static_check_pancake parse_local_ld8_struct_dest;


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


val ex_shared_ldw_struct_dest = `
  fun 1 f () {
    var {1} x = <1>;
    !ldw x, 0;
    return 1;
  }
`;

val parse_shared_ldw_struct_dest =
  check_parse_success $ parse_pancake ex_shared_ldw_struct_dest;

val static_shared_ldw_struct_dest =
  check_static_failure $ static_check_pancake parse_shared_ldw_struct_dest;

val warns_shared_ldw_struct_dest =
  check_static_no_warnings $ static_check_pancake parse_shared_ldw_struct_dest;


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


val ex_shared_stw_struct_src = `
  fun 1 f () {
    var {1} x = <1>;
    !stw 0, x;
    return 1;
  }
`;

val parse_shared_stw_struct_src =
  check_parse_success $ parse_pancake ex_shared_stw_struct_src;

val static_shared_stw_struct_src =
  check_static_failure $ static_check_pancake parse_shared_stw_struct_src;

val warns_shared_stw_struct_src =
  check_static_no_warnings $ static_check_pancake parse_shared_stw_struct_src;


(* Error: Non-word/mismatched operator operands *)

val ex_add_one_struct_operand = `
  fun 1 f () {
    return 1 + <2>;
  }
`;

val parse_add_one_struct_operand =
  check_parse_success $ parse_pancake ex_add_one_struct_operand;

val static_add_one_struct_operand =
  check_static_failure $ static_check_pancake parse_add_one_struct_operand;

val warns_add_one_struct_operand =
  check_static_no_warnings $ static_check_pancake parse_add_one_struct_operand;


val ex_add_all_struct_operands = `
  fun 1 f () {
    return <1> + <2, 3>;
  }
`;

val parse_add_all_struct_operands =
  check_parse_success $ parse_pancake ex_add_all_struct_operands;

val static_add_all_struct_operands =
  check_static_failure $ static_check_pancake parse_add_all_struct_operands;

val warns_add_all_struct_operands =
  check_static_no_warnings $ static_check_pancake parse_add_all_struct_operands;


val ex_mult_one_struct_operand = `
  fun 1 f () {
    return 1 * <2>;
  }
`;

val parse_mult_one_struct_operand =
  check_parse_success $ parse_pancake ex_mult_one_struct_operand;

val static_mult_one_struct_operand =
  check_static_failure $ static_check_pancake parse_mult_one_struct_operand;

val warns_mult_one_struct_operand =
  check_static_no_warnings $ static_check_pancake parse_mult_one_struct_operand;


val ex_mult_all_struct_operands = `
  fun 1 f () {
    return <1> * <2, 3>;
  }
`;

val parse_mult_all_struct_operands =
  check_parse_success $ parse_pancake ex_mult_all_struct_operands;

val static_mult_all_struct_operands =
  check_static_failure $ static_check_pancake parse_mult_all_struct_operands;

val warns_mult_all_struct_operands =
  check_static_no_warnings $ static_check_pancake parse_mult_all_struct_operands;


val ex_shift_struct_operand = `
  fun 1 f () {
    return <1> << 2;
  }
`;

val parse_shift_struct_operand =
  check_parse_success $ parse_pancake ex_shift_struct_operand;

val static_shift_struct_operand =
  check_static_failure $ static_check_pancake parse_shift_struct_operand;

val warns_shift_struct_operand =
  check_static_no_warnings $ static_check_pancake parse_shift_struct_operand;


val ex_cmp_word_struct_operands = `
  fun 1 f () {
    return 0 == <1>;
  }
`;

val parse_cmp_word_struct_operands =
  check_parse_success $ parse_pancake ex_cmp_word_struct_operands;

val static_cmp_word_struct_operands =
  check_static_failure $ static_check_pancake parse_cmp_word_struct_operands;

val warns_cmp_word_struct_operands =
  check_static_no_warnings $ static_check_pancake parse_cmp_word_struct_operands;


(* Error: Non-word condition expressions *)

val ex_if_cond_struct = `
  fun 1 f () {
    if <1> {
      skip;
    }
    return 1;
  }
`;

val parse_if_cond_struct =
  check_parse_success $ parse_pancake ex_if_cond_struct;

val static_if_cond_struct =
  check_static_failure $ static_check_pancake parse_if_cond_struct;

val warns_if_cond_struct =
  check_static_no_warnings $ static_check_pancake parse_if_cond_struct;


val ex_while_cond_struct = `
  fun 1 f () {
    while <1> {
      skip;
    }
    return 1;
  }
`;

val parse_while_cond_struct =
  check_parse_success $ parse_pancake ex_while_cond_struct;

val static_while_cond_struct =
  check_static_failure $ static_check_pancake parse_while_cond_struct;

val warns_while_cond_struct =
  check_static_no_warnings $ static_check_pancake parse_while_cond_struct;


(* Error: Returned shape size >32 words *)

val ex_big_var = `
  fun 1 f () {
    var 33 x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;
    return 1;
  }
`;

val parse_big_var =
  check_parse_success $ parse_pancake ex_big_var;

val static_big_var =
  check_static_success $ static_check_pancake parse_big_var;

val warns_big_var =
  check_static_no_warnings $ static_check_pancake parse_big_var;


val ex_big_func_ret = `
  fun 33 f () {
    return <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;
  }
`;

val parse_big_func_ret =
  check_parse_success $ parse_pancake ex_big_func_ret;

val static_big_func_ret =
  check_static_failure $ static_check_pancake parse_big_func_ret;

val warns_big_func_ret =
  check_static_no_warnings $ static_check_pancake parse_big_func_ret;


(* Misc: Default shape behaviour *)

val ex_default_all_good = `
  var n = 1;
  fun foo(a) {
    var x = 0;
    return n + a + x;
  }
`;

val parse_default_all_good =
  check_parse_success $ parse_pancake ex_default_all_good;

val static_default_all_good =
  check_static_success $ static_check_pancake parse_default_all_good;

val warns_default_all_good =
  check_static_no_warnings $ static_check_pancake parse_default_all_good;


val ex_default_bad_local_decl = `
  var n = 1;
  fun foo(a) {
    var x = <0>;
    return n + a + x;
  }
`;

val parse_default_bad_local_decl =
  check_parse_success $ parse_pancake ex_default_bad_local_decl;

val static_default_bad_local_decl =
  check_static_failure $ static_check_pancake parse_default_bad_local_decl;

val warns_default_bad_local_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_local_decl;


val ex_default_bad_global_decl = `
  var n = <1>;
  fun foo(a) {
    var x = 0;
    return n + a + x;
  }
`;

val parse_default_bad_global_decl =
  check_parse_success $ parse_pancake ex_default_bad_global_decl;

val static_default_bad_global_decl =
  check_static_failure $ static_check_pancake parse_default_bad_global_decl;

val warns_default_bad_global_decl =
  check_static_no_warnings $ static_check_pancake parse_default_bad_global_decl;


val ex_default_bad_local_deccall = `
  var n = 1;
  fun foo(a) {
    var x = bar();
    return n + a + x;
  }
  fun {1} bar() {
    return <0>;
  }
`;

val parse_default_bad_local_deccall =
  check_parse_success $ parse_pancake ex_default_bad_local_deccall;

val static_default_bad_local_deccall =
  check_static_failure $ static_check_pancake parse_default_bad_local_deccall;

val warns_default_bad_local_deccall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_local_deccall;


val ex_default_bad_local_assign = `
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = <1>;
    return n + a + x;
  }
`;

val parse_default_bad_local_assign =
  check_parse_success $ parse_pancake ex_default_bad_local_assign;

val static_default_bad_local_assign =
  check_static_failure $ static_check_pancake parse_default_bad_local_assign;

val warns_default_bad_local_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_local_assign;


val ex_default_bad_global_assign = `
  var n = 1;
  fun foo(a) {
    var x = 0;
    n = <1>;
    return n + a + x;
  }
`;

val parse_default_bad_global_assign =
  check_parse_success $ parse_pancake ex_default_bad_global_assign;

val static_default_bad_global_assign =
  check_static_failure $ static_check_pancake parse_default_bad_global_assign;

val warns_default_bad_global_assign =
  check_static_no_warnings $ static_check_pancake parse_default_bad_global_assign;


val ex_default_bad_local_assigncall = `
  var n = 1;
  fun foo(a) {
    var x = 0;
    x = bar();
    return n + a + x;
  }
  fun {1} bar() {
    return <0>;
  }
`;

val parse_default_bad_local_assigncall =
  check_parse_success $ parse_pancake ex_default_bad_local_assigncall;

val static_default_bad_local_assigncall =
  check_static_failure $ static_check_pancake parse_default_bad_local_assigncall;

val warns_default_bad_local_assigncall =
  check_static_no_warnings $ static_check_pancake parse_default_bad_local_assigncall;


val ex_default_bad_arg = `
  var n = 1;
  fun foo(a) {
    var x = foo(<0>);
    return n + a + x;
  }
`;

val parse_default_bad_arg =
  check_parse_success $ parse_pancake ex_default_bad_arg;

val static_default_bad_arg =
  check_static_failure $ static_check_pancake parse_default_bad_arg;

val warns_default_bad_arg =
  check_static_no_warnings $ static_check_pancake parse_default_bad_arg;


val ex_default_bad_return = `
  var n = 1;
  fun foo(a) {
    var x = 0;
    return <n + a + x>;
  }
`;

val parse_default_bad_return =
  check_parse_success $ parse_pancake ex_default_bad_return;

val static_default_bad_return =
  check_static_failure $ static_check_pancake parse_default_bad_return;

val warns_default_bad_return =
  check_static_no_warnings $ static_check_pancake parse_default_bad_return;


