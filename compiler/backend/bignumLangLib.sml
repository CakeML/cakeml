(*
  Implements a basic parser for bignumLang.
*)

(* Mostly generated using Claude Opus 4.6 with minor adjustments / additions. *)

structure bignumLangLib :> sig

  datatype binop = Add | Sub | And | Or | Xor
  datatype cmp = Equal | Lower | Less | Test
               | NotEqual | NotLower | NotLess | NotTest
  datatype shift = Lsl | Lsr | Asr | Ror

  datatype exp = Const of IntInf.int
               | Var of string
               | Load of exp
               | Op of binop * exp list
               | Shift of shift * exp * exp

  datatype cmp_arg = cVar of string | cConst of IntInf.int

  datatype stmt = Skip
                | Seq of stmt * stmt
                | If of cmp * string * cmp_arg * stmt * stmt
                | While of cmp * string * cmp_arg * stmt
                | Dec of string * exp * stmt
                | Assign of string * exp
                | Move of (string * string) list
                | Store of exp * string
                | Return of string list
                | Call of string list option * string * exp list

  type func
  type prog

  exception ParseError of string

  val parse : string -> prog

  val binop_to_term   : binop -> Term.term
  val cmp_to_term     : cmp -> Term.term
  val shift_to_term   : shift -> Term.term
  val exp_to_term     : exp -> Term.term
  val cmp_arg_to_term : cmp_arg -> Term.term
  val stmt_to_term    : stmt -> Term.term
  val func_to_term    : func -> Term.term
  val prog_to_term    : prog -> Term.term

  val bignum          : 'a frag list -> Term.term

end = struct

  (* --- AST types --- *)

  datatype binop = Add | Sub | And | Or | Xor
  datatype cmp = Equal | Lower | Less | Test
               | NotEqual | NotLower | NotLess | NotTest
  datatype shift = Lsl | Lsr | Asr | Ror

  datatype exp = Const of IntInf.int
               | Var of string
               | Load of exp
               | Op of binop * exp list
               | Shift of shift * exp * exp

  datatype cmp_arg = cVar of string | cConst of IntInf.int

  datatype stmt = Skip
                | Seq of stmt * stmt
                | If of cmp * string * cmp_arg * stmt * stmt
                | While of cmp * string * cmp_arg * stmt
                | Dec of string * exp * stmt
                | Assign of string * exp
                | Move of (string * string) list
                | Store of exp * string
                | Return of string list
                | Call of string list option * string * exp list

  type func = string * string list * stmt
  type prog = func list

  exception ParseError of string

  (* --- Lexer --- *)

  datatype token =
      LPAR | RPAR | LBRACE | RBRACE | SEMI | COMMA | ASSIGN
    | STAR
    | EQEQ | BANGEQ | LT | GEQ | LTU | GEQU | AMPTEST | AMPNTEST
    | PLUS | MINUS | AMP | PIPE | CARET
    | LSHIFT | RSHIFT | ARSHIFT
    | TOK_IF | TOK_ELSE | TOK_WHILE | TOK_RETURN | TOK_VAR
    | TOK_MOVE | LARROW | TOK_ROR
    | INT of IntInf.int
    | IDENT of string
    | EOF

  type positioned = token * int * int

  fun err (l, c) msg =
    raise ParseError ("Parse error at (" ^ Int.toString l ^ ", " ^
                       Int.toString c ^ "): " ^ msg)

  fun is_alpha c = Char.isAlpha c orelse c = #"_"
  fun is_alnum c = Char.isAlphaNum c orelse c = #"_"
  fun is_digit c = Char.isDigit c

  fun collect_while p [] = ([], [])
    | collect_while p (cs as c :: rest) =
        if p c then
          let val (w, cs') = collect_while p rest
          in (c :: w, cs') end
        else ([], cs)

  fun scan_hex s =
    valOf (StringCvt.scanString (IntInf.scan StringCvt.HEX) s)

  fun parse_int_literal (cs, line, col) =
    case cs of
      #"0" :: #"x" :: rest =>
        let val (digits, rest') = collect_while Char.isHexDigit rest
        in if null digits then err (line, col) "expected hex digits after 0x"
           else (scan_hex (implode digits),
                 rest', col + 2 + length digits)
        end
    | #"0" :: #"X" :: rest =>
        let val (digits, rest') = collect_while Char.isHexDigit rest
        in if null digits then err (line, col) "expected hex digits after 0X"
           else (scan_hex (implode digits),
                 rest', col + 2 + length digits)
        end
    | #"0" :: #"b" :: rest =>
        let val (digits, rest') = collect_while (fn c => c = #"0" orelse c = #"1") rest
            val _ = if null digits then err (line, col) "expected binary digits after 0b" else ()
            fun bin_val [] = 0 : IntInf.int
              | bin_val (d :: ds) =
                  (if d = #"1" then 1 else 0) + 2 * bin_val ds
        in (bin_val (rev digits), rest', col + 2 + length digits)
        end
    | #"0" :: #"B" :: rest =>
        let val (digits, rest') = collect_while (fn c => c = #"0" orelse c = #"1") rest
            val _ = if null digits then err (line, col) "expected binary digits after 0B" else ()
            fun bin_val [] = 0 : IntInf.int
              | bin_val (d :: ds) =
                  (if d = #"1" then 1 else 0) + 2 * bin_val ds
        in (bin_val (rev digits), rest', col + 2 + length digits)
        end
    | _ =>
        let val (digits, rest') = collect_while is_digit cs
        in (valOf (IntInf.fromString (implode digits)),
            rest', col + length digits)
        end

  fun keyword_or_ident s =
    case s of
      "if" => TOK_IF | "else" => TOK_ELSE | "while" => TOK_WHILE
    | "return" => TOK_RETURN | "var" => TOK_VAR | "move" => TOK_MOVE
    | "ror" => TOK_ROR
    | _ => IDENT s

  (* Skip whitespace and comments, return (remaining chars, line, col) *)
  fun skip_ws_comments [] line col = ([], line, col)
    | skip_ws_comments (#"\n" :: cs) line col =
        skip_ws_comments cs (line + 1) 1
    | skip_ws_comments (c :: cs) line col =
        if Char.isSpace c then skip_ws_comments cs line (col + 1)
        else if c = #"/" then
          case cs of
            #"/" :: rest =>
              (* line comment: skip to end of line *)
              let fun skip_line [] l c = ([], l, c)
                    | skip_line (#"\n" :: r) l _ = skip_ws_comments r (l+1) 1
                    | skip_line (_ :: r) l c = skip_line r l (c+1)
              in skip_line rest line (col+2) end
          | #"*" :: rest =>
              (* block comment: skip to */ *)
              let fun skip_block [] l c = err (l, c) "unterminated block comment"
                    | skip_block (#"*" :: #"/" :: r) l c =
                        skip_ws_comments r l (c+2)
                    | skip_block (#"\n" :: r) l _ =
                        skip_block r (l+1) 1
                    | skip_block (_ :: r) l c = skip_block r l (c+1)
              in skip_block rest line (col+2) end
          | _ => (#"/" :: cs, line, col)
        else (c :: cs, line, col)

  fun tokenize_all input =
    let
      val chars = explode input
      (* Check for (*#loc L C*) pragma at the start *)
      fun skip_initial_ws [] = []
        | skip_initial_ws (cs as c :: rest) =
            if Char.isSpace c then skip_initial_ws rest else cs
      val trimmed = skip_initial_ws chars
      val (chars0, base_line, base_col) =
        case trimmed of
          #"(" :: #"*" :: #"#" :: #"l" :: #"o" :: #"c" :: rest =>
            let
              (* skip spaces *)
              val rest1 = skip_initial_ws rest
              (* read line number *)
              val (ld, rest2) = collect_while is_digit rest1
              val _ = if null ld then err (1,1) "bad #loc pragma" else ()
              val loc_line = valOf (Int.fromString (implode ld))
              val rest3 = skip_initial_ws rest2
              (* read col number *)
              val (cd, rest4) = collect_while is_digit rest3
              val _ = if null cd then err (1,1) "bad #loc pragma" else ()
              val loc_col = valOf (Int.fromString (implode cd))
              val rest5 = skip_initial_ws rest4
              (* expect closing star-paren *)
              val rest6 = case rest5 of
                            #"*" :: #")" :: r => r
                          | _ => err (1,1) "bad #loc pragma: expected *)"
            in (rest6, loc_line, loc_col) end
        | _ => (chars, 1, 1)

      fun lex cs line col acc =
        let val (cs, line, col) = skip_ws_comments cs line col
        in
          case cs of
            [] => rev ((EOF, line, col) :: acc)
          | #"(" :: rest => lex rest line (col+1) ((LPAR, line, col) :: acc)
          | #")" :: rest => lex rest line (col+1) ((RPAR, line, col) :: acc)
          | #"{" :: rest => lex rest line (col+1) ((LBRACE, line, col) :: acc)
          | #"}" :: rest => lex rest line (col+1) ((RBRACE, line, col) :: acc)
          | #";" :: rest => lex rest line (col+1) ((SEMI, line, col) :: acc)
          | #"," :: rest => lex rest line (col+1) ((COMMA, line, col) :: acc)
          | #"+" :: rest => lex rest line (col+1) ((PLUS, line, col) :: acc)
          | #"-" :: rest => lex rest line (col+1) ((MINUS, line, col) :: acc)
          | #"|" :: rest => lex rest line (col+1) ((PIPE, line, col) :: acc)
          | #"^" :: rest => lex rest line (col+1) ((CARET, line, col) :: acc)
          | #"*" :: rest => lex rest line (col+1) ((STAR, line, col) :: acc)
          | #"=" :: #"=" :: rest =>
              lex rest line (col+2) ((EQEQ, line, col) :: acc)
          | #"=" :: rest =>
              lex rest line (col+1) ((ASSIGN, line, col) :: acc)
          | #"!" :: #"=" :: rest =>
              lex rest line (col+2) ((BANGEQ, line, col) :: acc)
          | #"<" :: #"<" :: rest =>
              lex rest line (col+2) ((LSHIFT, line, col) :: acc)
          | #"<" :: #"-" :: rest =>
              lex rest line (col+2) ((LARROW, line, col) :: acc)
          | #"<" :: #"u" :: rest =>
              lex rest line (col+2) ((LTU, line, col) :: acc)
          | #"<" :: rest =>
              lex rest line (col+1) ((LT, line, col) :: acc)
          | #">" :: #">" :: #">" :: rest =>
              lex rest line (col+3) ((ARSHIFT, line, col) :: acc)
          | #">" :: #">" :: rest =>
              lex rest line (col+2) ((RSHIFT, line, col) :: acc)
          | #">" :: #"=" :: #"u" :: rest =>
              lex rest line (col+3) ((GEQU, line, col) :: acc)
          | #">" :: #"=" :: rest =>
              lex rest line (col+2) ((GEQ, line, col) :: acc)
          | #"&" :: #"=" :: #"=" :: rest =>
              lex rest line (col+3) ((AMPTEST, line, col) :: acc)
          | #"&" :: #"!" :: #"=" :: rest =>
              lex rest line (col+3) ((AMPNTEST, line, col) :: acc)
          | #"&" :: rest =>
              lex rest line (col+1) ((AMP, line, col) :: acc)
          | c :: rest =>
              if is_digit c then
                let val (n, rest', col') = parse_int_literal (cs, line, col)
                in lex rest' line col' ((INT n, line, col) :: acc) end
              else if is_alpha c then
                let val (w, rest') = collect_while is_alnum rest
                    val s = implode (c :: w)
                    val col' = col + String.size s
                in lex rest' line col' ((keyword_or_ident s, line, col) :: acc) end
              else err (line, col) ("unexpected character: " ^ str c)
        end
    in
      lex chars0 base_line base_col []
    end

  (* --- Parser --- *)

  fun pos [] = (0, 0)
    | pos ((_, l, c) :: _) = (l, c)

  fun peek [] = EOF
    | peek ((t, _, _) :: _) = t

  fun expect_tok tok toks msg =
    case toks of
      (t, l, c) :: rest =>
        if t = tok then rest
        else err (l, c) (msg ^ " but found unexpected token")
    | [] => err (0, 0) (msg ^ " but found end of input")

  fun expect_ident toks =
    case toks of
      (IDENT s, _, _) :: rest => (s, rest)
    | (_, l, c) :: _ => err (l, c) "expected identifier"
    | [] => err (0, 0) "expected identifier but found end of input"

  fun expect_semi toks = expect_tok SEMI toks "expected ';'"

  (* Parse comma-separated identifiers for parameter lists *)
  fun parse_ident_list toks =
    case peek toks of
      RPAR => ([], toks)
    | _ =>
        let val (name, toks) = expect_ident toks
        in case peek toks of
             COMMA => let val toks = tl toks
                          val (rest, toks) = parse_ident_list toks
                      in (name :: rest, toks) end
           | _ => ([name], toks)
        end

  (* Expression parsing *)
  fun parse_primary toks =
    case toks of
      (INT n, _, _) :: rest => (Const n, rest)
    | (IDENT s, _, _) :: rest => (Var s, rest)
    | (LPAR, _, _) :: rest =>
        let val (e, rest) = parse_exp rest
            val rest = expect_tok RPAR rest "expected ')'"
        in (e, rest) end
    | (_, l, c) :: _ => err (l, c) "expected expression"
    | [] => err (0, 0) "expected expression but found end of input"

  and parse_unary toks =
    case peek toks of
      STAR => let val toks = tl toks
                  val (e, toks) = parse_unary toks
              in (Load e, toks) end
    | _ => parse_primary toks

  and parse_shift toks =
    let val (left, toks) = parse_unary toks
        fun loop left toks =
          case peek toks of
            LSHIFT =>
              let val toks = tl toks
                  val (right, toks) = parse_unary toks
              in loop (Shift (Lsl, left, right)) toks end
          | RSHIFT =>
              let val toks = tl toks
                  val (right, toks) = parse_unary toks
              in loop (Shift (Asr, left, right)) toks end
          | ARSHIFT =>
              let val toks = tl toks
                  val (right, toks) = parse_unary toks
              in loop (Shift (Lsr, left, right)) toks end
          | TOK_ROR =>
              let val toks = tl toks
                  val (right, toks) = parse_unary toks
              in loop (Shift (Ror, left, right)) toks end
          | _ => (left, toks)
    in loop left toks end

  and parse_add toks =
    let val (left, toks) = parse_shift toks
        fun loop left toks =
          case peek toks of
            PLUS =>
              let val toks = tl toks
                  val (right, toks) = parse_shift toks
              in loop (Op (Add, [left, right])) toks end
          | MINUS =>
              let val toks = tl toks
                  val (right, toks) = parse_shift toks
              in loop (Op (Sub, [left, right])) toks end
          | _ => (left, toks)
    in loop left toks end

  and parse_and toks =
    let val (left, toks) = parse_add toks
        fun loop left toks =
          case peek toks of
            AMP =>
              let val toks = tl toks
                  val (right, toks) = parse_add toks
              in loop (Op (And, [left, right])) toks end
          | _ => (left, toks)
    in loop left toks end

  and parse_xor toks =
    let val (left, toks) = parse_and toks
        fun loop left toks =
          case peek toks of
            CARET =>
              let val toks = tl toks
                  val (right, toks) = parse_and toks
              in loop (Op (Xor, [left, right])) toks end
          | _ => (left, toks)
    in loop left toks end

  and parse_or toks =
    let val (left, toks) = parse_xor toks
        fun loop left toks =
          case peek toks of
            PIPE =>
              let val toks = tl toks
                  val (right, toks) = parse_xor toks
              in loop (Op (Or, [left, right])) toks end
          | _ => (left, toks)
    in loop left toks end

  and parse_exp toks = parse_or toks

  (* Parse expression argument list: f(e1, e2, ...) *)
  fun parse_exp_list toks =
    case peek toks of
      RPAR => ([], toks)
    | _ =>
        let val (e, toks) = parse_exp toks
        in case peek toks of
             COMMA => let val toks = tl toks
                          val (rest, toks) = parse_exp_list toks
                      in (e :: rest, toks) end
           | _ => ([e], toks)
        end

  (* Parse condition: ( ident cmp_op (ident|num) ) *)
  fun parse_cmp_op toks =
    case toks of
      (EQEQ, _, _) :: rest => (Equal, rest)
    | (BANGEQ, _, _) :: rest => (NotEqual, rest)
    | (LT, _, _) :: rest => (Less, rest)
    | (GEQ, _, _) :: rest => (NotLess, rest)
    | (LTU, _, _) :: rest => (Lower, rest)
    | (GEQU, _, _) :: rest => (NotLower, rest)
    | (AMPTEST, _, _) :: rest => (Test, rest)
    | (AMPNTEST, _, _) :: rest => (NotTest, rest)
    | (_, l, c) :: _ => err (l, c) "expected comparison operator"
    | [] => err (0, 0) "expected comparison operator"

  fun parse_cmp_rhs toks =
    case toks of
      (INT n, _, _) :: rest => (cConst n, rest)
    | (IDENT s, _, _) :: rest => (cVar s, rest)
    | (_, l, c) :: _ => err (l, c) "expected identifier or number in condition"
    | [] => err (0, 0) "expected identifier or number in condition"

  fun parse_cond toks =
    let val toks = expect_tok LPAR toks "expected '('"
        val (lhs, toks) = expect_ident toks
        val (cmp_op, toks) = parse_cmp_op toks
        val (rhs, toks) = parse_cmp_rhs toks
        val toks = expect_tok RPAR toks "expected ')'"
    in (cmp_op, lhs, rhs, toks) end

  (* Parse a block: { stmts } *)
  fun parse_block toks =
    let val toks = expect_tok LBRACE toks "expected '{'"
        val (s, toks) = parse_stmts toks
        val toks = expect_tok RBRACE toks "expected '}'"
    in (s, toks) end

  (* Parse statements until RBRACE, folding with Seq *)
  and parse_stmts toks =
    case peek toks of
      RBRACE => (Skip, toks)
    | EOF => (Skip, toks)
    | _ =>
        let val (s, toks) = parse_stmt toks
        in
          (* If this was a Dec, it already consumed remaining stmts *)
          case s of
            Dec _ => (s, toks)
          | _ =>
            case peek toks of
              RBRACE => (s, toks)
            | EOF => (s, toks)
            | _ => let val (rest, toks) = parse_stmts toks
                   in (Seq (s, rest), toks) end
        end

  and parse_stmt toks =
    case peek toks of
      TOK_IF =>
        let val toks = tl toks
            val (cmp_op, lhs, rhs, toks) = parse_cond toks
            val (then_b, toks) = parse_block toks
            val (else_b, toks) =
              case peek toks of
                TOK_ELSE => let val toks = tl toks
                                val (b, toks) = parse_block toks
                            in (b, toks) end
              | _ => (Skip, toks)
        in (If (cmp_op, lhs, rhs, then_b, else_b), toks) end
    | TOK_WHILE =>
        let val toks = tl toks
            val (cmp_op, lhs, rhs, toks) = parse_cond toks
            val (body, toks) = parse_block toks
        in (While (cmp_op, lhs, rhs, body), toks) end
    | TOK_RETURN =>
        let val toks = tl toks
            val (names, toks) = parse_ident_list toks
            val toks = expect_semi toks
        in (Return names, toks) end
    | TOK_VAR =>
        let val toks = tl toks
            val (name, toks) = expect_ident toks
            val toks = expect_tok ASSIGN toks "expected '='"
            val (e, toks) = parse_exp toks
            val toks = expect_semi toks
            (* remaining stmts become the body of Dec *)
            val (body, toks) = parse_stmts toks
        in (Dec (name, e, body), toks) end
    | TOK_MOVE =>
        let val toks = tl toks
            fun parse_pairs toks =
              let val (dst, toks) = expect_ident toks
                  val toks = expect_tok LARROW toks "expected '<-'"
                  val (src, toks) = expect_ident toks
              in case peek toks of
                   COMMA => let val toks = tl toks
                                val (rest, toks) = parse_pairs toks
                            in ((dst, src) :: rest, toks) end
                 | _ => ([(dst, src)], toks)
              end
            val (pairs, toks) = parse_pairs toks
            val toks = expect_semi toks
        in (Move pairs, toks) end
    | STAR =>
        let val toks = tl toks
            val (addr, toks) = parse_exp toks
            val toks = expect_tok ASSIGN toks "expected '='"
            val (v, toks) = expect_ident toks
            val toks = expect_semi toks
        in (Store (addr, v), toks) end
    | IDENT name =>
        let val toks = tl toks
        in
          case peek toks of
            (* bare call: f(args); *)
            LPAR =>
              let val toks = tl toks
                  val (args, toks) = parse_exp_list toks
                  val toks = expect_tok RPAR toks "expected ')'"
                  val toks = expect_semi toks
              in (Call (NONE, name, args), toks) end
          | COMMA =>
              (* multi-return call: r1, r2 = f(args); *)
              let fun collect_rets acc toks =
                    case peek toks of
                      COMMA => let val toks = tl toks
                                   val (n, toks) = expect_ident toks
                               in collect_rets (n :: acc) toks end
                    | _ => (rev acc, toks)
                  val (more, toks) = collect_rets [name] toks
                  val toks = expect_tok ASSIGN toks "expected '='"
                  val (fname, toks) = expect_ident toks
                  val toks = expect_tok LPAR toks "expected '('"
                  val (args, toks) = parse_exp_list toks
                  val toks = expect_tok RPAR toks "expected ')'"
                  val toks = expect_semi toks
              in (Call (SOME more, fname, args), toks) end
          | ASSIGN =>
              (* x = expr; OR x = f(args); *)
              let val toks = tl toks (* consume = *)
              in
                (* Peek ahead: if IDENT followed by LPAR, it's a call *)
                case toks of
                  (IDENT fname, _, _) :: (LPAR, _, _) :: rest =>
                    let val toks = rest (* consumed fname and LPAR *)
                        val (args, toks) = parse_exp_list toks
                        val toks = expect_tok RPAR toks "expected ')'"
                        val toks = expect_semi toks
                    in (Call (SOME [name], fname, args), toks) end
                | _ =>
                    let val (e, toks) = parse_exp toks
                        val toks = expect_semi toks
                    in (Assign (name, e), toks) end
              end
          | _ => let val (l, c) = pos toks
                 in err (l, c) ("unexpected token after identifier '" ^ name ^ "'") end
        end
    | _ => let val (l, c) = pos toks
           in err (l, c) "expected statement" end

  (* Parse function: name(params) { body } *)
  fun parse_func toks =
    let val (name, toks) = expect_ident toks
        val toks = expect_tok LPAR toks "expected '('"
        val (params, toks) = parse_ident_list toks
        val toks = expect_tok RPAR toks "expected ')'"
        val (body, toks) = parse_block toks
    in ((name, params, body) : func, toks) end

  (* Parse program: sequence of functions until EOF *)
  fun parse_prog toks =
    case peek toks of
      EOF => []
    | _ => let val (f, toks) = parse_func toks
               val rest = parse_prog toks
           in f :: rest end

  fun parse input =
    let val toks = tokenize_all input
    in parse_prog toks end

  (* --- Term generation --- *)

  local
    val alpha = Type.alpha

    fun mk_asm_const n = HolKernel.prim_mk_const {Thy="asm", Name=n}
    val add_tm      = mk_asm_const "Add"
    val sub_tm      = mk_asm_const "Sub"
    val and_tm      = mk_asm_const "And"
    val or_tm       = mk_asm_const "Or"
    val xor_tm      = mk_asm_const "Xor"
    val equal_tm    = mk_asm_const "Equal"
    val lower_tm    = mk_asm_const "Lower"
    val less_tm     = mk_asm_const "Less"
    val test_tm     = mk_asm_const "Test"
    val notequal_tm = mk_asm_const "NotEqual"
    val notlower_tm = mk_asm_const "NotLower"
    val notless_tm  = mk_asm_const "NotLess"
    val nottest_tm  = mk_asm_const "NotTest"

    val str_ty = mlstringSyntax.mlstring_ty
    val str_pair_ty = pairSyntax.mk_prod (str_ty, str_ty)
    val str_list_ty = listSyntax.mk_list_type str_ty

    val mk_str = mlstringSyntax.mk_mlstring
    fun mk_str_pair (l, r) = pairSyntax.mk_pair (mk_str l, mk_str r)
    val mk_str_list = listSyntax.lift_list str_list_ty mk_str
    fun mk_word n =
      integer_wordSyntax.mk_i2w (intSyntax.term_of_int (Arbint.fromLargeInt n), alpha)

    fun mk_bignum_ty tyop =
      Type.mk_thy_type {Thy="bignumLang", Tyop=tyop, Args=[alpha]}
    val exp_ty = mk_bignum_ty "exp"
    val stmt_ty = mk_bignum_ty "stmt"
    val func_ty =
      pairSyntax.mk_prod(str_ty, pairSyntax.mk_prod (str_list_ty, stmt_ty))

    val (_,mk_Const,_,_) = HolKernel.syntax_fns1 "bignumLang" "Const"
    val (_,mk_Var,_,_)   = HolKernel.syntax_fns1 "bignumLang" "Var"
    val (_,mk_Load,_,_)  = HolKernel.syntax_fns1 "bignumLang" "Load"
    val (_,mk_Op,_,_)    = HolKernel.syntax_fns2 "bignumLang" "Op"
    val (_,mk_Shift,_,_) = HolKernel.syntax_fns3 "bignumLang" "Shift"

    val (_,mk_cVar,_,_)   = HolKernel.syntax_fns1 "bignumLang" "cVar"
    val (_,mk_cConst,_,_) = HolKernel.syntax_fns1 "bignumLang" "cConst"

    fun mk_bignum_const n = HolKernel.prim_mk_const {Thy="bignumLang", Name=n}
    val skip_tm = mk_bignum_const "Skip"
    val if_tm = mk_bignum_const "If"

    fun mk_If (cmp, var, arg, thn, els) =
      list_mk_comb (if_tm, [cmp, var, arg, thn, els])

    val (_,mk_Seq,_,_)    = HolKernel.syntax_fns2 "bignumLang" "Seq"
    val (_,mk_While,_,_)  = HolKernel.syntax_fns4 "bignumLang" "While"
    val (_,mk_Dec,_,_)    = HolKernel.syntax_fns3 "bignumLang" "Dec"
    val (_,mk_Assign,_,_) = HolKernel.syntax_fns2 "bignumLang" "Assign"
    val (_,mk_Move,_,_)   = HolKernel.syntax_fns1 "bignumLang" "Move"
    val (_,mk_Store,_,_)  = HolKernel.syntax_fns2 "bignumLang" "Store"
    val (_,mk_Return,_,_) = HolKernel.syntax_fns1 "bignumLang" "Return"
    val (_,mk_Call,_,_)   = HolKernel.syntax_fns3 "bignumLang" "Call"
  in

  fun binop_to_term Add = add_tm
    | binop_to_term Sub = sub_tm
    | binop_to_term And = and_tm
    | binop_to_term Or  = or_tm
    | binop_to_term Xor = xor_tm

  fun cmp_to_term Equal    = equal_tm
    | cmp_to_term Lower    = lower_tm
    | cmp_to_term Less     = less_tm
    | cmp_to_term Test     = test_tm
    | cmp_to_term NotEqual = notequal_tm
    | cmp_to_term NotLower = notlower_tm
    | cmp_to_term NotLess  = notless_tm
    | cmp_to_term NotTest  = nottest_tm

  fun shift_to_term Lsl = astSyntax.Lsl
    | shift_to_term Lsr = astSyntax.Lsr
    | shift_to_term Asr = astSyntax.Asr
    | shift_to_term Ror = astSyntax.Ror

  fun exp_to_term (Const n) =
        mk_Const (mk_word n)
    | exp_to_term (Var s) =
        mk_Var (mk_str s)
    | exp_to_term (Load e) =
        mk_Load (exp_to_term e)
    | exp_to_term (Op (b, es)) =
        mk_Op (binop_to_term b, listSyntax.lift_list (listSyntax.mk_list_type exp_ty) exp_to_term es)
    | exp_to_term (Shift (sh, e1, e2)) =
        mk_Shift (shift_to_term sh, exp_to_term e1, exp_to_term e2)

  fun cmp_arg_to_term (cVar s)   = mk_cVar (mk_str s)
    | cmp_arg_to_term (cConst n) = mk_cConst (mk_word n)

  fun stmt_to_term Skip = skip_tm
    | stmt_to_term (Seq (s1, s2)) =
        mk_Seq (stmt_to_term s1, stmt_to_term s2)
    | stmt_to_term (If (c, v, ca, s1, s2)) =
        mk_If (cmp_to_term c, mk_str v, cmp_arg_to_term ca,
               stmt_to_term s1, stmt_to_term s2)
    | stmt_to_term (While (c, v, ca, s)) =
        mk_While (cmp_to_term c, mk_str v, cmp_arg_to_term ca, stmt_to_term s)
    | stmt_to_term (Dec (v, e, s)) =
        mk_Dec (mk_str v, exp_to_term e, stmt_to_term s)
    | stmt_to_term (Assign (v, e)) =
        mk_Assign (mk_str v, exp_to_term e)
    | stmt_to_term (Move pairs) =
        mk_Move (listSyntax.lift_list (listSyntax.mk_list_type str_pair_ty) mk_str_pair pairs)
    | stmt_to_term (Store (e, v)) =
        mk_Store (exp_to_term e, mk_str v)
    | stmt_to_term (Return vs) =
        mk_Return (mk_str_list vs)
    | stmt_to_term (Call (ret, fname, args)) = let
        val ret_tm = optionSyntax.lift_option str_list_ty mk_str_list ret
        val args_tm = listSyntax.lift_list (listSyntax.mk_list_type exp_ty) exp_to_term args
      in mk_Call (ret_tm, mk_str fname, args_tm) end

  fun func_to_term (name, params, body) =
    pairSyntax.mk_pair (mk_str name,
      pairSyntax.mk_pair (mk_str_list params, stmt_to_term body))

  fun prog_to_term prog =
    listSyntax.lift_list (listSyntax.mk_list_type func_ty) func_to_term prog

  fun bignum [QUOTE s] =
        ((prog_to_term $ parse s) handle e => raise wrap_exn "bignumLangLib" "bignum" e)
    | bignum _         =
        raise mk_HOL_ERR "bignumLangLib" "bignum" "expected a single QUOTE fragment"
  end

end
