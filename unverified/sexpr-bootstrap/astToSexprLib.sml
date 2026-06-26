structure astToSexprLib = struct

open preamble mlstringSyntax

(* This library is a fast SML reimplementation of the HOL encoders in
   compiler/parsing/fromSexpScript.sml (decsexp/expsexp/patsexp/...).  It walks
   a HOL term representing a CakeML AST and writes the corresponding
   s-expression text, exactly as mlsexp$sexp_to_string would print the encoder
   result.  Working directly on terms avoids EVALuating the (slow) HOL
   definitions on large bootstrap programs.

   The textual format must match the mlsexp representation
   (basis/pure/mlsexpScript.sml): sexp = Atom mlstring | Expr (sexp list).
   There are no cons-pairs, no dotted notation and no nil; lists are Expr [...]
   and the empty list prints as "()".  The tag strings below mirror the
   encoder definitions and must be kept in sync with them. *)

datatype sexp = Atom of string | Expr of sexp list;

(*--------------------------------------------------------------*
   Printing: faithful port of mlsexp$sexp_to_string
 *--------------------------------------------------------------*)

(* HOL isPrint c <=> 32 <= ORD c < 127.  Do NOT use Char.isPrint, whose
   behaviour for ORD c >= 127 is implementation-defined. *)
fun isPrintH c = let val n = Char.ord c in 32 <= n andalso n < 127 end
(* HOL isSpace c <=> ORD c = 32 \/ 9 <= ORD c <= 13 *)
fun isSpaceH c = let val n = Char.ord c in n = 32 orelse (9 <= n andalso n <= 13) end

(* mlsexp$is_safe_char *)
fun is_safe_char c = not (Char.contains "()\"\000" c) andalso not (isSpaceH c)

(* mlstring$char_escaped *)
fun char_escaped c =
  case c of
      #"\t" => "\\t"
    | #"\n" => "\\n"
    | #"\\" => "\\\\"
    | #"\"" => "\\\""
    | _     => String.str c

(* mlstring$escape_str *)
fun escape_str s = "\"" ^ String.concat (map char_escaped (String.explode s)) ^ "\""

(* mlsexp$make_str_safe *)
fun make_str_safe s =
  if s = "" then "\"\""
  else if List.all is_safe_char (String.explode s) then s
  else escape_str s

(* mlsexp$sexp_to_string: atoms via make_str_safe, lists space-separated in
   parentheses ("()" when empty). *)
fun sexp_to_string (Atom s) = make_str_safe s
  | sexp_to_string (Expr l) =
      "(" ^ String.concatWith " " (map sexp_to_string l) ^ ")"

(*--------------------------------------------------------------*
   Atom builders mirroring SEXSTR / SXNUM and integer formatting
 *--------------------------------------------------------------*)

(* fromSexp$encode_control: double backslashes; keep printable chars; escape
   non-printable chars as a single backslash followed by two uppercase hex
   digits (with a leading "0" when ORD c < 16). *)
fun encode_control_char c =
  if c = #"\\" then "\\\\"
  else if isPrintH c then String.str c
  else "\\" ^ (if Char.ord c < 16 then "0" else "") ^ Int.fmt StringCvt.HEX (Char.ord c)
fun encode_control s = String.concat (map encode_control_char (String.explode s))

(* SEXSTR (string) and SEXSTR (mlstring term) *)
fun sexstr_str s = Atom (encode_control s)
fun sexstr t = sexstr_str (mlstringSyntax.dest_mlstring t)

(* SXNUM applied to a num term and to a word literal *)
fun sxnum_num n = Atom (Arbnum.toString (numSyntax.dest_numeral n))
fun sxnum_word w = Atom (Arbnum.toString (wordsSyntax.dest_word_literal w))

(* mlint$toString of an integer literal: "~" sign for negatives, decimal
   magnitude. *)
fun int_to_string t =
  let
    val i = intSyntax.int_of_term t
    val mag = Arbnum.toString (Arbint.toNat (Arbint.abs i))
  in
    if Arbint.<(i, Arbint.zero) then "~" ^ mag else mag
  end

(*--------------------------------------------------------------*
   Leaf encoders (explicit tables mirroring the HOL definitions)
 *--------------------------------------------------------------*)

val const_name = #1 o dest_const

fun width_digits w =
  case const_name w of
      "W8"  => "8"
    | "W64" => "64"
    | s     => failwith ("astToSexprLib: unknown word_size " ^ s)

(* fromSexp$prim_typesexp *)
fun prim_typesexp pt =
  let val (h, args) = strip_comb pt in
    case const_name h of
        "WordT" => Atom ("Word" ^ width_digits (hd args) ^ "T")
      | s       => Atom s  (* BoolT, IntT, CharT, StrT, Float64T *)
  end

(* fromSexp$arithsexp: constructor names match the tags verbatim *)
fun arithsexp a = Atom (const_name a)

(* fromSexp$testsexp *)
fun cmp_word nm =
  case nm of
      "Lt"  => "Less"
    | "Leq" => "LessEq"
    | "Gt"  => "Greater"
    | "Geq" => "GreaterEq"
    | s     => failwith ("astToSexprLib: unknown opb " ^ s)
fun testsexp t =
  let val (h, args) = strip_comb t in
    case const_name h of
        "Equal"      => Atom "Equal"
      | "Compare"    => Atom (cmp_word (const_name (hd args)))
      | "AltCompare" => Atom ("Alt" ^ cmp_word (const_name (hd args)))
      | s            => failwith ("astToSexprLib: unknown test " ^ s)
  end

(* fromSexp$opsexp for the ThunkOp cases; modes use encode_thunk_mode, whose
   output equals the constructor name. *)
fun thunkop t =
  let val (h, args) = strip_comb t in
    case const_name h of
        "ForceThunk"  => Atom "ForceThunk"
      | "AllocThunk"  => Expr [Atom "AllocThunk", Atom (const_name (hd args))]
      | "UpdateThunk" => Expr [Atom "UpdateThunk", Atom (const_name (hd args))]
      | s             => failwith ("astToSexprLib: unknown thunk_op " ^ s)
  end

(* fromSexp$opsexp.  Operators only ever appear as the first argument of App,
   so they are routed here rather than through the generic dispatcher. *)
fun opsexp t =
  let val (h, args) = strip_comb t in
    case const_name h of
        "Shift"   => Expr [Atom ("Shift" ^ width_digits (List.nth (args, 0))
                                          ^ const_name (List.nth (args, 1))),
                           sxnum_num (List.nth (args, 2))]
      | "FFI"     => Expr [Atom "FFI", sexstr (hd args)]
      | "Arith"   => Expr [Atom "Arith", arithsexp (List.nth (args, 0)),
                           prim_typesexp (List.nth (args, 1))]
      | "FromTo"  => Expr [Atom "FromTo", prim_typesexp (List.nth (args, 0)),
                           prim_typesexp (List.nth (args, 1))]
      | "Test"    => Expr [Atom "Test", testsexp (List.nth (args, 0)),
                           prim_typesexp (List.nth (args, 1))]
      | "ThunkOp" => thunkop (hd args)
      | nm        => Atom nm
  end

(* fromSexp$litsexp *)
fun lit_to_sexp t =
  let val (h, args) = strip_comb t val a = hd args in
    case const_name h of
        "IntLit"  => Expr [Atom "IntLit", Atom (int_to_string a)]
      | "Char"    => Expr [Atom "char", sexstr_str (String.str (stringSyntax.fromHOLchar a))]
      | "StrLit"  => sexstr a
      | "Word8"   => Expr [Atom "word8", sxnum_word a]
      | "Word64"  => Expr [Atom "word64", sxnum_word a]
      | "Float64" => Expr [Atom "float64", sxnum_word a]
      | s         => failwith ("astToSexprLib: unknown lit " ^ s)
  end

(* fromSexp$locnsexp *)
fun locnsexp p =
  let val (h, args) = strip_comb p in
    case const_name h of
        "UNKNOWNpt" => Atom "unk"
      | "EOFpt"     => Atom "eof"
      | "POSN"      => Expr [sxnum_num (List.nth (args, 0)), sxnum_num (List.nth (args, 1))]
      | s           => failwith ("astToSexprLib: unknown locn " ^ s)
  end
(* fromSexp$locssexp; args are the two arguments of Locs *)
fun locssexp args = Expr [locnsexp (List.nth (args, 0)), locnsexp (List.nth (args, 1))]

(*--------------------------------------------------------------*
   Generic recursive dispatcher
 *--------------------------------------------------------------*)

val pvar_tm = astSyntax.Pvar_tm
val pany_tm = astSyntax.Pany
val lit_tm = astSyntax.Lit_tm
val plit_tm = astSyntax.Plit_tm
val app_tm = astSyntax.App_tm
val cons_tm = listSyntax.cons_tm
val nil_tm = listSyntax.nil_tm
val comma_tm = pairSyntax.comma_tm
val locs_tm = prim_mk_const{Thy="location",Name="Locs"}

fun ast_to_sexp term =
  let
    val (x, xs) = strip_comb term
  in
    (* a list: nil -> Expr []; cons -> Expr of the converted elements *)
    if same_const x nil_tm then Expr []
    else if same_const x cons_tm then
      Expr (map ast_to_sexp (#1 (listSyntax.dest_list term)))
    (* a pair (a, b) -> 2-element Expr; the right-nested tuple structure makes
       triples like (f, x, e) nest as Expr [.; Expr [.; .]] to match the
       encoder lambdas. *)
    else if same_const x comma_tm then
      Expr [ast_to_sexp (List.nth (xs, 0)), ast_to_sexp (List.nth (xs, 1))]
    (* Pvar s is a bare SEXSTR (no tag); Pany is a one-element Expr *)
    else if same_const x pvar_tm then sexstr (hd xs)
    else if same_const x pany_tm then Expr [Atom "Pany"]
    (* literals are encoded by litsexp *)
    else if same_const x lit_tm then Expr [Atom "Lit", lit_to_sexp (hd xs)]
    else if same_const x plit_tm then Expr [Atom "Plit", lit_to_sexp (hd xs)]
    (* App routes its operator through opsexp *)
    else if same_const x app_tm then
      Expr [Atom "App", opsexp (List.nth (xs, 0)), ast_to_sexp (List.nth (xs, 1))]
    else if same_const x locs_tm then locssexp xs
    (* a raw mlstring (identifier names etc.) is a SEXSTR *)
    else if mlstringSyntax.is_mlstring_literal term then sexstr term
    (* generic: nullary constructor -> bare atom; applied -> tagged Expr.  This
       handles NONE/SOME, Short/Long, Andalso/Orelse, ast_t, and every other
       constructor whose tag equals its name. *)
    else
      case xs of
          [] => Atom (const_name x)
        | _  => Expr (Atom (const_name x) :: map ast_to_sexp xs)
  end

(*--------------------------------------------------------------*
   Top-level output
 *--------------------------------------------------------------*)

(* Writes the program as a single s-expression: an Expr of the top-level
   declarations, with newlines between them for readability (newlines are
   whitespace and parse identically to spaces). *)
fun write_ast write prog =
  let
    val out = write o sexp_to_string o ast_to_sexp
    val (decs, _) = listSyntax.dest_list prog
    fun step [] = ()
      | step [x] = out x
      | step (x::xs) = (out x; write " \n"; step xs)
  in
    write "(\n"; step decs; write "\n)"
  end

fun write_ast_to_file filename prog =
  let
    val fd = TextIO.openOut filename
    val _ = write_ast (fn s => TextIO.output(fd, s)) prog
  in
    TextIO.closeOut fd
  end

end
