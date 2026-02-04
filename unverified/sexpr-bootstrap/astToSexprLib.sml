structure astToSexprLib = struct

open preamble mlstringSyntax fromSexpTheory

datatype exp = exp_tuple of exp list | exp_list of exp list | exp_str of string;

fun escape_wrap c = "\"" ^ c ^ "\""
fun escape_char c =
  let
    val to_hex = (StringCvt.padLeft #"0" 2) o (Int.fmt StringCvt.HEX) o Char.ord
  in
    if c = #"\\" then "\\\\\\\\"
    else if c = #"\"" then "\\\""
    else if Char.isPrint c then Char.toString c
    else "\\\\" ^ (to_hex c)
  end

val fromHOLchar =
  escape_wrap o escape_char o stringSyntax.fromHOLchar;
val fromHOLstring =
  escape_wrap o (String.translate escape_char) o mlstringSyntax.dest_mlstring;
val fromHOLnum = Arbnumcore.toString o numSyntax.dest_numeral;

fun char_to_exp c = exp_list [exp_str "char", exp_str (fromHOLchar c)]
val string_to_exp = exp_str o fromHOLstring;
val num_to_exp = exp_str o fromHOLnum;

fun word_to_exp lit_name w =
  let
    val str = Arbnumcore.toString (wordsSyntax.dest_word_literal w)
  in
    exp_list [exp_str lit_name, exp_str str]
  end

fun int_to_exp i =
  let
    fun via_num i = (num_to_exp o rhs o concl o EVAL) ``Num (^i)``
  in
    if intSyntax.is_negated i
      then exp_list [exp_str "-", via_num (intSyntax.mk_negated i)]
      else via_num i
  end

fun loc_to_exp xs =
  let
    fun loc_to_str tm =
      if aconv tm “UNKNOWNpt” then "unk" else
      if aconv (repeat rator tm) “POSN” then
        "(" ^ (numSyntax.dest_numeral (rand (rator tm)) |> Arbnum.toString) ^
        " " ^ (numSyntax.dest_numeral (rand tm) |> Arbnum.toString) ^ ")"
      else "0 0 0"
    fun join [] = ""
      | join [x] = x
      | join (x::xs) = x ^ " " ^ join xs
  in
    exp_list [exp_str (join (map loc_to_str xs))]
  end

val int_lit = ``ast$IntLit``;
val char_lit = ``ast$Char``;
val word8_lit = ``ast$Word8``;
val word64_lit = ``ast$Word64``;
val float64_lit = prim_mk_const{Thy = "ast", Name = "Float64"}
fun lit_to_exp t =
  let
    val (x, xs) = strip_comb t
    val h = hd xs
  in
    if same_const x int_lit then int_to_exp h
    else if same_const x char_lit then char_to_exp h
    else if same_const x word8_lit then word_to_exp "word8" h
    else if same_const x word64_lit then word_to_exp "word64" h
    else if same_const x float64_lit then word_to_exp "float64" h
    else string_to_exp h
  end

val shift_op = ``ast$Shift``;
val test_op = ``ast$Test``;
val arith_op = ``ast$Arith``;
val from_to_op = ``ast$FromTo``;
val ffi_op = ``ast$FFI``;
val wordT_W8 = ``WordT W8``;
val wordT_W64 = ``WordT W64``;
val test_eq = ``ast$Equal``
val test_lt = ``ast$Compare Lt``
val test_leq = ``ast$Compare Leq``
val test_gt = ``ast$Compare Gt``
val test_geq = ``ast$Compare Geq``
val test_alt_lt = ``ast$AltCompare Lt``
val test_alt_leq = ``ast$AltCompare Leq``
val test_alt_gt = ``ast$AltCompare Gt``
val test_alt_geq = ``ast$AltCompare Geq``
fun op_to_exp arg =
  let
    val underscore_filter =
      String.implode o filter (fn n => n <> #"_") o String.explode
    val to_string = #1 o dest_const
    fun filtered_string t =
      case to_string t of "W8" => "8"
                        | "W64" => "64"
                        | s => underscore_filter s
    fun wordInt xs s = exp_str ((hd (map to_string xs)) ^ s)
    fun ffi xs = exp_tuple [exp_str "FFI", string_to_exp (hd xs)]
    fun test_ty x =
      if aconv x wordT_W8 then exp_str "Word8T" else
      if aconv x wordT_W64 then exp_str "Word64T" else
        exp_str (to_string x)
    fun test_name x =
      if aconv x test_eq      then exp_str "Equal" else
      if aconv x test_lt      then exp_str "Less" else
      if aconv x test_leq     then exp_str "LessEq" else
      if aconv x test_gt      then exp_str "Greater" else
      if aconv x test_geq     then exp_str "GreaterEq" else
      if aconv x test_alt_lt  then exp_str "AltLess" else
      if aconv x test_alt_leq then exp_str "AltLessEq" else
      if aconv x test_alt_gt  then exp_str "AltGreater" else
      if aconv x test_alt_geq then exp_str "AltGreaterEq" else
        failwith ("test_name failed for: " ^ term_to_string x)
    fun test xs = exp_tuple [exp_str "Test",
                             test_name (hd xs),
                             test_ty (hd (tl xs))]
    fun from_to xs = exp_tuple [exp_str "FromTo",
                                test_ty (hd xs),
                                test_ty (hd (tl xs))]
    fun arith xs = exp_tuple [exp_str "Arith",
                              exp_str (hd xs |> dest_const |> fst),
                              test_ty (hd (tl xs))]
    fun shift xs =
      let
        val consts = List.take (xs, 2)
        val str = "Shift" ^ String.concat (map filtered_string consts)
      in
        exp_tuple [exp_str str, num_to_exp (last xs)]
      end
    val (x, xs) = strip_comb arg
  in
    if same_const x shift_op then shift xs
    else if same_const x ffi_op then ffi xs
    else if same_const x test_op then test xs
    else if same_const x arith_op then arith xs
    else if same_const x from_to_op then from_to xs
    else exp_str (String.concat (map filtered_string (x::xs)))
  end

val cons = ``CONS : 'a -> 'a list -> 'a list``;
val comma = ``$, : 'a -> 'b -> 'a # 'b``;
val pvar = ``ast$Pvar``;
val pany = ``ast$Pany``;
val locs = ``Locs``;
val nil_l = ``[] : 'a list``;
val app = ``ast$App``;
val lit = ``ast$Lit``;
val plit = ``ast$Plit``;
fun ast_to_exp term =
  let
    val list_to_exp = map ast_to_exp
    fun app_to_exp const args =
      let
        val exp = (exp_str o #1 o dest_const) const
        val op_exp = op_to_exp (hd args)
        val args_exp = list_to_exp (tl args)
      in
        exp_list (exp::op_exp::args_exp)
      end
    fun generic_to_exp const args =
      let
        val exp = (exp_str o #1 o dest_const) const
        val args_exp = list_to_exp args
      in
        case args of [] => exp
                   | _ => exp_list (exp::args_exp)
      end
    fun cons_to_exp term =
      (exp_list o list_to_exp o #1 o listSyntax.dest_list) term
    val tuple_to_exp =
      exp_tuple o list_to_exp o pairSyntax.spine_pair
    val (x, xs) = strip_comb term
  in
    if same_const x pvar then ast_to_exp (hd xs)
    else if same_const x pany then exp_list [exp_str "Pany"]
    else if same_const x lit then
      exp_list [exp_str "Lit", lit_to_exp (hd xs)]
    else if same_const x plit then
      exp_list [exp_str "Plit", lit_to_exp (hd xs)]
    else if same_const x locs then loc_to_exp xs
    else if same_const x nil_l then exp_list []
    else if same_const x cons then cons_to_exp term
    else if same_const x comma then tuple_to_exp term
    else if same_const x app then app_to_exp x xs
    else if mlstringSyntax.is_mlstring_literal term then string_to_exp term
    else generic_to_exp x xs
  end

fun exp_to_string e =
  let
    val list_to_string =
      (String.concatWith " ") o (map exp_to_string)
    fun tuple_to_string t =
      case t of [] => ""
              | [x, exp_list l] => (exp_to_string x) ^ " " ^ (list_to_string l)
              | [x, y] => (exp_to_string x) ^ " . " ^ (exp_to_string y)
              | x::xs => (exp_to_string x) ^ " " ^ (tuple_to_string xs)
  in
    case e of exp_str s => s
            | exp_tuple l => "(" ^ (tuple_to_string l) ^ ")"
            | exp_list [] => "nil"
            | exp_list l => "(" ^ (list_to_string l) ^ ")"
  end

fun write_ast write prog =
  let
    val out = write o exp_to_string o ast_to_exp
    val (funcs, _) = listSyntax.dest_list prog
    fun step l =
      case l of [] => ()
               | [x] => out x
               | x::xs => (out x; write " \n"; step xs)
  in
    write "(\n"; step funcs; write "\n)"
  end

fun write_ast_to_file filename prog =
  let
    val fd = TextIO.openOut filename
    val _ = write_ast (fn s => TextIO.output(fd, s)) prog
  in
    TextIO.closeOut fd
  end

end
