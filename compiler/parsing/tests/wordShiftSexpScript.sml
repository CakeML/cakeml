(*
  S-expression regression tests for binary word shifts.
*)
Theory wordShiftSexp
Ancestors
  fromSexp
Libs
  preamble

fun check tm =
  if rhs (concl (EVAL tm)) ~~ ``T`` then ()
  else raise Fail ("Word-shift S-expression test failed: " ^ term_to_string tm);

val shifts = [("Lsl", ``Lsl``), ("Lsr", ``Lsr``),
              ("Asr", ``Asr``), ("Ror", ``Ror``)];
val sizes = [("8", "Word8T", ``W8``), ("64", "Word64T", ``W64``)];

val _ = app (fn (name, sh) => app (fn (width, type_name, sz) =>
  let
    val shift_name = stringSyntax.fromMLstring ("Shift" ^ name)
    val type_name = stringSyntax.fromMLstring type_name
    val old_name = stringSyntax.fromMLstring ("Shift" ^ width ^ name)
    val oper = ``Arith (Shift ^sh) (WordT ^sz)``
    val encoded = ``SX_CONS (SX_SYM "Arith")
                     (SX_CONS (SX_SYM ^shift_name) (SX_SYM ^type_name))``
    val expr = ``App ^oper [Var (Short «value»); Var (Short «amount»)]``
  in
    check ``sexpop ^encoded = SOME ^oper``;
    check ``opsexp ^oper = ^encoded``;
    check ``sexpexp (expsexp ^expr) = SOME ^expr``;
    check ``valid_sexp (expsexp ^expr)``;
    check ``sexpop (SX_CONS (SX_SYM ^old_name) (SX_NUM 7)) = NONE``
  end) sizes) shifts;
