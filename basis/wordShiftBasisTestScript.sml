(*
  Check that basis word shifts use one binary primitive and preserve
  the behavior of large shift counts.
*)
Theory wordShiftBasisTest[no_sig_docs]
Ancestors
  Word8Prog
Libs
  preamble astSyntax semanticPrimitivesSyntax

val _ = computeLib.add_funs (map
  (SIMP_CONV (srw_ss ()) [semanticPrimitivesTheory.check_type_def])
  [``check_type IntT (Litv (IntLit i))``,
   ``check_type (WordT W8) (Litv (Word8 w))``,
   ``check_type (WordT W64) (Litv (Word64 w))``]);

fun is_shift_app tm =
  case total astSyntax.dest_App tm of
    NONE => false
  | SOME (oper, _) => can (match_term ``Arith (Shift sh) (WordT sz)``) oper;

fun check_shift theory sz literal lookup width op_name sh =
  let
    val definition = DB.fetch theory ("var_word_" ^ op_name ^ "_v_def")
    val (_, value_name, body) =
      semanticPrimitivesSyntax.dest_Closure (rhs (concl definition))
    val (amount_name, body) = astSyntax.dest_Fun body
    val shift = case find_terms is_shift_app body of
                  [tm] => tm
                | _ => raise Fail (theory ^ ": expected one binary shift")
    val (oper, args) = astSyntax.dest_App shift
    val args = fst (listSyntax.dest_list args)
    val _ = if oper ~~ ``Arith (Shift ^sh) (WordT ^sz)`` andalso
               length args = 2 then ()
            else raise Fail (theory ^ ": incorrect shift operation")
    val value = if width = 8 then ``129w:word8``
                else ``0x8000000000000001w:word64``
    val amounts = map (numSyntax.mk_numeral o Arbnum.fromInt)
                    [0, 1, width - 1, width, width + 1, 256] @
                  [``18446744073709551616n``, ``18446744073709551617n``]
    fun check amount =
      let
        val code = subst
          [``Var (Short ^value_name)`` |-> ``Lit (^literal ^value)``,
           ``Var (Short ^amount_name)`` |-> ``Lit (IntLit (& ^amount))``] body
        val result = EVAL
          ``evaluate empty_state ARB [^code] =
            (empty_state, Rval [Litv (^literal (^lookup ^sh ^value ^amount))])``
      in
        if rhs (concl result) ~~ ``T`` then ()
        else raise Fail (theory ^ ": incorrect " ^ op_name ^ " result at " ^
                         term_to_string amount ^ "\n" ^
                         term_to_string (rhs (concl result)))
      end
  in app check amounts end;

val shifts = [("lsl", ``Lsl``), ("lsr", ``Lsr``),
              ("asr", ``Asr``), ("ror", ``Ror``)];

val _ = app (fn (name, sh) =>
  check_shift "Word64Prog" ``W64`` ``Word64`` ``shift64_lookup`` 64 name sh)
  shifts;

val _ = app (fn (name, sh) =>
  check_shift "Word8Prog" ``W8`` ``Word8`` ``shift8_lookup`` 8 name sh)
  shifts;
