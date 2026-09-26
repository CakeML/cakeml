(*
  Check fixed and computed word shifts at the flatLang-to-closLang boundary.
*)
Theory flat_to_clos_shift_test[no_sig_docs]
Ancestors
  flat_to_clos
Libs
  preamble

fun check expr expected =
  let
    val result = EVAL
      ``flat_to_clos$compile [SOME «n»; SOME «w»] [^expr]``
    val actual = rhs (concl result)
  in
    if actual ~~ ``[^expected]`` then ()
    else raise Fail ("Incorrect shift compilation:\n" ^ term_to_string actual)
  end;

val value = ``flatLang$Var_local None «w»``;
val count = ``flatLang$Var_local None «n»``;
val raised = ``flatLang$Raise None (flatLang$Lit None (IntLit 3))``;
val compiled_raise = ``closLang$Raise None (Op None (IntOp (Const 3)) [])``;

fun check_width sz literal width maximum one =
  let
    val amounts = map (numSyntax.mk_numeral o Arbnum.fromInt)
                    [0, 1, width - 1, width, width + 1] @ [maximum]
    fun shift sh =
      let
        fun source value count =
          ``flatLang$App None (Src (Arith (Shift ^sh) (WordT ^sz)))
              [^value; ^count]``
        val _ = app (fn amount =>
          check (source value ``flatLang$Lit None (^literal (n2w ^amount))``)
            ``closLang$Op None (WordOp (WordShift ^sz ^sh ^amount))
                [Var None 1]``) amounts
        val _ = check (source value count)
          ``closLang$Op None (WordOp (WordShiftVar ^sz ^sh))
              [Var None 0; Var None 1]``
        val sum =
          ``flatLang$App None (Src (Arith ast$Add (WordT ^sz)))
              [^count; flatLang$Lit None (^literal 1w)]``
        val _ = check (source value sum)
          ``closLang$Op None (WordOp (WordShiftVar ^sz ^sh))
              [Op None (WordOp (WordOpw ^sz Add)) [^one; Var None 0];
               Var None 1]``
        val _ = check (source value raised)
          ``closLang$Op None (WordOp (WordShiftVar ^sz ^sh))
              [^compiled_raise; Var None 1]``
        val _ = check (source raised ``flatLang$Lit None (^literal 1w)``)
          ``closLang$Op None (WordOp (WordShift ^sz ^sh 1)) [^compiled_raise]``
      in () end
  in app shift [``Lsl``, ``Lsr``, ``Asr``, ``Ror``] end;

val _ = check_width ``ast$W8`` ``ast$Word8`` 8 ``255n``
  ``closLang$Op None (IntOp (Const 1)) []``;

val _ = check_width ``ast$W64`` ``ast$Word64`` 64 ``18446744073709551615n``
  ``closLang$Op None (BlockOp (Constant (ConstWord64 1w))) []``;
