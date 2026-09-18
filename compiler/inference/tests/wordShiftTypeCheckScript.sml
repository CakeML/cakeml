(*
  Type inference and cv_eval regression tests for binary word shifts.
*)
Theory wordShiftTypeCheck[no_sig_docs]
Ancestors
  infer_cv
Libs
  preamble cv_transLib

val _ = cv_auto_trans inferTheory.init_config_def;
val _ = cv_trans locationTheory.unknown_loc_def;

fun infer_expr expr =
  rhs (concl (cv_eval
    ``infertype_prog init_config [Dlet unknown_loc (Pvar «shifted») ^expr]``))
  handle cv_repLib.NeedsTranslation (_, tm) =>
    raise Fail ("Word-shift test needs CV translation of: " ^ term_to_string tm);

fun check_success expected expr =
  let
    val result = infer_expr expr
    val _ = if can (match_term ``M_success _``) result then ()
            else raise Fail ("Word-shift inference failed: " ^ term_to_string result)
    val env = rand result
    val check = EVAL
      ``nsLookup (^env).inf_v (Short «shifted») =
        SOME (0, Infer_Tapp [] ^expected)``
  in
    if rhs (concl check) ~~ ``T`` then ()
    else raise Fail ("Incorrect word-shift type: " ^ term_to_string result)
  end;

fun check_failure expr =
  let val result = infer_expr expr in
    if can (match_term ``M_failure _``) result then ()
    else raise Fail ("Ill-typed word shift accepted: " ^ term_to_string expr)
  end;

val shifts = [``Lsl``, ``Lsr``, ``Asr``, ``Ror``];
val word_types =
  [(``W8``, ``Word8``, ``Tword8_num``, ``Lit (Word64 1w)``),
   (``W64``, ``Word64``, ``Tword64_num``, ``Lit (Word8 1w)``)];

val _ = app (fn sh => app (fn (sz, lit, expected, wrong_word) =>
  let
    val oper = ``Arith (Shift ^sh) (WordT ^sz)``
    val one = ``Lit (^lit 1w)``
    val two = ``Lit (^lit 2w)``
    val value = ``Lit (^lit 129w)``
  in
    check_success expected ``App ^oper [^value; ^one]``;
    check_success expected
      ``Let (SOME «amount») (App (Arith Add (WordT ^sz)) [^one; ^two])
          (App ^oper [^value; Var (Short «amount»)])``;
    check_failure ``App ^oper [^value]``;
    check_failure ``App ^oper [^value; ^one; ^two]``;
    check_failure ``App ^oper [^value; ^wrong_word]``;
    check_failure ``App ^oper [^value; Lit (IntLit 1)]``
  end) word_types) shifts;

val _ = app (fn sh =>
  check_failure
    ``App (Arith (Shift ^sh) IntT) [Lit (IntLit 129); Lit (IntLit 1)]``)
  shifts;
