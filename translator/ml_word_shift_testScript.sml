(*
  Translator regression tests for binary word shifts and word conversions.
*)
Theory ml_word_shift_test[no_sig_docs]
Ancestors
  ml_translator
Libs
  preamble ml_translatorLib

fun is_shift_app tm =
  case total astSyntax.dest_App tm of
    NONE => false
  | SOME (oper, _) =>
      can (match_term ``Arith (Shift sh) (WordT sz)``) oper;

fun check_shift_app tm =
  let
    val shape =
      can (match_term
        ``App (Arith (Shift sh) (WordT W8)) [v; Lit (Word8 n)]``) tm orelse
      can (match_term
        ``App (Arith (Shift sh) (WordT W64)) [v; Lit (Word64 n)]``) tm
    val _ = if shape then ()
            else raise Fail ("Malformed translated shift: " ^ term_to_string tm)
    val args = snd (astSyntax.dest_App tm) |> listSyntax.dest_list |> fst
    val amount = List.nth (args, 1) |> astSyntax.dest_Lit |> rand
    val _ = wordsSyntax.dest_word_literal amount
      handle HOL_ERR _ => raise Fail
        ("Nonconstant translated shift amount: " ^ term_to_string tm)
  in () end;

fun check expect_shift expr =
  let
    val th = hol2deep expr |> PROVE_HYP TRUTH
    val _ = if null (hyp th) then ()
            else raise Fail ("Unexpected translation precondition: " ^
                             term_to_string expr)
    val code = rand (rator (concl th))
    val shifts = find_terms is_shift_app code
    val _ = if expect_shift andalso null shifts then
              raise Fail ("No translated shift: " ^ term_to_string expr)
            else ()
  in app check_shift_app shifts end;

val widths = [(1, ``:1``), (7, ``:7``), (8, ``:8``),
              (9, ``:9``), (64, ``:64``)];
val shifts = [wordsSyntax.mk_word_lsl, wordsSyntax.mk_word_lsr,
              wordsSyntax.mk_word_asr];
val numeral = numSyntax.mk_numeral o Arbnum.fromInt;

val _ = app (fn (width, dim) =>
  let
    val word = mk_var ("w", wordsSyntax.mk_word_type dim)
    val amounts = map numeral [0, 1, width - 1, width, width + 1, 256] @
                  [``18446744073709551616n``, ``18446744073709551617n``]
    val operations = if width = 8 orelse width = 64 then
                       wordsSyntax.mk_word_ror :: shifts
                     else shifts
  in
    app (fn oper => app (fn amount =>
      check true (mk_abs (word, oper (word, amount)))) amounts) operations
  end) widths;

fun check_variable_shift sz sh expr =
  let
    val th = hol2deep expr |> PROVE_HYP TRUTH
    val _ = if null (hyp th) then ()
            else raise Fail ("Variable shift has a translation precondition: " ^
              term_to_string expr ^ "\n" ^
              String.concatWith "\n" (map term_to_string (hyp th)))
    val code = rand (rator (concl th))
    val shift = case find_terms is_shift_app code of
                  [tm] => tm
                | _ => raise Fail "Expected exactly one variable shift"
    val (oper, args) = astSyntax.dest_App shift
    val args = fst (listSyntax.dest_list args)
    val _ = if oper ~~ ``Arith (Shift ^sh) (WordT ^sz)`` andalso
               length args = 2 then ()
            else raise Fail "Incorrect variable shift operation"
    val (conversion, _) = astSyntax.dest_App (List.nth (args, 1))
    val _ = if conversion ~~ ``FromTo IntT (WordT ^sz)`` then ()
            else raise Fail "Variable shift count is not converted to a word"
  in () end;

val variable_shifts =
  [(``Lsl``, wordsSyntax.mk_word_lsl), (``Lsr``, wordsSyntax.mk_word_lsr),
   (``Asr``, wordsSyntax.mk_word_asr), (``Ror``, wordsSyntax.mk_word_ror)];

val _ = app (fn (sz, dim) =>
  let
    val word = mk_var ("w", wordsSyntax.mk_word_type dim)
    val amount = mk_var ("n", ``:num``)
    val amounts = [amount, ``^amount + 18446744073709551616``]
  in
    app (fn (sh, oper) => app (fn count =>
      check_variable_shift sz sh
        (mk_abs (word, mk_abs (amount, oper (word, count))))) amounts)
      variable_shifts
  end) [(``W8``, ``:8``), (``W64``, ``:64``)];

val _ = app (fn (_, dim) =>
  let
    val word = mk_var ("w", wordsSyntax.mk_word_type dim)
    val nat = mk_var ("n", ``:num``)
    val int = mk_var ("i", ``:int``)
  in
    check false (mk_abs (word, wordsSyntax.mk_w2n word));
    check false (mk_abs (word, integer_wordSyntax.mk_w2i word));
    check false (mk_abs (nat, wordsSyntax.mk_n2w (nat, dim)));
    check false (mk_abs (int, integer_wordSyntax.mk_i2w (int, dim)));
    app (fn (_, dest) =>
      check false (mk_abs (word, wordsSyntax.mk_w2w (word, dest)))) widths
  end) widths;

(* Shifts by a word-valued amount (word_lsl_bv, word_lsr_bv, word_asr_bv,
   and word_ror_bv for word8 and word64) *)
fun check_bv_shift sh expr =
  let
    val th = hol2deep expr |> PROVE_HYP TRUTH
    val _ = if null (hyp th) then ()
            else raise Fail ("Word-amount shift has a translation precondition: " ^
                             term_to_string expr)
    val code = rand (rator (concl th))
    fun is_var_shift tm =
      is_shift_app tm andalso
      (let val (oper, args) = astSyntax.dest_App tm
           val amount = List.nth (fst (listSyntax.dest_list args), 1)
       in oper ~~ ``Arith (Shift ^sh) (WordT W8)`` orelse
          oper ~~ ``Arith (Shift ^sh) (WordT W64)`` end
       andalso not (astSyntax.is_Lit
                      (List.nth (fst (listSyntax.dest_list
                                        (snd (astSyntax.dest_App tm))), 1))))
    val _ = case find_terms is_var_shift code of
              [_] => ()
            | _ => raise Fail ("Expected exactly one word-amount shift: " ^
                               term_to_string expr)
    val _ = app check_shift_app
              (filter (not o is_var_shift) (find_terms is_shift_app code))
  in () end;

val bv_shifts =
  [(``Lsl``, wordsSyntax.mk_word_lsl_bv), (``Lsr``, wordsSyntax.mk_word_lsr_bv),
   (``Asr``, wordsSyntax.mk_word_asr_bv)];

val _ = app (fn (width, dim) =>
  let
    val word = mk_var ("w", wordsSyntax.mk_word_type dim)
    val amount = mk_var ("n", wordsSyntax.mk_word_type dim)
    val ops = if width = 8 orelse width = 64 then
                (``Ror``, wordsSyntax.mk_word_ror_bv) :: bv_shifts
              else bv_shifts
  in
    app (fn (sh, oper) =>
      check_bv_shift sh (mk_abs (word, mk_abs (amount, oper (word, amount)))))
      ops
  end) widths;
