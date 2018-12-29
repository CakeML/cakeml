(*
  Tests of compset for evaluating lex_fun calls. Note that lex_fun isn't used
  in the compiler; there the equivalent lex_impl is used.
*)
open preamble
open lexer_funTheory
open testutils semanticsComputeLib


val _ = new_theory "lexfuncomputeTests"

val _ = temp_overload_on ("tlex", ``λs. MAP FST (lexer_fun s)``)

fun limit n cs t =
    let
      open computeLib
      val c = ref n
      fun stop t = if !c <= 0 then true else (c := !c - 1; false)
    in
      with_flag(stoppers, SOME stop) (CBV_CONV cs) t
    end

val compset = let
  val cs = listLib.list_compset()
in
  stringLib.add_string_compset cs;
  pairLib.add_pair_compset cs;
  optionLib.OPTION_rws cs;
  combinLib.add_combin_compset cs;
  computeLib.add_thms[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] cs;
  numposrepLib.add_numposrep_compset cs;
  bitLib.add_bit_compset cs;
  ASCIInumbersLib.add_ASCIInumbers_compset cs;
  intReduce.add_int_compset cs;
  add_lex_fun_compset cs;
  cs
end

fun test (t_in,t_expected) =
    (tprint ("Lexing " ^ term_to_string t_in);
     require_msg (check_result (aconv t_expected)) term_to_string
                 (rhs o concl o computeLib.CBV_CONV compset)
                 t_in)

val _ = app (ignore o test) [
      (“tlex "y = \"foo\" andalso z < 6;"”,
       “[AlphaT "y"; EqualsT; StringT "foo"; AndalsoT; AlphaT "z"; SymbolT "<";
        IntT 6; SemicolonT]”),
      (* (“tlex "val value = 0x10"”,
       “[ValT; IdentT "value"; EqualsT; IntT 16]”) *)
      (“tlex "val value = 0 *y - ~1"”,
       “[ValT; AlphaT "value"; EqualsT; IntT 0; StarT; AlphaT "y"; SymbolT "-";
         IntT (-1)]”),
      (“tlex "val value = 0 *y - ~a"”,
       “[ValT; AlphaT "value"; EqualsT; IntT 0; StarT; AlphaT "y"; SymbolT "-";
         SymbolT "~"; AlphaT "a"]”)
    ]

val _ = export_theory()
