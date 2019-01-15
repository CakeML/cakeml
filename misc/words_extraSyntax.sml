(*
   Syntax of word test operation
*)

structure words_extraSyntax :> words_extraSyntax =
struct

local open words_extraTheory in end

open Abbrev HolKernel

val (word_test_tm, mk_word_test, dest_word_test, is_word_test) = HolKernel.syntax_fns2 "words_extra" "word_test"

end
