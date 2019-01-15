signature words_extraSyntax =
sig

   include Abbrev

   val word_test_tm : term
   val dest_word_test : term -> term * term
   val is_word_test : term -> bool
   val mk_word_test : term * term -> term
end
