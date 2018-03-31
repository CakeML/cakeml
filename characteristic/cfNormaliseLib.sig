signature cfNormaliseLib =
sig
   include Abbrev

   val normalise_exp : term -> term
   val normalise_decl : term -> term
   val normalise_prog : term -> term

end
