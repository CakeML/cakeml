signature cfNormaliseLib =
sig
   include Abbrev

   val strip_annot_exp : term -> term
   val strip_annot_decl : term -> term
   val strip_annot_prog : term -> term

   val normalise_exp : term -> term
   val normalise_decl : term -> term
   val normalise_prog : term -> term

end
