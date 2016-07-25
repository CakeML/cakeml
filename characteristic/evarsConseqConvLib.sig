signature evarsConseqConvLib =
sig

include Abbrev

type evars = term list

type term_with_evars = {
  term: term,
  evars: evars
}

type evars_instantiation = {
  instantiation: (term, term) subst,
  new_evars: evars
}

type evars_conseq_conv = term_with_evars -> evars_instantiation * thm

val match_mp_ecc : thm -> evars_conseq_conv

val then_ecc : evars_conseq_conv -> evars_conseq_conv -> evars_conseq_conv
val lift_conseq_conv_ecc : ConseqConv.conseq_conv -> evars_conseq_conv

val conj1_ecc : evars_conseq_conv -> evars_conseq_conv

(* applies on terms of the form ?x1..xn. P, where the evars_conseq_conv appliens
   on P *)
val ecc_conseq_conv : evars_conseq_conv -> ConseqConv.conseq_conv


(* Auxiliary functions, mostly useful for writing your own evars_conseq_conv *)

val term_subst_then :
  (term, term) subst -> (term, term) subst -> (term, term) subst

val all_new_evars : evars -> evars_instantiation -> evars

end
