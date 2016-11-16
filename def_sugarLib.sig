signature def_sugarLib =
sig
    include Abbrev

    val otherwise_homomorphic : term -> term
    val ||> : term quotation * (term -> term) -> term quotation
end
