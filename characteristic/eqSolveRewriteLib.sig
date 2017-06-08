signature eqSolveRewriteLib =
sig
    include Abbrev
    val ELIM_UNKWN_CONV : term HOLset.set -> conv
end
