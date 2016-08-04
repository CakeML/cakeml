signature cfHeapsLib =
sig
  include Abbrev
  type conseq_conv = ConseqConv.conseq_conv
  type directed_conseq_conv = ConseqConv.directed_conseq_conv

  val dest_F_pre_post : term -> term * term * term
  val F_pre_post_conv : conv -> conv -> conv

  (** [hclean] *)

  (* the thm list argument is some "context" that may contain some
     [is_local F] theorems; useful in particular to use the
     assumptions, when bundling the conseq_convs in a tactic *)

  val hclean_one_conseq_conv : thm list -> directed_conseq_conv
  val hclean_conseq_conv : thm list -> directed_conseq_conv

  val hclean_one : tactic
  val hclean : tactic

  (** [hchange] *)

  val hchange_conseq_conv : thm -> directed_conseq_conv
  val hchanges_conseq_conv : thm -> directed_conseq_conv

  val hchange_top : thm -> tactic
  val hchanges_top : thm -> tactic

  val hchange : thm -> tactic
  val hchanges : thm -> tactic
end
