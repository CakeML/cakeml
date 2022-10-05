(**
  Library to convert between real-valued and rational-valued
  FloVer expressions
**)
structure expressionsLib = struct

  open HolKernel Parse Abbrev ExpressionsTheory;
  open RealArith realTheory realLib integerTheory intLib bossLib;

  exception FloVerException of string;

  val fvar_tm     = “Expressions$Var”
  val fconst_tm   = “Expressions$Const”
  val unop_tm     = “Expressions$Unop”
  val bop_tm      = “Expressions$Binop”
  val fma_tm      = “Expressions$Fma”
  val downcast_tm = “Expressions$Downcast”

  local fun err s = FloVerException ("Not a FloVer " ^ s) in
  val dest_fvar     = HolKernel.dest_monop fvar_tm     $ err "var"
  val dest_fconst   = HolKernel.dest_binop fconst_tm    $ err "const"
  val dest_unop     = HolKernel.dest_binop unop_tm     $ err "unop"
  val dest_bop      = HolKernel.dest_triop bop_tm      $ err "bop"
  val dest_fma      = HolKernel.dest_triop fma_tm      $ err "fma"
  val dest_downcast = HolKernel.dest_binop downcast_tm $ err "downcast"
  end;

  local fun getArgTy t = type_of t |> dest_type |> snd |> hd in
  fun mk_fvar ty n = mk_comb (fvar_tm, n) |> inst [alpha |-> ty]
  fun mk_fconst m c = list_mk_comb (inst [alpha |-> type_of c] fconst_tm, [m, c])
  fun mk_unop u e =
    list_mk_comb (inst [alpha |-> getArgTy e] unop_tm, [u, e])
  fun mk_bop b e1 e2 =
    list_mk_comb (inst [alpha |-> getArgTy e1] bop_tm, [b, e1, e2])
  fun mk_fma e1 e2 e3 =
    list_mk_comb (inst [alpha |-> getArgTy e1] fma_tm, [e1, e2, e3])
  fun mk_downcast m e =
    list_mk_comb (inst [alpha |-> getArgTy e] downcast_tm, [m, e])
  end;

  val is_fvar     = can dest_fvar
  val is_fconst   = can dest_fconst
  val is_unop     = can dest_unop
  val is_bop      = can dest_bop
  val is_fma      = can dest_fma
  val is_downcast = can dest_downcast

  fun realExp2ratExp (t:term) :term =
    if type_of t = “:real expr” then
      if is_fvar t then let
        val var = dest_fvar t in
        mk_fvar “:(int # int)” var end
      else if is_fconst t then let
        val (m,cst) = dest_fconst t
        val (n,d) =
          if realSyntax.is_div cst then
            realSyntax.dest_div cst
          else raise FloVerException ("Not a rational number" ^ (term_to_string cst))
        val ni =
          if realSyntax.is_real_literal n then
            intSyntax.term_of_int $ realSyntax.int_of_term n
          else raise FloVerException "Nominator not constant"
        val di =
          if realSyntax.is_real_literal d then
            intSyntax.term_of_int $ realSyntax.int_of_term d
          else raise FloVerException "Denominator not constant"
        in
          mk_fconst m (Parse.Term ‘(^ni, ^di)’) end
      else if is_unop t then let
        val (uop, e) = dest_unop t in
        mk_unop uop (realExp2ratExp e) end
      else if is_bop t then let
        val (bop, e1, e2) = dest_bop t in
        mk_bop bop (realExp2ratExp e1) (realExp2ratExp e2) end
      else if is_fma t then let
        val (e1, e2, e3) = dest_fma t in
        mk_fma (realExp2ratExp e1) (realExp2ratExp e2) (realExp2ratExp e3) end
      else if is_downcast t then let
        val (m, e) = dest_downcast t in
        mk_downcast m (realExp2ratExp e) end
      else raise FloVerException ("Unsupported expression constructor in" ^ (term_to_string t))
    else raise FloVerException "Not a real-valued expression";

  fun realExp2ratExpConv t =
    let val t_rat = realExp2ratExp t in
      EVAL “^t = ratExp2realExp ^t_rat” |> Rewrite.REWRITE_RULE [boolTheory.EQ_CLAUSES]
    end;

end;
