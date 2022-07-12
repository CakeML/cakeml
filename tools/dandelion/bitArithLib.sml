(**
  Library implementing Karatsuba multiplication for the HOL4 evaluator
  based on the theorems in bitArithScript.sml
**)
structure bitArithLib =
struct
  open HolKernel Parse Theory arithmeticTheory realTheory
        boolLib bossLib; (* HOL4 dependencies *)
  open bitArithTheory; (* Theory dependencies *)

  (** A simple karatsuba conversion **)
  val karatsuba_lim = ref $ Arbnum.fromInt 200

  val mk_frac_thm = DB.find_all "mk_frac_thm" |> hd |> snd |> #1
  val id_thm = DB.find_all "id_thm" |> hd |> snd |> #1
  val mul_frac_thm = DB.find_all "mul_frac_thm" |> hd |> snd |> #1

  local
    val subst_let_conv = (REWR_CONV LET_THM THENC BETA_CONV)
    fun eval_let_conv c = RAND_CONV c THENC subst_let_conv
    fun rhs_fun_conv c = RIGHT_CONV_RULE $ RAND_CONV c
    fun karatsuba_rec_conv tm = let
      val bs1 = rand $ rator $ rand tm
      val bs2 = rand $ rand tm
      val len_bs1 = numSyntax.dest_numeral $ rhs o concl $ EVAL “LENGTH ^bs1”
      val len_bs2 = numSyntax.dest_numeral $ rhs o concl $ EVAL “LENGTH ^bs2”
      in
        if Arbnum.<(len_bs1,!karatsuba_lim) orelse Arbnum.<(len_bs2,!karatsuba_lim)
        then  (RAND_CONV EVAL) tm
        else let
      val _ = print "."
      val th = SPECL [bs1, bs2] karatsuba_bit
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let d = ... *)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let x1 = ... *)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let x0 = ... *)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let y1 = ... *)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let y0 = ... *)
      (** Ugly: Get rid of lets for mults **)
      val z0 = th |> rhs o concl |> rand |> rand
      val th = th |> rhs_fun_conv subst_let_conv (* inline z0 *)
      val z2 = th |> rhs o concl |> rand |> rand
      val th = th |> rhs_fun_conv subst_let_conv (* inline z2 *)
      (** Continue eval **)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let z1a = ... *)
      val th = th |> rhs_fun_conv (eval_let_conv EVAL) (* let z1b = ... *)
      (** Ugly: More inlining **)
      val z1Mul = th |> rhs o concl |> rand |> rand
      val th = th |> rhs_fun_conv subst_let_conv (* inline z1Mul *)
      val th = th |> rhs_fun_conv subst_let_conv (* inline z1Sub *)
      (** Now evaluate the terms we inlined **)
      val z0Eval = karatsuba_rec_conv “bleval ^z0” (* z0 *)
      val z2Eval = karatsuba_rec_conv “bleval ^z2” (* z2 *)
      val z1MulEval = karatsuba_rec_conv “bleval ^z1Mul” (* z1Mul **)
      (** Now first get down to ‘bleval (mul _ _)’ terms **)
      (** TODO: Prove a single rewriting theorem for this part in the needed shape and apply it with REWR_CONV **)
      val th2 = th |> REWRITE_RULE [add_thm, mulpow2_thm, sub_thm]
      val th3 = th2 |> REWRITE_RULE [z0Eval, z2Eval, z1MulEval]
  (** TODO: Use a single use theorem here too *)
      val th4 = th3 |> REWRITE_RULE [GSYM add_thm, GSYM mulpow2_thm, GSYM sub_thm]
      in
        th4 |> rhs_fun_conv EVAL
      end end;
  in
    fun karatsuba_conv tm =
        let val (arg1, arg2) = numSyntax.dest_mult tm
          val arg1_bval = ONCE_REWRITE_CONV [GSYM tobl_correct] arg1 |> RIGHT_CONV_RULE $ RAND_CONV EVAL
          val arg2_bval = ONCE_REWRITE_CONV [GSYM tobl_correct] arg2 |> RIGHT_CONV_RULE $ RAND_CONV EVAL
          val th = REWRITE_CONV [arg1_bval, arg2_bval] tm |> REWRITE_RULE [GSYM mul_thm]
          val karat = th |> RIGHT_CONV_RULE $ karatsuba_rec_conv
        in
          karat |> REWRITE_RULE [GSYM fromBL_correct] |> RIGHT_CONV_RULE EVAL
      end
  end;

  (** Now turn this into a conversion on reals **)
  local
    (* Apply conversion c to term tm if tm is not a negation,
       otherwise use its rand with RAND_CONV **)
    fun real_neg_app_conv c tm =
      if realSyntax.is_negated tm then RAND_CONV c tm else c tm
    fun app_karatsuba_conv tm =
      if not $ numSyntax.is_mult tm then REFL tm
      else karatsuba_conv tm
  in
  fun real_mul_conv tm =
    if not $ realSyntax.is_mult tm then raise UNCHANGED else
    let
      val _ = print "rmc ";
      val (lhsTm, rhsTm) = realSyntax.dest_mult tm
      val ((lnom, lden), rw_lhs_thm) =
        if realSyntax.is_div lhsTm
        then (realSyntax.dest_div lhsTm, SPEC lhsTm id_thm)
        else ((lhsTm, “1”), SPEC lhsTm mk_frac_thm)
      val ((rnom, rden), rw_rhs_thm) =
        if realSyntax.is_div rhsTm
        then (realSyntax.dest_div rhsTm, SPEC rhsTm id_thm)
        else ((rhsTm, “1”), SPEC rhsTm mk_frac_thm)
      val th = tm |> ONCE_REWRITE_CONV [rw_lhs_thm, rw_rhs_thm]
                |> RIGHT_CONV_RULE $ ONCE_REWRITE_CONV [mul_frac_thm]
      (* Before multiplying, simplify *)
      val th = th |> RIGHT_CONV_RULE $ REWRITE_CONV [mult_ints, MULT_CLAUSES]
      val thKaratsuba_nom = th
        |> RIGHT_CONV_RULE $ RATOR_CONV $ RAND_CONV $ real_neg_app_conv $
              RAND_CONV app_karatsuba_conv
      val thKaratsuba_denom = thKaratsuba_nom
        |> RIGHT_CONV_RULE $ RAND_CONV $ real_neg_app_conv $ RAND_CONV app_karatsuba_conv
    in
      thKaratsuba_denom
    end
  end;

  val _ =
    (* record the library as a dependency for future theories *)
    (Theory.add_ML_dependency "bitArithLib";
      (*Theory.adjoin_to_theory
        {sig_ps = NONE,
          struct_ps =
            SOME(fn _ => PP.add_string "val _ = bitArithLib.use_karatsuba();")}; *)
      (* Remove old definitions of multiplication for reals and nums *)
      computeLib.del_consts [“($*):real->real->real”, “($*):num->num->num”];
      (* Add karatsuba multiplication as conversion for reals and nums *)
      computeLib.add_convs [(“($*):real->real->real”,2, real_mul_conv),
                            (“($*):num->num->num”, 2, karatsuba_conv)])

end
