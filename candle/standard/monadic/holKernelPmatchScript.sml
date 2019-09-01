(*
  This file proves alternative definitions of those HOL kernel
  functions that have complex pattern matching. The new definitions
  use PMATCH-based case expressions instead of HOL's standard
  per-datatype case constants.
*)
open preamble
open patternMatchesLib patternMatchesSyntax patternMatchesTheory
open ml_monadBaseTheory holKernelTheory

val _ = new_theory"holKernelPmatch"
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_overload_on ("raise_clash", ``raise_Clash``);
val _ = temp_overload_on ("handle_clash", ``handle_Clash``);

val _ = hide "state";

Type M = ``: hol_refs -> ('a, hol_exn) exc # hol_refs``

(* TODO: stolen from deepMatchesLib.sml; should be exported? *)
val PAIR_EQ_COLLAPSE = Q.prove (
`(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))`,
Cases_on `x` THEN SIMP_TAC std_ss [] THEN METIS_TAC[])

val pabs_elim_ss =
    simpLib.conv_ss
      {name  = "PABS_ELIM_CONV",
       trace = 2,
       key   = SOME ([],``UNCURRY (f:'a -> 'b -> bool)``),
       conv  = K (K pairTools.PABS_ELIM_CONV)}

val select_conj_ss =
    simpLib.conv_ss
      {name  = "SELECT_CONJ_SS_CONV",
       trace = 2,
       key   = SOME ([],``$@ (f:'a -> bool)``),
       conv  = K (K (SIMP_CONV (std_ss++boolSimps.CONJ_ss) []))};

val static_ss = simpLib.merge_ss
  [pabs_elim_ss,
   pairSimps.paired_forall_ss,
   pairSimps.paired_exists_ss,
   pairSimps.gen_beta_ss,
   select_conj_ss,
   elim_fst_snd_select_ss,
   boolSimps.EQUIV_EXTRACT_ss,
   simpLib.rewrites [
     some_var_bool_T, some_var_bool_F,
     GSYM boolTheory.F_DEF,
     pairTheory.EXISTS_PROD,
     pairTheory.FORALL_PROD,
     PMATCH_ROW_EQ_NONE,
     PMATCH_ROW_COND_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]];

fun rc_ss gl = srw_ss() ++ simpLib.merge_ss (static_ss :: gl)
(* -- *)

fun fix def name rwth =
  def |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(REWR_CONV rwth)))
      |> curry save_thm name

val monadtac =
  simp[FUN_EQ_THM,st_ex_bind_def] >> gen_tac

val tac =
  BasicProvers.PURE_CASE_TAC >>
  FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def,
    PMATCH_INCOMPLETE_def]

val () = ENABLE_PMATCH_CASES();

val codomain_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL holSyntaxTheory.codomain_raw))) =
    case ty of Tyapp n (y::x::xs) => x | _ => ty`,
  rpt tac)
val res = fix holSyntaxTheory.codomain_raw "codomain_def" codomain_PMATCH

val rev_assocd_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL rev_assocd_def))) =
    case l of
       (x,y)::l1 => if y = a then x else rev_assocd a l1 d
     | _ => d`,
  rpt tac)
val res = fix rev_assocd_def "rev_assocd_def" rev_assocd_PMATCH

val type_of_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL type_of_def))) =
    case tm of
    | Var _ ty => return ty
    | Const _ ty => return ty
    | Comb s _
        => do ty <- type_of s ;
              x <- dest_type ty ;
              case x of | (_,_::ty1::_) => return ty1
                        | _ => failwith (strlit "match")
           od
    | Abs (Var _ ty) t
        => do x <- type_of t; mk_fun_ty ty x od
    | _ => failwith (strlit "match")`,
  monadtac >> rpt tac)
val res = fix type_of_def "type_of_def" type_of_PMATCH

val raconv_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL raconv_def))) =
    case (tm1,tm2) of
    | (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2)
        => raconv env s1 s2 ∧ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2)
        => (case (v1,v2) of
            | (Var n1 ty1,Var n2 ty2)
                => (ty1 = ty2) ∧ raconv ((v1,v2)::env) t1 t2
            | _ => F)
    | _ => F`,
  rpt tac)
val res = fix raconv_def "raconv_def" raconv_PMATCH

val is_var_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL is_var_def))) =
    case x of (Var _ _) => T | _ => F`,
  rpt tac)
val res = fix is_var_def "is_var_def" is_var_PMATCH

val is_const_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL is_const_def))) =
    case x of (Const _ _) => T | _ => F`,
  rpt tac)
val res = fix is_const_def "is_const_def" is_const_PMATCH

val is_abs_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL is_abs_def))) =
    case x of (Abs _ _) => T | _ => F`,
  rpt tac)
val res = fix is_abs_def "is_abs_def" is_abs_PMATCH

val is_comb_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL is_comb_def))) =
    case x of (Comb _ _) => T | _ => F`,
  rpt tac)
val res = fix is_comb_def "is_comb_def" is_comb_PMATCH

val mk_abs_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL mk_abs_def))) =
    case bvar of Var n ty => return (Abs bvar bod)
    | _ => failwith (strlit "mk_abs: not a variable")`,
  rpt tac)
val res = fix mk_abs_def "mk_abs_def" mk_abs_PMATCH

val mk_comb_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL mk_comb_def))) =
    do tyf <- type_of f ;
       tya <- type_of a ;
       case tyf of
         Tyapp (strlit "fun") [ty;_] => if tya = ty then return (Comb f a) else
                                 failwith (strlit "mk_comb: types do not agree")
       | _ => failwith (strlit "mk_comb: types do not agree")
    od`,
  monadtac >> rpt tac)
val res = fix mk_comb_def "mk_comb_def" mk_comb_PMATCH

val dest_var_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL dest_var_def))) =
    case tm of Var s ty => return (s,ty)
            | _ => failwith (strlit "dest_var: not a variable")`,
  rpt tac)
val res = fix dest_var_def "dest_var_def" dest_var_PMATCH

val dest_const_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL dest_const_def))) =
    case tm of Const s ty => return (s,ty)
            | _ => failwith (strlit "dest_const: not a constant")`,
  rpt tac)
val res = fix dest_const_def "dest_const_def" dest_const_PMATCH

val dest_comb_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL dest_comb_def))) =
    case tm of Comb f x => return (f,x)
            | _ => failwith (strlit "dest_comb: not a combination")`,
  rpt tac)
val res = fix dest_comb_def "dest_comb_def" dest_comb_PMATCH

val dest_abs_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL dest_abs_def))) =
    case tm of Abs v b => return (v,b)
            | _ => failwith (strlit "dest_abs: not an abstraction")`,
  rpt tac)
val res = fix dest_abs_def "dest_abs_def" dest_abs_PMATCH

val vfree_in_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL holSyntaxExtraTheory.vfree_in_def))) =
    case tm of
    | Abs bv bod => v <> bv ∧ vfree_in v bod
    | Comb s t => vfree_in v s ∨ vfree_in v t
    | _ => tm = v`,
  rpt tac)
val res = fix holSyntaxExtraTheory.vfree_in_def "vfree_in_def" vfree_in_PMATCH

val rator_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL rator_def))) =
    case tm of
      Comb l r => return l
    | _ => failwith (strlit "rator: Not a combination")`,
  rpt tac)
val res = fix rator_def "rator_def" rator_PMATCH

val rand_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL rand_def))) =
    case tm of
      Comb l r => return r
    | _ => failwith (strlit "rand: Not a combination")`,
  rpt tac)
val res = fix rand_def "rand_def" rand_PMATCH

val dest_eq_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL dest_eq_def))) =
    case tm of
      Comb (Comb (Const (strlit "=") _) l) r => return (l,r)
    | _ => failwith (strlit "dest_eq")`,
  rpt tac)
val res = fix dest_eq_def "dest_eq_def" dest_eq_PMATCH

val is_eq_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL is_eq_def))) =
    case tm of
      Comb (Comb (Const (strlit "=") _) l) r => T
    | _ => F`,
  rpt tac)
val res = fix is_eq_def "is_eq_def" is_eq_PMATCH

val TRANS_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL TRANS_def))) =
    case (c1,c2) of
      (Comb (Comb (Const (strlit "=") _) l) m1, Comb (Comb (Const (strlit "=") _) m2) r) =>
        if aconv m1 m2 then do eq <- mk_eq(l,r);
                               return (Sequent (term_union asl1 asl2) eq) od
        else failwith (strlit "TRANS")
    | _ => failwith (strlit "TRANS")`,
  rpt tac)
val res = fix TRANS_def "TRANS_def" TRANS_PMATCH

val MK_COMB_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL MK_COMB_def))) =
   case (c1,c2) of
     (Comb (Comb (Const (strlit "=") _) l1) r1, Comb (Comb (Const (strlit "=") _) l2) r2) =>
       do x1 <- mk_comb(l1,l2) ;
          x2 <- mk_comb(r1,r2) ;
          eq <- mk_eq(x1,x2) ;
          return (Sequent(term_union asl1 asl2) eq) od
   | _ => failwith (strlit "MK_COMB")`,
  rpt tac)
val res = fix MK_COMB_def "MK_COMB_def" MK_COMB_PMATCH

val ABS_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL ABS_def))) =
    case c of
      Comb (Comb (Const (strlit "=") _) l) r =>
        if EXISTS (vfree_in v) asl
        then failwith (strlit "ABS: variable is free in assumptions")
        else do a1 <- mk_abs(v,l) ;
                a2 <- mk_abs(v,r) ;
                eq <- mk_eq(a1,a2) ;
                return (Sequent asl eq) od
    | _ => failwith (strlit "ABS: not an equation")`,
  BasicProvers.CASE_TAC >> rpt tac)
val res = fix ABS_def "ABS_def" ABS_PMATCH

val BETA_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL BETA_def))) =
    case tm of
      Comb (Abs v bod) arg =>
        if arg = v then do eq <- mk_eq(tm,bod) ; return (Sequent [] eq) od
        else failwith (strlit "BETA: not a trivial beta-redex")
    | _ => failwith (strlit "BETA: not a trivial beta-redex")`,
  rpt tac)
val res = fix BETA_def "BETA_def" BETA_PMATCH

val EQ_MP_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL EQ_MP_def))) =
    case eq of
      Comb (Comb (Const (strlit "=") _) l) r =>
        if aconv l c then return (Sequent (term_union asl1 asl2) r)
                     else failwith (strlit "EQ_MP")
    | _ => failwith (strlit "EQ_MP")`,
  rpt tac)
val res = fix EQ_MP_def "EQ_MP_def" EQ_MP_PMATCH

val SYM_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL SYM_def))) =
    case eq of
      Comb (Comb (Const (strlit "=") t) l) r =>
        return (Sequent asl (Comb (Comb (Const (strlit "=") t) r) l))
    | _ => failwith (strlit "SYM")`,
  rpt tac)
val res = fix SYM_def "SYM_def" SYM_PMATCH

val _ = export_theory()
