open HolKernel boolLib bossLib lcsymtacs
open Parse deepMatchesLib deepMatchesSyntax deepMatchesTheory
open holKernelTheory monadsyntax

val _ = new_theory"holKernelPmatch"

(* This file proves alternative definitions of those HOL kernel functions that
have complex pattern matching. The new definitions use PMATCH-based case
expressions instead of HOL's standard per-datatype case constants *)

val _ = temp_overload_on ("monad_bind", ``ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``ex_return``);

(* TODO: stolen from deepMatchesLib.sml; should be exported? *)
val PAIR_EQ_COLLAPSE = prove (
``(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))``,
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

val tac =
  BasicProvers.PURE_CASE_TAC >>
  FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def,
    PMATCH_INCOMPLETE_def]

val () = set_trace"parse deep cases"1

val type_of_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL type_of_def))) =
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
    | _ => failwith (strlit "match")``,
  simp[FUN_EQ_THM,ex_bind_def] >> gen_tac >>
  rpt tac)
val res = fix type_of_def "type_of_def" type_of_PMATCH

val raconv_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL raconv_def))) =
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
    | _ => F``,
  rpt tac)
val res = fix raconv_def "raconv_def" raconv_PMATCH

val is_var_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL is_var_def))) =
    case x of (Var _ _) => T | _ => F``,
  rpt tac)
val res = fix is_var_def "is_var_def" is_var_PMATCH

val is_const_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL is_const_def))) =
    case x of (Const _ _) => T | _ => F``,
  rpt tac)
val res = fix is_const_def "is_const_def" is_const_PMATCH

val is_abs_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL is_abs_def))) =
    case x of (Abs _ _) => T | _ => F``,
  rpt tac)
val res = fix is_abs_def "is_abs_def" is_abs_PMATCH

val is_comb_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL is_comb_def))) =
    case x of (Comb _ _) => T | _ => F``,
  rpt tac)
val res = fix is_comb_def "is_comb_def" is_comb_PMATCH

val mk_abs_PMATCH = prove(
  ``^(rhs(concl(SPEC_ALL mk_abs_def))) =
    case bvar of Var n ty => return (Abs bvar bod)
    | _ => failwith (strlit "mk_abs: not a variable")``,
  rpt tac)
val res = fix mk_abs_def "mk_abs_def" mk_abs_PMATCH

val _ = export_theory()
