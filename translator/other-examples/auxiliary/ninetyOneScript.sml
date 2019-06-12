(*---------------------------------------------------------------------------
           McCarthy's 91 function.
 ---------------------------------------------------------------------------*)
open bossLib Theory Parse Tactic boolLib Lib
open TotalDefn numLib prim_recTheory arithmeticTheory;

val _ = new_theory "ninetyOne"

(*---------------------------------------------------------------------------
       Define the 91 function. We call it "N". We use Hol_defn to
       make the definition, since we have to tackle the termination
       proof ourselves.
 ---------------------------------------------------------------------------*)

val N_defn = Hol_defn "N" `N(x) = if x>100 then x-10 else N (N (x+11))`;

val [Neqn] = Defn.eqns_of N_defn;
val SOME Nind = Defn.ind_of N_defn;

val SOME N_aux_defn = Defn.aux_defn N_defn;
val SOME N_aux_ind = Defn.ind_of N_aux_defn;
val [E] = map DISCH_ALL (Defn.eqns_of N_aux_defn);

(*---------------------------------------------------------------------------
      Prove partial correctness for N, to see how such a proof
      works when the termination relation has not yet been supplied.
 ---------------------------------------------------------------------------*)

val Npartly_correct = Q.prove
(`WF R /\
  (!x. ~(x > 100) ==> R (N_aux R (x + 11)) x) /\
  (!x. ~(x > 100) ==> R (x + 11) x)
    ==>
  !n. N(n) = if n>100 then n-10 else 91`,
 STRIP_TAC THEN recInduct Nind
   THEN RW_TAC arith_ss []
   THEN ONCE_REWRITE_TAC [Neqn]
   THEN RW_TAC arith_ss []);

val N_aux_partial_correctness = Q.prove
(`WF R /\
  (!x. ~(x > 100) ==> R (N_aux R (x + 11)) x) /\
  (!x. ~(x > 100) ==> R (x + 11) x)
    ==>
  !n. N_aux R n = if n>100 then n-10 else 91`,
 STRIP_TAC THEN recInduct N_aux_ind
   THEN RW_TAC arith_ss []
   THEN RW_TAC arith_ss [E]);

(*---------------------------------------------------------------------------*)
(* Termination of 91 is a bit tricky.                                        *)
(*---------------------------------------------------------------------------*)

val lem = DECIDE ``~(x > 100) ==> (101-y < 101-x = x<y)``;

val unexpand_measure = Q.prove
(`(\x' x''. 101 < x' + (101 - x'') /\ x'' < 101) = measure \x. 101-x`,
 RW_TAC arith_ss [FUN_EQ_THM, measure_thm]);

(*---------------------------------------------------------------------------*)
(* Get the auxiliary rec. eqns, instantiate with termination relation, and   *)
(* do some simplifications.                                                  *)
(*---------------------------------------------------------------------------*)

val condE =
  SIMP_RULE arith_ss [AND_IMP_INTRO,WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [`R` |-> `measure \x. 101-x`] E);

val correctness' =
  SIMP_RULE arith_ss [WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [`R` |-> `measure \x. 101-x`] (N_aux_partial_correctness));

val N_aux_ind' = (* takes ages, because of subtraction? *)
  SIMP_RULE arith_ss [WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [`R` |-> `measure \x. 101-x`] (DISCH_ALL N_aux_ind));

(*---------------------------------------------------------------------------*)
(* Termination. This is done the hard way, to prop up an obscure point.      *)
(* We'll use NA to abbreviate the instantiated auxiliary function: thus      *)
(* NA = N_aux(measure($- 101)). The proof goes as follows:                   *)
(*                                                                           *)
(* Induct on the termination relation, then tidy up the goal, obtaining the  *)
(* goal "x < NA (x+11)". We now want to unroll NA(x+11). This requires       *)
(* manually instantiating the auxiliary fn with `x+11`, and proving its      *)
(* constraints. One of these is                                              *)
(*                                                                           *)
(*   x+11 < NA (x+22)           (%%)                                         *)
(*                                                                           *)
(* We will prove this by using the IH, by means of first doing a case split  *)
(* on "x+11 > 100". Having (%%) allows NA(x+11) to be unrolled, but we will  *)
(* also keep (%%) around for later use. Now  conditional rewriting will      *)
(* unroll "NA(x+11)" yielding the goal "x < NA(NA(x+22))". Now we want to    *)
(* unroll NA one more time, at its argument NA(x+22). Again we do a case     *)
(* split, this time on "NA (x+22) > 100". Consider the two branches coming   *)
(* from the case split.                                                      *)
(* Case: NA (x+22) > 100. The goal is easy to prove by arithmetic            *)
(*       from the assumptions and unrolling NA into the base case.           *)
(* Case: ~(NA (x+22) > 100). Here the IH may be used with a somewhat clever  *)
(*       witness to deliver                                                  *)
(*       NA(x+22) -11 < NA(NA(x+22) -11+11)                                  *)
(*                    = NA(NA(x+22))                                         *)
(*       After that, the proof of this branch is also easy.                  *)
(*---------------------------------------------------------------------------*)

val (N_def,N_ind) = Defn.tprove
 (N_defn,
  WF_REL_TAC `measure \x. 101 - x`
    THEN RW_TAC arith_ss [SUB_LEFT_LESS,unexpand_measure]
    THEN Q.ABBREV_TAC `NA = N_aux (measure (\x. 101 - x))`
    THEN measureInduct_on `(\m. 101 - m) x`
    THEN STRIP_TAC THEN FULL_SIMP_TAC arith_ss [lem]
    THEN MP_TAC (Q.INST [`x` |-> `x+11`] condE)
    THEN RW_TAC arith_ss []  (* implicit case split *)
    THEN `x+11 < NA(x+22)` by METIS_TAC[DECIDE``x<x+11``,DECIDE``x+11+11=x+22``]
    THEN RW_TAC std_ss [] THEN WEAKEN_TAC is_imp
    THEN MP_TAC (Q.INST [`x` |-> `NA(x+22)`] condE)
    THEN RW_TAC arith_ss [] (* implicit case split *)
    THEN `x < NA (x+22) - 11 /\ ~(NA (x + 22) - 11 > 100)` by DECIDE_TAC
    THEN `NA(x+22) - 11 < NA(NA(x+22) - 11 + 11)` by METIS_TAC[]
    THEN POP_ASSUM MP_TAC
    THEN FULL_SIMP_TAC arith_ss [DECIDE ``x+y < p ==> ((p-y)+y = p)``]);

val _ = save_thm ("N_def", N_def);
val _ = save_thm ("N_ind", N_ind);

Theorem N_correct:
 !x. N x = if x > 100 then x - 10 else 91
Proof
HO_MATCH_MP_TAC N_ind THEN
SRW_TAC [] [] THEN
ONCE_REWRITE_TAC [N_def] THEN
SRW_TAC [] [] THEN
DECIDE_TAC
QED

(*---------------------------------------------------------------------------
      Note that the above development is slightly cranky, since
      the partial correctness theorem has constraints remaining.
      These were addressed by the termination proof, but the
      constraints were proved and then thrown away.

      Now try some computations with N.
 ---------------------------------------------------------------------------*)

EVAL ``N 0``;
EVAL ``N 10``;
EVAL ``N 11``;
EVAL ``N 12``;
EVAL ``N 40``;
EVAL ``N 89``;
EVAL ``N 90``;
EVAL ``N 99``;
EVAL ``N 100``;
EVAL ``N 101``;
EVAL ``N 102``;
EVAL ``N 127``;

(* translation to MiniML *)

(* val _ = ml_translatorLib.translate N_def; *)

val _ = export_theory ()
