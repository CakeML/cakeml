
open HolKernel Parse boolLib bossLib;

val _ = new_theory "holSemantics";

open holSyntaxTheory;
open sholSyntaxTheory;
open sholSemanticsTheory;
open listTheory arithmeticTheory combinTheory pairTheory;

(*

   This script defines the semantics of stateful HOL in terms of the
   semantics of the stateless HOL. This file has three parts:

    (1) a translation from stateful types, terms, sequents to
        stateless types, terms and sequents is define as a relation,

    (2) the semantics of stateful sequents is define in using the
        translation relation from above, and

    (3) finally, we prove that for any derivation in the stateful
        version there is a derivation in the stateless version for
        the appropriate translation of the sequent.

   Parts (2) and (3) imply soundness of stateful HOL, if soundness has
   been proved for the stateless version.

*)

infix \\
val op \\ = op THEN;

(* -- part 1 -- *)

val const_def_def = Define `
  const_def n defs =
    case defs of
    | [] => NONE
    | (Constdef name tm::defs) =>
         if n = name then SOME (0,tm) else const_def n defs
    | (Typedef name tm abs rep::defs) =>
         if n = abs then SOME (1,tm) else
         if n = rep then SOME (2,tm) else const_def n defs
    | d::defs => const_def n defs`

val type_def_def = Define `
  type_def n defs =
    case defs of
    | [] => NONE
    | (Typedef name tm x y::defs) =>
         if n = name then SOME (tm,x,y) else type_def n defs
    | d::defs => type_def n defs`;

val (term_rules,term_ind,term_cases) = xHol_reln "term" `
  (type defs (Tyvar s) (Tyvar s)) /\
  (type defs Bool (Tyapp (Typrim "bool" 0) [])) /\
  (type defs Ind (Tyapp (Typrim "ind" 0) [])) /\
  (type defs tx tx1 /\ type defs ty ty1 ==>
   type defs (Fun tx ty) (Tyapp (Typrim "->" 2) [tx1; ty1])) /\
  (EVERY2 (type defs) tys tys1 /\
   (type_def s defs = SOME (tm,abs,rep)) /\ term defs tm tm1 ==>
   type defs (Tyapp s tys) (Tyapp (Tydefined s tm1) tys1)) /\
  (type defs ty ty1 ==>
   term defs (Var s ty) (Var s ty1)) /\
  (type defs (Fun ty (Fun ty Bool)) ty1 ==>
   term defs (Equal ty) (Const "=" ty1 Prim)) /\
  (type defs (Fun (Fun ty Bool) ty) ty1 ==>
   term defs (Select ty) (Const "@" ty1 Prim)) /\
  (term defs x x1 /\ term defs y y1 ==>
   term defs (Comb x y) (Comb x1 y1)) /\
  (type defs ty ty1 /\ term defs x x1 ==>
   term defs (Abs s ty x) (Abs s ty1 x1)) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (n,tm)) /\ term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (if n = 0 then Defined tm1 else
                                        if n = 1 then Tyabs s tm1 else
                                     (* if n = 2 then *) Tyrep s tm1)))`

val seq_trans_def = Define `
  seq_trans ((defs,h),c) (h1,c1) <=>
    EVERY2 (term defs) h h1 /\ term defs c c1`;


(* -- part 2 -- *)

(*
val hol_seq_def = Define `
  hol_seq ((defs,hyps),tm) = ?h c. seq_trans ((defs,hyps),tm) (h,c) /\ h |= c`;
*)


(* -- part 3 -- *)

val type_ok_IMP = prove(
  ``!defs ty. type_ok defs ty ==> !ty1. type defs ty ty1 ==> type_ok ty1``,
  HO_MATCH_MP_TAC type_ok_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [term_cases]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ TRY (ONCE_REWRITE_TAC [sholSyntaxTheory.proves_cases]
    \\ SIMP_TAC (srw_ss()) [] \\ RES_TAC \\ ASM_SIMP_TAC std_ss [] \\ NO_TAC)
  THEN1 cheat (* Ind not supported *)
  THEN1 cheat (* Tyapp not supported *))
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];

val type_11 = prove(
  ``type defs ty ty1 /\ type defs ty ty2 ==> (ty1 = ty2)``,
  cheat);

val term_ok_IMP = prove(
  ``!tm defs. term_ok defs tm /\ welltyped tm ==>
              !tm1. term defs tm tm1 ==> term_ok tm1 /\ welltyped tm1``,
  Induct \\ SIMP_TAC std_ss [term_ok_def,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [term_cases]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_FORALL]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC type_ok_IMP
  \\ TRY (ONCE_REWRITE_TAC [sholSyntaxTheory.proves_cases]
          \\ ASM_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  THEN1 cheat (* Const not supported *)
  THEN1
   (ONCE_REWRITE_TAC [sholSyntaxTheory.proves_cases]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ DISJ1_TAC
    \\ Q.PAT_ASSUM `type defs tt ttt` MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC type_11
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1
   (ONCE_REWRITE_TAC [sholSyntaxTheory.proves_cases]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ DISJ1_TAC
    \\ Q.PAT_ASSUM `type defs tt ttt` MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `type defs (Fun t Bool) tx1` MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [term_cases] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC type_11
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1
   (ONCE_REWRITE_TAC [sholSyntaxTheory.proves_cases]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ `?rty. typeof x1 = Fun (typeof y1) rty` by cheat
    \\ METIS_TAC []));

val proves_IMP = prove(
  ``!dh c. dh |- c ==> ?h1 c1. seq_trans (dh,c) (h1,c1) /\ h1 |- c1``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_ind
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [seq_trans_def]
  \\ cheat (* holSyntaxTheory.proves_rules ought to provide context_ok *));


val _ = export_theory();

