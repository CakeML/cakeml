
open HolKernel Parse boolLib bossLib;

val _ = new_theory "hol_verification";

open hol_kernelTheory model_syntaxTheory;
open listTheory arithmeticTheory combinTheory pairTheory;

open monadsyntax;
val _ = temp_overload_on ("monad_bind", ``ex_bind``);
val _ = temp_overload_on ("return", ``ex_return``);
val _ = set_trace "Unicode" 0;

infix \\ val op \\ = op THEN;

(* ------------------------------------------------------------------------- *)
(* Translations from implementation types to model types.                    *)
(* ------------------------------------------------------------------------- *)

val MEM_hol_type_size = prove(
  ``!tys a. MEM a tys ==> hol_type_size a < hol_type1_size tys``,
  Induct \\ SIMP_TAC std_ss [MEM,hol_type_size_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val hol_ty_def = tDefine "hol_ty" `
  (hol_ty (hol_kernel$Tyvar v) = Tyvar v) /\
  (hol_ty (Tyapp s tys) =
     if (s = "bool") /\ (tys = []) then Bool else
     if (s = "ind") /\ (tys = []) then Ind else
     if (s = "fun") /\ (LENGTH tys = 2) then
       Fun (hol_ty (EL 0 tys)) (hol_ty (EL 1 tys))
     else Tyapp s (MAP hol_ty tys))`
 (WF_REL_TAC `measure hol_type_size`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MEM_hol_type_size \\ TRY DECIDE_TAC
  \\ Cases_on `tys` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) [hol_type_size_def]
  \\ DECIDE_TAC);

val _ = temp_overload_on("fun",``\x y. hol_kernel$Tyapp "fun" [x;y]``);
val _ = temp_overload_on("bool_ty",``hol_kernel$Tyapp "bool" []``);
val _ = temp_overload_on("impossible_term",``Const "=" Ind``);

val hol_tm_def = Define `
  (hol_tm (Var v ty) = Var v (hol_ty ty)) /\
  (hol_tm (Const s ty) =
     if s = "=" then
       if (?a. ty = fun a (fun a bool_ty))
       then Equal (domain (hol_ty ty))
       else impossible_term
     else
     if s = "@" then
       if (?a. ty = fun (fun a bool_ty) a)
       then Select (codomain (hol_ty ty))
       else impossible_term
     else
       Const s (hol_ty ty)) /\
  (hol_tm (Comb x y) = Comb (hol_tm x) (hol_tm y)) /\
  (hol_tm (Abs (Var v ty) x) = Abs v (hol_ty ty) (hol_tm x)) /\
  (hol_tm _ = impossible_term)`;

val hol_ctxt_def = Define `
  (hol_ctxt [] = []) /\
  (hol_ctxt (Axiomdef tm::ctxt) =
    (Axiomdef (hol_tm tm)) :: hol_ctxt ctxt) /\
  (hol_ctxt (Constdef n tm::ctxt) =
    (Constdef n (hol_tm tm)) :: hol_ctxt ctxt) /\
  (hol_ctxt (Typedef s1 tm s2 s3 :: ctxt) =
    (Typedef s1 (hol_tm tm) s2 s3) :: hol_ctxt ctxt)`;

(* ------------------------------------------------------------------------- *)
(* type_ok, term_ok, context_ok and |- for implementation types.             *)
(* ------------------------------------------------------------------------- *)

val TYPE_def = Define `
  TYPE ctxt ty = type_ok (hol_ctxt ctxt) (hol_ty ty)`;

val TERM_def = Define `
  TERM ctxt tm = welltyped_in (hol_tm tm) (hol_ctxt ctxt)`;

val CONTEXT_def = Define `
  CONTEXT ctxt = context_ok (hol_ctxt ctxt)`;

val THM_def = Define `
  THM ctxt (Sequent asl c) = ((MAP hol_tm asl, hol_ctxt ctxt) |- hol_tm c)`;

(* ------------------------------------------------------------------------- *)
(* Certain terms cannot occur                                                *)
(* ------------------------------------------------------------------------- *)

val NOT_EQ_CONST = prove(
  ``!ctxt x. context_ok (hol_ctxt ctxt) ==>
             ~MEM ("=",x) (consts (hol_ctxt ctxt))``,
  Induct \\ FULL_SIMP_TAC std_ss [consts,MAP,FLAT,MEM,hol_ctxt_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [consts,MAP,FLAT,MEM,hol_ctxt_def]
  \\ FULL_SIMP_TAC std_ss [consts_aux,APPEND,MEM,context_ok,def_ok]
  \\ FULL_SIMP_TAC std_ss [reserved_const_names,MEM]);

val impossible_term_thm = prove(
  ``TERM ctxt tm ==> hol_tm tm <> impossible_term ``,
  SIMP_TAC std_ss [TERM_def,welltyped_in] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [term_ok] \\ IMP_RES_TAC NOT_EQ_CONST);

val Abs_Var = prove(
  ``TERM ctxt (Abs v tm) ==> ?s ty. v = Var s ty``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]);

val Equal_type = prove(
  ``TERM ctxt (Const "=" ty) ==> ?a. ty = fun a (fun a bool_ty)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ FULL_SIMP_TAC std_ss [hol_tm_def] \\ METIS_TAC []);

val Select_type = prove(
  ``TERM ctxt (Const "@" ty) ==> ?a. ty = fun (fun a bool_ty) a``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,EVAL ``"@" = "="``] \\ METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* State invariant                                                           *)
(* ------------------------------------------------------------------------- *)



(*

type_ok_CASES
term_ok
REFL_def
mk_eq_def
mk_const_def
mk_comb_def
type_of_def
typeof
proves_RULES

*)

val _ = export_theory();
