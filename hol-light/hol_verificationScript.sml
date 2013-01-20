
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

val hol_defs_def = Define `
  (hol_defs [] = []) /\
  (hol_defs (Axiomdef tm::defs) =
    (Axiomdef (hol_tm tm)) :: hol_defs defs) /\
  (hol_defs (Constdef n tm::defs) =
    (Constdef n (hol_tm tm)) :: hol_defs defs) /\
  (hol_defs (Typedef s1 tm s2 s3 :: defs) =
    (Typedef s1 (hol_tm tm) s2 s3) :: hol_defs defs)`;

(* ------------------------------------------------------------------------- *)
(* type_ok, term_ok, context_ok and |- for implementation types.             *)
(* ------------------------------------------------------------------------- *)

val TYPE_def = Define `
  TYPE defs ty = type_ok (hol_defs defs) (hol_ty ty)`;

val TERM_def = Define `
  TERM defs tm = welltyped_in (hol_tm tm) (hol_defs defs)`;

val CONTEXT_def = Define `
  CONTEXT defs = context_ok (hol_defs defs)`;

val THM_def = Define `
  THM defs (Sequent asl c) = ((hol_defs defs, MAP hol_tm asl) |- hol_tm c)`;

(* ------------------------------------------------------------------------- *)
(* Certain terms cannot occur                                                *)
(* ------------------------------------------------------------------------- *)

val NOT_EQ_CONST = prove(
  ``!defs x. context_ok (hol_defs defs) ==>
             ~MEM ("=",x) (consts (hol_defs defs))``,
  Induct \\ FULL_SIMP_TAC std_ss [consts,MAP,FLAT,MEM,hol_defs_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [consts,MAP,FLAT,MEM,hol_defs_def]
  \\ FULL_SIMP_TAC std_ss [consts_aux,APPEND,MEM,context_ok,def_ok]
  \\ FULL_SIMP_TAC std_ss [reserved_const_names,MEM]);

val impossible_term_thm = prove(
  ``TERM defs tm ==> hol_tm tm <> impossible_term ``,
  SIMP_TAC std_ss [TERM_def,welltyped_in] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [term_ok] \\ IMP_RES_TAC NOT_EQ_CONST);

val Abs_Var = prove(
  ``TERM defs (Abs v tm) ==> ?s ty. v = Var s ty``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]);

val Equal_type = prove(
  ``TERM defs (Const "=" ty) ==> ?a. ty = fun a (fun a bool_ty)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ FULL_SIMP_TAC std_ss [hol_tm_def] \\ METIS_TAC []);

val Select_type = prove(
  ``TERM defs (Const "@" ty) ==> ?a. ty = fun (fun a bool_ty) a``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,EVAL ``"@" = "="``] \\ METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* State invariant - types/terms/axioms can be extracted from defs           *)
(* ------------------------------------------------------------------------- *)

val STATE_def = Define `
  STATE state defs =
    (defs = hol_defs state.the_definitions) /\ context_ok defs /\
    (state.the_type_constants = types defs ++ [("bool",0);("ind",0);("fun",2)]) /\
    ALL_DISTINCT (MAP FST state.the_type_constants) /\
    (consts defs = MAP (\(name,ty). (name, hol_ty ty)) state.the_term_constants)`

(* ------------------------------------------------------------------------- *)
(* Verification of type functions                                            *)
(* ------------------------------------------------------------------------- *)

val can_thm = prove(
  ``can f x s = case f x s of (HolRes _,s) => (HolRes T,s) |
                              (_,s) => (HolRes F,s)``,
  SIMP_TAC std_ss [can_def,ex_bind_def,otherwise_def]
  \\ Cases_on `f x s` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]);

val assoc_thm = prove(
  ``!xs y z s s'.
      (assoc y xs s = (z, s')) ==>
      (s' = s) /\ !i. (z = HolRes i) ==> MEM (y,i) xs``,
  Induct \\ SIMP_TAC (srw_ss()) [Once assoc_def,failwith_def]
  \\ Cases \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ Cases_on `y = q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ METIS_TAC []);

val get_type_arity_thm = prove(
  ``!name s z s'.
      (get_type_arity name s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> MEM (name,i) s.the_type_constants``,
  SIMP_TAC (srw_ss()) [get_type_arity_def,ex_bind_def,
    get_the_type_constants_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC assoc_thm);

val mk_vartype_thm = store_thm("mk_vartype_thm",
  ``!name s.
      TYPE s.the_definitions (mk_vartype name)``,
  SIMP_TAC (srw_ss()) [mk_vartype_def,TYPE_def,hol_ty_def,
    Once type_ok_CASES,type_INJ]);

val mk_type_thm = store_thm("mk_type_thm",
  ``!tyop args s z s'.
      STATE s defs /\ EVERY (TYPE s.the_definitions) args /\
      (mk_type (tyop,args) s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> TYPE s.the_definitions i /\
                             (i = Tyapp tyop args)``,
  SIMP_TAC std_ss [mk_type_def,try_def,ex_bind_def,otherwise_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `get_type_arity tyop s`
  \\ IMP_RES_TAC get_type_arity_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ SRW_TAC [] [ex_return_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_def,hol_ty_def]
  \\ SRW_TAC [] [] \\ SIMP_TAC std_ss [Once type_ok_CASES,type_INJ]
  THEN1 (Cases_on `args` \\ FULL_SIMP_TAC std_ss [LENGTH]
         \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
         \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_NIL,
              EVERY_DEF,HD,EVAL ``EL 1 (x::y::xs)``,TYPE_def])
  \\ SIMP_TAC std_ss [LENGTH_MAP,MEM_MAP,PULL_EXISTS]
  \\ NTAC 3 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [STATE_def,MEM_APPEND,MEM,LENGTH_NIL]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,TYPE_def]);

val dest_type_thm = store_thm("dest_type_thm",
  ``!ty s z s'.
      STATE s defs /\
      (dest_type ty s = (z,s')) /\ TYPE s.the_definitions ty ==> (s' = s) /\
      !i. (z = HolRes i) ==> ?n tys. (ty = Tyapp n tys) /\ (i = (n,tys)) /\
                                     EVERY (TYPE s.the_definitions) tys``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def,failwith_def,ex_return_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_def,hol_ty_def] \\ SRW_TAC [] [] THEN1
   (Cases_on `l` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC std_ss [HD, EVAL ``EL 1 (x::y::xs)``,EVERY_DEF]
    \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [Once type_ok_CASES,type_INJ,TYPE_def,type_DISTINCT]
    \\ REPEAT STRIP_TAC \\ `F` by DECIDE_TAC)
  \\ Cases_on `l` \\ SIMP_TAC std_ss [EVERY_DEF]
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once type_ok_CASES]
  \\ SIMP_TAC std_ss [type_INJ,TYPE_def,type_DISTINCT,EVERY_MEM,MEM_MAP,
      PULL_EXISTS,LENGTH_MAP,MEM]);

val dest_vartype_thm = store_thm("dest_vartype_thm",
  ``!ty s z s'.
      (dest_vartype ty s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> (ty = Tyvar i)``,
  Cases \\ FULL_SIMP_TAC (srw_ss())
    [dest_vartype_def,failwith_def,ex_return_def]);

val is_type_thm = store_thm("is_type_thm",
  ``!ty. is_type ty = ?s tys. ty = Tyapp s tys``,
  Cases \\ SIMP_TAC (srw_ss()) [is_type_def]);

val is_vartype_thm = store_thm("is_vartype_thm",
  ``!ty. is_vartype ty = ?s. ty = Tyvar s``,
  Cases \\ SIMP_TAC (srw_ss()) [is_vartype_def]);

val MEM_union = prove(
  ``!xs ys x. MEM x (union xs ys) = MEM x xs \/ MEM x ys``,
  Induct \\ FULL_SIMP_TAC std_ss [union_def]
  \\ ONCE_REWRITE_TAC [itlist_def] \\ SRW_TAC [] [insert_def]
  \\ METIS_TAC []);

val MEM_STRING_UNION = prove(
  ``!xs ys x. MEM x (STRING_UNION xs ys) = MEM x xs \/ MEM x ys``,
  Induct \\ FULL_SIMP_TAC std_ss [STRING_UNION]
  \\ ONCE_REWRITE_TAC [ITLIST] \\ SRW_TAC [] [STRING_INSERT]
  \\ METIS_TAC []);

val ITLIST_MAP = prove(
  ``!xs b. ITLIST f (MAP g xs) b = ITLIST (f o g) xs b``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,ITLIST]);

val tyvars_thm = prove(
  ``!ty s. MEM s (tyvars ty) = MEM s (tyvars (hol_ty ty))``,
  HO_MATCH_MP_TAC tyvars_ind \\ REPEAT STRIP_TAC
  \\ Cases_on `ty` \\ FULL_SIMP_TAC (srw_ss()) [type_INJ,type_DISTINCT]
  \\ SIMP_TAC (srw_ss()) [Once hol_kernelTheory.tyvars_def,Once tyvars,hol_ty_def]
  \\ SRW_TAC [] [tyvars]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [tyvars,Once itlist_def])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [tyvars,Once itlist_def])
  THEN1
   (FULL_SIMP_TAC (srw_ss()) [tyvars,Once itlist_def]
    \\ Cases_on `l` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC std_ss [HD, EVAL ``EL 1 (x::y::xs)``,EVERY_DEF]
    \\ FULL_SIMP_TAC (srw_ss()) [MEM,MAP,Once itlist_def]
    \\ FULL_SIMP_TAC (srw_ss()) [MEM,MAP,Once itlist_def]
    \\ FULL_SIMP_TAC std_ss [MEM_union,MEM,MEM_STRING_UNION]
    \\ `F` by DECIDE_TAC)
  \\ SIMP_TAC (srw_ss()) [Once tyvars] \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [ITLIST_MAP]
  \\ Induct_on `l`
  \\ SIMP_TAC (srw_ss()) [Once itlist_def,ITLIST,MEM_union,MEM_STRING_UNION]
  \\ METIS_TAC []);

val lemma = prove(``(if x = y then f y else f x) = f x``,METIS_TAC[]);

val LENGTH_EQ_2 = prove(
  ``!l. (LENGTH l = 2) = ?x1 x2. l = [x1;x2]``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]);

val type_subst_thm = store_thm("type_subst",
  ``!i ty.
      (hol_ty (type_subst i ty) =
       TYPE_SUBST (MAP (\(n,t). (hol_ty n,hol_ty t)) i) (hol_ty ty)) /\
      (EVERY (\(x,y). TYPE s x /\ TYPE s y) i /\ TYPE s ty ==>
       TYPE s (type_subst i ty))``,
  HO_MATCH_MP_TAC type_subst_ind \\ STRIP_TAC \\ Cases THEN1
   (SIMP_TAC (srw_ss()) [Once type_subst_def]
    \\ SIMP_TAC (srw_ss()) [Once type_subst_def]
    \\ SIMP_TAC std_ss [hol_ty_def,TYPE_SUBST]
    \\ Induct_on `i` \\ TRY Cases \\ ONCE_REWRITE_TAC [rev_assocd_def]
    \\ SIMP_TAC (srw_ss()) [REV_ASSOCD,MAP]
    \\ Cases_on `r = Tyvar s'` \\ FULL_SIMP_TAC std_ss [hol_ty_def]
    \\ SRW_TAC [] []
    \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [hol_ty_def,type_INJ]
    \\ `F` by ALL_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
    \\ SRW_TAC [] [type_DISTINCT])
  \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [type_subst_def] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC std_ss [LET_DEF,lemma]
  \\ Cases_on `l = []`
  THEN1 (FULL_SIMP_TAC std_ss [MAP,hol_ty_def] \\ SRW_TAC [] [TYPE_SUBST])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `LENGTH l = 2` THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_2]
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [TYPE_SUBST,MAP]
    \\ FULL_SIMP_TAC (srw_ss()) [TYPE_def,hol_ty_def]
    \\ Cases_on `s' = "fun"` \\ FULL_SIMP_TAC std_ss [TYPE_SUBST,MAP]
    \\ FULL_SIMP_TAC (srw_ss()) [TYPE_def,hol_ty_def]
    \\ SIMP_TAC (srw_ss()) [Once type_ok_CASES,type_DISTINCT,type_INJ]
    \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ SIMP_TAC (srw_ss()) [Once type_ok_CASES,type_DISTINCT,type_INJ]
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [hol_ty_def,LENGTH_MAP,GSYM LENGTH_NIL]
  \\ FULL_SIMP_TAC std_ss [TYPE_SUBST,type_INJ]
  \\ STRIP_TAC THEN1
   (NTAC 2 (POP_ASSUM (K ALL_TAC)) \\ Induct_on `l`
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,MEM])
  \\ FULL_SIMP_TAC std_ss [TYPE_def,hol_ty_def,LENGTH_MAP,GSYM LENGTH_NIL]
  \\ STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once type_ok_CASES,type_DISTINCT,type_INJ]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,EVERY_MEM,FORALL_PROD]
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once type_ok_CASES,type_DISTINCT,type_INJ]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,EVERY_MEM,FORALL_PROD]
  \\ METIS_TAC []);

val mk_fun_ty_thm = store_thm("mk_fun_ty_thm",
  ``!ty1 ty2 s z s'.
      STATE s defs /\ EVERY (TYPE s.the_definitions) [ty1;ty2] /\
      (mk_fun_ty ty1 ty2 s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> (i = Tyapp "fun" [ty1;ty2]) /\
                             TYPE s.the_definitions i``,
  SIMP_TAC std_ss [mk_fun_ty_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mk_type_thm);

(* ------------------------------------------------------------------------- *)
(* Verification of term functions                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Verification of thm functions                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Verification of definition functions                                      *)
(* ------------------------------------------------------------------------- *)


val _ = export_theory();
