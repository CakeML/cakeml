
(* ------------------------------------------------------------------------- *)
(* Definition of char type                                                   *)
(* ------------------------------------------------------------------------- *)

let (CHR,ORD) =
  let char_lemma = prove(`(\n:num. n < 256) 0`,SIMP_TAC [ARITH_LT]) in
    new_basic_type_definition "char" ("CHR","ORD") char_lemma;;

new_type_abbrev("string",`:char list`);;

(* ------------------------------------------------------------------------- *)
(* Start logging proofs for export to Opentheory (then import to HOL4)       *)
(* ------------------------------------------------------------------------- *)

start_logging ();;
logfile "model-syntax";;

let x name th = export_thm (DISCH (mk_var(name,`:bool`)) th);;

(* ========================================================================= *)
(* Syntactic definitions for "core HOL", including provability.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* HOL types.                                                                *)
(* ------------------------------------------------------------------------- *)

let type_INDUCT,type_RECURSION = define_type
  "type = Tyvar string
        | Tyapp string (type list)
        | Bool
        | Ind
        | Fun type type";;

let type_DISTINCT = distinctness "type";;

let type_INJ = injectivity "type";;

let domain = define
  `domain (Fun s t) = s`;;

let codomain = define
  `codomain (Fun s t) = t`;;

x "type_DISTINCT" type_DISTINCT;;
x "type_INJ" type_INJ;;
x "type_INDUCT" type_INDUCT;;
x "domain" domain;;
x "codomain" codomain;;

(* ------------------------------------------------------------------------- *)
(* HOL terms.                                                                *)
(* ------------------------------------------------------------------------- *)

let term_INDUCT,term_RECURSION = define_type
 "term = Var string type
       | Const string type
       | Equal type | Select type
       | Comb term term
       | Abs string type term";;

let term_DISTINCT = distinctness "term";;

let term_INJ = injectivity "term";;

x "term_DISTINCT" term_DISTINCT;;
x "term_INJ" term_INJ;;
x "term_INDUCT" term_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* Typing judgements.                                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_type",(12,"right"));;

let has_type_RULES,has_type_INDUCT,has_type_CASES = new_inductive_definition
  `(!n ty. (Var n ty) has_type ty) /\
   (!n ty. (Const n ty) has_type ty) /\
   (!ty. (Equal ty) has_type (Fun ty (Fun ty Bool))) /\
   (!ty. (Select ty) has_type (Fun (Fun ty Bool) ty)) /\
   (!s t dty rty. s has_type (Fun dty rty) /\ t has_type dty
                  ==> (Comb s t) has_type rty) /\
   (!n dty t rty. t has_type rty ==> (Abs n dty t) has_type (Fun dty rty))`;;

x "has_type_RULES" has_type_RULES;;
x "has_type_INDUCT" has_type_INDUCT;;
x "has_type_CASES" has_type_CASES;;

let welltyped = new_definition
  `welltyped tm <=> ?ty. tm has_type ty`;;

let typeof = new_recursive_definition term_RECURSION
 `(typeof (Var n ty) = ty) /\
  (typeof (Const n ty) = ty) /\
  (typeof (Equal ty) = Fun ty (Fun ty Bool)) /\
  (typeof (Select ty) = Fun (Fun ty Bool) ty) /\
  (typeof (Comb s t) = codomain (typeof s)) /\
  (typeof (Abs n ty t) = Fun ty (typeof t))`;;

let WELLTYPED_LEMMA = prove
 (`!tm ty. tm has_type ty ==> (typeof tm = ty)`,
  MATCH_MP_TAC has_type_INDUCT THEN
  SIMP_TAC[typeof; has_type_RULES; codomain]);;

let WELLTYPED = prove
 (`!tm. welltyped tm <=> tm has_type (typeof tm)`,
  REWRITE_TAC[welltyped] THEN MESON_TAC[WELLTYPED_LEMMA]);;

let WELLTYPED_CLAUSES = prove
 (`(!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!ty. welltyped(Equal ty)) /\
   (!ty. welltyped(Select ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!n ty t. welltyped (Abs n ty t) = welltyped t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped] THEN
  (GEN_REWRITE_TAC BINDER_CONV [has_type_CASES] ORELSE
   GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [has_type_CASES]) THEN
  REWRITE_TAC[term_INJ; term_DISTINCT] THEN
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

x "welltyped" welltyped;;
x "typeof" typeof;;
x "WELLTYPED" WELLTYPED;;
x "WELLTYPED_LEMMA" WELLTYPED_LEMMA;;
x "WELLTYPED_CLAUSES" WELLTYPED_CLAUSES;;

(* ------------------------------------------------------------------------- *)
(* Since equations are important, a bit of derived syntax.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("===",(18,"right"));;

let equation = new_definition
 `(s === t) = Comb (Comb (Equal(typeof s)) s) t`;;

let EQUATION_HAS_TYPE_BOOL = prove
 (`!s t. (s === t) has_type Bool
         <=> welltyped s /\ welltyped t /\ (typeof s = typeof t)`,
  REWRITE_TAC[equation] THEN
  ONCE_REWRITE_TAC[has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV) [has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2(BINDER_CONV o LAND_CONV))
    [has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ; type_INJ] THEN
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

x "equation" equation;;
x "EQUATION_HAS_TYPE_BOOL" EQUATION_HAS_TYPE_BOOL;;

(* ------------------------------------------------------------------------- *)
(* Alpha-conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS = new_recursive_definition list_RECURSION
  `(ALPHAVARS [] tmp <=> (FST tmp = SND tmp)) /\
   (ALPHAVARS (CONS tp oenv) tmp <=>
        (tmp = tp) \/
        ~(FST tp = FST tmp) /\ ~(SND tp = SND tmp) /\ ALPHAVARS oenv tmp)`;;

x "ALPHAVARS" ALPHAVARS;;

let RACONV_RULES,RACONV_INDUCT,RACONV_CASES = new_inductive_definition
 `(!env x1 ty1 x2 ty2.
       ALPHAVARS env (Var x1 ty1,Var x2 ty2)
       ==> RACONV env (Var x1 ty1,Var x2 ty2)) /\
  (!env x ty. RACONV env (Const x ty,Const x ty)) /\
  (!env ty. RACONV env (Equal ty,Equal ty)) /\
  (!env ty. RACONV env (Select ty,Select ty)) /\
  (!env s1 t1 s2 t2.
       RACONV env (s1,s2) /\ RACONV env (t1,t2)
       ==> RACONV env (Comb s1 t1,Comb s2 t2)) /\
  (!env x1 ty1 t1 x2 ty2 t2.
       (ty1 = ty2) /\ RACONV (CONS ((Var x1 ty1),(Var x2 ty2)) env) (t1,t2)
       ==> RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`;;

let RACONV = prove
 (`(RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Equal ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Select ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Equal ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Select ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Equal ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Equal ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Equal ty1,Equal ty2) <=> (ty1 = ty2)) /\
   (RACONV env (Equal ty1,Select ty2) <=> F) /\
   (RACONV env (Equal ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Equal ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Select ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Select ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Select ty1,Equal ty2) <=> F) /\
   (RACONV env (Select ty1,Select ty2) <=> (ty1 = ty2)) /\
   (RACONV env (Select ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Select ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Equal ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Select ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Equal ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Select ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2) <=>
        (ty1 = ty2) /\ RACONV (CONS (Var x1 ty1,Var x2 ty2) env) (t1,t2))`,
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RACONV_CASES] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let ACONV = new_definition
 `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;

x "RACONV" RACONV;;
x "ACONV" ACONV;;

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS_REFL = prove
 (`!env t. ALL (\(s,t). s = t) env ==> ALPHAVARS env (t,t)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; ALPHAVARS] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[PAIR_EQ]);;

let RACONV_REFL = prove
 (`!t env. ALL (\(s,t). s = t) env ==> RACONV env (t,t)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[RACONV] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[ALPHAVARS_REFL];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let ACONV_REFL = prove
 (`!t. ACONV t t`,
  REWRITE_TAC[ACONV] THEN SIMP_TAC[RACONV_REFL; ALL]);;

(* ------------------------------------------------------------------------- *)
(* Alpha-convertible terms have the same type (if welltyped).                *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS_TYPE = prove
 (`!env s t. ALPHAVARS env (s,t) /\
             ALL (\(x,y). welltyped x /\ welltyped y /\
                          (typeof x = typeof y)) env /\
             welltyped s /\ welltyped t
           ==> (typeof s = typeof t)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALPHAVARS; ALL; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let RACONV_TYPE = prove
 (`!env p. RACONV env p
           ==> ALL (\(x,y). welltyped x /\ welltyped y /\
                        (typeof x = typeof y)) env /\
               welltyped (FST p) /\ welltyped (SND p)
               ==> (typeof (FST p) = typeof (SND p))`,
  MATCH_MP_TAC RACONV_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; typeof] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[typeof; ALPHAVARS_TYPE];
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[WELLTYPED_CLAUSES];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[typeof] THEN ASM_MESON_TAC[WELLTYPED_CLAUSES]]);;

let ACONV_TYPE = prove
 (`!s t. ACONV s t ==> welltyped s /\ welltyped t ==> (typeof s = typeof t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`[]:(term#term)list`; `(s:term,t:term)`] RACONV_TYPE) THEN
  REWRITE_TAC[ACONV; ALL] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL version of "term_union".                                              *)
(* ------------------------------------------------------------------------- *)

let TERM_UNION = new_recursive_definition list_RECURSION
 `(TERM_UNION [] l2 = l2) /\
  (TERM_UNION (CONS h t) l2 =
        let subun = TERM_UNION t l2 in
        if EX (ACONV h) subun then subun else CONS h subun)`;;

x "TERM_UNION" TERM_UNION;;

let TERM_UNION_NONEW = prove
 (`!l1 l2 x. MEM x (TERM_UNION l1 l2) ==> MEM x l1 \/ MEM x l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; MEM] THEN
  LET_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[ACONV_REFL]);;

let TERM_UNION_THM = prove
 (`!l1 l2 x. MEM x l1 \/ MEM x l2
             ==> ?y. MEM y (TERM_UNION l1 l2) /\ ACONV x y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; MEM; GSYM EX_MEM] THENL
   [MESON_TAC[ACONV_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN LET_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MEM] THEN  ASM_MESON_TAC[ACONV_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Handy lemma for using it in a sequent.                                    *)
(* ------------------------------------------------------------------------- *)

let ALL_BOOL_TERM_UNION = prove
 (`ALL (\a. a has_type Bool) l1 /\ ALL (\a. a has_type Bool) l2
   ==> ALL (\a. a has_type Bool) (TERM_UNION l1 l2)`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[TERM_UNION_NONEW]);;

(* ------------------------------------------------------------------------- *)
(* Whether a variable/constant is free in a term.                            *)
(* ------------------------------------------------------------------------- *)

let VFREE_IN = new_recursive_definition term_RECURSION
  `(VFREE_IN v (Var x ty) <=> (Var x ty = v)) /\
   (VFREE_IN v (Const x ty) <=> (Const x ty = v)) /\
   (VFREE_IN v (Equal ty) <=> (Equal ty = v)) /\
   (VFREE_IN v (Select ty) <=> (Select ty = v)) /\
   (VFREE_IN v (Comb s t) <=> VFREE_IN v s \/ VFREE_IN v t) /\
   (VFREE_IN v (Abs x ty t) <=> ~(Var x ty = v) /\ VFREE_IN v t)`;;

x "VFREE_IN" VFREE_IN;;

let VFREE_IN_RACONV = prove
 (`!env p. RACONV env p
           ==> !x ty. VFREE_IN (Var x ty) (FST p) /\
                      ~(?y. MEM (Var x ty,y) env) <=>
                      VFREE_IN (Var x ty) (SND p) /\
                      ~(?y. MEM (y,Var x ty) env)`,
  MATCH_MP_TAC RACONV_INDUCT THEN REWRITE_TAC[VFREE_IN; term_DISTINCT] THEN
  REWRITE_TAC[PAIR_EQ; term_INJ; MEM] THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALPHAVARS] THEN
  REWRITE_TAC[MEM; FORALL_PAIR_THM; term_INJ; PAIR_EQ] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MESON_TAC[]);;

let VFREE_IN_ACONV = prove
 (`!s t x t. ACONV s t ==> (VFREE_IN (Var x ty) s <=> VFREE_IN (Var x ty) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ACONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VFREE_IN_RACONV) THEN
  SIMP_TAC[MEM; FST; SND]);;

x "VFREE_IN_ACONV" VFREE_IN_ACONV;;

let CLOSED = define
 `CLOSED tm = !x ty. ~(VFREE_IN (Var x ty) tm)`;;

x "CLOSED" CLOSED;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary association list function.                                      *)
(* ------------------------------------------------------------------------- *)

let REV_ASSOCD_DEF = new_recursive_definition list_RECURSION
  `(!(a:A) (d:B). REV_ASSOCD a [] d = d) /\
   (!a p t d. REV_ASSOCD a (CONS p t) d =
        if SND p = a then FST p else REV_ASSOCD a t d)`;;

let REV_ASSOCD = prove(
  `(!(a:A) (d:B). REV_ASSOCD a [] d = d) /\
   (!a x y (t:(A#B)list) d. REV_ASSOCD a (CONS (x,y) t) d =
        if y = a then x else REV_ASSOCD a t d)`,
  REWRITE_TAC[REV_ASSOCD_DEF]);;

x "REV_ASSOCD" REV_ASSOCD;;

(* ------------------------------------------------------------------------- *)
(* Substition of types in types.                                             *)
(* ------------------------------------------------------------------------- *)

let TYPE_SUBST_LEMMA =
  (SIMP_RULE [] o
   ISPEC `\(a0:type) (a1:(type)list) (x1:type) x2. CONS x1 x2` o
   ISPEC `[]:(type)list` o
   ISPEC `\(a0:type) (a1:type) x1 x2. Fun x1 x2` o
   ISPEC `Ind` o
   ISPEC `Bool` o
   ISPEC `\s (x:(type)list) ts. Tyapp s ts` o
   ISPEC `\v. REV_ASSOCD (Tyvar v) i (Tyvar v)`)
  type_RECURSION;;

let MAP_LEMMA = prove
 (`(!x y. (f [] = []) /\ (f (CONS x y) = CONS (g x) (f y))) ==> (f = MAP g)`,
  SIMP_TAC [FUN_EQ_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN ASM_SIMP_TAC [MAP]);;

let TYPE_SUBST_EXISTS = prove
 (`?TYPE_SUBST.
    !i v tys ty1 ty2.
     (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) /\
     (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) /\
     (TYPE_SUBST i Bool = Bool) /\
     (TYPE_SUBST i Ind = Ind) /\
     (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))`,
  MESON_TAC [TYPE_SUBST_LEMMA;MAP_LEMMA]);;

let TYPE_SUBST = new_specification ["TYPE_SUBST"] TYPE_SUBST_EXISTS;;

x "TYPE_SUBST" TYPE_SUBST;;

(* ------------------------------------------------------------------------- *)
(* Variant function.                                                         *)
(* ------------------------------------------------------------------------- *)

let rec SET_RULE g =
  prove(g,REWRITE_TAC[
    EXTENSION;IN_ELIM_THM;IN_INSERT;NOT_IN_EMPTY;
    IN_UNION;IN_INTER]
        THEN MESON_TAC[]);;

let VFREE_IN_FINITE = prove
 (`!t. FINITE {x | VFREE_IN x t}`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VFREE_IN] THEN
  REWRITE_TAC[SET_RULE `{x | a = x} = {a}`;
              SET_RULE `{x | P x \/ Q x} = {x | P x} UNION {x | Q x}`;
              SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_RULES; FINITE_UNION; FINITE_INTER]);;

let VFREE_IN_FINITE_ALT = prove
 (`!t ty. FINITE {x | VFREE_IN (Var x ty) t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(Var x ty). x) {x | VFREE_IN x t}` THEN
  SIMP_TAC[VFREE_IN_FINITE; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:string` THEN DISCH_TAC THEN
  EXISTS_TAC `Var x ty` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC []);;

let PRIME_CHAR = define
 `PRIME_CHAR = CHR 39`;;

let APPEND_CANCEL = prove
 (`!x y z. (APPEND x y = APPEND x z) = (y = z)`,
  MATCH_MP_TAC list_INDUCT THEN ASM_SIMP_TAC [APPEND;CONS_11]);;

let REPLICATE_CANCEL = prove
 (`!m n x. (REPLICATE x m = REPLICATE (x:'a) n) = (m = (n:num))`,
  INDUCT_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC (SPEC `n:num` num_CASES) THEN
  ASM_SIMP_TAC [REPLICATE;NOT_CONS_NIL] THEN
  FIRST_X_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN
  ASM_SIMP_TAC [REPLICATE;NOT_CONS_NIL;CONS_11;NOT_SUC;SUC_INJ]);;

let PRIMED_INFINITE = prove
 (`INFINITE (IMAGE (\n. APPEND x (REPLICATE PRIME_CHAR (n:num))) UNIV)`,
  MATCH_MP_TAC INFINITE_IMAGE_INJ THEN
  SIMP_TAC [APPEND_CANCEL;REPLICATE_CANCEL;num_INFINITE]);;

let PRIMED_NAME_EXISTS = prove
 (`?n. ~(VFREE_IN (Var (APPEND x (REPLICATE PRIME_CHAR n)) ty) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:term`; `ty:type`] VFREE_IN_FINITE_ALT) THEN
  DISCH_THEN(MP_TAC o CONJ PRIMED_INFINITE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_DIFF_FINITE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY;IN_DIFF;IN_ELIM_THM;IN_UNIV;IN_IMAGE] THEN
  ASM_MESON_TAC []);;

let LEAST_EXISTS = prove
 (`(?n. P n) ==> ?k. P k /\ !m. m < k ==> ~(P (m:num))`,
  STRIP_TAC THEN FIRST_X_ASSUM MP_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN
  MATCH_MP_TAC num_WF THEN ASM_MESON_TAC []);;

let VARIANT_PRIMES = new_specification ["VARIANT_PRIMES"]
  ((REWRITE_RULE[SKOLEM_THM] o
    GENL [`t:term`;`x:(char)list`;`ty:type`] o
    MATCH_MP LEAST_EXISTS) PRIMED_NAME_EXISTS);;

let VARIANT = (GENL [`t:term`;`x:string`;`ty:type`] o define)
 `VARIANT t x ty = APPEND x (REPLICATE PRIME_CHAR (VARIANT_PRIMES t x ty))`;;

let VARIANT_THM = prove
 (`!t x ty. ~VFREE_IN (Var (VARIANT t x ty) ty) t`,
  MESON_TAC [VARIANT;VARIANT_PRIMES]);;

x "PRIME_CHAR" PRIME_CHAR;;
x "VARIANT_PRIMES" VARIANT_PRIMES;;
x "VARIANT" VARIANT;;

(* ------------------------------------------------------------------------- *)
(* Term substitution.                                                        *)
(* ------------------------------------------------------------------------- *)

let VSUBST = new_recursive_definition term_RECURSION
  `(VSUBST ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) /\
   (VSUBST ilist (Const x ty) = Const x ty) /\
   (VSUBST ilist (Equal ty) = Equal ty) /\
   (VSUBST ilist (Select ty) = Select ty) /\
   (VSUBST ilist (Comb s t) = Comb (VSUBST ilist s) (VSUBST ilist t)) /\
   (VSUBST ilist (Abs x ty t) =
        let ilist' = FILTER (\(s',s). ~(s = Var x ty)) ilist in
        let t' = VSUBST ilist' t in
        if EX (\(s',s). VFREE_IN (Var x ty) s' /\ VFREE_IN s t) ilist'
        then let z = VARIANT t' x ty in
             let ilist'' = CONS (Var z ty,Var x ty) ilist' in
             Abs z ty (VSUBST ilist'' t)
        else Abs x ty t')`;;

x "VSUBST" VSUBST;;

(* ------------------------------------------------------------------------- *)
(* Preservation of type.                                                     *)
(* ------------------------------------------------------------------------- *)

let VSUBST_HAS_TYPE = prove
 (`!tm ty ilist.
        tm has_type ty /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
        ==> (VSUBST ilist tm) has_type ty`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `tty:type`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    SIMP_TAC[REV_ASSOCD; MEM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; PAIR_EQ] THEN
    REWRITE_TAC[ LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_CASES_TAC `(Var x ty) has_type tty` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; LEFT_EXISTS_AND_THM] THEN
    REWRITE_TAC[GSYM EXISTS_REFL] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`; `ilist:(term#term)list`] THEN
    DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:string` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `aty:type` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_MESON_TAC[term_INJ];
    SIMP_TAC[];
    SIMP_TAC[];
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(X_CHOOSE_THEN `dty:type` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(el 4 (CONJUNCTS has_type_RULES)) THEN
    EXISTS_TAC `dty:type` THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`fty:type`; `ilist:(term#term)list`] THEN STRIP_TAC THEN
  LET_TAC THEN LET_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
  REWRITE_TAC[term_DISTINCT; term_INJ; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  DISCH_THEN(X_CHOOSE_THEN `rty:type` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REPEAT LET_TAC THEN
  MATCH_MP_TAC(el 5 (CONJUNCTS has_type_RULES)) THEN
  EXPAND_TAC "t'" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXPAND_TAC ["ilist''"; "ilist'"]; EXPAND_TAC "ilist'"] THEN
  REWRITE_TAC[MEM; MEM_FILTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[has_type_RULES]);;

let VSUBST_WELLTYPED = prove
 (`!tm ty ilist.
        welltyped tm /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
        ==> welltyped (VSUBST ilist tm)`,
  MESON_TAC[VSUBST_HAS_TYPE; welltyped]);;

x "VSUBST_HAS_TYPE" VSUBST_HAS_TYPE;;
x "VSUBST_WELLTYPED" VSUBST_WELLTYPED;;

(* ------------------------------------------------------------------------- *)
(* Right set of free variables.                                              *)
(* ------------------------------------------------------------------------- *)

let REV_ASSOCD_FILTER = prove
 (`!l:(B#A)list a b d.
        REV_ASSOCD a (FILTER (\(y,x). P x) l) b =
            if P a then REV_ASSOCD a l b else b`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[REV_ASSOCD; FILTER; COND_ID] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `x:A`; `l:(B#A)list`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
  ASM_CASES_TAC `(P:A->bool) x` THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
  ASM_MESON_TAC[]);;

let VFREE_IN_VSUBST = prove
 (`!tm u uty ilist.
      VFREE_IN (Var u uty) (VSUBST ilist tm) <=>
        ?y ty. VFREE_IN (Var y ty) tm /\
               VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[VFREE_IN; VSUBST; term_DISTINCT] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[term_INJ];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN LET_TAC THEN LET_TAC THEN
  COND_CASES_TAC THEN REPEAT LET_TAC THEN
  ASM_REWRITE_TAC[VFREE_IN] THENL
   [MAP_EVERY EXPAND_TAC ["ilist''"; "ilist'"];
    EXPAND_TAC "t'" THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "ilist'"] THEN
  SIMP_TAC[REV_ASSOCD; REV_ASSOCD_FILTER] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN] THEN
  REWRITE_TAC[TAUT `(if ~b then x:bool else y) <=> (if b then y else x)`] THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b <=> ~(~a ==> ~b)`] THEN
  SIMP_TAC[TAUT `(if b then F else c) <=> ~b /\ c`] THEN
  MATCH_MP_TAC(TAUT
   `(a ==> ~c) /\ (~a ==> (b <=> c)) ==> (~(~a ==> ~b) <=> c)`) THEN
  (CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
  GEN_REWRITE_TAC LAND_CONV [term_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[NOT_IMP] THENL
   [MP_TAC(ISPECL [`VSUBST ilist' t`; `x:string`; `ty:type`] VARIANT_THM) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ilist'" THEN ASM_REWRITE_TAC[REV_ASSOCD_FILTER] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EX]) THEN
  EXPAND_TAC "ilist'" THEN
  SPEC_TAC(`ilist:(term#term)list`,`l:(term#term)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; REV_ASSOCD; VFREE_IN] THEN
  REWRITE_TAC[REV_ASSOCD; FILTER; FORALL_PAIR_THM] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[ALL] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

x "VFREE_IN_VSUBST" VFREE_IN_VSUBST;;

(* ------------------------------------------------------------------------- *)
(* Sum type to model exception-raising.                                      *)
(* ------------------------------------------------------------------------- *)

let result_INDUCT,result_RECURSION = define_type
 "result = Clash term | Result term";;

let result_INJ = injectivity "result";;

let result_DISTINCT = distinctness "result";;

x "result_INJ" result_INJ;;
x "result_INDUCT" result_INDUCT;;
x "result_DISTINCT" result_DISTINCT;;

(* ------------------------------------------------------------------------- *)
(* Discriminators and extractors. (Nicer to pattern-match...)                *)
(* ------------------------------------------------------------------------- *)

let IS_RESULT = define
 `(IS_RESULT(Clash t) = F) /\
  (IS_RESULT(Result t) = T)`;;

let IS_CLASH = define
 `(IS_CLASH(Clash t) = T) /\
  (IS_CLASH(Result t) = F)`;;

let RESULT = define
 `RESULT(Result t) = t`;;

let CLASH = define
 `CLASH(Clash t) = t`;;

x "IS_RESULT" IS_RESULT;;
x "IS_CLASH" IS_CLASH;;
x "RESULT" RESULT;;
x "CLASH" CLASH;;

(* ------------------------------------------------------------------------- *)
(* We want induction/recursion on term size next.                            *)
(* ------------------------------------------------------------------------- *)

let sizeof = new_recursive_definition term_RECURSION
 `(sizeof (Var x ty) = 1) /\
  (sizeof (Const x ty) = 1) /\
  (sizeof (Equal ty) = 1) /\
  (sizeof (Select ty) = 1) /\
  (sizeof (Comb s t) = 1 + sizeof s + sizeof t) /\
  (sizeof (Abs x ty t) = 2 + sizeof t)`;;

let SIZEOF_VSUBST = prove
 (`!t ilist. (!s' s. MEM (s',s) ilist ==> ?x ty. s' = Var x ty)
             ==> (sizeof (VSUBST ilist t) = sizeof t)`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST; sizeof] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[MEM; REV_ASSOCD; sizeof; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`s':term`; `s:term`; `l:(term#term)list`] THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[sizeof];
    ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN
  DISCH_TAC THEN X_GEN_TAC `ilist:(term#term)list` THEN DISCH_TAC THEN
  LET_TAC THEN LET_TAC THEN COND_CASES_TAC THEN
  REPEAT LET_TAC THEN REWRITE_TAC[sizeof; EQ_ADD_LCANCEL] THENL
   [ALL_TAC; ASM_MESON_TAC[MEM_FILTER]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXPAND_TAC "ilist''" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
  ASM_MESON_TAC[MEM_FILTER]);;

let sizeof_positive = prove(
  `!t. 0 < sizeof t`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[sizeof;ARITH] THEN
  REWRITE_TAC[LT_NZ] THEN
  REWRITE_TAC[ONE;TWO;ADD;NOT_SUC]);;

x "sizeof" sizeof;;
x "SIZEOF_VSUBST" SIZEOF_VSUBST;;
x "sizeof_positive" sizeof_positive;;

(* ------------------------------------------------------------------------- *)
(* Prove existence of INST_CORE.                                             *)
(* ------------------------------------------------------------------------- *)

let INST_CORE_EXISTS = prove
 (`?INST_CORE.
  (!env tyin x ty.
        INST_CORE env tyin (Var x ty) =
          let tm = Var x ty
          and tm' = Var x (TYPE_SUBST tyin ty) in
         if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') /\
  (!env tyin x ty.
        INST_CORE env tyin (Const x ty) =
          Result(Const x (TYPE_SUBST tyin ty))) /\
  (!env tyin ty.
        INST_CORE env tyin (Equal ty) = Result(Equal(TYPE_SUBST tyin ty))) /\
  (!env tyin ty.
        INST_CORE env tyin (Select ty) = Result(Select(TYPE_SUBST tyin ty))) /\
  (!env tyin s t.
        INST_CORE env tyin (Comb s t) =
            let sres = INST_CORE env tyin s in
            if IS_CLASH sres then sres else
            let tres = INST_CORE env tyin t in
            if IS_CLASH tres then tres else
            let s' = RESULT sres and t' = RESULT tres in
            Result (Comb s' t')) /\
  (!env tyin x ty t.
        INST_CORE env tyin (Abs x ty t) =
            let ty' = TYPE_SUBST tyin ty in
            let env' = CONS (Var x ty,Var x ty') env in
            let tres = INST_CORE env' tyin t in
            if IS_RESULT tres then Result(Abs x ty' (RESULT tres)) else
            let w = CLASH tres in
            if ~(w = Var x ty') then tres else
            let x' = VARIANT (RESULT(INST_CORE [] tyin t)) x ty' in
            INST_CORE env tyin (Abs x' ty (VSUBST [Var x' ty,Var x ty] t)))`,
  W(fun (asl,w) -> MATCH_MP_TAC(DISCH_ALL
   (pure_prove_recursive_function_exists w))) THEN
  EXISTS_TAC `MEASURE(\(env:(term#term)list,tyin:(type#type)list,t).
                        sizeof t)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE] THEN
  SIMP_TAC[MEM; PAIR_EQ; term_INJ; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
             GSYM EXISTS_REFL; SIZEOF_VSUBST; LE_REFL; sizeof;
                        LE_ADD; LE_ADDR; LT_ADD; LT_ADDR] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TWO;LT_NZ;NOT_SUC] THENL
  [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ] THEN
  REWRITE_TAC[ADD_ASSOC;LT_ADD;LE_ADD;sizeof_positive] THEN
  REWRITE_TAC[LE_ADDR;LT_ADDR] THEN
  REWRITE_TAC[ONE;LT_NZ;NOT_SUC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(fun tm ->
      SPECL [rand(rator tm);rand tm] ADD_SYM))) THEN
    REWRITE_TAC[ADD_ASSOC;LT_ADD;LE_ADD;sizeof_positive]);;

(* ------------------------------------------------------------------------- *)
(* So define it.                                                             *)
(* ------------------------------------------------------------------------- *)

let INST_CORE = new_specification ["INST_CORE"] INST_CORE_EXISTS;;

x "INST_CORE" INST_CORE;;

(* ------------------------------------------------------------------------- *)
(* And the overall function.                                                 *)
(* ------------------------------------------------------------------------- *)

let INST_DEF = new_definition
 `INST tyin tm = RESULT(INST_CORE [] tyin tm)`;;

x "INST_DEF" INST_DEF;;

(* ------------------------------------------------------------------------- *)
(* Various misc lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let NOT_IS_RESULT = prove
 (`!r. ~(IS_RESULT r) <=> IS_CLASH r`,
  MATCH_MP_TAC result_INDUCT THEN REWRITE_TAC[IS_RESULT; IS_CLASH]);;

let letlemma = prove
 (`(let x = t in P x) = P t`,
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Define INST_CORE_ALT                                                      *)
(* ------------------------------------------------------------------------- *)

let INST_ALT_EXISTS = prove(
 `?INST_ALT.
  (!env tyin x ty.
        INST_ALT env tyin (Var x ty) =
          let tm = Var x ty
          and tm' = Var x (TYPE_SUBST tyin ty) in
         if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') /\
  (!env tyin x ty.
        INST_ALT env tyin (Const x ty) =
          Result(Const x (TYPE_SUBST tyin ty))) /\
  (!env tyin ty.
        INST_ALT env tyin (Equal ty) = Result(Equal(TYPE_SUBST tyin ty))) /\
  (!env tyin ty.
        INST_ALT env tyin (Select ty) = Result(Select(TYPE_SUBST tyin ty))) /\
  (!env tyin s t.
        INST_ALT env tyin (Comb s t) =
            let sres = INST_ALT env tyin s in
            if IS_CLASH sres then sres else
            let tres = INST_ALT env tyin t in
            if IS_CLASH tres then tres else
            let s' = RESULT sres and t' = RESULT tres in
            Result (Comb s' t')) /\
  (!env tyin x ty t.
        INST_ALT env tyin (Abs x ty t) =
            let ty' = TYPE_SUBST tyin ty in
            let env' = CONS (Var x ty,Var x ty') env in
            let tres = INST_ALT env' tyin t in
            if IS_RESULT tres then Result(Abs x ty' (RESULT tres)) else
            let w = CLASH tres in
            if ~(w = Var x ty') then tres else
            let x' = VARIANT (RESULT(INST_ALT [] tyin t)) x ty' in
            let t' = VSUBST [Var x' ty,Var x ty] t in
            let ty' = TYPE_SUBST tyin ty in
            let env' = CONS (Var x' ty,Var x' ty') env in
            let tres = INST_ALT env' tyin t' in
            if IS_RESULT tres then Result(Abs x' ty' (RESULT tres)) else
                                   tres)`,
  W(fun (asl,w) -> MATCH_MP_TAC(DISCH_ALL
   (pure_prove_recursive_function_exists w))) THEN
  EXISTS_TAC `MEASURE(\(env:(term#term)list,tyin:(type#type)list,t).
                        sizeof t)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE] THEN
  SIMP_TAC[MEM; PAIR_EQ; term_INJ; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
             GSYM EXISTS_REFL; SIZEOF_VSUBST; LE_REFL; sizeof;
                        LE_ADD; LE_ADDR; LT_ADD; LT_ADDR] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TWO;LT_NZ;NOT_SUC] THENL
  [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof t`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ;MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1 + sizeof s`
  ] THEN
  REWRITE_TAC[ADD_ASSOC;LT_ADD;LE_ADD;sizeof_positive] THEN
  REWRITE_TAC[LE_ADDR;LT_ADDR] THEN
  REWRITE_TAC[ONE;LT_NZ;NOT_SUC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(fun tm ->
      SPECL [rand(rator tm);rand tm] ADD_SYM))) THEN
    REWRITE_TAC[ADD_ASSOC;LT_ADD;LE_ADD;sizeof_positive]);;

let INST_ALT = new_specification ["INST_ALT"] INST_ALT_EXISTS;;

x "INST_ALT" INST_ALT;;

(* ------------------------------------------------------------------------- *)
(* Property of INST_CORE                                                     *)
(* ------------------------------------------------------------------------- *)

let arith_lemma1 = prove(
  `s < 1 + s + t /\ t < 1 + s + t`,
  MESON_TAC [ADD_SYM;ADD_CLAUSES;ADD1;LT_EXISTS]);;

let arith_lemma2 = prove(
  `t < 2 + t`,
  SIMP_TAC [LT_EXISTS] THEN EXISTS_TAC `(SUC 0):num` THEN
     REWRITE_TAC [BIT1_THM;BIT0_THM;ADD_CLAUSES]);;

let INST_CORE_HAS_TYPE = prove(
  `!n tm env tyin.
        welltyped tm /\ (sizeof tm = n) /\
        (!s s'. MEM (s,s') env
                ==> ?x ty. (s = Var x ty) /\
                           (s' = Var x (TYPE_SUBST tyin ty)))
        ==> (?x ty. (INST_CORE env tyin tm =
                     Clash(Var x (TYPE_SUBST tyin ty))) /\
                    (INST_ALT env tyin tm =
                     Clash(Var x (TYPE_SUBST tyin ty))) /\
                    VFREE_IN (Var x ty) tm /\
                    ~(REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                                 env (Var x ty) = Var x ty)) \/
            (!x ty. VFREE_IN (Var x ty) tm
                    ==> (REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                                 env (Var x ty) = Var x ty)) /\
            (?tm'. (INST_CORE env tyin tm = Result tm') /\
                   (INST_ALT env tyin tm = Result tm') /\
                   tm' has_type (TYPE_SUBST tyin (typeof tm)) /\
                   (!u uty. VFREE_IN (Var u uty) tm' <=>
                                ?oty. VFREE_IN (Var u oty) tm /\
                                      (uty = TYPE_SUBST tyin oty)))`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN
  ONCE_REWRITE_TAC[INST_CORE; SIMP_RULE [letlemma] INST_ALT] THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[REV_ASSOCD; LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[RESULT; VFREE_IN; term_INJ] THEN ASM_MESON_TAC[];
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[TYPE_SUBST; RESULT; VFREE_IN; term_DISTINCT] THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES; TYPE_SUBST; VFREE_IN] THEN
    REWRITE_TAC[TYPE_SUBST; term_DISTINCT];
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[TYPE_SUBST; RESULT; VFREE_IN; term_DISTINCT] THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES; TYPE_SUBST; VFREE_IN] THEN
    REWRITE_TAC[TYPE_SUBST; term_DISTINCT];
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[TYPE_SUBST; RESULT; VFREE_IN; term_DISTINCT] THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES; TYPE_SUBST; VFREE_IN] THEN
    REWRITE_TAC[TYPE_SUBST; term_DISTINCT];
    MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN DISCH_THEN(K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC `n = sizeof(Comb s t)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `sizeof t` th) THEN
                         MP_TAC(SPEC `sizeof s` th)) THEN
    REWRITE_TAC[sizeof; arith_lemma1] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `t:term`) THEN
                         MP_TAC(SPEC `s:term` th)) THEN
    REWRITE_TAC[IMP_IMP; AND_FORALL_THM; WELLTYPED_CLAUSES] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
      DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; IS_CLASH; VFREE_IN];
      ALL_TAC] THEN
    REWRITE_TAC[TYPE_SUBST] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `s':term` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; IS_CLASH; VFREE_IN];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':term` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[VFREE_IN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `Comb s' t'` THEN
    ASM_SIMP_TAC[LET_DEF; LET_END_DEF; IS_CLASH; RESULT] THEN
    ASM_REWRITE_TAC[VFREE_IN] THEN
    ASM_REWRITE_TAC[typeof] THEN ONCE_REWRITE_TAC[has_type_CASES] THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; codomain] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN
  DISCH_THEN(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `n = sizeof (Abs x ty t)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN REPEAT LET_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `sizeof t`) THEN
  REWRITE_TAC[sizeof; arith_lemma2] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`t:term`; `env':(term#term)list`; `tyin:(type#type)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "env'" THEN (* EXPAND_TAC "env''" THEN *)
    REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':term` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[IS_RESULT] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th ->
       MP_TAC th THEN MATCH_MP_TAC MONO_FORALL THEN
       GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
       DISCH_THEN(MP_TAC o check (is_imp o concl))) THEN
       EXPAND_TAC "env'" THEN
      REWRITE_TAC[VFREE_IN; REV_ASSOCD; term_INJ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[term_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[result_INJ; UNWIND_THM1; RESULT] THEN
    MATCH_MP_TAC(TAUT `a /\ b ==> b /\ a`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
      MAP_EVERY X_GEN_TAC [`u:string`; `uty:type`] THEN
      ASM_CASES_TAC `u:string = x` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_THEN `u:string = x` SUBST_ALL_TAC THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `oty:type` THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `uty = TYPE_SUBST tyin oty` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `VFREE_IN (Var x oty) t` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      FIRST_X_ASSUM(fun th ->
       MP_TAC(SPECL [`x:string`; `oty:type`] th) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
      EXPAND_TAC "env'" THEN REWRITE_TAC[REV_ASSOCD] THEN
      ASM_MESON_TAC[term_INJ];
      REWRITE_TAC[typeof; TYPE_SUBST] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[has_type_RULES]]] THEN
  ABBREV_TAC `tres1 = INST_ALT env' tyin t` THEN
  DISCH_THEN(X_CHOOSE_THEN `z:string` (X_CHOOSE_THEN `zty:type`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC
   (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)))) THEN
  EXPAND_TAC "w" THEN REWRITE_TAC[CLASH; IS_RESULT; term_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
    DISCH_THEN(fun th ->
      DISJ1_TAC THEN REWRITE_TAC[result_INJ] THEN
      MAP_EVERY EXISTS_TAC [`z:string`; `zty:type`] THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
    EXPAND_TAC "env'" THEN ASM_REWRITE_TAC[REV_ASSOCD; term_INJ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[INST_CORE] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  ABBREV_TAC `env'' = CONS (Var x' ty,Var x' ty') env` THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  ABBREV_TAC
   `ures = INST_CORE env'' tyin (VSUBST[Var x' ty,Var x ty] t)` THEN
  ABBREV_TAC
   `ures' = INST_ALT env'' tyin (VSUBST[Var x' ty,Var x ty] t)` THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sizeof t`) THEN
  REWRITE_TAC[sizeof; arith_lemma2] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`VSUBST [Var x' ty,Var x ty] t`;
                  `env'':(term#term)list`; `tyin:(type#type)list`] th) THEN
    MP_TAC(SPECL [`t:term`; `[]:(term#term)list`; `tyin:(type#type)list`]
       th)) THEN
  REWRITE_TAC[MEM; REV_ASSOCD] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':term` MP_TAC) THEN STRIP_TAC THEN
  UNDISCH_TAC `VARIANT (RESULT (INST_CORE [] tyin t)) x ty' = x'` THEN
  ASM_REWRITE_TAC[RESULT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t':term`; `x:string`; `ty':type`] VARIANT_THM) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN DISCH_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      ASM_MESON_TAC[has_type_RULES];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIZEOF_VSUBST THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[has_type_RULES];
      ALL_TAC] THEN
    EXPAND_TAC "env''" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:string` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `vty:type` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC
               (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[IS_RESULT; CLASH] THEN
    ONCE_REWRITE_TAC[letlemma] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[VFREE_IN_VSUBST] THEN EXPAND_TAC "env''" THEN
      REWRITE_TAC[REV_ASSOCD] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[term_INJ] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN MP_TAC) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [term_INJ]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    EXPAND_TAC "env''" THEN REWRITE_TAC[REV_ASSOCD] THEN
    ASM_CASES_TAC `vty:type = ty` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[VFREE_IN_VSUBST; NOT_EXISTS_THM; REV_ASSOCD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN; term_INJ] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN
    MP_TAC(SPECL [`t':term`; `x:string`; `ty':type`] VARIANT_THM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t'':term` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IS_RESULT; result_INJ; UNWIND_THM1; result_DISTINCT] THEN
  REWRITE_TAC[RESULT] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> c /\ a) ==> a /\ b /\ c`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[typeof; TYPE_SUBST] THEN
    MATCH_MP_TAC(last(CONJUNCTS has_type_RULES)) THEN
    SUBGOAL_THEN `(VSUBST [Var x' ty,Var x ty] t) has_type (typeof t)`
      (fun th -> ASM_MESON_TAC[th; WELLTYPED_LEMMA]) THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[GSYM WELLTYPED] THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[has_type_RULES];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VFREE_IN] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`]  THEN
    ASM_REWRITE_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN; term_INJ] THEN
    SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `x /\ (if p then a /\ b else c /\ b) <=>
                      b /\ x /\ (if p then a else c)`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    REWRITE_TAC[TAUT `x /\ (if p /\ q then a else b) <=>
                      p /\ q /\ a /\ x \/ b /\ ~(p /\ q) /\ x`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM1; UNWIND_THM2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN
  REWRITE_TAC[VFREE_IN] THEN STRIP_TAC THEN
  UNDISCH_TAC `!x'' ty'.
         VFREE_IN (Var x'' ty') (VSUBST [Var x' ty,Var x ty] t)
         ==> (REV_ASSOCD (Var x'' (TYPE_SUBST tyin ty')) env''
                         (Var x'' ty') = Var x'' ty')` THEN
  DISCH_THEN(MP_TAC o SPECL [`k:string`; `kty:type`]) THEN
  REWRITE_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN] THEN
  REWRITE_TAC[VFREE_IN; term_INJ] THEN
  SIMP_TAC[] THEN
  REWRITE_TAC[TAUT `x /\ (if p then a /\ b else c /\ b) <=>
                    b /\ x /\ (if p then a else c)`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[TAUT `x /\ (if p /\ q then a else b) <=>
                    p /\ q /\ a /\ x \/ b /\ ~(p /\ q) /\ x`] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM1; UNWIND_THM2] THEN
  UNDISCH_TAC `~(Var x ty = Var k kty)` THEN
  REWRITE_TAC[term_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "env''" THEN REWRITE_TAC[REV_ASSOCD] THEN ASM_MESON_TAC[]);;

x "INST_CORE_HAS_TYPE" INST_CORE_HAS_TYPE;;

(* ------------------------------------------------------------------------- *)
(* Function for collecting type variables.                                   *)
(* ------------------------------------------------------------------------- *)

let ITLIST = new_recursive_definition list_RECURSION
 `(ITLIST f [] b = b) /\
  (ITLIST f (CONS x xs) b = f x (ITLIST f xs b))`;;

let STRING_INSERT = define
 `STRING_INSERT (x:string) xs = if MEM x xs then xs else CONS x xs`;;

let STRING_UNION = define
 `STRING_UNION xs ys = ITLIST STRING_INSERT xs ys`;;

x "ITLIST" ITLIST;;
x "STRING_INSERT" STRING_INSERT;;
x "STRING_UNION" STRING_UNION;;

let TYVARS_LEMMA =
  (SIMP_RULE [] o
   ISPEC `\(a0:type) (a1:(type)list) x1 x2. STRING_UNION x1 x2` o
   ISPEC `[]:(string)list` o
   ISPEC `\(a0:type) (a1:type) x1 x2. STRING_UNION x1 x2` o
   ISPEC `([]:(string)list)` o
   ISPEC `([]:(string)list)` o
   ISPEC `\(s:string) (x:(type)list) ts. (ts:(string)list)` o
   ISPEC `\v:string. [v]`)
  type_RECURSION;;

let TYVARS_EXISTS = prove
 (`?TYVARS.
    !v tys ty1 ty2.
     (TYVARS (Tyvar v) = [v]) /\
     (TYVARS (Tyapp v tys) = ITLIST (STRING_UNION o TYVARS) tys []) /\
     (TYVARS Bool = []) /\
     (TYVARS Ind = []) /\
     (TYVARS (Fun ty1 ty2) = STRING_UNION (TYVARS ty1) (TYVARS ty2))`,
  STRIP_ASSUME_TAC TYVARS_LEMMA THEN
  EXISTS_TAC `fn1:type->(string)list` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC list_INDUCT THEN
  ASM_SIMP_TAC [ITLIST;o_DEF]);;

let tyvars = new_specification ["tyvars"] TYVARS_EXISTS;;

let tvars = new_recursive_definition term_RECURSION
 `(tvars (Var n ty) = tyvars ty) /\
  (tvars (Const n ty) = tyvars ty) /\
  (tvars (Equal ty) = tyvars ty) /\
  (tvars (Select ty) = tyvars ty) /\
  (tvars (Comb s t) = STRING_UNION (tvars s) (tvars t)) /\
  (tvars (Abs n ty t) = STRING_UNION (tyvars ty) (tvars t))`;;

x "tyvars" tyvars;;
x "tvars" tvars;;

(* ------------------------------------------------------------------------- *)
(* Sorting strings.                                                          *)
(* ------------------------------------------------------------------------- *)

let string_lt = new_recursive_definition list_RECURSION
 `(string_lt [] t = ~((t:string) = [])) /\
  (string_lt (CONS x s) t =
     if t = [] then F else
     if x = HD t then string_lt s (TL t) else ORD x < ORD (HD t))`;;

let string_lt = prove
 (`(string_lt [] [] = F) /\
   (string_lt [] (CONS y t) = T) /\
   (string_lt (CONS x s) [] = F) /\
   (string_lt (CONS x s) (CONS y t) =
      if x = y then string_lt s t else ORD x < ORD y)`,
  SIMP_TAC [string_lt;NOT_CONS_NIL;HD;TL]);;

let INORDER_INSERT = define
 `INORDER_INSERT x xs =
    APPEND (FILTER (\y. string_lt y x) xs)
   (APPEND [x] (FILTER (\y. string_lt x y) xs))`;;

let STRING_SORT = define `
  STRING_SORT xs = ITLIST INORDER_INSERT xs []`;;

x "string_lt" string_lt;;
x "INORDER_INSERT" INORDER_INSERT;;
x "STRING_SORT" STRING_SORT;;

(* ------------------------------------------------------------------------- *)
(* Constant and type definitions. A context is a list of definitions.        *)
(* ------------------------------------------------------------------------- *)

let def_INDUCT,def_RECURSION = define_type
  "def = Axiomdef term
       | Constdef string term
       | Typedef string term string string";; (* tyname, P, absname, repname *)

let def_DISTINCT = distinctness "def";;

let def_INJ = injectivity "def";;

x "def_DISTINCT" def_DISTINCT;;
x "def_INJ" def_INJ;;
x "def_INDUCT" def_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* Types must have defined Tyapps and correct arity.                         *)
(* ------------------------------------------------------------------------- *)

let types_aux = new_recursive_definition def_RECURSION
 `(types_aux (Axiomdef t) = []) /\
  (types_aux (Constdef s t) = []) /\
  (types_aux (Typedef tyname t a r) = [(tyname,LENGTH (tvars t))])`;;

let types = define
 `types defs = concat (MAP types_aux defs)`;;

let type_ok_RULES,type_ok_INDUCT,type_ok_CASES = new_inductive_definition
  `(!n defs. type_ok defs (Tyvar n)) /\
   (!defs. type_ok defs Bool) /\
   (!defs. type_ok defs Ind) /\
   (!ty1 ty2 defs. type_ok defs ty1 /\ type_ok defs ty2 ==>
                   type_ok defs (Fun ty1 ty2)) /\
   (!n tys defs. (!ty. MEM ty tys ==> type_ok defs ty) /\
                 MEM (n,LENGTH tys) (types defs) ==>
                 type_ok defs (Tyapp n tys))`;;

x "types_aux" types_aux;;
x "types" types;;
x "type_ok_RULES" type_ok_RULES;;
x "type_ok_INDUCT" type_ok_INDUCT;;
x "type_ok_CASES" type_ok_CASES;;

(* ------------------------------------------------------------------------- *)
(* Terms must only contain defined constants and types.                      *)
(* ------------------------------------------------------------------------- *)

let consts_aux = new_recursive_definition def_RECURSION
 `(consts_aux (Axiomdef t) = []) /\
  (consts_aux (Constdef s t) = [(s,typeof t)]) /\
  (consts_aux (Typedef tyname t a r) =
     let rep_type = domain (typeof t) in
     let abs_type = Tyapp tyname (MAP Tyvar (STRING_SORT (tvars t))) in
       [(a,Fun rep_type abs_type);
        (r,Fun abs_type rep_type)])`;;

let consts = define
 `consts defs = concat (MAP consts_aux defs)`;;

let term_ok = new_recursive_definition term_RECURSION
 `(term_ok defs (Var s ty) <=> type_ok defs ty) /\
  (term_ok defs (Const s ty) <=> (type_ok defs ty /\
     (?ty2 i. MEM (s,ty2) (consts defs) /\ (TYPE_SUBST i ty2 = ty)))) /\
  (term_ok defs (Equal ty) <=> type_ok defs ty) /\
  (term_ok defs (Select ty) <=> type_ok defs ty) /\
  (term_ok defs (Comb x y) <=> (term_ok defs x /\ term_ok defs y)) /\
  (term_ok defs (Abs s ty x) <=> (type_ok defs ty /\ term_ok defs x))`;;

x "consts_aux" consts_aux;;
x "consts" consts;;
x "term_ok" term_ok;;

(* ------------------------------------------------------------------------- *)
(* A context is well-formed if all definitions are allowed in that order.    *)
(* ------------------------------------------------------------------------- *)

let def_ok = new_recursive_definition def_RECURSION
 `(def_ok (Axiomdef t) (defs:(def)list) <=>
     t has_type Bool /\ welltyped t /\ term_ok defs t) /\
  (def_ok (Constdef s t) (defs:(def)list) <=>
     CLOSED t /\ welltyped t /\ term_ok defs t /\
     ~(MEM s (MAP FST (consts defs))) /\ ~(s = [CHR 61]) /\
     !v. MEM v (tvars t) ==> MEM v (tyvars (typeof t))) /\
  (def_ok (Typedef tyname t a r) defs <=>
     CLOSED t /\ welltyped t /\ term_ok defs t /\
     ~(MEM tyname (MAP FST (types defs))) /\
     ~(MEM a (MAP FST (consts defs))) /\ ~(a = [CHR 61]) /\
     ~(MEM r (MAP FST (consts defs))) /\ ~(r = [CHR 61]) /\
     ?ty. (typeof t = Fun ty Bool))`;;

let context_ok = new_recursive_definition list_RECURSION
 `(context_ok [] = T) /\
  (context_ok (CONS def defs) <=> (def_ok def defs /\ context_ok defs))`;;

let welltyped_in = define
 `welltyped_in t defs <=> welltyped t /\ term_ok defs t /\ context_ok defs`;;

x "def_ok" def_ok;;
x "context_ok" context_ok;;
x "welltyped_in" welltyped_in;;

(* ------------------------------------------------------------------------- *)
(* Put everything together into a deductive system.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|-",(11,"right"));;

let proves_RULES,proves_INDUCT,proves_CASES = new_inductive_definition
 `(!t defs.
        welltyped_in t defs
        ==> defs, [] |- t === t) /\
  (!asl1 asl2 l m1 m2 r defs.
        defs, asl1 |- l === m1 /\ defs, asl2 |- m2 === r /\ ACONV m1 m2
        ==> defs, TERM_UNION asl1 asl2 |- l === r) /\
  (!asl1 l1 r1 asl2 l2 r2 defs.
        defs, asl1 |- l1 === r1 /\
        defs, asl2 |- l2 === r2 /\ welltyped(Comb l1 l2)
        ==> defs, TERM_UNION asl1 asl2 |- Comb l1 l2 === Comb r1 r2) /\
  (!asl x ty l r defs.
        ~(EX (VFREE_IN (Var x ty)) asl) /\ type_ok defs ty /\
        defs, asl |- l === r
        ==> defs, asl |- (Abs x ty l) === (Abs x ty r)) /\
  (!x ty t defs.
        welltyped_in t defs /\ type_ok defs ty
        ==> defs, [] |- Comb (Abs x ty t) (Var x ty) === t) /\
  (!p defs.
        p has_type Bool /\ welltyped_in p defs
        ==> defs, [p] |- p) /\
  (!asl1 asl2 p q p' defs.
        defs, asl1 |- p === q /\ defs, asl2 |- p' /\ ACONV p p'
        ==> defs, TERM_UNION asl1 asl2 |- q) /\
  (!asl1 asl2 c1 c2 defs.
        defs, asl1 |- c1 /\ defs, asl2 |- c2
        ==> defs, TERM_UNION (FILTER((~) o ACONV c2) asl1)
                             (FILTER((~) o ACONV c1) asl2)
               |- c1 === c2) /\
  (!tyin asl p defs.
        (!s s'. MEM (s',s) tyin ==> type_ok defs s') /\
        defs, asl |- p
        ==> defs, MAP (INST tyin) asl |- INST tyin p) /\
  (!ilist asl p defs.
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty /\
                                            welltyped_in s' defs) /\
        defs, asl |- p
        ==> defs, MAP (VSUBST ilist) asl |- VSUBST ilist p) /\
  (!asl p d defs.
        defs, asl |- p /\ def_ok d defs
        ==> (CONS d defs), asl |- p) /\
  (!t defs.
        context_ok defs /\ MEM (Axiomdef t) defs
        ==> defs, [] |- t) /\
  (!n t defs.
        context_ok defs /\ MEM (Constdef n t) defs
        ==> defs, [] |- Const n (typeof t) === t) /\
  (!tyname t a r defs x rep_type abs_type y d.
        (d = Typedef tyname t a r) /\
        (rep_type = domain (typeof t)) /\
        (abs_type = Tyapp tyname (MAP Tyvar (STRING_SORT (tvars t)))) /\
        context_ok (CONS d defs) /\ defs, [] |- Comb t y
        ==> (CONS d defs), []
             |- Comb (Const a (Fun rep_type abs_type))
                     (Comb (Const r (Fun abs_type rep_type))
                           (Var x abs_type)) === Var x abs_type) /\
  (!tyname t a r defs x rep_type abs_type y d.
        (d = Typedef tyname t a r) /\
        (rep_type = domain (typeof t)) /\
        (abs_type = Tyapp tyname (MAP Tyvar (STRING_SORT (tvars t)))) /\
        context_ok (CONS d defs) /\ defs, [] |- Comb t y
        ==> (CONS d defs), []
             |- Comb t (Var x rep_type) ===
                Comb (Const r (Fun abs_type rep_type))
                     (Comb (Const a (Fun rep_type abs_type))
                           (Var x rep_type)) === Var x rep_type)`;;

x "proves_RULES" proves_RULES;;
x "proves_INDUCT" proves_INDUCT;;
x "proves_CASES" proves_CASES;;

logfile_end ();;
stop_logging ();;
