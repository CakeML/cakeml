(*
  Prove correctness of the monadic functions, i.e. prove that they are
  faithful to the inference rules of the Candle logic.
*)
open preamble mlstringTheory ml_monadBaseTheory holKernelTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory

val _ = new_theory "holKernelProof";

val _ = ParseExtras.temp_loose_equality();
val _ = hide"str";
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_overload_on ("raise_clash", ``raise_Clash``);
val _ = temp_overload_on ("handle_clash", ``handle_Clash``);

val _ = hide "state";

val _ = type_abbrev("M", ``: hol_refs -> ('a, hol_exn) exc # hol_refs``);

Theorem rev_assocd_thm:
   rev_assocd = REV_ASSOCD
Proof
  SIMP_TAC std_ss [FUN_EQ_THM] \\ Induct_on `x'`
  \\ ONCE_REWRITE_TAC [rev_assocd_def] \\ SRW_TAC [] [REV_ASSOCD]
  \\ Cases_on `h` \\ SRW_TAC [] [REV_ASSOCD]
QED

val REPLICATE_GENLIST = rich_listTheory.REPLICATE_GENLIST

val REPLICATE_11 = Q.prove(
  `!m n x. (REPLICATE n x = REPLICATE m x) = (m = n)`,
  Induct \\ Cases \\ SRW_TAC [] [rich_listTheory.REPLICATE]);

val _ = temp_overload_on("impossible_term",``holSyntax$Comb (Var (strlit "x") Bool) (Var (strlit "x") Bool)``);

(* ------------------------------------------------------------------------- *)
(* case_eq theorems                                                          *)
(* ------------------------------------------------------------------------- *)

val case_eq_thms =
  CaseEqs ["prod", "list", "option", "type", "term", "thm", "update",
           "hol_exn", "exc"];

(* ------------------------------------------------------------------------- *)
(* Refinement invariants                                                     *)
(* ------------------------------------------------------------------------- *)

val TYPE_def = Define `
  TYPE ctxt ty = type_ok (tysof ctxt) ty`;

val TERM_def = Define `
  TERM ctxt tm = term_ok (sigof (ctxt:update list)) tm`;

val CONTEXT_def = Define `
  CONTEXT ctxt = ctxt extends init_ctxt`;

val THM_def = Define `
  THM ctxt (Sequent asl c) = ((thyof ctxt, asl) |- c)`;

val lift_tm_def = Define `lift_tm c = Sequent [] c`;

val STATE_def = Define `
  STATE ctxt state =
      (ctxt = state.the_context) /\ CONTEXT ctxt /\
      (state.the_type_constants = type_list ctxt) /\
      (state.the_term_constants = const_list ctxt) /\
      (state.the_axioms = MAP lift_tm (axexts ctxt))`;

(* ------------------------------------------------------------------------- *)
(* impossible term lemmas                                                    *)
(* ------------------------------------------------------------------------- *)

val term_ok_impossible_term = Q.prove(
  `~(term_ok defs impossible_term)`,
  simp[term_ok_def])

val impossible_term_thm = Q.prove(
  `TERM defs tm ==> tm <> impossible_term`,
  SIMP_TAC std_ss [TERM_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [term_ok_impossible_term])

val Abs_Var = Q.prove(
  `TERM defs (Abs v tm) ==> ?s ty. v = Var s ty`,
  simp[TERM_def,term_ok_def] >> rw[])

(* ------------------------------------------------------------------------- *)
(* invariant lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

val CONTEXT_ALL_DISTINCT = Q.prove(
  `CONTEXT defs ⇒ ALL_DISTINCT (MAP FST (type_list defs)) ∧
                   ALL_DISTINCT (MAP FST (const_list defs))`,
  rw[CONTEXT_def] >>
  METIS_TAC[extends_ALL_DISTINCT,init_ALL_DISTINCT])

val STATE_ALL_DISTINCT = Q.prove(
  `STATE defs s ⇒ ALL_DISTINCT (MAP FST s.the_type_constants) ∧
                   ALL_DISTINCT (MAP FST s.the_term_constants)`,
  rw[STATE_def] >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  qpat_x_assum`X = const_list Y`(assume_tac o SYM) >> fs[] >>
  fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val TYPE_Tyapp = Q.prove(
  `MEM (tyop,LENGTH args) r.the_type_constants /\
    STATE defs r /\ EVERY (TYPE defs) args ==>
    TYPE defs (Tyapp tyop args)`,
  rw[EVERY_MEM,TYPE_def] >>
  imp_res_tac STATE_ALL_DISTINCT >>
  rw[type_ok_def,EVERY_MAP,EVERY_MEM] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  rfs[STATE_def])

val CONTEXT_std_sig = Q.prove(
  `CONTEXT defs ⇒ is_std_sig (sigof defs)`,
  rw[CONTEXT_def] >>
  imp_res_tac extends_theory_ok >> fs[init_theory_ok] >>
  imp_res_tac theory_ok_sig >> fs[is_std_sig_def])

val CONTEXT_fun = Q.prove(
  `CONTEXT defs ⇒
      ∀a. MEM (strlit"fun",a) (type_list defs) ⇔ (a = 2)`,
  rw[] >> imp_res_tac CONTEXT_ALL_DISTINCT >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  EQ_TAC >> rw[] >> res_tac >> fs[] >>
  imp_res_tac ALOOKUP_MEM)

val TYPE = Q.prove(
  `(STATE defs state ==> TYPE defs (Tyvar v)) /\
    (TYPE defs (Tyapp op tys) ==> EVERY (TYPE defs) tys)`,
  conj_tac >- (
    simp[STATE_def,TYPE_def,EVERY_MEM] >>
    rw[] >> simp[type_ok_def] ) >>
  rw[EVERY_MEM,TYPE_def] >>
  fs[type_ok_def,EVERY_MAP,EVERY_MEM]);

val TERM = Q.prove(
  `(TERM defs (Var n ty) ==> TYPE defs ty) /\
    (TERM defs (Const n ty) ==> TYPE defs ty) /\
    (TERM defs (Abs (Var v ty) x) ==> TERM defs x /\ TYPE defs ty) /\
    (TERM defs (Comb x y) ==> TERM defs x /\ TERM defs y)`,
  rw[TERM_def,TYPE_def] >> fs[term_ok_def])

val TYPE_Fun = Q.prove(
  `CONTEXT defs ∧ TYPE defs ty1 /\ TYPE defs ty2 ==>
    TYPE defs (Tyapp (strlit "fun") [ty1;ty2])`,
  rw[TYPE_def,type_ok_def] >>
  imp_res_tac CONTEXT_fun >>
  METIS_TAC[ALOOKUP_ALL_DISTINCT_MEM,CONTEXT_ALL_DISTINCT]);

val TERM_Var_SIMP = Q.prove(
  `(TERM defs (Var n ty) = TYPE defs ty)`,
  rw[TERM_def,TYPE_def,term_ok_def]);

val TERM_Var = Q.prove(
  `TYPE defs ty ==> TERM defs (Var n ty)`,
  METIS_TAC [TERM_Var_SIMP]);

val IMP_TERM_Abs = Q.prove(
  `TERM defs (Var str ty) /\ TERM defs bod ==>
    TERM defs (Abs (Var str ty) bod)`,
  fs[TERM_def,term_ok_def]);

val IMP_TERM_Comb = Q.prove(
  `TERM defs f /\
    TERM defs a /\
    (typeof a = ty1) /\
    (typeof f = Fun ty1 ty2) ==>
    TERM defs (Comb f a)`,
  rw[TERM_def,term_ok_def] >>
  METIS_TAC[term_ok_welltyped])

val TERM_Abs = Q.prove(
  `TERM defs (Abs (Var v ty) tm) <=> TYPE defs ty /\ TERM defs tm`,
  rw[TERM_def,term_ok_def,TYPE_def]);

val INST_CORE_LEMMA =
  INST_CORE_HAS_TYPE |> Q.SPECL [`holSyntax$sizeof tm`,`tm`,`[]`,`tyin`]
  |> SIMP_RULE std_ss [MEM,REV_ASSOCD] |> Q.GENL [`tyin`,`tm`]

val INST_CORE_EMPTY = Q.prove(
  `!tm env.
      welltyped tm /\ EVERY (\(x,y). x = y) env ==>
      (holSyntax$INST_CORE env [] tm = Result tm)`,
  completeInduct_on `holSyntax$sizeof tm` \\ Cases \\ REPEAT STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [INST_CORE_def] \\ SIMP_TAC std_ss [TYPE_SUBST_NIL]
    \\ sg `REV_ASSOCD (Var m t) env (Var m t) = Var m t` THEN1
     (POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `env` \\ FULL_SIMP_TAC std_ss [REV_ASSOCD]
      \\ Cases \\ FULL_SIMP_TAC std_ss [REV_ASSOCD,EVERY_DEF])
    \\ FULL_SIMP_TAC std_ss [LET_THM])
  THEN1 (ONCE_REWRITE_TAC [INST_CORE_def] \\ SIMP_TAC std_ss [TYPE_SUBST_NIL])
  THEN1
   (FULL_SIMP_TAC std_ss [sizeof_def,term_ok_def]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ ONCE_REWRITE_TAC [INST_CORE_def]
    \\ qmatch_assum_rename_tac`v = 1 + holSyntax$sizeof a0 + holSyntax$sizeof a1`
    \\ FIRST_X_ASSUM (fn th => MP_TAC (Q.SPECL [`a0`,`env`] th) THEN
                               MP_TAC (Q.SPECL [`a1`,`env`] th))
    \\ simp[] >> fs[] ) >>
  ONCE_REWRITE_TAC [INST_CORE_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_SUBST_NIL,PULL_FORALL,sizeof_def]
  >> fs[]
  >> simp[])
  |> Q.SPECL [`tm`,`[]`] |> SIMP_RULE std_ss [EVERY_DEF] |> GEN_ALL;

val THM = Q.prove(
  `THM defs (Sequent asl c) ==> EVERY (TERM defs) asl /\ TERM defs c`,
  SIMP_TAC std_ss [THM_def] \\ SIMP_TAC std_ss [EVERY_MEM] >>
  strip_tac >> imp_res_tac proves_term_ok >>
  fs[EVERY_MEM,TERM_def,MEM_MAP,PULL_EXISTS])

val type_IND = type_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL
  |> Q.GEN`P`

val type_subst_EMPTY = Q.prove(
  `!ty. type_subst [] ty = ty`,
  HO_MATCH_MP_TAC type_IND
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once type_subst_def]
  \\ SIMP_TAC std_ss [rev_assocd_thm,REV_ASSOCD,LET_DEF]
  \\ sg `MAP (\a. type_subst [] a) l = l` \\ FULL_SIMP_TAC std_ss []
  \\ Induct_on `l` \\ FULL_SIMP_TAC std_ss [MAP,EVERY_DEF]);

val MAP_EQ_2 = Q.prove(
  `(MAP f l = [x;y]) ⇔ ∃x0 y0. (l = [x0;y0]) ∧ (x = f x0) ∧ (y = f y0)`,
  Cases_on`l`>>simp[]>>Cases_on`t`>>simp[]>>METIS_TAC[])

val sequent_has_type_bool = Q.prove(
  `(d,h) |- c ⇒ EVERY (λt. t has_type Bool) (c::h)`,
  strip_tac >> imp_res_tac proves_term_ok >> fs[EVERY_MEM])

val THM_term_ok_bool = Q.prove(
  `THM defs (Sequent asl p) ⇒
    EVERY (λt. term_ok (sigof defs) t ∧ (typeof t = Bool)) (p::asl)`,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [THM_def]
  \\ IMP_RES_TAC sequent_has_type_bool
  \\ IMP_RES_TAC proves_term_ok
  \\ FULL_SIMP_TAC std_ss [TERM_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM]
  \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [WELLTYPED_LEMMA])

(* TODO move *)
Theorem ALOOKUP_ALL_DISTINCT_MEM_EXISTS:
   (?k. MEM (k,v) alist) /\
    ALL_DISTINCT (MAP FST alist)
    ==>
    ?k. ALOOKUP alist k = SOME v
Proof
  rw [] \\ qexists_tac `k` \\ metis_tac [ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem the_term_constants_TYPE:
   STATE defs refs
   ==>
   EVERY (\(_, ty). TYPE defs ty) refs.the_term_constants
Proof
  rw [STATE_def, TYPE_def, EVERY_MEM, MEM_FLAT, UNCURRY]
  \\ imp_res_tac CONTEXT_ALL_DISTINCT
  \\ fs [CONTEXT_def]
  \\ drule extends_theory_ok \\ simp [init_theory_ok]
  \\ rw [theory_ok_def]
  \\ first_x_assum (qspec_then `SND e` match_mp_tac)
  \\ simp [IN_FRANGE_FLOOKUP]
  \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM_EXISTS \\ fs []
  \\ fs [MEM_FLAT]
  \\ qexists_tac `FST e` \\ fs []
  \\ asm_exists_tac \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* Verification of type functions                                            *)
(* ------------------------------------------------------------------------- *)
val can_thm = Q.prove(
  `can f x s = case f x s of (Success _,s) => (Success T,s) |
                              (_,s) => (Success F,s)`,
  SIMP_TAC std_ss [can_def,st_ex_ignore_bind_def,otherwise_def]
  \\ Cases_on `f x s` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]);

val assoc_thm = Q.prove(
  `!xs y z s s'.
      (assoc y xs s = (z, s')) ==>
      (s' = s) /\ (!i. (z = Success i) ==> MEM (y,i) xs) /\
                  (!e. (z = Failure e) ==> !i. ~MEM (y,i) xs)`,
  Induct \\ SIMP_TAC (srw_ss()) [Once assoc_def,raise_Fail_def]
  \\ Cases \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ Cases_on `y = q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ METIS_TAC []);

val get_type_arity_thm = Q.prove(
  `!name s z s'.
      (get_type_arity name s = (z,s')) ==> (s' = s) /\
      (!i. (z = Success i) ==> MEM (name,i) s.the_type_constants) /\
      (!e. (z = Failure e) ==> !i. ~MEM (name,i) s.the_type_constants)`,
  SIMP_TAC (srw_ss()) [get_type_arity_def,st_ex_bind_def,
    get_the_type_constants_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC assoc_thm);

Theorem mk_vartype_thm:
   !name s.
      STATE s.the_context s ⇒
      TYPE s.the_context (mk_vartype name)
Proof
  SIMP_TAC (srw_ss()) [mk_vartype_def,TYPE_def,type_ok_def,STATE_def]
QED

Theorem mk_type_thm:
   !tyop args s z s'.
      STATE defs s /\ EVERY (TYPE defs) args /\
      (mk_type (tyop,args) s = (z,s')) ==> (s' = s) /\
      ((tyop = (strlit "fun")) /\ (LENGTH args = 2) ==> ?i. z = Success i) /\
      !i. (z = Success i) ==> TYPE defs i /\ (i = Tyapp tyop args)
Proof
  SIMP_TAC std_ss [mk_type_def,try_def,st_ex_bind_def,otherwise_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `get_type_arity tyop s`
  \\ IMP_RES_TAC get_type_arity_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def]
  \\ SRW_TAC [] [st_ex_return_def]
  \\ IMP_RES_TAC TYPE_Tyapp
  \\ fs[STATE_def] >> METIS_TAC[CONTEXT_fun]
QED

Theorem dest_type_thm:
   !ty s z s'.
      STATE defs s /\
      (dest_type ty s = (z,s')) /\ TYPE defs ty ==> (s' = s) /\
      !i. (z = Success i) ==> ?n tys. (ty = Tyapp n tys) /\ (i = (n,tys)) /\
                                     EVERY (TYPE defs) tys
Proof
  Cases \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def,raise_Fail_def,st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_def,EVERY_MEM] \\ SRW_TAC [] []
  >> fs[type_ok_def,EVERY_MAP,EVERY_MEM]
QED

Theorem dest_vartype_thm:
   !ty s z s'.
      (dest_vartype ty s = (z,s')) ==> (s' = s) /\
      !i. (z = Success i) ==> (ty = Tyvar i)
Proof
  Cases \\ FULL_SIMP_TAC (srw_ss())
    [dest_vartype_def,raise_Fail_def,st_ex_return_def]
QED

Theorem is_type_thm:
   !ty. is_type ty = ?s tys. ty = Tyapp s tys
Proof
  Cases \\ SIMP_TAC (srw_ss()) [is_type_def]
QED

Theorem is_vartype_thm:
   !ty. is_vartype ty = ?s. ty = Tyvar s
Proof
  Cases \\ SIMP_TAC (srw_ss()) [is_vartype_def]
QED

val tyvars_thm = Q.prove(
  `!ty s. MEM s (holKernel$tyvars ty) = MEM s (holSyntax$tyvars ty)`,
  HO_MATCH_MP_TAC holKernelTheory.tyvars_ind \\ REPEAT STRIP_TAC
  \\ Cases_on `ty` \\ FULL_SIMP_TAC (srw_ss()) [type_11,type_distinct]
  \\ SIMP_TAC (srw_ss()) [Once holKernelTheory.tyvars_def,
       Once holSyntaxTheory.tyvars_def]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.FOLDR_MAP]
  \\ Induct_on `l`
  \\ SIMP_TAC (srw_ss()) [Once itlist_def,FOLDR,MEM_union,MEM_LIST_UNION]
  \\ METIS_TAC []);

Theorem type_subst:
   !i ty.
      (type_subst i ty = TYPE_SUBST i ty) /\
      (EVERY (\(x,y). TYPE s x /\ TYPE s y) i /\ TYPE s ty ==>
       TYPE s (type_subst i ty))
Proof
  HO_MATCH_MP_TAC type_subst_ind \\ STRIP_TAC \\ Cases THEN1
   (SIMP_TAC (srw_ss()) [Once type_subst_def] >>
    SIMP_TAC (srw_ss()) [Once type_subst_def]
    \\ Induct_on `i` \\ TRY Cases \\ ONCE_REWRITE_TAC [rev_assocd_def]
    \\ SIMP_TAC (srw_ss()) [REV_ASSOCD,MAP]
    \\ IF_CASES_TAC \\ FULL_SIMP_TAC std_ss []) >>
  srw_tac[][] >> srw_tac[][Once type_subst_def] >> srw_tac[][] >>
  TRY(
    fs[markerTheory.Abbrev_def] >>
    TRY (match_mp_tac EQ_TRANS >>
         first_assum(match_exists_tac o concl)) >>
    rw[MAP_EQ_f] ) >>
  fs[TYPE_def,type_ok_def,EVERY_MAP,EVERY_MEM]
QED

Theorem mk_fun_ty_thm:
   !ty1 ty2 s z s'.
      STATE defs s /\ EVERY (TYPE defs) [ty1;ty2] /\
      (mk_fun_ty ty1 ty2 s = (z,s')) ==> (s' = s) /\
      ?i. (z = Success i) /\ (i = Tyapp (strlit "fun") [ty1;ty2]) /\ TYPE defs i
Proof
  SIMP_TAC std_ss [mk_fun_ty_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mk_type_thm \\ FULL_SIMP_TAC (srw_ss()) []
QED

(* ------------------------------------------------------------------------- *)
(* Verification of term functions                                            *)
(* ------------------------------------------------------------------------- *)

val _ = temp_overload_on("aty",``(Tyvar (strlit "A")):type``);

val get_const_type_thm = Q.prove(
  `!name s z s'.
      (get_const_type name s = (z,s')) ==> (s' = s) /\
      (!i. (z = Success i) ==> MEM (name,i) s.the_term_constants) /\
      (!e. (z = Failure e) ==> !i. ~(MEM (name,i) s.the_term_constants))`,
  SIMP_TAC (srw_ss()) [get_const_type_def,st_ex_bind_def,
    get_the_term_constants_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC assoc_thm);

val term_type_def = Define `
  term_type tm =
    case tm of
      Var _ ty => ty
    | Const _ ty => ty
    | Comb s _ => (case term_type s of Tyapp (strlit "fun") (_::ty1::_) => ty1
                                    | _ => Tyvar (strlit ""))
    | Abs (Var _ ty) t => Tyapp (strlit "fun") [ty; term_type t]
    | _ => Tyvar (strlit "")`

val term_type = Q.prove(
  `!defs tm. CONTEXT defs ∧ TERM defs tm ==>
    (term_type tm = typeof tm) /\
    TYPE defs (term_type tm)`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ STRIP_TAC \\ Induct \\ ONCE_REWRITE_TAC [term_type_def]
  \\ SIMP_TAC (srw_ss()) [typeof_def]
  \\ rw[] >> imp_res_tac TERM >> fs[] >>
  fs[TERM_def,term_ok_def] >> rfs[] >>
  TRY(rw[Once term_type_def]>>NO_TAC)>>
  rw[]>>fs[term_ok_def]>>rw[]>>
  TRY(fs[TYPE_def,type_ok_def]>>NO_TAC)>>
  imp_res_tac CONTEXT_std_sig >>
  fs[TYPE_def,type_ok_def,is_std_sig_def])

Theorem type_of_has_type:
   !tm refs ty refs'.
     STATE defs refs /\
     TERM defs tm /\
     (type_of tm refs = (Success ty, refs'))
     ==>
     tm has_type ty /\
     (typeof tm = ty)
Proof
  Induct \\ rpt gen_tac \\ once_rewrite_tac [type_of_def] \\ fs []
  \\ fs [st_ex_return_def, st_ex_bind_def, raise_Fail_def] \\ rw []
  \\ once_rewrite_tac [holSyntaxTheory.has_type_rules]
  \\ fs [TERM_def]
  \\ fs [holSyntaxTheory.term_ok_def]
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []
  >-
   (fs [dest_type_def, raise_Fail_def, st_ex_return_def]
    \\ pop_assum mp_tac
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ match_mp_tac (CONJUNCTS holSyntaxTheory.has_type_rules |> el 3)
    \\ last_x_assum drule
    \\ disch_then drule \\ rw []
    \\ qexists_tac `typeof tm'` \\ fs []
    \\ fs [holSyntaxExtraTheory.WELLTYPED])
  >-
   (fs [dest_type_def, raise_Fail_def, st_ex_return_def]
    \\ pop_assum mp_tac
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ last_x_assum drule
    \\ disch_then drule \\ rw [])
  \\ fs [mk_fun_ty_def, mk_type_def, st_ex_bind_def, try_def, otherwise_def]
  \\ fs [get_type_arity_def, get_the_type_constants_def, st_ex_bind_def]
  \\ fs [st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ last_x_assum drule
  \\ disch_then drule \\ rw []
  \\ simp [holSyntaxTheory.has_type_rules]
QED

val type_of_thm = Q.prove(
  `!tm. TERM defs tm /\ STATE defs s ==>
         (type_of tm s = (Success (term_type tm),s))`,
  HO_MATCH_MP_TAC type_of_ind \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `CONTEXT defs` by fs[STATE_def]
  \\ Cases_on `tm` \\ ONCE_REWRITE_TAC [type_of_def]
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def,typeof_def]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ TRY (FULL_SIMP_TAC (srw_ss()) [Once term_type_def] \\ NO_TAC)
  THEN1
   (ONCE_REWRITE_TAC [st_ex_bind_def]
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [st_ex_bind_def]
    \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
    \\ reverse (sg `?ty1 ty2. term_type t = Tyapp (strlit "fun") [ty1;ty2]`) THEN1
     (FULL_SIMP_TAC (srw_ss()) [st_ex_return_def,codomain_def]
      \\ IMP_RES_TAC TYPE \\ ASM_SIMP_TAC (srw_ss()) [EVERY_DEF,Once term_type_def])
    \\ fs[TERM_def,term_ok_def] >>
    imp_res_tac term_type >> fs[TERM_def])
  \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC (srw_ss()) [Once term_type_def]
  \\ rw[st_ex_bind_def]
  \\ Cases_on `mk_fun_ty ty (term_type t0) s`
  \\ FULL_SIMP_TAC std_ss []
  \\ sg `EVERY (TYPE defs) [ty; term_type t0]`
  THEN1 FULL_SIMP_TAC std_ss [EVERY_DEF,term_type]
  \\ IMP_RES_TAC mk_fun_ty_thm
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_bind_def]);

val alphavars_thm = Q.prove(
  `!env.
      STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 /\
      EVERY (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
      (alphavars env tm1 tm2 = ALPHAVARS env (tm1, tm2))`,
  Induct \\ SIMP_TAC (srw_ss()) [Once alphavars_def,ALPHAVARS_def]
  \\ Cases \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val raconv_thm = Q.prove(
  `!tm1 tm2 env.
      STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 /\
      EVERY (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
      (raconv env tm1 tm2 = RACONV env (tm1, tm2))`,
  Induct THEN1
   (Cases_on `tm2` >> simp[Once raconv_def, Once RACONV] >> rw[] >>
    IMP_RES_TAC alphavars_thm)
  THEN1
   (Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,RACONV]
    \\ SRW_TAC [] [RACONV,domain_def]
    \\ IMP_RES_TAC TERM
    \\ IMP_RES_TAC Abs_Var
    \\ FULL_SIMP_TAC (srw_ss()) [RACONV,domain_def])
  THEN1
   (Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,RACONV]
    \\ SRW_TAC [] [RACONV] \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ imp_res_tac Abs_Var \\ simp[RACONV])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,RACONV]
  \\ IMP_RES_TAC Abs_Var
  \\ SRW_TAC [] [RACONV]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Abs (Var s4 ty4) t4)`
  \\ Q.PAT_X_ASSUM `!tm2.bbb` (MP_TAC o Q.SPECL
        [`t4`,`((Var s' ty,Var s4 ty4)::env)`])
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ impl_tac
  THEN1 (REPEAT STRIP_TAC \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])

Theorem aconv_thm:
   !tm1 tm2 env.
      STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 ==>
      (aconv tm1 tm2 = ACONV tm1 tm2)
Proof
  SIMP_TAC std_ss [aconv_def,ACONV_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (raconv_thm |> Q.SPECL [`t1`,`t2`,`[]`]
       |> SIMP_RULE std_ss [EVERY_DEF,MAP])
  \\ FULL_SIMP_TAC std_ss []
QED

Theorem is_term_thm:
   (is_var tm = ?n ty. tm = Var n ty) /\
    (is_const tm = ?n ty. tm = Const n ty) /\
    (is_abs tm = ?v x. tm = Abs v x) /\
    (is_comb tm = ?x y. tm = Comb x y)
Proof
  Cases_on `tm` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []
QED

Theorem mk_var_thm:
   STATE defs s /\ TYPE defs ty ==> TERM defs (mk_var(v,ty))
Proof
  SIMP_TAC std_ss [mk_var_def] \\ METIS_TAC [TERM_Var]
QED

Theorem mk_abs_thm:
   !res.
      TERM defs bvar /\ TERM defs bod /\ (mk_abs(bvar,bod) s = (res,s1)) ==>
      (s1 = s) /\ !t. (res = Success t) ==> TERM defs t /\ (t = Abs bvar bod)
Proof
  FULL_SIMP_TAC std_ss [mk_abs_def] \\ Cases_on `bvar`
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def,raise_Fail_def,IMP_TERM_Abs]
QED

val mk_comb_thm = Q.prove(
  `TERM defs f /\ TERM defs a /\ STATE defs s /\
    (mk_comb(f,a)s = (res,s1)) ==>
    (s1 = s) /\
    (!t. (res = Failure t) ==> !ty. term_type f <> Fun (term_type a) ty) /\
    !t. (res = Success t) ==> TERM defs t /\ (t = Comb f a)`,
  SIMP_TAC std_ss [mk_comb_def,st_ex_bind_def] \\ STRIP_TAC
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `f`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `a`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_X_ASSUM `xxx = (res,s1)` (ASSUME_TAC o GSYM)
  \\ Cases_on `term_type f` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def]
  \\ IMP_RES_TAC term_type
  \\ IMP_RES_TAC type_of_thm
  \\ FULL_SIMP_TAC (srw_ss()) [TYPE_def]
  \\ Q.PAT_X_ASSUM `term_type f = Fun h h'` ASSUME_TAC
  \\ Q.PAT_X_ASSUM `term_type a = h` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [MAP]
  \\ METIS_TAC [IMP_TERM_Comb,STATE_def]);

Theorem dest_var_thm:
   TERM defs v /\ STATE defs s ==>
    (dest_var v s = (res,s')) ==>
    (s' = s) /\ !n ty. (res = Success (n,ty)) ==> TYPE defs ty
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [holKernelTheory.dest_var_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
QED

Theorem dest_const_thm:
   TERM defs v /\ STATE defs s ==>
    (dest_const v s = (res,s')) ==>
    (s' = s) /\ !n ty. (res = Success (n,ty)) ==> TYPE defs ty
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_const_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
QED

Theorem dest_comb_thm:
   TERM defs v /\ STATE defs s ==>
    (dest_comb v s = (res,s')) ==>
    (s' = s) /\ !x y. (res = Success (x,y)) ==> TERM defs x /\ TERM defs y
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_comb_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
QED

Theorem dest_abs_thm:
   TERM defs v /\ STATE defs s ==>
    (dest_abs v s = (res,s')) ==>
    (s' = s) /\ !x y. (res = Success (x,y)) ==> TERM defs x /\ TERM defs y
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_abs_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss []
QED

Theorem rator_thm:
   TERM defs v /\ STATE defs s ==>
    (rator v s = (res,s')) ==>
    (s' = s) /\ !x. (res = Success x) ==> TERM defs x
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [rator_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
QED

Theorem rand_thm:
   TERM defs v /\ STATE defs s ==>
    (rand v s = (res,s')) ==>
    (s' = s) /\ !x. (res = Success x) ==> TERM defs x
Proof
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [rand_def,st_ex_return_def,Once EQ_SYM_EQ,raise_Fail_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
QED

val type_subst_bool = Q.prove(
  `type_subst i Bool = Bool`,
  SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF]);

val type_subst_fun = Q.prove(
  `type_subst i (Fun ty1 ty2) = Fun (type_subst i ty1) (type_subst i ty2)`,
  SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF] \\ SRW_TAC [] []);

val TERM_Const = Q.prove(
  `STATE defs r /\ MEM (name,a) r.the_term_constants ==>
    TERM defs (Const name a)`,
  rw[STATE_def,TERM_def,term_ok_def] >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  qpat_x_assum`_ = const_list _`(ASSUME_TAC o SYM) >>
  simp[ALOOKUP_MAP] >>
  qpat_x_assum`ALL_DISTINCT X`mp_tac >>
  simp[Once MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  strip_tac >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  fs[CONTEXT_def] >>
  imp_res_tac extends_theory_ok >> fs[init_theory_ok] >>
  fs[theory_ok_def] >> first_x_assum MATCH_MP_TAC >>
  MATCH_MP_TAC ALOOKUP_IN_FRANGE >>
  simp[ALOOKUP_MAP] >> METIS_TAC[])

val TERM_Const_type_subst = Q.prove(
  `EVERY (\(x,y). TYPE defs x /\ TYPE defs y) theta /\
    TERM defs (Const name a) ==> TERM defs (Const name (type_subst theta a))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ IMP_RES_TAC type_subst
  \\ FULL_SIMP_TAC std_ss [type_subst,TERM_def,TYPE_def] >>
  fs[term_ok_def] >>
  conj_tac >- (
    match_mp_tac type_ok_TYPE_SUBST >>
    rfs[EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
    METIS_TAC[] ) >>
  simp[TYPE_SUBST_compose] >>
  METIS_TAC[])

Theorem mk_const_thm:
   !name theta s z s'.
      STATE defs s /\ EVERY (\(x,y). TYPE defs x /\ TYPE defs y) theta /\
      (mk_const (name,theta) s = (z,s')) ==> (s' = s) /\
      !i. (z = Success i) ==> TERM defs i
Proof
  SIMP_TAC std_ss [mk_const_def,try_def,st_ex_bind_def,otherwise_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `get_const_type name s`
  \\ IMP_RES_TAC get_const_type_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def]
  \\ SRW_TAC [] [st_ex_return_def]
  \\ MATCH_MP_TAC TERM_Const_type_subst \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC get_const_type_thm \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC TERM_Const
QED

val get_const_type_Equal = Q.prove(
  `STATE defs s ==>
    (get_const_type (strlit "=") s = (Success (Fun aty (Fun aty Bool)),s))`,
  SIMP_TAC std_ss [STATE_def]
  \\ Cases_on `get_const_type (strlit "=") s`
  \\ IMP_RES_TAC get_const_type_thm \\ REPEAT STRIP_TAC >>
  imp_res_tac CONTEXT_std_sig >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  qpat_x_assum`X = Y`(ASSUME_TAC o SYM) >>
  fs[is_std_sig_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >>
  reverse(Cases_on`q`)>>fs[]>-METIS_TAC[]>>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  rfs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val mk_const_eq = Q.prove(
  `STATE defs s ==>
    (mk_const ((strlit "="),[]) s =
     (Success (Const (strlit "=") (Fun aty (Fun aty Bool))),s))`,
  SIMP_TAC std_ss [mk_const_def,st_ex_bind_def,try_def,otherwise_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_const_type_Equal
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ EVAL_TAC);

val mk_eq_lemma = Q.prove(
  `inst [(term_type x,aty)] (Const (strlit "=") (Fun aty (Fun aty Bool))) s =
    ex_return
        (Const (strlit "=")
           (Fun (term_type x) (Fun (term_type x) Bool))) s`,
  NTAC 10 (SIMP_TAC (srw_ss()) [Once inst_def, Once inst_aux_def, Once LET_DEF])
  \\ NTAC 50 (SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF, Once mk_vartype_def,
       Once rev_assocd_def]) \\ SRW_TAC [] [] \\ METIS_TAC []);

Theorem mk_eq_thm:
   TERM defs x /\ TERM defs y /\ STATE defs s ==>
    (mk_eq(x,y)s = (res,s')) ==>
    (s' = s) /\
    (!t. (res = Failure t) ==> ((term_type x) <> (term_type y))) /\
    !t. (res = Success t) ==>
    (t = Comb (Comb (Const (strlit "=") (Fun (term_type x)
                               (Fun (term_type x) Bool))) x) y) /\
    TERM defs t
Proof
  STRIP_TAC \\ SIMP_TAC std_ss [mk_eq_def,try_def,st_ex_bind_def,
    otherwise_def,mk_vartype_def]
  \\ `CONTEXT defs` by fs[STATE_def]
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `x`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC mk_const_eq \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [mk_eq_lemma,st_ex_return_def]
  \\ Cases_on `mk_comb (Const (strlit "=") (Fun (term_type x)
                                  (Fun (term_type x) Bool)),x) s`
  \\ sg `TERM defs (Const (strlit "=") (Fun (term_type x)
                           (Fun (term_type x) Bool)))` THEN1
   (IMP_RES_TAC term_type >>
    IMP_RES_TAC CONTEXT_std_sig
    \\ FULL_SIMP_TAC (srw_ss()) [TERM_def] >>
    simp[term_ok_def] >> fs[is_std_sig_def,type_ok_def,TYPE_def] >>
    rfs[] >>
    qexists_tac`[(typeof x,Tyvar(strlit "A"))]` >>
    simp[REV_ASSOCD] )
  \\ Q.ABBREV_TAC `eq = (Const (strlit "=") (Fun (term_type x) (Fun (term_type x) Bool)))`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`eq`,`a`|->`x`,`res`|->`q`,`s1`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def] THEN1
   (Q.UNABBREV_TAC `eq` \\ FULL_SIMP_TAC std_ss [mk_comb_def,st_ex_bind_def]
    \\ IMP_RES_TAC (Q.SPEC `y` type_of_thm)
    \\ Q.PAT_X_ASSUM `type_of x s = (Success (term_type x),s)` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``term_type (Const (strlit "=") ty)``,st_ex_return_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `mk_comb (Comb eq x,y) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`Comb eq x`,`a`|->`y`,
      `res`|->`q`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.UNABBREV_TAC `eq` \\ FULL_SIMP_TAC std_ss [mk_comb_def,st_ex_bind_def]
  \\ IMP_RES_TAC (Q.SPEC `y` type_of_thm)
  \\ Q.PAT_X_ASSUM `type_of x s = (Success (term_type x),s)` ASSUME_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``term_type (Const (strlit "=") ty)``,st_ex_return_def,
         ``term_type (Comb x y)`` |> SIMP_CONV (srw_ss()) [Once term_type_def],
         ``type_of (Comb x y)`` |> SIMP_CONV (srw_ss()) [Once type_of_def],
         ``type_of (Const x y)`` |> SIMP_CONV (srw_ss()) [Once type_of_def],
         st_ex_bind_def,dest_type_def]
QED

val TERM_Eq_x = Q.prove(
  `STATE defs s /\ TERM defs (Comb (Const (strlit "=") ty) x) ==>
    (Fun (typeof x) (Fun (typeof x) Bool) = ty)`,
  rw[TERM_def,STATE_def] >>
  fs[term_ok_def] >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def] >> rw[] >>
  fs[TYPE_SUBST_def])

val TERM_Comb = Q.prove(
  `CONTEXT defs ⇒
    (TERM defs (Comb f a) <=>
     TERM defs f /\ TERM defs a /\
     ?ty. term_type f = Fun (term_type a) ty)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC term_type
  \\ FULL_SIMP_TAC std_ss [TERM_def,WELLTYPED_CLAUSES,term_ok_def]
  \\ METIS_TAC[term_ok_welltyped])

val MAP_EQ_2_SYM = Q.prove(
  `([x;y] = MAP f l) ⇔ (MAP f l = [x;y])`,METIS_TAC[])

val Equal_type = Q.prove(
  `STATE defs s ∧ TERM defs (Const (strlit "=") ty) ==> ?a. ty = Fun a (Fun a Bool)`,
  rw[STATE_def,TERM_def] >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def,term_ok_def])

val Equal_type_IMP = Q.prove(
  `STATE defs s ∧ TERM defs (Comb (Const (strlit "=") (Fun a' (Fun a' Bool))) ll) ==>
    (typeof ll = a')`,
  simp[TERM_Comb] >> strip_tac >>
  imp_res_tac TERM_Eq_x >>
  fs[Once term_type_def] >>
  rw[] >> imp_res_tac term_type >> simp[])

Theorem dest_eq_thm:
   TERM defs tm /\ STATE defs s /\ (dest_eq tm s = (res, s')) ==>
    (s' = s) /\ !t1 t2. (res = Success (t1,t2)) ==> TERM defs t1 /\ TERM defs t2 /\
    (tm = Comb (Comb (Equal (typeof t1)) t1) t2)
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [dest_eq_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM_Eq_x
QED

val VFREE_IN_IMP = Q.prove(
  `!y. TERM defs y /\ TYPE defs ty /\ STATE defs s /\
        VFREE_IN (Var name ty) y ==>
        vfree_in (Var name ty) y`,
  METIS_TAC [vfree_in_thm]);

val SELECT_LEMMA = Q.prove(
  `(@f. !s s'. f (s',s) <=> s <> t) = (\(z,y). y <> t)`,
  Q.ABBREV_TAC `p = (@f. !s s'. f (s',s) <=> s <> t)`
  \\ sg `?f. !s s'. f (s',s) <=> s <> t`
  THEN1 (Q.EXISTS_TAC `(\(z,y). y <> t)` \\ FULL_SIMP_TAC std_ss [])
  \\ `!s s'. p (s',s) <=> s <> t` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]);

val SELECT_LEMMA2 = Q.prove(
  `(@f.
       !s s''.
         f (s'',s) <=>
         VFREE_IN (Var s' ty) s'' /\ VFREE_IN s tm') =
    (\(x,y). VFREE_IN (Var s' ty) x /\ VFREE_IN y tm')`,
  Q.ABBREV_TAC `p = (@f. !s s''. f (s'',s) <=>
         VFREE_IN (Var s' ty) s'' /\ VFREE_IN s tm')`
  \\ sg `?f. !s s''. f (s'',s) <=>
         VFREE_IN (Var s' ty) s'' /\ VFREE_IN s tm'`
  THEN1 (Q.EXISTS_TAC `(\(s'',s). VFREE_IN (Var s' ty) s'' /\
                VFREE_IN s tm')` \\ FULL_SIMP_TAC std_ss [])
  \\ `!s s''. p (s'',s) <=> VFREE_IN (Var s' ty) s'' /\
                            VFREE_IN s tm'` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]);

val is_var_thm = Q.prove(
  `!x. is_var x = ?v ty. x = Var v ty`,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]);

val VSUBST_EMPTY = Q.prove(
  `(!tm. holSyntax$VSUBST [] tm = tm)`,
  Induct
  \\ FULL_SIMP_TAC (srw_ss()) [VSUBST_def,REV_ASSOCD,EVERY_DEF,FILTER,LET_THM]);

val VFREE_IN_TYPE = Q.prove(
  `!x. VFREE_IN (Var name oty) x /\ TERM defs x ==>
        ?ty. (oty = ty) /\ TYPE defs ty`,
  Induct
  THEN1 (SIMP_TAC std_ss [VFREE_IN_def,term_11] \\ METIS_TAC [TERM])
  THEN1 (SRW_TAC [] [VFREE_IN_def,term_11,term_distinct])
  THEN1 (SIMP_TAC std_ss [VFREE_IN_def,term_11]
         \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [VFREE_IN_def,term_11] \\ STRIP_TAC
  \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [VFREE_IN_def] \\ METIS_TAC []);

val VFREE_IN_IMP_MEM = Q.prove(
  `VFREE_IN (Var name oty) h0 /\ TERM defs h0 /\ STATE defs s ==>
    ?ty1. MEM (Var name ty1) (frees h0) /\ (oty = ty1) /\ TYPE defs ty1`,
  Induct_on `h0` THEN1 (Q.SPEC_TAC (`oty`,`oty`)
    \\ FULL_SIMP_TAC (srw_ss()) [VFREE_IN_def,term_11,Once frees_def]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [])
  THEN1 (SRW_TAC [] [VFREE_IN_def,term_11,Once frees_def,term_distinct])
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union,VFREE_IN_def]
         \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC) \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [VFREE_IN_def]
  \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union,VFREE_IN_def]
  \\ SIMP_TAC (srw_ss()) [subtract_def,MEM_FILTER]
  \\ IMP_RES_TAC VFREE_IN_TYPE \\ FULL_SIMP_TAC std_ss []
  \\ fs[])

val term_type_Var = Q.prove(
  `term_type (Var v ty) = ty`,
  SIMP_TAC (srw_ss()) [Once term_type_def]);

val vsubst_aux_thm = Q.prove(
  `!t tm theta. EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2 /\
                     (term_type t1 = term_type t2) /\ is_var t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (vsubst_aux theta tm = t) ==>
    TERM defs t /\
    (t = VSUBST theta tm)`,
  SIMP_TAC std_ss [] \\ Induct THEN1
   (NTAC 4 STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def]
    \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def,VSUBST_def]
    \\ Induct_on `theta` \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [rev_assocd_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVERY_DEF,REV_ASSOCD]
    \\ Cases \\ FULL_SIMP_TAC (srw_ss()) [REV_ASSOCD_def]
    \\ Cases_on `r = Var s' h` \\ FULL_SIMP_TAC std_ss []
    \\ rw[] \\ fs[] \\ METIS_TAC[])
  THEN1
   (NTAC 4 STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def]
    \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def,VSUBST_def]
    \\ SRW_TAC [] [VSUBST_def])
  THEN1
   (STRIP_TAC \\ REPEAT (Q.PAT_X_ASSUM `!theta. bbb` (ASSUME_TAC o SPEC_ALL))
    \\ ONCE_REWRITE_TAC [vsubst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [VSUBST_def,term_11]
    \\ reverse (REPEAT STRIP_TAC)
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [TERM_def,term_ok_def]
    \\ SIMP_TAC std_ss [GSYM VSUBST_def]
    \\ MATCH_MP_TAC VSUBST_WELLTYPED
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,FORALL_PROD,EVERY_MEM]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [is_var_thm]
    \\ FULL_SIMP_TAC (srw_ss()) [term_11]
    \\ FULL_SIMP_TAC std_ss [EVAL ``term_type (Var v ty)``]
    \\ rw[]
    \\ fs[STATE_def]
    \\ IMP_RES_TAC (REWRITE_RULE [TERM_def] term_type)
    \\ METIS_TAC[WELLTYPED,term_ok_welltyped])
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [vsubst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]
  \\ Cases_on `FILTER (\(t,x). x <> Var s' ty) theta = []`
  \\ FULL_SIMP_TAC std_ss [] THEN1
   (SIMP_TAC std_ss [REWRITE_RULE[SELECT_LEMMA]VSUBST_def,LET_THM]
    \\ sg `(FILTER (\(z,y). y <> Var s' ty) theta) = []` THEN1
     (POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `theta` \\ FULL_SIMP_TAC std_ss [MAP,FILTER]
      \\ Cases \\ FULL_SIMP_TAC std_ss [MAP,FILTER]
      \\ Cases_on `r = Var s' ty` \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC (srw_ss()) [VSUBST_EMPTY])
  \\ reverse (Cases_on `EXISTS (\(t,x). vfree_in (Var s' ty) t /\ vfree_in x tm')
       (FILTER (\(t,x). x <> Var s' ty) theta)`) THEN1
   (IMP_RES_TAC TERM \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [] >>
    simp[TERM_Abs] >>
    simp[VSUBST_def] >>
    BasicProvers.CASE_TAC >- (
      fs[EXISTS_MEM,EVERY_MEM,MEM_FILTER,FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`VFREE_IN (Var x ty) pm` >>
      qmatch_assum_rename_tac`VFREE_IN qm pm2` >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >>
      impl_tac >- (
        simp[] >> spose_not_then STRIP_ASSUME_TAC >> fs[] ) >>
      strip_tac >- METIS_TAC[vfree_in_thm] >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >>
      Cases_on`qm`>>simp[]>>strip_tac>>fs[term_type_Var] >>
      METIS_TAC[vfree_in_thm,TERM] ) >>
    Q.PAT_ABBREV_TAC`thet = FILTER P theta` >>
    first_x_assum(qspec_then`thet`mp_tac)>>
    impl_tac >- (
      fs[EVERY_MEM,Abbr`thet`,MEM_FILTER,FORALL_PROD]>>
      rw[]>>METIS_TAC[])>>
    rw[Abbr`thet`] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[rich_listTheory.FILTER_MAP] >>
    AP_TERM_TAC >>
    simp[rich_listTheory.FILTER_EQ,FORALL_PROD] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    strip_tac >> Cases >> strip_tac >> res_tac >> fs[] >>
    METIS_TAC[] ) >>
  simp[] >>
  `TERM defs (vsubst_aux (FILTER (\(t,x). x <> Var s' ty) theta) tm') /\
      TYPE defs ty` by
   (IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `FILTER (\(t,x). x <> Var s' ty) theta`)
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_FILTER])
  \\ FULL_SIMP_TAC std_ss [variant_vsubst_thm]
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `(vsubst_aux (FILTER (\ (t,x). x <> Var s' ty) theta) tm') =
      (VSUBST
       (FILTER ( \ (z,y). y <> Var s' ty) theta) tm')` by
   (Q.PAT_X_ASSUM `!theta.bbb` (MP_TAC o
        Q.SPEC `FILTER (\(t,x). x <> Var s' ty) theta`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_FILTER,PULL_EXISTS])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ Q.PAT_X_ASSUM `EVERY PP xx` MP_TAC
    \\ Q.SPEC_TAC (`theta`,`xs`) \\ Induct
    \\ SIMP_TAC std_ss [MEM,FILTER,MAP] \\ Cases
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF] \\ STRIP_TAC
    \\ SRW_TAC [] []
    \\ METIS_TAC [TERM_def])
  \\ FULL_SIMP_TAC std_ss [TERM_Abs]
  \\ Q.PAT_ABBREV_TAC `theta1 = (FOO::FILTER (\(t,x). x <> Var s' ty) theta)`
  \\ Q.PAT_X_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `theta1`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `theta1` \\ IMP_RES_TAC TERM_Var_SIMP
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,MEM_FILTER,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [term_type_def] \\ SIMP_TAC (srw_ss()) [])
  \\ SIMP_TAC std_ss [VSUBST_def,LET_THM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SELECT_LEMMA2]
  \\ reverse BasicProvers.CASE_TAC >- (
      fs[EXISTS_MEM,EVERY_MEM,MEM_FILTER,FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`vfree_in (Var x ty) pm` >>
      qmatch_assum_rename_tac`vfree_in qm pm2` >>
      last_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >> simp[] >>
      strip_tac >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >>
      impl_tac >- (
        conj_tac >- (
          spose_not_then STRIP_ASSUME_TAC >>
          Cases_on`qm`>>fs[] >>
          METIS_TAC[] ) >>
        METIS_TAC[] ) >>
      Cases_on`qm`>>fs[] >>
      METIS_TAC[vfree_in_thm,TERM] ) >>
  qunabbrev_tac`theta1` >>
  Q.PAT_ABBREV_TAC`vv = holSyntax$VARIANT A B Z` >>
  simp[])

val forall_thm = Q.prove(
  `!f s (xs:(term # term) list). (forall f xs s = (res,s')) ==>
    (!x. ?r. f x s = (r,s)) ==>
    (s' = s) /\ ((res = Success T) ==> EVERY (\x. FST (f x s) = Success T) xs)`,
  STRIP_TAC \\ STRIP_TAC
  \\ Induct \\ ASM_SIMP_TAC (srw_ss()) [Once forall_def,st_ex_return_def,st_ex_bind_def]
  \\ STRIP_TAC \\ Cases_on `f h s` \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC \\ STRIP_TAC
  \\ `r = s` by METIS_TAC [PAIR,PAIR_EQ] \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `a` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [FST,PAIR]);

val assoc_state = Q.prove(
  `!xs x. ?r. assoc x xs s = (r,s)`,
  Induct \\ ONCE_REWRITE_TAC [assoc_def] \\ TRY Cases
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def] \\ SRW_TAC [] []);

val type_of_state = Q.prove(
  `!tm. ?r. type_of tm s = (r,s)`,
  HO_MATCH_MP_TAC type_of_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once type_of_def] \\ Cases_on `tm`
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def,raise_Fail_def,st_ex_bind_def]
  THEN1
   (TRY (Cases_on `r`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
    \\ TRY (Cases_on `a`)
    \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def,raise_Fail_def,st_ex_return_def]
    \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `t`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
  \\ TRY (Cases_on `r`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
  \\ FULL_SIMP_TAC (srw_ss()) [mk_fun_ty_def,mk_type_def,st_ex_bind_def,
        try_def,otherwise_def,get_type_arity_def,
        get_the_type_constants_def,raise_Fail_def,st_ex_return_def]
  \\ STRIP_ASSUME_TAC (assoc_state |> ISPEC ``s.the_type_constants``
        |> ISPEC ``strlit"fun"``) \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] []);

Theorem vsubst_thm:
   EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (vsubst theta tm s = (res, s')) ==>
    (s' = s) /\ !t. (res = Success t) ==> TERM defs t /\
    (t = VSUBST  theta tm) /\
    (EVERY (\(p_1,p_2). ?x ty. (p_2 = Var x ty) /\
                               (p_1) has_type ty) theta)
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [vsubst_def]
  \\ Cases_on `theta = []`
  \\ FULL_SIMP_TAC (srw_ss()) [MAP,VSUBST_EMPTY,st_ex_return_def,st_ex_bind_def]
  \\ Q.PAT_ABBREV_TAC `test = (\(t,x) state.
        case type_of t state of
          (Success ty,state) =>
            (case dest_var x state of
               (Success vty,state) => (Success (ty = SND vty),state)
             | (Failure e,state) => (Failure e,state))
        | (Failure e,state) => (Failure e,state))`
  \\ Cases_on `forall test theta s`
  \\ MP_TAC (forall_thm |> ISPECL [``test : term # term -> bool M``,``s : hol_refs``,``theta : (term, term) alist``] |> Q.GENL [`s'`,`res`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `TERM defs tm /\ STATE defs s` \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `test` \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
    \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `p_1` type_of_state)
    \\ Cases_on `r'` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `p_2`
    \\ FULL_SIMP_TAC (srw_ss()) [holKernelTheory.dest_var_def,st_ex_return_def,raise_Fail_def])
  \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `a` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ sg `EVERY
       (\(t1,t2).
          TERM defs t1 /\ TERM defs t2 /\
          (term_type t1 = term_type t2) /\ is_var t2) theta` THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD] \\ NTAC 3 STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `test`
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC type_of_thm
    \\ FULL_SIMP_TAC (srw_ss()) [holKernelTheory.dest_var_def]
    \\ Cases_on `p_2`
    \\ FULL_SIMP_TAC (srw_ss()) [holKernelTheory.dest_var_def,st_ex_return_def,raise_Fail_def,is_var_def]
    \\ SIMP_TAC (srw_ss()) [Once term_type_def])
  \\ IMP_RES_TAC (vsubst_aux_thm |> SIMP_RULE std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `p_2` \\ FULL_SIMP_TAC (srw_ss()) [is_var_def,term_11]
  \\ IMP_RES_TAC term_type
  \\ FULL_SIMP_TAC std_ss [TERM_def,typeof_def]
  \\ FULL_SIMP_TAC std_ss [WELLTYPED,term_type_Var] >>
  rfs[STATE_def] >>
  rw[] >> METIS_TAC [WELLTYPED,term_ok_welltyped]
QED

Theorem inst_aux_Var:
   inst_aux [] theta (Var v ty) state =
      (Success (Var v (type_subst theta ty)),state)
Proof
  SIMP_TAC (srw_ss()) [Once inst_aux_def,rev_assocd_thm,REV_ASSOCD,
       LET_DEF,st_ex_return_def] \\ METIS_TAC []
QED

val MEM_subtract = Q.prove(
  `!xs ys x. MEM x (subtract xs ys) <=> MEM x xs /\ ~MEM x ys`,
  FULL_SIMP_TAC std_ss [subtract_def,MEM_FILTER,MEM] \\ METIS_TAC []);

val MEM_frees = Q.prove(
  `!tm y. TERM defs tm /\ MEM y (frees tm) ==>
           ?v ty. (y = Var v ty) /\ TYPE defs ty`,
  Induct \\ SIMP_TAC (srw_ss()) [Once frees_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [MEM_union,MEM_subtract]);

Theorem inst_aux_thm:
   !env theta tm s s' res.
      EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
      EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) env /\
      TERM defs tm /\ STATE defs s /\
      (inst_aux env theta tm s = (res, s')) ==>
      STATE defs s' /\
      case res of
      | Success t => (INST_CORE env theta tm = Result t)
      | Failure (Clash v) => (INST_CORE env theta tm = Clash v)
      | _ => F
Proof
  HO_MATCH_MP_TAC inst_aux_ind \\ NTAC 4 STRIP_TAC \\ Cases_on `tm`
  \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (simp[inst_aux_def,INST_CORE_def,rev_assocd_thm] >>
    `(if type_subst theta t = t then Var m t
      else Var m (type_subst theta t)) = Var m (type_subst theta t)` by METIS_TAC [] >>
    simp[] >> POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM type_subst,st_ex_return_def] >>
    rw[] >> rw[] >> fs[st_ex_bind_def,raise_Fail_def,raise_Clash_def] >> rw[] >>
    fs[STATE_def]
    \\ MATCH_MP_TAC (TERM_Var |> GEN_ALL)
    \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst]
    \\ MATCH_MP_TAC type_ok_TYPE_SUBST \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [TYPE_def]
    \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
  THEN1
   (ONCE_REWRITE_TAC [inst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF,st_ex_return_def]
    \\ NTAC 4 STRIP_TAC
    \\ sg `(res = Success (Const m (type_subst theta t))) /\ (s = s')`
    THEN1 (Cases_on `type_subst theta t = t` \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [INST_CORE_def,type_subst])
  THEN1
   (ONCE_REWRITE_TAC [inst_aux_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,st_ex_return_def,st_ex_bind_def]
    \\ NTAC 4 STRIP_TAC \\ Cases_on `inst_aux env theta t s`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Q.PAT_X_ASSUM `Failure xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,LET_THM]
      \\ BasicProvers.CASE_TAC \\ simp[])
    \\ Cases_on `inst_aux env theta t0 r`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Q.PAT_X_ASSUM `Failure xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,LET_THM]
      \\ BasicProvers.CASE_TAC >> simp[])
    THEN1
     (Q.PAT_X_ASSUM `Success xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,RESULT_def,LET_THM]))
  \\ SIMP_TAC (srw_ss()) [Once inst_aux_def]
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ NTAC 7 STRIP_TAC
  \\ IMP_RES_TAC Abs_Var
  \\ Q.MATCH_ASSUM_RENAME_TAC `h = Var v ty`
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [Once inst_aux_def]
  \\ `!ty'. (if ty' = ty then Var v ty else Var v ty') = Var v ty'` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [rev_assocd_thm,REV_ASSOCD,LET_DEF,st_ex_return_def]
  \\ SIMP_TAC (srw_ss()) [st_ex_bind_def,otherwise_def,handle_Clash_def,raise_Clash_def]
  \\ Cases_on `inst_aux ((Var v ty,Var v (type_subst theta ty))::env) theta t0 s`
  \\ Q.PAT_X_ASSUM `!x yy.bbb` (K ALL_TAC)
  \\ first_x_assum(MP_TAC o Q.SPECL
       [`((Var v ty,Var v (type_subst theta ty))::env)`,`s`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (IMP_RES_TAC TERM \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst]
    \\ MATCH_MP_TAC type_ok_TYPE_SUBST
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD,
         EVERY_MEM] \\ METIS_TAC [])
  \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [INST_CORE_def,LET_THM]
    \\ FULL_SIMP_TAC std_ss [type_subst,IS_RESULT_def,RESULT_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] >> simp[])
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ sg `(Var v (type_subst theta ty)) =
      (Var v (TYPE_SUBST theta ty))` THEN1
   (SIMP_TAC std_ss [GSYM type_subst])
  \\ FULL_SIMP_TAC (srw_ss()) [] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >- (
    rw[] >> rw[]
    \\ rw[Once INST_CORE_def] )
  \\ SIMP_TAC (srw_ss()) [inst_aux_Var,``dest_var (Var v ty) state``
        |> SIMP_CONV (srw_ss()) [holKernelTheory.dest_var_def,st_ex_return_def]]
  \\ Q.ABBREV_TAC `fresh_name = (VARIANT
                (RESULT (INST_CORE [] theta (t0))) (explode v)
                (TYPE_SUBST theta ty))`
  \\ Q.PAT_X_ASSUM `!x y. bbb` (MP_TAC o Q.SPEC `r`)
  \\ IMP_RES_TAC TERM
  \\ Cases_on `inst_aux [] theta t0 r` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ reverse (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ MP_TAC (INST_CORE_LEMMA |> Q.SPECL [`theta`,`t0`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [TERM_def] >> METIS_TAC[term_ok_welltyped])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [result_distinct]
    \\ rw[] >> rw[] >> BasicProvers.CASE_TAC >> fs[])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.MATCH_ASSUM_RENAME_TAC `inst_aux [] theta h0 r = (Success a,r1)`
  \\ sg `(variant (frees a) (Var v (type_subst theta ty))) =
      Var fresh_name (type_subst theta ty)` THEN1
   (FULL_SIMP_TAC std_ss [GSYM type_subst,RESULT_def]
    \\ Q.UNABBREV_TAC `fresh_name`
    \\ MATCH_MP_TAC variant_inst_thm \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC[INST_def,RESULT_def,INST_WELLTYPED,TERM_def,term_ok_welltyped])
  \\ FULL_SIMP_TAC std_ss []
  \\ REV_FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [inst_aux_Var,``dest_var (Var v ty) state``
        |> SIMP_CONV (srw_ss()) [holKernelTheory.dest_var_def,st_ex_return_def]]
  \\ Q.PAT_X_ASSUM `!x y z.bbb` (MP_TAC o Q.SPECL
       [`fresh_name`,`ty`,`(type_subst theta ty)`,`r1`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `inst_aux ((Var fresh_name ty,
                  Var fresh_name (TYPE_SUBST theta ty))::env) theta
       (vsubst_aux [(Var fresh_name ty,Var v ty)] h0) r1`
  \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_DEF] \\ REPEAT STRIP_TAC
    \\ TRY (MATCH_MP_TAC TERM_Var) \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [TYPE_def,type_subst]
      \\ MATCH_MP_TAC type_ok_TYPE_SUBST
      \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
    \\ (vsubst_aux_thm |> SIMP_RULE std_ss []
     |> Q.SPECL [`tm`,`[Var v ty,Var y ty]`]
     |> SIMP_RULE std_ss [EVERY_DEF,MAP]
     |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> MP_CANON |> MATCH_MP_TAC)
    \\ ONCE_REWRITE_TAC [term_type_def]
    \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]
    \\ REPEAT STRIP_TAC
    \\ TRY (MATCH_MP_TAC TERM_Var) \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [type_subst]
  \\ SIMP_TAC std_ss [INST_CORE_def,LET_THM]
  \\ FULL_SIMP_TAC std_ss [type_subst,IS_RESULT_def,CLASH_def]
  \\ FULL_SIMP_TAC std_ss [GSYM type_subst]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `((vsubst_aux [(Var fresh_name ty,Var v ty)] h0)) =
      (VSUBST [(Var fresh_name (ty),Var v (ty))] (h0))` by
   ((vsubst_aux_thm |> SIMP_RULE std_ss []
     |> Q.SPECL [`tm`,`[Var v ty,Var y ty]`]
     |> SIMP_RULE std_ss [EVERY_DEF,MAP]
     |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> MP_CANON |> MATCH_MP_TAC)
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]
    \\ ONCE_REWRITE_TAC [term_type_def] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [IS_RESULT_def,RESULT_def] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[]
QED

val inst_lemma = Q.prove(
  `EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (inst theta tm s = (res, s')) ==>
    STATE defs s' /\ !t. (res = Success t) ==>
    (t = INST theta (tm))`,
  SIMP_TAC std_ss [INST_def,inst_def] \\ Cases_on `theta = []`
  \\ ASM_SIMP_TAC std_ss [MAP,EVERY_DEF,st_ex_return_def] THEN1
   (Q.SPEC_TAC (`res`,`res`) \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [TERM_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ imp_res_tac term_ok_welltyped
    \\ IMP_RES_TAC INST_CORE_HAS_TYPE
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`[]`,`[]`])
    \\ FULL_SIMP_TAC std_ss [MEM,REV_ASSOCD]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [RESULT_def]
    \\ FULL_SIMP_TAC std_ss [INST_CORE_EMPTY,result_11,RESULT_def])
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (inst_aux_thm |> Q.SPECL [`[]`,`theta`]
                  |> SIMP_RULE std_ss [EVERY_DEF,MAP])
  \\ REPEAT (Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [TERM_def] >> imp_res_tac term_ok_welltyped
  \\ IMP_RES_TAC INST_CORE_HAS_TYPE
  \\ POP_ASSUM (MP_TAC o Q.SPECL
       [`(MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta)`,`[]`])
  \\ FULL_SIMP_TAC std_ss [MEM,REV_ASSOCD] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,RESULT_def,result_distinct,result_11]
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [])

Theorem inst_thm:
   EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (inst theta tm s = (res, s')) ==>
    STATE defs s' /\ (res = Success (INST theta tm)) /\ TERM defs (INST theta tm)
Proof
  ntac 2 STRIP_TAC \\ IMP_RES_TAC inst_lemma
  \\ FULL_SIMP_TAC std_ss [TERM_def] >> imp_res_tac term_ok_welltyped
  \\ IMP_RES_TAC INST_CORE_LEMMA
  \\ fs[INST_def]
  \\ POP_ASSUM (MP_TAC o Q.SPEC `theta`)
  \\ STRIP_TAC \\ fs[]
  \\ conj_tac >- (
    fs[inst_def,st_ex_return_def]
    \\ Cases_on`theta=[]`\\fs[]
    \\ drule inst_aux_thm
    \\ disch_then(qspec_then`[]`mp_tac)
    \\ simp[TERM_def]
    \\ disch_then drule
    \\ simp[]
    \\ disch_then(qspec_then`s`mp_tac)
    \\ simp[]
    \\ CASE_TAC
    \\ CASE_TAC)
  \\ drule term_ok_INST_CORE
  \\ disch_then(qspecl_then[`[]`,`theta`]mp_tac) \\ simp[]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,FORALL_PROD,EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,TYPE_def,FORALL_PROD,MEM,IS_RESULT_def]
  \\ METIS_TAC []
QED

val freesin_IMP = Q.prove(
  `!rhs vars.
       freesin vars rhs /\ TERM defs rhs /\ VFREE_IN (Var x ty) (rhs) ==>
       MEM (Var x ty) vars`,
  Induct \\ SIMP_TAC (srw_ss()) [Once freesin_def]
  THEN1 (REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
         \\ FULL_SIMP_TAC std_ss [CLOSED_def,VFREE_IN_def])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [CLOSED_def,VFREE_IN_def]
  \\ IMP_RES_TAC TERM
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(Var s ty'::vars)`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ FULL_SIMP_TAC (srw_ss()) [term_11]);

val ALL_DISTINCT_union = Q.prove(
  `!xs. ALL_DISTINCT (holSyntaxExtra$union xs ys) = ALL_DISTINCT ys`,
  Induct \\ SIMP_TAC (srw_ss()) [union_def,Once itlist_def,insert_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [union_def]);

val ALL_DISTINCT_tyvars_ALT = Q.prove(
  `!h. ALL_DISTINCT (tyvars (h:type))`,
  HO_MATCH_MP_TAC type_IND \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once holKernelTheory.tyvars_def]
  \\ Induct_on `l` \\ SIMP_TAC (srw_ss()) [Once itlist_def,MAP]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_union]);

val ALL_DISTINCT_type_vars_in_term = Q.prove(
  `!P. ALL_DISTINCT (type_vars_in_term P)`,
  Induct \\ SIMP_TAC (srw_ss()) [Once type_vars_in_term_def]
  \\ FULL_SIMP_TAC std_ss [tyvars_ALL_DISTINCT,ALL_DISTINCT_union]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_tyvars_ALT]);

val MEM_type_vars_in_term = Q.prove(
  `!rhs v. TERM defs rhs ==>
            (MEM v (type_vars_in_term rhs) = MEM v (tvars rhs))`,
  Induct
  \\ SIMP_TAC (srw_ss()) [Once type_vars_in_term_def,tvars_def,tyvars_thm]
  THEN1 (FULL_SIMP_TAC std_ss [MEM_union,MEM_LIST_UNION] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [MEM_union,
       tvars_def,MEM_LIST_UNION]
  \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]);

val QSORT_type_vars_in_term = Q.prove(
  `TERM defs P ==>
    (QSORT $<= (MAP explode (type_vars_in_term P)) = STRING_SORT (MAP explode (tvars P)))`,
  REPEAT STRIP_TAC \\
  MATCH_MP_TAC (MP_CANON sortingTheory.SORTED_PERM_EQ) \\
  qexists_tac`$<=` >>
  conj_asm1_tac >- (
    simp[relationTheory.transitive_def,relationTheory.antisymmetric_def,stringTheory.string_le_def] >>
    METIS_TAC[stringTheory.string_lt_antisym,stringTheory.string_lt_trans] ) >>
  conj_tac >- (
    MATCH_MP_TAC sortingTheory.QSORT_SORTED >>
    simp[relationTheory.total_def,stringTheory.string_le_def] >>
    METIS_TAC[stringTheory.string_lt_cases] ) >>
  conj_tac >- (
    MATCH_MP_TAC sortingTheory.SORTED_weaken >>
    qexists_tac`$<` >>
    simp[STRING_SORT_SORTED,stringTheory.string_le_def] ) >>
  MATCH_MP_TAC (MP_CANON sortingTheory.PERM_ALL_DISTINCT) >>
  conj_tac >- (
    METIS_TAC[sortingTheory.ALL_DISTINCT_PERM
             ,sortingTheory.QSORT_PERM
             ,ALL_DISTINCT_type_vars_in_term
             ,ALL_DISTINCT_MAP_explode] ) >>
  simp[ALL_DISTINCT_STRING_SORT] >>
  METIS_TAC[sortingTheory.QSORT_MEM,MEM_type_vars_in_term,MEM_MAP])

(* ------------------------------------------------------------------------- *)
(* Verification of thm functions                                             *)
(* ------------------------------------------------------------------------- *)

Theorem dest_thm_thm:
   THM defs th /\ STATE defs s /\ (dest_thm th = (asl, c)) ==>
    EVERY (TERM defs) asl /\ TERM defs c
Proof
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [dest_thm_def] \\ METIS_TAC []
QED

Theorem hyp_thm:
   THM defs th /\ STATE defs s /\ (hyp th = asl) ==>
    EVERY (TERM defs) asl
Proof
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [hyp_def] \\ METIS_TAC []
QED

Theorem concl_thm:
   THM defs th /\ STATE defs s /\ (concl th = c) ==>
    TERM defs c
Proof
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [concl_def] \\ METIS_TAC []
QED

Theorem REFL_thm:
   TERM defs tm /\ STATE defs s /\ (REFL tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  SIMP_TAC std_ss [REFL_def,st_ex_bind_def] \\ Cases_on `mk_eq(tm,tm) s`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC mk_eq_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ Q.PAT_X_ASSUM `xxx = th` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [THM_def,domain_def] >>
  rw[] >>
  fs[STATE_def] >> rw[] >> imp_res_tac term_type
  \\ simp[GSYM equation_def]
  \\ MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,8)) >>
  fs[CONTEXT_def,TERM_def] >>
  METIS_TAC[extends_theory_ok,init_theory_ok]
QED

Theorem TRANS_thm:
   THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (TRANS th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [TRANS_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ SRW_TAC [] [st_ex_bind_def] \\ IMP_RES_TAC THM
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const (strlit "=") h1) ll) m1)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const (strlit "=") h2) m2) rr)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ Cases_on `mk_eq (ll,rr) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`ll`,`y`|->`rr`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  \\ MP_TAC (aconv_thm |> Q.SPECL [`m1`,`m2`] |> SIMP_RULE std_ss [])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC >>
  rpt(qpat_x_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[] >>
  imp_res_tac Equal_type >> fs[] >>
  imp_res_tac Equal_type_IMP >>
  ntac 2 (pop_assum(mp_tac o SYM)) >>
  simp[GSYM equation_def] >> rw[] >>
  match_mp_tac (MP_CANON trans_equation) >>
  METIS_TAC[]
QED

Theorem SYM_thm:
   THM defs th /\ STATE defs s /\
    (SYM th s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on`th`>>rw[EQ_SYM_EQ]>>fs[SYM_def]>>
  every_case_tac >> fs[raise_Fail_def,st_ex_return_def] >>
  fs[THM_def] >> rw[] >>
  qmatch_assum_rename_tac`_ |- Comb (Comb (Const _ ty) _) _` >>
  `∃a. ty = Fun a (Fun a Bool)` by (
    fs[STATE_def] >> imp_res_tac CONTEXT_std_sig >>
    imp_res_tac proves_term_ok >> rfs[term_ok_clauses] >> rw[] >>
    fs[codomain_def] >> rw[] >>
    rfs[term_ok_def,is_std_sig_def] ) >>
  rw[] >> match_mp_tac sym >> rw[]
QED

Theorem PROVE_HYP_thm:
   THM defs th1 ∧ THM defs th2 ∧ STATE defs s ∧
   (PROVE_HYP th1 th2 s = (res, s')) ⇒
   (s' = s) ∧ ∀th. (res = Success th) ⇒ THM defs th
Proof
  Cases_on`th1`>>Cases_on`th2`>>rw[EQ_SYM_EQ]>>
  fs[PROVE_HYP_def,st_ex_return_def,THM_def]>>
  match_mp_tac proveHyp >> rw[]
QED

val map_type_of = Q.prove(
  `∀ls s r s'.
      EVERY (TERM defs) ls ∧ STATE defs s ∧
      (map type_of ls s = (Success r,s')) ⇒
      (s' = s) ∧
      (r = MAP term_type ls)`,
  Induct >> simp[Once map_def] >- (
    simp[st_ex_return_def] ) >>
  rw[st_ex_bind_def] >>
  every_case_tac >> fs[st_ex_return_def] >> rw[] >>
  imp_res_tac type_of_thm >> fs[] >> rw[] >>
  METIS_TAC[])

val map_type_of_state = Q.prove(
  `∀ls s r s'.
      (map type_of ls s = (r,s')) ⇒
      (s' = s)`,
  Induct >> simp[Once map_def] >- (
    simp[st_ex_return_def] ) >>
  rw[st_ex_bind_def] >>
  every_case_tac >> fs[st_ex_return_def] >> rw[] >>
  METIS_TAC[type_of_state,PAIR,FST,SND])

Theorem hypset_ok_list_to_hypset[simp]:
   ∀ls a. hypset_ok a ⇒ hypset_ok (list_to_hypset ls a)
Proof
  Induct >> simp[list_to_hypset_def]
QED

Theorem MEM_list_to_hypset_imp:
   ∀ls a. MEM x (list_to_hypset ls a) ⇒ MEM x ls ∨ MEM x a
Proof
  Induct >> rw[list_to_hypset_def] >>
  res_tac >> simp[] >>
  imp_res_tac MEM_term_union_imp >> fs[]
QED

Theorem ALPHA_THM_thm:
   THM defs th ∧ EVERY (TERM defs) h ∧ TERM defs c ∧ STATE defs s ∧
   (ALPHA_THM th (h,c) s = (res,s')) ⇒
   (s' = s) ∧ ∀th. (res = Success th) ⇒ THM defs th
Proof
  Cases_on`th`>>simp[ALPHA_THM_def]>>
  IF_CASES_TAC>>strip_tac>>fs[raise_Fail_def]>>
  rpt var_eq_tac >> simp[] >>
  pop_assum mp_tac >>
  IF_CASES_TAC>>strip_tac>>fs[raise_Fail_def]>>
  rpt var_eq_tac >> simp[] >>
  fs[st_ex_bind_def,st_ex_return_def] >>
  BasicProvers.FULL_CASE_TAC >> fs[]>>
  BasicProvers.FULL_CASE_TAC >> fs[]>>
  IMP_RES_TAC map_type_of_state >> var_eq_tac >>
  every_case_tac >> fs[] >>
  rpt var_eq_tac >> simp[] >>
  qspecl_then[`strlit"bool"`,`[]`,`s`]mp_tac mk_type_thm >>
  simp[] >> strip_tac >>
  rpt var_eq_tac >> simp[] >>
  fs[THM_def] >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >>
  `TERM defs t` by (
    fs[TERM_def] >>
    imp_res_tac proves_term_ok >> fs[] ) >>
  `ACONV t c` by METIS_TAC[aconv_thm] >> fs[] >>
  qspecl_then[`list_to_hypset h []`,`r`]mp_tac map_type_of >>
  simp[] >>
  impl_keep_tac >- (
    rw[EVERY_MEM] >>
    imp_res_tac MEM_list_to_hypset_imp >> fs[EVERY_MEM] ) >>
  strip_tac >>
  conj_tac >- METIS_TAC[term_ok_welltyped,TERM_def] >>
  conj_asm2_tac >- (
    rw[] >> res_tac >>
    fs[EXISTS_MEM] >>
    imp_res_tac proves_term_ok >> fs[EVERY_MEM] >>
    METIS_TAC[aconv_thm,TERM_def] ) >>
  fs[EVERY_MEM] >>
  rw[] >> fs[TERM_def] >>
  fs[MEM_MAP,PULL_EXISTS] >>
  METIS_TAC[term_type,STATE_def,TERM_def,WELLTYPED_LEMMA,WELLTYPED,term_ok_welltyped]
QED

Theorem MK_COMB_thm:
   THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (MK_COMB (th1,th2) s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [MK_COMB_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ SRW_TAC [] [st_ex_bind_def] \\ IMP_RES_TAC THM
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const (strlit "=") h1) f1) f2)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const (strlit "=") h2) x1) x2)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Cases_on `mk_comb (f1,x1) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`f1`,`a`|->`x1`,`res`|->`q`,`s1`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ Cases_on `mk_comb (f2,x2) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`f2`,`a`|->`x2`,`res`|->`q`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ Cases_on `mk_eq (Comb f1 x1,Comb f2 x2) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Comb f1 x1`,
         `y`|->`Comb f2 x2`,`res`|->`q`,`s'`|->`r''`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  rpt(qpat_x_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[] >>
  imp_res_tac Equal_type >> fs[] >>
  imp_res_tac Equal_type_IMP >>
  ntac 2 (pop_assum(mp_tac o SYM)) >>
  `codomain (typeof (f1)) = typeof (Comb (f1) (x1))` by simp[] >>
  pop_assum SUBST1_TAC >> simp_tac std_ss [GSYM equation_def] >>
  rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,7)) >>
  qpat_x_assum`TERM x (Comb f1 x1)`mp_tac >> simp[TERM_Comb] >> strip_tac >>
  fs[TERM_def] >> imp_res_tac term_ok_welltyped >> simp[]
QED

Theorem ABS_thm:
   TERM defs tm /\ THM defs th1 /\ STATE defs s /\
    (ABS tm th1 s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ SIMP_TAC std_ss [ABS_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ FULL_SIMP_TAC std_ss [st_ex_bind_def]
  \\ Cases_on `m = (strlit "=")` \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []
  \\ TRY (
      POP_ASSUM MP_TAC \\
      NTAC 4 BasicProvers.CASE_TAC \\
      STRIP_TAC \\
      FULL_SIMP_TAC std_ss [] \\
      NO_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `THM defs (Sequent l (Comb (Comb (Const (strlit "=") h) t1) t2))`
  \\ Cases_on `mk_abs (tm,t1) s` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (mk_abs_thm |> Q.SPECL [`q`] |> Q.INST [`bvar`|->`tm`,
       `bod`|->`t1`,`s1`|->`r`])
  \\ IMP_RES_TAC THM \\ IMP_RES_TAC TERM \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `mk_abs (tm,t2) s` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (mk_abs_thm |> Q.SPECL [`q`] |> Q.INST [`bvar`|->`tm`,
       `bod`|->`t2`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Cases_on `mk_eq (Abs tm t1,Abs tm t2) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Abs tm t1`,`y`|->`Abs tm t2`,
                                  `res`|->`q`,`s'`|->`r''`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> rpt(qpat_x_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[] >>
  imp_res_tac Equal_type >> fs[] >>
  `typeof (Abs tm t1) = Fun (typeof tm) (typeof t1)` by simp[] >>
  pop_assum(SUBST1_TAC o SYM) >>
  simp[GSYM equation_def] >>
  imp_res_tac Abs_Var >>
  rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,0)) >>
  fs[EVERY_MAP,EVERY_MEM,PULL_EXISTS,TYPE_def,term_type_Var] >>
  imp_res_tac Equal_type_IMP >>
  reverse conj_tac >- METIS_TAC[equation_def] >>
  REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC TERM \\ IMP_RES_TAC VFREE_IN_IMP
QED

Theorem BETA_thm:
   TERM defs tm /\ STATE defs s /\
    (BETA tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  SIMP_TAC std_ss [BETA_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `tm` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ SRW_TAC [] [st_ex_bind_def,st_ex_return_def]
  \\ IMP_RES_TAC TERM \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `t2 = Var name ty` \\ POP_ASSUM (K ALL_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Abs (Var name ty) bod)`
  \\ Cases_on `mk_eq (Comb (Abs (Var name ty) bod) (Var name ty),bod) s`
  \\ IMP_RES_TAC TERM
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Comb (Abs (Var name ty) bod) (Var name ty)`,
         `y`|->`bod`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[] >>
  `typeof (bod) = typeof (Comb (Abs (Var name ty) (bod)) (Var name ty))` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp_tac std_ss [GSYM equation_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,2)) >>
  fs[CONTEXT_def,TERM_def,TYPE_def] >>
  METIS_TAC[extends_theory_ok,init_theory_ok]
QED

Theorem ASSUME_thm:
   TERM defs tm /\ STATE defs s /\
    (ASSUME tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  SIMP_TAC std_ss [ASSUME_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ STRIP_TAC \\ MP_TAC (type_of_thm |> Q.SPEC `tm`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [st_ex_bind_def]
  \\ MP_TAC (mk_type_thm |> Q.SPECL [`strlit"bool"`,`[]`,`s`])
  \\ Cases_on `mk_type (strlit"bool",[]) s`
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY_DEF]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `term_type tm = Bool`
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def,st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> simp[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,1)) >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[STATE_def] >> imp_res_tac term_type >> rfs[] >>
  fs[TERM_def] >>
  imp_res_tac term_ok_welltyped >>
  FULL_SIMP_TAC std_ss [WELLTYPED]
  >> METIS_TAC[CONTEXT_def,extends_theory_ok,init_theory_ok]
QED

Theorem EQ_MP_thm:
   THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (EQ_MP th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [EQ_MP_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [raise_Fail_def]
  \\ SRW_TAC [] [st_ex_bind_def,st_ex_return_def] \\ IMP_RES_TAC THM
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Q.MATCH_ASSUM_RENAME_TAC `THM defs (Sequent l
        (Comb (Comb (Const (strlit "=") h1) t1) t2))`
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> rpt(qpat_x_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[] >>
  imp_res_tac TERM_Eq_x >> pop_assum (assume_tac o SYM) >>
  simp[GSYM equation_def] >> rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,4)) >>
  fs[TERM_Comb] >>
  METIS_TAC[aconv_thm]
QED

Theorem DEDUCT_ANTISYM_RULE_thm:
   THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (DEDUCT_ANTISYM_RULE th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [DEDUCT_ANTISYM_RULE_def,LET_DEF,st_ex_bind_def]
  \\ Cases_on `mk_eq (t,t') s` \\ STRIP_TAC
  \\ IMP_RES_TAC THM
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`t`,
         `y`|->`t'`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> simp[] >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  `EVERY (TERM defs) (term_remove t' l) ∧
   EVERY (TERM defs) (term_remove t l')` by (
    conj_tac >>
    MATCH_MP_TAC EVERY_term_remove >>
    simp[]) >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  simp[GSYM equation_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,3)) >>
  simp[]
QED

val image_lemma = Q.prove(
  `∀f l s g defs res s'.
      (image f l s = (res,s')) ∧ STATE defs s ⇒
      EVERY (λx. ∀s. STATE defs s ⇒
                     ∃r s'. ((f x s = (r,s'))) ∧ STATE defs s' ∧
                            (∀t. (r = Success t) ⇒ (t = g x))) l ⇒
      STATE defs s' ∧ ∀ts. (res = Success ts) ⇒ (ts = term_image g l)`,
  gen_tac >> Induct >> simp[Once image_def] >- (
    simp[st_ex_return_def,Once term_image_def] ) >>
  simp[st_ex_bind_def] >> rpt gen_tac >>
  ntac 2 strip_tac >>
  first_x_assum(qspec_then`s`mp_tac) >> simp[] >> strip_tac >> fs[] >>
  reverse(Cases_on`r`)>>fs[]>-(rw[]) >>
  simp[Once term_image_def] >>
  qpat_x_assum`X = (res,Z)`mp_tac >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  simp[st_ex_return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >> res_tac >> fs[])

Theorem INST_TYPE_thm:
   EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    THM defs th1 /\ STATE defs s /\
    (INST_TYPE theta th1 s = (res, s')) ==>
    STATE defs s' /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [INST_TYPE_def,LET_DEF,st_ex_bind_def]
  \\ STRIP_TAC \\ IMP_RES_TAC THM
  \\ Cases_on `image (inst theta) l s`
  \\ MP_TAC (image_lemma |> ISPECL [``(inst theta) : term -> term M``, ``l : term list``, ``s : hol_refs``, ``(INST theta) : term -> term``, ``defs : update list``])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (fs[EVERY_MEM] >>
    qx_gen_tac`x` >> strip_tac >>
    qx_gen_tac`s9` >> strip_tac >>
    Cases_on`inst theta x s9` >>
    drule (GEN_ALL (inst_thm |> SIMP_RULE std_ss [EVERY_MEM])) >>
    simp[] >>
    METIS_TAC[exc_11] )
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ Cases_on `inst theta t r`
  \\ MP_TAC (inst_thm |> Q.INST [`res`|->`q`,`s'`|->`r'`,`tm`|->`t`,`s`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,6)) >>
  simp[EVERY_MAP] >>
  fs[EVERY_MEM,FORALL_PROD,TYPE_def] >>
  METIS_TAC[]
QED

val image_lemma = Q.prove(
  `∀f l s g defs res s'.
      (image f l s = (res,s')) ∧ STATE defs s ⇒
      EVERY (λx. ∀s. STATE defs s ⇒
                     ∃r s'. ((f x s = (r,s))) ∧
                            (∀t. (r = Success t) ⇒ (t = g x))) l ⇒
      (s' = s) ∧ ∀ts. (res = Success ts) ⇒ (ts = term_image g l)`,
  gen_tac >> Induct >> simp[Once image_def] >- (
    simp[st_ex_return_def,Once term_image_def] ) >>
  simp[st_ex_bind_def] >> rpt gen_tac >>
  ntac 2 strip_tac >>
  first_x_assum(qspec_then`s`mp_tac) >> simp[] >> strip_tac >> fs[] >>
  reverse(Cases_on`r`)>>fs[]>-(rw[]) >>
  simp[Once term_image_def] >>
  qpat_x_assum`X = (res,Z)`mp_tac >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  simp[st_ex_return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >> res_tac >> fs[])

Theorem INST_thm:
   EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
    THM defs th1 /\ STATE defs s /\
    (INST theta th1 s = (res, s')) ==>
    (s' = s) /\ !th. (res = Success th) ==> THM defs th
Proof
  Cases_on `th1` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [holKernelTheory.INST_def,LET_DEF,st_ex_bind_def]
  \\ STRIP_TAC \\ IMP_RES_TAC THM
  \\ Cases_on `image (vsubst theta) l s`
  \\ MP_TAC (image_lemma |> ISPECL [``(vsubst theta) : term -> term M``,``l : term list``,``s : hol_refs``,``(VSUBST theta) : term -> term``,``defs : update list``])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (fs[EVERY_MEM] >> ntac 2 strip_tac >>
    qx_gen_tac`s9`>>strip_tac >>
    Cases_on`vsubst theta x s9` >>
    imp_res_tac (vsubst_thm |> SIMP_RULE std_ss [EVERY_MEM]) >>
    METIS_TAC[])
  \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [st_ex_return_def]
  \\ Cases_on `vsubst theta t s`
  \\ MP_TAC (vsubst_thm |> Q.INST [`res`|->`q`,`s'`|->`r'`,`tm`|->`t`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,5)) >>
  simp[EVERY_MAP,MEM_MAP,PULL_EXISTS] >>
  fs[EVERY_MEM,FORALL_PROD,TERM_def] >>
  METIS_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Verification of definition functions                                      *)
(* ------------------------------------------------------------------------- *)

(* TODO move *)
Theorem ALL_DISTINCT_DISJOINT:
   !xs ys. ALL_DISTINCT (xs ++ ys) ==> DISJOINT (set xs) (set ys)
Proof
  Induct \\ rw []
QED

Theorem TYPE_CONS_EXTEND:
   STATE (d::defs) s /\ TYPE defs ty ==> TYPE (d::defs) ty
Proof
  simp[STATE_def,TYPE_def] >> strip_tac >>
  match_mp_tac type_ok_extend >>
  HINT_EXISTS_TAC >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  Cases_on`d`>>fs[SUBMAP_FUNION]
QED

Theorem TYPE_APPEND_EXTEND:
   STATE (ds++defs) s /\ TYPE defs ty ==> TYPE (ds++defs) ty
Proof
  simp [STATE_def, TYPE_def] \\ strip_tac
  \\ match_mp_tac type_ok_extend
  \\ HINT_EXISTS_TAC
  \\ imp_res_tac CONTEXT_ALL_DISTINCT \\ fs []
  \\ match_mp_tac SUBMAP_FUNION \\ fs []
  \\ disj2_tac
  \\ once_rewrite_tac [DISJOINT_SYM]
  \\ match_mp_tac ALL_DISTINCT_DISJOINT \\ fs []
QED

Theorem TERM_CONS_EXTEND:
   STATE (d::defs) s /\ TERM defs tm ==> TERM (d::defs) tm
Proof
  simp[STATE_def,TERM_def] >> strip_tac >>
  match_mp_tac term_ok_extend >>
  map_every qexists_tac[`tysof(defs)`,`tmsof(defs)`] >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  Cases_on`d`>>fs[SUBMAP_FUNION,LET_THM] >>
  match_mp_tac SUBMAP_FUNION >>
  fs[pred_setTheory.IN_DISJOINT] >>
  fs[ALL_DISTINCT_APPEND] >>
  METIS_TAC[]
QED

Theorem TERM_APPEND_EXTEND:
   STATE (ds++defs) s /\ TERM defs tm ==> TERM (ds++defs) tm
Proof
  simp [STATE_def, TERM_def] \\ strip_tac
  \\ match_mp_tac term_ok_extend
  \\ qexists_tac `tysof(defs)`
  \\ qexists_tac `tmsof(defs)`
  \\ imp_res_tac CONTEXT_ALL_DISTINCT \\ fs []
  \\ conj_tac
  \\ match_mp_tac SUBMAP_FUNION \\ fs []
  \\ disj2_tac
  \\ once_rewrite_tac [DISJOINT_SYM]
  \\ match_mp_tac ALL_DISTINCT_DISJOINT \\ fs []
QED

val STRCAT_SHADOW_def = zDefine`
  STRCAT_SHADOW = STRCAT`

val first_dup_thm = Q.prove(
  `∀ls acc. (first_dup ls acc = NONE) ⇒ ALL_DISTINCT ls ∧ (∀x. MEM x ls ⇒ ¬MEM x acc)`,
  Induct >> simp[Once first_dup_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  strip_tac >> res_tac >>
  fs[MEM] >> METIS_TAC[])

val first_dup_SOME = Q.prove(
  `∀ls acc. (first_dup ls acc = SOME x) ⇒ ¬ALL_DISTINCT (ls++acc)`,
  Induct >> simp[Once first_dup_def] >>
  rw[] >> fs[ALL_DISTINCT_APPEND] >>
  res_tac >> rw[] >> fs[ALL_DISTINCT] >> fs[] >>
  METIS_TAC[])

val add_constants_thm = Q.prove(
  `∀ls s res s'. (add_constants ls s = (res,s')) ⇒
      (∀u. (res = Success u) ∧ ALL_DISTINCT (MAP FST s.the_term_constants) ⇒
           ALL_DISTINCT (MAP FST ls ++ MAP FST s.the_term_constants) ∧
           (s' = s with the_term_constants := ls++s.the_term_constants)) ∧
      (∀msg. (res = Failure msg) ⇒ (s' = s) ∧ (¬ALL_DISTINCT (MAP FST ls ++ MAP FST s.the_term_constants)))`,
  simp_tac std_ss [add_constants_def,GSYM STRCAT_SHADOW_def] >>
  simp[st_ex_bind_def,get_the_term_constants_def] >>
  rpt gen_tac >>
  reverse BasicProvers.CASE_TAC >- (
    simp[raise_Fail_def] >> rw[] >>
    imp_res_tac first_dup_SOME) >>
  imp_res_tac first_dup_thm >>
  strip_tac >>
  Cases_on`res`>>
  fs[set_the_term_constants_def] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  simp[ALL_DISTINCT_APPEND])

(* TODO move *)
Theorem tyvars_EQ_thm:
   holKernel$tyvars = holSyntax$tyvars
Proof
  fs [FUN_EQ_THM]
  \\ recInduct tyvars_ind \\ rw []
  \\ once_rewrite_tac [holSyntaxTheory.tyvars_def, holKernelTheory.tyvars_def] \\ fs []
  \\ pop_assum mp_tac
  \\ Induct_on `tys` \\ rw [] \\ simp [itlist_def]
  \\ first_assum (qspec_then `h` assume_tac)
  \\ simp [union_def, Once itlist_def]
  \\ CASE_TAC \\ fs []
  \\ simp [LIST_UNION_def]
  \\ rename1 `FOLDR LIST_INSERT xs`
  \\ rpt (pop_assum kall_tac)
  \\ qid_spec_tac `xs`
  \\ qid_spec_tac `h'`
  \\ qid_spec_tac `t`
  \\ Induct \\ rw [] \\ simp [itlist_def, LIST_INSERT_def, insert_def]
QED

(* TODO move, unless it already exists elsewhere *)
Theorem LIST_REL_MAP_EQ:
   !r l. LIST_REL (\x y. x = f y) l r ==> (MAP f r = l)
Proof
  Induct \\ rw []
QED

Theorem new_specification_thm:
   THM defs th /\ STATE defs s ==>
    case new_specification th s of
    | (Failure exn, s') => (s' = s)
    | (Success th, s') => (?d. THM (d::defs) th /\
                              STATE (d::defs) s' /\
                              !th. THM defs th ==> THM (d::defs) th)
Proof
  Cases_on`th` >>
  simp_tac std_ss [new_specification_def,GSYM STRCAT_SHADOW_def] >>
  simp[st_ex_bind_def,st_ex_return_def] >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`(f:term -> hol_refs -> ((((mlstring#type)#term), hol_exn) exc#hol_refs)) = X` >>
  `EVERY (λt. term_ok (sigof defs) t ∧ (typeof t = Bool)) (t::l)` by (
    match_mp_tac THM_term_ok_bool >> fs[STATE_def]) >>
  `∀l defs s s'.
    STATE defs s ∧ EVERY (λt. term_ok (sigof defs) t ∧ (typeof t = Bool)) l
    ⇒ (∀res. (map f l s = (Success res,s')) ⇒
     (s' = s) ∧
     LIST_REL
       (λe ((s,ty),t).
         (e = Var s ty === t) ∧ t has_type ty ∧
         CLOSED t ∧ (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))) ∧
         term_ok (sigof (defs)) t ∧ type_ok (tysof (defs)) ty)
       l res) ∧
     (∀msg. (map f l s = (Failure msg,s')) ⇒ (s' = s))` by (
    pop_assum kall_tac >> pop_assum mp_tac >> ntac 2 (pop_assum kall_tac) >> strip_tac >>
    Induct >- simp[map_def,st_ex_return_def] >>
    simp[Once map_def,st_ex_bind_def] >>
    qx_genl_tac[`tm`,`defs`] >>
    rpt gen_tac >> strip_tac >>
    Cases_on`f tm s`>>fs[]>>
    `s = r` by (
      pop_assum mp_tac >>
      simp[Abbr`f`] >>
      mp_tac(Q.GENL[`s'`,`res`]dest_eq_thm) >>
      Cases_on`dest_eq tm s`>>simp[]>>
      `TERM defs tm` by simp[TERM_def] >>
      Cases_on`q'`>>simp[]>>
      qmatch_assum_rename_tac`dest_eq tm s = (Success q',_)` >>
      Cases_on`q'`>>simp[] >> strip_tac >>
      BasicProvers.VAR_EQ_TAC >>
      BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`dest_eq tm s = (Success(v,t),s)` >>
      MP_TAC(Q.GENL[`s'`,`res`]dest_var_thm) >>
      Cases_on`dest_var v s`>>simp[]>>
      Cases_on`q'`>>simp[]>>
      qmatch_assum_rename_tac`dest_var v s = (Success q',_)`>>
      Cases_on`q'`>>simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      simp[raise_Fail_def] ) >>
    BasicProvers.VAR_EQ_TAC >>
    reverse conj_tac >- (
      simp[Once map_def,st_ex_bind_def] >>
      Cases_on`q`>>fs[]>>
      Cases_on`map f l r`>>fs[]>>
      Cases_on`q`>>simp[st_ex_return_def] >>
      rw[] >>
      first_x_assum(qspecl_then[`defs`,`r`]mp_tac) >>
      simp[] ) >>
    Cases_on`q`>>simp[]>>
    Cases_on`map f l r`>>simp[]>>
    Cases_on`q`>>simp[st_ex_return_def]>>
    strip_tac >>
    qmatch_assum_rename_tac`f tm s = _` >>
    qpat_x_assum`f tm s = X`mp_tac >>
    simp[Abbr`f`] >>
    mp_tac(Q.GENL[`s'`,`res`]dest_eq_thm) >>
    `TERM defs tm` by simp[TERM_def] >>
    Cases_on`dest_eq tm s`>>simp[]>>
    Cases_on`q`>>rfs[]>>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`dest_eq tm s = (Success q,_)` >>
    Cases_on`q`>>simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`dest_eq _ s = (Success(v,t),s)` >>
    MP_TAC(Q.GENL[`s'`,`res`]dest_var_thm) >>
    Cases_on`dest_var v s`>>simp[]>>
    Cases_on`q`>>simp[]>>
    qmatch_assum_rename_tac`dest_var v s = (Success q,_)`>>
    Cases_on`q`>>simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC>>
    BasicProvers.CASE_TAC>>
    ntac 2 (pop_assum mp_tac ) >>
    simp_tac(srw_ss())[raise_Fail_def] >>
    ntac 3 strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[] >>
    simp[Once CONJ_SYM,GSYM CONJ_ASSOC] >>
    Cases_on`v`>>TRY(
      fs[holKernelTheory.dest_var_def,raise_Fail_def] >> NO_TAC) >>
    qpat_x_assum`dest_var Z X = Y`mp_tac >>
    simp[holKernelTheory.dest_var_def,st_ex_return_def] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qpat_x_assum`dest_eq tm r = X`mp_tac >>
    simp_tac(srw_ss())[dest_eq_def,raise_Fail_def,st_ex_return_def] >>
    simp[Once equation_def] >>
    qmatch_assum_abbrev_tac`TERM defs (Comb X Y)` >>
    `welltyped (Comb X Y)` by (
      metis_tac[TERM_def,term_ok_welltyped]) >>
    pop_assum mp_tac >>
    simp[Abbr`X`,Abbr`Y`] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    conj_tac >- (metis_tac[WELLTYPED]) >> simp[] >>
    conj_tac >- (
      simp[CLOSED_def] >>
      PROVE_TAC[freesin_IMP,MEM] ) >>
    imp_res_tac WELLTYPED_LEMMA >>
    conj_tac >- (
      fs[subset_def,EVERY_MEM] >>
      METIS_TAC[MEM_type_vars_in_term,tyvars_thm] ) >>
    conj_asm1_tac >- (
      fs[term_ok_def] ) >>
    conj_tac >- (
      imp_res_tac term_ok_type_ok >>
      fs[STATE_def] >> imp_res_tac CONTEXT_std_sig >> fs[] >>
      METIS_TAC[]) >>
    first_x_assum(qspecl_then[`defs`,`r`]mp_tac) >>
    simp[] ) >>
  first_x_assum(qspecl_then[`l`,`defs`,`s`]mp_tac) >>
  Cases_on`map f l s` >> simp[]>>
  reverse(Cases_on`q`)>>simp[] >>
  (impl_tac >- fs[]) >> simp[] >>
  strip_tac >>
  BasicProvers.CASE_TAC >- (
    simp[raise_Fail_def] ) >>
  BasicProvers.CASE_TAC >>
  qspecl_then[`MAP FST a`,`s`]mp_tac add_constants_thm >>
  simp[] >>
  `ALL_DISTINCT (MAP FST s.the_term_constants)` by
    imp_res_tac STATE_ALL_DISTINCT >>
  Cases_on`q`>>simp[] >>
  simp[oneTheory.one] >>
  strip_tac >>
  simp[add_def_def,st_ex_bind_def,get_the_context_def,set_the_context_def] >>
  qpat_x_assum`map f l _ = _`kall_tac >>
  qunabbrev_tac`f` >>
  Q.PAT_ABBREV_TAC`theta:(term#term)list = MAP X (MAP FST a)` >>
  Q.PAT_ABBREV_TAC`d = ConstSpec X h` >>
  Q.PAT_ABBREV_TAC`s':hol_refs = X` >>
  qexists_tac`d` >>
  reverse conj_asm2_tac >- (
    reverse conj_asm1_tac
    >-
     (
      Cases
      \\ once_rewrite_tac [THM_def]
      \\ strip_tac
      \\ irule updates_proves \\ fs []
      \\ `d::defs extends defs` suffices_by fs [Once RTC_CASES1, extends_def]
      \\ fs [STATE_def, CONTEXT_def, Abbr`s'`] \\ rw []
      \\ fs [extends_def, Once RTC_CASES1, init_ctxt_def] \\ rw [] \\ metis_tac []
     ) >>
    fs[STATE_def,Abbr`s'`] >>
    simp[Abbr`d`] >>
    simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
    conj_asm1_tac >- (
      fs[CONTEXT_def] >>
      simp[extends_def] >>
      simp[Once relationTheory.RTC_CASES1] >> disj2_tac >>
      simp[GSYM extends_def] >> rfs[] >>
      simp[updates_cases] >>
      conj_tac >- (
        fs[THM_def] >>
        qmatch_abbrev_tac`(thy,hh) |- cc` >>
        qmatch_assum_abbrev_tac`(thy,hh1) |- cc` >>
        `hh = hh1` by (
          UNABBREV_ALL_TAC >>
          simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
          fs[EVERY2_EVERY] >>
          rfs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,UNCURRY] >>
          simp[LIST_EQ_REWRITE,EL_MAP] >>
          simp[equation_def] >>
          METIS_TAC[WELLTYPED_LEMMA] ) >>
        rw[] ) >>
      simp[EVERY_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      fs[EVERY2_EVERY] >>
      rfs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,UNCURRY] >>
      simp[MEM_MAP,PULL_EXISTS] >>
      simp[Once MEM_EL,PULL_EXISTS] >>
      conj_tac >- (
        imp_res_tac freesin_IMP >> rw[] >>
        res_tac >>
        rfs[TERM_def,PULL_EXISTS,MEM_MAP] >>
        res_tac >>
        METIS_TAC[tyvars_thm]) >>
      simp[Once MEM_EL,PULL_EXISTS] >>
      fs[ALL_DISTINCT_APPEND,MAP_MAP_o,combinTheory.o_DEF] >>
      qpat_x_assum`X = FLAT Y`(assume_tac o SYM) >> fs[] >>
      fs[MEM_MAP,PULL_EXISTS,UNCURRY] >>
      rw[EXISTS_PROD] >>
      imp_res_tac THM >>
      imp_res_tac freesin_IMP >>
      fs[MEM_MAP,EXISTS_PROD] >>
      fs[MEM_EL] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[] >>
      qpat_x_assum`X = EL n a`(mp_tac o SYM) >> simp[] >>
      rw[] >>
      METIS_TAC[WELLTYPED_LEMMA]) >>
    simp[MAP_EQ_f] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,UNCURRY,PULL_EXISTS] >>
    simp[MEM_EL,PULL_EXISTS] >>
    rw[] >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    Cases_on`EL n a`>>simp[]>>Cases_on`q`>>rw[]>>
    METIS_TAC[term_ok_welltyped,WELLTYPED_LEMMA] ) >>
  fs [] >>
  simp[THM_def] >>
  qspecl_then[`s'`,`d::defs`,`theta`,`t`]mp_tac
    (Q.GENL[`s`,`defs`](CONV_RULE (RESORT_FORALL_CONV List.rev) vsubst_aux_thm)) >>
  simp[] >>
  match_mp_tac IMP_IMP >>
  conj_asm1_tac >- (
    reverse conj_tac >- (
      match_mp_tac (GEN_ALL TERM_CONS_EXTEND) >>
      fs[TERM_def,THM_def] >>
      METIS_TAC[] ) >>
    simp[Abbr`theta`,EVERY_MAP] >>
    simp[EVERY_MEM,UNCURRY,Once term_type_def,is_var_def] >>
    simp[Once term_type_def,TERM_Var_SIMP] >>
    ntac 2 strip_tac >>
    conj_asm1_tac >- (
      match_mp_tac (GEN_ALL TERM_Const) >>
      HINT_EXISTS_TAC >>
      simp[Abbr`s'`,MEM_MAP] >>
      METIS_TAC[] ) >>
    simp[TYPE_def] >>
    fs[TERM_def,term_ok_def]) >>
  strip_tac >> simp[] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,9)) >>
  conj_tac >- (
    fs[STATE_def,CONTEXT_def] >>
    imp_res_tac extends_theory_ok >>
    fs[init_theory_ok] >> rfs[] ) >>
  simp[Abbr`d`,conexts_of_upd_def] >>
  disj1_tac >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,Abbr`theta`] >>
  simp[MAP_EQ_f] >>
  fs[EVERY2_EVERY,EVERY_MEM,MEM_EL,PULL_EXISTS,UNCURRY] >>
  rfs[EL_ZIP,PULL_EXISTS] >>
  METIS_TAC[term_ok_welltyped,WELLTYPED_LEMMA]
QED

val _ = delete_const"STRCAT_SHADOW"

Theorem new_basic_definition_thm:
   TERM defs tm /\ STATE defs s ==>
    case new_basic_definition tm s of
    | (Failure exn, s') => (s' = s)
    | (Success th, s') => (?d. THM (d::defs) th /\
                               STATE (d::defs) s' /\
                               !th. THM defs th ==> THM (d::defs) th)
Proof
  rw[] >>
  simp[new_basic_definition_def,st_ex_bind_def] >>
  Cases_on`ASSUME tm s` >>
  imp_res_tac ASSUME_thm >>
  Cases_on`q`>>fs[] >>
  imp_res_tac new_specification_thm
QED

Theorem new_basic_type_definition_thm:
   THM defs th /\ STATE defs s ==>
    case new_basic_type_definition tyname absname repname th s of
    | (Failure exn, s') => (s' = s)
    | (Success (th1,th2), s') =>
      (?ds. THM (ds++defs) th1 /\ THM (ds++defs) th2 /\
            STATE (ds++defs) s' /\
            !th. THM defs th ==> THM (ds++defs) th)
Proof
  Cases_on `th` \\ SIMP_TAC (srw_ss())
     [new_basic_type_definition_def, Once st_ex_bind_def, st_ex_return_def,
      Once st_ex_ignore_bind_def,
      raise_Fail_def,
      can_def |> SIMP_RULE std_ss [otherwise_def,st_ex_ignore_bind_def,
                                   st_ex_bind_def, st_ex_return_def]] >>
  strip_tac >>
  qspecl_then[`tyname`,`s`]mp_tac get_type_arity_thm >>
  Cases_on`get_type_arity tyname s`>>simp[]>>strip_tac>>
  qspecl_then[`absname`,`s`]mp_tac get_const_type_thm >>
  qspecl_then[`repname`,`s`]mp_tac get_const_type_thm >>
  Cases_on`get_const_type absname s`>>simp[]>>strip_tac>>
  Cases_on`get_const_type repname s`>>simp[]>>strip_tac>>
  ntac 2 (simp[Once st_ex_bind_def]) >>
  Cases_on`q`>>fs[]>>
  BasicProvers.CASE_TAC >> simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  Cases_on`absname = repname`>>simp[]>>
  Cases_on `l = []` \\ FULL_SIMP_TAC (srw_ss()) [Once st_ex_bind_def,try_def] >>
  Cases_on`t`>>simp[dest_comb_def,raise_Fail_def,otherwise_def,st_ex_return_def] >>
  Q.MATCH_ASSUM_RENAME_TAC `THM defs (Sequent [] (Comb P x))` >>
  Cases_on `freesin [] P` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF] >>
  simp[Once st_ex_bind_def] >>
  qspec_then`x`mp_tac type_of_thm >>
  impl_tac >- METIS_TAC[STATE_def,TERM_Comb,THM] >>
  simp[] >> disch_then kall_tac >>
  simp[Once st_ex_bind_def] >>
  Q.PAT_ABBREV_TAC`vs:string list = QSORT R X` >>
  simp[add_type_def,can_def,otherwise_def,st_ex_return_def] >>
  ntac 2 (simp[Once st_ex_bind_def]) >>
  simp[Once st_ex_bind_def,get_the_type_constants_def] >>
  simp[Once st_ex_bind_def,set_the_type_constants_def] >>
  simp[Once st_ex_ignore_bind_def] >>
  Q.PAT_ABBREV_TAC `s1 = (s with
      <|the_type_constants := Y::s.the_type_constants|>)` >>
  `get_type_arity tyname s1 = (Success (LENGTH vs), s1)` by (
    simp[get_type_arity_def,st_ex_bind_def,Abbr`s1`] >>
    EVAL_TAC ) >>
  simp[mk_type_def,try_def,otherwise_def,raise_Fail_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[mk_fun_ty_def] >>
  `get_type_arity (strlit "fun") s1 = (Success 2, s1)` by (
    qspecl_then[`(strlit "fun")`,`s1`]mp_tac get_type_arity_thm >>
    Cases_on`get_type_arity (strlit "fun") s1`>>simp[] >>strip_tac >>
    qunabbrev_tac`s1` >> fs[STATE_def] >>
    imp_res_tac CONTEXT_fun >> rfs[] >>
    METIS_TAC[exc_distinct,exc_11,exc_nchotomy] ) >>
  SIMP_TAC (srw_ss()) [mk_type_def,try_def,otherwise_def] >>
  ntac 4(simp[Once st_ex_bind_def,st_ex_return_def]) >>
  Q.PAT_ABBREV_TAC`l1 = [(absname,Fun (X:type) Y);Z]` >>
  qspecl_then[`l1`,`s1`]mp_tac add_constants_thm >>
  Cases_on`add_constants l1 s1` >>
  simp[Once st_ex_bind_def] >> strip_tac >>
  imp_res_tac STATE_ALL_DISTINCT >>
  reverse(Cases_on`q`)>>fs[]>-(
    fs[Abbr`l1`]>>fs[Abbr`s1`,MEM_MAP,EXISTS_PROD] >>
    METIS_TAC[] ) >>
  `s1.the_term_constants = s.the_term_constants` by simp[Abbr`s1`] >>
  fs[oneTheory.one] >>
  simp[Once st_ex_bind_def,add_def_def,get_the_context_def] >>
  simp[Once st_ex_bind_def,set_the_context_def] >>
  Q.PAT_ABBREV_TAC`s2 = s1 with <|the_term_constants := X; the_context := Y|>` >>
  `STATE s2.the_context s2` by (
    fs[STATE_def] >>
    conj_asm1_tac >- (
      simp[Abbr`s2`] >>
      fs[CONTEXT_def] >>
      match_mp_tac extends_trans >>
      qexists_tac`defs` >> simp[] >>
      simp[extends_def,Once relationTheory.RTC_CASES1] >>
      disj2_tac >> simp[Once relationTheory.RTC_CASES1] >>
      simp[Abbr`s1`] >>
      simp[updates_cases] >>
      rfs[MEM_MAP,EXISTS_PROD] >>
      qexists_tac`x` >>
      conj_tac >- fs[THM_def] >>
      imp_res_tac THM_term_ok_bool >>
      fs[term_ok_def] >>
      fs[CLOSED_def] >>
      imp_res_tac freesin_IMP >>
      rfs[TERM_def] >> METIS_TAC[]) >>
    imp_res_tac THM >> rfs[TERM_Comb] >>
    imp_res_tac QSORT_type_vars_in_term >>
    imp_res_tac THM_term_ok_bool >>
    fs[term_ok_def] >>
    rfs[WELLTYPED] >>
    simp[Abbr`s2`,Abbr`s1`,Abbr`vs`,Abbr`l1`
        ,MAP_MAP_o,combinTheory.o_DEF,ETA_AX] >>
    METIS_TAC[term_type]) >>
  qmatch_assum_abbrev_tac`Abbrev(l1 = [(absname,absty);(repname,repty)])` >>
  `mk_const (repname,[]) s2 = (Success (Const repname repty), s2)` by (
    simp[Abbr`s2`,Abbr`s1`,Abbr`l1`] >>
    simp[mk_const_def,st_ex_bind_def,try_def,get_const_type_def
        ,get_the_term_constants_def,raise_Fail_def,otherwise_def] >>
    simp[Once assoc_def,st_ex_return_def] >>
    simp[Once assoc_def,st_ex_return_def] >>
    simp[type_subst_EMPTY] ) >>
  `mk_const (absname,[]) s2 = (Success (Const absname absty), s2)` by (
    simp[Abbr`s2`,Abbr`s1`,Abbr`l1`] >>
    simp[mk_const_def,st_ex_bind_def,try_def,get_const_type_def
        ,get_the_term_constants_def,raise_Fail_def,otherwise_def] >>
    simp[Once assoc_def,st_ex_return_def] >>
    simp[type_subst_EMPTY] ) >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  Q.PAT_ABBREV_TAC`a = mk_var X` >>
  rpt(qpat_x_assum`Z = s`kall_tac)>>
  Cases_on`mk_comb (Const repname repty,a) s2` >>
  MP_TAC (mk_comb_thm |> Q.INST [`f`|->`Const repname repty`,`res`|->`q`,`s1`|->`r`,`s`|->`s2`,`defs`|->`s2.the_context`]) >>
  impl_tac >- (
    simp[] >>
    conj_asm1_tac >- METIS_TAC[mk_const_thm,EVERY_DEF] >>
    imp_res_tac TERM >>
    simp[Abbr`a`,mk_var_def,TERM_Var_SIMP] >>
    qunabbrev_tac`repty` >>
    imp_res_tac TYPE >> fs[] ) >>
  simp[Once term_type_def,Abbr`repty`,Abbr`a`] >>
  simp[mk_var_def,Once term_type_def] >>
  strip_tac >> Cases_on`q`>>fs[] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Abbr`absty`] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_eq_def,try_def,otherwise_def,type_of_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  imp_res_tac mk_const_eq >>
  simp[Once st_ex_bind_def] >>
  simp[inst_def] >>
  simp[inst_aux_def,type_subst_def,rev_assocd_thm,REV_ASSOCD,mk_vartype_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  rpt(qpat_x_assum`Z = s2`kall_tac)>>
  `TERM s2.the_context (Comb P x)` by (
    imp_res_tac THM_term_ok_bool >> fs[] >>
    simp[TERM_def] >>
    match_mp_tac term_ok_extend >>
    map_every qexists_tac[`tysof (defs)`,`tmsof (defs)`] >>
    rfs[LET_THM,Abbr`s2`,Abbr`s1`,STATE_def] >>
    simp[MEM_MAP,EXISTS_PROD] >>
    simp[SUBMAP_DEF,MEM_MAP,EXISTS_PROD] >>
    qpat_x_assum`X = const_list Y`(assume_tac o SYM) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[MEM_MAP,EXISTS_PROD] >>
    simp[FAPPLY_FUPDATE_THM] >>
    rw[] >> METIS_TAC[]) >>
  `mk_comb (P,Var (strlit "r") (term_type x)) s2 = (Success (Comb P (Var (strlit "r") (term_type x))), s2)` by (
    Cases_on`mk_comb (P,Var (strlit "r") (term_type x)) s2` >>
    MP_TAC (mk_comb_thm |> Q.INST [`f`|->`P`,`a`|->`Var (strlit "r") (term_type x)`,`res`|->`q`,`s1`|->`r`,`s`|->`s2`,`defs`|->`s2.the_context`]) >>
    impl_tac >- (
      rfs[STATE_def,TERM_Comb,TERM_Var_SIMP] >>
      imp_res_tac term_type ) >>
    strip_tac >>
    fs[term_type_Var] >>
    imp_res_tac THM_term_ok_bool >>
    fs[term_ok_def] >>
    fs[STATE_def] >>
    imp_res_tac CONTEXT_std_sig >>
    `TERM defs P ∧ TERM defs x` by simp[TERM_def] >>
    imp_res_tac term_type >>
    rfs[] >> fs[] >>
    Cases_on`q`>>fs[] ) >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_eq_def,try_def,otherwise_def,type_of_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def,mk_vartype_def,mk_eq_lemma,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[mk_eq_def,try_def,otherwise_def,Once type_of_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  `CONTEXT s2.the_context` by fs[STATE_def] >>
  fs[TERM_Comb] >>
  imp_res_tac type_of_thm >>
  imp_res_tac term_type >>
  rfs[] >>
  simp[dest_type_def,st_ex_return_def,Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  imp_res_tac THM_term_ok_bool >> fs[] >>
  fs[term_ok_def] >> rfs[] >>
  fs[] >>
  simp[Once st_ex_bind_def] >>
  simp[inst_def,inst_aux_def,type_subst_def,rev_assocd_thm,REV_ASSOCD,mk_vartype_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,Once type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once type_of_def] >>
  simp[Once st_ex_bind_def,dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once mk_comb_def,Once type_of_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once type_of_def] >>
  simp[Once st_ex_bind_def,dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once type_of_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once type_of_def] >>
  simp[Once st_ex_bind_def] >>
  simp[Once type_of_def] >>
  simp[Once st_ex_bind_def,dest_type_def,st_ex_return_def] >>
  simp[Once st_ex_bind_def] >>
  `∃ds. s2.the_context = ds ++ defs` by (
    fs[Abbr`s2`,Abbr`s1`,STATE_def] ) >>
  qexists_tac`ds` >>
  pop_assum(ASSUME_TAC o SYM) >>
  simp[] >>
  simp[THM_def,ETA_AX] >>
  conj_tac
  >-
   (match_mp_tac (List.nth(CONJUNCTS proves_rules,9))
    \\ conj_tac
    >- METIS_TAC[STATE_def,CONTEXT_def,extends_theory_ok,init_theory_ok]
    \\ simp [Abbr`s2`,conexts_of_upd_def]
    \\ imp_res_tac QSORT_type_vars_in_term
    \\ simp [equation_def,Abbr`vs`,MAP_MAP_o,combinTheory.o_DEF,ETA_AX])
  \\ conj_tac
  >-
   (match_mp_tac (List.nth(CONJUNCTS proves_rules,9))
    \\ conj_tac
    >- METIS_TAC[STATE_def,CONTEXT_def,extends_theory_ok,init_theory_ok]
    \\ simp [Abbr`s2`,conexts_of_upd_def]
    \\ imp_res_tac QSORT_type_vars_in_term
    \\ simp [equation_def,Abbr`vs`,MAP_MAP_o,combinTheory.o_DEF,ETA_AX])
  \\ Cases
  \\ once_rewrite_tac [THM_def]
  \\ strip_tac
  \\ irule extends_proves
  \\ HINT_EXISTS_TAC \\ fs []
  \\ fs [STATE_def, CONTEXT_def, Abbr`s2`, Abbr`s1`] \\ rw []
  \\ fs [extends_def, Once RTC_CASES1, init_ctxt_def]
QED

(* ------------------------------------------------------------------------- *)
(* Verification of context extension functions                               *)
(* ------------------------------------------------------------------------- *)

Theorem new_type_thm:
   STATE defs s ⇒
    case new_type (name,arity) s of
    | (Failure exn, s') => (s' = s)
    | (Success (), s') => (?d. STATE (d::defs) s' /\
                               !th. THM defs th ==> THM (d::defs) th)
Proof
  rw[new_type_def,st_ex_bind_def,add_type_def,can_def,get_type_arity_def,
      get_the_type_constants_def,otherwise_def,st_ex_return_def,raise_Fail_def,
      st_ex_ignore_bind_def] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  imp_res_tac assoc_thm >>
  rw[set_the_type_constants_def,add_def_def,st_ex_bind_def
    ,get_the_context_def,set_the_context_def] >>
  qexists_tac`NewType name arity` >>
  conj_tac >- (
    fs[STATE_def] >>
    fs[CONTEXT_def] >>
    simp[extends_def,Once relationTheory.RTC_CASES1] >>
    disj2_tac >> simp[GSYM extends_def] >>
    rfs[updates_cases,MEM_MAP,EXISTS_PROD] ) >>
  Cases \\ once_rewrite_tac [THM_def] \\ strip_tac
  \\ irule updates_proves \\ fs []
  \\ simp [updates_cases]
  \\ fs [STATE_def, CONTEXT_def] \\ rveq
  \\ CCONTR_TAC \\ fs [MEM_MAP]
  \\ PairCases_on `y` \\ fs []
  \\ metis_tac []
QED

Theorem new_constant_thm:
   STATE defs s ∧ TYPE defs ty ⇒
    case new_constant (name,ty) s of
    | (Failure exn, s') => (s' = s)
    | (Success (), s') => (?d. STATE (d::defs) s' /\
                           !th. THM defs th ==> THM (d::defs) th)
Proof
  rw[new_constant_def,st_ex_bind_def] >>
  qspecl_then[`[(name,ty)]`,`s`]mp_tac add_constants_thm >>
  Cases_on`add_constants [(name,ty)] s`>>simp[] >>
  Cases_on`q`>>simp[oneTheory.one] >>
  imp_res_tac STATE_ALL_DISTINCT >> rw[] >>
  rw[add_def_def,st_ex_bind_def,get_the_context_def,set_the_context_def] >>
  qexists_tac`NewConst name ty` >>
  conj_tac >- (
    fs[STATE_def] >>
    fs[CONTEXT_def] >>
    simp[extends_def,Once relationTheory.RTC_CASES1] >>
    disj2_tac >> simp[GSYM extends_def] >>
    rfs[updates_cases,MEM_MAP,EXISTS_PROD] >>
    fs[TYPE_def] ) >>
  Cases \\ once_rewrite_tac [THM_def] \\ strip_tac
  \\ irule updates_proves \\ fs []
  \\ simp [updates_cases]
  \\ fs [STATE_def, CONTEXT_def] \\ rveq
  \\ conj_tac
  >- (CCONTR_TAC \\ fs [MEM_MAP] \\ metis_tac [])
  \\ fs [TYPE_def]
QED

Theorem new_axiom_thm:
   STATE defs s ∧ TERM defs p ⇒
    case new_axiom p s of
    | (Failure exn, s') => (s' = s)
    | (Success th, s') => (?d. THM (d::defs) th ∧ STATE (d::defs) s' /\
                               !th. THM defs th ==> THM (d::defs) th)
Proof
  rw[new_axiom_def,st_ex_bind_def] >>
  imp_res_tac type_of_thm >> rw[] >>
  qspecl_then[`(strlit "bool")`,`[]`,`s`]mp_tac mk_type_thm >>
  Cases_on`mk_type ((strlit "bool"),[]) s`>>simp[] >>
  Cases_on`q`>>simp[]>>strip_tac>>
  BasicProvers.CASE_TAC >> simp[raise_Fail_def,st_ex_return_def] >>
  simp[get_the_axioms_def,set_the_axioms_def] >>
  simp[add_def_def,st_ex_bind_def,get_the_context_def,set_the_context_def] >>
  qexists_tac`NewAxiom p` >>
  conj_asm2_tac >- (
    REWRITE_TAC[THM_def] >>
    MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,9)) >>
    reverse conj_tac >- simp[] >>
    METIS_TAC[STATE_def,CONTEXT_def,extends_theory_ok,init_theory_ok] ) >>
  conj_tac >- (
    fs[STATE_def,lift_tm_def] >>
    imp_res_tac term_type >>
    fs[CONTEXT_def] >>
    simp[extends_def,Once relationTheory.RTC_CASES1] >>
    disj2_tac >> simp[GSYM extends_def] >>
    rfs[updates_cases,MEM_MAP,EXISTS_PROD] >>
    fs[TERM_def] >>
    METIS_TAC[term_ok_welltyped,WELLTYPED] ) >>
  Cases \\ once_rewrite_tac [THM_def] \\ strip_tac
  \\ irule updates_proves \\ fs []
  \\ simp [updates_cases]
  \\ reverse conj_asm2_tac >- fs [TERM_def]
  \\ metis_tac [type_of_has_type]
QED

(* ------------------------------------------------------------------------- *)
(* Removing clash exceptions                                                 *)
(* ------------------------------------------------------------------------- *)

(* Support theorems *)

Theorem map_not_clash_thm:
   !f xs s.
   (!x s. f x s <> (Failure (Clash tm),refs)) ==>
   map f xs s <> (Failure (Clash tm),refs)
Proof
   recInduct map_ind \\ rw [] \\ once_rewrite_tac [map_def]
   \\ fs [st_ex_bind_def, st_ex_return_def]
   \\ every_case_tac \\ fs [] \\ metis_tac []
QED

Theorem forall_clash_thm:
   !f l s.
    (!x s. f x s <> (Failure (Clash tm),refs)) ==>
    forall f l s <> (Failure (Clash tm),refs)
Proof
  recInduct forall_ind \\ rw [] \\ once_rewrite_tac [forall_def]
  \\ fs [st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs [] \\ metis_tac []
QED

Theorem image_clash_thm:
   !f l s.
    (!x s. f x s <> (Failure (Clash tm),refs)) ==>
    image f l s <> (Failure (Clash tm),refs)
Proof
  recInduct image_ind \\ rw [] \\ once_rewrite_tac [image_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ metis_tac []
QED

(* Function specific theorems *)

Theorem dest_type_not_clash[simp]:
   dest_type x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem mk_fun_ty_not_clash[simp]:
   mk_fun_ty t a r ≠ (Failure(Clash tm),refs)
Proof
  Cases_on`t`
  \\ rw [mk_fun_ty_def, mk_type_def, st_ex_bind_def, st_ex_return_def,
         raise_Fail_def, try_def, otherwise_def]
  \\ fs [case_eq_thms, bool_case_eq, COND_RATOR]
QED

Theorem type_of_not_clash[simp]:
   ∀x y. type_of x y ≠ (Failure (Clash tm),refs)
Proof
  recInduct type_of_ind
  \\ rw[]
  \\ rw[Once type_of_def,st_ex_bind_def,raise_Fail_def,case_eq_thms]
  \\ CASE_TAC \\ fs[st_ex_return_def,case_eq_thms]
  \\ CCONTR_TAC \\ fs[pair_case_eq] \\ rw[] \\ fs[] \\ rfs[]
  \\ every_case_tac \\ fs[] \\ rfs[]
QED

Theorem mk_abs_not_clash[simp]:
   mk_abs x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC \\ CASE_TAC \\ fs[]
QED

Theorem mk_comb_not_clash[simp]:
   mk_comb x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ rw[mk_comb_def,st_ex_bind_def,case_eq_thms]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[raise_Fail_def,st_ex_return_def]
QED

Theorem mk_eq_not_clash[simp]:
   mk_eq x y ≠ (Failure(Clash tm),refs)
Proof
  Cases_on`x` \\ rw[mk_eq_def,st_ex_bind_def,try_def,otherwise_def,case_eq_thms]
  \\ CCONTR_TAC \\ fs[st_ex_return_def,raise_Fail_def] \\ rw[]
QED

Theorem ABS_not_clash[simp]:
   ABS x y z ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`y` \\ rw [ABS_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ every_case_tac \\ fs [case_eq_thms] \\ CCONTR_TAC \\ fs []
QED

Theorem MK_COMB_not_clash[simp]:
   MK_COMB (a,b) c <> (Failure (Clash tm), refs)
Proof
  Cases_on `a` \\ Cases_on `b` \\ rw [MK_COMB_def]
  \\ rw [raise_Fail_def, st_ex_return_def, st_ex_bind_def]
  \\ every_case_tac \\ fs [case_eq_thms]
  \\ CCONTR_TAC \\ fs []
QED

Theorem mk_type_not_clash[simp]:
   !a b. mk_type a b <> (Failure (Clash tm), refs)
Proof
  Cases \\ once_rewrite_tac [mk_type_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def, try_def, otherwise_def]
  \\ fs [case_eq_thms, bool_case_eq, COND_RATOR]
QED

Theorem ASSUME_not_clash[simp]:
   !a b. ASSUME a b <> (Failure (Clash tm), refs)
Proof
  Cases \\ rw [ASSUME_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ rw [case_eq_thms, bool_case_eq, COND_RATOR]
QED

Theorem BETA_not_clash[simp]:
   BETA a b <> (Failure (Clash tm),refs)
Proof
  strip_tac \\ Cases_on `a`
  \\ fs [BETA_def, raise_Fail_def, st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem mk_const_not_clash[simp]:
   mk_const (a,b) c <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ once_rewrite_tac [mk_const_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def, try_def, otherwise_def,
         case_eq_thms]
QED

Theorem assoc_not_clash[simp]:
   !a b c. assoc a b c <> (Failure (Clash tm),refs)
Proof
  recInduct assoc_ind \\ rw [] \\ once_rewrite_tac [assoc_def]
  \\ every_case_tac \\ fs [raise_Fail_def,st_ex_return_def]
QED

Theorem get_const_type_not_clash[simp]:
   get_const_type a b <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ rw [get_const_type_def,st_ex_bind_def,case_eq_thms, get_the_term_constants_def]
QED

Theorem DEDUCT_ANTISYM_RULE_not_clash[simp]:
   DEDUCT_ANTISYM_RULE a b c <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ Cases_on `b` \\ once_rewrite_tac [DEDUCT_ANTISYM_RULE_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def, case_eq_thms]
QED

Theorem SYM_not_clash[simp]:
   SYM a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ fs [raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []
QED

Theorem dest_comb_not_clash[simp]:
   dest_comb a b <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem dest_eq_not_clash[simp]:
   dest_eq a b <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ EVAL_TAC \\ fs [raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []
QED

Theorem EQ_MP_not_clash[simp]:
   EQ_MP a b c <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ Cases_on`b` \\ rw [EQ_MP_def, raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []
QED

Theorem PROVE_HYP_not_clash[simp]:
   PROVE_HYP a b c <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ Cases_on `b` \\ rw [PROVE_HYP_def, st_ex_return_def]
QED

Theorem REFL_not_clash[simp]:
   REFL a b <> (Failure (Clash tm),refs)
Proof
  rw [REFL_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem TRANS_not_clash[simp]:
   TRANS a b c <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ Cases_on `b`
  \\ rw [TRANS_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs []
QED

Theorem ALPHA_THM_not_clash[simp]:
   !a b c d. ALPHA_THM a (b, c) d <> (Failure (Clash tm),refs)
Proof
  recInduct ALPHA_THM_ind
  \\ rw [ALPHA_THM_def, raise_Fail_def, st_ex_return_def, st_ex_bind_def]
  \\ rw [case_eq_thms, bool_case_eq, COND_RATOR, map_not_clash_thm]
QED

Theorem add_constants_not_clash[simp]:
   add_constants a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ rw [add_constants_def, st_ex_bind_def, st_ex_return_def,
                      raise_Fail_def, get_the_term_constants_def,
                      set_the_term_constants_def]
  \\ every_case_tac \\ fs []
QED

Theorem add_def_not_clash[simp]:
   add_def a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
QED

Theorem dest_var_not_clash[simp]:
   dest_var a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs [raise_Fail_def, st_ex_return_def]
QED

Theorem new_specification_not_clash[simp]:
   new_specification a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ rw [new_specification_def, st_ex_bind_def, raise_Fail_def,
                      st_ex_return_def, case_eq_thms, bool_case_eq, COND_RATOR]
  \\ ho_match_mp_tac map_not_clash_thm \\ rw []
  \\ rw [case_eq_thms, bool_case_eq, COND_RATOR, ELIM_UNCURRY]
QED

Theorem new_basic_definition_not_clash[simp]:
   new_basic_definition a b <> (Failure (Clash tm),refs)
Proof
  fs [new_basic_definition_def, st_ex_bind_def, case_eq_thms]
QED

Theorem add_type_not_clash[simp]:
   add_type (a,b) c <> (Failure (Clash tm),refs)
Proof
  rw [add_type_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def, can_def,
      get_type_arity_def, get_the_type_constants_def, set_the_type_constants_def,
      otherwise_def]
  \\ rw [case_eq_thms, bool_case_eq, COND_RATOR]
QED

Theorem new_basic_type_definition_not_clash[simp]:
   new_basic_type_definition a b c d e <> (Failure (Clash tm),refs)
Proof
  Cases_on `d` \\ rw [new_basic_type_definition_def, st_ex_bind_def,
                      st_ex_return_def, raise_Fail_def, can_def,
                      get_type_arity_def, get_the_type_constants_def,
                      otherwise_def, try_def, case_eq_thms, bool_case_eq,
                      COND_RATOR, ELIM_UNCURRY]
QED

Theorem vsubst_not_clash[simp]:
   vsubst x y s <> (Failure (Clash tm),refs)
Proof
  rw [vsubst_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
      ELIM_UNCURRY, case_eq_thms, bool_case_eq, COND_RATOR]
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ fs []
  \\ ho_match_mp_tac forall_clash_thm \\ rw [case_eq_thms]
QED

Theorem INST_not_clash[simp]:
   INST theta x s <> (Failure (Clash tm),refs)
Proof
  Cases_on `x` \\ rw [holKernelTheory.INST_def, st_ex_bind_def, st_ex_return_def,
                      case_eq_thms, image_clash_thm]
QED

(* TODO Prove for inst_aux *)

(*
Theorem variant_same_ty:
   !x z c d.
     variant x z = Var c d
     ==>
     ?a b. z = Var a b /\ b = d
Proof
  recInduct holSyntaxExtraTheory.variant_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once holSyntaxExtraTheory.variant_def]
  \\ every_case_tac \\ fs []
QED

Theorem vsubst_same_Var[simp]:
   vsubst_aux [(Var a b, Var c d)] (Var c d) = Var a b
Proof
  once_rewrite_tac [vsubst_aux_def] \\ fs []
  \\ once_rewrite_tac [rev_assocd_def] \\ fs []
QED

Theorem inst_aux_clash_is_var:
   !env tyin tm s f t.
     inst_aux env tyin tm s = (Failure (Clash f),t)
     ==>
     ?a b. f = Var a b
Proof
  recInduct inst_aux_ind \\ rw []
  \\ pop_assum mp_tac
  \\ Cases_on `tm` \\ fs []
  \\ once_rewrite_tac [inst_aux_def] \\ fs []
  \\ simp [st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ simp [handle_Clash_def, raise_Clash_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
QED

val sizeof'_def = Define`
  sizeof' (Comb s t) = 1 + sizeof' s + sizeof' t ∧
  sizeof' (Abs v t) = 1 + sizeof' v + sizeof' t ∧
  sizeof' _ = 1n`;
val _ = export_rewrites["sizeof'_def"];

Theorem sizeof'_rev_assocd:
   ∀x  l d.
   sizeof' d = sizeof' x ∧
   EVERY (λp. sizeof' (FST p) = sizeof' (SND p)) l ⇒
   sizeof' (rev_assocd x l d) = sizeof' x
Proof
  simp[rev_assocd_thm]
  \\ Induct_on`l` \\ rw[holSyntaxLibTheory.REV_ASSOCD_def]
QED

Theorem sizeof'_variant[simp]:
   ∀avoid tm. sizeof' (variant avoid tm) = sizeof' tm
Proof
  recInduct holSyntaxExtraTheory.variant_ind
  \\ rw[]
  \\ rw[Once holSyntaxExtraTheory.variant_def]
  \\ CASE_TAC \\ fs[]
QED

Theorem sizeof'_vsubst_aux:
   ∀tm ss.
    EVERY (λp. sizeof' (FST p) = sizeof' (SND p)) ss ⇒
      sizeof' (vsubst_aux ss tm) = sizeof' tm
Proof
  Induct \\ rw[]
  \\ TRY (
    rw[Once vsubst_aux_def]
    \\ DEP_REWRITE_TAC[sizeof'_rev_assocd]
    \\ simp[]
    \\ NO_TAC )
  \\ rw[Once vsubst_aux_def]
  \\ TRY (
    first_x_assum match_mp_tac
    \\ simp[EVERY_FILTER]
    \\ fs[EVERY_MEM]
    \\ NO_TAC)
QED

Theorem inst_aux_clash_is_var_in_env:
   !n tm env tyin s f t.
     sizeof' tm = n ∧
     inst_aux env tyin tm s = (Failure (Clash f),t)
     ==>
     ?a b. f = Var a b /\ MEM f (MAP SND env) /\ (∀y t. tm <> Abs y t)
Proof
  gen_tac
  \\ completeInduct_on`n`
  \\ Induct
  \\ simp[Once inst_aux_def]
  \\ rw[st_ex_return_def,st_ex_bind_def,raise_Fail_def,raise_Clash_def,handle_Clash_def]
  \\ fs[exc_case_eq,pair_case_eq,hol_exn_case_eq,bool_case_eq] \\ rw[]
  \\ fs[rev_assocd_thm]
  \\ TRY (
    qmatch_asmsub_abbrev_tac`REV_ASSOCD x l d`
    \\ Q.ISPECL_THEN[`l`,`x`,`d`]strip_assume_tac holSyntaxLibTheory.REV_ASSOCD_MEM
    \\ fs[MEM_MAP,SND_EQ_EQUIV,PULL_EXISTS]
    \\ metis_tac[] )
  \\ TRY (
    first_x_assum(match_mp_tac o MP_CANON) \\ simp[]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac \\ simp[] )
  \\ TRY (
    first_x_assum(qspec_then`sizeof' tm`mp_tac) \\ simp[]
    \\ disch_then(qspec_then`tm`mp_tac) \\ simp[]
    \\ disch_then drule \\ rw[] )
  \\ TRY (
    first_x_assum(qspec_then`sizeof' tm'`mp_tac) \\ simp[]
    \\ disch_then(qspec_then`tm'`mp_tac) \\ simp[]
    \\ disch_then drule \\ rw[] \\ NO_TAC)
  \\ CCONTR_TAC \\ fs[] \\ rw[]
  \\ TRY (
    first_x_assum(qspec_then`sizeof' tm`mp_tac) \\ simp[]
    \\ qexists_tac`tm`\\ simp[]
    \\ asm_exists_tac \\ simp[])
  \\ pop_assum mp_tac \\ rw[]
  \\ fs[pair_case_eq,exc_case_eq] \\ rw[] \\ fs[]
  \\ CCONTR_TAC \\ fs[] \\ rw[]
  \\ TRY (
    first_x_assum(qspec_then`sizeof' tm'`mp_tac) \\ simp[]
    \\ qexists_tac`tm'`\\ simp[]
    \\ asm_exists_tac \\ simp[] \\ fs[])
  \\ pairarg_tac \\ fs[pair_case_eq,exc_case_eq] \\ rw[] \\ fs[]
  \\ pairarg_tac \\ fs[pair_case_eq,exc_case_eq] \\ rw[] \\ fs[]
  \\ imp_res_tac inst_aux_clash_is_var \\ fs[] \\ rw[]
  \\ qhdtm_x_assum`dest_var`mp_tac \\ simp[dest_var_def]
  \\ CASE_TAC \\ rw[raise_Fail_def,st_ex_return_def]
  \\ fs[inst_aux_Var] \\ rw[]
  \\ qhdtm_x_assum`dest_var`mp_tac \\ simp[dest_var_def]
  \\ CASE_TAC \\ rw[raise_Fail_def,st_ex_return_def]
  \\ imp_res_tac variant_same_ty \\ fs[] \\ rw[]
  \\ CCONTR_TAC
  \\ first_x_assum(qspec_then`sizeof' tm'`mp_tac) \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`vsubst_aux ss tm'`
  \\ qexists_tac`vsubst_aux ss tm'` \\ simp[]
  \\ DEP_REWRITE_TAC[sizeof'_vsubst_aux]
  \\ simp[Abbr`ss`]
  \\ asm_exists_tac \\ simp[]
  \\ fs[] \\ rveq
  \\ CCONTR_TAC \\ fs[] \\ rw[]

  recInduct inst_aux_ind \\ rw []
  \\ pop_assum mp_tac
  \\ Cases_on `tm` \\ fs []
  \\ once_rewrite_tac [inst_aux_def] \\ fs []
  \\ simp [st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ simp [handle_Clash_def, raise_Clash_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ rw[]
  \\ strip_tac \\ fs[rev_assocd_thm,holSyntaxLibTheory.REV_ASSOCD_def]
  \\ rw[]
QED

Theorem inst_aux_thm:
   !env tyin tm s f t.
     env = []
     ==>
     inst_aux env tyin tm s <> (Failure (Clash f),t)
Proof
  ...
QED

Theorem inst_not_clash[simp]:
   inst x y z <> (Failure (Clash tm),refs)
Proof
  fs [inst_def, st_ex_return_def, bool_case_eq, case_eq_thms, COND_RATOR]
  \\ fs [inst_aux_thm]
QED

Theorem INST_TYPE_not_clash[simp]:
   INST_TYPE x y z <> (Failure (Clash tm),refs)
Proof
  Cases_on `y` \\ fs [INST_TYPE_def, Once image_def]
  \\ fs [st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs [image_clash_thm]
QED
*)

val _ = export_theory();
