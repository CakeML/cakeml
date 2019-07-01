(*
  Correctness proof for bvi_to_data
*)

open preamble
     bvi_to_dataTheory
     bviSemTheory bviPropsTheory
     dataSemTheory dataPropsTheory
     data_simpProofTheory
     data_liveProofTheory
     data_spaceProofTheory;

val _ = new_theory"bvi_to_dataProof";

val _ = set_grammar_ancestry["bvi_to_data", "bviSem", "bviProps", "dataSem", "dataProps"];
val _ = hide"tail";

(* value relation *)

val code_rel_def = Define `
  code_rel (bvi_code : (num # bvi$exp) num_map)
           (data_code : (num # dataLang$prog) num_map) <=>
    wf bvi_code /\ wf data_code /\
    (domain bvi_code = domain data_code) /\
    !n exp arg_count.
      (lookup n bvi_code = SOME (arg_count,exp)) ==>
      (lookup n data_code = SOME (arg_count,compile_exp arg_count exp))`;

(* Projection from `dataSem$v` into `bvlSem$v` that basically gets rid of
   timestamp information (note this make the function non-injective)
*)
val data_to_bvi_v_def = tDefine"data_to_bvi_v_def"`
  data_to_bvi_v (Number i)      = bvlSem$Number i
∧ data_to_bvi_v (Word64 w)      = bvlSem$Word64 w
∧ data_to_bvi_v (CodePtr p)     = bvlSem$CodePtr p
∧ data_to_bvi_v (RefPtr r)      = bvlSem$RefPtr r
∧ data_to_bvi_v (Block _ tag l) = bvlSem$Block tag (MAP data_to_bvi_v l)
`
(wf_rel_tac `measure v_size`
\\ `∀l. v1_size l = SUM (MAP (λx. v_size x + 1) l)`
   by (Induct >> rw [v_size_def])
\\ rw []
\\ IMP_RES_TAC SUM_MAP_MEM_bound
\\ ho_match_mp_tac LESS_EQ_LESS_TRANS
\\ Q.EXISTS_TAC `SUM (MAP (λx. v_size x + 1) l)`
\\ rw []
\\ ho_match_mp_tac LESS_EQ_TRANS
\\ Q.EXISTS_TAC `v_size a + 1`
\\ rw [])

(* Projection for Unit constant *)
val data_to_bvi_v_Unit = Q.store_thm("data_to_bvi_v_Unit",
  `data_to_bvi_v Unit = Unit`,
  rw [data_to_bvi_v_def,Unit_def,bvlSemTheory.Unit_def]
);

(* Projection for Boolv constant *)
val data_to_bvi_v_Boolv = Q.store_thm("data_to_bvi_v_Boolv",
  `∀b. data_to_bvi_v (Boolv b) = (Boolv b)`,
  rw [data_to_bvi_v_def,Boolv_def,bvlSemTheory.Boolv_def]
);

(* Projection for references, non-injective for value arrays *)
val data_to_bvi_ref_def = Define`
  data_to_bvi_ref (ValueArray l)   = ValueArray (MAP data_to_bvi_v l)
∧ data_to_bvi_ref (ByteArray b bl) = ByteArray b bl
`

(* State relation *)
val state_rel_def = Define `
  state_rel (s:('c,'ffi) bviSem$state) (t:('c,'ffi) dataSem$state) <=>
    (s.clock = t.clock) /\
    code_rel s.code t.code /\
    (t.compile_oracle = ((I ## bvi_to_data$compile_prog) o s.compile_oracle)) /\
    (s.compile = (λcfg prog. t.compile cfg (bvi_to_data$compile_prog prog))) /\
    (s.refs = data_to_bvi_ref o_f t.refs) /\
    (s.ffi = t.ffi) /\
    (s.global = t.global)`;

(* semantics lemmas *)

val find_code_def = bvlSemTheory.find_code_def;
val _ = temp_bring_to_front_overload"find_code"{Name="find_code",Thy="bvlSem"};

val find_code_lemma = Q.prove(
  `state_rel r t2 ∧
    find_code dest (MAP data_to_bvi_v a) r.code = SOME (args,exp)
    ⇒ ∃args'.
       args = MAP data_to_bvi_v args' ∧
       dataSem$find_code dest a t2.code =
         SOME (args',compile_exp (LENGTH args') exp)`,
  reverse (Cases_on `dest`) \\ SIMP_TAC std_ss [find_code_def,dataSemTheory.find_code_def]
  \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,code_rel_def]
  \\ REPEAT STRIP_TAC THEN1
   (Cases_on `lookup x r.code` \\ fs [option_case_eq]
    \\ PairCases_on `x'` \\ fs []
    \\ RES_TAC \\ fs [])
  \\ Cases_on `LAST a` \\  rfs [] \\ fs [data_to_bvi_v_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `lookup n r.code` \\ fs [option_case_eq]
  \\ PairCases_on `x` \\ fs []
  \\ RES_TAC \\ fs []
  \\ `x0 = LENGTH args`
     by (qpat_x_assum `FRONT _ = _` (assume_tac o GSYM) \\ rveq
        \\ Cases_on `a` \\ fs [])
  \\ `?t1 t2. a = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [FRONT_SNOC,LENGTH_SNOC,ADD1,MAP_SNOC]);

Theorem optimise_correct:
   !c s. FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) /\
         FST (evaluate (c,s)) <> NONE ==>
         (evaluate (optimise c,s) = evaluate (c,s))
Proof
  full_simp_tac(srw_ss())[optimise_def] \\ REPEAT STRIP_TAC \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[]
  \\ METIS_TAC [simp_correct,data_liveProofTheory.compile_correct,data_spaceProofTheory.compile_correct,FST]
QED

val compile_RANGE_lemma = Q.prove(
  `!n env tail live xs.
      EVERY (\v. v < (SND (SND (compile n env tail live xs))))
        (FST (SND (compile n env tail live xs)))`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC compile_SING_IMP
  \\ full_simp_tac(srw_ss())[EVERY_MEM]
  \\ rw[]
  \\ RES_TAC
  \\ IMP_RES_TAC compile_LESS_EQ
  \\ TRY (Cases_on `tail`) \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC);

val compile_RANGE = Q.prove(
  `(compile n env tail live xs = (ys,vs,k)) ==> EVERY (\v.  v < k) vs`,
  REPEAT STRIP_TAC \\ MP_TAC (compile_RANGE_lemma |> SPEC_ALL) \\ full_simp_tac(srw_ss())[]);

val _ = temp_overload_on("res_list",``map_result (λv. [v]) I``);
val _ = temp_overload_on("isException",``λx. ∃v. x = Rerr(Rraise v)``);
val _ = temp_overload_on("isResult",``λx. ∃v. x = Rval v``);

val stack_case_eq_thm = prove_case_eq_thm { nchotomy = stack_nchotomy, case_def = stack_case_def };

val RW = REWRITE_RULE;

val compile_part_thm = Q.prove(
  `compile_part = λ(x,y). (x, (λ(a,b). (a, compile_exp a b)) y)`,
  simp[FUN_EQ_THM,FORALL_PROD,compile_part_def])

(* Projection for results, injective upto `dataSem$v` *)
val data_to_bvi_result_def = Define`
  data_to_bvi_result (Rval v) = Rval (data_to_bvi_v v)
∧ data_to_bvi_result (Rerr (Rraise v)) = Rerr (Rraise (data_to_bvi_v v))
∧ data_to_bvi_result (Rerr (Rabort err)) = Rerr (Rabort err)
`

(* All the `dataSem$v` values project to `bvlSem$Boolv b` satisfy `isBool` *)
val isBool_eq = Q.store_thm("isBool_eq",
  `∀z b. isBool b z ⇔ (Boolv b = data_to_bvi_v z)`,
  rw [] \\ EQ_TAC
  \\ Cases_on `z`
  \\ fs [isBool_def,data_to_bvi_v_def,bvlSemTheory.Boolv_def]
  \\ Cases_on `l`
  \\ fs [isBool_def,data_to_bvi_v_def,bvlSemTheory.Boolv_def]
);

(* Lifting `data_to_bvi_v` projection to work over `bvlSem$v list` *)
val v_to_list_eq = Q.store_thm("v_to_list_eq",
  `∀x. v_to_list (data_to_bvi_v x) = OPTION_MAP (MAP data_to_bvi_v) (v_to_list x)`,
  ho_match_mp_tac v_to_list_ind
  \\ rw [bvlSemTheory.v_to_list_def, v_to_list_def, data_to_bvi_v_def]
  \\ cases_on `v_to_list x` \\ rw []
);

(* Special bijection for `data_to_bvi_v` with `dataSem$Number` + `MAP` *)
val data_to_bvi_number_eq = Q.store_thm("data_to_bvi_number_eq",
  `∀ns.
    MAP data_to_bvi_v (MAP (Number ∘ $& ∘ w2n) ns) =
    MAP (Number ∘ $& ∘ w2n) ns`,
  Induct \\ rw[data_to_bvi_v_def]
);

(* Special bijection for `data_to_bvi_v` with `dataSem$Word64` + `MAP` *)
val data_to_bvi_word_eq = Q.store_thm("data_to_bvi_word_eq",
  `∀ns.
    MAP data_to_bvi_v (MAP Word64 ns) =
    MAP Word64 ns`,
  Induct \\ rw[data_to_bvi_v_def]
);

(* Bijection of `data_to_bvi_v (Number n)` over multiple maps *)
val MAP_data_to_bvi_Number = Q.store_thm("MAP_data_to_bvi_Number",
`∀xs ws. MAP data_to_bvi_v (MAP Number xs) = MAP data_to_bvi_v ws ⇔ (MAP Number xs) = ws`,
  Induct  \\ Cases_on `ws` \\ fs []
  \\ rw [data_to_bvi_v_def]
  \\ Cases_on `h`  \\ fs [data_to_bvi_v_def]);

(* Bijection of `data_to_bvi_v (Word64 n)` over multiple maps *)
val MAP_data_to_bvi_Word64 = Q.store_thm("MAP_data_to_bvi_Word64",
`∀xs ws. MAP data_to_bvi_v (MAP Word64 xs) = MAP data_to_bvi_v ws ⇔ (MAP Word64 xs) = ws`,
  Induct  \\ Cases_on `ws` \\ fs []
  \\ rw [data_to_bvi_v_def]
  \\ Cases_on `h`  \\ fs [data_to_bvi_v_def]);

(* `data_to_bvi_v_def` is idempotent over `v_to_bytes` *)
val v_to_bytes_eq = Q.store_thm("v_to_bytes_eq" ,
  `∀x. v_to_bytes (data_to_bvi_v x) = v_to_bytes x`,
  rw [ v_to_list_eq, bvlSemTheory.v_to_bytes_def
     , v_to_bytes_def
     , GSYM data_to_bvi_number_eq
     , MAP_data_to_bvi_Number,MAP_o]
);

(* `data_to_bvi_v_def` is idempotent over `v_to_words` *)
val v_to_words_eq = Q.store_thm("v_to_words_eq" ,
  `∀x. v_to_words (data_to_bvi_v x) = v_to_words x`,
  rw [ v_to_list_eq, bvlSemTheory.v_to_words_def
     , v_to_words_def
     , GSYM data_to_bvi_word_eq
     , MAP_data_to_bvi_Word64,MAP_o]
);

(* isBool simplifications *)
val isBool_simps = Q.store_thm("isBool_simps",
  `(∀b z. isBool T (z:v) ⇒ ¬isBool F z) ∧
   (∀b z. isBool F (z:v) ⇒ ¬isBool T z) `,
  rw []
  \\ Cases_on `z`
  \\ fs [isBool_def,data_to_bvi_v_def,bvlSemTheory.Boolv_def]
  \\ Cases_on `l`
  \\ fs [isBool_def,data_to_bvi_v_def
        , bvlSemTheory.Boolv_def
        , backend_commonTheory.bool_to_tag_def
        , backend_commonTheory.true_tag_def
        , backend_commonTheory.false_tag_def
        ]
);

val [isBool_T_F, isBool_F_T] = zip ["isBool_T_F", "isBool_F_T"]
                                   (CONJUNCTS isBool_simps) |> map save_thm;

(* A variable correspondece (`var_corr`) over projecte values in `t2`
   implies all values in `a` are projections of values in `t2`
 *)
val get_vars_lift_thm = Q.store_thm("get_vars_lift_thm" ,
  `∀vs a t2.
    var_corr a vs (map data_to_bvi_v t2)
    ⇒ ∃z. get_vars vs t2 = SOME z ∧ a = (MAP data_to_bvi_v z)`,
  Induct
  \\ Cases_on `a`
  \\ fs [var_corr_def,get_vars_def,lookup_map,get_var_def]
  \\ rw []
  \\ RES_TAC
  \\ rw [var_corr_def,get_vars_def,lookup_map,get_var_def]
);


val var_corr_inter = Q.store_thm("var_corr_inter",
  `∀t p vs z. var_corr z vs (inter p t) ⇒ var_corr z vs p`,
  fs [var_corr_def]
  \\ ntac 2 strip_tac
  \\ ho_match_mp_tac LIST_REL_ind
  \\ rw []
  \\ fs [get_var_def]
  \\ fs [lookup_inter_alt]
);

val get_vars_mk_wf = Q.store_thm("get_vars_mk_wf",
  `∀vs t z. get_vars vs (mk_wf t) = SOME z ⇒ get_vars vs t = SOME z`,
  Induct
  \\ rw [get_vars_def,get_var_def]
  \\ Cases_on `lookup h t` \\ fs []
  \\ Cases_on `get_vars vs (mk_wf t)` \\ fs []
  \\ RES_TAC
  \\ qpat_x_assum `_::_ = _` (ASSUME_TAC o GSYM)
  \\ fs []
);

val get_vars_inter = Q.store_thm("get_vars_inter",
  `∀vs p t z. get_vars vs  (inter p t) = SOME z ⇒ get_vars vs  p = SOME z`,
  Induct
  \\ rw [get_vars_def]
  \\ fs [get_var_def,lookup_inter_alt]
  \\ Cases_on `h ∈ domain t` \\ fs []
  \\ Cases_on `lookup h p`   \\ fs []
  \\ Cases_on `get_vars vs (inter p t)` \\ fs []
  \\ RES_TAC
  \\ qpat_x_assum `_::_ = _` (ASSUME_TAC o GSYM)
  \\ fs []
);

(* `data_to_bvi_v` preserves `var_corr` *)
val var_corr_map = Q.store_thm("var_corr_map",
  `∀p f vs z. var_corr z vs p ⇒ var_corr (MAP f z) vs (map f p)`,
  fs [var_corr_def,LIST_REL_MAP2,get_var_def]
  \\ ntac 2 strip_tac
  \\ ho_match_mp_tac LIST_REL_ind
  \\ fs [lookup_map]
);

(* Construction of the pre-image of `data_to_bvi_v`,
   wich in all cases except `Block` is bijective
 *)
val data_to_bvi_v_eq = Q.store_thm("data_to_bvi_v_eq",
  `(∀v n i. data_to_bvi_v v = Number i  ⇒ v = Number i)  ∧
   (∀v n w. data_to_bvi_v v = Word64 w  ⇒ v = Word64 w)  ∧
   (∀v n p. data_to_bvi_v v = CodePtr p ⇒ v = CodePtr p) ∧
   (∀v n r. data_to_bvi_v v = RefPtr r  ⇒ v = RefPtr r)  ∧
   (∀v n l. data_to_bvi_v v = Block n l
     ⇒ ∃ts l'. v = Block ts n l' ∧ l = MAP data_to_bvi_v l')`,
  rw [] \\ Cases_on `v` \\ fs [data_to_bvi_v_def] \\ METIS_TAC []);

val [ data_to_bvi_eq_Number,  data_to_bvi_eq_Word64
    , data_to_bvi_eq_CodePtr, data_to_bvi_eq_RefPtr
    , data_to_bvi_eq_Block] =
      zip [ "data_to_bvi_eq_Number",  "data_to_bvi_eq_Word64"
          , "data_to_bvi_eq_CodePtr", "data_to_bvi_eq_RefPtr"
          , "data_to_bvi_eq_Block"]
          (CONJUNCTS data_to_bvi_v_eq)  |> map save_thm;

val data_to_bvi_ref_eq = Q.store_thm("data_to_bvi_ref_eq",
  `(∀v fl ds. data_to_bvi_ref v = ByteArray fl ds ⇒ v = ByteArray fl ds) ∧
   (∀v l.     data_to_bvi_ref v = ValueArray l
     ⇒ ∃l'. v = ValueArray l' ∧ l = MAP data_to_bvi_v l')`,
  rw [] \\ Cases_on `v` \\ fs [data_to_bvi_ref_def] \\ METIS_TAC []
);

val [data_to_bvi_eq_ByteArray, data_to_bvi_eq_ValueArray] =
  zip ["data_to_bvi_eq_ByteArray", "data_to_bvi_eq_ValueArray"]
      (CONJUNCTS data_to_bvi_ref_eq)  |> map save_thm;

(* Construction of the pre-image of `data_to_bvi_result` *)
val data_to_bvi_result_eq = Q.store_thm("data_to_bvi_result_eq",
  `∀x v. data_to_bvi_result x = Rerr (Rraise v)
    ⇒ ∃z. x = Rerr (Rraise z) ∧ v = data_to_bvi_v z`,
   Cases_on `x` \\ fs [data_to_bvi_result_def]
   \\ Cases_on `e` \\ fs [data_to_bvi_result_def]
);

val list_to_v_MAP = Q.store_thm("list_to_v_MAP",
  `∀z. list_to_v (MAP data_to_bvi_v z) = data_to_bvi_v (list_to_v z)`,
  Induct \\ rw [list_to_v_def,bvlSemTheory.list_to_v_def,data_to_bvi_v_def]
);

(* `data_to_bvi_v` preservers `do_eq` *)
val data_to_bvi_do_eq = Q.store_thm("data_to_bvi_do_eq",
  `(∀t v1 v2. do_eq (data_to_bvi_ref o_f t) (data_to_bvi_v v1) (data_to_bvi_v v2)
              = do_eq t v1 v2) ∧
   (∀t l1 l2. do_eq_list (data_to_bvi_ref o_f t) (MAP data_to_bvi_v l1) (MAP data_to_bvi_v l2)
              = do_eq_list t l1 l2)`,
  ho_match_mp_tac do_eq_ind
  \\ rw [do_eq_def,bvlSemTheory.do_eq_def,data_to_bvi_v_def]
  \\ fs [ backend_commonTheory.closure_tag_def
        , backend_commonTheory.partial_app_tag_def
        , isClos_def,bvlSemTheory.isClos_def,isClos_def
        , FLOOKUP_o_f]
  >- (every_case_tac \\ fs [data_to_bvi_ref_def])
  >- METIS_TAC []
  >- (Cases_on `l1` \\ rw [do_eq_def,bvlSemTheory.do_eq_def])
  >- (Cases_on `l2` \\ rw [do_eq_def,bvlSemTheory.do_eq_def])
  >- (every_case_tac \\ fs [data_to_bvi_ref_def])
);

val data_to_bvi_do_app = Q.store_thm("data_to_bvi_do_app",
  `∀op t r z res s1.
    op ≠ Install ∧ op ≠ Greater ∧ op ≠ GreaterEq ∧ (∀b. op ≠ CopyByte b) ∧
    state_rel r t ∧
    do_app op (MAP data_to_bvi_v z) r = Rval (res,s1)
    ⇒ ∃s2 pres.
       do_app_aux op z t = Rval (pres,s2) ∧
       res = data_to_bvi_v pres ∧
       state_rel s1 s2`,
  Cases_on `op`
  \\ ntac 2 (fs [ do_app_aux_def
                , bvlSemTheory.do_app_def
                , bviSemTheory.do_app_def
                , bviSemTheory.do_app_aux_def
                , list_case_eq
                , option_case_eq
                , bool_case_eq
                , v_case_eq
                , bvlSemTheory.v_case_eq
                , ffiTheory.call_FFI_def
                , with_fresh_ts_def
                , closSemTheory.ref_case_eq
                , do_install_def
                , ffiTheory.ffi_result_case_eq
                , ffiTheory.oracle_result_case_eq
                , semanticPrimitivesTheory.eq_result_case_eq
                , astTheory.word_size_case_eq
                , pair_case_eq
                , dataLangTheory.op_space_reset_def
                , consume_space_def])
  \\ rw [case_eq_thms, bvlSemTheory.case_eq_thms, pair_case_eq]
  \\ every_case_tac \\ fs []
  \\ REPEAT (CHANGED_TAC (rfs [MAP_EQ_CONS]))
  \\ rveq
  \\ rpt (qpat_x_assum `_ = data_to_bvi_v _` (ASSUME_TAC o GSYM))
  \\ imp_res_tac data_to_bvi_v_eq
  \\ rw[data_to_bvi_v_def]
  \\ fs[bvi_to_bvl_def,bvl_to_bvi_def
       , bviSemTheory.state_component_equality
       , data_to_bvi_ref_def
       , state_rel_def
       , o_f_FUPDATE
       , map_replicate
       , data_to_bvi_eq_ByteArray
       , v_to_list_eq
       , v_to_list_def
       , data_to_bvi_v_Boolv
       , data_to_bvi_v_Unit]
  \\ rfs [FLOOKUP_o_f,option_case_eq]
  \\ imp_res_tac data_to_bvi_ref_eq
  \\ imp_res_tac data_to_bvi_v_eq
  \\ fs [data_to_bvi_v_def
        ,data_to_bvi_ref_def
        ,LENGTH_MAP,EL_MAP
        ,o_f_FUPDATE
        ,LUPDATE_MAP
        ,data_to_bvi_v_Unit
        ,data_to_bvi_v_Boolv]
  >- METIS_TAC [data_to_bvi_v_def]
  >- (Cases_on `z`
     \\ Cases_on `t.tstamps`
     \\ rw [data_to_bvi_v_def,MAP_TAKE,MAP_DROP]
     \\ METIS_TAC [])
  >- (Cases_on `t.tstamps`
     \\ rw [data_to_bvi_v_def,MAP_TAKE,MAP_DROP]
     \\ METIS_TAC [])
  >- (ONCE_REWRITE_TAC [GSYM MAP_APPEND] \\ rw [list_to_v_MAP])
  >- (Cases_on `t.tstamps`
     \\ Cases_on `z`
     \\ rw [data_to_bvi_v_def,MAP_TAKE,MAP_DROP]
     \\ METIS_TAC [])
  >- (`Num i < LENGTH l'`
      by ((drule o GEN_ALL o GSYM) integerTheory.NUM_LT \\ strip_tac \\ fs [])
      \\ rw [EL_MAP])
  >- rfs [code_rel_def]
  >- (rfs [data_to_bvi_do_eq,data_to_bvi_v_Boolv])
);

val compile_correct = Q.prove(
  `∀xs env s1 res s2 t1 n corr tail live.
     evaluate (xs,env,s1) = (res,s2) ∧
     res ≠ Rerr(Rabort Rtype_error) ∧
     var_corr env corr (map data_to_bvi_v t1.locals) ∧
     (LENGTH xs ≠ 1 ⇒ ¬tail) ∧
     (∀k. n ≤ k ⇒ (lookup k t1.locals = NONE)) ∧
     state_rel s1 t1 ∧
     EVERY (\n. lookup n t1.locals ≠ NONE) live ∧
     (isException res ⇒ jump_exc t1 ≠ NONE)
     ⇒ ∃t2 prog pres vs next_var.
         compile n corr tail live xs = (prog,vs,next_var) ∧
         evaluate (prog,t1) = (pres,t2) ∧
         state_rel s2 t2 ∧
         (case pres of
          | SOME r =>
             ((res_list (data_to_bvi_result r) = res) ∧
              (isResult res ⇒
                 tail ∧
                 (t1.stack = t2.stack) ∧
                 (t1.handler = t2.handler)) ∧
              (isException res ⇒
                 (jump_exc (t2 with <| stack := t1.stack;
                                       handler := t1.handler |>) = SOME t2)))
          | NONE => ~tail ∧  n <= next_var ∧
                    EVERY (\v. v < next_var) vs ∧
                    (∀k. next_var <= k ⇒ (lookup k t2.locals = NONE)) ∧
                    var_corr env corr (map data_to_bvi_v t2.locals) ∧
                    (∀k x. (lookup k t2.locals = SOME x) ⇒ k < next_var) ∧
                    (∀k x. (lookup k t1.locals = SOME x) ∧
                           (¬MEM k live ⇒ MEM k corr) ⇒
                           (lookup k t2.locals = SOME x)) ∧
                    (t1.stack = t2.stack) ∧  (t1.handler = t2.handler) ∧
                    (jump_exc t1 ≠ NONE ⇒ jump_exc t2 ≠ NONE) ∧
                    case res of
                    | Rval xs => var_corr xs vs (map data_to_bvi_v t2.locals)
                    | _ => F)`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct bviSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,dataSemTheory.evaluate_def,bviSemTheory.evaluate_def]
  THEN1 (* NIL *)
    (SRW_TAC [] [var_corr_def,data_to_bvi_v_def]
     \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [NOT_LESS]
     \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1 (* CONS *)
   (`?c1 v1 n1. compile n corr F live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 vs n2. compile n1 corr F (HD v1::live) (y::xs) = (c2,vs,n2)` by
          METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `evaluate (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`HD v1::live`])
    \\ simp[]
    \\ `EVERY (\n. lookup n t2.locals <> NONE) (HD v1::live)` by
     (IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC compile_SING_IMP
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [get_var_def,lookup_map]
    \\ metis_tac [])
  THEN1 (* Var *)
   (Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ fs[any_el_ALT]
    \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,LIST_REL_def]
    \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
    \\ FULL_SIMP_TAC (srw_ss()) [get_var_def,set_var_def,lookup_insert,lookup_map]
    \\ rfs []
    \\ RES_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,call_env_def,data_to_bvi_result_def]
    \\ REPEAT STRIP_TAC
    \\ DISJ1_TAC \\ CCONTR_TAC
    \\ `n' ≤ k'` by fs[]>>
    RES_TAC>>fs[])
  THEN1 (* If *)
   (`?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. compile n1 corr tail live [x2] = (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 v3 n3. compile n2 corr tail live [x3] = (c3,v3,n3)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [evaluate_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] (map data_to_bvi_v t2.locals)`
    \\ `∃z. get_var n5 t2.locals = SOME z ∧ w = data_to_bvi_v z`
       by FULL_SIMP_TAC (srw_ss()) [var_corr_def,lookup_map,get_var_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC compile_LESS_EQ
    THEN1
      (`EVERY (\n. lookup n t2.locals <> NONE) live` by
        (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
         \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
      \\ Cases_on `isBool T z ∨ isBool F z`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC (srw_ss()) [GSYM isBool_eq, isBool_simps]
      THEN1
       (Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss [])
      THEN1
       (Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
        THEN1 (REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC std_ss []))
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ Cases_on `isBool T z ∨ isBool F z`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM isBool_eq, isBool_simps]
    THEN1
     (Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`live`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ _ (_ t7))`
      \\ `∃z7. get_var n7 t7.locals = SOME z7 ∧ w7 = data_to_bvi_v z7`
         by FULL_SIMP_TAC (srw_ss()) [var_corr_def,lookup_map,get_var_def]
      \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
           var_corr_def,get_var_def,lookup_insert,lookup_map]
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\  DECIDE_TAC)
      THEN1
       (`∀k. n2 ≤ k ⇒ lookup k (map data_to_bvi_v t7.locals) = NONE`
        by rw [lookup_map]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ sg `EL l corr <> n3` \\ FULL_SIMP_TAC std_ss []
        \\ `n2 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n3 (map data_to_bvi_v t7.locals) = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [jump_exc_NONE,lookup_map])
    \\ Q.PAT_X_ASSUM `(res,s3) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`F`,`live`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ _ (_ t7))`
    \\ `∃z7. get_var n7 t7.locals = SOME z7 ∧ w7 = data_to_bvi_v z7`
       by FULL_SIMP_TAC (srw_ss()) [var_corr_def,lookup_map,get_var_def]
    \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
         var_corr_def,get_var_def,lookup_insert,lookup_map]
    \\ REPEAT STRIP_TAC
    THEN1 DECIDE_TAC
    THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
           \\ FIRST_X_ASSUM MATCH_MP_TAC \\  DECIDE_TAC)
    THEN1
     (FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
      \\ sg `EL l corr <> n3` \\ FULL_SIMP_TAC std_ss []
      \\ `n3 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
      \\ `lookup n3 t7.locals = NONE` by METIS_TAC []
      \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
    THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
           \\ RES_TAC \\ DECIDE_TAC)
    THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
           \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
           \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [jump_exc_NONE])
  THEN1 (* Let *)
   (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. compile n1 (vs ++ corr) tail live [x2] =
                   (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (a ++ env) (vs ++ corr) (map data_to_bvi_v t2.locals)` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC (GEN_ALL EVERY2_APPEND_suff)
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE_EQ])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,
         `vs ++ corr`,`tail`,`live`])
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ IMP_RES_TAC LIST_REL_APPEND_IMP
    \\ IMP_RES_TAC LIST_REL_LENGTH
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* Raise *)
   (`?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def,call_env_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ `∃z. get_var t t2.locals = SOME z ∧ w = data_to_bvi_v z`
       by full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
    \\ FULL_SIMP_TAC std_ss [state_rel_def]
    \\ IMP_RES_TAC jump_exc_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[jump_exc_def,data_to_bvi_result_def])
  THEN1 (* Op *)
   (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 SRW_TAC [] [evaluate_def]
    \\ `domain (list_to_num_set (REVERSE vs ++ live ++ corr)) SUBSET
        domain (map data_to_bvi_v t2.locals)` by
     (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,
           lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
      \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[]
      \\ `lookup x t1.locals <> NONE` by METIS_TAC []
      \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t2.locals (list_to_num_set (REVERSE vs++live++corr)))`
    \\ `var_corr (REVERSE a) (REVERSE vs) (map data_to_bvi_v env1)` by
     (UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,state_rel_def,
             lookup_inter_EQ,lookup_list_to_num_set,lookup_map]
      \\ Q.PAT_X_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
      \\ ONCE_REWRITE_TAC [LIST_REL_MEM]
      \\ full_simp_tac(srw_ss())[EVERY2_REVERSE] \\ NO_TAC)
    \\ IMP_RES_TAC get_vars_thm
    \\ IMP_RES_TAC get_vars_lift_thm
    \\ `state_rel r (t2 with <|locals := env1; space := 0|>)` by
          (full_simp_tac(srw_ss())[state_rel_def] \\ NO_TAC)
    \\ `z = REVERSE z'` by
       (rveq \\ UNABBREV_ALL_TAC
       \\ fs [get_vars_mk_wf]
       \\ IMP_RES_TAC get_vars_inter
       \\ IMP_RES_TAC get_vars_reverse
       \\ rveq \\ fs [])
    \\ reverse(Cases_on `do_app op (REVERSE a) r`) \\ full_simp_tac(srw_ss())[] >- (
         imp_res_tac bviPropsTheory.do_app_err >> full_simp_tac(srw_ss())[] >>
         rveq >> IF_CASES_TAC >>
         fs[dataSemTheory.evaluate_def,iAssign_def,dataLangTheory.op_requires_names_def,
            cut_state_opt_def,cut_state_def,cut_env_def] >>
         fs[bviSemTheory.do_app_def,do_app_aux_def,bvlSemTheory.do_app_def,domain_map,bviSemTheory.do_app_aux_def,
            do_space_def,dataSemTheory.do_app_def,dataLangTheory.op_space_reset_def,data_spaceTheory.op_space_req_def] >>
         rpt(PURE_CASE_TAC >> fs[data_to_bvi_v_def,GSYM MAP_REVERSE] >> rveq) >>
         fs[state_rel_def] >>
         rfs[] >> fs [data_to_bvi_result_def] >>
         fs[call_env_def,FLOOKUP_o_f,data_to_bvi_ref_def])
    \\ PairCases_on `a'` \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,iAssign_def]
    \\ (fn (hs,goal) => (reverse (sg `let tail = F in ^goal`))
           (hs,goal)) THEN1
     (full_simp_tac(srw_ss())[LET_DEF]
      \\ reverse (Cases_on `tail`) THEN1 METIS_TAC []
      \\ full_simp_tac(srw_ss())[evaluate_def,LET_DEF] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[]
      \\ `∃z2. get_var n1 t2'.locals = SOME  z2 ∧ a'0 = data_to_bvi_v z2`
         by FULL_SIMP_TAC (srw_ss()) [var_corr_def,lookup_map,get_var_def]
      \\ full_simp_tac(srw_ss())[var_corr_def,call_env_def,state_rel_def,data_to_bvi_result_def])
    \\ simp[]
    \\ Cases_on`op = Install`
    >- (
      fs[dataLangTheory.op_requires_names_def,domain_map]
      \\ simp[evaluate_def,cut_state_opt_def,cut_state_def,cut_env_def]
      \\ fs[bviSemTheory.do_app_def,dataSemTheory.do_app_def]
      \\ fs[bviSemTheory.do_install_def,dataSemTheory.do_install_def]
      \\ fs[case_eq_thms,GSYM MAP_REVERSE,bvlSemTheory.case_eq_thms]
      \\ ntac 4 (rfs [MAP_EQ_CONS])
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ rveq
      \\ fs[bvlPropsTheory.case_eq_thms,case_eq_thms]
      \\ rpt(pairarg_tac \\ fs[])
      \\ fs[Once SWAP_REVERSE_SYM]
      \\ rveq \\ fs[]
      \\ fs[bvlPropsTheory.case_eq_thms,case_eq_thms] \\ rveq
      \\ Cases_on`progs` \\ fs[]
      >- (
        rfs[state_rel_def] \\ fs[]
        \\ fs[compile_prog_def] )
      \\ `r.compile = λcfg prog. t2.compile cfg (compile_prog prog)` by fs[state_rel_def]
      \\ `t2.compile_oracle = (I ## compile_prog) o r.compile_oracle` by fs[state_rel_def]
      \\ fs[] \\ rveq \\ fs[shift_seq_def]
      \\ Cases_on`h` \\ fs[set_var_def,lookup_insert,var_corr_def,state_rel_def,o_DEF,get_var_def,lookup_insert,lookup_map]
      \\ qmatch_goalsub_abbrev_tac`fromAList progs1`
      \\ qmatch_goalsub_abbrev_tac`union t2.code (fromAList progs2)`
      \\ conj_tac
      >- (
        ntac 2 (pop_assum kall_tac) \\ rveq \\
        fs[code_rel_def,wf_union,wf_fromAList,domain_union,compile_prog_def,domain_fromAList,
           compile_part_thm,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX] \\
        fs[lookup_union,lookup_fromAList, ALOOKUP_MAP]
        \\ rpt gen_tac
        \\ TOP_CASE_TAC \\ fs[]
        >- (
          TOP_CASE_TAC \\ fs[]
          \\ fs[EXTENSION,domain_lookup]
          \\ metis_tac[NOT_SOME_NONE] )
        \\ rw[] \\ res_tac \\ fs[] )
      \\ rveq \\ fs[] \\ rveq
      \\ conj_tac
      >- ( simp[Abbr`env1`] \\ fs[lookup_inter_alt] )
      \\ conj_tac >- (
        fs[LIST_REL_EL_EQN]
        \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        >- ( res_tac \\ fs[] )
        \\ METIS_TAC[MEM_EL] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ res_tac \\ fs[] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[] )
      \\ reverse conj_tac >- (
        fs[compile_prog_def,compile_part_thm,Abbr`progs1`,data_to_bvi_v_def]
        \\ fs[markerTheory.Abbrev_def] )
      \\ rw[] \\ res_tac
      \\ fs[jump_exc_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[])
    \\ Cases_on `op = Greater \/ op = GreaterEq` THEN1
     (fs []
      \\ (fs [dataLangTheory.op_requires_names_def
             ,dataLangTheory.op_space_reset_def]
      \\ fs [evaluate_def,cut_state_opt_def]
      \\ fs [cut_state_def,cut_env_def,domain_map
            ,dataLangTheory.op_requires_names_def]
      \\ imp_res_tac get_vars_reverse \\ fs []
      \\ Cases_on `MAP data_to_bvi_v (REVERSE z')`
      THEN1 fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
                bvlSemTheory.do_app_def]
      \\ Cases_on `t`
      THEN1 fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
                bvlSemTheory.do_app_def]
      \\ reverse (Cases_on `t'`)
      THEN1 (fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
                 bvlSemTheory.do_app_def] \\ Cases_on `h'` \\ fs []
                 \\ Cases_on`h` \\ fs[data_to_bvi_v_def])
      \\ fs [SWAP_REVERSE_SYM,MAP_REVERSE] \\ rveq \\ fs []
      \\ Cases_on `h`
      \\ fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             bvlSemTheory.do_app_def]
      \\ Cases_on `h'`
      \\ fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             bvlSemTheory.do_app_def]
      \\ fs [MAP_EQ_CONS]
      \\ qpat_x_assum `Number _ = _` (ASSUME_TAC o GSYM)
      \\ qpat_x_assum `Number _ = _` (ASSUME_TAC o GSYM)
      \\ IMP_RES_TAC data_to_bvi_eq_Number \\ rveq
      \\ fs [EVAL ``dataSem$do_app Less [Number i'; Number i] t``]
      \\ fs [EVAL ``dataSem$do_app LessEq [Number i'; Number i] t``]
      \\ fs [set_var_def,lookup_insert,integerTheory.int_gt,integerTheory.int_ge]
      \\ fs [state_rel_def]
      \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).refs``]
      \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).ffi``]
      \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).global``]
      \\ fs [var_corr_def,get_var_def,lookup_insert,bvlSemTheory.Boolv_def,
             backend_commonTheory.bool_to_tag_def,
             backend_commonTheory.true_tag_def,
             backend_commonTheory.false_tag_def]
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ unabbrev_all_tac
      \\ fs [ lookup_inter_alt,map_insert,lookup_map
            , lookup_insert,data_to_bvi_v_def]
      \\  conj_tac
      >- ( fs[bvl_to_bvi_def] )
      \\ rpt strip_tac
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
                get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ IF_CASES_TAC \\ fs []
        \\ res_tac THEN1 (qpat_assum `EL l corr = n1` assume_tac \\ fs [])
        \\ fs [domain_lookup,lookup_list_to_num_set]
        \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
               lookup_list_to_num_set] \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
         \\ fs [lookup_list_to_num_set,domain_lookup])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])))
    \\ Cases_on`∃b. op = CopyByte b` >- (
      fs[dataLangTheory.op_requires_names_def]
      \\ qhdtm_x_assum`bviSem$do_app`mp_tac
      \\ simp[bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,closSemTheory.case_eq_thms]
      \\ strip_tac \\ rveq \\ fs[pair_case_eq,domain_map] \\ rw[]
      \\ simp[evaluate_def,cut_state_opt_def,cut_state_def,cut_env_def]
      \\ fs[dataSemTheory.do_app_def,do_space_def,dataLangTheory.op_space_reset_def,
            data_spaceTheory.op_space_req_def,do_app_aux_def]
      \\ fs[state_rel_def,code_rel_def]
      \\ fs [ bvlSemTheory.do_app_def
         , bvlSemTheory.case_eq_thms
         , case_eq_thms
         , pair_case_eq,SWAP_REVERSE_SYM,FLOOKUP_o_f]
      \\ ntac 5 (rfs [MAP_EQ_CONS])
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ qpat_x_assum `Number _ = _` (ASSUME_TAC o GSYM)
      \\ IMP_RES_TAC data_to_bvi_v_eq \\ rveq
      \\ fs [FLOOKUP_o_f,case_eq_thms]
      \\ IMP_RES_TAC data_to_bvi_eq_ByteArray \\ rveq
      \\ fs [ set_var_def,bvl_to_bvi_id,lookup_insert
            , lookup_map,map_insert]
      \\ fs[bvi_to_bvl_def,bvl_to_bvi_def
           ,bviSemTheory.state_component_equality
           , data_to_bvi_ref_def]
      \\ conj_tac >- ( rw[Abbr`env1`,lookup_inter_EQ] )
      \\ fs [ var_corr_def,data_to_bvi_v_Unit,get_var_def,lookup_insert
            , lookup_map,bvlPropsTheory.case_eq_thms
            , LENGTH_MAP,LIST_REL_LENGTH,lookup_map]
      \\ fs[] \\ rveq
      \\ fs[] \\ rveq
      \\ conj_tac >- (
        fs[LIST_REL_EL_EQN]
        \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[MEM_EL,prim_recTheory.LESS_REFL] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ res_tac \\ fs[] )
      \\ conj_tac >- (
        fs[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[prim_recTheory.LESS_REFL] )
      \\ rw[] \\ res_tac
      \\ fs[jump_exc_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[])
    \\ fs []
    \\ fs[bviSemTheory.state_component_equality] \\ rveq
    \\ Cases_on `op_requires_names op`
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
           cut_state_def,cut_env_def,domain_map]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def,LET_THM]
    \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def]
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ IMP_RES_TAC do_app_code \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC do_app_oracle \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\ full_simp_tac(srw_ss())[lookup_insert]
    THEN1
     (`op_space_reset op` by
      rfs [dataLangTheory.op_space_reset_def
          ,dataLangTheory.op_requires_names_def]
      \\ `state_rel r (t2 with <|locals := env1; space := 0|>)`
         by fs[state_rel_def]
      \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
      \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
      \\ rw []
     \\  rfs [dataLangTheory.op_space_reset_def
            ,code_rel_def
            ,state_rel_def]
     \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert]
     \\ REPEAT STRIP_TAC
      THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
                get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH z''`
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ `EL l corr <> n1`
           by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
        \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
        \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
        \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ rfs[lookup_insert,lookup_inter_EQ,
               lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map])
    \\ rveq
    \\ imp_res_tac get_vars_reverse
    \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac (srw_ss()) []
    \\ Cases_on `op_space_req op (LENGTH vs) = 0`
    \\ full_simp_tac(srw_ss())[evaluate_def,dataLangTheory.op_requires_names_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
          cut_state_def,cut_env_def]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ IMP_RES_TAC do_app_code
    \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\ full_simp_tac(srw_ss())[lookup_insert]
    THEN1
     (`state_rel r t2` by fs[state_rel_def]
     \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
     \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
     \\ rw []
     \\ rfs [dataLangTheory.op_space_reset_def
            ,code_rel_def
            ,state_rel_def]
     \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert]
     \\ REPEAT STRIP_TAC
     THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,
               var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ rename1 `l1 < LENGTH corr`
        \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ `EL l1 corr <> n1`
           by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
        \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
        \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
        \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,
               lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map])
    \\ full_simp_tac(srw_ss())[consume_space_add_space,lookup_insert]
    THEN1
     (`state_rel r (t2 with <|locals := env1; space := 0|>)` by fs[state_rel_def]
     \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
     \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
     \\ rw []
     \\ rfs [dataLangTheory.op_space_reset_def
            ,code_rel_def
            ,state_rel_def]
     \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert]
     \\ REPEAT STRIP_TAC
      THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,
               var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ rename1 `l1 < LENGTH corr`
        \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ `EL l1 corr <> n1`
           by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
        \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
        \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
        \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]))
  THEN1 (* Tick *)
   (`?c1 v1 n1. compile n corr tail live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (full_simp_tac(srw_ss())[state_rel_def,call_env_def,data_to_bvi_result_def])
    \\ `s.clock <> 0` by (FULL_SIMP_TAC std_ss [state_rel_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`,`corr`,`tail`,`live`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def,dataSemTheory.dec_clock_def,
         get_var_def,state_rel_def,bviSemTheory.dec_clock_def,jump_exc_NONE])
  THEN1 (* Call *)
   (Cases_on `handler` THEN1 (* Call without handler *)
     (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def,call_env_def,compile_def,
           evaluate_mk_ticks]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ first_assum (mp_then Any assume_tac get_vars_thm)
      \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
      \\ fs [] \\ rveq
      \\ first_assum (mp_then Any assume_tac find_code_lemma)
      \\ first_x_assum (first_assum o (mp_then Any assume_tac))
      \\ fs [] \\ rveq
      (* \\ `get_vars vs t2.locals = SOME a` by IMP_RES_TAC get_vars_thm *)
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
         (`lookup x t1.locals <> NONE` by METIS_TAC []
            \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
        \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
       (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock,data_to_bvi_result_def]
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ full_simp_tac(srw_ss())[cut_env_def,data_to_bvi_result_def])
      \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
      \\ `(FUNPOW dec_clock ticks t2).clock ≠ 0` by simp [funpow_dec_clock_clock]
      \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `tail` THEN1
       (`evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r) = (res,s2)` by
        (Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks+1) r)` \\ full_simp_tac(srw_ss())[]
           \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\
           Cases_on`e` >> full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM (qspecl_then
             [`call_env args' (FUNPOW dec_clock (ticks+1) t2)`,
               `LENGTH args'`,
               `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList_MAP,lookup_fromList_outside,jump_exc_NONE,call_env_def,
          funpow_dec_clock_clock,lookup_map])
        \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
        \\ MP_TAC (Q.SPECL [`prog`,
            `call_env args' (FUNPOW dec_clock (ticks+1) t2)`] optimise_correct)
        \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss [call_env_def]
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[funpow_dec_clock_clock]
          \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[data_to_bvi_result_def])
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[COUNT_LIST_GENLIST]
        \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code]
        \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
        \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[] \\ FULL_SIMP_TAC std_ss []
        \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,
           bviSemTheory.dec_clock_def,dataSemTheory.dec_clock_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [FUNPOW_dec_clock_code])
      \\ full_simp_tac(srw_ss())[cut_env_def]
      \\ `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r) = (res,s2)` by
       (Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r)` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args' (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`,
           `LENGTH args'`,
           `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList_MAP,lookup_fromList_outside,push_env_def,
          call_env_def,FUNPOW_dec_clock_code,lookup_map]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by full_simp_tac(srw_ss())[]
          \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def,FUNPOW_dec_clock_code]
          \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
          \\ DECIDE_TAC)
      \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args'
         (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`]
            optimise_correct) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[data_to_bvi_result_def])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
      \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[call_env_def]
      \\ `~(r.clock ≤ ticks)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `x`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[data_to_bvi_result_def]
      THEN1
       (Cases_on`e`>>full_simp_tac(srw_ss())[data_to_bvi_result_def]>>
        IMP_RES_TAC jump_exc_IMP
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def]
        \\ SIMP_TAC (srw_ss()) [jump_exc_def]
        \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code]
        \\ Cases_on `t2.handler = LENGTH t2.stack` THEN1
         (FULL_SIMP_TAC std_ss [Q.SPEC `x::xs` LASTN_LENGTH_ID
             |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ full_simp_tac(srw_ss())[])
        \\ `t2.handler < LENGTH t2.stack` by DECIDE_TAC
        \\ FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC LASTN_TL
        \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2 |>)` by
       (Q.PAT_X_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
             pop_env_def,dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def,
             FUNPOW_dec_clock_code])
      \\ full_simp_tac(srw_ss())[set_var_def,state_rel_def]
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ REPEAT STRIP_TAC
      THEN1
       (UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter]
        \\ SRW_TAC [] [] THEN1 DECIDE_TAC
        \\ sg `lookup k t2.locals = NONE` \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,lookup_map]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ sg `EL l corr <> n1` \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t1.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter]
        \\ POP_ASSUM MP_TAC \\ full_simp_tac(srw_ss())[]
        \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL]
        \\ full_simp_tac(srw_ss())[lookup_list_to_num_set])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ Cases_on `k = n1` \\ FULL_SIMP_TAC std_ss []
        \\ CCONTR_TAC \\ `n1 <= k` by DECIDE_TAC
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter])
      THEN1
       (`lookup k t2.locals = SOME x` by
          (FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[])
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter,lookup_insert]
        \\ `lookup k (list_to_num_set (live ++ corr)) = SOME ()` by
           (full_simp_tac(srw_ss())[lookup_list_to_num_set] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
        \\ sg `k <> n1` \\ full_simp_tac(srw_ss())[] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ REPEAT (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,lookup_map,
                call_env_def,push_env_def,dataSemTheory.dec_clock_def,
                bviSemTheory.dec_clock_def]
                 \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
                 \\ BasicProvers.EVERY_CASE_TAC))
    \\ (* Call with handle *)
      `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ `?c2 v n2. compile (n1+1) (n1::corr) F live [x] = (c2,v,n2)` by
            METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,evaluate_mk_ticks,call_env_def,compile_def]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ Cases_on `dest = NONE` \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
         (Cases_on `lookup x' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
        \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[lookup_map] \\ NO_TAC)
      \\ first_assum (mp_then Any assume_tac get_vars_thm)
      \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
      \\ fs [] \\ rveq
      \\ first_assum (mp_then Any assume_tac find_code_lemma)
      \\ first_x_assum (first_assum o (mp_then Any assume_tac))
      \\ fs [] \\ rveq
      (* \\ IMP_RES_TAC find_code_lemma *)
      (* \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC) *)
      (* \\ `get_vars vs t2.locals = SOME a` by IMP_RES_TAC get_vars_thm *)
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
       (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock,data_to_bvi_result_def]
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ full_simp_tac(srw_ss())[cut_env_def,data_to_bvi_result_def])
      \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ `~(r.clock < ticks) /\ ~(r.clock ≤ ticks)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[cut_env_def]
      \\ Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r)`
      \\ Q.MATCH_ASSUM_RENAME_TAC
            `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r) = (res4,r4)`
      \\ Cases_on `isException res4` THEN1
       (Cases_on `res4` \\ full_simp_tac(srw_ss())[LET_DEF] \\ full_simp_tac(srw_ss())[]
        \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
        \\ FIRST_X_ASSUM (qspecl_then
            [`call_env args' (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
             `LENGTH args'`,
             `GENLIST I (LENGTH args')`,`T`,`[]`] mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
            bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,lookup_map,
            LIST_REL_lookup_fromList_MAP,lookup_fromList_outside,push_env_def,call_env_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]])
        \\ REPEAT STRIP_TAC
        \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[]
        \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
        \\ MP_TAC (Q.SPECL [`prog`,`call_env args'
           (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
              optimise_correct) \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[COUNT_LIST_GENLIST]
        \\ SIMP_TAC std_ss [call_env_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
        \\ first_assum (mp_then Any assume_tac data_to_bvi_result_eq)
        \\ fs [] \\ rveq
        \\ Cases_on `evaluate (c2,set_var n1 z' t2')` \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
              [`set_var n1 z' t2'`,`n1+1`,`n1::corr`,`F`,`live`]) \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (full_simp_tac(srw_ss())[var_corr_def,state_rel_def,set_var_def,lookup_insert,get_var_def,lookup_map]
          \\ full_simp_tac(srw_ss())[jump_exc_def,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
          \\ Q.PAT_X_ASSUM `env2 = t2'.locals` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
          \\ Q.UNABBREV_TAC `env2` \\ full_simp_tac(srw_ss())[lookup_inter_alt]
          \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
          \\ REPEAT STRIP_TAC THEN1
           (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ REPEAT STRIP_TAC
            \\ Q.MATCH_ASSUM_RENAME_TAC `n3 < LENGTH env`
            \\ `MEM (EL n3 corr) corr` by METIS_TAC [MEM_EL] \\ full_simp_tac(srw_ss())[]
            \\ SRW_TAC [] []
            \\ `EL n3 corr <= EL n3 corr` by full_simp_tac(srw_ss())[] \\ RES_TAC \\ full_simp_tac(srw_ss())[])
          THEN1 (`k <> n1 /\ n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
          THEN1
           (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
            \\ Cases_on `n' = n1` \\ RES_TAC \\ full_simp_tac(srw_ss())[]
            \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[]
            \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ Cases_on `lookup n' t2.locals` \\ full_simp_tac(srw_ss())[])
          \\ Cases_on `LASTN (t2'.handler + 1) t2'.stack` \\ full_simp_tac(srw_ss())[]
          \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM ADD1, FUNPOW_SUC]
        \\ reverse (Cases_on `q`) \\ full_simp_tac(srw_ss())[] THEN1
         (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ NTAC 2 (POP_ASSUM MP_TAC)
          \\ Q.PAT_X_ASSUM `xxx = t2'` (fn th => ONCE_REWRITE_TAC [GSYM th]) \\ full_simp_tac(srw_ss())[])
        \\ Cases_on `res` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac compile_SING_IMP
        \\ fs[var_corr_def,set_var_def]
        \\ `(t2'.stack = t2.stack) /\ (t2'.handler = t2.handler)` by
         (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[evaluate_def]
        THEN1
         (IMP_RES_TAC compile_LENGTH
          \\ `?v1. v = [v1]` by (Cases_on `v` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
          \\ full_simp_tac(srw_ss())[var_corr_def,set_var_def,call_env_def,get_var_def]
          \\ full_simp_tac(srw_ss())[state_rel_def,data_to_bvi_result_def,lookup_map])
        \\ fs[get_var_def,lookup_insert,lookup_map]
        \\ REPEAT STRIP_TAC
        THEN1
          fs[state_rel_def]
        THEN1
          (fs[LIST_REL_EL_EQN]>>
          ntac 2 strip_tac>>
          `EL n' corr ≠ n2` by
            (last_x_assum(qspec_then `n'` assume_tac)>>
            last_x_assum(qspec_then`n2` assume_tac)>>rfs[]>>
            CCONTR_TAC>>fs[])>>
          fs[])
        THEN1
          (Cases_on`k=n2`>>fs[]>>
          res_tac>>fs[])
        THEN1
          (`k ≠ n2` by
           (CCONTR_TAC>>fs[]>>
           `n ≤ n2` by fs[]>>
           res_tac>> fs[])>>
          simp[]>>
          FIRST_X_ASSUM MATCH_MP_TAC \\ reverse STRIP_TAC THEN1 METIS_TAC []
          \\ full_simp_tac(srw_ss())[set_var_def,lookup_insert]
          \\ sg `k <> n1` \\ full_simp_tac(srw_ss())[] THEN1
           (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
            \\ `n <= n1` by DECIDE_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[])
          \\ UNABBREV_ALL_TAC
          \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
          \\ Q.PAT_X_ASSUM `xxx = t2'.locals` (ASSUME_TAC o GSYM)
          \\ full_simp_tac(srw_ss())[lookup_inter_alt]
          \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[set_var_def]
        \\ full_simp_tac(srw_ss())[jump_exc_def]
        \\ Cases_on `LASTN (t1.handler + 1) t1.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,dataSemTheory.dec_clock_def]
        \\ Cases_on `LASTN (r'.handler + 1) r'.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
      \\ `(res4,r4) = (res,s2)`
         by (Cases_on `res4` \\ full_simp_tac(srw_ss())[]
            \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args' (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
           `LENGTH args'`,
           `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,lookup_map,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList_MAP,lookup_fromList_outside,push_env_def,call_env_def]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by FULL_SIMP_TAC std_ss []
          \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def]
          \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
      \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args'
         (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
            optimise_correct) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[data_to_bvi_result_def])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,COUNT_LIST_GENLIST]
      \\ FULL_SIMP_TAC std_ss []
      \\ reverse (Cases_on `x'`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ full_simp_tac(srw_ss())[set_var_def,state_rel_def,data_to_bvi_result_def]
      THEN1 ( Cases_on`e`>>full_simp_tac(srw_ss())[data_to_bvi_result_def] )
      \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2
          ; handler := t2.handler |>)` by
       (Q.PAT_X_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           pop_env_def,dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def])
      \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[evaluate_def]
      THEN1 (full_simp_tac(srw_ss())[get_var_def,call_env_def,data_to_bvi_result_def])
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ IMP_RES_TAC compile_SING_IMP
      \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_RANGE \\ full_simp_tac(srw_ss())[EVERY_DEF]
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1
       (UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt]
        \\ `k ≠ n2` by DECIDE_TAC
        \\ `k <> t'` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,lookup_map]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
        \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
        \\ `EL l corr ≠ n2` by
          (CCONTR_TAC>>fs[LIST_REL_EL_EQN]>>
          last_x_assum(qspec_then `l` assume_tac)>>
          last_x_assum(qspec_then `n2` assume_tac)>>rfs[])
        \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL] \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ METIS_TAC [])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ Cases_on`k=n2`>>fs[]
        \\ Cases_on `k = t'` \\ FULL_SIMP_TAC std_ss []
        \\ CCONTR_TAC \\ `n2 <= k` by DECIDE_TAC
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
        \\ fs[])
      THEN1
        (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
        \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
        \\ `k ≠ n2` by
          (`n ≤ n2` by fs[]>>CCONTR_TAC>>fs[]>>res_tac>>fs[])
        \\ METIS_TAC [])
      THEN1
       (full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[jump_exc_def] \\ rev_full_simp_tac(srw_ss())[]
        \\ Cases_on `LASTN (t2.handler + 1) t2.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
      \\ fs[var_corr_def,get_var_def,lookup_map]));

val compile_exp_lemma = compile_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,`GENLIST I n`,`T`,`[]`]
  |> SIMP_RULE std_ss [LENGTH,GSYM compile_exp_def,option_case_NONE_F,
       PULL_EXISTS,EVERY_DEF];

Theorem compile_exp_correct:
   ^(compile_exp_lemma |> concl |> dest_imp |> fst) ==>
    ∃t2 prog vs next_var r.
      evaluate (compile_exp n exp,t1) = (SOME r,t2) /\
      state_rel s2 t2 /\ res_list (data_to_bvi_result r) = res
Proof
  REPEAT STRIP_TAC \\ MP_TAC compile_exp_lemma \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[compile_exp_def,LET_DEF]
  \\ MP_TAC (Q.SPECL [`prog`,`t1`] optimise_correct) \\ full_simp_tac(srw_ss())[]
  \\ impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[data_to_bvi_result_def])
  \\  srw_tac[][COUNT_LIST_GENLIST]
QED

val state_rel_dec_clock = Q.prove(
  `state_rel s1 t1 ⇒ state_rel (dec_clock 1 s1) (dec_clock t1)`,
  srw_tac[][state_rel_def,bviSemTheory.dec_clock_def,dataSemTheory.dec_clock_def])

Theorem compile_part_evaluate:
   evaluate ([Call 0 (SOME start) [] NONE],[],s1) = (res,s2) ∧
   res ≠ Rerr (Rabort Rtype_error) ∧ state_rel s1 t1 ∧
   isEmpty t1.locals ∧ (∀x. res = Rerr (Rraise x) ⇒ jump_exc t1 ≠ NONE)
   ⇒ ∃r t2.
      evaluate ((Call NONE (SOME start) [] NONE),t1) = (SOME r,t2) ∧
      state_rel s2 t2 ∧ res_list (data_to_bvi_result r) = res
Proof
  srw_tac[][bviSemTheory.evaluate_def,dataSemTheory.evaluate_def
           ,get_vars_def,find_code_def,dataSemTheory.find_code_def]
  \\ Cases_on`lookup start s1.code`
  \\ full_simp_tac(srw_ss())[]
  \\ qmatch_assum_rename_tac`lookup start s1.code = SOME p`
  \\ PairCases_on`p`
  \\ `lookup start t1.code = SOME (p0,compile_exp p0 p1)`
     by (full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
  \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> var_eq_tac
  \\ `s1.clock = t1.clock`
     by full_simp_tac(srw_ss())[state_rel_def]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- (full_simp_tac(srw_ss())[call_env_def,state_rel_def]
     \\ rpt var_eq_tac >> simp[data_to_bvi_result_def])
  \\ simp[] >> full_simp_tac(srw_ss())[]
  \\ first_assum(subterm split_pair_case0_tac o concl)
  \\ full_simp_tac(srw_ss())[]
  \\ drule (GEN_ALL compile_exp_correct)
  \\ simp[var_corr_def,SIMP_RULE std_ss [NULL_EQ]NULL_GENLIST]
  \\ imp_res_tac state_rel_dec_clock
  \\ disch_then(drule o (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``state_rel`` o fst o strip_comb))))))
  \\ simp[]
  \\ impl_tac
  >- (simp[lookup_def,dataSemTheory.dec_clock_def]
     \\ full_simp_tac(srw_ss())[jump_exc_def]
     \\ every_case_tac >> full_simp_tac(srw_ss())[]
     \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[])
  \\ strip_tac
  \\ simp[call_env_def,fromList_def]
  \\ `dec_clock t1 with locals := LN = dec_clock t1`
     by (EVAL_TAC >> simp[dataSemTheory.state_component_equality])
  \\ pop_assum SUBST1_TAC >> simp[]
  \\ every_case_tac
  \\ full_simp_tac(srw_ss())[]
QED

Theorem MAP_FST_compile_prog[simp]:
   ∀prog. MAP FST (compile_prog prog) = MAP FST prog
Proof
  simp[compile_prog_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD,compile_part_def]
QED

Theorem compile_prog_evaluate:
   evaluate ([Call 0 (SOME start) [] NONE],[],
     initial_state ffi0 (fromAList prog) co (λcfg prog. cc cfg (compile_prog prog)) k) = (r,s) ∧
   r ≠ Rerr (Rabort Rtype_error) ∧ (∀x. r ≠ Rerr (Rraise x))
   ⇒  ∃r2 s2.
       evaluate (Call NONE (SOME start) [] NONE,
         initial_state ffi0 (fromAList (compile_prog prog)) ((I ## compile_prog) o co) cc k) = (SOME r2,s2) ∧
         state_rel s s2 ∧ res_list (data_to_bvi_result r2) = r
Proof
  srw_tac[][]
  \\ match_mp_tac (GEN_ALL compile_part_evaluate)
  \\ asm_exists_tac >> simp[]
  \\ simp[initial_state_def,state_rel_def]
  \\ simp[code_rel_def,wf_fromAList,domain_fromAList,lookup_fromAList]
  \\ simp[compile_prog_def,ALOOKUP_MAP,compile_part_thm]
QED

Theorem FST_compile_part[simp]:
   FST (compile_part a) = (FST a)
Proof
  PairCases_on`a` \\ EVAL_TAC
QED

(* observational semantics *)

Theorem compile_prog_semantics:
   semantics (ffi0:'ffi ffi_state) (fromAList prog) co (λcfg prog. cc cfg (compile_prog prog)) start ≠ Fail ⇒
   semantics ffi0 (fromAList (compile_prog prog)) ((I ## compile_prog) o co) cc start =
   semantics ffi0 (fromAList prog) co (λcfg prog. cc cfg (compile_prog prog)) start
Proof
  simp[bviSemTheory.semantics_def]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro >> simp[]
  \\ conj_tac
  >- (qx_gen_tac`res`>>srw_tac[][]
     \\ simp[dataSemTheory.semantics_def]
     \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[]
     >- (qhdtm_x_assum`bviSem$evaluate`kall_tac
        \\ last_x_assum(qspec_then`k'`mp_tac)>>simp[]
        \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g)
        \\ spose_not_then strip_assume_tac
        \\ drule compile_prog_evaluate
        \\ impl_tac >- ( srw_tac[][] >> strip_tac >> full_simp_tac(srw_ss())[] )
        \\ strip_tac >> full_simp_tac(srw_ss())[] >> rveq
        \\ every_case_tac >> full_simp_tac(srw_ss())[]
        \\ Cases_on `e` >> fs [data_to_bvi_result_def])
     \\ DEEP_INTRO_TAC some_intro >> simp[]
     \\ conj_tac
     >- (gen_tac >> strip_tac >> rveq >> simp[]
        \\ qmatch_assum_abbrev_tac`bviSem$evaluate (exps,[],ss) = _`
        \\ qmatch_assum_abbrev_tac`dataSem$evaluate (bxps,bs) = _`
        \\ qspecl_then[`exps`,`[]`,`ss`]mp_tac
             (INST_TYPE[beta|->``:'ffi``]bviPropsTheory.evaluate_add_to_clock_io_events_mono)
        \\ Q.ISPECL_THEN[`bxps`,`bs`]mp_tac dataPropsTheory.evaluate_add_clock_io_events_mono
        \\ simp[bviPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`]
        \\ disch_then(qspec_then`k`strip_assume_tac)
        \\ disch_then(qspec_then`k'`strip_assume_tac)
        \\ qpat_x_assum `evaluate _ = (r,s)` assume_tac
        \\ drule bviPropsTheory.evaluate_add_clock
        \\ disch_then(qspec_then `k'` mp_tac)
        \\ impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[])
        \\ qpat_x_assum `evaluate _ = (SOME r',s')` assume_tac
        \\ drule dataPropsTheory.evaluate_add_clock
        \\ disch_then(qspec_then `k` mp_tac)
        \\ impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[])
        \\ simp[inc_clock_def]
        \\ ntac 2 strip_tac >> unabbrev_all_tac
        \\ drule compile_prog_evaluate
        \\ impl_tac >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
        \\ strip_tac >> rveq >> fs[state_rel_def]
        \\ rpt(PURE_FULL_CASE_TAC >> fs[data_to_bvi_result_def]))
     \\ drule compile_prog_evaluate
     \\ impl_tac
     >- (last_x_assum(qspec_then`k`mp_tac)
        \\ full_simp_tac(srw_ss())[]
        \\ rpt strip_tac
        \\ full_simp_tac(srw_ss())[])
     \\ strip_tac
     \\ asm_exists_tac >> simp[]
     \\ full_simp_tac(srw_ss())[state_rel_def]
     \\ every_case_tac >> full_simp_tac(srw_ss())[data_to_bvi_result_def])
  \\ strip_tac
  \\ simp[dataSemTheory.semantics_def]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- (last_x_assum(qspec_then`k`mp_tac)
     \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
     \\ strip_tac
     \\ drule compile_prog_evaluate
     \\ impl_tac
        >- (conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
     \\ strip_tac
     \\ full_simp_tac(srw_ss())[] >> srw_tac[][]
     \\ every_case_tac >> full_simp_tac(srw_ss())[]
     \\ Cases_on `e` >> fs [data_to_bvi_result_def])
  \\ DEEP_INTRO_TAC some_intro >> simp[]
  \\ conj_tac
  >- (spose_not_then strip_assume_tac
     \\ last_x_assum(qspec_then`k`mp_tac)
     \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
     \\ strip_tac
     \\ drule compile_prog_evaluate
     \\ impl_tac
     >- (conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
     \\ strip_tac
     \\ full_simp_tac(srw_ss())[] >> srw_tac[][]
     \\ every_case_tac >> full_simp_tac(srw_ss())[]
     \\ last_x_assum(qspec_then`k`mp_tac)
     \\ simp[]
     \\ every_case_tac >> simp[]
     \\ rev_full_simp_tac(srw_ss())[state_rel_def,data_to_bvi_result_def])
  \\ strip_tac
  \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM] >> gen_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (rhs(#2 g)))
  \\ drule compile_prog_evaluate
  \\ impl_tac
  >- (conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]
     \\ last_x_assum(qspec_then`k`mp_tac)>>simp[])
  \\ strip_tac >> simp[]
  \\ full_simp_tac(srw_ss())[state_rel_def]
QED

Theorem get_code_labels_iAssign[simp]:
   ∀a b c d e. get_code_labels (iAssign a b c d e) = closLang$assign_get_code_label b
Proof
  rw[bvi_to_dataTheory.iAssign_def]
  \\ EVAL_TAC
QED

Theorem get_code_labels_compile:
   ∀a b c d e. get_code_labels (FST (compile a b c d e)) ⊆
    BIGUNION (set (MAP get_code_labels e))
Proof
  recInduct bvi_to_dataTheory.compile_ind
  \\ rw[bvi_to_dataTheory.compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]
  \\ rw[] \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`mk_ticks a b`
  \\ qspecl_then[`a`,`b`]mp_tac dataPropsTheory.get_code_labels_mk_ticks
  \\ simp[SUBSET_DEF]
  \\ disch_then drule \\ rw[Abbr`b`,Abbr`a`]
  \\ qmatch_asmsub_abbrev_tac`mk_ticks a b`
  \\ qspecl_then[`a`,`b`]mp_tac dataPropsTheory.get_code_labels_mk_ticks
  \\ simp[SUBSET_DEF]
  \\ disch_then drule \\ rw[Abbr`b`,Abbr`a`]
QED

Theorem compile_prog_good_code_labels:
   ∀p. good_code_labels p ⇒ good_code_labels (bvi_to_data$compile_prog p)
Proof
  simp[bvi_to_dataTheory.compile_prog_def]
  \\ simp[dataPropsTheory.good_code_labels_def, MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ simp[bvi_to_dataTheory.compile_part_def]
  \\ simp[FST_triple]
  \\ simp[bviPropsTheory.good_code_labels_def]
  \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP, FORALL_PROD, EXISTS_PROD]
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[bvi_to_dataTheory.compile_exp_def]
  \\ fs[bvi_to_dataTheory.optimise_def]
  \\ qmatch_asmsub_abbrev_tac`get_code_labels (simp a b)`
  \\ qspecl_then[`a`,`b`]mp_tac data_simpProofTheory.get_code_labels_simp
  \\ simp_tac std_ss [SUBSET_DEF]
  \\ disch_then drule
  \\ rw[Abbr`a`,Abbr`b`]
  \\ qmatch_asmsub_abbrev_tac`FST (compile a b)`
  \\ qspecl_then[`a`,`b`]mp_tac data_liveProofTheory.get_code_labels_compile
  \\ simp[SUBSET_DEF]
  \\ disch_then drule
  \\ rw[Abbr`a`, Abbr`b`]
  \\ qmatch_asmsub_abbrev_tac`FST (compile a b c d e)`
  \\ qspecl_then[`a`,`b`,`c`,`d`,`e`]mp_tac get_code_labels_compile
  \\ simp[SUBSET_DEF,Abbr`c`]
  \\ disch_then drule
  \\ simp[Abbr`e`]
QED

val _ = export_theory();
