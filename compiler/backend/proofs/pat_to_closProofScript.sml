(*
  Correctness proof for pat_to_clos
*)
open preamble intLib integerTheory backendPropsTheory
     semanticPrimitivesTheory
     patSemTheory patPropsTheory pat_to_closTheory
     closLangTheory closSemTheory closPropsTheory

val _ = new_theory"pat_to_closProof"

val _ = set_grammar_ancestry
  ["patLang", "patSem", "patProps", "pat_to_clos",
   "closLang", "closSem", "closProps"];

(* value translation *)

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv (IntLit i)) = (Number i):closSem$v) ∧
  (compile_v (Litv (Word8 w)) = (Number (& (w2n w)))) ∧
  (compile_v (Litv (Word64 w)) = (Word64 w)) ∧
  (compile_v (Litv (Char c)) = (Number (& ORD c))) ∧
  (compile_v (Litv (StrLit s)) = (ByteVector (MAP (n2w o ORD) s))) ∧
  (compile_v (Loc m) = (RefPtr m)) ∧
  (compile_v (Conv cn vs) = (Block cn (MAP (compile_v) vs))) ∧
  (compile_v (Vectorv vs) = (Block vector_tag (MAP (compile_v) vs))) ∧
  (compile_v (Closure vs e) = (Closure NONE [] (MAP (compile_v) vs) 1 (compile e))) ∧
  (compile_v (Recclosure vs es k) = (Recclosure NONE [] (MAP (compile_v) vs) (MAP (λe. (1,compile e)) es) k))`
    (WF_REL_TAC`measure (patSem$v_size)` >> simp[patSemTheory.v_size_def] >>
     rpt conj_tac >> rpt gen_tac >>
     Induct_on`vs` >> simp[patSemTheory.v_size_def] >>
     rw[] >> res_tac >> fs[] >> simp[patSemTheory.v_size_def])
val _ = export_rewrites["compile_v_def"]

val compile_sv_def = Define `
  (compile_sv (Refv v) = ValueArray [compile_v v]) ∧
  (compile_sv (Varray vs) = ValueArray (MAP compile_v vs)) ∧
  (compile_sv (W8array bs) = ByteArray F bs)`
val _ = export_rewrites["compile_sv_def"];

val compile_state_def = Define`
  compile_state max_app cc (s:('c,'ffi) patSem$state) =
    <| globals := MAP (OPTION_MAP compile_v) s.globals;
       refs := alist_to_fmap (GENLIST (λi. (i, compile_sv (EL i s.refs))) (LENGTH s.refs));
       ffi := s.ffi;
       clock := s.clock;
       code := FEMPTY;
       compile := cc;
       compile_oracle := pure_co (λes. (MAP compile es,[])) o s.compile_oracle;
       max_app := max_app
    |>`;

Theorem compile_state_const[simp]:
   (compile_state max_app cc s).clock = s.clock ∧
   (compile_state max_app cc s).ffi = s.ffi ∧
   (compile_state max_app cc s).compile = cc ∧
   (compile_state max_app cc s).max_app = max_app ∧
   (compile_state max_app cc s).compile_oracle = pure_co (λe. (MAP compile e,[])) o s.compile_oracle
Proof
  EVAL_TAC
QED

Theorem compile_state_dec_clock[simp]:
   compile_state max_app cc (dec_clock y) = dec_clock 1 (compile_state max_app cc y)
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_state_with_clock[simp]:
   compile_state max_app cc (s with clock := k) = compile_state max_app cc s with clock := k
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_state_with_refs_const[simp]:
   (compile_state w cc (s with refs := r)).globals = (compile_state w cc s).globals ∧
   (compile_state w cc (s with refs := r)).code = (compile_state w cc s).code
Proof
  EVAL_TAC
QED

Theorem FLOOKUP_compile_state_refs:
   FLOOKUP (compile_state w cc s).refs =
   OPTION_MAP compile_sv o (combin$C store_lookup s.refs)
Proof
  rw[FUN_EQ_THM,compile_state_def,ALOOKUP_GENLIST,store_lookup_def] \\ rw[]
QED

Theorem FDOM_compile_state_refs[simp]:
   FDOM (compile_state w cc s).refs = count (LENGTH s.refs)
Proof
  rw[compile_state_def,MAP_GENLIST,o_DEF,LIST_TO_SET_GENLIST]
QED

Theorem compile_state_with_refs_snoc:
   compile_state w cc (s with refs := s.refs ++ [x]) =
   compile_state w cc s with refs :=
     (compile_state w cc s).refs |+ (LENGTH s.refs, compile_sv x)
Proof
  rw[compile_state_def,fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST]
  \\ rw[EL_APPEND1,EL_APPEND2]
QED

(* semantic functions respect translation *)

Theorem do_eq:
   (∀v1 v2. do_eq v1 v2 ≠ Eq_type_error ⇒
      (do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2))) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 ≠ Eq_type_error ⇒
      (do_eq_list vs1 vs2 = do_eq_list (MAP compile_v vs1) (MAP compile_v vs2)))
Proof
  ho_match_mp_tac patSemTheory.do_eq_ind >>
  simp[patSemTheory.do_eq_def,closSemTheory.do_eq_def] >>
  conj_tac >- (
    Cases >> Cases >> simp[lit_same_type_def,closSemTheory.do_eq_def] >>
    rw[LIST_EQ_REWRITE,EL_MAP,EQ_IMP_THM] \\ rfs[EL_MAP] \\ res_tac
    \\ fs[ORD_11,ORD_BOUND]) >>
  conj_tac >- rw[ETA_AX] >>
  conj_tac >- rw[ETA_AX] >>
  rw[] >>
  Cases_on`v1`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  Cases_on`v2`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  fs[closSemTheory.do_eq_def,patSemTheory.do_eq_def,lit_same_type_def,ORD_11] >>
  rw[]>>fs[]>>rfs[ETA_AX]>>
  BasicProvers.CASE_TAC>>fs[]>>
  rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]
QED

val v_to_list_def = closSemTheory.v_to_list_def;

Theorem v_to_char_list:
   ∀v ls. (v_to_char_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP (Number o $& o ORD) ls))
Proof
  ho_match_mp_tac v_to_char_list_ind >>
  simp[v_to_char_list_def,v_to_list_def] >>
  rw[] >>
  Cases_on`v`>>fs[v_to_char_list_def] >>
  Cases_on`l`>>fs[v_to_char_list_def,v_to_list_def] >>
  rw[]>>fs[]>>
  Cases_on`h`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`l`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`t`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`t'`>>fs[v_to_char_list_def,v_to_list_def] >>
  rw[]>>fs[]>>
  Cases_on`v_to_char_list h`>>fs[]>> rw[]
QED

Theorem v_to_list:
   ∀v ls. (v_to_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP compile_v ls))
Proof
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def,v_to_list_def] >>
  rw[] >> Cases_on`v_to_list v`>>fs[]>> rw[]
QED

Theorem vs_to_string:
   ∀vs ws. vs_to_string vs = SOME ws ⇒
    ∃wss. MAP compile_v vs = MAP ByteVector wss ∧
      FLAT wss = MAP (n2w o ORD) ws
Proof
  ho_match_mp_tac vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ qmatch_goalsub_abbrev_tac`ByteVector ws1`
  \\ qexists_tac`ws1::wss` \\ simp[]
QED

Theorem Boolv[simp]:
   compile_v (Boolv b) = Boolv b
Proof
  Cases_on`b`>>EVAL_TAC
QED

Theorem v_to_bytes:
   v_to_bytes v = SOME ls ==> v_to_bytes (compile_v v) = SOME ls
Proof
  simp[patSemTheory.v_to_bytes_def,v_to_bytes_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ imp_res_tac v_to_list
  \\ rw[MAP_MAP_o,o_DEF]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF]
  \\ metis_tac[]
QED

Theorem v_to_words:
   v_to_words v = SOME ls ==> v_to_words (compile_v v) = SOME ls
Proof
  simp[patSemTheory.v_to_words_def,v_to_words_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ imp_res_tac v_to_list
  \\ rw[MAP_MAP_o,o_DEF]
  \\ DEEP_INTRO_TAC some_intro \\ rw[ETA_AX]
  \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF]
  \\ metis_tac[]
QED

Theorem do_install:
   patSem$do_install vs s = SOME (v1,v2) ∧
   s.compile = pure_cc (λe. (MAP compile e,[])) cc
   ==>
   closSem$do_install (MAP compile_v vs) (compile_state max_app cc s) =
     if s.clock = 0 then (Rerr (Rabort Rtimeout_error),compile_state max_app cc v2)
     else (Rval (MAP compile v1),dec_clock 1(compile_state max_app cc v2))
Proof
  simp[do_install_def,patSemTheory.do_install_def,case_eq_thms]
  \\ simp[] \\ strip_tac \\ rveq \\ fs[]
  \\ imp_res_tac v_to_bytes \\ imp_res_tac v_to_words
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[pure_co_def] \\ rveq
  \\ rfs[pure_cc_def]
  \\ fs[case_eq_thms,pair_case_eq,shift_seq_def,FUPDATE_LIST_THM] \\ rveq
  \\ fs[bool_case_eq,dec_clock_def]
  \\ fs[state_component_equality,compile_state_def,pure_co_def,FUN_EQ_THM]
QED

(* compiler correctness *)

val true_neq_false = EVAL``true_tag = false_tag`` |> EQF_ELIM;

val arw = srw_tac[ARITH_ss]

val do_app_def = closSemTheory.do_app_def

val build_rec_env_pat_def = patSemTheory.build_rec_env_def
val do_opapp_pat_def = patSemTheory.do_opapp_def
val do_app_pat_def = patSemTheory.do_app_def
val evaluate_def = closSemTheory.evaluate_def
val evaluate_pat_def = patSemTheory.evaluate_def;

val s = mk_var("s",
  ``patSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> gamma, beta |-> ``:'ffi``]);

val LENGTH_eq = Q.prove(
  `(LENGTH ls = 1 ⇔ ∃y. ls = [y]) ∧
   (LENGTH ls = 2 ⇔ ∃y z. ls = [y; z]) ∧
   (LENGTH ls = 0 ⇔ ls = []) ∧
   (0 = LENGTH ls ⇔ LENGTH ls = 0) ∧
   (1 = LENGTH ls ⇔ LENGTH ls = 1) ∧
   (2 = LENGTH ls ⇔ LENGTH ls = 2)`,
  Cases_on`ls`>>simp[]>> Cases_on`t`>>simp[LENGTH_NIL]);

Theorem list_to_v_compile:
   !x xs.
   v_to_list x = SOME xs /\
   v_to_list (compile_v x) = SOME (MAP compile_v xs) ==>
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs)
Proof
  ho_match_mp_tac patSemTheory.v_to_list_ind
  \\ rw [patSemTheory.v_to_list_def] \\ fs []
  \\ fs [list_to_v_def, patSemTheory.list_to_v_def, case_eq_thms] \\ rveq
  \\ fs [v_to_list_def, case_eq_thms, list_to_v_def, patSemTheory.list_to_v_def]
QED

Theorem list_to_v_compile_APPEND:
   !xs ys.
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs) /\
     list_to_v (MAP compile_v ys) = compile_v (list_to_v ys) ==>
       list_to_v (MAP compile_v (xs ++ ys)) =
       compile_v (list_to_v (xs ++ ys))
Proof
  Induct \\ rw [patSemTheory.list_to_v_def]
  \\ fs [list_to_v_def, patSemTheory.list_to_v_def]
QED

Theorem dest_WordToInt_SOME:
   !w es x. dest_WordToInt w es = SOME x <=>
             ?tra. es = [App tra (Op (WordToInt w)) [x]]
Proof
  ho_match_mp_tac dest_WordToInt_ind
  \\ fs [dest_WordToInt_def]
QED

val Rabort_Rtype_error_map_error = prove(
  ``Rabort Rtype_error = map_error_result compile_v e <=>
    e = Rabort Rtype_error``,
  Cases_on `e` \\ fs [] \\ eq_tac \\ rw []);

val do_app_WordToInt_Rerr_IMP = prove(
  ``closSem$do_app WordToInt ws x = Rerr e ==> e = Rabort Rtype_error``,
  fs [do_app_def,case_eq_thms,pair_case_eq] \\ rw [] \\ fs []);

Theorem compile_evaluate:
   0 < max_app ⇒
   (∀env ^s es s' r.
      evaluate env s es = (s',r) ∧
      s.compile = pure_cc (λe. (MAP pat_to_clos$compile e,[])) cc ∧
      r ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate (MAP compile es,MAP compile_v env,compile_state max_app cc s) =
        (map_result (MAP compile_v) compile_v r, compile_state max_app cc s'))
Proof
  strip_tac >>
  ho_match_mp_tac patSemTheory.evaluate_ind >>
  strip_tac >- (rw[evaluate_pat_def,evaluate_def]>>rw[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum`_ = (_,_)`mp_tac >>
    simp[Once evaluate_cons] >>
    split_pair_case_tac >> fs[] >>
    simp[Once evaluate_CONS] >> strip_tac >>
    fs[case_eq_thms,pair_case_eq] \\ rveq \\ fs[] >>
    imp_res_tac patPropsTheory.evaluate_const \\ fs[] \\
    imp_res_tac evaluate_sing >> rw[] >>fs[] >> rfs[]) >>
  strip_tac >- (
    Cases_on`l`>>
    rw[evaluate_def,do_app_def] >> rw[] >>
    simp[GSYM MAP_REVERSE,evaluate_MAP_Op_Const,combinTheory.o_DEF]) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def,case_eq_thms,pair_case_eq] >>
    imp_res_tac evaluate_const \\ fs[] \\
    imp_res_tac evaluate_sing >> fs[]) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def,case_eq_thms,pair_case_eq] >>
    imp_res_tac patPropsTheory.evaluate_const \\ fs[] ) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def,do_app_def,case_eq_thms,pair_case_eq] >>
    fs[ETA_AX,MAP_REVERSE] ) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def,EL_MAP] >> rw[] >>
    spose_not_then strip_assume_tac >> rw[] >> fs[]) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def] >> rw[ETA_AX] ) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def] >>
    Cases_on`op=(Op Opapp)`>>fs[] >- (
      split_pair_case_tac >> fs[] >>
      qmatch_assum_rename_tac `_ = (s1,r1)` >>
      reverse(Cases_on`r1`)>>fs[] >- (
        rw[]>>fs[evaluate_def,MAP_REVERSE,ETA_AX] >>
        Cases_on`es`>>fs[] >> Cases_on`t`>>fs[LENGTH_NIL] >>
        fs[Once evaluate_CONS] >>
        fs[pair_case_eq,case_eq_thms] >> rw[] >>
        fs[evaluate_def] ) >>
      imp_res_tac evaluate_length >>
      fs[MAP_REVERSE,ETA_AX] >>
      IF_CASES_TAC >> fs[LENGTH_eq] >- (
        simp[evaluate_def,do_app_def] >>
        fs[case_eq_thms,pair_case_eq,bool_case_eq,do_opapp_def,SWAP_REVERSE_SYM] >>
        rw[] >> fs[LENGTH_eq]) >>
      rpt var_eq_tac >> fs[LENGTH_eq] >> var_eq_tac >>
      simp[evaluate_def] >>
      fs[Once evaluate_CONS] >>
      split_pair_case_tac >> fs[] >>
      fs[evaluate_def] >>
      pop_assum mp_tac >>
      split_pair_case_tac >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> strip_tac >>
      rpt var_eq_tac >> fs[] >>
      split_pair_case_tac >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> rpt var_eq_tac >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] >> rw[] >>
      qmatch_assum_rename_tac`_ = (s1,Rval [d; c])` >>
      Cases_on`do_opapp [c; d]`>>fs[] >>
      split_pair_case_tac >> fs[] >>
      rpt var_eq_tac >>
      fs[bool_case_eq] >- (
        simp[evaluate_def] >> fs[do_opapp_def] >>
        Cases_on`c`>>fs[dest_closure_def,check_loc_def,LET_THM] >>
        simp[state_component_equality,EL_MAP]) >>
      simp[evaluate_def] >> fs[do_opapp_def] >>
      imp_res_tac patPropsTheory.evaluate_const >>
      Cases_on`c`>>fs[dest_closure_def,check_loc_def,EL_MAP,LET_THM,ETA_AX] >>simp[] >>
      rpt var_eq_tac >> fs[build_rec_env_pat_def,patSemTheory.dec_clock_def,closSemTheory.dec_clock_def] >>
      split_pair_case_tac >> fs[] >>
      fs[MAP_GENLIST,o_DEF,ETA_AX] >>
      fsrw_tac[boolSimps.ETA_ss][] >>
      qpat_x_assum`(_,_) = _`(assume_tac o SYM) >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] >>
      simp[evaluate_def] >> rw[] >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] ) >>
    Cases_on`op = Run` \\ fs[] >- (
      split_pair_case_tac \\ fs[] \\
      fs[evaluate_def,MAP_REVERSE,ETA_AX] \\
      first_x_assum(fn th => mp_tac th \\ (impl_tac >- (strip_tac \\ fs[]))) \\
      rw[] \\
      fs[case_eq_thms,pair_case_eq] \\ rveq \\ fs[] \\
      drule do_install \\
      imp_res_tac patPropsTheory.evaluate_const \\ fs[MAP_REVERSE] \\
      imp_res_tac patPropsTheory.do_install_const \\
      IF_CASES_TAC \\ fs[] \\ fs[patSemTheory.dec_clock_def]
      \\ fs[CaseEq"prod"] \\ fs[]
      \\ fs[CaseEq"semanticPrimitives$result"] \\ rveq \\ fs[]
      \\ rw[]
      \\ irule LAST_MAP
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ strip_tac \\ fs[do_install_def,CaseEq"prod",CaseEq"option",CaseEq"bool",CaseEq"list"]
      \\ pairarg_tac \\ fs[CaseEq"bool",CaseEq"prod",CaseEq"option"]) \\
    reverse(fs[case_eq_thms,pair_case_eq]) \\ rw[] \\ fs[] >- (
      reverse(Cases_on`op`)>>fs[evaluate_def,ETA_AX,MAP_REVERSE] >- (
        rw[] >> fs[LENGTH_eq,evaluate_def,do_app_def] >>
        rw[] >> fs[] ) >>
      qmatch_assum_rename_tac`op ≠ Opapp` >>
      (Cases_on`op`)>>fs[evaluate_def,ETA_AX] >>
      TRY ( qmatch_goalsub_rename_tac`Opn op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`Opb op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`Chopb op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`WordFromInt wz` >> Cases_on`wz`) >>
      TRY ( qmatch_goalsub_rename_tac`WordToInt wz` >> Cases_on`wz`) >>
      fs[evaluate_def,ETA_AX,MAP_REVERSE]
      >- (
          rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
          rw[] >> fs[] >> qhdtm_x_assum`evaluate`mp_tac >>
          simp[Once evaluate_CONS] >>
          rw[case_eq_thms,pair_case_eq] >> rw[do_app_def])
      >- (
        rw[Once evaluate_CONS,evaluate_def] >>
        rw[do_app_def] ) >>
      TRY
       (qmatch_goalsub_abbrev_tac `dest_WordToInt www` >>
        Cases_on `dest_WordToInt www es` >>
        qunabbrev_tac `www` >>
        fs [dest_WordToInt_SOME] >> rw [] >>
        fs[evaluate_def,ETA_AX,MAP_REVERSE,compile_def] >>
        TRY (rw[Once evaluate_CONS,evaluate_def] >> rw[do_app_def] >> NO_TAC) >>
        TOP_CASE_TAC \\ fs [case_eq_thms,pair_case_eq] >>
        rveq \\ fs [] >>
        qabbrev_tac `ws = REVERSE vs` >>
        `vs = REVERSE ws` by (fs [Abbr `ws`]) \\ rveq >>
        fs [Rabort_Rtype_error_map_error] >>
        imp_res_tac do_app_WordToInt_Rerr_IMP \\ fs [])
      >> (
        rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
        rw[] >> fs[] >>
        fs[do_app_def])) >>
    Cases_on `op = (Op ListAppend)`
    >-
     (rw []
      \\ fs [do_app_cases, SWAP_REVERSE_SYM] \\ rw []
      \\ fsrw_tac [ETA_ss] [evaluate_def, do_app_def, case_eq_thms,
                            pair_case_eq, PULL_EXISTS, SWAP_REVERSE_SYM]
      \\ imp_res_tac evaluate_length
      \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
      \\ fs [evaluate_def, case_eq_thms, pair_case_eq] \\ rveq
      \\ imp_res_tac v_to_list \\ fs []
      \\ metis_tac [list_to_v_compile_APPEND, list_to_v_compile, MAP_APPEND]) >>
    fs[patSemTheory.do_app_cases] >> rw[] >>
    rfs[] >>
    fsrw_tac[ETA_ss][SWAP_REVERSE_SYM] >>
    fs[evaluate_def,MAP_REVERSE,do_app_def,PULL_EXISTS,
       store_alloc_def,FLOOKUP_compile_state_refs,int_gt,
       prim_exn_def,NOT_LESS,EL_MAP,GREATER_EQ] >>
    imp_res_tac evaluate_length >> fs[LENGTH_EQ_NUM_compute] >>
    rveq \\
    fs[evaluate_def,do_app_def,FLOOKUP_compile_state_refs,
       compile_state_with_refs_snoc,case_eq_thms,pair_case_eq,
       INT_NOT_LT,int_ge,PULL_EXISTS,IMPLODE_EXPLODE_I,
       INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd] >>
    simp[MAP_MAP_o,n2w_ORD_CHR_w2n,EL_MAP,Unit_def] >>
    simp[o_DEF] >>
    rfs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd] >>
    TRY (
      rename1`CopyByteStr`
      \\ rw[CopyByteStr_def]
      \\ fs[evaluate_def,do_app_def,do_eq_def,copy_array_def,store_lookup_def]
      \\ IF_CASES_TAC \\ fs[INT_NOT_LT]
      \\ IF_CASES_TAC \\ fs[INT_NOT_LT]
      \\ fs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ fs[FLOOKUP_compile_state_refs,store_lookup_def]
      \\ rename1`off + len ≤ &LENGTH st`
      \\ `off + len ≤ &LENGTH st ⇔ ¬(LENGTH st < Num (off + len))` by COOPER_TAC
      \\ simp[]
      \\ IF_CASES_TAC \\ simp[]
      \\ simp[MAP_TAKE,MAP_DROP,ws_to_chars_def,MAP_MAP_o,o_DEF,ORD_CHR,w2n_lt_256]
      \\ NO_TAC ) \\
    TRY (
      rename1`CopyByteAw8`
      \\ rw[CopyByteAw8_def]
      \\ fs[evaluate_def,do_app_def,do_eq_def,copy_array_def,store_lookup_def]
      \\ TRY IF_CASES_TAC \\ fs[INT_NOT_LT] \\ TRY COOPER_TAC
      \\ TRY IF_CASES_TAC \\ fs[INT_NOT_LT]
      \\ fs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ fs[FLOOKUP_compile_state_refs,store_lookup_def]
      \\ rename1`off + len ≤ &LENGTH st`
      \\ `off + len ≤ &LENGTH st ⇔ ¬(LENGTH st < Num (off + len))` by COOPER_TAC
      \\ simp[]
      \\ fs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ fs[ws_to_chars_def]
      \\ TRY IF_CASES_TAC \\ fs[] \\ TRY COOPER_TAC
      \\ TRY IF_CASES_TAC \\ fs[] \\ TRY COOPER_TAC
      \\ simp[FLOOKUP_compile_state_refs,store_lookup_def]
      \\ fs[INT_NOT_LT]
      \\ simp[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ rename1`dstoff + len ≤ &LENGTH ds`
      \\ `dstoff + len ≤ &LENGTH ds ⇔ ¬(LENGTH ds < Num (dstoff + len))` by COOPER_TAC
      \\ simp[]
      \\ fs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ TRY IF_CASES_TAC \\ fs[ws_to_chars_def] \\ TRY COOPER_TAC
      \\ fs[Unit_def,store_assign_def]
      \\ simp[state_component_equality,FLOOKUP_compile_state_refs,fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST]
      \\ rw[store_lookup_def,EL_LUPDATE,chars_to_ws_def,MAP_TAKE,MAP_DROP,MAP_MAP_o]
      \\ simp[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ simp[o_DEF,ORD_CHR,w2n_lt_256,integer_wordTheory.i2w_def]
      \\ `F` by COOPER_TAC) \\
    TRY (
      rename1`do_shift sh n wz wd`
      \\ Cases_on`wz` \\ Cases_on`wd` \\ fs[]
      \\ rw[] \\ NO_TAC) >>
    TRY (
      rename1`do_word_from_int wz i`
      \\ Cases_on`wz` \\ fs[evaluate_def,do_app_def,integer_wordTheory.w2n_i2w]
      \\ NO_TAC) >>
    TRY (
      rename1`do_word_to_int wz w`
      \\ Cases_on`wz` \\ Cases_on`w` \\ fs[evaluate_def,do_app_def]
      \\ NO_TAC) >>
    TRY (
      rename1`ORD(CHR(Num i))`
      \\ `Num i < 256` by COOPER_TAC
      \\ simp[ORD_CHR,INT_OF_NUM]
      \\ COOPER_TAC ) >>
    TRY (
      rename1`Opn opn`
      \\ Cases_on`opn`
      \\ fs[evaluate_def,do_app_def,opn_lookup_def,
            closSemTheory.do_eq_def]
      \\ NO_TAC) >>
    TRY (
      rename1`do_eq (Number 0) (Number 0)`
      \\ simp[closSemTheory.do_eq_def]
      \\ NO_TAC ) >>
    TRY (
      rename1`Opb opb`
      \\ Cases_on`opb`
      \\ fs[evaluate_def,do_app_def,opb_lookup_def]
      \\ NO_TAC) >>
    TRY (
      rename1`Chopb op` >>
      Cases_on`op`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def] >>
      NO_TAC) >>
    TRY (
      rename1`do_word_op op wz w1 w2`
      \\ Cases_on`wz` \\ Cases_on`w1` \\ Cases_on`w2` \\ fs[evaluate_def]
      \\ rveq \\ fs[]
      \\ DEEP_INTRO_TAC some_intro
      \\ simp[FORALL_PROD]
      \\ NO_TAC) >>
    imp_res_tac v_to_list \\ fs[] >>
    TRY (
      rename1`v_to_char_list` >>
      imp_res_tac v_to_char_list \\ fs[] >>
      DEEP_INTRO_TAC some_intro >> fs[PULL_EXISTS] >>
      qexists_tac`MAP ORD ls` \\
      simp[MAP_MAP_o,EVERY_MAP,ORD_BOUND] \\
      rw[LIST_EQ_REWRITE,EL_MAP,ORD_BOUND] \\ rfs[]
      \\ fs[EL_MAP] \\ metis_tac[ORD_BOUND]) >>
    TRY (
      rename1`vs_to_string` >>
      imp_res_tac vs_to_string \\ fs[] >>
      DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] >>
      qexists_tac`wss` \\ rw[] >>
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] >>
      simp[o_DEF]
      \\ NO_TAC) >>
    TRY (
      rename1`get_global` >>
      simp[compile_state_def,get_global_def,EL_MAP] >>
      simp[LUPDATE_MAP] >> NO_TAC) >>
    TRY (
      rename1`patSem$do_eq v1 v2`
      \\ Cases_on`do_eq v1 v2 = Eq_type_error` \\ fs[]
      \\ imp_res_tac do_eq \\ fs[] \\ rw[]
      \\ NO_TAC ) >>
    TRY (
      IF_CASES_TAC \\ TRY (`F` by COOPER_TAC)
      \\ simp[EL_MAP,ORD_BOUND] ) >>
    TRY (
      rename1`store_lookup`
      \\ fs[store_lookup_def,store_assign_def]
      \\ qmatch_assum_rename_tac`store_v_same_type (EL lnum t.refs) _`
      \\ Cases_on`EL lnum t.refs` \\ fs[store_v_same_type_def] ) >>
    TRY (
      rename1 `Litv w1`
      \\ Cases_on `w1` \\ fs [compile_v_def]
      \\ rename1 `do_shift sh n wl _`
      \\ Cases_on `wl` \\ fs [semanticPrimitivesPropsTheory.do_shift_def]
      \\ qpat_x_assum `_ = w` (fn thm => rw [GSYM thm])) >>
    TRY (
      rename1 `(Op (WordFromInt ws55))`
      \\ Cases_on `ws55` \\ fs [compile_v_def]
      \\ TOP_CASE_TAC \\ fs [dest_WordToInt_SOME] \\ rveq \\ fs []
      \\ fs[evaluate_def,do_app_def,integer_wordTheory.w2n_i2w,
            case_eq_thms,pair_case_eq] \\ rveq \\ fs [w2w_def]
      \\ fs [some_def]
      \\ fs [patSemTheory.evaluate_def,case_eq_thms,pair_case_eq]
      \\ rveq \\ fs []
      \\ qabbrev_tac `ws = REVERSE vs`
      \\ `vs = REVERSE ws` by (fs [Abbr `ws`]) \\ rveq
      \\ fs [patSemTheory.do_app_def,case_eq_thms,pair_case_eq]
      \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs []
      \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs []
      \\ fs [patSemTheory.do_app_def,case_eq_thms,pair_case_eq]
      \\ rveq \\ fs [] \\ Cases_on `l`
      \\ fs [semanticPrimitivesPropsTheory.do_word_to_int_def]
      \\ rveq \\ fs [w2w_def]) >>
    fs[state_component_equality,compile_state_def,fmap_eq_flookup,
       ALOOKUP_GENLIST,FLOOKUP_UPDATE,store_assign_def,store_lookup_def,
       get_global_def, EL_MAP, IS_SOME_EXISTS,
       evaluate_REPLICATE_Op_AllocGlobal, REPLICATE_GENLIST, MAP_GENLIST]
    \\ rveq \\ simp[EL_LUPDATE] \\ rw[LUPDATE_def,map_replicate,LUPDATE_MAP]
    \\ simp[ETA_THM]) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def,patSemTheory.do_if_def] >> rw[] >>
    fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ fs[] \\ rveq \\
    imp_res_tac evaluate_length >> fs[LENGTH_eq] >>
    imp_res_tac patPropsTheory.evaluate_const >> rw[] >> fs[] ) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >> rw[] >>
    fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ fs[] \\ rveq \\
    imp_res_tac evaluate_length >> fs[LENGTH_eq] >>
    imp_res_tac patPropsTheory.evaluate_const >> rw[] >> fs[] ) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >> rw[] >>
    fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ fs[] \\ rveq \\
    imp_res_tac patPropsTheory.evaluate_const \\ fs[] \\
    Cases_on`r` \\ fs[] \\
    imp_res_tac evaluate_length >> fs[LENGTH_eq]) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >>
    rw[] >> fs[EXISTS_MAP] >>
    fs[build_rec_env_pat_def,build_recc_def,MAP_GENLIST,
       combinTheory.o_DEF,ETA_AX,MAP_MAP_o,clos_env_def] >>
    fsrw_tac[ETA_ss][] )
QED

Theorem compile_semantics:
   0 < max_app ∧ st.compile = pure_cc (λe. (MAP compile e,[])) cc ∧ st.globals = [] ∧ st.refs = [] ⇒
   semantics [] (st:('c,'ffi)patSem$state) es ≠ Fail ⇒
   semantics st.ffi max_app FEMPTY (pure_co (λe. (MAP compile e,[])) o st.compile_oracle) cc (MAP compile es) =
   semantics [] st es
Proof
  strip_tac >>
  simp[patSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[] >>
    simp[closSemTheory.semantics_def] >>
    IF_CASES_TAC >> fs[] >- (
      qhdtm_x_assum`patSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      spose_not_then strip_assume_tac >>
      drule (UNDISCH compile_evaluate) >>
      impl_tac >- ( rw[] >> strip_tac >> fs[] ) >>
      strip_tac >> fs[compile_state_def,initial_state_def] >>
      rfs[] \\ fs[]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[] >>
      qmatch_assum_abbrev_tac`patSem$evaluate env ss es = _` >>
      qmatch_assum_abbrev_tac`closSem$evaluate bp = _` >>
      Q.ISPECL_THEN[`env`,`ss`,`es`](mp_tac o Q.GEN`extra`) patPropsTheory.evaluate_add_to_clock_io_events_mono >>
      Q.ISPEC_THEN`bp`(mp_tac o Q.GEN`extra`) (CONJUNCT1 closPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[Abbr`ss`,Abbr`bp`] >>
      disch_then(qspec_then`k`strip_assume_tac) >>
      disch_then(qspec_then`k'`strip_assume_tac) >>
      drule(GEN_ALL(SIMP_RULE std_ss [](CONJUNCT1 closPropsTheory.evaluate_add_to_clock))) >>
      disch_then(qspec_then `k` mp_tac) >>
      impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      drule(GEN_ALL(SIMP_RULE std_ss [] patPropsTheory.evaluate_add_to_clock)) >>
      disch_then(qspec_then `k'` mp_tac) >>
      impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      ntac 2 strip_tac >> fs[] >>
      drule (UNDISCH compile_evaluate) >>
      impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      strip_tac >> unabbrev_all_tac >> fs[] >>
      fs[compile_state_def,initial_state_def] >> rfs[] >>
      fs[state_component_equality] >> rpt(PURE_FULL_CASE_TAC >> fs[])) >>
    drule (UNDISCH compile_evaluate) >> simp[] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>
      fs[] >> rpt strip_tac >> fs[] ) >>
    strip_tac >>
    rfs[initial_state_def,compile_state_def] >>
    asm_exists_tac >> simp[] >> rpt(PURE_FULL_CASE_TAC >> fs[])) >>
  strip_tac >>
  simp[closSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`SND p ≠ _` >>
    Cases_on`p`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH compile_evaluate))) >>
    rw[compile_state_with_clock] >>
    strip_tac >> fs[initial_state_def,compile_state_def] >>
    rfs[] \\ fs[]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule (UNDISCH compile_evaluate) >> simp[] >>
    spose_not_then strip_assume_tac >>
    rveq >> fs[] >>
    last_x_assum(qspec_then`k`mp_tac) >>
    simp[] >>
    rfs[initial_state_def,compile_state_def] >> fs[] >>
    rpt(PURE_FULL_CASE_TAC >> fs[])) >>
  strip_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  qpat_abbrev_tac`s0 = closSem$initial_state _ _ _ _ _` \\
  specl_args_of_then``patSem$evaluate``(UNDISCH compile_evaluate) mp_tac >>
  qpat_abbrev_tac`s1 = compile_state _ _ _` \\
  `s1 = s0 k` by (
    simp[Abbr`s1`,Abbr`s0`,initial_state_def,compile_state_def] ) \\
  srw_tac[QI_ss][]
QED

(* more correctness properties *)

Theorem compile_contains_App_SOME:
   0 < max_app ⇒ ∀e. ¬contains_App_SOME max_app [compile e]
Proof
  strip_tac >>
  ho_match_mp_tac compile_ind >>
  simp[compile_def,contains_App_SOME_def,CopyByteStr_def,CopyByteAw8_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_App_SOME_def] >>
  TOP_CASE_TAC >> fs[contains_App_SOME_def] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  fs[contains_App_SOME_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem compile_every_Fn_vs_NONE:
   ∀e. every_Fn_vs_NONE[compile e]
Proof
  ho_match_mp_tac compile_ind >>
  rw[compile_def,CopyByteStr_def,CopyByteAw8_def] >>
  rw[Once every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_REVERSE,EVERY_MAP] >>
  fs[EVERY_MEM,REPLICATE_GENLIST,MEM_GENLIST] >>
  rw[] >> rw[] >>
  TOP_CASE_TAC >> fs[] >>
  rw[Once every_Fn_vs_NONE_EVERY,EVERY_MAP,GSYM MAP_REVERSE] >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem set_globals_eq:
   ∀e. set_globals e = set_globals (compile e)
Proof
  ho_match_mp_tac compile_ind >>
  rw[compile_def,patPropsTheory.op_gbag_def,op_gbag_def,elist_globals_reverse,CopyByteStr_def,CopyByteAw8_def]
  >>
    TRY
    (TRY(qpat_x_assum`LENGTH es ≠ A` kall_tac)>>
    TRY(qpat_x_assum`LENGTH es = A` kall_tac)>>
    Induct_on`es`>>fs[]>>NO_TAC)
  >> TRY
   (qmatch_goalsub_abbrev_tac `dest_WordToInt www` >>
    Cases_on `dest_WordToInt www es` >>
    qunabbrev_tac `www` >>
    fs [dest_WordToInt_SOME] >> rw [] >>
    fs[LENGTH_eq,op_gbag_def]>>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    TRY (EVAL_TAC \\ NO_TAC) >>
    fs [elist_globals_reverse] >>
    Induct_on`es`>>fs[] \\ EVAL_TAC)
  >>
    fs[LENGTH_eq,ETA_AX]>>
    TRY(pop_assum SUBST_ALL_TAC>>fs[bagTheory.COMM_BAG_UNION])>>
    Induct_on`n`>>fs[REPLICATE,op_gbag_def] >>
  Induct_on`es`>>fs[]
QED

Theorem compile_esgc_free:
   ∀e. esgc_free e ⇒ esgc_free (compile e)
Proof
  ho_match_mp_tac compile_ind >>
  rw[compile_def,CopyByteStr_def,CopyByteAw8_def] >>
  fs[EVERY_REVERSE,EVERY_MAP,EVERY_MEM]>>
  fs[set_globals_eq,LENGTH_eq,REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS]
  >> TRY
   (qmatch_goalsub_abbrev_tac `dest_WordToInt www` >>
    Cases_on `dest_WordToInt www es` >>
    qunabbrev_tac `www` >>
    fs [dest_WordToInt_SOME] >> rw [] >>
    fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
    fs [])
  >- (Induct_on`es`>>fs[set_globals_eq])
QED

Theorem compile_distinct_setglobals:
   ∀e. BAG_ALL_DISTINCT (set_globals e) ⇒
       BAG_ALL_DISTINCT (set_globals (compile e))
Proof
  fs[set_globals_eq]
QED

Theorem compile_no_Labels:
   !e. no_Labels (compile e)
Proof
  ho_match_mp_tac compile_ind \\ rw [compile_def]
  \\ fs [EVERY_REVERSE,EVERY_REPLICATE]
  \\ TRY (fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ NO_TAC)
  \\ every_case_tac \\ fs []
  \\ fs [EVERY_REVERSE,EVERY_REPLICATE]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
  \\ EVAL_TAC \\ fs []
QED

val _ = export_theory()
