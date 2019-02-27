(*
  Correctness proof for pat_to_clos
*)
open preamble intLib integerTheory backendPropsTheory
     semanticPrimitivesTheory
     patSemTheory patPropsTheory pat_to_closTheory
     closLangTheory closSemTheory closPropsTheory
(* TODO move *)
open bitstringTheory
open numposrepTheory;
open alist_treeTheory;
open logrootTheory;
open bitstring_extraTheory;

val _ = new_theory"pat_to_closProof"

val _ = set_grammar_ancestry
  ["patLang", "patSem", "patProps", "pat_to_clos",
   "closLang", "closSem", "closProps"];

(* value translation *)

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv (IntLit i)) = (Number i):closSem$v) ∧
  (compile_v (Litv (Word w)) = (Word w)) ∧
  (compile_v (Litv (Char c)) = (Word (bitstring$fixwidth 8 (bitstring$n2v (ORD c))))) ∧
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

Theorem compile_state_const[simp]
  `(compile_state max_app cc s).clock = s.clock ∧
   (compile_state max_app cc s).ffi = s.ffi ∧
   (compile_state max_app cc s).compile = cc ∧
   (compile_state max_app cc s).max_app = max_app ∧
   (compile_state max_app cc s).compile_oracle = pure_co (λe. (MAP compile e,[])) o s.compile_oracle`
  (EVAL_TAC);

Theorem compile_state_dec_clock[simp]
  `compile_state max_app cc (dec_clock y) = dec_clock 1 (compile_state max_app cc y)`
  (EVAL_TAC >> simp[])

Theorem compile_state_with_clock[simp]
  `compile_state max_app cc (s with clock := k) = compile_state max_app cc s with clock := k`
  (EVAL_TAC >> simp[])

Theorem compile_state_with_refs_const[simp]
  `(compile_state w cc (s with refs := r)).globals = (compile_state w cc s).globals ∧
   (compile_state w cc (s with refs := r)).code = (compile_state w cc s).code`
  (EVAL_TAC);

Theorem FLOOKUP_compile_state_refs
  `FLOOKUP (compile_state w cc s).refs =
   OPTION_MAP compile_sv o (combin$C store_lookup s.refs) `
  (rw[FUN_EQ_THM,compile_state_def,ALOOKUP_GENLIST,store_lookup_def] \\ rw[]);

Theorem FDOM_compile_state_refs[simp]
  `FDOM (compile_state w cc s).refs = count (LENGTH s.refs)`
  (rw[compile_state_def,MAP_GENLIST,o_DEF,LIST_TO_SET_GENLIST]);

Theorem compile_state_with_refs_snoc
  `compile_state w cc (s with refs := s.refs ++ [x]) =
   compile_state w cc s with refs :=
     (compile_state w cc s).refs |+ (LENGTH s.refs, compile_sv x)`
  (rw[compile_state_def,fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST]
  \\ rw[EL_APPEND1,EL_APPEND2]);

(* semantic functions respect translation *)

Theorem LENGTH_n2v
`!n. LENGTH (n2v n) = if n = 0 then 1 else SUC (LOG 2 n)`
(simp[n2v_def,num_to_bin_list_def,boolify_reverse_map] \\ rw[]
 \\ ASSUME_TAC (Q.SPEC `2` LENGTH_n2l) \\ fs[])

Theorem LENGTH_n2v_ORD
  `!c. LENGTH (n2v (ORD c)) <= 8`
 (Cases \\ simp[ORD_CHR]
  \\ simp[LENGTH_n2v]
  \\ TOP_CASE_TAC \\ simp[]
  \\ simp[GSYM LESS_EQ]
  \\ `8 = LOG 2 256` by EVAL_TAC
  \\ ASM_REWRITE_TAC[]
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ qexists_tac `LOG 2 255`
  \\ reverse CONJ_TAC
  >- EVAL_TAC
  \\ MATCH_MP_TAC (MP_CANON LOG_LE_MONO)
  \\ DECIDE_TAC
)

open bitTheory;

Theorem num_to_bin_list_eq
`!x y. num_to_bin_list x = num_to_bin_list y <=> x = y`
(rpt STRIP_TAC \\ reverse(EQ_TAC) >- rw[]
 \\ cheat)

Theorem EL_num_to_bin_list_not_SUC_SUC
 `!x n y. n < LENGTH (num_to_bin_list x) ==> ~(EL n (num_to_bin_list x) = SUC (SUC y))`
(Induct >- (EVAL_TAC \\ Cases \\ simp[]) \\ rw[EL_num_to_bin_list]
 \\ simp[BITV_def] \\ simp[BITS_THM]
 \\ rename1 `a MOD 2 = _`
 \\ `a MOD 2 = 0 \/ a MOD 2 = 1` by (Cases_on `a MOD 2` \\ fs[] \\ rename1 `b = 0` \\ Cases_on `b` \\ fs[]
     \\ `a MOD 2 < 2` by (MATCH_MP_TAC MOD_LESS \\ simp[])
     \\ DECIDE_TAC)
 \\ fs[]
)

Theorem LIST_REL_bin_list_eq `LIST_REL (λn n'. n = 0 ⇔ n' = 0) (num_to_bin_list x)
           (num_to_bin_list y) = LIST_REL (λn n'. n = n') (num_to_bin_list x)
           (num_to_bin_list y)`
(rw[LIST_REL_EL_EQN] \\ EQ_TAC \\ rw[] \\
`n < LENGTH (num_to_bin_list x)` by fs[] \\ RES_TAC
 \\ Cases_on `EL n (num_to_bin_list x)` \\ fs[]
 \\ Cases_on `EL n (num_to_bin_list y)` \\ fs[]
 \\ rename1 `a=b` \\ Cases_on `a` \\ Cases_on `b` \\ fs[]
 \\ metis_tac[EL_num_to_bin_list_not_SUC_SUC])


Theorem MAP_num_to_bin_list_eq `!x y. MAP (λn. n ≠ 0) (num_to_bin_list x) =
    MAP (λn. n ≠ 0) (num_to_bin_list y) <=> num_to_bin_list x = num_to_bin_list y`
(rpt STRIP_TAC \\ EQ_TAC \\ rw[] \\ fs[MAP_EQ_EVERY2]
\\ simp[LIST_EQ_REWRITE] \\ fs[LIST_REL_bin_list_eq]
\\ fs[LIST_REL_EL_EQN]
)

Theorem n2v_eq
`!x y. n2v x = n2v y <=> x = y`
(rpt STRIP_TAC \\ EQ_TAC \\ STRIP_TAC \\ fs[n2v_def]
 \\ fs[boolify_reverse_map]
 \\ fs[num_to_bin_list_eq,MAP_num_to_bin_list_eq])


Theorem do_eq
  `(∀v1 v2. do_eq v1 v2 ≠ Eq_type_error ⇒
      (do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2))) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 ≠ Eq_type_error ⇒
      (do_eq_list vs1 vs2 = do_eq_list (MAP compile_v vs1) (MAP compile_v vs2)))`
  (ho_match_mp_tac patSemTheory.do_eq_ind >>
  simp[patSemTheory.do_eq_def,closSemTheory.do_eq_def] >>
  conj_tac >- (
    reverse(Cases >> Cases >> simp[lit_same_type_def,closSemTheory.do_eq_def])
    >- (rw[LIST_EQ_REWRITE,EL_MAP,EQ_IMP_THM] \\ rfs[EL_MAP] \\ res_tac
    \\ fs[ORD_11,ORD_BOUND])
    \\ EQ_TAC \\ rw[]
    \\ rename1 `c=c'` \\ Cases_on `c` \\ Cases_on `c'`
    \\ `ORD (CHR n) = n` by fsrw_tac[][ORD_CHR]
    \\ `ORD (CHR n') = n'` by fsrw_tac[][ORD_CHR]
    \\ fs[]
    \\ `fixwidth 8 (n2v n) = fixwidth 8 (n2v n') <=> n2v n = n2v n'` by cheat
    \\ fs[n2v_eq]
  ) >>
  conj_tac >- rw[ETA_AX] >>
  conj_tac >- rw[ETA_AX] >>
  rw[] >>
  Cases_on`v1`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  Cases_on`v2`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  fs[closSemTheory.do_eq_def,patSemTheory.do_eq_def,lit_same_type_def,ORD_11] >>
  rw[]>>fs[]>>rfs[ETA_AX]>>
  BasicProvers.CASE_TAC>>fs[]>>
  rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]);

val v_to_list_def = closSemTheory.v_to_list_def;

Theorem v_to_char_list
  `∀v ls. (v_to_char_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP (Word o fixwidth 8 o n2v o ORD) ls))`
  (ho_match_mp_tac v_to_char_list_ind >>
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
  Cases_on`v_to_char_list h`>>fs[]>> rw[])

Theorem v_to_list
  `∀v ls. (v_to_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP compile_v ls))`
  (ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def,v_to_list_def] >>
  rw[] >> Cases_on`v_to_list v`>>fs[]>> rw[])

Theorem vs_to_string
  `∀vs ws. vs_to_string vs = SOME ws ⇒
    ∃wss. MAP compile_v vs = MAP ByteVector wss ∧
      FLAT wss = MAP (n2w o ORD) ws`
  (ho_match_mp_tac vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ qmatch_goalsub_abbrev_tac`ByteVector ws1`
  \\ qexists_tac`ws1::wss` \\ simp[]);

Theorem Boolv[simp]
  `compile_v (Boolv b) = Boolv b`
  (Cases_on`b`>>EVAL_TAC)

(* TODO fix definitions of v_to_bytes and v_to_words *)

Theorem MAP_Word_w2v_eq:
  MAP (\x. Word (w2v x)) ls = MAP (\x. Word (w2v x)) x <=> ls = x
Proof
  EQ_TAC \\ STRIP_TAC \\ fs[]
  \\ imp_res_tac INJ_MAP_EQ
  \\ POP_ASSUM MATCH_MP_TAC
  \\ rw[]
  \\ simp[INJ_DEF,bitstring_extraTheory.w2v_eq]
QED

Theorem v_to_bytes:
  v_to_bytes v = SOME ls ==> v_to_bytes (compile_v v) = SOME ls
Proof
  simp[patSemTheory.v_to_bytes_def,v_to_bytes_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ imp_res_tac v_to_list
  \\ rw[MAP_MAP_o,o_DEF]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ fs[MAP_Word_w2v_eq]
QED

Theorem v_to_words:
  v_to_words v = SOME ls ==> v_to_words (compile_v v) = SOME ls
Proof
  simp[patSemTheory.v_to_words_def,v_to_words_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ imp_res_tac v_to_list
  \\ rw[MAP_MAP_o,o_DEF]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ fs[MAP_Word_w2v_eq]
QED

Theorem do_install
  `patSem$do_install vs s = SOME (v1,v2) ∧
   s.compile = pure_cc (λe. (MAP compile e,[])) cc
   ==>
   closSem$do_install (MAP compile_v vs) (compile_state max_app cc s) =
     if s.clock = 0 then (Rerr (Rabort Rtimeout_error),compile_state max_app cc v2)
     else (Rval (MAP compile v1),dec_clock 1(compile_state max_app cc v2))`
  (simp[do_install_def,patSemTheory.do_install_def,case_eq_thms]
  \\ simp[] \\ strip_tac \\ rveq \\ fs[]
  \\ imp_res_tac v_to_bytes \\ imp_res_tac v_to_words
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[pure_co_def] \\ rveq
  \\ rfs[pure_cc_def]
  \\ fs[case_eq_thms,pair_case_eq,shift_seq_def,FUPDATE_LIST_THM] \\ rveq
  \\ fs[bool_case_eq,dec_clock_def]
  \\ fs[state_component_equality,compile_state_def,pure_co_def,FUN_EQ_THM]);

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

Theorem list_to_v_compile
  `!x xs.
   v_to_list x = SOME xs /\
   v_to_list (compile_v x) = SOME (MAP compile_v xs) ==>
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs)`
  (ho_match_mp_tac patSemTheory.v_to_list_ind
  \\ rw [patSemTheory.v_to_list_def] \\ fs []
  \\ fs [list_to_v_def, patSemTheory.list_to_v_def, case_eq_thms] \\ rveq
  \\ fs [v_to_list_def, case_eq_thms, list_to_v_def, patSemTheory.list_to_v_def]);

Theorem list_to_v_compile_APPEND
  `!xs ys.
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs) /\
     list_to_v (MAP compile_v ys) = compile_v (list_to_v ys) ==>
       list_to_v (MAP compile_v (xs ++ ys)) =
       compile_v (list_to_v (xs ++ ys))`
  (Induct \\ rw [patSemTheory.list_to_v_def]
  \\ fs [list_to_v_def, patSemTheory.list_to_v_def]);

Theorem dest_WordToInt_SOME
  `!wdx es x w. dest_WordToInt wdx es = SOME (x,w) ==> ?tra. es = [App tra (Op (WordToInt w)) [x]]`
  ( ho_match_mp_tac dest_WordToInt_ind >> fs[dest_WordToInt_def]
    >> Cases_on `op` \\ fs[]
    >> Cases_on `o'` \\ TRY(fs[] \\ NO_TAC)
  );

val Rabort_Rtype_error_map_error = prove(
  ``Rabort Rtype_error = map_error_result compile_v e <=>
    e = Rabort Rtype_error``,
  Cases_on `e` \\ fs [] \\ eq_tac \\ rw []);

val do_app_WordToInt_Rerr_IMP = prove(
  ``closSem$do_app (WordToInt n) ws x = Rerr e ==> e = Rabort Rtype_error``,
  fs [do_app_def,case_eq_thms,pair_case_eq] \\ rw [] \\ fs []);

(* TODO prove and move *)
val lem = Q.prove(`!t. EVERY ($= 0 ∘ combin$C $MOD 2)
           (REVERSE (MAP (λb. if b then 1 else 0) t)) ==> EVERY ($= F) t`,
     simp[EVERY_REVERSE,EVERY_MAP] \\ Induct \\ fs[])

val GENLIST_K_REVERSE_SUC = Q.prove(`!x y. GENLIST (K x) (SUC y) = [x] ++ GENLIST (K x) y`,
  rw[LIST_EQ_REWRITE] \\ rename1 `EL i _` \\ Cases_on `i` \\ simp[EL]
)

val GENLIST_K_REVERSE_SUC_CONS = Q.prove(`!x y. GENLIST (K x) (SUC y) = x::GENLIST (K x) y`,
  rw[LIST_EQ_REWRITE] \\ rename1 `EL i _` \\ Cases_on `i` \\ simp[EL]
)


val GENLIST_K_REVERSE_APPEND = Q.prove(`!x y. GENLIST (K x) y ++ [x] = GENLIST (K x) (SUC y)`,
  rw[LIST_EQ_REWRITE] \\ rename1 `EL i _` \\ Cases_on `i`
  >- (simp[HD_APPEND] \\ TOP_CASE_TAC \\ Induct_on `y` >- EVAL_TAC
      \\ Cases_on `y` \\ fs[] \\ simp[GSYM EL])
  \\ simp[EL_APPEND_EQN] \\ TOP_CASE_TAC \\ simp[]
  \\ `SUC n - y = 0` by DECIDE_TAC \\ ASM_REWRITE_TAC[] \\ simp[]
)



val EVERY_EQ_GENLIST = Q.prove(`!l x. EVERY ($= x) l = (l = GENLIST (K x) (LENGTH l))`,
     Induct \\ fs[] \\ rpt STRIP_TAC \\ EQ_TAC \\ rw[] \\ fs[GENLIST_K_REVERSE_SUC]
)

val LENGTH_zero_extend = Q.prove(`LENGTH (zero_extend n v) = MAX (LENGTH v) n`,
  simp[zero_extend_def,PAD_LEFT] \\ simp[MAX_DEF]
)


val PRE_SUB_PRE = Q.prove(`!x y. ~(y=0) ==> PRE x - PRE y = x - y`,
  rpt (Induct) >- simp[] >- fs[] >- simp[] \\ fs[]
)


Theorem length_zero_extend2
  `!x n. LENGTH (zero_extend n x) = MAX n (LENGTH x)`
(rw[zero_extend_def,PAD_LEFT] \\ simp[MAX_DEF])

val GENLIST_K_EVERY = Q.prove(`!x y. (y = GENLIST (K x) (LENGTH y)) = EVERY ($=x) y`,
 simp[EVERY_EQ_GENLIST]
)

val v2n_eq0 = Q.prove(`!x. (v2n x = 0) <=> (x = GENLIST (K F) (LENGTH x))`,
 simp[v2n_def,bitify_reverse_map,num_from_bin_list_def,l2n_eq_0,EVERY_REVERSE,EVERY_MAP]
 \\ simp[GENLIST_K_EVERY] \\ STRIP_TAC \\ rpt (MK_COMB_TAC \\ simp[]) \\ srw_tac[][FUN_EQ_THM]
 \\ TOP_CASE_TAC \\ EVAL_TAC
)


val TAKE_ID = prove(
  ``∀l n. (LENGTH l = n) ⇒ (TAKE n l = l)``,
Induct THEN SRW_TAC [ARITH_ss][]);


Theorem l2n_2_append
 `!y x. l2n 2 (x ++ y) = l2n 2 x + (2**LENGTH x) * (l2n 2 y)`
  (INDUCT_THEN list_INDUCT ASSUME_TAC \\ fs[] \\ STRIP_TAC \\ INDUCT_THEN list_INDUCT ASSUME_TAC \\ fs[]
  \\ rw[] \\ simp[Once l2n_def] \\ ONCE_REWRITE_TAC[ADD_SYM] \\ simp[EXP] \\ simp[LEFT_ADD_DISTRIB]
  \\ simp[l2n_def])


val l2n_GENLIST_0 = prove(``!n. l2n 2 (GENLIST (\v. 0) n) = 0``,
  ASSUME_TAC (Q.SPEC `2` l2n_eq_0) \\ fs[EVERY_GENLIST]
)

(* get an alternative version of zero extend with strict inquality the other way *)
val v2n_fixwidth_n2v_ORD = Q.prove(`!c. v2n (fixwidth 8 (n2v (ORD c))) = ORD c`, 
   lrw [n2v_def, v2n_def, bitify_def, num_from_bin_list_def, l2n_def,
       num_to_bin_list_def, bitify_reverse_map, boolify_reverse_map,
       rich_listTheory.MAP_REVERSE, listTheory.MAP_MAP_o,
numposrepTheory.n2l_BOUND, numposrepTheory.l2n_n2l,ORD_BOUND,fixwidth_def
         ,zero_extend_def,PAD_LEFT,MAP_GENLIST,REVERSE_APPEND,REVERSE_GENLIST,MAP_DROP,REVERSE_DROP
         , MAP_REVERSE, MAP_MAP_o,o_DEF]
  >- (simp[l2n_2_append,l2n_GENLIST_0] \\ fs[]
      \\ Q.MATCH_ABBREV_TAC `l2n 2 X = _`
  \\ `X = n2l 2 (ORD c)` by (UNABBREV_ALL_TAC \\ cheat)
  \\ fs[] \\ MATCH_MP_TAC l2n_n2l \\ simp[]
)
  \\ simp[LASTN_def,GSYM MAP_TAKE]
  \\ `LENGTH (n2l 2 (ORD c)) = 8` by cheat
  \\ srw_tac[][TAKE_ID]
  \\ Q.MATCH_ABBREV_TAC `l2n 2 X = _`
  \\ `X = n2l 2 (ORD c)` by (UNABBREV_ALL_TAC \\ cheat)
  \\ fs[]
  \\ MATCH_MP_TAC l2n_n2l \\ simp[]
)

Theorem EVERY_MOD_EQUAL_LESS_EQUIV_EQUAL
  `!l. (EVERY ($>2) l /\ EVERY ($=0 o combin$C $MOD 2) l) = EVERY ($=0) l`
  (INDUCT_THEN list_INDUCT ASSUME_TAC \\ rw[EVERY_DEF] \\ EQ_TAC \\ rw[] \\ fs[])

Theorem n2v_v2n_LENGTH_sub
  `!h t. LENGTH (n2v (v2n (h::t))) - LENGTH (h::t) = 0`
 (rw[] \\ simp[n2v_def,v2n_def,boolify_reverse_map,bitify_reverse_map,num_to_bin_list_def,num_from_bin_list_def]
  \\ simp[l2n_2_append] \\ Cases_on `h` \\ fs[] \\ `1<2` by simp[]
  \\ ASM_SIMP_TAC arith_ss [LENGTH_n2l]
  >- (ONCE_REWRITE_TAC[ADD_COMM]
      \\ `LOG 2 (l2n 2 (REVERSE (MAP (λb. if b then 1 else 0) t)) + 2 ** LENGTH t) = LENGTH t` by
        (MATCH_MP_TAC LOG_ADD \\ fs[] \\ `LENGTH t = LENGTH (REVERSE (MAP (λb. if b then 1 else 0) t))` by simp[LENGTH_REVERSE,LENGTH_MAP]
         \\ ONCE_ASM_REWRITE_TAC[]
         \\ `0<2` by fs[]
         \\ ASSUME_TAC l2n_lt
         \\ (POP_ASSUM (ASSUME_TAC o Q.SPECL[`(REVERSE (MAP (λb. if b then 1 else 0) t))`,`2`])) \\ fs[]
        )
      \\ fs[])
  \\ `0<2` by fs[]
  \\ ASM_SIMP_TAC arith_ss [l2n_eq_0]
  \\ simp[EVERY_REVERSE]
  \\ TOP_CASE_TAC \\ fs[]
  \\ `LOG 2 (l2n 2 (REVERSE (MAP (λb. if b then 1 else 0) t))) = PRE (LENGTH (dropWhile ($= 0) (REVERSE (REVERSE (MAP (λb. if b then 1 else 0) t)))))` by
     (cheat)
  \\ fs[] \\ `LENGTH (dropWhile ($= 0) (MAP (λb. if b then 1 else 0) t)) <= LENGTH (MAP (λb. if b then 1 else 0) t)` by simp[LENGTH_dropWhile_LESS_EQ]
  \\ fs[LENGTH_MAP])

Theorem DROP_n2v_v2n_sub
  `!h t. DROP (LENGTH (n2v (v2n (h::t))) - LENGTH (h::t)) (n2v (v2n (h::t)))
   = n2v (v2n (h::t))`
(rpt STRIP_TAC
 \\ ASM_SIMP_TAC arith_ss [DROP,n2v_v2n_LENGTH_sub])

(* TODO cleaner idea - prove that v2n (h::t) = v2n (non-zero prepended suffix of h::t) *)
Theorem zero_extend_n2v_v2n_cons
  `!h t. zero_extend (SUC (LENGTH t)) (n2v (v2n (h::t))) = h::t`
(rw[] \\ simp[zero_extend_def,PAD_LEFT,n2v_def,v2n_def,boolify_reverse_map,bitify_reverse_map,num_to_bin_list_def,num_from_bin_list_def]
 \\ ASM_SIMP_TAC arith_ss [LENGTH_n2l] \\ TOP_CASE_TAC \\ fs[] >-
    (fs[l2n_eq_0] \\ simp[GENLIST_K_REVERSE_APPEND] \\ simp[GENLIST_K_REVERSE_SUC]
     \\ Cases_on `h` \\ fs[] \\ fs[EVERY_REVERSE,EVERY_MAP] \\ cheat)
 \\ Q.MATCH_ABBREV_TAC `_ ++ (REVERSE (MAP _ (n2l 2 (l2n 2 P)))) = _`
 \\ `EVERY ($> 2) P` by (UNABBREV_ALL_TAC \\ simp[EVERY_REVERSE,EVERY_MAP]
                         \\ rw[] \\ rpt (POP_ASSUM (K ALL_TAC))
                         \\ Induct_on `t` \\ rw[EVERY_DEF])
 \\ ASM_SIMP_TAC arith_ss [n2l_l2n]
 \\ fs[l2n_eq_0,o_DEF]
 \\ ASSUME_TAC (Q.SPEC `2` LOG_l2n)
 \\ fs[]
 \\ Cases_on `h` \\ fs[]
 \\ UNABBREV_ALL_TAC
 >- (simp[MAP_TAKE,MAP_REVERSE,MAP_MAP_o,o_DEF,REVERSE_APPEND]
     \\ simp[TAKE_APPEND,GSYM MAP_REVERSE,GSYM MAP_TAKE]
     \\ simp[GSYM ADD1] >>
     `LENGTH (REVERSE t) <= SUC (LENGTH t)` by simp[] \\
      IMP_RES_TAC TAKE_LENGTH_TOO_LONG \\ fs[]
      \\ Q.MATCH_ABBREV_TAC `MAP f _ = _`
      \\ `f = I` by (UNABBREV_ALL_TAC \\ simp[I_DEF,S_DEF,K_DEF] \\ ABS_TAC \\ TOP_CASE_TAC \\ simp[])
      \\ fs[])
 \\ simp[l2n_2_append]
 \\ Induct_on `t` \\ rw[TAKE_APPEND,MAP_REVERSE,GSYM ADD1]
 >- (`LENGTH (REVERSE t) <= SUC (LENGTH t)` by simp[] \\ ASM_SIMP_TAC arith_ss [TAKE_LENGTH_TOO_LONG]
     \\ simp[REVERSE_REVERSE,MAP_REVERSE] \\ simp[MAP_TAKE,MAP_REVERSE,MAP_MAP_o,o_DEF]
     \\ cheat)
 \\ ASSUME_TAC (Q.SPEC `2` l2n_SNOC_0)
 \\ fs[]
 \\ ONCE_ASM_REWRITE_TAC[GSYM SNOC_APPEND]
 \\ ntac 3 (POP_ASSUM (K ALL_TAC))
 \\ POP_ASSUM (ASSUME_TAC o GSYM)
 \\ fs[]
 \\ POP_ASSUM (K ALL_TAC)
 \\ rw[]
 \\ ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
 \\ ASSUME_TAC (Q.SPEC `2` l2n_SNOC_0)
 \\ fs[]
 \\ ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
 \\ ASM_SIMP_TAC (simpLib.empty_ss) []
 \\ simp[MAP_TAKE,MAP_REVERSE,MAP_MAP_o,o_DEF,REVERSE_APPEND]
 (* \\ `!x. F::x = [F] ++ x` by simp[]
 \\ ONCE_ASM_REWRITE_TAC[] *) \\ cheat
)


Theorem n2v_v2n_not_less_id
  `~(LENGTH (n2v (v2n (h::t))) < LENGTH (h::t)) ==> n2v (v2n (h::t)) = (h::t)`
(simp[LENGTH_n2v] \\ TOP_CASE_TAC
 >- (Cases_on `t` \\ fs[] \\ Cases_on `h` \\ EVAL_TAC \\ POP_ASSUM (fn a => ASSUME_TAC a \\ UNDISCH_TAC (concl a)) \\ EVAL_TAC)
 \\ Cases_on `h` \\ rw[v2n_def,n2v_def,num_from_bin_list_def,num_to_bin_list_def,bitify_reverse_map,boolify_reverse_map]
 \\ Q.MATCH_ABBREV_TAC `REVERSE (MAP _ (n2l 2 (l2n 2 X))) = _`
 \\ `EVERY ($> 2) X` by (UNABBREV_ALL_TAC \\ simp[EVERY_REVERSE,EVERY_MAP]
                         \\ Q.MATCH_ABBREV_TAC `EVERY X _`
                         \\ `X = K T` by (UNABBREV_ALL_TAC \\ simp[K_DEF] \\ ABS_TAC \\ TOP_CASE_TAC \\ simp[])
                         \\ fs[] \\ rpt (POP_ASSUM (K ALL_TAC))
                         \\ Induct_on `t` \\ simp[EVERY_DEF])
 \\ IMP_RES_TAC n2l_l2n
 \\ fs[]
 \\ UNABBREV_ALL_TAC
 \\ fs[l2n_eq_0]
 \\ simp[MAP_TAKE,MAP_REVERSE,MAP_MAP_o,o_DEF,REVERSE_APPEND]
 \\ ASSUME_TAC (Q.SPEC `2` LOG_l2n)
 \\ fs[]
 \\ `0 < LENGTH t + 1` by simp[]
 \\ `SUC (PRE (LENGTH t + 1)) = LENGTH t + 1` by metis_tac[SUC_PRE]
 \\ ASM_REWRITE_TAC[]
 >- (simp[TAKE_APPEND,GSYM MAP_REVERSE,GSYM MAP_TAKE] \\ `LENGTH (REVERSE t) <= LENGTH t + 1` by simp[] \\ ASM_SIMP_TAC arith_ss [TAKE_LENGTH_TOO_LONG,REVERSE_REVERSE]
     \\ fs[EVERY_REVERSE] \\ fs[EVERY_MAP] \\ rw[]
     \\ simp[MAP_EQ_ID]
     \\ rpt STRIP_TAC
     \\ TOP_CASE_TAC \\ fs[])
 \\ TOP_CASE_TAC \\ fs[]
 >- (rw[] \\ POP_ASSUM (fn a => ASSUME_TAC a \\ UNDISCH_TAC (concl a)) \\ ntac 4 (POP_ASSUM (K ALL_TAC))
     \\ rw[] \\ fs[v2n_def,num_from_bin_list_def,l2n_eq_0,o_DEF,bitify_reverse_map]
     \\ FULL_SIMP_TAC(simpLib.empty_ss)[EXISTS_NOT_EVERY] \\ metis_tac[])
 \\ simp[TAKE_APPEND] \\ simp[MAP_TAKE] \\ simp[MAP_REVERSE,MAP_MAP_o,o_DEF] \\ fs[EXISTS_REVERSE,EXISTS_MAP]
 \\ `SUC (LOG 2 (l2n 2 (REVERSE (MAP (λb. if b then 1 else 0) t) ++ [0]))) <= LENGTH t` by
   (simp[GSYM SNOC_APPEND] \\ simp[l2n_SNOC_0] \\
    Q.MATCH_ABBREV_TAC `SUC (LOG 2 (l2n 2 X)) <= _`
    \\ `LOG 2 (l2n 2 X) = PRE (LENGTH (dropWhile ($=0) (REVERSE X)))`
        by (MATCH_MP_TAC LOG_l2n_dropWhile \\ fs[] \\ UNABBREV_ALL_TAC
            \\ simp[EXISTS_REVERSE,EXISTS_MAP]
            \\ POP_ASSUM (fn a => ASSUME_TAC a \\ UNDISCH_TAC (concl a))
            \\ rpt(POP_ASSUM (K ALL_TAC))
            \\ `!x y. (x = y) ==> (x ==> y)` by simp[]
            \\ POP_ASSUM MATCH_MP_TAC
            \\ rpt (MK_COMB_TAC \\ simp[])
            \\ ABS_TAC \\ rw[])
    \\ fs[]
    \\ UNABBREV_ALL_TAC
    \\ simp[REVERSE_REVERSE]
    \\ Q.MATCH_ABBREV_TAC `SUC (PRE X) <= _`
    \\ Cases_on `0 < X` >-
        (fs[SUC_PRE] \\ UNABBREV_ALL_TAC \\ metis_tac[LENGTH_MAP,LENGTH_dropWhile_LESS_EQ])
    \\ reverse(Cases_on `X`) >- (POP_ASSUM (fn x => ASSUME_TAC x \\ UNDISCH_TAC (concl x)) \\ simp[])
    \\ simp[] \\ rename1 `1 <= LENGTH t` \\ Cases_on `t` \\ simp[]
    \\ fs[]
  )
 \\ IMP_RES_TAC TAKE_REVERSE \\ fs[])
;

Theorem MAP_Word
  `!x y. MAP Word x = MAP Word y <=> x = y`
 (rpt STRIP_TAC \\  MATCH_MP_TAC INJ_MAP_EQ_IFF \\ simp[INJ_DEF])
Theorem compile_evaluate
  `0 < max_app ⇒
   (∀env ^s es s' r.
      evaluate env s es = (s',r) ∧
      s.compile = pure_cc (λe. (MAP pat_to_clos$compile e,[])) cc ∧
      r ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate (MAP compile es,MAP compile_v env,compile_state max_app cc s) =
        (map_result (MAP compile_v) compile_v r, compile_state max_app cc s'))`
  (strip_tac >>
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
    TRY (rw[evaluate_def,do_app_def] >> rw[] >>
    simp[GSYM MAP_REVERSE,evaluate_MAP_Op_Const,combinTheory.o_DEF] \\ NO_TAC)
    \\ simp[compile_def]
   ) >>
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
      fs[evaluate_def,ETA_AX,MAP_REVERSE] >>
      TRY (
          rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
          rw[] >> fs[] >> qhdtm_x_assum`evaluate`mp_tac >>
          simp[Once evaluate_CONS] >>
          rw[case_eq_thms,pair_case_eq] >> rw[do_app_def] \\ NO_TAC)
      >> TRY (
        rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
        rw[] >> fs[] >>
        fs[do_app_def] \\ NO_TAC)
      >- (rw[] >> fs[do_app_def,LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE]
          \\ simp[Once evaluate_CONS] \\ rw[case_eq_thms,pair_case_eq]
          \\ simp[evaluate_def,do_app_def])
      >- (TOP_CASE_TAC
          >- fs[evaluate_def,do_app_def,ETA_AX,MAP_REVERSE]
          >> TOP_CASE_TAC
          >> IMP_RES_TAC dest_WordToInt_SOME
          >> simp[evaluate_def,do_app_def]
          \\ rw[dest_WordToInt_def]
          \\ fs[evaluate_def]
          \\ ntac 2 (TOP_CASE_TAC \\ fs[])
          \\ fs[do_app_def]
          \\ TOP_CASE_TAC \\ fs[]
          >- (TOP_CASE_TAC \\ fs[]
              >> rename1 `REVERSE b`
              >> Cases_on `REVERSE b` \\ fs[]
              >> rename1 `REVERSE b = h::t` \\ Cases_on `h` \\ fs[]
              \\ Cases_on `t` \\ fs[]
              \\ rename1 `fixwidth r l` \\ Cases_on `r = LENGTH l` \\ fs[]
              \\ rename1 `n = LENGTH l` \\ Cases_on `n = LENGTH l` \\ fs[]
              \\ fs[dest_WordToInt_def])
          >> rename1 `REVERSE b` \\ Cases_on `REVERSE b` \\ fs[]
          >> rename1 `REVERSE b = h::t` \\ Cases_on `h` \\ fs[]
          \\ Cases_on `t` \\ fs[]
          \\ rename1 `_ = SOME (q,r)`
          \\ fs[case_eq_thms,pair_case_eq])
    ) >>
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
    fs[patSemTheory.do_app_cases] >> rw[] >> TRY(
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
      Cases_on`op`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def,SWAP_REVERSE_SYM,MAP_REVERSE,opwb_lookup_def,blt_def,bgt_def,bleq_def,bgeq_def]
      \\ simp[v2n_fixwidth_n2v_ORD] \\ intLib.COOPER_TAC
      \\ NO_TAC) >>
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
      \\ simp[EL_MAP,ORD_BOUND] \\ NO_TAC) >>
    TRY (
      rename1`store_lookup`
      \\ fs[store_lookup_def,store_assign_def]
      \\ qmatch_assum_rename_tac`store_v_same_type (EL lnum t.refs) _`
      \\ Cases_on`EL lnum t.refs` \\ fs[store_v_same_type_def] \\ NO_TAC) >>
    TRY (
      rename1`do_word_cmp cmp wz' w1' w2'`
      \\ Cases_on `w1'` \\ Cases_on `w2'`
      \\ fs[opwb_lookup_def,semanticPrimitivesPropsTheory.do_word_cmp_def] \\ NO_TAC) >>
    TRY (
      rename1 `Litv w1`
      \\ Cases_on `w1` \\ fs [compile_v_def]
      \\ rename1 `do_shift sh n wl _`
      \\ Cases_on `wl` \\ fs [semanticPrimitivesPropsTheory.do_shift_def,shift_lookup_def]
      \\ qpat_x_assum `_ = w` (fn thm => rw [GSYM thm]) \\ NO_TAC) >>
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
      \\ rveq \\ fs [w2w_def] >> NO_TAC) >>
    TRY (fs[state_component_equality,compile_state_def,fmap_eq_flookup,
       ALOOKUP_GENLIST,FLOOKUP_UPDATE,store_assign_def,store_lookup_def,
       get_global_def, EL_MAP, IS_SOME_EXISTS,
       evaluate_REPLICATE_Op_AllocGlobal, REPLICATE_GENLIST, MAP_GENLIST]
    \\ rveq \\ simp[EL_LUPDATE] \\ rw[LUPDATE_def,map_replicate,LUPDATE_MAP]
    \\ simp[ETA_THM] \\ NO_TAC) >>
    TRY (fs[store_assign_def,store_lookup_def]
         \\ qmatch_assum_rename_tac`store_v_same_type (EL lnum t.refs) _`
         \\ Cases_on `EL lnum t.refs` \\ TRY (fs[store_v_same_type_def] \\ NO_TAC)
         \\ rw[]
         \\ fs[state_component_equality,compile_state_def,fmap_eq_flookup,
       ALOOKUP_GENLIST,FLOOKUP_UPDATE,store_assign_def,store_lookup_def,
       get_global_def, EL_MAP, IS_SOME_EXISTS,
evaluate_REPLICATE_Op_AllocGlobal, REPLICATE_GENLIST, MAP_GENLIST]
         \\ STRIP_TAC \\ BasicProvers.TOP_CASE_TAC
         >- (simp[LUPDATE_def] >> simp[EL_LUPDATE])
         >> BasicProvers.TOP_CASE_TAC
         >> simp[EL_LUPDATE] \\ NO_TAC) \\ NO_TAC)
    >- (simp[Once evaluate_def] \\ fs[MAP_REVERSE,ETA_AX]
        \\ simp[Once evaluate_def] \\ simp[Once evaluate_def] \\ simp[Once evaluate_def] \\ ntac 2 (simp[Once evaluate_def])
        \\ simp[do_app_def] \\ simp[Once evaluate_def] \\ `1 < LENGTH env + LENGTH vs` by fs[SWAP_REVERSE_SYM] \\ fs[]
        \\ simp[EL_APPEND_EQN] \\ `LENGTH vs = 2` by fs[SWAP_REVERSE_SYM] \\ fs[] \\ rename1 `REVERSE vs = [Litv (IntLit n'');Litv (Word w'')]`
        \\ `vs = [Litv (Word w'');Litv (IntLit n'')]` by fs[SWAP_REVERSE_SYM] \\ fs[] \\ simp[evaluate_def] \\ simp[do_app_def]
        \\ fs[int_arithTheory.not_less]
        \\ `0 <= n''` by intLib.ARITH_TAC
        \\ `?wv:word8. w'' = w2v wv` by (CCONTR_TAC \\ fs[] \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `v2w w''`) \\ fs[bitstringTheory.w2v_v2w]
                                   \\ POP_ASSUM (MP_TAC) \\ simp[])
        \\ fs[bitstring_extraTheory.w2v_eq]
        \\ rename1 `list_result v2 = _`
        \\ reverse (Cases_on `v2`)
        \\ simp[evaluateTheory.list_result_def]
        >- fs[store_alloc_def]
        \\ fs[store_alloc_def]
        \\ rveq
        \\ simp[compile_state_with_refs_snoc]
        \\ `ABS n'' = n''` by (Cases_on `n''` \\ fs[INT_ABS_NEG])
        \\ ASM_REWRITE_TAC[]
        \\ rename1 `(LEAST ptr. ¬(ptr < LENGTH s''.refs)) = LENGTH s''.refs`
        \\ `(LEAST ptr. ¬(ptr < LENGTH s''.refs)) = LENGTH s''.refs` by
           (DEEP_INTRO_TAC whileTheory.LEAST_ELIM \\ rw[] >- (Q.EXISTS_TAC `SUC (LENGTH s''.refs)` \\ fs[])
             >> fs[NOT_LESS] \\ intLib.COOPER_TAC)
        \\ fs[]
        )
    >- (simp[Once evaluate_def] \\ fs[MAP_REVERSE,ETA_AX]
        \\ simp[Once evaluate_def] \\ simp[Once evaluate_def] \\ simp[Once evaluate_def]
        \\ simp[Once evaluate_def] \\ simp[Once evaluate_def] \\ fs[do_app_def]
        \\ `1 < LENGTH env + LENGTH vs /\ 2 < LENGTH env + LENGTH vs` by fs[SWAP_REVERSE_SYM]
        \\ fs[]
        \\ fs[SWAP_REVERSE_SYM]
        \\ fs[FLOOKUP_compile_state_refs]
        \\ rename1 `0<=i' /\ i' < &(LENGTH ws)`
        \\ `0<=i' /\ i' < &(LENGTH ws)` by intLib.COOPER_TAC
        \\ fs[]
        \\ ntac 5 (simp[Once evaluate_def])
        \\ simp[Once do_app_def]
        \\ simp[Once evaluate_def]
        \\ ntac 2 (simp[Once evaluate_def])
        \\ simp[FLOOKUP_compile_state_refs]
        \\ simp[do_app_def]
        \\ simp[Once evaluate_def]
        \\ simp[state_component_equality]
        \\ simp[compile_state_def]
        \\ simp[fmap_eq_flookup]
        \\ simp[ALOOKUP_GENLIST,FLOOKUP_UPDATE]
        \\ STRIP_TAC \\ rpt (TOP_CASE_TAC \\ fs[store_lookup_def,store_assign_def])
        \\ rveq >> simp[LUPDATE_LENGTH,EL_LUPDATE] \\ rpt(MK_COMB_TAC \\ simp[])
       )
   >- (TOP_CASE_TAC \\ fs[]
        >- (simp[evaluate_def] \\ fs[MAP_REVERSE,ETA_AX]
            \\ TOP_CASE_TAC \\ fs[]
            >- (fs[do_app_def] \\ TOP_CASE_TAC \\ fs[])
            \\ fs[do_app_def])
        \\ TOP_CASE_TAC
        \\ IMP_RES_TAC dest_WordToInt_SOME
        \\ fs[]
        \\ fs[evaluate_def]
        \\ TOP_CASE_TAC \\ fs[]
        \\ TOP_CASE_TAC \\ fs[do_app_def]
        \\ rename1 `REVERSE a` \\ Cases_on `REVERSE a` \\ fs[]
        \\ rename1 `REVERSE a = h::t` \\ Cases_on `h` \\ fs[]
        \\ Cases_on `t` \\ fs[]
        \\ rename1 `i2vN i'' _`
        \\ fs[patSemTheory.evaluate_def]
        \\ fs[evaluate_def,patSemTheory.evaluate_def,do_app_def,case_eq_thms,pair_case_eq]
        \\ fs[dest_WordToInt_def]
        \\ `i'' = &v2n l` by fs[]
        \\ fs[]
        \\ simp[bitstring_extraTheory.i2vN_def]
        \\ fs[fixwidth_def]
        \\ reverse TOP_CASE_TAC
        >- (Cases_on `l` >- EVAL_TAC \\ simp[DROP_n2v_v2n_sub] \\ ASM_SIMP_TAC arith_ss [n2v_v2n_not_less_id])
        \\ Cases_on `l` \\ fs[] \\ simp[zero_extend_n2v_v2n_cons]
      )
   >- (simp[evaluate_def] \\ fs[MAP_REVERSE,ETA_AX] \\ simp[do_app_def] \\ simp[v2n_fixwidth_n2v_ORD])
   >- (fs[evaluate_def,do_app_def,MAP_REVERSE,ETA_AX] \\ rw[] >- COOPER_TAC
       \\ fs[] \\ rename1 `ABS i` \\ Cases_on `i` \\ fs[i2vN_def]
      )
   >- (fsrw_tac [ETA_ss] [evaluate_def, do_app_def, case_eq_thms,pair_case_eq, PULL_EXISTS, SWAP_REVERSE_SYM,MAP_REVERSE]
       \\ imp_res_tac v_to_char_list \\ fs[]
       \\ DEEP_INTRO_TAC some_intro \\ simp[]
       \\ ONCE_REWRITE_TAC[MAP_o] \\ simp[o_DEF] \\ rw[] \\ fs[MAP_Word] \\ rveq
       >- (simp[MAP_MAP_o,o_DEF]
       \\ `!v. (v2w (fixwidth 8 v)):word8 = v2w v` by (
            ASSUME_TAC(INST_TYPE [alpha |-> Type`:8`] v2w_fixwidth) \\ fs[])
       \\ fs[]
       \\ simp[INST[``s``|->``ls``] IMPLODE_EXPLODE_I])
       \\ simp[EVERY_MAP]
     )
   >- (fsrw_tac[ETA_ss,ARITH_ss][evaluate_def,do_app_def,case_eq_thms,pair_case_eq,PULL_EXISTS,SWAP_REVERSE_SYM,MAP_REVERSE]
       \\ rename1 `0 <= i'⁴' ∧ i'⁴' < &STRLEN str''`
       \\ `0 <= i'⁴' ∧ i'⁴' < &STRLEN str''` by intLib.COOPER_TAC
       \\ Cases_on `i''''` \\ (ASM_SIMP_TAC arith_ss [EL_MAP] \\ fs[])
       >- (fsrw_tac[ETA_ss,ARITH_ss][EL_MAP] \\ simp[w2v_n2w])
       \\ Cases_on `str''` >- fs[STRLEN_DEF] \\ simp[HD_MAP]
       \\ simp[w2v_n2w])
   >- (simp[Once evaluate_def] \\ fs[MAP_REVERSE,ETA_AX]
       \\ ntac 5 (simp[Once evaluate_def])
       \\ fs[do_app_def]
       \\ fs[]
       \\ fs[SWAP_REVERSE_SYM]
       \\ fs[FLOOKUP_compile_state_refs]
       \\ ntac 7 (simp[Once evaluate_def])
       \\ simp[do_app_def]
       \\ fs[FLOOKUP_compile_state_refs]
       \\ rename1 `0<=i' /\ i' < &(LENGTH ws)`
       \\ `0<=i' /\ i' < &(LENGTH ws)` by intLib.COOPER_TAC
       \\ fs[]
       \\ ntac 2 (simp[Once evaluate_def])
       \\ simp[do_app_def]
       \\ simp[compile_state_def]
       \\ simp[fmap_eq_flookup]
       \\ simp[ALOOKUP_GENLIST,FLOOKUP_UPDATE]
       \\ STRIP_TAC \\ rpt (TOP_CASE_TAC \\ fs[store_lookup_def,store_assign_def])
       \\ rveq >> simp[LUPDATE_LENGTH,EL_LUPDATE] \\ simp[LUPDATE_MAP]
       \\ rpt(MK_COMB_TAC \\ simp[])
   )) >>
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
    fsrw_tac[ETA_ss][]));

Theorem compile_semantics
  `0 < max_app ∧ st.compile = pure_cc (λe. (MAP compile e,[])) cc ∧ st.globals = [] ∧ st.refs = [] ⇒
   semantics [] (st:('c,'ffi)patSem$state) es ≠ Fail ⇒
   semantics st.ffi max_app FEMPTY (pure_co (λe. (MAP compile e,[])) o st.compile_oracle) cc (MAP compile es) =
   semantics [] st es`
  (strip_tac >>
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
  srw_tac[QI_ss][]);

(* more correctness properties *)

Theorem compile_contains_App_SOME
  `0 < max_app ⇒ ∀e. ¬contains_App_SOME max_app [compile e]`
  (strip_tac >>
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
  fs[contains_App_SOME_def,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rename1 `dest_WordToInt n es = SOME x` >> Cases_on `x` >>
  IMP_RES_TAC dest_WordToInt_SOME
  >> rename1 `_ = [App tra' (Op (WordToInt r)) [q]]`
  >> Cases_on `(q,r)` >> fs[]
  >> fs[contains_App_SOME_def]
);

Theorem compile_every_Fn_vs_NONE
  `∀e. every_Fn_vs_NONE[compile e]`
  (ho_match_mp_tac compile_ind >>
  rw[compile_def,CopyByteStr_def,CopyByteAw8_def] >>
  rw[Once every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_REVERSE,EVERY_MAP] >>
  fs[EVERY_MEM,REPLICATE_GENLIST,MEM_GENLIST] >>
  rw[] >> rw[] >>
  TOP_CASE_TAC >> fs[] >>
  rw[Once every_Fn_vs_NONE_EVERY,EVERY_MAP,GSYM MAP_REVERSE] >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  TOP_CASE_TAC
  >> IMP_RES_TAC dest_WordToInt_SOME
  >> rw[Once every_Fn_vs_NONE_EVERY]
);

(* TODO cleanup *)
Theorem set_globals_eq
  `∀e. set_globals e = set_globals (compile e)`
  (ho_match_mp_tac compile_ind >>
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
    Induct_on`es`>>fs[] \\ EVAL_TAC \\ NO_TAC)
  >>
   TRY (fs[LENGTH_eq,ETA_AX]>>
    TRY(pop_assum SUBST_ALL_TAC>>fs[bagTheory.COMM_BAG_UNION])>>
    Induct_on`n`>>fs[REPLICATE,op_gbag_def] >>
  Induct_on`es`>>fs[] \\ NO_TAC)
  >> TRY
   (qmatch_goalsub_abbrev_tac `dest_WordToInt www` >>
    Cases_on `dest_WordToInt www es` >>
    qunabbrev_tac `www` \\ fs[]
    >> rw[]  >> fs[LENGTH_eq,op_gbag_def]
    >> TRY (    fs [dest_WordToInt_SOME] >> rw [] >>
    fs[LENGTH_eq,op_gbag_def]>>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    TRY (EVAL_TAC \\ NO_TAC) >>
    fs [elist_globals_reverse] >>
    Induct_on`es`>>fs[] \\ EVAL_TAC \\ NO_TAC)
    >> BasicProvers.TOP_CASE_TAC
    >> IMP_RES_TAC dest_WordToInt_SOME
    >> fs[]
    >> fs[LENGTH_eq,op_gbag_def]>>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    TRY (EVAL_TAC \\ NO_TAC) >>
    fs [elist_globals_reverse] >> NO_TAC))
;

Theorem compile_esgc_free
  `∀e. esgc_free e ⇒ esgc_free (compile e)`
  (ho_match_mp_tac compile_ind >>
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
  >- (rename1 `_ = SOME x` >> Cases_on `x` >> IMP_RES_TAC dest_WordToInt_SOME
      >> fs[])
  >- (Induct_on`es`>>fs[set_globals_eq]));

Theorem compile_distinct_setglobals
  `∀e. BAG_ALL_DISTINCT (set_globals e) ⇒
       BAG_ALL_DISTINCT (set_globals (compile e))`
  (fs[set_globals_eq]);

Theorem compile_no_Labels
  `!e. no_Labels (compile e)`
  (ho_match_mp_tac compile_ind \\ rw [compile_def]
  \\ fs [EVERY_REVERSE,EVERY_REPLICATE]
  \\ TRY (fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ NO_TAC)
  \\ every_case_tac \\ fs []
  \\ fs [EVERY_REVERSE,EVERY_REPLICATE]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
  \\ EVAL_TAC \\ fs []);

val _ = export_theory()
