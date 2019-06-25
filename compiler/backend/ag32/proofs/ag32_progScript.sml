(*
  Defines an ag32 instantiation of the machine-code Hoare triple for
  the decompiler.
*)
open preamble
open set_sepTheory progTheory ag32Theory temporal_stateTheory

val () = new_theory "ag32_prog"

val v2w_F_T = store_thm("v2w_F_T", (* TODO: move *)
  ``(v2w [F] = 0w) /\ (v2w [T] = 1w)``,
  fs [bitstringTheory.v2w_def,bitstringTheory.testbit_def,
      bitstringTheory.field_def,bitstringTheory.fixwidth_def]
  \\ fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_0]
  \\ fs [bitstringTheory.zero_extend_def,word_index]
  \\ rw [bitstringTheory.shiftr_def]
  \\ Cases_on `i` \\ fs [ADD1,DECIDE ``1-(n+1n) = 0``] \\ EVAL_TAC);

(* basic definitions *)

val _ = Datatype `
  ag32_el = aState ag32_state
          | aMem word32 word8
          | aPc word32`;

val ag32_el_11 = DB.fetch "-" "ag32_el_11";
val ag32_el_distinct = DB.fetch "-" "ag32_el_distinct";

val _ = Parse.type_abbrev("ag32_set",``:ag32_el set``);

val ag32_instr_def = Define`
  ag32_instr (a, w: word32) =
  { aMem (a+3w) ((31 >< 24) w) ;
    aMem (a+2w) ((23 >< 16) w) ;
    aMem (a+1w) ((15 ><  8) w) ;
    aMem (a+0w) (( 7 ><  0) w) }`;

val ag32_proj'_def = Define `
  ag32_proj' (fs,ms,pc) (s:ag32_state) =
    (if fs then { aState s } else {}) UNION
    IMAGE (\a. aMem a (s.MEM a)) ms UNION
    (if pc then { aPc (s.PC) } else {})`;

val ag32_proj_def   = Define `ag32_proj s = ag32_proj' (T,UNIV,T) s`;
val ag32_proj''_def = Define `ag32_proj'' x s = ag32_proj s DIFF ag32_proj' x s`;

val AG32_MODEL_def = Define`
   AG32_MODEL = (ag32_proj, (\x y. y = Next x), ag32_instr, (=), K F)
                :(ag32_state, ag32_el, word32 # word32) processor`

val aP_def = Define `aP x = SEP_EQ {aPc x}`;
val aM_def = Define `aM a x = SEP_EQ {aMem a x}`;
val aS_def = Define `aS x = SEP_EQ {aState x}`;
val aB_def = Define `aB md m = SEP_EQ { aMem a (m a) | a IN md }`;

val aD_def = Define `aD md = SEP_EXISTS m. aB md m`;
val aPC_def = Define `aPC x = aP x * cond (aligned 2 x)`;

(* lemmas about proj *)

val ag32_proj'_SUBSET_ag32_proj = prove(
  ``!y s. ag32_proj' y s SUBSET ag32_proj s``,
  strip_tac \\ PairCases_on `y`
  \\ rw [ag32_proj_def,ag32_proj'_def,SUBSET_DEF]);

val SPLIT_ag32_proj = prove(
  ``!x s. SPLIT (ag32_proj s) (ag32_proj' x s, ag32_proj'' x s)``,
  rpt strip_tac
  \\ `ag32_proj' x s SUBSET ag32_proj s` by metis_tac [ag32_proj'_SUBSET_ag32_proj]
  \\ simp [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,ag32_proj''_def]
  \\ simp [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ metis_tac [SUBSET_DEF]);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. (x IN (if g then y else z)) = if g then x IN y else x IN z``;

val SUBSET_ag32_proj = prove(
  ``!u s. u SUBSET ag32_proj s <=> ?y. u = ag32_proj' y s``,
  rw [] \\ eq_tac \\ rw [] \\ rw [ag32_proj'_SUBSET_ag32_proj]
  \\ qexists_tac `((?y. aState y IN u),
                   { a | a| ?x. aMem a x IN u },(?y. aPc y IN u))`
  \\ fs [ag32_proj'_def,ag32_proj_def,EXTENSION,SUBSET_DEF,PUSH_IN_INTO_IF]
  \\ rw [] \\ eq_tac \\ rw [] THEN1 metis_tac []
  \\ res_tac \\ fs []);

val SPLIT_ag32_proj_EXISTS = prove(
  ``!s u v. SPLIT (ag32_proj s) (u,v) =
            ?y. (u = ag32_proj' y s) /\ (v = ag32_proj'' y s)``,
  rpt strip_tac \\ eq_tac \\ rpt strip_tac \\ asm_rewrite_tac [SPLIT_ag32_proj]
  \\ fs [SPLIT_def,ag32_proj'_def,ag32_proj''_def]
  \\ `u SUBSET (ag32_proj s)` by
       (full_simp_tac std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ metis_tac [])
  \\ fs [SUBSET_ag32_proj] \\ qexists_tac `y` \\ rewrite_tac []
  \\ fs [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ metis_tac []);

val IN_ag32_proj = prove(``
  (!x s. aPc x IN (ag32_proj s) <=> (x = s.PC)) /\
  (!x s. aPc x IN (ag32_proj' (fs,ms,pc) s) <=> (x = s.PC) /\ pc) /\
  (!x s. aPc x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = s.PC) /\ ~pc) /\
  (!x s. aState x IN (ag32_proj s) <=> (x = s)) /\
  (!x s. aState x IN (ag32_proj' (fs,ms,pc) s) <=> (x = s) /\ fs) /\
  (!x s. aState x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = s) /\ ~fs) /\
  (!p x s. aMem p x IN (ag32_proj s) <=> (x = s.MEM p)) /\
  (!p x s. aMem p x IN (ag32_proj' (fs,ms,pc) s) <=> (x = s.MEM p) /\ p IN ms) /\
  (!p x s. aMem p x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = s.MEM p) /\ ~(p IN ms))``,
  rw [ag32_proj'_def,ag32_proj''_def,ag32_proj_def] \\ metis_tac []);

val ag32_proj''_11 = prove(
  ``!y y' s s'. (ag32_proj'' y' s' = ag32_proj'' y s) ==> (y = y')``,
  rpt strip_tac \\ CCONTR_TAC
  \\ rename [`x <> y`]
  \\ PairCases_on `x`
  \\ PairCases_on `y`
  \\ full_simp_tac bool_ss [PAIR_EQ]
  THEN1
   (`~((?x. aState x IN ag32_proj'' (x0,x1,x2) s) =
       (?x. aState x IN ag32_proj'' (y0,y1,y2) s'))` by
      (Q.PAT_X_ASSUM `ag32_proj'' _ _ = ag32_proj'' _ _` (K ALL_TAC)
       \\ full_simp_tac bool_ss [IN_ag32_proj] \\ metis_tac [])
    \\ fs [EXTENSION] \\ metis_tac [])
  THEN1
   (`?a. (a IN y1) <> (a IN x1)` by metis_tac [EXTENSION]
    \\ `~((?x. aMem a x IN ag32_proj'' (x0,x1,x2) s) =
          (?x. aMem a x IN ag32_proj'' (y0,y1,y2) s'))` by
      (Q.PAT_X_ASSUM `ag32_proj'' _ _ = ag32_proj'' _ _` (K ALL_TAC)
       \\ full_simp_tac bool_ss [IN_ag32_proj] \\ metis_tac [])
    \\ fs [EXTENSION] \\ metis_tac [])
  THEN1
   (`~((?x. aPc x IN ag32_proj'' (x0,x1,x2) s) =
       (?x. aPc x IN ag32_proj'' (y0,y1,y2) s'))` by
      (Q.PAT_X_ASSUM `ag32_proj'' _ _ = ag32_proj'' _ _` (K ALL_TAC)
       \\ full_simp_tac bool_ss [IN_ag32_proj] \\ metis_tac [])
    \\ fs [EXTENSION] \\ metis_tac []));

val DELETE_ag32_proj = prove(``
  (!s. (ag32_proj' (fs,ms,pc) s) DELETE aState s =
       (ag32_proj' (F,ms,pc) s)) /\
  (!b s. (ag32_proj' (fs,ms,pc) s) DELETE aMem b (s.MEM b) =
         (ag32_proj' (fs,ms DELETE b,pc) s)) /\
  (!s. (ag32_proj' (fs,ms,pc) s) DELETE aPc (s.PC) =
       (ag32_proj' (fs,ms,F) s))``,
  rw [ag32_proj'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ metis_tac []);

val EMPTY_ag32_proj = prove(``
  (ag32_proj' (fs,ms,pc) s = {}) <=> ~fs /\ (ms = {}) /\ ~pc``,
  rw [ag32_proj'_def,EXTENSION]
  \\ SRW_TAC [] [ag32_proj'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]);

(* theorems for construction of |- SPEC AG32_MODEL ... *)

val lemma =
  METIS_PROVE [SPLIT_ag32_proj]
  ``p (ag32_proj' y s) ==>
    (?u v. SPLIT (ag32_proj s) (u,v) /\ p u /\ (\v. v = ag32_proj'' y s) v)``;

Theorem AG32_SPEC_SEMANTICS:
   SPEC AG32_MODEL p {} q =
    !y s seq. p (ag32_proj' y s) /\ rel_sequence (λx y. y = Next x) seq s ==>
              ?k. q (ag32_proj' y (seq k)) /\
                  (ag32_proj'' y s = ag32_proj'' y (seq k))
Proof
  simp_tac std_ss [GSYM RUN_EQ_SPEC,RUN_def,AG32_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ rpt strip_tac \\ reverse eq_tac \\ rpt strip_tac
  THEN1 (full_simp_tac bool_ss [SPLIT_ag32_proj_EXISTS] \\ metis_tac [])
  \\ fs [PULL_EXISTS]
  \\ qspecl_then [`y`,`s`] assume_tac SPLIT_ag32_proj
  \\ first_x_assum drule
  \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
  \\ disch_then (qspec_then `(\v. v = ag32_proj'' y s)` mp_tac)
  \\ fs [] \\ rw []
  \\ full_simp_tac bool_ss [SPLIT_ag32_proj_EXISTS]
  \\ imp_res_tac ag32_proj''_11 \\ qexists_tac `i` \\ metis_tac []
QED

Theorem aD_STAR_ag32_proj:
   (aD md * p) (ag32_proj' (fs,ms,pc) s) <=>
      md SUBSET ms /\ p (ag32_proj' (fs,ms DIFF md,pc) s)
Proof
  simp_tac std_ss [aS_def,aM_def,aP_def,aB_def,EQ_STAR,INSERT_SUBSET,cond_STAR,
    EMPTY_SUBSET,IN_ag32_proj,GSYM DELETE_DEF,aD_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ eq_tac \\ rw []
  THEN1
   (fs [SUBSET_DEF] \\ rw [] \\ fs [PULL_EXISTS]
    \\ res_tac \\ fs [IN_ag32_proj])
  THEN1
   (last_x_assum mp_tac
    \\ match_mp_tac (METIS_PROVE [] ``x = y ==> (f x ==> f y)``)
    \\ fs [ag32_proj'_def,EXTENSION]
    \\ Cases \\ fs [] \\ rw [] \\ fs [SUBSET_DEF,PULL_EXISTS]
    \\ Cases_on `c IN md` \\ fs []    )
  \\ qexists_tac `s.MEM`
  \\ conj_tac
  THEN1
   (pop_assum mp_tac
    \\ match_mp_tac (METIS_PROVE [] ``x = y ==> (f x ==> f y)``)
    \\ fs [ag32_proj'_def,EXTENSION]
    \\ Cases \\ fs [] \\ rw [] \\ fs [SUBSET_DEF,PULL_EXISTS]
    \\ Cases_on `c IN md` \\ fs [])
  \\ fs [SUBSET_DEF] \\ rw [] \\ fs [PULL_EXISTS]
  \\ res_tac \\ fs [IN_ag32_proj]
QED

Theorem STAR_ag32_proj:
   ((aS t * p) (ag32_proj' (fs,ms,pc) s) <=>
      (t = s) /\ fs /\ p (ag32_proj' (F,ms,pc) s)) /\
    ((aM b y * p) (ag32_proj' (fs,ms,pc) s) <=>
      (y = s.MEM b) /\ b IN ms /\ p (ag32_proj' (fs,ms DELETE b,pc) s)) /\
    ((aD md * p) (ag32_proj' (fs,ms,pc) s) <=>
      md SUBSET ms /\ p (ag32_proj' (fs,ms DIFF md,pc) s)) /\
    ((aP q * p) (ag32_proj' (fs,ms,pc) s) <=>
      (q = s.PC) /\ pc /\ p (ag32_proj' (fs,ms,F) s)) /\
    ((cond g * p) (ag32_proj' (fs,ms,pc) s) <=>
      g /\ p (ag32_proj' (fs,ms,pc) s))
Proof
  simp [aD_STAR_ag32_proj]
  \\ simp_tac std_ss [aS_def,aM_def,aP_def,aB_def,EQ_STAR,INSERT_SUBSET,cond_STAR,
       EMPTY_SUBSET,IN_ag32_proj,GSYM DELETE_DEF,aD_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ Cases_on `t = s` \\ asm_simp_tac bool_ss [DELETE_ag32_proj]
  \\ Cases_on `y = s.MEM b` \\ asm_simp_tac bool_ss [DELETE_ag32_proj]
  \\ Cases_on `q = s.PC` \\ asm_simp_tac bool_ss [DELETE_ag32_proj]
  \\ asm_simp_tac std_ss [AC CONJ_COMM CONJ_ASSOC]
QED

val CODE_POOL_ag32_proj_LEMMA = prove(
  ``!x y z. (x = (z INSERT y)) <=> (z INSERT y) SUBSET x /\
            ((x DIFF (z INSERT y)) = {})``,
  fs [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ metis_tac []);

val CODE_POOL_ag32_proj = prove(
  ``CODE_POOL ag32_instr {(p,c)} (ag32_proj' (fs,ms,pc) s) <=>
      ({p+3w;p+2w;p+1w;p} = ms) /\ ~fs /\ ~pc /\
      (s.MEM (p + 0w) = ( 7 ><  0) c) /\
      (s.MEM (p + 1w) = (15 ><  8) c) /\
      (s.MEM (p + 2w) = (23 >< 16) c) /\
      (s.MEM (p + 3w) = (31 >< 24) c)``,
  simp_tac bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,ag32_instr_def,CODE_POOL_ag32_proj_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_ag32_proj]
  \\ Cases_on `(31 >< 24) c = s.MEM (p + 3w)` \\ asm_simp_tac std_ss []
  \\ Cases_on `(23 >< 16) c = s.MEM (p + 2w)` \\ asm_simp_tac std_ss []
  \\ Cases_on `(15 ><  8) c = s.MEM (p + 1w)` \\ asm_simp_tac std_ss []
  \\ Cases_on `( 7 ><  0) c = s.MEM (p + 0w)` \\ asm_simp_tac std_ss [WORD_ADD_0]
  \\ asm_simp_tac std_ss [DELETE_ag32_proj,EMPTY_ag32_proj,DIFF_INSERT]
  \\ asm_simp_tac std_ss [AC CONJ_COMM CONJ_ASSOC,DIFF_EMPTY,EMPTY_ag32_proj]);

val AG32_SPEC_CODE =
  SPEC_CODE |> ISPEC ``AG32_MODEL``
  |> SIMP_RULE std_ss [AG32_MODEL_def]
  |> REWRITE_RULE [GSYM AG32_MODEL_def];

val IMP_AG32_SPEC_LEMMA = prove(
  ``!p q.
      (!fs ms pc s. ?s'.
        (p (ag32_proj' (fs,ms,pc) s) ==>
        (Next s = s') /\ q (ag32_proj' (fs,ms,pc) s') /\
        (ag32_proj'' (fs,ms,pc) s = ag32_proj'' (fs,ms,pc) s'))) ==>
      SPEC AG32_MODEL p {} q``,
  simp_tac std_ss [RIGHT_EXISTS_IMP_THM] \\ rewrite_tac [AG32_SPEC_SEMANTICS]
  \\ simp_tac std_ss [FORALL_PROD]
  \\ rpt strip_tac \\ RES_TAC
  \\ full_simp_tac bool_ss [rel_sequence_def]
  \\ qexists_tac `SUC 0` \\ metis_tac [PAIR,optionTheory.SOME_11]);

val _ = wordsLib.guess_lengths();
Theorem BYTES_TO_WORD_LEMMA:
   !w. (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w
Proof
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] []
QED

val IMP_AG32_SPEC = save_thm("IMP_AG32_SPEC",
  (ONCE_REWRITE_RULE [STAR_COMM] o REWRITE_RULE [AG32_SPEC_CODE] o
   SPECL [``CODE_POOL ag32_instr c * p'``,
          ``CODE_POOL ag32_instr c * q'``]) IMP_AG32_SPEC_LEMMA);

val mem_unchanged_def = Define `
  mem_unchanged md m1 m2 = (!a. ~(a IN md) ==> m1 a = m2 a)`;

Theorem mem_unchanged_same[simp]:
   mem_unchanged md m m
Proof
  fs [mem_unchanged_def]
QED

Theorem ANY_AG32_SPEC_LEMMA:
   !w ast.
      ast = Decode w ==>
      mem_unchanged md (Run ast s).MEM s.MEM ==>
      SPEC AG32_MODEL
        (aS s * aD md * aPC p)
        {(p,w)}
        (aS (Run ast s) * aD md * aP (Run ast s).PC)
Proof
  fs [Next_def,mem_unchanged_def]
  \\ rw [aPC_def]
  \\ match_mp_tac IMP_AG32_SPEC
  \\ simp [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ rewrite_tac [GSYM STAR_ASSOC,STAR_ag32_proj,CODE_POOL_ag32_proj]
  \\ fs [RIGHT_EXISTS_IMP_THM]
  \\ ntac 2 strip_tac
  \\ fs [EXTENSION]
  \\ conj_asm1_tac
  THEN1
   (fs [Next_def] \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ rveq \\ fs [alignmentTheory.aligned_bitwise_and]
    \\ `((31 >< 2) s.PC:word30) @@ (0w:word2) = s.PC` by
          (qpat_x_assum `_ = 0w` mp_tac \\ blastLib.BBLAST_TAC)
    \\ fs [] \\ blastLib.BBLAST_TAC)
  \\ pop_assum (fn th => fs [GSYM th])
  \\ `~(p IN md)` by metis_tac []
  \\ `~(p + 1w IN md)` by metis_tac []
  \\ `~(p + 2w IN md)` by metis_tac []
  \\ `~(p + 3w IN md)` by metis_tac []
  \\ rveq \\ fs [Next_def]
  \\ Cases \\ fs [IN_ag32_proj]
  \\ Cases_on `c IN ms` \\ fs []
  \\ metis_tac [SUBSET_DEF]
QED

Theorem ANY_AG32_SPEC:
   !w ast.
      ast = Decode w ==>
      (aligned 2 s.PC ==> aligned 2 (Run ast s).PC) /\
      mem_unchanged md (Run ast s).MEM s.MEM ==>
      SPEC AG32_MODEL
        (aS s * aD md * aPC p)
        {(p,w)}
        (aS (Run ast s) * aD md * aPC (Run ast s).PC)
Proof
  rw []
  \\ drule (SIMP_RULE std_ss [] ANY_AG32_SPEC_LEMMA)
  \\ fs [aPC_def,STAR_ASSOC,SPEC_MOVE_COND]
  \\ Cases_on `aligned 2 (Run (Decode w) s).PC` \\ fs [SEP_CLAUSES]
  \\ rw [] \\ fs []
  \\ Cases_on `p = s.PC` \\ fs []
  \\ once_rewrite_tac [GSYM AG32_SPEC_CODE]
  \\ once_rewrite_tac [STAR_COMM]
  \\ fs [AG32_SPEC_SEMANTICS,FORALL_PROD]
  \\ fs [STAR_ag32_proj,GSYM STAR_ASSOC,aPC_def]
QED

Theorem SPEC_AG32_FIX_POST_PC:
   SPEC AG32_MODEL (aS s * aD md * aPC p) c (post s.PC) ==>
    SPEC AG32_MODEL (aS s * aD md * aPC p) c (post p)
Proof
  Cases_on `p = s.PC` \\ fs []
  \\ once_rewrite_tac [GSYM AG32_SPEC_CODE]
  \\ once_rewrite_tac [STAR_COMM]
  \\ fs [AG32_SPEC_SEMANTICS,FORALL_PROD]
  \\ fs [STAR_ag32_proj,GSYM STAR_ASSOC,aPC_def]
QED

(* SPEC implies FUNPOW Next *)

val code_set_def = Define `
  code_set a [] = {} /\
  code_set a (i::is) = (a:word32,i) INSERT code_set (a+4w) is`;

Theorem IN_code_set:
   !a xs p x.
      LENGTH xs < 2**30 ==>
      ((p,x) IN code_set a xs <=>
       ?i. p = a + n2w (4 * i) /\ x = EL i xs /\ i < LENGTH xs)
Proof
  Induct_on `xs` \\ fs [code_set_def] \\ rw []
  \\ reverse (Cases_on `p = a`) \\ fs [] THEN1
   (eq_tac \\ rw []
    THEN1 (qexists_tac `i+1`
      \\ fs [LEFT_ADD_DISTRIB,addressTheory.word_arith_lemma1]
      \\ fs [GSYM ADD1,EL])
    \\ Cases_on `i` \\ fs []
    \\ qexists_tac `n`
    \\ fs [LEFT_ADD_DISTRIB,addressTheory.word_arith_lemma1,ADD1])
  \\ fs [addressTheory.word_arith_lemma1]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ Cases_on `x = h` \\ fs []
  THEN1 (qexists_tac `0` \\ fs [])
  \\ eq_tac \\ rw []
  \\ `(4 * i + 4) < 4294967296` by fs [] \\ fs []
QED

val get_mem_word_def = ag32_memoryTheory.get_mem_word_def

Theorem SPEC_IMP_FUNPOW_Next:
   SPEC AG32_MODEL
      (aS s * aD md * aPC s.PC)
      (code_set a (MAP Encode instr_list))
      (aS s1 * aD md1 * other)
    ==>
    LENGTH instr_list < 2**30 ==>
    (∀k. k < LENGTH instr_list ==>
         (get_mem_word s.MEM (a + n2w (4 * k)) =
          Encode (EL k instr_list))) /\
    byte_aligned s.PC /\
    DISJOINT md { a + n2w k | k | k DIV 4 < LENGTH instr_list } ==>
    ∃k. FUNPOW Next k s = s1
Proof
  fs [alignmentTheory.byte_aligned_def]
  \\ once_rewrite_tac [GSYM AG32_SPEC_CODE]
  \\ once_rewrite_tac [STAR_COMM]
  \\ fs [AG32_SPEC_SEMANTICS,FORALL_PROD]
  \\ rewrite_tac [GSYM STAR_ASSOC,STAR_ag32_proj,aPC_def]
  \\ rpt strip_tac \\ fs []
  \\ first_x_assum (qspecl_then
    [`md UNION {a + n2w k | k DIV 4 < LENGTH instr_list}`,
     `\n. FUNPOW Next n s`] mp_tac)
  \\ reverse impl_tac
  THEN1 (fs [] \\ rw [] \\ fs [] \\ metis_tac [])
  \\ fs []
  \\ reverse conj_tac
  THEN1
   (fs [rel_sequence_def]
    \\ fs [ADD1] \\ once_rewrite_tac [ADD_COMM]
    \\ rewrite_tac [FUNPOW_ADD] \\ fs [])
  \\ fs [CODE_POOL_def]
  \\ `!x. DISJOINT md x ==> (md ∪ x DIFF md = x)` by
        (fs [IN_DISJOINT,EXTENSION] \\ metis_tac [])
  \\ res_tac \\ fs [ag32_proj'_def]
  \\ once_rewrite_tac [EXTENSION] \\ fs [PULL_EXISTS]
  \\ Cases \\ fs [ag32_instr_def,FORALL_PROD]
  \\ fs [EXISTS_PROD]
  \\ eq_tac \\ rw []
  THEN1
   (last_x_assum drule \\ strip_tac
    \\ simp [IN_code_set]
    \\ qexists_tac `a + n2w (4 * (k DIV 4))`
    \\ qexists_tac `Encode (EL (k DIV 4) instr_list)`
    \\ simp [PULL_EXISTS]
    \\ qexists_tac `k DIV 4`
    \\ fs [EL_MAP]
    \\ strip_assume_tac (
         MATCH_MP DIVISION (DECIDE ``0<4n``)
         |> ONCE_REWRITE_RULE [CONJ_COMM] |> Q.SPEC `k`)
    \\ pop_assum (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
    \\ simp [GSYM addressTheory.word_arith_lemma1]
    \\ imp_res_tac (DECIDE ``n < 4n ==> n=0 \/ n=1 \/ n=2 \/ n=3``)
    \\ fs [] \\ fs [ag32_instr_def]
    \\ rewrite_tac [addressTheory.WORD_EQ_ADD_CANCEL] \\ fs []
    \\ qpat_x_assum `_ = Encode _` (fn th => rewrite_tac [GSYM th])
    \\ fs [get_mem_word_def]
    \\ rpt (pop_assum kall_tac)
    \\ blastLib.BBLAST_TAC)
  \\ rfs [IN_code_set]
  \\ fs [ag32_instr_def] \\ rveq \\ fs []
  \\ fs [addressTheory.word_arith_lemma1]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  THENL [qexists_tac `4 * i + 3`,
         qexists_tac `4 * i + 2`,
         qexists_tac `4 * i + 1`,
         qexists_tac `4 * i`]
  \\ fs [DIV_LT_X,EL_MAP]
  \\ last_x_assum (drule o GSYM) \\ fs []
  \\ strip_tac
  \\ fs [get_mem_word_def,addressTheory.word_arith_lemma1]
  \\ rpt (pop_assum kall_tac)
  \\ blastLib.BBLAST_TAC
QED

val () = export_theory()
