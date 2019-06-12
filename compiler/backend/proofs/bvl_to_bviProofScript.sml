(*
  Correctness proof for bvl_to_bvi
*)
open preamble backendPropsTheory
     bvlSemTheory bvlPropsTheory
     bvl_to_bviTheory
     bviSemTheory bviPropsTheory;
local open
  bvl_constProofTheory
  bvl_handleProofTheory
  bvi_letProofTheory
  bvl_inlineProofTheory
  bvi_tailrecProofTheory
in end;

val _ = new_theory"bvl_to_bviProof";

val _ = set_grammar_ancestry
  ["ffi", "bvlSem", "bviSem", "bviProps", "bvl_to_bvi", "bvl_handleProof"];

val _ = Parse.hide"str";

val handle_ok_def = bvl_handleProofTheory.handle_ok_def;

(* value relation *)
val _ = temp_overload_on ("num_stubs", ``bvl_num_stubs``)
val _ = temp_overload_on ("nss", ``bvl_to_bvi_namespaces``);

val adjust_bv_def = tDefine "adjust_bv" `
  (adjust_bv b (Number i) = Number i) /\
  (adjust_bv b (Word64 w) = Word64 w) /\
  (adjust_bv b (RefPtr r) = RefPtr (b r)) /\
  (adjust_bv b (CodePtr c) = CodePtr (num_stubs + nss * c)) /\
  (adjust_bv b (Block tag vs) = Block tag (MAP (adjust_bv b) vs))`
  (WF_REL_TAC `measure (v_size o SND)`
   \\ Induct_on `vs` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [v_size_def]
   \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

val adjust_bv_ind = theorem"adjust_bv_ind";

Theorem adjust_bv_Unit[simp]:
   adjust_bv x Unit = Unit
Proof
  EVAL_TAC
QED

Theorem adjust_bv_Boolv[simp]:
   adjust_bv x (Boolv b) = Boolv b
Proof
  Cases_on`b`>>EVAL_TAC
QED

val aux_code_installed_def = Define `
  (aux_code_installed [] t <=> T) /\
  (aux_code_installed ((name,arg_count,body)::rest) t <=>
     (sptree$lookup name t = SOME (arg_count,body)) /\
     aux_code_installed rest t)`

val aux_code_installed_APPEND = Q.prove(
  `!xs ys.
      aux_code_installed (xs++ys) code ==>
      aux_code_installed xs code /\
      aux_code_installed ys code`,
  Induct \\ fs[APPEND,aux_code_installed_def,FORALL_PROD] \\ METIS_TAC []);

Theorem aux_code_installed_subspt:
   !x c1 c2. aux_code_installed x c1 /\ subspt c1 c2 ==>
              aux_code_installed x c2
Proof
  Induct \\ fs [aux_code_installed_def,subspt_lookup,FORALL_PROD]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

val _ = temp_overload_on("in_ns_0",``λn. n MOD bvl_to_bvi_namespaces = 0``);
val _ = temp_overload_on("in_ns_1",``λn. n MOD bvl_to_bvi_namespaces = 1``);

val names_ok_def = Define `
  names_ok s_code t_code s_oracle <=>
    (!n k prog. s_oracle n = (k,prog) ==>
                EVERY (\(name,arity,exp). handle_ok [exp]) prog) /\
    let next = FST (FST (s_oracle 0n)) in
      (!n. n IN sptree$domain t_code /\ num_stubs <= n ==>
           if in_ns_1 n then n < num_stubs + nss * next
           else in_ns_0 n /\
                (n - num_stubs) DIV bvl_to_bvi_namespaces IN sptree$domain s_code)`;

val state_rel_def = Define `
  state_rel (b:num->num) s (t:('c,'ffi) bviSem$state) <=>
    INJ b (FDOM s.refs) (FDOM t.refs) /\
    (!k. case FLOOKUP s.refs k of
         | NONE => T
         | SOME (ValueArray vs) =>
             (FLOOKUP t.refs (b k) = SOME (ValueArray (MAP (adjust_bv b) vs)))
         | SOME res => (FLOOKUP t.refs (b k) = SOME res)) /\
    (s.ffi = t.ffi) /\
    (∀p. t.global = SOME p ⇒
           p ∉ IMAGE b (FDOM s.refs) ∧
           ∃z. FLOOKUP t.refs p =
                 SOME (ValueArray
                   ((Number(&(SUC(LENGTH s.globals))))::
                    (MAP (the (Number 0) o OPTION_MAP (adjust_bv b)) s.globals ++
                    REPLICATE (z - (SUC(LENGTH s.globals))) (Number 0)))) ∧
               SUC(LENGTH s.globals) ≤ z) ∧
    (s.clock = t.clock) /\
    t.compile_oracle = state_co compile_inc s.compile_oracle /\
    s.compile = state_cc compile_inc t.compile /\
    (lookup AllocGlobal_location t.code = SOME AllocGlobal_code) ∧
    (lookup CopyGlobals_location t.code = SOME CopyGlobals_code) ∧
    (lookup ListLength_location t.code = SOME ListLength_code) ∧
    (lookup FromListByte_location t.code = SOME FromListByte_code) ∧
    (lookup SumListLength_location t.code = SOME SumListLength_code) ∧
    (lookup ConcatByte_location t.code = SOME ConcatByte_code) ∧
    (* (lookup InitGlobals_location t.code = SOME InitGlobals_code start) ∧ *)
    names_ok s.code t.code s.compile_oracle /\
    (!name arity exp.
       (lookup name s.code = SOME (arity,exp)) ==>
       ?n. let (c1,aux1,n1) = compile_exps n [exp] in
             (lookup (num_stubs + nss * name) t.code =
                SOME (arity,bvi_let$compile_exp (HD c1))) /\
             aux_code_installed (append aux1) t.code /\
             handle_ok [exp])`;

Theorem state_rel_FLOOKUP_byteArray:
   !b s t m l n. state_rel b s t /\ FLOOKUP s.refs n = SOME (ByteArray m l)
  ==> FLOOKUP t.refs (b n) = SOME (ByteArray m l)
Proof
  rpt strip_tac >> fs[state_rel_def]
  >> rpt(first_x_assum(qspec_then `n` assume_tac))
  >> rfs[]
QED

val bv_ok_def = tDefine "bv_ok" `
  (bv_ok (refs: num |-> v ref) (RefPtr r) <=> r IN FDOM refs) /\
  (bv_ok refs (Block tag vs) <=> EVERY (bv_ok refs) vs) /\
  (bv_ok refs _ <=> T)`
  (WF_REL_TAC `measure (v_size o SND)`
   \\ Induct_on `vs` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [v_size_def]
   \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

val bv_ok_ind = theorem"bv_ok_ind";

val bv_ok_SUBSET_IMP = Q.prove(
  `!refs x refs2.
      bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x`,
  HO_MATCH_MP_TAC bv_ok_ind \\ full_simp_tac(srw_ss())[bv_ok_def]
  \\ full_simp_tac(srw_ss())[SUBSET_DEF,EVERY_MEM]);

Theorem bv_ok_Unit[simp]:
   bv_ok refs Unit
Proof
  EVAL_TAC
QED

Theorem bv_ok_Boolv[simp]:
   bv_ok refs (Boolv b)
Proof
  EVAL_TAC
QED

val bv_ok_IMP_adjust_bv_eq = Q.prove(
  `!b2 a1 b3.
      bv_ok refs a1 /\
      (!a. a IN FDOM refs ==> b2 a = b3 a) ==>
      (adjust_bv b2 a1 = adjust_bv b3 a1)`,
  HO_MATCH_MP_TAC adjust_bv_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bv_ok_def]
  \\ full_simp_tac(srw_ss())[MAP_EQ_f,EVERY_MEM]);

val state_ok_def = Define `
  state_ok (s:('c,'ffi) bvlSem$state) <=>
    EVERY (\x. case x of NONE => T | SOME v => bv_ok s.refs v) s.globals /\
    !k. case FLOOKUP s.refs k of
        | SOME (ValueArray vs) => EVERY (bv_ok s.refs) vs
        | _ => T`;

(* evaluate preserves state_ok *)

val evaluate_ok_lemma = Q.prove(
  `(state_ok (dec_clock n s) = state_ok s) /\
    ((dec_clock n s).refs = s.refs)`,
  full_simp_tac(srw_ss())[state_ok_def,bvlSemTheory.dec_clock_def]);

val evaluate_IMP_bv_ok = Q.prove(
  `(bvlSem$evaluate (xs,env,s) = (res,t)) ==>
    (bv_ok s.refs a1 ==> bv_ok t.refs a1) /\
    (EVERY (bv_ok s.refs) as ==> EVERY (bv_ok t.refs) as)`,
  REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC evaluate_refs_SUBSET \\ IMP_RES_TAC bv_ok_SUBSET_IMP);

val v_to_list_ok = Q.prove(
  `∀v x. v_to_list v = SOME x ∧
         bv_ok refs v ⇒
         EVERY (bv_ok refs) x`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,bv_ok_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

Theorem list_to_v_ok:
   !xs. EVERY (bv_ok refs) xs ==> bv_ok refs (list_to_v xs)
Proof
  Induct \\ rw [list_to_v_def, bv_ok_def]
QED

Theorem list_to_v_ok_APPEND:
   !xs ys.
     bv_ok refs (list_to_v xs) /\
     bv_ok refs (list_to_v ys) ==>
       bv_ok refs (list_to_v (xs ++ ys))
Proof
  Induct \\ rw [list_to_v_def, bv_ok_def]
QED

val do_app_ok_lemma = Q.prove(
  `state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q`,
  `?f. f () = op` by (qexists_tac `K op` \\ fs [])
  \\ Cases_on `op = Install` THEN1
   (rw [] \\ fs [bvlSemTheory.do_app_def,bvlSemTheory.do_install_def,
      case_eq_thms,UNCURRY] \\ rveq \\ fs [state_ok_def]
    \\ fs [bv_ok_def])
  \\ Cases_on `op` \\ full_simp_tac(srw_ss())[bvlSemTheory.do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ TRY (full_simp_tac(srw_ss())[] \\ SRW_TAC [] [bv_ok_def]
    \\ full_simp_tac(srw_ss())[closSemTheory.get_global_def]
    \\ full_simp_tac(srw_ss())[state_ok_def,bv_ok_def] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bv_ok_def,EVERY_EL] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bv_ok_def,EVERY_MEM] \\ NO_TAC)
  \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_THM] \\ rpt BasicProvers.VAR_EQ_TAC THEN1
   (full_simp_tac(srw_ss())[closSemTheory.get_global_def,state_ok_def,EVERY_EL]
    \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ REPEAT (Q.PAT_X_ASSUM `!x.bb` (K ALL_TAC))
    \\ REV_FULL_SIMP_TAC std_ss [])
  THEN1
   (SRW_TAC [] [bv_ok_def] \\ full_simp_tac(srw_ss())[LET_DEF,state_ok_def]
    \\ MATCH_MP_TAC IMP_EVERY_LUPDATE \\ full_simp_tac(srw_ss())[])
  >- (
    rw [bv_ok_def]
    >- fs [EVERY_MEM] >>
    irule EVERY_TAKE >>
    simp []
    \\ conj_tac >- intLib.ARITH_TAC >>
    irule EVERY_DROP
    \\ conj_tac >- intLib.ARITH_TAC >>
    rw [] >>
    fs [bv_ok_def])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    BasicProvers.CASE_TAC >> TRY BasicProvers.CASE_TAC >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[] >>
    simp[SUBSET_DEF])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    rpt BasicProvers.CASE_TAC >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[rich_listTheory.REPLICATE_GENLIST,MEM_GENLIST] >>
    simp[SUBSET_DEF])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    every_case_tac >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[] >>
    simp[SUBSET_DEF])
  THEN1 (
    fs[state_ok_def,FLOOKUP_UPDATE,EVERY_MEM] \\ rw[]
    \\ TRY CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
    \\ res_tac
    \\ TRY asm_exists_tac \\ simp[SUBSET_DEF]
    \\ qmatch_goalsub_abbrev_tac`bv_ok _ (RefPtr ptr)`
    \\ qexists_tac`r.refs |+ (ptr,X)`
    \\ simp[bv_ok_def] )
  THEN1 (
    fs[state_ok_def,FLOOKUP_UPDATE,EVERY_MEM] \\ rw[]
    \\ TRY CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
    \\ res_tac
    \\ TRY asm_exists_tac \\ simp[SUBSET_DEF]
    \\ qmatch_goalsub_abbrev_tac`bv_ok _ (RefPtr ptr)`
    \\ qexists_tac`r.refs |+ (ptr,X)`
    \\ simp[bv_ok_def] )
  THEN1 (
    fs[state_ok_def,FLOOKUP_UPDATE,EVERY_MEM] \\ rw[]
    \\ TRY CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ res_tac \\ fs[]
    \\ TRY asm_exists_tac \\ simp[SUBSET_DEF]
    \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
    \\ res_tac
    \\ TRY asm_exists_tac \\ simp[SUBSET_DEF] )
  >- (* ListAppend *)
    metis_tac [v_to_list_ok, list_to_v_ok, list_to_v_ok_APPEND]
  THEN1 (
    rename1 `_ () = FromList n`
    \\ simp[bv_ok_def] >>
    imp_res_tac v_to_list_ok >>
    full_simp_tac(srw_ss())[EVERY_MEM])
  THEN1 (
    rename1`_ () = String _`
    \\ fs[state_ok_def,bv_ok_def,EVERY_MEM,FLOOKUP_UPDATE]
    \\ rw[]
    \\ CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ fs[] \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ TRY (first_x_assum(qspec_then`k`mp_tac) \\ rw[])
    \\ res_tac \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ fs[SUBSET_DEF] )
  THEN1 (
    rename1` _ () = FromListByte`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ strip_tac
    \\ imp_res_tac v_to_list_ok
    \\ fs[state_ok_def,bv_ok_def,EVERY_MEM,FLOOKUP_UPDATE]
    \\ rw[]
    \\ CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ fs[] \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ TRY (first_x_assum(qspec_then`k`mp_tac) \\ rw[])
    \\ TRY (first_x_assum(qspec_then`k`mp_tac) \\ rw[])
    \\ res_tac \\ fs[bv_ok_def]
    \\ asm_exists_tac \\ fs[]
    \\ fs[SUBSET_DEF] )
  THEN1
   (rename1 `_ () = Ref`
    \\ full_simp_tac(srw_ss())[LET_DEF,state_ok_def]
    \\ SRW_TAC [] [bv_ok_def,FLOOKUP_DEF,EVERY_MEM]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs []
    THEN1 (match_mp_tac bv_ok_SUBSET_IMP
           \\ asm_exists_tac \\ fs [] \\ fs [SUBSET_DEF])
    \\ rw [] \\ fs [] \\ fs [FAPPLY_FUPDATE_THM]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum (qspec_then `k` mp_tac)
    \\ fs [FLOOKUP_DEF] \\ rw [] \\ res_tac
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ TRY (asm_exists_tac \\ fs [] \\ fs [SUBSET_DEF])
    \\ every_case_tac \\ fs[FAPPLY_FUPDATE_THM]
    \\ every_case_tac \\ fs[LEAST_NOTIN_FDOM] \\ rw[] )
  THEN1
   (rename1 `_ () = Deref`
    \\ full_simp_tac(srw_ss())[state_ok_def]
    \\ Q.PAT_X_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[EVERY_EL] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ SRW_TAC [] [] \\ Cases_on `i` \\ full_simp_tac(srw_ss())[])
  THEN1
   (rename1 `_ () = Update`
    \\ full_simp_tac(srw_ss())[state_ok_def] \\ SRW_TAC [] [] THEN1
     (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    THEN1
     (full_simp_tac(srw_ss())[FLOOKUP_UPDATE] \\ Cases_on `k = n` \\ full_simp_tac(srw_ss())[] THEN1
       (MATCH_MP_TAC IMP_EVERY_LUPDATE \\ REPEAT STRIP_TAC
        THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
          \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
        \\ Q.PAT_X_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
        \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
      \\ Q.PAT_X_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.EVERY_CASE_TAC
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF]))
  THEN1 (
    full_simp_tac(srw_ss())[state_ok_def] \\ srw_tac[][] >-
     (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    \\ simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    first_x_assum(qspec_then`k`mp_tac) >> srw_tac[][] >>
    full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF]));

Theorem do_app_ok:
   state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q /\
    (EVERY (bv_ok r.refs) env ==> EVERY (bv_ok t.refs) env)
Proof
  STRIP_TAC \\ IMP_RES_TAC do_app_ok_lemma \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC do_app_refs_SUBSET
  \\ IMP_RES_TAC bv_ok_SUBSET_IMP
QED
val _ = print "Proved do_app_ok_lemma\n"

val dec_clock_inc_clock = prove(
  ``c <> 0 ==> dec_clock 1 (inc_clock c t) =
               inc_clock (c-1) (t: ('c,'ffi) bviSem$state)``,
  EVAL_TAC \\ fs [bviSemTheory.state_component_equality]);

Theorem find_code_bv_ok:
   bvlSem$find_code dest vs s = SOME (args,e2) /\
    EVERY (bv_ok (refs : num |-> bvlSem$v ref)) vs ==> EVERY (bv_ok refs) args
Proof
  Cases_on `dest` \\ fs [bvlSemTheory.find_code_def]
  \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ `?v xs. vs = SNOC v xs` by metis_tac [SNOC_CASES]
  \\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC]
  \\ fs [SNOC_APPEND,EVERY_APPEND]
QED

Theorem evaluate_ok:
   !xs env s res t.
      (evaluate (xs,env,s) = (res,t)) /\
      state_ok s /\ EVERY (bv_ok s.refs) env ==>
      state_ok t /\
      (case res of
       | Rval vs => EVERY (bv_ok t.refs) vs
       | Rerr(Rraise v) => bv_ok t.refs v
       | _ => T) /\
      EVERY (bv_ok t.refs) env
Proof
  recInduct bvlSemTheory.evaluate_ind \\ rpt strip_tac
  \\ fs[bvlSemTheory.evaluate_def] \\ rw [] \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs[] \\ rveq \\ fs []
  \\ imp_res_tac evaluate_IMP_bv_ok \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ TRY (full_simp_tac(srw_ss())[EVERY_EL] \\ NO_TAC)
  \\ TRY (qpat_x_assum `(_,_) = _` (assume_tac o GSYM)) \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs[] \\ rveq \\ fs []
  \\ TRY (fs [state_ok_def,evaluate_ok_lemma] \\ NO_TAC)
  \\ TRY (do_app_ok |> REWRITE_RULE [CONJ_ASSOC]
         |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL |> drule)
  \\ fs [EVERY_REVERSE]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac bvlPropsTheory.do_app_err \\ fs[evaluate_ok_lemma]
  \\ rfs []
  \\ drule (GEN_ALL find_code_bv_ok) \\ fs []
  \\ disch_then drule \\ rw [] \\ fs [] \\ rfs []
  \\ drule (GEN_ALL evaluate_IMP_bv_ok) \\ fs [dec_clock_def]
QED

(* semantics lemmas *)

val evaluate_MAP_Var = Q.prove(
  `!l env vs b s.
      EVERY isVar l /\ (get_vars (MAP destVar l) env = SOME vs) ==>
        (evaluate (MAP (Var o destVar) l,MAP (adjust_bv b) env,s) =
          (Rval (MAP (adjust_bv b) vs),s))`,
  Induct THEN1 (EVAL_TAC \\ SRW_TAC [] [])
  \\ Cases \\ full_simp_tac(srw_ss())[isVar_def,destVar_def,get_vars_def]
  \\ Cases_on `l` \\ full_simp_tac(srw_ss())[bviSemTheory.evaluate_def,get_vars_def,EL_MAP]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[isVar_def,destVar_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n' < LENGTH env` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars (MAP destVar t) env` \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!xx.bb` (MP_TAC o Q.SPEC `env`) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[EL_MAP])
  |> INST_TYPE[beta|->``:'ffi``,alpha|->``:'c``];

val evaluate_MAP_Var2 = Q.prove(
  `!args.
      bVarBound (LENGTH vs) args /\ EVERY isVar args ==>
      ?ts.
        bviSem$evaluate (MAP (Var o destVar) args,vs ++ env,s) = (Rval ts,s) /\
        evaluate (MAP (Var o destVar) args,vs,s) = (Rval ts,s)`,
  Induct \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def] \\ Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ Cases_on `args` \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def,destVar_def,bVarBound_def]
  \\ REPEAT STRIP_TAC
  \\ `n < LENGTH vs + LENGTH env` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]) |> SPEC_ALL
  |> INST_TYPE[beta|->``:'ffi``,alpha|->``:'c``];

val bEval_bVarBound = Q.prove(
  `!xs vs s env.
      bVarBound (LENGTH vs) xs ==>
      (bvlSem$evaluate (xs,vs ++ env,s) = evaluate (xs,vs,s))`,
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def,bVarBound_def]
  \\ TRY (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[ADD1] \\ NO_TAC)
  THEN1 (`n < LENGTH env + LENGTH env'` by DECIDE_TAC
         \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM MATCH_MP_TAC
         \\ IMP_RES_TAC bvlPropsTheory.evaluate_IMP_LENGTH
         \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]));

val iEval_def = bviSemTheory.evaluate_def;

(* correctness of stubs *)

val bEvalOp_def = bvlSemTheory.do_app_def;
val iEvalOp_def = bviSemTheory.do_app_def;

val evaluate_CopyGlobals_code = Q.prove(
  `∀n l1 s.
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code) ∧
   FLOOKUP s.refs p = SOME (ValueArray ls) ∧
   FLOOKUP s.refs p1 = SOME (ValueArray l1) ∧
   p ≠ p1 ∧
   n < LENGTH ls ∧ n < LENGTH l1
   ⇒
   ∃c.
     evaluate ([SND CopyGlobals_code],
               [RefPtr p1; RefPtr p; Number &n],
               inc_clock c s) =
     (Rval [Unit], s with refs := s.refs |+ (p1, ValueArray (TAKE (SUC n) ls ++ DROP (SUC n) l1)))`,
  Induct >> srw_tac[][] >> srw_tac[][CopyGlobals_code_def] >>
  srw_tac[][iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id,backend_commonTheory.small_enough_int_def,bvl_to_bvi_with_refs] >- (
    qexists_tac`0`>>simp[inc_clock_ZERO,state_component_equality] >>
    rpt AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_LUPDATE] >>
    srw_tac[][] >> simp[EL_APPEND2,EL_DROP] >>
    Cases_on`ls`>>full_simp_tac(srw_ss())[]) >>
  simp[find_code_def] >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`l2 = LUPDATE x y z` >>
  qpat_abbrev_tac`rf = s.refs |+ X` >>
  first_x_assum(qspecl_then[`l2`,`s with refs := rf`]mp_tac) >>
  impl_tac >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    simp[Abbr`l2`] ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with refs := rf)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n:int` by (
    simp[ADD1] >> intLib.COOPER_TAC ) >>
  simp[state_component_equality] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE] >>
  srw_tac[][] >>
  simp[LIST_EQ_REWRITE,Abbr`l2`] >> srw_tac[][] >>
  Cases_on`x < SUC n` >> simp[EL_APPEND1,EL_TAKE] >>
  simp[EL_APPEND2,EL_DROP,EL_LUPDATE] >>
  Cases_on`x = SUC n` >> simp[EL_APPEND1,EL_TAKE,EL_APPEND2,EL_DROP])
  |> Q.GEN`ls`;
val _ = print "Proved evaluate_CopyGlobals_code\n"

val evaluate_AllocGlobal_code = Q.prove(
  `s.global = SOME p ∧
   FLOOKUP s.refs p = SOME (ValueArray (Number(&(SUC n))::ls)) ∧ n ≤ LENGTH ls ∧
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code)
   ⇒
   ∃p1 c.
     (p1 ≠ p ⇒ p1 ∉ FDOM s.refs) ∧
     evaluate ([SND AllocGlobal_code],[],inc_clock c s) =
       (Rval [Unit],
        s with <| global := SOME p1; refs := s.refs
          |+ (p, ValueArray ((Number(&(SUC(n+1))))::ls))
          |+ (p1, ValueArray ((Number(&(SUC(n+1))))::
                              if n < LENGTH ls then ls
                              else ls ++ (REPLICATE (SUC(LENGTH ls)) (Number 0))))|>)`,
  strip_tac >>
  simp[AllocGlobal_code_def,iEval_def,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def,
       Once inc_clock_def,bEvalOp_def,bvl_to_bvi_id,bvl_to_bvi_with_refs,FLOOKUP_UPDATE,
       find_code_def] >>
  IF_CASES_TAC >> simp[] >- (
    Q.LIST_EXISTS_TAC[`p`,`0`] >>
    simp[state_component_equality] >>
    EVAL_TAC >>
    simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
    srw_tac[][] >> simp[] >> intLib.COOPER_TAC) >>
  `(λptr. ptr ≠ p ∧ ptr ∉ FDOM s.refs) = (λptr. ptr ∉ FDOM s.refs)` by (
    simp[FUN_EQ_THM] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[]) >> simp[] >>
  qpat_abbrev_tac`p1 = LEAST ptr. ptr ∉ FDOM s.refs` >>
  qexists_tac`p1` >>
  `p1 ∉ FDOM s.refs` by (
    rpt strip_tac >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
    metis_tac[LEAST_NOTIN_FDOM] ) >>
  simp[LUPDATE_def] >>
  qpat_abbrev_tac`l1 = REPLICATE _ _` >>
  qpat_abbrev_tac`rf = s.refs |+ _ |+ _` >>
  qspecl_then[`Number(1+ &SUC n)::ls`,`n`,`l1`,`s with <| global := SOME p1; refs := rf|>`]mp_tac evaluate_CopyGlobals_code >>
  impl_tac >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    IF_CASES_TAC >> simp[] >- (
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[LEAST_NOTIN_FDOM] ) >>
    simp[Abbr`l1`,LENGTH_REPLICATE] \\ intLib.COOPER_TAC ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with <| global := SOME p1; refs := rf|>)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n:int` by (Cases_on`n`>>full_simp_tac(srw_ss())[]>>simp[ADD1]>>intLib.COOPER_TAC) >> full_simp_tac(srw_ss())[] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE,state_component_equality] >>
  srw_tac[][] >> simp[] >> TRY(intLib.COOPER_TAC) >>
  `n = LENGTH ls`by decide_tac >>
  `2 * (LENGTH ls + 1) = LENGTH ls + LENGTH ls + 2` by DECIDE_TAC >>
  simp[Abbr`l1`,DROP_REPLICATE,ADD1]
  \\ rewrite_tac[GSYM REPLICATE]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ intLib.COOPER_TAC);

Theorem evaluate_ListLength_code:
   !lv vs n.
      lookup ListLength_location s.code = SOME (2,SND ListLength_code) /\
      v_to_list lv = SOME vs ==>
      ∃p1 c.
        evaluate ([SND ListLength_code],[lv;Number (&n)],inc_clock c s) =
          (Rval [Number (&(n + LENGTH vs))],s)
Proof
  HO_MATCH_MP_TAC v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rveq
  \\ fs [ListLength_code_def] THEN1
   (fs [bviSemTheory.evaluate_def,EVAL ``Boolv T``,
        EVAL ``bviSem$do_app (TagLenEq nil_tag 0) [Block nil_tag []] s``]
    \\ fs [inc_clock_def,bviSemTheory.state_component_equality])
  \\ simp [bviSemTheory.evaluate_def,EVAL ``Boolv T``]
  \\ fs [EVAL ``bviSem$do_app (TagLenEq nil_tag 0) [Block cons_tag [h; lv]] s``,
         EVAL ``bviSem$do_app (Const 1) [] s``,
         EVAL ``bviSem$do_app (Const 0) [] s``,EVAL ``Boolv F``,
         EVAL ``bviSem$do_app El [Block cons_tag [h; lv]; Number 1] s``,
         EVAL ``bviSem$do_app Add [Number (&n); Number (&m)] s``,
         bvlSemTheory.find_code_def]
  \\ Cases_on `v_to_list lv` \\ fs [] \\ rw [] \\ fs []
  \\ first_x_assum (qspec_then `n+1` mp_tac) \\ strip_tac
  \\ qexists_tac `c+1` \\ fs []
  \\ qpat_abbrev_tac `s1 = dec_clock 1 _`
  \\ `inc_clock c s = s1` by
   (unabbrev_all_tac \\ fs [bviSemTheory.state_component_equality,
       bviSemTheory.dec_clock_def] \\ fs [inc_clock_def])
  \\ fs [] \\ pop_assum kall_tac
  \\ `(1 + &n) = (&(n + 1)):int` by intLib.COOPER_TAC \\ fs []
QED

Theorem evaluate_FromListByte_code:
   ∀lv vs n bs (s:('c,'ffi) bviSem$state).
    v_to_list lv = SOME (MAP (Number o $&) vs) ∧ LENGTH vs ≤ LENGTH bs ∧
    lookup FromListByte_location s.code = SOME (3,SND FromListByte_code) ∧
    EVERY (λn. n < 256) vs ∧
    FLOOKUP s.refs p = SOME (ByteArray fl bs) ∧ n = LENGTH bs - LENGTH vs
    ⇒
    ∃c.
      evaluate ([SND FromListByte_code],[lv;Number (&n);RefPtr p],inc_clock c s) =
        (Rval [RefPtr p], s with refs := s.refs |+ (p,ByteArray fl (TAKE n bs ++ (MAP n2w vs))))
Proof
  ho_match_mp_tac v_to_list_ind \\ rw[] \\ fs[v_to_list_def] \\ rveq
  \\ rfs[FromListByte_code_def]
  >- (
    simp[iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,
         bvl_to_bvi_with_clock,inc_clock_def,bvl_to_bvi_id,
         state_component_equality]
    \\ simp[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[] \\ fs[] )
  \\ Cases_on`v_to_list lv` \\ fs[] \\ Cases_on`vs` \\ fs[]
  \\ Cases_on`bs` \\ fs[]
  \\ simp[iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,backend_commonTheory.small_enough_int_def,
          bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ rveq \\ fs [] (* fix *)
  \\ reverse CASE_TAC \\ fs[]
  >- ( first_x_assum(qspec_then`n2w h'`mp_tac) \\ fs[] )
  \\ simp[iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,backend_commonTheory.small_enough_int_def,
          bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ simp[find_code_def]
  \\ qmatch_goalsub_abbrev_tac`inc_clock _ _ with refs := refs`
  \\ qmatch_asmsub_abbrev_tac`ByteArray fl (h1::t1)`
  \\ qmatch_asmsub_abbrev_tac`h2 = w2n w`
  \\ qmatch_asmsub_abbrev_tac `LENGTH t ≤ LENGTH t1` (* fix *)
  \\ first_x_assum(qspecl_then[`t`,`LUPDATE w (LENGTH t1 - LENGTH t) (h1::t1)`,`s with refs := refs`]mp_tac)
  \\ impl_tac >- simp[Abbr`refs`,FLOOKUP_UPDATE] \\ strip_tac
  \\ qexists_tac`c+1`
  \\ simp[] \\ fs[ADD1]
  \\ fs[dec_clock_def,inc_clock_def]
  \\ qmatch_goalsub_abbrev_tac`Number n1`
  \\ qmatch_asmsub_abbrev_tac`Number n2`
  \\ `n1 = n2` by (simp[Abbr`n1`,Abbr`n2`,integerTheory.INT_ADD])
  \\ fs[Abbr`n1`,Abbr`n2`,state_component_equality]
  \\ simp[Abbr`refs`,fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[]
  \\ rw[LIST_EQ_REWRITE,EL_TAKE,EL_LUPDATE]
  \\ rw[EL_TAKE,EL_APPEND1,EL_APPEND2]
QED

Theorem evaluate_SumListLength_code:
   ∀lv ps wss n.
   lookup SumListLength_location s.code = SOME (2,SND SumListLength_code) ∧
   v_to_list lv = SOME (MAP RefPtr ps) ∧
   MAP (FLOOKUP s.refs) ps = MAP (SOME o ByteArray T) wss
   ⇒
   ∃c.
     evaluate
       ([SND SumListLength_code],[lv;Number(&n)],inc_clock c s) =
       (Rval [Number (&(n + LENGTH (FLAT wss)))],s)
Proof
  recInduct v_to_list_ind \\ rw[v_to_list_def]
  \\ fs[SumListLength_code_def]
  >- (
    rw[evaluate_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id]
    \\ qexists_tac`0` \\ rw[inc_clock_ZERO] )
  \\ rfs[]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`ps` \\ fs[]
  \\ Cases_on`wss` \\ fs[]
  \\ rw[evaluate_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,
        backend_commonTheory.small_enough_int_def,bvl_to_bvi_id]
  \\ fs[GSYM SumListLength_code_def]
  \\ rw[find_code_def]
  \\ CASE_TAC
  \\ rename1`SumListLength_code = (arity,code)`
  \\ `arity = 2` by fs[SumListLength_code_def]
  \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`evaluate ([code'],_,_)`
  \\ `code' = code` by fs[SumListLength_code_def]
  \\ rw[]
  \\ fs[Once CONJ_COMM]
  \\ first_x_assum drule
  \\ simp[]
  \\ rename1`&LENGTH ls + &n`
  \\ disch_then(qspec_then`LENGTH ls + n`(qx_choose_then`c`strip_assume_tac))
  \\ qexists_tac`c+1`
  \\ fs[inc_clock_def,dec_clock_def,integerTheory.INT_ADD]
QED

Theorem evaluate_ConcatByte_code:
   ∀lv ps wss (s:('c,'ffi) bviSem$state) ds1 ds2 n.
   lookup SumListLength_location s.code = SOME (2,SND SumListLength_code) ∧
   lookup ConcatByte_location s.code = SOME (3,SND ConcatByte_code) ∧
   v_to_list lv = SOME (MAP RefPtr ps) ∧ dst ∉ set ps ∧
   MAP (FLOOKUP s.refs) ps = MAP (SOME o ByteArray T) wss ∧
   FLOOKUP s.refs dst = SOME (ByteArray T (ds1++ds2)) ∧
   n = LENGTH ds1 ∧ LENGTH (FLAT wss) = LENGTH ds2
   ⇒
   ∃c.
     evaluate
       ([SND ConcatByte_code],[lv;Number(&n);RefPtr dst],inc_clock c s) =
       (Rval [RefPtr dst], s with refs := s.refs |+ (dst, ByteArray T (ds1++FLAT wss)))
Proof
  recInduct v_to_list_ind
  \\ rw[v_to_list_def]
  \\ rw[ConcatByte_code_def]
  >- (
    rw[evaluate_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id]
    \\ qexists_tac`0` \\ fs[inc_clock_ZERO,state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE]
    \\ rw[] \\ fs[LENGTH_NIL_SYM] )
  \\ every_case_tac \\ fs[]
  \\ Cases_on`ps` \\ fs[]
  \\ Cases_on`wss` \\ fs[]
  \\ rw[evaluate_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id,backend_commonTheory.small_enough_int_def,
        semanticPrimitivesTheory.copy_array_def]
  \\ TRY intLib.COOPER_TAC
  \\ rw[find_code_def,inc_clock_ZERO,bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ qpat_abbrev_tac`refs = s.refs |+ _`
  \\ qmatch_assum_abbrev_tac`lookup x s.code = y`
  \\ `lookup x (s with refs := refs).code = y` by simp[]
  \\ map_every qunabbrev_tac[`x`,`y`]
  \\ first_x_assum(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ rename1`¬MEM dst ts`
  \\ `MAP (FLOOKUP s.refs) ts = MAP (FLOOKUP refs) ts`
  by (
    rw[MAP_EQ_f,Abbr`refs`,FLOOKUP_UPDATE]
    \\ rw[] \\ fs[] \\ NO_TAC)
  \\ fs[]
  \\ disch_then(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`(dst,ByteArray T ds)`
  \\ `FLOOKUP refs dst = SOME (ByteArray T ds)` by simp[Abbr`refs`,FLOOKUP_UPDATE]
  \\ simp[Abbr`ds`]
  \\ fs[integerTheory.INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd]
  \\ fs[TAKE_APPEND1,integerTheory.INT_ADD,DROP_APPEND2]
  \\ rename1`ds1 ++ ws ++ _`
  \\ disch_then(qspec_then`ds1 ++ ws`mp_tac)
  \\ simp[] \\ disch_then(qx_choose_then`c`strip_assume_tac)
  \\ qexists_tac`c+1`
  \\ fs[inc_clock_def,dec_clock_def,state_component_equality,Abbr`refs`]
QED

(* compiler correctness *)

val bEval_def = bvlSemTheory.evaluate_def;
val iEval_append = bviPropsTheory.evaluate_APPEND;

val compile_exps_Var_list = Q.prove(
  `!l n. EVERY isVar l ==> (∃aux. compile_exps n l = (MAP (Var o destVar) l ,aux,n) ∧ append aux = [])`,
  Induct \\ fs[compile_exps_def] \\ Cases \\ rw[isVar_def] \\ fs[]
  \\ Cases_on`l` \\ fs[compile_exps_def,destVar_def]
  \\ qmatch_goalsub_rename_tac`compile_exps a`
  \\ first_x_assum(qspec_then`a`strip_assume_tac) \\ fs[]);

val compile_int_thm = Q.prove(
  `!i env s. evaluate ([compile_int i],env,s) = (Rval [Number i],s)`,
  STRIP_TAC \\ completeInduct_on `Num (ABS i)`
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ POP_ASSUM (K ALL_TAC)
  \\ reverse (Cases_on `i`) \\ full_simp_tac(srw_ss())[] THEN1 EVAL_TAC
  \\ (ONCE_REWRITE_TAC [compile_int_def] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ SRW_TAC [] [] THEN1
     (`n <= 268435457` by DECIDE_TAC
      \\ full_simp_tac(srw_ss())[evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,backend_commonTheory.small_enough_int_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`&(n DIV 268435457)`,`env`,`s`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[integerTheory.INT_ABS_NUM,DIV_LT_X] \\ intLib.COOPER_TAC)
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `n MOD 268435457 < 268435457` by full_simp_tac(srw_ss())[MOD_LESS]
    \\ `n MOD 268435457 <= 268435457` by DECIDE_TAC
    \\ full_simp_tac(srw_ss())[evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,backend_commonTheory.small_enough_int_def,bvlSemTheory.do_app_def]
    \\ full_simp_tac(srw_ss())[bvl_to_bvi_id]
    \\ STRIP_ASSUME_TAC
         (MATCH_MP DIVISION (DECIDE ``0 < 268435457:num``) |> Q.SPEC `n`)
    \\ intLib.COOPER_TAC));

val compile_string_thm = Q.prove(
  `∀str s ls vs.
   FLOOKUP s.refs ptr = SOME (ByteArray T ls) ∧ LENGTH vs + LENGTH str = LENGTH ls ⇒
   evaluate (MAPi (λn c. Op UpdateByte [Op (Const (&ORD c)) []; compile_int (&(n + LENGTH vs)); Var 0]) str,
    RefPtr ptr::env, s) = (Rval (REPLICATE (LENGTH str) Unit),
      s with refs := s.refs |+ (ptr, ByteArray T (TAKE (LENGTH vs) ls ++ (MAP (n2w o ORD) str))))`,
  Induct \\ rw[evaluate_def,REPLICATE]
  >- (rw[state_component_equality]
      \\ match_mp_tac (GSYM FUPDATE_ELIM) \\ fs[FLOOKUP_DEF])
  \\ rw[Once evaluate_CONS]
  \\ reverse(rw[evaluate_def,do_app_def,do_app_aux_def,backend_commonTheory.small_enough_int_def])
  >- ( qspec_then`h`strip_assume_tac ORD_BOUND \\ fs[] )
  \\ reverse(rw[bvlSemTheory.do_app_def,compile_int_thm,EL_LENGTH_APPEND])
  >- (
    fs[] \\ first_x_assum(qspec_then`n2w (ORD h)`mp_tac)
    \\ simp[w2n_n2w,ORD_BOUND] )
  \\ simp[o_DEF,ADD1]
  \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ qpat_abbrev_tac`ss = s with refs := _`
  \\ first_x_assum(qspec_then`ss`mp_tac)
  \\ simp[Abbr`ss`,FLOOKUP_UPDATE]
  \\ disch_then(qspec_then`ARB::vs`mp_tac)
  \\ rw[ADD1,state_component_equality]
  \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[]
  \\ rw[LIST_EQ_REWRITE]
  \\ Cases_on`x = LENGTH vs` \\ simp[EL_APPEND1,EL_LUPDATE,EL_APPEND2,EL_TAKE]
  \\ Cases_on`x < LENGTH vs` \\ simp[EL_APPEND1,EL_TAKE,EL_LUPDATE]
  \\ simp[EL_TAKE,EL_APPEND2,o_DEF])
  |> Q.SPECL[`str`,`s`,`ls`,`[]`]
  |> SIMP_RULE(srw_ss())[]
  |> Q.GENL[`str`,`ls`,`ptr`,`s`,`env`]
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];

Theorem HD_APPEND3:
   0 < LENGTH (l1 ++ l2) ⇒ HD (l1 ++ l2 ++ l3) = HD (l1 ++ l2)
Proof
  Cases_on`l1` \\ simp[] \\
  Cases_on`l2` \\ simp[]
QED

val iEval_bVarBound = Q.prove(
  `!(n:num) xs n vs (s:('c,'ffi) bviSem$state) env.
     bVarBound (LENGTH vs) xs /\ handle_ok xs ==>
     (evaluate (FST (compile_exps n xs),vs ++ env,s) =
      evaluate (FST (compile_exps n xs),vs,s))`,
  recInduct bVarBound_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[iEval_def,bVarBound_def,compile_exps_def]
  \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bEvery_def,handle_ok_def] \\ SRW_TAC [] []
  THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[])
  THEN1 (full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (fs [])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def])
  THEN1
   (fs [evaluate_def] \\ rveq \\ fs []
    \\ Cases_on `x2` \\ fs [destLet_def,NULL_EQ]
    \\ fs [destLet_def,markerTheory.Abbrev_def,
         bvl_handleProofTheory.let_ok_def] \\ rveq \\ fs[]
    \\ IMP_RES_TAC compile_exps_Var_list
    \\ first_x_assum(qspec_then`n`strip_assume_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bVarBound_def]
    \\ (evaluate_MAP_Var2 |> MP_TAC) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[iEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate (c1,vs,s)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[NULL_EQ,LENGTH_NIL]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a ++ vs`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC bviPropsTheory.evaluate_IMP_LENGTH \\ IMP_RES_TAC compile_exps_LENGTH
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  \\ TRY (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def] \\ NO_TAC)
  THEN1
   (Cases_on `op = Install` THEN1
     (fs [compile_op_def] \\ IF_CASES_TAC \\ fs []
      THEN1
       (once_rewrite_tac [evaluate_def]
        \\ `evaluate ([Let c1 (Op (Const 0) []); Op (Const 0) []],vs ⧺ env,s) =
            evaluate ([Let c1 (Op (Const 0) []); Op (Const 0) []],vs,s)` by
         (fs [evaluate_def]
          \\ first_x_assum (qspecl_then [`n`,`vs`] mp_tac) \\ fs [])
        \\ fs [] \\ CASE_TAC \\ simp [case_eq_thms]
        \\ Cases_on `q` \\ fs []
        \\ once_rewrite_tac [evaluate_def]
        \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ simp [evaluate_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ Cases_on `a` \\ fs []
        \\ Cases_on `t` \\ fs [])
      THEN1
       (once_rewrite_tac [evaluate_def]
        \\ imp_res_tac compile_exps_LENGTH \\ rfs []
        \\ FIRST_X_ASSUM (qspecl_then [`n`,`vs`] mp_tac) \\ fs [] \\ rw []
        \\ TOP_CASE_TAC \\ TOP_CASE_TAC
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ Cases_on `a` \\ fs [] \\ rveq \\ fs []
        \\ Cases_on `t` \\ fs [] \\ fs [evaluate_def]))
    \\ Cases_on `(?t. op = FromList t) ∨ op = FromListByte ∨ op = ConcatByteVec` THEN1
     (fs [] \\ rw[] \\ fs [compile_op_def]
      \\ once_rewrite_tac [bviSemTheory.evaluate_def]
      \\ (IF_CASES_TAC THEN1
        (fs [bviSemTheory.evaluate_def,EVAL ``bviSem$do_app (Const 0) [] s``]))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`])
      \\ full_simp_tac(srw_ss())[]
      \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on `a` \\ fs [LENGTH_NIL]
      \\ fs [bviSemTheory.evaluate_def])
    \\ Cases_on`∃str. op = String str`
    >- (
      fs[] \\ fs[compile_op_def]
      \\ once_rewrite_tac[bviSemTheory.evaluate_def]
      \\ once_rewrite_tac[bviSemTheory.evaluate_def]
      \\ once_rewrite_tac[bviSemTheory.evaluate_def]
      \\ once_rewrite_tac[bviSemTheory.evaluate_def]
      \\ simp[iEval_append]
      \\ simp[compile_int_thm]
      \\ first_x_assum(qspecl_then[`n`,`vs`]mp_tac) \\ fs[]
      \\ CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[]
      \\ simp[do_app_def,do_app_aux_def,backend_commonTheory.small_enough_int_def,bvlSemTheory.do_app_def]
      \\ IF_CASES_TAC \\ fs[] \\ pop_assum(SUBST_ALL_TAC o SYM)
      \\ qmatch_goalsub_abbrev_tac`r.refs |+ (ptr,ByteArray T ls)`
      \\ qpat_abbrev_tac`rr = r with refs := _`
      \\ qspecl_then[`str`,`ls`,`ptr`,`rr`,`vs`]mp_tac compile_string_thm
      \\ impl_tac >- simp[Abbr`ls`,Abbr`rr`,FLOOKUP_UPDATE,LENGTH_REPLICATE]
      \\ simp[]
      \\ qspecl_then[`str`,`ls`,`ptr`,`rr`,`vs++env`]mp_tac compile_string_thm
      \\ impl_tac >- simp[Abbr`ls`,Abbr`rr`,FLOOKUP_UPDATE,LENGTH_REPLICATE]
      \\ simp[]
      \\ ntac 3 (disch_then kall_tac)
      \\ simp[LENGTH_REPLICATE,Abbr`ls`,EL_APPEND1] )
    \\ Cases_on`op = CopyByte T`
    >- (
      fs[compile_op_def]
      \\ first_x_assum drule
      \\ disch_then(qspecl_then[`n`,`s`,`env`]mp_tac) \\ simp[]
      \\ IF_CASES_TAC
      >- (
        rw[Once bviSemTheory.evaluate_def]
        \\ rw[evaluate_APPEND]
        \\ rw[Once bviSemTheory.evaluate_def,SimpRHS]
        \\ rw[evaluate_APPEND,REPLICATE_compute]
        \\ CASE_TAC \\  simp[]
        \\ Cases_on`q` \\ simp[]
        \\ rw[bviSemTheory.evaluate_def,REPLICATE_compute,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def,HD_APPEND3]
        \\ CASE_TAC \\ simp[]
        \\ imp_res_tac evaluate_IMP_LENGTH
        \\ rewrite_tac[GSYM APPEND_ASSOC,GSYM EL]
        \\ simp[EL_APPEND1]
        \\ CASE_TAC \\ fs[EL_APPEND1]) \\
      rw[Once bviSemTheory.evaluate_def]
      \\ rw[evaluate_APPEND]
      \\ rw[Once bviSemTheory.evaluate_def,SimpRHS]
      \\ rw[evaluate_APPEND,REPLICATE_compute]
      \\ CASE_TAC \\  simp[]
      \\ Cases_on`q` \\ simp[]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on`a` \\ fs[]
      \\ Cases_on`t` \\ fs[]
      \\ rename1`SUC (LENGTH t)`
      \\ Cases_on`t` \\ fs[]
      \\ rw[bviSemTheory.evaluate_def,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `op`
    \\ full_simp_tac(srw_ss())[compile_op_def,iEval_def,compile_int_thm]
    \\ simp[iEval_def]
    \\ simp[iEval_append,iEval_def,compile_int_thm]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[iEval_def,compile_int_thm])
  \\ full_simp_tac(srw_ss())[iEval_def]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`]) \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ Cases_on `x1` \\ fs [] \\ rveq
  \\ Cases_on `e` \\ fs [] \\ rveq
  \\ fs [destLet_def,markerTheory.Abbrev_def] \\ rveq
  \\ IMP_RES_TAC compile_exps_Var_list
  \\ first_x_assum(qspec_then`n`strip_assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bVarBound_def]
  \\ (evaluate_MAP_Var2 |> MP_TAC) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ fs [])
  \\ ONCE_REWRITE_TAC [APPEND |> SPEC_ALL |> CONJUNCT2 |> GSYM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[ADD1]);

val v_to_list_adjust = Q.prove(
  `∀x. v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f)) (v_to_list x)`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,adjust_bv_def] >> srw_tac[][] >>
  Cases_on`v_to_list x`>>full_simp_tac(srw_ss())[]);

val do_eq_adjust_lemma = Q.prove(
  `(!refs x1 x2 b.
              refs = r.refs /\
              do_eq refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
              bv_ok r.refs x1 /\ bv_ok r.refs x2 ==>
              do_eq t2.refs (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b) /\
   (!refs x1 x2 b.
              refs = r.refs /\
              do_eq_list refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
              EVERY (bv_ok r.refs) x1 /\ EVERY (bv_ok r.refs) x2 ==>
              do_eq_list t2.refs (MAP (adjust_bv b2) x1) (MAP (adjust_bv b2) x2) = Eq_val b)`,
  ho_match_mp_tac do_eq_ind \\ rw [] \\ fs [adjust_bv_def]
  THEN1 (
    fs[bv_ok_def]
    \\ Cases_on`FLOOKUP r.refs n2` >- fs[FLOOKUP_DEF]
    \\ Cases_on`FLOOKUP r.refs n1` >- fs[FLOOKUP_DEF] \\ fs[]
    \\ fs[state_rel_def]
    \\ last_assum(qspec_then`n2`mp_tac)
    \\ last_x_assum(qspec_then`n1`mp_tac)
    \\ simp[]
    \\ every_case_tac \\ fs[]
    \\ fs[INJ_DEF]
    \\ metis_tac[])
  \\ fs [isClos_def] \\ rfs []
  \\ fs [bv_ok_def] \\ rfs []
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ rw [] \\ every_case_tac \\ fs []);

val do_eq_adjust = Q.prove(
  `do_eq r.refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
   bv_ok r.refs x1 /\ bv_ok r.refs x2 ==>
   do_eq t2.refs (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b`,
  metis_tac [do_eq_adjust_lemma]);

Theorem list_to_v_adjust:
   !xs.
   list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v xs)
Proof
   Induct \\ rw [list_to_v_def, adjust_bv_def]
QED

Theorem list_to_v_adjust_APPEND:
   !xs ys.
     list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v xs) /\
     list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v xs) ==>
      list_to_v (MAP (adjust_bv b) (xs ++ ys)) =
      adjust_bv b (list_to_v (xs ++ ys))
Proof
  Induct
  >- (Induct_on `ys` \\ rw [] \\ fs [adjust_bv_def, list_to_v_def])
  \\ rw [list_to_v_def, adjust_bv_def] \\ fs []
QED

val do_app_adjust = Q.prove(
  `state_rel b2 s5 t2 /\
   (!i. op <> Const i) /\ (op <> Ref) /\ (∀flag. op ≠ RefByte flag) ∧ (op ≠ RefArray) ∧
   (∀n. op ≠ Global n) ∧ (∀n. op ≠ SetGlobal n) ∧ (op ≠ AllocGlobal) ∧
   op <> Install /\
   (∀n. op ≠ FromList n) ∧ (op ≠ FromListByte) ∧ (∀str. op ≠ String str) ∧
   (∀b. op ≠ CopyByte b) ∧ (op ≠ ConcatByteVec) ∧ (∀n. op ≠ Label n) ∧
   (do_app op (REVERSE a) s5 = Rval (q,r)) /\ EVERY (bv_ok s5.refs) (REVERSE a) ==>
   ?t3. (do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 =
          Rval (adjust_bv b2 q,t3)) /\
        state_rel b2 r t3`,
  `?debug. debug () = op` by (qexists_tac `K op` \\ fs [])
  \\ SIMP_TAC std_ss [Once bEvalOp_def,iEvalOp_def,do_app_aux_def]
  \\ Cases_on `op = El` \\ fs [] THEN1
   (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bEvalOp_def]
    \\ every_case_tac >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id,
         bEvalOp_def,EL_MAP] \\ SRW_TAC [] [])
  \\ Cases_on `op = ListAppend` \\ fs []
  >-
   (fs [case_eq_thms, case_elim_thms, PULL_EXISTS, SWAP_REVERSE_SYM]
    \\ rw [] \\ fs []
    \\ fs [bvlSemTheory.do_app_def, case_eq_thms, PULL_EXISTS, bvl_to_bvi_id]
    \\ fs [v_to_list_adjust]
    \\ metis_tac [list_to_v_adjust, list_to_v_adjust_APPEND, MAP_APPEND])
  \\ Cases_on `op = Length` \\ fs [] THEN1
   (every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bEvalOp_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[adjust_bv_def,bvl_to_bvi_id] >- (
      full_simp_tac(srw_ss())[state_rel_def,bvi_to_bvl_def] >> srw_tac[][] >>
      last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][]) >>
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][])
  \\ Cases_on `op = LengthByte` \\ fs [] THEN1
   (every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bEvalOp_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[adjust_bv_def,bvl_to_bvi_id] >- (
      full_simp_tac(srw_ss())[state_rel_def,bvi_to_bvl_def] >> srw_tac[][] >>
      last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][]) >>
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][])
  \\ Cases_on `op = DerefByte` \\ fs [] THEN1
   (Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >>
    srw_tac[][adjust_bv_def,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
  \\ Cases_on `op = Deref` \\ fs [] THEN1
   (Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `FLOOKUP s5.refs n` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ full_simp_tac(srw_ss())[bEvalOp_def]
    \\ Q.EXISTS_TAC `t2` \\ full_simp_tac(srw_ss())[]
    \\ `FLOOKUP t2.refs (b2 n) = SOME(ValueArray(MAP (adjust_bv b2) l))` by (
        full_simp_tac(srw_ss())[state_rel_def] >>
        last_x_assum(qspec_then`n`mp_tac) >>
        simp[] )
    \\ simp[]
    \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
    \\ `Num i < LENGTH l` by METIS_TAC[integerTheory.INT_OF_NUM,integerTheory.INT_LT]
    \\ simp[EL_MAP,bvl_to_bvi_id])
  \\ Cases_on `op = Update` \\ fs [] THEN1
   (Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `FLOOKUP s5.refs n` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ full_simp_tac(srw_ss())[bEvalOp_def] \\ SIMP_TAC std_ss [Once bvi_to_bvl_def] \\ full_simp_tac(srw_ss())[]
    \\ `FLOOKUP t2.refs (b2 n) =
        SOME (ValueArray (MAP (adjust_bv b2) l))` by
     (full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
      \\ last_x_assum (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[])
    \\ simp[]
    \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac \\ simp[]
    \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
    \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
    \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE]
    \\ conj_tac >- full_simp_tac(srw_ss())[FLOOKUP_DEF,ABSORPTION_RWT]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LUPDATE_MAP,bv_ok_def]
    THEN1 (
      BasicProvers.CASE_TAC >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF,INJ_DEF] >>
      METIS_TAC[] ) >>
    res_tac >> METIS_TAC[])
  \\ Cases_on `?n. op = FFI n` \\ fs [] THEN1
   (Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    srw_tac[][] >>
    qmatch_assum_rename_tac`bv_ok s5.refs (RefPtr k)` >>
    qpat_x_assum `bv_ok s5.refs (RefPtr k)` mp_tac >>
    qmatch_assum_rename_tac`bv_ok s5.refs (RefPtr k')` >>
    DISCH_TAC >>
    Cases_on`FLOOKUP s5.refs k'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`FLOOKUP s5.refs k`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'`>>full_simp_tac(srw_ss())[]>>
    `FLOOKUP t2.refs (b2 k) = FLOOKUP s5.refs k` by (
      full_simp_tac(srw_ss())[state_rel_def] >>
      last_x_assum(qspec_then`k`mp_tac) >> simp[] ) >>
    `FLOOKUP t2.refs (b2 k') = FLOOKUP s5.refs k'` by (
      full_simp_tac(srw_ss())[state_rel_def] >>
      last_x_assum(qspec_then`k'`mp_tac) >> simp[] ) >>
    simp[] >>
    simp[Once bvi_to_bvl_def] >>
    `s5.ffi = t2.ffi` by full_simp_tac(srw_ss())[state_rel_def] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    simp[bvl_to_bvi_with_refs,bvl_to_bvi_with_ffi,bvl_to_bvi_id] >>
    simp[bvi_to_bvl_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    conj_tac >- (
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      simp[ABSORPTION_RWT] ) >>
    simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bv_ok_def] >>
    TRY BasicProvers.CASE_TAC >>
    full_simp_tac(srw_ss())[FLOOKUP_DEF,bvl_to_bvi_def] >>
    METIS_TAC[INJ_DEF])
  \\ Cases_on `op = UpdateByte` \\ fs [] THEN1
   (strip_tac
    \\ `?n i i'. REVERSE a = [RefPtr n; Number i; Number i']` by
          (every_case_tac \\ fs [] \\ NO_TAC) \\ fs [] >>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >>
    srw_tac[][adjust_bv_def,bvl_to_bvi_with_refs,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    TRY (
      last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
      spose_not_then strip_assume_tac >> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[] >>
      NO_TAC) >>
    simp[bvi_to_bvl_def] >>
    conj_asm1_tac >- (
      simp[INJ_INSERT] >>
      conj_tac >- (
        qhdtm_x_assum`INJ`mp_tac >>
        simp[INJ_DEF] ) >>
      `n ∈ FDOM s5.refs` by full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    simp[FLOOKUP_UPDATE] >>
    srw_tac[][] >> TRY (
      last_x_assum(qspec_then`k`mp_tac) >> simp[] >> NO_TAC) >>
    full_simp_tac(srw_ss())[bv_ok_def] >>
    TRY (
      qexists_tac`array_size`>>simp[]>>
      srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC) >>
    TRY (
      BasicProvers.CASE_TAC >>
      `k ∈ FDOM s5.refs ∧ n ∈ FDOM s5.refs` by fs[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    METIS_TAC[])
  \\ Cases_on `op = Equal` \\ fs [] THEN1
   (strip_tac
    \\ `?x1 x2. REVERSE a = [x1;x2]` by (every_case_tac \\ fs [] \\ NO_TAC)
    \\ fs [] \\ Cases_on `do_eq s5.refs x1 x2` \\ fs [] \\ rw []
    \\ fs [bvlSemTheory.do_app_def]
    \\ drule do_eq_adjust \\ fs []
    \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def])
  \\ Cases_on `op = BoundsCheckArray` THEN1
   (fs [] \\ strip_tac
    \\ `?x1 x2. REVERSE a = [x1;x2]` by (every_case_tac \\ fs [] \\ NO_TAC)
    \\ Cases_on `x1` \\ fs []
    \\ Cases_on `x2` \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ TOP_CASE_TAC \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ rpt strip_tac \\ rveq
    \\ fs [bviSemTheory.do_app_def]
    \\ simp[bEvalOp_def,adjust_bv_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >>
    srw_tac[][adjust_bv_def,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[])
  \\ Cases_on `∃b. op = BoundsCheckByte b` THEN1
   (fs [] \\ strip_tac
    \\ `?x1 x2. REVERSE a = [x1;x2]` by (every_case_tac \\ fs [] \\ NO_TAC)
    \\ Cases_on `x1` \\ fs []
    \\ Cases_on `x2` \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ TOP_CASE_TAC \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ rpt strip_tac \\ rveq
    \\ fs [bviSemTheory.do_app_def]
    \\ simp[bEvalOp_def,adjust_bv_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >>
    srw_tac[][adjust_bv_def,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[]) >>
  Cases_on `?tag. op = ConsExtend tag`
  >- (
    rw [] >>
    fs [] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    fs [adjust_bv_def, bvlSemTheory.do_app_def] >>
    rw [MAP_TAKE, MAP_DROP] >>
    metis_tac [bvl_to_bvi_id])
  \\ Cases_on `op` \\ full_simp_tac(srw_ss())[]
  \\ TRY (full_simp_tac(srw_ss())[bEvalOp_def]
          \\ every_case_tac \\ fs [adjust_bv_def]
          \\ fs [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id] \\ rveq \\ rw []
          \\ fs [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id] \\ NO_TAC));

Theorem eval_ind_alt:
   ∀P.
     (∀env s. P ([],env,s)) ∧
     (∀x y xs env s.
        (∀v3 s1 v1.
           evaluate ([x],env,s) = (v3,s1) ∧ v3 = Rval v1 ⇒
           P (y::xs,env,s1)) ∧ P ([x],env,s) ⇒
        P (x::y::xs,env,s)) ∧ (∀n env s. P ([Var n],env,s)) ∧
     (∀x1 x2 x3 env s.
        (∀v2 s1 vs.
           evaluate ([x1],env,s) = (v2,s1) ∧ v2 = Rval vs ∧
           Boolv T ≠ HD vs ∧ Boolv F = HD vs ⇒
           P ([x3],env,s1)) ∧
        (∀v2 s1 vs.
           evaluate ([x1],env,s) = (v2,s1) ∧ v2 = Rval vs ∧
           Boolv T = HD vs ⇒
           P ([x2],env,s1)) ∧ P ([x1],env,s) ⇒
        P ([If x1 x2 x3],env,s)) ∧
     (∀xs x2 env s.
        (∀ys v2 s1 vs.
           exp1_size ys <= exp_size x2 /\ evaluate (xs,env,s) = (v2,s1) ⇒
           P (ys,vs,s1)) ∧
        (∀ys env. exp1_size ys <= exp_size x2 ⇒ P (ys,env,s)) ∧
        (∀v2 s1 vs.
           evaluate (xs,env,s) = (v2,s1) ∧ v2 = Rval vs ⇒
           P ([x2],vs ++ env,s1)) ∧
        P (xs,env,s) ⇒
        P ([Let xs x2],env,s)) ∧
     (∀x1 env s. P ([x1],env,s) ⇒ P ([Raise x1],env,s)) ∧
     (∀x1 x2 env s1.
        (∀v3 s v8 v.
           evaluate ([x1],env,s1) = (v3,s) ∧ v3 = Rerr v8 ∧
           v8 = Rraise v ⇒
           P ([x2],v::env,s)) ∧
        (∀xs env. exp1_size xs <= exp_size x1 ⇒ P (xs,env,s1)) ⇒
        P ([Handle x1 x2],env,s1)) ∧
     (∀op xs env s. P (xs,env,s) ⇒ P ([Op op xs],env,s)) ∧
     (∀x env s.
        (s.clock ≠ 0 ⇒ P ([x],env,dec_clock 1 s)) ⇒
        P ([Tick x],env,s)) ∧
     (∀ticks dest xs env s1.
        (∀v2 s vs v args exp.
           evaluate (xs,env,s1) = (v2,s) ∧ v2 = Rval vs ∧
           find_code dest vs s.code = SOME v ∧ v = (args,exp) ∧
           ¬(s.clock < ticks + 1) ⇒
           P ([exp],args,dec_clock (ticks + 1) s)) ∧ P (xs,env,s1) ⇒
        P ([Call ticks dest xs],env,s1)) ⇒
     ∀v v1 v2. P (v,v1,v2:('c,'ffi) bvlSem$state)
Proof
  rpt strip_tac
  \\ HO_MATCH_MP_TAC (MP_CANON WF_INDUCTION_THM)
  \\ WF_REL_TAC `(inv_image (measure I LEX measure exp1_size)
                              (\(xs,env,s). (s.clock,xs)))`
  \\ rw [] \\ Cases_on `p_1` \\ fs []
  \\ reverse (Cases_on `t`) \\ fs [] THEN1
   (pop_assum (fn th => first_x_assum match_mp_tac \\ assume_tac th)
    \\ rw [] \\ first_x_assum match_mp_tac \\ fs []
    \\ imp_res_tac bvlSemTheory.evaluate_clock
    \\ fs [LESS_OR_EQ,bvlTheory.exp_size_def])
  \\ Cases_on `h` \\ fs []
  \\ pop_assum (fn th => first_x_assum match_mp_tac \\ assume_tac th)
  \\ rw [] \\ first_x_assum match_mp_tac \\ fs []
  \\ imp_res_tac bvlSemTheory.evaluate_clock
  \\ fs [LESS_OR_EQ,bvlTheory.exp_size_def]
  \\ fs [bvlSemTheory.dec_clock_def]
QED

Theorem EVERY_isVar_evaluate_Rval_MEM:
   !l env a s r.
      EVERY isVar l /\ bvlSem$evaluate (l,env,s) = (Rval a,r) ==>
      EVERY (\x. MEM x env) a /\ s = r
Proof
  Induct \\ fs [bvlSemTheory.evaluate_def]
  \\ Cases_on `h` \\ fs[isVar_def]
  \\ Cases_on `l` \\ fs [bvlSemTheory.evaluate_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [] \\ res_tac \\ fs [] \\ rveq
  \\ fs [MEM_EL] \\ asm_exists_tac \\ fs []
QED

val do_app_Ref = Q.prove(
  `do_app Ref vs s =
     Rval
      (RefPtr (LEAST ptr. ptr ∉ FDOM s.refs),
       bvl_to_bvi
        (bvi_to_bvl s with
         refs :=
           s.refs |+ ((LEAST ptr. ptr ∉ FDOM s.refs),ValueArray vs)) s)`,
  fs [iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_THM]
  \\ every_case_tac \\ fs []);

Theorem state_rel_add_bytearray:
   state_rel b2 s5 (t2:('c,'ffi) bviSem$state) ∧
   state_ok s5 ∧
   pp ∉ FDOM s5.refs ∧
   qq ∉ FDOM t2.refs ⇒
   state_rel ((pp =+ qq) b2)
     (s5 with refs := s5.refs |+ (pp,ByteArray fl ws))
     (t2 with refs := t2.refs |+ (qq,ByteArray fl ws))
Proof
  strip_tac
  \\ fs[state_rel_def,FLOOKUP_UPDATE]
  \\ conj_tac >- ( match_mp_tac INJ_EXTEND \\ fs[] )
  \\ conj_tac
  >- (
    fs[APPLY_UPDATE_THM]
    \\ gen_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ qpat_x_assum`∀k. option_CASE (FLOOKUP s5.refs k) _ _`(qspec_then`k`mp_tac)
    \\ TOP_CASE_TAC \\ simp[]
    \\ `qq ≠ b2 k`
    by ( pop_assum mp_tac \\ rw[FLOOKUP_DEF] \\ METIS_TAC[INJ_DEF] )
    \\ simp[]
    \\ TOP_CASE_TAC \\ rw[MAP_EQ_f]
    \\ match_mp_tac (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
    \\ qexists_tac `s5.refs`
    \\ fs[state_ok_def]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ simp[EVERY_MEM]
    \\ rw[APPLY_UPDATE_THM]
    \\ METIS_TAC[] )
  \\ simp[APPLY_UPDATE_THM]
  \\ gen_tac \\ strip_tac
  \\ `qq ≠ p`
  by (
    fs[]
    \\ `p ∈ FDOM t2.refs` by fs[FLOOKUP_DEF]
    \\ METIS_TAC[] )
  \\ fs[] \\ conj_tac >- ( rw[] )
  \\ simp[APPLY_UPDATE_THM]
  \\ qexists_tac`z` \\ simp[MAP_EQ_f]
  \\ Cases \\ rw[libTheory.the_def]
  \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq)
  \\ qexists_tac `s5.refs`
  \\ simp[APPLY_UPDATE_THM]
  \\ fs[state_ok_def,EVERY_MEM]
  \\ res_tac \\ fs[]
  \\ rw[]
  \\ metis_tac[INJ_DEF]
QED

val iEval_bVarBound_extra = prove(
  ``∀n xs n vs s env d.
     bVarBound (LENGTH vs) xs ∧ handle_ok xs /\ d = FST (compile_exps n xs) ⇒
     evaluate (d,vs ⧺ env,s)  =
     evaluate (d,vs,s)``,
  simp [iEval_bVarBound]);

val MAP_Num_11 = prove(
  ``!ns:word8 list ns'.
      MAP (λx. Number (&w2n x)) ns = MAP (λx. Number (&w2n x)) ns' <=> ns' = ns``,
  Induct \\ Cases_on `ns'` \\ fs [] \\ rw [] \\ eq_tac \\ rw []);

val MAP_Word_11 = prove(
  ``!ns ns'. MAP Word64 ns = MAP Word64 ns' <=> ns' = ns``,
  Induct \\ Cases_on `ns'` \\ fs [] \\ rw [] \\ eq_tac \\ rw []);

Theorem IMP_v_to_bytes:
   !v1 ns.
      v_to_list v1 = SOME (MAP (Number ∘ $& ∘ w2n) ns) ==>
      v_to_bytes (adjust_bv b2 v1) = SOME ns
Proof
  fs [v_to_bytes_def,v_to_list_adjust,MAP_MAP_o,o_DEF,adjust_bv_def,MAP_Num_11]
QED

Theorem IMP_v_to_words:
   v_to_list v2 = SOME (MAP Word64 ns') ==>
    v_to_words (adjust_bv b2 v2) = SOME ns'
Proof
  fs [v_to_words_def,v_to_list_adjust,MAP_MAP_o,o_DEF,adjust_bv_def,MAP_Word_11]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [MAP_Word_11]
QED

val sorted_lt_append =
  Q.ISPEC`prim_rec$<`SORTED_APPEND
  |> SIMP_RULE std_ss [transitive_LESS]

Theorem aux_code_installed_sublist:
   ∀aux ls.
    IS_SUBLIST ls aux ∧
    ALL_DISTINCT (MAP FST ls) ⇒
    aux_code_installed aux (fromAList ls)
Proof
  Induct >> simp[aux_code_installed_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  Cases >> simp[IS_SUBLIST] >> strip_tac >- (
    simp[aux_code_installed_def,lookup_fromAList] >>
    first_x_assum match_mp_tac >>
    var_eq_tac >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[IS_SUBLIST_APPEND,IS_PREFIX_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l`>>simp[] ) >>
  simp[aux_code_installed_def,lookup_fromAList] >>
  reverse conj_tac >- (
    first_x_assum match_mp_tac >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l'`>>simp[] ) >>
  full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
  PairCases_on`h` >>
  simp[ALOOKUP_APPEND] >>
  var_eq_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
  METIS_TAC[PAIR]
QED

Theorem compile_exps_aux_sorted:
   ∀n es c aux n1. compile_exps n es = (c,aux,n1) ⇒
   SORTED $< (MAP FST (append aux)) ∧
   EVERY (λx. ∃n. x = num_stubs + nss * n + 1) (MAP FST (append aux)) ∧
   EVERY (between (num_stubs + nss * n) (num_stubs + nss * n1)) (MAP FST (append aux)) ∧ n ≤ n1
Proof
   ho_match_mp_tac compile_exps_ind >>
   simp[compile_exps_def] >> srw_tac[][] >>
   rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >> srw_tac[][compile_aux_def] >>
   rpt ((sorted_lt_append |> match_mp_tac) >> full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
   fs[EVERY_MEM,between_def,backend_commonTheory.bvl_to_bvi_namespaces_def] >>
   srw_tac[][] >> res_tac >> (decide_tac ORELSE metis_tac[ADD_COMM,ADD_ASSOC])
QED

val in_ns_def = Define`in_ns k n ⇔ n MOD nss = k`;

Theorem nss_in_ns[simp]:
   in_ns k nss ⇔ k = 0
Proof
  rw[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

Theorem mult_nss_in_ns[simp]:
   in_ns k (m * nss) ⇔ k = 0
Proof
  rw[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

Theorem mult_nss_in_ns_1[simp]:
   in_ns k (m * nss + 1) ⇔ k = 1
Proof
  rw[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

Theorem mult_nss_in_ns_2[simp]:
   in_ns k (m * nss + 2) ⇔ k = 2
Proof
  rw[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

Theorem in_ns_1_add_1:
   in_ns 0 x ⇒ in_ns 1 (x + 1)
Proof
  rw[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def]
  \\ qspecl_then[`3`,`x`,`1`]mp_tac(Q.GENL[`n`,`x`,`k`]MOD_LIFT_PLUS_IFF)
  \\ simp[]
QED

val ODD_num_stubs = EVAL``in_ns 0 num_stubs``;

Theorem in_ns_add_num_stubs[simp]:
   in_ns k (num_stubs + x) ⇔ in_ns k x
Proof
  assume_tac ODD_num_stubs \\ fs[in_ns_def] \\
  qspecl_then[`nss`,`num_stubs`,`num_stubs MOD nss`,`x`]mp_tac ADD_MOD \\
  impl_keep_tac >- EVAL_TAC \\ simp[]
QED

val compile_list_imp = Q.prove(
  `∀n prog code n' name arity exp.
     compile_list n prog = (code,n') ∧
     ALOOKUP prog name = SOME (arity,exp) ⇒
     ∃n0 c aux n1.
     compile_exps n0 [exp] = ([c],aux,n1) ∧
     ALOOKUP (append code) (nss * name + num_stubs) = SOME (arity,bvi_let$compile_exp c) ∧
     IS_SUBLIST (append code) (append aux)`,
  Induct_on`prog` >> simp[] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  simp[compile_list_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >>
  full_simp_tac(srw_ss())[compile_single_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >>
  BasicProvers.FULL_CASE_TAC >- (
    full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    imp_res_tac compile_exps_SING >> var_eq_tac >>
    asm_exists_tac >> simp[] >>
    fs [IS_SUBLIST_APPEND] >>
    metis_tac [APPEND]) >>
  first_x_assum drule >>
  disch_then drule >> strip_tac >>
  asm_exists_tac >> simp[] >>
  conj_tac >- (
    simp[ALOOKUP_APPEND]
    \\ IF_CASES_TAC >- (pop_assum mp_tac \\ EVAL_TAC)
    \\ fs [case_eq_thms]
    \\ Cases_on `ALOOKUP (append aux) (num_stubs + name * nss)` \\ fs []
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac compile_exps_aux_sorted
    \\ fs[EVERY_MEM,EVERY_MAP] \\ res_tac \\ fs[]
    \\ qmatch_assum_rename_tac`a * nss = b * nss + 1` >>
    `in_ns 0 (a * nss)` by simp[] \\
    `in_ns 0 (b * nss + 1)` by METIS_TAC[] \\
    fs[]) >>
  full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
  metis_tac [APPEND,APPEND_ASSOC]);

val nss_lemma = prove(
  ``n * nss <> k * nss + 1``,
  strip_tac
  \\ `(n * nss) MOD nss = (k * nss + 1) MOD nss` by metis_tac [EVAL ``nss``]
  \\ sg `F` \\ fs [] \\ pop_assum mp_tac
  \\ simp_tac std_ss [MOD_MULT,EVAL ``1 < nss``,MOD_EQ_0,EVAL ``0 < nss``]);

val in_ns_0_simp = prove(
  ``in_ns 0 (nss * p_1 + num_stubs)``,
  fs [in_ns_def] \\ EVAL_TAC
  \\ `0 < nss` by EVAL_TAC \\ fs [EVAL ``nss``]);

Theorem compile_inc_lemma:
   compile_inc next1 prog1 = (next2,prog2) ==>
    (ALL_DISTINCT (MAP FST prog1) ==>
    ALL_DISTINCT (MAP FST prog2)) /\ next1 <= next2 /\
    (!p. MEM (num_stubs + p * nss) (MAP FST prog2) ==>
         MEM p (MAP FST prog1)) /\
    (!p. MEM p (MAP FST prog2) ==>
         if in_ns 0 p then (?q. num_stubs + q * nss = p) else
         in_ns 1 p /\ num_stubs + nss * next1 <= p /\
                      p < num_stubs + nss * next2)
Proof
  fs [compile_inc_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac `next1`
  \\ qid_spec_tac `prog1`
  \\ qid_spec_tac `p1`
  \\ qid_spec_tac `n1`
  \\ Induct_on `prog1` \\ fs [FORALL_PROD,compile_list_def,compile_single_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ res_tac
  \\ imp_res_tac compile_exps_aux_sorted \\ fs []
  \\ rpt strip_tac
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [nss_lemma])
  THEN1 res_tac
  THEN1
   (fs [ALL_DISTINCT_APPEND]
    \\ conj_tac THEN1
     (METIS_TAC[irreflexive_def,prim_recTheory.LESS_REFL,transitive_LESS,
        SORTED_ALL_DISTINCT])
    \\ rw [] \\ fs [EVERY_MEM] \\ res_tac
    \\ strip_tac \\ res_tac
    \\ fs [] \\ rveq \\ fs []
    \\ fs [] \\ rveq \\ fs [EVAL ``nss``]
    \\ qpat_x_assum `!e. _ ==> between _ _ e` drule
    \\ fs [between_def])
  THEN1 (CCONTR_TAC \\ fs [] \\ fs [EVAL ``nss``])
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [nss_lemma])
  \\ fs [EVAL ``nss``] \\ rveq
  \\ fs [in_ns_0_simp,GSYM (EVAL ``nss``)]
  \\ fs [EVERY_MEM] \\ res_tac \\ fs [between_def]
  \\ rveq \\ fs [EVAL ``nss``]
  \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem compile_inc_next:
   compile_inc next1 prog1 = (next2,prog2) ==>
    next1 <= next2
Proof
  rw [] \\ drule compile_inc_lemma \\ rw []
QED

Theorem compile_inc_DISTINCT:
   compile_inc next1 prog1 = (next2,prog2) /\
    ALL_DISTINCT (MAP FST prog1) ==>
    ALL_DISTINCT (MAP FST prog2)
Proof
  rw [] \\ drule compile_inc_lemma \\ rw []
QED

Theorem compile_inc_next_range:
   compile_inc next1 prog1 = (next2,prog2) /\
    MEM x (MAP FST prog2) ==>
    if in_ns_1 x then num_stubs + nss * next1 <= x /\ x < num_stubs + nss * next2
    else in_ns_0 x /\ num_stubs <= x /\ MEM ((x - num_stubs) DIV nss) (MAP FST prog1)
Proof
  rpt strip_tac
  \\ drule (GEN_ALL compile_inc_lemma)
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ Cases_on `in_ns 1 x` \\ fs [in_ns_def]
  \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [EVAL ``nss``,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
QED

val not_in_ns_1 = prove(
  ``~(in_ns_1 (num_stubs + name * nss))``,
  fs [EVAL ``nss``] \\ EVAL_TAC);

val names_nss_DIV_nss = prove(
  ``(name * nss) DIV nss = name``,
  fs [EVAL ``nss``,MULT_DIV]);

fun note_tac s g = (print ("compile_exps_correct: " ^ s ^ "\n"); ALL_TAC g)

val compile_exps_correct = Q.prove(
  `!xs env s1 n res s2 (t1:('c,'ffi) bviSem$state) n2 ys aux b1.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     (compile_exps n xs = (ys,aux,n2)) /\
     state_rel b1 s1 t1 /\
     state_ok s1 /\ EVERY (bv_ok s1.refs) env /\
     aux_code_installed (append aux) t1.code /\
     handle_ok xs /\ IS_SOME t1.global
     ==>
     ?t2 b2 c.
        (evaluate (ys,MAP (adjust_bv b2) env,inc_clock c t1) =
           (map_result (MAP (adjust_bv b2)) (adjust_bv b2) res,t2)) /\
        state_rel b2 s2 t2 /\
        (MAP (adjust_bv b1) env = MAP (adjust_bv b2) env) /\
        (!a. a IN FDOM s1.refs ==> (b1 a = b2 a))`,
  SIMP_TAC std_ss []
  \\ recInduct eval_ind_alt \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  THEN1 (* NIL *)
   (note_tac "NIL" \\ SRW_TAC [] [iEval_def]
    \\ Q.LIST_EXISTS_TAC [`b1`,`0`] \\ full_simp_tac(srw_ss())[inc_clock_ZERO])
  THEN1 (* CONS *)
   (note_tac "CONS" \\
    `?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 (y::xs) = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
    \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ TRY (impl_tac >- (spose_not_then strip_assume_tac
                         \\ full_simp_tac(srw_ss())[]))
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ full_simp_tac(srw_ss())[]
    \\ `res6 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1`
           \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ `aux_code_installed (append aux2) t2.code` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
      \\ match_mp_tac aux_code_installed_subspt
      \\ asm_exists_tac \\ fs [])
    \\ first_x_assum (qspecl_then [`t2`,`b2`] mp_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ `s2 = s6` by (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate (c2,MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res6` \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `xx = res` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
    \\ asm_exists_tac \\ fs [])
  THEN1 (* Var *)
   (note_tac "Var" \\
    Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[iEval_def] \\ Q.LIST_EXISTS_TAC [`b1`,`0`]
    \\ full_simp_tac(srw_ss())[inc_clock_ZERO,EL_MAP])
  THEN1 (* If *)
   (note_tac "If" \\
    Q.ABBREV_TAC `n4 = n2` \\ POP_ASSUM (K ALL_TAC)
    \\ `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2 [x3] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ TRY (
      impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `d1 = Boolv T` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux2) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF])
    \\ Cases_on `d1 = Boolv F` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d3. c3 = [d3]` by (Cases_on `c3` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n2`) \\ full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux3) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]))
  THEN1 (* Let *)
   (note_tac "Let" \\ reverse (Cases_on `NULL xs`) THEN1
     (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
      \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[PULL_FORALL]
      \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ full_simp_tac(srw_ss())[LENGTH_NIL,NULL_EQ]
      \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
      \\ TRY (
        impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
        \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
        \\ `?d. c2 = [d]` by (Cases_on `c2` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
        \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
        \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
        \\ srw_tac[][] \\ NO_TAC)
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate ([x2],a ++ env,s5) = (res6,s6)`
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`)
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c2 = [d]` by (Cases_on `c2`
           \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux2) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ Q.MATCH_ASSUM_RENAME_TAC
          `evaluate ([d],MAP (adjust_bv b3) a ++
                      MAP (adjust_bv b3) env,inc_clock c4 t2) =
             (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
      \\ IMP_RES_TAC evaluate_inv_clock
      \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ ONCE_REWRITE_TAC [iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[MAP_APPEND_MAP_EQ]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF])
    \\ fs [LENGTH_NIL,NULL_EQ] \\ rveq \\ fs [bvlSemTheory.evaluate_def]
    \\ Cases_on `x2` \\ fs [bvl_handleProofTheory.let_ok_def,destLet_def]
    \\ ntac 2 (pairarg_tac \\ fs []) \\ rveq \\ fs []
    \\ fs [bviSemTheory.evaluate_def,bvlSemTheory.evaluate_def]
    \\ Cases_on `evaluate (l,env,s)` \\ fs []
    \\ `exp1_size l ≤ exp_size (Let l e)` by fs [bvlTheory.exp_size_def]
    \\ first_assum drule \\ disch_then drule
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs []
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac THEN1
     (ntac 3 (IMP_RES_TAC aux_code_installed_APPEND \\ fs[])
      \\ match_mp_tac bvl_handleProofTheory.handle_ok_Var_Const_list \\ fs []
      \\ fs [EVERY_MEM] \\ rpt strip_tac
      \\ first_x_assum drule \\ Cases_on `x` \\ fs [isVar_def])
    \\ strip_tac \\ fs []
    \\ reverse (Cases_on `q`)
    \\ fs [semanticPrimitivesPropsTheory.map_result_def] \\ rveq \\ fs []
    THEN1 (Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs [find_code_def])
    \\ ntac 3 (IMP_RES_TAC aux_code_installed_APPEND \\ fs[])
    \\ fs [aux_code_installed_def,compile_aux_def]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac compile_exps_LENGTH \\ fs []
    \\ `exp1_size [e] ≤ exp_size (Let l e)` by fs [bvlTheory.exp_size_def]
    \\ ntac 3 (qpat_x_assum `!x y. _` kall_tac)
    \\ `r = s` by
     (drule (evaluate_Var_list
         |> INST_TYPE [beta|->``:'ffi``,alpha|->``:num # 'c``] |> GEN_ALL)
      \\ disch_then (qspecl_then [`s`,`env`] mp_tac) \\ fs []) \\ rveq
    \\ first_x_assum drule
    \\ `evaluate ([e],a,r) = (res,s2)` by
     (qpat_x_assum `_ = (res,s2)` (fn th => once_rewrite_tac [GSYM th])
      \\ match_mp_tac (GSYM bEval_bVarBound) \\ fs [] \\ NO_TAC)
    \\ rpt (disch_then drule \\ fs [])
    \\ impl_tac
    THEN1
     (rpt strip_tac \\ fs[handle_ok_def]
      \\ imp_res_tac bviPropsTheory.evaluate_code_mono \\ fs [inc_clock_def]
      \\ TRY (match_mp_tac aux_code_installed_subspt \\ asm_exists_tac \\ fs [])
      \\ imp_res_tac evaluate_global_mono
      \\ fs [inc_clock_def]
      \\ imp_res_tac EVERY_isVar_evaluate_Rval_MEM
      \\ fs [EVERY_MEM] \\ metis_tac [])
    \\ strip_tac
    \\ qpat_x_assum `evaluate (c2,_) = _` mp_tac
    \\ drule bviPropsTheory.evaluate_add_clock \\ simp[]
    \\ disch_then (qspec_then `c'+1` mp_tac) \\ strip_tac
    \\ `inc_clock (c'+1) (inc_clock c t1) = inc_clock (c+c'+1) t1` by
          (fs [inc_clock_def] \\ NO_TAC)
    \\ fs [] \\ strip_tac
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c+c'+1`]
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `r.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC \\ NO_TAC)
    \\ fs [find_code_def]
    \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\ fs [LENGTH_NIL]) \\ rveq \\ fs []
    \\ drule bvi_letProofTheory.evaluate_compile_exp
    \\ impl_tac THEN1 (Cases_on `res` \\ fs [semanticPrimitivesPropsTheory.map_result_def])
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_code_mono \\ fs [subspt_lookup]
    \\ res_tac \\ fs []
    \\ `dec_clock 1 (inc_clock (c' + 1) t2) = inc_clock c' t2` by
           (EVAL_TAC \\ fs [] \\ NO_TAC)
    \\ fs [] \\ Cases_on `res` \\ fs [semanticPrimitivesPropsTheory.map_result_def]
    \\ Cases_on `e'` \\ fs [semanticPrimitivesPropsTheory.map_error_result_def])
  THEN1 (* Raise *)
   (note_tac "Raise" \\
    `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[iEval_def] \\ NO_TAC)
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ SRW_TAC [] [])
  THEN1 (* Handle *)
   (note_tac "Handle" \\
    Cases_on `x1` \\ full_simp_tac(srw_ss())[handle_ok_def,destLet_def]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac compile_exps_Var_list
    \\ first_x_assum(qspec_then`n`strip_assume_tac)
    \\ full_simp_tac (srw_ss()) []
    \\ `?c2 aux2 n2. compile_exps n [e] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2' [x2] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ Q.ISPECL_THEN[`s1`,`l`]mp_tac (Q.GEN`s`evaluate_Var_list)
    \\ full_simp_tac(srw_ss())[]
    \\ STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `evaluate ([e],vs ++ env,s1) = evaluate ([e],vs,s1)` by (MATCH_MP_TAC bEval_bVarBound \\ fs[])
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `evaluate ([e],vs,s1)` \\ full_simp_tac(srw_ss())[]
    \\ `?d2. c2 = [d2]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c2`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ `?d3. c3 = [d3]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c3`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ full_simp_tac(srw_ss())[] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ `handle_ok l` by
     (match_mp_tac bvl_handleProofTheory.handle_ok_Var_Const_list \\ fs []
      \\ fs [EVERY_MEM] \\ rpt strip_tac
      \\ first_x_assum drule \\ Cases_on `x` \\ fs [isVar_def])
    \\ `exp1_size [e] <= exp_size (Let l e)` by
           (fs [bvlTheory.exp_size_def] \\ NO_TAC)
    \\ first_x_assum drule \\ fs [] \\ strip_tac
    \\ `EVERY (bv_ok s1.refs) vs` by
     (imp_res_tac evaluate_IMP_bv_ok
      \\ IMP_RES_TAC evaluate_ok \\ rfs [] \\ NO_TAC)
    \\ (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Result case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (Q.SPECL_THEN [`t1`,`b1`]mp_tac)
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,
           iEval_def,find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac bviPropsTheory.evaluate_code_mono \\ fs [subspt_lookup]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[] \\ fs []
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[] \\ rw []
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
    \\ (Cases_on`e'`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Raise case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.PAT_X_ASSUM `!nn mm nn1. bbb` (MP_TAC o Q.SPEC `n2'`)
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ fs []
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac evaluate_global_mono
        \\ full_simp_tac(srw_ss())[inc_clock_def]
        \\ sg `EVERY (bv_ok r.refs) env` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ IMP_RES_TAC bv_ok_SUBSET_IMP
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c' + c + 1) t1) = inc_clock (c' + c) t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ `MAP (adjust_bv b2) vs = MAP (adjust_bv b2') vs` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `r.refs` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
      \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ full_simp_tac(srw_ss())[SUBSET_DEF]
      \\ qpat_x_assum `!n. _ = _` (qspec_then `c'` assume_tac) \\ fs []
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
    THEN1 (* abort case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,
            find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC))
  THEN1 (* Op *)
   (note_tac "Op" \\
    `?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ fs [] \\ first_x_assum drule \\ fs []
    THEN1 (
      REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`op = Install` THEN1
       (fs[compile_op_def]
        \\ qexists_tac`c` \\ simp[] \\ rw []
        \\ fs [evaluate_def])
      \\ Cases_on`op = CopyByte T`
      >- (note_tac "Op: CopyByte" \\
        fs[compile_op_def]
        \\ qexists_tac`c` \\ simp[]
        \\ rw[evaluate_APPEND,bviSemTheory.evaluate_def] )
      \\ Cases_on `op`
      \\ fs[compile_op_def,iEval_def,compile_int_thm,iEval_append]
      \\ qexists_tac`c`>>simp[]>>
         every_case_tac \\ full_simp_tac(srw_ss())[iEval_def,compile_int_thm]
      \\ imp_res_tac compile_exps_LENGTH
      \\ fs [NULL_EQ,LENGTH_NIL]
      \\ Cases_on `xs` \\ fs [bviSemTheory.evaluate_def])
    \\ REPEAT STRIP_TAC \\ Cases_on `do_app op (REVERSE a) s5`
    \\ full_simp_tac(srw_ss())[]
    \\ TRY(
      qmatch_asmsub_abbrev_tac `do_app _ _ _ = Rerr _` >>
      srw_tac[][] >>
      CHANGED_TAC(imp_res_tac bvlPropsTheory.do_app_err) >>
      rveq >> fs[] >> fs[bvlSemTheory.do_app_def] >>
      simp[evaluate_def,compile_op_def] >>
      MAP_EVERY qexists_tac [`t2`,`b2`,`c`] >>
      simp[] >>
      fs[do_app_def,do_app_aux_def] >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
      fs[bvlSemTheory.do_app_def] >> Cases_on `a` >> fs[] >>
      rpt(PURE_FULL_CASE_TAC >> fs[adjust_bv_def] >> rveq) >>
      fs[GSYM PULL_FORALL] >>
      imp_res_tac state_rel_FLOOKUP_byteArray >>
      fs[] >> rveq >> rfs[state_rel_def])
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Cases_on`a'`>>full_simp_tac(srw_ss())[]\\srw_tac[][]
    \\ Cases_on `op = Install` \\ full_simp_tac(srw_ss())[] THEN1 (
      rveq \\ fs [compile_op_def]
      \\ `LENGTH a = 2` by
       (fs [bvlSemTheory.do_app_def,bvlSemTheory.do_install_def,
            case_eq_thms,UNCURRY] \\ rveq \\ fs [SWAP_REVERSE_SYM])
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ fs [bvlSemTheory.do_app_def,bvlSemTheory.do_install_def,
             case_eq_thms,UNCURRY] \\ rveq
      \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ `lookup ListLength_location t2.code = SOME ListLength_code` by
              (fs [state_rel_def] \\ NO_TAC) \\ fs []
      \\ fs [EVAL ``ListLength_code``] \\ fs [GSYM (EVAL ``SND ListLength_code``)]
      \\ drule (GEN_ALL evaluate_ListLength_code)
      \\ fs [v_to_bytes_def,some_def]
      \\ rfs [MAP_Num_11,o_DEF] \\ rveq
      \\ disch_then (qspec_then `adjust_bv b2 v1` mp_tac) \\ fs []
      \\ simp [v_to_list_adjust]
      \\ disch_then (qspec_then `0` strip_assume_tac)
      \\ drule (GEN_ALL evaluate_ListLength_code)
      \\ fs [v_to_words_def,some_def]
      \\ rfs [MAP_Word_11,o_DEF] \\ rveq
      \\ disch_then (qspec_then `adjust_bv b2 v2` mp_tac) \\ fs []
      \\ simp [v_to_list_adjust]
      \\ disch_then (qspec_then `0` strip_assume_tac) \\ fs []
      \\ qexists_tac `c + c' + c'' + 2`
      \\ ntac 2 (pop_assum mp_tac)
      \\ drule bviPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `c'+c''+2` assume_tac)
      \\ rpt strip_tac
      \\ drule bviPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `c'+1` assume_tac)
      \\ fs [inc_clock_ADD]
      \\ fs [evaluate_def,EVAL ``bviSem$do_app (Const 0) [] t2``,
             bvlSemTheory.find_code_def,dec_clock_inc_clock]
      \\ fs [do_install_def,do_app_def]
      \\ imp_res_tac IMP_v_to_bytes \\ fs []
      \\ imp_res_tac IMP_v_to_words \\ fs []
      \\ `t2.compile_oracle = state_co compile_inc s5.compile_oracle ∧
          s5.compile = state_cc compile_inc t2.compile`
              by fs [state_rel_def]
      \\ fs [state_co_def]
      \\ Cases_on `s5.compile_oracle 0` \\ fs []
      \\ PairCases_on `q` \\ fs []
      \\ qabbrev_tac `prog1 = (k,prog)::v7`
      \\ Cases_on `compile_inc q0 prog1` \\ fs [] \\ rveq
      \\ rename1 `compile_inc next1 prog1 = (next2,prog2)`
      \\ fs [state_cc_def,case_eq_thms] \\ rveq \\ fs [PULL_EXISTS]
      \\ simp [adjust_bv_def,shift_seq_def,UNCURRY]
      \\ Cases_on `shift_seq 1 s5.compile_oracle 0` \\ fs [] \\ rveq \\ fs []
      \\ pop_assum mp_tac
      \\ simp [adjust_bv_def,shift_seq_def,UNCURRY]
      \\ fs [state_rel_def,lookup_union] \\ strip_tac
      \\ simp [GSYM PULL_EXISTS,state_co_def,UNCURRY,case_eq_thms]
      \\ qpat_x_assum `names_ok _ _ _` assume_tac
      \\ conj_tac THEN1
       (fs [v_to_bytes_def,v_to_list_adjust,o_DEF,adjust_bv_def,MAP_MAP_o,
            MAP_Num_11])
      \\ conj_asm1_tac THEN1
       (simp [IN_DISJOINT] \\ CCONTR_TAC \\ fs [] \\ fs [names_ok_def]
        \\ rfs [] \\ first_x_assum drule
        \\ impl_tac >-  (
          imp_res_tac compile_inc_next_range
          \\ pop_assum mp_tac \\ rw[] )
        \\ IF_CASES_TAC \\ fs []
        \\ imp_res_tac compile_inc_next_range \\ rfs [EVAL ``nss``]
        \\ `DISJOINT (domain s5.code) (set (MAP FST prog1))` by fs [Abbr`prog1`]
        \\ pop_assum mp_tac \\ rewrite_tac [IN_DISJOINT]
        \\ strip_tac \\ fs []
        \\ pop_assum (qspec_then `(x - num_stubs) DIV nss` strip_assume_tac)
        \\ fs [EVAL ``nss``])
      \\ conj_asm1_tac THEN1
       (rfs [names_ok_def]
        \\ imp_res_tac compile_inc_DISTINCT \\ rfs [Abbr`prog1`])
      \\ conj_tac THEN1
       (fs [compile_inc_def,compile_list_def,Abbr `prog1`]
        \\ PairCases_on `prog` \\ fs [compile_single_def]
        \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [])
      \\ fs [state_cc_def,state_co_def]
      \\ rfs [] \\ fs [FUN_EQ_THM,FORALL_PROD]
      \\ qpat_x_assum `!x. _ = _` (qspec_then `0` mp_tac) \\ fs []
      \\ strip_tac \\ fs []
      \\ conj_tac THEN1
       (fs [names_ok_def,domain_union] \\ rfs [] \\ rveq \\ fs []
        \\ drule (GEN_ALL compile_inc_next)
        \\ strip_tac \\ fs []
        \\ rpt strip_tac
        THEN1 (res_tac \\ fs [] \\ rw [] \\ fs [EVAL ``nss``])
        THEN1 (res_tac \\ fs [] \\ rw [] \\ fs [EVAL ``nss``])
        \\ fs [domain_fromAList]
        \\ drule (GEN_ALL compile_inc_next_range) \\ fs []
        \\ disch_then drule \\ fs []
        \\ rw [] \\ fs [])
      \\ reverse (rpt strip_tac) \\ rveq \\ fs []
      THEN1
       (first_x_assum drule \\ strip_tac
        \\ pairarg_tac \\ fs []
        \\ drule compile_exps_SING \\ strip_tac \\ fs [] \\ rveq
        \\ rename1 `compile_exps n6 [exp] = _`
        \\ qexists_tac `n6` \\ fs []
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs []
        \\ fs [subspt_lookup,lookup_union])
      \\ `lookup (num_stubs + name * nss) t2.code = NONE` by
       (fs [names_ok_def,domain_lookup,PULL_EXISTS]
        \\ Cases_on `lookup (num_stubs + name * nss) t2.code` \\ fs []
        \\ first_x_assum drule
        \\ fs [names_nss_DIV_nss,not_in_ns_1]) \\ fs []
      \\ fs [lookup_fromAList,compile_inc_def]
      \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
      \\ drule compile_list_imp
      \\ disch_then drule \\ strip_tac
      \\ qexists_tac `n0` \\ fs []
      \\ conj_tac THEN1
       (match_mp_tac aux_code_installed_subspt
        \\ qexists_tac `(fromAList (append p1))`
        \\ reverse conj_tac THEN1
         (fs [subspt_lookup,lookup_union] \\ rw [] \\ simp [case_eq_thms]
          \\ fs [IN_DISJOINT]
          \\ rename1 `lookup kk _ = _`
          \\ first_x_assum (qspec_then `kk` mp_tac)
          \\ fs [lookup_fromAList] \\ imp_res_tac ALOOKUP_MEM
          \\ fs [domain_lookup]
          \\ Cases_on `lookup kk t2.code` \\ fs []
          \\ fs [MEM_MAP,FORALL_PROD] \\ PairCases_on `y` \\ metis_tac [])
        \\ match_mp_tac aux_code_installed_sublist \\ fs [])
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs [names_ok_def]
      \\ qpat_x_assum `!n k. _` (qspec_then `0` mp_tac) \\ fs []
      \\ fs [EVERY_MEM,FORALL_PROD] \\ metis_tac[])
    \\ Cases_on `?i. op = Const i` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: Const" \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[compile_op_def] \\ Cases_on `c1`
      \\ full_simp_tac(srw_ss())[compile_int_thm,bEvalOp_def,iEval_def]
      \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[iEval_def,iEvalOp_def]
      \\ full_simp_tac(srw_ss())[EVAL ``do_app_aux (Const 0) [] t2``]
      \\ SRW_TAC [] [adjust_bv_def])
    \\ Cases_on `∃n. op = Label n` THEN1
     (note_tac "Op: Label" \\
      fs[compile_op_def,evaluate_def,case_eq_thms] \\ rveq \\
      fs[do_app_def,do_app_aux_def,bvlSemTheory.do_app_def,
         case_eq_thms,bool_case_eq] \\
      CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`b2` \\
      CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`c` \\ simp[] \\ rveq \\
      simp[adjust_bv_def]
      \\ fs[state_rel_def,domain_lookup]
      \\ imp_res_tac evaluate_mono \\ fs [subspt_lookup,domain_lookup]
      \\ res_tac \\ fs []
      \\ Cases_on`v` \\ res_tac
      \\ pairarg_tac \\ fs[])
    \\ Cases_on `?i. op = FromList i` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: FromList" \\ fs [compile_op_def] \\ rveq
      \\ fs [bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ fs [] \\ Cases_on `t` \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `v_to_list h` \\ fs []
      \\ drule evaluate_IMP_LENGTH \\ rveq
      \\ Cases_on `c1` \\ fs [LENGTH_NIL]
      \\ strip_tac \\ rveq \\ fs []
      \\ qexists_tac `t2`
      \\ qexists_tac `b2`
      \\ `lookup ListLength_location t2.code = SOME ListLength_code` by
              (fs [state_rel_def] \\ NO_TAC) \\ fs []
      \\ fs [EVAL ``ListLength_code``] \\ fs [GSYM (EVAL ``SND ListLength_code``)]
      \\ `v_to_list (adjust_bv b2 h) = SOME (MAP (adjust_bv b2) x)` by
             fs [v_to_list_adjust]
      \\ drule evaluate_ListLength_code
      \\ disch_then drule \\ fs []
      \\ disch_then (qspec_then `0` strip_assume_tac)
      \\ qexists_tac `c+1+c'`
      \\ fs [bviSemTheory.evaluate_def,EVAL ``bviSem$do_app (Const 0) [] t2``]
      \\ qpat_assum `evaluate ([h'],_) = _` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `1+c'` assume_tac)
      \\ fs [inc_clock_ADD]
      \\ fs [find_code_def]
      \\ `dec_clock 1 (inc_clock (c' + 1) t2) = inc_clock c' t2` by
            (fs [dec_clock_def,inc_clock_def,
                 bviSemTheory.state_component_equality] \\ NO_TAC)
      \\ fs [] \\ fs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def]
      \\ fs [adjust_bv_def] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ Cases_on `op = Ref` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: Ref" \\ rw [] \\
      full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[do_app_Ref]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]) \\ fs []
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
      THEN1
        (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
         \\ fs [bvlSemTheory.do_app_def] \\ every_case_tac \\ fs []
         \\ rveq \\ fs [adjust_bv_def,APPLY_UPDATE_THM])
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,
            bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ STRIP_TAC
      \\ fs [bvl_do_app_Ref] \\ rveq
      THEN1 (Q.UNABBREV_TAC `b3` \\ fs []
             \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ fs [MAP_REVERSE]
      \\ Cases_on `FLOOKUP s5.refs k = NONE`
      \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3`
        \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC
        \\ full_simp_tac(srw_ss())[] \\ NO_TAC))
      \\ TRY (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
           \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ rfs [] \\ NO_TAC)
      \\ (`b3 k = b2 k` by
           (Q.UNABBREV_TAC `b3`
            \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF] \\ NO_TAC))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
      \\ qexists_tac `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `op = RefArray` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: RefArray" \\
      full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`0 ≤ i` >>full_simp_tac(srw_ss())[]
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ simp[FLOOKUP_UPDATE]
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ simp[map_replicate]
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`∃flag. op = RefByte flag` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "RefByte" \\ full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM]
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`X = Rval Y`mp_tac
      \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ rpt var_eq_tac
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IF_CASES_TAC \\ fs[] \\ rveq \\ fs[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >>
        NO_TAC)
      \\ TRY (
        qmatch_rename_tac`t2.global ≠ SOME p` >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[])
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`∃n. op = Global n` \\ full_simp_tac(srw_ss())[] THEN1 (
         note_tac "Global" >> simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         full_simp_tac(srw_ss())[LENGTH_NIL] >>
         simp[iEval_def,compile_int_thm] >>
         Q.LIST_EXISTS_TAC[`t2`,`b2`,`c`] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
         simp[bEvalOp_def] >>
         full_simp_tac(srw_ss())[closSemTheory.get_global_def] >>
         imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >> full_simp_tac(srw_ss())[LENGTH_NIL] >>
         full_simp_tac(srw_ss())[bEval_def] >> rpt var_eq_tac >>
         full_simp_tac(srw_ss())[iEval_def] >> rpt var_eq_tac >>
         last_x_assum mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[LENGTH_REPLICATE,ADD1] >>
         simp[EL_CONS,PRE_SUB1] >>
         reverse IF_CASES_TAC >>
         every_case_tac >> fsrw_tac[ARITH_ss][] >>
         rpt var_eq_tac >>
         simp[EL_APPEND1,EL_MAP,libTheory.the_def,bvl_to_bvi_with_clock,bvl_to_bvi_id] >>
         MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) >>
         qexists_tac`r.refs`>>simp[] >>
         full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
         first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
         simp[])
    \\ Cases_on`∃n. op = SetGlobal n` \\ full_simp_tac(srw_ss())[] THEN1 (
         note_tac "Op: SetGlobal" >> simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
         Cases_on`t`>>full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         Cases_on`c1`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> srw_tac[][] >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         simp[iEval_def] >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c`,`b2`] >>
         simp[compile_int_thm] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         imp_res_tac evaluate_global_mono >>
         BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
         simp[bEvalOp_def] >>
         qhdtm_x_assum`state_rel`mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[ADD1,LENGTH_REPLICATE] >>
         reverse IF_CASES_TAC >>
         fsrw_tac[ARITH_ss][closSemTheory.get_global_def] >>
         simp[bvl_to_bvi_with_refs,bvl_to_bvi_id,LUPDATE_def,GSYM ADD1] >>
         simp[ADD1,LUPDATE_APPEND1] >>
         full_simp_tac(srw_ss())[state_rel_def] >>
         simp[FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         srw_tac[][] >- ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> srw_tac[][] >> METIS_TAC[] ) >>
         qexists_tac`z` >> simp[ADD1,LUPDATE_MAP] >>
         simp[libTheory.the_def])
    \\ Cases_on`op = AllocGlobal` \\ full_simp_tac(srw_ss())[] THEN1 (
         note_tac "Op: AllocGlobal" >> simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
         imp_res_tac evaluate_IMP_LENGTH >>
         full_simp_tac(srw_ss())[LENGTH_NIL] >> srw_tac[][] >>
         srw_tac[][iEval_def] >>
         simp[Once inc_clock_def] >>
         simp[find_code_def] >>
         `lookup AllocGlobal_location t1.code = SOME(0,SND AllocGlobal_code)` by (
           full_simp_tac(srw_ss())[state_rel_def] >> simp[AllocGlobal_code_def] ) >>
         simp[] >>
         let
           val th = (Q.ISPEC`inc_clock c (t1:('c,'ffi) bviSem$state)`(Q.GEN`s`evaluate_AllocGlobal_code))
         in
         Q.SUBGOAL_THEN `∃p n ls. ^(fst(dest_imp(concl th)))` assume_tac
         THEN1 (
           full_simp_tac(srw_ss())[state_rel_def,REPLICATE_NIL] >>
           simp[Once inc_clock_def] >>
           simp[CopyGlobals_code_def] >>
           Cases_on`t1.global`>>full_simp_tac(srw_ss())[])
         end >>
         rpt(pop_assum CHOOSE_TAC) >>
         first_assum(mp_tac o MATCH_MP evaluate_AllocGlobal_code) >>
         disch_then(qx_choosel_then[`p1`,`ck`]strip_assume_tac) >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c+ck+1`,`b2`] >>
         simp[Once inc_clock_def] >>
         `dec_clock 1 (inc_clock (c + (ck+1)) t1) =
          inc_clock ck (inc_clock c t1)` by (
           EVAL_TAC >> simp[state_component_equality] ) >>
         simp[] >>
         ntac 2 (pop_assum kall_tac) >>
         full_simp_tac(srw_ss())[iEval_def] >> var_eq_tac >>
         full_simp_tac(srw_ss())[state_rel_def,LENGTH_REPLICATE,FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         conj_tac >- (
           gen_tac >>
           Cases_on`FLOOKUP s5.refs k`>>simp[]>>
           `p ≠ b2 k` by ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[]) >>
           `p1 ≠ b2 k` by (
             full_simp_tac(srw_ss())[INJ_DEF,FLOOKUP_DEF] >>
             METIS_TAC[] ) >>
           simp[] >>
           rpt(first_x_assum(qspec_then`k`mp_tac)) >>
           simp[] ) >>
         conj_tac >- (
           full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[INJ_DEF]) >>
         IF_CASES_TAC >- (
           qexists_tac`z'`>>simp[libTheory.the_def]>>
           simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,EL_REPLICATE] >>
           Cases >> simp[EL_REPLICATE] ) >>
         qexists_tac`z' * 2`>>simp[libTheory.the_def] >>
         qmatch_abbrev_tac`REPLICATE a x ++ [x] ++ REPLICATE b x = _` >>
         `REPLICATE a x ++ [x] ++ REPLICATE b x = REPLICATE (a + SUC b) x`
         by simp[GSYM REPLICATE_APPEND] >>
         `a + SUC b = SUC (a + b)` by simp[] >>
         rw[] >>
         simp[LIST_EQ_REWRITE,Abbr`a`,Abbr`b`,LENGTH_REPLICATE,EL_REPLICATE])
    \\ Cases_on`∃str. op = String str` \\ fs[] >- (
      note_tac "Op: String" \\ fs[compile_op_def,bEvalOp_def]
      \\ Cases_on`REVERSE a` \\ fs[] \\ rw[]
      \\ simp[iEval_def,compile_int_thm]
      \\ qmatch_goalsub_abbrev_tac`_ |+ (ptr,_)`
      \\ qabbrev_tac`b2' = (ptr =+ (LEAST ptr. ptr ∉ FDOM (bvi_to_bvl t2).refs)) b2`
      \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `s5.refs` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM]
        \\ simp[Abbr`b2'`,Abbr`ptr`,APPLY_UPDATE_THM]
        \\ rw[] \\ fs[LEAST_NOTIN_FDOM] \\ NO_TAC)
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2'`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ simp[adjust_bv_def,Abbr`b2'`,APPLY_UPDATE_THM]
      \\ simp[iEvalOp_def,do_app_aux_def,bEvalOp_def,backend_commonTheory.small_enough_int_def]
      \\ reverse IF_CASES_TAC \\ fs[]
      >- (first_x_assum(qspec_then`0w`mp_tac) \\ simp[])
      \\ qmatch_goalsub_abbrev_tac`RefPtr ptr'::MAP _ env,ss`
      \\ qmatch_asmsub_abbrev_tac`ByteArray T ls`
      \\ qspecl_then[`str`,`ls`,`ptr'`,`ss`,`MAP (adjust_bv b2) env`]mp_tac compile_string_thm
      \\ impl_tac >- simp[Abbr`ss`,FLOOKUP_UPDATE,Abbr`ls`,LENGTH_REPLICATE]
      \\ simp[] \\ disch_then kall_tac
      \\ simp[LENGTH_REPLICATE,Abbr`ls`,EL_APPEND1,EL_APPEND2]
      \\ qpat_x_assum`0 = _`(SUBST_ALL_TAC o SYM) \\ simp[]
      \\ reverse conj_tac
      >- (
        rw[Abbr`ptr`]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ fs[SUBSET_DEF]
        \\ res_tac \\ fs[LEAST_NOTIN_FDOM] )
      \\ fs[state_rel_def,Abbr`ptr'`,Abbr`ss`]
      \\ conj_tac
      >- (
        MATCH_MP_TAC INJ_EXTEND
        \\ fs[Abbr`ptr`,LEAST_NOTIN_FDOM] )
      \\ conj_tac
      >- (
        rw[FLOOKUP_UPDATE,APPLY_UPDATE_THM] \\ fs[]
        >- (
          CASE_TAC \\ fs[]
          \\ fs[INJ_DEF,FLOOKUP_DEF]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ qpat_x_assum`∀k. option_CASE _ _ _`(qspec_then`k`mp_tac)
        \\ CASE_TAC \\ fs[]
        \\ CASE_TAC \\ fs[] \\ rw[]
        \\ imp_res_tac evaluate_ok
        \\ fs[state_ok_def]
        \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
        \\ simp[MAP_EQ_f] \\ rw[] \\ fs[EVERY_MEM]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ simp[APPLY_UPDATE_THM] \\ rw[]
        \\ fs[Abbr`a`,LEAST_NOTIN_FDOM] )
      \\ simp[FLOOKUP_UPDATE,APPLY_UPDATE_THM]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ rw[]
      >- ( simp[FLOOKUP_DEF,LEAST_NOTIN_FDOM] )
      >- ( rw[] )
      >> simp[o_DEF]
      \\ qexists_tac`z` \\ simp[]
      \\ simp[MAP_EQ_f]
      \\ Cases \\ simp[libTheory.the_def]
      \\ rw[]
      \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq)
      \\ qexists_tac `s5.refs`
      \\ simp[APPLY_UPDATE_THM]
      \\ imp_res_tac evaluate_ok
      \\ fs[state_ok_def,EVERY_MEM]
      \\ res_tac \\ fs[] \\ rw[]
      \\ fs[Abbr`a`,LEAST_NOTIN_FDOM] )
    \\ Cases_on`∃str. op = FromListByte` \\ fs[] >- (
      note_tac "Op: FromListByte" \\ fs[compile_op_def,bEvalOp_def]
      \\ `∃lv. REVERSE a = [lv]` by (every_case_tac \\ fs[]) \\ fs[]
      \\ qpat_x_assum`_ = Rval _`mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[]
      \\ rpt strip_tac
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
      \\ simp[Once iEval_def]
      \\ `lookup ListLength_location t2.code = SOME (2,SND ListLength_code)`
      by ( fs[state_rel_def,ListLength_code_def])
      \\ qabbrev_tac`p = (LEAST ptr. ptr ∉ FDOM (bvi_to_bvl t2).refs)`
      \\ qmatch_goalsub_abbrev_tac`_ |+ (ptr,_)`
      \\ qabbrev_tac`b2' = (ptr =+ p) b2`
      \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `s5.refs` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM]
        \\ simp[Abbr`b2'`,Abbr`ptr`,APPLY_UPDATE_THM]
        \\ rw[] \\ fs[LEAST_NOTIN_FDOM] \\ NO_TAC)
      \\ `v_to_list (adjust_bv b2 lv) = v_to_list lv`
      by (simp[v_to_list_adjust,MAP_MAP_o,o_DEF,adjust_bv_def])
      \\ rfs[]
      \\ drule evaluate_ListLength_code
      \\ disch_then drule \\ simp[]
      \\ disch_then(qspec_then`0`(qx_choose_then`cl`strip_assume_tac))
      \\ drule (Q.GENL[`p`,`fl`]evaluate_FromListByte_code)
      \\ qabbrev_tac`bs = REPLICATE (LENGTH x) (0w:word8)`
      \\ disch_then(qspecl_then[`p`,`T`,`0`,`bs`,`t2 with refs := t2.refs |+ (p,ByteArray T bs)`]mp_tac)
      \\ simp[LENGTH_REPLICATE,Abbr`bs`,FLOOKUP_UPDATE]
      \\ impl_keep_tac >- fs[state_rel_def,FromListByte_code_def]
      \\ disch_then(qx_choose_then`cf`strip_assume_tac)
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2'`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `(cf+1) + (cl+1) + c`
      \\ qspecl_then[`[h]`,`MAP _ env`]drule evaluate_add_clock
      \\ simp[GSYM inc_clock_ADD]
      \\ disch_then(qspec_then`cf+1 + cl+1`mp_tac)
      \\ simp[GSYM inc_clock_ADD]
      \\ disch_then kall_tac
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ simp[find_code_def]
      \\ simp[inc_clock_def,dec_clock_def]
      \\ qspecl_then[`[SND ListLength_code]`]drule evaluate_add_clock
      \\ simp[]
      \\ disch_then(qspec_then`cf+1`mp_tac)
      \\ simp[inc_clock_def]
      \\ disch_then kall_tac
      \\ simp[iEvalOp_def,do_app_aux_def]
      \\ reverse IF_CASES_TAC \\ fs[]
      >- ( first_x_assum(qspec_then`0w`mp_tac) \\ simp[] )
      \\ Cases_on`w` \\ fs[] \\ rveq \\ fs[]
      \\ fs[inc_clock_def,adjust_bv_def,Abbr`b2'`,APPLY_UPDATE_THM]
      \\ reverse conj_tac
      >- (
        rw[Abbr`ptr`]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ fs[SUBSET_DEF]
        \\ res_tac \\ fs[LEAST_NOTIN_FDOM] )
      \\ fs[state_rel_def]
      \\ conj_tac
      >- (
        MATCH_MP_TAC INJ_EXTEND
        \\ fs[Abbr`ptr`,LEAST_NOTIN_FDOM,Abbr`p`] )
      \\ fs[v_to_list_adjust] \\ rfs[] \\ rveq
      \\ fs[MAP_MAP_o,o_DEF,adjust_bv_def]
      \\ conj_tac
      >- (
        rw[FLOOKUP_UPDATE,APPLY_UPDATE_THM] \\ fs[]
        >- (
          CASE_TAC \\ fs[]
          \\ fs[INJ_DEF,FLOOKUP_DEF]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ qpat_x_assum`∀k. option_CASE _ _ _`(qspec_then`k`mp_tac)
        \\ CASE_TAC \\ fs[]
        \\ CASE_TAC \\ fs[] \\ rw[]
        \\ imp_res_tac evaluate_ok
        \\ fs[state_ok_def]
        \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
        \\ simp[MAP_EQ_f] \\ rw[] \\ fs[EVERY_MEM]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ simp[APPLY_UPDATE_THM] \\ rw[]
        \\ fs[Abbr`a`,LEAST_NOTIN_FDOM] )
      \\ simp[FLOOKUP_UPDATE,APPLY_UPDATE_THM]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ rw[]
      >- ( simp[FLOOKUP_DEF,LEAST_NOTIN_FDOM,Abbr`p`] )
      >- ( rw[] )
      >> simp[o_DEF]
      \\ qexists_tac`z` \\ simp[]
      \\ simp[MAP_EQ_f]
      \\ Cases \\ simp[libTheory.the_def]
      \\ rw[]
      \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
      \\ simp[APPLY_UPDATE_THM]
      \\ imp_res_tac evaluate_ok
      \\ fs[state_ok_def,EVERY_MEM]
      \\ res_tac \\ fs[] \\ rw[]
      \\ fs[Abbr`a`,LEAST_NOTIN_FDOM,Abbr`p`] )
    \\ Cases_on`op = ConcatByteVec` \\ fs[] >- (
      note_tac "Op: ConcatByteVec" \\
      fs[compile_op_def,bEvalOp_def,case_eq_thms]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ rw[] \\ fs[NULL_EQ,LENGTH_EQ_NUM_compute]
      \\ qpat_x_assum`_ = SOME _`mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[]
      \\ strip_tac
      \\ `lookup SumListLength_location t2.code = SOME (2,SND SumListLength_code)`
      by ( fs[state_rel_def,SumListLength_code_def])
      \\ drule evaluate_SumListLength_code
      \\ disch_then(qspec_then`adjust_bv b2 lv`mp_tac)
      \\ simp[v_to_list_adjust,MAP_MAP_o,Once o_DEF,adjust_bv_def]
      \\ `MAP (FLOOKUP t2.refs o b2) ps = MAP (FLOOKUP s5.refs) ps`
      by (
        fs[state_rel_def,MAP_EQ_f,MAP_MAP_o]
        \\ qx_gen_tac`k` \\ rw[]
        \\ fs[LIST_EQ_REWRITE,MEM_EL]
        \\ first_x_assum drule
        \\ simp[EL_MAP] \\ strip_tac
        \\ ntac 4 (first_x_assum(qspec_then`k`mp_tac))
        \\ simp[] )
      \\ fs[GSYM MAP_MAP_o] \\ rfs[]
      \\ disch_then(first_assum o mp_then Any mp_tac)
      \\ simp[MAP_MAP_o,o_DEF] \\ rveq
      \\ disch_then(qspec_then`0`(qx_choose_then`c1`strip_assume_tac))
      \\ qabbrev_tac`dst = LEAST ptr. ptr ∉ FDOM t2.refs`
      \\ qabbrev_tac`t3 = t2 with refs := t2.refs |+ (dst, ByteArray T (REPLICATE (LENGTH (FLAT wss)) 0w))`
      \\ `lookup SumListLength_location t3.code = SOME (2,SND SumListLength_code)`
      by ( fs[state_rel_def,SumListLength_code_def,Abbr`t3`])
      \\ drule evaluate_ConcatByte_code
      \\ simp[Once(GSYM AND_IMP_INTRO),RIGHT_FORALL_IMP_THM]
      \\ impl_keep_tac >- fs[Abbr`t3`,state_rel_def,ConcatByte_code_def]
      \\ disch_then(qspec_then`adjust_bv b2 lv`mp_tac)
      \\ simp[v_to_list_adjust,MAP_MAP_o,Once o_DEF,adjust_bv_def]
      \\ `¬MEM dst (MAP b2 ps)`
      by (
        strip_tac
        \\ fs[LIST_EQ_REWRITE,MEM_EL,MEM_MAP]
        \\ first_x_assum drule
        \\ simp[EL_MAP] \\ strip_tac
        \\ fs[FLOOKUP_DEF,INJ_DEF,state_rel_def]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ `MAP (FLOOKUP t3.refs o b2) ps = MAP (FLOOKUP t2.refs o b2) ps`
      by (
        simp[Abbr`t3`,FLOOKUP_UPDATE,MAP_EQ_f]
        \\ fs[MEM_MAP] \\ rw[]
        \\ METIS_TAC[] )
      \\ fs[GSYM MAP_MAP_o] \\ rfs[]
      \\ disch_then(first_assum o mp_then Any mp_tac)
      \\ simp[MAP_MAP_o,o_DEF] \\ rveq
      \\ simp[Abbr`t3`,FLOOKUP_UPDATE]
      \\ disch_then(qspec_then`[]`mp_tac)
      \\ simp[LENGTH_REPLICATE]
      \\ disch_then(qx_choose_then`c2`strip_assume_tac)
      \\ last_x_assum(mp_then Any mp_tac
            (INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``]
               bviPropsTheory.evaluate_add_clock))
      \\ disch_then(qspec_then`c1+c2+2`mp_tac) \\ rw[inc_clock_ADD]
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ map_every qexists_tac[`c+c1+c2+2`,
           `((LEAST ptr. ptr ∉ FDOM s5.refs) =+ dst) b2`]
      \\ last_x_assum(mp_then Any mp_tac
            (INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``]
               bviPropsTheory.evaluate_add_clock))
      \\ disch_then(qspec_then`c2+1`mp_tac) \\ rw[inc_clock_ADD]
      \\ simp[LEFT_EXISTS_AND_THM,CONJ_ASSOC]
      \\ reverse conj_asm2_tac
      >- (
        rw[APPLY_UPDATE_THM]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ fs[SUBSET_DEF]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ reverse conj_asm2_tac
      >- (
        rw[MAP_EQ_f]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ fs[EVERY_MEM]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ imp_res_tac bv_ok_SUBSET_IMP
        \\ rw[APPLY_UPDATE_THM]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ pop_assum (assume_tac o SYM)
      \\ rw[iEval_def,find_code_def,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ fs[inc_clock_def,dec_clock_def]
      \\ reverse IF_CASES_TAC
      >- ( `F` by METIS_TAC[EVAL``w2n (0w:word8)``] )
      \\ simp[integer_wordTheory.i2w_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ imp_res_tac evaluate_ok
      \\ imp_res_tac evaluate_refs_SUBSET
      \\ rpt(qhdtm_x_assum`evaluate`kall_tac)
      \\ rpt(qhdtm_x_assum`lookup`kall_tac)
      \\ match_mp_tac state_rel_add_bytearray
      \\ METIS_TAC[LEAST_NOTIN_FDOM])
    \\ Cases_on`op = CopyByte F` \\ fs[] >- (
      note_tac "Op: CopyByte F" \\
      CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ qabbrev_tac`pp = LEAST ptr. ptr ∉ FDOM s5.refs`
      \\ qabbrev_tac`qq = LEAST ptr. ptr ∉ FDOM t2.refs`
      \\ (`MAP (adjust_bv ((pp =+ qq) b2)) env = MAP (adjust_bv b2) env`
      by (
        rw[MAP_EQ_f]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ imp_res_tac bv_ok_SUBSET_IMP
        \\ fs[EVERY_MEM]
        \\ rw[APPLY_UPDATE_THM]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] ))
      \\ qexists_tac`c`
      \\ fs[compile_op_def,bEvalOp_def,case_eq_thms,SWAP_REVERSE_SYM]
      \\ qexists_tac`b2`
      \\ rw[iEval_def,adjust_bv_def,iEvalOp_def,do_app_aux_def,bEvalOp_def]
      \\ fs[case_eq_thms,PULL_EXISTS] \\ rw[adjust_bv_def,APPLY_UPDATE_THM]
      \\ rename1`FLOOKUP s5.refs src = SOME _`
      \\ (`FLOOKUP t2.refs (b2 src) = FLOOKUP s5.refs src`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
        \\ simp[] \\ NO_TAC) ) \\ simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ `FLOOKUP t2.refs (b2 dst) = FLOOKUP s5.refs dst`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`dst`mp_tac))
        \\ simp[] \\ NO_TAC ) \\ simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs[state_rel_def,FLOOKUP_UPDATE]
      \\ conj_tac
      >- (
        `dst INSERT FDOM s5.refs = FDOM s5.refs ∧
         b2 dst INSERT FDOM t2.refs = FDOM t2.refs`
        by (simp[GSYM ABSORPTION]
          \\ fs[FLOOKUP_DEF]
          \\ METIS_TAC[INJ_DEF] ) \\
        simp[] )
      \\ rw[]
      >- (TOP_CASE_TAC \\ fs[FLOOKUP_DEF] \\ METIS_TAC[INJ_DEF])
      >- ( fs[FLOOKUP_DEF] \\ METIS_TAC[] )
      \\ METIS_TAC[] )
    \\ Cases_on`op = CopyByte T` \\ fs[] >- (
        note_tac "Op: CopyByte T" \\
        CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\ qexists_tac`c`
        \\ fs[bEvalOp_def,case_eq_thms] \\ rw[]
        \\ fs[SWAP_REVERSE_SYM]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
        \\ simp[compile_op_def]
        \\ fs[semanticPrimitivesTheory.copy_array_def,case_eq_thms]
        \\ qabbrev_tac`pp = LEAST ptr. ptr ∉ FDOM s5.refs`
        \\ qabbrev_tac`qq = LEAST ptr. ptr ∉ FDOM t2.refs`
        \\ qexists_tac`(pp =+ qq) b2` \\
        `MAP (adjust_bv b2) env = MAP (adjust_bv ((pp =+ qq) b2)) env` by (
          rw[MAP_EQ_f]
          \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac `s5.refs`
          \\ imp_res_tac evaluate_refs_SUBSET
          \\ imp_res_tac bv_ok_SUBSET_IMP
          \\ fs[EVERY_MEM]
          \\ rw[APPLY_UPDATE_THM]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ qhdtm_x_assum`bviSem$evaluate`mp_tac
        \\ simp[iEval_def,iEvalOp_def,do_app_aux_def,adjust_bv_def,backend_commonTheory.small_enough_int_def]
        \\ fsrw_tac[intLib.INT_ARITH_ss][]
        \\ reverse IF_CASES_TAC
        >- (fs[] \\ first_x_assum(qspec_then`0w`mp_tac) \\ simp[])
        \\ simp[bEvalOp_def,FLOOKUP_UPDATE]
        \\ rename1`qq = b2 src`
        \\ IF_CASES_TAC
        >- (
          fs[state_rel_def]
          \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
          \\ simp[]
          \\ fs[FLOOKUP_DEF]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ (`FLOOKUP t2.refs (b2 src) = FLOOKUP s5.refs src`
        by (
          fs[state_rel_def]
          \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
          \\ simp[] \\ NO_TAC) )
        \\ simp[semanticPrimitivesTheory.copy_array_def]
        \\ asm_simp_tac(srw_ss()++intLib.INT_ARITH_ss)[integerTheory.INT_ABS]
        \\ simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
        \\ strip_tac
        \\ simp[REPLICATE_GENLIST,DROP_LENGTH_NIL_rwt]
        \\ conj_tac
        >- (
          match_mp_tac state_rel_add_bytearray
          \\ imp_res_tac evaluate_ok
          \\ simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] )
        \\ rw[]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ METIS_TAC[SUBSET_DEF,LEAST_NOTIN_FDOM] )
    \\ Cases_on`∃b. op = CopyByte b` \\ fs[] >- (Cases_on`b` \\ fs[])
    \\ `compile_op op c1 = Op op c1` by
      (Cases_on `op` \\ full_simp_tac(srw_ss())[compile_op_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
    \\ `EVERY (bv_ok s5.refs) (REVERSE a)` by (IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[rich_listTheory.EVERY_REVERSE])
    \\ drule (GEN_ALL do_app_adjust) \\ fs []
    \\ disch_then (qspecl_then [`r`,`q`,`op`,`a`] mp_tac)
    \\ fs [] \\ strip_tac \\ fs [MAP_REVERSE])
  THEN1 (* Tick *)
   (note_tac "Tick" \\
    `?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [iEval_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (SRW_TAC [] [] \\ Q.LIST_EXISTS_TAC [`t1`,`b1`,`0`]
      \\ full_simp_tac(srw_ss())[inc_clock_ZERO] \\ full_simp_tac(srw_ss())[state_rel_def]) \\ full_simp_tac(srw_ss())[]
    \\ `t1.clock <> 0 /\ !c. (inc_clock c t1).clock <> 0` by
      (EVAL_TAC \\ full_simp_tac(srw_ss())[state_rel_def] \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ `(dec_clock 1 s).refs = s.refs` by EVAL_TAC \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!xx yy. bbb` (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`b1`])
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[evaluate_ok_lemma]
           \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def]
           \\ metis_tac[])
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL])
  THEN1 (* Call *)
   (note_tac "Call" \\
    `?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s1) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
    \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Cases_on `find_code dest a s5.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s5.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
     (Q.LIST_EXISTS_TAC [`t2 with clock := 0`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ TRY (full_simp_tac(srw_ss())[state_rel_def]
              \\ qexists_tac`array_size'` \\ simp[])
      \\ `t2.clock < ticks + 1` by (full_simp_tac(srw_ss())[state_rel_def]
                                    \\ rev_full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `dest`)
      \\ full_simp_tac(srw_ss())[bvlSemTheory.find_code_def,find_code_def]
      THEN1
       (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
        \\ `?x1 x2 x3. compile_exps n' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x1` \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
      \\ `?x1 x2 x3. compile_exps n'' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF])
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a s5.code = SOME (args,body)`
    \\ `?n7. let (c7,aux7,n8) = compile_exps n7 [body] in
               (find_code (case dest of NONE => NONE
                           | SOME n => SOME (num_stubs + nss * n))
                 (MAP (adjust_bv b2) a) t2.code =
                 SOME (MAP (adjust_bv b2) args,bvi_let$compile_exp (HD c7))) /\
               aux_code_installed (append aux7) t2.code /\
               handle_ok [body]` by
     (reverse (Cases_on `dest`)
      \\ full_simp_tac(srw_ss())[state_rel_def,find_code_def]
      THEN1 (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[]
             \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ FIRST_X_ASSUM (qspecl_then
             [`x`,`LENGTH a`,`body`]mp_tac) \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n'` \\ full_simp_tac(srw_ss())[]
        \\ `?c2 aux2 n2. compile_exps n' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?a1 a2. a = SNOC a1 a2` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `a1` \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `!x1 x2. bbb` (MP_TAC o Q.SPECL [`n'`])
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n''`
      \\ `?c2 aux2 n2. compile_exps n'' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF,adjust_bv_def])
    \\ `?c7 aux7 n8. compile_exps n7 [body] = (c7,aux7,n8)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `¬(t2.clock < ticks + 1)` by (full_simp_tac(srw_ss())[state_rel_def] \\ REV_FULL_SIMP_TAC std_ss [])
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c7 = [d]` by (Cases_on `c7` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n7`) \\ full_simp_tac(srw_ss())[]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock (ticks + 1) t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (`(dec_clock (ticks + 1) t2).code = t2.code` by (EVAL_TAC \\ full_simp_tac(srw_ss())[])
      \\ `(dec_clock (ticks + 1) t2).refs = t2.refs` by (EVAL_TAC \\ full_simp_tac(srw_ss())[])
      \\ IMP_RES_TAC evaluate_ok
      \\ full_simp_tac(srw_ss())[evaluate_ok_lemma] \\ REV_FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC THEN1
        (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def] >>
         METIS_TAC[])
      \\ IMP_RES_TAC find_code_EVERY_IMP
      \\ imp_res_tac evaluate_global_mono
      \\ full_simp_tac(srw_ss())[])
    \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s5.refs` \\ fs[bvlSemTheory.dec_clock_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ IMP_RES_TAC bv_ok_SUBSET_IMP \\ fs[EVERY_MEM] \\ NO_TAC)
    \\ `(inc_clock c' t2).code = t2.code` by (EVAL_TAC \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ `¬((inc_clock c' t2).clock < ticks + 1)` by (full_simp_tac(srw_ss())[inc_clock_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock]
    \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    >-
      (imp_res_tac bvi_letProofTheory.evaluate_compile_exp \\ fs[])
    >>
      (imp_res_tac bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])));

val _ = save_thm("compile_exps_correct",compile_exps_correct);

(* composed compiler correctness *)

Theorem compile_single_evaluate:
   evaluate ([Call 0 (SOME start) []],[],s1) = (res,s2) ∧
   state_rel b1 s1 t1 ∧ IS_SOME t1.global ∧ state_ok s1 ∧
   res ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 t2.
     evaluate ([Call 0 (SOME (num_stubs + nss * start))[] NONE],[],inc_clock ck t1) =
       (map_result (MAP (adjust_bv b2)) (adjust_bv b2) res,t2) ∧
     state_rel b2 s2 (t2:('c,'ffi) bviSem$state)
Proof
  srw_tac[][] >>
  full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def] >>
  full_simp_tac(srw_ss())[find_code_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][bviSemTheory.evaluate_def,find_code_def] >>
  first_assum(drule o last o CONJUNCTS o CONV_RULE(REWR_CONV state_rel_def)) >>
  simp[] >> strip_tac >> pairarg_tac >> full_simp_tac(srw_ss())[] >- (
    qpat_x_assum`0n = _`(assume_tac o SYM) >> simp[] >>
    `t1.clock = 0` by full_simp_tac(srw_ss())[state_rel_def] >> simp[] >>
    simp[inc_clock_def] >>
    qexists_tac`0`>>simp[]>>
    qexists_tac`b1` >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  `t1.clock ≠ 0` by (full_simp_tac(srw_ss())[state_rel_def] >> simp[]) >>
  drule compile_exps_correct >> simp[] >>
  disch_then drule >>
  `state_rel b1 (dec_clock 1 s1) (dec_clock 1 t1)` by (
    full_simp_tac(srw_ss())[state_rel_def,bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] ) >>
  disch_then drule >>
  impl_tac >- (
    full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] >>
    full_simp_tac(srw_ss())[state_ok_def] ) >>
  strip_tac >>
  imp_res_tac compile_exps_SING >> var_eq_tac >> simp[] >>
  qexists_tac`c` >>
  `dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1)` by (
    EVAL_TAC >> simp[state_component_equality] ) >>
  simp[] >>
  imp_res_tac bvi_letProofTheory.evaluate_compile_exp >> rfs[] >>
  Cases_on`res`>>simp[] >- METIS_TAC[] >>
  Cases_on`e`>>simp[] >> METIS_TAC[]
QED

val evaluate_REPLICATE_0 = Q.prove(
  `!n. evaluate (REPLICATE n (Op (Const 0) []),env,s) =
          (Rval (REPLICATE n (Number 0)),s)`,
  Induct \\ fs [evaluate_def,REPLICATE]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [evaluate_def,REPLICATE,do_app_def,do_app_aux_def]
  \\ fs [EVAL ``small_enough_int 0``]);

Theorem bvi_stubs_evaluate:
   ∀kk start ffi0 code k.
     0 < k ∧ num_stubs ≤ start ⇒
  let t0 = <| global := SOME 0
            ; ffi := ffi0
            ; clock := k
            ; compile := cc
            ; compile_oracle := co
            ; code := fromAList (stubs start kk ++ code);
              refs := FEMPTY |+
                (0,ValueArray ([Number 1] ++
                  REPLICATE ((MIN (MAX kk 1) InitGlobals_max) - 1) (Number 0))) |>
                :('c,'ffi) bviSem$state in
      evaluate ([Call 0 (SOME InitGlobals_location) [] NONE],[],
        initial_state ffi0 (fromAList (stubs start kk ++ code)) co cc (k+1)) =
   let (r,s) = evaluate ([Call 0 (SOME start) [] NONE],[],t0) in
     ((case r of Rerr(Rraise v) => Rval [v] | _ => r), s)
Proof
  srw_tac[][bviSemTheory.evaluate_def,find_code_def,
            lookup_fromAList,ALOOKUP_APPEND] >>
  srw_tac[][Once stubs_def] >>
  TRY (pop_assum(assume_tac o CONV_RULE EVAL)>>full_simp_tac(srw_ss())[]>>NO_TAC) >>
  simp[InitGlobals_code_def] >>
  simp[bviSemTheory.evaluate_def,
       bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,backend_commonTheory.small_enough_int_def] >>
  once_rewrite_tac [evaluate_SNOC |> REWRITE_RULE [SNOC_APPEND]] >>
  simp[bviSemTheory.evaluate_def,bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,backend_commonTheory.small_enough_int_def,evaluate_REPLICATE_0] >>
  simp[bvlSemTheory.do_app_def,find_code_def,lookup_fromAList,ALOOKUP_APPEND] >>
  fs [EVAL ``InitGlobals_max ≤ 268435457``,FAPPLY_FUPDATE_THM,
      EVAL ``(bvl_to_bvi _ _).refs``,FLOOKUP_DEF] >>
  reverse IF_CASES_TAC
  THEN1 (`F` by (fs [] \\ fs [LENGTH_REPLICATE,InitGlobals_max_def])) \\ fs []
  \\ `lookup start (fromAList (stubs start kk ++ code)) =
      lookup start t0.code /\ t0.clock <> 0` by (fs [Abbr `t0`] \\ NO_TAC)
  \\ fs [] \\ Cases_on `lookup start t0.code` \\ fs []
  \\ rveq \\ fs []
  \\ unabbrev_all_tac
  \\ full_simp_tac(srw_ss())[bvl_to_bvi_def,bvi_to_bvl_def,
       bviSemTheory.dec_clock_def,bviSemTheory.initial_state_def]
  \\ Cases_on `MIN (MAX kk 1) InitGlobals_max` \\ fs[]
  \\fs [bviSemTheory.state_component_equality,LUPDATE_def]
  \\ fs [InitGlobals_max_def]
  \\ fs [REPLICATE,LUPDATE_def]
  \\ Cases_on `x` \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs [] \\ rveq \\ fs []
  \\ CASE_TAC \\ fs [] \\ rveq \\ fs []
QED

Theorem compile_list_distinct_locs:
   ∀n prog code_app code n'.
     ALL_DISTINCT (MAP FST prog) ∧
     compile_list n prog = (code_app,n') ∧
     code = append code_app
     ⇒
     ALL_DISTINCT (MAP FST code) ∧
     EVERY (between (num_stubs + nss * n) (num_stubs + nss * n'))
       (FILTER (λn. in_ns 1 (n - num_stubs)) (MAP FST code)) ∧
     FILTER (λn. in_ns 0 (n - num_stubs)) (MAP FST code) =
       MAP (λn. num_stubs + nss * n) (MAP FST prog) ∧
     (*  redundant, but useful *) EVERY ($<= num_stubs) (MAP FST code) ∧
     EVERY (λn. ¬ in_ns 2 (n - num_stubs)) (MAP FST code) ∧
     n ≤ n'
Proof
  Induct_on`prog`>>simp[compile_list_def]>>
  qx_gen_tac`p`>>PairCases_on`p`>>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[compile_single_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac compile_exps_aux_sorted >>
  rpt var_eq_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY] >>
  simp[EVERY_MAP] >>
  reverse conj_tac >- (
    reverse conj_tac >- (
      simp[FILTER_APPEND] >>
      simp[FILTER_MAP,o_DEF] >>
      simp[MAP_MAP_o,o_DEF,UNCURRY,FILTER_EQ_NIL] >>
      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,between_def] >>
      rw[] >> res_tac >> fs[]) >>
    fsrw_tac[ARITH_ss][EVERY_FILTER,between_def,EVERY_MAP] >>
    full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >> res_tac >>
    fsrw_tac[ARITH_ss][] >>
    fs[backend_commonTheory.bvl_to_bvi_namespaces_def]) >>
  simp[ALL_DISTINCT_APPEND] >>
  reverse conj_tac
  THEN1
   (conj_tac >- (
      irule SORTED_ALL_DISTINCT >>
      METIS_TAC[irreflexive_def,prim_recTheory.LESS_REFL,transitive_LESS]) >>
    `EVERY (in_ns 1) (MAP FST (append aux))` by (
      fs[EVERY_MEM] \\ rw[] \\ res_tac \\ rw[]) >>
    full_simp_tac(srw_ss())[EVERY_MEM,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
    srw_tac[][] >> spose_not_then strip_assume_tac >>
    res_tac >> full_simp_tac(srw_ss())[between_def] >- (
      full_simp_tac(srw_ss())[MEM_FILTER,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      res_tac >> fs[]))
  \\ `EVERY (in_ns 1) (MAP FST (append aux))` by (
      fs[EVERY_MEM] \\ rw[] \\ res_tac \\ rw[])
  \\ full_simp_tac(srw_ss())[EVERY_MEM,PULL_EXISTS,MEM_MAP,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[EVERY_MEM,PULL_EXISTS,MEM_MAP,EXISTS_PROD]
  \\ srw_tac[][] \\ spose_not_then strip_assume_tac
  \\ res_tac \\ full_simp_tac(srw_ss())[between_def] >>
  qmatch_assum_abbrev_tac`l1 = l2` >>
  qmatch_assum_abbrev_tac`MEM x l3` >>
  `MEM (FST x) l1` by (
    unabbrev_all_tac >>
    simp[MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    METIS_TAC[] ) >>
  `MEM (FST x) l2` by METIS_TAC[] >>
  pop_assum mp_tac >>
  unabbrev_all_tac >> simp[MEM_MAP,EXISTS_PROD] >>
  fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

Theorem compile_prog_evaluate:
   compile_prog start n prog = (start', prog', n') ∧
   evaluate ([Call 0 (SOME start) []],[],
             initial_state ffi0 (fromAList prog) co (state_cc compile_inc cc) k) = (r,s) ∧
   0 < k ∧
   ALL_DISTINCT (MAP FST prog) ∧
   handle_ok (MAP (SND o SND) prog) ∧
   (∀n. EVERY ((λe. handle_ok [e]) o SND o SND) (SND (co n))) ∧
   n' ≤ (FST(FST(co 0))) ∧
   r ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 s2.
   evaluate ([Call 0 (SOME start') [] NONE],[],
             initial_state ffi0 (fromAList prog') (state_co compile_inc co) cc (k+ck)) =
     (map_result (MAP (adjust_bv b2)) (adjust_bv b2)
       (case r of Rerr(Rraise v) => Rval [v] | _ => r),s2) ∧
   state_rel b2 s (s2:('c,'ffi) bviSem$state)
Proof
(*
  theorems to compose:
    bvi_stubs_evaluate
    compile_single_evaluate
*)
  srw_tac[][compile_prog_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >> rveq >>
  drule (GEN_ALL compile_single_evaluate) >>
  simp[state_ok_def] >>
  qpat_abbrev_tac `kk = alloc_glob_count (MAP (λ(_,_,p). p) prog)` >>
  (Q.ISPECL_THEN[`state_co compile_inc co`,`cc`,`kk`,
       `num_stubs + nss * start`,`ffi0`,`append code`,`k`] mp_tac)
    (Q.GENL[`co`,`cc`] bvi_stubs_evaluate) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac`_ = _ (evaluate (_,[],t1))` >>
  strip_tac \\ pairarg_tac \\ fs[] \\
  simp [Once state_rel_def,FLOOKUP_UPDATE] >>
  disch_then(qspec_then`t1`mp_tac) >>
  simp[Abbr`t1`] >>
  impl_tac >- (
    conj_tac >- (qexists_tac `MIN (MAX kk 1) InitGlobals_max`
                 \\ fs [] \\ EVAL_TAC) >>
    rpt var_eq_tac >>
    simp[lookup_fromAList,ALOOKUP_APPEND] >>
    simp[stubs_def] >>
    IF_CASES_TAC >> simp[] >- (
      `F` suffices_by srw_tac[][] >> pop_assum mp_tac >> EVAL_TAC ) >>
    rpt gen_tac \\
    rpt (
      IF_CASES_TAC >- (
        `F` suffices_by srw_tac[][] >>
        pop_assum mp_tac >> EVAL_TAC >> decide_tac)) >>
    simp_tac std_ss [] >>
    conj_tac >- (
      simp_tac(srw_ss()++LET_ss)[names_ok_def,domain_fromAList]
      \\ conj_tac
      >- (
        qx_gen_tac`m`
        \\ rpt strip_tac
        \\ first_x_assum(qspec_then`m`mp_tac)
        \\ simp[EVERY_MEM,UNCURRY] )
      \\ rpt strip_tac \\ rveq
      \\ TRY (pop_assum mp_tac \\ EVAL_TAC \\ NO_TAC)
      \\ rpt(qpat_x_assum`_ ≠ _`kall_tac)
      \\ drule compile_list_distinct_locs
      \\ disch_then drule \\ simp[]
      \\ simp[EVERY_MEM,MEM_FILTER,between_def]
      \\ strip_tac
      \\ qmatch_assum_rename_tac`MEM m (MAP FST _)`
      \\ IF_CASES_TAC
      >- (
        last_x_assum(qspec_then`m`mp_tac) \\
        last_x_assum(qspec_then`m`mp_tac) \\
        impl_tac >- (
          simp[] \\
          ONCE_REWRITE_TAC[GSYM in_ns_add_num_stubs] \\
          asm_simp_tac(std_ss++ARITH_ss)[] \\
          simp[in_ns_def] )
        \\ rw[]
        \\ qmatch_assum_rename_tac`m < num_stubs + x * nss`
        \\ qmatch_assum_rename_tac`x <= y`
        \\ `x * nss <= y * nss` by simp[]
        \\ decide_tac )
      \\ conj_asm1_tac
      >- (
        assume_tac(EVAL``nss``)
        \\ `m MOD nss < nss` by simp[]
        \\ CCONTR_TAC
        \\ `m MOD nss = 2` by decide_tac
        \\ first_x_assum drule
        \\ simp_tac std_ss []
        \\ ONCE_REWRITE_TAC[GSYM in_ns_add_num_stubs]
        \\ asm_simp_tac(std_ss++ARITH_ss)[]
        \\ simp[in_ns_def] )
      \\ qpat_x_assum`FILTER _ _ = _`(mp_tac o Q.AP_TERM`LIST_TO_SET`)
      \\ simp[EXTENSION,MEM_FILTER]
      \\ qpat_x_assum`num_stubs ≤ _`mp_tac
      \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
      \\ disch_then(qx_choose_then`x`strip_assume_tac)
      \\ `0 < nss` by EVAL_TAC
      \\ `∃y. x = y * nss` by METIS_TAC[MOD_EQ_0_DIVISOR,in_ns_def,in_ns_add_num_stubs,ADD_COMM]
      \\ rveq
      \\ disch_then(qspec_then`num_stubs + y * nss`mp_tac)
      \\ simp[in_ns_def,MEM_MAP,MULT_DIV]) \\
    rpt gen_tac \\ strip_tac \\
    rpt (
      IF_CASES_TAC >- (
        `F` suffices_by srw_tac[][] >>
        pop_assum mp_tac >> EVAL_TAC >>
        rpt(pop_assum kall_tac) >>
        decide_tac)) >>
    simp_tac std_ss [] >>
    imp_res_tac compile_list_imp >>
    asm_simp_tac std_ss [] >>
    qmatch_assum_rename_tac`bvl_to_bvi$compile_exps nn _ = _` >>
    qexists_tac`nn` >>
    asm_simp_tac std_ss [] >>
    rewrite_tac [CONJ_ASSOC] >>
    reverse conj_tac >- (
      qpat_x_assum `handle_ok (MAP (SND ∘ SND) prog)` mp_tac
      \\ qpat_x_assum `ALOOKUP prog name = SOME (arity,exp)` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Induct_on `prog` \\ fs [] \\ Cases \\ fs [] \\ rw [] \\ fs []
      \\ Cases_on `MAP (SND ∘ SND) prog` \\ fs [handle_ok_def]) >>
    conj_tac THEN1
      (simp_tac (std_ss)[Once ADD_COMM,Once MULT_COMM,HD] \\
       first_x_assum MATCH_ACCEPT_TAC ) >>
    match_mp_tac aux_code_installed_sublist >>
    conj_tac >- (
      full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
      METIS_TAC[CONS_APPEND,APPEND_ASSOC] ) >>
    rpt(qpat_x_assum`_ ≠ _`kall_tac) >>
    imp_res_tac compile_list_distinct_locs >>
    simp[] >> srw_tac[][] >> (TRY (EVAL_TAC >> NO_TAC)) >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[EVERY_MEM] >>
    res_tac >> pop_assum mp_tac >> EVAL_TAC) >>
  strip_tac >>
  qexists_tac`ck+1` >>
  `0 < ck + k` by simp[] >>
  drule (GEN_ALL bvi_stubs_evaluate) >>
  disch_then (qspecl_then [`state_co compile_inc co`,`cc`,`kk`] mp_tac) >>
  `num_stubs ≤ num_stubs + nss * start` by fs[] >>
  disch_then drule >>
  disch_then(qspecl_then[`ffi0`,`append code`]mp_tac) >>
  simp[] >>
  rpt var_eq_tac >>
  fsrw_tac[ARITH_ss][inc_clock_def] >>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  TRY(Cases_on`e`)>>full_simp_tac(srw_ss())[] >>
  PROVE_TAC[ADD_ASSOC,ADD_COMM]
QED

Theorem compile_prog_semantics:
   compile_prog start n prog = (start', prog', n') ∧
   ALL_DISTINCT (MAP FST prog) ∧
   handle_ok (MAP (SND o SND) prog) ∧
   (∀n. EVERY ((λe. handle_ok [e]) o SND o SND) (SND (co n))) ∧
   n' ≤ FST (FST ((co:num -> (num # 'c) # (num # num # bvl$exp) list) 0)) ∧
   semantics (ffi0:'ffi ffi_state) (fromAList prog) co (state_cc compile_inc cc) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') (state_co compile_inc co) cc start' =
   semantics ffi0 (fromAList prog) co (state_cc compile_inc cc) start
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 5 strip_tac >>
  simp[bvlSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    gen_tac >> strip_tac >> rveq >> simp[] >>
    simp[bviSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
      drule bviPropsTheory.evaluate_add_clock >>
      CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL])) >>
      impl_tac >- full_simp_tac(srw_ss())[] >> strip_tac >>
      qhdtm_x_assum`bvlSem$evaluate`kall_tac >>
      qpat_assum`∀k. FST _ ≠ _`(qspec_then`SUC k'`mp_tac)>>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      drule (GEN_ALL compile_prog_evaluate) >>
      disch_then drule >>
      impl_tac >- ( full_simp_tac(srw_ss())[] >> METIS_TAC[FST] ) >>
      strip_tac >>
      strip_tac >>
      first_x_assum(qspec_then`SUC ck`mp_tac) >>
      simp[inc_clock_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[] >> rveq >>
      spose_not_then strip_assume_tac >>
      rveq >> full_simp_tac(srw_ss())[] >>
      Cases_on`a`>>full_simp_tac(srw_ss())[]
      ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_abbrev_tac`bvlSem$evaluate (bxps,[],bs) = _` >>
      qmatch_assum_abbrev_tac`bviSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`bxps`,`[]`,`bs`]mp_tac
        (INST_TYPE[alpha|->``:num#'c``,beta|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac
        (INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``]bviPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[bvlPropsTheory.inc_clock_def,bviPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`] >>
      ntac 2 strip_tac >>
      drule bvlPropsTheory.evaluate_add_clock >>
      disch_then(qspec_then `1` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      simp[bvlPropsTheory.inc_clock_def] >>
      strip_tac >> unabbrev_all_tac >>
      drule(GEN_ALL compile_prog_evaluate) >>
      disch_then dxrule >> simp[] >>
      impl_tac >- (CCONTR_TAC >> fs[] >> metis_tac[FST]) >>
      strip_tac >>
      dxrule bviPropsTheory.evaluate_add_clock >>
      disch_then(qspec_then `k'` mp_tac) >>
      impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      dxrule bviPropsTheory.evaluate_add_clock >>
      disch_then(qspec_then `ck + k + 1` mp_tac) >>
      impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      ntac 2 strip_tac >> fs[inc_clock_def] >> rveq >>
      rpt(PURE_FULL_CASE_TAC >> fs[bviSemTheory.state_component_equality,state_rel_def])) >>
    qmatch_assum_abbrev_tac`bvlSem$evaluate (bxps,[],bs) = _` >>
    qspecl_then[`bxps`,`[]`,`bs`]mp_tac
      (INST_TYPE[alpha|->``:num#'c``,beta|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
    simp[bvlPropsTheory.inc_clock_def,Abbr`bs`] >>
    disch_then(qspec_then`1`strip_assume_tac) >>
    first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
    unabbrev_all_tac >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    impl_tac >- (
      metis_tac[FST] ) >>
    strip_tac >>
    asm_exists_tac >> fs[] >>
    Cases_on `q` >> fs[] >> Cases_on `e` >> fs[]
    >> TOP_CASE_TAC >> fs[]
    >- metis_tac[FST]
    >> qpat_x_assum `evaluate _ = (r,s)` assume_tac >>
    drule bvlPropsTheory.evaluate_add_clock >>
    disch_then(qspec_then`1`mp_tac) >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    strip_tac >> fs[bvlPropsTheory.inc_clock_def] >>
    metis_tac[FST]) >>
  strip_tac >>
  simp[bviSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    qpat_x_assum`∀k. _ ≠ _`(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`FST q ≠ _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    conj_tac >- (
      Cases_on`k`>>simp[] >>
      full_simp_tac(srw_ss())[bviSemTheory.evaluate_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[compile_prog_def,LET_THM] >>
      pairarg_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[find_code_def,lookup_fromAList,ALOOKUP_APPEND,stubs_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      TRY(rpt(qpat_x_assum`_ = _`mp_tac) >> EVAL_TAC >> NO_TAC) >>
      full_simp_tac(srw_ss())[InitGlobals_code_def]) >>
    spose_not_then strip_assume_tac >>
    qmatch_assum_abbrev_tac`FST q = _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    imp_res_tac bviPropsTheory.evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`ck`mp_tac) >>
    simp[inc_clock_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    metis_tac[semanticPrimitivesTheory.abort_nchotomy]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    qpat_assum`∀k. _ ≠ _`(qspec_then`SUC k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >>
    impl_tac >- full_simp_tac(srw_ss())[] >>
    strip_tac >>
    qpat_x_assum `evaluate _ = (r,s)` assume_tac >>
    drule bviPropsTheory.evaluate_add_clock >>
    disch_then(qspec_then `SUC ck` mp_tac) >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    strip_tac >> fs[inc_clock_def,ADD1] >>
    rveq >> rpt(PURE_FULL_CASE_TAC >> fs[]) >>
    first_x_assum(qspecl_then [`k + 1`,`outcome`] assume_tac) >>
    rfs[]) >>
  strip_tac >>
  qmatch_abbrev_tac`lprefix_lub$build_lprefix_lub l1 = lprefix_lub$build_lprefix_lub l2` >>
  `(lprefix_lub$lprefix_chain l1 ∧ lprefix_lub$lprefix_chain l2) ∧ lprefix_lub$equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS,
      bviPropsTheory.initial_state_with_simp,
      bvlPropsTheory.initial_state_with_simp,
      bviPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE (srw_ss())[bviPropsTheory.inc_clock_def],
      bvlPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  drule (GEN_ALL compile_prog_evaluate) >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  disch_then(qspecl_then[`k`,`ffi0`,`co`,`cc`]mp_tac)>>simp[]>>
  Cases_on`k=0`>>simp[]>-(
    full_simp_tac(srw_ss())[bviSemTheory.evaluate_def,bvlSemTheory.evaluate_def]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    simp[GSYM IMP_CONJ_THM] >> strip_tac >>
    conj_tac >> qexists_tac`0`>>simp[])>>
  strip_tac >>
  qmatch_assum_abbrev_tac`state_rel _ (SND p1) (SND p2)` >>
  Cases_on`p1`>>Cases_on`p2`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  ntac 2 (pop_assum(mp_tac o SYM)) >> ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_rename_tac`state_rel _ p1 p2` >>
  `p1.ffi = p2.ffi` by full_simp_tac(srw_ss())[state_rel_def] >>
  reverse conj_tac >> srw_tac[][]
  >- ( qexists_tac`ck+k` >> full_simp_tac(srw_ss())[] ) >>
  qexists_tac`k` >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`_ < (LENGTH (_ ffi))` >>
  `ffi.io_events ≼ p2.ffi.io_events` by (
    qunabbrev_tac`ffi` >>
    metis_tac[
      bviPropsTheory.initial_state_with_simp,
      bviPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE(srw_ss())[bviPropsTheory.inc_clock_def],
      SND,ADD_SYM]) >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >> simp[EL_APPEND1]
QED

Theorem compile_prog_distinct_locs:
   compile_prog start n prog = (k,prog1,n1) /\ ALL_DISTINCT (MAP FST prog) ==>
    ALL_DISTINCT (MAP FST prog1) /\
    EVERY (between (nss * n + num_stubs) (nss * n1 + num_stubs))
      (FILTER (λn. in_ns 1 (n − num_stubs)) (MAP FST prog1)) /\
    EVERY (λn. ¬in_ns 2 (n - num_stubs)) (MAP FST prog1)
Proof
  fs [compile_prog_def] \\ pairarg_tac \\ fs [] \\ strip_tac \\ rveq
  \\ drule (compile_list_distinct_locs |> SIMP_RULE std_ss [])
  \\ disch_then drule
  \\ fs [ALL_DISTINCT_APPEND] \\ rw [] THEN1 EVAL_TAC
  THEN1
   (pop_assum mp_tac
    \\ CONV_TAC (RATOR_CONV EVAL)
    \\ CCONTR_TAC \\ fs []
    \\ fs [EVERY_MEM] \\ res_tac \\ rveq
    \\ pop_assum mp_tac \\ EVAL_TAC)
  \\ fs [FILTER_APPEND] \\ EVAL_TAC
QED

val ODD_lemma = prove(
  ``ODD (2 * n + k) = ODD k``,
  fs [ODD_ADD] \\ simp [ODD_EVEN,EVEN_DOUBLE]);

val full_cc_def = Define `
  full_cc c cc =
    let limit = c.inline_size_limit in
    let split = c.split_main_at_seq in
    let cut = c.exp_cut in
      state_cc (compile_inc limit split cut) (state_cc compile_inc (bvi_tailrecProof$mk_cc cc))`

val full_co_def = Define `
  full_co c co =
    let limit = c.inline_size_limit in
    let split = c.split_main_at_seq in
    let cut = c.exp_cut in
      bvi_tailrecProof$mk_co (state_co compile_inc (state_co (compile_inc limit split cut) co))`

Theorem compile_prog_avoids_nss_2:
   compile_prog start f prog = (loc,code,new_state) /\
    ALL_DISTINCT (MAP FST prog) /\
    k MOD nss = 2 /\ MEM k (MAP FST code) ==>
    k ≤ num_stubs
Proof
  fs [compile_prog_def] \\ pairarg_tac \\ fs []
  \\ rw [] \\ fs []
  THEN1 (pop_assum mp_tac \\ EVAL_TAC \\ rw [])
  \\ imp_res_tac (compile_list_distinct_locs |> SIMP_RULE std_ss [])
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ rveq
  \\ res_tac \\ fs [in_ns_def]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ fs []
  \\ qpat_x_assum `(p + num_stubs) MOD nss = 2` mp_tac
  \\ `(p MOD nss + num_stubs MOD nss) MOD nss = (p + num_stubs) MOD nss` by
       (match_mp_tac MOD_PLUS \\ EVAL_TAC)
  \\ fs [EVAL ``num_stubs MOD nss``]
  \\ `0 < nss` by EVAL_TAC \\ fs []
QED

Theorem compile_semantics:
   compile start c prog = (start', prog', inlines, n1, n2) ∧
   FST (FST (co 0)) = inlines /\
   FST (SND (FST (co 0))) = n1 /\
   FST (SND (SND (FST (co 0)))) = n2 /\
   (∀n. ALL_DISTINCT (MAP FST (SND (co n))) ∧
        num_stubs ≤ FST(SND(SND(FST(co n)))) ∧ in_ns 2 (FST(SND(SND(FST(co n)))))) /\
   ALL_DISTINCT (MAP FST prog) ==>
   semantics (ffi0:'ffi ffi_state) (fromAList prog) co (full_cc c cc) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') (full_co c co) cc start' =
   semantics ffi0 (fromAList prog) co (full_cc c cc) start
Proof
  rw [full_cc_def,full_co_def]
  \\ drule (bvl_inlineProofTheory.compile_prog_semantics
          |> ONCE_REWRITE_RULE [bvi_letProofTheory.IMP_COMM] |> GEN_ALL)
  \\ fs [] \\ fs [compile_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ drule (compile_prog_semantics |> REWRITE_RULE [CONJ_ASSOC]
            |> ONCE_REWRITE_RULE [CONJ_COMM] |> Q.GENL [`n`,`n'`,`start'`,`prog'`])
  \\ disch_then (qspec_then `0` mp_tac) \\ fs []
  \\ impl_tac
  THEN1
   (fs [state_co_def,UNCURRY]
    \\ imp_res_tac bvl_inlineProofTheory.compile_prog_handle_ok \\ fs []
    \\ imp_res_tac bvl_inlineProofTheory.compile_prog_names \\ fs []
    \\ fs [bvl_inlineTheory.compile_inc_def,UNCURRY,EVERY_MEM,MEM_MAP,EXISTS_PROD]
    \\ rw [] \\ fs [bvl_inlineTheory.optimise_def]
    \\ fs [bvl_handleProofTheory.compile_any_handle_ok])
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ drule (bvi_tailrecProofTheory.compile_prog_semantics
            |> REWRITE_RULE [CONJ_ASSOC]
            |> ONCE_REWRITE_RULE [CONJ_COMM] |> Q.GENL [`n`,`prog2`])
  \\ disch_then (qspec_then `num_stubs + 2` mp_tac) \\ fs []
  \\ reverse impl_tac
  THEN1 (disch_then (assume_tac o GSYM) \\ fs [])
  \\ simp [state_co_def,UNCURRY]
  \\ reverse conj_asm2_tac
  THEN1
   (rw [] \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac `num_stubs`
    \\ imp_res_tac compile_prog_avoids_nss_2 \\ fs[]
    \\ imp_res_tac bvl_inlineProofTheory.compile_prog_names
    \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
    \\ strip_tac \\ fs [])
  \\ fs [bvi_tailrecProofTheory.input_condition_def,GSYM ALL_EL_MAP]
  \\ fs [GSYM in_ns_def,EVAL ``in_ns 2 2``]
  \\ conj_asm1_tac
  >- (
    drule bvl_inlineProofTheory.compile_prog_names
    \\ strip_tac
    \\ drule compile_prog_distinct_locs
    \\ impl_tac >- fs[]
    \\ strip_tac
    \\ conj_tac >- (
      fs[EVERY_MEM,bvi_tailrecProofTheory.free_names_def]
      \\ rw[] \\ res_tac
      \\ strip_tac \\ rveq
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[] )
    \\ conj_tac >- fs[]
    \\ fs[EVERY_MAP] \\ fs[EVERY_MEM,MEM_FILTER]
    \\ rw[] \\ strip_tac \\ first_x_assum drule
    \\ simp_tac std_ss []
    \\ once_rewrite_tac[GSYM in_ns_add_num_stubs]
    \\ asm_simp_tac(std_ss++ARITH_ss)[])
  \\ rpt gen_tac \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`compile_inc next1 prog1`
  \\ Cases_on`compile_inc next1 prog1`
  \\ drule compile_inc_lemma
  \\ `ALL_DISTINCT (MAP FST prog1)`
  by (
    simp[Abbr`prog1`,bvl_inlineTheory.compile_inc_def]
    \\ pairarg_tac \\ fs[]
    \\ fs[bvl_inlineTheory.tick_compile_prog_def]
    \\ imp_res_tac bvl_inlineProofTheory.tick_inline_all_names \\ fs[]
    \\ metis_tac[] )
  \\ fs[] \\ strip_tac
  \\ last_x_assum(qspec_then`k`mp_tac) \\ simp[]
  \\ strip_tac
  \\ fs[EVERY_MEM,EVERY_MAP,MEM_MAP,PULL_EXISTS,MEM_FILTER]
  \\ reverse conj_tac
  >- (
    rw[]
    \\ `in_ns 0 (FST x) ∨ in_ns 1 (FST x)` by metis_tac[]
    \\ pop_assum mp_tac \\ EVAL_TAC \\ rw[] )
  \\ simp[bvi_tailrecProofTheory.free_names_def]
  \\ rw[] \\ strip_tac
  \\ first_x_assum drule
  \\ pop_assum(assume_tac o SYM)
  \\ `in_ns 2 (FST x)`
  by ( fs[in_ns_def,backend_commonTheory.bvl_to_bvi_namespaces_def] )
  \\ IF_CASES_TAC
  >- ( ntac 2 (pop_assum mp_tac) \\ EVAL_TAC \\ rw[] )
  \\ strip_tac
  \\ rpt(qpat_x_assum`in_ns _ _`mp_tac) \\ EVAL_TAC \\ rw[]
QED

(* -- old version of the above proof --
Theorem compile_semantics:
   compile start c prog = (start', prog', n1, n2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   c.next_name2 = num_stubs + 2 + x * nss ∧
   (∀n. EVERY ((λe. handle_ok [e]) o SND o SND) (SND (co n))) ∧
   c.next_name1 ≤ FST (FST (co 0)) (* TODO:fix*) ∧
   semantics (ffi0:'ffi ffi_state) romAList prog) co (state_cc compile_inc cc) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') (state_co compile_inc co) cc start' =
   semantics ffi0 (fromAList prog) co (state_cc compile_inc cc) start
Proof
  srw_tac[][compile_def]
  \\ fs [LET_THM]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ drule (GEN_ALL compile_prog_semantics)
  \\ fs [bvl_inlineProofTheory.MAP_FST_compile_prog]
  \\ disch_then (qspec_then `ffi0` mp_tac)
  \\ rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rename1 `_ c.exp_cut prog = (_,prog3)`
  \\ `ALL_DISTINCT (MAP FST prog3)` by
        metis_tac [bvl_inlineProofTheory.MAP_FST_compile_prog,PAIR,FST,SND]
  \\ fs []
  \\ impl_tac THEN1 metis_tac [bvl_inlineProofTheory.compile_prog_handle_ok]
  \\ impl_tac
  THEN1
   (imp_res_tac bvl_inlineProofTheory.compile_prog_semantics
    \\ metis_tac [PAIR,FST,SND])
  \\ strip_tac
  \\ sg `EVERY (free_names c.next_name2 o FST) code /\
         ALL_DISTINCT (MAP FST code)`
  THEN1
   (drule compile_prog_distinct_locs
    \\ fs [bvl_inlineProofTheory.MAP_FST_compile_prog]
    \\ fs [EVERY_MEM,MEM_FILTER,bvi_tailrecProofTheory.free_names_def,
           FORALL_PROD,MEM_MAP,PULL_EXISTS,between_def]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ res_tac \\ fs []
    \\ `¬in_ns 2 (((k + x) * nss)+2)` by metis_tac[ADD_ASSOC,ADD_COMM,
                                                   RIGHT_ADD_DISTRIB]
    \\ fs[])
  \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_semantics)
  \\ disch_then drule
  \\ simp [bvi_tailrecTheory.compile_prog_def]
  \\ disch_then (qspecl_then [`loc`,`ffi0`] mp_tac)
  \\ metis_tac [bvl_inlineProofTheory.compile_prog_semantics,PAIR,FST,SND]
QED
*)

Theorem compile_distinct_names:
    bvl_to_bvi$compile n0 c p2 = (k,p3,n1,n2) /\
   ALL_DISTINCT (MAP FST p2) /\
   c.next_name2 = bvl_num_stubs + 2 + n02 * nss
   ==>
   EVERY (λn. data_num_stubs ≤ n) (MAP FST p3) /\
   ALL_DISTINCT (MAP FST p3)
Proof
  fs[bvl_to_bviTheory.compile_def]>>
  strip_tac>>
  rpt (pairarg_tac>>fs[]>>rveq>>fs[])>>
  drule (GEN_ALL compile_prog_distinct_locs) >>
  fs [bvl_to_bviTheory.compile_prog_def] >>
  rpt (pairarg_tac>>fs[]>>rveq>>fs[])>>
  strip_tac>>
  EVAL_TAC>>
  REWRITE_TAC[GSYM append_def] >>
  fs[EVERY_MEM]>>
  `ALL_DISTINCT (MAP FST prog)` by
    metis_tac [bvl_inlineProofTheory.compile_prog_names,PAIR,FST,SND] >>
  imp_res_tac (SIMP_RULE std_ss [] compile_list_distinct_locs)>>
  rfs[backend_commonTheory.bvl_num_stubs_def,
      bvl_inlineProofTheory.compile_prog_names]>>
  fs[EVERY_MEM]
  \\ simp[PULL_FORALL] \\ strip_tac
  \\ reverse conj_tac >- (
    match_mp_tac (
      bvi_tailrecProofTheory.compile_prog_ALL_DISTINCT
      |> UNDISCH_ALL
      |> CONJUNCT1
      |> DISCH_ALL
      |> GEN_ALL)
    \\ asm_exists_tac \\ simp[]
    \\ EVAL_TAC \\ fs [GSYM append_def]
    \\ CCONTR_TAC \\ fs []
    \\ res_tac \\ fs [EXISTS_MEM]
    \\ qpat_x_assum `!e. _ ==> between _ _ e` mp_tac
    \\ qpat_x_assum `!e. _ ==> between _ _ e` mp_tac
    \\ EVAL_TAC
    \\ strip_tac \\ fs [MEM_FILTER,bvi_tailrecProofTheory.free_names_def]
    \\ PairCases_on `e` \\ fs [GSYM append_def]
    \\ qexists_tac `e0` \\ fs []
    \\ rveq \\ fs [MEM_MAP,EXISTS_PROD,ODD_ADD]
    \\ res_tac \\ fs[]
    \\ qpat_x_assum`¬in_ns 2 _`mp_tac
    \\ EVAL_TAC \\ strip_tac
    \\ `(3 * (n02+k) + 2) MOD 3 ≠ 2` by fs[]
    \\ `¬in_ns 2 (nss * (n02+k) + 2)` by (EVAL_TAC \\ fs[])
    \\ fs[])
  \\ strip_tac
  \\ drule bvi_tailrecProofTheory.compile_prog_MEM
  \\ simp[]
  \\ EVAL_TAC
  \\ rw[] \\ simp[]
  \\ fs[GSYM append_def]
  \\ res_tac
  \\ pop_assum mp_tac
  \\ EVAL_TAC \\ rw[]
QED

Theorem ALL_DISTINCT_MAP_FST_SND_full_co:
   ALL_DISTINCT (MAP FST (SND (co n))) ∧
   (FST (SND (SND (FST (co n)))) MOD bvl_to_bvi_namespaces = 2)
  ⇒
   ALL_DISTINCT (MAP FST (SND (full_co c co n)))
Proof
  rw[full_co_def, bvi_tailrecProofTheory.mk_co_def, UNCURRY, backendPropsTheory.FST_state_co]
  \\ qmatch_goalsub_abbrev_tac`bvi_tailrec$compile_prog m xs`
  \\ Cases_on`bvi_tailrec$compile_prog m xs`
  \\ drule bvi_tailrecProofTheory.compile_prog_ALL_DISTINCT
  \\ impl_tac
  >- (
    simp[Abbr`xs`]
    \\ simp[backendPropsTheory.SND_state_co, backendPropsTheory.FST_state_co]
    \\ qmatch_goalsub_abbrev_tac`bvl_to_bvi$compile_inc v p`
    \\ Cases_on`bvl_to_bvi$compile_inc v p`
    \\ drule compile_inc_DISTINCT
    \\ impl_tac
    >- (
      simp[Abbr`p`]
      \\ simp[bvl_inlineTheory.compile_inc_def, UNCURRY]
      \\ simp[bvl_inlineTheory.tick_compile_prog_def]
      \\ simp[bvl_inlineProofTheory.MAP_FST_tick_inline_all] )
    \\ rw[]
    \\ drule (GEN_ALL compile_inc_next_range)
    \\ simp[MEM_MAP, PULL_EXISTS, GSYM ALL_EL_MAP, EVERY_MEM, EXISTS_PROD]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[bvi_tailrecProofTheory.free_names_def]
    \\ rw[] \\ strip_tac \\ rw[]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC \\ simp[] )
  \\ simp[]
QED

Theorem destLet_code_labels:
   destLet x = (y,z) ⇒
    BIGUNION (set (MAP get_code_labels y)) ∪ get_code_labels z ⊆ get_code_labels x
Proof
 Cases_on`x`
 \\ rw[bvl_to_bviTheory.destLet_def]
 \\ fs[bvl_to_bviTheory.destLet_def]
QED

Theorem compile_int_code_labels[simp]:
   ∀i. get_code_labels (compile_int i) = {}
Proof
  recInduct bvl_to_bviTheory.compile_int_ind
  \\ rw[]
  \\ rw[Once bvl_to_bviTheory.compile_int_def]
  \\ rw[closLangTheory.assign_get_code_label_def]
QED

Theorem compile_op_code_labels:
   get_code_labels (compile_op op c) ⊆
    BIGUNION (set (MAP get_code_labels c)) ∪
    IMAGE (λn. bvl_num_stubs + n * bvl_to_bvi_namespaces) (closLang$assign_get_code_label op) ∪
    set (MAP FST (bvl_to_bvi$stubs x y))
Proof
  simp[bvl_to_bviTheory.compile_op_def, bvl_to_bviTheory.stubs_def, SUBSET_DEF]
  \\ every_case_tac \\ fs[closLangTheory.assign_get_code_label_def, REPLICATE_GENLIST, PULL_EXISTS, MAPi_GENLIST, MEM_GENLIST]
  \\ rw[] \\ fsrw_tac[DNF_ss][PULL_EXISTS] \\ metis_tac[]
QED

Theorem compile_exps_get_code_labels:
   ∀n xs ys aux m.
    bvl_to_bvi$compile_exps n xs = (ys,aux,m) ⇒
     BIGUNION (set (MAP get_code_labels ys)) ∪
     BIGUNION (set (MAP (get_code_labels o SND o SND) (append aux)))
     ⊆
     IMAGE (λk. bvl_num_stubs + (k * bvl_to_bvi_namespaces)) (BIGUNION (set (MAP get_code_labels xs))) ∪
     { bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n ≤ k ∧ k < m } ∪
     set (MAP FST (bvl_to_bvi$stubs x y))
Proof
  recInduct bvl_to_bviTheory.compile_exps_ind
  \\ rw[bvl_to_bviTheory.compile_exps_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac destLet_code_labels \\ fs[NULL_EQ]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF, PULL_EXISTS]
  \\ imp_res_tac compile_exps_aux_sorted \\ fs[]
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_SING \\ rveq \\ fs[bvl_to_bviTheory.compile_aux_def]
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (disj1_tac \\ rpt disj2_tac
      \\ rw[] \\ res_tac \\ fs[]
      \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ qspecl_then[`op`,`c1`]mp_tac(Q.GENL[`op`,`c`]compile_op_code_labels)
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ strip_tac
    \\ TRY(last_x_assum drule \\ simp[] \\ strip_tac \\
            ((ntac 2 disj1_tac \\ disj2_tac \\ rpt(asm_exists_tac \\ simp[]) \\ NO_TAC) ORELSE
             (disj1_tac \\ rpt disj2_tac \\ asm_exists_tac \\ simp[] \\ NO_TAC) ORELSE
             (rpt disj2_tac \\ fs[] \\ NO_TAC)))
    \\ rpt disj1_tac
    \\ rveq \\ simp[]
    \\ metis_tac[])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    disj1_tac
    \\ disj2_tac
    \\ disj2_tac
    \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    Cases_on`dest` \\ fs[] \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    Cases_on`dest` \\ fs[] \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
QED

Theorem compile_exps_aux_contains:
   ∀n es c aux n1. compile_exps n es = (c,aux,n1) ⇒
    { bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n ≤ k ∧ k < n1 } ⊆ set (MAP FST (append aux))
Proof
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_ind
  \\ rw[bvl_to_bviTheory.compile_exps_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS] )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]  )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ `k = n2` by decide_tac \\ rveq \\ fs[]
    \\ fs[bvl_to_bviTheory.compile_aux_def] )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]  )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n3` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ `k = n3` by decide_tac \\ rveq \\ fs[]
    \\ fs[bvl_to_bviTheory.compile_aux_def] )
QED

Theorem compile_single_get_code_labels:
   ∀n p code m. compile_single n p = (code, m) ⇒
      BIGUNION (set (MAP (get_code_labels o SND o SND) (append code))) ⊆
      IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (get_code_labels (SND(SND p))) ∪
      set (MAP FST (append code)) ∪
      set (MAP FST (bvl_to_bvi$stubs x y))
Proof
  rw[]
  \\ PairCases_on`p`
  \\ fs[bvl_to_bviTheory.compile_single_def]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac compile_exps_get_code_labels
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_SING
  \\ rveq \\ fs[]
  \\ fs[bvl_to_bviTheory.compile_exps_def]
  \\ first_x_assum(qspecl_then[`y`,`x`]mp_tac)
  \\ fs[SUBSET_DEF, PULL_EXISTS] \\ strip_tac
  \\ drule compile_exps_aux_contains
  \\ fsrw_tac[DNF_ss][SUBSET_DEF] \\ rw[]
  \\ metis_tac[]
QED

Theorem compile_list_get_code_labels:
     ∀n p code m. compile_list n p = (code,m) ⇒
     n ≤ m ∧
     BIGUNION (set (MAP (get_code_labels o SND o SND) (append code))) ⊆
     set (MAP FST (append code)) ∪
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces)
       (BIGUNION (set (MAP (get_code_labels o SND o SND) p))) ∪
     set (MAP FST (bvl_to_bvi$stubs x y))
Proof
  Induct_on`p`
  \\ rw[bvl_to_bviTheory.compile_list_def]
  >- (EVAL_TAC \\ rw[])
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ first_x_assum drule \\ rw[]
  >- (
    PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac compile_exps_aux_sorted
    \\ fs[] )
  >- (
    drule compile_single_get_code_labels
    \\ rw[]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fsrw_tac[DNF_ss][] \\ rw[]
    \\ first_x_assum drule
    \\ simp[]
    \\ strip_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_LESS_TRANS,LESS_TRANS] )
  >- (
    fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
    \\ fsrw_tac[DNF_ss][]
    \\ first_x_assum drule \\ rw[]
    \\ PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac compile_exps_aux_sorted
    \\ metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_LESS_TRANS,LESS_TRANS,LESS_EQ_TRANS] )
QED

Theorem compile_prog_get_code_labels:
   ∀s n p t q m.
   bvl_to_bvi$compile_prog s n p = (t,q,m) ⇒
   BIGUNION (set (MAP (get_code_labels o SND o SND) q)) ⊆
     bvl_num_stubs + s * bvl_to_bvi_namespaces INSERT
     set (MAP FST q) ∪
     IMAGE (λk. bvl_num_stubs + (k * bvl_to_bvi_namespaces)) (BIGUNION (set (MAP (get_code_labels o SND o SND) p)))
Proof
  rw[bvl_to_bviTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[]
  \\ drule (GEN_ALL compile_list_get_code_labels)
  \\ strip_tac
  \\ reverse conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`stubs x y`
    \\ first_x_assum(qspecl_then[`y`,`x`]strip_assume_tac)
    \\ fs[SUBSET_DEF, PULL_EXISTS] \\ metis_tac[] )
  \\ simp[bvl_to_bviTheory.stubs_def]
  \\ rpt conj_tac
  \\ CONV_TAC(LAND_CONV EVAL) \\ simp[] \\ EVAL_TAC
  \\ simp[]
QED

Theorem compile_list_code_labels_domain:
   ∀n p code m. compile_list n p = (code,m) ⇒
     n ≤ m ∧
     set (MAP FST (append code)) =
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set (MAP FST p)) ∪
     { bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n ≤ k ∧ k < m }
Proof
  Induct_on`p`
  \\ rw[bvl_to_bviTheory.compile_list_def]
  >- (EVAL_TAC \\ rw[])
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ first_x_assum drule \\ rw[]
  >- (
    PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac compile_exps_aux_sorted
    \\ fs[] )
  \\ PairCases_on`h`
  \\ fs[bvl_to_bviTheory.compile_single_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac compile_exps_aux_sorted
  \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac compile_exps_aux_contains
  \\ fs[EVERY_MEM, SUBSET_DEF, PULL_EXISTS]
  \\ simp[Once EXTENSION]
  \\ rw[EQ_IMP_THM] \\ fs[between_def]
  \\ res_tac \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def] \\ rveq
  \\ fs[EVAL``bvl_num_stubs``] \\ rw[]
  \\ Cases_on`n1 ≤ k` \\ fs[]
QED

Theorem compile_prog_code_labels_domain:
   ∀s n p t q m.
   bvl_to_bvi$compile_prog s n p = (t,q,m) ⇒
   set (MAP FST q) =
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set (MAP FST p)) ∪
     { bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n ≤ k ∧ k < m } ∪
     set (MAP FST (bvl_to_bvi$stubs x y))
Proof
  rw[bvl_to_bviTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[]
  \\ drule compile_list_code_labels_domain \\ rw[]
  \\ rw[bvl_to_bviTheory.stubs_def]
  \\ metis_tac[UNION_ASSOC, UNION_COMM]
QED

val _ = export_theory();
