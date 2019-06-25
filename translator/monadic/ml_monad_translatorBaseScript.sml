(*
  Assertions about references and arrays are defined. Lemmas for these
  are proved, including reasoning in separation logic.
*)
open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory semanticPrimitivesTheory evaluateTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory Satisfy
open cfHeapsBaseTheory (* basisFunctionsLib *) AC_Sort
open ml_monadBaseTheory
open cfStoreTheory cfTheory cfTacticsLib

val _ = new_theory "ml_monad_translatorBase";

val HCOND_EXTRACT = cfLetAutoTheory.HCOND_EXTRACT;

fun set_imp_as_sg th = let
    val imp = concl th |> dest_imp |> fst
in sg `^imp` end

val clear_first_assum = POP_ASSUM (fn x => ALL_TAC)

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(* a few basics *)
Theorem with_same_refs:
   (s with refs := s.refs) = s
Proof
  simp[state_component_equality]
QED

Theorem with_same_ffi:
   (s with ffi := s.ffi) = s
Proof
  simp[state_component_equality]
QED

Theorem with_same_clock:
   (s with clock := s.clock) = s
Proof
  simp[state_component_equality]
QED

(* REF_REL *)
val REF_REL_def = Define `REF_REL TYPE r x = SEP_EXISTS v. REF r v * &TYPE x v`;

val H = mk_var("H",``:('a -> hprop) # 'ffi ffi_proj``);

(* REFS_PRED *)
val REFS_PRED_def = Define `
  REFS_PRED (h,p:'ffi ffi_proj) refs s = (h refs * GC) (st2heap p s)`;

val VALID_REFS_PRED_def = Define `
  VALID_REFS_PRED ^H = ?(s : 'ffi state) refs. REFS_PRED H refs s`;

(* Frame rule for EvalM *)

val REFS_PRED_FRAME_def = Define `
  REFS_PRED_FRAME ro (h,p:'ffi ffi_proj) (refs1, s1) (refs2, s2) <=>
    (ro ==> ?refs. s2 = s1 with refs := refs) /\
    !F. (h refs1 * F) (st2heap p s1) ==> (h refs2 * F * GC) (st2heap p s2)`;

Theorem EMP_STAR_GC:
   !H. emp * H = H
Proof
  fs[STAR_def, emp_def, SPLIT_def, ETA_THM]
QED

Theorem SAT_GC:
   !h. GC h
Proof
  fs[GC_def, SEP_EXISTS_THM] \\ STRIP_TAC \\ qexists_tac `\s. T` \\ fs[]
QED

Theorem REFS_PRED_FRAME_imp:
   !refs1 s1 H refs2 s2.
   REFS_PRED ^H refs1 s1 ==>
   REFS_PRED_FRAME ro H (refs1, s1) (refs2, s2) ==> REFS_PRED H refs2 s2
Proof
  rw[]
  \\ PairCases_on `H`
  \\ fs[REFS_PRED_def, REFS_PRED_FRAME_def]
  \\ fs[st2heap_def]
  \\ metis_tac[GC_STAR_GC, STAR_ASSOC]
QED

Theorem REFS_PRED_FRAME_trans:
   REFS_PRED_FRAME ro ^H (refs1, s1) (refs2, s2) ==>
   REFS_PRED_FRAME ro H (refs2, s2) (refs3, s3) ==>
   REFS_PRED_FRAME ro H (refs1, s1) (refs3, s3)
Proof
  Cases_on `H` >>
  rw[REFS_PRED_FRAME_def]
  THEN1 (fs [] \\ metis_tac []) >>
  PURE_REWRITE_TAC[Once (GSYM GC_STAR_GC), STAR_ASSOC] >>
  `q refs3 * F' * GC * GC = q refs3 * (F' * GC) * GC` by fs[STAR_ASSOC] >>
  POP_ASSUM (fn x => PURE_REWRITE_TAC[x]) >>
  first_x_assum irule >>
  fs[STAR_ASSOC]
QED

Theorem H_STAR_GC_SAT_IMP:
  H s ==> (H * GC) s
Proof
  rw[STAR_def]
  \\ qexists_tac `s`
  \\ qexists_tac `{}`
  \\ rw[SPLIT_emp2, SAT_GC]
QED

Theorem REFS_PRED_FRAME_same:
   !H st s. REFS_PRED_FRAME ro H (st,s) (st,s)
Proof
  Cases_on `H`
  \\ rw[REFS_PRED_FRAME_def]
  >-(fs[state_component_equality])
  \\ irule H_STAR_GC_SAT_IMP
  \\ fs[]
QED

(*
 * Proof of REFS_PRED_APPEND:
 * `REFS_PRED H refs s ==> REFS_PRED H refs (s with refs := s.refs ++ junk)`
 *)
Theorem store2heap_aux_Mem:
   !s n x. x IN (store2heap_aux n s) ==> ?n' v. x = Mem n' v
Proof
  Induct_on `s`
  >-(rw[IN_DEF, store2heap_def, store2heap_aux_def]) >>
  rw[] >> fs[IN_DEF, store2heap_def, store2heap_aux_def] >>
  last_x_assum IMP_RES_TAC >>
  fs[]
QED

Theorem store2heap_aux_IN_LENGTH:
   !s r x n. Mem r x IN (store2heap_aux n s) ==> r < n + LENGTH s
Proof
  Induct THENL [all_tac, Cases] \\
  fs [store2heap_aux_def] \\
  Cases_on `r` \\ fs [] \\ rewrite_tac [ONE] \\
  rpt strip_tac \\ fs[ADD_CLAUSES, GSYM store2heap_aux_suc] \\
  metis_tac[]
QED

val NEG_DISJ_TO_IMP = Q.prove(
  `!A B. ~A \/ ~B <=> A /\ B ==> F`,
  rw[]);

Theorem store2heap_aux_DISJOINT:
   !n s1 s2. DISJOINT (store2heap_aux n s1) (store2heap_aux (n + LENGTH s1) s2)
Proof
  rw[DISJOINT_DEF, INTER_DEF, EMPTY_DEF] >>
  fs[GSPECIFICATION_applied] >>
  `!x. {x | x ∈ store2heap_aux n s1 ∧
            x ∈ store2heap_aux (n + LENGTH s1) s2} x = (\x. F) x` by
     (rw[] >>
      PURE_REWRITE_TAC[NEG_DISJ_TO_IMP] >>
      DISCH_TAC >> rw[] >>
      IMP_RES_TAC store2heap_aux_Mem >>
      rw[] >>
      IMP_RES_TAC store2heap_aux_IN_bound >>
      IMP_RES_TAC store2heap_aux_IN_LENGTH >>
      bossLib.DECIDE_TAC) >>
  POP_ASSUM (fn x => ASSUME_TAC (EXT x)) >> fs[]
QED

Theorem store2heap_aux_SPLIT:
   !s1 s2 n. SPLIT (store2heap_aux n (s1 ++ s2))
                 (store2heap_aux n s1, store2heap_aux (n + LENGTH s1) s2)
Proof
  fs[SPLIT_def] >> fs[store2heap_aux_append_many] >>
  metis_tac[UNION_COMM, store2heap_aux_append_many, store2heap_aux_DISJOINT]
QED

Theorem store2heap_DISJOINT:
   DISJOINT (store2heap s1) (store2heap_aux (LENGTH s1) s2)
Proof
  fs[store2heap_def] >> metis_tac[store2heap_aux_DISJOINT, arithmeticTheory.ADD]
QED

(* If the goal is: (\x. P x) = (\x. Q x), applies SUFF_TAC ``!x. P x = Q x`` *)
fun SUFF_ABS_TAC (g as (asl, w)) =
  let
      val (e1, e2) = dest_eq w
      val (x1, e1') = dest_abs e1
      val (x2, e2') = dest_abs e2
      val _ = if x1 !~ x2 then failwith "" else ()
      val w' = mk_forall(x1,  mk_eq(e1', e2'))
  in
      (SUFF_TAC w' THEN rw[]) g
  end;

Theorem store2heap_SPLIT:
   !s1 s2. SPLIT (store2heap (s1 ++ s2))
                 (store2heap s1, store2heap_aux (LENGTH s1) s2)
Proof
  fs[store2heap_def] >> metis_tac[store2heap_aux_SPLIT, arithmeticTheory.ADD]
QED

Theorem SPLIT_DECOMPOSWAP:
   SPLIT s1 (s2, s3) ==> SPLIT s2 (u, v) ==> SPLIT s1 (u, v UNION s3)
Proof
  fs[SPLIT_def, UNION_ASSOC, DISJOINT_SYM] >> rw[] >>
  fs[DISJOINT_SYM, DISJOINT_UNION_BOTH]
QED

Theorem STORE_APPEND_JUNK:
   !H s junk. H (store2heap s) ==> (H * GC) (store2heap (s ++ junk))
Proof
  rw[] >>
  qspecl_then [`s`, `junk`] ASSUME_TAC store2heap_SPLIT >>
  fs[STAR_def] >>
  qexists_tac `store2heap s` >>
  qexists_tac `store2heap_aux (LENGTH s) junk` >>
  `!H. GC H` by (rw[cfHeapsBaseTheory.GC_def, SEP_EXISTS] >>
                 qexists_tac `\x. T` >> fs[]) >>
  POP_ASSUM (fn x => fs[x])
QED

Theorem st2heap_SPLIT_FFI:
   !f st. SPLIT ((store2heap st.refs) UNION (ffi2heap f st.ffi))
                (store2heap st.refs, ffi2heap f st.ffi)
Proof
  rw[SPLIT_def]
  \\ fs[IN_DISJOINT]
  \\ STRIP_TAC
  \\ PURE_REWRITE_TAC[NEG_DISJ_TO_IMP]
  \\ STRIP_TAC
  \\ rw[]
  \\ fs[store2heap_def]
  \\ Cases_on `x`
  \\ fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux,
        FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux]
QED

Theorem SPLIT3_swap12:
   !h h1 h2 h3. SPLIT3 h (h1, h2, h3) = SPLIT3 h (h2, h1, h3)
Proof
  rw[SPLIT3_def, UNION_COMM, CONJ_COMM] >> metis_tac[DISJOINT_SYM]
QED

Theorem SPLIT_of_SPLIT3_1u3:
   ∀h h1 h2 h3. SPLIT3 h (h1,h2,h3) ⇒ SPLIT h (h2, h1 ∪ h3)
Proof
  metis_tac[SPLIT3_swap12, SPLIT_of_SPLIT3_2u3]
QED

Theorem SPLIT2_SPLIT3:
   SPLIT s1 (s2, t3) /\ SPLIT s2 (t1, t2) ==> SPLIT3 s1 (t1, t2, t3)
Proof
  rw[SPLIT_def] \\ fs[SPLIT3_def]
QED

Theorem SPLIT_SYM:
   SPLIT s (s1, s2) = SPLIT s (s2, s1)
Proof
  fs[SPLIT_def, DISJOINT_SYM, UNION_COMM]
QED

Theorem STATE_APPEND_JUNK:
   !H p s refs junk. H (st2heap p (s with refs := refs)) ==>
  (H * GC) (st2heap p (s with refs := refs ++ junk))
Proof
  rw[]
  \\ Cases_on `p`
  \\ fs[st2heap_def]
  \\ Q.PAT_ABBREV_TAC `h = A UNION B`
  \\ sg `SPLIT3 h (store2heap refs, store2heap_aux (LENGTH refs) junk,
                   ffi2heap (q,r) s.ffi)`
  >-(
     fs[markerTheory.Abbrev_def] \\ rw[]
     \\ irule SPLIT2_SPLIT3
     \\ qexists_tac `store2heap (refs ++ junk)`
     \\ fs[store2heap_SPLIT, SPLIT_def, IN_DISJOINT, store2heap_def]
     \\ PURE_REWRITE_TAC[NEG_DISJ_TO_IMP]
     \\ rpt STRIP_TAC
     \\ Cases_on `x`
     \\ fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux,
           FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
  \\ fs[markerTheory.Abbrev_def] \\ rw[]
  \\ POP_ASSUM(fn x => MATCH_MP SPLIT_of_SPLIT3_1u3 x |> ASSUME_TAC)
  \\ fs[Once SPLIT_SYM]
  \\ rw[STAR_def]
  \\ metis_tac[SAT_GC]
QED

Theorem STATE_SPLIT_REFS:
   !a b p s. SPLIT (st2heap p (s with refs := a ++ b))
  ((st2heap p (s with refs := a)), (store2heap_aux (LENGTH a) b))
Proof
  rw[] \\ Cases_on `p` \\ fs[st2heap_def] \\
  sg `SPLIT3 (store2heap (a ++ b) ∪ ffi2heap (q,r) s.ffi)
             (store2heap a, store2heap_aux (LENGTH a) b, ffi2heap (q,r) s.ffi)`
  >-(
     irule SPLIT2_SPLIT3
     \\ qexists_tac `store2heap (a ++ b)`
     \\ fs[store2heap_SPLIT, SPLIT_def, IN_DISJOINT, store2heap_def]
     \\ PURE_REWRITE_TAC[NEG_DISJ_TO_IMP]
     \\ rpt STRIP_TAC
     \\ Cases_on `x`
     \\ fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux,
           FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
  \\ POP_ASSUM(fn x => MATCH_MP SPLIT_of_SPLIT3_1u3 x |> ASSUME_TAC)
  \\ fs[Once SPLIT_SYM]
  \\ rw[STAR_def]
QED

Theorem REFS_PRED_append:
   !H refs s. REFS_PRED H refs s ==>
              REFS_PRED ^H refs (s with refs := s.refs ++ junk)
Proof
  Cases >>
  rw[REFS_PRED_def] >> PURE_ONCE_REWRITE_TAC [GSYM GC_STAR_GC] >>
  fs[STAR_ASSOC] >>
  metis_tac[with_same_refs, STATE_APPEND_JUNK]
QED

Theorem REFS_PRED_qappend:
   ∀H refs s.
     REFS_PRED H refs s ⇒
     !junk.
     REFS_PRED H refs (s with refs := s.refs ⧺ junk)
Proof
  fs[REFS_PRED_append]
QED

Theorem REFS_PRED_FRAME_append:
   !H refs s. REFS_PRED_FRAME ro ^H (refs, s) (refs, s with refs := s.refs ++ junk)
Proof
  Cases >>
  rw[REFS_PRED_FRAME_def] \\ metis_tac[with_same_refs, STATE_APPEND_JUNK]
QED

(*
 * Proof of STORE_EXTRACT_FROM_HPROP:
 * `!l xv H s. (REF (Loc l) xv * H) (store2heap s) ==> ?ps. ((ps ++ [Refv xv]) ≼ s) /\ LENGTH ps = l`
 *)

Theorem HEAP_LOC_MEM:
   (l ~~>> rv * H) h ==> Mem l rv IN h
Proof
  rw[STAR_def, SEP_EXISTS_THM, cond_def, cell_def, one_def, SPLIT_def]
  \\ rw[IN_UNION]
QED

Theorem st2heap_CELL_MEM:
   (l ~~>> rv * H) (st2heap p s) ==> Mem l rv IN (store2heap s.refs)
Proof
  Cases_on `p` \\ rw[st2heap_def] \\ IMP_RES_TAC HEAP_LOC_MEM
  \\ fs[IN_UNION]
  \\ fs[Mem_NOT_IN_ffi2heap]
QED

Theorem st2heap_REF_MEM:
   (Loc l ~~> xv * H) (st2heap p s) ==> Mem l (Refv xv) IN (store2heap s.refs)
Proof
  rw[REF_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  metis_tac[st2heap_CELL_MEM]
QED

Theorem st2heap_ARRAY_MEM:
   (ARRAY (Loc l) av * H) (st2heap p s) ==> Mem l (Varray av) IN (store2heap s.refs)
Proof
  rw[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  metis_tac[st2heap_CELL_MEM]
QED

Theorem store2heap_aux_LOC_MEM:
   !l rv H n s. (l ~~>> rv * H) (store2heap_aux n s) ==>
                Mem l rv IN (store2heap_aux n s)
Proof
  rw[] \\ IMP_RES_TAC HEAP_LOC_MEM
QED

Theorem store2heap_LOC_MEM:
   !l rv H s. (l ~~>> rv * H) (store2heap s) ==> Mem l rv IN (store2heap s)
Proof
  rw[] \\ IMP_RES_TAC HEAP_LOC_MEM
QED

Theorem isPREFIX_TAKE:
   !l s. isPREFIX (TAKE l s) s
Proof
  rw[] >>
  `isPREFIX (TAKE l s) (TAKE l s ++ DROP l s)` by fs[TAKE_DROP] >>
  metis_tac[TAKE_DROP]
QED

Theorem isPREFIX_APPEND_EQ:
   !a1 a2 b1 b2.
     LENGTH a1 = LENGTH a2 ==>
     (isPREFIX (a1 ++ b1) (a2 ++ b2) <=> a2 = a1 /\ isPREFIX b1 b2)
Proof
  Induct_on `a1` >- fs[LENGTH_NIL_SYM] >>
  rw[] >>
  Cases_on `a2` >- fs[] >>
  fs[] >> metis_tac[]
QED

Theorem STATE_DECOMPOS_FROM_HPROP:
   !l rv H p s. (l ~~>> rv * H) (st2heap p s) ==>
                ?ps. ((ps ++ [rv]) ≼ s.refs) /\ LENGTH ps = l
Proof
  rw[] >>
  IMP_RES_TAC st2heap_CELL_MEM >>
  IMP_RES_TAC store2heap_IN_EL >>
  qexists_tac `TAKE l s.refs` >>
  Cases_on `l + 1 <= LENGTH s.refs`
  >-(
      fs[LENGTH_TAKE] >>
      SUFF_TAC ``isPREFIX [rv : v store_v] (DROP l s.refs)``
      >- metis_tac[LENGTH_TAKE, LENGTH_DROP, GSYM isPREFIX_APPEND_EQ, TAKE_DROP] >>
      FIRST_ASSUM (fn x => PURE_REWRITE_TAC[x]) >>
      SUFF_TAC ``(rv : v store_v) = HD(DROP l s.refs)``
      >-( fs[] >> Cases_on `DROP l s.refs` >- fs[DROP_NIL] >> fs[]) >>
      fs[HD_DROP]
  ) >>
  irule FALSITY >>
  IMP_RES_TAC store2heap_IN_LENGTH >>
  fs[]
QED

Theorem STATE_DECOMPOS_FROM_HPROP_REF:
   !l xv H p s. (REF (Loc l) xv * H) (st2heap p s) ==>
                ?ps. ((ps ++ [Refv xv]) ≼ s.refs) /\ LENGTH ps = l
Proof
  rw[REF_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_DECOMPOS_FROM_HPROP >>
  instantiate
QED

Theorem STATE_DECOMPOS_FROM_HPROP_ARRAY:
   !l av H p s. (ARRAY (Loc l) av * H) (st2heap p s) ==>
                ?ps. ((ps ++ [Varray av]) ≼ s.refs) /\ LENGTH ps = l
Proof
  rw[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_DECOMPOS_FROM_HPROP >>
  instantiate
QED

Theorem STATE_EXTRACT_FROM_HPROP:
   !l rv H p s. (l ~~>> rv * H) (st2heap p s) ==>
  !junk. EL l (s.refs ++ junk) = rv
Proof
  rw[] >>
  IMP_RES_TAC STATE_DECOMPOS_FROM_HPROP >>
  fs[IS_PREFIX_APPEND] >>
  first_x_assum(fn x => CONV_RULE
    (CHANGED_CONV (SIMP_CONV pure_ss [GSYM APPEND_ASSOC])) x |> ASSUME_TAC) >>
  `~NULL ([rv] ++ (l' ++ junk))` by fs[NULL_EQ] >>
  IMP_RES_TAC EL_LENGTH_APPEND >>
  fs[HD] >>
  metis_tac[]
QED

Theorem STATE_EXTRACT_FROM_HPROP_REF:
   !l xv H p s. ((Loc l) ~~> xv * H) (st2heap p s) ==>
  !junk. EL l (s.refs ++ junk) = Refv xv
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_EXTRACT_FROM_HPROP >>
  instantiate
QED

Theorem STATE_EXTRACT_FROM_HPROP_ARRAY:
   !l av H p s. (ARRAY (Loc l) av * H) (st2heap p s) ==>
  !junk. EL l (s.refs ++ junk) = Varray av
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_EXTRACT_FROM_HPROP >>
  instantiate
QED

Theorem SEPARATE_STORE_ELEM_IN_HEAP:
   !s0 x s1. SPLIT3 (store2heap (s0 ++ [x] ++ s1))
                    (store2heap s0, {Mem (LENGTH s0) x},
                     store2heap_aux (LENGTH s0 + 1) s1)
Proof
  sg `!(s0 : v store) s1 x.
         SPLIT (store2heap_aux (LENGTH s0) (x::s1))
               ({Mem (LENGTH s0) x}, store2heap_aux (LENGTH s0 + 1) s1)`
  >-(
      rw[store2heap_def] >>
      PURE_REWRITE_TAC[Once rich_listTheory.CONS_APPEND] >>
      PURE_REWRITE_TAC [GSYM (EVAL ``store2heap_aux (LENGTH (s0 : v store)) [x]``)] >>
      ASSUME_TAC (EVAL ``LENGTH [x : v store_v]``) >>
      metis_tac[store2heap_aux_SPLIT, ADD_COMM]
  ) >>
  rw[] >>
  qspecl_then [`s0`, `[x] ++ s1`] ASSUME_TAC store2heap_SPLIT >> fs[] >>
  last_x_assum(qspecl_then [`s0`, `s1`, `x`] ASSUME_TAC) >>
  fs[SPLIT_def, SPLIT3_def] >>
  rw[]
  >-(metis_tac[UNION_ASSOC, EQ_REFL])
  >-(DISCH_TAC >> IMP_RES_TAC store2heap_IN_LENGTH >> fs[]) >>
  metis_tac[DISJOINT_UNION_BOTH, EQ_REFL]
QED

Theorem CELL_HPROP_SAT_EQ:
   !l xv s. (l ~~>> xv) s <=> s = {Mem l xv}
Proof
  fs[REF_def, SEP_EXISTS, HCOND_EXTRACT, cell_def, one_def]
QED

Theorem REF_HPROP_SAT_EQ:
   !l xv s. REF (Loc l) xv s <=> s = {Mem l (Refv xv)}
Proof
  fs[REF_def, SEP_EXISTS, HCOND_EXTRACT, cell_def, one_def]
QED

Theorem ARRAY_HPROP_SAT_EQ:
   !l av s. ARRAY (Loc l) av s <=> s = {Mem l (Varray av)}
Proof
  fs[ARRAY_def, SEP_EXISTS, HCOND_EXTRACT, cell_def, one_def]
QED

Theorem SPLIT_UNICITY_R:
   SPLIT s (u, v) ==> (SPLIT s (u, v') <=> v' = v)
Proof
  fs[SPLIT_EQ]
QED

Theorem DIFF_UNION_COMM:
   DISJOINT s2 s3 ==>
  (s1 UNION s2) DIFF s3 = (s1 DIFF s3) UNION s2
Proof
  rw[SET_EQ_SUBSET]
  \\ fs[SUBSET_DEF, IN_DISJOINT] \\rw[]
  \\ last_x_assum (fn x => PURE_ONCE_REWRITE_RULE [NEG_DISJ_TO_IMP] x |> IMP_RES_TAC)
  \\ fs[]
QED

Theorem STATE_SAT_CELL_STAR_H_EQ:
   !p s s0 rv s1 H.
     ((LENGTH s0) ~~>> rv * H) (st2heap p (s with refs := s0 ++ [rv] ++ s1)) <=>
     H ((store2heap s0) UNION
       (store2heap_aux (LENGTH s0 + 1) s1) UNION
       (ffi2heap p s.ffi))
Proof
  rw[] >>
  Cases_on `p` >>
  fs[st2heap_def] >>
  qspecl_then [`p`, `s with refs := s0 ++ [rv] ++ s1`] ASSUME_TAC st2heap_SPLIT_FFI >>
  fs[] >>
  qspecl_then [`s0`, `rv`, `s1`] ASSUME_TAC SEPARATE_STORE_ELEM_IN_HEAP >>
  IMP_RES_TAC SPLIT_of_SPLIT3_1u3 >>
  EQ_TAC
  >-(
      rw[STAR_def, CELL_HPROP_SAT_EQ] >>
      fs[SPLIT_EQ] >>
      rw[] >>
      fs[st2heap_def] >>
      `DISJOINT (ffi2heap (q, r) s.ffi) {Mem (LENGTH s0) rv}` by
          fs[DISJOINT_DEF, Mem_NOT_IN_ffi2heap] >>
      fs[Once DIFF_UNION_COMM]
  ) >>
  DISCH_TAC >>
  rw[STAR_def] >>
  instantiate >>
  qexists_tac `{Mem (LENGTH s0) rv}` >>
  fs[CELL_HPROP_SAT_EQ] >>
  fs[SPLIT_def, SPLIT3_def] >>
  rw[]
  >-(
      rw[store2heap_append_many, store2heap_aux_append_many]
      >> metis_tac[store2heap_aux_def, UNION_COMM, UNION_ASSOC])
  \\ fs[Mem_NOT_IN_ffi2heap]
QED

Theorem STATE_SAT_REF_STAR_H_EQ:
   !p s s0 xv s1 H.
     (Loc (LENGTH s0) ~~> xv * H)
        (st2heap p (s with refs := s0 ++ [Refv xv] ++ s1)) <=>
     H ((store2heap s0) UNION
        (store2heap_aux (LENGTH s0 + 1) s1) UNION (ffi2heap p s.ffi))
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  fs[STATE_SAT_CELL_STAR_H_EQ]
QED

Theorem STATE_SAT_ARRAY_STAR_H_EQ:
   !p s s0 av s1 H.
     (ARRAY (Loc (LENGTH s0)) av * H)
        (st2heap p (s with refs := s0 ++ [Varray av] ++ s1)) <=>
     H ((store2heap s0) UNION
        (store2heap_aux (LENGTH s0 + 1) s1) UNION (ffi2heap p s.ffi))
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  fs[STATE_SAT_CELL_STAR_H_EQ]
QED

Theorem STATE_UPDATE_HPROP_CELL:
   (l ~~>> rv * H) (st2heap p s) ==> (l ~~>> rv' * H)
    (st2heap p (s with refs := (LUPDATE rv' l s.refs)))
Proof
  DISCH_TAC >>
  sg `?s0 s1. s.refs = s0 ++ [rv] ++ s1 /\ LENGTH s0 = l`
  >-(
      IMP_RES_TAC STATE_DECOMPOS_FROM_HPROP >>
      IMP_RES_TAC rich_listTheory.IS_PREFIX_APPEND >>
      SATISFY_TAC
  ) >>
  rw[LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_def] >>
  fs[STATE_SAT_CELL_STAR_H_EQ] >>
  sg `(st2heap p s) = st2heap p (s with refs := s0 ++ [rv] ++ s1)`
  >-(
     `s = (s with refs := s0 ++ [rv] ++ s1)` by
            POP_ASSUM (fn x => rw[GSYM x, with_same_refs])
     >> POP_ASSUM(fn x => rw[GSYM x])
  ) >>
  POP_ASSUM(fn x => fs[x]) >>
  fs[STATE_SAT_CELL_STAR_H_EQ]
QED

Theorem STATE_UPDATE_HPROP_REF:
   (Loc l ~~> xv * H) (st2heap p s) ==> (Loc l ~~> xv' * H)
     (st2heap p (s with refs := (LUPDATE (Refv xv') l s.refs)))
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_UPDATE_HPROP_CELL >>
  instantiate
QED

Theorem STATE_UPDATE_HPROP_ARRAY:
   (ARRAY (Loc l) av * H) (st2heap p s) ==> (ARRAY (Loc l) av' * H)
     (st2heap p (s with refs := (LUPDATE (Varray av') l s.refs)))
Proof
  rw[REF_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
  fs[GSYM STAR_ASSOC, HCOND_EXTRACT] >>
  irule STATE_UPDATE_HPROP_CELL >>
  instantiate
QED

(*
Theorem evaluate_empty_state_IMP_junk:
   !junk refs' env s exp x.
     evaluate F env (empty_state with refs := s.refs ++ junk) exp
     (empty_state with refs := s.refs ++ junk ++ refs',Rval x) ⇒
     evaluate F env (s with refs := s.refs ++ junk) exp
       (s with refs := s.refs ++ junk ++ refs',Rval x)
Proof
  rw[]
  \\ ASSUME_TAC (
  Thm.INST_TYPE [``:'ffi`` |-> ``:'a``] evaluate_empty_state_IMP |>
  Thm.INST[``s:'a state`` |-> ``(s:'a state) with refs := s.refs ++ junk``])
  \\ fs[]
QED
*)

(* Fixed-size arrays *)
val ARRAY_REL = Define `
  ARRAY_REL TYPE rv l = SEP_EXISTS av. ARRAY rv av * &LIST_REL TYPE l av`;

(* Resizable arrays *)
val RARRAY_def = Define `
  RARRAY rv av = SEP_EXISTS arv. REF rv arv * ARRAY arv av`;

val RARRAY_REL_def = Define `
  RARRAY_REL TYPE rv l = SEP_EXISTS av. RARRAY rv av * &LIST_REL TYPE l av`;

Theorem RARRAY_HPROP_SAT_EQ:
   RARRAY (Loc l) av s <=>
  ?l'. s = {Mem l' (Varray av); Mem l (Refv (Loc l'))}
Proof
  fs[RARRAY_def, ARRAY_def, REF_def, SEP_EXISTS,
     HCOND_EXTRACT, cell_def, one_def, STAR_def]
  \\ EQ_TAC
  >-(rw[SPLIT_def, cond_def]
     \\ qexists_tac `y'`
     \\ PURE_ONCE_REWRITE_TAC[UNION_COMM]
     \\ irule EQ_EXT
     \\ rw[])
  \\ rw[SPLIT_def, cond_def]
  \\ qexists_tac `Loc l'`
  \\ rw[]
  \\ PURE_ONCE_REWRITE_TAC[UNION_COMM]
  \\ irule EQ_EXT
  \\ rw[]
QED

val GC_ABSORB_L = Q.prove(`!A B s. (A * B * GC) s ==> (A * GC) s`,
rw[]
\\ fs[GSYM STAR_ASSOC]
\\ fs[Once STAR_def]
\\ qexists_tac `u`
\\ qexists_tac `v`
\\ fs[SAT_GC]);

Theorem st2heap_SPLIT:
  SPLIT (st2heap ffi (s with refs := s.refs ++ junk))
        (st2heap ffi s, store2heap_aux (LENGTH s.refs) junk)
Proof
  rw[SPLIT_def, st2heap_def, store2heap_def]
  >-(
      fs[store2heap_aux_append_many]
      \\ metis_tac[UNION_COMM, UNION_ASSOC])
  >-(
      qspec_then `0` assume_tac store2heap_aux_DISJOINT
      \\ fs[])
  \\ fs[IN_DISJOINT]
  \\ PURE_REWRITE_TAC[NEG_DISJ_TO_IMP]
  \\ rw[]
  \\ Cases_on `x`
  \\ fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux,
        FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux]
QED

Theorem REFS_PRED_FRAME_remove_junk:
  REFS_PRED_FRAME ro H (n_st,s1 with refs := s1.refs ⧺ junk) (st2,s2) ==>
  REFS_PRED_FRAME ro H (n_st,s1) (st2,s2)
Proof
  Cases_on `H`
  \\ rw[REFS_PRED_FRAME_def]
  \\ first_x_assum (qspec_then `F' * (\h. h = store2heap_aux (LENGTH s1.refs) junk)` assume_tac)
  \\ first_assum set_imp_as_sg
  >-(
      clear_first_assum
      \\ fs[STAR_ASSOC]
      \\ rw[Once STAR_def]
      \\ qexists_tac `st2heap r s1`
      \\ fs[st2heap_SPLIT]
      \\ fs[st2heap_def])
  \\ fs[] \\ clear_first_assum
  \\ fs[STAR_ASSOC]
  \\ drule GC_ABSORB_L
  \\ fs[]
QED

val _ = export_theory();
