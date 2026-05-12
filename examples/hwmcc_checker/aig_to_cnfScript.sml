(*
  Mapping And-Inverter Graphs into CNF
*)
Theory aig_to_cnf
Ancestors
  misc mlstring aig cnf
Libs
  preamble

(*----------------------------------------------------------------------*
   pruning
 *----------------------------------------------------------------------*)

Definition new_live_def:
  new_live ([] : (('a,'i,'l) var # bool) list) l = (l:'a |-> unit) ∧
  new_live ((x,b) :: xs) l =
    case x of
    | Name n => new_live xs l |+ (n,())
    | Base _ => new_live xs l
End

Definition prune_def:
  prune ([]:('a,'i,'l) and list) (live :'a |-> unit) = [] ∧
  prune ((m,ts)::xs) live =
    case FLOOKUP live m of
    | NONE => prune xs live
    | _ =>
        let live' = live \\ m in
          (m,ts) :: prune xs (new_live ts live')
End

Definition prune_for_def:
  prune_for name ands = prune ands (FEMPTY |+ (name,()))
End

Theorem EVERY_EQ_EVERY[local]:
  EVERY (λx. P x = Q x) xs ⇒ (EVERY P xs = EVERY Q xs)
Proof
  Induct_on ‘xs’\\ fs []
QED

Theorem new_live_thm:
  ∀h1 live aa.
    MEM (Name aa,r) h1 ⇒
    FLOOKUP (new_live h1 live) aa = SOME ()
Proof
  Induct
  \\ fs [new_live_def,FORALL_PROD]
  \\ Cases \\ fs []
  \\ rw [] \\ rw [FLOOKUP_SIMP]
QED

Theorem new_live_pres[local]:
  ∀xs live name.
    FLOOKUP live name = SOME () ⇒
    FLOOKUP (new_live xs live) name = SOME ()
Proof
  Induct \\ simp [new_live_def, FORALL_PROD]
  \\ Cases \\ simp [new_live_def, FORALL_PROD]
  \\ rw [] \\ rw [FLOOKUP_SIMP]
QED

Theorem eval_circuit_prune:
  ∀ands name live x.
    FLOOKUP live name = SOME x ⇒
    eval_circuit (is,ls) ands name =
    eval_circuit (is,ls) (prune ands live) name
Proof
  Induct
  \\ fs [eval_circuit_def,prune_def]
  \\ PairCases \\ simp []
  \\ rw [prune_def]
  >-
   (simp [eval_circuit_def]
    \\ irule EVERY_EQ_EVERY
    \\ simp [EVERY_MEM]
    \\ Cases \\ Cases_on ‘q’
    \\ simp [eval_circuit_def]
    \\ rename [‘Name aa’]
    \\ strip_tac
    \\ first_x_assum $ qspecl_then [‘aa’,‘new_live h1 (live \\ h0)’] mp_tac
    \\ reverse impl_tac >- simp []
    \\ irule new_live_thm
    \\ simp [new_live_thm]
    \\ pop_assum $ irule_at Any)
  \\ CASE_TAC
  \\ simp [eval_circuit_def]
  \\ last_x_assum irule
  \\ irule new_live_pres
  \\ rw [] \\ fs [FLOOKUP_DEF]
QED

Definition eval_circuit'_def:
  eval_circuit' is_ls [] = F ∧
  eval_circuit' is_ls ((x,ts)::rest) = eval_circuit is_ls ((x,ts)::rest) x
End

Theorem eval_circuit'_same:
  (~NULL ands ⇒ FST (HD ands) = name) ⇒
  (eval_circuit (is,ls) ands name ⇔ eval_circuit' (is,ls) ands)
Proof
  Cases_on ‘ands’ \\ fs [eval_circuit'_def, eval_circuit_def]
  \\ PairCases_on ‘h’ \\ fs [eval_circuit'_def, eval_circuit_def]
QED

Theorem eval_circuit_prune_for:
  eval_circuit' (is,ls) (prune_for name ands) =
  eval_circuit (is,ls) ands name
Proof
  simp [Once EQ_SYM_EQ, prune_for_def]
  \\ irule EQ_TRANS
  \\ irule_at Any eval_circuit_prune
  \\ qrefinel [‘_’,‘FEMPTY⟨name ↦ ()⟩’]
  \\ simp [FLOOKUP_SIMP]
  \\ irule eval_circuit'_same
  \\ Induct_on ‘ands’ \\ fs [prune_def]
  \\ Cases \\ fs [prune_def, FLOOKUP_SIMP]
  \\ IF_CASES_TAC \\ fs []
QED

(*----------------------------------------------------------------------*
   renaming
 *----------------------------------------------------------------------*)

Definition aig_rename_aux_def:
  aig_rename_aux [] next im lm nm acc =
    ((acc:((num, num, num) var # bool) list, next:num, im, lm)) ∧
  aig_rename_aux ((x,b)::rest) next im lm nm acc =
    case (x : ('a, 'b, 'c) var) of
    | Name n =>
        (case FLOOKUP nm n of
         | NONE   => aig_rename_aux rest next im lm nm ((Base Ff,b)::acc)
         | SOME t => aig_rename_aux rest next im lm nm ((Name t,b)::acc))
    | Base (Input i) =>
        (case FLOOKUP im i of
         | NONE   => aig_rename_aux rest (next+1)
                       (im |+ (i,next)) lm nm ((Base (Input next),b)::acc)
         | SOME t => aig_rename_aux rest next im lm nm ((Base (Input t),b)::acc))
    | Base (Latch l) =>
        (case FLOOKUP lm l of
         | NONE   => aig_rename_aux rest (next+1) im
                       (lm |+ (l,next)) nm ((Base (Latch next),b)::acc)
         | SOME t => aig_rename_aux rest next im lm nm ((Base (Latch t),b)::acc))
    | Base Ff => aig_rename_aux rest next im lm nm ((Base Ff,b)::acc)
End

Definition aig_rename_def:
  aig_rename ([]:('a,'i,'l) and list) =
    ([]:(num,num,num) and list,0n,FEMPTY,FEMPTY,FEMPTY) ∧
  aig_rename ((m,ts)::xs) =
    let (res,next,im,lm,nm) = aig_rename xs in
    let (ts1,next,im,lm) = aig_rename_aux ts next im lm nm [] in
      ((next,ts1)::res, next+1, im, lm, nm |+ (m, next))
End

Definition DISJOINT3_def:
  DISJOINT3 s1 s2 s3 ⇔
    DISJOINT s1 s2 ∧ DISJOINT s1 s3 ∧ DISJOINT s2 s3
End

Definition aig_read_def:
  aig_read is im n = ∃t. is t ∧ FLOOKUP im t = SOME n
End

Definition has_var_def:
  has_var v ([]:('a,'i,'l) and list) = F ∧
  has_var v ((n,ts)::rest) = (has_var v rest ∨ ∃b. MEM (Base v,b) ts)
End

Theorem FUNION_SUBMAP_lemma[local]:
  im_1 SUBMAP im_2 ⇒
  (im_1 ⊌ im_2 = im_2) ∧
  FDOM im_1 ∪ FDOM im_2 = FDOM im_2
Proof
  rpt strip_tac
  >- (gvs [TO_FLOOKUP,FLOOKUP_FUNION,FUN_EQ_THM] \\ rw [] \\ CASE_TAC \\ rw [])
  \\ gvs [SUBMAP_DEF, EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ res_tac \\ fs []
QED

Theorem aig_rename_aux_acc:
  ∀ts next_1 im_1 lm_1 nm_1 acc.
    aig_rename_aux ts next_1 im_1 lm_1 nm_1 acc =
    let (ts_1,next_2,im_2,lm_2) = aig_rename_aux ts next_1 im_1 lm_1 nm_1 [] in
      (ts_1 ++ acc,next_2,im_2,lm_2)
Proof
  Induct \\ fs [aig_rename_aux_def] \\ PairCases
  \\ once_rewrite_tac [aig_rename_aux_def]
  \\ pop_assum $ once_rewrite_tac o single \\ rw []
  \\ rpt (CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem not_eval_circuit:
  ∀ands a. ~MEM a (MAP FST ands) ⇒ ¬eval_circuit (is,ls) ands a
Proof
  Induct \\ fs [eval_circuit_def, FORALL_PROD]
QED

Theorem aig_read_thm:
  INJ (FAPPLY (im_2 ⊌ ix)) (FDOM im_2 ∪ FDOM ix) UNIV ∧
  FLOOKUP im_2 i = SOME x ⇒
  aig_read is (im_2 ⊌ ix) x = is i
Proof
  rw [aig_read_def]
  \\ qsuff_tac ‘∀y. FLOOKUP (im_2 ⊌ ix) y = SOME x ⇔ y = i’
  >- (disch_then $ rewrite_tac o single \\ fs [])
  \\ rw [] \\ reverse eq_tac \\ rw []
  >- gvs [FLOOKUP_FUNION]
  \\ fs [INJ_DEF]
  \\ last_x_assum irule
  \\ fs [FLOOKUP_DEF,FUNION_DEF]
QED

Theorem IMP_DISJOINT3:
  INJ (FAPPLY lm_1) (FDOM lm_1) 𝕌(:num) ∧
  i ∉ FDOM lm_1 ∧
  (∀n. next_1 ≤ n ⇒ n ∉ FRANGE im_1 ∧ n ∉ FRANGE lm_1 ∧ n ∉ s) ∧
  DISJOINT3 (FRANGE im_1) (FRANGE lm_1) s
  ⇒
  INJ (FAPPLY lm_1⟨i ↦ next_1⟩) (i INSERT FDOM lm_1) 𝕌(:num) ∧
  (∀n. next_1 + 1 ≤ n ⇒ n ∉ FRANGE (lm_1 \\ i)) ∧
  DISJOINT3 (next_1 INSERT FRANGE (lm_1 \\ i)) (FRANGE im_1) s
Proof
  rw []
  \\ ‘FRANGE (lm_1 \\ i) SUBSET FRANGE lm_1’ by fs [FRANGE_DOMSUB_SUBSET]
  >-
   (gvs [INJ_DEF, SF DNF_ss, SF CONJ_ss]
    \\ gvs [FAPPLY_FUPDATE_THM, CaseEq"bool", SF DNF_ss]
    \\ ntac 3 $ first_x_assum $ qspec_then ‘next_1’ mp_tac
    \\ gvs [FRANGE_DEF] \\ rw []
    \\ metis_tac [])
  >-
   (first_x_assum $ qspec_then ‘n’ mp_tac \\ fs []
    \\ simp [] \\ rpt strip_tac
    \\ gvs [SUBSET_DEF])
  \\ fs [DISJOINT3_def]
  \\ once_rewrite_tac [DISJOINT_SYM]
  \\ conj_tac
  \\ irule DISJOINT_SUBSET
  \\ pop_assum $ irule_at Any \\ fs []
  \\ once_rewrite_tac [DISJOINT_SYM] \\ fs []
QED

Theorem DISJOINT3_COMM_12:
  DISJOINT3 x y z ⇔ DISJOINT3 y x z
Proof
  rw [DISJOINT3_def] \\ metis_tac [IN_DISJOINT]
QED

Theorem aig_rename_aux_thm:
  ∀ts next_1 im_1 lm_1 nm_1 ts_1 next_2 im_2 lm_2.
    aig_rename_aux ts next_1 im_1 lm_1 nm_1 [] = (ts_1,next_2,im_2,lm_2) ∧
    (∀n. ALOOKUP ands n ≠ NONE ⇒
         ∃t. FLOOKUP nm_1 n = SOME t ∧
             ∀ix lx.
               INJ (FAPPLY (im_1 ⊌ ix)) (FDOM (im_1 ⊌ ix)) UNIV ∧
               INJ (FAPPLY (lm_1 ⊌ lx)) (FDOM (lm_1 ⊌ lx)) UNIV
               ⇒
               eval_circuit (is,ls) ands n =
               eval_circuit (aig_read is (im_1 ⊌ ix),aig_read ls (lm_1 ⊌ lx)) res_1 t) ∧
    FDOM nm_1 = set (MAP FST ands) ∧
    INJ (FAPPLY lm_1) (FDOM lm_1) UNIV ∧
    INJ (FAPPLY im_1) (FDOM im_1) UNIV ∧
    FRANGE nm_1 SUBSET set (MAP FST res_1) ∧
    (∀n. next_1 ≤ n ⇒ n ∉ FRANGE im_1 ∧ n ∉ FRANGE lm_1 ∧ ~MEM n (MAP FST res_1)) ∧
    DISJOINT3 (FRANGE im_1) (FRANGE lm_1) (set (MAP FST res_1))
    ⇒
    im_1 SUBMAP im_2 ∧
    lm_1 SUBMAP lm_2 ∧
    INJ (FAPPLY lm_2) (FDOM lm_2) UNIV ∧
    INJ (FAPPLY im_2) (FDOM im_2) UNIV ∧
    (∀l b. MEM (Base (Latch l),b) ts ⇒ l ∈ FDOM lm_2) ∧
    (∀i b. MEM (Base (Input i),b) ts ⇒ i ∈ FDOM im_2) ∧
    (∀l b. MEM (Base (Latch l),b) ts_1 ⇒ l ∈ FRANGE lm_2) ∧
    (∀i b. MEM (Base (Input i),b) ts_1 ⇒ i ∈ FRANGE im_2) ∧
    (∀m b. MEM (Name m,b) ts_1 ⇒ m ∈ FRANGE nm_1) ∧
    next_1 ≤ next_2 ∧
    DISJOINT3 (FRANGE im_2) (FRANGE lm_2) (set (MAP FST res_1)) ∧
    (∀n. next_2 ≤ n ⇒ n ∉ FRANGE im_2 ∧ n ∉ FRANGE lm_2 ∧ ~MEM n (MAP FST res_1)) ∧
    ∀ix lx.
      INJ (FAPPLY (im_2 ⊌ ix)) (FDOM (im_2 ⊌ ix)) UNIV ∧
      INJ (FAPPLY (lm_2 ⊌ lx)) (FDOM (lm_2 ⊌ lx)) UNIV
      ⇒
      EVERY (eval_lit (is,ls) ands) ts =
      EVERY (eval_lit (aig_read is (im_2 ⊌ ix),aig_read ls (lm_2 ⊌ lx)) res_1) ts_1
Proof
  Induct >- fs [aig_rename_aux_def]
  \\ pop_assum $ mk_asm "hyp"
  \\ PairCases \\ fs [aig_rename_aux_def]
  \\ Cases_on ‘∃a. h0 = Name a’ \\ gvs []
  >-
   (rpt gen_tac
    \\ Cases_on ‘FLOOKUP nm_1 a’ \\ fs []
    \\ simp [Once aig_rename_aux_acc]
    \\ pairarg_tac \\ fs []
    \\ strip_tac \\ gvs []
    >-
     (asm_x "hyp" drule
      \\ impl_tac >- fs []
      \\ strip_tac \\ fs [SF SFY_ss]
      \\ fs [eval_circuit_def]
      \\ pop_assum $ assume_tac o GSYM \\ fs []
      \\ qsuff_tac ‘eval_circuit (is,ls) ands a = F’
      >- simp [AC CONJ_ASSOC CONJ_COMM]
      \\ fs [] \\ irule not_eval_circuit
      \\ gvs [FLOOKUP_DEF,EXTENSION])
    \\ asm_x "hyp" drule
    \\ impl_tac >- fs []
    \\ strip_tac \\ fs [SF SFY_ss]
    \\ simp [SF DNF_ss, SF SFY_ss]
    \\ conj_tac
    >-
     (gvs [FLOOKUP_DEF,FRANGE_DEF]
      \\ last_x_assum $ irule_at Any \\ fs [])
    \\ simp [eval_circuit_def]
    \\ pop_assum $ assume_tac o GSYM \\ fs []
    \\ rpt gen_tac
    \\ last_x_assum $ qspec_then ‘a’ mp_tac
    \\ simp []
    \\ impl_tac >- fs [ALOOKUP_NONE, EXTENSION, FLOOKUP_DEF]
    \\ disch_then $ qspecl_then [‘FUNION im_2 ix’,‘FUNION lm_2 lx’] mp_tac
    \\ imp_res_tac FUNION_SUBMAP_lemma
    \\ asm_rewrite_tac [FUNION_ASSOC, FDOM_FUNION, UNION_ASSOC]
    \\ simp [AC CONJ_COMM CONJ_ASSOC])
  \\ Cases_on ‘∃i. h0 = Base (Input i)’ \\ gvs []
  >-
   (rpt gen_tac
    \\ reverse $ Cases_on ‘FLOOKUP im_1 i’ \\ fs []
    \\ simp [Once aig_rename_aux_acc]
    \\ pairarg_tac \\ fs []
    \\ strip_tac \\ gvs []
    >-
     (asm_x "hyp" drule
      \\ impl_tac >- fs []
      \\ strip_tac \\ fs [SF SFY_ss]
      \\ fs [eval_circuit_def]
      \\ simp [SF DNF_ss, SF SFY_ss]
      \\ rewrite_tac [CONJ_ASSOC]
      \\ conj_tac
      >-
       (gvs [FRANGE_DEF, FLOOKUP_DEF, SUBMAP_DEF]
        \\ irule_at Any EQ_REFL \\ res_tac \\ fs [])
      \\ rpt strip_tac
      \\ first_x_assum drule_all
      \\ disch_then $ assume_tac o GSYM \\ fs []
      \\ ‘FLOOKUP im_2 i = SOME x’ by gvs [TO_FLOOKUP]
      \\ drule_all aig_read_thm
      \\ fs [AC CONJ_COMM CONJ_ASSOC])
    \\ asm_x "hyp" drule
    \\ impl_tac
    >-
     (‘im_1 SUBMAP im_1⟨i ↦ next_1⟩’ by fs [TO_FLOOKUP]
      \\ imp_res_tac FUNION_SUBMAP_lemma
      \\ conj_tac
      >-
       (rpt strip_tac
        \\ first_x_assum drule \\ strip_tac \\ simp []
        \\ rpt gen_tac
        \\ first_x_assum $ qspecl_then [‘FUNION (im_1⟨i ↦ next_1⟩) ix’,‘lx’] mp_tac
        \\ asm_rewrite_tac [FUNION_ASSOC]
        \\ rpt strip_tac
        \\ first_x_assum irule \\ simp []
        \\ pop_assum kall_tac
        \\ pop_assum mp_tac
        \\ match_mp_tac EQ_IMPLIES
        \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
        \\ rw [EXTENSION] \\ eq_tac \\ rw [] \\ rw [])
      \\ asm_rewrite_tac []
      \\ simp [SF DNF_ss]
      \\ last_x_assum mp_tac
      \\ simp [FLOOKUP_DEF, FAPPLY_FUPDATE_THM]
      \\ strip_tac
      \\ qpat_x_assum ‘∀x. ALOOKUP _ _ ≠ _ ⇒ _’ kall_tac
      \\ irule IMP_DISJOINT3
      \\ fs []
      \\ simp [Once DISJOINT3_COMM_12])
    \\ strip_tac \\ fs [SF SFY_ss]
    \\ simp [SF DNF_ss, SF SFY_ss]
    \\ rewrite_tac [CONJ_ASSOC]
    \\ conj_tac
    >-
     (fs [TO_FLOOKUP, FLOOKUP_SIMP, AllCaseEqs(), SF DNF_ss]
      \\ qexists ‘i’ \\ fs [] \\ rw [] \\ res_tac
      \\ Cases_on ‘i = k’ \\ gvs [])
    \\ rpt strip_tac
    \\ first_x_assum drule_all
    \\ disch_then $ assume_tac o GSYM
    \\ simp [eval_circuit_def]
    \\ ‘FLOOKUP im_2 i = SOME next_1’ by fs [TO_FLOOKUP, FLOOKUP_SIMP]
    \\ drule_all aig_read_thm
    \\ simp [AC CONJ_COMM CONJ_ASSOC])
  \\ Cases_on ‘∃l. h0 = Base (Latch l)’ \\ gvs []
  >-
   (rpt gen_tac
    \\ reverse $ Cases_on ‘FLOOKUP lm_1 l’ \\ fs []
    \\ simp [Once aig_rename_aux_acc]
    \\ pairarg_tac \\ fs []
    \\ strip_tac \\ gvs []
    >-
     (asm_x "hyp" drule
      \\ impl_tac >- fs []
      \\ strip_tac \\ fs [SF SFY_ss]
      \\ fs [eval_circuit_def]
      \\ simp [SF DNF_ss, SF SFY_ss]
      \\ rewrite_tac [CONJ_ASSOC]
      \\ conj_tac
      >-
       (gvs [FRANGE_DEF, FLOOKUP_DEF, SUBMAP_DEF]
        \\ irule_at Any EQ_REFL \\ res_tac \\ fs [])
      \\ rpt strip_tac
      \\ first_x_assum drule_all
      \\ disch_then $ assume_tac o GSYM \\ fs []
      \\ ‘FLOOKUP lm_2 l = SOME x’ by gvs [TO_FLOOKUP]
      \\ drule_all aig_read_thm
      \\ fs [AC CONJ_COMM CONJ_ASSOC])
    \\ asm_x "hyp" drule
    \\ impl_tac
    >-
     (‘lm_1 SUBMAP lm_1⟨l ↦ next_1⟩’ by fs [TO_FLOOKUP]
      \\ imp_res_tac FUNION_SUBMAP_lemma
      \\ conj_tac
      >-
       (rpt strip_tac
        \\ first_x_assum drule \\ strip_tac \\ simp []
        \\ rpt gen_tac
        \\ first_x_assum $ qspecl_then [‘ix’,‘FUNION (lm_1⟨l ↦ next_1⟩) lx’] mp_tac
        \\ asm_rewrite_tac [FUNION_ASSOC]
        \\ rpt strip_tac
        \\ first_x_assum irule \\ simp []
        \\ pop_assum mp_tac
        \\ match_mp_tac EQ_IMPLIES
        \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
        \\ rw [EXTENSION] \\ eq_tac \\ rw [] \\ rw [])
      \\ asm_rewrite_tac []
      \\ simp [SF DNF_ss]
      \\ last_x_assum mp_tac
      \\ simp [FLOOKUP_DEF, FAPPLY_FUPDATE_THM]
      \\ strip_tac
      \\ qpat_x_assum ‘∀x. ALOOKUP _ _ ≠ _ ⇒ _’ kall_tac
      \\ once_rewrite_tac [DISJOINT3_COMM_12]
      \\ irule IMP_DISJOINT3
      \\ fs [])
    \\ strip_tac \\ fs [SF SFY_ss]
    \\ simp [SF DNF_ss, SF SFY_ss]
    \\ rewrite_tac [CONJ_ASSOC]
    \\ conj_tac
    >-
     (fs [TO_FLOOKUP, FLOOKUP_SIMP, AllCaseEqs(), SF DNF_ss]
      \\ qexists ‘l’ \\ fs [] \\ rw [] \\ res_tac
      \\ Cases_on ‘l = k’ \\ gvs [])
    \\ rpt strip_tac
    \\ first_x_assum drule_all
    \\ disch_then $ assume_tac o GSYM
    \\ simp [eval_circuit_def]
    \\ ‘FLOOKUP lm_2 l = SOME next_1’ by fs [TO_FLOOKUP, FLOOKUP_SIMP]
    \\ drule_all aig_read_thm
    \\ simp [AC CONJ_COMM CONJ_ASSOC])
  \\ ‘h0 = Base Ff’ by (Cases_on ‘h0’ \\ fs [] \\ Cases_on ‘b’ \\ gvs [])
  \\ simp []
  \\ rpt gen_tac
  \\ simp [Once aig_rename_aux_acc]
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ gvs []
  \\ asm_x "hyp" drule
  \\ impl_tac >- fs []
  \\ strip_tac \\ fs [SF SFY_ss]
  \\ fs [eval_circuit_def]
  \\ pop_assum $ assume_tac o GSYM
  \\ simp [AC CONJ_COMM CONJ_ASSOC]
QED

Definition closed_def:
  closed ([] :('a,'i,'l) and list) = T ∧
  closed ((n,ts)::rest) =
    (closed rest ∧
     ∀m b. MEM (Name m, b) ts ⇒ ALOOKUP rest m ≠ NONE)
End

Theorem aig_rename_thm:
  ∀(ands:('a,'i,'l) and list) res next im lm nm.
    aig_rename ands = (res,next,im,lm,nm) ⇒
    (∀l. has_var (Latch l) ands ⇒ l ∈ FDOM lm) ∧
    (∀i. has_var (Input i) ands ⇒ i ∈ FDOM im) ∧
    (∀l. has_var (Latch l) res ⇒ l ∈ FRANGE lm) ∧
    (∀i. has_var (Input i) res ⇒ i ∈ FRANGE im) ∧
    INJ ($' lm) (FDOM lm) UNIV ∧
    INJ ($' im) (FDOM im) UNIV ∧
    ALL_DISTINCT (MAP FST res) ∧
    FDOM nm = set (MAP FST ands) ∧
    FRANGE nm SUBSET set (MAP FST res) ∧
    DISJOINT3 (FRANGE im) (FRANGE lm) (set (MAP FST res)) ∧ closed res ∧
    (∀n. next ≤ n ⇒ n ∉ FRANGE im ∪ FRANGE lm ∪ set (MAP FST res)) ∧
    ∀n. ALOOKUP ands n ≠ NONE ⇒
        ∃t. FLOOKUP nm n = SOME t ∧
            ∀ix lx.
              INJ (FAPPLY (im ⊌ ix)) (FDOM (im ⊌ ix)) UNIV ∧
              INJ (FAPPLY (lm ⊌ lx)) (FDOM (lm ⊌ lx)) UNIV
              ⇒
              eval_circuit (is,ls) ands n =
              eval_circuit (aig_read is (FUNION im ix),
                            aig_read ls (FUNION lm lx)) res (t:num)
Proof
  Induct
  >- fs [aig_rename_def, closed_def, DISJOINT3_def, has_var_def]
  \\ PairCases
  \\ fs [aig_rename_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ gvs [closed_def]
  \\ rename [‘aig_rename ands = (res_1,next_1,im_1,lm_1,nm_1)’]
  \\ rename [‘aig_rename_aux ts next_1 im_1 lm_1 nm_1 [] = (ts_1,next_2,im_2,lm_2)’]
  \\ fs [has_var_def, SF DNF_ss, GSYM CONJ_ASSOC]
  \\ drule aig_rename_aux_thm
  \\ disch_then $ qspecl_then [‘res_1’,‘ls’,‘is’,‘ands’] mp_tac
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ asm_rewrite_tac []
  \\ conj_tac >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  \\ conj_tac >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  \\ conj_tac >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  \\ conj_tac >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  \\ conj_tac >- (strip_tac \\ res_tac \\ fs [])
  \\ conj_tac
  >-
   (irule SUBSET_TRANS
    \\ irule_at Any FRANGE_DOMSUB_SUBSET
    \\ gvs [SUBSET_DEF])
  \\ conj_tac
  >-
   (gvs [DISJOINT3_def] \\ gvs [IN_DISJOINT]
    \\ fs [FRANGE_DEF]
    \\ metis_tac [DOMSUB_FAPPLY_NEQ])
  \\ conj_tac >- (rw [ALOOKUP_NONE] \\ fs [SUBSET_DEF] \\ res_tac \\ fs [])
  \\ conj_tac >- (rw [] \\ res_tac \\ fs [])
  \\ conj_tac >- rw []
  \\ conj_tac >- rw []
  \\ gen_tac
  \\ Cases_on ‘n = h0’ \\ gvs [FLOOKUP_SIMP]
  >- (gvs [eval_circuit_def] \\ fs [SF ETA_ss])
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac \\ fs [eval_circuit_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC
  >- (rw [] \\ res_tac \\ fs [FRANGE_DEF,FLOOKUP_DEF,SUBSET_DEF] \\ metis_tac [])
  \\ first_x_assum $ qspecl_then [‘FUNION im_2 ix’,‘FUNION lm_2 lx’] mp_tac
  \\ imp_res_tac FUNION_SUBMAP_lemma
  \\ rewrite_tac [FUNION_ASSOC,FDOM_FUNION,UNION_ASSOC]
  \\ asm_rewrite_tac [FUNION_ASSOC]
QED

Theorem eval_circuit'_swap:
  (∀i. has_var (Input i) res ⇒ is i = is1 i) ⇒
  (∀l. has_var (Latch l) res ⇒ ls l = ls1 l) ⇒
  (eval_circuit' (is,ls) res ⇔ eval_circuit' (is1,ls1) res)
Proof
  Cases_on ‘res’ \\ fs [eval_circuit'_def]
  \\ PairCases_on ‘h’ \\ fs [eval_circuit'_def]
  \\ qspec_tac (‘(h0,h1)::t’,‘xs’)
  \\ qspec_tac (‘h0’,‘h’)
  \\ Induct_on ‘xs’
  \\ fs [eval_circuit_def, FORALL_PROD]
  \\ reverse $ rw []
  >- (last_x_assum irule \\ gvs [has_var_def])
  \\ simp [SF ETA_ss]
  \\ irule EVERY_EQ_EVERY
  \\ rw [EVERY_MEM]
  \\ gvs [has_var_def, SF DNF_ss]
  \\ Cases_on ‘x’ \\ gvs [eval_circuit_def]
  \\ Cases_on ‘q’ \\ gvs [eval_circuit_def]
  \\ Cases_on ‘b’ \\ gvs [eval_bvar_def]
  \\ res_tac \\ gvs []
QED

Theorem eval_circuit'_aig_rename:
  (∃is ls. eval_circuit' (is,ls) (FST (aig_rename ands))) ⇔
  (∃is ls. eval_circuit' (is,ls) ands)
Proof
  ‘∃r. aig_rename ands = r’ by simp []
  \\ PairCases_on ‘r’ \\ gvs []
  \\ rename [‘_ = (res,next,im,lm,nm)’]
  \\ drule aig_rename_thm \\ strip_tac
  \\ Cases_on ‘ands’ \\ fs []
  >- gvs [aig_rename_def, eval_circuit'_def]
  \\ PairCases_on ‘h’ \\ fs []
  \\ reverse eq_tac \\ rw []
  >-
   (first_x_assum $ qspecl_then [‘ls’,‘is’] strip_assume_tac
    \\ first_x_assum $ qspec_then ‘h0’ mp_tac
    \\ strip_tac \\ fs []
    \\ first_x_assum $ qspecl_then [‘FEMPTY’,‘FEMPTY’] assume_tac
    \\ gvs [eval_circuit'_def]
    \\ fs [aig_rename_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ fs [eval_circuit'_def, FLOOKUP_SIMP]
    \\ last_x_assum $ irule_at Any)
  \\ first_x_assum $ qspecl_then [‘λt. ls (lm ' t)’, ‘λt. is (im ' t)’] strip_assume_tac
  \\ first_x_assum $ qspec_then ‘h0’ $ mp_tac o GSYM
  \\ strip_tac \\ fs []
  \\ first_x_assum $ qspecl_then [‘FEMPTY’,‘FEMPTY’] assume_tac
  \\ gvs []
  \\ simp [eval_circuit'_def]
  \\ drule EQ_IMPLIES
  \\ disch_then $ irule_at Any
  \\ qabbrev_tac ‘is1 = aig_read (λt. is im⟨t⟩) im’
  \\ qabbrev_tac ‘ls1 = aig_read (λt. ls lm⟨t⟩) lm’
  \\ qsuff_tac ‘eval_circuit' (is,ls) res = eval_circuit' (is1,ls1) res’
  >-
   (fs [aig_rename_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [eval_circuit'_def, FLOOKUP_SIMP])
  \\ irule eval_circuit'_swap
  \\ rw [] \\ first_x_assum drule
  \\ unabbrev_all_tac
  \\ fs [aig_read_def]
  \\ simp [FLOOKUP_DEF]
  \\ rw [IN_FRANGE]
  \\ fs [INJ_DEF]
  \\ metis_tac []
QED

(*----------------------------------------------------------------------*
   lowering to CNF
 *----------------------------------------------------------------------*)

Definition negate_def:
  negate (Pos n) = Neg n ∧
  negate (Neg n) = Pos n
End

Definition imp_to_cnf_def:
  imp_to_cnf xs y = y :: MAP negate xs
End

Definition eq_every_to_cnf_def:
  eq_every_to_cnf x xs = (x::MAP negate xs)::MAP (λy. [y; negate x]) xs
End

Theorem eq_every_to_cnf_eq:
  eq_every_to_cnf x xs =
    imp_to_cnf xs x :: MAP (λy. imp_to_cnf [x] y) xs
Proof
  simp [imp_to_cnf_def, eq_every_to_cnf_def]
QED

Theorem satisfies_cnf_INSERT:
  satisfies_cnf w (x INSERT s) ⇔
  satisfies_clause w x ∧ satisfies_cnf w s
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, SF DNF_ss]
QED

Theorem satisfies_cnf_set:
  satisfies_cnf w (set xs) = EVERY (satisfies_clause w) xs
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, EVERY_MEM]
QED

Theorem satisfies_lit_negate:
  satisfies_lit w (negate y) = ~ satisfies_lit w y
Proof
  Cases_on ‘y’ \\ gvs [negate_def, satisfies_lit_def]
QED

Theorem satisfies_clause_imp_to_cnf:
  satisfies_clause w (imp_to_cnf xs y) ⇔
  (EVERY (satisfies_lit w) xs ⇒ satisfies_lit w y)
Proof
  fs [satisfies_clause_def, imp_to_cnf_def]
  \\ gvs [MEM_MAP,PULL_EXISTS, SF DNF_ss, satisfies_lit_negate]
  \\ Cases_on ‘satisfies_lit w y’ \\ simp []
  \\ fs [EXISTS_MEM]
QED

Theorem eq_every_to_cnf_thm:
  satisfies_cnf w (set (eq_every_to_cnf x xs)) =
  (satisfies_lit w x = EVERY (satisfies_lit w) xs)
Proof
  simp [eq_every_to_cnf_eq]
  \\ once_rewrite_tac [satisfies_cnf_INSERT]
  \\ simp [satisfies_cnf_set, EVERY_MAP]
  \\ simp [satisfies_clause_imp_to_cnf]
  \\ Cases_on ‘satisfies_lit w x’ \\ fs [SF ETA_ss]
QED

Definition not_TT_def:
  not_TT (Base Ff, T) = F ∧
  not_TT _ = T
End

Definition var_to_name_def:
  var_to_name (Name n) = n:num ∧
  var_to_name (Base (Input i)) = i ∧
  var_to_name (Base (Latch l)) = l ∧
  var_to_name _ = 0
End

Definition var_to_lit_def:
  var_to_lit (v,F) = Pos (var_to_name v) ∧
  var_to_lit (v,T) = Neg (var_to_name v)
End

Definition and_to_cnf_def:
  and_to_cnf n (ys : (num, num, num) aig$lit list) =
    if MEM (Base Ff, F) ys then
      [[Neg (n:num)]]
    else
      eq_every_to_cnf (Pos (n:num))
        (MAP var_to_lit (FILTER not_TT ys))
End

Definition to_cnf_def:
  to_cnf ([] : (num,num,num) and list) acc = (acc : num lit list list) ∧
  to_cnf ((n,ys)::xs) acc = to_cnf xs (and_to_cnf n ys ++ acc)
End

Definition direct_circuit_to_cnf_def:
  direct_circuit_to_cnf (ands : (num,num,num) and list) =
    case ands of
    | [] => [[]]
    | ((name,_)::_) => ([Pos name] :: to_cnf ands []) : num lit list list
End

Definition eval_circuits_def:
  (eval_circuits (is,ls) [] w ⇔ T) ∧
  (eval_circuits (is,ls) ((k,ts)::rest) w ⇔
     (w k = eval_circuit (is,ls) ((k,ts)::rest) k) ∧
     eval_circuits (is,ls) rest w)
End

Theorem to_cnf_acc:
  ∀ands acc. set (to_cnf ands acc) = set (to_cnf ands []) ∪ set acc
Proof
  Induct
  >- (once_rewrite_tac [to_cnf_def] \\ simp [])
  \\ PairCases
  \\ once_rewrite_tac [to_cnf_def]
  \\ pop_assum $ once_rewrite_tac o single
  \\ fs [AC UNION_ASSOC UNION_COMM]
QED

Theorem satisfies_cnf_UNION_IMP:
  satisfies_cnf w (x ∪ y) ⇒
  satisfies_cnf w x ∧ satisfies_cnf w y
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def]
QED

Theorem IMP_satisfies_cnf_UNION:
  satisfies_cnf w x ∧ satisfies_cnf w y ⇒
  satisfies_cnf w (x ∪ y)
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, SF DNF_ss]
QED

Theorem to_filter:
  ∀xs.
    EVERY (eval_lit (is,ls) ands) xs =
    EVERY (eval_lit (is,ls) ands) (FILTER not_TT xs)
Proof
  Induct \\ rw []
  \\ Cases_on ‘h’ \\ fs [not_TT_def]
  \\ Cases_on ‘q’ \\ fs [not_TT_def]
  \\ Cases_on ‘b’ \\ fs [not_TT_def]
  \\ Cases_on ‘r’ \\ fs [not_TT_def]
  \\ simp [eval_circuit_def]
QED

Theorem eval_circuits_ALOOKUP:
  ∀ands a.
    eval_circuits (w,w) ands w ∧
    ALOOKUP ands a ≠ NONE ⇒
    (w a ⇔ eval_circuit (w,w) ands a)
Proof
  Induct \\ simp [ALOOKUP_def]
  \\ PairCases \\ simp [ALOOKUP_def] \\ rw []
  \\ Cases_on ‘h0 = a’ \\ gvs [eval_circuits_def]
  \\ gvs [eval_circuit_def]
QED

Theorem satisfies_cnf_IMP:
  ∀ands w.
    satisfies_cnf w (set (to_cnf ands [])) ∧ closed ands ⇒
    eval_circuits (w, w) ands w
Proof
  Induct
  \\ simp [eval_circuits_def]
  \\ PairCases \\ fs [closed_def]
  \\ simp [eval_circuits_def, to_cnf_def]
  \\ simp [Once to_cnf_acc]
  \\ rpt gen_tac
  \\ strip_tac
  \\ simp [eval_circuit_def]
  \\ dxrule satisfies_cnf_UNION_IMP \\ strip_tac
  \\ last_x_assum drule_all \\ strip_tac
  \\ simp []
  \\ fs [and_to_cnf_def]
  \\ Cases_on ‘MEM FF h1’ \\ fs []
  >-
   (gvs [satisfies_cnf_def, satisfies_fml_gen_def,
         satisfies_clause_def, satisfies_lit_def, EXISTS_MEM]
    \\ first_x_assum $ irule_at Any
    \\ gvs [eval_circuit_def])
  \\ fs [eq_every_to_cnf_thm, satisfies_lit_def, SF ETA_ss]
  \\ simp [Once to_filter]
  \\ simp [EVERY_MAP]
  \\ irule EVERY_EQ_EVERY
  \\ simp [EVERY_MEM, MEM_FILTER] \\ rw []
  \\ rename [‘not_TT z’]
  \\ PairCases_on ‘z’ \\ fs []
  \\ Cases_on ‘z1’ \\ fs []
  \\ Cases_on ‘z0’ \\ fs []
  \\ TRY (rename [‘Base b’] \\ Cases_on ‘b’ \\ fs [])
  \\ gvs [var_to_lit_def, satisfies_lit_def, var_to_name_def, not_TT_def]
  \\ gvs [eval_circuit_def, eval_bvar_def]
  \\ last_x_assum drule
  \\ strip_tac
  \\ drule_all eval_circuits_ALOOKUP
  \\ rewrite_tac []
QED

Definition find_suffix_def:
  find_suffix n [] = NONE ∧
  find_suffix n ((k,xs)::rest) =
    if k = n then SOME ((k,xs)::rest) else find_suffix n rest
End

Definition cnf_witness_def:
  cnf_witness i_dom l_dom is ls ands n =
    if n ∈ i_dom then is n else
    if n ∈ l_dom then ls n else
      case find_suffix n ands of
      | NONE => F
      | SOME rest => eval_circuit (is,ls) rest n
End

Theorem find_suffix_fast_forward:
  ∀past.
    ALL_DISTINCT (MAP FST past ++ h0::rest) ⇒
    find_suffix h0 (past ++ (h0,h1)::ands) = SOME ((h0,h1)::ands)
Proof
  Induct \\ fs [find_suffix_def, FORALL_PROD]
QED

Theorem eval_circuit_drop:
  ∀l1 a.
    ~ MEM a (MAP FST l1) ⇒
    eval_circuit (is,ls) (l1 ++ l2) a =
    eval_circuit (is,ls) l2 a
Proof
  Induct \\ fs [eval_circuit_def, FORALL_PROD]
QED

Theorem eval_circuit_IMP_cnf_lemma:
  ∀ands past.
    closed ands ∧ DISJOINT3 i_dom l_dom (set (MAP FST ands)) ∧
    (∀l. has_var (Latch l) ands ⇒ l ∈ l_dom) ∧
    (∀i. has_var (Input i) ands ⇒ i ∈ i_dom) ∧
    ALL_DISTINCT (MAP FST (past ++ ands)) ⇒
    satisfies_cnf (cnf_witness i_dom l_dom is ls (past ++ ands)) (set (to_cnf ands []))
Proof
  Induct \\ simp [Once to_cnf_def]
  >- simp [satisfies_cnf_def, satisfies_fml_gen_def]
  \\ PairCases \\ fs [closed_def]
  \\ strip_tac
  \\ simp [Once to_cnf_def]
  \\ simp [Once to_cnf_acc]
  \\ rpt strip_tac
  \\ irule IMP_satisfies_cnf_UNION
  \\ conj_tac
  >- (last_x_assum $ qspec_then ‘past ++ [(h0,h1)]’ mp_tac
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP]
      \\ disch_then irule
      \\ fs [has_var_def, SF DNF_ss]
      \\ fs [DISJOINT3_def,IN_DISJOINT])
  \\ fs [and_to_cnf_def] \\ rw []
  >-
   (gvs [satisfies_cnf_def, satisfies_fml_gen_def,
         satisfies_clause_def, satisfies_lit_def, EXISTS_MEM]
    \\ fs [cnf_witness_def]
    \\ drule find_suffix_fast_forward \\ fs [] \\ rw []
    >- fs [DISJOINT3_def,IN_DISJOINT]
    >- fs [DISJOINT3_def,IN_DISJOINT]
    \\ fs [eval_circuit_def]
    \\ simp [EXISTS_MEM]
    \\ first_x_assum $ irule_at Any
    \\ fs [eval_circuit_def])
  \\ fs [eq_every_to_cnf_thm, satisfies_lit_def, SF ETA_ss]
  \\ fs [cnf_witness_def]
  \\ drule find_suffix_fast_forward \\ fs [] \\ strip_tac
  \\ simp [eval_circuit_def, SF ETA_ss]
  \\ simp [Once to_filter]
  \\ simp [EVERY_MAP]
  \\ fs [has_var_def, SF DNF_ss] \\ rw []
  >- fs [DISJOINT3_def,IN_DISJOINT]
  >- fs [DISJOINT3_def,IN_DISJOINT]
  \\ irule EVERY_EQ_EVERY
  \\ simp [EVERY_MEM, MEM_FILTER] \\ rw []
  \\ rename [‘not_TT z’]
  \\ PairCases_on ‘z’ \\ fs []
  \\ reverse $ Cases_on ‘z0’ \\ fs []
  >-
   (rename [‘Base b’] \\ Cases_on ‘b’ \\ fs []
    \\ Cases_on ‘z1’ \\ fs [not_TT_def]
    \\ simp [var_to_lit_def, var_to_name_def, eval_circuit_def,
             satisfies_lit_def, cnf_witness_def]
    \\ res_tac \\ fs [] \\ rw []
    \\ fs [DISJOINT3_def,IN_DISJOINT] \\ metis_tac [])
  \\ Cases_on ‘z1’
  \\ gvs [var_to_lit_def, satisfies_lit_def, var_to_name_def]
  \\ gvs [eval_circuit_def, eval_bvar_def, cnf_witness_def]
  \\ res_tac
  \\ Cases_on ‘ALOOKUP ands a’ \\ fs []
  \\ dxrule ALOOKUP_MEM
  \\ strip_tac \\ (rw []
  >- (fs [DISJOINT3_def,IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
      \\ metis_tac [])
  >- (fs [DISJOINT3_def,IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
      \\ metis_tac []))
  \\ qpat_x_assum ‘MEM (a,x) ands’ mp_tac
  \\ simp [MEM_SPLIT]
  \\ strip_tac \\ gvs []
  \\ ‘ALL_DISTINCT (MAP FST (past ++ (h0,h1)::l1) ++ a :: MAP FST l2)’ by
    full_simp_tac std_ss [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]
  \\ drule find_suffix_fast_forward
  \\ simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ rw []
  \\ irule eval_circuit_drop
  \\ fs [ALL_DISTINCT_APPEND]
  \\ metis_tac []
QED

Theorem eval_circuit_IMP_cnf:
  closed ands ∧ ALL_DISTINCT (MAP FST ands) ∧
  (∀l. has_var (Latch l) ands ⇒ l ∈ l_dom) ∧
  (∀i. has_var (Input i) ands ⇒ i ∈ i_dom) ∧
  DISJOINT3 i_dom l_dom (set (MAP FST ands)) ⇒
  satisfies_cnf (cnf_witness i_dom l_dom is ls ands) (set (to_cnf ands []))
Proof
  qspecl_then [‘ands’,‘[]’] mp_tac eval_circuit_IMP_cnf_lemma \\ fs []
QED

Theorem direct_circuit_to_cnf_correct:
  ALL_DISTINCT (MAP FST ands) ∧ closed ands ∧
  (∀l. has_var (Latch l) ands ⇒ l ∈ l_dom) ∧
  (∀i. has_var (Input i) ands ⇒ i ∈ i_dom) ∧
  DISJOINT3 i_dom l_dom (set (MAP FST ands)) ⇒
  (satisfiable_cnf (set (direct_circuit_to_cnf ands)) =
   ∃is ls. eval_circuit' (is,ls) ands)
Proof
  rw [satisfiable_cnf_def] \\ eq_tac \\ strip_tac
  >-
   (qexists ‘w’ \\ qexists ‘w’
    \\ fs [direct_circuit_to_cnf_def]
    \\ pop_assum mp_tac
    \\ Cases_on ‘ands’
    >- (rw [] \\ gvs [eval_circuit'_def]
        \\ fs [satisfies_cnf_def, satisfies_fml_gen_def, satisfies_clause_def])
    \\ PairCases_on ‘h’
    \\ simp []
    \\ once_rewrite_tac [satisfies_cnf_INSERT]
    \\ rw [satisfies_clause_def, satisfies_lit_def]
    \\ drule_all satisfies_cnf_IMP
    \\ gvs [eval_circuits_def,eval_circuit'_def]
    \\ gvs [eval_circuit_def])
  \\ qexists ‘cnf_witness i_dom l_dom is ls ands’
  \\ simp [direct_circuit_to_cnf_def]
  \\ Cases_on ‘ands’ >- gvs [eval_circuit'_def]
  \\ PairCases_on ‘h’ \\ fs []
  \\ once_rewrite_tac [satisfies_cnf_INSERT]
  \\ conj_tac
  >-
   (simp [satisfies_clause_def, satisfies_lit_def]
    \\ simp [cnf_witness_def]
    \\ fs [find_suffix_def, eval_circuit'_def]
    \\ rw [] \\ fs [DISJOINT3_def,IN_DISJOINT])
  \\ drule eval_circuit_IMP_cnf \\ fs []
QED

(*----------------------------------------------------------------------*
   plugging everything together
 *----------------------------------------------------------------------*)

Definition aig_to_cnf_def:
  aig_to_cnf ands name =
    let ands_1 = prune_for name ands in
    let (ands_2,next,im,lm,nm) = aig_rename ands_1 in
      (direct_circuit_to_cnf ands_2, next)
End

Theorem aig_to_cnf_def_correct:
  aig_to_cnf aig name = (cnf, limit) ⇒
  (satisfiable_cnf (set cnf) = ∃is ls. eval_circuit (is,ls) aig name)
Proof
  simp [aig_to_cnf_def]
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ gvs []
  \\ irule EQ_TRANS
  \\ irule_at Any direct_circuit_to_cnf_correct
  \\ drule aig_rename_thm
  \\ simp [GSYM PULL_FORALL]
  \\ strip_tac
  \\ qexists ‘FRANGE lm’
  \\ qexists ‘FRANGE im’
  \\ fs []
  \\ ‘ands_2 = FST (aig_rename (prune_for name aig))’ by asm_rewrite_tac []
  \\ pop_assum $ rewrite_tac o single
  \\ rewrite_tac [eval_circuit'_aig_rename, eval_circuit_prune_for]
QED
