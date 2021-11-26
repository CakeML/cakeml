(*
  Lemmas about flat_size_of
*)

open preamble dataSemTheory size_ofPropsTheory;

val _ = new_theory "flat_size_ofProps";

Theorem flat_size_of_head_simps[simp]:
  (∀vs lims refs blocks n.
     flat_size_of lims refs blocks (Number n::vs) =
     flat_measure lims (Number n) + flat_size_of lims refs blocks vs)
  ∧ (∀vs lims refs blocks ptr.
     flat_size_of lims refs blocks (CodePtr ptr::vs) =
     flat_measure lims (CodePtr ptr) + flat_size_of lims refs blocks vs)
  ∧ (∀vs lims refs blocks w.
     flat_size_of lims refs blocks (Word64 w::vs) =
     flat_measure lims (Word64 w) + flat_size_of lims refs blocks vs)
Proof
  rw[flat_size_of_def,to_addrs_def,flat_size_of_def]
  \\ Cases_on ‘vs’ \\ rw[flat_measure_def]
QED

Definition ref_to_vs_def:
  ref_to_vs [] = []
∧ ref_to_vs (ValueArray vs::xs) = vs ++ ref_to_vs xs
∧ ref_to_vs (ByteArray _ _::xs) = ref_to_vs xs
End

Definition blocks_to_vs_def:
  blocks_to_vs [] = []
∧ blocks_to_vs (Block _ _ l::xs) = l ++ blocks_to_vs xs
∧ blocks_to_vs (x::xs) = blocks_to_vs xs
End

Theorem FINITE_to_addrs:
  ∀l. FINITE (to_addrs l)
Proof
  Induct \\ rw[to_addrs_def]
  \\ Cases_on ‘h’
  \\ rw[to_addrs_def]
  \\ Cases_on ‘l'’
  \\ rw[to_addrs_def]
QED

Theorem to_addrs_APPEND:
  ∀a b. to_addrs (a ++ b) = to_addrs a ∪ to_addrs b
Proof
  Induct \\ rw[to_addrs_def]
  \\ Cases_on ‘h’ \\ rw[to_addrs_def,UNION_ASSOC]
  \\ Cases_on ‘l’ \\ rw[to_addrs_def,UNION_ASSOC]
QED

Theorem to_addrs_cons:
  ∀a b. to_addrs (a::b) = to_addrs [a] ∪ to_addrs b
Proof
  Induct_on ‘b’ \\ rw[to_addrs_def]
  \\ Cases_on ‘h’ \\ rw[to_addrs_def,UNION_ASSOC]
  \\ Cases_on ‘a’ \\ rw[to_addrs_def,UNION_ASSOC]
  \\ Cases_on ‘l’ \\ rw[to_addrs_def,UNION_ASSOC]
  \\ Cases_on ‘l'’ \\ rw[to_addrs_def,UNION_ASSOC]
QED

(* Note: This might be tricky as it will relay on well-formedness properties
         of references  and blocks which should not have circular pointers/timestamps
 *)
Theorem FINITE_reachable_v:
  ∀refs blocks roots.
    FINITE roots ⇒
    FINITE (reachable_v refs blocks roots)
Proof
  rw[]
  \\ qspec_then ‘to_addrs (blocks_to_vs blocks) ∪
                 to_addrs (ref_to_vs (sptree$toList refs))  ∪
                 roots’
                mp_tac SUBSET_FINITE
  \\ impl_tac >- rw[FINITE_to_addrs]
  \\ disch_then ho_match_mp_tac
  \\ rw [SUBSET_DEF,IN_DEF,reachable_v_def]
  \\ gs[Once RTC_CASES2]
  \\ Cases_on ‘u’
  >- (gs[next_def,block_to_addrs_def]
      \\ Cases_on ‘LLOOKUP blocks n’ \\ gs []
      \\ Cases_on ‘x''’ \\ gs [LLOOKUP_EQ_EL]
      \\ drule EL_MEM
      \\ qpat_x_assum ‘Blocks _ _ _ = _’ (REWRITE_TAC o single o GSYM)
      \\ rw[] \\ DISJ1_TAC \\ DISJ1_TAC
      \\ gs[IN_DEF] \\ pop_assum mp_tac
      \\ qpat_x_assum ‘to_addrs _ _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp[AND_IMP_INTRO]
      \\ induct_on ‘blocks’
      \\ rw[]
      >- (simp[blocks_to_vs_def,to_addrs_APPEND,IN_DEF])
      \\ first_x_assum drule_all \\ rw[]
      \\ Cases_on ‘h’ \\ rw[]
      \\ rw[blocks_to_vs_def,to_addrs_def,to_addrs_APPEND,IN_DEF])
  >-(gs[next_def,ptr_to_addrs_def]
     \\ Cases_on ‘lookup n refs’ \\ gs[]
     \\ Cases_on ‘x''’ \\ gs[]
     \\ ‘MEM (ValueArray l) (toList refs)’ by metis_tac[MEM_toList]
     \\ DISJ1_TAC \\ DISJ2_TAC
     \\ pop_assum mp_tac \\ qpat_x_assum ‘x ∈ _’ mp_tac
     \\ rpt (pop_assum kall_tac)
     \\ qmatch_goalsub_abbrev_tac ‘MEM _ ll’
     \\ pop_assum kall_tac \\ simp[AND_IMP_INTRO]
     \\ induct_on ‘ll’
     \\ rw[]
     >- (simp[ref_to_vs_def,to_addrs_APPEND])
     \\ first_x_assum drule_all \\ rw[]
     \\ Cases_on ‘h’ \\ rw[]
     \\ rw[ref_to_vs_def,to_addrs_def,to_addrs_APPEND,IN_DEF])
QED

Theorem flat_size_of_le_APPEND:
  ∀lims refs blocks a b.
       flat_size_of lims refs blocks b ≤ flat_size_of lims refs blocks (a ++ b)
Proof
  rw[flat_size_of_def]
  \\ qmatch_goalsub_abbrev_tac ‘a1 + a2 ≤ b1 + b2’
  \\ ‘a1 ≤ b1’ by
    (simp[Abbr‘a1’,Abbr‘b1’]
     \\ ntac 2 (pop_assum kall_tac)
     \\ induct_on ‘a’ \\ rw[])
  \\ ‘a2 ≤ b2’ suffices_by simp[]
  \\ UNABBREV_ALL_TAC
  \\ irule SUM_IMAGE_SUBSET_LE
  \\ simp[FINITE_to_addrs,FINITE_reachable_v,SUBSET_DEF,to_addrs_APPEND]
  \\ rw[IN_DEF,reachable_v_def]
  \\ metis_tac[]
QED

(* SOUNDNESS *)

(* First, we need an alternative definition of flat_size_of
   where all_blocks is given as a finite map
*)
Definition block_to_addrs0_def:
  block_to_addrs0 blocks ts =
  (case sptree$lookup ts blocks of
   | SOME (Block _ _ vs) => to_addrs vs
   | _ => ∅ )
End

Definition ptr_to_addrs0_def:
  ptr_to_addrs0 refs p =
    case sptree$lookup p refs of
      SOME (ValueArray vs) => to_addrs vs
      | _ => {}
End

Definition addrs_in_def:
  (addrs_in refs blocks (BlockAddr ts) =
    case lookup ts blocks of
      SOME _ => T
    | _      => F)
∧ (addrs_in refs blocks (RefAddr p) =
    case lookup p refs of
      SOME _ => T
    | _      => F)
End

Definition next0_def:
  (next0 refs blocks (BlockAddr ts) r =
     (r ∈ block_to_addrs0 blocks ts))
∧ (next0 refs blocks (RefAddr ref) r =
     (r ∈ ptr_to_addrs0 refs ref))
End

(* The set of all addresses that can be reached from an initial set of roots *)
Definition reachable_v0_def:
  reachable_v0 refs blocks roots = { y | ∃x. x ∈ roots ∧ (next0 refs blocks)^* x y}
End

Definition size_of_addr0_def:
  (size_of_addr0 lims refs blocks (BlockAddr ts) =
   (case sptree$lookup ts blocks of
    | SOME (Block _ _ vs) => 1 + LENGTH vs + SUM (MAP (flat_measure lims) vs)
    | _ => 0))
∧ (size_of_addr0 lims refs blocks (RefAddr p) =
   (case sptree$lookup p refs of
    | SOME (ValueArray vs)  => 1 + LENGTH vs + SUM (MAP (flat_measure lims) vs)
    | SOME (ByteArray _ bs) => LENGTH bs DIV (arch_size lims DIV 8) + 2
    | _ => 0))
End

Definition aux_size_of_def:
  aux_size_of lims refs blocks roots =
    SUM (MAP (flat_measure lims) roots) +
    ∑ (size_of_addr0 lims refs blocks)
      (reachable_v0 refs blocks (to_addrs roots))
End

(* If a timestam has been seen then its not in all_blocks; conversely,
   if a timestamp has not been seen and it is present in the roots
   then it must be in all_blocks.
  *)
Definition blocks0_roots_inv_def:
  blocks0_roots_inv blocks seen roots =
   ∀ts tag l.
     (IS_SOME (sptree$lookup ts (seen : num_set)) ⇒ IS_NONE (sptree$lookup ts blocks)) ∧
     (IS_NONE (sptree$lookup ts seen) ∧ MEM (Block ts tag l) roots ⇒
        lookup ts blocks = SOME (Block ts tag l))
End

(* All values in a reference fulfil blocks0_roots_inv *)
Definition blocks0_refs_inv_def:
  blocks0_refs_inv blocks seen refs =
    ∀p vs.
      sptree$lookup p refs = SOME (ValueArray vs) ⇒
      blocks0_roots_inv blocks seen vs
End

(* All values in all_blocks fulfil blocks0_roots_inv
   in a way consistent with the recursion in size_of
 *)
Definition blocks0_all_inv_def:
  blocks0_all_inv blocks seen =
  ∀ts tag l.
    sptree$lookup ts blocks = SOME (Block ts tag l) ⇒
    blocks0_roots_inv (delete ts blocks) (insert ts () seen) l
End

Definition del_ptr_def[simp]:
  del_ptr (RefAddr p) refs = delete p refs
∧ del_ptr  _          refs = refs
End

Definition del_blk_def[simp]:
  del_blk (BlockAddr ts) blocks = delete ts blocks
∧ del_blk  _             blocks = blocks
End

Triviality next0_del:
  ∀refs blocks v x .
       (next0 refs blocks)^* v x
     ⇒ (∃y. (next0 refs blocks) v y ∧
           (next0 (del_ptr v refs) (del_blk v blocks))^* y x) ∨ x = v
Proof
  strip_tac \\ strip_tac
  \\ ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 \\ rw[]
  >~[‘(next0 refs blocks)^* v v’]
  >- (DISJ1_TAC \\ asm_exists_tac \\ simp[])
  >- (Cases_on ‘x = v’ \\ gs[]
      >- (DISJ1_TAC \\ qexists_tac ‘x'’ \\ simp[])
      \\ Cases_on ‘x' = v’ \\ gs[]
      \\ asm_exists_tac \\ simp[]
      \\ Cases_on ‘x = x'’ \\ gs[]
      \\ ‘next0 (del_ptr v refs) (del_blk v blocks) x x'’ by
         (Cases_on ‘x’ \\ Cases_on ‘v’
          \\ gs[next0_def,block_to_addrs0_def]
          \\ gs[lookup_delete,ptr_to_addrs0_def])
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES2)
      \\ DISJ2_TAC \\ metis_tac [])
QED

Triviality next0_subspt:
  ∀refs blocks x y.
    (next0 refs blocks)^* x y ⇒
    ∀refs' blocks'.
      subspt refs refs' ∧
      subspt blocks blocks' ⇒
      (next0 refs' blocks')^* x y
Proof
  strip_tac \\ strip_tac
  \\ ho_match_mp_tac RTC_strongind \\ rw[]
  \\ first_x_assum drule_all \\ rw[]
  \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
  \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
  \\ Cases_on ‘x’
  \\ gs[next0_def,block_to_addrs0_def,ptr_to_addrs0_def]
  \\ gs[subspt_lookup]
  >-(cases_on ‘lookup n blocks’ \\ gs[]
     \\ first_assum drule \\ disch_then (simp o single))
  >-(cases_on ‘lookup n refs’ \\ gs[]
     \\ first_assum drule \\ disch_then (simp o single))
QED

Triviality reachable_v0_del_ptr:
  ∀refs blocks r l.
    lookup r refs = SOME (ValueArray l) ⇒
    reachable_v0 refs blocks {RefAddr r} =
     reachable_v0 (delete r refs) blocks (to_addrs l) ∪ {RefAddr r}
Proof
  rw[reachable_v0_def,FUN_EQ_THM] \\ EQ_TAC \\ rw[] \\ simp[]
  >- (drule next0_del \\ rw[next0_def,ptr_to_addrs0_def])
  >- (drule next0_subspt \\ disch_then (qspecl_then [‘refs’,‘blocks’] mp_tac)
      \\ impl_tac >- gs[subspt_delete]
      \\ rw[]
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
      \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
      \\  simp [next0_def,ptr_to_addrs0_def])
QED

Triviality reachable_v0_del_blk:
  ∀refs blocks ts tag l.
    lookup ts blocks = SOME (Block ts tag l) ⇒
    reachable_v0 refs blocks {BlockAddr ts} =
     reachable_v0 refs (delete ts blocks) (to_addrs l) ∪ {BlockAddr ts}
Proof
  rw[reachable_v0_def,FUN_EQ_THM] \\ EQ_TAC \\ rw[] \\ simp[]
  >- (drule next0_del \\ rw[next0_def,block_to_addrs0_def])
  >- (drule next0_subspt \\ disch_then (qspecl_then [‘refs’,‘blocks’] mp_tac)
      \\ impl_tac >- gs[subspt_delete]
      \\ rw[]
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
      \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
      \\ simp [next0_def,block_to_addrs0_def])
QED

Triviality size_of_addr0_del_aux:
  ∀lims refs blocks v l.
    size_of_addr0 lims (del_ptr v refs) (del_blk v blocks) v = 0
Proof
  rw[] \\ Cases_on ‘v’ \\ rw[size_of_addr0_def,lookup_delete]
QED

Triviality size_of_addr0_del:
  ∀lims refs blocks v l.
    v ∉ l ⇒
    ∑ (size_of_addr0 lims refs blocks) l =
    ∑ (size_of_addr0 lims (del_ptr v refs) (del_blk v blocks)) l
Proof
  rw[] \\ irule SUM_IMAGE_CONG \\ rw[]
  \\ Cases_on ‘x’ \\ rw[size_of_addr0_def]
  \\ Cases_on ‘v’ \\ rw[lookup_delete]
  \\ gs[]
QED

Triviality size_of_addr0_del_in:
  ∀lims refs blocks v l.
    v ∈ l ∧ FINITE l ⇒
    ∑ (size_of_addr0 lims refs blocks) l =
    ∑ (size_of_addr0 lims (del_ptr v refs) (del_blk v blocks)) l +
    size_of_addr0 lims refs blocks v
Proof
  rw[]
  \\ ‘l = {v} ∪ (l DELETE v)’ by
    (rw [DELETE_DEF,FUN_EQ_THM] \\ gs[IN_DEF]
     \\ EQ_TAC \\ metis_tac [])
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ qmatch_goalsub_abbrev_tac ‘∑ ff (vv ∪ ll)’
  \\ qspecl_then [‘ff’,‘vv’,‘ll’] mp_tac SUM_IMAGE_UNION
  \\ impl_tac >- (UNABBREV_ALL_TAC \\ simp[])
  \\ disch_then (simp o single)
  \\ qmatch_goalsub_abbrev_tac ‘∑ ff' (vv ∪ ll)’
  \\ qspecl_then [‘ff'’,‘vv’,‘ll’] mp_tac SUM_IMAGE_UNION
  \\ impl_tac >- (UNABBREV_ALL_TAC \\ simp[])
  \\ disch_then (simp o single)
  \\ ‘vv ∩ ll = ∅’ by
    (UNABBREV_ALL_TAC \\ rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM])
  \\ simp [SUM_IMAGE_THM,Abbr‘vv’,Abbr‘ff’,Abbr‘ff'’,size_of_addr0_del_aux]
  \\ irule size_of_addr0_del
  \\ simp[Abbr‘ll’]
QED

Triviality FINITE_reachable_v0_0:
  ∀refs blocks roots.
    FINITE roots ⇒
    FINITE (reachable_v0 refs blocks roots)
Proof
  rw[]
  \\ qspec_then ‘to_addrs (blocks_to_vs (sptree$toList blocks)) ∪
                 to_addrs (ref_to_vs (sptree$toList refs))  ∪
                 roots’
                mp_tac SUBSET_FINITE
  \\ impl_tac >- rw[FINITE_to_addrs]
  \\ disch_then ho_match_mp_tac
  \\ rw [SUBSET_DEF,IN_DEF,reachable_v0_def]
  \\ gs[Once RTC_CASES2]
  \\ Cases_on ‘u’
  >- (gs[next0_def,block_to_addrs0_def]
      \\ Cases_on ‘lookup n blocks’ \\ gs []
      \\ Cases_on ‘x''’ \\ gs []
      \\ rw[] \\ DISJ1_TAC \\ DISJ1_TAC
      \\ gs[IN_DEF] \\ pop_assum mp_tac
      \\ rw[]
      \\ qmatch_goalsub_abbrev_tac ‘blocks_to_vs ll’
      \\ ‘MEM (Block n0 n' l) ll’ by
        (gs[Abbr‘ll’,MEM_toList] \\ metis_tac [])
      \\ pop_assum mp_tac
      \\ qpat_x_assum ‘to_addrs _ _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp[AND_IMP_INTRO]
      \\ induct_on ‘ll’
      \\ rw[]
      >- (simp[blocks_to_vs_def,to_addrs_APPEND,IN_DEF])
      \\ first_x_assum drule_all \\ rw[]
      \\ Cases_on ‘h’ \\ rw[]
      \\ rw[blocks_to_vs_def,to_addrs_def,to_addrs_APPEND,IN_DEF])
  >-(gs[next0_def,ptr_to_addrs0_def]
     \\ Cases_on ‘lookup n refs’ \\ gs[]
     \\ Cases_on ‘x''’ \\ gs[]
     \\ ‘MEM (ValueArray l) (toList refs)’ by metis_tac[MEM_toList]
     \\ DISJ1_TAC \\ DISJ2_TAC
     \\ pop_assum mp_tac \\ qpat_x_assum ‘x ∈ _’ mp_tac
     \\ rpt (pop_assum kall_tac)
     \\ qmatch_goalsub_abbrev_tac ‘MEM _ ll’
     \\ pop_assum kall_tac \\ simp[AND_IMP_INTRO]
     \\ induct_on ‘ll’
     \\ rw[]
     >- (simp[ref_to_vs_def,to_addrs_APPEND])
     \\ first_x_assum drule_all \\ rw[]
     \\ Cases_on ‘h’ \\ rw[]
     \\ rw[ref_to_vs_def,to_addrs_def,to_addrs_APPEND,IN_DEF])
QED

Triviality reachable_v0_UNION:
  ∀refs blocks a b.
  reachable_v0 refs blocks (a ∪ b) =
    reachable_v0 refs blocks a ∪ reachable_v0 refs blocks b
Proof
  gs[reachable_v0_def,FUN_EQ_THM] \\ rw[] \\ EQ_TAC
  \\ rw[] \\ metis_tac []
QED

Triviality addrs_in_subspt:
  ∀refs1 refs2 blocks1 blocks2 v.
    subspt refs1 refs2 ∧ subspt blocks1 blocks2 ⇒
      addrs_in refs1 blocks1 v ⇒ addrs_in refs2 blocks2 v
Proof
  rw[] \\ Cases_on ‘v’ \\ gs[addrs_in_def,subspt_lookup]
  \\ EVERY_CASE_TAC \\ gs[subspt_def,domain_lookup]
  \\ first_x_assum drule \\ rw[] \\ gs[]
QED

Triviality not_addrs_in_subspt:
  ∀refs1 refs2 blocks1 blocks2 v.
    subspt refs1 refs2 ∧ subspt blocks1 blocks2 ⇒
      ¬(addrs_in refs2  blocks2 v) ⇒ ¬(addrs_in refs1 blocks1 v)
Proof
 rpt gen_tac \\ disch_then assume_tac \\ gs[]
 \\ CCONTR_TAC \\ gs[]
 \\ metis_tac [addrs_in_subspt]
QED

(* TODO: Move to sptreeTheory *)
Theorem subspt_difference:
  ∀l r x.
    subspt l r ⇒ subspt (difference x r) (difference x l)
Proof
  rw[subspt_def,domain_lookup,lookup_difference]
  >- (Cases_on ‘lookup k l’ \\ simp[]
      \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ gs[])
  >- (IF_CASES_TAC >- metis_tac []
      \\ Cases_on ‘lookup k l’ \\ simp[]
      \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ gs[])
QED

Triviality reachable_v0_idem:
  ∀l refs blocks.
    (∀v. v ∈ l ⇒ ¬addrs_in refs blocks v)
    ⇒ reachable_v0 refs blocks l = l
Proof
  rw[reachable_v0_def,FUN_EQ_THM] \\ EQ_TAC \\ rw[]
  >- (drule ((fst o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
      \\ rw[] \\ gs[IN_DEF] \\ first_x_assum drule
      \\ Cases_on ‘x'’ \\ rw[addrs_in_def]
      \\ gs[next0_def,block_to_addrs0_def,ptr_to_addrs0_def]
      \\ EVERY_CASE_TAC \\ gs[])
  >- (simp[IN_DEF] \\ asm_exists_tac \\ simp[])
QED

Triviality size_of_reachable_not_addrs_in:
  ∀lims vs refs seen n refs0 seen0 blocks.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
        ∀v. v ∈ to_addrs vs ⇒ ¬addrs_in refs0 (difference blocks seen0) v
Proof
  ho_match_mp_tac size_of_ind \\ rw[] \\ gs[to_addrs_def]
  >- (gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ qmatch_asmsub_rename_tac ‘to_addrs (x::xs)’
      \\ gs [Once to_addrs_cons]
      \\ first_x_assum drule
      \\ disch_then (qspec_then ‘blocks’ assume_tac)
      \\ pop_assum mp_tac
      \\ ho_match_mp_tac not_addrs_in_subspt
      \\ simp[] \\ irule_at Any size_of_refs_subspt
      \\ asm_exists_tac  \\ drule size_of_seen_pres
      \\ rw[subspt_difference])
  >- (gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ Cases_on ‘lookup r refs’ \\ gs[addrs_in_def]
      \\ Cases_on ‘x’ \\ gs[addrs_in_def]
      >~ [‘delete r refs = _’]
      >- (rveq \\ gs[lookup_delete])
      \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ drule size_of_refs_subspt
      \\ rw[subspt_lookup]
      \\ Cases_on ‘lookup r refs'’ \\ gs[]
      \\ first_x_assum drule \\ gs[lookup_delete])
  >- (gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ Cases_on ‘lookup ts seen’ \\ gs[addrs_in_def,lookup_difference]
      \\ rveq \\ drule size_of_seen_pres
      \\ rw[subspt_lookup])
QED

Triviality size_of_reachable_v0_idem:
  ∀lims vs refs seen n refs0 seen0 blocks.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
        reachable_v0 refs0 (difference blocks seen0) (to_addrs vs) = to_addrs vs
Proof
  rw[]
  \\ irule reachable_v0_idem
  \\ ho_match_mp_tac size_of_reachable_not_addrs_in
  \\ metis_tac[]
QED


Triviality reachable_v0_nil:
  ∀refs blocks. reachable_v0 refs blocks ∅ = ∅
Proof
  rw[reachable_v0_def]
QED

Triviality size_of_addrs_addrs_in_eq:
  ∀lims refs refs0 blocks blocks0 l.
    FINITE l ∧
    subspt refs0 refs ∧
    subspt blocks0 blocks ∧
    (∀v. v ∈ l ⇒ (addrs_in refs0 blocks0 v ⇔ addrs_in refs blocks v)) ⇒
    ∑ (size_of_addr0 lims refs blocks)   l =
    ∑ (size_of_addr0 lims refs0 blocks0) l
Proof
  rw[] \\ irule SUM_IMAGE_CONG \\ rw[] \\ Cases_on ‘x’
  \\ first_x_assum drule \\ gs[subspt_lookup]
  \\ EVAL_TAC \\ EVERY_CASE_TAC \\ gs[]
  \\ first_x_assum drule \\ gs[]
QED

Triviality next0_addrs_in:
∀refs blocks v x.
  next0 refs blocks v x ⇒ addrs_in refs blocks v
Proof
  rpt (gen_tac) \\ Cases_on ‘v’
  \\ simp[next0_def,ptr_to_addrs0_def,block_to_addrs0_def,addrs_in_def]
  >- (cases_on ‘lookup n blocks’ \\ gs[])
  >- (cases_on ‘lookup n refs’ \\ gs[])
QED

Triviality reachable_v0_subspt:
  ∀refs refs0 blocks blocks0 l v.
    subspt refs0 refs ∧
    subspt blocks0 blocks ∧
    v ∈ reachable_v0 refs0 blocks0 l ⇒
    v ∈ reachable_v0 refs blocks l
Proof
  rw[IN_DEF] \\ Cases_on ‘v’
  \\ gs[reachable_v0_def,block_to_addrs0_def,ptr_to_addrs0_def]
  \\ metis_tac [next0_subspt]
QED

Triviality not_reachable_v0_subspt:
  ∀refs refs0 blocks blocks0 l v.
    subspt refs0 refs ∧
    subspt blocks0 blocks ∧
    v ∉ reachable_v0 refs blocks l ⇒
    v ∉ reachable_v0 refs0 blocks0 l
Proof
  metis_tac [reachable_v0_subspt]
QED

Triviality wf_seen_size_of:
  ∀lims vs refs seen n' refs' seen'.
    wf seen ∧ (size_of lims vs refs seen = (n',refs',seen'))
    ⇒ wf seen'
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [wf_insert,wf_delete]
QED

(* TODO: Move to sptreeTheory *)
Theorem difference_difference:
  ∀x r l.
    wf x ∧ wf r ∧ wf l ∧ subspt l r ⇒
    difference (difference x l) r = difference x r
Proof
  rw[]
  \\ ‘wf (difference x r) ∧ wf (difference (difference x l) r)’ by
     simp[wf_difference]
  \\ ntac 3 (last_x_assum kall_tac)
  \\ dxrule_all spt_eq_thm
  \\ disch_then (simp o single)
  \\ rw[] \\ gs[subspt_lookup]
  \\ simp[lookup_difference]
  \\ IF_CASES_TAC \\ gs[]
  \\ IF_CASES_TAC \\ gs[]
  \\ Cases_on ‘lookup n l’ \\ gs[]
  \\ first_x_assum drule \\ gs[]
QED

Triviality size_of_reachable_v0_cases:
  ∀lims vs refs seen n refs0 seen0.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
    ∀blocks.
      wf seen ∧ wf blocks ∧
      blocks0_roots_inv blocks seen vs   ∧
      blocks0_refs_inv  blocks seen refs ∧
      blocks0_all_inv   blocks seen ⇒
      (∀v. v ∈ reachable_v0 refs blocks (to_addrs vs) ⇒
          ¬addrs_in refs0  (difference blocks seen0) v) ∧
      (∀v. v ∉ reachable_v0 refs blocks (to_addrs vs) ⇒
          (next0 refs0  (difference blocks seen0) v =
           (next0 refs  blocks v)))
Proof
  let val cons_invariants =
      first_x_assum (qspec_then ‘blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- (last_x_assum kall_tac
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM]
          \\ metis_tac [])
      \\ first_x_assum (qspec_then ‘difference blocks seen1’ mp_tac)
      \\ impl_tac \\ rw[]
      (* head invariants *)
      >- metis_tac [wf_seen_size_of]
      >- metis_tac [wf_difference,wf_seen_size_of]
      >- (gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ ‘subspt refs1 refs’ by metis_tac [size_of_refs_subspt]
          \\ gs[subspt_lookup] \\ first_x_assum drule
          \\ disch_then (first_x_assum o C (mp_then Any assume_tac))
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_all_inv_def] \\ rw[]
          \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘l’] mp_tac)
          \\ impl_tac >- gs[lookup_difference]
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM
                ,lookup_difference,lookup_delete,lookup_insert]
          \\ rw[] \\ gs[]
          >- (first_x_assum irule \\ IF_CASES_TAC \\ gs[IS_SOME_EXISTS])
          >- (CCONTR_TAC \\ gs[IS_SOME_EXISTS])
          >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS])
          >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS]
              \\ first_x_assum (qspec_then ‘ts'’ mp_tac)
              \\ simp[] \\ disch_then irule \\ simp[]
              \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
              \\ CCONTR_TAC
              \\ Cases_on ‘lookup ts' seen’ \\ gs[]
              \\ gs[subspt_lookup]))
      val cons_aux1 =
          ‘difference (difference blocks seen1) seen0 =
           difference blocks seen0’ by
          (irule difference_difference
          \\ metis_tac [wf_difference,wf_seen_size_of,
                        subspt_refl,size_of_seen_pres])
      val cons_aux2 =
          ‘difference (difference blocks seen1) seen1 = difference blocks seen1’ by
          metis_tac [difference_difference,wf_difference,
                     wf_seen_size_of,subspt_refl]
      val cons_aux3 =
          ‘difference blocks seen = blocks’ by
          (‘wf (difference blocks seen)’ by simp[wf_difference]
           \\ drule_then (qspec_then ‘blocks’ mp_tac) spt_eq_thm
           \\ rw[FUN_EQ_THM,lookup_difference]
           \\ IF_CASES_TAC \\ gs[]
           \\ gs[blocks0_roots_inv_def,FORALL_AND_THM]
           \\ first_x_assum irule
           \\ qmatch_goalsub_rename_tac ‘lookup nnn seen’
           \\ Cases_on ‘lookup nnn seen’
           \\ gs[])
     val cons_aux = cons_aux1 \\ cons_aux2 \\ cons_aux3
     val block_invariants =
         first_x_assum (qspec_then ‘delete ts blocks’ mp_tac)
         \\ impl_tac \\ rw[wf_insert,wf_delete]
         >- (gs[blocks0_all_inv_def] \\ first_x_assum irule
             \\ qexists_tac ‘tag’ \\ gs [blocks0_roots_inv_def])
         >- (gs[blocks0_refs_inv_def] \\ rw[] \\ first_x_assum drule
             \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
             >- (CCONTR_TAC \\ gs[])
             >- (CCONTR_TAC \\ gs[])
             >- metis_tac [])
         >- (gs[blocks0_all_inv_def] \\ rw[lookup_delete]
             \\ first_x_assum drule
             \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- metis_tac [])
in
  ho_match_mp_tac size_of_ind \\ rw[] \\ gs[size_of_def,to_addrs_def,reachable_v0_nil]
  \\ TRY (rveq \\ cons_aux3 \\ simp[] \\ NO_TAC)
  (* Cons-1 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ qmatch_asmsub_rename_tac ‘to_addrs (x::xs)’
         (* Invariants *)
      \\ cons_invariants
      \\ cons_aux
      \\ gs[] \\ ntac 2 (pop_assum kall_tac)
      \\ qpat_x_assum ‘_ ∈ _’ assume_tac
      \\ gs [Once to_addrs_cons,reachable_v0_UNION]
      >- (Cases_on ‘v ∈ reachable_v0 refs blocks (to_addrs xs)’
          >- (irule not_addrs_in_subspt
              \\ qexistsl_tac [‘difference blocks seen1’,‘refs1’]
              \\ irule_at Any size_of_refs_subspt
              \\ asm_exists_tac  \\ drule size_of_seen_pres
              \\ rw[subspt_difference])
          \\ gs[]
          \\ first_x_assum irule
          \\ qpat_x_assum ‘v ∈ _’ mp_tac
          \\ rw[reachable_v0_def]
          \\ asm_exists_tac \\ simp[]
          \\ qpat_x_assum ‘x' ∈ _’ mp_tac
          \\ qpat_x_assum ‘v ∉ _’ mp_tac
          \\ pop_assum mp_tac
          \\ qid_spec_tac ‘v’
          \\ qid_spec_tac ‘x'’
          \\ ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1
          \\ rw[] \\ gs[]
          \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES2)
          \\ disj2_tac
          \\ first_x_assum (irule_at Any)
          \\ irule (PROVE [] “A ∧ (A ⇒ B) ⇒ A ∧ B”)
          \\ conj_tac
          >- (CCONTR_TAC \\ gs[]
              \\ ‘v' ∈ reachable_v0 refs blocks (to_addrs xs)’
                 suffices_by simp[]
              \\ gs[reachable_v0_def] \\ asm_exists_tac \\ simp[]
              \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES2)
              \\ metis_tac [])
          \\ rw[])
      \\ irule not_addrs_in_subspt
      \\ qexistsl_tac [‘difference blocks seen1’,‘refs1’]
      \\ simp[subspt_domain] \\ irule_at Any size_of_refs_subspt
      \\ asm_exists_tac  \\ drule size_of_seen_pres
      \\ rw[subspt_difference])
  (* Cons-2 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ qmatch_asmsub_rename_tac ‘to_addrs (x::xs)’
         (* Invariants *)
      \\ cons_invariants
      \\ cons_aux
      \\ gs[]
      \\ qpat_x_assum ‘_ ∉ _’ assume_tac
      \\ gs [Once to_addrs_cons,reachable_v0_UNION]
      \\ first_x_assum drule
      \\ disch_then (simp o single o GSYM)
      \\ first_x_assum irule
      \\ irule not_reachable_v0_subspt
      \\ asm_exists_tac \\ simp[]
      \\ metis_tac [subspt_difference,size_of_seen_pres,size_of_refs_subspt])
  (* Refs-1 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ Cases_on ‘lookup r refs’ \\ gs[]
      >- (rveq \\ gs[reachable_v0_def,IN_DEF]
          \\ drule ((fst o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
          \\ rw[] \\ gs[next0_def,ptr_to_addrs0_def,addrs_in_def])
      \\ reverse (Cases_on ‘x’) \\ gs[]
      >- (rveq \\ gs[reachable_v0_def,IN_DEF]
          \\ drule ((fst o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
          \\ rw[] \\ gs[next0_def,ptr_to_addrs0_def,addrs_in_def,lookup_delete])
      \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (qspec_then ‘blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- metis_tac [blocks0_refs_inv_def]
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ first_x_assum irule \\ qexists_tac ‘p’
          \\ gs[lookup_delete])
      \\ cons_aux3 \\ gs[]
      \\ drule reachable_v0_del_ptr
      \\ disch_then (qspec_then ‘blocks’ (gs o single))
      \\ simp[addrs_in_def]
      \\ drule size_of_refs_subspt
      \\ simp[subspt_lookup]
      \\ Cases_on ‘lookup r refs'’ \\ gs[]
      \\ asm_exists_tac  \\ simp [lookup_delete])
  (* Refs-2 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ Cases_on ‘lookup r refs’ \\ gs[]
      >- (rveq \\ cons_aux3 \\ simp[])
      \\ reverse (Cases_on ‘x’) \\ gs[]
      >- (rveq \\ gs[reachable_v0_def]
          \\ ‘v ≠ RefAddr r’ by (CCONTR_TAC \\ gs[])
          \\ Cases_on ‘v’
          \\ rw[next0_def,FUN_EQ_THM,IN_DEF,ptr_to_addrs0_def,lookup_delete]
          \\ cons_aux3 \\ simp[])
      \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (qspec_then ‘blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- metis_tac [blocks0_refs_inv_def]
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ first_x_assum irule \\ qexists_tac ‘p’
          \\ gs[lookup_delete])
      \\ drule reachable_v0_del_ptr
      \\ disch_then (qspec_then ‘blocks’ (gs o single))
      \\ Cases_on ‘v’
      \\ rw[next0_def,FUN_EQ_THM,IN_DEF,ptr_to_addrs0_def,lookup_delete])
  (* Block-1 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ reverse (Cases_on ‘lookup ts seen’) \\ gs[]
      \\ cons_aux3 \\ gs[]
      >- (rveq \\ gs[reachable_v0_def]
          \\ drule ((fst o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1) \\ rw[]
          \\ gs[next0_def,lookup_difference,block_to_addrs0_def,
                addrs_in_def,blocks0_roots_inv_def])
      \\ gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ block_invariants
      \\ ‘lookup ts blocks = SOME (Block ts tag (v20::v21))’ by
          gs[blocks0_roots_inv_def]
      \\ drule reachable_v0_del_blk
      \\ disch_then (qspec_then ‘refs’ (gs o single))
      >- (‘difference (delete ts blocks) seen' = difference blocks seen'’ by
          (‘wf (difference blocks seen') ∧
            wf (difference (delete ts blocks) seen')’ by
            metis_tac[wf_seen_size_of,wf_difference,wf_delete,wf_insert]
           \\ dxrule_all spt_eq_thm \\ rw[]
           \\ rw[lookup_difference,lookup_delete]
           \\ drule size_of_seen_pres
           \\ simp [subspt_lookup]
           \\ qexists_tac ‘n’ \\ simp [])
          \\ gs[])
      \\ irule not_addrs_in_subspt
      \\ irule_at Any size_of_refs_subspt
      \\ irule_at Any subspt_difference
      \\ irule_at Any size_of_seen_pres
      \\ asm_exists_tac \\ simp[]
      \\ asm_exists_tac \\ simp[]
      \\ simp[addrs_in_def,lookup_insert,lookup_difference])
  (* Block-2 *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ reverse (Cases_on ‘lookup ts seen’) \\ gs[]
      \\ cons_aux3 \\ gs[]
      \\ gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ block_invariants
      \\ ‘lookup ts blocks = SOME (Block ts tag (v20::v21))’ by
         gs[blocks0_roots_inv_def]
      \\ drule reachable_v0_del_blk
      \\ disch_then (qspec_then ‘refs’ (gs o single))
      \\ ‘difference (delete ts blocks) seen' = difference blocks seen'’ by
          (‘wf (difference blocks seen') ∧
            wf (difference (delete ts blocks) seen')’ by
            metis_tac[wf_seen_size_of,wf_difference,wf_delete,wf_insert]
           \\ dxrule_all spt_eq_thm \\ rw[]
           \\ rw[lookup_difference,lookup_delete]
           \\ drule size_of_seen_pres
           \\ simp [subspt_lookup]
           \\ qexists_tac ‘n’ \\ simp [])
      \\ gs[]
      \\ Cases_on ‘v’
      \\ rw[next0_def,FUN_EQ_THM,IN_DEF,block_to_addrs0_def,lookup_delete,lookup_difference]
      \\ gs[lookup_insert]
      \\ EVERY_CASE_TAC \\ gs[]
      \\ Cases_on ‘lookup n seen’ \\ gs[]
      \\ gs[blocks0_roots_inv_def])
end
QED

Triviality size_of_addrs_in:
  ∀lims vs refs seen n refs0 seen0.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
    ∀blocks.
      wf seen ∧ wf blocks ∧
      blocks0_roots_inv blocks seen vs   ∧
      blocks0_refs_inv  blocks seen refs ∧
      blocks0_all_inv   blocks seen ⇒
      ∀v. v ∉ reachable_v0 refs blocks (to_addrs vs) ⇒
          addrs_in refs0  (difference blocks seen0) v =
            (addrs_in refs blocks v)
Proof
  let val cons_invariants =
      first_x_assum (qspec_then ‘blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- (last_x_assum kall_tac
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM]
          \\ metis_tac [])
      \\ first_x_assum (qspec_then ‘difference blocks seen1’ mp_tac)
      \\ impl_tac \\ rw[]
      (* head invariants *)
      >- metis_tac [wf_seen_size_of]
      >- metis_tac [wf_difference,wf_seen_size_of]
      >- (gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ ‘subspt refs1 refs’ by metis_tac [size_of_refs_subspt]
          \\ gs[subspt_lookup] \\ first_x_assum drule
          \\ disch_then (first_x_assum o C (mp_then Any assume_tac))
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_all_inv_def] \\ rw[]
          \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘l’] mp_tac)
          \\ impl_tac >- gs[lookup_difference]
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM
                ,lookup_difference,lookup_delete,lookup_insert]
          \\ rw[] \\ gs[]
          >- (first_x_assum irule \\ IF_CASES_TAC \\ gs[IS_SOME_EXISTS])
          >- (CCONTR_TAC \\ gs[IS_SOME_EXISTS])
          >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS])
           >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS]
              \\ first_x_assum (qspec_then ‘ts'’ mp_tac)
              \\ simp[] \\ disch_then irule \\ simp[]
              \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
              \\ CCONTR_TAC
              \\ Cases_on ‘lookup ts' seen’ \\ gs[]
              \\ gs[subspt_lookup]))
      val cons_aux1 =
          ‘difference (difference blocks seen1) seen0 =
           difference blocks seen0’ by
          (irule difference_difference
          \\ metis_tac [wf_difference,wf_seen_size_of,
                        subspt_refl,size_of_seen_pres])
      val cons_aux2 =
          ‘difference (difference blocks seen1) seen1 = difference blocks seen1’ by
          metis_tac [difference_difference,wf_difference,
                     wf_seen_size_of,subspt_refl]
      val cons_aux3 =
          ‘difference blocks seen = blocks’ by
          (‘wf (difference blocks seen)’ by simp[wf_difference]
           \\ drule_then (qspec_then ‘blocks’ mp_tac) spt_eq_thm
           \\ rw[FUN_EQ_THM,lookup_difference]
           \\ IF_CASES_TAC \\ gs[]
           \\ gs[blocks0_roots_inv_def,FORALL_AND_THM]
           \\ first_x_assum irule
           \\ qmatch_goalsub_rename_tac ‘lookup nnn seen’
           \\ Cases_on ‘lookup nnn seen’
           \\ gs[])
     val cons_aux = cons_aux1 \\ cons_aux2 \\ cons_aux3
     val block_invariants =
         first_x_assum (qspec_then ‘delete ts blocks’ mp_tac)
         \\ impl_tac \\ rw[wf_insert,wf_delete]
         >- (gs[blocks0_all_inv_def] \\ first_x_assum irule
             \\ qexists_tac ‘tag’ \\ gs [blocks0_roots_inv_def])
         >- (gs[blocks0_refs_inv_def] \\ rw[] \\ first_x_assum drule
             \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
             >- (CCONTR_TAC \\ gs[])
             >- (CCONTR_TAC \\ gs[])
             >- metis_tac [])
         >- (gs[blocks0_all_inv_def] \\ rw[lookup_delete]
             \\ first_x_assum drule
             \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- (CCONTR_TAC \\ gs[]
                 \\ Cases_on ‘ts'' = ts’ \\ gs[]
                 \\ metis_tac [])
             >- metis_tac [])
in
  ho_match_mp_tac size_of_ind \\ rw[] \\ gs[size_of_def,to_addrs_def,reachable_v0_nil]
  \\ TRY (rveq \\ cons_aux3 \\ simp[] \\ NO_TAC)
  (* Cons *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ qmatch_asmsub_rename_tac ‘to_addrs (x::xs)’
         (* Invariants *)
      \\ cons_invariants
      \\ cons_aux
      \\ gs[]
      \\ qpat_x_assum ‘_ ∉ _’ assume_tac
      \\ gs [Once to_addrs_cons,reachable_v0_UNION]
      \\ first_x_assum drule
      \\ disch_then (simp o single o GSYM)
      \\ first_x_assum irule
      \\ irule not_reachable_v0_subspt
      \\ asm_exists_tac \\ simp[]
      \\ metis_tac [subspt_difference,size_of_seen_pres,size_of_refs_subspt])
  (* Refs *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ Cases_on ‘lookup r refs’ \\ gs[]
      >- (rveq \\ cons_aux3 \\ simp[])
      \\ reverse (Cases_on ‘x’) \\ gs[]
      >- (rveq \\ gs[reachable_v0_def]
          \\ ‘v ≠ RefAddr r’ by (CCONTR_TAC \\ gs[])
          \\ Cases_on ‘v’
          \\ rw[next0_def,FUN_EQ_THM,IN_DEF,ptr_to_addrs0_def,lookup_delete]
          \\ rveq \\ cons_aux3 \\ simp[addrs_in_def,lookup_delete])
      \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (qspec_then ‘blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- metis_tac [blocks0_refs_inv_def]
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ first_x_assum irule \\ qexists_tac ‘p’
          \\ gs[lookup_delete])
      \\ drule reachable_v0_del_ptr
      \\ disch_then (qspec_then ‘blocks’ (gs o single))
      \\ Cases_on ‘v’
      \\ rw[next0_def,FUN_EQ_THM,IN_DEF,ptr_to_addrs0_def,lookup_delete]
      \\ simp[addrs_in_def,lookup_delete])
  (* Block *)
  >- (rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ reverse (Cases_on ‘lookup ts seen’) \\ gs[]
      >- (rveq \\ cons_aux3 \\ simp[])
      \\ gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ block_invariants
      \\ ‘lookup ts blocks = SOME (Block ts tag (v20::v21))’ by
         gs[blocks0_roots_inv_def]
      \\ drule reachable_v0_del_blk
      \\ disch_then (qspec_then ‘refs’ (gs o single))
      \\ ‘difference (delete ts blocks) seen' = difference blocks seen'’ by
          (‘wf (difference blocks seen') ∧
            wf (difference (delete ts blocks) seen')’ by
            metis_tac[wf_seen_size_of,wf_difference,wf_delete,wf_insert]
           \\ dxrule_all spt_eq_thm \\ rw[]
           \\ rw[lookup_difference,lookup_delete]
           \\ drule size_of_seen_pres
           \\ simp [subspt_lookup]
           \\ qexists_tac ‘n’ \\ simp [])
      \\ gs[]
      \\ Cases_on ‘v’
      \\ rw[next0_def,FUN_EQ_THM,IN_DEF,block_to_addrs0_def,lookup_delete,lookup_difference]
      \\ gs[lookup_insert]
      \\ EVERY_CASE_TAC \\ gs[]
      \\ Cases_on ‘lookup n seen’ \\ gs[]
      \\ gs[blocks0_roots_inv_def]
      \\ simp[addrs_in_def,lookup_delete])
end
QED

(* TODO: Move? *)
Theorem DELETE_DIFF:
  ∀a x b.
    a DELETE x DIFF b = a DIFF b DELETE x
Proof
  rw[FUN_EQ_THM,DELETE_DEF,DIFF_DEF] \\ EQ_TAC
  \\ rw[]
QED

(* TODO: Move? *)
Theorem SUM_IMAGE_DIFF:
   ∀f a b.  FINITE a ∧ FINITE b ⇒ ∑ f (a DIFF b) = ∑ f a - ∑ f (a ∩ b)
Proof
  ntac 4 strip_tac \\ pop_assum mp_tac \\ qid_spec_tac ‘b’
  \\ ho_match_mp_tac FINITE_COMPLETE_INDUCTION \\ rw[]
  \\ Cases_on ‘b = ∅’ \\ simp[SUM_IMAGE_THM]
  \\ drule REST_PSUBSET
  \\ disch_then (first_x_assum o C (mp_then Any assume_tac))
  \\ drule CHOICE_INSERT_REST \\ disch_then (ONCE_REWRITE_TAC o single o GSYM)
  \\ Cases_on ‘CHOICE b ∈ a’
  \\ simp [DIFF_INSERT,Once INTER_COMM,SUM_IMAGE_DELETE,
           SUM_IMAGE_THM,INSERT_INTER,DELETE_DIFF,SUM_IMAGE_DELETE,
           CHOICE_NOT_IN_REST]
  \\ goal_assum (irule o GSYM)
  \\ simp [DIFF_INSERT,Once INTER_COMM,SUM_IMAGE_DELETE,
           SUM_IMAGE_THM,INSERT_INTER,DELETE_DIFF,SUM_IMAGE_DELETE,
           CHOICE_NOT_IN_REST]
  \\ simp[Once INTER_COMM]
QED

(* TODO: Move? *)
Theorem SUM_IMAGE_SUBSET_SPLIT:
∀l f r.
  FINITE r ∧
  FINITE l ∧
  r ⊆ l ⇒
  ∑ f l = ∑ f r + ∑ f (l DIFF r)
Proof
  rw[]
  \\ qspecl_then [‘f’,‘l’,‘r’] mp_tac SUM_IMAGE_DIFF
  \\ simp[] \\ disch_then (simp o single)
  \\ simp[SUB_LEFT_ADD]
  \\ IF_CASES_TAC
  >- (‘∑ f (l ∩ r) ≤ ∑ f r’ by
     (irule SUM_IMAGE_SUBSET_LE \\ simp[])
      \\ simp[EQ_LESS_EQ]
      \\ gs[SUM_IMAGE_SUBSET_LE])
  \\ dxrule_all SUM_IMAGE_UNION
  \\ disch_then (qspec_then ‘f’ (simp o single o GSYM))
  \\ simp[Once UNION_COMM]
  \\ gs[SUBSET_UNION_ABSORPTION]
QED

Triviality size_of_eq_aux_size_of:
  ∀lims vs refs seen n refs0 seen0.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
    ∀blocks.
      wf seen ∧ wf blocks ∧
      blocks0_roots_inv blocks seen vs   ∧
      blocks0_refs_inv  blocks seen refs ∧
      blocks0_all_inv   blocks seen      ⇒
        aux_size_of lims refs blocks vs = n
Proof
  ho_match_mp_tac size_of_ind \\ rw[]
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v0_def] \\ EVAL_TAC)
     (* TODO *)
  >- (gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (first_assum o mp_then Any mp_tac)
      (* tail invariants *)
      \\ impl_tac \\ rw[]
      >- (last_x_assum kall_tac
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM]
          \\ metis_tac [])
      \\ first_x_assum (qspec_then ‘difference blocks seen1’ mp_tac)
      \\ impl_tac \\ rw[]
      (* head invariants *)
      >- metis_tac [wf_seen_size_of]
      >- metis_tac [wf_seen_size_of,wf_difference]
      >- (gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_refs_inv_def] \\ rw[]
          \\ ‘subspt refs1 refs’ by metis_tac [size_of_refs_subspt]
          \\ gs[subspt_lookup] \\ first_x_assum drule
          \\ disch_then (first_x_assum o C (mp_then Any assume_tac))
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks0_all_inv_def] \\ rw[]
          \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘l’] mp_tac)
          \\ impl_tac >- gs[lookup_difference]
          \\ gs[blocks0_roots_inv_def,FORALL_AND_THM
                ,lookup_difference,lookup_delete,lookup_insert]
          \\ rw[] \\ gs[]
          >- (first_x_assum irule \\ IF_CASES_TAC \\ gs[IS_SOME_EXISTS])
          >- (CCONTR_TAC \\ gs[IS_SOME_EXISTS])
          >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS])
          >- (Cases_on ‘ts' = ts’ \\ gs[IS_SOME_EXISTS]
              \\ first_x_assum (qspec_then ‘ts'’ mp_tac)
              \\ simp[] \\ disch_then irule \\ simp[]
              \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
              \\ CCONTR_TAC
              \\ Cases_on ‘lookup ts' seen’ \\ gs[]
              \\ gs[subspt_lookup]))
      \\ gs[aux_size_of_def]
      \\ qmatch_goalsub_abbrev_tac ‘a + nn = _’
      \\ qmatch_goalsub_abbrev_tac ‘_ = b + (c + nn)’
      \\ ‘a = b + c’ suffices_by simp[]
      \\ UNABBREV_ALL_TAC
      \\ qpat_abbrev_tac ‘xs = y :: ys’
      \\ simp [Once to_addrs_cons,reachable_v0_UNION]
      \\ qmatch_goalsub_abbrev_tac ‘∑ ff (rr UNION nxt)’
      \\ qspecl_then [‘ff’,‘rr’,‘nxt’] mp_tac SUM_IMAGE_UNION
      \\ impl_tac
      >- (UNABBREV_ALL_TAC \\ simp[FINITE_reachable_v0_0,FINITE_to_addrs])
      \\ disch_then (simp o single) \\ simp[]
      \\ ‘∑ ff (rr ∩ nxt) ≤ ∑ ff rr’ by
        (irule SUM_IMAGE_SUBSET_LE
         \\ gs[Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs])
      \\ drule LESS_EQ_ADD_SUB
      \\ disch_then (qspec_then ‘∑ ff nxt’ (ONCE_REWRITE_TAC o single))
      \\ simp[]
      \\ qspecl_then [‘ff’,‘rr’,‘nxt’] mp_tac SUM_IMAGE_DIFF
      \\ impl_tac >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
      \\ disch_then (simp o single o GSYM)
      \\ qpat_x_assum  ‘size_of _ xs _ _ = _’ assume_tac
      \\ drule size_of_addrs_in
      \\ disch_then (qspec_then ‘blocks’ mp_tac) \\ simp[]
      \\ ‘blocks0_roots_inv blocks seen xs’ by
          (gs[blocks0_roots_inv_def,FORALL_AND_THM]
           \\ metis_tac [])
      \\ simp[] \\ rw[]
      \\ ‘(∀v. v ∈ (rr DIFF nxt) ⇒
             (addrs_in refs1 (difference blocks seen1) v ⇔
              addrs_in refs blocks v))’ by
         rw[]
      \\ drule size_of_seen_pres
      \\ drule size_of_refs_subspt
      \\ rw[]
      \\ ‘FINITE (rr DIFF nxt)’ by
          rw[Abbr‘rr’,Abbr‘nxt’,FINITE_DIFF,
             FINITE_reachable_v0_0,FINITE_to_addrs]
      \\ ‘subspt (difference blocks seen1) blocks’
         by (rw[subspt_lookup] \\ gs[lookup_difference])
      \\ drule_all size_of_addrs_addrs_in_eq
      \\ disch_then (qspec_then ‘lims’ mp_tac)
      \\ qunabbrev_tac ‘ff’ \\ disch_then (simp o single)
      \\ drule size_of_reachable_v0_cases
      \\ disch_then (qspec_then ‘blocks’ mp_tac)
      \\ rw[]
      \\ qmatch_goalsub_abbrev_tac ‘∑ ff' _’
      \\ qspecl_then [‘ff'’,‘rr’,‘nxt’] mp_tac SUM_IMAGE_DIFF
      \\ impl_tac >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
      \\ disch_then (simp o single)
      \\ ‘∑ ff' (rr ∩ nxt) = 0’ by
         (‘FINITE (rr ∩ nxt)’ by
            simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
          \\ drule SUM_IMAGE_ZERO
          \\ disch_then (qspec_then ‘ff'’ (simp o single))
          \\ rw[] \\ first_x_assum drule \\ qunabbrev_tac ‘ff'’
          \\ Cases_on ‘x'’ \\ EVAL_TAC \\ EVERY_CASE_TAC \\ gs[])
      \\ qmatch_goalsub_abbrev_tac ‘_ = ∑ _ ll’
      \\ qspecl_then [‘rr’,‘ff'’,‘ll’] mp_tac SUM_IMAGE_SUBSET_SPLIT
      \\ impl_tac
      >- (rw [Abbr‘ll’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs,SUBSET_DEF]
          \\ irule reachable_v0_subspt
          \\ asm_exists_tac \\ simp[])
      \\ disch_then (simp o single)
      \\ ‘FINITE (rr DIFF ll)’ by
            simp[Abbr‘ll’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
      \\ drule SUM_IMAGE_ZERO
      \\ disch_then (qspec_then ‘ff'’ (simp o single))
      \\ rw[Abbr‘rr’,Abbr‘ll’,Abbr‘ff'’]
      \\ Cases_on ‘x' ∈ nxt’
      >- (first_x_assum drule
          \\ Cases_on ‘x'’
          \\ EVAL_TAC \\ EVERY_CASE_TAC \\ gs[])
      \\ qpat_x_assum ‘x' ∉ reachable_v0 _ _ _ ’ mp_tac
      \\ qpat_x_assum ‘x' ∈ reachable_v0 _ _ _ ’ mp_tac
      \\ rw[reachable_v0_def,IN_DEF]
      \\ first_x_assum (qspec_then ‘x''’ mp_tac)
      \\ simp[] \\ CCONTR_TAC \\ gs[]
      \\ pop_assum mp_tac \\ simp[]
      \\ qmatch_asmsub_rename_tac ‘(next0 refs blocks)^* l r’
      \\ ‘l ∉ nxt’ by
        (Cases_on ‘r = l’ \\ gs[]
         \\ CCONTR_TAC \\ gs[]
         \\ simp[Abbr‘nxt’]
         \\ qpat_x_assum ‘r ∉ reachable_v0 _ _ _ ’ mp_tac
         \\ simp[] \\ pop_assum mp_tac
         \\ rw[reachable_v0_def] \\ asm_exists_tac
         \\ simp[] \\ metis_tac [RTC_RTC])
      \\ qpat_x_assum ‘l ∉ _’ mp_tac
      \\ qpat_x_assum ‘r ∉ _’ mp_tac
      \\ qpat_x_assum ‘RTC _ l r’ mp_tac
      \\ ntac 2 (pop_assum kall_tac)
      \\ qid_spec_tac ‘r’
      \\ qid_spec_tac ‘l’
      \\ ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 \\ rw[]
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES2)
      \\ disj2_tac
      \\ gs[AND_IMP_INTRO]
      \\ first_x_assum (irule_at Any)
      \\ irule (PROVE [] “A ∧ (A ⇒ B) ⇒ A ∧ B”)
      \\ conj_tac
      >- (CCONTR_TAC \\ gs[]
          \\ simp[Abbr‘nxt’]
          \\ qpat_x_assum ‘r' ∉ reachable_v0 _ _ _ ’ mp_tac
          \\ simp[] \\ pop_assum mp_tac
          \\ rw[reachable_v0_def] \\ asm_exists_tac \\ simp[]
          \\ metis_tac [RTC_CASES2])
      \\ rw[])
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v0_def] \\ EVAL_TAC)
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v0_def]
      \\ cases_on ‘small_num lims.arch_64_bit i’
      \\ gs[flat_measure_def] \\ EVAL_TAC)
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v0_def] \\ EVAL_TAC)
  >- (cases_on ‘lookup r refs’ \\ gs[] \\ TRY (cases_on ‘x’)
      >~ [‘lookup _ _ = SOME (ValueArray _)’]
      >- (first_x_assum (qspec_then ‘l’ assume_tac) \\ gs[size_of_def]
          \\ pairarg_tac \\ gs[] \\ rveq
          \\ first_x_assum (qspec_then ‘blocks’ mp_tac)
          \\ impl_tac \\ rw[]
          >- metis_tac [blocks0_refs_inv_def]
          >- (gs[blocks0_refs_inv_def] \\ rw[]
              \\ first_x_assum irule \\ qexists_tac ‘p’
              \\ gs[lookup_delete])
          >- (gs[aux_size_of_def,flat_measure_def,to_addrs_def]
              \\ drule reachable_v0_del_ptr
              \\ disch_then (qspec_then ‘blocks’ (simp o single))
              \\ qmatch_goalsub_abbrev_tac ‘∑ ff (nxt UNION rr)’
              \\ qspecl_then [‘ff’,‘nxt’,‘rr’] mp_tac SUM_IMAGE_UNION
              \\ impl_tac
              >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
              \\ disch_then (simp o single)
              \\ qunabbrev_tac ‘rr’
              \\ Cases_on ‘RefAddr r ∈ nxt’
              >- (‘nxt ∩ {RefAddr r} = {RefAddr r}’ by
                    (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
                     \\ EQ_TAC \\ metis_tac [])
                  \\ simp[Abbr‘ff’] \\ drule size_of_addr0_del_in
                  \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
                  \\ impl_tac
                  >- simp[Abbr‘nxt’,FINITE_reachable_v0_0,FINITE_to_addrs]
                  \\ disch_then (simp o single)
                  \\ simp[size_of_addr0_def])
              >- (‘nxt ∩ {RefAddr r} = ∅’ by
                    (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM])
                  \\ simp[Abbr‘ff’,SUM_IMAGE_THM]
                  \\ drule size_of_addr0_del
                  \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
                  \\ disch_then (simp o single)
                  \\ simp[size_of_addr0_def])))
      \\ gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v0_def,flat_measure_def]
      \\ qmatch_goalsub_abbrev_tac ‘∑ _ nxt’
      \\ ‘nxt = {RefAddr r}’ suffices_by simp[SUM_IMAGE_SING,size_of_addr0_def]
      \\ UNABBREV_ALL_TAC \\ simp[FUN_EQ_THM]
      \\ rw[] \\ EQ_TAC \\ rw[]
      \\ drule (RTC_CASES1  |> SPEC_ALL  |> EQ_IMP_RULE  |> fst)
      \\ rw[] \\ gs[next0_def,ptr_to_addrs0_def])
  >- gs[size_of_def,aux_size_of_def,to_addrs_def,
        flat_measure_def,reachable_v0_def,SUM_IMAGE_THM]
  >- (Cases_on ‘lookup ts seen’ \\ gs[]
      >~[‘lookup ts seen = SOME _’]
      >- (gs[size_of_def,blocks0_roots_inv_def] \\ rveq
          \\ first_x_assum (qspec_then ‘ts’ mp_tac)
          \\ rw [aux_size_of_def,to_addrs_def,flat_measure_def]
          \\ qmatch_goalsub_abbrev_tac ‘∑ _ ll’
          \\ ‘ll = {BlockAddr ts}’ by
            (qunabbrev_tac ‘ll’ \\ rw[reachable_v0_def,FUN_EQ_THM]
             \\ EQ_TAC \\ rw[] \\ gs[Once RTC_CASES1,next0_def,block_to_addrs0_def])
          \\ simp[SUM_IMAGE_SING,size_of_addr0_def])
      \\ gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (qspec_then ‘delete ts blocks’ mp_tac)
      \\ impl_tac \\ rw[wf_insert,wf_delete]
      >- (gs[blocks0_all_inv_def] \\ first_x_assum irule
          \\ qexists_tac ‘tag’ \\ gs [blocks0_roots_inv_def])
      >- (gs[blocks0_refs_inv_def] \\ rw[] \\ first_x_assum drule
          \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
          >- (CCONTR_TAC \\ gs[])
          >- (CCONTR_TAC \\ gs[])
          >- metis_tac [])
      >- (gs[blocks0_all_inv_def] \\ rw[lookup_delete]
          \\ first_x_assum drule
          \\ rw[blocks0_roots_inv_def,lookup_delete,lookup_insert]
          >- (CCONTR_TAC \\ gs[]
              \\ Cases_on ‘ts'' = ts’ \\ gs[]
              \\ metis_tac [])
          >- (CCONTR_TAC \\ gs[]
              \\ Cases_on ‘ts'' = ts’ \\ gs[]
              \\ metis_tac [])
          >- (CCONTR_TAC \\ gs[]
              \\ Cases_on ‘ts'' = ts’ \\ gs[]
              \\ metis_tac [])
          >- metis_tac [])
      \\ gs[blocks0_roots_inv_def]
      \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘v20::v21’] assume_tac)
      \\ gs [] \\ rw[aux_size_of_def,flat_measure_def,to_addrs_def]
      \\ drule reachable_v0_del_blk
      \\ disch_then (qspec_then ‘ref’ (simp o single))
      \\ qmatch_goalsub_abbrev_tac ‘∑ ff (nxt UNION rr)’
      \\ qspecl_then [‘ff’,‘nxt’,‘rr’] mp_tac SUM_IMAGE_UNION
      \\ impl_tac
      >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v0_0,FINITE_to_addrs]
      \\ disch_then (simp o single)
      \\ qunabbrev_tac ‘rr’
      \\ Cases_on ‘BlockAddr ts ∈ nxt’
      >- (‘nxt ∩ {BlockAddr ts} = {BlockAddr ts}’ by
            (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
             \\ EQ_TAC \\ metis_tac [])
          \\ simp[Abbr‘ff’] \\ drule size_of_addr0_del_in
          \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
          \\ impl_tac
          >- simp[Abbr‘nxt’,FINITE_reachable_v0_0,FINITE_to_addrs]
          \\ disch_then (simp o single)
          \\ simp[size_of_addr0_def])
      >- (‘nxt ∩ {BlockAddr ts} = ∅’ by rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
          \\ simp[Abbr‘ff’,SUM_IMAGE_THM]
          \\ drule size_of_addr0_del
          \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
          \\ disch_then (simp o single)
          \\ simp[size_of_addr0_def]))
QED

Triviality flat_size_of_eq_aux_size_of:
  ∀lims refs blocks roots.
    flat_size_of lims refs blocks roots =
    aux_size_of lims refs (fromList blocks) roots
Proof
  rw[flat_size_of_def,aux_size_of_def]
  \\ irule SUM_IMAGE_CONG \\ rw[]
  >- (cases_on ‘x’ \\
      gs[size_of_addr0_def,dataSemTheory.size_of_addr_def,
         lookup_fromList,LLOOKUP_THM])
  >- (rw[reachable_v0_def,dataSemTheory.reachable_v_def,FUN_EQ_THM]
      \\ EQ_TAC \\ rw[] \\ asm_exists_tac \\ simp[] (* 2 very similar goals *)
      \\ pop_assum mp_tac \\ ho_match_mp_tac RTC_MONOTONE
      \\ rw[] \\ Cases_on ‘x’
      \\ gs[next0_def,
            block_to_addrs0_def,
            ptr_to_addrs0_def,
            dataSemTheory.next_def,
            dataSemTheory.block_to_addrs_def,
            dataSemTheory.ptr_to_addrs_def,
            lookup_fromList,LLOOKUP_THM])
QED

Definition blocks0_all_inv0_def:
  blocks0_all_inv0 blocks seen =
  ∀ts tag l.
    sptree$lookup ts blocks = SOME (Block ts tag l) ⇒
    blocks0_roots_inv blocks seen l
End

Triviality blocks0_all_inv0_thm:
  ∀blocks.
    blocks0_all_inv0 blocks LN
    ⇒ blocks0_all_inv blocks LN
Proof
  rw[blocks0_all_inv0_def,blocks0_all_inv_def]
  \\ first_x_assum drule
  \\ rw[blocks0_roots_inv_def,lookup_def]
  >- (gs[lookup_insert,lookup_delete,lookup_def]
      \\ Cases_on ‘ts' = ts’ \\ gs[])
  >- (first_x_assum drule \\ rw[]
      \\ gs[lookup_insert,lookup_delete,lookup_def])
QED

(* TODO: Move to sptreeTheory *)
Theorem wf_fromList:
  ∀l. wf (fromList l)
Proof
  Induct_on ‘l’ \\ rw[fromList_def]
  \\ qmatch_goalsub_abbrev_tac ‘FOLDL f a _’
  \\ qspecl_then [‘(λx. wf (SND x))’,‘f’,‘l’,‘a’] mp_tac FOLDL_invariant
  \\ simp[] \\ disch_then irule \\ rw[]
  >- (Cases_on ‘x’ \\ gs[Abbr‘f’,wf_insert])
  >- (simp[Abbr‘a’,wf_insert])
QED

Triviality blocks_roots_to_all_blocks_roots:
  ∀blocks roots.
    blocks0_roots_inv (fromList blocks) LN roots ⇔
      all_blocks_roots_inv blocks roots
Proof
  rw[blocks0_roots_inv_def,all_blocks_roots_inv_def,lookup_def]
  \\ EQ_TAC \\ rw[] \\ gs[lookup_fromList,LLOOKUP_THM]
  \\ metis_tac []
QED

Theorem size_of_eq_flat_size_of:
  ∀lims refs blocks roots n refs0 seen0.
    all_blocks_inv refs blocks roots ∧
    size_of lims roots refs LN = (n,refs0,seen0) ⇒
    flat_size_of lims refs blocks roots = n
Proof
  rw[flat_size_of_eq_aux_size_of,all_blocks_inv_def]
  \\ irule size_of_eq_aux_size_of
  \\ simp[wf_fromList] \\ first_x_assum (irule_at Any)
  \\ rw[blocks_roots_to_all_blocks_roots]
  >- (irule blocks0_all_inv0_thm
      \\ gs[blocks0_all_inv0_def,blocks_roots_to_all_blocks_roots,
            lookup_fromList,LLOOKUP_THM,
            all_blocks_blocks_inv_def]
      \\ metis_tac [])
  >- (rw[blocks0_refs_inv_def,blocks_roots_to_all_blocks_roots]
      \\ gs[all_blocks_refs_inv_def] \\ metis_tac [])
QED

Theorem size_of_heap_flat_eq_size_of_heap:
  ∀s.
    size_inv s ⇒
    size_of_heap s = flat_size_of_heap s
Proof
  rw[size_of_heap_def,flat_size_of_heap_def,size_inv_def]
  \\ pairarg_tac \\ gs[]
  \\ metis_tac [size_of_eq_flat_size_of]
QED

val _ = map delete_binding ["block_to_addrs0_def",
                            "ptr_to_addrs0_def",
                            "addrs_in_def",
                            "next0_def",
                            "reachable_v0_def",
                            "size_of_addr0_def",
                            "aux_size_of_def",
                            "blocks0_roots_inv_def",
                            "blocks0_refs_inv_def",
                            "blocks0_all_inv_def",
                            "del_ptr_def",
                            "del_blk_def",
                            "blocks0_all_inv0_def"];

val _ = export_theory();
