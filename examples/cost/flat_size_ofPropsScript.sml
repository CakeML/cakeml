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

(* Any block within a block must also be in all_blocks *)
Definition all_blocks_ok_def:
  all_blocks_ok blocks =
    ∀ts ts' tag tag' l l'.
      MEM (Block ts tag l) blocks ∧
      MEM (Block ts' tag' l') l
      ⇒ MEM (Block ts' tag' l') blocks
End

Theorem to_addrs_APPEND:
  ∀a b. to_addrs (a ++ b) = to_addrs a ∪ to_addrs b
Proof
  Induct \\ rw[to_addrs_def]
  \\ Cases_on ‘h’ \\ rw[to_addrs_def,UNION_ASSOC]
  \\ Cases_on ‘l’ \\ rw[to_addrs_def,UNION_ASSOC]
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
Definition block_to_addrs_def:
  block_to_addrs blocks ts =
  (case sptree$lookup ts blocks of
   | SOME (Block _ _ vs) => to_addrs vs
   | _ => ∅ )
End

Definition ptr_to_addrs_def:
  ptr_to_addrs refs p =
    case sptree$lookup p refs of
      SOME (ValueArray vs) => to_addrs vs
      | _ => {}
End

Definition next_def:
  (next refs blocks (BlockAddr ts) r =
     (r ∈ block_to_addrs blocks ts))
∧ (next refs blocks (RefAddr ref) r =
     (r ∈ ptr_to_addrs refs ref))
End

(* The set of all addresses that can be reached from an initial set of roots *)
Definition reachable_v_def:
  reachable_v refs blocks roots = { y | ∃x. x ∈ roots ∧ (next refs blocks)^* x y}
End

Definition size_of_addr_def:
  (size_of_addr lims refs blocks (BlockAddr ts) =
   (case sptree$lookup ts blocks of
    | SOME (Block _ _ vs) => 1 + LENGTH vs + SUM (MAP (flat_measure lims) vs)
    | _ => 0))
∧ (size_of_addr lims refs blocks (RefAddr p) =
   (case sptree$lookup p refs of
    | SOME (ValueArray vs)  => 1 + LENGTH vs + SUM (MAP (flat_measure lims) vs)
    | SOME (ByteArray _ bs) => LENGTH bs DIV (arch_size lims DIV 8) + 2
    | _ => 0))
End

Definition aux_size_of_def:
  aux_size_of lims refs blocks roots =
    SUM (MAP (flat_measure lims) roots) +
    ∑ (size_of_addr lims refs blocks)
      (reachable_v refs blocks (to_addrs roots))
End

(* If a timestam has been seen then its not in all_blocks; conversely,
   if a timestamp has not been seen and it is present in the roots
   then it must be in all_blocks.
  *)
Definition blocks_roots_inv_def:
  blocks_roots_inv blocks seen roots =
   ∀ts tag l.
     (IS_SOME (sptree$lookup ts (seen : num_set)) ⇒ IS_NONE (sptree$lookup ts blocks)) ∧
     (IS_NONE (sptree$lookup ts seen) ∧ MEM (Block ts tag l) roots ⇒
        lookup ts blocks = SOME (Block ts tag l))
End

(* All values in a reference fulfil blocks_roots_inv *)
Definition blocks_refs_inv_def:
  blocks_refs_inv blocks seen refs =
    ∀p vs.
      sptree$lookup p refs = SOME (ValueArray vs) ⇒
      blocks_roots_inv blocks seen vs
End

(* All values in all_blocks fulfil blocks_roots_inv
   in a way consistent with the recursion in size_of
 *)
Definition blocks_all_inv_def:
  blocks_all_inv blocks seen =
  ∀ts tag l.
    sptree$lookup ts blocks = SOME (Block ts tag l) ⇒
    blocks_roots_inv (delete ts blocks) (insert ts () seen) l
End

Definition del_ptr_def[simp]:
  del_ptr (RefAddr p) refs = delete p refs
∧ del_ptr  _          refs = refs
End

Definition del_blk_def[simp]:
  del_blk (BlockAddr ts) blocks = delete ts blocks
∧ del_blk  _             blocks = blocks
End

Theorem next_del:
  ∀refs blocks v x .
       (next refs blocks)^* v x
     ⇒ (∃y. (next refs blocks) v y ∧
           (next (del_ptr v refs) (del_blk v blocks))^* y x) ∨ x = v
Proof
  strip_tac \\ strip_tac
  \\ ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 \\ rw[]
  >~[‘(next refs blocks)^* v v’]
  >- (DISJ1_TAC \\ asm_exists_tac \\ simp[])
  >- (Cases_on ‘x = v’ \\ gs[]
      >- (DISJ1_TAC \\ qexists_tac ‘x'’ \\ simp[])
      \\ Cases_on ‘x' = v’ \\ gs[]
      \\ asm_exists_tac \\ simp[]
      \\ Cases_on ‘x = x'’ \\ gs[]
      \\ ‘next (del_ptr v refs) (del_blk v blocks) x x'’ by
         (Cases_on ‘x’ \\ Cases_on ‘v’
          \\ gs[next_def,block_to_addrs_def]
          \\ gs[lookup_delete,ptr_to_addrs_def])
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES2)
      \\ DISJ2_TAC \\ metis_tac [])
QED

Theorem next_insert:
  ∀refs blocks x y.
    (next refs blocks)^* x y ⇒
    ∀refs' blocks'.
      subspt refs refs' ∧
      subspt blocks blocks' ⇒
      (next refs' blocks')^* x y
Proof
  strip_tac \\ strip_tac
  \\ ho_match_mp_tac RTC_strongind \\ rw[]
  \\ first_x_assum drule_all \\ rw[]
  \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
  \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
  \\ Cases_on ‘x’
  \\ gs[next_def,block_to_addrs_def,ptr_to_addrs_def]
  \\ gs[subspt_lookup]
  >-(cases_on ‘lookup n blocks’ \\ gs[]
     \\ first_assum drule \\ disch_then (simp o single))
  >-(cases_on ‘lookup n refs’ \\ gs[]
     \\ first_assum drule \\ disch_then (simp o single))
QED

Theorem reachable_v_del_ptr:
  ∀refs blocks r l.
    lookup r refs = SOME (ValueArray l) ⇒
    reachable_v refs blocks {RefAddr r} =
     reachable_v (delete r refs) blocks (to_addrs l) ∪ {RefAddr r}
Proof
  rw[reachable_v_def,FUN_EQ_THM] \\ EQ_TAC \\ rw[] \\ simp[]
  >- (drule next_del \\ rw[next_def,ptr_to_addrs_def])
  >- (drule next_insert \\ disch_then (qspecl_then [‘refs’,‘blocks’] mp_tac)
      \\ impl_tac >- gs[subspt_delete]
      \\ rw[]
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
      \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
      \\  simp [next_def,ptr_to_addrs_def])
QED

Theorem reachable_v_del_blk:
  ∀refs blocks ts tag l.
    lookup ts blocks = SOME (Block ts tag l) ⇒
    reachable_v refs blocks {BlockAddr ts} =
     reachable_v refs (delete ts blocks) (to_addrs l) ∪ {BlockAddr ts}
Proof
  rw[reachable_v_def,FUN_EQ_THM] \\ EQ_TAC \\ rw[] \\ simp[]
  >- (drule next_del \\ rw[next_def,block_to_addrs_def])
  >- (drule next_insert \\ disch_then (qspecl_then [‘refs’,‘blocks’] mp_tac)
      \\ impl_tac >- gs[subspt_delete]
      \\ rw[]
      \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
      \\ DISJ2_TAC \\ first_x_assum (irule_at Any)
      \\ simp [next_def,block_to_addrs_def])
QED

Theorem size_of_addr_del_aux:
  ∀lims refs blocks v l.
    size_of_addr lims (del_ptr v refs) (del_blk v blocks) v = 0
Proof
  rw[] \\ Cases_on ‘v’ \\ rw[size_of_addr_def,lookup_delete]
QED

Theorem size_of_addr_del:
  ∀lims refs blocks v l.
    v ∉ l ⇒
    ∑ (size_of_addr lims refs blocks) l =
    ∑ (size_of_addr lims (del_ptr v refs) (del_blk v blocks)) l
Proof
  rw[] \\ irule SUM_IMAGE_CONG \\ rw[]
  \\ Cases_on ‘x’ \\ rw[size_of_addr_def]
  \\ Cases_on ‘v’ \\ rw[lookup_delete]
  \\ gs[]
QED

Theorem size_of_addr_del_in:
  ∀lims refs blocks v l.
    v ∈ l ∧ FINITE l ⇒
    ∑ (size_of_addr lims refs blocks) l =
    ∑ (size_of_addr lims (del_ptr v refs) (del_blk v blocks)) l +
    size_of_addr lims refs blocks v
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
  \\ simp [SUM_IMAGE_THM,Abbr‘vv’,Abbr‘ff’,Abbr‘ff'’,size_of_addr_del_aux]
  \\ irule size_of_addr_del
  \\ simp[Abbr‘ll’]
QED

Triviality FINITE_reachable_v_0:
  ∀refs blocks roots.
    FINITE roots ⇒
    FINITE (reachable_v refs blocks roots)
Proof
  rw[]
  \\ qspec_then ‘to_addrs (blocks_to_vs (sptree$toList blocks)) ∪
                 to_addrs (ref_to_vs (sptree$toList refs))  ∪
                 roots’
                mp_tac SUBSET_FINITE
  \\ impl_tac >- rw[FINITE_to_addrs]
  \\ disch_then ho_match_mp_tac
  \\ rw [SUBSET_DEF,IN_DEF,reachable_v_def]
  \\ gs[Once RTC_CASES2]
  \\ Cases_on ‘u’
  >- (gs[next_def,block_to_addrs_def]
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

Theorem size_of_aux_size_of:
  ∀lims vs refs seen n refs0 seen0.
    size_of lims vs refs seen = (n,refs0,seen0) ⇒
    ∀blocks.
      blocks_roots_inv blocks seen vs   ∧
      blocks_refs_inv  blocks seen refs ∧
      blocks_all_inv   blocks seen      ⇒
        aux_size_of lims refs blocks vs = n
Proof
  ho_match_mp_tac size_of_ind \\ rw[]
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v_def] \\ EVAL_TAC)
     (* TODO *)
  >- (gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (first_assum o mp_then Any mp_tac)
      (* tail invariants *)
      \\ impl_tac \\ rw[]
      >- (last_x_assum kall_tac
          \\ gs[blocks_roots_inv_def,FORALL_AND_THM]
          \\ metis_tac [])
      \\ first_x_assum (qspec_then ‘difference blocks seen1’ mp_tac)
      \\ impl_tac \\ rw[]
      (* head invariants *)
      >- (gs[blocks_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks_refs_inv_def] \\ rw[]
          \\ ‘subspt refs1 refs’ by metis_tac [size_of_refs_subspt]
          \\ gs[subspt_lookup] \\ first_x_assum drule
          \\ disch_then (first_x_assum o C (mp_then Any assume_tac))
          \\ gs[blocks_roots_inv_def,FORALL_AND_THM,lookup_difference]
          \\ rw[] \\ gs[]
          \\ first_x_assum irule \\ simp[]
          \\ ‘subspt seen seen1’ by metis_tac [size_of_seen_pres]
          \\ CCONTR_TAC
          \\ Cases_on ‘lookup ts seen’ \\ gs[]
          \\ gs[subspt_lookup])
      >- (gs[blocks_all_inv_def] \\ rw[]
          \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘l’] mp_tac)
          \\ impl_tac >- gs[lookup_difference]
          \\ gs[blocks_roots_inv_def,FORALL_AND_THM
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
      \\ cheat)
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v_def] \\ EVAL_TAC)
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v_def]
      \\ cases_on ‘small_num lims.arch_64_bit i’
      \\ gs[flat_measure_def] \\ EVAL_TAC)
  >- (gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v_def] \\ EVAL_TAC)
  >- (cases_on ‘lookup r refs’ \\ gs[] \\ TRY (cases_on ‘x’)
      >~ [‘lookup _ _ = SOME (ValueArray _)’]
      >- (first_x_assum (qspec_then ‘l’ assume_tac) \\ gs[size_of_def]
          \\ pairarg_tac \\ gs[] \\ rveq
          \\ first_x_assum (qspec_then ‘blocks’ mp_tac)
          \\ impl_tac \\ rw[]
          >- metis_tac [blocks_refs_inv_def]
          >- (gs[blocks_refs_inv_def] \\ rw[]
              \\ first_x_assum irule \\ qexists_tac ‘p’
              \\ gs[lookup_delete])
          >- (gs[aux_size_of_def,flat_measure_def,to_addrs_def]
              \\ drule reachable_v_del_ptr
              \\ disch_then (qspec_then ‘blocks’ (simp o single))
              \\ qmatch_goalsub_abbrev_tac ‘∑ ff (nxt UNION rr)’
              \\ qspecl_then [‘ff’,‘nxt’,‘rr’] mp_tac SUM_IMAGE_UNION
              \\ impl_tac
              >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v_0,FINITE_to_addrs]
              \\ disch_then (simp o single)
              \\ qunabbrev_tac ‘rr’
              \\ Cases_on ‘RefAddr r ∈ nxt’
              >- (‘nxt ∩ {RefAddr r} = {RefAddr r}’ by
                    (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
                     \\ EQ_TAC \\ metis_tac [])
                  \\ simp[Abbr‘ff’] \\ drule size_of_addr_del_in
                  \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
                  \\ impl_tac
                  >- simp[Abbr‘nxt’,FINITE_reachable_v_0,FINITE_to_addrs]
                  \\ disch_then (simp o single)
                  \\ simp[size_of_addr_def])
              >- (‘nxt ∩ {RefAddr r} = ∅’ by
                    (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM])
                  \\ simp[Abbr‘ff’,SUM_IMAGE_THM]
                  \\ drule size_of_addr_del
                  \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
                  \\ disch_then (simp o single)
                  \\ simp[size_of_addr_def])))
      \\ gs[aux_size_of_def,size_of_def,to_addrs_def,reachable_v_def,flat_measure_def]
      \\ qmatch_goalsub_abbrev_tac ‘∑ _ nxt’
      \\ ‘nxt = {RefAddr r}’ suffices_by simp[SUM_IMAGE_SING,size_of_addr_def]
      \\ UNABBREV_ALL_TAC \\ simp[FUN_EQ_THM]
      \\ rw[] \\ EQ_TAC \\ rw[]
      \\ drule (RTC_CASES1  |> SPEC_ALL  |> EQ_IMP_RULE  |> fst)
      \\ rw[] \\ gs[next_def,ptr_to_addrs_def])
  >- gs[size_of_def,aux_size_of_def,to_addrs_def,flat_measure_def,reachable_v_def,SUM_IMAGE_THM]
  >- (Cases_on ‘lookup ts seen’ \\ gs[]
      >~[‘lookup ts seen = SOME _’]
      >- (gs[size_of_def,blocks_roots_inv_def] \\ rveq
          \\ first_x_assum (qspec_then ‘ts’ mp_tac)
          \\ rw [aux_size_of_def,to_addrs_def,flat_measure_def]
          \\ qmatch_goalsub_abbrev_tac ‘∑ _ ll’
          \\ ‘ll = {BlockAddr ts}’ by
            (qunabbrev_tac ‘ll’ \\ rw[reachable_v_def,FUN_EQ_THM]
             \\ EQ_TAC \\ rw[] \\ gs[Once RTC_CASES1,next_def,block_to_addrs_def])
          \\ simp[SUM_IMAGE_SING,size_of_addr_def])
      \\ gs[size_of_def] \\ rpt (pairarg_tac \\ gs[]) \\ rveq
      \\ first_x_assum (qspec_then ‘delete ts blocks’ mp_tac)
      \\ impl_tac \\ rw[]
      >- (gs[blocks_all_inv_def] \\ first_x_assum irule
          \\ qexists_tac ‘tag’ \\ gs [blocks_roots_inv_def])
      >- (gs[blocks_refs_inv_def] \\ rw[] \\ first_x_assum drule
          \\ rw[blocks_roots_inv_def,lookup_delete,lookup_insert]
          >- (CCONTR_TAC \\ gs[])
          >- (CCONTR_TAC \\ gs[])
          >- metis_tac [])
      >- (gs[blocks_all_inv_def] \\ rw[lookup_delete]
          \\ first_x_assum drule
          \\ rw[blocks_roots_inv_def,lookup_delete,lookup_insert]
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
      \\ gs[blocks_roots_inv_def]
      \\ first_x_assum (qspecl_then [‘ts’,‘tag’,‘v20::v21’] assume_tac)
      \\ gs [] \\ rw[aux_size_of_def,flat_measure_def,to_addrs_def]
      \\ drule reachable_v_del_blk
      \\ disch_then (qspec_then ‘ref’ (simp o single))
      \\ qmatch_goalsub_abbrev_tac ‘∑ ff (nxt UNION rr)’
      \\ qspecl_then [‘ff’,‘nxt’,‘rr’] mp_tac SUM_IMAGE_UNION
      \\ impl_tac
      >- simp[Abbr‘nxt’,Abbr‘rr’,FINITE_reachable_v_0,FINITE_to_addrs]
      \\ disch_then (simp o single)
      \\ qunabbrev_tac ‘rr’
      \\ Cases_on ‘BlockAddr ts ∈ nxt’
      >- (‘nxt ∩ {BlockAddr ts} = {BlockAddr ts}’ by
            (rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
             \\ EQ_TAC \\ metis_tac [])
          \\ simp[Abbr‘ff’] \\ drule size_of_addr_del_in
          \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
          \\ impl_tac
          >- simp[Abbr‘nxt’,FINITE_reachable_v_0,FINITE_to_addrs]
          \\ disch_then (simp o single)
          \\ simp[size_of_addr_def])
      >- (‘nxt ∩ {BlockAddr ts} = ∅’ by rw[INTER_DEF,DELETE_DEF,FUN_EQ_THM]
          \\ simp[Abbr‘ff’,SUM_IMAGE_THM]
          \\ drule size_of_addr_del
          \\ disch_then (qspecl_then [‘lims’,‘refs’,‘blocks’] mp_tac)
          \\ disch_then (simp o single)
          \\ simp[size_of_addr_def]))
QED



val _ = export_theory();
