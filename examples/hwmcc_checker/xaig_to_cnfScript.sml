(*
  Mapping eXtended And-Inverter Graphs into CNF
*)
Theory xaig_to_cnf
Ancestors
  misc mlstring aig xaig cnf aig_to_cnf
Libs
  preamble

(*----------------------------------------------------------------------*
   generic helpers
 *----------------------------------------------------------------------*)

Theorem EVERY_EQ_EVERY[local]:
  EVERY (λx. P x = Q x) xs ⇒ (EVERY P xs = EVERY Q xs)
Proof
  Induct_on ‘xs’ \\ fs []
QED

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

Theorem new_live_pres[local]:
  ∀xs live name.
    FLOOKUP live name = SOME () ⇒
    FLOOKUP (new_live xs live) name = SOME ()
Proof
  Induct \\ simp [new_live_def, FORALL_PROD]
  \\ Cases \\ simp [new_live_def, FORALL_PROD]
  \\ rw [] \\ rw [FLOOKUP_SIMP]
QED

(* the literals that a gate depends on *)

Definition gty_lits_def[simp]:
  gty_lits (And ts) = ts ∧
  gty_lits (Xor t1 t2) = [t1; t2] ∧
  gty_lits (Ite t1 t2 t3) = [t1; t2; t3]
End

Theorem xeval_gty_cong:
  ∀gt.
    EVERY (λt. xeval_lit ss xs t ⇔ xeval_lit ss' ys t) (gty_lits gt) ⇒
    (xeval_gty ss xs gt ⇔ xeval_gty ss' ys gt)
Proof
  Cases \\ simp [xeval_lit_def] \\ strip_tac \\ gvs []
  \\ irule EVERY_EQ_EVERY \\ fs []
QED

Theorem xeval_gate_nil[simp]:
  ¬xeval_gate ss [] n
Proof
  simp [xeval_lit_def]
QED

Theorem xeval_gate_cons:
  xeval_gate ss ((n,gt)::rest) m =
  if n = m then xeval_gty ss rest gt else xeval_gate ss rest m
Proof
  simp [xeval_lit_def]
QED

(*----------------------------------------------------------------------*
   pruning
 *----------------------------------------------------------------------*)

Definition xprune_def:
  xprune ([]:('a,'i,'l) xaig) (live :'a |-> unit) = [] ∧
  xprune ((m,gt)::xs) live =
    case FLOOKUP live m of
    | NONE => xprune xs live
    | _ =>
        let live' = live \\ m in
          (m,gt) :: xprune xs (new_live (gty_lits gt) live')
End

Definition xprune_rev_def:
  xprune_rev ([]:('a,'i,'l) xaig) (live :'a |-> unit) acc = acc ∧
  xprune_rev ((m,gt)::xs) live acc =
    case FLOOKUP live m of
    | NONE => xprune_rev xs live acc
    | _ =>
        let live' = live \\ m in
          xprune_rev xs (new_live (gty_lits gt) live') ((m,gt) :: acc)
End

Definition xprune_for_def:
  xprune_for name xaig = xprune_rev xaig (fmap_update FEMPTY name ()) []
End

Theorem xprune_rev_thm:
  ∀xs live acc. xprune_rev xs live acc = REVERSE (xprune xs live) ++ acc
Proof
  Induct \\ fs [xprune_rev_def,xprune_def] \\ rw []
  \\ Cases_on ‘h’ \\ fs [xprune_rev_def,xprune_def] \\ rw []
  \\ CASE_TAC \\ fs []
QED

Theorem xeval_gate_xprune:
  ∀xaig name live x.
    FLOOKUP live name = SOME x ⇒
    xeval_gate (is,ls) xaig name =
    xeval_gate (is,ls) (xprune xaig live) name
Proof
  Induct >- simp [xprune_def]
  \\ PairCases
  \\ rw [xprune_def, xeval_gate_cons]
  >-
   (irule xeval_gty_cong
    \\ simp [EVERY_MEM]
    \\ Cases \\ Cases_on ‘q’
    \\ simp [xeval_lit_def]
    \\ rename [‘Gate aa’]
    \\ strip_tac
    \\ first_x_assum $
         qspecl_then [‘aa’,‘new_live (gty_lits h1) (live \\ h0)’,‘()’] mp_tac
    \\ reverse impl_tac >- simp []
    \\ irule new_live_thm
    \\ pop_assum $ irule_at Any)
  \\ CASE_TAC \\ simp [xeval_gate_cons]
  \\ last_x_assum irule
  \\ irule_at Any new_live_pres
  \\ fs [FLOOKUP_DEF, DOMSUB_FAPPLY_THM]
QED

Definition xeval_gate'_def:
  xeval_gate' ss ([]:('a,'i,'l) xaig) = F ∧
  xeval_gate' ss ((x,gt)::rest) = xeval_gate ss ((x,gt)::rest) x
End

Theorem xeval_gate'_same:
  (~NULL xaig ⇒ FST (HD xaig) = name) ⇒
  (xeval_gate (is,ls) xaig name ⇔ xeval_gate' (is,ls) xaig)
Proof
  Cases_on ‘xaig’ \\ fs [xeval_gate'_def, xeval_lit_def]
  \\ PairCases_on ‘h’ \\ fs [xeval_gate'_def, xeval_lit_def]
QED

Theorem xeval_gate'_xprune:
  xeval_gate' (is,ls) (xprune xaig (FEMPTY |+ (name,()))) =
  xeval_gate (is,ls) xaig name
Proof
  simp [Once EQ_SYM_EQ]
  \\ irule EQ_TRANS
  \\ irule_at Any xeval_gate_xprune
  \\ qrefinel [‘_’,‘FEMPTY⟨name ↦ ()⟩’]
  \\ simp [FLOOKUP_SIMP]
  \\ irule xeval_gate'_same
  \\ Induct_on ‘xaig’ \\ fs [xprune_def]
  \\ Cases \\ fs [xprune_def, FLOOKUP_SIMP]
  \\ IF_CASES_TAC \\ fs []
QED

(*----------------------------------------------------------------------*
   renaming
 *----------------------------------------------------------------------*)

Definition xrename_lit_def:
  xrename_lit ((x,b):('a,'i,'l) aig$lit) next im lm nm =
    case x of
    | Gate n =>
        (case FLOOKUP nm n of
         | NONE   => ((Base Ff,b):(num,num,num) aig$lit, next:num, im, lm)
         | SOME t => ((Gate t,b), next, im, lm))
    | Base (Input i) =>
        (case FLOOKUP im i of
         | NONE   => ((Base (Input next),b), next+1, fmap_update im i next, lm)
         | SOME t => ((Base (Input t),b), next, im, lm))
    | Base (Latch l) =>
        (case FLOOKUP lm l of
         | NONE   => ((Base (Latch next),b), next+1, im, fmap_update lm l next)
         | SOME t => ((Base (Latch t),b), next, im, lm))
    | Base Ff => ((Base Ff,b), next, im, lm)
End

Definition xrename_lits_def:
  xrename_lits ([]:('a,'i,'l) aig$lit list) next im lm nm =
    ([]:(num,num,num) aig$lit list,next,im,lm) ∧
  xrename_lits (t::ts) next im lm nm =
    let (t1,next,im,lm) = xrename_lit t next im lm nm in
    let (ts1,next,im,lm) = xrename_lits ts next im lm nm in
      (t1::ts1,next,im,lm)
End

Definition xrename_gty_def:
  xrename_gty (And ts) next im lm nm =
    (let (ts1,next,im,lm) = xrename_lits ts next im lm nm in
       (And ts1,next,im,lm)) ∧
  xrename_gty (Xor t1 t2) next im lm nm =
    (let (u1,next,im,lm) = xrename_lit t1 next im lm nm in
     let (u2,next,im,lm) = xrename_lit t2 next im lm nm in
       (Xor u1 u2,next,im,lm)) ∧
  xrename_gty (Ite t1 t2 t3) next im lm nm =
    (let (u1,next,im,lm) = xrename_lit t1 next im lm nm in
     let (u2,next,im,lm) = xrename_lit t2 next im lm nm in
     let (u3,next,im,lm) = xrename_lit t3 next im lm nm in
       (Ite u1 u2 u3,next,im,lm))
End

Definition xaig_rename_def:
  xaig_rename ([]:('a,'i,'l) xaig) =
    ([]:(num,num,num) xaig,1n,FEMPTY,FEMPTY,FEMPTY) ∧
  xaig_rename ((m,gt)::xs) =
    let (res,next,im,lm,nm) = xaig_rename xs in
    let (gt1,next,im,lm) = xrename_gty gt next im lm nm in
      ((next,gt1)::res, next+1, im, lm, fmap_update nm m next)
End

Definition xaig_rename_rev_def:
  xaig_rename_rev ([]:('a,'i,'l) xaig) acc next im lm nm =
    (acc,next,im,lm,nm) ∧
  xaig_rename_rev ((m,gt)::xs) acc next im lm nm =
    let (gt1,next,im,lm) = xrename_gty gt next im lm nm in
      xaig_rename_rev xs ((next,gt1)::acc) (next+1) im lm (fmap_update nm m next)
End

Theorem xaig_rename_rev_append:
  ∀xs ys acc next im lm nm.
    xaig_rename_rev (xs ++ ys) acc next im lm nm =
      let (acc,next,im,lm,nm) = xaig_rename_rev xs acc next im lm nm in
        xaig_rename_rev ys acc next im lm nm
Proof
  Induct \\ fs [xaig_rename_rev_def]
  \\ PairCases \\ fs [xaig_rename_rev_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem xaig_rename_rev_thm:
  ∀xs. xaig_rename_rev (REVERSE xs) [] 1n FEMPTY FEMPTY FEMPTY = xaig_rename xs
Proof
  Induct \\ fs [xaig_rename_rev_def, xaig_rename_def]
  \\ Cases \\ fs [xaig_rename_rev_def, xaig_rename_def]
  \\ fs [xaig_rename_rev_append]
  \\ rw [] \\ rpt (pairarg_tac \\ fs [])
  \\ fs [xaig_rename_rev_def]
QED

Definition xhas_var_def:
  xhas_var v ([]:('a,'i,'l) xaig) = F ∧
  xhas_var v ((n,gt)::rest) =
    (xhas_var v rest ∨ ∃b. MEM (Base v,b) (gty_lits gt))
End

Definition xclosed_def:
  xclosed ([]:('a,'i,'l) xaig) = T ∧
  xclosed ((n,gt)::rest) =
    (xclosed rest ∧
     ∀m b. MEM (Gate m,b) (gty_lits gt) ⇒ ALOOKUP rest m ≠ NONE)
End

Theorem xnot_eval_gate:
  ∀xaig a. ~MEM a (MAP FST xaig) ⇒ ¬xeval_gate (is,ls) xaig a
Proof
  Induct \\ fs [xeval_gate_cons, FORALL_PROD]
QED

(* A property of the renamed variables that survives extensions of the
   renaming maps im and lm. *)

Definition wrt_ext_def:
  wrt_ext im lm P ⇔
    ∀ix lx.
      INJ (FAPPLY (im ⊌ ix)) (FDOM (im ⊌ ix)) UNIV ∧
      INJ (FAPPLY (lm ⊌ lx)) (FDOM (lm ⊌ lx)) UNIV
      ⇒
      P (im ⊌ ix) (lm ⊌ lx)
End

Theorem wrt_ext_mono:
  wrt_ext im lm P ∧ im SUBMAP im' ∧ lm SUBMAP lm' ⇒ wrt_ext im' lm' P
Proof
  rw [wrt_ext_def]
  \\ first_x_assum $ qspecl_then [‘im' ⊌ ix’,‘lm' ⊌ lx’] mp_tac
  \\ imp_res_tac FUNION_SUBMAP_lemma
  \\ asm_rewrite_tac [FUNION_ASSOC, FDOM_FUNION, UNION_ASSOC]
QED

(* Every gate of the original xaig has been given a name by nm, and
   evaluating that gate in the renamed xaig gives the same result. *)

Definition gates_ok_def:
  gates_ok is ls xaig res nm im lm ⇔
    ∀n. ALOOKUP xaig n ≠ NONE ⇒
        ∃t. FLOOKUP nm n = SOME t ∧
            wrt_ext im lm
              (λi l. xeval_gate (is,ls) xaig n =
                     xeval_gate (aig_read is i, aig_read ls l) res t)
End

(* The invariant that renaming maintains: the names handed out so far are
   distinct, are all below next, and none of them is 0 (CNF variable 0 is
   reserved for the constant false, see below). *)

Definition rename_inv_def:
  rename_inv is ls xaig res nm next im lm ⇔
    0 < next ∧
    (∀n. n ∈ FRANGE im ∪ FRANGE lm ∪ set (MAP FST res) ⇒ 0 < n ∧ n < next) ∧
    DISJOINT3 (FRANGE im) (FRANGE lm) (set (MAP FST res)) ∧
    INJ (FAPPLY im) (FDOM im) UNIV ∧
    INJ (FAPPLY lm) (FDOM lm) UNIV ∧
    FDOM nm = set (MAP FST xaig) ∧
    FRANGE nm ⊆ set (MAP FST res) ∧
    gates_ok is ls xaig res nm im lm
End

Theorem rename_inv_bound[local]:
  rename_inv is ls xaig res nm next im lm ⇒
  ∀n. next ≤ n ⇒ n ∉ FRANGE im ∧ n ∉ FRANGE lm ∧ ~MEM n (MAP FST res)
Proof
  rw [rename_inv_def] \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ fs []
QED

Theorem gates_ok_mono:
  gates_ok is ls xaig res nm im lm ∧ im SUBMAP im' ∧ lm SUBMAP lm' ⇒
  gates_ok is ls xaig res nm im' lm'
Proof
  rw [gates_ok_def] \\ first_x_assum drule \\ strip_tac \\ simp []
  \\ irule wrt_ext_mono \\ first_x_assum $ irule_at Any \\ simp []
QED

Theorem rename_inv_fresh_input[local]:
  rename_inv is ls xaig res nm next im lm ∧ FLOOKUP im i = NONE ⇒
  rename_inv is ls xaig res nm (next+1) im⟨i ↦ next⟩ lm
Proof
  strip_tac
  \\ drule rename_inv_bound \\ strip_tac
  \\ ‘i ∉ FDOM im’ by gvs [FLOOKUP_DEF]
  \\ ‘im \\ i = im’ by simp [DOMSUB_NOT_IN_DOM]
  \\ qpat_x_assum ‘rename_inv _ _ _ _ _ _ _ _’ mp_tac
  \\ simp [rename_inv_def] \\ strip_tac
  \\ ‘INJ (FAPPLY im⟨i ↦ next⟩) (i INSERT FDOM im) UNIV ∧
      (∀n. next + 1 ≤ n ⇒ n ∉ FRANGE (im \\ i)) ∧
      DISJOINT3 (next INSERT FRANGE (im \\ i)) (FRANGE lm) (set (MAP FST res))’ by
    (irule IMP_DISJOINT3 \\ fs [] \\ once_rewrite_tac [DISJOINT3_COMM_12] \\ fs [])
  \\ rpt conj_tac
  >- (rw [] \\ res_tac \\ fs [])
  >- gvs []
  >- fs []
  \\ irule gates_ok_mono \\ first_assum $ irule_at Any \\ fs [TO_FLOOKUP]
QED

Theorem rename_inv_fresh_latch[local]:
  rename_inv is ls xaig res nm next im lm ∧ FLOOKUP lm l = NONE ⇒
  rename_inv is ls xaig res nm (next+1) im lm⟨l ↦ next⟩
Proof
  strip_tac
  \\ drule rename_inv_bound \\ strip_tac
  \\ ‘l ∉ FDOM lm’ by gvs [FLOOKUP_DEF]
  \\ ‘lm \\ l = lm’ by simp [DOMSUB_NOT_IN_DOM]
  \\ qpat_x_assum ‘rename_inv _ _ _ _ _ _ _ _’ mp_tac
  \\ simp [rename_inv_def] \\ strip_tac
  \\ ‘INJ (FAPPLY lm⟨l ↦ next⟩) (l INSERT FDOM lm) UNIV ∧
      (∀n. next + 1 ≤ n ⇒ n ∉ FRANGE (lm \\ l)) ∧
      DISJOINT3 (next INSERT FRANGE (lm \\ l)) (FRANGE im) (set (MAP FST res))’ by
    (irule IMP_DISJOINT3 \\ fs [] \\ once_rewrite_tac [DISJOINT3_COMM_12] \\ fs [])
  \\ rpt conj_tac
  >- (rw [] \\ res_tac \\ fs [])
  >- (once_rewrite_tac [DISJOINT3_COMM_12] \\ gvs [])
  >- fs []
  \\ irule gates_ok_mono \\ first_assum $ irule_at Any \\ fs [TO_FLOOKUP]
QED

Theorem xrename_lit_thm:
  ∀t next_1 im_1 lm_1 t_1 next_2 im_2 lm_2.
    xrename_lit t next_1 im_1 lm_1 nm = (t_1,next_2,im_2,lm_2) ∧
    rename_inv is ls xaig res nm next_1 im_1 lm_1
    ⇒
    rename_inv is ls xaig res nm next_2 im_2 lm_2 ∧
    im_1 SUBMAP im_2 ∧ lm_1 SUBMAP lm_2 ∧ next_1 ≤ next_2 ∧
    (∀l b. t = (Base (Latch l),b) ⇒ l ∈ FDOM lm_2) ∧
    (∀i b. t = (Base (Input i),b) ⇒ i ∈ FDOM im_2) ∧
    (∀l b. t_1 = (Base (Latch l),b) ⇒ l ∈ FRANGE lm_2) ∧
    (∀i b. t_1 = (Base (Input i),b) ⇒ i ∈ FRANGE im_2) ∧
    (∀m b. t_1 = (Gate m,b) ⇒ m ∈ FRANGE nm) ∧
    wrt_ext im_2 lm_2
      (λi l. xeval_lit (is,ls) xaig t =
             xeval_lit (aig_read is i, aig_read ls l) res t_1)
Proof
  PairCases \\ gvs [xrename_lit_def, AllCaseEqs()]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  (* gate that is not in the xaig *)
  >-
   (gvs [wrt_ext_def, xeval_lit_def, rename_inv_def, FLOOKUP_DEF] \\ rw []
    \\ imp_res_tac xnot_eval_gate \\ fs [])
  (* gate that has already been renamed *)
  >-
   (conj_asm1_tac >- gvs [FRANGE_FLOOKUP, SF SFY_ss]
    \\ gvs [rename_inv_def, gates_ok_def]
    \\ first_x_assum $ qspec_then ‘n’ mp_tac
    \\ impl_tac >- gvs [ALOOKUP_NONE, FLOOKUP_DEF, EXTENSION]
    \\ strip_tac \\ gvs []
    \\ gvs [wrt_ext_def, xeval_lit_def]
    \\ rw [] \\ res_tac \\ simp [])
  (* the constant false *)
  >- simp [wrt_ext_def, xeval_lit_def]
  (* a fresh input *)
  >-
   (conj_tac >- (irule rename_inv_fresh_input \\ fs [])
    \\ conj_tac >- gvs [FLOOKUP_DEF]
    \\ simp [wrt_ext_def, xeval_lit_def] \\ rpt strip_tac
    \\ ‘aig_read is (im_1⟨i ↦ next_1⟩ ⊌ ix) next_1 = is i’ by
         (irule aig_read_thm \\ simp [FLOOKUP_SIMP])
    \\ simp [])
  (* an input that has already been renamed *)
  >-
   (conj_tac >- gvs [FLOOKUP_DEF]
    \\ conj_tac >- gvs [FRANGE_FLOOKUP, SF SFY_ss]
    \\ simp [wrt_ext_def, xeval_lit_def] \\ rpt strip_tac
    \\ ‘aig_read is (im_1 ⊌ ix) t = is i’ by (irule aig_read_thm \\ simp [])
    \\ simp [])
  (* a fresh latch *)
  >-
   (conj_tac >- (irule rename_inv_fresh_latch \\ fs [])
    \\ conj_tac >- gvs [FLOOKUP_DEF]
    \\ simp [wrt_ext_def, xeval_lit_def] \\ rpt strip_tac
    \\ ‘aig_read ls (lm_1⟨l ↦ next_1⟩ ⊌ lx) next_1 = ls l’ by
         (irule aig_read_thm \\ simp [FLOOKUP_SIMP])
    \\ simp [])
  (* a latch that has already been renamed *)
  \\ conj_tac >- gvs [FLOOKUP_DEF]
  \\ conj_tac >- gvs [FRANGE_FLOOKUP, SF SFY_ss]
  \\ simp [wrt_ext_def, xeval_lit_def] \\ rpt strip_tac
  \\ ‘aig_read ls (lm_1 ⊌ lx) t = ls l’ by (irule aig_read_thm \\ simp [])
  \\ simp []
QED

Theorem xrename_lits_thm:
  ∀ts next_1 im_1 lm_1 ts_1 next_2 im_2 lm_2.
    xrename_lits ts next_1 im_1 lm_1 nm = (ts_1,next_2,im_2,lm_2) ∧
    rename_inv is ls xaig res nm next_1 im_1 lm_1
    ⇒
    rename_inv is ls xaig res nm next_2 im_2 lm_2 ∧
    im_1 SUBMAP im_2 ∧ lm_1 SUBMAP lm_2 ∧ next_1 ≤ next_2 ∧
    (∀l b. MEM (Base (Latch l),b) ts ⇒ l ∈ FDOM lm_2) ∧
    (∀i b. MEM (Base (Input i),b) ts ⇒ i ∈ FDOM im_2) ∧
    (∀l b. MEM (Base (Latch l),b) ts_1 ⇒ l ∈ FRANGE lm_2) ∧
    (∀i b. MEM (Base (Input i),b) ts_1 ⇒ i ∈ FRANGE im_2) ∧
    (∀m b. MEM (Gate m,b) ts_1 ⇒ m ∈ FRANGE nm) ∧
    wrt_ext im_2 lm_2
      (λi l. EVERY (xeval_lit (is,ls) xaig) ts =
             EVERY (xeval_lit (aig_read is i, aig_read ls l) res) ts_1)
Proof
  Induct >- (fs [xrename_lits_def] \\ rw [] \\ simp [wrt_ext_def])
  \\ rpt gen_tac \\ simp [xrename_lits_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs []
  \\ drule_all xrename_lit_thm \\ strip_tac
  \\ last_x_assum drule_all \\ strip_tac
  \\ ‘im_1 SUBMAP im' ∧ lm_1 SUBMAP lm'’ by metis_tac [SUBMAP_TRANS]
  \\ simp []
  \\ ‘wrt_ext im' lm'
        (λi l. xeval_lit (is,ls) xaig h ⇔
               xeval_lit (aig_read is i,aig_read ls l) res t1)’ by
       (irule wrt_ext_mono
        \\ qpat_x_assum ‘wrt_ext im lm _’ $ irule_at Any \\ simp [])
  \\ rpt conj_tac
  >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  >- (rw [] \\ res_tac)
  \\ fs [wrt_ext_def] \\ rw [] \\ res_tac \\ simp []
QED

Theorem xrename_gty_thm:
  ∀gt next_1 im_1 lm_1 gt_1 next_2 im_2 lm_2.
    xrename_gty gt next_1 im_1 lm_1 nm = (gt_1,next_2,im_2,lm_2) ∧
    rename_inv is ls xaig res nm next_1 im_1 lm_1
    ⇒
    rename_inv is ls xaig res nm next_2 im_2 lm_2 ∧
    im_1 SUBMAP im_2 ∧ lm_1 SUBMAP lm_2 ∧ next_1 ≤ next_2 ∧
    (∀l b. MEM (Base (Latch l),b) (gty_lits gt) ⇒ l ∈ FDOM lm_2) ∧
    (∀i b. MEM (Base (Input i),b) (gty_lits gt) ⇒ i ∈ FDOM im_2) ∧
    (∀l b. MEM (Base (Latch l),b) (gty_lits gt_1) ⇒ l ∈ FRANGE lm_2) ∧
    (∀i b. MEM (Base (Input i),b) (gty_lits gt_1) ⇒ i ∈ FRANGE im_2) ∧
    (∀m b. MEM (Gate m,b) (gty_lits gt_1) ⇒ m ∈ FRANGE nm) ∧
    wrt_ext im_2 lm_2
      (λi l. xeval_gty (is,ls) xaig gt =
             xeval_gty (aig_read is i, aig_read ls l) res gt_1)
Proof
  Cases \\ rpt gen_tac \\ simp [xrename_gty_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs [xeval_lit_def]
  (* multi-input and gates *)
  >- (drule_all xrename_lits_thm \\ strip_tac \\ fs [SF ETA_ss]
      \\ rw [] \\ res_tac)
  (* xor gates *)
  >-
   (qpat_x_assum ‘xrename_lit p _ _ _ _ = _’ assume_tac
    \\ drule_all xrename_lit_thm \\ strip_tac
    \\ qpat_x_assum ‘xrename_lit p0 _ _ _ _ = _’ assume_tac
    \\ drule_all xrename_lit_thm \\ strip_tac
    \\ ‘im_1 SUBMAP im' ∧ lm_1 SUBMAP lm'’ by metis_tac [SUBMAP_TRANS]
    \\ simp []
    \\ ‘wrt_ext im' lm'
          (λi l. xeval_lit (is,ls) xaig p ⇔
                 xeval_lit (aig_read is i,aig_read ls l) res u1)’ by
         (irule wrt_ext_mono
          \\ qpat_x_assum ‘wrt_ext im lm _’ $ irule_at Any \\ simp [])
    \\ rpt conj_tac
    >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
    >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
    >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
    >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
    >- (rw [] \\ res_tac)
    \\ fs [wrt_ext_def] \\ rw [] \\ res_tac \\ simp [])
  (* if-then-else gates *)
  \\ qpat_x_assum ‘xrename_lit p _ _ _ _ = _’ assume_tac
  \\ drule_all xrename_lit_thm \\ strip_tac
  \\ qpat_x_assum ‘xrename_lit p0 _ _ _ _ = _’ assume_tac
  \\ drule_all xrename_lit_thm \\ strip_tac
  \\ qpat_x_assum ‘xrename_lit p1 _ _ _ _ = _’ assume_tac
  \\ drule_all xrename_lit_thm \\ strip_tac
  \\ ‘im_1 SUBMAP im'' ∧ lm_1 SUBMAP lm'' ∧ im SUBMAP im'' ∧ lm SUBMAP lm''’ by
       metis_tac [SUBMAP_TRANS]
  \\ simp []
  \\ ‘wrt_ext im'' lm''
        (λi l. xeval_lit (is,ls) xaig p ⇔
               xeval_lit (aig_read is i,aig_read ls l) res u1)’ by
       (irule wrt_ext_mono
        \\ qpat_x_assum ‘wrt_ext im lm _’ $ irule_at Any \\ simp [])
  \\ ‘wrt_ext im'' lm''
        (λi l. xeval_lit (is,ls) xaig p0 ⇔
               xeval_lit (aig_read is i,aig_read ls l) res u2)’ by
       (irule wrt_ext_mono
        \\ qpat_x_assum ‘wrt_ext im' lm' _’ $ irule_at Any \\ simp [])
  \\ rpt conj_tac
  >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  >- (rw [] \\ res_tac \\ fs [SUBMAP_DEF])
  >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  >- (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac \\ fs [SUBSET_DEF])
  >- (rw [] \\ res_tac)
  \\ fs [wrt_ext_def] \\ rw [] \\ res_tac \\ simp []
QED

Theorem xaig_rename_thm:
  ∀(xaig:('a,'i,'l) xaig) res next im lm nm.
    xaig_rename xaig = (res,next,im,lm,nm) ⇒
    (∀l. xhas_var (Latch l) xaig ⇒ l ∈ FDOM lm) ∧
    (∀i. xhas_var (Input i) xaig ⇒ i ∈ FDOM im) ∧
    (∀l. xhas_var (Latch l) res ⇒ l ∈ FRANGE lm) ∧
    (∀i. xhas_var (Input i) res ⇒ i ∈ FRANGE im) ∧
    ALL_DISTINCT (MAP FST res) ∧ xclosed res ∧
    rename_inv is ls xaig res nm next im lm
Proof
  Induct
  >- fs [xaig_rename_def, xclosed_def, xhas_var_def, rename_inv_def,
         DISJOINT3_def, gates_ok_def]
  \\ PairCases \\ fs [xaig_rename_def] \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs []
  \\ drule_all xrename_gty_thm \\ strip_tac
  \\ drule rename_inv_bound \\ strip_tac
  \\ fs [xhas_var_def, xclosed_def, SF DNF_ss]
  \\ rpt conj_tac
  \\ TRY (rw [] \\ imp_res_tac SUBMAP_FRANGE \\ res_tac
          \\ fs [SUBSET_DEF, SUBMAP_DEF] \\ NO_TAC)
  (* every gate mentioned by the new gate has been renamed already *)
  >-
   (rw [] \\ res_tac
    \\ qpat_x_assum ‘rename_inv is ls xaig res' nm' next'' im lm’ mp_tac
    \\ simp [rename_inv_def, ALOOKUP_NONE, SUBSET_DEF] \\ rw [] \\ res_tac)
  \\ qpat_x_assum ‘rename_inv is ls xaig res' nm' next'' im lm’ mp_tac
  \\ simp [rename_inv_def] \\ strip_tac
  \\ rpt conj_tac
  >- (rw [] \\ res_tac \\ fs [])
  >- gvs [DISJOINT3_def]
  >- (irule SUBSET_TRANS \\ irule_at Any FRANGE_DOMSUB_SUBSET
      \\ gvs [SUBSET_DEF])
  \\ simp [gates_ok_def] \\ gen_tac
  \\ Cases_on ‘n = h0’ \\ gvs [FLOOKUP_SIMP]
  >- fs [wrt_ext_def, xeval_gate_cons]
  \\ strip_tac \\ fs [gates_ok_def]
  \\ first_x_assum drule \\ strip_tac \\ simp []
  \\ ‘t ≠ next''’ by
       (strip_tac \\ gvs [] \\ fs [SUBSET_DEF, FRANGE_FLOOKUP]
        \\ res_tac \\ res_tac \\ fs [])
  \\ fs [wrt_ext_def, xeval_gate_cons]
QED

Theorem xeval_gate_swap[local]:
  ∀xs name.
    (∀i. xhas_var (Input i) xs ⇒ is i = is1 i) ∧
    (∀l. xhas_var (Latch l) xs ⇒ ls l = ls1 l) ⇒
    (xeval_gate (is,ls) xs name ⇔ xeval_gate (is1,ls1) xs name)
Proof
  Induct \\ fs [xeval_gate_cons, FORALL_PROD] \\ rw []
  >-
   (fs [xhas_var_def, SF DNF_ss]
    \\ irule xeval_gty_cong \\ simp [EVERY_MEM]
    \\ Cases \\ Cases_on ‘q’ \\ simp [xeval_lit_def]
    \\ Cases_on ‘b’ \\ rw [] \\ res_tac \\ fs [])
  \\ first_x_assum irule \\ fs [xhas_var_def]
QED

Theorem xeval_gate'_swap:
  (∀i. xhas_var (Input i) res ⇒ is i = is1 i) ∧
  (∀l. xhas_var (Latch l) res ⇒ ls l = ls1 l) ⇒
  (xeval_gate' (is,ls) res ⇔ xeval_gate' (is1,ls1) res)
Proof
  Cases_on ‘res’ \\ fs [xeval_gate'_def]
  \\ PairCases_on ‘h’ \\ fs [xeval_gate'_def]
  \\ strip_tac \\ irule xeval_gate_swap \\ fs []
QED

Theorem xeval_gate'_xaig_rename:
  (∃is ls. xeval_gate' (is,ls) (FST (xaig_rename xaig))) ⇔
  (∃is ls. xeval_gate' (is,ls) xaig)
Proof
  ‘∃r. xaig_rename xaig = r’ by simp []
  \\ PairCases_on ‘r’ \\ gvs []
  \\ rename [‘_ = (res,next,im,lm,nm)’]
  \\ drule xaig_rename_thm \\ strip_tac
  \\ Cases_on ‘xaig’ \\ fs []
  >- gvs [xaig_rename_def, xeval_gate'_def]
  \\ PairCases_on ‘h’ \\ fs []
  \\ reverse eq_tac \\ rw []
  (* every satisfying assignment for the renamed xaig can be mapped back *)
  >-
   (first_x_assum $ qspecl_then [‘ls’,‘is’] strip_assume_tac
    \\ fs [rename_inv_def, gates_ok_def]
    \\ first_x_assum $ qspec_then ‘h0’ mp_tac
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ fs [wrt_ext_def]
    \\ first_x_assum $ qspecl_then [‘FEMPTY’,‘FEMPTY’] mp_tac
    \\ impl_tac >- fs []
    \\ strip_tac
    \\ fs [xaig_rename_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [xeval_gate'_def, FLOOKUP_SIMP]
    \\ qexistsl [‘aig_read is im’,‘aig_read ls lm’] \\ simp [])
  (* and vice versa *)
  \\ first_x_assum $ qspecl_then [‘λt. ls (lm ' t)’, ‘λt. is (im ' t)’]
       strip_assume_tac
  \\ fs [rename_inv_def, gates_ok_def]
  \\ first_x_assum $ qspec_then ‘h0’ mp_tac
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ fs [wrt_ext_def]
  \\ first_x_assum $ qspecl_then [‘FEMPTY’,‘FEMPTY’] mp_tac
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ qexistsl [‘λt. is im⟨t⟩’,‘λt. ls lm⟨t⟩’]
  \\ simp [xeval_gate'_def]
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ qabbrev_tac ‘is1 = aig_read (λt. is im⟨t⟩) (im ⊌ FEMPTY)’
  \\ qabbrev_tac ‘ls1 = aig_read (λt. ls lm⟨t⟩) (lm ⊌ FEMPTY)’
  \\ qsuff_tac ‘xeval_gate' (is,ls) res = xeval_gate' (is1,ls1) res’
  >- (fs [xaig_rename_def] \\ rpt (pairarg_tac \\ gvs [])
      \\ gvs [xeval_gate'_def, FLOOKUP_SIMP])
  \\ irule xeval_gate'_swap \\ rw [] \\ first_x_assum drule
  \\ unabbrev_all_tac \\ fs [aig_read_def] \\ simp [FLOOKUP_DEF]
  \\ rw [IN_FRANGE] \\ fs [INJ_DEF] \\ metis_tac []
QED

(*----------------------------------------------------------------------*
   lowering to CNF
 *----------------------------------------------------------------------*)

(* CNF variable 0 is reserved for the constant false: every generated CNF
   contains the unit clause [Neg 0].  Renaming never produces the name 0,
   see rename_inv_def, so var_to_lit can map each literal, including the
   constants FF and TT, to a CNF literal without any special casing. *)

Definition xor_to_cnf_def:
  xor_to_cnf y a b =
    [[negate y; a; b];
     [negate y; negate a; negate b];
     [y; negate a; b];
     [y; a; negate b]]
End

Definition ite_to_cnf_def:
  ite_to_cnf y c a b =
    [[negate c; negate a; y];
     [negate c; a; negate y];
     [c; negate b; y];
     [c; b; negate y]]
End

Definition xgty_to_cnf_def:
  xgty_to_cnf n (And ts) =
    eq_every_to_cnf (Pos n) (MAP var_to_lit ts) ∧
  xgty_to_cnf n (Xor t1 t2) =
    xor_to_cnf (Pos n) (var_to_lit t1) (var_to_lit t2) ∧
  xgty_to_cnf n (Ite t1 t2 t3) =
    ite_to_cnf (Pos n) (var_to_lit t1) (var_to_lit t2) (var_to_lit t3)
End

Theorem xor_to_cnf_thm:
  satisfies_cnf w (set (xor_to_cnf y a b)) ⇔
  (satisfies_lit w y ⇔ (satisfies_lit w a ⇎ satisfies_lit w b))
Proof
  simp [satisfies_cnf_set, xor_to_cnf_def, satisfies_clause_def,
        satisfies_lit_negate, SF DNF_ss]
  \\ Cases_on ‘satisfies_lit w y’
  \\ Cases_on ‘satisfies_lit w a’
  \\ Cases_on ‘satisfies_lit w b’ \\ fs []
QED

Theorem ite_to_cnf_thm:
  satisfies_cnf w (set (ite_to_cnf y c a b)) ⇔
  (satisfies_lit w y ⇔
   if satisfies_lit w c then satisfies_lit w a else satisfies_lit w b)
Proof
  simp [satisfies_cnf_set, ite_to_cnf_def, satisfies_clause_def,
        satisfies_lit_negate, SF DNF_ss]
  \\ Cases_on ‘satisfies_lit w y’
  \\ Cases_on ‘satisfies_lit w c’
  \\ Cases_on ‘satisfies_lit w a’
  \\ Cases_on ‘satisfies_lit w b’ \\ fs []
QED

Theorem satisfies_lit_var_to_lit:
  ∀t. satisfies_lit w (var_to_lit t) ⇔ (SND t ⇎ w (var_to_num (FST t)))
Proof
  Cases \\ Cases_on ‘r’ \\ fs [var_to_lit_def, satisfies_lit_def]
QED

Theorem xgty_to_cnf_thm:
  ∀gt n.
    EVERY (λt. satisfies_lit w (var_to_lit t) ⇔ xeval_lit ss rest t)
          (gty_lits gt) ⇒
    (satisfies_cnf w (set (xgty_to_cnf n gt)) ⇔ (w n ⇔ xeval_gty ss rest gt))
Proof
  Cases \\ rw [xgty_to_cnf_def]
  >-
   (fs [eq_every_to_cnf_thm, satisfies_lit_def, EVERY_MAP, xeval_lit_def]
    \\ AP_TERM_TAC \\ irule EVERY_EQ_EVERY \\ fs [])
  >- fs [xor_to_cnf_thm, satisfies_lit_def, xeval_lit_def]
  \\ fs [ite_to_cnf_thm, satisfies_lit_def, xeval_lit_def]
QED

Definition xto_cnf_def:
  xto_cnf ([] : (num,num,num) xaig) acc = (acc : num lit list list) ∧
  xto_cnf ((n,gt)::xs) acc = xto_cnf xs (xgty_to_cnf n gt ++ acc)
End

Definition direct_xaig_to_cnf_def:
  direct_xaig_to_cnf (xaig : (num,num,num) xaig) =
    case xaig of
    | [] => [[]]
    | ((name,_)::_) =>
        ([Neg 0] :: [Pos name] :: xto_cnf xaig []) : num lit list list
End

Definition xeval_gates_def:
  (xeval_gates ss [] w ⇔ T) ∧
  (xeval_gates ss ((k,gt)::rest) w ⇔
     (w k = xeval_gate ss ((k,gt)::rest) k) ∧
     xeval_gates ss rest w)
End

Theorem xto_cnf_acc:
  ∀xaig acc. set (xto_cnf xaig acc) = set (xto_cnf xaig []) ∪ set acc
Proof
  Induct
  >- (once_rewrite_tac [xto_cnf_def] \\ simp [])
  \\ PairCases
  \\ once_rewrite_tac [xto_cnf_def]
  \\ pop_assum $ once_rewrite_tac o single
  \\ fs [AC UNION_ASSOC UNION_COMM]
QED

Theorem xeval_gates_ALOOKUP:
  ∀xaig a.
    xeval_gates (w,w) xaig w ∧ ALOOKUP xaig a ≠ NONE ⇒
    (w a ⇔ xeval_gate (w,w) xaig a)
Proof
  Induct \\ simp [ALOOKUP_def]
  \\ PairCases \\ simp [ALOOKUP_def] \\ rw []
  \\ Cases_on ‘h0 = a’ \\ gvs [xeval_gates_def]
  \\ gvs [xeval_gate_cons]
QED

Theorem satisfies_lit_var_to_lit_eq[local]:
  ∀t.
    ¬w 0 ∧ xeval_gates (w,w) rest w ∧
    (∀m b. t = (Gate m,b) ⇒ ALOOKUP rest m ≠ NONE) ⇒
    (satisfies_lit w (var_to_lit t) ⇔ xeval_lit (w,w) rest t)
Proof
  Cases \\ Cases_on ‘q’
  \\ simp [satisfies_lit_var_to_lit, var_to_num_def, xeval_lit_def]
  >- (rw [] \\ drule_all xeval_gates_ALOOKUP \\ simp [])
  \\ Cases_on ‘b’ \\ simp [var_to_num_def]
QED

Theorem satisfies_cnf_IMP_xeval_gates:
  ∀xaig w.
    satisfies_cnf w (set (xto_cnf xaig [])) ∧ xclosed xaig ∧ ¬w 0 ⇒
    xeval_gates (w,w) xaig w
Proof
  Induct \\ simp [xeval_gates_def]
  \\ PairCases \\ fs [xclosed_def]
  \\ simp [xeval_gates_def, xto_cnf_def]
  \\ simp [Once xto_cnf_acc]
  \\ rpt gen_tac \\ strip_tac
  \\ dxrule satisfies_cnf_UNION_IMP \\ strip_tac
  \\ last_x_assum drule_all \\ strip_tac
  \\ simp [xeval_gate_cons]
  \\ ‘EVERY (λt. satisfies_lit w (var_to_lit t) ⇔ xeval_lit (w,w) xaig t)
        (gty_lits h1)’ by
       (simp [EVERY_MEM] \\ rw [] \\ irule satisfies_lit_var_to_lit_eq
        \\ fs [] \\ rw [] \\ res_tac)
  \\ drule xgty_to_cnf_thm
  \\ disch_then $ qspec_then ‘h0’ mp_tac \\ fs []
QED

Definition xcnf_witness_def:
  xcnf_witness i_dom l_dom is ls xaig n =
    if n ∈ i_dom then is n else
    if n ∈ l_dom then ls n else
      case find_suffix n xaig of
      | NONE => F
      | SOME rest => xeval_gate (is,ls) rest n
End

Theorem xeval_gate_drop[local]:
  ∀l1 a.
    ~MEM a (MAP FST l1) ⇒
    xeval_gate (is,ls) (l1 ++ l2) a = xeval_gate (is,ls) l2 a
Proof
  Induct \\ fs [xeval_gate_cons, FORALL_PROD]
QED

Theorem find_suffix_MEM[local]:
  ∀xs rest. find_suffix n xs = SOME rest ⇒ MEM n (MAP FST xs)
Proof
  Induct \\ fs [find_suffix_def, FORALL_PROD] \\ rw [] \\ fs []
QED

Theorem xcnf_witness_0[local]:
  0 ∉ i_dom ∧ 0 ∉ l_dom ∧ ¬MEM 0 (MAP FST xaig) ⇒
  ¬xcnf_witness i_dom l_dom is ls xaig 0
Proof
  rw [xcnf_witness_def] \\ CASE_TAC \\ imp_res_tac find_suffix_MEM \\ fs []
QED

Theorem xcnf_witness_gate[local]:
  ∀before xs a.
    ALL_DISTINCT (MAP FST (before ++ xs)) ∧ MEM a (MAP FST xs) ∧
    a ∉ i_dom ∧ a ∉ l_dom ⇒
    (xcnf_witness i_dom l_dom is ls (before ++ xs) a ⇔ xeval_gate (is,ls) xs a)
Proof
  rw [xcnf_witness_def] \\ gvs [MEM_MAP, MEM_SPLIT, EXISTS_PROD]
  \\ ‘ALL_DISTINCT (MAP FST (before ++ l1) ++ a :: MAP FST l2)’ by
       full_simp_tac std_ss [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]
  \\ drule find_suffix_fast_forward
  \\ simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ irule xeval_gate_drop
  \\ fs [ALL_DISTINCT_APPEND] \\ metis_tac []
QED

Theorem xeval_gate_IMP_cnf_lemma[local]:
  ∀xaig past.
    xclosed xaig ∧
    DISJOINT3 i_dom l_dom (set (MAP FST xaig)) ∧
    0 ∉ i_dom ∧ 0 ∉ l_dom ∧ ~MEM 0 (MAP FST (past ++ xaig)) ∧
    (∀l. xhas_var (Latch l) xaig ⇒ l ∈ l_dom) ∧
    (∀i. xhas_var (Input i) xaig ⇒ i ∈ i_dom) ∧
    ALL_DISTINCT (MAP FST (past ++ xaig)) ⇒
    satisfies_cnf (xcnf_witness i_dom l_dom is ls (past ++ xaig))
      (set (xto_cnf xaig []))
Proof
  Induct \\ simp [Once xto_cnf_def]
  >- simp [satisfies_cnf_def, satisfies_fml_gen_def]
  \\ PairCases \\ fs [xclosed_def]
  \\ rpt strip_tac
  \\ simp [Once xto_cnf_def]
  \\ simp [Once xto_cnf_acc]
  \\ irule IMP_satisfies_cnf_UNION
  \\ conj_tac
  >-
   (last_x_assum $ qspec_then ‘past ++ [(h0,h1)]’ mp_tac
    \\ asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP]
    \\ disch_then irule
    \\ fs [xhas_var_def, SF DNF_ss]
    \\ fs [DISJOINT3_def, IN_DISJOINT])
  \\ ‘¬xcnf_witness i_dom l_dom is ls (past ++ (h0,h1)::xaig) 0’ by
       (irule xcnf_witness_0 \\ fs [])
  \\ ‘∀a. MEM a (MAP FST xaig) ⇒
          (xcnf_witness i_dom l_dom is ls (past ++ (h0,h1)::xaig) a ⇔
           xeval_gate (is,ls) xaig a)’ by
       (rw [] \\ ‘past ++ (h0,h1)::xaig = (past ++ [(h0,h1)]) ++ xaig’ by fs []
        \\ pop_assum (fn th => rewrite_tac [th])
        \\ irule xcnf_witness_gate
        \\ fs [DISJOINT3_def, IN_DISJOINT]
        \\ rpt conj_tac
        >- full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
        \\ metis_tac [])
  \\ ‘EVERY (λt. satisfies_lit
                   (xcnf_witness i_dom l_dom is ls (past ++ (h0,h1)::xaig))
                   (var_to_lit t) ⇔ xeval_lit (is,ls) xaig t) (gty_lits h1)’ by
       (simp [EVERY_MEM] \\ Cases \\ Cases_on ‘q’
        \\ simp [satisfies_lit_var_to_lit, var_to_num_def, xeval_lit_def]
        >- (strip_tac \\ res_tac \\ fs [ALOOKUP_NONE] \\ res_tac \\ fs [])
        \\ Cases_on ‘b’ \\ simp [var_to_num_def] \\ strip_tac
        >- (‘i ∈ i_dom’ by
              (first_x_assum irule \\ simp [xhas_var_def] \\ metis_tac [])
            \\ simp [xcnf_witness_def])
        \\ ‘l ∈ l_dom’ by
             (first_x_assum irule \\ simp [xhas_var_def] \\ metis_tac [])
        \\ ‘l ∉ i_dom’ by (fs [DISJOINT3_def, IN_DISJOINT] \\ metis_tac [])
        \\ simp [xcnf_witness_def])
  \\ drule xgty_to_cnf_thm \\ disch_then $ qspec_then ‘h0’ mp_tac
  \\ disch_then (fn th => rewrite_tac [th])
  \\ ‘xcnf_witness i_dom l_dom is ls (past ++ (h0,h1)::xaig) h0 ⇔
      xeval_gate (is,ls) ((h0,h1)::xaig) h0’ by
       (irule xcnf_witness_gate \\ fs [DISJOINT3_def, IN_DISJOINT])
  \\ fs [xeval_gate_cons]
QED

Theorem xeval_gate_IMP_cnf:
  xclosed xaig ∧ ALL_DISTINCT (MAP FST xaig) ∧
  0 ∉ i_dom ∧ 0 ∉ l_dom ∧ ~MEM 0 (MAP FST xaig) ∧
  (∀l. xhas_var (Latch l) xaig ⇒ l ∈ l_dom) ∧
  (∀i. xhas_var (Input i) xaig ⇒ i ∈ i_dom) ∧
  DISJOINT3 i_dom l_dom (set (MAP FST xaig)) ⇒
  satisfies_cnf (xcnf_witness i_dom l_dom is ls xaig) (set (xto_cnf xaig []))
Proof
  qspecl_then [‘xaig’,‘[]’] mp_tac xeval_gate_IMP_cnf_lemma \\ fs []
QED

Theorem direct_xaig_to_cnf_correct:
  ALL_DISTINCT (MAP FST xaig) ∧ xclosed xaig ∧
  0 ∉ i_dom ∧ 0 ∉ l_dom ∧ ~MEM 0 (MAP FST xaig) ∧
  (∀l. xhas_var (Latch l) xaig ⇒ l ∈ l_dom) ∧
  (∀i. xhas_var (Input i) xaig ⇒ i ∈ i_dom) ∧
  DISJOINT3 i_dom l_dom (set (MAP FST xaig)) ⇒
  (satisfiable_cnf (set (direct_xaig_to_cnf xaig)) =
   ∃is ls. xeval_gate' (is,ls) xaig)
Proof
  rw [satisfiable_cnf_def] \\ eq_tac \\ strip_tac
  >-
   (qexists ‘w’ \\ qexists ‘w’
    \\ fs [direct_xaig_to_cnf_def]
    \\ pop_assum mp_tac
    \\ Cases_on ‘xaig’
    >- (rw [] \\ gvs [xeval_gate'_def]
        \\ fs [satisfies_cnf_def, satisfies_fml_gen_def, satisfies_clause_def])
    \\ PairCases_on ‘h’ \\ simp []
    \\ ntac 2 (once_rewrite_tac [satisfies_cnf_INSERT])
    \\ rw [satisfies_clause_def, satisfies_lit_def]
    \\ drule_all satisfies_cnf_IMP_xeval_gates
    \\ gvs [xeval_gates_def, xeval_gate'_def, xeval_gate_cons])
  \\ qexists ‘xcnf_witness i_dom l_dom is ls xaig’
  \\ simp [direct_xaig_to_cnf_def]
  \\ Cases_on ‘xaig’ >- gvs [xeval_gate'_def]
  \\ PairCases_on ‘h’ \\ fs []
  \\ ntac 2 (once_rewrite_tac [satisfies_cnf_INSERT])
  \\ rpt conj_tac
  >- (simp [satisfies_clause_def, satisfies_lit_def]
      \\ irule xcnf_witness_0 \\ fs [])
  >- (simp [satisfies_clause_def, satisfies_lit_def]
      \\ simp [xcnf_witness_def]
      \\ fs [find_suffix_def, xeval_gate'_def]
      \\ rw [] \\ fs [DISJOINT3_def, IN_DISJOINT])
  \\ drule xeval_gate_IMP_cnf \\ fs []
QED

Theorem var_lit_var_to_lit[local]:
  var_lit (var_to_lit t) = var_to_num (FST t)
Proof
  Cases_on ‘t’ \\ Cases_on ‘r’ \\ fs [var_to_lit_def]
QED

Theorem lits_within_xgty_to_cnf[local]:
  n < limit ∧ EVERY (λt. var_lit (var_to_lit t) < limit) (gty_lits gt) ⇒
  lits_within limit (xgty_to_cnf n gt)
Proof
  Cases_on ‘gt’
  \\ fs [xgty_to_cnf_def, lits_within_def, xor_to_cnf_def, ite_to_cnf_def]
  \\ strip_tac
  \\ fs [GSYM lits_within_def]
  \\ irule lits_within_eq_every_to_cnf
  \\ fs [EVERY_MAP]
QED

Theorem xto_cnf_lits_within:
  ∀xaig acc.
    (∀l. xhas_var (Latch l) xaig ⇒ l < limit) ∧
    (∀i. xhas_var (Input i) xaig ⇒ i < limit) ∧
    0 < limit ∧ xclosed xaig ∧
    EVERY (λ(n,_). n < limit) xaig ∧
    lits_within limit acc ⇒
    lits_within limit (xto_cnf xaig acc)
Proof
  Induct \\ simp [xto_cnf_def]
  \\ Cases \\ simp [xto_cnf_def]
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ fs [xclosed_def, xhas_var_def, SF DNF_ss]
  \\ fs [lits_within_def]
  \\ fs [GSYM lits_within_def]
  \\ irule lits_within_xgty_to_cnf
  \\ fs [EVERY_MEM] \\ rw []
  \\ PairCases_on ‘t’ \\ fs [var_lit_var_to_lit]
  \\ Cases_on ‘t0’ \\ fs [var_to_num_def]
  >- (res_tac \\ fs [ALOOKUP_NONE, MEM_MAP, FORALL_PROD, EXISTS_PROD]
      \\ res_tac \\ fs [])
  \\ Cases_on ‘b’ \\ fs [var_to_num_def] \\ res_tac
QED

Theorem direct_xaig_to_cnf_lits_within:
  (∀l. xhas_var (Latch l) xaig ⇒ l < limit) ∧
  (∀i. xhas_var (Input i) xaig ⇒ i < limit) ∧
  0 < limit ∧ xclosed xaig ∧
  EVERY (λ(n,_). n < limit) xaig ⇒
  lits_within limit (direct_xaig_to_cnf xaig)
Proof
  strip_tac \\ fs [direct_xaig_to_cnf_def]
  \\ Cases_on ‘xaig’ >- fs [lits_within_def]
  \\ PairCases_on ‘h’ \\ fs []
  \\ fs [lits_within_def]
  \\ fs [GSYM lits_within_def]
  \\ irule xto_cnf_lits_within \\ fs [lits_within_def]
QED

(*----------------------------------------------------------------------*
   plugging everything together
 *----------------------------------------------------------------------*)

Definition xaig_to_cnf_def:
  xaig_to_cnf xaig name =
    let xaig_1 = xprune_for name xaig in
    let (xaig_2, limit, x) = xaig_rename_rev xaig_1 [] 1n FEMPTY FEMPTY FEMPTY in
      (direct_xaig_to_cnf xaig_2, limit)
End

Theorem xaig_to_cnf_correct:
  xaig_to_cnf xaig name = (cnf, limit) ⇒
  (satisfiable_cnf (set cnf) ⇔ ∃is ls. xeval_gate (is,ls) xaig name) ∧
  lits_within limit cnf
Proof
  simp [xaig_to_cnf_def]
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ gvs [xprune_for_def, xprune_rev_thm, xaig_rename_rev_thm]
  \\ PairCases_on ‘x’
  \\ drule xaig_rename_thm
  \\ simp [GSYM PULL_FORALL]
  \\ strip_tac
  \\ qpat_x_assum ‘∀ls is. rename_inv _ _ _ _ _ _ _ _’
       (qspecl_then [‘ARB’,‘ARB’] assume_tac)
  \\ fs [rename_inv_def]
  \\ ‘0 ∉ FRANGE x0 ∧ 0 ∉ FRANGE x1 ∧ ¬MEM 0 (MAP FST xaig_2)’ by
       (rpt strip_tac \\ res_tac \\ fs [])
  \\ conj_tac
  >-
   (irule EQ_TRANS
    \\ irule_at Any direct_xaig_to_cnf_correct
    \\ qexistsl [‘FRANGE x1’,‘FRANGE x0’] \\ fs []
    \\ ‘xaig_2 = FST (xaig_rename (xprune xaig FEMPTY⟨name ↦ ()⟩))’ by
         asm_rewrite_tac []
    \\ pop_assum $ rewrite_tac o single
    \\ rewrite_tac [xeval_gate'_xaig_rename, xeval_gate'_xprune])
  \\ irule direct_xaig_to_cnf_lits_within \\ fs [EVERY_MEM, FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs [MEM_MAP, EXISTS_PROD]
  \\ res_tac \\ fs []
QED
