open HolKernel boolLib boolSimps bossLib lcsymtacs
open pairTheory listTheory rich_listTheory relationTheory quantHeuristicsLib quantHeuristicsLibAbbrev arithmeticTheory finite_mapTheory stringTheory combinTheory sptreeTheory
open intLib miscLib miscTheory bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bvlTheory
open bytecodeTerminationTheory
val _ = new_theory"bvlBytecode"

(* TODO: move *)
val set_MAP_FST_toAList = store_thm("set_MAP_FST_toAList",
  ``set (MAP FST (toAList t)) = domain t``,
  rw[pred_setTheory.EXTENSION,domain_lookup,MEM_MAP,EXISTS_PROD] >>
  metis_tac[MEM_toAList])
(* -- *)

val _ = Datatype`
  bvl_bc_state = <|
    next_label : num;
    out : bc_inst list |>`

val bvl_bc_state_component_equality = theorem"bvl_bc_state_component_equality"

val emit_def = Define`
  emit = FOLDL (λs i. s with <| out := i :: s.out |>)`

val get_label_def = Define`
  get_label s = (s with <| next_label := s.next_label + 1 |>, s.next_label)`

val _ = Datatype`
  bvl_bc_tail = TCNonTail | TCTail num num`

val stackshiftaux_def = Define`
  stackshiftaux (n:num) i j =
    if n = 0 then []
    else (Load i)::(Store j)::(stackshiftaux (n-1) (i+1) (j+1))`

val stackshift_def = Define`
  stackshift j k =
    if k = 0 then []
    else if j = 0 then [Pops (k-1); Pop]
    else if j = 1 then [Pops k]
    else if j ≤ k then (GENLIST (K (Store (k-1))) j)++(stackshift 0 (k-j))
    else (stackshiftaux k (j-k) j)++(stackshift (j-k) k)`

val stackshiftaux_ind = theorem"stackshiftaux_ind"

val stackshiftaux_thm = store_thm("stackshiftaux_thm",
  ``∀n i j bs bc0 bc1 xs ys z0 zs st.
      let code = MAP Stack (stackshiftaux n i j) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++z0++zs++st ∧
      LENGTH xs = i ∧
      LENGTH ys = n ∧
      LENGTH zs = n ∧
      j = i + n + LENGTH z0
      ⇒
      bc_next^* bs (bs with <|stack := xs++ys++z0++ys++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshiftaux_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshiftaux_def] >>
  Cases_on`n=0`>>simp[LENGTH_NIL]>-(
    rw[] >> simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  rw[] >> fs[] >>
  `bc_fetch bs = SOME (Stack(Load (LENGTH xs)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,EL_APPEND1,EL_APPEND2] >>
  Cases_on`zs`>>fs[]>>
  Cases_on`ys`>>fs[]>>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (Stack (Store (LENGTH xs + LENGTH z0 + LENGTH t + 1)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qmatch_assum_abbrev_tac`bc_fetch bs = SOME i` >>
    qexists_tac`bc0++[i]` >>
    simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND,Abbr`i`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_fetch bs = SOME i1` >>
  qmatch_assum_abbrev_tac`bc_fetch bs0 = SOME i2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[i1;i2]`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`i2`] >>
  disch_then(qspecl_then[`xs++[h']`,`t'`,`z0++[h']`]mp_tac) >>
  simp[SUM_APPEND,FILTER_APPEND,Abbr`i1`] >>
  disch_then(qspec_then`t`mp_tac) >>
  simp[ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val GENLIST_Store_thm = store_thm("GENLIST_Store_thm",
  ``∀n k bs bc0 bc1 xs ys zs.
    let code = MAP Stack (GENLIST (K (Store k)) n) in
    bs.code = bc0 ++ code ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs.stack = xs ++ ys ++ zs ∧
    LENGTH xs = n ∧
    LENGTH ys = SUC k ∧
    n ≤ SUC k
    ⇒
    bc_next^* bs (bs with <| stack := TAKE (SUC k - n) ys ++ xs ++ zs; pc := next_addr bs.inst_length (bc0++code) |>)``,
  Induct >- (
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[GENLIST_CONS] >> rw[] >>
  Q.PAT_ABBREV_TAC`f:num->bc_stack_op = K (Store k)` >>
  `f o SUC = f` by simp[Abbr`f`,FUN_EQ_THM] >> fs[] >>
  `bc_fetch bs = SOME (Stack (Store k))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  Cases_on`xs`>>fs[]>>
  simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`k`,`bs1`,`bc0++[Stack(Store k)]`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(qspecl_then[`t`]mp_tac) >> simp[] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspecl_then[`zs`]mp_tac) >> simp[] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val stackshift_ind = theorem"stackshift_ind"

val stackshift_thm = store_thm("stackshift_thm",
  ``∀j k bs bc0 bc1 xs ys st.
      let code = MAP Stack (stackshift j k) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++st ∧
      LENGTH xs = j ∧
      LENGTH ys = k
      ⇒
      bc_next^* bs (bs with <|stack := xs++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshift_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshift_def] >>
  rpt gen_tac >>
  Cases_on`k=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  Cases_on`j=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    `bc_fetch bs = SOME (Stack (Pops (LENGTH t)))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >>
      simp[] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,DROP_APPEND2] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_fetch bs1 = SOME (Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc1` >>
      simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] ) >>
  Cases_on`j=1`>>simp[] >- (
    rw[] >>
    Cases_on`xs`>>fs[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ [xi] ++ bc1` >>
    `bc_fetch bs = SOME xi` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >> simp[Abbr`xi`] ) >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`xi`] >>
    simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND,DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
  fs[] >>
  Cases_on`j ≤ k` >> fsrw_tac[ARITH_ss][] >- (
    rw[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (GENLIST (K(Store k)) n) ++ bc10 ++ bc1` >>
    qspecl_then[`n`,`k`,`bs`,`bc0`,`bc10++bc1`]mp_tac GENLIST_Store_thm >>
    simp[Abbr`bc10`] >>
    disch_then(qspecl_then[`xs`,`ys`]mp_tac) >>
    simp[Abbr`n`,Abbr`k`] >>
    qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
    strip_tac >>
    qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
    disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`,ADD1,LENGTH_NIL] >>
    disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    disch_then(qspecl_then[`xs++st`]mp_tac) >> simp[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (stackshiftaux n i j) ++ MAP Stack (stackshift i n) ++ bc1` >>
  qunabbrev_tac`i` >> qabbrev_tac`i = j-n` >>
  qspecl_then[`n`,`i`,`j`,`bs`,`bc0`]mp_tac stackshiftaux_thm >>
  simp[] >>
  disch_then(qspecl_then[`TAKE i xs`,`DROP i xs`,`[]`]mp_tac) >> simp[] >>
  simp[Abbr`i`,Abbr`j`,Abbr`n`] >>
  disch_then(qspecl_then[`ys`]mp_tac) >> simp[] >>
  qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
  strip_tac >>
  qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
  disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`] >>
  disch_then(qspecl_then[`TAKE (LENGTH xs - LENGTH ys) xs`,`DROP (LENGTH xs - LENGTH ys) xs`]mp_tac) >> simp[])

val pushret_def = Define`
  (pushret TCNonTail s = s) ∧
  (pushret (TCTail j k) s =
    if j = 0 then
      emit s [Stack (Pops k); Return]
    else
      emit s [
      (* v::|k|++ret++|j| *)
        Stack (Pops k);
      (* v::ret::|j| *)
        Stack (Load 1);
      (* ret::v::ret::|j| *)
        Stack (Store (j+1));
      (* v::ret::|j-1|::ret *)
        Stack (Pops j);
      (* v::ret *)
        Return])`

(*
RefPtr ptr::vn::...::v1::st
*)

val bvl_bc_ref_def = Define`
  (bvl_bc_ref 0 = []) ∧
  (bvl_bc_ref (SUC n) =
   [Stack(Load 0);
    Stack(PushInt(&(n)));
    Stack(Load 3);
    Update;
    Stack(Store 0)]++(bvl_bc_ref n))`

val bvl_bc_ref_correct = prove(
  ``∀n bs bc0 bc1 vs st ws ptr.
      bs.code = bc0 ++ (bvl_bc_ref n) ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = RefPtr ptr::vs++st ∧
      LENGTH vs = n ∧
      FLOOKUP bs.refs ptr = SOME (ValueArray ws) ∧
      n ≤ LENGTH ws
      ⇒
      bc_next^* bs
        (bs with <|
          pc := next_addr bs.inst_length (bc0 ++ bvl_bc_ref n);
          stack := RefPtr ptr::st;
          refs := bs.refs |+ (ptr,ValueArray (REVERSE vs ++ DROP(LENGTH vs)ws))|>)``,
  Induct >> simp[bvl_bc_ref_def,LENGTH_NIL] >- (
    rw[] >>
    qmatch_abbrev_tac`bc_next^* bs bs'` >>
    `bs' = bs` by (
      simp[Abbr`bs'`,bc_state_component_equality] >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[] >>
      simp[BUTLASTN]) >>
    rw[] ) >>
  rw[] >>
  Cases_on`vs`>>fs[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (EL 0 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++(TAKE 0 ls)` >>
    simp[Abbr`bs1`,Abbr`ls`] ) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qunabbrev_tac`bs1` >> qunabbrev_tac`bs2` >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (EL 1 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++(TAKE 1 ls)` >>
    simp[Abbr`bs1`,Abbr`ls`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qunabbrev_tac`bs1` >> qunabbrev_tac`bs2` >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (EL 2 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++(TAKE 2 ls)` >>
    simp[Abbr`bs1`,Abbr`ls`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  simp[Abbr`bs1`,Abbr`bs2`] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (EL 3 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++(TAKE 3 ls)` >>
    simp[Abbr`bs1`,Abbr`ls`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  simp[Abbr`bs1`,Abbr`bs2`] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (EL 4 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++(TAKE 4 ls)` >>
    simp[Abbr`bs1`,Abbr`ls`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  simp[Abbr`bs1`,Abbr`bs2`,bc_eval_stack_def] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ l1 ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++ls`,`bc1`,`t`]mp_tac) >>
  simp[Abbr`bs1`,FLOOKUP_UPDATE] >>
  discharge_hyps >- (
    simp[Abbr`ls`,FILTER_APPEND,SUM_APPEND] ) >>
  strip_tac >>
  simp[Abbr`bs2`] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2'` >>
  `bs1' = bs1` by (
    unabbrev_all_tac >> simp[bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  `bs2' = bs2` by (
    unabbrev_all_tac >> simp[bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
    rw[] >> simp[] >>
    simp[LIST_EQ_REWRITE] >>
    simp[EL_CONS,EL_DROP] >>
    Cases >> simp[EL_LUPDATE] >>
    simp[EL_DROP,ADD1] ) >>
  rw[])

val tlookup_def = Define`
  tlookup t k = case lookup k t of NONE => k | SOME v => v`

val bvl_bc_def = C (tDefine "bvl_bc")
  (WF_REL_TAC`measure (bvl_exp1_size o SND o SND o SND o SND o SND)`)`
  (bvl_bc f cenv t sz s [] = s) ∧
  (bvl_bc f cenv t sz s (e1::e2::es) =
    let s = bvl_bc f cenv TCNonTail sz s [e1] in
    bvl_bc f cenv t (sz+1) s (e2::es)) ∧
  (bvl_bc f cenv t sz s [Var n] =
     if n < LENGTH cenv then
       pushret t (emit s [Stack(Load(sz-(EL n cenv)))])
     else s) ∧
  (bvl_bc f cenv t sz s [If e1 e2 e3] =
    let (s,l1) = get_label s in
    let (s,l2) = get_label s in
    let s = bvl_bc f cenv TCNonTail sz s [e1] in
    let s = emit s [JumpIf (Lab l1)] in
    let s = bvl_bc f cenv t sz s [e3] in
    let s = emit s [Jump (Lab l2);Label l1] in
    let s = bvl_bc f cenv t sz s [e2] in
            emit s [Label l2]) ∧
  (bvl_bc f cenv t sz s [Let es e] =
    let s = bvl_bc f cenv TCNonTail sz s es in
    let n = LENGTH es in
    let s =
      bvl_bc f ((GENLIST (λi. sz+i+1) n)++cenv)
             (case t of TCTail j k => TCTail j (k+n) | _ => t)
             (sz+n) s [e] in
    emit s (case t of TCNonTail => [Stack(Pops n)] | _ => [])) ∧
  (bvl_bc f cenv t sz s [Raise e] =
    let s = bvl_bc f cenv TCNonTail sz s [e] in
            emit s [PopExc; Return]) ∧
  (bvl_bc f cenv t sz s [Handle e1 e2] =
    let (s,l0) = get_label s in
    let (s,l1) = get_label s in
    let s = emit s [PushPtr (Lab l0); PushExc] in
    let s = bvl_bc f cenv TCNonTail (sz+2) s [e1] in
    let s = pushret t (emit s [PopExc; Stack (Pops 1)]) in
    let s = emit s [Jump (Lab l1); Label l0] in
    let s = bvl_bc f ((sz+1)::cenv) (case t of TCTail j k => TCTail j (k+1) | _ => t) (sz+1) s [e2] in
            emit s [Stack (Pops 1); Label l1]) ∧
  (bvl_bc f cenv t sz s [Tick e] =
    let s = emit s [Tick] in
            bvl_bc f cenv t sz s [e]) ∧
  (bvl_bc f cenv t sz s [Call dest es] =
    let s = bvl_bc f cenv TCNonTail sz s es in
    let s = emit s [Tick] in
    let n = LENGTH es in
    case t of
    | TCNonTail =>
        (case dest of
           (* ptr::args *)
         | NONE => emit s [Stack(Load 0); CallPtr]
           (* args *)
         | SOME p => emit s [Stack(PushInt 0); Call (Addr (tlookup f p))])
    | TCTail j k =>
      (* args++|k|++ret::|j| *)
        (case dest of
         | NONE =>
           (* ptr::args++|k|++ret::|j| *)
             let s = emit s [Stack(Load 0);Stack(Load (1+n+k));Stack(Store 1);Stack(PushInt 0)] in
           (*      ptr::ptr::args++|k|++ret::|j| *)
           (* ret::ptr::ptr::args++|k|++ret::|j| *)
           (*      ptr::ret::args++|k|++ret::|j| *)
           (*  ig::ptr::ret::args++|k|++ret::|j| *)
             let s = emit s (MAP Stack (stackshift (1+1+n) (k+1+j))) in
           (* ig::ptr::ret::args *)
                     emit s [Return]
         | SOME p =>
           (* args++|k|++ret::|j| *)
             let s = emit s [Stack(Load(n+k));Stack(PushInt 0)] in
           (*     ret::args++|k|++ret::|j| *)
           (* ig::ret::args++|k|++ret::|j| *)
             let s = emit s (MAP Stack (stackshift (1+1+n) (k+1+j))) in
           (* ig::ret::args *)
                     emit s [Jump (Addr (tlookup f p))])) ∧
  (bvl_bc f cenv t sz s [Op op es] =
    let s = bvl_bc f cenv TCNonTail sz s es in
    let s = emit s (case op of
    | Global n => [Gread n]
    | AllocGlobal => [Galloc 1; Stack(PushInt 0)]
    | SetGlobal n => [Gupdate n; Stack(PushInt 0)]
    | Cons n => [Stack(PushInt (&(LENGTH es))); Stack (Cons n)]
    | El => [Stack El]
    | LengthBlock => [Stack LengthBlock]
    | Length => [Length]
    | LengthByte => [LengthByte]
    | RefByte => [RefByte]
    | RefArray => [Ref]
    | DerefByte => [DerefByte]
    | UpdateByte => [Stack(Load 2);Stack(Load 2);Stack(Load 2);UpdateByte;Stack(Pops 2)]
    | FromList n => [] (* TODO *)
    | ToList => [] (* TODO *)
    | Const i => [Stack (PushInt i)]
    | TagEq n => [Stack (TagEq n)]
    | IsBlock => [Stack IsBlock]
    | Equal => [Stack Equal]
    | Ref => [Stack(PushInt 0);Stack(PushInt(&(LENGTH es)));Ref]++(bvl_bc_ref (LENGTH es))
    | Deref => [Deref]
    | Update => [Stack(Load 2);Stack(Load 2);Stack(Load 2);Update;Stack(Pops 2)]
    | Label n => [PushPtr (Addr (tlookup f n))]
    | Print => [Stack(Load 0);Print]
    | PrintC c => [PrintC c; Stack(PushInt 0)]
    | Add => [Stack Add]
    | Sub => [Stack Sub]
    | Mult => [Stack Mult]
    | Div => [Stack Div]
    | Mod => [Stack Mod]
    | Less => [Stack Less])
    in pushret t s)`

val bvl_bc_ind = theorem"bvl_bc_ind"

(*
stack = a,b,x5,x4,x3,c,x7,x6,d
sz = 9
env = [x3,x4,x5,x6,x7]
cenv = [5,6,7,2,3]

add another junk:
stack = z,a,b,x5,x4,x3,c,x7,x6,d
sz = 10
env = [x3,x4,x5,x6,x7]
cenv = [5,6,7,2,3]

add another let:
stack = x2,x1,x0,z,a,b,x5,x4,x3,c,x7,x6,d
sz = 13
env = [x0,x1,x2,x3,x4,x5,x6,x7]
cenv = [11,12,13,5,6,7,2,3]
*)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ((pushret t s).next_label = s.next_label) ∧
          ∃bc. ((pushret t s).out = bc ++ s.out) ∧
               (FILTER is_Label bc = [])``,
  Cases >> rw[pushret_def,emit_def])

val FOLDL_emit_append_out = prove(
  ``∀ls s. emit s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[bvl_bc_state_component_equality,emit_def] >> fs[emit_def])
  |> SIMP_RULE (srw_ss())[]

val FILTER_is_Label_bvl_bc_ref = prove(
  ``∀n. FILTER is_Label (bvl_bc_ref n) = []``,
  Induct >> simp[bvl_bc_ref_def])

val bvl_bc_append_out = store_thm("bvl_bc_append_out",
  ``(∀f cenv t sz s e.
       ∃bc. ((bvl_bc f cenv t sz s e).out = bc ++ s.out) ∧
            ALL_DISTINCT (FILTER is_Label bc) ∧
            s.next_label ≤ (bvl_bc f cenv t sz s e).next_label ∧
            EVERY (between s.next_label (bvl_bc f cenv t sz s e).next_label)
              (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac bvl_bc_ind >>
  strip_tac >- simp[bvl_bc_def] >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    fs[emit_def,FILTER_APPEND] ) >>
  strip_tac >- (
    simp[bvl_bc_def,get_label_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    Cases_on`t`>>fs[]>>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS]) >>
  strip_tac >- (
    simp[bvl_bc_def,get_label_def,emit_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> res_tac >> fs[]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def,FOLDL_emit_append_out] >> rw[] >>
    Cases_on`t`>>Cases_on`dest`>>fs[]>>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       FILTER_REVERSE,EVERY_REVERSE,ALL_DISTINCT_REVERSE,is_Label_rwt,PULL_EXISTS] >>
    fs[MEM_MAP] >>
    qmatch_abbrev_tac`ALL_DISTINCT ls` >>
    qsuff_tac`ls=[]`>>rw[Abbr`ls`]>>
    rw[FILTER_EQ_NIL,EVERY_MAP]) >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    Cases_on`op`>>
    TRY (
      fs[emit_def] >>
      SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
      qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
      fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
         is_Label_rwt,PULL_EXISTS] >>
      fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
      spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
      fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> res_tac >> fs[] >> NO_TAC) >>
    simp[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    simp[FOLDL_emit_append_out,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    simp[FILTER_is_Label_bvl_bc_ref]))

val good_code_env_def = Define`
  good_code_env f il cmap ls ⇔
    ∀ptr exp arity. (lookup ptr cmap = SOME (arity,exp)) ⇒
      ∃cs l0 cc l1.
        ((bvl_bc f (GENLIST SUC arity) (TCTail arity 1) (arity+2) cs [exp]).out = cc ++ cs.out) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label l0) ∧
        ALL_DISTINCT (FILTER is_Label l0) ∧
        (ls = l0 ++ REVERSE cc ++ l1) ∧
        (tlookup f ptr = next_addr il l0)`

val bvl_to_bc_value_def = tDefine"bvl_to_bc_value"`
  (bvl_to_bc_value f (CodePtr ptr) = CodePtr (tlookup f ptr)) ∧
  (bvl_to_bc_value f (Block n vs) = Block n (MAP (bvl_to_bc_value f) vs)) ∧
  (bvl_to_bc_value f v = v)`
(WF_REL_TAC`measure (bc_value_size o SND)` >>
 gen_tac>>Induct_on`vs`>>simp[bc_value_size_def] >>
 rw[] >> res_tac >> fsrw_tac[ARITH_ss][])

val good_env_def = Define`
  good_env f sz st env cenv ⇔
      sz ≤ LENGTH st ∧
      LIST_REL (λv n. n ≤ sz ∧ (sz-n) < LENGTH st ∧ (EL (sz-n) st = bvl_to_bc_value f v)) env cenv`

val good_env_cons = store_thm("good_env_cons",
  ``good_env f sz st env cenv ⇒
    good_env f (sz+1) (h::st) env cenv``,
  rw[good_env_def,LIST_REL_EL_EQN] >> rfs[] >> res_tac >>
  simp[EL_CONS,PRE_SUB1])

val pushret_correct = store_thm("pushret_correct",
  ``∀t s bs prc igc code bc0 bc1 bs1 v ret rst.
      ((pushret t s).out = REVERSE prc ++ s.out) ∧
      (s.out = REVERSE code ++ igc) ∧
      (bs.code = bc0 ++ code ++ prc ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (bc_next^* bs bs1) ∧
      (bs1.stack = v::bs.stack) ∧
      (bs1.pc = next_addr bs.inst_length (bc0++code)) ∧
      (case t of TCTail j k =>
         ∃ig args. bs.stack = ig ++ [CodePtr ret] ++ args ++ rst ∧
                   LENGTH ig = k ∧ LENGTH args = j
       | TCNonTail => T)
      ⇒
      ∃bs2.
        bc_next^* bs bs2 ∧
        case t of TCNonTail => bs2 = bs1
        | TCTail j k =>
            bs2 = bs1 with <| stack := v::rst; pc := ret |>``,
  Cases >> rw[pushret_def,emit_def] >>
  fs[Once (GSYM SWAP_REVERSE)] >> rw[] >>
  simp[Once RTC_CASES_RTC_TWICE] >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  imp_res_tac RTC_bc_next_preserves >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 0 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 0 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  simp[DROP_APPEND1,DROP_LENGTH_NIL] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 1 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 1 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >- (
    disj1_tac >> unabbrev_all_tac >> fs[LENGTH_NIL] ) >>
  disj2_tac >>
  `bc_fetch bs0 = SOME(EL 2 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 2 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 3 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 3 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  simp[TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 4 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 4 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`])

val refv_map_def = Define`
  refv_map f ((ValueArray vs):ref_value) = (ValueArray (MAP f vs):ref_value) ∧
  refv_map f (ByteArray bs) = ByteArray bs`
val _ = export_rewrites["refv_map_def"]

val bc_equal_bvl_to_bc_value = prove(
  ``(∀x y. (bc_equal (bvl_to_bc_value f x) (bvl_to_bc_value f y) = bc_equal x y)) ∧
    (∀xs ys. (bc_equal_list (MAP (bvl_to_bc_value f) xs) (MAP (bvl_to_bc_value f) ys) = bc_equal_list xs ys))``,
  ho_match_mp_tac bc_equal_ind >>
  simp[bc_equal_def,bvl_to_bc_value_def] >>
  rw[] >> fs[] >> rfs[] >> srw_tac[ETA_ss][] >>
  BasicProvers.CASE_TAC >> fs[])

val bvs_to_chars_bvl_to_bc_value = prove(
  ``∀vs acc. bvs_to_chars (MAP (bvl_to_bc_value f) vs) acc = bvs_to_chars vs acc``,
  Induct >> simp[] >>
  Cases >> simp[bvl_to_bc_value_def,bvs_to_chars_def])

val bv_to_string_bvl_to_bc_value = prove(
  ``∀v. bv_to_string (bvl_to_bc_value f v) = bv_to_string v``,
  ho_match_mp_tac bv_to_string_ind >>
  simp[bvl_to_bc_value_def,bv_to_string_def] >>
  srw_tac[ETA_ss][bvs_to_chars_bvl_to_bc_value])

val bvl_bc_correct = store_thm("bvl_bc_correct",
  ``∀exps env s res s' bs1 bc0 code bc1 cenv t sz cs stw ret sp hdl rst1 rst2.
      (bEval (exps,env,s) = (res,s')) ∧ res ≠ Error ∧
      (good_env f sz bs1.stack env cenv) ∧
      (good_code_env f bs1.inst_length s.code bs1.code) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧
      ((bvl_bc f cenv t sz cs exps).out = REVERSE code ++ cs.out) ∧
      (bs1.code = bc0 ++ code ++ bc1) ∧
      (bs1.pc = next_addr bs1.inst_length bc0) ∧
      (bs1.output = s.output) ∧ (bs1.clock = SOME s.clock) ∧
      (bs1.globals = MAP (OPTION_MAP (bvl_to_bc_value f)) s.globals) ∧
      (bs1.refs = (refv_map (bvl_to_bc_value f)) o_f s.refs) ∧
      (case t of
       | TCTail j k =>
           (LENGTH exps = 1) ∧
           (∃ig args. (bs1.stack = ig++(CodePtr ret::args)++rst1) ∧ (LENGTH ig = k) ∧ (LENGTH args = j))
       | TCNonTail => bs1.stack = rst1) ∧
      (case res of Exception _ =>
        ∃ig. (rst1 = ig ++ [StackPtr sp; CodePtr hdl] ++ rst2) ∧
             (LENGTH rst2 + 1 = bs1.handler)
       | _ => T)
      ⇒
      ∃bs2.
        bc_next^* bs1 bs2 ∧
        case res of
        | TimeOut =>
            (bc_fetch bs2 = SOME Tick) ∧
            (bs2.output = s'.output) ∧ (bs2.clock = SOME 0) ∧
            (bs2.globals = MAP (OPTION_MAP (bvl_to_bc_value f)) s'.globals) ∧
            (bs2.refs = (refv_map (bvl_to_bc_value f)) o_f s'.refs)
        | Exception v =>
            (bs2 = bs1 with <|stack := (bvl_to_bc_value f v)::rst2; pc := hdl; handler := sp;
                              output := s'.output; clock := SOME s'.clock;
                              globals := MAP (OPTION_MAP (bvl_to_bc_value f)) s'.globals;
                              refs := (refv_map (bvl_to_bc_value f)) o_f s'.refs|>)
        | Result vs =>
          (case t of
            | TCNonTail =>
              (bs2 = bs1 with <|
                stack := (REVERSE (MAP (bvl_to_bc_value f) vs))++bs1.stack;
                pc := next_addr bs2.inst_length (bc0++code);
                output := s'.output; clock := SOME s'.clock;
                globals := MAP (OPTION_MAP (bvl_to_bc_value f)) s'.globals;
                refs := (refv_map (bvl_to_bc_value f)) o_f s'.refs|>)
            | TCTail _ _ =>
              (bs2 = bs1 with <|
                stack := (bvl_to_bc_value f (HD vs))::rst1; pc := ret;
                output := s'.output; clock := SOME s'.clock;
                globals := MAP (OPTION_MAP (bvl_to_bc_value f)) s'.globals;
                refs := (refv_map (bvl_to_bc_value f)) o_f s'.refs|>))``,
  recInduct bEval_ind >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    simp[Once SWAP_REVERSE] >>
    Cases_on`t`>>rw[] >>
    qexists_tac`bs1`>>rw[bc_state_component_equality] ) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    rw[] >> Cases_on`t`>>fs[] >>
    `∃res0 s0. bEval ([x],env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    `∃res1 s1. bEval (y::xs,env,s0) = (res1,s1)` by metis_tac[pair_CASES] >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs`,`[x]`]strip_assume_tac bvl_bc_append_out >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz+1`,`bvl_bc f cenv TCNonTail sz cs [x]`,`y::xs`]strip_assume_tac bvl_bc_append_out >>
    Cases_on`res0`>>fs[] >- (
      first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc'++bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
      simp[] >> fs[Once SWAP_REVERSE] >> strip_tac >>
      first_x_assum(qspecl_then[`bs2`,`bc0++REVERSE bc`,`REVERSE bc'`,`bc1`,`cenv`,`TCNonTail`,`sz+1`
                               ,`bvl_bc f cenv TCNonTail sz cs [x]`]mp_tac) >>
      imp_res_tac bEval_IMP_LENGTH >>
      Cases_on`a`>>fs[LENGTH_NIL] >>
      imp_res_tac bEval_code >> simp[] >>
      Cases_on`res1`>>fs[] >- (
        rpt BasicProvers.VAR_EQ_TAC >>
        discharge_hyps >- (
          qpat_assum`bs2 = X`SUBST1_TAC >>
          imp_res_tac RTC_bc_next_preserves >> simp[] >>
          conj_tac >- (match_mp_tac good_env_cons >> rw[] ) >>
          simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
          fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
          fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
          spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        strip_tac >> simp[] >>
        qexists_tac`bs2'` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
        simp[bc_state_component_equality] >>
        first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
        imp_res_tac RTC_bc_next_preserves >>
        simp[bc_state_component_equality] ) >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >- (
        disch_then(qspecl_then[`sp`,`hdl`,`rst2`]mp_tac) >>
        discharge_hyps >- (
          qpat_assum`bs2 = X`SUBST1_TAC >>
          imp_res_tac RTC_bc_next_preserves >> simp[] >>
          conj_tac >- (match_mp_tac good_env_cons >> fs[] ) >>
          simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
          fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
          fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
          spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        strip_tac >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3'` >>
        `bs3 = bs3'` by (
          unabbrev_all_tac >> simp[bc_state_component_equality] >>
          imp_res_tac RTC_bc_next_preserves >> simp[] ) >>
        rw[] ) >>
      discharge_hyps >- (
        qpat_assum`bs2 = X`SUBST1_TAC >>
        imp_res_tac RTC_bc_next_preserves >> simp[] >>
        conj_tac >- (match_mp_tac good_env_cons >> fs[] ) >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      strip_tac >>
      qexists_tac`bs2'` >> simp[] >>
      metis_tac[transitive_def,RTC_TRANSITIVE] ) >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc'++bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
    simp[] >> fs[Once SWAP_REVERSE]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    reverse(rw[]) >> fs[] >- (
      fs[good_env_def,LIST_REL_EL_EQN] ) >>
    qmatch_assum_abbrev_tac`(pushret t s0).out = X` >>
    qspecl_then[`t`,`s0`]mp_tac pushret_append_out >>
    simp[Abbr`s0`,Abbr`X`,emit_def] >>
    Q.PAT_ABBREV_TAC`i = Stack X` >> rw[] >>
    fs[Once SWAP_REVERSE_SYM] >>
    `bc_fetch bs1 = SOME i` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[] >>
      qexists_tac`bc0`>>simp[Abbr`i`] ) >>
    mp_tac(Q.REFL `bc_eval1 bs1`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[Abbr`i`,bc_eval_stack_def,bump_pc_def] >>
    fs[good_env_def,LIST_REL_EL_EQN] >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[] >> strip_tac >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`(pushret t s0).out = X` >>
    qspecl_then[`t`,`s0`,`bs1`]mp_tac pushret_correct >>
    simp[Abbr`s0`,Abbr`X`,emit_def,Once SWAP_REVERSE] >>
    disch_then(qspec_then`cs.out`mp_tac) >> simp[Once SWAP_REVERSE] >>
    disch_then(qspec_then`bc0`mp_tac) >> simp[] >>
    first_x_assum(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
    simp[FILTER_APPEND,SUM_APPEND] >>
    disch_then(qspecl_then[`ret`,`rst1`]mp_tac) >>
    discharge_hyps >- (
      Cases_on`t`>>fs[] >> metis_tac[] ) >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`t`>>fs[bc_state_component_equality,pushret_def,emit_def] >>
    simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE,ADD1] >>
    rw[] ) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    fs[get_label_def] >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv t sz (emit (bvl_bc f cenv t sz
        (emit (bvl_bc f cenv TCNonTail sz cs1 [x1]) l1) [x3]) l2) [x2]) l3).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs1`,`[x1]`]strip_assume_tac bvl_bc_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv t sz (emit (bvl_bc f cenv t sz cs2 [x3]) l2) [x2]) l3).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv`,`t`,`sz`,`cs2`,`[x3]`]strip_assume_tac bvl_bc_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv t sz cs3 [x2]) l3).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv`,`t`,`sz`,`cs3`,`[x2]`]strip_assume_tac bvl_bc_append_out >>
    `∃res0 s0. bEval ([x1],env,s) = (res0,s0)` by metis_tac[pair_CASES] >> fs[] >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`l1++REVERSE bc'++l2++REVERSE bc''++l3++bc1`,`cenv`,`TCNonTail`,`sz`,`cs1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`sp`,`hdl`,`rst2`]mp_tac) >>
    discharge_hyps >- (
      unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      fs[EVERY_MEM,MEM_FILTER,is_Label_rwt,PULL_EXISTS] >>
      conj_tac >- (Cases_on`res0`>>fs[]) >>
      conj_tac >- (
        last_x_assum kall_tac >>
        last_x_assum kall_tac >>
        rw[] >> res_tac >> fs[] >> simp[] ) >>
      Cases_on`res0`>>fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      Cases_on`t`>>fs[] ) >>
    strip_tac >>
    Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    TRY( qexists_tac`bs2` >> simp[] >> NO_TAC ) >>
    imp_res_tac bEval_IMP_LENGTH >>
    Cases_on`a`>>fs[LENGTH_NIL] >>
    qpat_assum`bs2 = X`(fn th => assume_tac (EQ_MP (SYM (ISPEC (concl th) markerTheory.Abbrev_def)) th)) >> fs[] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    `bc_fetch bs2 = SOME (HD l1)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`,Abbr`l1`] >>
      unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      qexists_tac`bc0++REVERSE bc`>>simp[]) >>
    fs[Abbr`l1`] >>
    mp_tac(Q.REFL `bc_eval1 bs2`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def,bc_fetch_with_stack,bc_find_loc_def] >>
    Q.PAT_ABBREV_TAC`ptro = bc_find_loc_aux X Y Z 0` >>
    `ptro = SOME (next_addr bs1.inst_length (bc0 ++ REVERSE bc ++ [JumpIf(Lab cs.next_label)] ++ REVERSE bc' ++ l2))` by (
      unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH bc + LENGTH bc' + 2` >>
      simp[EL_APPEND1,EL_APPEND2,TAKE_APPEND1,TAKE_APPEND2] >>
      conj_tac >- (
        ntac 2 (last_x_assum kall_tac) >>
        unabbrev_all_tac >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] ) >>
    `∃b. h = Block b [] ∧ b < 2` by (
      qpat_assum`X = (res,Y)`mp_tac >> rw[] ) >>
    `bs2.stack = h::bs1.stack` by (
      simp[Abbr`bs2`,bvl_to_bc_value_def] ) >>
    simp[] >>
    IF_CASES_TAC >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
    fs[] >> rpt BasicProvers.VAR_EQ_TAC >- (
      first_x_assum(qspecl_then[`bs3`,`bc0++REVERSE bc++[JumpIf(Lab cs.next_label)]`,`REVERSE bc'`,`l2++REVERSE bc''++l3++bc1`,
                                `cenv`,`t`,`sz`,`cs2`]mp_tac) >>
      simp[] >>
      disch_then(qspecl_then[`ret`,`sp`,`hdl`,`rst1`,`rst2`]mp_tac) >>
      discharge_hyps >- (
        imp_res_tac bEval_code >>
        unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,MAP_REVERSE,SUM_REVERSE,SUM_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      disch_then(qx_choose_then`bs4`strip_assume_tac) >>
      Cases_on`res`>>fs[]>>
      TRY (
        TRY(qexists_tac`bs4`>>simp[])>>
        qmatch_abbrev_tac`bc_next^* bs1 bs4'` >>
        `bs4' = bs4` by (
          simp[Abbr`bs4'`,bc_state_component_equality,Abbr`bs3`] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      Cases_on`t`>>fs[] >>
      TRY (
        qmatch_abbrev_tac`bc_next^* bs1 bs4'` >>
        `bs4' = bs4` by (
          simp[Abbr`bs4'`,bc_state_component_equality,Abbr`bs3`,Abbr`bs2`] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      `bc_fetch bs4 = SOME(Jump(Lab (cs.next_label+1)))` by (
        match_mp_tac bc_fetch_next_addr >>
        imp_res_tac RTC_bc_next_preserves >>
        qpat_assum`bs4 = X`SUBST1_TAC >>
        simp[Abbr`bs3`] >>
        unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
        fs[Once(GSYM SWAP_REVERSE)] >>
        qexists_tac`bc0++REVERSE bc++[JumpIf(Lab cs.next_label)]++REVERSE bc'`>>simp[]) >>
      mp_tac(Q.REFL`bc_eval1 bs4`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def,bc_find_loc_def] >>
      Q.PAT_ABBREV_TAC`ptro = bc_find_loc_aux X Y Z 0` >>
      `ptro = SOME (next_addr bs1.inst_length (bc0 ++ REVERSE bc ++ [JumpIf(Lab cs.next_label)] ++ REVERSE bc' ++ l2 ++ REVERSE bc''++l3))` by (
        simp[Abbr`ptro`] >>
        qpat_assum`bs4 = X`SUBST1_TAC >>
        unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        qexists_tac`LENGTH bc0 + LENGTH bc + LENGTH bc' + LENGTH bc'' + 3` >>
        simp[EL_APPEND1,EL_APPEND2,TAKE_APPEND1,TAKE_APPEND2] >>
        conj_tac >- (
          simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
          fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
          fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
          spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
          rfs[] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
        simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE,TAKE_LENGTH_ID_rwt] ) >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
      qexists_tac`bs5` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      simp[Abbr`bs5`,bc_state_component_equality] >>
      qpat_assum`bs4 = X`SUBST1_TAC >>
      simp[Abbr`bs3`,Abbr`bs2`] >>
      unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
      fs[GSYM(Once SWAP_REVERSE)] ) >>
    `b = 1` by simp[] >> fs[] >> rw[] >>
    first_x_assum(qspecl_then[`bs3`,`bc0++REVERSE bc++[JumpIf(Lab cs.next_label)]++REVERSE bc'++l2`,`REVERSE bc''`,`l3++bc1`,
                              `cenv`,`t`,`sz`,`cs3`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`ret`,`sp`,`hdl`,`rst1`,`rst2`]mp_tac) >>
    discharge_hyps >- (
      imp_res_tac bEval_code >>
      unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,MAP_REVERSE,SUM_REVERSE,SUM_APPEND] >>
      fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
      fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
      spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    disch_then(qx_choose_then`bs4`strip_assume_tac) >>
    Cases_on`res`>>fs[]>>
    TRY (
      TRY(qexists_tac`bs4`>>simp[])>>
      qmatch_abbrev_tac`bc_next^* bs1 bs4'` >>
      `bs4' = bs4` by (
        simp[Abbr`bs4'`,bc_state_component_equality,Abbr`bs3`] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
    Cases_on`t`>>fs[] >>
    TRY (
      qmatch_abbrev_tac`bc_next^* bs1 bs4'` >>
      `bs4' = bs4` by (
        simp[Abbr`bs4'`,bc_state_component_equality,Abbr`bs3`,Abbr`bs2`] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
    qexists_tac`bs4` >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum SUBST1_TAC >>
    simp[bc_state_component_equality,Abbr`bs3`,Abbr`bs2`] >>
    unabbrev_all_tac >> rfs[FOLDL_emit_append_out] >>
    fs[GSYM(Once SWAP_REVERSE)] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval (xs,env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs`,`xs`]strip_assume_tac bvl_bc_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv1 t1 sz1 s1 [x2]) l1).out = REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv1`,`t1`,`sz1`,`s1`,`[x2]`]strip_assume_tac bvl_bc_append_out >>
    fs[FOLDL_emit_append_out] >>
    fs[Once (GSYM SWAP_REVERSE)] >>
    imp_res_tac bEval_code >>
    Cases_on`res0`>>fs[] >- (
      first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc' ++ l1 ++ bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
      simp[] >> strip_tac >>
      imp_res_tac RTC_bc_next_preserves >>
      imp_res_tac bEval_IMP_LENGTH >>
      first_x_assum(qspecl_then[`bs2`,`bc0++REVERSE bc`,`REVERSE bc'`,`l1++bc1`,`cenv1`,`t1`,`sz1`,`s1`]mp_tac) >>
      qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >> simp[] >>
      disch_then(qspecl_then[`ret`,`sp`,`hdl`,`case t of TCNonTail => bs2.stack | _ => rst1`,`rst2`]mp_tac) >>
      discharge_hyps >- (
        conj_tac >- (
          fs[good_env_def,LIST_REL_EL_EQN,Abbr`cenv1`,Abbr`sz1`] >> simp[] >>
          gen_tac >> strip_tac >>
          Cases_on`n < LENGTH a` >- (
            simp[EL_APPEND1,EL_REVERSE,PRE_SUB1,EL_MAP] ) >>
          first_x_assum(qspec_then`n-LENGTH a`mp_tac) >>
          simp[EL_APPEND2] ) >>
        REWRITE_TAC[Once CONJ_ASSOC] >>
        conj_tac >- (
          simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
          fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
          fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
          spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        conj_tac >- (
          qunabbrev_tac`t1` >>
          pop_assum SUBST1_TAC >>
          Cases_on`t`>>fs[] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`args`>>simp[]) >>
        pop_assum SUBST1_TAC >>
        Cases_on`res`>>fs[] >>
        Cases_on`t`>>fs[] >>
        qpat_assum`X = bs1.stack`(SUBST1_TAC o SYM) >>
        simp[]) >>
      strip_tac >>
      Cases_on`res`>>fs[] >- (
        Cases_on`t`>>fs[Abbr`t1`] >- (
          mp_tac(Q.REFL `bc_eval1 bs2'`) >>
          `bc_fetch bs2' = SOME (Stack(Pops (LENGTH a)))` by (
            match_mp_tac bc_fetch_next_addr >>
            pop_assum SUBST1_TAC >> simp[] >>
            imp_res_tac RTC_bc_next_preserves >> simp[] >>
            CONV_TAC(SWAP_EXISTS_CONV) >>
            qexists_tac`bc1`>>simp[] ) >>
          CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
          simp[bump_pc_def] >>
          imp_res_tac bEval_IMP_LENGTH >>
          Cases_on`a'`>>fs[LENGTH_NIL] >>
          qpat_assum`bs2' = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
          simp[bc_eval_stack_def,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
          simp[GSYM bc_eval1_thm] >> disch_then(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
          srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
          imp_res_tac RTC_bc_next_preserves >> fs[] >>
          srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,Abbr`l1`] ) >>
        imp_res_tac bEval_IMP_LENGTH >>
        Cases_on`a'`>>fs[LENGTH_NIL] >>
        srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
        imp_res_tac RTC_bc_next_preserves >> fs[] >>
        rfs[] ) >>
      imp_res_tac RTC_bc_next_preserves >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rfs[] >>
      first_assum(match_exists_tac o concl) >> simp[]) >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    first_x_assum match_mp_tac >> simp[] >>
    qexists_tac`bc0`>>simp[] >>
    qexists_tac`REVERSE bc` >> simp[] >>
    map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`] >> simp[] >>
    fs[] >>
    Cases_on`t`>>fs[] >>
    metis_tac[]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval ([x1],env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs`,`[x1]`]strip_assume_tac bvl_bc_append_out >>
    fs[FOLDL_emit_append_out] >>
    fs[Once (GSYM SWAP_REVERSE)] >>
    imp_res_tac bEval_code >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`[PopExc; Return] ++ bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
    simp[] >>
    Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    TRY (
      simp[PULL_EXISTS] >>
      Cases_on`t`>>fs[]>>
      metis_tac[]) >>
    imp_res_tac bEval_IMP_LENGTH >>
    Cases_on`a`>>fs[LENGTH_NIL] >>
    strip_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac RTC_bc_next_preserves >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    `bc_fetch bs2 = SOME PopExc` by (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      qexists_tac`bc0++REVERSE bc`>>simp[] >>
      qpat_assum`bs2 = X`SUBST1_TAC >> simp[] ) >>
    qpat_assum`X = bs1.handler`(assume_tac o SYM) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
    `EL (LENGTH bs1.stack - (LENGTH rst2 + 2)) bs1.stack = StackPtr sp ∧
     LENGTH rst2 + 1 < LENGTH bs1.stack ∧
     LASTN (LENGTH rst2 + 1) bs1.stack = CodePtr hdl::rst2` by (
      Cases_on`t`>>fs[] >>
      simp[EL_REVERSE,EL_APPEND1,EL_APPEND2,PRE_SUB1,TAKE_REVERSE,
           LASTN_APPEND1,LASTN_APPEND2,LASTN_CONS,LASTN_1] ) >>
    simp[EL_REVERSE,PRE_SUB1] >>
    qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
    `bc_fetch bs3 = SOME Return` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs3`] >>
      qexists_tac`bc0 ++ REVERSE bc ++ [PopExc]` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs3`] >>
    simp[TAKE_REVERSE,REVERSE_APPEND]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval ([x1],env,s1) = (res0,s0)` by metis_tac[pair_CASES] >>
    fs[get_label_def] >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv1 t1 sz1 (emit (pushret t (emit (bvl_bc f cenv TCNonTail sz2 s3 [x1]) l3)) l2) [x2]) l1).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz2`,`s3`,`[x1]`]strip_assume_tac bvl_bc_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv1 t1 sz1 (emit (pushret t s2) l2) [x2]) l1).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`t`,`s2`]strip_assume_tac pushret_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc f cenv1 t1 sz1 s4 [x2]) l1).out =
      REVERSE code ++ cs.out` >>
    qspecl_then[`f`,`cenv1`,`t1`,`sz1`,`s4`,`[x2]`]strip_assume_tac bvl_bc_append_out >>
    rfs[FOLDL_emit_append_out] >> fs[] >>
    mp_tac(Q.REFL`s4.out`) >>
    first_assum(fn th => CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(REWR_CONV(REWRITE_RULE[markerTheory.Abbrev_def]th)))))) >>
    simp[] >>
    qpat_assum`Abbrev(s2 = X)`(fn th => CONV_TAC(LAND_CONV(REWRITE_CONV[REWRITE_RULE[markerTheory.Abbrev_def]th])) >>
      assume_tac th) >> simp[] >>
    qpat_assum`Abbrev(s3 = X)`(fn th => CONV_TAC(LAND_CONV(REWRITE_CONV[REWRITE_RULE[markerTheory.Abbrev_def]th])) >>
      assume_tac th) >> simp[] >>
    strip_tac >> fs[Once (GSYM SWAP_REVERSE)] >>
    mp_tac(Q.REFL `bc_eval1 bs1`) >>
    `bc_fetch bs1 = SOME (PushPtr(Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      qexists_tac`bc0` >> simp[] ) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def,bc_find_loc_def] >>
    Q.PAT_ABBREV_TAC`ptro = bc_find_loc_aux X Y Z 0` >>
    `ptro = SOME (next_addr bs1.inst_length (bc0 ++ [PushPtr(Lab cs.next_label);PushExc] ++ REVERSE bc ++ l3 ++ REVERSE bc' ++ [HD l2]))` by (
      simp[Abbr`ptro`] >>
      ONCE_REWRITE_TAC[Q.SPECL[`x`,`y::(a++b)`]CONS_APPEND] >>
      ONCE_REWRITE_TAC[Q.SPECL[`x`,`(a++b)`]CONS_APPEND] >>
      REWRITE_TAC[APPEND_ASSOC] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + 2 + LENGTH bc + LENGTH l3 + LENGTH bc' + 1` >>
      simp[EL_APPEND1,EL_APPEND2,TAKE_APPEND1,TAKE_APPEND2] >>
      conj_tac >- (
        ntac 2 (last_x_assum kall_tac) >>
        unabbrev_all_tac >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      unabbrev_all_tac >> simp[] >>
      simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] ) >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs2 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    mp_tac(Q.REFL `bc_eval1 bs2`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
    first_x_assum(qspecl_then[`bs3`,`bc0++[PushPtr(Lab cs.next_label);PushExc]`,`REVERSE bc`,`l3++REVERSE bc'++l2++REVERSE bc''++l1++bc1`]mp_tac) >>
    `bs3.code = bs1.code` by simp[Abbr`bs3`,Abbr`bs2`] >>
    simp[] >>
    `∃hdl2. HD bs2.stack = CodePtr hdl2` by ( simp[Abbr`bs2`] ) >>
    disch_then(qspecl_then[`cenv`,`TCNonTail`,`sz2`,`s3`,`ret`,`bs1.handler`,`hdl2`,
      `bs3.stack`,`bs1.stack`]mp_tac) >>
      (*
      `case t of TCNonTail => bs3.stack | _ => rst1`,
      `bs1.stack`]mp_tac) >>
      *)
    discharge_hyps >- (
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`sz2`] >>
      conj_tac >- ( Cases_on`res0`>>fs[] ) >>
      conj_tac >- (
        `sz + 2 = (sz + 1) + 1` by simp[Abbr`sz1`] >>
        metis_tac[good_env_cons] ) >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      conj_tac >- (
        ntac 2 (last_x_assum kall_tac) >>
        unabbrev_all_tac >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      Cases_on`res0`>>fs[Abbr`l2`,ADD1] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[FILTER_APPEND,SUM_APPEND]) >>
    disch_then(qx_choose_then`bs4`strip_assume_tac) >> fs[] >>
    Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC>>fs[]>-(
      imp_res_tac bc_next_preserves_inst_length >>
      imp_res_tac RTC_bc_next_preserves >>
      `bc_fetch bs4 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        qpat_assum`bs4 = X`(fn th => SUBST1_TAC th >> assume_tac th) >> simp[] >>
        simp[Abbr`l3`] >>
        qexists_tac`bc0 ++ [PushPtr(Lab cs.next_label);PushExc]++REVERSE bc` >>
        simp[] ) >>
      mp_tac(Q.REFL`bc_eval1 bs4`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      qpat_assum`bs4 = X`(fn th => SUBST1_TAC th >> assume_tac th) >> simp[] >>
      imp_res_tac bEval_IMP_LENGTH >>
      Cases_on`a`>>fs[LENGTH_NIL] >>
      simp[Abbr`bs3`,EL_APPEND2,TAKE_APPEND2] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >> rfs[] >>
      qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
      qpat_assum`bs4 = X`(fn th => assume_tac (EQ_MP (SYM (ISPEC (concl th) markerTheory.Abbrev_def)) th)) >> fs[] >>
      qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
      `bc_fetch bs5 = SOME (Stack(Pops 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs5`,Abbr`l3`] >>
        qexists_tac`bc0 ++ [PushPtr(Lab cs.next_label);PushExc]++REVERSE bc++[PopExc]` >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      mp_tac(Q.REFL`bc_eval1 bs5`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
      simp[Abbr`bs5`,bc_eval_stack_def,Abbr`bs2`] >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
      qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs5' bs6` >>
      `bs5' = bs5` by ( unabbrev_all_tac >> simp[] ) >>
      qunabbrev_tac`bs5'` >> fs[] >> pop_assum kall_tac >>
      qspecl_then[`t`,`s2`]mp_tac pushret_correct >>
      simp[Once SWAP_REVERSE] >>
      simp[Abbr`s2`] >>
      disch_then(qspec_then`bs1`mp_tac) >>
      disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["bc0'","code"]))) >>
      disch_then(qspec_then`bc0`mp_tac) >> simp[] >>
      disch_then(qspec_then`PushPtr(Lab cs.next_label)::PushExc::(REVERSE bc ++ l3)`mp_tac) >> simp[] >>
      simp[Abbr`s3`] >>
      disch_then(qspec_then`bs6`mp_tac) >>
      simp[Abbr`bs6`] >>
      disch_then(qspecl_then[`ret`,`rst1`]mp_tac) >>
      discharge_hyps >- (
        conj_tac >- (
          qmatch_assum_abbrev_tac`bc_next bs5 bs6` >>
          `bc_next^* bs1 bs4` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,Abbr`l3`] >>
        Cases_on`t`>>fs[]>>metis_tac[]) >>
      disch_then(qx_choose_then`bs7`strip_assume_tac) >>
      reverse(Cases_on`t`)>>fs[] >- (
        qmatch_abbrev_tac`bc_next^* bs1 bs7'` >>
        `bs7' = bs7` by (
          unabbrev_all_tac >> simp[bc_state_component_equality] ) >>
        rw[] ) >>
      qpat_assum`bs7 = X`(fn th => assume_tac (EQ_MP (SYM (ISPEC (concl th) markerTheory.Abbrev_def)) th)) >> fs[] >>
      full_simp_tac std_ss [pushret_def] >>
      `bc' = []` by (
        ntac 2(qpat_assum`X.out = Y`kall_tac) >>
        qpat_assum`X.out = Y`mp_tac >>
        simp_tac(srw_ss())[]) >>
      fs[] >>
      `bc_fetch bs7 = SOME(Jump(Lab (cs.next_label +1)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs7`,Abbr`l2`] >>
        qexists_tac`bc0++[PushPtr(Lab cs.next_label);PushExc]++REVERSE bc++l3` >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      mp_tac(Q.REFL`bc_eval1 bs7`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >> pop_assum kall_tac >>
      simp[bc_find_loc_def,Abbr`bs7`] >>
      Q.PAT_ABBREV_TAC`ptro = bc_find_loc_aux X Y Z 0` >>
      `ptro = SOME (next_addr bs1.inst_length (bc0 ++ [PushPtr(Lab cs.next_label);PushExc] ++
                                               REVERSE bc ++ l3 ++ l2 ++ REVERSE bc'' ++ [HD l1]))` by (
        simp[Abbr`ptro`] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        qexists_tac`LENGTH bc0 + 2 + LENGTH bc + LENGTH l3 + LENGTH l2 + LENGTH bc'' + 1` >>
        simp[EL_APPEND1,EL_APPEND2,TAKE_APPEND1,TAKE_APPEND2,Abbr`l1`] >>
        unabbrev_all_tac >>
        simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
        fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
        fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
        rfs[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
      simp[GSYM bc_eval1_thm] >>
      qunabbrev_tac`ptro`>>pop_assum kall_tac >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs7 bs8` >>
      qexists_tac`bs8` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      simp[Abbr`bs8`,bc_state_component_equality] >>
      unabbrev_all_tac >> simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      rpt(qpat_assum`bc_fetch Y = X`kall_tac) >>
      qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
      qmatch_assum_abbrev_tac`Abbrev(SOME(next_addr il ls) = bc_find_loc_aux cc il nl 0)` >>
      first_x_assum(qspecl_then[`bs4`,`ls++(TL l2)`]mp_tac) >>
      imp_res_tac RTC_bc_next_preserves >>
      imp_res_tac bc_next_preserves_inst_length >>
      simp[] >>
      simp[Abbr`ls`] >>
      disch_then(qspec_then`REVERSE bc''`mp_tac) >>
      simp[Abbr`l2`] >>
      disch_then(qspecl_then[`cenv1`,`t1`,`sz1`,`s4`]mp_tac) >> simp[] >>
      disch_then(qspecl_then[`ret`,`sp`,`hdl`,`case t of TCNonTail => bs4.stack | _ => rst1`,`rst2`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bs4`,Abbr`cenv1`] >>
        imp_res_tac bEval_code >> simp[] >> fs[] >>
        fs[Abbr`bs2`] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        conj_tac >- (
          fs[good_env_def,LIST_REL_EL_EQN,Abbr`sz1`,ADD1] >> simp[] >>
          gen_tac >> strip_tac >>
          first_x_assum(qspec_then`n`mp_tac) >>
          simp[] >> simp[EL_CONS,PRE_SUB1] ) >>
        ONCE_REWRITE_TAC[CONJ_ASSOC] >>
        conj_tac >- (
          unabbrev_all_tac >>
          simp[FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
          fs[EVERY_REVERSE,EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_FILTER] >>
          fs[EVERY_MEM] >> rw[] >> fsrw_tac[ARITH_ss][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
          spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        simp[FILTER_APPEND,SUM_APPEND] >>
        conj_tac >- (
          Cases_on`t`>>fs[Abbr`t1`] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`args`>>simp[]) >>
        Cases_on`res`>>fs[] >>
        Cases_on`t`>>fs[]) >>
      disch_then(qx_choose_then`bs5`strip_assume_tac) >>
      Cases_on`res`>>TRY(
        qexists_tac`bs5`>>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        fs[bc_state_component_equality] >> NO_TAC) >>
      fs[] >>
      reverse(Cases_on`t`)>>fs[Abbr`t1`]>-(
        rw[] >>
        simp[Once RTC_CASES_RTC_TWICE] >>
        qexists_tac`bs4` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        qmatch_abbrev_tac`bc_next^* bs4 bs5` >>
        qmatch_assum_abbrev_tac`bc_next^* bs4 bs5'` >>
        `bs5' = bs5` by (
          simp[Abbr`bs5`,Abbr`bs5'`,bc_state_component_equality] >>
          simp[Abbr`bs4`] ) >>
        rw[] ) >>
      `bc_fetch bs5 = SOME (Stack(Pops 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        pop_assum SUBST1_TAC >> simp[] >>
        simp[Abbr`cc`] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`TL l1 ++ bc1` >>
        simp[Abbr`l1`] >>
        imp_res_tac RTC_bc_next_preserves >>
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      mp_tac(Q.REFL`bc_eval1 bs5`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      qpat_assum`bs5 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
      imp_res_tac bEval_IMP_LENGTH >>
      Cases_on`a`>>fs[LENGTH_NIL] >>
      simp[bc_eval_stack_def,Abbr`bs4`] >>
      simp[GSYM bc_eval1_thm] >>
      imp_res_tac RTC_bc_next_preserves >> fs[] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs5' bs6` >>
      `bs5' = bs5` by ( simp[Abbr`bs5'`] ) >>
      qexists_tac`bs6` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      simp[Abbr`bs6`,Abbr`bs3`,Abbr`bs2`] >>
      simp[bc_state_component_equality,Abbr`il`] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`l1`] ) >>
    qexists_tac`bs4` >> simp[] >>
    metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval (xs,env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs`,`xs`]strip_assume_tac bvl_bc_append_out >>
    fs[] >>
    fs[FOLDL_emit_append_out] >>
    qmatch_assum_abbrev_tac`(pushret t cs1).out = REVERSE code ++ cs.out` >>
    qspecl_then[`t`,`cs1`]strip_assume_tac pushret_append_out >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`DROP(LENGTH bc0+LENGTH bc)bs1.code`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`sp`,`hdl`,`rst2`]mp_tac) >>
    discharge_hyps >- (
      fs[Abbr`cs1`,Once(GSYM SWAP_REVERSE)] >>
      simp[DROP_APPEND1,DROP_LENGTH_NIL_rwt]  >>
      Cases_on`res0`>>fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      Cases_on`t`>>fs[]) >>
    strip_tac >>
    Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC>>fs[] >>
    TRY ( qexists_tac`bs2`>>simp[]>>NO_TAC) >>
    Cases_on`res`>>fs[] >>
    TRY (
      last_x_assum mp_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      NO_TAC ) >>
    Cases_on`bEvalOp op a s0`>>fs[]>>
    Cases_on`x`>>fs[]>>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    `∃bco. cs1.out = bco ++ bc ++ cs.out` by (
      simp[Abbr`cs1`] ) >>
    qsuff_tac`
      bc_next^* bs2
        (bs1 with <|
          stack := bvl_to_bc_value f q::bs1.stack;
          pc := next_addr bs1.inst_length (bc0++REVERSE bc++REVERSE bco);
          refs := refv_map (bvl_to_bc_value f) o_f r.refs;
          globals := MAP (OPTION_MAP (bvl_to_bc_value f)) r.globals;
          output := r.output;
          clock := SOME r.clock |>)` >- (
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
      qspecl_then[`t`,`cs1`]mp_tac pushret_correct >> simp[] >>
      disch_then(qspecl_then[`bs1`,`REVERSE bc'`]mp_tac) >> simp[] >>
      disch_then(qspec_then`cs.out`mp_tac) >>
      simp[Once(GSYM SWAP_REVERSE)] >>
      fs[Once(GSYM SWAP_REVERSE)] >>
      disch_then(qspec_then`bc0`mp_tac) >>
      simp[] >>
      disch_then(qspec_then`bs3`mp_tac) >> simp[] >>
      simp[Abbr`bs3`] >>
      disch_then(qspecl_then[`ret`,`rst1`]mp_tac) >>
      discharge_hyps >- (
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        Cases_on`t`>>fs[] >> metis_tac[] ) >>
      strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      Cases_on`t`>>fs[bc_state_component_equality] >>
      fs[pushret_def] >> rw[] ) >>
    qpat_assum`bs2 = X`(fn th => assume_tac (EQ_MP (SYM (ISPEC (concl th) markerTheory.Abbrev_def)) th)) >> fs[] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    Cases_on`op`>>Cases_on`a`>>fs[bEvalOp_def,Abbr`cs1`]
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Gread n)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      fs[get_global_def] >>
      qpat_assum`X = SOME (y,Z)`mp_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[Abbr`bs2`] >> simp[EL_MAP] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Galloc 1)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
      `bc_fetch bs3 = SOME (Stack(PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`,Abbr`bs2`] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`REVERSE bc' ++ bc1`>>simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs4`,Abbr`bs2`,bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[SUM_APPEND,FILTER_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Gupdate n)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[] >>
      fs[get_global_def] >>
      qpat_assum`X = SOME (y,Z)`mp_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,EL_MAP,LUPDATE_MAP] >>
      qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
      `bc_fetch bs3 = SOME (Stack(PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`REVERSE bc' ++ bc1`>>simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs4`,bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[SUM_APPEND,FILTER_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack(PushInt(&LENGTH xs)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
      `bc_fetch bs3 = SOME (Stack(Cons n))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`REVERSE bc' ++ bc1`>>simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      imp_res_tac bEval_IMP_LENGTH >> fs[LENGTH_NIL] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs4`,bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[SUM_APPEND,FILTER_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack(PushInt(&LENGTH xs)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
      `bc_fetch bs3 = SOME (Stack(Cons n))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`REVERSE bc' ++ bc1`>>simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      imp_res_tac bEval_IMP_LENGTH >> fs[] >> simp[] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs4`,bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[TAKE_APPEND2,DROP_APPEND2,ADD1] >>
      simp[SUM_APPEND,FILTER_APPEND] >>
      srw_tac[ETA_ss][])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack El)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def,EL_MAP] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack LengthBlock)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME Length` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME LengthByte` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME RefByte` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      fs[LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,wordsTheory.dimword_8] >>
      conj_tac >- COOPER_TAC >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      simp[fmap_eq_flookup,FLOOKUP_o_f,FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME Ref` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      fs[LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      simp[fmap_eq_flookup,FLOOKUP_o_f,FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM,map_replicate])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME DerefByte` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      conj_tac >- COOPER_TAC >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      Cases_on`h''`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME UpdateByte` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2);Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      conj_asm1_tac >- COOPER_TAC >>
      conj_tac >- (simp[wordsTheory.dimword_8]>>COOPER_TAC) >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack (Pops 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2);Stack(Load 2);UpdateByte]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs3`,bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM,FLOOKUP_o_f])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack (PushInt i))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack (TagEq n))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      Cases_on`t'`>>fs[]>>
      `bc_fetch bs2 = SOME (Stack IsBlock)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      Cases_on`h`>>fs[bvl_to_bc_value_def,bc_eval_stack_def] >>
      rw[bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Equal)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      simp[bc_equal_bvl_to_bc_value,bc_eval_stack_def] >>
      BasicProvers.CASE_TAC >> fs[] >> rw[bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack (PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(PushInt(&LENGTH xs)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(PushInt 0)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME Ref` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(PushInt 0);Stack(PushInt(&LENGTH xs))]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      qspecl_then[`LENGTH xs`,`bs2`,`bc0++REVERSE bc++[Stack(PushInt 0);Stack(PushInt(&LENGTH xs));Ref]`]mp_tac bvl_bc_ref_correct >>
      simp[Abbr`bs2`] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      imp_res_tac bEval_IMP_LENGTH >> fs[LENGTH_NIL] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[REPLICATE,FLOOKUP_UPDATE] >>
      discharge_hyps >- (
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      strip_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
      `bs2' = bs2` by (
        unabbrev_all_tac >> simp[bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      `bs3' = bs3` by (
        unabbrev_all_tac >> simp[bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] >> fs[LET_THM] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        simp[bvl_to_bc_value_def,ADD1,bvl_bc_ref_def] >>
        simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
        rw[] >> simp[] >>
        simp[DOMSUB_FLOOKUP_THM,FLOOKUP_o_f]) >>
      rw[])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack (PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(PushInt(&LENGTH xs)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(PushInt 0)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME Ref` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(PushInt 0);Stack(PushInt(&LENGTH xs))]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`] >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      qspecl_then[`LENGTH xs`,`bs2`,`bc0++REVERSE bc++[Stack(PushInt 0);Stack(PushInt(&LENGTH xs));Ref]`]mp_tac bvl_bc_ref_correct >>
      simp[Abbr`bs2`] >>
      fs[GSYM(Once SWAP_REVERSE)] >>
      imp_res_tac bEval_IMP_LENGTH >> fs[] >>
      disch_then(qspec_then`REVERSE(MAP(bvl_to_bc_value f)t')++[bvl_to_bc_value f h]`mp_tac) >>
      simp[] >>
      simp[FLOOKUP_UPDATE] >>
      discharge_hyps >- (
        simp[FILTER_APPEND,SUM_APPEND,LENGTH_REPLICATE] ) >>
      strip_tac >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
      `bs2' = bs2` by (
        unabbrev_all_tac >> simp[bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      `bs3' = bs3` by (
        unabbrev_all_tac >> simp[bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] >> fs[LET_THM] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        simp[bvl_to_bc_value_def,ADD1] >>
        simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] >>
        simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
        simp[REPLICATE_GENLIST,DROP_LENGTH_NIL_rwt] >>
        rw[] >> simp[] >>
        simp[DOMSUB_FLOOKUP_THM,FLOOKUP_o_f]) >>
      rw[])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Deref)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      conj_asm1_tac >- COOPER_TAC >>
      simp[EL_MAP] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] )
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      Cases_on`t'`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`FLOOKUP s0.refs n`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack(Load 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME Update` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2);Stack(Load 2)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bvl_to_bc_value_def,FLOOKUP_o_f] >>
      conj_asm1_tac >- COOPER_TAC >>
      simp[LUPDATE_MAP] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Stack (Pops 2))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 2);Stack(Load 2);Stack(Load 2);Update]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs3`,bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM,FLOOKUP_o_f] >>
      rw[LUPDATE_MAP])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (PushPtr(Addr (tlookup f n)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_find_loc_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs2`,bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack(Load 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`bv_to_string h`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def] >>
      qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_fetch bs2 = SOME (Print)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc++[Stack(Load 0)]` >>
        fs[GSYM(Once SWAP_REVERSE)] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bv_to_string_bvl_to_bc_value] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs3`,bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (PrintC c)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
      `bc_fetch bs3 = SOME (Stack(PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        qexists_tac`bc0++REVERSE bc++[PrintC c]` >>
        fs[GSYM(Once SWAP_REVERSE),Abbr`bs2`] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`bs4`,Abbr`bs2`,bc_state_component_equality,bvl_to_bc_value_def] >>
      simp[FILTER_APPEND,SUM_APPEND,IMPLODE_EXPLODE_I])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Add)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Sub)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Mult)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Div)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Mod)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])
    >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      `bc_fetch bs2 = SOME (Stack Less)` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE bc` >>
        fs[GSYM(Once SWAP_REVERSE)] ) >>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t''`>>fs[]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs2`,bc_eval_stack_def,bvl_to_bc_value_def] >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND])) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >- (
      qexists_tac`bs1` >> simp[] >>
      qspecl_then[`f`,`cenv`,`t`,`sz`,`emit cs [Tick]`,`[x]`]strip_assume_tac bvl_bc_append_out >>
      fs[emit_def] >>
      match_mp_tac bc_fetch_next_addr >>
      simp[] >> qexists_tac`bc0`>>simp[] >>
      fs[Once (GSYM SWAP_REVERSE)] ) >>
    qspecl_then[`f`,`cenv`,`t`,`sz`,`emit cs [Tick]`,`[x]`]strip_assume_tac bvl_bc_append_out >> fs[] >>
    fs[Once(GSYM SWAP_REVERSE),emit_def] >>
    mp_tac(Q.REFL `bc_eval1 bs1`) >>
    `bc_fetch bs1 = SOME Tick` by (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      qexists_tac`bc0` >> simp[] ) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >>
    simp[GSYM bc_eval1_thm] >>
    disch_then(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
    srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    imp_res_tac RTC_bc_next_preserves >>
    first_x_assum(qspecl_then[`bs2`,`bc0++[Tick]`,`REVERSE bc`]mp_tac) >> simp[] >>
    simp[Abbr`bs2`,dec_clock_def,SUM_APPEND,FILTER_APPEND] >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(qspecl_then[`t`,`cs with out := Tick::cs.out`]mp_tac) >>
    simp[] ) >>
  simp[bEval_def,bvl_bc_def] >> rw[] >>
  `∃res0 s0. bEval (xs,env,s1) = (res0,s0)` by metis_tac[pair_CASES] >>
  qspecl_then[`f`,`cenv`,`TCNonTail`,`sz`,`cs`,`xs`]strip_assume_tac bvl_bc_append_out >> fs[] >>
  first_x_assum(qspecl_then[`bs1`,`bc0`]mp_tac) >> simp[] >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["cenv'","t'","sz'","cs'"]))) >>
  disch_then(qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >> simp[] >>
  simp[Once SWAP_REVERSE] >>
  `∃bc11. code ++ bc1 = REVERSE bc ++ Tick::bc11` by (
    Cases_on`t`>>Cases_on`dest`>>fs[FOLDL_emit_append_out,Once(GSYM SWAP_REVERSE)] ) >>
  simp[] >>
  disch_then(qspecl_then[`sp`,`hdl`,`rst2`]mp_tac) >>
  discharge_hyps >- (
    Cases_on`res0`>>fs[] >> rw[] >> fs[] >>
    Cases_on`t`>>fs[]) >>
  strip_tac >>
  imp_res_tac RTC_bc_next_preserves >>
  Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC>>fs[] >- (
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    Cases_on`find_code dest a s0.code`>>fs[] >>
    `∃args exp. x = (args,exp)` by metis_tac[pair_CASES] >> fs[] >>
    `bc_fetch bs2 = SOME Tick` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE bc` >> simp[]) >>
    Cases_on`s0.clock = 0`>>fs[] >- (
      rw[] >>
      qexists_tac`bs2`>>simp[]>>
      simp[Abbr`bs2`]) >>
    fs[dec_clock_def] >>
    Cases_on`dest`>>fs[find_code_def] >- (
      Cases_on`t`>>fs[FOLDL_emit_append_out] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      Q.ISPEC_THEN`a`FULL_STRUCT_CASES_TAC SNOC_CASES >> fs[] >>
      Cases_on`x`>>fs[] >>
      Cases_on`lookup n s0.code`>>fs[] >>
      `∃arity exp. x = (arity,exp)` by metis_tac[pair_CASES] >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[ADD1] >> rpt BasicProvers.VAR_EQ_TAC >>
      mp_tac(Q.REFL`bc_eval1 bs2`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      simp[Abbr`bs2`,GSYM bc_eval1_thm] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      `bc_fetch bs3 = SOME (Stack(Load 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        qexists_tac`bc0 ++ REVERSE bc ++ [Tick]` >> simp[] >>
        fs[GSYM(Once SWAP_REVERSE)] >> rw[] >> fs[] >> rw[] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      mp_tac(Q.REFL`bc_eval1 bs3`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def,REVERSE_SNOC,MAP_SNOC,GSYM bc_eval1_thm] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs3 bs4` >>
      qpat_assum`bc_fetch X = Y`kall_tac >> fs[REVERSE_SNOC,MAP_SNOC] >>
      rator_assum`good_code_env`mp_tac >>
      simp_tac std_ss [good_code_env_def] >>
      disch_then(qspec_then`n`mp_tac) >>
      imp_res_tac bEval_code >> fs[] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`(bvl_bc f cenv1 t1 sz1 cs1 [exp]).out = cc ++ cs1.out` >>
      qpat_assum`X = Y ++ l1`(assume_tac o SYM) >- (
        `bc_fetch bs4 = SOME CallPtr` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs4`] >>
          qexists_tac`bc0 ++ REVERSE bc ++ [Tick;Stack(Load 0)]` >> simp[] >>
          fs[GSYM(Once SWAP_REVERSE)] >> rw[] >> fs[] >> rw[] >>
          simp[SUM_APPEND,FILTER_APPEND]) >>
        mp_tac(Q.REFL`bc_eval1 bs4`) >>
        CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
        simp[bump_pc_def] >>
        qpat_assum`bc_fetch X = Y`kall_tac >>
        simp[Abbr`bs4`,GSYM bc_eval1_thm,bvl_to_bc_value_def] >>
        strip_tac >>
        qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
        first_x_assum(qspecl_then[`bs5`,`l0`,`REVERSE cc`,`l1`,`cenv1`,`t1`,`sz1`,`cs1`]mp_tac) >>
        simp[] >>
        `∃ret1. HD(TL bs5.stack) = CodePtr ret1` by ( simp[Abbr`bs5`] ) >>
        disch_then(qspecl_then[`ret1`,`sp`,`hdl`,`bs1.stack`,`rst2`]mp_tac) >>
        discharge_hyps >- (
          simp[Abbr`bs5`] >>
          conj_tac >- (
            simp[Abbr`sz1`,Abbr`cenv1`] >>
            simp[good_env_def,LIST_REL_EL_EQN,EL_CONS,PRE_SUB1,EL_APPEND1] >>
            simp[EL_REVERSE,EL_MAP] ) >>
          (* conj_tac >- ( *)
            simp[Abbr`t1`] >>
            qexists_tac`[CodePtr (next_addr bs1.inst_length l0)]` >>
            simp[] >> fs[] (* ) >>
          Cases_on`res`>>fs[] *) ) >>
        disch_then(qx_choose_then`bs6`strip_assume_tac) >>
        rw[] >> fs[Abbr`t1`] >>
        Cases_on`res`>>fs[] >- (
          imp_res_tac bEval_IMP_LENGTH >>
          Cases_on`a`>>fs[LENGTH_NIL] >>
          qexists_tac`bs6` >>
          fs[bvl_to_bc_value_def] >>
          conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
          simp[Abbr`bs5`,bc_state_component_equality] >> fs[] >> rw[] >>
          fs[Once(GSYM SWAP_REVERSE)] >>
          simp[FILTER_APPEND,SUM_APPEND] ) >>
        TRY(qexists_tac`bs6`)>>
        fs[bvl_to_bc_value_def] >>
        qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
        `bs6' = bs6` by (
          simp[Abbr`bs6'`,bc_state_component_equality] >>
          imp_res_tac RTC_bc_next_preserves >>
          imp_res_tac bc_next_preserves_inst_length >>
          simp[Abbr`bs5`] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      `bc_fetch bs4 = SOME (Stack(Load(LENGTH ig + LENGTH xs + 1)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs4`] >>
        qexists_tac`bc0 ++ REVERSE bc ++ [Tick;Stack(Load 0)]` >> simp[] >>
        fs[GSYM(Once SWAP_REVERSE)] >> rw[] >> fs[] >> rw[] >>
        simp[SUM_APPEND,FILTER_APPEND]) >>
      mp_tac(Q.REFL`bc_eval1 bs4`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      imp_res_tac bEval_IMP_LENGTH >> fs[] >>
      simp[Abbr`bs4`,bc_eval_stack_def,ADD1,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,Abbr`sz1`] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
      `bc_fetch bs5 = SOME (Stack(Store 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs5`] >>
        qexists_tac`bc0 ++ REVERSE bc ++ [Tick;Stack(Load 0);Stack(Load(LENGTH ig + SUC(LENGTH args)+1))]` >> simp[] >>
        fs[GSYM(Once SWAP_REVERSE)] >> rw[] >> fs[] >> rw[] >>
        simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
      mp_tac(Q.REFL`bc_eval1 bs5`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      simp[Abbr`bs5`,bc_eval_stack_def] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_assum_abbrev_tac`bc_next bs5 bs6` >>
      `bc_fetch bs6 = SOME (Stack(PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs6`] >>
        qexists_tac`bc0 ++ REVERSE bc ++ [Tick;Stack(Load 0);Stack(Load(LENGTH ig + SUC(LENGTH args)+1));Stack(Store 1)]` >> simp[] >>
        fs[GSYM(Once SWAP_REVERSE)] >> rw[] >> fs[] >> rw[] >>
        simp[SUM_APPEND,FILTER_APPEND,ADD1]) >>
      mp_tac(Q.REFL`bc_eval1 bs6`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >> simp[bc_eval_stack_def] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      qmatch_assum_abbrev_tac`bc_next bs6 bs7` >>
      qspecl_then[`(LENGTH args)+3`,`LENGTH args'+(LENGTH ig+1)`,`bs7`]mp_tac stackshift_thm >>
      `bs7.code = bs1.code` by simp[Abbr`bs7`,Abbr`bs6`] >>
      simp[] >>
      fs[Once(GSYM SWAP_REVERSE)] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      disch_then(qspec_then`Return::bc1`mp_tac o (CONV_RULE SWAP_FORALL_CONV)) >>
      simp[ADD1] >>
      disch_then(qspec_then`TAKE (LENGTH args+3) bs7.stack`mp_tac) >>
      simp[Abbr`bs7`,Abbr`bs6`,TAKE_APPEND1,TAKE_LENGTH_ID_rwt] >>
      disch_then(qspec_then`rst1`mp_tac o (CONV_RULE SWAP_FORALL_CONV)) >>
      simp[] >>
      discharge_hyps >- (
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`bc_next bs5 bs6` >>
      qmatch_assum_abbrev_tac`bc_next bs6 bs7` >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs7' bs8` >>
      `bs7' = bs7` by (
        simp[Abbr`bs7'`,Abbr`bs7`,bc_state_component_equality] >>
        simp[Abbr`bs6`] >> simp[SUM_APPEND,FILTER_APPEND] ) >>
      qunabbrev_tac`bs7'`>>fs[] >> pop_assum kall_tac >>
      `bc_fetch bs8 = SOME Return` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs8`] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`bc1`>>simp[] >>
        simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
      mp_tac(Q.REFL`bc_eval1 bs8`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      simp[Abbr`bs8`,bvl_to_bc_value_def] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      fs[bvl_to_bc_value_def] >>
      qmatch_assum_abbrev_tac`bc_next bs8 bs9` >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      first_x_assum(qspecl_then[`bs9`,`l0`,`REVERSE cc`,`l1`,`cenv1`,`t1`,`LENGTH args+2`,`cs1`]mp_tac) >>
      simp[] >>
      disch_then(qspecl_then[`ret`,`sp`,`hdl`,`rst1`,`rst2`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bs9`] >>
        conj_tac >- (
          simp[Abbr`cenv1`] >>
          simp[good_env_def,LIST_REL_EL_EQN,EL_CONS,PRE_SUB1,EL_APPEND1] >>
          simp[EL_REVERSE,EL_MAP] ) >>
        (* conj_tac >- ( *)
          simp[Abbr`t1`] >>
          qexists_tac`[Number 0]` >>
          simp[] >> fs[] (* ) >>
        Cases_on`res`>>fs[]*) ) >>
      disch_then(qx_choose_then`bs10`strip_assume_tac) >>
      rw[] >> fs[Abbr`t1`] >>
      `bc_next^* bs1 bs10` by (
        qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
        qmatch_assum_abbrev_tac`bc_next^* bs7 bs8'` >>
        `bs2' = bs2` by (
          unabbrev_all_tac >> simp[bc_state_component_equality] ) >>
        `bs8' = bs8` by (
          unabbrev_all_tac >> simp[bc_state_component_equality] ) >>
        `bc_next^* bs1 bs5` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      Cases_on`res`>>fs[] >- (
        imp_res_tac bEval_IMP_LENGTH >>
        Cases_on`a`>>fs[LENGTH_NIL] >>
        qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
        `bs6' = bs10` by (
          simp[Abbr`bs6'`,bc_state_component_equality] >>
          imp_res_tac RTC_bc_next_preserves >>
          imp_res_tac bc_next_preserves_inst_length >>
          simp[Abbr`bs9`,Abbr`bs8`] ) >>
        rw[] ) >>
      TRY(qexists_tac`bs10`>>simp[])>>
      qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
      `bs6' = bs10` by (
        simp[Abbr`bs6'`,bc_state_component_equality] >>
        imp_res_tac RTC_bc_next_preserves >>
        imp_res_tac bc_next_preserves_inst_length >>
        simp[Abbr`bs9`,Abbr`bs8`] ) >>
      rw[]) >>
    rw[] >>
    Cases_on`lookup x' s0.code`>>fs[] >>
    qmatch_assum_rename_tac`lookup n s0.code = _` >>
    `∃args exp. x = (args,exp)` by metis_tac[pair_CASES] >> fs[] >>
    rw[] >>
    rator_assum`good_code_env`mp_tac >>
    simp_tac std_ss [good_code_env_def] >>
    disch_then(qspec_then`n`mp_tac) >>
    imp_res_tac bEval_code >> fs[] >> strip_tac >>
    qmatch_assum_abbrev_tac`(bvl_bc f cenv1 t1 sz1 cs1 [exp]).out = cc ++ cs1.out` >>
    qpat_assum`X = Y ++ l1`(assume_tac o SYM) >>
    Cases_on`t`>>fs[FOLDL_emit_append_out] >>
    fs[Once(GSYM SWAP_REVERSE)] >> rw[] >>
    mp_tac(Q.REFL`bc_eval1 bs2`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >>
    simp[Abbr`bs2`,GSYM bc_eval1_thm] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
    qpat_assum`bc_fetch X = Y`kall_tac >- (
      `bc_fetch bs3 = SOME(Stack(PushInt 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        qexists_tac`bc0++REVERSE bc++[Tick]` >> simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      mp_tac(Q.REFL`bc_eval1 bs3`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def] >>
      simp[Abbr`bs3`,bc_eval_stack_def] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs3 bs4` >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      `bc_fetch bs4 = SOME(Call(Addr (tlookup f n)))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs4`] >>
        qexists_tac`bc0++REVERSE bc++[Tick;Stack(PushInt 0)]` >> simp[] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      mp_tac(Q.REFL`bc_eval1 bs4`) >>
      CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
      simp[bump_pc_def,bc_find_loc_def] >>
      simp[Abbr`bs4`] >>
      simp[GSYM bc_eval1_thm] >> strip_tac >>
      qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
      qpat_assum`bc_fetch X = Y`kall_tac >>
      first_x_assum(qspecl_then[`bs5`,`l0`,`REVERSE cc`,`l1`,`cenv1`,`t1`,`sz1`,`cs1`]mp_tac) >>
      simp[] >>
      `∃ret1. HD(TL bs5.stack) = CodePtr ret1` by ( simp[Abbr`bs5`] ) >>
      disch_then(qspecl_then[`ret1`,`sp`,`hdl`,`bs1.stack`,`rst2`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bs5`] >>
        conj_tac >- (
          simp[Abbr`sz1`,Abbr`cenv1`] >>
          simp[good_env_def,LIST_REL_EL_EQN,EL_CONS,PRE_SUB1,EL_APPEND1] >>
          simp[EL_REVERSE,EL_MAP] ) >>
        simp[Abbr`t1`] >>
        qexists_tac`[Number 0]` >>
        simp[] >> fs[] ) >>
      disch_then(qx_choose_then`bs6`strip_assume_tac) >>
      rw[] >> fs[Abbr`t1`] >>
      Cases_on`res`>>fs[] >- (
        imp_res_tac bEval_IMP_LENGTH >>
        Cases_on`a'`>>fs[LENGTH_NIL] >>
        qexists_tac`bs6` >>
        fs[bvl_to_bc_value_def] >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        simp[Abbr`bs5`,bc_state_component_equality] >> fs[] >> rw[] >>
        fs[Once(GSYM SWAP_REVERSE)] >>
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      TRY(qexists_tac`bs6`)>>
      fs[bvl_to_bc_value_def] >>
      qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
      `bs6' = bs6` by (
        simp[Abbr`bs6'`,bc_state_component_equality] >>
        imp_res_tac RTC_bc_next_preserves >>
        imp_res_tac bc_next_preserves_inst_length >>
        simp[Abbr`bs5`] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
    `bc_fetch bs3 = SOME (Stack(Load(LENGTH ig + LENGTH xs)))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs3`] >>
      qexists_tac`bc0 ++ REVERSE bc ++ [Tick]` >> simp[] >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    mp_tac(Q.REFL`bc_eval1 bs3`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >>
    imp_res_tac bEval_IMP_LENGTH >> fs[] >>
    simp[Abbr`bs3`,bc_eval_stack_def,ADD1,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,Abbr`sz1`] >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    qmatch_assum_abbrev_tac`bc_next bs3 bs4` >>
    `bc_fetch bs4 = SOME (Stack(PushInt 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs4`] >>
      qexists_tac`bc0 ++ REVERSE bc ++ [Tick;Stack(Load(LENGTH ig + (LENGTH a)))]` >> simp[] >>
      simp[SUM_APPEND,FILTER_APPEND,ADD1]) >>
    mp_tac(Q.REFL`bc_eval1 bs4`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >> simp[bc_eval_stack_def] >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
    qspecl_then[`(LENGTH a)+2`,`LENGTH args+(LENGTH ig+1)`,`bs5`]mp_tac stackshift_thm >>
    `bs5.code = bs1.code` by simp[Abbr`bs5`,Abbr`bs4`] >>
    simp[] >>
    disch_then(qspec_then`(Jump(Addr (tlookup f n)))::bc1`mp_tac o (CONV_RULE SWAP_FORALL_CONV)) >>
    simp[ADD1] >>
    disch_then(qspec_then`TAKE (LENGTH a+2) bs5.stack`mp_tac) >>
    simp[Abbr`bs5`,Abbr`bs4`,TAKE_APPEND1,TAKE_LENGTH_ID_rwt] >>
    disch_then(qspec_then`rst1`mp_tac o (CONV_RULE SWAP_FORALL_CONV)) >>
    simp[] >>
    discharge_hyps >- (
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac`bc_next bs3 bs4` >>
    qmatch_assum_abbrev_tac`bc_next bs4 bs5` >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs6` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5'`,Abbr`bs5`,bc_state_component_equality] >>
      simp[Abbr`bs4`] >> simp[SUM_APPEND,FILTER_APPEND] ) >>
    qunabbrev_tac`bs5'`>>fs[] >> pop_assum kall_tac >>
    `bc_fetch bs6 = SOME (Jump(Addr(tlookup f n)))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs6`] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc1`>>simp[]) >>
    mp_tac(Q.REFL`bc_eval1 bs6`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def,bc_find_loc_def] >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs6 bs7` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    first_x_assum(qspecl_then[`bs7`,`l0`,`REVERSE cc`,`l1`,`cenv1`,`t1`,`LENGTH a+2`,`cs1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`ret`,`sp`,`hdl`,`rst1`,`rst2`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bs7`,Abbr`bs6`] >>
      conj_tac >- (
        simp[Abbr`cenv1`] >>
        simp[good_env_def,LIST_REL_EL_EQN,EL_CONS,PRE_SUB1,EL_APPEND1] >>
        simp[EL_REVERSE,EL_MAP] ) >>
      conj_tac >- (
        rator_assum`good_code_env`mp_tac >>
        simp_tac(std_ss++ARITH_ss)[] ) >>
      simp[Abbr`t1`] >>
      qexists_tac`[Number 0]` >>
      simp[] >> fs[] ) >>
    disch_then(qx_choose_then`bs8`strip_assume_tac) >>
    rw[] >> fs[Abbr`t1`] >>
    `bc_next^* bs1 bs8` by (
      qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
      `bs2' = bs2` by (
        unabbrev_all_tac >> simp[bc_state_component_equality] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
    Cases_on`res`>>fs[] >- (
      imp_res_tac bEval_IMP_LENGTH >>
      Cases_on`a'`>>fs[LENGTH_NIL] >>
      qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
      `bs6' = bs8` by (
        simp[Abbr`bs6'`,bc_state_component_equality] >>
        imp_res_tac RTC_bc_next_preserves >>
        imp_res_tac bc_next_preserves_inst_length >>
        simp[Abbr`bs7`,Abbr`bs6`,Abbr`bs5`,Abbr`bs4`,Abbr`bs2`] ) >>
      rw[] ) >>
    TRY(qexists_tac`bs8`>>simp[])>>
    qmatch_abbrev_tac`bc_next^* bs1 bs6'` >>
    `bs6' = bs8` by (
      simp[Abbr`bs6'`,bc_state_component_equality] >>
      imp_res_tac RTC_bc_next_preserves >>
      imp_res_tac bc_next_preserves_inst_length >>
      unabbrev_all_tac >> simp[]) >>
    rw[]) >>
  qexists_tac`bs2`>>simp[])

val bvl_bc_ptrfun_def = Define`
  bvl_bc_ptrfun il ptr (arity,exp) (f,s) =
     let f = insert ptr (next_addr il (REVERSE s.out)) f in
     let s = bvl_bc LN (GENLIST SUC arity) (TCTail arity 1) (arity+2) s [exp] in
       (f,s)`

val bvl_bc_ptrfun_domain = prove(
  ``∀ls.
      let (f,s) = FOLDR (UNCURRY (bvl_bc_ptrfun il)) (f0,s0) ls in
      domain f = domain f0 ∪ set(MAP FST ls)``,
  Induct >> simp[] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o concl) >> fs[] >>
  simp[bvl_bc_ptrfun_def] >>
  simp[pred_setTheory.EXTENSION] >>
  metis_tac[])

val bvl_bc_ptrfun_correct = prove(
  ``∀ls.
      ALL_DISTINCT (MAP FST ls) ∧
      ALL_DISTINCT (FILTER is_Label s0.out) ∧
      EVERY (combin$C $< s0.next_label o dest_Label) (FILTER is_Label s0.out)
      ⇒
      let (f,s) = FOLDR (UNCURRY (bvl_bc_ptrfun il)) (f0,s0) ls in
        ALL_DISTINCT (FILTER is_Label s.out) ∧
        (∃code.
           code ++ s0.out = s.out ∧
           EVERY (between s0.next_label s.next_label o dest_Label) (FILTER is_Label code) ∧
           s0.next_label ≤ s.next_label) ∧
        ∀ptr exp arity.
          MEM (ptr,(arity,exp)) ls ⇒
            ∃cs l0 cc l1.
              (bvl_bc LN (GENLIST SUC arity) (TCTail arity 1) (arity + 2) cs [exp]).out = cc ++ cs.out ∧
              EVERY (combin$C $< cs.next_label o dest_Label)
                (FILTER is_Label l0) ∧ ALL_DISTINCT (FILTER is_Label l0) ∧
              (REVERSE s.out = l0 ++ REVERSE cc ++ l1) ∧
              tlookup f ptr = next_addr il l0``,
  Induct >> simp[] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  simp[] >> rw[] >> fs[] >>
  Cases_on`FOLDR (UNCURRY (bvl_bc_ptrfun il)) (f0,s0) ls` >> fs[LET_THM] >>
  simp[bvl_bc_ptrfun_def] >>
  simp[PULL_FORALL] >> rpt gen_tac >>
  specl_args_of_then``bvl_bc``bvl_bc_append_out strip_assume_tac >>
  conj_tac >- (
    qpat_assum`X = r.out`(assume_tac o SYM) >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_FILTER,is_Label_rwt,between_def] >>
    rw[]>>res_tac>>rfs[]>>spose_not_then strip_assume_tac>>fsrw_tac[ARITH_ss][]>>
    res_tac>>fsrw_tac[ARITH_ss][]) >>
  conj_tac >- (
    qpat_assum`X = r.out`(assume_tac o SYM) >> simp[] >>
    fs[EVERY_MEM,between_def,MEM_MAP,PULL_EXISTS,FILTER_APPEND] >>
    fs[MEM_FILTER,is_Label_rwt,PULL_EXISTS] >> rw[] >> simp[] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  reverse strip_tac >- (
    res_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[] >>
    simp[tlookup_def,lookup_insert] >> rw[] >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[tlookup_def] ) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qexists_tac`r`>> fs[] >>
  simp[tlookup_def] >>
  qexists_tac`REVERSE r.out`>>simp[] >>
  simp[FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_REVERSE] >>
  qpat_assum`X = r.out`(assume_tac o SYM) >>
  fs[EVERY_MEM,MEM_FILTER,is_Label_rwt,PULL_EXISTS,between_def,MEM_MAP] >>
  rw[] >> res_tac >> fsrw_tac[ARITH_ss][])
  |> Q.GENL[`s0`,`f0`]

val update_ptr_def = Define`
  (update_ptr f (Jump (Addr x)) = Jump(Addr (tlookup f x))) ∧
  (update_ptr f (Call (Addr x)) = Call(Addr (tlookup f x))) ∧
  (update_ptr f (PushPtr (Addr x)) = PushPtr(Addr (tlookup f x))) ∧
  (update_ptr f i = i)`
val _ = export_rewrites["update_ptr_def"]

val apo = prove(
  ``∀f cenv t sz s e. ∃bc. (bvl_bc f cenv t sz s e).out = bc ++ s.out``,
  metis_tac[bvl_bc_append_out])

fun do_apo_tac q tm (g as (asl,w)) =
  let
    val ls = free_varsl(w::asl)
    val a = Parse.parse_in_context ls q
    val pat = ``bvl_bc f cenv t sz s ^a``
    fun finder tm =
      case total (match_term pat) tm of NONE => false
      | SOME s => last(snd(strip_comb tm)) = a
    val tm1 = find_term(finder)tm
    val args = snd (strip_comb tm1)
    val th = SPECL args apo
  in
    strip_assume_tac th g
  end

val tac =
  first_x_assum(fn th =>
    let
      val tm = th |> concl |> strip_forall |> snd |> dest_imp |> fst |> lhs
    in
      first_assum(fn th2 =>
        let
          val tm2 = lhs(concl th2)
          val (_,args) = strip_comb (rand tm2)
        in
          case total (match_term tm) tm2 of NONE => NO_TAC
          | SOME s => if last args = last(snd(strip_comb(rand tm))) then
            (mp_tac(SPEC(el 5 args)th) >>
             asm_simp_tac(srw_ss())[]>>
             strip_tac) else NO_TAC
        end)
     end)

val update_ptr_o_Stack = prove(
  ``update_ptr f o Stack = Stack``,
  simp[FUN_EQ_THM] >> Cases >> simp[])

val bvl_bc_ref_update_ptr = prove(
  ``∀n. MAP (update_ptr f) (bvl_bc_ref n) = bvl_bc_ref n``,
  Induct >> simp[bvl_bc_ref_def])

val bvl_bc_update_ptr = store_thm("bvl_bc_update_ptr",
  ``∀f cenv t sz s e bc s0 bc0.
      ((bvl_bc f cenv t sz s e).out = bc ++ s.out) ⇒
      ((bvl_bc LN cenv t sz s0 e).out = bc0 ++ s0.out) ⇒
      (s.next_label = s0.next_label) ⇒
      ((bvl_bc f cenv t sz s e).next_label = (bvl_bc LN cenv t sz s0 e).next_label) ∧
      (bc = MAP (update_ptr f) bc0)``,
  ho_match_mp_tac bvl_bc_ind >>
  strip_tac >- simp[bvl_bc_def] >>
  strip_tac >- (
    rw[] >> fs[bvl_bc_def,LET_THM] >>
    ASSUM_LIST(fn ls =>
      do_apo_tac`[e1]`(concl(el 2 ls)) >>
      do_apo_tac`[e1]`(concl (el 3 ls)) >>
      do_apo_tac`e2::es`(concl (el 2 ls)) >>
      do_apo_tac`e2::es`(concl (el 3 ls))) >>
    fs[] >> rw[]>>fs[] >>
    res_tac >> rw[] >> fs[]) >>
  strip_tac >- (
    simp[bvl_bc_def] >>
    Cases_on`t`>>simp[pushret_def,emit_def]>>rw[]>>rw[] ) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM,get_label_def] >>
    ASSUM_LIST(fn ls =>
      do_apo_tac`[e2]`(concl(el 2 ls)) >>
      do_apo_tac`[e2]`(concl(el 3 ls)) >>
      do_apo_tac`[e3]`(concl(el 2 ls)) >>
      do_apo_tac`[e3]`(concl(el 3 ls)) >>
      do_apo_tac`[e1]`(concl(el 2 ls)) >>
      do_apo_tac`[e1]`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >>
    res_tac >> rw[] >> fs[] >>
    rpt tac) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM] >>
    Cases_on`t`>>fs[]>>
    ASSUM_LIST(fn ls =>
      do_apo_tac`e`(concl(el 2 ls)) >>
      do_apo_tac`e`(concl(el 3 ls)) >>
      do_apo_tac`[e']`(concl(el 2 ls)) >>
      do_apo_tac`[e']`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >>
    res_tac >> rw[] >> fs[] >>
    rpt tac ) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM] >>
    ASSUM_LIST(fn ls =>
      do_apo_tac`[e]`(concl(el 2 ls)) >>
      do_apo_tac`[e]`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >>
    res_tac >> rw[] >> fs[] ) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM,get_label_def] >>
    Cases_on`t`>>fs[pushret_def]>>
    ASSUM_LIST(fn ls =>
      do_apo_tac`[e1]`(concl(el 2 ls)) >>
      do_apo_tac`[e1]`(concl(el 3 ls)) >>
      do_apo_tac`[e2]`(concl(el 2 ls)) >>
      do_apo_tac`[e2]`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >> rw[] >>
    res_tac >> rw[] >> fs[] >> rw[] >>
    rpt tac >>
    Cases_on`n=0`>>fs[]>>rw[]) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM] >>
    ASSUM_LIST(fn ls =>
      do_apo_tac`[e]`(concl(el 2 ls)) >>
      do_apo_tac`[e]`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >>
    res_tac >> rw[] >> fs[] >>
    rpt tac) >>
  strip_tac >- (
    rw[] >>
    fs[bvl_bc_def,LET_THM] >>
    Cases_on`t`>>Cases_on`dest`>>fs[]>>
    ASSUM_LIST(fn ls =>
      do_apo_tac`e`(concl(el 2 ls)) >>
      do_apo_tac`e`(concl(el 3 ls))) >>
    fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >> rw[] >>
    res_tac >> rw[] >> fs[] >> rw[] >>
    rpt tac >>
    simp[tlookup_def,lookup_def] >>
    simp[MAP_REVERSE,MAP_MAP_o,update_ptr_o_Stack] ) >>
  rw[] >>
  fs[bvl_bc_def,LET_THM] >>
  Cases_on`t`>>Cases_on`op`>>fs[pushret_def]>>
  ASSUM_LIST(fn ls =>
    do_apo_tac`e`(concl(el 2 ls)) >>
    do_apo_tac`e`(concl(el 3 ls))) >>
  fs[FOLDL_emit_append_out] >> rw[] >> fs[] >> rfs[] >> rw[] >>
  rpt tac >>
  TRY(Cases_on`n=0`>>fs[]>>rw[]) >>
  simp[tlookup_def,lookup_def] >>
  simp[MAP_REVERSE,bvl_bc_ref_update_ptr])

val bvl_bc_table_def = Define`
  bvl_bc_table il nl cmap =
    let (f,s) = foldi (bvl_bc_ptrfun il) 0 (LN, <|next_label:=nl+1;out:=[Jump(Lab nl)]|>) cmap in
    (f,s with out := (Label nl)::(MAP (update_ptr f) s.out))`

val is_Label_o_update_ptr = prove(
  ``is_Label o (update_ptr f) = is_Label``,
  simp[FUN_EQ_THM] >> Cases >> simp[] >>
  Cases_on`l`>>simp[])

val FILTER_is_Label_MAP_update_ptr = prove(
  ``FILTER is_Label (MAP (update_ptr f) ls) = FILTER is_Label ls``,
  rw[FILTER_MAP,is_Label_o_update_ptr] >>
  Induct_on`ls` >> simp[] >>
  Cases >> simp[])

val next_addr_MAP_update_ptr = prove(
  ``length_ok il ⇒
    ∀ls. next_addr il ls = next_addr il (MAP (update_ptr f) ls)``,
  strip_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases_on`l`>>simp[] >>
  fs[bytecodeLabelsTheory.length_ok_def])

val bvl_bc_table_good = store_thm("bvl_bc_table_good",
  ``length_ok il ⇒
    bvl_bc_table il nl cmap = (f,s) ⇒
    good_code_env f il cmap (REVERSE s.out)``,
  rw[bvl_bc_table_def,foldi_FOLDR_toAList] >>
  qspecl_then[`LN`,`<|next_label := nl+1; out:=[Jump(Lab nl)]|>`,`toAList cmap`]mp_tac
    (INST_TYPE[alpha|->numSyntax.num] bvl_bc_ptrfun_correct) >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_MAP_FST_toAList] ) >>
  fs[LET_THM] >>
  first_assum (split_applied_pair_tac o lhs o concl) >>
  fs[] >> rw[] >>
  rw[good_code_env_def] >>
  fs[GSYM MEM_toAList] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  specl_args_of_then``bvl_bc``bvl_bc_append_out strip_assume_tac >>
  imp_res_tac bvl_bc_update_ptr >>
  pop_assum kall_tac >>
  qexists_tac`cs`>> simp[] >>
  qexists_tac`MAP (update_ptr f) l0`>>simp[] >>
  simp[GSYM MAP_REVERSE] >>
  simp[FILTER_is_Label_MAP_update_ptr] >>
  simp[next_addr_MAP_update_ptr])

val bvl_bc_table_thm = store_thm("bvl_bc_table_thm",
  ``bvl_bc_table il nl cmap = (f,s) ⇒
    domain f = domain cmap ∧
    ∀bs bc0 bc1.
    ALL_DISTINCT (FILTER is_Label bc0) ∧
    EVERY ($> nl o dest_Label) (FILTER is_Label bc0) ∧
    bs.code = bc0 ++ REVERSE s.out ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ⇒
    bc_next bs (bs with <|pc := next_addr bs.inst_length (bc0++REVERSE s.out)|>)``,
  simp[bvl_bc_table_def,foldi_FOLDR_toAList] >>
  qspecl_then[`LN`,`<|next_label := nl+1; out:=[Jump(Lab nl)]|>`,`toAList cmap`]mp_tac
    (INST_TYPE[alpha|->numSyntax.num] bvl_bc_ptrfun_correct) >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_MAP_FST_toAList] ) >>
  fs[LET_THM] >> ntac 2 strip_tac >>
  first_assum (split_applied_pair_tac o lhs o concl) >>
  fs[] >> rw[] >- (
    qspecl_then[`LN`,`<|next_label := nl+1; out:=[Jump(Lab nl)]|>`,`toAList cmap`]mp_tac
      (INST_TYPE[alpha|->numSyntax.num] (Q.GENL[`s0`,`f0`]bvl_bc_ptrfun_domain)) >>
    simp[set_MAP_FST_toAList] ) >>
  `bc_fetch bs = SOME(Jump(Lab nl))` by (
    qpat_assum`X = Y.out`(assume_tac o SYM) >> fs[] >>
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_state_component_equality] >>
  simp[bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + LENGTH s'.out` >>
  simp[EL_APPEND1,EL_APPEND2,TAKE_APPEND2,TAKE_APPEND1] >>
  simp[SUM_APPEND,FILTER_APPEND,SUM_REVERSE,FILTER_REVERSE,MAP_REVERSE] >>
  simp[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,FILTER_is_Label_MAP_update_ptr] >>
  fs[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_MEM] >>
  qpat_assum`X = Y.out`(assume_tac o SYM) >> fs[between_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][])

open clos_to_bvlTheory

val bvl_bc_code_locs = prove(
  ``∀f cenv t sz s e.
      EVERY (λl. lookup l f = lookup l f1) (code_locs e) ⇒
      bvl_bc f cenv t sz s e = bvl_bc f1 cenv t sz s e``,
  ho_match_mp_tac bvl_bc_ind >>
  simp[bvl_bc_def,UNCURRY,code_locs_def] >>
  rw[] >> fs[]
  >- metis_tac[PAIR,FST]
  >- metis_tac[PAIR,FST]
  >- (
    Cases_on`t`>>Cases_on`dest`>>fs[]>>
    rw[tlookup_def] )
  >- ( Cases_on`op`>>fs[tlookup_def] ))
|> Q.GEN`f1` |> curry save_thm "bvl_bc_code_locs"

val _ = export_theory()
