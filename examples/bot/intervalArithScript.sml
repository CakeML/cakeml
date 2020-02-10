(*
  A HOL4 copy of interval arithmetic
*)

open preamble blastLib;

val _ = new_theory "intervalArith";

(*
  Define a copy of the word arithmetic semantics
  from the Isabelle/HOL formalization

  NOTE: the Isabelle semantics removes the constant 0x80000000
  from the word32 type, which we omit here
*)

val NEG_INF = (rconc o EVAL) ``((INT_MINw: 32 word) + 1w)``
val POS_INF = (rconc o EVAL) ``((INT_MAXw: 32 word) )``

val NEG_INF_def = Define`NEG_INF:word32 = ^NEG_INF`
val POS_INF_def = Define`POS_INF:word32 = ^POS_INF`

val _ = Datatype`
  trm = Const word32
      | Var string
      | Plus trm trm
      | Times trm trm
      | Div trm trm
      | Max trm trm
      | Min trm trm
      | Neg trm
      | Abs trm`

val _ = Datatype`
  fml = Le trm trm
      | Leq trm trm
      | Equals trm trm
      | And fml fml
      | Or fml fml
      | Not fml`

val _ = Datatype`
   hp = Test fml
      | Assign string trm
      | AssignAny string
      | Seq hp hp
      | Choice hp hp
      | Loop hp`

(* First, define the helper functions following Isabelle formalization
  We will simplify these later *)
val pu_def = Define`
  pu (w1:word32) (w2:word32) =
  if w1 = POS_INF then POS_INF
  else if w2 = POS_INF then POS_INF
  else if w1 = NEG_INF then
    (if w2 = NEG_INF then NEG_INF
    else
      let sum:word64 = sw2sw w2 + sw2sw NEG_INF in
      if sum ≤ sw2sw NEG_INF then NEG_INF
      else sw2sw sum)
  else if w2 = NEG_INF then
    let sum:word64 = sw2sw w1 +sw2sw NEG_INF in
    if sum ≤ sw2sw NEG_INF then NEG_INF
    else sw2sw sum
  else
    let sum:word64 = sw2sw w1 + sw2sw w2 in
    if sw2sw POS_INF ≤ sum then POS_INF
    else if sum ≤ sw2sw NEG_INF then NEG_INF
    else sw2sw sum`

val pl_def = Define`
  pl (w1:word32) (w2:word32) =
  if w1 = NEG_INF then NEG_INF
  else if w2 = NEG_INF then NEG_INF
  else if w1 = POS_INF then
    (if w2 = POS_INF then POS_INF
    else
      let sum:word64 = sw2sw w2 + sw2sw POS_INF in
      if sw2sw POS_INF ≤ sum then POS_INF
      else sw2sw sum)
  else if w2 = NEG_INF then
    let sum:word64 = sw2sw w1 + sw2sw POS_INF in
    if sw2sw POS_INF ≤ sum then POS_INF
    else sw2sw sum
  else
    let sum:word64 = sw2sw w1 + sw2sw w2 in
    if sw2sw POS_INF ≤ sum then POS_INF
    else if sum ≤ sw2sw NEG_INF then NEG_INF
    else sw2sw sum`

val wtimes_def = Define`
  wtimes (w1:word32) (w2:word32) =
  if w1 = POS_INF ∧ w2 = POS_INF then POS_INF
  else if w1 = NEG_INF ∧ w2 = POS_INF then NEG_INF
  else if w1 = POS_INF ∧ w2 = NEG_INF then NEG_INF
  else if w1 = NEG_INF ∧ w2 = NEG_INF then POS_INF

  else if w1 = POS_INF ∧ w2 < 0w then NEG_INF
  else if w1 = POS_INF ∧ 0w < w2 then POS_INF
  else if w1 = POS_INF ∧ 0w = w2 then 0w
  else if w1 = NEG_INF ∧ w2 < 0w then POS_INF
  else if w1 = NEG_INF ∧ 0w < w2 then NEG_INF
  else if w1 = NEG_INF ∧ 0w = w2 then 0w

  else if w1 < 0w ∧ w2 = POS_INF then NEG_INF
  else if 0w < w1 ∧ w2 = POS_INF then POS_INF
  else if 0w = w1 ∧ w2 = POS_INF then 0w
  else if w1 < 0w ∧ w2 = NEG_INF then POS_INF
  else if 0w < w1 ∧ w2 = NEG_INF then NEG_INF
  else if 0w = w1 ∧ w2 = NEG_INF then 0w
  else
  let prod:word64 = sw2sw w1 * sw2sw w2 in
  if prod ≤ sw2sw NEG_INF then NEG_INF
  else if sw2sw POS_INF ≤ prod then POS_INF
  else sw2sw prod`

val wmax_def = Define`
  wmax (w1:word32) (w2:word32) = if w1 < w2 then w2 else w1`

val wmin_def = Define`
  wmin (w1:word32) (w2:word32) = if w1 < w2 then w1 else w2`

val tu_def = Define`
  tu w1l w1u w2l w2u =
  wmax (wmax (wtimes w1l w2l) (wtimes w1u w2l))
       (wmax (wtimes w1l w2u) (wtimes w1u w2u))`

val tl_def = Define`
  tl w1l w1u w2l w2u =
  wmin (wmin (wtimes w1l w2l) (wtimes w1u w2l))
       (wmin (wtimes w1l w2u) (wtimes w1u w2u))`

val wneg_def = Define`
  wneg w =
  if w = NEG_INF then POS_INF
  else if w = POS_INF then NEG_INF
  else -w`;

val divfloor_def = Define`
  divfloor (w1:word32) (w2:word32) =
  if word_smod w1 w2 = 0w then
    word_sdiv w1 w2
  else
    (word_sdiv w1 w2) + 1w`

val divceil_def = Define`
  divceil (w1:word32) (w2:word32) = word_sdiv w1 w2`

val wle_def = Define`
  wle (w1:word32) w2 <=> w1 < w2`

val wleq_def = Define`
  wleq (w1:word32) w2 <=>
  ¬ (w1 = NEG_INF ∧ w2 = NEG_INF) ∧
  ¬ (w2 = POS_INF ∧ w2 = POS_INF) ∧
  w1 <= w2`

val divl_def = Define`
  divl w1 w2 =
  if wle NEG_INF w1 ∧ wle w1 POS_INF ∧ wle NEG_INF w2 ∧ wle w2 POS_INF then divfloor w1 w2
  else if wleq w1 0w ∧ w2 = NEG_INF ∨ wleq 0w w1 ∧ w2 = POS_INF then 0w
  else if w1 = NEG_INF ∧ wle w2 0w then divfloor NEG_INF w2
  else if w1 = NEG_INF ∧ wleq 0w w2 ∨ w2 = POS_INF ∧ wle w2 0w then NEG_INF
  else if w1 = POS_INF then divfloor POS_INF w2
  else -1w`

val divu_def = Define`
  divu w1 w2 =
  if wle NEG_INF w1 ∧ wle w1 POS_INF ∧ wle NEG_INF w2 ∧ wle w2 POS_INF then divceil w1 w2
  else if wleq 0w w1 ∧ w2 = NEG_INF ∨ wleq w1 0w ∧ w2 = POS_INF then 0w
  else if w1 = NEG_INF then
    (if wle w2 0w then POS_INF else divceil NEG_INF w2)
  else if w1 = POS_INF ∧ wle w2 POS_INF then divceil POS_INF w2
  else 1w`

val divPair_def = Define`
  divPair l1 u1 l2 u2 =
  if wleq l2 u2 then (
    if wleq l2 0w ∧ wleq 0w u2
      then (NEG_INF,POS_INF)
    else if wle 0w l2 then
      (if wleq l1 0w ∧ wleq 0w u1 then
        (wmin (divl l1 l2) 0w, wmax (divu u1 l2) 0w)
      else if wle u1 0w then
        (divl l1 l2, divu u1 u2)
      else
        (divl l1 u2, divu u1 l2))
    else
      (if wleq l1 0w ∧ wleq 0w u1 then
        (wmin (divl u1 u2) 0w, wmax (divu l1 u2) 0w)
      else if wle u1 0w then
        (divl u1 l2, divu l1 u2)
      else
        (divl u1 u2, divu l1 l2)))
  else (NEG_INF, POS_INF)`

(* Following the Isabelle semantics, we first use abstract word states
   that map a sum to words *)
val _ = type_abbrev ("wstate",``:string+string -> word32``);

val wtsem_def = Define`
  (wtsem (Const r) (s:wstate) = (r,r)) ∧
  (wtsem (Var x) s = (s (INL x), s (INR x))) ∧
  (wtsem (Plus t1 t2) s =
    let (l1,u1) = wtsem t1 s in
    let (l2,u2) = wtsem t2 s in
    (pl l1 l2, pu u1 u2)) ∧
  (wtsem (Times t1 t2) s =
    let (l1,u1) = wtsem t1 s in
    let (l2,u2) = wtsem t2 s in
    (tl l1 u1 l2 u2, tu l1 u1 l2 u2)) ∧
  (wtsem (Div t1 t2) s =
    let (l1,u1) = wtsem t1 s in
    let (l2,u2) = wtsem t2 s in
    divPair l1 u1 l2 u2) ∧
  (wtsem (Max t1 t2) s =
    let (l1,u1) = wtsem t1 s in
    let (l2,u2) = wtsem t2 s in
    (wmax l1 l2, wmax u1 u2)) ∧
  (wtsem (Min t1 t2) s =
    let (l1,u1) = wtsem t1 s in
    let (l2,u2) = wtsem t2 s in
    (wmin l1 l2, wmin u1 u2)) ∧
  (wtsem (Neg t) s =
    let (l,u) = wtsem t s in
    (wneg u, wneg l)) ∧
  (wtsem (Abs t) s =
    let (l,u) = wtsem t s in
    (wmax l (wneg u), wmax u (wneg l)))`

val (wfsem_rules,wfsem_ind, wfsem_cases) = Hol_reln`
  (∀t1 t2 s.
    wle (SND (wtsem t1 s)) (FST (wtsem t2 s)) ⇒
    wfsem (Le t1 t2) s T) ∧
  (∀t1 t2 s.
    wleq (SND (wtsem t2 s)) (FST (wtsem t1 s)) ⇒
    wfsem (Le t1 t2) s F) ∧
  (∀t1 t2 s.
    wleq (SND (wtsem t1 s)) (FST (wtsem t2 s)) ⇒
    wfsem (Leq t1 t2) s T) ∧
  (∀t1 t2 s.
    wle (SND (wtsem t2 s)) (FST (wtsem t1 s)) ⇒
    wfsem (Leq t1 t2) s F) ∧
  (∀t1 t2 s.
    FST (wtsem t2 s) = SND (wtsem t2 s) ∧
    SND (wtsem t2 s) = SND (wtsem t1 s) ∧
    SND (wtsem t1 s) = FST (wtsem t1 s) ∧
    FST (wtsem t2 s) ≠ NEG_INF ∧
    FST (wtsem t2 s) ≠ POS_INF ⇒
    wfsem (Equals t1 t2) s T) ∧
  (∀t1 t2 s.
    wle (SND (wtsem t1 s)) (FST (wtsem t2 s)) ⇒
    wfsem (Equals t1 t2) s F) ∧
  (∀t1 t2 s.
    wle (SND (wtsem t2 s)) (FST (wtsem t1 s)) ⇒
    wfsem (Equals t1 t2) s F) ∧
  (∀f1 f2 s.
    wfsem f1 s T ∧
    wfsem f2 s T ⇒
    wfsem (And f1 f2) s T) ∧
  (∀f1 f2 s.
    wfsem f1 s F ⇒
    wfsem (And f1 f2) s F) ∧
  (∀f1 f2 s.
    wfsem f2 s F ⇒
    wfsem (And f1 f2) s F) ∧
  (∀f1 f2 s.
    wfsem f1 s T ⇒
    wfsem (Or f1 f2) s T) ∧
  (∀f1 f2 s.
    wfsem f2 s T ⇒
    wfsem (Or f1 f2) s T) ∧
  (∀f1 f2 s.
    wfsem f1 s F ∧
    wfsem f1 s F ⇒
    wfsem (Or f1 f2) s F) ∧
  (∀f s.
    wfsem f s F ⇒
    wfsem (Not f) s T) ∧
  (∀f s.
    wfsem f s T ⇒
    wfsem (Not f) s F)`

(* The non-deterministic big-step relational semantics of hybrid programs *)
val (wpsem_rules,wpsem_ind, wpsem_cases) = Hol_reln`
  (* wTest *)
  (∀f w v.
    wfsem f w T ∧ v = w ⇒
    wpsem (Test f) v w) ∧
  (* wSeq *)
  (∀a b w u v.
    wpsem a v u ∧
    wpsem b u w ⇒
    wpsem (Seq a b) v w) ∧
  (* wAssign *)
  (∀x t w v.
    (w = λy. if y = INR x then SND (wtsem t v)
            else if y = INL x then FST (wtsem t v)
            else v y) ⇒
    wpsem (Assign x t) v w) ∧
  (* wChoice1 *)
  (∀a b w v.
    wpsem a v w ⇒
    wpsem (Choice a b) v w) ∧
  (* wChoice2 *)
  (∀a b w v.
    wpsem b v w ⇒
    wpsem (Choice a b) v w) ∧
  (* Non-deterministic assignment *)
  (∀x a b w v.
  a ≤ b ∧
  (w = λy. if y = INR x then b
            else if y = INL x then a
            else v y) ⇒
  wpsem (AssignAny x) v w) ∧
  (∀a w.
    wpsem (Loop a) w w) ∧
  (∀a w v u.
    wpsem a v u ∧
    wpsem (Loop a) u w ⇒
    wpsem (Loop a) v w)`

(* Now we define the actual semantics that we will work with
  These operate over concrete word states
*)
val _ = type_abbrev ("cwstate",``:(string,word32 # word32) alist``)

val lookup_var_def = Define`
  lookup_var s n =
    case ALOOKUP s n of
      NONE => (NEG_INF,POS_INF)
    | SOME i => i`

(* abstract concrete cwstate back into a wstate *)
val abs_state_def = Define`
  abs_state (s:cwstate) =
  λy.
    case y of
      INL x => FST (lookup_var s x)
    | INR x => SND (lookup_var s x)`

val cwtsem_def = Define`
  (cwtsem (Const w) (s:cwstate) = (w,w)) ∧
  (cwtsem (Var n) s = lookup_var s n) ∧
  (cwtsem (Plus t1 t2) s =
    let (l1,u1) = cwtsem t1 s in
    let (l2,u2) = cwtsem t2 s in
    (pl l1 l2, pu u1 u2)) ∧
  (cwtsem (Times t1 t2) s =
    let (l1,u1) = cwtsem t1 s in
    let (l2,u2) = cwtsem t2 s in
    (tl l1 u1 l2 u2, tu l1 u1 l2 u2)) ∧
  (cwtsem (Div t1 t2) s =
    let (l1,u1) = cwtsem t1 s in
    let (l2,u2) = cwtsem t2 s in
    divPair l1 u1 l2 u2) ∧
  (cwtsem (Max t1 t2) s =
    let (l1,u1) = cwtsem t1 s in
    let (l2,u2) = cwtsem t2 s in
    (wmax l1 l2, wmax u1 u2)) ∧
  (cwtsem (Min t1 t2) s =
    let (l1,u1) = cwtsem t1 s in
    let (l2,u2) = cwtsem t2 s in
    (wmin l1 l2, wmin u1 u2)) ∧
  (cwtsem (Neg t) s =
    let (l,u) = cwtsem t s in
    (wneg u, wneg l)) ∧
  (cwtsem (Abs t) s =
    let (l,u) = cwtsem t s in
    (wmax l (wneg u), wmax u (wneg l)))`

val cwtsem_wtsem = Q.store_thm("cwtsem_wtsem",`
  ∀t cs s.
 cwtsem t cs = wtsem t (abs_state cs)`,
  Induct>>fs[cwtsem_def,wtsem_def,lookup_var_def,abs_state_def]);

(* We use a tri-valued logic for wfsem instead of an underspecified relation *)
val cwfsem_def = Define`
  (cwfsem (Le t1 t2) (s:cwstate) =
  let (l1,u1) = cwtsem t1 s in
  let (l2,u2) = cwtsem t2 s in
  if wle u1 l2 then SOME T
  else if wleq u2 l1 then SOME F
  else NONE) ∧
  (cwfsem (Leq t1 t2) s =
  let (l1,u1) = cwtsem t1 s in
  let (l2,u2) = cwtsem t2 s in
  if wleq u1 l2 then SOME T
  else if wle u2 l1 then SOME F
  else NONE) ∧
  (cwfsem (Equals t1 t2) s =
  let (l1,u1) = cwtsem t1 s in
  let (l2,u2) = cwtsem t2 s in
  if l2 = u2 ∧ u2 = u1 ∧ u1 = l1 ∧ l2 ≠ NEG_INF ∧ l2 ≠ POS_INF then SOME T
  else if wle u1 l2 then SOME F
  else if wle u2 l1 then SOME F
  else NONE) ∧
  (cwfsem (And f1 f2) s =
  case (cwfsem f1 s, cwfsem f2 s) of
    SOME T, SOME T => SOME T
  | SOME F, _ => SOME F
  | _, SOME F => SOME F
  | _ => NONE) ∧
  (cwfsem (Or f1 f2) s =
  case (cwfsem f1 s, cwfsem f2 s) of
    SOME T, _ => SOME T
  | _, SOME T => SOME T
  | SOME F, SOME F => SOME F
  | _ => NONE) ∧
  (cwfsem (Not f) s =
  case cwfsem f s of
    SOME F => SOME T
  | SOME T => SOME F
  | _ => NONE)`

(* The reverse direction should also be true, but we do not need it *)
val cwfsem_wfsem = Q.store_thm("cwfsem_wfsem",`
  ∀f cs s b.
  (cwfsem f cs = SOME b ⇒ wfsem f (abs_state cs) b)`,
  Induct>>fs[cwfsem_def]>>rw[]>>
  TRY
    (rpt (pairarg_tac>>fs[])>>
    EVERY_CASE_TAC>>fs[]>>
    simp[Once wfsem_cases,GSYM cwtsem_wtsem])>>
  rw[]);

(* The non-deterministic big-step relational semantics of hybrid programs *)
val (cwpsem_rules,cwpsem_ind, cwpsem_cases) = Hol_reln`
  (* Non-deterministic assignment *)
  (∀x a b w.
  a ≤ b ⇒
  cwpsem (AssignAny x) w ((x,(a,b))::w)) ∧
  (* Deterministic assignment *)
  (∀x t w.
  cwpsem (Assign x t) w ((x,(cwtsem t w))::w)) ∧
  (∀f w.
    cwfsem f w = SOME T ⇒
    cwpsem (Test f) w w) ∧
  (∀a b w u v.
    cwpsem a w u ∧
    cwpsem b u v ⇒
    cwpsem (Seq a b) w v) ∧
  (∀a b w v.
    cwpsem a w v ⇒
    cwpsem (Choice a b) w v) ∧
  (∀a b w v.
    cwpsem b w v ⇒
    cwpsem (Choice a b) w v) ∧
  (∀a w.
    cwpsem (Loop a) w w) ∧
  (∀a w u v.
    cwpsem a w u ∧
    cwpsem (Loop a) u v ⇒
    cwpsem (Loop a) w v)`

val cwpsem_wpsem = Q.store_thm("cwpsem_wpsem",`
  ∀p w v.
  cwpsem p w v ⇒ wpsem p (abs_state w) (abs_state v)`,
  ho_match_mp_tac cwpsem_ind>>rw[]>>
  simp[Once wpsem_cases,cwfsem_wfsem]
  >-
    (asm_exists_tac>>simp[abs_state_def]>>
    simp[FUN_EQ_THM,lookup_var_def]>>
    rw[]>>EVERY_CASE_TAC>>fs[])
  >-
    (simp[cwtsem_wtsem,abs_state_def]>>
    simp[FUN_EQ_THM,lookup_var_def]>>
    rw[]>>EVERY_CASE_TAC>>fs[])
  >>
    metis_tac[]);

(* More efficient simplifications for the bounds checks *)
val round_to_inf_def = Define`
  round_to_inf (w:word64) =
    if w ≤ sw2sw NEG_INF then NEG_INF
    else if
      sw2sw POS_INF ≤ w then POS_INF
    else
      w2w w`

val pu_compute = Q.store_thm("pu_compute",`
  pu (w1:word32) (w2:word32) =
  if w1 = POS_INF ∨ w2 = POS_INF
  then POS_INF
  else
    let s:word64 = sw2sw w1 + sw2sw w2 in
    round_to_inf s`,
  rw[pu_def]>>fs[round_to_inf_def]>>
  rpt (pop_assum mp_tac)>> EVAL_TAC>>
  simp[POS_INF_def,NEG_INF_def]>>
  rw[]>>
  blastLib.FULL_BBLAST_TAC>>
  fs[]
  );

val pl_compute = Q.store_thm("pl_compute",`
  pl (w1:word32) (w2:word32) =
  if w1 = NEG_INF ∨ w2 = NEG_INF then NEG_INF
  else
  let s:word64 = sw2sw w1 + sw2sw w2 in
  round_to_inf s`,
  rw[pl_def]>>fs[round_to_inf_def]>>
  rpt (pop_assum mp_tac)>> EVAL_TAC>>
  simp[POS_INF_def,NEG_INF_def]>>
  rw[]>>
  blastLib.FULL_BBLAST_TAC)

val wtimes_compute = Q.store_thm("wtimes_compute",`
  wtimes w1 w2 =
  let prod = sw2sw w1 * sw2sw w2 in round_to_inf prod`,
  EVAL_TAC>>rw[]>>
  rpt(pop_assum mp_tac)>> EVAL_TAC>>
  simp[POS_INF_def,NEG_INF_def]>>
  blastLib.FULL_BBLAST_TAC);

(* Free variables *)
val fv_trm_def = Define`
  (fv_trm (Const _) = []) ∧
  (fv_trm (Var x) = [x]) ∧
  (fv_trm (Plus t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_trm (Times t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_trm (Div t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_trm (Max t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_trm (Min t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_trm (Neg t) = fv_trm t) ∧
  (fv_trm (Abs t) = fv_trm t)`

val fv_fml_def = Define`
  (fv_fml (Le t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_fml (Leq t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_fml (Equals t1 t2) = fv_trm t1 ++ fv_trm t2) ∧
  (fv_fml (And f1 f2) = fv_fml f1 ++ fv_fml f2) ∧
  (fv_fml (Or f1 f2) = fv_fml f1 ++ fv_fml f2) ∧
  (fv_fml (Not f) = fv_fml f)`

(* Term Coincidence *)
val fv_trm_coincide = Q.store_thm("fv_trm_coincide",`
  ∀t w v.
  EVERY (λx. ALOOKUP w x = ALOOKUP v x) (fv_trm t) ⇒
  cwtsem t w = cwtsem t v`,
  Induct>>fs[fv_trm_def,cwtsem_def,lookup_var_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  metis_tac[PAIR,FST,SND]);

(* Formula Coincidence *)
val fv_fml_coincide = Q.store_thm("fv_fml_coincide",`
  ∀f w v.
  EVERY (λx. ALOOKUP w x = ALOOKUP v x) (fv_fml f) ⇒
  cwfsem f w = cwfsem f v`,
  Induct>>fs[fv_fml_def,cwfsem_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  metis_tac[PAIR,FST,SND,fv_trm_coincide]);

(* Some abbreviations for convenience *)
val True_def = Define`
  True = Leq (Const 0w) (Const 0w)`

val Skip_def = Define`
  Skip = Test True`

val Skip_sem = Q.store_thm("Skip_sem",`
  cwpsem Skip w w' ⇔ w' = w`,
  EVAL_TAC>>
  simp[Once cwpsem_cases,cwfsem_def,cwtsem_def]>>
  EVAL_TAC);

val AssignAnyPar_def = Define`
  (AssignAnyPar [] = Skip) ∧
  (AssignAnyPar (x::xs) = Seq (AssignAny x) (AssignAnyPar xs))`

val AssignAnyPar_sem = Q.store_thm("AssignAnyPar_sem",`
  ∀xs ws w w'.
  ALL_DISTINCT xs ==>
  (cwpsem (AssignAnyPar xs) w w' ⇔
  ∃ws.
  LENGTH ws = LENGTH xs ∧
  EVERY (λ(a,b). a ≤ b) ws ∧
  w' = (REVERSE (ZIP(xs,ws)) ++ w))`,
  Induct>>rw[AssignAnyPar_def,Skip_sem]>>
  simp[Once cwpsem_cases]>>
  simp[Once cwpsem_cases,PULL_EXISTS]>>
  rw[EQ_IMP_THM]
  >-
    (qexists_tac`(a,b)::ws`>>simp[])
  >>
  Cases_on`ws`>>fs[]>>
  pairarg_tac>>fs[]>>
  asm_exists_tac>>fs[]);

val AssignPar_def = Define`
  (AssignPar (l::ls) (r::rs) =
    Seq (Assign l r) (AssignPar ls rs)) ∧
  (AssignPar [] [] = Skip)`

(* EVAL-able non-overlap *)
val no_overlap_def = Define`
  (no_overlap [] ys ⇔ T) ∧
  (no_overlap (x::xs) ys ⇔ ¬MEMBER x ys ∧ no_overlap xs ys)`

val no_overlap_thm = Q.store_thm("no_overlap_thm",`
  ∀xs ys.
  no_overlap xs ys ⇔
  (∀x. MEM x xs ⇒  ¬ MEM x ys)`,
  Induct>>rw[no_overlap_def,GSYM ml_translatorTheory.MEMBER_INTRO]>>
  metis_tac[]);

val no_overlap_sym = Q.store_thm("no_overlap_sym",`
  no_overlap xs ys ⇔ no_overlap ys xs`,
  rw[no_overlap_thm]>>
  metis_tac[]);

val AssignPar_sem = Q.store_thm("AssignPar_sem",`
  ∀ls rs w w'.
  ALL_DISTINCT ls ∧
  no_overlap ls (FLAT (MAP fv_trm rs)) ∧
  LENGTH ls = LENGTH rs ⇒
  (cwpsem (AssignPar ls rs) w w' ⇔
  w' = REVERSE (ZIP(ls, MAP (λr. cwtsem r w) rs)) ++ w)`,
  simp[Once no_overlap_sym]>>
  Induct>>rw[AssignPar_def]
  >-
    simp[Skip_sem]
  >>
  Cases_on`rs`>>fs[AssignPar_def]>>
  simp[Once cwpsem_cases]>>
  simp[Once cwpsem_cases]>>
  first_x_assum(qspec_then`t` mp_tac)>>
  simp[]>>
  disch_then(qspecl_then [`(h,cwtsem h' w):: w`,`w'`] mp_tac)>>
  impl_tac>-
    fs[no_overlap_thm]>>
  rw[]>>
  rpt(AP_TERM_TAC>>AP_THM_TAC)>>
  rpt(AP_TERM_TAC)>>
  simp[MAP_EQ_f]>>rw[]>>
  match_mp_tac fv_trm_coincide>>
  fs[ALOOKUP_def,EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS,no_overlap_thm]>>
  rw[]>>
  metis_tac[]);

val AssignVarPar_def = Define`
  AssignVarPar lhs rhs = AssignPar lhs (MAP Var rhs)`

val AssignVarPar_sem = Q.store_thm("AssignVarPar_sem",`
  ∀ls rs w w'.
  ALL_DISTINCT ls ∧
  no_overlap ls rs ∧
  LENGTH ls = LENGTH rs ⇒
  (cwpsem (AssignVarPar ls rs) w w' ⇔
  w' = REVERSE (ZIP(ls, MAP (lookup_var w) rs)) ++ w)`,
  rw[AssignVarPar_def]>>
  `MAP (lookup_var w) rs = MAP (λr. cwtsem r w) (MAP Var rs)` by
     simp[MAP_EQ_f,MAP_MAP_o,cwtsem_def]>>
  rw[]>>
  match_mp_tac AssignPar_sem>>
  fs[MAP_MAP_o,fv_trm_def,o_DEF,FLAT_MAP_SING]);

val AssignVarPar_imp = Q.store_thm("AssignVarPar_imp",`
  ∀ls rs w.
  ALL_DISTINCT ls ∧
  no_overlap ls rs ∧
  LENGTH ls = LENGTH rs ⇒
  cwpsem (AssignVarPar ls rs) w (REVERSE (ZIP(ls, MAP (lookup_var w) rs)) ++ w)`,
  metis_tac[AssignVarPar_sem]);

val _ = export_theory();
