(*
  An eXtended AIG format for internal use
*)
Theory xaig
Ancestors
  aig
Libs
  preamble

Datatype:
  gty =
    (* Multi-input And gates out = \And_i in_i *)
    And (('a,'i,'l) lit list)
    (* Two-input XOR gates out = in_1 XOR in_2 *)
  | Xor (('a,'i,'l) lit) (('a,'i,'l) lit)
    (* Three-input if-then-else gates
      out = if in_1 then in_2 else in_3 *)
  | Ite (('a,'i,'l) lit) (('a,'i,'l) lit) (('a,'i,'l) lit)
End

Type xaig[pp] = “:('a # ('a,'i,'l) gty) list”

(* Analogous to eval_lit for aig *)

Definition xeval_lit_def:
  (xeval_lit (ss : 'i istate # 'l lstate) xaig
    ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Gate n => b ⇎ xeval_gate ss xaig n) ∧
  (xeval_gate ss ([]:('a,'i,'l) xaig) n = F) ∧
  (xeval_gate ss (h::tl) n =
   let (n', gt) = h in
     if n' = n then
       xeval_gty ss tl gt
     else xeval_gate ss tl n) ∧
  (xeval_gty ss tl gt =
      (case gt of
        And ins => EVERY (xeval_lit ss tl) ins
      | Xor in1 in2 =>
        xeval_lit ss tl in1 ⇎ xeval_lit ss tl in2
      | Ite in1 inT inF =>
        if xeval_lit ss tl in1
        then xeval_lit ss tl inT
        else xeval_lit ss tl inF))
End

(* Naive *)
Definition aig_to_xaig_def:
  (aig_to_xaig [] = []) ∧
  (aig_to_xaig ((n,ins)::tl) =
    (n,And ins)::aig_to_xaig tl)
End

(* Sanity check *)
Theorem aig_to_xaig_sound:
  ∀aig xaig lit gs.
  aig_to_xaig aig = xaig ⇒
  (eval_lit ss aig lit =
  xeval_lit ss xaig lit) ∧
  (eval_gate ss aig gs =
  xeval_gate ss xaig gs)
Proof
  Induct>>rw[aig_to_xaig_def]
  >-
    (Cases_on`lit`>>simp[eval_lit_def,xeval_lit_def])
  >-
    simp[xeval_lit_def]
  >- (
    Cases_on`h`>>
    Cases_on`lit`>>
    simp[eval_lit_def,xeval_lit_def,aig_to_xaig_def]>>
    every_case_tac>>rw[]
    >- (
      cong_tac NONE>>
      simp[FUN_EQ_THM])>>
    metis_tac[])>>
  Cases_on`h`>>
  rw[eval_lit_def,aig_to_xaig_def,xeval_lit_def]>>
  cong_tac NONE>>
  simp[FUN_EQ_THM]
QED

(* Literals matching an XOR

  out = ¬(a ∧ b) ∧ ¬(~a ∧ ¬ b)
      = a XOR b

  Note: a,b an be literals
*)
Definition match_xor_def:
  match_xor (x0,bx0) (x1,bx1) (y0,by0) (y1,by1) ⇔
    x0 = y0 ∧ bx0 = ¬by0 ∧
    x1 = y1 ∧ bx1 = ¬by1 ∨
    x0 = y1 ∧ bx0 = ¬by1 ∧
    x1 = y0 ∧ bx1 = ¬by0
End

(* slow version, for proof.
  The finite map being returned
    is a mapping
      gate_name |-> lits
    which tracks gates which are Ands
    Note: this should be (lit # lit) instead of a
      lit list once aig changes type.
*)
Definition optimize_gate_def:
  optimize_gate ins gm =
  case ins of
    [(Gate l,bl);(Gate r,br)] =>
      (case FLOOKUP gm l of
        SOME [l0;l1] =>
        (case FLOOKUP gm r of
          SOME [r0;r1] =>
            (* The XOR pattern *)
            if bl ∧ br ∧ match_xor l0 l1 r0 r1
            then
              SOME (Xor l0 l1)
            else NONE
          | _ => NONE)
      | _ => NONE)
  | _ => NONE
End

(* TODO: the mapping isn't quite right because of shadowing *)
Definition aig_to_xaig_opt_def:
  (aig_to_xaig_opt [] = ([],FEMPTY)) ∧
  (aig_to_xaig_opt ((n,ins)::tl) =
    case aig_to_xaig_opt tl of
      (xtl,gm) =>
    case optimize_gate ins gm of
      NONE =>
        ((n,And ins) :: xtl, gm⟨n ↦ ins⟩)
    | SOME g =>
        ((n,g) :: xtl, gm))
End

Theorem optimize_gate_sound:
  optimize_gate ins gm = SOME x ∧
  (∀g ins.
    FLOOKUP gm g = SOME ins ⇒
    (xeval_gate ss rest g =
      EVERY (λa. xeval_lit ss rest a) ins))
  ⇒
  (EVERY (λa. xeval_lit ss rest a) ins =
  xeval_gty ss rest x)
Proof
  rw[optimize_gate_def]>>
  gvs[AllCaseEqs()]
  >- (
    first_assum drule>>
    qpat_x_assum`FLOOKUP _ l = _` assume_tac>>
    first_x_assum drule>>
    rw[]>>
    gvs[oneline match_xor_def,AllCasePreds()]>>
    simp[xeval_lit_def]>>
    every_case_tac>>fs[]>>
    metis_tac[])
QED

(* Not quite right because of forward/backward refs *)
Theorem aig_to_xaig_opt_sound:
  ∀aig xaig gm lit gs.
  aig_to_xaig_opt aig = (xaig,gm) ∧
  ALL_DISTINCT (MAP FST aig) ⇒
  FDOM gm ⊆ set (MAP FST aig) ∧
  (∀g ins.
    FLOOKUP gm g = SOME ins ⇒
    (xeval_gate ss xaig g =
      EVERY (λa. xeval_lit ss xaig a) ins)) ∧
  (eval_lit ss aig lit =
  xeval_lit ss xaig lit) ∧
  (eval_gate ss aig gs =
  xeval_gate ss xaig gs)
Proof
  Induct
  >- (
    simp[aig_to_xaig_opt_def]>>
    Cases>>
    simp[eval_lit_def,xeval_lit_def])>>
  Cases>>
  fs[eval_lit_def,xeval_lit_def,aig_to_xaig_opt_def]>>
  rpt gen_tac>>
  strip_tac>>
  gvs[AllCaseEqs(),GSYM PULL_FORALL]>>
  cheat
QED

