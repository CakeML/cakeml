(*
  Tutorial excercise
*)

Definition PARITY_def:
  (PARITY 0 f = T) ∧
  (PARITY (SUC n) f = if f(SUC n) then ¬PARITY n f
                      else PARITY n f)
End

Theorem UNIQUENESS_LEMMA:
  ∀inp out.
    (out 0 ⇔ T) ∧
    (∀t. out(SUC t) ⇔ (if inp(SUC t) then ¬(out t) else out t)) ⇒
    (∀t. out t ⇔ PARITY t inp)
Proof
  (rpt gen_tac \\ strip_tac)
  \\ Induct_on ‘t’
  >- rw[PARITY_def]
  >- rw[PARITY_def]
QED

Definition ONE_def:
  ONE(out:num->bool) ⇔ ∀t. out t ⇔ T
End

Definition NOT_def:
  NOT(inp, out:num->bool) ⇔ ∀t. out t ⇔ ¬(inp t)
End

Definition MUX_def:
  MUX(sw, in1, in2, out:num->bool) ⇔ ∀t. out t ⇔ if sw t then in1 t else in2 t
End

Definition REG_def:
  REG(inp, out:num->bool) ⇔ ∀t. out t ⇔ if (t=0) then F else inp(t-1)
End

Definition PARITY_IMP_def:
  PARITY_IMP(inp,out) =
  ∃ l1 l2 l3 l4 l5.
    NOT(l2,l1) ∧ MUX(inp, l1, l2, l3) ∧ REG(out, l2) ∧
    REG(l4,l5) ∧ MUX(l5, l3, l4, out) ∧ ONE l4
End

Theorem PARITY_LEMMA:
  ∀inp out. PARITY_IMP(inp,out) ⇒
            (out 0 ⇔ T) ∧ ∀t. out(SUC t) ⇔ if inp(SUC t) then ¬(out t) else out t
Proof
  PURE_REWRITE_TAC [PARITY_IMP_def, ONE_def, NOT_def, MUX_def, REG_def]
  \\ rpt strip_tac
  >- metis_tac[]
  >- (qpat_x_assum ‘∀t. out t = X t’
      (fn th => REWRITE_TAC [SPEC “SUC t” th])
      \\ rw[])
QED

Theorem PARITY_CORRECT:
  ∀inp out. PARITY_IMP(inp,out) ⇒ ∀t. out t = PARITY t inp
Proof
  rpt strip_tac
  \\ match_mp_tac UNIQUENESS_LEMMA
  \\ irule PARITY_LEMMA
  \\ rw[]
QED

(* Exercise 1 *)

Definition RESET_REG_def:
  RESET_REG(reset,inp,out) ⇔
    (∀t. reset t ⇒ (out t ⇔ T)) ∧
    (∀t. out (t + 1) = if reset t ∨ reset (t + 1) then T else inp t)
End

Definition RESET_REG_IMP_def:
  RESET_REG_IMP(reset, inp, out) ⇔
    ∃ro1 ro2 mo.
    MUX(reset, reset, ro1, mo) ∧
    REG(reset, ro1) ∧
    REG(inp, ro2) ∧
    MUX(mo, mo, ro2, out)
End

Theorem RESET_REG_CORRECTNESS:
  RESET_REG_IMP(reset, inp, out) ⇒ RESET_REG(reset, inp, out)
Proof
  rw[RESET_REG_IMP_def, RESET_REG_def, REG_def, MUX_def]
  \\ rw[]
  \\ PROVE_TAC[]
QED

(* Exercise 2 *)

Definition RESET_PARITY_def:
  RESET_PARITY(reset, inp, out) ⇔
    (out 0 ⇔ T) ∧
    ∀t. out(t+1) ⇔
          if reset(t+1) then T
          else if inp(t+1) then ¬out t
          else out t
End

Definition RESET_PARITTY_IMP_def:
  RESET_PARITY_IMP(reset, inp, out) ⇔
    ∃mo1 mo2 no oo ro1 ro2.
      MUX(inp, no, ro1, mo1) ∧
      NOT(ro1, no) ∧
      MUX(reset, reset, mo1, mo2) ∧
      ONE(oo) ∧
      REG(oo, ro2) ∧
      MUX(ro2, mo2, oo, out) ∧
      REG(out, ro1)
End

Theorem RESET_PARITY_CORRECTNESS:
  RESET_PARITY_IMP(reset, inp, out) ⇒ RESET_PARITY(reset, inp, out)
Proof
  (* TODO *)
QED
