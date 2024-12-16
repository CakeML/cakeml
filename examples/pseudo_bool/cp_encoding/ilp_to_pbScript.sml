(*
  Formalization of the ILP to PB phase
*)
open preamble ilpTheory pbcTheory pbc_encodeTheory int_bitwiseTheory cpTheory;

val _ = new_theory "ilp_to_pb";

(*
  X: (lb,ub)

  We start from iconstraints:

  ``:'a ilin_term # 'b lin_term # int``

  a X + b Y + c Z + (PB) ≥ d

  a {X0 + 2X1 + 4 X2+ ... } +
  b {-2^n Yc + Y0 + ... } +
  c {...} + (PB) ≥ d
*)

Datatype:
  epb =
  | Tc 'a
  | Bit 'a num
  (* Bit X i is the i-th bit of X *)
  | Var 'b
End

Definition bit_of_int_def:
  bit_of_int i n =
    let (ls,b) = bits_of_int i in
    if n < LENGTH ls then EL n ls
    else b
End

Definition reify_epb_def:
  reify_epb (wi:'a -> int,wb: 'b -> bool) epb ⇔
  case epb of
    Tc X => wi X < 0
  | Bit X n => bit_of_int (wi X) n
  | Var B => wb B
End

Definition bit_width_def:
  bit_width bnd X =
  let (lb,ub) = bnd X in
  (lb < 0,
    MAX (LENGTH (FST (bits_of_int lb)))
        (LENGTH (FST (bits_of_int ub))))
End

Definition encode_ivar_def:
  encode_ivar bnd (X:'a) =
  let (comp,h) = bit_width bnd X in
  let bits = GENLIST (λi. (2**i,Pos (Bit X i))) h in
  if comp then
      (-(2**h),Pos(Tc X)):: bits
  else (bits:('a,'b) epb lin_term)
End

Theorem encode_ivar_sem:
  valid_assignment bnd wi ⇒
  eval_lin_term
    (reify_epb (wi,wb)) (encode_ivar bnd X) =
  wi X
Proof
  rw[encode_ivar_def]>>
  pairarg_tac>>gvs[eval_lin_term_def]>>
  rw[]>>
  simp[MAP_GENLIST,iSUM_def,eval_term_def,o_DEF,reify_epb_def]
  >-
    cheat
  >>
    cheat
    (*
    simp[iSUM_GENLIST_bit_of_int]>>
    `wi X = int_of_bits (bits_of_int (wi X))` by
      fs[int_of_bits_bits_of_int]>>
    pop_assum (fn th => simp[Once th,SimpRHS])>>
    simp[bits_of_int_def]>>
    `¬ (wi X < 0)` by (
      gvs[bit_width_def]>>
      pairarg_tac>>gvs[valid_assignment_def]>>
      first_x_assum drule>>
      intLib.ARITH_TAC)>>
    simp[int_of_bits_def,bit_of_int]>>
    `?n. wi X = &n` by
      intLib.ARITH_TAC>>
    simp[]>>
    gvs[bit_width_def]>> *)
QED

Definition mul_lin_term_def:
  mul_lin_term d ls =
    MAP (λ(c:int,x). (c*d,x)) ls
End

Definition encode_iconstraint_def:
  encode_iconstraint bnd (is,bs,c) =
    (
    GreaterEqual,
    FLAT
      (MAP (λ(d,X).
        mul_lin_term d (encode_ivar bnd X)) is) ++
    MAP (λ(d,l). (d,map_lit Var l)) bs,
    c):(('a,'b) epb pbc)
End

Theorem eval_lin_term_mul_lin_term[simp]:
  ∀c.
  eval_lin_term w (mul_lin_term d c) =
  d * eval_lin_term w c
Proof
  simp[mul_lin_term_def,eval_lin_term_def]>>
  Induct>>rw[iSUM_def]>>
  pairarg_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem encode_iconstraint_sem:
  valid_assignment bnd wi ⇒
  iconstraint_sem iconstr (wi,wb) =
  satisfies_pbc (reify_epb (wi,wb))
   (encode_iconstraint bnd iconstr)
Proof
  `∃is bs c. iconstr = (is,bs,c)`
    by metis_tac[PAIR] >>
  rw[encode_iconstraint_def,satisfies_pbc_def,iconstraint_sem_def,eval_lin_term_def,eval_ilin_term_def]>>
  qmatch_goalsub_abbrev_tac`A + B ≥ _ ⇔ X + Y ≥ _`>>
  `A = X ∧ B = Y` suffices_by simp[]>>
  unabbrev_all_tac>>rw[]
  >- (
    simp[iSUM_FLAT,MAP_FLAT,MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    simp[GSYM eval_lin_term_def]>>
    pairarg_tac>>gvs[]>>
    simp[encode_ivar_sem])
  >- (
    simp[MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    pairarg_tac>>gvs[]>>
    rename1`MEM (_,l) _`>>
    Cases_on`l`>>
    gvs[lit_def,map_lit_def,reify_epb_def])
QED

val _ = export_theory();
