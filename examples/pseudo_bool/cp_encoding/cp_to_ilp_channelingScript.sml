(*
  Formalization of the CP to ILP phase (channeling constraints)
*)
Theory cp_to_ilp_channeling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Inverse: Xs and Ys are inverse permutations
   Xs[i] = j ⇔ Ys[j] = i
   This is very complex as it involves bidirectional constraints
*)

Definition mk_bounds_def:
  mk_bounds X a b =
  [
    mk_constraint_one_ge 1 X a;
    mk_constraint_one_ge (-1) X (-b)
  ]
End

Theorem mk_bounds_sem[simp]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (mk_bounds X a b) ⇔
  varc wi X ≥ a ∧ varc wi X ≤ b
Proof
  simp[mk_bounds_def]>>
  intLib.ARITH_TAC
QED

Definition encode_inverse_def:
  encode_inverse bnd Xsi Ysi =
  let (Xs,offx) = Xsi in
  let (Ys,offy) = Ysi in
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then
    [false_constr]
  else
    FLAT (
      MAP (λX. mk_bounds X offy (offy + &n - 1)) Xs ++
      MAP (λY. mk_bounds Y offx (offx + &n - 1)) Ys ++
      FLAT (GENLIST
        (λi.
          (MAP (λX. encode_full_eq bnd X (offy + &i)) Xs) ++
          (MAP (λY. encode_full_eq bnd Y (offx + &i)) Ys))
        n)) ++
    FLAT (FLAT $ GENLIST
      (λi. GENLIST
        (λj. encode_bvar_eq
          (INL (Eq (EL i Xs) (offy + &j)))
          (INL (Eq (EL j Ys) (offx + &i))))
        n)
      n)
End

Theorem encode_inverse_sem_1:
  valid_assignment bnd wi ∧
  inverse_sem Xsi Ysi wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_inverse bnd Xsi Ysi)
Proof
  simp[encode_inverse_def]>>
  rpt (pairarg_tac>>fs[inverse_sem_def])>>
  rw[]
  >~[‘encode_full_eq _ _ _’]
  >-(
    simp[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP,reify_avar_def]>>
    simp[EVERY_MEM,reify_reif_def])
  >~[‘encode_bvar_eq _ _’]
  >-(
    rw[EVERY_FLAT,EVERY_GENLIST,reify_avar_def,reify_reif_def]>>
    ntac 2 (pop_assum mp_tac)>>
    rename1‘i < _ ⇒ j < _ ⇒ _’>>
    pop_assum $ qspecl_then[‘&i + offx’,‘&j + offy’] mp_tac>>
    simp[]>>
    qmatch_goalsub_abbrev_tac
    ‘(P ⇒ (varc _ (EL a _) = c ⇔ varc _ (EL b _) = d)) ⇒
      Q ⇒ R ⇒ (_ = e ⇔ _ = f)’>>
    ‘(P ⇔ (Q ∧ R)) ∧ a = i ∧ b = j ∧
      c = e ∧ d = f’ suffices_by metis_tac[]>>
    unabbrev_all_tac>>
    intLib.ARITH_TAC)>>
  simp[mk_bounds_def,EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac‘EVERY P (MAP _ _)’>>
  rw[EVERY_MAP,EVERY_MEM,Abbr‘P’]>>
  fs[EVERY_MEM,mk_array_ind_def]>>
  last_x_assum $ drule_then mp_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_inverse_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_inverse bnd Xsi Ysi) ⇒
  inverse_sem Xsi Ysi wi
Proof
  simp[encode_inverse_def]>>
  rpt (pairarg_tac>>fs[inverse_sem_def])>>
  IF_CASES_TAC>>
  rw[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP]>>
  gvs[EVERY_MEM]
  >~[‘varc _ _ = _ ⇔ _’]
  >-cheat>>
  rw[mk_array_ind_def]>>
  last_x_assum $ drule_then mp_tac>>
  intLib.ARITH_TAC
QED

(*
Definition encode_inverse_def:
  encode_inverse bnd Xsi Ysi =
  let (Xs,offx) = Xsi in
  let (Ys,offy) = Ysi in
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then
    [false_constr]
  else
    (* Bounds constraints *)
    MAP (λX. mk_constraint_ge 1 X (-1) (INR offy) 0) Xs ++
    MAP (λX. mk_constraint_ge (-1) X (1) (INR (offy + &n)) (-1)) Xs ++
    MAP (λY. mk_constraint_ge 1 Y (-1) (INR offx) 0) Ys ++
    MAP (λY. mk_constraint_ge (-1) Y (1) (INR (offx + &n)) (-1)) Ys ++
    (* Channeling constraints: Xs[i] = j ⇔ Ys[j] = i
       This requires complex encoding with element constraints *)
    [false_constr]
End
*)

Definition encode_channeling_constr_def:
  encode_channeling_constr bnd c name =
  case c of Inverse Xsi Ysi =>
    encode_inverse bnd Xsi Ysi
End

Theorem encode_channeling_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Channeling c) ∧
  channeling_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_channeling_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_1]
QED

Theorem encode_channeling_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_channeling_constr bnd c name) ⇒
  channeling_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_channeling_constr_def:
  cencode_channeling_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_channeling_constr_sem:
  valid_assignment bnd wi ∧
  cencode_channeling_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_channeling_constr bnd c name) ec ec'
Proof
  cheat
QED
