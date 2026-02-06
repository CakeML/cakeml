(*
  Formalization of the CP to ILP phase (array constraints)
*)
Theory cp_to_ilp_array
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Element: Xs[Y - offset] = Z *)
Definition encode_element_def:
  encode_element bnd Xs Yi Z =
  [false_constr]
End

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem Xs Yi Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element bnd Xs Yi Z)
Proof
  cheat
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element bnd Xs Yi Z) ⇒
  element_sem Xs Yi Z wi
Proof
  cheat
QED

(* Element2D: Xss[Y1 - offset1][Y2 - offset2] = Z *)
Definition encode_element2d_def:
  encode_element2d bnd Xss Y1i Y2i Z =
  [false_constr]
End

Theorem encode_element2d_sem_1:
  valid_assignment bnd wi ∧
  element2d_sem Xss Y1i Y2i Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element2d bnd Xss Y1i Y2i Z)
Proof
  cheat
QED

Theorem encode_element2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element2d bnd Xss Y1i Y2i Z) ⇒
  element2d_sem Xss Y1i Y2i Z wi
Proof
  cheat
QED

Definition arri_def[simp]:
  arri name (i:num) =
    INR (name, Indices [i] NONE)
End

(* ArrayMax: Y = max(Xs) *)
Definition cencode_array_max_def:
  cencode_array_max bnd Xs Y name =
  if NULL Xs
  then cfalse_constr
  else
    Append
      (flat_app (MAPi (λi X. cvar_imply bnd (arri name i) (mk_ge X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ int_to_string #"-" (&i) ^ strlit"le"]
            [mk_le X Y]) Xs)) $
        cat_least_one name $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
End

Definition encode_array_max_def:
  encode_array_max bnd Xs Y name =
  abstr $ cencode_array_max bnd Xs Y name
End

Theorem encode_array_max_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array (ArrayMax Xs Y)) ∧
  array_max_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_max bnd Xs Y name)
Proof
  Cases_on ‘NULL Xs’>>
  rw[cencode_array_max_def,encode_array_max_def,array_max_sem_def]>>
  gvs[NULL_EQ]>>
  rw[EVERY_FLAT,Once EVERY_MEM]>>
  gvs[MEM_FLAT,MEM_MAPi]
  >-(
    simp[reify_avar_def,reify_flag_def]>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_MEM,MEM_MAP,SF DNF_ss]>>
    drule EL_MEM>>
    strip_tac>>
    first_x_assum drule>>
    intLib.ARITH_TAC)>>
  gs[MEM_EL,SF DNF_ss,MEM_MAP]>>
  rename1 ‘n < LENGTH _’>>
  qexists ‘n’>>
  simp[reify_avar_def,reify_flag_def,EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_array_max_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_max bnd Xs Y name) ⇒
  array_max_sem Xs Y wi
Proof
  simp[encode_array_max_def,cencode_array_max_def,array_max_sem_def]>>
  Cases_on ‘NULL Xs’>>
  gs[NULL_EQ]
  >-simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    rename1 ‘n < LENGTH Xs’>>
    qexists ‘n’>>
    ntac 3 (first_x_assum $ drule_then assume_tac)>>
    simp[EL_MAP]>>
    intLib.ARITH_TAC)>>
  gs[EL_MAP]>>
  first_x_assum $ drule_then assume_tac>>
  intLib.ARITH_TAC
QED

Theorem cencode_array_max_sem:
  enc_rel wi (cencode_array_max bnd Xs Y name) (encode_array_max bnd Xs Y name) ec ec
Proof
  simp[encode_array_max_def]
QED

(* ArrayMin: Y = min(Xs) *)
Definition cencode_array_min_def:
  cencode_array_min bnd Xs Y name =
  if NULL Xs
  then cfalse_constr
  else
    Append
      (flat_app (MAPi (λi X. cvar_imply bnd (arri name i) (mk_le X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ int_to_string #"-" (&i) ^ strlit"ge"]
            [mk_ge X Y]) Xs)) $
        cat_least_one name $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
End

Definition encode_array_min_def:
  encode_array_min bnd Xs Y name =
  abstr $ cencode_array_min bnd Xs Y name
End

Theorem encode_array_min_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array (ArrayMin Xs Y)) ∧
  array_min_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_min bnd Xs Y name)
Proof
  Cases_on ‘NULL Xs’>>
  rw[cencode_array_min_def,encode_array_min_def,array_min_sem_def]>>
  gvs[NULL_EQ]>>
  rw[EVERY_FLAT,Once EVERY_MEM]>>
  gvs[MEM_FLAT,MEM_MAPi]
  >-(
    simp[reify_avar_def,reify_flag_def]>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_MEM,MEM_MAP,SF DNF_ss]>>
    drule EL_MEM>>
    strip_tac>>
    first_x_assum drule>>
    intLib.ARITH_TAC)>>
  gs[MEM_EL,SF DNF_ss,MEM_MAP]>>
  rename1 ‘n < LENGTH _’>>
  qexists ‘n’>>
  simp[reify_avar_def,reify_flag_def,EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_array_min_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_min bnd Xs Y name) ⇒
  array_min_sem Xs Y wi
Proof
  simp[encode_array_min_def,cencode_array_min_def,array_min_sem_def]>>
  Cases_on ‘NULL Xs’>>
  gs[NULL_EQ]
  >-simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    rename1 ‘n < LENGTH Xs’>>
    qexists ‘n’>>
    ntac 3 (first_x_assum $ drule_then assume_tac)>>
    simp[EL_MAP]>>
    intLib.ARITH_TAC)>>
  gs[EL_MAP]>>
  first_x_assum $ drule_then assume_tac>>
  intLib.ARITH_TAC
QED

Theorem cencode_array_min_sem:
  enc_rel wi (cencode_array_min bnd Xs Y name) (encode_array_min bnd Xs Y name) ec ec
Proof
  simp[encode_array_min_def]
QED

Definition encode_array_constr_def:
  encode_array_constr bnd c name =
  case c of
    Element Xs Yi Z => encode_element bnd Xs Yi Z
  | Element2D Xss Y1i Y2i Z => encode_element2d bnd Xss Y1i Y2i Z
  | ArrayMax Xs Y => encode_array_max bnd Xs Y name
  | ArrayMin Xs Y => encode_array_min bnd Xs Y name
End

Theorem encode_array_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array c) ∧
  array_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_1]
  >- metis_tac[encode_element2d_sem_1]
  >- metis_tac[encode_array_max_sem_1]
  >- metis_tac[encode_array_min_sem_1]
QED

Theorem encode_array_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_constr bnd c name) ⇒
  array_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_2]
  >- metis_tac[encode_element2d_sem_2]
  >- metis_tac[encode_array_max_sem_2]
  >- metis_tac[encode_array_min_sem_2]
QED

(* Concrete encodings *)
Definition cencode_array_constr_def:
  cencode_array_constr bnd c name ec =
  case c of
    Element Xs Yi Z => (List [], ec)
  | Element2D Xss Y1i Y2i Z => (List [], ec)
  | ArrayMax Xs Y => (cencode_array_max bnd Xs Y name,ec)
  | ArrayMin Xs Y => (cencode_array_min bnd Xs Y name,ec)
End

Theorem cencode_array_constr_sem:
  valid_assignment bnd wi ∧
  cencode_array_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_array_constr bnd c name) ec ec'
Proof
  Cases_on‘c’>>
  rw[cencode_array_constr_def,encode_array_constr_def]
  >- cheat
  >- cheat
  >- metis_tac[cencode_array_max_sem]
  >- metis_tac[cencode_array_min_sem]
QED
