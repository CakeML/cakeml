(*
  Correctness proof for pan_structs

  Side-stepped for now as the "named_structs_ok" switch in the semantics
  prevents the structures adjusted by the pan_structs phase from appearing
  in a verified program.
*)
Theory pan_structsProof
Ancestors
  panSem pan_structs panProps panLang pan_commonProps
Libs
  preamble

Theorem compile_exps_eq_map[local]:
  compile_exps ctxt = MAP (compile_exp ctxt)
Proof
  rw [FUN_EQ_THM]
  \\ Induct_on `x`
  \\ simp [compile_exp_def]
QED

Theorem opt_mmap_eq_some_el:
  !xs ys. (OPT_MMAP f xs = SOME ys) = (LENGTH xs = LENGTH ys /\
    (!n. n < LENGTH ys ==> f (EL n xs) = SOME (EL n ys)))
Proof
  Induct_on `xs`
  \\ csimp []
  \\ rw []
  \\ Cases_on `ys` \\ fs []
  \\ simp [LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
  \\ metis_tac []
QED

Definition convert_v_def:
  convert_v (Val x) = Val x /\
  convert_v (RStruct xs) = RStruct (MAP convert_v xs) /\
  convert_v (NStruct nm flds) = (let
    vs = MAP (\(nm, v). convert_v v) flds
  in RStruct vs)
End

Definition v_flds_ok_def:
  v_flds_ok _ (Val x) = T /\
  v_flds_ok ctxt (RStruct vs) = EVERY (v_flds_ok ctxt) vs /\
  v_flds_ok ctxt (NStruct nm flds) =
    (EVERY (\(nm, v). v_flds_ok ctxt v) flds /\
        (case ALOOKUP ctxt nm of NONE => F | SOME info =>
            MAP FST flds = MAP FST info.fields /\
            MAP (shape_of o SND) flds = MAP SND info.fields))
End

Definition convert_eshapes_def:
  convert_eshapes str_ctxt = FMAP_MAP2 (\(eid, sh). compile_shape str_ctxt sh)
End

Definition convert_code_def:
  convert_code ctxt = FMAP_MAP2 ((\(nm, (params, prog)).
    (MAP (I ## compile_shape ctxt.structs) params, compile (ctxt with locals := params) prog)))
End

Definition convert_s_def:
  convert_s ctxt s = s with <|
    locals := FMAP_MAP2 (\(nm, v). convert_v v) s.locals;
    globals := FMAP_MAP2 (\(nm, v). convert_v v) s.globals;
    structs := [];
    code := convert_code ctxt s.code;
    eshapes := convert_eshapes ctxt.structs s.eshapes
  |>
End

Definition struct_infos_ok_def:
  struct_infos_ok sh_ctxt <=>
    EVERY (\(nm, info). ALL_DISTINCT (MAP FST info.fields)) sh_ctxt ∧
    ALL_DISTINCT (MAP FST sh_ctxt) ∧
    (!i nm info. i < LENGTH sh_ctxt /\ EL i sh_ctxt = (nm, info) ==>
        EVERY (is_wf_shape (DROP (i + 1) sh_ctxt)) (MAP SND info.fields)) ∧
    EVERY (λ(nm,info). info.size = size_of_sh_with_ctxt sh_ctxt
        (Comb (MAP SND info.fields))) sh_ctxt
End

Theorem alookup_drop_helper[local]:
  ALOOKUP (DROP n xs) k = SOME v /\
  ALL_DISTINCT (MAP FST xs) ==>
  ~ MEM k (MAP FST (TAKE n xs)) /\ ALOOKUP xs k = SOME v
Proof
  strip_tac
  >> subgoal `?ys zs. xs = ys ++ zs /\ LENGTH ys = n`
  >- (
    map_every qexists_tac [`TAKE n xs`, `DROP n xs`]
    >> simp []
    >> Cases_on `n < LENGTH xs`
    >> fs [DROP_LENGTH_TOO_LONG]
  )
  >> fs [DROP_APPEND1, DROP_LENGTH_TOO_LONG, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]
  >> csimp [ALOOKUP_APPEND, option_case_eq, ALOOKUP_NONE]
  >> dxrule ALOOKUP_MEM
  >> fs [ALL_DISTINCT_APPEND]
  >> fs [MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> metis_tac []
QED

Theorem size_of_sh_with_ctxt_drop:
  !sh_ctxt sh. is_wf_shape (DROP n sh_ctxt) sh /\
  ALL_DISTINCT (MAP FST sh_ctxt) ==>
  size_of_sh_with_ctxt (DROP n sh_ctxt) sh = size_of_sh_with_ctxt sh_ctxt sh
Proof
  recInduct size_of_sh_with_ctxt_ind
  >> simp [size_of_sh_with_ctxt_def, is_wf_shape_def]
  >> simp [Cong MAP_CONG, EVERY_MEM]
  >> simp [SF ETA_ss]
  >> rw []
  >> every_case_tac >> fs []
  >> imp_res_tac alookup_drop_helper
  >> simp []
QED

Theorem struct_infos_ok_cons:
  struct_infos_ok xs /\
  ALL_DISTINCT (MAP FST info.fields) /\
  ~ MEM nm (MAP FST xs) /\
  EVERY (is_wf_shape xs) (MAP SND info.fields) /\
  info.size = size_of_sh_with_ctxt xs (Comb (MAP SND info.fields))
  ==>
  struct_infos_ok ((nm, info) :: xs)
Proof
  rw []
  >> fs [struct_infos_ok_def]
  >> conj_asm1_tac
  >- (
    rw []
    >> gs [LT_SUC]
    >> res_tac
    >> fs [ADD1]
  )
  >> first_x_assum (qspec_then `0` assume_tac)
  >> gs []
  >> simp [ (size_of_sh_with_ctxt_drop
        |> Q.SPEC `x :: xs` |> Q.GEN `n` |> Q.SPEC `1`
        |> SIMP_RULE list_ss []) , is_wf_shape_def, SF ETA_ss]
  >> fs [EVERY_EL]
  >> rw []
  >> rpt (first_x_assum drule)
  >> rpt (pairarg_tac >> fs [])
  >> rw []
  >> DEP_REWRITE_TAC [ (size_of_sh_with_ctxt_drop
        |> Q.SPEC `x :: xs` |> Q.GEN `n` |> Q.SPEC `1`
        |> SIMP_RULE list_ss [] |> GSYM)]
  >> simp [is_wf_shape_def, EVERY_MAP]
  >> simp [EVERY_EL]
  >> fs [EL_MAP]
  >> metis_tac [is_wf_shape_drop]
QED

Theorem is_wf_shape_drop:
  !sh_ctxt sh n. is_wf_shape (DROP n sh_ctxt) sh ==>
    is_wf_shape sh_ctxt sh
Proof
  recInduct is_wf_shape_ind
  >> simp [is_wf_shape_def, EVERY_MEM]
  >> rw []
  >- (
    metis_tac []
  )
  >- (
    every_case_tac >> fs [] >>
    qspecl_then [`TAKE n ctxt`, `DROP n ctxt`, `nm`] mp_tac ALOOKUP_APPEND >>
    simp [] >>
    simp [option_case_eq]
  )
QED

Theorem struct_infos_ok_drop:
  struct_infos_ok sh_ctxt ==> struct_infos_ok (DROP n sh_ctxt)
Proof
  rw [struct_infos_ok_def, EVERY_DROP, MAP_DROP, ALL_DISTINCT_DROP]
  >- (
    gs [EL_DROP]
    >> first_x_assum (drule_at (Pat `EL _ _ = _`))
    >> simp [DROP_DROP]
  )
  >-(
    gs [EVERY_EL, EL_DROP]
    >> rw []
    >> fs [arithmeticTheory.SUB_LEFT_LESS]
    >> first_x_assum drule
    >> simp [ELIM_UNCURRY]
    >> dep_rewrite.DEP_REWRITE_TAC [size_of_sh_with_ctxt_drop]
    >> simp [is_wf_shape_def]
    >> rpt (first_x_assum drule)
    >> simp []
    >> pairarg_tac >> fs []
    >> rw [EVERY_EL]
    >> res_tac
    >> irule is_wf_shape_drop
    >> simp [DROP_DROP]
    >> qexists_tac `n' + 1`
    >> simp [DROP_DROP]
  )
QED

Theorem struct_infos_ok_append:
  struct_infos_ok (xs ++ ys) ==> struct_infos_ok ys
Proof
  rw []
  >> drule_then (qspec_then `LENGTH xs` mp_tac) struct_infos_ok_drop
  >> simp [DROP_APPEND2]
QED

Theorem compile_exp_correct_mmap_helper[local]:
  !es vs. OPT_MMAP (eval s) es = SOME vs /\
  (!e. MEM e es ==> (!v. eval s e = SOME v ==>
    eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v))) ==>
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt es) = SOME (MAP convert_v vs)
Proof
  Induct
  >> simp [compile_exp_def, DISJ_IMP_THM, FORALL_AND_THM]
  >> rw []
  >> simp []
QED

Theorem fields_in_order_reorder_noop:
  !eflds info_fields. MAP FST info_fields = MAP FST eflds /\
  ALL_DISTINCT (MAP FST info_fields) ==>
  FLAT (MAP (λ(nm',sh). case ALOOKUP (compile_fields ctxt eflds) nm' of
         NONE => [] | SOME e => [e]) info_fields) =
  MAP (compile_exp ctxt o SND) eflds
Proof
  Induct >>
  simp [MAP_EQ_CONS, EXISTS_PROD] >>
  simp [PULL_EXISTS, FORALL_PROD] >>
  simp [compile_exp_def] >>
  rw [] >>
  irule EQ_TRANS >>
  first_x_assum (irule_at Any) >>
  simp [] >>
  irule_at Any EQ_REFL >>
  simp [] >>
  AP_TERM_TAC >>
  irule MAP_CONG >>
  simp [FORALL_PROD] >>
  rw [] >>
  every_case_tac >> fs [] >>
  gs [MEM_MAP, FORALL_PROD]
QED

Theorem alookup_map_structs_ok[local]:
  ALOOKUP s_ctxt nm = SOME info /\
  struct_infos_ok s_ctxt ==>
  ALL_DISTINCT (MAP FST info.fields)
Proof
  rw []
  >> imp_res_tac ALOOKUP_MEM
  >> fs [struct_infos_ok_def, EVERY_MAP]
  >> imp_res_tac EVERY_MEM
  >> fs []
QED

Theorem opt_mmap_eq_every[local]:
  OPT_MMAP f xs = SOME ys /\
  (!x y. MEM x xs /\ f x = SOME y ==> P y) ==>
  EVERY P ys
Proof
  rw [EVERY_EL]
  >> imp_res_tac opt_mmap_length_eq >> fs []
  >> imp_res_tac opt_mmap_el >> fs []
  >> gs []
  >> res_tac
  >> metis_tac [EL_MEM]
QED

Theorem every_convert_v_eq[local]:
  EVERY (\w. case w of Val _ => T | _ => F) vs ==>
  MAP convert_v vs = vs
Proof
  rw [EVERY_EL, LIST_EQ_REWRITE]
  >> res_tac
  >> every_case_tac
  >> fs [EL_MAP, convert_v_def]
QED

Theorem map_fst_eq_alookup[local]:
  !xs ys. MAP FST xs = MAP FST ys /\
  ALOOKUP xs nm = SOME v ==>
  ?i. afindi nm xs = SOME i /\ afindi nm ys = SOME i /\
    i < LENGTH xs /\ i < LENGTH ys /\
    v = SND (EL i xs) /\ ALOOKUP ys nm = SOME (SND (EL i ys))
Proof
  Induct_on `ys`
  >> simp [FORALL_PROD, MAP_EQ_CONS, PULL_EXISTS]
  >> rw []
  >> simp [afindi_def]
  >> first_x_assum (drule o GSYM)
  >> simp []
  >> disch_then (assume_tac o GSYM)
  >> fs [EL_CONS, PRE_SUB1]
QED

val sh_ctxt = rand ``SND (compile_shape ctxt.structs, ctxt.structs) = sh_ctxt``;
val sh_ctxt_ty = type_of sh_ctxt;

Theorem is_wf_shape_compile_shape:
  (! ^sh_ctxt sh. is_wf_shape str_ctxt (compile_shape sh_ctxt sh))
  ∧
  (! ^sh_ctxt shs. EVERY (is_wf_shape str_ctxt) (compile_shapes sh_ctxt shs))
Proof
  ho_match_mp_tac compile_shape_ind
  >> simp [compile_shape_def, is_wf_shape_def, SF ETA_ss]
  >> rw []
  >> every_case_tac
  >> simp [is_wf_shape_def, SF ETA_ss]
QED

Theorem compile_shapes_eq_map:
  !shs. compile_shapes sctxt shs = MAP (compile_shape sctxt) shs
Proof
  Induct
  >> simp [compile_shape_def]
QED

Definition compile_shape_n_def:
  compile_shape_n sctxt n One = One /\
  compile_shape_n sctxt n (Comb shs) = Comb (MAP (compile_shape_n sctxt n) shs) /\
  compile_shape_n sctxt n (Named nm) = (
    case afindi nm (DROP n sctxt)
    of NONE => One
      | SOME j => let (nm', flds) = EL (n + j) sctxt
      in Comb (MAP (compile_shape_n sctxt (n + j + 1)) (MAP SND flds))
  )
Termination
  WF_REL_TAC `inv_image (measure I LEX measure shape_size)
    (\(sctxt, n, v). (LENGTH sctxt - n, v))`
  >> rw []
  >> CCONTR_TAC
  >> fs [DROP_LENGTH_TOO_LONG, afindi_def]
End

Theorem dropWhile_afindi:
  dropWhile (\(k, v). k <> kx) xs = (case afindi kx xs of
    NONE => []
  | SOME n => DROP n xs)
Proof
  Induct_on `xs`
  >> simp [afindi_def, FORALL_PROD]
  >> rw []
  >> every_case_tac >> fs []
QED

Theorem afindi_less_length:
  !xs n. afindi kx xs = SOME n ==> n < LENGTH xs
Proof
  Induct
  >> simp [afindi_def, FORALL_PROD]
  >> rw []
  >> fs [option_case_eq]
  >> res_tac
  >> simp []
QED

Theorem afindi_MAP_eq:
  !xs. (!x y. MEM (x, y) xs ==> FST (f (x, y)) = x) ==>
  afindi kx (MAP f xs) = afindi kx xs
Proof
  Induct
  >> simp [afindi_def, FORALL_PROD]
  >> rpt gen_tac
  >> Cases_on `f (p_1, p_2)`
  >> simp [DISJ_IMP_THM, FORALL_AND_THM, afindi_def]
  >> rw []
  >> fs [FORALL_PROD]
QED

Theorem compile_shape_n_eq:
  !sctxt n sh. compile_shape_n sctxt n sh = compile_shape (DROP n sctxt) sh
Proof
  recInduct compile_shape_n_ind
  >> simp [compile_shape_n_def, compile_shape_def]
  >> simp [Cong MAP_CONG, compile_shapes_eq_map]
  >> rw []
  >> simp [dropWhile_afindi]
  >> every_case_tac >> fs []
  >> fs [DROP_LENGTH_TOO_LONG]
  >> imp_res_tac afindi_less_length
  >> fs []
  >> first_x_assum (mp_tac o Q.AP_TERM `\xs. (EL 0 xs, DROP 1 xs)`)
  >> fs [HD_DROP, EL_DROP, DROP_DROP, Cong MAP_CONG]
QED

Theorem compile_shape_n_eq_rev[local] =
  Q.SPECL [`sctxt`, `0`] compile_shape_n_eq
  |> SIMP_RULE list_ss []
  |> GSYM


Theorem mem_load_flds_eq:
  ! fld_shs vflds x. mem_load_flds fld_shs x madd memry stcs = SOME vflds ==>
  ?vs. mem_loads (MAP SND fld_shs) x madd memry stcs = SOME vs /\
    LENGTH vs = LENGTH fld_shs /\ vflds = ZIP (MAP FST fld_shs, vs)
Proof
  Induct
  >> simp [mem_load_def, FORALL_PROD]
  >> rpt (gen_tac ORELSE disch_tac)
  >> gvs [option_case_eq, shape_case_eq]
  >> first_x_assum drule
  >> rw []
  >> simp []
QED

Theorem ALOOKUP_eq_afindi:
  ALOOKUP xs nm = OPTION_MAP (\i. SND (EL i xs)) (afindi nm xs)
Proof
  Induct_on `xs`
  >> simp [afindi_def, FORALL_PROD]
  >> rpt gen_tac
  >> TOP_CASE_TAC
  >> simp []
  >> TOP_CASE_TAC
  >> simp [EL_CONS, PRE_SUB1]
QED

Theorem afindi_append:
  !k xs ys. afindi k (xs ++ ys) = (case afindi k xs of
    NONE => OPTION_MAP ((+) (LENGTH xs)) (afindi k ys)
  | SOME i => SOME i
  )
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp [afindi_def, FORALL_PROD]
  >> rw []
  >> every_case_tac >> fs []
QED

Theorem afindi_EL:
  !xs i. afindi k xs = SOME i ==> FST (EL i xs) = k
Proof
  Induct_on `xs`
  >> simp [afindi_def, FORALL_PROD]
  >> rw []
  >> fs [option_case_eq]
  >> res_tac
  >> gvs [EL_CONS, PRE_SUB1]
QED

Theorem wf_shape_struct_infos_ok_helper[local]:
  ALOOKUP (DROP n ctxt) nm = SOME info /\
  struct_infos_ok ctxt ==>
  ?i.
  afindi nm (DROP n ctxt) = SOME i /\
  i + n < LENGTH ctxt /\
  EL (i + n) ctxt = (nm, info) /\
  afindi nm ctxt = SOME (i + n) /\
  (!sh. MEM sh (MAP SND info.fields) ==> is_wf_shape (DROP (i + n + 1) ctxt) sh)
Proof
  rw [struct_infos_ok_def]
  >> subgoal `?c1 c2. ctxt = c1 ++ c2 /\ LENGTH c1 = n`
  >- (
    map_every qexists_tac [`TAKE n ctxt`, `DROP n ctxt`]
    >> simp []
    >> Cases_on `n < LENGTH ctxt`
    >> fs [DROP_LENGTH_TOO_LONG]
  )
  >> fs [DROP_APPEND2]
  >> qspecl_then [`nm`, `c1`, `c2`] mp_tac afindi_append
  >> simp []
  >> Cases_on `ALOOKUP c1 nm`
  >- (
    fs [ALOOKUP_eq_afindi, EL_APPEND2]
    >> imp_res_tac afindi_less_length
    >> imp_res_tac afindi_EL
    >> fs []
    >> simp [PAIR_FST_SND_EQ]
    >> rw []
    >> first_x_assum (qspec_then `i + LENGTH c1` mp_tac)
    >> simp [EL_APPEND2, PAIR_FST_SND_EQ, EVERY_MEM, DROP_APPEND2]
  )
  >- (
    imp_res_tac ALOOKUP_MEM
    >> fs [ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> metis_tac []
  )
QED

Theorem size_of_compile_shape_n[local]:
  (! ^sh_ctxt n sh.
    sh_ctxt = MAP (λ(nm,info). (nm, info.fields)) ctxt /\
    is_wf_shape (DROP n ctxt) sh /\
    struct_infos_ok ctxt ==>
    size_of_sh_with_ctxt [] (compile_shape_n sh_ctxt n sh) = size_of_sh_with_ctxt ctxt sh
  )
Proof
  recInduct compile_shape_n_ind
  >> simp [compile_shape_n_def, size_of_sh_with_ctxt_def, is_wf_shape_def]
  >> rw []
  >- (
    fs [EVERY_MEM]
    >> simp [Cong MAP_CONG, MAP_MAP_o]
    >> simp [SF ETA_ss]
  )
  >- (
    fs [is_wf_shape_def, ALOOKUP_MAP]
    >> fs [CasePred "option"]
    >> drule_then drule wf_shape_struct_infos_ok_helper
    >> strip_tac
    >> fs [GSYM MAP_DROP, afindi_MAP_eq, EL_MAP, ALOOKUP_eq_afindi]
    >> simp [size_of_sh_with_ctxt_def, MAP_MAP_o, o_DEF]
    >> fs [MEM_MAP, PULL_EXISTS]
    >> simp [MAP_MAP_o, o_DEF, Cong MAP_CONG]
    >> fs [struct_infos_ok_def]
    >> imp_res_tac EVERY_EL
    >> gs []
    >> simp [size_of_sh_with_ctxt_def, MAP_MAP_o, o_DEF]
 )
QED

Theorem size_of_compile_shape:
  is_wf_shape ctxt sh /\
  struct_infos_ok ctxt ==>
  size_of_sh_with_ctxt [] (compile_shape (MAP (λ(nm,info). (nm, info.fields)) ctxt) sh) =
    size_of_sh_with_ctxt ctxt sh
Proof
  rw [compile_shape_n_eq_rev]
  >> simp [size_of_compile_shape_n]
QED

Theorem v_flds_ok_append:
  !ctxt v. v_flds_ok ctxt v /\ ALL_DISTINCT (MAP FST pfx ++ MAP FST ctxt) ==>
  v_flds_ok (pfx ++ ctxt) v
Proof
  recInduct v_flds_ok_ind
  >> simp [v_flds_ok_def]
  >> rw []
  >> fs [EVERY_MEM, FORALL_PROD]
  >- (
    metis_tac []
  )
  >- (
    every_case_tac >> fs []
    >> fs [ALOOKUP_APPEND, option_case_eq]
    >> imp_res_tac ALOOKUP_MEM
    >> fs [ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> metis_tac []
  )
QED

Theorem dropWhile_MAP_helper:
  !xs. dropWhile P xs = ys /\
  (!x. MEM x xs ==> P x = Q (f x)) ==>
  dropWhile Q (MAP f xs) = MAP f ys
Proof
  Induct
  >> rw []
  >> gs []
QED

Theorem UNCURRY_EQ_o_SND[local]:
  UNCURRY (\x. f) = (f o SND)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem mem_load_rec1[local] =
  cj 1 mem_load_def |> Q.SPEC `stcs`

Theorem mem_load_rec[local] = LIST_CONJ
  [mem_load_rec1 |> Q.SPEC `One`,
    mem_load_rec1 |> Q.SPEC `Comb shs`,
    mem_load_rec1 |> Q.SPEC `Named nm`]

val x = ``x : 'a word``

Theorem mem_loads_convert_helper[local]:
  !shs vs x.
  mem_loads shs x madd memry stcs = SOME vs /\
  (!sh y v. MEM sh shs /\ mem_load sh y madd memry stcs = SOME v ==>
    size_of_sh_with_ctxt stcs2 (f sh) = size_of_sh_with_ctxt stcs sh /\
    mem_load (f sh) y madd memry stcs2 = SOME (convert_v v)
  ) ==>
  mem_loads (MAP f shs) x madd memry stcs2 = SOME (MAP convert_v vs)
Proof
  Induct_on `shs`
  >> rw [cj 2 mem_load_def, cj 3 mem_load_def]
  >> fs [DISJ_IMP_THM, FORALL_AND_THM, option_case_eq, GSYM AND_IMP_INTRO]
  >> rpt (first_x_assum drule)
  >> simp [SF SFY_ss]
  >> gvs []
QED

Theorem mem_loads_EL:
  !shs vs x i. mem_loads shs x madd memry stcs = SOME vs /\
  i < LENGTH shs ==>
  ?y. mem_load (EL i shs) y madd memry stcs = SOME (EL i vs)
Proof
  Induct
  >> rw [cj 2 mem_load_def, cj 3 mem_load_def]
  >> fs [option_case_eq, LT_SUC]
  >> gvs []
  >> metis_tac []
QED

Theorem mem_loads_mem:
  !shs vs x. mem_loads shs x madd memry stcs = SOME vs /\
  MEM v vs ==>
  ?sh y. MEM sh shs /\ mem_load sh y madd memry stcs = SOME v
Proof
  Induct
  >> rw [cj 2 mem_load_def, cj 3 mem_load_def]
  >> fs [option_case_eq]
  >> gvs []
  >> metis_tac []
QED

Theorem mem_load_conversion:
  (! str2 n shape x v.
  mem_load shape x madd memry (DROP n str_ctxt) = SOME v ∧
  str2 = MAP (λ(nm,info). (nm,info.fields)) str_ctxt ∧
  is_wf_shape (DROP n str_ctxt) shape ∧
  struct_infos_ok str_ctxt ⇒
  mem_load (compile_shape_n str2 n shape) x madd memry [] = SOME (convert_v v) ∧
  v_flds_ok str_ctxt v
  )
Proof
  recInduct compile_shape_n_ind
  >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >- (
    gvs [compile_shape_n_def, mem_load_def, convert_v_def, v_flds_ok_def]
  )
  >- (
    gvs [mem_load_rec, option_case_eq, compile_shape_n_def, is_wf_shape_def]
    >> fs [convert_v_def, SF ETA_ss, v_flds_ok_def]
    >> drule_then (DEP_REWRITE_TAC o single) mem_loads_helper
    >> rw [EVERY_MEM]
    >> imp_res_tac struct_infos_ok_def
    >> fs [EVERY_MEM, size_of_compile_shape_n, size_of_sh_with_ctxt_drop, SF SFY_ss]
    >> imp_res_tac mem_loads_mem
    >> simp [SF SFY_ss]
  )
  >- (
    gvs [compile_shape_n_def, cj 3 mem_load_def, mem_load_rec, convert_v_def,
        v_flds_ok_def,
        option_case_eq, SF ETA_ss, list_case_eq, pair_case_eq, is_wf_shape_def]
    >> fs [CasePred "option"]
    >> drule_then drule wf_shape_struct_infos_ok_helper
    >> strip_tac
    >> fs [afindi_MAP_eq, GSYM MAP_DROP, EL_MAP, mem_load_rec]
    >> simp [option_case_eq]
    >> imp_res_tac mem_load_flds_eq
    >> imp_res_tac mem_loads_some_shape_eq
    >> fs [dropWhile_afindi, ALOOKUP_eq_afindi, MAP_ZIP]
    >> qpat_x_assum `DROP _ _ = _` (mp_tac o GSYM o Q.AP_TERM `\xs. (EL 0 xs, DROP 1 xs)`)
    >> simp [HD_DROP, DROP_DROP]
    >> strip_tac >> fs []
    >> fs [EL_DROP]
    >> drule_then (DEP_REWRITE_TAC o single) mem_loads_helper
    >> rpt conj_tac
    >- (
      rw []
      >> imp_res_tac struct_infos_ok_def
      >> fs [EVERY_MEM, size_of_sh_with_ctxt_drop, size_of_compile_shape_n]
      >> res_tac
      >> simp [SF SFY_ss]
    )
    >- (
      simp [LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
    )
    >- (
      subgoal `EVERY (v_flds_ok str_ctxt) vs`
      >- (
        fs [EVERY_MEM]
        >> imp_res_tac mem_loads_mem
        >> simp []
      )
      >> fs [EVERY_EL, EL_ZIP]
    )
  )
QED

Theorem mem_load_conversion_inst[local] =
  mem_load_conversion |> SIMP_RULE bool_ss []
    |> Q.SPEC `0` |> SIMP_RULE list_ss [compile_shape_n_eq]

Theorem old_exp_shapes_eq:
  old_exp_shapes ctxt es = MAP (old_exp_shape ctxt) es
Proof
  Induct_on `es` >> simp [old_exp_shape_def]
QED

Theorem compile_exp_correct:
  ∀s e v.
  eval s e = SOME v ∧
  alist_to_fmap ctxt.locals = FMAP_MAP2 (shape_of o SND) s.locals ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of o SND ) s.globals ∧
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) s.structs ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.locals ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.globals ∧
  struct_infos_ok s.structs
  ==>
  old_exp_shape ctxt e = shape_of v ∧
  v_flds_ok s.structs v ∧
  eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v)
Proof
  recInduct (name_ind_cases [] eval_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >~ [`NStruct`]
  >- (
    fs [eval_def, UNCURRY_EQ]
    >> fs [option_case_eq, UNCURRY_EQ, UNZIP_MAP]
    >> simp [compile_exp_def, eval_def, convert_v_def]
    >> gvs [v_flds_ok_def, shape_of_def, old_exp_shape_def]
    >> fs [ALOOKUP_MAP]
    >> imp_res_tac opt_mmap_length_eq >> fs []
    >> simp [MAP_ZIP]
    >> imp_res_tac alookup_map_structs_ok
    >> simp [fields_in_order_reorder_noop]
    >> fs [SF ETA_ss]
    >> rpt conj_tac
    >- (
      simp [UNCURRY_EQ_o_SND, o_DEF, GSYM EVERY_MAP, MAP_ZIP]
      >> drule_then irule opt_mmap_eq_every
      >> simp [SF SFY_ss]
    )
    >- (
      gs [EVERY_EL, EL_ZIP, LIST_EQ_REWRITE, EL_MAP]
    )
    >- (
      drule compile_exp_correct_mmap_helper
      >> simp [GSYM MAP_MAP_o, GSYM compile_exps_eq_map]
      >> simp [convert_v_def, UNCURRY_EQ_o_SND, MAP_ZIP, SF ETA_ss]
    )
  )
  >~ [`NField`]
  >- (
    fs [eval_def, option_case_eq, bool_case_eq, v_case_eq, compile_exp_def]
    >> Cases_on `ALOOKUP s.structs nm` >> fs []
    >> simp [convert_v_def, shape_of_def, old_exp_shape_def, alistTheory.ALOOKUP_MAP_2]
    >> fs [shape_of_def, v_flds_ok_def, ALOOKUP_MAP_2]
    >> drule_then drule map_fst_eq_alookup
    >> strip_tac
    >> fs [EL_MAP, EVERY_EL, convert_v_def]
    >> res_tac
    >> fs [ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP]
  )
  >~ [`Load`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, word_lab_case_eq, compile_exp_def,
        is_wf_shape_v_def, convert_v_def]
    >> simp [convert_s_def, is_wf_shape_compile_shape]
    >> drule mem_load_conversion_inst
    >> imp_res_tac mem_loads_some_shape_eq
    >> simp [old_exp_shape_def]
  )
  >~ [`RStruct`]
  >- (
    gvs [eval_def, compile_exp_def, convert_v_def, v_flds_ok_def,
        option_case_eq, old_exp_shape_def, shape_of_def]
    >> fs [SF ETA_ss]
    >> drule_then (irule_at Any) opt_mmap_eq_every
    >> drule_then (irule_at Any) compile_exp_correct_mmap_helper
    >> simp [SF SFY_ss]
    >> fs [old_exp_shapes_eq, LIST_EQ_REWRITE, EL_MAP,
        opt_mmap_eq_some_el, EL_MEM]
  )
  >~ [`RField`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def,
        old_exp_shape_def, shape_of_def, LLOOKUP_THM]
    >> fs [EVERY_EL, convert_v_def, EL_MAP, v_flds_ok_def]
  )
  >~ [`Panop`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def,
        old_exp_shape_def, shape_of_def]
    >> fs [convert_v_def, v_flds_ok_def, SF ETA_ss]
    >> drule_then (simp o single) compile_exp_correct_mmap_helper
    >> imp_res_tac every_convert_v_eq
    >> fs []
  )
  >~ [`Op`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def,
        old_exp_shape_def, shape_of_def]
    >> fs [convert_v_def, v_flds_ok_def, SF ETA_ss]
    >> drule_then (simp o single) compile_exp_correct_mmap_helper
    >> imp_res_tac every_convert_v_eq
    >> fs []
  )
  >> gvs [eval_def, compile_exp_def, convert_v_def, v_flds_ok_def,
    convert_s_def, FLOOKUP_FMAP_MAP2, AllCaseEqs (), old_exp_shape_def,
    shape_of_def]
  >> simp [compile_exp_correct_mmap_helper, EL_MAP]
  >> drule_then drule FEVERY_FLOOKUP
  >> asm_simp_tac bool_ss [GSYM (cj 1 ALOOKUP_EQ_FLOOKUP), FLOOKUP_FMAP_MAP2]
  >> simp []
QED

Theorem evaluate_structs_code_inv[local]:
  evaluate (p, s) = (res, s') ==>
  s'.structs = s.structs ∧ s'.code = s.code
Proof
  rw [] \\ imp_res_tac evaluate_invariants
QED

Theorem eval_upd_code_eq2[local]:
  eval (t with code := code) = eval t
Proof
  simp [eval_upd_code_eq, FUN_EQ_THM]
QED

Theorem res_var_FMAP_MAP2:
  (!y. x = SOME y ==> f (nm, y) = g y) ==>
  res_var (FMAP_MAP2 f fmap) (nm, OPTION_MAP g x) =
  FMAP_MAP2 f (res_var fmap (nm, x))
Proof
  Cases_on `x`
  >> rw []
  >> simp [res_var_def, DOMSUB_FMAP_MAP2, FMAP_MAP2_FUPDATE]
QED

Theorem res_var_FMAP_MAP2_rev:
  FMAP_MAP2 f (res_var fmap (nm, x)) =
  res_var (FMAP_MAP2 f fmap) (nm, OPTION_MAP (\y. f (nm, y)) x)
Proof
  Cases_on `x`
  >> rw []
  >> simp [res_var_def, DOMSUB_FMAP_MAP2, FMAP_MAP2_FUPDATE]
QED

Theorem FEVERY_res_var:
  FEVERY P (res_var fmap (k, opt_v)) =
  (FEVERY P (DRESTRICT fmap (COMPL {k})) /\
    (!v. opt_v = SOME v ==> P (k, v)))
Proof
  Cases_on `opt_v`
  >> simp [res_var_def, fmap_domsub, FEVERY_FUPDATE]
  >> metis_tac []
QED

Theorem shape_of_convert_v_ind[local]:
  ! str_ctxt n sh v.
  struct_infos_ok ctxt /\
  is_wf_shape (DROP n ctxt) sh /\
  v_flds_ok ctxt v /\
  str_ctxt = MAP (λ(nm,info). (nm, info.fields)) ctxt /\
  shape_of v = sh ==>
  compile_shape_n str_ctxt n sh = shape_of (convert_v v)
Proof
  recInduct compile_shape_n_ind
  >> simp [convert_v_def, shape_of_def, compile_shape_n_def,
        compile_shapes_eq_map, MAP_MAP_o, shape_of_val, v_flds_ok_def,
        shape_of_def]
  >> rw []
  >> Cases_on `v`
  >> fs [shape_of_def, shape_of_val, convert_v_def, v_flds_ok_def]
  >- (
    gvs [MAP_MAP_o, o_DEF, MEM_MAP, PULL_EXISTS, is_wf_shape_def, EVERY_MAP]
    >> irule MAP_CONG
    >> fs [v_flds_ok_def, EVERY_MEM]
  )
  >- (
    fs [is_wf_shape_def, CasePred "option"]
    >> drule_then drule wf_shape_struct_infos_ok_helper
    >> strip_tac
    >> fs [GSYM MAP_DROP, afindi_MAP_eq, EL_MAP, GSYM MAP_MAP_o]
    >> gs [LIST_EQ_REWRITE, EL_MAP, ALOOKUP_eq_afindi]
    >> rw []
    >> irule EQ_TRANS
    >> first_x_assum (irule_at Any)
    >> first_x_assum (irule_at Any)
    >> simp [ELIM_UNCURRY, EL_MEM, EL_MAP]
    >> simp [MEM_MAP]
    >> drule_then (irule_at Any) EL_MEM
    >> fs [EVERY_EL, ELIM_UNCURRY]
  )
QED

Theorem shape_of_convert_v:
  ! v str_ctxt n. v_flds_ok ctxt v /\
  str_ctxt = MAP (λ(nm,info). (nm, info.fields)) ctxt /\
  is_wf_shape_v ctxt v /\
  struct_infos_ok ctxt ==>
  compile_shape str_ctxt (shape_of v) = shape_of (convert_v v)
Proof
  rw [compile_shape_n_eq_rev]
  >> drule_then irule shape_of_convert_v_ind
  >> simp [is_wf_shape_of_v]
QED

Theorem shape_of_convert_v_rev[local] =
  SIMP_RULE std_ss [] (GSYM shape_of_convert_v)

Theorem flatten_convert_v:
  !v. flatten (convert_v v) = flatten v
Proof
  recInduct convert_v_ind
  >> simp [convert_v_def, flatten_def, MAP_MAP_o, Cong MAP_CONG]
  >> simp [SF ETA_ss]
  >> rw []
  >> AP_TERM_TAC
  >> irule MAP_CONG
  >> simp [FORALL_PROD, SF SFY_ss]
QED

Theorem map_uncurry_zip_again[local]:
  LENGTH xs = LENGTH ys ==>
  MAP (\(x, y). (f x, g y)) (ZIP (xs, ys)) = ZIP (MAP f xs, MAP g ys)
Proof
  simp [LIST_EQ_REWRITE, EL_MAP, EL_ZIP, FORALL_PROD]
QED

Theorem fupdate_elim2[local]:
  FLOOKUP fm x = SOME y ==>
  FUPDATE fm (x, y) = fm
Proof
  simp [FUPDATE_ELIM, TO_FLOOKUP]
QED

Theorem lookup_code_flds_ok[local]:
  OPT_MMAP (eval s) argexps = SOME args ∧
  lookup_code s.code fname args = SOME (prog, newlocals) ∧
  alist_to_fmap ctxt.locals = FMAP_MAP2 (shape_of o SND) s.locals ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of o SND ) s.globals ∧
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) s.structs ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.locals ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.globals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.locals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.globals ∧
  struct_infos_ok s.structs ⇒
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt argexps) =
    SOME (MAP convert_v args) ∧
  EVERY (\v. v_flds_ok s.structs v) args ∧
  (? new_l.
  lookup_code (convert_s ctxt s).code fname (MAP convert_v args) =
    SOME (compile (ctxt with locals := new_l) prog,
        FMAP_MAP2 (λ(nm,v). convert_v v) newlocals) ∧
    alist_to_fmap new_l = FMAP_MAP2 (shape_of o SND) newlocals
  ) ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) newlocals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) newlocals
Proof
  strip_tac
  >> subgoal `EVERY (\v. is_wf_shape_v s.structs v ∧ v_flds_ok s.structs v) args`
  >- (
    drule_then irule opt_mmap_eq_every
    >> rw []
    >> imp_res_tac eval_is_wf_shape_v
    >> drule_then drule compile_exp_correct
    >> simp []
  )
  >> subgoal `FEVERY (\(nm, v). MEM v args) newlocals`
  >- (
    gvs [lookup_code_def, option_case_eq, bool_case_eq, pair_case_eq]
    >> rw [FEVERY_ALL_FLOOKUP, alistTheory.flookup_fupdate_list, option_case_eq]
    >> dxrule ALOOKUP_MEM
    >> rw []
    >> dxrule_at Any MEM_ZIP_MEM_MAP
    >> fs [LIST_REL_EL_EQN]
  )
  >> rpt conj_tac
  >- (
    irule compile_exp_correct_mmap_helper
    >> simp [compile_exp_correct]
  )
  >- (
    fs [EVERY_MEM]
  )
  >- (
    gvs [lookup_code_def, convert_s_def, option_case_eq, bool_case_eq, pair_case_eq]
    >> fs [convert_code_def, FLOOKUP_FMAP_MAP2,
        FMAP_MAP2_FUPDATE_LIST, FMAP_MAP2_FEMPTY, LIST_REL_MAP]
    >> irule_at Any EQ_REFL
    >> fs [LIST_REL_EL_EQN, EVERY_EL]
    >> simp [map_uncurry_zip_again, fm_empty_zip_alist]
    >> drule_at (Pat `struct_infos_ok _`) shape_of_convert_v_rev
    >> rw []
    >> AP_TERM_TAC
    >> irule LIST_EQ
    >> simp [EL_MAP, EL_ZIP, PAIR_FST_SND_EQ]
  )
  >- (
    fs [FEVERY_ALL_FLOOKUP, EVERY_MEM]
    >> metis_tac []
  )
  >- (
    fs [FEVERY_ALL_FLOOKUP, EVERY_MEM]
    >> metis_tac []
  )
QED

Theorem convert_code_locals_upd[local, simp]:
  convert_code (ctxt with locals updated_by f) code = convert_code ctxt code
Proof
  simp [convert_code_def]
QED

Definition is_cont_res_def:
  is_cont_res NONE = T /\
  is_cont_res (SOME Break) = T /\
  is_cont_res (SOME Continue) = T /\
  is_cont_res _ = F
End

Theorem is_cont_res_eq_disj[local]:
  is_cont_res res = (res = NONE \/ res = SOME Break \/ res = SOME Continue)
Proof
  Cases_on `THE res` >> Cases_on `res` >> fs [is_cont_res_def]
QED

Definition convert_res_def:
  convert_res (SOME Break) = SOME Break /\
  convert_res (SOME (Return v)) = SOME (Return (convert_v v)) /\
  convert_res (SOME (Exception eid ev)) = SOME (Exception eid (convert_v ev)) /\
  convert_res res = res
End

Theorem convert_res_eq_case1[local]:
  convert_res res = (case res of
    SOME Break => convert_res (SOME Break)
  | SOME x => convert_res (SOME x)
  | NONE => NONE)
Proof
  every_case_tac >> simp [convert_res_def]
QED

Theorem convert_res_eq_case[local] =
  REWRITE_RULE [convert_res_def] convert_res_eq_case1

Theorem convert_res_eq_NONE[local] =
  SIMP_CONV (srw_ss ()) [convert_res_eq_case, option_case_eq, result_case_eq]
    ``convert_res res = NONE``

Definition res_vs_def:
  res_vs (SOME (Return v)) = [v] /\
  res_vs (SOME (Exception eid ev)) = [ev] /\
  res_vs _ = []
End

Theorem compile_correct:
  ∀ p s res s' ctxt.
  evaluate (p, s) = (res, s') ∧
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) s.structs ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.locals ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.globals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.locals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.globals ∧
  struct_infos_ok s.structs ∧
  alist_to_fmap ctxt.locals = FMAP_MAP2 (shape_of o SND) s.locals ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of o SND ) s.globals ∧
  res ≠ SOME Error
  ⇒
  evaluate (compile ctxt p, convert_s ctxt s) =
    (convert_res res, convert_s ctxt s') ∧
  FEVERY (\(nm, v). v_flds_ok s'.structs v) s'.locals ∧
  FEVERY (\(nm, v). v_flds_ok s'.structs v) s'.globals ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of o SND ) s'.globals ∧
  (is_cont_res res ==>
    alist_to_fmap ctxt.locals = FMAP_MAP2 (shape_of o SND) s'.locals
  ) ∧
  EVERY (v_flds_ok s'.structs) (res_vs res) ∧
  EVERY (is_wf_shape_v s'.structs) (res_vs res)
Proof
  recInduct (name_ind_cases [] evaluate_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE (disch_then strip_assume_tac))
  >> rpt (qpat_x_assum `!x. _` (assume_named_tac "forall_IH"))
  >> fs [compile_def]
  >~ [`While`]
  >- (
    qpat_x_assum `evaluate _ = _` mp_tac
    >> ONCE_REWRITE_TAC [evaluate_def]
    >> strip_tac
    >> gs [option_case_eq]
    >> drule_then drule compile_exp_correct
    >> gvs [v_case_eq, word_lab_case_eq, convert_v_def, bool_case_eq,
        convert_s_def, empty_locals_def, FMAP_MAP2_FEMPTY, UNCURRY_EQ,
        dec_clock_def, FEVERY_FEMPTY, convert_res_def, is_cont_res_def,
        res_vs_def]
    >> last_x_assum mp_tac
    >> simp [markerTheory.label_def, dec_clock_def, convert_s_def]
    >> disch_then (drule_at (Pat `alist_to_fmap _ = _`))
    >> gs [option_case_eq, result_case_eq, dec_clock_def, convert_s_def,
        convert_res_def, is_cont_res_def, res_vs_def]
    (* down to looping cases *)
    >> rpt disch_tac
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> imp_res_tac evaluate_structs_code_inv
    >> gs [markerTheory.label_def, dec_clock_def, compile_def, convert_s_def,
        is_cont_res_def, res_vs_def]
    >> first_x_assum (drule_at (Pat `alist_to_fmap _ = _`))
    >> simp []
    >> rpt disch_tac
    >> gs []
  )
  >~ [`Dec`]
  >- (
    gs [evaluate_def, AllCaseEqs (), UNCURRY_EQ, eval_upd_code_eq]
    >> drule_then drule compile_exp_correct
    >> strip_tac
    >> gs [markerTheory.label_def]
    >> qmatch_goalsub_abbrev_tac `compile upd_ctxt _`
    >> last_x_assum (qspec_then `upd_ctxt` mp_tac)
    >> fs [markerTheory.Abbrev_def]
    >> simp [FEVERY_FUPDATE, fevery_to_drestrict, FMAP_MAP2_FUPDATE]
    >> simp [convert_s_def, FMAP_MAP2_FUPDATE, FLOOKUP_FMAP_MAP2, SF ETA_ss,
        res_var_FMAP_MAP2_rev]
    >> rpt disch_tac >> gs []
    >> imp_res_tac eval_is_wf_shape_v
    >> gvs [FORALL_AND_THM]
    >> simp [SIMP_RULE std_ss [] shape_of_convert_v]
    >> imp_res_tac evaluate_structs_code_inv
    >> fs []
    >> simp [res_var_FMAP_MAP2_rev, FEVERY_res_var, fevery_to_drestrict,
        SF ETA_ss, fmap_eq_flookup, FLOOKUP_pan_res_var_thm, FLOOKUP_FMAP_MAP2,
        COND_ID]
    >> rw [] >> rw []
    >> imp_res_tac FEVERY_FLOOKUP
    >> fs []
    >> qpat_x_assum `FUPDATE _ _ = _` (mp_tac o GSYM)
    >> simp [fmap_eq_flookup, FLOOKUP_FMAP_MAP2, SF ETA_ss, FLOOKUP_UPDATE]
  )
  >~ [`Assign`]
  >- (
    gvs [evaluate_def, option_case_eq, pair_case_eq, bool_case_eq]
    >> imp_res_tac compile_exp_correct
    >> simp [is_cont_res_def, res_vs_def]
    >> simp [set_kvar_def]
    >> every_case_tac
    >> fs [set_var_def, is_valid_value_def, convert_s_def, FLOOKUP_FMAP_MAP2,
        CasePred "option", FMAP_MAP2_FUPDATE, FEVERY_FUPDATE, fevery_to_drestrict,
        set_global_def, convert_res_def]
    >> simp [fupdate_elim2, FLOOKUP_FMAP_MAP2]
    >> imp_res_tac eval_is_wf_shape_v
    >> imp_res_tac FEVERY_FLOOKUP
    >> fs []
    >> imp_res_tac shape_of_convert_v_rev
    >> simp []
  )
  >~ [`Call`]
  >- (
    (* a bit fiddly, handles the cases in parallel *)
    every_case_tac
    >> gvs [evaluate_def, option_case_eq, pair_case_eq]
    >> drule_then (drule_then (drule_then drule)) lookup_code_flds_ok
    >> simp [EVAL ``(convert_s _ _).clock``]
    >> strip_tac
    >> gvs [bool_case_eq, is_cont_res_def, convert_res_def, empty_locals_def,
        FEVERY_FEMPTY, res_vs_def]
    >> simp [convert_s_def, empty_locals_def, FMAP_MAP2_FEMPTY]
    >> last_x_assum (mp_tac o REWRITE_RULE [markerTheory.label_def])
    >> fs [pair_case_eq, option_case_eq] >> fs []
    >> fs [dec_clock_def]
    >> disch_then (qspec_then `ctxt with locals := new_l` mp_tac)
    >> simp []
    >> imp_res_tac evaluate_structs_code_inv
    >> gvs [bool_case_eq, convert_res_def, is_cont_res_def, empty_locals_def,
        FEVERY_FEMPTY, convert_s_def, FMAP_MAP2_FEMPTY, dec_clock_def,
        pair_case_eq, option_case_eq, result_case_eq, markerTheory.label_def,
        res_vs_def]
    (* Return and Exception cases remain *)
    >~ [`evaluate _ = (SOME (Exception _ _), _)`]
    >- (
      (* Handler case with extra evaluate. *)
      fs [set_var_def, convert_eshapes_def, FLOOKUP_FMAP_MAP2]
      >> strip_tac
      >> first_x_assum (qspec_then `ctxt` mp_tac)
      >> simp [FEVERY_FUPDATE, FMAP_MAP2_FUPDATE, fevery_to_drestrict]
      >> impl_tac
      >- (
        fs []
        >> imp_res_tac evaluate_is_wf_shape_invariant
        >> gs [FEVERY_FUPDATE, fevery_to_drestrict]
        >> fs [is_valid_value_def, CasePred "option"]
        >> simp [FMAP_MAP2_FUPDATE, fupdate_elim2, FLOOKUP_FMAP_MAP2,
            FLOOKUP_UPDATE]
      )
      >> strip_tac
      >> fs [FLOOKUP_FMAP_MAP2, is_valid_value_def, CasePred "option"]
      >> imp_res_tac FEVERY_FLOOKUP
      >> fs []
      >> imp_res_tac shape_of_convert_v_rev
      >> gs [fupdate_elim2, FMAP_MAP2_FUPDATE, FLOOKUP_FMAP_MAP2]
    )
    >> strip_tac
    >> simp [set_kvar_def] >> every_case_tac
    >> fs [is_valid_value_def, CasePred "option"]
    (* sigh @ repeating the "assign" argument again *)
    >> fs [set_var_def, set_global_def, FEVERY_FUPDATE, FMAP_MAP2_FUPDATE,
        fevery_to_drestrict, FLOOKUP_FMAP_MAP2, fupdate_elim2]
    >> imp_res_tac FEVERY_FLOOKUP
    >> fs []
    >> imp_res_tac shape_of_convert_v_rev
    >> qspecl_then [`p`, `_ with <|locals := _; clock := _|>`]
        drule evaluate_global_shape_invariant
    >> simp []
    >> disch_then imp_res_tac
    >> simp [fupdate_elim2, FLOOKUP_FMAP_MAP2]
  )
  >~ [`DecCall`]
  >- (
    (* here we go again *)
    gvs [evaluate_def, option_case_eq, pair_case_eq]
    >> drule_then (drule_then (drule_then drule)) lookup_code_flds_ok
    >> simp [EVAL ``(convert_s _ _).clock``]
    >> strip_tac
    >> gvs [bool_case_eq, is_cont_res_def, convert_res_def, empty_locals_def,
        FEVERY_FEMPTY, res_vs_def]
    >> simp [convert_s_def, empty_locals_def, FMAP_MAP2_FEMPTY]
    >> last_x_assum (mp_tac o REWRITE_RULE [markerTheory.label_def])
    >> fs [pair_case_eq, option_case_eq] >> fs []
    >> fs [dec_clock_def]
    >> disch_then (qspec_then `ctxt with locals := new_l` mp_tac)
    >> simp []
    >> imp_res_tac evaluate_structs_code_inv
    >> gvs [bool_case_eq, convert_res_def, is_cont_res_def, empty_locals_def,
        FEVERY_FEMPTY, convert_s_def, FMAP_MAP2_FEMPTY, dec_clock_def,
        pair_case_eq, option_case_eq, result_case_eq, markerTheory.label_def,
        res_vs_def]
    >> simp [shape_of_convert_v_rev]
    >> strip_tac
    >> fs [UNCURRY_EQ] >> fs []
    >> qmatch_goalsub_abbrev_tac `compile upd_ctxt _`
    >> last_x_assum (qspec_then `upd_ctxt` mp_tac)
    >> fs [markerTheory.Abbrev_def, set_var_def]
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [FEVERY_FUPDATE, fevery_to_drestrict, FMAP_MAP2_FUPDATE]
    >> strip_tac
    >> gvs []
    >> simp [res_var_FMAP_MAP2_rev, FEVERY_res_var, fevery_to_drestrict,
        FLOOKUP_pan_res_var_thm, FLOOKUP_FMAP_MAP2]
    >> conj_tac
    >- (
      rw []
      >> imp_res_tac FEVERY_FLOOKUP
      >> imp_res_tac evaluate_structs_code_inv
      >> fs []
    )
    >> disch_tac
    >> fs []
    >> qpat_x_assum `FUPDATE _ _ = _` (mp_tac o GSYM)
    >> simp [fmap_eq_flookup, FLOOKUP_pan_res_var_thm, FLOOKUP_FMAP_MAP2,
        FLOOKUP_UPDATE]
    >> rw [] >> rw []
  )
  >~ [`ShMemLoad`]
  >- (
    gvs [evaluate_def, option_case_eq, pair_case_eq, bool_case_eq, v_case_eq,
        word_lab_case_eq, flatten_convert_v]
    >> imp_res_tac compile_exp_correct
    >> simp [convert_v_def, convert_s_def, convert_res_def]
    >> fs [lookup_kvar_def, varkind_case_eq, FLOOKUP_FMAP_MAP2, convert_v_def]
    >> gvs [sh_mem_load_def, bool_case_eq, ffiTheory.ffi_result_case_eq,
        set_var_def, set_global_def, is_cont_res_def, FEVERY_FUPDATE,
        fevery_to_drestrict, FMAP_MAP2_FUPDATE, convert_v_def, v_flds_ok_def,
        empty_locals_def, FMAP_MAP2_FEMPTY, FEVERY_FEMPTY, convert_res_def,
        res_vs_def]
    >> simp [fupdate_elim2, FLOOKUP_UPDATE, FLOOKUP_FMAP_MAP2, shape_of_val]
  )
  >~ [`Seq`]
  >- (
    gvs [evaluate_def, UNCURRY_EQ]
    >> rpt (label_x_assum "forall_IH" mp_tac)
    >> simp []
    >> disch_then drule
    >> simp []
    >> gs [bool_case_eq, convert_res_def, is_cont_res_def, convert_res_eq_NONE,
        res_vs_def]
    >> strip_tac
    >> imp_res_tac evaluate_structs_code_inv
    >> fs []
    >> disch_then drule
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [convert_s_def, is_cont_res_def, res_vs_def]
  )
  >~ [`If`]
  >- (
    gvs [evaluate_def, option_case_eq, v_case_eq, word_lab_case_eq]
    >> imp_res_tac compile_exp_correct
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> imp_res_tac evaluate_structs_code_inv
    >> gs [convert_v_def, GSYM (Q.ISPEC `compile c` COND_RAND),
        markerTheory.label_def]
    >> res_tac >> simp []
  )
  >~ [`Return`]
  >- (
    gvs [evaluate_def, option_case_eq, v_case_eq, word_lab_case_eq, bool_case_eq]
    >> imp_res_tac compile_exp_correct
    >> simp [convert_v_def, convert_s_def, flatten_convert_v, convert_res_def,
        empty_locals_def, FMAP_MAP2_FEMPTY, FEVERY_FEMPTY, is_cont_res_def,
        res_vs_def]
    >> imp_res_tac eval_is_wf_shape_v
    >> imp_res_tac is_wf_shape_of_v
    >> imp_res_tac shape_of_convert_v_rev
    >> simp [size_of_compile_shape]
  )
  >~ [`Raise`]
  >- (
    gvs [evaluate_def, option_case_eq, v_case_eq, word_lab_case_eq, bool_case_eq]
    >> imp_res_tac compile_exp_correct
    >> simp [convert_v_def, convert_s_def, flatten_convert_v, convert_res_def,
        empty_locals_def, FMAP_MAP2_FEMPTY, FEVERY_FEMPTY, is_cont_res_def,
        FLOOKUP_FMAP_MAP2, res_vs_def, convert_eshapes_def]
    >> imp_res_tac eval_is_wf_shape_v
    >> imp_res_tac is_wf_shape_of_v
    >> imp_res_tac shape_of_convert_v_rev
    >> simp [size_of_compile_shape]
  )
  >~ [`Tick`]
  >- (
    gvs [evaluate_def, option_case_eq, v_case_eq, word_lab_case_eq, bool_case_eq]
    >> simp [convert_res_def, convert_s_def, empty_locals_def, FMAP_MAP2_FEMPTY,
        FEVERY_FEMPTY, is_cont_res_def, dec_clock_def, res_vs_def]
  )
  >> gvs [evaluate_def, option_case_eq, pair_case_eq, bool_case_eq, v_case_eq,
        word_lab_case_eq, flatten_convert_v, sh_mem_store_def,
        ffiTheory.ffi_result_case_eq, is_cont_res_def]
  >> rw []
  >> imp_res_tac compile_exp_correct
  >> simp [convert_v_def, convert_s_def, flatten_convert_v, convert_res_def,
        empty_locals_def, FMAP_MAP2_FEMPTY, FEVERY_FEMPTY, res_vs_def]
QED

Theorem compile_decs_structs[local]:
  ! ctxt decs decs' ctxt'.
  compile_decs ctxt decs = (decs', ctxt') ==>
  ctxt'.structs = ctxt.structs
Proof
  recInduct compile_decs_ind
  >> simp [compile_decs_def]
  >> rw []
  >> fs [UNCURRY_EQ]
QED

Theorem compile_decls_correct:
  ∀s decs ctxt decs' ctxt'.
  evaluate_decls s decs = SOME s' /\
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) s.structs /\
  ctxt.locals = [] /\
  struct_infos_ok s.structs /\
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.globals /\
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.globals /\
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of ∘ SND) s.globals /\
  compile_decs ctxt decs = (decs', ctxt') ==>
  evaluate_decls (convert_s ctxt' s) decs' =
    SOME (convert_s ctxt' s') /\
  (?gb. ctxt' = (ctxt with globals := gb) /\
  FEVERY (\(nm, v). v_flds_ok s.structs v) s'.globals /\
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s'.globals /\
  s'.structs = s.structs /\
  s'.locals = s.locals /\
  alist_to_fmap gb = FMAP_MAP2 (shape_of ∘ SND) s'.globals
  )
Proof
  recInduct (name_ind_cases [] evaluate_decls_ind)
  >> rpt conj_tac
  >> rpt (gen_tac ORELSE (disch_then strip_assume_tac))
  >> fs [evaluate_decls_def, compile_decs_def]
  >> rpt (pairarg_tac >> fs [])
  >> gvs [evaluate_decls_def, compile_decs_def]
  >- (
    gvs [context_component_equality, FMAP_MAP2_FEMPTY]
  )
  >- (
    simp [SF SFY_ss]
  )
  >- (
    fs [option_case_eq]
    >> fs []
    >> drule_then (qspecl_then [`ctxt`] mp_tac) compile_exp_correct
    >> simp [FEVERY_FEMPTY, FMAP_MAP2_FEMPTY]
    >> strip_tac
    >> gs [convert_s_def, FMAP_MAP2_FEMPTY, FEVERY_FUPDATE, fevery_to_drestrict,
        FEVERY_FEMPTY]
    >> first_x_assum (drule_at (Pat `compile_decs _ _= _`))
    >> fs [markerTheory.Abbrev_def, FMAP_MAP2_FUPDATE]
    >> imp_res_tac eval_is_wf_shape_v
    >> gs [FEVERY_FEMPTY]
    >> strip_tac
    >> gs []
    >> imp_res_tac (REWRITE_CONV [eval_upd_code_eq] ``eval (s with code := c) e = SOME r``)
    >> fs []
    >> gs [shape_of_convert_v_rev]
  )
  >- (
    first_x_assum (drule_at (Pat `compile_decs _ _= _`))
    >> simp []
    >> imp_res_tac compile_decs_structs
    >> simp []
    >> strip_tac
    >> gs [is_wf_shape_compile_shape, EVERY_MAP, ELIM_UNCURRY]
    >> drule_then irule (Q.prove (`evaluate_decls s decs = r /\ s' = s ==>
            evaluate_decls s' decs = r`, simp []))
    >> simp [convert_s_def, convert_code_def, state_component_equality]
    >> simp [FMAP_MAP2_FUPDATE, Cong MAP_CONG, PAIR_MAP, ELIM_UNCURRY]
  )
QED

Theorem decs_stcnames_compile_decs:
  !ctxt decs.
  decs_stcnames acc (FST (compile_decs ctxt decs)) = SOME acc
Proof
  recInduct compile_decs_ind
  >> simp [compile_decs_def, decs_stcnames_def]
  >> rw []
  >> rpt (pairarg_tac >> fs [])
  >> fs [decs_stcnames_def]
QED

Theorem decs_stcnames_to_get_names:
  !acc code res ctxt. decs_stcnames acc code = SOME res /\
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) acc ==>
  get_names ctxt code = (ctxt with structs :=
    MAP (\(nm, info). (nm, info.fields)) res)
Proof
  recInduct decs_stcnames_ind
  >> simp [decs_stcnames_def, get_names_def]
  >> rw []
  >> fs [option_case_eq]
  >> simp [context_component_equality]
QED

Theorem struct_infos_ok_cons:
  struct_infos_ok xs /\
  ALL_DISTINCT (MAP FST info.fields) /\
  ~ MEM nm (MAP FST xs) /\
  EVERY (is_wf_shape xs) (MAP SND info.fields) /\
  info.size = size_of_sh_with_ctxt xs (Comb (MAP SND info.fields))
  ==>
  struct_infos_ok ((nm, info) :: xs)
Proof
  rw []
  >> fs [struct_infos_ok_def]
  >> conj_asm1_tac
  >- (
    rw []
    >> gs [LT_SUC]
    >> res_tac
    >> fs [ADD1]
  )
  >> first_x_assum (qspec_then `0` assume_tac)
  >> gs []
  >> simp [ (size_of_sh_with_ctxt_drop
        |> Q.SPEC `x :: xs` |> Q.GEN `n` |> Q.SPEC `1`
        |> SIMP_RULE list_ss []) , is_wf_shape_def, SF ETA_ss]
  >> fs [EVERY_EL]
  >> rw []
  >> rpt (first_x_assum drule)
  >> rpt (pairarg_tac >> fs [])
  >> rw []
  >> DEP_REWRITE_TAC [ (size_of_sh_with_ctxt_drop
        |> Q.SPEC `x :: xs` |> Q.GEN `n` |> Q.SPEC `1`
        |> SIMP_RULE list_ss [] |> GSYM)]
  >> simp [is_wf_shape_def, EVERY_MAP]
  >> simp [EVERY_EL]
  >> fs [EL_MAP]
  >> metis_tac [is_wf_shape_drop]
QED

Theorem decs_stcnames_infos_ok:
  !acc code res ctxt. decs_stcnames acc code = SOME res /\
  struct_infos_ok acc ==>
  struct_infos_ok res
Proof
  recInduct decs_stcnames_ind
  >> simp [decs_stcnames_def]
  >> rw []
  >> fs [option_case_eq, ALOOKUP_NONE]
  >> first_x_assum irule
  >> irule struct_infos_ok_cons
  >> simp []
QED

Theorem semantics_eq:
  semantics s start <> Fail ∧
  ctxt.structs = MAP (λ(nm,info). (nm,info.fields)) s.structs ∧
  s.locals = FEMPTY ∧
  FEVERY (λ(nm,v). v_flds_ok s.structs v) s.globals ∧
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) s.globals ∧
  ctxt.locals = [] ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of ∘ SND) s.globals ∧
  struct_infos_ok s.structs
  ==>
  semantics (convert_s ctxt s) start = semantics s start
Proof
  rw []
  >> fs [pan_sem_is_wrapper]
  >> drule_then irule semantics_wrapper_eq
  >> csimp []
  >> rw []
  >- (
    gvs [PAIR_FST_SND_EQ]
    >> irule isPREFIX_TRANS
    >> irule_at Any evaluate_add_clock_io_events_mono
    >> simp []
    >> metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    gvs [PAIR_FST_SND_EQ]
    >> irule isPREFIX_TRANS
    >> irule_at Any evaluate_add_clock_io_events_mono
    >> simp []
    >> metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq
    >> simp []
    (* ugh at renaming a variable so it sorts to the right *)
    >> disch_then (qspec_then `x` (mp_tac o Q.GEN `x`))
    >> Cases_on `res = SOME TimeOut` >> fs []
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq
    >> simp []
    (* ugh at renaming a variable so it sorts to the right *)
    >> disch_then (qspec_then `x` (mp_tac o Q.GEN `x`))
    >> Cases_on `res = SOME TimeOut` >> fs []
  )
  >- (
    qexists_tac `0`
    >> drule_then (qspecl_then [`ctxt`] mp_tac) compile_correct
    >> simp [FEVERY_FEMPTY, FMAP_MAP2_FEMPTY]
    >> impl_tac
    >- (
      fs []
      >> CCONTR_TAC >> fs []
    )
    >> simp [compile_def, compile_exp_def]
    >> simp [convert_s_def]
    >> rw []
    >> simp [convert_res_eq_case]
    >> rpt (TOP_CASE_TAC >> simp [])
  )
QED

Theorem compile_top_semantics_decls:
  semantics_decls s start code <> Fail ∧
  s.locals = FEMPTY ∧ s.code = FEMPTY ∧
  s.globals = FEMPTY ⇒
  semantics_decls s start code =
  semantics_decls (s with eshapes :=
        FMAP_MAP2 (\(eid, sh). compile_shape (get_names (<| structs := [] |>) code).structs
            sh) s.eshapes)
    start (compile_top code)
Proof
  rw [semantics_decls_def]
  >> TOP_CASE_TAC >> fs []
  >> TOP_CASE_TAC >> fs []
  >> simp [EVAL ``decs_stcnames [] (compile_top c)``, decs_stcnames_compile_decs]
  >> simp [compile_top_def]
  >> qmatch_goalsub_abbrev_tac `compile_decs nm_ctxt`
  >> Cases_on `compile_decs nm_ctxt code`
  >> drule_then (qspecl_then [`nm_ctxt`] mp_tac) compile_decls_correct
  >> fs [markerTheory.Abbrev_def]
  >> simp [FEVERY_FEMPTY, FMAP_MAP2_FEMPTY]
  >> imp_res_tac decs_stcnames_to_get_names
  >> imp_res_tac decs_stcnames_infos_ok
  >> fs [Q.SPEC `[]` struct_infos_ok_def]
  >> strip_tac
  >> subgoal `!s s' code res. evaluate_decls s code = SOME res /\
        s = s' ==> evaluate_decls s' code = SOME res`
  >> simp []
  >> pop_assum (drule_then (DEP_REWRITE_TAC o single))
  >> simp []
  >> DEP_REWRITE_TAC [semantics_eq]
  >> fs []
  >> simp [convert_s_def, state_component_equality, FMAP_MAP2_FEMPTY,
        convert_code_def, convert_eshapes_def]
QED

Theorem compile_decs_no_names[local]:
  !ctxt decs. EVERY (λd. is_function d ∨ is_decl d)
    (FST (compile_decs ctxt decs))
Proof
  recInduct (name_ind_cases [] compile_decs_ind)
  >> rw [compile_decs_def, ELIM_UNCURRY, is_function_def, is_decl_def]
QED

Theorem compile_top_no_names:
  EVERY (λd. is_function d ∨ is_decl d) (pan_structs$compile_top pan_code)
Proof
  simp [compile_top_def, compile_decs_no_names]
QED

