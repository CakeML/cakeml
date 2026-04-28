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

val sh_ctxt = rand ``SND (compile_shape ctxt.structs, ctxt.structs) = sh_ctxt``;
val sh_ctxt_ty = type_of sh_ctxt;

Definition convert_v_def:
  convert_v (Val x) = Val x /\
  convert_v (RStruct xs) = RStruct (MAP convert_v xs) /\
  convert_v (NStruct nm flds) = (let
    vs = MAP (\(nm, v). convert_v v) flds
  in RStruct vs)
End

Definition v_flds_ok_def:
  v_flds_ok _ (Val x) = T /\
  v_flds_ok sh_ctxt (RStruct vs) = EVERY (v_flds_ok sh_ctxt) vs /\
  v_flds_ok sh_ctxt (NStruct nm flds) =
    (EVERY (\(nm, v). v_flds_ok sh_ctxt v) flds /\
        (case ALOOKUP sh_ctxt nm of NONE => F | SOME flds2 => MAP FST flds = MAP FST flds2)) 
End

Definition convert_s_def:
  convert_s s = s with <|
    locals := FMAP_MAP2 (\(nm, v). convert_v v) s.locals;
    globals := FMAP_MAP2 (\(nm, v). convert_v v) s.globals;
    structs := []
  |>
End

Definition s_contents_ok_def:
  s_contents_ok sh_ctxt s = (
    FEVERY (\(nm, v). v_flds_ok sh_ctxt v) s.locals /\
    FEVERY (\(nm, v). v_flds_ok sh_ctxt v) s.globals
  )
End

Definition is_wf_shape_ctxt_def:
  is_wf_shape_ctxt [] = T ∧
  is_wf_shape_ctxt ((nm, flds) :: sh_ctxt) = (
    EVERY (is_wf_shape sh_ctxt) (MAP SND flds) ∧
    is_wf_shape_ctxt sh_ctxt
  )
End

Definition structs_ok_def:
  structs_ok sh_ctxt <=>
    EVERY (\(nm, flds). ALL_DISTINCT (MAP FST flds)) sh_ctxt ∧
    ALL_DISTINCT (MAP FST sh_ctxt) ∧
    is_wf_shape_ctxt sh_ctxt
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
  cheat
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

Theorem is_wf_shape_ctxt_drop:
  !sh_ctxt n. is_wf_shape_ctxt sh_ctxt ==> is_wf_shape_ctxt (DROP n sh_ctxt)
Proof
  Induct
  >> simp [is_wf_shape_ctxt_def]
  >> Cases_on `n`
  >> simp [is_wf_shape_ctxt_def, FORALL_PROD]
QED

Theorem structs_ok_drop:
  structs_ok sh_ctxt ==> structs_ok (DROP n sh_ctxt)
Proof
  rw [structs_ok_def, EVERY_DROP, MAP_DROP, ALL_DISTINCT_DROP,
    is_wf_shape_ctxt_drop]
QED

Theorem compile_shape_eq:
  (! ^sh_ctxt shape. is_wf_shape_nil shape ==>
    compile_shape sh_ctxt shape = shape) ∧
  (! ^sh_ctxt shapes. EVERY is_wf_shape_nil shapes ==>
    compile_shapes sh_ctxt shapes = shapes)
Proof
  ho_match_mp_tac compile_shape_ind
  \\ simp [compile_shape_def, is_wf_shape_def, SF ETA_ss]
QED

Theorem compile_exp_correct_mmap_helper[local]:
  !es vs. OPT_MMAP (eval s) es = SOME vs /\
  (!e. MEM e es ==> (!v. eval s e = SOME v ==>
    eval (convert_s s) (compile_exp ctxt e) = SOME (convert_v v))) ==>
  OPT_MMAP (eval (convert_s s)) (compile_exps ctxt es) = SOME (MAP convert_v vs)
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
  ALOOKUP s.structs nm = SOME info /\
  structs_ok (MAP (λ(nm,info). (nm, info.fields)) s.structs) ==>
  ALL_DISTINCT (MAP FST info.fields)
Proof
  rw []
  >> imp_res_tac ALOOKUP_MEM
  >> fs [structs_ok_def, EVERY_MAP]
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

Theorem is_wf_shape_nil_compile_shape:
  (! ^sh_ctxt sh. is_wf_shape_nil (compile_shape sh_ctxt sh))
  ∧
  (! ^sh_ctxt shs. EVERY is_wf_shape_nil (compile_shapes sh_ctxt shs))
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

Theorem ALOOKUP_ALL_DISTINCT_split:
  ALL_DISTINCT (MAP FST xs) /\ ALOOKUP xs nm = SOME y ==>
  ?xs1 xs2. xs = xs1 ++ [(nm, y)] ++ xs2 /\
  ~ MEM nm (MAP FST xs1) /\ ~ MEM nm (MAP FST xs2)
Proof
  Induct_on `xs`
  >> simp [FORALL_PROD]
  >> rw []
  >- (
    qexists_tac `[]`
    >> simp []
  )
  >> fs []
  >> REWRITE_TAC [GSYM (cj 2 APPEND)]
  >> irule_at Any EQ_REFL
  >> simp []
QED

Theorem ALOOKUP_ALL_DISTINCT_DROP_split:
  !xs n. ALL_DISTINCT (MAP FST xs) /\ ALOOKUP (DROP n xs) nm = SOME y ==>
  ?xs1 xs2. xs = xs1 ++ [(nm, y)] ++ xs2 /\
  n <= LENGTH xs1 /\ ~ MEM nm (MAP FST xs1) /\ ~ MEM nm (MAP FST xs2)
Proof
  rw []
  >> qspecl_then [`TAKE n xs`, `DROP n xs`, `nm`] mp_tac ALOOKUP_APPEND
  >> simp []
  >> TOP_CASE_TAC
  >- (
    rw []
    >> drule_then drule ALOOKUP_ALL_DISTINCT_split
    >> rw []
    >> irule_at Any EQ_REFL
    >> simp []
    >> CCONTR_TAC
    >> fs [DROP_APPEND, TAKE_APPEND, ALOOKUP_APPEND]
    >> fs [option_case_eq]
  )
  >- (
    imp_res_tac ALOOKUP_MEM
    >> fs [MEM_SPLIT]
    >> qspecl_then [`n`, `xs`] mp_tac TAKE_DROP
    >> asm_simp_tac bool_ss []
    >> rw []
    >> fs [ALL_DISTINCT_APPEND]
  )
QED

Theorem size_of_compile_shape_ind[local]:
  (! ^sh_ctxt sh ctxt n.
    sh_ctxt = MAP (λ(nm,info). (nm, info.fields)) (DROP n ctxt) /\
    is_wf_shape (DROP n ctxt) sh /\
    struct_infos_ok ctxt ==>
    size_of_sh_with_ctxt [] (compile_shape sh_ctxt sh) = size_of_sh_with_ctxt ctxt sh
  ) /\
  (! ^sh_ctxt shs ctxt n.
    sh_ctxt = MAP (λ(nm,info). (nm, info.fields)) (DROP n ctxt) /\
    EVERY (is_wf_shape (DROP n ctxt)) shs /\
    struct_infos_ok ctxt ==>
    SUM (MAP (size_of_sh_with_ctxt []) (compile_shapes sh_ctxt shs)) =
      SUM (MAP (size_of_sh_with_ctxt ctxt) shs)
  )
Proof
  ho_match_mp_tac compile_shape_ind
  >> rw []
  >> simp [compile_shape_def, size_of_sh_with_ctxt_def]
  >> fs [SF ETA_ss, is_wf_shape_def]
  (* one non-trivial case, named shapes *)
  >> fs [ALOOKUP_MAP]
  >> Cases_on `ALOOKUP (DROP n ctxt) nm` >> fs []
  >> imp_res_tac struct_infos_ok_def
  >> drule_then drule ALOOKUP_ALL_DISTINCT_DROP_split
  >> strip_tac
  >> fs [DROP_APPEND1]
  >> fs [dropWhile_APPEND_EXISTS]
  >> dep_rewrite.DEP_REWRITE_TAC [dropWhile_APPEND_EVERY]
  >> conj_asm1_tac
  >- (
    simp [EVERY_MAP, ELIM_UNCURRY]
    >> irule EVERY_DROP
    >> fs [EVERY_MEM, MEM_MAP]
    >> metis_tac []
  )
  >> fs [dropWhile_APPEND_EVERY]
  >> simp [size_of_sh_with_ctxt_def]
  >> simp [ALOOKUP_APPEND, last (RES_CANON ALOOKUP_NONE)]
  >> simp [size_of_sh_with_ctxt_def, SF ETA_ss]
  >> irule EQ_TRANS
  >> last_x_assum (irule_at Any)
  >> qexists_tac `LENGTH xs1 + 1`
  >> simp [DROP_APPEND2]
  >> rfs [struct_infos_ok_def]
  >> first_x_assum (qspec_then `LENGTH xs1` mp_tac)
  >> simp [EL_APPEND, DROP_APPEND2]
QED

Theorem size_of_compile_shape:
  is_wf_shape ctxt sh /\
  struct_infos_ok ctxt ==>
  size_of_sh_with_ctxt [] (compile_shape (MAP (λ(nm,info). (nm, info.fields)) ctxt) sh) =
    size_of_sh_with_ctxt ctxt sh
Proof
  rw []
  >> irule EQ_TRANS
  >> drule_at_then Any (irule_at Any) (cj 1 size_of_compile_shape_ind)
  >> qexists_tac `0`
  >> simp []
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



val x = ``x : 'a word``


Theorem mem_load_conversion:
  (! str2 shape ^x madd mem str v.
  mem_load shape x madd mem str = SOME v ∧
  str2 = MAP (λ(nm,info). (nm,info.fields)) str ∧
  is_wf_shape str shape ∧
  struct_infos_ok str ⇒
  mem_load (compile_shape str2 shape) x madd mem [] = SOME (convert_v v)
  ) ∧
  (! str2 shapes ^x madd mem str vs.
  mem_loads shapes x madd mem str = SOME vs ∧
  str2 = MAP (λ(nm,info). (nm,info.fields)) str  ∧
  EVERY (is_wf_shape str) shapes ∧
  struct_infos_ok str ⇒
  mem_loads (compile_shapes str2 shapes) x madd mem [] = SOME (MAP convert_v vs)
  )
Proof
  ho_match_mp_tac compile_shape_ind
  >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >- (
    gvs [compile_shape_def, mem_load_def, convert_v_def, v_flds_ok_def]
  )
  >- (
    gvs [compile_shape_def, mem_load_def, convert_v_def, v_flds_ok_def,
        option_case_eq, SF ETA_ss, is_wf_shape_def]
    >> first_x_assum drule
    >> simp []
  )
  >- (
    gvs [compile_shape_def, mem_load_def, convert_v_def, v_flds_ok_def,
        option_case_eq, SF ETA_ss, list_case_eq, pair_case_eq, is_wf_shape_def]
    >> simp [ALOOKUP_MAP]
    >> fs [CasePred "option"]
    >> imp_res_tac struct_infos_ok_def
    >> drule_then drule ALOOKUP_ALL_DISTINCT_split
    >> strip_tac
    >> fs [DROP_APPEND1, dropWhile_APPEND_EXISTS]
    >> fs [REWRITE_RULE [EVERY_MEM] dropWhile_APPEND_EVERY, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> dep_rewrite.DEP_REWRITE_TAC [REWRITE_RULE [EVERY_MEM] dropWhile_APPEND_EVERY]
    >> simp [MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> gvs []
    >> imp_res_tac mem_load_flds_eq
    >> first_x_assum (drule_at (Pat `mem_loads _ _ _ _ _ = SOME _`))
    >> simp []
    >> dep_rewrite.DEP_REWRITE_TAC [REWRITE_RULE [EVERY_MEM] dropWhile_APPEND_EVERY]
    >> simp [MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> impl_tac
    >- (
      imp_res_tac struct_infos_ok_append
      >> simp []
      >> rfs [struct_infos_ok_def]
      >> rpt (first_x_assum (qspec_then `LENGTH xs1` mp_tac))
      >> simp [EL_APPEND2, EL_APPEND1, DROP_APPEND2]
    )
    >> strip_tac
    >> simp []
    >> simp [LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
  )
  >- (
    gvs [compile_shape_def, mem_load_def, convert_v_def, v_flds_ok_def]
  )
  >- (
    gvs [compile_shape_def, convert_v_def, v_flds_ok_def]
    >> fs [cj 3 mem_load_def, option_case_eq]
    >> rpt (first_x_assum drule)
    >> gvs []
    >> simp [size_of_compile_shape]
  )
QED


Theorem compile_exp_correct:
  ∀s e ctxt v.
  eval s e = SOME v ∧
  MAP (\(nm, info). (nm, info.fields)) s.structs = ctxt.structs ∧
  FEVERY (\(nm, v). v_flds_ok ctxt.structs v) s.locals ∧
  FEVERY (\(nm, v). v_flds_ok ctxt.structs v) s.globals ∧
  structs_ok ctxt.structs
  ⇒
  v_flds_ok ctxt.structs v ∧ 
  eval (convert_s s) (compile_exp ctxt e) = SOME (convert_v v)

Proof

  recInduct (name_ind_cases [] eval_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >~ [`NStruct`]
  >- (
    fs [eval_def, UNCURRY_EQ]
    >> fs [option_case_eq, UNCURRY_EQ, UNZIP_MAP]
    >> simp [compile_exp_def, eval_def, convert_v_def]
    >> gvs [v_flds_ok_def]
    >> qpat_x_assum `MAP _ _ = _.structs` (assume_tac o GSYM)
    >> fs [ALOOKUP_MAP]
    >> imp_res_tac opt_mmap_length_eq >> fs []
    >> csimp [LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
    >> simp [SF ETA_ss]
    >> conj_tac
    >- (
      ONCE_REWRITE_TAC [ELIM_UNCURRY]
      >> simp [every_zip_snd]
      >> drule_then (irule_at Any) opt_mmap_eq_every
      >> simp []
      >> metis_tac []
    )
    >> imp_res_tac alookup_map_structs_ok
    >> simp [fields_in_order_reorder_noop]
    >> simp [GSYM MAP_MAP_o, GSYM compile_exps_eq_map]
    >> fs [SF ETA_ss]
    >> dxrule compile_exp_correct_mmap_helper
    >> simp [convert_v_def, LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
  )
  >~ [`NField`]
  >- (
    fs [eval_def, option_case_eq, bool_case_eq, v_case_eq, compile_exp_def]
    >> subgoal `old_exp_shape ctxt e = shape_of (THE (eval s e))`
    >- cheat
    >> simp [shape_of_def, convert_v_def]
    >> Cases_on `ALOOKUP s.structs nm` >> fs []
    >> qpat_x_assum `MAP _ _ = _.structs` (assume_tac o GSYM)
    >> simp [alistTheory.ALOOKUP_MAP_2]
    >> first_x_assum (drule_at (Pat `FEVERY _ _`))
    >> simp [v_flds_ok_def, ALOOKUP_MAP_2]
    >> strip_tac
    >> drule_then drule map_fst_eq_alookup
    >> strip_tac
    >> fs [EL_MAP, EVERY_EL, convert_v_def]
    >> res_tac
    >> fs [ELIM_UNCURRY]
  )
  >~ [`Load`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, word_lab_case_eq, compile_exp_def,
        is_wf_shape_v_def, convert_v_def]
    >> simp [convert_s_def, is_wf_shape_nil_compile_shape]

mem_load_def

word_lab_case_eq
 

MEM_SPLIT_APPEND_first

print_match [] ``afindi``

DB.apropos ``MEM _ _`` |> DB.apropos_in ``(++)``

    >> imp_res_tac ALOOKUP_MEM
 
  >~ [`RStruct`]
  >- (
    gvs [eval_def, compile_exp_def, convert_v_def, v_flds_ok_def, option_case_eq]
    >> fs [SF ETA_ss]
    >> drule_then (irule_at Any) opt_mmap_eq_every
    >> drule_then (irule_at Any) compile_exp_correct_mmap_helper
    >> simp [SF SFY_ss]
  )
  >~ [`RField`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def]
    >> fs [EVERY_EL, convert_v_def, EL_MAP, v_flds_ok_def]
  )
  >~ [`Panop`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def]
    >> fs [convert_v_def, v_flds_ok_def, SF ETA_ss]
    >> drule_then (simp o single) compile_exp_correct_mmap_helper
    >> imp_res_tac every_convert_v_eq
    >> fs []
  )
  >~ [`Op`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def]
    >> fs [convert_v_def, v_flds_ok_def, SF ETA_ss]
    >> drule_then (simp o single) compile_exp_correct_mmap_helper
    >> imp_res_tac every_convert_v_eq
    >> fs []
  )



  >> TRY (all_tac
  >> gvs [eval_def, compile_exp_def, convert_v_def, v_flds_ok_def,
    convert_s_def, FLOOKUP_FMAP_MAP2, AllCaseEqs ()]
  >> simp [compile_exp_correct_mmap_helper, EL_MAP]
  >> drule_then drule FEVERY_FLOOKUP
  >> simp []
  >> NO_TAC)



  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def]
    >> fs [EVERY_EL, convert_v_def, EL_MAP, v_flds_ok_def, SF ETA_ss]
    >> drule_then (simp o single) compile_exp_correct_mmap_helper
 
    >> simp [compile_exp_correct_mmap_helper, SF SFY_ss]
    >> drule_then (irule_at Any) compile_exp_correct_mmap_helper
    

    >> fs [EVERY_EL, convert_v_def, EL_MAP, v_flds_ok_def]

  >> TRY (all_tac
  >> gvs [eval_def, compile_exp_def, convert_v_def, v_flds_ok_def,
    convert_s_def, FLOOKUP_FMAP_MAP2, AllCaseEqs ()]
  >> imp_res_tac every_convert_v_eq
  >> simp [compile_exp_correct_mmap_helper, EL_MAP]
  >> drule_then drule FEVERY_FLOOKUP
  >> simp []
  >> NO_TAC)

print_find "fst_zip"
print_find "map_fst"
print_find "flookup_fmap"

print_match [] ``ALOOKUP (MAP _ _)``;
fs [Q.ISPEC `MAP _ _` EQ_SYM_EQ |> Q.SPEC `_.structs`]
print_find "comm"
EQ_COMM

print_find "opt_mmap_el";

  )
  >~ [`NField`]
  >- (
    gs [eval_def, UNCURRY_EQ, v_case_eq, option_case_eq]
  )
  >~ [`RField`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def, is_wf_shape_v_def]
    >> fs [FORALL_AND_THM, EVERY_EL]
  )
  >~ [`Load`]
  >- (
    gvs [eval_def, AllCaseEqs (), compile_exp_def, is_wf_shape_v_def]
    >> simp [compile_shape_eq]
  )
  >> gvs [eval_def, compile_exp_def, AllCaseEqs (), is_wf_shape_v_def]
  >> imp_res_tac FEVERY_FLOOKUP
  >> fs []
  >> dxrule compile_exp_correct_mmap_helper
  >> simp []
QED

Theorem compile_exp_correct_eq[local]:
  ∀s e v.
  eval s e <> NONE /\ s.structs = []
  ⇒
  eval s (compile_exp ctxt e) = eval s e
Proof
  rw []
  \\ Cases_on `eval s e` \\ fs []
  \\ dxrule compile_exp_correct
  \\ simp []
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

Definition code_rel_def:
  code_rel code1 code2 = (
    !nm sh prog. FLOOKUP code1 nm = SOME (sh, prog) ==>
      ?ctxt. FLOOKUP code2 nm = SOME (sh, compile ctxt prog))
End

Theorem code_rel_imp[local] = hd (RES_CANON code_rel_def)

Theorem compile_correct:
  ∀ p s res s' ctxt.
  evaluate (p, s) = (res, s') ∧
  code_rel s.code code ∧
  s.structs = [] ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ∧
  res ≠ SOME Error
  ⇒
  evaluate (compile ctxt p, (s with code := code)) = (res, (s' with code := code))
Proof
  recInduct (name_ind_cases [] evaluate_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >> fs [compile_def]
  >~ [`While`]
  >- (
    qpat_x_assum `evaluate _ = _` mp_tac
    >> ONCE_REWRITE_TAC [evaluate_def]
    >> strip_tac
    >> gs [AllCaseEqs (), UNCURRY_EQ, eval_upd_code_eq]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gvs [compile_exp_correct_eq, dec_clock_def, empty_locals_def]
  )
  >~ [`Dec`]
  >- (
    gs [evaluate_def, AllCaseEqs (), UNCURRY_EQ, eval_upd_code_eq]
    >> imp_res_tac eval_is_wf_shape_v
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gvs [FEVERY_FUPDATE, fevery_to_drestrict]
    >> simp [compile_exp_correct_eq, compile_shape_eq, is_wf_shape_v_nil]
  )
  >~ [`Call`]
  >- (
    every_case_tac
    >> gvs [evaluate_def, option_case_eq, pair_case_eq, eval_upd_code_eq2]
    >> drule_then (drule_then assume_tac) lookup_code_wf_shape_invariant_step
    >> gs []
    >> gvs [evaluate_def, lookup_code_def, AllCaseEqs (), UNCURRY_EQ,
            compile_exp_correct_eq, eval_upd_code_eq2]
    >> imp_res_tac code_rel_imp
    >> drule_then (irule_at Any) (SIMP_RULE bool_ss [SF ETA_ss] compile_exp_correct_mmap_helper)
    >> simp [compile_exp_correct_eq, FLOOKUP_FMAP_MAP2, empty_locals_def]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [dec_clock_def, set_var_def, set_kvar_def, set_global_def, FEVERY_FUPDATE, fevery_to_drestrict]
    >> every_case_tac >> simp []
  )
  >~ [`DecCall`]
  >- (
    gvs [evaluate_def, option_case_eq, pair_case_eq, eval_upd_code_eq2]
    >> drule_then (drule_then assume_tac) lookup_code_wf_shape_invariant_step
    >> gs []
    >> gvs [evaluate_def, lookup_code_def, AllCaseEqs (), UNCURRY_EQ, compile_exp_correct_eq]
    >> imp_res_tac code_rel_imp
    >> drule_then (irule_at Any) (SIMP_RULE bool_ss [SF ETA_ss] compile_exp_correct_mmap_helper)
    >> simp [compile_exp_correct_eq, FLOOKUP_FMAP_MAP2, empty_locals_def]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [dec_clock_def, set_var_def, FEVERY_FUPDATE, fevery_to_drestrict,
        compile_shape_eq, is_wf_shape_v_nil]
  )
  >> gs [evaluate_def, AllCaseEqs (), UNCURRY_EQ, compile_exp_correct_eq,
        eval_upd_code_eq2, sh_mem_load_def, sh_mem_store_def]
  >> simp [GSYM (Q.ISPEC `compile ctxt` boolTheory.COND_RAND)]
  >> imp_res_tac evaluate_structs_code_inv
  >> imp_res_tac evaluate_is_wf_shape_invariant
  >> fs [set_kvar_def, set_var_def, set_global_def] >> every_case_tac
  >> gvs [empty_locals_def, dec_clock_def]
QED

Theorem compile_decs_correct:
  !s decs ctxt code. evaluate_decls s decs = SOME s' ∧
  code_rel s.code code ∧
  ctxt.structs = [] ∧ s.structs = [] ∧ s.locals = FEMPTY ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
  ?code'.
  evaluate_decls (s with code := code) (FST (compile_decs ctxt decs)) =
    SOME (s' with code := code') ∧
  code_rel s'.code code'
Proof
  recInduct (name_ind_cases [] evaluate_decls_ind)
  >> rw []
  >> fs [compile_decs_def, evaluate_decls_def]
  >- (
    metis_tac []
  )
  >- (
    gs [option_case_eq, bool_case_eq]
    >> simp [UNCURRY]
    >> fs [evaluate_decls_def, compile_exp_correct_eq,
        eval_upd_code_eq |> Q.SPEC `st with locals := l` |> SIMP_RULE (srw_ss ()) []]
    >> imp_res_tac eval_is_wf_shape_v
    >> gs [FEVERY_FEMPTY, compile_shape_eq, is_wf_shape_v_nil]
    >> fs [FEVERY_FUPDATE, fevery_to_drestrict]
  )
  >- (
    simp [UNCURRY]
    >> fs [evaluate_decls_def]
    >> simp [compile_shape_eq, EVERY_MAP, UNCURRY]
    >> fs [EVERY_MEM, compile_shape_eq, UNCURRY, last (RES_CANON MAP_EQ_ID)]
    >> fs [FMAP_MAP2_FUPDATE]
    >> first_x_assum irule
    >> fs [code_rel_def, FLOOKUP_UPDATE]
    >> rw []
    >> metis_tac []
  )
QED

Theorem decs_stcnames_get_names_no_named_structs:
  !st_ctxt decs st_ctxt'. decs_stcnames st_ctxt decs = SOME st_ctxt' ==>
  get_names ctxt decs = ctxt
Proof
  recInduct (name_ind_cases [] decs_stcnames_ind)
  >> rw [decs_stcnames_def, get_names_def]
  >> fs [named_structs_ok_def, option_case_eq]
QED

Theorem decs_stcnames_compile_no_named_structs:
  !st_ctxt decs st_ctxt'. decs_stcnames st_ctxt decs = SOME st_ctxt' ==>
  !st_ctxt2. decs_stcnames st_ctxt (FST (compile_decs st_ctxt2 decs)) = SOME st_ctxt
Proof
  recInduct (name_ind_cases [] decs_stcnames_ind)
  >> rw [decs_stcnames_def, compile_decs_def, ELIM_UNCURRY]
  >> fs [named_structs_ok_def, option_case_eq]
QED

Theorem semantics_eq:
  semantics s start <> Fail ∧
  code_rel s.code code ∧
  ctxt.structs = [] ∧ s.structs = [] ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
  semantics (s with code := code) start = semantics s start
Proof
  rw []
  >> fs [pan_sem_is_wrapper]
  >> drule_then irule semantics_wrapper_eq
  >> csimp []
  >> rw []
  >> TRY (
    rename [`option_CASE res _ _ <> Incomplete`] >>
    Cases_on `res = SOME TimeOut` >> fs []
  )
  >- (
    gvs [PAIR_FST_SND_EQ] >>
    irule isPREFIX_TRANS >>
    irule_at Any evaluate_add_clock_io_events_mono >>
    simp [] >>
    metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    gvs [PAIR_FST_SND_EQ] >>
    irule isPREFIX_TRANS >>
    irule_at Any evaluate_add_clock_io_events_mono >>
    simp [] >>
    metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq >>
    simp [] >>
    (* ugh at renaming a variable so it sorts to the right *)
    disch_then (qspec_then `x` (mp_tac o Q.GEN `x`)) >>
    simp []
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq >>
    simp [] >>
    (* ugh at renaming a variable so it sorts to the right *)
    disch_then (qspec_then `x` (mp_tac o Q.GEN `x`)) >>
    simp []
  )
  >- (
    qexists_tac `0` >>
    drule compile_correct >>
    simp [compile_def, compile_exp_def] >>
    disch_then drule >>
    impl_tac >> strip_tac >> fs []
  )
QED

Theorem evaluate_decls_invariant:
  !s code. evaluate_decls s code = SOME s' /\
  s.locals = FEMPTY /\
  s.structs = [] ==>
  s'.structs = [] /\
  s'.locals = FEMPTY /\
  (FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
    FEVERY (λ(nm,v). is_wf_shape_v_nil v) s'.globals)
Proof
  recInduct evaluate_decls_ind
  >> simp [evaluate_decls_def]
  >> rw []
  >> fs [option_case_eq]
  >> drule eval_is_wf_shape_v
  >> fs []
  >> rw [FEVERY_FEMPTY]
  >> first_x_assum irule
  >> simp [FEVERY_FUPDATE, fevery_to_drestrict]
QED

Theorem compile_top_semantics_decls:
  semantics_decls s start code <> Fail ∧
  s.locals = FEMPTY ∧ s.code = FEMPTY ∧
  s.globals = FEMPTY ⇒
  semantics_decls s start code =
  semantics_decls s start (compile_top code)
Proof
  rw [semantics_decls_def]
  >> TOP_CASE_TAC >> fs []
  >> TOP_CASE_TAC >> fs []
  >> imp_res_tac decs_stcnames_no_named_structs
  >> imp_res_tac decs_stcnames_compile_no_named_structs
  >> imp_res_tac decs_stcnames_get_names_no_named_structs
  >> simp [compile_top_def]
  >> qmatch_goalsub_abbrev_tac `compile_decs nm_ctxt`
  >> drule_then (qspecl_then [`nm_ctxt`, `FEMPTY`] mp_tac) compile_decs_correct
  >> fs [markerTheory.Abbrev_def]
  >> simp [FEVERY_FEMPTY, Q.SPEC `FEMPTY` code_rel_def]
  >> rw []
  >> subgoal `!s. s.code = FEMPTY ==> (s with code := FEMPTY) = s`
  >- ( simp [state_component_equality] )
  >> gs []
  >> irule (GSYM semantics_eq)
  >> simp []
  >> imp_res_tac evaluate_decls_invariant
  >> gs [FEVERY_FEMPTY]
  >> qexists_tac `ARB with structs := []`
  >> simp []
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

