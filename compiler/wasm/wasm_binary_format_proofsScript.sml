(*
  CWasm 1.ε AST ⇔ Wasm binary format En- & De- coder theorems
*)

Theory      wasm_binary_format_proofs
Ancestors   leb128 ancillaryOps wasmLang wasm_binary_format
Libs        preamble wordsLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  =          [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]

(***************************)
(*                         *)
(*     byte-y Theorems     *)
(*                         *)
(***************************)

Theorem enc_numI_nEmp_nTermB:
  ∀i. ∃b bs. enc_numI i = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  gen_tac
  \\ ‘∃val. enc_numI i = val’ by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_numI_def, AllCaseEqs()]
QED

Theorem enc_paraI_nEmp_nTermB:
  ∀i. ∃b bs. enc_paraI i = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases \\ simp[Once enc_paraI_def, AllCaseEqs()]
QED

Theorem enc_varI_nEmp_nTermB:
  ∀i. ∃b bs. enc_varI i = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases \\ simp[Once enc_varI_def, AllCaseEqs()]
QED

Theorem enc_loadI_nEmp_nTermB:
  ∀i. ∃b bs. enc_loadI i = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  gen_tac
  \\ ‘∃val. enc_loadI i = val’ by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_loadI_def, AllCaseEqs()]
QED

Theorem enc_storeI_nEmp_nTermB:
  ∀i. ∃b bs. enc_storeI i = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  gen_tac
  \\ ‘∃val. enc_storeI i = val’ by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_storeI_def, AllCaseEqs()]
QED

Theorem enc_instr_nEmp_nTermB:
  ∀i enci. enc_instr i = SOME enci ⇒
  ∃b bs. enci = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases
  >> rw[Once enc_instr_def, AllCaseEqs()]
  >> mp_tac enc_numI_nEmp_nTermB
  >> mp_tac enc_paraI_nEmp_nTermB
  >> mp_tac enc_varI_nEmp_nTermB
  >> mp_tac enc_loadI_nEmp_nTermB
  >> mp_tac enc_storeI_nEmp_nTermB
  >> simp[]
QED

Theorem num_cf_instr_disjoint:
  ∀i b bs. enc_numI i = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     rw[enc_numI_def, AllCaseEqs()]
  \\ simp[]
QED

Theorem para_cf_instr_disjoint:
  ∀i b bs. enc_paraI i = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     rw[enc_paraI_def, AllCaseEqs()]
  \\ simp[]
QED

Theorem var_cf_instr_disjoint:
  ∀i b bs. enc_varI i = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     rw[enc_varI_def, AllCaseEqs()]
  \\ simp[]
QED

Theorem load_cf_instr_disjoint:
  ∀i b bs. enc_loadI i = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     rw[enc_loadI_def, AllCaseEqs()]
  \\ simp[]
QED

Theorem store_cf_instr_disjoint:
  ∀i b bs. enc_storeI i = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     rw[enc_storeI_def, AllCaseEqs()]
  \\ simp[]
QED

Theorem var_para_disjoint:
  ∀p rest. ∃ e. dec_varI (enc_paraI p ++ rest) = (INL e, enc_paraI p ++ rest)
Proof
  Cases >> simp[enc_paraI_def, dec_varI_def]
QED

Theorem var_num_disjoint:
  ∀n rest. ∃ e. dec_varI (enc_numI n ++ rest) = (INL e, enc_numI n ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_numI_def]
  >> every_case_tac
  >> simp[dec_varI_def]
QED

Theorem para_num_disjoint:
  ∀n rest. ∃ e. dec_paraI (enc_numI n ++ rest) = (INL e, enc_numI n ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_numI_def]
  >> every_case_tac
  >> simp[dec_paraI_def]
QED

Theorem var_load_disjoint:
  ∀l rest. ∃ e. dec_varI (enc_loadI l ++ rest) = (INL e, enc_loadI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def]
  >> every_case_tac
  >> simp[dec_varI_def]
QED

Theorem para_load_disjoint:
  ∀l rest. ∃ e. dec_paraI (enc_loadI l ++ rest) = (INL e, enc_loadI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def]
  >> every_case_tac
  >> simp[dec_paraI_def]
QED

Theorem num_load_disjoint:
  ∀l rest. ∃ e. dec_numI (enc_loadI l ++ rest) = (INL e, enc_loadI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def]
  >> every_case_tac
  >> simp[dec_numI_def]
QED

Theorem var_store_disjoint:
  ∀l rest. ∃ e. dec_varI (enc_storeI l ++ rest) = (INL e, enc_storeI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def]
  >> every_case_tac
  >> simp[dec_varI_def]
QED

Theorem para_store_disjoint:
  ∀l rest. ∃ e. dec_paraI (enc_storeI l ++ rest) = (INL e, enc_storeI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def]
  >> every_case_tac
  >> simp[dec_paraI_def]
QED

Theorem num_store_disjoint:
  ∀l rest. ∃ e. dec_numI (enc_storeI l ++ rest) = (INL e, enc_storeI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def]
  >> every_case_tac
  >> simp[dec_numI_def]
QED

Theorem load_store_disjoint:
  ∀l rest. ∃ e. dec_loadI (enc_storeI l ++ rest) = (INL e, enc_storeI l ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def]
  >> every_case_tac
  >> simp[dec_loadI_def]
QED




(***********************************)
(*                                 *)
(*     Decode--Encode Theorems     *)
(*                                 *)
(***********************************)

(* MM's neat trick to check if we're making progress *)
fun print_dot_tac h = (print "."; all_tac h);

(*****************************************)
(*   Vectors (not vector instructions)   *)
(*****************************************)

Theorem dec_enc_vector[simp]:
  ∀is enc dec encis.
    enc_vector enc is = SOME encis ∧
    (∀x rs. dec (enc x ++ rs) = (INR x,rs))
    ⇒
    ∀rest. dec_vector dec (encis ++ rest) = (INR is, rest)
Proof
  rpt strip_tac
  \\ last_x_assum mp_tac
  \\ rw[dec_vector_def, enc_vector_def, AllCaseEqs()]
  \\ gvs $ ssaa [GSYM NOT_LESS]
  \\ qid_spec_tac ‘rest’
  \\ qid_spec_tac ‘is’
  \\ Induct
  >> simp $ ssaa [enc_list_def, Once dec_list_def, CaseEq "sum", CaseEq "prod"]
QED

Theorem dec_enc_vector_opt[simp]:
  ∀dec enc is encis.
    enc_vector_opt enc is = SOME encis ∧
    (∀x encx rs. enc x = SOME encx ⇒ dec (encx ++ rs) = (INR x,rs))
    ⇒
    ∀rest. dec_vector dec (encis ++ rest) = (INR is, rest)
Proof
  rpt strip_tac
  \\ last_x_assum mp_tac
  \\ rw[dec_vector_def, enc_vector_opt_def, AllCaseEqs()]
  \\ gvs $ ssaa [GSYM NOT_LESS]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘rest’
  \\ qid_spec_tac ‘encxs’
  \\ qid_spec_tac ‘is’
  \\ Induct
  >> simp[enc_list_opt_def, Once dec_list_def, CaseEq "sum", CaseEq "prod"]
  \\ rpt strip_tac
  \\ gvs[]
  \\ last_x_assum dxrule
  \\ simp ssa
QED





(*************)
(*   Types   *)
(*************)

Theorem dec_enc_valtype[simp]:
  ∀t rest. dec_valtype (enc_valtype t ++ rest) = (INR t, rest)
Proof
     rpt gen_tac
  \\ ‘∃ val. enc_valtype t = val’ by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ simp[enc_valtype_def, AllCaseEqs(), bvtype_nchotomy]
  \\ rpt strip_tac
    >> gvs[dec_valtype_def]
QED

Theorem dec_enc_functype:
  ∀sg encsg rest.
    enc_functype sg = SOME encsg ⇒
    dec_functype (encsg ++ rest) = (INR sg, rest)
Proof
     rw[AllCaseEqs(), enc_functype_def]
  \\ PairCases_on ‘sg’
  \\ gvs[dec_functype_def, AllCaseEqs()]
  \\ dxrule dec_enc_vector
  \\ disch_then $ qspec_then ‘dec_valtype’ assume_tac
  \\ dxrule dec_enc_vector
  \\ disch_then $ qspec_then ‘dec_valtype’ assume_tac
  \\ gvs[dec_enc_valtype]
  \\ simp ssa
QED

Theorem dec_enc_limits[simp]:
  ∀ lim rest. dec_limits (enc_limits lim ++ rest) = (INR lim, rest)
Proof
     rpt gen_tac
  \\ ‘∃ val. enc_limits lim = val’ by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[enc_limits_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
    >> gvs[dec_limits_def]
QED

Theorem dec_enc_globaltype[simp]:
  ∀ x rest. dec_globaltype (enc_globaltype x ++ rest) = (INR x, rest)
Proof
     rpt gen_tac
  \\ ‘∃ val. enc_globaltype x = val’ by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[enc_globaltype_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
    >> gvs $ ssaa [dec_globaltype_def, dec_enc_valtype]
QED



(*******************************************)
(*   Instructions (hierarchically lower)   *)
(*******************************************)

Theorem dec_enc_numI[simp]:
  ∀ i rest. dec_numI (enc_numI i ++ rest) = (INR i, rest)
Proof
     rpt gen_tac
  \\ ‘∃res. enc_numI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_numI_def]
  \\ simp[AllCaseEqs(), bvtype_nchotomy, convert_op_nchotomy]
  \\ rpt strip_tac
  (* single byte encoding cases *)
  >> asm_rewrite_tac[APPEND, dec_numI_def]
  >> simp[AllCaseEqs()]
    (* cases requiring further encoding (of their "immediates") *)
    >> (
      pop_assum sym_sub_tac
      >- simp[dec_numI_def, AllCaseEqs()]
    )
QED

Theorem dec_enc_paraI[simp]:
  ∀ i rest. dec_paraI (enc_paraI i ++ rest) = (INR i, rest)
Proof
  rw[enc_paraI_def] \\ every_case_tac \\ rw[dec_paraI_def]
QED

Theorem dec_enc_varI[simp]:
  ∀ i rest. dec_varI (enc_varI i ++ rest) = (INR i, rest)
Proof
  rw[enc_varI_def] \\ every_case_tac \\ rw[dec_varI_def, dec_enc_unsigned_word]
QED

Theorem dec_enc_loadI[simp]:
  ∀ i rest. dec_loadI (enc_loadI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_loadI i = res’ by simp [] >> asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ simp[enc_loadI_def, AllCaseEqs(), bvtype_nchotomy]
  \\ rpt strip_tac
    >> ( pop_assum sym_sub_tac >- simp[dec_loadI_def, AllCaseEqs()] )
QED

Theorem dec_enc_storeI[simp]:
  ∀ i rest. dec_storeI (enc_storeI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_storeI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ simp[enc_storeI_def, AllCaseEqs(), bvtype_nchotomy]
  \\ rpt strip_tac
    >> gvs[dec_storeI_def]
QED



(**********************************************)
(*                                            *)
(*     Top-level Instructions + Controls      *)
(*                                            *)
(**********************************************)

Theorem dec_enc_blocktype[simp]:
  ∀b rest. dec_blocktype (enc_blocktype b ++ rest) = (INR b, rest)
Proof
  rpt strip_tac
  \\ ‘∃ val. enc_blocktype b = val’ by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ gvs[enc_blocktype_def, AllCaseEqs()]
  \\ rpt strip_tac
  >> gvs[dec_blocktype_def]
  \\ Cases_on ‘vt’ \\ Cases_on ‘w’
  >> simp[enc_valtype_def, AllCaseEqs()]
QED


Theorem dec_enc_lift_u32[simp]:
  ∀b rest. lift_dec_u32 (enc_u32 b ++ rest) = (INR b, rest)
Proof
  rpt gen_tac
  \\ simp[lift_dec_u32_def]
QED

Theorem dec_enc_indxs:
  ∀bs encbs rest. enc_indxs bs = SOME encbs ⇒
  dec_indxs (encbs ++ rest) = (INR bs, rest)
Proof
  rpt strip_tac
  \\ dxrule_at Any dec_enc_vector
  \\ simp[dec_enc_lift_u32]
QED





Overload exprB[local] = “λe. if e then endB else elseB”

(* [Note] on "dc": Here the statements says that if we encode an expr (e=T), then we _must_ see an endB (¬e ∨ dc=F)
   But if we're encoding a then-arm (e=F), then we (dc:=)don't care whether the decoder gets a T or F flag *)
Theorem dec_enc_instructions:
  (∀e is dc encis rs. enc_instr_list e is = SOME encis ⇒ dec_instr_list (¬e ∨ dc) (encis ++ rs) = (INR (exprB e,is), rs)) ∧
  (∀  i     enci  rs. enc_instr        i  = SOME enci  ⇒ dec_instr                (enci  ++ rs) = (INR          i  , rs))
Proof
  (* askyk - how to: golf? make more ergonomic and/or robust? *)
  (* Note - all the work is really done in the instr (as opposed to instr_list) case *)
  ho_match_mp_tac enc_instr_ind
  \\ simp[]
  \\ rpt strip_tac
  >> pop_assum mp_tac
  >-( Cases_on ‘e’ >> simp[enc_instr_def, Once dec_instr_def] )
  >-(
    simp[Once enc_instr_def]
    >> rpt strip_tac
    >> imp_res_tac enc_instr_nEmp_nTermB
    >> gvs[]
    >> simp[Once dec_instr_def]
    >> simp ssa
    )
  \\
    Cases_on ‘i’
    >> rw[Once enc_instr_def]
    >> rewrite_tac[APPEND, dec_instr_def]
    >> simp ssa
    >>~- ([‘dec_indxs’   ], imp_res_tac dec_enc_indxs    \\ simp[] )
    >>~- ([‘dec_functype’], imp_res_tac dec_enc_functype \\ simp[] )
    >>~- ([‘enc_varI’    ],
                            qspec_then ‘v’ strip_assume_tac enc_varI_nEmp_nTermB
                            \\ imp_res_tac var_cf_instr_disjoint
                            \\ gvs[Once dec_instr_def]
                            \\ ‘b::(bs ++ rs) =  (b::bs) ++ rs’ by simp[]
                            \\ asm_rewrite_tac[]
                            \\ last_x_assum $ (fn x => rewrite_tac[GSYM x])
                            \\ simp[]
    )
    >>~- ([‘enc_paraI’   ],
                            qspec_then ‘p’ strip_assume_tac enc_paraI_nEmp_nTermB
                            \\ imp_res_tac para_cf_instr_disjoint
                            \\ gvs[Once dec_instr_def]
                            \\ ‘b::(bs ++ rs) =  (b::bs) ++ rs’ by simp[]
                            \\ pop_assum $ (fn x => rewrite_tac[x])
                            \\ last_assum $ (fn x => rewrite_tac[GSYM x])
                            \\ qspecl_then [‘p’, ‘rs’] strip_assume_tac var_para_disjoint
                            \\ simp[]
    )
    >>~- ([‘enc_numI’    ],
                            qspec_then ‘n’ strip_assume_tac enc_numI_nEmp_nTermB
                            \\ imp_res_tac num_cf_instr_disjoint
                            \\ gvs[Once dec_instr_def]
                            \\ ‘b::(bs ++ rs) =  (b::bs) ++ rs’ by simp[]
                            \\ pop_assum $ (fn x => rewrite_tac[x])
                            \\ last_x_assum $ (fn x => rewrite_tac[GSYM x])
                            \\ qspecl_then [‘n’, ‘rs’] strip_assume_tac var_num_disjoint
                            \\ qspecl_then [‘n’, ‘rs’] strip_assume_tac para_num_disjoint
                            \\ simp[]
    )
    >>~- ([‘enc_loadI’   ],
                            qspec_then ‘l’ strip_assume_tac enc_loadI_nEmp_nTermB
                            \\ imp_res_tac load_cf_instr_disjoint
                            \\ simp[Once dec_instr_def]
                            \\ ‘b::(bs ++ rs) =  (b::bs) ++ rs’ by simp[]
                            \\ pop_assum $ (fn x => rewrite_tac[x])
                            \\ last_x_assum $ (fn x => rewrite_tac[GSYM x])
                            \\ qspecl_then [‘l’, ‘rs’] strip_assume_tac var_load_disjoint
                            \\ qspecl_then [‘l’, ‘rs’] strip_assume_tac para_load_disjoint
                            \\ qspecl_then [‘l’, ‘rs’] strip_assume_tac num_load_disjoint
                            \\ simp[]
    )
    >>~- ([‘enc_storeI’  ],
                            qspec_then ‘s’ strip_assume_tac enc_storeI_nEmp_nTermB
                            \\ imp_res_tac store_cf_instr_disjoint
                            \\ simp[Once dec_instr_def]
                            \\ ‘b::(bs ++ rs) =  (b::bs) ++ rs’ by simp[]
                            \\ pop_assum $ (fn x => rewrite_tac[x])
                            \\ last_x_assum $ (fn x => rewrite_tac[GSYM x])
                            \\ qspecl_then [‘s’, ‘rs’] strip_assume_tac var_store_disjoint
                            \\ qspecl_then [‘s’, ‘rs’] strip_assume_tac para_store_disjoint
                            \\ qspecl_then [‘s’, ‘rs’] strip_assume_tac num_store_disjoint
                            \\ qspecl_then [‘s’, ‘rs’] strip_assume_tac load_store_disjoint
                            \\ simp[]
    )
QED

Triviality dec_enc_instr_list:
  ∀e is dc encis rs. enc_instr_list e is = SOME encis ⇒
  dec_instr_list (¬e ∨ dc) (encis ++ rs) = (INR (exprB e,is), rs)
Proof
  strip_assume_tac dec_enc_instructions
QED

Triviality dec_enc_instr:
  ∀i enci rs. enc_instr i = SOME enci ⇒
  dec_instr $ enci  ++ rs = (INR i , rs)
Proof
  strip_assume_tac dec_enc_instructions
QED

Triviality dec_enc_expr:
  ∀is encis rs dc. enc_expr is = SOME encis ⇒
  dec_instr_list dc (encis ++ rs) = (INR (endB,is), rs)
Proof
  rw[] \\ dxrule dec_enc_instr_list \\ rw[]
QED

Triviality dec_enc_tArm:
  ∀es ences rs. enc_tArm es = SOME ences ⇒
  ∃tmB. dec_tArm (ences ++ rs) = (INR (tmB,es), rs)
Proof
     rpt strip_tac
  \\ strip_assume_tac dec_enc_instructions
  \\ pop_assum kall_tac
  \\ pop_assum dxrule
  \\ simp[]
QED





(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)

Theorem dec_enc_global[simp]:
  ∀g encg rs. enc_global g = SOME encg ⇒
  dec_global $ encg ++ rs = (INR g, rs)
Proof
     rpt gen_tac
  \\ simp $ ssaa [enc_global_def, dec_global_def, AllCaseEqs()]
  \\ rpt strip_tac
  >- ( Cases_on ‘g.gtype’ >> gvs[enc_globaltype_def] )
  \\ gvs $ ssaa []
  \\ imp_res_tac dec_enc_instr_list
  \\ pop_assum $ qspec_then ‘rs’ assume_tac
  \\ fs[]
  \\ simp[global_component_equality]
QED

Theorem enc_u32_nEmp:
  ∀w. ¬ (NULL $ enc_u32 w)
Proof
  rw[enc_unsigned_word_def, Once enc_num_def]
QED

Theorem dec_enc_code:
  ∀cd encC rs.
    enc_code cd = SOME encC ⇒
    dec_code $ encC ++ rs = (INR cd, rs)
Proof
  PairCases
  \\ rw[enc_code_def, AllCaseEqs(), dec_code_def]
  >-( mp_tac enc_u32_nEmp \\ simp[] )
  \\ rewrite_tac $ ssaa [dec_enc_u32]
  \\ gvs[]
  \\ assume_tac dec_enc_valtype
  \\ dxrule_all dec_enc_vector \\ strip_tac
  \\ gvs ssa
  \\ dxrule dec_enc_instr_list
  \\ simp[]
QED

Theorem dec_enc_byte:
  ∀b rs. dec_byte $ (λb. [b]) b ++ rs = (INR b, rs)
Proof
  gen_tac \\ Cases >> rw[dec_byte_def]
QED

Theorem dec_enc_data:
  ∀dt encD rs.
    enc_data dt = SOME encD ⇒
    dec_data $ encD ++ rs = (INR dt, rs)
Proof
     simp[enc_data_def, dec_data_def, AllCaseEqs()]
  \\ rpt strip_tac
  >> gvs[enc_u32_nEmp]
  \\ rewrite_tac $ ssaa [dec_enc_u32]
  \\ gvs[]
  \\ dxrule_at Any dec_enc_instr_list \\ rw ssa
  \\ pop_assum kall_tac
  \\ dxrule_at Any dec_enc_vector
  \\ assume_tac dec_enc_byte
  \\ disch_then dxrule
  \\ simp[data_component_equality]
QED


Theorem dec_enc_section:
  ∀xs enc dec lb encxs rest. enc_section lb enc xs = SOME encxs ∧
  (∀x rs. dec (enc x ++ rs) = (INR x, rs)) ⇒
  dec_section lb dec $ encxs ++ rest = (INR xs, rest)
Proof
     rw[enc_section_def]
  \\ simp $ ssaa [dec_section_def]
  \\ dxrule_at Any dec_enc_vector
  \\ disch_then dxrule
  \\ simp[]
QED


Theorem dec_enc_section_opt:
  ∀xs enc dec lb encxs rest. enc_section_opt lb enc xs = SOME encxs ∧
  (∀x encx rs. enc x = SOME encx ⇒ dec (encx ++ rs) = (INR x, rs)) ⇒
  dec_section lb dec $ encxs ++ rest = (INR xs, rest)
Proof
     rw[enc_section_opt_def]
  \\ simp $ ssaa [dec_section_def]
  \\ dxrule_at Any dec_enc_vector_opt
  \\ disch_then dxrule
  \\ simp[]
QED







Theorem dec_enc_module:
  ∀mod nms encM rs.
    enc_module mod nms = SOME encM ⇒
    dec_module $ encM ++ rs = (INR mod, rs)
Proof
(*
  Cases >> simp[enc_module_def]
  >> ‘∃a b. split_funcs l0 = (a,b)’ by simp[]
 Cases_on `split_funcs l0`
  >> rpt strip_tac >> gvs[]
*)
  Cases >> Induct_on ‘l0’
  >> simp[enc_module_def, split_funcs_def]
  >> rpt strip_tac >> gvs[]
  >-(
       ‘enc_section_opt 10w enc_code [] = SOME code'’   by fs[]
    >> ‘enc_section      3w enc_u32  [] = SOME fTIdxs'’ by fs[]
    >> rpt $ dxrule_at Any dec_enc_section
    >> rpt $ dxrule_at Any dec_enc_section_opt
    >> rpt $ pop_assum kall_tac

    \\ assume_tac dec_enc_functype
    \\ assume_tac dec_enc_global
    \\ assume_tac dec_enc_data
    \\ assume_tac dec_enc_code
    \\ assume_tac dec_enc_lift_u32
    \\ assume_tac dec_enc_limits
    \\ rpt (disch_then dxrule \\ strip_tac)

    \\ simp $ ssaa [dec_module_def, AllCaseEqs(), mod_leader_def]
    \\ simp [module_component_equality, zip_funcs_def]
    \\ cheat
    )
  \\ cheat
QED


(***************)
(*             *)
(*     WIP     *)
(*             *)
(***************)




(*




Theorem shorten_failure_shortens:
  ∀bs xs _x rs. shorten bs xs = (INL _x,rs) ⇒ lst_se rs bs
Proof
  Cases_on `xs` \\ Cases_on `q`
  >> rw[shorten_def]
  >> simp[]
QED


Triviality shorten_success_inversion:
  ∀bs fbs _x rs. shorten bs fbs = (INR _x,rs) ⇒ ∃ _x frs. fbs = (INR _x,frs)
Proof
  gvs [oneline shorten_def, AllCaseEqs()] \\ rw [] \\ fs []
QED


Triviality shorten_failure_inversion:
  ∀bs fbs _x rs. shorten bs fbs = (INL _x,rs) ⇒ ∃ _x frs. fbs = (INL _x,frs)
Proof
  gvs [oneline shorten_def, AllCaseEqs()] \\ rw [] \\ fs []
QED




Theorem dec_instructions_failure_shortens_maybe:
  (∀e bs x rs. dec_instr_list e bs = (INL x,rs) ⇒ lst_se rs bs) ∧
  (∀  bs x rs. dec_instr        bs = (INL x,rs) ⇒ lst_se rs bs)
Proof
  rpt strip_tac >> imp_res_tac dec_instructions_error >> simp[]
QED



*)



(*





Triviality dec_instr_shortens:
  (∀xs x rs. dec_instr xs = (INR x,rs) ⇒ lst_st rs xs)
Proof
  rewrite_tac[dec_instructions_shorten]
QED



Theorem dec_expr_shortens:
  (∀xs x rs. dec_expr xs = (INR x,rs) ⇒ lst_st rs xs)
Proof
  mp_tac dec_instructions_shorten
  \\ strip_tac
  \\ pop_assum kall_tac
  \\ rpt strip_tac
  \\ Cases_on ‘dec_instr_list F xs’
  \\ Cases_on ‘q’ >> gvs[]
  \\ Cases_on ‘y’ >> gvs[]
  \\ first_x_assum dxrule
  \\ gvs[]
QED

Theorem dec_tArm_shortens:
  (∀xs x rs. dec_tArm xs = (INR x,rs) ⇒ lst_st rs xs)
Proof
  rewrite_tac[dec_instructions_shorten]
QED

Theorem dec_instr_short_enough:
  ∀bs. force_shtr dec_instr bs = dec_instr bs
Proof
  rw[dec_instructions_short_enough]
QED

Theorem dec_instructions_short_enough:
  ∀e bs. force_shtr (dec_instr_list e) bs = dec_instr_list e bs
Proof
  rw[dec_instructions_short_enough]
QED









(* for study
MATCH_MP
dec_vector_shortens_lt
(dec_byte_shortens  |> INST_TYPE [alpha |-> ``:byte``])
  \\ (qspec_then `dec_byte` assume_tac (dec_vector_shortens_lt |> INST_TYPE [alpha |-> ``:byte``]))
*)

Definition emp_module_def:
  emp_module : module =
  <| types   := []
   ; funcs   := []
   ; mems    := []
   ; globals := []
   ; datas   := []
   |>
End





Theorem dec_il_end_or_else_B:
  ∀bs e tmB x rs. dec_instr_list e bs = (INR (tmB,x),rs) ⇒ (tmB = endB ∨ tmB = elseB)
Proof
  Induct
  >> simp[Once dec_instr_def, AllCaseEqs()]
QED




 *)













