(*
  Properties of CWasm 1.ε AST ⇔ WBF En-/De-coders
*)
Theory      wbf_thms
Ancestors   mlstring leb128 wasmLang wbf_prelim wbf
Libs        preamble wordsLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  =          [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]

(***************************)
(*                         *)
(*     byte-y Theorems     *)
(*                         *)
(***************************)

Theorem enc_numI_nEmp_nTermB:
  ∀x encx. enc_numI x = SOME encx ⇒
  ∃b bs. append encx =  b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_numI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_paraI_nEmp_nTermB:
  ∀x encx. enc_paraI x = SOME encx ⇒
  ∃b bs. append encx =  b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases \\ simp[Once enc_paraI_def, AllCaseEqs()]
QED

Theorem enc_varI_nEmp_nTermB:
  ∀x encx. enc_varI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_varI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_loadI_nEmp_nTermB:
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_loadI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_storeI_nEmp_nTermB:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_storeI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_instr_nEmp_nTermB:
  ∀x encx. enc_instr x = SOME encx ⇒
  ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases
  >> rw[Once enc_instr_def, AllCaseEqs()]
  >> imp_res_tac enc_numI_nEmp_nTermB
  >> imp_res_tac enc_paraI_nEmp_nTermB
  >> imp_res_tac enc_varI_nEmp_nTermB
  >> imp_res_tac enc_loadI_nEmp_nTermB
  >> imp_res_tac enc_storeI_nEmp_nTermB
  >> simp[]
QED

Theorem num_cf_instr_disjoint:
  ∀x encx b bs. enc_numI x = SOME encx ⇒
  append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     simp[enc_numI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem para_cf_instr_disjoint:
  ∀x encx b bs. enc_paraI x = SOME encx ⇒
  append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
  Cases \\ simp[enc_paraI_def, AllCaseEqs()]
QED

Theorem var_cf_instr_disjoint:
  ∀x encx b bs. enc_varI x = SOME encx ⇒
  append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     simp[enc_varI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem load_cf_instr_disjoint:
  ∀x encx b bs. enc_loadI x = SOME encx ⇒
  append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem store_cf_instr_disjoint:
  ∀x encx b bs. enc_storeI x = SOME encx ⇒
  append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
     simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem var_para_disjoint:
  ∀x encx rest. enc_paraI x = SOME encx ⇒
  ∃e. dec_varI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
  Cases
  >> rw[enc_paraI_def, AllCaseEqs(), Once dec_varI_def]
  >> Cases_on ‘dec_u32 rest’
  >> Cases_on ‘q’
  >> simp[]
QED

Theorem var_num_disjoint:
  ∀x encx rest. enc_numI x = SOME encx ⇒
  ∃e. dec_varI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
  rw[]
  \\ imp_res_tac enc_numI_nEmp_nTermB
  \\ gvs[dec_varI_def, AllCaseEqs()]
  \\ Cases_on ‘dec_u32 (bs ++ rest)’
  \\ Cases_on ‘q’
  >> simp[]
    \\ last_x_assum mp_tac
    \\ rw[enc_numI_def, AllCaseEqs()]
    >> gvs[]
QED

Theorem para_num_disjoint:
  ∀x encx rest. enc_numI x = SOME encx ⇒
  ∃e. dec_paraI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> rw[enc_numI_def, AllCaseEqs()]
  >> simp[dec_paraI_def]
QED

Theorem var_load_disjoint:
  ∀x encx rest. enc_loadI x = SOME encx ⇒
  ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  rw[]
  \\ imp_res_tac enc_loadI_nEmp_nTermB
  \\ gvs[dec_varI_def, AllCaseEqs()]
  \\ Cases_on ‘dec_u32 (bs ++ rest)’
  \\ Cases_on ‘q’
  >> simp[]
    \\ last_x_assum mp_tac
    \\ rw[enc_loadI_def, AllCaseEqs()]
    >> gvs[]
QED

Theorem para_load_disjoint:
  ∀x encx rest. enc_loadI x = SOME encx ⇒
  ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_load_disjoint:
  ∀x encx rest. enc_loadI x = SOME encx ⇒
  ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED

Theorem var_store_disjoint:
  ∀x encx rest. enc_storeI x = SOME encx ⇒
  ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  rw[]
  \\ imp_res_tac enc_storeI_nEmp_nTermB
  \\ gvs[dec_varI_def, AllCaseEqs()]
  \\ Cases_on ‘dec_u32 (bs ++ rest)’
  \\ Cases_on ‘q’
  >> simp[]
    \\ last_x_assum mp_tac
    \\ rw[enc_storeI_def, AllCaseEqs()]
    >> gvs[]
QED

Theorem para_store_disjoint:
  ∀x encx rest. enc_storeI x = SOME encx ⇒
  ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_store_disjoint:
  ∀x encx rest. enc_storeI x = SOME encx ⇒
  ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED

Theorem load_store_disjoint:
  ∀x encx rest. enc_storeI x = SOME encx ⇒
  ∃e. dec_loadI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac >> imp_res_tac dec_enc_2u32
  >> gvs[dec_loadI_def]
QED

Theorem enc_valtype_nEmp_n0x40:
  ∀x encx. enc_valtype x = SOME encx ⇒ ∃b bs. append encx = b::bs ∧ b ≠ 0x40w
Proof
  Cases
  >> Cases_on ‘w’
  >> rw[enc_valtype_def, AllCaseEqs(), bvtype_nchotomy]
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

Theorem dec_enc_vector:
  ∀enc dec is encis.
    enc_vector enc is = SOME encis ∧
    (∀x encx rs. enc x = SOME encx ⇒ dec (append encx ++ rs) = (INR x,rs))
    ⇒
    ∀rest. dec_vector dec (encis a++ rest) = (INR is, rest)
Proof
  rpt strip_tac
  \\ last_x_assum mp_tac
  \\ simp[dec_vector_def, enc_vector_def, AllCaseEqs(), GSYM NOT_LESS]
  \\ rpt strip_tac
  \\ gvs ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
  \\ (* tidy up from dec enc vec pf *)
     ntac 2 $ pop_assum kall_tac
  (* dec_enc_list *)
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘rest’
  \\ qid_spec_tac ‘encxs’
  \\ qid_spec_tac ‘is’
  \\ Induct
  >> simp[enc_list_def, Once dec_list_def, CaseEq "sum", CaseEq "prod"]
  \\ rpt strip_tac
  \\ gvs[]
  \\ last_x_assum dxrule
  \\ simp ssa
QED


(*************)
(*   Types   *)
(*************)

Theorem dec_enc_valtype:
  ∀x encx rest. enc_valtype x = SOME encx ⇒
  dec_valtype (encx a++ rest) = (INR x, rest)
Proof
     Cases
  \\ simp[bvtype_nchotomy, enc_valtype_def, dec_valtype_def, AllCaseEqs()]
  \\ Cases_on ‘w’
  >> simp[]
QED

Theorem dec_enc_functype:
  ∀x encx rest. enc_functype x = SOME encx ⇒
  dec_functype (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_functype_def, AllCaseEqs()]
  \\ PairCases_on ‘x’
  \\ gvs[dec_functype_def, AllCaseEqs()]
  \\ rpt $ dxrule dec_enc_vector
  \\ rpt $ disch_then $ qspec_then ‘dec_valtype’ assume_tac
  \\ gvs[dec_enc_valtype]
  \\ simp ssa
QED

Theorem dec_enc_limits:
  ∀x encx rest. enc_limits x = SOME encx ⇒
  dec_limits (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_limits_def, AllCaseEqs()]
  >> simp[dec_limits_def, AllCaseEqs(), dec_enc_u32, dec_enc_2u32]
QED

Theorem dec_enc_globaltype:
  ∀x encx rest. enc_globaltype x = SOME encx ⇒
  dec_globaltype (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_globaltype_def, dec_globaltype_def, AllCaseEqs()]
  >> simp $ ssaa [dec_enc_valtype]
QED



(*******************************************)
(*   Instructions (hierarchically lower)   *)
(*******************************************)

Theorem dec_enc_numI:
  ∀x encx. enc_numI x = SOME encx ⇒
  ∀rest. dec_numI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_numI_def, AllCaseEqs(), bvtype_nchotomy, convert_op_nchotomy]
  >> simp[]
  >>~- ([‘N_const32’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s32])
  >>~- ([‘N_const64’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s64])
  >> rewrite_tac[dec_numI_def]
(*
I clearly don't know how "Once" works...
  >> rewrite_tac[Once dec_numI_def]
*)
  >> gvs[]
QED

Theorem dec_enc_paraI:
  ∀x encx. enc_paraI x = SOME encx ⇒
  ∀rest. dec_paraI (encx a++ rest) = (INR x, rest)
Proof
  Cases
  >> rw[enc_paraI_def, AllCaseEqs()]
  >> simp[dec_paraI_def]
QED

Theorem dec_enc_varI:
  ∀x encx. enc_varI x = SOME encx ⇒
  ∀rest. dec_varI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_varI_def, AllCaseEqs()]
  >> simp[dec_varI_def, AllCaseEqs(), dec_enc_u32]
QED

Theorem dec_enc_loadI:
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∀rest. dec_loadI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_loadI_def, AllCaseEqs(), bvtype_nchotomy]
  >> simp[dec_loadI_def, AllCaseEqs(), dec_enc_2u32]
QED

Theorem dec_enc_storeI:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∀rest. dec_storeI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_storeI_def, AllCaseEqs(), bvtype_nchotomy]
  >> simp[dec_storeI_def, AllCaseEqs(), dec_enc_2u32]
QED



(**********************************************)
(*                                            *)
(*     Top-level Instructions + Controls      *)
(*                                            *)
(**********************************************)

Theorem dec_enc_blocktype:
  ∀x encx. enc_blocktype x = SOME encx ⇒
  ∀rest. dec_blocktype (encx a++ rest) = (INR x, rest)
Proof
  rw[enc_blocktype_def, AllCaseEqs()]
  >> simp[dec_blocktype_def, AllCaseEqs()]
  \\ imp_res_tac enc_valtype_nEmp_n0x40
  \\ imp_res_tac dec_enc_valtype
  \\ gvs[]
QED


Theorem dec_enc_indxs:
  ∀x encx. enc_indxs x = SOME encx ⇒
  ∀rest. dec_indxs (encx a++ rest) = (INR x, rest)
Proof
  rpt strip_tac
  \\ qspec_then ‘enc_u32’ irule dec_enc_vector
  \\ assume_tac dec_enc_u32
  \\ simp[]
QED





Overload exprB[local] = “λe. if e then endB else elseB”

(*  [Note] on "dc" in enc_instr_list:
    (**)
    if we encode an expr (e=T), then we _must_ see an endB(= exprB e) terminator
    byte on decode, regardless of what flag(= ¬e ∨ dc = dc) the decoder gets
    (**)
    when encoding a then-arm (e=F) we expect an elseB(= exprB e) terminator,
    _if_ we're also decoding a then-arm ie, the decoder flag is T(= ¬e ∨ dc).
    Decoding an expression
     *)
Theorem dec_enc_instructions:
  (∀e xs dc encxs rs. enc_instr_list e xs = SOME encxs ⇒ dec_instr_list (¬e ∨ dc) (encxs a++ rs) = ret rs $ (exprB e,xs)) ∧
  (∀  x     encx  rs. enc_instr        x  = SOME encx  ⇒ dec_instr                (encx  a++ rs) = ret rs $          x  )
Proof
  (* askyk - how to: golf? make more ergonomic and/or robust? *)
  (* Note - all the work is really done in the instr (as opposed to instr_list) case *)
  ho_match_mp_tac enc_instr_ind
  \\ simp[]
  \\ rpt strip_tac
  >> pop_assum mp_tac
  >-(
     Cases_on ‘e’ >> simp[enc_instr_def, Once dec_instr_def]
  )
  >-(
     simp[Once enc_instr_def]
     >> rpt strip_tac
     >> imp_res_tac enc_instr_nEmp_nTermB
     >> gvs[]
     >> simp[Once dec_instr_def]
     >> simp ssa
  )
  \\
    Cases_on ‘x’
    >> rw[Once enc_instr_def]
    >> imp_res_tac dec_enc_u32
    >> imp_res_tac dec_enc_indxs
    >> imp_res_tac dec_enc_functype
    >> imp_res_tac dec_enc_blocktype
    >> simp $ ssaa [dec_instr_def]
    (**)
    >>~- ([‘enc_numI’    ],
               imp_res_tac enc_numI_nEmp_nTermB
            \\ imp_res_tac num_cf_instr_disjoint
            \\ imp_res_tac para_num_disjoint
            \\ imp_res_tac var_num_disjoint
            \\ rpt $ pop_assum $ qspec_then ‘rs’ mp_tac
            \\ rpt strip_tac
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum (fn x => rewrite_tac[x])
            \\ simp[dec_enc_numI]
    )
    >>~- ([‘enc_paraI’   ],
               imp_res_tac enc_paraI_nEmp_nTermB
            \\ imp_res_tac para_cf_instr_disjoint
            \\ imp_res_tac var_para_disjoint
            \\ pop_assum $ qspec_then ‘rs’ strip_assume_tac
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum (fn x => rewrite_tac[x])
            \\ simp[dec_enc_paraI]
    )
    >>~- ([‘enc_varI’    ],
               imp_res_tac enc_varI_nEmp_nTermB
            \\ imp_res_tac var_cf_instr_disjoint
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum (fn x => rewrite_tac[x])
            \\ simp[dec_enc_varI]
    )
    >>~- ([‘enc_loadI’   ],
               imp_res_tac enc_loadI_nEmp_nTermB
            \\ imp_res_tac load_cf_instr_disjoint
            \\ imp_res_tac var_load_disjoint
            \\ imp_res_tac para_load_disjoint
            \\ imp_res_tac num_load_disjoint
            \\ rpt $ pop_assum $ qspec_then ‘rs’ mp_tac
            \\ rpt strip_tac
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum $ (fn x => rewrite_tac[x])
            \\ simp[dec_enc_loadI]
    )
    >>~- ([‘enc_storeI’  ],
               imp_res_tac enc_storeI_nEmp_nTermB
            \\ imp_res_tac store_cf_instr_disjoint
            \\ imp_res_tac var_store_disjoint
            \\ imp_res_tac para_store_disjoint
            \\ imp_res_tac num_store_disjoint
            \\ imp_res_tac load_store_disjoint
            \\ rpt $ pop_assum $ qspec_then ‘rs’ mp_tac
            \\ rpt strip_tac
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum $ (fn x => rewrite_tac[x])
            \\ simp[dec_enc_storeI]
    )
QED

Triviality dec_enc_instr_list:
  ∀e is dc encis rest. enc_instr_list e is = SOME encis ⇒
  dec_instr_list (¬e ∨ dc) (encis a++ rest) = (INR (exprB e,is), rest)
Proof
  strip_assume_tac dec_enc_instructions
QED

Triviality dec_enc_instr:
  ∀i enci rest. enc_instr i = SOME enci ⇒
  dec_instr $ enci a++ rest = (INR i , rest)
Proof
  strip_assume_tac dec_enc_instructions
QED

Triviality dec_enc_expr:
  ∀is encis rest dc. enc_expr is = SOME encis ⇒
  dec_instr_list dc (encis a++ rest) = (INR (endB,is), rest)
Proof
  rw[] \\ dxrule dec_enc_instr_list \\ rw[]
QED

Triviality dec_enc_tArm:
  ∀es ences rest. enc_tArm es = SOME ences ⇒
  ∃tmB. dec_tArm (ences a++ rest) = (INR (tmB,es), rest)
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
  ∀g encg rest. enc_global g = SOME encg ⇒
  dec_global $ encg a++ rest = (INR g, rest)
Proof
     rw $ ssaa [enc_global_def, dec_global_def, AllCaseEqs()]
  >-( Cases_on ‘g.gtype’ >> gvs[enc_globaltype_def] )
  \\ imp_res_tac dec_enc_globaltype
  \\ imp_res_tac dec_enc_instr_list
  \\ pop_assum $ qspecl_then [‘rest’, ‘F’] assume_tac
  \\ fs ssa
  \\ simp[global_component_equality]
QED

Theorem enc_u32_nEmp:
  ∀x encx. enc_u32 x = SOME encx ⇒ ¬NULL (append encx)
Proof
     simp[enc_u32_def, enc_unsigned_word_def]
  \\ rw[Once enc_num_def]
QED

Theorem dec_enc_code:
  ∀cd encC rs.
    enc_code cd = SOME encC ⇒
    dec_code $ encC a++ rs = (INR cd, rs)
Proof
  PairCases
  \\ rw[enc_code_def, AllCaseEqs(), dec_code_def, prepend_sz_def]
  >-( imp_res_tac enc_u32_nEmp \\ simp[] )
  \\ simp ssa
  \\ imp_res_tac dec_enc_u32
  \\ gvs[]
  \\ assume_tac dec_enc_valtype
  \\ imp_res_tac dec_enc_vector
  \\ simp ssa
  \\ dxrule dec_enc_instr_list
  \\ simp[]
QED

Theorem dec_enc_byte:
  ∀x encx rest. enc_byte x = SOME encx ⇒
    dec_byte $ encx a++ rest = (INR x, rest)
Proof
  simp[enc_byte_def, dec_byte_def]
QED

Theorem dec_enc_data:
  ∀dt encD rs.
    enc_data dt = SOME encD ⇒
    dec_data $ encD a++ rs = (INR dt, rs)
Proof
     rw[enc_data_def, dec_data_def, AllCaseEqs()]
  >> imp_res_tac enc_u32_nEmp
  >> simp ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
  \\ dxrule_at Any dec_enc_instr_list
  \\ rw ssa
  \\ ntac 3 $ pop_assum kall_tac
  \\ assume_tac dec_enc_byte
  \\ imp_res_tac dec_enc_vector
  \\ simp[data_component_equality]
QED


Theorem dec_enc_mls:
  ∀x encx rest. enc_mls x = SOME encx ⇒
  dec_mls $ encx a++ rest = (INR x, rest)
Proof
  rw[dec_mls_def, enc_mls_def]
  \\ assume_tac dec_enc_byte
  \\ imp_res_tac dec_enc_vector
  \\ simp[string2bytes_def, bytes2string_def, MAP_MAP_o, CHR_w2n_n2w_ORD]
QED

Theorem dec_enc_idx_alpha:
  ∀enc dec x encx rest.
  enc_idx_alpha enc x = SOME encx ∧
  (∀y ency rs. enc y = SOME ency ⇒ dec (append ency ++ rs) = (INR y,rs))
  ⇒
  dec_idx_alpha dec $ encx a++ rest = (INR x, rest)
Proof
  rpt strip_tac
  \\ last_x_assum mp_tac
  \\ PairCases_on ‘x’
  \\ simp[dec_idx_alpha_def, enc_idx_alpha_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ gvs ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
QED

Theorem dec_enc_ass:
  ∀x encx rest. enc_ass x = SOME encx ⇒
  dec_ass $ encx a++ rest = (INR x, rest)
Proof
  rw[dec_ass_def, enc_ass_def]
  \\ assume_tac dec_enc_mls
  \\ imp_res_tac dec_enc_idx_alpha
  \\ simp[]
QED

Theorem dec_enc_map:
  ∀x encx rest. enc_map x = SOME encx ⇒
  dec_map $ encx a++ rest = (INR x, rest)
Proof
  rw[dec_map_def, enc_map_def]
  \\ assume_tac dec_enc_ass
  \\ imp_res_tac dec_enc_vector
  \\ simp[]
QED

(*
m ``implode``
mlstringTheory.explode_thm
mlstringTheory.implode_explode
miscTheory.CHR_w2n_n2w_ORD
miscTheory.CHR_w2n_n2w_ORD_simp
miscTheory.n2w_ORD_CHR_w2n
miscTheory.n2w_ORD_CHR_w2n_simp
stringTheory.CHR_ORD
stringTheory.ORD_CHR
rich_listTheory.MAP_o
rich_listTheory.MAP_MAP_o

  ∀enc dec is encis.
    enc_vector enc is = SOME encis ∧
    (∀x encx rs. enc x = SOME encx ⇒ dec (append encx ++ rs) = (INR x,rs))
    ⇒
    ∀rest. dec_vector dec (encis a++ rest) = (INR is, rest)

  rpt strip_tac
  \\ last_x_assum mp_tac
  \\ simp[dec_vector_def, enc_vector_def, AllCaseEqs(), GSYM NOT_LESS]
  \\ rpt strip_tac
  \\ gvs ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
  \\ (* tidy up from dec enc vec pf *)
     ntac 2 $ pop_assum kall_tac
  (* dec_enc_list *)
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘rest’
  \\ qid_spec_tac ‘encxs’
  \\ qid_spec_tac ‘is’
  \\ Induct
  >> simp[enc_list_def, Once dec_list_def, CaseEq "sum", CaseEq "prod"]
  \\ rpt strip_tac
  \\ gvs[]
  \\ last_x_assum dxrule
  \\ simp ssa

*)




Theorem dec_enc_section:
  ∀xs enc dec lb encxs rest. enc_section lb enc xs = SOME encxs ∧
  (∀x encx rs. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs)) ⇒
  dec_section lb dec $ encxs a++ rest = (INR xs, rest)
Proof
     rw[enc_section_def, prepend_sz_def]
  \\ simp[dec_section_def]
  \\ imp_res_tac dec_enc_u32
  \\ simp ssa
  \\ imp_res_tac dec_enc_vector
  \\ simp[]
QED


Theorem enc_vector_nEmp:
  ∀enc xs encxs. enc_vector enc xs = SOME encxs ⇒ ∃b bs. append encxs = b::bs
Proof
     Cases_on ‘xs’
  >- simp[enc_vector_def, enc_list_def, enc_u32_def, enc_unsigned_word_def, Once enc_num_def]
  \\ simp[enc_vector_def]
  \\ rpt strip_tac
  \\ imp_res_tac enc_u32_nEmp
  \\ Cases_on ‘append encln’
  \\ gvs[]
QED

Theorem enc_section_nEmp:
  ∀lb enc x encx. enc_section lb enc x = SOME encx ⇒
  ∃bs. append encx = lb::bs
Proof
     rw[enc_section_def, prepend_sz_def]
  \\ simp[]
QED




Theorem dec_enc_names:
  ∀no eno rest.
  enc_names_section no = SOME eno ⇒
  dec_names_section $ append eno = (INR no, [])
Proof

  Cases
  >> rw[Once enc_names_section_def, Once dec_names_section_def, AllCaseEqs()]
    >> gvs[prepend_sz_def, dec_names_section_def, magic_str_def]
    >> gvs[string2bytes_def, bytes2string_def, blank_def]
    (**)
    >> TRY (qpat_x_assum `SOME _ = enc_u32 _` $ mp_tac o GSYM \\ strip_tac)
    (**)
    >> imp_res_tac dec_enc_u32
    >> simp ssa
    (* mname *)
    >> TRY (imp_res_tac dec_enc_mls \\ pop_assum $ qspec_then `[]` assume_tac)
    >> fs[dec_section_def]
    >> pop_assum kall_tac
>>
cheat
(*
    (* fnames *)
    >> assume_tac dec_enc_ass
    >> imp_res_tac dec_enc_section
    >> TRY (qpat_x_assum `enc_section 1w _ _ = SOME _` mp_tac)
    >> rw[enc_section_def]
    >> simp[dec_section_def]
    >> imp_res_tac dec_enc_vector

    >> imp_res_tac dec_enc_u32
    >> assume_tac dec_enc_idx_alpha
    >> imp_res_tac dec_enc_vector

    >> gvs[enc_section_def, dec_section_def, AllCaseEqs(), prepend_sz_def]
    >> imp_res_tac dec_enc_u32
    >> simp[]
    (**)
    >> assume_tac dec_enc_map
    >> imp_res_tac dec_enc_idx_alpha
    >> imp_res_tac dec_enc_vector
    >> pop_assum $ qspec_then `[]` assume_tac
    >> fs[]

    >> dxrule_at Any dec_enc_idx_alpha
    >> strip_tac

    >> simp[names_component_equality]
cheat

    >> `append encxs = encxs a++ []` by simp[]
    >> asm_rewrite_tac[]
    >> simp[]
    >> assume_tac dec_enc_idx_alpha

    >> TRY (qpat_x_assum `enc_section _ _ _ = SOME _` mp_tac)
    >> rw[enc_section_def]
    >> imp_res_tac dec_enc_u32
    >> imp_res_tac dec_enc_vector
    >> assume_tac dec_enc_idx_alpha
    >> imp_res_tac dec_enc_vector

    >> assume_tac dec_enc_map
    >> dxrule_at Any dec_enc_idx_alpha
    >> strip_tac
    >> imp_res_tac dec_enc_vector

    >> simp[]
    >>

    >> gvs[dec_section_def, AllCaseEqs()]

    >> imp_res_tac enc_section_nEmp
    >> simp[dec_section_def, AllCaseEqs()]

    >> asm_rewrite_tac[]
    (* lnames *)
    (**)
    >> simp[names_component_equality]

    asm_rewrite_tac[]

    (* 1 *)
    >> simp[names_component_equality]

    (* 2 *)
    >- cheat

    (* 3 *)
    >- cheat

    (* 4 *)
    >- cheat

    (* 5 *)
    >> ntac 2 $ pop_assum kall_tac
    >> imp_res_tac dec_enc_mls
    >> simp ssa

    (* 6 *)

    (* 7 *)

    (* 8 *)

    >> cheat
*)
QED
(*

Theorem dec_enc_names:
  ∀no eno rest.
  enc_names_section no = SOME eno ⇒
  dec_names_section $ append eno = (INR no, [])
Proof

  Cases
  >> rw[Once enc_names_section_def, Once dec_names_section_def, AllCaseEqs()]
    >> gvs[prepend_sz_def, dec_names_section_def, magic_str_def]
    >> gvs[string2bytes_def, bytes2string_def, blank_def]
    (**)
    >> imp_res_tac dec_enc_u32
    >> simp ssa

    >> pop_assum (fn x => mp_tac $ GSYM x)
    >> strip_tac
    >> simp[names_component_equality]

    >> imp_res_tac dec_enc_u32
    >> simp ssa
    >> ntac 2 $ pop_assum kall_tac
    >> assume_tac dec_enc_map
    >> imp_res_tac dec_enc_idx_alpha
    >> pop_assum mp_tac
    >> pop_assum kall_tac
    >> strip_tac
    >> imp_res_tac dec_enc_section

    >> rw[]
    >> rw[magic_str_def, string2bytes_def, AllCaseEqs()]
    (**)
ntac 2 $ pop_assum kall_tac
    (**)
    >> assume_tac dec_enc_map
    >> imp_res_tac dec_enc_idx_alpha
    >> pop_assum mp_tac
    >> pop_assum kall_tac
    >> strip_tac
    >> imp_res_tac dec_enc_section
    >> qspec_then ‘dec_idx_alpha dec_map’ imp_res_tac
    >>

    >> dxrule dec_enc_idx_alpha
    >> dxrule_all dec_enc_idx_alpha
    >> simp[]
    >> gvs[]

    >> assume_tac dec_enc_idx_alpha
    >> assume_tac dec_enc_map
    >> imp_res_tac dec_enc_section
    >> rw[]

    >> assume_tac

    >> rw[AllCaseEqs()]
    >> rw[magic_str_def, string2bytes_def, AllCaseEqs()]
    >> rw[magic_str_def, string2bytes_def, AllCaseEqs()]


cheat

QED




Theorem dec_enc_module:
  ∀mod nms encM rs.
    enc_module mod nms = SOME encM ⇒
    dec_module $ encM ++ rs = (INR mod, rs)
Proof
(*
  Cases >> simp[enc_module_def]
  >> ‘∃a b. split_funcs l0 = (a,b)’ by simp[]
 Cases_on ‘split_funcs l0’
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
*)

(*



Theorem dec_enc_vector:
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

*)
