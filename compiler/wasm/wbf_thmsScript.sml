(*
  Properties of CWasm 1.ε AST ⇔ WBF En-/De-coders
*)
Theory      wbf_thms
Ancestors   mlstring leb128 wasmLang wbf_prelim wbf
Libs        preamble wordsLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  =          [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]

val ifSolves = fn x => TRY (x \\ NO_TAC)
val ifHypx   = fn pat => (fn tac => TRY $ qpat_x_assum pat tac)
val ifHyp    = fn pat => (fn tac => TRY $ qpat_assum   pat tac)
(***************************)
(*                         *)
(*     byte-y Theorems     *)
(*                         *)
(***************************)

(**********************)
(*   non-empty thms   *)
(**********************)

Theorem enc_numI_nEmp_nTermB:
  ∀x encx.
    enc_numI x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
     rw[Once enc_numI_def, AllCaseEqs()]
  >> simp[]
QED

Theorem enc_paraI_nEmp_nTermB:
  ∀x encx.
    enc_paraI x = SOME encx ⇒
    ∃b bs.append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  Cases \\ simp[Once enc_paraI_def, AllCaseEqs()]
QED

Theorem enc_varI_nEmp_nTermB:
  ∀x encx.
    enc_varI x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_varI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_loadI_nEmp_nTermB:
  ∀x encx.
    enc_loadI x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_loadI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_storeI_nEmp_nTermB:
  ∀x encx.
    enc_storeI x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
  rw[Once enc_storeI_def, AllCaseEqs()] >> simp[]
QED

Theorem enc_instr_nEmp_nTermB:
  ∀x encx.
    enc_instr x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ endB ∧ b ≠ elseB
Proof
     Cases
  >> rw[Once enc_instr_def, AllCaseEqs()]
  >> simp[] (* will this speed up the proof? *)
  >> imp_res_tac enc_numI_nEmp_nTermB
  >> imp_res_tac enc_paraI_nEmp_nTermB
  >> imp_res_tac enc_varI_nEmp_nTermB
  >> imp_res_tac enc_loadI_nEmp_nTermB
  >> imp_res_tac enc_storeI_nEmp_nTermB
  >> simp[]
QED



Theorem enc_valtype_nEmp_n0x40:
  ∀x encx.
    enc_valtype x = SOME encx ⇒
    ∃b bs. append encx = b::bs ∧ b ≠ 0x40w
Proof
     namedCases ["bvtype width"]
  \\ Cases_on ‘width’
  >> rw[enc_valtype_def, AllCaseEqs(), bvtype_nchotomy]
QED

Theorem enc_u32_nNUL:
  ∀x encx.
    enc_u32 x = SOME encx ⇒ ¬NULL (append encx)
Proof
     simp[enc_u32_def, enc_unsigned_word_def]
  \\ rw[Once enc_num_def]
QED

Theorem enc_vector_nEmp:
  ∀enc xs encxs.
    enc_vector enc xs = SOME encxs ⇒
    ∃b bs. append encxs = b::bs
Proof
     Cases_on ‘xs’
  >- simp[enc_vector_def, enc_list_def, enc_u32_def, enc_unsigned_word_def, Once enc_num_def]
  \\ simp[enc_vector_def]
  \\ rpt strip_tac
  \\ imp_res_tac enc_u32_nNUL
  \\ Cases_on ‘append encln’
  \\ gvs[]
QED

Theorem enc_section_nEmp__nNUL:
  ∀lb enc x xs exxs.
    enc_section lb enc (x::xs) = SOME exxs ⇒ ¬NULL (append exxs)
Proof
     rw[enc_section_def]
  \\ simp[]
QED

Theorem enc_section_nNUL__nNUL:
  ∀lb enc xs exs.
    ¬NULL xs ∧ enc_section lb enc xs = SOME exs ⇒
    ¬NULL (append exs)
Proof
     rw[enc_section_def]
  \\ simp[]
QED





(*********************)
(*   disjoint thms   *)
(*********************)

Theorem num_cf_disjoint:
  ∀x encx b bs.
    enc_numI x = SOME encx ∧ append encx = b::bs
    ⇒
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

Theorem para_cf_disjoint:
  ∀x encx b bs.
    enc_paraI x = SOME encx ∧ append encx = b::bs
    ⇒
    b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
    b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
    b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
    b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
    b ≠ rciOC
Proof
  Cases \\ simp[enc_paraI_def, AllCaseEqs()]
QED

Theorem var_cf_disjoint:
  ∀x encx b bs.
    enc_varI x = SOME encx ∧ append encx = b::bs
    ⇒
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

Theorem load_cf_disjoint:
  ∀x encx b bs.
    enc_loadI x = SOME encx ∧ append encx = b::bs
    ⇒
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

Theorem store_cf_disjoint:
  ∀x encx b bs.
    enc_storeI x = SOME encx ∧ append encx = b::bs
    ⇒
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



Theorem var_store_disjoint:
  ∀x encx rest.
    enc_storeI x = SOME encx ⇒
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
  ∀x encx rest.
    enc_storeI x = SOME encx ⇒
    ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_store_disjoint:
  ∀x encx rest.
    enc_storeI x = SOME encx ⇒
    ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED

Theorem load_store_disjoint:
  ∀x encx rest.
    enc_storeI x = SOME encx ⇒
    ∃e. dec_loadI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac >> imp_res_tac dec_enc_2u32
  >> gvs[dec_loadI_def]
QED



Theorem var_load_disjoint:
  ∀x encx rest.
    enc_loadI x = SOME encx ⇒
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
  ∀x encx rest.
    enc_loadI x = SOME encx ⇒
    ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_load_disjoint:
  ∀x encx rest.
    enc_loadI x = SOME encx ⇒
    ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED



Theorem var_num_disjoint:
  ∀x encx rest.
    enc_numI x = SOME encx ⇒
    ∃e. dec_varI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
     rw[]
  \\ imp_res_tac enc_numI_nEmp_nTermB
  \\ gvs[dec_varI_def, AllCaseEqs()]
  \\ namedCases_on ‘dec_u32 (bs ++ rest)’ ["either rs"]
  \\ namedCases_on ‘either’ ["e", "x"]
  >> simp[]
    \\ last_x_assum mp_tac
    \\ rw[enc_numI_def, AllCaseEqs()]
    >> gvs[]
QED

Theorem para_num_disjoint:
  ∀x encx rest.
    enc_numI x = SOME encx ⇒
    ∃e. dec_paraI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
     Cases
  >> gen_tac
    >> rw[enc_numI_def, AllCaseEqs()]
    >> simp[dec_paraI_def]
QED



Theorem var_para_disjoint:
  ∀x encx rest.
    enc_paraI x = SOME encx ⇒
    ∃e. dec_varI (encx a++ rest) = (INL e, append encx ++ rest)
Proof
     Cases
  >> rw[enc_paraI_def, AllCaseEqs(), Once dec_varI_def]
    >> namedCases_on ‘dec_u32 rest’ ["either rs"]
    >> namedCases_on ‘either’ ["e", "x"]
    >> simp[]
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
    (∀rs x encx. enc x = SOME encx ⇒ dec (append encx ++ rs) = (INR x,rs))
    ⇒
    ∀rest. dec_vector dec (encis a++ rest) = (INR is, rest)
Proof
     rpt strip_tac
  \\ last_x_assum mp_tac
  \\ rw[enc_vector_def, dec_vector_def, AllCaseEqs()]
  \\ gvs ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
  \\ ntac 2 $ pop_assum kall_tac (* tidy up from dec enc vec pf *)
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
  ∀rest x encx.
    enc_valtype x = SOME encx ⇒
    dec_valtype (encx a++ rest) = (INR x, rest)
Proof
     namedCases_on ‘x’ ["bvtype width"]
  \\ simp[bvtype_nchotomy, enc_valtype_def, dec_valtype_def, AllCaseEqs()]
  \\ Cases_on ‘width’
  >> simp[]
QED

Theorem dec_enc_functype:
  ∀rest x encx.
    enc_functype x = SOME encx ⇒
    dec_functype (encx a++ rest) = (INR x, rest)
Proof
     namedCases_on ‘x’ ["args retvs"]
  \\ rw[enc_functype_def, AllCaseEqs()]
  \\ simp[dec_functype_def, AllCaseEqs()]
  \\ rpt $ dxrule dec_enc_vector
  \\ rpt $ disch_then $ qspec_then ‘dec_valtype’ assume_tac
  \\ gvs[dec_enc_valtype]
  \\ simp ssa
QED

Theorem dec_enc_limits:
  ∀rest x encx.
    enc_limits x = SOME encx ⇒
    dec_limits (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_limits_def, AllCaseEqs()]
  >> simp[dec_limits_def, AllCaseEqs(), dec_enc_u32, dec_enc_2u32]
QED

Theorem dec_enc_globaltype:
  ∀rest x encx.
    enc_globaltype x = SOME encx ⇒
    dec_globaltype (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_globaltype_def, dec_globaltype_def, AllCaseEqs()]
  >> simp $ ssaa [dec_enc_valtype]
QED



(******************************************************)
(*   Instructions (hierarchically lower components)   *)
(******************************************************)

Theorem dec_enc_numI:
  ∀rest x encx.
    enc_numI x = SOME encx ⇒
    dec_numI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_numI_def, AllCaseEqs(), bvtype_nchotomy, convert_op_nchotomy]
  >> simp[]
  >>~- ([‘N_const32’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s32])
  >>~- ([‘N_const64’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s64])
  >> rewrite_tac[dec_numI_def]
  >> gvs[]
QED

Theorem dec_enc_paraI:
  ∀rest x encx.
    enc_paraI x = SOME encx ⇒
    dec_paraI (encx a++ rest) = (INR x, rest)
Proof
     Cases_on ‘x’
  >> rw[enc_paraI_def, AllCaseEqs()]
  >> simp[dec_paraI_def]
QED

Theorem dec_enc_varI:
  ∀rest x encx.
    enc_varI x = SOME encx ⇒
    dec_varI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_varI_def, AllCaseEqs()]
  >> simp[dec_varI_def, AllCaseEqs(), dec_enc_u32]
QED

Theorem dec_enc_loadI:
  ∀rest x encx.
    enc_loadI x = SOME encx ⇒
    dec_loadI (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_loadI_def, AllCaseEqs(), bvtype_nchotomy]
  >> simp[dec_loadI_def, AllCaseEqs(), dec_enc_2u32]
QED

Theorem dec_enc_storeI:
  ∀rest x encx.
    enc_storeI x = SOME encx ⇒
    dec_storeI (encx a++ rest) = (INR x, rest)
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
  ∀rest x encx.
    enc_blocktype x = SOME encx ⇒
    dec_blocktype (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_blocktype_def, AllCaseEqs()]
  >> simp[dec_blocktype_def, AllCaseEqs()]
  \\ imp_res_tac enc_valtype_nEmp_n0x40
  \\ imp_res_tac dec_enc_valtype
  \\ gvs[]
QED

Theorem dec_enc_indxs:
  ∀rest x encx.
  enc_indxs x = SOME encx ⇒
  dec_indxs (encx a++ rest) = (INR x, rest)
Proof
     rpt strip_tac
  \\ qspec_then ‘enc_u32’ irule dec_enc_vector
  \\ assume_tac dec_enc_u32
  \\ simp[]
QED





Overload exprB[local] = “λe. if e then endB else elseB”

(*  [Note] on "dc" in enc_instr_list:
    (**)
    if we encode an expr (e=T), then we _must_ see an endB(= exprB T) terminator
    byte on decode, regardless of what flag(= ¬T ∨ dc = dc) the decoder gets
    (**)
    when encoding a then-arm (e=F) we expect an elseB(= exprB F) terminator,
    _if_ we're also decoding a then-arm ie, the decoder flag is T(= ¬F ∨ dc).     *)
Theorem dec_enc_instructions:
  (∀e xs dc encxs rs. enc_instr_list e xs = SOME encxs ⇒ dec_instr_list (¬e ∨ dc) (encxs a++ rs) = ret rs $ (exprB e,xs)) ∧
  (∀  x     encx  rs. enc_instr        x  = SOME encx  ⇒ dec_instr                (encx  a++ rs) = ret rs $          x  )
Proof (* Note - all the work is really done in the instr (VS instr_list) case *)
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
  \\ Cases_on ‘x’
  >> rw[Once enc_instr_def]
  >> imp_res_tac dec_enc_u32
  >> imp_res_tac dec_enc_indxs
  >> imp_res_tac dec_enc_functype
  >> imp_res_tac dec_enc_blocktype
  >> simp $ ssaa [dec_instr_def]
  (**)
  >>~- ([‘enc_numI’  ],
         imp_res_tac enc_numI_nEmp_nTermB
      \\ imp_res_tac num_cf_disjoint
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
  >>~- ([‘enc_paraI’ ],
         imp_res_tac enc_paraI_nEmp_nTermB
      \\ imp_res_tac para_cf_disjoint
      \\ imp_res_tac var_para_disjoint
      \\ pop_assum $ qspec_then ‘rs’ strip_assume_tac
      \\ gvs[Once dec_instr_def, AllCaseEqs()]
      (**)
      \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
      \\ pop_assum (fn x => rewrite_tac[x])
      \\ simp[dec_enc_paraI]
  )
  >>~- ([‘enc_varI’  ],
         imp_res_tac enc_varI_nEmp_nTermB
      \\ imp_res_tac var_cf_disjoint
      \\ gvs[Once dec_instr_def, AllCaseEqs()]
      (**)
      \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
      \\ pop_assum (fn x => rewrite_tac[x])
      \\ simp[dec_enc_varI]
  )
  >>~- ([‘enc_loadI’ ],
         imp_res_tac enc_loadI_nEmp_nTermB
      \\ imp_res_tac load_cf_disjoint
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
  >>~- ([‘enc_storeI’],
         imp_res_tac enc_storeI_nEmp_nTermB
      \\ imp_res_tac store_cf_disjoint
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
  \\ Cases_on ‘l0’ (* if case *)
  >> gvs[dec_instr_def]
  >> simp $ ssaa [dec_instr_def]
  >> imp_res_tac dec_enc_blocktype
  >> simp ssa
QED

Triviality dec_enc_instr_list:
  ∀rest e is dc encis.
    enc_instr_list e is = SOME encis ⇒
    dec_instr_list (¬e ∨ dc) (encis a++ rest) = ret rest (exprB e,is)
Proof
     rpt gen_tac
  \\ rw[dec_enc_instructions]
QED

Triviality dec_enc_instr:
  ∀rest i enci.
    enc_instr i = SOME enci ⇒
    dec_instr $ enci a++ rest = ret rest i
Proof
     rpt gen_tac
  \\ rw[dec_enc_instructions]
QED

Triviality dec_enc_expr:
  ∀is encis rest dc.
    enc_expr is = SOME encis ⇒
    dec_instr_list dc (encis a++ rest) = ret rest (endB,is)
Proof
     rpt strip_tac
  \\ dxrule dec_enc_instr_list
  \\ simp[]
QED

Triviality dec_enc_tArm:
  ∀es ences rest.
    enc_tArm es = SOME ences ⇒
    ∃tmB. dec_tArm (ences a++ rest) = ret rest (tmB,es)
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

Triviality s2b_o_b2s__I[simp]:
  string2bytes ∘ bytes2string = I
Proof
  rw[string2bytes_def, bytes2string_def, GSYM MAP_o, n2w_ORD_CHR_w2n, MAP_ID_I]
QED

Triviality s2b_b2s__I[simp]:
  ∀x. string2bytes $ bytes2string x = x
Proof
  rw[string2bytes_def, bytes2string_def, MAP_MAP_o, n2w_ORD_CHR_w2n, MAP_ID_I]
QED

Triviality b2s_o_s2b__I[simp]:
  bytes2string ∘ string2bytes = I
Proof
  rw[string2bytes_def, bytes2string_def, GSYM MAP_o, CHR_w2n_n2w_ORD, MAP_ID_I]
QED

Triviality b2s_s2b__I[simp]:
  ∀x. bytes2string $ string2bytes x = x
Proof
  rw[string2bytes_def, bytes2string_def, MAP_MAP_o, CHR_w2n_n2w_ORD, MAP_ID_I]
QED

Triviality imp_b2s_null:
  ∀x. bytes2string x = "" ⇒ x = []
Proof
  simp[implode_def, bytes2string_def]
QED

Triviality imp_b2s_null[simp]:
  bytes2string [] = ""
Proof
  simp[implode_def, bytes2string_def]
QED

Triviality implode_emp[simp]:
  implode "" = «»
Proof
  simp[implode_def]
QED

Triviality id_OK_emp[simp]:
  id_OK ""
Proof
  simp[id_OK_def]
QED

Triviality s2b_explode_NUL:
  ∀x. NULL (string2bytes (explode x)) ⇔ x = «»
Proof
     gen_tac
  \\ simp[string2bytes_def, NULL_EQ_NIL]
  \\ iff_tac
  >> rw[]
  \\ qspec_then ‘x’ mp_tac implode_explode
  \\ pop_assum (fn x => rewrite_tac[x])
  \\ disch_then $ assume_tac o GSYM
  \\ simp[]
QED

Triviality blank_names_values:
  blank_names = names «» [] []
Proof
  simp[blank_names_def, names_component_equality]
QED

Triviality b2s__STRING[simp]:
  ∀s' ss. implode (bytes2string (n2w (ORD s')::MAP (n2w ∘ ORD) ss)) = implode $ STRING s' ss
Proof
  rw[bytes2string_def, MAP_MAP_o, CHR_w2n_n2w_ORD]
QED





Theorem enc_section_emp[simp]:
  ∀lb enc. enc_section lb enc [] = SOME $ List []
Proof
  rw[enc_section_def]
QED

Theorem enc_section_emp__NUL_conv:
  ∀lb enc xs encxs.
    enc_section lb enc xs = SOME encxs ∧ NULL (append encxs) ⇒ xs = []
Proof
     rw[enc_section_def, NULL_EQ_NIL, prepend_B_sz_def]
  \\ gvs[append_def]
QED

Triviality enc_names_section_blank[simp]:
  enc_names_section blank_names = SOME $ List []
Proof
     rw[enc_names_section_def, blank_names_def, enc_section_def]
  >- simp[prepend_B_sz_def, name_bytes_def, string2bytes_def, enc_u32_def]
  >- fs[string2bytes_def]
QED

Triviality enc_names_section_blank__NUL_conv:
  ∀x ex. enc_names_section x = SOME ex ∧ NULL (append ex) ⇒ x = blank_names
Proof
(* askyk askmm *)
     namedCases_on ‘x’ ["mname fnames lnames"]
  \\ rw[enc_names_section_def, blank_names_values]
  >-(
       Cases_on ‘NULL $ string2bytes $ explode mname’
    >- imp_res_tac s2b_explode_NUL
    \\ imp_res_tac enc_section_nNUL__nNUL
    \\ ntac 2 $ pop_assum kall_tac
    \\ gvs[]
  )
  >-(
       Cases_on ‘NULL fnames’
    >- gvs[NULL_EQ_NIL]
    \\ imp_res_tac enc_section_nNUL__nNUL
    \\ ntac 2 $ pop_assum kall_tac
    \\ gvs[]
  )
  \\ Cases_on ‘NULL lnames’
  >- gvs[NULL_EQ_NIL]
  \\ imp_res_tac enc_section_nNUL__nNUL
  \\ ntac 2 $ pop_assum kall_tac
  \\ gvs[]
QED

Triviality names_not_blank:
  ∀x. x ≠ blank_names ⇒ x.mname ≠ «» ∨ ¬NULL x.fnames ∨ ¬NULL x.lnames
Proof
     namedCases ["mname fnames lnames"]
  \\ namedCases_on ‘mname’ ["x"]
  \\ rewrite_tac[GSYM implode_def]
  \\ namedCases_on ‘x’ ["", "s ss"]
  >> namedCases_on ‘fnames’ ["", "f fs"]
  >> namedCases_on ‘lnames’ ["", "l ls"]
  >> simp[blank_names_values]
QED

Triviality names_not_blank':
  ∀x. x ≠ blank_names ⇒ ¬NULL (string2bytes $ explode x.mname) ∨ ¬NULL x.fnames ∨ ¬NULL x.lnames
Proof
     rpt strip_tac
  \\ imp_res_tac names_not_blank
  >> simp[]
  \\ namedCases_on ‘x.mname’ ["s"]
  \\ namedCases_on ‘s’ ["", "s ss"]
  >> gvs[string2bytes_def]
QED



Triviality enc_names_section_not_blank__nNUL:
  ∀x encx.
    x ≠ blank_names ∧ enc_names_section x = SOME encx ⇒
    ¬NULL (append encx)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_names_section_blank__NUL_conv
QED

Triviality enc_names_section_not_blank__lbn0:
  ∀x encx.
    x ≠ blank_names ∧ enc_names_section x = SOME encx ⇒
    ∃dc. append encx = 0w::dc
Proof
     rpt strip_tac
  \\ drule enc_names_section_blank__NUL_conv
  \\ rw[]
  \\ gvs[oneline enc_names_section_def, NULL_EQ_NIL]
  >> Cases_on ‘append ss0’
  >> Cases_on ‘append ss1’
  >> Cases_on ‘append ss2’
  >> gvs[]
QED





Triviality dec_names_section_empty[simp]:
  ∀lb enc. dec_names_section [] = ret [] [blank_names]
Proof
  rw[Once dec_names_section_def]
QED

Triviality dec_section_empty[simp]:
  ∀lb dec. dec_section lb dec [] = ret [] []
Proof
  rw[Once dec_section_def]
QED









Theorem dec_enc_global:
  ∀rest g encg.
    enc_global g = SOME encg ⇒
    dec_global $ encg a++ rest = (INR g, rest)
Proof
     rw $ ssaa [enc_global_def, dec_global_def, AllCaseEqs()]
  >-(
       Cases_on ‘g.gtype’
    >> gvs[enc_globaltype_def]
  )
  \\ imp_res_tac dec_enc_globaltype
  \\ imp_res_tac dec_enc_instr_list
  \\ pop_assum $ qspecl_then [‘rest’, ‘F’] assume_tac
  \\ fs ssa
  \\ simp[global_component_equality]
QED



Theorem dec_enc_code:
  ∀rest cd encC.
    enc_code cd = SOME encC ⇒
    dec_code $ encC a++ rest = (INR cd, rest)
Proof
     namedCases_on `cd` ["argTs exp"]
  \\ rw[enc_code_def, AllCaseEqs(), dec_code_def, prepend_B_sz_def]
  >-(
       imp_res_tac enc_u32_nNUL
    \\ simp[]
  )
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
  ∀rest x encx.
    enc_byte x = SOME encx ⇒
    dec_byte $ encx a++ rest = (INR x, rest)
Proof
  simp[enc_byte_def, dec_byte_def]
QED



Theorem dec_enc_data:
  ∀rest dt encD.
    enc_data dt = SOME encD ⇒
    dec_data $ encD a++ rest = (INR dt, rest)
Proof
     rw[enc_data_def, dec_data_def, AllCaseEqs()]
  >> imp_res_tac enc_u32_nNUL
  >> simp ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
  \\ dxrule_at Any dec_enc_instr_list
  \\ rw ssa
  \\ assume_tac dec_enc_byte
  \\ imp_res_tac dec_enc_vector
  \\ simp[data_component_equality]
QED



Theorem dec_enc_mls:
  ∀rest x encx.
    enc_mls x = SOME encx ⇒
    dec_mls $ encx a++ rest = (INR x, rest)
Proof
     rw[dec_mls_def, enc_mls_def]
  \\ assume_tac dec_enc_byte
  \\ imp_res_tac dec_enc_vector
  \\ simp[string2bytes_def, bytes2string_def, MAP_MAP_o, CHR_w2n_n2w_ORD]
QED

Theorem dec_enc_idx_alpha:
  ∀rest enc dec x encx.
    enc_idx_alpha enc x = SOME encx ∧
    (∀rs y ency. enc y = SOME ency ⇒ dec (append ency ++ rs) = (INR y,rs))
    ⇒
    dec_idx_alpha dec $ encx a++ rest = (INR x, rest)
Proof
     rpt strip_tac
  \\ last_x_assum mp_tac
  \\ namedCases_on ‘x’ ["idx alpha"]
  \\ simp[dec_idx_alpha_def, enc_idx_alpha_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ gvs ssa
  \\ imp_res_tac dec_enc_u32
  \\ simp[]
QED

Theorem dec_enc_ass:
  ∀rest x encx.
    enc_ass x = SOME encx ⇒
    dec_ass $ encx a++ rest = (INR x, rest)
Proof
     rw[dec_ass_def, enc_ass_def]
  \\ assume_tac dec_enc_mls
  \\ imp_res_tac dec_enc_idx_alpha
  \\ simp[]
QED

Theorem dec_enc_map:
  ∀rest x encx.
    enc_map x = SOME encx ⇒
    dec_map $ encx a++ rest = (INR x, rest)
Proof
     rw[dec_map_def, enc_map_def]
  \\ assume_tac dec_enc_ass
  \\ imp_res_tac dec_enc_vector
  \\ simp[]
QED





Theorem dec_enc_section_NE: (* non empty *)
  ∀rest lb xs enc dec encxs.
    ¬NULL xs ∧ enc_section lb enc xs = SOME encxs ∧
    (∀rs x encx. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
    ⇒
    dec_section lb dec $ encxs a++ rest= (INR xs, rest)
Proof
     rw[enc_section_def, prepend_B_sz_def]
  \\ simp[dec_section_def]
  \\ imp_res_tac dec_enc_u32
  \\ simp ssa
  \\ imp_res_tac dec_enc_vector
  \\ simp[]
QED

Theorem dec_enc_section_NR: (* no rest *)
  ∀lb xs enc dec encxs.
    enc_section lb enc xs = SOME encxs ∧
    (∀rs x encx. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
    ⇒
    dec_section lb dec $ append encxs = (INR xs, [])
Proof
     rpt strip_tac
  \\ Cases_on ‘NULL xs’
  >- gvs[enc_section_def, NULL_EQ_NIL]
  \\ qspec_then ‘[]’ imp_res_tac dec_enc_section_NE
  \\ gvs[]
QED

Theorem dec_enc_section:
  ∀rest lb xs enc dec encxs.
    enc_section lb enc xs = SOME encxs ∧
    (∀rs x encx. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
    ⇒
    dec_section lb dec $ encxs a++ rest = (INR xs, rest) ∨ xs = []
Proof
     Cases_on ‘xs’
  >> rw[enc_section_def, prepend_B_sz_def]
  \\ imp_res_tac dec_enc_u32
  \\ imp_res_tac dec_enc_vector
  \\ simp $ ssaa [dec_section_def]
QED


Theorem dec_section_pt:
  ∀lb b dec bs. lb ≠ b ⇒ dec_section lb dec (b::bs) = ret (b::bs) []
Proof
  simp[Once dec_section_def]
QED

Theorem enc_dec_section_pt:
  ∀b2 dec b1 enc x xs exxs.
    b1 ≠ b2 ∧
    enc_section b1 enc (x::xs) = SOME exxs ⇒
    dec_section b2 dec $ append exxs = ret (append exxs) []
Proof
     rw[enc_section_def]
  \\ rw[dec_section_pt]
QED

Theorem enc_dec_section_ptr:
  ∀b2 dec b1 enc rest x xs exxs.
    b1 ≠ b2 ∧
    enc_section b1 enc (x::xs) = SOME exxs ⇒
    dec_section b2 dec $ exxs a++ rest = ret (exxs a++ rest) []
Proof
     rw[enc_section_def]
  \\ rw[dec_section_pt]
QED



Theorem dec_enc_names_pt:
  ∀rest b. b ≠ 0w ⇒ dec_names_section $ (b::rest) = ret (b::rest) []
Proof
  rw[Once dec_names_section_def]
QED



Theorem dec_enc_module_blank:
  ∀mod emn. enc_module blank_mod = SOME emn ⇒ NULL $ append emn
Proof
  rw[blank_mod_def, enc_mod_and_names_def, split_funcs_def]
QED



Theorem split_zip_funcs:
  ∀fs fs_types fs_lbods.
    split_funcs fs = (fs_types, fs_lbods) ⇒
    zip_funcs fs_types fs_lbods = fs
Proof
     Induct
  >> rw[split_funcs_def, zip_funcs_def]
  \\ namedCases_on ‘split_funcs fs’ ["fns_types fns_lbods"]
  \\ gvs[zip_funcs_def, func_component_equality]
QED


(*****************************************************************************)
(*   Some widgets to make the names/module proof more modular and abstract   *)
(*****************************************************************************)

(* dec-enc sub-section (specialized) thms. used in the names_section proof *)
Triviality dess0r:
  ∀rest x xs ex.
    enc_section 0w enc_byte (x::xs) = SOME ex ⇒
    dec_section 0w dec_byte (ex a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp__nNUL
  \\ assume_tac dec_enc_byte
  \\ imp_res_tac dec_enc_section
  \\ pop_assum $ qspec_then ‘rest’ mp_tac
  \\ simp[]
QED

Triviality dess0:
  ∀x xs ex.
    enc_section 0w enc_byte (x::xs) = SOME ex ⇒
    dec_section 0w dec_byte (append ex) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac dess0r \\ simp[]
QED


Triviality dess1r:
  ∀rest x xs ex.
    enc_section 1w enc_ass (x::xs) = SOME ex ⇒
    dec_section 1w dec_ass (ex a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp__nNUL
  \\ assume_tac dec_enc_ass
  \\ imp_res_tac dec_enc_section
  \\ pop_assum $ qspec_then ‘rest’ mp_tac
  \\ simp[]
QED

Triviality dess1:
  ∀x xs ex.
    enc_section 1w enc_ass (x::xs) = SOME ex ⇒
    dec_section 1w dec_ass (append ex) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac dess1r \\ simp[]
QED


Triviality dess2:
  ∀x xs ex.
    enc_section 2w (enc_idx_alpha enc_map) (x::xs) = SOME ex ⇒
    dec_section 2w (dec_idx_alpha dec_map) (append ex) = ret [] (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp__nNUL
  \\ assume_tac dec_enc_map
  \\ dxrule_at Any dec_enc_idx_alpha
  \\ strip_tac
  \\ imp_res_tac dec_enc_section_NR
QED





(* dec-enc section thms used in the module proof *)
Triviality des1r:
  ∀rest x xs ex.
    enc_section 1w enc_functype (x::xs) = SOME ex ⇒
    dec_section 1w dec_functype (ex a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp__nNUL
  \\ assume_tac dec_enc_functype
  \\ imp_res_tac dec_enc_section
  \\ pop_assum $ qspec_then ‘rest’ mp_tac
  \\ simp[]
QED

Triviality des1:
  ∀x xs es.
  enc_section 1w enc_functype (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des1r \\ simp[]
QED


Triviality des3r:
  ∀rest x xs es.
    enc_section 3w enc_u32 (x::xs) = SOME es ⇒
    dec_section 3w dec_u32 (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp__nNUL
  \\ assume_tac dec_enc_u32
  \\ imp_res_tac dec_enc_section
  \\ pop_assum $ qspec_then ‘rest’ mp_tac
  \\ simp[]
QED

Triviality des3:
  ∀rest x xs es.
    enc_section 3w enc_u32 (x::xs) = SOME es ⇒
    dec_section 3w dec_u32 (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des3r \\ simp[]
QED

Triviality des5r:
  ∀rest x xs es.
    enc_section 5w enc_limits (x::xs) = SOME es ⇒
    dec_section 5w dec_limits (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp__nNUL
  >> assume_tac dec_enc_limits
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality des5:
  ∀rest x xs es.
    enc_section 5w enc_limits (x::xs) = SOME es ⇒
    dec_section 5w dec_limits (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des5r \\ simp[]
QED

Triviality des6r:
  ∀rest x xs es.
    enc_section 6w enc_global (x::xs) = SOME es ⇒
    dec_section 6w dec_global (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp__nNUL
  >> assume_tac dec_enc_global
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality des6:
  ∀rest x xs es.
    enc_section 6w enc_global (x::xs) = SOME es ⇒
    dec_section 6w dec_global (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des6r \\ simp[]
QED


Triviality des10r:
  ∀rest x xs es.
    enc_section 10w enc_code (x::xs) = SOME es ⇒
    dec_section 10w dec_code (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp__nNUL
  >> assume_tac dec_enc_code
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality des10:
  ∀rest x xs es.
    enc_section 10w enc_code (x::xs) = SOME es ⇒
    dec_section 10w dec_code (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des10r \\ simp[]
QED

Triviality des11r:
  ∀rest x xs es.
    enc_section 11w enc_data (x::xs) = SOME es ⇒
    dec_section 11w dec_data (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp__nNUL
  >> assume_tac dec_enc_data
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED


Triviality des11:
  ∀x xs es.
    enc_section 11w enc_data (x::xs) = SOME es ⇒
    dec_section 11w dec_data (append es) = ret [] (x::xs)
Proof
  qspec_then ‘[]’ mp_tac des11r \\ simp[]
QED




(* pass through thms; saying that if trying to decode a X from the bytecode of a Y results in a no-op *)
Triviality pt12:
  ∀x xs ss2.
    enc_section 2w (enc_idx_alpha enc_map) (x::xs) = SOME ss2 ⇒
    dec_section 1w dec_ass (append ss2) = ret (append ss2) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_ass’] (drule_at Any) enc_dec_section_pt
  >> simp[]
QED


Triviality pt0r:
  ∀rest b enc x xs es. b ≠ 0w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 0w dec_byte (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  \\ qspecl_then [‘0w’, ‘dec_byte’, ‘b’, ‘enc’] dxrule_all enc_dec_section_ptr
  \\ simp[]
QED

Triviality pt0:
  ∀b enc x xs es. b ≠ 0w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 0w dec_byte (append es) = ret (append es) []
Proof
     rpt strip_tac
  \\ qspec_then ‘[]’ dxrule_all pt0r
  \\ simp[]
QED


Triviality pt1r:
  ∀rest b enc x xs es. b ≠ 1w ∧
  enc_section b enc (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’, ‘b’, ‘enc’] (drule_at Any) enc_dec_section_ptr
  >> simp[]
QED

Triviality pt1:
  ∀b enc x xs es. b ≠ 1w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 1w dec_functype (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspec_then ‘[]’ (drule_at Any) pt1r
  >> simp[]
QED


Triviality pt3r:
  ∀rest b enc x xs es. b ≠ 3w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 3w dec_u32 (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’, ‘b’, ‘enc’] (drule_at Any) enc_dec_section_ptr
  >> simp[]
QED

Triviality pt3:
  ∀b enc x xs es. b ≠ 3w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 3w dec_u32 (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspec_then ‘[]’ (drule_at Any) pt3r
  >> simp[]
QED


Triviality pt5r:
  ∀rest b enc x xs es. b ≠ 5w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 5w dec_limits (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’, ‘b’, ‘enc’] (drule_at Any) enc_dec_section_ptr
  >> simp[]
QED

Triviality pt5:
  ∀b enc x xs es. b ≠ 5w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 5w dec_limits (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspec_then ‘[]’ (drule_at Any) pt5r
  >> simp[]
QED


Triviality pt6r:
  ∀rest b enc x xs es. b ≠ 6w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 6w dec_global (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘6w’, ‘dec_global’, ‘b’, ‘enc’] (drule_at Any) enc_dec_section_ptr
  >> simp[]
QED

Triviality pt6:
  ∀b enc x xs es. b ≠ 6w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 6w dec_global (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspec_then ‘[]’ (drule_at Any) pt6r
  >> simp[]
QED


Triviality pt10r:
  ∀rest b enc x xs es. b ≠ 10w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 10w dec_code (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘10w’, ‘dec_code’, ‘b’, ‘enc’] (drule_at Any) enc_dec_section_ptr
  >> simp[]
QED

Triviality pt10:
  ∀b enc x xs es. b ≠ 10w ∧
    enc_section b enc (x::xs) = SOME es ⇒
    dec_section 10w dec_code (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspec_then ‘[]’ (drule_at Any) pt10r
  >> simp[]
QED





(***********************************)
(*   Pass through, names section   *)
(***********************************)

Triviality ptns1:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 1w dec_functype (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

Triviality ptns3:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 3w dec_u32 (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

Triviality ptns5:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 5w dec_limits (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

Triviality ptns6:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 6w dec_global (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

Triviality ptns10:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 10w dec_code (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

Triviality ptns11:
  ∀x ex.
    enc_names_section x = SOME ex ⇒
    dec_section 11w dec_data (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ Cases_on ‘x = blank_names’
  >- gvs[]
  \\ imp_res_tac enc_names_section_not_blank__lbn0
  >> rw[oneline dec_section_def]
QED

(*************************)
(*     dec-enc names     *)
(*************************)

Theorem dec_enc_names:
  ∀n encn rest.
    enc_names_section n = SOME encn ⇒
    dec_names_section $ encn a++ rest = ret rest [n] ∨ n = blank_names
Proof
     namedCases ["m_name f_names l_names"]
  \\ namedCases_on ‘m_name’ ["s"]
  \\ rewrite_tac[GSYM implode_def]
  \\ namedCases_on ‘s’ ["", "s ss"]
  >> namedCases_on ‘f_names’ ["", "f fs"]
  >> namedCases_on ‘l_names’ ["", "l ls"]
    >> rw $ ssaa [enc_names_section_def, prepend_B_sz_def, string2bytes_def, blank_names_values]
    (* get encoders in the right shape *)
    >> ifHyp ‘SOME _ = enc_u32 _         ’ $ assume_tac o GSYM
    >> ifHyp ‘SOME _ = enc_section 0w _ _’ $     mp_tac o GSYM
    (* remove superfluous hyps - for interactive proofs
    >> ifHyp ‘id_OK ""’                        $ kall_tac
    >> ifHyp ‘LENGTH magic_bytes < 4294967296’ $ kall_tac
    *)
    (* magic bytes & prepended size *)
    >> imp_res_tac dec_enc_u32
    >> imp_res_tac enc_section_nEmp__nNUL
    (* decode various sections, based on whether they're present or not *)
    >> gvs $ ssaa [dec_names_section_def, name_bytes_def, string2bytes_def]
    >> gvs $ [GSYM LENGTH_APPEND, Excl "LENGTH_APPEND", TAKE_LENGTH_APPEND]
    >> simp ssa
    (**)
    >> imp_res_tac pt0      (* imp_res_tac only fires if antecedent is present *)
    >> imp_res_tac pt0r (* for any given goal, some of these hyps may be superfluous *)
    >> imp_res_tac pt12
    (**)
    >> imp_res_tac dess0
    >> imp_res_tac dess1
    >> imp_res_tac dess2
    >> imp_res_tac dess0r
    >> imp_res_tac dess1r
    (**)
    >> fs[names_component_equality, DROP_LENGTH_APPEND, GSYM LENGTH_APPEND, Excl "LENGTH_APPEND"]
QED

Theorem dec_enc_names_NE: (* not empty *)
  ∀n encn rest.
    n ≠ blank_names ∧ enc_names_section n = SOME encn ⇒
    dec_names_section $ encn a++ rest = ret rest [n]
Proof
     ntac 4 strip_tac
  \\ imp_res_tac dec_enc_names
  \\ gvs[]
QED

Theorem dec_enc_names_NR: (* no rest *)
  ∀n encn.
    enc_names_section n = SOME encn ⇒
    dec_names_section $ append encn = ret [] [n]
Proof
     rpt strip_tac
  \\ Cases_on ‘n = blank_names’
  >-(
       rw[oneline dec_names_section_def]
    >> assume_tac enc_names_section_blank
    >> gvs[]
  )
  \\ imp_res_tac dec_enc_names
  \\ pop_assum $ qspec_then ‘[]’ mp_tac
  \\ simp[]
QED

Theorem dec_enc_module:
  ∀mod emn.
    enc_module mod = SOME emn ⇒
    dec_mod_and_names $ append emn = ret [] (mod,blank_names)
Proof
     rpt strip_tac
  >> namedCases_on ‘mod’ ["types funcs mems globals datas"]
  >> namedCases_on ‘funcs’   ["","f fs"]
  >> TRY $ qpat_assum ‘enc_module (_ _ (f::fs) _ _ _) = _’ (fn _ => namedCases_on ‘split_funcs fs’ ["fs_types fs_lbods"])
  >> namedCases_on ‘types’   ["","t ts"]
  >> namedCases_on ‘mems’    ["","m ms"]
  >> namedCases_on ‘globals’ ["","g gs"]
  >> namedCases_on ‘datas’   ["","d ds"]
    >> gvs[blank_mod_def, enc_mod_and_names_def, dec_mod_and_names_def, split_funcs_def]
    >> imp_res_tac enc_section_nEmp__nNUL
    >> gvs[mod_leader_def]
    (**)
    >> imp_res_tac pt1
    >> imp_res_tac pt1r
    >> imp_res_tac pt3
    >> imp_res_tac pt3r
    >> imp_res_tac pt5
    >> imp_res_tac pt5r
    >> imp_res_tac pt6
    >> imp_res_tac pt6r
    >> imp_res_tac pt10
    (**)
    >> imp_res_tac des11
    >> imp_res_tac des10r
    >> imp_res_tac des10
    >> imp_res_tac des6r
    >> imp_res_tac des6
    >> imp_res_tac des5r
    >> imp_res_tac des5
    >> imp_res_tac des3r
    >> imp_res_tac des3
    >> imp_res_tac des1r
    >> imp_res_tac des1
    (**)
    >> simp ssa
    >> simp [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs]
QED

Theorem dec_enc_mod_and_names:
  ∀mod emn nms.
    enc_mod_and_names mod nms = SOME emn ⇒
    dec_mod_and_names $ append emn = ret [] (mod,nms)
Proof
     rpt strip_tac
  \\ Cases_on ‘nms = blank_names’
  >- gvs[dec_enc_module]
  \\ namedCases_on ‘mod’ ["types funcs mems globals datas"]
  >> namedCases_on ‘funcs’   ["","f fs"]
  >> ifHyp ‘enc_mod_and_names (_ _ (f::fs) _ _ _) _ = _’ (fn _ => namedCases_on ‘split_funcs fs’ ["fs_types fs_lbods"])
  >> namedCases_on ‘types’   ["","t ts"]
  >> namedCases_on ‘mems’    ["","m ms"]
  >> namedCases_on ‘globals’ ["","g gs"]
  >> namedCases_on ‘datas’   ["","d ds"]
    >> gvs[blank_mod_def, enc_mod_and_names_def, dec_mod_and_names_def, split_funcs_def]
    >> imp_res_tac enc_section_nEmp__nNUL
    >> imp_res_tac enc_names_section_not_blank__nNUL
    >> gvs[mod_leader_def]
    (**)
    >> imp_res_tac pt1
    >> imp_res_tac pt3
    >> imp_res_tac pt5
    >> imp_res_tac pt6
    >> imp_res_tac pt10
    >> imp_res_tac pt1r
    >> imp_res_tac pt3r
    >> imp_res_tac pt5r
    >> imp_res_tac pt6r
    >> imp_res_tac pt10r
    (**)
    >> imp_res_tac des11r
    >> imp_res_tac des10r
    >> imp_res_tac des6r
    >> imp_res_tac des5r
    >> imp_res_tac des3r
    >> imp_res_tac des1r
    >> imp_res_tac des11
    >> imp_res_tac des10
    >> imp_res_tac des6
    >> imp_res_tac des5
    >> imp_res_tac des3
    >> imp_res_tac des1
    (**)
    >> imp_res_tac ptns1
    >> imp_res_tac ptns3
    >> imp_res_tac ptns5
    >> imp_res_tac ptns6
    >> imp_res_tac ptns10
    >> imp_res_tac ptns11
    >> imp_res_tac dec_enc_names_NR
    (**)
    >> simp ssa
    >> simp [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs]
QED

