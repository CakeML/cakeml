(*
  Properties of CWasm 1.ε AST ⇔ WBF En-/De-coders
*)
Theory      wbf_thms
Ancestors   mlstring leb128 wasmLang wbf_prelim wbf
Libs        preamble wordsLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  =          [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]

val ifsolves = fn x => TRY (x \\ NO_TAC)
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



Theorem enc_u32_nEmp:
  ∀x encx. enc_u32 x = SOME encx ⇒ ¬NULL (append encx)
Proof
     simp[enc_u32_def, enc_unsigned_word_def]
  \\ rw[Once enc_num_def]
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
  ∀lb enc x xs exxs. enc_section lb enc (x::xs) = SOME exxs ⇒ ¬NULL (append exxs)
Proof
     rw[enc_section_def]
  \\ simp[]
QED

Theorem enc_section_nEmp':
  ∀lb enc xs exs. ¬NULL xs ∧ enc_section lb enc xs = SOME exs ⇒
  ¬NULL (append exs)
Proof
     rw[enc_section_def]
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
    >>~- ([‘enc_numI’  ],
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
    >>~- ([‘enc_paraI’ ],
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
    >>~- ([‘enc_varI’  ],
               imp_res_tac enc_varI_nEmp_nTermB
            \\ imp_res_tac var_cf_instr_disjoint
            \\ gvs[Once dec_instr_def, AllCaseEqs()]
            (**)
            \\ ‘b::(bs ++ rs) = append encx ++ rs’ by simp[]
            \\ pop_assum (fn x => rewrite_tac[x])
            \\ simp[dec_enc_varI]
    )
    >>~- ([‘enc_loadI’ ],
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
    >>~- ([‘enc_storeI’],
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
    \\ (* if case *)
       Cases_on ‘l0’
      >> gvs[dec_instr_def]
      >> simp $ ssaa [dec_instr_def]
      >> imp_res_tac dec_enc_blocktype
      >> simp ssa
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

(*
  m ``MAP``
MAP_MAPi
MAP_MAP_o
MAP_o
MAP_COMPOSE
*)


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

Triviality s2b_explode[simp]:
  ∀x. string2bytes (explode x) = [] ⇔ x = «»
Proof
  gen_tac
  \\ simp[string2bytes_def]
  \\ iff_tac
  >> rw[]
  \\ qspec_then `x` mp_tac implode_explode
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


Theorem enc_section_empty[simp]:
  ∀lb enc. enc_section lb enc [] = SOME $ List []
Proof
  rw[enc_section_def]
QED

Theorem enc_section_empty_conv:
  ∀lb enc xs encxs. NULL (append encxs) ∧
  enc_section lb enc xs = SOME encxs ⇒ xs = []
Proof
     rw[enc_section_def, NULL_EQ_NIL, prepend_sz_def]
  >> gvs[append_def]
QED


Triviality enc_names_section_blank[simp]:
  enc_names_section blank_names = SOME $ List []
Proof
     rw[enc_names_section_def, blank_names_def, enc_section_def]
  >> fs[id_OK_def, prepend_sz_def, enc_u32_def, magic_bytes_def, string2bytes_def]
QED

Triviality enc_names_section_blank_conv:
  ∀x ex. enc_names_section x = SOME ex ∧ NULL (append ex) ⇒
  x = blank_names
Proof
     rw[enc_names_section_def, enc_section_def, NULL_EQ_NIL, blank_names_values]
  >> Cases_on `x`
  >> gvs[names_component_equality]
QED

Triviality names_not_blank:
  ∀x. x ≠ blank_names ⇒ x.mname ≠ «» ∨ ¬NULL x.fnames ∨ ¬NULL x.lnames
Proof
     namedCases ["m_name f_names l_names"]
  \\ namedCases_on ‘m_name’ ["s"]
  \\ rewrite_tac[GSYM implode_def]
  \\ namedCases_on ‘s’ ["", "s ss"]
  >> namedCases_on ‘f_names’ ["", "f fs"]
  >> namedCases_on ‘l_names’ ["", "l ls"]
  >> simp[blank_names_values]
QED

Triviality names_not_blank':
  ∀x. x ≠ blank_names ⇒ ¬NULL (string2bytes $ explode x.mname) ∨ ¬NULL x.fnames ∨ ¬NULL x.lnames
Proof
     ntac 2 $ rpt strip_tac
  \\ imp_res_tac names_not_blank
  >> simp[]
  \\ Cases_on `x.mname`
  \\ Cases_on `s`
  >> gvs[string2bytes_def]
QED


Triviality enc_names_section_nEmp:
  ∀x encx. x ≠ blank_names ∧ enc_names_section x = SOME encx ⇒
  ¬NULL (append encx)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_names_section_blank_conv
QED

Triviality enc_names_section_nEmp':
  ∀x encx. x ≠ blank_names ∧ enc_names_section x = SOME encx ⇒
  ∃dc. append encx = 0w::dc
Proof
     rpt strip_tac
  \\ drule enc_names_section_blank_conv
  \\ rw[]
  \\ gvs[oneline enc_names_section_def, NULL_EQ_NIL]
  >> Cases_on `append ss0`
  >> Cases_on `append ss1`
  >> Cases_on `append ss2`
  >> gvs[]
QED


(*
Triviality enc_names_section_nEmp:
  ∀x. x ≠ blank_names ⇒ ∃encx. enc_names_section x = SOME encx
Proof
  Cases
  rw[enc_names_section_def]
QED
*)

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


Theorem dec_enc_section_NE: (* non empty *)
  ∀lb xs enc dec encxs rest. ¬(NULL xs) ∧
  enc_section lb enc xs = SOME encxs ∧
  (∀x encx rs. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
  ⇒
  dec_section lb dec $ encxs a++ rest= (INR xs, rest)
Proof
     rw[enc_section_def, prepend_sz_def]
  \\ simp[dec_section_def]
  \\ imp_res_tac dec_enc_u32
  \\ simp ssa
  \\ imp_res_tac dec_enc_vector
  \\ simp[]
QED

Theorem dec_enc_section_NR: (* no rest *)
  ∀lb xs enc dec encxs.
  enc_section lb enc xs = SOME encxs ∧
  (∀x encx rs. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
  ⇒
  dec_section lb dec $ append encxs = (INR xs, [])
Proof
     rw[enc_section_def, prepend_sz_def]
  >- (Cases_on `xs` >> gvs[NULL, dec_section_def])
  \\ simp[dec_section_def]
  \\ imp_res_tac dec_enc_u32
  \\ simp ssa
  \\ imp_res_tac dec_enc_vector
  \\ pop_assum $ qspec_then `[]` mp_tac
  \\ simp[]
QED

Theorem dec_enc_section:
  ∀lb xs enc dec encxs rest.
  enc_section lb enc xs = SOME encxs ∧
  (∀x encx rs. enc x = SOME encx ⇒ dec (encx a++ rs) = (INR x, rs))
  ⇒
  dec_section lb dec $ encxs a++ rest = (INR xs, rest) ∨ xs = []
Proof
     Cases_on `xs`
  >> rw[enc_section_def, prepend_sz_def]
  \\ imp_res_tac dec_enc_u32
  \\ imp_res_tac dec_enc_vector
  \\ simp $ ssaa [dec_section_def]
QED


Theorem dec_section_passThrough:
  ∀lb b dec bs. lb ≠ b ⇒
  dec_section lb dec (b::bs) = ret (b::bs) []
Proof
  simp[Once dec_section_def]
QED

Theorem enc_dec_section_passThrough:
  ∀b2 dec b1 enc x xs exxs. b1 ≠ b2 ∧
  enc_section b1 enc (x::xs) = SOME exxs ⇒
  dec_section b2 dec $ append exxs = ret (append exxs) []
Proof
     rw[enc_section_def]
  \\ rw[dec_section_passThrough]
QED

Theorem enc_dec_section_passThrough_rest:
  ∀b2 dec b1 enc x xs exxs rest. b1 ≠ b2 ∧
  enc_section b1 enc (x::xs) = SOME exxs ⇒
  dec_section b2 dec $ exxs a++ rest = ret (exxs a++ rest) []
Proof
     rw[enc_section_def]
  \\ rw[dec_section_passThrough]
QED



Theorem dec_enc_names_passThrough:
  ∀b rest. b ≠ 0w ⇒
  dec_names_section $ (b::rest) = ret (b::rest) []
Proof
  rw[Once dec_names_section_def]
QED

(**********************************************************************)
(*   Some widgets to make the names proof more modular and abstract   *)
(**********************************************************************)

Triviality widget0_rest:
  ∀rest x xs ss0.
  enc_section 0w enc_byte (x::xs) = SOME ss0 ⇒
  dec_section 0w dec_byte (ss0 a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_byte
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget0:
  ∀x xs ss0.
  enc_section 0w enc_byte (x::xs) = SOME ss0 ⇒
  dec_section 0w dec_byte (append ss0) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget0_rest \\ simp[]
QED

Triviality widget1_rest:
  ∀rest x xs ss1.
  enc_section 1w enc_ass (x::xs) = SOME ss1 ⇒
  dec_section 1w dec_ass (ss1 a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_ass
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget1:
  ∀x xs ss1.
  enc_section 1w enc_ass (x::xs) = SOME ss1 ⇒
  dec_section 1w dec_ass (append ss1) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget1_rest \\ simp[]
QED

Triviality widget2:
  ∀x xs ss2.
  enc_section 2w (enc_idx_alpha enc_map) (x::xs) = SOME ss2 ⇒
  dec_section 2w (dec_idx_alpha dec_map) (append ss2) = ret [] (x::xs)
Proof
     rpt strip_tac
  \\ imp_res_tac enc_section_nEmp
  \\ assume_tac dec_enc_map
  \\ dxrule_at Any dec_enc_idx_alpha
  \\ strip_tac
  \\ imp_res_tac dec_enc_section_NR
QED

Triviality widget_1_rest:
  ∀rest x xs es.
  enc_section 1w enc_functype (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_functype
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget_1:
  ∀x xs es.
  enc_section 1w enc_functype (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget_1_rest \\ simp[]
QED

Triviality widget3_rest:
  ∀rest x xs es.
  enc_section 3w enc_u32 (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_u32
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget3:
  ∀rest x xs es.
  enc_section 3w enc_u32 (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget3_rest \\ simp[]
QED

Triviality widget5_rest:
  ∀rest x xs es.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_limits
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget5:
  ∀rest x xs es.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget5_rest \\ simp[]
QED

Triviality widget6_rest:
  ∀rest x xs es.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 6w dec_global (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_global
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget6:
  ∀rest x xs es.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 6w dec_global (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget6_rest \\ simp[]
QED


Triviality widget10_rest:
  ∀rest x xs es.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 10w dec_code (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_code
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED

Triviality widget10:
  ∀rest x xs es.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 10w dec_code (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget10_rest \\ simp[]
QED

Triviality widget11_rest:
  ∀rest x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 11w dec_data (es a++ rest) = ret rest (x::xs)
Proof
     rpt strip_tac
  >> imp_res_tac enc_section_nEmp
  >> assume_tac dec_enc_data
  >> imp_res_tac dec_enc_section
  >> pop_assum $ qspec_then ‘rest’ mp_tac
  >> simp[]
QED


Triviality widget11:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 11w dec_data (append es) = ret [] (x::xs)
Proof
  qspec_then `[]` mp_tac widget11_rest \\ simp[]
QED

Triviality pt01_rest:
  ∀rest x xs ss1.
  enc_section 1w enc_ass (x::xs) = SOME ss1 ⇒
  dec_section 0w dec_byte (ss1 a++ rest) = ret (ss1 a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘0w’, ‘dec_byte’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt01:
  ∀x xs ss1.
  enc_section 1w enc_ass (x::xs) = SOME ss1 ⇒
  dec_section 0w dec_byte (append ss1) = ret (append ss1) []
Proof
     rpt strip_tac
  >> qspecl_then [‘0w’, ‘dec_byte’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt02:
  ∀x xs ss2.
  enc_section 2w (enc_idx_alpha enc_map) (x::xs) = SOME ss2 ⇒
  dec_section 0w dec_byte (append ss2) = ret (append ss2) []
Proof
     rpt strip_tac
  >> qspecl_then [‘0w’, ‘dec_byte’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt12:
  ∀x xs ss2.
  enc_section 2w (enc_idx_alpha enc_map) (x::xs) = SOME ss2 ⇒
  dec_section 1w dec_ass (append ss2) = ret (append ss2) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_ass’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_1:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_3:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_5:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_6:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 6w dec_global (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘6w’, ‘dec_global’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_10:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 10w dec_code (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘10w’, ‘dec_code’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED



Triviality pt11_1_rest:
  ∀x xs es rest.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt11_3_rest:
  ∀x xs es rest.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt11_5_rest:
  ∀x xs es rest.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt11_6_rest:
  ∀x xs es rest.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 6w dec_global (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘6w’, ‘dec_global’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt11_10_rest:
  ∀x xs es rest.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 10w dec_code (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘10w’, ‘dec_code’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt6_1:
  ∀x xs es.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt6_1_rest:
  ∀x xs es rest.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt6_3:
  ∀x xs es.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt6_3_rest:
  ∀x xs es rest.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt6_5:
  ∀x xs es.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt6_5_rest:
  ∀x xs es rest.
  enc_section 6w enc_global (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED


Triviality pt3_1:
  ∀x xs es.
  enc_section 3w enc_u32 (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt3_1_rest:
  ∀x xs es rest.
  enc_section 3w enc_u32 (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt5_1:
  ∀x xs es.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt5_1_rest:
  ∀x xs es rest.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 1w dec_functype (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘1w’, ‘dec_functype’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt5_3:
  ∀x xs es.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt5_3_rest:
  ∀x xs es rest.
  enc_section 5w enc_limits (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED




Triviality pt10_5:
  ∀x xs es.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt10_5_rest:
  ∀x xs es rest.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED

Triviality pt10_6:
  ∀x xs es.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 6w dec_global (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘6w’, ‘dec_global’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt10_6_rest:
  ∀x xs es rest.
  enc_section 10w enc_code (x::xs) = SOME es ⇒
  dec_section 6w dec_global (es a++ rest) = ret (es a++ rest) []
Proof
     rpt strip_tac
  >> qspecl_then [‘6w’, ‘dec_global’] (drule_at Any) enc_dec_section_passThrough_rest
  >> simp[]
QED



Triviality pt11_3:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 3w dec_u32 (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘3w’, ‘dec_u32’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality pt11_5:
  ∀x xs es.
  enc_section 11w enc_data (x::xs) = SOME es ⇒
  dec_section 5w dec_limits (append es) = ret (append es) []
Proof
     rpt strip_tac
  >> qspecl_then [‘5w’, ‘dec_limits’] (drule_at Any) enc_dec_section_passThrough
  >> simp[]
QED

Triviality ptns_1:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 1w dec_functype (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED


Triviality ptns_3:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 3w dec_u32 (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED

Triviality ptns_5:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 5w dec_limits (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED

Triviality ptns_6:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 6w dec_global (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED

Triviality ptns_10:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 10w dec_code (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED

Triviality ptns_11:
  ∀x ex.
  enc_names_section x = SOME ex ⇒
  dec_section 11w dec_data (append ex) = ret (append ex) []
Proof
     rpt strip_tac
  \\ `x = blank_names ∨ x ≠ blank_names` by simp[]
  >- gvs[]
  \\ imp_res_tac enc_names_section_nEmp'
  >> rw[oneline dec_section_def]
QED


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
    >> rw $ ssaa [enc_names_section_def, prepend_sz_def, string2bytes_def, blank_names_values]
    (* get encoders in the right shape *)
    >> TRY $ qpat_x_assum ‘SOME _ = enc_u32 _         ’ $ assume_tac o GSYM
    >> TRY $ qpat_x_assum ‘SOME _ = enc_section 0w _ _’ $ mp_tac o GSYM
    (* remove superfluous hyps - for interactive proofs
    >> TRY $ qpat_x_assum ‘id_OK ""’ $ kall_tac
    >> TRY $ qpat_x_assum ‘LENGTH magic_bytes < 4294967296’ $ kall_tac
    *)
    (* magic bytes & prepended size *)
    >> imp_res_tac dec_enc_u32
    >> imp_res_tac enc_section_nEmp
    (* decode various sections, based on whether they're present or not *)
    >> gvs $ ssaa [dec_names_section_def, magic_bytes_def, string2bytes_def]
    >> gvs $ [GSYM LENGTH_APPEND, Excl "LENGTH_APPEND", TAKE_LENGTH_APPEND]
    >> simp ssa
    >> imp_res_tac pt01 (* imp_res_tac only fires if antecedent is present *)
    >> imp_res_tac pt02 (* for any given goal, some of these hyps may be superfluous *)
    >> imp_res_tac pt12
    >> imp_res_tac pt01_rest
    >> imp_res_tac widget0
    >> imp_res_tac widget1
    >> imp_res_tac widget2
    >> imp_res_tac widget0_rest
    >> imp_res_tac widget1_rest
    >> fs[names_component_equality, DROP_LENGTH_APPEND, GSYM LENGTH_APPEND, Excl "LENGTH_APPEND"]
QED

Theorem dec_enc_names_NE: (* not empty *)
  ∀n encn rest. n ≠ blank_names ∧
  enc_names_section n = SOME encn ⇒
  dec_names_section $ encn a++ rest = ret rest [n]
Proof
     ntac 4 $ strip_tac
  \\ imp_res_tac dec_enc_names
  \\ gvs[]
QED

Theorem dec_enc_names_NR: (* no rest *)
  ∀n encn.
  enc_names_section n = SOME encn ⇒
  dec_names_section $ append encn = ret [] [n]
Proof
     rpt strip_tac
  \\ `n = blank_names ∨ n ≠ blank_names` by simp[]
  >-(
       rw[oneline dec_names_section_def]
    >> assume_tac enc_names_section_blank
    >> gvs[]
  )
  \\ imp_res_tac dec_enc_names
  \\ pop_assum $ qspec_then `[]` mp_tac
  \\ simp[]
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

Theorem dec_enc_module:
  ∀mod emn. enc_module mod = SOME emn ⇒
  dec_mod_and_names $ append emn = ret [] (mod,blank_names)
Proof
     rpt strip_tac
  >> namedCases_on ‘mod’ ["types funcs mems globals datas"]
  >> namedCases_on ‘funcs’   ["","f fs"]
  >> TRY $ qpat_assum ‘enc_module (_ _ (f::fs) _ _ _) = _’ (fn _ => namedCases_on `split_funcs fs` ["fs_types fs_lbods"])
  >> namedCases_on ‘types’   ["","t ts"]
  >> namedCases_on ‘mems’    ["","m ms"]
  >> namedCases_on ‘globals’ ["","g gs"]
  >> namedCases_on ‘datas’   ["","d ds"]
    >> gvs[blank_mod_def, enc_mod_and_names_def, dec_mod_and_names_def, split_funcs_def]
    >> imp_res_tac enc_section_nEmp
    >> gvs[mod_leader_def]
    (**)
    >> imp_res_tac pt11_1
    >> imp_res_tac pt11_3
    >> imp_res_tac pt11_5
    >> imp_res_tac pt11_6
    >> imp_res_tac pt11_10
    (**)
    >> imp_res_tac pt10_5
    >> imp_res_tac pt10_5_rest
    >> imp_res_tac pt10_6
    >> imp_res_tac pt10_6_rest
    (**)
    >> imp_res_tac pt6_1
    >> imp_res_tac pt6_1_rest
    >> imp_res_tac pt6_3
    >> imp_res_tac pt6_3_rest
    >> imp_res_tac pt6_5
    >> imp_res_tac pt6_5_rest
    (**)
    >> imp_res_tac pt5_1
    >> imp_res_tac pt5_1_rest
    >> imp_res_tac pt5_3
    >> imp_res_tac pt5_3_rest
    (**)
    >> imp_res_tac pt3_1
    >> imp_res_tac pt3_1_rest
    (**)
    >> imp_res_tac widget11
    >> imp_res_tac widget10_rest
    >> imp_res_tac widget10
    >> imp_res_tac widget6_rest
    >> imp_res_tac widget6
    >> imp_res_tac widget5_rest
    >> imp_res_tac widget5
    >> imp_res_tac widget3_rest
    >> imp_res_tac widget3
    >> imp_res_tac widget_1_rest
    >> imp_res_tac widget_1
    (**)
    >> ifsolves (simp $ ssaa [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs])
    >> simp                  [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs]
QED

Theorem dec_enc_mod_and_names:
  ∀mod emn nms. enc_mod_and_names mod nms = SOME emn ⇒
  dec_mod_and_names $ append emn = ret [] (mod,nms)
Proof
  rpt strip_tac
  \\ `nms = blank_names ∨ nms ≠ blank_names` by simp[]
  >- gvs[dec_enc_module]
  \\
     namedCases_on ‘mod’ ["types funcs mems globals datas"]
  >> namedCases_on ‘funcs’   ["","f fs"]
  >> TRY $ qpat_assum ‘enc_mod_and_names (_ _ (f::fs) _ _ _) _ = _’ (fn _ => namedCases_on `split_funcs fs` ["fs_types fs_lbods"])
  >> namedCases_on ‘types’   ["","t ts"]
  >> namedCases_on ‘mems’    ["","m ms"]
  >> namedCases_on ‘globals’ ["","g gs"]
  >> namedCases_on ‘datas’   ["","d ds"]
    >> gvs[blank_mod_def, enc_mod_and_names_def, dec_mod_and_names_def, split_funcs_def]
    >> imp_res_tac enc_section_nEmp
    >> imp_res_tac enc_names_section_nEmp
    >> gvs[mod_leader_def]
    (**)
    >> imp_res_tac pt11_1
    >> imp_res_tac pt11_1_rest
    >> imp_res_tac pt11_3
    >> imp_res_tac pt11_3_rest
    >> imp_res_tac pt11_5
    >> imp_res_tac pt11_5_rest
    >> imp_res_tac pt11_6
    >> imp_res_tac pt11_6_rest
    >> imp_res_tac pt11_10
    >> imp_res_tac pt11_10_rest
    (**)
    >> imp_res_tac pt10_5
    >> imp_res_tac pt10_5_rest
    >> imp_res_tac pt10_6
    >> imp_res_tac pt10_6_rest
    (**)
    >> imp_res_tac pt6_1
    >> imp_res_tac pt6_1_rest
    >> imp_res_tac pt6_3
    >> imp_res_tac pt6_3_rest
    >> imp_res_tac pt6_5
    >> imp_res_tac pt6_5_rest
    (**)
    >> imp_res_tac pt5_1
    >> imp_res_tac pt5_1_rest
    >> imp_res_tac pt5_3
    >> imp_res_tac pt5_3_rest
    (**)
    >> imp_res_tac pt3_1
    >> imp_res_tac pt3_1_rest
    (**)
    >> imp_res_tac widget11_rest
    >> imp_res_tac widget11
    >> imp_res_tac widget10_rest
    >> imp_res_tac widget10
    >> imp_res_tac widget6_rest
    >> imp_res_tac widget6
    >> imp_res_tac widget5_rest
    >> imp_res_tac widget5
    >> imp_res_tac widget3_rest
    >> imp_res_tac widget3
    >> imp_res_tac widget_1_rest
    >> imp_res_tac widget_1
    (**)
    >> imp_res_tac ptns_1
    >> imp_res_tac ptns_3
    >> imp_res_tac ptns_5
    >> imp_res_tac ptns_6
    >> imp_res_tac ptns_10
    >> imp_res_tac ptns_11
    >> imp_res_tac dec_enc_names_NR
    (**)
    >> ifsolves (simp $ ssaa [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs])
    >> simp                  [module_component_equality, func_component_equality, zip_funcs_def, split_zip_funcs]
QED

(*
Theorem dec_enc_module1:
  ∀mod nms emn. enc_mod_and_names mod nms = SOME emn ⇒
  dec_mod_and_names $ append emn = ret [] (mod,nms)
Proof

     namedCases ["types funcs mems globals datas"]
  \\ namedCases_on ‘types’   ["","t ts"]
  \\ namedCases_on ‘funcs’   ["","f fs"]
  \\ namedCases_on ‘mems’    ["","m ms"]
  \\ namedCases_on ‘globals’ ["","g gs"]
  \\ namedCases_on ‘datas’   ["","d ds"]

     namedCases ["m_name f_names l_names"]
  \\ namedCases_on ‘m_name’ ["s"]
  \\ rewrite_tac[GSYM implode_def]
  \\ namedCases_on ‘s’ ["", "s ss"]
  >> namedCases_on ‘f_names’ ["", "f fs"]
  >> namedCases_on ‘l_names’ ["", "l ls"]

     Cases_on `l`
     gen_tac
  \\ `mod = blank_mod ∨ mod ≠ blank_mod` by simp[]
  >- simp[]
  \\ rw[enc_module_def]
  \\ namedCases_on `split_funcs mod.funcs` ["mod_fns mod_code"]
  \\ gvs[dec_module_def, mod_leader_def]

  \\ namedCases_on ‘split_funcs mod.funcs’
simp[]
QED

Theorem dec_enc_module:
  ∀mod nms emn. enc_module mod nms = SOME emn ⇒
  dec_module $ emn = ret [] (mod,nms)
Proof

     ntac 2 $ gen_tac
  \\ `mod = blank_mod ∧ nms = blank ∨ ¬(mod = blank_mod ∧ nms = blank)` by simp[]
  >> rpt $ pop_assum mp_tac
  >> simp[]

  \\ ``

  >> `mod = blank_mod ∧ nms = blank ∨ ¬(mod = blank_mod ∧ nms = blank)` by simp[]
  >> rw[]

  >> pop_assum mp_tac
  >> `nms = blank ∨ nms ≠ blank` by simp[]

      rw[enc_module_def, dec_module_def, AllCaseEqs()]
  \\ namedCases_on `split_funcs mod.funcs` ["mod_fns mod_code"]
  \\ gvs[mod_leader_def]
  >> `nms = blank ∨ nms ≠ blank` by simp[]
  >> pop_assum mp_tac
  >> simp[]

cheat
  >> gvs[]

  (**)
  \\ assume_tac dec_enc_functype
  \\ assume_tac dec_enc_u32
  \\ assume_tac dec_enc_limits
  \\ assume_tac dec_enc_global
  \\ assume_tac dec_enc_code
  \\ assume_tac dec_enc_data
  \\ imp_res_tac dec_enc_section_NE
  \\ imp_res_tac dec_enc_section_NR
  (**)
    \\ cheat
QED

  \\ ntac 6 $ pop_assum mp_tac
  \\ ntac 6 $ pop_assum kall_tac
  \\ rpt strip_tac
  \\ ntac 6 $ (
     asm_rewrite_tac ssa \\ simp[]
  )
  \\ imp_res_tac dec_enc_names'

  \\ simp[]
  (**)
  \\ rewrite_tac ssa
  (**)

   rw[dec_module_def, AllCaseEqs()]
   \\ gvs[AllCaseEqs()]
   \\ rpt strip_tac
(*
  Cases >>
rpt strip_tac
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


*)


(*
Triviality foo:
  ∀n encn xs len. n ≠ blank ∧
  enc_names_section n = SOME encn ⇒
  ∃xs. append encn = 0w :: xs ∧ ∃ys len. dec_u32 xs = ret ys len
Proof
  ntac 5 $ strip_tac
  \\ imp_res_tac enc_names_section_nEmp
  >> imp_res_tac names_not_blank'
  >> gvs[enc_names_section_def]
  >> imp_res_tac enc_section_nEmp'
  >> gvs[prepend_sz_def]
  >> imp_res_tac dec_enc_u32
  >> rewrite_tac ssa
  >> pop_assum $ qspec_then `magic_bytes ++ ss0 a++ ss1 a++ append ss2` assume_tac
  >> simp[]
QED
*)
