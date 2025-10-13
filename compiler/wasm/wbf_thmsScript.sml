(*
  CWasm 1.ε AST ⇔ Wasm binary format En- & De- coder theorems
*)
Theory      wbf_thms
Ancestors   leb128 wasmLang wbf_prelim wbf
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
  ∀x encx. enc_numI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ⇒
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
  ∀x encx. enc_paraI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ⇒
  b ≠ unrOC ∧ b ≠ nopOC ∧ b ≠ blkOC ∧
  b ≠ lopOC ∧ b ≠ if_OC ∧ b ≠ br_OC ∧
  b ≠ briOC ∧ b ≠ brtOC ∧ b ≠ retOC ∧
  b ≠ calOC ∧ b ≠ rclOC ∧ b ≠ cinOC ∧
  b ≠ rciOC
Proof
  Cases >> rw[enc_paraI_def, AllCaseEqs()]
QED

Theorem var_cf_instr_disjoint:
  ∀x encx. enc_varI x = SOME encx ⇒
  ∃b bs. append encx =  b::bs ⇒
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
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∃b bs. append encx =  b::bs ⇒
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
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∃b bs. append encx = b::bs ⇒
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
  ∀x encx. enc_paraI x = SOME encx ⇒
  ∀rest. ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> simp[enc_paraI_def, dec_varI_def]
QED

Theorem var_num_disjoint:
  ∀x encx. enc_numI x = SOME encx ⇒
  ∀rest. ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> rw[enc_numI_def, AllCaseEqs()]
  >> simp[dec_varI_def]
QED

Theorem para_num_disjoint:
  ∀x encx. enc_numI x = SOME encx ⇒
  ∀rest. ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> rw[enc_numI_def, AllCaseEqs()]
  >> simp[dec_paraI_def]
QED

Theorem var_load_disjoint:
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∀rest. ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_varI_def]
QED

Theorem para_load_disjoint:
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∀rest. ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_load_disjoint:
  ∀x encx. enc_loadI x = SOME encx ⇒
  ∀rest. ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_loadI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED

Theorem var_store_disjoint:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∀rest. ∃e. dec_varI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_varI_def]
QED

Theorem para_store_disjoint:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∀rest. ∃e. dec_paraI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_paraI_def]
QED

Theorem num_store_disjoint:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∀rest. ∃e. dec_numI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  Cases >> gen_tac
  >> simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_numI_def]
QED

Theorem load_store_disjoint:
  ∀x encx. enc_storeI x = SOME encx ⇒
  ∀rest. ∃e. dec_loadI (append encx ++ rest) = (INL e, append encx ++ rest)
Proof
  simp[enc_storeI_def, AllCaseEqs()]
  >> rpt strip_tac >> imp_res_tac dec_enc_2u32
  >> gvs[dec_loadI_def]
QED

Theorem enc_valtype_nEmp_n0x40:
  ∀x encx. enc_valtype x = SOME encx ⇒ ∃b bs. append encx = b::bs ∧ b ≠ 0x40w
Proof
  Cases
  >> Cases_on `w`
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
  ∀x encx. enc_valtype x = SOME encx ⇒
  ∀rest. dec_valtype (encx a++ rest) = (INR x, rest)
Proof
     Cases
  \\ simp[bvtype_nchotomy, enc_valtype_def, dec_valtype_def, AllCaseEqs()]
  \\ Cases_on `w`
  >> simp[]
QED

Theorem dec_enc_functype:
  ∀sg encsg. enc_functype sg = SOME encsg ⇒
  ∀rest. dec_functype (encsg a++ rest) = (INR sg, rest)
Proof
     rw[enc_functype_def, AllCaseEqs()]
  \\ PairCases_on ‘sg’
  \\ gvs[dec_functype_def, AllCaseEqs()]
  \\ rpt $ dxrule dec_enc_vector
  \\ rpt $ disch_then $ qspec_then ‘dec_valtype’ assume_tac
  \\ gvs[dec_enc_valtype]
  \\ simp ssa
QED

Theorem dec_enc_limits:
  ∀x encx. enc_limits x = SOME encx ⇒
  ∀ rest. dec_limits (encx a++ rest) = (INR x, rest)
Proof
     rw[enc_limits_def, AllCaseEqs()]
  >> simp[dec_limits_def, AllCaseEqs(), dec_enc_u32, dec_enc_2u32]
QED

Theorem dec_enc_globaltype:
  ∀x encx. enc_globaltype x = SOME encx ⇒
  ∀rest. dec_globaltype (encx a++ rest) = (INR x, rest)
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
  >>~- ([‘N_const32’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s32])
  >>~- ([‘N_const64’], simp[dec_numI_def, AllCaseEqs(), dec_enc_s64])
  >> simp[dec_numI_def]
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

(*
(* [Note] on "dc": Here the statements says that if we encode an expr (e=T), then we _must_ see an endB (¬e ∨ dc=F)
   But if we're encoding a then-arm (e=F), then we (dc:=)don't care whether the decoder gets a T or F flag *)
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
    >> simp ssa
    >> simp[dec_instr_def]
    (**)

>>~- ([‘enc_blocktype’],
    simp ssa
    >> pop_assum drule_all
    >> imp_res_tac dec_enc_blocktype
    >> strip_tac
    >> simp[]
)
cheat

imp_res_tac dec_enc_u32
simp[]
pop_assum mp_tac
disch_then $ qspec_then `rs` assume_tac
gvs[]
asm_rewrite_tac[]
simp[]
simp[]
simp[AllCaseEqs()]
assume_tac dec_enc_u32
simp[append_def]
simp[append_aux_def]

qspecl_then [‘b’,‘enct’] drule dec_enc_blocktype
gvs[AllCaseEqs()]
rewrite_tac[]
rw[dec_enc_blocktype]

    >> simp[dec_instr_def, AllCaseEqs()]

simp ssa

    >> simp[APPEND, dec_instr_def]



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

Theorem dec_enc_names:
  ∀no eno rest.
  enc_names_section no = SOME eno ⇒
  dec_names_section eno = (INR no, rest)
Proof

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
