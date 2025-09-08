(*
  CWasm 1.ε AST ⇔ Wasm binary format En- & De- coder theorems
*)

Theory      wasm_binary_format_proofs
Ancestors   leb128 ancillaryOps wasmLang wasm_binary_format
Libs        preamble wordsLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  = [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]

(******************************)
(*                            *)
(*     non-empty Theorems     *)
(*                            *)
(******************************)

Theorem enc_numI_nEmp:
  ∀i. ∃b bs. enc_numI i = b::bs
Proof
  gen_tac
  \\ `∃val. enc_numI i = val` by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_numI_def, AllCaseEqs()]
QED

Theorem enc_paraI_nEmp:
  ∀i. ∃b bs. enc_paraI i = b::bs
Proof
  Cases \\ simp[Once enc_paraI_def, AllCaseEqs()]
QED

Theorem enc_varI_nEmp:
  ∀i. ∃b bs. enc_varI i = b::bs
Proof
  Cases \\ simp[Once enc_varI_def, AllCaseEqs()]
QED

Theorem enc_loadI_nEmp:
  ∀i. ∃b bs. enc_loadI i = b::bs
Proof
  gen_tac
  \\ `∃val. enc_loadI i = val` by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_loadI_def, AllCaseEqs()]
QED

Theorem enc_storeI_nEmp:
  ∀i. ∃b bs. enc_storeI i = b::bs
Proof
  gen_tac
  \\ `∃val. enc_storeI i = val` by simp[]
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rw[Once enc_storeI_def, AllCaseEqs()]
QED

Theorem enc_instr_nEmp:
  ∀i enci. enc_instr i = SOME enci ⇒
  ∃b bs. enci = b::bs
Proof
  Cases
  >> rw[Once enc_instr_def, AllCaseEqs()]
  >> mp_tac enc_numI_nEmp
  >> mp_tac enc_paraI_nEmp
  >> mp_tac enc_varI_nEmp
  >> mp_tac enc_loadI_nEmp
  >> mp_tac enc_storeI_nEmp
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

Theorem dec_enc_vector[simp]:
  ∀is dec enc encis rest.
    enc_vector enc is = SOME encis ∧
    (∀x rs. dec (enc x ++ rs) = (INR x,rs))
    ⇒
    dec_vector dec (encis ++ rest) = (INR is, rest)
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
  ∀dec enc is encis rest.
    enc_vector_opt enc is = SOME encis ∧
    (∀x encx rs. enc x = SOME encx ⇒ dec (encx ++ rs) = (INR x,rs))
    ⇒
    dec_vector dec (encis ++ rest) = (INR is, rest)
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
  \\ `∃ val. enc_valtype t = val` by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ simp[enc_valtype_def, AllCaseEqs(), bvtype_nchotomy]
  \\ rpt strip_tac
    >> gvs[dec_valtype_def]
QED

(* askyk about this kind of conditional rewrite *)
Theorem dec_enc_functype[simp]:
  ∀sg encsg rest.
    enc_functype sg = SOME encsg ⇒
    dec_functype (encsg ++ rest) = (INR sg, rest)
Proof
     rw[AllCaseEqs(), enc_functype_def]
  \\ PairCases_on `sg`
  \\ gvs[dec_functype_def, AllCaseEqs()]
  \\ dxrule dec_enc_vector
  \\ disch_then $ qspec_then `dec_valtype` assume_tac
  \\ dxrule dec_enc_vector
  \\ disch_then $ qspec_then `dec_valtype` assume_tac
  \\ gvs[dec_enc_valtype]
  \\ simp ssa
QED

Theorem dec_enc_limits[simp]:
  ∀ lim rest. dec_limits (enc_limits lim ++ rest) = (INR lim, rest)
Proof
     rpt gen_tac
  \\ `∃ val. enc_limits lim = val` by simp []
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
  \\ `∃ val. enc_globaltype x = val` by simp []
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
  \\ `∃ val. enc_blocktype b = val` by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ gvs[enc_blocktype_def, AllCaseEqs()]
  \\ rpt strip_tac
  >> gvs[dec_blocktype_def]
  \\ Cases_on `vt` \\ Cases_on `w`
  >> simp[enc_valtype_def, AllCaseEqs()]
QED

(*
Theorem dec_enc_instructions:
  ∀e is encis rest. enc_instr_list e is = SOME encis ⇒ dec_expr  (encis ++ rest) = (INR is, rest) ∧
  ∀  i  enci  rest. enc_instr        i  = SOME enci  ⇒ dec_instr (enci  ++ rest) = (INR i , rest)
Proof
  ho_match_mp_tac enc_instr_ind
  cheat
QED *)


(*
Theorem dec_enc_instr:
  ∀i enci rest. enc_instr i = SOME enci ⇒
  dec_instr (enci ++ rest) = (INR i, rest)
Proof

  Cases >> rpt gen_tac
  >> rw[Once enc_instr_def]
  >- simp $ ssaa [Once dec_instr_def]
  >- simp $ ssaa [Once dec_instr_def]
  >-
  gvs $ ssaa [Once dec_instr_def]
gvs


  strip_tac
 simp[]
QED



(* askyk *)
Theorem dec_enc_expr:
  ∀is encis rest. enc_expr is = SOME encis ⇒
  dec_expr (encis ++ rest) = (INR is, rest)
Proof

  Induct >> rpt gen_tac
  >> gvs[Once enc_instr_def, dec_instr_def]
  \\ rpt strip_tac
  \\ gvs ssa
  \\ rewrite_tac[dec_instr_def]

  \\ last_assum drule
  \\ rpt strip_tac
  (* \\ gvs[AllCaseEqs()] *)

  \\ imp_res_tac enc_instr_nEmp
  (* what now? How to make this more managable *)
\\ cheat
(*
  \\ simp[dec_instr_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ cheat
  (* what now? How to make this more managable *)
*)
QED
 *)


(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)
(*
Theorem dec_enc_global[simp]:
  ∀g encg rs.
    enc_global g = SOME encg ⇒
    dec_global $ encg ++ rs = (INR g, rs)
Proof

     rpt gen_tac
  \\ simp[enc_global_def, dec_global_def, AllCaseEqs()]
  \\ rpt strip_tac
  >> Cases_on `g.gtype` >> gvs[enc_globaltype_def]
    >> simp $ ssaa [dec_globaltype_def]


drule dec
rpt strip_tac
    simp[]
    >> rw $ ssaa [dec_globaltype_def]


    rw[]
  \\ simp[]
], enc_globaltype_def]
  \\ Cases_on ‘g.gtype’ >> Cases_on  `g.ginit`
    >> gvs[]
\\
  cheat
QED *)

Theorem enc_u32_nEmp:
  ∀w. ¬ (NULL $ enc_u32 w)
Proof
  gen_tac
  \\ rw[enc_unsigned_word_def, Once enc_num_def]
QED

Theorem enc_u32_nEmp':
  ∀w. (NULL $ enc_u32 w) ⇒ F
Proof
  gen_tac
  \\ rw[enc_unsigned_word_def, Once enc_num_def]
QED


(* ASKYK *)
(* Theorem dec_enc_code:
  ∀cd encC rs.
    enc_code cd = SOME encC ⇒
    dec_code $ encC ++ rs = (INR cd, rs)
Proof

  PairCases
  \\ rw[enc_code_def, AllCaseEqs(), dec_code_def]
  >-( mp_tac enc_u32_nEmp \\ simp[] )
  \\ rewrite_tac[GSYM APPEND_ASSOC, dec_enc_u32]
  \\ gvs[]
  \\ dxrule dec_enc_vector


  \\ disch_then $ qspec_tac `dec_valtype` assume_tac



  \\ qspec_tac `dec_valtype` assume_tac dec_enc_valtype_Seq
assume_tac dec_enc_valtype_Seq

  \\ pop_assum mp_tac
  \\ Cases_on `cd0` >> gvs[enc_vector_def]
rpt strip_tac
gvs[]


  \\ rw[]


  \\ rpt strip_tac
gvs[]
  \\ simp ssa


  \\ rpt strip_tac
  \\ pop_assum kall_tac
  \\ sass
  \\ disch_then (fn thm => DEP_REWRITE_TAC [thm])
  \\ rw[dec_enc_valtype_Seq]
  \\ cheat
QED *)

(* ASKYK *)
Theorem dec_enc_data:
  ∀dt encD rs.
    enc_data dt = SOME encD ⇒
    dec_data $ encD ++ rs = (INR dt, rs)
Proof
  Cases_on `dt` >> Cases_on `l` >> Cases_on `l0` >> gvs[]
  \\ rpt gen_tac
  \\ gvs[enc_data_def, enc_vector_def, Once enc_instr_def]
  (* \\ simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", dec_data_def] *)
  \\
  cheat
QED

(*
Theorem dec_enc_section:
  dec_section ??? enc_section lb contents ++ rs =
T
Proof
  cheat
QED

Theorem dec_enc_module:
  ∀mod encM rs.
    enc_data mod = SOME encM ⇒
    dec_data $ encM ++ rs = (INR mod, rs)
T
Proof
  cheat
QED *)


(***************)
(*             *)
(*     WIP     *)
(*             *)
(***************)

(* Theorem check_len_IMP_INL:
  check_len bs xs = (INL x,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs
Proof
  PairCases_on ‘xs’
  \\ rw [check_len_def]
  \\ Cases_on ‘xs0’
    >> gvs [check_len_def,AllCaseEqs()]
QED

Triviality check_len_INR:
  check_len bs0 y = (INR x,bs1) ⇒ ∃y1 y2. y = (INR y1,y2)
Proof
  gvs [oneline check_len_def, AllCaseEqs()] \\ rw [] \\ fs []
QED

Triviality check_len_INL:
  check_len bs0 y = (INL x,bs1) ⇒ ∃y1 y2. y = (INL y1,y2)
Proof
  gvs [oneline check_len_def, AllCaseEqs()] \\ rw [] \\ fs []
QED *)


(*
(* ASKYK *)
Theorem dec_instr_shortens:
  (∀bs x bs1. dec_instr      bs = (INR x,bs1) ⇒ LENGTH bs1 < LENGTH bs) ∧
  (∀bs x bs1. dec_instr_list bs = (INR x,bs1) ⇒ LENGTH bs1 < LENGTH bs)
Proof
  ho_match_mp_tac dec_instr_ind \\ rw []
  >~ [‘dec_instr      []’] >- simp [dec_instr_def]
  >~ [‘dec_instr_list []’] >- simp [dec_instr_def]
    >> pop_assum mp_tac
    >> simp [Once dec_instr_def]
    >> strip_tac
      >> gvs [AllCaseEqs()]
      >> imp_res_tac dec_u32_shortens \\ fs[]
      >> imp_res_tac dec_blocktype_shortens \\ fs []
      >> imp_res_tac dec_indxs_shortens \\ fs[]
      >> cheat
  (*
      >> imp_res_tac check_len_INL \\ fs []
      >> imp_res_tac check_len_INR \\ fs []
      >> gvs [check_len_def]
      >> imp_res_tac dec_u32_shortens
      >>~ [‘dec_u32’]
        >> TRY (drule dec_u32_shortens     )
        >> TRY (drule dec_indxs_shortens   )
        >> TRY (drule dec_functype_shortens)
        >> simp[]
        >>
        cheat *)
QED

Theorem dec_instr_INL_length:
  (∀bs x bs1. dec_instr      bs = (INL x,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs) ∧
  (∀bs x bs1. dec_instr_list bs = (INL x,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs)
Proof
  ho_match_mp_tac dec_instr_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once dec_instr_def]
  \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac dec_blocktype_shortens \\ gvs []
  \\ imp_res_tac check_len_IMP_INL \\ gvs []
  \\ imp_res_tac check_len_INR \\ fs []
  \\ imp_res_tac check_len_IMP \\ fs []
  \\ cheat (* not implemented cases *)
QED

Theorem check_len_thm:
  check_len bs (dec_instr bs) = dec_instr bs ∧
  check_len bs (dec_instr_list bs) = dec_instr_list bs
Proof
  conj_tac
  >-
   (Cases_on ‘dec_instr bs’ \\ fs []
    \\ Cases_on ‘q’ \\ fs [check_len_def]
    \\ imp_res_tac dec_instr_INL_length \\ fs []
    \\ imp_res_tac dec_instr_shortens \\ fs [])
  \\ Cases_on ‘dec_instr_list bs’ \\ fs []
  \\ Cases_on ‘q’ \\ fs [check_len_def]
  \\ imp_res_tac dec_instr_INL_length \\ fs []
  \\ imp_res_tac dec_instr_shortens \\ fs []
QED

Theorem dec_instr_def[allow_rebind] = REWRITE_RULE [check_len_thm] dec_instr_def;
Theorem dec_instr_ind[allow_rebind] = REWRITE_RULE [check_len_thm] dec_instr_ind;

Theorem enc_instr_not_end:
  ∀i b. ∃h t. enc_instr i = SOME $ h::t ∧ h ≠ 0x0Bw
Proof
  Cases \\ simp [Once enc_instr_def]
  >~ [‘enc_varI’  ] >- (simp [enc_varI_def  ] \\ every_case_tac \\ fs [])
  >~ [‘enc_paraI’ ] >- (simp [enc_paraI_def ] \\ every_case_tac \\ fs [])
  >~ [‘enc_numI’  ] >- (simp [enc_numI_def  ] \\ every_case_tac \\ fs [])
  >~ [‘enc_loadI’ ] >- (simp [enc_loadI_def ] \\ every_case_tac \\ fs [])
  >~ [‘enc_storeI’] >- (simp [enc_storeI_def] \\ every_case_tac \\ fs [])
  \\ cheat
QED

(* Theorem dec_enc_instr:
  (∀i rest. dec_instr (enc_instr i ++ rest) = (INR i,rest)) ∧
  (∀is rest. dec_instr_list (enc_instr_list is ++ rest) = (INR is,rest))
Proof
  ho_match_mp_tac enc_instr_ind \\ reverse $ rw []
  \\ once_rewrite_tac [enc_instr_def]
  >- (rename [‘enc_instr i’]
      \\ qspec_then ‘i’ strip_assume_tac enc_instr_not_end \\ fs []
      \\ simp [Once dec_instr_def]
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC] \\ simp [])
  >- simp [dec_instr_def]
  \\ Cases_on ‘i’ \\ fs []
  >~ [‘Unreachable’] >- (simp [dec_instr_def])
  >~ [‘Nop’] >- (simp [dec_instr_def])
  >~ [‘Block’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp [])
  >~ [‘Loop’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp [])
  >~ [‘If g b1 b2’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp []
    \\ Cases_on ‘b2’ \\ simp []
    \\ asm_rewrite_tac [GSYM APPEND_ASSOC] \\ simp [])
  \\ cheat (* not yet implemented cases *)
QED *)
*)
