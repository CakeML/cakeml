(* Example of the infinite program yes. *)
        
Theory yes
Ancestors
  itreeTau panLang panSem
  pan_itreeSem pan_itreeProps
  panItreeAbsSem
  panPtreeConversion
  alignment wordLang ffi misc
Libs
  preamble stringSyntax numSyntax
  stringLib sumSyntax
  HolKernel boolLib bossLib
  listSyntax mlstringLib optionSyntax
  simpLib panItreeDecompilerLib



val _ = set_trace "notify type variable guesses" 0;


(* Extension of itreeTauTheory *)
val _ = monadsyntax.enable_monadsyntax();
val _ = declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
                      ignorebind = NONE,
                      choice = NONE,
                      fail = NONE,
                      guard = NONE});
val _ = enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;


                                                   
fun read_file fname = let
    val s = TextIO.openIn fname
    fun get ss = case TextIO.inputLine s of
        SOME str => get (str :: ss)
      | NONE => rev ss
  in concat (get []) end


(** Copied from panPtreeConversion *)
fun parse_pancake_code word_ty str =
  let
    val parse_topdecs_to_ast_s = inst [alpha |-> word_ty] “parse_topdecs_to_ast”
    val thm = EVAL (mk_comb (parse_topdecs_to_ast_s, stringLib.fromMLstring str))
    val r = rhs (concl thm)
  in
    if sumSyntax.is_inl r
    then (fst (sumSyntax.dest_inl r), thm)
    else failwith ("parse_pancake_code: failed to EVAL")
  end


fun parse_pancake_file word_ty fname =
  parse_pancake_code word_ty (read_file fname)

                     

val (yes_topdecs, _) = parse_pancake_file “:32” "yes.pnk"

val yes_fundecs = topdecs_to_fundecs yes_topdecs

val yes_result = decompile_2_reduce "yes" [] yes_fundecs


val yes_while = List.nth (fst yes_result, 0) |> (fn (x, y, z) => hd y)
                                                 |> SIMP_RULE (srw_ss ()) [read_bytearray_def]

val yes_shallow = List.nth (fst yes_result, 0) |> (fn (x, y, z) => x)

Theorem event_satisfy_Tau:
  event_satisfy P (Tau t) ⇔ event_satisfy P t
Proof
  iff_tac
  \\ gvs[event_satisfy_rules]
  \\ strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once event_satisfy_cases]
  \\ gvs[]
QED
    
Theorem event_satisfy_FUNPOW:
  event_satisfy P (FUNPOW Tau n t) ⇔ event_satisfy P t
Proof
  Induct_on ‘n’
  \\ gvs[FUNPOW_SUC, event_satisfy_Tau]
QED

    
Theorem itree_wbisim_impl_event_satisfy:
  t ≈ t' ⇒ event_satisfy P t ⇒ event_satisfy P t'
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘λx. ∃t'. x ≈ t' ∧ event_satisfy P t'’
  \\ rw[]
  >- metis_tac[itree_wbisim_sym]
  \\ Cases_on ‘a0’ \\ gvs[]
  >- metis_tac[itree_wbisim_sym]
  \\ qpat_x_assum ‘Vis _ _ ≈ _’ $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[strip_tau_FUNPOW_cancel, event_satisfy_FUNPOW]
  \\ drule_then assume_tac $ iffLR event_satisfy_cases
  \\ gvs[]
  \\ metis_tac[]
QED

    
Theorem yes_while_1_safety:
  read_bytearray 0w 4 (mem_load_byte s.memory s.memaddrs s.be) = SOME x ⇒
  event_satisfy (λe. ∃x'. e = (ExtCall «putChar», x, x')) (yes_while_1 s)
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘λt. (∃s. t ≈ yes_while_1 s ∧ read_bytearray 0w 4 (mem_load_byte s.memory s.memaddrs s.be) = SOME x) ∨ ∃v. t ≈ Ret v’
  \\ rw[]
  >- metis_tac[itree_wbisim_refl]
  >- (Cases_on ‘a0’
      >- metis_tac[]
      >- (gvs[]
          \\ metis_tac[]
         )
      \\ assume_tac yes_while
      \\ pop_assum $ qspec_then ‘s'’ assume_tac
      \\ gvs[]
      \\ rev_dxrule_then (dxrule_then assume_tac) itree_wbisim_trans
      \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ gvs[]
      \\ rpt strip_tac
      \\ pop_assum $ qspec_then ‘r’ assume_tac \\ gvs[]
      \\ EVERY_CASE_TAC \\ gvs[]
      >- metis_tac[]
      >- (disj1_tac
          \\ qpat_x_assum ‘_ ≈ _’ $ irule_at Any
          \\ rw[write_bytearray_def]
         )
      >- metis_tac[]
      \\ metis_tac[]
     )
  \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[]
  \\ Cases_on ‘n’ \\ gvs[FUNPOW_SUC]
  \\ disj2_tac
  \\ metis_tac[itree_wbisim_sym, FUNPOW_Tau_wbisim]
QED


Theorem yes_safety:
  0w ∈ s.memaddrs ⇒
  event_satisfy (λe. ∃x'. e = (ExtCall «putChar», word_to_bytes (121w:word32) s.be, x')) (yes_body [] s)
Proof
  rpt strip_tac
  \\ assume_tac yes_shallow
  \\ pop_assum $ qspec_then ‘s’ assume_tac
  \\ gvs[]
  \\ irule itree_wbisim_impl_event_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ pop_assum $ irule_at Any
  \\ irule event_satisfy_bind
  \\ conj_tac
  >- (strip_tac
      \\ rw[]
      \\ EVERY_CASE_TAC \\ gvs[event_satisfy_rules]
     )
  \\ irule yes_while_1_safety
  \\ rw[read_bytearray_compute, mem_load_byte_def, byte_align_extract]
  \\ Cases_on ‘s.be’ \\ gvs[word_to_bytes_def, word_to_bytes_aux_compute, get_byte_def]
QED


CoInductive branch_satisfy:
  (P_k (Ret v) ⇒ branch_satisfy P_e_res P_k (Ret v)) ∧
  (P_k (Tau t) ∧ branch_satisfy P_e_res P_k t ⇒ branch_satisfy P_e_res P_k (Tau t)) ∧
  (∀r. P_k (Vis e k) ∧ P_e_res e r ∧ branch_satisfy P_e_res P_k (k r) ⇒ branch_satisfy P_e_res P_k (Vis e k))
End


Theorem branch_satisfy_Tau:
  branch_satisfy P_e_res P_k (Tau t) ⇔ P_k (Tau t) ∧ branch_satisfy P_e_res P_k t
Proof
  iff_tac
  \\ gvs[branch_satisfy_rules]
  \\ strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
  \\ gvs[]
QED
    
Theorem branch_satisfy_FUNPOW:
  ∀t. branch_satisfy P_e_res P_k (FUNPOW Tau n t) ⇔ (∀n'. n' ≤ n ⇒ P_k (FUNPOW Tau n' t)) ∧ branch_satisfy P_e_res P_k t
Proof
  Induct_on ‘n’
  \\ gvs[FUNPOW_SUC, branch_satisfy_Tau]
  \\ rpt strip_tac
  >- (iff_tac
      \\ rpt strip_tac
      >- (pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
          \\ gvs[]
         )
      \\ pop_assum $ irule
     )
  \\ iff_tac
  >- (rpt strip_tac
      >- (Cases_on ‘n'’ \\ gvs[FUNPOW, GSYM FUNPOW_SUC]
          \\ ‘branch_satisfy P_e_res P_k (Tau (FUNPOW Tau n t))’ by rw[branch_satisfy_Tau, GSYM FUNPOW_SUC, FUNPOW]
          \\ pop_assum $ assume_tac o SRULE[GSYM FUNPOW_SUC, FUNPOW]
          \\ last_x_assum $ qspec_then ‘Tau t’ assume_tac
          \\ gvs[]
         )
      \\ pop_assum $ irule
     )
  \\ rw[GSYM FUNPOW_SUC]
QED
        
Theorem itree_wbisim_impl_branch_satisfy:
  t ≈ t' ⇒ (∀t t'. t ≈ t' ⇒ P_k t = P_k t') ⇒ branch_satisfy P_e_res P_k t ⇒ branch_satisfy P_e_res P_k t'
Proof
  rpt strip_tac
  \\ irule branch_satisfy_coind
  \\ qexists ‘λx. ∃t'. x ≈ t' ∧ branch_satisfy P_e_res P_k t'’
  \\ rw[]
  >- metis_tac[itree_wbisim_sym]
  \\ Cases_on ‘a0’ \\ gvs[]
  >- (qpat_x_assum ‘Ret __ ≈ _’ $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ imp_res_tac strip_tau_FUNPOW
      \\ gvs[branch_satisfy_FUNPOW, strip_tau_FUNPOW_cancel]
      \\ pop_assum $ irule o SRULE[Once branch_satisfy_cases]
     )
  >- (conj_tac
      >- (pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
          \\ first_x_assum $ qspecl_then [‘Tau u’, ‘t''’] assume_tac
          \\ gvs[]
         )
      \\ metis_tac[]
     )
  \\ qpat_x_assum ‘Vis _ _ ≈ _’ $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[strip_tau_FUNPOW_cancel, branch_satisfy_FUNPOW]
  \\ drule_then assume_tac $ iffLR branch_satisfy_cases
  \\ gvs[]
  \\ qexists ‘r’ \\ rw[]
  >- (last_x_assum $ qspecl_then [‘Vis a g’, ‘Vis a k'’] assume_tac
      \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ gvs[]
     )
  \\ metis_tac[]
QED

Theorem itree_wbisim_nonret_bind_nonret:
  (∀v. ¬(t ≈ Ret v)) ⇒ (∀v. ¬(t >>= k ≈ Ret v))
Proof
  rpt strip_tac
  \\ dxrule_then assume_tac itree_wbisim_Ret_FUNPOW
  \\ gvs[]
  \\ pop_assum $ assume_tac o SRULE[Once itree_bind_cases]
  \\ gvs[]
  >- (‘FUNPOW Tau n' (Ret r) ≈ Ret r’ by metis_tac[FUNPOW_Tau_wbisim, itree_wbisim_sym]
      \\ gvs[]
     )
  \\ gvs[FUNPOW_Ret_spin_F]
QED

Theorem branch_satisfy_non_ret_bind:
  (∀t' k. (∀v. P_k t' ⇒ ¬(t' ≈ Ret v)) ∧ (P_k t' ⇒ P_k (t' >>= k))) ⇒ branch_satisfy P_e_res P_k t ⇒ branch_satisfy P_e_res P_k (t >>= k)
Proof
  rpt strip_tac
  \\ irule branch_satisfy_coind
  \\ qexists ‘λt'. ∃t k. t' = t >>= k ∧ branch_satisfy P_e_res P_k t ∧ (∀v. ¬(t' ≈ Ret v))’ \\ rw[]
  >- (pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
      \\ gvs[]
      >- (first_x_assum $ qspec_then ‘Ret v’ assume_tac
          \\ gvs[]
          \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
          \\ rw[]
         )
      >- (qexistsl [‘Tau t'’, ‘k’]
          \\ rw[branch_satisfy_Tau]
         )
      >- (qexistsl [‘Vis e k'’, ‘k’]
          \\ rw[Once branch_satisfy_cases]
          \\ metis_tac[]
         )
     )
  \\ Cases_on ‘t'’
  >- (qpat_x_assum ‘branch_satisfy _ _ (Ret _)’ $ assume_tac o SRULE[Once branch_satisfy_cases]
      \\ res_tac
      \\ qpat_x_assum ‘∀_. ¬_’ $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ gvs[]
     )
  >- (gvs[itree_bind_thm, branch_satisfy_Tau]
      \\ last_x_assum $ qspecl_then [‘Tau u’, ‘k’] assume_tac
      \\ gvs[]
      \\ qexistsl [‘u’, ‘k’]
      \\ rw[itree_wbisim_nonret_bind_nonret]
     )
  \\ qpat_x_assum ‘branch_satisfy _ _ (Vis _ _)’ $ assume_tac o SRULE[Once branch_satisfy_cases]
  \\ gvs[itree_bind_thm]
  \\ last_assum $ qspecl_then [‘Vis a g’, ‘k’] (assume_tac o SRULE[])
  \\ gvs[]
  \\ qexists ‘r’ \\ rw[]
  \\ qexistsl [‘g r’, ‘k’]
  \\ rw[]
  \\ qpat_x_assum ‘branch_satisfy _ _ (_ _)’ $ assume_tac o SRULE[Once branch_satisfy_cases]
  \\ gvs[itree_wbisim_nonret_bind_nonret]
QED

Theorem yes_while_1_liveness:
  read_bytearray 0w 4 (mem_load_byte s.memory s.memaddrs s.be) = SOME x ⇒
  branch_satisfy (λe res. ∃x'. e = (ExtCall «putChar», x, x') ⇒ (∃new_bytes. res = INL (INR new_bytes) ∧ LENGTH new_bytes = LENGTH x'))
                 (λt. ∃x' k'. t ≈ Vis (ExtCall «putChar», x, x') k') (yes_while_1 s)
Proof
  rpt strip_tac
  \\ irule branch_satisfy_coind
  \\ qexists ‘λt. (∃s. t ≈ yes_while_1 s ∧ read_bytearray 0w 4 (mem_load_byte s.memory s.memaddrs s.be) = SOME x)’
  \\ rw[]
  >- metis_tac[itree_wbisim_refl]
  \\ assume_tac yes_while
  \\ pop_assum $ qspec_then ‘s'’ assume_tac \\ gvs[]
  \\ rev_dxrule_then (drule_then assume_tac) itree_wbisim_trans
  \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[strip_tau_FUNPOW_cancel, write_bytearray_def]
  \\ ‘s' with memory := s'.memory = s'’ by rw[bstate_component_equality]
  \\ gvs[]
  \\ Cases_on ‘n’ \\ rw[]
  >- (qexists ‘INL (INR [])’ \\ gvs[]
      \\ first_x_assum $ qspec_then ‘INL (INR [])’ assume_tac \\ gvs[]
      \\ reverse $ conj_tac
      >- (pop_assum $ irule_at Any
          \\ rw[write_bytearray_def]
         )
      \\ metis_tac[itree_wbisim_refl]
     )
  \\ rw[FUNPOW_SUC]
  >- (irule_at Any itree_wbisim_trans
      \\ irule_at Any FUNPOW_Tau_wbisim
      \\ metis_tac[itree_wbisim_refl]
     )
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any FUNPOW_Tau_wbisim
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any itree_wbisim_trans
  \\ first_assum $ irule_at (Pos hd)
  \\ rw[Once itree_wbisim_cases]
  \\ irule itree_wbisim_sym
  \\ first_assum $ irule_at Any
QED


Theorem yes2_liveness:
  0w ∈ s.memaddrs ⇒
  branch_satisfy (λe res. ∃x'. e = (ExtCall «putChar», word_to_bytes (121w:word32) s.be, x') ⇒
                               (∃new_bytes. res = INL (INR new_bytes) ∧ LENGTH new_bytes = LENGTH x'))
                 (λt. ∃x' k'. t ≈ Vis (ExtCall «putChar», word_to_bytes (121w:word32) s.be, x') k') (yes_body [] s)
Proof
  rpt strip_tac
  \\ irule itree_wbisim_impl_branch_satisfy
  \\ rw[]
  >- (iff_tac
      \\ rpt strip_tac
      >- (rev_dxrule_then assume_tac itree_wbisim_sym
          \\ drule_then (dxrule_then assume_tac) itree_wbisim_trans
          \\ metis_tac[]
         )
      \\ rev_drule_then (dxrule_then assume_tac) itree_wbisim_trans
      \\ metis_tac[]
     )
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any yes_shallow
  \\ gvs[]
  \\ irule branch_satisfy_non_ret_bind
  \\ irule_at Any yes_while_1_liveness
  \\ rw[read_bytearray_compute, mem_load_byte_def, byte_align_extract]
  >- (Cases_on ‘s.be’ \\ gvs[word_to_bytes_def, word_to_bytes_aux_compute, get_byte_def]
     )
  >- (CCONTR_TAC
      \\ gvs[]
      \\ dxrule_then assume_tac itree_wbisim_sym
      \\ dxrule_then (dxrule_then assume_tac) itree_wbisim_trans
      \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ rw[]
     )
  \\ rpt strip_tac
  \\qexistsl [‘x'’, ‘λx. k' x >>= k’]
  \\ PURE_ONCE_REWRITE_TAC[(cj 3 (GSYM itree_bind_thm))]
  \\ irule itree_bind_resp_t_wbisim
  \\ pop_assum $ irule
QED
