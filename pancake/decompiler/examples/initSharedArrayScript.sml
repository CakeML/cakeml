(* Example on program dealing with shared memory *)
        
Theory initSharedArray
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

                     

val (initSharedArray_topdecs, _) = parse_pancake_file “:32” "initSharedArray.pnk"

val initSharedArray_fundecs = topdecs_to_fundecs initSharedArray_topdecs

val initSharedArray_result = decompile_2_reduce "initSharedArray" [] initSharedArray_fundecs





                                                                  

Theorem itree_bind_resp_wbisim_compose_intro:
  t ≈ t' ⇒ (∀r. k r ≈ k' r) ⇒ t'' = t' >>= k' ⇒ t >>= k ≈ t''
Proof
  rw[]
  \\ irule itree_bind_resp_wbisim
  \\ gvs[]
QED

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

CoInductive branch_satisfy:
  (P_k (Ret v) ⇒ branch_satisfy P_e_res P_k (Ret v)) ∧
  (branch_satisfy P_e_res P_k t ⇒ branch_satisfy P_e_res P_k (Tau t)) ∧
  (∀r. P_e_res e r ∧ P_k (k r) ∧ branch_satisfy P_e_res P_k (k r) ⇒ branch_satisfy P_e_res P_k (Vis e k))
End


Theorem branch_satisfy_Tau:
  branch_satisfy P_e_res P_k (Tau t) ⇔ branch_satisfy P_e_res P_k t
Proof
  iff_tac
  \\ gvs[branch_satisfy_rules]
  \\ strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
  \\ gvs[]
QED
    
Theorem branch_satisfy_FUNPOW:
  branch_satisfy P_e_res P_k (FUNPOW Tau n t) ⇔ branch_satisfy P_e_res P_k  t
Proof
  Induct_on ‘n’
  \\ gvs[FUNPOW_SUC, branch_satisfy_Tau]
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
  >- metis_tac[]
  \\ qpat_x_assum ‘Vis _ _ ≈ _’ $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[strip_tau_FUNPOW_cancel, branch_satisfy_FUNPOW]
  \\ drule_then assume_tac $ iffLR branch_satisfy_cases
  \\ gvs[]
  \\ metis_tac[]
QED

Theorem branch_satisfy_non_ret_bind:
  (∀t' v k. (P_k t' ⇒ ¬(t' ≈ Ret v)) ∧ (P_k t' ⇒ P_k (t' >>= k))) ⇒ branch_satisfy P_e_res P_k t ⇒ branch_satisfy P_e_res P_k (t >>= k)
Proof
  rpt strip_tac
  \\ irule branch_satisfy_coind
  \\ qexists ‘λt'. ∃t k. t' = t >>= k ∧ branch_satisfy P_e_res P_k t’ \\ rw[]
  >- metis_tac[]
  \\ Cases_on ‘t'’
  >- (pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
      \\ res_tac
      \\ qpat_x_assum ‘∀_. ¬_’ $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ gvs[]
     )
  >- (gvs[itree_bind_thm, branch_satisfy_Tau]
      \\ metis_tac[]
     )
  \\ pop_assum $ assume_tac o SRULE[Once branch_satisfy_cases]
  \\ gvs[itree_bind_thm]
  \\ metis_tac[]
QED
                                                                       
Inductive w_list:
  ((~ (i:'a word < x)) ⇒ w_list i x []) ∧
  (((i:'a word < x) ∧ w_list (i + 1w) x l) ⇒ w_list i x (i :: l))
End

Inductive branch_terminate_satisfy:
  (P_r v ⇒ branch_terminate_satisfy P_e_res P_r (Ret v)) ∧
  (branch_terminate_satisfy P_e_res P_r t ⇒ branch_terminate_satisfy P_e_res P_r (Tau t)) ∧
  (∀res. P_e_res e res ∧ branch_terminate_satisfy P_e_res P_r (k res) ⇒ branch_terminate_satisfy P_e_res P_r (Vis e k))
End


Theorem branch_terminate_satisfy_Tau:
  branch_terminate_satisfy P_e_res P_r (Tau t) ⇔ branch_terminate_satisfy P_e_res P_r t
Proof
  iff_tac
  \\ gvs[branch_terminate_satisfy_rules]
  \\ strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once branch_terminate_satisfy_cases]
  \\ gvs[]
QED

Theorem branch_terminate_satisfy_Ret:
  branch_terminate_satisfy P_e_res P_r (Ret v) ⇔ P_r v
Proof
  iff_tac
  \\ gvs[branch_terminate_satisfy_rules]
  \\ strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once branch_terminate_satisfy_cases]
  \\ gvs[]
QED
    
Theorem branch_terminate_satisfy_FUNPOW:
  branch_terminate_satisfy P_e_res P_r (FUNPOW Tau n t) ⇔ branch_terminate_satisfy P_e_res P_r  t
Proof
  Induct_on ‘n’
  \\ gvs[FUNPOW_SUC, branch_terminate_satisfy_Tau]
QED

Theorem itree_wbisim_impl_branch_terminate_satisfy:
  ∀t.
    branch_terminate_satisfy P_e_res P_r t ⇒
    ∀t'. t ≈ t' ⇒ branch_terminate_satisfy P_e_res P_r t'
Proof
  ho_match_mp_tac branch_terminate_satisfy_ind
  \\ rpt strip_tac
  >- (pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
      \\ imp_res_tac strip_tau_FUNPOW
      \\ gvs[branch_terminate_satisfy_FUNPOW]
      \\ irule $ cj 1 branch_terminate_satisfy_rules
      \\ last_assum $ irule
     )
  >- gvs[]
  \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[]
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[strip_tau_FUNPOW_cancel, branch_terminate_satisfy_FUNPOW]
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ first_assum $ irule_at Any
  \\ metis_tac[]
QED

Theorem branch_terminate_satisfy_ret_cond_impl:
  ∀t.
    branch_terminate_satisfy P_e_res P_r t ⇒
    (∀r. P_r r ⇒ P_r' r) ⇒ branch_terminate_satisfy P_e_res P_r' t
Proof
  ho_match_mp_tac branch_terminate_satisfy_ind
  \\ rpt strip_tac
  >- (irule $ cj 1 branch_terminate_satisfy_rules
      \\ gvs[]
     )
  >- (irule $ cj 2 branch_terminate_satisfy_rules
      \\ gvs[]
     )
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ metis_tac[]
QED

Theorem branch_terminate_satisfy_branch_cond_impl:
  ∀t.
    branch_terminate_satisfy P_e_res P_r t ⇒
    (∀e res. P_e_res e res ⇒ P_e_res' e res) ⇒ branch_terminate_satisfy P_e_res' P_r t
Proof
  ho_match_mp_tac branch_terminate_satisfy_ind
  \\ rpt strip_tac
  >- (irule $ cj 1 branch_terminate_satisfy_rules
      \\ gvs[]
     )
  >- (irule $ cj 2 branch_terminate_satisfy_rules
      \\ gvs[]
     )
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ metis_tac[]
QED


Theorem branch_terminate_satisfy_bind:
  ∀t.
    branch_terminate_satisfy P_e_res P_r t ⇒
    (∀r. P_r r ⇒ branch_terminate_satisfy P_e_res P_k_r (k r)) ⇒ branch_terminate_satisfy P_e_res P_k_r (t >>= k)
Proof
  ho_match_mp_tac branch_terminate_satisfy_ind
  \\ rw[itree_bind_thm]
  >- (irule $ cj 2 branch_terminate_satisfy_rules
      \\ gvs[]
     )
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ metis_tac[]
QED

        
Theorem exists_list_LENGTH:
  ∃x. LENGTH x = n
Proof
  Induct_on ‘n’
  \\ rw[]
  \\ qexists ‘ARB::x’
  \\ rw[]
QED


Theorem word_plus_one_le:
  x < y ⇒ x + 1w ≤ y
Proof
  qspec_then `w2n (x + 1w)` mp_tac (GEN_ALL wordsTheory.word_msb_n2w_numeric)
  \\ qspec_then `w2n x` mp_tac (GEN_ALL wordsTheory.word_msb_n2w_numeric)
  \\ simp [w2n_lt]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ qspec_then `y` mp_tac w2n_lt
  \\ rw [] \\ fs [WORD_LE, WORD_LT, wordsTheory.w2n_minus1]
  \\ fs []
QED


val [init_sh_array_while] = List.nth (fst initSharedArray_result, 0) |> (fn (x,y,z) => y)

val init_sh_array_shallow = List.nth (fst initSharedArray_result, 0) |> (fn (x,y,z) => x)
     
        
Theorem ret_satisfy_init_shared_while:
  ∀curr_i len base_addr s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ⇒
    let
      s' = if ¬(curr_i < len) then s else s with locals := s.locals |+ («i», ValWord len)
    in
      ret_satisfy (λx.
                     ∃rv s''.
                       x = INR (rv,s'') ∧
                       (rv = NONE ⇒ s'' = s')
                       ∧ (rv = NONE ∨ rv = SOME Error ∨ ∃ffe. rv = SOME (FinalFFI ffe)))
                  (init_shared_array_while_0 s)
Proof
  Induct_on ‘w_arr’
  >- (simp[Once w_list_cases]
      \\ rw[]
      \\ assume_tac $ cj 1 init_sh_array_while
      \\ first_x_assum $ qspecl_then [‘s’] assume_tac
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind,  word_of_val_def, FUPDATE_LIST_THM]
      \\ irule ret_satisfy_wbisim_impl
      \\ irule_at Any itree_wbisim_sym
      \\ pop_assum $ irule_at Any
      \\ rw[ret_satisfy_Ret]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
  \\ gvs[]
  \\ assume_tac $ cj 2 init_sh_array_while
  \\ first_x_assum $ qspecl_then [‘s’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM]
  \\ irule ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ pop_assum $ irule_at Any
  \\ rw[ret_satisfy_Ret, ret_satisfy_Vis, ret_satisfy_Tau]
  \\ EVERY_CASE_TAC \\ rw[ret_satisfy_Ret, ret_satisfy_Vis, ret_satisfy_Tau]
  \\ irule ret_satisfy_strengthen
  \\ last_x_assum $ irule_at Any
  \\ gvs[FLOOKUP_SIMP]
  \\ rpt strip_tac
  \\ FULL_CASE_TAC
  >- (dxrule_then assume_tac $ iffLR WORD_NOT_LESS
      \\ dxrule_then assume_tac word_plus_one_le
      \\ dxrule_all WORD_LESS_EQUAL_ANTISYM
      \\ strip_tac
      \\ rw[]
     )
  \\ gvs[]
QED

Theorem ret_satisfy_init_shared_array:
  ∀curr_i len base_addr s.
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr)  ⇒
      ret_satisfy (λx.
                     ∃rv s''.
                       x = INR (rv,s'') ∧
                       (rv = SOME (Return (ValWord 0w)) ⇒ s'' = s with locals := FEMPTY)
                       ∧ (rv = SOME (Return (ValWord 0w)) ∨ rv = SOME Error ∨ ∃ffe. rv = SOME (FinalFFI ffe)))
                  (init_shared_array_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ irule ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any init_sh_array_shallow
  \\ irule_at Any ret_satisfy_impl_bind_impl
  \\ irule_at Any $ SIMP_RULE (srw_ss ()) [LET_THM] ret_satisfy_init_shared_while
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind,  word_of_val_def, FUPDATE_LIST_THM]
  \\ last_assum $ irule_at Any
  \\ rw[ret_satisfy_Ret]
  \\ FULL_CASE_TAC \\ rw[ret_satisfy_Ret]
QED

Theorem init_sh_array_while_correctness:
  ∀curr_i base_addr s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    (∀i. MEM i w_arr ⇒ LENGTH (nb_func (SharedMem MappedWrite,[0w],
                                      word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) =
                     LENGTH (word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) ⇒
    let
      s' = if ¬(curr_i < len) then s else s with locals := s.locals |+ («i», ValWord len)
    in
    branch_terminate_satisfy (λe res. res = INL (INR (nb_func e)))
                   (λv. v = INR (NONE, s')) (init_shared_array_while_0 s)
Proof
  Induct_on ‘w_arr’
  >- (rpt strip_tac
      \\ gvs[Once w_list_cases]
      \\ irule itree_wbisim_impl_branch_terminate_satisfy
      \\ irule_at Any itree_wbisim_sym
      \\ irule_at Any $ cj 1 init_sh_array_while
      \\ rw[word_of_val_def]
      \\ irule $ cj 1 branch_terminate_satisfy_rules
      \\ rw[]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE[Once w_list_cases]
  \\ gvs[]
  \\ irule itree_wbisim_impl_branch_terminate_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any $ cj 2 init_sh_array_while
  \\ rw[word_of_val_def]
  \\ first_assum $ qspec_then ‘curr_i’ (assume_tac o SRULE[])
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ rw[]
  \\ irule branch_terminate_satisfy_ret_cond_impl
  \\ last_x_assum $ irule_at Any
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM]
  \\ FULL_CASE_TAC \\ gvs[]
  \\ dxrule_then assume_tac $ iffLR WORD_NOT_LESS
  \\ dxrule_then assume_tac word_plus_one_le
  \\ dxrule_all WORD_LESS_EQUAL_ANTISYM
  \\ strip_tac
  \\ rw[]
QED

Theorem init_sh_array_correctness:
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    (∀i. MEM i w_arr ⇒ LENGTH (nb_func (SharedMem MappedWrite,[0w],
                                        word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) =
                       LENGTH (word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) ⇒
    branch_terminate_satisfy (λe res. res = INL (INR (nb_func e)))
                             (λv. v = INR (SOME (Return (ValWord 0w)), s with locals := FEMPTY))
                             (init_shared_array_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ irule itree_wbisim_impl_branch_terminate_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any init_sh_array_shallow
  \\ irule branch_terminate_satisfy_bind
  \\ irule_at (Pos last) $ SIMP_RULE (srw_ss ()) [LET_THM] init_sh_array_while_correctness
  \\ last_assum $ irule_at Any
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM]
  \\ irule $ cj 1 branch_terminate_satisfy_rules
  \\ rw[]
QED
        
val [sum_sh_array_while] = List.nth (fst initSharedArray_result, 1) |> (fn (x,y,z) => y)

val sum_sh_array_shallow = List.nth (fst initSharedArray_result, 1) |> (fn (x,y,z) => x)

                                                                           
Theorem FOLDR_word_add_init_val:
  FOLDR $+ ((init_value:'a word) + extra) l = extra + FOLDR $+ init_value l
Proof
  Induct_on ‘l’ \\ rw[]
QED

Theorem sum_sh_array_while_correctness:
  ∀curr_i curr_tot base_addr s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «tot» = SOME (ValWord curr_tot) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    (∀i. MEM i w_arr ⇒ LENGTH (nb_func (SharedMem MappedRead,[0w],
                                        word_to_bytes (base_addr + 8w * i) F)) =
                       LENGTH (word_to_bytes (base_addr + 8w * i) F)) ⇒
    let
      s' = if ¬(curr_i < len) then
             s
           else
             s with locals :=
             res_var_list (s.locals
                            |+ («i», ValWord len)
                            |+ («tot», ValWord (FOLDR $+ curr_tot
                                                         (MAP (λaddr. word_of_bytes
                                                                      F 0w (nb_func (SharedMem MappedRead, [0w],
                                                                                     word_to_bytes (base_addr + 8w * addr) F))) w_arr))))
                          [(«x»,FLOOKUP s.locals «x»)]
    in
      branch_terminate_satisfy (λe res. res = INL (INR (nb_func e))) (λv. v = INR (NONE, s')) (sum_shared_array_while_0 s)
Proof
  Induct_on ‘w_arr’
  >- (simp[Once w_list_cases]
      \\ rw[]
      \\ irule itree_wbisim_impl_branch_terminate_satisfy
      \\ irule_at Any itree_wbisim_sym
      \\ irule_at Any $ cj 1 sum_sh_array_while
      \\ rw[word_of_val_def]
      \\ irule $ cj 1 branch_terminate_satisfy_rules
      \\ rw[]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE[Once w_list_cases]
  \\ gvs[]
  \\ irule itree_wbisim_impl_branch_terminate_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any $ cj 2 sum_sh_array_while
  \\ rw[word_of_val_def]
  >- (EVERY_CASE_TAC \\ gvs[]
     )
  \\ first_assum $ qspec_then ‘curr_i’ (assume_tac o SRULE[])
  \\ irule $ cj 3 branch_terminate_satisfy_rules
  \\ gvs[]
  \\ irule branch_terminate_satisfy_ret_cond_impl
  \\ last_x_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ Cases_on ‘FLOOKUP s.locals «x»’
  \\ qexistsl [‘curr_tot +
              word_of_bytes F 0w
                            (nb_func
                             (SharedMem MappedRead,[0w],
                              word_to_bytes (base_addr + 8w * curr_i) F))’, ‘base_addr’]
  \\ gvs[FLOOKUP_SIMP, eval_def, DOMSUB_FLOOKUP_THM, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ (FULL_CASE_TAC \\ gvs[]
      >- (dxrule_then assume_tac $ iffLR WORD_NOT_LESS
          \\ dxrule_then assume_tac word_plus_one_le
          \\ dxrule_all WORD_LESS_EQUAL_ANTISYM
          \\ strip_tac
          \\ rw[]
          \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
          \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, finite_mapTheory.FUPDATE_COMMUTES, finite_mapTheory.DOMSUB_FUPDATE_THM]
         )
      \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, finite_mapTheory.FUPDATE_COMMUTES,
             finite_mapTheory.DOMSUB_FUPDATE_THM, bstate_component_equality]
      \\ metis_tac[FOLDR_word_add_init_val, WORD_ADD_COMM]
     )
QED

Theorem ret_satisfy_sum_shared_while:
  ∀curr_i tot s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    FLOOKUP s.locals «tot» = SOME (ValWord tot) ⇒
    ret_satisfy
          (λx.
               ∃rv s'.
                 x = INR (rv,s') ∧
                 (rv = NONE ⇒
                  size_of_shape (shape_of (THE (FLOOKUP s'.locals «tot»))) ≤
                  32 ∧ ∃v. FLOOKUP s'.locals «tot» = SOME v)
                  ∧ (rv = NONE ∨ rv = SOME Error ∨ ∃ffe. rv = SOME (FinalFFI ffe)))
          (sum_shared_array_while_0 s)
Proof
  Induct_on ‘w_arr’
  >- (simp[Once w_list_cases]
      \\ rw[]
      \\ assume_tac $ cj 1 sum_sh_array_while
      \\ first_x_assum $ qspecl_then [‘s’] assume_tac
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM]
      \\ dxrule_then assume_tac ret_satisfy_wbisim_biim
      \\ gvs[ret_satisfy_Ret, size_of_shape_def, shape_of_def]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
  \\ gvs[]
  \\ assume_tac $ cj 2 sum_sh_array_while
  \\ first_x_assum $ qspecl_then [‘s’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, word_of_val_def, FUPDATE_LIST_THM]
  \\ irule ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ pop_assum $ irule_at Any
  \\ conj_tac
  >- (strip_tac \\ EVERY_CASE_TAC \\ gvs[]
     )
  \\ rw[ret_satisfy_Vis, ret_satisfy_Ret, ret_satisfy_Tau]
  \\ EVERY_CASE_TAC \\ rw[ret_satisfy_Vis, ret_satisfy_Ret, ret_satisfy_Tau]
  \\ last_x_assum $ qspecl_then [‘curr_i + 1w’, ‘tot + word_of_bytes F 0w y’,
                                 ‘s with
                                  locals :=
                                  res_var_list
                                  (s.locals |+ («x»,ValWord (word_of_bytes F 0w y)) |+
                                    («tot»,ValWord (tot + word_of_bytes F 0w y)) |+
                                    («i»,ValWord (curr_i + 1w))) [(«x»,FLOOKUP s.locals «x»)]’] assume_tac
  \\ gvs[FLOOKUP_SIMP, res_var_list_thm]
  \\ qmatch_asmsub_abbrev_tac ‘fl_asm ⇒ _’
  \\ subgoal ‘fl_asm’
  >- (Cases_on ‘FLOOKUP s.locals «x»’
      \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, Abbr ‘fl_asm’]
     )
  \\ gvs[]
QED

Theorem ret_satisfy_sum_shared_array:
  ∀curr_i tot s.
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ⇒
    ret_satisfy
        (λx.
               ∃rv retv s'.
                 x = INR (rv,s') ∧
                 (rv = SOME (Return retv) ⇒
                  (size_of_shape (shape_of (retv)) ≤ 32))
                  ∧ (rv = SOME (Return retv) ∨ rv = SOME Error ∨ ∃ffe. rv = SOME (FinalFFI ffe)))
          (sum_shared_array_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ rw[]
  \\ irule ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any sum_sh_array_shallow
  \\ irule_at Any ret_satisfy_impl_bind_impl
  \\ irule_at Any $ SIMP_RULE (srw_ss ()) [LET_THM] ret_satisfy_sum_shared_while
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind,  word_of_val_def, FUPDATE_LIST_THM]
  \\ last_assum $ irule_at Any
  \\ gvs[]
  \\ irule_at (Pos last) ret_satisfy_strengthen
  \\ irule_at Any $ SIMP_RULE (srw_ss ()) [LET_THM] ret_satisfy_sum_shared_while
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind,  word_of_val_def, FUPDATE_LIST_THM]
  \\ last_assum $ irule_at Any
  \\ gvs[]
  \\ rw[ret_satisfy_Ret]
  \\ FULL_CASE_TAC \\ gvs[ret_satisfy_Ret]
QED


Theorem sum_sh_array_correctness:
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    (∀i. MEM i w_arr ⇒ LENGTH (nb_func (SharedMem MappedRead,[0w],
                                        word_to_bytes (base_addr + 8w * i) F)) =
                       LENGTH (word_to_bytes (base_addr + 8w * i) F)) ⇒
    let
        tot = (FOLDR $+ 0w
                        (MAP (λaddr. word_of_bytes
                                     F 0w (nb_func (SharedMem MappedRead, [0w],
                                                    word_to_bytes (base_addr + 8w * addr) F))) w_arr))
    in
    branch_terminate_satisfy (λe res. res = INL (INR (nb_func e)))
                             (λv. v = INR (SOME (Return (ValWord tot)), s with locals := FEMPTY))
                             (sum_shared_array_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ gvs[]
  \\ irule itree_wbisim_impl_branch_terminate_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any sum_sh_array_shallow
  \\ irule_at Any ret_satisfy_strengthen
  \\ irule_at Any ret_satisfy_sum_shared_while
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ last_assum $ irule_at Any
  \\ gvs[]
  \\ conj_tac
  >- rw[]
  \\ irule branch_terminate_satisfy_bind
  \\ irule_at (Pos last) $ SIMP_RULE (srw_ss ()) [LET_THM] sum_sh_array_while_correctness
  \\ last_assum $ irule_at Any
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ irule $ cj 1 branch_terminate_satisfy_rules
  \\ rw[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ gvs[Once w_list_cases]
QED

Theorem sum_sh_array_correctness_read_id:
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    (∀i. MEM i w_arr ⇒ nb_func (SharedMem MappedRead,[0w],
                                        word_to_bytes (base_addr + 8w * i) F) = word_to_bytes i F) ⇒
    let
        tot = (FOLDR $+ 0w w_arr)
    in
    branch_terminate_satisfy (λe res. res = INL (INR (nb_func e)))
                             (λv. v = INR (SOME (Return (ValWord tot)), s with locals := FEMPTY))
                             (sum_shared_array_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ gvs[]
  \\ irule branch_terminate_satisfy_ret_cond_impl
  \\ irule_at Any $ SIMP_RULE (srw_ss ()) [LET_THM] sum_sh_array_correctness
  \\ last_assum $ irule_at Any
  \\ rw[]
  \\ irule FOLDR_CONG \\ rw[MAP_EQ_ID]
  \\ first_x_assum $ qspec_then ‘addr’ assume_tac
  \\ gvs[]
  \\ irule word_to_bytes_word_of_bytes_32
QED

val call_both_shallow = List.nth (fst initSharedArray_result, 2) |> (fn (x,y,z) => x)

Theorem call_both_correctness:
  s.code = initSharedArray_codes ∧
  w_list 0w len w_arr ∧
  set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
  ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
  (∀i. MEM i w_arr ⇒
       LENGTH
       (nb_func
        (SharedMem MappedRead,[0w],word_to_bytes (base_addr + 8w * i) F)) =
       LENGTH (word_to_bytes (base_addr + 8w * i) F) ∧
       LENGTH
       (nb_func
        (SharedMem MappedWrite,[0w],
         word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) =
       LENGTH (word_to_bytes i F ++ word_to_bytes (base_addr + 8w * i) F)) ⇒
  let
    tot = (FOLDR $+ 0w
                    (MAP (λaddr. word_of_bytes
                                 F 0w (nb_func (SharedMem MappedRead, [0w],
                                                    word_to_bytes (base_addr + 8w * addr) F))) w_arr))
  in
  branch_terminate_satisfy (λe res. res = INL (INR (nb_func e)))
                           (λv. v = INR (SOME (Return (ValWord tot)), s with locals := FEMPTY))
                           (call_both_body [ValWord base_addr; ValWord len] s)
Proof
  rpt strip_tac
  \\ gvs[]
  \\ irule itree_wbisim_impl_branch_terminate_satisfy
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any call_both_shallow
  \\ irule_at Any ret_satisfy_impl_bind_impl
  \\ irule_at Any ret_satisfy_init_shared_array
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ last_assum $ irule_at Any
  \\ gvs[itree_bind_assoc]
  \\ irule_at (Pos last) branch_terminate_satisfy_bind
  \\ irule_at Any $ SIMP_RULE (srw_ss ()) [LET_THM] init_sh_array_correctness
  \\ last_assum $ irule_at Any
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ gvs[Once itree_call_handler_def, itree_bind_assoc]
  \\ irule_at (Pos hd) branch_terminate_satisfy_bind
  \\ irule_at (Pos hd) $ SIMP_RULE (srw_ss ()) [LET_THM] sum_sh_array_correctness
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_list_thm]
  \\ last_assum $ irule_at Any
  \\ gvs[]
  \\ conj_tac
  >- rw[itree_deccall_handler_def, branch_terminate_satisfy_Tau, branch_terminate_satisfy_Ret, set_var_defs, shape_of_def,
         FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, DOMSUB_FLOOKUP_THM, word_of_val_def, FUPDATE_LIST_THM, res_var_def]
  \\ rw[itree_call_handler_def, ret_satisfy_Ret, ret_satisfy_Tau]
  \\ rw[ret_satisfy_Ret, ret_satisfy_Tau, FLOOKUP_SIMP]
  \\ irule_at Any ret_satisfy_strengthen
  \\ irule_at Any ret_satisfy_sum_shared_array
  \\ gvs[word_of_val_def]
  \\ last_assum $ irule_at Any
  \\ rw[]
QED
