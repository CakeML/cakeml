
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

    
Definition ffi_rw_shmem_def:
  ffi_rw_shmem fc =
  ((∀c ad shmem_map. fc (SharedMem MappedRead) shmem_map c ad =
           Oracle_return shmem_map
                         (word_to_bytes (THE (FLOOKUP shmem_map (word_of_bytes F 0w ad))) F)) ∧
   (∀c wad shmem_map. ∃ws'. fc (SharedMem MappedWrite) shmem_map c (wad:word8 list) =
                  Oracle_return (shmem_map |+ (word_of_bytes F (0w : 32 word) (DROP (LENGTH wad - 4) wad),
                                               (word_of_bytes F (0w : 32 word)
                                                              (TAKE (LENGTH wad - 4) wad)))) ws' ∧
                  LENGTH wad = LENGTH ws'))
End

Inductive w_list:
  ((~ (i:'a word < x)) ⇒ w_list i x []) ∧
  (((i:'a word < x) ∧ w_list (i + 1w) x l) ⇒ w_list i x (i :: l))
End

Definition ftree_def:
  (ftree:β fst -> α ptree ->
           (unit, unit, ((ffi_outcome + word8 list) + α result option # α bstate) # β) itree)
  (fs:'b fst) (t:'a ptree) =
    itree_iter
      (λ(t,st).
           case t of
             Ret r => Ret (INR (r, st))
           | Tau u => Ret (INL (u,st))
           | Vis (s,c,ws) g =>
             case FST fs s st c ws of
               Oracle_return fs' ws' =>
                 if LENGTH ws = LENGTH ws' then
                   Ret (INL (g (INL (INR ws')),fs'))
                 else Ret (INL (g (INL (INL FFI_failed)),st))
             | Oracle_final outcome => Ret (INL (g (INL (INL outcome)),st)))
      (t,SND fs)
End

Theorem ftree_simps:
  ftree fs (Ret r) = Ret (r, SND fs) ∧ ftree fs (Tau u) = Tau (ftree fs u) ∧
  ftree fs (Vis (s,c,ws) g) =
  case FST fs s (SND fs) c ws of
    Oracle_return fs' ws' =>
      if LENGTH ws = LENGTH ws' then
        Tau (ftree (FST fs,fs') (g (INL (INR ws'))))
      else Tau (ftree fs (g (INL (INL FFI_failed))))
  | Oracle_final outcome => Tau (ftree fs (g (INL (INL outcome))))
Proof
  rpt conj_tac
  >- rw[ftree_def, itree_iter_def, Once itree_unfold]
  >- rw[ftree_def, itree_iter_def, Once itree_unfold]
  \\ FULL_CASE_TAC
  \\ rw[ftree_def, itree_iter_def, Once itree_unfold]
QED

Theorem ftree_non_vis:
  ftree fs t ≠ FUNPOW Tau n (Vis e k)
Proof
  map_every qid_spec_tac [‘fs’, ‘t’, ‘e’ , ‘k’]
  \\ Induct_on ‘n’
  >- (rw[FUNPOW, ftree_def]
      \\ Cases_on ‘t’ \\ gvs[Once itree_iter_thm]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  \\ rw[GSYM FUNPOW, FUNPOW_SUC]
  \\ Cases_on ‘t’ \\ gvs[ftree_simps]
  \\ Cases_on ‘a’
  \\ Cases_on ‘r’ \\ gvs[ftree_simps]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem ftree_bind:
  ftree fs (t >>= k) = ftree fs t >>= (λ(r, fs'). ftree (FST fs, fs') (k r))
Proof
  rw[Once itree_strong_bisimulation]
  \\ qexists ‘CURRY {(ftree fs (t >>= k), ftree fs t >>= (λ(r,fs'). ftree (FST fs,fs') (k r))) | T }’
  \\ rw[]
  >- (rw[EXISTS_PROD]
      \\ metis_tac[PAIR]
     )
  >- (Cases_on ‘x'’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[]
      \\ Cases_on ‘q'’ \\ gvs[ftree_simps, itree_bind_thm]
      \\ Cases_on ‘a’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[ftree_simps, itree_bind_thm]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[]
      \\ Cases_on ‘q'’ \\ gvs[ftree_simps, itree_bind_thm]
      >- metis_tac[]
      >- (disj1_tac
          \\ rw[EXISTS_PROD]
          \\ metis_tac[PAIR]
         )
      \\ Cases_on ‘a’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[ftree_simps, itree_bind_thm]
      \\ EVERY_CASE_TAC \\ gvs[]
      \\disj1_tac
      \\ rw[EXISTS_PROD]
      \\ metis_tac[PAIR]
     )
  \\ Cases_on ‘x’ \\ gvs[]
  \\ Cases_on ‘r’ \\ gvs[]
  \\ pop_assum $ assume_tac o GSYM
  \\ ‘ftree q (q' >>= r') = FUNPOW Tau 0 (Vis a f)’ by rw[FUNPOW]
  \\ gvs[ftree_non_vis]
QED

Theorem ftree_spin:
  ftree fs spin = spin
Proof
  rw[Once itree_strong_bisimulation]
  \\ qexists ‘CURRY {(ftree fs spin, spin)}’
  \\ PURE_ONCE_REWRITE_TAC[spin]
  \\ rw[ftree_simps]
  \\ disj1_tac
  \\ rw[Once spin]
  \\ rw[Once spin, ftree_simps]
QED

Theorem ftree_FUNPOW:
  ftree fs (FUNPOW Tau n t) = FUNPOW Tau n (ftree fs t)
Proof
  Induct_on ‘n’
  >- gvs[FUNPOW, ftree_simps]
  \\ simp[SimpLHS, FUNPOW_SUC, ftree_simps]
  \\ simp[FUNPOW_SUC]
QED

Theorem itree_bisim_impl_ftree_bisim:
  t = t' ⇒ ftree fs t = ftree fs t'
Proof
  rpt strip_tac
  \\ rw[Once itree_bisimulation]
  \\ qexists ‘CURRY {(ftree fs t, ftree fs t') | fs, t, t' | t = t'}’
  \\ rw[]
  >- (qexists ‘(fs, t, t)’
      \\ rw[]
     )
  >- (Cases_on ‘x'’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘r ’\\ gvs[]
      \\ qexists ‘u’ \\ rw[]
      \\ Cases_on ‘q'’ \\ gvs[ftree_simps]
      >- (qexists ‘(q, u', u')’ \\ rw[]
         )
      \\ Cases_on ‘a’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[ftree_simps]
      \\ EVERY_CASE_TAC \\ gvs[]
      >- (qexists ‘((FST q, f), g (INL (INR l)), g (INL (INR l)))’ \\ rw[]
         )
      >- (qexists ‘(q, (g (INL (INL FFI_failed))), (g (INL (INL FFI_failed))))’ \\ rw[]
         )
      >- (qexists ‘(q, (g (INL (INL f))), (g (INL (INL f))))’ \\ rw[]
         )
     )
  \\ Cases_on ‘x’ \\ gvs[]
  \\ Cases_on ‘r’ \\ gvs[]
  \\ assume_tac $ GEN_ALL $ SPEC “0:num” $ GEN “n:num” ftree_non_vis
  \\ gvs[]
QED

        
Theorem itree_wbisim_impl_ftree_wbisim:
  t ≈ t' ⇒ ftree fs t ≈ ftree fs t'
Proof
  rpt strip_tac
  \\ irule itree_wbisim_coind
  \\ qexists ‘CURRY {(ftree fs t, ftree fs t') | fs, t, t' | t ≈ t'}’
  \\ reverse $ rw[]
  >- (qexists ‘(fs, t, t')’
      \\ rw[]
     )
  \\ Cases_on ‘x’ \\ gvs[]
  \\ Cases_on ‘r’ \\ gvs[]
  \\ pop_assum $ assume_tac o SRULE [Once itree_wbisim_cases]
  \\ gvs[ftree_simps]
  >- (disj1_tac
      \\ qexists ‘(q, t'', t''')’ \\ gvs[]
     )
  >- (imp_res_tac strip_tau_FUNPOW
      \\ gvs[ftree_simps, ftree_FUNPOW]
      \\ disj1_tac
      \\ Cases_on ‘e’ \\ gvs[]
      \\ Cases_on ‘r’ \\ gvs[ftree_simps]
      \\ EVERY_CASE_TAC \\ gvs[GSYM FUNPOW, FUNPOW_SUC]
      \\ rw[GSYM ftree_FUNPOW]
      >- (qexists ‘((FST q,f), FUNPOW Tau n' (k (INL (INR l))), FUNPOW Tau n (k' (INL (INR l))))’ \\ gvs[]
          \\ irule FUNPOW_Tau_wbisim_intro
          \\ rw[]
         )
      >- (qexists ‘(q, FUNPOW Tau n' (k (INL (INL FFI_failed))), FUNPOW Tau n (k' (INL (INL FFI_failed))))’ \\ gvs[]
          \\ irule FUNPOW_Tau_wbisim_intro
          \\ rw[]
         )
      >- (qexists ‘(q, FUNPOW Tau n' (k (INL (INL f))), FUNPOW Tau n (k' (INL (INL f))))’ \\ gvs[]
          \\ irule FUNPOW_Tau_wbisim_intro
          \\ rw[]
         )
     )
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[ftree_simps, ftree_FUNPOW]
  \\ disj2_tac
  \\ disj2_tac
  \\ qexists ‘r, SND q’
  \\ rw[strip_tau_FUNPOW_cancel]
QED

        
Definition result_ffi_def:
  result_ffi fs t = some x. strip_tau (ftree fs t) (Ret x)
End

Theorem ftree_spin_result_ffi:
  ftree fs t = spin ⇔ result_ffi fs t = NONE
Proof
  rw[result_ffi_def, some_def]
  \\ iff_tac
  >- rw[spin_strip_tau]
  \\ rpt strip_tac
  \\ irule strip_tau_spin
  \\ CCONTR_TAC
  \\ gvs[]
  \\ Cases_on ‘t'’ \\ gvs[]
  \\ drule strip_tau_FUNPOW
  \\ rpt strip_tac
  \\ fs[ftree_non_vis]
QED

Theorem ftree_ret_result_ffi:
  result_ffi fs t = SOME r ⇔ ∃n. ftree fs t = FUNPOW Tau n (Ret r)
Proof
  rw[result_ffi_def, some_def]
  \\ iff_tac
  >- (rw[]
      \\ subgoal ‘(@x. strip_tau (ftree fs t) (Ret x)) = x’
      >- (irule SELECT_UNIQUE
          \\ rpt strip_tac
          \\ iff_tac
          \\ rpt strip_tac
          \\ gvs[]
          \\ drule strip_tau_inj
          \\ rw[]
          \\ pop_assum $ qspec_then ‘Ret x’ assume_tac
          \\ rfs[]
         )
      \\ rw[]
      \\ drule_then assume_tac strip_tau_FUNPOW
      \\ pop_assum $ irule
     )
  \\ rpt strip_tac
  \\ gvs[]
  >- (irule_at Any strip_tau_FUNPOW_cancel
      \\ rw[]
     )
  \\ irule SELECT_UNIQUE
  \\ rpt strip_tac
  \\ iff_tac
  \\ rpt strip_tac
  \\ gvs[strip_tau_FUNPOW_cancel]
  \\ drule strip_tau_FUNPOW
  \\ rpt strip_tac
  \\ fs[FUNPOW_Tau_Ret_eq_simp]
QED

Theorem strip_tau_FUNPOW_simp:
  strip_tau (FUNPOW Tau n t) t' ⇔ strip_tau t t'
Proof
  iff_tac \\ simp[strip_tau_FUNPOW_strip_tau]
  \\ map_every qid_spec_tac [‘t’, ‘t'’]
  \\ Induct_on ‘n’
  >- rw[FUNPOW]
  \\ rw[FUNPOW_SUC]
QED
        
Theorem result_ffi_bind:
  result_ffi fs (t >>= k) = OPTION_BIND (result_ffi fs t) (λ(r, fs'). result_ffi (FST fs, fs') (k r))
Proof
  Cases_on ‘result_ffi fs t’ \\ rw[]
  >- (dxrule_then assume_tac $ iffRL ftree_spin_result_ffi
      \\ rw[result_ffi_def, ftree_bind, spin_bind, some_def, spin_strip_tau]
     )
  \\ pop_assum $ assume_tac o SRULE[ftree_ret_result_ffi]
  \\ gvs[result_ffi_def, ftree_bind, FUNPOW_Tau_bind, FUN_EQ_THM]
  \\ Cases_on ‘x’ \\ rw[FUN_EQ_THM, strip_tau_FUNPOW_simp]
QED

Theorem result_ffi_simps:
  result_ffi fs (Ret r) = SOME (r, SND fs) ∧
  result_ffi fs (Tau t) = result_ffi fs t ∧
  result_ffi fs (Vis (s,c,ws) g) =
  case FST fs s (SND fs) c ws of
    Oracle_return fs' ws' =>
      if LENGTH ws = LENGTH ws' then
         result_ffi (FST fs, fs') (g (INL (INR ws')))
      else result_ffi fs (g (INL (INL FFI_failed)))
  | Oracle_final outcome => result_ffi fs (g (INL (INL outcome)))
Proof
  rpt conj_tac
  >- rw[ftree_ret_result_ffi, ftree_simps]
  >- rw[result_ffi_def, ftree_simps]
  \\ rw[result_ffi_def, ftree_simps]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem ptree_wbisim_impl_result_ffi_eq:
  t ≈ t' ⇒ result_ffi fs t = result_ffi fs t'
Proof
  rpt strip_tac
  \\ Cases_on ‘result_ffi fs t’ \\ gvs[]
  >- (pop_assum $ assume_tac o SRULE[GSYM ftree_spin_result_ffi]
      \\ drule itree_wbisim_impl_ftree_wbisim
      \\ rpt strip_tac
      \\ pop_assum $ qspec_then ‘fs’ assume_tac
      \\ gvs[]
      \\ dxrule_then assume_tac itree_wbisim_sym
      \\ pop_assum $ assume_tac o SRULE[wbisim_spin_eq]
      \\ fs[ftree_spin_result_ffi]
     )
  \\ fs[ftree_ret_result_ffi]
  \\ drule itree_wbisim_impl_ftree_wbisim
  \\ disch_tac
  \\ pop_assum $ qspec_then ‘fs’ assume_tac
  \\ gvs[]
  \\ dxrule_then assume_tac itree_wbisim_sym
  \\ pop_assum $ assume_tac o SRULE[wbisim_spin_eq, wbisim_FUNPOW_Tau]
  \\ irule itree_wbisim_Ret_FUNPOW
  \\ pop_assum $ irule
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

    
Theorem init_shared_while_loop_ftree:
  ∀curr_i base_addr shmem_map shmem_new_map s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    ffi_rw_shmem fc ⇒
    let
      s' = if ¬(curr_i < len) then s else s with locals := s.locals |+ («i», ValWord len)
    in
      ftree (fc, (shmem_map:word32 |-> word32)) (init_shared_array_while_0 s) ≈
            (Ret (INR (NONE, s'), shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i), curr_i) w_arr))
Proof
  Induct_on ‘w_arr’
  >- (simp[Once w_list_cases]
      \\ rw[]
      \\ assume_tac $ cj 1 init_sh_array_while
      \\ first_x_assum $ qspecl_then [‘s’] assume_tac
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
      \\ irule_at Any itree_wbisim_trans
      \\ irule_at Any itree_wbisim_impl_ftree_wbisim
      \\ pop_assum $ irule_at Any
      \\ rw[ftree_simps, itree_wbisim_refl]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
  \\ assume_tac $ cj 2 init_sh_array_while
  \\ first_x_assum $ qspecl_then [‘s’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_wbisim_impl_ftree_wbisim
  \\ pop_assum $ irule_at Any
  \\ rw[ftree_simps]                
  \\ qpat_assum ‘ffi_rw_shmem _’ $ assume_tac o SRULE[ffi_rw_shmem_def]
  \\ fs[]
  \\ pop_assum $ qspecl_then [‘[0w]’, ‘word_to_bytes curr_i F ++ word_to_bytes (base_addr + 8w * curr_i) F’, ‘shmem_map’] assume_tac
  \\ gvs[]
  \\ ‘4 = LENGTH (word_to_bytes curr_i F)’ by rw[]
  \\ drule TAKE_LENGTH_ID_rwt
  \\ dxrule DROP_LENGTH_NIL_rwt
  \\ rpt strip_tac
  \\ rw[TAKE_APPEND, DROP_APPEND, ftree_simps, word_to_bytes_word_of_bytes_32]
  \\ last_x_assum $ qspecl_then [‘curr_i + 1w’, ‘base_addr’, ‘shmem_map |+ (base_addr + 8w * curr_i,curr_i)’,
                                 ‘s with locals := s.locals |+ («i»,ValWord (curr_i + 1w))’] assume_tac
  \\ gvs[FLOOKUP_SIMP, ftree_simps, word_to_bytes_word_of_bytes_32]
  \\ Cases_on ‘curr_i + 1w < len’
  \\ gvs[]
  \\ dxrule_then assume_tac $ iffLR WORD_NOT_LESS
  \\ dxrule_then assume_tac word_plus_one_le
  \\ dxrule_all WORD_LESS_EQUAL_ANTISYM
  \\ strip_tac
  \\ rw[]
QED

Theorem ret_satisfy_init_shared_while_loop:
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
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
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
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
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



Theorem init_shared_while_loop_correct_ftree:
  ∀curr_i base_addr shmem_map shmem_new_map s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    ffi_rw_shmem fc ⇒
    ftree (fc, (shmem_map:word32 |-> word32)) (init_shared_array_while_0 s) ≈ (Ret (INR (NONE, s'), shmem_new_map)) ⇒
    (∀i. MEM i w_arr ⇒ FLOOKUP shmem_new_map (base_addr + 8w * i) = SOME i)
Proof
  rpt strip_tac
  \\ drule_all init_shared_while_loop_ftree
  \\ rpt strip_tac
  \\ pop_assum $ qspec_then ‘shmem_map’ assume_tac
  \\ gvs[]
  \\ dxrule_then assume_tac itree_wbisim_sym
  \\ dxrule_all_then assume_tac itree_wbisim_trans
  \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ gvs[flookup_update_list_some]
  \\ disj1_tac
  \\ irule $ iffRL $ GSYM MEM_ALOOKUP
  \\ rw[GSYM MAP_REVERSE, MAP_MAP_o, o_DEF]
  >- rw[MAP_REVERSE]
  \\ rw[MEM_MAP]
QED


Theorem init_shared_ftree:
  ∀base_addr len shmem_map s.
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    ffi_rw_shmem fc ⇒
    ftree (fc, (shmem_map:word32 |-> word32)) (init_shared_array_body [ValWord base_addr; ValWord len] s) ≈
          (Ret (INR (SOME (Return (ValWord 0w)), s with locals := FEMPTY), shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i), curr_i) w_arr))
Proof
  rpt strip_tac
  \\ assume_tac init_sh_array_shallow
  \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘s’] assume_tac
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_wbisim_impl_ftree_wbisim
  \\ pop_assum $ irule_at Any
  \\ gvs[ftree_simps, ftree_bind]
  \\ drule_then assume_tac init_shared_while_loop_ftree
  \\ pop_assum $ qspecl_then [‘fc’, ‘base_addr’, ‘shmem_map’, ‘shmem_new_map’,
                              ‘s with
                               locals :=
                               FEMPTY |+ («base_addr»,ValWord base_addr) |+
                                      («len»,ValWord len) |+ («i», ValWord 0w)’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ pop_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’, ftree_simps]
  \\ EVERY_CASE_TAC \\ gvs[itree_wbisim_refl]
QED
        
val [sum_sh_array_while] = List.nth (fst initSharedArray_result, 1) |> (fn (x,y,z) => y)

val sum_sh_array_shallow = List.nth (fst initSharedArray_result, 1) |> (fn (x,y,z) => x)



Theorem FOLDR_word_add_init_val:
  FOLDR $+ ((init_value:'a word) + extra) l = extra + FOLDR $+ init_value l
Proof
  Induct_on ‘l’ \\ rw[]
QED

    
Theorem sum_shared_while_loop_ftree:
  ∀curr_i tot shmem_map s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    FLOOKUP s.locals «tot» = SOME (ValWord tot) ∧
    (∀addr:word32. MEM addr w_arr ⇒ ∃v. FLOOKUP shmem_map (base_addr + 8w * addr) = SOME v) ∧
    ffi_rw_shmem fc ⇒
    let
      s' = if ¬(curr_i < len) then
             s
           else
             s with locals :=
             res_var_list (s.locals
                            |+ («i», ValWord len)
                            |+ («tot», ValWord (FOLDR $+ tot (MAP (λaddr. THE (FLOOKUP shmem_map (base_addr + 8w * addr))) w_arr))))
                          [(«x»,FLOOKUP s.locals «x»)]
    in
      ftree (fc,shmem_map) (sum_shared_array_while_0 s) ≈ Ret (INR (NONE,s'),shmem_map)
Proof
  Induct_on ‘w_arr’
  >- (simp[Once w_list_cases]
      \\ rw[]
      \\ assume_tac $ cj 1 sum_sh_array_while
      \\ first_x_assum $ qspecl_then [‘s’] assume_tac
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
      \\ irule_at Any itree_wbisim_trans
      \\ irule_at Any itree_wbisim_impl_ftree_wbisim
      \\ pop_assum $ irule_at Any
      \\ rw[ftree_simps, itree_wbisim_refl]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
  \\ gvs[]
  \\ assume_tac $ cj 2 sum_sh_array_while
  \\ first_x_assum $ qspec_then ‘s’ assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_wbisim_impl_ftree_wbisim
  \\ pop_assum $ irule_at Any
  \\ gvs[ftree_simps]
  \\ qpat_assum ‘ffi_rw_shmem _’ $ assume_tac o SRULE[ffi_rw_shmem_def]
  \\ fs[set_kvar_defs, word_to_bytes_word_of_bytes_32, set_var_defs]
  \\ first_assum $ qspec_then ‘curr_i’ (assume_tac o SRULE[])
  \\ gvs[FLOOKUP_SIMP, OPTION_BIND_def, res_var_list_thm]
  \\ last_x_assum $ qspecl_then [‘curr_i + 1w’, ‘tot + v’, ‘shmem_map’,
                                 ‘s with
                                  locals :=
                                  res_var_list
                                  (s.locals |+ («x»,ValWord v) |+
                                    («tot»,ValWord (tot + v)) |+ («i»,ValWord (curr_i + 1w)))
                                  [(«x»,FLOOKUP s.locals «x»)]’] assume_tac
  \\ gvs[FLOOKUP_SIMP, res_var_list_thm]
  \\ irule_at Any itree_wbisim_trans
  \\ qmatch_asmsub_abbrev_tac ‘fl_asm ⇒ _’
  \\ subgoal ‘fl_asm’
  >- (Cases_on ‘FLOOKUP s.locals «x»’
      \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, Abbr ‘fl_asm’]
     )
  \\ gvs[]
  \\ first_x_assum $ irule_at Any
  \\ reverse conj_tac
  >- (strip_tac \\ EVERY_CASE_TAC \\ rw[]
     ) 
  \\ rw[Once itree_wbisim_cases]
  >- (dxrule_then assume_tac $ iffLR WORD_NOT_LESS
      \\ dxrule_then assume_tac word_plus_one_le
      \\ dxrule_all WORD_LESS_EQUAL_ANTISYM
      \\ strip_tac
      \\ rw[]
      \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
      \\ gvs[]
      \\ Cases_on ‘FLOOKUP s.locals «x»’
      \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, finite_mapTheory.FUPDATE_COMMUTES, finite_mapTheory.DOMSUB_FUPDATE_THM]
     )
  \\ ‘FOLDR $+ (tot + v)
               (MAP
                (λaddr. THE (FLOOKUP shmem_map (8w * addr + base_addr)))
                w_arr) =
      v +
      FOLDR $+ tot
               (MAP
                (λaddr. THE (FLOOKUP shmem_map (8w * addr + base_addr)))
                w_arr)’ by rw[FOLDR_word_add_init_val]                          
  \\ Cases_on ‘FLOOKUP s.locals «x»’
  \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM, finite_mapTheory.FUPDATE_COMMUTES, finite_mapTheory.DOMSUB_FUPDATE_THM]
QED

    
Theorem ret_satisfy_sum_shared_while_loop:
  ∀curr_i tot s.
    w_list curr_i len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    FLOOKUP s.locals «i» = SOME (ValWord curr_i) ∧
    FLOOKUP s.locals «len» = SOME (ValWord len) ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    FLOOKUP s.locals «tot» = SOME (ValWord tot)  ⇒
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
      \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
      \\ dxrule_then assume_tac ret_satisfy_wbisim_biim
      \\ gvs[ret_satisfy_Ret, size_of_shape_def, shape_of_def]
     )
  \\ rpt strip_tac
  \\ qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
  \\ gvs[]
  \\ assume_tac $ cj 2 sum_sh_array_while
  \\ first_x_assum $ qspecl_then [‘s’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps, word_of_val_def, FUPDATE_LIST_THM]
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

Theorem sum_shared_ftree:
  ∀shmem_map s.
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    (∀addr:word32. MEM addr w_arr ⇒ ∃v. FLOOKUP shmem_map (base_addr + 8w * addr) = SOME v) ∧
    ffi_rw_shmem fc ⇒
    ftree (fc, (shmem_map:word32 |-> word32)) (sum_shared_array_body [ValWord base_addr; ValWord len] s) ≈
          (Ret (INR (SOME (Return (ValWord (FOLDR $+ 0w (MAP (λaddr. THE (FLOOKUP shmem_map (base_addr + 8w * addr))) w_arr)))),
                     s with locals := FEMPTY), shmem_map))
Proof
  rpt strip_tac
  \\ assume_tac sum_sh_array_shallow
  \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘s’] assume_tac
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_wbisim_impl_ftree_wbisim
  \\ pop_assum $ irule_at Any
  \\ gvs[ftree_simps, ftree_bind]
  \\ drule_then assume_tac sum_shared_while_loop_ftree
  \\ pop_assum $ qspecl_then [‘fc’, ‘base_addr’,  ‘0w’, ‘shmem_map’,
                              ‘s with
                               locals :=
                               FEMPTY |+ («base_addr»,ValWord base_addr) |+
                                      («len»,ValWord len) |+ («i»,ValWord 0w) |+
                                      («tot»,ValWord 0w)’] assume_tac
  \\ gvs[FLOOKUP_SIMP, eval_def, FUNPOW_Tau_bind, ftree_simps]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ first_x_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’, ftree_simps]
  \\ reverse $ conj_tac
  >- (irule ret_satisfy_strengthen
      \\ irule_at Any ret_satisfy_sum_shared_while_loop
      \\ Cases_on ‘FLOOKUP s.locals «x»’
      \\ gvs[FLOOKUP_SIMP, res_var_list_thm, DOMSUB_FLOOKUP_THM]
      \\ metis_tac[]
     )
  \\ FULL_CASE_TAC \\ gvs[FLOOKUP_SIMP]
  >- (qpat_x_assum ‘w_list _ _ _’ $ assume_tac o SRULE [Once w_list_cases]
      \\ gvs[itree_wbisim_refl]
     )
  \\ gvs[res_var_list_thm, FLOOKUP_SIMP, DOMSUB_FLOOKUP_THM, itree_wbisim_refl]
QED

val call_both_shallow = List.nth (fst initSharedArray_result, 2) |> (fn (x,y,z) => x)
    
Theorem call_both_ftree:
  ∀curr_i shmem_map shmem_new_map fs s.
    s.code = initSharedArray_codes ∧
    w_list 0w len w_arr ∧
    set (MAP (\i. (base_addr + (i * 8w))) w_arr) ⊆ s.sh_memaddrs ∧
    ALL_DISTINCT (MAP (\i. (base_addr + (i * 8w))) w_arr) ∧
    ffi_rw_shmem fc ⇒
    ftree (fc, (shmem_map:word32 |-> word32)) (call_both_body [ValWord base_addr; ValWord len] s) ≈
          (Ret (INR (SOME (Return (ValWord (FOLDR $+ 0w w_arr))), s with locals := FEMPTY),
                shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i), curr_i) w_arr))
Proof
  rpt strip_tac
  \\ assume_tac call_both_shallow
  \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘s’] assume_tac
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_wbisim_impl_ftree_wbisim
  \\ pop_assum $ irule_at Any
  \\ gvs[ftree_simps, ftree_bind]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ drule_then assume_tac init_shared_ftree
  \\ pop_assum $ qspecl_then [‘fc’, ‘base_addr’, ‘shmem_map’,
                              ‘s with
                               locals :=
                               FEMPTY |+ («base_addr»,ValWord base_addr) |+
                                      («len»,ValWord len)’] assume_tac
  \\ gvs[FLOOKUP_SIMP]
  \\ pop_assum $ irule_at Any
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’, ftree_simps]
  \\ gvs[Once itree_call_handler_def, ftree_simps, FLOOKUP_SIMP, word_of_val_def, ftree_bind]
  \\ drule_then assume_tac sum_shared_ftree
  \\ pop_assum $ qspecl_then [‘fc’, ‘base_addr’, ‘shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i,curr_i)) w_arr’,
                              ‘s with
                               locals :=
                               FEMPTY |+ («base_addr»,ValWord base_addr) |+
                                      («len»,ValWord len)’] assume_tac
  \\ gvs[]
  \\ irule_at Any itree_wbisim_trans
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ pop_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’, ftree_simps]
  \\ gvs[Once itree_deccall_handler_def, shape_of_def, ftree_simps, set_var_defs,
         res_var_list_thm, FLOOKUP_SIMP, DOMSUB_FLOOKUP_THM]
  \\ rpt $ conj_tac
  >- (rw[flookup_update_list_some]
      \\ qexists ‘addr’
      \\ disj1_tac
      \\ irule $ iffRL $ GSYM MEM_ALOOKUP
      \\ rw[GSYM MAP_REVERSE, MAP_MAP_o, o_DEF]
      >- rw[MAP_REVERSE]
      \\ rw[MEM_MAP]
     )
  >- (rw[Once itree_wbisim_cases, res_var_def]
      \\ ‘MAP (λaddr. THE (FLOOKUP (shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i,curr_i)) w_arr)
                                   (8w * addr + base_addr))) w_arr = w_arr’ suffices_by rw[]
      \\ rw[MAP_EQ_ID]
      \\ ‘FLOOKUP (shmem_map |++ MAP (λcurr_i. (base_addr + 8w * curr_i,curr_i)) w_arr)
          (8w * addr + base_addr) = SOME addr’ suffices_by rw[]
      \\ rw[flookup_update_list_some]
      \\ disj1_tac
      \\ irule $ iffRL $ GSYM MEM_ALOOKUP
      \\ rw[GSYM MAP_REVERSE, MAP_MAP_o, o_DEF]
      >- rw[MAP_REVERSE]
      \\ rw[MEM_MAP]
     )
  \\ irule_at Any ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ irule_at Any init_sh_array_shallow
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[Abbr ‘k’, itree_wbisim_refl]
  \\ rw[itree_bind_assoc]
  \\ irule ret_satisfy_impl_bind_impl
  \\ irule_at Any (SIMP_RULE (srw_ss ()) [LET_THM] ret_satisfy_init_shared_while_loop)
  \\ gvs[FLOOKUP_SIMP]
  \\ first_assum $ irule_at Any
  \\ gvs[]
  \\ strip_tac
  \\ Cases_on ‘r’ \\ gvs[]
  \\ Cases_on ‘y’ \\ gvs[]
  \\ reverse $ Cases_on ‘q’ \\ gvs[]
  >- (rpt strip_tac
      \\ fs[itree_call_handler_def, ret_satisfy_Ret]
     )
  \\ gvs[itree_call_handler_def, ret_satisfy_Ret, FLOOKUP_SIMP, word_of_val_def]
  \\ strip_tac
  \\ irule_at Any ret_satisfy_wbisim_impl
  \\ irule_at Any itree_wbisim_sym
  \\ irule_at Any sum_sh_array_shallow
  \\ gvs[FLOOKUP_SIMP]
  \\ irule_at Any ret_satisfy_strengthen
  \\ irule_at Any ret_satisfy_sum_shared_while_loop
  \\ gvs[FLOOKUP_SIMP]
  \\ first_assum $ irule_at Any
  \\ gvs[]
  \\ conj_tac
  >- rw[]
  \\ conj_tac
  >- rw[]
  \\ reverse $ conj_tac
  >- rw[]
  \\ irule_at Any ret_satisfy_impl_bind_impl
  \\ irule_at Any ret_satisfy_sum_shared_while_loop
  \\ gvs[FLOOKUP_SIMP]
  \\ first_assum $ irule_at Any
  \\ gvs[]
  \\ conj_tac
  >- rw[]
  \\ strip_tac
  \\ EVERY_CASE_TAC \\ rw[ret_satisfy_Ret]
QED



