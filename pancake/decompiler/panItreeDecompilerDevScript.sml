
Theory panDecompilerDev
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
  simpLib

  

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

Definition del_annot_def:
  del_annot (Seq (Annot _ _) (p : 'a panLang$prog)) = del_annot p ∧
  del_annot (Seq a b) = (Seq (del_annot a) (del_annot b)) ∧
  del_annot (Dec vname sh e p) = (Dec vname sh e (del_annot p)) ∧
  del_annot (DecCall rt shape fname argexps p) = (DecCall rt shape fname argexps (del_annot p)) ∧
  del_annot (If gexp p1 p2) = (If gexp (del_annot p1) (del_annot p2)) ∧
  del_annot (While gexp p) = (While gexp (del_annot p)) ∧
  del_annot (Annot _ _) = Skip ∧
  del_annot p = p
End

Theorem while_weak_bisim_upfrom_abs:
  (∀s. itree_semantics (p, s) ≈ itree_semantics (p', s))
  ⇒ ∀s. weak_bisim_upfrom_abs ((λs. itree_semantics (While g p, s)), (λs. itree_semantics (While g p', s)))
                                               (itree_semantics (While g p, s)) (itree_semantics (While g p', s))
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘weak_bisim_upfrom_abs (abs, abs') _ _’
  \\ PURE_ONCE_REWRITE_TAC[itree_semantics_While]
  \\ Cases_on ‘eval s g’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ reverse $ Cases_on ‘x’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ reverse $ Cases_on ‘w’ \\ gvs[]
  \\ FULL_CASE_TAC \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ last_x_assum $ qspec_then ‘s’ assume_tac
  \\ PURE_ONCE_REWRITE_TAC[GSYM itree_bind_thm]
  \\ irule weak_bisim_upfrom_abs_wbisim_bind
  \\ rw[]
  \\ Cases_on ‘r’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ Cases_on ‘y’ \\ gvs[]
  \\ Cases_on ‘q’ \\ gvs[]
  >- metis_tac[FUNPOW, weak_bisim_upfrom_abs_rules]
  \\ Cases_on ‘x’ \\ gvs[]
  \\ metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2, GSYM FUNPOW_SUC, GSYM FUNPOW]
QED
        
Theorem while_bisim:
  (∀s. itree_semantics (p, s) ≈ itree_semantics (p', s))
   ⇒ ∀s. itree_semantics (While g p, s) ≈ itree_semantics (While g p', s)
Proof
  disch_tac
  \\ ‘∀s. (λs. itree_semantics (While g p, s)) s ≈ (λs. itree_semantics (While g p', s)) s’ suffices_by metis_tac[]
  \\ irule $ iffLR cyclic_weak_bisim_upfrom_abs
  \\ rw[while_weak_bisim_upfrom_abs]
QED

Theorem panprog_induct:
  ∀P.
    P Skip ∧ (∀p. P p ⇒ ∀s e m. P (Dec m s e p)) ∧
    (∀v m e. P (Assign v m e)) ∧ (∀e e0. P (Store e e0)) ∧
    (∀e e0. P (Store32 e e0)) ∧
    (∀e e0. P (StoreByte e e0)) ∧ (∀p p0. P p ∧ P p0 ⇒ P (Seq p p0)) ∧
    (∀p p0. P p ∧ P p0 ⇒ ∀e. P (If e p p0)) ∧
    (∀p. P p ⇒ ∀e. P (While e p)) ∧ P Break ∧ P Continue ∧
    (∀$o l e. P (Call $o e l)) ∧
    (∀p. P p ⇒ ∀l e s m. P (DecCall m s e l p)) ∧
    (∀m e e0 e1 e2. P (ExtCall m e e0 e1 e2)) ∧ (∀m e. P (Raise m e)) ∧
    (∀e. P (Return e)) ∧ (∀$o v m e. P (ShMemLoad $o v m e)) ∧
    (∀$o e e0. P (ShMemStore $o e e0)) ∧ P Tick ∧
    (∀m m0. P (Annot m m0))
    ⇒ ∀p. P (p : 'a panLang$prog)
Proof
  strip_tac >>
  qspecl_then [‘P’,‘K T’,‘K T’,‘K T’,‘K T’,‘K T’]
              strip_assume_tac (cj 1 panLangTheory.prog_induction) >>
  rw[]
QED

Theorem itree_semantics_While_ret_satisfy_INR:
  (∀s. ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (prog, s))) ⇒
  ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (While e prog, s))
Proof
  rpt strip_tac
  \\ rw[Once itree_semantics_While]
  \\ EVERY_CASE_TAC \\ gvs[ret_satisfy_rules]
  \\ irule $ cj 2 ret_satisfy_rules
  \\ irule ret_satisfy_coind
  \\ qexists ‘λx. (∃t st. x = ((t:'a ptree) >>= (λa.
                                                   case a of
                                                     INL l => Ret (INR (SOME Error,st))
                                                   | INR (res,s') =>
                                                       case res of
                                                         NONE => Tau (itree_semantics (While e prog,s'))
                                                       | SOME Error => Ret (INR (res,s'))
                                                       | SOME TimeOut => Ret (INR (res,s'))
                                                       | SOME Break => Ret (INR (NONE,s'))
                                                       | SOME Continue =>
                                                           Tau (itree_semantics (While e prog,s'))
                                                       | SOME (Return v6) => Ret (INR (res,s'))
                                                       | SOME (Exception v7 v8) => Ret (INR (res,s'))
                                                       | SOME (FinalFFI v9) => Ret (INR (res,s'))))) ∨
                  (∃s'. x = (itree_semantics (While e prog,s')))’
  \\ rpt conj_tac
  >- metis_tac[]
  \\ rpt strip_tac
  \\ Cases_on ‘a0’ \\ rfs[]
  >- (pop_assum $ assume_tac o GSYM
      \\ drule itree_bind_ret_inv
      \\ rw[]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (pop_assum $ assume_tac o GSYM
      \\ fs[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (Cases_on ‘t’ \\ gvs[]
      \\ EVERY_CASE_TAC \\ gvs[]
      \\ metis_tac[]
      \\ gvs[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (pop_assum $ assume_tac o SRULE[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
      \\ metis_tac[]
     )
  >- (Cases_on ‘t’ \\ gvs[]
      >- (EVERY_CASE_TAC \\ gvs[]
          \\ metis_tac[]
         )
      \\ metis_tac[]
     )
  \\ gvs[Once itree_semantics_While]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem ret_satisfy_bind_k_wrap:
  (∀r. ret_satisfy P (k r)) ⇒ ret_satisfy P (t >>= k)
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λx. (∃t. x = t >>= k) ∨ (ret_satisfy P x)’
  \\ rw[]
  >- metis_tac[]
  >- (Cases_on ‘t’ \\ fs[]
      >- (pop_assum $ qspec_then ‘x’ assume_tac
          \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
          \\ rfs[]
         )
      >- metis_tac[]
      \\ metis_tac[]
     )
  \\ Cases_on ‘a0’ \\ fs[]
  >- (pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ pop_assum $ irule
     )
  >- (pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ disj2_tac
      \\ pop_assum $ irule
     )
  \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
  \\ fs[]
QED

Theorem ret_satisfy_bind_unchanged:
  ret_satisfy (λx. k x = Ret x) t ⇒ (t >>= k) = t
Proof
  rpt strip_tac
  \\ irule $ iffRL itree_bisimulation
  \\ qexists ‘CURRY {t >>= k, t | t, k | ret_satisfy (λx. k x = Ret x) t}’
  \\ rw[]
  >- (qexists ‘(t, k)’
      \\ rw[]
     )
  >- (Cases_on ‘x'’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ simp[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
      \\ qexists ‘(u', r)’ \\ gvs[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
      \\ rpt strip_tac
      \\ qexists ‘(g s, r)’ \\ gvs[]
     )
QED

Theorem ret_satisfy_INR_itree_semantics:
  ∀prog s. ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (prog,s))
Proof
  ho_match_mp_tac panprog_induct
  \\ rw[ret_satisfy_rules, itree_semantics_Annot, itree_semantics_Tick, itree_semantics_Raise, itree_semantics_Return, itree_semantics_Skip,
        itree_semantics_StoreByte, itree_semantics_Store32, itree_semantics_Store, itree_semantics_Continue, itree_semantics_Break]
  >- (rw[itree_semantics_Dec]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Assign]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Seq]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- (rw[itree_semantics_If]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- fs[itree_semantics_While_ret_satisfy_INR]
  >- (rw[itree_semantics_Call]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules, itree_call_handler_def]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r''’ \\ fs[ret_satisfy_rules]
     )
  >- (rw[itree_semantics_DecCall]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules, itree_deccall_handler_def]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r''’ \\ fs[ret_satisfy_rules]
     )
  \\ rw[itree_semantics_ExtCall, itree_semantics_ShMemStore, itree_semantics_ShMemLoad]
  \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
QED

Theorem itree_bisim_impl_wbisim:
  t = t' ⇒ t ≈ t'
Proof rw[itree_wbisim_refl]
QED

Theorem del_annot_preserve_semantics:
  ∀prog s. itree_semantics (prog, s) ≈ itree_semantics (del_annot prog, s)
Proof
  ho_match_mp_tac panprog_induct
  \\ fs[del_annot_def, while_bisim, itree_wbisim_refl]
  \\ rpt strip_tac
  >~ [‘Seq’]
  >- (Cases_on ‘prog’ \\ fs[del_annot_def]
      >~ [‘Seq (Annot _ _)’]
      >- (fs[del_annot_def, itree_semantics_Seq, itree_semantics_Annot]
          \\ irule itree_wbisim_trans
          \\ pop_assum $ irule_at Any
          \\ irule itree_bisim_impl_wbisim
          \\ irule ret_satisfy_bind_unchanged
          \\ irule ret_satisfy_strengthen
          \\ irule_at Any ret_satisfy_INR_itree_semantics
          \\ rw[]
          \\ FULL_CASE_TAC \\ fs[]
         )
      \\ fs[del_annot_def, itree_semantics_Seq, itree_semantics_Skip, itree_semantics_Annot]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
      \\ rpt strip_tac
      \\ EVERY_CASE_TAC
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
  )
  >- (fs[itree_semantics_Dec]
      \\ FULL_CASE_TAC
      \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_t_wbisim
      \\ rw[]
     )
  >- (Cases_on ‘e’ \\ fs[itree_semantics_If]
      \\ EVERY_CASE_TAC \\ gvs[eval_def, itree_wbisim_refl]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
     )
  >- (fs[itree_semantics_DecCall, itree_deccall_handler_def]
      \\ EVERY_CASE_TAC
      \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_k_wbisim
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ rw[]
      \\ EVERY_CASE_TAC \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_t_wbisim \\ fs[itree_wbisim_refl]
     )
  \\ fs[itree_semantics_Skip, itree_semantics_Annot, itree_wbisim_refl]
QED


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


(* Try to open init_array.pnk *)
val (init_array_topdecs, _) = parse_pancake_file “:64” "init_array.pnk"

(* Filter function out *)
Definition is_func:
  is_func (Function _) = T ∧
  is_func _ = F
End

Definition dest_func:
  dest_func (Function f) = f ∧
  dest_func _ = ARB
End

fun topdecs_to_fundecs topdecs =
  let val fun_topdecs = EVAL “FILTER is_func ^topdecs” |> concl |> rhs
      val fundecs = EVAL “MAP dest_func ^fun_topdecs” |> concl |> rhs
  in
    fundecs
  end

val init_array_fundecs = topdecs_to_fundecs init_array_topdecs

Definition file_code_def:
  file_code fundecs = FEMPTY |++ (MAP (λx. (x.name, (x.params, del_annot x.body))) (fundecs))
End

Definition funcname_bodies_def:
  funcname_bodies fundecs = MAP (λx. (x.name, del_annot x.body)) fundecs
End

fun funcname_bodies_list fundecs = EVAL “funcname_bodies ^fundecs” |> concl |> rhs |> dest_list |> fst |> map dest_pair
        
fun codes_lookup_funcs_assms fname fundecs =
  let val funcnames_list = funcname_bodies_list fundecs |> map fst
      val file_code_decs = EVAL “file_code ^fundecs” |> concl |> rhs
      val codes_name_str = concat [fname, "_codes"]
      val codes_name = mk_var(codes_name_str, type_of “file_code ^fundecs”)
      val codes_abbr_def = Define $ single $ ANTIQUOTE $ mk_eq(codes_name, file_code_decs)
      val codes_abbr = codes_abbr_def |> concl |> lhs
  in
    (codes_abbr_def, map (fn x => EVAL “FLOOKUP ^codes_abbr ^x”) funcnames_list)
  end

val (init_codes, init_all_func_lookups) = codes_lookup_funcs_assms "init_array" init_array_fundecs
