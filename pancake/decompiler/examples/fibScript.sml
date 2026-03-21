
Theory fib
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

                     

val (fib_topdecs, _) = parse_pancake_file “:32” "fib.pnk"

val fib_fundecs = topdecs_to_fundecs fib_topdecs

val fib_result = decompile_2_reduce "fib" [] fib_fundecs


val fib_shallow = List.nth (fst fib_result, 0) |> (fn (x,y,z) => x)
                                           

Theorem itree_bind_resp_wbisim_compose_intro:
  t ≈ t' ⇒ (∀r. k r ≈ k' r) ⇒ t'' = t' >>= k' ⇒ t >>= k ≈ t''
Proof
  rw[]
  \\ irule itree_bind_resp_wbisim
  \\ gvs[]
QED

Theorem fib_body_0:
  fib_body [ValWord 0w] s ≈ Ret (INR (SOME (Return (ValWord 1w)),s with locals := FEMPTY))
Proof
  assume_tac fib_shallow
  \\ pop_assum $ qspecl_then [‘0w’, ‘s’] assume_tac
  \\ gvs[itree_wbisim_refl]
QED

Theorem fib_body_1:
  fib_body [ValWord 1w] s ≈ Ret (INR (SOME (Return (ValWord 1w)),s with locals := FEMPTY))
Proof
  assume_tac fib_shallow
  \\ pop_assum $ qspecl_then [‘1w’, ‘s’] assume_tac
  \\ gvs[itree_wbisim_refl]
QED

Theorem fib_body_greater:
  v_x > 1w ⇒
  v_x_1 = v_x - 1w ⇒
  v_x_2 = v_x - 2w ⇒
  s.code = fib_codes ⇒
  (∀s. s.code = fib_codes ⇒
       fib_body [ValWord v_x_1] s ≈ Ret (INR (SOME (Return (ValWord v_curr_1)),s with locals := FEMPTY))) ⇒
  (∀s. s.code = fib_codes ⇒
       fib_body [ValWord v_x_2] s ≈ Ret (INR (SOME (Return (ValWord v_curr_2)),s with locals := FEMPTY))) ⇒
  v_curr_1 + v_curr_2 = v_curr ⇒
  fib_body [ValWord v_x] s ≈ Ret (INR (SOME (Return (ValWord v_curr)),s with locals := FEMPTY))
Proof
  rpt strip_tac
  \\ assume_tac fib_shallow
  \\ pop_assum $ qspecl_then [‘v_x’, ‘s’] assume_tac
  \\ gvs[]
  \\ ‘v_x ≠ 0w’ by (CCONTR_TAC \\ gvs[])
  \\ ‘v_x ≠ 1w’ by (CCONTR_TAC \\ gvs[])
  \\ gvs[]
  \\ irule itree_wbisim_trans
  \\ irule_at Any itree_bisim_impl_wbisim
  \\ first_x_assum $ irule_at Any
  \\ rw[]
  >- (irule ret_satisfy_wbisim_impl
      \\ irule_at Any itree_wbisim_sym
      \\ first_x_assum $ irule_at Any
      \\ gvs[ret_satisfy_Ret]
      \\ irule ret_satisfy_wbisim_impl
      \\ irule_at Any itree_wbisim_sym
      \\ first_x_assum $ irule_at Any
      \\ gvs[ret_satisfy_Ret]
     )
  \\ irule itree_wbisim_trans
  \\ rw[itree_bind_assoc]
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
  \\ rw[Once itree_deccall_handler_def, word_of_val_def, FLOOKUP_SIMP, set_var_defs, shape_of_def, itree_bind_assoc]
  \\ irule itree_wbisim_trans
  \\ rw[itree_bind_assoc]
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
  \\ rw[Once itree_deccall_handler_def, word_of_val_def, FLOOKUP_SIMP,
        res_var_def, set_var_defs, shape_of_def, itree_bind_assoc, itree_wbisim_refl]
QED

Definition fib_def:
  fib (0:num) = (1:num) ∧
  fib 1 = 1 ∧
  fib n = fib (n - 1) + fib (n - 2)
End



Theorem fib_cond_fib:
  ∀v s.
    s.code = fib_codes ⇒
    v < 2 ** 31 ⇒
    fib_body [ValWord (n2w v)] s ≈ Ret (INR (SOME (Return (ValWord (n2w (fib v)))),s with locals := FEMPTY))
Proof
  ho_match_mp_tac fib_ind
  \\ rpt strip_tac
  >- rw[fib_body_0, fib_def]
  >- rw[fib_body_1, fib_def]
  \\ Cases_on ‘v = 0’
  >- rw[fib_body_0, fib_def]
  \\ Cases_on ‘v = 1’
  >- rw[fib_body_1, fib_def]
  \\ gvs[]
  \\ irule_at Any fib_body_greater
  \\ REWRITE_TAC[Once fib_def]
  \\ gvs[]
  \\ ‘(n2w:num -> word32) (fib (v − 1) + fib (v − 2)) = n2w (fib (v − 1)) + n2w (fib (v − 2))’ by gvs[word_add_def, word_add_n2w]
  \\ gvs[]
  \\ irule_at Any EQ_REFL
  \\ subgoal ‘(n2w:num -> word32) (v − 1) = n2w v + -1w’
  >- (rw[word_add_def, word_add_n2w]
      \\ ‘(v - 1) MOD 4294967296 =  (v + 4294967295) MOD 4294967296’ suffices_by rw[]
      \\ irule $ iffLR ADD_MOD
      \\ rw[]
      \\ qexists ‘1’ \\ rw[]
     )
  \\ subgoal ‘(n2w:num -> word32) (v − 2) = n2w v + -2w’
  >- (gvs[word_add_def, word_add_n2w]
      \\ ‘(v - 2) MOD 4294967296 =  (v + 4294967294) MOD 4294967296’ suffices_by rw[]
      \\ irule $ iffLR ADD_MOD
      \\ rw[]
      \\ qexists ‘2’ \\ rw[]
     )
  \\ gvs[word_gt_n2w, bitTheory.NOT_BIT]
  \\ irule bitTheory.BITS_LT_LOW
  \\ rw[]
QED
