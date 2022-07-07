(*
  Correctness proof for word_cse
*)
open preamble alistTheory totoTheory;
open wordLangTheory wordSemTheory wordPropsTheory word_simpTheory word_cseTheory;

val _ = new_theory "word_cseProof";

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_cse"];

Definition data_inv_def:
  data_inv (data:knowledge) (s:('a,'c,'ffi) wordSem$state) ⇔
    (∀r v. lookup r data.map = SOME v ⇒
           get_var r s = get_var v s ∧
           v IN domain data.all_names ∧
           r IN domain data.all_names) ∧
    (∀n c v. lookup data.instrs (instToNumList (Const n c)) = SOME v ⇒
             lookup v s.locals = SOME (Word c) ∧
             v IN domain data.all_names) ∧
    (∀(a:'a arith) v. lookup data.instrs (instToNumList (Arith a)) = SOME v ⇒
                      v IN domain data.all_names ∧
                      ¬is_complex a ∧
                      are_reads_seen a data ∧
                      ∃w. get_var v s = SOME w ∧
                          evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s)) ∧
    (∀op src v. lookup data.instrs (OpCurrHeapToNumList op src) = SOME v ⇒
                v IN domain data.all_names ∧
                is_seen src data ∧
                ∃w. word_exp s (Op op [Var src; Lookup CurrHeap]) = SOME w ∧
                    get_var v s = SOME w) ∧
    map_ok data.instrs
    (*
    (∀r (c:'a word) x v. lookup data.inst_instrs (instToNumList (Const r c)) = SOME x ⇒
           x IN domain data.all_names ∧ get_var x s = SOME (Word c)) ∧
    (∀r v (a:'a arith). lookup data.inst_instrs (instToNumList (Arith a)) = SOME v ∧ firstRegOfArith a = r ⇒
             get_var r s = get_var v s ∧
             r IN domain data.all_names ∧ v IN domain data.all_names)
     *)
End
(* domain_lookup lookup_insert*)

Theorem canonicalRegs_correct[simp]:
  ∀data r s. data_inv data s ⇒ get_var (canonicalRegs data r) s = get_var r s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, canonicalRegs_def]
  \\ fs [lookup_any_def]
  \\ Cases_on ‘lookup r data.map’ \\ fs []
QED

Theorem canonicalRegs_correct_bis[simp]:
  ∀data r s. data_inv data s ⇒ lookup (canonicalRegs data r) s.locals = lookup r s.locals
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, canonicalRegs_def]
  \\ fs [lookup_any_def]
  \\ Cases_on ‘lookup r data.map’ \\ fs [get_var_def]
QED

Theorem canonicalArith_correct[simp]:
  ∀data s a. data_inv data s ⇒ inst (Arith (canonicalArith data a)) s = inst (Arith a) s
Proof
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [canonicalArith_def, inst_def, assign_def, word_exp_def, the_words_def]
  >- (Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘r’ \\ gvs [canonicalImmReg_def, word_exp_def])
  \\ gvs [get_vars_def]
QED

Theorem canonicalExp_correct[simp]:
  ∀data s exp. data_inv data s ⇒ word_exp s (canonicalExp data exp) = word_exp s exp
Proof
  gen_tac \\ gen_tac
  \\ Cases_on ‘exp’
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [canonicalExp_def, word_exp_def]
QED

Theorem firstRegOfArith_canonicalArith[simp]:
  ∀data a. firstRegOfArith (canonicalArith data a) = firstRegOfArith a
Proof
  rpt gen_tac \\ Cases_on ‘a’ \\ gvs [firstRegOfArith_def, canonicalArith_def]
QED

(* Some usefull proofs to automize *)

Theorem lookup_empty[simp]:
  ∀l. lookup (empty listCmp) l = NONE
Proof
  gen_tac
  \\ gvs [mlmapTheory.lookup_def, balanced_mapTheory.lookup_def,
          mlmapTheory.empty_def, balanced_mapTheory.empty_def]
QED

Theorem not_in_all_names_impl:
  ∀r data s. data_inv data s ⇒ ¬is_seen r data ⇒ lookup r data.map = NONE
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, is_seen_def] \\ Cases_on ‘lookup r data.all_names’ \\ gvs []
  \\ Cases_on ‘lookup r data.map’ \\ gvs [] \\ first_x_assum drule_all \\ strip_tac \\ gvs [domain_lookup]
QED

Theorem data_inv_locals[simp]:
  ∀s. s with locals := s.locals = s
Proof
  rpt gen_tac
  \\ gvs [state_component_equality]
QED

Theorem insert_eq:
  ∀(n1:num) n2 v1 v2 l. insert n1 v1 l = insert n1 v2 l ⇔ v1 = v2
Proof
  rpt strip_tac \\ eq_tac \\ gvs [] \\ strip_tac
  \\ ‘lookup n1 (insert n1 v1 l) = lookup n1 (insert n1 v2 l)’ by asm_rewrite_tac []
  \\ gvs []
QED

Theorem evaluate_arith_insert[simp]:
  ∀a w s r v. ¬is_seen r data ⇒
              ¬is_complex a ⇒
              are_reads_seen a data ⇒
              evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s) ⇒
                evaluate (Inst (Arith a), set_var r v s) =
                (NONE, set_var (firstRegOfArith a) w (set_var r v s))
Proof
  rpt strip_tac
  \\ Cases_on ‘a’ \\ gvs [is_complex_def, are_reads_seen_def]
  >- (Cases_on ‘r'’ \\ gvs [are_reads_seen_def]
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def]
      >- (Cases_on ‘n0=r’ \\ gvs [set_var_def, lookup_insert]
          \\ Cases_on ‘n'=r’ \\ gvs [AllCaseEqs(), firstRegOfArith_def]
          \\ gvs [state_component_equality]
          \\ gvs [insert_eq])
      \\ Cases_on ‘n0=r’ \\ gvs [set_var_def, lookup_insert]
      \\ gvs [AllCaseEqs(), firstRegOfArith_def]
      \\ gvs [state_component_equality]
      \\ gvs [insert_eq])
  >- (gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def]
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘OPTION_MAP Word (word_sh s' c n1)’ \\ gvs []
      \\ gvs [set_var_def, lookup_insert]
      \\ Cases_on ‘n0=r’ \\ gvs []
      \\ gvs [state_component_equality, firstRegOfArith_def]
      \\ gvs [insert_eq])
  \\ gvs [evaluate_def, inst_def, assign_def]
  \\ gvs [get_vars_def, get_var_def, set_var_def, lookup_insert]
  \\ Cases_on ‘n1=r’ \\ gvs []
  \\ Cases_on ‘n0=r’ \\ gvs []
  \\ Cases_on ‘lookup n1 s.locals’ \\ gvs []
  \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
  \\ Cases_on ‘x'’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘c' = 0w’ \\ gvs []
  \\ gvs [state_component_equality, firstRegOfArith_def]
  \\ gvs [insert_eq]
QED

Theorem not_seen_data_inv_alist_insert[simp]:
  ∀data s l r v.
    ¬is_seen r data ⇒
    data_inv data (s with locals := l) ⇒
    data_inv data (s with locals := insert r v l)
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ rpt conj_tac
  \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule \\ strip_tac
  >- (gvs [get_var_def, lookup_insert, domain_lookup, is_seen_def]
      \\ Cases_on ‘r'=r’ \\ Cases_on ‘v'=r’ \\ gvs [])
  >- (Cases_on ‘v'=r’ \\ gvs [lookup_insert, domain_lookup, is_seen_def])
  >- (Cases_on ‘v'=r’ \\ gvs [get_var_def, lookup_insert, is_seen_def, domain_lookup]
      \\ assume_tac evaluate_arith_insert \\ gvs [is_seen_def]
      \\ last_x_assum drule \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [set_var_def])
  \\ Cases_on ‘v'=r’ \\ gvs [get_var_def, lookup_insert, is_seen_def, domain_lookup]
  \\ Cases_on ‘src=r’ \\ gvs [word_exp_def, lookup_insert]
QED

Theorem are_reads_seen_insert[simp]:
  ∀a data r. are_reads_seen a data ⇒ are_reads_seen a (data with all_names := insert r () data.all_names)
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
  >- (Cases_on ‘r'’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
      \\ Cases_on ‘lookup n0 data.all_names’ \\ gvs []
      \\ Cases_on ‘lookup n' data.all_names’ \\ gvs []
      \\ Cases_on ‘n0=r’ \\ gvs []
      \\ Cases_on ‘n'=r’ \\ gvs [])
  \\ Cases_on ‘lookup n0 data.all_names’ \\ gvs []
  \\ Cases_on ‘lookup n1 data.all_names’ \\ gvs []
QED

Theorem is_seen_insert[simp]:
  ∀r data r'. is_seen r data ⇒ is_seen r (data with all_names := insert r' () data.all_names)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [is_seen_def, lookup_insert]
  \\ Cases_on ‘r=r'’ \\ gvs []
                            \\ Cases_on ‘lookup r data.all_names’ \\ gvs []
QED

Theorem data_inv_insert_all_names[simp]:
  ∀data s r. data_inv data s ⇒ data_inv (data with all_names:=insert r () data.all_names) s
Proof
  rpt gen_tac
  \\ gvs [data_inv_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rw []
QED

Theorem listCmpEq_correct:
  ∀L1 L2. listCmp L1 L2 = Equal ⇔ L1 = L2
Proof
  strip_tac
  \\Induct_on ‘L1’
    >- (Cases_on ‘L2’
        \\ rw[listCmp_def])
    >- (Cases_on ‘L2’
        >- rw[listCmp_def]
        >- (strip_tac >>
            Cases_on ‘h=h'’
            \\ rw[listCmp_def]))
QED

Theorem antisym_listCmp:
  ∀x y. listCmp x y = Greater ⇔ listCmp y x = Less
Proof
  gen_tac \\ Induct_on ‘x’
  >- (Cases_on ‘y’ \\ gvs [listCmp_def])
  \\ rpt gen_tac
  \\ Cases_on ‘y’ \\ gvs [listCmp_def]
  \\ Cases_on ‘h=h'’ \\ gvs []
  \\ Cases_on ‘h>h'’ \\ gvs []
QED

Theorem transit_listCmp:
  ∀x y z. listCmp x y = Less ∧ listCmp y z = Less ⇒ listCmp x z = Less
Proof
  gen_tac
  \\ Induct_on ‘x’
  >- (Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [listCmp_def])
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [listCmp_def]
  \\ Cases_on ‘h=h'’ \\ Cases_on ‘h'=h''’ \\ gvs [listCmp_def]
  >- (‘listCmp x t = Less ∧ listCmp t t' = Less’ by gvs []
      \\ first_x_assum drule_all \\ gvs [])
  \\ Cases_on ‘h>h'’ \\ Cases_on ‘h'>h''’ \\ gvs []
QED

Theorem TotOrd_listCmp[simp]:
  TotOrd listCmp
Proof
  gvs [TotOrd, listCmpEq_correct, antisym_listCmp, transit_listCmp, SF SFY_ss]
QED

Theorem map_ok_insert[simp]:
  ∀m l v. map_ok m ⇒ map_ok (insert m l v)
Proof
  gvs [mlmapTheory.insert_thm]
QED

Theorem map_ok_empty[simp]:
  map_ok (empty listCmp)
Proof
  gvs [mlmapTheory.empty_thm]
QED

Theorem data_inv_empty[simp]:
  ∀s. data_inv empty_data s
Proof
  gvs [data_inv_def, empty_data_def, lookup_def]
QED

Theorem almost_empty_data[simp]:
  ∀a_n s. data_inv (empty_data with all_names:=a_n) s
Proof
  gvs [data_inv_def, empty_data_def, lookup_def]
QED

(* setting up the goal *)

val goal = “
 λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
   ∀res s' data p' data'.
     evaluate (p, s) = (res, s') ∧ flat_exp_conventions p ∧
     data_inv data s ∧
     res ≠ SOME Error ∧
     word_cse data p  = (data', p') ⇒
     evaluate (p', s) = (res, s') ∧
     (res = NONE ⇒ data_inv data' s')”

local
  val gst = goal |> Ho_Rewrite.PURE_ONCE_REWRITE_CONV [Once PFORALL_THM] |> concl |> rhs
  val ind_thm = evaluate_ind |> ISPEC goal |> GEN_BETA_RULE
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end;

(* proof of the cases *)

Theorem comp_Skip_correct:
  ^(get_goal "Skip")
Proof
  gvs[word_cse_def, evaluate_def]
QED

Theorem comp_Alloc_correct:
  ^(get_goal "Alloc")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, sptreeTheory.lookup_def]
QED

Theorem MAP_FST_lemma[local]:
  ∀moves. MAP FST (MAP (λ(a,b). (a,canonicalRegs data b)) moves) = MAP FST moves
Proof
  Induct \\ gvs []
  \\ gen_tac \\ Cases_on ‘h’ \\ gvs []
QED

Theorem MAP_SND_lemma[local]:
  ∀moves x.
    get_vars (MAP SND moves) s = SOME x ∧ data_inv data s ⇒
    get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s = SOME x
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ gvs [get_vars_def]
  \\ Cases_on ‘get_var r s’ \\ gvs []
  \\ Cases_on ‘get_vars (MAP SND moves) s’ \\ gvs []
QED

(*
Theorem data_inv_insert[local]:
  ∀moves data s q h t.
  ¬MEM q (MAP FST moves) ⇒
  ¬is_seen q data ⇒
  data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
           (s with locals := alist_insert (MAP FST moves) t s.locals) ⇒
  data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
           (s with locals := insert q h (alist_insert (MAP FST moves) t s.locals))
Proof
  Induct
  >- gvs [alist_insert_def]
  \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
  >- (‘∀data s q h.
       ¬MEM q (MAP FST moves) ⇒
       ¬is_seen q data ⇒
       data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
                (s with locals := alist_insert (MAP FST moves) [] s.locals) ⇒
       data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
                (s with locals := insert q h (alist_insert (MAP FST moves) [] s.locals))’
        by gvs [] \\ cheat)
  \\ cheat
     (* may be false, may need more assumptions like ‘get_vars (MAP SND moves) s = t’ *)
QED
*)

Theorem lookup_map_insert:
  ∀xs r. lookup r (map_insert xs m) = case ALOOKUP xs r of NONE => lookup r m | SOME r' => SOME r'
Proof
  cheat
QED

Theorem get_set_vars_lemma:
  ∀xs xs' x y s. ¬MEM x xs ∧ ¬MEM y xs ⇒ get_var x (set_vars xs xs' s) = get_var y (set_vars xs xs' s)
Proof
  cheat
QED

Theorem comp_Move_correct:
  ^(get_goal "Move")
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [evaluate_def, word_cse_def]
  \\ Cases_on ‘ALL_DISTINCT (MAP FST moves)’ \\ gvs [flat_exp_conventions_def]
  \\ Cases_on ‘get_vars (MAP SND moves) s’ \\ gvs []
  \\ pairarg_tac \\ gvs [canonicalMoveRegs3_def]
  \\ ‘rs' = MAP (λ(a,b). (a,canonicalRegs data b)) moves’ by gvs [AllCaseEqs()]
  \\ gvs [evaluate_def, MAP_FST_lemma]
  \\ drule_all MAP_SND_lemma
  \\ strip_tac \\ gvs []
  \\ gvs [AllCaseEqs()]
  (*\\ gvs [EVERY_MEM, FORALL_PROD]*)
  \\ gvs [data_inv_def]
  (* print_match [] “domain (list_insert _ _)” *)
  \\ gvs [domain_list_insert]
  \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_map_insert, AllCaseEqs()]
      >- (gvs [ALOOKUP_NONE, MEM_MAP, MEM_FILTER, FORALL_PROD, EXISTS_PROD]
          \\ last_x_assum drule \\ strip_tac
          \\ gvs []
          \\ irule get_set_vars_lemma
          \\ CCONTR_TAC \\ gvs [MEM_MAP, EXISTS_PROD, EVERY_MEM]
          \\ first_x_assum drule \\ gvs [is_seen_def, domain_lookup])
      \\ drule ALOOKUP_MEM \\ strip_tac
      \\ gvs [MEM_FILTER, MEM_MAP, EXISTS_PROD]
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]



  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘data’
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘moves’
  \\ Induct
  >- gvs [set_vars_def, canonicalMoveRegs_aux_def, alist_insert_def, data_inv_locals]
  \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ gvs []
  \\ gvs [canonicalMoveRegs_aux_def]
  \\ IF_CASES_TAC
  >- (pop_assum kall_tac
      \\ gvs [set_vars_def]
      \\ rpt gen_tac
      \\ Cases_on ‘x’ \\ gvs [alist_insert_def]
      >- (gvs [get_vars_def]
          \\ Cases_on ‘get_var r s’ \\ gvs []
          \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs [])
      \\ irule data_inv_insert \\ gvs []
      \\ last_x_assum irule \\ gvs [get_vars_def]
      \\ Cases_on ‘get_var r s’ \\ gvs []
      \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs []
      \\ rpt (first_x_assum mp_tac)
      \\ qid_spec_tac ‘t’
      \\ Induct_on ‘moves’ \\ gvs []
      \\ rpt strip_tac
      \\ Cases_on ‘get_vars (SND h'::MAP SND moves) s’ \\ gvs []
     )

  \\ gvs [set_vars_def, get_vars_def, AllCaseEqs()]
  \\ gvs [alist_insert_def]

  \\ qabbrev_tac ‘data1 = data with <|map := insert q (canonicalRegs data r) data.map;
                                      all_names := insert q () data.all_names|>’

  \\ qsuff_tac ‘data_inv
                (canonicalMoveRegs_aux
                 (data with
                  <|map := insert q (canonicalRegs data r) data.map;
                    all_names := insert q () data.all_names|>)
                 (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
                ((s with locals := insert q x' s.locals) with
                 locals := (alist_insert (MAP FST moves) xs (s with locals := insert q x' s.locals).locals))’
  >- cheat (* easier *)
  \\ cheat

     (*
  \\ last_x_assum irule

  \\ ‘data_inv (data with <|map := insert q (canonicalRegs data r) data.map; all_names := insert q () data.all_names|>)
               (s with locals := insert q x' s.locals)’ by cheat
  \\ last_x_assum drule
  \\ disch_then (qspec_then ‘xs’ mp_tac)
  \\ impl_tac

  \\ Cases_on ‘get_var r s’ \\ gvs []
  \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs []
  \\ gvs [data_inv_def] \\ rpt strip_tac
  >- (first_x_assum (drule_at Any) \\ strip_tac \\ gvs [get_var_def, lookup_insert]
      \\ Cases_on ‘r' = q’ \\ gvs []
      \\ Cases_on ‘v = q’ \\ gvs [] \\ cheat)
  (* Proof hard stuck *)
  \\ cheat
     *)
QED

Theorem comp_Inst_correct:
  ^(get_goal "Inst")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on ‘i’
  >- (* Skip *)
   ( gvs [evaluate_def, data_inv_def, word_cse_def, word_cseInst_def,
          inst_def, flat_exp_conventions_def]
     \\ strip_tac
     \\ rw [] \\ gvs []
     \\ first_x_assum (drule_at Any) \\ gvs [] )

  >- (* Const *)
   ( gvs [evaluate_def, word_cse_def, word_cseInst_def]
     \\ pairarg_tac \\ gvs []
     \\ Cases_on ‘is_seen n data’ \\ gvs [evaluate_def, add_to_data_def, add_to_data_aux_def]
     \\ Cases_on ‘lookup data.instrs (instToNumList (Const n c))’ \\ gvs[evaluate_def]
     >- ( gvs [inst_def, assign_def, word_exp_def, data_inv_def]
          \\ strip_tac
          >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac
              \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup]
              \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [is_seen_def])
          \\ strip_tac
          >- (rpt gen_tac \\ gvs [set_var_def, lookup_insert, domain_lookup]
              \\ Cases_on ‘c = c'’ \\ gvs [instToNumList_def, wordToNum_def, mlmapTheory.lookup_insert, word_exp_def]
              \\ strip_tac \\ first_x_assum drule_all
              \\ strip_tac \\ Cases_on ‘v = n’ \\ gvs [is_seen_def])
          \\ strip_tac
          >- (rpt gen_tac \\ gvs [instToNumList_def, arithToNumList_def, mlmapTheory.lookup_insert]
              \\ strip_tac \\ first_assum drule_all \\ strip_tac
              \\ Cases_on ‘v=n’
              >- gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, is_seen_def]
              \\ Cases_on ‘a’ \\ gvs [is_complex_def, get_var_def, set_var_def, lookup_insert]

              >- (last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ Cases_on ‘n0=n’
                  \\ Cases_on ‘r=Reg n’
                  >- (cheat)
                  >- (cheat)
                  >- (cheat)
                  >- (cheat)
                 )
              >- (last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ last_x_assum kall_tac
                  \\ Cases_on ‘n0=n’
                  >- (cheat)
                  >- (cheat)
                 )
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ Cases_on ‘n0=n’
              \\ Cases_on ‘n1=n’
              >- (cheat)
              >- (cheat)
              >- (cheat)
              >- (cheat)
             )
        \\ cheat
        )
     \\ Cases_on ‘inst (Const n c) s’ \\ gvs [inst_def, assign_def, word_exp_def, data_inv_def]
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ gvs [get_vars_def, get_var_def, set_vars_def, alist_insert_def, set_var_def])
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ rpt gen_tac
         \\ gvs [lookup_insert]
         \\ Cases_on ‘r = n’ \\ strip_tac \\ gvs []
         >- (Cases_on ‘n=v’ \\ gvs [set_var_def, get_var_def, lookup_insert])
         \\ gvs [set_var_def, get_var_def, lookup_insert]
         \\ first_x_assum drule_all \\ strip_tac \\ gvs []
         \\ Cases_on ‘v = n’ \\ gvs [domain_lookup, is_seen_def])
     \\ strip_tac
     >- (first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
         \\ strip_tac \\ gvs [set_var_def, lookup_insert, domain_lookup, is_seen_def]
         \\ Cases_on ‘v=n’ \\ gvs [] )
     \\ strip_tac
     >- (first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
         \\ strip_tac \\ gvs [set_var_def, get_var_def, lookup_insert, domain_lookup, is_seen_def]
         \\ Cases_on ‘v = n’ \\ gvs []
         \\ cheat)
     \\ first_x_assum drule_all \\ strip_tac
     \\ rpt gen_tac \\ strip_tac
     \\ first_x_assum drule_all \\ strip_tac \\ gvs[get_var_def, set_var_def, lookup_insert]
     \\ Cases_on ‘v=n’ \\ Cases_on ‘src=n’ \\ gvs [domain_lookup]
     \\ cheat
   )

  >- (* Arith *)
   ( gvs [word_cse_def, word_cseInst_def]
     \\ pairarg_tac \\ gvs []
     \\ Cases_on ‘is_seen (firstRegOfArith a) data’ \\ gvs []
     \\ Cases_on ‘lookup data.instrs (instToNumList (Arith (canonicalArith data a)))’ \\ gvs [evaluate_def]
     >- ( strip_tac \\ cases_on ‘inst (Arith a) s’ \\ gvs []
          \\ gvs [data_inv_def]
          \\ strip_tac
          >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac
              \\ Cases_on ‘a’ \\ gvs [inst_def, assign_def]
              >- (Cases_on ‘word_exp s (Op b [Var n0; case r' of Reg r3 => Var r3 | Imm w => Const w])’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘word_exp s (Shift s'' (Var n0) n1)’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘get_vars [n1; n0] s’ \\ gvs [get_var_def, set_var_def]
                  \\ Cases_on ‘x’ \\ gvs []
                  \\ Cases_on ‘t’ \\ gvs []
                  \\ Cases_on ‘h'’ \\ gvs []
                  \\ Cases_on ‘h’ \\ gvs []
                  \\ Cases_on ‘t'’ \\ gvs []
                  \\ gvs [lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs []
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup])
              >- (Cases_on ‘get_vars [n1; n2] s’
                  \\ gvs [get_var_def, set_var_def, lookup_insert]
                  \\ Cases_on ‘x’ \\ gvs []
                  \\ Cases_on ‘t’ \\ gvs []
                  \\ Cases_on ‘h'’ \\ gvs []
                  \\ Cases_on ‘h’ \\ gvs []
                  \\ Cases_on ‘t'’ \\ gvs []
                  \\ gvs [lookup_insert]
                  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup]
                  \\ Cases_on ‘r=n0’ \\ Cases_on ‘v=n0’ \\ gvs [word_exp_def]
                  \\ gvs [firstRegOfArith_def, is_seen_def, domain_lookup]
                  \\ cheat)
              >- (cheat)
              >- (cheat)
              >- (cheat)
              >- (cheat)
             )
          \\ cheat)
     \\ cheat
   )
  >- (* Mem *)
   ( Cases_on ‘a’
   \\ gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def, empty_data_def, lookup_def] )
  >- (* FP *)
   ( gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def, empty_data_def, lookup_def] )
QED

Theorem comp_Assign_correct:
  ^(get_goal "Assign")
Proof
  fs[flat_exp_conventions_def]
QED

Theorem comp_Get_correct:
  ^(get_goal "Get")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘is_seen v data’ \\ gvs [evaluate_def]
  >- gvs [empty_data_def, lookup_def, lookup_empty, sptreeTheory.lookup_def]
  \\ strip_tac
  \\ Cases_on ‘FLOOKUP s.store name’ \\ gvs[]
  \\ fs [get_var_def, set_var_def]
  \\ fs [lookup_insert, is_seen_def]
  \\ Cases_on ‘lookup v data.all_names’ \\ gvs [domain_lookup]
  \\ strip_tac
  >- metis_tac [NOT_NONE_SOME]
  \\ strip_tac
  >- metis_tac [NOT_NONE_SOME]
  \\ cheat
QED
(* similare cases : Loc *)

Theorem comp_Set_correct:
  ^(get_goal "wordLang$Set")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def]
  \\ Cases_on ‘exp’ \\ gvs [flat_exp_conventions_def]
  \\ Cases_on ‘v=CurrHeap’ \\ gvs [evaluate_def]
  \\ Cases_on ‘v = Handler ∨ v = BitmapBase’ \\ gvs [word_exp_def]
  \\ strip_tac
  \\ Cases_on ‘lookup n s.locals’ \\ gvs [set_store_def, get_var_def]
  \\ gvs [data_inv_def, get_var_def]
  \\ strip_tac
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac \\ gvs [])
  \\ strip_tac
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac \\ gvs [])
  \\ strip_tac
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac \\ gvs []
      \\ Cases_on ‘a’ \\ gvs [is_complex_def, firstRegOfArith_def]
      >- (gvs [evaluate_def, inst_def, assign_def] \\ Cases_on ‘r’ \\ gvs [word_exp_def, the_words_def]
          \\ gvs [AllCaseEqs()]
          \\ gvs [set_var_def, state_component_equality])
      \\ gvs [evaluate_def, inst_def, assign_def] \\ gvs [word_exp_def, the_words_def, get_vars_def, get_var_def]
      \\ gvs [AllCaseEqs()]
      \\ gvs [set_var_def, state_component_equality])
  \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [word_exp_def, the_words_def, FLOOKUP_UPDATE]
QED

Theorem comp_OpCurrHeap_correct:
  ^(get_goal "OpCurrHeap")
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
  \\ Cases_on ‘is_seen dst data’ \\ gvs []
  \\ Cases_on ‘is_seen src data’ \\ gvs []
  \\ gvs [add_to_data_aux_def]
  \\ Cases_on ‘lookup data.instrs (OpCurrHeapToNumList b (canonicalRegs data src))’ \\ gvs []
  >- (gvs [evaluate_def, word_exp_def]
      \\ strip_tac \\ gvs []
      \\ gvs [AllCaseEqs()]
      \\ gvs [data_inv_def]
      \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
      >- (first_x_assum drule \\ strip_tac
          \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, is_seen_def]
          \\ Cases_on ‘r=dst’ \\ Cases_on ‘v=dst’ \\ gvs [])
      >- (gvs [mlmapTheory.lookup_insert, OpCurrHeapToNumList_def, instToNumList_def]
          \\ gvs [the_words_def, AllCaseEqs()]
          \\ first_x_assum drule \\ strip_tac \\ gvs []
          \\ Cases_on ‘v=dst’ \\ gvs [set_var_def, lookup_insert, domain_lookup, is_seen_def])
      >- (gvs [mlmapTheory.lookup_insert, OpCurrHeapToNumList_def, instToNumList_def]
          \\ first_x_assum drule \\ strip_tac \\ gvs []
          \\ Cases_on ‘a’ \\ gvs [is_complex_def, are_reads_seen_def, is_seen_def]
          >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
              \\ gvs [lookup_insert]
              \\ Cases_on ‘n0=dst’ \\ gvs []
              \\ gvs [get_var_def, set_var_def, lookup_insert]
              \\ Cases_on ‘v=dst’ \\ gvs [domain_lookup]
              \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, lookup_insert]
              \\ gvs [AllCaseEqs(), set_var_def, firstRegOfArith_def]
              \\ gvs [state_component_equality]
              >- (Cases_on ‘n'=dst’ \\ gvs [] \\ cheat)
              \\ cheat
             )
          >- (gvs [lookup_insert, get_var_def, set_var_def, evaluate_def, firstRegOfArith_def]
              \\ Cases_on ‘n0=dst’ \\ gvs []
              \\ Cases_on ‘v=dst’ \\ gvs [inst_def, assign_def, word_exp_def, the_words_def]
              \\ gvs [lookup_insert, AllCaseEqs()]
              \\ gvs [set_var_def, state_component_equality]
      )
  \\ Cases_on ‘word_exp s (Op b [Var src; Lookup CurrHeap])’ \\ gvs []
  \\ Cases_on ‘lookup dst data.all_names ≠ NONE’ \\ gvs [evaluate_def]
  \\ Cases_on ‘lookup data.instrs (OpCurrHeapToNumList b (canonicalRegs data src))’
  \\ gvs [evaluate_def, word_exp_def]
  >- (gvs [the_words_def]
      \\ Cases_on ‘lookup src s.locals’ \\ gvs []
      \\ Cases_on ‘x'’ \\ gvs []
      \\ Cases_on ‘FLOOKUP s.store CurrHeap’ \\ gvs []
      \\ Cases_on ‘x'’ \\ gvs []

      \\ gvs [data_inv_def]
      \\ strip_tac
      >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule_all \\ strip_tac
          \\ gvs [get_var_def, set_var_def, lookup_insert]
          \\ Cases_on ‘r = dst’ \\ Cases_on ‘v = dst’ \\ gvs []
          \\ cheat
         )
      \\ cheat
  )
  \\ cheat
QED

Theorem comp_Store_correct:
  ^(get_goal "Store")
Proof
  fs[flat_exp_conventions_def]
QED

Theorem comp_Tick_correct:
  ^(get_goal "Tick")
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs[word_cse_def, evaluate_def]
  \\ Cases_on ‘s.clock = 0’ \\ gvs []
  \\ fs [get_var_def, dec_clock_def, data_inv_def]
  \\ rw []
  \\ first_assum drule_all \\ gs []
  \\ first_x_assum drule_all \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [is_complex_def]
  \\ gvs [evaluate_def, inst_def, firstRegOfArith_def, word_exp_def, the_words_def]
  \\ gvs [AllCaseEqs()]
QED

Theorem data_inv_clock:
  ∀data s c td. data_inv data s ⇒ data_inv data (s with <|clock := c; termdep := td |>)
Proof
  rpt gen_tac \\ strip_tac \\ gvs [data_inv_def]
  \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule \\ strip_tac
      \\ gvs [get_var_def])
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule \\ strip_tac
      \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ first_x_assum drule \\ strip_tac
      \\ gvs [get_var_def, set_var_def]
      \\ Cases_on ‘a’ \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, is_complex_def]
      >- (Cases_on ‘r’ \\ gvs [word_exp_def, set_var_def, firstRegOfArith_def, AllCaseEqs()]
          \\ gvs [state_component_equality])
      >- (gvs [set_var_def, firstRegOfArith_def, AllCaseEqs()] \\ gvs [state_component_equality])
      \\ gvs [get_vars_def, get_var_def, AllCaseEqs(), set_var_def]
      \\ gvs [state_component_equality])
  \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule \\ strip_tac
  \\ gvs [get_var_def, word_exp_def]
QED

Theorem comp_MustTerminate_correct:
  ^(get_goal "MustTerminate")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ gs[word_cse_def]
  \\ pairarg_tac \\ gvs [evaluate_def,flat_exp_conventions_def]
  \\ gvs [AllCaseEqs()]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum (drule_at Any)
  \\ Cases_on ‘res'' = SOME TimeOut’ \\ gvs []
  \\ impl_tac
  >- gvs [data_inv_clock]
  \\ rpt (strip_tac \\ gvs [data_inv_clock])
QED

Theorem comp_Seq_correct:
  ^(get_goal "wordLang$Seq")
Proof
  rpt gen_tac \\
  strip_tac \\
  rpt gen_tac \\
  strip_tac \\
  gvs[word_cse_def, evaluate_def, flat_exp_conventions_def] \\
  rpt (pairarg_tac \\ gvs []) \\
  reverse(gvs [AllCaseEqs(),evaluate_def])
  >- (pairarg_tac \\ gvs [] \\
      first_x_assum drule_all \\ gs []) \\
  pairarg_tac \\ gvs [] \\
  first_x_assum drule_all \\ gs [] \\
  strip_tac \\ gvs [] \\
  first_x_assum drule_all \\
  fs []
QED

Theorem comp_Return_correct:
  ^(get_goal "Return")
Proof
  fs[word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED

Theorem comp_Raise_correct:
  ^(get_goal "wordLang$Raise")
Proof
  fs[word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED

Theorem comp_If_correct:
  ^(get_goal "wordLang$If")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ simp_tac std_ss [evaluate_def, AllCaseEqs(), word_cse_def, LET_THM]
  \\ rpt (pairarg_tac \\ simp [])
  \\ strip_tac
  \\ gvs [evaluate_def]
  \\ ‘get_var_imm (canonicalImmReg data ri) s = get_var_imm ri s’ by
    (Cases_on ‘ri’ \\ fs [get_var_imm_def, canonicalImmReg_def])
  \\ fs [flat_exp_conventions_def]
  \\ first_x_assum drule_all
  \\ rw []
  \\ simp [data_inv_def, empty_data_def, get_var_def, lookup_def]
QED

Theorem comp_LocValue_correct:
  ^(get_goal "wordLang$LocValue")
Proof
  gvs[word_cse_def, data_inv_def, evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘is_seen r data’ \\ gvs [evaluate_def]
  >- gvs [empty_data_def, lookup_def]
  \\ strip_tac
  \\ Cases_on ‘l1 ∈ domain s.code’ \\ gvs[]
  \\ fs [get_var_def, set_var_def]
  \\ fs [lookup_insert, is_seen_def]
  \\ Cases_on ‘lookup r data.all_names’ \\ gvs [domain_lookup]
  \\ metis_tac [NOT_NONE_SOME]
QED

(* DATA EMPTY *)

Theorem comp_Install_correct:
  ^(get_goal "wordLang$Install")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_CodeBufferWrite_correct:
  ^(get_goal "wordLang$CodeBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_DataBufferWrite_correct:
  ^(get_goal "wordLang$DataBufferWrite")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_FFI_correct:
  ^(get_goal "wordLang$FFI")
Proof
  gvs[word_cse_def, data_inv_def, empty_data_def, lookup_def]
QED

Theorem comp_Call_correct:
  ^(get_goal "wordLang$Call")
Proof
  rpt gen_tac \\ strip_tac
  \\ rpt (pop_assum kall_tac)
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
QED

(* DATA EMPTY *)

Theorem comp_correct:
  ^(compile_correct_tm ())
Proof
  match_mp_tac (the_ind_thm()) >>
  rpt conj_tac >>
  MAP_FIRST MATCH_ACCEPT_TAC
    [comp_Skip_correct,comp_Alloc_correct,comp_Move_correct,comp_Inst_correct,comp_Assign_correct,
     comp_Get_correct,comp_Set_correct,comp_Store_correct,comp_Tick_correct,comp_MustTerminate_correct,
     comp_Seq_correct,comp_Return_correct,comp_Raise_correct,comp_If_correct,comp_LocValue_correct,
     comp_Install_correct,comp_CodeBufferWrite_correct,comp_DataBufferWrite_correct,
     comp_FFI_correct,comp_OpCurrHeap_correct,comp_Call_correct
    ]
QED

val _ = export_theory();
