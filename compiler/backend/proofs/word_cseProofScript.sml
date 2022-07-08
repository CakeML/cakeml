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

Theorem are_reads_seen_canonical[simp]:
  ∀a data s. data_inv data s ⇒ ¬is_complex a ⇒ are_reads_seen (canonicalArith data a) data = are_reads_seen a data
Proof
  rpt strip_tac
  \\ Cases_on ‘a’ \\ gvs [canonicalArith_def, is_complex_def]
  >- (reverse (Cases_on ‘r’) \\ gvs [canonicalRegs_def, canonicalImmReg_def, are_reads_seen_def]
      \\ gvs [lookup_any_def, is_seen_def]
      >- (Cases_on ‘lookup n0 data.map’ \\ gvs [data_inv_def]
          \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac
          \\ gvs [domain_lookup])
      \\ Cases_on ‘lookup n0 data.map’ \\ gvs []
      >- (Cases_on ‘lookup n' data.map’ \\ gvs [data_inv_def]
          \\ first_x_assum drule \\ strip_tac \\ gvs [domain_lookup])
      \\ gvs [data_inv_def]
      \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac \\ gvs [domain_lookup]
      \\ Cases_on ‘lookup n' data.map’ \\ gvs []
      \\ first_x_assum drule \\ strip_tac \\ gvs [domain_lookup])
  \\ gvs [are_reads_seen_def, is_seen_def, canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup n0 data.map’ \\ gvs [data_inv_def]
  >- (first_x_assum drule \\ strip_tac \\ gvs [domain_lookup])
  >- (Cases_on ‘lookup n1 data.map’ \\ gvs []
      \\ first_x_assum drule \\ strip_tac \\ gvs [domain_lookup])
  \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac \\ gvs [domain_lookup]
  \\ Cases_on ‘lookup n1 data.map’ \\ gvs [] \\ first_x_assum drule \\ strip_tac \\ gvs [domain_lookup]
QED

Theorem is_complex_canonical[simp]:
  ∀data a. is_complex (canonicalArith data a) = is_complex a
Proof
  Cases_on ‘a’ \\ gvs [canonicalArith_def, is_complex_def]
QED

Theorem wordToNum_unique[simp]:
  ∀c1 c2. wordToNum c1 = wordToNum c2 ⇔ c1 = c2
Proof
  gvs [wordToNum_def]
QED

Theorem arithOpToNum_eq[simp]:
  ∀op1 op2. arithOpToNum op1 = arithOpToNum op2 ⇔ op1 = op2
Proof
  strip_tac
  \\ Cases_on ‘op1’ \\ Cases_on ‘op2’ \\ gvs [arithOpToNum_def]
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
      \\ rpt (first_x_assum drule \\ strip_tac)
      \\ gvs [set_var_def])
  \\ Cases_on ‘v'=r’ \\ gvs [get_var_def, lookup_insert, is_seen_def, domain_lookup]
  \\ Cases_on ‘src=r’ \\ gvs [word_exp_def, lookup_insert]
QED

Theorem are_reads_seen_insert[simp]:
  ∀a data r. are_reads_seen a data ⇒
             are_reads_seen a (data with all_names := insert r () data.all_names)
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

Theorem are_reads_seen_insert_instrs[simp]:
  ∀a data n l. are_reads_seen a data ⇒
               are_reads_seen a (data with <| instrs:= l ;
                                              all_names:=insert n () data.all_names |>)
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
  >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
      \\ Cases_on ‘lookup n0 data.all_names’ \\ gvs []
      \\ Cases_on ‘n0=n’ \\ gvs []
      \\ Cases_on ‘lookup n'' data.all_names’ \\ gvs []
      \\ Cases_on ‘n''=r’ \\ gvs [])
  \\ Cases_on ‘lookup n0 data.all_names’ \\ gvs []
  \\ Cases_on ‘lookup n1 data.all_names’ \\ gvs []
QED

Theorem are_reads_seen_insert_map[simp]:
  ∀a data n l. are_reads_seen a data ⇒
               are_reads_seen a (data with <| map:= l ;
                                              all_names:=insert n () data.all_names |>)
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
  >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
      \\ Cases_on ‘lookup n0 data.all_names’ \\ gvs []
      \\ Cases_on ‘n0=n’ \\ gvs []
      \\ Cases_on ‘lookup n'' data.all_names’ \\ gvs []
      \\ Cases_on ‘n''=r’ \\ gvs [])
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
  Induct
  >- gvs [map_insert_def, ALOOKUP_def]
  \\ rpt gen_tac
  \\ Cases_on ‘h’ \\ gvs [map_insert_def, lookup_insert]
  \\ Cases_on ‘r=q’ \\ gvs []
QED

Theorem get_set_vars_lemma:
  ∀xs xs' x y s. ¬MEM x xs ∧ ¬MEM y xs ⇒
                 get_var x s = get_var y s ⇒
                 get_var x (set_vars xs xs' s) = get_var y (set_vars xs xs' s)
Proof
  Induct
  >- rw [set_vars_def, alist_insert_def]
  \\ rpt strip_tac
  \\ Cases_on ‘xs'’
  >- rw [set_vars_def, alist_insert_def]
  \\ gvs [set_vars_def, alist_insert_def, get_var_def, lookup_insert]
QED

Theorem get_set_vars_not_in[local]:
  ∀rs vs r s. ¬MEM r rs ⇒ get_var r (set_vars rs vs s) = get_var r s
Proof
  Induct \\ gvs [set_vars_def]
  >- gvs [alist_insert_def, get_var_def]
  \\ rpt strip_tac
  \\ gvs [get_var_def]
  \\ Cases_on ‘vs’ \\ gvs [alist_insert_def, lookup_insert]
QED

Theorem MEM_FST_reduc:
  ∀moves r p_2. MEM (r,p_2) moves ⇒ MEM r (MAP FST moves)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  >- (Cases_on ‘h’ \\ gvs [])
  \\ first_x_assum drule \\ rw []
QED

Theorem get_set_vars_in[local]:
  ∀moves r p_2 x s.
    MEM (r,p_2) moves ⇒
    ALL_DISTINCT (MAP FST moves) ⇒
    get_vars (MAP SND moves) s = SOME x ⇒
    get_var r (set_vars (MAP FST moves) x s) = get_var p_2 s
Proof
  Induct \\ gvs [set_vars_def]
  \\ rpt strip_tac
  >- (Cases_on ‘x’ \\ gvs [alist_insert_def, get_vars_def, AllCaseEqs()]
      \\ gvs [get_var_def, lookup_insert])
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [alist_insert_def, get_var_def]
  \\ Cases_on ‘h’ \\ gvs [lookup_insert]
  \\ drule MEM_FST_reduc \\ strip_tac
  \\ Cases_on ‘r=q’ \\ gvs []
QED

Theorem get_set_vars_in_2[local]:
  ∀moves r p_2 x' x data s.
    MEM (r,p_2) moves ⇒
    ALL_DISTINCT (MAP FST moves) ⇒
    lookup p_2 data.map = SOME x' ⇒
    get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s = SOME x ⇒
    get_var r (set_vars (MAP FST moves) x s) = get_var x' s
Proof
  Induct \\ gvs [set_vars_def]
  \\ rpt strip_tac
  >- (Cases_on ‘x’ \\ gvs [alist_insert_def, get_vars_def, AllCaseEqs()]
      \\ gvs [get_var_def, lookup_insert, canonicalRegs_def, lookup_any_def])
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [alist_insert_def, get_var_def]
  \\ Cases_on ‘h’ \\ gvs [lookup_insert]
  \\ drule MEM_FST_reduc \\ strip_tac
  \\ Cases_on ‘r=q’ \\ gvs [canonicalRegs_def, lookup_any_def]
QED

val insert_insert = store_thm("insert_insert",
  ``!x1 x2 v1 v2 t.
      insert x1 v1 (insert x2 v2 t) =
      if x1 = x2 then insert x1 v1 t else insert x2 v2 (insert x1 v1 t)``,
  rpt strip_tac
  \\ qspec_tac (`x1`,`x1`)
  \\ qspec_tac (`v1`,`v1`)
  \\ qspec_tac (`t`,`t`)
  \\ qspec_tac (`v2`,`v2`)
  \\ qspec_tac (`x2`,`x2`)
  \\ recInduct insert_ind \\ rpt strip_tac \\
    (Cases_on `k = 0` \\ fs [] THEN1
     (once_rewrite_tac [insert_def] \\ fs [] \\ rw []
      THEN1 (once_rewrite_tac [insert_def] \\ fs [])
      \\ once_rewrite_tac [insert_def] \\ fs [] \\ rw [])
    \\ once_rewrite_tac [insert_def] \\ fs [] \\ rw []
    \\ simp [Once insert_def]
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ simp [Once insert_def]
    \\ Cases_on `x1` \\ fs [ADD1]
    \\ Cases_on `k` \\ fs [ADD1]
    \\ rw [] \\ fs [EVEN_ADD]
    \\ fs [GSYM ODD_EVEN]
    \\ fs [EVEN_EXISTS,ODD_EXISTS] \\ rpt BasicProvers.var_eq_tac
    \\ fs [ADD1,DIV_MULT|>ONCE_REWRITE_RULE[MULT_COMM],
                MULT_DIV|>ONCE_REWRITE_RULE[MULT_COMM]]));

Theorem lookup_set_vars_not_in[local]:
  ∀moves v data c x.
    ¬MEM v (MAP FST moves) ⇒
    lookup v s.locals = SOME (Word c) ⇒
    lookup v (set_vars (MAP FST moves) x s).locals = SOME (Word c)
Proof
  Induct \\ gvs [set_vars_def]
  >- gvs [alist_insert_def, get_var_def]
  \\ rpt strip_tac
  \\ gvs [get_var_def]
  \\ Cases_on ‘x’ \\ gvs [alist_insert_def, lookup_insert]
QED

Theorem list_insert_insert[local]:
  ∀l n an. list_insert l (insert n () an) = insert n () (list_insert l an)
Proof
  Induct \\ gvs [list_insert_def]
  \\ rpt gen_tac
  \\ Cases_on ‘h=n’ \\ gvs []
  \\ qspecl_then [‘h’, ‘n’, ‘()’, ‘()’, ‘list_insert l an’] assume_tac insert_insert
  \\ gvs []
QED

Theorem are_reads_seen_insert_list[local]:
  ∀l a data m.
    ¬is_complex a ⇒
    are_reads_seen a data ⇒
    are_reads_seen a (data with <| map:= m ;
                                   all_names:=list_insert l data.all_names |>)
Proof
  Induct \\ rpt strip_tac \\ gvs [list_insert_def]
  \\ Cases_on ‘a’ \\ gvs [is_complex_def, are_reads_seen_def, is_seen_def]
  >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def])
  >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
      \\ gvs [list_insert_insert, lookup_insert]
      >- (‘¬is_complex (Binop Add n n0 (Reg n'))’ by gvs [is_complex_def]
          \\ last_x_assum drule \\ strip_tac
          \\ gvs [are_reads_seen_def, is_seen_def]
          \\ pop_assum drule_all \\ strip_tac
          \\ Cases_on ‘n0=h’ \\ Cases_on ‘n'=h’ \\ gvs [])
      \\ ‘¬is_complex (Binop Add n n0 (Imm x))’ by gvs [is_complex_def]
      \\ last_x_assum drule \\ strip_tac
      \\ gvs [are_reads_seen_def, is_seen_def]
      \\ pop_assum drule_all \\ strip_tac
      \\ Cases_on ‘n0=h’ \\ gvs [])
  >- (‘¬is_complex (Shift s d n0 x)’ by gvs [is_complex_def]
      \\ last_x_assum drule \\ strip_tac
      \\ gvs [are_reads_seen_def, is_seen_def, list_insert_insert]
      \\ pop_assum drule_all \\ strip_tac
      \\ Cases_on ‘n0=h’ \\ gvs [lookup_insert])
  \\ ‘¬is_complex (Div n n0 n1)’ by gvs [is_complex_def]
  \\ last_x_assum drule \\ strip_tac
  \\ gvs [are_reads_seen_def, is_seen_def, list_insert_insert]
  \\ pop_assum drule_all \\ strip_tac
  \\ Cases_on ‘n0=h’ \\ Cases_on ‘n1=h’ \\ gvs [lookup_insert]
QED

Theorem evaluate_arith_insert_list[local]:
  ∀x a w s y. (∀p. MEM p x ⇒ ¬is_seen p data) ⇒
              ¬is_complex a ⇒
              are_reads_seen a data ⇒
              evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s) ⇒
              evaluate (Inst (Arith a), set_vars x y s) =
              (NONE, set_var (firstRegOfArith a) w (set_vars x y s))
Proof
  Induct \\ gvs [set_vars_def, alist_insert_def]
  \\ rpt strip_tac
  \\ ‘∀p. MEM p x ⇒ ¬is_seen p data’ by metis_tac []
  \\ last_x_assum drule_all \\ strip_tac
  \\ Cases_on ‘y’ \\ gvs [alist_insert_def]
  \\ first_x_assum (qspec_then ‘t’ mp_tac) \\ strip_tac
  \\ last_x_assum (qspec_then ‘h’ mp_tac) \\ strip_tac
  \\ gvs []
  \\ drule_all evaluate_arith_insert
                \\ gvs [set_var_def]
QED

Theorem MEM_FST_not_seen[local]:
  ∀moves data.
  (∀p_1 p_2. MEM (p_1,p_2) moves ⇒ ¬is_seen p_1 data) ⇒
  ∀p. MEM p (MAP FST moves) ⇒ ¬is_seen p data
Proof
  Induct \\ gvs []
  \\ rpt gen_tac \\ strip_tac \\ gen_tac \\ strip_tac
  >- (Cases_on ‘h’ \\ gvs [])
  \\ ‘∀p_1 p_2. MEM (p_1,p_2) moves ⇒ ¬is_seen p_1 data’ by metis_tac []
  \\ strip_tac
  \\ last_x_assum drule \\ disch_then drule \\ gvs []
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
  \\ gvs [domain_list_insert, MEM_FILTER, ODD_EVEN]
  \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_map_insert, AllCaseEqs()]
      >- (qpat_x_assum ‘EVERY _ _’ kall_tac
          \\ gvs [ALOOKUP_NONE, MEM_MAP, MEM_FILTER, FORALL_PROD, EXISTS_PROD]
          \\ last_x_assum drule \\ strip_tac
          \\ gvs []
          \\ irule get_set_vars_lemma
          \\ CCONTR_TAC \\ gvs [MEM_MAP, EXISTS_PROD, EVERY_MEM]
          \\ first_x_assum drule \\ gvs [is_seen_def, domain_lookup])
      \\ drule ALOOKUP_MEM \\ strip_tac
      \\ gvs [MEM_FILTER, MEM_MAP, EXISTS_PROD]
      \\ Cases_on ‘lookup p_2 data.map’ \\ gvs []
      >- (‘canonicalRegs data p_2 = p_2’ by gvs [canonicalRegs_def, lookup_any_def]
          \\ gvs [EVERY_MEM, FORALL_PROD]
          \\ first_assum drule \\ strip_tac \\ gvs []
          \\ ‘¬MEM p_2 (MAP FST moves)’
            by (CCONTR_TAC \\ gvs [MEM_MAP]
                \\ Cases_on ‘y’ \\ gvs []
                \\ last_x_assum drule \\ gvs [])
          \\ simp [get_set_vars_not_in]
          \\ simp [get_set_vars_in]
          \\ gvs [is_seen_def, domain_lookup]
          \\ Cases_on ‘lookup p_2 data.all_names’ \\ gvs []
          \\ metis_tac [])
      \\ last_x_assum drule \\ strip_tac \\ gvs []
      \\ simp [canonicalRegs_def, lookup_any_def]
      \\ gvs [EVERY_MEM, FORALL_PROD]
      \\ ‘¬MEM x' (MAP FST moves)’
        by (CCONTR_TAC \\ gvs [MEM_MAP]
            \\ Cases_on ‘y’ \\ gvs []
            \\ last_x_assum drule \\ gvs [is_seen_def, domain_lookup])
      \\ simp [get_set_vars_not_in]
      \\ drule_all get_set_vars_in_2 \\ metis_tac [])
  >- (rpt gen_tac \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [EVERY_MEM, FORALL_PROD]
      \\ ‘¬MEM v (MAP FST moves)’
        by (strip_tac \\ drule MEM_FST_not_seen \\ strip_tac
            \\ pop_assum drule \\ gvs [is_seen_def, domain_lookup])
      \\ drule_all lookup_set_vars_not_in
      \\ rw [])
  >- (rpt gen_tac \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [EVERY_MEM, FORALL_PROD]
      \\ drule are_reads_seen_insert_list \\ rw []
      \\ drule MEM_FST_not_seen \\ strip_tac
      \\ drule_all evaluate_arith_insert_list \\ strip_tac
      \\ qexists_tac ‘w’ \\ gvs []
      \\ ‘¬MEM v (MAP FST moves)’
        by (CCONTR_TAC \\ gvs []
            \\ first_x_assum drule \\ gvs [is_seen_def, domain_lookup])
      \\ rw [get_set_vars_not_in])
  \\ cheat
QED

Theorem data_inv_unchanged_map:
∀data s n r v. data_inv data s ⇒
               ¬is_seen n data ⇒
               lookup r data.map = SOME v ⇒
               get_var r (set_var n x s) = get_var v (set_var n x s) ∧
               (v = n ∨ v ∈ domain data.all_names) ∧
               (r = n ∨ r ∈ domain data.all_names)
Proof
  rpt gen_tac \\ strip_tac \\ strip_tac \\ strip_tac
  \\ gvs [data_inv_def]
  \\ last_x_assum drule \\ strip_tac
  \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’
  \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, is_seen_def]
QED

Theorem data_inv_unchanged_const:
∀data s n1 n2 n c v. data_inv data s ⇒
                     ¬is_seen n2 data ⇒
                     lookup data.instrs (instToNumList (Const n c)) = SOME n1 ⇒
                     lookup n1 (set_var n2 v s).locals = SOME (Word c) ∧
                     (n1 = n2 ∨ n1 ∈ domain data.all_names)
Proof
  rpt gen_tac \\ strip_tac \\ strip_tac \\ strip_tac
  \\ gvs [data_inv_def]
  \\ last_x_assum drule \\ strip_tac
  \\ Cases_on ‘n1=n2’ \\ gvs [set_var_def, lookup_insert, domain_lookup, is_seen_def]
QED

Theorem Inst_Arith_NONE_lemma:
  ∀data s s' a.
    data_inv data s ⇒
    inst (Arith a) s = SOME s' ⇒
    ¬is_complex a ⇒ are_reads_seen a data ⇒ ¬is_seen (firstRegOfArith a) data ⇒
    data_inv (data with <|instrs:=insert data.instrs (instToNumList (Arith (canonicalArith data a))) (firstRegOfArith a);
                          all_names:=insert (firstRegOfArith a) () data.all_names|>) s'
Proof
  cheat
QED

Theorem Inst_Arith_SOME_lemma:
  ∀data s s' a x.
    data_inv data s ⇒
    inst (Arith a) s = SOME s' ⇒
    ¬is_complex a ⇒ are_reads_seen a data ⇒ ¬is_seen (firstRegOfArith a) data ⇒
    lookup data.instrs (instToNumList (Arith (canonicalArith data a))) = SOME x ⇒
    data_inv (data with <|eq := regsUpdate x (firstRegOfArith a) data.eq;
                          map := insert (firstRegOfArith a) x data.map;
                          all_names := insert (firstRegOfArith a) () data.all_names|>) s'
Proof
  cheat
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
   ( gvs [word_cse_def, word_cseInst_def, evaluate_def, inst_def, assign_def]
     \\ Cases_on ‘word_exp s (Const c)’ \\ gvs []
     \\ Cases_on ‘is_seen n data’ \\ gvs [evaluate_def, inst_def, assign_def]
     \\ gvs [add_to_data_def, add_to_data_aux_def]
     \\ Cases_on ‘lookup data.instrs (instToNumList (Const n c))’
     \\ gvs [evaluate_def, inst_def, assign_def]
     >- (gvs [data_inv_def]
         \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
         >- (first_x_assum drule \\ strip_tac
             \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’
             \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, is_seen_def])
         >- (Cases_on ‘c=c'’ \\ gvs [mlmapTheory.lookup_insert, instToNumList_def]
             >- gvs [set_var_def, lookup_insert, word_exp_def]
             \\ gvs [] \\ first_x_assum drule \\ strip_tac
             \\ Cases_on ‘v=n’ \\ gvs [set_var_def, lookup_insert, domain_lookup, is_seen_def])
         >- (gvs [instToNumList_def, mlmapTheory.lookup_insert]
             \\ first_x_assum drule \\ strip_tac \\ gvs []
             \\ qexists_tac ‘w’ \\ gvs []
             \\ drule_all evaluate_arith_insert \\ strip_tac
             \\ Cases_on ‘v=n’
             \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, is_seen_def])
         \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, mlmapTheory.lookup_insert]
         \\ first_x_assum drule \\ strip_tac
         \\ Cases_on ‘src=n’ \\ gvs [is_seen_def, lookup_insert]
         \\ Cases_on ‘v=n’ \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup]
         \\ gvs [word_exp_def, the_words_def, lookup_insert])
     \\ gvs [data_inv_def]
     \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac
     \\ gvs [get_vars_def, get_var_def, set_vars_def, alist_insert_def, set_var_def, word_exp_def]
     \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
     >- (Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
         \\ first_x_assum drule \\ strip_tac \\ gvs [is_seen_def])
     >- (first_x_assum drule \\ strip_tac \\ Cases_on ‘v=n’ \\ gvs [lookup_insert, domain_lookup, is_seen_def])
     >- (first_x_assum drule \\ strip_tac \\ gvs []
         \\ ‘evaluate (Inst (Arith a),s) = (NONE, set_var (firstRegOfArith a) w s)’ by gvs [set_var_def]
         \\ drule_all evaluate_arith_insert \\ strip_tac \\ gvs [set_var_def]
         \\ Cases_on ‘v=n’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
         \\ Cases_on ‘a’ \\ gvs [is_complex_def]
         >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
             \\ Cases_on ‘n0=n’ \\ gvs [lookup_insert]
             \\ Cases_on ‘n''=n’ \\ gvs [])
         \\ gvs [are_reads_seen_def, is_seen_def]
         \\ Cases_on ‘n0=n’ \\ gvs [lookup_insert]
         \\ Cases_on ‘n1=n’ \\ gvs [])
     \\ first_x_assum drule \\ strip_tac \\ gvs []
     \\ Cases_on ‘v=n’ \\ Cases_on ‘src=n’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
   )

  >- (* Arith *)
    (gvs [word_cse_def, word_cseInst_def]
     \\ pairarg_tac \\ gvs []
     \\ Cases_on ‘is_seen (firstRegOfArith a) data’ \\ gvs [evaluate_def]
     \\ Cases_on ‘is_complex a’ \\ gvs [evaluate_def]
     \\ drule_all are_reads_seen_canonical \\ strip_tac \\ gvs []
     \\ Cases_on ‘are_reads_seen a data’ \\ gvs [evaluate_def]
     \\ Cases_on ‘inst (Arith a) s’ \\ gvs [add_to_data_def, add_to_data_aux_def]
     \\ Cases_on ‘lookup data.instrs (instToNumList (Arith (canonicalArith data a)))’ \\ gvs [evaluate_def]
     >- (drule_all Inst_Arith_NONE_lemma \\ rw [])
     \\ drule_all Inst_Arith_SOME_lemma \\ rw []
     \\ pop_assum kall_tac
     \\ gvs [get_vars_def, data_inv_def]
     \\ first_x_assum drule \\ pop_assum kall_tac \\ strip_tac \\ gvs []
     \\ Cases_on ‘a’ \\ gvs [is_complex_def, firstRegOfArith_def, inst_def, assign_def]
     >- (Cases_on ‘r’ \\ gvs [word_exp_def]
         \\ gvs [are_reads_seen_def, canonicalArith_def, canonicalRegs_def,
                 canonicalImmReg_def, lookup_any_def]
         >- (Cases_on ‘lookup n0 data.map’ \\ gvs []
             >- (Cases_on ‘lookup n' data.map’ \\ gvs []
                 >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                         assign_def, word_exp_def, set_var_def]
                 \\ first_x_assum drule \\ strip_tac
                 \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                         assign_def, word_exp_def, set_var_def, get_var_def])
             \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac
             \\ Cases_on ‘lookup n' data.map’ \\ gvs []
             >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                     assign_def, word_exp_def, set_var_def, get_var_def]
             \\ first_x_assum drule \\ strip_tac
             \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                     assign_def, word_exp_def, set_var_def, get_var_def])
         \\ Cases_on ‘lookup n0 data.map’ \\ gvs []
         >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def]
         \\ first_x_assum drule \\ strip_tac
         \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def, get_var_def])
     >- (gvs [word_exp_def, are_reads_seen_def, canonicalArith_def,
              canonicalRegs_def, canonicalImmReg_def, lookup_any_def]
         \\ Cases_on ‘lookup n0 data.map’ \\ gvs []
         >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def]
         \\ first_x_assum drule \\ strip_tac
         \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def, get_var_def])
     \\ gvs [word_exp_def, are_reads_seen_def, canonicalArith_def,
             canonicalRegs_def, canonicalImmReg_def, lookup_any_def]
     \\ Cases_on ‘lookup n0 data.map’ \\ gvs []
     >- (Cases_on ‘lookup n1 data.map’ \\ gvs []
         >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def]
         \\ first_x_assum drule \\ strip_tac
         \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
                 assign_def, word_exp_def, set_var_def, get_var_def, get_vars_def])
     \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac
     \\ Cases_on ‘lookup n1 data.map’ \\ gvs []
     >- gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
             assign_def, word_exp_def, set_var_def, get_var_def, get_vars_def]
     \\ first_assum drule \\ pop_assum kall_tac \\ strip_tac
     \\ gvs [set_vars_def, alist_insert_def, evaluate_def, inst_def,
             assign_def, word_exp_def, set_var_def, get_var_def, get_vars_def])

  >- (* Mem *)
   ( Cases_on ‘a’
   \\ gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def, empty_data_def, lookup_def] \\ cheat)
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
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
  \\ Cases_on ‘is_seen v data’ \\ gvs []
  \\ strip_tac
  \\ gvs [evaluate_def, AllCaseEqs()]
  \\ gvs [set_var_def]
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
          \\ drule_at (Pos last) evaluate_arith_insert
          \\ strip_tac \\ first_x_assum (qspec_then ‘data’ mp_tac)
          \\ disch_then drule \\ gvs [] \\ strip_tac
          \\ reverse strip_tac
          >- (gvs [get_var_def, set_var_def, lookup_insert] \\ rw [] \\ gvs [is_seen_def, domain_lookup])
          \\ Cases_on ‘a’ \\ gvs [is_complex_def]
          >- (Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
              \\ gvs [lookup_insert]
              \\ Cases_on ‘n0=dst’ \\ gvs [domain_lookup]
              \\ Cases_on ‘n'=dst’ \\ gvs [])
          \\ gvs [are_reads_seen_def, is_seen_def, lookup_insert]
          \\ Cases_on ‘n0=dst’ \\ gvs []
          \\ Cases_on ‘n1=dst’ \\ gvs [])
      \\ gvs [mlmapTheory.lookup_insert]
      \\ Cases_on ‘OpCurrHeapToNumList b (canonicalRegs data src) = OpCurrHeapToNumList op src'’ \\ gvs []
      >- (gvs [is_seen_def, OpCurrHeapToNumList_def, canonicalRegs_def, lookup_any_def]
          \\ Cases_on ‘lookup src data.map’ \\ gvs []
          >- (Cases_on ‘src=dst’ \\ gvs [lookup_insert]
              \\ gvs [word_exp_def, set_var_def, get_var_def, lookup_insert])
          \\ first_x_assum drule \\ strip_tac
          \\ Cases_on ‘x=dst’ \\ gvs [lookup_insert, domain_lookup]
          \\ gvs [word_exp_def, set_var_def, get_var_def, lookup_insert])
      \\ pop_assum mp_tac \\ first_x_assum drule \\ strip_tac \\ strip_tac \\ gvs []
      \\ gvs [is_seen_def]
      \\ Cases_on ‘src'=dst’ \\ gvs [lookup_insert]
      \\ gvs [word_exp_def, set_var_def, get_var_def, lookup_insert]
      \\ Cases_on ‘v=dst’ \\ gvs [domain_lookup])
  \\ gvs [evaluate_def, AllCaseEqs()]
  \\ gvs [data_inv_def]
  \\ first_assum drule \\ strip_tac
  \\ gvs [get_vars_def, set_vars_def, alist_insert_def, set_var_def]
  \\ gvs [canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup src data.map’ \\ gvs []
  >- (rpt conj_tac \\ rpt gen_tac \\ strip_tac
      >- (Cases_on ‘r=dst’ \\ gvs [get_var_def, lookup_insert]
          \\ pop_assum kall_tac \\ first_x_assum drule \\ first_x_assum drule \\ strip_tac
          \\ Cases_on ‘v=dst’ \\ gvs [domain_lookup, is_seen_def])
      >- (first_x_assum drule \\ first_x_assum drule \\ strip_tac
          \\ Cases_on ‘v=dst’ \\ gvs [lookup_insert, domain_lookup, is_seen_def])
      >- (first_x_assum drule \\ strip_tac \\ first_x_assum drule \\ strip_tac
          \\ gvs [get_var_def]
          \\ Cases_on ‘v=dst’ \\ gvs [domain_lookup, lookup_insert, is_seen_def]
          \\ pop_assum kall_tac
          \\ ‘evaluate (Inst (Arith a),s) = (NONE, set_var (firstRegOfArith a) w'' s)’ by gvs [set_var_def]
          \\ drule_at (Pos last) evaluate_arith_insert
          \\ strip_tac \\ gvs [is_seen_def] \\ first_x_assum drule_all \\ strip_tac
          \\ gvs [set_var_def]
          \\ drule_at Any are_reads_seen_insert \\ strip_tac
          \\ reverse (Cases_on ‘a’) \\ gvs [are_reads_seen_def, is_complex_def, is_seen_def]
          \\ Cases_on ‘n0=dst’ \\ gvs [lookup_insert, domain_lookup]
          >- (Cases_on ‘n1=dst’ \\ gvs [])
          \\ Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
          \\ Cases_on ‘n0=dst’ \\ gvs [lookup_insert, domain_lookup]
          \\ Cases_on ‘n'=dst’ \\ gvs [])
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [get_var_def]
      \\ Cases_on ‘v=dst’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
      \\ Cases_on ‘src'=dst’ \\ gvs []
      \\ gvs [word_exp_def, the_words_def, lookup_insert])
  \\ last_assum drule \\ pop_assum kall_tac \\ strip_tac
  \\ Cases_on ‘lookup x' s.locals = lookup src s.locals’ \\ gvs [get_var_def, word_exp_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  >- (Cases_on ‘r=dst’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
      \\ last_x_assum drule \\ strip_tac
      \\ Cases_on ‘v=dst’ \\ gvs [])
  >- (last_x_assum drule \\ strip_tac
      \\ Cases_on ‘v=dst’ \\ gvs [lookup_insert, domain_lookup, is_seen_def])
  >- (last_x_assum drule \\ strip_tac
      \\ Cases_on ‘dst=v’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
      \\ pop_assum kall_tac
      \\ ‘evaluate (Inst (Arith a),s) = (NONE, set_var (firstRegOfArith a) w'' s)’ by gvs [set_var_def]
      \\ drule_at (Pos last) evaluate_arith_insert
      \\ strip_tac \\ gvs [is_seen_def] \\ first_x_assum drule_all \\ strip_tac
      \\ gvs [set_var_def]
      \\ drule_at Any are_reads_seen_insert \\ strip_tac
      \\ reverse (Cases_on ‘a’) \\ gvs [are_reads_seen_def, is_complex_def, is_seen_def]
      \\ Cases_on ‘n0=dst’ \\ gvs [lookup_insert, domain_lookup]
      >- (Cases_on ‘n1=dst’ \\ gvs [])
      \\ Cases_on ‘r’ \\ gvs [are_reads_seen_def, is_seen_def]
      \\ Cases_on ‘n0=dst’ \\ gvs [lookup_insert, domain_lookup]
      \\ Cases_on ‘n'=dst’ \\ gvs []
     )
  \\ first_x_assum drule \\ strip_tac
  \\ Cases_on ‘v=dst’ \\ gvs [lookup_insert, domain_lookup, is_seen_def]
  \\ Cases_on ‘src'=dst’ \\ gvs []
  \\ gvs [word_exp_def, the_words_def, lookup_insert]
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
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
  \\ Cases_on ‘is_seen v data’ \\ gvs []
  \\ strip_tac
  \\ gvs [evaluate_def, AllCaseEqs()]
  \\ gvs [set_var_def]
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
