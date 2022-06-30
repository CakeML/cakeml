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
                      get_var v s = get_var (firstRegOfArith a) s ∧
                      v IN domain data.all_names ∧ firstRegOfArith a IN domain data.all_names) ∧
    (∀op src dst v. lookup data.instrs (progToNumList (OpCurrHeap op dst src : 'a prog)) = SOME v ⇒
                    get_var v s = get_var dst s ∧
                    v IN domain data.all_names ∧ dst IN domain data.all_names) ∧
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
  \\ cheat
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

Theorem data_inv_locals:
  ∀data s. data_inv data s ⇒ data_inv data (s with locals := s.locals)
Proof
  rpt gen_tac
  \\ gvs [data_inv_def, get_var_def] \\ strip_tac \\ gvs []
  \\ rpt strip_tac \\ first_x_assum drule_all \\ strip_tac \\ gvs []
QED

Theorem not_seen_data_inv_alist_insert[simp]:
  ∀data s l r v.
    ¬is_seen r data ⇒
    data_inv data (s with locals := insert r v l) =
    data_inv data (s with locals := l)
Proof
  rpt strip_tac
  \\ cheat
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

Theorem data_inv_insert[local]:
  ∀moves data s q h t.
  ¬MEM q (MAP FST moves) ⇒
  ¬is_seen q data ⇒
  data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
           (s with locals := insert q h (alist_insert (MAP FST moves) t s.locals)) =
  data_inv (canonicalMoveRegs_aux data (MAP (λ(a,b). (a,canonicalRegs data b)) moves))
           (s with locals := alist_insert (MAP FST moves) t s.locals)
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
  \\ Cases_on ‘EVEN q’ \\ gvs [set_vars_def]
  >- (rpt gen_tac
      \\ Cases_on ‘x’ \\ gvs [alist_insert_def]
      >- (gvs [get_vars_def]
          \\ Cases_on ‘get_var r s’ \\ gvs []
          \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs [])
      \\ gvs [data_inv_insert]
      \\ last_x_assum irule \\ gvs [get_vars_def]
      \\ Cases_on ‘get_var r s’ \\ gvs []
      \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs []
      \\ rpt (first_x_assum mp_tac)
      \\ qid_spec_tac ‘t’
      \\ Induct_on ‘moves’ \\ gvs []
      \\ rpt strip_tac
      \\ Cases_on ‘get_vars (SND h'::MAP SND moves) s’ \\ gvs []
  )
  \\ Cases_on ‘x’ \\ gvs [alist_insert_def]
  \\ gvs [get_vars_def]
  \\ Cases_on ‘get_var r s’ \\ gvs []
  \\ Cases_on ‘get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s’ \\ gvs []
  \\ gvs [data_inv_def] \\ rpt strip_tac
  >- (first_x_assum (drule_at Any) \\ strip_tac \\ gvs [get_var_def, lookup_insert]
      \\ Cases_on ‘r' = q’ \\ gvs []
      \\ Cases_on ‘v = q’ \\ gvs [] \\ cheat)
  (* Proof hard stuck *)
  \\ cheat
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
   ( gvs [evaluate_def, word_cse_def, word_cseInst_def, data_inv_def]
     \\ Cases_on ‘is_seen n data’ \\ gvs [evaluate_def]
     >- gvs [data_inv_def, empty_data_def, lookup_def]
     \\ gvs [is_seen_def] \\ Cases_on ‘lookup n data.all_names’ \\ gvs []
     \\ Cases_on ‘lookup data.instrs (instToNumList (Const n c))’ \\ gvs[evaluate_def]
     >- ( Cases_on ‘inst (Const n c) s’ \\ gvs [data_inv_def, inst_def, assign_def]
          \\ Cases_on ‘word_exp s (Const c)’
          \\ gvs [get_var_def, set_var_def, lookup_insert, domain_lookup, word_exp_def]
          \\ strip_tac
          >- (rpt gen_tac \\ Cases_on ‘r=n’ \\ Cases_on ‘v=n’ \\ gvs []
              \\ strip_tac \\ first_x_assum drule_all \\ rw [])
          \\ strip_tac
          >- (rpt gen_tac \\ gvs [mlmapTheory.lookup_insert]
              \\ Cases_on ‘c = c'’ \\ gvs [instToNumList_def, wordToNum_def]
              \\ strip_tac \\ first_x_assum drule_all
              \\ strip_tac
              \\ Cases_on ‘v = n’ \\ gvs [])
          \\ strip_tac
          >- (rpt gen_tac \\ gvs [instToNumList_def, arithToNumList_def, mlmapTheory.lookup_insert]
              \\ strip_tac
              \\ first_assum drule_all
              \\ strip_tac
              \\ Cases_on ‘v=n’ \\ gvs []
              \\ Cases_on ‘firstRegOfArith a = n’ \\ gvs [])
          \\ rpt gen_tac \\ strip_tac
          \\ gvs [mlmapTheory.lookup_insert, instToNumList_def, progToNumList_def]
          \\ first_x_assum drule_all \\ strip_tac \\ gvs []
        )
     \\ Cases_on ‘inst (Const n c) s’ \\ gvs [inst_def, assign_def, word_exp_def]
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ gvs [get_vars_def, get_var_def, set_vars_def, alist_insert_def, set_var_def])
     \\ strip_tac
     >- (first_x_assum drule_all \\ strip_tac
         \\ rpt gen_tac
         \\ gvs [sptreeTheory.lookup_insert]
         \\ Cases_on ‘r = n’ \\ strip_tac \\ gvs []
         >- (Cases_on ‘n=v’ \\ gvs [set_var_def, get_var_def, lookup_insert])
         \\ gvs [set_var_def, get_var_def, lookup_insert]
         \\ first_x_assum drule_all \\ strip_tac \\ gvs []
         \\ Cases_on ‘v = n’ \\ gvs [domain_lookup])
     \\ strip_tac
     >- (first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
         \\ strip_tac \\ gvs [set_var_def, lookup_insert, domain_lookup]
         \\ Cases_on ‘v=n’ \\ gvs [] )
     \\ strip_tac
     >- (first_assum drule_all \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ first_x_assum drule_all
         \\ strip_tac \\ gvs [set_var_def, get_var_def, lookup_insert, domain_lookup]
         \\ Cases_on ‘v = n’ \\ gvs []
         \\ Cases_on ‘firstRegOfArith a = n’ \\ gvs [])
     \\ first_x_assum drule_all \\ strip_tac
     \\ rpt gen_tac \\ strip_tac
     \\ first_x_assum drule_all \\ strip_tac \\ gvs[get_var_def, set_var_def, lookup_insert]
     \\ Cases_on ‘v=n’ \\ Cases_on ‘dst=n’ \\ gvs [domain_lookup]
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
  \\ metis_tac [NOT_NONE_SOME]
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
  \\ rpt strip_tac \\ first_x_assum drule_all \\ gvs []
QED

Theorem comp_OpCurrHeap_correct:
  ^(get_goal "OpCurrHeap")
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [evaluate_def, word_cse_def]
  \\ Cases_on ‘word_exp s (Op b [Var src; Lookup CurrHeap])’ \\ gvs []
  \\ Cases_on ‘lookup dst data.all_names ≠ NONE’ \\ gvs [evaluate_def]
  \\ Cases_on ‘lookup data.instrs (progToNumList (OpCurrHeap b dst (canonicalRegs data src)))’
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
  gvs[word_cse_def, data_inv_def, evaluate_def] \\
  rw [] \\
  fs [get_var_def, dec_clock_def] \\
  first_x_assum drule_all \\ gs []
QED

Theorem comp_MustTerminate_correct:
  ^(get_goal "MustTerminate")
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ gs[word_cse_def]
  \\ pairarg_tac \\ gvs [evaluate_def,flat_exp_conventions_def]
  \\ gvs [AllCaseEqs()]
  \\ strip_tac
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum (drule_at Any)
  \\ impl_tac
  >- (gvs [data_inv_def, get_var_def, SF SFY_ss] \\ Cases_on ‘res' = SOME TimeOut’ \\ gvs [])
  \\ gvs [evaluate_def]
  \\ rw []
  \\ gvs [AllCaseEqs(), data_inv_def, get_var_def, SF SFY_ss]
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
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ cheat
(* never end
  gvs [data_inv_def]
 *)
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
