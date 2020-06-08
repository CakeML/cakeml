(*
  Correctness proof for ---
*)

open preamble
     crepSemTheory crepPropsTheory
     loopLangTheory loopSemTheory loopPropsTheory
     pan_commonTheory pan_commonPropsTheory
     crep_to_loopTheory


val _ = new_theory "crep_to_loopProof";

Datatype:
  context =
  <| vars    : crepLang$varname |-> num;
     funcs   : crepLang$funname |-> num # num list;  (* loc, args *)
     vmax : num|>
End

Definition find_var_def:
  find_var ct v =
   case FLOOKUP ct.vars v of
    | SOME n => n
    | NONE => 0
End

Definition find_lab_def:
  find_lab ct f =
   case FLOOKUP ct.funcs f of
    | SOME (n, _) => n
    | NONE => 0
End

Definition prog_if_def:
  prog_if cmp p q e e' n m l =
   p ++ q ++ [
    Assign n e; Assign m e';
    If cmp n (Reg m)
    (Assign n (Const 1w)) (Assign n (Const 0w)) (list_insert [n; m] l)]
End

Definition compile_exp_def:
  (compile_exp ctxt tmp l ((Const c):'a crepLang$exp) = ([], Const c, tmp, l)) /\
  (compile_exp ctxt tmp l (Var v) = ([], Var (find_var ctxt v), tmp, l)) /\
  (compile_exp ctxt tmp l (Label f) = ([LocValue tmp (find_lab ctxt f)], Var tmp, tmp + 1, insert tmp () l)) /\
  (compile_exp ctxt tmp l (Load ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in (p, Load le, tmp, l)) /\
  (compile_exp ctxt tmp l (LoadByte ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in
    (p ++ [Assign tmp le; LoadByte tmp 0w tmp], Var tmp, tmp + 1, insert tmp () l)) /\
  (compile_exp ctxt tmp l (LoadGlob gadr) = ([], Lookup gadr, tmp, l)) /\
  (compile_exp ctxt tmp l (Op bop es) =
   let (p, les, tmp, l) = compile_exps ctxt tmp l es in
   (p, Op bop les, tmp, l)) /\
  (compile_exp ctxt tmp l (Cmp cmp e e') =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in
   let (p', le', tmp', l) = compile_exp ctxt tmp l e' in
    (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l, Var (tmp' + 1), tmp' + 3, list_insert [tmp' + 1; tmp' + 2] l)) /\
  (compile_exp ctxt tmp l (Shift sh e n) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in (p, Shift sh le n, tmp, l)) /\

  (compile_exps ctxt tmp l cps = (* to generate ind thm *)
   case cps of
   | [] => ([], [], tmp, l)
   | e::es =>
     let (p, le, tmp, l) = compile_exp ctxt tmp l e in
      let (p1, les, tmp, l) = compile_exps ctxt tmp l es in
      (p ++ p1, le::les, tmp, l))
Termination
  cheat
End

Definition compile_prog_def:
  (compile_prog _ l (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog, l)) /\
  (compile_prog ctxt l (Assign v e) =
   case FLOOKUP ctxt.vars v of
    | SOME n =>
      let (p,le,tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in
       (nested_seq (p ++ [Assign n le]), l)
    | NONE => (Skip,l))
End

(* state relation *)

val s = ``(s:('a,'ffi) crepSem$state)``


Definition state_rel_def:
  state_rel (s:('a,'ffi) crepSem$state) (t:('a,'ffi) loopSem$state) <=>
  s.memaddrs = t.mdomain ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi
End

(*
  Loc encodes label of a function, e.g:
  Loc n1 n2 represents the label n2
  inside the function n1
*)

Definition wlab_wloc_def:
  (wlab_wloc _ (Word w) = Word w) /\
  (wlab_wloc ctxt (Label fname) =
   case FLOOKUP ctxt.funcs fname of
    | SOME (n, _) =>  Loc n 0
    | NONE =>  Loc 0 0)  (* impossible *)
End

Definition mem_rel_def:
  mem_rel ctxt smem tmem <=>
  (!ad. wlab_wloc ctxt (smem ad) = tmem ad) /\
  (!ad f.
    smem ad = Label f ==>
    ?n args. FLOOKUP ctxt.funcs f = SOME (n, args))
End

Definition globals_rel_def:
  globals_rel ctxt sglobals tglobals <=>
  (!ad w. FLOOKUP sglobals ad = SOME w ==>
    ?w'. FLOOKUP tglobals ad = SOME w' /\ wlab_wloc ctxt w = w') /\
  (!ad f.
    FLOOKUP sglobals ad = SOME (Label f) ==>
    ?n args. FLOOKUP ctxt.funcs f = SOME (n, args))
End

Definition distinct_funcs_def:
  distinct_funcs fm <=>
    (!x y n m rm rm'.
       FLOOKUP fm x = SOME (n, rm) /\
       FLOOKUP fm y = SOME (m, rm') /\
       n = m ==> x = y)
End

Definition ctxt_fc_def:
  ctxt_fc cvs ns args =
    <|vars := FEMPTY |++ ZIP (ns, args);
      funcs := cvs;
      vmax := list_max args |>
End

Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
   distinct_funcs ctxt.funcs /\
   (∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc args l. FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, FST (compile_prog nctxt l prog)))
End

Definition excp_rel_def:
  excp_rel ctxt <=> T
End

Definition ctxt_max_def:
  ctxt_max (n:num) fm <=>
    0 <= n ∧
    (!v m. FLOOKUP fm v = SOME m ==> m <= n)
End

Definition distinct_vars_def:
  distinct_vars fm <=>
    (!x y n m.
       FLOOKUP fm x = SOME n /\
       FLOOKUP fm y = SOME m /\
       n = m ==> x = y)
End

Definition locals_rel_def:
  locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals <=>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n v'. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧ (* remove that later *)
    lookup n t_locals = SOME v' ∧ wlab_wloc ctxt v = v'
End

Theorem state_rel_intro:
  state_rel ^s (t:('a,'ffi) loopSem$state) <=>
  s.memaddrs = t.mdomain ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi
Proof
  rw [state_rel_def]
QED


Theorem locals_rel_intro:
  locals_rel ctxt l (s_locals:num |-> 'a word_lab) t_locals ==>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n v'. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME v' ∧ wlab_wloc ctxt v = v'
Proof
  rw [locals_rel_def]
QED

Theorem code_rel_intro:
  code_rel ctxt s_code t_code ==>
   distinct_funcs ctxt.funcs /\
   (∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc args l . FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, FST (compile_prog nctxt l prog)))
Proof
  rw [code_rel_def]
QED

Theorem mem_rel_intro:
  mem_rel ctxt smem tmem ==>
  (!ad. wlab_wloc ctxt (smem ad) = tmem ad) /\
  (!ad f.
    smem ad = Label f ==>
    ?n args. FLOOKUP ctxt.funcs f = SOME (n, args))
Proof
  rw [mem_rel_def]
QED

Theorem globals_rel_intro:
 globals_rel ctxt sglobals tglobals ==>
   (!ad w. FLOOKUP sglobals ad = SOME w ==>
    ?w'. FLOOKUP tglobals ad = SOME w' /\ wlab_wloc ctxt w = w') /\
   (!ad f.
    FLOOKUP sglobals ad = SOME (Label f) ==>
    ?n args. FLOOKUP ctxt.funcs f = SOME (n, args))
Proof
  rw [globals_rel_def]
QED


Theorem evaluate_nested_seq_cases:
  (!p q s st t.
    evaluate (nested_seq (p ++ q), s) = (NONE, t) /\
    evaluate (nested_seq p,s) = (NONE,st) ==>
    evaluate (nested_seq q,st) = (NONE,t)) /\
  (!p s st q.
    evaluate (nested_seq p, s) = (NONE, st) ==>
    evaluate (nested_seq (p ++ q), s) =  evaluate (nested_seq q, st)) /\
  (!p s res st q.
    evaluate (nested_seq p, s) = (res, st) /\
    res <> NONE ==>
    evaluate (nested_seq (p ++ q), s) =  evaluate (nested_seq p, s))
Proof
  rpt conj_tac >>
  Induct >> rw []
  >- fs [nested_seq_def, evaluate_def] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  FULL_CASE_TAC >> fs [] >>
  res_tac >> fs []
QED

val evaluate_nested_seq_append_first = evaluate_nested_seq_cases |> CONJUNCT1
val evaluate_none_nested_seq_append = evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT1
val evaluate_not_none_nested_seq_append = evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT2

Definition comp_syntax_ok_def:
  comp_syntax_ok p = every_prog
  (λp. p = Skip ∨
   ?n m. p = LocValue n m ∨
   ?n e. p = Assign n e ∨
   ?n e m. p = LoadByte n e m ∨
   (?c n m ns v v'. p = If c n (Reg m) (Assign n v) (Assign n v') ns) ∨
   (?q r. p = Seq q r ∧ comp_syntax_ok q ∧ comp_syntax_ok r)) p
Termination
 cheat
End


Theorem comp_syn_ok_basic_cases:
  comp_syntax_ok Skip /\ (!n m. comp_syntax_ok (LocValue n m)) /\
  (!n e. comp_syntax_ok (Assign n e)) /\  (!n e m. comp_syntax_ok (LoadByte n e m)) /\
  (!c n m ns v v'. comp_syntax_ok (If c n (Reg m) (Assign n v) (Assign n v') ns))
Proof
  rw [] >>
  ntac 3 (fs [Once comp_syntax_ok_def, Once every_prog_def])
QED


Theorem comp_syn_ok_seq:
  !p q. comp_syntax_ok (Seq p q) ==>
   comp_syntax_ok p /\ comp_syntax_ok q
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def, Once every_prog_def]
QED


Theorem comp_syn_ok_if:
  comp_syntax_ok (If cmp n m p q ls) ==>
   ?v v'. p = Assign n v /\ q = Assign n v'
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def, Once every_prog_def]
QED


Theorem comp_syn_ok_seq2:
  !p q. comp_syntax_ok p /\ comp_syntax_ok q ==>
   comp_syntax_ok (Seq p q)
Proof
  rw [] >>
  once_rewrite_tac [comp_syntax_ok_def] >>
  fs [every_prog_def] >>
  fs [Once comp_syntax_ok_def]
QED


Theorem comp_syn_ok_nested_seq:
  !p q. comp_syntax_ok (nested_seq p) ∧
   comp_syntax_ok (nested_seq q) ==>
   comp_syntax_ok (nested_seq (p ++ q))
Proof
  Induct >> rw [] >>
  fs [nested_seq_def] >>
  drule comp_syn_ok_seq >>
  strip_tac >> res_tac >> fs [] >>
  metis_tac [comp_syn_ok_seq2]
QED

Theorem comp_syn_ok_nested_seq2:
  !p q. comp_syntax_ok (nested_seq (p ++ q)) ==>
   comp_syntax_ok (nested_seq p) ∧
   comp_syntax_ok (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, comp_syn_ok_basic_cases] >>
   drule comp_syn_ok_seq >> strip_tac >> fs [] >>
   metis_tac [comp_syn_ok_seq2]
QED

Definition cut_sets_def:
  (cut_sets l Skip = l) ∧
  (cut_sets l (LocValue n m) = insert n () l) ∧
  (cut_sets l (Assign n e) = insert n () l) ∧
  (cut_sets l (LoadByte n e m) = insert m () l) ∧
  (cut_sets l (Seq p q) = cut_sets (cut_sets l p) q) ∧
  (cut_sets l (If _ _ _ p q nl) = cut_sets (cut_sets l p) q) ∧
  (cut_sets _ _ = ARB)
End


Theorem comp_syn_ok_cut_sets_nested_seq:
  !p q l. comp_syntax_ok (nested_seq p) ∧
   comp_syntax_ok (nested_seq q) ==>
   cut_sets l (nested_seq (p ++ q)) =
   cut_sets (cut_sets l (nested_seq p)) (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def]
  >- fs [cut_sets_def] >>
  fs [cut_sets_def] >>
  drule comp_syn_ok_seq >>
  strip_tac >>
  res_tac >> fs []
QED

Theorem cut_sets_union_accumulate:
  !p l. comp_syntax_ok p ==>
   ?(l' :sptree$num_set). cut_sets l p = union l l'
Proof
  Induct >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  fs [cut_sets_def]
  >- (qexists_tac ‘LN’ >> fs [])
  >- (
   qexists_tac ‘insert n () LN’ >>
   fs [Once insert_union] >>
   fs [union_num_set_sym])
  >- (
   qexists_tac ‘insert n0 () LN’ >>
   fs [Once insert_union] >>
   fs [union_num_set_sym])
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   last_x_assum drule >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘union l l'’ mp_tac) >>
   strip_tac >> fs [] >>
   qexists_tac ‘union l' l''’ >>
   fs [] >> metis_tac [union_assoc])
  >- (
   drule comp_syn_ok_if >>
   strip_tac >> rveq >>
   fs [cut_sets_def] >>
   qexists_tac ‘insert n () LN’ >>
   fs [Once insert_insert, Once insert_union, union_num_set_sym]) >>
  qexists_tac ‘insert n () LN’ >>
  fs [Once insert_union] >>
  fs [union_num_set_sym]
QED


Theorem cut_sets_union_domain_union:
  !p l. comp_syntax_ok p ==>
   ?(l' :sptree$num_set). domain (cut_sets l p) = domain l ∪ domain l'
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  disch_then (qspec_then ‘l’ mp_tac) >>
  strip_tac >> fs [] >>
  qexists_tac ‘l'’ >>
  fs [domain_union]
QED

Theorem comp_syn_impl_cut_sets_subspt:
  !p l. comp_syntax_ok p ==>
  subspt l (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  disch_then (qspec_then ‘l’ assume_tac) >>
  fs [subspt_union]
QED

Theorem comp_syn_cut_sets_mem_domain:
  !p l n .
   comp_syntax_ok p /\ n ∈ domain l ==>
    n ∈ domain (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_domain_union >>
  disch_then (qspec_then ‘l’ mp_tac) >>
  strip_tac >> fs []
QED

Theorem cut_set_seq_subspt_prop:
  !(p:'a prog) (q:'a prog) l. comp_syntax_ok p /\ comp_syntax_ok q /\
  subspt l (cut_sets (cut_sets l p) q) ==> subspt l (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  disch_then (qspec_then ‘cut_sets l p’ assume_tac) >>
  fs [] >>
  fs [] >>
  last_x_assum assume_tac >>
  drule cut_sets_union_accumulate >>
  disch_then (qspec_then ‘l’ assume_tac) >>
  fs [] >>
  fs [subspt_union]
QED

Theorem cut_set_subspt_cut_sets_subspt_inter:
  !p n m n' m'. comp_syntax_ok p /\ subspt n m /\
     cut_sets n p = union n n' /\  cut_sets m p = union m m' ==>
       subspt (union n n') (union m m')
Proof
  Induct >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  fs [cut_sets_def] >> rveq >> fs [] >>
  TRY (
  fs [Once insert_union, subspt_domain] >>
  pop_assum (mp_tac o GSYM) >>
  pop_assum (mp_tac o GSYM) >>
  strip_tac >> strip_tac >> fs [] >>
  fs [domain_union] >>
  fs [SUBSET_DEF] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >> fs [] >>
   last_x_assum drule >>
   pop_assum mp_tac >>
   drule cut_sets_union_accumulate >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   drule cut_sets_union_accumulate >>
   disch_then (qspec_then ‘m’ mp_tac) >>
   ntac 3 strip_tac >>
   disch_then drule >>
   disch_then drule >>
   strip_tac >>
   last_x_assum mp_tac >>
   drule cut_sets_union_accumulate >>
   disch_then (qspec_then ‘union n l''’ mp_tac) >>
   drule cut_sets_union_accumulate >>
   disch_then (qspec_then ‘union m l'’ mp_tac) >>
   ntac 2 strip_tac >>
   disch_then drule >>
   disch_then drule >>
   disch_then drule >>
   strip_tac >>
   fs [subspt_domain] >>
   rfs []) >>
  drule comp_syn_ok_if >>
  strip_tac >> fs [] >>
  fs [comp_syn_ok_basic_cases] >>
  fs [cut_sets_def] >>
  ntac 2 (pop_assum kall_tac) >>
  ntac 2 (pop_assum (mp_tac o GSYM)) >>
  fs [] >>
  strip_tac >> strip_tac >>
  fs [Once insert_union, subspt_domain] >>
  fs [SUBSET_DEF]
QED

Theorem cut_set_subspt_cut_sets_subspt:
  !p l l'. comp_syntax_ok p /\ subspt l l' ==>
  subspt (cut_sets l p) (cut_sets l' p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  drule cut_sets_union_accumulate >>
  disch_then (qspec_then ‘l’ assume_tac) >>
  disch_then (qspec_then ‘l'’ assume_tac) >>
  fs [] >>
  ho_match_mp_tac cut_set_subspt_cut_sets_subspt_inter >>
  metis_tac []
QED


Theorem compile_exp_out_rel_cases:
  (!ct tmp l (e:'a crepLang$exp) p le ntmp nl.
    compile_exp ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok (nested_seq p) /\ tmp <= ntmp /\ subspt l nl /\
    subspt (cut_sets l (nested_seq p)) nl) /\
  (!ct tmp l (e:'a crepLang$exp list) p le ntmp nl.
    compile_exps ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok (nested_seq p) /\ tmp <= ntmp /\ subspt l nl /\
    subspt (cut_sets l (nested_seq p)) nl)
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   conj_tac
   >- (
    fs [nested_seq_def] >>
    match_mp_tac comp_syn_ok_seq2 >>
    fs [comp_syn_ok_basic_cases]) >>
   fs [subspt_insert] >>
   fs [nested_seq_def, cut_sets_def])
  >- (
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   res_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   conj_asm1_tac
   >- (
    fs [compile_exp_def] >>
    pairarg_tac >> fs [] >> rveq >> fs [] >>
    match_mp_tac comp_syn_ok_nested_seq >>
    fs [] >>
    fs [nested_seq_def] >>
    match_mp_tac comp_syn_ok_seq2 >>
    fs [comp_syn_ok_basic_cases] >>
    match_mp_tac comp_syn_ok_seq2 >>
    fs [comp_syn_ok_basic_cases]) >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   res_tac >> fs [] >>
   qmatch_goalsub_rename_tac ‘insert itmp () il’ >>
   conj_tac
   >- (match_mp_tac subspt_right_insert_subspt >> fs []) >>
   drule comp_syn_ok_nested_seq2 >>
   strip_tac >> fs [] >>
   last_x_assum assume_tac >>
   qmatch_goalsub_abbrev_tac ‘p' ++ np’ >>
   drule comp_syn_ok_cut_sets_nested_seq >>
   disch_then (qspecl_then [‘np’, ‘l’] assume_tac) >>
   fs [Abbr ‘np’] >> pop_assum kall_tac >>
   fs [nested_seq_def] >>
   fs [cut_sets_def] >>
   fs [Once insert_insert] >>
   match_mp_tac subspt_same_insert_subspt >>
   fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def])
  >- (
   fs [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   cases_on ‘e’
   >- fs [compile_exp_def] >>
   fs [] >>
   fs [Once compile_exp_def])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   conj_tac
   >- (
    fs [prog_if_def] >>
    match_mp_tac comp_syn_ok_nested_seq >>
    conj_tac
    >- (
     match_mp_tac comp_syn_ok_nested_seq >>
     fs []) >>
    fs [nested_seq_def] >>
    rpt (match_mp_tac comp_syn_ok_seq2 >>
         fs [comp_syn_ok_basic_cases])) >>
   qmatch_goalsub_rename_tac ‘list_insert [ntmp + 1; _] nl’ >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e = (_,_,itmp,il)’ >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e' = (_,_,iitmp,_)’ >>
   conj_tac
   >- (
    fs [list_insert_def] >>
    metis_tac [subspt_right_insert_subspt, subspt_trans]) >>
   fs [list_insert_def, prog_if_def] >>
   qmatch_goalsub_abbrev_tac ‘p' ++ p'' ++ np’ >>
   ‘comp_syntax_ok (nested_seq np)’ by (
     fs [Abbr ‘np’] >>
     fs [nested_seq_def] >>
     rpt (match_mp_tac comp_syn_ok_seq2 >>
          fs [comp_syn_ok_basic_cases])) >>
   ‘comp_syntax_ok (nested_seq (p' ++ p''))’ by
     metis_tac [comp_syn_ok_nested_seq] >>
   drule comp_syn_ok_cut_sets_nested_seq >>
   disch_then (qspecl_then [‘np’, ‘l’] mp_tac) >>
   fs [] >> strip_tac >> pop_assum kall_tac >>
   fs [Abbr ‘np’] >> fs [nested_seq_def, cut_sets_def] >>
   fs [Once insert_insert] >>
   match_mp_tac subspt_same_insert_cancel >>
   pop_assum kall_tac >>
   drule comp_syn_ok_cut_sets_nested_seq >>
   disch_then (qspecl_then [‘p''’, ‘l’] mp_tac) >>
   fs [] >> strip_tac >> pop_assum kall_tac >>
   pop_assum kall_tac >>
   ‘subspt (cut_sets (cut_sets l (nested_seq p')) (nested_seq p''))
    (cut_sets il (nested_seq p''))’ by (
     ho_match_mp_tac cut_set_subspt_cut_sets_subspt >>
     fs []) >>
   drule  subspt_trans >>
   disch_then drule >> fs [])
  >- (
   fs [compile_exp_def] >>
   pairarg_tac >> fs []) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   fs [nested_seq_def] >>
   fs [Once comp_syntax_ok_def, every_prog_def, cut_sets_def]) >>
  pop_assum mp_tac >>
  once_rewrite_tac [compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘t’
  >- (
   fs [compile_exp_def] >>
   strip_tac >> rveq >> fs []) >>
  strip_tac >> fs [] >> rveq >>
  conj_tac >- metis_tac [subspt_trans, comp_syn_ok_nested_seq] >>
  conj_tac >-  metis_tac [subspt_trans, comp_syn_ok_nested_seq] >>
  drule comp_syn_ok_cut_sets_nested_seq >>
  disch_then (qspecl_then [‘p1’, ‘l’] mp_tac) >>
  fs [] >> strip_tac >> pop_assum kall_tac >>
  ‘subspt (cut_sets (cut_sets l (nested_seq p')) (nested_seq p1))
   (cut_sets l' (nested_seq p1))’  by (
    ho_match_mp_tac cut_set_subspt_cut_sets_subspt >>
    fs []) >>
  drule  subspt_trans >>
  disch_then drule >> fs []
QED


val compile_exp_out_rel = compile_exp_out_rel_cases |> CONJUNCT1
val compile_exps_out_rel = compile_exp_out_rel_cases |> CONJUNCT2


Theorem comp_syn_ok_upd_local_clock:
  !p s res t.
    evaluate (p,s) = (res,t) /\
    comp_syntax_ok p ==>
     t = s with <|locals := t.locals; clock := t.clock|>
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC)
  >- (
   fs [evaluate_def] >> rveq >>
   fs [state_component_equality])
  >- (
   fs [evaluate_def] >>
   FULL_CASE_TAC >> fs [set_var_def] >>
   rveq >> fs [state_component_equality])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [set_var_def] >> rveq >>
   fs [state_component_equality])
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   FULL_CASE_TAC >> fs []  >> rveq >>
   fs [state_component_equality])
  >- (
   drule comp_syn_ok_if >>
   strip_tac >> rveq >>
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [state_component_equality] >>
   fs [evaluate_def, comp_syn_ok_basic_cases] >>
   every_case_tac >>
   fs [cut_res_def, cut_state_def, dec_clock_def, set_var_def] >>
   every_case_tac >> fs [] >> rveq >> fs []) >>
  fs [evaluate_def] >>
  FULL_CASE_TAC >> fs [set_var_def] >>
  rveq >> fs [state_component_equality]
QED


Theorem assigned_vars_nested_seq_split:
  !p q.
   comp_syntax_ok (nested_seq p) /\ comp_syntax_ok (nested_seq q) ==>
    assigned_vars (nested_seq (p ++ q)) =
    assigned_vars (nested_seq p) ++ assigned_vars (nested_seq q)
Proof
  Induct >> rw []
  >- fs [nested_seq_def, assigned_vars_def] >>
  fs [nested_seq_def, assigned_vars_def] >>
  drule comp_syn_ok_seq >> fs []
QED

Theorem assigned_vars_seq_split:
  !q p.
   comp_syntax_ok q /\ comp_syntax_ok p ==>
    assigned_vars (Seq p q) =
    assigned_vars p ++ assigned_vars q
Proof
  rw [] >> fs [assigned_vars_def]
QED


Theorem comp_exp_assigned_vars_tmp_bound_cases:
  (!ct tmp l (e :α crepLang$exp) p le ntmp nl n.
    compile_exp ct tmp l e = (p,le,ntmp,nl) /\
    MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp) /\
  (!ct tmp l (e :α crepLang$exp list) p le ntmp nl n.
    compile_exps ct tmp l e = (p,le,ntmp,nl) /\
    MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp)
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [])
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [] >>
   drule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘nested_seq (_ ++ q)’ >>
   ‘comp_syntax_ok (nested_seq q)’ by (
     fs [Abbr ‘q’, nested_seq_def] >>
     rpt (match_mp_tac comp_syn_ok_seq2 >>
          fs [comp_syn_ok_basic_cases])) >>
   qpat_x_assum ‘comp_syntax_ok (nested_seq p')’ assume_tac >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac
   >- (res_tac >> fs []) >>
   fs [Abbr ‘q’, nested_seq_def] >>
   fs [assigned_vars_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def])
  >- (
   rpt gen_tac >>
   strip_tac >>
   qpat_x_assum ‘compile_exp _ _ _  _ = _’ mp_tac >>
   once_rewrite_tac [compile_exp_def] >> fs [] >> strip_tac >>
   pairarg_tac >> fs [])
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [prog_if_def] >>
   ‘tmp <= tmp' /\ tmp' <= tmp''’ by metis_tac [compile_exp_out_rel_cases] >>
   dxrule compile_exp_out_rel >>
   dxrule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘nested_seq (p' ++ p'' ++ q)’ >>
   ‘comp_syntax_ok (nested_seq q)’ by (
     fs [Abbr ‘q’, nested_seq_def] >>
     rpt (match_mp_tac comp_syn_ok_seq2 >>
          fs [comp_syn_ok_basic_cases])) >>
   strip_tac >>
   qpat_x_assum ‘comp_syntax_ok (nested_seq p')’ assume_tac >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘p'' ++ q’ mp_tac) >>
   fs [] >>
   pop_assum mp_tac >>
   drule comp_syn_ok_nested_seq >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   fs [] >>
   ntac 3 strip_tac >>
   fs []
   >- (res_tac >> fs []) >>
   ntac 3 (pop_assum kall_tac) >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   fs [] >>
   strip_tac >> fs []
   >- (res_tac >> fs []) >>
   pop_assum kall_tac >>
   fs [Abbr ‘q’, nested_seq_def] >>
   pop_assum kall_tac >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   drule assigned_vars_seq_split >>
   disch_then (qspec_then ‘Assign (tmp'' + 1) le'’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac
   >- fs [assigned_vars_def] >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   drule assigned_vars_seq_split >>
   disch_then (qspec_then ‘Assign (tmp'' + 2) le''’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac
   >- fs [assigned_vars_def] >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   drule assigned_vars_seq_split >>
   disch_then (qspec_then ‘If cmp (tmp'' + 1) (Reg (tmp'' + 2))
             (Assign (tmp'' + 1) (Const 1w)) (Assign (tmp'' + 1) (Const 0w))
             (insert (tmp'' + 1) () l'')’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac >>
   fs [assigned_vars_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs []) >>
  rpt gen_tac >>
  strip_tac >>
  pop_assum mp_tac >> fs [] >>
  once_rewrite_tac [compile_exp_def] >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def]) >>
  pop_assum mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> rveq >> fs [] >>
  strip_tac >>
  ‘tmp <= tmp' /\ tmp' <= ntmp’ by metis_tac [compile_exp_out_rel_cases] >>
  dxrule compile_exp_out_rel >>
  dxrule compile_exps_out_rel >>
  rpt strip_tac >> fs [] >>
  drule assigned_vars_nested_seq_split >>
  disch_then (qspec_then ‘p1’ mp_tac) >>
  fs [] >>
  strip_tac >> fs [] >>
  res_tac >> fs []
QED

val comp_exp_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT1
val comp_exps_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT2

Theorem compile_exp_le_tmp_domain_cases:
  (!ct tmp l (e:'a crepLang$exp) p le tmp' l' n.
    ctxt_max ct.vmax ct.vars /\
    compile_exp ct tmp l e = (p,le,tmp', l') /\ ct.vmax < tmp /\
    (!n. MEM n (var_cexp e) ==> ?m. FLOOKUP ct.vars n = SOME m /\ m ∈ domain l) /\
    MEM n (locals_touched le) ==> n < tmp' /\ n ∈ domain l') /\
  (!ct tmp l (es:'a crepLang$exp list) p les tmp' l' n.
    ctxt_max ct.vmax ct.vars /\
    compile_exps ct tmp l es = (p,les,tmp', l') /\ ct.vmax < tmp /\
    (!n. MEM n (FLAT (MAP var_cexp es)) ==> ?m. FLOOKUP ct.vars n = SOME m /\ m ∈ domain l) /\
    MEM n (FLAT (MAP locals_touched les)) ==> n < tmp' /\ n ∈ domain l')
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def, find_var_def, crepLangTheory.var_cexp_def, ctxt_max_def] >>
   rfs [] >> rveq >> res_tac >> fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def, crepLangTheory.var_cexp_def])
  >- (
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepLangTheory.var_cexp_def, locals_touched_def])
  >- (
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepLangTheory.var_cexp_def, locals_touched_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [crepLangTheory.var_cexp_def, locals_touched_def])
  >- (
   rpt gen_tac >>
   strip_tac >>
   qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
   once_rewrite_tac [compile_exp_def] >>
   strip_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [locals_touched_def, crepLangTheory.var_cexp_def, ETA_AX])
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [list_insert_def, crepLangTheory.var_cexp_def, locals_touched_def])
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [locals_touched_def, crepLangTheory.var_cexp_def]) >>
  rpt gen_tac >>
  strip_tac >>
  qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  cases_on ‘es’ >> fs [] >> rveq
  >- (
   strip_tac >> rveq >>
   fs [MAP]) >>
  strip_tac >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  ‘tmp <= tmp'' /\ tmp'' <= tmp' /\ subspt l l'' /\ subspt l'' l'’ by
    metis_tac [compile_exp_out_rel_cases] >>
  fs [MAP]
  >- (
   res_tac >> fs [subspt_domain] >>
   metis_tac [SUBSET_IMP]) >>
  last_x_assum match_mp_tac >>
  fs [] >>
  rw [] >>
  res_tac >> fs [subspt_domain] >>
  metis_tac [SUBSET_IMP]
QED

val compile_exp_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT1
val compile_exps_le_tmp_domain_cases = compile_exp_le_tmp_domain_cases |> CONJUNCT2


Theorem comp_syn_ok_lookup_locals_eq:
  !p s res t l n.
   evaluate (p,s) = (res,t) /\
   comp_syntax_ok p /\ n ∈ domain l /\
   subspt l (cut_sets l p) /\
    ~MEM n (assigned_vars p) ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC)
  >- fs [evaluate_def]
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [set_var_def, assigned_vars_def, lookup_insert])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [set_var_def, assigned_vars_def, lookup_insert])
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def, assigned_vars_def] >>
   pairarg_tac >> fs [AllCaseEqs ()] >> rveq >> fs []
   >- (
    fs [cut_sets_def] >>
    qpat_x_assum ‘comp_syntax_ok c1’ assume_tac >>
    drule cut_set_seq_subspt_prop >>
    disch_then (qspecl_then [‘c2’, ‘l’] mp_tac) >>
    fs [] >>
    strip_tac >>
    first_x_assum drule >>
    fs [] >> strip_tac >>
    drule comp_syn_cut_sets_mem_domain >>
    disch_then (qspecl_then [‘l’,‘n’] mp_tac) >>
    fs [] >> strip_tac >>
    last_x_assum drule >> fs [] >>
    metis_tac [comp_syn_impl_cut_sets_subspt]) >>
   first_x_assum drule >>
   fs [] >> metis_tac [comp_syn_impl_cut_sets_subspt])
  >- (
   drule comp_syn_ok_if >>
   strip_tac >>
   fs [evaluate_def, assigned_vars_def] >>
   fs [AllCaseEqs()]  >> rveq >> fs [cut_sets_def, domain_inter] >>
   cases_on ‘word_cmp cmp x y’ >> fs []
   >- (
    cases_on ‘evaluate (c1,s)’ >> fs [] >>
    fs [cut_res_def, cut_state_def, AllCaseEqs()] >>
    fs [evaluate_def] >>
    FULL_CASE_TAC >> fs [cut_res_def] >>
    fs [set_var_def, dec_clock_def] >>
    FULL_CASE_TAC >> fs [] >> rveq >>
    fs [comp_syn_ok_basic_cases, cut_sets_def, assigned_vars_def] >>
    rfs [Once insert_insert] >>
    res_tac >> fs [] >> cheat) >>
   cases_on ‘evaluate (c2,s)’ >> fs [] >>
   fs [cut_res_def, cut_state_def, AllCaseEqs()] >>
   fs [evaluate_def] >>
   FULL_CASE_TAC >> fs [cut_res_def] >>
   fs [set_var_def, dec_clock_def] >>
   FULL_CASE_TAC >> fs [] >> rveq >>
   fs [comp_syn_ok_basic_cases, cut_sets_def, assigned_vars_def] >>
   rfs [Once insert_insert] >>
   res_tac >> fs [] >> cheat) >>
  fs [dec_clock_def, lookup_inter] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [set_var_def, assigned_vars_def, lookup_insert]
QED



Theorem nested_seq_pure_evaluation:
  !p q t r st l m e v.
  evaluate (nested_seq (p ++ q),t) = (NONE,r) /\
  evaluate (nested_seq p,t) = (NONE,st) /\
  comp_syntax_ok (nested_seq p) /\
  comp_syntax_ok (nested_seq q) /\
  subspt l (cut_sets l (nested_seq p)) /\
  subspt (cut_sets l (nested_seq p)) (cut_sets (cut_sets l (nested_seq p)) (nested_seq q)) /\
  (!n. MEM n (assigned_vars (nested_seq p)) ==> n < m) /\
  (!n. MEM n (assigned_vars (nested_seq q)) ==> m <= n) /\
  (!n. MEM n (locals_touched e) ==> n < m /\ n ∈ domain l) /\
   eval st e = SOME v ==>
    eval r e = SOME v
Proof
  rw [] >>
  drule_all evaluate_nested_seq_append_first >> strip_tac >>
  drule comp_syn_ok_upd_local_clock >>
  fs [] >> strip_tac >>
  ‘st.globals = r.globals /\ st.memory = r.memory /\
   st.mdomain = r.mdomain’ by fs [state_component_equality] >>
  drule locals_touched_eq_eval_eq >> fs [] >>
  disch_then (qspec_then ‘e’ mp_tac) >> fs [] >>
  impl_tac
  >- (
   rw []  >>
   drule comp_syn_ok_lookup_locals_eq >>
   fs [] >>
   disch_then (qspecl_then [‘l’, ‘n’] mp_tac) >>
   impl_tac
   >- (
    fs [comp_syn_impl_cut_sets_subspt] >> CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >>
   fs []) >> fs []
QED


Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) ctxt tmp l.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  ctxt.vmax < tmp ==>
    let (p,le, tmp, l) = compile_exp ctxt tmp l e in
     ?st. evaluate (nested_seq p,t) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt l s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [nested_seq_def, evaluate_def, eval_def, wlab_wloc_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_var_def] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   pairarg_tac >> fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def] >>
   fs [locals_rel_def, SUBSET_INSERT_RIGHT] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   fs [loopSemTheory.eval_def, wlab_wloc_def] >>
   fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
   imp_res_tac state_rel_intro >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp' le; LoadByte tmp' 0w tmp']’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [set_var_def, wlab_wloc_def] >>
   fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >>
   fs [eval_def, state_rel_def] >>
   imp_res_tac compile_exp_out_rel >>
   fs [locals_rel_def, SUBSET_INSERT_RIGHT] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [Once compile_exp_def] >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   fs [loopSemTheory.eval_def] >>
   cases_on ‘evaluate (nested_seq p,t)’ >> fs [] >>
   ‘q = NONE /\ the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     ntac 11 strip_tac >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     strip_tac >> pairarg_tac >> fs [] >> rveq >>
     qmatch_asmsub_rename_tac ‘compile_exp _ _ _ h = (p,le,itmp,il)’ >>
     qmatch_asmsub_rename_tac ‘compile_exps _ _ _ _ = (fp,les,ntmp,nl)’ >>
     last_x_assum (qspecl_then
                   [‘il’, ‘itmp’, ‘les’, ‘fp’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_out_rel >>
     fs [] >>
     impl_tac
     >- (
      imp_res_tac evaluate_none_nested_seq_append >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>
     ‘eval r le = eval st le’ suffices_by fs [wlab_wloc_def] >>
     drule evaluate_nested_seq_append_first >>
     disch_then drule >>
     strip_tac >> fs [] >>
     imp_res_tac compile_exps_out_rel >>
     drule comp_syn_ok_upd_local_clock >>
     fs [] >> strip_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then drule >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘il’, ‘itmp’, ‘le’, ‘Word c’] mp_tac) >>
     impl_tac
     >- (
      fs [comp_syn_impl_cut_sets_subspt] >>
      drule comp_exp_assigned_vars_tmp_bound >> fs [] >>
      strip_tac >>
      drule comp_exps_assigned_vars_tmp_bound >> fs [] >>
      strip_tac >>
      gen_tac >>
      strip_tac >> fs [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_le_tmp_domain >>
      disch_then (qspecl_then [‘tmp’, ‘l’, ‘h’, ‘p’, ‘le’,
                               ‘itmp’, ‘il’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac
      >- (
       rw [] >>
       drule eval_some_var_cexp_local_lookup >>
       disch_then drule >>
       strip_tac >> res_tac >> fs []) >>
      fs []) >>
     fs []) >>
   fs [wlab_wloc_def] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 8 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’, ‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   once_rewrite_tac [compile_exp_def] >>
   ntac 10 strip_tac >> fs [] >>
   last_x_assum mp_tac >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs [] >>
   fs [OPT_MMAP_def] >> rveq >>
   disch_then drule_all >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘l''’, ‘tmp''’, ‘les'’, ‘p1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   imp_res_tac evaluate_nested_seq_append_first >>
   fs [])
  >- (
   rw [] >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   pairarg_tac >> fs [] >>
   strip_tac >> fs [] >> rveq >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e = (p1,le1,tmp1,l1)’ >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e' = (p2,le2,tmp2,l2)’ >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp1’, ‘l1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_out_rel >> fs [] >>
   strip_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ _ ++ np)’ >>
   qpat_x_assum ‘evaluate (_,st) = _’ mp_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘p2 ++ np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   strip_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rfs [] >>
   ‘eval st' le1 = eval st le1’ by (
     ‘evaluate (nested_seq (p1 ++ p2),t) = (NONE,st')’ by
       metis_tac [evaluate_none_nested_seq_append] >>
     drule nested_seq_pure_evaluation >>
     fs [] >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘l1’, ‘tmp1’, ‘le1’, ‘Word w1’] mp_tac) >>
     impl_tac
     >- (
      fs [comp_syn_impl_cut_sets_subspt] >>
      imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
      gen_tac >>
      strip_tac >> fs [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_le_tmp_domain >>
      disch_then (qspecl_then [‘tmp’, ‘l’, ‘e’, ‘p1’, ‘le1’,
                               ‘tmp1’, ‘l1’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac
      >- (
       rw [] >>
       last_x_assum assume_tac >>
       drule_all eval_some_var_cexp_local_lookup >>
       strip_tac >> res_tac >> fs []) >>
      fs []) >> fs []) >>
     fs [] >> rfs [] >> rveq >>
     fs [wlab_wloc_def, loopSemTheory.set_var_def,
         loopSemTheory.eval_def] >>
     ‘eval (st' with locals := insert (tmp2 + 1) (Word w1) st'.locals)
      le2 = eval st' le2’ by (
       ho_match_mp_tac locals_touched_eq_eval_eq >>
       fs [] >> rw [] >> fs [lookup_insert] >>
       TOP_CASE_TAC >> fs [] >>
       imp_res_tac locals_rel_intro >>
       drule compile_exp_le_tmp_domain >>
       disch_then (qspecl_then [‘tmp1’, ‘l1’, ‘e'’, ‘p2’, ‘le2’,
                                ‘tmp2’, ‘l2’, ‘n’] mp_tac) >>
       impl_tac
       >- (
        conj_tac >- fs [] >>
        conj_tac >- fs [] >>
        conj_tac
        >- (
         rw [] >>
         drule_all eval_some_var_cexp_local_lookup >>
         strip_tac >> res_tac >> fs [] >> rveq >> fs []) >>
        fs []) >>
       fs []) >>
     fs [] >> rfs [] >> rveq >>
     fs [lookup_insert] >>
     fs [get_var_imm_def] >>
     cases_on ‘word_cmp cmp w1 w2’ >>
     fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
         loopSemTheory.set_var_def] >> (
     fs [cut_res_def, list_insert_def] >>
     fs [cut_state_def] >>
     imp_res_tac locals_rel_intro >>
     fs [SUBSET_INSERT_RIGHT] >>
     cases_on ‘st'.clock = 0’ >- cheat >>
     fs [dec_clock_def] >> rveq >> fs [] >>
     fs [lookup_inter, lookup_insert] >>
     conj_tac >- EVAL_TAC >>
     conj_tac >- cheat (* clock is changed *) >>
     fs [list_insert_def, locals_rel_def, domain_inter, SUBSET_INSERT_RIGHT] >>
     rw [] >>
     fs [lookup_inter, lookup_insert] >>
     res_tac >> fs [] >> rveq >> fs [] >>
     ‘n <= tmp2’ by (fs [ctxt_max_def] >> res_tac >> fs []) >>
     fs [domain_lookup])) >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [loopSemTheory.evaluate_def] >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def]
QED

(*
(* with clock *)

Theorem comp_syn_ok_lookup_locals_eq:
  !p s res t n.
   evaluate (p,s) = (res,t) /\ t.clock <> 0 /\
   comp_syntax_ok p /\ n ∈ domain (cut_sets p) /\
    ~MEM n (assigned_vars p) ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC)
  >- fs [evaluate_def]
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [set_var_def, assigned_vars_def, lookup_insert])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [set_var_def, assigned_vars_def, lookup_insert])
  >- (
   drule comp_syn_ok_seq >>
   fs [cut_sets_def, domain_inter] >>
   fs [evaluate_def, assigned_vars_def] >>
   pairarg_tac >> fs [AllCaseEqs ()] >> rveq >> fs [] >>
   dxrule evaluate_clock >> dxrule evaluate_clock >>
   fs [])
  >- (
   drule comp_syn_ok_if >>
   strip_tac >>
   fs [evaluate_def, assigned_vars_def] >>
   fs [AllCaseEqs()]  >> rveq >> fs [cut_sets_def, domain_inter] >>
   cases_on ‘word_cmp cmp x y’ >> fs []
   >- (
    cases_on ‘evaluate (c1,s)’ >> fs [] >>
    fs [get_var_imm_add_clk_eq,
        cut_res_def, cut_state_def, AllCaseEqs()] >>
    rveq >> res_tac >> fs [] >>
    fs [dec_clock_def, lookup_inter] >>
    fs [domain_lookup] >> TOP_CASE_TAC >> fs []) >>
   cases_on ‘evaluate (c2,s)’ >> fs [] >>
   fs [cut_res_def, cut_state_def, AllCaseEqs()] >>
   rveq >> fs [dec_clock_def, lookup_inter] >>
   fs [domain_lookup] >> TOP_CASE_TAC >> fs []) >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [set_var_def, assigned_vars_def, lookup_insert]
QED

Theorem state_rel_add_clock:
  state_rel s t ==>
  ∃ck. state_rel s (t with clock := ck + t.clock)
Proof
  rw [] >>
  qexists_tac ‘0’ >>
  fs [state_component_equality, state_rel_def]
QED


Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) ctxt tmp l.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt s.locals t.locals /\
  ctxt.vmax < tmp ==>
    let (p,le, tmp, l) = compile_exp ctxt tmp l e in
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [nested_seq_def, evaluate_def, eval_def,
       wlab_wloc_def, state_rel_add_clock])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_var_def] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def, state_rel_add_clock])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   pairarg_tac >> fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def] >>
   qexists_tac ‘0’ >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   qexists_tac ‘ck’ >> fs [] >>
   fs [loopSemTheory.eval_def, wlab_wloc_def] >>
   fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
   imp_res_tac state_rel_intro >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   qexists_tac ‘ck’ >> fs [] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp'' le'; LoadByte tmp'' 0w tmp'']’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [set_var_def, wlab_wloc_def] >>
   fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >>
   fs [eval_def, state_rel_def] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [state_rel_add_clock])
  >- (
   rename [‘eval s (Op op es)’] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [Once compile_exp_def] >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   (* qexists_tac ‘0’ >> fs [] >> *)


   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   fs [loopSemTheory.eval_def] >>
   ‘∃ck st.
    evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) ∧
    the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     rw [] >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     disch_then (qspec_then ‘l’ assume_tac) >>
     fs [] >> rfs [] >>
     fs [loopSemTheory.evaluate_def] >>
     last_x_assum (qspecl_then
                   [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_temp_ge >>
     fs [] >> strip_tac >> fs [] >>
     qexists_tac ‘ck’ >>
     qpat_x_assum ‘evaluate (nested_seq p',_) = (_,_)’ assume_tac >>
     drule evaluate_none_nested_seq_append >>
     disch_then (qspec_then ‘p1’ mp_tac) >>
     strip_tac >> fs [] >>




     impl_tac
     >- (
      imp_res_tac evaluate_none_nested_seq_append >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>
     ‘eval r le = eval st le’ suffices_by fs [wlab_wloc_def] >>
     drule evaluate_nested_seq_append_first >>
     disch_then drule >>
     strip_tac >> fs [] >>
     drule compile_exps_prog_update_locals_clock >>
     disch_then drule >>
     strip_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then drule >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘tmp''’, ‘le’, ‘Word c’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_locals_touched_le_tmp >>
      disch_then (qspecl_then [‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le’,
                               ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >> fs []) >>
     fs []) >>







   ‘t with clock := t.clock = t’ by cheat >> fs [] >>
   pop_assum kall_tac


   cases_on ‘evaluate (nested_seq p,t)’ >> fs [] >>
   ‘q = NONE /\ the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     ntac 11 strip_tac >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     disch_then (qspec_then ‘l’ assume_tac) >>
     fs [] >> rfs [] >>
     fs [loopSemTheory.evaluate_def] >>
     last_x_assum (qspecl_then
                   [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_temp_ge >>
     fs [] >>
     impl_tac
     >- (
      imp_res_tac evaluate_none_nested_seq_append >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>
     ‘eval r le = eval st le’ suffices_by fs [wlab_wloc_def] >>
     drule evaluate_nested_seq_append_first >>
     disch_then drule >>
     strip_tac >> fs [] >>
     drule compile_exps_prog_update_locals_clock >>
     disch_then drule >>
     strip_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then drule >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘tmp''’, ‘le’, ‘Word c’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_locals_touched_le_tmp >>
      disch_then (qspecl_then [‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le’,
                               ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >> fs []) >>
     fs []) >>
   fs [wlab_wloc_def] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 8 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’, ‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   once_rewrite_tac [compile_exp_def] >>
   ntac 10 strip_tac >> fs [] >>
   last_x_assum mp_tac >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs [] >>
   fs [OPT_MMAP_def] >> rveq >>
   disch_then drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘l''’, ‘tmp''’, ‘les'’, ‘p1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [] >>
   imp_res_tac evaluate_nested_seq_append_first >>
   fs [])
  >- (
   rw [] >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   strip_tac >> rfs [] >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp''’, ‘l''’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >> fs [] >>
   strip_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ _ ++ np)’ >>


   qpat_x_assum ‘evaluate (_,st) = _’ mp_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘p'' ++ np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   strip_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rfs [] >>
   ‘eval st' le' = eval st le'’ by (
     ‘evaluate (nested_seq (p' ++ p''),t) = (NONE,st')’ by
       metis_tac [evaluate_none_nested_seq_append] >>
     drule nested_seq_pure_evaluation >>
     drule_all compile_exp_prog_update_locals_clock >>
     fs [] >> strip_tac >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘tmp''’, ‘le'’, ‘Word w1’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw [] >>
      imp_res_tac locals_rel_intro >>
      dxrule compile_exp_locals_touched_le_tmp >>
      drule compile_exp_locals_touched_le_tmp >>
      disch_then (qspecl_then [‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le'’,
                               ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >> fs []) >>
     fs []) >>
   fs [] >> rfs [] >> rveq >>
   fs [wlab_wloc_def, loopSemTheory.set_var_def,
       loopSemTheory.eval_def] >>
   qmatch_goalsub_rename_tac ‘lookup (ftmp + _) _’ >>
   ‘eval (st' with locals := insert (ftmp + 1) (Word w1) st'.locals)
    le'' = eval st' le''’ by (
     ntac 3 (pop_assum kall_tac) >>




cheat
     ) >>
   fs [] >> rfs [] >>
   rveq >>
   fs [lookup_insert] >>
   fs [get_var_imm_def] >>
   cases_on ‘word_cmp cmp w1 w2’ >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.set_var_def] >>



   fs [cut_res_def, cut_state_def] >>
   fs [AllCaseEqs()]  >> rveq >> fs [] >>



   ‘domain l'³' ⊆
    tmp'³' + 1 INSERT tmp'³' + 2 INSERT tmp'³' + 1 INSERT
    domain st'.locals’ by cheat >>
   fs [] >>
   ‘st'.clock <> 0’ by cheat >> fs [] >>
   rveq >>
   fs [dec_clock_def] >>
   fs [lookup_inter_alt] >>
   conj_tac >> EVAL_TAC >>
   conj_tac >> fs [state_rel_def]


   , cut_state_def]






























Theorem compile_exp_prog_upd_locals_clock_cases:
  (!ct tmp l (e :α crepLang$exp) p le tmp' l' res s (t :(α, β) state).
    compile_exp ct tmp l e = (p,le,tmp', l') /\
    evaluate (nested_seq p,s) = (res,t) ==>
       t = s with <|locals := t.locals; clock := t.clock|>) /\
   (!ct tmp l (e :α crepLang$exp list) p le tmp' l' res s (t :(α, β) state).
    compile_exps ct tmp l e = (p,le,tmp', l') /\
    evaluate (nested_seq p,s) = (res,t) ==>
       t = s with <|locals := t.locals; clock := t.clock|>)
Proof
  rw []
  >- (
   drule compile_exp_comp_syn_ok >>
   strip_tac >> fs [] >>
   drule comp_syn_ok_upd_local_clock >> fs []) >>
  drule compile_exps_comp_syn_ok >>
  strip_tac >> fs [] >>
  drule comp_syn_ok_upd_local_clock >> fs []
QED

val compile_exp_prog_upd_locals_clock = compile_exp_prog_upd_locals_clock_cases |> CONJUNCT1
val compile_exps_prog_upd_locals_clock = compile_exp_prog_upd_locals_clock_cases |> CONJUNCT2


Theorem comp_syn_ok_upd_local_clock:
  !p s res t.
    evaluate (p,s) = (res,t) /\
    comp_syntax_ok p ==>
     t = s with <|locals := t.locals; clock := t.clock|>
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC)
  >- (
   fs [evaluate_def] >> rveq >>
   fs [state_component_equality])
  >- (
   fs [evaluate_def] >>
   FULL_CASE_TAC >> fs [set_var_def] >>
   rveq >> fs [state_component_equality])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [set_var_def] >> rveq >>
   fs [state_component_equality])
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   FULL_CASE_TAC >> fs []  >> rveq >>
   fs [state_component_equality])
  >- (
   drule comp_syn_ok_if >>
   strip_tac >>
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs [state_component_equality]
   >- (
    cases_on ‘evaluate (c1,s)’ >> fs [] >>
    fs [cut_res_def, cut_state_def, dec_clock_def] >>
    every_case_tac >> fs [] >> rveq >> fs []) >>
   cases_on ‘evaluate (c2,s)’ >> fs [] >>
   fs [cut_res_def, cut_state_def, dec_clock_def] >>
   every_case_tac >> fs [] >> rveq >> fs []) >>
  fs [evaluate_def] >>
  FULL_CASE_TAC >> fs [set_var_def] >>
  rveq >> fs [state_component_equality]
QED



(* p can have cut_set *)

Theorem unassigned_vars_evaluate_same:
  !p s res t n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_vars p) ==>
  lookup n t.locals = lookup n s.locals
Proof
  cheat
QED


Theorem compile_exp_locals_touched_le_tmp:
  !s e v ct tmp l p le tmp' l' n.
   eval s e = SOME v /\
   ctxt_max ct.vmax ct.vars ∧
   (∀n v. FLOOKUP s.locals n = SOME v ⇒
   ∃m. FLOOKUP ct.vars n = SOME m) /\
   compile_exp ct tmp l e = (p,le,tmp', l') /\
   ctxt_max ct.vmax ct.vars /\ ct.vmax < tmp /\
    MEM n (locals_touched le) ==>
    n < tmp'
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >> rw []
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def] >>
   fs [crepSemTheory.eval_def, find_var_def] >>
   res_tac >> rfs [] >> fs [] >>
   rveq >> fs [ctxt_max_def] >>
   res_tac >> fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   fs [locals_touched_def] >> res_tac >> fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [locals_touched_def])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [locals_touched_def])
  >- (
   fs [Once compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [locals_touched_def] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >> fs [] >>
   qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
   qpat_x_assum ‘EVERY _ _’ kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   rw [] >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >>
   fs [OPT_MMAP_def] >> rveq >> fs [] >>
   qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
   once_rewrite_tac [compile_exp_def] >>
   fs [] >>
   strip_tac >> pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs []
   >- (
    last_x_assum (qspec_then ‘h’ mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then drule >>
    fs [] >>
    disch_then (qspecl_then
                  [‘tmp’, ‘l’, ‘p'’, ‘le’, ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    imp_res_tac compile_exps_temp_ge >> fs []) >>
   rfs [] >>
   first_x_assum (qspecl_then [‘l''’, ‘tmp''’ , ‘les'’, ‘p1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >> fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   fs [locals_touched_def]) >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  fs [compile_exp_def] >> rveq >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  fs [locals_touched_def] >>
  res_tac >> fs []
QED


Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) ctxt tmp l.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt s.locals t.locals /\
  ctxt.vmax < tmp ==>
    let (p,le, tmp, l) = compile_exp ctxt tmp l e in
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [nested_seq_def, evaluate_def, eval_def, wlab_wloc_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_var_def] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   pairarg_tac >> fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   fs [loopSemTheory.eval_def, wlab_wloc_def] >>
   fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
   imp_res_tac state_rel_intro >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp'' le'; LoadByte tmp'' 0w tmp'']’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [set_var_def, wlab_wloc_def] >>
   fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >>
   fs [eval_def, state_rel_def] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [Once compile_exp_def] >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   fs [loopSemTheory.eval_def] >>
   cases_on ‘evaluate (nested_seq p,t)’ >> fs [] >>
   ‘q = NONE /\ the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     ntac 11 strip_tac >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     disch_then (qspec_then ‘l’ assume_tac) >>
     fs [] >> rfs [] >>
     fs [loopSemTheory.evaluate_def] >>
     last_x_assum (qspecl_then
                   [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_temp_ge >>
     fs [] >>
     impl_tac
     >- (
      imp_res_tac evaluate_none_nested_seq_append >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>
     ‘eval r le = eval st le’ suffices_by fs [wlab_wloc_def] >>
     drule evaluate_nested_seq_append_first >>
     disch_then drule >>
     strip_tac >> fs [] >>
     drule compile_exps_prog_update_locals_clock >>
     disch_then drule >>
     strip_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then drule >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘tmp''’, ‘le’, ‘Word c’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_locals_touched_le_tmp >>
      disch_then (qspecl_then [‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le’,
                               ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >> fs []) >>
     fs []) >>
   fs [wlab_wloc_def] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 8 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’, ‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   once_rewrite_tac [compile_exp_def] >>
   ntac 10 strip_tac >> fs [] >>
   last_x_assum mp_tac >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs [] >>
   fs [OPT_MMAP_def] >> rveq >>
   disch_then drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘l''’, ‘tmp''’, ‘les'’, ‘p1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [] >>
   imp_res_tac evaluate_nested_seq_append_first >>
   fs [])
  >- (
   rw [] >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   strip_tac >> rfs [] >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp''’, ‘l''’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >> fs [] >>
   strip_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ _ ++ np)’ >>


   qpat_x_assum ‘evaluate (_,st) = _’ mp_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘p'' ++ np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   strip_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘np’ mp_tac) >>
   strip_tac >> fs [] >>
   pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rfs [] >>
   ‘eval st' le' = eval st le'’ by (
     ‘evaluate (nested_seq (p' ++ p''),t) = (NONE,st')’ by
       metis_tac [evaluate_none_nested_seq_append] >>
     drule nested_seq_pure_evaluation >>
     drule_all compile_exp_prog_update_locals_clock >>
     fs [] >> strip_tac >> fs [wlab_wloc_def] >>
     disch_then (qspecl_then [‘tmp''’, ‘le'’, ‘Word w1’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw [] >>
      imp_res_tac locals_rel_intro >>
      dxrule compile_exp_locals_touched_le_tmp >>
      drule compile_exp_locals_touched_le_tmp >>
      disch_then (qspecl_then [‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le'’,
                               ‘tmp''’, ‘l''’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >> fs []) >>
     fs []) >>
   fs [] >> rfs [] >> rveq >>
   fs [wlab_wloc_def, loopSemTheory.set_var_def,
       loopSemTheory.eval_def] >>
   qmatch_goalsub_rename_tac ‘lookup (ftmp + _) _’ >>
   ‘eval (st' with locals := insert (ftmp + 1) (Word w1) st'.locals)
    le'' = eval st' le''’ by (
     ntac 3 (pop_assum kall_tac) >>




cheat
     ) >>
   fs [] >> rfs [] >>
   rveq >>
   fs [lookup_insert] >>
   fs [get_var_imm_def] >>
   cases_on ‘word_cmp cmp w1 w2’ >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.set_var_def] >>



   fs [cut_res_def, cut_state_def] >>
   fs [AllCaseEqs()]  >> rveq >> fs [] >>



   ‘domain l'³' ⊆
    tmp'³' + 1 INSERT tmp'³' + 2 INSERT tmp'³' + 1 INSERT
    domain st'.locals’ by cheat >>
   fs [] >>
   ‘st'.clock <> 0’ by cheat >> fs [] >>
   rveq >>
   fs [dec_clock_def] >>
   fs [lookup_inter_alt] >>
   conj_tac >> EVAL_TAC >>
   conj_tac >> fs [state_rel_def]


   , cut_state_def]















   ) >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [loopSemTheory.evaluate_def] >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def]
QED









QED


Theorem nested_seq_pure_evaluation:
  !s e v t ctxt tmp l p le ntmp nl st q.
  eval s e = SOME v ∧ state_rel s t ∧ mem_rel ctxt s.memory t.memory ∧
  globals_rel ctxt s.globals t.globals ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt s.locals t.locals ∧ ctxt.vmax < tmp /\
  compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
  evaluate (nested_seq p, t) = (NONE, st) /\
  st = t with <|locals := st.locals; clock := st.clock |> /\
  (!n. MEM n (assigned_vars (nested_seq q)) ==> ntmp <= n) /\
  (!(st :(α, β) loopSem$state) pt res. evaluate (nested_seq q,st) = (res, pt) ==>
   res = NONE /\ pt = st with <|locals := pt.locals; clock := pt.clock |>) ==>
    ?res (nt :(α, β) loopSem$state). evaluate (nested_seq (p ++ q),t) = (res, nt) /\
    eval nt le = SOME (wlab_wloc ctxt v)
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   fs [crepSemTheory.eval_def] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   cases_on ‘evaluate (nested_seq q,t)’ >>
   fs [eval_def, wlab_wloc_def])
  >- (
   fs [crepSemTheory.eval_def] >>
   rveq >> fs [] >>
   fs [compile_exp_def, find_var_def] >>
   rveq >> fs [] >>
   cases_on ‘evaluate (nested_seq q,t)’ >>
   fs [] >>
   first_x_assum drule >>
   strip_tac >> fs [] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def] >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    CCONTR_TAC >> fs [] >>
    ‘n <= ctxt.vmax’ by (
      fs [ctxt_max_def] >> res_tac >> fs []) >>
    ‘n < ntmp’ by DECIDE_TAC >>
    res_tac >> fs []) >>
   fs [])
  >- (
   fs [crepSemTheory.eval_def, CaseEq "option"] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘v1’ >> fs [] >>
   imp_res_tac code_rel_intro >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       find_lab_def, domain_lookup, set_var_def] >>
   rveq >> fs [] >>
   fs [eval_def] >>
   cases_on ‘evaluate (nested_seq q,t with locals :=
              insert tmp (Loc loc 0) t.locals)’ >>
   fs [] >>
   res_tac >> fs [] >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspec_then ‘tmp’ mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >>
   ‘t with <|locals := insert tmp (Loc loc 0) t.locals;
    clock := t.clock|> = t with <|locals := insert tmp (Loc loc 0) t.locals|>’ by
     fs [state_component_equality] >>
   fs [wlab_wloc_def])
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   last_x_assum drule >>
   disch_then drule_all >>
   strip_tac >>
   fs [eval_def, wlab_wloc_def] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   fs [] >> strip_tac >>
   pop_assum (assume_tac o GSYM) >>
   res_tac >> fs [] >>
   fs [mem_load_def, crepSemTheory.mem_load_def] >>
   fs [Once state_component_equality, state_rel_def, mem_rel_def] >>
   last_x_assum (qspec_then ‘w’ mp_tac) >> fs [] >>
   first_x_assum (qspec_then ‘w’ mp_tac) >>
   fs [])
  >- cheat
  >- cheat
  >- (
   rpt gen_tac >>
   strip_tac >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >>
   rveq >> fs [] >>
   fs [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   fs [eval_def] >>
   cases_on ‘evaluate (nested_seq (p ++ q),t)’ >> fs [] >>
   ‘the_words (MAP (λa. eval st a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     qpat_x_assum ‘∀n. MEM n (assigned_vars (nested_seq q)) ⇒ ntmp <= n’ kall_tac >>
     pop_assum kall_tac >> pop_assum mp_tac >>
     pop_assum kall_tac >>
     strip_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘st’, ‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     rpt strip_tac >>
     fs [OPT_MMAP_def] >> rveq >> fs [] >>
     qpat_x_assum ‘compile_exps _ _ _ (h::es) = _’ mp_tac >>
     once_rewrite_tac [compile_exp_def] >>
     fs [] >> strip_tac >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >>
     rveq >> fs [] >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule >> disch_then drule >>
     fs [] >>
     disch_then (qspecl_then [‘tmp’, ‘l’, ‘p'’, ‘le’, ‘tmp'’, ‘l''’] mp_tac) >>
     fs [] >>
     cases_on ‘evaluate (nested_seq p',t) = (NONE,st')’ >> fs [] >>
     disch_then (qspec_then ‘[]’ mp_tac) >>
     fs [] >>
     impl_tac
     >- (
      conj_tac >- cheat >>
      fs [nested_seq_def, assigned_vars_def, evaluate_def] >>
      fs [state_component_equality]) >>
     strip_tac >>


      )




     last_x_assum mp_tac >>
     impl_tac >- metis_tac [] >>
     fs [] >>
     disch_then drule >>
     fs [] >>
     disch_then (qspecl_then [‘l''’, ‘tmp'’,
                              ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs []







     rveq >> rfs [] >>
     pairarg_tac >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac)>>
     simp [] >>
     disch_then (qspecl_then [‘t’, ‘ctxt’] mp_tac) >>


     disch_then (qspecl_then [‘tmp’, ‘l’, ‘p'’, ‘le’, ‘tmp'’, ‘l''’] mp_tac) >>
     simp [] >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     fs [wordSemTheory.the_words_def] >>
     cases_on ‘evaluate (nested_seq p', t)’ >>
     disch_then (qspecl_then [‘p1’, ‘r’, ‘st’] mp_tac) >>
     impl_tac
     >- cheat >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wlab_wloc_def] >>
     last_x_assum drule >>
     fs [] >>
     disch_then (qspecl_then [‘l''’, ‘tmp'’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     impl_tac >- cheat >>
     fs []) >>




   )


QED



Theorem nested_seq_pure_evaluation:
  !s e v t ctxt tmp l p le ntmp nl q st nt.
  eval s e = SOME v ∧ state_rel s t ∧ mem_rel ctxt s.memory t.memory ∧
  globals_rel ctxt s.globals t.globals ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt s.locals t.locals ∧ ctxt.vmax < tmp /\
  compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
  (!n. MEM n (assigned_vars (nested_seq q)) ==> ntmp <= n) /\
  evaluate (nested_seq p, t) = (NONE, st) /\
  evaluate (nested_seq q,st) = (NONE, nt) /\
  nt = st with <|locals := nt.locals; clock := nt.clock |> ==>
  eval nt le = SOME (wlab_wloc ctxt v) /\
  state_rel s st ∧ mem_rel ctxt s.memory st.memory ∧
  globals_rel ctxt s.globals st.globals ∧ code_rel ctxt s.code st.code ∧
  locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   fs [crepSemTheory.eval_def] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   fs [nested_seq_def, evaluate_def, eval_def,
       wlab_wloc_def])
  >- (
   fs [crepSemTheory.eval_def] >>
   rveq >> fs [] >>
   fs [compile_exp_def, find_var_def] >>
   rveq >> fs [] >>
   imp_res_tac locals_rel_intro >>
   fs [nested_seq_def, evaluate_def] >>
   rveq >> fs [eval_def] >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    CCONTR_TAC >> fs [] >>
    ‘n <= ctxt.vmax’ by (
      fs [ctxt_max_def] >> res_tac >> fs []) >>
    ‘n < ntmp’ by DECIDE_TAC >>
    res_tac >> fs []) >>
   fs [])
  >- (
   fs [crepSemTheory.eval_def, CaseEq "option"] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘v1’ >> fs [] >>
   imp_res_tac code_rel_intro >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       find_lab_def, domain_lookup, set_var_def] >>
   rveq >> fs [] >>
   fs [eval_def] >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspec_then ‘tmp’ mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >>
   fs [wlab_wloc_def] >>
   strip_tac >>
   conj_tac >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rw [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >>
   strip_tac >> fs [] >>
   last_x_assum drule >>
   fs [lookup_insert])
  >- (
   rpt gen_tac >>
   strip_tac >>
   last_x_assum mp_tac >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   fs [Once compile_exp_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   fs [eval_def] >>
   disch_then drule_all >>
   strip_tac >> fs [wlab_wloc_def] >>
   drule_all compile_exp_prog_update_locals_clock >>
   strip_tac >> fs [] >>
   fs [mem_load_def, crepSemTheory.mem_load_def] >>
   fs [Once state_component_equality, state_rel_def, mem_rel_def] >>
   last_x_assum (qspec_then ‘w’ mp_tac) >> fs [] >>
   first_x_assum (qspec_then ‘w’ mp_tac) >>
   fs [])
  >- (
   rpt gen_tac >>
   strip_tac >>
   last_x_assum mp_tac >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   fs [Once compile_exp_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   fs [eval_def] >>
   cases_on ‘evaluate (nested_seq p',t)’ >>
   reverse (cases_on ‘q'’) >> fs []
   >- (
    drule evaluate_not_none_nested_seq_append >>
    disch_then (qspec_then ‘[Assign tmp' le'; LoadByte tmp' 0w tmp']’ mp_tac) >>
    fs []) >>
   disch_then (qspecl_then [‘t’, ‘ctxt’, ‘tmp’, ‘l’, ‘p'’, ‘le'’, ‘tmp'’, ‘l'’] mp_tac) >>
   disch_then (qspecl_then [‘[]’, ‘r’, ‘r’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    conj_tac
    >- (
     rw [] >>
     fs [nested_seq_def] >>
     fs [assigned_vars_def] >> res_tac >> fs []) >>
    fs [state_component_equality, nested_seq_def, evaluate_def]) >>
   strip_tac >> fs [] >>
   ‘lookup tmp' st.locals = SOME (wlab_wloc ctxt (Word (w2w w')))’ by (
     drule_all evaluate_nested_seq_append_first >>
     fs [] >> strip_tac >>
     fs [nested_seq_def, evaluate_def] >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >>
     cases_on ‘eval r le'’ >> fs [] >> rveq >> fs [] >>
     fs [set_var_def, lookup_insert, wlab_wloc_def] >>
     imp_res_tac state_rel_intro >> fs [] >>
     fs [wordSemTheory.mem_load_byte_aux_def,
         panSemTheory.mem_load_byte_def] >>
     imp_res_tac mem_rel_intro >>
     last_x_assum (qspec_then ‘byte_align w’ mp_tac) >>
     strip_tac >> fs [] >>
     cases_on ‘s.memory (byte_align w)’ >> fs [wlab_wloc_def] >>
     pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
     fs [] >> rfs [] >> rveq >> fs [] >>
     fs [state_component_equality] >>
     qpat_x_assum ‘_ = st.locals’ (assume_tac o GSYM) >>
     fs []) >>
   fs [] >>
   drule_all evaluate_nested_seq_append_first >>
   fs [nested_seq_def, evaluate_def] >>
   pairarg_tac >> fs [] >>
   fs [set_var_def, lookup_insert] >>
   fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >> fs [] >>
   fs [wordSemTheory.mem_load_byte_aux_def,
       panSemTheory.mem_load_byte_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align w’ mp_tac) >>
   strip_tac >> fs [] >>
   cases_on ‘s.memory (byte_align w)’ >> fs [wlab_wloc_def] >>
   pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
   fs [] >> rfs [] >> rveq >> fs [] >>
   strip_tac >> strip_tac >>
   fs [] >> rveq >> fs [] >>
   dxrule unassigned_vars_evaluate_same >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspec_then ‘tmp'’ assume_tac) >>
   strip_tac >>
   pop_assum kall_tac >> fs [] >>
   pop_assum mp_tac >> fs [] >>
   impl_tac
   >- (
    CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >>
   fs [] >> strip_tac >> fs [] >>
   fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rw [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >>
   strip_tac >> fs [] >>
   first_x_assum drule >>
   strip_tac >> fs [] >>
   drule compile_exp_temp_ge >>
   strip_tac >>
   fs [lookup_insert])
  >- (
   fs [crepSemTheory.eval_def] >>
   rveq >> fs [] >>
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   fs [nested_seq_def, evaluate_def, eval_def,
       wlab_wloc_def] >>
   imp_res_tac globals_rel_intro >>
   res_tac >> fs [] >> rveq >>
   fs [state_component_equality])
  >- (
   rpt gen_tac >>
   strip_tac >>
   last_x_assum mp_tac >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >>
   rveq >> fs [] >>
   fs [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   fs [eval_def] >>
   strip_tac >>
   ‘the_words (MAP (λa. eval st a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     qpat_x_assum ‘∀n. MEM n (assigned_vars (nested_seq q)) ⇒ ntmp <= n’ kall_tac >>
     qpat_x_assum ‘evaluate (nested_seq q,st) = (NONE,nt)’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘st’, ‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     ntac 12 strip_tac >>





     qpat_x_assum ‘OPT_MMAP _ (_::_) = _’ mp_tac >>
     simp [OPT_MMAP_def] >>
     strip_tac >>  rveq >>
     qpat_x_assum ‘compile_exps _ _ _ (h::es) = _’ mp_tac >>
     once_rewrite_tac [compile_exp_def] >>
     simp [] >>
     strip_tac >> rveq >> rfs [] >>
     pairarg_tac >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac)>>
     simp [] >>
     disch_then (qspecl_then [‘t’, ‘ctxt’] mp_tac) >>


     disch_then (qspecl_then [‘tmp’, ‘l’, ‘p'’, ‘le’, ‘tmp'’, ‘l''’] mp_tac) >>
     simp [] >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     fs [wordSemTheory.the_words_def] >>
     cases_on ‘evaluate (nested_seq p', t)’ >>
     disch_then (qspecl_then [‘p1’, ‘r’, ‘st’] mp_tac) >>
     impl_tac
     >- cheat >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wlab_wloc_def] >>
     last_x_assum drule >>
     fs [] >>
     disch_then (qspecl_then [‘l''’, ‘tmp'’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     impl_tac >- cheat >>
     fs []) >>




      )


     last_x_assum drule >>
     fs [] >>
     disch_then (qspecl_then [‘l''’, ‘tmp'’, ‘les'’, ‘p1’, ‘q’] mp_tac) >>
     fs []






     impl_tac
     >- (



      )

nt = st

     cheat) >>
   fs [] >>



































     ) >>
   fs [] >>




   )









Theorem foo:
  ∀s e v (t :('a, 'b) state) ctxt tmp l.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt s.locals t.locals /\
  ctxt.vmax < tmp  ==>
    let (p,le, tmp, l) = compile_exp ctxt tmp l e in
     ?st. evaluate (nested_seq p,t) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [nested_seq_def, evaluate_def, eval_def, wlab_wloc_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_var_def] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   pairarg_tac >> fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   fs [loopSemTheory.eval_def, wlab_wloc_def] >>
   fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
   imp_res_tac state_rel_intro >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp'' le'; LoadByte tmp'' 0w tmp'']’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [set_var_def, wlab_wloc_def] >>
   fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >>
   fs [eval_def, state_rel_def] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   fs [eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [Once compile_exp_def] >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   fs [loopSemTheory.eval_def] >>
   cases_on ‘evaluate (nested_seq p,t)’ >> fs [] >>
   ‘q = NONE /\ the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     ntac 11 strip_tac >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     disch_then (qspec_then ‘l’ assume_tac) >>
     fs [] >> rfs [] >>
     fs [loopSemTheory.evaluate_def] >>
     last_x_assum (qspecl_then
                   [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_temp_ge >>
     fs [] >>
     impl_tac
     >- (
      imp_res_tac evaluate_none_nested_seq_append >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>
     ‘eval r le = eval st le’ suffices_by fs [wlab_wloc_def] >>
     drule isit >>
     disch_then (qspecl_then [‘t’, ‘ctxt’, ‘tmp’] mp_tac) >>
     fs [] >>
     disch_then drule >>
     disch_then (qspecl_then [‘p1’, ‘st’, ‘r’] mp_tac) >>
     fs [] >>
     impl_tac >- cheat >>
     fs []) >>
   fs [wlab_wloc_def] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 8 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’, ‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   once_rewrite_tac [compile_exp_def] >>
   ntac 10 strip_tac >> fs [] >>
   last_x_assum mp_tac >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs [] >>
   fs [OPT_MMAP_def] >> rveq >>
   disch_then drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘l''’, ‘tmp''’, ‘les'’, ‘p1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [] >>
   imp_res_tac evaluate_nested_seq_append_first >>
   fs [])


       compile_exp ct tmp l ce = (prog,le,ntmp,nl) /\
  evaluate (nested_seq prog,s) = (NONE,st) /\
  eval st le = SOME w /\
  (!n. MEM n (assigned_vars prog') ==> ntmp <= n)




  evaluate (nested_seq q,st) = (res, nt) /\
  res = NONE /\ nt = st with locals := nt.locals ==>
  evaluate (nested_seq (p ++ q), s) = (NONE, nt) /\
   eval nt e = SOME w
Proof

QED

eval cexp cs = SOME w
  compile_exp cexp tmp = (prog, lexp, tmp') ==>
  ?...
    evaluate (prog ++ prog', s) = (NONE, s') /\
    eval lexp s' = SOME (convert w)
  lexp -- only reads from vars < tmp'
  prog' -- only assigns to vars >= tmp'
  prog' -- only touches the locals part of state



fs []
  evaluate (prog ++ prog', s) = (NONE, s') /\
    eval lexp s' = SOME (convert w)



  prog =unseq p p'
       evaluate p t = st
       evaluate p' st = r

       le:les


     ‘eval r le = eval st le’ by (
       pop_assum kall_tac >>
       qpat_x_assum ‘T’ kall_tac >>
       qpat_x_assum ‘EVERY _ _’ kall_tac >>
       rpt (pop_assum mp_tac) >>
       MAP_EVERY qid_spec_tac [‘t’, ‘p1’, ‘st’,‘les'’ ,‘tmp'’, ‘l'’,
                               ‘tmp''’, ‘l''’, ‘t'’, ‘es’] >>
       Induct
       >- (
        rw [] >>
        fs [compile_exp_def] >> rveq >>
        fs [evaluate_def] >> rveq >> fs []) >>
       rw [] >>
       rfs [] >>
       fs [OPT_MMAP_def] >> rveq >> fs [] >>
       qpat_x_assum ‘compile_exps _ _ _ _ = _ ’ mp_tac >>
       once_rewrite_tac [compile_exp_def] >>
       fs [] >>
       pairarg_tac >> fs [] >>
       pairarg_tac >> fs [] >>
       strip_tac >> fs [] >> rveq >>
       first_x_assum drule >>
       disch_then drule >>
       fs [] >>
       strip_tac >>








































Theorem abc:
  !ct tmp l e ps les ntmp nl i t.
   compile_exp ct tmp l e = (ps, les, ntmp, nl) /\
   i < LENGTH ps ==>
     let (q,st) = evaluate (nested_seq (TAKE i ps),t);
         (r, nt)  = evaluate (EL i ps, st) in
         st.globals = nt.globals
Proof
  qsuff_tac ‘(!ct tmp l (e :α crepLang$exp) ps les ntmp nl i t.
               compile_exp ct tmp l e = (ps, les, ntmp, nl) /\
               i < LENGTH ps==>
               let (q,st:(α, β) state) = evaluate (nested_seq (TAKE i ps),t);
               (r, nt)  = evaluate (EL i ps, st) in
               st.globals = nt.globals) /\
             (!ct tmp l (es :α crepLang$exp list) ps les ntmp nl i t.
               compile_exps ct tmp l es = (ps, les, ntmp, nl) /\
                i < LENGTH ps ==>
                let (q,st:(α, β) state) = evaluate (nested_seq (TAKE i ps),t);
                (r, nt)  = evaluate (EL i ps, st) in
                st.globals = nt.globals)’
  >- metis_tac [] >>
  ho_match_mp_tac compile_exp_ind >> rw []
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘i’ >> fs [] >>
   fs [nested_seq_def, evaluate_def])
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘i’ >> fs [] >>
   fs [nested_seq_def, evaluate_def])
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘i’ >> fs [] >>
   fs [nested_seq_def, evaluate_def] >>
   every_case_tac >> fs [set_var_def] >> rveq >> fs [])
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   last_x_assum (qspec_then ‘i’ mp_tac) >>
   fs [] >>
   disch_then (qspec_then ‘t’ mp_tac) >>
   pairarg_tac >> fs []) >>
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   ‘p <> []’ by cheat >>
   fs [] >>
   cases_on ‘i < LENGTH p’ >> fs []
   >- (
    last_x_assum (qspec_then ‘i’ mp_tac) >>
    fs [] >>
    ‘i - LENGTH p = 0’ by fs [] >>
    fs [] >>
    dxrule TAKE_APPEND1 >>
    disch_then (qspec_then ‘[Assign tmp' le; LoadByte tmp' 0w tmp']’ mp_tac) >>
    strip_tac >> fs [] >>
    disch_then (qspec_then ‘t’ mp_tac) >>
    fs [EL_APPEND_EQN]) >>
   fs [NOT_LESS] >>
   cases_on ‘LENGTH p = i’ >> fs []
   >- (
    ‘EL i (p ++ [Assign tmp' le; LoadByte tmp' 0w tmp']) =
     Assign tmp' le’ by fs [EL_APPEND_EQN] >>
    fs [evaluate_def, CaseEq "option", set_var_def] >> rveq >> fs []) >>
   ‘EL i (p ++ [Assign tmp' le; LoadByte tmp' 0w tmp']) =
    LoadByte tmp' 0w tmp'’ by (
     fs [EL_APPEND_EQN] >>
     ‘i - LENGTH p = 1’ by fs [] >>
     fs []) >>
   fs [evaluate_def, CaseEq "option", CaseEq "word_loc",
       set_var_def] >> rveq >> fs [])
  >- (
   TRY (rpt (pairarg_tac >> fs [])) >>
   fs [compile_exp_def] >> rveq >> fs [] >>
   cases_on ‘i’ >> fs [] >>
   fs [nested_seq_def, evaluate_def] >>
   every_case_tac >> fs [set_var_def] >> rveq >> fs [])
  >- (
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
   once_rewrite_tac [compile_exp_def] >>
   strip_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> fs [] >>
   last_x_assum (qspec_then ‘i’ mp_tac) >>
   fs [] >>
   disch_then (qspec_then ‘t’ mp_tac) >>
   fs [])
  >- (
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   ‘p <> [] ∧ p' <> []’ by cheat >>
   fs [] >>
   cases_on ‘i < LENGTH p’ >> fs []
   >- (
    first_x_assum (qspec_then ‘i’ mp_tac) >>
    fs [] >>
    ‘i - LENGTH p = 0’ by fs [] >>
    fs [] >>
    dxrule TAKE_APPEND1 >>
    disch_then (qspec_then ‘p' ++
                 [Assign (tmp'' + 1) le; Assign (tmp'' + 2) le';
                  If cmp (tmp'' + 1) (Reg (tmp'' + 2))
                    (Assign (tmp'' + 1) (Const 1w))
                    (Assign (tmp'' + 1) (Const 0w))
                    (insert (tmp'' + 1) () l'')]’ mp_tac) >>
    strip_tac >> fs [] >>
    disch_then (qspec_then ‘t’ mp_tac) >>
    fs [EL_APPEND_EQN]) >>
   fs [NOT_LESS] >>
   cases_on ‘i <= LENGTH (p ++ p')’
   >- (
    dxrule TAKE_APPEND1 >>
    disch_then (qspec_then ‘
                 [Assign (tmp'' + 1) le; Assign (tmp'' + 2) le';
                  If cmp (tmp'' + 1) (Reg (tmp'' + 2))
                  (Assign (tmp'' + 1) (Const 1w))
                  (Assign (tmp'' + 1) (Const 0w))
                  (insert (tmp'' + 1) () l'')]’ mp_tac) >>
    strip_tac >> fs [] >>





   )


   cases_on ‘i’ >> fs []
   >- (
    fs [nested_seq_def, evaluate_def] >>
    rveq >> fs [] >>
    cases_on ‘p’ >> fs [] >>
    fs [evaluate_def] >>
    every_case_tac >> fs [set_var_def] >> rveq >> fs []

    )


   disch_then (qspec_then ‘t’ mp_tac) >>
   pairarg_tac >> fs [])

   rveq >> rfs [])




  >- fs [compile_exp_def]
  >- fs [compile_exp_def]
QED


(*
Definition prog_comp_def:
  (prog_comp ct tmp l [] = []) /\
  (prog_comp ct tmp l (e::es) =
   let (p, le, tmp, l) = compile_exp ct tmp l e in
     p :: prog_comp ct tmp l es)
End


Theorem compile_exps_prog_seq:
  !es ct tmp l.
   ?les tmp' l'.
   compile_exps ct tmp l es = (nested_seq (prog_comp ct tmp l es),les,tmp', l')
Proof
  Induct >> rw []
  >- fs [compile_exp_def, nested_seq_def, prog_comp_def] >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  fs [] >>
  fs [prog_comp_def] >>
  fs [nested_seq_def] >>
  last_x_assum (qspecl_then [‘ct’, ‘tmp'’, ‘l'’] mp_tac) >>
  fs []
QED
*)






  rw [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  ‘LENGTH es = LENGTH les’ by cheat >>
  match_mp_tac locals_touched_eq_eval_eq >>
  conj_tac
  >- (
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘q’,‘t’,‘l’,‘l'’, ‘tmp'’, ‘ctxt’,‘tmp’, ‘n’, ‘p’, ‘st’,
                           ‘r’,‘nt’,  ‘les’, ‘es’] >>
   Induct
   >- (
    rw [] >> fs [compile_exp_def] >>
    rveq >> fs []) >>
   rw [] >>
   cases_on ‘les’ >> fs [] >>



   )



     Theorem abc:
  !ctxt tmp l e ps les ntmp nl i.
   compile_exp ctxt tmp l e = (ps, les, ntmp, nl) /\
   i <= LENGTH ps ==>
     let (q,st) = evaluate (nested_seq (TAKE i ps),t);
         (r, nt)  = evaluate (nested_seq (DROP i ps), st) in
         st.globals = nt.globals
Proof
  rw [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  ‘LENGTH es = LENGTH les’ by cheat >>
  match_mp_tac locals_touched_eq_eval_eq >>
  conj_tac
  >- (
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘q’,‘t’,‘l’,‘l'’, ‘tmp'’, ‘ctxt’,‘tmp’, ‘n’, ‘p’, ‘st’,
                           ‘r’,‘nt’,  ‘les’, ‘es’] >>
   Induct
   >- (
    rw [] >> fs [compile_exp_def] >>
    rveq >> fs []) >>
   rw [] >>
   cases_on ‘les’ >> fs [] >>



   )




     Theorem abc:
  !es ctxt tmp l p les tmp' l' n t.
   compile_exps ctxt tmp l es = (p, les, tmp', l') /\
   n < LENGTH les ==>
     let (q,st) = evaluate (nested_seq (TAKE (n + 1) p),t);
         (r, nt)  = evaluate (nested_seq (DROP (n + 1) p), st) in
         eval st (EL n les) = eval nt (EL n les)
Proof
  rw [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  ‘LENGTH es = LENGTH les’ by cheat >>
  match_mp_tac locals_touched_eq_eval_eq >>
  conj_tac
  >- (
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘q’,‘t’,‘l’,‘l'’, ‘tmp'’, ‘ctxt’,‘tmp’, ‘n’, ‘p’, ‘st’,
                           ‘r’,‘nt’,  ‘les’, ‘es’] >>
   Induct
   >- (
    rw [] >> fs [compile_exp_def] >>
    rveq >> fs []) >>
   rw [] >>
   cases_on ‘les’ >> fs [] >>



   )




(*

  eval cexp cs = SOME w
  compile_exp cexp tmp = (prog, lexp, tmp') ==>
  ?...
    evaluate (prog ++ prog', s) = (NONE, s') /\
    eval lexp s' = SOME (convert w)


  lexp -- only reads from vars < tmp'
  prog' -- only assigns to vars >= tmp'
  prog' -- only touches the locals part of state


  compile_exp cexp tmp liveset = (prog, lexp, tmp', liveset') ==>
  only_reads_from_lower tmp' prog /\
  only assigns_to_ge tmp prog (also liveset) /\
  subspt liveset liveset'


  compile_exp .. = (ps, ...) ==> prop is true for ps
  prop is true for ps ==>
  ps

*)



Theorem abc:
  !es ctxt tmp l p les tmp' l' n t.
   compile_exps ctxt tmp l es = (p, les, tmp', l') /\
   n < LENGTH les ==>
     let (a,inst) = evaluate (nested_seq (TAKE n p),t);
         (b, nst) = evaluate (nested_seq (TAKE (n + 1) p),inst);
         (c, nist) = evaluate (nested_seq (TAKE (n + 1) p),t);
         (d, fist)  = evaluate (nested_seq (DROP (n + 1) p), nist) in
         eval nst (EL n les) = eval fist (EL n les)
Proof
  rw [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  match_mp_tac locals_touched_eq_eval_eq >>
  conj_tac >-



  Induct >> rw []
  >- (
   fs [compile_exp_def] >>
   rveq >> fs []) >>
  qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> rveq >> fs [] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   match_mp_tac locals_touched_eq_eval_eq >> cheat) >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>


  last_x_assum mp_tac >>
  disch_then drule_all >>
  disch_then (qspecl_then [‘s1’] mp_tac) >>
  fs [] >>
  ‘res = NONE’ by cheat >> fs [] >> rveq >> fs []
  ‘res' = NONE’ by cheat >> fs [] >>
  fs [ADD1] >>
  pairarg_tac >> fs [] >>
  strip_tac >> fs []


  disch_then (qspecl_then [‘ctxt’, ‘tmp''’, ‘l''’, ‘p1’, ‘les'’, ‘tmp'’, ‘l'’] mp_tac) >>
  fs []











   ) >>



   )



QED

Theorem foo:
  ∀s e v (t :('a, 'b) state) ctxt tmp l.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt s.locals t.locals /\
  ctxt.vmax < tmp  ==>
    let (p,le, tmp, l) = compile_exp ctxt tmp l e in
      ?st. evaluate (nested_seq p,t) = (NONE,st) /\ eval st le = SOME (wlab_wloc ctxt v) /\
    state_rel s st /\ mem_rel ctxt s.memory st.memory /\
    globals_rel ctxt s.globals st.globals /\
    code_rel ctxt s.code st.code /\
    locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [evaluate_def, eval_def, wlab_wloc_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [evaluate_def, find_var_def] >>
   imp_res_tac locals_rel_intro >>
   fs [eval_def])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   pairarg_tac >> fs [compile_exp_def] >> rveq >>
   fs [evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   fs [loopSemTheory.eval_def, wlab_wloc_def] >>
   fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
   imp_res_tac state_rel_intro >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ assume_tac) >>
   fs [] >> rfs [] >>
   fs [loopSemTheory.evaluate_def] >>
   fs [set_var_def, wlab_wloc_def] >>
   fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   imp_res_tac mem_rel_intro >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   strip_tac >> fs [wlab_wloc_def] >>
   imp_res_tac state_rel_intro >>
   fs [eval_def, state_rel_def] >>
   imp_res_tac compile_exp_temp_ge >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [loopSemTheory.evaluate_def] >>
   fs [eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rw [] >>
   pairarg_tac >> fs [] >>
   fs [Once compile_exp_def] >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
   fs [loopSemTheory.eval_def] >>
   ‘LENGTH les = LENGTH es’ by cheat >>
   (* cases_on ‘evaluate (p,t)’ >> fs [] >> *)

   ‘!n. n < LENGTH les ==>
     eval
     (SND (evaluate (nested_seq (TAKE (n+1) p'),
      SND (evaluate (nested_seq (TAKE n p'), t))))) (EL n les) =
     eval
     (SND (evaluate (nested_seq (DROP (n+1) p'),
      SND (evaluate (nested_seq (TAKE (n+1) p'), t)))))
     (EL n les)’ by (
     qpat_x_assum ‘EVERY _ _’ kall_tac >>
     qpat_x_assum ‘word_op _ _ = _ ’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘ctxt’, ‘s’,‘t’, ‘p'’, ‘tmp'’, ‘tmp’,
                             ‘l'’,‘l’, ‘ws’, ‘es’, ‘les’] >>
     Induct
     >- rw [] >>
     rw [] >>



     cases_on ‘n’ >> fs []
     >- (
      fs [nested_seq_def, evaluate_def]


      )


     match_mp_tac eval_states_eq >>


     strip_tac

     last_x_assum mp_tac >>
     disch_then drule >>
     disch_then drule >>
     disch_then drule >>

     impl_tac >- metis_tac [] >>

     cases_on ‘n’ >> fs []
     >- (
      cases_on ‘es’ >> fs [] >>
      qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
      once_rewrite_tac [compile_exp_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      strip_tac >> rveq >> fs [] >>
      fs [nested_seq_def, evaluate_def] >>
      pairarg_tac >> fs [] >>
      first_x_assum (qspec_then ‘h'’ mp_tac) >>
      fs [] >>
      fs [OPT_MMAP_def] >> fs [] >>
      disch_then drule_all >>
      disch_then (qspec_then ‘l’ mp_tac) >>
      pairarg_tac >> fs [] >>
      rveq >> fs [] >>
      strip_tac >> fs [] >>
      last_x_assum mp_tac >>
      disch_then (qspecl_then [‘t'’, ‘t''’, ‘l''’, ‘l'’, ‘tmp''’, ‘tmp'’,
                               ‘p1’, ‘s1’ ,‘s’, ‘ctxt’] mp_tac) >>
      fs []

         impl_tac >- cheat >>




      )



      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>




  (* length les = length es *)








   ‘q = NONE /\
    the_words (MAP (λa. eval r a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws))’ by (
     qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
     rpt (pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
     Induct
     >- (
      rw [] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [compile_exp_def] >> rveq >>
      fs [loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
     rpt gen_tac >>
     once_rewrite_tac [compile_exp_def] >>
     ntac 11 strip_tac >> fs [] >>
     fs [OPT_MMAP_def] >> rveq >>
     pairarg_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     first_x_assum (qspec_then ‘h’ mp_tac) >>
     fs [] >>
     disch_then drule_all >>
     disch_then (qspec_then ‘l’ assume_tac) >>
     fs [] >> rfs [] >>
     fs [loopSemTheory.evaluate_def] >>
     last_x_assum (qspecl_then
                   [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘st’] mp_tac) >>
     fs [] >>
     imp_res_tac compile_exp_temp_ge >>
     fs [] >>
     strip_tac >> fs [] >>
     cases_on ‘h'’ >> fs [] >>
     fs [wordSemTheory.the_words_def] >>

  prog =unseq p p'
       evaluate p t = st
       evaluate p' st = r

       le:les


     ‘eval r le = eval st le’ by (
       pop_assum kall_tac >>
       qpat_x_assum ‘T’ kall_tac >>
       qpat_x_assum ‘EVERY _ _’ kall_tac >>
       rpt (pop_assum mp_tac) >>
       MAP_EVERY qid_spec_tac [‘t’, ‘p1’, ‘st’,‘les'’ ,‘tmp'’, ‘l'’,
                               ‘tmp''’, ‘l''’, ‘t'’, ‘es’] >>
       Induct
       >- (
        rw [] >>
        fs [compile_exp_def] >> rveq >>
        fs [evaluate_def] >> rveq >> fs []) >>
       rw [] >>
       rfs [] >>
       fs [OPT_MMAP_def] >> rveq >> fs [] >>
       qpat_x_assum ‘compile_exps _ _ _ _ = _ ’ mp_tac >>
       once_rewrite_tac [compile_exp_def] >>
       fs [] >>
       pairarg_tac >> fs [] >>
       pairarg_tac >> fs [] >>
       strip_tac >> fs [] >> rveq >>
       first_x_assum drule >>
       disch_then drule >>
       fs [] >>
       strip_tac >>



















 eval st le = SOME (wlab_wloc ctxt (Word c))
       evaluate (p',t) = (NONE,st)
        evaluate (p1,st) = (NONE,r)

  compile_exp ctxt tmp l h = (p',le,tmp'',l'') /\
   compile_exps ctxt tmp'' l'' es = (p1,les',tmp',l')










       ) >>
     fs [wlab_wloc_def]) >>
   fs [wlab_wloc_def] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 8 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’, ‘ws’, ‘es’] >>
   Induct
   >- (
    rw [] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [loopSemTheory.evaluate_def, wordSemTheory.the_words_def]) >>
   rpt gen_tac >>
   once_rewrite_tac [compile_exp_def] >>
   ntac 10 strip_tac >> fs [] >>
   last_x_assum mp_tac >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [loopSemTheory.evaluate_def] >>
   pairarg_tac >> fs [] >>
   cases_on ‘res’ >> fs [] >>
   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs [] >>
   fs [OPT_MMAP_def] >> rveq >>
   disch_then drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   pairarg_tac >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   disch_then (qspecl_then
               [‘l''’, ‘tmp''’, ‘les'’, ‘p1’, ‘s1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >> fs [])
  >- (
   rw [] >>
   fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   disch_then (qspec_then ‘l’ mp_tac) >>
   strip_tac >> rfs [] >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp''’, ‘l''’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_temp_ge >> fs [] >>
   strip_tac >> fs [] >>
   fs [nested_seq_def, loopSemTheory.evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rfs [] >>
   ‘eval st' le' = eval st le'’ by cheat >>
   fs [] >> rfs [] >> rveq >>
   fs [wlab_wloc_def, loopSemTheory.set_var_def,
       loopSemTheory.eval_def] >>
   ‘eval (st' with locals := insert (tmp'³' + 1) (Word w1) st'.locals)
    le'' = eval st' le''’ by cheat >>
   fs [] >> rfs [] >>
   rveq >>
   fs [lookup_insert] >>
   fs [get_var_imm_def] >>
   cases_on ‘word_cmp cmp w1 w2’ >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.set_var_def] >>



   fs [cut_res_def, cut_state_def]

‘domain l'³' ⊆
             tmp'³' + 1 INSERT tmp'³' + 2 INSERT tmp'³' + 1 INSERT
             domain st'.locals’ by cheat >>
   fs [] >>
   ‘st'.clock <> 0’ by cheat >> fs [] >>
   rveq >>
   fs [dec_clock_def] >>
   fs [lookup_inter_alt] >>
   conj_tac >> EVAL_TAC >>
   conj_tac >> fs [state_rel_def]


   , cut_state_def]















   ) >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [loopSemTheory.evaluate_def] >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def]
QED

Theorem compile_Assign:
  ^(get_goal "compile_prog _ (crepLang$Assign _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  fs [crepSemTheory.evaluate_def] >>
  fs [CaseEq "option"] >> rveq >> fs [] >>
  fs [compile_prog_def] >>
  imp_res_tac locals_rel_intro >>
  fs [] >>
  pairarg_tac >> fs [] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>




  TOP_CASE_TAC >> fs []
  >- (
   fs [lo] >>

   )


  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>




QED




Theorem foo:
  ∀s e v (t :('a, 'b) state) ctxt.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt s.locals t.locals ==>
    ?st. evaluate (compile_exp ctxt e,t) = (NONE,st) /\
    lookup (ctxt.vmax + 1) st.locals = SOME (wlab_wloc ctxt v) /\
    state_rel s st /\ mem_rel ctxt s.memory st.memory /\
    globals_rel ctxt s.globals st.globals /\
    code_rel ctxt s.code st.code /\
    locals_rel ctxt s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   fs [evaluate_def, eval_def, set_var_def] >>
   fs [wlab_wloc_def, state_rel_def] >>
   fs [locals_rel_def] >>
   rw [] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [crepSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   TOP_CASE_TAC >> fs []
   >- (
    fs [locals_rel_def] >>
    first_x_assum drule >>
    fs []) >>
   fs [evaluate_def, eval_def] >>
   imp_res_tac locals_rel_intro >>
   fs [] >> rveq >>
   fs [set_var_def, state_rel_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, CaseEq "option"] >>
   cases_on ‘v1’ >> rveq >>
   fs [compile_exp_def] >>
   imp_res_tac code_rel_intro >>
   fs [] >> rveq >>
   fs [evaluate_def, set_var_def, domain_lookup, wlab_wloc_def] >>
   fs [state_rel_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (Load e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   last_x_assum drule_all >>
   strip_tac >> fs [] >>
   fs [compile_exp_def] >>
   fs [evaluate_def] >>
   fs [eval_def, wlab_wloc_def] >>
   imp_res_tac mem_rel_intro >> fs [] >> rveq >>
   ‘st.memory = t.memory ∧ st.mdomain = t.mdomain’ by cheat >>
   fs [crepSemTheory.mem_load_def, mem_load_def, state_rel_def,set_var_def] >>
   last_x_assum (qspec_then ‘c’ mp_tac) >> fs [] >>
   strip_tac >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
   >- (
   rename [‘eval s (LoadByte e)’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   last_x_assum drule_all >>
   strip_tac >> fs [] >>
   fs [compile_exp_def] >>
   fs [evaluate_def] >>
   fs [eval_def, wlab_wloc_def] >>
   imp_res_tac mem_rel_intro >> fs [] >> rveq >>
   ‘st.memory = t.memory ∧ st.mdomain = t.mdomain ∧ st.be = t.be’ by cheat >>
   fs [state_rel_def, panSemTheory.mem_load_byte_def, CaseEq "word_lab",
       wordSemTheory.mem_load_byte_aux_def] >>
   last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
   fs [wlab_wloc_def, set_var_def] >>
   strip_tac >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   rename [‘eval s (LoadGlob gadr)’] >>
   fs [crepSemTheory.eval_def] >>
   fs [compile_exp_def] >>
   fs [evaluate_def, eval_def] >>
   imp_res_tac globals_rel_intro >>
   fs [state_rel_def, set_var_def] >>
   fs [locals_rel_def] >> rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs [])
  >- (
   pop_assum mp_tac >>
   qid_spec_tac ‘es’ >>
   Induct >> rw []
   >- (
    fs [crepSemTheory.eval_def] >>
    fs [OPT_MMAP_def] >> rveq >>
    fs [compile_exp_def, comp_assigns_def, load_exps_def] >>
    fs [loopSemTheory.evaluate_def] >>
    fs [loopSemTheory.eval_def] >>
    fs [wordSemTheory.the_words_def] >>
    fs [set_var_def, wlab_wloc_def, state_rel_def] >>
    fs [locals_rel_def] >> rw [] >>
    first_x_assum drule >> fs [] >>
    strip_tac >> fs [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >>
    fs [ctxt_max_def] >>
    first_x_assum drule >> fs []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >>
   fs [compile_exp_def, comp_assigns_def, load_exps_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   last_assum (qspec_then ‘h’ assume_tac) >>
   fs [] >>
   qpat_x_assum ‘eval s (Op op (h::es)) = _’ mp_tac >>
   once_rewrite_tac [crepSemTheory.eval_def] >>
   strip_tac >>
   fs [OPT_MMAP_def] >>
   cases_on ‘eval s h’ >> fs [] >>
   first_x_assum drule_all >>
   strip_tac >> fs [] >> rveq >> fs []  >>
   fs [CaseEq "option"] >> rveq >> fs [] >>
   last_x_assum (qspec_then ‘Word z’ mp_tac) >>
   disch_then (qspecl_then [‘s1'’, ‘ctxt with vmax := ctxt.vmax + 1’] mp_tac) >>
   impl_tac >- cheat >>
   strip_tac >> fs [] >>
   rfs [] >> cheat)



Theorem opt_mmap_eq_some:
  ∀xs f ys.
  OPT_MMAP f xs = SOME ys <=>
   MAP f xs = MAP SOME ys
Proof
  Induct >> rw [OPT_MMAP_def]
  >- metis_tac [] >>
  eq_tac >> rw [] >> fs [] >>
  cases_on ‘ys’ >> fs []
QED





   last_x_assum (qspec_then ‘h’ mp_tac) >>
   fs []





    )



   rw [] >>
   fs []



   )




  >- (
   rename [‘eval s (Cmp cmp e e')’] >>
   fs [crepSemTheory.eval_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   rw [] >>
   last_x_assum drule_all >>
   strip_tac >>
   fs [compile_exp_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘compile_exp nctxt e',_’ >>
   last_x_assum (qspecl_then [‘st’, ‘nctxt’] mp_tac) >>
   impl_tac
   >- (
    fs [Abbr ‘nctxt’] >> cheat) >>
   strip_tac >> fs [] >> rveq >>
   fs [Abbr ‘nctxt’] >>
   fs [wlab_wloc_def] >>
   ‘lookup (ctxt.vmax + 1) s1.locals = SOME (Word c)’ by cheat >>
   fs [] >>
   fs [get_var_imm_def] >>
   TOP_CASE_TAC >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.cut_res_def, loopSemTheory.set_var_def,
       cut_state_def] >>
   ‘s1.clock <> 0’ by cheat >>
   fs [dec_clock_def, bitstringTheory.v2w_def] >>




   fs [loopSemTheory.evaluate_def, loopSemTheory.cut_res_def] >>





   fs [comp_assigns_def] >>
   fs [evaluate_def] >>
   ntac 4 (pairarg_tac >> fs []) >>
   rfs [] >> rveq >> rfs [eval_def] >>
   rveq >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘evaluate (compile_exp ctxt e',nt) = (_,_)’ >>
   last_x_assum (qspecl_then [‘nt’, ‘ctxt’] mp_tac) >>
   impl_tac
   >- (
    fs [Abbr ‘nt’, state_rel_def, set_var_def] >>
    fs [locals_rel_def] >> rw [] >>
    first_x_assum drule >> fs [] >>
    strip_tac >> fs [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >>
    fs [ctxt_max_def] >>
    first_x_assum drule >> fs []) >>
   fs [] >>
   strip_tac >> fs [] >> rveq >>
   fs [Abbr ‘nt’, set_var_def] >>
   fs [lookup_insert]



    )



   , comp_assigns_def]



   last_x_assum drule_all >>




   )





   )


QED



(*

(*
 let (p, les, tmp) = compile_exps ctxt tmp [e;e'] in
   (Seq p (Seq (Assign tmp le) (Assign (tmp + 1) le'))
        (If cmp tmp (Reg (tmp + 1))
         (Assign (tmp + 1) (Const 1w)) (Assign (tmp + 1) (Const 0w)) LN)
*)


(compile_exp ctxt tmp (Op bop es) =
 let (p, les, tmp) = compile_exps ctxt tmp es in
     (p, Op bop les, tmp)

(compile_exps ctxt tmp [] = (Skip, [], tmp))
(compile_exps ctxt tmp (e::es) =
 let (p, le, tmp) = compile_exp ctxt tmp e in
 let (p1, les, tmp) = compile_exps ctxt tmp es in
     (Seq p p1, le::les, tmp)

 (Skip, [], tmp))



  (compile_exp ctxt ((Const c):'a crepLang$exp) =
   Assign (ctxt.vmax + 1) ((Const c): 'a loopLang$exp)) /\
  (compile_exp ctxt (Var vname) = Assign (ctxt.vmax + 1)
   (case FLOOKUP ctxt.vars vname of
     | SOME n => Var n
     | NONE => Var 0)) /\
  (compile_exp ctxt (Label fname) = LocValue (ctxt.vmax + 1)
   (case FLOOKUP ctxt.funcs fname of
     | SOME (n, _) => n
     | NONE => 0)) /\
  (compile_exp ctxt (Load adr) =
   Seq (compile_exp ctxt adr)
       (Assign (ctxt.vmax + 1) (Load (Var (ctxt.vmax + 1))))) /\
  (compile_exp ctxt (LoadByte adr) =
   Seq (compile_exp ctxt adr)
       (LoadByte (ctxt.vmax + 1) 0w (ctxt.vmax + 1))) /\
  (compile_exp ctxt (LoadGlob gadr) = Assign (ctxt.vmax + 1) (Lookup gadr)) /\

  (compile_exp ctxt (Op bop es) =
   Seq (comp_assigns (λc e. compile_exp c e) ctxt es)
       (Assign (ctxt.vmax + 1) (Op bop (load_exps (ctxt.vmax + 1) (LENGTH es))))) /\


  (compile_exp ctxt (Cmp cmp e e') =
   Seq (Seq (compile_exp ctxt e) (compile_exp (ctxt with vmax := ctxt.vmax + 1) e'))
        (If cmp (ctxt.vmax + 1) (Reg (ctxt.vmax + 2))
           (Assign (ctxt.vmax + 1) (Const 1w)) (Assign (ctxt.vmax + 1) (Const 0w)) LN)) /\
  (compile_exp ctxt (Shift sh e n) =
   Seq (compile_exp ctxt e)
   (Assign (ctxt.vmax + 1) (Shift sh (Var (ctxt.vmax + 1)) n)))
Termination
  cheat
End
*)


Definition comp_assigns_def:
  (comp_assigns f ctxt [] =  Skip) /\
  (comp_assigns f ctxt (e::es) =
   Seq (f ctxt e)
       (comp_assigns f (ctxt with vmax := ctxt.vmax + 1) es))
End


Definition load_exps_def:
  load_exps n m  = MAP Var (GENLIST (λx. n + x) m)
End




Definition compile_exp_def:
  (compile_exp ctxt tmp l ((Const c):'a crepLang$exp) = (Skip, Const c, tmp, l)) /\
  (compile_exp ctxt tmp l (Var v) = (Skip, Var (find_var ctxt v), tmp, l)) /\
  (compile_exp ctxt tmp l (Label f) = (LocValue tmp (find_lab ctxt f), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (Load ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in (p, Load le, tmp, l)) /\
  (compile_exp ctxt tmp l (LoadByte ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in
    (Seq (Seq p (Assign tmp le)) (LoadByte tmp 0w tmp), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (LoadGlob gadr) = (Skip, Lookup gadr, tmp, l)) /\
  (compile_exp ctxt tmp l (Op bop es) =
   let (p, les, tmp, l) = compile_exps ctxt tmp l es in
    (p, Op bop les, tmp, l)) /\
  (compile_exp ctxt tmp l (Cmp cmp e e') =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in
   let (p', le', tmp', l) = compile_exp ctxt tmp l e' in
    (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l, Var (tmp' + 1), tmp' + 3, insert (tmp' + 1) () l)) /\
  (compile_exp ctxt tmp l (Shift sh e n) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in (p, Shift sh le n, tmp, l)) /\

  (compile_exps ctxt tmp l [] = (Skip, [], tmp, l)) /\
  (compile_exps ctxt tmp l (e::es) =
    let (p, le, tmp, l) = compile_exp ctxt tmp l e in
    let (p1, les, tmp, l) = compile_exps ctxt tmp l es in
        (Seq p p1, le::les, tmp, l))
End
(*
Definition toNumSet_def:
  toNumSet [] = LN ∧
  toNumSet (n::ns) = insert n () (toNumSet ns)
End

Definition fromNumSet_def:
  fromNumSet t = MAP FST (toAList t)
End

Definition mk_new_cutset_def:
  mk_new_cutset ctxt (l:num_set) =
    insert 0 () (toNumSet (MAP (find_var ctxt) (fromNumSet l)))
End
*)





Definition compile_exp_def:
  (compile_exp ctxt tmp l ((Const c):'a crepLang$exp) = (Skip, Const c, tmp, l)) /\
  (compile_exp ctxt tmp l (Var v) = (Skip, Var (find_var ctxt v), tmp, l)) /\
  (compile_exp ctxt tmp l (Label f) = (LocValue tmp (find_lab ctxt f), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (Load ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in (p, Load le, tmp, l)) /\
  (compile_exp ctxt tmp l (LoadByte ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in
    (Seq (Seq p (Assign tmp le)) (LoadByte tmp 0w tmp), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (LoadGlob gadr) = (Skip, Lookup gadr, tmp, l)) /\
  (compile_exp ctxt tmp l (Op bop es) =
   let (p, les, tmp, l) = compile_exps ctxt tmp l es in
    (p, Op bop les, tmp, l)) /\
  (compile_exp ctxt tmp l (Cmp cmp e e') =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in
   let (p', le', tmp', l) = compile_exp ctxt tmp l e' in
    (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l, Var (tmp' + 1), tmp' + 3, insert (tmp' + 1) () l)) /\
  (compile_exp ctxt tmp l (Shift sh e n) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in (p, Shift sh le n, tmp, l)) /\

  (compile_exps ctxt tmp l cps = (* to generate ind thm *)
   case cps of
   | [] => (Skip, [], tmp, l)
   | e::es =>
     let (p, le, tmp, l) = compile_exp ctxt tmp l e in
      let (p1, les, tmp, l) = compile_exps ctxt tmp l es in
      (Seq p p1, le::les, tmp, l))
Termination
  cheat
End

 ‘es <> [] ==> MAP (EL 0) (MAP2 evals (comp_sts t ct tmp l es les) les) =
    MAP (λe. eval r e) les’ by cheat >>
   qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
   qpat_x_assum ‘EVERY _ _’ kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
   Induct
   >- rw [] >>
   rw [] >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   fs [OPT_MMAP_def] >> rveq >>

   fs [] >>


Theorem bar:
  !es ct tmp l.
   ?les tmp' l'.
   compile_exps ct tmp l es = (nested_seq (prog_comp ct tmp l es),les,tmp', l')

    (le::les)  eval _ le = eval _ le


Proof
  Induct >> rw []
  >- fs [compile_exp_def, nested_seq_def, prog_comp_def] >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  fs [] >>
  fs [prog_comp_def] >>
  fs [nested_seq_def] >>
  last_x_assum (qspecl_then [‘ct’, ‘tmp'’, ‘l'’] mp_tac) >>
  fs []
QED




Definition temps_comp_def:
  (temp_comp ct tmp l [] = [tmp]) /\
  (temp_comp ct tmp l (e::es) = tmp ::
   let (p, le, tmp, l) = compile_exp ct tmp l e in
     temp_comp ct tmp l es)
End


Definition live_comp_def:
  (live_comp ct tmp l [] = [l]) /\
  (live_comp ct tmp l (e::es) = l ::
   let (p, le, tmp, l) = compile_exp ct tmp l e in
     live_comp ct tmp l es)
End




Definition eval_sts_def:
  (eval_sts s [] = []) /\
  (eval_sts s (p::ps) =
   let (r,t) = evaluate (p,s) in
     t :: eval_sts t ps)
End

Definition arrange_sts_def:
  (arrange_sts sts [] = []) /\
  (arrange_sts sts (le::les) =
   TAKE (LENGTH (le::les)) sts ::
    arrange_sts (DROP 1 sts) les)
End


Definition comp_sts_def:
  comp_sts t ct tmp l es les =
    arrange_sts (eval_sts t (prog_comp ct tmp l es)) les
End


Definition evals_def:
  evals sts e = MAP (λst. eval st e) sts
End

(*
Definition id_list_mem_def:
  evals sts e = MAP (λst. eval st e) sts
End
*)


(*
Definition prog_if_def:
  prog_if cmp p q e e' n m l =
  nested_seq [
    p; q;
    Assign n e; Assign m e';
    If cmp n (Reg m)
    (Assign n (Const 1w)) (Assign n (Const 0w)) (insert n () l)]
End

Definition compile_exp_def:
  (compile_exp ctxt tmp l ((Const c):'a crepLang$exp) = (Skip, Const c, tmp, l)) /\
  (compile_exp ctxt tmp l (Var v) = (Skip, Var (find_var ctxt v), tmp, l)) /\
  (compile_exp ctxt tmp l (Label f) = (LocValue tmp (find_lab ctxt f), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (Load ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in (p, Load le, tmp, l)) /\
  (compile_exp ctxt tmp l (LoadByte ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in
    (Seq (Seq p (Assign tmp le)) (LoadByte tmp 0w tmp), Var tmp, tmp + 1, l)) /\
  (compile_exp ctxt tmp l (LoadGlob gadr) = (Skip, Lookup gadr, tmp, l)) /\
  (compile_exp ctxt tmp l (Op bop es) =
   let (p, les, tmp, l) = compile_exps ctxt tmp l es in
    (nested_seq p, Op bop les, tmp, l)) /\
  (compile_exp ctxt tmp l (Cmp cmp e e') =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in
   let (p', le', tmp', l) = compile_exp ctxt tmp l e' in
    (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l, Var (tmp' + 1), tmp' + 3, insert (tmp' + 1) () l)) /\
  (compile_exp ctxt tmp l (Shift sh e n) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in (p, Shift sh le n, tmp, l)) /\

  (compile_exps ctxt tmp l cps = (* to generate ind thm *)
   case cps of
   | [] => ([Skip], [], tmp, l)
   | e::es =>
     let (p, le, tmp, l) = compile_exp ctxt tmp l e in
      let (p1, les, tmp, l) = compile_exps ctxt tmp l es in
      (p :: p1, le::les, tmp, l))
Termination
  cheat
End


Definition compile_prog_def:
  (compile_prog _ l (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog, l)) /\
  (compile_prog ctxt l (Assign v e) =
   case FLOOKUP ctxt.vars v of
    | SOME n =>
      let (p,le,tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in (Seq p (Assign n le), l)
    | NONE => (Skip,l))
End

 *) *)
val _ = export_theory();
