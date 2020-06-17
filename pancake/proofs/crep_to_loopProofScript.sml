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
  (compile_exp ctxt tmp l (Label f) = ([LocValue tmp (find_lab ctxt f)],
                                       Var tmp, tmp + 1, insert tmp () l)) /\
  (compile_exp ctxt tmp l (Load ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in (p, Load le, tmp, l)) /\
  (compile_exp ctxt tmp l (LoadByte ad) =
   let (p, le, tmp, l) = compile_exp ctxt tmp l ad in
    (p ++ [Assign tmp le; LoadByte tmp tmp], Var tmp, tmp + 1, insert tmp () l)) /\
  (compile_exp ctxt tmp l (LoadGlob gadr) = ([], Lookup gadr, tmp, l)) /\
  (compile_exp ctxt tmp l (Op bop es) =
   let (p, les, tmp, l) = compile_exps ctxt tmp l es in
   (p, Op bop les, tmp, l)) /\
  (compile_exp ctxt tmp l (Cmp cmp e e') =
   let (p, le, tmp, l) = compile_exp ctxt tmp l e in
   let (p', le', tmp', l) = compile_exp ctxt tmp l e' in
     (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l, Var (tmp' + 1), tmp' + 3,
      list_insert [tmp' + 1; tmp' + 2] l)) /\
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

Definition cut_sets_def:
  (cut_sets l Skip = l) ∧
  (cut_sets l (LocValue n m) = insert n () l) ∧
  (cut_sets l (Assign n e) = insert n () l) ∧
  (cut_sets l (LoadByte n m) = insert m () l) ∧
  (cut_sets l (Seq p q) = cut_sets (cut_sets l p) q) ∧
  (cut_sets l (If _ _ _ p q nl) = nl)
End

Definition comp_syntax_ok_def:
  comp_syntax_ok l p <=>
    p = Skip ∨
    ?n m. p = LocValue n m ∨
    ?n e. p = Assign n e ∨
    ?n m. p = LoadByte n m ∨
    ?c n m v v'. p = If c n (Reg m) (Assign n v) (Assign n v') (list_insert [n; m] l) ∨
    ?q r. p = Seq q r ∧ comp_syntax_ok l q ∧ comp_syntax_ok (cut_sets l q) r
Termination
 cheat
End

Definition compile_prog_def:
  (compile_prog _ _ (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog)) /\
  (compile_prog _ _ Break = Break) /\
  (compile_prog _ _ Continue = Continue) /\
  (compile_prog _ _ Tick = Tick) /\
  (compile_prog ctxt l (Return e) =
    let (p, le, ntmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e in
      nested_seq (p ++ [Assign (ntmp + 1) le; Return (ntmp + 1)])) /\
  (compile_prog ctxt l (Raise eid) =
    Seq (Assign (ctxt.vmax + 1) (Const eid)) (Raise (ctxt.vmax + 1))) /\
  (compile_prog ctxt l (Store dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++ [Assign (tmp + 1) le'; Store le (tmp + 1)])) /\
  (compile_prog ctxt l (StoreByte dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++
                     [Assign (tmp + 1) le; Assign (tmp + 2) le';
                      StoreByte (tmp + 1) (tmp + 2)])) /\
  (compile_prog ctxt l (StoreGlob adr e) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in
        nested_seq (p ++ [SetGlobal adr le])) /\
  (compile_prog ctxt l (Seq p q) =
    Seq (compile_prog ctxt l p) (compile_prog ctxt l q)) /\
  (compile_prog ctxt l (Assign v e) =
    case FLOOKUP ctxt.vars v of
     | SOME n =>
       let (p,le,tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in
        nested_seq (p ++ [Assign n le])
     | NONE => Skip) /\
  (compile_prog ctxt l (Dec v e prog) =
    let (p,le,tmp,nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
         nctxt = ctxt with <|vars := ctxt.vars |+ (v,tmp);
                             vmax := tmp|>;
         fl = insert tmp () l;
         lp = compile_prog nctxt fl prog in
     Seq (nested_seq p) (Seq (Assign tmp le) lp)) /\
  (compile_prog ctxt l (If e p q) =
    let (np, le, tmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
        lp = compile_prog ctxt l p;
        lq = compile_prog ctxt l q in
    nested_seq (np ++ [Assign tmp le;
                       If NotEqual tmp (Imm 0w) lp lq l])) /\
  (compile_prog ctxt l (While e p) = Skip) /\
  (compile_prog ctxt l (Call ct n es) = Skip) /\
  (compile_prog ctxt l (ExtCall f ptr1 len1 ptr2 len2) =
    case (FLOOKUP ctxt.vars ptr1, FLOOKUP ctxt.vars len1,
          FLOOKUP ctxt.vars ptr2, FLOOKUP ctxt.vars len2) of
     | (SOME pc, SOME lc, SOME pc', SOME lc') =>
         FFI (explode f) pc lc pc' lc' l
     | _ => Skip)
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
  !ad. wlab_wloc ctxt (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
End

Definition globals_rel_def:
  globals_rel ctxt sglobals tglobals <=>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc ctxt v) /\
     !f. v = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
End

Definition distinct_funcs_def:
  distinct_funcs fm <=>
    !x y n m rm rm'. FLOOKUP fm x = SOME (n, rm) /\
       FLOOKUP fm y = SOME (m, rm') /\ n = m ==> x = y
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
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc args l. FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, compile_prog nctxt l prog)
End

Definition ctxt_max_def:
  ctxt_max (n:num) fm <=>
   !v m. FLOOKUP fm v = SOME m ==> m <= n
End

Definition distinct_vars_def:
  distinct_vars fm <=>
    (!x y n m. FLOOKUP fm x = SOME n /\
               FLOOKUP fm y = SOME m /\ n = m ==> x = y)
End

Definition locals_rel_def:
  locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals <=>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc ctxt v) /\
    !f. v = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
End

(*
Definition locals_preserved_def:
  locals_preserved ctxt l l1 l2 =
   !n. n IN domain l /\ n NOTIN (FRANGE ctxt.vars) /\
       n <= ctxt.vmax ==>
    !v. lookup n l1 = SOME v ==> lookup n l2 = SOME v
End
*)
val goal =
  ``λ(prog, s). ∀res s1 t ctxt l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ mem_rel ctxt s.memory t.memory ∧
      globals_rel ctxt s.globals t.globals ∧
      code_rel ctxt s.code t.code ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃ck res1 t1. evaluate (compile_prog ctxt l prog,
                             t with clock := t.clock + ck) = (res1,t1) /\
      state_rel s1 t1 ∧ mem_rel ctxt s1.memory t1.memory ∧
      globals_rel ctxt s1.globals t1.globals ∧
      code_rel ctxt s1.code t1.code ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt l s1.locals t1.locals (* /\
                 locals_preserved l t.locals t1.locals *)
       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt l s1.locals t1.locals (* /\
                       locals_preserved l t.locals t1.locals *)
       | SOME Continue => res1 = SOME Continue /\
                       locals_rel ctxt l s1.locals t1.locals (* /\
                       locals_preserved l t.locals t1.locals *)
       | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt v))
       | SOME (Exception eid) => res1 = SOME (Exception (Word eid))
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | SOME Error => F``

local
  val ind_thm = crepSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_prog_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

(* theorems start from here *)

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
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc ctxt v) /\
    !f. v = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
Proof
  rw [locals_rel_def]
QED

Theorem code_rel_intro:
  code_rel ctxt s_code t_code ==>
    distinct_funcs ctxt.funcs /\
    ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc args l. FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, compile_prog nctxt l prog)
Proof
  rw [code_rel_def]
QED

Theorem mem_rel_intro:
  mem_rel ctxt smem tmem ==>
   !ad. wlab_wloc ctxt (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
Proof
  rw [mem_rel_def] >>
  metis_tac []
QED

Theorem globals_rel_intro:
  globals_rel ctxt sglobals tglobals ==>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc ctxt v) /\
     !f. v = Label f ==>
      ?n args. FLOOKUP ctxt.funcs f = SOME (n, args)
Proof
  rw [globals_rel_def] >> metis_tac []
QED

Theorem locals_rel_cut_sets_flookup_locals:
  locals_rel ctxt l (s_locals:num |-> 'a word_lab) t_locals /\ n ∈ domain l ==>
  ?x. lookup n t_locals = SOME x
Proof
  rw [locals_rel_def] >>
  fs [domain_lookup] >> cheat
QED

Triviality state_rel_clock_add_zero:
  !s t. state_rel s t ==>
   ?ck. state_rel s (t with clock := ck + t.clock)
Proof
  rw [] >>
  qexists_tac ‘0’ >>
  fs [state_rel_def, state_component_equality]
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

Theorem comp_syn_ok_basic_cases:
  (!l. comp_syntax_ok l Skip) /\ (!l n m. comp_syntax_ok l (LocValue n m)) /\
  (!l n e. comp_syntax_ok l (Assign n e)) /\  (!l n m. comp_syntax_ok l (LoadByte n m)) /\
  (!l c n m v v'. comp_syntax_ok l (If c n (Reg m) (Assign n v) (Assign n v') (list_insert [n; m] l)))
Proof
  rw [] >>
  ntac 3 (fs [Once comp_syntax_ok_def])
QED


Theorem comp_syn_ok_seq:
  !l p q. comp_syntax_ok l (Seq p q) ==>
   comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def]
QED


Theorem comp_syn_ok_if:
  comp_syntax_ok l (If cmp n ri p q ns) ==>
   ?v v' m. ri = Reg m /\ p = Assign n v /\ q = Assign n v' /\ ns = list_insert [n; m] l
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def]
QED


Theorem comp_syn_ok_seq2:
  !l p q. comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q ==>
   comp_syntax_ok l (Seq p q)
Proof
  rw [] >>
  once_rewrite_tac [comp_syntax_ok_def] >>
  fs []
QED


Theorem comp_syn_ok_nested_seq:
  !p q l. comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) ==>
   comp_syntax_ok l (nested_seq (p ++ q))
Proof
  Induct >> rw [] >>
  fs [nested_seq_def] >>
  fs [cut_sets_def] >>
  drule comp_syn_ok_seq >>
  strip_tac >> res_tac >> fs [] >>
  metis_tac [comp_syn_ok_seq2]
QED

Theorem comp_syn_ok_nested_seq2:
  !p q l. comp_syntax_ok l (nested_seq (p ++ q)) ==>
   comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def] >>
  drule comp_syn_ok_seq >> strip_tac >> fs [] >>
  metis_tac [comp_syn_ok_seq2]
QED


Theorem comp_syn_ok_cut_sets_nested_seq:
  !p q l. comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) ==>
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


Theorem comp_syn_ok_cut_sets_nested_seq2:
  !p q l. comp_syntax_ok l (nested_seq (p ++ q)) ==>
   cut_sets l (nested_seq (p ++ q)) =
   cut_sets (cut_sets l (nested_seq p)) (nested_seq q)
Proof
 metis_tac [comp_syn_ok_nested_seq2, comp_syn_ok_cut_sets_nested_seq]
QED

Theorem cut_sets_union_accumulate:
  !p l. comp_syntax_ok l p ==>
   ?(l' :sptree$num_set). cut_sets l p = union l l'
Proof
  Induct >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def] >> NO_TAC) >>
  fs [cut_sets_def] >>
  TRY (qexists_tac ‘LN’ >> fs [] >> NO_TAC) >>
  TRY (
  rename [‘insert vn () l’] >>
  qexists_tac ‘insert vn () LN’ >>
  fs [Once insert_union, union_num_set_sym] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘union l l'’ mp_tac) >>
   fs [] >> strip_tac >>
   qexists_tac ‘union l' l''’ >>
   fs [] >> metis_tac [union_assoc]) >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >>
  qexists_tac ‘insert m () (insert n () LN)’ >>
  fs [list_insert_def] >>
  metis_tac [union_insert_LN, insert_union, union_num_set_sym, union_assoc]
QED


Theorem cut_sets_union_domain_subset:
  !p l. comp_syntax_ok l p ==>
    domain l ⊆ domain (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >> fs [] >>
  fs [domain_union]
QED

Theorem cut_sets_union_domain_union:
  !p l. comp_syntax_ok l p ==>
   ?(l' :sptree$num_set). domain (cut_sets l p) = domain l ∪ domain l'
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >> fs [] >>
  qexists_tac ‘l'’ >>
  fs [domain_union]
QED

Theorem comp_syn_impl_cut_sets_subspt:
  !p l. comp_syntax_ok l p ==>
  subspt l (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >>
  fs [subspt_union]
QED

Theorem comp_syn_cut_sets_mem_domain:
  !p l n .
   comp_syntax_ok l p /\ n ∈ domain l ==>
    n ∈ domain (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_domain_union >>
  strip_tac >> fs []
QED

Theorem compile_exp_out_rel_cases:
  (!ct tmp l (e:'a crepLang$exp) p le ntmp nl.
    compile_exp ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p)) /\
  (!ct tmp l (e:'a crepLang$exp list) p le ntmp nl.
    compile_exps ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p))
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  fs [Once compile_exp_def] >> rveq >>
  TRY (pairarg_tac >> fs [] >> rveq >> NO_TAC) >>
  fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def] >> NO_TAC)
  >- (
   rename [‘compile_exp _ _ _ (Label f)’] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, cut_sets_def] >>
   match_mp_tac comp_syn_ok_seq2 >>
   fs [comp_syn_ok_basic_cases])
  >- (
   rename [‘compile_exp _ _ _ (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   conj_asm1_tac
   >- (
    fs [compile_exp_def] >>
    pairarg_tac >> fs [] >> rveq >> fs [] >>
    match_mp_tac comp_syn_ok_nested_seq >>
    fs [] >>
    fs [nested_seq_def] >>
    rpt (
    match_mp_tac comp_syn_ok_seq2 >>
    fs [comp_syn_ok_basic_cases])) >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   res_tac >> fs [] >>
   imp_res_tac comp_syn_ok_nested_seq2 >>
   last_x_assum assume_tac >>
   qmatch_goalsub_abbrev_tac ‘p' ++ np’ >>
   drule comp_syn_ok_cut_sets_nested_seq >>
   disch_then (qspecl_then [‘np’] assume_tac) >>
   fs [Abbr ‘np’] >> pop_assum kall_tac >>
   fs [nested_seq_def, cut_sets_def, Once insert_insert])
  >- (
   rename [‘compile_exp _ _ _ (Op _ _)’] >>
   fs [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   cases_on ‘e’
   >- fs [compile_exp_def] >>
   fs [] >>
   fs [Once compile_exp_def])
  >- (
   rename [‘compile_exp _ _ _ (Cmp _ _ _)’] >>
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
    fs [list_insert_def, nested_seq_def, cut_sets_def] >>
    rpt (match_mp_tac comp_syn_ok_seq2 >>
         fs [comp_syn_ok_basic_cases]) >>
    fs [cut_sets_def] >>
    rw [Once comp_syntax_ok_def, list_insert_def] >>
    drule_all comp_syn_ok_cut_sets_nested_seq >>
    strip_tac >> fs [] >>
    pop_assum kall_tac >>
    qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
    match_mp_tac EQ_SYM >>
    ‘insert t1 () (insert t2 () (insert t1 () cc)) = insert t2 () (insert t1 () cc)’ by (
      ‘insert t2 () (insert t1 () cc) = insert t1 () (insert t2 () cc)’
        by (fs [Abbr ‘t1’, Abbr ‘t2’] >> match_mp_tac insert_swap >> fs []) >>
      fs [Abbr ‘t1’, Abbr ‘t2’] >> fs [Once insert_insert]) >>
    fs [] >> pop_assum kall_tac >>
    fs [Once insert_insert]) >>
   conj_tac >- (res_tac >> fs []) >>
   res_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘list_insert _ ll’ >>
   fs [prog_if_def] >>
   qmatch_goalsub_abbrev_tac ‘p' ++ p'' ++ np’ >>
   ‘comp_syntax_ok l (nested_seq (p' ++ p''))’ by (
     match_mp_tac comp_syn_ok_nested_seq >>
     fs []) >>
   ‘comp_syntax_ok (cut_sets l (nested_seq (p' ++ p''))) (nested_seq np)’ by (
     fs [Abbr ‘np’, nested_seq_def] >>
     ntac 3 (rw [Once comp_syntax_ok_def]) >>
     rw [Once comp_syntax_ok_def, cut_sets_def, Abbr ‘l''’, list_insert_def] >>
     drule comp_syn_ok_cut_sets_nested_seq2 >>
     fs [] >> strip_tac >> pop_assum kall_tac >>
     qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
     match_mp_tac EQ_SYM >>
     ‘insert t1 () (insert t2 () (insert t1 () cc)) = insert t2 () (insert t1 () cc)’ by (
       ‘insert t2 () (insert t1 () cc) = insert t1 () (insert t2 () cc)’
         by (fs [Abbr ‘t1’, Abbr ‘t2’] >> match_mp_tac insert_swap >> fs []) >>
       fs [Abbr ‘t1’, Abbr ‘t2’] >> fs [Once insert_insert]) >>
     fs [] >> pop_assum kall_tac >>
     fs [Once insert_insert]) >>
   qpat_x_assum ‘comp_syntax_ok l (nested_seq (p' ++ p''))’ assume_tac >>
   drule comp_syn_ok_cut_sets_nested_seq >>
   disch_then (qspec_then ‘np’ mp_tac) >>
   fs [] >>
   strip_tac >> pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def, cut_sets_def]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   fs [nested_seq_def, Once comp_syntax_ok_def, every_prog_def, cut_sets_def]) >>
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
  drule comp_syn_ok_cut_sets_nested_seq >>
  disch_then (qspecl_then [‘p1’] mp_tac) >>
  fs []
QED

val compile_exp_out_rel = compile_exp_out_rel_cases |> CONJUNCT1
val compile_exps_out_rel = compile_exp_out_rel_cases |> CONJUNCT2


Theorem comp_syn_ok_upd_local_clock:
  !p s res t l.
    evaluate (p,s) = (res,t) /\
    comp_syntax_ok l p ==>
     t = s with <|locals := t.locals; clock := t.clock|>
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  TRY (
  fs [evaluate_def] >> rveq >>
  TRY every_case_tac >> fs [set_var_def, state_component_equality] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   FULL_CASE_TAC >> fs []  >> rveq >>
   res_tac >> fs [state_component_equality]) >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [state_component_equality, evaluate_def, comp_syn_ok_basic_cases] >>
  every_case_tac >>
  fs [cut_res_def, cut_state_def, dec_clock_def, set_var_def] >>
  every_case_tac >> fs [] >> rveq >> fs []
QED


Theorem assigned_vars_nested_seq_split:
  !p q l.
   comp_syntax_ok l (nested_seq p) /\ comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) ==>
    assigned_vars (nested_seq (p ++ q)) =
    assigned_vars (nested_seq p) ++ assigned_vars (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, assigned_vars_def] >>
  drule comp_syn_ok_seq >> fs [] >>
  strip_tac >>
  fs [cut_sets_def] >> res_tac >> fs []
QED

Theorem assigned_vars_seq_split:
  !q p l .
   comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q ==>
    assigned_vars (Seq p q) = assigned_vars p ++ assigned_vars q
Proof
  rw [] >> fs [assigned_vars_def, cut_sets_def]
QED


Theorem comp_exp_assigned_vars_tmp_bound_cases:
  (!ct tmp l (e :α crepLang$exp) p le ntmp nl n.
    compile_exp ct tmp l e = (p,le,ntmp,nl) /\ MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp) /\
  (!ct tmp l (e :α crepLang$exp list) p le ntmp nl n.
    compile_exps ct tmp l e = (p,le,ntmp,nl) /\ MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp)
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  fs [Once compile_exp_def] >> TRY (pairarg_tac >> fs []) >>
  rveq >> fs [nested_seq_def, assigned_vars_def] >> NO_TAC)
  >- (
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   drule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘nested_seq (_ ++ q)’ >>
   ‘comp_syntax_ok (cut_sets l (nested_seq p')) (nested_seq q)’ by (
     fs [Abbr ‘q’, nested_seq_def] >>
     rpt (match_mp_tac comp_syn_ok_seq2 >> fs [comp_syn_ok_basic_cases])) >>
   qpat_x_assum ‘comp_syntax_ok _ (nested_seq p')’ assume_tac >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac
   >- (res_tac >> fs []) >>
   fs [Abbr ‘q’, nested_seq_def, assigned_vars_def])
  >- (
   once_rewrite_tac [compile_exp_def] >> fs [] >> strip_tac >>
   pairarg_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [prog_if_def] >>
   ‘tmp <= tmp' /\ tmp' <= tmp''’ by metis_tac [compile_exp_out_rel_cases] >>
   dxrule compile_exp_out_rel >>
   dxrule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘nested_seq (p' ++ p'' ++ q)’ >>
   strip_tac >> fs [] >>
   ‘comp_syntax_ok l'' (nested_seq q)’ by (
     fs [Abbr ‘q’, nested_seq_def, list_insert_def, cut_sets_def] >>
     rpt (match_mp_tac comp_syn_ok_seq2 >> fs [comp_syn_ok_basic_cases]) >>
     rw [Once comp_syntax_ok_def] >>
     fs [list_insert_def, cut_sets_def] >>
     qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
     match_mp_tac EQ_SYM >>
     ‘insert t1 () (insert t2 () (insert t1 () cc)) = insert t2 () (insert t1 () cc)’ by (
       ‘insert t2 () (insert t1 () cc) = insert t1 () (insert t2 () cc)’
         by (fs [Abbr ‘t1’, Abbr ‘t2’] >> match_mp_tac insert_swap >> fs []) >>
       fs [Abbr ‘t1’, Abbr ‘t2’] >> fs [Once insert_insert]) >>
     fs [] >> pop_assum kall_tac >>
     fs [Once insert_insert]) >>
   rveq >> fs [] >>
   qpat_x_assum ‘comp_syntax_ok _ (nested_seq p')’ assume_tac >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘p'' ++ q’ mp_tac) >>
   fs [] >>
   impl_tac
   >- imp_res_tac comp_syn_ok_nested_seq >>
   strip_tac >> fs []
   >- (res_tac >> fs []) >>
   ntac 2 (pop_assum kall_tac) >>
   pop_assum mp_tac >>
   drule assigned_vars_nested_seq_split >>
   disch_then (qspec_then ‘q’ mp_tac) >>
   strip_tac >> strip_tac >> fs []
   >- (res_tac >> fs []) >>
   fs [Abbr ‘q’, nested_seq_def] >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   drule assigned_vars_seq_split >>
   disch_then (qspec_then ‘Assign (tmp'' + 1) le'’ mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   pop_assum kall_tac >>
   fs [assigned_vars_def]) >>
  rpt gen_tac >> strip_tac >>
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
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  rename [‘Op bop es’] >>
  rpt gen_tac >>
  strip_tac >>
  qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  strip_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [locals_touched_def, crepLangTheory.var_cexp_def, ETA_AX]) >>
  TRY (
  rename [‘compile_exps’] >>
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
  ‘tmp <= tmp'' /\ tmp'' <= tmp' /\ l'' =  cut_sets l (nested_seq p') /\ l' = cut_sets l'' (nested_seq p1)’ by
    metis_tac [compile_exp_out_rel_cases] >>
  fs [MAP]
  >- (
   res_tac >> fs [subspt_domain] >>
   drule compile_exps_out_rel >>
   strip_tac >>
   drule cut_sets_union_domain_union >>
   strip_tac >> fs []) >>
  last_x_assum match_mp_tac >>
  fs [] >>
  rw [] >>
  res_tac >> fs [subspt_domain] >>
  drule compile_exp_out_rel >>
  strip_tac >>
  drule cut_sets_union_domain_union >>
  strip_tac >> fs [] >> NO_TAC) >>
  fs [compile_exp_def] >>
  TRY (pairarg_tac >> fs []) >> rveq >>
  TRY (pairarg_tac >> fs []) >> rveq >>
  fs [locals_touched_def, find_var_def, crepLangTheory.var_cexp_def,
      ctxt_max_def, list_insert_def] >>
  rfs [] >> rveq >> res_tac >> fs []
QED

val compile_exp_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT1
val compile_exps_le_tmp_domain_cases = compile_exp_le_tmp_domain_cases |> CONJUNCT2


Theorem comp_syn_ok_lookup_locals_eq:
  !p s res t l n.
   evaluate (p,s) = (res,t) /\ res <> SOME TimeOut /\
   comp_syntax_ok l p /\ n ∈ domain l /\
    ~MEM n (assigned_vars p) ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  TRY (
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [set_var_def, assigned_vars_def, lookup_insert] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def, assigned_vars_def] >>
   pairarg_tac >> fs [AllCaseEqs ()] >> rveq >> fs []
   >- (
    qpat_x_assum ‘evaluate (_,s1) = _’ assume_tac  >>
    drule evaluate_clock >> fs [] >>
    strip_tac >> fs [] >>
    dxrule comp_syn_ok_seq >>
    strip_tac >>
    first_x_assum drule >>
    disch_then (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    strip_tac >>
    first_x_assum drule >>
    disch_then (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    impl_tac
    >- (
     qpat_x_assum ‘comp_syntax_ok l c1’ assume_tac >>
     drule cut_sets_union_domain_union >>
     strip_tac >> fs []) >>
    fs []) >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   res_tac >> fs []) >>
  drule evaluate_clock >> fs [] >>
  strip_tac >> fs [] >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >> fs [] >>
  fs [evaluate_def, assigned_vars_def] >>
  fs [AllCaseEqs()]  >> rveq >> fs [domain_inter] >>
  cases_on ‘word_cmp cmp x y’ >> fs [] >>
  fs [evaluate_def, list_insert_def, AllCaseEqs()] >>
  FULL_CASE_TAC >> fs [cut_res_def, set_var_def, dec_clock_def, cut_state_def] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  every_case_tac >> rfs [] >> rveq >> fs [] >>
  fs [state_component_equality, lookup_inter, lookup_insert] >>
  every_case_tac >> rfs [domain_lookup]
QED

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  qsuff_tac ‘the_words (MAP (λa. eval (t with clock := ck) a) wexps) =
             the_words (MAP (λa. eval t a) wexps)’ >>
  fs [] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘wexps’ >>
  Induct >> rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [wordSemTheory.the_words_def]
QED

(* should be trivial, but record updates are annoying *)

Theorem eval_upd_locals_clock_eq:
  !t e l ck. eval (t with <|locals := l; clock := ck|>) e =  eval (t with locals := l) e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  qsuff_tac ‘the_words (MAP (λa. eval (t with <|locals := l; clock := ck|>) a) wexps) =
             the_words (MAP (λa. eval (t with locals := l) a) wexps)’ >>
  fs [] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘wexps’ >>
  Induct >> rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [wordSemTheory.the_words_def]
QED

Theorem evaluate_add_clock_eq:
  !p t res st ck.
   evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
    evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once evaluate_def] >> NO_TAC) >>
  TRY (
  rename [‘Seq’] >>
  fs [evaluate_def] >> pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [AllCaseEqs ()] >> rveq >> fs [] >>
  first_x_assum (qspec_then ‘ck’ mp_tac) >>
  fs []) >>
  TRY (
  rename [‘If’] >>
  fs [evaluate_def, AllCaseEqs ()] >>
  rveq >> cases_on ‘ri’ >> fs [get_var_imm_def] >>
  TOP_CASE_TAC >> cases_on ‘evaluate (c1,s)’ >> cases_on ‘evaluate (c2,s)’ >>
  fs [cut_res_def, cut_state_def, AllCaseEqs (), dec_clock_def] >>
  rveq >> fs []) >>
  TRY (
  rename [‘FFI’] >>
  fs [evaluate_def, AllCaseEqs (), cut_state_def, call_env_def] >>
  rveq >> fs []) >>
  TRY (
  rename [‘Loop’] >>
  fs [Once evaluate_def,  AllCaseEqs ()] >> rveq >> fs [] >>
  cheat) >>
  TRY (rename [‘Call’] >> cheat) >>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ,
      set_var_def, mem_store_def, set_globals_def,
      call_env_def, dec_clock_def] >> rveq >>
  fs [state_component_equality]
QED

Triviality evaluate_comb_seq:
  !p s t q r.
    evaluate (p,s) = (NONE, t) /\ evaluate (q,t) = (NONE,r) ==>
    evaluate (Seq p q,s) = (NONE,r)
Proof
  fs [evaluate_def]
QED

Theorem evaluate_nested_seq_comb_seq:
  !p q t.
   evaluate (Seq (nested_seq p) (nested_seq q), t) =
   evaluate (nested_seq (p ++ q), t)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  cases_on ‘res' = NONE’ >> fs [] >> rveq >> fs [] >>
  first_x_assum (qspecl_then [‘q’,‘s1'’] mp_tac) >>
  fs []
QED


Theorem nested_seq_pure_evaluation:
  !p q t r st l m e v ck ck'.
  evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) /\
  evaluate (nested_seq q,st with clock := ck' + st.clock) = (NONE,r) /\
  comp_syntax_ok l (nested_seq p) /\
  comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) /\
  (!n. MEM n (assigned_vars (nested_seq p)) ==> n < m) /\
  (!n. MEM n (assigned_vars (nested_seq q)) ==> m <= n) /\
  (!n. MEM n (locals_touched e) ==> n < m /\ n ∈ domain (cut_sets l (nested_seq p))) /\
   eval st e = SOME v ==>
    eval r e = SOME v
Proof
  rw [] >>
  drule_all comp_syn_ok_upd_local_clock >>
  fs [] >> strip_tac >>
  ‘st.globals = r.globals /\ st.memory = r.memory /\
   st.mdomain = r.mdomain’ by fs [state_component_equality] >>
  drule locals_touched_eq_eval_eq >> fs [] >>
  disch_then (qspec_then ‘e’ mp_tac) >> fs [] >>
  impl_tac
  >- (
   rw []  >>
   drule comp_syn_ok_lookup_locals_eq >>
   disch_then (qspecl_then [‘cut_sets l (nested_seq p)’, ‘n’] mp_tac) >>
   impl_tac
   >- (
    fs [] >>
    CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >> fs []) >> fs []
QED


Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) ctxt tmp l p le ntmp nl.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exp ctxt tmp l e = (p,le, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt nl s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  rename [‘eval s (Op op es)’] >>
  rw [] >>
  fs [Once compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
  fs [loopSemTheory.eval_def, wlab_wloc_def] >>
  qsuff_tac ‘∃ck st.
    evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) ∧
    the_words (MAP (λa. eval st a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws)) /\
    state_rel s st ∧ mem_rel ctxt s.memory st.memory ∧
    globals_rel ctxt s.globals st.globals ∧
    code_rel ctxt s.code st.code ∧ locals_rel ctxt l' s.locals st.locals’
  >- (
   strip_tac >>
   qexists_tac ‘ck’ >>
   fs [wlab_wloc_def]) >>
  qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
  Induct
  >- (
   rw [] >>
   fs [OPT_MMAP_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def,
       wordSemTheory.the_words_def, state_rel_clock_add_zero]) >>
  rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘compile_exps _ _ _ (h::_) = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >> pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> rveq >>
  fs [OPT_MMAP_def] >> rveq >>
  last_x_assum (qspec_then ‘h’ mp_tac) >>
  fs [] >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ h = (p,le,itmp,il)’ >>
  qmatch_asmsub_rename_tac ‘compile_exps _ _ _ _ = (fp,les,ntmp,nl)’ >>
  last_x_assum (qspecl_then
                [‘t'’, ‘il’, ‘itmp’, ‘les’, ‘fp’, ‘st’] mp_tac) >>
  fs [] >>
  imp_res_tac compile_exp_out_rel >>
  fs [] >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq p, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  qexists_tac ‘ck + ck'’ >>
  qexists_tac ‘st'’ >>
  fs [] >>
  cases_on ‘h'’ >> fs [] >>
  fs [wordSemTheory.the_words_def] >>
  ‘eval st' le = eval st le’ suffices_by fs [wlab_wloc_def] >>
  imp_res_tac compile_exps_out_rel >>
  qpat_x_assum ‘evaluate (nested_seq fp, _) = _’ assume_tac >>
  drule comp_syn_ok_upd_local_clock >>
  disch_then drule >>
  fs [] >> strip_tac >>
  qpat_x_assum ‘evaluate (nested_seq p,_) = _’ mp_tac >>
  once_rewrite_tac [ADD_ASSOC] >>
  strip_tac >>
  fs [wlab_wloc_def] >>
  assume_tac nested_seq_pure_evaluation >>
  pop_assum (qspecl_then [‘p’, ‘fp’, ‘t’, ‘st'’, ‘st with clock := ck' + st.clock’, ‘l’,
                          ‘itmp’, ‘le’, ‘Word c’, ‘ck + ck'’, ‘0’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   fs [eval_upd_clock_eq] >>
   drule comp_exp_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   drule comp_exps_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   gen_tac >>
   strip_tac >> fs [] >>
   imp_res_tac locals_rel_intro >>
   drule compile_exp_le_tmp_domain >>
   disch_then (qspecl_then [‘tmp’, ‘l’, ‘h’, ‘p’, ‘le’,
                            ‘itmp’, ‘cut_sets l (nested_seq p)’, ‘n’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    rw [] >>
    drule eval_some_var_cexp_local_lookup >>
    disch_then drule >>
    strip_tac >> res_tac >> fs []) >>
   fs []) >>
  fs []) >>
  TRY (
  rename [‘Const w’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, evaluate_def, eval_def,
      wlab_wloc_def, state_rel_clock_add_zero]) >>
  TRY (
  rename [‘eval s (Var vname)’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, evaluate_def, find_var_def] >>
  imp_res_tac locals_rel_intro >>
  fs [eval_def, state_rel_clock_add_zero]) >>
  TRY (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, compile_exp_def, CaseEq "option"] >>
   rveq >>
   qexists_tac ‘0’ >> fs [] >>
   ‘t with clock := t.clock = t’ by fs [state_component_equality] >>
   fs [] >> pop_assum kall_tac >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def, locals_rel_def, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs []) >>
  TRY (
  rename [‘eval s (Load e)’] >>
  fs [crepSemTheory.eval_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >>
  fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  last_x_assum drule_all >> fs [] >> rveq >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def] >>
  fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
  imp_res_tac state_rel_intro >>
  imp_res_tac mem_rel_intro >>
  last_x_assum (qspec_then ‘c’ mp_tac) >> fs []) >>
  TRY (
  rename [‘eval s (LoadByte e)’] >>
  fs [crepSemTheory.eval_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >>
  fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  last_x_assum drule_all >>
  fs [] >> rveq >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign tmp' le'; LoadByte tmp' tmp']’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
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
  first_x_assum drule >> fs []) >>
  TRY (
  rename [‘eval s (LoadGlob gadr)’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, loopSemTheory.evaluate_def] >>
  fs [eval_def] >>
  imp_res_tac globals_rel_intro >>
  fs [] >>
  qexists_tac ‘0’ >> fs [] >>
  ‘t with clock := t.clock = t’ suffices_by fs [] >>
  fs [state_component_equality]) >>
  TRY (
  rename [‘Shift’] >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab",
      compile_exp_def] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [loopSemTheory.evaluate_def] >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def]) >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> fs [compile_exp_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   strip_tac >> fs [] >> rveq >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e = (p1,le1,tmp1,l1)’ >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e' = (p2,le2,tmp2,l2)’ >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp1’, ‘l1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_out_rel >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ _ ++ np)’ >>
   qpat_x_assum ‘evaluate (nested_seq p1,_) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'’ assume_tac) >>
   drule evaluate_comb_seq >>
   disch_then drule >>
   fs [evaluate_nested_seq_comb_seq] >>
   strip_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   fs [] >>
   qexists_tac ‘ck + ck' + 1’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘np’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [eval_upd_clock_eq] >>
   ‘eval st' le1 = eval st le1’ by (
     qpat_x_assum ‘_ = (_, st)’ assume_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then (qspecl_then [‘p2’, ‘st'’, ‘l’, ‘tmp1’, ‘le1’, ‘Word w1’, ‘ck'’] mp_tac) >>
     fs [wlab_wloc_def] >>
     impl_tac
     >- (
      imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
      gen_tac >>
      strip_tac >> fs [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_le_tmp_domain >>
      disch_then (qspecl_then [‘tmp’, ‘l’, ‘e’, ‘p1’, ‘le1’,
                               ‘tmp1’, ‘cut_sets l (nested_seq p1)’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac
      >- (
       rw [] >>
       imp_res_tac eval_some_var_cexp_local_lookup >>
       res_tac >> fs []) >>
      fs []) >>
     fs []) >>
   fs [] >> rfs [] >>
   pop_assum kall_tac >>
   rveq >>
   fs [wlab_wloc_def, loopSemTheory.set_var_def,
       loopSemTheory.eval_def] >>
   fs [Once eval_upd_locals_clock_eq] >>
   ‘eval (st' with locals := insert (tmp2 + 1) (Word w1) st'.locals) le2 =
    eval st' le2’ by (
     ho_match_mp_tac locals_touched_eq_eval_eq >>
     fs [] >> rw [] >> fs [lookup_insert] >>
     TOP_CASE_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then [‘tmp1’, ‘cut_sets l (nested_seq p1)’, ‘e'’, ‘p2’, ‘le2’,
                              ‘tmp2’, ‘cut_sets (cut_sets l (nested_seq p1)) (nested_seq p2)’, ‘n’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      rw [] >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> res_tac >> fs [] >> rveq >> fs []) >>
     fs []) >>
   fs [] >>
   pop_assum kall_tac >>
   fs [] >> rfs [] >> rveq >>
   fs [lookup_insert] >>
   fs [get_var_imm_def, list_insert_def] >>
   cases_on ‘word_cmp cmp w1 w2’ >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.set_var_def] >> (
   fs [cut_res_def, list_insert_def] >>
   fs [cut_state_def] >>
   imp_res_tac locals_rel_intro >>
   fs [SUBSET_INSERT_RIGHT] >>
   rveq >> fs [dec_clock_def] >>
   fs [lookup_inter, lookup_insert] >>
   conj_tac >- EVAL_TAC >>
   conj_tac >- fs [state_rel_def] >>
   fs [list_insert_def, locals_rel_def, domain_inter, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   fs [lookup_inter, lookup_insert] >>
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <= tmp2’ by (fs [ctxt_max_def] >> res_tac >> fs []) >>
   fs [domain_lookup])
QED

Theorem compile_Skip_Break_Continue:
  ^(get_goal "compile_prog _ _ crepLang$Skip") /\
  ^(get_goal "compile_prog _ _ crepLang$Break") /\
  ^(get_goal "compile_prog _ _ crepLang$Continue")
Proof
  rpt strip_tac >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def] >> rveq >>
  fs [state_rel_clock_add_zero]
QED


Theorem compile_Tick:
  ^(get_goal "compile_prog _ _ crepLang$Tick")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  fs [state_rel_def, empty_locals_def,
      crepSemTheory.dec_clock_def, dec_clock_def] >>
  qexists_tac ‘0’ >> fs []
QED

Theorem compile_Seq:
  ^(get_goal "compile_prog _ _ (crepLang$Seq _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def] >>
  pairarg_tac >> fs [] >>
  cases_on ‘res' = NONE’ >> fs [] >> rveq
  >- (
   fs [compile_prog_def] >>
   fs [evaluate_def] >>
   first_x_assum drule_all >>
   strip_tac >> fs [] >>
   first_x_assum  drule_all >>
   strip_tac >> fs [] >>
   qexists_tac ‘ck + ck'’ >> rfs [] >>
   qpat_x_assum ‘_ (compile_prog _ _ c1, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs []) >>
  fs [compile_prog_def] >>
  fs [evaluate_def] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> rfs [] >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs []
QED


Theorem compile_Return:
  ^(get_goal "compile_prog _ _ (crepLang$Return _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘ntmp’,‘nl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[Assign (ntmp + 1) le; Return (ntmp + 1)]’ mp_tac) >>
  strip_tac >> fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >>
  fs [set_var_def, lookup_insert, call_env_def] >>
  rveq >> fs [crepSemTheory.empty_locals_def, state_rel_def]
QED

Theorem compile_Raise:
  ^(get_goal "compile_prog _ _ (crepLang$Raise _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, eval_def, set_var_def, lookup_insert,
      call_env_def, state_rel_def, crepSemTheory.empty_locals_def] >> rveq >>
  fs [] >>
  qexists_tac ‘0’ >>
  fs []
QED

Theorem locals_rel_insert_gt_vmax:
  !ct cset lcl lcl' n w.
   locals_rel ct cset lcl lcl' /\ ct.vmax < n ==>
    locals_rel ct cset lcl (insert n w lcl')
Proof
  rw [] >>
  fs [locals_rel_def, SUBSET_INSERT_RIGHT, AllCaseEqs(),
      lookup_insert, ctxt_max_def] >>
  rw [] >> rpt (res_tac >> fs [])
QED

Theorem locals_rel_cutset_prop:
  !ct cset lcl lcl' cset' lcl''.
   locals_rel ct cset lcl lcl' /\
   locals_rel ct cset' lcl lcl'' /\
   subspt cset cset' ==>
    locals_rel ct cset lcl lcl''
Proof
  rw [locals_rel_def]
  >- metis_tac [subspt_domain, SUBSET_TRANS] >>
  res_tac >> fs [] >> rveq >> fs []
QED


Theorem compile_Store:
  ^(get_goal "compile_prog _ _ (crepLang$Store _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ dst = (dp, dle,dtmp,dl)’ >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ src = (sp, sle, stmp, sl)’ >>
  qpat_x_assum ‘eval _ dst = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘dp’,‘dle’,‘dtmp’,‘dl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qpat_x_assum ‘eval _ src = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘st’, ‘ctxt’, ‘dtmp’, ‘dl’,
                           ‘sp’,‘sle’,‘stmp’,‘sl’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel >> fs []) >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck + ck'’ >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq dp, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ mp_tac) >>
  strip_tac >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign (stmp + 1) sle; Store dle (stmp + 1)]’ mp_tac) >>
  fs [] >>
  strip_tac >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def, set_var_def] >>
  fs [wlab_wloc_def] >>
  ‘eval (st' with locals := insert (stmp + 1) (wlab_wloc ctxt w) st'.locals) dle =
   SOME (Word adr)’ by (
    qpat_x_assum ‘evaluate (nested_seq dp,_ with clock := ck + _) = _’ assume_tac >>
    drule nested_seq_pure_evaluation >>
    disch_then (qspecl_then [‘sp’, ‘st'’, ‘l’, ‘dtmp’, ‘dle’,
                             ‘Word adr’,‘ck'’] mp_tac) >> fs [] >>
    impl_tac
    >- (
     imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
     imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
     gen_tac >> strip_tac >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then [‘(ctxt.vmax + 1)’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                              ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘n’] mp_tac) >>
     fs [] >>
     impl_tac
     >- (
      rw [] >>
      imp_res_tac eval_some_var_cexp_local_lookup >>
      res_tac >> fs []) >>
     fs []) >>
    strip_tac >>
    pop_assum (assume_tac o GSYM) >>
    fs [] >>
    pop_assum kall_tac >>
    match_mp_tac locals_touched_eq_eval_eq >>
    fs [] >> rw [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
    imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exp_le_tmp_domain >>
    disch_then (qspecl_then [‘(ctxt.vmax + 1)’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                             ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘stmp + 1’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    imp_res_tac eval_some_var_cexp_local_lookup >>
    res_tac >> fs []) >>
  fs [] >> pop_assum kall_tac >>
  fs [mem_store_def, panSemTheory.mem_store_def] >>
  rveq >> fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l sl’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac mem_rel_intro >>
  rw [mem_rel_def] >>
  fs [APPLY_UPDATE_THM] >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs []) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac globals_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED


Theorem compile_StoreByte:
  ^(get_goal "compile_prog _ _ (crepLang$StoreByte _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ dst = (dp, dle,dtmp,dl)’ >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ src = (sp, sle, stmp, sl)’ >>
  qpat_x_assum ‘eval _ dst = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘dp’,‘dle’,‘dtmp’,‘dl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qpat_x_assum ‘eval _ src = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘st’, ‘ctxt’, ‘dtmp’, ‘dl’,
                           ‘sp’,‘sle’,‘stmp’,‘sl’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel >> fs []) >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck + ck'’ >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq dp, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ mp_tac) >>
  strip_tac >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign (stmp + 1) dle; Assign (stmp + 2) sle;
                   StoreByte (stmp + 1) (stmp + 2)]’ mp_tac) >>
  fs [] >>
  strip_tac >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def, set_var_def] >>
  fs [wlab_wloc_def] >>
  ‘eval st' dle = SOME (Word adr)’ by (
    qpat_x_assum ‘evaluate (nested_seq dp,_ with clock := ck + _) = _’ assume_tac >>
    drule nested_seq_pure_evaluation >>
    disch_then (qspecl_then [‘sp’, ‘st'’, ‘l’, ‘dtmp’, ‘dle’,
                             ‘Word adr’,‘ck'’] mp_tac) >> fs [] >>
    impl_tac
    >- (
     imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
     imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
     gen_tac >> strip_tac >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then [‘ctxt.vmax + 1’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                              ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘n’] mp_tac) >>
     fs [] >>
     impl_tac
     >- (
      rw [] >>
      imp_res_tac eval_some_var_cexp_local_lookup >>
      res_tac >> fs []) >>
     fs []) >>
    fs []) >>
  fs [] >> pop_assum kall_tac >>
  ‘eval (st' with locals := insert (stmp + 1) (Word adr) st'.locals) sle =
   eval st' sle’ by (
    match_mp_tac locals_touched_eq_eval_eq >>
    fs [] >> rw [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
    imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exp_le_tmp_domain >>
    disch_then (qspecl_then [‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘src’,
                             ‘sp’, ‘sle’, ‘stmp’,
                             ‘cut_sets (cut_sets l (nested_seq dp)) (nested_seq sp)’,
                             ‘stmp + 1’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    imp_res_tac eval_some_var_cexp_local_lookup >>
    res_tac >> fs [] >> rveq >> rfs []) >>
  fs [] >> pop_assum kall_tac >>
  fs [wordSemTheory.mem_store_byte_aux_def, panSemTheory.mem_store_byte_def,
      AllCaseEqs ()] >>
  rveq >> fs [lookup_insert] >>
  ‘st'.memory (byte_align adr) = Word v’ by (
    imp_res_tac mem_rel_intro >>
    last_x_assum (qspec_then ‘byte_align adr’ mp_tac) >>
    metis_tac [wlab_wloc_def]) >>
  fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l sl’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac mem_rel_intro >>
  rw [mem_rel_def] >>
  fs [APPLY_UPDATE_THM] >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs [wlab_wloc_def]) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac globals_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem compile_StoreGlob:
  ^(get_goal "compile_prog _ _ (crepLang$StoreGlob _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘tmp’,‘l'’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[SetGlobal dst le]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  fs [crepSemTheory.set_globals_def, set_globals_def] >>
  fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l l'’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac globals_rel_intro >>
  rw [globals_rel_def, FLOOKUP_UPDATE]
  >- (TOP_CASE_TAC >> res_tac >> fs []) >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs []) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac mem_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem compile_Assign:
  ^(get_goal "compile_prog _ _ (crepLang$Assign _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  TOP_CASE_TAC >> fs []
  >- (imp_res_tac locals_rel_intro >> fs []) >>
  qmatch_goalsub_rename_tac ‘Assign n le’ >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘tmp’,‘l'’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[Assign n le]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  fs [crepSemTheory.set_var_def, set_var_def] >>
  fs [state_rel_def] >>
  imp_res_tac compile_exp_out_rel >>
  rveq >>
  drule cut_sets_union_domain_subset >>
  strip_tac >>
  fs [locals_rel_def] >>
  rw []
  >- (
   match_mp_tac SUBSET_TRANS >>
   qexists_tac ‘domain (cut_sets l (nested_seq p))’ >> fs [] >>
   metis_tac [SUBSET_INSERT_RIGHT]) >>
  fs [FLOOKUP_UPDATE] >> reverse FULL_CASE_TAC >> rveq >> fs []
  >- (
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <> n'’ suffices_by fs [lookup_insert] >>
   CCONTR_TAC >>
   fs [distinct_vars_def] >>
   res_tac >> fs []) >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >> rveq >>
  rw [] >>
  imp_res_tac globals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac mem_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem not_mem_context_assigned_mem_gt:
  !ctxt l p n.
   ctxt_max ctxt.vmax ctxt.vars /\
   (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧
   n <= ctxt.vmax  (* /\  n ∈ domain l *) ==>
   ~MEM n (assigned_vars (compile_prog ctxt l p))
Proof
 cheat
QED

Theorem member_cutset_survives_comp:
  !ctxt l p n.
   n ∈ domain l ==>
   survives n (compile_prog ctxt l p)
Proof
  cheat
QED

val abc_tac =
    conj_tac >- fs [state_rel_def] >>
    conj_tac
    >- (
     rw [mem_rel_def] >>
     drule mem_rel_intro >>
     disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
     cases_on ‘st.memory ad’ >> fs [wlab_wloc_def]) >>
    conj_tac
    >- (
     rw [globals_rel_def] >>
     drule globals_rel_intro >>
     disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
     res_tac >> fs [] >>
     cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
     fs [code_rel_def]


Theorem compile_Dec:
  ^(get_goal "compile_prog _ _ (crepLang$Dec _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’, ‘le’, ‘tmp’, ‘nl’] mp_tac) >>
  fs [] >>
  strip_tac >> fs [] >>
  last_x_assum (qspecl_then
                [‘st' with locals := insert tmp (wlab_wloc ctxt value) st'.locals’,
                 ‘ctxt with <|vars := ctxt.vars |+ (v,tmp); vmax := tmp|>’,
                 ‘insert tmp () l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   imp_res_tac compile_exp_out_rel >>
   conj_tac
   >- (
    rw [mem_rel_def] >>
    drule mem_rel_intro >>
    disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
    cases_on ‘s.memory ad’ >> fs [wlab_wloc_def] >>
    FULL_CASE_TAC >> rfs []) >>
   conj_tac
   >- (
    rw [globals_rel_def] >>
    drule globals_rel_intro >>
    disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
    res_tac >> fs [] >>
    cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
   conj_tac >- fs [code_rel_def] >>
   imp_res_tac locals_rel_intro >>
   rw [locals_rel_def]
   >- (
    fs [distinct_vars_def] >>
    rw [] >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs [] >>
    FULL_CASE_TAC >> fs [] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs [])
   >- (
    rw [ctxt_max_def] >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs [] >>
    fs [ctxt_max_def] >> res_tac >> rfs [])
   >- (
    drule cut_sets_union_domain_subset >>
    strip_tac >>
    metis_tac [SUBSET_TRANS, SUBSET_INSERT_RIGHT]) >>
   fs [FLOOKUP_UPDATE] >>
   TOP_CASE_TAC >> fs [] >> rveq
   >- (
    cases_on ‘v'’ >> fs [wlab_wloc_def] >>
    imp_res_tac globals_rel_intro >>
    imp_res_tac code_rel_intro >>
    imp_res_tac mem_rel_intro >>
    drule eval_label_eq_state_contains_label >>
    rw [] >> res_tac >> fs []) >>
   res_tac >> fs [] >> rveq >>
   fs [lookup_insert] >> TOP_CASE_TAC >> fs [] >> rveq
   >- (
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq p,_) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >> disch_then (qspec_then ‘ck'’ assume_tac) >>
  qexists_tac ‘ck + ck'’ >>
  fs [evaluate_def] >>
  fs [Once eval_upd_clock_eq] >>
  fs [set_var_def] >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac
  >- (
   rw [mem_rel_def] >>
   drule mem_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   cases_on ‘st.memory ad’ >> fs [wlab_wloc_def]) >>
  conj_tac
  >- (
   rw [globals_rel_def] >>
   drule globals_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   res_tac >> fs [] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  conj_tac >- fs [code_rel_def] >>
  imp_res_tac compile_exp_out_rel_cases >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   imp_res_tac locals_rel_intro >>
   rw [locals_rel_def]
   >- fs [domain_insert] >>
  cases_on ‘vname = v’ >> rveq
   >- (
    cases_on ‘FLOOKUP s.locals v’ >>
    fs [crepSemTheory.res_var_def] >>
    fs [FLOOKUP_UPDATE] >> rveq >>
    qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME pv’ >>
    res_tac >> fs [] >> rveq >>
    qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.vars v = SOME pn’ >>
    qpat_x_assum ‘evaluate (compile_prog _ _ _, _) = _’ assume_tac >>
    drule unassigned_vars_evaluate_same >>
    fs [] >>
    disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt pv’] mp_tac) >>
    impl_tac
    >- (
     conj_tac
     >- (
      ‘pn <> tmp’ suffices_by fs [lookup_insert] >>
      CCONTR_TAC >>
      fs [] >>
      imp_res_tac compile_exp_out_rel_cases >>
      fs [ctxt_max_def] >> res_tac >> fs []) >>
     conj_tac
     >- (
      match_mp_tac not_mem_context_assigned_mem_gt >>
      fs [] >>
      imp_res_tac compile_exp_out_rel_cases >>
      fs [ctxt_max_def] >> res_tac >> fs [] >>
      rw [FLOOKUP_UPDATE] >>
      CCONTR_TAC >>
      fs [distinct_vars_def] >>
      res_tac >> fs []) >>
     match_mp_tac member_cutset_survives_comp >>
     fs [domain_insert]) >>
    fs []) >>
   cases_on ‘FLOOKUP s.locals v’ >>
   fs [crepSemTheory.res_var_def]
   >- (
    fs [DOMSUB_FLOOKUP_THM] >>
    last_x_assum drule >>
    strip_tac >> fs [] >> rveq
    >- (
     rfs [FLOOKUP_UPDATE] >> rveq >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
    rfs [FLOOKUP_UPDATE] >>
    cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
   qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME rv’ >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >> rveq
   >- (
    rfs [FLOOKUP_UPDATE] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   rfs [FLOOKUP_UPDATE] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  cases_on ‘x’ >> fs [] >> rveq >>
  TRY abc_tac >>
  TRY (
  cases_on ‘w’ >> fs [wlab_wloc_def] >> NO_TAC) >> (
  imp_res_tac locals_rel_intro >>
  rw [locals_rel_def]
  >- fs [domain_insert] >>
  cases_on ‘vname = v’ >> rveq
  >- (
   cases_on ‘FLOOKUP s.locals v’ >>
   fs [crepSemTheory.res_var_def] >>
   fs [FLOOKUP_UPDATE] >> rveq >>
   qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME pv’ >>
   res_tac >> fs [] >> rveq >>
   qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.vars v = SOME pn’ >>
   qpat_x_assum ‘evaluate (compile_prog _ _ _, _) = _’ assume_tac >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt pv’] mp_tac) >>
   impl_tac
   >- (
    conj_tac
    >- (
     ‘pn <> tmp’ suffices_by fs [lookup_insert] >>
     CCONTR_TAC >>
     fs [] >>
     imp_res_tac compile_exp_out_rel_cases >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    conj_tac
    >- (
     match_mp_tac not_mem_context_assigned_mem_gt >>
     fs [] >>
     imp_res_tac compile_exp_out_rel_cases >>
     fs [ctxt_max_def] >> res_tac >> fs [] >>
     rw [FLOOKUP_UPDATE] >>
     CCONTR_TAC >>
     fs [distinct_vars_def] >>
     res_tac >> fs []) >>
    match_mp_tac member_cutset_survives_comp >>
    fs [domain_insert]) >>
   fs []) >>
  cases_on ‘FLOOKUP s.locals v’ >>
  fs [crepSemTheory.res_var_def]
  >- (
   fs [DOMSUB_FLOOKUP_THM] >>
   last_x_assum drule >>
   strip_tac >> fs [] >> rveq
   >- (
    rfs [FLOOKUP_UPDATE] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   rfs [FLOOKUP_UPDATE] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME rv’ >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >> rveq
  >- (
   rfs [FLOOKUP_UPDATE] >> rveq >>
   fs [ctxt_max_def] >> res_tac >> rfs []) >>
  rfs [FLOOKUP_UPDATE] >>
  cases_on ‘v'’ >> fs [wlab_wloc_def])
QED

Theorem compile_If:
  ^(get_goal "compile_prog _ _ (crepLang$If _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘np’,‘le’,‘tmp’,‘nl’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [wlab_wloc_def] >>
  last_x_assum mp_tac >>
  disch_then (qspecl_then
              [‘st with locals := insert tmp (Word w) st.locals’,
               ‘ctxt’, ‘l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   imp_res_tac locals_rel_intro >>
   imp_res_tac compile_exp_out_rel >>
   rveq >>
   drule cut_sets_union_domain_subset >>
   strip_tac >>
   rw [locals_rel_def]
   >- (
    drule cut_sets_union_domain_subset >>
    strip_tac >>
    ‘domain l ⊆ domain st.locals’
    suffices_by fs [SUBSET_INSERT_RIGHT] >>
    match_mp_tac SUBSET_TRANS >>
    qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
    fs []) >>
   res_tac >> fs [] >> rveq >>
   ‘n <> tmp’ suffices_by fs [lookup_insert] >>
   CCONTR_TAC >> fs [] >> rveq >>
   fs [ctxt_max_def] >> res_tac >> rfs []) >>
  strip_tac >> fs [] >>
  cases_on ‘res’ >> fs [] >> rveq
  >- (
   qpat_x_assum ‘evaluate (compile_prog _ _ _, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + 1’ assume_tac) >>
   qexists_tac ‘ck + ck' + 1’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp le;
                 If NotEqual tmp (Imm 0w) (compile_prog ctxt l c1)
                 (compile_prog ctxt l c2) l]’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [nested_seq_def] >>
   fs [evaluate_def, eval_upd_clock_eq, set_var_def] >>
   fs [get_var_imm_def] >>
   cases_on ‘w <> 0w’ >>
   fs [asmTheory.word_cmp_def, cut_res_def, cut_state_def] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   TRY (imp_res_tac locals_rel_intro >> fs [] >> NO_TAC) >>
   fs [dec_clock_def] >> conj_tac >>
   TRY (fs [state_rel_def] >> NO_TAC) >>
   imp_res_tac locals_rel_intro >>
   imp_res_tac compile_exp_out_rel >>
   rveq >>
   drule cut_sets_union_domain_subset >>
   strip_tac >>
   rw [locals_rel_def] >>
   TRY (
   fs [domain_inter] >>
   match_mp_tac SUBSET_TRANS >>
   qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
   fs [] >> NO_TAC) >>
   res_tac >> rfs [] >>
   fs [lookup_inter, domain_lookup]) >>
  qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  qexists_tac ‘ck + ck'’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign tmp le;
                If NotEqual tmp (Imm 0w) (compile_prog ctxt l c1)
                 (compile_prog ctxt l c2) l]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def] >>
  fs [evaluate_def, eval_upd_clock_eq, set_var_def] >>
  fs [get_var_imm_def] >>
  cases_on ‘x’ >> fs [] >> rveq >>
  cases_on ‘w <> 0w’ >>
  fs [asmTheory.word_cmp_def, cut_res_def]
QED

Theorem compile_FFI:
  ^(get_goal "compile_prog _ _ (crepLang$ExtCall _ _ _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_prog_def, AllCaseEqs ()] >> rveq >> fs [] >>
  imp_res_tac locals_rel_intro >>
  res_tac >> rfs [] >>
  fs [evaluate_def, wlab_wloc_def] >>
  fs [cut_state_def] >>
  ‘mem_load_byte_aux t.memory t.mdomain t.be =
   mem_load_byte s.memory s.memaddrs s.be’ by (
    match_mp_tac EQ_EXT >>
    rw [] >>
    fs [state_rel_def, panSemTheory.mem_load_byte_def,
        wordSemTheory.mem_load_byte_aux_def] >>
    fs [mem_rel_def] >>
    first_x_assum (qspec_then ‘byte_align x’ assume_tac) >>
    TOP_CASE_TAC >> fs [wlab_wloc_def] >>
    cases_on ‘s.memory (byte_align x)’ >>
    fs [wlab_wloc_def, AllCaseEqs ()]) >>
  fs [state_rel_def]
  >- (
  (* qexists_tac ‘0’ >> fs [] >>
   reverse conj_tac
   >- (
    fs [locals_rel_def] >>
    fs [domain_inter] >>
    rw [] >>
    res_tac >> fs [] >> rveq >>
    rfs [lookup_inter, domain_lookup]) >>
   cases_on ‘new_bytes’ >>
   fs [panSemTheory.write_bytearray_def,
       wordSemTheory.write_bytearray_def] >>
   rveq >> fs [AllCaseEqs ()] >>
   TOP_CASE_TAC >> fs [] >> cheat *)
   cheat) >>
  fs [call_env_def] >>
  qexists_tac ‘0’ >> fs []
QED




val _ = export_theory();
