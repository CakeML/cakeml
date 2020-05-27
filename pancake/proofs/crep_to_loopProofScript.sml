(*
  Correctness proof for ---
*)

open preamble
     crepSemTheory loopSemTheory
     crep_to_loopTheory


val _ = new_theory "crep_to_loopProof";

val _ = set_grammar_ancestry  ["crepSem", "loopSem", "crep_to_loop"];

Datatype:
  context =
  <| vars    : crepLang$varname |-> num;
     funcs   : crepLang$funname |-> num # num list;  (* loc, args *)
     vmax : num|>
End


Definition comp_assigns_def:
  (comp_assigns f ctxt [] =  Skip) /\
  (comp_assigns f ctxt (e::es) =
   Seq (f ctxt e)
       (comp_assigns f (ctxt with vmax := ctxt.vmax + 1) es))
End



(*
Definition comp_assigns_def:
  (comp_assigns f m re [] =  Skip) /\
  (comp_assigns f m re (e::es) =
   Seq (Seq (f e) (Assign m re))
       (comp_assigns f (m+1) re es))
End
*)

Definition load_exps_def:
  load_exps n m  = MAP Var (GENLIST (λx. n + x) m)
End

Definition compile_exp_def:
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


(*  (compile_exp ctxt (Op bop es) =
   Seq (comp_assigns (compile_exp ctxt) (ctxt.vmax + 2) (Var (ctxt.vmax + 1)) es)
       (Assign (ctxt.vmax + 1) (Op bop (load_exps (ctxt.vmax + 2) (LENGTH es))))) /\ *)
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



Definition compile_prog_def:
  (compile_prog _ (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog)) /\
  (compile_prog _ (Dec v e p) = ARB) /\
  (compile_prog ctxt (Assign v e) =
    Seq (compile_exp ctxt e)
        (Assign v (Var (ctxt.vmax + 1))))
End


(* state relation *)

val s = ``(s:('a,'ffi) crepSem$state)``

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) loopSem$state) <=>
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
    | NONE =>  Loc 0 0)
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
     ?loc args. FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, compile_prog nctxt prog))
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
  locals_rel ctxt (s_locals:num |-> 'a word_lab) t_locals <=>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n v'. FLOOKUP ctxt.vars vname = SOME n ∧
    lookup n t_locals = SOME v' ∧ wlab_wloc ctxt v = v'
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ code_rel ctxt s.code t.code /\
      locals_rel ctxt s.locals t.locals ⇒
      ∃res1 t1. evaluate (compile_prog ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧ code_rel ctxt s1.code t1.code /\
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME _ => ARB``

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


Theorem locals_rel_intro:
  locals_rel ctxt (s_locals:num |-> 'a word_lab) t_locals ==>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n v'. FLOOKUP ctxt.vars vname = SOME n ∧
    lookup n t_locals = SOME v' ∧ wlab_wloc ctxt v = v'
Proof
  rw [locals_rel_def]
QED

Theorem code_rel_intro:
  code_rel ctxt s_code t_code ==>
   distinct_funcs ctxt.funcs /\
   (∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc args. FLOOKUP ctxt.funcs f = SOME (loc, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup loc t_code = SOME (ns, compile_prog nctxt prog))
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


Theorem compile_Assign:
  ^(get_goal "compile_prog _ (crepLang$Assign _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  fs [crepSemTheory.evaluate_def] >>
  fs [CaseEq "option"] >> rveq >> fs [] >>
  fs [compile_prog_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>




QED

val _ = export_theory();
