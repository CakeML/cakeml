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
     funcs   : crepLang$funname |-> num # num list;
     vmax : num|>
End

Definition comp_assigns_def:
  (comp_assigns f m re [] =  Skip) /\
  (comp_assigns f m re (e::es) =
   Seq (Seq (f e) (Assign m re))
       (comp_assigns f (m+1) re es))
End

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
  (compile_exp ctxt (Label fname) = Assign (ctxt.vmax + 1)
   (case FLOOKUP ctxt.funcs fname of
     | SOME (n, _) => Var n
     | NONE => Var 0)) /\
  (compile_exp ctxt (Load adr) =
   Seq (compile_exp ctxt adr)
       (Assign (ctxt.vmax + 1) (Load (Var (ctxt.vmax + 1))))) /\
  (compile_exp ctxt (LoadByte adr) =
   Seq (compile_exp ctxt adr)
       (LoadByte (ctxt.vmax + 1) 0w (ctxt.vmax + 1))) /\
  (compile_exp ctxt (LoadGlob gadr) = Assign (ctxt.vmax + 1) (Lookup gadr)) /\
  (compile_exp ctxt (Op bop es) =
   Seq (comp_assigns (compile_exp ctxt) (ctxt.vmax + 2) (Var (ctxt.vmax + 1)) es)
       (Assign (ctxt.vmax + 1) (Op bop (load_exps (ctxt.vmax + 2) (LENGTH es))))) /\
  (compile_exp ctxt (Cmp cmp e e') =
   Seq (comp_assigns (compile_exp ctxt) (ctxt.vmax + 2) (Var (ctxt.vmax + 1)) [e;e'])
       (If cmp (ctxt.vmax + 2) (Reg (ctxt.vmax + 3))
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
  (λad. wlab_wloc ctxt (smem ad)) = tmem
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
     ?fvar args. FLOOKUP ctxt.funcs f = SOME (fvar, args) /\
       LENGTH ns = LENGTH args /\
       let nctxt = ctxt_fc ctxt.funcs ns args  in
       lookup fvar t_code = SOME (ns, compile_prog nctxt prog))
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




val _ = export_theory();
