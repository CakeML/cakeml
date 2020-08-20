(*
  Compilation from crepLang to panLang.
*)
open preamble crepLangTheory
     loopLangTheory sptreeTheory
     loop_liveTheory

val _ = new_theory "crep_to_loop"

val _ = set_grammar_ancestry
        ["crepLang", "loopLang",
         "backend_common", "sptree"];

Datatype:
  context =
  <| vars   : crepLang$varname |-> num;
     funcs  : crepLang$funname |-> num # num;  (* loc, length args *)
     ceids  : ('a word) list;
     vmax   : num|>
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
  wf_rel_tac ‘measure (\x. case ISR x of
                       | T => list_size (crepLang$exp_size ARB) (SND(SND(SND (OUTR x))))
                       | F => crepLang$exp_size ARB (SND(SND(SND (OUTL x)))))’ >>
  rw [] >>
  TRY (rw [list_size_def,
           crepLangTheory.exp_size_def] >> NO_TAC) >>
  qid_spec_tac ‘es’ >>
  Induct >> rw [] >>
  fs [list_size_def, crepLangTheory.exp_size_def]
End

Definition gen_temps_def:
  gen_temps n l = GENLIST (\x. n + x) l
End

Definition rt_var_def:
  rt_var fm NONE (n:num) mx = n /\
  rt_var fm (SOME v) n mx =
    case FLOOKUP fm v of
     | NONE => mx+1 (* impossible, greater than max to prove a prop later *)
     | SOME m => m
End


Definition compile_def:
  (compile _ _ (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog)) /\
  (compile _ _ Break = Break) /\
  (compile _ _ Continue = Continue) /\
  (compile _ _ Tick = Tick) /\
  (compile ctxt l (Return e) =
    let (p, le, ntmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e in
      nested_seq (p ++ [Assign ntmp le; Return ntmp])) /\
  (compile ctxt l (Raise eid) =
    Seq (Assign (ctxt.vmax + 1) (Const eid)) (Raise (ctxt.vmax + 1))) /\
  (compile ctxt l (Store dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++ [Assign tmp le'; Store le tmp])) /\
  (compile ctxt l (StoreByte dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++
                     [Assign tmp le; Assign (tmp + 1) le';
                      StoreByte tmp (tmp + 1)])) /\
  (compile ctxt l (StoreGlob adr e) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in
        nested_seq (p ++ [SetGlobal adr le])) /\
  (compile ctxt l (Seq p q) =
    Seq (compile ctxt l p) (compile ctxt l q)) /\
  (compile ctxt l (Assign v e) =
    case FLOOKUP ctxt.vars v of
     | SOME n =>
       let (p,le,tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l e in
        nested_seq (p ++ [Assign n le])
     | NONE => Skip) /\
  (compile ctxt l (Dec v e prog) =
    let (p,le,tmp,nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
         nctxt = ctxt with <|vars := ctxt.vars |+ (v,tmp);
                             vmax := tmp|>;
         fl = insert tmp () l;
         lp = compile nctxt fl prog in
     Seq (nested_seq p) (Seq (Assign tmp le) lp)) /\
  (compile ctxt l (If e p q) =
    let (np, le, tmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
        lp = compile ctxt l p;
        lq = compile ctxt l q in
    nested_seq (np ++ [Assign tmp le;
                       If NotEqual tmp (Imm 0w) lp lq l])) /\

  (compile ctxt l (While e p) =
    let (np, le, tmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
        lp = compile ctxt l p in
     Loop l (nested_seq (np ++ [
                Assign tmp le;
                If NotEqual tmp (Imm 0w)
                   (Seq lp Continue) Break l]))
          l) /\
  (compile ctxt l (Call Tail e es) =
   let (p, les, tmp, nl) = compile_exps ctxt (ctxt.vmax + 1) l (es ++ [e]);
       nargs = gen_temps tmp (LENGTH les) in
   nested_seq (p ++ MAP2 Assign nargs les ++
               [Call NONE NONE nargs NONE])) /\
  (compile ctxt l (Call (Ret rt rp hdl) e es) =
   let (p, les, tmp, nl) = compile_exps ctxt (ctxt.vmax + 1) l (es ++ [e]);
       nargs = gen_temps tmp (LENGTH les);
       rn  = rt_var ctxt.vars rt (ctxt.vmax + 1) (ctxt.vmax + 1);
       en  = ctxt.vmax + 1;
       pr  = compile ctxt l rp;
       pe  = case hdl of
              | NONE => Raise en
              | SOME (Handle eid ep) =>
                let cpe = compile ctxt l ep in
                if ~MEM eid ctxt.ceids then (Raise en)
                else (If NotEqual en (Imm eid) (Raise en) (Seq Tick cpe) l) in
      nested_seq (p ++ MAP2 Assign nargs les ++
               [Call (SOME (rn, l)) NONE nargs
                     (SOME (en, pe, pr, l))])) /\
  (compile ctxt l (ExtCall f ptr1 len1 ptr2 len2) =
    case (FLOOKUP ctxt.vars ptr1, FLOOKUP ctxt.vars len1,
          FLOOKUP ctxt.vars ptr2, FLOOKUP ctxt.vars len2) of
     | (SOME pc, SOME lc, SOME pc', SOME lc') =>
         FFI (explode f) pc lc pc' lc' l
     | _ => Skip)
End

Definition mk_ctxt_def:
  mk_ctxt vmap fs vmax (eids:'a word list) =
     <|vars  := vmap;
       funcs := fs;
       vmax  := vmax;
       ceids := eids|>
End

Definition make_vmap_def:
  make_vmap params =
    FEMPTY |++ ZIP (params, GENLIST I (LENGTH params))
End

Definition comp_func_def:
  comp_func fs eids params body =
    let vmap = make_vmap params;
        vmax = LENGTH params - 1;
        l = list_to_num_set (GENLIST I (LENGTH params)) in
    compile (mk_ctxt vmap fs vmax eids) l body
End


Definition get_eids_def:
  get_eids prog =
   let prog = MAP (SND o SND) prog;
       p     = crepLang$nested_seq prog in
   SET_TO_LIST (exp_ids p)
End

Definition make_funcs_def:
  make_funcs prog =
  let fnames = MAP FST prog;
      fnums  = GENLIST I (LENGTH prog);
      lens = MAP (LENGTH o FST o SND) prog;
      fnums_lens = MAP2 (λx y. (x,y)) fnums lens;
      fs =  MAP2 (λx y. (x,y)) fnames fnums_lens in
    alist_to_fmap fs
End


Definition comp_c2l_def:
  comp_c2l prog =
  let fnums  = GENLIST I (LENGTH prog) in
   MAP2 (λn (name, params, body).
         (n,
          (GENLIST I o LENGTH) params,
          comp_func (make_funcs prog) (get_eids prog) params body))
   fnums prog
End

Definition compile_prog_def:
  compile_prog l prog =
  MAP (λ(n,ns,p). (n,ns, loop_live$optimise l p)) (comp_c2l prog)
End


val _ = export_theory();
