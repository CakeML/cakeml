(*
  Compilation from crepLang to panLang.
*)
open preamble crepLangTheory
     loopLangTheory sptreeTheory

val _ = new_theory "crep_to_loop"

val _ = set_grammar_ancestry
        ["crepLang", "loopLang",
         "backend_common", "sptree"];

Datatype:
  context =
  <| vars    : crepLang$varname |-> num;
     funcs   : crepLang$funname |-> num # num list;  (* loc, args *)
     ceids    : ('a word) list;
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


Definition compile_prog_def:
  (compile_prog _ _ (Skip:'a crepLang$prog) = (Skip:'a loopLang$prog)) /\
  (compile_prog _ _ Break = Break) /\
  (compile_prog _ _ Continue = Continue) /\
  (compile_prog _ _ Tick = Tick) /\
  (compile_prog ctxt l (Return e) =
    let (p, le, ntmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e in
      nested_seq (p ++ [Assign ntmp le; Return ntmp])) /\
  (compile_prog ctxt l (Raise eid) =
    Seq (Assign (ctxt.vmax + 1) (Const eid)) (Raise (ctxt.vmax + 1))) /\
  (compile_prog ctxt l (Store dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++ [Assign tmp le'; Store le tmp])) /\
  (compile_prog ctxt l (StoreByte dst src) =
    let (p, le, tmp, l) = compile_exp ctxt (ctxt.vmax + 1) l dst in
      let (p', le', tmp, l) = compile_exp ctxt tmp l src in
        nested_seq (p ++ p' ++
                     [Assign tmp le; Assign (tmp + 1) le';
                      StoreByte tmp (tmp + 1)])) /\
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

  (compile_prog ctxt l (While e p) =
    let (np, le, tmp, nl) = compile_exp ctxt (ctxt.vmax + 1) l e;
        lp = compile_prog ctxt l p in
     Loop l (nested_seq (np ++ [
                Assign tmp le;
                If NotEqual tmp (Imm 0w)
                   (Seq lp Continue) Break l]))
          l) /\
  (compile_prog ctxt l (Call Tail e es) =
   let (p, les, tmp, nl) = compile_exps ctxt (ctxt.vmax + 1) l (es ++ [e]);
       nargs = gen_temps tmp (LENGTH les) in
   nested_seq (p ++ MAP2 Assign nargs les ++
               [Call NONE NONE nargs NONE])) /\


  (compile_prog ctxt l (Call (Ret rt rp hdl) e es) =
   let (p, les, tmp, nl) = compile_exps ctxt (ctxt.vmax + 1) l (es ++ [e]);
       nargs = gen_temps tmp (LENGTH les);
       rn  = rt_var ctxt.vars rt (ctxt.vmax + 1) (ctxt.vmax + 1);
       en  = ctxt.vmax + 1;
       pr  = compile_prog ctxt l rp;
       pe  = case hdl of
              | NONE => Raise en
              | SOME (Handle eid ep) =>
                let cpe = compile_prog ctxt l ep in
                if ~MEM eid ctxt.ceids then (Raise en)
                else (If NotEqual en (Imm eid) (Raise en) (Seq Tick cpe) l) in
      nested_seq (p ++ MAP2 Assign nargs les ++
               [Call (SOME (rn, l)) NONE nargs
                     (SOME (en, pe, pr, l))])) /\
  (compile_prog ctxt l (ExtCall f ptr1 len1 ptr2 len2) =
    case (FLOOKUP ctxt.vars ptr1, FLOOKUP ctxt.vars len1,
          FLOOKUP ctxt.vars ptr2, FLOOKUP ctxt.vars len2) of
     | (SOME pc, SOME lc, SOME pc', SOME lc') =>
         FFI (explode f) pc lc pc' lc' l
     | _ => Skip)
End

val _ = export_theory();
