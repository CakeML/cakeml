(*
  Compilation from panLang to crepLang.
*)
open preamble pan_commonTheory panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["pan_common", "panLang","crepLang", "backend_common"];

Datatype:
  context =
  <| var_nums  : panLang$varname |-> shape # num list;
     code_vars : panLang$funname |-> ((panLang$varname # shape) list # num list);
     eid_map   : panLang$eid  |-> shape # ('a word);
     max_var   : num|>
End

(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es) of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End

Definition comp_field_def:
  (comp_field i [] es = ([Const 0w], One)) ∧
  (comp_field i (sh::shs) es =
   if i = (0:num) then (TAKE (size_of_shape sh) es, sh)
   else comp_field (i-1) shs (DROP (size_of_shape sh) es))
End

Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) =
   ([(Const c): 'a crepLang$exp], One)) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME (shape, ns) => (MAP Var ns, shape)
   | NONE => ([Const 0w], One)) /\
  (compile_exp ctxt (Label fname) = ([Label fname], One)) /\
  (compile_exp ctxt (Struct es) =
   let cexps = MAP (compile_exp ctxt) es in
   (FLAT (MAP FST cexps), Comb (MAP SND cexps))) /\
  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes => comp_field index shapes cexp) /\
  (compile_exp ctxt (Load sh e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | e::es => (load_shape (0w) (size_of_shape sh) e, sh)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case (cexp, shape) of
   | (e::es, One) => ([LoadByte e], One)
   | (_, _) => ([Const 0w], One)) /\
  (* have a check here for the shape *)
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   case cexp_heads cexps of
   | SOME es => ([Op bop es], One)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (Cmp cmp e e') =
   let ce  = FST (compile_exp ctxt e);
       ce' = FST (compile_exp ctxt e') in
   case (ce, ce') of
   | (e::es, e'::es') => ([Cmp cmp e e'], One)
   | (_, _) => ([Const 0w], One)) /\
  (compile_exp ctxt (Shift sh e n) =
   case FST (compile_exp ctxt e) of
   | [] => ([Const 0w], One)
   | e::es => ([Shift sh e n], One))
Termination
  wf_rel_tac `measure (\e. panLang$exp_size ARB (SND e))` >>
  rpt strip_tac >>
  imp_res_tac panLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

(*
Definition declared_handler_def:
  declared_handler sh mv =
    let nvars = GENLIST (λx. mv + SUC x) (size_of_shape sh);
        vs = load_globals 0w (LENGTH nvars) in
    nested_decs nvars vs
End
*)

Definition ret_var_def:
  ret_var sh ns =
   if size_of_shape (Comb sh) = 1 then oHD ns
    else NONE
End


Definition ret_hdl_def:
  ret_hdl sh ns =
   if 1 < size_of_shape (Comb sh) then (assign_ret ns)
    else Skip
End


Definition exp_hdl_def:
  exp_hdl fm v =
  case FLOOKUP fm v of
  | NONE => Skip
  | SOME (vshp, ns) => nested_seq
      (MAP2 Assign ns (load_globals 0w (LENGTH ns)))
End


Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.max_var;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|var_nums := ctxt.var_nums |+ (v, (sh, nvars));
                            max_var := ctxt.max_var + size_of_shape sh|> in
            if size_of_shape sh = LENGTH es
            then nested_decs nvars es (compile_prog nctxt p)
            else Skip) /\
  (compile_prog ctxt (Assign v e) =
   let (es, sh) = compile_exp ctxt e in
   case FLOOKUP ctxt.var_nums v of
    | SOME (vshp, ns) =>
      if LENGTH ns = LENGTH es
      then if distinct_lists ns (FLAT (MAP var_cexp es))
      then nested_seq (MAP2 Assign ns es)
      else let vmax = ctxt.max_var;
               temps = GENLIST (λx. vmax + SUC x) (LENGTH ns) in
           nested_decs temps es
                       (nested_seq (MAP2 Assign ns (MAP Var temps)))
      else Skip:'a crepLang$prog
    | NONE => Skip) /\
  (compile_prog ctxt (Store ad v) =
   case compile_exp ctxt ad of
    | (e::es',sh') =>
       let (es,sh) = compile_exp ctxt v;
            adv = ctxt.max_var + 1;
            temps = GENLIST (λx. adv + SUC x) (size_of_shape sh) in
            if size_of_shape sh = LENGTH es
            then nested_decs (adv::temps) (e::es)
                 (nested_seq (stores (Var adv) (MAP Var temps) 0w))
            else Skip
    | (_,_) => Skip) /\
  (compile_prog ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile_prog ctxt (Return rt) =
   let (ces,sh) = compile_exp ctxt rt in
   if size_of_shape sh = 0 then Return (Const 0w)
   else case ces of
         | [] => Skip
         | e::es => if size_of_shape sh = 1 then (Return e) else
          let temps = GENLIST (λx. ctxt.max_var + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH (e::es)
           then Seq (nested_decs temps (e::es)
                                 (nested_seq (store_globals 0w (MAP Var temps)))) (Return (Const 0w))
        else Skip) /\
  (compile_prog ctxt (Raise eid excp) =
    case FLOOKUP ctxt.eid_map eid of
    | SOME (esh,n) =>
      if size_of_shape esh = 0 then (Raise n)
      else
      let (ces,sh) = compile_exp ctxt excp;
          temps = GENLIST (λx. ctxt.max_var + SUC x) (size_of_shape sh) in
       if size_of_shape sh = LENGTH ces
       then Seq (nested_decs temps ces (nested_seq (store_globals 0w (MAP Var temps))))
                (Raise n)
       else Skip
    | NONE => Skip) /\
  (compile_prog ctxt (Seq p p') =
    Seq (compile_prog ctxt p) (compile_prog ctxt p')) /\
  (compile_prog ctxt (If e p p') =
   case compile_exp ctxt e of
    | (ce::ces, _) =>
      If ce (compile_prog ctxt p) (compile_prog ctxt p')
    | _ => Skip) /\
  (compile_prog ctxt (While e p) =
   case compile_exp ctxt e of
   | (ce::ces, _) =>
     While ce (compile_prog ctxt p)
   | _ => Skip) /\
  (compile_prog ctxt Break = Break) /\
  (compile_prog ctxt Continue = Continue) /\
  (compile_prog ctxt (Call rtyp e es) =
   let (cs, sh) = compile_exp ctxt e;
       cexps = MAP (compile_exp ctxt) es;
       args = FLAT (MAP FST cexps) in
    case cs of
    | ce::ces =>
     (case rtyp of
       | Tail => Call Tail ce args
       | Ret rt hdl =>
         (case FLOOKUP ctxt.var_nums rt of
          | SOME (One, n::ns) =>
            (case hdl of
              | NONE => Call (Ret (SOME n) Skip NONE) ce args
              | SOME (Handle eid evar p) =>
                (case FLOOKUP ctxt.eid_map eid of
                  | NONE => Call (Ret (SOME n) Skip NONE) ce args
                  | SOME (esh,neid) =>
                    let comp_hdl = compile_prog ctxt p;
                        hndlr = Seq (exp_hdl ctxt.var_nums evar) comp_hdl in
                    Call (Ret (SOME n) Skip (SOME (Handle neid hndlr))) ce args))
          | SOME (Comb sh, ns) =>
            (case hdl of
             | NONE => Call (Ret (ret_var sh ns) (ret_hdl sh ns) NONE) ce args
                       (* not same as Tail call *)
             | SOME (Handle eid evar p) =>
                (case FLOOKUP ctxt.eid_map eid of
                  | NONE => Call (Ret (ret_var sh ns) (ret_hdl sh ns) NONE) ce args
                  | SOME (esh,neid) =>
                    let comp_hdl = compile_prog ctxt p;
                        hndlr = Seq (exp_hdl ctxt.var_nums evar) comp_hdl in
                      Call (Ret (ret_var sh ns) (ret_hdl sh ns)
                              (SOME (Handle neid hndlr))) ce args))
          | _ =>
             (case hdl of
              | NONE => Call Tail ce args
              | SOME (Handle eid evar p) =>
                (case FLOOKUP ctxt.eid_map eid of
                   | NONE => Call Tail ce args
                   | SOME (esh,neid) =>
                     let comp_hdl = compile_prog ctxt p;
                        hndlr = Seq (exp_hdl ctxt.var_nums evar) comp_hdl in
                     Call (Ret NONE Skip (SOME (Handle neid hndlr))) ce args))))
    | [] => Skip) /\
  (compile_prog ctxt (ExtCall f ptr1 len1 ptr2 len2) =
   case (FLOOKUP ctxt.var_nums ptr1, FLOOKUP ctxt.var_nums len1,
         FLOOKUP ctxt.var_nums ptr2, FLOOKUP ctxt.var_nums len2) of
    | (SOME (One, pc::pcs), SOME (One, lc::lcs),
       SOME (One, pc'::pcs'), SOME (One, lc'::lcs')) => ExtCall f pc lc pc' lc'
    | _ => Skip) /\
  (compile_prog ctxt Tick = Tick)
End

val _ = export_theory();
