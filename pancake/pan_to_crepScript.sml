(*
  Compilation from panLang to crepLang.
*)
open preamble pan_commonTheory panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["pan_common", "panLang","crepLang", "backend_common"];

Datatype:
  context =
  <| vars  : panLang$varname |-> shape # num list;
     funcs : panLang$funname |-> (panLang$varname # shape) list;
     eids  : panLang$eid     |-> 'a word;
     vmax  : num|>
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
   case FLOOKUP ctxt.vars vname of
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

Definition exp_hdl_def:
  exp_hdl fm v =
  case FLOOKUP fm v of
  | NONE => Skip
  | SOME (vshp, ns) => nested_seq
      (MAP2 Assign ns (load_globals 0w (LENGTH ns)))
End

Definition ret_var_def:
  (ret_var One ns = oHD ns) /\
  (ret_var (Comb sh) ns =
     if size_of_shape (Comb sh) = 1 then oHD ns
     else NONE)
End

Definition ret_hdl_def:
   (ret_hdl One ns = Skip) /\
   (ret_hdl (Comb sh) ns =
     if 1 < size_of_shape (Comb sh) then (assign_ret ns)
     else Skip)
End

(* defining it with inner case to enable rewriting later *)
Definition wrap_rt_def:
  wrap_rt n =
    case n of
    | NONE => NONE
    | SOME (One, []) => NONE
    | m => m
End

Definition compile_def:
  (compile _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.vmax;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|vars := ctxt.vars |+ (v, (sh, nvars));
                            vmax := ctxt.vmax + size_of_shape sh|> in
            if size_of_shape sh = LENGTH es
            then nested_decs nvars es (compile nctxt p)
            else Skip) /\
  (compile ctxt (Assign v e) =
   let (es, sh) = compile_exp ctxt e in
   case FLOOKUP ctxt.vars v of
    | SOME (vshp, ns) =>
      if LENGTH ns = LENGTH es
      then if distinct_lists ns (FLAT (MAP var_cexp es))
      then nested_seq (MAP2 Assign ns es)
      else let vmax = ctxt.vmax;
               temps = GENLIST (λx. vmax + SUC x) (LENGTH ns) in
           nested_decs temps es
                       (nested_seq (MAP2 Assign ns (MAP Var temps)))
      else Skip:'a crepLang$prog
    | NONE => Skip) /\
  (compile ctxt (Store ad v) =
   case compile_exp ctxt ad of
    | (e::es',sh') =>
       let (es,sh) = compile_exp ctxt v;
            adv = ctxt.vmax + 1;
            temps = GENLIST (λx. adv + SUC x) (size_of_shape sh) in
            if size_of_shape sh = LENGTH es
            then nested_decs (adv::temps) (e::es)
                 (nested_seq (stores (Var adv) (MAP Var temps) 0w))
            else Skip
    | (_,_) => Skip) /\
  (compile ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile ctxt (Return rt) =
   let (ces,sh) = compile_exp ctxt rt in
   if size_of_shape sh = 0 then Return (Const 0w)
   else case ces of
         | [] => Skip
         | e::es => if size_of_shape sh = 1 then (Return e) else
          let temps = GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH (e::es)
           then Seq (nested_decs temps (e::es)
                                 (nested_seq (store_globals 0w (MAP Var temps)))) (Return (Const 0w))
        else Skip) /\
  (compile ctxt (Raise eid excp) =
    case FLOOKUP ctxt.eids eid of
    | SOME n =>
      let (ces,sh) = compile_exp ctxt excp;
          temps = GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape sh) in
       if size_of_shape sh = LENGTH ces
       then Seq (nested_decs temps ces (nested_seq (store_globals 0w (MAP Var temps))))
                (Raise n)
       else Skip
    | NONE => Skip) /\
  (compile ctxt (Seq p p') =
    Seq (compile ctxt p) (compile ctxt p')) /\
  (compile ctxt (If e p p') =
   case compile_exp ctxt e of
    | (ce::ces, _) =>
      If ce (compile ctxt p) (compile ctxt p')
    | _ => Skip) /\
  (compile ctxt (While e p) =
   case compile_exp ctxt e of
   | (ce::ces, _) =>
     While ce (compile ctxt p)
   | _ => Skip) /\
  (compile ctxt Break = Break) /\
  (compile ctxt Continue = Continue) /\
  (compile ctxt (Call rtyp e es) =
   let (cs, sh) = compile_exp ctxt e;
       cexps = MAP (compile_exp ctxt) es;
       args = FLAT (MAP FST cexps) in
    case cs of
    | ce::ces =>
     (case rtyp of
       | Tail => Call Tail ce args
       | Ret rt hdl =>
         (case wrap_rt (FLOOKUP ctxt.vars rt) of
          | NONE =>
            (case hdl of
              | NONE => Call Tail ce args
              | SOME (Handle eid evar p) =>
                (case FLOOKUP ctxt.eids eid of
                   | NONE => Call Tail ce args
                   | SOME neid =>
                     let comp_hdl = compile ctxt p;
                        hndlr = Seq (exp_hdl ctxt.vars evar) comp_hdl in
                     Call (Ret NONE Skip (SOME (Handle neid hndlr))) ce args))
          | SOME (sh, ns) =>
            (case hdl of
             | NONE => Call (Ret (ret_var sh ns) (ret_hdl sh ns) NONE) ce args
             | SOME (Handle eid evar p) =>
                (case FLOOKUP ctxt.eids eid of
                  | NONE => Call (Ret (ret_var sh ns) (ret_hdl sh ns) NONE) ce args
                  | SOME neid =>
                    let comp_hdl = compile ctxt p;
                        hndlr = Seq (exp_hdl ctxt.vars evar) comp_hdl in
                      Call (Ret (ret_var sh ns) (ret_hdl sh ns)
                              (SOME (Handle neid hndlr))) ce args))))
    | [] => Skip) /\
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
   case (FLOOKUP ctxt.vars ptr1, FLOOKUP ctxt.vars len1,
         FLOOKUP ctxt.vars ptr2, FLOOKUP ctxt.vars len2) of
    | (SOME (One, pc::pcs), SOME (One, lc::lcs),
       SOME (One, pc'::pcs'), SOME (One, lc'::lcs')) => ExtCall f pc lc pc' lc'
    | _ => Skip) /\
  (compile ctxt Tick = Tick)
End


Definition mk_ctxt_def:
  mk_ctxt vmap fs m (es:panLang$eid |-> 'a word) =
     <|vars  := vmap;
       funcs := fs;
       eids  := es;
       vmax  := m|>
End

(*
Definition shape_vars_def:
  (shape_vars [] ns = []) ∧
  (shape_vars (sh::shs) ns = (sh, TAKE (size_of_shape sh) ns) ::
                              shape_vars shs (DROP (size_of_shape sh) ns))
End
*)

(* params : (varname # shape) list *)
Definition make_vmap_def:
  make_vmap params =
   let pvars  = MAP FST params;
       shs = MAP SND params;
       ns  = GENLIST I (size_of_shape (Comb shs));
       (* defining in this way to make proof in sync with "with_shape" *)
       cvars = ZIP (shs, with_shape shs ns) in
    FEMPTY |++ ZIP (pvars, cvars)
End

Definition comp_func_def:
  comp_func fs eids params body =
    let vmap   = make_vmap params;
        shapes = MAP SND params;
        vmax = size_of_shape (Comb shapes) - 1 in
    compile (mk_ctxt vmap fs vmax eids) body
End

Definition get_eids_def:
  get_eids prog =
   let eids = remove_dup (FLAT (MAP (exp_ids o SND o SND) prog));
       ns   = GENLIST (λx. n2w x) (LENGTH eids);
       es   = MAP2 (λx y. (x,y)) eids ns in
    alist_to_fmap es
End


Definition make_funcs_def:
  make_funcs prog =
  let fnames = MAP FST prog;
      params = MAP (FST o SND) prog;
      fs = MAP2 (λx y. (x,y)) fnames params in
    alist_to_fmap fs
End


Definition crep_vars_def:
  crep_vars params =
  let shapes = MAP SND params;
      len    = size_of_shape (Comb shapes) in
      GENLIST I len
End


Definition compile_prog_def:
  compile_prog prog =
  let comp = comp_func (make_funcs prog) (get_eids prog) in
    MAP (λ(name, params, body).
          (name,
           crep_vars params,
           comp params body)) prog
End

val _ = export_theory();
