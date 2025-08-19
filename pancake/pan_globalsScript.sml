(*
  Allocate globals at the end of heap.
*)

open preamble panLangTheory byteTheory

val _ = new_theory "pan_globals"

val _ = set_grammar_ancestry ["panLang","backend_common","byte"];

Datatype:
  context =
  <| globals  : varname |-> shape # 'a word;
     globals_size : 'a word;
     max_globals_size : 'a word
   |>
End

Definition compile_exp_def:
  (compile_exp ctxt (Var Local vname) = Var Local vname) ∧
  (compile_exp ctxt (Var Global vname) =
   case FLOOKUP ctxt.globals vname of
     NONE => Const 0w (* should never happen *)
   | SOME(sh,addr) => Load sh (Op Sub [TopAddr; Const addr])) ∧
  (compile_exp ctxt (Struct es) = Struct (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Field index e) =
   Field index (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Load sh e) =
   Load sh (compile_exp ctxt e)) ∧
  (compile_exp ctxt (LoadByte e) =
   LoadByte (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Load32 e) =
   Load32 (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Op bop es) =
   Op bop (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Panop pop es) =
   Panop pop (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Cmp cmp e e') =
   Cmp cmp (compile_exp ctxt e) (compile_exp ctxt e')) ∧
  (compile_exp ctxt (Shift sh e n) =
   Shift sh (compile_exp ctxt e) n) ∧
  (compile_exp ctxt TopAddr = Op Sub [TopAddr; Const ctxt.max_globals_size]) ∧
  (compile_exp ctxt e = e)
Termination
  wf_rel_tac `measure (\e. panLang$exp_size ARB (SND e))` >>
  rpt strip_tac >>
  imp_res_tac panLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition fresh_name_def:
  fresh_name name names =
  if MEM name names then
    fresh_name (strcat name «'») names
  else
    name
Termination
  qexists ‘measure $ λ(name,names). 1 + MAX_SET(IMAGE strlen (set names)) - strlen name’ >>
  rw[] >>
  ‘strlen name <= MAX_SET (IMAGE strlen (set names))’
    by(irule MAX_SET_PROPERTY >> rw[]) >>
  simp[]
End

Definition shape_val_def:
  shape_val One = Const 0w ∧
  shape_val (Comb shapes) = Struct (shape_vals shapes) ∧
  shape_vals [] = [] ∧
  shape_vals (sh::shs) = shape_val sh :: shape_vals shs
End

Definition compile_def:
  (compile ctxt (Dec v e p) =
   Dec v (compile_exp ctxt e) (compile ctxt p)) ∧
  (compile ctxt (Assign Local v e) =
   Assign Local v (compile_exp ctxt e)) ∧
  (compile ctxt (Assign Global v e) =
   case FLOOKUP ctxt.globals v of
     NONE => Skip (* shouldn't happen *)
   | SOME (sh, addr) => Store (Op Sub [TopAddr; Const addr]) (compile_exp ctxt e)
   ) ∧
  (compile ctxt (Store ad v) =
   Store (compile_exp ctxt ad) (compile_exp ctxt v)) ∧
  (compile ctxt (Store32 ad v) =
   Store32 (compile_exp ctxt ad) (compile_exp ctxt v)) ∧
  (compile ctxt (StoreByte dest src) =
   StoreByte (compile_exp ctxt dest) (compile_exp ctxt src)) ∧
  (compile ctxt (Return rt) =
   Return (compile_exp ctxt rt)) ∧
  (compile ctxt (Raise eid excp) =
   Raise eid (compile_exp ctxt excp)) ∧
  (compile ctxt (Seq p p') =
   Seq (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (If e p p') =
   If (compile_exp ctxt e) (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (While e p) =
   While (compile_exp ctxt e) (compile ctxt p)) ∧
  (compile ctxt (Call rtyp e es) =
   let cexps = MAP (compile_exp ctxt) es in
     case rtyp of
       NONE => Call NONE e cexps
     | SOME (SOME(Global,vn), hdl) =>
         (case FLOOKUP ctxt.globals vn of
           NONE => (* ...should never happen, but needs to preserve timeouts *)
             Call (SOME (NONE,
                         case hdl of
                         | NONE => NONE
                         | SOME (eid, evar, p) =>
                             SOME (eid, evar, compile ctxt p)))
                  e
                  cexps
         | SOME (sh,addr) =>
             (case hdl of
                NONE =>
                  DecCall «» sh e cexps $ Store (Op Sub [TopAddr; Const addr]) (Var Local «»)
              | SOME (eid, evar, p) =>
                  let
                    p' = compile ctxt p;
                    names = evar::free_var_ids p' ++ FLAT(MAP var_exp cexps);
                    vn'  = fresh_name «» names;
                    flag = fresh_name «vn'» (vn'::names)
                  in
                    Dec vn' (shape_val sh) $ Dec flag (Const 0w) $
                        Seq (Call (SOME (SOME(Local,vn'), SOME(eid, evar, Seq p' (Assign Local flag (Const 1w))))) e cexps) $
                        If (Var Local flag) Skip $
                        Store (Op Sub [TopAddr; Const addr]) (Var Local vn')
             )
         )
     | SOME (tl, hdl) =>
         Call (SOME (tl,
                     case hdl of
                     | NONE => NONE
                     | SOME (eid, evar, p) =>
                         SOME (eid, evar, compile ctxt p)))
              e
              cexps) ∧
  (compile ctxt (DecCall v s e es p) =
   DecCall v s e (MAP (compile_exp ctxt) es) (compile ctxt p)) ∧
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
   ExtCall f
           (compile_exp ctxt ptr1)
           (compile_exp ctxt len1)
           (compile_exp ctxt ptr2)
           (compile_exp ctxt len2)) ∧
  (compile ctxt (ShMemStore op r ad) =
   ShMemStore op (compile_exp ctxt r) (compile_exp ctxt ad)) ∧
  (compile ctxt (ShMemLoad op Local r ad) =
   ShMemLoad op Local r (compile_exp ctxt ad)) ∧
  (compile ctxt (ShMemLoad op Global r ad) =
   case FLOOKUP ctxt.globals r of
   | SOME (One, addr) =>
       (let r' = strcat r «'» in
          Dec r (compile_exp ctxt ad) $
              Dec r' (Const 0w) $
              Seq (ShMemLoad op Local r' (Var Local r)) $
              Store (Op Sub [TopAddr; Const addr]) (Var Local r'))
   | _ => Skip (* Should never happen *)) ∧
  (compile _ p = p)
End

Definition compile_decs_def:
    compile_decs ctxt [] = ([],[],ctxt) ∧
    (compile_decs ctxt (Decl sh v e::ds) =
     let
       s = ctxt.globals_size + bytes_in_word*n2w(size_of_shape sh);
       ctxt' = ctxt with <|globals  := ctxt.globals |+ (v,sh,s);
                           globals_size := s|>;
       (decs,funs,ctxt'') = compile_decs ctxt' ds
     in
        (Store (Op Sub [TopAddr; Const s]) (compile_exp ctxt e)::decs,funs,ctxt'')) ∧
    (compile_decs ctxt (Function fi::ds) =
     let (decs,funs,ctxt'') = compile_decs ctxt ds
     in (decs,Function (fi with body := compile ctxt fi.body)::funs,ctxt''))
End

Definition resort_decls_def:
  resort_decls decs =
  FILTER ($¬ o is_function) decs ++ FILTER is_function decs
End

Definition fperm_name_def:
  fperm_name f g h =
  if f = h then g
  else if g = h then f
  else h
End

Definition fperm_def:
  (fperm f g (Dec v e p) =
   Dec v e (fperm f g p)) ∧
  (fperm f g (Seq p p') =
   Seq (fperm f g p) (fperm f g p')) ∧
  (fperm f g (If e p p') =
   If e (fperm f g p) (fperm f g p')) ∧
  (fperm f g (While e p) =
   While e (fperm f g p)) ∧
  (fperm f g (Call rtyp e es) =
   Call (case rtyp of
         | NONE => NONE
         | SOME (tl, hdl) =>
             SOME (tl,
                   case hdl of
                   | NONE => NONE
                   | SOME (eid, evar, p) =>
                       SOME (eid, evar, fperm f g p)))
        (fperm_name f g e)
        es) ∧
  (fperm f g (DecCall v s e es p) =
   DecCall v s (fperm_name f g e) es (fperm f g p)) ∧
  (fperm _ _ p = p)
End

Definition fperm_decs_def:
  (fperm_decs f g [] = []) ∧
  (fperm_decs f g (Function fi::decs) =
   Function (fi with <| name := fperm_name f g fi.name; body := (fperm f g fi.body)|>)
            ::fperm_decs f g decs) ∧
  (fperm_decs f g (d::decs) = d::fperm_decs f g decs)
End

Definition new_main_name_def:
  new_main_name decls = fresh_name «main» (MAP FST (functions decls))
End

Definition dec_shapes_def:
  dec_shapes(Function _::ds) = dec_shapes ds ∧
  dec_shapes(Decl sh _ _::ds) = sh::dec_shapes ds ∧
  dec_shapes [] = []
End

Definition compile_top_def:
  compile_top decs start =
  case ALOOKUP (functions decs) start of
    NONE => []
  | SOME (args, body) =>
      let nds = resort_decls decs;
          start' = new_main_name decs;
          nds' = fperm_decs start start' nds;
          (decls,funs,ctxt) = compile_decs
                              <| globals := FEMPTY; globals_size := 0w;
                                 max_globals_size := bytes_in_word*n2w(SUM(MAP size_of_shape(dec_shapes nds')))
                              |> nds';
          params = MAP (Var Local o FST) args;
          new_main = Function <| name   := start
                               ;  export := F
                               ;  params := args
                               ;  body := Seq (nested_seq decls) (TailCall start' params)
                              |>
      in
        new_main::funs
End

val _ = export_theory();
