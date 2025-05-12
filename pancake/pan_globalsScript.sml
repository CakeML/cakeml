(*
  Allocate globals at the end of heap.
*)

open preamble panLangTheory

val _ = new_theory "pan_globals"

val _ = set_grammar_ancestry ["panLang","backend_common"];

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Datatype:
  context =
  <| globals  : varname |-> shape # 'a word # 'a exp;
     globals_size : 'a word
   |>
End

Definition compile_exp_def:
  (compile_exp ctxt (Var Local vname) = Var Local vname) ∧
  (compile_exp ctxt (Var Global vname) =
   case FLOOKUP ctxt.globals vname of
     NONE => Const 0w (* should never happen *)
   | SOME(sh,addr,_) => Load sh (Op Sub [TopAddr; Const addr])) ∧
  (compile_exp ctxt (Struct es) = Struct (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Field index e) =
   Field index (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Load sh e) =
   Load sh (compile_exp ctxt e)) ∧
  (compile_exp ctxt (LoadByte e) =
   LoadByte (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Op bop es) =
   Op bop (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Panop pop es) =
   Panop pop (MAP (compile_exp ctxt) es)) ∧
  (compile_exp ctxt (Cmp cmp e e') =
   Cmp cmp (compile_exp ctxt e) (compile_exp ctxt e')) ∧
  (compile_exp ctxt (Shift sh e n) =
   Shift sh (compile_exp ctxt e) n) ∧
  (compile_exp ctxt TopAddr = Op Sub [TopAddr; Const ctxt.globals_size]) ∧
  (compile_exp ctxt e = e)
Termination
  wf_rel_tac `measure (\e. panLang$exp_size ARB (SND e))` >>
  rpt strip_tac >>
  imp_res_tac panLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition compile_def:
  (compile ctxt (Dec v e p) =
   Dec v (compile_exp ctxt e) (compile ctxt p)) /\
  (compile ctxt (Assign Local v e) =
   Assign Local v (compile_exp ctxt e)) ∧
  (compile ctxt (Assign Global v e) =
   case FLOOKUP ctxt.globals v of
     NONE => Skip (* shouldn't happen *)
   | SOME (sh, addr, _) => Store (Op Sub [TopAddr; Const addr]) (compile_exp ctxt e)
   ) ∧
  (compile ctxt (Store ad v) =
   Store (compile_exp ctxt ad) (compile_exp ctxt v)) /\
  (compile ctxt (StoreByte dest src) =
   StoreByte (compile_exp ctxt dest) (compile_exp ctxt src)) /\
  (compile ctxt (Return rt) =
   Return (compile_exp ctxt rt)) /\
  (compile ctxt (Raise eid excp) =
   Raise eid (compile_exp ctxt excp)) /\
  (compile ctxt (Seq p p') =
   Seq (compile ctxt p) (compile ctxt p')) /\
  (compile ctxt (If e p p') =
   If (compile_exp ctxt e) (compile ctxt p) (compile ctxt p')) /\
  (compile ctxt (While e p) =
   While (compile_exp ctxt e) (compile ctxt p)) /\
  (compile ctxt (Call rtyp e es) =
   let cexps = MAP (compile_exp ctxt) es in
     Call (case rtyp of
           | NONE => NONE
           | SOME (tl, hdl) =>
               SOME (tl,
                     case hdl of
                     | NONE => NONE
                     | SOME (eid, evar, p) =>
                         SOME (eid, evar, compile ctxt p)))
          e
          cexps) /\
  (compile ctxt (DecCall v s e es p) =
   DecCall v s e (MAP (compile_exp ctxt) es) (compile ctxt p)) /\
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
   ExtCall f
           (compile_exp ctxt ptr1)
           (compile_exp ctxt len1)
           (compile_exp ctxt ptr2)
           (compile_exp ctxt len2)) /\
  (compile ctxt (ShMemStore op r ad) =
   ShMemStore op (compile_exp ctxt r) (compile_exp ctxt ad)) ∧
  (compile ctxt (ShMemLoad op Local r ad) =
   ShMemLoad op Local r (compile_exp ctxt ad)) ∧
  (compile _ p = p)
End

Definition compile_decs_def:
    compile_decs ctxt [] = ([],[]) ∧
    (compile_decs ctxt (Decl sh v e::ds) =
     let
       s = ctxt.globals_size + n2w(size_of_shape sh);
       ctxt' = ctxt with <|globals  := ctxt.globals |+ (v,sh,s);
                           globals_size := s|>;
       (decs,funs) = compile_decs ctxt' ds
     in
        (Store (Op Sub [TopAddr; Const s]) (compile_exp ctxt e)::decs,funs)) ∧
    (compile_decs ctxt (Function f xp args body::ds) =
     let (decs,funs) = compile_decs ctxt ds
     in (decs,Function f xp args (compile ctxt body)::funs))
End

Definition resort_decls_def:
  resort_decls decs =
  FILTER ($¬ o is_function) decs ++ FILTER is_function decs
End

(* TODO: alpha-conversion *)
Definition compile_top_def:
  compile_top decs start =
  case ALOOKUP (functions decs) start of
    NONE => []
  | SOME (args, body) =>
      let nds = resort_decls decs;
          (decls,funs) = compile_decs <| globals := FEMPTY; globals_size := 0w |> nds;
          params = MAP (Var Local o FST) args;
          new_main = Function start
                              F
                              args
                              (Seq (nested_seq decls) (TailCall start params))
      in
        new_main::funs
End

val _ = export_theory();
