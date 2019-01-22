(*
  This compiler phase minimises the live-var annotations that are
  attached to MakeSpace, Assign and Call in dataLang programs. This
  phase also locally deletes code that has no observable effect.
*)
open preamble dataLangTheory;

val _ = new_theory "data_live";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val is_small_def = Define `is_small (arch_size:num) (n:num) = (n <= arch_size - 2)`

val is_pure_def = Define `
  (is_pure SetGlobalsPtr _ = F) /\
  (is_pure Ref _ = F) /\
  (is_pure (RefByte _) _ = F) /\
  (is_pure RefArray _ = F) /\
  (is_pure Update _ = F) /\
  (is_pure UpdateByte _ = F) /\
  (is_pure FromListByte _ = F) /\
  (is_pure (CopyByte _) _ = F) /\
  (is_pure (String _) _ = F) /\
  (is_pure (Cons _) _ = F) /\
  (is_pure (ConsExtend _) _ = F) /\
  (is_pure (FFI _) _ = F) /\
  (is_pure (FromList _) _ = F) /\
  (is_pure ListAppend _ = F) /\
  (is_pure (WordOp n _) arch_size = is_small arch_size n) /\
  (is_pure (WordShift n _ _) arch_size = is_small arch_size n) /\
  (is_pure (WordCmp n _) arch_size = is_small arch_size n) /\ (* WordCmp is pure for all sizes if integer comparisons are pure *)
  (is_pure (WordFromInt n) arch_size = is_small arch_size n) /\
  (is_pure (WordToInt n) arch_size = is_small arch_size n) /\
  (is_pure (WordToWord _ dest_size) arch_size = is_small arch_size dest_size) /\
  (is_pure Add _ = F) /\ (* TODO: these would be pure if space usage were not tracked *)
  (is_pure Sub _ = F) /\ (* which could be a switch in the semantics *)
  (is_pure Mult _ = F) /\
  (is_pure Div _ = F) /\
  (is_pure Mod _ = F) /\
  (is_pure Less _ = F) /\ (* TODO: are these really impure? *)
  (is_pure LessEq _ = F) /\
  (is_pure Equal _ = F) /\
  (is_pure Install _ = F) /\
  (is_pure (FP_uop _) _ = F) /\
  (is_pure (FP_bop _) _ = F) /\
  (is_pure ConfigGC _ = F) /\
  (is_pure _ _ = T)`

Theorem is_pure_pmatch `!op.
  is_pure op arch_size =
    case op of
      SetGlobalsPtr => F
    | Ref => F
    | RefByte _ => F
    | RefArray => F
    | Update => F
    | UpdateByte => F
    | FromListByte => F
    | CopyByte _ => F
    | String _ => F
    | Cons _ => F
    | ConsExtend _ => F
    | FFI _ => F
    | FromList _ => F
    | ListAppend => F
    (* TODO: mark small wordops/wordshifts/wordcmps/conversions as pure *)
    | WordOp n _ => is_small arch_size n 
    | WordShift n _ _ => is_small arch_size n
    | WordCmp n _ => is_small arch_size n
    | WordFromInt n => is_small arch_size n
    | WordToInt n => is_small arch_size n
    | WordToWord _ dest_size => is_small arch_size dest_size
    | Add => F
    | Sub => F
    | Mult => F
    | Div => F
    | Mod => F
    | Less => F
    | LessEq => F
    | Equal => F
    | Install => F
    | FP_uop _ => F
    | FP_bop _ => F
    | ConfigGC => F
    | _ => T`
  (rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[is_pure_def]);

val compile_def = Define `
  (compile Skip live _ = (Skip,live)) /\
  (compile (Return n) live _ = (Return n, insert n () LN)) /\
  (compile (Raise n) live _ = (Raise n, insert n () LN)) /\
  (compile (Move n1 n2) live _ =
    (Move n1 n2, insert n2 () (delete n1 live))) /\
  (compile (Seq c1 c2) live arch_size =
     let (d2,l2) = compile c2 live arch_size in
     let (d1,l1) = compile c1 l2 arch_size in
       (Seq d1 d2, l1)) /\
  (compile Tick live _ = (Tick,live)) /\
  (compile (MakeSpace k names) live _ =
     let l1 = inter names live in (MakeSpace k l1,l1)) /\
  (compile (Assign v op vs NONE) live arch_size =
     if IS_NONE (lookup v live) /\ is_pure op arch_size then (Skip,live) else
       let l1 = list_insert vs (delete v live) in
         (Assign v op vs NONE,l1)) /\
  (compile (Assign v op vs (SOME names)) live _ =
     let l1 = inter names (list_insert vs (delete v live)) in
       (Assign v op vs (SOME l1),l1)) /\
  (compile (If n c2 c3) live arch_size =
     let (d3,l3) = compile c3 live arch_size in
     let (d2,l2) = compile c2 live arch_size in
       (If n d2 d3, insert n () (union l2 l3))) /\
  (compile (Call NONE dest vs handler) live _ =
     (Call NONE dest vs handler,list_to_num_set vs)) /\
  (compile (Call (SOME (n,names)) dest vs NONE) live _ =
     let l1 = inter names (delete n live) in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs NONE,l2)) /\
  (compile (Call (SOME (n,names)) dest vs (SOME (v,c))) live arch_size =
     let (d,l3) = compile c live arch_size in
     let l0 = union (delete n live) (delete v l3) in
     let l1 = inter names l0 in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs (SOME (v,d)),l2))`;

val _ = export_theory();
