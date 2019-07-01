(*
  This compiler phase minimises the live-var annotations that are
  attached to MakeSpace, Assign and Call in dataLang programs. This
  phase also locally deletes code that has no observable effect.
*)
open preamble dataLangTheory;

val _ = new_theory "data_live";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val is_pure_def = Define `
  (is_pure SetGlobalsPtr = F) /\
  (is_pure Ref = F) /\
  (is_pure (RefByte _) = F) /\
  (is_pure RefArray = F) /\
  (is_pure Update = F) /\
  (is_pure UpdateByte = F) /\
  (is_pure FromListByte = F) /\
  (is_pure (CopyByte _) = F) /\
  (is_pure (String _) = F) /\
  (is_pure (Cons _) = F) /\
  (is_pure (ConsExtend _) = F) /\
  (is_pure (FFI _) = F) /\
  (is_pure (FromList _) = F) /\
  (is_pure ListAppend = F) /\
  (is_pure Add = F) /\ (* TODO: these would be pure if space usage were not tracked *)
  (is_pure Sub = F) /\ (* which could be a switch in the semantics *)
  (is_pure Mult = F) /\
  (is_pure Div = F) /\
  (is_pure Mod = F) /\
  (is_pure Less = F) /\ (* TODO: are these really impure? *)
  (is_pure LessEq = F) /\
  (is_pure Equal = F) /\
  (is_pure (WordOp W64 _) = F) /\
  (is_pure (WordShift W64 _ _) = F) /\
  (is_pure WordFromInt = F) /\
  (is_pure WordToInt = F) /\
  (is_pure Install = F) /\
  (is_pure (WordFromWord b) = F) /\
  (is_pure (FP_uop _) = F) /\
  (is_pure (FP_bop _) = F) /\
  (is_pure (FP_top _) = F) /\
  (is_pure ConfigGC = F) /\
  (is_pure _ = T)`

Theorem is_pure_pmatch:
  !op.
  is_pure op =
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
    | Add => F
    | Sub => F
    | Mult => F
    | Div => F
    | Mod => F
    | Less => F
    | LessEq => F
    | Equal => F
    | WordOp W64 _ => F
    | WordShift W64 _ _ => F
    | WordFromInt => F
    | WordToInt => F
    | Install => F
    | WordFromWord b => F
    | FP_uop _ => F
    | FP_bop _ => F
    | FP_top _ => F
    | ConfigGC => F
    | _ => T
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[is_pure_def]
QED

val compile_def = Define `
  (compile Skip live = (Skip,live)) /\
  (compile (Return n) live = (Return n, insert n () LN)) /\
  (compile (Raise n) live = (Raise n, insert n () LN)) /\
  (compile (Move n1 n2) live =
    (Move n1 n2, insert n2 () (delete n1 live))) /\
  (compile (Seq c1 c2) live =
     let (d2,l2) = compile c2 live in
     let (d1,l1) = compile c1 l2 in
       (Seq d1 d2, l1)) /\
  (compile Tick live = (Tick,live)) /\
  (compile (MakeSpace k names) live =
     let l1 = inter names live in (MakeSpace k l1,l1)) /\
  (compile (Assign v op vs NONE) live =
     if IS_NONE (lookup v live) /\ is_pure op then (Skip,live) else
       let l1 = list_insert vs (delete v live) in
         (Assign v op vs NONE,l1)) /\
  (compile (Assign v op vs (SOME names)) live =
     let l1 = inter names (list_insert vs (delete v live)) in
       (Assign v op vs (SOME l1),l1)) /\
  (compile (If n c2 c3) live =
     let (d3,l3) = compile c3 live in
     let (d2,l2) = compile c2 live in
       (If n d2 d3, insert n () (union l2 l3))) /\
  (compile (Call NONE dest vs handler) live =
     (Call NONE dest vs handler,list_to_num_set vs)) /\
  (compile (Call (SOME (n,names)) dest vs NONE) live =
     let l1 = inter names (delete n live) in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs NONE,l2)) /\
  (compile (Call (SOME (n,names)) dest vs (SOME (v,c))) live =
     let (d,l3) = compile c live in
     let l0 = union (delete n live) (delete v l3) in
     let l1 = inter names l0 in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs (SOME (v,d)),l2))`;

val _ = export_theory();
