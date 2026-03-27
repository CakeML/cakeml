(*
  This compiler phase minimises the live-var annotations that are
  attached to MakeSpace, Assign and Call in dataLang programs. This
  phase also locally deletes code that has no observable effect.
*)
Theory data_live
Ancestors
  dataLang
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

Definition is_pure_def:
  (is_pure (FFI _) = F) /\
  (is_pure (IntOp Add) = F) /\ (* TODO: these would be pure if space usage were not tracked *)
  (is_pure (IntOp Sub) = F) /\ (* which could be a switch in the semantics *)
  (is_pure (IntOp Mult) = F) /\
  (is_pure (IntOp Div) = F) /\
  (is_pure (IntOp Mod) = F) /\
  (is_pure (IntOp Less) = F) /\ (* TODO: are these really impure? *)
  (is_pure (IntOp LessEq) = F) /\
  (is_pure (WordOp (WordOpw W64 _)) = F) /\
  (is_pure (WordOp (WordShift W64 _ _)) = F) /\
  (is_pure (WordOp WordFromInt) = F) /\
  (is_pure (WordOp WordToInt) = F) /\
  (is_pure (WordOp (WordFromWord b)) = F) /\
  (is_pure (WordOp (FP_uop _)) = F) /\
  (is_pure (WordOp (FP_bop _)) = F) /\
  (is_pure (WordOp (FP_top _)) = F) /\
  (is_pure (BlockOp (Build _)) = F) /\
  (is_pure (BlockOp (Cons _)) = F) /\
  (is_pure (BlockOp (ConsExtend _)) = F) /\
  (is_pure (BlockOp (FromList _)) = F) /\
  (is_pure (BlockOp ListAppend) = F) /\
  (is_pure (BlockOp Equal) = F) /\
  (is_pure (GlobOp (SetGlobal _)) = F) /\
  (is_pure (GlobOp SetGlobalsPtr) = F) /\
  (is_pure (MemOp Ref) = F) /\
  (is_pure (MemOp (RefByte _)) = F) /\
  (is_pure (MemOp RefArray) = F) /\
  (is_pure (MemOp Update) = F) /\
  (is_pure (MemOp UpdateByte) = F) /\
  (is_pure (MemOp FromListByte) = F) /\
  (is_pure (MemOp (CopyByte _)) = F) /\
  (is_pure (MemOp XorByte) = F) /\
  (is_pure (MemOp ConfigGC) = F) /\
  (is_pure Install = F) /\
  (is_pure (ThunkOp _) = F) /\
  (is_pure _ = T)
End

Theorem is_pure_pmatch:
  !op.
  is_pure op =
    pmatch op of
    | FFI _ => F
    | GlobOp (SetGlobal _) => F
    | GlobOp SetGlobalsPtr => F
    | WordOp (WordOpw W64 _) => F
    | WordOp (WordShift W64 _ _) => F
    | WordOp WordFromInt => F
    | WordOp WordToInt => F
    | WordOp (WordFromWord b) => F
    | WordOp (FP_uop _) => F
    | WordOp (FP_bop _) => F
    | WordOp (FP_top _) => F
    | BlockOp (Build _) => F
    | BlockOp (Cons _) => F
    | BlockOp (ConsExtend _) => F
    | BlockOp (FromList _) => F
    | BlockOp ListAppend => F
    | BlockOp Equal => F
    | MemOp Ref => F
    | MemOp (RefByte _) => F
    | MemOp RefArray => F
    | MemOp Update => F
    | MemOp UpdateByte => F
    | MemOp FromListByte => F
    | MemOp (CopyByte _) => F
    | MemOp XorByte => F
    | IntOp Add => F
    | IntOp Sub => F
    | IntOp Mult => F
    | IntOp Div => F
    | IntOp Mod => F
    | IntOp Less => F
    | IntOp LessEq => F
    | Install => F
    | MemOp ConfigGC => F
    | ThunkOp _ => F
    | _ => T
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[is_pure_def]
QED

Definition compile_def:
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
  (compile (Force NONE loc src) live =
     (Force NONE loc src,insert src () LN)) /\
  (compile (Force (SOME (n,names)) loc src) live =
     let l1 = inter names (delete n live) in
     let l2 = insert src () l1 in
       (Force (SOME (n,l1)) loc src,l2)) /\
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
       (Call (SOME (n,l1)) dest vs (SOME (v,d)),l2))
End

