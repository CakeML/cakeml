(*
  This dataLang phase lumps together MakeSpace operations. Each
  MakeSpace operations corresponds to a memory allocation in the later
  wordLang code. By lumping together MakeSpace operations we turn
  several calls to the memory allocator into a single efficient call.
*)
open preamble dataLangTheory;

val _ = new_theory "data_space";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition num_size_def:
  num_size (n:num) =
    if n < 2**32 then 2:num else 1 + num_size (n DIV 2 ** 32)
End

Definition part_space_req_def:
  part_space_req (W64 s) = 3 ∧
  part_space_req (Int i) =
    (if Num (ABS i) < 2**29 then 0 else num_size (Num (ABS i))) ∧
  part_space_req (Str s) = strlen s DIV 4 + 2 ∧
  part_space_req (Con t ns) =
    let l = LENGTH ns in if l = 0n then 0 else l+1
End

Definition op_space_req_def:
  (op_space_req (MemOp Ref) l = l + 1) /\
  (op_space_req (BlockOp (Cons _)) l = if l = 0n then 0 else l+1) /\
  (op_space_req (BlockOp (Build parts)) l = SUM (MAP part_space_req parts)) /\
  (op_space_req (WordOp (WordOpw W64 _)) _ = 3) /\
  (op_space_req (WordOp (WordShift W64 _ _)) _ = 3) /\
  (op_space_req (WordOp WordFromInt) _ = 3) /\
  (op_space_req (WordOp WordToInt) _ = 3) /\
  (op_space_req (WordOp (WordFromWord F)) _ = 3) /\
  (op_space_req (WordOp (FP_uop _)) _ = 3) /\
  (op_space_req (WordOp (FP_bop _)) _ = 3) /\
  (op_space_req (WordOp (FP_top _)) _ = 3) /\
  (op_space_req _ _ = 0)
End

(*
Theorem op_space_req_pmatch:
  !op l.
  op_space_req op l =
    case op of
      Cons _ => if l = 0n then 0 else l+1
    | Ref => l + 1
    | WordOp (WordOpw W64 _) => 3
    | WordShift W64 _ _ => 3
    | WordFromInt => 3
    | WordToInt => 3
    | WordFromWord b => (if b then 0 else 3)
    | FP_uop _ => 3
    | FP_bop _ => 3
    | _ => 0
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[op_space_req_def]
QED
*)

Definition pMakeSpace_def:
  (pMakeSpace (INL c) = c) /\
  (pMakeSpace (INR (k,names,c)) = Seq (MakeSpace k names) c)
End

Definition space_def:
  (space (MakeSpace k names) = INR (k,names,Skip)) /\
  (space (Seq c1 c2) =
     let d1 = pMakeSpace (space c1) in
     let x2 = space c2 in
       dtcase x2 of
       | INL c4 =>
          (dtcase c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k2,names2,c4) =>
          (dtcase c1 of
           | Skip => INR (k2,names2,c4)
           | MakeSpace k1 names1 => INR (k2,inter names1 names2,c4)
           | Move dest src =>
               INR (k2,insert src () (delete dest names2),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (op_space_req op (LENGTH args) + k2,
                    list_insert args (delete dest names2),
                    Seq (Assign dest op args NONE) c4)
           | _ => INL (Seq d1 (pMakeSpace x2)))) /\
  (space (If n c2 c3) =
     INL (If n (pMakeSpace (space c2)) (pMakeSpace (space c3)))) /\
  (space c = INL c)
End

Theorem space_pmatch:
  ∀c.
  space c =
    case c of
    | MakeSpace k names => INR (k,names,Skip)
    | Seq c1 c2 => (
     let d1 = pMakeSpace (space c1) in
     let x2 = space c2 in
       case x2 of
       | INL c4 =>
          (case c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k2,names2,c4) =>
          (case c1 of
           | Skip => INR (k2,names2,c4)
           | MakeSpace k1 names1 => INR (k2,inter names1 names2,c4)
           | Move dest src =>
               INR (k2,insert src () (delete dest names2),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (op_space_req op (LENGTH args) + k2,
                    list_insert args (delete dest names2),
                    Seq (Assign dest op args NONE) c4)
           | _ => INL (Seq d1 (pMakeSpace x2))))
    | If n c2 c3 =>
      INL (If n (pMakeSpace (space c2)) (pMakeSpace (space c3)))
    | c => INL c
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> TRY(PURE_REWRITE_TAC [LET_DEF] >> BETA_TAC))
  >> fs[space_def]
QED

Definition compile_def:
  compile c = pMakeSpace (space c)
End

val _ = export_theory();
