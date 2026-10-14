(*
  This compiler phase performs lightweight optimisations on wordLang
  programs. It is in particular designed to clean up some awkward
  patterns that can be produced by the data_to_word compiler.
*)
Theory word_simp
Ancestors
  wordLang asm sptree int_bitwise
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

(* function that makes all Seq associate to the left *)

Definition SmartSeq_def:
  SmartSeq p1 (p2:wordLang$prog) =
    if p1 = Skip then p2 else Seq p1 p2
End

Definition Seq_assoc_def:
  (Seq_assoc p1 Skip = p1) /\
  (Seq_assoc p1 (Seq q1 q2) = Seq_assoc (Seq_assoc p1 q1) q2) /\
  (Seq_assoc p1 (If v n r q1 q2) =
     SmartSeq p1 (If v n r (Seq_assoc Skip q1) (Seq_assoc Skip q2))) /\
  (Seq_assoc p1 (MustTerminate q) =
     SmartSeq p1 (MustTerminate (Seq_assoc Skip q))) /\
  (Seq_assoc p1 (Call ret_prog dest args handler) =
     SmartSeq p1 (Call (case ret_prog of
           | NONE => NONE
           | SOME (x1,x2,q1,x3,x4) => SOME (x1,x2,Seq_assoc Skip q1,x3,x4))
       dest args
          (case handler of
           | NONE => NONE
           | SOME (y1,q2,y2,y3) => SOME (y1,Seq_assoc Skip q2,y2,y3)))) /\
  (Seq_assoc p1 (Loop names body exit_names) =
     SmartSeq p1 (Loop names (Seq_assoc Skip body) exit_names)) /\
  (Seq_assoc p1 other = SmartSeq p1 other)
End

Theorem Seq_assoc_pmatch:
  !p1 prog.
  Seq_assoc p1 prog =
  pmatch prog of
  | Skip => p1
  | (Seq q1 q2) => Seq_assoc (Seq_assoc p1 q1) q2
  | (If v n r q1 q2) =>
     SmartSeq p1 (If v n r (Seq_assoc Skip q1) (Seq_assoc Skip q2))
  | (MustTerminate q) =>
     SmartSeq p1 (MustTerminate (Seq_assoc Skip q))
  | (Call ret_prog dest args handler) =>
     SmartSeq p1 (Call (case ret_prog of
           | NONE => NONE
           | SOME (x1,x2,q1,x3,x4) => SOME (x1,x2,Seq_assoc Skip q1,x3,x4))
       dest args
          (case handler of
           | NONE => NONE
           | SOME (y1,q2,y2,y3) => SOME (y1,Seq_assoc Skip q2,y2,y3)))
  | (Loop names body exit_names) =>
     SmartSeq p1 (Loop names (Seq_assoc Skip body) exit_names)
  | other => SmartSeq p1 other
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac
  >> fs[Seq_assoc_def]
QED

(* optimise certain consequtive If statements that arise from data-to-word

   If something (q1 ; n := X) (q2 ; n := Y) ;
   If (n == Z) p1 p2

   --> (in case X <> Y and Z == X)

   If something (q1 ; n := X ; p1) (q2 ; n := Y ; p2) ;

   similarly if Z == Y and X <> Y

*)

Definition dest_Seq_def:
  (dest_Seq (Seq p1 p2) = (p1,p2:wordLang$prog)) /\
  (dest_Seq p = (Skip,p))
End

Theorem dest_Seq_pmatch:
  !p.
  dest_Seq p =
  pmatch p of
    Seq p1 p2 => (p1,p2:wordLang$prog)
   | p => (Skip,p)
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[dest_Seq_def]
QED

Definition dest_If_def:
  (dest_If (If x1 x2 x3 p1 p2) = SOME (x1,x2,x3,p1,p2:wordLang$prog)) /\
  (dest_If _ = NONE)
End

Theorem dest_If_pmatch:
  !p.
  dest_If p =
  pmatch p of
    If x1 x2 x3 p1 p2 => SOME (x1,x2,x3,p1,p2:wordLang$prog)
   | _ => NONE
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[dest_If_def]
QED

Definition dest_If_Eq_Imm_def:
  dest_If_Eq_Imm p =
    case dest_If p of
    | SOME (Equal,n,Imm w,p1,p2) => SOME (n,w,p1,p2)
    | _ => NONE
End

Theorem dest_If_Eq_Imm_pmatch:
  !p.
  dest_If_Eq_Imm p =
    pmatch dest_If p of
    | SOME (Equal,n,Imm w,p1,p2) => SOME (n,w,p1,p2)
    | _ => NONE
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[dest_If_Eq_Imm_def]
QED

Definition dest_Seq_Assign_Const_def:
  dest_Seq_Assign_Const n p =
    let (p1,p2) = dest_Seq p in
      case p2 of
      | Assign m (Const w) => if m = n then SOME (p1,w) else NONE
      | _ => NONE
End

Theorem dest_Seq_Assign_Const_pmatch:
  !n p.
  dest_Seq_Assign_Const n p =
    let (p1,p2) = dest_Seq p in
      pmatch p2 of
      | Assign m (Const w) => if m = n then SOME (p1,w) else NONE
      | _ => NONE
Proof
  rpt strip_tac
  >> Cases_on `dest_Seq p`
  >> PURE_REWRITE_TAC [LET_THM,pairTheory.UNCURRY_DEF]
  >> BETA_TAC
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[dest_Seq_Assign_Const_def]
QED

(* Constant folding and propagation optimization, e.g.

   x := 1;
   y := x + 4;
   z := y;

   becomes

   x := 1;
   y := 5;
   z := 5;

  Limitation: The current implementation forgets all constant values after a
  function call with a handler (for easier implementation and proofs). This is
  probably not difficult to improve, but would require some kind of theorem
  saying that a program does not change variables not mentioned in the program
  (because we cannot know beforehand/statically if the handler code is going to
  run, so we must throw away all variables mentioned in the handler).
 *)

Definition strip_const_def:
  (strip_const [] = SOME []) /\
  (strip_const (Const w::cs) =
     case strip_const cs of
       | SOME ws => SOME (w::ws)
       | _ => NONE) /\
  (strip_const _ = NONE)
End

Definition int_op_def:
  int_op op ws =
    case (op,ws) of
    | (And,ws) => SOME (FOLDR int_and (-1) ws)
    | (Add,ws) => SOME (FOLDR $+ 0 ws)
    | (Or,ws) => SOME (FOLDR int_or 0 ws)
    | (Xor,ws) => SOME (FOLDR int_xor 0 ws)
    | (Sub,[w1;w2]) => SOME (w1 - w2)
    | _ => NONE
End

Definition int_unsigned_def:
  int_unsigned (bits:num) i = i % &(2 ** bits)
End

Definition int_signed_def:
  int_signed bits i =
    let u = int_unsigned bits i in
      if u < &(2 ** (bits - 1)) then u else u - &(2 ** bits)
End

Definition int_sh_def:
  int_sh bits sh i j =
    let n = Num (int_unsigned bits j) in
      if n = 0 then SOME i
      else if bits <= n then NONE
      else let p = &(2 ** n) in
        case sh of
        | Lsl => SOME (i * p)
        | Lsr => SOME (int_unsigned bits i / p)
        | Asr => SOME (int_signed bits i / p)
        | Ror => let u = int_unsigned bits i in
                   SOME (u / p + (u % p) * &(2 ** (bits - n)))
End

Definition int_cmp_def:
  int_cmp bits cmp i j =
    let u = int_unsigned bits i in
    let v = int_unsigned bits j in
      case cmp of
      | Equal => u = v
      | NotEqual => u <> v
      | Lower => u < v
      | NotLower => ~(u < v)
      | Less => int_signed bits i < int_signed bits j
      | NotLess => ~(int_signed bits i < int_signed bits j)
      | Test => int_and u v = 0
      | NotTest => int_and u v <> 0
End

Definition const_fp_exp_def:
  (const_fp_exp bits (Var v) cs =
     case lookup v cs of
       | SOME x => Const x
       | NONE => Var v) /\
  (const_fp_exp bits (Op op args) cs =
     let const_fp_args = MAP (\a. const_fp_exp bits a cs) args in
       case strip_const const_fp_args of
         | SOME ws => (case int_op op ws of
                        | SOME w => Const w
                        | _ => Op op (MAP Const ws))
         | _ => Op op const_fp_args) /\
  (const_fp_exp bits (Shift sh e e1) cs =
     let e' = const_fp_exp bits e cs in
     let e1' = const_fp_exp bits e1 cs in
       case (e',e1') of
       | (Const i,Const j) =>
           (case int_sh bits sh i j of
            | SOME k => Const k
            | NONE => Shift sh e' e1')
       | _ => Shift sh e' e1') /\
  (const_fp_exp bits e _ = e)
End

Definition const_fp_move_cs_def:
  (const_fp_move_cs [] _ cs = cs) /\
  (const_fp_move_cs (m::ms) ocs ncs =
    let v = FST m in
    let nncs =
      (case lookup (SND m) ocs of
        | SOME c => insert v c ncs
        | _ => delete v ncs) in
        const_fp_move_cs ms ocs nncs)
End

Definition const_fp_inst_cs_def:
  (const_fp_inst_cs (bits:num) (Const r _) (cs:int num_map) = delete r cs) /\
  (const_fp_inst_cs bits (Arith (Binop _ r _ _)) cs = delete r cs) /\
  (const_fp_inst_cs bits (Arith (Shift _ r _ _)) cs = delete r cs) /\
  (const_fp_inst_cs bits (Arith (AddCarry r1 _ _ r2)) cs = delete r2 (delete r1 cs)) /\
  (const_fp_inst_cs bits (Arith (AddOverflow r1 _ _ r2)) cs = delete r2 (delete r1 cs)) /\
  (const_fp_inst_cs bits (Arith (SubOverflow r1 _ _ r2)) cs = delete r2 (delete r1 cs)) /\
  (const_fp_inst_cs bits (Arith (IMul r1 _ _ r2)) cs = delete r2 (delete r1 cs)) /\
  (const_fp_inst_cs bits (Arith (IDiv r1 r2 _ _)) cs = delete r1 (delete r2 cs)) /\
  (const_fp_inst_cs bits (Arith (LongMul r1 r2 _ _)) cs = delete r1 (delete r2 cs)) /\
  (const_fp_inst_cs bits (Arith (LongDiv r1 r2 _ _ _)) cs = delete r1 (delete r2 cs)) /\
  (const_fp_inst_cs bits (Arith (Div r1 _ _)) cs = delete r1 cs) /\
  (const_fp_inst_cs bits (Mem Load r _) cs = delete r cs) /\
  (const_fp_inst_cs bits (Mem Load32 r _) cs = delete r cs) /\
  (const_fp_inst_cs bits (Mem Load8 r _) cs = delete r cs) /\
  (const_fp_inst_cs bits (FP (FPLess r f1 f2)) cs = delete r cs) ∧
  (const_fp_inst_cs bits (FP (FPLessEqual r f1 f2)) cs = delete r cs) ∧
  (const_fp_inst_cs bits (FP (FPEqual r f1 f2)) cs = delete r cs) ∧
  (const_fp_inst_cs bits (FP (FPMovToReg r1 r2 d)) cs =
    if bits = 64 then delete r1 cs
    else delete r2 (delete r1 cs)) ∧
  (const_fp_inst_cs bits _ cs = cs)
End

Definition get_var_imm_cs_def:
  (get_var_imm_cs (Reg r) cs = lookup r cs) /\
  (get_var_imm_cs (Imm i) _ = SOME i)
End

Definition is_gc_const_def:
  is_gc_const c = (int_and c 1 = 0)
End


Definition all_names_def[simp]:
  all_names (n,m) = union n m
End

Overload delete_all[local] = “λn l. FOLDR delete l n”

(* We only drop constants that can potentially be in registers *)
Definition drop_consts_def:
  drop_consts cs [] = Skip ∧
  drop_consts cs (n::ns) =
    case lookup n cs of
    | NONE => drop_consts cs ns
    | SOME w => SmartSeq (drop_consts cs ns) (Assign n (Const w))
End

Definition const_fp_loop_def:
  (const_fp_loop bits (Move pri moves : prog) cs = (Move pri moves, const_fp_move_cs moves cs cs)) /\
  (const_fp_loop bits (Inst i) cs = (Inst i, const_fp_inst_cs bits i cs)) /\
  (const_fp_loop bits (Assign v e) cs =
     let const_fp_e = const_fp_exp bits e cs in
       case const_fp_e of
         | Const c => (Assign v const_fp_e, insert v c cs)
         | _ => (Assign v const_fp_e, delete v cs)) /\
  (const_fp_loop bits (Get v name) cs = (Get v name, delete v cs)) /\
  (const_fp_loop bits (OpCurrHeap b v w) cs = (OpCurrHeap b v w, delete v cs)) /\
  (const_fp_loop bits (MustTerminate p) cs =
    let (p', cs') = const_fp_loop bits p cs in
      (MustTerminate p', cs')) /\
  (const_fp_loop bits (Seq p1 p2) cs =
    let (p1', cs') = const_fp_loop bits p1 cs in
    let (p2', cs'') = const_fp_loop bits p2 cs' in
      (Seq p1' p2', cs'')) /\
  (const_fp_loop bits (wordLang$If cmp lhs rhs p1 p2) cs =
    case (lookup lhs cs, get_var_imm_cs rhs cs) of
      | (SOME clhs, SOME crhs) =>
        (if int_cmp bits cmp clhs crhs
         then const_fp_loop bits p1 cs else const_fp_loop bits p2 cs)
      | _ => (let (p1', p1cs) = const_fp_loop bits p1 cs in
              let (p2', p2cs) = const_fp_loop bits p2 cs in
               (wordLang$If cmp lhs rhs p1' p2', inter_eq p1cs p2cs))) /\
  (const_fp_loop bits (Call ret dest args handler) cs =
    case ret of
      | NONE => (SmartSeq (drop_consts cs args) (Call ret dest args handler),
                 filter_v is_gc_const cs)
      | SOME (n, names, ret_handler, l1, l2) =>
        (if handler = NONE then
           (let cs' = delete_all n (filter_v is_gc_const (inter cs (all_names names))) in
            let (ret_handler', cs'') = const_fp_loop bits ret_handler cs' in
              (SmartSeq (drop_consts cs args)
                (Call (SOME (n, names, ret_handler', l1, l2)) dest args handler), cs''))
         else
           (SmartSeq (drop_consts cs args)
             (Call ret dest args handler), LN))) /\
  (const_fp_loop bits (FFI x0 x1 x2 x3 x4 names) cs =
    (SmartSeq (drop_consts cs [x1;x2;x3;x4]) (FFI x0 x1 x2 x3 x4 names), inter cs (all_names names))) /\
  (const_fp_loop bits (LocValue v x3) cs = (LocValue v x3, delete v cs)) /\
  (const_fp_loop bits (Alloc n names) cs =
    (SmartSeq (drop_consts cs [n]) (Alloc n names), filter_v is_gc_const (inter cs (all_names names)))) /\
  (const_fp_loop bits (StoreConsts a b c d ws) cs = (StoreConsts a b c d ws, delete a (delete b (delete c (delete d cs))))) /\
  (const_fp_loop bits (Install r1 r2 r3 r4 r5 names) cs =
    (SmartSeq (drop_consts cs [r1;r2;r3;r4;r5])
      (Install r1 r2 r3 r4 r5 names), delete r1 (filter_v is_gc_const (inter cs (all_names names))))) /\
  (const_fp_loop bits (Store e v) cs =
    (Store (const_fp_exp bits e cs) v, cs)) /\
  (const_fp_loop bits (ShareInst Load v e) cs =
    (ShareInst Load v (const_fp_exp bits e cs), delete v cs)) /\
  (const_fp_loop bits (ShareInst Load8 v e) cs =
    (ShareInst Load8 v (const_fp_exp bits e cs), delete v cs)) /\
  (const_fp_loop bits (ShareInst Load16 v e) cs =
    (ShareInst Load16 v (const_fp_exp bits e cs), delete v cs)) /\
  (const_fp_loop bits (ShareInst Load32 v e) cs =
    (ShareInst Load32 v (const_fp_exp bits e cs), delete v cs)) /\
  (const_fp_loop bits (ShareInst Store v e) cs =
    (ShareInst Store v (const_fp_exp bits e cs), cs)) /\
  (const_fp_loop bits (ShareInst Store8 v e) cs =
    (ShareInst Store8 v (const_fp_exp bits e cs), cs)) /\
  (const_fp_loop bits (ShareInst Store16 v e) cs =
    (ShareInst Store16 v (const_fp_exp bits e cs), cs)) /\
  (const_fp_loop bits (ShareInst Store32 v e) cs =
    (ShareInst Store32 v (const_fp_exp bits e cs), cs)) /\
  (const_fp_loop bits (Loop names body exit_names) cs =
    (Loop names (FST (const_fp_loop bits body LN)) exit_names, LN)) /\
  (const_fp_loop bits p cs = (p, cs))
End

Definition const_fp_def:
  const_fp bits p = FST (const_fp_loop bits p LN)
End

(*
Optimise near-consecutive If/If pairs into a single If when there are only two
possible control-flow paths.

This case looks like:
  (if C then X else Y) ; Zs ; (if C2 then X2 else Y2)

Also, the number of intermediate Zs is small, (X ; Zs) guarantees either C2 or
not C2, and (Y ; Zs) guarantees the opposite. The second If can be removed at
the cost of duplicating the Zs.

The strategy here is (1) recognise the case, (2) expand the first If to cover
everything, hoisting copies of the second If into both branches and (3) re-run
the const_fp pass to simplify each branch down to a straight line.

This means the correctness follows straightforwardly from that of const_fp.

To recognise the case (1), step through Seq sequences which we expect to be
right-associated, and incrementally build up their left-associated variant
(which we will need eventually to pull things into the first If). Give up if
this takes too many steps (too many Zs). When an If is found, test-run the
const_fp pass to see if it would reduce the condition in the second If.
*)

Definition rewrite_duplicate_if_max_reassoc_def:
  rewrite_duplicate_if_max_reassoc = 8n
End

Definition dest_Raise_num_pmatch_def[nocompute]:
  dest_Raise_num p = pmatch p of wordLang$Raise n => n | _ => 0n
End

Theorem dest_Raise_num_def[compute] = dest_Raise_num_pmatch_def
  |> CONV_RULE (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)

Definition is_simple_pmatch_def[nocompute]:
  is_simple p = pmatch p of
    | Tick => T
    | Skip => T
    | Move _ _ => T
    | Assign _ _ => T
    | _ => F
End

Theorem is_simple_def[compute] = is_simple_pmatch_def
  |> CONV_RULE (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)

Definition try_if_hoist2_def:
  try_if_hoist2 bits N p1 interm dummy p2 = if N = 0n then NONE
  else case p1 of
    | wordLang$If cmp lhs rhs br1 br2 =>
      let res1 = dest_Raise_num (SND (dest_Seq (const_fp bits (Seq (Seq br1 interm) dummy)))) in
      if res1 = 0n then NONE
      else
      let res2 = dest_Raise_num (SND (dest_Seq (const_fp bits (Seq (Seq br2 interm) dummy)))) in
      if res1 + res2 <> 3n then NONE
      else SOME (const_fp bits (If cmp lhs rhs (Seq (Seq br1 interm) p2)
          (Seq (Seq br2 interm) p2)))
    | Seq p3 p4 => (
      case dest_If p4 of
      | SOME (cmp, lhs, rhs, br1, br2) =>
      let res1 = dest_Raise_num (SND (dest_Seq (const_fp bits (Seq (Seq br1 interm) dummy)))) in
      if res1 = 0n then NONE
      else
      let res2 = dest_Raise_num (SND (dest_Seq (const_fp bits (Seq (Seq br2 interm) dummy)))) in
      if res1 + res2 <> 3n then NONE
      else SOME (Seq p3 (const_fp bits (If cmp lhs rhs (Seq (Seq br1 interm) p2)
          (Seq (Seq br2 interm) p2))))
      | NONE =>
      if is_simple p4
      then try_if_hoist2 bits (N - 1n) p3 (Seq p4 interm) dummy p2
      else NONE
      )
    | _ => NONE
End

Definition try_if_hoist1_def:
  try_if_hoist1 bits p1 p2 = (case dest_If p2 of
  | NONE => NONE
  | SOME (cmp, lhs, rhs, _, _) => (
    let dummy = wordLang$If cmp lhs rhs (Raise 1) (Raise 2) in
    try_if_hoist2 bits rewrite_duplicate_if_max_reassoc p1 Skip dummy p2
  )
  )
End

Definition simp_duplicate_if_def:
  simp_duplicate_if bits p = case p of
  | MustTerminate q => MustTerminate (simp_duplicate_if bits q)
  | Call ret_prog dest args handler =>
     Call (case ret_prog of
           | NONE => NONE
           | SOME (x1,x2,q1,x3,x4) => SOME (x1,x2,simp_duplicate_if bits q1,x3,x4))
       dest args
          (case handler of
           | NONE => NONE
           | SOME (y1,q2,y2,y3) => SOME (y1,simp_duplicate_if bits q2,y2,y3))
  | If cmp lhs rhs br1 br2 =>
    If cmp lhs rhs (simp_duplicate_if bits br1) (simp_duplicate_if bits br2)
  | Seq p1 p2 => (
    let p1x = simp_duplicate_if bits p1;
        p2x = simp_duplicate_if bits p2 in
    case try_if_hoist1 bits p1x p2x of
    | NONE => Seq p1x p2x
    | SOME p3 => Seq_assoc Skip p3
  )
  | Loop names body exit_names =>
    Loop names (simp_duplicate_if bits body) exit_names
  | _ => p
End

(*Optimize pairs where one side is known to terminate due to a Raise or a Return
the flag is T when its known to halt and F otherwise

*)
Definition push_out_if_aux_def:
(* all of them together *)
  push_out_if_aux p = case p of
  | MustTerminate q =>
    (case (push_out_if_aux q) of
    | (c,b) => (MustTerminate c,b))
  | Return _ _ => (p,T)
  | Raise _ => (p,T)
  | Call NONE _ _ _ => (p, T)
  | If cmp r1 ri c1 c2 => (case (push_out_if_aux c1,push_out_if_aux c2) of
                            | ((c1',T),(c2',T)) => (If cmp r1 ri c1' c2', T)
                            | ((c1',F),(c2',T)) => (Seq (If cmp r1 ri Skip c2') c1', F)
                            | ((c1',T),(c2',F)) => (Seq (If cmp r1 ri c1' Skip) c2', F)
                            | ((c1',F),(c2',F)) => (If cmp r1 ri c1' c2', F))
  | Seq c1 c2 => (case (push_out_if_aux c1) of
                   | (c1', T) => ((Seq c1' c2),T) (*Don't have to bother as DCE will get rid of it*)
                   | (c1', F) =>
                      (case (push_out_if_aux c2) of
                      |  (c2',b) => (Seq c1' c2', b)))
  | Loop names body exit_names =>
    (Loop names (FST (push_out_if_aux body)) exit_names, F)
  | _ => (p,F)
End

Definition push_out_if_def:
 push_out_if p = FST (push_out_if_aux p)
End



Definition compile_exp_def:
  compile_exp bits (e:wordLang$prog) =
    let e = Seq_assoc Skip e in
    let e = const_fp bits e in
    let e = simp_duplicate_if bits e in
    let e = push_out_if e in
      e
End
