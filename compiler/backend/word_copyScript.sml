(*
  This compilation pass performs a copy propagation phase.
  NOTE: Copy propagation may be incomplete if input is not in SSA form.
*)
Theory word_copy
Ancestors
  wordLang reg_alloc
Libs
  preamble

(*
  The copy propagator does the "propagation" but
    does not delete the old copy, i.e.:

  {a}
  b := a
  {b}
  c := b
  {c}
  (any future use of a or b would be replaced by c)

  The propagator state consists of
  1) a map from vars to its equivalence class
  2) a map from equivalence class to its representative
  3) a counter to generate fresh equivalences
  4) a partial map from store_names to a vars holding its value

  Only alloc vars (is_alloc_var) are ever stored in
    this mapping because we never want to
    copy propagate the others.
*)

Datatype:
  copy_state =
  <| (* maps var to its equivalence class *)
     to_eq : num num_map ;
     (* maps equivalence class to its representative *)
     from_eq : num num_map ;
     (* maps store names to an equivalence class *)
     store_to_eq : (store_name, num) alist;
     next : num |>
End

Definition empty_eq_def:
  empty_eq =
    <| to_eq := LN ; from_eq := LN;
      store_to_eq := []; next := 0|>
End

(* lookup representative of eq class, if it exists
  otherwise it's just the var itself *)
Definition lookup_eq_def:
  lookup_eq cs v =
  case lookup v cs.to_eq of
    NONE => v
  | SOME c =>
    case lookup c cs.from_eq of
      NONE => v
    | SOME v' => v'
End

Definition lookup_eq_imm_def:
  lookup_eq_imm cs vi =
  case vi of
    Reg v => Reg (lookup_eq cs v)
  | _ => vi
End

(* remove v from its equivalence class,
    possibly destroying the entire class
  In SSA, this should never happen, so
  we simply drop the entire eq state if it does *)
Definition remove_eq_def:
  remove_eq cs v =
  case lookup v cs.to_eq of
    NONE => cs
  | SOME c => empty_eq
End
(*
    let to_eq = delete v cs.to_eq in
    (case lookup v cs.from_eq of
      NONE => cs with to_eq := to_eq
    | SOME v' =>
      if v = v' then
        cs with from_eq := LN
      else
        cs with to_eq := to_eq) *)

Definition remove_eqs_def:
  (remove_eqs cs [] = cs) ∧
  (remove_eqs cs (v::vs) =
    remove_eqs (remove_eq cs v) vs)
End

Definition copy_prop_inst_def:
  (copy_prop_inst Skip cs = (Skip,cs)) ∧
  (copy_prop_inst (Const reg w) cs =
    (Inst (Const reg w), remove_eq cs reg)) ∧
  (copy_prop_inst (Arith (Binop bop r1 r2 ri)) cs =
    let cs' = remove_eq cs r1 in
    let r2' = lookup_eq cs r2 in
    let ri' = lookup_eq_imm cs ri in
    let ri'' = if ri'=Reg r1 then ri else ri' in
    (Inst (Arith (Binop bop r1 r2' ri'')), cs')) ∧
  (copy_prop_inst (Arith (Shift shift r1 r2 n)) cs =
    let r2' = lookup_eq cs r2 in
      (Inst (Arith (Shift shift r1 r2' n)),
        remove_eq cs r1)) ∧
  (copy_prop_inst (Arith (Div r1 r2 r3)) cs =
    let r2' = lookup_eq cs r2 in
    let r3' = lookup_eq cs r3 in
    (Inst (Arith (Div r1 r2' r3')),
        remove_eq cs r1)) ∧
  (copy_prop_inst (Arith (AddCarry r1 r2 r3 r4)) cs =
    (* r4 is both read from and written to *)
    let cs' = remove_eqs cs [r1;r4] in
    let r2' = lookup_eq cs r2 in
    let r3' = lookup_eq cs r3 in
    let r3'' = if r3'=r1 then r3 else r3' in
    (Inst (Arith (AddCarry r1 r2' r3'' r4)), cs')) ∧
  (copy_prop_inst (Arith (AddOverflow r1 r2 r3 r4)) cs =
    let cs' = remove_eqs cs [r1;r4] in
    let r2' = lookup_eq cs r2 in
    let r3' = lookup_eq cs r3 in
    let r3'' = if r3'=r1 then r3 else r3' in
    (Inst (Arith (AddOverflow r1 r2' r3'' r4)), cs')) ∧
  (copy_prop_inst (Arith (SubOverflow r1 r2 r3 r4)) cs =
    let cs' = remove_eqs cs [r1;r4] in
    let r2' = lookup_eq cs r2 in
    let r3' = lookup_eq cs r3 in
    let r3'' = if r3'=r1 then r3 else r3' in
    (Inst (Arith (SubOverflow r1 r2' r3'' r4)), cs')) ∧
  (copy_prop_inst (Arith (LongMul r1 r2 r3 r4)) cs =
    let r3' = lookup_eq cs r3 in
    let r4' = lookup_eq cs r4 in
    (Inst (Arith (LongMul r1 r2 r3 r4)),
        remove_eqs cs [r1;r2] )) ∧
  (copy_prop_inst (Arith (LongDiv r1 r2 r3 r4 r5)) cs =
    let r3' = lookup_eq cs r3 in
    let r4' = lookup_eq cs r4 in
    let r5' = lookup_eq cs r5 in
    (Inst (Arith (LongDiv r1 r2 r3' r4' r5')),
        remove_eqs cs [r2;r1] )) ∧
  (copy_prop_inst (Mem Load r (Addr a w)) cs =
    let a' = lookup_eq cs a in
      (Inst (Mem Load r (Addr a' w)),
        remove_eq cs r)) ∧
  (copy_prop_inst (Mem Store r (Addr a w)) cs =
    let a' = lookup_eq cs a in
    let r' = lookup_eq cs r in
      (Inst (Mem Store r' (Addr a' w)), cs)) ∧
  (copy_prop_inst (Mem Load8 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
      (Inst (Mem Load8 r (Addr a' w)),
        remove_eq cs r)) ∧
  (copy_prop_inst (Mem Store8 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
    let r' = lookup_eq cs r in
      (Inst (Mem Store8 r' (Addr a' w)),cs)) ∧
  (copy_prop_inst (Mem Load16 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
      (Inst (Mem Load16 r (Addr a' w)),
        remove_eq cs r)) ∧
  (copy_prop_inst (Mem Store16 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
    let r' = lookup_eq cs r in
      (Inst (Mem Store16 r' (Addr a' w)),cs)) ∧
  (copy_prop_inst (Mem Load32 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
      (Inst (Mem Load32 r (Addr a' w)),
        remove_eq cs r)) ∧
  (copy_prop_inst (Mem Store32 r (Addr a w)) cs =
    let a' = lookup_eq cs a in
    let r' = lookup_eq cs r in
      (Inst (Mem Store32 r' (Addr a' w)),cs)) ∧
  (copy_prop_inst (FP (FPLess r f1 f2)) cs =
      (Inst (FP (FPLess r f1 f2)),
        remove_eq cs r)) ∧
  (copy_prop_inst (FP (FPLessEqual r f1 f2)) cs =
      (Inst (FP (FPLessEqual r f1 f2)),
        remove_eq cs r)) ∧
  (copy_prop_inst (FP (FPEqual r f1 f2)) cs =
      (Inst (FP (FPEqual r f1 f2)),
        remove_eq cs r)) ∧
  (copy_prop_inst (FP (FPMovToReg r1 r2 d):'a inst) cs =
      (Inst (FP (FPMovToReg r1 r2 d)),
        remove_eqs cs [r1;r2] )) ∧
  (copy_prop_inst (FP (FPMovFromReg d r1 r2)) cs =
      let r1' = lookup_eq cs r1 in
      let r2' = lookup_eq cs r2 in
      let (r1'',r2'') = if r1'=r2' then (r1,r2) else (r1',r2') in
      (Inst (FP (FPMovFromReg d r1'' r2'')), cs)) ∧
  (* Catchall: all FP *)
  (copy_prop_inst (FP x) cs = (Inst (FP x),cs)) ∧
  (* Catchall: should not happen *)
  (copy_prop_inst _ cs = ARB)
End

(* handle x := y by making x the new
  class representative of y.
  x must be guaranteed to not have to_eq *)
Definition set_eq_def:
  set_eq cs x y =
  if is_alloc_var x ∧ is_alloc_var y
  then
    case
      case lookup y cs.to_eq of
        NONE => NONE
      | SOME c => if lookup c cs.from_eq = NONE then NONE else SOME c
    of
       NONE =>
      <| to_eq := insert x cs.next (insert y cs.next cs.to_eq);
         from_eq := insert cs.next x cs.from_eq;
         store_to_eq := cs.store_to_eq;
         next := cs.next +1 |>
    | SOME c =>
      <| to_eq := insert x c cs.to_eq;
         from_eq := insert c x cs.from_eq;
         store_to_eq := cs.store_to_eq;
         next := cs.next |>
  else
    cs
End

(* Handle Store <- y
  If y has no equivalence class,
    create a singleton equivalence class for y
  Otherwise, reuse the existing class for y.
  Note: SSA ensures y is always an alloc_var, so the else branch is dead code.
*)
Definition set_store_eq_def:
  set_store_eq cs s y =
  if is_alloc_var y
  then
    case
      case lookup y cs.to_eq of
        NONE => NONE
      | SOME c => if lookup c cs.from_eq = NONE then NONE else SOME c
    of
      NONE =>
      <| to_eq := insert y cs.next cs.to_eq;
         from_eq := insert cs.next y cs.from_eq;
         store_to_eq := (s,cs.next)::cs.store_to_eq;
         next := cs.next +1 |>
    | SOME c =>
      cs with store_to_eq := (s,c)::cs.store_to_eq
  else empty_eq
End

Definition lookup_store_eq_def:
  lookup_store_eq cs s =
  case ALOOKUP cs.store_to_eq s of
    NONE => NONE
  | SOME c =>
    case lookup c cs.from_eq of
      NONE => NONE
    | SOME v' => SOME v'
End

(* conservatively merge two equivalence classes *)
Definition merge_eqs_def:
  merge_eqs cs ds =
  <|  to_eq := inter_eq cs.to_eq ds.to_eq;
      from_eq := inter_eq cs.from_eq ds.from_eq;
      store_to_eq :=
        FILTER (\(s,c). ALOOKUP cs.store_to_eq s = SOME c /\
                        ALOOKUP ds.store_to_eq s = SOME c) cs.store_to_eq;
      next  := MAX cs.next ds.next |>
End

(* shouldn't matter whether we put y or y' in set_eq? *)
Definition copy_prop_move_def:
  (copy_prop_move [] cs = ([],cs)) ∧
  (copy_prop_move ((x,y)::xs) cs =
    let y' = lookup_eq cs y in
    let (ms,cs') = copy_prop_move xs cs in
    let cs'' = set_eq (remove_eq cs' x) x y in
    ((x,y') :: ms, cs'') )
End

Definition copy_prop_share_def:
  copy_prop_share exp cs =
    case exp of
    Var r => Var (lookup_eq cs r)
  | (Op Add [Var r;Const c]) =>
     Op Add [Var (lookup_eq cs r);Const c]
  | _ => exp
End

Definition copy_prop_prog_def:
  (copy_prop_prog (Skip:'a wordLang$prog) cs =
    (Skip, cs)) ∧
  (copy_prop_prog (Move pri xs) cs =
    let tt = MAP FST xs; ss = MAP SND xs in
    if EVERY (λt. ¬ MEM t ss) tt then
      (* set (MAP FST xs) ∩ set (MAP SND xs) = ∅ *)
      let (xs',cs') = copy_prop_move xs cs in
      (Move pri xs', cs')
    else (Move pri xs, empty_eq)) ∧
  (copy_prop_prog (Inst i) cs =
    copy_prop_inst i cs) ∧
  (copy_prop_prog (Return v1 v2) cs =
    let v1' = lookup_eq cs v1 in
    let v2' = MAP (lookup_eq cs) v2 in
      (Return v1' v2',cs)) ∧
  (copy_prop_prog (Raise v) cs =
    let v' = lookup_eq cs v in
      (Raise v',cs)) ∧
  (copy_prop_prog (OpCurrHeap b dst src) cs =
    let src' = lookup_eq cs src in
    let src'' = if src'=dst then src else src' in
      (OpCurrHeap b dst src'',
         remove_eq cs dst)) ∧
  (copy_prop_prog Tick cs = (Tick, cs)) ∧
  (copy_prop_prog (MustTerminate p1) cs =
    let (p1',cs') = copy_prop_prog p1 cs in
    (MustTerminate p1', cs')) ∧
  (copy_prop_prog (Seq p1 p2) cs =
     let (q1,cs') = copy_prop_prog p1 cs in
     let (q2,cs'') = copy_prop_prog p2 cs' in
       (Seq q1 q2,cs'')) ∧
  (copy_prop_prog (If cmp r ri p1 p2) cs =
     let r' = lookup_eq cs r in
     let ri' = lookup_eq_imm cs ri in
     (* TODO: same mapping going in *)
     let (q1,cs') = copy_prop_prog p1 cs in
     let (q2,cs'') = copy_prop_prog p2 cs in
       (If cmp r' ri' q1 q2,
       merge_eqs cs' cs'')) ∧
  (copy_prop_prog (Set name exp) cs =
    case exp of
      Var n =>
      let n' = lookup_eq cs n in
      (Set name (Var n'), set_store_eq cs name n)
    | _ => (Set name exp, empty_eq)) ∧ (* flat_exp *)
  (copy_prop_prog (Get n name) cs =
    case lookup_store_eq cs name of
      NONE =>
        (Get n name, remove_eq cs n)
    | SOME v =>
      if v ≠ n then
      let (xs',cs') = copy_prop_move [(n,v)] cs in
        (Move 0 xs', cs')
      else (Skip, cs)
  ) ∧
  (copy_prop_prog (Call ret dest args handler) cs =
    (Call ret dest args handler, empty_eq)) ∧
    (* args will be 0,2,4,...
      TODO: are handlers worth analyzing? *)
  (copy_prop_prog (Alloc r live) cs =
     (Alloc r live, empty_eq)) ∧
  (copy_prop_prog (StoreConsts a b c d ws) cs =
      (StoreConsts a b c d ws,
        remove_eqs cs [a;b;c;d])) ∧
  (copy_prop_prog (LocValue r l1) cs =
      (LocValue r l1, remove_eq cs r)) ∧
  (copy_prop_prog (Install r1 r2 r3 r4 live) cs =
     (Install r1 r2 r3 r4 live, empty_eq)) ∧
  (copy_prop_prog (CodeBufferWrite r1 r2) cs =
     let r1' = lookup_eq cs r1 in
     let r2' = lookup_eq cs r2 in
     (CodeBufferWrite r1' r2', cs)) ∧
  (copy_prop_prog (DataBufferWrite r1 r2) cs =
     let r1' = lookup_eq cs r1 in
     let r2' = lookup_eq cs r2 in
     (DataBufferWrite r1' r2', cs)) ∧
  (copy_prop_prog (FFI i r1 r2 r3 r4 live) cs =
    (FFI i r1 r2 r3 r4 live, empty_eq)) ∧
  (copy_prop_prog (ShareInst op v exp) cs =
    let exp' = copy_prop_share exp cs in
    (ShareInst op v exp',
      remove_eq cs v)) ∧
  (copy_prop_prog prog cs = (prog, empty_eq))
  (* impossible? *)
End

Definition copy_prop_def:
  copy_prop (e:'a wordLang$prog) =
    FST (copy_prop_prog e empty_eq)
End

