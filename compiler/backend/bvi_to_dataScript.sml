(*
  A compiler phase that turns programs of the functional language BVI
  into the first imperative language of the CakeML compiler: dataLang.
*)
open preamble bviTheory dataLangTheory
     data_simpTheory data_liveTheory data_spaceTheory;

val _ = new_theory "bvi_to_data";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* compilation from BVI to dataLang *)

Theorem op_space_reset_pmatch:
  ! op.
  op_space_reset op =
    case op of
      Add => T
    | Sub => T
    | Mult => T
    | Div => T
    | Mod => T
    | Less => T
    | LessEq => T
    | Greater => T
    | GreaterEq => T
    | Equal => T
    | ListAppend => T
    | FromList _ => T
    | RefArray => T
    | RefByte _ => T
    | ConsExtend _ => T
    | CopyByte new_flag => new_flag
    | ConfigGC => T
    | FFI _ => T
    | _ => F
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> Cases_on `op` >> fs[op_space_reset_def]
QED

Theorem op_requires_names_eqn:
   ∀op. op_requires_names op =
    (op_space_reset op ∨ (dtcase op of
                          | FFI n => T
                          | Install => T
                          | CopyByte new_flag => T
                          | _ => F))
Proof
  Cases>>fs[op_requires_names_def]
QED

Theorem op_requires_names_pmatch:
   ∀op. op_requires_names op =
  (op_space_reset op ∨ (case op of
                        | FFI n => T
                        | Install => T
                        | CopyByte new_flag => T
                        | _ => F))
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)) >>
  fs[op_requires_names_eqn]
QED

val _ = Parse.hide"tail";

Definition pure_enough_def:
  (pure_enough (closLang$FFI _) = F) /\
  (pure_enough Install = F) /\
  (pure_enough (CopyByte _) = F) /\
  (pure_enough DerefByte = F)/\
  (pure_enough UpdateByte = F) /\
  (pure_enough RefArray = F) /\
  (pure_enough (RefByte _) = F) /\
  (pure_enough SetGlobalsPtr = F) /\
  (pure_enough GlobalsPtr = F) /\
  (pure_enough AllocGlobal = F) /\
  (pure_enough (SetGlobal _) = F) /\
  (pure_enough (Global _) = F) /\
  (pure_enough Ref = F) /\
  (pure_enough Length = F) /\
  (pure_enough LengthByte = F) /\
  (pure_enough _ = T)
End

Definition compile_op_def:
  compile_op op vs arch_size =
    let p = pure_enough op in
      if op_requires_names op then
        if op = closLang$Greater then (closLang$Less, REVERSE vs, T, 0, p) else
        if op = closLang$GreaterEq then (LessEq, REVERSE vs, T, 0, p) else
          (op, vs, T, 0, p)
      else (op, vs, F, op_space_req op (LENGTH vs) arch_size, p)
End

Definition compile_assign_def:
  compile_assign acc op vs =
    let (n,live,cache,arch_size) = acc in
    let (new_op,new_vs,names,k,p) = compile_op op vs arch_size in
(*
      if p /\ IS_SOME (ALOOKUP cache (new_op,new_vs)) then
        (Skip,THE (ALOOKUP cache (new_op,new_vs)),acc)
      else
*)
         let c0 = Assign n new_op new_vs (if names then SOME live else NONE) in
         let c1 = (if k = 0 then c0 else Seq (MakeSpace k live) c0) in
         let new_cache = if p then ((new_op,new_vs),n) :: cache else cache in
         let new_acc = (n+1,insert n () live,new_cache,arch_size) in
           (c1,n,new_acc)
End

Definition compile_def:
  (compile acc (env:num list) tail [] =
    (Skip,[]:num list,acc)) /\
  (compile acc env tail (x::y::xs) =
     let (c1,v1,acc1) = compile acc env F [x] in
     let (c2,vs,acc2) = compile acc1 env F (y::xs) in
       (Seq c1 c2, HD v1 :: vs, acc2)) /\
  (compile acc env tail [(Var v):bvi$exp] =
     let var = any_el v env 0n in
       if tail then (Return var, [var], acc)
               else (Skip, [var], acc)) /\
  (compile acc env tail [If x1 x2 x3] =
     let (c1,v1,acc1) = compile acc env F [x1] in
     let (c2,v2,acc2) = compile acc1 env tail [x2] in
     let (c3,v3,acc3) = compile acc1 env tail [x3] in
       if tail then
         (Seq c1 (If (HD v1) c2 c3),v2,acc1)
       else
         let var = MAX (FST acc2) (FST acc3) in
          (Seq c1 (If (HD v1) (Seq c2 (Move var (HD v2)))
                              (Seq c3 (Move var (HD v3)))),
           [var],(var+1,SND acc1))) /\
  (compile acc env tail [Let xs x2] =
     let (c1,vs,acc1) = compile acc env F xs in
     let (c2,v2,acc2) = compile acc1 (vs ++ env) tail [x2] in
       (Seq c1 c2, v2, acc2)) /\
  (compile acc env tail [Raise x1] =
     let (c1,v1,acc1) = compile acc env F [x1] in
       (Seq c1 (Raise (HD v1)), v1, acc1)) /\
  (compile acc env tail [Op op xs] =
     let (c1,vs,acc1) = compile acc env F xs in
     let (c2,var,acc2) = compile_assign acc1 op (REVERSE vs) in
     let c3 = Seq c1 c2 in
       (if tail then Seq c3 (Return var) else c3, [var], acc2)) /\
  (compile acc env tail [Tick x1] =
     let (c1,v1,acc1) = compile acc env tail [x1] in
       (Seq Tick c1, v1, acc1)) /\
  (compile acc env tail [Call ticks dest xs NONE] =
     let (c1,vs,acc1) = compile acc env F xs in
     let (var,live:num_set,acc1') = acc1 in
     let acc2 = (var+1:num,live,acc1') in
     let ret = (if tail then NONE else SOME (var, live)) in
       (Seq c1 (mk_ticks ticks (Call ret dest vs NONE)), [var], acc2)) /\
  (compile acc env tail [Call ticks dest xs (SOME handler)] =
     let (c1,vs,acc1) = compile acc env F xs in
     let (var,live,acc1') = acc1 in
     let acc2 = (var+2,live,acc1') in
     let (c2,v,acc3) = compile acc2 (var::env) F [handler] in
     let ret = SOME (var+1, live) in
     let c3 = (if tail then Return (var+1) else Skip) in
       (Seq c1 (mk_ticks ticks (Seq (Call ret dest vs
                 (SOME (var,Seq c2 (Move (var+1) (HD v))))) c3)), [var+1], acc3))
Termination
  WF_REL_TAC ‘measure (exp2_size o SND o SND o SND)’
End

Definition compile_main_def:
  compile_main arch_size arg_count e =
    let env = COUNT_LIST arg_count in
    let acc = (arg_count,fromAList (MAP (\n.(n,())) env),[],arch_size) in
      FST (bvi_to_data$compile acc env T [e])
End

Theorem compile_LENGTH:
  !acc env tail xs c vs acc1.
     (compile acc env tail xs = (c,vs,acc1)) ==> (LENGTH vs = LENGTH xs)
Proof
  recInduct compile_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once compile_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw[] \\ fs []
QED

Theorem compile_SING:
  (compile acc env tail [x] = (c,vs,acc1)) ==> ?t. vs = [t]
Proof
  rw [] \\ imp_res_tac compile_LENGTH
  \\ fs [LENGTH_EQ_NUM_compute]
QED

(* combine dataLang optimisations *)

val optimise_def = Define `
  optimise arch_size prog =
    data_space$compile
      (simp (FST (data_live$compile prog LN arch_size)) Skip) arch_size`

(* the top-level compiler includes the optimisations, because the correctness
   proofs are combined *)

val compile_exp = Define `
  compile_exp arch_size arg_count exp =
    optimise arch_size (compile_main arch_size arg_count exp)`

val compile_part = Define `
  compile_part arch_size (name:num, arg_count, exp) =
    (name, arg_count, compile_exp arch_size arg_count exp)`

val compile_prog_def = Define `
  compile_prog arch_size prog = MAP (compile_part arch_size) prog`;

(* tests

val input1 =
  “Let [Op El [Var 0; Op (Const 0) []] ;
        Op El [Var 0; Op (Const 0) []]]
     (Op (Cons 7) [Op (Const 0) []; Op (Const 0) []; Var 0; Var 1])”

val input2 =
  “If (Op (TagLenEq 0 0) [Op El [Var 0; Op (Const 0) []]])
     (Var 1)
     (If (Op (TagLenEq 0 0) [Op El [Op El [Var 0; Op (Const 0) []]; Op (Const 0) []]])
       (Var 1) (Var 0))”

fun test input =
  EVAL “simp (compile_main 32 2 ^input) Skip”
  |> SIMP_RULE (srw_ss()) [data_simpTheory.simp_def,data_simpTheory.pSeq_def]
  |> CONV_RULE (RAND_CONV EVAL)

val r1 = test input1;
val r2 = test input2;

*)

val _ = export_theory();
