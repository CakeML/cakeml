(*
  A compiler phases that transforms BVL programs into BVI programs. As
  part of this phase, certain primitive operations map to "stubs" code
  implemented in BVI; numeric constants are split into smaller ones to
  ease code generation later; Handle is fused with Call; and very
  large expressions are split into samller ones (in order to protect
  the register allocator from overly large inputs).
*)
open preamble bvlTheory bviTheory;
open backend_commonTheory
local open
  bvl_inlineTheory
  bvl_constTheory
  bvl_handleTheory
  bvi_letTheory
  bvi_tailrecTheory
  dataLangTheory
in end;

val _ = new_theory "bvl_to_bvi";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val destLet_def = Define `
  (destLet ((Let xs b):bvl$exp) = (xs,b)) /\
  (destLet _ = ([],Var 0))`;

Theorem destLet_pmatch:
  ∀exp.
  destLet exp =
    case exp of
      Let xs b => (xs,b)
    | _ => ([],Var 0)
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[destLet_def]
QED

val large_int = ``268435457:int`` (* 2**28-1 *)

val compile_int_def = tDefine "compile_int" `
  compile_int (i:int) =
    if 0 <= i then
      if i <= ^large_int then
        (Op (Const i) []:bvi$exp)
      else
        let x = compile_int (i / ^large_int) in
        let y = Op (Const (i % ^large_int)) [] in
        let n = Op (Const ^large_int) [] in
          Op Add [Op Mult [x; n]; y]
    else
      if -^large_int <= i then
        Op (Const i) []
      else
        let i = 0 - i in
        let x = compile_int (i / ^large_int) in
        let y = Op (Const (0 - (i % ^large_int))) [] in
        let n = Op (Const (0 - ^large_int)) [] in
          Op Add [Op Mult [x; n]; y]`
 (WF_REL_TAC `measure (Num o ABS)`
  \\ REPEAT STRIP_TAC \\ intLib.COOPER_TAC)

val alloc_glob_count_def = tDefine "alloc_glob_count" `
  (alloc_glob_count [] = 0:num) /\
  (alloc_glob_count (x::y::xs) =
     alloc_glob_count [x] + alloc_glob_count (y::xs) /\
  (alloc_glob_count [(Var _):bvl$exp] = 0) /\
  (alloc_glob_count [If x y z] =
     alloc_glob_count [x] +
     alloc_glob_count [y] +
     alloc_glob_count [z]) /\
  (alloc_glob_count [Handle x y] =
     alloc_glob_count [x] +
     alloc_glob_count [y]) /\
  (alloc_glob_count [Tick x] = alloc_glob_count [x]) /\
  (alloc_glob_count [Raise x] = alloc_glob_count [x]) /\
  (alloc_glob_count [Let xs x] = alloc_glob_count (x::xs)) /\
  (alloc_glob_count [Call _ _ xs] = alloc_glob_count xs) /\
  (alloc_glob_count [Op op xs] =
     if op = AllocGlobal then 1 + alloc_glob_count xs
                         else alloc_glob_count xs) /\
  (alloc_glob_count [_] = 0))`
  (WF_REL_TAC `measure exp1_size`)

val AllocGlobal_location_def = Define`
  AllocGlobal_location = data_num_stubs`;
val CopyGlobals_location_def = Define`
  CopyGlobals_location = AllocGlobal_location+1`;
val InitGlobals_location_def = Define`
  InitGlobals_location = CopyGlobals_location+1`;
val ListLength_location_def = Define`
  ListLength_location = InitGlobals_location+1`;
val FromListByte_location_def = Define`
  FromListByte_location = ListLength_location+1`;
val SumListLength_location_def = Define`
  SumListLength_location = FromListByte_location+1`;
val ConcatByte_location_def = Define`
  ConcatByte_location = SumListLength_location+1`;

val AllocGlobal_location_eq = save_thm("AllocGlobal_location_eq",
  ``AllocGlobal_location`` |> EVAL);
val CopyGlobals_location_eq = save_thm("CopyGlobals_location_eq",
  ``CopyGlobals_location`` |> EVAL);
val InitGlobals_location_eq = save_thm("InitGlobals_location_eq",
  ``InitGlobals_location`` |> EVAL);
val ListLength_location_eq = save_thm("ListLength_location_eq",
  ``ListLength_location`` |> EVAL);
val FromListByte_location_eq = save_thm("FromListByte_location_eq",
  ``FromListByte_location`` |> EVAL);
val SumListLength_location_eq = save_thm("SumListLength_location_eq",
  ``SumListLength_location`` |> EVAL);
val ConcatByte_location_eq = save_thm("ConcatByte_location_eq",
  ``ConcatByte_location`` |> EVAL);

val AllocGlobal_code_def = Define`
  AllocGlobal_code = (0:num,
    Let [Op GlobalsPtr []]
     (Let [Op Deref [Op (Const 0) []; Var 0]]
       (Let [Op Update [Op Add [Var 0; Op(Const 1)[]]; Op (Const 0) []; Var 1]]
         (Let [Op Length [Var 2]]
           (If (Op Less [Var 0; Var 2]) (Var 1)
               (Let [Op RefArray [Op (Const 0) []; Op Add [Var 0; Var 0]]]
                 (Let [Op SetGlobalsPtr [Var 0]]
                   (Call 0 (SOME CopyGlobals_location) [Var 1; Var 5; Op Sub [Op (Const 1) []; Var 4]] NONE))))))))`;

val CopyGlobals_code_def = Define`
  CopyGlobals_code = (3:num, (* ptr to new array, ptr to old array, index to copy *)
    Let [Op Update [Op Deref [Var 2; Var 1]; Var 2; Var 0]]
      (If (Op Equal [Op(Const 0)[]; Var 3]) (Var 0)
        (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op Sub [Op(Const 1)[];Var 3]] NONE)))`;

val InitGlobals_max_def = Define`
  InitGlobals_max = 10000n`;

val InitGlobals_code_def = Define`
  InitGlobals_code start n = (0:num,
    let n = MIN (MAX n 1) InitGlobals_max in
      Let [Op RefArray [Op (Const 0) []; Op (Const (&n)) []]]
        (Let [Op Update [Op (Const 1) []; Op (Const 0) []; Var 0]]
          (Let [Op SetGlobalsPtr [Var 1]]
             (Call 0 (SOME start) [] (SOME (Var 0))))))`;

val ListLength_code_def = Define `
  ListLength_code = (2n, (* ptr to array, accumulated length *)
    If (Op (TagLenEq nil_tag 0) [Var 0])
      (Var 1) (Call 0 (SOME ListLength_location)
                [Op El [Op (Const 1) []; Var 0];
                 Op Add [Var 1; Op (Const 1) []]] NONE))`

val FromListByte_code_def = Define`
  FromListByte_code = (3n, (* list, current index, byte array *)
    If (Op (TagLenEq nil_tag 0) [Var 0]) (Var 2)
      (Let [Op UpdateByte [Op El [Op (Const 0) []; Var 0]; Var 1; Var 2]]
        (Call 0 (SOME FromListByte_location)
          [Op El [Op (Const 1) []; Var 1];
           Op Add [Var 2; Op (Const 1) []];
           Var 3] NONE)))`;

val SumListLength_code_def = Define`
  SumListLength_code = (2n, (* ptr to list, accumulated length *)
    If (Op (TagLenEq nil_tag 0) [Var 0])
      (Var 1)
      (Call 0 (SOME SumListLength_location)
         [Op El [Op (Const 1) []; Var 0];
          Op Add [Var 1; Op LengthByte
                           [Op El [Op (Const 0) []; Var 0]]]] NONE))`

val ConcatByte_code_def = Define`
  ConcatByte_code = (3n, (* list, current index, destination *)
    If (Op (TagLenEq nil_tag 0) [Var 0]) (Var 2)
      (Let [Op El [Op (Const 0) []; Var 0]]
        (Let [Op LengthByte [Var 0]]
          (Let [Op (CopyByte F)
                  [Var 3; Var 4; Var 0; Op (Const 0) []; Var 1]]
            (Call 0 (SOME ConcatByte_location)
              [Op El [Op (Const 1) []; Var 3];
               Op Add [Var 4; Var 1];
               Var 5] NONE)))))`;

val stubs_def = Define `
  stubs start n = [(AllocGlobal_location, AllocGlobal_code);
                   (CopyGlobals_location, CopyGlobals_code);
                   (InitGlobals_location, InitGlobals_code start n);
                   (ListLength_location, ListLength_code);
                   (FromListByte_location, FromListByte_code);
                   (SumListLength_location, SumListLength_code);
                   (ConcatByte_location, ConcatByte_code)]`;

val _ = temp_overload_on ("num_stubs", ``backend_common$bvl_num_stubs``)

local val compile_op_quotation = `
  compile_op op c1 =
    dtcase op of
    | Const i => (dtcase c1 of [] => compile_int i
                  | _ => Let [Op (Const 0) c1] (compile_int i))
    | Global n => Op Deref (c1++[compile_int(&(n+1)); Op GlobalsPtr []])
    | SetGlobal n => Op Update (c1++[compile_int(&(n+1)); Op GlobalsPtr []])
    | AllocGlobal =>
        (dtcase c1 of [] => Call 0 (SOME AllocGlobal_location) [] NONE
         | _ => Let [Op (Const 0) c1] (Call 0 (SOME AllocGlobal_location) [] NONE))
    | (FromList n) => Let (if NULL c1 then [Op (Const 0) []] else c1)
                        (Op (FromList n)
                        [Var 0; Call 0 (SOME ListLength_location)
                                   [Var 0; Op (Const 0) []] NONE])
    | Install => Let (if LENGTH c1 <> 2
                      then [Let c1 (Op (Const 0) []); Op (Const 0) []] else c1)
                        (Op Install
                        [Call 0 (SOME ListLength_location)
                           [Var 0; Op (Const 0) []] NONE;
                         Call 0 (SOME ListLength_location)
                           [Var 1; Op (Const 0) []] NONE;
                         Var 0; Var 1])
    | String str =>
        Let [Op (RefByte T) [Op (Const 0) c1; compile_int (&(LENGTH str))]]
          (Let (MAPi (λn c. Op UpdateByte [Op (Const &(ORD c)) []; compile_int (&n); Var 0]) str)
            (Var (LENGTH str)))
    | FromListByte =>
        Let (if NULL c1 then [Op (Const 0) []] else c1)
          (Call 0 (SOME FromListByte_location)
             [Var 0;
              Op (Const 0) [];
              Op (RefByte T)
                [Op (Const 0) [];
                 Call 0 (SOME ListLength_location)
                   [Var 0; Op (Const 0) []] NONE]]
             NONE)
    | ConcatByteVec =>
        Let (if NULL c1 then [Op (Const 0) []] else c1)
          (Call 0 (SOME ConcatByte_location)
            [Var 0;
             Op (Const 0) [];
             Op (RefByte T)
               [Op (Const 0) [];
                Call 0 (SOME SumListLength_location)
                  [Var 0; Op (Const 0) []] NONE]] NONE)
    | CopyByte T => (* TODO: this should eventually be implemented in data_to_word instead for efficiency *)
      Let (if LENGTH c1 < 3 then (c1 ++ REPLICATE 3 (Op (Const 0) [])) else c1)
        (Let [Op (RefByte T) [Op (Const 0) []; Var 0]]
           (Let [Op (CopyByte F) [Op (Const 0) []; Var 0; Var 1; Var 2; Var 3]]
             (Var 1)))
    | Label l => Op (Label (bvl_num_stubs + bvl_to_bvi_namespaces * l)) c1
    | _ => Op op c1`
in
val compile_op_def = Define compile_op_quotation;

Theorem compile_op_pmatch = Q.prove(
  `∀op c1.` @
    (compile_op_quotation |>
     map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq)),
   rpt strip_tac
   >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
   >> fs[compile_op_def]);
end

val _ = temp_overload_on("++",``SmartAppend``);
val _ = temp_overload_on("nss",``bvl_to_bvi_namespaces``);

val compile_aux_def = Define`
  compile_aux (k,args,p) =
    List[(num_stubs + nss * k + 1, args, bvi_let$compile_exp p)]`;

val compile_exps_def = tDefine "compile_exps" `
  (compile_exps n [] = ([],Nil,n)) /\
  (compile_exps n ((x:bvl$exp)::y::xs) =
     let (c1,aux1,n1) = compile_exps n [x] in
     let (c2,aux2,n2) = compile_exps n1 (y::xs) in
       (c1 ++ c2, aux1 ++ aux2, n2)) /\
  (compile_exps n [Var v] = ([(Var v):bvi$exp], Nil, n)) /\
  (compile_exps n [If x1 x2 x3] =
     let (c1,aux1,n1) = compile_exps n [x1] in
     let (c2,aux2,n2) = compile_exps n1 [x2] in
     let (c3,aux3,n3) = compile_exps n2 [x3] in
       ([If (HD c1) (HD c2) (HD c3)],aux1++aux2++aux3,n3)) /\
  (compile_exps n [Let xs x2] =
     if NULL xs (* i.e. a marker *) then
       let (args,x0) = destLet x2 in
       let (c1,aux1,n1) = compile_exps n args in
       let (c2,aux2,n2) = compile_exps n1 [x0] in
       let n3 = n2 + 1 in
         ([Call 0 (SOME (num_stubs + nss * n2 + 1)) c1 NONE],
          aux1++aux2++compile_aux(n2,LENGTH args,HD c2), n3)
     else
       let (c1,aux1,n1) = compile_exps n xs in
       let (c2,aux2,n2) = compile_exps n1 [x2] in
         ([Let c1 (HD c2)], aux1++aux2, n2)) /\
  (compile_exps n [Raise x1] =
     let (c1,aux1,n1) = compile_exps n [x1] in
       ([Raise (HD c1)], aux1, n1)) /\
  (compile_exps n [Tick x1] =
     let (c1,aux1,n1) = compile_exps n [x1] in
       ([Tick (HD c1)], aux1, n1)) /\
  (compile_exps n [Op op xs] =
     let (c1,aux1,n1) = compile_exps n xs in
       ([compile_op op c1],aux1,n1)) /\
  (compile_exps n [Handle x1 x2] =
     let (args,x0) = destLet x1 in
     let (c1,aux1,n1) = compile_exps n args in
     let (c2,aux2,n2) = compile_exps n1 [x0] in
     let (c3,aux3,n3) = compile_exps n2 [x2] in
     let aux4 = compile_aux(n3,LENGTH args,HD c2) in
     let n4 = n3 + 1 in
       ([Call 0 (SOME (num_stubs + nss * n3 + 1)) c1 (SOME (HD c3))],
        aux1++aux2++aux3++aux4, n4)) /\
  (compile_exps n [Call ticks dest xs] =
     let (c1,aux1,n1) = compile_exps n xs in
       ([Call ticks
              (dtcase dest of
               | NONE => NONE
               | SOME n => SOME (num_stubs + nss * n)) c1 NONE],aux1,n1))`
 (WF_REL_TAC `measure (exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (Cases_on `x1`) \\ fs [destLet_def]
  \\ TRY (Cases_on `x2`) \\ fs [destLet_def]
  \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val compile_exps_ind = theorem"compile_exps_ind";

val compile_exps_LENGTH_lemma = Q.prove(
  `!n xs. (LENGTH (FST (compile_exps n xs)) = LENGTH xs)`,
  HO_MATCH_MP_TAC compile_exps_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_exps_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

Theorem compile_exps_LENGTH:
   (compile_exps n xs = (ys,aux,n1)) ==> (LENGTH ys = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_exps_LENGTH_lemma) \\ fs []
QED

Theorem compile_exps_SING:
   (compile_exps n [x] = (c,aux,n1)) ==> ?y. c = [y]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
  \\ Cases_on `c` \\ fs [LENGTH_NIL]
QED

val compile_single_def = Define `
  compile_single n (name,arg_count,exp) =
    let (c,aux,n1) = compile_exps n [exp] in
      (List [(num_stubs + nss * name,arg_count,bvi_let$compile_exp (HD c))]
        ++ aux, n1)`

val compile_list_def = Define `
  (compile_list n [] = (List [],n)) /\
  (compile_list n (p::progs) =
     let (code1,n1) = compile_single n p in
     let (code2,n2) = compile_list n1 progs in
       (code1 ++ code2,n2))`

val compile_inc_def = Define ` (* incremental version used by Install *)
  compile_inc n prog =
    let (p1,n1) = bvl_to_bvi$compile_list n prog in
      (n1,append p1)`

val compile_prog_def = Define `
  compile_prog start n prog =
    let k = alloc_glob_count (MAP (\(_,_,p). p) prog) in
    let (code,n1) = compile_list n prog in
      (InitGlobals_location, bvl_to_bvi$stubs (num_stubs + nss * start) k ++ append code, n1)`;

val _ = Datatype`
  config = <| inline_size_limit : num (* zero disables inlining *)
            ; exp_cut : num (* huge number effectively disables exp splitting *)
            ; split_main_at_seq : bool (* split main expression at Seqs *)
            ; next_name1 : num (* there should be as many of       *)
            ; next_name2 : num (* these as bvl_to_bvi_namespaces-1 *)
            ; inlines : (num # bvl$exp) spt
            |>`;

val default_config_def = Define`
  default_config =
    <| inline_size_limit := 10
     ; exp_cut := 1000
     ; split_main_at_seq := T
     ; next_name1 := num_stubs + 1
     ; next_name2 := num_stubs + 2
     ; inlines := LN
     |>`;

val compile_def = Define `
  compile start c prog =
    let (inlines, prog) = bvl_inline$compile_prog c.inline_size_limit
           c.split_main_at_seq c.exp_cut prog in
    let (loc, code, n1) = compile_prog start 0 prog in
    let (n2, code') = bvi_tailrec$compile_prog (num_stubs + 2) code in
      (loc, code', inlines, n1, n2)`;

val _ = export_theory();
