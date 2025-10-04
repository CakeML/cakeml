(*
  A compiler phases that transforms BVL programs into BVI programs. As
  part of this phase, certain primitive operations map to "stubs" code
  implemented in BVI; numeric constants are split into smaller ones to
  ease code generation later; Handle is fused with Call; and very
  large expressions are split into samller ones (in order to protect
  the register allocator from overly large inputs).
*)
Theory bvl_to_bvi
Ancestors
  bvl bvi backend_common bvl_inline[qualified]
  bvl_const[qualified] bvl_handle[qualified] bvi_let[qualified]
  bvi_tailrec[qualified] dataLang[qualified]
Libs
  preamble

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition destLet_def:
  (destLet ((Let xs b):bvl$exp) = (xs,b)) /\
  (destLet _ = ([],Var 0))
End

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

val large_int = ``268435457:int``; (* 2**28-1 *)

Definition compile_int_def:
  compile_int (i:int) =
    bvi$Op (if -^large_int ≤ i ∧ i ≤ ^large_int then IntOp (Const i) else BlockOp (Build [Int i])) []
End

Definition alloc_glob_count_def:
  (alloc_glob_count [] = 0:num) /\
  (alloc_glob_count (x::y::xs) =
     alloc_glob_count [x] + alloc_glob_count (y::xs)) /\
  (alloc_glob_count [(Var _):bvl$exp] = 0) /\
  (alloc_glob_count [If x y z] =
     alloc_glob_count [x] +
     alloc_glob_count [y] +
     alloc_glob_count [z]) /\
  (alloc_glob_count [Handle x y] =
     alloc_glob_count [x] +
     alloc_glob_count [y]) /\
  (alloc_glob_count [Tick x] = alloc_glob_count [x]) /\
  (alloc_glob_count [Force loc v] = 0) /\
  (alloc_glob_count [Raise x] = alloc_glob_count [x]) /\
  (alloc_glob_count [Let xs x] = alloc_glob_count (x::xs)) /\
  (alloc_glob_count [Call _ _ xs] = alloc_glob_count xs) /\
  (alloc_glob_count [Op op xs] =
     if op = GlobOp AllocGlobal then 1 + alloc_glob_count xs
                                else alloc_glob_count xs) /\
  (alloc_glob_count [_] = 0) (* Impossible *)
End

Definition global_count_sing_def:
  (global_count_sing ((Var _):bvl$exp) = 0) /\
  (global_count_sing (If x y z) =
     global_count_sing x +
     global_count_sing y +
     global_count_sing z) /\
  (global_count_sing (Handle x y) =
     global_count_sing x +
     global_count_sing y) /\
  (global_count_sing (Force loc v) = 0) /\
  (global_count_sing (Tick x) = global_count_sing x) /\
  (global_count_sing (Raise x) = global_count_sing x) /\
  (global_count_sing (Let xs x) =
     global_count_sing x + global_count_list xs) /\
  (global_count_sing (Call _ _ xs) = global_count_list xs) /\
  (global_count_sing (Op op xs) =
     if op = GlobOp AllocGlobal then 1 + global_count_list xs
                                else global_count_list xs) /\
  (global_count_list [] = 0:num) /\
  (global_count_list (x::xs) =
     global_count_sing x + global_count_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL e => bvl$exp_size e
                            | INR es => bvl$exp1_size es’
  \\ rpt strip_tac \\ simp [bvlTheory.exp_size_def]
End

Theorem alloc_glob_count_eq_global_count_list:
  (∀e. global_count_sing e = alloc_glob_count [e]) ∧
  (∀es. global_count_list es = alloc_glob_count es)
Proof
  Induct \\ gvs [global_count_sing_def,alloc_glob_count_def]
  \\ rw [] \\ Cases_on ‘es’ \\ gvs []
  \\ gvs [global_count_sing_def,alloc_glob_count_def]
QED

Definition AllocGlobal_location_def:
  AllocGlobal_location = data_num_stubs
End
Definition CopyGlobals_location_def:
  CopyGlobals_location = AllocGlobal_location+1
End
Definition InitGlobals_location_def:
  InitGlobals_location = CopyGlobals_location+1
End
Definition ListLength_location_def:
  ListLength_location = InitGlobals_location+1
End
Definition FromListByte_location_def:
  FromListByte_location = ListLength_location+1
End
Definition ToListByte_location_def:
  ToListByte_location = FromListByte_location+1
End
Definition SumListLength_location_def:
  SumListLength_location = ToListByte_location+1
End
Definition ConcatByte_location_def:
  ConcatByte_location = SumListLength_location+1
End

Theorem AllocGlobal_location_eq =
  ``AllocGlobal_location`` |> EVAL
Theorem CopyGlobals_location_eq =
  ``CopyGlobals_location`` |> EVAL
Theorem InitGlobals_location_eq =
  ``InitGlobals_location`` |> EVAL
Theorem ListLength_location_eq =
  ``ListLength_location`` |> EVAL
Theorem FromListByte_location_eq =
  ``FromListByte_location`` |> EVAL
Theorem ToListByte_location_eq =
  ``ToListByte_location`` |> EVAL
Theorem SumListLength_location_eq =
  ``SumListLength_location`` |> EVAL
Theorem ConcatByte_location_eq =
  ``ConcatByte_location`` |> EVAL

Definition AllocGlobal_code_def:
  AllocGlobal_code = (1:num,
    Let [Op (GlobOp GlobalsPtr) []] $
    Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 0]] $
    Let [Op (IntOp Add) [Var 0; Var 2]] $
    Let [Op (MemOp Length) [Var 2]] $
    Let [Op (MemOp Update) [Var 1; Op (IntOp (Const 0)) []; Var 3]] $
      If (Op (IntOp Less) [Var 1; Var 2]) (Var 0)
         (Let [Op (MemOp RefArray) [Op (IntOp (Const 0)) []; Op (IntOp Add) [Var 2; Var 2]]] $
          Let [Op (GlobOp SetGlobalsPtr) [Var 0]] $
            Call 0 (SOME CopyGlobals_location)
              [Var 1; Var 6; Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 3]] NONE))
End

Definition CopyGlobals_code_def:
  CopyGlobals_code = (3:num, (* ptr to new array, ptr to old array, index to copy *)
    Let [Op (MemOp Update) [Op (MemOp El) [Var 2; Var 1]; Var 2; Var 0]]
      (If (Op (BlockOp Equal) [Op (IntOp (Const 0)) []; Var 3]) (Var 0)
        (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 3]] NONE)))
End

Definition InitGlobals_max_def:
  InitGlobals_max = 10000n
End

Definition InitGlobals_code_def:
  InitGlobals_code start n = (0:num,
    let n = MIN (MAX n 1) InitGlobals_max in
      Let [Op (MemOp RefArray) [Op (IntOp (Const 0)) []; Op (IntOp (Const (&n))) []]]
        (Let [Op (MemOp Update) [Op (IntOp (Const 1)) []; Op (IntOp (Const 0)) []; Var 0]]
          (Let [Op (GlobOp SetGlobalsPtr) [Var 1]]
             (Call 0 (SOME start) [] (SOME (Var 0))))))
End

Definition ListLength_code_def:
  ListLength_code = (2n, (* ptr to array, accumulated length *)
    If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0])
      (Var 1) (Call 0 (SOME ListLength_location)
                [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 0];
                 Op (IntOp Add) [Var 1; Op (IntOp (Const 1)) []]] NONE))
End

Definition FromListByte_code_def:
  FromListByte_code = (3n, (* list, current index, byte array *)
    If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0]) (Var 2)
      (Let [Op (MemOp UpdateByte) [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 0]; Var 1; Var 2]]
        (Call 0 (SOME FromListByte_location)
          [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 1];
           Op (IntOp Add) [Var 2; Op (IntOp (Const 1)) []];
           Var 3] NONE)))
End

Definition ToListByte_code_def:
  ToListByte_code = (3n, (* list, current index, byte array *)
    If (Op (BlockOp (EqualConst (Int 0i))) [Var 1]) (Var 0)
      (Let [Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 1]]
      (Let [Op (MemOp DerefByte) [Var 0; Var 3]]
        (Call 0 (SOME ToListByte_location)
          [Op (BlockOp (Cons 0)) [Var 2; Var 0];
           Var 1;
           Var 4] NONE))))
End

Definition SumListLength_code_def:
  SumListLength_code = (2n, (* ptr to list, accumulated length *)
    If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0])
      (Var 1)
      (Call 0 (SOME SumListLength_location)
         [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 0];
          Op (IntOp Add) [Var 1; Op (MemOp LengthByte)
                           [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 0]]]] NONE))
End

Definition ConcatByte_code_def:
  ConcatByte_code = (3n, (* list, current index, destination *)
    If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0]) (Var 2)
      (Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 0]]
        (Let [Op (MemOp LengthByte) [Var 0]]
          (Let [Op (MemOp (CopyByte F))
                  [Var 3; Var 4; Var 0; Op (IntOp (Const 0)) []; Var 1]]
            (Call 0 (SOME ConcatByte_location)
              [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 3];
               Op (IntOp Add) [Var 4; Var 1];
               Var 5] NONE)))))
End

Definition stubs_def:
  stubs start n = [(AllocGlobal_location, AllocGlobal_code);
                   (CopyGlobals_location, CopyGlobals_code);
                   (InitGlobals_location, InitGlobals_code start n);
                   (ListLength_location, ListLength_code);
                   (FromListByte_location, FromListByte_code);
                   (ToListByte_location, ToListByte_code);
                   (SumListLength_location, SumListLength_code);
                   (ConcatByte_location, ConcatByte_code)]
End

Overload num_stubs[local] = ``backend_common$bvl_num_stubs``

local val compile_op_quotation = `
  compile_op op c1 =
    dtcase op of
    | IntOp (Const i) =>
      (dtcase c1 of [] => compile_int i
      | _ => Let [Op (IntOp (Const 0)) c1] (compile_int i))
    | GlobOp (Global n) =>
      (if NULL c1 then Op (GlobOp (Global (n+1))) []
      else Let c1 (Op (MemOp El) [
        Op (IntOp Add) [Op (IntOp (Const 2)) []; Var 0];
        Op (GlobOp GlobalsPtr) []]))
    | GlobOp (SetGlobal n) => Op (GlobOp (SetGlobal (n+1))) c1
    | GlobOp AllocGlobal => Call 0 (SOME AllocGlobal_location) c1 NONE
    | BlockOp (FromList n) => Let
        (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
        (Op (BlockOp (FromList n))
        [Var 0; Call 0 (SOME ListLength_location) [Var 0; Op (IntOp (Const 0)) []] NONE])
    | Install => Let
      (if LENGTH c1 <> 2
       then [Let c1 (Op (IntOp (Const 0)) []); Op (IntOp (Const 0)) []] else c1)
      (Op Install
       [Call 0 (SOME ListLength_location)
          [Var 0; Op (IntOp (Const 0)) []] NONE;
        Call 0 (SOME ListLength_location)
          [Var 1; Op (IntOp (Const 0)) []] NONE;
        Var 0; Var 1])
    | MemOp FromListByte =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME FromListByte_location)
             [Var 0;
              Op (IntOp (Const 0)) [];
              Op (MemOp (RefByte T))
                [Op (IntOp (Const 0)) [];
                 Call 0 (SOME ListLength_location)
                   [Var 0; Op (IntOp (Const 0)) []] NONE]]
             NONE)
    | MemOp ToListByte =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME ToListByte_location)
             [Op (BlockOp (Cons 0)) [];
              Op (MemOp LengthByte) [Var 0];
              Var 0]
             NONE)
    | MemOp ConcatByteVec =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME ConcatByte_location)
            [Var 0;
             Op (IntOp (Const 0)) [];
             Op (MemOp (RefByte T))
               [Op (IntOp (Const 0)) [];
                Call 0 (SOME SumListLength_location)
                  [Var 0; Op (IntOp (Const 0)) []] NONE]] NONE)
    | MemOp (CopyByte T) => (* TODO: this should eventually be implemented in data_to_word instead for efficiency *)
      Let (if LENGTH c1 < 3 then (c1 ++ REPLICATE 3 (Op (IntOp (Const 0)) [])) else c1)
        (Let [Op (MemOp (RefByte T)) [Op (IntOp (Const 0)) []; Var 0]]
           (Let [Op (MemOp (CopyByte F)) [Op (IntOp (Const 0)) []; Var 0; Var 1; Var 2; Var 3]]
             (Var 1)))
    | Label l => Op (Label (bvl_num_stubs + bvl_to_bvi_namespaces * l)) c1
    | BlockOp (Build ps) => Op (BlockOp (Build ps)) c1
    | BlockOp (EqualConst p) => Op (BlockOp (EqualConst p)) c1
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

Overload "++"[local] = ``SmartAppend``
Overload "nss"[local] = ``bvl_to_bvi_namespaces``

Definition compile_aux_def:
  compile_aux (k,args,p) =
    List[(num_stubs + nss * k + 1, args, bvi_let$compile_exp p)]
End

Definition compile_exps_def:
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
  (compile_exps n [Force loc v] =
     ([Force (num_stubs + nss * loc) v], Nil, n)) /\
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
               | SOME n => SOME (num_stubs + nss * n)) c1 NONE],aux1,n1))
Termination
  WF_REL_TAC `measure (exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (Cases_on `x1`) \\ fs [destLet_def]
  \\ TRY (Cases_on `x2`) \\ fs [destLet_def]
  \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC
End

Definition compile_exps_sing_def:
  (compile_exps_sing n (Var v) = (((Var v):bvi$exp), Nil, n)) /\
  (compile_exps_sing n (If x1 x2 x3) =
     let (c1,aux1,n1) = compile_exps_sing n x1 in
     let (c2,aux2,n2) = compile_exps_sing n1 x2 in
     let (c3,aux3,n3) = compile_exps_sing n2 x3 in
       (If c1 c2 c3,aux1++aux2++aux3,n3)) /\
  (compile_exps_sing n (Let xs x2) =
     if NULL xs (* i.e. a marker *) then
       let (args,x0) = destLet x2 in
       let (c1,aux1,n1) = compile_exps_list n args in
       let (c2,aux2,n2) = compile_exps_sing n1 x0 in
       let n3 = n2 + 1 in
         ((Call 0 (SOME (num_stubs + nss * n2 + 1)) c1 NONE),
          aux1++aux2++compile_aux(n2,LENGTH args,c2), n3)
     else
       let (c1,aux1,n1) = compile_exps_list n xs in
       let (c2,aux2,n2) = compile_exps_sing n1 x2 in
         ((Let c1 (c2)), aux1++aux2, n2)) /\
  (compile_exps_sing n (Raise x1) =
     let (c1,aux1,n1) = compile_exps_sing n x1 in
       (Raise c1, aux1, n1)) /\
  (compile_exps_sing n (Tick x1) =
     let (c1,aux1,n1) = compile_exps_sing n x1 in
       (Tick c1, aux1, n1)) /\
  (compile_exps_sing n (Force loc v) =
     (Force (num_stubs + nss * loc) v, Nil, n)) /\
  (compile_exps_sing n (Op op xs) =
     let (c1,aux1,n1) = compile_exps_list n xs in
       (compile_op op c1,aux1,n1)) /\
  (compile_exps_sing n (Handle x1 x2) =
     let (args,x0) = destLet x1 in
     let (c1,aux1,n1) = compile_exps_list n args in
     let (c2,aux2,n2) = compile_exps_sing n1 x0 in
     let (c3,aux3,n3) = compile_exps_sing n2 x2 in
     let aux4 = compile_aux(n3,LENGTH args,c2) in
     let n4 = n3 + 1 in
       ((Call 0 (SOME (num_stubs + nss * n3 + 1)) c1 (SOME c3)),
        aux1++aux2++aux3++aux4, n4)) /\
  (compile_exps_sing n (Call ticks dest xs) =
     let (c1,aux1,n1) = compile_exps_list n xs in
       ((Call ticks
              (dtcase dest of
               | NONE => NONE
               | SOME n => SOME (num_stubs + nss * n)) c1 NONE),aux1,n1)) /\
  (compile_exps_list n [] = ([],Nil,n)) /\
  (compile_exps_list n ((x:bvl$exp)::xs) =
     let (c1,aux1,n1) = compile_exps_sing n x in
     let (c2,aux2,n2) = compile_exps_list n1 xs in
       (c1::c2, aux1 ++ aux2, n2))
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (n,e) => exp_size e
                                    | INR (n,es) => exp1_size es’
  \\ rpt strip_tac
  \\ rpt $ qpat_x_assum ‘(_,_,_) = _’ kall_tac
  \\ gvs [bvlTheory.exp_size_def]
  \\ gvs [oneline destLet_def, AllCaseEqs(), bvlTheory.exp_size_def]
End

Theorem compile_exps_sing:
  (∀n e. compile_exps n [e] =
         (let (x,y,z) = compile_exps_sing n e in ([x],y,z))) ∧
  (∀n es. compile_exps_list n es = compile_exps n es)
Proof
  ho_match_mp_tac compile_exps_sing_ind \\ rpt strip_tac
  \\ gvs [compile_exps_def,compile_exps_sing_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rpt IF_CASES_TAC \\ gvs []
  \\ Cases_on ‘es’ \\ gvs []
  \\ gvs [compile_exps_def,compile_exps_sing_def,SmartAppend_Nil]
QED

Triviality compile_exps_LENGTH_lemma:
  !n xs. (LENGTH (FST (compile_exps n xs)) = LENGTH xs)
Proof
  HO_MATCH_MP_TAC compile_exps_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_exps_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC
QED

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

Definition compile_single_def:
  compile_single n (name,arg_count,exp) =
    let (c,aux,n1) = compile_exps n [exp] in
      (List [(num_stubs + nss * name,arg_count,bvi_let$compile_exp (HD c))]
        ++ aux, n1)
End

Theorem compile_single_eq:
  compile_single n (name,arg_count,exp) =
    let (c,aux,n1) = compile_exps_sing n exp in
      (List [(num_stubs + nss * name,arg_count,bvi_let$compile_exp c)]
        ++ aux, n1)
Proof
  gvs [compile_single_def,compile_exps_sing]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Definition compile_list_def:
  (compile_list n [] = (List [],n)) /\
  (compile_list n (p::progs) =
     let (code1,n1) = compile_single n p in
     let (code2,n2) = compile_list n1 progs in
       (code1 ++ code2,n2))
End

Definition compile_inc_def: (* incremental version used by Install *)
  compile_inc n prog =
    let (p1,n1) = bvl_to_bvi$compile_list n prog in
      (n1,append p1)
End

Definition compile_prog_def:
  compile_prog start n prog =
    let k = alloc_glob_count (MAP (\(_,_,p). p) prog) in
    let (code,n1) = compile_list n prog in
      (InitGlobals_location, bvl_to_bvi$stubs (num_stubs + nss * start) k ++ append code, n1)
End

Theorem compile_prog_eq =
  compile_prog_def |> SRULE [GSYM alloc_glob_count_eq_global_count_list];

Datatype:
  config = <| inline_size_limit : num (* zero disables inlining *)
            ; exp_cut : num (* huge number effectively disables exp splitting *)
            ; split_main_at_seq : bool (* split main expression at Seqs *)
            ; next_name1 : num (* there should be as many of       *)
            ; next_name2 : num (* these as bvl_to_bvi_namespaces-1 *)
            ; inlines : (num # bvl$exp) spt
            |>
End

Definition default_config_def:
  default_config =
    <| inline_size_limit := 10
     ; exp_cut := 1000
     ; split_main_at_seq := T
     ; next_name1 := num_stubs + 1
     ; next_name2 := num_stubs + 2
     ; inlines := LN
     |>
End

Definition get_names_def:
  get_names final_nums old_names =
    fromAList (MAP (λn. (n,
      if n = InitGlobals_location then mlstring$strlit "start" else
      if n = AllocGlobal_location then mlstring$strlit "AllocGlobal" else
      if n = CopyGlobals_location then mlstring$strlit "CopyGlobals" else
      if n = ListLength_location then mlstring$strlit "ListLength" else
      if n = FromListByte_location then mlstring$strlit "FromListByte" else
      if n = ToListByte_location then mlstring$strlit "ToListByte" else
      if n = SumListLength_location then mlstring$strlit "SumListLength" else
      if n = ConcatByte_location then mlstring$strlit "ConcatByte" else
      if n < num_stubs then mlstring$strlit "bvi_unknown" else
        let k = n - num_stubs in
        let kd = k DIV nss in
        let km = k MOD nss in
        let n = (dtcase lookup kd old_names of
          | NONE => mlstring$strlit "bvi_unmapped"
          | SOME name => name) in
        let aux = (if km = 0 then mlstring$strlit "" else mlstring$strlit "_bvi_aux") in
          n ^ aux)) final_nums)
End

Definition compile_def:
  compile start c names prog =
    let (inlines, prog) = bvl_inline$compile_prog c.inline_size_limit
           c.split_main_at_seq c.exp_cut prog in
    let (loc, code, n1) = compile_prog start 0 prog in
    let (n2, code') = bvi_tailrec$compile_prog (num_stubs + 2) code in
      (loc, code', inlines, n1, n2, get_names (MAP FST code') names)
End

Definition bvl_to_bvi_compile_inc_all_def:
  bvl_to_bvi_compile_inc_all c p =
    let (inl, p) = bvl_inline$compile_inc c.inline_size_limit
        c.split_main_at_seq c.exp_cut c.inlines p in
    let c = c with <| inlines := inl |> in
    let (nn1, p) = bvl_to_bvi$compile_inc c.next_name1 p in
    let c = c with <| next_name1 := nn1 |> in
    let (nn2, p) = bvi_tailrec$compile_prog c.next_name2 p in
    let c = c with <| next_name2 := nn2 |> in
      (c, p)
End

