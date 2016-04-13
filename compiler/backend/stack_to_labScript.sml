open preamble stackLangTheory labLangTheory;
local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

val _ = new_theory "stack_to_lab";

val _ = Datatype `
  app_list = List ('a list) | Append app_list app_list`

val append_aux_def = Define `
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))`;

val append_def = Define `
  append l = append_aux l []`;

val no_ret_def = Define `
  no_ret (p:'a stackLang$prog) =
    case p of
    | Halt _ => T
    | Raise _ => T
    | Return _ _ => T
    | Seq p1 p2 => no_ret p1 \/ no_ret p2
    | If _ _ _ p1 p2 => no_ret p1 /\ no_ret p2
    | Call NONE _ _ => T
    | Call (SOME (p1,_,_,_)) _ NONE => no_ret p1
    | Call (SOME (p1,_,_,_)) _ (SOME (p2,_,_)) => no_ret p1 /\ no_ret p2
    | _ => F`

val compile_jump_def = Define `
  (compile_jump (INL n) = LabAsm (Jump (Lab n 0)) 0w [] 0) /\
  (compile_jump (INR r) = Asm (JumpReg r) [] 0)`;

val negate_def = Define `
  (negate Less = NotLess) /\
  (negate Equal = NotEqual) /\
  (negate Lower = NotLower) /\
  (negate Test = NotTest) /\
  (negate NotLess = Less) /\
  (negate NotEqual = Equal) /\
  (negate NotLower = Lower) /\
  (negate NotTest = Test)`

val _ = export_rewrites ["negate_def"];

val _ = temp_overload_on("++",``Append``)

val flatten_def = Define `
  flatten p n m =
    case p of
    | Tick => (List [Asm (Inst (Skip)) [] 0],m)
    | Inst a => (List [Asm (Inst a) [] 0],m)
    | Halt _ => (List [LabAsm Halt 0w [] 0],m)
    | Seq p1 p2 =>
        let (xs,m) = flatten p1 n m in
        let (ys,m) = flatten p2 n m in
          (xs ++ ys, m)
    | If c r ri p1 p2 =>
        let (xs,m) = flatten p1 n m in
        let (ys,m) = flatten p2 n m in
          if (p1 = Skip) /\ (p2 = Skip) then (List [],m)
          else if p1 = Skip then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0],m+1)
          else if p2 = Skip then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             List [Label n m 0],m+1)
          else if no_ret p1 then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             List [Label n m 0] ++ ys,m+1)
          else if no_ret p2 then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0] ++ xs,m+1)
          else
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [LabAsm (Jump (Lab n (m+1))) 0w [] 0; Label n m 0] ++ xs ++
             List [Label n (m+1) 0],m+2)
    | While c r ri p1 =>
        let (xs,m) = flatten p1 n m in
          (List [Label n m 0; LabAsm (JumpCmp (negate c) r ri (Lab n (m+1))) 0w [] 0] ++
           xs ++ List [LabAsm (Jump (Lab n m)) 0w [] 0; Label n (m+1) 0],m+2)
    | Raise r => (List [Asm (JumpReg r) [] 0],m)
    | Return r _ => (List [Asm (JumpReg r) [] 0],m)
    | Call NONE dest _ => (List [compile_jump dest],m)
    | Call (SOME (p1,lr,l1,l2)) dest handler =>
        let (xs,m) = flatten p1 n m in
          (List [LabAsm (LocValue lr (Lab l1 l2)) 0w [] 0;
                 compile_jump dest; Label l1 l2 0] ++ xs ++
           (case handler of
            | NONE => List []
            | SOME (p2,k1,k2) =>
                let (ys,m) = flatten p2 n m in
                  List [LabAsm (Jump (Lab n m)) 0w [] 0; Label k1 k2 0] ++
                  ys ++ List [Label n m 0]),
           if IS_SOME handler then m+1 else m)
    | JumpLower r1 r2 target =>
        (List [LabAsm (JumpCmp Lower r1 (Reg r2) (Lab target 0)) 0w [] 0],m)
    | FFI ffi_index _ _ lr => (List [LabAsm (LocValue lr (Lab n m)) 0w [] 0;
                                     LabAsm (CallFFI ffi_index) 0w [] 0;
                                     Label n m 0],m+1)
    | LocValue i l1 l2 => (List [LabAsm (LocValue i (Lab l1 l2)) 0w [] 0],m)
    | _  => (List [],m)`

val prog_to_section_def = Define `
  prog_to_section (n,p) =
    let (lines,m) = (flatten p n (next_lab p)) in
      Section n (append (Append lines (List [Label n m 0])))`

val _ = Datatype`config =
  <| reg_names : num num_map
   ; max_heap : num
   |>`;

val compile_def = Define `
  compile c c2 c3 sp prog =
    let prog = stack_alloc$compile c2 prog in
    let prog = stack_remove$compile c.max_heap c3.bitmaps sp InitGlobals_location prog in
    let prog = stack_names$compile c.reg_names prog in
      MAP prog_to_section prog`;

val _ = export_theory();
