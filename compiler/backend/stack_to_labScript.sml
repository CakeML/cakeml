(*
  This compiler phase maps stackLang programs, which has structure
  such as If, While, Return etc, to labLang programs that are a soup
  of goto-like jumps.
*)
open preamble stackLangTheory labLangTheory;
local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

val _ = new_theory "stack_to_lab";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = temp_overload_on ("Asm",``λa. Asm (Asmi a)``);

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

val _ = temp_overload_on("++",``misc$Append``)

local val flatten_quotation = `
  flatten p n m =
    dtcase p of
    | Tick => (List [Asm (Inst (Skip)) [] 0],F,m)
    | Inst a => (List [Asm (Inst a) [] 0],F,m)
    | Halt _ => (List [LabAsm Halt 0w [] 0],T,m)
    | Seq p1 p2 =>
        let (xs,nr1,m) = flatten p1 n m in
        let (ys,nr2,m) = flatten p2 n m in
          (xs ++ ys, nr1 ∨ nr2, m)
    | If c r ri p1 p2 =>
        let (xs,nr1,m) = flatten p1 n m in
        let (ys,nr2,m) = flatten p2 n m in
          if (p1 = Skip) /\ (p2 = Skip) then (List [],F,m)
          else if p1 = Skip then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0],F,m+1)
          else if p2 = Skip then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             List [Label n m 0],F,m+1)
          else if nr1 then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             List [Label n m 0] ++ ys,nr2,m+1)
          else if nr2 then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0] ++ xs,nr1,m+1)
          else
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [LabAsm (Jump (Lab n (m+1))) 0w [] 0; Label n m 0] ++ xs ++
             List [Label n (m+1) 0],nr1 ∧ nr2,m+2)
    | While c r ri p1 =>
        let (xs,_,m) = flatten p1 n m in
          (List [Label n m 0; LabAsm (JumpCmp (negate c) r ri (Lab n (m+1))) 0w [] 0] ++
           xs ++ List [LabAsm (Jump (Lab n m)) 0w [] 0; Label n (m+1) 0],F,m+2)
    | Raise r => (List [Asm (JumpReg r) [] 0],T,m)
    | Return r _ => (List [Asm (JumpReg r) [] 0],T,m)
    | Call NONE dest handler => (List [compile_jump dest],T,m)
    | Call (SOME (p1,lr,l1,l2)) dest handler =>
        let (xs,nr1,m) = flatten p1 n m in
        let prefix = List [LabAsm (LocValue lr (Lab l1 l2)) 0w [] 0;
                 compile_jump dest; Label l1 l2 0] ++ xs in
        (dtcase handler of
        | NONE => (prefix, nr1, m)
        | SOME (p2,k1,k2) =>
            let (ys,nr2,m) = flatten p2 n m in
              (prefix ++ (List [LabAsm (Jump (Lab n m)) 0w [] 0; Label k1 k2 0] ++
              ys ++ List [Label n m 0]), nr1 ∧ nr2, m+1))
    | JumpLower r1 r2 target =>
        (List [LabAsm (JumpCmp Lower r1 (Reg r2) (Lab target 0)) 0w [] 0],F,m)
    | FFI ffi_index _ _ _ _ lr => (List [LabAsm (LocValue lr (Lab n m)) 0w [] 0;
                                         LabAsm (CallFFI ffi_index) 0w [] 0;
                                         Label n m 0],F,m+1)
    | LocValue i l1 l2 => (List [LabAsm (LocValue i (Lab l1 l2)) 0w [] 0],F,m)
    | Install _ _ _ _ ret =>
      (List [LabAsm (LocValue ret (Lab n m)) 0w [] 0;
      LabAsm Install 0w [] 0;
      Label n m 0],F,m+1)
    | CodeBufferWrite r1 r2 =>
      (List [Asm (Cbw r1 r2) [] 0],F,m)
    | _  => (List [],F,m)`
in
val flatten_def = Define flatten_quotation;

Theorem flatten_pmatch = Q.prove(
  `∀p n m.` @
    (flatten_quotation |>
     map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq)),
   rpt strip_tac
   >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
   >> rpt strip_tac
   >> rw[Once flatten_def,pairTheory.ELIM_UNCURRY] >> every_case_tac >> fs[]);
end

val prog_to_section_def = Define `
  prog_to_section (n,p) =
    let (lines,_,m) = (flatten p n (next_lab p 1)) in
      Section n (append (Append lines (List [Label n m 0])))`

val is_gen_gc_def = Define `
  (is_gen_gc (Generational l) = T) /\
  (is_gen_gc _ = F)`

val _ = Datatype`config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>`;

val compile_def = Define `
 compile stack_conf data_conf max_heap sp offset prog =
   let prog = stack_alloc$compile data_conf prog in
   let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                max_heap sp InitGlobals_location prog in
   let prog = stack_names$compile stack_conf.reg_names prog in
     MAP prog_to_section prog`;

val _ = export_theory();
