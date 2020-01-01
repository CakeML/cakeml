(*
  This compiler phase introduces calls past the stack allocation code
  that is present at almost every start of function. A call past stack
  allocation is called a RawCall. RawCalls are introduced to shortcut
  some bookkeeping during tail-calls to known locations, i.e
  `Call NONE (INL dest) ..`.
*)
open preamble stackLangTheory data_to_wordTheory;

val _ = new_theory "stack_rawcall";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* collect stack allocation information *)

Definition seq_stack_alloc_def:
  seq_stack_alloc (p: 'a stackLang$prog) =
    dtcase p of Seq (StackAlloc k) _ => SOME k | _ => NONE
End

Theorem seq_stack_alloc_pmatch:
  seq_stack_alloc (p: 'a stackLang$prog) =
    case p of Seq (StackAlloc k) _ => SOME k | _ => NONE
Proof
  CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true) \\ rw []
  \\ rw[Once seq_stack_alloc_def,pairTheory.ELIM_UNCURRY] \\ every_case_tac \\ fs[]
QED

Definition collect_info_def:
  (collect_info [] f = f) /\
  (collect_info ((n,b:'a stackLang$prog)::xs) f =
     collect_info xs (dtcase seq_stack_alloc b of
                      | NONE => f
                      | SOME k => insert n k f))
End

(* optimise based on stack allocation information *)

Definition dest_case_def:
  dest_case (p: 'a stackLang$prog # 'a stackLang$prog) =
    dtcase p of (StackFree k, Call NONE (INL d) _) => SOME (k,d) | _ => NONE
End

Theorem dest_case_pmatch:
  dest_case (p: 'a stackLang$prog # 'a stackLang$prog) =
    case p of (StackFree k, Call NONE (INL d) _) => SOME (k,d) | _ => NONE
Proof
  CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true) \\ rw []
  \\ rw[Once dest_case_def,pairTheory.ELIM_UNCURRY] \\ every_case_tac \\ fs[]
QED

Definition comp_seq_def:
  comp_seq (p1:'a stackLang$prog) (p2:'a stackLang$prog) i (default:'a stackLang$prog) =
  dtcase dest_case (p1,p2) of
  | SOME (k,dest) =>
      (dtcase lookup dest i of
       | NONE => default
       | SOME l =>
           if l = k then RawCall dest else
           if l < k then Seq (StackFree (k - l)) (RawCall dest) else
               Seq Tick (Seq (StackAlloc (l - k)) (RawCall dest)))
  | _ => default
End

local
val q = `
  comp i (p:'a stackLang$prog) =
    dtcase p of
    | Seq p1 p2 => comp_seq p1 p2 i (Seq (comp i p1) (comp i p2))
    | If c r ri p1 p2 => If c r ri (comp i p1) (comp i p2)
    | While c r ri p1 => While c r ri (comp i p1)
    | Call (SOME (p1,lr,l1,l2)) dest NONE =>
        Call (SOME (comp i p1,lr,l1,l2)) dest NONE
    | Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2)) =>
        Call (SOME (comp i p1,lr,l1,l2)) dest (SOME (comp i p2,k1,k2))
    | _ => p`
in
val comp_def = Define q;
Theorem comp_pmatch = Q.prove(
  `∀i p.` @
    (map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq) q),
  rpt strip_tac
  \\ CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true) \\ rw []
  \\ rw[Once comp_def,pairTheory.ELIM_UNCURRY] \\ every_case_tac \\ fs[]
  \\ rename [`NONE = opt`] \\ Cases_on `opt` \\ fs [] \\ metis_tac [PAIR]);
end

Definition comp_top_def:
  comp_top i (p: 'a stackLang$prog) =
    dtcase p of Seq p1 p2 => Seq (comp i p1) (comp i p2) | _ => comp i p
End

Theorem comp_top_pmatch:
  comp_top i (p: 'a stackLang$prog) =
    case p of Seq p1 p2 => Seq (comp i p1) (comp i p2) | _ => comp i p
Proof
  CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true) \\ rw []
  \\ rw[Once comp_top_def,pairTheory.ELIM_UNCURRY] \\ every_case_tac \\ fs[]
QED

Definition compile_def:
  compile prog =
    let i = collect_info prog LN in
      MAP (\(n,b:'a stackLang$prog). (n,comp_top i b)) prog
End

val _ = export_theory();
