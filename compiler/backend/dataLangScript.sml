(*
  The dataLang intermediate lannguage is the last language with a
  functional-programming-style data abstraction.

  dataLang is the next step from BVL/BVI: (1) dataLang is an
  imperative version of BVL/BVI, i.e. operations update state; (2)
  there is a new state component (called space) and an explicit
  MakeSpace operation that increases space. Space is consumed by Ref
  and Cons, and space is reset by Add, Sub, etc.

  The idea is that the MakeSpace calls can be moved around and lumped
  together. This optimisation reduces the number of calls to the
  allocator and, thus, simplifies the program.  The MakeSpace function
  can, unfortunately, not be moved across function calls or bignum
  operations, which can internally call the allocator.

  The MakeSpace command has an optional variable name list. If this
  list is provided, i.e. SOME var_names, then only these variables can
  survive the execution of the MakeSpace command. The idea is that one
  generates MakeSpace X NONE when compiling into dataLang. Then
  optimisations move around and combine MakeSpace commands. Then
  liveness analysis annotates each MakeSpace command with a SOME. The
  translation from dataLang into more concete forms must implement a
  GC that only looks at the variables in the SOME annotations.
*)

open preamble;
local open closLangTheory in end;

val _ = new_theory "dataLang";
val _ = set_grammar_ancestry ["closLang" (* for op *), "misc" (* for num_set *)]

(* --- Syntax of dataLang --- *)
Definition op_space_reset_def:
  (op_space_reset (IntOp Add) = T) /\
  (op_space_reset (IntOp Sub) = T) /\
  (op_space_reset (IntOp Mult) = T) /\
  (op_space_reset (IntOp Div) = T) /\
  (op_space_reset (IntOp Mod) = T) /\
  (op_space_reset (IntOp Less) = T) /\
  (op_space_reset (IntOp LessEq) = T) /\
  (op_space_reset (IntOp Greater) = T) /\
  (op_space_reset (IntOp GreaterEq) = T) /\
  (op_space_reset (BlockOp Equal) = T) /\
  (op_space_reset (BlockOp ListAppend) = T) /\
  (op_space_reset (BlockOp (FromList _)) = T) /\
  (op_space_reset (MemOp RefArray) = T) /\
  (op_space_reset (MemOp (RefByte _)) = T) /\
  (op_space_reset (BlockOp (ConsExtend _)) = T) /\
  (op_space_reset (MemOp (CopyByte new_flag)) = new_flag) /\
  (op_space_reset (MemOp ConfigGC) = T) /\
  (op_space_reset (FFI _) = T) /\
  (op_space_reset _ = F)
End

Definition op_requires_names_def:
  op_requires_names op = (op_space_reset op ∨ (∃n. op = FFI n) ∨
                         (∃new_flag. op = (MemOp (CopyByte new_flag))) ∨
                         (op = MemOp XorByte) ∨
                         (op = Install))
End

Datatype:
  prog = Skip
       | Move num num
       | Call ((num # num_set) option) (* return var, cut-set *)
                          (num option) (* target of call *)
                            (num list) (* arguments *)
                 ((num # prog) option) (* handler: varname, handler code *)
       | Assign num op (num list) (num_set option)
       | Seq prog prog
       | If num prog prog
       | MakeSpace num num_set
       | Raise num
       | Return num
       | Tick
End

Definition mk_ticks_def:
  mk_ticks n e = FUNPOW (Seq Tick) n e
End

val _ = export_theory();
