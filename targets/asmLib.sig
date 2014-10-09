signature asmLib =
sig
   val add_asm_compset: computeLib.compset -> unit
   val asm_ok_rwts: Thm.thm list
   val asm_rwts: Thm.thm list
   val split_bytes_in_memory_tac: int -> Tactic.tactic
   val using_first: int -> (Thm.thm list -> Tactic.tactic) -> Tactic.tactic
end
