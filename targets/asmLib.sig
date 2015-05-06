signature asmLib =
sig
   val add_asm_compset: computeLib.compset -> unit
   val asm_ok_rwts: Thm.thm list
   val asm_rwts: Thm.thm list
   val byte_eq_tac: Tactical.tactic
   val dest_bytes_in_memory:
      Term.term -> Term.term * Term.term * Term.term * Term.term * Term.term
   val mk_bytes_in_memory:
      Term.term * Term.term * Term.term * Term.term * Term.term -> Term.term
   val strip_bytes_in_memory: Term.term -> Term.term list option
   val split_bytes_in_memory_tac: int -> Tactic.tactic
   val using_first: int -> (Thm.thm list -> Tactic.tactic) -> Tactic.tactic
   val v2w_BIT_n2w: int -> Thm.thm
end
