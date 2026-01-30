signature asmLib =
sig
   val add_asm_ok_thm: Thm.thm -> unit
   val add_asm_compset: computeLib.compset -> computeLib.compset
   val asm_cases_tac: Term.term Abbrev.quotation -> Tactic.tactic
   val asm_ok_rwts: Thm.thm list
   val asm_rwts: Thm.thm list
   val byte_eq_tac: Tactical.tactic
   val dest_bytes_in_memory:
      Term.term -> Term.term * Term.term * Term.term * Term.term
   val env_tac:
      (Term.term * Term.term -> Term.term * Tactic.tactic) -> Tactic.tactic
   val find_env:
      (Term.term -> bool) -> Term.term -> (Term.term * Term.term) option
   val isAddCarry: Term.term -> bool
   val isAddOverflow: Term.term -> bool
   val isArith: Term.term -> bool
   val isBinop: Term.term -> bool
   val isCall: Term.term -> bool
   val isConst: Term.term -> bool
   val isFP: Term.term -> bool
   val isInst: Term.term -> bool
   val isJump: Term.term -> bool
   val isJumpCmp: Term.term -> bool
   val isJumpReg: Term.term -> bool
   val isLoc: Term.term -> bool
   val isMem: Term.term -> bool
   val isShift: Term.term -> bool
   val isSkip: Term.term -> bool
   val isSubOverflow: Term.term -> bool
   val mk_blast_thm: Term.term -> Thm.thm
   val mk_bytes_in_memory:
      Term.term * Term.term * Term.term * Term.term -> Term.term
   val print_tac : string -> string -> Tactic.tactic
   val strip_bytes_in_memory: Term.term -> Term.term list option
   val split_bytes_in_memory_tac: int -> Tactic.tactic
   val target_asm_rwts: Thm.thm list -> Term.term -> Thm.thm * Thm.thm
   val using_first: int -> (Thm.thm list -> Tactic.tactic) -> Tactic.tactic
   val v2w_BIT_n2w: int -> Thm.thm
end
