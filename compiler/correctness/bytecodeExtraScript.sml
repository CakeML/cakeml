open HolKernel bossLib boolLib boolSimps lcsymtacs
open bytecodeTerminationTheory
val _ = intLib.deprecate_int()
val _ = new_theory"bytecodeExtra"

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bump_pc_with_stack = store_thm("bump_pc_with_stack",
  ``bump_pc (s with stack := st) = (bump_pc s) with stack := st``,
  rw[bump_pc_def,bc_fetch_with_stack] >>
  BasicProvers.EVERY_CASE_TAC)

val bc_fetch_aux_MAP = store_thm("bc_fetch_aux_MAP",
  ``!il f. (∀x. il (f x) = il x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
      ∀ls n. (bc_fetch_aux (MAP f ls) il n = OPTION_MAP f (bc_fetch_aux ls il n))``,
  ntac 2 gen_tac >> strip_tac >>
  Induct >> rw[bc_fetch_aux_def])

val bc_fetch_MAP = store_thm("bc_fetch_MAP",
  ``∀f s. (∀x. s.inst_length (f x) = s.inst_length x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
    (bc_fetch (s with <| code := MAP f s.code |>) = OPTION_MAP f (bc_fetch s))``,
  rw[bc_fetch_def,bc_fetch_aux_MAP])

val bc_find_loc_aux_NONE = store_thm("bc_find_loc_aux_NONE",
  ``∀il l ls n. (bc_find_loc_aux ls il l n = NONE) ⇒ ¬MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac >> fs[])

val bc_find_loc_aux_MEM = store_thm("bc_find_loc_aux_MEM",
  ``∀il l ls n. (bc_find_loc_aux ls il l n ≠ NONE) ⇒ MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac)

val dest_Label_def = Define`(dest_Label (Label n) = n)`
val _ = export_rewrites["dest_Label_def"]

val _ = export_theory()
