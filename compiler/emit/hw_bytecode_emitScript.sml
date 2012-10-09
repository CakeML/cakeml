open HolKernel bossLib boolLib EmitTeX basis_emitTheory
open bytecode_emitTheory hw_bytecodeTheory
val _ = new_theory "hw_bytecode_emit"

(*
val _ = Parse.disable_tyabbrev_printing "env"
val _ = Parse.disable_tyabbrev_printing "alist"
*)

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
  [ datatype_hw_instruction
  ]

val defs = map EmitML.DEFN
[ push_fixed_imm_def
, push_imm_def
, hwml_def
, full_hwml_def
, hwml_length_def
, hw_encode_def
]

val _ = EmitML.eSML "hw_bytecode" (
  (EmitML.OPEN ["num","list","bytecode","words"])
::(EmitML.MLSIG "type num = numML.num")
::(EmitML.MLSIG "type bc_inst = bytecodeML.bc_inst")
::(EmitML.MLSIG "type word6 = wordsML.word6")
::(EmitML.MLSIG "type word8 = wordsML.word8")
::data@defs)

val _ = export_theory ();
