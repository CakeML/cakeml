open HolKernel bossLib boolLib EmitTeX basis_emitTheory
open bytecode_emitTheory bytecode_x64Theory
val _ = new_theory "bytecode_x64_emit"

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
  []

val defs = map EmitML.DEFN
[IMMEDIATE32_def
,bc2x64_aux_def
,bc_length_x64_def
]

val _ = EmitML.eSML "bytecode_x64" (
EmitML.OPEN["bytecode"]
::EmitML.MLSIGSTRUCT
["type num = numML.num"
,"type int = intML.int"
,"type word8 = wordsML.word8"
,"type word32 = wordsML.word32"
,"type bc_inst = bytecodeML.bc_inst"
]@data@defs)

val _ = export_theory ();
