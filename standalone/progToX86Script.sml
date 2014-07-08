open preamble;
open progToBytecodeTheory wordsTheory wordsLib;
open x64_heapTheory x64_code_evalTheory;

val _ = new_theory "progToX86";

val prog_to_x86_64_def = Define `
  prog_to_x86_64 p =
    case prog_to_bytecode real_inst_length p of
       | Failure x => Failure x
       | Success bcs => Success (x64_code 0 bcs)`;

val _ = export_theory ();
