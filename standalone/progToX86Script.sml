open preamble;
open progToBytecodeTheory wordsTheory wordsLib;
open bc_compileTheory;

val _ = new_theory "progToX86";

val prog_to_x86_64_def = Define `
  prog_to_x86_64 p =
    case prog_to_bytecode real_inst_length p of
       | Failure x => Failure x
       | Success bcs => Success (bc_compile 0 bcs)`;

val _ = export_theory ();
