structure testLib = struct

open progToBytecodeTheory stringSyntax optionSyntax;
open pairSyntax;
open intLib;
open bytecodeLabelsTheory wordsLib wordsTheory;
open bytecodeEncodeTheory;

open TextIO;

val _ = computeLib.add_funs [
  astTheory.pat_bindings_def, 
  decLangTheory.prog_to_i3_def,
  CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook) compilerTerminationTheory.compile_def];

val _ = unifyLib.add_unify_compset (computeLib.the_compset)

val _ = computeLib.add_funs [bc_inst_to_string_def, encode_bc_insts_def,
                             encode_bc_inst_def, encode_num_def, encode_loc_def,
                             encode_char_def, bc_loc_to_string_def, dimword_64,
                             int_to_string2_def];

end;

