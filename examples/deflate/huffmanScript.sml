(*
Script for Huffman encodings.
*)

open preamble;

open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;
open LZSSrbTheory;

val _ = new_theory"huffman";


Datatype:
  tree = leaf α | node tree tree
End


Definition get_frequencies_def:

End


Definition create_tree_def:

End


Definition fixed_huffman_main_def:

End


Definition dynamic_huffman_main_def:

End

val _ = export_theory();
