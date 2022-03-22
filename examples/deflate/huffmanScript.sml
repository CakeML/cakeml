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


Definition get_freq_def:
  get_freq [] ls tot = (ls, tot) ∧
  get_freq (s::ss) ls tot =
  let
    ls' = (case ALOOKUP ls s of
             NONE => (s,1)::ls
           | SOME n => AFUPDKEY s (n. n+1) ls)
  in
    get_freq ss ls' tot+1
End
Definition get_frequencies_def:
  get_frequencies input = get_freq input [] 0
End
EVAL “get_frequencies "aaabbc"”;

Definition create_tree_def:

End


Definition fixed_huffman_main_def:

End


Definition dynamic_huffman_main_def:

End

val _ = export_theory();
