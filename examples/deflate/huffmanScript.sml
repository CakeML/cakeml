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
  Tree = Leaf α | Node Tree Tree
End

Definition get_freq_def:
  get_freq [] ls = ls ∧
  get_freq (s::ss) ls =
  let
    ls' = (case ALOOKUP ls s of
             NONE => (s,1:num)::ls
           | SOME n => AFUPDKEY s (λ n. n + 1) ls)
  in
    get_freq ss ls'
End

Definition get_frequencies_def:
  get_frequencies (input:string) = get_freq input []
End

EVAL “get_frequencies "ababca"”;

Definition convert_frequencies_def:
  convert_frequencies ls = MAP (λ (c,(f:num)). (Leaf c, f)) ls
End

EVAL “convert_frequencies (get_frequencies "aaabbc")”;

Definition sort_frequencies_def:
  sort_frequencies ls = QSORT (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
End

EVAL “sort_frequencies (convert_frequencies (get_frequencies "ababca"))”;

Definition create_tree_def:
  create_tree ((c,f)::[]) = [(c,f)] ∧
  create_tree ((c1,f1)::(c2,f2)::ls) =
  (let
     nn = (Node c1 c2, f1+f2)
   in
    create_tree (sort_frequencies (nn::ls)))
Termination
  WF_REL_TAC ‘measure $ λ ls. LENGTH ls’
  \\ rw[sort_frequencies_def]
End

EVAL “let s = sort_frequencies (convert_frequencies (get_frequencies "ababca"))
     in create_tree s”;

Definition build_huffman_tree_def:
  build_huffman_tree (s:string) =
  (let
     freqs = sort_frequencies (convert_frequencies (get_frequencies s))
   in
     FST (HD (create_tree freqs)))
End

EVAL “build_huffman_tree "aaabbc"”

val _ = export_theory();
