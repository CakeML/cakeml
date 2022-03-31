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

val _ = new_theory"huffmanOG";


Datatype:
  Tree = Empty | Leaf α | Node Tree Tree
End


(******************************************
               Frequencies
*******************************************)

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

Definition convert_frequencies_def:
  convert_frequencies ls = MAP (λ (c,(f:num)). (Leaf c, f)) ls
End

Definition sort_frequencies_def:
  sort_frequencies ls = QSORT (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
End


(******************************************
             Huffman tree
*******************************************)

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

Definition build_huffman_tree_def:
  build_huffman_tree (s:string) =
  (let
     freqs = sort_frequencies (convert_frequencies (get_frequencies s))
   in
     FST (HD (create_tree freqs)))
End


(******************************************
              Huffman encoding
*******************************************)

Definition get_huffman_codes_def:
    get_huffman_codes (Leaf c) code ls = (c,code)::ls ∧
    get_huffman_codes (Node ltr rtr) code ls =
    let
      left = get_huffman_codes ltr (code++[T]) ls;
      right = get_huffman_codes rtr (code++[F]) ls
    in
        (left++right)
End

Definition encode_def:
  encode "" ls = [] ∧
  encode ((s::ss):string) ls =
  let
    res = ALOOKUP ls s
  in
    case res of
      NONE => []
    | SOME b => b++encode ss ls
End

Definition huffman_encoding_def:
  huffman_encoding (s:string) =
  let
    huff_tree = build_huffman_tree s;
    assoc_list = get_huffman_codes huff_tree [] []
  in
    (huff_tree, encode s assoc_list)
End

EVAL “huffman_encoding "aabcccd"”;


(******************************************
             Huffman decoding
*******************************************)

Definition decode_char_def:
  decode_char Empty _ = NONE ∧
  decode_char (Leaf (c:char)) [] = SOME c ∧
  decode_char (Leaf (c:char)) code = NONE ∧
  decode_char (Node ltr rtr) [] = NONE ∧
  decode_char (Node ltr rtr) (x::xs) =
  case x of
    T => decode_char ltr xs
  | F => decode_char rtr xs
End

Definition decode_def:
  decode tree ((b::bs) :bool list) ([]   :bool list) :string = (decode tree bs [b]) ∧
  decode tree ([]      :bool list) (code :bool list) :string = (
  let
    res = decode_char tree code
  in
    case res of
      NONE => []
    | SOME (r:char) => [r:char]) ∧
  decode tree ((b::bs) :bool list) (code :bool list) :string = (
  let
    res = decode_char tree code
  in
    case res of
      NONE => decode tree bs (code++[b])
    | SOME (r:char) => [r]++(decode tree bs [b]))
End

EVAL “let
        (tree, code) = huffman_encoding "abbbbbcddd"
      in
     decode tree code []”;

Definition huffman_decoding_def:
  huffman_decoding (tree, code) = decode tree code []
End


EVAL “let
        (tree, code) = huffman_encoding "hejsan svejsan"
      in
        huffman_decoding (tree, code)”;

Definition huffman_enc_main_def:
  huffman_enc_main s =
  if huffman_decoding (huffman_encoding s) = s
  then (huffman_encoding s, s)
  else ((Empty, []), s)
End

Definition huffman_dec_main_def:
  huffman_dec_main ((tree, code), s) =
  if tree ≠ Empty
  then (huffman_decoding (tree, code))
  else s
End

EVAL “let
        ((tree, code), b) = huffman_enc_main "hejsan svejsan"
      in
        huffman_dec_main ((tree, code), b)”;

(*
Theorem huffman_inverse:
  ∀s. huffman_dec_main (huffman_enc_main s) = s
Proof


  REWRITE_TAC[huffman_enc_main_def, huffman_dec_main_def]
  \\ strip_tac
  \\ CASE_TAC
  \\ simp[]


QED
*)









val _ = export_theory();
