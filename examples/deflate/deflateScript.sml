(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;
open sortingTheory arithmeticTheory;
open LZSSTheory;
open huffmanTheory;
open deflateTableTheory;

val _ = new_theory "deflate";


Definition fixed_huff_tree_def:
  fixed_huff_tree =
   let
     ls = (REPLICATE 144 8) ++ (REPLICATE 112 9) ++ (REPLICATE 24 7) ++ (REPLICATE 8 8);
   in
     len_from_codes_inv ls
End

EVAL “fixed_huff_tree”;

(******************************************
             Deflate encoding
*******************************************)

(* Encodes each LZSS *)
Definition encode_LZSS_def:
  encode_LZSS (Lit a) huff assoc = T ∧
  encode_LZSS (LenDist (a, b)) huff assoc = F
End

Definition deflate_encoding_def:
  deflate_encoding [] huff assoc = [] ∧
  deflate_encoding (l::ls) huff assoc = encode_LZSS l huff assoc :: deflate_encoding ls huff assoc
End

(* Should handle block level logic *)
Definition deflate_encoding_main_def:
  deflate_encoding_main s =
  let
    lzList = LZSS_compress s;
    lenList = MAP encode_LZSS_len lzList;
    (huff_tree, assoc_list) = huff_enc_dyn lenList
  in
    deflate_encoding lzList huff_tree assoc_list
End

EVAL “deflate_encoding_main "hej hello hello hejsan"”;


val _ = export_theory();
