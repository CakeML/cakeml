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
  encode_LZSS (Lit c)  assoc = encode1 assoc (ORD c) ∧
  encode_LZSS (LenDist (len, dist)) assoc =
  let
    (lnum, lbits, lvalue) = find_in_len_table len;
    (dnum, dbits, dvalue) = find_in_dist_table dist;
    enc_len = (encode1 assoc lnum) ++ (pad0 lbits (TN2BL (len - lvalue)));
    enc_dist = (pad0 5 (TN2BL dnum)) ++ (pad0 dbits (TN2BL (dist - dvalue)))
  in
      enc_len ++ enc_dist
End

EVAL “encode_LZSS (Lit #"g") fixed_huff_tree”;
EVAL “encode_LZSS (LenDist (20, 20)) fixed_huff_tree”;


Definition deflate_encoding_def:
  deflate_encoding [] assoc = [] ∧
  deflate_encoding (l::ls) assoc = encode_LZSS l assoc ++ deflate_encoding ls assoc
End

(* Should handle block level logic *)
Definition deflate_encoding_main_def:
  deflate_encoding_main s =
  let
    lzList = LZSS_compress s;
    lenList = MAP encode_LZSS_len lzList;
    (*assoc_list = unique_huff_tree lenList*)
    assoc_list = fixed_huff_tree
  in
    deflate_encoding lzList assoc_list
End

EVAL “deflate_encoding_main "hej hello hello hejsan"”;


Definition find_decode_match_def:
  find_decode_match s         []  = NONE ∧
  find_decode_match s ((k,v)::ts) =
  if (IS_PREFIX s v)
  then SOME (k,v)
  else find_decode_match s ts
End
(*
(* use find_decode_match to find value stored if num < 256 then return Lit num
   else create LenDist using decode_LZSS_len and decode_LZSS_dist *)

Definition decode_LZSS_def:

End

(* using num from decode_LZSS, parameter, find_in_table, read num calc len  *)
Definition decode_LZSS_len_def:

End

(* reads 5 bits, find_in_table, read num bits calc dist*)
Definition decode_LZSS_dist_def:

End

Definition deflate_decoding_def:
  deflate_decoding bl assoc =
  let
    (lz, bl') = decode_LZSS bl assoc
  in
    lz :: deflate_decoding bl' assoc
End

Definition deflate_decoding_main_def:
  deflate_decoding_main s =
  let
    lzList = deflate_decoding s fixed_huff_tree;
    res = LZSS_decompress lzList
  in
    res
End

EVAL “deflate_decoding_main s”
*)
val _ = export_theory();
