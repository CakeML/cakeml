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

Overload MAX_CODE_LENGTH = “16 :num”


(******************************************
        Read tree from num list
******************************************)

Definition bl_count_aux_def:
  bl_count_aux [] (bl: num list) = LUPDATE 0 0 bl ∧
  bl_count_aux (x::xs) bl =
  let
val = EL x bl;
new_bl = LUPDATE (SUC val) x bl
  in
    bl_count_aux xs new_bl
End

Definition bl_count_def:
  bl_count l = bl_count_aux l (GENLIST (λ x. 0) MAX_CODE_LENGTH)
End

EVAL “bl_count [3;3;3;3;3;2;4;4]”;

Definition next_code_aux_def:
  next_code_aux max (n:num) (code:num) bl codes =
  if n < max
  then
      let
         code = (code + (EL (n-1) bl)) * 2
       in
         next_code_aux max (SUC n) code bl (SNOC code codes)
  else
      codes
Termination
  WF_REL_TAC ‘measure $ λ(max, s, _, _, _). max - s’
End

Definition index_largest_nonzero_def:
  index_largest_nonzero ([]: num list) (ci:num) (hi:num) = hi ∧
  index_largest_nonzero (x::xs) ci hi =
  let
    i = if x = 0 then hi else ci
  in
      index_largest_nonzero xs (1 + ci) i
End

Definition next_code_def:
  next_code (bl:num list) =
  let
    max = index_largest_nonzero bl 0 0
  in
    next_code_aux (max+1) 1 0 bl [0]
End

EVAL “next_code (bl_count [3;3;3;3;3;2;4;4])”;

(*  From kraft_ineq  *)
Definition inv_tbl2n_def:
  inv_tbl2n 0n = [] /\
  inv_tbl2n a = if EVEN a then [F]++(inv_tbl2n (a DIV 2))
                else [T]++(inv_tbl2n ((a-1) DIV 2 ))
Termination
  WF_REL_TAC‘$<’ >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac‘v’ >> ‘0<2n’ by simp[] >>
  rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ]
End
(* binary numbers in big-endian format *)
Overload TN2BL = “\n. REVERSE (inv_tbl2n n)”

Definition pad0_def:
  pad0 n bl = PAD_LEFT F n bl
End

Definition len_from_codes_inv_def:
  len_from_codes_inv  [] n nc = [] ∧
  len_from_codes_inv (0::ls) n nc = len_from_codes_inv ls (SUC n) nc ∧
  len_from_codes_inv (l::ls) n nc =
  let
    code = EL l nc;
    nc = LUPDATE (SUC code) l nc;
  in
      (n, pad0 l (TN2BL code)) :: len_from_codes_inv ls (SUC n) nc
End

EVAL “
 let
   ls = [3;3;3;3;3;2;4;4];
   bl = bl_count ls;
   nc = next_code bl;
   codes = len_from_codes_inv ls 0 nc;
 in
   codes
   ”;

Definition gen_zero_codes_def:
  gen_zero_codes l 0 = APPEND [(0,[])] l ∧
  gen_zero_codes (l: (num # bool list) list) (n: num) =
  if (0 < n)
  then (gen_zero_codes (APPEND [(n,[])] l) (n-1))
  else (l)
End

Definition fill_assoc_list_def:
  fill_assoc_list gs [] = gs ∧
  fill_assoc_list [] ls = [] ∧
  fill_assoc_list ((n1,bl1)::gs) ((n2,bl2)::ls) =
  if (n1 = n2)
  then ([(n1, bl2)] ++ fill_assoc_list gs ls)
  else ([(n1, bl1)] ++ fill_assoc_list gs ((n2,bl2)::ls))
End

Definition complete_assoc_list_def:
  complete_assoc_list ls =
  let
    gs = gen_zero_codes [] 287;
    as = QSORT (λ (a,_) (b,_). a < b) ls;
  in
    fill_assoc_list gs ls
End

Definition len_from_codes_def:
  len_from_codes [] = [] ∧
  len_from_codes ((n,bl)::ns) =
  LENGTH bl :: len_from_codes ns
End

Definition all_lens_def:
  all_lens as = len_from_codes (complete_assoc_list as)
End


(* EVAL that tests whether the tree we create from length list is equal to original tree *)
EVAL “ let
   s = MAP ORD "abbbbd";
   (tree, as) = huff_enc_dyn s;
   s_enc = encode s as;
   ls = all_lens as;
   cs = len_from_codes_inv ls 0 (next_code (bl_count ls));
 in
   (as, cs)”;

Definition fixed_huff_tree_def:
  fixed_huff_tree =
   let
     ls = (REPLICATE 144 8) ++ (REPLICATE 112 9) ++ (REPLICATE 24 7) ++ (REPLICATE 8 8);
     bl = bl_count ls;
     nc = next_code bl;
     codes = len_from_codes_inv ls 0 nc;
   in
     codes
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
