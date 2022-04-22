(*
Script for Huffman encodings.
*)

open preamble;
open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;

val _ = new_theory"huffman";


(******************************************
               Frequencies
*******************************************)

Definition get_freq_def:
  get_freq []      ls = ls ∧
  get_freq (s::ss) ls =
  let
    ls' = (case ALOOKUP ls s of
             NONE => (s,1:num)::ls
           | SOME v => AFUPDKEY s (λ a. a + 1) ls)
  in
    get_freq ss ls'
End

Definition get_frequencies_def:
  get_frequencies input = get_freq input []
End

Definition sort_frequencies_def:
  sort_frequencies ls = QSORT (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
End

(******************************************
             Huffman tree
*******************************************)


Datatype:
  Tree = Empty | Leaf α | Node Tree Tree
End

Definition convert_frequencies_def:
  convert_frequencies ls = MAP (λ (c,(f:num)). (Leaf c, f)) ls
End

Definition create_tree_def:
  create_tree ((Leaf c, f)::[]) = Node (Leaf c) Empty ∧
  create_tree ((c,f)::[]) = c ∧
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
  build_huffman_tree s =
  (let
     freqs = sort_frequencies (convert_frequencies (get_frequencies s))
   in
     create_tree freqs)
End

(******************************************
         Huffman encoding/decoding
*******************************************)

Definition get_huffman_codes_def:
    get_huffman_codes (Leaf c) code ls = (c,code)::ls ∧
    get_huffman_codes (Node ltr rtr) code ls =
    let
      left = get_huffman_codes ltr (code++[F]) ls;
      right = get_huffman_codes rtr (code++[T]) ls
    in
        (left++right)
End

Definition encode_single_huff_val_def:
  encode_single_huff_val ls s =
  let
    res = ALOOKUP ls s
  in
    case res of
      NONE => []
    | SOME b => b
End

Definition encode_huff_def:
  encode ls ss = MAP (encode_single_huff_val ls) ss
End


Definition find_decode_match_def:
  find_decode_match s         []  = NONE ∧
  find_decode_match s ((k,v)::ts) =
  if (IS_PREFIX s v)
  then SOME (k,v)
  else find_decode_match s ts
End

Definition huff_enc_dyn_def:
  huff_enc_dyn l =
  let
    huff_tree = build_huffman_tree l;
    assoc_list = get_huffman_codes huff_tree [] [];
  in
    (huff_tree, assoc_list)
End

(*EVAL “huff_enc_dyn ( MAP encode_LZSS_len  [Lit #"a"; Lit #"a"; Lit #"b"; Lit #"c"; Lit #"c"; Lit #"c"; Lit #"d"])”;*)
EVAL “huff_enc_dyn (MAP ORD "aabcccd")”;


(******************************************
         Canonical huffman codes
******************************************)

Definition gen_zero_codes_def:
  gen_zero_codes n = GENLIST (λ a. (a,[])) (SUC n)
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
    max_val = FOLDL (λ a:num (b:num,_). if a < b then b else a) 0 ls;
    gs = gen_zero_codes max_val;
    as = QSORT (λ (a,_) (b,_). a < b) ls;
  in
    fill_assoc_list gs as
End

Definition len_from_codes_def:
  len_from_codes [] = [] ∧
  len_from_codes ((n,bl)::ns) =
  LENGTH bl :: len_from_codes ns
End

Definition all_lens_def:
  all_lens as = len_from_codes (complete_assoc_list as)
End

Overload MAX_CODE_LENGTH = “16 :num”

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
(* binary numbers in little-endian format *)
Definition tbl2n_def[simp]:
  tbl2n [] = 0n /\
  tbl2n (T::t) = 2*tbl2n t + 1 /\
  tbl2n (F::t) = 2*tbl2n t
End

(* binary numbers in big-endian format *)
Overload TBL2N = “\l. tbl2n (REVERSE l)”

Definition inv_tbl2n_def:
  inv_tbl2n 0n = [] /\
  inv_tbl2n a = if EVEN a then [F]++(inv_tbl2n (a DIV 2))
                else [T]++(inv_tbl2n ((a-1) DIV 2 ))
Termination
  WF_REL_TAC‘$<’ >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac‘v’ >> ‘0<2n’ by simp[] >>
  rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ]
End

Overload TN2BL = “\n. REVERSE (inv_tbl2n n)”

Definition pad0_def:
  pad0 n bl = PAD_LEFT F n bl
End

Definition len_from_codes_inv_aux_def:
  len_from_codes_inv_aux  []     n nc = [] ∧
  len_from_codes_inv_aux (0::ls) n nc = len_from_codes_inv_aux ls (SUC n) nc ∧
  len_from_codes_inv_aux (l::ls) n nc =
  let
    code = EL l nc;
    nc = LUPDATE (SUC code) l nc;
  in
      (n, pad0 l (TN2BL code)) :: len_from_codes_inv_aux ls (SUC n) nc
End

Definition len_from_codes_inv_def:
  len_from_codes_inv ls =
  let
    nc = next_code (bl_count ls)
  in
    len_from_codes_inv_aux ls 0 nc
End

EVAL “
 let
   ls = [3;3;3;3;3;2;4;4];
 in
   len_from_codes_inv ls
    ”;

(* EVAL that tests whether the tree we create from length list is equal to original tree *)
EVAL “ let
   s = MAP ORD "abbbbd";
   (tree, as) = huff_enc_dyn s;
   ls = all_lens as;
   cs = len_from_codes_inv ls;
 in
   (as, cs)”;


(*****************************************
            Unique huff tree
*****************************************)

Definition unique_huff_tree_def:
  unique_huff_tree (l:num list)  =
  let
    huff_tree = build_huffman_tree l;
    assoc_list = get_huffman_codes huff_tree [] [];
    ls = all_lens assoc_list;
    cs = len_from_codes_inv ls;
  in
    (cs, ls)
End

EVAL “unique_huff_tree (MAP ORD "aaaaccb")”;

val _ = export_theory();
