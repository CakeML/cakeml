(*
Implementation of Huffman Trees and Canonical Huffman codes.
*)
Theory huffman
Libs
  preamble
Ancestors
  alist string list rich_list option pair arithmetic mllist ringBuffer


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
  sort_frequencies ls = sort (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
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
  create_tree ls =
  case ls of
    []                     => Empty
  | ((Empty, f)::[])       => Empty
  | ((Leaf c, f)::[])      => Node (Leaf c) Empty
  | ((Node ltr rtr,f)::[]) => Node ltr rtr
  | ((c1,f1)::(c2,f2)::ls) =>
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
  get_huffman_codes tree code =
  case tree of
    Empty          => []
  | Leaf c         => [(c,code)]
  | (Node ltr rtr) =>
      (let
         left = get_huffman_codes ltr (code++[F]);
         right = get_huffman_codes rtr (code++[T])
       in
         (left++right))
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
    assoc_list = get_huffman_codes huff_tree [];
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
    as = sort (λ (a,_) (b,_). a < b) ls;
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
  bl_count_aux      0      []  d = [1] ∧
  bl_count_aux      0  (l::ls) d = SUC l :: ls ∧
  bl_count_aux (SUC i)     []  d =     d :: bl_count_aux i [] d ∧
  bl_count_aux (SUC i) (l::ls) d =     l :: bl_count_aux i ls d
End

Definition bl_count_def:
  bl_count bl = 0 :: (TL $ FOLDL (λ ls b. bl_count_aux b ls 0 ) [] bl)
End
EVAL “next_code (bl_count [3;3;3;3;3;2;4;4])”;

Definition next_code_aux_def:
  next_code_aux     []  prev :num list = [prev * 2] ∧
  next_code_aux (x::xs) prev =
  let
    new = 2*(x + prev)
  in
    new :: next_code_aux xs new
End

Definition next_code_def:
  next_code ls = 0 :: next_code_aux ls 0
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

Definition canonical_codes_aux_def:
  canonical_codes_aux  []     n nc = [] ∧
  canonical_codes_aux (0::ls) n nc = canonical_codes_aux ls (SUC n) nc ∧
  canonical_codes_aux (l::ls) n nc =
    case oEL l nc of
      NONE => []
    | SOME code =>
        (n, pad0 l (TN2BL code)) :: canonical_codes_aux
                                 ls
                                 (SUC n)
                                 (LUPDATE (SUC code) l nc)
End

Definition canonical_codes_def:
  canonical_codes ls =
  let
    nc = next_code (bl_count ls)
  in
    canonical_codes_aux ls 0 nc
End

EVAL “
 let
   ls = [3;3;3;3;3;2;4;4];
 in
   canonical_codes ls
    ”;

(* EVAL that tests whether the tree we create from length list is equal to original tree *)
EVAL “ let
   s = MAP ORD "abbbbd";
   (tree, as) = huff_enc_dyn s;
   ls = all_lens as;
   cs = canonical_codes ls;
 in
   (as, cs)”;


(*****************************************
            Unique huff tree
*****************************************)

Definition unique_huff_tree_def:
  unique_huff_tree (l:num list)  =
  let
    huff_tree = build_huffman_tree l;
    assoc_list = get_huffman_codes huff_tree [];
    ls = all_lens assoc_list;
    cs = canonical_codes ls;
  in
    (cs, ls)
End

EVAL “unique_huff_tree [5]”;

EVAL “unique_huff_tree []”;

EVAL “canonical_codes [0]”;

EVAL “unique_huff_tree (MAP ORD "aaaaccb")”;
