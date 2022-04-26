(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;
open sortingTheory arithmeticTheory;
open LZSSTheory;
open huffmanTheory;

val _ = new_theory "deflate";


Definition fixed_len_tree_def:
  fixed_len_tree =
   let
     ls = (REPLICATE 144 8) ++ (REPLICATE 112 9) ++ (REPLICATE 24 7) ++ (REPLICATE 8 8);
   in
     len_from_codes_inv ls
End

Definition fixed_dist_tree:
  fixed_dist_tree = GENLIST (λ n. (n, pad0 5 (TN2BL n))) 32
End


(******************************************
               Deflate table
*******************************************)

(* (5-bit code value, number of extra bits after value, inclusive exclusive range for extra bits) *)
Definition dist_table_def:
  dist_table : (num # num # num) list =
  [ (0,   0,     1);
    (1,   0,     2);
    (2,   0,     3);
    (3,   0,     4);
    (4,   1,     5);
    (5,   1,     7);
    (6,   2,     9);
    (7,   2,    13);
    (8,   3,    17);
    (9,   3,    25);
    (10,  4,    33);
    (11,  4,    49);
    (12,  5,    65);
    (13,  5,    97);
    (14,  6,   129);
    (15,  6,   193);
    (16,  7,   257);
    (17,  7,   385);
    (18,  8,   513);
    (19,  8,   769);
    (20,  9,  1025);
    (21,  9,  1537);
    (22, 10,  2049);
    (23, 10,  3073);
    (24, 11,  4097);
    (25, 11,  6145);
    (26, 12,  8193);
    (27, 12, 12289);
    (28, 13, 16384);
    (29, 13, 24577);
]
End

(* (5-bit code value, number of extra bits after value, inclusive exclusive range for extra bits) *)
Definition len_table_def:
  len_table : (num # num # num) list =
  [ (257, 0,   3);
    (258, 0,   4);
    (259, 0,   5);
    (260, 0,   6);
    (261, 0,   7);
    (262, 0,   8);
    (263, 0,   9);
    (264, 0,  10);
    (265, 1,  11);
    (266, 1,  13);
    (267, 1,  15);
    (268, 1,  17);
    (269, 2,  19);
    (270, 2,  23);
    (271, 2,  27);
    (272, 2,  31);
    (273, 3,  35);
    (274, 3,  43);
    (275, 3,  51);
    (276, 3,  59);
    (277, 4,  67);
    (278, 4,  83);
    (279, 4,  99);
    (280, 4, 115);
    (281, 5, 131);
    (282, 5, 163);
    (283, 5, 195);
    (284, 5, 227);
    (285, 0, 258);
]
End

Definition find_level_in_table_def:
  find_level_in_table v [] prev = prev ∧
  find_level_in_table v (((curr, bits, value): num # num # num)::tab) prev  =
  if value <= v
  then find_level_in_table v tab (curr, bits, value)
  else prev
End

Definition find_level_in_len_table_def:
  find_level_in_len_table n = find_level_in_table n len_table (HD len_table)
End

Definition find_in_dist_table_def:
  find_level_in_dist_table n = find_level_in_table n dist_table (HD dist_table)
End


Definition find_code_in_table_def:
  find_code_in_table v [] = (0,0,0) ∧
  find_code_in_table v (((code, bits, value): num # num # num)::tab)  =
  if v = code
  then (code, bits, value)
  else find_code_in_table v tab
End

Definition clen_position_def:
  clen_position : num list =
  [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15;]
End

(*********************************
       Run length encoding
*********************************)

Definition rle_table_def:
  rle_table : (num # num # num) =
  (16,2,3)
End

Definition rle0_table_def:
  rle0_table : (num # num # num) list =
  [
    (17, 3, 3);
    (18, 7, 11)
  ]
End


Definition add_repetition_def:
  add_repetition clen r =
  if  r = 1
  then [(clen, r)]
  else if clen = 0 ∧ 3 ≤ r
  then let
         (code, bits, value) = find_level_in_table r rle0_table (HD rle0_table);
       in
         [(code, r)]
  else if 3 < r
  then let
         (code, bits, value) = rle_table;
         r' = r-1;
         n = (r'-3) DIV 6;
         r'' = r' - 6*n;
         base = if 6 < r''
                then [(code,((r''-3)));(code, 3)]
                else
                  if  r'' = 0
                  then []
                  else [(code, r'')];
       in (clen,1):: REPLICATE n (code, 6) ++ base
  else REPLICATE r (clen, 1)
End

Definition find_repeat_def:
  find_repeat      []            prev  n      = add_repetition prev n ∧
  find_repeat ((l::ls):num list) prev (n:num) =
  case l = prev of
    T => if ((l = 0 ∧ n = 138) ∨ (l ≠ 0 ∧ 6 < n))
         then (add_repetition l n) ++ find_repeat ls l 1
         else find_repeat ls prev (SUC n)
  | F => (add_repetition prev n) ++ find_repeat ls l 1
End


Definition encode_rle_aux_def:
  encode_rle_aux            []  tree = [] ∧
  encode_rle_aux ((clen,r)::ls) tree =
  if  r = 1
  then (encode_single_huff_val tree clen) ++ encode_rle_aux ls tree
  else  let
          (code, bits, value) =  if clen = 16
                                 then rle_table
                                 else find_code_in_table clen rle0_table;
          enc = (encode_single_huff_val tree clen) ++ (pad0 bits (TN2BL (r - value)));
        in
         enc ++ encode_rle_aux ls tree
End

Definition encode_rle_def:
  encode_rle (l::ls) =
  let
    repeat = find_repeat ls l 1;
    (repeat_tree, repeat_alph) = unique_huff_tree (MAP FST repeat);
    enc = encode_rle_aux repeat repeat_tree;
  in
    (enc, repeat_tree, repeat_alph, repeat)
End

EVAL “
 let
   ls = [0;0;0;0;1;1;1;1;1;2;2;2;3];
   (enc, clen_tree, clen_alph, r) = encode_rle ls;
   (output, rest) = decode_rle enc (LENGTH ls) clen_tree
 in
   (ls, r, clen_tree, [],[],[],[],enc)
”;

Definition decode_repeating_def:
  decode_repeating bl code prev =
  case code < 16 of
    T => ([code], 0, code)
  | F => if code = 16
         then
           let
             (code, bits, value) = rle_table;
             clens = REPLICATE (TBL2N (TAKE bits bl) + value) prev;
           in
             (clens, bits, prev)
         else
           let
             (code, bits, value) = find_code_in_table code rle0_table;
             clens = REPLICATE (TBL2N (TAKE bits bl) + value) 0;
           in
             (clens, bits, 0)
End

Definition decode_rle_aux_def:
  decode_rle_aux bl clens_rem tree acc prev =
  if clens_rem <= 0
  then (acc, bl)
  else
    case find_decode_match bl tree of
      NONE => ([], []) (* Something went wrong, huffman can't find match *)
    | SOME (code, bits) =>
        case bits of
          [] => ([], []) (* Something went wrong, huffman match should never be empty *)
        | _  => (let
                   (clens, extra_bits, new_prev) = decode_repeating (DROP (LENGTH bits) bl) code prev;
                 in
                   decode_rle_aux
                   (DROP (extra_bits + (LENGTH bits)) bl)
                   (clens_rem - (1 + (LENGTH clens - 1))) (* Ugly shit that is there to satisfy the termination proof *)
                   tree
                   (acc++clens)
                   new_prev)
Termination
  WF_REL_TAC ‘measure $ λ (_, clens_rem, _, _, _). clens_rem’
End

Definition decode_rle_def:
  decode_rle bl clens_rem tree =
  case find_decode_match bl tree of
    NONE => ([], []) (* Something went wrong, huffman can't find match *)
  | SOME (code, bits) =>
      case bits of
        [] => ([], []) (* Something went wrong, huffman match should never be empty *)
      | _ =>  decode_rle_aux (DROP (LENGTH bits) bl) (clens_rem - 1) tree [code] code
                             (*The first is guaranteed to be a code length and not a repetition since there is no previous code to repeat yet*)
End

EVAL “
 let
   ls = [0;0;0;0;1;1;1;1;1;2;2;2;3];
   (enc, clen_tree, clen_alph, r) = encode_rle ls;
   (output, rest) = decode_rle_aux enc (LENGTH ls) clen_tree [] 0;
 in
   (ls, output, clen_tree, enc, r)
”;

(******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
******************************************
             Deflate encoding
*******************************************)

Overload END_BLOCK = “256:num”;

Definition find_LZSS_val_def:
  find_LZSS_val l : num # num =
  case l of
    Lit c => (ORD c, 0)
  | LenDist (l, d) =>
      let
        (lnum, _, _) = find_level_in_len_table l;
        (dnum, _, _) = find_level_in_dist_table d;
      in
        (lnum, dnum)
End

Definition encode_LZSS_table_def:
  encode_LZSS_table n table_func tree  =
  let
    (code, bits, value) = table_func n;
  in
    (encode_single_huff_val tree code) ++ (pad0 bits (TN2BL (n - value)))
End

(* Encodes each LZSS *)
Definition encode_LZSS_def:
  encode_LZSS (Lit c) len_tree dist_tree = encode_single_huff_val len_tree (ORD c) ∧
  encode_LZSS (LenDist (len, dist)) len_tree dist_tree =
  let
    enc_len  = encode_LZSS_table len  (find_level_in_len_table)  len_tree;
    enc_dist = encode_LZSS_table dist (find_level_in_dist_table) dist_tree;
  in
      enc_len ++ enc_dist
End

EVAL “encode_LZSS (Lit #"g") fixed_len_tree”;
EVAL “encode_LZSS (LenDist (3,3)) fixed_len_tree”;

Definition deflate_encoding_def:
  deflate_encoding [] len_tree dist_tree = [] ∧
  deflate_encoding (l::ls) len_tree dist_tree =
  encode_LZSS l len_tree dist_tree ++ deflate_encoding ls len_tree dist_tree
End

Definition split_len_dist:
  split_len_dist       []  ls ds = (ls, ds) ∧
  split_len_dist (lz::lzs) ls ds =
  let
    (a, b) = find_LZSS_val lz;
  in
    case a < 257 of
      T => split_len_dist lzs (a::ls) ds
    | F => split_len_dist lzs (a::ls) (b::ds)
End

EVAL “
 let
   lzList = LZSS_compress "hejsan hejsan";
   (lenList, distList) = split_len_dist lzList [] [];
 in
   (lenList, distList)
”;

Definition max_fst_pair_def:
  max_fst_pair ls : num = FOLDL (λ a (b,_). if a < b then b else a) (FST $ HD ls) ls
End

Definition encode_clen_pos_def:
  encode_clen_pos alph = REVERSE $ FOLDL (λ ls i. (EL i alph)::ls ) [] clen_position
End

Definition trim_zeroes_end_def:
  trim_zeroes_end (alph:num list) =
  let
    zeroes = FOLDL (λ n clen. if clen = 0 then n+1 else 0) 0 alph;
  in
    BUTLASTN zeroes alph
End

Definition encode_clen_alph_def:
  encode_clen_alph (alph: num list) =
  let
    alph = trim_zeroes_end $ encode_clen_pos $ PAD_RIGHT 0 19 alph;
    CLEN_bits = FLAT ( MAP (λa. (pad0 3 (TN2BL a))) alph);
    NCLEN = LENGTH alph
  in
    (NCLEN, CLEN_bits)
End

Definition deflate_encoding_main_def:
  deflate_encoding_main s fix =
  case fix of
    T =>
      ( let
          BTYPE = [F; T];
          lzList = LZSS_compress s;
          (len_tree, dist_tree) = (fixed_len_tree, fixed_dist_tree);
        in
          BTYPE++
          (deflate_encoding lzList len_tree dist_tree)
      )
  | F =>
      let
        lzList = LZSS_compress s;
        (lenList, distList) = split_len_dist lzList [] [];
        (*    Build huffman tree for len/dist       *)
        (len_tree,  len_alph)  = unique_huff_tree lenList;
        (dist_tree, dist_alph) = unique_huff_tree distList;
        (*    Build huffman tree for len/dist codelengths    *)
        len_dist_alph = (len_alph ++ dist_alph);
        (*    Encode len/dist codelengths                    *)
        (lendist_alph_enc, clen_tree, clen_alph, _) = encode_rle len_dist_alph;
        (NCLEN_num, CLEN_bits) = encode_clen_alph clen_alph;
        (*    Setup header bits                              *)
        BTYPE = [T; F];
        NLIT  = pad0 5 $ TN2BL ((MIN (max_fst_pair len_tree) 257)  - 257);
        NDIST = pad0 5 $ TN2BL ((max_fst_pair dist_tree) - 1);
        NCLEN = pad0 4 $ TN2BL (NCLEN_num - 4);
        header_bits = BTYPE ++ NLIT ++ NDIST ++ NCLEN;
      in
        header_bits ++
        CLEN_bits ++
        lendist_alph_enc ++
        (deflate_encoding lzList len_tree dist_tree)
End

EVAL “deflate_encoding_main "hejsan hejsan" F”;

(************************************
          Deflate Decoding
************************************)

Definition decode_LZSS_table_def:
  decode_LZSS_table lzvalue bl table =
  let
    (lzvalue', bits, value) = find_code_in_table lzvalue table;
    lz = TBL2N (TAKE bits bl) + value;
  in
    (lz, bits)
End

Definition decode_LZSS_lendist:
  decode_LZSS_lendist lznum bl dist_tree =
  let
    (len, lbits) = decode_LZSS_table lznum bl len_table;
    dist_res = find_decode_match bl dist_tree;
    lz =  case dist_res of
            NONE => (LenDist (len,0),0) (* Something went wrong, huffman can't decode *)
          | SOME (dist_huff, bits) =>
              let
                (dist, dbits) = decode_LZSS_table dist_huff (DROP ((LENGTH bits) + lbits) bl) dist_table;
              in
                (LenDist (len, dist), lbits + (LENGTH bits) + dbits)
  in
    lz
End

Definition decode_LZSS_def:
  decode_LZSS (lznum:num) bl dist_tree =
  case lznum < END_BLOCK of
    T => (Lit $ CHR lznum, 0)
  | F => decode_LZSS_lendist lznum bl dist_tree
End

Definition decode_check_end_block:
  decode_check_end_block bl len_tree =
  case find_decode_match bl len_tree of
    NONE => (T, [], 0, []) (* Something went wrong, huffman can't decode *)
  | SOME (lznum, bits) =>
      case lznum = END_BLOCK of
        T => (T, DROP (LENGTH bits) bl, END_BLOCK, bits) (* End block *)
      | F => (F, bl, lznum, bits)
End

Definition deflate_decoding_def:
  deflate_decoding [] len_tree dist_tree acc = (acc, []) ∧
  deflate_decoding bl len_tree dist_tree acc =
  case decode_check_end_block bl len_tree  of
    (T, bl', _, _) => (acc, bl')
  | (F, bl', lznum, bits) =>
      case bits of
        [] => (acc, bl)
      | _ =>  (let
                 (lz, extra_bits) = decode_LZSS lznum (DROP (LENGTH bits) bl) dist_tree
               in
                 deflate_decoding (DROP (extra_bits + (LENGTH bits)) bl) len_tree dist_tree (acc++[lz]))
Termination
  WF_REL_TAC ‘measure $ λ (bl, len_tree, dist_tree, acc). LENGTH bl’
  \\ rw[decode_check_end_block, find_decode_match_def, decode_LZSS_def, decode_LZSS_table_def, decode_LZSS_def]
End

Definition read_dyn_header_def:
  read_dyn_header bl =
  let
    NLIT = TBL2N (TAKE 5 bl) + 257;
    bl = DROP 5 bl;
    NDIST = TBL2N (TAKE 5 bl) + 1;
    bl = DROP 5 bl;
    NCLEN = TBL2N (TAKE 4 bl) + 4;
    bl = DROP 4 bl;
  in
    (NLIT, NDIST, NCLEN, bl)
End

Definition read_clen_def:
  read_clen bl 0 = [] ∧
  read_clen bl (SUC CLEN) = TBL2N (TAKE 3 bl) :: read_clen (DROP 3 bl) CLEN
End

Definition recreate_clen_def:
  recreate_clen []   _        res = res ∧
  recreate_clen (cl::clen) (clp::clen_pos) res =
  recreate_clen clen clen_pos (LUPDATE cl clp res)
End

Definition decode_clen_def:
  decode_clen bl nclen =
  let
    clens = read_clen bl nclen;
    clens = recreate_clen clens clen_position (GENLIST (λn. 0) 19);
  in
    (len_from_codes_inv clens, DROP (3*nclen) bl)
End

Definition deflate_decoding_main_def:
  deflate_decoding_main (b1::b2::bl) =
  if b1 = F ∧ b2 = T
  then
    ( let
        (len_tree, dist_tree) = (fixed_len_tree, fixed_dist_tree);
        (lzList, bl') = deflate_decoding bl len_tree dist_tree [];
        res = LZSS_decompress lzList
      in
        (res, bl'))
  else if b1 = T ∧ b2 = F
  then
    ( let
        (NLIT, NDIST, NCLEN, bl) = read_dyn_header bl;
        (clen_tree, bl') = decode_clen bl NCLEN;
        (len_dist_alph, bl'') = decode_rle bl' (NLIT + NDIST) clen_tree;
        len_alph = TAKE (NLIT + 257) len_dist_alph;
        dist_alph = DROP (NLIT + 257) len_dist_alph;

        len_tree = len_from_codes_inv len_alph;
        dist_tree = len_from_codes_inv dist_alph;

        (lzList, bl''') = deflate_decoding bl'' len_tree dist_tree [];
        res = LZSS_decompress lzList;
      in
        (res, bl''')
    )
  else ("", [])
End

(* Fixed Huffman *)
EVAL “let
        inp = "hejhejhellohejsanhello";
        enc =  deflate_encoding_main inp T;
        (dec, rest) = deflate_decoding_main enc;
      in
        (inp, dec)
     ”;

(* Dynamic Huffman*)
EVAL “let
        inp = "hejhejhellohejsanhello";
        enc =  deflate_encoding_main inp F;
        (dec, rest) = deflate_decoding_main enc;
      in
        (inp, dec)
     ”;

EVAL “
 let
   inp = "hejsan hejsan";
   lzList = LZSS_compress inp;
   (lenList, distList) = split_len_dist lzList [] [];
   (*    Build huffman tree for len/dist       *)
   (len_tree,  len_alph)  = unique_huff_tree lenList;
   (dist_tree, dist_alph) = unique_huff_tree distList;
   (*    Build huffman tree for len/dist codelengths    *)
   len_dist_alph = (len_alph ++ dist_alph);
   (*    Encode len/dist codelengths                    *)
   (lendist_alph_enc, clen_tree, clen_alph, _) = encode_rle len_dist_alph;
   (NCLEN_num, CLEN_bits) = encode_clen_alph clen_alph;
   (*    Setup header bits                              *)
   BTYPE = [T; F];
   NLIT  = pad0 5 $ TN2BL ((MIN (max_fst_pair len_tree) 257)  - 257);
   NDIST = pad0 5 $ TN2BL ((max_fst_pair dist_tree) - 1);
   NCLEN = pad0 4 $ TN2BL (NCLEN_num - 4);
   header_bits = BTYPE ++ NLIT ++ NDIST ++ NCLEN;
   enc = header_bits ++
         CLEN_bits ++
         lendist_alph_enc ++
         (deflate_encoding lzList len_tree dist_tree);
   enc = DROP 2 enc;
   bl = enc;
   (NLIT', NDIST', NCLEN', bl) = read_dyn_header bl;
   (clen_tree', bl') = decode_clen bl NCLEN';
   (len_dist_alph', bl'') = decode_rle bl' (NLIT' + NDIST') clen_tree';
   (aa, ab) = decode_rle lendist_alph_enc (LENGTH len_dist_alph) clen_tree';
   len_alph' = TAKE (NLIT' + 257) len_dist_alph';
   dist_alph' = DROP (NLIT' + 257) len_dist_alph';
   len_tree' = len_from_codes_inv len_alph';
   dist_tree' = len_from_codes_inv dist_alph';
   (lzList, bl''') = deflate_decoding  bl'' len_tree' dist_tree' [];
   res = LZSS_decompress lzList;

   ls = [11;12;0;0;0;0;0;0;0;0;0;0;14;0;13;6;6;6;5;4;4;4;4;4;4;2;2;15;1;2;2;2;2];
   (enc, clen_tree, clen_alph, _) = encode_rle ls;
   (output, rest) = decode_rle enc (LENGTH ls) clen_tree;
 in
   (ls, output)
”;



val _ = export_theory();
