(*
Implementation of Deflate encoding and decoding
*)
Theory deflate
Ancestors
  string rich_list alist list sorting arithmetic LZSS huffman rle
  deflateTable
Libs
  preamble stringLib


Overload END_BLOCK = “256:num”;

Overload BLOCK_LENGTH = “16383:num”


(******************************************
              Deflate fixed
*******************************************)


Definition fixed_len_tree_def:
  fixed_len_tree =
   let
     ls = (REPLICATE 144 8) ++ (REPLICATE 112 9) ++ (REPLICATE 24 7) ++ (REPLICATE 8 8);
   in
     canonical_codes ls
End

Definition fixed_dist_tree_def:
  fixed_dist_tree = GENLIST (λ n. (n, pad0 5 (TN2BL n))) 32
End

(******************************************
             Deflate encoding
*******************************************)

(***** Encode codelengths for huffman trees  *****)
Definition clen_position_def:
  clen_position : num list =
  [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15;]
End

Definition encode_clen_pos_def:
  encode_clen_pos alph: num list = REVERSE $ FOLDL (λ ls i. (case oEL i alph of NONE => 0 | SOME c => c)::ls ) [] clen_position
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

(***** help functions for encoder *****)
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

Definition split_len_dist_def:
  split_len_dist       []  ls ds = (ls, ds) ∧
  split_len_dist (lz::lzs) ls ds =
  let
    (a, b) = find_LZSS_val lz;
  in
    case a < 257 of
      T => split_len_dist lzs (a::ls) ds
    | F => split_len_dist lzs (a::ls) (b::ds)
End


(***** Encode indiviual LZSS  *****)
Definition encode_LZSS_table_def:
  encode_LZSS_table n table_func tree  =
  let
    (code, bits, value) = table_func n;
  in
    (encode_single_huff_val tree code) ++ (pad0 bits (TN2BL (n - value)))
End

Definition encode_LZSS_def:
  encode_LZSS lz len_tree dist_tree =
  case lz of
    Lit c =>
      encode_single_huff_val len_tree (ORD c)
  | LenDist (len, dist) =>
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

(***** Main encoder functions *****)

Definition encode_uncompressed_def:
  encode_uncompressed s : bool list =
  let
    rest_of_first_byte = [T;T;T;T;T];
    LEN = pad0 16 $ TN2BL $ LENGTH s;
    NLEN = MAP (λ b. if b = T then F else T) LEN;
    input = FLAT $ MAP (λ n. pad0 8 $ TN2BL n) (REVERSE s);
  in
    rest_of_first_byte ++
    LEN ++
    NLEN ++
    input
End

Definition encode_fixed_def:
  encode_fixed lzList : bool list =
  deflate_encoding lzList fixed_len_tree fixed_dist_tree ++
  (encode_single_huff_val fixed_len_tree END_BLOCK)
End

Definition encode_dynamic_def:
 encode_dynamic lzList len_tree len_alph dist_tree dist_alph clen_alph lendist_alph_enc : bool list =
  let
           (NCLEN_num, CLEN_bits) = encode_clen_alph clen_alph;
           (*    Setup header bits                              *)
           NLIT  = pad0 5 $ TN2BL ((MAX (LENGTH len_alph) 257)  - 257);
           NDIST = pad0 5 $ TN2BL ((LENGTH dist_alph) - 1);
           NCLEN = pad0 4 $ TN2BL (NCLEN_num - 4);
           header_bits = NLIT ++ NDIST ++ NCLEN;
      in
        header_bits ++
        CLEN_bits ++
        lendist_alph_enc ++
        (deflate_encoding lzList len_tree dist_tree) ++
        (encode_single_huff_val len_tree END_BLOCK)
End

Definition encode_block_def:
  encode_block [] = [] ∧
  encode_block s  =
  let
    block_input = TAKE (BLOCK_LENGTH) s;
    s' = DROP (BLOCK_LENGTH) s;
    lzList = LZSS_compress block_input;
    (lenList, distList) = split_len_dist lzList [] [];
    (*    Build huffman tree for len/dist       *)
    (len_tree,  len_alph)  = unique_huff_tree (256::lenList);
    (dist_tree, dist_alph) = unique_huff_tree distList;
    longest_code1 = FOLDL (λ e x. if e < x then x else e) 0 (len_alph ++ dist_alph);
    (lendist_alph_enc, clen_tree, clen_alph, _) = encode_rle (len_alph ++ dist_alph);
    longest_code2 = FOLDL (λ e x. if e < x then x else e) 0 clen_alph;
    BFINAL = if s' = [] then [T] else [F];
    enc = if LENGTH dist_tree = 0
          then
            [F;F] ++ encode_uncompressed lenList
          else
            if (LENGTH block_input < 100 ∨ 15 < longest_code1 ∨ 7 < longest_code2)
            then [F;T] ++ encode_fixed lzList
            else [T;F] ++ encode_dynamic lzList len_tree len_alph dist_tree dist_alph clen_alph lendist_alph_enc
  in
    BFINAL ++
    enc ++
    encode_block s'
Termination
  WF_REL_TAC ‘measure $ λ (s). LENGTH s’
  \\ rw[encode_fixed_def, encode_dynamic_def, encode_uncompressed_def]
End

(************************************
          Deflate Decoding
************************************)

(***** Decodes each LZSS *****)
Definition decode_LZSS_table_def:
  decode_LZSS_table lzvalue bl table =
  let
    (lzvalue', bits, value) = find_code_in_table lzvalue table;
    lz = TBL2N (TAKE bits bl) + value;
  in
    (lz, bits)
End

Definition decode_LZSS_lendist_def:
  decode_LZSS_lendist lznum bl dist_tree =
  let
    (len, lbits) = decode_LZSS_table lznum bl len_table;
    dist_res = find_decode_match (DROP lbits bl) dist_tree;
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

Definition decode_check_end_block_def:
  decode_check_end_block bl len_tree =
  case find_decode_match bl len_tree of
    NONE => (T, [], 0, []) (* Something went wrong, huffman can't decode *)
  | SOME (lznum, bits) =>
      case lznum = END_BLOCK of
        T => (T, DROP (LENGTH bits) bl, END_BLOCK, bits) (* End block *)
      | F => (F, bl, lznum, bits)
End

Definition deflate_decoding_def:
  deflate_decoding [] len_tree dist_tree acc drop_bits = (acc, drop_bits) ∧
  deflate_decoding bl len_tree dist_tree acc drop_bits =
  case decode_check_end_block bl len_tree  of
    (T, _, _, bits) => (acc, LENGTH bits + drop_bits)
  | (F, bl', lznum, bits) =>
      case bits of
        [] => (acc, drop_bits)
      | _ =>  (let
                 (lz, extra_bits) = decode_LZSS lznum (DROP (LENGTH bits) bl) dist_tree
               in
                 deflate_decoding
                 (DROP (extra_bits + (LENGTH bits)) bl)
                 len_tree
                 dist_tree
                 (acc++[lz])
                 (drop_bits + extra_bits + LENGTH bits)
              )
Termination
  WF_REL_TAC ‘measure $ λ (bl, len_tree, dist_tree, acc). LENGTH bl’
  \\ rw[decode_check_end_block_def, find_decode_match_def, decode_LZSS_def, decode_LZSS_table_def, decode_LZSS_def]
End


(***** Decode header dynamic *****)
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
  recreate_clen _ [] _ = [] ∧
  recreate_clen [] _ res = res ∧
  recreate_clen (cl::clen) (clp::clen_pos) res =
  recreate_clen clen clen_pos (LUPDATE cl clp res)
End

Definition decode_clen_def:
  decode_clen bl nclen =
  let
    clens = read_clen bl nclen;
    clens = recreate_clen clens clen_position (GENLIST (λn. 0) 19);
  in
    (canonical_codes clens, 3*nclen)
End

(***** Main decoder function *****)

Definition read_literals_def:
  read_literals [] _ = [] ∧
  read_literals bl 0 = [] ∧
  read_literals bl (SUC n) = (CHR $ (TBL2N $ (TAKE 8 bl)) MOD 256) :: (read_literals (DROP 8 bl) n)
End

Definition decode_uncompressed_def:
  decode_uncompressed bl =
  let
    bl' = DROP 5 bl;
    LEN = TBL2N $ TAKE 16 bl';
    bl'' = DROP 16 bl';
    NLEN = TBL2N $ TAKE 16 bl'';
  in
    (read_literals (DROP 16 bl'') LEN, 5 + 2*16 + LEN*8)
End

Definition decode_fixed_def:
  decode_fixed bl =
  let
    (lzList, drop_bits) = deflate_decoding bl fixed_len_tree fixed_dist_tree [] 0;
    res = LZSS_decompress lzList
  in
    (res, drop_bits)
End

Definition decode_dynamic_def:
  decode_dynamic bl =
  let
    (NLIT', NDIST', NCLEN', bl) = read_dyn_header bl;
    (clen_tree', bits) = decode_clen bl NCLEN';
    bl' = DROP bits bl;
    (len_dist_alph', bits') = decode_rle bl' (NLIT' + NDIST') clen_tree';
    bl'' = DROP bits' bl';
    len_alph' = TAKE NLIT' len_dist_alph';
    dist_alph' = DROP NLIT' len_dist_alph';
    len_tree' = canonical_codes len_alph';
    dist_tree' = canonical_codes dist_alph';
    (lzList', drop_bits'') = deflate_decoding  bl'' len_tree' dist_tree' [] 0;
    res = LZSS_decompress lzList';
  in
    (res, 5+5+4+bits+bits'+drop_bits'')
End

Definition decode_block_def:
  decode_block (b0::b1::b2::bl) =
  (let
     (enc, drop_bits) = if      b1 = F ∧ b2 = F
                        then decode_uncompressed bl
                        else if b1 = F ∧ b2 = T
                        then decode_fixed bl
                        else if b1 = T ∧ b2 = F
                        then decode_dynamic bl
                        else ("", 0);
   in
     (if b0 = T
      then enc
      else enc ++ decode_block (DROP drop_bits bl))) ∧
  decode_block ls = []
Termination
  WF_REL_TAC ‘measure $ λ (bl). LENGTH bl’
  \\ rw[decode_fixed_def, decode_dynamic_def, deflate_decoding_def]
End


(***********************************
          Main functions
***********************************)
Definition bl2s_def:
  bl2s [] = [] ∧
  bl2s bl =
  if LENGTH bl ≤  8
  then [CHR $ (TBL2N $ PAD_RIGHT F 8 bl) MOD 256]
  else (CHR $ (TBL2N $ TAKE 8 bl) MOD 256 ) :: bl2s (DROP 8 bl)
Termination
  WF_REL_TAC ‘measure $ λ (bl). LENGTH bl’
  \\ rw[]
End

Definition s2bl_def:
  s2bl [] = [] ∧
  s2bl (c::cs) = (pad0 8 $ TN2BL $ ORD c) ++ s2bl cs
End

Definition deflate_encode_def:
  deflate_encode s = bl2s $ encode_block s
End

Definition deflate_decode_def:
  deflate_decode s = decode_block $ s2bl s
End

Definition deflate_encode_main_def:
  deflate_encode_main s =
  if deflate_decode (deflate_encode s) = s
  then "Compressed: " ++ deflate_encode s
  else "Uncompressed: " ++ s
End

Definition deflate_decode_main_def:
  deflate_decode_main s =
  if IS_PREFIX s "Compressed: "
  then deflate_decode (DROP (LENGTH "Compressed: ") s)
  else DROP (LENGTH "Uncompressed: ")  s
End

Theorem deflate_main_inv:
 ∀s. deflate_decode_main (deflate_encode_main s) = s
Proof
  REWRITE_TAC[deflate_decode_main_def, deflate_encode_main_def]
  \\ strip_tac
  \\ CASE_TAC
  \\ simp[]
QED


