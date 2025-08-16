(*
Implementation of Deflate specific Run Length Encoding
*)
Theory rle
Ancestors
  rich_list list deflateTable huffman
Libs
  preamble


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
  encode_rle [] = ([], [], [], []) ∧
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
  decode_rle_aux bl clens_rem tree acc prev drop_bits =
  if clens_rem <= 0
  then (acc, drop_bits)
  else
    case find_decode_match bl tree of
      NONE => ([2], 0) (* Something went wrong, huffman can't find match *)
    | SOME (code, bits) =>
        case bits of
          [] => ([3], 0) (* Something went wrong, huffman match should never be empty *)
        | _  => (let
                   (clens, extra_bits, new_prev) = decode_repeating (DROP (LENGTH bits) bl) code prev;
                 in
                   decode_rle_aux
                   (DROP (extra_bits + (LENGTH bits)) bl)
                   (clens_rem - (1 + (LENGTH clens - 1))) (* Ugly shit that is there to satisfy the termination proof *)
                   tree
                   (acc++clens)
                   new_prev
                   (drop_bits + (LENGTH bits) + extra_bits)
                )
Termination
  WF_REL_TAC ‘measure $ λ (_, clens_rem, _, _, _). clens_rem’
End

Definition decode_rle_def:
  decode_rle bl clens_rem tree = decode_rle_aux bl clens_rem tree [] 0 0
End

EVAL “
 let
   ls = [0;0;0;0;1;1;1;1;10;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;2;2;2;7;7;7;7;7;7];
   (enc, clen_tree, clen_alph, r) = encode_rle ls;
   (output, rest) = decode_rle enc (LENGTH ls) clen_tree;
 in
   (ls, output, LENGTH ls * 8, rest)
”;

