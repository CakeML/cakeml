(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;
open sortingTheory arithmeticTheory;
open LZSSrbTheory;

val _ = new_theory "deflateTable";


(* (5-bit code value, number of extra bits after value, inclusive exclusive range for extra bits) *)
Definition dist_table:
  dist_table =
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
Definition len_table:
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

Definition find_in_table:
  find_in_table v [] prev = prev ∧
  find_in_table v (((curr, bits, value): num # num # num)::tab) prev  =
  if value <= v
  then find_in_table v tab curr
  else prev
End

EVAL “find_in_table 67 len_table ((λ (a, b, c). a) (HD len_table))”;

Definition encode_LZSS_len_def:
  encode_LZSS_len l : num =
  case l of
    Lit c => ORD c
  | LenDist (l, d) => find_in_table l len_table ((λ (a, b, c). a) (HD len_table))
End

EVAL “encode_LZSS_len (Lit #"g")”;
EVAL “encode_LZSS_len (LenDist (20, 20))”;

val _ = export_theory();
