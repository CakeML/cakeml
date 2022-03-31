(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;
open sortingTheory arithmeticTheory;

val _ = new_theory "deflate";

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

(* binary numbers in little-endian format *)
Definition tbl2n_def[simp]:
  tbl2n [] = 0n /\
  tbl2n (T::t) = 2*tbl2n t + 1 /\
  tbl2n (F::t) = 2*tbl2n t
End

(* binary numbers in big-endian format *)
Overload TN2BL = “\n. REVERSE (inv_tbl2n n)”

Definition inv_tbl2n_def:
  inv_tbl2n 0n = [] /\
  inv_tbl2n a = if EVEN a then [F]++(inv_tbl2n (a DIV 2))
                else [T]++(inv_tbl2n ((a-1) DIV 2 ))
Termination
  WF_REL_TAC‘$<’ >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac‘v’ >> ‘0<2n’ by simp[] >>
  rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ]
End

Theorem tbl2n_inv_tbl2n[simp]:
  tbl2n (inv_tbl2n n) = n
Proof
  completeInduct_on ‘n’ >> Cases_on‘n’ >> simp[tbl2n_def,inv_tbl2n_def] >>
  Cases_on‘EVEN (SUC n')’ >>
  simp[tbl2n_def]
  >- (‘2 * (SUC n' DIV 2) = (SUC n' DIV 2)*2’ by simp[MULT_COMM] >>
      ‘0<2n’ by simp[] >>
      ‘SUC n' MOD 2=0’ by metis_tac[EVEN_MOD2] >>
      ‘SUC n' DIV 2 * 2 + SUC n' MOD 2 = SUC n'’ by metis_tac[GSYM DIVISION] >>
      fs[])
  >- (‘0<2n’ by simp[] >> ‘n' DIV 2 <= n'’ by simp[DIV_LESS_EQ] >>
      ‘n' DIV 2 < SUC n'’ by
        simp[LESS_EQ_IMP_LESS_SUC] >> fs[] >>
      ‘EVEN n'’ by metis_tac[ODD,EVEN_OR_ODD] >>
      ‘2 * (n' DIV 2) =  (n' DIV 2)*2’ by simp[MULT_COMM] >> ‘0<2n’ by simp[] >>
      ‘n' MOD 2=0’ by metis_tac[EVEN_MOD2] >>
      ‘n' DIV 2 * 2 + n' MOD 2 = n'’ by metis_tac[GSYM DIVISION] >> fs[] )
QED

Definition pad0_def:
  pad0 n bl = PAD_LEFT F n bl
End

Definition get_codes_from_len_def:
  get_codes_from_len  [] n nc = [] ∧
  get_codes_from_len (0::ls) n nc = get_codes_from_len ls (SUC n) nc ∧
  get_codes_from_len (l::ls) n nc =
  let
    code = EL l nc;
    nc = LUPDATE (SUC code) l nc;
  in
      (n, pad0 l $ TN2BL code) :: get_codes_from_len ls (SUC n) nc
End

EVAL “
 let
   ls = [3;3;3;3;3;2;4;4];
   bl = bl_count ls;
   nc = next_code bl;
   codes = get_codes_from_len ls 0 nc;
 in
   codes
   ”;

Definition fixed_huff_tree_def:
  fixed_huff_tree =
   let
     ls = (REPLICATE 144 8) ++ (REPLICATE 112 9) ++ (REPLICATE 24 7) ++ (REPLICATE 8 8);
     bl = bl_count ls;
     nc = next_code bl;
     codes = get_codes_from_len ls 0 nc;
   in
     codes
End
EVAL “fixed_huff_tree”;

(* (5-bit code value, number of extra bits after value, inclusive exclusive range for extra bits) *)
Definition dist_table:
  dist_table =
  [ (0, 0, (1,2));
    (1, 0, (2,3));
    (2, 0, (3,4));
    (3, 0, (4,5));
    (4, 1, (5,7));
    (5, 1, (7,9));
    (6, 2, (9,13));
    (7, 2, (13,17));
    (8, 3, (17,25));
    (9, 3, (25,33));
    (10,4, (33,49));
    (11,4, (49,65));
    (12,5, (65,97));
    (13,5, (97,129));
    (14,6, (129,192));
    (15,6, (193,256));
    (16,7, (257,385));
    (17,7, (385,513));
    (18,8, (513,768));
    (19,8, (769,1025));
    (20,9, (1025,1537));
    (21,9, (1537,2049));
    (22,10,(2049,3073));
    (23,10,(3073,4097));
    (24,11,(4097,6145));
    (25,11,(6145,8193));
    (26,12,(8193,12289));
    (27,12,(12289,16384));
    (28,13,(16384,24576));
    (29,13,(24577,32769));
]
End

val _ = export_theory();
