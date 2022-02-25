(*
First simple compressor
*)

open preamble;
open stringLib stringTheory string_numTheory ASCIInumbersTheory;
open rich_listTheory alistTheory listTheory;
open mergesortTheory;
val _ = new_theory "compression";


(********************************************)
(*          Substitution function           *)
(********************************************)

Definition find_match_def:
  find_match s          []          = ([],[]) ∧
  find_match (s:string) ((k,v)::ts) =
  if (IS_PREFIX s k)
  then (k,v)
  else find_match s ts
End

Definition tab_sub_def:
  tab_sub [] tab = [] ∧
  tab_sub (s: string) tab =
  case (find_match s tab) of
  | ([],_) => ""
  | (match, value) => value ++ (tab_sub (DROP (LENGTH match) s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\ rpt strip_tac
  \\ gvs[find_match_def]
End

(********************************************)
(*          Generate dictionary             *)
(********************************************)

Definition base_keys_def:
  base_keys = GENLIST (λ x. [CHR x]) 256
End

Theorem base_keys_not_empty:
  base_keys ≠ []
Proof
  rw[base_keys_def]
QED

Theorem base_keys_length:
  LENGTH base_keys = 256
Proof
  rw[base_keys_def, LENGTH]
QED

Theorem base_keys_contain:

Proof

QED

Definition extract_fixed_substrings_def:
  extract_fixed_substrings [] n = [] ∧
  extract_fixed_substrings (x::xs) n =
  if LENGTH (x::xs) < n
  then []
  else TAKE n (x::xs) :: extract_fixed_substrings xs n
End

Definition extract_substrings_n:
  extract_substrings_n s n =
  nub $ FLAT $ GENLIST (λ l. if l < 2 then [] else  extract_fixed_substrings s l) n
End

Definition extract_keys_def:
  extract_keys s = base_keys ++ extract_substrings_n s 6
End

Definition gen_fix_codes:
  gen_fix_codes n =
  let
    len = (LOG 2 n)+1;
    bit_transform = (λ l. PAD_LEFT #"0" len (num_to_bin_string l));
  in
    GENLIST bit_transform n
End

Definition create_fixed_dict_def:
  create_fixed_dict s =
  let
    keys = mergesort (λ x y. LENGTH y < LENGTH x) $ extract_keys s
  in
    ZIP (keys, gen_fix_codes $ LENGTH keys)
End

Definition lorem_dict_def:
  lorem_dict = create_fixed_dict "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
End


(***************************************************)
(*              FLIP_ALIST + THeorems              *)
(***************************************************)

Definition FLIP_ALIST_def:
  FLIP_ALIST [] = [] ∧
  FLIP_ALIST ((x, y)::t) = (y,x):: FLIP_ALIST t
End

Theorem FLIP_ALIST_EMPTY: FLIP_ALIST [] = []
Proof rw[FLIP_ALIST_def]
QED

Theorem FLIP_ALIST_o:
  ∀x y l. FLIP_ALIST ((x,y)::l) = ((y,x):: FLIP_ALIST l)
Proof
  rpt strip_tac
  \\ Induct_on ‘(x,y)’
  \\ rpt strip_tac
  \\ gvs[FLIP_ALIST_def]
QED

Theorem FLIP_ALIST_inv:
  ∀x y l. FLIP_ALIST (FLIP_ALIST ((x,y)::l)) = ((x,y)::l)
Proof
  rpt strip_tac
  \\ gvs[FLIP_ALIST_o, FLIP_ALIST_def]
  \\ Induct_on ‘l’
  \\ gvs[FLIP_ALIST_o, FLIP_ALIST_def]
  \\ strip_tac
  \\ Cases_on ‘h’
  \\ gvs[FLIP_ALIST_o]
QED

(***************************************************)
(*      Compression & Expansion functions          *)
(***************************************************)


Definition decompress_def:
  decompress (s:string) = tab_sub s (FLIP_ALIST lorem_dict)
End

Definition compress_def:
  compress (s:string) = tab_sub s lorem_dict
End

Definition compress_main_def:
  compress_main (s:string)=
  let
    compr_res = compress s
  in
    if decompress compr_res = s
    then "Compressed: " ++ compr_res
    else "Uncompressed: " ++ s
End

Definition decompress_main_def:
  decompress_main s =
  let
    comp_prefix = "Compressed: "
  in
    if IS_PREFIX s comp_prefix
    then decompress (DROP (LENGTH comp_prefix) s)
    else s
End

Theorem compress_inv:
  ∀s. decompress (compress s) = s
Proof
  strip_tac
  \\ gvs[decompress_def, compress_def, tab_sub_def]
  \\ Cases_on ‘s’
  \\ gvs[decompress_def, compress_def, tab_sub_def]
  \\ Cases_on ‘t’
  \\ rw[decompress_def, compress_def, tab_sub_def, FLIP_ALIST_def]
  \\cheat



QED


Theorem compress_main_inv:
 ∀s. decompress_main (compress_main s) = s
Proof
  strip_tac
  \\ rw[decompression_main_def, compression_main_def]
  \\ cheat


QED




val _ = export_theory();
