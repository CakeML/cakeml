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

Definition FLIP_ALIST_def:
  FLIP_ALIST [] = [] ∧
  FLIP_ALIST ((x, y)::t) = (y,x):: FLIP_ALIST t
End

Definition find_match_def:
  find_match []         tab         = ([],[]) ∧
  find_match s          []          = ([],[]) ∧
  find_match (s:string) ((k,v)::ts) =
  let
    prefix = IS_PREFIX s k;
  in
    if prefix then (k,v) else find_match s ts
End

Definition tab_sub_def:
  tab_sub [] tab = [] ∧
  tab_sub (s: string) tab =
  let
    (match, value) = find_match s tab;
  in
    if LENGTH match <= 0
    then
      [". Compression failed."]
    else
      value :: (tab_sub (DROP (LENGTH match) s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\ rw[find_match_def]
  \\ rename1 ‘STRING h t’
  \\ Cases_on ‘t’
  \\ rw[]
  \\ Cases_on ‘match’
  \\ gvs[find_match_def]
  \\ Cases_on ‘match’
  \\ gvs[find_match_def]
End

EVAL “tab_sub "Ahhhhej" [("hhh", "f")]”;


(********************************************)
(*          Generate dictionary             *)
(********************************************)

Definition base_keys_def:
  base_keys = GENLIST (λ x. n2s x) 128
End

Definition extract_fixed_substrings_def:
  extract_fixed_substrings (x::xs) n = if n > LENGTH (x::xs)
                                 then []
                                 else TAKE n (x::xs) :: extract_fixed_substrings xs n
End
EVAL “extract_substrings "asdefg" 2”;

Definition extract_substrings_n:
  extract_substrings_n s n = nub $ FLAT $ GENLIST (λ l. if l < 2 then [] else  extract_fixed_substrings s l) n
End
EVAL “extract_substrings_n "abcdefghij" 4”;

Definition extract_keys_def:
  extract_keys s = base_keys ++ extract_substrings_n s 6
End
EVAL “extract_keys "hejsan svejsan"”;

Definition gen_fix_codes:
  gen_fix_codes n =
  let
    len = (LOG 2 n)+1;
    bit_transform = (λ l. PAD_LEFT #"0" len (num_to_bin_string l));
  in
    GENLIST bit_transform n
End
EVAL “gen_fix_codes 34”;

Definition create_dict_def:
  create_fixed_dict s =
  let
    keys = mergesort (λ x y. LENGTH x > LENGTH y) $ extract_keys s
  in
    ZIP (keys, gen_fix_codes $ LENGTH keys)
End
EVAL “create_fixed_dict "asdfg"”;

Definition lorem_dict:
  lorem_dict = create_fixed_dict "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
End
(*EVAL “lorem_dict”;*)


(***************************************************)
(*      Compression & Expansion functions          *)
(***************************************************)

Definition expansion_def:
  expansion (s:string) =
  let
    prefix = "Compressed: ";
    tab = lorem_dict;
  in
    if IS_PREFIX s prefix
    then tab_sub (DROP (LENGTH prefix) s) (FLIP_ALIST tab)
    else s
End

Definition compression_def:
  compression (s:string) =
  let
    tab = lorem_dict
  in
    "Compressed: " ++ tab_sub s tab
End

Definition compression_proof_def:
  compression_proof (s:string)=
  let
    compr_res = compression s
  in
    if expansion compr_res = s
    then "Compressed: " ++ compr_res
    else "Uncompressed: " ++ s
End

(* WARNING TAKES LONG TIME  *)
EVAL “compression "Lorem ipsum dolor sit amet, consectetur adipiscing elit."”;
EVAL “expansion "Compressed: 000110011000101110000101001000100100000011111000011010000010101000010000000001011000000110000000001100011111"”;
EVAL “let s = "Duis quis quam dolor. Quisque elementum fermentum nunc. Nunc placerat, elit id consectetur sodales, metus urna consequat urna, quis auctor nunc massa " in expansion $ compression s = s”


val _ = export_theory();
