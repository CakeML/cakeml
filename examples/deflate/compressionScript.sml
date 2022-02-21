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

Definition key_len_def:
  key_len []      sm tab :num = 0 ∧
  key_len (s::ss) sm tab :num =
  let
    match = sm ++ [s];
    t = EXISTS (λ(x,_). IS_PREFIX x match) tab;
  in
    if t then (1 + key_len ss match tab) else 0
End

EVAL “key_len "hhhej" "" [("hhh", "f")]”;

Definition tab_sub_def:
  tab_sub [] tab = [] ∧
  tab_sub (s: string) tab =
  let len = key_len s "" tab in
    if len = 0 then (TAKE 1 s) ++ (tab_sub (DROP 1 s) tab) else
      let
        str = TAKE len s;
        v = ALOOKUP tab str;
        out = (case v of
                SOME x => x
              | NONE => str);
      in
        out ++ (tab_sub (DROP len s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\rw[]
End

EVAL “tab_sub "hhhhej" [("hhh", "f")]”;


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
EVAL “expansion "Compressed: 000110000000101000000100000000011000000010000000001000000000000"”;
EVAL “let s = "Duis quis quam dolor. Quisque elementum fermentum nunc. Nunc placerat, elit id consectetur sodales, metus urna consequat urna, quis auctor nunc massa " in expansion $ compression s = s”


val _ = export_theory();
