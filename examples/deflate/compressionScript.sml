(*
First simple compressor
*)
Theory compression
Libs
  preamble stringLib
Ancestors
  string string_num ASCIInumbers rich_list alist list sorting
  mllist arithmetic


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
  tab_sub (s: string) tab =
  if s = "" then []
  else
    let (match, value) = find_match s tab
    in
      if match = [] then ""
      else value ++ (tab_sub (DROP (LENGTH match) s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\ rpt strip_tac
  \\ Cases_on ‘s’
  \\ gvs[find_match_def]
  \\ Cases_on ‘match’
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


Theorem base_keys_contains_all_chars1:
  ∀s. s = STRING h [] ⇒ MEM s base_keys
Proof
  REWRITE_TAC [base_keys_def, listTheory.MEM_GENLIST]
  \\ Cases_on ‘h’
  \\ simp []
  \\ irule_at Any EQ_REFL
  \\ simp []
QED

Theorem base_keys_contains_all_chars2:
  ∀s. s = STRING h [] ⇒ MEM s base_keys
Proof
  Cases_on ‘h’
  \\ simp_tac std_ss [base_keys_def, listTheory.MEM_GENLIST, listTheory.CONS_11]
  \\ metis_tac []
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

Definition LOG2_def:
  LOG2 (n:num) :num = if ((DIV2 n) < 1) then 1 else 1 + LOG2 (DIV2 n)
Termination
  WF_REL_TAC ‘measure $ λ(n). n’
  \\ simp[DIV2_def]
  \\ strip_tac
  \\ Induct_on ‘n’
  \\ rw[]
End

Definition gen_fix_codes:
  gen_fix_codes n =
  let
    len = (LOG2 n);
    bit_transform = (λ l. PAD_LEFT #"0" len (num_to_bin_string l));
  in
    GENLIST bit_transform n
End

Definition create_fixed_dict_def:
  create_fixed_dict s =
  let
    keys = sort (λ x y. LENGTH y < LENGTH x) $ extract_keys s
  in
    ZIP (keys, gen_fix_codes $ LENGTH keys)
End

Definition lorem_dict_def:
  lorem_dict = create_fixed_dict "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
End


(***************************************************)
(*              FLIP_ALIST + Theorems              *)
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
  compress_main (s:string) =
  if decompress (compress s) = s
  then "Compressed: " ++ compress s
  else "Uncompressed: " ++ s
End

Definition decompress_main_def:
  decompress_main s =
  if IS_PREFIX s "Compressed: "
  then decompress (DROP (LENGTH "Compressed: ") s)
  else DROP (LENGTH "Uncompressed: ")  s
End

Theorem compress_main_inv:
 ∀s. decompress_main (compress_main s) = s
Proof
  REWRITE_TAC[decompress_main_def, compress_main_def]
  \\ strip_tac
  \\ CASE_TAC
  \\ simp[]
QED
