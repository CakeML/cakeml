(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;

val _ = new_theory "compression";


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


Definition expansion_def:
  expansion (s:string) tab =
  let prefix = "Compressed: " in
               if IS_PREFIX s prefix
               then tab_sub (DROP (LENGTH prefix) s) (FLIP_ALIST tab)
               else s
End

Definition compression_def:
  compression (s:string) tab = "Compressed: " ++ tab_sub s tab
End

Definition compression_proof_def:
  compression (s:string) tab =
  let
    compr_res = compression s tab
  in
    if (((expansion compr_res tab) = s) ∧ (compr_res ≠ s))
    then "Compressed: " ++ compr_res
    else "Uncompressed: " ++ s
End

EVAL “compression "hhhhhhhhej" [("hhh", "f")]”;

EVAL “expansion "Compressed: ffhhej" [("hhh", "f")]”;



val _ = export_theory();
