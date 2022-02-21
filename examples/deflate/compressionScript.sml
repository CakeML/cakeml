(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory alistTheory listTheory;

val _ = new_theory "compression";

(*
Function that find how many repeating char can be found counting from the first char in the string
*)
Definition findRptChar_def:
  findRptChar [] : num = 0 ∧
  findRptChar (x::[]) = 1 ∧
  findRptChar ((x::y::xs): char list) = if x = y then 1 + findRptChar (y::xs) else 1
End

Definition splitAt_def:
  splitAt s n = (TAKE n s, DROP n s)
End

(*
Initial attempt, this however did not take the table into account when picking strings to substitute
*)
Definition compr_def:
  compr [] tab = [] ∧
  compr (s: string) tab =
  let
    n = findRptChar s;
    (rpt, rest) = splitAt s n;
    code = ALOOKUP tab rpt;
    cout = case code of
             SOME x => x
           | NONE => rpt;
  in
    cout ++ (compr rest tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\ rw[splitAt_def]
  \\ rename1 ‘STRING h t’
  \\ Cases_on ‘t’
  \\ rw[findRptChar_def]
End

EVAL “compr "hhhej" [("hhh", "f")]”;


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


Definition key_len_snd_def:
  key_len_snd []      sm tab :num = 0 ∧
  key_len_snd (s::ss) sm tab :num =
  let
    match = sm ++ [s];
    t = EXISTS (λ(_,y). IS_PREFIX y match) tab;
  in
    if t then (1 + key_len_snd ss match tab) else 0
End

EVAL “key_len_snd "bcdefgh" ""  [("xxxxxx", "bc"); ("YYYYYY", "fg"); ("123", "e")]”;

Definition compr_alt_def:
  compr_alt [] tab = [] ∧
  compr_alt (s: string) tab =
  let len = key_len s "" tab in
    if len = 0 then (TAKE 1 s) ++ (compr_alt (DROP 1 s) tab) else
      let
        str = TAKE len s;
        v = ALOOKUP tab str;
        out = (case v of
                SOME x => x
              | NONE => str);
      in
        out ++ (compr_alt (DROP len s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\rw[]
End

EVAL “compr_alt "hhhhej" [("hhh", "f")]”;


Definition ALOOKUP_SND_def:
  ALOOKUP_SND [] q = NONE ∧
  ALOOKUP_SND ((x,y)::t) q = if y = q then SOME x else ALOOKUP_SND t q
End


Definition decompr_def:
  decompr [] tab = [] ∧
  decompr (s: string) tab =
  let len = key_len_snd s "" tab; in
    if len = 0 then (TAKE 1 s) ++ (decompr (DROP 1 s) tab) else
      let
        str = TAKE len s;
        v = ALOOKUP_SND tab str;
        out = case v of
                SOME x => x
              | NONE => str;
      in
        out ++ (decompr (DROP len s) tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’
  \\rw[]
End

EVAL “decompr "3" [("xxxx", "3"); ("YYYYYY", "fg"); ("123", "e")] ”;

Definition compression_def:
  compression (s:string) tab =
  let
    compr_res = compr_alt s tab
  in
    if (((decompr compr_res tab) = s) ∧ (compr_res ≠ s))
    then compr_res
    else "Uncompressed: " ++ s
End

EVAL “compression "hhhhhhhhej" [("hhh", "f")]”;

val _ = export_theory();
