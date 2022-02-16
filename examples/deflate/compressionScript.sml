(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory;
open alistTheory;


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


Definition ALOOKUP_SND_def:
  (ALOOKUP_SND [] q = NONE) /\
  (ALOOKUP_SND ((x,y)::t) q = if y = q then SOME x else ALOOKUP_SND t q)
End

Definition KEYLEN_def:
  KEYLEN []      sm tab :num = 0 ∧
  KEYLEN (s::ss) sm tab :num =
  let
    match = sm ++ [s];
    t = EXISTS (λ(_,y). IS_PREFIX y match) tab;
  in
    if t then (1 + KEYLEN ss match tab) else 0
End

EVAL “KEYLEN "bcdefgh" ""  [("xxxxxx", "bc"); ("YYYYYY", "fg"); ("123", "e")]”


Definition decompr_def:
  decompr [] tab = [] ∧
  decompr (s: string) tab =
  let
    len = KEYLEN s "" tab;
  in
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

EVAL “decompr "aabbbbbcdefgh" [("xxxx", "b"); ("YYYYYY", "fg"); ("123", "e")] ”


val _ = export_theory();
