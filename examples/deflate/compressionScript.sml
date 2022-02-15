(*
First simple compressor
*)

(*
Haskell inspired pseudo code for a simple compressor and decompressor

-- Datatype for our lookup table
Type Table = [(String, String)]

findSymbol :: String -> Table -> (String, String)

translateSymbol :: String -> Table -> String


compr :: String -> Table -> String:
compr str(s:ss) tab = do
      let n = findNumRepeatingChar s ss
      let out = lookup ( repeat n s ) tab
      return  out ++ compr (drop n str) tab
compr [] tab =  return ""

decompr :: String -> Table -> String
decompr str tab = do
        let sym, left = findSymbol str tab
        let out = translateSymbol sym tab
        return out ++ decompr left tab

-- When changing to dynamic
-- createTable :: String -> Table

*)

open preamble;
open stringLib stringTheory;
open rich_listTheory;
open alistTheory;


val _ = new_theory "compression";

(*
Function that find how many repeating char can be found counting from the first char in the string
*)



(*
Table for stored keys and values for a Dictionary compressor
Properties:
* no dulicate values
* no key is a prefix to another key

compr :: String -> Table -> String:
compr str(s:ss) tab = do
      let n = findNumRepeatingChar s ss
      let out = lookup ( repeat n s ) tab
      return  out ++ compr (drop n str) tab
compr [] tab =  return ""

*)


Definition findRptChar_def:
  findRptChar [] : num = 1 ∧
  findRptChar ((x::y::xs): char list) = if x = y then 1 + findRptChar (y::xs) else 1
End

Definition splitAt_def:
  splitAt s n = (TAKE n s, DROP n s)
End

Definition compr_def:
  compr [] tab = [] ∧
  compr (s: string) (tab: string |-> string) =
  let
    n = findRptChar s;
    (rpt, rest) = splitAt s n;
    code = FLOOKUP tab rpt;
    cout = case code of
             SOME x => x
           | NONE => rpt;
  in
    cout :: (compr rest tab)
Termination
  WF_REL_TAC ‘measure $ λ(s, _). LENGTH s’ THEN cheat
End

EVAL “compr "hhhej" FEMPTY ”


Definition decompr_def:
  decompr a = a
End

val _ = export_theory();
