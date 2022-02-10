(*
First simple compressor
*)

(*
Haskell inspired pseudo code for a simple compressor and decompressor

-- Datatype for our lookup table
Type Table = [(String, String)]

lookup :: String -> Table -> String

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

findNumRepeatingChar :: Char -> String -> Num
findNumRepeatingChar    c str(s:ss) | c == s    = return 1 + find... c ss
                                    | otherwise = return 0
findNumRepeatingChar    c []                    = return 0

-- When changing to dynamic
-- createTable :: String -> Table

*)

open preamble;

open stringLib stringTheory;

open rich_listTheory;
open pathTheory;

Definition append_char_def:
  append_char s (c:char) = s ++ [c]
End

Definition remove_last_def:
  remove_last ((x::[]): char list)  = [] ∧
  remove_last ((x::xs ): char list) = [x] ++ remove_last xs
End

EVAL “remove_last (append_char "hello" s)”

EVAL “remove_last "hello"”

EVAL “append_char "hello" "s"”

Theorem correctness:
  ∀s c. remove_last (append_char s c) = s
Proof
  cheat
  Induct_on ‘s’
  \\ rw[compr_def, decompr_def]
  \\ rw[STRCAT_def]
QED

        DB.find "strcat"
