(*
  Pure functions for the PrettyPrinter module.

  These are generally functions for converting an element of a CakeML type to
  an mlstring app_list (representing that element).
*)
open
  preamble
  mlstringTheory
  mlintTheory
  wordsTheory

val _ = new_theory "mlprettyprinter"

val fromString_def = Define`
  fromString s = List [implode "\""; s; implode "\""]
`

val fromChar_def = Define`
  fromChar c = List [implode "#\""; str c; implode "\""]
`

val fromBool_def = Define`
  fromBool b =
  List [if b then (implode "true") else (implode "false")]
`

val fromInt_def = Define`
  fromInt i = List [(mlint$toString i)]
`

val fromNum_def = Define`
  fromNum n = List [(mlint$toString (& n))]
`

val fromWord8_def = Define`
  fromWord8 (w : 8 word) =
  List [implode "0wx"; mlint$toString (& (words$w2n w))]
`

val fromWord64_def = Define`
  fromWord64 (w : 64 word) =
  List [implode "0wx"; mlint$toString (& (words$w2n w))]
`

val fromRat_def = Define`
  fromRat (n:int, d:num) =
  if d = 1 then List [mlint$toString n]
  else List [mlint$toString n; implode "/"; mlint$toString (& d)]
`

val fromOption_def = Define`
  fromOption f opt =
  case opt of
      NONE => List [implode "NONE"]
    | SOME x => Append (List [implode "SOME "]) (f x)
`

val fromPair_def = Define`
  fromPair f1 f2 (x,y) =
    Append (List [implode "("])
   (Append (f1 x)
   (Append (List [implode ", "])
   (Append (f2 y)
           (List [implode ")"]))))
`

val fromList_def = Define`
  fromList f l =
  case l of
    [] => List [implode "[]"]
  | h::t =>
    Append
      (Append
        (List [implode "["])
        ( FOLDL (λ acc x .
            Append (Append acc (List [implode ", "])) (f x)
          ) (f h) t
        )
      )
      (List [implode "]"])
`

val fromArray_def = Define`
  fromArray f a =
  Append
    ( foldli (λ i acc x .
        if i = 0 then f x
        else Append (Append acc (List [implode ", "])) (f x)
      ) (List [implode "fromList["]) a
    )
    (List [implode "]"])
`

val fromVector_def = Define`
  fromVector f v =
  Append
    ( foldli (λ i acc x .
        if i = 0 then f x
        else Append (Append acc (List [implode ", "])) (f x)
      ) (List [implode "fromList["]) v
    )
    (List [implode "]"])
`

val _ = export_theory ()
