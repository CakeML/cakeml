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
  fromString s = List [strlit "\""; s; strlit "\""]
`

val fromChar_def = Define`
  fromChar c = List [strlit "#\""; str c; strlit "\""]
`

val fromBool_def = Define`
  fromBool b =
  List [if b then (strlit "true") else (strlit "false")]
`

val fromInt_def = Define`
  fromInt i = List [(mlint$toString i)]
`

val fromNum_def = Define`
  fromNum n = List [(mlint$toString (& n))]
`

val fromWord8_def = Define`
  fromWord8 (w : 8 word) =
  List [strlit "0wx"; mlint$toString (& (words$w2n w))]
`

val fromWord64_def = Define`
  fromWord64 (w : 64 word) =
  List [strlit "0wx"; mlint$toString (& (words$w2n w))]
`

val fromRat_def = Define`
  fromRat (n:int, d:num) =
  if d = 1 then List [mlint$toString n]
  else List [mlint$toString n; strlit "/"; mlint$toString (& d)]
`

val fromOption_def = Define`
  fromOption f opt =
  case opt of
      NONE => List [strlit "NONE"]
    | SOME x => Append (List [strlit "SOME "]) (f x)
`

val fromList_def = Define`
  fromList f l =
  case l of
    [] => List [strlit "[]"]
  | h::t =>
    Append
      (Append
        (List [strlit "["])
        ( FOLDL (λ acc x .
            Append (Append acc (List [strlit ", "])) (f x)
          ) (f h) t
        )
      )
      (List [strlit "]"])
`

val fromArray_def = Define`
  fromArray f a =
  Append
    ( foldli (λ i acc x .
        if i = 0 then f x
        else Append (Append acc (List [strlit ", "])) (f x)
      ) (List [strlit "fromList["]) a
    )
    (List [strlit "]"])
`

val fromVector_def = Define`
  fromVector f v =
  Append
    ( foldli (λ i acc x .
        if i = 0 then f x
        else Append (Append acc (List [strlit ", "])) (f x)
      ) (List [strlit "fromList["]) v
    )
    (List [strlit "]"])
`

val _ = export_theory ()
