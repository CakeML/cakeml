open
  preamble
  ml_translatorLib
  ml_translatorTheory
  ml_progLib
  basisFunctionsLib
  StringProgTheory

val _ = (
  new_theory "PrettyPrintProg";
  translation_extends "StringProg";
  ml_prog_update (open_module "PrettyPrint")
)

(*val () = generate_sigs := true;*)

val pp_fromString = process_topdecs`
  fun fromString s =
    List ["\"", s, "\""]
`

val pp_printString = process_topdecs`
  fun printString s = (
    TextIO.print "\"";
    TextIO.print s;
    TextIO.print "\""
  )
`

val pp_fromChar = process_topdecs`
  fun fromChar c =
    List ["#\"", (Char.toString c), "\""]
    (* TODO: check result of Char.toString for non-printable char, should be e.g. \3 and not something weird *)
`

val pp_printChar = process_topdecs`
  fun printChar c = (
    TextIO.print "\"";
    TextIO.print s;
    TextIO.print "\""
  )
`

val pp_fromBool = process_topdecs`
  fun fromBool b =
    List [Bool.toString b]
`

val pp_printBool = process_topdecs`
  fun printBool b =
    TextIO.print (Bool.toString b)
`

val pp_fromInt = process_topdecs`
  fun fromInt i =
    List [Int.toString i]
`

val pp_printInt = process_topdecs`
  fun printInt i =
    TextIO.print (Int.toString i)
`

val pp_fromWord = process_topdecs`
  fun fromWord w =
    List ["0wx", (Word.toString w)]
`

val pp_printWord = process_topdecs`
  fun printWord w = (
    TextIO.print "0wx";
    TextIO.print (Word.toString w)
  )
`

val pp_fromReal = process_topdecs`
  fun fromReal r =
    List [Real.toString r]
`

val pp_printReal = process_topdecs`
  fun printReal r =
    TextIO.print (Real.toString r)
`

val pp_fromOption = process_topdecs`
  fun fromOption f opt =
    case opt of
        NONE => List ["NONE"]
      | (SOME el) => Append ["SOME "] (f el)
`

val pp_printOption = process_topdecs`
  fun printOption f opt =
    case opt of
      NONE => TextIO.print "NONE"
    | (SOME el) => (
        TextIO.print "SOME ";
        f el
      )
`

val pp_fromList = process_topdecs`
  fun fromList f l =
    case l of
      [] => List ["[]"]
    | (h::t) =>
      Append
        (Append 
          (List ["["])
          (List.foldl (fn (acc, el) => Append (Append acc (List [", "])) (f el)) (f h) t)
        )
        List ["]"]
`

val pp_printList = process_topdecs`
  fun printList f l =
    case l of
      [] => TextIO.print "[]"
    | (h::t) => (
        TextIO.print "[";
        f h;
        List.app (fn el => TextIO.print ", "; f el) t;
        TextIO.print "]"
      )
`

val pp_fromArray = process_topdecs`
  fun fromArray f a =
    Append
      (Array.foldli (fn (i, acc, el) =>
          if i = 0 then f el
          else Append (Append acc (List [", "])) (f el)
        ) (List ["fromList["]) a
      )
      (List ["]"])
`

val pp_printArray = process_topdecs`
  fun printArray f a = (
    TextIO.print "fromList[";
    Array.appi (fn (i, el) =>
        if i = 0 then f el
        else (TextIO.print ", "; f a)
      ) a;
    TextIO.print "]"
  )
`

val pp_fromVector = process_topdecs`
  fun fromVector f v =
    Append
      (Vector.foldli (fn (i, acc, el) =>
          if i = 0 then f el
          else Append (Append acc (List [", "])) (f el)
        ) (List ["fromList["]) v
      )
      (List ["]"])
`

val pp_printVector = process_topdecs`
  fun printVector f v = (
    TextIO.print "fromList[";
    Vector.appi (fn (i, el) =>
        if i = 0 then f el
        else (TextIO.print ", "; f el)
      ) a;
    TextIO.print "]"
  )
`

val _ = List.app append_prog [
  pp_fromString,
  pp_printString,
  pp_fromChar,
  pp_printChar,
  pp_fromBool,
  pp_printBool,
  pp_fromInt,
  pp_printInt,
  pp_fromWord,
  pp_printWord,
  pp_fromReal,
  pp_printReal,
  pp_fromOption,
  pp_printOption,
  pp_fromList,
  pp_printList,
  pp_fromArray,
  pp_printArray,
  pp_fromVector,
  pp_printVector
]

(*
val sigs = module_signatures [
  "fromString",
  "fromChar",
  "fromBool",
  "fromInt",
  "fromWord",
  "fromReal",
  "fromOption",
  "fromList",
  "fromArray",
  "fromVector"
]*)

val _ = (
  ml_prog_update (close_module (NONE));
  export_theory ()
)
