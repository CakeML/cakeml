(*
  TODO
*)
Theory bignumLang
Ancestors
  wordLang
Libs
  preamble

Datatype:
  exp = Const ('a word)
      | Var mlstring
      | Load exp
      | Op binop (exp list)
      | Shift shift exp exp
End

Datatype:
  cmp_arg = cVar mlstring | cConst ('a word)
End

Overload Var = “cVar”;
Overload Const = “cConst”;

Datatype:
  stmt = Skip
       | Seq stmt stmt
       | If cmp mlstring ('a cmp_arg) stmt stmt
       | While cmp mlstring ('a cmp_arg) stmt
       (* | Dec ((mlstring # 'a exp) list) stmt *)
       | Assign mlstring ('a exp)
       (* | Move ((mlstring # mlstring) list) *)
       | Store ('a exp) mlstring
       | Return (mlstring list)
       | Call ((mlstring list) option) mlstring (('a exp) list)
End
