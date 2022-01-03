(*
  Types and pure functions for pretty printing

  Most of these functions are translated in the first phase of the basis
  setup so that default pretty-printing (c.f. the addTypePP system) will
  work from then on.
*)
open
  preamble
  mlstringTheory
  mlintTheory
  mlvectorTheory
  wordsTheory

val _ = new_theory "mlprettyprinter"

(* Data for pretty-printing. The bool indicates if this data needs to be
   wrapped in parens, if this data is given as an argument to an application.
*)
Datatype:
  pp_data = PP_Data bool (mlstring app_list)
End

(* avoid the pp_X naming scheme by using ppd_X (i.e. pp_data_X) internally *)
Definition ppd_token_def:
  ppd_token s = PP_Data F (List [s])
End

Definition pp_fun_def:
  pp_fun = ppd_token (strlit "<fun>")
End

(* there is a plan to replace this with an impure extensible implementation *)
Definition pp_exn_def:
  pp_exn e = ppd_token (strlit "<exn>")
End

Definition app_intersperse_def:
  app_intersperse c [] = Nil /\
  app_intersperse c [x] = x /\
  app_intersperse c (x :: y :: zs) = Append (Append x (List [c])) (app_intersperse c (y :: zs))
End

Definition ppd_contents_def:
  ppd_contents (PP_Data _ xs) = xs
End

Definition app_list_wrap_def:
  app_list_wrap l xs r = Append (List [l]) (Append xs (List [r]))
End

Definition ppd_paren_contents_def:
  ppd_paren_contents (PP_Data F xs) = xs /\
  ppd_paren_contents (PP_Data T xs) = app_list_wrap (strlit "(") xs (strlit ")")
End

Definition pp_paren_tuple_def:
  pp_paren_tuple pps = PP_Data F (app_list_wrap (strlit "(")
    (app_intersperse (strlit ", ") (MAP ppd_contents pps))
    (strlit ")")
  )
End

Definition pp_app_block_def:
  pp_app_block nm [] = PP_Data F (List [nm]) /\
  pp_app_block nm xs = PP_Data T (app_intersperse (strlit " ")
    (List [nm] :: MAP ppd_paren_contents xs))
End

Definition pp_list_def:
  pp_list f xs = PP_Data F (app_list_wrap (strlit "[")
    (app_intersperse (strlit "; ") (MAP (\x. ppd_contents (f x)) xs))
    (strlit "]")
  )
End

Definition pp_string_def:
  pp_string s = PP_Data F (List [strlit "\""; s; strlit "\""])
End

Definition pp_char_def:
  pp_char c = PP_Data F (List [strlit "#\""; str c; strlit "\""])
End

Definition pp_bool_def:
  pp_bool b = PP_Data F (List [if b then (strlit "true") else (strlit "false")])
End

Definition pp_vector_def:
  pp_vector f v = pp_app_block (strlit "Vector.fromList") [pp_list f (mlvector$toList v)]
End

(* pp of array, ref, word8array will be added later (impure)  *)

Definition pp_int_def:
  pp_int i = ppd_token (mlint$toString i)
End

Definition pp_word8_def:
  pp_word8 w = pp_app_block (strlit "Word8.fromInt") [pp_int (w2i w)]
End

Definition pp_word64_def:
  pp_word64 w = pp_app_block (strlit "Word64.fromInt") [pp_int (w2i w)]
End

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

val _ = export_theory ()
