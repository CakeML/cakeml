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

Definition pp_spaced_block_def:
  pp_spaced_block xs = PP_Data (LENGTH xs > 1)
    (app_intersperse (strlit " ") (MAP ppd_paren_contents xs))
End

Definition pp_app_block_def:
  pp_app_block nm xs = pp_spaced_block (ppd_token nm :: xs)
End

Definition pp_val_eq_def:
  pp_val_eq nm pp_f v = pp_app_block (strlit "val")
    [ppd_token (implode nm); ppd_token (strlit "="); pp_f v; ppd_token ("\n")]
End

Definition pp_val_hidden_type_def:
  pp_val_hidden_type nm = pp_app_block (strlit "val")
    [ppd_token (implode nm); ppd_token (strlit ": <hidden type>\n")]
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

Definition pp_bool_def:
  pp_bool b = PP_Data F (List [if b then (strlit "true") else (strlit "false")])
End

(* pretty-printers for the pretty-printer types *)
Definition pp_app_list_def:
  pp_app_list f (List xs) = pp_app_block (strlit "PrettyPrinter.List")
    [pp_list f xs] /\
  pp_app_list f Nil = ppd_token (strlit "PrettyPrinter.Nil") /\
  pp_app_list f (Append x y) = pp_app_block (strlit "PrettyPrinter.Append")
    [pp_app_list f x; pp_app_list f y]
End

Definition pp_pp_data_def:
  pp_pp_data (PP_Data b d) = pp_app_block (strlit "PrettyPrinter.PP_Data")
    [pp_bool b; pp_app_list pp_string d]
End

Definition pp_char_def:
  pp_char c = PP_Data F (List [strlit "#\""; str c; strlit "\""])
End

Definition pp_int_def:
  pp_int (i : int) = ppd_token (mlint$toString i)
End

Definition pp_word8_def:
  pp_word8 (w : 8 word) = pp_app_block (strlit "Word8.fromInt") [pp_int (w2i w)]
End

Definition pp_word64_def:
  pp_word64 (w : 64 word) = pp_app_block (strlit "Word64.fromInt") [pp_int (w2i w)]
End

(* these initial pure and useless pps will be replaced later *)
Definition pp_array_def:
  pp_array f arr = ppd_token (strlit "<array>")
End

Definition pp_ref_def:
  pp_ref r = ppd_token (strlit "<array>")
End

Definition pp_word8array_def:
  pp_word8array arr = ppd_token (strlit "<array>")
End

Definition pp_vector_def:
  pp_vector f v = pp_app_block (strlit "Vector.fromList")
    [pp_list f (mlvector$toList v)]
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
