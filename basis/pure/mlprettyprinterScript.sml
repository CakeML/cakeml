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

Definition pp_token_def:
  pp_token s = PP_Data F (List [s])
End

Definition pp_fun_def:
  pp_fun = pp_token (strlit "<fun>")
End

Definition pp_unprintable_def:
  pp_unprintable s = PP_Data F (List [strlit "<val of unprintable type "; s; strlit ">"])
End

(* there is a plan to replace this with an impure extensible implementation *)
Definition pp_exn_def:
  pp_exn e = pp_token (strlit "<exn>")
End

Definition app_intersperse_def:
  app_intersperse c [] = Nil /\
  app_intersperse c [x] = x /\
  app_intersperse c (x :: y :: zs) = Append (Append x (List [c])) (app_intersperse c (y :: zs))
End

Definition pp_contents_def:
  pp_contents (PP_Data _ xs) = xs
End

Definition pp_no_parens_def:
  pp_no_parens pp = PP_Data F (pp_contents pp)
End

Definition app_list_wrap_def:
  app_list_wrap l xs r = Append (List [l]) (Append xs (List [r]))
End

Definition pp_paren_contents_def:
  pp_paren_contents (PP_Data F xs) = xs /\
  pp_paren_contents (PP_Data T xs) = app_list_wrap (strlit "(") xs (strlit ")")
End

Definition pp_paren_tuple_def:
  pp_paren_tuple pps = PP_Data F (app_list_wrap (strlit "(")
    (app_intersperse (strlit ", ") (MAP pp_contents pps))
    (strlit ")")
  )
End

Definition pp_spaced_block_def:
  pp_spaced_block xs = PP_Data (LENGTH xs > 1)
    (app_intersperse (strlit " ") (MAP pp_paren_contents xs))
End

Definition pp_app_block_def:
  pp_app_block nm xs = pp_spaced_block (pp_token nm :: xs)
End

Definition pp_val_eq_def:
  pp_val_eq nm pp_f v ty = PP_Data F (Append
    (List [strlit "val "; nm; strlit " = "])
    (Append (pp_contents (pp_f v)) (List [strlit ": "; ty; strlit "\n"])))
End

Definition pp_val_hidden_type_def:
  pp_val_hidden_type nm ty = PP_Data F
    (List [strlit "val "; nm; strlit " <not printable> : "; ty; strlit "\n"])
End

Definition pp_failure_message_def:
  pp_failure_message s = PP_Data F
    (List [strlit "<failure: "; s; strlit ">\n"])
End

Definition pp_list_def:
  pp_list f xs = PP_Data F (app_list_wrap (strlit "[")
    (app_intersperse (strlit "; ") (MAP (\x. pp_contents (f x)) xs))
    (strlit "]")
  )
End

Definition pp_unit_def:
  pp_unit u = pp_token (strlit "()")
End

Definition escape_str_app_list_def:
  escape_str_app_list i s = case str_findi (\c. IS_SOME (char_escape_seq c)) i s of
    NONE => List [substring s i (strlen s - i)]
  | SOME j => Append (List [substring s i (j - i);
        case char_escape_seq (strsub s j) of NONE => strlit "" | SOME s => s])
    (escape_str_app_list (j + 1) s)
Termination
  WF_REL_TAC `measure (\(i, s). strlen s - i)`
  \\ rw []
  \\ drule str_findi_range
  \\ simp []
End

Triviality findi_map_escape:
  !P i s. P = IS_SOME o char_escape_seq ==>
  FLAT (MAP char_escaped (DROP i (explode s))) =
  case str_findi P i s of
    NONE => DROP i (explode s)
  | SOME j => TAKE (j - i) (DROP i (explode s))
    ++ (case char_escape_seq (strsub s j) of NONE => "" | SOME s => explode s)
    ++ FLAT (MAP char_escaped (DROP (j + 1) (explode s)))
Proof
  recInduct str_findi_ind
  \\ rw []
  \\ simp [Once str_findi_def]
  \\ rw []
  \\ simp [listTheory.DROP_LENGTH_TOO_LONG]
  \\ `DROP i (explode s) = strsub s i :: DROP (i + 1) (explode s)`
    by (Cases_on `s` \\ fs [DROP_EL_CONS])
  \\ fs [char_escaped_def, IS_SOME_EXISTS]
  \\ EVERY_CASE_TAC \\ fs []
  \\ imp_res_tac str_findi_range
  \\ simp [TAKE_def]
QED

Theorem escape_str_app_list_thm:
  !i s. concat (append (escape_str_app_list i s)) =
  implode (FLAT (MAP char_escaped (DROP i (explode s))))
Proof
  recInduct escape_str_app_list_ind
  \\ rw []
  \\ simp [Once (Q.SPEC `\c. IS_SOME (char_escape_seq c)` findi_map_escape), FUN_EQ_THM]
  \\ simp [Once escape_str_app_list_def]
  \\ Cases_on `s`
  \\ EVERY_CASE_TAC \\ fs []
  \\ rw [substring_def, SEG_TAKE_DROP, mlstringTheory.concat_def, implode_def]
  \\ imp_res_tac str_findi_range
  \\ fs [mlstringTheory.concat_def, implode_def]
  \\ imp_res_tac (Q.prove (`!s. x = SOME s ==> ?xs. s = strlit xs`, Cases \\ simp []))
  \\ simp []
QED

Definition pp_string_def:
  pp_string s = PP_Data F (app_list_wrap (strlit "\"") (escape_str_app_list 0 s) (strlit "\""))
End

Theorem pp_string_thm:
  concat (append (pp_contents (pp_string s))) = escape_str s
Proof
  simp [pp_string_def, pp_contents_def, app_list_wrap_def, concat_cons,
    escape_str_app_list_thm, concat_append, escape_str_def]
  \\ simp [implode_def, strcat_def, mlstringTheory.concat_def]
QED

Definition pp_bool_def:
  pp_bool b = PP_Data F (List [if b then (strlit "True") else (strlit "False")])
End

(* pretty-printers for the pretty-printer types *)
Definition pp_app_list_def:
  pp_app_list f (List xs) = pp_app_block (strlit "List")
    [pp_list f xs] /\
  pp_app_list f Nil = pp_token (strlit "Nil") /\
  pp_app_list f (Append x y) = pp_app_block (strlit "Append")
    [pp_app_list f x; pp_app_list f y]
End

Definition pp_pp_data_def:
  pp_pp_data (PP_Data b d) = pp_app_block (strlit "PP_Data")
    [pp_bool b; pp_app_list pp_string d]
End

Definition pp_char_def:
  pp_char c = PP_Data F (List [strlit "#\""; case char_escape_seq c of NONE => implode [c]
    | SOME s => s; strlit "\""])
End

Theorem pp_char_thm:
  concat (append (pp_contents (pp_char c))) = escape_char c
Proof
  simp [pp_char_def, escape_char_def, char_escaped_def]
  \\ every_case_tac
  \\ simp [pp_contents_def, mlstringTheory.concat_def, implode_def]
  \\ every_case_tac \\ simp []
QED

Definition pp_int_def:
  pp_int (i : int) = pp_token (mlint$toString i)
End

Definition pp_word8_def:
  pp_word8 (w : 8 word) = pp_app_block (strlit "Word8.fromInt") [pp_int (w2i w)]
End

Definition pp_word64_def:
  pp_word64 (w : 64 word) = pp_app_block (strlit "Word64.fromInt") [pp_int (w2i w)]
End

(* these initial pure and useless pps might be replaced later *)
Definition pp_array_def:
  pp_array f arr = pp_token (strlit "<array>")
End

Definition pp_ref_def:
  pp_ref f r = pp_token (strlit "<ref>")
End

Definition pp_word8array_def:
  pp_word8array arr = pp_token (strlit "<w8array>")
End

Definition pp_vector_def:
  pp_vector f v = pp_app_block (strlit "Vector.fromList")
    [pp_list f (mlvector$toList v)]
End

(* values of this type should never appear in programs.
   it is used to monomorphise some expressions so they
   can be printed safely. *)
Datatype:
  default_type = Default_Type
End

Definition pp_default_type_def:
  pp_default_type v = case v of Default_Type =>
    pp_token (strlit "<val of default type: this should be impossible>")
End

Definition fromRat_def:
  fromRat (n:int, d:num) =
  if d = 1 then List [mlint$toString n]
  else List [mlint$toString n; strlit "/"; mlint$toString (& d)]
End

Definition fromOption_def:
  fromOption f opt =
  case opt of
      NONE => List [strlit "NONE"]
    | SOME x => Append (List [strlit "SOME "]) (f x)
End

val _ = export_theory ()
