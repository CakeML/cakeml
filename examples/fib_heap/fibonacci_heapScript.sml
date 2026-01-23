(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep
Libs
  wordsLib

Definition double_linked_list_seg_def:
  (dllseg a p [] s e = emp * cond ( p <> 0w /\ a = s /\ e = p )) /\
  (dllseg a p (x::xs) s e =
    SEP_EXISTS b.
      one (a:'a word, x:'a word) *
      one (a + bytes_in_word, p) *
      one (a + 2w * bytes_in_word, b) *
      dllseg b a xs s e)
End

(* This one is a bit odd. Is this a cyclic version?
Definition double_linked_list_def:
  (dll a [] = emp) /\
  (dll a (x::xs) = ?b c. one (a:word64, (x:word64, b:word64, c:word64)) * dllseg(c a xs a b))
End
*)
