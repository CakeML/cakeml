(*
  Definition of Scheme values
*)
Theory scheme_values
Ancestors
  arithmetic list string
Libs
  preamble

(* Values in the source semantics are binary trees *)
Datatype:
  v = Pair v v | Num int | Bool bool | Word string | Nil
End
(*
(* Since strings are not in the representation, we have a function that
   coverts strings into numbers. Note that parsing and pretty printing
   is set up so that printing reproduces these strings when possible. *)
Definition name_def:
  name [] = 0 ∧
  name (c::cs) = ORD c * 256 ** (LENGTH cs) + name cs
End

Overload Name = “λn. Num (name n)”

(* Lists are terminated with Num 0 *)
Definition list_def[simp]:
  list [] = Num 0 ∧
  list (x::xs) = Pair x (list xs)
End

(* various convenience functions below, most are automatic rewrites [simp] *)

Definition less_def[simp]:
  less (Num n) (Num m) <=> n < m
End

Definition plus_def[simp]:
  plus (Num n) (Num m) = Num (n + m)
End

Definition minus_def[simp]:
  minus (Num n) (Num m) = Num (n - m)
End

Definition div_def[simp]:
  div (Num n) (Num m) = Num (n DIV m)
End
*)

Definition head_def[simp]:
  head (Pair x y) = x ∧
  head v = v
End

Definition tail_def[simp]:
  tail (Pair x y) = y ∧
  tail v = v
End

Definition cons_def[simp]:
  cons x y = Pair x y
End

(*
Definition bool_def[simp]:
  bool T = Num 1 ∧
  bool F = Num 0
End

Definition map_def[simp]:
  map f xs = list (MAP f xs)
End

Overload "list" = “map”;

Definition pair_def[simp]:
  pair f g (x,y) = Pair (f x) (g y)
End

Definition option_def[simp]:
  option f NONE = list [] ∧
  option f (SOME x) = list [f x]
End

Definition char_def[simp]:
  char c = Num (ORD c)
End

Definition isNum_def[simp]:
  isNum (Num n) = T ∧ isNum _ = F
End

Definition getNum_def[simp]:
  getNum (Num n) = n ∧
  getNum _ = 0
End

Definition el1_def[simp]:
  el1 v = head (tail v)
End

Definition el2_def[simp]:
  el2 v = el1 (tail v)
End

Definition el3_def[simp]:
  el3 v = el2 (tail v)
End

Overload isNil[inferior] = “isNum”;
Overload el0[inferior] = “head”;

Theorem isNum_bool[simp]:
  isNum (bool b)
Proof
  Cases_on ‘b’ \\ EVAL_TAC
QED
*)

Theorem v_size_def[simp,allow_rebind] = fetch "-" "v_size_def";

(*Theorem all_macro_defs = LIST_CONJ [list_def, cons_def, bool_def,
   map_def, pair_def, option_def];

Definition is_upper_def:
  (* checks whether string (represented as num) starts with uppercase letter *)
  is_upper n =
    if n < 256:num then
      if n < 65 (* ord A = 65 *) then F else
      if n < 91 (* ord Z = 90 *) then T else F
    else is_upper (n DIV 256)
End

Definition otherwise_def[simp]:
  otherwise x = x
End
*)

