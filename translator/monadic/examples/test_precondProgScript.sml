(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "test_precondProg"

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| the_num : num ;
                  the_num_array : num list ;
                  the_int_array : int list |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [("the_num", ``0 : num``)] |>
              with_resizeable_arrays [
                ("the_num_array", ``[] : num list``,
                  ``Subscript``, ``Subscript``),
                ("the_int_array", ``[] : int list``,
                  ``Subscript``, ``Subscript``)
              ];

Overload failwith = ``raise_Fail``

val _ = start_translation config;

val hd_v_thm = translate HD;
val tl_v_thm = translate TL;
val el_v_thm = translate EL;

(* Some tests *)
Definition f1_def:
  f1 x y (z : num) = return (x + y + z)
End
val f1_v_thm = m_translate f1_def;

Definition f2_def:
  f2 x y (z : num) = return ((HD x) + y + z)
End
val f2_v_thm = m_translate f2_def;

Definition f3_def:
  f3 x = return (HD x)
End
val f3_v_thm = m_translate f3_def;

Definition f4_def:
  f4 x = do y <- return x; return y od
End
val f4_v_thm = m_translate f4_def;

Definition f5_def:
  f5 l n1 = do
    n2 <- get_the_num;
    return (EL (n1 + n2) l)
  od
End
val f5_v_thm = m_translate f5_def;

Definition f6_def:
  f6 l n = f5 l n
End
val f6_v_thm = m_translate f6_def;

Definition f7_def:
  f7 x y z = f1 x y z
End
val f7_v_thm = m_translate f7_def;

Definition f8_def:
  (f8 (x::xs) n = (do l <- f8 xs n; return (1+l) od)) /\
  (f8 [] n = return (n : num))
End
val f8_v_thm = m_translate f8_def;

Definition f9_def:
  (f9 (x::xs) n = (do l <- f9 xs n; return (1+l) od)) /\
  (f9 [] n = return ((HD n) : num))
End
val f9_v_thm = m_translate f9_def;

Definition f10_def:
  f10 y = handle_Fail (
    do x <- (raise_Fail "fail");
       return x
    od
  ) (\e. return e)
End
val f10_v_thm = m_translate f10_def;

Definition f11_def:
  f11 x = case x of []    => return (0 : num)
                  | x::xs => (do l <- f11 xs; return (1 + l) od)
End
val f11_v_thm = m_translate f11_def;

Definition f12_def:
  f12 x = ((return (1:num)) otherwise (return 0))
End
val f12_v_thm = m_translate f12_def;

(* Mutually recursive function with preconditions *)
Datatype:
  tree = T1 (num list) | T2 (tree list)
End

val _ = register_type ``:tree``;

val _ = ParseExtras.temp_tight_equality();

Definition tree_sum_def:
  tree_sum  (T1 l) = return (HD l) /\
  tree_sum  (T2 x) = tree_suml x /\
  tree_suml []     = return 0 /\
  tree_suml (t::l) = do
      x1 <- tree_sum t;
      x2 <- tree_suml l;
      return (x1 + x2)
    od
End
val tree_sum_v_thm = m_translate tree_sum_def;

(* No precondition *)
Definition tree_sum2_def:
  tree_sum2  (T1 l) = return (1 : num) /\
  tree_sum2  (T2 x) = tree_suml2 x /\
  tree_suml2 []     = return 0 /\
  tree_suml2 (t::l) = do
    x1 <- tree_sum2 t;
    x2 <- tree_suml2 l;
    return (x1 + x2)
  od
End
val tree_sum2_v_thm = m_translate tree_sum2_def;

(* pattern matching *)
Definition tree_sum3_def:
  tree_sum3  (T1 l) = return (HD l) /\
  tree_sum3  (T2 x) = tree_suml3 x /\
  tree_suml3 []     = return 0 /\
  tree_suml3 (t::l) = do
    x1 <- tree_sum3 t;
    x2 <- tree_suml3 l;
    return (x1 + x2)
  od
End
val tree_sum_v_thm = m_translate tree_sum_def;

val _ = export_theory ();
