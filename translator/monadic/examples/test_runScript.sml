(*
  An example showing how to make use of m_translate_run
*)
Theory test_run
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();


val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = patternMatchesSyntax.temp_enable_pmatch();

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| the_num : num |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string
End

val config =  local_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [("the_num", ``0 : num``)];

val _ = start_translation config;

Overload failwith = ``raise_Fail``

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
  f5 l n1 = do n2 <- get_the_num; return (EL (n1 + n2) l) od
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
  (f8 []      n = return (n : num))
End
val f8_v_thm = m_translate f8_def;

Definition f9_def:
  (f9 (x::xs) n = (do l <- f9 xs n; return (1+l) od)) /\
  (f9 []      n = return ((HD n) : num))
End
val f9_v_thm = m_translate f9_def;

Definition f10_def:
f10 y = handle_Fail (
  do
    x <- (raise_Fail "fail"); return x
  od)
  (\e. return e)
End
val f10_v_thm = m_translate f10_def;

Definition f11_def:
  f11 x = pmatch x of
      []    => return (0 : num)
    | x::xs => (do l <- f11 xs; return (1 + l) od)
End
val f11_v_thm = m_translate f11_def;
val f11_side_def = fetch "-" "f11_side_def"
Theorem f11_side_true[local]:
  !xs st. f11_side st xs
Proof
  Induct \\ rw[Once f11_side_def]
QED

Definition f12_def:
  f12 x = ((return (1:num)) otherwise (return 0))
End
val f12_v_thm = m_translate f12_def;

Definition f13_def:
  f13 l1 n1 l2 n2 = do x1 <- f5 l1 n1; f5 l2 n2 od
End
val f13_v_thm = m_translate f13_def;

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

(* m_translate_run *)
Definition r1_def:
  r1 x y z st = run (f1 x y z) st
End
val r1_v_thm = m_translate_run r1_def;

Definition r2_def:
  r2 x y z st = run (f2 x y z) st
End
val r2_v_thm = m_translate_run r2_def;

Definition r3_def:
  r3 x st = run (f3 x) st
End
val r3_v_thm = m_translate_run r3_def;

Definition r4_def:
  r4 x st = run (f4 x) st
End
val r4_v_thm = m_translate_run r4_def;

Definition r5_def:
  r5 l n1 st = run (f5 l n1) st
End
val r5_v_thm = m_translate_run r5_def;

Definition r6_def:
  r6 l n1 st = run (f6 l n1) st
End
val r6_v_thm = m_translate_run r6_def;

Definition r7_def:
  r7 x y z st = run (f7 x y z) st
End
val r7_v_thm = m_translate_run r7_def;

Definition r8_def:
  r8 xs n st = run (f8 xs n) st
End
val r8_v_thm = m_translate_run r8_def;

Definition r9_def:
  r9 xs n st = run (f9 xs n) st
End
val r9_v_thm = m_translate_run r9_def;

Definition r10_def:
  r10 x st = run (f10 x) st
End
val r10_v_thm = m_translate_run r10_def;

Definition r11_def:
  r11 x st = run (f11 x) st
End
val r11_v_thm = m_translate_run r11_def;

Definition r12_def:
  r12 x st = run (f12 x) st
End
val r12_v_thm = m_translate_run r12_def;

Definition r13_def:
  r13 w x y z st = run (f13 w x y z) st
End
val r13_v_thm = m_translate_run r13_def;

Definition r14_def:
  r14 l n1 = run (f5 l n1) <| the_num := 0 |>
End
val def = r14_def;
val r14_v_thm = m_translate_run r14_def;
