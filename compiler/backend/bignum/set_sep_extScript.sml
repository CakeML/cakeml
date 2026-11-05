(*
  Extensions to set_sep that should be eventually merged into it.
*)
Theory set_sep_ext
Ancestors
  arithmetic pred_set rich_list byte words set_sep
Libs
  helperLib

(* TODO Check whether these fixities/symbols are OK; CF also defines things *)
val _ = set_fixity "==>>" (Infixr 470)
val _ = set_fixity "-*" (Infixr 490)

(** Separating Implication ****************************************************)

Overload "==>>" = “SEP_IMP”

(** ones **********************************************************************)

Definition ones_def:
  ones a [] = emp ∧
  ones a (x::xs) = one (a,x) * ones (a + bytes_in_word) xs
End

Definition el_addr_def:
  el_addr a i = a + n2w i * bytes_in_word
End

Theorem ones_append:
  ∀xs ys a.
    ones a (xs ++ ys) =
    ones a xs * ones (a + n2w (LENGTH xs) * bytes_in_word) ys
Proof
  Induct
  >> rw [ones_def, SEP_CLAUSES]
  >> simp [ADD1, WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w]
  >> fs [AC STAR_ASSOC STAR_COMM]
QED

Theorem ones_TAKE_DROP:
  i < LENGTH xs ⇒
  ones x xs =
  ones x (TAKE i xs) *
  one (el_addr x i,xs❲i❳) *
  ones (el_addr x (i + 1)) (DROP (SUC i) xs)
Proof
  strip_tac
  >> have ‘xs = TAKE i xs ++ [xs❲i❳] ++ DROP (SUC i) xs’
  >- simp [TAKE_DROP_SUC]
  >> qpat_assum ‘xs = _’ (CONV_TAC o LHS_CONV o ONCE_REWRITE_CONV o single)
  >> simp [ones_append, ones_def, SEP_CLAUSES, el_addr_def]
QED

Theorem ones_SNOC:
  ones a (SNOC x xs) =
  ones a xs * one (a + n2w (LENGTH xs) * bytes_in_word, x)
Proof
  simp [SNOC_APPEND, ones_append, ones_def, SEP_CLAUSES]
QED

Theorem read_el_addr:
  ∀frame x xs f d i.
    (frame * ones (x: α word) (xs: β list)) (fun2set (f, d)) ⇒
    i < LENGTH xs ⇒
    el_addr x i ∈ d ∧ f (el_addr x i) = xs❲i❳
Proof
  rpt gen_tac
  >> ntac 2 strip_tac
  >> drule $ INST_TYPE [“:α” |-> “:β”, “:β” |-> “:α”] ones_TAKE_DROP
  >> disch_then $ qspec_then ‘x’ assume_tac>> fs []
  >> SEP_R_TAC
  >> simp []
QED

(** Magic Wand ****************************************************************)

Definition SEP_WAND_def:
  SEP_WAND p q = λs. ∀s'. DISJOINT s' s ∧ p s' ⇒ q (s' ∪ s)
End

Overload "-*" = “SEP_WAND”

Theorem SEP_WAND_EQ:
  (H0 ==>> H1 -* H2) ⇔ (H1 * H0 ==>> H2)
Proof
  simp [SEP_IMP_def, SEP_WAND_def, STAR_def, SPLIT_def]
  >> metis_tac [DISJOINT_SYM, UNION_COMM]
QED

Theorem SEP_WAND_CANCEL:
  H0 * (H0 -* H1) ==>> H1
Proof
  simp [GSYM SEP_WAND_EQ, SEP_IMP_REFL]
QED

(*
  References:
  1. Separation Logic Foundations (Software Foundations, Vol. 6) by
     Arthur Charguéraud
*)
