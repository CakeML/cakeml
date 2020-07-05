(*
  Kernel initialisation
*)
open preamble readerTheory holSyntaxTheory

val _ = new_theory "reader_init";

Overload monad_bind[local] = “st_ex_bind”
Overload monad_unitbind[local] = “λx y. st_ex_bind x (λz. y)”
Overload monad_ignore_bind[local] = “λx y. st_ex_bind x (λz. y)”
Overload return[local] = “st_ex_return”
Overload failwith[local] = “raise_Fail”
val _ = temp_add_monadsyntax()

(* -------------------------------------------------------------------------
 * Kernel initialisation
 * ------------------------------------------------------------------------- *)

Definition init_refs_def:
  init_refs =
    <| the_type_constants := init_type_constants
     ; the_term_constants := init_term_constants
     ; the_axioms         := init_axioms
     ; the_context        := init_context |>
End

(* -------------------------------------------------------------------------
 * Axioms, constants and types
 * ------------------------------------------------------------------------- *)

(* The OpenTheory articles requires that the three axioms are stated only in
 * terms of the constant "=", the types "bool", "ind", "fun", and various
 * lambda terms -- e.g. no pre-defined logical constants such as !,?,~,/\,.. *)

Overload A[local] = “Tyvar «A»”
Overload B[local] = “Tyvar «B»”
Overload Ind[local] = “Tyapp «ind» []”

(* -- ETA_AX: |- !t. (\x. t x) = t ----------------------------------------- *)

(* T := (λp. p) = λp. p *)
Definition mk_true_def:
  mk_true () =
    do
      p <- return (mk_var («p», Bool));
      f <- mk_abs (p, p);
      mk_eq (f, f)
    od
End

(* (∀) := λp. (p = λx. T) *)
Definition mk_univ_def:
  mk_univ ty =
    do
      p <- return (mk_var («p», Fun ty Bool));
      x <- return (mk_var («x», ty));
      tru <- mk_true ();
      f <- mk_abs (x, tru);
      b <- mk_eq (p, f);
      mk_abs (p, b)
    od
End

(* ∀x. P[x] := (∀) (λx. P[x]) *)
Definition mk_forall_def:
  mk_forall (v, P) =
    do
      ty <- type_of v;
      all <- mk_univ ty;
      pabs <- mk_abs (v, P);
      mk_comb (all, pabs)
    od
End

(* ∀(t: 'a -> 'b). (λ(x:'a). t x) = t *)
Definition mk_eta_ax_def:
  mk_eta_ax () =
    do
      t <- return (mk_var («t», Fun A B));
      x <- return (mk_var («x», A));
      body <- mk_comb (t, x);
      tabs <- mk_abs (x, body);
      P <- mk_eq (tabs, t);
      mk_forall (t, P)
    od
End

(* -- SELECT_AX: |- !p. (!x. (p x) ==> (p ((select) p))) ------------------- *)

(* @ *)
Definition select_const_def:
  select_const =
    Const «@» (Fun (Fun A Bool) A)
End

(* (∧) := λp q. (λf. f p q) = λf. f T T *)
Definition mk_conj_const_def:
  mk_conj_const () =
    do
      p <- return (mk_var («p», Bool));
      q <- return (mk_var («q», Bool));
      t <- mk_true ();
      f <- return (mk_var («f», Fun Bool (Fun Bool Bool)));
      ft <- mk_comb (f, t); ftt <- mk_comb (ft, t);
      fp <- mk_comb (f, p); fpq <- mk_comb (fp, q);
      labs <- mk_abs (f, fpq);
      rabs <- mk_abs (f, ftt);
      eq <- mk_eq (labs, rabs);
      eabs <- mk_abs (q, eq);
      mk_abs (p, eabs)
    od
End

(* p ∧ q *)
Definition mk_conj_def:
  mk_conj (p, q) =
    do
      c <- mk_conj_const ();
      app <- mk_comb (c, p);
      mk_comb (app, q)
    od
End

(* (⇒) := λp q. p ∧ q = p *)
Definition mk_imp_const_def:
  mk_imp_const () =
    do
      p <- return (mk_var («p», Bool));
      q <- return (mk_var («q», Bool));
      conj <- mk_conj (p, q);
      eq <- mk_eq (conj, p);
      eabs <- mk_abs (q, eq);
      mk_abs (p, eabs)
    od
End

(* p ⇒ q *)
Definition mk_imp_def:
  mk_imp (p, q) =
    do
      imp <- mk_imp_const ();
      app <- mk_comb (imp, p);
      mk_comb (app, q)
    od
End

(* ∀p x. p x ⇒ p ((@) p) *)
Definition mk_select_ax_def:
  mk_select_ax () =
    do
      p <- return (mk_var («p», Fun A Bool));
      x <- return (mk_var («x», A));
      px <- mk_comb (p, x);
      sp <- mk_comb (select_const, p);
      psp <- mk_comb (p, sp);
      imp <- mk_imp (px, psp);
      all <- mk_forall (x, imp);
      mk_forall (p, all)
    od
End

(* -- INFINITY_AX: |- ∃f. injective f ∧ ¬surjective f ---------------------- *)

(* (∃) := λp. ∀q. (∀x. p x ⇒ q) ⇒ q *)
Definition mk_ex_def:
  mk_ex ty =
    do
      p <- return (mk_var («p», Fun ty Bool));
      q <- return (mk_var («q», Bool));
      x <- return (mk_var («x», ty));
      px <- mk_comb (p, x);
      imp <- mk_imp (px, q);
      l <- mk_forall (x, imp);
      imp2 <- mk_imp (l, q);
      all <- mk_forall (q, imp2);
      mk_abs (p, all)
    od
End

(* ∃x. P[x] := (∃) (λx. P[x]) *)
Definition mk_exists_def:
  mk_exists (v, P) =
    do
      ty <- type_of v;
      ex <- mk_ex ty;
      pabs <- mk_abs (v, P);
      mk_comb (ex, pabs)
    od
End

(* surjective f :=     ∀y. ∃x. y = f x *)
(* surjective   := λf. ∀y. ∃x. y = f x *)
Definition mk_surj_def:
  mk_surj f dom codom =
    do
      ty <- type_of f;
      y <- return (mk_var («y», codom));
      x <- return (mk_var («x», dom));
      fx <- mk_comb (f, x);
      eq <- mk_eq (y, fx);
      ex <- mk_exists (x, eq);
      mk_forall (y, ex);
    od
End

(* injective f :=     ∀x y. f x = f y ⇒ x = y *)
(* injective   := λf. ∀x y. f x = f y ⇒ x = y *)
Definition mk_inj_def:
  mk_inj f dom =
    do
      ty <- type_of f;
      x <- return (mk_var («x», dom));
      y <- return (mk_var («y», dom));
      fx <- mk_comb (f, x);
      fy <- mk_comb (f, y);
      lhs <- mk_eq (fx, fy);
      rhs <- mk_eq (x, y);
      imp <- mk_imp (lhs, rhs);
      yall <- mk_forall (y, imp);
      mk_forall (x, yall);
    od
End

(* F := ∀p. p *)
Definition mk_false_def:
  mk_false () =
    do
      p <- return (mk_var («p», Bool));
      mk_forall (p, p)
    od
End

(* (¬) := λp. p ⇒ F *)
Definition mk_neg_const_def:
  mk_neg_const () =
    do
      p <- return (mk_var («p», Bool));
      f <- mk_false ();
      imp <- mk_imp (p, f);
      mk_abs (p, imp)
    od
End

(* ¬p := (¬) p *)
Definition mk_neg_def:
  mk_neg p =
    do
      neg <- mk_neg_const ();
      mk_comb (neg, p)
    od
End

Definition mk_infinity_ax_def:
  mk_infinity_ax () =
    do
      f <- return (mk_var («f», Fun Ind Ind));
      surj <- mk_surj f Ind Ind;
      inj <- mk_inj f Ind;
      nsurj <- mk_neg surj;
      conj <- mk_conj (inj, nsurj);
      mk_exists (f, conj)
    od
End

(* -------------------------------------------------------------------------
 * Start reader with axioms
 * ------------------------------------------------------------------------- *)

Definition ind_type_def:
  ind_type = («ind», 0n)
End

Definition select_sym_def:
  select_sym = («@», Fun (Fun A Bool) A)
End

Definition init_reader_def:
  init_reader () =
    do
      ax <- mk_eta_ax (); new_axiom ax;
      new_constant select_sym;
      ax <- mk_select_ax (); new_axiom ax;
      new_type ind_type;
      ax <- mk_infinity_ax (); new_axiom ax;
      return ()
    od
End

val _ = export_theory ();

