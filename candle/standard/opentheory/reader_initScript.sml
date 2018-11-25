(*
  Kernel initialisation
*)
open preamble readerTheory holSyntaxTheory

val _ = new_theory "reader_init";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_add_monadsyntax()

(* ------------------------------------------------------------------------- *)
(* Kernel initialisation                                                     *)
(* ------------------------------------------------------------------------- *)

val init_refs_def = Define `
  init_refs =
    <| the_type_constants := init_type_constants
     ; the_term_constants := init_term_constants
     ; the_axioms         := init_axioms
     ; the_context        := init_context |>`;

(* ------------------------------------------------------------------------- *)
(* Axioms, constants and types                                               *)
(* ------------------------------------------------------------------------- *)

(* The OpenTheory articles requires that the three axioms are stated only in *)
(* terms of the constant "=", the types "bool", "ind", "fun", and various    *)
(* lambda terms -- e.g. no pre-defined logical constants such as !,?,~,/\,.. *)

val _ = temp_overload_on ("A", ``Tyvar (strlit"A")``);
val _ = temp_overload_on ("B", ``Tyvar (strlit"B")``);
val _ = temp_overload_on ("Ind", ``Tyapp (strlit"ind") []``);

(* -- ETA_AX: |- !t. (\x. t x) = t ----------------------------------------- *)

(* T := (\p. p) = \p. p *)
val mk_true_def = Define `
  mk_true () =
    do
      p <- return (mk_var (strlit"p", Bool));
      f <- mk_abs (p, p);
      mk_eq (f, f)
    od`;

(* (!) := \p. (p = \x. T) *)
val mk_univ_def = Define `
  mk_univ ty =
    do
      p <- return (mk_var (strlit"p", Fun ty Bool));
      x <- return (mk_var (strlit"x", ty));
      tru <- mk_true ();
      f <- mk_abs (x, tru);
      b <- mk_eq (p, f);
      mk_abs (p, b)
    od`;

(* !x. P[x] := (!) (\x. P[x]) *)
val mk_forall_def = Define `
  mk_forall (v, P) =
    do
      ty <- type_of v;
      all <- mk_univ ty;
      pabs <- mk_abs (v, P);
      mk_comb (all, pabs)
    od`;

(* !(t: 'a -> 'b). (\(x:'a). t x) = t *)
val mk_eta_ax_def = Define `
  mk_eta_ax () =
    do
      t <- return (mk_var (strlit"t", Fun A B));
      x <- return (mk_var (strlit"x", A));
      body <- mk_comb (t, x);
      tabs <- mk_abs (x, body);
      P <- mk_eq (tabs, t);
      mk_forall (t, P)
    od`;

(* -- SELECT_AX: |- !p. (!x. (p x) ==> (p ((select) p))) ------------------- *)

(* @ *)
val select_const_def = Define `
  select_const = Const (strlit"@") (Fun (Fun A Bool) A)`;

(* (/\) := \p q. (\f. f p q) = \f. f T T *)
val mk_conj_const_def = Define `
  mk_conj_const () =
    do
      p <- return (mk_var (strlit"p", Bool));
      q <- return (mk_var (strlit"q", Bool));
      t <- mk_true ();
      f <- return (mk_var (strlit"f", Fun Bool (Fun Bool Bool)));
      ft <- mk_comb (f, t); ftt <- mk_comb (ft, t);
      fp <- mk_comb (f, p); fpq <- mk_comb (fp, q);
      labs <- mk_abs (f, fpq);
      rabs <- mk_abs (f, ftt);
      eq <- mk_eq (labs, rabs);
      eabs <- mk_abs (q, eq);
      mk_abs (p, eabs)
    od`;

(* p /\ q *)
val mk_conj_def = Define `
  mk_conj (p, q) =
    do
      c <- mk_conj_const ();
      app <- mk_comb (c, p);
      mk_comb (app, q)
    od`;

(* (==>) := \p q. p /\ q = p *)
val mk_imp_const_def = Define `
  mk_imp_const () =
    do
      p <- return (mk_var (strlit"p", Bool));
      q <- return (mk_var (strlit"q", Bool));
      conj <- mk_conj (p, q);
      eq <- mk_eq (conj, p);
      eabs <- mk_abs (q, eq);
      mk_abs (p, eabs)
    od`;

(* p ==> q *)
val mk_imp_def = Define `
  mk_imp (p, q) =
    do
      imp <- mk_imp_const ();
      app <- mk_comb (imp, p);
      mk_comb (app, q)
    od`;

(* !p x. p x ==> p ((@) p) *)
val mk_select_ax_def = Define `
  mk_select_ax () =
    do
      p <- return (mk_var (strlit"p", Fun A Bool));
      x <- return (mk_var (strlit"x", A));
      px <- mk_comb (p, x);
      sp <- mk_comb (select_const, p);
      psp <- mk_comb (p, sp);
      imp <- mk_imp (px, psp);
      all <- mk_forall (x, imp);
      mk_forall (p, all)
    od`;

(* -- INFINITY_AX: |- ?f. injective f /\ ~surjective f --------------------- *)

(* (?) := \p. !q. (!x. p x ==> q) ==> q *)
val mk_ex_def = Define `
  mk_ex ty =
    do
      p <- return (mk_var (strlit"p", Fun ty Bool));
      q <- return (mk_var (strlit"q", Bool));
      x <- return (mk_var (strlit"x", ty));
      px <- mk_comb (p, x);
      imp <- mk_imp (px, q);
      l <- mk_forall (x, imp);
      imp2 <- mk_imp (l, q);
      all <- mk_forall (q, imp2);
      mk_abs (p, all)
    od`;

(* ?x. P[x] := (?) (\x. P[x]) *)
val mk_exists_def = Define `
  mk_exists (v, P) =
    do
      ty <- type_of v;
      ex <- mk_ex ty;
      pabs <- mk_abs (v, P);
      mk_comb (ex, pabs)
    od`;

(* surjective f :=     !y. ?x. y = f x *)
(* surjective   := \f. !y. ?x. y = f x *)
val mk_surj_def = Define `
  mk_surj f dom codom=
    do
      ty <- type_of f;
      y <- return (mk_var (strlit"y", codom));
      x <- return (mk_var (strlit"x", dom));
      fx <- mk_comb (f, x);
      eq <- mk_eq (y, fx);
      ex <- mk_exists (x, eq);
      mk_forall (y, ex);
    od`;

(* injective f :=     !x y. f x = f y ==> x = y *)
(* injective   := \f. !x y. f x = f y ==> x = y *)
val mk_inj_def = Define `
  mk_inj f dom =
    do
      ty <- type_of f;
      x <- return (mk_var (strlit"x", dom));
      y <- return (mk_var (strlit"y", dom));
      fx <- mk_comb (f, x);
      fy <- mk_comb (f, y);
      lhs <- mk_eq (fx, fy);
      rhs <- mk_eq (x, y);
      imp <- mk_imp (lhs, rhs);
      yall <- mk_forall (y, imp);
      mk_forall (x, yall);
    od`;

(* F := !p. p *)
val mk_false_def = Define `
  mk_false () =
    do
      p <- return (mk_var (strlit"p", Bool));
      mk_forall (p, p)
    od`;

(* (~) := \p. p ==> F *)
val mk_neg_const_def = Define `
  mk_neg_const () =
    do
      p <- return (mk_var (strlit"p", Bool));
      f <- mk_false ();
      imp <- mk_imp (p, f);
      mk_abs (p, imp)
    od`;

(* ~p := (~) p *)
val mk_neg_def = Define `
  mk_neg p =
    do
      neg <- mk_neg_const ();
      mk_comb (neg, p)
    od`;

val mk_infinity_ax_def = Define `
  mk_infinity_ax () =
    do
      f <- return (mk_var (strlit"f", Fun Ind Ind));
      surj <- mk_surj f Ind Ind;
      inj <- mk_inj f Ind;
      nsurj <- mk_neg surj;
      conj <- mk_conj (inj, nsurj);
      mk_exists (f, conj)
    od`;

(* ------------------------------------------------------------------------- *)
(* Start reader with axioms                                                  *)
(* ------------------------------------------------------------------------- *)

val ind_type_def = Define `
  ind_type = (strlit"ind", 0n)`;

val select_sym_def = Define `
  select_sym = (strlit"@", Fun (Fun A Bool) A)`;

val init_reader_def = Define `
  init_reader () =
    do
      ax <- mk_eta_ax (); new_axiom ax;
      new_constant select_sym;
      ax <- mk_select_ax (); new_axiom ax;
      new_type ind_type;
      ax <- mk_infinity_ax (); new_axiom ax;
      return ()
    od`;

val _ = export_theory ();
