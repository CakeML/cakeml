(*
  Parses an S-expression into a Dafny AST.
*)

open preamble
open result_monadTheory
open dafny_sexpTheory
open dafny_astTheory

val _ = new_theory "sexp_to_dafny";

(* TODO Possible improvement: Use a logging monad instead of result monad,
   to avoid having to write ... <- prefix_error here ... over and over again.

   Alternatively, one could perhaps add some notation for
   ... <- prefix_error here ... instead? *)

(* Helpers *)

Definition to_string_def:
  to_string (Atom s) = return s ∧
  to_string _ = fail "to_string: Was not Atom"
End

Definition to_bool_def:
  to_bool (Atom s) =
  (if (s = "True") then return T
   else if (s = "False") then return F
   else fail "to_bool: Not a bool") ∧
  to_bool _ = fail "to_bool: Was not Atom"
End

Definition to_int_def:
  to_int (Atom s) =
  (case fromString (implode s) of
   | NONE => fail "to_int: fromString failed"
   | SOME i => return i) ∧
  to_int _ = fail "to_int: Was not Atom"
End

Definition dest_expr_def:
  dest_expr (Expr ses) = return ses ∧
  dest_expr _ = fail "dest_expr: Was not Expr"
End

Definition split_def:
  split (Expr ((Atom s)::rest)) = return (s, rest) ∧
  split _ = fail "split: Did not match pattern"
End

Definition dest0_def:
  dest0 [] = return () ∧
  dest0 xs =
  fail ("dest0: Expected length 0, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest1_def:
  dest1 [x] = return x ∧
  dest1 xs =
  fail ("dest1: Expected length 1, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest2_def:
  dest2 [x₁; x₂] = return (x₁, x₂) ∧
  dest2 xs =
  fail ("dest2: Expected length 2, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest3_def:
  dest3 [x₁; x₂; x₃] = return (x₁, x₂, x₃) ∧
  dest3 xs =
  fail ("dest3: Expected length 3, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest5_def:
  dest5 [x₁; x₂; x₃; x₄; x₅] = return (x₁, x₂, x₃, x₄, x₅) ∧
  dest5 xs =
  fail ("dest5: Expected length 5, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest6_def:
  dest6 [x₁; x₂; x₃; x₄; x₅; x₆] = return (x₁, x₂, x₃, x₄, x₅, x₆) ∧
  dest6 xs =
  fail ("dest6: Expected length 6, received length "
        ++ num_to_string (LENGTH xs))
End

Definition dest9_def:
  dest9 [x₁; x₂; x₃; x₄; x₅; x₆; x₇; x₈; x₉] =
  return (x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉) ∧
  dest9 xs =
  fail ("dest9: Expected length 9, received length "
        ++ num_to_string (LENGTH xs))
End

Definition extend_path_def:
  extend_path cur next = cur ++ next ++ ":"
End

(* Converting to Dafny AST *)

(* unescape_string is adapted from Dafny (MIT License):
   https://github.com/dafny-lang/dafny - function UnescapedCharacters at
   Source/DafnyCore/Generic/Util.cs *)
Definition unescape_string_def:
  (unescape_string (c1::c2::rest) verbatim =
  if verbatim then
    if c1 = #"\"" ∧ c2 = #"\"" then
      #"\""::(unescape_string rest verbatim)
    else
      c1::(unescape_string (c2::rest) verbatim)
  else if c1 = #"\\" ∧ c2 = #"'" then
    #"'"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\"" then
    #"\""::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\\" then
    #"\\"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"0" then
    #"\000"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"n" then
    #"\n"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"r" then
    #"\r"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"t" then
    #"\t"::(unescape_string rest verbatim)
  else
    c1::(unescape_string (c2::rest) verbatim)) ∧
  (unescape_string (c::rest) verbatim = c::(unescape_string rest verbatim)) ∧
  (unescape_string "" _ = "")
End

(* NOTE We do not use do notation for arguments of a recursive call, to avoid
   problems with the termination proofs. *)

Definition to_type_def:
  to_type se =
  (let here = extend_path "" "to_type" in
   (case split se of
    | INL err => fail (here ++ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      if (cns = "IntT") then
        do _ <- prefix_error here (dest0 args); return IntT od
      else if (cns = "BoolT") then
        do _ <- prefix_error here (dest0 args); return BoolT od
      else if (cns = "ArrayT") then
        (case dest1 args of
         | INL err => fail (here ++ err)
         | INR t => do t <- to_type t; return (ArrayT t) od)
      else
        fail (here ++ " Unexpected constructor")))
Termination
  wf_rel_tac ‘measure sexp_size’
  >> gvs [oneline split_def, oneline dest1_def, AllCaseEqs (), sexp_size_def]
End

Definition to_string_type_tup_def:
  to_string_type_tup se =
  (let here = extend_path "" "to_string_type_tup" in
   do
     tup <- prefix_error here (dest_expr se);
     (s, t) <- prefix_error here (dest2 tup);
     s <- prefix_error here (to_string s);
     t <- prefix_error here (to_type t);
     return (s, t)
   od)
End

Definition to_string_type_tup_lst_def:
  to_string_type_tup_lst se =
  (let here = extend_path "" "to_string_type_tup_lst" in
   do
     lst <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_string_type_tup lst)
   od)
End

Definition to_bop_def:
  to_bop se =
  (let here = extend_path "" "to_bop" in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = "Lt") then
       do _ <- prefix_error here (dest0 args); return Lt od
     else if (cns = "Le") then
       do _ <- prefix_error here (dest0 args); return Le od
     else if (cns = "Ge") then
       do _ <- prefix_error here (dest0 args); return Ge od
     else if (cns = "Eq") then
       do _ <- prefix_error here (dest0 args); return Eq od
     else if (cns = "Neq") then
       do _ <- prefix_error here (dest0 args); return Neq od
     else if (cns = "Sub") then
       do _ <- prefix_error here (dest0 args); return Sub od
     else if (cns = "Add") then
       do _ <- prefix_error here (dest0 args); return Add od
     else if (cns = "Mul") then
       do _ <- prefix_error here (dest0 args); return Mul od
     else if (cns = "Div") then
       do _ <- prefix_error here (dest0 args); return Div od
     else if (cns = "And") then
       do _ <- prefix_error here (dest0 args); return And od
     else if (cns = "Imp") then
       do _ <- prefix_error here (dest0 args); return Imp od
     else if (cns = "Or") then
       do _ <- prefix_error here (dest0 args); return Or od
     else
       fail (here ++ " Unexpected constructor")
   od)
End

Definition to_literal_def:
  to_literal se =
  (let here = extend_path "" "to_literal" in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = "IntLit") then
       do
         i <- prefix_error here (dest1 args);
         i <- prefix_error here (to_int i);
         return (IntLit i)
       od
     else if (cns = "BoolLit") then
       do
         b <- prefix_error here (dest1 args);
         b <- prefix_error here (to_bool b);
         return (BoolLit b)
       od
     else if (cns = "StringLit") then
       do
         (is_verbatim, s) <- prefix_error here (dest2 args);
         is_verbatim <- prefix_error here (to_bool is_verbatim);
         s <- prefix_error here (to_string s);
         return (StringLit (unescape_string s is_verbatim))
       od
     else
       fail (here ++ " Unexpected constructor")
   od)
End

Definition to_expression_def:
  to_expression se =
  (let here = extend_path "" "to_expression" in
   (case split se of
    | INL err => fail (here ++ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      (if (cns = "FunctionCall") then
         (case dest2 args of
          | INL err => fail (here ++ err)
          | INR (s, es) =>
            (case dest_expr es of
             | INL err => fail (here ++ err)
             | INR es =>
               do
                 es <- prefix_error here (map_to_expression es);
                 s <- prefix_error here (to_string s);
                 return (FunctionCall s es)
               od))
       else if (cns = "IdentifierExp") then
         do
           (s, t) <- prefix_error here (dest2 args);
           s <- prefix_error here (to_string s);
           t <- prefix_error here (to_type t);
           return (IdentifierExp s t)
         od
       else if (cns = "BinaryExp") then
         (case dest3 args of
          | INL err => fail (here ++ err)
          | INR (bop, e₀, e₁) =>
            do
              e₀ <- prefix_error here (to_expression e₀);
              e₁ <- prefix_error here (to_expression e₁);
              bop <- prefix_error here (to_bop bop);
              return (BinaryExp bop e₀ e₁)
            od)
       else if (cns = "LiteralExp") then
         do
           lit <- prefix_error here (dest1 args);
           lit <- prefix_error here (to_literal lit);
           return (LiteralExp lit)
         od
       else if (cns = "ArrayLen") then
         (case dest1 args of
          | INL err => fail (here ++ err)
          | INR e =>
            do
              e <- prefix_error here (to_expression e);
              return (ArrayLen e)
            od)
       else if (cns = "ArraySelect") then
         (case dest2 args of
          | INL err => fail (here ++ err)
          | INR (arr, idx) =>
            do
              arr <- prefix_error here (to_expression arr);
              idx <- prefix_error here (to_expression idx);
              return (ArraySelect arr idx)
            od)
       else if (cns = "ITE") then
         (case dest3 args of
          | INL err => fail (here ++ err)
          | INR (tst, thn, els) =>
            do
              tst <- prefix_error here (to_expression tst);
              thn <- prefix_error here (to_expression thn);
              els <- prefix_error here (to_expression els);
              return (ITE tst thn els)
            od)
       else if (cns = "ForallExp") then
         (case dest2 args of
          | INL err => fail (here ++ err)
          | INR (bound_vars, term) =>
            do
              bound_vars <- prefix_error here (to_string_type_tup bound_vars);
              term <- prefix_error here (to_expression term);
              return (ForallExp bound_vars term)
            od)
       else
         fail (here ++ " Unsupported constructor")))) ∧
  map_to_expression [] = return [] ∧
  map_to_expression (e::es) =
  do
    e <- to_expression e;
    es <- map_to_expression es;
    return (e:: es)
  od
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL se => sexp_size se
                           | INR ses => sexp1_size ses)’
  >> gvs [oneline split_def, oneline dest1_def, oneline dest2_def,
          oneline dest3_def, oneline dest_expr_def, AllCaseEqs (),
          sexp_size_def]
End

Definition to_expression_list_def:
  to_expression_list se =
  (let here = extend_path "" "to_expression_list" in
   do
     es <- prefix_error here (dest_expr se);
     prefix_error here (map_to_expression es)
   od)
End

Definition to_rhs_exp_def:
  to_rhs_exp se =
  (let here = extend_path "" "to_rhs_exp" in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = "ExpRhs") then
       do
         e <- prefix_error here (dest1 args);
         e <- prefix_error here (to_expression e);
         return (ExpRhs e)
       od
     else if (cns = "MethodCall") then
       do
         (s, es) <- prefix_error here (dest2 args);
         s <- prefix_error here (to_string s);
         es <- prefix_error here (to_expression_list es);
         return (MethodCall s es)
       od
     else if (cns = "AllocArray") then
       do
         (t, e₀, e₁) <- prefix_error here (dest3 args);
         t <- prefix_error here (to_type t);
         e₀ <- prefix_error here (to_expression e₀);
         e₁ <- prefix_error here (to_expression e₁);
         return (AllocArray t e₀ e₁)
       od
     else
       fail (here ++ " Unsupported constructor")
   od)
End

Definition to_rhs_exp_list_def:
  to_rhs_exp_list se =
  (let here = extend_path "" "to_rhs_exp_list" in
   do
     es <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_rhs_exp es)
   od)
End

Definition to_statement_def:
  to_statement se =
  (let here = extend_path "" "to_statement" in
   (case split se of
    | INL err => fail (here ++ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      (if (cns = "Skip") then
         do
           _ <- prefix_error here (dest0 args);
           return Skip
         od
       else if (cns = "Then") then
         (case dest2 args of
          | INL err => fail (here ++ err)
          | INR (stmt₁, stmt₂) =>
            do
              stmt₁ <- prefix_error here (to_statement stmt₁);
              stmt₂ <- prefix_error here (to_statement stmt₂);
              return (Then stmt₁ stmt₂)
            od)
       else if (cns = "Assign") then
         do
           (lhss, rhss) <- prefix_error here (dest2 args);
           lhss <- prefix_error here (to_expression_list lhss);
           rhss <- prefix_error here (to_rhs_exp_list rhss);
           return (Assign lhss rhss)
         od
       else if (cns = "If") then
         (case dest3 args of
          | INL err => fail (here ++ err)
          | INR (grd, thn, els) =>
            do
              grd <- prefix_error here (to_expression grd);
              thn <- prefix_error here (to_statement thn);
              els <- prefix_error here (to_statement els);
              return (If grd thn els)
            od)
       else if (cns = "VarDecl") then
         (case dest3 args of
          | INL err => fail (here ++ err)
          | INR (locals, assign, scope) =>
            do
              locals <- prefix_error here (to_string_type_tup_lst locals);
              assign <- prefix_error here (to_statement assign);
              scope <- prefix_error here (to_statement scope);
              return (VarDecl locals assign scope)
            od)
       else if (cns = "While") then
         (case dest5 args of
          | INL err => fail (here ++ err)
          | INR (grd, invs, decrs, mods, bdy) =>
            do
              grd <- prefix_error here (to_expression grd);
              invs <- prefix_error here (to_expression_list invs);
              decrs <- prefix_error here (to_expression_list decrs);
              mods <- prefix_error here (to_expression_list mods);
              bdy <- prefix_error here (to_statement bdy);
              return (While grd invs decrs mods bdy)
            od)
       else if (cns = "Print") then
         do
           es <- prefix_error here (dest1 args);
           es <- prefix_error here (to_expression_list es);
           return (Print es)
         od
       else if (cns = "Return") then
         do
           rhss <- prefix_error here (dest1 args);
           rhss <- prefix_error here (to_rhs_exp_list rhss);
           return (Return rhss)
         od
       else if (cns = "Assert") then
         do
           e <- prefix_error here (dest1 args);
           e <- prefix_error here (to_expression e);
           return (Assert e)
         od
       else
         fail (here ++ " Unsupported constructor"))))
Termination
  wf_rel_tac ‘measure sexp_size’
  >> gvs [oneline split_def, oneline dest2_def, oneline dest3_def,
          oneline dest5_def, AllCaseEqs (), sexp_size_def]
End

Definition to_member_decl_def:
  to_member_decl se =
  (let here = extend_path "" "to_member_decl" in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = "Method") then
       do
         (name, ins, reqs, ens, reads,
          decrs, outs, mods, body) <- prefix_error here (dest9 args);
         name <- prefix_error here (to_string name);
         ins <- prefix_error here (to_string_type_tup_lst ins);
         reqs <- prefix_error here (to_expression_list reqs);
         ens <- prefix_error here (to_expression_list ens);
         reads <- prefix_error here (to_expression_list reads);
         decrs <- prefix_error here (to_expression_list decrs);
         outs <- prefix_error here (to_string_type_tup_lst outs);
         mods <- prefix_error here (to_expression_list mods);
         body <- prefix_error here (to_statement body);
         return (Method name ins reqs ens reads decrs outs mods body)
       od
     else if (cns = "Function") then
       do
         (name, ins, res_t,
          reqs, reads, body) <- prefix_error here (dest6 args);
         name <- prefix_error here (to_string name);
         ins <- prefix_error here (to_string_type_tup_lst ins);
         res_t <- prefix_error here (to_type res_t);
         reqs <- prefix_error here (to_expression_list reqs);
         reads <- prefix_error here (to_expression_list reads);
         body <- prefix_error here (to_expression body);
         return (Function name ins res_t reqs reads body)
       od
     else
       fail (here ++ " Unsupported constructor")
   od)
End

Definition to_program_def:
  to_program se =
  (let here = extend_path "" "to_program" in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = "Program") then
       do
         members <- prefix_error here (dest1 args);
         members <- prefix_error here (dest_expr members);
         prefix_error here (result_mmap to_member_decl members)
       od
     else
       fail (here ++ " Unsupported constructor")
   od)
End

val _ = export_theory ();
