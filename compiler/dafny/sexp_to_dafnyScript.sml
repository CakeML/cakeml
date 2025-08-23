(*
  Parses an S-expression into a Dafny AST.
*)
Theory sexp_to_dafny
Ancestors
  result_monad dafny_sexp dafny_ast mlint
Libs
  preamble


(* TODO Possible improvement: Use a logging monad instead of result monad,
   to avoid having to write ... <- prefix_error here ... over and over again.

   Alternatively, one could perhaps add some notation for
   ... <- prefix_error here ... instead? *)

(* Helpers *)

Definition to_mlstring_def:
  to_mlstring (Atom s) = return s ∧
  to_mlstring _ = fail «to_mlstring: Was not Atom»
End

Definition to_bool_def:
  to_bool (Atom s) =
  (if (s = «True») then return T
   else if (s = «False») then return F
   else fail «to_bool: Not a bool») ∧
  to_bool _ = fail «to_bool: Was not Atom»
End

Definition to_int_def:
  to_int (Atom s) =
  (case fromString s of
   | NONE => fail «to_int: fromString failed»
   | SOME i => return i) ∧
  to_int _ = fail «to_int: Was not Atom»
End

Definition dest_expr_def:
  dest_expr (Expr ses) = return ses ∧
  dest_expr _ = fail «dest_expr: Was not Expr»
End

Definition split_def:
  split (Expr ((Atom s)::rest)) = return (s, rest) ∧
  split _ = fail «split: Did not match pattern»
End

Definition dest_fail_def[simp]:
  dest_fail expect xs =
  let expect_len = num_to_str expect;
      receive_len = num_to_str (LENGTH xs) in
    fail (concat [«dest»; expect_len; «: Expected length »; expect_len;
                  «, received length »; receive_len])
End

Definition dest0_def:
  dest0 [] = return () ∧
  dest0 xs = dest_fail 0 xs
End

Definition dest1_def:
  dest1 [x] = return x ∧
  dest1 xs = dest_fail 1 xs
End

Definition dest2_def:
  dest2 [x₁; x₂] = return (x₁, x₂) ∧
  dest2 xs = dest_fail 2 xs
End

Definition dest3_def:
  dest3 [x₁; x₂; x₃] = return (x₁, x₂, x₃) ∧
  dest3 xs = dest_fail 3 xs
End

Definition dest5_def:
  dest5 [x₁; x₂; x₃; x₄; x₅] = return (x₁, x₂, x₃, x₄, x₅) ∧
  dest5 xs = dest_fail 5 xs
End

Definition dest7_def:
  dest7 [x₁; x₂; x₃; x₄; x₅; x₆; x₇] = return (x₁, x₂, x₃, x₄, x₅, x₆, x₇) ∧
  dest7 xs = dest_fail 7 xs
End

Definition dest9_def:
  dest9 [x₁; x₂; x₃; x₄; x₅; x₆; x₇; x₈; x₉] =
  return (x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉) ∧
  dest9 xs = dest_fail 9 xs
End

Definition bad_con_def[simp]:
  bad_con here = fail (here ^ « Unexpected constructor»)
End

(* Converting to Dafny AST *)

(* NOTE We do not use do notation for arguments of a recursive call, to avoid
   problems with the termination proofs. *)

Definition to_type_def:
  to_type se =
  (let here = extend_path «» «to_type» in
   (case split se of
    | INL err => fail (here ^ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      if (cns = «BoolT») then
        do _ <- prefix_error here (dest0 args); return BoolT od
      else if (cns = «IntT») then
        do _ <- prefix_error here (dest0 args); return IntT od
      else if (cns = «StrT») then
        do _ <- prefix_error here (dest0 args); return StrT od
      else if (cns = «ArrT») then
        (case dest1 args of
         | INL err => fail (here ^ err)
         | INR t => do t <- to_type t; return (ArrT t) od)
      else
        bad_con here))
Termination
  wf_rel_tac ‘measure sexp_size’
  >> gvs [oneline split_def, oneline dest1_def, AllCaseEqs (), sexp_size_def]
End

Definition to_mlstring_type_tup_def:
  to_mlstring_type_tup se =
  (let here = extend_path «» «to_mlstring_type_tup» in
   do
     tup <- prefix_error here (dest_expr se);
     (s, t) <- prefix_error here (dest2 tup);
     s <- prefix_error here (to_mlstring s);
     t <- prefix_error here (to_type t);
     return (s, t)
   od)
End

Definition to_mlstring_type_tup_lst_def:
  to_mlstring_type_tup_lst se =
  (let here = extend_path «» «to_mlstring_type_tup_lst» in
   do
     lst <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_mlstring_type_tup lst)
   od)
End

Definition to_un_op_def:
  to_un_op se =
  (let here = extend_path «» «to_un_op» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «Not») then
       do _ <- prefix_error here (dest0 args); return Not od
     else
       bad_con here
   od)
End

Definition to_bin_op_def:
  to_bin_op se =
  (let here = extend_path «» «to_bin_op» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «Lt») then
       do _ <- prefix_error here (dest0 args); return Lt od
     else if (cns = «Le») then
       do _ <- prefix_error here (dest0 args); return Le od
     else if (cns = «Ge») then
       do _ <- prefix_error here (dest0 args); return Ge od
     else if (cns = «Eq») then
       do _ <- prefix_error here (dest0 args); return Eq od
     else if (cns = «Neq») then
       do _ <- prefix_error here (dest0 args); return Neq od
     else if (cns = «Sub») then
       do _ <- prefix_error here (dest0 args); return Sub od
     else if (cns = «Add») then
       do _ <- prefix_error here (dest0 args); return Add od
     else if (cns = «Mul») then
       do _ <- prefix_error here (dest0 args); return Mul od
     else if (cns = «And») then
       do _ <- prefix_error here (dest0 args); return And od
     else if (cns = «Or») then
       do _ <- prefix_error here (dest0 args); return Or od
     else if (cns = «Imp») then
       do _ <- prefix_error here (dest0 args); return Imp od
     else if (cns = «Div») then
       do _ <- prefix_error here (dest0 args); return Div od
     else if (cns = «Mod») then
       do _ <- prefix_error here (dest0 args); return Mod od
     else
       bad_con here
   od)
End

Definition to_lit_def:
  to_lit se =
  (let here = extend_path «» «to_lit» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «BoolL») then
       do
         b <- prefix_error here (dest1 args);
         b <- prefix_error here (to_bool b);
         return (BoolL b)
       od
     else if (cns = «IntL») then
       do
         i <- prefix_error here (dest1 args);
         i <- prefix_error here (to_int i);
         return (IntL i)
       od
     else if (cns = «StrL») then
       do
         s <- prefix_error here (dest1 args);
         s <- prefix_error here (to_mlstring s);
         return (StrL s)
       od
     else
       bad_con here
   od)
End

Definition to_exp_def:
  to_exp se =
  (let here = extend_path «» «to_exp» in
   (case split se of
    | INL err => fail (here ^ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      (if (cns = «Lit») then
         do
           l <- prefix_error here (dest1 args);
           l <- prefix_error here (to_lit l);
           return (Lit l)
         od
       else if (cns = «Var») then
         do
           s <- prefix_error here (dest1 args);
           s <- prefix_error here (to_mlstring s);
           return (Var s)
         od
       else if (cns = «Exp_If») then
         (case dest3 args of
          | INL err => fail (here ^ err)
          | INR (tst, thn, els) =>
            do
              tst <- prefix_error here (to_exp tst);
              thn <- prefix_error here (to_exp thn);
              els <- prefix_error here (to_exp els);
              return (If tst thn els)
            od)
       else if (cns = «UnOp») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (uop, e) =>
            do
              uop <- prefix_error here (to_un_op uop);
              e <- prefix_error here (to_exp e);
              return (UnOp uop e)
            od)
       else if (cns = «BinOp») then
         (case dest3 args of
          | INL err => fail (here ^ err)
          | INR (bop, e₀, e₁) =>
            do
              e₀ <- prefix_error here (to_exp e₀);
              e₁ <- prefix_error here (to_exp e₁);
              bop <- prefix_error here (to_bin_op bop);
              return (BinOp bop e₀ e₁)
            od)
       else if (cns = «ArrLen») then
         (case dest1 args of
          | INL err => fail (here ^ err)
          | INR e =>
            do
              e <- prefix_error here (to_exp e);
              return (ArrLen e)
            od)
       else if (cns = «ArrSel») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (arr, idx) =>
            do
              arr <- prefix_error here (to_exp arr);
              idx <- prefix_error here (to_exp idx);
              return (ArrSel arr idx)
            od)
       else if (cns = «FunCall») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (s, es) =>
            (case dest_expr es of
             | INL err => fail (here ^ err)
             | INR es =>
               do
                 es <- prefix_error here (map_to_exp es);
                 s <- prefix_error here (to_mlstring s);
                 return (FunCall s es)
               od))
       else if (cns = «Forall») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (bound_var, term) =>
            do
              bound_var <- prefix_error here (to_mlstring_type_tup bound_var);
              term <- prefix_error here (to_exp term);
              return (Forall bound_var term)
            od)
       else if (cns = «Old») then
         (case dest1 args of
          | INL err => fail (here ^ err)
          | INR old_e =>
            do
              old_e <- prefix_error here (to_exp old_e);
              return (Old old_e)
            od)
       else
         bad_con here))) ∧
  map_to_exp [] = return [] ∧
  map_to_exp (e::es) =
  do
    e <- to_exp e;
    es <- map_to_exp es;
    return (e::es)
  od
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL se => sexp_size se
                           | INR ses => sexp1_size ses)’
  >> gvs [oneline split_def, oneline dest1_def, oneline dest2_def,
          oneline dest3_def, oneline dest_expr_def, AllCaseEqs (),
          sexp_size_def]
End

Definition to_exp_list_def:
  to_exp_list se =
  (let here = extend_path «» «to_exp_list» in
   do
     es <- prefix_error here (dest_expr se);
     prefix_error here (map_to_exp es)
   od)
End

Definition to_exp_type_tup_def:
  to_exp_type_tup se =
  (let here = extend_path «» «to_exp_type_tup» in
   do
     tup <- prefix_error here (dest_expr se);
     (s, t) <- prefix_error here (dest2 tup);
     s <- prefix_error here (to_exp s);
     t <- prefix_error here (to_type t);
     return (s, t)
   od)
End

Definition to_exp_type_tup_lst_def:
  to_exp_type_tup_lst se =
  (let here = extend_path «» «to_exp_type_tup_lst» in
   do
     lst <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_exp_type_tup lst)
   od)
End

Definition to_lhs_exp_def:
  to_lhs_exp se =
  (let here = extend_path «» «to_lhs_exp» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «VarLhs») then
       do
         s <- prefix_error here (dest1 args);
         s <- prefix_error here (to_mlstring s);
         return (VarLhs s)
       od
     else if (cns = «ArrSelLhs») then
       do
         (arr, idx) <- prefix_error here (dest2 args);
         arr <- prefix_error here (to_exp arr);
         idx <- prefix_error here (to_exp idx);
         return (ArrSelLhs arr idx)
       od
     else
       bad_con here
   od)
End

Definition to_lhs_exp_list_def:
  to_lhs_exp_list se =
  (let here = extend_path «» «to_lhs_exp_list» in
   do
     es <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_lhs_exp es)
   od)
End

Definition to_rhs_exp_def:
  to_rhs_exp se =
  (let here = extend_path «» «to_rhs_exp» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «ExpRhs») then
       do
         e <- prefix_error here (dest1 args);
         e <- prefix_error here (to_exp e);
         return (ExpRhs e)
       od
     else if (cns = «ArrAlloc») then
       do
         (len, init) <- prefix_error here (dest2 args);
         len <- prefix_error here (to_exp len);
         init <- prefix_error here (to_exp init);
         return (ArrAlloc len init)
       od
     else
       bad_con here
   od)
End

Definition to_lhs_rhs_exp_tup_def:
  to_lhs_rhs_exp_tup se =
  (let here = extend_path «» «to_lhs_rhs_exp_tup» in
   do
     tup <- prefix_error here (dest_expr se);
     (lhs, rhs) <- prefix_error here (dest2 tup);
     lhs <- prefix_error here (to_lhs_exp lhs);
     rhs <- prefix_error here (to_rhs_exp rhs);
     return (lhs, rhs)
   od)
End

Definition to_lhs_rhs_exp_tup_list_def:
  to_lhs_rhs_exp_tup_list se =
  (let here = extend_path «» «to_lhs_rhs_exp_tup_list» in
   do
     lst <- prefix_error here (dest_expr se);
     prefix_error here (result_mmap to_lhs_rhs_exp_tup lst)
   od)
End

Definition to_statement_def:
  to_statement se =
  (let here = extend_path «» «to_statement» in
   (case split se of
    | INL err => fail (here ^ err)
    | INR (cns, args) =>
      let here = extend_path here cns in
      (if (cns = «Skip») then
         do
           _ <- prefix_error here (dest0 args);
           return Skip
         od
       else if (cns = «Assert») then
         do
           e <- prefix_error here (dest1 args);
           e <- prefix_error here (to_exp e);
           return (Assert e)
         od
       else if (cns = «Then») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (stmt₁, stmt₂) =>
            do
              stmt₁ <- prefix_error here (to_statement stmt₁);
              stmt₂ <- prefix_error here (to_statement stmt₂);
              return (Then stmt₁ stmt₂)
            od)
       else if (cns = «If») then
         (case dest3 args of
          | INL err => fail (here ^ err)
          | INR (grd, thn, els) =>
            do
              grd <- prefix_error here (to_exp grd);
              thn <- prefix_error here (to_statement thn);
              els <- prefix_error here (to_statement els);
              return (If grd thn els)
            od)
       else if (cns = «Dec») then
         (case dest2 args of
          | INL err => fail (here ^ err)
          | INR (local, scope) =>
            do
              local <- prefix_error here (to_mlstring_type_tup local);
              scope <- prefix_error here (to_statement scope);
              return (Dec local scope)
            od)
       else if (cns = «Assign») then
         do
           ass <- prefix_error here (dest1 args);
           ass <- prefix_error here (to_lhs_rhs_exp_tup_list ass);
           return (Assign ass)
         od
       else if (cns = «While») then
         (case dest5 args of
          | INL err => fail (here ^ err)
          | INR (grd, invs, decrs, mods, bdy) =>
            do
              grd <- prefix_error here (to_exp grd);
              invs <- prefix_error here (to_exp_list invs);
              decrs <- prefix_error here (to_exp_list decrs);
              mods <- prefix_error here (to_exp_list mods);
              bdy <- prefix_error here (to_statement bdy);
              return (While grd invs decrs mods bdy)
            od)
       else if (cns = «Print») then
         do
           (e, ty) <- prefix_error here (dest2 args);
           e <- prefix_error here (to_exp e);
           ty <- prefix_error here (to_type ty);
           return (Print e ty)
         od
       else if (cns = «MetCall») then
         do
           (lhss, name, met_args) <- prefix_error here (dest3 args);
           lhss <- prefix_error here (to_lhs_exp_list lhss);
           name <- prefix_error here (to_mlstring name);
           met_args <- prefix_error here (to_exp_list met_args);
           return (MetCall lhss name met_args)
         od
       else if (cns = «Return») then
         do
           _ <- prefix_error here (dest0 args);
           return Return
         od
       else
         bad_con here)))
Termination
  wf_rel_tac ‘measure sexp_size’
  >> gvs [oneline split_def, oneline dest2_def, oneline dest3_def,
          oneline dest5_def, AllCaseEqs (), sexp_size_def]
End

Definition to_member_decl_def:
  to_member_decl se =
  (let here = extend_path «» «to_member_decl» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «Method») then
       do
         (name, ins, reqs, ens, reads,
          decrs, outs, mods, body) <- prefix_error here (dest9 args);
         name <- prefix_error here (to_mlstring name);
         ins <- prefix_error here (to_mlstring_type_tup_lst ins);
         reqs <- prefix_error here (to_exp_list reqs);
         ens <- prefix_error here (to_exp_list ens);
         reads <- prefix_error here (to_exp_list reads);
         decrs <- prefix_error here (to_exp_list decrs);
         outs <- prefix_error here (to_mlstring_type_tup_lst outs);
         mods <- prefix_error here (to_exp_list mods);
         body <- prefix_error here (to_statement body);
         return (Method name ins reqs ens reads decrs outs mods body)
       od
     else if (cns = «Function») then
       do
         (name, ins, res_t,
          reqs, reads, decrs, body) <- prefix_error here (dest7 args);
         name <- prefix_error here (to_mlstring name);
         ins <- prefix_error here (to_mlstring_type_tup_lst ins);
         res_t <- prefix_error here (to_type res_t);
         reqs <- prefix_error here (to_exp_list reqs);
         reads <- prefix_error here (to_exp_list reads);
         decrs <- prefix_error here (to_exp_list decrs);
         body <- prefix_error here (to_exp body);
         return (Function name ins res_t reqs reads decrs body)
       od
     else
       bad_con here
   od)
End

Definition to_program_def:
  to_program se =
  (let here = extend_path «» «to_program» in
   do
     (cns, args) <- prefix_error here (split se);
     here <<- extend_path here cns;
     if (cns = «Program») then
       do
         members <- prefix_error here (dest1 args);
         members <- prefix_error here (dest_expr members);
         decls <- prefix_error here (result_mmap to_member_decl members);
         return (Program decls)
       od
     else
       bad_con here
   od)
End

