(*
  Defines functions for turning a ctxt & thm to a string and back
*)
Theory print_thm
Ancestors
  holKernel mlstring mlint mlsexp
Libs
  preamble

(* encoding into v *)

Definition ty_to_v_def:
  ty_to_v (Tyvar s) = Expr [Atom «Tyvar»; Atom s] ∧
  ty_to_v (Tyapp s tys) = Expr (Atom «Tyapp» :: Atom s :: (MAP ty_to_v tys))
Termination
  WF_REL_TAC ‘measure type_size’
End

Definition term_to_v_def:
  term_to_v (Var s ty) = Expr [Atom «Var»; Atom s; ty_to_v ty] ∧
  term_to_v (Const s ty) = Expr [Atom «Const»; Atom s; ty_to_v ty] ∧
  term_to_v (Comb f x) = Expr [Atom «Comb»; term_to_v f; term_to_v x] ∧
  term_to_v (Abs f x) = Expr [Atom «Abs»; term_to_v f; term_to_v x]
End

Definition thm_to_v_def:
  thm_to_v (Sequent ts t) =
    Expr [Atom «Sequent»; Expr (MAP term_to_v ts); term_to_v t]
End

Definition update_to_v_def:
  update_to_v (ConstSpec xs t) =
    Expr [Atom «ConstSpec»;
          Expr (MAP (λ(s,t). Expr [Atom s; term_to_v t]) xs);
          term_to_v t] ∧
  update_to_v (TypeDefn s1 t s2 s3) =
    Expr [Atom «TypeDefn»;
          Atom s1; term_to_v t; Atom s2; Atom s3] ∧
  update_to_v (NewType s n) =
    Expr [Atom «NewType»; Atom s; Atom (mlint$num_to_str n)] ∧
  update_to_v (NewConst s ty) =
    Expr [Atom «NewConst»; Atom s; ty_to_v ty] ∧
  update_to_v (NewAxiom t) =
    Expr [Atom «NewAxiom»; term_to_v t]
End

(* decoding from v *)

Theorem MEM_IMP_sexp_size_LESS:
  ∀xs a. MEM a xs ⇒ sexp_size a < list_size sexp_size xs
Proof
  Induct \\ rw [] \\ simp [] \\ res_tac \\ fs []
QED

Definition v_to_str_def[simp]:
  v_to_str (Atom s) = s
End

Definition v_to_ty_def:
  v_to_ty (Expr xs) =
    if HD xs = Atom «Tyvar» then
      Tyvar (v_to_str (EL 1 xs))
    else if LENGTH xs < 2 then ARB else
      Tyapp (v_to_str (EL 1 xs)) (MAP v_to_ty (TL (TL xs)))
Termination
  WF_REL_TAC ‘measure sexp_size’
  \\ Cases \\ simp []
  \\ Cases_on ‘t’ \\ simp [] \\ rw []
  \\ imp_res_tac MEM_IMP_sexp_size_LESS \\ fs []
End

Definition v_to_term_def:
  v_to_term (Expr xs) =
    if LENGTH xs < 3 then ARB
    else if HD xs = Atom «Comb» then
      Comb (v_to_term (EL 1 xs)) (v_to_term (EL 2 xs))
    else if HD xs = Atom «Abs» then
      Abs (v_to_term (EL 1 xs)) (v_to_term (EL 2 xs))
    else if HD xs = Atom «Var» then
      Var (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))
    else
      Const (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))
Termination
  WF_REL_TAC  ‘measure sexp_size’ \\ rw []
  \\ rpt (rename [‘LENGTH xs’] \\ Cases_on ‘xs’ \\ gvs [])
End

Definition v_to_thm_def:
  v_to_thm (Expr xs) =
    Sequent
      (case EL 1 xs of Expr ys => MAP v_to_term ys)
      (v_to_term (EL 2 xs))
End

Definition v_to_update_def:
  v_to_update (Expr xs) =
    if HD xs = Atom «ConstSpec» then
      ConstSpec
        (case EL 1 xs of Expr ys =>
           MAP (λy. case y of Expr zs =>
                     (v_to_str (EL 0 zs), v_to_term (EL 1 zs))) ys)
        (v_to_term (EL 2 xs))
    else if HD xs = Atom «TypeDefn» then
      TypeDefn (v_to_str (EL 1 xs))
               (v_to_term (EL 2 xs))
               (v_to_str (EL 3 xs))
               (v_to_str (EL 4 xs))
    else if HD xs = Atom «NewType» then
      NewType (v_to_str (EL 1 xs)) (THE (fromNatString (v_to_str (EL 2 xs))))
    else if HD xs = Atom «NewConst» then
      NewConst (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))
    else
      NewAxiom (v_to_term (EL 1 xs))
End

Theorem ty_to_v_thm[simp]:
  ∀ty. v_to_ty (ty_to_v ty) = ty
Proof
  ho_match_mp_tac ty_to_v_ind \\ rw []
  \\ simp [ty_to_v_def,v_to_ty_def]
  \\ fs [MAP_MAP_o,miscTheory.MAP_EQ_ID]
QED

Theorem term_to_v_thm[simp]:
  ∀t. v_to_term (term_to_v t) = t
Proof
  Induct \\ simp [term_to_v_def,Once v_to_term_def]
QED

Theorem thm_to_v_thm[simp]:
  ∀th. v_to_thm (thm_to_v th) = th
Proof
  Cases
  \\ simp [thm_to_v_def,Once v_to_thm_def]
  \\ fs [MAP_MAP_o,miscTheory.MAP_EQ_ID]
QED

Theorem update_to_v_update[simp]:
  ∀u. v_to_update (update_to_v u) = u
Proof
  Cases
  \\ simp [update_to_v_def,Once v_to_update_def]
  \\ fs [MAP_MAP_o,miscTheory.MAP_EQ_ID,FORALL_PROD]
QED

(* main definition *)

Definition thm_to_string_def:
  thm_to_string (ctxt:update list) (th:thm) =
    concat
      ([strlit "# The following is a theorem of higher-order logic\n\n"] ++
       [sexp_to_pretty_string (thm_to_v th)] ++
       [strlit "\n# which is proved in the following context\n"] ++
       FLAT (MAP (λdef. [«\n»; sexp_to_pretty_string (update_to_v def)]) ctxt))
End

(* it has an inverse: *)

Definition char_list_to_defs_def:
  char_list_to_defs input =
    case mlsexp$parse input of
    | INL _ => []
    | INR (x,rest) => v_to_update x :: char_list_to_defs rest
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ drule parse_IMP_LENGTH_LESS \\ simp []
End

Definition string_to_thm_def:
  string_to_thm s =
    let rest = dropWhile (λc. c ≠ #"\n") (explode s) in
    let (th_v, rest) = OUTR $ mlsexp$parse rest in
    let rest = dropWhile (λc. c ≠ #"\n") (TL (TL rest)) in
      (char_list_to_defs rest, v_to_thm th_v)
End

Theorem to_explode[local]:
  (case s of strlit t => t) = explode s
Proof
  Cases_on ‘s’ \\ simp []
QED

Theorem string_to_thm_thm_to_string:
  string_to_thm (thm_to_string ctxt th) = (ctxt,th)
Proof
  fs [thm_to_string_def,concat_append]
  \\ simp [string_to_thm_def,parse_space]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rewrite_tac [parse_sexp_to_pretty_string, OUTR]
  \\ simp_tac std_ss [thm_to_v_thm] \\ simp []
  \\ simp [Once char_list_to_defs_def,parse_space]
  \\ simp [GSYM char_list_to_defs_def]
  \\ Induct_on ‘ctxt’ >- EVAL_TAC
  \\ rw [] \\ fs [concat_def,to_explode]
  \\ simp [Once char_list_to_defs_def,parse_space]
  \\ rewrite_tac [parse_sexp_to_pretty_string] \\ simp []
  \\ simp [Once char_list_to_defs_def,parse_space]
  \\ simp [GSYM char_list_to_defs_def]
QED

Theorem thm_to_string_injective:
  thm_to_string ctxt1 th1 = thm_to_string ctxt2 th2 ⇒
  ctxt1 = ctxt2 ∧ th1 = th2
Proof
  metis_tac [string_to_thm_thm_to_string,PAIR_EQ]
QED

local

val bool_ty = “Tyapp (strlit "bool") []”
val fun_ty = “Tyapp (strlit "fun") [^bool_ty; ^bool_ty]”
val p = “Var (strlit "p") ^bool_ty”
val id = “Abs ^p ^p”
val eq = “Const (strlit "=") ^fun_ty”
val t = “Var (strlit "T") ^bool_ty”

Overload Eq = “λl r. Comb (Comb ^eq l) r”

val up =
  “ConstSpec [(strlit "T", Eq ^id ^id)]
     (Eq ^t (Eq ^id ^id))”

in

val _ =
  EVAL “thm_to_string [^up]
     (Sequent [] (Const (strlit "T") ^bool_ty))”
  |> concl |> rand |> rand |> stringSyntax.fromHOLstring |> print;

end
