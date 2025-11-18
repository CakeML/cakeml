(*
  Defines functions for turning a ctxt & thm to a string and back
*)
Theory print_thm
Ancestors
  holKernel mlstring lisp_values lisp_parsing lisp_printing
  lisp_parsing_proofs
Libs
  preamble

(* encoding into v *)

Definition nil_list_def[simp]:
  nil_list [] = Name "nil" ∧
  nil_list (x::xs) = Pair x (nil_list xs)
End

Definition str_to_v_def:
  str_to_v (s:mlstring) =
    let xs = explode s in
    let n = name xs in
      if ~NULL xs ∧ name2str n = xs then
        Num n
      else
        list [Num (name "'"); list (MAP (λc. Num (ORD c)) xs)]
End

Definition ty_to_v_def:
  ty_to_v (Tyvar s) = list [Name "Tyvar"; str_to_v s] ∧
  ty_to_v (Tyapp s tys) =
    list (Name "Tyapp" :: str_to_v s :: (MAP ty_to_v tys))
Termination
  WF_REL_TAC ‘measure type_size’
End

Definition term_to_v_def:
  term_to_v (Var s ty) = list [Name "Var"; str_to_v s; ty_to_v ty] ∧
  term_to_v (Const s ty) = list [Name "Const"; str_to_v s; ty_to_v ty] ∧
  term_to_v (Comb f x) = list [Name "Comb"; term_to_v f; term_to_v x] ∧
  term_to_v (Abs f x) = list [Name "Abs"; term_to_v f; term_to_v x]
End

Definition thm_to_v_def:
  thm_to_v (Sequent ts t) =
    list [Name "Sequent"; nil_list (MAP term_to_v ts); term_to_v t]
End

Definition update_to_v_def:
  update_to_v (ConstSpec xs t) =
    list [Name "ConstSpec";
          list (MAP (λ(s,t). list [str_to_v s; term_to_v t]) xs);
          term_to_v t] ∧
  update_to_v (TypeDefn s1 t s2 s3) =
    list [Name "TypeDefn";
          str_to_v s1; term_to_v t; str_to_v s2; str_to_v s3] ∧
  update_to_v (NewType s n) =
    list [Name "NewType"; str_to_v s; Num n] ∧
  update_to_v (NewConst s ty) =
    list [Name "NewConst"; str_to_v s; ty_to_v ty] ∧
  update_to_v (NewAxiom t) =
    list [Name "NewAxiom"; term_to_v t]
End

(* decoding from v *)

Definition v2list_def[simp]:
  v2list (Num n) = [] ∧
  v2list (Pair x y) = x :: v2list y
End

Definition v_to_str_def:
  v_to_str (Num n) = implode (name2str n) ∧
  v_to_str x = implode (MAP (λv. CHR (getNum v)) (v2list (el1 x)))
End

Theorem v2list_lisp_v_size[local]:
  ∀x a. MEM a (v2list x) ⇒ lisp_v_size a < lisp_v_size x
Proof
  Induct \\ simp [Once v2list_def] \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

Definition v_to_ty_def:
  v_to_ty v =
    let n = getNum (head v) in
      if n = name "Tyapp" then
        Tyapp (v_to_str (el1 v)) (MAP v_to_ty (v2list (tail (tail v))))
      else Tyvar (v_to_str (el1 v))
Termination
  WF_REL_TAC ‘measure lisp_v_size’
  \\ rw [isNum_def,head_def,tail_def,lisp_v_size_def]
  \\ imp_res_tac v2list_lisp_v_size
  \\ Cases_on ‘v’ \\ fs []
  \\ Cases_on ‘l0’ \\ fs []
End

Definition v_to_term_def:
  v_to_term v =
    let n = getNum (head v) in
      if n = name "Comb" ∧ ~isNum v then
        Comb (v_to_term (el1 v)) (v_to_term (el2 v))
      else if n = name "Abs" ∧ ~isNum v then
        Abs (v_to_term (el1 v)) (v_to_term (el2 v))
      else if n = name "Var" ∧ ~isNum v then
        Var (v_to_str (el1 v)) (v_to_ty (el2 v))
      else
        Const (v_to_str (el1 v)) (v_to_ty (el2 v))
Termination
  WF_REL_TAC ‘measure lisp_v_size’
  \\ rw [isNum_def,head_def,tail_def,lisp_v_size_def]
  \\ Cases_on ‘v’ \\ fs []
  \\ Cases_on ‘l0’ \\ fs []
  \\ Cases_on ‘l0'’ \\ fs []
End

Definition v_to_thm_def:
  v_to_thm v =
    Sequent (MAP v_to_term (v2list (el1 v))) (v_to_term (el2 v))
End

Definition v_to_update_def:
  v_to_update v =
    let n = getNum (head v) in
      if n = name "ConstSpec" then
        ConstSpec (MAP ((λxs. (v_to_str (HD xs), v_to_term (EL 1 xs))) o v2list)
                     (v2list (el1 v))) (v_to_term (el2 v))
      else if n = name "TypeDefn" then
        TypeDefn (v_to_str (el1 v)) (v_to_term (el2 v))
                 (v_to_str (el3 v)) (v_to_str (el3 (tail v)))
      else if n = name "NewType" then
        NewType (v_to_str (el1 v)) (getNum (el2 v))
      else if n = name "NewConst" then
        NewConst (v_to_str (el1 v)) (v_to_ty (el2 v))
      else
        NewAxiom (v_to_term (el1 v))
End

Theorem v2list_nil_thm[simp]:
  ∀xs. v2list (nil_list xs) = xs
Proof
  Induct \\ simp [Once v2list_def]
QED

Theorem v2list_thm[simp]:
  ∀xs. v2list (list xs) = xs
Proof
  Induct \\ simp [Once v2list_def]
QED

Theorem str_to_v_thm[simp]:
  ∀s. v_to_str (str_to_v s) = s
Proof
  Cases \\ fs [str_to_v_def]
  \\ rw [v_to_str_def,mlstringTheory.implode_def]
  \\ fs [MAP_MAP_o,miscTheory.MAP_EQ_ID,CHR_ORD]
QED

Theorem ty_to_v_thm[simp]:
  ∀ty. v_to_ty (ty_to_v ty) = ty
Proof
  ho_match_mp_tac ty_to_v_ind \\ rw []
  \\ simp [ty_to_v_def,Once v_to_ty_def]
  \\ fs [name_def,MAP_MAP_o,miscTheory.MAP_EQ_ID]
QED

Theorem term_to_v_thm[simp]:
  ∀t. v_to_term (term_to_v t) = t
Proof
  Induct
  \\ simp [term_to_v_def,Once v_to_term_def]
  \\ fs [name_def,MAP_MAP_o,miscTheory.MAP_EQ_ID]
QED

Theorem thm_to_v_thm[simp]:
  ∀th. v_to_thm (thm_to_v th) = th
Proof
  Cases
  \\ simp [thm_to_v_def,Once v_to_thm_def]
  \\ fs [name_def,MAP_MAP_o,miscTheory.MAP_EQ_ID]
QED

Theorem update_to_v_update[simp]:
  ∀u. v_to_update (update_to_v u) = u
Proof
  Cases
  \\ simp [update_to_v_def,Once v_to_update_def]
  \\ fs [name_def,MAP_MAP_o,miscTheory.MAP_EQ_ID,FORALL_PROD]
  \\ rpt (simp [Once v2list_def])
QED

(* main definition *)

Definition thm_to_string_def:
  thm_to_string (ctxt:update list) (th:thm) =
    let vs = thm_to_v th :: MAP update_to_v ctxt in
      implode (vs2str vs
                 ["# The following is a theorem of higher-order logic\n";
                  "\n# which is proved in the following context\n"])
End

(* it has an inverse: *)

Definition string_to_thm_def:
  string_to_thm s =
    let vs = v2list (parse (lexer (explode s)) (Num 0) []) in
      (MAP v_to_update (TL vs), v_to_thm (HD vs))
End

Theorem string_to_thm_thm_to_string:
  string_to_thm (thm_to_string ctxt th) = (ctxt,th)
Proof
  fs [parse_lexer_vs2str,thm_to_string_def,string_to_thm_def]
  \\ once_rewrite_tac [v2list_def] \\ fs []
  \\ fs [MAP_MAP_o,miscTheory.MAP_EQ_ID,FORALL_PROD]
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

