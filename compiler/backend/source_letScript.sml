(*
  This is a source-to-source transformation that lifts Let/Letrec expressions
  out of Dlet/Dletrecs when they are independent of function arguments.

  The optimization works in two steps. First, all Fun binders are pushed under
  Let/Letrec bodies as far as possible. After this, a second pass picks out
  all Let/Letrec expressions that (hopefully) sit at the top of the Dlet/
  Dletrec.

  The hope is that code such as this:

    fun f x =
      let fun f1 y = ... (* no free x here *)
          fun f2 y = ...  (* no free x here *)
          val v = ...    (* no free x here *)
      in f1 x end;

  Can be turned into:

    fun f1 x = ...
    fun f2 y = ...
    val v = ...
    fun f x = f1 x;
 *)

open preamble evaluateTheory astTheory mlmapTheory;

val _ = new_theory "source_let";

val _ = set_grammar_ancestry ["ast", "mlmap", "evaluate", "misc"];

Overload string_size = “list_size char_size”;

Overload empty = “mlmap$empty string_cmp : (string,unit) mlmap$map”;
Overload union = “mlmap$union”;
Overload delete = “mlmap$delete”;
Overload diff_keys = “FOLDL mlmap$delete”;
Overload singleton = “λk. mlmap$insert empty k ()”;
Overload member = “λk m: ('a, unit) map. IS_SOME (mlmap$lookup m k)”;

Definition frees_def:
  frees [] = empty ∧
  frees (x::y::xs) = union (frees [x]) (frees (y::xs)) ∧
  frees [Raise x] = frees [x] ∧
  frees [Handle x pes] = union (frees [x]) (frees_pats pes) ∧
  frees [Lit lit] = empty ∧
  frees [Con cn xs] = frees xs ∧
  frees [Var id] =
    (case id of
       Long mn id' => empty
     | Short nm => singleton nm) ∧
  frees [Fun nm x] = delete (frees [x]) nm ∧
  frees [App op xs] = frees xs ∧
  frees [Log lop x y] = union (frees [x]) (frees [y]) ∧
  frees [If x y z] = union (frees [x]) (union (frees [y]) (frees [z])) ∧
  frees [Mat x pes] = union (frees [x]) (frees_pats pes) ∧
  frees [Let opt x y] =
    (case opt of
      NONE => union (frees [x]) (frees [y])
    | SOME nm => union (frees [x]) (delete (frees [y]) nm)) ∧
  frees [Letrec funs x] =
    union (frees_funs funs) (diff_keys (frees [x]) (MAP FST funs)) ∧
  frees [Tannot x t] = frees [x] ∧
  frees [Lannot x l] = frees [x] ∧
  frees_pats [] = empty ∧
  frees_pats ((p,x)::xs) = union (diff_keys (frees [x]) (pat_bindings p []))
                                 (frees_pats xs) ∧
  frees_funs [] = empty ∧
  frees_funs ((f,n,x)::xs) = union (delete (frees [x]) n) (frees_funs xs)
Termination
  wf_rel_tac
    ‘measure $ sum_size (list_size exp_size) $
               sum_size (list_size $ pair_size pat_size exp_size)
                        (list_size $ pair_size string_size $
                                     pair_size string_size exp_size)’
End

Definition free_in_def:
  free_in v [] = F ∧
  free_in v (x::y::xs) = (free_in v [x] ∨ free_in v (y::xs)) ∧
  free_in v [Raise x] = free_in v [x] ∧
  free_in v [Handle x pes] = (free_in v [x] ∨ free_in_pats v pes) ∧
  free_in v [Lit lit] = F ∧
  free_in v [Con cn xs] = free_in v xs ∧
  free_in v [Var id] =
    (case id of
       Long mn id' => F
     | Short nm => nm = v) ∧
  free_in v [Fun nm x] = (if v = nm then F else free_in v [x]) ∧
  free_in v [App op xs] = free_in v xs ∧
  free_in v [Log lop x y] = (free_in v [x] ∨ free_in v [y]) ∧
  free_in v [If x y z] = (free_in v [x] ∨ free_in v [y] ∨ free_in v [z]) ∧
  free_in v [Mat x pes] = (free_in v [x] ∨ free_in_pats v pes) ∧
  free_in v [Let opt x y] =
    (case opt of
      NONE => free_in v [x] ∨ free_in v [y]
    | SOME nm => free_in v [x] ∨ if nm = v then F else free_in v [y]) ∧
  free_in v [Letrec funs x] =
    (¬MEM v (MAP FST funs) ∧ (free_in_funs v funs ∨ free_in v [x])) ∧
  free_in v [Tannot x t] = free_in v [x] ∧
  free_in v [Lannot x l] = free_in v [x] ∧
  free_in_pats v [] = F ∧
  free_in_pats v ((p,x)::xs) =
    (if MEM v (pat_bindings p [])
     then free_in_pats v xs
     else free_in v [x] ∨ free_in_pats v xs) ∧
  free_in_funs v [] = F ∧
  free_in_funs v ((f,n,x)::xs) =
    (if v = n then free_in_funs v xs
     else free_in v [x] ∨ free_in_funs v xs)
Termination
  wf_rel_tac
    ‘measure
     $ sum_size (pair_size string_size (list_size exp_size))
     $ sum_size (pair_size string_size
                           (list_size $ pair_size pat_size exp_size))
         (pair_size string_size
           (list_size (pair_size string_size (pair_size string_size exp_size))))’
End

Definition variant_def:
  variant frees x =
    if MEM x frees then
      variant frees (#"_"::x)
    else x
Termination
  wf_rel_tac
    ‘measure $ λ(fs,x).
       SUM (MAP (SUC o LENGTH) (FILTER (λx. MEM x fs) fs)) - LENGTH x’
  \\ rw [] \\ rename [‘MEM x xs’]
  \\ ‘FILTER (λx. MEM x xs) xs = xs’
    by simp [FILTER_EQ_ID, EVERY_MEM]
  \\ simp []
  \\ pop_assum kall_tac
  \\ Induct_on ‘xs’ \\ rw []
  \\ res_tac \\ decide_tac
End

Overload variant =
  “λm: (string, unit) map. variant (MAP FST (mlmap$toAscList m))”;

Definition dest_Let_def[simp]:
  dest_Let (Let opt x y) = SOME (opt,x,y) ∧
  dest_Let _ = NONE
End

Theorem dest_Let_SOME:
  dest_Let z = SOME (opt,x,y) ⇔ z = Let opt x y
Proof
  Cases_on ‘z’ \\ gs []
QED

Theorem dest_Let_NONE:
  dest_Let z = NONE ⇔ ∀opt x y. z ≠ Let opt x y
Proof
  Cases_on ‘z’ \\ gs []
QED

Definition dest_Letrec_def[simp]:
  dest_Letrec (Letrec funs x) = SOME (funs, x) ∧
  dest_Letrec _ = NONE
End

Theorem dest_Letrec_SOME:
  dest_Letrec z = SOME (funs,x) ⇔ z = Letrec funs x
Proof
  Cases_on ‘z’ \\ gs []
QED

Theorem dest_Letrec_NONE:
  dest_Letrec z = NONE ⇔ ∀funs x. z ≠ Letrec funs x
Proof
  Cases_on ‘z’ \\ gs []
QED

(* exp_size without the annoying stuff *)
Definition exp_size_alt_def:
  exp_size_alt (Raise x) =
    (1 + exp_size_alt x) ∧
  exp_size_alt (Handle x pes) =
    (1 + exp_size_alt x + pats_size_alt pes) ∧
  exp_size_alt (Lit l) = 1 ∧
  exp_size_alt (Con opt xs) =
    (1 + list_size exp_size_alt xs) ∧
  exp_size_alt (Var n) = 1 ∧
  exp_size_alt (Fun n x) =
    (1 + exp_size_alt x) ∧
  exp_size_alt (App op xs) =
    (1 + list_size exp_size_alt xs) ∧
  exp_size_alt (Log lop x y) =
    (1 + exp_size_alt x + exp_size_alt y) ∧
  exp_size_alt (If x y z) =
    (1 + exp_size_alt x + exp_size_alt y + exp_size_alt z) ∧
  exp_size_alt (Mat x pes) =
    (1 + exp_size_alt x + pats_size_alt pes) ∧
  exp_size_alt (Let opt x y) =
    (1 + exp_size_alt x + exp_size_alt y) ∧
  exp_size_alt (Letrec funs x) =
    (1 + exp_size_alt x + funs_size_alt funs) ∧
  exp_size_alt (Tannot x t) = (1 + exp_size_alt x) ∧
  exp_size_alt (Lannot x l) = (1 + exp_size_alt x) ∧
  pats_size_alt [] = 0 ∧
  pats_size_alt ((p,x)::ps) =
    (1 + pat_size p + exp_size_alt x + pats_size_alt ps) ∧
  funs_size_alt [] = 0 ∧
  funs_size_alt ((f,n,x)::fs) = (1 + exp_size_alt x + funs_size_alt fs)
Termination
  wf_rel_tac
    ‘measure $ sum_size exp_size
             $ sum_size (list_size (pair_size pat_size exp_size))
             $ list_size (pair_size string_size $
                                    pair_size string_size exp_size)’
End

(* Bottom-up and then top-down moves all Fun:s past several Let/Letrec:s,
 * but the definition package does not like it.
 *)

Definition push_fun_def:
  (push_fun (Fun n z) =
    let z = push_fun z in
    case dest_Let z of
    | SOME (NONE,x,y) =>
        if ¬free_in n [x] then
          Let NONE x (push_fun (Fun n y))
        else
          Fun n z
    | SOME (SOME m,x,y) =>
        if ¬free_in n [x] then
          if n ≠ m then
            Let (SOME m) x (push_fun (Fun n y))
          else
            let n = variant (frees [y]) n in
            Let (SOME m) x (push_fun (Fun n y))
        else
          Fun n z
    | NONE =>
        case dest_Letrec z of
        | NONE => Fun n z
        | SOME (funs,x) =>
            if EVERY (λ(f,v,x). ¬free_in n [x]) funs ∧
               EVERY (λ(f,v,x). n ≠ f) funs then
                Letrec funs (push_fun (Fun n x))
            else
              Fun n z) ∧
  (push_fun (Let opt x y) = Let opt x (push_fun y)) ∧
  (push_fun (Letrec funs x) = Letrec funs (push_fun x)) ∧
  (push_fun x = x)
Termination
  cheat
End

(*
val test1 = EVAL “
  push_fun $
  Let (SOME "f") (Fun "_" (Var (Short "_"))) $
    Let (SOME "g") (Fun "_" (Var (Short "_"))) $
      Fun "baz" $
        Fun "bar" $
          Let (SOME "h") (Fun "_" (Var (Short "_")))
            (Var (Short "f"))”;
 *)
(*
val test2 = EVAL “
  push_fun $
  Let (SOME "f") (Fun "_" (Var (Short "_"))) $
    Let (SOME "g") (Fun "_" (Var (Short "_"))) $
      Fun "baz" $
        Fun "bar" $
          Let (SOME "h") (Fun "_" (Var (Short "_"))) $
            Let (SOME "baz") (Var (Short "_"))
            (Var (Short "baz"))”;
 *)

(* This function lifts Let/Letrec:s out of Dlet/Dletrec:s when they're at the
 * top and no function arguments (in the case of Dletrec) can interfer.
 *)

Definition lift_let_def:
  (lift_let (Dlet l p x) =
    case dest_Let x of
    | SOME (NONE,x,y) => SOME (Dlet l Pany x, Dlet l p y)
    | SOME (SOME m,x,y) => SOME (Dlet l (Pvar m) x, Dlet l p y)
    | NONE =>
        case dest_Letrec x of
        | SOME (funs,x) => SOME (Dletrec l funs, Dlet l p x)
        | NONE => NONE) ∧
  (lift_let (Dletrec l funs) = NONE (* TODO a slight repetition of push_fun *)) ∧
  (lift_let _ = NONE)
End

(* Apply the first step (push_fun) to a single declaration (in preparation for
 * calling lift_let).
 *)

Definition compile_dec_def:
  (compile_dec (Dlet l p x) = Dlet l p (push_fun x)) ∧
  (compile_dec (Dletrec l funs) =
    Dletrec l (MAP (λ(f,v,x). (f,v,push_fun x)) funs)) ∧
  (compile_dec d = d)
End

(* Apply the optimization on a series of declarations.
 * It's not strictly necessary to put the Dlocal around the single declaration
 * that has been lifted, but I'd like to imagine it will help me somewhere else.
 *)

Definition compile_decs_def:
  (compile_decs [] = []) ∧
  (compile_decs (d::ds) =
    let d = compile_dec d in
    case lift_let d of
    | NONE => d::compile_decs ds
    | SOME (d1,d2) => compile_decs (d1::d2::ds))
Termination
  cheat
End

(*
val test3 = EVAL “
  compile_decs [
    Dlet l (Pvar "foo")
      (Letrec [("bar", "x", App Opapp [Var (Short "baz"); Con NONE []])]
              (Var (Short "glob")))]”;
 *)

val _ = export_theory ();

