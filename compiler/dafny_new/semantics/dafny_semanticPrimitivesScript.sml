(*
  Defines semantic primitives used in Dafny's semantics.
*)

open preamble

val _ = new_theory "dafny_semanticPrimitives";

Datatype:
  sem_env =
  <|
    (* methods : method_name |-> (param_names, body) *)
    methods : (string |-> (string list # statement));
    (* functions : function_name |-> (param_names, body) *)
    functions : (string |-> (string list # expression))
  |>;
End

Datatype:
  value =
  | IntV int
  | BoolV bool
  | StrV string
End

Datatype:
  heap_value =
  | HArray (value list)
End

Datatype:
  state =
  <| clock: num;
     locals: (string |-> value) list;
     heap: heap_value list;
     cout: string list |>
End

Datatype:
  error_result =
  | Rtype_error
  | Rtimeout_error
End

Datatype:
  result =
  | Rval 'a
  | Rret (value list)
  | Rerr error_result
End

Definition strict_zip_def:
  strict_zip (x::xs) (y::ys) =
  OPTION_MAP (CONS (x,y)) (strict_zip xs ys)
End

Definition push_param_frame_def:
  push_param_frame st param_names vals =
  (case (strict_zip param_names vals) of
   | NONE => NONE
   | SOME params =>
     SOME (st with locals := (alist_to_fmap params)::st.locals))
End

Definition lit_to_val_def[simp]:
  lit_to_val (IntLit i) = (IntV i) ∧
  lit_to_val (BoolLit b) = (BoolV b) ∧
  lit_to_val (StringLit s) = (StrV s)
End

(* Returns the value in case it is already known due to short-circuiting. *)
Definition try_sc_def:
  try_sc And v = (if (v = BoolV F) then (SOME v) else NONE) ∧
  try_sc Or v = (if (v = BoolV T) then (SOME v) else NONE) ∧
  try_sc Imp v = (if (v = BoolV F) then (SOME (BoolV T)) else NONE) ∧
  try_sc _ _ = NONE
End

Definition do_bop_def:
  do_bop Eq v₀ v₁ = SOME (BoolV (v₀ = v₁)) ∧
  do_bop Neq v₀ v₁ = SOME (BoolV (v₀ ≠ v₁)) ∧
  do_bop And v₀ v₁ =
  (case (v₀, v₁) of
   | (BoolV b₀, BoolV b₁) => SOME (BoolV (b₀ ∧ b₁))
   | _ => NONE) ∧
  do_bop Imp v₀ v₁ =
  (case (v₀, v₁) of
   | (BoolV b₀, BoolV b₁) => SOME (BoolV (b₀ ⇒ b₁))
   | _ => NONE) ∧
  do_bop Or v₀ v₁ =
  (case (v₀, v₁) of
   | (BoolV b₀, BoolV b₁) => SOME (BoolV (b₀ ∨ b₁))
   | _ => NONE) ∧
  do_bop Lt v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (BoolV (i₀ < i₁))
   | _ => NONE) ∧
  do_bop Le v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (BoolV (i₀ ≤ i₁))
   | _ => NONE) ∧
  do_bop Ge v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (BoolV (i₀ ≥ i₁))
   | _ => NONE) ∧
  do_bop Sub v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (IntV (i₀ - i₁))
   | _ => NONE) ∧
  do_bop Add v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (IntV (i₀ + i₁))
   | _ => NONE) ∧
  do_bop Mul v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (IntV (i₀ * i₁))
   | _ => NONE) ∧
  do_bop Div v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) => SOME (IntV (ediv i₀ i₁))
   | _ => NONE)
End

val _ = export_theory ();
