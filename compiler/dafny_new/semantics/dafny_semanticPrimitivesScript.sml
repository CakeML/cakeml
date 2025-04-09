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
  (* ArrayV length location *)
  | ArrayV num num
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
  | Rerr error_result
End

Definition strict_zip_def:
  strict_zip (x::xs) (y::ys) =
  OPTION_MAP (CONS (x,y)) (strict_zip xs ys)
End

Definition set_up_call_def:
  set_up_call st names vals =
  (case (strict_zip names vals) of
   | NONE => NONE
   | SOME params =>
     (let old_locals = st.locals in
        SOME (old_locals, st with locals := [alist_to_fmap params])))
End

Theorem set_up_call_clock:
  ∀ s₁ ns vs locals s₂.
    set_up_call s₁ ns vs = SOME (locals, s₂) ⇒ s₂.clock = s₁.clock
Proof
  rpt strip_tac >> gvs [set_up_call_def, CaseEq "option"]
QED

Definition restore_locals_def:
  restore_locals st old_locals = (st with locals := old_locals)
End

Theorem restore_locals_clock:
  ∀ s₁ old_locals.
    restore_locals s₁ old_locals = s₂ ⇒ s₂.clock = s₁.clock
Proof
  rpt strip_tac >> gvs [restore_locals_def]
QED

Definition read_local_aux_def:
  read_local_aux [] name = NONE ∧
  read_local_aux (cur::rest) name =
  (case FLOOKUP cur name of
   | NONE => read_local_aux rest name
   | SOME v => SOME v)
End

Definition read_local_def:
  read_local st name = read_local_aux st.locals name
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

Definition lit_to_val_def[simp]:
  lit_to_val (IntLit i) = (IntV i) ∧
  lit_to_val (BoolLit b) = (BoolV b) ∧
  lit_to_val (StringLit s) = (StrV s)
End

Definition get_array_len_def:
  get_array_len (ArrayV len _) = SOME len ∧
  get_array_len _ = NONE
End

Definition val_to_num:
  val_to_num (IntV i) = SOME (Num i) ∧
  val_to_num _ = NONE
End

Definition index_array_def:
  index_array st arr idx =
  (case (arr, val_to_num idx) of
   | (ArrayV len loc, SOME idx) =>
     (case LLOOKUP st.heap loc of
      | NONE => NONE
      | SOME (HArray arr) => LLOOKUP arr idx)
   | _ => NONE)
End

(* Can be used for both conditionals ITE and If *)
Definition do_cond_def:
  do_cond (BoolV b) thn els = SOME (if b then thn else els) ∧
  do_cond _ _ _ = NONE
End

val _ = export_theory ();
