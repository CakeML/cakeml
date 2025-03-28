(*
 Definition of semantic primitives used in the semantics.
*)

open preamble
open alistTheory
open dafny_astTheory
open finite_mapTheory

val _ = new_theory "dafny_semanticPrimitives"

Datatype:
  sem_env =
  (* For now, we are assuming (module, method) is enough as a key *)
  <| methods: ((name # name), method) alist |>
End

Datatype:
  value =
  | UnitV
  | BoolV bool
  | IntV int
  | CharV char
  | StrV string
  (* ArrayV dims location *)
  | ArrayV (num list) num
End

Definition init_val_def:
  init_val (Primitive Int) = SOME (IntV 0) ∧
  init_val (t: type): (value option) = NONE
End

Definition val_to_num:
  val_to_num (IntV i) = SOME (Num i) ∧
  val_to_num _ = NONE
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
     cout: string |>
End

Definition strict_zip_def:
  strict_zip (x::xs) (y::ys) =
  (case (strict_zip xs ys) of
   | SOME rest => SOME ((x, y)::rest)
   | NONE => NONE) ∧
  strict_zip [] (y::ys) = NONE ∧
  strict_zip (x::xs) [] = NONE ∧
  strict_zip [] [] = SOME []
End

Definition push_param_frame_def:
  push_param_frame st param_names vals =
  let param_names = MAP dest_varName param_names in
    (case (strict_zip param_names vals) of
     | NONE => NONE
     | SOME params =>
         SOME (st with locals := (alist_to_fmap params)::st.locals))
End

Theorem push_param_frame_clock:
  ∀ s₁ pns vs s₂.
    push_param_frame s₁ pns vs = SOME s₂ ⇒ s₂.clock = s₁.clock
Proof
  rpt strip_tac >> gvs [push_param_frame_def, CaseEq "option"]
QED

Definition add_local_def:
  add_local (st: state) (varNam: string) (v: value): state option =
  case st.locals of
  | [] => NONE
  | (cur::rest) => SOME (st with locals := (cur |+ (varNam, v))::rest)
End

Theorem add_local_clock:
  ∀s1 varNam v s2. add_local s1 varNam v = SOME s2 ⇒ s2.clock = s1.clock
Proof
  rw[] >> gvs[add_local_def, AllCaseEqs()]
QED

Definition assign_to_local_def:
  assign_to_local (st: state) (varNam: string) (v: value): (state option) =
  case st.locals of
  | [] => NONE
  | (cur::rest) =>
      if varNam ∉ FDOM cur
      then NONE
      else SOME (st with locals := (cur |+ (varNam, v))::rest)
End

Theorem assign_to_local_clock:
  ∀s1 varNam v s2. assign_to_local s1 varNam v = SOME s2 ⇒ s2.clock = s1.clock
Proof
  rw[] >> gvs[assign_to_local_def, AllCaseEqs()]
QED

Definition init_state_def:
  init_state = <| clock := 424242;
                  locals := [FEMPTY];
                  cout := "" |>
End

Datatype:
  error_result =
  | Rtype_error
  | Rtimeout_error
  | Runsupported
End

Datatype:
  result =
  | Rval 'a
  | Rerr error_result
End

val _ = export_theory();
