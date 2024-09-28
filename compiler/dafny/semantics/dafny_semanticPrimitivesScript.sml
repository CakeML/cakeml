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
End

Definition init_val_def:
  init_val (Primitive Int) = SOME (IntV 0) ∧
  init_val (t: type): (value option) = NONE
End

Datatype:
  state =
  <| clock: num;
     locals: (string |-> value) list;
     cout: string |>
End

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
  | Rval value
  | Rret value
  | Rerr error_result
End

val _ = export_theory();
