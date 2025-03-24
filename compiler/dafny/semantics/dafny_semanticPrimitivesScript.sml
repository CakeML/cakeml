(*
 Definition of semantic primitives used in the semantics.
*)

open preamble
open alistTheory
open dafny_astTheory
open finite_mapTheory

val _ = new_theory "dafny_semanticPrimitives"

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
  sem_env =
  <|
    (* For now, we are assuming (module, method) is enough as a key *)
    methods: ((name # name), method) alist;
    (* locals are stored as refs *)
    locals: (string |-> num) list
  |>
End

Datatype:
  state =
  <| clock: num;
     (* As in the CakeML semantics, the nth item in the list is the value at
        location n *)
     refs: value list;
     cout: string |>
End

Definition add_local_def:
  add_local (env: sem_env) (st: state) (varNam: string) (v: value) (t: type)
    : (sem_env # state) option =
  case (env.locals, st.locals) of
  | ((env_cur::env_rest), (st_cur::st_rest)) =>
      SOME (env with locals := (env_cur |+ (varNam, t)::env_rest),
            st with locals := (st_cur |+ (varNam, v))::st_rest)
  | _ => NONE
End

Theorem add_local_clock:
  ∀env₁ s₁ varNam v t env₂ s₂.
    add_local env₁ s₁ varNam v t = SOME (env₂, s₂) ⇒ s₂.clock = s₁.clock
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
  | Rerr error_result
End

val _ = export_theory();
