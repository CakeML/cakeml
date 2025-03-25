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
  <|
    (* For now, we are assuming (module, method) is enough as a key *)
    methods: ((name # name), method) alist;
    (* We use a list of maps from variable names to locations to model
       (potentially nested) scopes and mutable variables. *)
    locals: (string |-> num) list
  |>
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
     (* The nth item in the list is the value at location n *)
     heap: value list;
     cout: string |>
End

Definition add_local_def:
  add_local (env: sem_env) (st: state) (varNam: string) (v: value): (sem_env # state) option =
  case env.locals of
  | [] => NONE
  | (cur::rest) =>
      let next_location = LENGTH st.heap in
        SOME (env with locals := (cur |+ (varNam, next_location))::rest,
              st with heap := SNOC v st.heap)
End

Theorem add_local_clock:
  ∀env₁ s₁ varNam v env₂ s₂.
    add_local env₁ s₁ varNam v = SOME (env₂, s₂) ⇒ s₂.clock = s₁.clock
Proof
  rw[] >> gvs[add_local_def, AllCaseEqs()]
QED

Definition assign_to_local_def:
  assign_to_local (env: sem_env) (st: state) (varNam: string) (v: value): state option =
  case env.locals of
  | [] => NONE
  | (cur::rest) =>
      let loc = cur ' varNam;
          new_heap = LUPDATE v loc (st.heap) in
        SOME (st with heap := new_heap)
End

Theorem assign_to_local_clock:
  ∀ env s₁ varNam v s₂.
    assign_to_local env s₁ varNam v = SOME s₂ ⇒ s₂.clock = s₁.clock
Proof
  rw[] >> gvs[assign_to_local_def, AllCaseEqs()]
QED

Definition init_state_def:
  init_state = <| clock := 424242;
                  heap := [];
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
