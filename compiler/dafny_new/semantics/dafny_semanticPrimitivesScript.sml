(*
  Defines semantic primitives used in Dafny's semantics.
*)

open preamble
open dafny_astTheory
open mlstringTheory
open mlintTheory  (* int_to_string *)
open alistTheory

val _ = new_theory "dafny_semanticPrimitives";

Datatype:
  sem_env =
  <|
    (* Determines whether evaluate is actually running; relevant for Forall *)
    is_running : bool;
    (* Store functions and methods *)
    prog : program
  |>;
End

Datatype:
  value =
  | IntV int
  | BoolV bool
  | StrV mlstring
  (* ArrV length location *)
  | ArrV num num
End

Datatype:
  heap_value =
  | HArr (value list)
End

Datatype:
  state =
  <| clock: num;
     locals: (mlstring, (value option)) alist;
     heap: heap_value list;
     output: mlstring list |>
End

Datatype:
  error_result =
  | Rtype_error
  | Rtimeout_error
End

Datatype:
  exp_result =
  | Rval 'a
  | Rerr error_result
End

(* NOTE We use a separate type, so that we can easily add more cases in
   the future (e.g., break, continue, ...) *)
Datatype:
  stop =
  | Sret
  | Serr error_result
End

Datatype:
  stmt_result =
  | Rcont  (* for example, Skip *)
  | Rstop stop
End

Definition mk_env_def:
  mk_env is_running program =
    <| is_running := is_running; prog := program |>
End

Definition get_member_aux_def:
  get_member_aux name [] = NONE ∧
  get_member_aux name (member::members) =
  (case member of
   | Function name' _ _ _ _ _ _ =>
       if name' = name
       then SOME member
       else get_member_aux name members
   | Method name' _ _ _ _ _ _ _ _ =>
       if name' = name
       then SOME member
       else get_member_aux name members)
End

Definition get_member_def:
  get_member name (Program members) =
    get_member_aux name members
End

Definition init_state_def:
  init_state = <| clock := 424242; locals := []; heap := []; output := [] |>
End

Definition safe_zip_def:
  safe_zip xs ys =
    if LENGTH xs ≠ LENGTH ys then NONE else SOME (ZIP (xs, ys))
End

(* Given input parameters i₁, i₂, and output variables o₁, o₂, we enforce that
   all of their names are different, and prepare locals to be [o₂, o₁, i₂, i₁],
   which intuitively corresponds to pushing the parameters and variables from
   left to right. *)
Definition set_up_call_def:
  set_up_call st in_ns in_vs outs =
  if ¬ALL_DISTINCT (in_ns ++ outs) then NONE else
  (case (safe_zip in_ns (MAP SOME in_vs)) of
   | NONE => NONE
   | SOME params =>
     (let old_locals = st.locals in
      let new_locals = params ++ ZIP (outs, REPLICATE (LENGTH outs) NONE) in
        SOME (old_locals, st with locals := REVERSE new_locals)))
End

Theorem set_up_call_clock:
  ∀ st₀ ins ivs os locals st₁.
    set_up_call st₀ ins ivs os = SOME (locals, st₁) ⇒ st₁.clock = st₀.clock
Proof
  rpt strip_tac \\ gvs [set_up_call_def, CaseEq "option"]
QED

Definition restore_locals_def:
  restore_locals st old_locals = (st with locals := old_locals)
End

Theorem restore_locals_clock:
  ∀ st₀ old_locals st₁.
    restore_locals st₀ old_locals = st₁ ⇒ st₁.clock = st₀.clock
Proof
  rpt strip_tac \\ gvs [restore_locals_def]
QED

Definition read_local_def:
  read_local locals var =
  (case ALOOKUP locals var of
   | NONE => NONE
   | SOME ov => ov)
End

(* Short-circuiting *)
Datatype:
  sc_res = Done value | Continue | Abort
End

Definition do_sc_def:
  do_sc And v =
    (if (v = BoolV F) then (Done v)
     else if (v = BoolV T) then Continue
     else Abort) ∧
  do_sc Or v =
    (if (v = BoolV T) then (Done v)
     else if (v = BoolV F) then Continue
     else Abort) ∧
  do_sc Imp v =
    (if (v = BoolV F) then (Done (BoolV T))
     else if (v = BoolV T) then Continue
     else Abort) ∧
  do_sc _ _ = Continue
End

Definition do_uop_def:
  do_uop Not v = case v of BoolV b => SOME (BoolV ¬b) | _ => NONE
End

Definition value_same_type_def[simp]:
  (value_same_type (IntV _) (IntV _) ⇔ T) ∧
  (value_same_type (BoolV _) (BoolV _) ⇔ T) ∧
  (value_same_type (StrV _) (StrV _) ⇔ T) ∧
  (value_same_type (ArrV _ _) (ArrV _ _) ⇔ T) ∧
  (value_same_type _ _ ⇔ F)
End

Definition do_bop_def:
  do_bop Eq v₀ v₁ =
    (if value_same_type v₀ v₁ then SOME (BoolV (v₀ = v₁)) else NONE) ∧
  do_bop Neq v₀ v₁ =
    (if value_same_type v₀ v₁ then SOME (BoolV (v₀ ≠ v₁)) else NONE) ∧
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
   | (IntV i₀, IntV i₁) =>
       if i₁ = 0 then NONE else SOME (IntV (ediv i₀ i₁))
   | _ => NONE)
End

Definition lit_to_val_def[simp]:
  lit_to_val (IntL i) = (IntV i) ∧
  lit_to_val (BoolL b) = (BoolV b) ∧
  lit_to_val (StrL s) = (StrV s)
End

Definition get_array_len_def:
  get_array_len (ArrV len _) = SOME len ∧
  get_array_len _ = NONE
End

Definition val_to_num:
  val_to_num (IntV i) = (if i ≥ 0i then SOME (Num i) else NONE) ∧
  val_to_num _ = NONE
End

Definition index_array_def:
  index_array st arr idx =
  (case (arr, val_to_num idx) of
   | (ArrV len loc, SOME idx) =>
     (case LLOOKUP st.heap loc of
      | NONE => NONE
      | SOME (HArr arr) => LLOOKUP arr idx)
   | _ => NONE)
End

(* Can be used for both conditionals ITE and If *)
Definition do_cond_def:
  do_cond (BoolV b) thn els = SOME (if b then thn else els) ∧
  do_cond _ _ _ = NONE
End

Definition alloc_array_def:
  alloc_array st len init =
  (case val_to_num len of
   | NONE => NONE
   | SOME len =>
     let arr = (HArr (REPLICATE len init)) in
       SOME (st with heap := SNOC arr st.heap, ArrV len (LENGTH st.heap)))
End

Definition update_local_aux_def:
  update_local_aux [] var val = NONE ∧
  update_local_aux ((x, w)::xs) var val =
  (if x ≠ var then
     (case update_local_aux xs var val of
      | NONE => NONE
      | SOME xs => SOME ((x, w)::xs))
   else SOME ((x, SOME val)::xs))
End

Definition update_local_def:
  update_local st var val =
  (case update_local_aux st.locals var val of
   | NONE => NONE
   | SOME new_locals => SOME (st with locals := new_locals))
End

Definition update_array_def:
  update_array st arr idx val =
  (case (arr, val_to_num idx) of
   | (ArrV len loc, SOME idx) =>
     (case LLOOKUP st.heap loc of
      | NONE => NONE
      | SOME (HArr arr) =>
          if idx ≥ LENGTH arr then NONE else
          let new_arr = LUPDATE val idx arr;
              new_heap = LUPDATE (HArr new_arr) loc st.heap
          in
            SOME (st with heap := new_heap))
   | _ => NONE)
End

Definition push_local_def:
  push_local st var val =
  (st with locals := (var, SOME val)::st.locals)
End

Definition all_values_def:
  all_values IntT = {IntV i | i ∈ 𝕌(:int)} ∧
  all_values BoolT = {BoolV T; BoolV F} ∧
  all_values StrT = {StrV s | s ∈ 𝕌(:mlstring)} ∧
  all_values _ = ∅
End

Definition declare_local_def:
  declare_local st n =
    st with locals := (n, NONE)::st.locals
End

Theorem declare_local_clock:
  (declare_local st names).clock = st.clock
Proof
  gvs [declare_local_def]
QED

Definition pop_local_def:
  pop_local st =
  (case st.locals of
   | [] => NONE
   | l::rest => SOME (st with locals := rest))
End

Theorem pop_local_clock:
  ∀st st'. pop_local st = SOME st' ⇒ st'.clock = st.clock
Proof
  rpt strip_tac \\ gvs [pop_local_def, AllCaseEqs ()]
QED

Definition val_to_string_def:
  val_to_string st (IntV i) =
    SOME (int_to_string #"-" i) ∧
  val_to_string st (BoolV b) =
    SOME (if b then (strlit "True") else (strlit "False")) ∧
  val_to_string st (StrV s) = SOME s ∧
  val_to_string st _ = NONE
End

Definition print_string_def:
  print_string st vs =
  (case OPT_MMAP (val_to_string st) vs of
   | NONE => NONE
   | SOME ss => SOME (st with output := SNOC (concat ss) st.output))
End

val _ = export_theory ();
