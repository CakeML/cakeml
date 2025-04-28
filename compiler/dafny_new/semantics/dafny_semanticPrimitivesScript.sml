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
    (* methods : method_name |-> (param_names, out_names, body) *)
    methods : (mlstring |-> (mlstring list # mlstring list # statement));
    (* functions : function_name |-> (param_names, body) *)
    functions : (mlstring |-> (mlstring list # exp))
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
     cout: mlstring list |>
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

Definition safe_zip_def:
  safe_zip xs ys =
  if LENGTH xs ≠ LENGTH ys then NONE
  else SOME (ZIP (xs, ys))
End

Definition set_up_call_def:
  set_up_call st in_ns in_vs outs =
  (case (safe_zip in_ns (MAP SOME in_vs)) of
   | NONE => NONE
   | SOME params =>
     (let old_locals = st.locals in
      let new_locals = params ++ (MAP (λn. (n, NONE)) outs) in
        SOME (old_locals, st with locals := new_locals)))
End

Theorem set_up_call_clock:
  ∀ st₀ ins ivs os locals st₁.
    set_up_call st₀ ins ivs os = SOME (locals, st₁) ⇒ st₁.clock = st₀.clock
Proof
  rpt strip_tac >> gvs [set_up_call_def, CaseEq "option"]
QED

Definition restore_locals_def:
  restore_locals st old_locals = (st with locals := old_locals)
End

Theorem restore_locals_clock:
  ∀ st₀ old_locals st₁.
    restore_locals st₀ old_locals = st₁ ⇒ st₁.clock = st₀.clock
Proof
  rpt strip_tac >> gvs [restore_locals_def]
QED

Definition read_local_def:
  read_local locals var =
  (case ALOOKUP locals var of
   | NONE => NONE
   | SOME ov => ov)
End

(* Returns the value in case it is already known due to short-circuiting. *)
Definition try_sc_def:
  try_sc And v = (if (v = BoolV F) then (SOME v) else NONE) ∧
  try_sc Or v = (if (v = BoolV T) then (SOME v) else NONE) ∧
  try_sc Imp v = (if (v = BoolV F) then (SOME (BoolV T)) else NONE) ∧
  try_sc _ _ = NONE
End

Definition do_uop_def:
  do_uop Not v = case v of BoolV b => SOME (BoolV ¬b) | _ => NONE
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
  update_local_aux [] var val acc = NONE ∧
  update_local_aux ((x, w)::xs) var val acc =
  (if x = var then SOME (acc ++ ((x, SOME val)::xs))
   else update_local_aux xs var val (SNOC (x, w) acc))
End

Definition update_local_def:
  update_local st var val =
  (case update_local_aux st.locals var val [] of
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

Definition declare_locals_def:
  declare_locals st names =
  let uninit = MAP (λn. (n, NONE)) names in
    (st with locals := uninit ++ st.locals)
End

Theorem declare_locals_clock:
  (declare_locals st names).clock = st.clock
Proof
  gvs [declare_locals_def]
QED

Definition safe_drop_def:
  safe_drop n l =
  if LENGTH l < n then NONE else SOME (DROP n l)
End

Definition pop_locals_def:
  pop_locals n st =
  (case safe_drop n st.locals of
   | NONE => NONE
   | SOME new_locals => SOME (st with locals := new_locals))
End

Theorem pop_locals_clock:
  ∀n st st'. pop_locals n st = SOME st' ⇒ st'.clock = st.clock
Proof
  rpt strip_tac \\ gvs [pop_locals_def, AllCaseEqs ()]
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
   | SOME ss => SOME (st with cout := SNOC (concat ss) st.cout))
End

val _ = export_theory ();
