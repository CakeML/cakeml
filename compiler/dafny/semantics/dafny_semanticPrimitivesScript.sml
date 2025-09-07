(*
  Defines semantic primitives used in Dafny's semantics.
*)
Theory dafny_semanticPrimitives
Ancestors
  alist
  mlstring
  dafny_ast
Libs
  preamble

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
  (* ArrV length location type *)
  | ArrV num num type
End

Datatype:
  heap_value =
  | HArr (value list) type
End

Datatype:
  state = <|
    clock: num;
    locals: (mlstring, (value option)) alist;
    heap: heap_value list;
    (* For old-expressions *)
    locals_old: (mlstring, (value option)) alist;
    heap_old: heap_value list;
    (* For prev-expressions *)
    locals_prev: (mlstring, (value option)) alist;
    heap_prev: heap_value list;
  |>
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
  init_state ck = <|
    clock := ck;
    locals := [];
    heap := [];
    locals_old := [];
    heap_old := [];
    locals_prev := [];
    heap_prev := [];
  |>
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
     (let new_locals = params ++ ZIP (outs, REPLICATE (LENGTH outs) NONE) in
      SOME (st with <|
                 locals := REVERSE new_locals;
                 locals_old := REVERSE new_locals;
                 locals_prev := REVERSE new_locals;
                 heap_old := st.heap
               |>)))
End

Definition restore_caller_def:
  restore_caller cur prev =
    cur with <|
      locals := prev.locals;
      locals_old := prev.locals_old;
      locals_prev := prev.locals_prev;
      heap_old := prev.heap_old;
      heap_prev := prev.heap_prev
    |>
End

Definition use_old_def:
  use_old st = st with <| locals := st.locals_old; heap := st.heap_old |>
End

Definition unuse_old_def:
  unuse_old cur prev = cur with <| locals := prev.locals; heap := prev.heap |>
End

Definition use_prev_def:
  use_prev st = st with <| locals := st.locals_prev; heap := st.heap_prev |>
End

Definition unuse_prev_def:
  unuse_prev cur prev = cur with <| locals := prev.locals; heap := prev.heap |>
End

Definition set_prev_def:
  set_prev st = st with <| locals_prev := st.locals; heap_prev := st.heap |>
End

Definition unset_prev_def:
  unset_prev cur prev = cur with <| locals_prev := prev.locals_prev; heap_prev := prev.heap_prev |>
End

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
  (value_same_type (ArrV _ _ ty) (ArrV _ _ ty') ⇔ ty' = ty) ∧
  (value_same_type _ _ ⇔ F)
End

Definition value_has_type_def[simp]:
  (value_has_type IntT (IntV _) ⇔ T) ∧
  (value_has_type BoolT (BoolV _) ⇔ T) ∧
  (value_has_type StrT (StrV _) ⇔ T) ∧
  (value_has_type (ArrT ty) (ArrV _ _ ty') ⇔ ty' = ty) ∧
  (value_has_type _ _ ⇔ F)
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
   | _ => NONE) ∧
  do_bop Mod v₀ v₁ =
  (case (v₀, v₁) of
   | (IntV i₀, IntV i₁) =>
       if i₁ = 0 then NONE else SOME (IntV (emod i₀ i₁))
   | _ => NONE)
End

Definition lit_to_val_def[simp]:
  lit_to_val (IntL i) = (IntV i) ∧
  lit_to_val (BoolL b) = (BoolV b) ∧
  lit_to_val (StrL s) = (StrV s)
End

Definition get_array_len_def:
  get_array_len (ArrV len _ _) = SOME len ∧
  get_array_len _ = NONE
End

Definition val_to_num_def:
  val_to_num (IntV i) = (if i < 0i then NONE else SOME (Num i)) ∧
  val_to_num _ = NONE
End

Definition index_array_def:
  index_array st arr idx =
  (case (arr, val_to_num idx) of
   | (ArrV len loc _, SOME idx) =>
     (case LLOOKUP st.heap loc of
      | NONE => NONE
      | SOME (HArr arr _) => LLOOKUP arr idx)
   | _ => NONE)
End

(* Can be used for both conditionals ITE and If *)
Definition do_cond_def:
  do_cond (BoolV b) thn els = SOME (if b then thn else els) ∧
  do_cond _ _ _ = NONE
End

Definition alloc_array_def:
  alloc_array st len init ty =
  (case val_to_num len of
   | NONE => NONE
   | SOME len =>
     let arr = (HArr (REPLICATE len init) ty) in
       SOME (st with heap := SNOC arr st.heap, ArrV len (LENGTH st.heap) ty))
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
   | (ArrV len loc _, SOME idx) =>
     (case LLOOKUP st.heap loc of
      | NONE => NONE
      | SOME (HArr arr ty) =>
          if idx ≥ LENGTH arr then NONE else
          let new_arr = LUPDATE val idx arr;
              new_heap = LUPDATE (HArr new_arr ty) loc st.heap
          in
            SOME (st with heap := new_heap))
   | _ => NONE)
End

Definition all_values_def:
  all_values IntT      = {IntV i | i ∈ 𝕌(:int)} ∧
  all_values BoolT     = {BoolV T; BoolV F} ∧
  all_values StrT      = {StrV s | s ∈ 𝕌(:mlstring)} ∧
  all_values (ArrT ty)  = {ArrV len loc ty | len ∈ 𝕌(:num) ∧ loc ∈ 𝕌(:num)}
End

Definition declare_local_def:
  declare_local st n =
    st with locals := (n, NONE)::st.locals
End

Definition push_local_def:
  push_local st var val =
  (st with locals := (var, SOME val)::st.locals)
End

Definition push_locals_def:
  push_locals st binds =
  let binds = (MAP (λ(var,val). (var, SOME val)) binds) in
    (st with locals := REVERSE binds ++ st.locals)
End

(* TODO Instead of safe_{drop,zip}, it would probably more accurate to call them
   strict *)
Definition safe_drop_def:
  safe_drop n xs = if n ≤ LENGTH xs then SOME (DROP n xs) else NONE
End

Definition pop_locals_def:
  pop_locals n st =
  (case safe_drop n st.locals of
   | NONE => NONE
   | SOME rest => SOME (st with locals := rest))
End

Definition eval_forall_def:
  eval_forall (dom: α set) eval =
    if (∃v. v ∈ dom ∧ SND (eval v) = Rerr Rtype_error)
    then Rerr Rtype_error
    else if (∃v. v ∈ dom ∧ SND (eval v) = Rerr Rtimeout_error)
    then Rerr Rtimeout_error
    else if (∀v. v ∈ dom ⇒ SND (eval v) = Rval (BoolV T))
    then Rval (BoolV T)
    (* NOTE For now, for simplicity reasons, we do not check whether (eval v) *)
    (*   is a Bool to throw a type error if not. Instead, we return (BoolV F). *)
    else Rval (BoolV F)
End

Definition valid_mod_def:
  valid_mod h locs h' =
  ∀loc hv. MEM loc locs ∧ oEL loc h = SOME hv ⇒ oEL loc h' = SOME hv
End

Definition get_loc_def:
  get_loc (ArrV _ loc _) = SOME loc ∧
  get_loc _ = NONE
End

Definition get_locs_def:
  get_locs vs = OPT_MMAP get_loc vs
End
