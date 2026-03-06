(*
  The formal semantics of bignumLang
*)
Theory bignumSem
Ancestors
  wordLang
  wordSem
  bignumLang
Libs
  preamble

Datatype:
  state =
    <| locals  : mlstring |-> 'a word
     (* ; stack   : ('a stack_frame) list *)
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     (* ; gc_fun  : 'a gc_fun_type *)
     ; clock   : num
     ; code    : mlstring |-> (mlstring list # ('a stmt))
     ; be      : bool (*is big-endian*) |>
End

Definition is_var_def:
  is_var s v ⇔ v ∈ FDOM s.locals
End

Definition get_var_def:
  get_var s v = FLOOKUP s.locals v
End

Definition get_var_const_def:
  (get_var_const s (cVar v) = get_var s v) ∧
  (get_var_const _ (cConst w) = SOME w)
End

Definition get_vars_def:
  get_vars s vs = OPT_MMAP (get_var s) vs
End

Definition set_var_def:
  set_var s v w = s with locals := s.locals⟨v ↦ w⟩
End

Definition set_vars_def:
  set_vars s vws = s with locals := s.locals |++ vws
End

Definition drop_var_def:
  drop_var s v = s with locals := s.locals \\ v
End

Definition mem_load_word_def:
  mem_load_word (addr:'a word) s =
  if addr IN s.mdomain then
    case s.memory addr of Word w => SOME w | _ => NONE
  else NONE
End

Definition dec_clock_def:
  dec_clock s = s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res,new_s) =
    (res, new_s with clock :=
          if old_s.clock < new_s.clock then old_s.clock else new_s.clock)
End

Theorem fix_clock_imp[local]:
  fix_clock st₀ x = (res, st₁) ⇒ st₁.clock ≤ st₀.clock
Proof
  Cases_on ‘x’ >> rw[fix_clock_def] >> gvs[]
QED

Definition find_code_def:
  find_code s name = FLOOKUP s.code name
End

Definition bignum_exp_def:
  (bignum_exp s (Const w) = SOME w) ∧
  (bignum_exp s (Var v) = get_var s v) ∧
  (bignum_exp s (Load addr) =
     case bignum_exp s addr of
     | NONE => NONE
     | SOME w => mem_load_word w s) ∧
  (bignum_exp s (Op op wexps) =
     case OPT_MMAP (bignum_exp s) wexps of
     | NONE => NONE
     | SOME ws => word_op op ws) ∧
  (bignum_exp s (Shift sh wexp wexp1) =
     case (bignum_exp s wexp, bignum_exp s wexp1) of
     | (SOME w, SOME w1) => word_sh sh w (w2n w1)
     | _ => NONE)
End

Definition bignum_exps_def:
  bignum_exps s es = OPT_MMAP (bignum_exp s) es
End

Datatype:
  result = (* todo how should return semantics be (return address) *)
           Result (('a word) list)
         | TimeOut
         | Error
End

Definition mem_store_word_def:
  mem_store_word s (addr:'a word) (w:'a word) =
    if addr ∈ s.mdomain then
      SOME (s with memory := s.memory⦇addr ↦ Word w⦈)
    else NONE
End

Definition call_env_def:
  call_env s params args =
    s with locals := FEMPTY |++ ZIP (params, args)
End

Definition restore_caller_def:
  restore_caller cur prev = cur with locals := prev.locals
End

Definition evaluate_def[nocompute]:
  (evaluate (Skip, s) = (NONE,s)) ∧
  (evaluate (Move moves, s) =
     if ALL_DISTINCT (MAP FST moves) then
       case get_vars s (MAP SND moves) of
       | NONE => (SOME Error,s)
       | SOME vs => (NONE, set_vars s (ZIP (MAP FST moves, vs)))
     else (SOME Error,s)) ∧
  (evaluate (Assign v exp, s) =
     case bignum_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var s v w)) ∧
  (evaluate (Store exp v, s) =
     case (bignum_exp s exp, get_var s v) of
     | (SOME a, SOME w) =>
         (case mem_store_word s a w of
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) ∧
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (Return ms,s) =
     case get_vars s ms of
     | SOME ys => (SOME (Result ys), s)
     | _ => (SOME Error,s)) ∧
  (evaluate (If cmp v arg c1 c2,s) =
    (case (get_var s v,get_var_const s arg) of
    | SOME x,SOME y =>
     (case word_cmp cmp (Word x) (Word y) of
      | SOME T => evaluate (c1,s)
      | SOME F => evaluate (c2,s)
      | NONE => (SOME Error,s))
    | _ => (SOME Error,s))) ∧
  (evaluate (While cmp v arg body, s) = (NONE, s)) ∧
  (evaluate (Dec name exp body, s) =
     if ¬is_var s name then (SOME Error, s) else
     case bignum_exp s exp of
     | SOME w =>
       let (res, s) = evaluate (body, set_var s name w) in
         (res, drop_var s name)
     | _ => (SOME Error, s)) ∧
  (evaluate (Call ret name args, s) =
   case bignum_exps s args of
   | NONE => (SOME Error,s)
   | SOME args =>
     case find_code s name of
     | NONE => (SOME Error,s)
     | SOME (params, body) =>
       if LENGTH params ≠ LENGTH args then (SOME Error, s)
       else if s.clock = 0 then (SOME TimeOut, s) else
         let (res, s₁) = evaluate (body, call_env (dec_clock s) params args) in
           (case ret of
            | NONE (* tail call *) => (res, s₁)
            | SOME outs (* return result into outs *) =>
                let s₂ = restore_caller s₁ s in
                  (case res of
                   | SOME (Result ws) =>
                       if LENGTH outs ≠ LENGTH ws then (SOME Error, s₂)
                       else (NONE, set_vars s₂ (ZIP (outs, ws)))
                   | res => (res, s₂))))
Termination
  wf_rel_tac ‘inv_image ($< LEX $<) (λ(stmt, s). (s.clock, stmt_size (K 0) stmt))’
  >> rw [call_env_def, dec_clock_def, set_var_def]
  >> drule $ GSYM fix_clock_imp >> simp []
End

Theorem evaluate_clock:
  ∀xs s₁ vs s₂. evaluate (xs, s₁) = (vs, s₂) ⇒ s₂.clock ≤ s₁.clock
Proof
  recInduct evaluate_ind >> rw [evaluate_def]
  >> gvs [mem_store_word_def, set_var_def, set_vars_def, AllCaseEqs()]
  >> rpt (pairarg_tac >> gvs [AllCaseEqs()])
  >> gvs [dec_clock_def, restore_caller_def, call_env_def, set_vars_def,
          drop_var_def]
  >> imp_res_tac fix_clock_imp >> simp []
QED

(* We store the theorems without fix_clock *)

Theorem fix_clock_evaluate[local]:
  fix_clock s (evaluate (c1,s)) = evaluate (c1,s)
Proof
  Cases_on ‘evaluate (c1,s)’ >> simp [fix_clock_def]
  >> imp_res_tac evaluate_clock >> simp [theorem "state_component_equality"]
QED

Theorem evaluate_ind[allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind
Theorem evaluate_def[allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_def
