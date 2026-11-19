(*
  Bignum and operation implementation in Pancake
*)
Theory bignum_and
Ancestors
  errorLogMonad panPtreeConversion panLang panStatic multiword multiword_ext
  stackTest set_sep set_sep_ext address backend_common wordLang integer_word wordSem panSem
Libs
  stringLib numLib intLib preamble helperLib set_sep_extLib

(* Next: I feel like we want to run some sort of simp before our tactics *)
(* TODO Check for consistent naming *)

(* TODO
   Refactor tactics; should be stepable (i.e. modular and composed of things),
   and have good error messages. *)

(* TODO Should we give hint when we have something of shape
     x ∈ (dec_clock s).memaddrs as a side condition? *)

(* TODO Can we prove ⇔ for our step-theorems to make it clearer which ones
     are "safe" (i.e. cannot result in a stuck proof) *)

(* TODO Write a custom Pancake frontend:
   - annotations
   - labels
   - should generate both AST and theorem statements
 *)

(* TODO Maybe this should live in list syntax? *)
fun list_mk_cons tms tm = List.foldr listSyntax.mk_cons tm tms

(** set_sep and word helpers **************************************************)

(* TODO Move somewhere better *)
(* #bits is a power of two and at least 8 ⇒ byte-addressable memory *)
Definition byte_dimindex_def:
  byte_dimindex (:α) ⇔ ∃k. dimindex(:α) = 2 ** k ∧ 3 ≤ k
End

(* TODO Move somewhere better *)
Theorem byte_dimindex_leq:
  8 < dimindex (:α) ∧ byte_dimindex (:α) ⇒ 16 ≤ dimindex (:α)
Proof
  rw [byte_dimindex_def]
  >> qpat_x_assum ‘2 ** k = _’ $ SUBST_ALL_TAC o GSYM
  >> fs []
QED

(* TODO Move somewhere better *)
Theorem dimindex_DIV_8_lt_dimword:
  (dimindex (:α) DIV 8) < dimword (:α)
Proof
  simp [dimword_def]
  >> irule LESS_TRANS
  >> irule_at (Pos hd) DIV_LESS
  >> simp []
QED

(* TODO Move somewhere better *)
Theorem one_lt_w2n_bytes_in_word:
  16 ≤ dimindex (:α) ⇒ 1 < w2n (bytes_in_word: α word)
Proof
  simp [bytes_in_word_def, dimindex_DIV_8_lt_dimword, X_LT_DIV]
QED

(*
(* TODO Move somewhere better *)
Theorem one_lt_w2n_bytes_in_word:
  8 < dimindex (:α) ∧ byte_dimindex (:α) ⇒ 1 < w2n (bytes_in_word: α word)
Proof
  rw [byte_dimindex_def, bytes_in_word_def]
  >> simp [dimindex_DIV_8_lt_dimword]
  >> qpat_x_assum ‘2 ** k = _’ $ SUBST_ALL_TAC o GSYM >> simp []
  >> ‘8n = 2 ** 3’ by simp []
  >> pop_assum SUBST_ALL_TAC
  >> DEP_REWRITE_TAC [GSYM EXP_SUB] >> simp []
  >> Cases_on ‘k = 3’ >> gvs []
QED
*)

(* TODO Move somewhere better *)
Theorem dimword_MOD_bytes_in_word:
  byte_dimindex (:α) ⇒
  dimword (:α) MOD w2n (bytes_in_word: α word) = 0
Proof
  rw [bytes_in_word_def]
  >> ‘(dimindex (:α) DIV 8) MOD dimword (:α) = dimindex (:α) DIV 8’ by
    (simp [dimindex_DIV_8_lt_dimword])
  >> fs [byte_dimindex_def, dimword_def]
  >> ‘0 < dimindex (:α) DIV 8’ by
    (irule dividesTheory.DIV_POS >> simp []
     >> qpat_x_assum ‘2 ** k = _’ $ SUBST_ALL_TAC o GSYM >> simp [])
  >> ‘∃k. 2 ** dimindex (:α) = k * (dimindex (:α) DIV 8)’ by
    (qpat_x_assum ‘2 ** _ = dimindex (:α)’ $ SUBST_ALL_TAC o GSYM
     >> ‘8n = 2 ** 3’ by simp []
     >> pop_assum SUBST_ALL_TAC
     >> DEP_REWRITE_TAC [GSYM EXP_SUB] >> simp []
     >> qexists ‘2 ** (2 ** k − (k − 3))’
     >> rewrite_tac [GSYM EXP_ADD]
     >> DEP_REWRITE_TAC [SUB_ADD]
     >> irule LESS_EQ_TRANS
     >> irule_at (Pos hd) LESS_IMP_LESS_OR_EQ
     >> irule_at (Pos hd) LESS_2_EXP
     >> simp [])
  >> simp []
QED

(* TODO move to set_sep *)
Theorem ones_leq_dimword:
  ∀(frame: (α word # β -> bool) -> bool).
    byte_dimindex (:α) ∧ (ones a xs * frame) (fun2set (f, d)) ⇒
    LENGTH xs * w2n (bytes_in_word: α word) ≤ dimword (:α)
Proof
  rw []
  >> qabbrev_tac ‘bytes = w2n (bytes_in_word: α word)’
  >> qabbrev_tac ‘max_index = dimword (:α) DIV bytes’
  >> Cases_on ‘bytes = 0’ >- simp []
  >> ‘1 ≤ max_index’ by
    (unabbrev_all_tac >> simp [Req0 X_LE_DIV, w2n_lt, LESS_IMP_LESS_OR_EQ])
  >> simp [Req0 $ GSYM X_LE_DIV]
  >> CCONTR_TAC
  >> ‘∃ys zs. xs = ys ++ zs ∧ LENGTH ys = max_index ∧ 1 ≤ LENGTH zs’ by (
    qexistsl [‘TAKE max_index xs’, ‘DROP max_index xs’]
    >> unabbrev_all_tac >> Cases_on ‘xs’ >> gvs [])
  >> Cases_on ‘zs’ >> gvs [ones_append, ones_def]
  >> Cases_on ‘ys’ >> gvs [ones_def]
  >> qpat_x_assum ‘dimword _ DIV _ = _’ $ assume_tac o GSYM
  >> fs []
  >> qmatch_asmsub_abbrev_tac ‘one (a + more, _)’
  >> ‘a ≠ a + more’ by SEP_NEQ_TAC
  >> ‘more = 0w’ by
    (simp [Abbr ‘more’]
     >> ‘bytes_in_word = n2w bytes’ by simp [Abbr ‘bytes’]
     >> simp [word_mul_n2w]
     >> ‘bytes * (dimword (:α) DIV bytes) = dimword (:α)’ by
       (qspec_then ‘bytes’ mp_tac $ GSYM DIVISION >> simp []
        >> disch_then $ qspec_then ‘dimword (:α)’ mp_tac
        >> drule_then assume_tac dimword_MOD_bytes_in_word
        >> simp [Abbr ‘bytes’])
     >> simp [])
  >> gvs []
QED

Theorem i2w_one:
  i2w 1 = 1w
Proof
  simp [i2w_def]
QED

Theorem b2w_b2n:
  (if b2w b = 0w then 0n else 1) = b2n b
Proof
  Cases_on ‘b’ >> simp [b2w_def, b2n_def]
QED

Theorem WORD_NEG1_MUL_NOT:
  -1w * x  = ¬(x + -1w)
Proof
  simp [WORD_NOT, WORD_LEFT_ADD_DISTRIB]
QED

Theorem single_sub_0w_co[local]:
  single_sub (x: α word) 0w ci = (r, co)
  ⇒
  r = (x + -1w + b2w ci) ∧
  co = (dimword (:α) ≤ w2n x + w2n (-1w :α word) + b2n ci)
Proof
  strip_tac >> gvs [single_sub_def, single_add_def]
QED

(* TODO move *)
Theorem el_addr_add:
  n2w n * bytes_in_word + el_addr a i = el_addr a (i + n)
Proof
  simp [el_addr_def, GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB]
QED

(* TODO move *)
Theorem el_addr_sub:
  n ≤ i ⇒ -n2w n * bytes_in_word + el_addr a i = el_addr a (i - n)
Proof
  simp [el_addr_def, n2w_sub, WORD_LEFT_ADD_DISTRIB]
QED

(* TODO move *)
Theorem mw_fix_snoc_zero:
  mw_fix (SNOC 0w xs) = mw_fix xs
Proof
  simp [Once mw_fix_def]
QED

(* TODO Move? *)
Theorem LENGTH_mw_and:
  ∀xs ys. LENGTH (mw_and xs ys) = MIN (LENGTH xs) (LENGTH ys)
Proof
  recInduct mw_and_ind >> rw [mw_and_def, MIN_DEF]
QED

(** Pancake semantics rewrites ************************************************)

(** misc **********************************************************************)

Theorem FLOOKUP_res_var_neq[local]:
  n' ≠ n ⇒ FLOOKUP (res_var s (n, opt)) n' = FLOOKUP s n'
Proof
  Cases_on ‘opt’ >> rw [res_var_def, FLOOKUP_SIMP, DOMSUB_FLOOKUP_NEQ]
QED

Theorem FLOOKUP_res_var:
  FLOOKUP (res_var s (n, NONE))   n = NONE ∧
  FLOOKUP (res_var s (n, SOME v)) n = SOME v
Proof
  simp [res_var_def, FLOOKUP_SIMP]
QED

(*
Theorem FLOOKUP_set_var_neq[local]:
  n' ≠ n ⇒ FLOOKUP (set_var n value s).locals n' = FLOOKUP s.locals n'
Proof
  simp [set_var_def, FLOOKUP_SIMP]
QED

Theorem FLOOKUP_set_var:
  FLOOKUP (set_var n value s).locals n = SOME value
Proof
  simp [set_var_def, FLOOKUP_SIMP]
QED
*)

Theorem shape_of_ValWord:
  shape_of (ValWord x) = One
Proof
  simp [shape_of_def]
QED

Theorem shape_of_RStruct_One_One:
  shape_of (RStruct [ValWord x; ValWord y]) = Comb [One; One]
Proof
  simp [shape_of_def]
QED

(*
Theorem set_var_record:
  (set_var v value s).clock = s.clock ∧
  (set_var v value s).memaddrs = s.memaddrs ∧
  (set_var v value s).memory = s.memory ∧
  (set_var v value s).globals = s.globals ∧
  (set_var v value s).code = s.code ∧
  (set_var v value s).eshapes = s.eshapes ∧
  (set_var v value s).sh_memaddrs = s.sh_memaddrs ∧
  (set_var v value s).be = s.be ∧
  (set_var v value s).ffi = s.ffi ∧
  (set_var v value s).base_addr = s.base_addr ∧
  (set_var v value s).top_addr = s.top_addr ∧
  (set_var v value s).structs = s.structs
Proof
  simp [set_var_def]
QED
*)

Theorem dec_clock_record:
  (dec_clock s).locals = s.locals ∧
  (dec_clock s).memaddrs = s.memaddrs ∧
  (dec_clock s).memory = s.memory
Proof
  simp [dec_clock_def]
QED

(** eval **********************************************************************)

Theorem eval_Const:
  eval s (Const i) = SOME (ValWord (i2w i))
Proof
  simp [eval_def]
QED

Theorem eval_RStruct_One_One:
  r = RStruct [xv; yv] ∧
  eval s x = SOME xv ∧
  eval s y = SOME yv
  ⇒
  eval s (RStruct [x; y]) = SOME r
Proof
  simp [eval_def]
QED

Theorem eval_Var_Local:
  eval s (Var Local n) = FLOOKUP s.locals n
Proof
  simp [eval_def]
QED

Theorem eval_RField_Var_Local:
  FLOOKUP s.locals n = SOME (RStruct vs) ∧
  LLOOKUP vs i = SOME r
  ⇒
  eval s (RField i (Var Local n)) = SOME r
Proof
  simp [eval_def, LLOOKUP_THM]
QED

Theorem eval_BytesInWord:
  eval s BytesInWord = SOME (ValWord bytes_in_word)
Proof
  simp [eval_def]
QED

Theorem eval_Op_And_SOME:
  r = ValWord (v₁ && v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op And [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_Sub_SOME:
  r = ValWord (v₁ - v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Sub [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_Add_SOME:
  r = ValWord (v₁ + v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Add [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_BitwiseNot_SOME:
  r = (ValWord ¬v₁) ∧
  eval s x₁ = SOME (ValWord (v₁: α word))
  ⇒
  eval s (Op Xor [x₁; Const (-1)]) = SOME r
Proof
  simp [eval_def, word_op_def, i2w_minus_1]
QED

Theorem eval_Cmp_NotEqual_SOME:
  eval s e₁ = SOME (ValWord v₁) ∧
  eval s e₂ = SOME (ValWord v₂)
  ⇒
  eval s (Cmp NotEqual e₁ e₂) = SOME (ValWord (if v₁ ≠ v₂ then 1w else 0w))
Proof
  simp [eval_def, asmTheory.word_cmp_def]
QED

Theorem eval_Cmp_NotLower_SOME:
  eval s e₁ = SOME (ValWord v₁) ∧
  eval s e₂ = SOME (ValWord v₂) ∧
  (w = if v₂ ≤₊ v₁ then 1w else 0w)
  ⇒
  eval s (Cmp NotLower e₁ e₂) = SOME (ValWord w)
Proof
  simp [eval_def, asmTheory.word_cmp_def, WORD_NOT_LOWER]
QED

Theorem eval_Load_One_Local_SOME:
  r = (Val (s.memory v)) ∧
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  v ∈ s.memaddrs
  ⇒
  eval s (Load One (Var Local n)) = SOME r
Proof
  simp [eval_def, mem_load_def, is_wf_shape_def]
QED

(** evaluate ******************************************************************)

Theorem evaluate_Annot:
  evaluate (Annot s₁ s₂, s) = (NONE, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot_Left:
  evaluate (Seq (Annot s₁ s₂) c, s) = evaluate (c, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot_Right:
  evaluate (Seq c (Annot s₁ s₂), s) = evaluate (c, s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> simp []
QED


Theorem evaluate_Seq_assoc:
  evaluate (Seq (Seq s₁ s₂) (Seq s₃ s₄), s) =
  evaluate (Seq s₁ (Seq s₂ (Seq s₃ s₄)), s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rpt (IF_CASES_TAC >> gvs [])
QED

Theorem evaluate_While_False_NONE:
  res = NONE ∧
  s' = s ∧
  eval s e = SOME (ValWord (i2w i: α word)) ∧
  i2w i = (0w :α word)
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_While_True:
  eval s e = SOME (ValWord w) ∧
  w ≠ (0w :α word) ∧
  s.clock ≠ 0 ∧
  evaluate (c, dec_clock s) = (res, s₁) ∧
  (case res of
   | SOME Continue => evaluate (While e c, s₁) = (res₁, s₂)
   | NONE => evaluate (While e c, s₁) = (res₁, s₂)
   | SOME Break => (NONE, s₁) = (res₁, s₂)
   | _ => (res, s₁) = (res₁, s₂))
  ⇒
  evaluate (While e c,s) = (res₁, s₂)
Proof
  rw [] >> simp [Once evaluate_def]
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
QED

(*
Theorem evaluate_While_True_NONE:
  eval s e = SOME (ValWord w) ∧
  w ≠ (0w :α word) ∧
  s.clock ≠ 0 ∧
  evaluate (c, dec_clock s) = (res, s₁) ∧
  (case res of
   | SOME Continue => evaluate (While e c, s₁) = (NONE, s₂)
   | NONE => evaluate (While e c, s₁) = (NONE, s₂)
   | SOME Break => s₁ = s₂
   | _ => F) ∧
  evaluate (While e c, s₁) = (NONE, s₂)
  ⇒
  evaluate (While e c,s) = (NONE, s₂)
Proof
  rw [] >> simp [Once evaluate_def]
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
QED

Theorem evaluate_While_NONE:
  0 < s.clock ∧
  eval s e = SOME (ValWord (i2w i: α word)) ∧
  (if i2w i = (0w: α word) then s = s₂
   else
     evaluate (Seq Tick c, s) = (res, s₁) ∧
     (case res of
      | SOME Continue => evaluate (While e c, s₁) = (NONE, s₂)
      | NONE => evaluate (While e c, s₁) = (NONE, s₂)
      | SOME Break => s₁ = s₂
      | _ => F)) ⇒
  evaluate (While e c,s) = (NONE, s₂)
Proof
  simp [Once evaluate_def]
  >> simp [Once evaluate_def]
  >> IF_CASES_TAC
  >> strip_tac >> gvs []
  >> simp [Once evaluate_def]
  >> qabbrev_tac ‘hidden = While e c’
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
QED

Theorem evaluate_While_NONE:
  eval s e = SOME (ValWord (i2w i)) ∧
  evaluate (If (Const i) (Seq Tick (Seq c (While e c))) Skip, s) = (NONE, s')
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  once_rewrite_tac [evaluate_def]
  >> qabbrev_tac ‘hidden = While e c’
  >> simp []
  >> reverse IF_CASES_TAC >> gvs []
  >- simp [evaluate_def]
  >> simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘s.clock = 0’ >> gvs []
  >> IF_CASES_TAC >> gvs []
QED
*)

Theorem evaluate_If:
  eval s e = SOME (ValWord w) ∧
  w = i2w i ∧
  evaluate (If (Const i) c1 c2,s) = (res, s')
  ⇒
  evaluate (If e c1 c2,s) = (res, s')
Proof
  once_rewrite_tac [evaluate_def] >> simp [eval_Const]
QED

Theorem evaluate_Dec_no_error:
  (s₂ = s₁ with locals := res_var s₁.locals (v, FLOOKUP s.locals v)) ∧
  eval s e = SOME value ∧
  shape = shape_of value ∧
  evaluate (prog,s with locals := s.locals |+ (v,value)) = (res,s₁)
  ⇒
  evaluate (Dec v shape e prog, s) = (res, s₂)
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_Seq:
  evaluate (c₁, s) = (res, s₁) ∧
  (if res = NONE
   then evaluate (c₂, s₁) = (res₁, s₂)
   else (res₁, s₂) = (res, s₁))
  ⇒
  evaluate (Seq c₁ c₂, s) = (res₁, s₂)
Proof
  rw [] >> simp [evaluate_def]
QED

Theorem evaluate_Store_Local_NONE:
  res = NONE ∧
  s' = s with memory := s.memory⦇addr ↦ v⦈ ∧
  FLOOKUP s.locals dst = SOME (ValWord addr) ∧
  addr ∈ s.memaddrs ∧
  eval s e = SOME (Val v)
  ⇒
  evaluate (Store (Var Local dst) e, s) = (res, s')
Proof
  simp [evaluate_def, flatten_def, mem_stores_def, mem_store_def,
        eval_Var_Local]
QED

Theorem evaluate_Assign_Local:
  res = NONE ∧
  s' = s with locals := s.locals⟨dst ↦ value⟩ ∧
  eval s src = SOME value ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of value = shape_of old_value
  ⇒
  evaluate ((Assign Local dst src), s) = (res, s')
Proof
  simp [evaluate_def, is_valid_value_def, set_var_def]
QED

Theorem evaluate_Primitive_AddCarry:
  res = NONE ∧
  s' =
    s with locals :=
      s.locals⟨
       dst ↦
       (RStruct
          [ValWord (n2w add_res : α word);
           ValWord (if dimword (:α) ≤ add_res then 1w else 0w)])⟩ ∧
  eval s l = SOME (ValWord lv) ∧
  eval s r = SOME (ValWord rv) ∧
  eval s ci = SOME (ValWord civ) ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of old_value = Comb [One; One] ∧
  add_res = w2n lv + w2n rv + (if civ = 0w then 0 else 1)
  ⇒
  evaluate (Primitive dst AddCarry [l; r; ci], s) = (res, s')
Proof
  simp [evaluate_def, pan_primop_def, isValWord_def, theValWord_def,
        is_valid_value_def, word_add_carry_def, set_var_def,
        shape_of_RStruct_One_One]
QED

Theorem evaluate_Tick_NONE:
  res = NONE ∧
  s' = dec_clock s ∧  (* NOTE we are using this form for easier matching of the rules *)
  s.clock ≠ 0
  ⇒
  evaluate (Tick, s) = (res, s')
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Break:
  res = SOME Break ∧ s' = s
  ⇒
  evaluate (Break, s) = (res, s')
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Return_no_error:
  eval s e = SOME value ∧
  size_of_sh_with_ctxt s.structs (shape_of value) ≤ 32 ∧
  res = SOME (Return value) ∧
  s' = empty_locals s
  ⇒
  evaluate (Return e, s) = (res, s')
Proof
  simp [evaluate_def]
QED

(* TODO Generalize to arbitrary number of arguments *)
(* TODO Generalize to deal with exception handler (SOME) *)
Theorem evaluate_StandAloneCall_NONE_4:
  eval s arg₀ = SOME argv₀ ∧
  eval s arg₁ = SOME argv₁ ∧
  eval s arg₂ = SOME argv₂ ∧
  eval s arg₃ = SOME argv₃ ∧
  lookup_code s.code fname [argv₀; argv₁; argv₂; argv₃] =
    SOME (prog, newlocals, return_sh) ∧
  s.clock ≠ 0 ∧
  evaluate (prog, (dec_clock s) with locals:= newlocals) = (res₁, s₁) ∧
  (case res₁ of
   | SOME (Return retv) =>
       if shape_of retv ≠ return_sh
       then res = SOME Error ∧ s' = s₁
       else res = NONE ∧ s' = (s₁ with locals := s.locals)
   | SOME (Exception _ _) =>
       res = res₁ ∧ s' = empty_locals s₁
   | NONE => res = SOME Error ∧ s' = s₁
   | SOME Break => res = SOME Error ∧ s' = s₁
   | SOME Continue => res = SOME Error ∧ s' = s₁
   | _ => res = res₁ ∧ s' = empty_locals s₁)
  ⇒
  evaluate (StandAloneCall NONE fname [arg₀; arg₁; arg₂; arg₃], s) = (res, s')
Proof
  rw [evaluate_def]
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
  >> IF_CASES_TAC >> gvs []
QED

(** lookup_code ***************************************************************)

Theorem lookup_code_SOME:
  FLOOKUP code fname = SOME (vshapes, prog, rshape) ∧
  ALL_DISTINCT (MAP FST vshapes) ∧
  LIST_REL (\vshape arg. SND vshape = shape_of arg) vshapes args ∧
  res = SOME (prog, FEMPTY |++ ZIP (MAP FST vshapes,args), rshape)
  ⇒
  lookup_code code fname args = res
Proof
  simp [lookup_code_def]
QED


(** Pancake implementation ****************************************************)

(* Pancake woes
  - Pancake parser is not very fast
  - Error messages are not very good
  - What if I don't want to return anything?
  - nested else-if?
*)

(* Following copied from panConcreteExamples*)

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_topdecs_to_ast ^code” |> concl |> rand |> rand
  end

(* TODO rewrite this slop properly *)
fun get_function name prog =
  let
    val target = ``strlit ^(stringSyntax.fromMLstring name)``
    fun field_of fld r =
      Option.map snd
        (List.find (fn (f, _) => f = fld) (snd (TypeBase.dest_record r)))
    fun is_named d =
      (case strip_comb d of
         (c, [r]) =>
           fst (dest_const c) = "Function" andalso
           (case field_of "name" r of
              SOME v => aconv v target
            | NONE => false)
       | _ => false)
      handle HOL_ERR _ => false
  in
    case List.find is_named (fst (listSyntax.dest_list prog)) of
      SOME d => d
    | NONE => raise mk_HOL_ERR "get_function" "get_function"
                      ("no function named " ^ name)
  end;

(* TODO rewrite this slop properly *)
fun get_field fld name prog =
  let
    val (_, args) = strip_comb (get_function name prog)
    val r = case args of
              [r] => r
            | _ => raise mk_HOL_ERR "get_field" "get_field" "unexpected shape"
  in
    case List.find (fn (f, _) => f = fld) (snd (TypeBase.dest_record r)) of
      SOME (_, v) => v
    | NONE => raise mk_HOL_ERR "get_field" "get_field" ("no field " ^ fld)
  end;

fun state_alpha ty =
  case dest_thy_type ty of
    {Thy = "panSem", Tyop = "state", Args = [a, _]} => a
  | _ => raise mk_HOL_ERR "bignum_and" "state_alpha" "not a panSem$state type";

Quote pan_playground = parse_pancake:
End

(* TODO go through Pancake code and see whether it could be improved with
   additions to Pancake *)
Quote and_prog = parse_pancake:
fun copy(to, from, num) {
  while num {
    var tmp = lds 1 from;
    st to, tmp;
    to   = to + @biw;
    from = from + @biw;
    num  = num - 1;
  }
  return 0;
}

(* Assumes xs points to the end *)
fun mw_fix_pan(xs_len, xs) {
  while xs_len {
    var t1 = lds 1 xs;
    if t1 {
      break;
    } else {
      xs_len = xs_len - 1;
      xs = xs - @biw;
    }
  }
  return xs_len;
}

fun mw_and_pan(xs_len, xs, ys, zs) {
  while xs_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    st zs, x & y;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    xs_len = xs_len - 1;
  }
  return 0;
}

fun mw_and_flip_pan(xs_len, xs, ys_len, ys, zs) {
  if xs_len <=+ ys_len { mw_and_pan(xs_len, xs, ys, zs); return xs_len; }
  else { mw_and_pan(ys_len, ys, xs, zs); return ys_len; }
}

fun mwi_and_neg_pos_geq_pan(c, xs, ys_len, ys, zs) {
  while ys_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} y1c1 = __add_with_carry__(y, -1, c);
    var y2 = y1c1.0 ^ -1;
    st zs, x & y2;
    c = y1c1.1;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    ys_len = ys_len - 1;
  }
  return 0;
}

fun mwi_and_neg_pos_lt(c, xs_len, xs, ys_len, ys, zs) {
  var diff = ys_len - xs_len;
  while xs_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} x1c1 = __add_with_carry__(x, -1, c);
    var x2 = x1c1.1 ^ -1;
    st zs, x2 & y;
    c = y1c1.1;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    xs_len = xs_len - 1;
  }
  return copy(zs, ys, diff);
}

fun mwi_and_neg_neg_pan(c, d, e, xs_len, xs, ys_len, ys, zs) {
  while xs_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} x1c1 = __add_with_carry__(x, -1, c);
    var {1,1} y1d1 = __add_with_carry__(y, -1, d);
    var {1,1} z1e1 = __add_with_carry__(x1c1.1 | y1d1.1, 0, e);
    st zs, z1e1.1;
    c = x1c1.2;
    d = y1d1.2;
    e = z1e1.2;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    xs_len = xs_len - 1;
    ys_len = ys_len - 1;
  }
  while ys_len {
    var y = lds 1 ys;
    var {1,1} y1d1 = __add_with_carry__(y, -1, d);
    var {1,1} z1e1 = __add_with_carry__(y1d1.1, 0, e);
    st zs, z1e1.1;
    d = y1d1.2;
    e = z1e1.2;
    ys = ys + @biw;
    zs = zs + @biw;
    ys_len = ys_len - 1;
  }
  if e { st zs, 1; } else { st zs, 0; }
}

fun mwi_and_fused_pan(s, xs_len, xs, t, ys_len, ys, zs) {
  if s {
    if t {
      if xs_len <= ys_len {
        var t1 = mwi_and_neg_neg_pan(0, 0, 1, xs, ys_len, ys, zs);
      } else {
        var t1 = mwi_and_neg_neg_pan(0, 0, 1, ys, xs_len, xs, zs);
      }
      var zs_len = mw_fix_pan(t1, zs);
      return <1, zs_len>;
    } else {
      if xs_len < ys_len {
        mwi_and_neg_pos_lt_pan(0, xs, xs_len, ys, ys_len, zs);
        var t1 = ys_len;
      } else {
        mwi_and_neg_pos_geq_pan(0, ys, xs_len, xs, zs);
        var t1 = ys_len;
      }
      var zs_len = mw_fix_pan(t1, zs);
      return <0, zs_len>;
    }
  } else {
    if t {
      if ys_len < xs_len {
        mwi_and_neg_pos_lt_pan(0, ys_len, ys, xs_len, xs, zs);
        var t1 = ys_len;
      } else {
        mwi_and_neg_pos_geq_pan(0, xs, ys_len, ys, zs);
        var t1 = xs_len;
      }
      var zs_len = mw_fix_pan(t1, zs);
      return <0, zs_len>;
    } else {
      var t1 = mw_and_flip_pan(xs_len, xs, ys_len, ys, zs);
      var zs_len = mw_fix_pan(t1, zs);
      return <0, zs_len>;
    }
  }
}
End

(* TODO Run the Pancake static analyzer here *)

fun get_params name = get_field "params" name and_prog
fun get_body name   = get_field "body" name and_prog
fun get_return name = get_field "return" name and_prog

fun fold_back snippets body =
  body |> REWRITE_CONV (map GSYM snippets) |> concl |> rhs

fun get_loops name =
  rev $ find_terms (can $ match_term “panLang$While _ _”) $ get_body name

val mw_fix_pan_body              = get_body "mw_fix_pan"
val mw_and_pan_body              = get_body "mw_and_pan"
val mwi_and_neg_pos_geq_pan_body = get_body "mwi_and_neg_pos_geq_pan"
val mw_and_flip_pan_body         = get_body "mw_and_flip_pan"
val mwi_and_neg_neg_pan_body     = get_body "mwi_and_neg_neg_pan"

(** mw_fix_pan ****************************************************************)

Definition mw_fix_pan_loop_def:
  mw_fix_pan_loop = ^(List.nth (get_loops "mw_fix_pan", 0))
End

(** mw_and_pan ****************************************************************)

Definition mw_and_pan_loop_def:
  mw_and_pan_loop = ^(List.nth (get_loops "mw_and_pan", 0))
End

Definition mw_and_pan_body_def:
  mw_and_pan_body = ^(fold_back [mw_and_pan_loop_def] mw_and_pan_body)
End

val mw_and_pan_code =
  list_mk_pair [
      get_params "mw_and_pan",
      “mw_and_pan_body”,
      get_return "mw_and_pan"
    ]

(** mw_and_flip_pan ***********************************************************)

Definition mw_and_flip_pan_body_def:
  mw_and_flip_pan_body = ^(mw_and_flip_pan_body)
End

(** mwi_and_neg_pos_geq_pan ***************************************************)

Definition mwi_and_neg_pos_geq_pan_loop_def:
  mwi_and_neg_pos_geq_pan_loop =
    ^(List.nth (get_loops "mwi_and_neg_pos_geq_pan", 0))
End

Definition mwi_and_neg_pos_geq_pan_body_def:
  mwi_and_neg_pos_geq_pan_body =
    ^(fold_back [mwi_and_neg_pos_geq_pan_loop_def] mwi_and_neg_pos_geq_pan_body)
End

(** mwi_and_neg_neg_pan *******************************************************)

Definition mwi_and_neg_neg_pan_loop0_def:
  mwi_and_neg_neg_pan_loop0 =
    ^(List.nth (get_loops "mwi_and_neg_neg_pan", 0))
End

Definition mwi_and_neg_neg_pan_loop1_def:
  mwi_and_neg_neg_pan_loop1 =
    ^(List.nth (get_loops "mwi_and_neg_neg_pan", 1))
End

Definition mwi_and_neg_neg_pan_body_def:
  mwi_and_neg_neg_pan_body =
    ^(fold_back [mwi_and_neg_neg_pan_loop0_def, mwi_and_neg_neg_pan_loop1_def]
        mwi_and_neg_neg_pan_body)
End

(** Correctness ***************************************************************)

(* stack_empty_eq, stack_sing_eq and stack_cons_eq are used in automation to
   unfold stack. *)
Theorem stack_empty_eq:
  stack [] ⇔ T
Proof
  simp [stack_def]
QED

Theorem stack_sing_eq:
  stack [x] ⇔ x
Proof
  simp [stack_def]
QED

Theorem stack_cons_eq:
  stack (x::xs) ⇔ x ∧ stack xs
Proof
  simp [stack_def]
QED

Theorem stack_T:
  stack (T::xs) = stack xs
Proof
  simp [stack_def]
QED

Theorem stack_pull:
  x ∧ stack xs
  ⇒
  stack (x::xs)
Proof
  simp [stack_def]
QED

Theorem stack_evaluate:
  stack [evaluate (stmt, s) = (res, s')] ⇔ evaluate (stmt, s) = (res, s')
Proof
  simp [stack_def]
QED

Theorem add_rest[local]:
  (stack P ⇒ stack Q) ⇒ stack (P ++ rest) ⇒ stack (Q ++ rest)
Proof
  simp [stack_def]
QED

Theorem stack_mono[local]:
  (P ⇒ Q) ⇒ stack [P] ⇒ stack [Q]
Proof
  simp [stack_def]
QED

Theorem stack_conj[local]:
  stack ((P ∧ Q)::rest) = stack (P::Q::rest)
Proof
  simp [stack_def, CONJ_ASSOC]
QED

val ERR = mk_HOL_ERR "bignum_and";
val WRAP_EXN = wrap_exn "bignum_and";

fun stackify_imp_th th = let
  val RRULE = REWRITE_RULE
  val ADD_STACK = MATCH_MP stack_mono
  (* TODO look at this again; we might be able to do it more efficently? *)
  fun FLATTEN_STACK th = th |> RRULE [CONJ_ASSOC] |> RRULE [stack_conj];
  fun ADD_REST th = th |> MATCH_MP add_rest |> RRULE [APPEND]
in
  th |> ADD_STACK |> FLATTEN_STACK |> ADD_REST
    handle e => raise WRAP_EXN "stackify_imp_th" e
end

(* TODO Add comments *)
(* TODO make LLM look over it *)

(* TODO Add more hints/make it easy to step through *)

(* todo add tactic to turn head into subgoal *)

(* Adds the assumptions asl to thl. Useful for rewriters/simplifiers that make
   use of the assumptions. *)
fun add_asms asl thl = map ASSUME asl @ thl

(*
val it = stackify_imp_th evaluate_Dec_no_error
*)

val (stack_tm, mk_stack, dest_stack, is_stack) = syntax_fns1 "stackTest" "stack"
fun is_stack_cons tm = is_stack tm andalso listSyntax.is_cons (dest_stack tm)
val (eval_tm, mk_eval, dest_eval, is_eval) = syntax_fns2 "panSem" "eval"
val (evaluate_tm, mk_evaluate, dest_evaluate, is_evaluate) = syntax_fns1 "panSem" "evaluate"
val (While_tm, mk_While, dest_While, is_While) = syntax_fns2 "panLang" "While"
val (If_tm, mk_If, dest_If, is_If) = syntax_fns3 "panLang" "If"
val (Const_tm, mk_Const, dest_Const, is_Const) = syntax_fns1 "panLang" "Const"

(* Returns i2w tm ≠ 0w, given that tm is of type word. *)
fun mk_i2w_neq_0w ty tm = let
  val w = integer_wordSyntax.mk_i2w (tm, ty)
    handle e => raise WRAP_EXN "mk_i2w_neq_0w" e
  val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, ty)
in mk_neg (mk_eq (w, zero)) end

(* Returns whether tm is of form evaluate (While ..., ...). *)
fun is_evaluate_While tm =
  if not $ is_evaluate tm then false
  else is_While $ fst $ dest_pair $ dest_evaluate tm

(* Returns whether tm is of form evaluate (If ..., ...). *)
fun is_evaluate_If tm =
  if not $ is_evaluate tm then false
  else is_If $ fst $ dest_pair $ dest_evaluate tm

(* Returns w if tm is of the form (If (Const w) ... , ...)*)
fun dest_evaluate_If_Const tm =
  let val (cond, _, _,) = dest_If $ fst $ dest_pair $ dest_evaluate tm in
    dest_Const cond end

(* Returns whether tm is of form evaluate (If (Const ...) ... , ...). *)
val is_evaluate_If_Const = can $ dest_evaluate_If_Const

(* Applies a conversion to the first instance of stack in the top-level
   conjuncts (modulo leading quantifiers) *)
fun STACK_CONV c =
  let
    fun search tm =
      if is_stack tm then c tm
      else if is_conj tm then
        let val (l, _) = dest_conj tm in
          if is_stack l then LAND_CONV c tm
          else RAND_CONV search tm
        end
      else raise ERR "STACK_CONV" "no stack conjunct found"
  in
    STRIP_QUANT_CONV search
  end

(* Applies a conversion to the head of the first instance of stack
   in the top-level conjuncts (modulo leading quantifiers) *)
fun STACK_HEAD_CONV conv =
  let
    fun head_conv tm =
      if is_stack_cons tm then RAND_CONV (LAND_CONV conv) tm
      else raise ERR "STACK_HEAD_CONV" "stack is empty"
  in
    STACK_CONV head_conv
  end

(* Theorems of the form {evaluate,eval} ... = ...  *)
val (step_eq_thl: thm list) =
  [eval_Var_Local, evaluate_Seq_Annot_Left, eval_Const, eval_BytesInWord]
val _ =
  if not (all (is_eq o concl) step_eq_thl) then
    raise ERR "assertion failure" "non-equality found in step_eq_thl"

(* Theorems of the form
   stack (...) ⇒ stack ({evaluate,eval,lookup_code} ...) *)
val (step_imp_thl: thm list) =
  [evaluate_Dec_no_error, eval_Load_One_Local_SOME, eval_RStruct_One_One,
   evaluate_Primitive_AddCarry, evaluate_Seq, eval_Op_BitwiseNot_SOME,
   eval_Cmp_NotLower_SOME,
   eval_RField_Var_Local, evaluate_Store_Local_NONE,
   eval_Op_And_SOME, evaluate_Assign_Local, eval_Op_Add_SOME, eval_Op_Sub_SOME,
   evaluate_Tick_NONE, evaluate_Break, evaluate_Return_no_error,
   evaluate_StandAloneCall_NONE_4, lookup_code_SOME]
  |> map stackify_imp_th

(* Given ⊢ A = B, returns A. *)
fun eq_thm_lhs thm = thm |> concl |> dest_eq |> fst

(* Given ⊢ A ⇒ B, returns B. *)
fun imp_thm_rhs thm = thm |> concl |> dest_imp |> snd

(* Rewrites with the theorems in step_eq_thl at the stack head, failing if
   the goal remains unchanged. *)
val step_eq_tac : tactic =
  CHANGED_TAC (CONV_TAC (STACK_HEAD_CONV (REWRITE_CONV step_eq_thl)))
    handle e => raise WRAP_EXN "step_eq_tac" e

(* Returns the first stack term in a list of terms. *)
fun first_stack tms =
  Lib.first is_stack tms
  handle e => raise WRAP_EXN "first_stack: could not find stack term" e

(* Given a stack term, returns the appropriate irule instantiation using an
   appropriate theorem from thl. *)
fun stack_imp_tac thl (stack: term) = let
  val candidates =
    filter (fn thm => can (match_term (imp_thm_rhs thm)) stack) thl
  val count = length candidates
  val winner =
    if count = 1 then hd candidates
    else if count = 0 then
      raise ERR "stack_imp_tac" "no matching stack theorem found."
    else raise ERR "stack_imp_tac" "found multiple candidate stack theorems."
in irule_at (Pos first_stack) winner end

val step_imp_tac = stack_imp_tac step_imp_thl

(* TODO Some automation that tries to make this choice for us. *)
(* Unfolds evaluate (While ...) = ... at the head. *)
val enter_loop =
  irule_at (Pos first_stack) (stackify_imp_th evaluate_While_True)
val skip_loop =
  irule_at (Pos first_stack) (stackify_imp_th evaluate_While_False_NONE)

(* Reduces evaluate (If ...) = ... at the head to
   evaluate (If (Const ...) ...) = ... . This tactic should not be used on
   If with a Const condition, as it will not lead to progress in the proof. *)
val step_If = irule_at (Pos first_stack) (stackify_imp_th evaluate_If)

(* Finds the "redex" of the stack (lhs of wants at the top of the stack) . *)
fun find_redex tm = let
  val stack = find_term is_stack tm
    handle HOL_ERR _ => raise ERR "find_redex" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "find_redex" "stack is empty"
in
  lhs head handle HOL_ERR _ => raise ERR "find_redex" "not an equality"
end

(* For use in step_If_Const *)
Theorem evaluate_If_Const_T:
  (i2w i ≠ (0w :α word) ⇔ T)
  ⇒
  evaluate (c1, s: (α, γ) state) = (res, s')
  ⇒
  evaluate (If (Const i) c1 c2,s) = (res, s')
Proof
  simp [evaluate_def, eval_Const]
QED

(* For use in step_If_Const *)
Theorem evaluate_If_Const_F:
  (i2w i ≠ (0w :α word) ⇔ F)
  ⇒
  evaluate (c2, s: (α, γ) state) = (res, s')
  ⇒
  evaluate (If (Const i) c1 c2,s) = (res, s')
Proof
  simp [evaluate_def, eval_Const]
QED

(* Given a head of the form  evaluate (If (Const w) ...) = ..., tries to
   reduce w ≠ 0w to T or F and choose the branch accordingly. *)
val step_If_Const : tactic = fn (g as (asl, w)) => fn ctxt => let
  val redex = find_redex w
  val word_ty = state_alpha $ el 2 $ snd $ dest_type $ type_of redex
  val cond = mk_i2w_neq_0w word_ty (dest_evaluate_If_Const redex)
    handle e => raise WRAP_EXN "step_If_Const" e
  val thl = [i2w_pos, n2w_11, LESS_MOD, ZERO_MOD, ZERO_LT_dimword, ONE_LT_dimword]
  val reduced_th = QCONV (SIMP_CONV arith_ss (add_asms asl thl)) cond
  val reduced = rhs $ concl $ reduced_th
in
  if aconv reduced boolSyntax.T then
    irule_at (Pos first_stack)
      (stackify_imp_th $ MATCH_MP evaluate_If_Const_T reduced_th) g ctxt
  else if aconv reduced boolSyntax.F then
    irule_at (Pos first_stack)
      (stackify_imp_th $ MATCH_MP evaluate_If_Const_F reduced_th) g ctxt
  else raise ERR "step_If_Const" $
    concat [
      "failed to reduce condition ", term_to_string cond, " to a boolean.\n",
      "Hint: no assumption determines this; add one and try again.\n",
      "debug: reduced_th: ", thm_to_string reduced_th
      ]
end

(* Reduces a goal that contains
  stack (({evaluate,eval,lookup_code} ... = ...)::...). *)
val step : tactic = fn (g as (asl, w)) => fn ctxt => let
  val stack = find_term is_stack w
    handle HOL_ERR _ => raise ERR "step_core" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "step_core" "stack is empty"
  val _ =
    if not (is_eq head) then
      raise ERR "step_core" "stack head is not an equality"
  val redex = lhs head
  val matches_eq =
    exists (fn thm => can (match_term (eq_thm_lhs thm)) redex) step_eq_thl
in
  (if is_evaluate_While redex then
     raise ERR "step_core" "Use enter_loop or skip_loop."
   else if is_evaluate_If_Const redex then step_If_Const
   else if is_evaluate_If redex then step_If
   else if matches_eq then
     step_eq_tac handle e => raise WRAP_EXN "step_core" e
   else
     step_imp_tac stack handle e => raise WRAP_EXN "step_core" e) g ctxt
end

(* Rewrites stack (T::rest) to stack (rest). *)
val head_pop_T_conv = STACK_CONV (REWR_CONV stack_T)
val head_pop_T = CHANGED_TAC (CONV_TAC head_pop_T_conv)

(* Unfolds the stack into a conjunction.
   Examples:
   > STACK_UNFOLD_CONV “stack [A ∧ B ∧ C; D; (E ∧ G) ∧ H]”
   val it = ⊢ ... ⇔ (A ∧ B ∧ C) ∧ D ∧ (E ∧ G) ∧ H: thm
   > STACK_UNFOLD_CONV “stack ((A ∧ B ∧ C)::xs)”
   val it = ⊢ ... ⇔ (A ∧ B ∧ C) ∧ stack xs: thm
 *)
val STACK_UNFOLD_CONV: conv = let
  val unfold_empty = REWR_CONV stack_empty_eq
  val unfold_sing  = REWR_CONV stack_sing_eq
  val unfold_cons  = REWR_CONV stack_cons_eq
  fun unfold tm =
    (unfold_sing ORELSEC
     (unfold_cons THENC (TRY_CONV (RAND_CONV unfold)))) tm
in
  fn tm => (unfold_empty ORELSEC unfold) tm
    handle HOL_ERR _ => raise ERR "STACK_UNFOLD_CONV" "cannot unfold this shape"
end

(* Flattens a conjunction in the head of the stack into the stack.
   Example:
   > FLATTEN_HEAD_CONV “stack [A ∧ B ∧ C; D; E ∧ G]”
   val it = ... ⇔ stack [A; B; C; D; E ∧ G]: thm
   > FLATTEN_HEAD_CONV “stack ((A ∧ B)::xs)”
   val it = ... ⇔ stack (A::B::xs): thm
 *)
fun FLATTEN_HEAD_CONV stack = let
  fun err msg = raise ERR "FLATTEN_HEAD_CONV" msg
  fun wrap e = raise WRAP_EXN "FLATTEN_HEAD_CONV" e
  val stack_xs = dest_stack stack
    handle HOL_ERR _ => err "not a stack"
  val (head, tail) = listSyntax.dest_cons stack_xs
    handle HOL_ERR _ => err "not cons"
  val new_stack = mk_stack $ list_mk_cons (strip_conj head) tail
in
  NORM_EQ (STACK_UNFOLD_CONV THENC Canon.CONJ_CANON_CONV) stack new_stack
    handle e => wrap e
end
val flatten_head = CONV_TAC (STACK_CONV FLATTEN_HEAD_CONV)

(* Rewrites the head of the stack using the assumptions and the passed
   theorem list. *)
(*
fun head_asm_rewrite thl : tactic = fn (g as (asl, w)) =>
    CONV_TAC (STACK_HEAD_CONV (ASM_REWRITE_CONV asl thl)) g
*)

(* Simplifies the head of the stack using the assumptions, the simpset and
   the passed theorem list. *)
fun head_asm_simp ss thl : tactic = fn (g as (asl, w)) => fn ctxt =>
  CONV_TAC (STACK_HEAD_CONV (SIMP_CONV ss (add_asms asl thl))) g ctxt


Theorem n2w_i2w_eq:
  &n = i ⇒ n2w n = i2w i
Proof
  rw [] >> simp [i2w_pos]
QED

(* Theorems of the form stack (...) ⇒ stack (...) for reducing side conditions. *)
val (side_imp_thl: thm list) = [n2w_i2w_eq] |> map stackify_imp_th

val side_imp_tac : tactic = let
  val side_imp_tac_core = stack_imp_tac side_imp_thl
in
  fn (g as (asl, w)) => fn ctxt => let
    val stack = find_term is_stack w
      handle HOL_ERR _ => raise ERR "side_imp_tac" "could not find stack"
    in
    (side_imp_tac_core stack handle e => raise WRAP_EXN "side_imp_tac" e) g ctxt
  end
end

(* "cleaned up" tactic *)

(* Given a term of the form ∃x₁ ... xₙ. t₁ ∧ ... ∧ tₙ, returns
   ([x₁, ..., xₙ], [t₁, ..., tₙ]). *)
fun dest_exists_conj tm =
  let val (evars, rest) = strip_exists tm
  in (evars, strip_conj rest) end

(* Given a list of terms, finds the stack and returns its head. *)
fun get_stack_head tms = let
  val stack = Lib.first is_stack tms
    handle HOL_ERR _ => raise ERR "get_stack_head" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "get_stack_head" "stack is empty"
in head end

(* Returns the first variable from evars that can be unwound using tm.
   This function mirrors check_var from Unwind.sml. *)
fun find_unwind_var (evars: term list) (tm: term) =
  if is_eq tm then let
    val (arg1, arg2) = dest_eq tm in
      if op_mem aconv arg1 (free_vars arg2) orelse
         op_mem aconv arg2 (free_vars arg1)
      then raise ERR "find_unwind_var" "duplicate values"
      else
        (Lib.first (fn e => aconv arg1 e orelse aconv arg2 e) evars
           handle HOL_ERR _ => raise ERR "find_unwind_var" "no value")
    end
  else if is_neg tm andalso List.exists (aconv (dest_neg tm)) evars then
    Lib.first (aconv (dest_neg tm)) evars
  else
    (Lib.first (aconv tm) evars
       handle HOL_ERR _ => raise ERR "find_unwind_var" "no value")

(* Applies UNWIND_EXISTS_CONV to the first (top-level) existential quantifier
   that is equal to tm. *)
fun UNWIND_EXISTS_VAR_CONV v tm =
  if is_exists tm then let
    val (bv, _) = dest_exists tm in
      if aconv bv v then Unwind.UNWIND_EXISTS_CONV tm
      else QUANT_CONV (UNWIND_EXISTS_VAR_CONV v) tm
    end
  else ALL_CONV tm

(* Eliminates existentials that are restricted to a point at the head of the
   stack. *)
val head_unwind : tactic = fn (g as (_, w)) => fn ctxt =>
  let
    val (evars, conjs) = dest_exists_conj w
    val head = get_stack_head conjs
      handle e => raise WRAP_EXN "head_unwind" e
    val target = find_unwind_var evars head
      handle e => raise WRAP_EXN "head_unwind" e
  in
    (irule_at (Pos first_stack) stack_pull
     >> CONV_TAC (UNWIND_EXISTS_VAR_CONV target)) g ctxt
  end

(* Variant of simp that only applies to the stack head for the use in user
   proof-scripts. Makes sure to reduce stack (T::...) and apply unwind for
   existentials. *)
val hsimp : thm list -> tactic = let
  val hsimp_core = head_asm_simp (boss_ss())
in
  fn thl => fn g => fn ctxt =>
    (hsimp_core thl
     >> flatten_head
     >> TRY (head_pop_T ORELSE head_unwind)) g ctxt
end

(* Simplifier used to automatically discharge side-conditions.
   Since it does not fail, it is useful for debugging side. *)
val side_simp =
  head_asm_simp arith_ss [
    v_11, word_lab_11, mlstringTheory.mlstring_11, list_11, NOT_CONS_NIL, CHR_11,
    shape_of_ValWord, shape_of_RStruct_One_One,
    dec_clock_record, panSemTheory.state_accfupds,
    FLOOKUP_UPDATE, (* FLOOKUP_set_var_neq, FLOOKUP_set_var, *) LLOOKUP_def,
    (* ALL_DISTINCT
         (MAP FST [(«xs_len»,One); («xs»,One); («ys»,One); («zs»,One)]) *)
    MAP, ALL_DISTINCT, MEM,
    (* LIST_REL (λvshape arg. SND vshape = shape_of arg)
               [(«xs_len»,One); («xs»,One); («ys»,One); («zs»,One)]
               [ValWord (n2w (LENGTH xs)); ValWord x; ValWord y; ValWord z] *)
    LIST_REL_def,
    (* TODO Could try adding some of these to get rid of hsimp for something like
         n2w (SUC (LENGTH ys)) *)
    (* n2w_11, LESS_MOD, ZERO_MOD, ZERO_LT_dimword, SUC_NOT_ZERO, NOT_CLAUSES   *)
    word_ls_n2w
  ]

(* Attempts to prove side-conditions produced by step. Fails if a
   side-condition cannot be discharged. *)
val side : tactic = fn g => fn ctxt =>
  (side_simp
   >> flatten_head
   >> TRY side_imp_tac
   >> (head_pop_T ORELSE head_unwind)) g ctxt
    handle HOL_ERR _ => raise ERR "side" "failed to discharge side-condition"

(* Tries to apply step or side. *)
val step_or_side : tactic = fn (g as (_, w)) => fn ctxt =>
  ((step ORELSE side) g ctxt)
    handle HOL_ERR _ =>
      raise ERR "step_or_side"
        "Failed to take a step or to discharge a side condition; try step or side."
(*
val step_or_side : tactic = fn (g as (_, w)) => fn ctxt => let
  val is_step =
    case total find_redex w of
      NONE => false
    | SOME redex => is_evaluate redex orelse is_eval redex
in
  (if is_step then step else side) g ctxt
    handle e => raise WRAP_EXN "step_or_side_core" e
end
*)

(* Apply tactic one or more times. *)
fun rpt1 tac : tactic = tac >> rpt tac

(* Takes as many steps as possible, except unfold while-loops. *)
val walk : tactic = fn (g as (asl, w)) => fn ctxt =>
  (rpt1 (step_or_side)) g ctxt handle e => raise WRAP_EXN "walk" e

(*
val g as (asl, w) = top_goal ();
*)

val _ = max_print_depth := 14

(** mw_fix_pan ****************************************************************)

Theorem mw_fix_pan_loop_thm:
  ∀(xs: α word list) rs s x frame.
    mw_fix xs = rs ∧
    LENGTH xs ≤ s.clock ∧  (* LENGTH xs - LENGTH rs would probably be enough *)
    FLOOKUP s.locals «xs_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «xs»    =
      SOME (Val (Word (el_addr x (LENGTH xs) - bytes_in_word))) ∧
    (ones x (MAP Word xs) * frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l clk.
      evaluate (mw_fix_pan_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := clk |>) ∧
      FLOOKUP l «xs_len» = SOME (Val (Word (n2w (LENGTH rs)))) ∧
      (ones x (MAP Word xs) * frame) (fun2set (m, s.memaddrs))
Proof
  simp []
  >> Induct using SNOC_INDUCT
  >> rw [mw_fix_pan_loop_def]
  >- (
    simp [Once evaluate_def, state_component_equality, eval_Var_Local]
    >> once_rewrite_tac [mw_fix_def] >> simp []
  )
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> enter_loop
  >> have ‘SUC (LENGTH xs) < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
         INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then drule >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> walk
  >> hsimp []
  >> walk
  >> gvs [Req0 el_addr_sub]
  >> rename1 ‘el_addr base _’
  >> read_ones_at_auto ‘base’ ‘LENGTH xs’
  >> have ‘(MAP Word (SNOC x xs))❲LENGTH xs❳ = Word x’
  >- simp [EL_MAP, EL_LENGTH_SNOC]
  >> walk
  >> Cases_on ‘x’ >> gvs []
  >> walk
  >> Cases_on ‘n’
  >- (
    (* TODO the following two todos came because I changed head_pop_T to us
       REWR_CONV instead of REWRITE_CONV - I guess the implicit rewrites
       are not applied as often as they used to *)
    rpt (walk >> hsimp [])
    >> once_rewrite_tac [GSYM mw_fix_pan_loop_def]
    >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
    >> gvs [MAP_SNOC, ones_SNOC]
    >> last_x_assum $ qspecl_then [‘s'’, ‘base’] mp_tac
    (* TODO a gadget that takes a theorem and the goal, and tries to
       instantiate the frame? *)
    >> simp [Abbr ‘s'’, dec_clock_def, FLOOKUP_SIMP, i2w_one, n2w_SUC,
             FLOOKUP_res_var_neq]
    >> strip_tac
    >> SEP_F_TAC
    >> strip_tac
    >> fs [stack_def, state_component_equality, mw_fix_snoc_zero,
           AC STAR_ASSOC STAR_COMM]
  )
  >> walk >> hsimp []
  >> simp [stack_def, dec_clock_def, state_component_equality]
  >> qmatch_goalsub_abbrev_tac ‘mw_fix xs'’
  >> have ‘LENGTH (mw_fix xs') = SUC (LENGTH xs)’
  >- simp [Abbr ‘xs'’, Once mw_fix_def]
  >> simp [FLOOKUP_res_var_neq, FLOOKUP_SIMP]
QED

(** mw_and_pan ****************************************************************)

Theorem mw_and_pan_loop_thm_raw[local]:
  ∀(xs: α word list) ys zs rs s x y z frame.
    mw_and xs ys = zs ∧ LENGTH xs ≤ LENGTH ys ∧
    LENGTH rs = LENGTH xs ∧ LENGTH xs ≤ s.clock ∧
    FLOOKUP s.locals «xs_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (mw_and_pan_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH xs |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp [] >> Induct >> rw [mw_and_pan_loop_def]
  >- (simp [Once evaluate_def, state_component_equality, mw_and_def, eval_Var_Local])
  (* TODO make this into a tactic and use it everythwere *)
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> enter_loop
  >> walk
  (* TODO Can we not prove something like this at the beginning for
       everything? *)
  (* TODO I wonder whether the theorems involved in this can have their
       assumptions weakened or conclusions strengthened *)
  >> have ‘SUC (LENGTH xs) < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
      INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then $ qspec_then ‘Word h::MAP Word xs’ assume_tac
    >> SEP_F_TAC >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> hsimp []
  >> walk
  (* TODO Maybe we should have another tactic that reads the first element? *)
  >> fs [ones_def, dec_clock_record] >> SEP_R_TAC
  >> walk
  (* TODO SEP_R_TAC without the Cases seems to just do nothing?
       Maybe it should fail instead, and give a hint?  *)
  >> Cases_on ‘ys’ >> fs [ones_def, dec_clock_record]
  >> SEP_R_TAC >> walk
  >> Cases_on ‘rs’ >> fs [ones_def, dec_clock_record]
  >> SEP_R_TAC
  (* TODO Again a if NONE = NONE/case NONE of NONE => pattern *)
  >> rpt (walk >> hsimp [])
  (* TODO simp [stack_evaluate] could be a tactic. *)
  >> simp [stack_evaluate, Req0 $ GSYM mw_and_pan_loop_def]
  (* Apply induction hypothesis *)
  >> last_x_assum drule >> disch_then drule
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >> disch_then $ qspec_then ‘s'’ mp_tac
  >> simp [Abbr ‘s'’]
  (* TODO If I remember correctly, the qabbrev_tac is required here because
       SEP_W_TAC don't handle records gracefully? *)
  >> qabbrev_tac ‘memory = s.memory’ >> SEP_W_TAC >> simp [Abbr ‘memory’]
  >> simp [FLOOKUP_SIMP, i2w_one, n2w_SUC, dec_clock_def, FLOOKUP_res_var_neq]
  >> strip_tac >> SEP_F_TAC
  >> disch_then $ qx_choosel_then [‘m’, ‘l’] assume_tac
  >> qexistsl [‘m’, ‘l’]
  >> fs [state_component_equality, mw_and_def, AC STAR_ASSOC STAR_COMM, ones_def]
QED

Theorem mw_and_pan_loop_thm[local] =
  SIMP_RULE bool_ss [] mw_and_pan_loop_thm_raw

Theorem mw_and_pan_thm:
  ∀(xs: α word list) ys rs s x y z frame.
    LENGTH xs ≤ LENGTH ys ∧
    LENGTH rs = LENGTH xs ∧ LENGTH xs ≤ s.clock ∧
    FLOOKUP s.locals «xs_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m.
      evaluate (mw_and_pan_body,s) =
        (SOME (Return (ValWord (i2w 0))),
         s with <| memory := m;
                   locals := FEMPTY;
                   clock := s.clock - LENGTH xs |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word (mw_and xs ys)) *
       frame) (fun2set (m, s.memaddrs))
Proof
  rw [mw_and_pan_body_def]
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> walk
  (* TODO Automate this instantation; surely smart people have already
       thought about problems like this *)
  >> qspecl_then [‘xs’, ‘ys’, ‘rs’, ‘s’, ‘x’, ‘y’, ‘z’, ‘frame’]
       mp_tac mw_and_pan_loop_thm
  >> impl_tac >- simp []
  >> strip_tac
  >> hsimp []
  (* TODO again, the walk/hsimp/walk/... pattern *)
  >> rpt (walk >> hsimp [])
  (* TODO Maybe we should have something that computes this? *)
  >> hsimp [size_of_sh_with_ctxt_def, i2w_0, shape_of_ValWord]
  >> simp [stack_def, state_component_equality, empty_locals_def]
QED

(** mwi_and_flip_pan **********************************************************)

Theorem mw_and_flip_pan_thm:
  ∀(xs: α word list) ys rs s x y z frame.
    LENGTH xs + 1 ≤ s.clock ∧ LENGTH ys + 1 ≤ s.clock ∧
    LENGTH rs = MIN (LENGTH xs) (LENGTH ys) ∧
    FLOOKUP s.code «mw_and_pan» = SOME ^mw_and_pan_code ∧
    FLOOKUP s.locals «xs_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l clk.
      evaluate (mw_and_flip_pan_body,s) =
        (SOME (Return (ValWord (n2w (LENGTH (mw_and_flip xs ys))))),
         s with <| memory := m;
                   locals := l;
                   clock := clk |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word (mw_and_flip xs ys)) *
       frame) (fun2set (m, s.memaddrs))
Proof
  rpt strip_tac
  >> have ‘LENGTH xs < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
      INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then $ qspec_then ‘MAP Word xs’ assume_tac
    >> SEP_F_TAC >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> Cases_on ‘LENGTH xs = 0’ >- simp []
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> have ‘LENGTH ys < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
      INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then $ qspec_then ‘MAP Word ys’ assume_tac
    >> SEP_F_TAC >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> Cases_on ‘LENGTH ys = 0’ >- simp []
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> simp [mw_and_flip_pan_body_def]
  >> walk
  >> IF_CASES_TAC >> walk
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >- (
    (* TODO would be nice if the instantiation could be done automatically *)
    qspecl_then [‘xs’, ‘ys’, ‘rs’, ‘s'’, ‘x’, ‘y’, ‘z’, ‘frame’] mp_tac mw_and_pan_thm
    >> impl_tac
    >- simp [Abbr ‘s'’, flookup_fupdate_list, dec_clock_def, MIN_DEF]
    >> strip_tac
    (* TODO again, the walk/hsimp/walk/... pattern *)
    >> rpt (walk >> hsimp [])
    (* TODO Maybe we should have something that computes this? *)
    >> hsimp [size_of_sh_with_ctxt_def, shape_of_ValWord]
    >> gvs [Abbr ‘s'’, stack_def, state_component_equality, empty_locals_def,
            mw_and_flip_def, dec_clock_def, LENGTH_mw_and, MIN_DEF]
  )
  (* TODO would be nice if the instantiation could be done automatically *)
  >> qspecl_then [‘ys’, ‘xs’, ‘rs’, ‘s'’, ‘y’, ‘x’, ‘z’, ‘frame’] mp_tac mw_and_pan_thm
  >> impl_tac
  >- fs [Abbr ‘s'’, flookup_fupdate_list, dec_clock_def, MIN_DEF,
         AC STAR_ASSOC STAR_COMM]
  >> strip_tac
  (* TODO again, the walk/hsimp/walk/... pattern *)
  >> rpt (walk >> hsimp [])
  >> hsimp [size_of_sh_with_ctxt_def, shape_of_ValWord]
  >> gvs [Abbr ‘s'’, stack_def, state_component_equality, empty_locals_def,
          mw_and_flip_def, dec_clock_def, LENGTH_mw_and, MIN_DEF,
          AC STAR_ASSOC STAR_COMM]
QED

(** mwi_and_neg_pos_geq_pan ***************************************************)

Theorem mwi_and_neg_pos_geq_pan_loop_thm:
  ∀(ys: α word list) xs zs rs s c x y z frame.
    LENGTH ys ≤ LENGTH xs ∧ LENGTH rs = LENGTH ys ∧ LENGTH ys ≤ s.clock ∧
    FLOOKUP s.locals «ys_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «c» = SOME (Val (Word (b2w c))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (mwi_and_neg_pos_geq_pan_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH ys |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word (mwi_and_neg_pos_geq c xs ys)) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp [] >> Induct >> rw [mwi_and_neg_pos_geq_pan_loop_def]
  >- (simp [Once evaluate_def, state_component_equality, i2w_def, eval_Var_Local])
  >> rename1 ‘ones _ (Word h::MAP Word _)’
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> enter_loop >> walk
  >> have ‘SUC (LENGTH ys) < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
         INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then $ qspec_then ‘Word h::MAP Word ys’ assume_tac
    >> SEP_F_TAC >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> hsimp []
  >> walk
  >> Cases_on ‘xs’ >> fs [ones_def, dec_clock_record] >> SEP_R_TAC
  >> walk
  >> hsimp [dec_clock_record]
  >> SEP_R_TAC
  (* TODO again, the walk/hsimp/walk/... pattern *)
  >> rpt (walk >> hsimp [])
  >> Cases_on ‘rs’ >> gvs []
  >> fs [ones_def, dec_clock_record] >> SEP_R_TAC >> hsimp []
  (* TODO again, the walk/hsimp/walk/... pattern *)
  >> rpt (walk >> hsimp [])
  >> simp [stack_evaluate]
  >> simp [Req0 $ GSYM mwi_and_neg_pos_geq_pan_loop_def]
  >> rename1 ‘evaluate (mwi_and_neg_pos_geq_pan_loop, _)’
  >> last_x_assum drule
  >> disch_then drule
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >> disch_then $ qspec_then ‘s'’ mp_tac
  >> simp [Abbr ‘s'’]
  >> qabbrev_tac ‘memory = s.memory’
  >> SEP_W_TAC
  >> simp [Abbr ‘memory’]
  >> fs [GSYM b2w_ite, dec_clock_def, FLOOKUP_SIMP, i2w_one, n2w_SUC, FLOOKUP_res_var_neq]
  >> qmatch_goalsub_abbrev_tac ‘b2w (dimword (:α) ≤ r)’
  >> disch_then $ qspec_then ‘dimword (:α) ≤ r’ mp_tac
  >> simp []
  >> strip_tac >> SEP_F_TAC
  >> disch_then $ qx_choosel_then [‘m’, ‘l’] assume_tac
  >> qexistsl [‘m’, ‘l’]
  >> simp [mwi_and_neg_pos_geq_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘single_sub _ 0w _ = (y₂, c₁)’
  >> have ‘(-1w * (n2w r + 1w) = ¬y₂) ∧ (dimword (:α) ≤ r ⇔ c₁)’
  >- (
    drule_then assume_tac single_sub_0w_co
    >> simp [Abbr ‘r’, i2w_minus_1, w2n_minus1, b2w_b2n, GSYM word_add_n2w,
             GSYM b2w_def, WORD_NEG1_MUL_NOT]
  )
  >> fs [ones_def, AC STAR_ASSOC STAR_COMM, n2w_SUC, state_component_equality]
QED

Theorem mwi_and_neg_pos_geq_pan_body_thm:
  ∀(ys: α word list) xs zs rs s c x y z frame.
    LENGTH ys ≤ LENGTH xs ∧ LENGTH rs = LENGTH ys ∧ LENGTH ys ≤ s.clock ∧
    FLOOKUP s.locals «ys_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «c» = SOME (Val (Word (b2w c))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (mwi_and_neg_pos_geq_pan_body,s) = (
        SOME (Return (ValWord (i2w 0))),
        s with <| memory := m;
                  locals := FEMPTY;
                  clock := s.clock - LENGTH ys |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word (mwi_and_neg_pos_geq c xs ys)) *
       frame) (fun2set (m, s.memaddrs))
Proof
  rw [mwi_and_neg_pos_geq_pan_body_def]
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> walk
  >> qspecl_then [‘ys’, ‘xs’, ‘zs’, ‘rs’, ‘s’, ‘c’, ‘x’, ‘y’, ‘z’, ‘frame’]
                 mp_tac mwi_and_neg_pos_geq_pan_loop_thm
  >> simp [] >> strip_tac >> simp []
  >> rpt (walk >> hsimp [])
  >> simp [shape_of_ValWord, size_of_sh_with_ctxt_def, stack_def,
           state_component_equality, empty_locals_def]
QED

(** mwi_and_neg_neg_pan *******************************************************)

Theorem mwi_and_neg_neg_pan_loop0_thm_raw[local]:
  ∀(xs: α word list) ys zs rs rs' s c d e x y z len_written frame.
    LENGTH xs ≤ LENGTH ys ∧
    LENGTH xs ≤ LENGTH rs ∧
    LENGTH xs ≤ s.clock ∧
    rs' =
      MAP Word (TAKE (LENGTH xs) (mwi_and_neg_neg c d e xs ys)) ++
      DROP (LENGTH xs) rs ∧
    FLOOKUP s.locals «c» = SOME (Val (Word (b2w c))) ∧
    FLOOKUP s.locals «d» = SOME (Val (Word (b2w d))) ∧
    FLOOKUP s.locals «e» = SOME (Val (Word (b2w e))) ∧
    FLOOKUP s.locals «xs_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (mwi_and_neg_neg_pan_loop0,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH xs |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z rs' *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp [] >> Induct >> rw [mwi_and_neg_neg_pan_loop0_def]
  >- rw [Once evaluate_def, eval_Var_Local, state_component_equality]
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> have ‘SUC (LENGTH xs) < dimword (:α)’
  >- (
    drule_all_then assume_tac byte_dimindex_leq
    >> drule_then mp_tac $
         INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
    >> disch_then $ qspec_then ‘Word h::MAP Word xs’ assume_tac
    >> SEP_F_TAC >> simp [] >> strip_tac
    >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
    >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
    >> first_assum $ irule_at (Pos last)
    >> simp []
  )
  >> enter_loop
  >> walk >> hsimp []
  >> walk
  >> cheat
QED

Theorem mwi_and_neg_neg_pan_loop0_thm[local] =
  SIMP_RULE bool_ss [] mwi_and_neg_neg_pan_loop0_thm_raw
