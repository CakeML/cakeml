(*
  Bignum and operation implementation in Pancake
*)
Theory bignum_and
Ancestors
  errorLogMonad panPtreeConversion panStatic multiword multiword_ext
  set_sep address panSem
Libs
  stringLib numLib intLib preamble helperLib

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

(** Copied from panPtreeConversion *)
fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_topdecs_to_ast ^code” |> concl |> rand |> rand |> rator |> rand
  end


Quote and_pos_pos = parse_pancake:
  fun and_pos_pos (x_len, x, y, z) {
    while (x_len != 0) {
      var t1 = lds 1 x;
      var t2 = lds 1 y;
      var t3 = t1 && t2;
      st z, t3;
      x_len = x_len - 1;
    }
    return x;
  }
End

Definition and_pos_pos_loop_def:
  and_pos_pos_loop =
    ^(find_term (can $ match_term “panLang$While _ _”) and_pos_pos)
End

Definition one_list_def:
  one_list a [] = emp ∧
  one_list a (x::xs) = one (a,x) * one_list (a + bytes_in_word) xs
End

Theorem eval_Const[simp]:
  eval s (Const w) = SOME (ValWord w)
Proof
  simp [eval_def]
QED

Theorem eval_Var_Local[simp]:
  eval s (Var Local n) = FLOOKUP s.locals n
Proof
  simp [eval_def]
QED

Theorem evaluate_Annot[simp]:
  evaluate (Annot s₁ s₂, s) = (NONE, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot[simp]:
  evaluate (Seq (Annot s₁ s₂) c, s) = evaluate (c, s) ∧
  evaluate (Seq c (Annot s₁ s₂), s) = evaluate (c, s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> simp []
QED

Theorem evaluate_Seq_assoc[simp]:
  evaluate (Seq (Seq s₁ s₂) (Seq s₃ s₄), s) =
  evaluate (Seq s₁ (Seq s₂ (Seq s₃ s₄)), s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rpt (IF_CASES_TAC >> gvs [])
QED

Theorem dec_clock_eq[simp]:
  (dec_clock s).locals = s.locals ∧
  (dec_clock s).memaddrs = s.memaddrs ∧
  (dec_clock s).memory = s.memory
Proof
  simp [dec_clock_def]
QED

Theorem evaluate_While_True_NONE:
  eval s e = SOME (ValWord w) ∧ w ≠ 0w ∧ s.clock ≠ 0 ∧
  evaluate (c, dec_clock s) = (NONE, s₁) ∧
  evaluate (While e c, s₁) = (NONE, s')
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_Dec_NONE:
  eval s e = SOME value ∧
  evaluate (prog,s with locals := s.locals |+ (v,value)) = (NONE,s₁)
  ⇒
  evaluate (Dec v shape e prog, s) =
    (NONE, s₁ with locals := res_var s₁.locals (v, FLOOKUP s.locals v))
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_Seq_NONE:
  evaluate (c₁, s) = (NONE, s₁) ∧
  evaluate (c₂, s₁) = (NONE, s')
  ⇒
  evaluate (Seq c₁ c₂, s) = (NONE, s')
Proof
  rw [] >> simp [evaluate_def]
QED

Theorem eval_Op_And_SOME:
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op And [x₁; x₂]) = SOME (ValWord (v₁ && v₂))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED

Theorem eval_Op_Sub_SOME:
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Sub [x₁; x₂]) = SOME (ValWord (v₁ - v₂))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED

Theorem eval_Cmp_NotEqual_SOME:
  eval s e₁ = SOME (ValWord v₁) ∧
  eval s e₂ = SOME (ValWord v₂)
  ⇒
  eval s (Cmp NotEqual e₁ e₂) = SOME (ValWord (if v₁ ≠ v₂ then 1w else 0w))
Proof
  simp [eval_def, asmTheory.word_cmp_def]
QED

Theorem evaluate_Store_Local_Local_Val:
  FLOOKUP s.locals dst = SOME (ValWord addr) ∧
  FLOOKUP s.locals src = SOME (Val v) ∧
  addr ∈ s.memaddrs
  ⇒
  evaluate (Store (Var Local dst) (Var Local src), s) =
    (NONE, s with memory := s.memory⦇addr ↦ v⦈)
Proof
  simp [evaluate_def, flatten_def, mem_stores_def, mem_store_def]
QED

Theorem evaluate_Assign_Local:
  eval s src = SOME value ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of value = shape_of old_value
  ⇒
  evaluate ((Assign Local dst src), s) = (NONE, set_var dst value s)
Proof
  simp [evaluate_def, is_valid_value_def]
QED

Theorem and_pos_pos_thm:
  ∀xs ys zs rs x y z frame s s1.
    mw_and xs ys = zs ∧ LENGTH xs ≤ LENGTH ys ∧
    LENGTH rs = LENGTH xs ∧ LENGTH xs ≤ s.clock ∧
    FLOOKUP s.locals (strlit "x_len") = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals (strlit "x") = SOME (Val (Word x)) ∧
    FLOOKUP s.locals (strlit "y") = SOME (Val (Word y)) ∧
    FLOOKUP s.locals (strlit "z") = SOME (Val (Word z)) ∧
    (one_list x (MAP Word xs) *
     one_list y (MAP Word ys) *
     one_list z rs *
     frame) (fun2set (s.memory, s.memaddrs))
    ⇒
    ∃m l.
      evaluate (and_pos_pos_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH xs |>) ∧
      (one_list x (MAP Word xs) *
       one_list y (MAP Word ys) *
       one_list z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp []
  >> Induct >> rw [mw_and_def]
  >-
   (simp [and_pos_pos_loop_def]
    >> simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
    >> simp [state_component_equality])
  >> simp [and_pos_pos_loop_def]

  >> irule_at (Pos hd) evaluate_While_True_NONE
  >> simp [eval_def, asmTheory.word_cmp_def]
  >> ‘SUC (LENGTH xs) < dimword (:α)’ by cheat
  >> simp []

  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> simp [eval_def, mem_load_def]
  >> fs [one_list_def] >> SEP_R_TAC
  >> simp []

  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> simp [eval_def, mem_load_def]
  >> simp [FLOOKUP_SIMP]
  >> Cases_on ‘ys’ >> gvs []
  >> fs [one_list_def] >> SEP_R_TAC
  >> simp []

  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Op_And_SOME
  >> irule_at (Pos hd) eval_Cmp_NotEqual_SOME
  >> simp [FLOOKUP_SIMP]

  >> irule_at (Pos hd) eval_Cmp_NotEqual_SOME
  >> simp [FLOOKUP_SIMP]

  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Store_Local_Local_Val
  >> simp [FLOOKUP_SIMP]
  >> Cases_on ‘rs’ >> gvs []
  >> fs [one_list_def] >> SEP_R_TAC
  >> simp []

  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Sub_SOME
  >> simp [FLOOKUP_SIMP, shape_of_def]

  >> simp [GSYM and_pos_pos_loop_def]

  >> cheat
QED

(*
  SEP_R_TAC
  SEP_W_TAC
  SEP_F_TAC
*)
