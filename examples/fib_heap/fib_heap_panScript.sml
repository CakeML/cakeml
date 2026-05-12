(*
  fib_heap merge implementation in Pancake
*)
Theory fib_heap_pan
Ancestors
  errorLogMonad panPtreeConversion panStatic set_sep address panSem fibonacci_heap
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


Quote melt_pan = parse_pancake:
  fun 1 melt (1 a1, 1 a2) {
    if (a2 == 0) {return a1;} else {}
    if (a1 == 0) {return a2;} else {}
    return a1;
  }
End


Definition merge_body_def:
  merge_body =
    ^(find_term (can $ match_term “panLang$Seq _ _”) merge_pan)
End


(*
Definition one_list_def:
  one_list a [] = emp ∧
  one_list a (x::xs) = one (a,x) * one_list (a + bytes_in_word) xs
End
*)

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

Theorem dec_clock_eq[simp]:
  (dec_clock s).locals = s.locals ∧
  (dec_clock s).memaddrs = s.memaddrs ∧
  (dec_clock s).memory = s.memory
Proof
  simp [dec_clock_def]
QED




(* Theorem evaluate_Dec: *)
(*   eval s e = SOME value ⇒ *)
(*   evaluate (Dec v shape e prog, s) = *)
(*   let (res,st) = evaluate (prog,s with locals := s.locals |+ (v,value)) in *)
(*     (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v)) *)
(* Proof *)
(*   simp [evaluate_def] *)
(* QED *)

(* Theorem evaluate_While_True_NONE: *)
(*   eval s e = SOME (ValWord w) ∧ w ≠ 0w ∧ s.clock ≠ 0 ∧ *)
(*   evaluate (c, dec_clock s) = (NONE, s₁) *)
(*   ⇒ *)
(*   (evaluate (While e c,s) = (NONE, s') ⇔ *)
(*    evaluate (While e c, s₁) = (NONE, s')) *)
(* Proof *)
(*   rw [Once evaluate_def] *)
(* QED *)
(*
Theorem and_pos_pos_thm:
  ∀xs ys zs rs x y z dm m frame s s1.
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
  >> simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
  >> simp [GSYM and_pos_pos_loop_def]
  >> ‘SUC (LENGTH xs) < dimword (:α)’ by cheat
  >> gvs []
  >> simp [Once evaluate_def, eval_def]
  >> cheat
QED
*)
(*
  SEP_R_TAC
  SEP_W_TAC
  SEP_F_TAC
*)

(*

Theorem melt_pan_thm:
  ∀a1 a2 dm m frame s.
    fib_heap_melt (a1,a2,m,dm) = (a',m',T) /\
    FLOOKUP s.locals (strlit "a1") = SOME (Val (Word a1)) ∧
    FLOOKUP s.locals (strlit "a2") = SOME (Val (Word a2)) ∧
    m = s.memory /\ dm = s.memaddrs
    ⇒
    ∃l.
      evaluate (merge_body,s) = (NONE,
        s with <| memory := m';
                  locals := l |>)
Proof
  cheat
QED

*)
