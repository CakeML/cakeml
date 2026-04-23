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
  \\ Induct \\ rw [mw_and_def]
  >-
   (simp [and_pos_pos_loop_def]
    \\ simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
    \\ simp [state_component_equality])
  \\ simp [and_pos_pos_loop_def]
  \\ simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
  \\ simp [GSYM and_pos_pos_loop_def]
  \\ ‘SUC (LENGTH xs) < dimword (:α)’ by cheat
  \\ gvs []
  \\ cheat
QED

(*
  SEP_R_TAC
  SEP_W_TAC
  SEP_F_TAC
*)
