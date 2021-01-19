open preamble
     panSemTheory
     multiwordTheory


val _ = new_theory "ffiTime";

val _ = set_grammar_ancestry
        ["panSem",
         "multiword"];



Type time = ``:num -> num``

Type time_ffi = ``:time ffi_state``

Type time_oracle = ``:string -> time oracle_function``

Type pan_state = ``:('a, time) panSem$state``



Definition time_seq_def:
  time_seq (f:num -> num) =
    ∀n. f n ≤ f (SUC n)
End


Definition nffi_def:
  nffi (f:num -> num) =
   λn. f (n+1)
End

Overload k2mw = “multiword$k2mw”

Definition nffi_def:
  nbytes (f:num -> num) n =
    (k2mw n (f 0)):word8 list
End

(* n = dimindex (:α) DIV 8 *)
Definition build_ffi_def:
  build_ffi (seq:time) =
     <| oracle    :=
        (λs f conf bytes.
          if s = "get_time"
          then Oracle_return (nffi f) (nbytes f (LENGTH bytes))
          else Oracle_final FFI_failed)
      ; ffi_state := seq
      ; io_events := [] |> : time_ffi
End


val _ = export_theory();
