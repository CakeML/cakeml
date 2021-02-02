open preamble
     panSemTheory
     multiwordTheory


val _ = new_theory "ffiTime";

val _ = set_grammar_ancestry
        ["panSem",
         "multiword"];

Type time_input = ``:num -> num # bool``

Type time_input_ffi = ``:time_input ffi_state``

Type pan_state = ``:('a, time_input) panSem$state``

Overload k2mw = “multiword$k2mw”


Definition get_bytes_def:
  get_bytes (:'a) be w =
  let m  = dimindex (:'a) DIV 8;
      as = GENLIST (λm. (n2w m): 'a word) m
  in
    MAP (λa. get_byte a w be) as
End


Definition time_input_def:
  time_input (:'a) be (f:num -> num # bool) =
  let
    t = n2w (FST (f 0)):'a word;
    b = if SND (f 0) then 0w else (1w:'a word)
  in
    get_bytes (:'a) be t ++
    get_bytes (:'a) be b
End

Definition next_ffi_def:
  next_ffi (f:num -> (num # bool)) =
    λn. f (n+1)
End


Definition build_ffi_def:
  build_ffi (:'a) be (seq:time_input) io =
     <| oracle    :=
        (λs f conf bytes.
          if s = "get_ffi"
          then Oracle_return (next_ffi f) (time_input (:'a) be f)
          else Oracle_final FFI_failed)
      ; ffi_state := seq
      ; io_events := io|> : time_input_ffi
End

(*
[IO_event "get_ffi" []
               (ZIP
                (bytes,
                 k2mw (LENGTH bytes − 1) (FST (t'.ffi.ffi_state 0)) ++
                      [if SND (t'.ffi.ffi_state 0) then 0w:word8 else 1w]))]
*)

val _ = export_theory();
