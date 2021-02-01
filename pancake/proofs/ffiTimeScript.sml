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
  get_bytes (:'a) n =
  let m  = dimindex (:'a) DIV 8;
      as = GENLIST (λm. (n2w m): 'a word) m;
      w  = (n2w n):'a word
  in
    MAP (λa. get_byte a w F) as
End


Definition ntime_input_def:
  ntime_input (:'a) (f:num -> num # bool) =
  let
    t = FST (f 0);
    b = if SND (f 0) then 0 else 1
  in
    get_bytes (:'a) t ++
    get_bytes (:'a) b
End

Definition next_ffi_def:
  next_ffi (f:num -> (num # bool)) =
    λn. f (n+1)
End


Definition build_ffi_def:
  build_ffi (:'a) (seq:time_input) io =
     <| oracle    :=
        (λs f conf bytes.
          if s = "get_ffi"
          then Oracle_return (next_ffi f) (ntime_input (:'a) f)
          else Oracle_final FFI_failed)
      ; ffi_state := seq
      ; io_events := io|> : time_input_ffi
End


(*
Definition ntime_input_def:
  ntime_input (f:num -> num # bool) n =
    ((k2mw (n-1) (FST (f 0))):word8 list) ++
    [if SND (f 0) then 0w else 1w]
End
*)

(*
[IO_event "get_ffi" []
               (ZIP
                (bytes,
                 k2mw (LENGTH bytes − 1) (FST (t'.ffi.ffi_state 0)) ++
                      [if SND (t'.ffi.ffi_state 0) then 0w:word8 else 1w]))]
*)

val _ = export_theory();
