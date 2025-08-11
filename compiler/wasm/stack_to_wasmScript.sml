(*
  Compilation from stackLang to wasmLang
*)
Theory stack_to_wasm
Ancestors
  wasmLang stackLang words arithmetic list rich_list sptree mlstring
Libs
  wordsLib

Definition stack_to_wasm_def:
  stack_to_wasm ( names          : mlstring spt )
                ( read_only_data : word64 list )
                ( prog           : (num # 64 stackLang$prog) list )
  =
    INR <| funcs   := []
         ; mems    := []
         ; globals := []
         ; start   := 0w |> : mlstring + wasmLang$module
End
