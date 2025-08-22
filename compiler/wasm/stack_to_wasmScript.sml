(*
  Compilation from stackLang to wasmLang
*)
Theory stack_to_wasm
Ancestors
  wasmLang stackLang words arithmetic list rich_list sptree mlstring
Libs
  wordsLib

Definition mk_func_def:
  mk_func ftype_index locals instrs func_name local_names =
    <| ftype  := ftype_index
     ; locals := locals
     ; body   := instrs
     ; fname  := func_name
     ; lnames := local_names
   |>
End

Definition stack_to_wasm_def:
  stack_to_wasm ( names          : mlstring spt )
                ( read_only_data : word64 list )
                ( prog           : (num # 64 stackLang$prog) list )
  =
    INR <| types   := [([],[])]
         ; funcs   := [mk_func 0w [] [Nop; Unreachable] (strlit "cake_start") []]
         ; mems    := [Lwmx 0w 16w]
         ; globals := []
         ; datas   := [] |> : mlstring + wasmLang$module
End

