(*
  Compilation from stackLang to wasmLang
*)
Theory stack_to_wasm
Ancestors
  wasmLang stackLang words arithmetic list rich_list sptree mlstring
Libs
  wordsLib

Definition mk_func_def:
  mk_func ftype_index locals instrs =
    <| ftype  := ftype_index
     ; locals := locals
     ; body   := instrs
   |>
End

Definition stack_to_wasm_def:
  (* Chris: MM added "names" but it's not used in the function? *)
  (* stack_to_wasm ( names          : mlstring spt ) *)
  stack_to_wasm
                ( read_only_data : word64 list )
                ( prog           : (num # 64 stackLang$prog) list )
  =
    INR <| types   := [([],[])]
         ; funcs   := [mk_func 0w [] [Nop; Unreachable]]
         ; mems    := [Lwmx 0w 16w]
         ; globals := []
         ; datas   := [] |> : mlstring + wasmLang$module
End

