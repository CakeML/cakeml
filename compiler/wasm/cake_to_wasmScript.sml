(*
  A compiler from CakeML source to wasmLang and its binary encoding
*)
Theory cake_to_wasm
Ancestors
  stack_to_wasm backend wasm_binary_format

(* CakeML source to wasmLang module *)

Definition cake_to_wasm_def:
  cake_to_wasm c p =
    let (bm,c,p,names) = to_stack c p in
      stack_to_wasm names bm p
End

(* CakeML source to wasmLang module in binary format *)

Definition cake_to_wasm_binary_def:
  cake_to_wasm_binary c p =
    case cake_to_wasm c p of
    | INL err_msg => INL err_msg
    | INR wasm_module =>
    case enc_wasm_module wasm_module of
    | INL err_msg => INL (strlit "wasm encoding failure: " ^ err_msg)
    | INR binary => INR binary
End
