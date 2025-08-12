(*
  A compiler from CakeML source to wasmLang and its binary encoding
*)
Theory cake_to_wasm
Ancestors
  stack_to_wasm backend stack_to_lab wasm_binary_format

(* CakeML source to wasmLang module *)

Definition cake_to_wasm_def:
  cake_to_wasm c p =
    let (bm,c,p,names) = to_stack_0 c p in
      stack_to_wasm names bm p
End

(* CakeML source to wasmLang module in binary format *)

Definition cake_to_wasm_binary_def:
  cake_to_wasm_binary c p =
    case cake_to_wasm c p of
    | INL err_msg => INL err_msg
    | INR wasm_module =>
    case enc_module wasm_module of
    | NONE => INL (strlit "wasm encoding failure")
    | SOME binary => INR binary
End
