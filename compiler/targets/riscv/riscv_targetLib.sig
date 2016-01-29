signature riscv_targetLib =
sig
   val add_riscv_decode_compset: computeLib.compset -> unit
   val add_riscv_encode_compset: computeLib.compset -> unit
   val riscv_encode_decode_conv: Conv.conv
end
