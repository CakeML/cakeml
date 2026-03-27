signature riscv_targetLib =
sig
   val add_riscv_encode_compset: computeLib.compset -> computeLib.compset
   val riscv_encode_conv: Conv.conv
end
