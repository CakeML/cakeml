signature mips_targetLib =
sig
   val add_mips_decode_compset: computeLib.compset -> unit
   val add_mips_encode_compset: computeLib.compset -> unit
   val mips_encode_decode_conv: Conv.conv
end
