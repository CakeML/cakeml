signature arm8_targetLib =
sig
   val add_arm8_decode_compset: computeLib.compset -> unit
   val add_arm8_encode_compset: computeLib.compset -> unit
   val arm8_encode_decode_conv: Conv.conv
end
