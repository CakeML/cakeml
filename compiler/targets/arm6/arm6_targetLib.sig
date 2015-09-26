signature arm6_targetLib =
sig
   val add_arm6_decode_compset: computeLib.compset -> unit
   val add_arm6_encode_compset: computeLib.compset -> unit
   val arm6_encode_decode_conv: Conv.conv
end
