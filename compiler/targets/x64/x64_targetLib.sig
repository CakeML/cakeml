signature x64_targetLib =
sig
   val add_x64_datatypes: computeLib.compset -> unit
   val add_x64_decode_compset: computeLib.compset -> unit
   val add_x64_encode_compset: computeLib.compset -> unit
   val x64_encode_decode_conv: Conv.conv
end
