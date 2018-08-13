(*
  compset for the pure basis functions.
*)
structure basisComputeLib :> basisComputeLib = struct
open mlstringTheory mlintTheory

val add_basis_compset = computeLib.extend_compset
  [computeLib.Tys
    [``:mlstring$mlstring``
    ]
  ,computeLib.Defs
    [mlstringTheory.implode_def,
     mlstringTheory.str_def,
     mlstringTheory.concat_thm,
     mlstringTheory.explode_thm,
     mlintTheory.zero_pad_def,
     mlintTheory.toChar_def,
     mlintTheory.simple_toChars_def,
     mlintTheory.maxSmall_DEC_def,
     mlintTheory.padLen_DEC_eq,
     mlintTheory.toChars_def,
     mlintTheory.toString_def,
     mlnumTheory.toString_def,
     mlnumTheory.num_toString_def,
     mlnumTheory.fromString_def,
     mlnumTheory.fromString_unsafe_def
    ]
  ]

end
