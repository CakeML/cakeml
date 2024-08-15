(*
  compset for the pure basis functions.
*)
structure basisComputeLib :> basisComputeLib = struct
open mlstringTheory mlintTheory mloptionTheory

val add_basis_compset = computeLib.extend_compset
  [computeLib.Tys
    [``:mlstring$mlstring``
    ]
  ,computeLib.Defs
    [mlstringTheory.implode_def,
     mlstringTheory.str_def,
     mlstringTheory.concat_thm,
     mlstringTheory.explode_thm,
     mloptionTheory.getOpt_def,
     mlintTheory.toChar_def,
     mlintTheory.maxSmall_DEC_def,
     mlintTheory.padLen_DEC_eq,
     mlintTheory.exp_for_dec_enc_def,
     mlintTheory.num_to_chars_compute,
     mlintTheory.toString_def,
     mlintTheory.num_to_str_def
    ]
  ]

end
