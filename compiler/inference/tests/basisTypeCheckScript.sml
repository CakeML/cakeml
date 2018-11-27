(*
  This file checks that the CakeML standard basis library passes the
  type inferencer. This file also acts as a test of the type
  inferencer's compset.
*)
open preamble basicComputeLib inferenceComputeLib basisProgTheory

val _ = new_theory "basisTypeCheck"

(* A simple test for the inferencer, precomputes the basis config, but doesn't store it as a constant *)
val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
      basicComputeLib.add_basic_compset
      ],
     computeLib.Defs
      [basisProgTheory.basis_def
      ],
    computeLib.Tys
    [    ]
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp

val test = inf_eval ``infertype_prog init_config basis``

val infertype_prog_succeeds = Q.store_thm("infertype_prog_succeeds",
  `∃s. infertype_prog init_config basis = Success s`,
  simp [test]);

val _ = export_theory ();
