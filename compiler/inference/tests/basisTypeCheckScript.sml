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

local
  val test = inf_eval ``infertype_prog init_config basis``
in
  val print_types = let
    val x = test |> concl |> rhs
    val _ = if can (match_term ``infer$Success _``) x then () else
            if can (match_term ``infer$Failure _``) x then let
              val msg = x |> rand |> rand |> rand |> stringSyntax.fromHOLstring
              in failwith ("Type inference failed for basis with message: " ^ msg) end handle HOL_ERR _ => failwith "Type inference failed for basis. (Also failed to fully evaluate type inferencer error message)"
            else failwith "Failed to fully evaluate type inferencer applied to basis."
    val _ = print "\nTypes of all basis functions:\n\n"
    val x = x |> rand
    val strs = EVAL ``inf_env_to_types_string ^x``
                 |> concl |> rand |> listSyntax.dest_list |> fst
                 |> map (stringSyntax.fromHOLstring o rand) |> map print
    val _ = print "\n"
    in () end
end

val _ = export_theory ();
