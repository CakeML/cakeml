(*
  This file checks that the CakeML standard basis library passes the
  type inferencer. This file also acts as a test of the type
  inferencer's compset.
*)
open preamble basicComputeLib inferenceComputeLib basisProgTheory

val _ = new_theory "basisTypeCheck"

val cmp = wordsLib.words_compset ()
val basis_def = basisProgTheory.basis_def
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
      basicComputeLib.add_basic_compset
      ],
     computeLib.Defs
      [basis_def
      ],
    computeLib.Tys
    [    ]
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp

val _ = (max_print_depth := 20);

local
  val eval1 = inf_eval ``infer_ds init_config basis
              (init_infer_state
                 <|next_uvar := 0; subst := FEMPTY;
                   next_id := start_type_id|>)``
  val test = ``infertype_prog init_config basis``
    |> (REWRITE_CONV [infertype_prog_def, eval1]
        THENC inf_eval)
in
  val basis_ienv = test |> concl |> rhs |> rand
  val basis_ienv_def = Define `basis_ienv = ^basis_ienv`
  val basis_infer_st = eval1 |> concl |> rhs |> rand
  val basis_infer_st_def = Define `basis_infer_st = ^basis_infer_st`

  val print_types = let
    val x = test |> concl |> rhs
    val _ = if can (match_term ``infer$Success _``) x then () else
            if can (match_term ``infer$Failure _``) x then let
              val msg = x |> rand |> rand |> rand
              in case total stringSyntax.fromHOLstring msg of
                SOME s => failwith ("Type inference failed for basis with message: " ^ s)
                | NONE => failwith "Type inference failed for basis. (Also failed to fully evaluate type inferencer error message)"
            end
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
