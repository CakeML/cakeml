(*
  Tests of compset for evaluating various functions in cmlPtreeConversion.
*)
open preamble
open cmlPtreeConversionTheory
open testutils semanticsComputeLib


val _ = new_theory "cmlPtreeTests"

fun limit n cs t =
    let
      open computeLib
      val c = ref n
      fun stop t = if !c <= 0 then true else (c := !c - 1; false)
    in
      with_flag(stoppers, SOME stop) (CBV_CONV cs) t
    end

val add_grammar_compset =
    computeLib.extend_compset [
      computeLib.Tys [“:(α,β,γ) grammar$parsetree”]
    ]

val compset = let
  val cs = listLib.list_compset()
in
  stringLib.add_string_compset cs;
  pairLib.add_pair_compset cs;
  optionLib.OPTION_rws cs;
  combinLib.add_combin_compset cs;
  add_grammar_compset cs;
  add_gram_compset cs;
  add_tokenUtils_compset cs;
  add_cmlPtreeConversion_compset cs;
  cs
end

fun test (t_in,t_expected) =
    (tprint ("Converting " ^ term_to_string t_in);
     require_msg (check_result (aconv t_expected)) term_to_string
                 (rhs o concl o limit 1000 compset)
                 t_in)

val _ = temp_overload_on ("L", ``Locs (locn 0 0 0) (locn 0 0 0)``)

val _ = temp_overload_on ("simpleTyop",
                          “λs. Nd (mkNT nType, L) [
                            Nd (mkNT nPType, L) [
                              Nd (mkNT nDType, l) [
                                Nd (mkNT nTbase, L) [
                                  Nd (mkNT nTyOp, L) [
                                    Nd (mkNT nUQTyOp, L) [
                                      Lf (TK (AlphaT s), L)
                                    ]
                                  ]
                                ]
                              ]
                            ]
                          ]”)

val _ = app (ignore o test) [
      (“ptree_Type nType (simpleTyop "int")”, “SOME (Atapp [] (Short "int"))”),
      (“ptree_Type nType (
          Nd (mkNT nType,L) [
            Nd (mkNT nPType,L) [
              Nd (mkNT nDType,L) [
                Nd (mkNT nDType,L) [
                  Nd (mkNT nTbase,L) [Lf (TK (TyvarT "'a"),L)]
                ];
                Nd (mkNT nTyOp,L) [
                  Nd (mkNT nUQTyOp,L) [Lf (TK (AlphaT "list"),L)]
                ]
              ]
            ]
          ]
        )”, “SOME (Atapp [Atvar "'a"] (Short "list"))”),
      (“ptree_Expr nEbase (
          Nd (mkNT nEbase,L) [Nd (mkNT nEliteral,L) [Lf (TK (IntT 15),L)]]
        )”,
       “SOME (Lannot (Lit (IntLit 15)) L)”)
    ]

val _ = export_theory()
