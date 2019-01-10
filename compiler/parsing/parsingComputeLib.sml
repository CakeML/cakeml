(*
  compset for the lexer and parser.
*)
structure parsingComputeLib :> parsingComputeLib =
struct

open HolKernel boolLib bossLib
open cmlParseTheory cmlPEGTheory lexer_implTheory lexer_funTheory astUtilsTheory

structure Parse =
struct
  open Parse
  val (Type,Term) =
      parse_from_grammars (merge_grammars ["cmlPEG", "lexer_impl"])
end
open Parse

val add_parsing_compset =
    computeLib.extend_compset [
      computeLib.Defs
        [bindNT0_def
        ,bindNT_def
        ,choicel_def
        ,cmlPEG_exec_thm
        ,cmlParseExpr_def
        ,destResult_def
        ,mkNd_def
        ,mk_linfix_def
        ,mk_rinfix_def
        ,mktokLf_def
        ,parse_prog_def
        ,peg_EbaseParenFn_def
        ,peg_EbaseParen_def
        ,peg_StructName_def
        ,peg_TypeDec_def
        ,peg_UQConstructorName_def
        ,peg_V_def
        ,peg_linfix_def
        ,peg_longV_def
        ,pegf_def
        ,pnt_def
        ,ptPapply0_def
        ,ptPapply_def
        ,seql_def
        ,sumID_def
        ,tokeq_def
        ,try_def
        ],
      computeLib.Defs [
        pegexecTheory.applykont_thm,
        pegexecTheory.peg_exec_thm,
        pegexecTheory.poplistval_def,
        pegexecTheory.poplist_aux_def
      ]
    ]


fun limit n cs t =
    let
      open computeLib
      val c = ref n
      fun stop t = if !c <= 0 then true else (c := !c - 1; false)
    in
      with_flag(stoppers, SOME stop) (CBV_CONV cs) t
    end


fun parsing_compset() = let
  val cs = listLib.list_compset()
in
  List.app (fn f => f cs) [
    combinLib.add_combin_compset,
    stringLib.add_string_compset,
    optionLib.OPTION_rws,
    pairLib.add_pair_compset,
    computeLib.extend_compset [
      computeLib.Tys [“:tokens$token”]
    ],
    computeLib.add_thms
      [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY],
    computeLib.add_thms [
      grammarTheory.ptree_list_loc_def,
      grammarTheory.ptree_loc_def,
      locationTheory.merge_list_locs_def,
      locationTheory.merge_locs_def,
      locationTheory.unknown_loc_def
    ],
    semanticsComputeLib.add_tokenUtils_compset,
    add_parsing_compset
  ];
  cs
end;


val parse_t =
  Lib.with_flag (Feedback.MESG_outstream, (fn s => ()))
   Parse.Term
     `\inputnt sem s.
        case
          peg_exec cmlPEG (nt (mkNT inputnt) I) (lexer_fun s) [] done failed
        of
          Result (SOME([],[x])) => sem x : 'a
        | Result (SOME (toks, _)) =>
            ARB (ARB "Parse failed with remaining tokens" toks)
        | _ => ARB "Parse failed"`

fun string_of_q [] = ""
  | string_of_q (QUOTE s :: qs) = s ^ (string_of_q qs)
  | string_of_q (ANTIQUOTE s :: qs) = s ^ (string_of_q qs)

(* ultimate objective: val EVAL = computeLib.CBV_CONV parsing_compset *)
fun parse nt sem q =
  let
    val (_,r) = dom_rng (type_of sem)
  in
    EVAL (list_mk_comb(inst [alpha |-> r] parse_t,
                       [nt, sem, stringSyntax.fromMLstring (string_of_q q)]))
         |> concl |> rhs |> rand
  end

val parse_exp = parse ``nE`` ``OPTION_MAP remove_lannots o ptree_Expr nE``
val parse_decl = parse ``nDecl`` ``OPTION_MAP remove_decl_lannots o ptree_Decl``
val parse_topdecs =
    parse ``nTopLevelDecs`` ``OPTION_MAP remove_decl_lannots o ptree_TopLevelDecs``


end
