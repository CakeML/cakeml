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

val add_parsing_compset = computeLib.extend_compset
  [computeLib.Defs
    [destResult_def
    (* ,parse_top_def
       ,cmlParseREPLTop_def *)
    ,cmlParseExpr_def
    ,sumID_def
    ,tokeq_def
    ,cmlPEG_exec_thm
    ,peg_StructName_def
    ,peg_EbaseParen_def
    ,peg_EbaseParenFn_def
    ,peg_longV_def
    ,peg_V_def
    ,peg_TypeDec_def
    ,peg_UQConstructorName_def
    ,pnt_def
    ,try_def
    ,pegf_def
    ,seql_def
    ,choicel_def
    ,mktokLf_def
    ,bindNT_def
    ,peg_linfix_def
    ,mk_linfix_def
    ,mk_rinfix_def
    ,parse_prog_def
    ],
   computeLib.Defs [
     lex_until_toplevel_semicolon_def ,
     get_token_eqn ,
     lex_aux_def
   ],
   computeLib.Defs [ (* lexer_funTheory *)
     lexer_fun_def,
     lexer_fun_aux_def,
     next_token_def,
     next_sym_def,
     read_while_def,
     read_string_def,
     isSymbol_def,
     isAlphaNumPrime_def,
     is_single_char_symbol_def,
     init_loc_def,
     pred_setTheory.IN_INSERT,
     pred_setTheory.NOT_IN_EMPTY,
     token_of_sym_def
    ],
   computeLib.Tys [``:locn``, ``:locs``, ``:symbol``, ``:token``]
  ]


fun limit n cs t =
    let
      open computeLib
      val c = ref n
      fun stop t = if !c <= 0 then true else (c := !c - 1; false)
    in
      with_flag(stoppers, SOME stop) (CBV_CONV cs) t
    end


val parsing_compset = let
  val cs = listLib.list_compset()
in
  combinLib.add_combin_compset cs;
  stringLib.add_string_compset cs;
  optionLib.OPTION_rws cs;
  pairLib.add_pair_compset cs;
  add_parsing_compset cs;
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
