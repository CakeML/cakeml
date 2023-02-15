(*
  Temporary file: A simple (unverified) printer for MCIS
*)
open preamble basis mcisTheory pb_parseTheory graph_basicTheory;
open cfLib basisFunctionsLib;

val _ = new_theory "mcisProg";

val _ = translation_extends "basisProg";

Definition usage_string_def:
  usage_string = strlit "Usage: mcis_encode <LAD format file (pattern)> <LAD format file (target)>\n"
End

val r = translate usage_string_def;

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]`;

val r = translate noparse_string_def;

val _ = translate blanks_def;
val _ = translate graph_basicTheory.tokenize_def;

val _ = translate parse_num_list_def;
val _ = translate insert_def;
val _ = translate parse_edges_def;
val _ = translate parse_lad_toks_def;

val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;
val _ = translate lookup_def;

Theorem check_good_edges_inner_thm:
  check_good_edges_inner u v es ⇔
       case lookup u es of NONE => F | SOME edges => MEMBER v edges
Proof
  fs[check_good_edges_inner_def,MEMBER_INTRO]>>
  metis_tac[]
QED

val _ = translate check_good_edges_inner_thm;

val _ = translate (check_good_edges_def |> SIMP_RULE std_ss [GSYM check_good_edges_inner_def]);
val _ = translate check_good_graph_def;

val parse_lad = (append_prog o process_topdecs) `
  fun parse_lad f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_lad_toks lines of
    None => Inl (noparse_string f "LAD")
  | Some x =>
    if check_good_graph x then
      Inr x
    else Inl ("Input graph fails undirectedness check")))`

val _ = translate k_size_def;
val _ = translate has_mapping_def;
val _ = translate all_has_mapping_def;
val _ = translate one_one_def;
val _ = translate all_one_one_def;
val _ = translate lookup_def;
val _ = translate graph_basicTheory.neighbours_def;

Theorem is_edge_compute:
  is_edge e a b =
  case lookup a e of NONE => F
  | SOME ns => MEMBER b ns
Proof
  simp[graph_basicTheory.is_edge_def]>>
  every_case_tac>>metis_tac[MEMBER_INTRO]
QED

val _ = translate is_edge_compute;

val _ = translate edge_map_def;

val _ = translate COUNT_LIST_AUX_def;
val _ = translate COUNT_LIST_compute;
val _ = translate (graph_basicTheory.not_neighbours_def |> SIMP_RULE std_ss [MEMBER_INTRO]);
val _ = translate not_edge_map_def;
val _ = translate all_full_edge_map_def;

val _ = translate encode_base_def;

Definition log2_def:
  log2 n =
  if n < 2 then 0:num
  else (log2 (n DIV 2))+1
End

val _ = translate log2_def;

(* Just for the sake of translation *)
Theorem LOG2_log2:
  LOG 2 n = log2 n
Proof
  cheat
QED

val _ = translate pbcTheory.negate_def;
val _ = translate iff_and_def;
val _ = translate iff_or_def;
val _ = translate walk_base_def;
val _ = translate walk_aux_def;
val _ = translate walk_ind_def;
val _ = translate walk_k_def;

val _ = translate (encode_connected_def |> SIMP_RULE std_ss [LOG2_log2])

val _ = translate encode_def;

(* Translate the string converter *)
val res = translate enc_string_def;

val _ = translate pbcTheory.map_lit_def;
val _ = translate pbcTheory.map_pbc_def;
val _ = translate full_encode_def;


Definition print_pbf_def:
  print_pbf f = MAP pbc_string f
End

val res = translate lit_string_def;
val res = translate lhs_string_def;
val res = translate pbc_string_def;
val res = translate enc_string_def;
val res = translate print_pbf_def;

val _ = (append_prog o process_topdecs) `
  fun print_list ls =
    case ls of [] => () | (x::xs) => (print x; print"\n"; print_list xs)`

val enc_and_print = (append_prog o process_topdecs) `
  fun enc_and_print f1 f2 =
  case parse_lad f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr pattern =>
  (case parse_lad f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr target =>
    print_list (print_pbf (full_encode pattern target 0))
  )`

val top = (append_prog o process_topdecs) `
  fun top u =
  case CommandLine.arguments () of
    [f1,f2] => enc_and_print f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

Theorem top_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 top_v cl fs NONE (λfs'. ∃err. fs' = foo)
Proof
  cheat
QED

local

val name = "top"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH top_whole_prog_spec2)
val top_prog_def = Define`top_prog = ^prog_tm`;

in

Theorem top_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM top_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

val _ = export_theory();