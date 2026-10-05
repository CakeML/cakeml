(*
  Parse and print for multi-objective pbc problems
*)
Theory pb_parse_mo
Ancestors
  pbc pb_parse
Libs
  preamble

val _ = numLib.temp_prefer_num();

(* Multi-objective problem: one min: line per objective, then the constraints *)
Definition print_mo_prob_def:
  print_mo_prob (objs,fml) =
  MAP obj_string objs ++ MAP pbc_string fml
End

(* parse a run of objective lines *)
Definition parse_objs_maybe_def:
  (parse_objs_maybe [] acc = (REVERSE acc, [])) ∧
  (parse_objs_maybe (l::ls) acc =
  case parse_obj l of
    NONE => (REVERSE acc, l::ls)
  | SOME obj => parse_objs_maybe ls (obj::acc))
End

(* Parse the tokenized multi-objective pbf file *)
Definition parse_mo_pbf_toks_def:
  parse_mo_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  let (objs,rest) = parse_objs_maybe nocomments [] in
  case parse_constraints rest [] of
    NONE => NONE
  | SOME pbf => SOME (objs, MAP SND pbf)
End

(* Parse a list of strings in multi-objective pbf format *)
Definition parse_mo_pbf_def:
  parse_mo_pbf strs = parse_mo_pbf_toks (MAP toks strs)
End
