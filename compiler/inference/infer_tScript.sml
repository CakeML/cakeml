(*
  The infer_t datatype and various to_string functions.
*)
open preamble;
open mlstringTheory mlintTheory;
open astTheory semanticPrimitivesTheory typeSystemTheory;

val _ = numLib.prefer_num();

val _ = new_theory "infer_t";
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = Datatype `
 infer_t =
    Infer_Tvar_db num
  | Infer_Tapp (infer_t list) type_ident
  | Infer_Tuvar num`;

val id_to_string_def = Define `
  (id_to_string (Short s) = implode s) ∧
  (id_to_string (Long x id) =
    concat [implode x; implode "."; id_to_string id])`;

val type_ident_to_string_def = Define `
  type_ident_to_string ti =
  if ti = Tarray_num then
    implode "<array>"
  else if ti = Tbool_num then
    implode "<bool>"
  else if ti = Tchar_num then
    implode "<char>"
  else if ti = Texn_num then
    implode "<exn>"
  else if ti = Tint_num then
    implode "<int>"
  else if ti = Tlist_num then
    implode "<list>"
  else if ti = Tref_num then
    implode "<ref>"
  else if ti = Tstring_num then
    implode "<string>"
  else if ti = Tvector_num then
    implode "<vector>"
  else if ti = Tword64_num then
    implode "<word64>"
  else if ti = Tword8_num then
    implode "<word8>"
  else if ti = Tword8array_num then
    implode "<word8array>"
  else
    toString (&ti)`;

(* TODO: update for pretty printing *)

val inf_type_to_string_def = tDefine "inf_type_to_string" `
  (inf_type_to_string (Infer_Tuvar n) =
    concat [implode "<unification variable "; toString (&n); implode ">"]) ∧
  (inf_type_to_string (Infer_Tvar_db n) =
    concat [implode "<type variable "; toString (&n); implode ">"]) ∧
  (inf_type_to_string (Infer_Tapp ts ti) =
    if ti = Tfn_num then
      case ts of
      | [t1; t2] =>
        concat [implode "("; inf_type_to_string t1; implode " -> ";
                inf_type_to_string t2; implode ")"]
      | _ => implode "<bad function type>"
    else if ti = Ttup_num then
      concat [implode "("; inf_types_to_string ts; implode ")"]
    else
      case ts of
      | [] => type_ident_to_string ti
      | [t] =>
        concat [inf_type_to_string t; implode " "; type_ident_to_string ti]
      | _ =>
        concat [implode "("; inf_types_to_string ts; implode ") ";
                type_ident_to_string ti]) ∧
  (inf_types_to_string [] =
    implode "") ∧
  (inf_types_to_string [t] =
    inf_type_to_string t) ∧
  (inf_types_to_string (t::ts) =
    concat [inf_type_to_string t; implode ", "; inf_types_to_string ts])`
 (WF_REL_TAC `measure (\x. dtcase x of INL x => infer_t_size x | INR x => infer_t1_size x)`);

 (*
val inf_type_to_string_pmatch = Q.store_thm("inf_type_to_string_pmatch",
 `(∀t. inf_type_to_string t =
    case t of
      Infer_Tuvar n =>
      concat [implode "<unification variable "; toString (&n); implode ">"]
    | Infer_Tvar_db n =>
      concat [implode "<type variable "; toString (&n); implode ">"]
    | Infer_Tapp [t1;t2] TC_fn =>
      concat [implode "("; inf_type_to_string t1; implode " -> "; inf_type_to_string t2; implode ")"]
    | Infer_Tapp _ TC_fn => implode "<bad function type>"
    | Infer_Tapp ts TC_tup =>
      concat [implode "("; inf_types_to_string ts; implode ")"]
    | Infer_Tapp [] tc1 => tc_to_string tc1
    | Infer_Tapp [t] tc1 =>
      concat [inf_type_to_string t; implode " "; tc_to_string tc1]
    | Infer_Tapp ts tc1 =>
      concat [implode "("; inf_types_to_string ts; implode ") "; tc_to_string tc1]) ∧
 (∀ts. inf_types_to_string ts =
    case ts of
      [] => implode ""
    | [t] => inf_type_to_string t
    | t::ts => concat [inf_type_to_string t; implode ", "; inf_types_to_string ts])`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[inf_type_to_string_def]);
  *)

val _ = export_theory ();
