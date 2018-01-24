open preamble;
open mlstringTheory mlnumTheory mlintTheory;
open astTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();

val _ = new_theory "infer_t";
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = Datatype `
 infer_t =
    Infer_Tvar_db num
  | Infer_Tapp (infer_t list) tctor
  | Infer_Tuvar num`;

val id_to_string_def = Define `
  (id_to_string (Short s) = implode s) ∧
  (id_to_string (Long x id) =
    concat [implode x; implode "."; id_to_string id])`;

val tc_to_string_def = Define `
  tc_to_string tc =
    case tc of
      TC_name id => id_to_string id
    | TC_int => implode "<int>"
    | TC_char => implode "<char>"
    | TC_string => implode "<string>"
    | TC_ref => implode "<ref>"
    | TC_word8 => implode "<word8>"
    | TC_word64 => implode "<word64>"
    | TC_word8array => implode "<word8array>"
    | TC_exn => implode "<exn>"
    | TC_vector => implode "<vector>"
    | TC_array => implode "<array>"
    | TC_fn => implode "<fn>"
    | TC_tup => implode "<tup>"`;

val inf_type_to_string_def = tDefine "inf_type_to_string" `
  (inf_type_to_string (Infer_Tuvar n) =
    concat [implode "<unification variable "; toString n; implode ">"]) ∧
  (inf_type_to_string (Infer_Tvar_db n) =
    concat [implode "<type variable "; toString n; implode ">"]) ∧
  (inf_type_to_string (Infer_Tapp [t1;t2] TC_fn) =
    concat [implode "("; inf_type_to_string t1; implode " -> "; inf_type_to_string t2; implode ")"]) ∧
  (inf_type_to_string (Infer_Tapp ts TC_fn) =
    implode "<bad function type>") ∧
  (inf_type_to_string (Infer_Tapp ts TC_tup) =
    concat [implode "("; inf_types_to_string ts; implode ")"]) ∧
  (inf_type_to_string (Infer_Tapp [] tc1) =
    tc_to_string tc1) ∧
  (inf_type_to_string (Infer_Tapp [t] tc1) =
    concat [inf_type_to_string t; implode " "; tc_to_string tc1]) ∧
  (inf_type_to_string (Infer_Tapp ts tc1) =
    concat [implode "("; inf_types_to_string ts; implode ") "; tc_to_string tc1]) ∧
  (inf_types_to_string [] =
    implode "") ∧
  (inf_types_to_string [t] =
    inf_type_to_string t) ∧
  (inf_types_to_string (t::ts) =
    concat [inf_type_to_string t; implode ", "; inf_types_to_string ts])`
 (WF_REL_TAC `measure (\x. dtcase x of INL x => infer_t_size x | INR x => infer_t1_size x)`);

val inf_type_to_string_pmatch = Q.store_thm("inf_type_to_string_pmatch",
 `(∀t. inf_type_to_string t =
    case t of
      Infer_Tuvar n =>
      concat [implode "<unification variable "; toString n; implode ">"]
    | Infer_Tvar_db n =>
      concat [implode "<type variable "; toString n; implode ">"]
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

val type_to_string_def = tDefine "type_to_string" `
  (type_to_string (Tvar s) =
    concat [implode "'"; implode s]) ∧
  (type_to_string (Tvar_db n) =
    concat [implode "<type variable "; toString n; implode ">"]) ∧
  (type_to_string (Tapp [t1;t2] TC_fn) =
    concat [implode "("; type_to_string t1; implode " -> "; type_to_string t2; implode ")"]) ∧
  (type_to_string (Tapp ts TC_fn) =
    implode "<bad function type>") ∧
  (type_to_string (Tapp ts TC_tup) =
    concat [implode "("; types_to_string ts; implode ")"]) ∧
  (type_to_string (Tapp [] tc1) =
    tc_to_string tc1) ∧
  (type_to_string (Tapp [t] tc1) =
    concat [type_to_string t; implode " "; tc_to_string tc1]) ∧
  (type_to_string (Tapp ts tc1) =
    concat [implode "("; types_to_string ts; implode ") "; tc_to_string tc1]) ∧
  (types_to_string [] =
    implode "") ∧
  (types_to_string [t] =
    type_to_string t) ∧
  (types_to_string (t::ts) =
    concat [type_to_string t; implode ", "; types_to_string ts])`
 (WF_REL_TAC `measure (\x. dtcase x of INL x => t_size x | INR x => t1_size x)`);

val type_to_string_pmatch = Q.store_thm("type_to_string_pmatch",
 `(∀t. type_to_string t =
    case t of
      Tvar s =>
      concat [implode "'"; implode s]
    | Tvar_db n =>
      concat [implode "<type variable "; toString n; implode ">"]
    | Tapp [t1;t2] TC_fn =>
      concat [implode "("; type_to_string t1; implode " -> "; type_to_string t2; implode ")"]
    | Tapp _ TC_fn => implode "<bad function type>"
    | Tapp ts TC_tup =>
      concat [implode "("; types_to_string ts; implode ")"]
    | Tapp [] tc1 => tc_to_string tc1
    | Tapp [t] tc1 =>
      concat [type_to_string t; implode " "; tc_to_string tc1]
    | Tapp ts tc1 =>
      concat [implode "("; types_to_string ts; implode ") "; tc_to_string tc1]) ∧
 (∀ts. types_to_string ts =
    case ts of
      [] => implode ""
    | [t] => type_to_string t
    | t::ts => concat [type_to_string t; implode ", "; types_to_string ts])`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[type_to_string_def]);

val _ = export_theory ();
