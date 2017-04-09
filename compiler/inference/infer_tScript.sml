open HolKernel Parse boolLib bossLib;
open mlstringTheory mlintTheory;
open astTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();

val _ = new_theory "infer_t"

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
  tc =
    Case tc of
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

val inf_type_to_string_def = Define `
  (inf_type_to_string (Infer_Tuvar _) =
    implode "<unification variable>") ∧
  (inf_type_to_string (Infer_Tvar_db n) =
    toString (&n)) ∧
  (inf_type_to_string (Infer_Tapp [t1;t2] TC_fn) =
    concat [implode "("; inf_type_to_string t1; implode "->"; inf_type_to_string t2; implode ")"]) ∧
  (inf_type_to_string (Infer_Tapp ts TC_fn) =
    implode "<bad function type>") ∧
  (inf_type_to_string (Infer_Tapp ts TC_tup) =
    concat [implode "("; inf_types_to_string ts; implode ")"]) ∧
  (inf_type_to_string (Infer_Tapp [] tc1) =
    tc_to_string tc1) ∧
  (inf_type_to_string (Infer_Tapp ts tc1) =
    concat [implode "("; inf_types_to_string ts; implode ") "; tc_to_string tc1]) ∧
  (inf_types_to_string [] =
    implode "") ∧
  (inf_types_to_string [t] =
    inf_type_to_string t) ∧
  (inf_types_to_string (t::ts) =
    concat [inf_type_to_string t; implode ", "; inf_types_to_string ts])`;

(*WF_REL_TAC `measure (\x. dtcase x of INL x => infer_t_size x | INR x => infer_t1_size x)`*)

val inf_type_to_string_pmatch = Q.store_thm("inf_type_to_string_pmatch",`
 (∀t. inf_type_to_string t =
    case t of
      Infer_Tuvar _ => "<unification variable>"
    | Infer_Tvar_db n => num_to_dec_string n
    | Infer_Tapp [t1;t2] TC_fn =>
       STRCAT"("  (STRCAT(inf_type_to_string t1)  (STRCAT"->"  (STRCAT(inf_type_to_string t2) ")")))
    | Infer_Tapp _ TC_fn => "<bad function type>"
    | Infer_Tapp ts TC_tup => (STRCAT"("  (STRCAT(inf_types_to_string ts) ")"))
    | Infer_Tapp [] tc1 => tc_to_string tc1
    | Infer_Tapp ts tc1 => STRCAT"("  (STRCAT(inf_types_to_string ts)  (STRCAT") " (tc_to_string tc1)))) /\
 (∀ts. inf_types_to_string ts =
    case ts of
      [] => ""
    | [t] => inf_type_to_string t
    | t::ts => STRCAT(inf_type_to_string t)  (STRCAT", " (inf_types_to_string ts)))`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[inf_type_to_string_def]);

val hex_alt_def = Define`
  hex_alt x = (if x < 16 then HEX x else #"0")`

val num_to_dec_string_alt_def = Define `num_to_dec_string_alt = n2s 10 hex_alt`;

val inf_type_to_string_alt_def = tDefine"inf_type_to_string_alt"`
(inf_type_to_string_alt (Infer_Tuvar _)=  "<unification variable>")
/\ (inf_type_to_string_alt (Infer_Tvar_db n)=  (num_to_dec_string_alt n))
/\ (inf_type_to_string_alt (Infer_Tapp [t1;t2] TC_fn)=
 (STRCAT"("  (STRCAT(inf_type_to_string_alt t1)  (STRCAT"->"  (STRCAT(inf_type_to_string_alt t2) ")")))))
/\ (inf_type_to_string_alt (Infer_Tapp ts TC_fn)=  "<bad function type>")
/\ (inf_type_to_string_alt (Infer_Tapp ts TC_tup)=
 (STRCAT"("  (STRCAT(inf_types_to_string_alt ts) ")")))
/\ (inf_type_to_string_alt (Infer_Tapp [] tc1)=  (tc_to_string tc1))
/\ (inf_type_to_string_alt (Infer_Tapp ts tc1)=
 (STRCAT"("  (STRCAT(inf_types_to_string_alt ts)  (STRCAT") " (tc_to_string tc1)))))
/\ (inf_types_to_string_alt []=  "")
/\ (inf_types_to_string_alt [t]=  (inf_type_to_string_alt t))
/\ (inf_types_to_string_alt (t::ts)=   (STRCAT(inf_type_to_string_alt t)  (STRCAT", " (inf_types_to_string_alt ts))))`
(WF_REL_TAC `measure (\x. case x of INL x => infer_t_size x | INR x => infer_t1_size x)`>>
rw[infer_t_size_def])

val inf_type_to_string_alt_eqn = Q.store_thm("inf_type_to_string_alt_eqn",`
  (∀t.inf_type_to_string_alt t = inf_type_to_string t) ∧
  (∀ts.inf_types_to_string_alt ts = inf_types_to_string ts)`,
  ho_match_mp_tac inf_type_to_string_ind>>
  rw[inf_type_to_string_alt_def,inf_type_to_string_def,num_to_dec_string_alt_def]>>
  fs[ASCIInumbersTheory.n2s_def,ASCIInumbersTheory.num_to_dec_string_def]>>
  fs[MAP_EQ_f,hex_alt_def,MEM_EL]>>
  ntac 2 strip_tac>>
  imp_res_tac numposrepTheory.EL_n2l>>fs[]>>
  `(n DIV 10 ** n') MOD 10 < 10` by fs[]>>
  simp[]);


val _ = export_theory()

