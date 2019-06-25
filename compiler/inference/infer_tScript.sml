(*
  The infer_t datatype and various to_string functions.
*)
open preamble;
open mlstringTheory mlintTheory;
open astTheory semanticPrimitivesTheory typeSystemTheory;

val _ = numLib.prefer_num();

val _ = new_theory "infer_t";

val _ = Datatype `
 infer_t =
    Infer_Tvar_db num
  | Infer_Tapp (infer_t list) type_ident
  | Infer_Tuvar num`;

val infer_t_size_def = fetch "-" "infer_t_size_def";

val id_to_string_def = Define `
  (id_to_string (Short s) = implode s) ∧
  (id_to_string (Long x id) =
    concat [implode x; implode "."; id_to_string id])`;

val get_tyname_def = Define `
  get_tyname n (Bind [] []) = NONE /\
  get_tyname n (Bind [] ((m,ys)::xs)) =
    (case get_tyname n ys of
     | NONE => get_tyname n (Bind [] xs)
     | SOME x => SOME (m ++ "." ++ x)) /\
  get_tyname n (Bind ((tyname,_,t)::xs) m) =
    if (case t of Tapp _ m => m = n | _ => F) then
      SOME tyname
    else get_tyname n (Bind xs m)`

val type_ident_to_string_def = Define `
  type_ident_to_string tys ti =
  if ti = Tarray_num then
    strlit "Array.array"
  else if ti = Tbool_num then
    strlit "bool"
  else if ti = Tchar_num then
    strlit "char"
  else if ti = Texn_num then
    strlit "exn"
  else if ti = Tint_num then
    strlit "int"
  else if ti = Tlist_num then
    strlit "list"
  else if ti = Tref_num then
    strlit "ref"
  else if ti = Tstring_num then
    strlit "string"
  else if ti = Tvector_num then
    strlit "Vector.vector"
  else if ti = Tword64_num then
    strlit "Word64.word"
  else if ti = Tword8_num then
    strlit "Word8.word"
  else if ti = Tword8array_num then
    strlit "byte_array"
  else
    case get_tyname ti tys of
    | NONE => mlint$toString (&ti)
    | SOME s => implode s`;

(* TODO: update for pretty printing *)

val ty_var_name_def = Define `
  ty_var_name n =
    if n < 28 then implode ("'" ++ [CHR (n + ORD #"a")]) else
                   concat [implode "'"; mlint$toString (&n)]`;

val commas_def = Define `
  commas c [] = [] /\
  commas c [x] = [x] /\
  commas c (x::ys) = x :: c :: commas c ys`;

val add_parens_def = Define `
  add_parens threshold (x,n) =
    if threshold < n:num then concat [strlit "("; x; strlit ")"] else x`

val infer_t_size_lemma = prove(
  ``!ts a. MEM a ts ==> infer_t_size a < infer_t1_size ts``,
  Induct \\ fs [infer_t_size_def] \\ rw [] \\ fs [infer_t_size_def]
  \\ res_tac \\ fs []);

val inf_type_to_string_def = tDefine "inf_type_to_string" `
  (inf_type_to_string tys (Infer_Tuvar n) =
    (concat [strlit "_"; mlint$toString (&n)],0)) ∧
  (inf_type_to_string tys (Infer_Tvar_db n) =
    (concat [ty_var_name n],0n)) ∧
  (inf_type_to_string tys (Infer_Tapp ts ti) =
    if ti = Tfn_num then
     (case ts of
      | [t1; t2] =>
        (concat [add_parens 2 (inf_type_to_string tys t1); implode " -> ";
                 add_parens 3 (inf_type_to_string tys t2)],3)
      | _ => (implode "<bad function type>",0))
    else if ti = Ttup_num then
     (case ts of
      | [] => (strlit "unit",0)
      | [t] => inf_type_to_string tys t
      | _ => (concat (commas (implode " * ")
               (MAP (add_parens 1) (MAP (inf_type_to_string tys) ts))),2n))
    else
      case ts of
      | [] => (type_ident_to_string tys ti,0)
      | [t] =>
        (concat [add_parens 1 (inf_type_to_string tys t); implode " ";
                 type_ident_to_string tys ti],1)
      | _ =>
        (concat ([strlit "("] ++
                 commas (implode ", ")
                   (MAP (add_parens 5) (MAP (inf_type_to_string tys) ts)) ++
                 [strlit ") "; type_ident_to_string tys ti]),1))`
 (WF_REL_TAC `measure (\(_,x). infer_t_size x)`
  \\ rw [] \\ imp_res_tac infer_t_size_lemma \\ fs []);

(*

val a = ``Infer_Tvar_db 0``
val b = ``Infer_Tvar_db 1``
fun mk_fn t1 t2 = ``Infer_Tapp [^t1;^t2] Tfn_num``;
fun mk_tup t1 t2 = ``Infer_Tapp [^t1;^t2] Ttup_num``;
fun mk_sum t1 t2 = ``Infer_Tapp [^t1;^t2] Tlist_num``;
fun mk_list t1 = ``Infer_Tapp [^t1] Tlist_num``;

val t = mk_fn a a
val t = mk_tup t t

val t = mk_tup a a
val t = mk_fn t t

val t = mk_fn a a
val t = mk_tup a t
val t = mk_tup a a
val t = mk_sum t t

  EVAL ``FST (inf_type_to_string ^tys ^t)`` |> concl |> rand |> rand

  ``(x,y):'a # ('a -> 'a) list list``

  EVAL ``FST (inf_type_to_string ^tys ^t)`` |> concl |> rand |> rand

*)

(*
Theorem inf_type_to_string_pmatch:
  (∀t. inf_type_to_string t =
    case t of
      Infer_Tuvar n =>
      concat [implode "<unification variable "; mlint$toString (&n); implode ">"]
    | Infer_Tvar_db n =>
      concat [implode "<type variable "; mlint$toString (&n); implode ">"]
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
    | t::ts => concat [inf_type_to_string t; implode ", "; inf_types_to_string ts])
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[inf_type_to_string_def]
QED
  *)

val _ = export_theory ();
