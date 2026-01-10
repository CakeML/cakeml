(*
  The infer_t datatype and various to_string functions.
*)
Theory infer_t
Ancestors
  mlstring mlint ast semanticPrimitives typeSystem
Libs
  preamble

val _ = numLib.temp_prefer_num();

Datatype:
 infer_t =
    Infer_Tvar_db num
  | Infer_Tapp (infer_t list) type_ident
  | Infer_Tuvar num
End

Theorem infer_t_ind = fetch "-" "infer_t_induction"
  |> Q.SPEC ‘P’ |> Q.SPEC ‘EVERY P’ |> SRULE [] |> cj 1 |> SRULE [EVERY_MEM];

Definition id_to_string_def:
  (id_to_string (Short s) = s) ∧
  (id_to_string (Long x id) =
    concat [x; implode "."; id_to_string id])
End

Definition get_tyname_def:
  get_tyname n (Bind [] []) = NONE /\
  get_tyname n (Bind [] ((m,ys)::xs)) =
    (case get_tyname n ys of
     | NONE => get_tyname n (Bind [] xs)
     | SOME x => SOME (m ^ «.» ^ x)) /\
  get_tyname n (Bind ((tyname,_,t)::xs) m) =
    if (case t of Tapp _ m => m = n | _ => F) then
      SOME tyname
    else get_tyname n (Bind xs m)
End

Definition type_ident_to_string_def:
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
  else if ti = Tdouble_num then
    strlit "Double.double"
  else
    case get_tyname ti tys of
    | NONE => mlint$toString (&ti)
    | SOME s => s
End

Definition ty_var_name_def:
  ty_var_name n =
    if n < 28 then implode ("'" ++ [CHR (n + ORD #"a")]) else
                   concat [implode "'"; mlint$toString (&n)]
End

Definition commas_def:
  commas c [] = [] /\
  commas c [x] = [x] /\
  commas c (x::ys) = x :: c :: commas c ys
End

Definition add_parens_def:
  add_parens threshold (x,n) =
    if threshold < n:num then concat [strlit "("; x; strlit ")"] else x
End

Definition inf_type_to_string_rec_def:
  (inf_type_to_string_rec tys (Infer_Tuvar n) =
    (concat [strlit "_"; mlint$toString (&n)],0)) ∧
  (inf_type_to_string_rec tys (Infer_Tvar_db n) =
    (concat [ty_var_name n],0n)) ∧
  (inf_type_to_string_rec tys (Infer_Tapp ts ti) =
    if ti = Tfn_num then
     (case ts of
      | [t1; t2] =>
        (concat [add_parens 2 (inf_type_to_string_rec tys t1); strlit " -> ";
                 add_parens 3 (inf_type_to_string_rec tys t2)],3)
      | _ => (implode "<bad function type>",0))
    else if ti = Ttup_num then
     (case ts of
      | [] => (strlit "unit",0)
      | [t] => inf_type_to_string_rec tys t
      | _ => (concat (commas (strlit " * ")
               (MAP (add_parens 1) (inf_type_to_string_rec_list tys ts))),2n))
    else
      case ts of
      | [] => (type_ident_to_string tys ti,0)
      | [t] =>
        (concat [add_parens 1 (inf_type_to_string_rec tys t); strlit " ";
                 type_ident_to_string tys ti],1)
      | _ =>
        (concat ([strlit "("] ++
                 commas (strlit ", ")
                   (MAP (add_parens 5) (inf_type_to_string_rec_list tys ts)) ++
                 [strlit ") "; type_ident_to_string tys ti]),1)) ∧
  inf_type_to_string_rec_list tys [] = [] ∧
  inf_type_to_string_rec_list tys (t::ts) =
    inf_type_to_string_rec tys t ::
    inf_type_to_string_rec_list tys ts
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (_,t) => infer_t_size t
                                    | INR (_,ts) => list_size infer_t_size ts’
End

Definition inf_type_to_string_def:
  inf_type_to_string tys t = FST (inf_type_to_string_rec tys t)
End
