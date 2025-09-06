(*
  Library that helps pretty print code
*)
structure presLangLib :> presLangLib =
struct

open HolKernel boolLib bossLib;

local
  val s1 = HolKernel.syntax_fns1 "misc"
  val s2 = HolKernel.syntax_fns2 "misc"
  val m1 = HolKernel.syntax_fns1 "mlstring"
in
  val (Append_tm,mk_Append,dest_Append,is_Append) = s2 "Append";
  val (List_tm,mk_List,dest_List,is_List) = s1 "List";
  val (strlit_tm,mk_strlit,dest_strlit,is_strlit) = m1 "strlit";
end

(* expects tm to be a concrete app_list *)
fun dest_app_list tm = let
  fun aux tm acc =
    if is_Append tm then
      let val (x,y) = dest_Append tm
      in aux x (aux y acc) end
    else if is_List tm then
      let val x = dest_List tm
      in fst (listSyntax.dest_list x) @ acc end
    else acc
  in aux tm [] end;

(* turns mlstring app_list into string list *)
fun mlstring_app_list_to_string_list tm =
  map (stringSyntax.fromHOLstring o dest_strlit) (dest_app_list tm);

fun flat_to_strs flat_prog_tm =
  presLangTheory.flat_to_strs_def
      |> SPECL [flat_prog_tm]
      |> concl |> dest_eq |> fst |> EVAL |> concl |> rand
      |> mlstring_app_list_to_string_list;

fun clos_to_strs clos_prog_tm =
  presLangTheory.clos_to_strs_def
      |> SPECL [clos_prog_tm]
      |> Q.SPEC ‘[]’
      |> concl |> dest_eq |> fst |> EVAL |> concl |> rand
      |> mlstring_app_list_to_string_list;

fun bvl_to_strs names_tm bvl_prog_tm =
  presLangTheory.bvl_to_strs_def
      |> SPECL [names_tm,bvl_prog_tm]
      |> concl |> dest_eq |> fst |> EVAL |> concl |> rand
      |> mlstring_app_list_to_string_list;

fun bvi_to_strs names_tm bvi_prog_tm =
  presLangTheory.bvi_to_strs_def
      |> SPECL [names_tm,bvi_prog_tm]
      |> concl |> dest_eq |> fst |> EVAL |> concl |> rand
      |> mlstring_app_list_to_string_list;

fun data_to_strs names_tm data_prog_tm =
  presLangTheory.data_to_strs_def
      |> SPECL [names_tm,data_prog_tm]
      |> concl |> dest_eq |> fst |> EVAL |> concl |> rand
      |> mlstring_app_list_to_string_list;

fun print_strs strs = app print strs;

fun write_strs_to_file filename strs = let
  val f = TextIO.openOut filename
  val _ = app (curry TextIO.output f) strs
  val _ = TextIO.closeOut f
  in () end;

end
