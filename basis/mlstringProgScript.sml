open preamble 
  ml_translatorLib ml_progLib
open mlstringTheory

val _ = new_theory"mlstringProg"

val _ = translation_extends "listProg";

val _ = ml_prog_update (open_module "String");

val res = append_dec ``Dlet (Pvar "size") (Fun "x" (App (Strlen) [Var(Short"x")]))``;
val _ = trans "explode" `explode`
val _ = trans "implode" `implode`
val _ = trans "size" `strlen`


val result = translate EL;
val result = translate sub_def;


val result = translate extract_aux_def;
val result = translate extract_def;
val result = translate substring_def;


val result = translate strcat_def;

val result = translate stringListToChars_def;
val result = translate concat_def;

val result = translate concatWith_aux_def;
val result = translate concatWith_def;

val result = translate str_def;

translate explode_aux_def;
translate explode_def;

val result = translate translate_aux_def;
val result = translate translate_def;

(*these have pre-conditions because sub has a precondition *)
val result = translate tokens_aux_def;
val result = translate tokens_def;

val result = translate fields_aux_def;
val result = translate fields_def;

(*These may also not be translating because of the sub precondition *)
val result = translate isStringThere_aux_def;
val result = translate isPrefix_def;
val result = translate isSuffix_def;
val result = translate is Substring_aux;

(*Pre conditions from sub *)
val result = translate compare_aux_def;
val result = translate compare_def;


(*Pre conditions from sub *)
val result = translate collate_aux_def;
val result = translate collate_def;


val _ = ml_prog_update (close_module NONE);

val _ = export_theory()

