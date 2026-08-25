(*
  Pancake news presentation and validation
*)
Theory news
Ancestors
  panLang backend_common[qualified]
Libs
  preamble TextIO listSyntax stringLib pairSyntax bitstringSyntax

fun toMLstring s = mk_comb(“implode”,fromMLstring s)

val news_in = openIn "NEWS.md";
val news = inputAll news_in;
val _ = closeIn news_in;

Definition news_def:
  news = ^(toMLstring news)
End

val aprefix = "<sub>"
val eprefix = "<sub>Feature enabled: `"
val dprefix = "<sub>Feature disabled: `"
val suffix = "`</sub>"

val parseErr = Feedback.mk_HOL_ERR "news" "parseFeatureLine"
val validateErr = Feedback.mk_HOL_ERR "news" "validateFeatures"

(* Validate that lines beginning with <sub> are well-formed feature lines *)
fun parseFeatureLine s =
  if String.isSuffix suffix s then
     let val s' = String.substring(s,0,size s - size suffix)
     in
       if String.isPrefix eprefix s' then
         (String.substring(s',size eprefix,size s' - size eprefix),true)
       else if String.isPrefix dprefix s' then
         (String.substring(s',size dprefix,size s' - size dprefix),false)
       else
         raise parseErr $ "Feature line in NEWS.md needs to begin with " ^ eprefix ^ " or " ^ dprefix
     end
  else
    raise parseErr $ "Feature line in NEWS.md needs to end with " ^ suffix

(* Validate that lines beginning with <sub> are well-formed feature lines *)
val feature_lines =
  String.tokens (curry op = #"\n") news
  |> filter (String.isPrefix aprefix)
  |> map parseFeatureLine

(* Validate that features aren't enabled or disabled twice in a row. *)
(* this is worst-case quadratic time *)
fun validateFeatures [] = fs
  | validateFeatures ((s,b)::fs) =
    validateFeatures fs before
    case List.find (curry op = s o fst) fs of
      NONE => ()
    | SOME (_,b') =>
        if b = b' then
          raise validateErr $
                "Feature " ^ s ^ " was already " ^ if b then "enabled" else "disabled"
        else
          ()

val _ = validateFeatures feature_lines

(* this is also worst-case quadratic time *)
fun cleanFeatures [] =  []
  | cleanFeatures ((s,b)::fs) =
    let val fs' = cleanFeatures $ filter (curry op <> s o fst) fs
    in
      if b then
        s::fs'
      else
        fs'
    end

val feature_lines_tm =
  feature_lines
  |> cleanFeatures
  |> lift_list “:mlstring list” toMLstring

Definition query_news_def:
  query_news s =
  MEM ^feature_lines_tm s
End
