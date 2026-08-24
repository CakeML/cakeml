(*
  Pancake news as an mlstring
*)
Theory news
Ancestors
  panLang backend_common[qualified]
Libs
  preamble TextIO

val news_in = openIn "NEWS.md";
val news = inputAll news_in;
val _ = closeIn news_in;

Definition news_def:
  news = implode ^(stringLib.fromMLstring news)
End
