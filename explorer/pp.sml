(*
 Code for CGI modified from:
 mosmlcgi.sml

 (c) Jonas Barklund, Computing Science Dept., Uppsala University, 1996.

 Anyone is granted to copy and/or use this code, provided that this note
 is retained, also in modified versions.  The code is provided as is with
 no guarantee about any functionality.  I take no responsibility for its
 proper function.

*)

val _ = PolyML.SaveState.loadState "heap";
val _ = use"html.sml";

open allPP html

datatype result = Nothing | Success of allIntermediates | Error of string

fun printBody src out =
  let open Html
  in
    page {title = "CakeML Compiler Explorer",
         css = ["css/explorer.css",
                "https://code.jquery.com/ui/1.10.4/themes/smoothness/jquery-ui.css"],
         javascript = ["https://code.jquery.com/jquery-2.1.1.min.js"
                      ,"https://code.jquery.com/ui/1.10.4/jquery-ui.min.js"],
         body = ([], [
         (*Introductory header*)
         H(2,[],"CakeML Compiler Explorer"),
         P (Sequence [String "Write", A([("href","..")],String"CakeML"), String"code and see how it is transformed by each phase of compilation."]),
         (*Form to submit code*)
         FORM ([("method","POST")],
           [
             String(quote_to_string[QUOTE"Code"]), BR,
             TEXTAREA([("name","src")],src), BR,
             INPUT [("type","submit") , ("name","run") , ("value","Compile")]
           ]
         )] @
         (case out of Nothing => []
          | Error err => [DIV ([("class","error")], PAR (String err))]
          | Success out => [
         (*Tabs for compiler intermediates*)
         DIV ([("class","tabs")],
           Sequence
           [
             UL ([],
               Sequence(
               let
                 fun f i q = LI (A ([("href","#"^(Int.toString i)),("class","m")], String (quote_to_string q)))
               in
                 mapi f [[QUOTE"AST"]
                        ,[QUOTE"modLang"]
                        ,[QUOTE"conLang"]
                        ,[QUOTE"decLang"]
                        ,[QUOTE"exhLang"]
                        ,[QUOTE"patLang"]]
               end)),
             DIV([],
               Sequence
               let
                 fun f i t = DIV([("id",Int.toString i)], T 80 t)
               in
                 mapi f (#ils out)
               end)
           ]), BR ,

           (*Globals,Ctors Module and annotations table*)
           DIV ([("class","tabs")],
             Sequence
             [
               UL ([],
                 Sequence(
                 [
                   LI (A ([("href","#globals"),("class","m")], String (quote_to_string [QUOTE"Globals"]))) ,
                   LI (A ([("href","#modules"),("class","m")], String (quote_to_string [QUOTE"Modules"]))),
                   LI (A ([("href","#constructors"),("class","m")], String (quote_to_string [QUOTE"Constructors"]))),
                   LI (A ([("href","#annotations"),("class","m")], String (quote_to_string [QUOTE"Annotations"])))
                 ])),
               DIV( [],
                 Sequence
                 [
                   (*
                   DIV([("id","globals")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o (term_to_html_string 80)) (#globMap out)))),
                   DIV([("id","modules")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o (term_to_html_string 80)) (#modMap out)))),
                   DIV([("id","constructors")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#ctors out)))),
                   DIV([("id","annotations")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#annotations out))))
                   *)
                 ])
             ]),
          (*Javascript call*)
          JSINLINE ("$( \".tabs\" ).tabs();")
         ]))
       }
end

fun main() =
  let open Html
      val cgi_request_method = Process.getEnv("REQUEST_METHOD");
      val cgi_content_length = Process.getEnv("CONTENT_LENGTH");
      fun int_from_str_opt(NONE, default) = default
      | int_from_str_opt(SOME(s), default) =
        getOpt(Int.fromString(s),default);

      val _ = TextIO.input1 TextIO.stdIn (* discard leading newline *)
      val url_encoded_string = if cgi_request_method = SOME("POST")
			       then (TextIO.inputN(TextIO.stdIn,int_from_str_opt(cgi_content_length,0)))
			       else "";
      val sizeofStr = size url_encoded_string
      val the_fields =
	Substring.tokens(fn c => c = #"&")(Substring.substring (url_encoded_string,0,size url_encoded_string ));

      val dict_with_codes =
	map(Substring.fields(fn( c) => c = #"="))(the_fields);

      fun decode(sus) =
        let
            val sz = Substring.size(sus);
            exception Dehex;
            fun dehex(ch) =
                if #"0" <= ch andalso ch <= #"9"
                    then ord(ch) - ord(#"0")
                else if #"A" <= ch andalso ch <= #"F"
                         then (ord(ch) - ord(#"A")) + 10
                     else if #"a" <= ch andalso ch <= #"f"
                              then (ord(ch) - ord(#"a")) + 10
                          else raise Dehex;
            fun decode_one(i) =
                chr(16*dehex(Substring.sub(sus,i+1))+
		    dehex(Substring.sub(sus,i+2)));
            fun dec(i) =
                if i>=sz then []
                else case Substring.sub(sus,i)
                       of #"+" => #" "::dec(i+1)
                        | #"%" => decode_one(i)::dec(i+3)
                        | ch => ch::dec(i+1);
        in
            String.implode(dec(0))
        end;

      val cgi_dict = List.map (fn item => (decode(hd(item)),decode(hd(tl(item))))) dict_with_codes;

      fun cgi_field_string(name) =
        let fun lookup [] = NONE
            |   lookup ((x,y)::xs) = if x=name then SOME y else lookup xs
        in
          lookup cgi_dict
        end;

      val src = case cgi_field_string("src") of NONE => "" | SOME(src) => src;

      val out = if src = "" then Nothing
                else Success(allIntermediates (stringSyntax.fromMLstring src))
                handle compilationError e => Error e
                       | _ => Error "Unknown error"

  in
    printBody src out
  end;
