(*
 Code for CGI modified from:
 mosmlcgi.sml

 (c) Jonas Barklund, Computing Science Dept., Uppsala University, 1996.

 Anyone is granted to copy and/or use this code, provided that this note
 is retained, also in modified versions.  The code is provided as is with
 no guarantee about any functionality.  I take no responsibility for its
 proper function.

*)

open allPP html

datatype result = Nothing | Success of allIntermediates | Error of string

fun io() =
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
      (*testing*)
      (*val url_encoded_string = 
          "asdasf=asdasasdf&asdfasd=asdasdasd&src=val+x+%3D5%2B5%3B%0D%0A&bla=bla&asdf=asf";*) 
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

      (*testing*)
      (*val src = "val x = 5;"*)
      val out = if src = "" then Nothing
                else Success(allIntermediates (stringSyntax.fromMLstring src))
                handle compilationError e => Error e
                       | _ => Error "Unknown error"

  in
    page {title = "CakeML Compiler Explorer",
         css = ["css/explorer.css",
                "//code.jquery.com/ui/1.10.4/themes/smoothness/jquery-ui.css"],
         javascript = ["//code.jquery.com/jquery-2.1.1.min.js"
                      ,"//code.jquery.com/ui/1.10.4/jquery-ui.min.js"],
         body = ([], [
         (*Introductory header*)
         H(2,[],"CakeML Compiler Explorer"),
         P (Sequence [String "Write", A([("href","..")],String"CakeML"), String"code and see how it is transformed by each phase of compilation."]),
         (*Form to submit code*)
         FORM ([("method","POST")],
           [
             String(quote_to_string`Code`), BR,
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
                 mapi f [`AST`
                        ,`modLang`
                        ,`conLang`
                        ,`decLang`
                        ,`exhLang`
                        ,`patLang`
                        ,`intLang`
                        ,`Bytecode 1`
                        ,`Bytecode 2`
                        ,`x86`]
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
                   LI (A ([("href","#globals"),("class","m")], String (quote_to_string `Globals`))) ,
                   LI (A ([("href","#modules"),("class","m")], String (quote_to_string `Modules`))),
                   LI (A ([("href","#constructors"),("class","m")], String (quote_to_string `Constructors`))),
                   LI (A ([("href","#annotations"),("class","m")], String (quote_to_string `Annotations`)))
                 ])),
               DIV( [],
                 Sequence
                 [
                   DIV([("id","globals")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o (term_to_html_string 80)) (#globMap out)))),
                   DIV([("id","modules")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o (term_to_html_string 80)) (#modMap out)))),
                   DIV([("id","constructors")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#ctors out)))),
                   DIV([("id","annotations")],Preformatted(String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#annotations out))))
                 ])
             ]),
          (*Javascript call*)
          JSINLINE ("$( \".tabs\" ).tabs();")
         ]))
       }
end;

val _ = PolyML.export("pp",io);
