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

fun termToList ls = #1(listSyntax.dest_list(ls));

val _ = set_trace"pp_avoids_symbol_merges"0;

fun io_Handler2() =
  let open Html
      val cgi_request_method = Process.getEnv("REQUEST_METHOD");
      val cgi_content_length = Process.getEnv("CONTENT_LENGTH");
      fun int_from_str_opt(NONE, default) = default
      | int_from_str_opt(SOME(s), default) =
        getOpt(Int.fromString(s),default);

      val url_encoded_string = if cgi_request_method = SOME("POST")
			       then (TextIO.inputN(TextIO.stdIn,int_from_str_opt(cgi_content_length,0)))
			       else "";
      (*testing*)
      (*val url_encoded_string = "asdasf=asdasasdf&asdfasd=asdasdasd&src=val+x+%3D5%2B5%3B%0D%0A&bla=bla&asdf=asf";*)
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

      val errStr = ref "";
      (*probably needs error handling here*)
      val out = if src = "" then NONE
                else (SOME(allIntermediates (stringSyntax.fromMLstring src)))
                  handle compilationError e => (errStr:=e;NONE)
                       | _ => (errStr := "Unknown error"; NONE)

      (*Could put this into the CSS*)
      val taAtts = [("rows","22"),("cols","192")];
  in
    page {title = "CakeML PP",
         css = ["css/explorer.css",
                "//code.jquery.com/ui/1.10.4/themes/smoothness/jquery-ui.css"],
         javascript = ["//code.jquery.com/jquery-2.1.1.min.js"
                      ,"//code.jquery.com/ui/1.10.4/jquery-ui.min.js"],
         body = ([], [
         (*Form to submit code*)
         FORM ([("method","POST")],
           [
             String(quote_to_string`Code`), BR,
             TEXTAREA([("name","src")]@taAtts,src), BR,
             INPUT [("type","submit") , ("name","run") , ("value","Compile")]
           ]
         ),

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
             (*Tab contents, maybe set rows and cols dynamically?
              need to somehow disable pretty printing in textarea...*)
             DIV( [],
               Sequence
               [
                 (*Prettify the list printing*)
                 DIV([("id","0")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) => String.concat
                 (map ((fn s => s^";") o term_to_string) (termToList (#ast out))))),

                 DIV([("id","1")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) => String.concat
                 (map ((fn s => s^";") o term_to_string) (termToList (#i1 out))))),

                 DIV([("id","2")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) => String.concat
                 (map ((fn s => s^";") o term_to_string) (termToList (#i2 out))))),

                 DIV([("id","3")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i3 out))),

                 DIV([("id","4")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i4 out))),
                 DIV([("id","5")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i5 out))),
                 DIV([("id","6")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i6 out))),


                 DIV([("id","7")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>String.concat
                 (map ((fn s => if(String.isPrefix "Label" s) then s^":\n" else "\t"^s^";\n")
                  o term_to_string) (termToList (#i7 out))))),

                 DIV([("id","8")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i8 out))),
                 DIV([("id","9")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i9 out))),
                 DIV([("id","10")],TEXTAREA (taAtts,case out of NONE => !errStr | SOME(out) =>
                 term_to_string (#i10 out)))
               ])
           ]), BR ,

           (*Globals,Ctor and Module table*)
           DIV ([("class","tabs")],
             Sequence
             [
               UL ([],
                 Sequence(
                 [
                   LI (A ([("href","#globals"),("class","m")], String (quote_to_string `Globals`))) ,
                   LI (A ([("href","#modules"),("class","m")], String (quote_to_string `Modules`))),
                   LI (A ([("href","#constructors"),("class","m")], String (quote_to_string `Constructors`)))
                 ])),
               DIV( [],
                 Sequence
                 [
                   DIV([("id","globals")],TEXTAREA (taAtts, case out of NONE => !errStr | SOME(out) => String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#globMap out)))),
                   DIV([("id","modules")],TEXTAREA (taAtts, case out of NONE => !errStr | SOME(out) => String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#modMap out)))),
                   DIV([("id","constructors")],TEXTAREA (taAtts, case out of NONE => !errStr | SOME(out) => String.concat
                   (map ((fn s => s^"\n") o term_to_string) (#ctors out))))
                 ])
             ]),
          (*Javascript call*)
          JSINLINE ("$( \".tabs\" ).tabs();")
         ])
       }
end;

val _ = PolyML.export("pp",io_Handler2);
