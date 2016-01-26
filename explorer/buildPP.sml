structure buildPP = struct
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
end
end
