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

fun io2() =
  let open Html
      fun genIntermediates src i =
        (test_location:=SOME ("Test"^Int.toString i^".html") ;
        printBody src (if src = "" then Nothing
        else Success(allIntermediates (stringSyntax.fromMLstring src))
        handle compilationError e => Error e
               | _ => Error "Unknown error"))
  in
  foldl (fn (x,y) => (genIntermediates x y;y+1)) 0 [

"exception Fail; val x = 5+4; if((if(x>4 andalso x>5) then 5 else 4) > 3 ) then (if x>5 then 4 else 5) else (if x<2 orelse x>100 then 3 else raise Fail);",

"fun f x y = (g x) + (g y) and g x = x+1; f 5 4; g it;",

"exception Fail of int; exception Odd; exception Even; val x = 1; (case x of 1 => 2 | 2 => raise Even | 3 => raise Odd | _ => raise Fail 4) handle Odd => 1 | Even => 0+1+2+((raise Fail 5) handle Fail _ => 4) | Fail n => n;",

"structure Nat :> sig type nat val zero:nat val succ:nat-> nat end = struct datatype nat = Int of int val zero = Int 0 fun succ n = case n of Int x => Int (x+1) end;",

"fun f y = let val x = ref y in x:= !x+1 end;",

"datatype 'a foo = Br of 'a * 'a foo * 'a foo | Lf of 'a | Nil; fun f x = case x of Br(v,l,r) => v + (f l) + (f r) | Lf v => v ; f (Br (1, Br(2,Lf 1, Lf 2), (Lf 1)));",

"fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2));",

"datatype foo = Br of ((int * string) * int) * string;",

"datatype ('a,'b,'c) foo2 = Foo of 'a * 'b | Foo2 of 'b * ('c * 'a->'b) | Foo3 of ('a*'b)*'c*('a,'a,'a) foo2;",

"val x = let fun f x = x + 1 val y = f 5 fun g z = y+1 and k y = g 1 val h = g 4 in let val k = 2 in k + f (f y) end end;",
  
"val x = let val y = (let val k = 4 in k+5 end) val z = 2 in let val k = 3 in k+z+y end end;",
  
"fun fabracadabra x = gabracadabra (x-1) and gabracadabra x = if x = 0 then 1 else fabracadabra (x-1); fabracadabra 3;",

"exception E of int*int->string*unit;",

"datatype tree = Br of int * tree * tree | Lf;",

"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];",

"val x = \"hello\";",

"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f n) end; (Nat.iter Nat.succ 5) Nat.zero;",

"structure Nat2 = struct val x = 1 val y=2 val z=3 fun f n = x+y+z+n end;",

"structure blablablabla :> sig type nat     datatype 'a blabla= Lf of 'a | Br of 'a blabla * 'a     val k : nat     val f : 'a blabla -> 'a blabla  end = struct     datatype nat = Int of int     datatype 'a blabla = Lf of 'a | Br of 'a blabla * 'a     val k = Int 0     fun f x = x end;",

"datatype foo = Lf of int * (int -> unit) * int| Br of (int * int) -> (unit * int);",

"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f (n-1)) end;fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2)); (Nat.iter Nat.succ 5) Nat.zero;",

(*random semicolons in the struct, exceptions*)
"structure Nat :> sig val one:int; val zero:int end = struct val one = 1 ; val zero = 0 fun succ x y z = x+y+z+(if x>0 then one else zero); end; ",

(*Exception ctors must start with uppercase*)
"structure Nat :> sig exception E end = struct exception E end; raise Nat.E;",

(*pretty print for brackets*)
"val x = 1+2+3*4+5;",

"val x = (f y;if 5>4 then 3 else 2;let val x = 2 in 3 end;4;if(4<5) then 5 else f y);",

(*Type abbreviations*)
"type 'a nat = int*string*string*int*'a;",

"structure Nat :> sig type nat; type nat2 = nat*nat; val zero:nat; val succ:nat->nat end = struct type nat = int; type nat2 = nat*nat; val zero = 5:nat end;",

"type ('a,'b) compose = 'a -> 'b;",

"type t = exn;"

]; ()
  end

val _ = PolyML.export("pp",io);

val _ = PolyML.export("regression",io2);

