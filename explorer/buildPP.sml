(*
 Code for CGI modified from:
 mosmlcgi.sml

 (c) Jonas Barklund, Computing Science Dept., Uppsala University, 1996.

 Anyone is granted to copy and/or use this code, provided that this note
 is retained, also in modified versions.  The code is provided as is with
 no guarantee about any functionality.  I take no responsibility for its
 proper function.

*)

open cakeml_computeLib
open HolKernel boolLib bossLib Parse
open Portable smpp 
open astPP modPP conPP exhPP patPP
open html

fun println str = (print str; print"#@#");
fun printls sep str = (print str; print sep);
fun termToList ls = #1(listSyntax.dest_list(ls));

val _ = set_trace"pp_avoids_symbol_merges"0;

fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;
(*RHS of theorem to term*)
val rhsThm = rhs o concl;

val compile_primitives_def = Define`
  compile_primitives =
    FST(compile_top NONE init_compiler_state
    (Tdec initial_program))`;

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_def,compilerTheory.compile_top_def] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_full = eval ``compile_primitives``

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_full] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_pieces =
  LIST_CONJ[
  eval ``compile_primitives.globals_env``
  ,eval ``compile_primitives.next_global``
  ,eval ``compile_primitives.exh``
  ,eval ``compile_primitives.contags_env``
  ,eval ``compile_primitives.rnext_label``];
val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_pieces] cs
val eval = computeLib.CBV_CONV cs

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)
      
      (*i1 translation*)
      val n = rhsThm (eval ``compile_primitives.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``compile_primitives.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*Assume start from fempty*)
      val (_,modMap) = finite_mapSyntax.strip_fupdate v2
      val (_,globMap) = finite_mapSyntax.strip_fupdate m2

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 compile_primitives.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      val p2' = (v,exh,p2)
      (*print the CTORS (num,name,typeid)*)
      val [_,_,_,ct] =pairSyntax.strip_pair v 

      val (_,ctors) = finite_mapSyntax.strip_fupdate ct;
      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ compile_primitives.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=compile_primitives.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp


  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7,ctors = ctors,globMap=globMap,modMap=modMap}
  end;

(*Not included yet
val compile_print_err = eval ``compile_print_err ^(r)``;
val r = rhs(concl compile_print_err)

val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(r)
                           | SOME n =>
                               (let r = emit ^(r) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``
val r = rhs(concl addIt)
val emit = eval ``emit ^(r) [Stop T]``
val rev = eval ``REVERSE (^(rhs(concl emit))).out``

val tm = "val x = 5;";

fun io_Handler() = 
  let val str = SOME(tm)
  in
  (
    case str 
    of SOME(x) =>  
    let val str = stringSyntax.fromMLstring x
    val out = allIntermediates str
    in
      map (printls ";" o term_to_string) (termToList (#ast out));
      println "";
      map (printls ";" o term_to_string) (termToList (#i1 out));
      println ""; 
      map (printls ";" o term_to_string) (termToList (#i2 out));
      println "";
      println (term_to_string (#i3(out)));
      println (term_to_string (#i4(out)));
      println (term_to_string (#i5(out)));
      println (term_to_string (#i6(out)));
      map (printls "\n" o term_to_string) (#globMap out);
      println "";
      map (printls "\n" o term_to_string) (#modMap out);
      println "";
      map (printls "\n" o term_to_string) (#ctors out);()
    end
  ) handle _ => TextIO.print "Invalid Input\n"
  end;
*)


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
      
      (*probably needs error handling here*)
      val out = allIntermediates (stringSyntax.fromMLstring src);

      (*Could put this into the CSS*)
      val taAtts = [("rows","22"),("cols","192")];
  in
    page {title = "CakeML PP",
         css = SOME("/css/standalone.css"),
         javascript = SOME("http://cdn.jquerytools.org/1.2.7/full/jquery.tools.min.js"),
         body = ([], [
         (*Form to submit code*)
         FORM ([("action","pp.cgi"),("method","POST")],
           [ 
             String(quote_to_string`Code`), BR,
             TEXTAREA([("name","src")]@taAtts,src), BR,
             INPUT [("type","submit") , ("name","run") , ("value","Compile")]
           ]
         ),

         (*Tabs for compiler intermediates*)
         DIV ([],
           Sequence
           [ 
             UL ([("class","tabs")],
               Sequence(
               [
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `AST`))) ,
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `modLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `conLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `decLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `exhLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `patLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `intLang`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `Bytecode 1`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `Bytecode 2`))),
                 LI (A ([("href","#"),("class","m")], String (quote_to_string `x86`)))

               ])),
             (*Tab contents, maybe set rows and cols dynamically?
              need to somehow disable pretty printing in textarea...*)
             DIV( [("class","panes")],
               Sequence
               [
                 (*Prettify the list printing*)
                 DIV([],TEXTAREA (taAtts,String.concat
                 (map ((fn s => s^";") o term_to_string) (termToList (#ast out))))),

                 DIV([],TEXTAREA (taAtts,String.concat 
                 (map ((fn s => s^";") o term_to_string) (termToList (#i1 out))))),

                 DIV([],TEXTAREA (taAtts,String.concat 
                 (map ((fn s => s^";") o term_to_string) (termToList (#i2 out))))),

                 DIV([],TEXTAREA (taAtts, term_to_string (#i3 out))),
                 DIV([],TEXTAREA (taAtts, term_to_string (#i4 out))),
                 DIV([],TEXTAREA (taAtts, term_to_string (#i5 out))),
                 DIV([],TEXTAREA (taAtts, term_to_string (#i6 out))),
                 DIV([],TEXTAREA (taAtts, "i7")),
                 DIV([],TEXTAREA (taAtts,"i8")),
                 DIV([],TEXTAREA (taAtts,"i9")),
                 DIV([],TEXTAREA (taAtts, "i10"))
               ])
           ]),
          
           (*Globals,Ctor and Module table*)
           DIV ([],
             Sequence
             [
               UL ([("class","tabs")],
                 Sequence(
                 [
                   LI (A ([("href","#"),("class","m")], String (quote_to_string `Globals`))) ,
                   LI (A ([("href","#"),("class","m")], String (quote_to_string `Modules`))),
                   LI (A ([("href","#"),("class","m")], String (quote_to_string `Constructors`)))
                 ])),     
               DIV( [("class","panes")],
                 Sequence
                 [
                   DIV([],TEXTAREA (taAtts, String.concat 
                   (map ((fn s => s^"\n") o term_to_string) (#globMap out)))),
                   DIV([],TEXTAREA (taAtts, String.concat 
                   (map ((fn s => s^"\n") o term_to_string) (#modMap out)))),
                   DIV([],TEXTAREA (taAtts, String.concat 
                   (map ((fn s => s^"\n") o term_to_string) (#ctors out))))                 
                 ])
             ]),
          (*Javascript call*)
          JAVASCRIPT ("/js/test.js")

         ])
       }
end;     

val _ = PolyML.export("pp",io_Handler2);

