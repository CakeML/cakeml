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

exception compilationError of string;

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)

      val _ =if ast = ``"<parse error>\n"`` then raise compilationError "Parse Error" else ();

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
      val p7_1 = rhsThm compile_Cexp

      (*compile print err*)
      val compile_print_err = eval ``compile_print_err ^(p7_1)``;
      val p7_2 = rhsThm compile_print_err

      (*Add it*)
      val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(p7_2)
                           | SOME n =>
                               (let r = emit ^(p7_2) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``

      val p7_3 = rhsThm addIt

      val emit = eval ``emit ^(p7_3) [Stop T]``
      val p7_4 = rhsThm emit

      val rev = eval ``REVERSE (^p7_4).out``

      val p7 = rhsThm rev
      (*temporaries*)
      val p8 = p7;
      val p9 = p7;
      val p10 =p7;
      val p11 =p7;
  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7,i8=p8,i9=p9,i10=p10,i11=p11,ctors = ctors
      ,globMap=globMap,modMap=modMap}
  end;

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
         FORM ([("action","pp.cgi"),("method","POST")],
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
