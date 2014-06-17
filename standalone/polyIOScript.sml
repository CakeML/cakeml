fun println str = (print str; print"#@#");
fun printls sep str = (print str; print sep);
fun termToList ls = #1(listSyntax.dest_list(ls))

fun io_Handler() = 
  let val str = TextIO.inputLine TextIO.stdIn
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

