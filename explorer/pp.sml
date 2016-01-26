PolyML.SaveState.loadState"heap";
load"buildPP";
open buildPP

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
