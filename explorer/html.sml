(* Code originally comes from Anthony Fox's ARM model web interface. *)
structure html =
struct
open HolKernel Parse
fun quote_to_string q =
   let
      fun strip_loc s =
         let
            val (l,r) = Substring.position "*)" (Substring.full s)
         in
            if Substring.string r = ""
               then Substring.string l
            else String.extract (Substring.string r,2,NONE)
         end
      fun recurse [] r = r
        | recurse (QUOTE s :: t) r = recurse t (r ^ strip_loc s)
        | recurse (ANTIQUOTE s :: t) r = recurse t (r ^ s)
   in
      recurse q ""
   end

local
   val () = set_trace "pp_avoids_symbol_merges" 0
   val tmg = Parse.term_grammar()
   val tyg = Parse.type_grammar()
   fun t2s back n = HOLPP.pp_to_string n (term_pp.pp_term tmg tyg back)
in
   val term_to_html_string = t2s PPBackEnd.html_terminal
   fun thm_to_html_string n =
      with_flag (current_backend,PPBackEnd.html_terminal)
         (HOLPP.pp_to_string n Parse.pp_thm)
end

structure Html =
struct

  type attribs = (string * string) list
  datatype html = Element of string * bool * html * html list
                | Attributes of attribs
                | Sequence of html list
                | String of string
                | Preformatted of string

  structure Inline =
  struct
    local
      fun assign (s,v) = String.concat [s,"=",Lib.quote v]
      val assigns = String.concat o (Lib.separate " ") o (List.map assign)
    in
      fun inline n [] s = String.concat ["<",n,">",s,"</",n,">"]
        | inline n l s = String.concat ["<",n," ",assigns l,">",s,"</",n,">"]

      fun link l src = inline "a" (("href",src)::l)
      val span = inline "span"

      fun tag sep escape f s =
         let
            val l = String.fields (equal sep) s
            val l =
               Lib.mapi
                  (fn i => fn v =>
                     let
                        val h = if escape then PPBackEnd.html_escape v else v
                     in
                        if i mod 2 = 0 then h else f h
                     end) l
         in
            String (String.concat l)
         end
    end
  end

  type page = {title : string,
               css : string option,
               javascript : string option,
               body : attribs * html list}
  local
    local
      fun assign (s,v) = String.concat [s,"=",Lib.quote v]
      fun tag s = String.concat ["<",s,">"]
      fun otag s = String.concat ["<",s," "]
      fun ctag s = String.concat ["</",s,">"]
      fun attr (n,s) = PolyML.PrettyString (if s = "" then n else assign(n,s))
      fun front l = List.take (l, List.length l - 1)
      fun break_block _ _ _ c []  = PolyML.PrettyString ""
        | break_block f _ d c [e] = PolyML.PrettyBlock (0, c, [], [f (e, d)])
        | break_block f x d c l =
            let
              val pps = map (fn a => [f (a, d), PolyML.PrettyBreak x]) (front l)
              val pps = List.concat pps @ [f (List.last l, d)]
            in
              PolyML.PrettyBlock (0, c, [], pps)
            end
      fun close (n,pp) = PolyML.PrettyBlock (0, true, [],
                           [pp, PolyML.PrettyBreak (0,0),
                            PolyML.PrettyString (ctag n)])
    in
      fun html_printer d y (h : html) =
         let
           fun ps (n,Sequence []) = PolyML.PrettyString (tag n)
             | ps (n,x) = PolyML.PrettyBlock (2, false, [],
                            [PolyML.PrettyString (tag n),
                             PolyML.PrettyBreak (0,0),
                             html_printer (d + 1) y x])
           fun ps2 (n,a,x) = PolyML.PrettyBlock (2, false, [],
                               [PolyML.PrettyString (otag n),
                                html_printer (d + 1) y a,
                                PolyML.PrettyString ">"] @
                                (case x of
                                    Sequence [] => []
                                  | _ => [PolyML.PrettyBreak (0,0),
                                          html_printer (d + 1) y x]))
         in
           case h of
              Attributes [] => PolyML.PrettyString ""
            | Attributes [x] => attr x
            | Attributes l => break_block (attr o #1) (1,0) (d + 1) false l
            | String s => break_block (fn (s,_) => PolyML.PrettyString s)
                            (0,0) d true (String.tokens (Lib.equal #"\n") s)
            | Preformatted s => PolyML.PrettyBlock (0,true,[],
                                  [PolyML.PrettyString "<pre>",
                                   PolyML.PrettyString s,
                                   PolyML.PrettyString "</pre>"])
            | Sequence [] => PolyML.PrettyString ""
            | Sequence [e] => html_printer d y e
            | Sequence l => break_block (fn (x,d) => html_printer d y x) (0,0)
                              (d + 1) true l
            (*Special case for textarea with atts*)
            | Element ("textarea", c , Attributes a, [String str]) =>
                    PolyML.PrettyString (Inline.inline "textarea" a str)
            | Element (n, c, Attributes [], x) =>
                let
                   val pp = ps (n, Sequence x)
                in
                   if c then close (n,pp) else pp
                end
            | Element (n, c, a as Attributes l, x) =>
                let
                   val pp = ps2 (n, a, Sequence x)
                in
                   if c then close (n,pp) else pp
                end
            | _ => PolyML.PrettyString "??"
         end
    end

    fun a n (l,h) = Element (n,true,Attributes l,[h])
    fun b n h     = Element (n,true,Attributes [],h)
    fun c n h     = b n [h]
  in
    val HEAD         = b "head"
    fun BODY (a,h)   = Element ("body",true,Attributes a,h)
    val PRE          = b "body"
    val DIV          = a "div"
    val SPAN         = a "span"
    val A            = a "a"
    val UL           = a "ul"
    fun LI s         = Element ("li",false,Attributes [],[s])
    fun LABEL (id,s) = Element ("label",true,Attributes [("for",id)],[String s])
    fun T n s        = Preformatted (term_to_html_string n s)
    fun THM n s      = Preformatted (thm_to_html_string n s)
    val TITLE        = c "title" o String
    fun H (i,a,s)    = Element ("h" ^ Int.toString i, true,
                         Attributes a, [String s])
    fun FORM (x,l)   = Element ("form",true,Attributes x,l)
    fun INPUT x      = Element ("input",false,Attributes x,[])
    fun SELECT (x,l) = Element ("select",true,Attributes x,l)
    fun OPTION (x,s) = a "option" (x,String s)
    val COLGROUP     = b "colgroup"
    fun COL x        = Element ("col",false,Attributes x,[])
    fun TABLE (x,l)  = Element ("table",true,Attributes x,l)
    val THEAD        = b "thead"
    val TFOOT        = b "tfoot"
    val TBODY        = b "tbody"
    val CAPTION      = c "caption"
    val TH           = a "th"
    val TD           = a "td"
    fun TR (x,l)     = Element ("tr",true,Attributes x,l)
    val PAR          = c "p"
    fun META x       = Element ("meta",false,Attributes x,[])
    val BR           = Element ("br",false,Attributes [],[])
    fun P s          = Element ("p",false,Attributes [],[s])
    val PARS         = Sequence o map P
    fun CSS s        = a "style" ([("type","text/css")],String s)
    fun LINK_CSS s   = Element ("link",false,
                         Attributes [("href",s),("rel","stylesheet"),
                          ("type","text/css")],[])
    fun JAVASCRIPT s = Element ("script",true,
                         Attributes [("src",s),("type","text/javascript")],[])
    fun JSINLINE s   = a "script" ([("type","text/javascript")],String s)
    val NOSCRIPT     = c "noscript"
    fun HTML (h,a,bd)  = b "html" [HEAD h, BODY (a,bd)]
    fun TEXTAREA (a,s) = Element ("textarea",true,Attributes a,[String s])

    fun print_html (h:html) =
      PolyML.prettyPrint (print, 80) (PolyML.prettyRepresentation (h,100))

    fun output_html filename (h:html) =
       let
          val ostrm = TextIO.openOut filename
          fun out s = TextIO.output(ostrm, s)
       in
          PolyML.prettyPrint (out, 80) (PolyML.prettyRepresentation (h,100))
          before TextIO.closeOut ostrm
       end

    val test_location = ref NONE : string option ref

    fun page (p:page) =
       let
          val (a,b) = #body p
          val h = HTML (META [("http-equiv", "content-type"),
                              ("content", "text/html; charset=UTF-8")] ::
                        TITLE (#title p) ::
                        (case #css p of
                            SOME c => [LINK_CSS c]
                          | NONE => []) @
                        (case #javascript p of
                            SOME j => [JAVASCRIPT j]
                          | NONE => []),a,b)
       in
          case !test_location of
             SOME loc => output_html loc h
           | NONE     => print_html h
       end

    val _ = PolyML.addPrettyPrinter html_printer;
  end
end;

local
  fun hex_to_char s =
    case StringCvt.scanString (Int.scan StringCvt.HEX) s of
       SOME i => SOME (Char.chr i)
     | NONE   => NONE
in
  fun url_decode s =
     let
       fun loop [] s = String.implode (List.rev s)
         | loop (#"%" :: m :: n :: l) s =
            (case hex_to_char (String.implode [m,n]) of
                SOME c => loop l (c :: s)
              | NONE   => loop (m :: n :: l) (#"%" :: s))
         | loop (#"+" :: l) s = loop l (#" " :: s)
         | loop (c :: l) s = loop l (c :: s)
     in
       loop (String.explode s) []
     end
end

val url_encode =
  String.translate
    (fn c =>
      if c = #" "
         then "+"
      else if Char.isAlphaNum c
         then String.str c
      else "%" ^ Int.fmt StringCvt.HEX (Char.ord c))

(* example:
let
   open Html
in
   page {title = "The Title",
         css = NONE,
         javascript = NONE,
         body = ([], [DIV ([("style","font-size: 14px;")],
                           String (quote_to_string `This is some text.`))])}
end
*)
end;
