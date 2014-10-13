(*Pretty print for bytecode, asm*)
structure miscPP =
struct
open astPP
open compute_bytecodeLib
open x64DisassembleLib
(*x64DisassembleLib.sig is missing include Abbrev*)

val miscPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_miscPP hd = miscPrettyPrinters:= (hd:: !miscPrettyPrinters)

(*Pretty Printer specifics for globals, types & exceptions*)
fun tidPrinter sys d t pg str brk blk =
  str "datatype " >>str (toString (strip (strip t)));

fun texnPrinter sys d t pg str brk blk = 
  str "exception " >>str (toString (strip (strip t)));

fun tlongPrinter pref sys d t pg str brk blk =
  let val t = rand t
      val(_,[l,r]) = strip_comb t
  in
    str pref >>str" ">> str (toString l) >> str".">>str(toString r)
  end;


val _=add_miscPP("typeidprint",``TypeId (Short x)``, genPrint tidPrinter);
val _=add_miscPP("typeexnprint",``TypeExn (Short x)``, genPrint texnPrinter);

val _=add_miscPP("typelongidprint",``TypeId (Long x y)``, genPrint (tlongPrinter "datatype"));
val _=add_miscPP("typelongexnprint",``TypeExn (Long x y)``, genPrint (tlongPrinter "exception"));

fun modmapPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let open term_pp_types PPBackEnd
      val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
      val (modname,map) = pairSyntax.dest_pair t
      val modname = toString modname
  (*Assume first is always FEMPTY*)
      val (_,ls) = finite_mapSyntax.strip_fupdate map
      fun printer [] = str""
      |   printer [x] = 
            let val (name,num) = pairSyntax.dest_pair x in 
              str (modname^"."^(toString name)^" --> ")>>sys (Top,Top,Top) d num >>add_newline
            end
      |   printer (x::xs) = printer [x] >>printer xs
  in
    (sty [FG DarkGrey] (str modname)) >>add_newline>> blk CONSISTENT 0 (printer ls)
  end;

val _=add_miscPP("modmapprint",``x:(tvarN #(tvarN |-> num))``,modmapPrint);

fun globmapPrint sys d t pg str brk blk=
   let val (name,num) = pairSyntax.dest_pair t in 
     str ((toString name)^" --> ")>>sys (Top,Top,Top) d num
   end

val _ = add_miscPP ("globmapprint",``x:(tvarN # num)``,genPrint globmapPrint);


(*Labeled bytecode*)
fun bclistPrint sys d t pg str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = str ((fn s=> if(String.isPrefix "Label" s) then s^":" else "  "^s^"") 
		               (term_to_string x)) >> str"\n"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;

val _=add_miscPP("bclistprint",``(SOME x ,(y:bc_inst list))``,genPrint bclistPrint);

(*Unlabeled bytecode*)
fun ubclistPrint sys d t pg str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms _ [] = str""
  |   printterms n [x] = str (Int.toString n) >>str":  ">> str (term_to_string x)>>str"\n"
  |   printterms n (x::xs) = (printterms n [x])>>printterms (n+1) xs
  in
    printterms 0 ls
  end;

val _=add_miscPP("ubclistprint",``(NONE ,(y:bc_inst list))``,genPrint ubclistPrint);

(*ASM*)
fun asmPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val ls = x64_disassemble t
    val maxlen = 45 (*x86 inst at most 15 bytes long so leave 45 bytes of space, could probably do with less*)
    fun pad 0 = str""
    |   pad n = str" ">>pad (n-1)
    fun printAsm [] = str""
    |   printAsm (x::xs) = case x of (hex,dis) => 
          (sty [FG DarkGrey] (str hex))>> pad (maxlen - String.size hex) >>str dis>>str"\n">>printAsm xs
    (*Hex dump*)
    (*fun print [] = str""
    |   print (x::xs) = case x of (hex,dis) => str hex>>str" ">>print xs*)
  in
    printAsm ls
  end;

val _ =add_miscPP("asmlistprint",``x:word8 list``,asmPrint);

fun enable_miscPP_verbose () = map temp_add_user_printer (!miscPrettyPrinters); 
fun enable_miscPP () = (enable_miscPP_verbose();())
fun disable_miscPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!miscPrettyPrinters);
fun disable_miscPP () = (disable_miscPP_verbose();())

end;

