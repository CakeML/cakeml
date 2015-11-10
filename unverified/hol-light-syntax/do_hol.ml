(*Run on HOL Light*)
#use "setup.ml";;
#use "tin.ml";;
#use "bake.ml";;
#use "back.ml";;
#use "print.ml";;

(*Process OCaml from source files and keep a list of processed items*)

let str_items = ref ([]:ml_str_item list);;

let env = ref(!Toploop.toplevel_env)
let execute = ref false;;

let rec process_file name =
  Warnings.parse_options false "-8";
  let filename = Misc.find_in_path !Config.load_path name in
  let ic = open_in_bin filename in
  let lb = Lexing.from_channel ic in
  Location.init lb filename;
  let oldname = !Location.input_name in
  Location.input_name := filename;
  let phrases = try !Toploop.parse_use_file lb
    with e -> Location.input_name := oldname; raise e in
  Location.input_name := oldname;
  close_in ic;
  List.iter (fun phrase ->
      let str =
        (match phrase with
         | Parsetree.Ptop_def s ->
             let (str,_,newenv) = Typemod.type_toplevel_phrase !env s in
             env:=newenv;
	     if(!execute) then 
               ignore (Toploop.execute_phrase false
                       Format.std_formatter phrase);
	     List.map str_item_of str.str_items;
	 | Parsetree.Ptop_dir ("install_printer",Parsetree.Pdir_ident i) ->
             [Str_install_printer (string_of_longident i)]
         | _ -> raise (Unknown_toplevel_phrase phrase)) in
    str_items := !str_items@str)
    phrases;
  Warnings.parse_options false "+8";;

use_file := process_file;;

let start_time = Sys.time();;

print_string "Parsing & Executing...";;

execute:=true;;

(*Load the HOL Light state only*)
(*List.iter (fun s ->
  str_items := [];
  print_string (s^"\n");
  loads (s^".ml") )
  [
  "lib";
  "fusion";
  "basics";
  "nets";
  "printer";
  "preterm";
  "parser";];;
*)

let print_sml name_sml baked= 
  let ch = open_out name_sml in
    sml_ppf := Format.formatter_of_out_channel ch;
    Format.pp_open_vbox !sml_ppf 0;
    sml_print "use \"glob.sml\";";
    sml_emptyline();
    (try iter (fun s -> sml_print_str_item ";" s; Format.print_flush ()) baked
    with ex -> Format.print_flush (); close_out ch; sml_ppf := Format.std_formatter;
               raise ex);
    Format.pp_close_box !sml_ppf ();
    sml_ppf := Format.std_formatter;
    close_out ch;;

List.iter (fun (s,b) -> 
  str_items := [];
  print_string (s^"\n");
  loads (s^".ml");
  (if b then print_sml ("sml/"^s^".sml") (flatten (map bake_str_item !str_items)))
  ) [
  "lib",true;
  "fusion",true;
  "basics",true;
  "nets",false; (*Removed equality type*)
  "printer",false; (*Custom printer.sml*)
  "preterm",true;
  "parser",false; (*Custom changes to parser.sml*)
  "equal",true;
  "bool",true;
  "drule",true;
  "tactics",true;
  "itab",true;
  "simp",true;
  "theorems",true;
  "ind_defs",true;
  "class",true;
  "trivia",true;
  "canon",true;
  "meson",true;
  "quot",true;
  "pair",true;
  "nums",true;
  "recursion",true;
  "arith",true;
  "wf",true;
  "calc_num",true;
  "normalizer",true;
  "grobner",true;
  "ind_types",true;
  "lists",true;
  "realax",true;
  "calc_int",true;
  "realarith",true;
  "real",true;
  "calc_rat",true;
  "int",true;
  "sets",true;
  "iterate",true;
  "cart",true;
  "define",true;
];;


(*Back into OCaml*)
(*
let name_mangled = "hol_mangled";;

print_string ("Back to OCaml... "^name_mangled);;

let ch = open_out name_mangled in
ocaml_ppf := Format.formatter_of_out_channel ch;
(try iter (fun s -> ocaml_print_str_item ";;\n\n" s; Format.print_flush ())
  str_items_baked
with ex -> Format.print_flush (); close_out ch; ocaml_ppf := Format.std_formatter;
  raise ex);
close_out ch;
ocaml_ppf := Format.std_formatter;;
*)
(*Quick check that it parses back...

Hashtbl.reset typ_abbrevs;;
str_items := [];;
time process_file name_mangled;;

str_items_baked = !str_items;;
*)

