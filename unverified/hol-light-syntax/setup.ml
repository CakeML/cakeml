(*
  This file sets up for the rest of the translation:
  - OCaml's parser for HOL Light,
  - Some filepath settings for working with the HOL Light directory
  - Copied utility functions over from HOL Light
*)

unset_jrh_lexer;;

(*From hol.ml *)

let hol_version = "2.20++";;

let hol_dir = ref
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> "");;

let temp_path = ref "/tmp";;

let use_file_hol s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let use_file = ref use_file_hol;;

let hol_expand_directory s =
  if s = "$" or s = "$/" then !hol_dir
  else if s = "$$" then "$"
  else if String.length s <= 2 then s
  else if String.sub s 0 2 = "$$" then (String.sub s 1 (String.length s - 1))
  else if String.sub s 0 2 = "$/"
  then Filename.concat (!hol_dir) (String.sub s 2 (String.length s - 2))
  else s;;

let load_path = ref ["."; "$"];;

let loaded_files = ref [];;

let file_on_path p s =
  if not (Filename.is_relative s) then s else
  let p' = List.map hol_expand_directory p in
  let d = List.find (fun d -> Sys.file_exists(Filename.concat d s)) p' in
  Filename.concat (if d = "." then Sys.getcwd() else d) s;;

let load_on_path p s =
  let s' = file_on_path p s in
  let fileid = (Filename.basename s',Digest.file s') in
  (!use_file s'; loaded_files := fileid::(!loaded_files));;

let loads s = load_on_path ["$";"."] s;;

let loadt s = load_on_path (!load_path) s;;

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files)
  then Format.print_string("File \""^s^"\" already loaded\n") else loadt s;;

(*From system.ml *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;

Sys.catch_break true;;

let quotexpander s =
  if s = "" then failwith "Empty quotation" else
  let c = String.sub s 0 1 in
  if c = ":" then
    "parse_type \""^
    (String.escaped (String.sub s 1 (String.length s - 1)))^"\""
  else if c = ";" then "parse_qproof \""^(String.escaped s)^"\""
  else "parse_term \""^(String.escaped s)^"\"";;

Quotation.add "tot" (Quotation.ExStr (fun x -> quotexpander));;

include Num;;

let print_num n =
  Format.open_hbox();
  Format.print_string(string_of_num n);
  Format.close_box();;

#install_printer print_num;;

(*From lib.ml*)

open List;;

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let (o) = fun f g x -> f (g x);;

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

(*Can is slightly modified --> Changed to catchall instead of Failure _*)
let can f x = try (f x; true) with _ -> false;;

set_jrh_lexer;;

