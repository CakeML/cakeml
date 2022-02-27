(* ------------------------------------------------------------------------- *
 * Prelude
 * ------------------------------------------------------------------------- *)

let ref x = Ref x;;

let (/) = div;;
let (-.) = Double.(-);;
let (+.) = Double.(+);;
let ( *.) = Double.( * );;
let (/.) = Double.(/);;

let failwith msg = raise (Failure msg);;

let pp_exn e =
  match e with
  | Chr  -> Pretty_printer.token "Chr"
  | Div  -> Pretty_printer.token "Div"
  | Bind -> Pretty_printer.token "Bind"
  | Subscript -> Pretty_printer.token "Subscript"
  | Interrupt -> Pretty_printer.token "Interrupt"
  | Failure s -> Pretty_printer.app_block "Failure" [Pretty_printer.pp_string s]
  | _ -> Pretty_printer.token "<exn>";;

(* Some conversions in OCaml style: *)

let string_of_int = Int.toString;;
let string_of_float = Double.toString;;
let int_of_string = Option.valOf o Int.fromString;;

(* Left shifting integers. HOL Light expects these to not be bigints, so I
   suppose we can just map in and out of word64. *)
let (lsl) x y =
  Word64.toInt (Word64.(<<) (Word64.fromInt x) y);;
let (lsr) x y =
  Word64.toInt (Word64.(>>) (Word64.fromInt x) y);;

let (land) x y =
  Word64.toInt (Word64.andb (Word64.fromInt x) (Word64.fromInt y));;

(* TODO Need a better string escaping thing. *)
let string_escaped =
  let rec escape cs =
    match cs with
    | [] -> []
    | '\\'::l -> '\\'::'\\'::escape l
    | '\b'::l -> '\\'::'b'::escape l
    | '\t'::l -> '\\'::'t'::escape l
    | '\n'::l -> '\\'::'n'::escape l
    | c::l -> c::escape l in
  fun s -> String.implode (escape (String.explode s));;

(* Add printers for things we deal with differently, e.g. bool, app_list, etc *)

let pp_bool b = Pretty_printer.token (if b then "true" else "false");;

let pp_char c =
  Pretty_printer.token ("'" ^ string_escaped (String.str c)  ^ "'");;

let rec pp_app_list f xs =
  match xs with
  | Nil -> Pretty_printer.token "Nil"
  | List xs ->
      Pretty_printer.app_block "List" [Pretty_printer.pp_list f xs]
  | Append (l, r) ->
      Pretty_printer.app_block "Append" [
        Pretty_printer.tuple [pp_app_list f l; pp_app_list f r]]
;;

let abs x = if x < 0 then -x else x;;

let ignore x = x; ();;

(* ------------------------------------------------------------------------- *
 * Helpful banner
 * ------------------------------------------------------------------------- *)

let _ = List.app print [
  "\n";
  "---------------------------------------\n";
  "                Candle                 \n";
  "---------------------------------------\n";
  "\n";
  "\n";
  ];;

(* ------------------------------------------------------------------------- *
 * Operations on filenames
 * ------------------------------------------------------------------------- *)

module Filename = struct
  let currentDir = ".";;
  let parentDir = "..";;
  let dirSep = "/";;
  let isRelative fname =
    try String.sub fname 0 <> '/'
    with Subscript -> true;;
  let concat dname fname =
    if dname = currentDir then fname
    else String.concat [dname; dirSep; fname];;
  let (basename, dirname) =
    let trimSep s = (* trim trailing separators *)
      let len = String.size s in
      let dsl = String.size dirSep in
      let rec search i =
        if i < dsl then s
        else if String.substring s i dsl = dirSep then
          search (i - dsl)
        else
          String.substring s 0 i in
      search (len - 1) in
    let splitPath s =
      let len = String.size s in
      let dsl = String.size dirSep in
      let s = trimSep s in
      let rec search i =
        if i <= dsl then
          (currentDir, s)
        else if String.substring s i dsl = dirSep then
          (String.substring s 0 (i - 1),
           String.extract s (i + dsl) None)
        else
          search (i - dsl) in
      search (len - 1) in
    ((fun s -> let (_, b) = splitPath s in b),
     (fun s -> let (d, _) = splitPath s in d))
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Double-ended functional queue
 * ------------------------------------------------------------------------- *)

module Queue = struct
  type 'a queue = 'a list * 'a list;;
  let push_back (xs, ys) y = (xs, y::ys);;
  let push_front (xs, ys) x = (x::xs, ys);;
  let rec dequeue (xs, ys) =
    match xs with
    | x::xs -> Some (x, (xs, ys))
    | [] ->
        match ys with
        | [] -> None
        | _ -> dequeue (List.rev ys, []);;
  let empty = ([], []);;
  let flush (xs, ys) = xs @ List.rev ys;;
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Imperative wrapper around Queue
 * ------------------------------------------------------------------------- *)

module Buffer = struct
  type 'a buffer = 'a Queue.queue ref;;
  let push_back q x = q := Queue.push_back (!q) x;;
  let push_front q x = q := Queue.push_front (!q) x;;
  let dequeue q =
    match Queue.dequeue (!q) with
    | None -> None
    | Some (x, q') ->
        q := q';
        Some x;;
  let empty () = ref Queue.empty;;
  let flush q =
    let els = Queue.flush (!q) in
    q := Queue.empty;
    els
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Operations on strings
 * ------------------------------------------------------------------------- *)

let trimLeft str =
  let rec nom n =
    if n >= String.size str then str
    else if Char.isSpace (String.sub str n) then nom (n + 1)
    else String.extract str n None in
  nom 0
  ;;

let trimRight str =
  let rec nom n =
    if n < 1 then str
    else if Char.isSpace (String.sub str n) then nom (n - 1)
    else String.substring str 0 (n + 1) in
  nom (String.size str - 1)
;;

(* ------------------------------------------------------------------------- *
 * Operations on files
 * ------------------------------------------------------------------------- *)

let isFile fname =
  try let ins = Text_io.b_openIn fname in
      Text_io.b_closeIn ins;
      true
  with Text_io.Bad_file_name -> false
;;

(* ------------------------------------------------------------------------- *
 * Lexer for enough parts of the language to keep track on whether semi-colons
 * appear on the top-level or not.
 * ------------------------------------------------------------------------- *)

module Lexer = struct

type directive =
  | D_load
  | D_need
  | D_use
;;

let string_of_directive d =
  match d with
  | D_load -> "load"
  | D_need -> "need"
  | D_use -> "use"
;;

type token =
  | T_begin | T_end | T_struct | T_sig | T_semis | T_newline
  | T_other of string
  | T_symb of string
  | T_directive of directive * string
  | T_comment of string
  | T_string of string
  | T_quote of string
  | T_char of string
  | T_number of string
  | T_spaces of string
  | T_done (* pseudo-token at switch from loading to user input *)
;;

let string_of_token unquote tok =
  match tok with
  | T_begin -> "begin"
  | T_end -> "end"
  | T_struct -> "struct"
  | T_sig -> "sig"
  | T_semis -> ";;"
  | T_newline -> "\n"
  | T_string s -> "\"" ^ s ^ "\""
  | T_quote s ->
      begin
        match unquote with
        | None -> "`" ^ s ^ "`"
        | Some f -> "(" ^ f s ^ ")"
      end
  | T_char s -> "'" ^ s ^ "'"
  | T_directive (d, f) ->
      String.concat ["#"; string_of_directive d; " "; "\""; f; "\";;"]
  | T_comment s | T_other s | T_symb s | T_number s | T_spaces s -> s
  | T_done -> "(* shouldn't happen *)"
;;

let scan nextChar peekChar =
  let quoteSym c = c = '`' in
  let tok_from_keyword =
    let keywords = [
      "begin",  T_begin;
      "end",    T_end;
      "struct", T_struct;
      "sig",    T_sig;
    ] in
    fun s -> match Alist.lookup keywords s with
             | None -> T_other s
             | Some tok -> tok in
  let is_symbol =
    let symchars = String.explode "#$&*+-/=>@^|~!?%<:.()[]{}," in
    fun c -> List.exists (fun x -> x = c) symchars in
  let is_alpha c =
    Char.(<=) 'a' c && Char.(<=) c 'z' ||
    Char.(<=) 'A' c && Char.(<=) c 'Z' in
  let is_digit c =
    Char.(<=) '0' c && Char.(<=) c '9' in
  let is_name_char c =
    is_alpha c || is_digit c || c = '_' || c = '\'' in
  let is_int_char c =
    is_digit c || c = '_' || c = 'l' || c = 'L' || c = 'n' in
  let scan_while acc pred =
    let rec nom acc =
      Interrupt.check ();
      match peekChar () with
      | None -> None
      | Some c when pred c ->
          nextChar ();
          nom (c::acc)
      | _ -> Some (String.implode (List.rev acc)) in
    nom acc in
  let scan_comment () =
    let rec nom acc level =
      Interrupt.check ();
      if level = 0 then
        Some (String.implode ('('::'*'::List.rev acc))
      else
        match nextChar () with
        | Some '(' ->
            begin
              match peekChar () with
              | Some '*' ->
                  nextChar ();
                  nom ('*'::'('::acc) (level + 1)
              | _ -> nom ('('::acc) level
            end
        | Some '*' ->
            begin
              match peekChar () with
              | Some ')' ->
                  nextChar ();
                  nom (')'::'*'::acc) (level - 1)
              | _ -> nom ('*'::acc) level
            end
        | Some c -> nom (c::acc) level
        | None -> None in
    nom [] 1 in
  let scan_name c =
    match scan_while [c] is_name_char with
    | None -> None
    | Some s -> Some (tok_from_keyword s) in
  let scan_symb c =
    Option.map (fun s -> T_symb s)
               (scan_while [c] is_symbol) in
  let scan_int c =
    Option.map (fun s -> T_number s)
               (scan_while [c] is_int_char) in
  let scan_quote () =
    match scan_while [] (not o quoteSym) with
    | None -> None
    | Some str ->
        nextChar ();
        Some (T_quote str) in
  let skip_line () =
    scan_while [] (fun x -> x <> '\n');
    nextChar () in
  let scan_spaces c =
    Option.map (fun s -> T_spaces s)
               (scan_while [c] (fun c -> c <> '\n' && Char.isSpace c)) in
  let dir_from_string =
    let dirs = [
      "load", D_load;
      "need", D_need;
      "use",  D_use ] in
    Alist.lookup dirs in
  let scan_directive () = (* TODO *)
    match scan_while [] (fun x -> x <> ';') with
    | None -> None
    | Some s ->
        nextChar ();
        match peekChar () with
        | None -> Some (T_other ("#" ^ s ^ ";"))
        | Some c ->
            if c <> ';' then
              Some (T_other ("#" ^ s ^ ";" ^ String.str c))
            else
              begin
                nextChar ();
                match String.fields (fun x -> x = '"') s with
                | [dir; fname; rest] ->
                    let dir = trimRight dir in
                    let rest = trimLeft rest in
                    if rest <> "" then Some (T_other ("#" ^ s ^ ";;")) else
                      begin
                        match dir_from_string dir with
                        | None -> Some (T_other ("#" ^ s ^ ";;"))
                        | Some d -> Some (T_directive (d, fname))
                      end
                | _ -> Some (T_other ("#" ^ s ^ ";;"))
              end in
  let scan_escaped ch =
    let rec nom acc =
      Interrupt.check ();
      match nextChar () with
      | None -> None
      | Some '\\' ->
          begin
            match nextChar () with
            | None -> nom ('\\'::acc)
            | Some c -> nom (c::'\\'::acc)
          end
      | Some c when c = ch -> Some (String.implode (List.rev acc))
      | Some c -> nom (c::acc) in
    nom [] in
  let scan_strlit () =
    Option.map (fun s -> T_string s)
               (scan_escaped '"') in
  let scan_charlit () =
    Option.map (fun s -> T_char s)
               (scan_escaped '\'') in
  let rec nextToken () =
    match nextChar () with
    | None -> None
    (* Attempt to scan semis *)
    | Some ';' ->
        begin
          match peekChar () with
          | Some ';' ->
              nextChar ();
              Some T_semis
          | _ -> scan_symb ';'
        end
    (* Attempt to scan comment *)
    | Some '(' ->
        begin
          match peekChar () with
          | Some '*' ->
              nextChar ();
              begin
                match scan_comment () with
                | None -> Some (T_symb "(*")
                | Some str -> Some (T_comment str)
              end
          | _ -> Some (T_symb "(")
        end
    (* Attempt to scan char literal *)
    | Some '\'' -> scan_charlit ()
    (* Attempt to scan string literal *)
    | Some '"' -> scan_strlit ()
    (* Attempt to scan load directive *)
    | Some '#' -> scan_directive ()
    (* Newlines *)
    | Some '\n' -> Some T_newline
    (* Anything else *)
    | Some c ->
        if quoteSym c then
          scan_quote ()
        else if is_digit c then
          scan_int c
        else if is_symbol c then
          scan_symb c
        else if is_alpha c || c = '_' then
          scan_name c
        else if Char.isSpace c then
          scan_spaces c
        else
          Some (T_other (String.str c)) in
  fun () -> Interrupt.check (); nextToken ()
;;

end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * CakeML struct: setting up REPL, reading/loading.
 * ------------------------------------------------------------------------- *)

module Cakeml = struct

let loadPath = ref [Filename.currentDir];;
let (input1 : (unit -> char option) ref) =
  ref (fun () -> Text_io.input1 Text_io.stdIn);;

let prompt1 = ref "# ";;
let prompt2 = ref "  ";;
let userInput = ref true;;

let unquote = ref (fun (s: string) -> s);;

exception Repl_error;;

let () =
  let prompt = ref (!prompt2) in
  let peekChar, nextChar =
    let lookahead = ref (None: char option) in
    let peek () =
      match !lookahead with
      | Some c -> Some c
      | None ->
          match (!input1) () with
          | None -> None
          | Some c ->
              lookahead := Some c;
              Some c in
    let next () =
      match !lookahead with
      | None -> (!input1) ()
      | Some c ->
          lookahead := None;
          Some c in
    peek, next in
  (* Load files from disk and keep track on what has been loaded.
   *)
  let load =
    let loadedFiles = (ref [] : string list ref) in
    let loadMsg s = print ("- Loading " ^ s ^ "\n") in
    let load_use fname =
      loadMsg fname;
      Text_io.b_inputLinesFrom fname in
    let load fname =
      loadMsg fname;
      match Text_io.b_inputLinesFrom fname with
      | None -> None
      | Some lns ->
          begin
            if not (List.exists (fun x -> x = fname) (!loadedFiles)) then
             loadedFiles := fname :: !loadedFiles
          end;
          Some lns in
    let load1 fname =
      if List.exists (fun x -> x = fname) (!loadedFiles) then
        begin
          print ("- Already loaded: " ^ fname ^ "\n");
          None
        end
      else
        load fname in
    let loadOnPath pragma fname =
      let paths = List.map (fun p -> Filename.concat p fname) (!loadPath) in
      match List.find isFile paths with
      | None ->
          print ("- No such file: " ^ fname ^ "\n");
          Repl.nextString := "";
          failwith ("No such file : " ^ fname)
      | Some fname ->
          let loader = match pragma with
                       | Lexer.D_load -> load
                       | Lexer.D_need -> load1
                       | Lexer.D_use -> load_use in
          (match loader fname with
          | None -> []
          | Some ls -> ls) in
    loadOnPath in
  (* Instantiate lexer *)
  let scan1 = Lexer.scan nextChar peekChar in
  (* Enqueue input here *)
  let input_buffer = (Buffer.empty () : Lexer.token Buffer.buffer) in
  (* Set up a nextChar/peekChar pair on the list of lines, lex all of it,
   * and then stuff it all into input_buffer.
   *)
  let scan_lines lines =
    let inp = ref lines in
    let idx = ref 0 in
    let rec peekChar () =
      match !inp with
      | [] -> None
      | s::ss ->
          try Some (String.sub s (!idx))
          with Subscript ->
            (* Look into next string. It should not be empty. *)
            match ss with
            | [] -> None
            | s::ss -> try Some (String.sub s 0)
                       with Subscript -> None in
    let rec nextChar () =
      match !inp with
      | [] -> None
      | s::ss ->
          try let res = String.sub s (!idx) in
              idx := (!idx) + 1;
              Some res
          with Subscript ->
            idx := 0;
            inp := ss;
            nextChar () in
    let scan = Lexer.scan nextChar peekChar in
    let rec nom acc =
      match scan () with
      | None -> List.app (Buffer.push_front input_buffer) acc
      | Some tok -> nom (tok::acc) in
    nom [];
    Buffer.push_back input_buffer Lexer.T_done in
  let next () =
    match Buffer.dequeue input_buffer with
    | Some tok -> Some tok
    | None -> scan1 () in
  let output_buffer = (Buffer.empty () : Lexer.token Buffer.buffer) in
  let rec scan level =
    try match next () with
        | None -> None
        | Some (Lexer.T_done) ->
            userInput := true;
            scan level
        | Some (Lexer.T_directive (dir, fname)) ->
            let lines = load dir fname in
            if List.null lines then scan level else
              begin
                userInput := false;
                scan_lines lines;
                scan level
              end
        | Some tok ->
            Buffer.push_back output_buffer tok;
            match tok with
            | Lexer.T_begin | Lexer.T_struct | Lexer.T_sig ->
                scan (level + 1)
            | Lexer.T_end -> scan (level - 1)
            | Lexer.T_semis when level = 0 ->
                prompt := !prompt1;
                Some (Buffer.flush output_buffer)
            | Lexer.T_newline when !userInput ->
                print (!prompt);
                prompt := !prompt2;
                scan level
            | _ -> scan level
    with Interrupt ->
      print "Compilation interrupted\n";
      raise Repl_error in
  let checkError () =
    let err = !Repl.errorMessage in
    Repl.errorMessage := "";
    if err <> "" then raise Repl_error in
  let next () =
    try checkError ();
        match scan 0 with
        | None ->
            Repl.isEOF := true;
            Repl.nextString := ""
        | Some ts ->
            Repl.isEOF := false;
            Repl.nextString :=
              String.concat
                (List.map (Lexer.string_of_token (Some (!unquote))) ts)
    with Repl_error ->
      if not (!userInput) then print (!prompt1);
      Buffer.flush input_buffer;
      Buffer.flush output_buffer;
      Repl.nextString := "" in
  Repl.readNextString := (fun () ->
    print (!prompt1);
    next ();
    Repl.readNextString := next)
;;

end;; (* struct *)

