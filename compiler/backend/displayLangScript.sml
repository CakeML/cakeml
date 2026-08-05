(*
  displayLang is a stepping stone before pretty printing any of
  the compiler's intermediate languages for inspection by humans. The
  design of displayLang is intentionally very simple. The language
  supports Tuples, Items (e.g. datatype constructors), and Lists.
*)
Theory displayLang
Ancestors
  jsonLang mlint backend_common mlsexp (* for str_tree *)
Libs
  preamble

Datatype:
  sExp =
    | Item (tra option) mlstring (sExp list)
    | String mlstring
    | Tuple (sExp list)
    | List (sExp list)
End

val sExp_size_def = fetch "-" "sExp_size_def";

(* display_to_json *)
Definition trace_to_json_def:
  (trace_to_json (backend_common$Cons tra num) =
    Object [(«name», String «Cons»);
      («num», String (toString num));
      («trace», trace_to_json tra)])
  /\
  (trace_to_json (Union tra1 tra2) =
    Object [(«name», String «Union»);
      («trace1», trace_to_json tra1);
      («trace2», trace_to_json tra2)])
  /\
  (trace_to_json (SourceLoc sr scc er ec) =
    let arr = MAP Int (MAP (&)  [ sr; scc; er; ec ]) in
      Object [(«name», String «SourcePos»);
        («pos», Array arr)])
  /\
  (* TODO: cancel entire trace when None, or verify that None will always be at
  * the top level of a trace. *)
  (trace_to_json None = Null)
End

Theorem MEM_sExp_size:
  !es a. MEM a es ==> sExp_size a < sExp1_size es
Proof
  Induct \\ fs [] \\ rw [sExp_size_def] \\ fs [] \\ res_tac \\ fs []
QED

(* Converts a display expression to JSON *)
Definition display_to_json_def:
  (display_to_json (Item tra name es) =
    let es' = MAP display_to_json es in
    let props = [(«name», String name); («args», Array es')] in
    let props' = case tra of
                   | NONE => props
                   | SOME t => («trace», trace_to_json t)::props in
      Object props')
   /\
  (display_to_json (String s : sExp) = String s) /\
  (display_to_json (Tuple es) =
    let es' = MAP display_to_json es in
      Object [(«isTuple», Bool T); («elements», Array es')])
  /\
   (display_to_json (List es) = Array (MAP display_to_json es))
End

Definition display_to_str_tree_def:
  (display_to_str_tree (Item tra name es) =
     Trees (Str name :: display_to_str_tree_list es)) ∧
  (display_to_str_tree (String s : sExp) = Str s) /\
  (display_to_str_tree (Tuple es) =
     if NULL es then Str «()»
     else Trees (display_to_str_tree_list es)) ∧
  (display_to_str_tree (List es) =
     if NULL es then Str «()»
     else Trees (MAP GrabLine (display_to_str_tree_list es))) ∧
  (display_to_str_tree_list [] = []) ∧
  (display_to_str_tree_list (x::xs) =
    display_to_str_tree x :: display_to_str_tree_list xs)
End
