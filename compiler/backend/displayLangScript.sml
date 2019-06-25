(*
  displayLang is a stepping stone when before pretty printing any of
  the compiler's intermediate languages for inspection by humans. The
  design of displayLang is intentionally very simple. The language
  supports Tuples, Items (e.g. datatype constructors), and Lists.
*)
open preamble jsonLangTheory mlintTheory backend_commonTheory;

val _ = new_theory"displayLang";

val _ = Datatype`
  sExp =
    | Item (tra option) mlstring (sExp list)
    | Tuple (sExp list)
    | List (sExp list)`;

val sExp_size_def = fetch "-" "sExp_size_def";

(* display_to_json *)
val num_to_json_def = Define`
  num_to_json n = String (explode (toString n))`;

val trace_to_json_def = Define`
  (trace_to_json (backend_common$Cons tra num) =
    Object [("name", String "Cons"); ("num", num_to_json num); ("trace", trace_to_json tra)])
  /\
  (trace_to_json (Union tra1 tra2) =
      Object [("name", String "Union"); ("trace1", trace_to_json tra1); ("trace2", trace_to_json tra2)])
  /\
  (trace_to_json (SourceLoc sr sc er ec) =
    let arr = MAP Int (MAP (&)  [ sr; sc; er; ec ]) in
      Object [("name", String "SourcePos"); ("pos", Array arr)])
  /\
  (* TODO: cancel entire trace when None, or verify that None will always be at
  * the top level of a trace. *)
  (trace_to_json None = Null)`;

Theorem MEM_sExp_size:
   !es a. MEM a es ==> sExp_size a < sExp1_size es
Proof
  Induct \\ fs [] \\ rw [sExp_size_def] \\ fs [] \\ res_tac \\ fs []
QED

(* Converts a display expression to JSON *)
val display_to_json_def = tDefine"display_to_json" `
  (display_to_json (Item tra name es) =
    let es' = MAP display_to_json es in
    let props = [("name", String (explode name)); ("args", Array es')] in
    let props' = case tra of
                   | NONE => props
                   | SOME t => ("trace", trace_to_json t)::props in
      Object props')
   /\
  (display_to_json (Tuple es) =
    let es' = MAP display_to_json es in
      Object [("isTuple", Bool T); ("elements", Array es')])
  /\
   (display_to_json (List es) = Array (MAP display_to_json es))`
  (WF_REL_TAC `measure sExp_size` \\ rw []
   \\ imp_res_tac MEM_sExp_size \\ fs []);

val _ = export_theory();
