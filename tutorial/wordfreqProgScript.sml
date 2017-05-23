(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble
     ml_translatorLib cfTacticsLib basisFunctionsLib basisProgTheory
     wordfreqTheory

(* TODO: simplify the required includes (translator, basis, CF) for such examples *)

val _ = new_theory "wordfreqProg";

val _ = translation_extends"basisProg";

(* TODO:
  given that this is also used in grep,
  should we include it in the basis? *)

val res = translate balanced_mapTheory.lookup_def
val res = translate balanced_mapTheory.singleton_def
val res = translate balanced_mapTheory.ratio_def
val res = translate balanced_mapTheory.size_def
val res = translate balanced_mapTheory.delta_def
val res = translate balanced_mapTheory.balanceL_def
val res = translate balanced_mapTheory.balanceR_def
val res = translate balanced_mapTheory.insert_def

val res = translate lookup0_def;
val res = translate insert_word_def;
(* TODO: want this in the basis *)
val res = translate stringTheory.isSpace_def
(* -- *)
val res = translate insert_line_def;

(* An imperative higher-order function for applying a function to every element
   in a bst in order *)

(* TODO: explain process_topdecs, CakeML syntax etc. *)

(* TODO: possible extension: pad the word so the colons will line up *)

val format_output_def = Define`
  format_output k v = concat [k; strlit": "; toString (&v); strlit"\n"]`;

(* TODO: stick with a first-order version of this instead? *)

val app_in_order = process_topdecs`
  fun app_in_order f t =
  case t of
    Tip => ()
  | Bin (_,k,v,l,r) =>
      (f k v; app_in_order f l; app_in_order f r)`;
val () = append_prog app_in_order;

(* TODO: how do you debug a definition like this that fails to process?
I tried processing one internal declaration at a time (deleting the others)
val wordfreq = process_topdecs`
  fun wordfreq _ =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val _ = FileIO.close fd
      fun print_output k v = print (format_output k v)
    in
      app_in_order print_output t
    end`;
*)

val wordfreq = process_topdecs`
  fun wordfreq u =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val u = FileIO.close fd
      fun print_output k v = print (format_output k v)
    in
      app_in_order print_output t
    end`;
val () = append_prog wordfreq;

(* TODO: explain p:'ffi ffi_proj, or make it simpler *)

(*
val app_in_order_spec = Q.store_thm("app_in_order_spec",
  `BALANCED_MAP_BALANCED_MAP_TYPE kty vty t tv ∧
   (∀n kv vv.
      n < LENGTH (toAscList t) ∧
      kty (FST (EL n (toAscList t))) kv ∧
      vty (SND (EL n (toAscList t))) vv
      ⇒
        app p fv [kv; vv] (P (TAKE n (toAscList t)))
          (POSTv uv. &UNIT_TYPE () uv * P (TAKE (n+1) (toAscList t))))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"app_in_order"(get_ml_prog_state())) [fv; tv]
     (P [])
     (POSTv uv. &UNIT_TYPE () uv *
                P (toAscList t))`,
  rw[] \\
  Induct_on`t`
*)

val _ = export_theory();
