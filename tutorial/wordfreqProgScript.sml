(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble
     ml_translatorLib cfTacticsLib basisFunctionsLib ioProgLib basisProgTheory
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

(* TODO: possible extension: pad the word so the colons will line up *)
val format_output_def = Define`
  format_output (k,v) = concat [k; strlit": "; toString (&v); strlit"\n"]`;
val res = translate format_output_def;

(* TODO: explain process_topdecs, CakeML syntax etc. *)

(* TODO: do something like this as an exercise?

(* An imperative higher-order function for applying a function to every element
   in a bst in order *)

val app_in_order = process_topdecs`
  fun app_in_order f t =
  case t of
    Tip => ()
  | Bin (_,k,v,l,r) =>
      (f k v; app_in_order f l; app_in_order f r)`;
val () = append_prog app_in_order;

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

*)

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
    in
      List.app (print o format_output) (toAscList t)
    end`;

val () = append_prog wordfreq;

(* Now we state and prove a correctness theorem for the wordfreq program *)

val st = get_ml_prog_state();

val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ls. PERM ls (all_words file_contents) ∧ SORTED $<= ls ∧
         output = FLAT (MAP (λw. explode (format_output (implode w, frequency file_contents w))) ls)`;

(* TODO: explain p:'ffi ffi_proj, or make it simpler *)
(* TODO: explain ^ *)

(* TODO:
   this is the spec I originally devised, but it doesn't work with ioProgLib.call_thm
   could ioProgLib.call_thm be made more robust for that?
   (but note since this isn't proved, it is probably wrong)
val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `EVERY validArg cl ∧
   LENGTH cl > 1 ∧ SUM (MAP LENGTH cl) + LENGTH cl < 257 ∧
   fname = implode (EL 1 cl) ∧
   inFS_fname fs fname ∧
   wfFS fs
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (COMMANDLINE cl * ROFS fs * STDOUT out)
       (POSTv uv.
        &UNIT_TYPE () uv * COMMANDLINE cl * ROFS fs *
        (SEP_EXISTS out'.
           STDOUT (out ++ out') *
           &valid_wordfreq_output (THE (ALOOKUP fs.files fname)) out'))`,
  strip_tac \\
  xcf "wordfreq" st \\
  cheat);
*)

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `EVERY validArg cl ∧
   LENGTH cl > 1 ∧ SUM (MAP LENGTH cl) + LENGTH cl < 257 ∧
   fname = implode (EL 1 cl) ∧
   inFS_fname fs fname ∧
   wfFS fs
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (COMMANDLINE cl * ROFS fs * STDOUT out * STDERR err)
       (POSTv uv.
        &UNIT_TYPE () uv *
        (SEP_EXISTS out' err'.
           &(∃ls.
               out' = out ++ ls ∧
               valid_wordfreq_output (THE (ALOOKUP fs.files fname)) ls ∧
               err' = err) *
           STDOUT out' * STDERR err') *
        (COMMANDLINE cl * ROFS fs))`,
  strip_tac \\
  xcf "wordfreq" st \\
  cheat);

val spec = wordfreq_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "wordfreq"
val (sem_thm,prog_tm) = ioProgLib.call_thm (get_ml_prog_state ()) name spec
val wordfreq_prog_def = Define `wordfreq_prog = ^prog_tm`;

(* TODO:
  want a way to print this program out as concrete syntax (to be fed
  into the bootstrapped compiler for example) *)

val wordfreq_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM wordfreq_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[rofsFFITheory.wfFS_def,rofsFFITheory.inFS_fname_def,PULL_EXISTS]
  |> curry save_thm "wordfreq_semantics";

val _ = export_theory();
