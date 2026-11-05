(*
  Provides build information for embedding in programs,
  e.g. in the output of cake --version.
*)
structure buildInfoLib =
struct

(*
  Depends on build_info.txt, which is maintained by update_build_info.sh,
  which in turn is invoked via Holmake trickery.
*)

open HolKernel boolLib

local
  fun warn msg = HOL_WARNING "buildInfoLib" "build_info" msg

  (* Returns path to build_info.txt *)
  fun stamp_file () =
    case holpathdb.lookup_holpath {vname = "CAKEMLDIR"} of
      NONE => (
        warn "CAKEMLDIR is not registered, so build_info.txt cannot be found";
        NONE)
    | SOME dir => SOME (OS.Path.concat (dir, "misc/build_info.txt"))

  (* Converts a key=value string into a (key, value) tuple with surrounding
     whitespace trimmed. Returns NONE if the key or value is empty. *)
  fun split_line l =
    let
      val trim = Substring.dropl Char.isSpace o Substring.dropr Char.isSpace
      val (k, v) = Substring.position "=" (Substring.full l)
    in
      if Substring.isEmpty v then NONE
      else
        let
          val k = trim k
          val v = trim (Substring.triml 1 v)
        in
          if Substring.isEmpty k orelse Substring.isEmpty v then NONE
          else SOME (Substring.string k, Substring.string v)
        end
    end

  (* Converts key=value pairs in build_info.txt into an association list. *)
  fun read_stamp () =
    case stamp_file () of
      NONE => []
    | SOME f =>
      let
        val ins = TextIO.openIn f
        val s = TextIO.inputAll ins
                handle e => (TextIO.closeIn ins; raise e)
        val () = TextIO.closeIn ins
      in
        List.rev
          (List.mapPartial split_line (String.fields (fn c => c = #"\n") s))
      end
      handle IO.Io _ => (warn ("cannot read " ^ f); [])

  (* Looks up key in the association list kvs. *)
  fun lookup key kvs =
    Option.map #2 (List.find (fn (k, _) => k = key) kvs)

  (* Returns a string containing metadata for the repository name.
     Example: "HOL4:   <commit>-dirty (<tag>)" *)
  fun commit_line kvs name prefix =
    let
      fun get suffix = lookup (prefix ^ suffix) kvs
      val label = StringCvt.padRight #" " 7 (name ^ ":")
      fun line s = label ^ " " ^ s ^ "\n"
    in
      case get "_commit" of
        NONE =>
          (warn ("the " ^ name ^ " commit is unknown");
           line "unknown")
      | SOME c =>
          let
            val dirty =
              case get "_dirty" of
                SOME "0" => ""
              | SOME "1" => "-dirty"
              | _ =>
                  (warn ("it is unknown whether the " ^ name ^
                         " worktree is clean");
                   "-dirty?")
            (* most commits are not tagged, so no warning here *)
            val tag =
              case get "_tag" of
                NONE => ""
              | SOME t => " (" ^ t ^ ")"
          in
            line (c ^ dirty ^ tag)
          end
    end
in

(* Returns a string with build information about CakeML, HOL4 and PolyML.
   If name is given, it is printed as a header above the version details. *)
fun build_info name =
  let
    val kvs = read_stamp ()
    val header = case name of
                   NONE => ""
                 | SOME n => n ^ "\n\n"
    val date = case lookup "cakeml_date" kvs of
                 NONE => (warn "the CakeML commit date is unknown"; "unknown")
               | SOME d => d
  in
    String.concat
      [header,
       "Version details:\n",
       "Commit date: ", date, "\n\n",
       commit_line kvs "CakeML" "cakeml",
       commit_line kvs "HOL4" "hol",
       "PolyML: Poly/ML ", PolyML.Compiler.compilerVersion, "\n"]
  end

fun build_info_tm name =
  (* We don't use mlstringSyntax to avoid having misc to depend on mlstring *)
  mk_comb (prim_mk_const {Thy = "mlstring", Name = "implode"},
           stringSyntax.fromMLstring (build_info name))

end

end
