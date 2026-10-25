(*
  Build information (CakeML and HOL4 commits and tags, and whether their
  worktrees have uncommitted or untracked changes) for embedding in
  programs, e.g. in the output of cake --version. It is read from
  build_info.txt, which update_build_info.sh keeps up to date whenever
  Holmake reads the Holmakefile in this directory. Anything that cannot be
  determined is shown as unknown, with a warning.
*)
structure buildInfoLib =
struct

open HolKernel boolLib

local
  fun warn msg = HOL_WARNING "buildInfoLib" "build_info" msg

  fun stamp_file () =
    case holpathdb.lookup_holpath {vname = "CAKEMLDIR"} of
      NONE => NONE
    | SOME dir => SOME (OS.Path.concat (dir, "misc/build_info.txt"))

  fun split_line l =
    let
      val (k, v) = Substring.position "=" (Substring.full l)
    in
      if Substring.isEmpty v then NONE
      else SOME (Substring.string k, Substring.string (Substring.triml 1 v))
    end

  (* The key=value pairs in build_info.txt; none if it cannot be read *)
  fun read_stamp () =
    case stamp_file () of
      NONE =>
        (warn "CAKEMLDIR is not registered, so build_info.txt cannot be found";
         [])
    | SOME f =>
      let
        val ins = TextIO.openIn f
        val s = TextIO.inputAll ins before TextIO.closeIn ins
      in
        List.mapPartial split_line (String.fields (fn c => c = #"\n") s)
      end
      handle IO.Io _ => (warn ("cannot read " ^ f); [])

  fun lookup kvs k =
    case List.find (fn (k', _) => k' = k) kvs of
      SOME (_, v) => if v = "" then NONE else SOME v
    | NONE => NONE

  (* e.g. "HOL4:   <commit>-dirty (<tag>)"; labels are padded to line up *)
  fun commit_line kvs name prefix =
    let
      val label = StringCvt.padRight #" " 7 (name ^ ":")
    in
      case lookup kvs (prefix ^ "_commit") of
        NONE =>
          (warn (String.concat ["the ", name, " commit is unknown"]);
           label ^ " unknown\n")
      | SOME c =>
          let
            val dirty =
              case lookup kvs (prefix ^ "_dirty") of
                SOME "0" => ""
              | SOME "1" => "-dirty"
              | _ =>
                  (warn (String.concat ["it is unknown whether the ", name,
                                        " worktree is clean"]);
                   "-dirty?")
            (* most commits are not tagged, so no warning here *)
            val tag =
              case lookup kvs (prefix ^ "_tag") of
                NONE => ""
              | SOME t => String.concat [" (", t, ")"]
          in
            String.concat [label, " ", c, dirty, tag, "\n"]
          end
    end
in

(* build_info name: the version details printed by the program called name *)
fun build_info name =
  let
    val kvs = read_stamp ()
    val date = case lookup kvs "cakeml_date" of
                 NONE =>
                   (warn "the CakeML commit date is unknown";
                    "unknown")
               | SOME d => d
  in
    String.concat
      [name, "\n\n",
       "Version details:\n",
       "Commit date: ", date, "\n\n",
       commit_line kvs "CakeML" "cakeml",
       commit_line kvs "HOL4" "hol",
       "PolyML: Poly/ML ", PolyML.Compiler.compilerVersion, "\n"]
  end

(* build_info_tm name: build_info name as an mlstring literal; needs
   mlstringTheory to be loaded (strlit is an overload for implode) *)
fun build_info_tm name =
  mk_comb (prim_mk_const {Thy = "mlstring", Name = "implode"},
           stringSyntax.fromMLstring (build_info name))

end

end
