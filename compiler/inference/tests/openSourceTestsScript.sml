(* Complete-source regressions: parse, infer, then check observable results.
   These assertions exercise the ordinary source entry points, not hand-built ASTs. *)
Theory openSourceTests[no_sig_docs]
Ancestors
  infer_cv evaluate cmlParse lexer_fun lexer_impl
Libs
  preamble cv_transLib

val _ = cv_auto_trans inferTheory.init_config_def;

(* Match cmlTests' lazy evaluation of parser choices and case continuations. *)
val _ = computeLib.del_consts [``list_CASE``];
val _ = computeLib.add_funs [listTheory.list_case_def];
val _ = List.app
  (fn name => computeLib.upd_compset
    (fn compset => computeLib.set_skip compset name (SOME 1)))
  [``OPTION_CHOICE``, ``OPTION_BIND``, ``OPTION_IGNORE_BIND``,
   ``option_CASE``, ``list_CASE``, ``pair_CASE``, ``COND``];

fun parse_source source = let
  val _ = print ("Open source test: " ^ source ^ "\n")
  val source_tm = stringSyntax.fromMLstring source
  val parsed = rhs (concl (EVAL ``parse_prog (lexer_fun ^source_tm)``))
  val (head, args) = strip_comb parsed
in
  if same_const head ``Success`` andalso length args = 3 andalso
     listSyntax.is_nil (hd args) then List.nth (args, 1)
  else raise Fail ("Source did not parse completely: " ^ source ^
                   "\n" ^ term_to_string parsed)
end

val source_state =
  ``(ARB : unit semanticPrimitives$state) with
      <|clock := 100; refs := []; next_type_stamp := 0;
        next_exn_stamp := 0; eval_state := NONE|>``;
val source_env = ``<|v := nsEmpty; c := nsEmpty|> : v sem_env``;

fun infer_source program =
  rhs (concl (cv_eval ``infertype_prog init_config ^program``));

fun source_result program =
  rhs (concl (EVAL
    ``case evaluate_decs ^source_state ^source_env ^program of
      | (_, Rval delta) => nsLookup delta.v (Short «result»)
      | _ => NONE``));

fun source_value source expected = let
  val program = parse_source source
  val inferred = infer_source program
  val _ = if same_const (#1 (strip_comb inferred)) ``M_success`` then ()
          else raise Fail ("Source did not infer: " ^ source ^
                           "\n" ^ term_to_string inferred)
  val actual = source_result program
in
  if aconv actual (optionSyntax.mk_some expected) then ()
  else raise Fail ("Wrong source result: " ^ source ^ "\n" ^ term_to_string actual)
end

fun source_rejected source = let
  val program = parse_source source
  val inferred = infer_source program
in
  if same_const (#1 (strip_comb inferred)) ``M_failure`` then ()
  else raise Fail ("Ill-typed source was accepted: " ^ source)
end

val module_and_outer = "structure M = struct val x = 7 end; val x = 1; ";

val _ = source_value (module_and_outer ^
  "val result = let val x = 2 open M in x end") ``Litv (IntLit 7)``;
val _ = source_value (module_and_outer ^
  "val result = let open M val x = 9 in x end") ``Litv (IntLit 9)``;
val _ = source_value (module_and_outer ^
  "val result = let val saved = x open M val later = x in (saved,later) end")
  ``Conv NONE [Litv (IntLit 1); Litv (IntLit 7)]``;
val _ = source_value (module_and_outer ^
  "val result = (let open M in fn unused => x end) 0") ``Litv (IntLit 7)``;
val _ = source_value (module_and_outer ^
  "val result = (fn x => let open M in x end) 2") ``Litv (IntLit 7)``;
val _ = source_value (module_and_outer ^
  "val result = (let open M in fn x => x end) 2") ``Litv (IntLit 2)``;
val _ = source_value (module_and_outer ^
  "val result = let fun f arg = x open M in f 0 end") ``Litv (IntLit 1)``;
val _ = source_value (module_and_outer ^
  "val result = let open M fun f arg = x in f 0 end") ``Litv (IntLit 7)``;
val _ = source_value (module_and_outer ^
  "val result = (let open M in x end, x)")
  ``Conv NONE [Litv (IntLit 7); Litv (IntLit 1)]``;
val _ = source_value
  "structure E = struct end; val x = 3; val result = let open E in x end"
  ``Litv (IntLit 3)``;
val _ = source_value
  "structure Outer = struct structure M = struct val x = 7 end end; \
  \val result = (let open Outer.M in x end, let open Outer open M in x end)"
  ``Conv NONE [Litv (IntLit 7); Litv (IntLit 7)]``;
val _ = source_value
  "structure M = struct val r = Ref 1 end; \
  \val result = (M.r, let open M in r end)"
  ``Conv NONE [Loc T 0; Loc T 0]``;
val _ = source_value
  "structure M = struct exception E end; \
  \val result = (M.E, let open M in E end)"
  ``Conv NONE [Conv (SOME (ExnStamp 0)) []; Conv (SOME (ExnStamp 0)) []]``;
val _ = source_value
  "structure M = struct datatype t = C end; datatype s = C int; \
  \val result = let open M in C end"
  ``Conv (SOME (TypeStamp «C» 0)) []``;
val _ = source_value
  "structure M = struct datatype t = C end; datatype s = C int; \
  \val result = (fn arg => let open M in C end) 0"
  ``Conv (SOME (TypeStamp «C» 0)) []``;
val _ = source_value
  "structure M = struct val id = fn z => z end; \
  \val f = let open M in id end; val result = (f 1,f #\"a\")"
  ``Conv NONE [Litv (IntLit 1); Litv (Char #"a")]``;
val _ = source_value
  "structure M = struct val id = fn z => z end; \
  \val result = let open M in (id 1,id #\"a\") end"
  ``Conv NONE [Litv (IntLit 1); Litv (Char #"a")]``;

val _ = source_rejected
  "structure N = struct val y = 1 end; \
  \structure M = struct structure N = struct end end; \
  \val result = let open M in N.y end";
val _ = source_rejected
  "structure M = struct datatype t = C end; \
  \val result = let open M in C 1 end";
val _ = source_rejected "val result = let open Missing in 1 end";
val _ = source_rejected
  "structure M = struct end; \
  \val r = let open M in Ref (fn z => z) end; \
  \val Ref f = r; val result = (f 1,f #\"a\")";
