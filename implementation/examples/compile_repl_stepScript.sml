open preamble repl_computeLib ml_repl_stepTheory
val _ = new_theory"compile_repl_step"

val _ = Hol_datatype`stop_list = stop_NIL | stop_CONS of 'a => stop_list`

val _ = computeLib.stoppers := let
  val stop_CONS = inst[alpha|->``:bc_inst list``]``stop_CONS``
  val stoppers = [stop_CONS ,``Dlet``,``Dletrec``,``Dtype``]
  in SOME (fn tm => mem tm stoppers) end

val compile_decs_def = Define`
  compile_decs cs [] acc = acc ∧
  compile_decs cs (d::ds) acc =
  let (css,csf,code) = compile_top cs (Tdec d) in
  compile_decs css ds (stop_CONS code acc)`

val _ = computeLib.add_funs[ml_repl_step_decls]

val compile_dec1_def = Define`
  compile_dec1 (a,cs) d =
    let (css,csf,code) = compile_top cs (Tdec d)
    in
      (stop_CONS code a, css)
`

val compile_decs_FOLDL = store_thm(
  "compile_decs_FOLDL",
  ``∀cs acc.
      compile_decs (cs:compiler_state) ds acc =
      FST (FOLDL compile_dec1 (acc,cs) ds)``,
  Induct_on `ds` >> rw[compile_decs_def, compile_dec1_def]);

fun listlength acc t =
    if listSyntax.is_nil t then acc
    else listlength (acc + 1) (rand t)

fun chunkify_CONV n t = let
  val n_t = numSyntax.mk_numeral (Arbnum.fromInt n)
  val td = listTheory.TAKE_DROP |> SPEC n_t |> GSYM
  fun recurse t =
    if listlength 0 t < n then raise UNCHANGED
    else
      (REWR_CONV td THENC LAND_CONV ListConv1.FIRSTN_CONV THENC
       RAND_CONV (ListConv1.BUTFIRSTN_CONV THENC chunkify_CONV n)) t
in
  recurse t
end

fun foldl_append_CONV t = let
  fun core t = (PolyML.fullGC(); EVAL t)
in
  REWR_CONV rich_listTheory.FOLDL_APPEND THENC
  RATOR_CONV (RAND_CONV core)
end t

fun iterate n t = let
  fun recurse m th =
      if m < 1 then th
      else
        let
          val _ = print (Int.toString (n - m) ^ ": ")
          val th' = time foldl_append_CONV (rhs (concl th))
        in
          recurse (m - 1) (TRANS th th')
        end
in
  recurse n (REFL t)
end


(*
val _ = Globals.max_print_depth := 20

fun mk_initial_split n =
  ``FOLDL compile_dec1 (stop_NIL, init_compiler_state) ml_repl_step_decls``
     |> (RAND_CONV (EVAL THENC chunkify_CONV n) THENC
         RATOR_CONV (RAND_CONV EVAL))

val initial_split20 = mk_initial_split 20
val initial_split10 = time mk_initial_split 10

val thm150 = CONV_RULE (RAND_CONV (iterate 15)) initial_split10

val thm120 = CONV_RULE (RAND_CONV (iterate 6)) initial_split20
val thm140 = CONV_RULE (RAND_CONV (iterate 1)) thm120
val thm160 = CONV_RULE (RAND_CONV (iterate 1)) thm140

val _ = PolyML.fullGC();
val res = time EVAL
  ``compile_decs init_compiler_state (TAKE 100 ml_repl_step_decls) stop_NIL``
*)

(*
EVAL ``TAKE 20 (DROP 100 ml_repl_step_decls)``
val _ = time EVAL ``compile_decs init_compiler_state ml_repl_step_decls stop_NIL``
*)

(*
val Dlet_o = time EVAL ``EL 11 ml_repl_step_decls`` |> concl |> rhs
val many_o10 = EVAL ``GENLIST (K ^Dlet_o) 10`` |> concl |> rhs
val many_o20 = EVAL ``GENLIST (K ^Dlet_o) 20`` |> concl |> rhs
val many_o40 = EVAL ``GENLIST (K ^Dlet_o) 40`` |> concl |> rhs
val many_o80 = EVAL ``GENLIST (K ^Dlet_o) 80`` |> concl |> rhs
val many_o160 = EVAL ``GENLIST (K ^Dlet_o) 160`` |> concl |> rhs

val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o10 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o20 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o40 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o80 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o160 stop_NIL``

val _ = computeLib.stoppers := NONE
val num_compset = reduceLib.num_compset()
*)

val _ = export_theory()
