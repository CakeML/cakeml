open preamble repl_computeLib repl_computeTheory ml_repl_stepTheory replDecsTheory
val _ = new_theory"compileReplDecs"

val ct = ``init_compiler_state.contab``
val m = ``<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap(^ct)|>``
val cs = ``<|out:=[];next_label:=init_compiler_state.rnext_label|>``

val compile_repl_decs_def = zDefine`
  compile_repl_decs = FOLDL (compile_dec1 NONE FEMPTY) (^ct,^m,[],0,^cs) repl_decs`

val _ = computeLib.add_funs[ml_repl_step_decls,repl_decs_def,call_repl_step_dec_def]
val _ = computeLib.stoppers := let
  val stoppers = [``Dlet``,``Dletrec``,``Dtype``]
  in SOME (fn tm => mem tm stoppers) end

fun mk_initial_split n =
  (rhs(concl(compile_repl_decs_def)))
     |> (RAND_CONV (EVAL THENC chunkify_CONV n) THENC
         RATOR_CONV (RAND_CONV EVAL))

val initial_split20 = mk_initial_split 20

val (initial', decllist_defs) = let
  val r = rhs (concl initial_split20)
  val r' = rand r
  val lists = spine_binop (Lib.total listSyntax.dest_append) r'
  val defs = map mk_def lists
  fun replace ths t =
    case ths of
      []=> ALL_CONV t
    | [d] => SYM d
    | d::ds => (LAND_CONV (K (SYM d)) THENC RAND_CONV (replace ds)) t
in
  (CONV_RULE (RAND_CONV (RAND_CONV (replace defs))) initial_split20, defs)
end

val x100 = doit 5 (TRUTH, decllist_defs, initial')
val x140 = doit 2 x100;
val x180 = doit 2 x140
val x220 = doit 2 x180;
val x240 = doit 1 x220;
val x260 = doit 1 x240;
val x280 = doit 1 x260;
val x300 = doit 1 x280;
val x320 = doit 1 x300;
val x340 = doit 1 x320;
val x360 = doit 1 x340;
val x380 = doit 1 x360;
val x400 = doit 1 x380;
val (_,_,th) = x400;

val repl_decs_compiled = save_thm("repl_decs_compiled", th);

val _ = export_theory()
