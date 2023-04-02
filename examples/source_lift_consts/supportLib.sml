(*
  Library defining commonly used functions for Icing integration
*)
structure supportLib =
struct

open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib;
open astToSexprLib fromSexpTheory basis_ffiTheory cfHeapsBaseTheory basis;
open preamble;

local
  val heap_thms = [COMMANDLINE_precond, STDIO_precond];
  val heap_thms2 = [COMMANDLINE_precond, STDIO_precond, RUNTIME_precond];
  val user_thms = ref ([]: thm list);
  fun build_set [] = raise(ERR"subset_basis_st""no STDOUT in precondition")
    | build_set [th] = th
    | build_set (th1::th2::ths) =
        let
          val th = MATCH_MP append_hprop (CONJ th1 th2)
          val th = CONV_RULE(LAND_CONV EVAL)th
          val th = MATCH_MP th TRUTH |> SIMP_RULE (srw_ss()) [UNION_EMPTY]
          val th = (CONV_RULE(RAND_CONV (pred_setLib.UNION_CONV EVAL)) th
          handle _ => th) (* TODO quick fix *)
        in build_set (th::ths) end
in
  fun add_user_heap_thm thm =
      (user_thms := thm :: (!user_thms);
       HOL_MESG ("Adding user heap theorem:\n" ^ thm_to_string thm ^ "\n"))
  val sets_thm2 = build_set heap_thms2;
  val sets2 = rand (concl sets_thm2)
  fun mk_user_sets_thm () = build_set (heap_thms @ (!user_thms))
end

fun write_code_to_file theAST_def theBenchmarkMain_def fname numArgs =
let
  val fullProg =
      EVAL (Parse.Term
            ‘APPEND (^theAST_def) ^(theBenchmarkMain_def)’)
  val fileBasePath = "output/" ^(Int.toString numArgs) ^ "/" ^ fname
  val filenamePlain = fileBasePath ^ ".sexp.cml";
  val _ = ((write_ast_to_file filenamePlain) o rhs o concl) fullProg;
  in
  ()
end;

end;
