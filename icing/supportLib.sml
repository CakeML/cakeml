(*
  Library defining commonly used functions for Icing integration
*)
structure supportLib =
struct

open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib;
open source_to_source2Theory source_to_source2ProofsTheory CakeMLtoFloVerTheory
     CakeMLtoFloVerProofsTheory icing_optimisationProofsTheory
     cfSupportTheory;
open astToSexprLib fromSexpTheory basis_ffiTheory cfHeapsBaseTheory basis;
open icing_optimisationsLib preamble;

fun mk_local_opt_thm (th1:thm) (th2:thm) =
  th1
    |> REWRITE_RULE [th2]
    |> REWRITE_RULE [opt_pass_with_plans_decs_unfold,
                     stos_pass_with_plans_fun_unfold,
                     opt_pass_with_plans_scope_unfold,
                     locationTheory.unknown_loc_def, HD]
    |> SIMP_RULE std_ss [TypeBase.one_one_of “:ast$exp”,
                         TypeBase.one_one_of “:ast$dec”,
                         TypeBase.one_one_of “:'a list”];

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

fun mk_whole_prog_spec_thm spec name st =
  let
(** TODO: Below copied from basis_ffiLib.sml because of a bug in subset_basis_st *)
val basis_ffi_const = prim_mk_const{Thy="basis_ffi",Name="basis_ffi"};
val basis_ffi_tm =
  list_mk_comb(basis_ffi_const,
    map mk_var
      (zip ["cl","fs"]
        (#1(strip_fun(type_of basis_ffi_const)))))

val (whole_prog_spec_thm,sets,sets_thm) =
let
  val sets_thm = mk_user_sets_thm ()
  val sets     = rand (concl sets_thm)
in
  (whole_prog_spec_semantics_prog, sets, sets_thm)
end

(** Build intermediate theorem with SPLIT assumption **)
val th =
  whole_prog_spec_thm
  |> C MATCH_MP (st |> get_Decls_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
  |> SPEC(stringSyntax.fromMLstring name)
  |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
  |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
  |> C HO_MATCH_MP (CONJUNCT1 (UNDISCH_ALL spec))
  |> SIMP_RULE bool_ss [option_case_def, set_sepTheory.SEP_CLAUSES]

val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
val prog_rewrite = EVAL prog_with_snoc
val th = PURE_REWRITE_RULE[prog_rewrite] th
val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
val precond = rator precondh1
val st = split |> rator |> rand

(*This tactic proves that for a given state, parts_ok holds for the ffi and the basis_proj2*)
val prove_parts_ok_st =
    qmatch_goalsub_abbrev_tac`st.ffi`
    \\ `st.ffi.oracle = basis_ffi_oracle`
    by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
    \\ rw[cfStoreTheory.parts_ok_def]
    \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
    \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
    \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
    \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
    \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
    \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
    \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
    \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
    \\ TRY PURE_FULL_CASE_TAC
    \\ fs[]
    \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms))
    \\ fs[fs_ffi_no_ffi_div,cl_ffi_no_ffi_div]
    \\ srw_tac[DNF_ss][] \\ simp[basis_ffi_oracle_def];

val SPLIT_thm =
  let
    val to_inst = free_vars sets
    val goal = pred_setSyntax.mk_subset(sets,st)
    val tac = (
          fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
             cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
       \\ qmatch_goalsub_abbrev_tac`parts_ok ffii (basis_proj1,basis_proj2)`
       \\ `parts_ok ffii (basis_proj1,basis_proj2)`
              by (fs[Abbr`ffii`] \\ prove_parts_ok_st)
       \\ fs[Abbr`ffii`]
       \\ EVAL_TAC
       \\ rw[cfAppTheory.store2heap_aux_append_many,INJ_MAP_EQ_IFF,INJ_DEF,FLOOKUP_UPDATE]
       \\ rw[cfStoreTheory.store2heap_aux_def]
       )
    val (subgoals,_) = tac ([],goal)
    fun mk_mapping (x,y) =
      if tmem x to_inst then SOME (x |-> y) else
      if tmem y to_inst then SOME (y |-> x) else NONE
    fun safe_dest_eq tm =
      if boolSyntax.is_eq tm then boolSyntax.dest_eq tm else
      Lib.tryfind boolSyntax.dest_eq (boolSyntax.strip_disj tm)
      handle HOL_ERR _ =>
        raise(ERR"subset_basis_st"("Could not prove heap subgoal: "^(Parse.term_to_string tm)))
    val s =
       List.mapPartial (mk_mapping o safe_dest_eq o #2) subgoals
    val goal' = Term.subst s goal
    val th = prove(goal',tac)
    val th =
        MATCH_MP SPLIT_exists (CONJ (INST s sets_thm) th)
    val length_hyps = mapfilter (assert listSyntax.is_length o lhs) (hyp th)
                   |> map EVAL
  in
    foldl (uncurry PROVE_HYP) th length_hyps
  end;

val semantics_prog_thm =
  MATCH_MP th SPLIT_thm
  |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [LENGTH]))
  |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH_ALL
in (prog_rewrite, semantics_prog_thm) end;

fun write_code_to_file benchmarking theAST_def theAST_opt theBenchmarkMain_def main_def fname numArgs =
let
  val fullProg =
    if benchmarking
    then
      EVAL (Parse.Term
            ‘APPEND (^(theAST_def |> concl |> rhs)) ^(theBenchmarkMain_def)’)
    else
     EVAL (Parse.Term ‘APPEND ^(theAST_def |> concl |> rhs) ^main_def’);
  val fullOptProg =
   if benchmarking
   then
     EVAL (Parse.Term ‘APPEND (^(theAST_opt |> concl |> rhs)) ^theBenchmarkMain_def’)
  else
    EVAL (Parse.Term ‘APPEND ^(theAST_opt |> concl |> rhs) ^main_def’);
  val fileBasePath = "output/" ^(Int.toString numArgs) ^ "/" ^ fname ^ "_"
  val filenamePlain = fileBasePath ^ "theProg.sexp.cml";
  val filenameOpt = fileBasePath ^ "theOptProg.sexp.cml";
  val _ = ((write_ast_to_file filenamePlain) o rhs o concl) fullProg;
  val _ = ((write_ast_to_file filenameOpt) o rhs o concl) fullOptProg;
  in
  ()
end;

end;
