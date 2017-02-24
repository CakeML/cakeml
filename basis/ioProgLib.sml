structure ioProgLib =
struct

open preamble
open ml_progLib ioProgTheory mlcharioProgTheory mlcommandLineProgTheory semanticsLib

val hprop_heap_thms =
        ref [STDOUT_precond,COMMANDLINE_precond,STDIN_T_precond,STDIN_F_precond,emp_precond];

fun mk_main_call s =
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;

val basis_ffi_tm =
  list_mk_comb(
    prim_mk_const{Thy="ioProg",Name="basis_ffi"},
    [mk_var("inp",stringSyntax.string_ty),
     mk_var("cls",listSyntax.mk_list_type(stringSyntax.string_ty))])

fun add_basis_proj spec =
  let val spec1 = HO_MATCH_MP append_emp spec handle HOL_ERR _ => spec in 
    spec1 |> Q.GEN`p` |> Q.ISPEC`(basis_proj1, basis_proj2):(string#string#string list) ffi_proj`
  end

fun ERR f s = mk_HOL_ERR"ioProgLib" f s 

(*This function proves that for a given state, parts_ok holds for the ffi and the basis_proj2*)
fun parts_ok_basis_st st = 
  let val goal = ``parts_ok ^st.ffi (basis_proj1, basis_proj2)``
  val th = prove(goal,
    rw[cfStoreTheory.parts_ok_def] \\ TRY (
    EVAL_TAC 
    \\ fs[basis_proj2_def, basis_proj1_def, FLOOKUP_UPDATE, FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rw[]
    \\ imp_res_tac stdout_fun_length
    \\ imp_res_tac stdin_fun_length
    \\ imp_res_tac commandLine_fun_length
    \\ NO_TAC)
    \\ `^st.ffi.oracle = basis_ffi_oracle` suffices_by
      metis_tac[oracle_parts]
    \\ EVAL_TAC)
  in th end

(* This function proves the SPLIT pre-condition of call_main_thm_basis *)
fun subset_basis_st st precond =
  let 
  val hprops = precond |>  helperLib.list_dest helperLib.dest_star
  fun match_and_instantiate tm th =
    INST_TY_TERM (match_term (rator(concl th)) tm) th
  fun find_heap_thm hprop =
    Lib.tryfind (match_and_instantiate hprop) (!hprop_heap_thms)
    handle HOL_ERR _ => raise(ERR"subset_basis_st"
                                 ("no hprop_heap_thm for "^Parse.term_to_string(hprop)))
  val heap_thms = List.map find_heap_thm hprops
  fun build_set [] = raise(ERR"subset_basis_st""no STDOUT in precondition")
    | build_set [th] = th
    | build_set (th1::th2::ths) =
        let
          val th = MATCH_MP append_hprop (CONJ th1 th2)
          val th = CONV_RULE(LAND_CONV EVAL)th
          val th = MATCH_MP th TRUTH
          val th = CONV_RULE(RAND_CONV (pred_setLib.UNION_CONV EVAL)) th
        in build_set (th::ths) end
  val sets_thm = build_set heap_thms
  val sets = rand(concl sets_thm)
  val to_inst = free_vars sets
  val goal = pred_setSyntax.mk_subset(sets,st)
  val pok_thm = parts_ok_basis_st (rand st) 
  val tac = (strip_assume_tac pok_thm
     \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap, 
           cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
     \\ EVAL_TAC \\ rw[INJ_MAP_EQ_IFF,INJ_DEF])
  val (subgoals,_) = tac ([],goal)
  fun mk_mapping (x,y) =
    if mem x to_inst then SOME (x |-> y) else
    if mem y to_inst then SOME (y |-> x) else NONE
  val s = 
     List.mapPartial (mk_mapping o dest_eq o #2) subgoals
  val goal' = Term.subst s goal
  val th = prove(goal',tac)
  val th = MATCH_MP SPLIT_exists (CONJ (INST s sets_thm) th)
  in th end


(*
  - st is the ML prog state of the final desired program
  - name (string) is the name of the program's main function (unit->unit) 
  - spec is a theorem of the form
     |- app (basis_proj1, basis_proj2) main_v [Conv NONE []] P
          (POSTv uv. &UNIT_TYPE () uv * STDOUT x * Q)
    where main_v is the value corresponding to the main function
          P is the precondition
          x is the desired output
          Q is any remaining postconditions

    (add_basis_proj can turn an |- app p ... spec into the form above)
*)

fun call_thm st name spec =
  let 
    val call_ERR = ERR "call_thm"
    val th =
      call_main_thm_basis
        |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
        |> SPEC(stringSyntax.fromMLstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C MATCH_MP spec
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc
    val th = PURE_REWRITE_RULE[prog_rewrite] th
    val (mods_tm,types_tm) = th |> concl |> dest_imp |> #1 |> dest_conj
    val mods_thm = 
      mods_tm |> (RAND_CONV EVAL THENC no_dup_mods_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(call_ERR "duplicate modules")
    val types_thm = 
      types_tm |> (RAND_CONV EVAL THENC no_dup_top_types_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(call_ERR "duplicate top types")
    val th = MATCH_MP th (CONJ mods_thm types_thm)
    val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
    val precond = rator precondh1
    val st = split |> rator |> rand
    val SPLIT_thm = subset_basis_st st precond
    val th = PART_MATCH_A (#1 o dest_imp) th (concl SPLIT_thm)
    val th = MATCH_MP th SPLIT_thm
  in (th,rhs(concl prog_rewrite)) end

end
