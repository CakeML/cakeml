(*
  Automation for instantiating the FFI oracle with the
  basis library functions, and removing CF separation logic.
*)
structure basis_ffiLib :> basis_ffiLib =
struct

open preamble
open ml_progLib basis_ffiTheory semanticsLib helperLib set_sepTheory cfHeapsBaseTheory
     CommandLineProofTheory TextIOProofTheory

fun ERR f s = mk_HOL_ERR"basis_ffiLib" f s;

val basis_ffi_const = prim_mk_const{Thy="basis_ffi",Name="basis_ffi"};
val basis_ffi_tm =
  list_mk_comb(basis_ffi_const,
    map mk_var
      (zip ["cl","fs"]
        (#1(strip_fun(type_of basis_ffi_const)))))

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
    \\ TRY pairarg_tac \\ fs[]
    \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
    \\ srw_tac[DNF_ss][];

val sets = rand(concl sets_thm)
val to_inst = free_vars sets

(* This function proves the SPLIT pre-condition of call_main_thm_basis *)
fun subset_basis_st st precond =
  let
  val goal = pred_setSyntax.mk_subset(sets,st)
  val tac = (
        fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
     \\ qmatch_goalsub_abbrev_tac`parts_ok ffii (basis_proj1,basis_proj2)`
     \\ `parts_ok ffii (basis_proj1,basis_proj2)`
            by (fs[Abbr`ffii`] \\ prove_parts_ok_st)
     \\ fs[Abbr`ffii`]
     \\ EVAL_TAC \\ rw[INJ_MAP_EQ_IFF,INJ_DEF,FLOOKUP_UPDATE])
  val (subgoals,_) = tac ([],goal)
  fun mk_mapping (x,y) =
    if mem x to_inst then SOME (x |-> y) else
    if mem y to_inst then SOME (y |-> x) else NONE
  fun safe_dest_eq tm =
    if boolSyntax.is_eq tm then boolSyntax.dest_eq tm else
    Lib.tryfind boolSyntax.dest_eq (boolSyntax.strip_disj tm)
    handle HOL_ERR _ =>
      raise(ERR"subset_basis_st"("Could not prove heap subgoal: "^(Parse.term_to_string tm)))
  val s =
     List.mapPartial (mk_mapping o safe_dest_eq o #2) subgoals
  val goal' = Term.subst s goal
  val th = prove(goal',tac)
  val th = MATCH_MP SPLIT_exists (CONJ (INST s sets_thm) th)
  val length_hyps = mapfilter (assert listSyntax.is_length o lhs) (hyp th)
                 |> map EVAL
  in foldl (uncurry PROVE_HYP) th length_hyps end;

fun whole_prog_thm st name spec =
  let
    val call_ERR = ERR "whole_prog_thm"
    val th =
      whole_prog_spec_semantics_prog
        |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
        |> SPEC(stringSyntax.fromMLstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C HO_MATCH_MP spec
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc (* TODO: this is too slow for large progs *)
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
    val precond = rator precondh1 (* must be COMMANDNLINE cl * STDIO fs *)
    val st = split |> rator |> rand
    val SPLIT_thm = subset_basis_st st precond
    val th = PART_MATCH_A (#1 o dest_imp) th (concl SPLIT_thm)
    val th = MATCH_MP th SPLIT_thm
  in (th,rhs(concl prog_rewrite)) end;

end
