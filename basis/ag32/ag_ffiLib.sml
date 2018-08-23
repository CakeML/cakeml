(*
  Automation for instantiating the FFI oracle with the
  Silver library function, and removing CF separation logic.
*)
structure ag_ffiLib =
struct

open preamble
open ml_progLib basis_ffiTheory semanticsLib set_sepTheory cfHeapsBaseTheory ag_ffiTheory

val ERR = mk_HOL_ERR"ag_ffiLib";

val ag_ffi_const = prim_mk_const{Thy="ag_ffi",Name="ag_ffi"};

val prove_parts_ok_st =
    qmatch_goalsub_abbrev_tac`st.ffi`
    \\ `st.ffi.oracle = ag_ffi_oracle`
    by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
    \\ simp[cfStoreTheory.parts_ok_def]
    \\ conj_tac >- EVAL_TAC
    \\ conj_tac >- (simp[Abbr`st`] \\ EVAL_TAC)
    \\ conj_tac >- ( EVAL_TAC \\ rw[] )
    \\ EVAL_TAC \\ simp[] \\ EVAL_TAC \\ simp[]

val sets = rand(concl ag_ffiTheory.sets_thm)
val to_inst = free_vars sets

fun subset_ag_st st precond sets sets_thm =
  let
  val goal = pred_setSyntax.mk_subset(sets,st)
  val tac = (
        fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
     \\ qmatch_goalsub_abbrev_tac`parts_ok ffii (ag_proj1,ag_proj2)`
     \\ `parts_ok ffii (ag_proj1,ag_proj2)`
            by (fs[Abbr`ffii`] \\ prove_parts_ok_st)
     \\ fs[Abbr`ffii`]
     \\ EVAL_TAC
     \\ rw[cfAppTheory.store2heap_aux_append_many,INJ_MAP_EQ_IFF,INJ_DEF,FLOOKUP_UPDATE]
     \\ rw[cfStoreTheory.store2heap_aux_def]
     )
  val (subgoals,_) = tac ([],goal)
  fun mk_mapping (x,y) =
    if mem x to_inst then SOME (x |-> y) else
    if mem y to_inst then SOME (y |-> x) else NONE
  fun safe_dest_eq tm =
    if boolSyntax.is_eq tm then boolSyntax.dest_eq tm else
    Lib.tryfind boolSyntax.dest_eq (boolSyntax.strip_disj tm)
    handle HOL_ERR _ =>
      raise(ERR"subset_ag_st"("Could not prove heap subgoal: "^(Parse.term_to_string tm)))
  val s =
     List.mapPartial (mk_mapping o safe_dest_eq o #2) subgoals
  val goal' = Term.subst s goal
  val th = prove(goal',tac)
  val th =
      MATCH_MP ag_ffiTheory.SPLIT_exists (CONJ (INST s ag_ffiTheory.sets_thm) th)
  val length_hyps = mapfilter (assert listSyntax.is_length o lhs) (hyp th)
                 |> map EVAL
  in foldl (uncurry PROVE_HYP) th length_hyps end;

fun ag_prog_thm st name spec =
  let
    val call_ERR = ERR "ag_prog_thm"
    val ag_prog_spec_tm = spec |> concl |> strip_imp |> snd |> strip_comb |> fst
    val (ag_prog_spec_thm,sets_term,sets_theorem) =
        if same_const ag_prog_spec_tm ``ag_prog_spec`` then
          (ag_prog_spec_semantics_prog,sets,sets_thm)
        else raise(call_ERR "Conclusion must be an ag_prog_spec")
    val th =
      ag_prog_spec_thm
        |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC ag_ffi_const)
        |> SPEC(stringSyntax.fromMLstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C HO_MATCH_MP spec
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc (* TODO: this is too slow for large progs *)
    val th = PURE_REWRITE_RULE[prog_rewrite] th
    val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
    val precond = rator precondh1 (* must be PRINTER "" *)
    val st = split |> rator |> rand
    val SPLIT_thm = subset_ag_st st precond sets_term sets_theorem
    val th = PART_MATCH_A (#1 o dest_imp) th (concl SPLIT_thm)
    val th = MATCH_MP th SPLIT_thm
  in (th,rhs(concl prog_rewrite)) end;

end
