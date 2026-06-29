(*
  Automation for instantiating the FFI oracle with the
  basis library functions, and removing CF separation logic.
*)
structure basis_ffiLib :> basis_ffiLib =
struct

open preamble
open ml_progLib basis_ffiTheory set_sepTheory cfHeapsBaseTheory
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
    >- EVAL_TAC
    >- (simp[Abbr`st`] \\ EVAL_TAC)
    >~ [‘_ |++ _’] >- (imp_res_tac oracle_parts \\ gvs [])
    >~ [‘SOME FFIdiverge’] >- (imp_res_tac oracle_parts_div \\ rfs[])
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

(* TODO
 * - the functionality should be the same when we want a RUNTIME postcond
 *   with a custom precondition. *)
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


(* This function proves the SPLIT pre-condition of call_main_thm_basis *)
fun subset_basis_st st precond sets sets_thm =
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

fun whole_prog_thm st name spec =
  let
    val call_ERR = ERR "whole_prog_thm"
    val whole_prog_spec_tm = spec |> concl |> strip_imp |> snd |> strip_comb |> fst
    val (whole_prog_spec_thm,sets_term,sets_theorem) =
        if same_const whole_prog_spec_tm ``whole_prog_spec`` orelse
           same_const whole_prog_spec_tm ``whole_prog_spec2``
        then
          let
            val sets_thm = mk_user_sets_thm ()
            val sets     = rand (concl sets_thm)
            val thm =
              if same_const whole_prog_spec_tm ``whole_prog_spec`` then
                whole_prog_spec_semantics_prog
              else
                whole_prog_spec2_semantics_prog
          in
            (thm, sets, sets_thm)
          end
        else if same_const whole_prog_spec_tm ``whole_prog_ffidiv_spec`` then
          (whole_prog_spec_semantics_prog_ffidiv,sets2,sets_thm2)
       else raise(call_ERR "Conclusion must be a whole_prog_spec or whole_prog_spec2 or whole_prog_ffidiv_spec")
    val ffi_v = st |> get_Decls_thm |> concl |> free_vars
                   |> first (fn v => fst (dest_var v) = "ffi")
    val s_th = (st |> get_Decls_thm |> GEN ffi_v |> ISPEC basis_ffi_tm) |> SPEC_ALL
    val th =
      whole_prog_spec_thm
        |> (fn th => MATCH_MP th s_th handle HOL_ERR _ =>
                     MATCH_MP th (PURE_ONCE_REWRITE_RULE [GSYM same_eval_state] s_th)
                     |> PURE_REWRITE_RULE [same_eval_state])
        |> SPEC(mlstringSyntax.mk_mlstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C HO_MATCH_MP spec
        |> SIMP_RULE bool_ss [option_case_def, set_sepTheory.SEP_CLAUSES]
    (* TS: what is this doing? why not call remove_snocs? *)
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc
    val th = PURE_REWRITE_RULE[prog_rewrite] th
    val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
    val precond = rator precondh1
    val st = split |> rator |> rand
    val SPLIT_thm = subset_basis_st st precond sets_term sets_theorem
    val th = PART_MATCH_A (#1 o dest_imp) th (concl SPLIT_thm)
    val th = MATCH_MP th SPLIT_thm
    val th = DISCH_ALL th
             |> REWRITE_RULE [AND_IMP_INTRO]
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [LENGTH]))
             |> REWRITE_RULE [GSYM AND_IMP_INTRO]
             |> UNDISCH_ALL
  in (th,rhs(concl prog_rewrite)) end;

val basis_ffi_term =
  basis_ffiTheory.whole_prog_spec_IMP
  |> concl |> rator |> rand |> rand
  |> rator |> rator |> rator |> rand |> rand;

fun simple_timer t = let
  val new_t = Time.now()
  val _ = print (" " ^ Time.fmt 1 (new_t - t) ^ " seconds\n")
  in new_t end;

fun prove_sem_thm name code_const_name spec = let
  val t = Time.now()
  fun print_pad s =
    print (s ^ " " ^ implode (List.tabulate(Int.max(0,50 - String.size s), K #"_")))
  val _ = print_pad ("prove_sem_thm: collecting declarations")
  val Decls_lemma =
    ml_translatorLib.get_ml_prog_state ()
    |> ml_progLib.get_thm
    |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def]
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: instantiating main theorem")
  val spec = spec |> UNDISCH_ALL
  val th1 = CONJ spec (Decls_lemma |> GEN_ALL |> ISPEC basis_ffi_term |> SPEC_ALL);
  val th2 = (MATCH_MP basis_ffiTheory.whole_prog_spec_IMP th1
             handle HOL_ERR _ =>
             MATCH_MP basis_ffiTheory.whole_prog_spec_IMP' th1)
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: removing snocs from code")
  val remove_snocs_conv =
        PURE_REWRITE_CONV [listTheory.SNOC_APPEND] THENC
        PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC] THENC
        PURE_REWRITE_CONV [listTheory.APPEND]
  val th3 = SPEC (mlstringSyntax.mk_mlstring name) th2
            |> CONV_RULE (RAND_CONV remove_snocs_conv)
  val code_tm = th3 |> concl |> rand
  val code_v = mk_var(code_const_name, type_of code_tm)
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: defining " ^ code_const_name)
  val code_def = new_definition(code_const_name ^ "_def[compute]",mk_eq(code_v,code_tm))
  val th4 = th3 |> CONV_RULE (RAND_CONV (K (SYM code_def)))
                |> CONV_RULE (REWR_CONV LET_THM THENC BETA_CONV)
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: using nsLookup for " ^ name ^ " in env")
  val th5 = let
    val g1 = th4 |> concl |> dest_imp |> fst
    val l = dest_eq g1 |> fst |> nsLookup_conv
    val l1 = prove(g1,REWRITE_TAC [l])
    in MP th4 l1 end
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: proving ffi is unchanged")
  val th6 = let
    val g2 = th5 |> concl |> dest_imp |> fst
    val l2 = prove(g2,EVAL_TAC)
    in MP th5 l2 end
  val t = simple_timer t
  val _ = print_pad ("prove_sem_thm: checking refs are basis refs")
  val th7 = let
    val g2 = th6 |> concl |> dest_imp |> fst
    val l2 = prove(g2,
                   EVAL_TAC
                   \\ REWRITE_TAC [semanticPrimitivesTheory.store_v_11,
                                   APPEND, CONS_11, basis_ffiTheory.basis_refs_eqs]
                   \\ simp_tac std_ss []
                   \\ EVAL_TAC)
    in MP th6 l2 end
  val th8 = th7 |> DISCH_ALL |> SIMP_RULE bool_ss [GSYM CONJ_ASSOC, AND_IMP_INTRO]
  val _ = simple_timer t
  val _ = print ("prove_sem_thm: done\n")
  in th8 end;

end
