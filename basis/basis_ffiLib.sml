(*
  Automation for instantiating the FFI oracle with the
  basis library functions, and removing CF separation logic.
*)
structure basis_ffiLib :> basis_ffiLib =
struct

open preamble
open ml_progLib basis_ffiTheory set_sepTheory cfHeapsBaseTheory
     CommandLineProofTheory TextIOProofTheory

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
             MATCH_MP basis_ffiTheory.whole_prog_spec_SOME_IMP th1
             handle HOL_ERR _ =>
             MATCH_MP basis_ffiTheory.whole_prog_spec_IMP' th1
             handle HOL_ERR _ =>
             MATCH_MP basis_ffiTheory.whole_prog_spec2_IMP th1
             handle HOL_ERR _ =>
             MATCH_MP basis_ffiTheory.whole_prog_spec_ffidiv_IMP th1)
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
