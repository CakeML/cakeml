(*
  Preliminary data-cost examples
*)

open preamble basis compilationLib dataSemTheory data_monadTheory;

val _ = new_theory "divProg"

fun to_data prog name =
  let
    val heap_size      = 1000
    val stack_size     = 1000
    val prog_def       = REFL (process_topdecs prog)
    val cs             = compilation_compset()
    val conf_def       = x64_backend_config_def
    val data_prog_name = name ^ "_data_prog"
    val to_data_thm    = compile_to_data cs conf_def prog_def data_prog_name
    val data_prog_def  = definition(mk_abbrev_name data_prog_name)
    val bvi_conf_def   = definition (mk_abbrev_name "bvi_conf")
    (* configuration *)
    val conf      =  ``^(rhs (concl bvi_conf_def))``
    (* code *)
    val code      = ``fromAList ^(rhs (concl data_prog_def))``
    val code_name = mk_var (name ^ "_data_code", type_of code)
    val code_def  = Define `^code_name = ^code`
    (* initial call *)
    val initial_call = (rhs o concl o EVAL)
      ``dataLang$Call NONE (SOME ^(conf).clos_conf.start) [] NONE``
    val initial_call_name = mk_var (name ^ "_data_call", type_of initial_call)
    val initial_call_def  = Define `^initial_call_name = ^initial_call`
  in
    (initial_call,code)
  end

val pureLoop =
  `fun pureLoop x = pureLoop x;
   val _ = pureLoop 1`

val pureLoop2 =
  `fun pureLoop x = pureLoop (x+1);
   val _ = pureLoop 1`

val (pureLoop_call_def,pureLoop_code_def) =
  to_data pureLoop "pureLoop"

val (pureLoop2_call_def,pureLoop2_code_def) =
  to_data pureLoop2 "pureLoop2"

val [(p1,p2)] = let
  val l1 = pureLoop_code_def
           |> dest_comb
           |> snd
           |> listSyntax.dest_list
           |> fst;
  val l2 = pureLoop2_code_def
           |> dest_comb
           |> snd
           |> listSyntax.dest_list
           |> fst;
  in filter (not o (uncurry aconv)) (zip l1 l2)
  end

Theorem data_safe_pureLoop_code:
  ∀s v. s.safe_for_space
      ⇒ data_safe (evaluate ((SND o SND) ^p1,
                 s with <| code   := fromAList [^p1];
                           locals := fromList [v] |>))
Proof
  measureInduct_on `s.clock`
  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]
  \\ first_x_assum (drule_then (qspec_then `v` mp_tac))
  \\ impl_tac
  >- rw [Abbr `s'`]
  \\ rw []
  \\ qmatch_asmsub_abbrev_tac `evaluate (_,s'')`
  \\ `s' = s''`
     by (UNABBREV_ALL_TAC
        \\ rw [state_component_equality]
        \\ EVAL_TAC)
  \\ fs [] \\ EVERY_CASE_TAC \\ fs [data_safe_def]
QED

Overload monad_unitbind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

Theorem data_safe_pureLoop:
  data_safe (evaluate (pureLoop_data_call,
                    initial_state ARB pureLoop_data_code
                                  ARB ARB T 1000 32 100000))
Proof
  (* Start *)
  (* Turn into shallow embedding  *)
 REWRITE_TAC [ definition "pureLoop_data_call_def"
             , to_shallow_thm
             , to_shallow_def]
  (* Make first call *)
  \\ rw [ initial_state_def
        , tailcall_def
        , find_code_def
        , get_vars_def
        , EVAL ``lookup 60 pureLoop_data_code``]
  \\ rw [to_shallow_thm,to_shallow_def,call_env_def,dec_clock_def]
  \\ ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
  \\ rw []
  (* Bootcode *)
  \\ ntac 7
     (ho_match_mp_tac data_safe_bind
     \\ conj_tac
     >- (rw [assign_def,data_safe_def]
        \\ EVAL_TAC \\ rw [size_of_def])
     \\ qmatch_goalsub_abbrev_tac `data_safe (f _)`
     \\ rw [ assign_def,data_safe_def
           , bvi_to_dataTheory.op_requires_names_eqn
           , dataLangTheory.op_space_reset_def]
     \\ computeLib.RESTR_EVAL_TAC [``pureLoop_data_code``] \\ rw [size_of_def]
     \\ unabbrev_all_tac)
  (* Another call *)
  \\ ho_match_mp_tac data_safe_bind
  \\ reverse conj_tac
  >- cheat (* TODO: it always timeout *)
  \\ rw [ call_def
        , find_code_def
        , get_vars_def
        , EVAL ``lookup 231 pureLoop_data_code``]
  \\ rw [ to_shallow_thm,to_shallow_def
        , call_env_def,dec_clock_def
        , cut_env_def,domain_def
        , EMPTY_SUBSET]
  \\ cheat (* TODO *)
QED


val _ = export_theory();
