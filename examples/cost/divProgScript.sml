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

fun diff_code code1 code2 = let
  val l1 = code1
           |> dest_comb
           |> snd
           |> listSyntax.dest_list
           |> fst;
  val l2 = code2
           |> dest_comb
           |> snd
           |> listSyntax.dest_list
           |> fst;
  val [(p1,p2)] = filter (not o (uncurry aconv)) (zip l1 l2)
  in (p1,p2)
  end

val (p1,p2) = diff_code pureLoop_code_def pureLoop2_code_def

val s = ``s:('c,'ffi) dataSem$state``

Theorem data_safe_pureLoop_code[local]:
  ∀s. s.safe_for_space ∧
      (∃x. lookup 0 s.locals = SOME x) ∧
      (lookup 249 s.code =
         ^((rhs o concl o EVAL) ``lookup 249 pureLoop_data_code``))
      ⇒ data_safe (evaluate ((SND o SND) ^p1, s))
Proof
  measureInduct_on `^s.clock`
  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]
  \\ first_x_assum drule
  \\ impl_tac
  >- rw [Abbr `s'`,lookup_fromList]
  \\ rw []
  \\ qmatch_asmsub_abbrev_tac `evaluate (_,s'')`
  \\ `s' = s''`
     by (UNABBREV_ALL_TAC
        \\ rw [state_component_equality]
        \\ EVAL_TAC)
  \\ fs [] \\ EVERY_CASE_TAC \\ fs [data_safe_def]
QED

Theorem data_safe_pureLoop_code_shallow[local] =
  data_safe_pureLoop_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_pureLoop_code_timeout[local]:
  ∀s. (∃x. lookup 0 s.locals = SOME x) ∧
      (lookup 249 s.code =
         ^((rhs o concl o EVAL) ``lookup 249 pureLoop_data_code``))
      ⇒ ∃s'. evaluate ((SND o SND) ^p1, s) =
               (SOME (Rerr(Rabort Rtimeout_error)),s')
Proof
  measureInduct_on `^s.clock`
  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]
  \\ first_x_assum drule
  \\ impl_tac
  >- rw [Abbr `s'`,lookup_fromList]
  \\ rw [] \\ rw []
QED

Theorem data_safe_pureLoop_code_timeout_shallow[local] =
  data_safe_pureLoop_code_timeout |> simp_rule [to_shallow_thm,to_shallow_def]

Overload monad_unitbind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

Theorem data_safe_pureLoop:
 ∀ffi coracle cc n. data_safe (evaluate (pureLoop_data_call,
                          initial_state ffi pureLoop_data_code
                                        coracle cc T 1000 32 n))
Proof
  (* Some tactics *)
  let
    val data_eval_step =
      computeLib.RESTR_EVAL_TAC [ ``IS_NONE``
                                , ``op_requires_names``
                                , ``pureLoop_data_code``]
      \\ fs [bvi_to_dataTheory.op_requires_names_eqn
            , IS_NONE_DEF
            , cut_state_opt_def
            , get_vars_def
            , lookup_def
            , dataLangTheory.op_space_reset_def]
    val strip_assign =
      qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
      \\ ONCE_REWRITE_TAC [bind_def]
      \\ rw [assign_def,data_safe_def]
      \\ EVAL_TAC \\ rw [size_of_def,lookup_def,lookup_delete]
      \\ ONCE_REWRITE_TAC [GSYM (EVAL ``pureLoop_data_code``)]
      \\ Q.UNABBREV_TAC `rest_ass`
      \\ fs [bvi_to_dataTheory.op_requires_names_eqn, dataLangTheory.op_space_reset_def]
      \\ rw []
    val open_call =
      qmatch_goalsub_abbrev_tac `call _ (SOME nn)`
      \\ qpat_assum `Abbrev (nn = _)` (fn ab =>
         let val eq = CONV_RULE (REWR_CONV markerTheory.Abbrev_def) ab
             val n  = rhs (concl eq)
         in Q.UNABBREV_TAC `nn`
         \\ rw [ call_def
               , find_code_def
               , push_env_def
               , get_vars_def
               , EVAL ``lookup ^n pureLoop_data_code``
               , to_shallow_thm,to_shallow_def
               , call_env_def,dec_clock_def
               , cut_env_def,domain_def
               , data_safe_def
               , EMPTY_SUBSET]
         end)
    val close_call =
      qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
      \\ qmatch_goalsub_abbrev_tac `f s`
      \\ `data_safe (f s)` suffices_by
         (EVERY_CASE_TAC \\ rw [data_safe_def]
         \\ fs [data_safe_def,data_safe_move
               ,set_var_safe_for_space]
         \\ drule_then drule pop_env_safe_for_space
         \\ fs [set_var_safe_for_space])
      \\ Q.UNABBREV_TAC `f`
      \\ Q.UNABBREV_TAC `s`
    val make_call =
      open_call \\ close_call
    val open_tailcall =
      qmatch_goalsub_abbrev_tac `tailcall (SOME nn)`
      \\ qpat_assum `Abbrev (nn = _)` (fn ab =>
         let val eq = CONV_RULE (REWR_CONV markerTheory.Abbrev_def) ab
             val n  = rhs (concl eq)
         in Q.UNABBREV_TAC `nn`
         \\ rw [ tailcall_def
               , find_code_def
               , get_vars_def
               , get_var_def
               , lookup_def
               , EVAL ``lookup ^n pureLoop_data_code``]
         end)
      \\ rw [ to_shallow_thm,to_shallow_def,call_env_def
            , dec_clock_def,data_safe_def,size_of_def,lookup_def]
    val close_tailcall =
      ho_match_mp_tac data_safe_res
      \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
      \\ rw []
    val make_tailcall =
      open_tailcall \\ close_tailcall
    val strip_call =
      qmatch_goalsub_abbrev_tac `bind _ rest_call _`
      \\ ONCE_REWRITE_TAC [bind_def]
      \\ open_call \\ rw [data_safe_def]
    val make_if =
      rw [if_var_def,data_safe_def,lookup_def]
      \\ fs [ isBool_def
            , backend_commonTheory.bool_to_tag_def
            , backend_commonTheory.true_tag_def
            , backend_commonTheory.false_tag_def]
  (* Start *)
  (* Turn into shallow embedding  *)
 in
 REWRITE_TAC [ definition "pureLoop_data_call_def"
                , to_shallow_thm
                , to_shallow_def]
  (* Make first call *)
 \\ rw [ initial_state_def ]
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 (* Another call *)
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ data_eval_step
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ ntac 50 strip_assign
 (* Another tailcall *)
 \\ make_tailcall
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ ntac 6 strip_assign
 \\ open_tailcall
 \\ ntac 4 strip_assign
 \\ make_if
 \\ ntac 2 strip_assign
 \\ open_tailcall
 \\ ntac 4 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 \\ ntac 3 strip_assign
 \\ make_tailcall
 \\ ntac 8 strip_assign
 \\ make_tailcall
 \\ strip_assign
 (* Finally we reach our function call *)
 \\ ho_match_mp_tac data_safe_bind_error
 \\ open_call
 \\ rw [get_var_def,lookup_def,data_safe_def,to_shallow_def]
 \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
 \\ qmatch_goalsub_abbrev_tac `f s`
 \\ `∃s'. f s = (SOME (Rerr(Rabort Rtimeout_error)),s')`
    by (unabbrev_all_tac
       \\ ho_match_mp_tac data_safe_pureLoop_code_timeout_shallow
       \\ rw [lookup_def,lookup_fromList]
       \\ EVAL_TAC)
 \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
 \\ unabbrev_all_tac
 \\ ho_match_mp_tac data_safe_pureLoop_code_shallow
 \\ rw [lookup_def,lookup_fromList]
 \\ EVAL_TAC
 end
QED

val _ = export_theory();
