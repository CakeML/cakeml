(*
  Preliminary data-cost examples
*)

open preamble basis compilationLib ;
open dataSemTheory data_monadTheory dataLangTheory;

val _ = new_theory "divProg"

(* *********************** *)
(* * Auxiliary functions * *)
(* *********************** *)

fun to_data prog name =
  let
    val heap_size      = 1000
    val stack_size     = 1000
    val prog_def       = REFL prog
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
    val code_def  = zDefine `^code_name = ^code`
    (* initial call *)
    val initial_call = (rhs o concl o EVAL)
      ``dataLang$Call NONE (SOME ^(conf).clos_conf.start) [] NONE``
    val initial_call_name = mk_var (name ^ "_data_call", type_of initial_call)
    val initial_call_def  = Define `^initial_call_name = ^initial_call`
  in
    (initial_call,code_def)
  end

fun diff_code code1 code2 = let
  val l1 = code1
           |> concl                |> rhs
           |> dest_comb            |> snd
           |> listSyntax.dest_list |> fst;
  val l2 = code2
           |> concl                |> rhs
           |> dest_comb            |> snd
           |> listSyntax.dest_list |> fst;
  val [(p1,p2)] = filter (not o (uncurry aconv)) (zip l1 l2)
  in (p1,p2)
  end

fun diff_codes code1 code2 = let
  val l1 = code1
           |> concl                |> rhs
           |> dest_comb            |> snd
           |> listSyntax.dest_list |> fst;
  val l2 = code2
           |> concl                |> rhs
           |> dest_comb            |> snd
           |> listSyntax.dest_list |> fst;
  in filter (not o (uncurry aconv)) (zip l1 l2)
  end

val _ = translation_extends "basisProg";

val whole_prog = get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_prog

Overload monad_unitbind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

Theorem EVERY_lookup:
  ∀t. EVERY (\(k,v). lookup k t = SOME v) (toAList t)
Proof
  fs [EVERY_MEM,MEM_toAList,FORALL_PROD]
QED

(* MOVE: sptreeTheory *)
Theorem domain_IS_SOME:
  ∀t k. k ∈ domain t = IS_SOME (lookup k t)
Proof
  rw [domain_lookup,IS_SOME_EXISTS]
QED

(* REMOVE *)
val _ = computeLib.add_thms [size_of_def] computeLib.the_compset;

val _ = sptreeSyntax.temp_add_sptree_printer ()

(* *********** *)
(* * Tactics * *)
(* *********** *)

(* Conversion with memoization  *)
fun mem_conv c =
  let val memory = ref ([] : (term * thm) list)
  in fn t => (snd (first (aconv t o fst) (!memory)))
             handle HOL_ERR _ =>
                    let val th = QCONV c t
                    in memory := (t,th) :: (!memory);
                       th
                    end
  end

(* Evaluate a subterm of the goal *)
fun eval_goalsub_tac pat (asms,goal) =
   let
   val tm = goal |> find_term (can (match_term pat))
   val th = EVAL tm
   in PURE_ONCE_REWRITE_TAC [th] (asms,goal)
   end

(* Generate all possible lookup for a code sptree *)
fun mk_code_lookup code_tm code_def = EVERY_lookup
    |> Q.ISPEC code_tm
    |> CONV_RULE ((RAND_CONV o RAND_CONV) (fn tm => code_def))
    |> CONV_RULE (RAND_CONV EVAL)
    |> SIMP_RULE (srw_ss()) []

(* remove makespace bindings *)
val strip_makespace =
  qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def ]
  \\ eval_goalsub_tac ``cut_env _ _`` \\ simp []
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_mkspc`

fun mk_strip_assign code_lookup =
  qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ REWRITE_TAC [ bind_def           , assign_def
                 , op_space_reset_def , closLangTheory.op_case_def
                 , cut_state_opt_def  , option_case_def
                 , do_app_def         , data_spaceTheory.op_space_req_def
                 , do_space_def       , closLangTheory.op_distinct
                 , MEM                , IS_NONE_DEF
                 , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ TRY(eval_goalsub_tac ``cut_state _ _`` \\ simp [])
  \\ TRY(eval_goalsub_tac ``get_vars    _ _`` \\ simp [])
  \\ simp [ do_app_aux_def    , set_var_def    , lookup_def
          , domain_IS_SOME    , code_lookup    , size_of_heap_def
          , consume_space_def , with_fresh_ts_def
          , backend_commonTheory.small_enough_int_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_ass`

fun mk_open_tailcall code_lookup =
  ASM_REWRITE_TAC [ tailcall_def , find_code_def
                  , get_vars_def , get_var_def
                  , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def]
  \\ IF_CASES_TAC >- (simp [data_safe_def,size_of_def] \\ EVAL_TAC)
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``

val close_tailcall =
  ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])

fun mk_make_tailcall open_tailcall =
  open_tailcall \\ close_tailcall

fun mk_open_call code_lookup =
  ASM_REWRITE_TAC [ call_def     , find_code_def , push_env_def
                  , get_vars_def , call_env_def  , dec_clock_def
                  , cut_env_def  , domain_def    , data_safe_def
                  , EMPTY_SUBSET , get_var_def ]
  \\ simp [code_lookup,lookup_def,domain_IS_SOME]
  \\ IF_CASES_TAC >- (simp [data_safe_def,size_of_def] \\ EVAL_TAC)
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``

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

fun mk_make_call open_call =
  open_call \\ close_call

(* val (asms,goal) = top_goal() *)

fun mk_strip_call open_call (asms,goal) =
  let val free_names = map (fn tm => fst (dest_var tm)) (free_varsl (goal::asms))
      fun next_name n name =
          let val new_name = name^"_"^(Int.toString n)
          in if n = 0
             then if mem name free_names
                  then next_name (n+1) name
                  else [QUOTE name]
             else if mem new_name free_names
             then next_name (n+1) name
             else [QUOTE new_name]
          end
  in (qmatch_goalsub_abbrev_tac (`bind _ ` @ (next_name 0 "rest_call") @ ` _`)
     \\ ONCE_REWRITE_TAC [bind_def]
     \\ open_call \\ rw [data_safe_def]) (asms,goal)
  end

val make_if =
  simp [if_var_def,data_safe_def,lookup_def]
  \\ REWRITE_TAC [ isBool_def
                 , backend_commonTheory.bool_to_tag_def
                 , backend_commonTheory.true_tag_def
                 , backend_commonTheory.false_tag_def]
  \\ simp [pop_env_def]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``


(* ************ *)
(* * pureLoop * *)
(* ************ *)

(* A simple infinite loop that does nothing *)

val pureLoop = process_topdecs
  `fun pureLoop x = pureLoop x;
   val _ = pureLoop 1`

val pureLoop2 = process_topdecs
  `fun pureLoop x = pureLoop (x+1);
   val _ = pureLoop 1`

val (pureLoop_call_def,pureLoop_code_def) =
  to_data pureLoop "pureLoop"

val (pureLoop2_call_def,pureLoop2_code_def) =
  to_data pureLoop2 "pureLoop2"


val (p1,p2) = diff_code pureLoop_code_def pureLoop2_code_def

val s = ``s:('c,'ffi) dataSem$state``

Theorem data_safe_pureLoop_code[local]:
  ∀s. s.safe_for_space ∧
      (∃x. lookup 0 s.locals = SOME x) ∧
      (lookup 249 s.code =
         ^((``lookup 249 pureLoop_data_code``
           |> (REWRITE_CONV [pureLoop_code_def]
               THENC EVAL)
           |> rhs o concl)))
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
         ^((``lookup 249 pureLoop_data_code``
           |> (REWRITE_CONV [pureLoop_code_def]
               THENC EVAL)
           |> rhs o concl)))
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

Theorem data_safe_pureLoop:
 ∀ffi coracle cc n. data_safe (evaluate (pureLoop_data_call,
                          initial_state ffi pureLoop_data_code
                                        coracle cc T 1000 32 n))
Proof
 let
  val code_lookup   = mk_code_lookup `pureLoop_data_code` pureLoop_code_def
  val strip_assign  = mk_strip_assign code_lookup
  val open_call     = mk_open_call code_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
  (* Some tactics *)
 REWRITE_TAC [ definition "pureLoop_data_call_def"
             , to_shallow_thm
             , to_shallow_def
             , initial_state_def]
 \\ rpt strip_tac
  (* Make first call *)
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 (* Another call *)
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
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
 \\ strip_makespace
 \\ ntac 7 strip_assign
 \\ make_tailcall
 \\ strip_assign
 (* Finally we reach our function call *)
 \\ ho_match_mp_tac data_safe_bind_error
 \\ open_call
 \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
 \\ qmatch_goalsub_abbrev_tac `f s`
 \\ `∃s'. f s = (SOME (Rerr(Rabort Rtimeout_error)),s')`
    by (unabbrev_all_tac
       \\ ho_match_mp_tac data_safe_pureLoop_code_timeout_shallow
       \\ rw [lookup_def,lookup_fromList,code_lookup])
 \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
 \\ unabbrev_all_tac
 \\ ho_match_mp_tac data_safe_pureLoop_code_shallow
 \\ rw [lookup_def,lookup_fromList,code_lookup]
 end
QED

(* ****************************** *)
(* * condLoop (with mini-basis) * *)
(* ****************************** *)

(* A loop functions with a stopping condition *)

val minus_prog = find_term (can (match_term ``Dlet _ (Pvar "-") _``)) whole_prog
val equal_prog = find_term (can (match_term ``Dlet _ (Pvar "=") _``)) whole_prog

val condLoop =
  let val prog = process_topdecs
        `fun condLoop x = if x = 0 then 0 else condLoop (x - 1);
         val _ = condLoop 5`
  in (rhs o concl o EVAL) ``[^minus_prog;^equal_prog] ++ ^prog``
  end

val condLoop2 =
  let val prog = process_topdecs
        `fun condLoop x = if x = 0 then 0 else condLoop (x - 2);
         val _ = condLoop 5`
  in (rhs o concl o EVAL) ``[^minus_prog;^equal_prog] ++ ^prog``
  end

val (condLoop_call_def,condLoop_code_def) =
  to_data condLoop "condLoop"

val (condLoop2_call_def,condLoop2_code_def) =
  to_data condLoop2 "condLoop2"

val (b1,b2) = diff_code condLoop_code_def condLoop2_code_def

Theorem data_safe_basis_condLoop:
 ∀ffi coracle cc n. data_safe (evaluate (condLoop_data_call,
                          initial_state ffi condLoop_data_code
                                        coracle cc T 10000 32 n))
Proof
 let
  val code_lookup   = mk_code_lookup `condLoop_data_code` condLoop_code_def
  val strip_assign  = mk_strip_assign code_lookup
  val open_call     = mk_open_call code_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 REWRITE_TAC [ definition "condLoop_data_call_def"
             , to_shallow_thm
             , to_shallow_def
             , initial_state_def ]
  (* Make first call *)
 \\ rpt strip_tac
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 (* Another call *)
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 (* Another tailcall *)
 \\ make_tailcall
 \\ time (ntac 3
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC))
 \\ ntac 6 strip_assign
 \\ open_tailcall
 \\ time (ntac 3
    (ntac 4 strip_assign
    \\ make_if
    \\ ntac 2 strip_assign
    \\ open_tailcall))
 \\ ntac 4 strip_assign
 \\ make_if
 \\ simp [code_lookup]
 \\ IF_CASES_TAC >- simp [data_safe_def]
 \\ close_tailcall
 \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
 \\ eval_goalsub_tac ``state_locals_fupd _ _``
 \\ ntac 3
    (strip_makespace
    \\ ntac 7 strip_assign
    \\ make_tailcall)
 \\ strip_assign
 \\ strip_call
 \\ ntac 5
    (strip_assign
    \\ make_if
    \\ strip_assign
    \\ strip_assign
    \\ open_tailcall)
 \\ strip_assign
 \\ make_if
 \\ strip_assign
 \\ simp [return_def,lookup_def]
 \\ Q.UNABBREV_TAC `rest_call`
 \\ make_tailcall
 \\ strip_assign
 \\ simp [return_def,lookup_def]
 \\ simp [data_safe_def]
end
QED

(* ************************** *)
(* * echo (with mini-basis) * *)
(* ************************** *)

val word8_mod =
  find_term (can (match_term ``Dmod "Word8" _``)) whole_prog

val word8_fromInt =
  find_term (can (match_term ``Dlet _ (Pvar "fromInt") _``)) word8_mod

val string_mod =
  find_term (can (match_term ``Dmod "String" _``)) whole_prog

val string_implode =
  find_term (can (match_term ``Dlet _ (Pvar "implode") _``)) string_mod

val word8array_mod =
  find_term (can (match_term ``Dmod "Word8Array" _``)) whole_prog

val word8array_array =
  find_term (can (match_term ``Dlet _ (Pvar "array") _``)) word8array_mod

val echo =
  let val prog = process_topdecs `
      fun put_char c = let
        val s = String.implode [c]
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (put_char c; printLoop c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``[Dmod "Word8"      [^word8_fromInt];
                             Dmod "String"     [^string_implode];
                             Dmod "Word8Array" [^word8array_array]
                            ] ++ ^prog``
  end

val echo2 =
  let val prog = process_topdecs `
      fun put_char c = let
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val s = String.implode [c]
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_char c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``[Dmod "Word8"      [^word8_fromInt];
                             Dmod "String"     [^string_implode];
                             Dmod "Word8Array" [^word8array_array]
                            ] ++ ^prog``
  end

val (echo_call_def,echo_code_def) =
  to_data echo "echo"

val (echo2_call_def,echo2_code_def) =
  to_data echo2 "echo2"

val f_diff = diff_codes echo_code_def echo2_code_def

val (f11,f12) = hd f_diff
val (f21,f22) = (hd o tl) f_diff

Theorem data_safe_echo_code:
  ∀s ts.
   s.safe_for_space ∧
   check_state s ∧
   size_of_heap s ≤ s.limits.heap_limit ∧
   (s.tstamps = SOME ts) ∧
   (∃x. lookup 0 s.locals = SOME (Number 97)) ∧
   (s.code = echo_data_code)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
  let
    val code_lookup   = mk_code_lookup `echo_data_code` echo_code_def
    val strip_assign  = mk_strip_assign code_lookup
    val open_call     = mk_open_call code_lookup
    val make_call     = mk_make_call open_call
    val strip_call    = mk_strip_call open_call
    val open_tailcall = mk_open_tailcall code_lookup
    val make_tailcall = mk_make_tailcall open_tailcall
  in
  measureInduct_on `^s.clock`
  \\ fs [ to_shallow_thm
        , to_shallow_def
        , initial_state_def ]
  \\ rw []
  \\ strip_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s1`
  \\ Q.UNABBREV_TAC `f`
  \\ `check_state s1` by
     by (Q.UNABBREV_TAC `s1`
        \\ rw [check_state_def]
        >- EVAL_TAC
        >-


  \\ strip_makespace
  \\ ntac 6 strip_assign
  \\ strip_call


``lookup 61 echo_data_code``
|> (REWRITE_CONV [echo_code_def] THENC EVAL)
(* Finds out the length of the array *)

``lookup 62 echo_data_code``
|> (REWRITE_CONV [echo_code_def] THENC EVAL)
(* Move the string into a byte array *)


  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def,cut_env_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]


  end
QED


Theorem data_safe_echo:
 ∀ffi coracle cc n. data_safe (evaluate (echo_data_call,
                          initial_state ffi echo_data_code
                                        coracle cc T 1000 32 n))
Proof
 let
  val code_lookup   = mk_code_lookup `echo_data_code` echo_code_def
  val strip_assign  = mk_strip_assign code_lookup
  val open_call     = mk_open_call code_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 REWRITE_TAC [ definition "echo_data_call_def"
             , to_shallow_thm
             , to_shallow_def
             , initial_state_def ]
  (* Make first call *)
 \\ rpt strip_tac
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 \\ make_tailcall
 \\ ntac 4
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
  \\ strip_call
  \\ ntac 9 strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ntac 5
     (open_tailcall
     \\ ntac 4 strip_assign
     \\ make_if
     \\ ntac 2 strip_assign)
  \\ open_tailcall
  \\ ntac 4 strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call`
  \\ ntac 3 strip_assign
  \\ make_tailcall
  \\ ntac 5
     (strip_makespace
     \\ ntac 7 strip_assign
     \\ make_tailcall)



  \\ strip_assign
  \\ strip_call
  \\ strip_call



  let val st =
      (snd (top_goal()) |> find_term (can (match_term ``state_locals_fupd _ _``)))
  in EVAL ``lookup 0 ^st.locals``
  end

f21








val basis_echo =
  let val prog = process_topdecs `
      fun put_char c = let
        val s = String.implode [c]
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (put_char c; printLoop c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val basis_echo2 =
  let val prog = process_topdecs `
      fun put_char c = let
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val s = String.implode [c]
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_char c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val (basis_echo_call_def,basis_echo_code_def) =
  to_data basis_echo "basis_echo"

val (basis_echo2_call_def,basis_echo2_code_def) =
  to_data basis_echo2 "basis_echo2"

val bf_diff = diff_codes basis_echo_code_def basis_echo2_code_def

val (bf11,bf12) = hd bf_diff
val (bf21,bf22) = (hd o tl) bf_diff

(* aconv (rand f12) (rand bf12) *)
(* aconv (rand f21) (rand bf21) *)

val basis_condLoop =
  let val prog = process_topdecs
        `fun basis_condLoop x = if x = 0 then 0 else basis_condLoop (x - 1);
         val _ = basis_condLoop 5`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val basis_condLoop2 =
  let val prog = process_topdecs
        `fun basis_condLoop x = if x = 0 then 0 else basis_condLoop (x - 2);
         val _ = basis_condLoop 5`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val (basis_condLoop_call_def,basis_condLoop_code_def) =
  to_data basis_condLoop "basis_condLoop"

val (basis_condLoop2_call_def,basis_condLoop2_code_def) =
  to_data basis_condLoop2 "basis_condLoop2"

val (c1,c2) = diff_code basis_condLoop_code_def basis_condLoop2_code_def

Theorem data_safe_basis_condLoop:
 ∀ffi coracle cc n. data_safe (evaluate (basis_condLoop_data_call,
                          initial_state ffi basis_condLoop_data_code
                                        coracle cc T 10000 32 n))
Proof
let
  fun eval_goalsub_tac pat (asms,goal) =
     let
     val tm = goal |> find_term (can (match_term pat))
     val th = EVAL tm
     in PURE_ONCE_REWRITE_TAC [th] (asms,goal)
     end
  val code_lookup = EVERY_lookup
      |> Q.ISPEC `basis_condLoop_data_code`
      |> CONV_RULE ((RAND_CONV o RAND_CONV) (fn tm => basis_condLoop_code_def))
      |> CONV_RULE (RAND_CONV EVAL)
      |> SIMP_RULE (srw_ss()) []
  val strip_makespace =
      qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
      \\ REWRITE_TAC [ bind_def, makespace_def ]
      \\ eval_goalsub_tac ``cut_env _ _`` \\ simp []
      \\ eval_goalsub_tac ``state_locals_fupd _ _``
      \\ Q.UNABBREV_TAC `rest_mkspc`
  val strip_assign =
      qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
      \\ REWRITE_TAC [ bind_def           , assign_def
                     , op_space_reset_def , closLangTheory.op_case_def
                     , cut_state_opt_def  , option_case_def
                     , do_app_def         , data_spaceTheory.op_space_req_def
                     , do_space_def       , closLangTheory.op_distinct
                     , MEM                , IS_NONE_DEF
                     , bvi_to_dataTheory.op_requires_names_eqn ]
      \\ BETA_TAC
      \\ TRY(eval_goalsub_tac ``cut_state _ _`` \\ simp [])
      \\ TRY(eval_goalsub_tac ``get_vars    _ _`` \\ simp [])
      \\ simp [ do_app_aux_def    , set_var_def    , lookup_def
              , domain_IS_SOME    , code_lookup    , size_of_heap_def
              , consume_space_def , with_fresh_ts_def
              , backend_commonTheory.small_enough_int_def ]
      \\ eval_goalsub_tac ``state_locals_fupd _ _``
      \\ Q.UNABBREV_TAC `rest_ass`
  val open_tailcall =
      ASM_REWRITE_TAC [ tailcall_def , find_code_def
                      , get_vars_def , get_var_def
                      , lookup_def   , timeout_def ]
      \\ simp [code_lookup,lookup_def]
      \\ IF_CASES_TAC >- (simp [data_safe_def,size_of_def] \\ EVAL_TAC)
      \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                     , to_shallow_thm , to_shallow_def ]
      \\ eval_goalsub_tac ``state_locals_fupd _ _``
    val close_tailcall =
      ho_match_mp_tac data_safe_res
      \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
    val make_tailcall =
      open_tailcall \\ close_tailcall
    val open_call =
      ASM_REWRITE_TAC [ call_def     , find_code_def , push_env_def
                      , get_vars_def , call_env_def  , dec_clock_def
                      , cut_env_def  , domain_def    , data_safe_def
                      , EMPTY_SUBSET , get_var_def ]
      \\ simp [code_lookup,lookup_def]
      \\ IF_CASES_TAC >- (simp [data_safe_def,size_of_def] \\ EVAL_TAC)
      \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
      \\ eval_goalsub_tac ``state_locals_fupd _ _``
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
    fun strip_call (asms,goal)=
      let val free_names = map (fn tm => fst (dest_var tm)) (free_varsl (goal::asms))
      fun next_name n name =
          if mem name free_names
          then next_name (n+1) (name ^ "_" ^ Int.toString (n+1))
          else [QUOTE name]
      qmatch_goalsub_abbrev_tac (`bind _ ` @ (next_name 0 "rest_call") @ ` _`)
      \\ ONCE_REWRITE_TAC [bind_def]
      \\ open_call \\ rw [data_safe_def]
    val make_if =
      simp [if_var_def,data_safe_def,lookup_def]
      \\ REWRITE_TAC [ isBool_def
                     , backend_commonTheory.bool_to_tag_def
                     , backend_commonTheory.true_tag_def
                     , backend_commonTheory.false_tag_def]
      \\ simp [pop_env_def]
      \\ eval_goalsub_tac ``state_locals_fupd _ _``
  (* Start *)
  (* Turn into shallow embedding  *)
 in
 REWRITE_TAC [ definition "basis_condLoop_data_call_def"
             , to_shallow_thm
             , to_shallow_def
             , initial_state_def ]
  (* Make first call *)
 \\ rpt strip_tac
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 (* Another call *)
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 (* Another tailcall *)
 \\ make_tailcall
 \\ time (ntac 436
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC))
 \\ fs [NOT_LEQ]
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ ntac 6 strip_assign
 \\ open_tailcall
 \\ qmatch_goalsub_abbrev_tac `f (_ (state_locals_fupd _ _))`
 \\ `∀p. f (f p) = f p` by (Cases \\ Cases_on `q` \\ fs [Abbr `f`])
 \\ Q.UNABBREV_TAC `f`
 \\ time (ntac 437
    (ntac 4 strip_assign
    \\ make_if
    \\ ntac 2 strip_assign
    \\ open_tailcall
    \\ ASM_REWRITE_TAC []))
 (* HERE *)
 \\ fs [NOT_LEQ]
 \\ ntac 4 strip_assign
 \\ make_if
 \\ rw []
 \\ Q.UNABBREV_TAC `rest_call`
 \\ ntac 3 strip_assign
 \\ make_tailcall
 \\ ntac 17
    (strip_makespace
    \\ ntac 7 strip_assign
    \\ make_tailcall)
 \\ cheat
 end
QED

val _ = export_theory();
