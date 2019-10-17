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

fun ops_in_prog prog_def =
  let
    fun rpt_rator t = rpt_rator (rator t) handle _ => t
    val terms = find_terms (can (match_term ``_ : closLang$op``)) ((rhs o concl) prog_def)
  in foldl (fn (x,l) => if exists (aconv x) l then l else (x::l)) [] (map rpt_rator terms)
  end

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

val s = ``s:('c,'ffi) dataSem$state``

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
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
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
                 , add_space_def      , check_lim_def
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
(* * cyes (with mini-basis) * *)
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

val cyes =
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

val cyes2 =
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

val (cyes_call_def,cyes_code_def) =
  to_data cyes "cyes"

val (cyes2_call_def,cyes2_code_def) =
  to_data cyes2 "cyes2"

val f_diff = diff_codes cyes_code_def cyes2_code_def

val (f11,f12) = hd f_diff
val (f21,f22) = (hd o tl) f_diff

Theorem size_of_Number_head:
  ∀vs refs seen n. size_of (Number n::vs) refs seen = size_of vs refs seen
Proof
  Cases \\ rw [size_of_def] \\ pairarg_tac \\ fs []
QED

Theorem size_of_seen_SUBSET:
  ∀vs refs seen n1 seen1 refs1.
  (size_of vs refs seen = (n1,refs1,seen1))
  ⇒ domain seen ⊆  domain seen1
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (ho_match_mp_tac SUBSET_TRANS
     \\ asm_exists_tac \\ fs [])
 \\ every_case_tac \\ fs []
 \\ first_x_assum irule
 \\ rpt (pairarg_tac \\ fs [])
QED

Theorem size_of_le_head:
  ∀vs refs seen v n1 seen1 refs1 n2 refs2 seen2.
   (size_of (v::vs) refs seen = (n1,refs1,seen1)) ∧
   (size_of vs refs seen = (n2,refs2,seen2))
   ⇒ n2 ≤ n1
Proof
  Cases \\ fs [size_of_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
QED

Theorem size_of_le_APPEND:
  ∀a b refs seen n1 seen1 refs1 n2 refs2 seen2.
   (size_of (a ++ b) refs seen = (n1,refs1,seen1)) ∧
   (size_of b refs seen = (n2,refs2,seen2))
   ⇒ n2 ≤ n1
Proof
  Induct
  >- (rw [] \\ fs [])
  \\ rw [] \\ irule LESS_EQ_TRANS
  \\ qexists_tac `FST (size_of (a++b) refs seen)`
  \\ Cases_on `size_of (a++b) refs seen` \\ Cases_on `r`
  \\ simp []
  \\ conj_tac
  >- (first_x_assum irule \\ metis_tac [])
  \\ (ho_match_mp_tac size_of_le_head \\ metis_tac [])
QED

Definition closed_ptrs_list_def:
  (closed_ptrs_list [] refs = T)
∧ (closed_ptrs_list (RefPtr p::vs) refs =
     IS_SOME (lookup p refs) ∧
     closed_ptrs_list vs refs)
∧ (closed_ptrs_list (Block ts tag l::vs) refs =
     closed_ptrs_list l refs ∧
     closed_ptrs_list vs refs)
∧ (closed_ptrs_list (v::vs) refs = closed_ptrs_list vs refs)
Termination
  WF_REL_TAC `(inv_image (measure v1_size) (\(vs,refs). vs))`
End


Definition closed_ptrs_refs_def:
  closed_ptrs_refs refs =
    ∀x l. (sptree$lookup x refs = SOME (ValueArray l))
        ⇒ closed_ptrs_list l refs
End

Definition closed_ptrs_def:
  closed_ptrs vs refs = closed_ptrs_list vs refs ∧ closed_ptrs_refs refs
End

Theorem closed_ptrs_cons_intro:
  ∀vs refs v. closed_ptrs (v::vs) refs ⇒ closed_ptrs vs refs ∧ closed_ptrs [v] refs
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def,closed_ptrs_list_def]
  \\ Cases_on `v` \\ fs [closed_ptrs_list_def]
QED

Theorem closed_ptrs_cons_dest:
  ∀vs refs v. closed_ptrs vs refs ∧ closed_ptrs [v] refs ⇒ closed_ptrs (v::vs) refs
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def,closed_ptrs_list_def]
  \\ Cases_on `v` \\ fs [closed_ptrs_list_def]
QED

Theorem closed_ptrs_cons:
  ∀vs refs v. closed_ptrs (v::vs) refs = closed_ptrs vs refs ∧ closed_ptrs [v] refs
Proof
  rw [] \\ eq_tac \\ fs [closed_ptrs_cons_dest]
  \\ rw [] \\ drule closed_ptrs_cons_intro \\ rw []
QED

Definition live_ptr_list_def:
  (live_ptr_list p [] = F)
∧ (live_ptr_list p (RefPtr n::vs) = ((p = n) ∨ live_ptr_list p vs))
∧ (live_ptr_list p (Block ts tag l::vs) = (live_ptr_list p l ∨ live_ptr_list p vs))
∧ (live_ptr_list p (v::vs) = live_ptr_list p vs)
Termination
  WF_REL_TAC `(inv_image (measure v1_size) (\(p,vs). vs))`
End

Definition live_ptr_def:
  (live_ptr p vs refs =
     live_ptr_list p vs ∨
     (∃x l. (sptree$lookup x refs = SOME (ValueArray l)) ∧
            live_ptr_list p l))
End

Theorem live_ptr_cons:
  ∀p vs refs v. live_ptr p (v::vs) refs = live_ptr p [v] refs ∨ live_ptr p vs refs
Proof
  ho_match_mp_tac live_ptr_list_ind \\ rw [live_ptr_def,live_ptr_list_def]
  \\ EQ_TAC \\ rw []
  \\ TRY (Cases_on `v` \\ fs [live_ptr_list_def] \\ NO_TAC)
  \\ metis_tac []
QED

Theorem size_of_refs_subspt:
  ∀vs refs seen n refs' seen'.
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ subspt refs' refs
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (irule subspt_trans \\ metis_tac [])
  \\ EVERY_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [subspt_delete] \\ irule subspt_trans
  \\ asm_exists_tac \\ fs [subspt_delete]
QED

Theorem not_live_ptr_subspt:
  ∀vs refs refs' p.
    subspt refs' refs ∧
    ¬live_ptr p vs refs
    ⇒¬live_ptr p vs refs'
Proof
  rw [live_ptr_def] \\ fs []
  \\ first_x_assum (qspecl_then [`x`,`l`] assume_tac) \\ rw []
  >- (disj1_tac \\ CCONTR_TAC \\ fs [subspt_lookup]
     \\ first_x_assum drule \\ rw [])
  \\ disj2_tac \\ rw []
QED

Theorem live_ptr_ptr:
  ∀r refs l p.
   (lookup r refs = SOME (ValueArray l))
   ⇒ (live_ptr p [RefPtr r] refs = ((p = r) ∨ live_ptr p l refs))
Proof
  rw [] \\ EQ_TAC
  \\ rw [live_ptr_def] \\ fs [live_ptr_list_def]
  \\ metis_tac []
QED

Theorem live_ptr_delete:
  ∀vs p refs r l.
    p ≠ r ∧ (lookup r refs = SOME (ValueArray l))
    ⇒ (live_ptr p vs refs = live_ptr_list p l ∨ live_ptr p vs (delete r refs))
Proof
  rw []
  \\ EQ_TAC \\ rw [live_ptr_def] \\ fs [live_ptr_list_def]
  >- (Cases_on `x = r` \\ fs [] \\ rveq \\ metis_tac [lookup_delete])
  >- metis_tac []
  \\ Cases_on `x = r` \\ fs [lookup_delete] \\ metis_tac [lookup_delete]
QED

Theorem insert_delete_swap:
  ∀k v x r.
   wf r ∧ k ≠ x
   ⇒ (insert k v (delete x r) = delete x (insert k v r))
Proof
  rw []
  \\ `wf (insert k v (delete x r))` by rw [wf_insert,wf_delete]
  \\ `wf (delete x (insert k v r))` by rw [wf_insert,wf_delete]
  \\ drule spt_eq_thm \\ disch_then (qspec_then `insert k v (delete x r)` drule)
  \\ rw [] \\ rw [lookup_delete,lookup_insert]
QED

Theorem wf_size_of:
  ∀vs refs seen n' refs' seen'.
    wf refs ∧ (size_of vs refs seen = (n',refs',seen'))
    ⇒ wf refs'
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [wf_delete]
QED

Triviality size_of_insert_aux:
  ∀vs refs seen p x n refs' seen'.
    wf refs                 ∧
    ¬live_ptr p vs refs     ∧
    (lookup p refs = NONE)  ∧
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ (size_of vs (insert p x refs) seen = (n,insert p x refs',seen'))
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (qpat_x_assum `¬ _` (assume_tac o ONCE_REWRITE_RULE [live_ptr_cons])
     \\ fs [] \\ first_x_assum drule
     \\ disch_then (qspec_then `x'` assume_tac) \\ rfs [] \\ rveq
     \\ `subspt refs1' refs` by
        (ho_match_mp_tac size_of_refs_subspt
        \\ asm_exists_tac \\ fs [])
     \\ drule wf_size_of \\ disch_then (drule_then assume_tac)
     \\ drule_then (qspec_then `[x]` (drule_then assume_tac)) not_live_ptr_subspt
     \\ first_x_assum (drule_then (drule_then (qspec_then `x'` mp_tac)))
     \\ impl_tac
     >- (CCONTR_TAC \\ fs []
        \\ Cases_on `lookup p refs1'`
        \\ fs [subspt_lookup]
        \\ first_x_assum drule \\ fs [])
     \\ rw [])
  >- (`p ≠ r` by fs [live_ptr_def,live_ptr_list_def]
     \\ fs [lookup_insert]
     \\ every_case_tac \\ fs [] \\ rveq
     >- (rpt (pairarg_tac \\ fs []) \\ rveq
        \\ drule live_ptr_ptr
        \\ disch_then (qspec_then `p` (fn t => fs [t]))
        \\ drule live_ptr_delete
        \\ disch_then (drule_then (qspec_then `l` (fn t => fs [t])))
        \\ drule_then (qspec_then `r` assume_tac) wf_delete
        \\ first_x_assum drule \\ disch_then drule \\ fs [lookup_delete]
        \\ disch_then (qspec_then `x` assume_tac) \\ fs []
        \\ qpat_x_assum `_ = (_,refs'',seen'')` mp_tac
        \\ qmatch_goalsub_abbrev_tac `size_of l refs1 seen`
        \\ qmatch_asmsub_abbrev_tac  `size_of l refs2 seen`
        \\ `refs1 = refs2` suffices_by fs []
        \\ UNABBREV_ALL_TAC \\ fs [insert_delete_swap])
     \\ fs [insert_delete_swap])
  \\ fs [live_ptr_def,live_ptr_list_def]
  \\ first_x_assum drule \\ disch_then drule \\ disch_then drule
  \\ disch_then (qspec_then `x` assume_tac) \\ fs [] \\ rfs []
QED

Theorem closed_ptrs_list_not_live_ptr_list:
  ∀p vs refs.
    closed_ptrs_list vs refs ∧
    (lookup p refs = NONE)
    ⇒ ¬live_ptr_list p vs
Proof
  ho_match_mp_tac live_ptr_list_ind\\ rw [closed_ptrs_list_def,live_ptr_list_def]
  \\ fs [IS_SOME_EXISTS]
  >- (CCONTR_TAC \\ fs [])
  \\ first_x_assum ho_match_mp_tac \\ metis_tac []
QED

Theorem closed_ptrs_not_live_ptr:
  ∀vs refs p.
    closed_ptrs vs refs ∧
    (lookup p refs = NONE)
    ⇒ ¬live_ptr p vs refs
Proof
  rw [closed_ptrs_def,live_ptr_def]
  >- (drule closed_ptrs_list_not_live_ptr_list \\ disch_then drule \\ fs [])
  \\ CCONTR_TAC \\ fs [closed_ptrs_refs_def]  \\ first_x_assum drule \\ strip_tac
  \\ drule closed_ptrs_list_not_live_ptr_list \\ disch_then drule \\ fs []
QED

Theorem size_of_insert:
  ∀vs refs seen p x n refs' seen'.
    wf refs                 ∧
    closed_ptrs vs refs     ∧
    (lookup p refs = NONE)  ∧
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ (size_of vs (insert p x refs) seen = (n,insert p x refs',seen'))
Proof
  rw [] \\ ho_match_mp_tac size_of_insert_aux
  \\ fs [closed_ptrs_not_live_ptr]
QED

Theorem closed_ptrs_APPEND:
  ∀a b refs. closed_ptrs (a ++ b) refs = closed_ptrs a refs ∧ closed_ptrs b refs
Proof
  Induct
  >- (rw [closed_ptrs_def,closed_ptrs_list_def] \\ metis_tac [])
  \\ rw [] \\ ONCE_REWRITE_TAC [closed_ptrs_cons] \\ metis_tac []
QED

Theorem closed_ptrs_refs_insert:
  ∀refs p x y.
    closed_ptrs_refs refs ∧
    (lookup p refs = NONE)
    ⇒ closed_ptrs_refs (insert p (ByteArray x y) refs)
Proof
  rw [closed_ptrs_refs_def]
  \\ Cases_on `x' = p` \\ fs [lookup_insert]
  \\ first_x_assum drule
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`refs`,`refs`)
  \\ Q.SPEC_TAC (`l`,`l`)
  \\ ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_list_def]
  \\ metis_tac [IS_SOME_EXISTS,lookup_insert]
QED

Theorem closed_ptrs_insert:
  ∀vs refs p x.
  closed_ptrs vs refs
  ∧ (lookup p refs = NONE)
  ∧ closed_ptrs_refs (insert p x refs)
  ⇒ closed_ptrs vs (insert p x refs)
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def]
  \\ fs [closed_ptrs_list_def]
  \\ metis_tac [lookup_insert,IS_SOME_EXISTS]
QED

Theorem data_safe_cyes_code:
  ∀s ts.
   s.safe_for_space ∧
   wf s.refs ∧
   closed_ptrs (stack_to_vs s) s.refs ∧
   size_of_heap s + 4 ≤ s.limits.heap_limit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (lookup 0 s.locals = SOME (Number 97)) ∧
   (s.code = cyes_data_code)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
  let
    val code_lookup   = mk_code_lookup `cyes_data_code` cyes_code_def
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
  \\ `toListA [] (inter s.locals (LS ())) = [Number 97]`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def,toListA_def])
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ `cut_env (LS ()) s.locals = SOME (LS (Number 97))`
     by (REWRITE_TAC [cut_env_def,domain_def,SUBSET_DEF]
        \\ fs [domain_lookup] \\ Cases_on `s.locals`
        \\ fs [lookup_def,inter_def,toListA_def])
  \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ eval_goalsub_tac ``cut_env _ _`` \\ simp []
  (* strip_assign *)
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ ntac 3 (strip_assign \\ fs [])
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ ASM_REWRITE_TAC [ call_def     , find_code_def , push_env_def
                     , get_vars_def , call_env_def  , dec_clock_def
                     , cut_env_def  , domain_def    , data_safe_def
                     , EMPTY_SUBSET , get_var_def ]
  \\ simp [code_lookup,lookup_def,domain_IS_SOME]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ `n ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ irule LESS_EQ_TRANS \\ qexists_tac `n' + 3` \\ rw [])
  \\ simp []
  \\ Q.UNABBREV_TAC `safe`
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 4 strip_assign
  (* open_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ Cases_on `ts` \\ fs [size_of_def,lookup_def]
     \\ `n1''''' ≤ n''` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ Cases_on `lookup (SUC n) seen1'''''` \\ fs [] \\ rveq \\ fs [])
  \\ simp []
  \\ Q.UNABBREV_TAC `safe`
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  (* strip_assign *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ ASM_REWRITE_TAC [ call_def     , find_code_def , push_env_def
                     , get_vars_def , call_env_def  , dec_clock_def
                     , cut_env_def  , domain_def    , data_safe_def
                     , EMPTY_SUBSET , get_var_def ]
  \\ simp [code_lookup,lookup_def,domain_IS_SOME]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ Cases_on `ts` \\ fs [size_of_def,lookup_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head] \\ rveq
     \\ Cases_on `lookup (SUC n) seen1'''''` \\ fs [])
  \\ simp [] \\ Q.UNABBREV_TAC `safe`
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ ntac 4 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def]
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ `closed_ptrs (b ++ c) s.refs` by fs [closed_ptrs_APPEND]
     \\ map_every  Q.UNABBREV_TAC [`a`,`b`,`c`]
     \\ drule size_of_insert \\ disch_then drule
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ disch_then drule \\ disch_then (drule_then (qspec_then `x` assume_tac))
     \\ fs [] \\ rveq \\ rfs []
     \\ Q.UNABBREV_TAC `x` \\ fs [])
  \\ simp [] \\ Q.UNABBREV_TAC `safe`
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ strip_assign
  \\ fs [lookup_insert]
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ fs []
  \\ `lookup p2 (insert p1 (ByteArray T [97w]) s.refs) = NONE` by
     (fs [lookup_insert]
     \\ rw [Abbr `p2`, least_from_def]
     >- (Cases_on `p1 = 0` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `wf (insert p1 (ByteArray T [97w]) s.refs)` by fs [wf_insert]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`b ++ c`,`LN`,`p2`,`y`,`n1''`,`refs1''`,`seen1''`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs []
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ qmatch_asmsub_rename_tac `size_of (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then [`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ impl_tac
     >- fs [closed_ptrs_APPEND]
     \\ rw [] \\ Cases_on `lookup ts seen1'` \\ fs [] \\ rveq
     \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
     \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
     \\ `n1' ≤ n'''''` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ Q.UNABBREV_TAC `safe` \\ fs []
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []` \\ fs [])
  >- simp [data_safe_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ Q.UNABBREV_TAC `rest_call`
  (* strip tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter]
  \\ IF_CASES_TAC
  >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
  \\ qmatch_goalsub_abbrev_tac `data_safe (_ s0)`
  \\ first_x_assum (qspec_then `s0` assume_tac)
  \\ `s0.clock < s.clock` by (UNABBREV_ALL_TAC \\ rw [])
  \\ first_x_assum (drule_then irule) \\ Q.UNABBREV_TAC `s0` \\  fs []
  \\ simp [ size_of_heap_def,size_of_Number_head,stack_to_vs_def
          , lookup_def,toList_def,toListA_def
          , wf_insert, wf_delete ]
  \\ rw []
  >- (pairarg_tac \\ fs []
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`b ++ c`,`LN`,`p2`,`y`,`n1'`,`refs1'`,`seen1'`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs [size_of_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [size_of_Number_head]
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ qmatch_asmsub_rename_tac `size_of (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then [`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ impl_tac >- fs [closed_ptrs_APPEND]
     \\ rveq \\ rw [] \\ Cases_on `lookup ts _` \\ fs [] \\ rveq
     \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
     \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
     \\ `n ≤ n''` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ fs [closed_ptrs_def])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [closed_ptrs_def])
   \\ ONCE_REWRITE_TAC [closed_ptrs_cons]
   \\ conj_tac >- fs [closed_ptrs_APPEND,stack_to_vs_def]
   \\ fs [closed_ptrs_def,closed_ptrs_list_def]
  end
QED

Theorem data_safe_cyes_code_shallow[local] =
  data_safe_cyes_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem closed_ptrs_refs_compute[compute]:
  ∀refs. closed_ptrs_refs refs =
     EVERY (λ(k,v). case v of
                   | ByteArray _ _ => T
                   | ValueArray l => closed_ptrs_list l refs)
          (toAList refs)
Proof
  rw [] \\ eq_tac \\ rw [closed_ptrs_refs_def]
  >- (fs [EVERY_MEM] \\ rw [] \\ Cases_on `e`
     \\ fs [MEM_toAList] \\ Cases_on `r` \\ fs []
     \\ first_x_assum drule \\ fs [])
  \\ fs [EVERY_MEM]
  \\ first_x_assum (qspec_then `(x,ValueArray l)` assume_tac)
  \\ fs [MEM_toAList]
QED

Theorem data_safe_cyes_code_abort:
 ∀s ts.
   (lookup 0 s.locals = SOME (Number 97)) ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   (s.code = cyes_data_code)
   ⇒ ∃s' e. evaluate ((SND o SND) ^f21, s) =
       (SOME (Rerr (Rabort e)),s')
Proof
  let
    val code_lookup   = mk_code_lookup `cyes_data_code` cyes_code_def
    val strip_assign  = mk_strip_assign code_lookup
    val open_call     = mk_open_call code_lookup
    val make_call     = mk_make_call open_call
    val strip_call    = mk_strip_call open_call
    val open_tailcall = mk_open_tailcall code_lookup
    val make_tailcall = mk_make_tailcall open_tailcall
  in
  measureInduct_on `^s.clock`
  \\ rw [to_shallow_def,to_shallow_thm]
  \\ strip_call
  \\ `(inter s.locals (LS ())) = LS (Number 97)`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def])
  \\ strip_makespace
  \\ ntac 6 strip_assign
  \\ strip_call
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call_1 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  (* open_call *)
  \\ ASM_REWRITE_TAC [ call_def     , find_code_def , push_env_def
                     , get_vars_def , call_env_def  , dec_clock_def
                     , cut_env_def  , domain_def    , data_safe_def
                     , EMPTY_SUBSET , get_var_def ]
  \\ simp [code_lookup,lookup_def,domain_IS_SOME,lookup_insert]
  \\ IF_CASES_TAC >- simp []
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac [] >- metis_tac [] >- metis_tac [] >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw [] >- metis_tac []
        \\ CCONTR_TAC \\ fs [lookup_insert])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
        \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
        \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
        \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
     \\ CCONTR_TAC \\ fs [lookup_insert])
  \\ strip_assign \\ fs [lookup_insert]
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []`) >- simp []
  \\ strip_assign \\ strip_assign
  \\ rw [return_def,lookup_def]
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_call`
  (*  make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter]
  \\ IF_CASES_TAC
  >- simp []
  \\ eval_goalsub_tac ``call_env _ _``
  \\ qmatch_goalsub_abbrev_tac `evaluate (p0,s0)`
  \\ `s0.clock < s.clock` by fs [Abbr `s0`]
  \\ first_x_assum (drule_then (qspec_then `ts + 1` mp_tac))
  \\ impl_tac >- (fs [Abbr `s0`] \\ EVAL_TAC)
  \\ rw [] \\ fs []
  end
QED

Theorem data_safe_cyes_code_abort_shallow[local] =
  data_safe_cyes_code_abort |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_cyes:
 ∀ffi coracle cc n. data_safe (evaluate (cyes_data_call,
                          initial_state ffi cyes_data_code
                                        coracle cc T 1000 32 n))
Proof
 let
  val code_lookup   = mk_code_lookup `cyes_data_code` cyes_code_def
  val strip_assign  = mk_strip_assign code_lookup
  val open_call     = mk_open_call code_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 REWRITE_TAC [ definition "cyes_data_call_def"
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
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr (Rabort e')),s')`
     by (UNABBREV_ALL_TAC
        \\ ho_match_mp_tac data_safe_cyes_code_abort_shallow
        \\ fs [] \\ EVAL_TAC)
  \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac data_safe_cyes_code_shallow
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  end
QED

val basis_pureLoop =
  let val prog = process_topdecs
      `fun pureLoop x = pureLoop x;
       val _ = pureLoop 1`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val (basis_pureLoop_call_def,basis_pureLoop_code_def) =
  to_data basis_pureLoop "basis_pureLoop"

val basis_pureLoop_ops = ops_in_prog basis_pureLoop_code_def

val basis_cyes =
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

val basis_cyes2 =
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

val (basis_cyes_call_def,basis_cyes_code_def) =
  to_data basis_cyes "basis_cyes"

val (basis_cyes2_call_def,basis_cyes2_code_def) =
  to_data basis_cyes2 "basis_cyes2"

val basis_cyes_ops = ops_in_prog basis_cyes_code_def

val bf_diff = diff_codes basis_cyes_code_def basis_cyes2_code_def

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

val basis_condLoop_ops = ops_in_prog basis_condLoop_code_def

fun sub_list l1 l2 = filter (fn c => not (exists (aconv c) l2)) l1

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
