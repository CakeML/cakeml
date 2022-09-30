(*
  Define a monad to make dataLang ASTs nicer to work with
*)
open preamble dataLangTheory dataSemTheory;

val _ = new_theory"data_monad";

Type M = ``:('c,'ffi) dataSem$state -> (v, v) result option # ('c,'ffi) dataSem$state``

val s = ``s:('c,'ffi) dataSem$state``
val f = ``f: ('c,'ffi) M``
val g = ``g: ('c,'ffi) M``

Theorem OPTION_MAP2_ADD_SOME_0[simp]:
  (OPTION_MAP2 $+ x (SOME 0n)) = x
Proof
  Cases_on `x` \\ fs []
QED

Definition skip_def[simp]:
  (skip : ('c,'ffi) M) s =
    (NONE, s)
End

Definition fail_def[simp]:
  (fail : ('c,'ffi) M) s =
    (SOME (Rerr(Rabort Rtype_error)), s)
End

Definition timeout_def[simp]:
  (timeout : ('c,'ffi) M) s =
    (SOME (Rerr(Rabort Rtimeout_error)),s)
End

Definition bind_def:
  bind ^f ^g s =
    case f s of
    | (SOME res, s1) => (SOME res, s1)
    | (NONE, s1) => g s1
End

Definition if_var_def:
  if_var n ^f ^g s =
    case sptree$lookup n s.locals of
    | NONE => fail s
    | SOME v => if isBool T v then f s else
                if isBool F v then g s else fail s
End

Definition return_def[simp]:
  return n s =
    case sptree$lookup n s.locals of
    | NONE => fail s
    | SOME v => (SOME (Rval v), flush_state F s)
End

Definition tailcall_def:
  tailcall dest args ^s =
    case get_vars args s.locals of
    | NONE => fail s
    | SOME vs =>
      case find_code dest vs s.code s.stack_frame_sizes of
      | NONE => fail s
      | SOME (args,prog,ss) =>
        if s.clock = 0
        then timeout (flush_state T s)
        else let (res,s) = evaluate (prog, call_env args ss (dec_clock s))
             in if res = NONE then fail s else (res,s)
End

Definition call_def:
  call (n,names) dest args handler s =
     case get_vars args s.locals of
     | NONE => fail s
     | SOME xs =>
       (case find_code dest xs s.code s.stack_frame_sizes of
        | NONE => fail s
        | SOME (args1,prog,ss) =>
          (case cut_env names s.locals of
           | NONE => fail s
           | SOME env =>
             let s1 = call_env args1 ss
                        (push_env env (IS_SOME handler) (dec_clock s))
             in if s.clock = 0
                then timeout (s1 with <| stack := [] ; locals := LN |>)
                else (case evaluate (prog, call_env args1 ss
                            (push_env env (IS_SOME handler) (dec_clock s))) of
                      | (SOME (Rval x),s2) =>
                        (case pop_env s2 of
                         | NONE => fail s2
                         | SOME s1 => (NONE, set_var n x s1))
                      | (SOME (Rerr(Rraise x)),s2) =>
                        (* if handler is present, then handle exc *)
                        (case handler of
                         | NONE => (SOME (Rerr(Rraise x)),s2)
                         | SOME (n,h) => evaluate (h, set_var n x s2))
                      | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                      | res => res)))
End

Definition makespace_def:
  makespace k names s =
     case cut_env names s.locals of
     | NONE => fail s
     | SOME env => (NONE,add_space (s with locals := env) k)
End

Definition assign_def:
  assign dest (op, args, names_opt) s =
    if op_requires_names op /\ IS_NONE names_opt then fail s else
      case cut_state_opt names_opt s of
      | NONE => fail s
      | SOME s =>
        case get_vars args s.locals of
        | NONE => fail s
        | SOME xs =>
          case do_app op xs s of
          | Rerr e => (SOME (Rerr e), flush_state T (install_sfs op s))
          | Rval (v,s) => (NONE, set_var dest v (install_sfs op s))
End

Overload ":≡" = ``assign``
val _ = set_fixity ":≡" (Infixl 480);

Definition move_def:
  move dest src s =
    case sptree$lookup src s.locals of
    | NONE => fail s
    | SOME v => (NONE, set_var dest v s)
End

Definition tick_def:
  tick s =
      if s.clock = 0
      then timeout (flush_state T s)
      else (NONE,dec_clock s)
End

Definition raise_def:
  raise n s =
    case get_var n s.locals of
    | NONE => fail s
    | SOME x =>
      (case jump_exc s of
       | NONE => fail s
       | SOME s => (SOME (Rerr(Rraise x)),s))
End

Definition to_shallow_def:
  to_shallow Skip            = skip /\
  to_shallow Tick            = tick /\
  to_shallow (Move dest src) = move dest src /\
  to_shallow (Raise n)       = raise n /\
  to_shallow (MakeSpace k names) =  makespace k names /\
  to_shallow (Assign n op vars cutset) = assign n (op, vars, cutset) /\
  to_shallow (Seq p1 p2) = bind (to_shallow p1) (to_shallow p2) /\
  to_shallow (Return n) = return n /\
  to_shallow (Call NONE       dest args NONE) = tailcall dest args /\
  to_shallow (Call NONE       dest args (SOME x)) = fail /\
  to_shallow (Call (SOME ret) dest args handler) = call ret dest args handler /\
  to_shallow (If n p1 p2) = if_var n (to_shallow p1) (to_shallow p2)
End

Theorem to_shallow_thm:
  !ast ^s. evaluate (ast, s) = to_shallow ast s
Proof
  Induct \\ fs [to_shallow_def,evaluate_def]
  \\ rpt gen_tac
  (* Move *)
  >- rw [move_def,get_var_def]
  (* Call *)
  >-(rename [`Call ret dest args handler`]
    \\ Cases_on `ret`
    >- (reverse (Cases_on `handler`) \\ fs [to_shallow_def]
       \\ fs [tailcall_def]
       \\ rpt (TOP_CASE_TAC \\ fs [call_env_def,fromList_def]))
    \\ PairCases_on `x` \\ rw[to_shallow_def,call_def,call_env_def]
    \\ rpt (TOP_CASE_TAC \\ fs [call_env_def,fromList_def]))
  (* Assign *)
  >-(rw [assign_def] \\ fs []
    \\ rpt (TOP_CASE_TAC \\ fs [call_env_def,fromList_def]))
  (* Seq/Bind *)
  >- (rw[bind_def]  \\ rpt (TOP_CASE_TAC \\ fs []))
  (* If *)
  >- (rw[if_var_def] \\ fs [get_var_def]
     \\ rpt (TOP_CASE_TAC \\ fs []))
  (* Makespace *)
  >- rw [makespace_def]
  (* Raise *)
  >- rw [raise_def]
  (* Return *)
  >- (fs [get_var_def] \\ rw []
     \\ CASE_TAC \\ fs [call_env_def,fromList_def])
  (* Tick *)
  \\ rw[tick_def,timeout_def,call_env_def,state_component_equality,fromList_def]
QED

Overload monad_unitbind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

val challenge_program =
  ``Seq (Assign 2 (TagLenEq 0 0) [0] NONE)
        (If 2 (Return 1)
              (Seq (Assign 5 (Const 0) [] NONE)
              (Seq (Assign 3 El [0; 5] NONE)
              (Seq (Assign 5 (Const 1) [] NONE)
              (Seq (Assign 6 El [0; 5] NONE)
              (Seq (Assign 4 (Cons 0) [5; 1] NONE)
                   (Call NONE (SOME 500) [6; 4] NONE)))))))``

val to_shallow_thm =
  ``to_shallow ^challenge_program``
  |> REWRITE_CONV [to_shallow_def]

val res = ``(res:(v, v) result option)``

Definition data_safe_def:
  data_safe (^res ,^s) = s.safe_for_space
End

Theorem data_safe_res:
  ∀p f. data_safe p ∧ (∀x. (SND o f) x = SND x) ⇒ data_safe (f p)
Proof
  Cases \\ rw [data_safe_def]
  \\ Cases_on `f (q,r)`
  \\ fs [data_safe_def]
  \\ first_x_assum (qspec_then `(q,r)` assume_tac)
  \\ fs [] \\ rfs []
QED

Theorem data_safe_bind:
  ∀f g s.
   data_safe (f s) ∧ data_safe (g (SND (f s)))
   ⇒ data_safe (bind f g s)
Proof
 rw [data_safe_def,bind_def]
 \\ Cases_on `f s` \\ Cases_on `q` \\ fs []
QED

Theorem data_safe_move:
  ∀s dest src. s.safe_for_space ⇒ data_safe (move dest src s)
Proof
  rw [move_def] \\ every_case_tac \\ rw [data_safe_def,set_var_def]
QED

Theorem set_var_safe_for_space:
  ∀s v x. s.safe_for_space ⇒ (set_var v x s).safe_for_space
Proof
  rw [set_var_def]
QED

Theorem pop_env_safe_for_space:
  ∀s x. s.safe_for_space ∧ (pop_env s = SOME x) ⇒ x.safe_for_space
Proof
  rw [pop_env_def] \\ EVERY_CASE_TAC \\ fs [state_component_equality]
QED

Theorem data_safe_bind_return:
  ∀f n s. data_safe (f s) ⇒ data_safe (bind f (return n) s)
Proof
  rw [bind_def,return_def]
  \\ EVERY_CASE_TAC
  \\ fs [data_safe_def,call_env_def,flush_state_def]
QED

Theorem data_safe_bind_error:
  ∀f g s s' err. data_safe (f s) ∧ (f s = (SOME (Rerr err),s')) ⇒ data_safe (bind f g s)
Proof
  rw [data_safe_def,bind_def]
  \\ rw [] \\ fs [data_safe_def]
QED

Theorem data_safe_bind_some:
  ∀f g s s' err. data_safe (f s) ∧ (f s = (SOME err,s')) ⇒ data_safe (bind f g s)
Proof
  rw [data_safe_def,bind_def]
  \\ rw [] \\ fs [data_safe_def]
QED

val _ = export_theory();
