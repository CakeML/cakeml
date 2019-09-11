(*
  Define a monad to make dataLang ASTs nicer to work with
*)
open preamble dataLangTheory dataSemTheory;

val _ = new_theory"data_monad";

Type M = ``:('c,'ffi) dataSem$state -> (v, v) result option # ('c,'ffi) dataSem$state``

val s = ``s:('c,'ffi) dataSem$state``
val f = ``f: ('c,'ffi) M``
val g = ``g: ('c,'ffi) M``

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
    (SOME (Rerr(Rabort Rtimeout_error)),
     s with <| stack := []; locals := LN|>)
End

Definition bind_def:
  bind ^f ^g s =
    case f s of
    | (SOME res, s1) => (SOME res, s1)
    | (NONE, s1) => g s1
End

Definition if_var_def:
  if_var n ^f ^g s =
    case lookup n s.locals of
    | NONE => fail s
    | SOME v => if isBool T v then f s else
                if isBool F v then g s else fail s
End

Definition return_def[simp]:
  return n s =
    case lookup n s.locals of
    | NONE => fail s
    | SOME v => (SOME (Rval v), s with locals := LN)
End

Definition tailcall_def:
  tailcall dest args ^s =
    case get_vars args s.locals of
    | NONE => fail s
    | SOME vs =>
      case find_code dest vs s.code of
      | NONE => fail s
      | SOME (args,prog) =>
          if s.clock = 0 then timeout s
          else
            let (res,s) = evaluate (prog, call_env args (dec_clock s)) in
              if res = NONE then fail s else (res,s)
End

Definition makespace_def:
  makespace k names s =
     case cut_env names s.locals of
     | NONE => fail s
     | SOME env => (NONE,add_space s k with locals := env)
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
          | Rerr e => (SOME (Rerr e), s with <| stack := []; locals := LN |>)
          | Rval (v,s) => (NONE, set_var dest v s)
End

Overload ":=" = ``assign``
val _ = set_fixity ":=" (Infixl 480);

Definition move_def:
  move dest src s =
    case lookup src s.locals of
    | NONE => fail s
    | SOME v => (NONE, set_var dest v s)
End

Definition tick_def:
  tick s =
      if s.clock = 0
      then timeout s
      else (NONE,dec_clock s)
End

Definition to_shallow_def:
  to_shallow Skip            = skip /\
  to_shallow Tick            = tick /\
  to_shallow (Move dest src) = move dest src /\
  to_shallow (MakeSpace k names) =  makespace k names /\
  to_shallow (Assign n op vars cutset) = assign n (op, vars, cutset) /\
  to_shallow (Seq p1 p2) = bind (to_shallow p1) (to_shallow p2) /\
  to_shallow (Return n) = return n /\
  to_shallow (Call NONE dest args NONE) = tailcall dest args /\
  to_shallow (Call NONE dest args (SOME x)) = fail /\
  to_shallow (If n p1 p2) = if_var n (to_shallow p1) (to_shallow p2) /\
  to_shallow c = ARB c "not yet done..."
End

Theorem to_shallow_thm:
  !ast ^s. evaluate (ast, s) = to_shallow ast s
Proof
  Induct \\ fs [to_shallow_def,evaluate_def]
  \\ rpt gen_tac
  THEN1 rw [move_def,get_var_def]
  THEN1
   (rename [`Call ret dest args handler`]
    \\ Cases_on `ret` THEN1
     (reverse (Cases_on `handler`) \\ fs [to_shallow_def]
      \\ fs [tailcall_def]
      \\ rpt (TOP_CASE_TAC \\ fs [call_env_def,fromList_def]))
    \\ cheat)
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 rw [makespace_def]
  THEN1 cheat
  THEN1
   (fs [get_var_def] \\ rw [] \\ CASE_TAC
    \\ fs [call_env_def,fromList_def])
  THEN1 rw[tick_def,timeout_def,call_env_def,state_component_equality,fromList_def]
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

val _ = export_theory();
