(*
  Define a monad to make dataLang ASTs nicer to work with
*)
open preamble dataLangTheory dataSemTheory ml_monadBaseTheory;

val _ = new_theory"data_monad";

val s = ``s:('c,'ffi) dataSem$state``
val f = ``(f: (('c,'ffi) dataSem$state, unit, (v,v) result) M)``
val g = ``(g: (('c,'ffi) dataSem$state, unit, (v,v) result) M)``

Definition Corr_def:
  Corr ast ^f <=>
    !^s. evaluate (ast, s) =
           case f s of
           | (Success (), s1) => (NONE, s1)
           | (Failure res, s1) => (SOME res, s1)
End

Definition skip_def[simp]:
  (skip : (('c,'ffi) dataSem$state, unit, (v,v) result) M) s =
    (Success (), s)
End

Definition bind_def:
  bind ^f ^g s =
    case f s of
    | (Failure res, s1) => (Failure res, s1)
    | (Success _, s1) => g s1
End

Definition return_def[simp]:
  return n s =
    case lookup n s.locals of
    | NONE => (Failure (Rerr(Rabort Rtype_error)), s)
    | SOME v => (Failure (Rval v), s with locals := LN)
End

Definition tailcall_def:
  tailcall dest args ^s =
    case get_vars args s.locals of
    | NONE => (Failure (Rerr(Rabort Rtype_error)), s)
    | SOME vs =>
      case find_code dest vs s.code of
      | NONE => (Failure (Rerr(Rabort Rtype_error)), s)
      | SOME (args,prog) =>
          if s.clock = 0 then
            (Failure (Rerr(Rabort Rtimeout_error)),
             s with <| stack := [] ; locals := LN |>)
          else
            case evaluate (prog, call_env args (dec_clock s)) of
            | (NONE, s1) => (Failure (Rerr(Rabort Rtype_error)), s1)
            | (SOME r, s1) => (Failure r, s1)
End

Definition to_shallow_def:
  to_shallow Skip = skip /\
  to_shallow (Seq p1 p2) = bind (to_shallow p1) (to_shallow p2) /\
  to_shallow (Return n) = return n /\
  to_shallow (Call NONE dest args NONE) = tailcall dest args
End

Theorem Corr_thm:
  !ast. Corr ast (to_shallow ast)
Proof
  Induct \\ fs [to_shallow_def,Corr_def,evaluate_def]
  \\ rpt gen_tac
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1
   (fs [get_var_def] \\ rw [] \\ CASE_TAC
    \\ fs [call_env_def,fromList_def])
  THEN1 cheat
QED

(* Overload monad_bind[local] = ``st_ex_bind`` *)
(* Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)`` *)
Overload monad_unitbind[local] = ``\x y. bind x y``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

val _ = export_theory();
