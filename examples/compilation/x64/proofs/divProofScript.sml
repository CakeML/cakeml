(*
  Prove various divergent programs are safe for space (wrt some limit)
*)

open preamble divCompileTheory dataSemTheory data_monadTheory

val _ = new_theory "divProof"

Overload monad_unitbind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.temp_add_monadsyntax()

(* TODO *)
(* Theorem data_safe_assign: *)
(*   s.safe_for_space *)
(*   ∧  ?? *)
(* data_safe (assign dest (op,args,names_opt) s) *)
(* Proof *)
(* ??  *)
(* QED *)

Theorem data_safe_coreLoop:
  data_safe (evaluate (pureLoop_data_call,
                  initial_state ARB outerLoop_data_code
                                ARB ARB T 1000 4 100000))
Proof
  (* Start *)
  (* Turn into shallow embedding  *)
  REWRITE_TAC [to_shallow_thm,to_shallow_def,pureLoop_data_call_def]
  (* Make first call *)
  \\ rw [ pureLoop_data_call_def
        , initial_state_def
        , find_code_def
        , get_vars_def
        , EVAL ``lookup 60 outerLoop_data_code``
        , tailcall_def]
  (* Turn it into shallow embedding again *)
  \\ REWRITE_TAC [to_shallow_thm,to_shallow_def,call_env_def,dec_clock_def]
  \\ ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
  (* Operate *)
  \\ rw []
  \\ ho_match_mp_tac data_safe_bind
  \\ conj_tac
  >- cheat
  \\ cheat
  (* TODO *)
QED

val _ = export_theory();
