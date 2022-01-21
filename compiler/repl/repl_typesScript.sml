(*
  Proofs about how the REPL uses types and the type inferencer
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory inferSoundTheory typeSoundTheory semanticsTheory
open ml_progTheory

val _ = new_theory "repl_types";

Datatype:
  simple_type = Bool | Str | Exn
End

Definition to_type_def:
  to_type Bool = Infer_Tapp [] Tbool_num ∧
  to_type Str  = Infer_Tapp [] Tstring_num ∧
  to_type Exn  = Infer_Tapp [] Texn_num
End

Definition check_ref_types_def:
  check_ref_types types (env :semanticPrimitives$v sem_env) (name,ty,loc) ⇔
    nsLookup types.inf_v name = SOME (0,Infer_Tapp [to_type ty] Tref_num) ∧
    nsLookup env.v name = SOME (Loc loc)
End

Inductive repl_types:
[repl_types_init:]
  (∀ffi rs decs types (s:'ffi semanticPrimitives$state) env b.
     infertype_prog init_config decs = Success types ∧
     evaluate$evaluate_decs (init_state ffi) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types types env) rs ⇒
     repl_types b (ffi,rs) (types,s,env)) ∧
[repl_types_skip:]
  (∀ffi rs types junk ck t e (s:'ffi semanticPrimitives$state) env.
     repl_types T (ffi,rs) (types,s,env) ⇒
     repl_types T (ffi,rs) (types,s with <| refs  := s.refs ++ junk                  ;
                                            clock := s.clock - ck                    ;
                                            next_type_stamp := s.next_type_stamp + t ;
                                            next_exn_stamp  := s.next_exn_stamp + e  |>,env)) ∧
[repl_types_eval:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env new_env new_s b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types b (ffi,rs) (new_types,new_s,extend_dec_env new_env env)) ∧
[repl_types_exn:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e new_s b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types b (ffi,rs) (types,new_s,env)) ∧
[repl_types_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e
    new_s name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types b (ffi,rs) (types,new_s with refs := new_store,env)) ∧
[repl_types_str_assign:]
  (∀ffi rs types (s:'ffi semanticPrimitives$state) env t name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types b (ffi,rs) (types,s with refs := new_store,env))
End

Definition ref_lookup_ok_def:
  ref_lookup_ok refs (name:(string,string) id,ty,loc) =
    ∃v:semanticPrimitives$v.
      store_lookup loc refs = SOME (Refv v) ∧
      (ty = Bool ⇒ v = Boolv T ∨ v = Boolv F) ∧
      (ty = Str ⇒ ∃t. v = Litv (StrLit t))
End

Theorem repl_types_F_thm:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  cheat
QED

Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) b rs types s env.
    repl_types b (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  cheat (* Magnus: I believe this can be proved using an
           evaluate-simulation proof from repl_types_F_thm *)
QED

val _ = export_theory();
