(*
  Proving that kernel types are abstract.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory;
open kernelTheory ast_extrasTheory;

val _ = new_theory "abstype";

val _ = set_grammar_ancestry [
  "kernel", "ast_extras", "termination", "namespaceProps",
  "semanticPrimitivesProps", "misc"];

(* -------------------------------------------------------------------------
 * We define a set of permissions for our value relation, which restricts
 * what our code can do.
 * ------------------------------------------------------------------------- *)

Datatype:
  permission = FFIWrite string (* Write to FFI channel with name     *)
             | RefMention loc  (* Mention reference using pointer    *)
             | RefUpdate       (* Write to references                *)
             | RefAlloc        (* Allocate new references            *)
             | RefPmatch       (* Do pattern-matching on references  *)
             | DoEval          (* Call Eval                          *)
End

Definition pats_ok_def:
  pats_ok ps = every_pat $ λp. case p of Pref p => RefPmatch ∈ ps | _ => T
End

Theorem pats_ok_thm[simp] =
  [“pats_ok ps Pany”,
   “pats_ok ps (Pvar n)”,
   “pats_ok ps (Plit lit)”,
   “pats_ok ps (Pcon cn pats)”,
   “pats_ok ps (Pref p)”,
   “pats_ok ps (Pas p n)”,
   “pats_ok ps (Ptannot p t)”]
  |> map (SIMP_CONV (srw_ss()) [pats_ok_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM pats_ok_def, SF ETA_ss])
  |> LIST_CONJ;

Definition perms_ok_exp_def:
  perms_ok_exp ps =
    every_exp $ λx.
      case x of
        App op xs =>
          (op = Eval ⇒ DoEval ∈ ps) ∧
          (op = Opref ⇒ RefAlloc ∈ ps) ∧
          (op = Opassign ⇒ RefUpdate ∈ ps) ∧
          (∀chn. op = FFI chn ⇒ FFIWrite chn ∈ ps)
      | Handle x pes => EVERY (pats_ok ps) (MAP FST pes)
      | Mat x pes => EVERY (pats_ok ps) (MAP FST pes)
      | _ => T
End

Theorem perms_ok_exp_thm[simp] =
  [“perms_ok_exp ps (Raise e)”,
   “perms_ok_exp ps (Handle e pes)”,
   “perms_ok_exp ps (Lit lit)”,
   “perms_ok_exp ps (Con cn es)”,
   “perms_ok_exp ps (Var n)”,
   “perms_ok_exp ps (Fun n x)”,
   “perms_ok_exp ps (App op xs)”,
   “perms_ok_exp ps (Log lop x y)”,
   “perms_ok_exp ps (If x y z)”,
   “perms_ok_exp ps (Mat e pes)”,
   “perms_ok_exp ps (Let opt x y)”,
   “perms_ok_exp ps (Letrec f x)”,
   “perms_ok_exp ps (Tannot x t)”,
   “perms_ok_exp ps (Lannot x l)”]
  |> map (SIMP_CONV (srw_ss()) [perms_ok_exp_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM perms_ok_exp_def, SF ETA_ss])
  |> LIST_CONJ;

Definition perms_ok_dec_def:
  perms_ok_dec ps =
    every_dec $ λd.
      case d of
        Dlet locs pat exp => pats_ok ps pat ∧ perms_ok_exp ps exp
      | Dletrec locs funs => EVERY (perms_ok_exp ps) (MAP (SND o SND) funs)
      | _ => T
End

Theorem perms_ok_dec_thm[simp] =
  [“perms_ok_dec ps (Dlet l p e)”,
   “perms_ok_dec ps (Dletrec l f)”,
   “perms_ok_dec ps (Dtype l tds)”,
   “perms_ok_dec ps (Dtabbrev l ns n t)”,
   “perms_ok_dec ps (Dexn l n ts)”,
   “perms_ok_dec ps (Dmod n ds)”,
   “perms_ok_dec ps (Dlocal ds1 ds2)”,
   “perms_ok_dec ps (Denv n)”]
  |> map (SIMP_CONV (srw_ss()) [perms_ok_dec_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM perms_ok_dec_def, SF ETA_ss])
  |> LIST_CONJ;

Inductive perms_ok:
[~Conv:]
  (∀ps opt vs.
     EVERY (perms_ok ps) vs ⇒
       perms_ok ps (Conv opt vs)) ∧
[~Closure:]
  (∀ps env n x.
     perms_ok_env ps (freevars x DIFF {Short n}) env ∧
     perms_ok_exp ps x ⇒
       perms_ok ps (Closure env n x)) ∧
[~Recclosure:]
  (∀ps env f n.
     perms_ok_env ps
                  (BIGUNION (set (MAP (λ(fn,vn,x). freevars x DIFF
                                                   {Short fn; Short vn}) f)))
                  env ∧
     EVERY (perms_ok_exp ps) (MAP (SND o SND) f) ⇒
       perms_ok ps (Recclosure env f n)) ∧
[~Vectorv:]
  (∀ps vs.
     EVERY (perms_ok ps) vs ⇒
       perms_ok ps (Vectorv vs)) ∧
[~Litv:]
  (∀ps lit.
     perms_ok ps (Litv lit)) ∧
[~Loc:]
  (∀ps loc.
     RefMention loc ∈ ps ⇒
       perms_ok ps (Loc loc)) ∧
[~Env:]
  (∀ps env ns.
     perms_ok_env ps UNIV env  ⇒
       perms_ok ps (Env env ns)) ∧
[~env:]
  (∀ps fvs env.
     (∀n v.
        n ∈ fvs ∧
        nsLookup env.v n = SOME v ⇒
          perms_ok ps v) ⇒
       perms_ok_env ps fvs env)
End

Theorem perms_ok_def =
  [“perms_ok ps (Litv lit)”,
   “perms_ok ps (Conv opt vs)”,
   “perms_ok ps (Closure env n x)”,
   “perms_ok ps (Recclosure env f n)”,
   “perms_ok ps (Loc loc)”,
   “perms_ok ps (Vectorv vs)”,
   “perms_ok ps (Env env ns)”]
  |> map (SIMP_CONV (srw_ss()) [Once perms_ok_cases])
  |> LIST_CONJ;

Theorem perms_ok_env_def =
  SIMP_CONV (srw_ss()) [Once perms_ok_cases] “perms_ok_env ps fvs env”;

Theorem perms_ok_env_UNION:
  perms_ok_env ps (x ∪ y) env ⇔
    perms_ok_env ps x env ∧
    perms_ok_env ps y env
Proof
  rw [perms_ok_env_def, EQ_IMP_THM]
  \\ gs [SF SFY_ss]
QED

Theorem perms_ok_env_BIGUNION:
  perms_ok_env ps (BIGUNION xs) env ⇔
    ∀x. x ∈ xs ⇒ perms_ok_env ps x env
Proof
  rw [perms_ok_env_def, EQ_IMP_THM]
  \\ gs [PULL_EXISTS, SF SFY_ss]
QED

Theorem perms_ok_bind_exn_v[simp]:
  perms_ok ps bind_exn_v
Proof
  rw [perms_ok_def, bind_exn_v_def]
QED

Definition refc_ok_def:
  refc_ok ps (Refv v) = perms_ok ps v ∧
  refc_ok ps (Varray vs) = EVERY (perms_ok ps) vs ∧
  refc_ok ps (W8array ws) = T
End

Theorem pmatch_perms_ok:
  (∀envC s p v ws env.
    pmatch envC s p v ws = Match env ∧
    pats_ok perms p ∧
    perms_ok perms v ∧
    (RefPmatch ∈ perms ⇒ EVERY (refc_ok perms) s) ∧
    EVERY (perms_ok perms) (MAP SND ws) ⇒
      EVERY (perms_ok perms) (MAP SND env)) ∧
  (∀envC s ps vs ws env.
    pmatch_list envC s ps vs ws = Match env ∧
    EVERY (pats_ok perms) ps ∧
    EVERY (perms_ok perms) vs ∧
    (RefPmatch ∈ perms ⇒ EVERY (refc_ok perms) s) ∧
    EVERY (perms_ok perms) (MAP SND ws) ⇒
      EVERY (perms_ok perms) (MAP SND env))
Proof
  ho_match_mp_tac pmatch_ind \\ rw [] \\ gvs [pmatch_def]
  >- ((* Plit *)
    gs [CaseEq "bool"])
  >- ((* Pcon SOME *)
    gvs [CaseEqs ["bool", "option", "prod"]]
    \\ gs [EVERY_MEM, perms_ok_def])
  >- ((* Pcon NONE *)
    gvs [CaseEqs ["bool", "option", "prod"]]
    \\ gs [perms_ok_def, EVERY_MEM])
  >- ((* Pref *)
    gvs [perms_ok_def, EVERY_MEM, CaseEqs ["option", "store_v"]]
    \\ gs [store_lookup_def, MEM_EL, PULL_EXISTS, EL_MAP]
    \\ first_x_assum drule \\ gs [refc_ok_def])
  \\ gvs [CaseEqs ["bool", "option", "prod", "match_result"]]
QED

Theorem perms_ok_env_extend_dec_env:
  perms_ok_env ps fvs env1 ∧
  perms_ok_env ps fvs env ⇒
    perms_ok_env ps fvs (extend_dec_env env1 env)
Proof
  rw [perms_ok_env_def, extend_dec_env_def]
  \\ gs [nsLookup_nsAppend_some, SF SFY_ss]
QED

Theorem EVERY_perms_ok_env_BIGUNION:
  ∀xs.
    EVERY (λx. perms_ok_env ps (P x) env) xs =
    perms_ok_env ps (BIGUNION (set (MAP P xs))) env
Proof
  Induct >- simp [perms_ok_env_def]
  \\ rw [perms_ok_env_UNION]
QED

Theorem perms_ok_env_EMPTY:
  perms_ok_env ps EMPTY env
Proof
  rw [perms_ok_env_def]
QED

Definition dfreevars_def:
  dfreevars (Dlet locs p x) =
    (freevars x DIFF set (MAP Short (pat_bindings p []))) ∧
  dfreevars (Dletrec locs f) =
    BIGUNION (set (MAP (λ(fn,vn,x). freevars x DIFF {Short fn; Short vn}) f)) ∧
  dfreevars (Dmod mn ds) =
    BIGUNION (set (MAP dfreevars ds)) ∧
  dfreevars (Dlocal ds1 ds2) =
    BIGUNION (set (MAP dfreevars ds1)) ∪
    BIGUNION (set (MAP dfreevars ds2)) ∧
  dfreevars _ = EMPTY
Termination
  WF_REL_TAC ‘measure dec_size’
End

Theorem evaluate_perms_ok:
  (∀s:'ffi semanticPrimitives$state. ∀env xs s' res.
     EVERY (perms_ok_exp ps) xs ∧
     EVERY (λx. perms_ok_env ps (freevars x) env) xs ∧
     (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s.refs) ∧
     evaluate s env xs = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       (DoEval ∉ ps ⇒ s'.next_type_stamp = s.next_type_stamp) ∧
       (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s'.refs) ∧
       (∀ffi out y.
          MEM (IO_event ffi out y) s'.ffi.io_events ⇒
          MEM (IO_event ffi out y) s.ffi.io_events ∨ FFIWrite ffi ∈ ps) ∧
       case res of
         Rerr (Rraise v) => perms_ok ps v
       | Rval vs => EVERY (perms_ok ps) vs
       | _ => T) ∧
  (∀s:'ffi semanticPrimitives$state. ∀env v pes errv s' res.
     EVERY (perms_ok_exp ps) (MAP SND pes) ∧
     EVERY (λ(p,x). perms_ok_env ps (freevars x DIFF
                                     set (MAP Short (pat_bindings p []))) env)
           pes ∧
     EVERY (pats_ok ps) (MAP FST pes) ∧
     (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s.refs) ∧
     perms_ok ps v ∧
     perms_ok ps errv ∧
     evaluate_match s env v pes errv = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       (DoEval ∉ ps ⇒ s'.next_type_stamp = s.next_type_stamp) ∧
       (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s'.refs) ∧
       (∀ffi out y.
          MEM (IO_event ffi out y) s'.ffi.io_events ⇒
          MEM (IO_event ffi out y) s.ffi.io_events ∨ FFIWrite ffi ∈ ps) ∧
       case res of
         Rerr (Rraise v) => perms_ok ps v
       | Rval vs => EVERY (perms_ok ps) vs
       | _ => T) ∧
  (∀s:'ffi semanticPrimitives$state. ∀env ds s' res.
     EVERY (perms_ok_dec ps) ds ∧
     (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s.refs) ∧
     perms_ok_env ps UNIV env ∧
     evaluate_decs s env ds = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       (RefPmatch ∈ ps ⇒ EVERY (refc_ok ps) s'.refs) ∧
       (∀ffi out y.
          MEM (IO_event ffi out y) s'.ffi.io_events ⇒
          MEM (IO_event ffi out y) s.ffi.io_events ∨ FFIWrite ffi ∈ ps) ∧
       case res of
         Rerr (Rraise v) => perms_ok ps v
       | Rval env1 => perms_ok_env ps UNIV env1
       | _ => T)
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  >~ [‘[]’] >- (
    rw [evaluate_def]
    \\ gs [])
  \\ rpt gen_tac \\ TRY disch_tac
  >~ [‘_::_::_’] >-(
    gvs [evaluate_def, CaseEqs ["prod", "result", "error_result"]]
    \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
    \\ rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >~ [‘Lit l’] >- (
    gvs [evaluate_def, perms_ok_def])
  >~ [‘Raise e’] >- (
    gvs [evaluate_def, CaseEqs ["prod", "result", "error_result"]]
    \\ drule_then strip_assume_tac evaluate_sing \\ gvs [])
  >~ [‘Handle e pes’] >- (
    gvs [evaluate_def, CaseEqs ["prod", "result", "error_result", "bool"],
         perms_ok_env_UNION, EVERY_MAP, LAMBDA_PROD, perms_ok_env_BIGUNION]
    \\ last_x_assum mp_tac
    \\ impl_tac
    >- (
      gs [EVERY_MEM, ELIM_UNCURRY] \\ rw []
      \\ first_x_assum irule \\ gs [MEM_MAP]
      \\ first_assum (irule_at Any) \\ gs [])
    \\ rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >~ [‘Con cn es’] >- (
    gvs [evaluate_def, perms_ok_env_BIGUNION, EVERY_MEM, MEM_MAP, PULL_EXISTS,
         CaseEqs ["prod", "result", "error_result", "bool", "option"],
         build_conv_def, perms_ok_def])
  >~ [‘Var n’] >- (
    gvs [evaluate_def, perms_ok_def, CaseEqs ["option", "result"],
         perms_ok_env_def])
  >~ [‘Fun n e’] >- (
    gvs [evaluate_def, perms_ok_env_def, perms_ok_def, SF SFY_ss])
  >~ [‘App op xs’] >- (
    gvs [evaluate_def]
    \\ Cases_on ‘op = Opapp’ \\ gs []
    >- ((* Opapp *)
      gvs [CaseEqs ["result", "prod", "bool", "option"],
           perms_ok_env_BIGUNION, EVERY_MEM, MEM_MAP, PULL_EXISTS, SF SFY_ss,
           evaluateTheory.dec_clock_def]
      \\ gvs [do_opapp_cases]
      \\ rename1 ‘REVERSE vs = [_; _]’ \\ Cases_on ‘vs’ \\ gvs []
      >- ((* Closure *)
        last_x_assum mp_tac
        \\ reverse impl_tac
        >- (
          rw [] \\ gs []
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
        \\ gs [SF DNF_ss, perms_ok_env_def, perms_ok_def, find_recfun_ALOOKUP,
               EVERY_MEM, MEM_MAP, PULL_EXISTS]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ last_x_assum irule
        \\ first_assum (irule_at Any) \\ gs [])
      >- ((* Recclosure *)
        last_x_assum mp_tac
        \\ reverse impl_tac
        >- (
          rw [] \\ gs []
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
        \\ gs [SF DNF_ss, perms_ok_env_def, perms_ok_def, find_recfun_ALOOKUP,
               EVERY_MEM, MEM_MAP, PULL_EXISTS]
        \\ drule_then assume_tac ALOOKUP_MEM
        \\ qmatch_asmsub_abbrev_tac ‘MEM yyy funs’
        \\ first_assum drule \\ simp_tac std_ss [Abbr ‘yyy’]
        \\ strip_tac
        \\ simp [build_rec_env_merge]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
                        nsLookup_alist_to_ns_none]
        >~ [‘ALOOKUP _ _ = NONE’] >- (
          last_x_assum irule
          \\ first_assum (irule_at Any)
          \\ gs [ALOOKUP_NONE, MAP_MAP_o, o_DEF, LAMBDA_PROD, MEM_MAP,
                 EXISTS_PROD]
          \\ first_assum (irule_at Any)
          \\ first_assum (irule_at Any) \\ gs []
          \\ strip_tac \\ gvs [])
        >~ [‘ALOOKUP _ _ = SOME _’] >- (
          drule_then assume_tac ALOOKUP_MEM
          \\ gs [MEM_MAP, EXISTS_PROD, perms_ok_def, EVERY_MAP, EVERY_MEM]
          \\ gs [perms_ok_env_def, MEM_MAP, EXISTS_PROD]
          \\ rw [] \\ gs [FORALL_PROD, SF SFY_ss])
        \\ last_x_assum irule
        \\ first_assum (irule_at Any)
        \\ gs [ALOOKUP_NONE, MAP_MAP_o, o_DEF, LAMBDA_PROD, MEM_MAP,
               EXISTS_PROD]
        \\ first_assum (irule_at Any)
        \\ first_assum (irule_at Any) \\ gs []))
    \\ Cases_on ‘op = Eval’ \\ gs []
    >- ((* Eval *)
      gvs [CaseEqs ["result", "prod", "bool", "option"],
           perms_ok_env_BIGUNION, EVERY_MEM, MEM_MAP, PULL_EXISTS, SF SFY_ss,
           evaluateTheory.dec_clock_def]
      \\ cheat (* theorems about decs out of do_eval *))
    \\ cheat (* do_app theorem *))
  >~ [‘Log lop x y’] >- (
    gvs [evaluate_def, perms_ok_env_UNION, do_log_def,
         CaseEqs ["option", "exp_or_val", "result", "prod", "bool"]]
    \\ drule_then strip_assume_tac evaluate_sing \\ gs []
    \\ rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >~ [‘If x y z’] >- (
    gvs [evaluate_def, CaseEqs ["result", "prod", "option", "bool"],
         perms_ok_env_UNION, do_if_def]
    \\ rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >~ [‘Mat e pes’] >- (
    gvs [evaluate_def, CaseEqs ["prod", "result", "error_result", "bool"],
         perms_ok_env_UNION, EVERY_MAP, LAMBDA_PROD, perms_ok_env_BIGUNION]
    \\ last_x_assum mp_tac
    \\ reverse impl_tac
    >- (
      rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
    \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
    \\ gs [EVERY_MEM, ELIM_UNCURRY] \\ rw []
    \\ first_x_assum irule \\ gs [MEM_MAP]
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘Let opt x y’] >- (
    gvs [evaluate_def, CaseEqs ["result", "prod"], perms_ok_env_UNION]
    \\ drule_then strip_assume_tac evaluate_sing \\ gs []
    \\ Cases_on ‘opt’ \\ gs [namespaceTheory.nsOptBind_def]
    >- (
      rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
    \\ last_x_assum mp_tac
    \\ reverse impl_tac
    >- (
      rw [] \\ first_x_assum (drule_then assume_tac) \\ gs [])
    \\ gs [perms_ok_env_def]
    \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute] \\ rw [] \\ gs []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘Letrec f x’] >- (
    gvs [evaluate_def, CaseEqs ["result", "prod", "bool"], perms_ok_env_UNION]
    \\ first_x_assum irule
    \\ gs [perms_ok_env_def, build_rec_env_merge]
    \\ rw [] \\ gs [namespacePropsTheory.nsLookup_nsAppend_some]
    >~ [‘nsLookup _ n = SOME v’] >- (
      gvs [namespacePropsTheory.nsLookup_alist_to_ns_some]
      \\ drule_then assume_tac ALOOKUP_MEM
      \\ gvs [MEM_MAP, PULL_EXISTS, EXISTS_PROD, perms_ok_def,
              SF SFY_ss, perms_ok_env_def, EVERY_MEM])
    \\ gs [namespacePropsTheory.nsLookup_alist_to_ns_none]
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ gs [MEM_MAP, ALOOKUP_NONE, ELIM_UNCURRY])
  >~ [‘Tannot x t’] >- (
    gvs [evaluate_def, CaseEqs ["result", "prod"]])
  >~ [‘Lannot x l’] >- (
    gvs [evaluate_def, CaseEqs ["result", "prod"]])
  >~ [‘[]’] >- (
    gvs [evaluate_def])
  >~ [‘_::_’] >- (
    gvs [evaluate_def, CaseEqs ["bool", "match_result", "result"]]
    \\ last_x_assum mp_tac \\ impl_tac \\ gs []
    \\ drule (CONJUNCT1 pmatch_perms_ok) \\ simp []
    \\ disch_then drule \\ strip_tac
    \\ gs [perms_ok_env_def]
    \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
    \\ rw [] \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
                    nsLookup_alist_to_ns_none]
    >~ [‘ALOOKUP _ _ = SOME _’] >- (
      drule_then assume_tac ALOOKUP_MEM
      \\ gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS, SF SFY_ss])
    \\ gs [ALOOKUP_NONE]
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ drule_then assume_tac (CONJUNCT1 pmatch_extend) \\ gs []
    \\ pop_assum (SUBST_ALL_TAC o SYM)
    \\ gs [MEM_MAP])
  >~ [‘[]’] >- (
    gvs [evaluate_decs_def]
    \\ simp [perms_ok_env_def])
  >~ [‘_::_::_’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "error_result"]]
    \\ gs [combine_dec_result_def]
    \\ last_x_assum mp_tac
    \\ impl_tac \\ gs []
    >- (
      irule perms_ok_env_extend_dec_env
      \\ gs [])
    \\ CASE_TAC \\ gs []
    \\ rw [] \\ gs []
    >~ [‘perms_ok_env ps _ <| v := nsAppend _ _; c := nsAppend _ _ |>’] >- (
      gs [perms_ok_env_def, nsLookup_nsAppend_some]
      \\ rw [] \\ gs [SF SFY_ss])
    \\ first_x_assum (drule_then strip_assume_tac) \\ gs [])
  >~ [‘Dlet locs p e’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "bool"]]
    \\ last_x_assum mp_tac
    \\ impl_tac \\ gs []
    >~ [‘pmatch’] >- (
      drule_then strip_assume_tac evaluate_sing \\ gvs []
      \\ rw [] \\ CASE_TAC \\ gs []
      \\ drule (CONJUNCT1 pmatch_perms_ok) \\ simp []
      \\ disch_then drule \\ rw []
      \\ gs [perms_ok_env_def, nsLookup_alist_to_ns_some, PULL_EXISTS] \\ rw []
      \\ drule_then assume_tac ALOOKUP_MEM
      \\ gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS, SF SFY_ss])
    \\ gs [perms_ok_env_def, SF SFY_ss])
  >~ [‘Dletrec locs funs’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "bool"]]
    \\ gs [build_rec_env_merge, perms_ok_env_def, nsLookup_alist_to_ns_some,
           PULL_EXISTS]
    \\ rw []
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ simp [perms_ok_def, EVERY_MEM, MEM_MAP, EXISTS_PROD,
             perms_ok_env_BIGUNION, PULL_EXISTS]
    \\ rw [perms_ok_env_def] \\ gs [SF SFY_ss])
  >~ [‘Dtype locs tds’] >- (
    gvs [evaluate_decs_def, CaseEq "bool"]
    \\ simp [perms_ok_env_def])
  >~ [‘Dtabbrev locs tvs tn t’] >- (
    gvs [evaluate_decs_def]
    \\ simp [perms_ok_env_def])
  >~ [‘Denv n’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "eval_state", "option"],
         perms_ok_env_def, declare_env_def, perms_ok_def, nat_to_v_def,
         SF SFY_ss])
  >~ [‘Dexn locs cn ts’] >- (
    gvs [evaluate_decs_def]
    \\ simp [perms_ok_env_def])
  >~ [‘Dmod mn ds’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], perms_ok_env_def,
         nsLookup_nsLift]
    \\ Cases \\ gs [SF SFY_ss])
  >~ [‘Dlocal ds1 ds2’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"]]
    \\ last_x_assum mp_tac
    \\ impl_tac \\ gs []
    >- (
      gs [perms_ok_env_def, extend_dec_env_def, nsLookup_nsAppend_some]
      \\ rw [] \\ gs [SF SFY_ss])
    \\ rw []
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
QED

Theorem evaluate_perms_ok_exp =
  CONJUNCT1 evaluate_perms_ok
  |> Q.SPECL [‘s’, ‘env’, ‘[exp]’]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [];

Theorem evaluate_perms_ok_pat =
  CONJUNCT1 (CONJUNCT2 evaluate_perms_ok)
  |> Q.SPECL [‘s’, ‘env’, ‘v’, ‘[p,e]’]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [];

(* -------------------------------------------------------------------------
 *
 * ------------------------------------------------------------------------- *)

Inductive v_ok:
[~Inferred:]
  (∀ctxt v.
     inferred ctxt v ⇒
       kernel_vals ctxt v) ∧
[~PartialApp:]
  (∀ctxt f v g.
     kernel_vals ctxt f ∧
     v_ok ctxt v ∧
     do_partial_app f v = SOME g ⇒
       kernel_vals ctxt g) ∧
[~KernelVals:]
  (∀ctxt v.
     kernel_vals ctxt v ⇒
       v_ok ctxt v) ∧
[~Conv:]
  (∀ctxt opt vs.
     EVERY (v_ok ctxt) vs ∧
     (∀tag x. opt = SOME (TypeStamp tag x) ⇒ x ∉ kernel_types) ⇒
       v_ok ctxt (Conv opt vs)) ∧
[~Closure:]
  (∀ctxt env n x ps.
     env_ok ctxt env ∧
     DoEval ∉ ps ∧
     RefAlloc ∉ ps ∧
     perms_ok_exp ps x ⇒
       v_ok ctxt (Closure env n x)) ∧
[~Recclosure:]
  (∀ctxt env f n ps.
     env_ok ctxt env ∧
     DoEval ∉ ps ∧
     RefAlloc ∉ ps ∧
     EVERY (perms_ok_exp ps) (MAP (SND o SND) f) ⇒
       v_ok ctxt (Recclosure env f n)) ∧
[~Vectorv:]
  (∀ctxt vs.
     EVERY (v_ok ctxt) vs ⇒
       v_ok ctxt (Vectorv vs)) ∧
[~Lit:]
  (∀ctxt lit.
     v_ok ctxt (Litv lit)) ∧
[~Loc:]
  (∀ctxt loc.
     loc ∉ kernel_locs ⇒
       v_ok ctxt (Loc loc)) ∧
[~Env:]
  (∀ctxt env ns.
     env_ok ctxt env ⇒
       v_ok ctxt (Env env ns)) ∧
[env_ok:]
  (∀ctxt env.
     (∀n len tag m. nsLookup env.c n = SOME (len, TypeStamp tag m) ⇒
                  m ∉ kernel_types) ∧
     (∀n v. nsLookup env.v n = SOME v ⇒ v_ok ctxt v) ⇒
       env_ok ctxt env)
End

Definition ref_ok_def:
  ref_ok ctxt (Varray vs) = EVERY (v_ok ctxt) vs ∧
  ref_ok ctxt (Refv v) = v_ok ctxt v ∧
  ref_ok ctxt (W8array vs) = T
End

Definition state_ok_def:
  state_ok ctxt s ⇔
    (∀loc. loc ∈ kernel_locs ⇒ loc < LENGTH s.refs) ∧
    (∀n. n ∈ kernel_types ⇒ n < s.next_type_stamp) ∧
    EVERY (ref_ok ctxt) s.refs ∧
    EVERY (ok_event ctxt) s.ffi.io_events
End

(* -------------------------------------------------------------------------
 * Proving env_ok/v_ok/ref_ok/state_ok for things
 * ------------------------------------------------------------------------- *)

Theorem env_ok_write_cons:
  t ∉ kernel_types ∧
  env_ok ctxt env ⇒
    env_ok ctxt (write_cons nm (n, TypeStamp s t) env)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, ml_progTheory.nsLookup_write_cons, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write_cons]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_write:
  env_ok ctxt env ∧
  v_ok ctxt v ⇒
    env_ok ctxt (write nm v env)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, ml_progTheory.nsLookup_write, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_merge_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (merge_env env1 env2)
Proof
  simp [GSYM AND_IMP_INTRO]
  \\ simp [Once v_ok_cases] \\ strip_tac
  \\ simp [Once v_ok_cases] \\ strip_tac
  \\ simp [Once v_ok_cases, ml_progTheory.merge_env_def]
  \\ conj_tac
  \\ Cases \\ gs [nsLookup_nsAppend_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_with:
  env_ok ctxt (env1 with c := env.c) ⇒
    env_ok ctxt (env with v := env1.v)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, SF SFY_ss]
QED

Theorem env_ok_with_nsBind:
  v_ok ctxt v ∧
  env_ok ctxt (env2 with c := env.c) ⇒
    env_ok ctxt (env with v := nsBind n v env2.v )
Proof
  simp [GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases]
  \\ conj_tac
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_empty_env:
  env_ok ctxt empty_env
Proof
  rw [Once v_ok_cases, ml_progTheory.empty_env_def]
QED

(*
 * env_ok holds for the prim environment.
 *)

Theorem env_ok_init_env:
  env_ok ctxt init_env
Proof
  rw [Once v_ok_cases, ml_progTheory.init_env_def]
  \\ gvs [nsLookup_Bind_v_some, CaseEqs ["bool", "option"], kernel_types_def]
QED

(*
 * env_ok holds for the kernel_env
 *)

Theorem env_ok_kernel_env:
  env_ok ctxt kernel_env
Proof
  rw [kernel_env_def, env_ok_write_cons, kernel_types_def, env_ok_empty_env]
QED

Theorem v_ok_member_v:
  v_ok ctxt member_v
Proof
  rw [member_v_def]
  \\ irule v_ok_Recclosure
  \\ simp [env_ok_merge_env, env_ok_kernel_env, perms_ok_exp_def,
           env_ok_init_env, pats_ok_def]
  \\ qexists_tac ‘EMPTY’ \\ gs []
QED

(* TODO: Use v_thms *)

Theorem inferred_ok:
  inferred ctxt f ∧
  state_ok ctxt s ∧
  v_ok ctxt v ∧
  do_opapp [f; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ∃ctxt'.
      state_ok ctxt' s' ∧
      (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
      (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
      (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
      (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once inferred_cases]
  >~ [‘f ∈ kernel_funs’] >- (
    gs [kernel_funs_def]
    >~ [‘conj_v’] >- (
      gvs [conj_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘conj_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, conj_v_def])
    >~ [‘imp_v’] >- (
      gvs [imp_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘imp_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, imp_v_def])
    >~ [‘disj1_v’] >- (
      gvs [disj1_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘disj1_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, disj1_v_def])
    >~ [‘not_not_v’] >- (
      cheat))
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_opapp_cases])
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def, do_opapp_cases])
QED

Theorem v_ok_THM_TYPE_HEAD:
  v_ok ctxt v ∧
  THM_TYPE_HEAD v ⇒
    ∃th. THM_TYPE th v
Proof
  rw [Once v_ok_cases, kernel_types_def, THM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, kernel_funs_def, conj_v_def, disj1_v_def,
         imp_v_def, not_not_v_def, SF SFY_ss]
  \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def]
QED

Theorem v_ok_TERM_TYPE_HEAD:
  v_ok ctxt v ∧
  TERM_TYPE_HEAD v ⇒
    ∃tm. TERM_TYPE tm v
Proof
  rw [Once v_ok_cases, kernel_types_def, TERM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, kernel_funs_def, conj_v_def, disj1_v_def,
         imp_v_def, not_not_v_def, SF SFY_ss]
  \\ Cases_on ‘th’ \\ gs [THM_TYPE_def]
QED

(*
 * TODO Move elsewhere
 *)

Theorem Arrow2:
  (A --> B --> C) f fv ∧
  do_partial_app fv av = SOME gv ∧
  do_opapp [gv; bv] = SOME (env, exp) ∧
  evaluate (s:'ffi semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧ B b bv ∧
  DoEval ∉ ps ∧
  RefAlloc ∉ ps ∧
  RefPmatch ∉ ps ∧
  perms_ok ps av ∧
  perms_ok ps bv ∧
  perms_ok ps fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.refs = s'.refs ∧
     s.next_type_stamp = s'.next_type_stamp ∧
     ∃rv. res = Rval [rv] ∧
          C (f a b) rv)
Proof
  strip_tac
  \\ ‘LENGTH s'.refs = LENGTH s.refs’
    by (gvs [do_partial_app_def, AllCaseEqs (), do_opapp_cases]
        \\ gs [perms_ok_def]
        \\ ‘perms_ok_exp ps e’
          by gs [perms_ok_exp_def]
        \\ drule_at_then (Pos (el 4))
                         (qspec_then ‘ps’ mp_tac)
                         evaluate_perms_ok_exp
        \\ impl_tac \\ simp []
        \\ gs [perms_ok_env_def]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ first_x_assum irule
        \\ first_assum (irule_at (Pos last)) \\ gs [])
  \\ qabbrev_tac ‘env' = write "a" av (write "b" bv (write "f" fv ARB))’
  \\ ‘Eval env' (Var (Short "a")) (A a)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "b")) (B b)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "f")) ((A --> B --> C) f)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ qpat_x_assum ‘(_ --> _) _ _’ kall_tac
  \\ qpat_x_assum ‘A _ _’ kall_tac
  \\ qpat_x_assum ‘B _ _’ kall_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow \\ strip_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow
  \\ simp [ml_translatorTheory.Eval_def]
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ dxrule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def, evaluate_def, Abbr ‘env'’,
           ml_progTheory.nsLookup_write]
  \\ qpat_x_assum ‘do_partial_app _ _ = _’ mp_tac
  \\ simp [do_partial_app_def, Once do_opapp_def, AllCaseEqs (), PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘do_opapp _ = SOME (env,exp)’ mp_tac
  \\ simp [do_opapp_cases]
  \\ strip_tac \\ gvs [evaluate_def, do_opapp_cases,
                       evaluateTheory.dec_clock_def]
  \\ dxrule_then (qspec_then ‘s.clock’ mp_tac) evaluate_set_init_clock
  \\ simp [with_same_clock]
  \\ strip_tac \\ gvs []
  \\ mp_tac (CONJUNCT1 is_clock_io_mono_evaluate)
  \\ qmatch_asmsub_abbrev_tac ‘evaluate s env1 [e]’
  \\ disch_then (qspecl_then [`s`,`env1`,`[e]`] mp_tac)
  \\ rw [is_clock_io_mono_def]
  \\ gs [io_events_mono_antisym]
QED

Theorem v_ok_TERM:
  v_ok ctxt v ∧
  TERM_TYPE tm v ⇒
    TERM ctxt tm
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule TERM_from_TERM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def, Once v_ok_cases, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_THM:
  v_ok ctxt v ∧
  THM_TYPE th v ⇒
    THM ctxt th
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule THM_from_THM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def, Once v_ok_cases, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  rw [Once v_ok_cases, bind_exn_v_def]
  \\rw [Once v_ok_cases, bind_stamp_def, kernel_types_def]
QED

Theorem kernel_vals_max_app:
  kernel_vals ctxt f ∧
  do_partial_app f v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ⇒
    f ∈ kernel_funs
Proof
  cheat
QED

Theorem TERM_TYPE_perms_ok:
  ∀tm v. TERM_TYPE tm v ⇒ perms_ok ps v
Proof
  Induct \\ rw [TERM_TYPE_def]
  \\ gs [ml_translatorTheory.NUM_def,
         ml_translatorTheory.INT_def,
         perms_ok_def]
QED

Theorem LIST_TYPE_perms_ok:
  ∀xs xsv.
    (∀x v. A x v ⇒ perms_ok ps v) ∧
    LIST_TYPE A xs xsv ⇒
      perms_ok ps xsv
Proof
  Induct \\ rw []
  \\ gs [ml_translatorTheory.LIST_TYPE_def, perms_ok_def, SF SFY_ss]
QED

Theorem THM_TYPE_perms_ok:
  ∀th v. THM_TYPE th v ⇒ perms_ok ps v
Proof
  Cases \\ rw [THM_TYPE_def]
  \\ gs [perms_ok_def, TERM_TYPE_perms_ok, SF SFY_ss,
         Q.ISPECL [‘(ps:permission set)’, ‘TERM_TYPE’]
                  (GEN_ALL LIST_TYPE_perms_ok)]
QED

Theorem perms_ok_member_v:
  perms_ok ps member_v
Proof
  rw [member_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def, pats_ok_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem perms_ok_list_union_v:
  perms_ok ps list_union_v
Proof
  rw [list_union_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def, pats_ok_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "member"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_member_v]
QED

Theorem conj_v_perms_ok:
  perms_ok ps conj_v
Proof
  rw [conj_v_def, perms_ok_def, perms_ok_exp_def, pats_ok_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "list_union"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_list_union_v]
QED

Theorem disj1_v_perms_ok:
  perms_ok ps disj1_v
Proof
  rw [disj1_v_def, perms_ok_def, perms_ok_exp_def, pats_ok_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs []
        \\ CCONTR_TAC \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem kernel_vals_ok:
  ∀ctxt f.
    kernel_vals ctxt f ⇒
      ∀s v env exp s' res.
        do_opapp [f; v] = SOME (env, exp) ∧
        state_ok ctxt s ∧
        v_ok ctxt v ∧
        evaluate s env [exp] = (s', res) ⇒
          (∃abort. s'.ffi = s.ffi ∧ res = Rerr (Rabort abort)) ∨
          ∃ctxt'.
            state_ok ctxt' s' ∧
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
            (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
            (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once v_ok_cases]
  >~ [‘inferred ctxt f’] >- (
    rw [DISJ_EQ_IMP]
    \\ irule_at Any inferred_ok
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘do_partial_app f v = SOME g’] >- (
    rw [DISJ_EQ_IMP]
    \\ Cases_on ‘f ∈ kernel_funs’ \\ gs [kernel_funs_def]
    >~ [‘conj_v’] >- (
      drule_all_then strip_assume_tac conj_v_alt \\ gvs []
      \\ TRY (first_assum (irule_at Any) \\ gs [] \\ NO_TAC)
      \\ rename1 ‘do_opapp [g; w]’
      \\ ‘∃th1. THM_TYPE th1 v’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ ‘∃th2. THM_TYPE th2 w’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ assume_tac conj_v_thm
      \\ ‘∃ps. DoEval ∉ ps ∧
               RefAlloc ∉ ps ∧
               RefPmatch ∉ ps ∧
               perms_ok ps conj_v’
        by (irule_at Any conj_v_perms_ok
            \\ qexists_tac ‘EMPTY’ \\ gs [])
      \\ ‘perms_ok ps v ∧ perms_ok ps w’
        by gs [SF SFY_ss, THM_TYPE_perms_ok]
      \\ drule_all Arrow2
      \\ strip_tac \\ gvs []
      \\ irule_at (Pos last) v_ok_KernelVals
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_THM
      \\ first_assum (irule_at (Pos (el 2)))
      \\ irule_at Any conj_thm
      \\ imp_res_tac v_ok_THM
      \\ first_assum (irule_at Any) \\ gs []
      \\ gs [state_ok_def])
    >~ [‘disj1_v’] >- (
      drule_all_then strip_assume_tac disj1_v_alt \\ gvs []
      \\ TRY (first_assum (irule_at Any) \\ gs [] \\ NO_TAC)
      \\ rename1 ‘do_opapp [g; w]’
      \\ ‘∃th. THM_TYPE th v’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ ‘∃tm. TERM_TYPE tm w’
        by (irule_at Any v_ok_TERM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ assume_tac disj1_v_thm
      \\ ‘∃ps. DoEval ∉ ps ∧
               RefAlloc ∉ ps ∧
               RefPmatch ∉ ps ∧
               perms_ok ps disj1_v’
        by (irule_at Any disj1_v_perms_ok
            \\ qexists_tac ‘EMPTY’ \\ gs [])
      \\ ‘perms_ok ps v ∧ perms_ok ps w’
        by gs [SF SFY_ss, THM_TYPE_perms_ok, TERM_TYPE_perms_ok]
      \\ drule_all Arrow2
      \\ strip_tac \\ gvs []
      \\ irule_at (Pos last) v_ok_KernelVals
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_THM
      \\ first_assum (irule_at (Pos (el 2)))
      \\ cheat
      (* \\ irule_at Any disj_thm
      \\ imp_res_tac v_ok_THM
      \\ first_assum (irule_at Any) \\ gs []
      \\ gs [state_ok_def] *))
    >~ [‘imp_v’] >- (
      cheat)
    >~ [‘not_not_v’] >- (
      cheat)
    \\ gs [Once v_ok_cases, Once inferred_cases, kernel_funs_def]
    >- (
      Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_partial_app_def])
    >- (
      Cases_on ‘th’ \\ gs [THM_TYPE_def, do_partial_app_def])
    \\ ‘kernel_vals ctxt f’
      by (irule v_ok_PartialApp
          \\ first_assum (irule_at (Pos hd))
          \\ gs [])
    \\ drule_all kernel_vals_max_app
    \\ rw [kernel_funs_def])
QED

local
  val ind_thm =
    full_evaluate_ind
    |> Q.SPECL [
      ‘λs env xs. ∀res s' ctxt.
        evaluate s env xs = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        FFIWrite kernel_ffi ∉ perms ∧
        EVERY (perms_ok_exp perms) xs ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval vs =>
                state_ok ctxt' s' ∧
                EVERY (v_ok ctxt') vs
            | Rerr (Rraise v) =>
                state_ok ctxt' s' ∧
                v_ok ctxt' v
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’,
      ‘λs env v ps errv. ∀res s' ctxt.
        evaluate_match s env v ps errv = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        FFIWrite kernel_ffi ∉ perms ∧
        EVERY (perms_ok_exp perms) (MAP SND ps) ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval vs =>
                state_ok ctxt' s' ∧
                EVERY (v_ok ctxt') vs
            | Rerr (Rraise v) =>
                state_ok ctxt' s' ∧
                v_ok ctxt' v
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’,
      ‘λs env ds. ∀res s' ctxt.
        evaluate_decs s env ds = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        FFIWrite kernel_ffi ∉ perms ∧
        EVERY (perms_ok_dec perms) (MAP SND ps) ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval env =>
                state_ok ctxt' s'  ∧
                env_ok ctxt env
            | Rerr (Rraise v) =>
                state_ok ctxt' s'  ∧
                v_ok ctxt' v
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ ‘env_ok ctxt1 env’
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ rpt CASE_TAC \\ gs []
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any)
  \\ simp [v_ok_Lit]
QED

Theorem compile_Raise:
  ^(get_goal "Raise e")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem compile_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "bool"], EVERY_MAP]
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  >~ [‘¬can_pmatch_all _ _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ ‘env_ok ctxt1 env’
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "option"], EVERY_MAP]
  >~ [‘¬do_con_check _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gvs [build_conv_def, CaseEqs ["option", "prod"]]
  \\ irule v_ok_Conv \\ gs []
  \\ qpat_x_assum ‘env_ok _ _’ mp_tac
  \\ rw [Once v_ok_cases] \\ gs [SF SFY_ss]
QED

Theorem compile_Var:
  ^(get_goal "Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  >- (
    gs [state_ok_def]
    \\ metis_tac [])
  \\ first_assum (irule_at Any) \\ gs []
  \\ qpat_x_assum ‘env_ok _ _’ mp_tac
  \\ rw [Once v_ok_cases] \\ gs [SF SFY_ss]
QED

Theorem compile_Fun:
  ^(get_goal "Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule v_ok_Closure \\ gs []
  \\ first_assum (irule_at Any)
  \\ cheat (* DoEval and RefAlloc are not in permissions *)
QED

Theorem compile_App:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "bool"]]
  >~ [‘do_opapp _ = NONE’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘s.clock = 0’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ ‘env_ok ctxt1 env’
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ rename1 ‘state_ok ctxt1 s’
  \\ ‘state_ok ctxt1 (dec_clock s)’
    by gs [evaluateTheory.dec_clock_def, state_ok_def]
  \\ ‘∃f v. vs = [v; f]’
    by (gvs [do_opapp_cases]
        \\ Cases_on ‘vs’ \\ gs [])
  \\ gvs []
  \\ Cases_on ‘kernel_vals ctxt1 f’
  >- (
    drule (INST_TYPE [“:'a”|->“:'ffi”] kernel_vals_ok)
    \\ disch_then (drule_all_then (strip_assume_tac)) \\ gs []
    >- (
      gs [state_ok_def]
      \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [evaluateTheory.dec_clock_def]
    \\ qexists_tac ‘ctxt'’ \\ gs []
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs []
    \\ gs [state_ok_def])
  \\ rename1 ‘do_opapp _ = SOME (env1, e)’
  \\ ‘env_ok ctxt1 env1’
    by (gvs [do_opapp_cases]
        >~ [‘Closure env1 n e’] >- (
          irule env_ok_with_nsBind \\ gs []
          \\ ‘env1 with c := env1.c = env1’
            by rw [sem_env_component_equality]
          \\ gs []
          \\ qpat_x_assum ‘v_ok _ (Closure _ _ _)’ mp_tac
          \\ rewrite_tac [Once v_ok_cases] \\ simp []
          \\ rw [] \\ gs [])
        \\ qpat_x_assum ‘v_ok _ (Recclosure _ _ _)’ mp_tac
        \\ rewrite_tac [Once v_ok_cases] \\ simp []
        \\ rw [Once v_ok_cases]
        \\ simp [Once v_ok_cases, SF SFY_ss]
        \\ Cases \\ simp [build_rec_env_merge,
                          ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
               nsLookup_alist_to_ns_none]
        >~ [‘ALOOKUP _ _ = SOME _’] >- (
          drule_then assume_tac ALOOKUP_MEM
          \\ gvs [MEM_MAP, EXISTS_PROD]
          \\ rewrite_tac [Once v_ok_cases] \\ simp []
          \\ rw [DISJ_EQ_IMP]
          \\ gs [EVERY_MAP, EVERY_MEM, FORALL_PROD, SF SFY_ss]
          \\ simp [Once v_ok_cases, SF SFY_ss]
          \\ first_assum (irule_at Any) \\ gs []
          \\ rw []
          \\ first_x_assum irule
          \\ gs [SF SFY_ss])
        \\ first_x_assum irule
        \\ gs [SF SFY_ss])
  \\ cheat (* there's permissions in v_ok now *)
QED

Theorem evaluate_v_ok:
  ^(compile_correct_tm ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac
  \\ rewrite_tac [compile_Nil, compile_Cons, compile_Lit, compile_Raise,
                 compile_Handle, compile_Con, compile_Var, compile_Fun,
                 compile_App]
  \\ cheat
QED

val _ = export_theory ();

