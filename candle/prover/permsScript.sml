(*
  Permissions for CakeML values.
 *)

open preamble;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_progTheory;
open ast_extrasTheory;

val _ = new_theory "perms";

Type loc = “:num”;

(* -------------------------------------------------------------------------
 * We define a set of permissions for our value relation, which restricts
 * what our code can do.
 * ------------------------------------------------------------------------- *)

Datatype:
  permission = FFIWrite string (* Write to FFI channel with name     *)
             | RefMention loc  (* Mention reference using pointer    *)
             | RefUpdate       (* Write to references                *)
             | RefAlloc        (* Allocate new references            *)
             | DoEval          (* Call Eval                          *)
End

(*
Definition pats_ok_def:
  pats_ok ps = every_pat $ λp. case p of Pref p => RefPmatch ∈ ps | _ => T
End
 *)

(*
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
 *)

Definition perms_ok_exp_def:
  perms_ok_exp ps =
    every_exp $ λx.
      case x of
        App op xs =>
          (op = Eval ⇒ DoEval ∈ ps) ∧
          (op = Opref ⇒ RefAlloc ∈ ps) ∧
          (op = Opassign ⇒ RefUpdate ∈ ps) ∧
          (∀chn. op = FFI chn ⇒ FFIWrite chn ∈ ps)
   (* | Handle x pes => EVERY (pats_ok ps) (MAP FST pes)
      | Mat x pes => EVERY (pats_ok ps) (MAP FST pes) *)
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
        Dlet locs pat exp => (* pats_ok ps pat ∧ *) perms_ok_exp ps exp
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

Theorem perms_ok_div_exn_v[simp]:
  perms_ok ps div_exn_v
Proof
  rw [perms_ok_def, div_exn_v_def]
QED

Definition perms_ok_ref_def:
  perms_ok_ref ps (Refv v) = perms_ok ps v ∧
  perms_ok_ref ps (Varray vs) = EVERY (perms_ok ps) vs ∧
  perms_ok_ref ps (W8array ws) = T
End

Definition perms_ok_state_def:
  perms_ok_state ps s =
    ∀n. n < LENGTH s.refs ∧ RefMention n ∈ ps  ⇒ perms_ok_ref ps (EL n s.refs)
End

Theorem perms_ok_state_with_clock[simp]:
  perms_ok_state ps (s with clock := ck) = perms_ok_state ps s
Proof
  rw [perms_ok_state_def]
QED

Theorem pmatch_perms_ok:
  (∀envC s p v ws env.
    pmatch envC s p v ws = Match env ∧
    perms_ok perms v ∧
    (RefAlloc ∈ perms ⇒ IMAGE RefMention UNIV ⊆ perms) ∧
    (∀n. n < LENGTH s ∧ RefMention n ∈ perms ⇒ perms_ok_ref perms (EL n s)) ∧
    EVERY (perms_ok perms) (MAP SND ws) ⇒
      EVERY (perms_ok perms) (MAP SND env)) ∧
  (∀envC s ps vs ws env.
    pmatch_list envC s ps vs ws = Match env ∧
    EVERY (perms_ok perms) vs ∧
    (RefAlloc ∈ perms ⇒ IMAGE RefMention UNIV ⊆ perms) ∧
    (∀n. n < LENGTH s ∧ RefMention n ∈ perms ⇒ perms_ok_ref perms (EL n s)) ∧
    EVERY (perms_ok perms) (MAP SND ws) ⇒
      EVERY (perms_ok perms) (MAP SND env))
Proof
  ho_match_mp_tac pmatch_ind \\ rw [] \\ gvs [pmatch_def]
  >- ((* Plit *)
    gs [CaseEq "bool"])
  >- ((* Pcon SOME *)
    gvs [CaseEqs ["bool", "option", "prod"]]
    \\ gs [EVERY_MEM, perms_ok_def, SF DNF_ss])
  >- ((* Pcon NONE *)
    gvs [CaseEqs ["bool", "option", "prod"]]
    \\ gs [perms_ok_def, EVERY_MEM, SF DNF_ss])
  >- ((* Pref *)
    gvs [perms_ok_def, EVERY_MEM, CaseEqs ["option", "store_v"]]
    \\ gs [store_lookup_def, MEM_EL, PULL_EXISTS, EL_MAP, SF DNF_ss]
    \\ first_x_assum drule \\ gs [perms_ok_ref_def])
  \\ gvs [CaseEqs ["bool", "option", "prod", "match_result"], SF DNF_ss]
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

Theorem do_app_perms:
  do_app (refs, ffi) op vs = SOME ((refs1,ffi1),res) ∧
  EVERY (perms_ok ps) vs ∧
  (RefAlloc ∈ ps ⇒ IMAGE RefMention UNIV ⊆ ps) ∧
  (∀n. n < LENGTH refs ∧ RefMention n ∈ ps ⇒ perms_ok_ref ps (EL n refs)) ∧
  (op = Opref ⇒
    RefAlloc ∈ ps ∧
    RefMention (LENGTH refs) ∈ ps) ∧
  (op = Opassign ⇒ RefUpdate ∈ ps) ∧
  (∀chn. op = FFI chn ⇒ FFIWrite chn ∈ ps) ∧
  op ≠ Opapp ∧
  op ≠ Eval ⇒
    (∀n. n < LENGTH refs1 ∧ RefMention n ∈ ps ⇒ perms_ok_ref ps (EL n refs1)) ∧
    (RefAlloc ∉ ps ⇒ LENGTH refs1 = LENGTH refs) ∧
    (∀ch out y.
       MEM (IO_event ch out y) ffi1.io_events ⇒
       MEM (IO_event ch out y) ffi.io_events ∨ FFIWrite ch ∈ ps) ∧
    case list_result res of
      Rval vs => EVERY (perms_ok ps) vs
    | Rerr (Rraise v) => perms_ok ps v
    | Rerr (Rabort err) => T
Proof
  strip_tac
  \\ qpat_x_assum ‘do_app _ _ _ = _’ mp_tac
  \\ Cases_on ‘∃opn. op = Opn opn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [div_exn_v_def, perms_ok_def])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gs [perms_ok_def, store_lookup_def, EVERY_EL]
    \\ first_x_assum drule \\ gs [perms_ok_ref_def])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [perms_ok_def, store_assign_def]
    \\ rw [EL_LUPDATE, perms_ok_ref_def])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [perms_ok_def, store_alloc_def, perms_ok_ref_def]
    \\ simp [EL_APPEND_EQN]
    \\ rw [] \\ gs []
    \\ gvs [NOT_LESS, LESS_OR_EQ, perms_ok_ref_def])
  \\ cheat
QED

Theorem evaluate_perms_ok:
  (∀s:'ffi semanticPrimitives$state. ∀env xs s' res.
     EVERY (perms_ok_exp ps) xs ∧
     EVERY (λx. perms_ok_env ps (freevars x) env) xs ∧
     perms_ok_state ps s ∧
     (RefAlloc ∈ ps ⇒ IMAGE RefMention UNIV ⊆ ps) ∧
     evaluate s env xs = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       (DoEval ∉ ps ⇒ s'.next_type_stamp = s.next_type_stamp) ∧
       perms_ok_state ps s' ∧
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
     perms_ok_state ps s ∧
     perms_ok ps v ∧
     perms_ok ps errv ∧
     (RefAlloc ∈ ps ⇒ IMAGE RefMention UNIV ⊆ ps) ∧
     evaluate_match s env v pes errv = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       (DoEval ∉ ps ⇒ s'.next_type_stamp = s.next_type_stamp) ∧
       perms_ok_state ps s' ∧
       (∀ffi out y.
          MEM (IO_event ffi out y) s'.ffi.io_events ⇒
          MEM (IO_event ffi out y) s.ffi.io_events ∨ FFIWrite ffi ∈ ps) ∧
       case res of
         Rerr (Rraise v) => perms_ok ps v
       | Rval vs => EVERY (perms_ok ps) vs
       | _ => T) ∧
  (∀s:'ffi semanticPrimitives$state. ∀env ds s' res.
     EVERY (perms_ok_dec ps) ds ∧
     perms_ok_state ps s ∧
     perms_ok_env ps UNIV env ∧
     (RefAlloc ∈ ps ⇒ IMAGE RefMention UNIV ⊆ ps) ∧
     evaluate_decs s env ds = (s', res) ⇒
       (RefAlloc ∉ ps ⇒ LENGTH s'.refs = LENGTH s.refs) ∧
       perms_ok_state ps s' ∧
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
        \\ Cases \\ simp [nsLookup_nsBind_compute]
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
        \\ Cases \\ simp [nsLookup_nsBind_compute]
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
      \\ cheat)
    \\ ‘EVERY (λx. perms_ok_env ps (freevars x) env) xs’
      by gs [EVERY_perms_ok_env_BIGUNION, SF ETA_ss]
    \\ gvs [CaseEqs ["result", "prod", "bool", "option"]]
    \\ drule_then (qspec_then ‘ps’ mp_tac) do_app_perms
    \\ impl_tac
    >- (
      gs [perms_ok_state_def, SUBSET_DEF])
    \\ strip_tac \\ gs []
    \\ gs [perms_ok_state_def]
    \\ rw [] \\ gs []
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
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
    \\ Cases \\ simp [nsLookup_nsBind_compute] \\ rw [] \\ gs []
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
    \\ drule_then (qspec_then ‘ps’ mp_tac) (CONJUNCT1 pmatch_perms_ok)
    \\ gs [perms_ok_state_def, perms_ok_env_def]
    \\ strip_tac
    \\ Cases \\ simp [nsLookup_nsBind_compute]
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
      \\ drule_then (qspec_then ‘ps’ mp_tac) (CONJUNCT1 pmatch_perms_ok)
      \\ gs [perms_ok_state_def] \\ rw []
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
    gvs [evaluate_decs_def, CaseEq "bool", perms_ok_state_def,
         perms_ok_env_def])
  >~ [‘Dtabbrev locs tvs tn t’] >- (
    gvs [evaluate_decs_def]
    \\ simp [perms_ok_env_def])
  >~ [‘Denv n’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "eval_state", "option"],
         perms_ok_env_def, declare_env_def, perms_ok_def, nat_to_v_def,
         perms_ok_state_def, SF SFY_ss])
  >~ [‘Dexn locs cn ts’] >- (
    gvs [evaluate_decs_def, perms_ok_env_def, perms_ok_state_def])
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

Theorem evaluate_perms_ok_dec =
  CONJUNCT2 (CONJUNCT2 evaluate_perms_ok)
  |> Q.SPECL [‘s’, ‘env’, ‘[dec]’]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [];

val _ = export_theory ();

