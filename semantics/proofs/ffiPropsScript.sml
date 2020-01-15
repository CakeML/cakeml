(*
  Various basic properties of the semantic primitives.
*)

open preamble;
open semanticPrimitivesTheory;

val _ = new_theory "ffiProps";

Theorem get_cargs_sem_SOME_IMP_args_ok:
  get_cargs_sem s sign.args args = SOME cargs ==>
  args_ok sign.args cargs
Proof
  `!s cts args cargs.
  get_cargs_sem s cts args = SOME cargs ==>
  LIST_REL arg_ok cts cargs
  `
  by(ho_match_mp_tac get_cargs_sem_ind \\
     rw[get_cargs_sem_def,ffiTheory.args_ok_def] \\
     Cases_on `ty` \\ Cases_on `arg` \\
     fs[get_carg_sem_def,ffiTheory.arg_ok_def] \\
     rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\
     rename1 `Litv v` \\
     Cases_on `v` \\ fs[get_carg_sem_def]) \\
  strip_tac \\
  first_x_assum dxrule \\
  rw[ffiTheory.args_ok_def]
QED


Theorem mut_args_split:
   get_mut_args (ty::ty') (arg::args) =  MAP SND (FILTER (is_mutty o FST) [(ty, arg)]) ++
                           get_mut_args ty' args
Proof
  rw [ffiTheory.get_mut_args_def] >> fs [listTheory.ZIP_def]
QED

(* TODO: move? *)
Theorem LUPDATE_LUPDATE_same:
  !e n l e'. LUPDATE e n (LUPDATE e' n l) = LUPDATE e n l
Proof
  Induct_on `l` >> Cases_on `n` >> rw[LUPDATE_def]
QED

Theorem store_cargs_none_lupdate:
 !margs l s h n. store_cargs_sem margs l (LUPDATE (W8array h) n s) = NONE /\  n < LENGTH s ==>
  store_cargs_sem margs l s = NONE
Proof
  ho_match_mp_tac store_cargs_sem_ind >>
  rw[store_cargs_sem_def,option_case_eq] >>
  Cases_on `marg` >> fs[store_carg_sem_def,store_assign_def,EL_LUPDATE] >>
  rveq >> fs[] >>
  TRY(rename1 `store_v_same_type` >>
      PURE_FULL_CASE_TAC >> fs[] >> rveq >>
      fs[store_v_same_type_def] >>
      PURE_FULL_CASE_TAC >> fs[LUPDATE_LUPDATE_same] >>
      metis_tac[LUPDATE_commutes]) >>
  metis_tac[]
QED


Theorem store_cargs_SOME_same_loc:
  !s ty args cargs sign l. get_cargs_sem s sign.args args = SOME cargs ==>
  store_cargs_sem (get_mut_args sign.args args) l s <> NONE
Proof
  rw [] >>
  qmatch_asmsub_abbrev_tac `get_cargs_sem _ cts _ = SOME _` >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`l`, `cargs`, `args`, `cts`, `s`] >>
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_FORALL] >>
  ho_match_mp_tac get_cargs_sem_ind >> rw [get_cargs_sem_def]
  >- (induct_on `l` >> fs [store_cargs_sem_def, ffiTheory.get_mut_args_def, listTheory.ZIP_def])
  >- (Cases_on `get_mut_args (ty::cts) (arg::args)`
      >- (induct_on `l` >> fs [store_cargs_sem_def])
      >- (fs [mut_args_split] >>
          Cases_on `ty` >> fs [ffiTheory.is_mutty_def] >>
          rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
          Cases_on `l` >> fs [store_cargs_sem_def] >>
          rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
           >- (Cases_on `arg` >> fs [get_carg_sem_def, store_carg_sem_def] >>
               rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
               fs [store_assign_def, store_lookup_def, store_v_same_type_def]) >>
              Cases_on `arg` >> fs [get_carg_sem_def, store_carg_sem_def] >>
              rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
              fs [store_assign_def, store_lookup_def, store_v_same_type_def]>>
              metis_tac [store_cargs_none_lupdate]))
QED



(* TODO: duplicated from mllistScript. move? *)
Theorem index_find_thm:
   !x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)
Proof
  Induct_on`l` \\ rw[INDEX_FIND_def]
QED

Theorem FIND_thm:
   (FIND f [] = NONE) ∧
   (∀h t. FIND f (h::t) = if f h then SOME h else FIND f t)
Proof
  rw[FIND_def,INDEX_FIND_def,index_find_thm]
QED

Theorem do_ffi_NONE_ffi:
   do_ffi s t n args = NONE /\
   t.signatures = t'.signatures /\
   ffi_oracle_ok t /\
   ffi_oracle_ok t'
   ⇒
   do_ffi s t' n args = NONE
Proof
  rw[do_ffi_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
  \\ rfs[ffiTheory.debug_sig_def,FIND_thm]
  >> metis_tac[ffiTheory.ffi_oracle_ok_def, ffiTheory.valid_ffi_name_def,
               get_cargs_sem_SOME_IMP_args_ok, store_cargs_SOME_same_loc]
QED


Theorem do_ffi_SOME_ffi_same:
   do_ffi refs ffi n args = SOME ((refs',ffi),r)
   ∧ (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
    /\ ffi.signatures = ffi'.signatures
    /\ ffi_oracle_ok ffi
    /\ ffi_oracle_ok ffi'
      ⇒
   do_ffi refs ffi' n args = SOME ((refs',ffi'),r)
Proof
  rw [do_ffi_def, ffiTheory.ffi_oracle_ok_def, ffiTheory.valid_ffi_name_def, ffiTheory.call_FFI_def]
  \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
  \\ rfs[ffiTheory.ffi_state_component_equality]
QED

(* TODO: move? *)
val sign_extends_def = Define `
  sign_extends t s =
  (!n sign. FIND (λsg. sg.mlname = n) s.signatures = SOME sign
    ==> FIND (λsg. sg.mlname = n) t.signatures = SOME sign)
`

Theorem do_ffi_SOME_ffi_extends:
   do_ffi refs ffi n args = SOME ((refs',ffi),r)
   ∧ (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
   /\ sign_extends ffi' ffi
      ⇒
   do_ffi refs ffi' n args = SOME ((refs',ffi'),r)
Proof
  rw [do_ffi_def, ffiTheory.ffi_oracle_ok_def, ffiTheory.valid_ffi_name_def, ffiTheory.call_FFI_def,
      sign_extends_def]
  \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
  \\ rfs[ffiTheory.ffi_state_component_equality,ffiTheory.debug_sig_def,FIND_thm]
  \\ res_tac \\ fs[] \\ rveq \\ fs[]
  \\ rveq
  \\ fs[ffiTheory.get_mut_args_def,store_cargs_sem_def]
QED

(* from type sound *)

Theorem get_cargs_sem_LENGTH:
  !st ct args cargs. get_cargs_sem st ct args = SOME cargs ==> LENGTH ct = LENGTH args
Proof
  ho_match_mp_tac get_cargs_sem_ind >> rw[get_cargs_sem_def] >> fs[]
QED

Theorem get_cargs_sem_EVERY_get_carg_sem:
  !st ct args cargs. get_cargs_sem st ct args = SOME cargs ==> EVERY (λ(c,a). ?carg. get_carg_sem st c a = SOME carg) (ZIP(ct,args))
Proof
  ho_match_mp_tac get_cargs_sem_ind >> rw[get_cargs_sem_def] >> fs[]
QED

Theorem get_carg_byte_array_upd:
  !st ct args cargs loc w w'.
    get_cargs_sem st ct args = SOME cargs /\ EL loc st = W8array w ==>
     ?carg'. get_cargs_sem (LUPDATE (W8array w') loc st) ct args = SOME carg'
Proof
  ho_match_mp_tac get_cargs_sem_ind >>
  rw [get_cargs_sem_def] >>
  simp [GSYM PULL_EXISTS] >>
  Cases_on `ty` >> Cases_on `arg` >> fs [get_carg_sem_def] >>
  TRY (Cases_on `l` >> fs [get_carg_sem_def, CaseEq "option",
                   CaseEq "store_v",  store_lookup_def, EL_LUPDATE])
  >- (fs [get_carg_sem_def, CaseEq "option",
                   CaseEq "store_v",  store_lookup_def, EL_LUPDATE, bool_case_eq] >>
          metis_tac [])
QED

Theorem get_cargs_sem_some_drop:
  !st ct args cargs n. get_cargs_sem st ct args = SOME cargs ==>
   ?cargs'. get_cargs_sem st (DROP n ct) (DROP n args) = SOME cargs'
Proof
  ho_match_mp_tac get_cargs_sem_ind >> rw [get_cargs_sem_def] >> fs [DROP_def] >>
  Cases_on `n = 0 ` >> rw [get_cargs_sem_def]
QED


Theorem do_ffi_SOME_same_signs:
   do_ffi refs ffi n args = SOME ((refs',ffi'),r) ⇒ ffi.signatures = ffi'.signatures
Proof
  rw[do_ffi_def]
  >> fs[ffiTheory.call_FFI_def]
  >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
  >> simp []
QED

Theorem valid_ffi_name_ffi_update:
  valid_ffi_name n sign ffi = valid_ffi_name n sign (ffi with <|ffi_state := f; io_events := io|>)
Proof
  rw [ffiTheory.valid_ffi_name_def]
QED


Theorem do_ffi_SOME_oracle_ok:
   ffi_oracle_ok ffi /\ do_ffi refs ffi n args = SOME ((refs',ffi'),r)  ⇒
     ffi_oracle_ok ffi'
Proof
  rw[do_ffi_def]
  >> fs[ffiTheory.call_FFI_def]
  >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
  >> rw [ffiTheory.ffi_oracle_ok_def]
  >> fs [ffiTheory.ffi_oracle_ok_def , GSYM valid_ffi_name_ffi_update] >> res_tac >> fs []
QED


val call_FFI_rel_def = Define `
  call_FFI_rel s s' <=> ?n sign args als nargs retv.
    FIND (λsig. sig.mlname = sign.mlname) (debug_sig::s.signatures) = SOME sign
    /\
    args_ok sign.args args
    /\
    call_FFI s n sign args als = SOME (FFI_return s' nargs retv)`;


Theorem call_FFI_rel_consts:
   call_FFI_rel s s' ⇒ (s.oracle = s'.oracle)
Proof
  rw[call_FFI_rel_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ fs[CaseEq"bool",CaseEq"oracle_result"]
  \\ rw[]
  \\ metis_tac []
QED

Theorem FIND_IMP_pred:
  FIND P l = SOME e ==> P e
Proof
  Induct_on `l` >> rw[FIND_thm] >> rw[]
QED


Theorem call_ffi_sign_eq:
  call_FFI_rel s s' ==>
   s.signatures = s'.signatures
Proof
  rw [call_FFI_rel_def, ffiTheory.call_FFI_def]
  \\ (qpat_x_assum `(if _ then _ else _) = _` mp_tac \\ TOP_CASE_TAC >> rw[])
  \\ fs [CaseEq"oracle_result"]
  \\ rw []
QED


Theorem ffi_valid_ffi_name:
  call_FFI_rel s s' /\ valid_ffi_name n sign s ==>
  valid_ffi_name n sign s'
Proof
  rw [ffiTheory.valid_ffi_name_def]
  \\ metis_tac [call_ffi_sign_eq]
QED


Theorem ffi_valid_ffi_name_rev:
  call_FFI_rel s s' /\ valid_ffi_name n sign s' ==>
  valid_ffi_name n sign s
Proof
  rw [ffiTheory.valid_ffi_name_def]
  \\ metis_tac [call_ffi_sign_eq]
QED

val sign_eq_def = Define `
  sign_eq t s = (t.ffi.signatures = s.ffi.signatures)`

Theorem sign_eq_ffi_id:
  sign_eq t s /\ s'.ffi = s.ffi ==> sign_eq t s'
Proof
  rw [sign_eq_def]
QED

Theorem sign_eq_ffi_id':
  sign_eq t s /\ s'.ffi = s.ffi ==> sign_eq (t with <|clock := s'.clock; refs := s'.refs|>) s'
Proof
  rw [sign_eq_def]
QED

Theorem ffi_oracle_clock_refs_up:
  ffi_oracle_ok t.ffi ==> ffi_oracle_ok (t with <|clock := clk; refs := refs|>).ffi
Proof
  rw [ffiTheory.ffi_oracle_ok_def]
QED

Theorem st_clock_up:
  (t with <|clock := clk; refs := refs|>).clock = clk
Proof
  rw []
QED

Theorem st_refs_up:
  (t with <|clock := clk; refs := refs|>).refs = refs
Proof
  rw []
QED

val state_sign_extends_def = Define `
  state_sign_extends t s =
  sign_extends t.ffi s.ffi
`

Theorem state_sign_extends_ffi_id':
  state_sign_extends t s /\ s'.ffi = s.ffi ==>
    state_sign_extends (t with <|clock := s'.clock; refs := s'.refs|>) s'
Proof
  rw [state_sign_extends_def]
QED


val _ = export_theory ();
