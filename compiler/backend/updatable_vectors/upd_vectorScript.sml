(*
  An abstract formalisation of updatable vectors. The view of the data makes
  it seem immutable, while the actual implementation performs mutation.
*)
open preamble;

val _ = new_theory "upd_vector";

Datatype:
  content = Array ('a list)
          | Link num num ((num # 'a) option)
End

Type state = “:num |-> 'a content”

Inductive spec:
[~last:]
  (∀arr a t.
     FLOOKUP m a = SOME $ Link t t NONE ∧
     FLOOKUP m t = SOME $ Array arr ⇒
     spec (a,arr) m) ∧
[~step:]
  (∀arr t u i x a m.
     FLOOKUP m a = SOME $ Link u t $ SOME (i,EL i arr) ∧ t ≠ u ∧
     spec (u,LUPDATE x i arr) m ∧ i < LENGTH arr ⇒
     spec (a,arr) m)
End

val _ = set_fixity "∈" (Infixl 480);

Overload "∈" = “spec”;

Definition state_ok_def:
  state_ok (m:'a state) ⇔
    (* Each final link is unique *)
    (∀a1 a2 t.
       FLOOKUP m a1 = SOME $ Link t t NONE ∧
       FLOOKUP m a2 = SOME $ Link t t NONE ⇒
       a1 = a2) ∧
    (* The link to the eventual array is always shared down a path *)
    (∀a1 a2 a3 u1 u2 opt1 opt2.
       FLOOKUP m a1 = SOME $ Link a2 u1 opt1 ∧
       FLOOKUP m a2 = SOME $ Link a3 u2 opt2 ⇒
       u1 = u2) ∧
    (* Pointer props *)
    (∀a a1 t opt.
       FLOOKUP m a = SOME $ Link a1 t opt ⇒
       ∃x arr. FLOOKUP m a1 = SOME x ∧ FLOOKUP m t = SOME $ Array arr)
End

(* length *)

Inductive calc_length:
  FLOOKUP m a = SOME (Link t b opt) ∧
  FLOOKUP m b = SOME (Array xs) ⇒
  calc_length a m (LENGTH xs)
End

Triviality mutvet_length_lemma:
  ∀u arr m a t opt.
    (u,arr) ∈ m ∧ state_ok m ∧
    FLOOKUP m a = SOME (Link u t opt) ⇒
    ∃arr2. FLOOKUP m t = SOME (Array arr2) ∧ LENGTH arr2 = LENGTH arr
Proof
  Induct_on ‘spec’ \\ fs [] \\ rw [] \\ fs []
  \\ fs [state_ok_def]
  \\ res_tac
  \\ rpt $ last_x_assum drule_all \\ rw [] \\ gvs []
QED

Theorem mutvec_length:
  state_ok m ∧ spec (a,arr) m ⇒
  calc_length a m (LENGTH arr)
Proof
  simp [Once spec_cases] \\ rw []
  \\ fs [calc_length_cases]
  \\ drule_all mutvet_length_lemma
  \\ rw [] \\ fs []
QED

(* lookup *)

Inductive calc_lookup:
  (FLOOKUP m a = SOME (Link t t opt) ∧
   FLOOKUP m t = SOME (Array xs) ∧ i < LENGTH xs ⇒
   calc_lookup a i m (EL i xs)) ∧
  (FLOOKUP m a = SOME (Link t u (SOME (i,y))) ∧ t ≠ u ⇒
   calc_lookup a i m y) ∧
  (FLOOKUP m a = SOME (Link t u (SOME (j,y))) ∧ t ≠ u ∧ i ≠ j ∧
   calc_lookup t i m res ⇒
   calc_lookup a i m res)
End

Theorem mutvec_lookup:
  ∀a arr m i.
    spec (a,arr) m ∧ i < LENGTH arr ∧ state_ok m ⇒
    calc_lookup a i m (EL i arr)
Proof
  Induct_on ‘spec’ \\ rw [] \\ fs []
  \\ simp [Once calc_lookup_cases]
  \\ Cases_on ‘i = i'’ \\ gvs []
  \\ res_tac \\ gvs [EL_LUPDATE]
QED

(* update *)

Inductive calc_update:
[~last:]
  (FLOOKUP m a = SOME (Link t t opt) ∧
   FLOOKUP m t = SOME (Array xs) ∧ i < LENGTH xs ⇒
   calc_update a i x m new (m |+ (t,Array (LUPDATE x i xs))
                              |+ (a,Link new t (SOME (i,EL i xs)))
                              |+ (new,Link t t NONE))) ∧
[~step:]
  (FLOOKUP m a = SOME (Link t u opt) ∧ t ≠ u ⇒
   calc_update a i x m new (m |+ (new,Link a u (SOME (i,x)))))
End

Triviality LUPDATE_EL:
  ∀arr i. LUPDATE (EL i arr) i (LUPDATE x i arr) = arr
Proof
  Induct \\ fs [] \\ Cases_on ‘i’ \\ fs [LUPDATE_def]
QED

Theorem spec_extend:
  ∀y m new x. y ∈ m ∧ new ∉ FDOM m ⇒ y ∈ m |+ (new,x)
Proof
  Induct_on ‘spec’ \\ fs [] \\ rw []
  \\ simp [Once spec_cases,FLOOKUP_UPDATE]
  >- (disj1_tac \\ qexists_tac ‘t’ \\ fs []
      \\ rw [] \\ fs [FLOOKUP_DEF])
  >- (disj2_tac \\ rw [] \\ fs [FLOOKUP_DEF]
      \\ first_x_assum $ irule_at Any \\ fs [])
QED

Theorem mutvec_update:
  ∀a arr m i new x.
    spec (a,arr) m ∧ i < LENGTH arr ∧ state_ok m ∧ new ∉ FDOM m ⇒
    ∃m1. calc_update a i x m new m1 ∧
         spec (new,LUPDATE x i arr) m1 ∧
         state_ok m1 ∧
         ∀y. spec y m ⇒ spec y m1
Proof
  rw []
  \\ ‘∃u t opt. FLOOKUP m a = SOME (Link u t opt)’ by
       fs [Once spec_cases]
  \\ reverse $ Cases_on ‘u = t’
  >-
   (irule_at Any calc_update_step \\ fs []
    \\ irule_at Any spec_step
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE]
    \\ qexists_tac ‘EL i arr’ \\ fs [LUPDATE_EL]
    \\ irule_at Any spec_extend \\ fs []
    \\ ‘t ≠ a’ by
     (CCONTR_TAC \\ gvs [state_ok_def]
      \\ fs [] \\ res_tac \\ gvs []) \\ fs []
    \\ conj_tac >-
     (fs [state_ok_def,FLOOKUP_UPDATE]
      \\ fs [AllCaseEqs()]
      \\ reverse conj_tac
      >-
       (rw [] \\ gvs []
        \\ first_x_assum drule
        \\ strip_tac \\ gvs []
        \\ fs [FLOOKUP_DEF] \\ metis_tac [])
      \\ rw [] \\ gvs []
      >- (first_x_assum drule
          \\ strip_tac \\ gvs []
          \\ fs [FLOOKUP_DEF] \\ metis_tac [])
      \\  metis_tac [])
    \\ rw [] \\ irule_at Any spec_extend \\ fs [])
  \\ gvs []
  \\ irule_at Any calc_update_last \\ gvs []
  \\ last_x_assum mp_tac
  \\ simp [Once spec_cases]
  \\ strip_tac \\ gvs []
  \\ simp [Once spec_cases,FLOOKUP_UPDATE]
  \\ ‘new ≠ t ∧ a ≠ t’ by (CCONTR_TAC \\ fs [FLOOKUP_DEF] \\ gvs [])
  \\ fs []
  \\ conj_tac
  >-
   (fs [state_ok_def,FLOOKUP_UPDATE,AllCaseEqs()]
    \\ conj_tac >- metis_tac []
    \\ reverse conj_tac
    >-
     (rw [] \\ gvs []
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [FLOOKUP_DEF]
      \\ Cases_on ‘new = a1’ \\ gvs []
      \\ Cases_on ‘new = t'’ \\ gvs []
      \\ Cases_on ‘t ≠ a1’ \\ gvs []
      \\ Cases_on ‘a ≠ t'’ \\ gvs []
      \\ Cases_on ‘a = a1’ \\ gvs []
      \\ metis_tac [])
    \\ rw [] \\ gvs []
    >- (first_x_assum drule
        \\ strip_tac \\ gvs []
        \\ fs [FLOOKUP_DEF] \\ metis_tac [])
    \\ metis_tac [])
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘m’
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ Induct_on ‘spec’
  \\ rw []
  \\ gvs []
  \\ Cases_on ‘a = a'’ \\ gvs []
  >-
   (gvs []
    \\ irule_at Any spec_step
    \\ gvs [FLOOKUP_UPDATE]
    \\ ‘new ≠ a’ by (CCONTR_TAC \\ fs [FLOOKUP_DEF] \\ gvs [])
    \\ fs [] \\ qexists_tac ‘x’ \\ fs []
    \\ irule_at Any spec_last
    \\ gvs [FLOOKUP_UPDATE])
  >-
   (‘t ≠ t'’ by (fs [state_ok_def] \\ CCONTR_TAC \\ gvs [])
    \\ irule_at Any spec_last
    \\ gvs [FLOOKUP_UPDATE]
    \\ qexists_tac ‘t'’ \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ CCONTR_TAC \\ gvs [FLOOKUP_DEF])
  \\ irule_at Any spec_step
  \\ ‘new ≠ a' ∧ t ≠ a'’ by (CCONTR_TAC \\ fs [FLOOKUP_DEF] \\ gvs [])
  \\ gvs [FLOOKUP_UPDATE]
  \\ first_x_assum $ irule_at Any
QED

(* focus *)

Theorem LUPDATE_LUPDATE:
  ∀xs i x y. LUPDATE x i (LUPDATE y i xs) = LUPDATE x i xs
Proof
  Induct \\ fs [LUPDATE_def] \\ Cases_on ‘i’ \\ fs [LUPDATE_def]
QED

Theorem LUPDATE_eq:
  ∀xs i x y ys. LUPDATE x i xs = LUPDATE y i ys ∧ i < LENGTH xs ⇒ x = y
Proof
  Induct \\ fs []
  \\ Cases_on ‘i’ \\ Cases_on ‘ys’ \\ gvs [LUPDATE_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Theorem mutvec_focus_one:
  FLOOKUP m a = SOME $ Link b t (SOME (i,x)) ∧
  FLOOKUP m b = SOME $ Link t t NONE ∧
  FLOOKUP m t = SOME $ Array arr ∧
  i < LENGTH arr ∧
  state_ok m ⇒
  let m1 = m |+ (t,Array (LUPDATE x i arr))
             |+ (a,Link t t NONE)
             |+ (b,Link a t (SOME (i,EL i arr))) in
    state_ok m1 ∧
    ∀y. spec y m ⇒ spec y m1
Proof
  fs [] \\ strip_tac \\ conj_tac
  >-
   (‘ALL_DISTINCT [a;b;t]’ by (fs [ALL_DISTINCT] \\ CCONTR_TAC \\ gvs [])
    \\ fs [ALL_DISTINCT]
    \\ rewrite_tac [FLOOKUP_UPDATE,state_ok_def]
    \\ simp [AllCaseEqs()]
    \\ qpat_x_assum ‘state_ok m’ mp_tac
    \\ rewrite_tac [state_ok_def] \\ strip_tac
    \\ conj_tac >- metis_tac []
    \\ conj_tac >- metis_tac []
    \\ rw [] \\ simp_tac std_ss [GSYM PULL_EXISTS]
    \\ conj_tac >- metis_tac []
    \\ first_x_assum drule \\ strip_tac \\ gvs []
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ Cases_on ‘b = t'’ \\ fs []
    \\ Cases_on ‘a = t'’ \\ fs []
    \\ Cases_on ‘t = t'’ \\ fs [])
  \\ gvs []
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘m’
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ Induct_on ‘spec’ \\ rw []
  \\ gvs []
  >-
   (Cases_on ‘a = a'’ >- gvs []
    \\ Cases_on ‘t = a'’ >- gvs []
    \\ Cases_on ‘t = t'’ >-
     (gvs [] \\ ‘a' = b’ by (fs [state_ok_def] \\ metis_tac [])
      \\ irule_at Any spec_step \\ fs [FLOOKUP_UPDATE]
      \\ qexists_tac ‘x’ \\ fs []
      \\ ‘t ≠ a’ by (CCONTR_TAC \\ gvs []) \\ fs []
      \\ irule_at Any spec_last \\ fs [FLOOKUP_UPDATE])
    \\ irule_at Any spec_last \\ fs [FLOOKUP_UPDATE]
    \\ qexists_tac ‘t'’ \\ fs [AllCaseEqs()]
    \\ CCONTR_TAC \\ gvs [])
  \\ Cases_on ‘a' = a’ >-
   (gvs []
    \\ irule_at Any spec_last \\ fs [FLOOKUP_UPDATE]
    \\ Cases_on ‘b = a’ >- gvs [] \\ fs []
    \\ Cases_on ‘t = a’ >- gvs [] \\ fs []
    \\ qpat_x_assum ‘spec _ _’ mp_tac
    \\ simp [Once spec_cases]
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE]
    \\ simp [Once spec_cases]
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE]
    \\ strip_tac \\ gvs [LUPDATE_LUPDATE]
    \\ drule_all LUPDATE_eq
    \\ strip_tac \\ gvs [LUPDATE_EL |> REWRITE_RULE [LUPDATE_LUPDATE]])
  \\ irule_at Any spec_step \\ fs [FLOOKUP_UPDATE]
  \\ rpt $ last_assum $ irule_at $ Pos hd
  \\ rpt $ last_assum $ irule_at $ Any
  \\ IF_CASES_TAC >- gvs []
  \\ IF_CASES_TAC \\ gvs []
QED

Definition lookups_def:
  (lookups m a x [] t xs ⇔
     x = Link t t NONE ∧
     FLOOKUP m a = SOME x ∧
     FLOOKUP m t = SOME $ Array xs) ∧
  (lookups m a x ((b,y)::zs) t xs ⇔
     FLOOKUP m a = SOME x ∧
     ∃i d. x = Link b t (SOME (i,d)) ∧ i < LENGTH xs ∧ b ≠ t ∧
           lookups m b y zs t xs)
End

Definition lupdate_list_def:
  lupdate_list [] xs = xs ∧
  lupdate_list (Link _ _ NONE::ys) xs = lupdate_list ys xs ∧
  lupdate_list (Link _ _ (SOME (i,x))::ys) xs = LUPDATE x i (lupdate_list ys xs) ∧
  lupdate_list (y::ys) xs = lupdate_list ys xs
End

Theorem spec_imp_lookups:
  ∀a xs m.
    spec (a,xs) m ∧ state_ok m ⇒
    ∃x ys t zs. lookups m a x ys t zs ∧
                xs = lupdate_list (x::MAP SND ys) zs ∧
                LENGTH xs = LENGTH zs
Proof
  Induct_on ‘spec’ \\ rw []
  >- (qexists_tac ‘Link t t NONE’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘t’
      \\ qexists_tac ‘arr’
      \\ fs [lookups_def,lupdate_list_def])
  \\ gvs []
  \\ qexists_tac ‘Link u t (SOME (i,EL i arr))’
  \\ qexists_tac ‘(u,x')::ys’
  \\ qexists_tac ‘t'’
  \\ qexists_tac ‘zs’
  \\ fs [lookups_def,lupdate_list_def]
  \\ qpat_x_assum ‘LUPDATE _ _ _ = _’ (assume_tac o GSYM)
  \\ fs [LUPDATE_EL]
  \\ qsuff_tac ‘t = t'’ >- fs []
  \\ ‘∃a opt. FLOOKUP m u = SOME (Link a t' opt)’ by
    (Cases_on ‘ys’ \\ fs [lookups_def] \\ PairCases_on ‘h’ \\ fs [lookups_def])
  \\ metis_tac [state_ok_def]
QED

Triviality lookups_append:
  ∀xs a x.
    lookups m a x (xs ++ (b,y)::ys) t zs ⇒
    lookups m b y ys t zs
Proof
  Induct
  \\ fs [lookups_def,PULL_EXISTS,FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality lookups_11:
  ∀a x xs y ys.
    lookups m a x xs t zs ∧ lookups m a y ys t zs ⇒
    x = y ∧ xs = ys
Proof
  Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [lookups_def]
  >- (PairCases_on ‘h’ \\ gvs [lookups_def])
  >- (PairCases \\ gvs [lookups_def])
  \\ PairCases_on ‘h’ \\ gvs [lookups_def]
  \\ PairCases \\ gvs [lookups_def]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ res_tac \\ fs []
QED

Triviality lookups_imp_Array:
  ∀ys a x.
    lookups m a x ys b zs ⇒ FLOOKUP m b = SOME (Array zs)
Proof
  Induct \\ fs [lookups_def,FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality lookup_same_a:
  lookups m a x ys a zs ⇒ F
Proof
  strip_tac \\ imp_res_tac lookups_imp_Array
  \\ Cases_on ‘ys’ \\ gvs [lookups_def]
  \\ PairCases_on ‘h’ \\ gvs [lookups_def]
QED

Theorem lookups_distinct:
  lookups m a x ys t zs ⇒ ALL_DISTINCT (t::a::MAP FST ys)
Proof
  strip_tac \\ CCONTR_TAC
  \\ gvs [lookup_same_a]
  >-
   (gvs [MEM_MAP,MEM_SPLIT] \\ Cases_on ‘y’
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac lookups_append \\ fs [lookup_same_a])
  >-
   (gvs [MEM_MAP,MEM_SPLIT] \\ Cases_on ‘y’
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac lookups_append
    \\ imp_res_tac lookups_11 \\ fs [])
  \\ qsuff_tac ‘∀ys a x. lookups m a x ys t zs ⇒ ALL_DISTINCT (MAP FST ys)’
  >- metis_tac []
  \\ Induct \\ fs [lookups_def,FORALL_PROD]
  \\ rw [] \\ res_tac \\ gvs []
  \\ CCONTR_TAC \\ fs []
  \\ gvs [MEM_MAP,MEM_SPLIT] \\ Cases_on ‘y’
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ imp_res_tac lookups_append
  \\ imp_res_tac lookups_11 \\ fs []
QED

Inductive calc_focus:
[~last:]
  (FLOOKUP m a = SOME (Link arr arr NONE) ⇒
   calc_focus a m arr m) ∧
[~step:]
  (FLOOKUP m a = SOME (Link b u (SOME (i,x))) ∧ u ≠ b ∧
   calc_focus b m arr m1 ∧
   FLOOKUP m1 arr = SOME (Array ts) ∧ i < LENGTH ts ⇒
   calc_focus a m arr (m1 |+ (arr,Array (LUPDATE x i ts))
                          |+ (a,Link arr arr NONE)
                          |+ (b,Link a arr (SOME (i,EL i ts)))))
End

Theorem mutvec_focus:
  spec (a,xs) m ∧ state_ok m ⇒
  ∃arr m1.
    calc_focus a m arr m1 ∧
    FLOOKUP m1 a = SOME (Link arr arr NONE) ∧
    state_ok m1 ∧ (∀y. spec y m ⇒ spec y m1)
Proof
  strip_tac
  \\ drule_all spec_imp_lookups \\ strip_tac
  \\ imp_res_tac lookups_distinct
  \\ qsuff_tac ‘
      ∀m ys a x arr.
        state_ok m ∧ lookups m a x ys arr zs ∧ ALL_DISTINCT (arr::a::MAP FST ys) ⇒
        ∃m1 us.
          calc_focus a m arr m1 ∧ FLOOKUP m1 a = SOME (Link arr arr NONE) ∧
          state_ok m1 ∧ (∀y. y ∈ m ⇒ y ∈ m1) ∧
          FLOOKUP m1 arr = SOME (Array us) ∧ LENGTH us = LENGTH zs ∧
          (∀b. ~MEM b (a::MAP FST ys) ∧ b ≠ arr ⇒ FLOOKUP m1 b = FLOOKUP m b)’
  >- (disch_then drule_all \\ strip_tac \\ fs [] \\ metis_tac [])
  \\ rpt $ pop_assum kall_tac
  \\ Induct_on ‘ys’ \\ fs [lookups_def] \\ rw []
  >- (irule_at Any calc_focus_last \\ fs [])
  \\ PairCases_on ‘h’ \\ gvs [lookups_def]
  \\ irule_at Any calc_focus_step
  \\ last_x_assum drule_all \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos $ el 2 \\ fs []
  \\ qexists_tac ‘LUPDATE d i us’
  \\ fs [FLOOKUP_UPDATE]
  \\ ‘FLOOKUP m1 a = SOME (Link h0 arr (SOME (i,d)))’ by
    (irule EQ_TRANS \\ last_assum $ irule_at Any
     \\ first_x_assum irule \\ fs [])
  \\ drule (GEN_ALL mutvec_focus_one) \\ fs []
QED

(* new *)

Inductive calc_new:
  (∀new1 new2 xs m.
    calc_new new1 new2 xs m (m |+ (new1,Link new2 new2 NONE)
                               |+ (new2,Array xs)))
End

Theorem mutvec_new:
  state_ok m ∧ new1 ∉ FDOM m ∧ new2 ∉ FDOM m ∧ new1 ≠ new2 ⇒
  ∃m1.
    calc_new new1 new2 xs m m1 ∧
    state_ok m1 ∧
    spec (new1,xs) m1 ∧ (∀y. spec y m ⇒ spec y m1)
Proof
  simp [Once calc_new_cases,PULL_EXISTS]
  \\ rw []
  >-
   (fs [Once state_ok_def,FLOOKUP_UPDATE]
    \\ fs [FLOOKUP_DEF,AllCaseEqs()]
    \\ conj_tac >- (rw [] \\ res_tac \\ gvs [])
    \\ conj_tac >- (rw [] \\ res_tac \\ gvs [])
    \\ last_x_assum kall_tac
    \\ last_x_assum kall_tac
    \\ metis_tac [])
  >- (irule_at Any spec_last \\ fs [FLOOKUP_UPDATE])
  \\ irule_at Any spec_extend
  \\ irule_at Any spec_extend
  \\ fs []
QED

(* copy *)

Inductive copy_array:
  ∀arr m new.
    FLOOKUP m arr = SOME (Array xs) ∧ new ∉ FDOM m ⇒
    copy_array arr new m (m |+ (new,Array xs))
End

Inductive update_array:
  ∀arr i x m.
    FLOOKUP m arr = SOME (Array xs) ∧ i < LENGTH xs ⇒
    update_array arr i x m (m |+ (arr,Array (LUPDATE x i xs)))
End

Inductive calc_copy_rec:
  (∀a new m m1.
     FLOOKUP m a = SOME $ Link arr arr NONE ∧
     copy_array arr new m m1 ⇒
     calc_copy_rec a m new m1) ∧
  (∀a m arr i x b t.
     FLOOKUP m a = SOME $ Link b t (SOME (i,x)) ∧ b ≠ arr ∧
     calc_copy_rec b m arr m1 ∧
     update_array arr i x m1 m2 ⇒
     calc_copy_rec a m arr m2)
End

Inductive calc_copy:
  ∀a m new1 new2 m1.
    calc_copy_rec a m new2 m1 ⇒
    calc_copy a new1 new2 m (m1 |+ (new1, Link new2 new2 NONE))
End

Triviality LENGTH_lupdate_list:
  ∀xs zs. LENGTH (lupdate_list xs zs) = LENGTH zs
Proof
  Induct \\ fs [lupdate_list_def]
  \\ Cases \\ fs [lupdate_list_def]
  \\ Cases_on ‘o'’ \\ fs [lupdate_list_def]
  \\ Cases_on ‘x’ \\ fs [lupdate_list_def]
QED

Theorem calc_copy_thm:
  spec (a,xs) m ∧ state_ok m ∧ new1 ∉ FDOM m ∧ new2 ∉ FDOM m ∧ new1 ≠ new2 ⇒
  calc_copy a new1 new2 m (m |+ (new1,Link new2 new2 NONE)
                             |+ (new2,Array xs))
Proof
  strip_tac
  \\ drule_all spec_imp_lookups
  \\ strip_tac \\ gvs []
  \\ simp [Once FUPDATE_COMMUTES]
  \\ simp [Once calc_copy_cases]
  \\ qexists_tac ‘m |+ (new2,Array (lupdate_list (x::MAP SND ys) zs))’ \\ fs []
  \\ qsuff_tac ‘
      ∀a x ys.
        lookups m a x ys t zs ∧ new2 ∉ FDOM m ⇒
        calc_copy_rec a m new2 (m |+ (new2,Array (lupdate_list (x::MAP SND ys) zs)))’
  >- (disch_then drule \\ fs [])
  \\ rpt $ pop_assum kall_tac
  \\ Induct_on ‘ys’
  \\ fs [lookups_def] \\ rw[]
  >- simp [Once calc_copy_rec_cases,copy_array_cases,lupdate_list_def]
  \\ PairCases_on ‘h’ \\ gvs [lookups_def,lupdate_list_def]
  \\ first_x_assum drule
  \\ strip_tac
  \\ simp [Once calc_copy_rec_cases,copy_array_cases,lupdate_list_def]
  \\ pop_assum $ irule_at Any
  \\ fs [update_array_cases,FLOOKUP_UPDATE,LENGTH_lupdate_list]
  \\ Cases_on ‘ys’ \\ fs [lookups_def,FLOOKUP_DEF]
  \\ CCONTR_TAC \\ gvs []
  \\ Cases_on ‘h’ \\ fs [lookups_def,FLOOKUP_DEF]
QED

Theorem mutvec_copy:
  spec (a,xs) m ∧ state_ok m ∧ new1 ∉ FDOM m ∧ new2 ∉ FDOM m ∧ new1 ≠ new2 ⇒
  ∃m1.
    calc_copy a new1 new2 m m1 ∧
    state_ok m1 ∧
    spec (new1,xs) m1 ∧ (∀y. spec y m ⇒ spec y m1)
Proof
  strip_tac
  \\ irule_at Any calc_copy_thm
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [] \\ mp_tac mutvec_new \\ fs []
  \\ simp [Once calc_new_cases]
QED

(*
  TODO:
   - speed up slow proofs
   - implement focus using only tail recursion?
   - implement copy with only tail recursion?
*)

val _ = export_theory();
