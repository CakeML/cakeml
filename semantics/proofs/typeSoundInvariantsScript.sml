(*
  A type system for values, and
  the invariants that are used for type soundness.
*)
Theory typeSoundInvariants
Ancestors
  ast namespace semanticPrimitives typeSystem namespaceProps

Datatype:
 store_t =
 | Ref_t t
 | W8array_t
 | Varray_t t
End

(* Store typing *)
Type tenv_store = ``:(num, store_t) fmap``

(* Check that the type names map to valid types *)
Definition tenv_abbrev_ok_def:
  tenv_abbrev_ok tenvT ⇔ nsAll (\id (tvs,t). check_freevars 0 tvs t) tenvT
End

Definition tenv_ctor_ok_def:
  tenv_ctor_ok tenvC ⇔ nsAll (\id (tvs,ts,tn). EVERY (check_freevars 0 tvs) ts) tenvC
End

Definition tenv_val_ok_def:
  tenv_val_ok tenvV ⇔ nsAll (\id (tvs,t). check_freevars tvs [] t) tenvV
End

Definition tenv_ok_def:
  tenv_ok tenv ⇔
    tenv_val_ok tenv.v ∧
    tenv_ctor_ok tenv.c ∧
    tenv_abbrev_ok tenv.t
End

Definition tenv_val_exp_ok_def:
  (tenv_val_exp_ok Empty ⇔ T) ∧
  (tenv_val_exp_ok (Bind_tvar n tenv) ⇔ tenv_val_exp_ok tenv) ∧
  (tenv_val_exp_ok (Bind_name x tvs t tenv) ⇔
    check_freevars (tvs + num_tvs tenv) [] t ∧
    tenv_val_exp_ok tenv)
End

(* Global constructor type environments keyed by constructor name and type
 * stamp. Contains the type variables, the type of the arguments, and
 * the identity of the type. *)
Type ctMap = ``:(stamp, (tvarN list # t list # type_ident)) fmap``

(* Ordinary datatype signatures are closed: unlike exceptions, declarations
 * cannot add constructors to an existing static type identity.  Record the
 * complete entry, including parameter order and resolved argument types. *)
Definition datatype_signature_def:
  datatype_signature (ctMap:ctMap) ti =
    {entry | ?cn n tvs ts.
      entry = (cn,n,tvs,ts) /\
      FLOOKUP ctMap (TypeStamp cn n) = SOME (tvs,ts,ti)}
End

Definition preserves_datatype_signatures_def:
  preserves_datatype_signatures tids (ctMap:ctMap) ctMap' <=>
    !ti. ti NOTIN tids ==>
      datatype_signature ctMap' ti = datatype_signature ctMap ti
End

Theorem datatype_signature_member:
  (cn,n,tvs,ts) IN datatype_signature ctMap ti <=>
  FLOOKUP ctMap (TypeStamp cn n) = SOME (tvs,ts,ti)
Proof
  simp [datatype_signature_def]
QED

Theorem preserves_datatype_signatures_refl:
  preserves_datatype_signatures tids ctMap ctMap
Proof
  simp [preserves_datatype_signatures_def]
QED

Theorem preserves_datatype_signatures_mono:
  preserves_datatype_signatures tids ctMap ctMap' /\ tids SUBSET tids' ==>
  preserves_datatype_signatures tids' ctMap ctMap'
Proof
  rw [preserves_datatype_signatures_def, pred_setTheory.SUBSET_DEF] >>
  metis_tac []
QED

Theorem preserves_datatype_signatures_trans:
  preserves_datatype_signatures tids ctMap ctMap' /\
  preserves_datatype_signatures tids' ctMap' ctMap'' ==>
  preserves_datatype_signatures (tids UNION tids') ctMap ctMap''
Proof
  rw [preserves_datatype_signatures_def]
QED

Theorem preserves_datatype_signatures_fresh:
  ctMap SUBMAP ctMap' /\
  (!cn n tvs ts ti.
    FLOOKUP ctMap' (TypeStamp cn n) = SOME (tvs,ts,ti) /\
    FLOOKUP ctMap (TypeStamp cn n) = NONE ==> ti IN tids) ==>
  preserves_datatype_signatures tids ctMap ctMap'
Proof
  rw [preserves_datatype_signatures_def, pred_setTheory.EXTENSION,
      pairTheory.FORALL_PROD, datatype_signature_member] >>
  rename1 `FLOOKUP ctMap' (TypeStamp cn n) = SOME (tvs,ts,ti)` >>
  Cases_on `FLOOKUP ctMap (TypeStamp cn n)`
  >- (
    simp [] >>
    metis_tac []) >>
  imp_res_tac finite_mapTheory.FLOOKUP_SUBMAP >> simp []
QED

Theorem preserves_datatype_signatures_funion:
  ctMap SUBMAP (FUNION added ctMap) /\
  (!cn n tvs ts ti.
    FLOOKUP added (TypeStamp cn n) = SOME (tvs,ts,ti) ==> ti IN tids) ==>
  preserves_datatype_signatures tids ctMap (FUNION added ctMap)
Proof
  strip_tac >>
  irule preserves_datatype_signatures_fresh >>
  simp [] >>
  rw [finite_mapTheory.FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP added (TypeStamp cn n)` >> gvs [] >> res_tac
QED

Theorem preserves_datatype_signatures_exn:
  preserves_datatype_signatures tids ctMap (ctMap |+ (ExnStamp n,entry))
Proof
  simp [preserves_datatype_signatures_def, pred_setTheory.EXTENSION,
        pairTheory.FORALL_PROD, datatype_signature_member,
        finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem datatype_signature_empty:
  datatype_signature ctMap ti = EMPTY <=>
  !cn n tvs ts. FLOOKUP ctMap (TypeStamp cn n) <> SOME (tvs,ts,ti)
Proof
  simp [pred_setTheory.EXTENSION, pairTheory.FORALL_PROD,
        datatype_signature_member]
QED

Theorem datatype_signature_funion_new:
  datatype_signature ctMap ti = EMPTY ==>
  datatype_signature (FUNION added ctMap) ti = datatype_signature added ti
Proof
  rw [datatype_signature_empty, pred_setTheory.EXTENSION,
      pairTheory.FORALL_PROD, datatype_signature_member,
      finite_mapTheory.FLOOKUP_FUNION] >>
  rename1 `FLOOKUP added (TypeStamp cn n) = SOME (tvs,ts,ti)` >>
  Cases_on `FLOOKUP added (TypeStamp cn n)` >> simp []
QED

Definition ctMap_ok_def:
  ctMap_ok ctMap ⇔
    (* No free variables in the range *)
    FEVERY (\ (stamp,(tvs,ts, _)). EVERY (check_freevars 0 tvs) ts) ctMap ∧
    (* Exceptions have type exception, and no type variables *)
    (!ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs, ts, ti) ⇒
      tvs = [] ∧ ti = Texn_num) ∧
    (* Primitive, non-constructor types are not mapped *)
    (!cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME (tvs, ts, ti) ⇒
      ~MEM ti prim_type_nums) ∧
    (* If type identities are equal then the stamps are from the same type *)
    (!stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
      FLOOKUP ctMap stamp1 = SOME (tvs1, ts1, ti) ∧
      FLOOKUP ctMap stamp2 = SOME (tvs2, ts2, ti) ⇒
      same_type stamp1 stamp2)
End

(* Check that a constructor type environment is consistent with a runtime type
 * enviroment, using the full type keyed constructor type environment to ensure
 * that the correct types are used. *)
Definition type_ctor_def:
  type_ctor ctMap _ (n, stamp) (tvs, ts, ti) ⇔
    FLOOKUP ctMap stamp = SOME (tvs, ts, ti) ∧
    LENGTH ts = n
End

Definition add_tenvE_def:
  (add_tenvE Empty tenvV = tenvV) ∧
  (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) ∧
  (add_tenvE (Bind_name x tvs t tenvE) tenvV = nsBind x (tvs,t) (add_tenvE tenvE tenvV))
End

Inductive type_v:
  (!tvs ctMap tenvS n.
    type_v tvs ctMap tenvS (Litv (IntLit n)) Tint) ∧
  (!tvs ctMap tenvS c.
    type_v tvs ctMap tenvS (Litv (Char c)) Tchar) ∧
  (!tvs ctMap tenvS s.
    type_v tvs ctMap tenvS (Litv (StrLit s)) Tstring) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Word8 w)) Tword8) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Word64 w)) Tword64) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Float64 w)) Tdouble) ∧
  (!tvs ctMap tenvS vs tvs' stamp ts' ts ti.
    EVERY (check_freevars tvs []) ts' ∧
    LENGTH tvs' = LENGTH ts' ∧
    LIST_REL (type_v tvs ctMap tenvS)
      vs (MAP (type_subst (FUPDATE_LIST FEMPTY (REVERSE (ZIP (tvs', ts'))))) ts) ∧
    FLOOKUP ctMap stamp = SOME (tvs',ts,ti)
    ⇒
    type_v tvs ctMap tenvS (Conv (SOME stamp) vs) (Tapp ts' ti)) ∧
  (!tvs ctMap tenvS vs ts.
    LIST_REL (type_v tvs ctMap tenvS) vs ts
    ⇒
    type_v tvs ctMap tenvS (Conv NONE vs) (Ttup ts)) ∧
  (!tvs ctMap tenvS env tenv tenvE n e t1 t2.
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    nsAll2 (type_ctor ctMap) env.c tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
    check_freevars tvs [] t1 ∧
    type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2
    ⇒
    type_v tvs ctMap tenvS (Closure env n e) (Tfn t1 t2)) ∧
  (!tvs ctMap tenvS env funs n t tenv tenvE bindings.
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    nsAll2 (type_ctor ctMap) env.c tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALOOKUP bindings n = SOME t ∧
    ALL_DISTINCT (MAP FST funs) ∧
    MEM n (MAP FST funs)
    ⇒
    type_v tvs ctMap tenvS (Recclosure env funs n) t) ∧
  (!tvs ctMap tenvS n t.
    check_freevars 0 [] t ∧
    FLOOKUP tenvS n = SOME (Ref_t t)
    ⇒
    type_v tvs ctMap tenvS (Loc T n) (Tref t)) ∧
  (!tvs ctMap tenvS n.
    FLOOKUP tenvS n = SOME W8array_t
    ⇒
    type_v tvs ctMap tenvS (Loc T n) Tword8array) ∧
  (!tvs ctMap tenvS n t.
    check_freevars 0 [] t ∧
    FLOOKUP tenvS n = SOME (Varray_t t)
    ⇒
    type_v tvs ctMap tenvS (Loc T n) (Tarray t)) ∧
  (!tvs ctMap tenvS vs t.
    check_freevars 0 [] t ∧
    EVERY (\v. type_v tvs ctMap tenvS v t) vs
    ⇒
    type_v tvs ctMap tenvS (Vectorv vs) (Tvector t))
End

Definition type_sv_def:
  (type_sv ctMap tenvS (Refv v) (Ref_t t) ⇔ type_v 0 ctMap tenvS v t) ∧
  (type_sv ctMap tenvS (W8array v) W8array_t ⇔ T) ∧
  (type_sv ctMap tenvS (Varray vs) (Varray_t t) ⇔
    EVERY (\v. type_v 0 ctMap tenvS v t) vs) ∧
  (type_sv _ _ _ _ ⇔ F)
End


(* The type of the store *)
Definition type_s_def:
  type_s ctMap envS tenvS ⇔
    (!l.
      ((?st. FLOOKUP tenvS l = SOME st) ⇔ (?v. store_lookup l envS = SOME v)) ∧
      (!st sv.
        FLOOKUP tenvS l = SOME st ∧ store_lookup l envS = SOME sv
        ⇒
        type_sv ctMap tenvS sv st))
End

(* The global constructor type environment has the primitive exceptions in it *)
Definition ctMap_has_exns_def:
  ctMap_has_exns ctMap ⇔
    FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)
End

(* The global constructor type environment has the list primitives in it *)
Definition ctMap_has_lists_def:
  ctMap_has_lists ctMap ⇔
    FLOOKUP ctMap (TypeStamp «[]» list_type_num) = SOME ([«'a»],[],Tlist_num) ∧
    FLOOKUP ctMap (TypeStamp «::» list_type_num) =
      SOME ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num) ∧
    (!cn. cn ≠ «::» ∧ cn ≠ «[]» ⇒ FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)
End

(* The global constructor type environment has the bool primitives in it *)
Definition ctMap_has_bools_def:
  ctMap_has_bools ctMap ⇔
    FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) ∧
    FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) ∧
    (!cn. cn ≠ «True» ∧ cn ≠ «False» ⇒ FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)
End

Definition good_ctMap_def:
  good_ctMap ctMap ⇔
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap
End

    (*
(* The types and exceptions that are missing are all declared in modules. *)
Definition weak_decls_only_mods_def:
  weak_decls_only_mods d1 d2 ⇔
    (!tn. Short tn ∈ d1.defined_types ⇒ Short tn ∈ d2.defined_types) ∧
    (!cn. Short cn ∈ d1.defined_exns ⇒ Short cn ∈ d2.defined_exns)
End

(* The run-time declared constructors and exceptions are all either declared in
 * the type system, or from modules that have been declared *)
Definition consistent_decls_def:
  consistent_decls tes d ⇔
    (!(te :: tes).
       case te of
       | TypeExn cid =>
           cid ∈ d.defined_exns ∨
           (?mn cn. cid = Long mn (Short cn) ∧ [mn] ∈ d.defined_mods)
       | TypeId tid =>
           tid ∈ d.defined_types ∨
           (?mn tn. tid = Long mn (Short tn) ∧([mn] ∈ d.defined_mods)))
End
           *)

Definition consistent_ctMap_def:
  consistent_ctMap st type_ids ctMap ⇔
    (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) ∧
    !cn id.
      (TypeStamp cn id ∈ FDOM ctMap ⇒ id < st.next_type_stamp) ∧
      (ExnStamp id ∈ FDOM ctMap ⇒ id < st.next_exn_stamp)
End

       (*
Definition decls_ok_def:
  decls_ok d ⇔ [] ∉ d.defined_mods ∧ decls_to_mods d ⊆ {[]} ∪ d.defined_mods
End
  *)

Definition type_all_env_def:
  type_all_env ctMap tenvS env tenv ⇔
    nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v env) tenv.v
End

Definition type_sound_invariant_def:
type_sound_invariant st env ctMap tenvS type_idents tenv ⇔
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS
End

(* Reference inversions expose the store-typing witness used by an environment. *)
Theorem type_v_reference:
  type_v tvs ctMap tenvS (Loc T loc) (Tref ty) <=>
  check_freevars 0 [] ty /\ FLOOKUP tenvS loc = SOME (Ref_t ty)
Proof
  simp [Once type_v_cases, Tref_def, Tarray_def, Tword8array_def,
        Tref_num_def, Tarray_num_def, Tword8array_num_def]
QED

Theorem type_all_env_reference:
  type_all_env ctMap tenvS env tenv /\
  nsLookup env.v name = SOME (Loc T loc) /\
  nsLookup tenv.v name = SOME (0,Tref ty) ==>
  check_freevars 0 [] ty /\ FLOOKUP tenvS loc = SOME (Ref_t ty)
Proof
  strip_tac >> fs [type_all_env_def] >>
  drule_all nsAll2_nsLookup1 >>
  simp [type_v_reference]
QED

Theorem type_s_reference:
  type_s ctMap refs tenvS /\ FLOOKUP tenvS loc = SOME (Ref_t ty) ==>
  ?value. store_lookup loc refs = SOME (Refv value) /\
    type_v 0 ctMap tenvS value ty
Proof
  rw [type_s_def] >>
  first_x_assum (qspec_then `loc` mp_tac) >> simp [] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `stored` assume_tac) mp_tac) >>
  disch_then (qspec_then `stored` mp_tac) >> simp [] >>
  Cases_on `stored` >> simp [type_sv_def]
QED

Theorem constructor_type_stamp_index:
  ctMap_ok ctMap /\
  FLOOKUP ctMap (TypeStamp anchor index) = SOME (ctor_params,ctor_fields,ti) /\
  FLOOKUP ctMap (TypeStamp cn n) = SOME (other_params,other_fields,ti) ==>
  n = index
Proof
  rw [ctMap_ok_def] >> res_tac >> fs [same_type_def]
QED

Theorem type_sound_invariant_reserve:
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS {} tenv /\
  DISJOINT tids (FRANGE ((SND o SND) o_f ctMap)) ==>
  type_sound_invariant st env ctMap tenvS tids tenv
Proof
  simp [type_sound_invariant_def, consistent_ctMap_def] >>
  rw [] >> res_tac
QED

Theorem type_sound_invariant_clock:
  type_sound_invariant ((st:'ffi semanticPrimitives$state) with clock := ck)
    env ctMap tenvS tids tenv <=>
  type_sound_invariant st env ctMap tenvS tids tenv
Proof
  simp [type_sound_invariant_def, consistent_ctMap_def]
QED

(* Abbreviation environments may differ while c/v typing is unchanged. *)
Theorem type_sound_invariant_retarget:
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS tids
    input_tenv /\
  tenv_ok output_tenv /\
  output_tenv.c = input_tenv.c /\ output_tenv.v = input_tenv.v ==>
  type_sound_invariant st env ctMap tenvS tids output_tenv
Proof
  simp [type_sound_invariant_def, type_all_env_def]
QED
