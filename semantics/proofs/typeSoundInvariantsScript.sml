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
