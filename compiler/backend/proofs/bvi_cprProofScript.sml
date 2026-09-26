(*
  Correctness of the constructed product result (CPR) optimisation of
  BVI, bvi_cpr.
*)
Theory bvi_cprProof
Ancestors
  bvi bviSem bviProps bvi_cpr backend_common[qualified] bvi_inline[qualified]
Libs
  preamble

Definition flex_free_def:
  (flex_free Leaf ⇔ T) ∧
  (flex_free Flexible ⇔ F) ∧
  (flex_free (ConsShape t shs) ⇔ flex_free_list shs) ∧

  (flex_free_list [] ⇔ T) ∧
  (flex_free_list (sh::shs) ⇔ flex_free sh ∧ flex_free_list shs)
End

Theorem sub_shape_refl:
  (∀sh. sub_shape sh sh) ∧
  (∀l. sub_shape_list l l)
Proof
  Induct >> rw[sub_shape_def]
QED


Theorem sub_shape_trans:
  (∀s1 s2 s3. sub_shape s1 s2 ∧ sub_shape s2 s3 ⇒ sub_shape s1 s3) ∧
  (∀l1 l2 l3. sub_shape_list l1 l2 ∧ sub_shape_list l2 l3 ⇒ sub_shape_list l1 l3)
Proof
  Induct >> rw[sub_shape_def]
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def]
      >- (Cases_on ‘s3’ >> gvs[sub_shape_def]
          >> metis_tac[]
         )
      >> Cases_on ‘s3’ >> gvs[sub_shape_def]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def]
      >> Cases_on ‘l3’ >> gvs[sub_shape_def]
      >> metis_tac[]
     )
QED

Theorem sub_shape_flex_free:
  (∀s1 s2. sub_shape s1 s2 ∧ flex_free s2 ⇒ flex_free s1) ∧
  (∀l1 l2. sub_shape_list l1 l2 ∧ flex_free_list l2 ⇒ flex_free_list l1)
Proof
  Induct >> rw[sub_shape_def, flex_free_def]
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, flex_free_def]
      >> metis_tac[]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, flex_free_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def, flex_free_def]
      >> metis_tac[]
     )
  >> Cases_on ‘l2’ >> gvs[sub_shape_def, flex_free_def]
  >> metis_tac[]
QED

Theorem cpr_merge_sub_shape:
  (∀s1 s2. sub_shape (cpr_merge s1 s2) s1 ∧ sub_shape (cpr_merge s1 s2) s2) ∧
  (∀l1 l2. LENGTH l1 = LENGTH l2 ⇒
           sub_shape_list (cpr_merge_list l1 l2) l1 ∧ sub_shape_list (cpr_merge_list l1 l2) l2)
Proof
  Induct >> rw[sub_shape_def, cpr_merge_def]
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
      >- rw[sub_shape_def, cpr_merge_def]
      >> rw[sub_shape_refl]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> rw[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘s2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> rw[sub_shape_refl]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
QED


Theorem flex_free_cpr_merge:
  (∀s1 s2. (flex_free s1) ∧ (flex_free s2) ⇒ flex_free (cpr_merge s1 s2)) ∧
  (∀l1 l2. (flex_free_list l1) ∧ (flex_free_list l2) ⇒ flex_free_list (cpr_merge_list l1 l2))
Proof
  Induct >> rw[flex_free_def, cpr_merge_def]
  >- (Cases_on ‘s2’ >> gvs[flex_free_def, cpr_merge_def]
     )
  >- (Cases_on ‘s2’ >> gvs[flex_free_def, cpr_merge_def]
      >> rw[flex_free_def, cpr_merge_def]
     )
  >> Cases_on ‘l2’ >> rw[flex_free_def, cpr_merge_def]
  >- (last_x_assum $ irule
      >> gvs[flex_free_def]
     )
  >> last_x_assum $ irule
  >> gvs[flex_free_def]
QED


Theorem split_ok_ConsShape:
  ∀sh. split_ok sh ⇒ ∃t shs. sh = ConsShape t shs ∧ 1 < shape_width sh
Proof
  rw[split_ok_def]
  >> Cases_on ‘sh’ >> gvs[shape_width_def]
QED

Definition exp_shape_ok_def:
  (exp_shape_ok Leaf (e:bvi$exp) ⇔ T) ∧
  (exp_shape_ok Flexible e ⇔ T) ∧
  (exp_shape_ok (ConsShape t shs) e ⇔
     ∃xs. e = Op (BlockOp (Cons t)) xs ∧ LENGTH xs = LENGTH shs ∧
          exp_shape_ok_list shs xs) ∧

  (exp_shape_ok_list [] xs ⇔ xs = []) ∧
  (exp_shape_ok_list (sh::shs) xs ⇔
     ∃x xs'. xs = x::xs' ∧ exp_shape_ok sh x ∧ exp_shape_ok_list shs xs')
End

Theorem field_shape_exp_shape_ok:
  (∀e. exp_shape_ok (field_shape e) e ∧ flex_free (field_shape e)) ∧
  (∀xs. exp_shape_ok_list (field_shape_list xs) xs ∧
        flex_free_list (field_shape_list xs))
Proof
  ho_match_mp_tac field_shape_ind >> rw[exp_shape_ok_def, field_shape_def, flex_free_def]
  >> Induct_on ‘xs’ >> gvs[exp_shape_ok_def, field_shape_def, flex_free_def]
QED

Theorem exp_shape_ok_list_length_eq:
  ∀l l'. exp_shape_ok_list l l' ⇒ LENGTH l = LENGTH l'
Proof
  Induct >> rw[exp_shape_ok_def]
  >> fs[]
QED


Theorem exp_shape_ok_mono:
  (∀sh sh' e.
     sub_shape sh' sh ∧ flex_free sh ∧ exp_shape_ok sh e ⇒ exp_shape_ok sh' e) ∧
  (∀l l' le.
     sub_shape_list l' l ∧ flex_free_list l ∧ exp_shape_ok_list l le ⇒ exp_shape_ok_list l' le)
Proof
  Induct >> rw[sub_shape_def, flex_free_def, exp_shape_ok_def]
  >- (Cases_on ‘sh'’ >> gvs[sub_shape_def, flex_free_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘sh'’ >> gvs[sub_shape_def, flex_free_def, exp_shape_ok_def]
      >> last_x_assum $ rev_drule_then assume_tac
      >> first_x_assum $ drule_then assume_tac
      >> metis_tac[exp_shape_ok_list_length_eq]
     )
  >- (Cases_on ‘l'’ >> gvs[sub_shape_def, flex_free_def, exp_shape_ok_def]
     )
  >> Cases_on ‘l'’ >> gvs[sub_shape_def, flex_free_def, exp_shape_ok_def]
QED


Theorem flatten_exp_LENGTH:
  (∀sh e. exp_shape_ok sh e ⇒ LENGTH (flatten_exp sh e) = shape_width sh) ∧
  (∀shs xs. exp_shape_ok_list shs xs ⇒
            LENGTH (flatten_list shs xs) = shape_width_list shs)
Proof
  Induct >> rw[flatten_exp_def, shape_width_def, exp_shape_ok_def]
  >- (FULL_CASE_TAC >> gvs[]
     )
  >> rw[flatten_exp_def]
QED

Definition tail_ok_def:
  (tail_ok m f sh (If g e1 e2) ⇔ tail_ok m f sh e1 ∧ tail_ok m f sh e2) ∧
  (tail_ok m f sh (Let xs e) ⇔ tail_ok m f sh e) ∧
  (tail_ok m f sh (Tick e) ⇔ tail_ok m f sh e) ∧
  (tail_ok m f sh (LetCall n ts d args e) ⇔ tail_ok m f sh e) ∧
  (tail_ok m f sh (Raise e) ⇔ T) ∧
  (tail_ok m f sh (Call ts dest args NONE) ⇔
     (sh = Leaf ∨
     (∃d. dest = SOME d ∧
         (d = f ∨ ∃dwk. lookup d m = SOME (sh,dwk))))) ∧
  (tail_ok m f sh (Call ts dest args (SOME hdle)) ⇔ sh = Leaf) ∧
  (tail_ok m f sh e ⇔ exp_shape_ok sh e)
End

Theorem tail_ok_submap:
  ∀m f sh e m'.
    (∀d x. lookup d m = SOME x ⇒ lookup d m' = SOME x) ∧ tail_ok m f sh e ⇒
    tail_ok m' f sh e
Proof
  ho_match_mp_tac tail_ok_ind >> rw[tail_ok_def, lookup_def]
  >> metis_tac[]
QED

Definition dest_cons_def:
  dest_cons t v =
    case v of
      Block t' vs => if t = t' then SOME (REVERSE vs) else NONE
    | _ => NONE
End

Definition v_shape_def:
  (v_shape Leaf v ⇔ T) ∧
  (v_shape Flexible v ⇔ T) ∧
  (v_shape (ConsShape t shs) v ⇔
     ∃vs. dest_cons t v = SOME vs ∧ LENGTH vs = LENGTH shs ∧
          v_shape_list shs vs) ∧

  (v_shape_list [] vs ⇔ vs = []) ∧
  (v_shape_list (sh::shs) vs ⇔
     ∃v vs'. vs = v::vs' ∧ v_shape sh v ∧ v_shape_list shs vs')
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (sh,_) => cpr_shape_size sh
                           | INR (shs,_) => list_size cpr_shape_size shs)’
End

Definition flat_vals_def:
  (flat_vals Leaf v = [v]) ∧
  (flat_vals Flexible v = [v]) ∧
  (flat_vals (ConsShape t shs) v =
     case dest_cons t v of
       SOME vs => flat_vals_list shs vs
     | NONE => [v]) ∧

  (flat_vals_list [] vs = []) ∧
  (flat_vals_list shs [] = []) ∧
  (flat_vals_list (sh::shs) (v::vs) = flat_vals sh v ++ flat_vals_list shs vs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (sh,_) => cpr_shape_size sh
                           | INR (shs,_) => list_size cpr_shape_size shs)’
End

Theorem flat_vals_LENGTH:
  (∀sh v. v_shape sh v ⇒ LENGTH (flat_vals sh v) = shape_width sh) ∧
  (∀shs vs. v_shape_list shs vs ⇒
            LENGTH (flat_vals_list shs vs) = shape_width_list shs)
Proof
  Induct >> rw[flat_vals_def, v_shape_def, shape_width_def, dest_cons_def]
  >- (FULL_CASE_TAC >> gvs[]
     )
  >> rw[flat_vals_def]
QED

Theorem evaluate_flatten_exp:
  (∀e sh env (s: ('a,'b) state) v t.
    exp_shape_ok sh e ∧ evaluate ([e],env,s) = (Rval [v],t) ⇒
    v_shape sh v ∧
    evaluate (flatten_exp sh e,env,s) = (Rval (flat_vals sh v),t)) ∧
  (∀oe.
     case oe of
     | SOME e =>
         (∀sh env (s: ('a,'b) state) v t.
           exp_shape_ok sh e ∧ evaluate ([e],env,s) = (Rval [v],t) ⇒
           v_shape sh v ∧
           evaluate (flatten_exp sh e,env,s) = (Rval (flat_vals sh v),t))
     | NONE => T) ∧
  (∀xs shs env (s: ('a,'b) state) vs t.
     exp_shape_ok_list shs xs ∧ evaluate (xs,env,s) = (Rval vs,t) ⇒
     v_shape_list shs vs ∧
     evaluate (flatten_list shs xs,env,s) = (Rval (flat_vals_list shs vs),t))
Proof
  Induct >> rw[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def]
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
      >- (FULL_CASE_TAC >> gvs[IS_SOME_DEF]
         )
      >> FULL_CASE_TAC >> gvs[IS_SOME_DEF]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
      >> every_case_tac >> gvs[do_app_def, do_app_aux_def, dest_cons_def]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘xs’, ‘env’, ‘s’] assume_tac >> gvs[]
      >> first_x_assum $ rev_drule_then assume_tac
      >> metis_tac[]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
      >> every_case_tac >> gvs[do_app_def, do_app_aux_def, dest_cons_def]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘xs’, ‘env’, ‘s’] assume_tac >> gvs[]
      >> first_x_assum $ rev_drule_then assume_tac
      >> metis_tac[bvl_to_bvi_id]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- metis_tac[]
  >- (Cases_on ‘shs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘shs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘shs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘e::xs’, ‘env’, ‘s’] assume_tac >> gvs[]
      >> Cases_on ‘vs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
      >> Cases_on ‘xs’ >> gvs[evaluate_def ,exp_shape_ok_def, flat_vals_def,
                              flatten_exp_def, evaluate_def, v_shape_def]
      >- metis_tac[]
      >> every_case_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[e]’, ‘env’, ‘s’] assume_tac >> gvs[]
      >> Cases_on ‘a'’ >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
     )
  >> Cases_on ‘shs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def, evaluate_def, v_shape_def]
  >> assume_tac evaluate_LENGTH
  >> pop_assum $ qspecl_then [‘e::xs’, ‘env’, ‘s’] assume_tac >> gvs[]
  >> Cases_on ‘vs’ >> gvs[exp_shape_ok_def, flat_vals_def, flatten_exp_def,
                          evaluate_def, v_shape_def]
  >> Cases_on ‘xs’ >> gvs[evaluate_def ,exp_shape_ok_def, flat_vals_def,
                          flatten_exp_def, evaluate_def, v_shape_def]
  >- (Cases_on ‘t'’ >> gvs[exp_shape_ok_def, evaluate_APPEND, flatten_exp_def, flat_vals_def]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
     )
  >> every_case_tac >> gvs[exp_shape_ok_def, evaluate_APPEND, flatten_exp_def, flat_vals_def]
  >> first_x_assum $ dxrule_then assume_tac >> gvs[]
  >> first_x_assum $ dxrule_then assume_tac >> gvs[]
  >> assume_tac evaluate_LENGTH
  >> pop_assum $ qspecl_then [‘[e]’, ‘env’, ‘s’] assume_tac >> gvs[]
  >> Cases_on ‘a'’ >> gvs[]
  >> first_x_assum $ dxrule_then assume_tac >> gvs[]
  >> first_x_assum $ dxrule_then assume_tac >> gvs[]
QED

Theorem evaluate_flatten_exp_err:
  (∀e sh env (s: ('a,'b) state) err t.
    exp_shape_ok sh e ∧ evaluate ([e],env,s) = (Rerr err,t) ⇒
    evaluate (flatten_exp sh e,env,s) = (Rerr err,t)) ∧
  (∀oe.
     case oe of
     | SOME e =>
         (∀sh env (s: ('a,'b) state) err t.
            exp_shape_ok sh e ∧ evaluate ([e],env,s) = (Rerr err,t) ⇒
            evaluate (flatten_exp sh e,env,s) = (Rerr err,t))
     | NONE => T) ∧
  (∀xs shs env (s: ('a,'b) state) err t.
     exp_shape_ok_list shs xs ∧ evaluate (xs,env,s) = (Rerr err,t) ⇒
     evaluate (flatten_list shs xs,env,s) = (Rerr err,t))
Proof
  Induct >> rw[exp_shape_ok_def, flatten_exp_def, evaluate_def]
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
      >- (FULL_CASE_TAC >> gvs[IS_SOME_DEF]
         )
      >> FULL_CASE_TAC >> gvs[IS_SOME_DEF]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
      >> every_case_tac >> gvs[do_app_def, do_app_aux_def, dest_cons_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘sh’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def]
     )
  >- (Cases_on ‘shs’ >> gvs[exp_shape_ok_def, flatten_exp_def, evaluate_def, v_shape_def, evaluate_APPEND]
      >> Cases_on ‘xs’ >> gvs[evaluate_def ,exp_shape_ok_def, flatten_exp_def]
      >- (first_x_assum $ dxrule_then assume_tac >> gvs[]
          >> first_x_assum $ dxrule_then assume_tac >> gvs[]
         )
      >> Cases_on ‘evaluate ([e],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (drule_then assume_tac $ cj 1 evaluate_flatten_exp
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[e]’, ‘env’, ‘s’] assume_tac >> gvs[]
          >> first_x_assum $ dxrule_then assume_tac >> gvs[]
          >> Cases_on ‘evaluate (h'::t'',env,r)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> first_x_assum $ dxrule_then assume_tac >> gvs[flatten_exp_def]
          >> first_x_assum $ dxrule_then assume_tac >> gvs[flatten_exp_def]
       )
      >> last_assum $ rev_dxrule_then assume_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
     )
QED

Theorem evaluate_rebuild:
 (∀sh v i env (s: ('a,'b) state).
    v_shape sh v ∧ i + shape_width sh ≤ LENGTH env ∧
    flat_vals sh v = TAKE (shape_width sh) (DROP i env) ⇒
    evaluate ([rebuild i sh],env,s) = (Rval [v],s)) ∧
 (∀shs vs i env (s: ('a,'b) state).
    v_shape_list shs vs ∧ i + shape_width_list shs ≤ LENGTH env ∧
    flat_vals_list shs vs = TAKE (shape_width_list shs) (DROP i env) ⇒
    evaluate (rebuild_list i shs,env,s) = (Rval vs,s))
Proof
  Induct >> rw[evaluate_def, rebuild_def, shape_width_def, flat_vals_def, v_shape_def, dest_cons_def]
  >- (Cases_on ‘v’ >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> first_x_assum $ dxrule_then assume_tac >> gvs[]
      >> rw[do_app_def, do_app_aux_def, bvl_to_bvi_id]
     )
  >> PURE_REWRITE_TAC[Once CONS_APPEND, evaluate_APPEND]
  >> last_x_assum $ rev_drule_then assume_tac >> gvs[]
  >> subgoal ‘i + shape_width sh ≤ LENGTH env’
  >- (irule LESS_EQ_TRANS
      >> first_assum $ irule_at Any
      >> irule $ iffRL ADD_MONO_LESS_EQ
      >> irule LESS_EQ_ADD
     )
  >> first_x_assum $ dxrule_then assume_tac >> gvs[flat_vals_def, TAKE_SUM]
  >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
  >> drule_then assume_tac $ cj 2 flat_vals_LENGTH
  >> subgoal ‘LENGTH (flat_vals sh v) = LENGTH (TAKE (shape_width sh) (DROP i env))’
  >- (irule EQ_TRANS
      >> first_x_assum $ irule_at Any
      >> irule EQ_SYM
      >> irule LENGTH_TAKE
      >> rw[LENGTH_DROP]
     )
  >> subgoal ‘LENGTH (flat_vals_list shs vs') = LENGTH (TAKE (shape_width_list shs)
                                                             (DROP (shape_width sh) (DROP i env)))’
  >- (irule EQ_TRANS
      >> first_x_assum $ irule_at Any
      >> irule EQ_SYM
      >> irule LENGTH_TAKE
      >> rw[LENGTH_DROP]
     )
  >> rev_drule_then assume_tac APPEND_LENGTH_EQ
  >> pop_assum $ drule_then assume_tac
  >> gvs[]
  >> first_x_assum $ drule_then assume_tac >> gvs[]
  >> ‘i + shape_width sh + shape_width_list shs ≤ LENGTH env’ by rw[]
  >> first_x_assum $ drule_then assume_tac >> gvs[]
  >> pop_assum $ qspec_then ‘s’ mp_tac >> impl_tac
  >- rw[DROP_DROP_T]
  >> rw[]
QED

Definition map_ok_def:
  map_ok m ⇔
    ∀d dsh dwk. lookup d m = SOME (dsh,dwk) ⇒ split_ok dsh ∧ flex_free dsh
End

Theorem flex_free_field_shape:
  (∀e. flex_free (field_shape e)) ∧
  (∀l. flex_free_list (field_shape_list l))
Proof
  Induct >> rw[flex_free_def, field_shape_def]
  >> Cases_on ‘o'’ >> rw[flex_free_def, field_shape_def]
  >> Cases_on ‘b’ >> rw[flex_free_def, field_shape_def]
QED

Theorem shape_and_tail_wf:
  ∀e f sh cs. shape_and_tail f e = (sh,cs) ⇒ flex_free sh ∨ sh = Flexible
Proof
  Induct >> rw[shape_and_tail_def, flex_free_def]
  >- (Cases_on ‘shape_and_tail f e''’ >> gvs[]
      >> Cases_on ‘shape_and_tail f e'’ >> gvs[]
      >> first_assum $ drule_then assume_tac >> gvs[cpr_merge_def]
      >- (last_assum $ drule_then assume_tac >> gvs[cpr_merge_def]
          >- (disj1_tac
              >> irule $ cj 1 flex_free_cpr_merge
              >> rw[]
             )
          >> Cases_on ‘q’ >> gvs[cpr_merge_def]
         )
      >> last_assum $ drule_then assume_tac >> gvs[cpr_merge_def]
      >> disj1_tac
      >> Cases_on ‘q'’ >> gvs[cpr_merge_def]
     )
  >- (last_x_assum $ drule_then assume_tac >> gvs[]
     )
  >- (last_x_assum $ drule_then assume_tac >> gvs[]
     )
  >- (every_case_tac >> gvs[flex_free_def]
     )
  >- rw[flex_free_field_shape]
  >> last_x_assum $ drule_then assume_tac >> gvs[]
QED

Theorem tail_shape_Flexible:
  ∀m cs. map_ok m ∧ tail_shape m cs = Flexible ⇒ cs = []
Proof
  Cases_on ‘cs’ >> gvs[tail_shape_def, map_ok_def]
  >> rpt strip_tac
  >> every_case_tac >> gvs[]
  >> pop_assum $ irule_at Any
  >> gvs[flex_free_def]
QED

Theorem tail_shape_lookup:
  ∀m cs csh.
    map_ok m ∧ tail_shape m cs = csh ∧ csh ≠ Leaf ∧ csh ≠ Flexible ⇒
    ∀d. MEM d cs ⇒ ∃dwk. lookup d m = SOME (csh,dwk)
Proof
  Induct_on ‘cs’ >> rw[tail_shape_def, lookup_def, MEM]
  >> every_case_tac >> gvs[]
  >> drule_all_then assume_tac tail_shape_Flexible >> gvs[]
QED

Theorem sub_shape_cpr_merge:
  (∀sh sh1 sh2. sub_shape sh (cpr_merge sh1 sh2) ⇒ sub_shape sh sh1 ∧ sub_shape sh sh2) ∧
  (∀l l1 l2. LENGTH l1 = LENGTH l2 ∧
             sub_shape_list l (cpr_merge_list l1 l2) ⇒ sub_shape_list l l1 ∧ sub_shape_list l l2)
Proof
  Induct >> rw[sub_shape_def, cpr_merge_def]
  >- (Cases_on ‘sh1’ >> gvs[sub_shape_def, cpr_merge_def]
      >- (Cases_on ‘sh2’ >> gvs[sub_shape_def, cpr_merge_def]
         )
      >- (Cases_on ‘sh2’ >> gvs[sub_shape_def, cpr_merge_def]
          >> every_case_tac >> gvs[sub_shape_def, cpr_merge_def]
          >> last_x_assum $ dxrule_then assume_tac
          >> rw[]
         )
     )
  >- (Cases_on ‘sh2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘sh1’ >> gvs[sub_shape_def, cpr_merge_def]
      >> every_case_tac >> gvs[sub_shape_def, cpr_merge_def]
      >> last_x_assum $ dxrule_then assume_tac
      >> rw[]
     )
  >- (Cases_on ‘sh1’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘sh2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> every_case_tac >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘sh2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘sh1’ >> gvs[sub_shape_def, cpr_merge_def]
      >> every_case_tac >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘l1’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘l1’ >> gvs[sub_shape_def, cpr_merge_def]
     )
  >- (Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
      >> Cases_on ‘l1’ >> gvs[sub_shape_def, cpr_merge_def]
      >> metis_tac[]
     )
  >> Cases_on ‘l1’ >> gvs[sub_shape_def, cpr_merge_def]
  >> Cases_on ‘l2’ >> gvs[sub_shape_def, cpr_merge_def]
  >> metis_tac[]
QED

Theorem sub_shape_field_shape_ok:
  (∀e s. sub_shape s (field_shape e) ⇒ exp_shape_ok s e) ∧
  (∀ls l. sub_shape_list l (field_shape_list ls) ⇒ exp_shape_ok_list l ls)
Proof
  Induct >> rw[sub_shape_def, field_shape_def, exp_shape_ok_def]
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
      >> Cases_on ‘o'’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
      >> Cases_on ‘b’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
      >> first_assum $ drule_then assume_tac
      >> drule exp_shape_ok_list_length_eq
      >> rw[]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘s’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘l’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
     )
  >> Cases_on ‘l’ >> gvs[sub_shape_def, field_shape_def, exp_shape_ok_def]
QED

Theorem shape_and_tail_tail_ok:
  ∀e f sh cs m sh'.
    shape_and_tail f e = (sh,cs) ∧
    sub_shape sh' sh ∧ flex_free sh' ∧ split_ok sh' ∧
    (∀d. MEM d cs ⇒ ∃dwk. lookup d m = SOME (sh',dwk)) ⇒
    tail_ok m f sh' e
Proof
  Induct_on ‘e’ >> rw[shape_and_tail_def, sub_shape_def, tail_ok_def, exp_shape_ok_def]
  >- (Cases_on ‘sh'’ >> gvs[sub_shape_def, tail_ok_def, exp_shape_ok_def]
     )
  >- (Cases_on ‘shape_and_tail f e'’ >> gvs[]
      >> Cases_on ‘shape_and_tail f e''’ >> gvs[]
      >> first_x_assum $ irule
      >> rw[]
      >> drule $ cj 1 sub_shape_cpr_merge
      >> rw[]
     )
  >- (Cases_on ‘shape_and_tail f e'’ >> gvs[]
      >> Cases_on ‘shape_and_tail f e''’ >> gvs[]
      >> first_x_assum $ irule
      >> rw[]
      >> drule $ cj 1 sub_shape_cpr_merge
      >> rw[]
     )
  >- (every_case_tac >> gvs[]
      >> Cases_on ‘sh'’ >> gvs[sub_shape_def, split_ok_def, shape_width_def, tail_ok_def]
     )
  >- (every_case_tac >> gvs[]
      >> Cases_on ‘sh'’ >> gvs[sub_shape_def, split_ok_def, shape_width_def, tail_ok_def]
     )
  >- (Cases_on ‘o'’ >> gvs[sub_shape_def, split_ok_def, shape_width_def, field_shape_def, shape_width_def]
      >> Cases_on ‘sh'’ >> gvs[sub_shape_def, shape_width_def, exp_shape_ok_def]
      >> Cases_on ‘b’ >> gvs[sub_shape_def, field_shape_def]
      >> conj_asm2_tac
      >- (drule exp_shape_ok_list_length_eq
          >> rw[]
         )
      >> irule $ cj 2 sub_shape_field_shape_ok
      >> rw[]
     )
  >> Cases_on ‘sh'’ >> gvs[sub_shape_def, split_ok_def, shape_width_def]
QED

Theorem tail_ok_Leaf:
  (∀e (m:(cpr_shape # 'a) sptree$num_map) f. tail_ok m f Leaf e) ∧
  (∀oe.
     case oe of
       SOME e => T
     | NONE => T) ∧
  (∀l (m:(cpr_shape # 'a) sptree$num_map) f. EVERY (tail_ok m f Leaf) l)
Proof
  Induct >> rw[tail_ok_def, exp_shape_ok_def]
  >> Cases_on ‘o'’ >> gvs[tail_ok_def]
QED

Theorem tail_shape_cases:
  ∀m cs.
    map_ok m ⇒
    (tail_shape m cs = Flexible ∧ cs = []) ∨
    tail_shape m cs = Leaf ∨
    (split_ok (tail_shape m cs) ∧ flex_free (tail_shape m cs) ∧
     ∀d. MEM d cs ⇒ ∃dwk. lookup d m = SOME (tail_shape m cs,dwk))
Proof
  rw[]
  >> Cases_on ‘tail_shape m cs = Flexible’
  >- (drule_all_then assume_tac tail_shape_Flexible >> rw[]
     )
  >> Cases_on ‘tail_shape m cs = Leaf’ >- rw[]
  >> ntac 2 disj2_tac
  >> drule_then assume_tac tail_shape_lookup
  >> pop_assum $ qspec_then ‘cs’ assume_tac >> gvs[]
  >> ‘cs ≠ []’ by (Cases_on ‘cs’ >> gvs[tail_shape_def])
  >> Cases_on ‘cs’ >> gvs[]
  >> first_assum $ qspec_then ‘h’ mp_tac
  >> rw[] >> gvs[map_ok_def]
  >> metis_tac[]
QED

Theorem return_shape_tail_ok:
  ∀m f body sh.
    map_ok m ∧ return_shape m f body = sh ∧ split_ok sh ⇒
    tail_ok m f sh body ∧ flex_free sh
Proof
  rpt gen_tac >> strip_tac
  >> gvs[return_shape_def]
  >> Cases_on ‘shape_and_tail f body’ >> gvs[]
  >> rename1 ‘shape_and_tail f body = (own,cs)’
  >> drule_then assume_tac shape_and_tail_wf
  >> drule_all_then strip_assume_tac tail_shape_cases
  >> Cases_on ‘tail_shape m cs’ >> fs[]
  >- (Cases_on ‘own’ >> gvs[flex_free_def, tail_ok_Leaf]
     )
  >- gvs[flex_free_def, tail_ok_Leaf]
  >- (Cases_on ‘own’ >> gvs[flex_free_def, tail_ok_Leaf, sub_shape_def]
      >> full_case_tac >> gvs[flex_free_def, tail_ok_Leaf, sub_shape_def]
      >> first_x_assum $ qspec_then ‘cs’ assume_tac >> gvs[flex_free_def, tail_ok_def]
      >> irule shape_and_tail_tail_ok >> gvs[flex_free_def, tail_ok_Leaf, sub_shape_def]
     )
  >- (gvs[flex_free_def, tail_ok_Leaf, sub_shape_def]
      >> first_x_assum $ qspec_then ‘cs’ assume_tac >> gvs[flex_free_def, tail_ok_def]
      >> irule shape_and_tail_tail_ok >> gvs[flex_free_def, tail_ok_Leaf, sub_shape_def]
     )
  >- (first_x_assum $ qspec_then ‘cs’ assume_tac >> gvs[flex_free_def, tail_ok_def]
      >> irule shape_and_tail_tail_ok >> gvs[flex_free_def, tail_ok_Leaf, sub_shape_def, sub_shape_refl]
  )
  >> gvs[split_ok_def, shape_width_def]
QED

Definition returns_def:
  (returns n (If g e1 e2) ⇔ returns n e1 ∧ returns n e2) ∧
  (returns n (Let xs e) ⇔ returns n e) ∧
  (returns n (Tick e) ⇔ returns n e) ∧
  (returns n (LetCall r ts d args e) ⇔ returns n e) ∧
  (returns n (Raise e) ⇔ T) ∧
  (returns n (Return xs) ⇔ LENGTH xs = n) ∧
  (returns n (Call ts d args hdl) ⇔
     n = 1 ∧ case hdl of NONE => T | SOME h => returns 1 h) ∧
  (returns n e ⇔ n = 1)
End

Theorem tail_ok_returns:
  ∀m f sh e. tail_ok m f sh e ∧ split_ok sh ⇒ returns 1 e
Proof
  ho_match_mp_tac tail_ok_ind
  >> rw[tail_ok_def,returns_def]
  >- gvs[split_ok_def, shape_width_def]
  >> drule_then strip_assume_tac split_ok_ConsShape
  >> gvs[exp_shape_ok_def]
QED

Theorem worker_body_returns:
  ∀m f wk sh e.
    tail_ok m f sh e ∧ split_ok sh ⇒
    returns (shape_width sh) (worker_body m f wk sh e)
Proof
  ho_match_mp_tac worker_body_ind
  >> rw[worker_body_def,tail_ok_def,returns_def] >> gvs[]
  >~ [‘Call ts dest args hdl’]
  >- (Cases_on ‘hdl’ >> gvs[split_ok_def,shape_width_def, returns_def, tail_ok_def]
      >> rw[split_ok_def,shape_width_def, returns_def, tail_ok_def]
     )
  >~ [‘Return xs’]
  >- (drule_then strip_assume_tac split_ok_ConsShape
      >> gvs[exp_shape_ok_def]
     )
  >> gvs[returns_def]
  >> irule $ cj 1 flatten_exp_LENGTH
  >> gvs[]
QED

Theorem make_wrapper_returns:
  ∀arity wk sh. returns 1 (make_wrapper arity wk sh)
Proof
  rw[make_wrapper_def,returns_def]
  >> Cases_on ‘sh’ >> rw[rebuild_def,returns_def]
QED

Definition submap_def:
  submap m1 m2 ⇔ ∀d x. lookup d m1 = SOME x ⇒ lookup d m2 = SOME x
End

Theorem submap_refl:
  submap m m
Proof
  rw[submap_def]
QED

Theorem submap_trans:
  submap m1 m2 ∧ submap m2 m3 ⇒ submap m1 m3
Proof
  rw[submap_def]
QED

Theorem submap_insert:
  lookup q m = NONE ⇒
  submap m (insert q v m)
Proof
  rw[submap_def, lookup_insert]
  >> every_case_tac >> gvs[]
QED


Definition fun_rel_def:
  fun_rel m2 prog2 (loc,arity,e) ⇔
    case lookup loc m2 of
      NONE => MEM (loc,arity,e) prog2
    | SOME (sh,wk) =>
        ∃m'. submap m' m2 ∧ map_ok m' ∧
             return_shape m' loc e = sh ∧ split_ok sh ∧ tail_form e ∧
             MEM (loc,arity,make_wrapper arity wk sh) prog2 ∧
             MEM (wk,arity,worker_body m' loc wk sh e) prog2
End

Theorem split_fun_map_ok:
  ∀m next loc arity body wkb wrap m'.
    map_ok m ∧ split_fun m next loc arity body = SOME (wkb,wrap,m') ⇒
    ∃sh. m' = insert loc (sh,next) m ∧
         return_shape m loc body = sh ∧ split_ok sh ∧ flex_free sh ∧
         wkb = worker_body m loc next sh body ∧
         wrap = make_wrapper arity next sh ∧
         tail_ok m loc sh body ∧ tail_form body ∧
         map_ok m'
Proof
  rw[split_fun_def]
  >> drule_all_then strip_assume_tac $ SRULE [Once EQ_SYM] return_shape_tail_ok
  >> gvs[map_ok_def,lookup_insert]
  >> strip_tac
  >> Cases_on ‘d = loc’ >> gvs[]
  >> rpt gen_tac
  >> disch_tac
  >> last_x_assum $ irule
  >> metis_tac[]
QED

(* CPR workers are named in namespace 4 of bvl_to_bvi. *)
Definition in_ns_4_def:
  in_ns_4 n ⇔ n MOD bvl_to_bvi_namespaces = 4
End

Definition free_names_def:
  free_names n (name: num) ⇔ ∀k. n + bvl_to_bvi_namespaces * k ≠ name
End

Theorem bvl_to_bvi_namespaces_pos[local]:
  0 < bvl_to_bvi_namespaces
Proof
  EVAL_TAC
QED

Theorem free_names_add[local]:
  free_names n x ⇒ ∀j. free_names (n + bvl_to_bvi_namespaces * j) x
Proof
  rw[free_names_def]
  >> first_x_assum (qspec_then ‘j + k’ mp_tac) >> simp[LEFT_ADD_DISTRIB]
QED

Theorem free_names_neq[local]:
  free_names n x ⇒ ∀j. x ≠ n + j * bvl_to_bvi_namespaces
Proof
  rw[free_names_def] >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]
QED

Theorem free_names_add_succ[local]:
  free_names n x ⇒
  free_names (n + (bvl_to_bvi_namespaces + j * bvl_to_bvi_namespaces)) x
Proof
  rw[free_names_def]
  >> first_x_assum (qspec_then ‘j + k + 1’ mp_tac) >> simp[LEFT_ADD_DISTRIB]
QED

Theorem free_names_refl_F[local,simp]:
  free_names n n ⇔ F
Proof
  simp[free_names_def] >> qexists_tac ‘0’ >> simp[]
QED

Theorem free_names_succ_F[local,simp]:
  free_names n (n + (bvl_to_bvi_namespaces + j * bvl_to_bvi_namespaces)) ⇔ F
Proof
  simp[free_names_def] >> qexists_tac ‘j + 1’ >> simp[]
QED

Theorem compile_prog_with_map_next_mono:
  ∀xs csh next n1 c1 ys.
    compile_prog_with_map csh next xs = ((n1,c1),ys) ⇒
    ∃k. n1 = next + bvl_to_bvi_namespaces * k
Proof
  Induct >> rw[compile_prog_with_map_def]
  >- (qexists_tac ‘0’ >> simp[])
  >> PairCases_on ‘h’
  >> gvs[compile_prog_with_map_def]
  >> Cases_on ‘split_fun csh next h0 h1 h2’ >> gvs[]
  >- (pairarg_tac >> gvs[] >> first_x_assum drule >> simp[])
  >> PairCases_on ‘x’ >> gvs[] >> pairarg_tac >> gvs[]
  >> first_x_assum drule >> strip_tac
  >> qexists_tac ‘k + 1’ >> simp[]
QED

Theorem compile_prog_with_map_MEM:
  ∀xs csh next n1 c1 ys e.
    compile_prog_with_map csh next xs = ((n1,c1),ys) ∧ MEM e (MAP FST ys) ⇒
    MEM e (MAP FST xs) ∨
    next ≤ e ∧ e < n1 ∧ ∃k. e = next + k * bvl_to_bvi_namespaces
Proof
  Induct >> rw[compile_prog_with_map_def]
  >> PairCases_on ‘h’
  >> gvs[compile_prog_with_map_def]
  >> Cases_on ‘split_fun csh next h0 h1 h2’ >> gvs[]
  >- (pairarg_tac >> gvs[] >> metis_tac[])
  >> PairCases_on ‘x’ >> gvs[] >> pairarg_tac >> gvs[]
  >> assume_tac bvl_to_bvi_namespaces_pos
  >> drule compile_prog_with_map_next_mono >> strip_tac
  >> gvs[]
  >> first_x_assum drule_all >> strip_tac >> gvs[]
  >> disj2_tac
  >> qmatch_goalsub_rename_tac ‘bvl_to_bvi_namespaces + j * bvl_to_bvi_namespaces = _’
  >> qexists_tac ‘j + 1’ >> simp[]
QED

Theorem compile_prog_with_map_keeps_names:
  ∀xs csh next st ys x.
    compile_prog_with_map csh next xs = (st,ys) ∧ MEM x (MAP FST xs) ⇒
    MEM x (MAP FST ys)
Proof
  Induct >> simp[compile_prog_with_map_def]
  >> rpt strip_tac >> PairCases_on ‘h’
  >> gvs[compile_prog_with_map_def, AllCaseEqs(), UNCURRY]
  >> metis_tac[PAIR]
QED

Theorem compile_prog_with_map_HD:
  ∀xs csh next st ys.
    compile_prog_with_map csh next xs = (st,ys) ∧ xs ≠ [] ⇒
    ys ≠ [] ∧ FST (HD ys) = FST (HD xs)
Proof
  Cases >> simp[] >> PairCases_on ‘h’
  >> rw[compile_prog_with_map_def]
  >> gvs[AllCaseEqs(), UNCURRY]
QED

Theorem compile_prog_with_map_ALL_DISTINCT:
  ∀xs csh next n1 c1 ys.
    compile_prog_with_map csh next xs = ((n1,c1),ys) ∧
    ALL_DISTINCT (MAP FST xs) ∧ EVERY (free_names next o FST) xs ⇒
    ALL_DISTINCT (MAP FST ys) ∧ EVERY (free_names n1 o FST) ys
Proof
  Induct >> simp[compile_prog_with_map_def]
  >> rpt gen_tac >> PairCases_on ‘h’
  >> simp[compile_prog_with_map_def]
  >> Cases_on ‘split_fun csh next h0 h1 h2’ >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[]
      >> first_x_assum drule_all >> strip_tac
      >> drule compile_prog_with_map_next_mono >> strip_tac >> gvs[]
      >> conj_tac
      >- (strip_tac >> drule_all compile_prog_with_map_MEM >> strip_tac >> gvs[]
          >> metis_tac[free_names_neq])
      >> metis_tac[free_names_add, MULT_COMM])
  >> PairCases_on ‘x’ >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> ‘EVERY (free_names (next + bvl_to_bvi_namespaces) o FST) xs’
    by (gvs[EVERY_MEM] >> metis_tac[free_names_add, MULT_RIGHT_1])
  >> first_x_assum drule_all >> strip_tac
  >> drule compile_prog_with_map_next_mono >> strip_tac >> gvs[]
  >> assume_tac bvl_to_bvi_namespaces_pos
  >> rpt conj_tac
  >- (strip_tac >> gvs[])
  >- (strip_tac >> drule_all compile_prog_with_map_MEM >> strip_tac >> gvs[])
  >- (strip_tac >> drule_all compile_prog_with_map_MEM >> strip_tac
      >> gvs[EVERY_MEM, MEM_MAP]
      >> rename1 ‘MEM y0 xs’
      >> qpat_x_assum ‘∀e. MEM e xs ⇒ free_names (FST y0) _’ drule >> simp[])
  >- metis_tac[free_names_add_succ]
  >> simp[free_names_def]
QED

Theorem fun_rel_CONS:
  fun_rel m p x ⇒ fun_rel m (y::p) x
Proof
  PairCases_on ‘x’ >> rw[fun_rel_def] >> every_case_tac >> gvs[]
  >> metis_tac[]
QED

Theorem compile_prog_with_map_thm:
  ∀xs csh next n1 c1 ys.
    compile_prog_with_map csh next xs = ((n1,c1),ys) ∧
    map_ok csh ∧ ALL_DISTINCT (MAP FST xs) ∧ EVERY (free_names next o FST) xs ∧
    (∀loc. MEM loc (MAP FST xs) ⇒ lookup loc csh = NONE) ⇒
    submap csh c1 ∧ map_ok c1 ∧ EVERY (fun_rel c1 ys) xs ∧
    (∀d sh wk.
       lookup d c1 = SOME (sh,wk) ∧ lookup d csh = NONE ⇒
       MEM d (MAP FST xs) ∧ MEM wk (MAP FST ys) ∧ ¬MEM wk (MAP FST xs)) ∧
    (∀x. MEM x (MAP FST ys) ⇒
       MEM x (MAP FST xs) ∨
       ∃d sh. lookup d c1 = SOME (sh,x) ∧ lookup d csh = NONE)
Proof
  Induct >> simp[compile_prog_with_map_def]
  >- rw[submap_refl]
  >> rpt gen_tac >> PairCases_on ‘h’
  >> simp[compile_prog_with_map_def]
  >> Cases_on ‘split_fun csh next h0 h1 h2’ >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[]
      >> first_x_assum drule >> impl_tac >- metis_tac[]
      >> strip_tac >> simp[]
      >> rpt conj_tac
      >- (simp[fun_rel_def] >> Cases_on ‘lookup h0 c1’ >> simp[]
          >> rename1 ‘lookup h0 c1 = SOME p’ >> PairCases_on ‘p’ >> metis_tac[])
      >- gvs[EVERY_MEM, fun_rel_CONS]
      >- (rpt gen_tac >> strip_tac
          >> qpat_x_assum ‘∀d sh wk. _ ⇒ MEM d _ ∧ _’ drule_all >> strip_tac >> simp[]
          >> strip_tac >> gvs[]
          >> drule_all compile_prog_with_map_MEM >> strip_tac >> gvs[]
          >> metis_tac[free_names_neq])
      >> rw[] >> metis_tac[])
  >> PairCases_on ‘x’ >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> qmatch_asmsub_rename_tac ‘compile_prog_with_map _ _ xs = (_,rest)’
  >> drule_all split_fun_map_ok >> strip_tac >> gvs[]
  >> ‘EVERY (free_names (next + bvl_to_bvi_namespaces) o FST) xs’
    by (gvs[EVERY_MEM] >> metis_tac[free_names_add, MULT_RIGHT_1])
  >> ‘∀loc. MEM loc (MAP FST xs) ⇒
            lookup loc (insert h0 (return_shape csh h0 h2,next) csh) = NONE’
    by (rw[lookup_insert] >> metis_tac[])
  >> first_x_assum drule_all >> strip_tac
  >> ‘lookup h0 csh = NONE’ by metis_tac[]
  >> ‘submap csh c1’ by metis_tac[submap_trans, submap_insert]
  >> ‘lookup h0 c1 = SOME (return_shape csh h0 h2,next)’
    by gvs[submap_def, lookup_insert]
  >> simp[]
  >> rpt conj_tac
  >- (simp[fun_rel_def] >> qexists_tac ‘csh’ >> simp[submap_refl])
  >- gvs[EVERY_MEM, fun_rel_CONS]
  >- (rpt gen_tac >> strip_tac
      >> Cases_on ‘d = h0’ >> gvs[]
      >- (conj_tac
          >- (strip_tac >> gvs[])
          >> strip_tac >> gvs[EVERY_MEM, MEM_MAP]
          >> rename1 ‘MEM y0 xs’
          >> qpat_x_assum ‘∀e. MEM e xs ⇒ free_names (FST y0) _’ drule >> simp[])
      >> qpat_x_assum ‘∀d sh wk. _ ∧ lookup d (insert _ _ _) = NONE ⇒ _’
           (qspecl_then [‘d’,‘sh’,‘wk’] mp_tac)
      >> simp[lookup_insert] >> strip_tac >> simp[]
      >> strip_tac >> gvs[]
      >> drule_all compile_prog_with_map_MEM >> strip_tac >> gvs[])
  >> rpt strip_tac >> gvs[]
  >- metis_tac[]
  >> qpat_x_assum ‘∀x. MEM x (MAP FST rest) ⇒ _’ drule >> strip_tac >> gvs[]
  >> gvs[lookup_insert, AllCaseEqs()] >> metis_tac[]
QED

Theorem code_rel_of_fun_rel:
  ∀m2 prog prog2.
    ALL_DISTINCT (MAP FST prog) ∧ ALL_DISTINCT (MAP FST prog2) ∧
    EVERY (fun_rel m2 prog2) prog ⇒
    ∀d arity body.
      lookup d (fromAList prog) = SOME (arity,body) ⇒
      case lookup d m2 of
        NONE => lookup d (fromAList prog2) = SOME (arity,body)
      | SOME (sh,wk) =>
          ∃m'. submap m' m2 ∧ map_ok m' ∧
               return_shape m' d body = sh ∧ split_ok sh ∧
               tail_form body ∧
               lookup d (fromAList prog2) =
                 SOME (arity,make_wrapper arity wk sh) ∧
               lookup wk (fromAList prog2) =
                 SOME (arity,worker_body m' d wk sh body)
Proof
  rpt strip_tac
  >> gvs[lookup_fromAList]
  >> drule_then assume_tac ALOOKUP_MEM >> gvs[EVERY_MEM]
  >> first_assum $ drule_then $ assume_tac o SRULE [fun_rel_def]
  >> Cases_on ‘lookup d m2’ >> gvs[]
  >- (drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM
      >> gvs[]
     )
  >> Cases_on ‘x’ >> gvs[]
  >> first_assum $ irule_at Any
  >> gvs[ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem no_ret_list_APPEND:
  ∀a b. no_ret_list a ∧ no_ret_list b ⇒ no_ret_list (a ++ b)
Proof
  Induct_on ‘a’ >> rw[no_ret_def]
QED

Theorem no_ret_flatten_exp:
  (∀sh e. no_ret e ⇒ no_ret_list (flatten_exp sh e)) ∧
  (∀shs xs. no_ret_list xs ⇒ no_ret_list (flatten_list shs xs))
Proof
  Induct >> rw[flatten_exp_def, no_ret_def]
  >- (every_case_tac >> gvs[no_ret_def]
     )
  >> Cases_on ‘xs’ >> gvs[flatten_exp_def, no_ret_def, no_ret_list_APPEND]
QED

Theorem no_ret_rebuild:
  (∀sh i. no_ret (rebuild i sh)) ∧
  (∀shs i. no_ret_list (rebuild_list i shs))
Proof
  Induct >> rw[rebuild_def, no_ret_def]
QED

Theorem tail_form_rebuild:
  (∀sh i. tail_form (rebuild i sh)) ∧
  (∀shs. EVERY (λsh. ∀i. tail_form (rebuild i sh)) shs)
Proof
  Induct >> rw[tail_form_def, rebuild_def, no_ret_def, no_ret_rebuild]
QED

Theorem no_ret_list_GENLIST_Var:
  ∀n. no_ret_list (GENLIST Var n)
Proof
  Induct >> rw[no_ret_def, GENLIST, SNOC_APPEND, no_ret_list_APPEND]
QED

Theorem tail_form_make_wrapper:
  (∀sh arity wk. tail_form (make_wrapper arity wk sh)) ∧
  (∀shs. EVERY (λsh. ∀arity wk. tail_form (make_wrapper arity wk sh)) shs)
Proof
  Induct >> rw[make_wrapper_def, tail_form_def, no_ret_def, tail_form_rebuild, no_ret_list_GENLIST_Var]
QED

Theorem tail_form_worker_body:
  ∀m f wk sh e. tail_form e ⇒ tail_form (worker_body m f wk sh e)
Proof
  ho_match_mp_tac worker_body_ind
  >> rw[worker_body_def, tail_form_def]
  >~ [‘Call ts dest args hdl’]
  >- (Cases_on ‘hdl’ >> gvs[tail_form_def, no_ret_def]
      >> Cases_on ‘dest’ >> gvs[tail_form_def, no_ret_def]
      >> IF_CASES_TAC
      >> gvs[tail_form_def, no_ret_def, no_ret_list_GENLIST_Var]
      >> every_case_tac
      >> gvs[tail_form_def, no_ret_def, EVERY_GENLIST, no_ret_list_GENLIST_Var]
     )
  >> drule_then assume_tac $ cj 1 no_ret_flatten_exp
  >> rw[]
QED

Theorem do_app_no_Ret:
  ∀op vs (s:('c,'ffi) bviSem$state) e.
    do_app op vs s = Rerr e ⇒ ∀ws. e ≠ Rraise (Ret ws)
Proof
  rw[do_app_def, do_install_def]
  >> every_case_tac >> gvs[]
  >> Cases_on ‘s.compile_oracle 0’ >> gvs[]
  >> every_case_tac >> gvs[]
QED

Theorem evaluate_no_Ret:
  ∀xs env (s:('c,'ffi) bviSem$state) res t.
    evaluate (xs,env,s) = (res,t) ∧ no_ret_list xs ⇒
    ∀vs. res ≠ Rerr (Rraise (Ret vs))
Proof
  recInduct evaluate_ind
  >> rw[evaluate_def] >> gvs[no_ret_def]
  >> every_case_tac >> gvs[]
  >> imp_res_tac do_app_no_Ret >> gvs[]
QED

Theorem evaluate_tail_no_Ret:
  ∀e env (s:('c,'ffi) bviSem$state) res t m f sh.
    tail_form e ∧ tail_ok m f sh e ∧ split_ok sh ∧
    evaluate ([e],env,s) = (res,t) ⇒
    ∀vs. res ≠ Rerr (Rraise (Ret vs))
Proof
  Induct_on ‘e’
  >> rw[evaluate_def, tail_form_def, tail_ok_def] >> gvs[no_ret_def]
  >> every_case_tac >> gvs[]
  >> imp_res_tac evaluate_no_Ret >> gvs[no_ret_def]
  >> imp_res_tac do_app_no_Ret >> gvs[]
  >> imp_res_tac split_ok_ConsShape >> gvs[exp_shape_ok_def]
  >- (first_x_assum $ drule_then assume_tac
      >> pop_assum irule
      >> rw[split_ok_def]
      >> metis_tac[]
     )
  >- (last_x_assum $ drule_then assume_tac
      >> pop_assum irule
      >> rw[split_ok_def]
      >> metis_tac[]
     )
  >- (last_x_assum $ drule_then assume_tac
      >> pop_assum irule
      >> rw[split_ok_def]
      >> metis_tac[]
     )
  >- (last_x_assum $ drule_then assume_tac
      >> pop_assum irule
      >> rw[split_ok_def]
      >> metis_tac[]
     )
  >- (last_x_assum $ drule_then assume_tac
      >> pop_assum irule
      >> rw[split_ok_def]
      >> metis_tac[]
     )
QED

Theorem evaluate_genlist_prefix:
  ∀n vs env (s:('c,'ffi) bviSem$state).
    n ≤ LENGTH vs ⇒
    evaluate (GENLIST Var n, vs ++ env, s) = (Rval (TAKE n vs),s)
Proof
  rw[]
  >> subgoal ‘evaluate (GENLIST (λi. Var (i + 0)) n, vs ++ env, s) =
              (Rval (TAKE n (DROP 0 (vs ++ env))),s)’
  >- (irule evaluate_genlist_vars >> rw[])
  >> pop_assum $ assume_tac o SRULE []
  >> pop_assum $ assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)
  >> gvs[TAKE_APPEND1]
QED

Theorem evaluate_TailCall:
  ∀w ticks d xs env (s:('c,'ffi) bviSem$state) vs s1 args cbody rvs t.
    evaluate (xs,env,s) = (Rval vs,s1) ∧
    find_code (SOME d) vs s1.code = SOME (args,cbody) ∧
    ¬(s1.clock < ticks + 1) ∧ LENGTH rvs = w ∧
    evaluate ([cbody],args,dec_clock (ticks + 1) s1) =
      (Rerr (Rraise (Ret rvs)),t) ⇒
    evaluate ([TailCall w ticks d xs],env,s) = (Rerr (Rraise (Ret rvs)),t)
Proof
  rw[evaluate_def]
  >> gvs[evaluate_genlist_prefix, TAKE_LENGTH_ID_rwt]
QED

Definition code_rel_def:
  code_rel m c1 c2 ⇔
    map_ok m ∧
    (∀d arity body.
       lookup d c1 = SOME (arity,body) ⇒
       case lookup d m of
         NONE => lookup d c2 = SOME (arity,body)
       | SOME (sh,wk) =>
           ∃m'. submap m' m ∧ map_ok m' ∧
                return_shape m' d body = sh ∧ split_ok sh ∧
                lookup d c2 = SOME (arity,make_wrapper arity wk sh) ∧
                lookup wk c2 = SOME (arity,worker_body m' d wk sh body) ∧
                tail_form body) ∧
    (∀d. d ∈ domain c2 ⇒ d ∈ domain c1 ∨ ∃f fsh. lookup f m = SOME (fsh,d)) ∧
    (∀d sh wk. lookup d m = SOME (sh,wk) ⇒ d ∈ domain c1 ∧ wk ∉ domain c1)
End

Theorem code_rel_find_code:
  code_rel m c1 c2 ∧ find_code (SOME f) args c1 = SOME (a, e) ∧ lookup f m = NONE
  ⇒ find_code (SOME f) args c2 = SOME (a, e)
Proof
  rw[code_rel_def, bvlSemTheory.find_code_def]
  >> Cases_on ‘lookup f c1’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> Cases_on ‘lookup f m’ >> gvs[]
QED

Theorem code_rel_find_code_NONE:
  ∀m c1 c2 f args a e.
    code_rel m c1 c2 ∧ find_code (SOME f) args c1 = SOME (a,e) ∧
    lookup f m = NONE ⇒
    find_code (SOME f) args c2 = SOME (a,e)
Proof
  rw[code_rel_def, bvlSemTheory.find_code_def]
  >> Cases_on ‘lookup f c1’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> Cases_on ‘lookup f m’ >> gvs[]
QED

Theorem code_rel_find_code_SOME:
  ∀m c1 c2 f args a body sh wk.
    code_rel m c1 c2 ∧ find_code (SOME f) args c1 = SOME (a,body) ∧
    lookup f m = SOME (sh,wk) ⇒
    find_code (SOME f) args c2 = SOME (a,make_wrapper (LENGTH a) wk sh) ∧
    split_ok sh ∧ flex_free sh ∧ tail_form body ∧ tail_ok m f sh body ∧
    ∃m'. submap m' m ∧
         find_code (SOME wk) args c2 = SOME (a,worker_body m' f wk sh body)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[code_rel_def, bvlSemTheory.find_code_def]
  >> Cases_on ‘lookup f c2’ >> gvs[]
  >- (Cases_on ‘lookup f c1’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> last_x_assum $ drule_then assume_tac
      >> gvs[]
     )
  >> Cases_on ‘lookup f c1’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> Cases_on ‘x'’ >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[]
  >> rev_drule_all_then assume_tac (SRULE [Once EQ_SYM] return_shape_tail_ok)
  >> gvs[]
  >> irule_at Any tail_ok_submap
  >> qexistsl [‘m'’, ‘m'’]
  >> gvs[submap_def]
QED

Theorem no_ret_tail_form:
  no_ret e ⇒ tail_form e
Proof
  Induct_on ‘e’ using tail_form_ind >> rw[no_ret_def, tail_form_def]
QED

Theorem worker_body_submap:
  ∀m' f wk sh e m.
    submap m' m ∧ tail_ok m' f sh e ∧ split_ok sh ⇒
    worker_body m' f wk sh e = worker_body m f wk sh e
Proof
  ho_match_mp_tac worker_body_ind
  >> rw[worker_body_def, tail_ok_def]
  >> Cases_on ‘hdl’ >> gvs[worker_body_def, tail_ok_def]
  >- gvs[split_ok_def, shape_width_def]
  >> IF_CASES_TAC >> gvs[]
  >> gvs[submap_def]
  >> first_x_assum $ drule_then assume_tac
  >> gvs[]
QED

Theorem submap_map_ok:
  submap m' m ∧ map_ok m ⇒ map_ok m'
Proof
  rw[submap_def, map_ok_def]
  >- (first_x_assum $ drule_then assume_tac
      >> first_x_assum $ drule_then assume_tac
      >> rw[]
     )
  >> first_x_assum $ drule_then assume_tac
  >> first_x_assum $ drule_then assume_tac
  >> rw[]
QED

Theorem evaluate_make_wrapper_err:
  ∀arity wk sh args (s:('c,'ffi) bviSem$state) wbody err t.
    LENGTH args = arity ∧ lookup wk s.code = SOME (arity,wbody) ∧
    s.clock ≠ 0 ∧ (∀vs. err ≠ Rraise (Ret vs)) ∧
    evaluate ([wbody],args,dec_clock 1 s) = (Rerr err,t) ⇒
    evaluate ([make_wrapper arity wk sh],args,s) = (Rerr err,t)
Proof
  rw[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def]
  >> qspecl_then [‘LENGTH args’,‘args’,‘[]’,‘s’] assume_tac evaluate_genlist_prefix
  >> gvs[]
  >> Cases_on ‘err’ >> gvs[]
  >> rename1 ‘Rraise x’ >> Cases_on ‘x’ >> gvs[]
QED

Theorem code_rel_find_code_lookup:
  ∀m c1 c2 dest vs args body.
    code_rel m c1 c2 ∧ find_code dest vs c1 = SOME (args,body) ⇒
    ∃d.
      lookup d c1 = SOME (LENGTH args,body) ∧
      case lookup d m of
        NONE => find_code dest vs c2 = SOME (args,body)
      | SOME (sh,wk) =>
          find_code dest vs c2 = SOME (args,make_wrapper (LENGTH args) wk sh) ∧
          split_ok sh ∧ flex_free sh ∧ tail_form body ∧ tail_ok m d sh body ∧
          lookup wk c2 = SOME (LENGTH args,worker_body m d wk sh body)
Proof
  rw[bvlSemTheory.find_code_def]
  >> reverse $ Cases_on ‘dest’ >> gvs[bvlSemTheory.find_code_def]
  >- (Cases_on ‘lookup x c1’ >> gvs[]
      >> Cases_on ‘x'’ >> gvs[]
      >> qexists ‘x’ >> gvs[]
      >> qpat_x_assum ‘code_rel _ _ _’ $ assume_tac o SRULE [code_rel_def]
      >> gvs[]
      >> first_assum $ drule_then assume_tac
      >> Cases_on ‘lookup x m’ >> gvs[]
      >> Cases_on ‘x'’ >> gvs[]
      >> rev_drule_all_then assume_tac $ SRULE [Once EQ_SYM] return_shape_tail_ok
      >> gvs[]
      >> conj_tac
      >- (irule tail_ok_submap >> gvs[submap_def] >> metis_tac[]
         )
      >> irule worker_body_submap
      >> gvs[])
  >> Cases_on ‘vs = []’ >> gvs[]
  >> Cases_on ‘LAST vs’ >> gvs[]
  >> rename1 ‘CodePtr loc’
  >> Cases_on ‘lookup loc c1’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> qexists ‘loc’
  >> ‘LENGTH (FRONT vs) = q’ by gvs[LENGTH_FRONT]
  >> gvs[]
  >> qpat_x_assum ‘code_rel _ _ _’ $ assume_tac o SRULE [code_rel_def]
  >> gvs[]
  >> first_assum $ drule_then assume_tac
  >> Cases_on ‘lookup loc m’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> rev_drule_all_then assume_tac $ SRULE [Once EQ_SYM] return_shape_tail_ok
  >> gvs[]
  >> conj_tac
  >- (irule tail_ok_submap >> gvs[submap_def] >> metis_tac[]
     )
  >> irule worker_body_submap
  >> gvs[]
QED

Theorem code_rel_find_code_SOME_dest:
  ∀m c1 c2 d vs args body.
    code_rel m c1 c2 ∧ find_code (SOME d) vs c1 = SOME (args,body) ⇒
    args = vs ∧ lookup d c1 = SOME (LENGTH args,body) ∧
    case lookup d m of
      NONE => find_code (SOME d) vs c2 = SOME (args,body)
    | SOME (sh,wk) =>
        find_code (SOME d) vs c2 = SOME (args,make_wrapper (LENGTH args) wk sh) ∧
        split_ok sh ∧ flex_free sh ∧ tail_form body ∧ tail_ok m d sh body ∧
        lookup wk c2 = SOME (LENGTH args,worker_body m d wk sh body)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[bvlSemTheory.find_code_def, AllCaseEqs()]
  >> qpat_x_assum ‘code_rel _ _ _’ $ assume_tac o SRULE [code_rel_def]
  >> gvs[]
  >> first_assum $ drule_then assume_tac
  >> Cases_on ‘lookup d m’ >> gvs[bvlSemTheory.find_code_def]
  >> rename1 ‘lookup d m = SOME x’ >> PairCases_on ‘x’ >> gvs[]
  >> drule_all_then strip_assume_tac
                    (SRULE [Once EQ_SYM] return_shape_tail_ok)
  >> gvs[]
  >> irule_at Any tail_ok_submap
  >> qexists ‘m'’ >> gvs[]
  >> conj_tac
  >- gvs[submap_def]
  >> irule worker_body_submap
  >> gvs[]
QED

Theorem code_rel_find_code_NONE_exists:
  ∀m c1 c2 vs args body.
    code_rel m c1 c2 ∧ find_code NONE vs c1 = SOME (args,body) ⇒
    ∃d.
      vs ≠ [] ∧ LAST vs = CodePtr d ∧ args = FRONT vs ∧
      lookup d c1 = SOME (LENGTH args,body) ∧
      case lookup d m of
        NONE => find_code NONE vs c2 = SOME (args,body)
      | SOME (sh,wk) =>
          find_code NONE vs c2 = SOME (args,make_wrapper (LENGTH args) wk sh) ∧
          split_ok sh ∧ flex_free sh ∧ tail_form body ∧ tail_ok m d sh body ∧
          lookup wk c2 = SOME (LENGTH args,worker_body m d wk sh body)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[bvlSemTheory.find_code_def, AllCaseEqs()]
  >> ‘LENGTH (FRONT vs) = LENGTH vs − 1’ by gvs[LENGTH_FRONT]
  >> gvs[]
  >> qpat_x_assum ‘code_rel _ _ _’ $ assume_tac o SRULE [code_rel_def]
  >> gvs[]
  >> first_assum $ drule_then assume_tac
  >> Cases_on ‘lookup loc m’ >> gvs[bvlSemTheory.find_code_def]
  >> PairCases_on ‘x’ >> gvs[]
  >> drule_all_then strip_assume_tac
                    (SRULE [Once EQ_SYM] return_shape_tail_ok)
  >> gvs[]
  >> irule_at Any tail_ok_submap
  >> qexists ‘m'’ >> gvs[]
  >> conj_tac
  >- gvs[submap_def]
  >> irule worker_body_submap
  >> gvs[]
QED

Theorem code_rel_domain:
  code_rel m c1 c2 ⇒ domain c1 ⊆ domain c2
Proof
  rw[code_rel_def, SUBSET_DEF, domain_lookup]
  >> Cases_on ‘v’ >> gvs[]
  >> first_x_assum $ drule_then assume_tac
  >> Cases_on ‘lookup x m’ >> gvs[]
  >> Cases_on ‘x'’ >> gvs[]
QED

Theorem evaluate_TailCall_err:
  ∀w ticks d xs env (s:('c,'ffi) bviSem$state) vs s1 args cbody err t.
    evaluate (xs,env,s) = (Rval vs,s1) ∧
    find_code (SOME d) vs s1.code = SOME (args,cbody) ∧
    ¬(s1.clock < ticks + 1) ∧
    evaluate ([cbody],args,dec_clock (ticks + 1) s1) = (Rerr err,t) ∧
    (∀rvs. err ≠ Rraise (Ret rvs)) ⇒
    evaluate ([TailCall w ticks d xs],env,s) = (Rerr err,t)
Proof
  rw[evaluate_def]
  >> Cases_on ‘err’ >> gvs[]
  >> rename1 ‘Rraise x’ >> Cases_on ‘x’ >> gvs[]
QED

(* The condition on each program chunk given to CPR. *)
Definition input_condition_def:
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
    ALL_DISTINCT (MAP FST prog) ∧
    EVERY ($~ o in_ns_4 o FST) (FILTER ((<=) bvl_num_stubs o FST) prog) ∧
    bvl_num_stubs ≤ next ∧ in_ns_4 next
End

(* [m] maps each split function to its shape and worker. The source
   oracle carries CPR's state [(next, map)] for each chunk. *)
Definition state_rel_def:
  state_rel m (s:((num # (cpr_shape # num) num_map) # 'c,'ffi) bviSem$state)
    (t:('c,'ffi) bviSem$state) ⇔
    code_rel m s.code t.code ∧
    t.refs = s.refs ∧ t.clock = s.clock ∧ t.global = s.global ∧ t.ffi = s.ffi ∧
    t.compile_oracle = state_co (compile_prog T) s.compile_oracle ∧
    s.compile = state_cc (compile_prog T) t.compile ∧
    (∀n. input_condition (FST (FST (FST (s.compile_oracle n))))
           (SND (s.compile_oracle n))) ∧
    submap (SND (FST (FST (s.compile_oracle 0)))) m ∧
    (∀n. n ∈ domain t.code ∧ in_ns_4 n ⇒
         n < FST (FST (FST (s.compile_oracle 0)))) ∧
    (∀n. n ∈ domain s.code ∧ bvl_num_stubs ≤ n ⇒ ¬in_ns_4 n) ∧
    (∀d sh wk. lookup d m = SOME (sh,wk) ⇒ in_ns_4 wk ∧ bvl_num_stubs ≤ wk)
End

Theorem state_rel_with_clock:
  state_rel m s t ⇒ state_rel m (s with clock := k) (t with clock := k)
Proof
  rw[state_rel_def]
QED

Theorem state_rel_dec_clock:
  state_rel m s t ⇒ state_rel m (dec_clock n s) (dec_clock n t)
Proof
  rw[dec_clock_def]
  >> ‘t.clock = s.clock’ by gvs[state_rel_def]
  >> simp[state_rel_with_clock]
QED

Theorem evaluate_make_wrapper:
  lookup wk (t:('c,'ffi) bviSem$state).code = SOME (LENGTH args,wbody) ∧
  evaluate ([wbody],args,t) = (Rerr (Rraise (Ret (flat_vals sh v))),t1) ∧
  v_shape sh v ⇒
  evaluate ([make_wrapper (LENGTH args) wk sh],args,inc_clock 1 t) =
    (Rval [v],t1)
Proof
  rw[make_wrapper_def, evaluate_def]
  >> qspecl_then [‘LENGTH args’,‘args’,‘[]’,‘inc_clock 1 t’] mp_tac
       evaluate_genlist_prefix
  >> simp[] >> disch_then kall_tac
  >> simp[bvlSemTheory.find_code_def, inc_clock_def, dec_clock_def]
  >> drule_then assume_tac (cj 1 flat_vals_LENGTH) >> simp[]
  >> irule (cj 1 evaluate_rebuild)
  >> qpat_x_assum ‘LENGTH _ = _’ (assume_tac o SYM)
  >> simp[TAKE_LENGTH_APPEND]
QED

Theorem evaluate_make_wrapper_Rerr:
  lookup wk (t:('c,'ffi) bviSem$state).code = SOME (LENGTH args,wbody) ∧
  evaluate ([wbody],args,t) = (Rerr err,t1) ∧ (∀vs. err ≠ Rraise (Ret vs)) ⇒
  evaluate ([make_wrapper (LENGTH args) wk sh],args,inc_clock 1 t) =
    (Rerr err,t1)
Proof
  rw[make_wrapper_def, evaluate_def]
  >> qspecl_then [‘LENGTH args’,‘args’,‘[]’,‘inc_clock 1 t’] mp_tac
       evaluate_genlist_prefix
  >> simp[] >> disch_then kall_tac
  >> simp[bvlSemTheory.find_code_def, inc_clock_def, dec_clock_def]
  >> Cases_on ‘err’ >> simp[]
  >> rename1 ‘Rraise x’ >> Cases_on ‘x’ >> gvs[]
QED

Theorem in_ns_4_add[local]:
  in_ns_4 (n + k * bvl_to_bvi_namespaces) ⇔ in_ns_4 n
Proof
  assume_tac bvl_to_bvi_namespaces_pos
  >> ‘n + k * bvl_to_bvi_namespaces = k * bvl_to_bvi_namespaces + n’ by simp[]
  >> pop_assum SUBST1_TAC
  >> simp[in_ns_4_def, MOD_TIMES]
QED

(* One CPR chunk extends related code tables to related code tables. *)
Theorem code_rel_compile:
  code_rel m c1 c2 ∧ submap csh m ∧
  compile_prog_with_map csh next progs = ((next1,csh1),progs1) ∧
  input_condition next progs ∧ DISJOINT (domain c1) (set (MAP FST progs)) ∧
  (∀n. n ∈ domain c2 ∧ in_ns_4 n ⇒ n < next) ∧
  (∀n. n ∈ domain c1 ∧ bvl_num_stubs ≤ n ⇒ ¬in_ns_4 n) ∧
  (∀d sh wk. lookup d m = SOME (sh,wk) ⇒ in_ns_4 wk ∧ bvl_num_stubs ≤ wk) ⇒
  DISJOINT (domain c2) (set (MAP FST progs1)) ∧ ALL_DISTINCT (MAP FST progs1) ∧
  submap m (union m csh1) ∧ submap csh1 (union m csh1) ∧
  code_rel (union m csh1) (union c1 (fromAList progs))
    (union c2 (fromAList progs1)) ∧
  (∀d sh wk. lookup d (union m csh1) = SOME (sh,wk) ⇒
     in_ns_4 wk ∧ bvl_num_stubs ≤ wk) ∧
  (∀n. MEM n (MAP FST progs1) ∧ in_ns_4 n ⇒ n < next1)
Proof
  strip_tac
  >> ‘map_ok m ∧ map_ok csh’ by metis_tac[code_rel_def, submap_map_ok]
  >> ‘∀loc. MEM loc (MAP FST progs) ⇒ lookup loc m = NONE ∧ lookup loc csh = NONE’
    by (rpt gen_tac >> strip_tac
        >> ‘lookup loc m = NONE’
          by (Cases_on ‘lookup loc m’ >> simp[] >> rename1 ‘SOME q’ >> PairCases_on ‘q’
              >> gvs[code_rel_def, IN_DISJOINT] >> metis_tac[])
        >> gvs[submap_def] >> Cases_on ‘lookup loc csh’ >> gvs[]
        >> first_x_assum drule >> simp[])
  >> ‘ALL_DISTINCT (MAP FST progs) ∧ EVERY (free_names next o FST) progs ∧
      bvl_num_stubs ≤ next ∧ in_ns_4 next ∧
      ∀x. MEM x (MAP FST progs) ∧ bvl_num_stubs ≤ x ⇒ ¬in_ns_4 x’
    by (gvs[input_condition_def, EVERY_MEM, MEM_FILTER, MEM_MAP, PULL_EXISTS]
        >> metis_tac[])
  >> drule compile_prog_with_map_thm >> impl_tac >- metis_tac[]
  >> strip_tac
  >> drule_all compile_prog_with_map_ALL_DISTINCT >> strip_tac
  >> drule compile_prog_with_map_next_mono >> strip_tac
  >> ‘∀x. MEM x (MAP FST progs1) ∧ ¬MEM x (MAP FST progs) ⇒
          next ≤ x ∧ x < next1 ∧ in_ns_4 x’
    by (rpt gen_tac >> strip_tac >> drule_all compile_prog_with_map_MEM
        >> strip_tac >> gvs[in_ns_4_add])
  >> ‘submap m (union m csh1)’ by rw[submap_def, lookup_union]
  >> subgoal ‘submap csh1 (union m csh1)’
  >- (
    simp[submap_def, lookup_union] >> rpt strip_tac
    >> Cases_on ‘lookup d m’ >> simp[]
    >> rename1 ‘lookup d m = SOME y’
    >> Cases_on ‘lookup d csh’
    >- (PairCases_on ‘x’
        >> qpat_x_assum ‘∀d sh wk. lookup d csh1 = SOME (sh,wk) ∧ _ ⇒ _’
             (qspecl_then [‘d’,‘x0’,‘x1’] mp_tac)
        >> simp[] >> strip_tac >> res_tac >> gvs[])
    >> gvs[submap_def] >> res_tac >> gvs[])
  >> subgoal ‘DISJOINT (domain c2) (set (MAP FST progs1))’
  >- (
    simp[IN_DISJOINT] >> rpt strip_tac >> CCONTR_TAC >> fs[]
    >> Cases_on ‘MEM x (MAP FST progs)’
    >- (
      ‘x ∉ domain c1’ by (gvs[IN_DISJOINT] >> metis_tac[])
      >> qpat_x_assum ‘code_rel m c1 c2’ (strip_assume_tac o SRULE[code_rel_def])
      >> ‘∃f fsh. lookup f m = SOME (fsh,x)’ by metis_tac[]
      >> ‘in_ns_4 x ∧ bvl_num_stubs ≤ x’ by metis_tac[]
      >> metis_tac[])
    >> ‘next ≤ x ∧ in_ns_4 x’ by metis_tac[]
    >> ‘x < next’ by metis_tac[]
    >> simp[])
  >> simp[]
  >> rpt conj_tac
  >- (
    ‘∀x a b. MEM (x,a,b) progs1 ⇒
             lookup x (union c2 (fromAList progs1)) = SOME (a,b)’
      by (rpt strip_tac
          >> ‘x ∉ domain c2’
            by (gvs[IN_DISJOINT, MEM_MAP] >> metis_tac[FST])
          >> gvs[lookup_union, domain_lookup, lookup_fromAList]
          >> Cases_on ‘lookup x c2’ >> gvs[]
          >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[])
    >> ‘∀d. d ∈ domain c1 ⇒ lookup d (union m csh1) = lookup d m’
      by (rpt strip_tac >> simp[lookup_union]
          >> Cases_on ‘lookup d m’ >> simp[]
          >> Cases_on ‘lookup d csh1’ >> simp[]
          >> rename1 ‘lookup d csh1 = SOME q’ >> PairCases_on ‘q’
          >> Cases_on ‘lookup d csh’
          >- (‘MEM d (MAP FST progs)’ by metis_tac[]
              >> gvs[IN_DISJOINT] >> metis_tac[])
          >> gvs[submap_def] >> res_tac >> gvs[])
    >> qpat_x_assum ‘code_rel m c1 c2’ (strip_assume_tac o SRULE[code_rel_def])
    >> simp[code_rel_def]
    >> rpt conj_tac
    >- (
      gvs[map_ok_def, lookup_union, AllCaseEqs()] >> metis_tac[])
    >- (
      rpt gen_tac >> strip_tac
      >> Cases_on ‘d ∈ domain c1’
      >- (
        ‘lookup d c1 = SOME (arity,body)’ by gvs[lookup_union, domain_lookup]
        >> ‘lookup d (union m csh1) = lookup d m’ by metis_tac[]
        >> pop_assum SUBST1_TAC
        >> qpat_x_assum ‘∀d arity body. lookup d c1 = _ ⇒ _’ drule
        >> Cases_on ‘lookup d m’ >> simp[lookup_union]
        >> rename1 ‘lookup d m = SOME q’ >> PairCases_on ‘q’ >> simp[]
        >> strip_tac >> qexists_tac ‘m'’ >> simp[]
        >> metis_tac[submap_trans])
      >> ‘lookup d c1 = NONE’ by gvs[lookup_NONE_domain]
      >> ‘lookup d (fromAList progs) = SOME (arity,body)’ by gvs[lookup_union]
      >> ‘MEM (d,arity,body) progs’
        by (gvs[lookup_fromAList] >> imp_res_tac ALOOKUP_MEM)
      >> ‘MEM d (MAP FST progs)’ by (simp[MEM_MAP] >> metis_tac[FST])
      >> ‘lookup d m = NONE’ by metis_tac[]
      >> ‘lookup d (union m csh1) = lookup d csh1’ by simp[lookup_union]
      >> pop_assum SUBST1_TAC
      >> ‘fun_rel csh1 progs1 (d,arity,body)’ by gvs[EVERY_MEM]
      >> gvs[fun_rel_def]
      >> Cases_on ‘lookup d csh1’ >> gvs[]
      >> rename1 ‘lookup d csh1 = SOME q’ >> PairCases_on ‘q’ >> gvs[]
      >> qexists_tac ‘m'’ >> simp[]
      >> metis_tac[submap_trans])
    >- (
      rpt strip_tac
      >- (qpat_x_assum ‘∀d. d ∈ domain c2 ⇒ _’ drule >> strip_tac >> simp[]
          >> metis_tac[submap_def])
      >> gvs[domain_fromAList]
      >> qpat_x_assum ‘∀x. MEM x (MAP FST progs1) ⇒ _’ drule >> strip_tac >> simp[]
      >> metis_tac[submap_def])
    >- (
      simp[lookup_union, domain_fromAList] >> rpt gen_tac
      >> Cases_on ‘lookup d m’ >> simp[]
      >- (strip_tac
          >> ‘lookup d csh = NONE’
            by (Cases_on ‘lookup d csh’ >> gvs[submap_def] >> res_tac >> gvs[])
          >> ‘MEM d (MAP FST progs) ∧ MEM wk (MAP FST progs1) ∧
              ¬MEM wk (MAP FST progs)’ by metis_tac[]
          >> ‘next ≤ wk ∧ in_ns_4 wk’ by metis_tac[]
          >> simp[] >> strip_tac
          >> ‘bvl_num_stubs ≤ wk’ by simp[]
          >> metis_tac[])
      >> strip_tac >> gvs[]
      >> metis_tac[]))
  >- (
    simp[lookup_union] >> rpt gen_tac >> Cases_on ‘lookup d m’ >> simp[]
    >- (strip_tac
        >> ‘lookup d csh = NONE’
          by (Cases_on ‘lookup d csh’ >> gvs[submap_def] >> res_tac >> gvs[])
        >> ‘MEM wk (MAP FST progs1) ∧ ¬MEM wk (MAP FST progs)’ by metis_tac[]
        >> ‘next ≤ wk ∧ in_ns_4 wk’ by metis_tac[]
        >> simp[])
    >> strip_tac >> gvs[] >> metis_tac[])
  >- (
    rpt strip_tac >> Cases_on ‘MEM n (MAP FST progs)’
    >- (Cases_on ‘bvl_num_stubs ≤ n’ >- metis_tac[] >> gvs[])
    >> qpat_x_assum ‘∀x. MEM x (MAP FST progs1) ∧ ¬MEM x (MAP FST progs) ⇒ _’
         (qspec_then ‘n’ mp_tac)
    >> simp[])
QED

Theorem do_install_state_rel:
  state_rel m s t ∧ do_app Install vs s = Rval (v,s1) ⇒
  ∃m1 t1. submap m m1 ∧ do_app Install vs t = Rval (v,t1) ∧ state_rel m1 s1 t1
Proof
  strip_tac
  >> qpat_x_assum ‘do_app _ _ _ = _’ mp_tac
  >> simp[do_app_def, do_install_def]
  >> ‘∃n0 c0 cfg0 progs. s.compile_oracle 0 = (((n0,c0),cfg0),progs)’
    by metis_tac[PAIR]
  >> simp[]
  >> Cases_on ‘compile_prog T (n0,c0) progs’
  >> rename1 ‘compile_prog T (n0,c0) progs = (st1,progs1)’
  >> PairCases_on ‘st1’
  >> rename1 ‘compile_prog T (n0,c0) progs = ((n1,c1),progs1)’
  >> ‘t.compile_oracle 0 = (cfg0,progs1) ∧ t.refs = s.refs’
    by gvs[state_rel_def, backendPropsTheory.state_co_def]
  >> ‘∀cfg p. s.compile ((n0,c0),cfg) p =
              case t.compile cfg (SND (compile_prog T (n0,c0) p)) of
                NONE => NONE
              | SOME (b,d,cfg1) =>
                  SOME (b,d,FST (compile_prog T (n0,c0) p),cfg1)’
    by (gvs[state_rel_def, backendPropsTheory.state_cc_def] >> rw[]
        >> pairarg_tac >> simp[] >> CASE_TAC >> simp[]
        >> PairCases_on ‘x’ >> simp[])
  >> simp[] >> strip_tac >> gvs[AllCaseEqs()]
  >> qmatch_asmsub_rename_tac ‘s.compile_oracle 0 = (_,(k,kbody)::rest)’
  >> qabbrev_tac ‘progs = (k,kbody)::rest’
  >> ‘compile_prog_with_map c0 n0 progs = ((n1,c1),progs1)’
    by gvs[compile_prog_def]
  >> qpat_x_assum ‘state_rel m s t’
       (fn th => assume_tac th >> strip_assume_tac (SRULE [state_rel_def] th))
  >> ‘submap c0 m’ by (qpat_x_assum ‘submap (SND _) m’ mp_tac >> simp[])
  >> ‘∀n. n ∈ domain t.code ∧ in_ns_4 n ⇒ n < n0’
    by (qpat_x_assum ‘∀n. n ∈ domain t.code ∧ _ ⇒ _’ mp_tac >> simp[])
  >> ‘input_condition n0 progs’
    by (qpat_x_assum ‘∀n. input_condition _ _’ (qspec_then ‘0’ mp_tac)
        >> simp[])
  >> ‘DISJOINT (domain s.code) (set (MAP FST progs))’ by simp[Abbr ‘progs’]
  >> drule_all code_rel_compile >> strip_tac
  >> ‘FST (s.compile_oracle 1) = ((n1,c1),cfg1)’ by gvs[shift_seq_def]
  >> qpat_x_assum ‘((n1,c1),cfg1) = _’ kall_tac
  >> ‘FST (t.compile_oracle 1) = cfg1’
    by (qpat_x_assum ‘t.compile_oracle = _’ SUBST1_TAC
        >> simp[backendPropsTheory.FST_state_co])
  >> ‘∃p1 rest1. progs1 = (k,p1)::rest1’
    by (qspecl_then [‘progs’,‘c0’,‘n0’,‘(n1,c1)’,‘progs1’] mp_tac
          compile_prog_with_map_HD
        >> simp[Abbr ‘progs’] >> Cases_on ‘progs1’ >> simp[]
        >> rename1 ‘FST h = k’ >> PairCases_on ‘h’ >> simp[])
  >> gvs[]
  >> qexists_tac ‘union m c1’ >> simp[shift_seq_def]
  >> ‘insert k kbody (fromAList rest) = fromAList progs’
    by simp[Abbr ‘progs’, fromAList_def]
  >> pop_assum SUBST1_TAC
  >> ‘insert k p1 (fromAList rest1) = fromAList ((k,p1)::rest1)’
    by simp[fromAList_def]
  >> pop_assum SUBST1_TAC
  >> drule compile_prog_with_map_next_mono >> strip_tac
  >> simp[state_rel_def]
  >> rpt conj_tac
  >- simp[FUN_EQ_THM, backendPropsTheory.state_co_def]
  >- (rpt strip_tac >> gvs[domain_fromAList] >> res_tac >> simp[])
  >- (
    gen_tac >> Cases_on ‘n ∈ domain s.code’ >- metis_tac[]
    >> simp[domain_fromAList] >> strip_tac
    >> qpat_x_assum ‘input_condition n0 progs’ mp_tac
    >> simp[input_condition_def, EVERY_MEM, MEM_FILTER, MEM_MAP, PULL_EXISTS]
    >> strip_tac >> gvs[MEM_MAP] >> metis_tac[])
  >> metis_tac[]
QED

Theorem do_app_state_swap[local]:
  op ≠ Install ⇒
    ((do_app op args s = Rval (value,s1) ∧
      domain s.code ⊆ domain t.code ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rval
        (value,
         t with <| refs := s1.refs; clock := s1.clock;
                   global := s1.global; ffi := s1.ffi |>)) ∧
     (do_app op args s = Rerr error ∧ error ≠ Rabort Rtype_error ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rerr error))
Proof
  strip_tac
  >> Cases_on `op`
  >> gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def, bvl_to_bvi_def,
          bvlSemTheory.do_app_def, AllCaseEqs(), state_component_equality,
          SUBSET_DEF, pairTheory.ELIM_UNCURRY]
  >> rpt strip_tac
  >> gvs []
  >- metis_tac []
  >> qmatch_asmsub_rename_tac
       `s.refs |+ (global_ptr,
                   ValueArray (LUPDATE new_value set_index global_values)) =
        s1.refs`
  >> qexists_tac
       `SOME (Unit,
              t with
                <| refs := s.refs |+ (global_ptr,
                     ValueArray (LUPDATE new_value set_index global_values));
                   clock := s1.clock; global := s1.global; ffi := s1.ffi |>)`
  >> conj_tac
  >- (qexists_tac `global_ptr` >> gvs [])
  >> disj2_tac
  >> gvs []
QED

Theorem do_app_state_rel:
  state_rel m s t ∧ do_app op vs s = Rval (v,s1) ⇒
  ∃m1 t1. submap m m1 ∧ do_app op vs t = Rval (v,t1) ∧ state_rel m1 s1 t1
Proof
  strip_tac
  >> Cases_on ‘op = Install’
  >- (gvs[] >> metis_tac[do_install_state_rel])
  >> ‘t with <| refs := s.refs; clock := s.clock; global := s.global;
                ffi := s.ffi |> = t’
    by gvs[state_rel_def, state_component_equality]
  >> ‘domain s.code ⊆ domain t.code’ by metis_tac[state_rel_def, code_rel_domain]
  >> ‘do_app op vs t =
        Rval (v,t with <| refs := s1.refs; clock := s1.clock;
                          global := s1.global; ffi := s1.ffi |>)’
    by metis_tac[do_app_state_swap]
  >> qexistsl_tac [‘m’,‘t with <| refs := s1.refs; clock := s1.clock;
                                  global := s1.global; ffi := s1.ffi |>’]
  >> imp_res_tac do_app_code >> imp_res_tac do_app_oracle
  >> gvs[state_rel_def, submap_refl] >> metis_tac[]
QED

Theorem do_app_state_rel_err:
  state_rel m s t ∧ do_app op vs s = Rerr e ∧ e ≠ Rabort Rtype_error ⇒
  do_app op vs t = Rerr e
Proof
  strip_tac
  >> Cases_on ‘op = Install’
  >- gvs[do_app_def, do_install_def, AllCaseEqs(), UNCURRY]
  >> ‘t with <| refs := s.refs; clock := s.clock; global := s.global;
                ffi := s.ffi |> = t’
    by gvs[state_rel_def, state_component_equality]
  >> metis_tac[do_app_state_swap]
QED

Theorem evaluate_wrapper_worker:
  ∀wk (t:('c,'ffi) bviSem$state) args wbody r sh t1.
    lookup wk t.code = SOME (LENGTH args,wbody) ∧
    (case r of
       Rval [v] =>
         v_shape sh v ∧
         evaluate ([wbody],args,t) = (Rerr (Rraise (Ret (flat_vals sh v))),t1)
     | Rerr err => evaluate ([wbody],args,t) = (Rerr err,t1)
     | _ => F) ∧
    (∀vs. r ≠ Rerr (Rraise (Ret vs))) ⇒
    evaluate ([make_wrapper (LENGTH args) wk sh],args,inc_clock 1 t) = (r,t1)
Proof
  rpt strip_tac >> Cases_on ‘r’ >> gvs[]
  >- (rename1 ‘Rval rv’ >> Cases_on ‘rv’ >> gvs[]
      >> rename1 ‘Rval (v::rest)’ >> Cases_on ‘rest’ >> gvs[]
      >> drule_all evaluate_make_wrapper >> simp[])
  >> drule_all evaluate_make_wrapper_Rerr >> simp[]
QED

Theorem evaluate_inc_clock_Rval[local]:
  evaluate (xs,env,inc_clock ck1 (t:('c,'ffi) bviSem$state)) = (Rval v,t1) ⇒
  evaluate (xs,env,inc_clock (ck1 + ck2) t) = (Rval v,inc_clock ck2 t1)
Proof
  strip_tac >> drule evaluate_add_clock >> simp[inc_clock_ADD]
  >> ‘ck1 + ck2 = ck2 + ck1’ by simp[]
  >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem evaluate_inc_clock_res[local]:
  evaluate (xs,env,inc_clock ck1 (t:('c,'ffi) bviSem$state)) = (r,t1) ∧
  r ≠ Rerr (Rabort Rtimeout_error) ⇒
  evaluate (xs,env,inc_clock (ck1 + ck2) t) = (r,inc_clock ck2 t1)
Proof
  strip_tac >> drule_all evaluate_add_clock >> simp[inc_clock_ADD]
  >> ‘ck1 + ck2 = ck2 + ck1’ by simp[]
  >> pop_assum SUBST1_TAC >> simp[]
QED

(* In a worker, a tail call of a split function becomes a tail call of its
   worker. *)
Theorem worker_body_tail_call[local]:
  tail_ok m f sh (Call ts dest args hdl) ∧ lookup f m = SOME (sh,wk) ∧
  split_ok sh ⇒
  ∃d dwk.
    dest = SOME d ∧ hdl = NONE ∧ lookup d m = SOME (sh,dwk) ∧
    worker_body m f wk sh (Call ts dest args hdl) =
      TailCall (shape_width sh) ts dwk args
Proof
  strip_tac >> imp_res_tac split_ok_ConsShape
  >> Cases_on ‘hdl’ >> gvs[tail_ok_def]
  >> gvs[worker_body_def] >> rw[] >> gvs[]
QED

Theorem cpr_correct:
  ∀xs env (s:((num # (cpr_shape # num) num_map) # 'c,'ffi) bviSem$state).
    (∀m t res s1.
       state_rel m s t ∧ evaluate (xs,env,s) = (res,s1) ∧
       res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃ck m1 t1.
         submap m m1 ∧ state_rel m1 s1 t1 ∧
         evaluate (xs,env,inc_clock ck t) = (res,t1)) ∧
    (∀m t e f wk sh res s1.
       xs = [e] ∧ state_rel m s t ∧
       lookup f m = SOME (sh,wk) ∧ split_ok sh ∧
       tail_ok m f sh e ∧ tail_form e ∧
       evaluate ([e],env,s) = (res,s1) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃ck m1 t1.
         submap m m1 ∧ state_rel m1 s1 t1 ∧
         case res of
           Rval [v] =>
             v_shape sh v ∧
             evaluate ([worker_body m f wk sh e],env,inc_clock ck t) =
               (Rerr (Rraise (Ret (flat_vals sh v))),t1)
         | Rerr err =>
             evaluate ([worker_body m f wk sh e],env,inc_clock ck t) =
               (Rerr err,t1)
         | _ => F)
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >- suspend "Nil"
  >- suspend "Cons"
  >- suspend "Var"
  >- suspend "If"
  >- suspend "Let"
  >- suspend "Raise"
  >- suspend "Return"
  >- suspend "Op"
  >- suspend "Tick"
  >- suspend "Force"
  >- suspend "Call"
  >- suspend "LetCall"
QED

Resume cpr_correct[Nil]:
  rw[evaluate_def] >> qexistsl_tac [‘0’,‘m’] >> simp[submap_refl, inc_clock_ZERO]
QED

Resume cpr_correct[Cons]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate (x::y::xs,_,_) = _’ mp_tac
    >> simp[evaluate_def]
    >> Cases_on ‘evaluate ([x],env,s)’ >> rename1 ‘evaluate ([x],env,s) = (r1,s2)’
    >> reverse (Cases_on ‘r1’) >> simp[]
    >- (
      strip_tac >> gvs[]
      >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ drule
      >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
      >> qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[])
    >> rename1 ‘evaluate ([x],env,s) = (Rval v1,s2)’
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> Cases_on ‘evaluate (y::xs,env,s2)’
    >> rename1 ‘evaluate (y::xs,env,s2) = (r2,s3)’
    >> strip_tac
    >> ‘r2 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀v4 s1 v1. _’ (qspecl_then [‘Rval v1’,‘s2’,‘v1’] mp_tac)
    >> simp[] >> disch_then (qspecl_then [‘m1’,‘t1’] mp_tac o CONJUNCT1) >> simp[]
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> drule_then (qspec_then ‘ck2’ assume_tac) evaluate_inc_clock_Rval
    >> Cases_on ‘r2’ >> gvs[evaluate_def])
  >> simp[]
QED

Resume cpr_correct[Var]:
  rw[evaluate_def]
  >> gvs[tail_ok_def]
  >> imp_res_tac split_ok_ConsShape >> gvs[exp_shape_ok_def]
  >> qexistsl_tac [‘0’,‘m’] >> simp[submap_refl, inc_clock_ZERO]
QED

Resume cpr_correct[If]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([If _ _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate ([x1],env,s)’ >> rename1 ‘evaluate ([x1],env,s) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate ([x1],env,s) = (Rval vs,s2)’
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> Cases_on ‘HD vs = Boolv T’ >> gvs[]
    >- (
      qpat_x_assum ‘∀m t. state_rel m s2 t ⇒ _’ drule
      >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
      >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
      >> simp[evaluate_def] >> metis_tac[submap_trans])
    >> Cases_on ‘HD vs = Boolv F’ >> gvs[]
    >> qpat_x_assum ‘∀m t. state_rel m s2 t ⇒ _’ drule
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> simp[evaluate_def] >> metis_tac[submap_trans])
  >- (
    rpt strip_tac >> gvs[tail_ok_def, tail_form_def, worker_body_def]
    >> qpat_x_assum ‘evaluate ([If _ _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate ([x1],env,s)’ >> rename1 ‘evaluate ([x1],env,s) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate ([x1],env,s) = (Rval vs,s2)’
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> ‘lookup f m1 = SOME (sh,wk)’ by gvs[submap_def]
    >> Cases_on ‘HD vs = Boolv T’ >> gvs[]
    >- (
      ‘tail_ok m1 f sh x2’ by (irule tail_ok_submap >> qexists_tac ‘m’ >> gvs[submap_def])
      >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' s2 t' ∧ _ ⇒ _’
           (qspecl_then [‘m1’,‘t1’,‘f’,‘wk’,‘sh’] mp_tac) >> simp[]
      >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
      >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
      >> ‘worker_body m1 f wk sh x2 = worker_body m f wk sh x2’
        by metis_tac[worker_body_submap]
      >> ‘submap m m2’ by metis_tac[submap_trans]
      >> gvs[AllCaseEqs()] >> simp[evaluate_def])
    >> Cases_on ‘HD vs = Boolv F’ >> gvs[]
    >> ‘tail_ok m1 f sh x3’ by (irule tail_ok_submap >> qexists_tac ‘m’ >> gvs[submap_def])
    >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' s2 t' ∧ _ ⇒ _’
         (qspecl_then [‘m1’,‘t1’,‘f’,‘wk’,‘sh’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> ‘worker_body m1 f wk sh x3 = worker_body m f wk sh x3’
      by metis_tac[worker_body_submap]
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> gvs[AllCaseEqs()] >> simp[evaluate_def])
QED

Resume cpr_correct[Let]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([Let _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s)’ >> rename1 ‘evaluate (xs,env,s) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s) = (Rval vs,s2)’
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> qpat_x_assum ‘∀m t. state_rel m s2 t ⇒ _’ drule
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> simp[evaluate_def])
  >- (
    rpt strip_tac >> gvs[tail_ok_def, tail_form_def, worker_body_def]
    >> qpat_x_assum ‘evaluate ([Let _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s)’ >> rename1 ‘evaluate (xs,env,s) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s) = (Rval vs,s2)’
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> ‘lookup f m1 = SOME (sh,wk)’ by gvs[submap_def]
    >> ‘tail_ok m1 f sh x2’ by (irule tail_ok_submap >> qexists_tac ‘m’ >> gvs[submap_def])
    >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' s2 t' ∧ _ ⇒ _’
         (qspecl_then [‘m1’,‘t1’,‘f’,‘wk’,‘sh’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> ‘worker_body m1 f wk sh x2 = worker_body m f wk sh x2’
      by metis_tac[worker_body_submap]
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> gvs[AllCaseEqs()] >> simp[evaluate_def])
QED

Resume cpr_correct[Raise]:
  rpt gen_tac >> strip_tac
  >> ‘∀m t res s1.
        state_rel m s t ∧ evaluate ([Raise x1],env,s) = (res,s1) ∧
        res ≠ Rerr (Rabort Rtype_error) ⇒
        ∃ck m1 t1. submap m m1 ∧ state_rel m1 s1 t1 ∧
          evaluate ([Raise x1],env,inc_clock ck t) = (res,t1)’
    by (rpt strip_tac
        >> qpat_x_assum ‘evaluate ([Raise _],_,_) = _’
             (assume_tac o SRULE[evaluate_def])
        >> Cases_on ‘evaluate ([x1],env,s)’
        >> rename1 ‘evaluate ([x1],env,s) = (r1,s2)’
        >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
        >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
             (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
        >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
        >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
        >> Cases_on ‘r1’ >> gvs[evaluate_def])
  >> simp[] >> rpt strip_tac >> gvs[worker_body_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
  >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
  >> gvs[evaluate_def, AllCaseEqs()]
QED

Resume cpr_correct[Return]:
  rpt gen_tac >> strip_tac
  >> reverse conj_tac
  >- (rpt strip_tac >> gvs[tail_ok_def]
      >> imp_res_tac split_ok_ConsShape >> gvs[exp_shape_ok_def])
  >> rpt strip_tac
  >> qpat_x_assum ‘evaluate ([Return _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
  >> Cases_on ‘evaluate (xs,env,s)’ >> rename1 ‘evaluate (xs,env,s) = (r1,s2)’
  >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
  >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
       (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
  >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
  >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
  >> Cases_on ‘r1’ >> gvs[evaluate_def]
QED

Resume cpr_correct[Op]:
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([Op _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s)’ >> rename1 ‘evaluate (xs,env,s) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1. state_rel m s t ∧ _ = (res,s1) ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s) = (Rval vs,s2)’
    >> Cases_on ‘do_app op (REVERSE vs) s2’ >> gvs[]
    >- (rename1 ‘do_app op (REVERSE vs) s2 = Rval p’ >> PairCases_on ‘p’ >> gvs[]
        >> drule_all do_app_state_rel
        >> disch_then (qx_choosel_then [‘m2’,‘t2’] strip_assume_tac)
        >> qexistsl_tac [‘ck1’,‘m2’,‘t2’] >> simp[evaluate_def]
        >> metis_tac[submap_trans])
    >> drule_all do_app_state_rel_err >> strip_tac
    >> qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
  >> rpt strip_tac >> gvs[]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
  >> qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[]
  >> gvs[tail_ok_def, worker_body_def]
  >> Cases_on ‘res’ >> simp[]
  >- (rename1 ‘Rval rv’
      >> imp_res_tac evaluate_SING_IMP >> gvs[]
      >> drule_all (cj 1 evaluate_flatten_exp) >> strip_tac
      >> simp[evaluate_def])
  >> drule_all (cj 1 evaluate_flatten_exp_err) >> strip_tac
  >> simp[evaluate_def]
QED

Resume cpr_correct[Tick]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([Tick _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> ‘t.clock = s.clock’ by gvs[state_rel_def]
    >> Cases_on ‘s.clock = 0’ >> gvs[]
    >- (qexistsl_tac [‘0’,‘m’,‘t’] >> simp[evaluate_def, inc_clock_ZERO, submap_refl])
    >> ‘state_rel m (dec_clock 1 s) (dec_clock 1 t)’ by simp[state_rel_dec_clock]
    >> qpat_x_assum ‘∀m t. state_rel m (dec_clock 1 s) t ⇒ _’ drule
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
    >> simp[evaluate_def, dec_clock_inv_clock1, inc_clock_clock])
  >- (
    rpt strip_tac >> gvs[tail_ok_def, tail_form_def, worker_body_def]
    >> qpat_x_assum ‘evaluate ([Tick _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> ‘t.clock = s.clock’ by gvs[state_rel_def]
    >> Cases_on ‘s.clock = 0’ >> gvs[]
    >- (qexistsl_tac [‘0’,‘m’,‘t’] >> simp[evaluate_def, inc_clock_ZERO, submap_refl])
    >> ‘state_rel m (dec_clock 1 s) (dec_clock 1 t)’ by simp[state_rel_dec_clock]
    >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' (dec_clock 1 s) t' ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘dec_clock 1 t’,‘f’,‘wk’,‘sh’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
    >> gvs[AllCaseEqs()] >> simp[evaluate_def, dec_clock_inv_clock1, inc_clock_clock])
QED

Resume cpr_correct[Force]:
  rpt gen_tac >> strip_tac
  >> reverse conj_tac
  >- (rpt strip_tac >> gvs[tail_ok_def]
      >> imp_res_tac split_ok_ConsShape >> gvs[exp_shape_ok_def])
  >> rpt strip_tac
  >> qpat_x_assum ‘evaluate ([Force _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
  >> ‘t.refs = s.refs ∧ t.clock = s.clock ∧ code_rel m s.code t.code’
    by gvs[state_rel_def]
  >> Cases_on ‘n < LENGTH env’ >> gvs[]
  >> Cases_on ‘dest_thunk env❲n❳ s.refs’ >> gvs[]
  >> rename1 ‘IsThunk mode fv’ >> Cases_on ‘mode’ >> gvs[]
  >- (qexistsl_tac [‘0’,‘m’,‘t’] >> simp[evaluate_def, inc_clock_ZERO, submap_refl])
  >> Cases_on ‘find_code (SOME force_loc) [env❲n❳; fv] s.code’ >> gvs[]
  >> rename1 ‘find_code _ _ s.code = SOME p’ >> PairCases_on ‘p’
  >> rename1 ‘find_code _ _ s.code = SOME (args,body)’
  >> drule_all code_rel_find_code_SOME_dest >> strip_tac
  >> qpat_x_assum ‘∀args' exp. _’ (qspecl_then [‘args’,‘body’] mp_tac) >> simp[]
  >> Cases_on ‘s.clock = 0’ >> gvs[]
  >- (
    ‘∃p. find_code (SOME force_loc) [env❲n❳; fv] t.code = SOME p’
      by (Cases_on ‘lookup force_loc m’ >> gvs[]
          >> rename1 ‘lookup force_loc m = SOME q’ >> PairCases_on ‘q’ >> gvs[])
    >> PairCases_on ‘p’
    >> qexistsl_tac [‘0’,‘m’,‘t with clock := 0’]
    >> simp[evaluate_def, inc_clock_ZERO, submap_refl, state_rel_with_clock])
  >> strip_tac
  >> Cases_on ‘evaluate ([body],[env❲n❳; fv],dec_clock 1 s)’
  >> rename1 ‘evaluate ([body],_,dec_clock 1 s) = (r0,s3)’
  >> ‘res = r0 ∧ s1 = s3 ∧ ∀vs. r0 ≠ Rerr (Rraise (Ret vs))’
    by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
        >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
  >> gvs[]
  >> ‘state_rel m (dec_clock 1 s) (dec_clock 1 t)’ by simp[state_rel_dec_clock]
  >> Cases_on ‘lookup force_loc m’ >> gvs[]
  >- (
    qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock 1 s) t' ⇒ _’ drule
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> qexistsl_tac [‘ck1’,‘m1’,‘t1’]
    >> simp[evaluate_def, dec_clock_inv_clock1, inc_clock_clock, inc_clock_code,
            inc_clock_refs]
    >> Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
    >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
  >> rename1 ‘lookup force_loc m = SOME p’ >> PairCases_on ‘p’ >> gvs[]
  >> rename1 ‘lookup force_loc m = SOME (sh,wk)’
  >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' (dec_clock 1 s) t' ∧ _ ⇒ _’
       (qspecl_then [‘m’,‘dec_clock 1 t’,‘force_loc’,‘wk’,‘sh’] mp_tac) >> simp[]
  >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
  >> qspecl_then [‘wk’,‘inc_clock ck1 (dec_clock 1 t)’,‘[env❲n❳; fv]’,
                  ‘worker_body m force_loc wk sh body’,‘r0’,‘sh’,‘t1’] mp_tac
       evaluate_wrapper_worker
  >> simp[inc_clock_code, dec_clock_code]
  >> strip_tac
  >> qexistsl_tac [‘ck1 + 1’,‘m1’,‘t1’]
  >> ‘inc_clock (ck1 + 1) (dec_clock 1 t) =
      inc_clock 1 (inc_clock ck1 (dec_clock 1 t))’ by simp[inc_clock_ADD]
  >> simp[evaluate_def, dec_clock_inv_clock1, inc_clock_clock, inc_clock_code,
          inc_clock_refs]
  >> Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
  >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[]
QED

Resume cpr_correct[Call]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([Call _ _ _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘IS_NONE dest ∧ IS_SOME handler’ >- gvs[]
    >> qpat_x_assum ‘¬(IS_NONE dest ∧ IS_SOME handler) ⇒ _’ drule >> strip_tac
    >> ‘¬(dest = NONE ∧ IS_SOME handler)’ by (Cases_on ‘dest’ >> gvs[])
    >> qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> simp[]
    >> Cases_on ‘evaluate (xs,env,s1)’ >> rename1 ‘evaluate (xs,env,s1) = (r1,s2)’
    >> strip_tac
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1'. state_rel m s1 t ∧ _ = (res,s1') ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def]
      >> Cases_on ‘dest’ >> gvs[])
    >> rename1 ‘evaluate (xs,env,s1) = (Rval vs,s2)’
    >> ‘(IS_NONE dest ∧ IS_SOME handler) ⇔ F’ by (Cases_on ‘dest’ >> gvs[])
    >> Cases_on ‘find_code dest vs s2.code’ >> gvs[]
    >> rename1 ‘find_code dest vs s2.code = SOME p’ >> PairCases_on ‘p’
    >> rename1 ‘find_code dest vs s2.code = SOME (args,body)’
    >> ‘code_rel m1 s2.code t1.code ∧ t1.clock = s2.clock’ by gvs[state_rel_def]
    >> drule_all code_rel_find_code_lookup >> strip_tac
    >> ‘∃tb. find_code dest vs t1.code = SOME (args,tb)’
      by (Cases_on ‘lookup d m1’ >> gvs[]
          >> rename1 ‘lookup d m1 = SOME q’ >> PairCases_on ‘q’ >> gvs[])
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> Cases_on ‘s2.clock < ticks + 1’ >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1 with clock := 0’]
      >> simp[state_rel_with_clock]
      >> ‘¬(IS_NONE dest ∧ IS_SOME handler)’ by (Cases_on ‘dest’ >> gvs[])
      >> simp[evaluate_def])
    >> ‘state_rel m1 (dec_clock (ticks + 1) s2) (dec_clock (ticks + 1) t1)’
      by simp[state_rel_dec_clock]
    >> Cases_on ‘evaluate ([body],args,dec_clock (ticks + 1) s2)’
    >> rename1 ‘evaluate ([body],args,dec_clock (ticks + 1) s2) = (r0,s3)’
    >> ‘r0 ≠ Rerr (Rabort Rtype_error) ∧ ∀vs. r0 ≠ Rerr (Rraise (Ret vs))’
      by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
          >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
    >> subgoal ‘∃ck2 m2 t2. submap m1 m2 ∧ state_rel m2 s3 t2 ∧
                  evaluate ([tb],args,inc_clock ck2 (dec_clock (ticks + 1) t1)) =
                    (r0,t2)’
    >- (
      Cases_on ‘lookup d m1’ >> gvs[]
      >> rename1 ‘lookup d m1 = SOME p’ >> PairCases_on ‘p’ >> gvs[]
      >> rename1 ‘lookup d m1 = SOME (sh,wk)’
      >> qpat_x_assum
           ‘∀m' t' f wk sh. state_rel m' (dec_clock (ticks + 1) s2) t' ∧ _ ⇒ _’
           (qspecl_then [‘m1’,‘dec_clock (ticks + 1) t1’,‘d’,‘wk’,‘sh’] mp_tac)
      >> simp[]
      >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
      >> qspecl_then [‘wk’,‘inc_clock ck2 (dec_clock (ticks + 1) t1)’,‘args’,
                      ‘worker_body m1 d wk sh body’,‘r0’,‘sh’,‘t2’] mp_tac
           evaluate_wrapper_worker
      >> simp[inc_clock_code, dec_clock_code] >> strip_tac
      >> qexistsl_tac [‘ck2 + 1’,‘m2’,‘t2’]
      >> ‘inc_clock (ck2 + 1) (dec_clock (ticks + 1) t1) =
          inc_clock 1 (inc_clock ck2 (dec_clock (ticks + 1) t1))’ by simp[inc_clock_ADD]
      >> simp[])
    >> ‘¬(IS_NONE dest ∧ IS_SOME handler)’ by (Cases_on ‘dest’ >> gvs[])
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> Cases_on ‘∃v x. r0 = Rerr (Rraise (Exn v)) ∧ handler = SOME x’
    >- (
      gvs[]
      >> Cases_on ‘evaluate ([x],v::env,s3)’ >> rename1 ‘evaluate ([x],v::env,s3) = (hr,s4)’
      >> ‘res = hr ∧ s1' = s4 ∧ ∀vs. hr ≠ Rerr (Rraise (Ret vs))’
        by (Cases_on ‘hr’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
            >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
      >> gvs[]
      >> qpat_x_assum ‘∀m t. state_rel m s3 t ⇒ _’ drule
      >> disch_then (qx_choosel_then [‘ck3’,‘m3’,‘t3’] strip_assume_tac)
      >> qexistsl_tac [‘ck1 + (ck2 + ck3)’,‘m3’,‘t3’]
      >> ‘submap m m3’ by metis_tac[submap_trans]
      >> qpat_x_assum ‘evaluate ([tb],_,_) = _’ assume_tac
      >> drule_then (qspec_then ‘ck3’ mp_tac) evaluate_inc_clock_res
      >> simp[] >> strip_tac
      >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock]
      >> Cases_on ‘hr’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
      >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
    >> ‘res = r0 ∧ s1' = s3’
      by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
          >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[] >> Cases_on ‘handler’ >> gvs[])
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock]
    >> Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
    >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[] >> Cases_on ‘handler’ >> gvs[])
  >- (
    rpt strip_tac >> gvs[]
    >> drule_all worker_body_tail_call >> strip_tac >> gvs[tail_form_def, no_ret_def]
    >> qpat_x_assum ‘evaluate ([Call _ _ _ _],_,_) = _’ (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s1)’ >> rename1 ‘evaluate (xs,env,s1) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1'. state_rel m s1 t ∧ _ = (res,s1') ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s1) = (Rval vs,s2)’
    >> Cases_on ‘find_code (SOME d) vs s2.code’ >> gvs[]
    >> rename1 ‘find_code _ vs s2.code = SOME p’ >> PairCases_on ‘p’
    >> rename1 ‘find_code _ vs s2.code = SOME (args,body)’
    >> ‘code_rel m1 s2.code t1.code ∧ t1.clock = s2.clock’ by gvs[state_rel_def]
    >> ‘lookup d m1 = SOME (sh,dwk)’ by gvs[submap_def]
    >> drule_all code_rel_find_code_SOME_dest >> strip_tac >> gvs[]
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> ‘find_code (SOME dwk) args t1.code =
          SOME (args,worker_body m1 d dwk sh body)’
      by simp[bvlSemTheory.find_code_def]
    >> Cases_on ‘s2.clock < ticks + 1’ >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1 with clock := 0’]
      >> simp[state_rel_with_clock, evaluate_def])
    >> ‘state_rel m1 (dec_clock (ticks + 1) s2) (dec_clock (ticks + 1) t1)’
      by simp[state_rel_dec_clock]
    >> Cases_on ‘evaluate ([body],args,dec_clock (ticks + 1) s2)’
    >> rename1 ‘evaluate ([body],args,dec_clock (ticks + 1) s2) = (r0,s3)’
    >> ‘res = r0 ∧ s1' = s3 ∧ ∀vs. r0 ≠ Rerr (Rraise (Ret vs))’
      by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
          >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
    >> gvs[]
    >> qpat_x_assum
         ‘∀m' t' f' wk' sh'. state_rel m' (dec_clock (ticks + 1) s2) t' ∧ _ ⇒ _’
         (qspecl_then [‘m1’,‘dec_clock (ticks + 1) t1’,‘d’,‘dwk’,‘sh’] mp_tac)
    >> simp[]
    >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> ‘dec_clock (ticks + 1) (inc_clock ck2 t1) =
        inc_clock ck2 (dec_clock (ticks + 1) t1)’ by simp[dec_clock_inv_clock]
    >> Cases_on ‘r0’ >> gvs[]
    >- (
      rename1 ‘Rval rv’ >> Cases_on ‘rv’ >> gvs[]
      >> rename1 ‘Rval (v::rest)’ >> Cases_on ‘rest’ >> gvs[]
      >> irule evaluate_TailCall
      >> conj_tac >- (irule (cj 1 flat_vals_LENGTH) >> simp[])
      >> qexistsl_tac [‘args’,‘worker_body m1 d dwk sh body’,‘inc_clock ck2 t1’,‘args’]
      >> simp[inc_clock_code, inc_clock_clock])
    >> irule evaluate_TailCall_err >> simp[]
    >> qexistsl_tac [‘args’,‘worker_body m1 d dwk sh body’,‘inc_clock ck2 t1’,‘args’]
    >> simp[inc_clock_code, inc_clock_clock])
QED

Resume cpr_correct[LetCall]:
  rpt gen_tac >> strip_tac
  >> conj_tac >- (
    rpt strip_tac
    >> qpat_x_assum ‘evaluate ([LetCall _ _ _ _ _],_,_) = _’
         (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s1)’ >> rename1 ‘evaluate (xs,env,s1) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1'. state_rel m s1 t ∧ _ = (res,s1') ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s1) = (Rval vs,s2)’
    >> Cases_on ‘find_code (SOME dest) vs s2.code’ >> gvs[]
    >> rename1 ‘find_code _ vs s2.code = SOME p’ >> PairCases_on ‘p’
    >> rename1 ‘find_code _ vs s2.code = SOME (args,body)’
    >> ‘code_rel m1 s2.code t1.code ∧ t1.clock = s2.clock’ by gvs[state_rel_def]
    >> drule_all code_rel_find_code_SOME_dest >> strip_tac >> gvs[]
    >> ‘∃tb. find_code (SOME dest) args t1.code = SOME (args,tb)’
      by (Cases_on ‘lookup dest m1’ >> gvs[]
          >> rename1 ‘lookup dest m1 = SOME q’ >> PairCases_on ‘q’ >> gvs[])
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> Cases_on ‘s2.clock < ticks + 1’ >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1 with clock := 0’]
      >> simp[state_rel_with_clock, evaluate_def])
    >> ‘state_rel m1 (dec_clock (ticks + 1) s2) (dec_clock (ticks + 1) t1)’
      by simp[state_rel_dec_clock]
    >> Cases_on ‘evaluate ([body],args,dec_clock (ticks + 1) s2)’
    >> rename1 ‘evaluate ([body],args,dec_clock (ticks + 1) s2) = (r0,s3)’
    >> ‘r0 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> subgoal ‘∃ck2 m2 t2. submap m1 m2 ∧ state_rel m2 s3 t2 ∧
                  evaluate ([tb],args,inc_clock ck2 (dec_clock (ticks + 1) t1)) =
                    (r0,t2)’
    >- (
      Cases_on ‘lookup dest m1’ >> gvs[]
      >> rename1 ‘lookup dest m1 = SOME p’ >> PairCases_on ‘p’ >> gvs[]
      >> rename1 ‘lookup dest m1 = SOME (sh,wk)’
      >> ‘∀vs. r0 ≠ Rerr (Rraise (Ret vs))’ by metis_tac[evaluate_tail_no_Ret]
      >> qpat_x_assum
           ‘∀m' t' f wk sh. state_rel m' (dec_clock (ticks + 1) s2) t' ∧ _ ⇒ _’
           (qspecl_then [‘m1’,‘dec_clock (ticks + 1) t1’,‘dest’,‘wk’,‘sh’] mp_tac)
      >> simp[]
      >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
      >> qspecl_then [‘wk’,‘inc_clock ck2 (dec_clock (ticks + 1) t1)’,‘args’,
                      ‘worker_body m1 dest wk sh body’,‘r0’,‘sh’,‘t2’] mp_tac
           evaluate_wrapper_worker
      >> simp[inc_clock_code, dec_clock_code] >> strip_tac
      >> qexistsl_tac [‘ck2 + 1’,‘m2’,‘t2’]
      >> ‘inc_clock (ck2 + 1) (dec_clock (ticks + 1) t1) =
          inc_clock 1 (inc_clock ck2 (dec_clock (ticks + 1) t1))’ by simp[inc_clock_ADD]
      >> simp[])
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> Cases_on ‘∃ret_vs. r0 = Rerr (Rraise (Ret ret_vs)) ∧ LENGTH ret_vs = rets’
    >- (
      gvs[]
      >> qpat_x_assum ‘∀m t. state_rel m s3 t ⇒ _’ drule
      >> disch_then (qx_choosel_then [‘ck3’,‘m3’,‘t3’] strip_assume_tac)
      >> qexistsl_tac [‘ck1 + (ck2 + ck3)’,‘m3’,‘t3’]
      >> ‘submap m m3’ by metis_tac[submap_trans]
      >> qpat_x_assum ‘evaluate ([tb],_,_) = _’ assume_tac
      >> drule_then (qspec_then ‘ck3’ mp_tac) evaluate_inc_clock_res
      >> simp[] >> strip_tac
      >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock])
    >> ‘res = r0 ∧ s1' = s3’
      by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
          >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock]
    >> Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
    >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
  >- (
    rpt strip_tac >> gvs[tail_ok_def, tail_form_def, worker_body_def]
    >> qpat_x_assum ‘evaluate ([LetCall _ _ _ _ _],_,_) = _’
         (assume_tac o SRULE[evaluate_def])
    >> Cases_on ‘evaluate (xs,env,s1)’ >> rename1 ‘evaluate (xs,env,s1) = (r1,s2)’
    >> ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀m t res s1'. state_rel m s1 t ∧ _ = (res,s1') ∧ _ ⇒ _’
         (qspecl_then [‘m’,‘t’] mp_tac) >> simp[]
    >> disch_then (qx_choosel_then [‘ck1’,‘m1’,‘t1’] strip_assume_tac)
    >> reverse (Cases_on ‘r1’) >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1’] >> simp[evaluate_def])
    >> rename1 ‘evaluate (xs,env,s1) = (Rval vs,s2)’
    >> Cases_on ‘find_code (SOME dest) vs s2.code’ >> gvs[]
    >> rename1 ‘find_code _ vs s2.code = SOME p’ >> PairCases_on ‘p’
    >> rename1 ‘find_code _ vs s2.code = SOME (args,body)’
    >> ‘code_rel m1 s2.code t1.code ∧ t1.clock = s2.clock’ by gvs[state_rel_def]
    >> drule_all code_rel_find_code_SOME_dest >> strip_tac >> gvs[]
    >> ‘∃tb. find_code (SOME dest) args t1.code = SOME (args,tb)’
      by (Cases_on ‘lookup dest m1’ >> gvs[]
          >> rename1 ‘lookup dest m1 = SOME q’ >> PairCases_on ‘q’ >> gvs[])
    >> drule_then assume_tac evaluate_inc_clock_Rval
    >> Cases_on ‘s2.clock < ticks + 1’ >> gvs[]
    >- (
      qexistsl_tac [‘ck1’,‘m1’,‘t1 with clock := 0’]
      >> simp[state_rel_with_clock, evaluate_def])
    >> ‘state_rel m1 (dec_clock (ticks + 1) s2) (dec_clock (ticks + 1) t1)’
      by simp[state_rel_dec_clock]
    >> Cases_on ‘evaluate ([body],args,dec_clock (ticks + 1) s2)’
    >> rename1 ‘evaluate ([body],args,dec_clock (ticks + 1) s2) = (r0,s3)’
    >> ‘r0 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac >> gvs[])
    >> subgoal ‘∃ck2 m2 t2. submap m1 m2 ∧ state_rel m2 s3 t2 ∧
                  evaluate ([tb],args,inc_clock ck2 (dec_clock (ticks + 1) t1)) =
                    (r0,t2)’
    >- (
      Cases_on ‘lookup dest m1’ >> gvs[]
      >> rename1 ‘lookup dest m1 = SOME p’ >> PairCases_on ‘p’ >> gvs[]
      >> rename1 ‘lookup dest m1 = SOME (dsh,dwk)’
      >> ‘∀vs. r0 ≠ Rerr (Rraise (Ret vs))’ by metis_tac[evaluate_tail_no_Ret]
      >> qpat_x_assum
           ‘∀m' t' f wk sh. state_rel m' (dec_clock (ticks + 1) s2) t' ∧ _ ⇒ _’
           (qspecl_then [‘m1’,‘dec_clock (ticks + 1) t1’,‘dest’,‘dwk’,‘dsh’] mp_tac)
      >> simp[]
      >> disch_then (qx_choosel_then [‘ck2’,‘m2’,‘t2’] strip_assume_tac)
      >> qspecl_then [‘dwk’,‘inc_clock ck2 (dec_clock (ticks + 1) t1)’,‘args’,
                      ‘worker_body m1 dest dwk dsh body’,‘r0’,‘dsh’,‘t2’] mp_tac
           evaluate_wrapper_worker
      >> simp[inc_clock_code, dec_clock_code] >> strip_tac
      >> qexistsl_tac [‘ck2 + 1’,‘m2’,‘t2’]
      >> ‘inc_clock (ck2 + 1) (dec_clock (ticks + 1) t1) =
          inc_clock 1 (inc_clock ck2 (dec_clock (ticks + 1) t1))’ by simp[inc_clock_ADD]
      >> simp[])
    >> ‘submap m m2’ by metis_tac[submap_trans]
    >> Cases_on ‘∃ret_vs. r0 = Rerr (Rraise (Ret ret_vs)) ∧ LENGTH ret_vs = rets’
    >- (
      gvs[]
      >> ‘lookup f m2 = SOME (sh,wk)’ by gvs[submap_def]
      >> ‘tail_ok m2 f sh y’ by (irule tail_ok_submap >> qexists_tac ‘m’ >> gvs[submap_def])
      >> qpat_x_assum ‘∀m' t' f wk sh. state_rel m' s3 t' ∧ _ ⇒ _’
           (qspecl_then [‘m2’,‘t2’,‘f’,‘wk’,‘sh’] mp_tac) >> simp[]
      >> disch_then (qx_choosel_then [‘ck3’,‘m3’,‘t3’] strip_assume_tac)
      >> qexistsl_tac [‘ck1 + (ck2 + ck3)’,‘m3’,‘t3’]
      >> ‘submap m m3’ by metis_tac[submap_trans]
      >> ‘worker_body m2 f wk sh y = worker_body m f wk sh y’
        by metis_tac[worker_body_submap]
      >> qpat_x_assum ‘evaluate ([tb],_,_) = _’ assume_tac
      >> drule_then (qspec_then ‘ck3’ mp_tac) evaluate_inc_clock_res
      >> simp[] >> strip_tac
      >> gvs[AllCaseEqs()]
      >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock])
    >> ‘res = r0 ∧ s1' = s3’
      by (Cases_on ‘r0’ >> gvs[] >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
          >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
    >> qexistsl_tac [‘ck1 + ck2’,‘m2’,‘t2’]
    >> Cases_on ‘r0’ >> gvs[]
    >> simp[evaluate_def, dec_clock_inv_clock, inc_clock_code, inc_clock_clock]
    >> rename1 ‘Rerr e’ >> Cases_on ‘e’ >> gvs[]
    >> rename1 ‘Rraise ex’ >> Cases_on ‘ex’ >> gvs[])
QED

Finalise cpr_correct;

Theorem compile_prog_evaluate:
  input_condition n prog ∧
  (∀k st cfg p. co k = ((st,cfg),p) ⇒ input_condition (FST st) p) ∧
  compile_prog T (n,LN) prog = (st1,prog2) ∧
  (∀k. MEM k (MAP FST prog2) ∧ in_ns_4 k ⇒ k < FST (FST (FST (co 0)))) ∧
  SND (FST (FST (co 0))) = SND st1 ∧
  evaluate ([Call 0 (SOME start) [] NONE],[],
            initial_state ffi0 (fromAList prog) co
              (state_cc (compile_prog T) cc) k) = (r,s) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃ck m t.
    evaluate ([Call 0 (SOME start) [] NONE],[],
              initial_state ffi0 (fromAList prog2)
                (state_co (compile_prog T) co) cc (k + ck)) = (r,t) ∧
    state_rel m s t
Proof
  strip_tac
  >> PairCases_on ‘st1’
  >> ‘compile_prog_with_map LN n prog = ((st10,st11),prog2)’
    by gvs[compile_prog_def]
  >> ‘code_rel LN (LN:(num # bvi$exp) num_map) (LN:(num # bvi$exp) num_map) ∧
      submap LN (LN:(cpr_shape # num) num_map) ∧
      DISJOINT (domain (LN:(num # bvi$exp) num_map)) (set (MAP FST prog)) ∧
      (∀x. x ∈ domain (LN:(num # bvi$exp) num_map) ∧ in_ns_4 x ⇒ x < n) ∧
      (∀x. x ∈ domain (LN:(num # bvi$exp) num_map) ∧ bvl_num_stubs ≤ x ⇒
           ¬in_ns_4 x) ∧
      (∀d sh wk. lookup d (LN:(cpr_shape # num) num_map) = SOME (sh,wk) ⇒
                 in_ns_4 wk ∧ bvl_num_stubs ≤ wk)’
    by simp[code_rel_def, map_ok_def, submap_refl]
  >> drule_all code_rel_compile >> simp[] >> strip_tac
  >> qabbrev_tac ‘s0 = initial_state ffi0 (fromAList prog) co
                         (state_cc (compile_prog T) cc) k’
  >> qabbrev_tac ‘t0 = initial_state ffi0 (fromAList prog2)
                         (state_co (compile_prog T) co) cc k’
  >> subgoal ‘state_rel st11 s0 t0’
  >- (
    simp[state_rel_def, Abbr ‘s0’, Abbr ‘t0’]
    >> rpt conj_tac
    >- (
      gen_tac >> ‘∃st cfg p. co n' = ((st,cfg),p)’ by metis_tac[PAIR]
      >> simp[]
      >> qpat_x_assum ‘∀k st cfg p. co k = _ ⇒ _’ drule >> simp[])
    >- (
      simp[domain_fromAList] >> rpt strip_tac
      >> qpat_x_assum ‘∀k. MEM k (MAP FST prog2) ∧ _ ⇒ _’ irule >> simp[])
    >- (
      qpat_x_assum ‘input_condition n prog’ mp_tac
      >> simp[domain_fromAList, input_condition_def, EVERY_MEM, MEM_FILTER,
              MEM_MAP, PULL_EXISTS]
      >> rpt strip_tac >> res_tac)
    >> qpat_x_assum ‘∀d sh wk. lookup d st11 = _ ⇒ _’ ACCEPT_TAC)
  >> drule_all (cj 1 cpr_correct)
  >> disch_then (qx_choosel_then [‘ck’,‘m1’,‘t1’] strip_assume_tac)
  >> qexistsl_tac [‘ck’,‘m1’,‘t1’]
  >> gvs[Abbr ‘t0’, inc_clock_def, initial_state_with_simp]
QED

Theorem evaluate_initial_state_mono[local]:
  bviSem$evaluate (es,[],bviSem$initial_state ffi c co cc k1) = (r,s) ∧
  r ≠ Rerr (Rabort Rtimeout_error) ∧ k1 ≤ k2 ⇒
  ∃s1. bviSem$evaluate (es,[],bviSem$initial_state ffi c co cc k2) = (r,s1) ∧
       s1.ffi = s.ffi
Proof
  strip_tac
  >> drule_all evaluate_add_clock
  >> disch_then (qspec_then ‘k2 - k1’ mp_tac)
  >> simp[inc_clock_def]
QED

Theorem semantics_fwd_sim[local]:
  (∀k r s.
     evaluate ([Call 0 (SOME start) [] NONE],[],
               initial_state ffi c1 co1 cc1 k) = (r,s) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
     ∃ck t.
       evaluate ([Call 0 (SOME start) [] NONE],[],
                 initial_state ffi c2 co2 cc2 (k + ck)) = (r,t) ∧
       t.ffi = s.ffi) ∧
  semantics ffi c1 co1 cc1 start ≠ Fail ⇒
  semantics ffi c1 co1 cc1 start = semantics ffi c2 co2 cc2 start
Proof
  strip_tac
  >> ‘∀k e. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
                           initial_state ffi c1 co1 cc1 k)) = Rerr e ⇒
            e = Rabort Rtimeout_error ∨ ∃f. e = Rabort (Rffi_error f)’
    by (qpat_x_assum ‘_ ≠ Fail’ mp_tac >> simp[semantics_def] >> metis_tac[])
  >> ‘∀k. ∃ck t.
        evaluate ([Call 0 (SOME start) [] NONE],[],
                  initial_state ffi c2 co2 cc2 (k + ck)) =
          (FST (evaluate ([Call 0 (SOME start) [] NONE],[],
                          initial_state ffi c1 co1 cc1 k)),t) ∧
        t.ffi = (SND (evaluate ([Call 0 (SOME start) [] NONE],[],
                                initial_state ffi c1 co1 cc1 k))).ffi’
    by (
      gen_tac
      >> Cases_on ‘evaluate ([Call 0 (SOME start) [] NONE],[],
                             initial_state ffi c1 co1 cc1 k)’
      >> qpat_x_assum ‘∀k r s. _ ∧ _ ⇒ ∃ck t. _’
           (qspecl_then [‘k’,‘q’,‘r’] mp_tac)
      >> impl_tac
      >- (
        simp[] >> strip_tac
        >> qpat_x_assum ‘∀k e. _ ⇒ _’ (qspecl_then [‘k’,‘Rabort Rtype_error’] mp_tac)
        >> simp[])
      >> simp[])
  >> qpat_x_assum ‘∀k r s. _ ∧ _ ⇒ ∃ck t. _’ kall_tac
  >> ‘∀k e. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
                           initial_state ffi c2 co2 cc2 k)) = Rerr e ⇒
            e = Rabort Rtimeout_error ∨ ∃f. e = Rabort (Rffi_error f)’
    by (
      rpt strip_tac
      >> Cases_on ‘evaluate ([Call 0 (SOME start) [] NONE],[],
                             initial_state ffi c2 co2 cc2 k)’
      >> gvs[]
      >> Cases_on ‘e = Rabort Rtimeout_error’ >> simp[]
      >> drule evaluate_add_clock >> simp[]
      >> qpat_x_assum ‘∀k. ∃ck t. _’ (qspec_then ‘k’ strip_assume_tac)
      >> disch_then (qspec_then ‘ck’ mp_tac)
      >> simp[inc_clock_def]
      >> strip_tac >> gvs[]
      >> qpat_x_assum ‘∀k e. FST (evaluate (_,_,initial_state _ c1 _ _ _)) = _ ⇒ _’
           (qspecl_then [‘k’,‘e’] mp_tac)
      >> simp[])
  >> simp[semantics_def]
  >> IF_CASES_TAC >- metis_tac[]
  >> IF_CASES_TAC >- metis_tac[]
  >> DEEP_INTRO_TAC some_intro >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> DEEP_INTRO_TAC some_intro >> simp[]
    >> conj_tac
    >- (
      simp[PULL_EXISTS] >> qx_genl_tac [‘k2’,‘s2’,‘r2’,‘out2’] >> strip_tac
      >> qpat_x_assum ‘∀k. ∃ck t. _’ (qspec_then ‘k’ strip_assume_tac)
      >> gvs[]
      >> ‘r ≠ Rerr (Rabort Rtimeout_error) ∧ r2 ≠ Rerr (Rabort Rtimeout_error)’
        by (conj_tac >> strip_tac >> gvs[])
      >> qpat_assum ‘evaluate (_,_,initial_state _ c2 _ _ _) = (r,t)’
           (mp_then (Pos hd) (qspec_then ‘ck + k + k2’ mp_tac)
              evaluate_initial_state_mono)
      >> qpat_assum ‘evaluate (_,_,initial_state _ c2 _ _ _) = (r2,s2)’
           (mp_then (Pos hd) (qspec_then ‘ck + k + k2’ mp_tac)
              evaluate_initial_state_mono)
      >> simp[] >> rpt strip_tac
      >> gvs[] >> every_case_tac >> gvs[])
    >> qpat_x_assum ‘∀k. ∃ck t. _’ (qspec_then ‘k’ strip_assume_tac)
    >> gvs[]
    >> qpat_assum ‘evaluate (_,_,initial_state _ c2 _ _ _) = (r,t)’ (irule_at Any)
    >> qexists_tac ‘outcome’ >> simp[])
  >> strip_tac
  >> DEEP_INTRO_TAC some_intro >> simp[]
  >> conj_tac
  >- (
    simp[PULL_EXISTS] >> qx_genl_tac [‘k2’,‘s2’,‘r2’,‘out2’] >> rpt strip_tac
    >> ‘r2 ≠ Rerr (Rabort Rtimeout_error)’ by (strip_tac >> gvs[])
    >> qpat_x_assum ‘∀k. ∃ck t. _’ (qspec_then ‘k2’ strip_assume_tac)
    >> namedCases_on ‘evaluate ([Call 0 (SOME start) [] NONE],[],
                                initial_state ffi c1 co1 cc1 k2)’ ["r1 s1"]
    >> gvs[]
    >> qpat_assum ‘evaluate (_,_,initial_state _ c2 _ _ _) = (r2,s2)’
         (mp_then (Pos hd) (qspec_then ‘ck + k2’ mp_tac)
            evaluate_initial_state_mono)
    >> simp[] >> strip_tac >> gvs[]
    >> qpat_x_assum ‘∀k s r outcome. _ ⇒ ¬_’
         (qspecl_then [‘k2’,‘s1’,‘r1’,‘out2’] mp_tac)
    >> simp[])
  >> strip_tac
  >> qmatch_abbrev_tac ‘build_lprefix_lub l1 = build_lprefix_lub l2’
  >> ‘(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2’
    suffices_by metis_tac[build_lprefix_lub_thm, lprefix_lub_new_chain,
                          unique_lprefix_lub]
  >> conj_asm1_tac
  >- (
    unabbrev_all_tac
    >> conj_tac
    >> Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    >> REWRITE_TAC [IMAGE_COMPOSE]
    >> match_mp_tac prefix_chain_lprefix_chain
    >> simp [prefix_chain_def, PULL_EXISTS]
    >> qx_genl_tac [‘k1’,‘k2’]
    >> qspecl_then [‘k1’,‘k2’] mp_tac LESS_EQ_CASES
    >> metis_tac [LESS_EQ_EXISTS, initial_state_with_simp,
                  evaluate_add_to_clock_io_events_mono
                    |> CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s"]))
                    |> Q.SPEC ‘s with clock := k’
                    |> SIMP_RULE (srw_ss()) [inc_clock_def]])
  >> simp [equiv_lprefix_chain_thm]
  >> unabbrev_all_tac >> simp [PULL_EXISTS]
  >> ntac 2 (pop_assum kall_tac)
  >> simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  >> qx_genl_tac [‘n’,‘x’,‘k’]
  >> qpat_x_assum ‘∀k. ∃ck t. _’ (qspec_then ‘k’ strip_assume_tac)
  >> conj_tac
  >- (strip_tac >> qexists_tac ‘k + ck’ >> gvs[])
  >> strip_tac >> qexists_tac ‘k’
  >> qspecl_then [‘[Call 0 (SOME start) [] NONE]’,‘[]’,
                  ‘initial_state ffi c2 co2 cc2 k’,‘ck’] mp_tac
       evaluate_add_to_clock_io_events_mono
  >> simp[inc_clock_def]
  >> strip_tac
  >> gvs[]
  >> drule_then assume_tac IS_PREFIX_LENGTH
  >> conj_asm1_tac >- simp[]
  >> irule (GSYM is_prefix_el) >> simp[]
QED

Theorem compile_prog_semantics:
  input_condition n prog ∧
  (∀k st cfg p. co k = ((st,cfg),p) ⇒ input_condition (FST st) p) ∧
  compile_prog b (n,LN) prog = (st1,prog2) ∧
  (∀k. MEM k (MAP FST prog2) ∧ in_ns_4 k ⇒ k < FST (FST (FST (co 0)))) ∧
  SND (FST (FST (co 0))) = SND st1 ∧
  semantics ffi (fromAList prog) co (state_cc (compile_prog b) cc) start ≠
    Fail ⇒
  semantics ffi (fromAList prog) co (state_cc (compile_prog b) cc) start =
  semantics ffi (fromAList prog2) (state_co (compile_prog b) co) cc start
Proof
  Cases_on ‘b’
  >- (
    strip_tac
    >> irule semantics_fwd_sim >> simp[]
    >> rpt strip_tac
    >> drule_all compile_prog_evaluate
    >> disch_then (qx_choosel_then [‘ck’,‘m’,‘t’] strip_assume_tac)
    >> qexistsl_tac [‘ck’,‘t’]
    >> gvs[state_rel_def])
  >> ‘bvi_cpr$compile_prog F = CURRY I’
    by simp[FUN_EQ_THM, FORALL_PROD, compile_prog_def]
  >> strip_tac >> gvs[]
  >> irule semantics_CURRY_I >> simp[]
QED

Theorem compile_prog_next_mono:
  compile_prog b (n,csh) xs = ((n1,c1),ys) ⇒
  ∃k. n1 = n + bvl_to_bvi_namespaces * k
Proof
  Cases_on ‘b’ >> rw[compile_prog_def]
  >- (
    drule compile_prog_with_map_next_mono >> strip_tac
    >> qexists_tac ‘k’ >> simp[])
  >> qexists_tac ‘0’ >> simp[]
QED

Theorem compile_prog_MEM:
  compile_prog b (n,csh) xs = ((n1,c1),ys) ∧ MEM e (MAP FST ys) ⇒
  MEM e (MAP FST xs) ∨
  n ≤ e ∧ e < n1 ∧ ∃k. e = n + k * bvl_to_bvi_namespaces
Proof
  rw[compile_prog_def] >> gvs[]
  >> metis_tac[compile_prog_with_map_MEM]
QED

Theorem compile_prog_ALL_DISTINCT:
  compile_prog b (n,csh) xs = ((n1,c1),ys) ∧
  ALL_DISTINCT (MAP FST xs) ∧ EVERY (free_names n o FST) xs ⇒
  ALL_DISTINCT (MAP FST ys) ∧ EVERY (free_names n1 o FST) ys
Proof
  rw[compile_prog_def] >> gvs[]
  >> metis_tac[compile_prog_with_map_ALL_DISTINCT]
QED

Theorem compile_prog_keeps_names:
  compile_prog b st xs = (st1,ys) ∧ MEM x (MAP FST xs) ⇒ MEM x (MAP FST ys)
Proof
  PairCases_on ‘st’ >> rw[compile_prog_def] >> gvs[]
  >> metis_tac[compile_prog_with_map_keeps_names]
QED

Theorem compile_prog_HD:
  compile_prog b st xs = (st1,ys) ∧ xs ≠ [] ⇒
  ys ≠ [] ∧ FST (HD ys) = FST (HD xs)
Proof
  PairCases_on ‘st’ >> rw[compile_prog_def] >> gvs[]
  >> metis_tac[compile_prog_with_map_HD]
QED

Theorem flatten_exp_code_labels[local]:
  (∀sh e. BIGUNION (set (MAP get_code_labels (flatten_exp sh e))) ⊆
          get_code_labels e) ∧
  (∀shs xs. BIGUNION (set (MAP get_code_labels (flatten_list shs xs))) ⊆
            BIGUNION (set (MAP get_code_labels xs)))
Proof
  ho_match_mp_tac flatten_exp_ind >> rw[flatten_exp_def]
  >- (every_case_tac >> gvs[SUBSET_DEF])
  >> gvs[SUBSET_DEF]
QED

Theorem rebuild_code_labels[local]:
  (∀sh i. get_code_labels (rebuild i sh) = {}) ∧
  (∀shs i. BIGUNION (set (MAP get_code_labels (rebuild_list i shs))) = {})
Proof
  Induct >> simp[rebuild_def, closLangTheory.assign_get_code_label_def]
  >> fs[BIGUNION_EQ_EMPTY] >> gen_tac
  >> first_x_assum (qspec_then ‘i + shape_width sh’ strip_assume_tac)
  >> simp[]
QED

Theorem worker_body_code_labels[local]:
  ∀csh fname next sh e.
    get_code_labels (worker_body csh fname next sh e) ⊆
    get_code_labels e ∪ {next} ∪ {wk | ∃d s. lookup d csh = SOME (s,wk)}
Proof
  ho_match_mp_tac worker_body_ind >> rw[worker_body_def]
  >> assume_tac (cj 1 flatten_exp_code_labels)
  >> every_case_tac >> gvs[SUBSET_DEF, MEM_MAP, MEM_GENLIST, PULL_EXISTS]
  >> rpt strip_tac >> res_tac >> gvs[MEM_MAP]
  >> metis_tac[]
QED

Theorem compile_prog_with_map_good_code_labels:
  ∀xs csh next n1 c1 ys.
    compile_prog_with_map csh next xs = ((n1,c1),ys) ∧
    BIGUNION (set (MAP (get_code_labels o SND o SND) xs)) ⊆ all ∧
    {next + k * bvl_to_bvi_namespaces | k |
       next + k * bvl_to_bvi_namespaces < n1} ⊆ all ∧
    (∀d sh wk. lookup d csh = SOME (sh,wk) ⇒ wk ∈ all) ⇒
    BIGUNION (set (MAP (get_code_labels o SND o SND) ys)) ⊆ all
Proof
  Induct >> simp[compile_prog_with_map_def]
  >> rpt gen_tac >> PairCases_on ‘h’
  >> simp[compile_prog_with_map_def]
  >> Cases_on ‘split_fun csh next h0 h1 h2’ >> simp[]
  >- (
    pairarg_tac >> simp[] >> strip_tac >> gvs[]
    >> last_x_assum irule >> metis_tac[])
  >> PairCases_on ‘x’ >> simp[] >> pairarg_tac >> simp[] >> strip_tac
  >> gvs[split_fun_def]
  >> drule compile_prog_with_map_next_mono >> strip_tac
  >> assume_tac bvl_to_bvi_namespaces_pos
  >> ‘next ∈ all’
    by (
      qpat_x_assum ‘{_ | k | _} ⊆ all’ mp_tac
      >> simp[SUBSET_DEF, PULL_EXISTS]
      >> disch_then (qspec_then ‘0’ mp_tac) >> simp[])
  >> rpt conj_tac
  >- simp[make_wrapper_def, rebuild_code_labels, SUBSET_DEF, MEM_MAP,
          MEM_GENLIST, PULL_EXISTS]
  >- (
    irule SUBSET_TRANS >> irule_at Any worker_body_code_labels
    >> gvs[SUBSET_DEF] >> metis_tac[])
  >> last_x_assum irule
  >> qpat_assum ‘compile_prog_with_map _ _ _ = _’ (irule_at Any)
  >> conj_tac
  >- (rw[lookup_insert] >> gvs[] >> res_tac)
  >> simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac
  >> qmatch_goalsub_rename_tac ‘next + (_ + j * _) ∈ _’
  >> qpat_x_assum ‘{_ | k | _} ⊆ all’ mp_tac
  >> simp[SUBSET_DEF, PULL_EXISTS]
  >> disch_then (qspec_then ‘j + 1’ mp_tac)
  >> simp[RIGHT_ADD_DISTRIB]
QED

Theorem compile_prog_good_code_labels:
  compile_prog b (n,csh) xs = ((n1,c1),ys) ∧
  BIGUNION (set (MAP (get_code_labels o SND o SND) xs)) ⊆ all ∧
  {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n1} ⊆ all ∧
  (∀d sh wk. lookup d csh = SOME (sh,wk) ⇒ wk ∈ all) ⇒
  BIGUNION (set (MAP (get_code_labels o SND o SND) ys)) ⊆ all
Proof
  rw[compile_prog_def] >> gvs[]
  >> metis_tac[compile_prog_with_map_good_code_labels]
QED

Theorem cons_tree_rebuild:
  (∀sh i. bvi_inline$cons_tree i (rebuild i sh) = SOME (i + shape_width sh)) ∧
  (∀shs i.
     bvi_inline$cons_trees i (rebuild_list i shs) =
     SOME (i + shape_width_list shs))
Proof
  Induct >> simp[rebuild_def, bvi_inlineTheory.cons_tree_def, shape_width_def]
QED

Theorem make_wrapper_wrapper_ok:
  wk ≠ d ⇒ bvi_inline$wrapper_ok d arity (make_wrapper arity wk sh)
Proof
  simp[make_wrapper_def, bvi_inlineTheory.wrapper_ok_def, cons_tree_rebuild]
QED
