
Theory bvi_cprProof
Ancestors
  bvi bviSem bviProps bvi_cpr backend_common[qualified]
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
  ∀m f arity body sh.
    map_ok m ∧ return_shape m f arity body = sh ∧ split_ok sh ⇒
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

        
Definition map_inv_def:
  map_inv m next ⇔
    map_ok m ∧
    (∀d dsh dwk. lookup d m = SOME (dsh,dwk) ⇒ d < next ∧ dwk < next) ∧
    (∀d1 d2 s1 s2 w.
       lookup d1 m = SOME (s1,w) ∧ lookup d2 m = SOME (s2,w) ⇒ d1 = d2)
End

Theorem map_inv_submap:
  map_ok m ∧ submap m m' ∧ map_inv m' n ⇒ map_inv m n
Proof
  rw[submap_def, map_inv_def]
  >- (last_x_assum $ drule_then assume_tac >> gvs[]
     )
  >- (last_x_assum $ drule_then assume_tac >> gvs[]
      >> last_x_assum $ drule_then assume_tac >> gvs[]
     )
  >> first_x_assum $ irule
  >> metis_tac[]
QED

Definition prog_keys_ok_def:
  prog_keys_ok (next:num) prog ⇔
    ALL_DISTINCT (MAP FST prog) ∧
    EVERY (λ(loc,arity,e). loc < next) prog
End
   
Definition fun_rel_def:
  fun_rel m2 prog2 (loc,arity,e) ⇔
    case lookup loc m2 of
      NONE => MEM (loc,arity,e) prog2
    | SOME (sh,wk) =>
        ∃m'. submap m' m2 ∧ map_ok m' ∧
             return_shape m' loc arity e = sh ∧ split_ok sh ∧ tail_form e ∧
             MEM (loc,arity,make_wrapper arity wk sh) prog2 ∧
             MEM (wk,arity,worker_body m' loc wk sh e) prog2
End

Theorem split_fun_map_ok:
  ∀m next loc arity body wkb wrap m'.
    map_ok m ∧ split_fun m next loc arity body = SOME (wkb,wrap,m') ⇒
    ∃sh. m' = insert loc (sh,next) m ∧
         return_shape m loc arity body = sh ∧ split_ok sh ∧ flex_free sh ∧
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

Theorem compile_prog_with_map_fun_greater:
  ∀m next prog n r.
    compile_prog_with_map m next prog = (n,r) ⇒
    next ≤ n ∧
    ∀q. ¬MEM q (MAP FST prog) ∧ MEM q (MAP FST r) ⇒ next ≤ q
Proof
  Induct_on ‘prog’ >> rw[compile_prog_with_map_def]
  >- (Cases_on ‘h’ >> Cases_on ‘r'’ >> gvs[compile_prog_with_map_def]
      >> Cases_on ‘split_fun m next q q' r''’ >> gvs[]
      >- (Cases_on ‘compile_prog_with_map m next prog’ >> gvs[]
          >> first_x_assum $ drule_then assume_tac >> gvs[]
         )
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘r'’ >> gvs[]
      >> Cases_on ‘compile_prog_with_map r'³' (next + bvl_to_bvi_namespaces) prog’ >> gvs[]
      >> first_x_assum $ drule_then assume_tac >> gvs[]
     )
  >> Cases_on ‘h’ >> Cases_on ‘r'’ >> gvs[compile_prog_with_map_def]
  >> Cases_on ‘split_fun m next q' q'' r''’ >> gvs[]
  >- (Cases_on ‘compile_prog_with_map m next prog’ >> gvs[]
      >> first_x_assum $ drule_then assume_tac >> gvs[]
     )
  >> Cases_on ‘x’ >> gvs[]
  >> Cases_on ‘r'’ >> gvs[]
  >> Cases_on ‘compile_prog_with_map r'³' (next + bvl_to_bvi_namespaces) prog’ >> gvs[]
  >> first_x_assum $ drule_then assume_tac >> gvs[]
  >> pop_assum $ drule_all_then assume_tac >> gvs[]
QED

Theorem compile_prog_with_map_thm:
  ∀prog m next n prog2.
    compile_prog_with_map m next prog = (n,prog2) ∧
    map_inv m next ∧ prog_keys_ok next prog ∧
    (∀loc arity e. MEM (loc,arity,e) prog ⇒ lookup loc m = NONE) ⇒
    ∃m2.
      submap m m2 ∧ map_inv m2 n ∧ next ≤ n ∧
      ALL_DISTINCT (MAP FST prog2) ∧
      EVERY (fun_rel m2 prog2) prog ∧
      (∀loc arity e.
         MEM (loc,arity,e) prog2 ⇒
         (∃e'. MEM (loc,arity,e') prog) ∨
         ∃f fsh. lookup f m2 = SOME (fsh,loc)) ∧
      (∀d sh wk.
         lookup d m2 = SOME (sh,wk) ∧ lookup d m = NONE ⇒
         MEM d (MAP FST prog) ∧ next ≤ wk)
Proof
  Induct >> rw[]
  >- (gvs[compile_prog_with_map_def]
      >> last_x_assum $ irule_at Any
      >> gvs[submap_def]
     )
  >> Cases_on ‘h’ >> Cases_on ‘r’
  >> gvs[compile_prog_with_map_def, prog_keys_ok_def]
  >> Cases_on ‘split_fun m next q q' r'’ >> gvs[]
  >~ [‘NONE’]
  >- suspend "NONE"
  >~ [‘SOME _’]
  >- suspend "SOME"
QED



Resume compile_prog_with_map_thm[NONE]:
  Cases_on ‘compile_prog_with_map m next prog’ >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[]
  >> pop_assum mp_tac >> impl_tac
  >- (rpt strip_tac
      >> first_x_assum $ irule
      >> metis_tac[]
     )
  >> rpt strip_tac
  >> rw[]
  >> drule_then assume_tac compile_prog_with_map_fun_greater
  >> gvs[]
  >> pop_assum $ qspec_then ‘q’ assume_tac >> gvs[]
  >> qexists ‘m2’ >> gvs[]
  >> conj_tac
  >- (conj_tac
      >- (gvs[fun_rel_def]
          >> Cases_on ‘lookup q m2’ >> gvs[]
          >> every_case_tac >> gvs[]
         )
      >> gvs[EVERY_MEM]
      >> rpt strip_tac
      >> first_x_assum $ drule_then assume_tac >> gvs[]
      >> Cases_on ‘e’ >> Cases_on ‘r''’
      >> gvs[fun_rel_def]
      >> Cases_on ‘lookup q'' m2’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> qexists ‘m'’ >> gvs[]
     )
  >> rw[]
  >- metis_tac[]
  >- (first_x_assum $ qspecl_then [‘loc’, ‘arity’, ‘e’] assume_tac >> gvs[]
      >- metis_tac[]
      >> metis_tac[]
     )
  >- metis_tac[]
  >> metis_tac[]
QED

        
Resume compile_prog_with_map_thm[SOME]:
  Cases_on ‘x’ >> gvs[]
  >> Cases_on ‘r’ >> gvs[]
  >> Cases_on ‘compile_prog_with_map r'' (next + bvl_to_bvi_namespaces) prog’ >> gvs[]
  >> ‘map_ok m’ by gvs[map_inv_def]
  >> drule_all_then assume_tac split_fun_map_ok
  >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[]
  >> pop_assum mp_tac >> impl_keep_tac
  >- (conj_tac
      >- (fs[map_inv_def]
          >> conj_tac
          >- (rpt gen_tac >> strip_tac
              >> gvs[lookup_insert]
              >> Cases_on ‘d = q’
              >> gvs[backend_commonTheory.bvl_to_bvi_namespaces_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
             )
          >> rpt gen_tac >> strip_tac
          >> gvs[lookup_insert]
          >> Cases_on ‘d1 = q’ >> gvs[]
          >- (Cases_on ‘d2 = d1’ >> gvs[]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
             )
          >> Cases_on ‘d2 = q’ >> gvs[]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
         )
      >> conj_tac
      >- (gvs[EVERY_MEM]
          >> rpt strip_tac
          >> last_x_assum $ drule_then assume_tac
          >> Cases_on ‘e’ >> gvs[]
         )
      >> rpt strip_tac
      >> rw[lookup_insert]
      >- (CCONTR_TAC >> gvs[MEM_MAP]
         )
      >> last_x_assum $ irule
      >> metis_tac[]
     )
  >> rpt strip_tac >> gvs[]
  >> drule_then assume_tac compile_prog_with_map_fun_greater
  >> gvs[]
  >> first_assum $ qspec_then ‘q’ $ drule_then assume_tac
  >> Cases_on ‘MEM q (MAP FST r)’ >> fs[]
  >> first_x_assum $ qspec_then ‘next’ assume_tac
  >> gvs[]
  >> subgoal ‘¬MEM next (MAP FST prog)’
  >- (gvs[EVERY_MEM, MEM_MAP]
      >> rpt strip_tac
      >> last_x_assum $ drule_then assume_tac
      >> Cases_on ‘y’ >> gvs[]
     )
  >> first_x_assum $ drule_then assume_tac >> gvs[]
  >> Cases_on ‘MEM next (MAP FST r)’ >> gvs[]
  >- fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
  >> first_assum $ irule_at Any
  >> conj_asm1_tac
  >- (irule submap_trans
      >> first_assum $ irule_at Any
      >> irule submap_insert
      >> rw[]
     )
  >> conj_tac
  >- (subgoal ‘lookup q m2 = SOME (return_shape m q q' r',next)’
      >- gvs[submap_def]
      >> rw[fun_rel_def]
      >> qexists ‘m’
      >> gvs[]
     )
  >> conj_tac
  >- (rw[EVERY_MEM]
      >> subgoal ‘fun_rel m2 r e’
      >- gvs[EVERY_MEM]
      >> Cases_on ‘e’ >> gvs[]
      >> Cases_on ‘r''’ >> gvs[fun_rel_def]
      >> Cases_on ‘lookup q'' m2’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> metis_tac[]
     )
  >> conj_tac
  >- (rw[]
      >- metis_tac[]
      >- (disj2_tac
          >> gvs[submap_def]
          >> last_x_assum $
                          qspecl_then [‘q’, ‘(return_shape m q arity r', loc)’] assume_tac
          >> gvs[lookup_insert]
          >> metis_tac[]
         )
      >> metis_tac[]
     )
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘d = q’ >> gvs[]
  >- (‘lookup d m2 = SOME (return_shape m d q' r',next)’ by gvs[submap_def]
      >> gvs[]
     )
  >> first_x_assum $ drule_then assume_tac
  >> pop_assum mp_tac >> impl_tac
  >- gvs[lookup_insert]
  >> rw[]
QED

Finalise compile_prog_with_map_thm; 
        



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
               return_shape m' d arity body = sh ∧ split_ok sh ∧
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
                return_shape m' d arity body = sh ∧ split_ok sh ∧
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


Definition oracle_free_def:
  oracle_free s ⇔ ∀n. SND (s.compile_oracle n) = []
End

Definition state_rel_def:
  state_rel m s t ⇔
    code_rel m s.code t.code ∧
    s.refs = t.refs ∧ s.global = t.global ∧ s.ffi = t.ffi ∧
    s.compile = t.compile ∧ s.compile_oracle = t.compile_oracle ∧
    oracle_free s
End

Theorem state_rel_clock:
  ∀m s t k.
    state_rel m s t ⇒
    state_rel m (s with clock := k) t ∧ state_rel m s (t with clock := k)
Proof
  rw[state_rel_def, oracle_free_def]
  >> gvs[]
QED

Theorem state_rel_inc_clock:
  ∀m s t k. state_rel m s t ⇒ state_rel m s (inc_clock k t)
Proof
  rw[inc_clock_def] >> irule $ cj 2 state_rel_clock
  >> first_assum $ irule_at Any
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

Theorem cpr_correct:
  ∀xs env s.
    (∀m t res s1.
       state_rel m s t ∧
       evaluate (xs,env,s) = (res,s1) ∧
       res ≠ Rerr (Rabort Rtype_error) ∧ res ≠ Rerr (Rabort Rtimeout_error) ⇒
       ∃ck t1.
         state_rel m s1 t1 ∧
         evaluate (xs,env,inc_clock ck t) = (res,t1)) ∧
    (∀m t e f wk sh res s1.
       xs = [e] ∧ state_rel m s t ∧
       lookup f m = SOME (sh,wk) ∧ split_ok sh ∧
       tail_ok m f sh e ∧ tail_form e ∧
       evaluate ([e],env,s) = (res,s1) ∧
       res ≠ Rerr (Rabort Rtype_error) ∧ res ≠ Rerr (Rabort Rtimeout_error) ⇒
       ∃ck t1.
         state_rel m s1 t1 ∧
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
  recInduct evaluate_ind
  >> rpt conj_tac
         
  >- (rw[evaluate_def]
      >> qexists ‘0’ >> gvs[inc_clock_def, state_rel_def]
     )
  >- (rw[evaluate_def]
      >> Cases_on ‘evaluate ([x],env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then assume_tac
          >> gvs[no_ret_def]
          >> qexistsl [‘ck’,‘t1’] >> gvs[inc_clock_def]
         )
      >> Cases_on ‘evaluate (y::xs,env,r)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[no_ret_def]
      >- (last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> first_assum $ irule_at Any
          >> qpat_x_assum ‘evaluate ([_], _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexists ‘ck + ck'’ >> gvs[inc_clock_def]
         )
      >> last_x_assum $ drule_then assume_tac
      >> gvs[]
      >> last_x_assum $ drule_then assume_tac
      >> gvs[]
      >> first_assum $ irule_at Any
      >> qpat_x_assum ‘evaluate ([_], _, inc_clock _ _) = _’ $ assume_tac
      >> drule_then assume_tac evaluate_add_clock
      >> gvs[]
      >> pop_assum $ qspec_then ‘ck'’ assume_tac
      >> qexists ‘ck + ck'’ >> gvs[inc_clock_def]
     )
  >- (rw[evaluate_def]
      >- (qexists ‘0’ >> gvs[inc_clock_def, state_rel_def]
         )
      >> qexistsl [‘0’,‘t’] >> gvs[inc_clock_def, state_rel_def]
      >> imp_res_tac split_ok_ConsShape
      >> gvs[tail_ok_def, exp_shape_ok_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
          >> reverse $ Cases_on ‘q’ >> gvs[no_ret_def]
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck’,‘t1’] >> gvs[inc_clock_def]
             )
          >> Cases_on ‘HD a = Boolv T’ >> gvs[]
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
              >> drule_then assume_tac evaluate_add_clock
              >> gvs[]
              >> pop_assum $ qspec_then ‘ck'’ assume_tac
              >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
             )
          >> Cases_on ‘HD a = Boolv F’ >> gvs[]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >> Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[no_ret_def, tail_ok_def, tail_form_def]
      >- (gvs[worker_body_def, evaluate_def]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> qexistsl [‘ck’,‘t1’] >> gvs[inc_clock_def]
         )
      >> Cases_on ‘HD a = Boolv T’ >> gvs[]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[x2]’, ‘env’, ‘r’] assume_tac
      >> gvs[]
      >> Cases_on ‘res’ >> gvs[]
      >- (Cases_on ‘a'’ >> gvs[]
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x1]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac no_ret_tail_form
          >> gvs[]
          >> last_x_assum $ drule_then assume_tac >> gvs[]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[evaluate_def, worker_body_def]
          >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >- (last_x_assum $ drule_then assume_tac >> gvs[]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[evaluate_def, worker_body_def]
          >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >- (Cases_on ‘HD a = Boolv F’ >> gvs[]
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x1]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x3]’, ‘env’, ‘r’] assume_tac
          >> gvs[]
          >> Cases_on ‘a'’ >> gvs[]
          >> last_x_assum $ drule_then assume_tac >> gvs[]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[evaluate_def, worker_body_def]
          >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >> Cases_on ‘HD a = Boolv F’ >> gvs[]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[x1]’, ‘env’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘a’ >> gvs[]
      >> last_x_assum $ drule_then assume_tac >> gvs[]
      >> first_x_assum $ drule_all_then assume_tac
      >> gvs[evaluate_def, worker_body_def]
      >> qpat_x_assum ‘evaluate ([x1], _, inc_clock _ _) = _’ $ assume_tac
      >> drule_then assume_tac evaluate_add_clock
      >> gvs[]
      >> pop_assum $ qspec_then ‘ck'’ assume_tac
      >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[no_ret_def]
          >> reverse $ Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck’, ‘t1’] >> gvs[]
             )
          >> Cases_on ‘res’ >> gvs[]
          >- (assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[x2]’, ‘a ++ env’, ‘r’] assume_tac
              >> gvs[]
              >> Cases_on ‘a'’ >> gvs[]
              >> last_x_assum $ drule_then assume_tac >> gvs[]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[evaluate_def, worker_body_def]
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ $ assume_tac
              >> drule_then assume_tac evaluate_add_clock
              >> gvs[]
              >> pop_assum $ qspec_then ‘ck'’ assume_tac
              >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
             )
          >> last_x_assum $ drule_then assume_tac >> gvs[]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[evaluate_def, worker_body_def]
          >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[no_ret_def]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then assume_tac
          >> gvs[tail_form_def, worker_body_def, evaluate_def]
          >> qexistsl [‘ck’, ‘t1’] >> gvs[]
         )
      >> Cases_on ‘res’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x2]’, ‘a ++ env’, ‘r’] assume_tac
          >> gvs[]
          >> Cases_on ‘a'’ >> gvs[tail_form_def, tail_ok_def]
          >> first_x_assum $ drule_then assume_tac >> gvs[]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[evaluate_def, worker_body_def]
          >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> gvs[]
          >> pop_assum $ qspec_then ‘ck'’ assume_tac
          >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
         )
      >> first_x_assum $ drule_then assume_tac >> gvs[tail_form_def, tail_ok_def]
      >> first_x_assum $ drule_all_then assume_tac
      >> gvs[evaluate_def, worker_body_def]
      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ $ assume_tac
      >> drule_then assume_tac evaluate_add_clock
      >> gvs[]
      >> pop_assum $ qspec_then ‘ck'’ assume_tac
      >> qexistsl [‘ck + ck'’,‘t1'’] >> gvs[inc_clock_def]
   )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate ([x1],env,s)’ >> gvs[no_ret_def]
          >> reverse $ Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[tail_form_def, worker_body_def, evaluate_def]
              >> qexistsl [‘ck’, ‘t1’] >> gvs[]
             )
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x1]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> last_x_assum $ drule_then assume_tac >> gvs[]
          >> qexistsl [‘ck’, ‘t1’] >> gvs[]
         )
      >> Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then assume_tac
          >> gvs[tail_form_def, worker_body_def, evaluate_def, no_ret_def]
          >> qexistsl [‘ck’, ‘t1’] >> gvs[]
         )
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[x1]’, ‘env’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘a’ >> gvs[]
      >> last_x_assum $ drule_then assume_tac >> gvs[tail_form_def, worker_body_def, evaluate_def, no_ret_def]
      >> qexistsl [‘ck’, ‘t1’] >> gvs[]
     )
  >- (rw[evaluate_def, no_ret_def, tail_form_def, tail_ok_def, exp_shape_ok_def]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then assume_tac
          >> gvs[tail_form_def, worker_body_def, evaluate_def, no_ret_def]
          >> qexistsl [‘ck’, ‘t1’] >> gvs[]
         )
      >> last_x_assum $ drule_then assume_tac
      >> gvs[tail_form_def, worker_body_def, evaluate_def, no_ret_def]
      >> qexistsl [‘ck’, ‘t1’] >> gvs[]
     )
  >- (rpt gen_tac >> strip_tac
      >> conj_asm1_tac
      >- (rw[evaluate_def, no_ret_def, tail_form_def, tail_ok_def, exp_shape_ok_def]
          >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> reverse $ Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[tail_form_def, worker_body_def, evaluate_def, no_ret_def]
              >> qexistsl [‘ck’, ‘t1’] >> gvs[]
             )
          >> Cases_on ‘op’ >> gvs[]
          >~ [‘Label’]
          >- (gvs[do_app_def, do_app_aux_def]
              >> every_case_tac >> gvs[]
              >- (assume_tac evaluate_LENGTH
                  >> pop_assum $ qspecl_then [‘xs’, ‘env’, ‘s’] assume_tac
                  >> gvs[evaluate_def, bvlSemTheory.do_app_def]
                  >> every_case_tac >> gvs[]
                  >> qpat_x_assum ‘state_rel _ _ _’ $ assume_tac o SRULE [state_rel_def, code_rel_def]
                  >> gvs[domain_lookup]
                  >> Cases_on ‘v’ >> gvs[]
                  >> first_x_assum $ drule_then assume_tac
                  >> Cases_on ‘lookup n m’ >> gvs[]
                  >> Cases_on ‘x’ >> gvs[]
                 )
              >>  assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘xs’, ‘env’, ‘s’] assume_tac
              >> gvs[evaluate_def, bvlSemTheory.do_app_def]
             )
          >~ [‘Install’]
          >- (gvs[do_app_def, do_app_aux_def, do_install_def]
              >> every_case_tac >> gvs[]
              >- (Cases_on ‘r.compile_oracle 0’ >> gvs[]
                  >> every_case_tac >> gvs[]
                  >> last_x_assum $ drule_then assume_tac >> gvs[]
                  >> qpat_x_assum ‘state_rel m r _’ $ assume_tac o SRULE[state_rel_def]
                  >> gvs[oracle_free_def]
                  >> pop_assum $ qspec_then ‘0’ assume_tac >> gvs[]
                 )
              >> Cases_on ‘r.compile_oracle 0’ >> gvs[]
              >> every_case_tac >> gvs[]
              >> last_x_assum $ drule_then assume_tac >> gvs[]
              >> qpat_x_assum ‘state_rel m r _’ $ assume_tac o SRULE[state_rel_def]
              >> gvs[oracle_free_def]
              >> pop_assum $ qspec_then ‘0’ assume_tac >> gvs[]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
              >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                     bvl_to_bvi_id, oracle_free_def]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
              >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                     bvl_to_bvi_id, oracle_free_def]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
              >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                     bvl_to_bvi_id, oracle_free_def]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
              >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                     bvl_to_bvi_id, oracle_free_def]
              >> Cases_on ‘do_build_const l t1.refs’
              >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                     bvl_to_bvi_id, oracle_free_def]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
              >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                     bvl_to_bvi_id, oracle_free_def]
              >> Cases_on ‘t1.global’ >> gvs[]
             )
          >- (last_x_assum $ drule_then assume_tac
              >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
              >> qexists ‘ck’
              >> rpt (full_case_tac >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                           bvl_to_bvi_id, oracle_free_def])
             )  
          >> last_x_assum $ drule_then assume_tac
          >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
          >> every_case_tac >> gvs[bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi, bvl_to_bvi_id]
          >> qexists ‘ck’ >> gvs[state_rel_def, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
                                 bvl_to_bvi_id, oracle_free_def]
         )
      >> rw[evaluate_def, no_ret_def, tail_form_def, tail_ok_def, exp_shape_ok_def]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[Op op xs]’, ‘env’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘res’ >> gvs[]
      >- (Cases_on ‘a’ >> gvs[no_ret_def, tail_form_def]
          >> first_x_assum $ drule_then assume_tac >> gvs[tail_ok_def]
          >> drule_all_then assume_tac $ cj 1 evaluate_flatten_exp
          >> gvs[]
          >> rw[Once evaluate_def, worker_body_def]
          >> qexistsl [‘ck’, ‘t1’] >> gvs[]
         )
      >> first_x_assum $ drule_then assume_tac >> gvs[tail_ok_def, no_ret_def, tail_form_def]
      >> drule_all_then assume_tac $ cj 1 evaluate_flatten_exp_err
      >> rw[Once evaluate_def, worker_body_def]
      >> qexistsl [‘ck’, ‘t1’] >> gvs[]
     )
  >- (rw[evaluate_def]
      >- (gvs[dec_clock_def, no_ret_def]
          >> drule_then assume_tac $ cj 1 state_rel_clock
          >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def]
         )
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘[x]’, ‘env’, ‘dec_clock 1 s’] assume_tac
      >> gvs[]
      >> reverse $ Cases_on ‘res’ >> gvs[no_ret_def]
      >- (gvs[dec_clock_def, no_ret_def]
          >> drule_then assume_tac $ cj 1 state_rel_clock
          >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac
          >> first_x_assum $ drule_then assume_tac
          >> gvs[]
          >> first_x_assum $ drule_then assume_tac
          >> gvs[tail_ok_def, tail_form_def]
          >> rw[worker_body_def, evaluate_def]
          >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def, dec_clock_def]
         ) 
      >> Cases_on ‘a’ >> gvs[tail_form_def, tail_ok_def]
      >> gvs[dec_clock_def, no_ret_def]
      >> drule_then assume_tac $ cj 1 state_rel_clock
      >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac
      >> first_x_assum $ drule_then assume_tac
      >> gvs[tail_form_def]
      >> first_x_assum $ drule_then assume_tac
      >> gvs[]
      >> rw[worker_body_def, evaluate_def]
      >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def, dec_clock_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘dest_thunk env❲n❳ s.refs’ >> gvs[]
          >> ‘dest_thunk env❲n❳ t.refs = dest_thunk env❲n❳ s.refs’ by gvs[state_rel_def]
          >> gvs[]
          >> Cases_on ‘t'’ >> gvs[]
          >- metis_tac[inc_clock_def, state_rel_clock]
          >> Cases_on ‘find_code (SOME force_loc) [env❲n❳; v] s.code’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> ‘code_rel m s.code t.code’ by gvs[state_rel_def]
          >> Cases_on ‘lookup force_loc m’ >> gvs[]
          >- (drule_all_then assume_tac code_rel_find_code_NONE
              >> gvs[]
              >> Cases_on ‘s.clock = 0’ >> gvs[]
              >> Cases_on ‘evaluate ([r],q,dec_clock 1 s)’ >> gvs[]
              >> reverse $ Cases_on ‘q'’ >> gvs[]
              >- (Cases_on ‘e’ >> gvs[]
                  >- (Cases_on ‘a’ >> gvs[dec_clock_def, no_ret_def]
                      >> drule_then assume_tac $ cj 1 state_rel_clock
                      >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def]
                     )
                  >> drule_then assume_tac $ cj 1 state_rel_clock
                  >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac >> gvs[dec_clock_def]
                  >> last_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def]
                 )
              >> drule_then assume_tac $ cj 1 state_rel_clock
              >> pop_assum $ qspec_then ‘s.clock - 1’ assume_tac >> gvs[dec_clock_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck + 1’, ‘t1’] >> gvs[inc_clock_def]
             )
          >> Cases_on ‘x’ >> gvs[]
          >> drule_all_then assume_tac code_rel_find_code_lookup
          >> Cases_on ‘s.clock = 0’ >> gvs[]
          >> Cases_on ‘evaluate ([r],q,dec_clock 1 s)’ >> gvs[]
          >> Cases_on ‘lookup d m’ >> gvs[]
          >- (reverse $ Cases_on ‘q''’ >> gvs[]
              >- (Cases_on ‘e’ >> gvs[]
                  >- (Cases_on ‘a’ >> gvs[]
                      >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> qexistsl [‘ck + 1’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
                  >> last_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> qexistsl [‘ck + 1’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
                 )
              >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck + 1’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
             )
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘q''’ >> gvs[]
          >- (assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[r]’, ‘q’, ‘dec_clock 1 s’] assume_tac
              >> gvs[]
              >> Cases_on ‘a’ >> gvs[]
              >> rw[make_wrapper_def, evaluate_def]
              >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                               (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
              >- (irule evaluate_genlist_vars
                  >> gvs[]
                 )
              >> pop_assum $ assume_tac o SRULE[]
              >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
              >> gvs[bvlSemTheory.find_code_def, dec_clock_def, inc_clock_def]
              >> ‘state_rel m (s with clock := s.clock − 1) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck + 2’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
              >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
              >> gvs[]
              >> ‘evaluate ([rebuild 0 q'³'],flat_vals q'³' h ++ q,t1) = (Rval [h],t1)’ suffices_by rw[]
              >> irule $ cj 1 evaluate_rebuild
              >> rw[]
              >> DEP_REWRITE_TAC [TAKE_APPEND1]
              >> rw[]
             )
          >> Cases_on ‘e’ >> gvs[]
          >- (Cases_on ‘a’ >> gvs[]
              >> rw[make_wrapper_def, evaluate_def]
              >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                               (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
              >- (irule evaluate_genlist_vars
                  >> gvs[]
                 )
              >> pop_assum $ assume_tac o SRULE[]
              >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
              >> gvs[bvlSemTheory.find_code_def, dec_clock_def, inc_clock_def]
              >> ‘state_rel m (s with clock := s.clock − 1) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck + 2’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
             )
          >> rw[make_wrapper_def, evaluate_def]
          >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                           (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
          >- (irule evaluate_genlist_vars
              >> gvs[]
             )
          >> pop_assum $ assume_tac o SRULE[]
          >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
          >> gvs[bvlSemTheory.find_code_def, dec_clock_def, inc_clock_def]
          >> ‘state_rel m (s with clock := s.clock − 1) t’ by gvs[state_rel_def, dec_clock_def, oracle_free_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> qexistsl [‘ck + 2’,‘t1’] >> gvs[inc_clock_def, dec_clock_def]
         )
      >> drule_then assume_tac split_ok_ConsShape
      >> gvs[tail_ok_def, exp_shape_ok_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (Cases_on ‘find_code dest a r.code’ >> gvs[]
              >> Cases_on ‘x’ >> gvs[]
              >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
              >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
              >> Cases_on ‘q'’ >> gvs[]
              >- (assume_tac evaluate_LENGTH
                  >> pop_assum $ qspecl_then [‘[r']’, ‘q’, ‘dec_clock (ticks + 1) r’] assume_tac
                  >> gvs[]
                  >> Cases_on ‘a'’ >> gvs[]
                  >> first_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                  >> drule_all_then assume_tac code_rel_find_code_lookup
                  >> gvs[]
                  >> Cases_on ‘lookup d m’ >> gvs[]
                  >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> Cases_on ‘x’ >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                  >> first_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                  >> first_assum $ irule_at Any
                  >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ticks + 2 + ck'’ assume_tac) evaluate_add_clock
                  >> gvs[]
                  >> qexists ‘ck + ticks + 2 + ck'’ >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                                   (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> gvs[bvlSemTheory.find_code_def]
                  >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
                  >> gvs[]
                  >> ‘evaluate ([rebuild 0 q'],flat_vals q' h ++ q,t1') = (Rval [h],t1')’ suffices_by rw[]
                  >> irule $ cj 1 evaluate_rebuild
                  >> rw[]
                  >> DEP_REWRITE_TAC [TAKE_APPEND1]
                  >> rw[]
                 )
              >> Cases_on ‘e’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> Cases_on ‘handler’ >> gvs[]
                  >- (first_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                      >> drule_all_then assume_tac code_rel_find_code_lookup
                      >> gvs[]
                      >> Cases_on ‘lookup d m’ >> gvs[]
                      >- (qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                          >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
                          >> gvs[]
                          >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def]
                         )
                      >> Cases_on ‘x’ >> gvs[]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_all_then assume_tac
                      >> gvs[]                                                
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 2 + ck''’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 2 + ck''’ >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                                       (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
                      >> gvs[]
                     )
                  >> Cases_on ‘evaluate ([x],v::env,r'')’ >> gvs[]
                  >> Cases_on ‘q'’ >> gvs[]
                  >- (assume_tac evaluate_LENGTH
                      >> pop_assum $ qspecl_then [‘[x]’, ‘v::env’, ‘r''’] assume_tac
                      >> gvs[]
                      >> Cases_on ‘a'’ >> gvs[] 
                      >> first_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                      >> drule_all_then assume_tac code_rel_find_code_lookup
                      >> gvs[]
                      >> Cases_on ‘lookup d m’ >> gvs[]
                      >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                          >> first_x_assum $ drule_all_then assume_tac
                          >> gvs[]
                          >> last_x_assum $ drule_then assume_tac
                          >> gvs[]
                          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def,
                                                                               oracle_free_def, inc_clock_def]
                          >> last_x_assum $ drule_then assume_tac
                          >> gvs[]
                          >> first_assum $ irule_at Any
                          >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                          >> drule_then (qspec_then ‘ticks + 1 + ck' + ck''’ assume_tac) evaluate_add_clock
                          >> gvs[]
                          >> qexists ‘ck + ticks + 1 + ck' + ck''’ >> gvs[inc_clock_def, dec_clock_def]
                          >> qpat_x_assum ‘evaluate ([r'], _, t1 with clock := _) = _’ assume_tac
                          >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                          >> gvs[inc_clock_def, dec_clock_def]
                         )
                      >> Cases_on ‘x'’ >> gvs[]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac
                      >> gvs[]
                      >> last_x_assum $ drule_all_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 2 + ck' + ck''’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 2 + ck' + ck''’
                      >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                                       (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> qpat_x_assum ‘evaluate ([worker_body m d r'⁴' q' r'], _, t1 with clock := _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                      >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> Cases_on ‘e’ >> gvs[]
                  >- (Cases_on ‘a'’ >> gvs[]
                      >> first_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                      >> drule_all_then assume_tac code_rel_find_code_lookup
                      >> gvs[]
                      >> Cases_on ‘lookup d m’ >> gvs[]
                      >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                          >> first_x_assum $ drule_all_then assume_tac
                          >> gvs[]
                          >> last_x_assum $ drule_then assume_tac
                          >> gvs[]
                          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def,
                                                                               oracle_free_def, inc_clock_def]
                          >> last_x_assum $ drule_then assume_tac
                          >> gvs[]
                          >> first_assum $ irule_at Any
                          >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                          >> drule_then (qspec_then ‘ticks + 1 + ck' + ck''’ assume_tac) evaluate_add_clock
                          >> gvs[]
                          >> qexists ‘ck + ticks + 1 + ck' + ck''’ >> gvs[inc_clock_def, dec_clock_def]
                          >> qpat_x_assum ‘evaluate ([r'], _, t1 with clock := _) = _’ assume_tac
                          >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                          >> gvs[inc_clock_def, dec_clock_def]
                         )
                      >> Cases_on ‘x'’ >> gvs[]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac
                      >> gvs[]
                      >> last_x_assum $ drule_all_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 2 + ck' + ck''’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 2 + ck' + ck''’
                      >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                                       (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> qpat_x_assum ‘evaluate ([worker_body m d r'⁴' q' r'], _, t1 with clock := _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                      >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> first_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                  >> drule_all_then assume_tac code_rel_find_code_lookup
                  >> gvs[]
                  >> Cases_on ‘lookup d m’ >> gvs[]
                  >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac
                      >> gvs[]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def,
                                                                           oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 1 + ck' + ck''’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 1 + ck' + ck''’ >> gvs[inc_clock_def, dec_clock_def]
                      >> qpat_x_assum ‘evaluate ([r'], _, t1 with clock := _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                      >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> Cases_on ‘x'’ >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                  >> first_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                  >> last_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                  >> first_assum $ irule_at Any
                  >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ticks + 2 + ck' + ck''’ assume_tac) evaluate_add_clock
                  >> gvs[]
                  >> qexists ‘ck + ticks + 2 + ck' + ck''’
                  >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                                   (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> gvs[bvlSemTheory.find_code_def]
                  >> qpat_x_assum ‘evaluate ([worker_body m d r'⁴' q' r'], _, t1 with clock := _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                  >> gvs[inc_clock_def, dec_clock_def]
                 )
              >> first_x_assum $ drule_then assume_tac
              >> gvs[]
              >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then assume_tac code_rel_find_code_lookup
              >> gvs[]
              >> Cases_on ‘lookup d m’ >> gvs[]
              >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                  >> last_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
                  >> gvs[]
                  >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def]
                 )
              >> Cases_on ‘x’ >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 2 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 2 + ck'’
              >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
              >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH q), q, t) =
                                               (Rval (TAKE (LENGTH q) (DROP 0 q)), t)’
              >- (irule evaluate_genlist_vars
                  >> gvs[]
                 )
              >> pop_assum $ assume_tac o SRULE[]
              >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
              >> gvs[bvlSemTheory.find_code_def]
             )
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> first_assum $ irule_at Any
          >> qexists ‘ck’ >> gvs[]
         )
      >> Cases_on ‘evaluate (xs,env,s1)’ >> fs[]
      >> reverse $ Cases_on ‘q’ >> fs[]
      >- (gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def, no_ret_def]
          >> reverse $ Cases_on ‘handler’ >> gvs[]
          >- (rw[evaluate_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexists ‘ck’ >> gvs[]
             )
          >> Cases_on ‘dest’ >> gvs[]
          >- (rw[evaluate_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexists ‘ck’ >> gvs[]
             )
          >> Cases_on ‘f = x’ >> gvs[]
          >- (rw[evaluate_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexists ‘ck’ >> gvs[]
             )
          >> full_case_tac >> gvs[]
          >- (rw[evaluate_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexists ‘ck’ >> gvs[]
             )
          >> full_case_tac >> gvs[]
          >> rw[evaluate_def]
          >> last_x_assum $ drule_then assume_tac
          >> gvs[]
          >> qexists ‘ck’ >> gvs[]
         )
      >> Cases_on ‘find_code dest a r.code’ >> fs[]                                  
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[r']’, ‘q’, ‘dec_clock (ticks + 1) r’] assume_tac
          >> gvs[]
          >> Cases_on ‘a'’ >> gvs[tail_ok_def, tail_form_def, no_ret_def, tail_ok_def]
          >> rw[worker_body_def, evaluate_def]
          >> first_x_assum $ drule_then assume_tac
          >> gvs[]
          >> Cases_on ‘handler’ >> gvs[tail_ok_def, split_ok_def, shape_width_def]
          >- (‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> rw[evaluate_def]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
              >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
              >> gvs[]
              >> DEP_REWRITE_TAC[evaluate_genlist_prefix]
              >> gvs[]
             )
          >> Cases_on ‘f = d’ >> gvs[]
          >- (‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> rw[evaluate_def]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
              >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
              >> gvs[]
              >> DEP_REWRITE_TAC[evaluate_genlist_prefix]
              >> gvs[]
             )
          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
          >> gvs[]
          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
            gvs[state_rel_def, dec_clock_def, oracle_free_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> first_assum $ irule_at Any
          >> qexists ‘ck + ck' + 1 + ticks’
          >> irule evaluate_TailCall
          >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> pop_assum $ qspec_then ‘ck' + 1 + ticks’ assume_tac
          >> ‘inc_clock (ck' + 1 + ticks) (inc_clock ck t) =
              inc_clock (ck + ck' + 1 + ticks) t’ by
            gvs[inc_clock_def, state_component_equality]
          >> gvs[]
          >> irule_at Any (cj 1 flat_vals_LENGTH)
          >> gvs[inc_clock_def, dec_clock_def, state_component_equality, bvlSemTheory.find_code_def]
         )
      >> reverse $ Cases_on ‘e’ >> gvs[]
      >- (rw[worker_body_def, evaluate_def]
          >> first_x_assum $ drule_then assume_tac
          >> gvs[]
          >> Cases_on ‘handler’ >> gvs[tail_ok_def, split_ok_def, shape_width_def]
          >- (‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> rw[evaluate_def]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
              >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
              >> gvs[]
              >> DEP_REWRITE_TAC[evaluate_genlist_prefix]
              >> gvs[]
             )
          >> Cases_on ‘f = d’ >> gvs[]
          >- (‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> rw[evaluate_def]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
              >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
              >> gvs[]
              >> DEP_REWRITE_TAC[evaluate_genlist_prefix]
              >> gvs[]
             )
          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
          >> gvs[]
          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
            gvs[state_rel_def, dec_clock_def, oracle_free_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> first_assum $ irule_at Any
          >> rw[evaluate_def]
          >> qexists ‘ck + ck' + 1 + ticks’
          >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> pop_assum $ qspec_then ‘ck' + 1 + ticks’ assume_tac
          >> ‘inc_clock (ck' + 1 + ticks) (inc_clock ck t) =
              inc_clock (ck + ck' + 1 + ticks) t’ by
            gvs[inc_clock_def, state_component_equality]
          >> gvs[bvlSemTheory.find_code_def, dec_clock_def, inc_clock_def]
         )
      >> Cases_on ‘a'’ >> gvs[]
      >> Cases_on ‘handler’ >> gvs[tail_ok_def, split_ok_def, shape_width_def]
      >- (first_x_assum $ drule_then assume_tac
          >> gvs[]
          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
          >> gvs[]
          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> rw[evaluate_def, worker_body_def]
          >> first_assum $ irule_at Any
          >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
          >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
          >> gvs[]
          >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
          >> drule_then assume_tac $ cj 1 flat_vals_LENGTH
          >> gvs[]
          >> DEP_REWRITE_TAC[evaluate_genlist_prefix]
          >> gvs[]
         )
      >> first_x_assum $ drule_then assume_tac
      >> gvs[]
      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
      >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
      >> gvs[]
      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
      >> first_x_assum $ drule_all_then assume_tac
      >> gvs[]
      >> first_assum $ irule_at Any
      >> rw[evaluate_def, worker_body_def]
      >- (qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
          >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
          >> gvs[]
          >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
         )
      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
      >> drule_then (qspec_then ‘1 + ck' + ticks’ assume_tac) evaluate_add_clock
      >> gvs[]
      >> qexists ‘ck + 1 + ck' + ticks’ >> gvs[inc_clock_def, dec_clock_def, bvlSemTheory.find_code_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
          >> reverse $ Cases_on ‘q’ >> gvs[]
          >- (first_x_assum $ drule_then assume_tac
              >> gvs[]
              >> qexistsl [‘ck’, ‘t1’] >> gvs[]
             )
          >> Cases_on ‘find_code (SOME dest) a r.code ’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
          >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
          >> Cases_on ‘e’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >- (first_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
                  >> gvs[]
                  >> Cases_on ‘lookup dest m’ >> gvs[]
                  >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[inc_clock_def, dec_clock_def]
                     )
                  >> Cases_on ‘x’ >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                  >> first_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                  >> first_assum $ irule_at Any
                  >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ticks + 2 + ck'’ assume_tac) evaluate_add_clock
                  >> gvs[]
                  >> qexists ‘ck + ticks + 2 + ck'’ >> gvs[inc_clock_def, dec_clock_def, evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                   (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> gvs[bvlSemTheory.find_code_def]
                 )
              >> Cases_on ‘LENGTH l = rets’ >> gvs[]
              >> assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[y]’, ‘l ++ env’, ‘r''’] assume_tac
              >> gvs[]
              >> Cases_on ‘res’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> first_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
                  >> gvs[]
                  >> Cases_on ‘lookup dest m’ >> gvs[]
                  >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> last_x_assum $ drule_then assume_tac
                      >> gvs[]
                      >> first_assum $ irule_at Any
                      >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ticks + 1 + ck' + ck''’ assume_tac) evaluate_add_clock
                      >> gvs[]
                      >> qexists ‘ck + ticks + 1 + ck' + ck''’ >> gvs[dec_clock_def, inc_clock_def]
                      >> qpat_x_assum ‘evaluate ([r'], a, _) = _’ assume_tac
                      >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                      >> gvs[dec_clock_def, inc_clock_def]
                     )
                  >> Cases_on ‘x’ >> gvs[]
                  >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
                 )
              >> first_x_assum $ drule_then assume_tac
              >> gvs[]
              >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> Cases_on ‘lookup dest m’ >> gvs[]
              >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
                  >> last_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> last_x_assum $ drule_then assume_tac
                  >> gvs[]
                  >> first_assum $ irule_at Any
                  >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ticks + 1 + ck' + ck''’ assume_tac) evaluate_add_clock
                  >> gvs[]
                  >> qexists ‘ck + ticks + 1 + ck' + ck''’ >> gvs[dec_clock_def, inc_clock_def]
                  >> qpat_x_assum ‘evaluate ([r'], a, _) = _’ assume_tac
                  >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
                  >> gvs[dec_clock_def, inc_clock_def]
                 )
              >> Cases_on ‘x’ >> gvs[]
              >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
             )
          >> first_x_assum $ drule_then assume_tac
          >> gvs[]
          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
          >> gvs[]
          >> Cases_on ‘lookup dest m’ >> gvs[]
          >- (‘state_rel m (dec_clock (ticks + 1) r) t1’ by gvs[state_rel_def, dec_clock_def, oracle_free_def, inc_clock_def]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> last_x_assum $ drule_then assume_tac
              >> gvs[]
              >> first_assum $ irule_at Any
              >> qpat_x_assum ‘evaluate (xs, _, inc_clock _ _) = _’ assume_tac
              >> drule_then (qspec_then ‘ticks + 1 + ck'’ assume_tac) evaluate_add_clock
              >> gvs[]
              >> qexists ‘ck + ticks + 1 + ck'’ >> gvs[dec_clock_def, inc_clock_def]
             )
          >> Cases_on ‘x’ >> gvs[]
          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
            gvs[state_rel_def, dec_clock_def, oracle_free_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> rename1 ‘evaluate ([worker_body m dest x1 x0 r'],a,inc_clock ck0 t1) = _’
          >> qexists ‘ck + ck0 + ticks + 2’
          >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> pop_assum $ qspec_then ‘ck0 + ticks + 2’ assume_tac
          >> gvs[inc_clock_def]
          >> subgoal ‘evaluate
                      ([make_wrapper (LENGTH a) x1 x0],a,
                       dec_clock (ticks + 1)
                                 (t1 with clock := ck0 + (ticks + (t1.clock + 2)))) = (Rerr (Rabort a'),t1')’
          >- (irule evaluate_make_wrapper_err
              >> gvs[dec_clock_def]
              )
          >> gvs[inc_clock_def, dec_clock_def]
         )
      >> rw[worker_body_def, evaluate_def]
      >> Cases_on ‘evaluate (xs,env,s1)’ >> gvs[tail_ok_def, tail_form_def]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (first_x_assum $ drule_all_then strip_assume_tac
          >> qexistsl [‘ck’,‘t1’] >> gvs[]
         )
      >> first_x_assum $ drule_all_then strip_assume_tac
      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
      >> Cases_on ‘find_code (SOME dest) a r.code’ >> gvs[]
      >> PairCases_on ‘x’ >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >> Cases_on ‘evaluate ([x1],x0,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘e’ >> gvs[]
      >- (Cases_on ‘a'’ >> gvs[]
          >- (Cases_on ‘lookup dest m’
              >- (drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
                    gvs[state_rel_def, dec_clock_def, oracle_free_def]
                  >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock _ _) t' ⇒ _’ $
                                  qspecl_then [‘m’,‘t1’] mp_tac
                  >> impl_tac >- gvs[] >> strip_tac
                  >> rename1 ‘evaluate ([x1],x0,inc_clock ck0 t1) = _’
                  >> qexists ‘ck + ck0 + ticks + 1’
                  >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
                  >> drule_then assume_tac evaluate_add_clock
                  >> pop_assum $ qspec_then ‘ck0 + ticks + 1’ assume_tac
                  >> gvs[inc_clock_def, dec_clock_def]
                 )
              >> rename1 ‘lookup dest m = SOME z’ >> PairCases_on ‘z’
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
                gvs[state_rel_def, dec_clock_def, oracle_free_def]
              >> first_x_assum $ qspecl_then [‘m’,‘t1’,‘dest’,‘z1’,‘z0’] mp_tac
              >> impl_tac >- gvs[] >> strip_tac
              >> rename1 ‘evaluate ([worker_body m dest z1 z0 x1],x0,inc_clock ck0 t1) = _’
              >> qexists ‘ck + ck0 + ticks + 2’
              >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
              >> drule_then assume_tac evaluate_add_clock
              >> pop_assum $ qspec_then ‘ck0 + ticks + 2’ assume_tac
              >> gvs[dec_clock_def, inc_clock_def]
              >> first_assum $ irule_at Any
              >> ‘evaluate ([make_wrapper (LENGTH x0) z1 z0],x0, inc_clock (ck0 + 1) t1) =
                  (Rerr (Rraise (Exn v)),t1')’ suffices_by gvs[inc_clock_def, dec_clock_def]
              >> irule evaluate_make_wrapper_err
              >> gvs[dec_clock_def, inc_clock_def]
             )
          >> Cases_on ‘LENGTH l = rets’ >> gvs[]
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[y]’, ‘l ++ env’, ‘r'’] assume_tac
          >> gvs[]
          >> Cases_on ‘res’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> Cases_on ‘lookup dest m’
              >- (drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
                    gvs[state_rel_def, dec_clock_def, oracle_free_def]
                  >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock _ _) t' ⇒ _’ $
                                  qspecl_then [‘m’,‘t1’] mp_tac
                  >> impl_tac >- gvs[] >> strip_tac
                  >> rename1 ‘evaluate ([x1],x0,inc_clock ck0 t1) = _’
                  >> first_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                  >> first_assum $ irule_at Any
                  >> gvs[] 
                  >> qexists ‘ck + ck0 + ticks + 1 + ck'’
                  >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
                  >> drule_then assume_tac evaluate_add_clock
                  >> pop_assum $ qspec_then ‘ck0 + ticks + 1 + ck'’ assume_tac
                  >> gvs[inc_clock_def, dec_clock_def]
                  >> qpat_x_assum ‘evaluate ([x1],x0,_) = _’ $ assume_tac
                  >> drule_then assume_tac evaluate_add_clock
                  >> pop_assum $ qspec_then ‘ck'’ assume_tac
                  >> gvs[inc_clock_def, dec_clock_def]
                 )
              >> rename1 ‘lookup dest m = SOME z’ >> PairCases_on ‘z’
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
              >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
             )
          >> Cases_on ‘lookup dest m’
          >- (drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
              >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
                gvs[state_rel_def, dec_clock_def, oracle_free_def]
              >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock _ _) t' ⇒ _’ $
                              qspecl_then [‘m’,‘t1’] mp_tac
              >> impl_tac >- gvs[] >> strip_tac
              >> rename1 ‘evaluate ([x1],x0,inc_clock ck0 t1) = _’
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> first_assum $ irule_at Any
              >> gvs[] 
              >> qexists ‘ck + ck0 + ticks + 1 + ck'’
              >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
              >> drule_then assume_tac evaluate_add_clock
              >> pop_assum $ qspec_then ‘ck0 + ticks + 1 + ck'’ assume_tac
              >> gvs[inc_clock_def, dec_clock_def]
              >> qpat_x_assum ‘evaluate ([x1],x0,_) = _’ $ assume_tac
              >> drule_then assume_tac evaluate_add_clock
              >> pop_assum $ qspec_then ‘ck'’ assume_tac
              >> gvs[inc_clock_def, dec_clock_def]
             )
          >> rename1 ‘lookup dest m = SOME z’ >> PairCases_on ‘z’
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
         )
      >> Cases_on ‘lookup dest m’
      >- (drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
            gvs[state_rel_def, dec_clock_def, oracle_free_def]
          >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock _ _) t' ⇒ _’ $
                          qspecl_then [‘m’,‘t1’] mp_tac
          >> impl_tac >- gvs[] >> strip_tac
          >> rename1 ‘evaluate ([x1],x0,inc_clock ck0 t1) = _’
          >> qexists ‘ck + ck0 + ticks + 1’
          >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
          >> drule_then assume_tac evaluate_add_clock
          >> pop_assum $ qspec_then ‘ck0 + ticks + 1’ assume_tac
          >> gvs[inc_clock_def, dec_clock_def]
         )
      >> rename1 ‘lookup dest m = SOME z’ >> PairCases_on ‘z’
      >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
      >> ‘state_rel m (dec_clock (ticks + 1) r) t1’ by
        gvs[state_rel_def, dec_clock_def, oracle_free_def]
      >> first_x_assum $ qspecl_then [‘m’,‘t1’,‘dest’,‘z1’,‘z0’] mp_tac
      >> impl_tac >- gvs[] >> strip_tac
      >> rename1 ‘evaluate ([worker_body m dest z1 z0 x1],x0,inc_clock ck0 t1) = _’
      >> qexists ‘ck + ck0 + ticks + 2’
      >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = _’ $ assume_tac
      >> drule_then assume_tac evaluate_add_clock
      >> pop_assum $ qspec_then ‘ck0 + ticks + 2’ assume_tac
      >> gvs[dec_clock_def, inc_clock_def]
      >> first_assum $ irule_at Any
      >> ‘evaluate ([make_wrapper (LENGTH x0) z1 z0],x0, inc_clock (ck0 + 1) t1) =
          (Rerr (Rabort a'),t1')’ suffices_by gvs[inc_clock_def, dec_clock_def]
      >> irule evaluate_make_wrapper_err
      >> gvs[dec_clock_def, inc_clock_def]
     )
QED

Theorem evaluate_wrapper_sim:
  ∀m t d arity body sh wk args (s:('a, 'b) bviSem$state) res s1.
    state_rel m s t ∧ lookup d s.code = SOME (arity,body) ∧
    lookup d m = SOME (sh,wk) ∧ LENGTH args = arity ∧
    evaluate ([body],args,s) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧ res ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∃ck t1.
      state_rel m s1 t1 ∧
      evaluate ([make_wrapper arity wk sh],args,inc_clock (ck + 1) t) =
        (res,t1)
Proof
  rpt strip_tac
  >> ‘code_rel m s.code t.code’ by gvs[state_rel_def]
  >> drule_then assume_tac code_rel_find_code_SOME_dest
  >> pop_assum $ qspecl_then [‘d’, ‘args’] assume_tac >> gvs[bvlSemTheory.find_code_def]
  >> Cases_on ‘lookup d t.code’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> drule_all_then assume_tac $ SRULE [] $ cj 2 cpr_correct
  >> gvs[]
  >> assume_tac evaluate_LENGTH
  >> pop_assum $ qspecl_then [‘[body]’, ‘args’, ‘s’] assume_tac >> gvs[]
  >> reverse $ Cases_on ‘res’ >> gvs[]
  >- (drule_all_then assume_tac evaluate_tail_no_Ret
      >> first_assum $ irule_at Any
      >> irule_at Any evaluate_make_wrapper_err
      >> gvs[dec_clock_def, inc_clock_def]
      >> metis_tac[]
     )
  >> Cases_on ‘a’ >> gvs[]
  >> first_assum $ irule_at Any
  >> rw[make_wrapper_def, evaluate_def]
  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH args), args, t) =
                                   (Rval (TAKE (LENGTH args) (DROP 0 args)), t)’
  >- (irule evaluate_genlist_vars
      >> gvs[]
     )
  >> pop_assum $ assume_tac o SRULE[]
  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
  >> gvs[bvlSemTheory.find_code_def]
  >> qexists ‘ck’ >> gvs[inc_clock_def, dec_clock_def]
  >> drule_all_then assume_tac $ cj 1 flat_vals_LENGTH
  >> gvs[]
  >> irule $ cj 1 evaluate_rebuild
  >> gvs[]
  >> DEP_REWRITE_TAC[TAKE_APPEND1]
  >> gvs[]
QED
 
Theorem compile_prog_state_rel:
  ∀next prog n prog2 (s:('c,'ffi) bviSem$state).
    compile_prog next prog = (n,prog2) ∧
    map_inv LN next ∧ prog_keys_ok next prog ∧
    s.code = fromAList prog ∧ oracle_free s ⇒
    ∃m. state_rel m s (s with code := fromAList prog2)
Proof
  rw[compile_prog_def]
  >> drule_then assume_tac compile_prog_with_map_thm
  >> pop_assum mp_tac >> impl_tac >- gvs[lookup_def]
  >> strip_tac
  >> qexists ‘m2’
  >> gvs[state_rel_def, code_rel_def]
  >> rpt conj_tac >> gvs[]
  >- gvs[map_inv_def]
  >- (rpt gen_tac >> strip_tac
      >> drule_at Any code_rel_of_fun_rel
      >> gvs[prog_keys_ok_def]
      >> disch_then $ drule_then assume_tac
      >> gvs[]
      >> pop_assum $ drule_then assume_tac
      >> Cases_on ‘lookup d m2’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> first_assum $ irule_at Any
      >> gvs[]
     )
  >- (rw[domain_fromAList] >> gvs[MEM_MAP]
      >> PairCases_on ‘y’ >> gvs[]
      >> first_x_assum $ drule_then assume_tac >> gvs[]
      >- (disj1_tac >> gvs[domain_fromAList, MEM_MAP] >> metis_tac[FST])
      >> metis_tac[]
      )
  >> rpt gen_tac >> strip_tac
  >> conj_tac
  >- (first_x_assum $ drule_then assume_tac
      >> gvs[lookup_def, domain_fromAList]
     )
  >> first_x_assum $ drule_then assume_tac >> gvs[lookup_def]
  >> gvs[domain_fromAList, MEM_MAP]
  >> rpt strip_tac >> PairCases_on ‘y'’
  >> gvs[prog_keys_ok_def, EVERY_MEM]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[]
QED
   
Theorem compile_prog_init_state_rel:
  ∀next prog n prog2 ffi co cc.
    compile_prog next prog = (n,prog2) ∧ map_inv LN next ∧
    prog_keys_ok next prog ∧ (∀k. SND (co k) = []) ⇒
    ∃m. ∀k. state_rel m (initial_state ffi (fromAList prog) co cc k)
                        (initial_state ffi (fromAList prog2) co cc k)
Proof
  rpt strip_tac
  >> qspecl_then [‘next’,‘prog’,‘n’,‘prog2’,
                  ‘initial_state ffi (fromAList prog) co cc 0’] mp_tac
       compile_prog_state_rel
  >> impl_tac >- gvs[initial_state_def, oracle_free_def]
  >> strip_tac >> qexists ‘m’ >> rw[]
  >> ‘initial_state ffi (fromAList prog) co cc k =
        (initial_state ffi (fromAList prog) co cc 0) with clock := k ∧
      initial_state ffi (fromAList prog2) co cc k =
        ((initial_state ffi (fromAList prog) co cc 0)
           with code := fromAList prog2) with clock := k’
       by gvs[initial_state_def, state_component_equality]
  >> gvs[]
  >> dxrule_then (qspec_then ‘k’ assume_tac) $ cj 1 state_rel_clock
  >> dxrule_then (qspec_then ‘k’ assume_tac) $ cj 2 state_rel_clock
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

        
Theorem do_app_state_rel_rval:
  ∀op vs m s t v s1.
    state_rel m s t ∧ do_app op vs s = Rval (v,s1)  ⇒
    ∃t1. do_app op vs t = Rval (v,t1) ∧ state_rel m s1 t1 ∧
         t1.clock = t.clock ∧ s1.clock = s.clock
Proof
  rw[state_rel_def]
  >> Cases_on ‘op’ >> gvs[]
  >~ [‘Install’]
  >- (gvs[do_app_def, do_install_def]
      >> Cases_on ‘s.compile_oracle 0’ >> gvs[]
      >> gvs[oracle_free_def]
      >> first_x_assum $ qspec_then ‘0’ assume_tac >> gvs[]
      >> every_case_tac >> gvs[]
     )
  >~ [‘Label’]
  >- (gvs[do_app_def, do_app_aux_def]
      >> every_case_tac >> gvs[]
      >> drule_then assume_tac code_rel_domain
      >> gvs[SUBSET_DEF, domain_lookup]
      >> metis_tac[]
      )
  >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  >> every_case_tac
  >> gvs[bvl_to_bvi_id, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
         bvi_to_bvl_def, bvl_to_bvi_def, oracle_free_def,
         state_component_equality]
  >> Cases_on ‘do_build_const l t.refs’ >> gvs[]
QED

Theorem do_app_state_rel_rerr:
  ∀op vs m s t v e.
    state_rel m s t ∧ do_app op vs s = Rerr e ∧ e ≠ Rabort Rtype_error ⇒ do_app op vs t = Rerr e 
Proof
  rw[state_rel_def]
  >> Cases_on ‘op’ >> gvs[]
  >~ [‘Install’]
  >- (gvs[do_app_def, do_install_def]
      >> Cases_on ‘s.compile_oracle 0’ >> gvs[]
      >> gvs[oracle_free_def]
      >> first_x_assum $ qspec_then ‘0’ assume_tac >> gvs[]
     )
  >~ [‘Label’]
  >- (gvs[do_app_def, do_app_aux_def]
      >> every_case_tac >> gvs[]
      )
  >> gvs[do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  >> every_case_tac
  >> gvs[bvl_to_bvi_id, bvl_to_bvi_with_refs, bvl_to_bvi_with_ffi,
         bvi_to_bvl_def, bvl_to_bvi_def, oracle_free_def,
         state_component_equality]
  >> Cases_on ‘do_build_const l t.refs’ >> gvs[]
QED


Theorem lag_events:
  ∀xs env (s:('a,'b) state) res s1 (t:('a,'b) state).
    evaluate (xs,env,s) = (res,s1) ∧ t.ffi = s.ffi ⇒
    t.ffi.io_events ≼ s1.ffi.io_events
Proof
  rw[] >> imp_res_tac evaluate_io_events_mono >> gvs[]
QED

Theorem state_rel_dec_clock:
  ∀m s t k1 k2. state_rel m s t ⇒ state_rel m (dec_clock k1 s) (dec_clock k2 t)
Proof
  rw[dec_clock_def] >> rw[state_rel_clock]
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


Theorem cpr_lag:
  ∀xs env (s:('a,'b) state).
    (∀m t res s1.
       state_rel m s t ∧ t.clock ≤ s.clock ∧
       evaluate (xs,env,s) = (res,s1) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃t1.
         (evaluate (xs,env,t) = (res,t1) ∧ state_rel m s1 t1 ∧
          t1.clock ≤ s1.clock) ∨
         (evaluate (xs,env,t) = (Rerr (Rabort Rtimeout_error),t1) ∧
          t1.ffi.io_events ≼ s1.ffi.io_events)) ∧
    (∀m t e f wk sh res s1.
       xs = [e] ∧ state_rel m s t ∧ t.clock ≤ s.clock ∧
       lookup f m = SOME (sh,wk) ∧ split_ok sh ∧
       tail_ok m f sh e ∧ tail_form e ∧
       evaluate ([e],env,s) = (res,s1) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃t1.
         ((case res of
             Rval [v] => v_shape sh v ∧
                         evaluate ([worker_body m f wk sh e],env,t) =
                         (Rerr (Rraise (Ret (flat_vals sh v))),t1)
           | Rerr err => evaluate ([worker_body m f wk sh e],env,t) =
                         (Rerr err,t1)
           | _ => F) ∧ state_rel m s1 t1 ∧ t1.clock ≤ s1.clock) ∨
         (evaluate ([worker_body m f wk sh e],env,t) =
          (Rerr (Rabort Rtimeout_error),t1) ∧
          t1.ffi.io_events ≼ s1.ffi.io_events))
Proof
  recInduct evaluate_ind
  >> rpt conj_tac
  >- (fs[evaluate_def]
     )
  >- (rw[evaluate_def]
      >> Cases_on ‘evaluate ([x],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >- (Cases_on ‘evaluate (y::xs,env,r)’ >> gvs[]
              >> Cases_on ‘q’ >> gvs[]
              >- (last_x_assum $ drule_all_then assume_tac
                  >> gvs[]
                 )
              >> last_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> metis_tac[]
             )
          >> qexists ‘t1’ >> disj2_tac >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> Cases_on ‘evaluate (y::xs,env,r)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono
          >> gvs[]
         )
      >> last_x_assum $ drule_all_then assume_tac
      >> gvs[]
      >> metis_tac[]
     )
  >- (rw[evaluate_def]
      >> Cases_on ‘sh’ >> gvs[tail_ok_def, tail_form_def, exp_shape_ok_def,
                              split_ok_def, no_ret_def, shape_width_def]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >- (IF_CASES_TAC >> gvs[]
                  >> IF_CASES_TAC >> gvs[]
                 )
              >> Cases_on ‘HD a = Boolv T’ >> gvs[]
              >- (qexists ‘t1’ >> disj2_tac >> gvs[]
                  >> irule IS_PREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> rev_drule_then assume_tac evaluate_io_events_mono
                  >> gvs[]
                 )
              >> Cases_on ‘HD a = Boolv F’ >> gvs[]
              >> qexists ‘t1’ >> disj2_tac >> gvs[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> rev_drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> last_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> metis_tac[]
         )
      >> Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >- (Cases_on ‘HD a = Boolv T’ >> gvs[tail_form_def, tail_ok_def]
              >- (first_x_assum $ drule_all_then assume_tac
                  >> rw[worker_body_def, evaluate_def]
                 )
              >> Cases_on ‘HD a = Boolv F’ >> gvs[tail_form_def, tail_ok_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> rw[worker_body_def, evaluate_def]
             )
          >> Cases_on ‘HD a = Boolv T’ >> gvs[tail_form_def, tail_ok_def]
          >- (assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[x2]’, ‘env’, ‘r’] assume_tac
              >> gvs[]
              >> Cases_on ‘res’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> qexists ‘t1’ >> disj2_tac
                  >> rw[worker_body_def, evaluate_def]
                  >> irule IS_PREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> rev_drule_then assume_tac evaluate_io_events_mono
                  >> gvs[]
                 )
              >> qexists ‘t1’ >> disj2_tac
              >> rw[worker_body_def, evaluate_def]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> rev_drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> Cases_on ‘HD a = Boolv F’ >> gvs[tail_form_def, tail_ok_def]
          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x3]’, ‘env’, ‘r’] assume_tac
          >> gvs[]
          >> Cases_on ‘res’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> qexists ‘t1’ >> disj2_tac
              >> rw[worker_body_def, evaluate_def]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> rev_drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> qexists ‘t1’ >> disj2_tac
          >> rw[worker_body_def, evaluate_def]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> rev_drule_then assume_tac evaluate_io_events_mono
          >> gvs[]
         )
      >> last_x_assum $ drule_all_then assume_tac
      >> gvs[worker_body_def, evaluate_def]
      >> metis_tac[]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (first_x_assum $ drule_all_then assume_tac >> gvs[]
              >> qexists ‘t1’ >> disj2_tac
              >> rw[worker_body_def, evaluate_def]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> rev_drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> first_x_assum $ drule_all_then assume_tac >> gvs[]
          >> metis_tac[]
         )
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[x2]’, ‘a ++ env’, ‘r’] assume_tac
          >> gvs[]
          >> Cases_on ‘res’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> rw[worker_body_def, evaluate_def]
              >> first_x_assum $ drule_all_then assume_tac >> gvs[tail_form_def, tail_ok_def]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> rev_drule_then irule evaluate_io_events_mono
             )
          >> first_x_assum $ drule_all_then assume_tac >> gvs[tail_form_def, tail_ok_def]
          >- rw[worker_body_def, evaluate_def]
          >> rw[worker_body_def, evaluate_def]
          >> qexists ‘t1’ >> disj2_tac >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> rev_drule_then irule evaluate_io_events_mono
         )
      >> rw[worker_body_def, evaluate_def]
      >> first_x_assum $ drule_all_then assume_tac >> gvs[tail_form_def, tail_ok_def]
      >- metis_tac[]
      >> qexists ‘t1’ >> disj2_tac >> gvs[]
      >> irule IS_PREFIX_TRANS
      >> first_assum $ irule_at Any
      >> rev_drule_then irule evaluate_io_events_mono
     )
  >- (rw[evaluate_def]
      >- (rpt full_case_tac >> gvs[AllCaseEqs ()]
          >> first_x_assum $ drule_all_then assume_tac >> gvs[]
          >- metis_tac[]
          >> qexists ‘r’ >> disj2_tac >> gvs[]
          >> irule_at Any IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> rev_drule_then irule evaluate_io_events_mono
         )
      >> rpt full_case_tac >> gvs[AllCaseEqs (), tail_form_def, tail_ok_def]
      >> rw[evaluate_def, worker_body_def]
      >- (first_x_assum $ drule_all_then assume_tac >> gvs[]
         )
      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
      >> metis_tac[]
     )
  >- (rw[evaluate_def]
      >- (rpt full_case_tac >> gvs[AllCaseEqs ()]
          >> first_x_assum $ drule_all_then assume_tac >> gvs[]
          >- metis_tac[]
          >> qexists ‘r’ >> disj2_tac >> gvs[]
          >> irule_at Any IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> rev_drule_then irule evaluate_io_events_mono
         )
      >> rpt full_case_tac >> gvs[AllCaseEqs (), tail_form_def, tail_ok_def]
      >> rw[evaluate_def, worker_body_def]
      >- (first_x_assum $ drule_all_then assume_tac >> gvs[]
         )
      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
      >> metis_tac[]
     )
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
              >- (Cases_on ‘do_app op (REVERSE a) r’ >> gvs[]
                  >- (Cases_on ‘a'’ >> gvs[]
                      >> drule_all_then assume_tac do_app_state_rel_rval
                      >> gvs[]
                     )
                  >> qexists ‘t1’ >> disj1_tac >> gvs[]
                  >> drule_all_then assume_tac  do_app_state_rel_rerr
                  >> gvs[]
                 )
              >> Cases_on ‘do_app op (REVERSE a) r’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> drule_all_then assume_tac do_app_io_events_mono
                  >> irule IS_PREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> gvs[]
                 )
              >> metis_tac[]
             )
          >> last_x_assum $ drule_all_then assume_tac >> gvs[]
          >> metis_tac[]
         )
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (Cases_on ‘do_app op (REVERSE a) r’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> last_x_assum $ drule_all_then assume_tac >> gvs[tail_ok_def, tail_form_def]
              >- (rw[evaluate_def, worker_body_def]
                  >> drule_all_then assume_tac do_app_state_rel_rval
                  >> gvs[]
                  >> qexists ‘t1'’ >> gvs[] >> disj1_tac
                  >> ‘v_shape sh q ∧evaluate (flatten_exp sh (Op op xs),env,t) = (Rval (flat_vals sh q),t1')’ suffices_by rw[]
                  >> irule $ cj 1 evaluate_flatten_exp
                  >> gvs[evaluate_def]
                 )
              >> rw[evaluate_def, worker_body_def]
              >> drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
              >> gvs[evaluate_def]
              >> pop_assum $ qspecl_then [‘env’, ‘t’] assume_tac >> gvs[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> drule_all_then assume_tac do_app_io_events_mono
              >> gvs[]
             )
          >> last_x_assum $ drule_all_then assume_tac >> gvs[tail_ok_def, tail_form_def]
          >- (rw[evaluate_def, worker_body_def]
              >> drule_all_then assume_tac do_app_state_rel_rerr
              >> gvs[]
              >> qexists ‘t1’ >> gvs[] >> disj1_tac
              >> ‘evaluate (flatten_exp sh (Op op xs),env,t) = (Rerr e,t1)’ suffices_by rw[]
              >> irule $ cj 1 evaluate_flatten_exp_err
              >> gvs[evaluate_def]
             )
          >> rw[evaluate_def, worker_body_def]
          >> drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
          >> gvs[evaluate_def]
          >> pop_assum $ qspecl_then [‘env’, ‘t’] assume_tac >> gvs[]
          >> qexists ‘t1’ >> disj2_tac >> gvs[]
         )
      >> last_x_assum $ drule_all_then assume_tac >> gvs[tail_ok_def, tail_form_def]
      >- (drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
          >> pop_assum $ qspecl_then [‘env’, ‘t’] (assume_tac o SRULE[evaluate_def]) >> gvs[]
          >> rw[evaluate_def, worker_body_def]
          >> metis_tac[]
         )
      >> drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
      >> pop_assum $ qspecl_then [‘env’, ‘t’] (assume_tac o SRULE[evaluate_def]) >> gvs[]
      >> rw[evaluate_def, worker_body_def]
      >> metis_tac[]
     )
        
  >- (rw[evaluate_def]
      >- metis_tac[]
      >- metis_tac[evaluate_def, worker_body_def]
      >- (full_case_tac >> gvs[]
          >- (qexists ‘t’ >> disj2_tac >> gvs[]
              >> qpat_x_assum ‘evaluate ([x],env,dec_clock 1 s) = _’ assume_tac
              >> drule_then assume_tac evaluate_io_events_mono
              >> gvs[state_rel_def, dec_clock_def]
             )
          >> last_x_assum $ qspecl_then [‘m’,‘dec_clock 1 t’] mp_tac
          >> impl_tac
          >- gvs[state_rel_def, dec_clock_def, oracle_free_def, state_component_equality]
          >> strip_tac
          >> qexists ‘t1’ >> gvs[]
         )
      >> rw[worker_body_def, evaluate_def]
      >> Cases_on ‘t.clock = 0’ >> gvs[]
      >- (qexists ‘t’ >> disj2_tac >> gvs[]
          >> qpat_x_assum ‘evaluate ([x],env,dec_clock 1 s) = _’ assume_tac
          >> drule_then assume_tac evaluate_io_events_mono
          >> gvs[state_rel_def, dec_clock_def]
         )
      >> first_x_assum $ qspecl_then [‘m’,‘dec_clock 1 t’,‘f’,‘wk’,‘sh’] mp_tac
      >> impl_tac
      >- gvs[state_rel_def, dec_clock_def, oracle_free_def,
             state_component_equality, tail_ok_def, tail_form_def]
      >> strip_tac
      >> qexists ‘t1’ >> gvs[]
     )
        
  >- (rw[evaluate_def]
      >> ‘dest_thunk env❲n❳ t.refs = dest_thunk env❲n❳ s.refs’ by gvs[state_rel_def]
      >> gvs[AllCaseEqs()]
      >~ [‘IsThunk Evaluated’]
      >- (qexists ‘t’ >> disj1_tac >> gvs[worker_body_def, evaluate_def]
          >> ‘v_shape sh v ∧ evaluate (flatten_exp sh (Force force_loc n),env,t) = (Rval (flat_vals sh v), t)’ suffices_by rw[]
          >> irule $ cj 1 evaluate_flatten_exp
          >> gvs[evaluate_def, tail_ok_def, tail_form_def]
         )
      >- (qexists ‘t with clock := 0’ >> disj1_tac
          >> conj_tac
          >- (‘code_rel m s.code t.code’ by gvs[state_rel_def]
              >> Cases_on ‘lookup force_loc m’
              >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[])
              >> rename1 ‘lookup force_loc m = SOME z’ >> PairCases_on ‘z’
              >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> metis_tac[]
             )
          >> gvs[state_rel_def, oracle_free_def]
       )

      >- (‘code_rel m s.code t.code’ by gvs[state_rel_def]
          >> Cases_on ‘t.clock = 0’
          >- (qexists ‘t with clock := 0’ >> disj2_tac
              >> conj_tac
              >- (Cases_on ‘lookup force_loc m’
                  >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
                     )
                  >> PairCases_on ‘x’
                  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
                  >> gvs[] >> metis_tac[]
                 )
              >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
              >> first_assum $ irule_at Any
              >> gvs[state_accessors]
             )
          >> Cases_on ‘lookup force_loc m’ >> gvs[]
          >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
              >> last_x_assum $ qspecl_then [‘m’,‘dec_clock 1 t’] mp_tac
              >> impl_tac
              >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def]
                 )
              >> strip_tac >> qexists ‘t1’ >> gvs[] >> metis_tac[]
             )
          >> PairCases_on ‘x’
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> Cases_on ‘t.clock ≤ 1’ >> gvs[]
          >- (gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
              >> irule lag_events
              >> first_x_assum $ irule_at Any
              >> gvs[state_accessors, state_rel_def]
             )
          >> qpat_x_assum ‘∀m' t' f wk sh. _ ∧ _ ∧ lookup _ _ = _ ∧ _ ⇒ _’ $
                          qspecl_then [‘m’,‘dec_clock 1 (dec_clock 1 t)’,‘force_loc’,‘x1’,‘x0’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def, state_rel_def]
             )

          >> assume_tac evaluate_LENGTH
          >> pop_assum $ qspecl_then [‘[exp]’,‘[env❲n❳; v]’,‘dec_clock 1 s’] assume_tac >> gvs[]
          >> Cases_on ‘v6’ >> gvs[]
          >> strip_tac
          >> qexists ‘t1’
          >- (disj1_tac >> gvs[]
              >> drule_then assume_tac (cj 1 flat_vals_LENGTH)
              >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
              >> irule (cj 1 evaluate_rebuild) >> gvs[]
              >> DEP_REWRITE_TAC[TAKE_APPEND1] >> gvs[]
             )
          >> disj2_tac
          >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
         )
      >- (‘code_rel m s.code t.code’ by gvs[state_rel_def]
          >> Cases_on ‘t.clock = 0’
          >- (qexists ‘t with clock := 0’ >> disj2_tac
              >> conj_tac
              >- (Cases_on ‘lookup force_loc m’
                  >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
                     )
                  >> PairCases_on ‘x’
                  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
                  >> gvs[] >> metis_tac[]
                 )
              >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
              >> first_assum $ irule_at Any
              >> gvs[state_accessors]
             )
          >> Cases_on ‘lookup force_loc m’ >> gvs[]
          >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
              >> last_x_assum $ qspecl_then [‘m’,‘dec_clock 1 t’] mp_tac
              >> impl_tac
              >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def]
                 )
              >> strip_tac >> qexists ‘t1’ >> gvs[] >> metis_tac[]
             )
          >> PairCases_on ‘x’
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> Cases_on ‘t.clock ≤ 1’ >> gvs[]
          >- (gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
              >> irule lag_events
              >> first_x_assum $ irule_at Any
              >> gvs[state_accessors, state_rel_def]
             )
          >> qpat_x_assum ‘∀m' t' f wk sh. _ ∧ _ ∧ lookup _ _ = _ ∧ _ ⇒ _’ $
                          qspecl_then [‘m’,‘dec_clock 1 (dec_clock 1 t)’,‘force_loc’,‘x1’,‘x0’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def, state_rel_def]
             )
          >> strip_tac >> gvs[]
          >> qexists ‘t1’
          >- (disj1_tac >> gvs[]
              >> irule evaluate_make_wrapper_err >> gvs[]
              >> gvs[dec_clock_def]
             )
          >> disj2_tac >> gvs[]
          >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
         )
      >- (‘code_rel m s.code t.code’ by gvs[state_rel_def]
          >> Cases_on ‘t.clock = 0’
          >- (qexists ‘t with clock := 0’ >> disj2_tac
              >> conj_tac
              >- (Cases_on ‘lookup force_loc m’
                  >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
                     )
                  >> rename1 ‘lookup force_loc m = SOME z’ >> PairCases_on ‘z’
                  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest
                  >> gvs[] >> metis_tac[]
                 )
              >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
              >> first_assum $ irule_at Any
              >> gvs[state_accessors]
              )
          >> Cases_on ‘lookup force_loc m’
          >- (drule_all_then assume_tac code_rel_find_code_NONE >> gvs[]
              >> last_x_assum $ qspecl_then [‘m’,‘dec_clock 1 t’] mp_tac
              >> impl_tac
              >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def]
                 )
              >> strip_tac >> qexists ‘t1’ >> gvs[] >> metis_tac[]
             )
          >> rename1 ‘lookup force_loc m = SOME z’ >> PairCases_on ‘z’
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> Cases_on ‘t.clock ≤ 1’
          >- (qexists ‘dec_clock 1 t with clock := 0’ >> disj2_tac
              >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def, dec_clock_def]
              >> irule lag_events >> gvs[state_rel_def]
              >> first_assum $ irule_at Any
              >> gvs[state_accessors]
             )
          >> qpat_x_assum ‘∀m' t' f wk sh. _ ∧ _ ∧ lookup _ _ = _ ∧ _ ⇒ _’ $
                          qspecl_then [‘m’,‘dec_clock 1 (dec_clock 1 t)’,‘force_loc’,‘z1’,‘z0’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def, state_rel_def]
             )
          >> strip_tac >> qexists ‘t1’
          >- (disj1_tac
              >> gvs[]
              >> irule evaluate_make_wrapper_err >> gvs[dec_clock_def]
           )                  
          >> disj2_tac
          >> gvs[]
          >> irule evaluate_make_wrapper_err >> gvs[dec_clock_def]
         )
      >> Cases_on ‘sh’ >> gvs [tail_ok_def, exp_shape_ok_def, split_ok_def, shape_width_def]
     )


  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (first_x_assum $ drule_all_then assume_tac >> reverse $ gvs[]
              >- (qexists_tac ‘t1’ >> disj2_tac >> gvs []
                  >> irule_at Any IS_PREFIX_TRANS >> first_assum (irule_at Any)
                  >> every_case_tac >> gvs []
                  >> imp_res_tac evaluate_io_events_mono >> gvs [dec_clock_def]
                  >> metis_tac [IS_PREFIX_TRANS, IS_PREFIX_REFL]
                 )
              >> Cases_on ‘find_code dest a r.code’ >> gvs[]
              >> Cases_on ‘x’ >> gvs[]
              >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
              >- (Cases_on ‘dest’ >> gvs[]
                  >- (gvs[bvlSemTheory.find_code_def]
                      >> Cases_on ‘LAST a’ >> gvs[]
                      >> Cases_on ‘lookup n r.code’ >> gvs[]
                      >> Cases_on ‘x’ >> gvs[]
                      >> subgoal ‘∃body'. lookup n t1.code = SOME (q',body')’
                      >- (gvs [state_rel_def, code_rel_def]
                          >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                          >> Cases_on ‘lookup n m’ >> gvs[]
                          >> Cases_on ‘x’ >> gvs[]
                         )
                      >> gvs[]
                      >> qexists_tac ‘t1 with clock := 0’ >> disj1_tac >> simp []
                      >> irule $ cj 1 state_rel_clock
                      >> irule $ cj 2 state_rel_clock
                      >> first_assum $ irule
                     )
                  >> drule_at_then Any assume_tac code_rel_find_code_SOME_dest >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                  >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                  >> Cases_on ‘lookup x m’ >> gvs[]
                  >- (qexists ‘t1 with clock := 0’ >> gvs[]
                      >> disj1_tac
                      >> irule $ cj 1 state_rel_clock
                      >> irule $ cj 2 state_rel_clock
                      >> first_assum $ irule
                     )
                  >> Cases_on ‘x'’ >> gvs[]
                  >> qexists ‘t1 with clock := 0’ >> gvs[]
                  >> disj1_tac
                  >> irule $ cj 1 state_rel_clock
                  >> irule $ cj 2 state_rel_clock
                  >> first_assum $ irule
                 )
              >> Cases_on ‘dest’ >> gvs[]
              >- (gvs[bvlSemTheory.find_code_def]
                  >> Cases_on ‘LAST a’ >> gvs[]
                  >> Cases_on ‘lookup n r.code’ >> gvs[]
                  >> Cases_on ‘x’ >> gvs[]
                  >> subgoal ‘∃body'. lookup n t1.code = SOME (q',body')’
                  >- (gvs [state_rel_def, code_rel_def]
                      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                      >> Cases_on ‘lookup n m’ >> gvs[]
                      >> Cases_on ‘x’ >> gvs[]
                     )
                  >> gvs[]
                  >> IF_CASES_TAC
                  >- (qexists_tac ‘t1 with clock := 0’ >> disj2_tac >> gvs [state_rel_def]
                      >> every_case_tac >> gvs []
                      >> imp_res_tac evaluate_io_events_mono >> gvs [dec_clock_def]
                      >> metis_tac [IS_PREFIX_TRANS, IS_PREFIX_REFL]
                     )

                  >> ‘LENGTH (FRONT a) = q'’ by gvs [LENGTH_FRONT]
                  >> Cases_on ‘evaluate ([r'],FRONT a,dec_clock (ticks+1) r)’
                  >> rename1 ‘_ = (res0,s0)’
                  >> ‘res0 ≠ Rerr (Rabort Rtype_error) ∧ ∀vs. res0 ≠ Rerr (Rraise (Ret vs))’ by (every_case_tac >> gvs [])
                  >> ‘s1' = s0’ by (every_case_tac >> gvs []) >> gvs [] 
                  >> Cases_on ‘lookup n m’ >> gvs[]
                  >- (subgoal ‘body' = r'’
                      >- (‘code_rel m r.code t1.code’ by gvs[state_rel_def]
                          >> gvs[code_rel_def]
                          >> first_x_assum $ drule_then assume_tac
                          >> gvs[]
                         )
                      >> gvs[]
                      >> last_x_assum $ qspecl_then [‘m’,‘dec_clock (ticks+1) t1’] mp_tac
                      >> impl_tac >- gvs [state_rel_dec_clock, dec_clock_def]
                      >> strip_tac >> gvs [] >> qexists_tac ‘t1'’ >> every_case_tac >> gvs []
                     )
                  >> Cases_on ‘x’ >> gvs[]
                  >> ‘code_rel m r.code t1.code’ by gvs [state_rel_def]
                  >> pop_assum $ assume_tac o SRULE[code_rel_def] >> gvs[]
                  >> first_x_assum $ qspecl_then [‘n’,‘LENGTH (FRONT a)’,‘r'’] assume_tac >> gvs[]
                  >> drule_all_then assume_tac $ SRULE [] return_shape_tail_ok >> gvs[]
                  >> Cases_on ‘(dec_clock (ticks+1) t1).clock = 0’
                  >- (qexists_tac ‘dec_clock (ticks+1) t1 with clock := 0’ >> disj2_tac
                      >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                      >> imp_res_tac evaluate_io_events_mono >> gvs []
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH (FRONT a)), FRONT a, t) =
                                                       (Rval (TAKE (LENGTH (FRONT a)) (DROP 0 (FRONT a))), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                     )
                  >> first_x_assum $ qspecl_then [‘m’,‘dec_clock 1 (dec_clock (ticks+1) t1)’,‘n’,‘r''’,
                                                  ‘return_shape m' n (LENGTH (FRONT a)) r'’] mp_tac
                  >> impl_tac
                  >- (gvs [state_rel_clock, dec_clock_def]
                      >> irule tail_ok_submap
                      >> qexists ‘m'’
                      >> gvs[submap_def]
                     )
                  >> strip_tac >> Cases_on ‘res0’ >> gvs []
                  >- (Cases_on ‘a'’ >> gvs [] >> Cases_on ‘t'’ >> gvs []
                      >> qexists_tac ‘t1'’ >> disj1_tac
                      >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH (FRONT a)), FRONT a, t) =
                                                       (Rval (TAKE (LENGTH (FRONT a)) (DROP 0 (FRONT a))), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> subgoal ‘worker_body m' n r'' (return_shape m' n (LENGTH (FRONT a)) r') r' =
                                  worker_body m n r'' (return_shape m' n (LENGTH (FRONT a)) r') r'’
                      >- (irule worker_body_submap
                          >> gvs[submap_def]
                         )
                      >> gvs[]
                      >> subgoal ‘LENGTH (flat_vals (return_shape m' n (LENGTH (FRONT a)) r') h) =
                                  shape_width (return_shape m' n (LENGTH (FRONT a)) r')’
                      >- gvs[flat_vals_LENGTH]
                      >> gvs[]
                      >> ‘evaluate
                          ([rebuild 0 (return_shape m' n (LENGTH (FRONT a)) r')],
                           flat_vals (return_shape m' n (LENGTH (FRONT a)) r') h ++
                           FRONT a,t1') = (Rval [h],t1')’ suffices_by rw[]
                      >> irule $ cj 1 evaluate_rebuild
                      >> gvs[TAKE_APPEND1]
                     )
                  >- (Cases_on ‘e’ >> gvs[]
                      >- (Cases_on ‘a'’ >> gvs[]
                          >> qexists_tac ‘t1'’ >> disj1_tac
                          >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                          >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH (FRONT a)), FRONT a, t) =
                                                           (Rval (TAKE (LENGTH (FRONT a)) (DROP 0 (FRONT a))), t)’
                          >- (irule evaluate_genlist_vars
                              >> gvs[]
                             )
                          >> pop_assum $ assume_tac o SRULE[]
                          >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                          >> gvs[bvlSemTheory.find_code_def]
                          >> subgoal ‘worker_body m' n r'' (return_shape m' n (LENGTH (FRONT a)) r') r' =
                                      worker_body m n r'' (return_shape m' n (LENGTH (FRONT a)) r') r'’
                          >- (irule worker_body_submap
                              >> gvs[submap_def]
                             )
                          >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                         )
                      >> qexists_tac ‘t1'’ >> disj1_tac
                      >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH (FRONT a)), FRONT a, t) =
                                                       (Rval (TAKE (LENGTH (FRONT a)) (DROP 0 (FRONT a))), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> subgoal ‘worker_body m' n r'' (return_shape m' n (LENGTH (FRONT a)) r') r' =
                                  worker_body m n r'' (return_shape m' n (LENGTH (FRONT a)) r') r'’
                      >- (irule worker_body_submap
                          >> gvs[submap_def]
                         )
                      >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def]
                     )
                  >> (qexists_tac ‘t1'’ >> disj2_tac
                      >> gvs[evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH (FRONT a)), FRONT a, t) =
                                                       (Rval (TAKE (LENGTH (FRONT a)) (DROP 0 (FRONT a))), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> gvs[bvlSemTheory.find_code_def]
                      >> subgoal ‘worker_body m' n r'' (return_shape m' n (LENGTH (FRONT a)) r') r' =
                                  worker_body m n r'' (return_shape m' n (LENGTH (FRONT a)) r') r'’
                      >- (irule worker_body_submap
                          >> gvs[submap_def]
                         )
                      >> gvs [evaluate_def, state_rel_def, dec_clock_def, make_wrapper_def])
                 )
              >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
              >> drule_all_then assume_tac code_rel_find_code_SOME_dest >> gvs[]
              >> Cases_on ‘lookup x m’ >> gvs[]
              >- (Cases_on ‘evaluate ([r'],a,dec_clock (ticks + 1) r)’ >> gvs[]
                  >> Cases_on ‘q’ >> gvs[]
                  >- (IF_CASES_TAC >> gvs[]
                      >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                      bviPropsTheory.evaluate_io_events_mono
                          >> gvs [dec_clock_def]
                         )
                      >> last_x_assum $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                      >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                      >> strip_tac >> gvs[]
                     )
                  >> Cases_on ‘e’ >> gvs[]
                  >- (Cases_on ‘a'’ >> gvs[]
                      >> Cases_on ‘handler’ >> gvs[]
                      >- (IF_CASES_TAC >> gvs[]
                          >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                              >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                             bviPropsTheory.evaluate_io_events_mono
                              >> gvs [dec_clock_def]
                             )
                          >> last_x_assum $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                          >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                          >> strip_tac >> gvs[]
                         )
                      >> Cases_on ‘evaluate ([x'],v::env,r'')’ >> gvs[]
                      >> Cases_on ‘q’ >> gvs[]
                      >- (IF_CASES_TAC >> gvs[]
                          >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                              >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                             bviPropsTheory.evaluate_io_events_mono
                              >> gvs[dec_clock_def]
                              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                              >> metis_tac[isPREFIX_TRANS]
                             )
                          >> qpat_x_assum ‘∀_ _. _ ∧ _ ⇒ _’ $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                          >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                          >> strip_tac >> gvs[]
                          >- (last_x_assum $ qspecl_then [‘m’, ‘t1'’] mp_tac
                              >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                              >> strip_tac >> gvs[]
                             )
                          >> irule isPREFIX_TRANS
                          >> first_assum $ irule_at Any
                          >> irule bviPropsTheory.evaluate_io_events_mono
                          >> metis_tac[]
                         )
                      >> Cases_on ‘e’ >> gvs[]
                      >- (Cases_on ‘a'’ >> gvs[]
                          >> IF_CASES_TAC >> gvs[]
                          >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                              >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                             bviPropsTheory.evaluate_io_events_mono
                              >> gvs[dec_clock_def]
                              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                              >> metis_tac[isPREFIX_TRANS]
                             )
                          >> qpat_x_assum ‘∀_ _. _ ∧ _ ⇒ _’ $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                          >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                          >> strip_tac >> gvs[]
                          >- (last_x_assum $ qspecl_then [‘m’, ‘t1'’] mp_tac
                              >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                              >> strip_tac >> gvs[]
                             )
                          >> irule isPREFIX_TRANS
                          >> first_assum $ irule_at Any
                          >> irule bviPropsTheory.evaluate_io_events_mono
                          >> metis_tac[]
                         )
                      >> IF_CASES_TAC
                      >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                          >> disj2_tac
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[dec_clock_def]
                          >> metis_tac[isPREFIX_TRANS]
                         )
                      >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock (ticks + 1) r) t' ∧ _ ⇒ _’
                                      (qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’] mp_tac)
                      >> impl_tac >- gvs [state_rel_clock, dec_clock_def]
                      >> strip_tac
                      >- (gvs[]
                          >> qpat_x_assum ‘∀m' t'. state_rel m' r'' t' ∧ _ ⇒ _’
                                          (qspecl_then [‘m’,‘t1'’] mp_tac)
                          >> impl_tac >- gvs []
                          >> strip_tac
                          >- (qexists_tac ‘t1''’ >> disj1_tac >> gvs []
                             )
                          >> qexists_tac ‘t1''’ >> disj2_tac >> gvs [] >>
                          disj2_tac >> gvs[state_rel_def, dec_clock_def]
                          >> imp_res_tac evaluate_io_events_mono
                          >> gvs[]
                          >> metis_tac[IS_PREFIX_TRANS, IS_PREFIX_REFL]
                         )
                      >> gvs [] >> qexists_tac ‘t1'’ >> disj2_tac >> gvs []
                      >> irule isPREFIX_TRANS
                      >> first_assum $ irule_at Any
                      >> irule bviPropsTheory.evaluate_io_events_mono
                      >> metis_tac[]
                     )
                  >> IF_CASES_TAC >> gvs[]
                  >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                      >> disj2_tac
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[dec_clock_def]
                      >> metis_tac[isPREFIX_TRANS]
                     )
                  >> last_x_assum $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                  >> impl_tac >- gvs[state_rel_def, dec_clock_def, oracle_free_def]
                  >> strip_tac >> gvs[]
                  >- metis_tac[]
                  >> metis_tac[]
                 )
              >> Cases_on ‘x'’ >> gvs[]
              >> Cases_on ‘evaluate ([r'],a,dec_clock (ticks + 1) r)’ >> gvs[]
              >> Cases_on ‘q'’ >> gvs[]
              >- (IF_CASES_TAC >> gvs[]
                  >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                     bviPropsTheory.evaluate_io_events_mono
                      >> gvs [dec_clock_def]
                     )
                  >> gvs[evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                   (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> rw[bvlSemTheory.find_code_def, dec_clock_def]
                  >- (irule isPREFIX_TRANS
                      >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                      >> last_assum $ irule_at (Pos hd)
                      >> rw[dec_clock_def]
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[]
                     )
                  >> assume_tac evaluate_LENGTH
                  >> pop_assum $ qspecl_then [‘[r']’, ‘a’, ‘dec_clock (ticks + 1) r’] assume_tac >> gvs[]
                  >> Cases_on ‘a'’ >> gvs[]
                  >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                    by gvs[dec_clock_def, state_rel_clock]
                  >> ‘t1.clock ≤ ticks + ((dec_clock (ticks + 1) r).clock + 2)’ by gvs[dec_clock_def]
                  >> first_x_assum $ drule_then assume_tac >> gvs[]
                  >> pop_assum $ drule_all_then assume_tac >> gvs[]
                  >> ‘LENGTH (flat_vals q h) = shape_width q’ by rw[flat_vals_LENGTH]
                  >> gvs[]
                  >> ‘evaluate ([rebuild 0 q],flat_vals q h ++ a,t1') = (Rval [h],t1')’ suffices_by rw[]
                  >> irule $ cj 1 evaluate_rebuild
                  >> gvs[TAKE_APPEND1]
                 )
              >> Cases_on ‘e’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> Cases_on ‘handler’ >> gvs[]
                  >- (IF_CASES_TAC >> gvs[]
                      >- (‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> qspecl_then [‘[r']’,‘a’,‘dec_clock (ticks + 1) r’] mp_tac
                                         bviPropsTheory.evaluate_io_events_mono
                          >> gvs [dec_clock_def]
                         )
                      >> gvs[evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                       (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> rw[bvlSemTheory.find_code_def, dec_clock_def]
                      >- (irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> rw[dec_clock_def]
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[]
                         )
                      >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                        by gvs[dec_clock_def, state_rel_clock]
                      >> ‘t1.clock ≤ ticks + ((dec_clock (ticks + 1) r).clock + 2)’ by gvs[dec_clock_def]
                      >> first_x_assum $ drule_then assume_tac >> gvs[]
                      >> pop_assum $ drule_all_then assume_tac >> gvs[]
                     )
                  >> Cases_on ‘evaluate ([x'],v::env,r'³')’ >> gvs[]
                  >> Cases_on ‘q'’ >> gvs[]
                  >- (IF_CASES_TAC >> gvs[]
                      >- (irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> rw[dec_clock_def]
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[]
                         )
                      >> gvs[evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                       (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> rw[bvlSemTheory.find_code_def]
                      >- (irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> rw[dec_clock_def]
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[]
                         )
                      >> assume_tac evaluate_LENGTH
                      >> pop_assum $ qspecl_then [‘[x']’, ‘v::env’, ‘r'''’] assume_tac >> gvs[]
                      >> Cases_on ‘a'’ >> gvs[]
                      >> ‘state_rel m (dec_clock (ticks + 1) r) (dec_clock 1 (dec_clock (ticks + 1) t1))’
                        by gvs[dec_clock_def, state_rel_clock]
                      >> ‘(dec_clock 1 (dec_clock (ticks + 1) t1)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                      >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
                         )
                      >> irule isPREFIX_TRANS
                      >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                      >> last_assum $ irule_at (Pos hd)
                      >> gvs[]
                     )
                  >> Cases_on ‘e’ >> gvs[]
                  >- (Cases_on ‘a'’ >> gvs[]
                      >> IF_CASES_TAC >> gvs[]
                      >- (irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> rw[dec_clock_def]
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[]
                         )
                      >> gvs[evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                       (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> rw[bvlSemTheory.find_code_def]
                      >- (irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> irule isPREFIX_TRANS
                          >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                          >> last_assum $ irule_at (Pos hd)
                          >> rw[dec_clock_def]
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[]
                         )
                      >> ‘state_rel m (dec_clock (ticks + 1) r) (dec_clock 1 (dec_clock (ticks + 1) t1))’
                        by gvs[dec_clock_def, state_rel_clock]
                      >> ‘(dec_clock 1 (dec_clock (ticks + 1) t1)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                      >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
                         )
                      >> irule isPREFIX_TRANS
                      >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                      >> last_assum $ irule_at (Pos hd)
                      >> gvs[]
                     )
                  >> Cases_on ‘a'’ >> gvs[]
                  >- (IF_CASES_TAC >> gvs[]
                      >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                          >> disj2_tac
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[dec_clock_def]
                          >> metis_tac[isPREFIX_TRANS]
                         )
                      >> gvs[evaluate_def, make_wrapper_def]
                      >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                       (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                      >- (irule evaluate_genlist_vars
                          >> gvs[]
                         )
                      >> pop_assum $ assume_tac o SRULE[]
                      >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                      >> rw[bvlSemTheory.find_code_def, dec_clock_def]
                      >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                          >> disj2_tac
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                          >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                          >> gvs[dec_clock_def]
                          >> metis_tac[isPREFIX_TRANS]
                         )
                      >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                        by gvs[dec_clock_def, state_rel_clock]
                      >> ‘(t1 with clock := t1.clock − (ticks + 2)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
                      >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                      >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
                          >> metis_tac[]
                         )
                      >> qexists ‘t1'’ >> disj2_tac >> gvs[]
                      >> irule isPREFIX_TRANS
                      >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                      >> last_assum $ irule_at (Pos hd)
                      >> gvs[]
                     )
                  >> IF_CASES_TAC >> gvs[]
                  >- (dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[dec_clock_def]
                      >> metis_tac[isPREFIX_TRANS]
                     )
                  >> gvs[evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                   (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> rw[bvlSemTheory.find_code_def, dec_clock_def]
                  >- (dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[dec_clock_def]
                      >> metis_tac[isPREFIX_TRANS]
                     )
                     
                  >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                    by gvs[dec_clock_def, state_rel_clock]
                  >> ‘(t1 with clock := t1.clock − (ticks + 2)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
                  >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                  >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
                     )
                  >> irule isPREFIX_TRANS
                  >> irule_at (Pos last) bviPropsTheory.evaluate_io_events_mono
                  >> last_assum $ irule_at (Pos hd)
                  >> gvs[]
                 )
              >> Cases_on ‘a'’ >> gvs[]
              >- (IF_CASES_TAC >> gvs[]
                  >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                      >> disj2_tac
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[dec_clock_def]
                      >> metis_tac[isPREFIX_TRANS]
                     )
                  >> gvs[evaluate_def, make_wrapper_def]
                  >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                                   (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
                  >- (irule evaluate_genlist_vars
                      >> gvs[]
                     )
                  >> pop_assum $ assume_tac o SRULE[]
                  >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
                  >> rw[bvlSemTheory.find_code_def, dec_clock_def]
                  >- (qexists_tac ‘t1 with clock := 0’ >> gvs[]
                      >> disj2_tac
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                      >> gvs[dec_clock_def]
                      >> metis_tac[isPREFIX_TRANS]
                     )
                  >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                    by gvs[dec_clock_def, state_rel_clock]
                  >> ‘(t1 with clock := t1.clock − (ticks + 2)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
                  >> first_x_assum $ drule_all_then assume_tac >> gvs[]
                  >> metis_tac[]
                 )
              >> IF_CASES_TAC >> gvs[]
              >- (dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                  >> gvs[dec_clock_def]
                  >> metis_tac[isPREFIX_TRANS]
                 )
              >> gvs[evaluate_def, make_wrapper_def]
              >> subgoal ‘∀(t:('a, 'b) state). evaluate (GENLIST (λarg. Var (arg + 0)) (LENGTH a), a, t) =
                                               (Rval (TAKE (LENGTH a) (DROP 0 a)), t)’
              >- (irule evaluate_genlist_vars
                  >> gvs[]
                 )
              >> pop_assum $ assume_tac o SRULE[]
              >> pop_assum $ assume_tac o (CONV_RULE $ DEPTH_CONV ETA_CONV)
              >> rw[bvlSemTheory.find_code_def, dec_clock_def]
              >- (dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> dxrule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> ‘t1.ffi = r.ffi’ by gvs [state_rel_def]
                  >> gvs[dec_clock_def]
                  >> metis_tac[isPREFIX_TRANS]
                 )
              >> ‘state_rel m (dec_clock (ticks + 1) r) (t1 with clock := t1.clock − (ticks + 2))’
                by gvs[dec_clock_def, state_rel_clock]
              >> ‘(t1 with clock := t1.clock − (ticks + 2)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
              >> first_x_assum $ drule_all_then assume_tac >> gvs[]
             )
          >> last_x_assum $ drule_all_then assume_tac >> gvs[]
          >> metis_tac[]
         )
                
      >> Cases_on ‘handler’ >> Cases_on ‘dest’
      >> gvs[tail_ok_def, tail_form_def, split_ok_def, shape_width_def, no_ret_def]
      >> rename1 ‘Call ticks (SOME d) xs NONE’
      >> ‘∃wk'. lookup d m = SOME (sh,wk') ∧
                worker_body m f wk sh (Call ticks (SOME d) xs NONE) =
                  TailCall (shape_width sh) ticks wk' xs’
           by (gvs[worker_body_def] >> IF_CASES_TAC >> gvs[]
               >> every_case_tac >> gvs[])
      >> gvs[]
      >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
          >> reverse $ Cases_on ‘q’ >> gvs[]
          >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
              >> rw[evaluate_def, worker_body_def]
              >> metis_tac[]
             )
          >> first_x_assum $ drule_all_then assume_tac >> reverse $ gvs[]
          >- (Cases_on ‘find_code (SOME d) a r.code’ >> gvs[]
              >> Cases_on ‘x’ >> gvs[]
              >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
              >- (qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
                 )
              >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
              >> Cases_on ‘q'’ >> gvs[]
              >- (qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
                  >> irule isPREFIX_TRANS
                  >> first_assum $ irule_at (Pos hd)
                  >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> gvs[dec_clock_def]
                 )
              >> Cases_on ‘e’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[]
                  >> qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
                  >> irule isPREFIX_TRANS
                  >> first_assum $ irule_at (Pos hd)
                  >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> gvs[dec_clock_def]
                 )
              >> qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at (Pos hd)
              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
             )
          >> Cases_on ‘find_code (SOME d) a r.code’ >> gvs[]
          >> PairCases_on ‘x’ >> gvs[]
          >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
          >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> gvs[worker_body_def]
          >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
          >- (qexists ‘t1 with clock := 0’ >> disj1_tac
              >> gvs[evaluate_def, bvlSemTheory.find_code_def]
              >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
              >> first_assum $ irule
             )

          >> Cases_on ‘evaluate ([x1],a,dec_clock (ticks + 1) r)’ >> gvs[]
          >> rename1 ‘_ = (res0,s0)’
          >> ‘res = res0 ∧ s1' = s0 ∧ res0 ≠ Rerr (Rabort Rtype_error) ∧
              ∀rvs. res0 ≠ Rerr (Rraise (Ret rvs))’
            by (every_case_tac >> gvs[]
               )
          >> gvs[]
          >> Cases_on ‘t1.clock < ticks + 1’
          >- (qexists ‘t1 with clock := 0’ >> disj2_tac
              >> gvs[evaluate_def, bvlSemTheory.find_code_def]
              >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
              >> first_assum $ irule_at Any >> gvs[state_accessors]
             )
          >> first_x_assum $ qspecl_then
                           [‘m’,‘dec_clock (ticks + 1) t1’,‘d’,‘wk’,‘sh’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def])
          >> strip_tac
          >- (Cases_on ‘res’ >> gvs[]
              >- (Cases_on ‘a'’ >> gvs[] >> Cases_on ‘t'’ >> gvs[]
                  >> qexists ‘t1'’ >> disj1_tac >> gvs[]
                  >> irule_at Any evaluate_TailCall
                  >> irule_at Any (cj 1 flat_vals_LENGTH)
                  >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
                  >> metis_tac[]
                 )
              >> qexists ‘t1'’ >> disj1_tac >> gvs[]
              >> irule evaluate_TailCall_err
              >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
              >> metis_tac[]
             )
          >> qexists ‘t1'’ >> disj2_tac >> gvs[]
          >> irule_at Any evaluate_TailCall_err
          >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
          >> metis_tac[]
             
         )
                
      >> Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
          >> rw[evaluate_def, worker_body_def]
          >> metis_tac[]
         )
      >> first_x_assum $ drule_all_then assume_tac >> reverse $ gvs[]
      >- (Cases_on ‘find_code (SOME d) a r.code’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
          >- (qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
             )
          >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
          >- (qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at (Pos hd)
              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
             )
          >> Cases_on ‘e’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at (Pos hd)
              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
             )
          >> qexists ‘t1’ >> disj2_tac >> rw[evaluate_def, worker_body_def]
          >> irule isPREFIX_TRANS
          >> first_assum $ irule_at (Pos hd)
          >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
          >> gvs[dec_clock_def]
         )
      >> Cases_on ‘find_code (SOME d) a r.code’ >> gvs[]
      >> PairCases_on ‘x’ >> gvs[]
      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
      >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
      >> gvs[worker_body_def]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >- (qexists ‘t1 with clock := 0’ >> disj1_tac
          >> gvs[evaluate_def, bvlSemTheory.find_code_def]
          >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
          >> first_assum $ irule
         )

      >> Cases_on ‘evaluate ([x1],a,dec_clock (ticks + 1) r)’ >> gvs[]
      >> rename1 ‘_ = (res0,s0)’
      >> ‘res = res0 ∧ s1' = s0 ∧ res0 ≠ Rerr (Rabort Rtype_error) ∧
          ∀rvs. res0 ≠ Rerr (Rraise (Ret rvs))’
        by (every_case_tac >> gvs[]
           )
      >> gvs[]
      >> Cases_on ‘t1.clock < ticks + 1’
      >- (qexists ‘t1 with clock := 0’ >> disj2_tac
          >> gvs[evaluate_def, bvlSemTheory.find_code_def]
          >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
          >> first_assum $ irule_at Any >> gvs[state_accessors]
         )

      >> qpat_x_assum ‘∀m' t' f' wk' sh'. _ ∧ _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x1 ⇒ _’ $
                      qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’,‘d’,‘dwk’,‘sh’] mp_tac
      >> impl_tac
      >- (conj_tac
          >- (irule state_rel_dec_clock >> gvs[])
          >> gvs[dec_clock_def])
      >> strip_tac

      >- (Cases_on ‘res’ >> gvs[]
          >- (rename1 ‘Rval vs’ >> Cases_on ‘vs’ >> gvs[]
              >> rename1 ‘Rval (v::vs)’ >> Cases_on ‘vs’ >> gvs[]
              >> qexists ‘t1'’ >> disj1_tac >> gvs[]
              >> irule_at Any evaluate_TailCall
              >> irule_at Any (cj 1 flat_vals_LENGTH)
              >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
              >> metis_tac[])
          >> qexists ‘t1'’ >> disj1_tac >> gvs[]
          >> irule evaluate_TailCall_err
          >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
          >> metis_tac[]
          )

      >> qexists ‘t1'’ >> disj2_tac >> gvs[]
      >> irule_at Any evaluate_TailCall_err
      >> gvs[bvlSemTheory.find_code_def, dec_clock_def]
      >> metis_tac[]             
     )

        
  >> rw[evaluate_def]
  >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (first_x_assum $ drule_all_then assume_tac >> gvs[] >> metis_tac[]
         )
      >> first_x_assum $ drule_all_then assume_tac >> reverse $ gvs[]
      >- (Cases_on ‘find_code (SOME dest) a r.code’ >> gvs[]
          >> PairCases_on ‘x’ >> gvs[]
          >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
          >- metis_tac[state_rel_clock]
          >> Cases_on ‘evaluate ([x1],x0,dec_clock (ticks + 1) r)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >> Cases_on ‘e’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >- (irule isPREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> gvs[dec_clock_def]
                 )
              >> Cases_on ‘LENGTH l = rets’ >> gvs[]
              >> qexists ‘t1’ >> disj2_tac >> gvs[]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at Any
              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at Any
              >> irule bviPropsTheory.evaluate_io_events_mono
              >> metis_tac[]
             )
          >> qexists ‘t1’ >> disj2_tac >> gvs[]
          >> irule isPREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
          >> gvs[dec_clock_def]
         )
         
      >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
      >> Cases_on ‘find_code (SOME dest) a r.code’ >> gvs[]
      >> PairCases_on ‘x’ >> gvs[]
      >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >- (Cases_on ‘lookup dest m’ >> gvs[]
          >- (qexists ‘t1 with clock := 0’ >> disj1_tac >> gvs[]
              >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
              >> first_assum $ irule)
          >> PairCases_on ‘x’ >> gvs[]
          >> qexists ‘t1 with clock := 0’ >> disj1_tac
          >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def]
          >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
          >> first_assum $ irule
         )
         
      >> Cases_on ‘evaluate ([x1],a,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘e’ >> gvs[]
      >- (Cases_on ‘a'’ >> gvs[]
          >- (Cases_on ‘lookup dest m’ >> gvs[]
              >- (IF_CASES_TAC >> gvs[]
                  >- (drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                      >> gvs[dec_clock_def]
                      >> irule isPREFIX_TRANS
                      >> first_assum $ irule_at Any
                      >> ‘t1.ffi = r.ffi’ suffices_by rw[]
                      >> gvs[state_rel_def]
                     )
                  >> last_x_assum $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
                  >> impl_tac >- gvs[state_rel_dec_clock, dec_clock_def]
                  >> strip_tac >> gvs[]
                 )
              >> PairCases_on ‘x’ >> gvs[]
              >> Cases_on ‘t1.clock < ticks + 1’ >> gvs[]
              >- (drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> gvs[dec_clock_def]
                  >> irule isPREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> ‘t1.ffi = r.ffi’ suffices_by rw[]
                  >> gvs[state_rel_def]
                 )
              >> Cases_on ‘t1.clock ≤ ticks + 1’ >> gvs[]
              >- (qexists ‘t1 with clock := 0’ >> disj2_tac
                  >> ‘t1.clock = ticks + 1’ by gvs[]
                  >> gvs[dec_clock_def, make_wrapper_def, evaluate_def]
                  >> conj_tac
                  >- (qspecl_then [‘LENGTH a’,‘a’,‘[]’,‘t1 with clock := 0’] assume_tac
                                  evaluate_genlist_prefix
                      >> gvs[bvlSemTheory.find_code_def]
                     )
                  >> irule lag_events
                  >> first_assum $ irule_at Any
                  >> gvs[state_rel_def, state_accessors]
                 )
              >> subgoal ‘state_rel m (dec_clock (ticks + 1) r) (dec_clock 1 (dec_clock (ticks + 1) t1))’
              >- (irule state_rel_dec_clock
                  >> gvs[dec_clock_def, state_rel_clock]
                 )
              >> ‘(dec_clock 1 (dec_clock (ticks + 1) t1)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
              >> first_x_assum $ drule_all_then assume_tac >> gvs[]
              >- (qexists ‘t1'’ >> disj1_tac >> gvs[]
                  >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
                      (Rerr (Rraise (Exn v)),t1')’ suffices_by rw[]
                  >> irule evaluate_make_wrapper_err
                  >> gvs[dec_clock_def]
                 )
                
              >> qexists ‘t1'’ >> disj2_tac >> gvs[]
              >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
                  (Rerr (Rabort Rtimeout_error),t1')’ suffices_by rw[]
              >> irule evaluate_make_wrapper_err
              >> gvs[dec_clock_def]
             )
          >> Cases_on ‘LENGTH l = rets’ >> gvs[]
          >> Cases_on ‘lookup dest m’ >> gvs[]
          >- (IF_CASES_TAC >> gvs[]
              >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
                  >> irule isPREFIX_TRANS
                  >> irule_at (Pos last) evaluate_io_events_mono
                  >> last_assum $ irule_at (Pos hd)
                  >> irule lag_events
                  >> first_assum $ irule_at Any
                  >> gvs[state_rel_def, dec_clock_def, state_accessors]
                 )
              >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock (ticks + 1) r) t' ∧ _ ⇒ _’ $
                              qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’] mp_tac
              >> impl_tac
              >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def])
              >> strip_tac >- gvs[]
              >> qexists ‘t1'’ >> disj2_tac >> gvs[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> irule evaluate_io_events_mono
              >> metis_tac[]
             )
          >> PairCases_on ‘x’ >> gvs[]
          >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
         )
      >> Cases_on ‘lookup dest m’ >> gvs[]
      >- (IF_CASES_TAC
          >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
              >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
              >> first_assum $ irule_at Any >> gvs[state_accessors])
          >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock (ticks + 1) r) t' ∧ _ ⇒ _’ $
                          qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def])
          >> strip_tac
          >> qexists ‘t1'’ >> gvs[]
         )
      >> PairCases_on ‘x’ >> gvs[]
      >> IF_CASES_TAC
      >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
          >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
          >> first_assum $ irule_at Any >> gvs[state_accessors]
         )
      >> Cases_on ‘t1.clock ≤ ticks + 1’ >> gvs[]
      >- (qexists ‘t1 with clock := 0’ >> disj2_tac
          >> ‘t1.clock = ticks + 1’ by gvs[]
          >> gvs[dec_clock_def, make_wrapper_def, evaluate_def]
          >> conj_tac
          >- (qspecl_then [‘LENGTH a’,‘a’,‘[]’,‘t1 with clock := 0’] assume_tac
                          evaluate_genlist_prefix
              >> gvs[bvlSemTheory.find_code_def]
             )
          >> irule lag_events
          >> first_assum $ irule_at Any
          >> gvs[state_rel_def, state_accessors]
         )

      >> qpat_x_assum ‘∀m' t' f wk sh. _ ∧ _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x1 ⇒ _’ $
                      qspecl_then [‘m’,‘dec_clock 1 (dec_clock (ticks + 1) t1)’,
                                   ‘dest’,‘x1'’,‘x0’] mp_tac
      >> impl_tac
      >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def, state_rel_clock]
         )
      >> strip_tac
      >- (qexists ‘t1'’ >> disj1_tac >> gvs[]
          >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
              (Rerr (Rabort a'),t1')’ suffices_by rw[]
          >> irule evaluate_make_wrapper_err >> gvs[dec_clock_def]
         )
      >> qexists ‘t1'’ >> disj2_tac >> gvs[]
      >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
          (Rerr (Rabort Rtimeout_error),t1')’ suffices_by rw[]
      >> irule_at Any evaluate_make_wrapper_err >> gvs[dec_clock_def]
     )
  >> rw[worker_body_def, evaluate_def]
  >> gvs[tail_ok_def, tail_form_def]
  >> Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
  >> reverse $ Cases_on ‘q’ >> gvs[]
  >- (first_x_assum $ drule_all_then assume_tac >> gvs[] >> metis_tac[]
     )
  >> first_x_assum $ drule_all_then assume_tac >> reverse $ gvs[]
  >- (Cases_on ‘find_code (SOME dest) a r.code’ >> gvs[]
      >> PairCases_on ‘x’ >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >- metis_tac[state_rel_clock]
      >> Cases_on ‘evaluate ([x1],x0,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘e’ >> gvs[]
      >- (Cases_on ‘a'’ >> gvs[]
          >- (irule isPREFIX_TRANS
              >> first_assum $ irule_at Any
              >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
             )
          >> Cases_on ‘LENGTH l = rets’ >> gvs[]
          >> qexists ‘t1’ >> disj2_tac >> gvs[]
          >> irule isPREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
          >> gvs[dec_clock_def]
          >> irule isPREFIX_TRANS
          >> first_assum $ irule_at Any
          >> irule bviPropsTheory.evaluate_io_events_mono
          >> metis_tac[]
         )
      >> qexists ‘t1’ >> disj2_tac >> gvs[]
      >> irule isPREFIX_TRANS
      >> first_assum $ irule_at Any
      >> drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
      >> gvs[dec_clock_def]
     )
     
  >> ‘code_rel m r.code t1.code’ by gvs[state_rel_def]
  >> Cases_on ‘find_code (SOME dest) a r.code’ >> gvs[]
  >> PairCases_on ‘x’ >> gvs[]
  >> drule_all_then strip_assume_tac code_rel_find_code_SOME_dest >> gvs[]
  >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
  (* LEAF: source timed out at the call; so does the target *)
  >- (Cases_on ‘lookup dest m’ >> gvs[]
      >- (qexists ‘t1 with clock := 0’ >> disj1_tac >> gvs[]
          >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
          >> first_assum $ irule)
      >> PairCases_on ‘x’ >> gvs[]
      >> qexists ‘t1 with clock := 0’ >> disj1_tac
      >> gvs[make_wrapper_def, evaluate_def, bvlSemTheory.find_code_def]
      >> irule $ cj 1 state_rel_clock >> irule $ cj 2 state_rel_clock
      >> first_assum $ irule
     )
     
  >> Cases_on ‘evaluate ([x1],a,dec_clock (ticks + 1) r)’ >> gvs[]
  >> Cases_on ‘q’ >> gvs[]
  >> Cases_on ‘e’ >> gvs[]
  >- (Cases_on ‘a'’ >> gvs[]
      >- (Cases_on ‘lookup dest m’ >> gvs[]
          >- (IF_CASES_TAC >> gvs[]
              >- (drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
                  >> gvs[dec_clock_def]
                  >> irule isPREFIX_TRANS
                  >> first_assum $ irule_at Any
                  >> ‘t1.ffi = r.ffi’ suffices_by rw[]
                  >> gvs[state_rel_def]
                 )
              >> last_x_assum $ qspecl_then [‘m’, ‘dec_clock (ticks + 1) t1’] mp_tac
              >> impl_tac >- gvs[state_rel_dec_clock, dec_clock_def]
              >> strip_tac >> gvs[]
             )
          >> PairCases_on ‘x’ >> gvs[]
          >> Cases_on ‘t1.clock < ticks + 1’ >> gvs[]
          >- (drule_then assume_tac bviPropsTheory.evaluate_io_events_mono
              >> gvs[dec_clock_def]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at Any
              >> ‘t1.ffi = r.ffi’ suffices_by rw[]
              >> gvs[state_rel_def]
             )
          >> Cases_on ‘t1.clock ≤ ticks + 1’ >> gvs[]
          >- (qexists ‘t1 with clock := 0’ >> disj2_tac
              >> ‘t1.clock = ticks + 1’ by gvs[]
              >> gvs[dec_clock_def, make_wrapper_def, evaluate_def]
              >> conj_tac
              >- (qspecl_then [‘LENGTH a’,‘a’,‘[]’,‘t1 with clock := 0’] assume_tac
                              evaluate_genlist_prefix
                  >> gvs[bvlSemTheory.find_code_def]
                 )
              >> irule lag_events
              >> first_assum $ irule_at Any
              >> gvs[state_rel_def, state_accessors]
             )
          >> subgoal ‘state_rel m (dec_clock (ticks + 1) r) (dec_clock 1 (dec_clock (ticks + 1) t1))’
          >- (irule state_rel_dec_clock
              >> gvs[dec_clock_def, state_rel_clock]
             )
          >> ‘(dec_clock 1 (dec_clock (ticks + 1) t1)).clock ≤ (dec_clock (ticks + 1) r).clock’ by gvs[dec_clock_def]
          >> first_x_assum $ drule_all_then assume_tac >> gvs[]
          >- (qexists ‘t1'’ >> disj1_tac >> gvs[]
              >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
                  (Rerr (Rraise (Exn v)),t1')’ suffices_by rw[]
              >> irule evaluate_make_wrapper_err
              >> gvs[dec_clock_def]
             )
             
          >> qexists ‘t1'’ >> disj2_tac >> gvs[]
          >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
              (Rerr (Rabort Rtimeout_error),t1')’ suffices_by rw[]
          >> irule evaluate_make_wrapper_err
          >> gvs[dec_clock_def]
         )
      >> Cases_on ‘LENGTH l = rets’ >> gvs[]
      >> Cases_on ‘lookup dest m’ >> gvs[]
      >- (IF_CASES_TAC >> gvs[]
          >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
              >> irule isPREFIX_TRANS
              >> irule_at (Pos last) evaluate_io_events_mono
              >> last_assum $ irule_at (Pos hd)
              >> irule lag_events
              >> first_assum $ irule_at Any
              >> gvs[state_rel_def, dec_clock_def, state_accessors]
             )
          >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock (ticks + 1) r) t' ∧ _ ⇒ _’ $
                          qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’] mp_tac
          >> impl_tac
          >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def])
          >> strip_tac >- gvs[]
          >> qexists ‘t1'’ >> disj2_tac >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> irule evaluate_io_events_mono
          >> metis_tac[]
         )
      >> PairCases_on ‘x’ >> gvs[]
      >> drule_all_then assume_tac evaluate_tail_no_Ret >> gvs[]
     )
     
  >> Cases_on ‘lookup dest m’ >> gvs[]
  >- (IF_CASES_TAC
      >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
          >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
          >> first_assum $ irule_at Any >> gvs[state_accessors]
         )
      >> qpat_x_assum ‘∀m' t'. state_rel m' (dec_clock (ticks + 1) r) t' ∧ _ ⇒ _’ $
                      qspecl_then [‘m’,‘dec_clock (ticks + 1) t1’] mp_tac
      >> impl_tac
      >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def])
      >> strip_tac
      >> qexists ‘t1'’ >> gvs[]
     )
  >> PairCases_on ‘x’ >> gvs[]
  >> IF_CASES_TAC
  >- (qexists ‘t1 with clock := 0’ >> disj2_tac >> gvs[]
      >> irule lag_events >> gvs[state_rel_def, dec_clock_def]
      >> first_assum $ irule_at Any >> gvs[state_accessors]
     )
  >> Cases_on ‘t1.clock ≤ ticks + 1’ >> gvs[]
  >- (qexists ‘t1 with clock := 0’ >> disj2_tac
      >> ‘t1.clock = ticks + 1’ by gvs[]
      >> gvs[dec_clock_def, make_wrapper_def, evaluate_def]
      >> conj_tac
      >- (qspecl_then [‘LENGTH a’,‘a’,‘[]’,‘t1 with clock := 0’] assume_tac
                      evaluate_genlist_prefix
          >> gvs[bvlSemTheory.find_code_def]
         )
      >> irule lag_events
      >> first_assum $ irule_at Any
      >> gvs[state_rel_def, state_accessors]
     )

  >> qpat_x_assum ‘∀m' t' f wk sh. _ ∧ _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x1 ⇒ _’ $
                  qspecl_then [‘m’,‘dec_clock 1 (dec_clock (ticks + 1) t1)’,
                               ‘dest’,‘x1'’,‘x0’] mp_tac
  >> impl_tac
  >- (irule_at Any state_rel_dec_clock >> gvs[dec_clock_def, state_rel_clock]
     )
  >> strip_tac
  >- (qexists ‘t1'’ >> disj1_tac >> gvs[]
      >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
          (Rerr (Rabort a'),t1')’ suffices_by rw[]
      >> irule evaluate_make_wrapper_err >> gvs[dec_clock_def]
     )
  >> qexists ‘t1'’ >> disj2_tac >> gvs[]
  >> ‘evaluate ([make_wrapper (LENGTH a) x1' x0],a,dec_clock (ticks + 1) t1) =
      (Rerr (Rabort Rtimeout_error),t1')’ suffices_by rw[]
  >> irule_at Any evaluate_make_wrapper_err >> gvs[dec_clock_def]
QED

Theorem cpr_lag_timeout:
  ∀xs env m s t s1.
    state_rel m s t ∧ t.clock ≤ s.clock ∧
    evaluate (xs,env,s) = (Rerr (Rabort Rtimeout_error),s1) ⇒
    ∃t1. evaluate (xs,env,t) = (Rerr (Rabort Rtimeout_error),t1) ∧
         t1.ffi.io_events ≼ s1.ffi.io_events
Proof
  rpt strip_tac
  >> drule_at Any (cj 1 cpr_lag)
  >> gvs[] >> disch_then $ drule_then strip_assume_tac
  >> gvs[state_rel_def]
QED



Theorem do_app_no_timeout:
  ∀op vs (s:('c,'ffi) bviSem$state) e.
    do_app op vs s = Rerr e ⇒ e ≠ Rabort Rtimeout_error
Proof
  rw[do_app_def, do_install_def]
  >> every_case_tac >> gvs[]
  >- (Cases_on ‘s.compile_oracle 0’ >> gvs[]
      >> every_case_tac >> gvs[]
     )
  >> gvs[bvlSemTheory.do_app_def, do_app_aux_def]
  >> rpt full_case_tac >> gvs[]
  >- (rpt full_case_tac >> gvs[]
     )
  >- (rpt full_case_tac >> gvs[]
     )
  >- (rpt full_case_tac >> gvs[bvlSemTheory.do_build_const_def]
      >> Cases_on ‘do_build (λx. Number 0) 0 l s.refs’ >> gvs[]
     )
  >> every_case_tac >> gvs[]
QED

Theorem cpr_timeout:
  ∀xs env (s:('a,'b) state).
    (∀m t res s1.
       state_rel m s t ∧
       evaluate (xs,env,s) = (res,s1) ∧
       res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃ck t1 res'.
         evaluate (xs,env,inc_clock ck t) = (res',t1) ∧
         s1.ffi.io_events ≼ t1.ffi.io_events) ∧
    (∀m t e f wk sh res s1.
       xs = [e] ∧ state_rel m s t ∧
       lookup f m = SOME (sh,wk) ∧ split_ok sh ∧
       tail_ok m f sh e ∧ tail_form e ∧
       evaluate ([e],env,s) = (res,s1) ∧
       res ≠ Rerr (Rabort Rtype_error) ⇒
       ∃ck t1 res'.
         evaluate ([worker_body m f wk sh e],env,inc_clock ck t) = (res',t1) ∧
         s1.ffi.io_events ≼ t1.ffi.io_events)
Proof
  recInduct evaluate_ind
  >> rpt conj_tac
  >- gvs[evaluate_def, state_rel_def]
  >- (rw[evaluate_def]
      >> Cases_on ‘evaluate ([x],env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_all_then strip_assume_tac >> gvs[]
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> Cases_on ‘evaluate (y::xs,env,t1)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then irule evaluate_io_events_mono
         )
      >> Cases_on ‘evaluate (y::xs,env,r)’ >> gvs[]
      >> ‘s1 = r'’ by (Cases_on ‘q’ >> gvs[]) >> gvs[]
      >> ‘q ≠ Rerr (Rabort Rtype_error)’ by (Cases_on ‘q’ >> gvs[])
      >> first_x_assum $ drule_all_then assume_tac
      >> gvs[]
      >> qpat_x_assum ‘evaluate ([x],env,inc_clock ck t) = _’ kall_tac
      >> qpat_x_assum ‘r.ffi.io_events ≼ t1.ffi.io_events’ kall_tac
      >> qspecl_then [‘[x]’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
      >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
      >> impl_tac >- gvs[]
      >> strip_tac
      >> qpat_x_assum ‘∀m' t'. state_rel m' r t' ⇒ _’ $ drule_then strip_assume_tac
      >> qexists ‘ck + ck'’
      >> qpat_x_assum ‘evaluate ([x],env,inc_clock ck t) = (Rval a,_)’ assume_tac
      >> drule_then (qspec_then ‘ck'’ assume_tac) evaluate_add_clock
      >> ‘inc_clock ck' (inc_clock ck t) = inc_clock (ck + ck') t’
        by gvs[inc_clock_def, state_component_equality]
      >> gvs[]
      >> Cases_on ‘res'’ >> gvs[]                                           
     )

  >- (rw[evaluate_def]
      >- gvs[state_rel_def]
      >> rw[evaluate_def, worker_body_def]
      >> Cases_on ‘sh’ >> gvs[tail_ok_def, exp_shape_ok_def, split_ok_def, shape_width_def]   
     )

  >- (rw[evaluate_def]
      >> Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_all_then assume_tac >> gvs[]
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> IF_CASES_TAC >> gvs[]
          >- (Cases_on ‘evaluate ([x2],env,t1)’ >> gvs[]
              >> irule isPREFIX_TRANS
              >> first_assum $ irule_at Any
              >> irule evaluate_io_events_mono
              >> metis_tac[]
             )
          >> IF_CASES_TAC >> gvs[]
          >> Cases_on ‘evaluate ([x3],env,t1)’ >> gvs[]
          >> irule isPREFIX_TRANS
          >> first_assum $ irule_at Any
          >> irule evaluate_io_events_mono
          >> metis_tac[]
       )
      >- (qspecl_then [‘[x1]’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
          >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
          >> impl_tac >- gvs[]
          >> strip_tac
          >> Cases_on ‘HD a = Boolv T’ >> gvs[]
          >- (first_x_assum $ drule_all_then strip_assume_tac >> gvs[]
              >> first_x_assum $ drule_all_then strip_assume_tac >> gvs[]
              >> qexists ‘ck + ck' + ck''’
              >> qpat_x_assum ‘evaluate ([x1],env,inc_clock ck t) = _’ assume_tac
              >> drule_then (qspec_then ‘ck' + ck''’ assume_tac) evaluate_add_clock
              >> ‘inc_clock (ck' + ck'') (inc_clock ck t) = inc_clock (ck + ck' + ck'') t’
                by gvs[inc_clock_def, state_component_equality]
              >> gvs[]
              >> qexistsl [‘SND (evaluate ([x2],env,inc_clock (ck' + ck'') t1))’,
                           ‘FST (evaluate ([x2],env,inc_clock (ck' + ck'') t1))’]
              >> simp[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> qspecl_then [‘[x2]’,‘env’,‘inc_clock ck'' t1’,‘ck'’] mp_tac
                             evaluate_add_to_clock_io_events_mono
              >> gvs[inc_clock_def, state_component_equality]
              )
          >> Cases_on ‘HD a = Boolv F’ >> gvs[]
          >> qpat_x_assum ‘∀m' t'. state_rel m' r t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck + ck'’
          >> qpat_x_assum ‘evaluate ([x1],env,inc_clock ck t) = (Rval a,_)’ assume_tac
          >> drule_then (qspec_then ‘ck'’ assume_tac) evaluate_add_clock
          >> ‘inc_clock ck' (inc_clock ck t) = inc_clock (ck + ck') t’
            by gvs[inc_clock_def, state_component_equality]
          >> gvs[]
       )
      >- (gvs[worker_body_def, evaluate_def]
          >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> full_case_tac >> gvs[tail_ok_def, tail_form_def]
          >- (Cases_on ‘evaluate ([worker_body m f wk sh x3],env,t1)’ >> gvs[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> drule_then irule evaluate_io_events_mono
             )
          >> full_case_tac >> gvs[tail_ok_def, tail_form_def]
          >> Cases_on ‘evaluate ([worker_body m f wk sh x2],env,t1)’ >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then irule evaluate_io_events_mono
         )
      >> gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def]
      >> qspecl_then [‘[x1]’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
      >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
      >> impl_tac >- gvs[]
      >> strip_tac
      >> Cases_on ‘HD a = Boolv T’ >> gvs[]
      >- (first_x_assum $ drule_all_then strip_assume_tac
          >> qpat_x_assum ‘∀_ _ _ _ _. _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x2 ⇒ _’ $ drule_all_then assume_tac
          >> gvs[]
          >> qexists ‘ck + ck''’
          >> qpat_x_assum ‘evaluate ([x1],env,inc_clock ck t) = (Rval a,_)’ assume_tac
          >> drule_then (qspec_then ‘ck''’ assume_tac) evaluate_add_clock
          >> ‘inc_clock ck'' (inc_clock ck t) = inc_clock (ck + ck'') t’
            by gvs[inc_clock_def, state_component_equality]
          >> gvs[]
         )
      >> Cases_on ‘HD a = Boolv F’ >> gvs[]
      >> qpat_x_assum ‘∀_ _ _ _ _. _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x3 ⇒ _’ $ drule_all_then assume_tac
      >> gvs[]
      >> qexists ‘ck + ck'’
      >> qpat_x_assum ‘evaluate ([x1],env,inc_clock ck t) = (Rval a,_)’ assume_tac
      >> drule_then (qspec_then ‘ck'’ assume_tac) evaluate_add_clock
      >> ‘inc_clock ck' (inc_clock ck t) = inc_clock (ck + ck') t’
        by gvs[inc_clock_def, state_component_equality]
      >> gvs[]
     )

  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (qspecl_then [‘xs’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
              >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
              >> impl_tac >- gvs[]
              >> strip_tac
              >> qpat_x_assum ‘∀m' t'. state_rel m' r t' ⇒ _’ $ drule_then strip_assume_tac
              >> qexists ‘ck + ck'’
              >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = (Rval a,_)’ assume_tac
              >> drule_then (qspec_then ‘ck'’ assume_tac) evaluate_add_clock
              >> ‘inc_clock ck' (inc_clock ck t) = inc_clock (ck + ck') t’
                by gvs[inc_clock_def, state_component_equality]
              >> gvs[]
             )
          >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> Cases_on ‘evaluate ([x2],a ++ env,t1)’ >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then irule evaluate_io_events_mono
         )
      >> gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> reverse $ Cases_on ‘q’ >> gvs[]

      >- (first_x_assum $ drule_all_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> Cases_on ‘evaluate ([worker_body m f wk sh x2],a ++ env,t1)’ >> gvs[]
          >> irule IS_PREFIX_TRANS
          >> first_assum $ irule_at Any
          >> drule_then irule evaluate_io_events_mono
         )

      >> qspecl_then [‘xs’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
      >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
      >> impl_tac >- gvs[]
      >> strip_tac
      >> qpat_x_assum ‘∀_ _ _ _ _. _ ∧ _ ∧ _ ∧ tail_ok _ _ _ x2 ⇒ _’
                      $ drule_all_then strip_assume_tac
      >> qexists ‘ck + ck'’
      >> qpat_x_assum ‘evaluate (xs,env,inc_clock ck t) = (Rval a,_)’ assume_tac
      >> drule_then (qspec_then ‘ck'’ assume_tac) evaluate_add_clock
      >> ‘inc_clock ck' (inc_clock ck t) = inc_clock (ck + ck') t’
        by gvs[inc_clock_def, state_component_equality]
      >> gvs[]
     )
     
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
              >> qexists ‘ck’ >> gvs[]
              >> Cases_on ‘res'’ >> gvs[]
             )
          >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
         )
      >> gvs[worker_body_def, evaluate_def]
      >> Cases_on ‘evaluate ([x1],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
         )               
      >> last_x_assum $ drule_then strip_assume_tac
      >> qexists ‘ck’ >> gvs[]
      >> Cases_on ‘res'’ >> gvs[]
     )

  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
              >> qexists ‘ck’ >> gvs[]
              >> Cases_on ‘res'’ >> gvs[]
             )
          >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
         )
      >> gvs[worker_body_def, evaluate_def]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (last_x_assum $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
         )               
      >> last_x_assum $ drule_then strip_assume_tac
      >> qexists ‘ck’ >> gvs[]
      >> Cases_on ‘res'’ >> gvs[]
     )
     
  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (qspecl_then [‘xs’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
              >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
              >> impl_tac >- gvs[]
              >> strip_tac
              >> qexists ‘ck’ >> gvs[]
              >> Cases_on ‘do_app op (REVERSE a) r’ >> gvs[]
              >- (PairCases_on ‘a'’ >> gvs[]
                  >> drule_all_then assume_tac do_app_state_rel_rval >> gvs[state_rel_def]
                 )
              >> drule_all_then assume_tac do_app_state_rel_rerr
              >> gvs[state_rel_def]
             )
          >> qpat_x_assum ‘∀m' t'. state_rel m' s t' ⇒ _’ $ drule_then strip_assume_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res'’ >> gvs[]
          >> Cases_on ‘do_app op (REVERSE a) t1’ >> gvs[]
          >- (PairCases_on ‘a'’ >> gvs[]
              >> irule IS_PREFIX_TRANS
              >> first_assum $ irule_at Any
              >> drule_then irule do_app_io_events_mono
             )
          >> gvs[]
         )
      >> gvs[worker_body_def, evaluate_def]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def]
          >> qspecl_then [‘[Op op xs]’,‘env’,‘s’] mp_tac (cj 1 cpr_correct)
          >> disch_then $ qspecl_then [‘m’,‘t’,‘res’,‘s1’] mp_tac
          >> impl_tac
          >- (gvs[evaluate_def]
              >> Cases_on ‘do_app op (REVERSE a) r’ >> gvs[]
              >> imp_res_tac do_app_no_Ret
              >- (every_case_tac >> gvs[]
                 )
              >> drule_then assume_tac do_app_no_timeout
              >> rw[]
             )
          >> strip_tac
          >> qexists ‘ck’ >> gvs[]
          >> Cases_on ‘res’ >> gvs[]
          >- (assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[Op op xs]’, ‘env’, ‘inc_clock ck t’] assume_tac >> gvs[]
              >> Cases_on ‘a'’ >> gvs[]
              >> drule_all_then assume_tac (cj 1 evaluate_flatten_exp)
              >> gvs[state_rel_def]
             )
          >> drule_then assume_tac (cj 1 evaluate_flatten_exp_err)
          >> pop_assum $ qspecl_then [‘env’,‘inc_clock ck t’] assume_tac
          >> gvs[state_rel_def]
         )
      >> gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def]
      >> last_x_assum $ drule_then strip_assume_tac
      >> Cases_on ‘res'’ >> gvs[]
      >- (Cases_on ‘do_app op (REVERSE a) t1’ >> gvs[]
          >- (drule_then assume_tac $ cj 1 evaluate_flatten_exp
              >> gvs[evaluate_def]
              >> pop_assum $ qspecl_then [‘env’, ‘inc_clock ck t’] assume_tac >> gvs[]
              >> Cases_on ‘a'’ >> gvs[]
              >> qexists ‘ck’ >> gvs[]
              >> drule_then assume_tac do_app_io_events_mono
              >> irule isPREFIX_TRANS
              >> metis_tac[]
             )
          >> drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
          >> gvs[evaluate_def]
          >> pop_assum $ qspecl_then [‘env’, ‘inc_clock ck t’] assume_tac >> gvs[]
          >> qexists ‘ck’ >> gvs[]
         )
      >> drule_then assume_tac $ cj 1 evaluate_flatten_exp_err
      >> gvs[evaluate_def]
      >> pop_assum $ qspecl_then [‘env’, ‘inc_clock ck t’] assume_tac >> gvs[]
      >> qexists ‘ck’ >> gvs[]
     )
     
  >- (rw[evaluate_def]
      >- (qexists ‘1’ >> gvs[]
          >> Cases_on ‘evaluate ([x],env,dec_clock 1 (inc_clock 1 t))’ >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono
          >> gvs[dec_clock_def, inc_clock_def, state_rel_def]
         )
      >- (gvs[worker_body_def, evaluate_def]
          >> qexists ‘1’ >> gvs[]
          >> Cases_on ‘evaluate ([worker_body m f wk sh x],env,dec_clock 1 (inc_clock 1 t))’ >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono
          >> gvs[dec_clock_def, inc_clock_def, state_rel_def]
         )
      >- (‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
          >> last_x_assum $ drule_then strip_assume_tac
          >> gvs[]
          >> qexists ‘ck + 1’
          >> gvs[dec_clock_def, inc_clock_def]
         )
      >> gvs[worker_body_def, evaluate_def, tail_ok_def, tail_form_def]
      >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
      >> first_x_assum $ drule_all_then strip_assume_tac
      >> qexists ‘ck + 1’
      >> gvs[dec_clock_def, inc_clock_def]
     )
        
  >- (rw[evaluate_def]
      >- (Cases_on ‘env❲n❳’ >> gvs[dest_thunk_def]
          >> Cases_on ‘FLOOKUP s.refs n'’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘t'’ >> gvs[]
          >- (Cases_on ‘b’ >> gvs[]
              >> gvs[state_rel_def]
             )
          >> Cases_on ‘b’ >> gvs[]
          >> Cases_on ‘find_code (SOME force_loc) [RefPtr F n'; a] s.code’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘s.clock = 0’ >> gvs[]
          >- (gvs[state_rel_def]
              >> drule_all_then assume_tac code_rel_find_code_SOME_dest
              >> Cases_on ‘lookup force_loc m’ >> gvs[]
              >- (qexists ‘1’ >> gvs[]
                  >> Cases_on ‘evaluate ([r],[RefPtr F n'; a],dec_clock 1 (inc_clock 1 t))’ >> gvs[]
                  >> Cases_on ‘q’ >> gvs[]
                  >- (drule_then assume_tac evaluate_io_events_mono
                      >> gvs[]
                     )
                  >> every_case_tac >> gvs[]
                  >> drule_then assume_tac evaluate_io_events_mono
                  >> gvs[]
                 )
              >> Cases_on ‘x’ >> gvs[]
              >> qexists ‘1’ >> gvs[]
              >> Cases_on ‘evaluate ([make_wrapper 2 r' q],[RefPtr F n'; a], dec_clock 1 (inc_clock 1 t))’ >> gvs[]
              >> every_case_tac >> gvs[]
              >> drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> Cases_on ‘evaluate ([r],q,dec_clock 1 s)’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
          >- (‘s.refs = t.refs ∧ code_rel m s.code t.code’ by gvs[state_rel_def]
              >> gvs[]
              >> drule_all_then assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> Cases_on ‘lookup force_loc m’ >> gvs[]
              >- (‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
                  >> last_x_assum $ drule_all_then strip_assume_tac
                  >> gvs[]
                  >> qexists ‘ck + 1’ >> gvs[inc_clock_def, dec_clock_def]
                  >> every_case_tac >> gvs[]
                 )
              >> Cases_on ‘x’ >> gvs[make_wrapper_def, evaluate_def]
              >> rw[bvlSemTheory.find_code_def]
              >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> qexists ‘ck + 2’ >> gvs[dec_clock_def, inc_clock_def]
              >> every_case_tac >> gvs[]
              >> drule_then assume_tac evaluate_io_events_mono
              >> irule isPREFIX_TRANS
              >> metis_tac[]
             )
          >> Cases_on ‘e’ >> gvs[]
          >- (Cases_on ‘a'’ >> gvs[]
              >> ‘s.refs = t.refs ∧ code_rel m s.code t.code’ by gvs[state_rel_def]
              >> gvs[]
              >> drule_all_then assume_tac code_rel_find_code_SOME_dest
              >> gvs[]
              >> Cases_on ‘lookup force_loc m’ >> gvs[]
              >- (‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
                  >> last_x_assum $ drule_all_then strip_assume_tac
                  >> gvs[]
                  >> qexists ‘ck + 1’ >> gvs[inc_clock_def, dec_clock_def]
                  >> every_case_tac >> gvs[]
                 )
              >> Cases_on ‘x’ >> gvs[make_wrapper_def, evaluate_def]
              >> rw[bvlSemTheory.find_code_def]
              >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
              >> first_x_assum $ drule_all_then assume_tac
              >> gvs[]
              >> qexists ‘ck + 2’ >> gvs[dec_clock_def, inc_clock_def]
              >> every_case_tac >> gvs[]
              >> drule_then assume_tac evaluate_io_events_mono
              >> irule isPREFIX_TRANS
              >> metis_tac[]
             )
          >> ‘s.refs = t.refs ∧ code_rel m s.code t.code’ by gvs[state_rel_def]
          >> gvs[]
          >> drule_all_then assume_tac code_rel_find_code_SOME_dest
          >> gvs[]
          >> Cases_on ‘lookup force_loc m’ >> gvs[]
          >- (‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
              >> last_x_assum $ drule_all_then strip_assume_tac
              >> gvs[]
              >> qexists ‘ck + 1’ >> gvs[inc_clock_def, dec_clock_def]
              >> every_case_tac >> gvs[]
             )
          >> Cases_on ‘x’ >> gvs[make_wrapper_def, evaluate_def]
          >> rw[bvlSemTheory.find_code_def]
          >> ‘state_rel m (dec_clock 1 s) t’ by gvs[state_rel_clock, dec_clock_def]
          >> first_x_assum $ drule_all_then assume_tac
          >> gvs[]
          >> qexists ‘ck + 2’ >> gvs[dec_clock_def, inc_clock_def]
          >> every_case_tac >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono
          >> irule isPREFIX_TRANS
          >> metis_tac[]
       )
      >> Cases_on ‘env❲n❳’ >> gvs[dest_thunk_def]
      >> Cases_on ‘FLOOKUP s.refs n'’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘t'’ >> gvs[]
      >- (Cases_on ‘b’ >> gvs[]
          >> gvs[state_rel_def, worker_body_def, evaluate_def]
          >> qexists ‘0’ >> gvs[]
          >> Cases_on ‘evaluate (flatten_exp sh (Force force_loc n),env,inc_clock 0 t)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono >> gvs[]
         )
      >> Cases_on ‘b’ >> gvs[]
      >> Cases_on ‘find_code (SOME force_loc) [RefPtr F n'; a] s.code’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘s.clock = 0’ >> gvs[]
      >- (gvs[state_rel_def, worker_body_def, evaluate_def]
          >> drule_all_then assume_tac code_rel_find_code_SOME_dest >> gvs[]
          >> Cases_on ‘lookup force_loc m’ >> gvs[]
          >- (qexists ‘1’ >> gvs[]
              >> Cases_on ‘evaluate (flatten_exp sh (Force force_loc n),env,inc_clock 1 t)’ >> gvs[]
              >> Cases_on ‘q’ >> gvs[]
              >- (drule_then assume_tac evaluate_io_events_mono
                  >> gvs[]
                 )
              >> drule_then assume_tac evaluate_io_events_mono
              >> gvs[]
             )
          >> Cases_on ‘x’ >> gvs[]
          >> qexists ‘1’ >> gvs[]
          >> Cases_on ‘evaluate (flatten_exp sh (Force force_loc n),env,inc_clock 1 t)’ >> gvs[]
          >> every_case_tac >> gvs[]
          >> drule_then assume_tac evaluate_io_events_mono
          >> gvs[]
         )
      >> Cases_on ‘evaluate ([r],q,dec_clock 1 s)’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >> drule_then strip_assume_tac split_ok_ConsShape
      >> gvs[tail_ok_def, exp_shape_ok_def]
     )

  >- (rw[evaluate_def]
      >- (Cases_on ‘evaluate (xs,env,s1)’ >> gvs[]
          >> Cases_on ‘q’ >> gvs[]
          >- (qspecl_then [‘xs’,‘env’,‘s1’] mp_tac (cj 1 cpr_correct)
              >> disch_then $ qspecl_then [‘m’,‘t’,‘Rval a’,‘r’] mp_tac
              >> impl_tac
              >- gvs[]
              >> strip_tac
              >> Cases_on ‘find_code dest a r.code’ >> gvs[]
              >> Cases_on ‘x’ >> gvs[]
              >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
              >- (cheat
                 )
              >> cheat
             )
          >> cheat
         )
      >> cheat
     )
        
  >> cheat
QED


Theorem compile_prog_semantics:
  ∀start prog next n prog2 ffi co cc.
    compile_prog next prog = (n,prog2) ∧
    map_inv LN next ∧ prog_keys_ok next prog ∧
    (∀k. SND (co k) = []) ∧
    semantics ffi (fromAList prog) co cc start ≠ Fail ⇒
    semantics ffi (fromAList prog2) co cc start =
    semantics ffi (fromAList prog) co cc start
Proof
  rpt strip_tac
  >> qspecl_then [‘next’,‘prog’,‘n’,‘prog2’,‘ffi’,‘co’,‘cc’] mp_tac
       compile_prog_init_state_rel
  >> impl_tac >- gvs[] >> strip_tac
  >> qabbrev_tac ‘es = [bvi$Call 0 (SOME start) [] NONE]’
  >> qabbrev_tac ‘init1 = initial_state ffi (fromAList prog)  co cc’
  >> qabbrev_tac ‘init2 = initial_state ffi (fromAList prog2) co cc’
  >> ‘∀j k. inc_clock j (init2 k) = init2 (k + j)’ by
       gvs[Abbr‘init2’, inc_clock_def, initial_state_def,
           state_component_equality]
  >> ‘∀k. (init1 k).clock = k ∧ (init2 k).clock = k’ by
       gvs[Abbr‘init1’, Abbr‘init2’, initial_state_def]
  >> qpat_x_assum ‘semantics _ (fromAList prog) _ _ _ ≠ Fail’ mp_tac
  >> simp[semantics_def] >> IF_CASES_TAC >- simp[]
  >> strip_tac >> gvs[]
  >> subgoal ‘∀k. FST (evaluate (es,[],init1 k)) ≠ Rerr (Rabort Rtype_error)’
  >- (strip_tac
      >> first_x_assum $ qspec_then ‘k’ assume_tac >> gvs[]
      >> Cases_on ‘FST (evaluate (es,[],init1 k))’ >> gvs[]
     )
  >> subgoal ‘∀k. FST (evaluate (es,[],init2 k)) ≠ Rerr (Rabort Rtype_error)’
  >- (rpt strip_tac
      >> Cases_on ‘evaluate (es,[],init1 k)’
      >> qpat_x_assum ‘∀k. FST (evaluate (es,[],init1 k)) ≠ _’ $ qspec_then ‘k’ assume_tac
      >> qpat_x_assum ‘∀k. state_rel _ (init1 _) (init2 _)’ $ qspec_then ‘k’ assume_tac
      >> gvs[]
      >> drule_at Any (cj 1 cpr_lag)
      >> disch_then $ qspecl_then [‘es’,‘[]’] mp_tac >> gvs[]
      >> rpt strip_tac >> gvs[]
     )
  >> subgoal ‘∀k. ∃ck.
       (FST (evaluate (es,[],init1 k)) ≠ Rerr (Rabort Rtimeout_error) ⇒
          FST (evaluate (es,[],init2 (k + ck))) =
          FST (evaluate (es,[],init1 k)) ∧
          (SND (evaluate (es,[],init2 (k + ck)))).ffi =
          (SND (evaluate (es,[],init1 k))).ffi) ∧
       (SND (evaluate (es,[],init1 k))).ffi.io_events ≼
       (SND (evaluate (es,[],init2 (k + ck)))).ffi.io_events’
  >- (strip_tac
      >> Cases_on ‘evaluate (es,[],init1 k)’
      >> qpat_x_assum ‘∀k. state_rel _ (init1 _) (init2 _)’
                      $ qspec_then ‘k’ assume_tac
      >> Cases_on ‘q = Rerr (Rabort Rtimeout_error)’
      >- (drule_at Any (cj 1 cpr_timeout)
          >> disch_then $ qspecl_then [‘es’,‘[]’] mp_tac
          >> rpt strip_tac
          >> gvs[]
          >> qexists ‘ck’ >> gvs[]
         )
      >> gvs[]
      >> drule_at Any (cj 1 $ INST_TYPE [alpha |-> beta, beta |-> alpha] cpr_correct)
      >> disch_then $ qspecl_then [‘es’,‘[]’, ‘init1 k’, ‘m’, ‘init2 k’] mp_tac
      >> strip_tac >> gvs[]
      >> qsuff_tac ‘q ≠ Rerr (Rabort Rtype_error)’
      >- (rpt strip_tac
          >> gvs[]
          >> qexists ‘ck’ >> gvs[state_rel_def]
         )
      >> ‘FST (evaluate (es,[],init1 k)) ≠ Rerr (Rabort Rtype_error)’ by rw[]
      >> Cases_on ‘evaluate (es,[],init1 k)’ >> gvs[]
     )
  >> subgoal ‘∀k. (SND (evaluate (es,[],init2 k))).ffi.io_events ≼
                                                  (SND (evaluate (es,[],init1 k))).ffi.io_events’
  >- (strip_tac
      >> Cases_on ‘evaluate (es,[],init1 k)’
      >> qpat_x_assum ‘∀k. state_rel _ (init1 _) (init2 _)’
                      $ qspec_then ‘k’ assume_tac
      >> Cases_on ‘q = Rerr (Rabort Rtimeout_error)’
      >- (gvs[] >> drule_at Any cpr_lag_timeout
          >> disch_then $ qspecl_then [‘es’,‘[]’] mp_tac
          >> rpt strip_tac >> gvs[]
         )
      >> first_x_assum $ qspec_then ‘k’ strip_assume_tac
      >> gvs[]
      >> qspecl_then [‘es’,‘[]’,‘init2 k’,‘ck’] mp_tac
                     evaluate_add_to_clock_io_events_mono
      >> gvs[]
     )
  >> cheat
QED

