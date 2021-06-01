(*
  Encoding from boolExp to cnf using Tseytin transformation
*)

open preamble miscTheory ASCIInumbersTheory;
open boolExpToCnfTheory quantifierExpTheory orderEncodingBoolTheory;
open numBoolExpTheory numBoolExtendedTheory numBoolRangeTheory;
open unorderedSetsTheory;

val _ = new_theory "tseytin";

(* --------------------------- Datatypes -------------------------------- *)

Datatype:
  constFree =
  | CLit literal
  | CNot constFree
  | CAnd constFree constFree
  | COr constFree constFree
  | CImpl constFree constFree
  | CIff constFree constFree
End

Datatype:
  rhs =
  | RNot literal
  | RAnd literal literal
  | ROr literal literal
  | RImpl literal literal
  | RIff literal literal
End

(* --------------------------- Well-formed -------------------------------- *)

Definition bigger_than_literal_def:
  bigger_than_literal (n:num) (INL x) = (n > x) ∧
  bigger_than_literal n (INR y) = (n > y)
End

Definition num_bigger_than_rhs_def:
  num_bigger_than_rhs (q:num) (RNot l) = bigger_than_literal q l ∧
  num_bigger_than_rhs q (RAnd l1 l2) =
  (bigger_than_literal q l1 ∧ bigger_than_literal q l2) ∧
  num_bigger_than_rhs q (ROr l1 l2) =
  (bigger_than_literal q l1 ∧ bigger_than_literal q l2) ∧
  num_bigger_than_rhs q (RImpl l1 l2) =
  (bigger_than_literal q l1 ∧ bigger_than_literal q l2) ∧
  num_bigger_than_rhs q (RIff l1 l2) =
  (bigger_than_literal q l1 ∧ bigger_than_literal q l2)
End

Definition mapping_ok_def:
  (mapping_ok [] ⇔ T) ∧
  (mapping_ok ((q, r)::xs) ⇔
     (¬ MEM q (MAP FST xs) ∧ EVERY (λ q'. q > q') (MAP FST xs)) ∧
     (num_bigger_than_rhs q r) ∧ mapping_ok xs)
End

Definition constFree_mapping_ok_def:
  constFree_mapping_ok mapping (CLit (INL x)) =
  ¬ MEM x (MAP FST mapping) ∧
  constFree_mapping_ok mapping (CLit (INR x)) =
  ¬ MEM x (MAP FST mapping) ∧
  constFree_mapping_ok mapping (CNot b) =
  constFree_mapping_ok mapping b ∧
  constFree_mapping_ok mapping (CAnd b1 b2) =
  (constFree_mapping_ok mapping b1 ∧ constFree_mapping_ok mapping b2) ∧
  constFree_mapping_ok mapping (COr b1 b2) =
  (constFree_mapping_ok mapping b1 ∧ constFree_mapping_ok mapping b2) ∧
  constFree_mapping_ok mapping (CIff b1 b2) =
  (constFree_mapping_ok mapping b1 ∧ constFree_mapping_ok mapping b2) ∧
  constFree_mapping_ok mapping (CImpl b1 b2) =
  (constFree_mapping_ok mapping b1 ∧ constFree_mapping_ok mapping b2)
End

(* --------------------------- Evaluation -------------------------------- *)

Definition eval_constFree_def:
  eval_constFree (w:assignment) (CLit l) = eval_literal w l ∧
  eval_constFree w (CNot b) = ¬ eval_constFree w b ∧
  eval_constFree w (CAnd b1 b2) =
  (eval_constFree w b1 ∧ eval_constFree w b2) ∧
  eval_constFree w (COr b1 b2) =
  (eval_constFree w b1 ∨ eval_constFree w b2) ∧
  eval_constFree w (CImpl b1 b2) =
  (eval_constFree w b1 ⇒ eval_constFree w b2) ∧
  eval_constFree w (CIff b1 b2) =
  (eval_constFree w b1 ⇔ eval_constFree w b2)
End


(* --------------------------- Encoding -------------------------------- *)

Definition boolExp_to_constFree_def:
  boolExp_to_constFree True = INR T ∧
  boolExp_to_constFree False = INR F ∧
  boolExp_to_constFree (Lit l) = INL (CLit l) ∧
  boolExp_to_constFree (Not b) =
  (case boolExp_to_constFree b of
   | INL b' => INL (CNot b')
   | INR bv => INR (¬ bv)) ∧
  boolExp_to_constFree (And b1 b2) =
  (case (boolExp_to_constFree b1, boolExp_to_constFree b2) of
   | (INL b1', INL b2') => INL (CAnd b1' b2')
   | (INR F, _) => INR F
   | (_, INR F) => INR F
   | (b1', INR T) => b1'
   | (INR T, b2') => b2') ∧
  boolExp_to_constFree (Or b1 b2) =
  (case (boolExp_to_constFree b1, boolExp_to_constFree b2) of
   | (INL b1', INL b2') => INL (COr b1' b2')
   | (INR T, _) => INR T
   | (_, INR T) => INR T
   | (b1', INR F) => b1'
   | (INR F, b2') => b2') ∧
  boolExp_to_constFree (Impl b1 b2) =
  (case (boolExp_to_constFree b1, boolExp_to_constFree b2) of
   | (INL b1', INL b2') => INL (CImpl b1' b2')
   | (INR F, _) => INR T
   | (_, INR T) => INR T
   | (INR T, b2') => b2'
   | (INL b1', INR F) => INL (CNot b1')) ∧
  boolExp_to_constFree (Iff b1 b2) =
  (case (boolExp_to_constFree b1, boolExp_to_constFree b2) of
   | (INL b1', INL b2') => INL (CIff b1' b2')
   | (INR T, b2') => b2'
   | (b1', INR T) => b1'
   | (INR F, INR F) => INR T
   | (INR F, INL b2') => INL (CNot b2')
   | (INL b1', INR F) => INL (CNot b1'))
End

Definition bind_def:
  bind (next:num) b map =
  (next + 1, INL next, Append (List [(next, b)]) map)
End

Definition constFree_to_cnf_inner_def:
  constFree_to_cnf_inner next (CLit l) =
  (next, l, Nil) ∧
  constFree_to_cnf_inner next (CNot b) =
  (let (next', l, map) = constFree_to_cnf_inner next b in
     bind next' (RNot l) map) ∧
  constFree_to_cnf_inner next (CAnd b1 b2) =
  (let (next', l1, map1) = constFree_to_cnf_inner next b1 in
     let (next'', l2, map2) = constFree_to_cnf_inner next' b2 in
       bind next'' (RAnd l1 l2) (Append map2 map1)) ∧
  constFree_to_cnf_inner next (COr b1 b2) =
  (let (next', l1, map1) = constFree_to_cnf_inner next b1 in
     let (next'', l2, map2) = constFree_to_cnf_inner next' b2 in
       bind next'' (ROr l1 l2) (Append map2 map1)) ∧
  constFree_to_cnf_inner next (CImpl b1 b2) =
  (let (next', l1, map1) = constFree_to_cnf_inner next b1 in
     let (next'', l2, map2) = constFree_to_cnf_inner next' b2 in
       bind next'' (RImpl l1 l2) (Append map2 map1)) ∧
  constFree_to_cnf_inner next (CIff b1 b2) =
  (let (next', l1, map1) = constFree_to_cnf_inner next b1 in
     let (next'', l2, map2) = constFree_to_cnf_inner next' b2 in
       bind next'' (RIff l1 l2) (Append map2 map1))
End

(* l1 ⇔ ¬ l2
   (l1 ⇒ ¬ l2) ∧ (¬ l2 ⇒ l1)
   (¬ l1 ∨ ¬ l2) ∧ (l2 ∨ l1) *)
Definition replace_not_def:
  replace_not l1 l2 =
  CnfAnd
  (CnfClause
   (ClauseOr
    (ClauseLit (negate_literal l1))
    (ClauseLit (negate_literal l2))))
  (CnfClause (ClauseOr (ClauseLit l2) (ClauseLit l1)))
End

(* l1 ⇔ (l2 ∧ l3)
 (l1 ⇒ (l2 ∧ l3)) ∧ ((l2 ∧ l3) ⇒ l1)
 (¬l1 ∨ (l2 ∧ l3)) ∧ (¬(l2 ∧ l3) ∨ l1)
 (¬l1 ∨ l2) ∧ (¬l1 ∨ l3) ∧ (¬l2 ∨ ¬l3 ∨ l1)
 *)
Definition replace_and_def:
  replace_and l1 l2 l3 =
  CnfAnd
  (CnfClause (ClauseOr (ClauseLit (negate_literal l1)) (ClauseLit l2)))
  (CnfAnd
   (CnfClause (ClauseOr (ClauseLit (negate_literal l1)) (ClauseLit l3)))
   (CnfClause (ClauseOr
               (ClauseLit (negate_literal l2))
               (ClauseOr (ClauseLit (negate_literal l3)) (ClauseLit l1)))))
End


(* l1 ⇔ (l2 ∨ l3)
 (l1 ⇒ (l2 ∨ l3)) ∧ ((l2 ∨ l3) ⇒ l1)
 (¬l1 ∨ (l2 ∨ l3)) ∧ (¬(l2 ∨ l3) ∨ l1)
 (¬l1 ∨ l2 ∨ l3) ∧ ((¬l2 ∧ ¬ l3) ∨ l1)
 (¬l1 ∨ l2 ∨ l3) ∧ (¬l2 ∨ l1) ∧ (¬l3 ∨ l1))
*)
Definition replace_or_def:
  replace_or l1 l2 l3 =
  CnfAnd
  (CnfClause (ClauseOr
              (ClauseLit (negate_literal l1))
              (ClauseOr (ClauseLit l2) (ClauseLit l3))))
  (CnfAnd
   (CnfClause (ClauseOr (ClauseLit (negate_literal l2)) (ClauseLit l1)))
   (CnfClause (ClauseOr (ClauseLit (negate_literal l3)) (ClauseLit l1))))
End

(* l1 ⇔ (l2 ⇒ l3)
 (l1 ⇒ (l2 ⇒ l3)) ∧ ((l2 ⇒ l3) ⇒ l1)
 (¬l1 ∨ (l2 ⇒ l3)) ∧ (¬(l2 ⇒ l3) ∨ l1)
 (¬l1 ∨ (¬l2 ∨ l3)) ∧ (¬(¬l2 ∨ l3) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (l2 ∧ ¬l3) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (l2 ∨ l1) ∧ (¬l3 ∨ l1)
*)
Definition replace_impl_def:
  replace_impl l1 l2 l3 =
  CnfAnd
  (CnfClause (ClauseOr
              (ClauseLit (negate_literal l1))
              (ClauseOr (ClauseLit (negate_literal l2)) (ClauseLit l3))))
  (CnfAnd
   (CnfClause (ClauseOr (ClauseLit l2) (ClauseLit l1)))
   (CnfClause (ClauseOr (ClauseLit (negate_literal l3)) (ClauseLit l1))))
End

(* l1 ⇔ (l2 ⇔ l3)
 (l1 ⇒ (l2 ⇔ l3)) ∧ ((l2 ⇔ l3) ⇒ l1)
 (¬l1 ∨ (l2 ⇔ l3)) ∧ (¬(l2 ⇔ l3) ∨ l1)
 (¬l1 ∨ ((l2 ⇒ l3) ∧ (l3 ⇒ l2))) ∧ (¬((l2 ⇒ l3) ∧ (l3 ⇒ l2)) ∨ l1)
 (¬l1 ∨ ((¬l2 ∨ l3) ∧ (¬l3 ∨ l2))) ∧ ((¬(¬l2 ∨ l3) ∨ ¬(¬l3 ∨ l2)) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (¬l1 ∨ ¬l3 ∨ l2) ∧ (((l2 ∧ ¬l3) ∨ (l3 ∧ ¬l2)) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (¬l1 ∨ ¬l3 ∨ l2) ∧ (((l2 ∧ ¬l3) ∨ l3) ∧ ((l2 ∧ ¬l3) ∨ ¬l2)) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (¬l1 ∨ ¬l3 ∨ l2) ∧ (((l2 ∨ l3) ∧ T ∧ T ∧ (¬l3 ∨ ¬l2)) ∨ l1)
 (¬l1 ∨ ¬l2 ∨ l3) ∧ (¬l1 ∨ ¬l3 ∨ l2) ∧ (l2 ∨ l3 ∨ l1) ∧ (¬l3 ∨ ¬l2 ∨ l1)
*)
Definition replace_iff_def:
  replace_iff l1 l2 l3 =
  CnfAnd
  (CnfClause (ClauseOr
              (ClauseLit (negate_literal l1))
              (ClauseOr
               (ClauseLit (negate_literal l2)) (ClauseLit l3))))
  (CnfAnd
   (CnfClause (ClauseOr
               (ClauseLit (negate_literal l1))
               (ClauseOr
                (ClauseLit (negate_literal l3)) (ClauseLit l2))))
   (CnfAnd
    (CnfClause (ClauseOr
                (ClauseLit l2)
                (ClauseOr
                 (ClauseLit l3) (ClauseLit l1))))
    (CnfClause (ClauseOr
                (ClauseLit (negate_literal l3))
                (ClauseOr
                 (ClauseLit (negate_literal l2)) (ClauseLit l1))))))
End

Definition rhs_to_cnf_def:
  rhs_to_cnf x (RNot l) = replace_not (INL x) l ∧
  rhs_to_cnf x (RAnd l1 l2) = replace_and (INL x) l1 l2 ∧
  rhs_to_cnf x (ROr l1 l2) = replace_or (INL x) l1 l2 ∧
  rhs_to_cnf x (RImpl l1 l2) = replace_impl (INL x) l1 l2 ∧
  rhs_to_cnf x (RIff l1 l2) = replace_iff (INL x) l1 l2
End

Definition map_to_cnf_def:
  map_to_cnf [] = CnfEmpty ∧
  map_to_cnf ((x, rhs)::map) =
  CnfAnd (rhs_to_cnf x rhs) (map_to_cnf map)
End

Definition get_fresh_name_constFree_def:
  get_fresh_name_constFree (CLit (INL x)) = x + 1 ∧
  get_fresh_name_constFree (CLit (INR x)) = x + 1 ∧
  get_fresh_name_constFree (CNot b) = get_fresh_name_constFree b ∧
  get_fresh_name_constFree (CAnd b1 b2) =
  MAX (get_fresh_name_constFree b1) (get_fresh_name_constFree b2) ∧
  get_fresh_name_constFree (COr b1 b2) =
  MAX (get_fresh_name_constFree b1) (get_fresh_name_constFree b2) ∧
  get_fresh_name_constFree (CImpl b1 b2) =
  MAX (get_fresh_name_constFree b1) (get_fresh_name_constFree b2) ∧
  get_fresh_name_constFree (CIff b1 b2) =
  MAX (get_fresh_name_constFree b1) (get_fresh_name_constFree b2)
End


(* ------------------- Encodings to cnf --------------------- *)

Definition constFree_to_cnf_def:
  constFree_to_cnf b =
  let next = get_fresh_name_constFree b in
    let (next', l, map) = constFree_to_cnf_inner next b in
      CnfAnd (CnfClause (ClauseLit l)) (map_to_cnf (append map))
End

Definition t_boolExp_to_cnf_def:
  t_boolExp_to_cnf b =
  case boolExp_to_constFree b of
  | INL b' => constFree_to_cnf b'
  | INR T => CnfEmpty
  | INR F => CnfClause ClauseEmpty
End

Definition t_pseudoBool_to_cnf_def:
  t_pseudoBool_to_cnf b =
  t_boolExp_to_cnf (quant_to_boolExp (pseudoBool_to_quant b))
End

Definition t_orderBool_to_cnf_def:
  t_orderBool_to_cnf exp = t_pseudoBool_to_cnf (orderBool_to_pseudoBool exp)
End

Definition t_numBool_to_cnf_def:
  t_numBool_to_cnf l exp = t_orderBool_to_cnf (numBool_to_orderBool l exp)
End

Definition t_numBoolExtended_to_cnf_def:
  t_numBoolExtended_to_cnf l e =
  let e' = numBoolExtended_to_numBoolExp e in
    t_numBool_to_cnf l e'
End

Definition t_numBoolRange_to_cnf_def:
  t_numBoolRange_to_cnf (l:rangeList) e =
  t_numBoolExtended_to_cnf
  (rangeList_to_numVarList l)
  (numBoolRange_to_numBoolExtended l e)
End

Definition t_equation_to_cnf_def:
  t_equation_to_cnf (l:setList) e =
  t_numBoolRange_to_cnf
  (equation_to_rangeList e l)
  (equation_to_numBoolRange l e)
End


(* -------------------- Encoding the assignment ---------------------- *)

Definition eval_rhs_def:
  eval_rhs w (RNot l) = ¬ eval_literal w l ∧
  eval_rhs w (RAnd l1 l2) =
  (eval_literal w l1 ∧ eval_literal w l2) ∧
  eval_rhs w (ROr l1 l2) =
  (eval_literal w l1 ∨ eval_literal w l2) ∧
  eval_rhs w (RImpl l1 l2) =
  (eval_literal w l1 ⇒ eval_literal w l2) ∧
  eval_rhs w (RIff l1 l2) =
  (eval_literal w l1 ⇔ eval_literal w l2)
End

Definition make_assignments_def:
  make_assignments w [] = w ∧
  make_assignments w ((n, rhs)::mapping) =
  let w' = make_assignments w mapping in
    ((n =+ eval_rhs w' rhs)w')
End

Definition constFree_to_assignment_def:
  constFree_to_assignment w b =
  let (next,l,map) = constFree_to_cnf_inner (get_fresh_name_constFree b) b in
    make_assignments w (append map)
End

Definition t_boolExp_to_assignment_def:
  t_boolExp_to_assignment w b =
  case boolExp_to_constFree b of
  | INL b' => constFree_to_assignment w b'
  | INR _ => w
End

Definition t_pseudoBool_to_assignment_def:
  t_pseudoBool_to_assignment w b =
  t_boolExp_to_assignment w (quant_to_boolExp (pseudoBool_to_quant b))
End

Definition t_orderBool_to_assignment_def:
  t_orderBool_to_assignment w b =
  t_pseudoBool_to_assignment w (orderBool_to_pseudoBool b)
End

Definition t_numBoolExp_to_assignment_def:
  t_numBoolExp_to_assignment
  (w:assignment) (w':numVarAssignment) (vList:numVarList) (e:numBoolExp) =
  t_orderBool_to_assignment
  (minimal_encode_assignment w w' vList e)
  (numBool_to_orderBool vList e)
End

Definition t_numBoolExtended_to_assignment_def:
  t_numBoolExtended_to_assignment w w' l e =
  t_numBoolExp_to_assignment w w' l (numBoolExtended_to_numBoolExp e)
End

Definition t_numBoolRange_to_assignment_def:
  t_numBoolRange_to_assignment w w' l e =
  t_numBoolExtended_to_assignment
  w w' (rangeList_to_numVarList l) (numBoolRange_to_numBoolExtended l e)
End


(* -------------------------------- Theorems ---------------------------- *)


Theorem next_bigger_lemma:
  ∀b next next' x map1.
  constFree_to_cnf_inner next b = (next', x, map1) ⇒
  next ≤ next'
Proof
  Induct >> rw[]
  >- gs[constFree_to_cnf_inner_def]
  >- (gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> gs[bind_def]
      >> last_x_assum
         (qspecl_then [‘next’, ‘next''’, ‘l’, ‘map'’] assume_tac) >> gs[])
  >> (gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> last_x_assum
         (qspecl_then [‘next’, ‘next''’, ‘l1’, ‘map1'’] assume_tac) >> gs[]
      >> last_x_assum
         (qspecl_then [‘next''’, ‘next'''’, ‘l2’, ‘map2’] assume_tac) >> gs[])
QED

Definition next_range_def:
  next_range n1 n2 = {(k:num) | n1 ≤ k ∧ k < n2}
End

Theorem make_assignment_not_mem:
  ∀ xs ys next w.
    ¬MEM next (MAP FST xs) ⇒
    make_assignments w (xs ++ ys) next = make_assignments w ys next
Proof
  Induct >> rw[]
  >> Cases_on ‘h’ >> gs[]
  >> gs[make_assignments_def, APPLY_UPDATE_THM]
QED

Theorem make_assignment_not_mem_2:
  ∀ xs next w.
    ¬MEM next (MAP FST xs) ⇒
    make_assignments w xs next = w next
Proof
  Induct >> rw[]
  >- rw[make_assignments_def]
  >> Cases_on ‘h’ >> gs[]
  >> gs[make_assignments_def, APPLY_UPDATE_THM]
QED

Theorem mapping_range:
  ∀ map1 next next' b l.
    constFree_to_cnf_inner next b = (next',l,map1) ⇒
    EVERY (λ x. x ∈ (next_range next next')) (MAP FST (append map1))
Proof
  Induct_on ‘b’ >> rw[]
  >- gs[constFree_to_cnf_inner_def]
  >- (gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> rw[]
      >- (rw[next_range_def]
          >> metis_tac[next_bigger_lemma])
      >> last_x_assum
         (qspecl_then [‘map'’, ‘next’, ‘next''’, ‘l'’] assume_tac) >> gs[]
      >> gs[next_range_def]
      >> gs[EVERY_MEM]
      >> rw[]
      >> last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
  >> (gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> rw[]
      >- (gs[next_range_def]
          >> imp_res_tac next_bigger_lemma
          >> gs[])
      >- (gs[next_range_def]
          >> last_x_assum imp_res_tac
          >> last_x_assum imp_res_tac
          >> gs[EVERY_MEM]
          >> rw[]
          >- (first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
              >> imp_res_tac next_bigger_lemma
              >> gs[])
          >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
      >> gs[next_range_def]
      >> last_x_assum imp_res_tac
      >> last_x_assum imp_res_tac
      >> gs[EVERY_MEM]
      >> rw[]
      >> last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
      >> imp_res_tac next_bigger_lemma
      >> gs[])
QED

Theorem literal_smaller_than_next:
  ∀ b next next' l map'.
    constFree_to_cnf_inner next b = (next',l,map') ∧
    get_fresh_name_constFree b ≤ next ⇒
    bigger_than_literal next' l
Proof
  Induct >> rw[]
  >- (gs[constFree_to_cnf_inner_def]
      >> Cases_on ‘l’ >> gs[]
      >> gs[bigger_than_literal_def, get_fresh_name_constFree_def])
  >- (gs[constFree_to_cnf_inner_def, get_fresh_name_constFree_def]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def, bigger_than_literal_def])
  >> (gs[constFree_to_cnf_inner_def, get_fresh_name_constFree_def]
      >> pairarg_tac >> gs[]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def, bigger_than_literal_def])
QED

(* ------------------- Theorems about mapping_created_ok ------------------ *)

Theorem mapping_ok_append:
  ∀ mapping2 mapping1 next next' next''.
    mapping_ok mapping1 ∧
    mapping_ok mapping2 ∧
    EVERY (λx. x ∈ next_range next next') (MAP FST mapping1) ∧
    EVERY (λx. x ∈ next_range next' next'') (MAP FST mapping2) ∧
    next ≤ next' ∧
    next' ≤ next'' ⇒
    mapping_ok (mapping2 ++ mapping1)
Proof
  Induct >> rw[]
  >> Cases_on ‘h’ >> gs[]
  >> gs[mapping_ok_def]
  >> rw[]
  >- (gs[next_range_def]
      >> gs[EVERY_MEM]
      >> qpat_x_assum ‘∀x. MEM x (MAP FST mapping1) ⇒ next ≤ x ∧ x < next'’
                      (qspecl_then [‘q’] assume_tac) >> gs[])
  >- (gs[next_range_def]
      >> gs[EVERY_MEM]
      >> rw[]
      >> qpat_x_assum ‘∀x. MEM x (MAP FST mapping1) ⇒ next ≤ x ∧ x < next'’
                      (qspecl_then [‘q'’] assume_tac) >> gs[])
  >> last_x_assum irule >> rw[]
  >> metis_tac[]
QED

Theorem mapping_created_ok:
  ∀ b map' next next' l.
    get_fresh_name_constFree b ≤ next ∧
    constFree_to_cnf_inner next b = (next',l,map') ⇒
    mapping_ok (append map')
Proof
  Induct >> rw[]
  >- (Cases_on ‘s’ >> gs[]
      >> gs[get_fresh_name_constFree_def, constFree_to_cnf_inner_def,
            mapping_ok_def])
  >- (gs[get_fresh_name_constFree_def]
      >> gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> rw[mapping_ok_def]
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> first_x_assum (qspecl_then [‘next''’] assume_tac) >> gs[])
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> rw[]
          >> last_x_assum (qspecl_then [‘q'’] assume_tac) >> gs[])
      >- (rw[num_bigger_than_rhs_def]
          >> irule literal_smaller_than_next
          >> qexists_tac ‘b’
          >> qexists_tac ‘map''’
          >> qexists_tac ‘next’
          >> gs[])
      >> metis_tac[])
  >> (gs[get_fresh_name_constFree_def]
      >> gs[constFree_to_cnf_inner_def]
      >> pairarg_tac >> gs[]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> rw[mapping_ok_def]
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> last_x_assum (qspecl_then [‘next'''’] assume_tac) >> gs[])
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> first_x_assum (qspecl_then [‘next'''’] assume_tac) >> gs[]
          >> imp_res_tac next_bigger_lemma >> gs[])
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> rw[]
          >> last_x_assum (qspecl_then [‘q'’] assume_tac) >> gs[])
      >- (imp_res_tac mapping_range
          >> gs[EVERY_MEM, next_range_def]
          >> rw[]
          >> first_x_assum (qspecl_then [‘q'’] assume_tac) >> gs[]
          >> imp_res_tac next_bigger_lemma
          >> gs[])
      >- (rw[num_bigger_than_rhs_def]
          >- (imp_res_tac literal_smaller_than_next
              >> gs[]
              >> imp_res_tac next_bigger_lemma
              >> Cases_on ‘l1’ >> gs[bigger_than_literal_def])
          >> imp_res_tac literal_smaller_than_next
          >> gs[]
          >> imp_res_tac next_bigger_lemma
          >> gs[])
      >> last_x_assum imp_res_tac
      >> imp_res_tac next_bigger_lemma
      >> last_x_assum
         (qspecl_then [‘map2’, ‘next''’, ‘next'''’, ‘l2’] assume_tac) >> gs[]
      >> imp_res_tac mapping_range
      >> metis_tac[mapping_ok_append])
QED

(* -------------- Theorems about mappings_always_true ------------ *)

Theorem one_mapping_true:
  ∀ r q mapping w.
    mapping_ok mapping ∧
    num_bigger_than_rhs q r ∧
    EVERY (λq'. q > q') (MAP FST mapping) ∧
    ¬MEM q (MAP FST mapping) ⇒
    eval_cnf (make_assignments w ((q,r)::mapping)) (rhs_to_cnf q r)
Proof
  Induct >> rw[]
  >- (rw[rhs_to_cnf_def]
      >> rw[replace_not_def]
      >> rw[make_assignments_def]
      >> rw[eval_rhs_def]
      >> rw[eval_cnf_def]
      >> (rw[eval_clause_def]
          >> Cases_on ‘s’ >> rw[]
          >> (rw[negate_literal_def]
              >> rw[eval_literal_def]
              >> rewrite_tac[APPLY_UPDATE_THM]
              >> gs[num_bigger_than_rhs_def]
              >> gs[bigger_than_literal_def])))
  >> (rw[rhs_to_cnf_def]
      >> rw[replace_and_def, replace_or_def,
            replace_impl_def, replace_iff_def]
      >> rw[eval_cnf_def]
      >> (rw[eval_clause_def]
          >> rw[make_assignments_def]
          >> rw[eval_rhs_def]
          >> Cases_on ‘s’ >> rw[]
          >> (Cases_on ‘s0’ >> rw[]
              >> (rw[negate_literal_def]
                  >> rw[eval_literal_def]
                  >> rewrite_tac[APPLY_UPDATE_THM]
                  >> gs[num_bigger_than_rhs_def]
                  >> gs[bigger_than_literal_def]
                  >> metis_tac[]))))
QED

Theorem eval_same:
  ∀ r' q q' r v w.
    num_bigger_than_rhs q' r' ∧
    num_bigger_than_rhs q r ∧
    q > q' ⇒
    (eval_cnf w⦇q ↦ v⦈ (rhs_to_cnf q' r') ⇔
       eval_cnf w (rhs_to_cnf q' r'))
Proof
  Induct >> rw[]
  >- (rw[rhs_to_cnf_def]
      >> gs[num_bigger_than_rhs_def]
      >> Cases_on ‘s’ >> gs[]
      >> (gs[bigger_than_literal_def]
          >> rw[replace_not_def]
          >> rw[eval_cnf_def, eval_clause_def, negate_literal_def,
                eval_literal_def, APPLY_UPDATE_THM]))
  >> (rw[rhs_to_cnf_def]
      >> gs[num_bigger_than_rhs_def]
      >> Cases_on ‘s’ >> gs[]
      >> (Cases_on ‘s0’ >> gs[]
          >> (gs[bigger_than_literal_def]
              >> rw[replace_and_def, replace_or_def,
                    replace_impl_def, replace_iff_def]
              >> rw[eval_cnf_def, eval_clause_def, negate_literal_def,
                    eval_literal_def, APPLY_UPDATE_THM])))
QED

Theorem mapping_always_true_inductive_step:
  ∀ mapping q v w.
    mapping_ok mapping ∧
    num_bigger_than_rhs q r ∧
    EVERY (λq'. q > q') (MAP FST mapping) ∧
    ¬MEM q (MAP FST mapping) ⇒
    (eval_cnf w⦇q ↦ v⦈ (map_to_cnf mapping) ⇔
       eval_cnf w (map_to_cnf mapping))
Proof
  Induct >> rw[]
  >- rw[map_to_cnf_def, eval_cnf_def]
  >> Cases_on ‘h’ >> gs[]
  >> rw[map_to_cnf_def]
  >> rw[eval_cnf_def]
  >> last_x_assum (qspecl_then [‘q’, ‘v’, ‘w’] assume_tac)
  >> gs[mapping_ok_def]
  >> metis_tac[eval_same]
QED

Theorem mapping_always_true:
  ∀ mapping w.
    mapping_ok mapping ⇒
    eval_cnf (make_assignments w mapping) (map_to_cnf mapping)
Proof
  Induct >> rw[]
  >- rw[map_to_cnf_def, eval_cnf_def]
  >> Cases_on ‘h’ >> gs[]
  >> gs[mapping_ok_def]
  >> gs[map_to_cnf_def]
  >> rw[eval_cnf_def]
  >- rw[one_mapping_true]
  >> rw[make_assignments_def]
  >> metis_tac[mapping_always_true_inductive_step]
QED

Theorem make_assignments_thm:
  ∀xs w.
    eval_cnf w (map_to_cnf xs) ∧ mapping_ok xs ⇒
    make_assignments w xs = w
Proof
  Induct \\ fs [make_assignments_def,FORALL_PROD]
  \\ fs [APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum (qspecl_then [‘w’] mp_tac)
  \\ impl_tac
  THEN1 (fs [mapping_ok_def,map_to_cnf_def,eval_cnf_def])
  \\ rw [] \\ fs []
  \\ rw [] \\ fs []
  \\ fs [map_to_cnf_def,eval_cnf_def]
  \\ rename [‘rhs_to_cnf x y’]
  \\ Cases_on ‘y’ \\ fs []
  \\ fs [eval_rhs_def]
  \\ Cases_on ‘s’
  \\ TRY (Cases_on ‘s0’)
  \\ gvs [rhs_to_cnf_def,eval_cnf_def,eval_literal_def,replace_not_def,
          eval_clause_def,negate_literal_def,replace_and_def,replace_or_def,
          replace_impl_def,replace_iff_def]
QED

(* ------------- Main theorems ----------------------- *)

Theorem constFree_to_cnf_preserves_sat_2:
  ∀ b map' w l next next' xs ys.
    constFree_to_cnf_inner next b = (next', l, map') ∧
    get_fresh_name_constFree b ≤ next ∧
    (DISJOINT (next_range next next') (set (MAP FST xs))) ∧
    (DISJOINT (next_range next next') (set (MAP FST ys))) ∧
    (DISJOINT (next_range 0 (get_fresh_name_constFree b)) (set (MAP FST xs))) ∧
    (DISJOINT (next_range 0 (get_fresh_name_constFree b)) (set (MAP FST ys))) ⇒
    (eval_constFree w b ⇔
       eval_literal (make_assignments w (xs ++ append map' ++ ys)) l)
Proof
  Induct >> rw[]
  >- (gs[constFree_to_cnf_inner_def]
      >> gs[make_assignments_def]
      >> rw[eval_constFree_def]
      >> gvs[IN_DISJOINT, next_range_def]
      >> Cases_on ‘l’ >> gvs[get_fresh_name_constFree_def]
      >- (last_x_assum (qspecl_then [‘x’] mp_tac)
          >> last_x_assum (qspecl_then [‘x’] mp_tac)
          >> gvs[make_assignment_not_mem, make_assignment_not_mem_2,
                 eval_literal_def])
      >> last_x_assum (qspecl_then [‘y’] mp_tac)
      >> last_x_assum (qspecl_then [‘y’] mp_tac)
      >> gvs[make_assignment_not_mem, make_assignment_not_mem_2,
             eval_literal_def])
  >- (rw[eval_constFree_def]
      >> gs[constFree_to_cnf_inner_def, get_fresh_name_constFree_def]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> gvs[eval_literal_def]
      >> gvs[IN_DISJOINT]
      >> gvs[next_range_def]
      >> qspecl_then
         [‘xs’, ‘(next'',RNot l')::append map'' ++ ys’, ‘next''’, ‘w’]
         assume_tac make_assignment_not_mem
      >> last_x_assum (qspecl_then [‘next''’] assume_tac) >> gs[]
      >- metis_tac[next_bigger_lemma]
      >> rw[make_assignments_def]
      >> rw[APPLY_UPDATE_THM]
      >> rw[eval_rhs_def]
      >> rw[eval_literal_def]
      >> last_x_assum
         (qspecl_then [‘map''’, ‘w’, ‘l'’, ‘next’, ‘next''’, ‘[]’, ‘ys’]
          assume_tac)
      >> gs[]
      >> first_x_assum irule
      >> rw[]
      >> last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
  >> (rw[eval_constFree_def]
      >> gs[constFree_to_cnf_inner_def, get_fresh_name_constFree_def]
      >> pairarg_tac >> gs[]
      >> pairarg_tac >> gs[]
      >> gvs[bind_def]
      >> imp_res_tac next_bigger_lemma
      >> gvs[]
      >> rw[eval_literal_def, SimpRHS]
      >> gs[IN_DISJOINT]
      >> gs[next_range_def]
      >> last_x_assum (qspecl_then [‘next'''’] assume_tac) >> gs[]
      >> asm_simp_tac std_ss[make_assignment_not_mem, GSYM APPEND_ASSOC]
      >> rw[make_assignments_def]
      >> rw[APPLY_UPDATE_THM]
      >> rw[eval_rhs_def]
      >> last_x_assum
         (qspecl_then
          [‘map1’, ‘w’, ‘l1’, ‘next’, ‘next''’, ‘append map2’, ‘ys’] mp_tac)
      >> last_x_assum
         (qspecl_then [‘map2’, ‘w’, ‘l2’, ‘next''’, ‘next'''’,
                       ‘[]’, ‘append map1 ++ ys’] mp_tac)
      >> gvs[]
      >> impl_tac
      >- (rw[]
          >- (last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
              >> imp_res_tac mapping_range
              >> gs[EVERY_MEM]
              >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
              >> gs[next_range_def]
              >> Cases_on ‘MEM x (MAP FST (append map1))’ >> gs[])
          >> last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
          >- (first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
              >> imp_res_tac mapping_range
              >> gs[EVERY_MEM]
              >> first_x_assum (qspecl_then [‘x’] assume_tac)
              >> gs[next_range_def])
          >> imp_res_tac mapping_range
          >> gs[EVERY_MEM]
          >> gs[next_range_def]
          >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
          >> Cases_on ‘MEM x (MAP FST (append map1))’ >> gs[])
      >> strip_tac
      >> impl_tac
      >- (rw[]
          >- (imp_res_tac mapping_range
              >> gs[EVERY_MEM, next_range_def]
              >> Cases_on ‘MEM x (MAP FST (append map2))’ >> gs[]
              >> first_x_assum (qspecl_then [‘x’] assume_tac)
              >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
          >- (last_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
          >- (imp_res_tac mapping_range
              >> gs[EVERY_MEM, next_range_def]
              >> first_x_assum (qspecl_then [‘x’] assume_tac)
              >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[]
              >> Cases_on ‘MEM x (MAP FST (append map2))’ >> gs[])
          >> first_x_assum (qspecl_then [‘x’] assume_tac) >> gs[])
      >> strip_tac
      >> gvs[])
QED

Theorem constFree_to_cnf_preserves_sat:
  ∀ b w.
    eval_constFree w b ⇔
      eval_cnf (constFree_to_assignment w b) (constFree_to_cnf b)
Proof
  rw[constFree_to_cnf_def]
  >> pairarg_tac >> gvs[]
  >> rw[constFree_to_assignment_def]
  >> rw[eval_cnf_def, eval_clause_def]
  >> qspecl_then [‘b’, ‘map'’, ‘get_fresh_name_constFree b’, ‘next'’, ‘l’]
                 assume_tac mapping_created_ok
  >> gs[mapping_always_true]
  >> qspecl_then
     [‘b’, ‘map'’, ‘w’, ‘l’, ‘get_fresh_name_constFree b’, ‘next'’, ‘[]’, ‘[]’]
     assume_tac constFree_to_cnf_preserves_sat_2
  >> gs[]
QED                             (*  *)


(* ------------------ Theorems for boolExp to cnf --------------- *)

Theorem boolExp_to_constFree_preserves_sat:
  ∀ b w.
    eval_boolExp w b ⇔
      case boolExp_to_constFree b of
      | INL b' => eval_constFree w b'
      | INR bv => bv
Proof
  Induct >> rw[]
  >> TRY (rw[eval_boolExp_def, boolExp_to_constFree_def, eval_constFree_def]
          >> NO_TAC)
  >- (rw[eval_boolExp_def, boolExp_to_constFree_def]
      >> Cases_on ‘boolExp_to_constFree b’ >> gs[]
      >> rw[eval_constFree_def])
  >> (rw[eval_boolExp_def, boolExp_to_constFree_def]
      >> Cases_on ‘boolExp_to_constFree b’ >> gs[]
      >- (Cases_on ‘boolExp_to_constFree b'’ >> gs[]
          >> rw[eval_constFree_def])
      >> rw[]
      >> Cases_on ‘boolExp_to_constFree b'’ >> rw[]
      >> rw[eval_constFree_def])
QED

Theorem t_boolExp_to_cnf_preserves_sat:
  ∀ b w.
    eval_boolExp w b ⇔
      eval_cnf
      (t_boolExp_to_assignment w b)
      (t_boolExp_to_cnf b)
Proof
  gs[t_boolExp_to_cnf_def]
  >> gs[boolExp_to_constFree_preserves_sat]
  >> rw[]
  >> Cases_on ‘boolExp_to_constFree b’ >> rw[]
  >- gs[constFree_to_cnf_preserves_sat, t_boolExp_to_assignment_def]
  >- gs[eval_cnf_def]
  >> gs[eval_cnf_def, eval_clause_def]
QED

Theorem t_boolExp_to_cnf_imp_sat:
  eval_cnf w (t_boolExp_to_cnf b) ⇒
  eval_boolExp w b
Proof
  gvs [t_boolExp_to_cnf_preserves_sat]
  \\ gvs [t_boolExp_to_cnf_def]
  \\ reverse CASE_TAC \\ fs []
  THEN1 (rw [] \\ gvs [eval_cnf_def,eval_clause_def])
  \\ fs [constFree_to_cnf_def]
  \\ pairarg_tac \\ fs []
  \\ fs [eval_cnf_def] \\ strip_tac
  \\ fs [t_boolExp_to_assignment_def,constFree_to_assignment_def]
  \\ qsuff_tac ‘make_assignments w (append map') = w’ \\ fs []
  \\ ‘get_fresh_name_constFree x ≤ get_fresh_name_constFree x’ by gs []
  \\ drule_all mapping_created_ok \\ strip_tac
  \\ drule_all make_assignments_thm \\ fs []
QED

Theorem t_boolExp_to_cnf_preserves_unsat:
  unsat_boolExp b ⇔ unsat_cnf (t_boolExp_to_cnf b)
Proof
  eq_tac \\ rw [unsat_boolExp_def,unsat_cnf_def] \\ strip_tac
  \\ imp_res_tac t_boolExp_to_cnf_imp_sat
  \\ gvs [t_boolExp_to_cnf_preserves_sat]
QED


(* ----------------- Theorems for other encodings to cnf -------------------- *)

Theorem t_pseudoBool_to_cnf_preserves_sat:
  ∀ b w.
    eval_pseudoBool w b ⇔
      eval_cnf
      (t_pseudoBool_to_assignment w b)
      (t_pseudoBool_to_cnf b)
Proof
  gs[pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat,
     t_pseudoBool_to_cnf_def, t_pseudoBool_to_assignment_def,
     t_boolExp_to_cnf_preserves_sat]
QED

Theorem t_pseudoBool_to_cnf_imp_sat:
  eval_cnf w (t_pseudoBool_to_cnf b) ⇒
  eval_pseudoBool w b
Proof
  rw [t_pseudoBool_to_cnf_def]
  \\ imp_res_tac t_boolExp_to_cnf_imp_sat
  \\ fs [pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat]
QED

Theorem t_pseudoBool_to_cnf_preserves_unsat:
  unsat_pseudoBool b ⇔ unsat_cnf (t_pseudoBool_to_cnf b)
Proof
  fs [unsat_pseudoBool_def,t_pseudoBool_to_cnf_def,
      GSYM t_boolExp_to_cnf_preserves_unsat, unsat_boolExp_def,
      pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat]
QED

Theorem t_orderBool_to_cnf_preserves_sat:
  ∀ b w.
    eval_orderBool w b ⇔
      eval_cnf
      (t_orderBool_to_assignment w b)
      (t_orderBool_to_cnf b)
Proof
  gs[orderBool_to_pseudoBool_preserves_sat, t_orderBool_to_cnf_def,
     t_orderBool_to_assignment_def, t_pseudoBool_to_cnf_preserves_sat]
QED

Theorem t_orderBool_to_cnf_imp_sat:
  eval_cnf w (t_orderBool_to_cnf b) ⇒
  eval_orderBool w b
Proof
  rw [t_orderBool_to_cnf_def]
  \\ imp_res_tac t_pseudoBool_to_cnf_imp_sat
  \\ fs [orderBool_to_pseudoBool_preserves_sat]
QED

Theorem t_orderBool_to_cnf_preserves_unsat:
  unsat_orderBool b ⇔ unsat_cnf (t_orderBool_to_cnf b)
Proof
  fs [unsat_orderBool_def,t_orderBool_to_cnf_def, unsat_pseudoBool_def,
      GSYM t_pseudoBool_to_cnf_preserves_unsat, orderBool_to_pseudoBool_preserves_sat]
QED

Theorem t_numBool_to_cnf_preserves_sat:
  ∀ e vList w w'.
    numVarList_ok vList ∧
    exp_numVarList_ok vList e ∧
    minimal_numVarAssignment_ok w' vList ⇒
    (eval_numBoolExp w w' e ⇔
       eval_cnf
       (t_numBoolExp_to_assignment w w' vList e)
       (t_numBool_to_cnf vList e))
Proof
  rw[]
  >> imp_res_tac minimal_numVarAssignment_equal
  >> first_x_assum (qspecl_then [‘e’] assume_tac)
  >> qspecl_then [‘e’, ‘w’, ‘w'’, ‘vList’] assume_tac
                 numBool_to_orderBool_preserves_sat >> gs[]
  >> rw[t_numBool_to_cnf_def, t_numBoolExp_to_assignment_def,
        t_orderBool_to_cnf_preserves_sat]
  >> metis_tac[minimal_encode_assignment_def]
QED

Theorem imp_find_value_lt:
  ∀xs. EVERY (λ(k,m). m < n) xs ∧ n ≠ 0 ⇒
       find_value w xs < n
Proof
  Induct \\ fs [find_value_def, FORALL_PROD] \\ rw []
QED

Theorem find_value_le_lemma:
  ∀n m p_2.
    n < LENGTH p_2 ∧ EL n p_2 = (x,m) ∧ w x ∧
    (∀i. i ≤ n ⇒ ∃y k. EL i p_2 = (y,k) ∧ k ≤ m) ⇒
    find_value w p_2 ≤ m
Proof
  Induct_on ‘p_2’ \\ fs [] \\ strip_tac
  \\ PairCases_on ‘h’ \\ fs [find_value_def]
  \\ Cases \\ fs [] \\ rw []
  THEN1 (first_x_assum (qspec_then ‘0’ mp_tac) \\ fs [])
  \\ first_x_assum irule \\ fs []
  \\ first_x_assum (irule_at (Pos last)) \\ rw []
  \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ fs []
QED

Theorem MEM_encode_axioms:
  eval_orderBool w (encode_axioms vMap) ∧ MEM (p_1,p_2) vMap ⇒
  eval_orderAxiom w (MAP FST p_2)
Proof
  Induct_on ‘vMap’ \\ fs [FORALL_PROD] \\ rw []
  \\ fs [encode_axioms_def,eval_orderBool_def]
QED

Theorem find_value_append_lemma:
  eval_orderAxiom w (MAP FST ys1 ++ x::MAP FST t) ∧ ¬w x ⇒
  find_value w (ys1 ++ (x,m)::t) = find_value w t ∧
  eval_orderAxiom w (MAP FST t)
Proof
  Induct_on ‘ys1’ \\ fs [] \\ rw []
  \\ gvs [find_value_def,eval_orderAxiom_def]
  \\ PairCases_on ‘h’ \\ gvs [find_value_def]
QED

Theorem encode_assignment_cancel:
  numVarMap_ok vMap ∧ exp_numVarMap_ok vMap e ∧
  eval_orderBool w (encode_axioms vMap) ⇒
  encode_assignment w
    (assignment_to_numVarAssignment w vMap) vMap = w
Proof
  fs [encode_assignment_def,FUN_EQ_THM]
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [invert_numVarMap_def]
  \\ gvs [MEM_FLAT,MEM_MAP,EXISTS_PROD]
  \\ fs [assignment_to_numVarAssignment_def]
  \\ fs [numVarMap_ok_def]
  \\ drule_all ALOOKUP_ALL_DISTINCT_MEM
  \\ rw []
  \\ ‘MAP SND p_2 = GENLIST I (LENGTH p_2)’ by
   (fs [EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ first_x_assum irule \\ metis_tac [])
  \\ drule_at Any el_genlist_lemma
  \\ qpat_x_assum ‘MEM (x,r) p_2’ mp_tac
  \\ simp [MEM_EL] \\ rw []
  \\ qpat_x_assum ‘_  = EL n p_2’ (assume_tac o GSYM)
  \\ first_x_assum drule \\ gvs []
  \\ rw [] \\ gvs []
  \\ ‘p_2 ≠ []’ by (strip_tac \\ gvs [])
  \\ ‘∀i. i ≤ n ⇒ ∃y k. EL i p_2 = (y,k) ∧ k ≤ n’ by
        (rw [] \\ drule_at (Pos last) el_genlist_lemma
         \\ Cases_on ‘EL i p_2’ \\ fs []
         \\ ‘i < LENGTH p_2’ by fs []
         \\ disch_then drule \\ fs [])
  \\ Cases_on ‘w x’ \\ fs []
  THEN1 (drule_all find_value_le_lemma \\ fs [])
  \\ fs [GSYM NOT_LESS]
  \\ drule_all MEM_encode_axioms
  \\ fs [NOT_LESS]
  \\ ‘∀i. n < i ∧ i < LENGTH p_2 ⇒ ∃y k. EL i p_2 = (y,k) ∧ n < k’ by
        (rw [] \\ drule_at (Pos last) el_genlist_lemma
         \\ Cases_on ‘EL i p_2’ \\ fs []
         \\ ‘i < LENGTH p_2’ by fs []
         \\ disch_then drule \\ fs [])
  \\ ‘n ≤ LENGTH p_2’ by fs []
  \\ drule LESS_EQ_LENGTH
  \\ rfs [] \\ strip_tac \\ gvs []
  \\ ‘~NULL ys2’ by (Cases_on ‘ys2’ \\ fs [])
  \\ gvs [EL_LENGTH_APPEND]
  \\ Cases_on ‘ys2’ \\ gvs []
  \\ strip_tac
  \\ drule_all find_value_append_lemma \\ rw []
  \\ ‘EVERY (λ(y,k). LENGTH ys1 < k) t’ by
   (fs [EVERY_EL,FORALL_PROD] \\ rw []
    \\ qpat_x_assum ‘∀x._’ kall_tac
    \\ first_x_assum (qspec_then ‘LENGTH ys1 + SUC n’ mp_tac)
    \\ fs [] \\ fs [EL_APPEND2] \\ rw [] \\ fs [])
  \\ fs [GSYM PULL_FORALL]
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac ‘t’ \\ Induct \\ fs [eval_orderAxiom_def]
  \\ fs [FORALL_PROD,find_value_def] \\ rw []
QED

Theorem t_numBool_to_cnf_imp_sat:
  numVarList_ok vList ∧
  exp_numVarList_ok vList e ⇒
  eval_cnf w (t_numBool_to_cnf vList e) ⇒
  eval_numBoolExp w
    (assignment_to_numVarAssignment w (create_numVarMap e vList)) e
Proof
  rw [t_numBool_to_cnf_def, numBool_to_orderBool_def]
  \\ drule t_orderBool_to_cnf_imp_sat \\ strip_tac
  \\ fs [eval_orderBool_def]
  \\ drule numBool_to_orderBool_preserves_sat
  \\ disch_then drule
  \\ qsuff_tac
     ‘numVarAssignment_ok (assignment_to_numVarAssignment w
        (create_numVarMap e vList)) (create_numVarMap e vList) ∧
      encode_assignment w
        (assignment_to_numVarAssignment w (create_numVarMap e vList))
        (create_numVarMap e vList) = w’
  THEN1 (strip_tac \\ disch_then drule \\ fs []
         \\ fs [numBool_to_orderBool_def,eval_orderBool_def])
  \\ reverse (rw [])
  THEN1
   (drule_all (SIMP_RULE std_ss [] numVarMap_created_ok) \\ rw []
    \\ irule encode_assignment_cancel
    \\ fs [] \\ metis_tac [])
  \\ rw [numVarAssignment_ok_def,EVERY_MEM,FORALL_PROD]
  \\ fs [assignment_to_numVarAssignment_def]
  \\ drule_all (SIMP_RULE std_ss [] numVarMap_created_ok)
  \\ fs [numVarMap_ok_def] \\ strip_tac
  \\ drule_all ALOOKUP_ALL_DISTINCT_MEM \\ rw []
  \\ irule imp_find_value_lt
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ first_x_assum drule
  \\ rw [] THEN1 (CCONTR_TAC \\ fs [])
  \\ drule_at Any el_genlist_lemma
  \\ pop_assum mp_tac
  \\ simp [MEM_EL] \\ rw []
  \\ first_x_assum drule \\ fs []
  \\ pop_assum (assume_tac o GSYM) \\ fs []
QED

Theorem imp_find_value_leq:
  ∀xs. EVERY (λ(k,m). m ≤ n) xs ⇒ find_value w xs ≤ n
Proof
  Induct \\ fs [find_value_def, FORALL_PROD] \\ rw []
QED

Theorem t_numBool_to_cnf_preserves_unsat:
  numVarList_ok vList ∧ exp_numVarList_ok vList e ⇒
  (unsat_numBoolExp (SND vList) e ⇔
   unsat_cnf (t_numBool_to_cnf vList e))
Proof
  rw [] \\ eq_tac \\ rw [unsat_numBoolExp_def,unsat_cnf_def] \\ strip_tac
  THEN1
   (drule t_numBool_to_cnf_imp_sat
    \\ disch_then drule
    \\ disch_then drule
    \\ fs [] \\ CCONTR_TAC \\ fs []
    \\ first_x_assum (qspec_then ‘w’ mp_tac) \\ fs []
    \\ first_x_assum $ irule_at Any
    \\ fs [assignment_to_numVarAssignment_def] \\ rw []
    \\ CASE_TAC \\ fs [create_numVarMap_def]
    \\ Cases_on ‘vList’ \\ fs []
    \\ pop_assum mp_tac
    \\ qspec_tac (‘get_fresh_boolVar e’,‘nn’)
    \\ qid_spec_tac ‘q’
    \\ Induct \\ fs [create_numVarMap_inner_def]
    \\ rw [] \\ res_tac \\ fs []
    \\ irule imp_find_value_leq \\ fs [EVERY_GENLIST])
  \\ drule t_numBool_to_cnf_preserves_sat
  \\ disch_then drule
  \\ ‘minimal_numVarAssignment_ok w' vList’ by fs [minimal_numVarAssignment_ok_def]
  \\ disch_then drule
  \\ strip_tac \\ gvs []
QED

Theorem t_numBoolExtended_to_cnf_preserves_sat:
  ∀ e vList w w'.
    numVarList_ok vList ∧
    extended_numVarList_ok  vList e ∧
    minimal_numVarAssignment_ok w' vList ⇒
    (eval_numBoolExtended w w' e ⇔
       eval_cnf
       (t_numBoolExtended_to_assignment w w' vList e)
       (t_numBoolExtended_to_cnf vList e))
Proof
  rw[numBoolExtended_to_numBoolExp_preserves_sat, t_numBoolExtended_to_cnf_def,
     t_numBoolExtended_to_assignment_def]
  >> metis_tac[t_numBool_to_cnf_preserves_sat, numVarList_ok_lemma]
QED

Theorem t_numBool_to_cnf_imp_sat:
  numVarList_ok vList ∧
  extended_numVarList_ok vList e ∧
  eval_cnf w (t_numBoolExtended_to_cnf vList e) ⇒
  eval_numBoolExtended w (assignment_to_numVarAssignment w
    (create_numVarMap (numBoolExtended_to_numBoolExp e) vList)) e
Proof
  rw [t_numBoolExtended_to_cnf_def,
      extended_numVarList_ok_def]
  \\ imp_res_tac numVarList_ok_lemma
  \\ drule_all t_numBool_to_cnf_imp_sat
  \\ fs [numBoolExtended_to_numBoolExp_preserves_sat]
QED

Theorem t_numBool_to_cnf_preserves_unsat:
  numVarList_ok vList ∧ extended_numVarList_ok vList e ⇒
  (unsat_numBoolExtended (SND vList) e ⇔
   unsat_cnf (t_numBoolExtended_to_cnf vList e))
Proof
  rw [t_numBoolExtended_to_cnf_def]
  \\ imp_res_tac numVarList_ok_lemma
  \\ fs [GSYM t_numBool_to_cnf_preserves_unsat]
  \\ fs [unsat_numBoolExp_def,unsat_numBoolExtended_def]
  \\ fs [numBoolExtended_to_numBoolExp_preserves_sat]
QED

Theorem t_numBoolRange_to_cnf_preserves_sat:
  ∀ e l w w'.
    rangeList_ok l ∧
    exp_rangeList_ok l e ∧
    numVarAssignment_range_ok w' l ⇒
    (eval_numBoolRange w w' e ⇔
       eval_cnf
       (t_numBoolRange_to_assignment w w' l e)
       (t_numBoolRange_to_cnf l e))
Proof
  rw[]
  >> imp_res_tac numBoolRange_to_numBoolExtended_preserves_sat >> gs[]
  >> rw[t_numBoolRange_to_cnf_def, t_numBoolRange_to_assignment_def]
  >> imp_res_tac rangeList_encoded_ok
  >> imp_res_tac exp_rangeList_encoded_ok
  >> imp_res_tac numVarAssignment_encoded_ok
  >> metis_tac[t_numBoolExtended_to_cnf_preserves_sat]
QED

val _ = export_theory();
