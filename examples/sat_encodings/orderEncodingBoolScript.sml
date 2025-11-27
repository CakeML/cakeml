(*
  Extend pseudoBoolExp with OrderAxiom, to prepare for order encoding
  of natural numbers.
*)
Theory orderEncodingBool
Ancestors
  misc quantifierExp boolExpToCnf cnf
Libs
  preamble


(* ----------------------------- Types --------------------------- *)

Datatype:
  orderBool =
  OTrue
  | OFalse
  | OLit literal
  | ONot orderBool
  | OAnd orderBool orderBool
  | OOr orderBool orderBool
  | OImpl orderBool orderBool
  | OIff orderBool orderBool
  | OAll name orderBool
  | OEx name orderBool
  | OLeastOne (orderBool list) (* At least one *)
  | OMostOne (orderBool list) (* At most one *)
  | OExactlyOne (orderBool list) (* Exactly one *)
  | OOrderAxiom (name list)
End

(* OOrderAxiom [a, b, c] = FFT or FTT or TTT *)

Definition orderBool_size':
  (orderBool_size' OTrue = 1:num) ∧
  (orderBool_size' OFalse = 1) ∧
  (orderBool_size' (OLit l) = 1) ∧
  (orderBool_size' (ONot b) = 1 + orderBool_size' b) ∧
  (orderBool_size' (OAnd b1 b2) =
   1 + (orderBool_size' b1 + orderBool_size' b2)) ∧
  (orderBool_size' (OOr b1 b2) =
   1 + (orderBool_size' b1 + orderBool_size' b2)) ∧
  (orderBool_size' (OImpl b1 b2) =
   1 + (orderBool_size' b1 + orderBool_size' b2)) ∧
  (orderBool_size' (OIff b1 b2) =
   1 + (orderBool_size' b1 + orderBool_size' b2)) ∧
  (orderBool_size' (OAll x b) =
   1 + 4 * (orderBool_size' b)) ∧
  (orderBool_size' (OEx x b) =
   1 + 4 * (orderBool_size' b)) ∧
  (orderBool_size' (OLeastOne []) = 1) ∧
  (orderBool_size' (OLeastOne (b::bs)) =
   1 + orderBool_size' b + orderBool_size' (OLeastOne bs)) ∧
  (orderBool_size' (OMostOne []) = 1) ∧
  (orderBool_size' (OMostOne (b::bs)) =
   1 + orderBool_size' b + orderBool_size' (OMostOne bs)) ∧
  (orderBool_size' (OExactlyOne []) = 2) ∧
  (orderBool_size' (OExactlyOne (b::bs)) =
   3 + orderBool_size' b * 2 + orderBool_size' (OExactlyOne bs)) ∧
  (orderBool_size' (OOrderAxiom xs) = 1)
End

(* ----------------------------- Evaluation --------------------------- *)

Definition eval_orderAxiom_def:
  eval_orderAxiom (w:assignment) [] = F ∧  (* Last element has to be T *)
  eval_orderAxiom w (x::xs) =
  if w x
  then EVERY w xs
  else eval_orderAxiom w xs
End

Definition eval_orderBool_def:
  eval_orderBool (w: assignment) OTrue = T ∧
  eval_orderBool w OFalse = F ∧
  eval_orderBool w (OLit l) = eval_literal w l ∧
  eval_orderBool w (ONot b) = ¬ (eval_orderBool w b) ∧
  eval_orderBool w (OAnd b1 b2) =
  (eval_orderBool w b1 ∧ eval_orderBool w b2) ∧
  eval_orderBool w (OOr b1 b2) =
  (eval_orderBool w b1 ∨ eval_orderBool w b2) ∧
  eval_orderBool w (OImpl b1 b2) =
  (eval_orderBool w b1 ⇒ eval_orderBool w b2) ∧
  eval_orderBool w (OIff b1 b2) =
  (eval_orderBool w b1 ⇔ eval_orderBool w b2) ∧
  eval_orderBool w (OAll x b) =
  (∀ v. eval_orderBool ((x =+ v) w) b) ∧
  eval_orderBool w (OEx x b) =
  (∃ v. eval_orderBool ((x =+ v) w) b) ∧
  eval_orderBool w (OLeastOne bs) =
  (sum_bools (MAP (eval_orderBool w) bs) ≥ 1) ∧
  eval_orderBool w (OMostOne bs) =
  (sum_bools (MAP (eval_orderBool w) bs) ≤ 1) ∧
  eval_orderBool w (OExactlyOne bs) =
  (sum_bools (MAP (eval_orderBool w) bs) = 1) ∧
  eval_orderBool w (OOrderAxiom xs) = eval_orderAxiom w xs
Termination
  WF_REL_TAC ‘measure (λ (w,b). orderBool_size' b)’
  >> rw[orderBool_size']
  >> Induct_on ‘bs’
  >> rw[orderBool_size']
  >> gs[orderBool_size']
End

Definition unsat_orderBool_def:
  unsat_orderBool b ⇔ ∀w. ¬eval_orderBool w b
End

(* ----------------------- Encoding ---------------------------------- *)

Definition encode_orderAxiom_def:
  encode_orderAxiom [] = PFalse ∧
  encode_orderAxiom [x] = PLit (INL x) ∧
  encode_orderAxiom (x::y::xs) =
  PAnd (PImpl (PLit (INL x)) (PLit (INL y))) (encode_orderAxiom (y::xs))
End

Definition orderBool_to_pseudoBool_def:
  (orderBool_to_pseudoBool OTrue = PTrue) ∧
  (orderBool_to_pseudoBool OFalse = PFalse) ∧
  (orderBool_to_pseudoBool (OLit l) = PLit l) ∧
  (orderBool_to_pseudoBool (ONot b) = PNot (orderBool_to_pseudoBool b)) ∧
  (orderBool_to_pseudoBool (OAnd b1 b2) =
   PAnd (orderBool_to_pseudoBool b1) (orderBool_to_pseudoBool b2)) ∧
  (orderBool_to_pseudoBool (OOr b1 b2) =
   POr (orderBool_to_pseudoBool b1) (orderBool_to_pseudoBool b2)) ∧
  (orderBool_to_pseudoBool (OImpl b1 b2) =
   PImpl (orderBool_to_pseudoBool b1) (orderBool_to_pseudoBool b2)) ∧
  (orderBool_to_pseudoBool (OIff b1 b2) =
   PIff (orderBool_to_pseudoBool b1) (orderBool_to_pseudoBool b2)) ∧
  (orderBool_to_pseudoBool (OAll x b) =
   PAll x (orderBool_to_pseudoBool b)) ∧
  (orderBool_to_pseudoBool (OEx x b) =
   PEx x (orderBool_to_pseudoBool b)) ∧
  (orderBool_to_pseudoBool (OLeastOne bs) =
   PLeastOne (MAP orderBool_to_pseudoBool bs)) ∧
  (orderBool_to_pseudoBool (OMostOne bs) =
   PMostOne (MAP orderBool_to_pseudoBool bs)) ∧
  (orderBool_to_pseudoBool (OExactlyOne bs) =
   PExactlyOne (MAP orderBool_to_pseudoBool bs)) ∧
  (orderBool_to_pseudoBool (OOrderAxiom xs) = encode_orderAxiom xs)
Termination
  WF_REL_TAC ‘measure orderBool_size'’
  >> rw[orderBool_size']
  >> Induct_on ‘bs’
  >> rw[pseudoBool_size']
  >> gs[orderBool_size']
End

Definition orderBool_to_cnf_def:
  orderBool_to_cnf exp = pseudoBool_to_cnf (orderBool_to_pseudoBool exp)
End

(* ----------------------- Theorems ------------------------------------ *)

Theorem sum_bools_equal:
  ∀ bs w.
    (∀ b. MEM b bs ⇒
          ∀ w. eval_orderBool w b ⇔
                 eval_pseudoBool w (orderBool_to_pseudoBool b)) ⇒
    (sum_bools (MAP (eval_orderBool w) bs) =
       sum_bools (MAP (eval_pseudoBool w) (MAP orderBool_to_pseudoBool bs)))
Proof
  Induct >> rw[]
  >> Cases_on ‘eval_pseudoBool w (orderBool_to_pseudoBool h)’
  >> gs[sum_bools_def]
QED

Theorem orderBool_to_pseudoBool_preserves_sat:
  ∀ b w.
    eval_orderBool w b =
    eval_pseudoBool w (orderBool_to_pseudoBool b)
Proof
  ho_match_mp_tac orderBool_to_pseudoBool_ind >> rw[]
  >> TRY (rw[eval_orderBool_def, orderBool_to_pseudoBool_def,
             eval_pseudoBool_def]
          >> NO_TAC)
  >> TRY (gs[eval_orderBool_def, orderBool_to_pseudoBool_def,
             eval_pseudoBool_def]
          >> qspecl_then [‘bs’, ‘w’] assume_tac sum_bools_equal
          >> gs[]
          >> metis_tac[]
          >> NO_TAC)
  >> rw[eval_orderBool_def, orderBool_to_pseudoBool_def]
  >> Induct_on ‘xs’
  >- rw[eval_orderAxiom_def, encode_orderAxiom_def, eval_pseudoBool_def]
  >> gs[eval_orderAxiom_def]
  >> Induct_on ‘xs’
  >- gs[encode_orderAxiom_def, eval_pseudoBool_def, eval_literal_def]
  >> rw[]
  >> gs[eval_orderAxiom_def, encode_orderAxiom_def,
        eval_pseudoBool_def, eval_literal_def]
  >> Cases_on ‘w h'’ >> rw[]
  >> Cases_on ‘w h’ >> rw[]
  >> gs[]
QED

Definition orderBool_to_assignment_def:
  orderBool_to_assignment w b =
  pseudoBool_to_assignment w (orderBool_to_pseudoBool b)
End

Theorem orderBool_to_cnf_preserves_sat:
  ∀ b w.
    eval_orderBool w b ⇔
      eval_cnf
      (orderBool_to_assignment w b)
      (orderBool_to_cnf b)
Proof
  gs[orderBool_to_pseudoBool_preserves_sat, orderBool_to_cnf_def,
     orderBool_to_assignment_def, pseudoBool_to_cnf_preserves_sat]
QED

Theorem orderBool_to_cnf_imp_sat:
  eval_cnf w (orderBool_to_cnf b) ⇒
  eval_orderBool w b
Proof
  rw [orderBool_to_cnf_def]
  \\ imp_res_tac pseudoBool_to_cnf_imp_sat
  \\ fs [orderBool_to_pseudoBool_preserves_sat]
QED

Theorem orderBool_to_cnf_preserves_unsat:
  unsat_orderBool b ⇔ unsat_cnf (orderBool_to_cnf b)
Proof
  fs [unsat_orderBool_def,orderBool_to_cnf_def, unsat_pseudoBool_def,
      GSYM pseudoBool_to_cnf_preserves_unsat, orderBool_to_pseudoBool_preserves_sat]
QED

