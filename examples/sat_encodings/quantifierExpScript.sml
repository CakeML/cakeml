(*
  Quantifiers over Boolean expressions and pseudo-Boolean constraints
*)
Theory quantifierExp
Ancestors
  misc boolExpToCnf cnf
Libs
  preamble


Datatype:
  quant =
    QTrue
  | QFalse
  | QLit literal
  | QNot quant
  | QAnd quant quant
  | QOr quant quant
  | QImpl quant quant
  | QIff quant quant
  | QAll name quant
  | QEx name quant
End

Datatype:
  pseudoBool =
    PTrue
  | PFalse
  | PLit literal
  | PNot pseudoBool
  | PAnd pseudoBool pseudoBool
  | POr pseudoBool pseudoBool
  | PImpl pseudoBool pseudoBool
  | PIff pseudoBool pseudoBool
  | PAll name pseudoBool
  | PEx name pseudoBool
  | PLeastOne (pseudoBool list) (* At least one *)
  | PMostOne (pseudoBool list) (* At most one *)
  | PExactlyOne (pseudoBool list) (* Exactly one *)
End

(* PLeastOne [a, b, c] = a ∨ b ∨ c *)
(* PMostOne [a, b, c] = (a ⇒ (¬b ∧ ¬c)) ∧ (b ⇒ ¬c) ∧ (c ⇒ T) *)
(* PExactlyOne [a, b, c] = PLeastOne [a, b, c] ∧ PMostOne [a, b, c] *)


Definition quant_size':
  (quant_size' QTrue = 1:num) ∧
  (quant_size' QFalse = 1) ∧
  (quant_size' (QLit l) = 1) ∧
  (quant_size' (QNot b) = 1 + quant_size' b) ∧
  (quant_size' (QAnd b1 b2) =
     1 + (quant_size' b1 + quant_size' b2)) ∧
  (quant_size' (QOr b1 b2) =
     1 + (quant_size' b1 + quant_size' b2)) ∧
  (quant_size' (QImpl b1 b2) =
     1 + (quant_size' b1 + quant_size' b2)) ∧
  (quant_size' (QIff b1 b2) =
   1 + (quant_size' b1 + quant_size' b2)) ∧
  (quant_size' (QAll x b) =
   1 + 4 * (quant_size' b)) ∧
   (quant_size' (QEx x b) =
   1 + 4 * (quant_size' b))
End

Definition pseudoBool_size':
  (pseudoBool_size' PTrue = 1:num) ∧
  (pseudoBool_size' PFalse = 1) ∧
  (pseudoBool_size' (PLit l) = 1) ∧
  (pseudoBool_size' (PNot b) = 1 + pseudoBool_size' b) ∧
  (pseudoBool_size' (PAnd b1 b2) =
     1 + (pseudoBool_size' b1 + pseudoBool_size' b2)) ∧
  (pseudoBool_size' (POr b1 b2) =
     1 + (pseudoBool_size' b1 + pseudoBool_size' b2)) ∧
  (pseudoBool_size' (PImpl b1 b2) =
     1 + (pseudoBool_size' b1 + pseudoBool_size' b2)) ∧
  (pseudoBool_size' (PIff b1 b2) =
   1 + (pseudoBool_size' b1 + pseudoBool_size' b2)) ∧
  (pseudoBool_size' (PAll x b) =
   1 + 4 * (pseudoBool_size' b)) ∧
  (pseudoBool_size' (PEx x b) =
   1 + 4 * (pseudoBool_size' b)) ∧
  (pseudoBool_size' (PLeastOne []) = 1) ∧
  (pseudoBool_size' (PLeastOne (b::bs)) =
   1 + pseudoBool_size' b + pseudoBool_size' (PLeastOne bs)) ∧
  (pseudoBool_size' (PMostOne []) = 1) ∧
  (pseudoBool_size' (PMostOne (b::bs)) =
   1 + pseudoBool_size' b + pseudoBool_size' (PMostOne bs)) ∧
  (pseudoBool_size' (PExactlyOne []) = 2) ∧
  (pseudoBool_size' (PExactlyOne (b::bs)) =
   3 + pseudoBool_size' b * 2 + pseudoBool_size' (PExactlyOne bs))
End


(* ----------------------------- Evaluation --------------------------- *)

Definition bool_to_quant_def[simp]:
  bool_to_quant T = QTrue ∧
  bool_to_quant F = QFalse
End

Definition remove_def:
  remove (x: 'a) [] = [] ∧
  remove x (y::ys) = (if x = y then ys else y :: remove x ys)
End

Definition eval_quant_def:
  eval_quant (w: assignment) QTrue = T ∧
  eval_quant w QFalse = F ∧
  eval_quant w (QLit l) = eval_literal w l ∧
  eval_quant w (QNot b) = ¬ (eval_quant w b) ∧
  eval_quant w (QAnd b1 b2) = (eval_quant w b1 ∧ eval_quant w b2) ∧
  eval_quant w (QOr b1 b2) = (eval_quant w b1 ∨ eval_quant w b2) ∧
  eval_quant w (QImpl b1 b2) = (eval_quant w b1 ⇒ eval_quant w b2) ∧
  eval_quant w (QIff b1 b2) = (eval_quant w b1 ⇔ eval_quant w b2) ∧
  eval_quant w (QAll x b) =
  (∀ v. eval_quant ((x =+ v) w) b) ∧
  eval_quant w (QEx x b) =
  (∃ v. eval_quant ((x =+ v) w) b)
End

Definition sum_bools_def:
  sum_bools [] = (0:num) ∧
  sum_bools (T::bs) = 1 + sum_bools bs ∧
  sum_bools (F::bs) = sum_bools bs
End

Definition eval_pseudoBool_def:
  eval_pseudoBool (w: assignment) PTrue = T ∧
  eval_pseudoBool w PFalse = F ∧
  eval_pseudoBool w (PLit l) = eval_literal w l ∧
  eval_pseudoBool w (PNot b) = ¬ (eval_pseudoBool w b) ∧
  eval_pseudoBool w (PAnd b1 b2) =
  (eval_pseudoBool w b1 ∧ eval_pseudoBool w b2) ∧
  eval_pseudoBool w (POr b1 b2) =
  (eval_pseudoBool w b1 ∨ eval_pseudoBool w b2) ∧
  eval_pseudoBool w (PImpl b1 b2) =
  (eval_pseudoBool w b1 ⇒ eval_pseudoBool w b2) ∧
  eval_pseudoBool w (PIff b1 b2) =
  (eval_pseudoBool w b1 ⇔ eval_pseudoBool w b2) ∧
  eval_pseudoBool w (PAll x b) =
  (∀ v. eval_pseudoBool ((x =+ v) w) b) ∧
  eval_pseudoBool w (PEx x b) =
  (∃ v. eval_pseudoBool ((x =+ v) w) b) ∧
  eval_pseudoBool w (PLeastOne bs) =
  (sum_bools (MAP (eval_pseudoBool w) bs) ≥ 1) ∧
  eval_pseudoBool w (PMostOne bs) =
  (sum_bools (MAP (eval_pseudoBool w) bs) ≤ 1) ∧
  eval_pseudoBool w (PExactlyOne bs) =
  (sum_bools (MAP (eval_pseudoBool w) bs) = 1)
Termination
  WF_REL_TAC ‘measure (λ (w,b). pseudoBool_size' b)’
  >> rw[pseudoBool_size']
  >> Induct_on ‘bs’
  >> rw[pseudoBool_size']
  >> gs[pseudoBool_size']
End

Definition unsat_pseudoBool_def:
  unsat_pseudoBool b ⇔ ∀w. ¬eval_pseudoBool w b
End

(* ----------------------- Encoding ---------------------------------- *)

Definition replace_name_quant_def:
  (replace_name_quant x v QTrue = QTrue) ∧
  (replace_name_quant x v QFalse = QFalse) ∧
  (replace_name_quant x v (QLit l) =
   if l = INL x then (bool_to_quant v) else
     if l = INR x then (bool_to_quant ¬ v) else
       QLit l) ∧
  (replace_name_quant x v (QNot b) = QNot (replace_name_quant x v b)) ∧
  (replace_name_quant x v (QAnd b1 b2) =
   QAnd (replace_name_quant x v b1) (replace_name_quant x v b2)) ∧
  (replace_name_quant x v (QOr b1 b2) =
   QOr (replace_name_quant x v b1) (replace_name_quant x v b2)) ∧
  (replace_name_quant x v (QImpl b1 b2) =
   QImpl (replace_name_quant x v b1) (replace_name_quant x v b2)) ∧
  (replace_name_quant x v (QIff b1 b2) =
   QIff (replace_name_quant x v b1) (replace_name_quant x v b2)) ∧
  (replace_name_quant x v (QAll x' b) =
   if x = x' then QAll x b else
     QAll x' (replace_name_quant x v b)) ∧
  (replace_name_quant x v (QEx x' b) =
   if x = x' then QEx x b else
     QEx x' (replace_name_quant x v b))
End

Definition quant_to_boolExp_def:
  (quant_to_boolExp QTrue = True) ∧
  (quant_to_boolExp QFalse = False) ∧
  (quant_to_boolExp (QLit l) = Lit l) ∧
  (quant_to_boolExp (QNot b) = Not (quant_to_boolExp b)) ∧
  (quant_to_boolExp (QAnd b1 b2) =
   And (quant_to_boolExp b1) (quant_to_boolExp b2)) ∧
  (quant_to_boolExp (QOr b1 b2) =
   Or (quant_to_boolExp b1) (quant_to_boolExp b2)) ∧
  (quant_to_boolExp (QImpl b1 b2) =
   Impl (quant_to_boolExp b1) (quant_to_boolExp b2)) ∧
  (quant_to_boolExp (QIff b1 b2) =
   Iff (quant_to_boolExp b1) (quant_to_boolExp b2)) ∧
  (quant_to_boolExp (QAll x b) =
   And
   (quant_to_boolExp (replace_name_quant x T b))
   (quant_to_boolExp (replace_name_quant x F b))) ∧
  (quant_to_boolExp (QEx x b) =
   Or
   (quant_to_boolExp (replace_name_quant x T b))
   (quant_to_boolExp (replace_name_quant x F b)))
Termination
  WF_REL_TAC ‘measure (λ b. quant_size' b)’
  >> rw[quant_size']
  >> Induct_on ‘b’
  >> rw[quant_size', replace_name_quant_def]
End

Definition none_of_list_to_quant_def:
  none_of_list_to_quant [] = QTrue ∧
  none_of_list_to_quant (b::bs) =
  QAnd (QNot b) (none_of_list_to_quant bs)
End

Definition most_one_to_quant_def:
  most_one_to_quant [] = QTrue ∧
  most_one_to_quant (b::bs) =
  QAnd
  (QImpl b (none_of_list_to_quant bs))
  (most_one_to_quant bs)
End

Definition pseudoBool_to_quant_def:
  (pseudoBool_to_quant PTrue = QTrue) ∧
  (pseudoBool_to_quant PFalse = QFalse) ∧
  (pseudoBool_to_quant (PLit l) = QLit l) ∧
  (pseudoBool_to_quant (PNot b) = QNot (pseudoBool_to_quant b)) ∧
  (pseudoBool_to_quant (PAnd b1 b2) =
   QAnd (pseudoBool_to_quant b1) (pseudoBool_to_quant b2)) ∧
  (pseudoBool_to_quant (POr b1 b2) =
   QOr (pseudoBool_to_quant b1) (pseudoBool_to_quant b2)) ∧
  (pseudoBool_to_quant (PImpl b1 b2) =
   QImpl (pseudoBool_to_quant b1) (pseudoBool_to_quant b2)) ∧
  (pseudoBool_to_quant (PIff b1 b2) =
   QIff (pseudoBool_to_quant b1) (pseudoBool_to_quant b2)) ∧
  (pseudoBool_to_quant (PAll x b) =
   QAll x (pseudoBool_to_quant b)) ∧
  (pseudoBool_to_quant (PEx x b) =
   QEx x (pseudoBool_to_quant b)) ∧
  (pseudoBool_to_quant (PLeastOne []) = QFalse) ∧
  (pseudoBool_to_quant (PLeastOne (b::bs)) =
   QOr (pseudoBool_to_quant b) (pseudoBool_to_quant (PLeastOne bs))) ∧
  (pseudoBool_to_quant (PMostOne bs) =
     most_one_to_quant (MAP pseudoBool_to_quant bs)) ∧
  (pseudoBool_to_quant (PExactlyOne bs) =
   QAnd
   (pseudoBool_to_quant (PLeastOne bs))
   (pseudoBool_to_quant (PMostOne bs)))
Termination
  WF_REL_TAC ‘measure pseudoBool_size'’
  >> rw[pseudoBool_size']
  >> Induct_on ‘bs’
  >> rw[pseudoBool_size']
  >> gs[]
End

Definition pseudoBool_to_cnf_def:
  pseudoBool_to_cnf b = boolExp_to_cnf (quant_to_boolExp (pseudoBool_to_quant b))
End


(* ----------------------- Theorems ------------------------------------ *)

Theorem eval_quant_update_ignore:
  ∀ b w n v v'.
    eval_quant w⦇n ↦ v⦈ (replace_name_quant n v' b) ⇔
    eval_quant w (replace_name_quant n v' b)
Proof
  Induct
  >> rw[replace_name_quant_def, eval_quant_def, eval_literal_def]
  >- (Cases_on ‘v'’
      >> rw[replace_name_quant_def, eval_quant_def,
            eval_literal_def])
  >- (Cases_on ‘v'’
      >> rw[replace_name_quant_def, eval_quant_def,
            eval_literal_def])
  >- (Cases_on ‘s’
      >> rw[replace_name_quant_def, eval_quant_def,
            eval_literal_def, APPLY_UPDATE_THM])
  >> metis_tac[UPDATE_COMMUTES]
QED

Theorem replace_preserves_sat:
 ∀ b x v w. eval_quant w⦇x ↦ v⦈ b ⇔ eval_quant w (replace_name_quant x v b)
Proof
  Induct
  >> rw[eval_quant_def, replace_name_quant_def, eval_literal_def,
        APPLY_UPDATE_THM, eval_quant_update_ignore]
  >- (Cases_on‘v’
      >> EVAL_TAC)
  >- (Cases_on‘v’
      >> EVAL_TAC)
  >- (Cases_on‘s’
      >> gs[])
  >> metis_tac[UPDATE_COMMUTES]
QED

Theorem quant_to_boolExp_preserves_sat:
  ∀b. eval_quant w b = eval_boolExp w (quant_to_boolExp b)
Proof
  ho_match_mp_tac quant_to_boolExp_ind
  >> rw[replace_name_quant_def, eval_quant_def,
        quant_to_boolExp_def, eval_boolExp_def, replace_preserves_sat]
  >- (eq_tac >> rw[]
      >> gvs[]
      >> Cases_on‘v’
      >> gs[])
  >- (eq_tac >> rw[]
      >- (Cases_on ‘v’ >> gvs[])
      >> metis_tac[])
QED

Theorem mOne_first_false:
  ∀ w h bs.
    ¬ eval_quant w (pseudoBool_to_quant h) ⇒
    (eval_quant w (pseudoBool_to_quant (PMostOne bs)) ⇔
       eval_quant w (pseudoBool_to_quant (PMostOne (h::bs))))
Proof
  rw[pseudoBool_to_quant_def, most_one_to_quant_def, eval_quant_def]
QED

Theorem all_false:
  ∀ bs w.
    (∀ b. MEM b bs ⇒
          (eval_quant w (pseudoBool_to_quant b) ⇔
             eval_pseudoBool w b)) ⇒
    (eval_quant w (none_of_list_to_quant (
                    MAP pseudoBool_to_quant bs))
     ⇔
       sum_bools (MAP (eval_pseudoBool w) bs) = 0)
Proof
 Induct
  >- gs[pseudoBool_to_quant_def, none_of_list_to_quant_def,
        eval_quant_def, eval_pseudoBool_def, sum_bools_def]
  >> rw[sum_bools_def]
  >> Cases_on ‘eval_pseudoBool w h’
  >> fs[sum_bools_def, none_of_list_to_quant_def, eval_quant_def]
QED

Theorem pseudoBool_to_quant_preserves_sat:
  ∀b w. eval_pseudoBool w b = eval_quant w (pseudoBool_to_quant b)
Proof
  ho_match_mp_tac pseudoBool_to_quant_ind
  >> rw[]
  >> TRY (rw[eval_quant_def, pseudoBool_to_quant_def,
             eval_pseudoBool_def, eval_literal_def,
             sum_bools_def, most_one_to_quant_def,
             none_of_list_to_quant_def]
    >> NO_TAC)
  (* PLeastOne *)
  >- (Cases_on ‘eval_quant w (pseudoBool_to_quant b)’
      >> gs[eval_pseudoBool_def, sum_bools_def,
            pseudoBool_to_quant_def, eval_quant_def])
  (* PMostOne *)
  >- (Induct_on ‘bs’
      >- rw[sum_bools_def, pseudoBool_to_quant_def,
            most_one_to_quant_def, eval_quant_def, eval_pseudoBool_def]
      >> rw[eval_pseudoBool_def]
      >> Cases_on ‘eval_quant w (pseudoBool_to_quant h)’
      >- (fs[sum_bools_def, pseudoBool_to_quant_def,
             most_one_to_quant_def, eval_quant_def,
             arithmeticTheory.LESS_OR_EQ]
          >> eq_tac >> rw[]
          >- metis_tac[all_false]
          >> fs[eval_pseudoBool_def, pseudoBool_to_quant_def]
          >> metis_tac[all_false])
      >> fs[sum_bools_def]
      >> ‘eval_pseudoBool w (PMostOne bs) ⇔
            eval_quant w (pseudoBool_to_quant (PMostOne (h::bs)))’
        suffices_by fs[eval_pseudoBool_def]
      >> fs[mOne_first_false])
  (* PExactlyOne *)
  >> gvs[pseudoBool_to_quant_def, eval_quant_def, eval_pseudoBool_def,
         EQ_IMP_THM, EQ_LESS_EQ, GREATER_EQ]
QED

Definition pseudoBool_to_assignment_def:
  pseudoBool_to_assignment w b =
  boolExp_to_assignment w (quant_to_boolExp (pseudoBool_to_quant b))
End

Theorem pseudoBool_to_cnf_preserves_sat:
  ∀ b w.
    eval_pseudoBool w b ⇔
      eval_cnf
      (pseudoBool_to_assignment w b)
      (pseudoBool_to_cnf b)
Proof
  gs[pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat,
     pseudoBool_to_cnf_def, pseudoBool_to_assignment_def,
     boolExp_to_cnf_preserves_sat]
QED

Theorem pseudoBool_to_cnf_imp_sat:
  eval_cnf w (pseudoBool_to_cnf b) ⇒
  eval_pseudoBool w b
Proof
  rw [pseudoBool_to_cnf_def]
  \\ imp_res_tac boolExp_to_cnf_imp_sat
  \\ fs [pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat]
QED

Theorem pseudoBool_to_cnf_preserves_unsat:
  unsat_pseudoBool b ⇔ unsat_cnf (pseudoBool_to_cnf b)
Proof
  fs [unsat_pseudoBool_def,pseudoBool_to_cnf_def,
      GSYM boolExp_to_cnf_preserves_unsat, unsat_boolExp_def,
      pseudoBool_to_quant_preserves_sat, quant_to_boolExp_preserves_sat]
QED

