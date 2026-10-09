(*
  Encoding from Boolean expressions to CNF.
*)
Theory old_boolExpToCnf
Ancestors
  misc ASCIInumbers satCnf
Libs
  preamble


(* ----------------------- Types --------------------------------------- *)

Datatype:
  nnf =
    NnfTrue
  | NnfFalse
  | NnfLit literal
  | NnfAnd nnf nnf
  | NnfOr nnf nnf
End

Datatype:
  noImp =
    NoImpTrue
  | NoImpFalse
  | NoImpLit literal
  | NoImpNot noImp
  | NoImpAnd noImp noImp
  | NoImpOr noImp noImp
End

Datatype:
  boolExp =
    True
  | False
  | Lit literal
  | Not boolExp
  | And boolExp boolExp
  | Or boolExp boolExp
  | Impl boolExp boolExp
  | Iff boolExp boolExp
End

(* ----------------------- Satisfiability ------------------------------ *)

Definition eval_nnf_def:
  (eval_nnf (w:num assignment) NnfTrue = T) ∧
  (eval_nnf w NnfFalse = F) ∧
  (eval_nnf w (NnfLit l) = satisfies_lit w l) ∧
  (eval_nnf w (NnfAnd nnf1 nnf2) =
   (eval_nnf w nnf1 ∧ eval_nnf w nnf2)) ∧
  (eval_nnf w (NnfOr nnf1 nnf2) =
   (eval_nnf w nnf1 ∨ eval_nnf w nnf2))
End

Definition eval_noImp_def:
  (eval_noImp (w:num assignment) NoImpTrue = T) ∧
  (eval_noImp w NoImpFalse = F) ∧
  (eval_noImp w (NoImpLit l) =
   satisfies_lit w l) ∧
  (eval_noImp w (NoImpNot b) =
   ¬ (eval_noImp w b)) ∧
  (eval_noImp w (NoImpAnd b1 b2) =
   (eval_noImp w b1 ∧ eval_noImp w b2)) ∧
  (eval_noImp w (NoImpOr b1 b2) =
   (eval_noImp w b1 ∨ eval_noImp w b2))
End

Definition eval_boolExp_def:
  (eval_boolExp (w:num assignment) True = T) ∧
  (eval_boolExp w False = F) ∧
  (eval_boolExp w (Lit l) = satisfies_lit w l) ∧
  (eval_boolExp w (Not b) = ¬ (eval_boolExp w b)) ∧
  (eval_boolExp w (And b1 b2) =
   (eval_boolExp w b1 ∧ eval_boolExp w b2)) ∧
  (eval_boolExp w (Or b1 b2) =
   (eval_boolExp w b1 ∨ eval_boolExp w b2)) ∧
  (eval_boolExp w (Impl b1 b2) =
   (eval_boolExp w b1 ⇒ eval_boolExp w b2)) ∧
  (eval_boolExp w (Iff b1 b2) =
   (eval_boolExp w b1 ⇔ eval_boolExp w b2))
End

Definition unsat_boolExp_def:
  unsat_boolExp b = ∀w. ¬ eval_boolExp w b
End

(* ----------------- Simplification functions -------------------------- *)

Definition distr_def:
  distr a b = FLAT (MAP (λc. MAP (λd. c ++ d) b) a)
End

Definition nnf_to_cnf_def:
  (nnf_to_cnf NnfTrue = CnfEmpty) ∧
  (nnf_to_cnf NnfFalse = CnfClause ClauseEmpty) ∧
  (nnf_to_cnf (NnfLit l) = CnfClause (ClauseLit l)) ∧
  (nnf_to_cnf (NnfAnd a b) = CnfAnd (nnf_to_cnf a) (nnf_to_cnf b)) ∧
  (nnf_to_cnf (NnfOr a b) = distr (nnf_to_cnf a) (nnf_to_cnf b))
End

Definition noImp_to_nnf_def:
  (noImp_to_nnf NoImpTrue = NnfTrue) ∧
  (noImp_to_nnf NoImpFalse = NnfFalse) ∧
  (noImp_to_nnf (NoImpLit l) = NnfLit l) ∧
  (noImp_to_nnf (NoImpNot NoImpTrue) = NnfFalse) ∧
  (noImp_to_nnf (NoImpNot NoImpFalse) = NnfTrue) ∧
  (noImp_to_nnf (NoImpNot (NoImpLit l)) =
   NnfLit (negate_literal l)) ∧
  (noImp_to_nnf (NoImpNot (NoImpNot b)) = noImp_to_nnf b) ∧
  (noImp_to_nnf (NoImpNot (NoImpAnd b1 b2)) =
   NnfOr
   (noImp_to_nnf (NoImpNot b1))
   (noImp_to_nnf (NoImpNot b2))) ∧
  (noImp_to_nnf (NoImpNot (NoImpOr b1 b2)) =
   NnfAnd
   (noImp_to_nnf (NoImpNot b1))
   (noImp_to_nnf (NoImpNot b2))) ∧
  (noImp_to_nnf (NoImpAnd b1 b2) =
   NnfAnd (noImp_to_nnf b1) (noImp_to_nnf b2)) ∧
  (noImp_to_nnf (NoImpOr b1 b2) =
   NnfOr (noImp_to_nnf b1) (noImp_to_nnf b2))
End

Definition boolExp_to_noImp_def:
  (boolExp_to_noImp True = NoImpTrue) ∧
  (boolExp_to_noImp False = NoImpFalse) ∧
  (boolExp_to_noImp (Lit l) = NoImpLit l) ∧
  (boolExp_to_noImp (Not b) =
   case (boolExp_to_noImp b) of
     NoImpTrue => NoImpFalse
   | NoImpFalse => NoImpTrue
   | b' => (NoImpNot b')) ∧
  (boolExp_to_noImp (And b1 b2) =
   case (boolExp_to_noImp b1, boolExp_to_noImp b2) of
     (NoImpFalse, _) => NoImpFalse
   | (NoImpTrue, b2') => b2'
   | (_, NoImpFalse) => NoImpFalse
   | (b1', NoImpTrue) => b1'
   | (b1', b2') => (NoImpAnd b1' b2')) ∧
  (boolExp_to_noImp (Or b1 b2) =
   case (boolExp_to_noImp b1, boolExp_to_noImp b2) of
     (NoImpTrue, _) => NoImpTrue
   | (NoImpFalse, b2') => b2'
   | (_, NoImpTrue) => NoImpTrue
   | (b1', NoImpFalse) => b1'
   | (b1', b2') => (NoImpOr b1' b2')) ∧
  (boolExp_to_noImp (Impl b1 b2) =
   case (boolExp_to_noImp b1, boolExp_to_noImp b2) of
     (NoImpFalse, _) => NoImpTrue
   | (NoImpTrue, b2') => b2'
   | (_, NoImpTrue) => NoImpTrue
   | (b1', NoImpFalse) => (NoImpNot b1')
   | (b1', b2') => (NoImpOr (NoImpNot b1') b2')) ∧
  (boolExp_to_noImp (Iff b1 b2) =
   case (boolExp_to_noImp b1, boolExp_to_noImp b2) of
     (NoImpTrue, NoImpTrue) => NoImpTrue
   | (NoImpFalse, NoImpFalse) => NoImpTrue
   | (NoImpTrue, NoImpFalse) => NoImpFalse
   | (NoImpFalse, NoImpTrue) => NoImpFalse
   | (NoImpTrue, b2') => b2'
   | (NoImpFalse, b2') => (NoImpNot b2')
   | (b1', NoImpTrue) => b1'
   | (b1', NoImpFalse) => (NoImpNot b1')
   | (b1', b2') => NoImpOr
                     (NoImpAnd b1' b2')
                     (NoImpAnd (NoImpNot b1') (NoImpNot b2')))
End

Definition boolExp_to_cnf_def:
  boolExp_to_cnf b = nnf_to_cnf (noImp_to_nnf (boolExp_to_noImp b))
End

(* ----------------------- Theorems ------------------------------------ *)

Theorem mem_distr:
  MEM c (distr b1 b2) ⇔
    ∃c1 c2. MEM c1 b1 ∧ MEM c2 b2 ∧ c = c1 ++ c2
Proof
  simp[distr_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem distr_preserves_sat:
  ∀ b1 b2.
    satisfies_cnf w (set (distr b1 b2)) ⇔
    (satisfies_cnf w (set b1) ∨ satisfies_cnf w (set b2))
Proof
  simp[cnfTheory.satisfies_cnf_def,
       cnfTheory.satisfies_fml_gen_def,
       mem_distr, satisfies_clause_append, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem nnf_to_cnf_preserves_sat:
  eval_nnf w b = satisfies_cnf w (set (nnf_to_cnf b))
Proof
  Induct_on ‘b’
  >> simp[eval_nnf_def, nnf_to_cnf_def,
          satisfies_cnf_constructors, satisfies_clause_constructors,
          distr_preserves_sat]
QED

Theorem negate_literal_thm:
  satisfies_lit w (negate_literal l) ⇔ ¬ satisfies_lit w l
Proof
  Cases_on ‘l’
  >> rw[negate_literal_def, cnfTheory.satisfies_lit_def]
QED

Theorem noImpNot_thm:
  ∀ b.
    eval_nnf w (noImp_to_nnf (NoImpNot b)) ⇔
      ¬ eval_nnf w (noImp_to_nnf b)
Proof
  Induct
  >> rw[noImp_to_nnf_def, eval_nnf_def, negate_literal_thm]
QED

Theorem noImp_to_nnf_preserves_sat:
  eval_noImp w b = eval_nnf w (noImp_to_nnf b)
Proof
  Induct_on ‘b’
  >> rw[eval_noImp_def,
        noImp_to_nnf_def,
        eval_nnf_def,
        noImpNot_thm]
QED


Theorem boolExp_to_noImp_preserves_sat:
  eval_boolExp w b = eval_noImp w (boolExp_to_noImp b)
Proof
  Induct_on ‘b’
  >> Cases_on‘boolExp_to_noImp b’
  >> Cases_on‘boolExp_to_noImp b'’
  >> rw[eval_boolExp_def,
        boolExp_to_noImp_def,
        eval_noImp_def]
  >> metis_tac[]
QED

Theorem boolExp_to_cnf_preserves_sat:
  eval_boolExp w b = satisfies_cnf w (set (boolExp_to_cnf b))
Proof
  rw[boolExp_to_noImp_preserves_sat,
     noImp_to_nnf_preserves_sat,
     nnf_to_cnf_preserves_sat,
     boolExp_to_cnf_def]
QED


(* --------------------- Pretty printing ------------------------- *)

Definition lit_to_str_def:
  lit_to_str (Pos l) = "b" ++ num_to_dec_string l ∧
  lit_to_str (Neg l) = "~b" ++ num_to_dec_string l
End

Definition clause_to_str_def:
  clause_to_str [] = "False" ∧
  clause_to_str (l::ls) =
    if NULL ls then lit_to_str l
    else lit_to_str l ++ " \\/ " ++ clause_to_str ls
End

Definition cnf_to_str_def:
  cnf_to_str [] = "True" ∧
  cnf_to_str (c::cs) =
    if NULL cs then clause_to_str c
    else clause_to_str c ++ " /\\ " ++ cnf_to_str cs
End

Theorem example1 =
        EVAL “cnf_to_str
              (boolExp_to_cnf
               (And
                (Not (And
                      (Lit (Pos 2))
                      (Lit (Neg 1))))
                (Or
                 (Lit (Pos 0))
                 (Lit (Neg 1)))))”;

Theorem example2 =
        EVAL “cnf_to_str
              (boolExp_to_cnf
               (And
                (Lit (Pos 0))
                (And
                 (Lit (Pos 2))
                 (And
                  (Lit (Neg 1))
                  (Lit (Neg 3))))))”;

Theorem example3 =
        EVAL “(boolExp_to_cnf
               (Or
                (Lit (Pos 0))
                (Or
                 (Lit (Pos 2))
                 (Or
                  (Lit (Neg 1))
                  (Lit (Neg 3))))))”;
