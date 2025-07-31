(*
  Encoding of n-queeens problem to cnf
*)
Theory nqueens
Ancestors
  misc boolExpToCnf quantifierExp cnf
Libs
  preamble


(* ---------------------------- Help functions ------------------------- *)

Definition get_rows_def:
  get_rows (n:num) =
  GENLIST (λ row. GENLIST (λ col. row * n + (col + 1)) n) n
End

Definition get_cols_def:
  get_cols (n:num) =
  GENLIST (λ col. GENLIST (λ row. row * n + (col + 1)) n) n
End

Definition get_element_def:
  get_element i j (xs: num list list) =
  case oEL i xs of
  | NONE => 0
  | SOME ys =>
      case oEL j ys of
      | NONE => 0
      | SOME y => y
End

Definition get_lr_diagonals_def:
  get_lr_diagonals (n:num) =
  let rows = get_rows n in
    let cols = get_cols n in
      nub ((GENLIST
            (λ i. GENLIST
                  (λ j. get_element j (i + j) rows) (n - i)) n) ++
           (GENLIST
            (λ i. GENLIST
                  (λ j. get_element j (i + j) cols) (n - i)) n))
End

Definition get_rl_diagonals_def:
  get_rl_diagonals (n:num) =
  let rows = get_rows n in
    let cols = get_cols n in
      nub ((GENLIST
            (λ i. GENLIST
                  (λ j. get_element j (n - 1 - (i + j)) rows) (n - i)) n) ++
           (GENLIST
            (λ i. GENLIST
                  (λ j. get_element (i + j) (n - 1 - j) rows) (n - i)) n))
End

Definition get_diagonals_def:
  get_diagonals (n:num) =
  get_lr_diagonals n ++ get_rl_diagonals n
End


(* ---------------------------- Evaluation ---------------------------- *)

Definition eval_nqueens_def:
  eval_nqueens (w:assignment) (n:num) =
  (EVERY (λ row. sum_bools (MAP w row) = 1) (get_rows n) ∧
   EVERY (λ col. sum_bools (MAP w col) ≤ 1) (get_cols n) ∧
   EVERY (λ diagonal. sum_bools (MAP w diagonal) ≤ 1) (get_diagonals n))
End


(* ---------------------------- Encoding ---------------------------- *)

Definition every_at_most_one_def:
  every_at_most_one [] = PTrue ∧
  every_at_most_one (x::xs) =
  PAnd (PMostOne (MAP (λ y. PLit (INL y)) x)) (every_at_most_one xs)
End

Definition every_at_least_one_def:
  every_at_least_one [] = PTrue ∧
  every_at_least_one (x::xs) =
  PAnd (PLeastOne (MAP (λ y. PLit (INL y)) x)) (every_at_least_one xs)
End

Definition nqueens_to_pseudoBool_def:
  nqueens_to_pseudoBool (n:num) =
  PAnd
  (every_at_most_one (get_rows n ++ get_cols n ++ get_diagonals n))
  (every_at_least_one (get_rows n))
End

Definition nqueens_to_cnf_def:
  nqueens_to_cnf (n:num) = pseudoBool_to_cnf (nqueens_to_pseudoBool n)
End


(* ---------------------------- Theorems ---------------------------- *)


Theorem eval_every_at_most_one_append:
  ∀ xs ys w.
    eval_pseudoBool w (every_at_most_one (xs ++ ys)) =
    (eval_pseudoBool w (every_at_most_one xs) ∧
     eval_pseudoBool w (every_at_most_one ys))
Proof
  Induct >> rw[]
  >> rw[every_at_most_one_def, eval_pseudoBool_def]
  >> metis_tac[]
QED

Theorem map_eval:
  ∀ xs w.
    MAP w xs =
    MAP (λ y. eval_pseudoBool w y) (MAP (λ x. PLit (INL x)) xs)
Proof
  Induct >> rw[]
  >> rw[eval_pseudoBool_def, eval_literal_def]
QED

Theorem eval_every_at_most_one:
  ∀ xs w.
    EVERY (λ x. sum_bools (MAP w x) ≤ 1) xs =
    eval_pseudoBool w (every_at_most_one xs)
Proof
  Induct >> rw[]
  >- rw[every_at_most_one_def, eval_pseudoBool_def]
  >> rw[every_at_most_one_def]
  >> rw[eval_pseudoBool_def]
  >> rw[map_eval]
QED

Theorem sum_bools_lemma:
  ∀ xs.
    sum_bools xs = 1 ⇔
      (sum_bools xs ≤ 1 ∧ sum_bools xs ≥ 1)
Proof
  Induct >> rw[]
QED

Theorem eval_every_exactly_one:
  ∀ xs w.
    EVERY (λ x. sum_bools (MAP w x) = 1) xs =
    (eval_pseudoBool w (every_at_most_one xs) ∧
     eval_pseudoBool w (every_at_least_one xs))
Proof
  Induct >> rw[]
  >- rw[every_at_most_one_def, eval_pseudoBool_def]
  >- rw[every_at_least_one_def, eval_pseudoBool_def]
  >> rw[every_at_most_one_def, every_at_least_one_def,
        map_eval, eval_pseudoBool_def]
  >> rw[sum_bools_lemma]
  >> metis_tac[]
QED

Theorem nqueens_to_pseudoBool_preserves_sat:
  ∀ n w.
    eval_nqueens w n =
    eval_pseudoBool w (nqueens_to_pseudoBool n)
Proof
  gs[eval_nqueens_def]
  >> gs[nqueens_to_pseudoBool_def]
  >> gs[eval_pseudoBool_def]
  >> gs[eval_every_at_most_one_append]
  >> gs[eval_every_at_most_one]
  >> gs[eval_every_exactly_one]
  >> metis_tac[]
QED

