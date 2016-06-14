open preamble closLangTheory;

val _ = new_theory"clos_number";

(* add fresh code locations *)

val renumber_code_locs_def = tDefine "renumber_code_locs" `
  (renumber_code_locs_list n [] = (n,[])) /\
  (renumber_code_locs_list n (x::xs) =
     let (n,x) = renumber_code_locs n x in
     let (n,xs) = renumber_code_locs_list n xs in
     (n, x::xs)) /\
  (renumber_code_locs n (Var v) = (n,(Var v))) /\
  (renumber_code_locs n (If x1 x2 x3) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs n x2 in
     let (n,x3) = renumber_code_locs n x3 in
       (n,If x1 x2 x3)) /\
  (renumber_code_locs n (Let xs x2) =
     let (n,xs) = renumber_code_locs_list n xs in
     let (n,x2) = renumber_code_locs n x2 in
       (n,Let xs x2)) /\
  (renumber_code_locs n (Raise x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n,Raise x1)) /\
  (renumber_code_locs n (Tick x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n,Tick x1)) /\
  (renumber_code_locs n (Op op xs) =
     let (n,xs) = renumber_code_locs_list n xs in
       (n,Op op xs)) /\
  (renumber_code_locs n (App loc_opt x1 x2) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs_list n x2 in
       (n,App loc_opt x1 x2)) /\
  (renumber_code_locs n (Fn loc vs num_args x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n+2,Fn (SOME n) vs num_args x1)) /\
  (renumber_code_locs n (Letrec loc vs fns x1) =
     let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
     let (n,x1) = renumber_code_locs (m+2*LENGTH fns') x1 in
     (n,Letrec (SOME m) vs (ZIP (MAP FST fns, fns')) x1)) /\
  (renumber_code_locs n (Handle x1 x2) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs n x2 in
     (n,Handle x1 x2)) /\
  (renumber_code_locs n (Call dest xs) =
     let (n,xs) = renumber_code_locs_list n xs in
     (n,Call dest xs))`
 (WF_REL_TAC `inv_image $< (λx. case x of INL p => exp3_size (SND p) | INR p => exp_size (SND p))` >>
 rw [] >>
 TRY decide_tac >>
 Induct_on `fns` >>
 srw_tac [ARITH_ss] [exp_size_def] >>
 Cases_on `h` >>
 rw [exp_size_def] >>
 decide_tac);

val renumber_code_locs_ind = theorem"renumber_code_locs_ind";

val renumber_code_locs_length = store_thm("renumber_code_locs_length",
  ``(∀x y. LENGTH (SND (renumber_code_locs_list x y)) = LENGTH y) ∧
    (∀(x:num)(y:closLang$exp). T)``,
    ho_match_mp_tac renumber_code_locs_ind >>
    simp[renumber_code_locs_def,UNCURRY] >> rw[] >>
    METIS_TAC[PAIR,FST,SND]);

val _ = export_theory()
