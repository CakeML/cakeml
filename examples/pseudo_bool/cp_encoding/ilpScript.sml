(*
  An ILP-style language designed as an intermediate layer for CP encodings
*)
open preamble mlintTheory pbcTheory cpTheory;

val _ = new_theory "ilp";

(*
  This "ILP"-style intermediate language is designed for convenience of
  verified encodings from CP (and then to PB).

  It is NOT intended for use as a standalone and NOT a pure ILP formalization.
*)

Type ilin_term = ``:(int # 'a) list ``

(* A constraint consists of two lists (c_i, X_i), (d_i, l_i) and a RHS *)
Type iconstraint = ``:'a ilin_term # 'b lin_term # int``

(* An assignment assigns both the integer and boolean variables *)
Type iassignment = ``:('a -> int) # ('b -> bool)``;

Definition eval_iterm_def[simp]:
  eval_iterm wi (c:int,X) = c * wi X
End

Definition eval_ilin_term_def:
  eval_ilin_term wi (xs:(int # 'a) list) = iSUM (MAP (eval_iterm wi) xs)
End

Definition iconstraint_sem_def:
  iconstraint_sem ((is,bs,c):('a,'b) iconstraint)
    ((wi,wb):('a,'b) iassignment) ⇔
    eval_ilin_term wi is + eval_lin_term wb bs ≥ c
End

(* normalize away varc *)
Definition norm_varcs_aux_def:
  (norm_varcs_aux [] res = res) ∧
  (norm_varcs_aux (vc::vs) (xs,acc) =
    case (vc:'a varc) of
      INL v => norm_varcs_aux vs ((1i,v)::xs,acc)
    | INR c => norm_varcs_aux vs (xs,c+acc))
End

Theorem norm_varcs_aux_sound:
  ∀vcs xs acc xs' acc'.
  norm_varcs_aux vcs (xs,acc) = (xs',acc') ⇒
  iSUM (MAP (varc wi) vcs) + eval_ilin_term wi xs + acc =
  eval_ilin_term wi xs' + acc'
Proof
  Induct>>
  rw[norm_varcs_aux_def,iSUM_def,AllCaseEqs(),varc_def,norm_varcs_aux_def]>>
  fs[]>>
  first_x_assum drule>>
  rw[]>>
  fs[eval_ilin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition norm_varcs_def:
  norm_varcs vcs = norm_varcs_aux vcs ([],0)
End

Theorem norm_varcs_sound:
  norm_varcs vcs = (xs',acc') ⇒
  iSUM (MAP (varc wi) vcs) = eval_ilin_term wi xs' + acc'
Proof
  rw[norm_varcs_def]>>
  drule norm_varcs_aux_sound>>
  simp[eval_ilin_term_def,iSUM_def]
QED

val _ = export_theory();
