open HolKernel boolLib bossLib lcsymtacs
open Defn intLang2Theory intLang4Theory
val _ = new_theory"toIntLang4Proof"

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (exp_to_i4_def, exp_to_i4_ind) =
  tprove_no_defn ((exp_to_i4_def, exp_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,e) => exp_i2_size e
                                        | INR (INL (bvs,es)) => exp_i26_size es
                                        | INR (INR (INL (bvs,funs))) => exp_i21_size funs
                                        | INR (INR (INR (bvs,pes))) => exp_i23_size pes)`);
val _ = register "exp_to_i4" exp_to_i4_def exp_to_i4_ind;

val (row_to_i4_def, row_to_i4_ind) =
  tprove_no_defn ((row_to_i4_def, row_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,p) => pat_i2_size p
                                        | INR (bvs,n,k,ps) => pat_i21_size ps)`);
val _ = register "row_to_i4" row_to_i4_def row_to_i4_ind;

val (Let_Els_i4_def, Let_Els_i4_ind) =
  tprove_no_defn ((Let_Els_i4_def, Let_Els_i4_ind),
  WF_REL_TAC `measure (FST o SND)`);
val _ = register "Let_els_i4" Let_Els_i4_def Let_Els_i4_ind;

(*
(* 0 = SOME, 1 = NONE, 2 = INL, 3 = INR, 4 = NIL, 5 = CONS, 6 = PAIR *)

(*
case x of
  (SOME (INL n) :: ys) => (* something with n ys *) ...
| [NONE] => ...
| ... =>
*)

val th =
EVAL
``exp_to_i4 [SOME "y";SOME "x"]
  (Mat_i2 (Var_local_i2 "x")
    [((Pcon_i2 5 [Pcon_i2 0 [Pcon_i2 2 [Pvar_i2 "n"]]; Pvar_i2 "ys"])
     ,(Con_i2 6 [Var_local_i2 "n"; Var_local_i2 "ys"])
     );
     ((Pcon_i2 5 [Pcon_i2 1 []; Pcon_i2 4 []])
     ,(Con_i2 6 [Lit_i2 (IntLit 0); Var_local_i2 "y"])
     )]
  )``

val _ = Parse.overload_on("COND",``If_i4``)
val _ = Parse.overload_on("tageq", ``λn v. Uapp_i4 (Tag_eq_i4 n) (Var_local_i4 v)``)
val _ = Parse.overload_on("isSOME", ``λv. Uapp_i4 (Tag_eq_i4 0) (Var_local_i4 v)``)
val _ = Parse.overload_on("isNONE", ``λv. Uapp_i4 (Tag_eq_i4 1) (Var_local_i4 v)``)
val _ = Parse.overload_on("isINL", ``λv. Uapp_i4 (Tag_eq_i4 2) (Var_local_i4 v)``)
val _ = Parse.overload_on("isNIL", ``λv. Uapp_i4 (Tag_eq_i4 4) (Var_local_i4 v)``)
val _ = Parse.overload_on("isCONS", ``λv. Uapp_i4 (Tag_eq_i4 5) (Var_local_i4 v)``)
val _ = Parse.overload_on("el", ``λn v. Uapp_i4 (El_i4 n) (Var_local_i4 v)``)
val _ = Parse.overload_on("true", ``Lit_i4 (Bool T)``)
val _ = Parse.overload_on("false", ``Lit_i4 (Bool F)``)
val _ = Parse.overload_on("pair", ``λx y. Con_i4 6 [x;y]``)
val tm = rhs(concl th)

*)

val _ = export_theory()
