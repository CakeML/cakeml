(*
 * example of acyclic theory
 *)
open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory
     holSyntaxExtraTheory holBoolSyntaxTheory holAxiomsSyntaxTheory
     holExtensionTheory holBoolTheory holSyntaxCyclicityTheory

val _ = new_theory"holSyntaxCyclicityExample";

Overload Fun = ``λs t. Tyapp «fun» [s;t]``
Overload Bool = ``Tyapp «bool» []``

Definition hol_ctxt_dep_def:
  hol_ctxt_dep = [
  (INL (Fun (Tyvar «A» ) (Tyvar «B» )),INL (Tyvar «A» ));
  (INL (Fun (Tyvar «A» ) (Tyvar «B» )),INL (Tyvar «B» ));
  (INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INL (Tyvar «A» ));
  (INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)),INR (Const «T» Bool));
  (INR (Const «/\\» (Fun Bool (Fun Bool Bool))),INR (Const «T» Bool));
  (INR (Const «==>» (Fun Bool (Fun Bool Bool))), INR (Const «/\\» (Fun Bool (Fun Bool Bool))));
  (INR (Const «=» (Fun (Tyvar «A» ) (Fun (Tyvar «A» ) Bool)) ),INL (Tyvar «A» ));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INL (Tyvar «A» ));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «@» (Fun (Fun (Tyvar «A» ) Bool) (Tyvar «A» )) ),INL (Tyvar «A» ));
  (INR (Const «F» Bool),INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «A» ));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «B» ));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «A»));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «B»));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «!» (Fun (Fun (Tyvar «B» ) Bool) Bool)));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «\\/» (Fun Bool (Fun Bool Bool))), INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «\\/» (Fun Bool (Fun Bool Bool))), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «~» (Fun Bool Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «~» (Fun Bool Bool)),INR (Const «F» Bool))
  ]
End

(* write dependency relation to file *)

fun write_hol_string_to_file filename tm =
  let
    val f = TextIO.openOut filename
    val s = tm |> Hol_pp.term_to_string
    val _ = TextIO.output (f,s)
    val _ = TextIO.closeOut f
  in () end

val _ = temp_clear_overloads_on "Equal" ;
val _ = temp_clear_overloads_on "Select" ;
val _ = write_hol_string_to_file "hol_ctxt_dep.txt" (EVAL ``hol_ctxt_dep`` |> concl |> rand) ;

Theorem dependency_hol_ctxt_eq:
  set (MAP ((λf. (f ## f)) (LR_TYPE_SUBST [(Tyvar «B», Tyvar «aa»);(Tyvar «A»,Tyvar «a»)]))
  (dependency_compute hol_ctxt)) = set hol_ctxt_dep
Proof
  fs[dependency_compute_def,hol_ctxt_def,dependency_cases,mk_infinity_ctxt_def,
    mk_bool_ctxt_def,mk_eta_ctxt_def,mk_select_ctxt_def,finite_hol_ctxt_def,
    init_ctxt_def,TrueDef_def,wellformed_compute_def,allCInsts_def,typeof_def,
    equation_def,ImpliesDef_def,is_fun_def,REPLICATE,Excl"TYPE_SUBST_def",
    TrueDef_def,AndDef_def,ForallDef_def,ExistsDef_def,FalseDef_def,NotDef_def,
    cj 2 TYPE_SUBST_def,cj 2 $ GSYM is_instance_simps,PULL_EXISTS,PAIR_MAP]
  >> EVAL_TAC
  >> fs[cj 2 TYPE_SUBST_def,cj 2 $ GSYM is_instance_simps,Excl"TYPE_SUBST_def",LR_TYPE_SUBST_cases]
  >> EVAL_TAC
QED

Theorem dependency_hol_ctxt_eq =
  REWRITE_RULE[hol_ctxt_dep_def] dependency_hol_ctxt_eq

Theorem dep_steps_dep_thm = time EVAL ``dep_steps hol_ctxt_dep 4 hol_ctxt_dep`` ;

Theorem terminating_dep:
  terminating $ TC $ subst_clos $ CURRY $ set hol_ctxt_dep
Proof
  irule dep_steps_acyclic_sound'
  >> conj_asm1_tac
  >- (
    EVAL_TAC >> fs[LIST_TO_SET,DISJ_IMP_THM]
    >> EVAL_TAC >> fs[]
  )
  >> conj_asm1_tac >- EVAL_TAC
  >> conj_tac >- (qexists_tac `3` >> fs[dep_steps_dep_thm])
  >> fs[composable_len_ONE_compute]
  >> EVAL_TAC
QED

val _ = export_theory();
