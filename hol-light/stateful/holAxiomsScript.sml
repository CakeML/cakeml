open HolKernel boolLib bossLib lcsymtacs
open holBoolTheory
val _ = new_theory"holAxioms"

val _ = Parse.temp_overload_on("A",``Tyvar "A"``)
val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.temp_overload_on("x",``Var "x" A``)
val _ = Parse.temp_overload_on("Absx",``Abs "x" A``)
val _ = Parse.temp_overload_on("g",``Var "f" (Fun A B)``)

(* ETA_AX *)
val mk_eta_ctxt_def = Define`
  mk_eta_ctxt ctxt = NewAxiom ((Absx (Comb g x)) === g)::ctxt`

val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty)``)
val _ = Parse.temp_overload_on("P",``Var "P" (Fun A Bool)``)

(* SELECT_AX *)
val mk_select_ctxt_def = Define`
  mk_select_ctxt ctxt =
    NewAxiom (Comb P (Comb (Select A) P)) ::
    NewConst "@" (Fun (Fun A Bool) A) ::
    ctxt`

val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.overload_on("One_One",``λf. Comb (Const "ONE_ONE" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Onto",``λf. Comb (Const "ONTO" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Ind",``Tyapp "ind" []``)

val _ = Parse.temp_overload_on("EXx",``Exists "x" A``)
val _ = Parse.temp_overload_on("Absg",``Abs "f" (Fun A B)``)
val _ = Parse.temp_overload_on("x1",``Var "x1" A``)
val _ = Parse.temp_overload_on("FAx1",``Forall "x1" A``)
val _ = Parse.temp_overload_on("x2",``Var "x2" A``)
val _ = Parse.temp_overload_on("FAx2",``Forall "x2" A``)
val _ = Parse.temp_overload_on("y",``Var "y" B``)
val _ = Parse.temp_overload_on("FAy",``Forall "y" B``)
val _ = Parse.temp_overload_on("h",``Var "f" (Fun A B)``)
val _ = Parse.temp_overload_on("Exh",``Exists "f" (Fun Ind Ind)``)

 (* INFINITY_AX *)
val mk_inf_ctxt_def = Define`
  mk_inf_ctxt ctxt =
    NewAxiom (Exh (And (One_One h) (Not (Onto h)))) ::
    NewType "ind" 0 ::
    ConstDef "ONTO" (Absg (FAy (EXx (y === Comb g x)))) ::
    ConstDef "ONE_ONE"
      (Absg (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))) ::
    ctxt`

val _ = export_theory()
