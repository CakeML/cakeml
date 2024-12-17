(*
  Code generator for Scheme to CakeML compiler
*)
open preamble;
open astTheory;
open scheme_astTheory;

val _ = new_theory "scheme_to_cake";

Definition cake_print_def:
  cake_print e =
    (* val _ = print e; *)
    [Dlet unknown_loc Pany (App Opapp [Var (Short "print"); e])]
End

Definition codegen_def:
  (codegen (Print s)) : string + dec list =
    INR (cake_print (Lit (StrLit (explode s))))
End

val _ = export_theory();
