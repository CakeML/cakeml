load "ml_progTheory";
open HolKernel boolLib bossLib Parse;

val fs = TypeBase.fields_of ``:env_entry``;
val _ = List.app (fn (nm, info) =>
  let val fu = #fupd info
      val acc = #accessor info
      val fu_const = repeat rator fu
      val acc_const = repeat rator acc
  in print ("field: " ^ nm);
     (case Lib.total dest_thy_const fu_const of
         SOME {Name, Thy, ...} => print ("  fupd=" ^ Thy ^ "$" ^ Name) | _ => ());
     (case Lib.total dest_thy_const acc_const of
         SOME {Name, Thy, ...} => print ("  acc=" ^ Thy ^ "$" ^ Name) | _ => ());
     print "\n"
  end) fs;

(* ARB term *)
val arb = prim_mk_const {Name = "ARB", Thy = "bool"};
val arb_tm = inst [alpha |-> mk_type ("env_entry", [])] arb;
val _ = print "ARB inst: "; val _ = print_term arb_tm; val _ = print "\n";
