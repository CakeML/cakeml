load "ml_progLib";
open HolKernel boolLib bossLib Parse ml_progLib;

(* What does mk_sc_entry_tm produce? Compare to <|..|> form. *)
val c = ``(1n, TypeStamp (strlit "Some") 2)``;
(* mk_sc_entry_tm is internal — replicate its definition here. *)
val env_entry_sc_fupd =
    prim_mk_const {Name = "recordtype.env_entry.seldef.sc_fupd",
                   Thy = "ml_prog"};
val empty_entry_const =
    prim_mk_const {Name = "empty_entry", Thy = "ml_prog"};
val K_const = combinSyntax.K_tm;
val opt_ty = type_of (optionSyntax.mk_some c);
val k_inst = inst [alpha |-> opt_ty, beta |-> opt_ty] K_const;
val k_v = mk_comb (k_inst, optionSyntax.mk_some c);
val lib_form = list_mk_comb (env_entry_sc_fupd, [k_v, empty_entry_const]);
val lit_form = ``<| sv:=NONE; sc:=SOME (1n, TypeStamp (strlit "Some") 2);
                    mv:=NONE; mc:=NONE |> : env_entry``;
val _ = print "lib form:  "; val _ = print_term lib_form; val _ = print "\n";
val _ = print "lit form:  "; val _ = print_term lit_form; val _ = print "\n";
val _ = print ("aconv: " ^ Bool.toString (aconv lib_form lit_form) ^ "\n");
val _ = print ("lib head: " ^ (fst (dest_const (fst (strip_comb lib_form)))
                               handle _ => "(non-const)") ^ "\n");
val _ = print ("lit head: " ^ (fst (dest_const (fst (strip_comb lit_form)))
                               handle _ => "(non-const)") ^ "\n");
