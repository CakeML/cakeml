structure ioProgLib =
struct

open preamble
open ml_progLib ioProgTheory semanticsLib


val append_emp = Q.prove(
  `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT x) ==> app p fv xs (P * emp) (POSTv uv. (A uv) * (STDOUT x * emp))`,
  rw[set_sepTheory.SEP_CLAUSES]
);

fun mk_main_call s =
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;

val basis_ffi_tm =
  list_mk_comb(
    prim_mk_const{Thy="ioProg",Name="basis_ffi"},
    [mk_var("inp",stringSyntax.string_ty),
     mk_var("cls",listSyntax.mk_list_type(stringSyntax.string_ty))])

fun add_basis_proj spec =
  let val spec1 = HO_MATCH_MP append_emp spec handle HOL_ERR _ => spec in 
    spec1 |> Q.GEN`p` |> Q.ISPEC`(basis_proj1, basis_proj2):(string#string#string list) ffi_proj`
  end

fun ERR f s = mk_HOL_ERR"ioProgLib" f s 

(*
  - st is the ML prog state of the final desired program
  - name (string) is the name of the program's main function (unit->unit) 
  - spec is a theorem of the form
     |- app (basis_proj1, basis_proj2) main_v [Conv NONE []] P
          (POSTv uv. &UNIT_TYPE () uv * STDOUT x * Q)
    where main_v is the value corresponding to the main function
          P is the precondition
          x is the desired output
          Q is any remaining postconditions

    (add_basis_proj can turn an |- app p ... spec into the form above)
*)
fun call_thm st name spec =
  let 
    val ERR = ERR "call_thm"
    val th =
      call_main_thm_basis
        |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
        |> SPEC(stringSyntax.fromMLstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C MATCH_MP spec
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc
    val th = PURE_REWRITE_RULE[prog_rewrite] th
    val (mods_tm,types_tm) = th |> concl |> dest_imp |> #1 |> dest_conj
    val mods_thm = 
      mods_tm |> (RAND_CONV EVAL THENC no_dup_mods_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(ERR "duplicate modules")
    val types_thm = 
      types_tm |> (RAND_CONV EVAL THENC no_dup_top_types_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(ERR "duplicate top types")
    val th = MATCH_MP th (CONJ mods_thm types_thm)
  in (th,rhs(concl prog_rewrite)) end

end
