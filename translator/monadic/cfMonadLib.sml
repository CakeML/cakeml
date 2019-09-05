(*
  Automation that converts between judgements used by CF and
  judgements used by the monadic translator.
*)
structure cfMonadLib (* :> cfMonadLib *) = struct

open cfAppTheory cfTacticsLib ml_monad_translatorTheory cfMonadTheory packLib
open ml_monad_translatorBaseTheory

val get_term = let
  val ys = unpack_list (unpack_pair unpack_string unpack_term) cfMonadTheory.parsed_terms
  in fn s => snd (first (fn (n,_) => n = s) ys) end

fun get_fun_const def =
  def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
fun get_ro_var def = concl def |> strip_comb |> snd |> hd

val REF_REL_tm = get_fun_const REF_REL_def;
val RARRY_REL_tm = get_fun_const RARRAY_REL_def;
val emp_tm = get_term "emp";

val PURE_tm = get_term "PURE";
val Eq_pat = SPEC_ALL ml_translatorTheory.Eq_def |> concl |> lhs;
val EqSt_pat = SPEC_ALL EqSt_def |> concl |> lhs;

(*
val spec = spec1
*)
fun mk_app_of_ArrowP spec = let
    val spec = PURE_REWRITE_RULE[ArrowM_def] spec
                                |> UNDISCH_ALL
    val arrow_RI = concl spec |> rator |> rator
    val f_const = concl spec |> rator |> rand
    val fv_const = concl spec |> rand
    val H_pair = arrow_RI |> rator |> rator |> rand
    val (H, p_var) = dest_pair H_pair
    val state_type = type_of H |> dest_type |> snd |> List.hd
    val state_var = mk_var("state", state_type)
    val ro = get_ro_var spec

    (* Create variables for the HOL and CakeML parameters,
       retrieve the refinement invariants *)
    fun get_params arrow_RI n = let
        val (comb_tm, params) = strip_comb arrow_RI
        val ri = rator arrow_RI |> rand
        val arrow_RI' = rand arrow_RI
        val comb_tm = rator arrow_RI'
        val x = mk_var("x"^(Int.toString n), type_of ri |> dest_type |> snd |> List.hd)
        val xv = mk_var("xv"^(Int.toString n), v_ty)
        val x_triple = (x, xv, ri)
    in if same_const PURE_tm comb_tm then let
           val arrow_RI' = rand arrow_RI'
           val (params_v, ret_invs) = get_params arrow_RI' (n+1)
       in (x_triple::params_v, ret_invs) end
       else ([x_triple], (rator arrow_RI' |> rand, rand arrow_RI'))
    end
    val (params_info, (ret_inv, exn_inv)) = get_params arrow_RI 1

    (* If there are occurences of Eq and EqSt *)
    fun clean_inv x inv var_subst =
      if can (match_term Eq_pat) (rand inv)
      then let
          val inv = rand inv
          val x' = rand inv
          val s = (x' |-> x)
          val inv = subst [s] inv
      in (inv,s::var_subst) end
      else (rand inv,var_subst)
    fun clean_params ((x,xv,inv)::params_info) = let
        val (params_info,var_subst,has_EqSt) = clean_params params_info
    in
        if can (match_term EqSt_pat) inv then let
            val st = rand inv
            val inv = rator inv |> rand
            val var_subst = (st |-> state_var)::var_subst
            val (inv,var_subst) = clean_inv x inv var_subst
        in ((x,xv,inv)::params_info,var_subst,true) end
        else let
            val (inv,var_subst) = clean_inv x inv var_subst
        in ((x,xv,inv)::params_info,var_subst,has_EqSt) end
    end
      | clean_params [] = ([],[],false)
    val (params_info,var_subst,has_EqSt) = clean_params params_info
    val spec = INST var_subst spec

    (* val (x, xv, ri) = hd params_info *)
    val ri_hyps = List.map (fn (x, xv, ri) => list_mk_comb(ri, [x, xv])) params_info
    val params = List.map #1 params_info

    (* Start the recursion *)
    val current_f = list_mk_comb (f_const, List.take(params, List.length params - 1))
    val (last_x, last_xv, last_ri) = List.last params_info
    val xl = List.map #1 params_info
    val xvl = List.map #2 params_info
    val params_info = List.tl(List.rev params_info)
    val fv_var = mk_var("fv", v_ty)
    val gv_var = mk_var("gv", v_ty)

    val lemma = if has_EqSt then ArrowP_MONAD_EqSt_to_app
                else ArrowP_MONAD_to_app
    val th = ISPECL[last_ri,ret_inv,exn_inv,current_f,gv_var,H,last_x,
                    last_xv,ro,state_var,p_var] lemma |> UNDISCH
    val Q = concl th |> rand |> rand
    val Q_abs = mk_abs(state_var, Q)

    (* Perform the recursion *)
    (* val (x, xv, ri) = List.hd params_info *)
    fun mk_app_rec th ((x, xv, ri)::x_info) = let
        val A = ri
        val B = concl th |> dest_imp |> fst |> rator |> rator
        val (xv2, xvl) = concl th |> dest_imp |> snd |> rator |> rator |> rand |> dest_comb
        val xv2 = rand xv2
        val f_tm = concl th |> dest_imp |> fst |> rator |> rand |> rator

        val assum = GEN gv_var th
        val imp_th = ISPECL[A,B,f_tm,fv_var,x,xv,xv2,xvl,H,
                            Q_abs,ro,state_var,p_var] ArrowP_PURE_to_app
                        |> UNDISCH |> BETA_RULE
        val th = MATCH_MP imp_th assum |> SPEC_ALL |> Thm.INST [fv_var |-> gv_var]
    in mk_app_rec th x_info end
      | mk_app_rec th [] = th
    val th = mk_app_rec th params_info

    (* Instantiate the CakeML function variable and remove the ArrowP hypothesis *)
    val th = MP (Thm.INST[gv_var |-> fv_const] th) spec

    (* Undischarge the refinement invariants for the arguments and
       the precondition*)
    val th = List.foldr (fn (a, th) => DISCH a th) th ri_hyps |> DISCH_ALL

    (* Perform some cleanup *)
    val th = SIMP_RULE bool_ss[ml_translatorTheory.PRECONDITION_def,
                               ml_translatorTheory.Eq_def] th

    (* Generalize the variables *)
    val th = GENL[state_var] th |> GENL xvl |> GENL xl
in th end

(*

Datatype:
  state_refs = <| the_num : num ;
                  the_num_array : num list ;
                  the_int_array : int list |>
End

val ptr1_def = Define `ptr1 = Loc 1`;
val ptr2_def = Define `ptr2 = Loc 2`;
val ptr3_def = Define `ptr3 = Loc 3`;

val STATE_REF_def = Define `
  STATE_REF = \st.
    REF_REL NUM ptr1 st.the_num *
    RARRAY_REL NUM ptr2 st.the_num_array *
    RARRAY_REL INT ptr3 st.the_int_array`

val f1_def = Define `f1 (x : num) y = st_ex_return(x + y)`
val f1_v_def = Define `f1_v = Loc 0`
val f1_side_def = Define `f1_side x y st = T`

val ffi = ``p:'ffi ffi_proj``

val spec1 = Q.prove (
  `ArrowP ro (STATE_REF, ^ffi) (PURE NUM)
          (ArrowM ro (STATE_REF, ^ffi) (PURE NUM) (MONAD NUM UNIT_TYPE)) f1 f1_v`,
  ...);

val spec2 = Q.prove (
  `PRECONDITION (f1_side x y st)
   ==>
   ArrowP ro (STATE_REF, ^ffi) (PURE (Eq NUM x))
          (ArrowM ro (STATE_REF, ^ffi) (EqSt (PURE (Eq NUM y)) st)
            (MONAD NUM UNIT_TYPE)) f1 f1_v`,
  ...)

mk_app_of_ArrowP spec1
mk_app_of_ArrowP spec2

*)

(* Some tests

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload ex_bind[local] = ``st_ex_bind``
Overload ex_return[local] = ``st_ex_return``

val _ = Datatype `
  my_state =
    <| my_count : num
     ; has_init : bool
     |>`

val init_state_def = Define `
  init_state =
    do
      is_done <- get_has_init;
      if is_done then
        raise_Fail (strlit"init")
      else
        do
          set_my_count 0;
          set_has_init true;
          return ()
        od
    od`

*)

end
