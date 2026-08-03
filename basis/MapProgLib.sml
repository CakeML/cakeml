(*
  Functions for teaching the translator about fmap operations
*)
structure MapProgLib :> MapProgLib =
struct

open HolKernel boolLib bossLib BasicProvers ml_translatorLib;
open MapProgTheory;

(*
  val _  = translation_extends "MapProg";
  val th = miscTheory.TotOrd_num_cmp;
*)

fun add_fmap_for_cmp th = let
  val cmp_tm = th |> concl |> rand
  val _ = hol2deep cmp_tm handle UnableToTranslate _ =>
          failwith "Ordering must the translated first"
  fun find_name name i = let
    val s = if i < 0 then name else name ^ "_" ^ int_to_string i
    in
      (if (Parse.Term [QUOTE (s ^ " :'a ")] |> is_const) then
         find_name name (i+1)
       else s)
      handle HOL_ERR _ => find_name name (i+1)
    end
  val const_name = find_name "fempty" (0-1)
  val tm = mlmapTheory.empty_def |> ISPEC cmp_tm |> concl |> dest_eq |> fst
  val def_tm = mk_eq(mk_var(const_name,type_of tm), tm)
  val def = new_definition(const_name ^ "_def", def_tm)
  val empty_v_thm = translate (def |> REWRITE_RULE [mlmapTheory.empty_def,
                                                    balanced_mapTheory.empty_def])
  val lem = CONJ (empty_v_thm |> REWRITE_RULE [def]) th
  val ops_thm = MATCH_MP IMP_FMAP_TYPE_ops lem
  val fempty_thm = ops_thm |> cj 1
  (* empty + teach about type’*)
  val res = fempty_thm |> concl |> rator
  val fmap_ty = res |> rand |> type_of
  val fmap_inv = res |> rator
  val _ = add_type_inv fmap_inv fmap_ty
  val _ = add_user_proved_v_thm fempty_thm
  (* lookup *)
  val th1 = cj 2 ops_thm
  val th2 = cj 1 mlmap_op_v_thms
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val flookup_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm flookup_thm
  (* delete *)
  val th1 = cj 4 ops_thm
  val th2 = cj 3 mlmap_op_v_thms
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val domsub_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm domsub_thm
  (* update *)
  val th1 = cj 3 ops_thm
  val th2 = cj 4 mlmap_op_v_thms
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val fmap_update_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm fmap_update_thm
  (* union *)
  val th1 = cj 5 ops_thm
  val th2 = cj 2 mlmap_op_v_thms
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val funion_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm funion_thm
  in () end;

end