open preamble
     set_sepTheory helperLib
     ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfTheory cfTacticsBaseLib cfTacticsLib

val initial_prog = EVAL ``basis_program`` |> concl |> rand
val initial_st = ml_progLib.add_prog initial_prog pick_name ml_progLib.init_state

val lnull = parse_topdecl
  "fun lnull l = case l of [] => true | x::xs => false"

val st = ml_progLib.add_prog lnull pick_name initial_st

local
  val cs = listLib.list_compset()
  val () = basicComputeLib.add_basic_compset cs
  val () = semanticsComputeLib.add_semantics_compset cs
  val eval = computeLib.CBV_CONV cs
in
val eval_pat_bindings = eval
end

val exists_v_of_pat_norest_length = Q.prove (
  `!envC pat insts v.
     (?insts. v_of_pat_norest envC pat insts = SOME v) <=>
     (?insts. LENGTH insts = LENGTH (pat_bindings pat []) /\
              v_of_pat_norest envC pat insts = SOME v)`,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\ instantiate \\
  progress v_of_pat_norest_insts_length
)

val forall_v_of_pat_norest_length = Q.prove (
  `!envC pat insts v P.
     (!insts. v_of_pat_norest envC pat insts = SOME v ==> P insts) <=>
     (!insts. LENGTH insts = LENGTH (pat_bindings pat []) ==>
              v_of_pat_norest envC pat insts = SOME v ==>
              P insts)`,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\
  progress v_of_pat_norest_insts_length \\ first_assum progress
)

val lnull_spec = Q.prove (
  `!lv a l.
     app (p:'ffi ffi_proj) ^(fetch_v "lnull" st) [lv]
       (cond (LIST_TYPE a l lv))
       (\bv. cond (BOOL (l = []) bv))`,

  xcf "lnull" st \\
  fs [cf_mat_def] \\ irule local_elim \\ reduce_tac \\
  strip_tac THEN1 cheat \\
  fs [build_cases_def] \\ fs [exists_v_of_pat_norest_length] \\
  fs [forall_v_of_pat_norest_length] \\
  CONV_TAC (DEPTH_CONV (fn t => (match_term ``LENGTH (pat_bindings _ _)`` t; eval_pat_bindings t))) \\
  fs [LENGTH_EQ_NUM_compute, PULL_EXISTS, PULL_FORALL] \\
  cfTacticsBaseLib.qeval_pat_tac `v_of_pat_norest _ _ _` \\
  fs [option_CLAUSES] \\
  cheat
)

