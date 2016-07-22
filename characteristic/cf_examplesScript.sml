open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfAppTheory cfTheory
open cfTacticsTheory cfTacticsBaseLib cfTacticsLib

val initial_prog = EVAL ``basis_program`` |> concl |> rand
val initial_st = ml_progLib.add_prog initial_prog pick_name ml_progLib.init_state

val example_let0 = parse_topdecl
  "fun example_let0 n = let val a = 3; in a end"

val st0 = ml_progLib.add_prog example_let0 pick_name initial_st

val example_let0_spec = Q.prove (
  `!nv. app (p:'ffi ffi_proj) ^(fetch_v "example_let0" st0) [nv]
          emp
          (\v. cond (INT 3 v))`,
  xcf "example_let0" st0 \\ xlet `\v. cond (INT 3 v)` `a`
  THEN1 (xret \\ hsimpl \\ fs [INT_def]) \\
  xret \\ hsimpl \\ fs []
)

val example_let1 = parse_topdecl
  "fun example_let1 _ = let val a = (); in a end"

val st1 = ml_progLib.add_prog example_let1 pick_name initial_st

val example_let1_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let1" st1) [uv]
          emp
          (\v. cond (UNIT_TYPE () v))`,
  xcf "example_let1" st1 \\ xlet `\v. cond (UNIT_TYPE () v)` `a`
  THEN1 (xret \\ hsimpl \\ fs [UNIT_TYPE_def]) \\
  xret \\ hsimpl \\ fs []
)

val example_let2 = parse_topdecl
  "fun example_let2 u = let val a = u; in a end"

val st2 = ml_progLib.add_prog example_let2 pick_name initial_st

val example_let2_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let2" st2) [uv]
          emp
          (\v. cond (v = uv))`,
  xcf "example_let2" st2 \\ xlet `\v. cond (v = uv)` `a`
  THEN1 (xret \\ hsimpl) \\
  xret \\ hsimpl
)

(*------------------------------------------------------------------*)
(* Specs for functions of the initial environment *)

val ref_spec = Q.prove (
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "ref" initial_st) [xv]
          emp
          (\rv. rv ~~> xv)`,

  xcf "ref" initial_st \\ fs [cf_ref_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def] \\ hsimpl
)

val deref_spec = Q.prove (
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "!" initial_st) [rv]
          (rv ~~> xv)
          (\yv. cond (xv = yv) * rv ~~> xv)`,

  xcf "!" initial_st \\ fs [cf_deref_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_deref_def] \\ hsimpl \\ fs [] \\
  qexists_tac `emp` \\ hsimpl
)

val assign_spec = Q.prove (
  `!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v ":=" initial_st) [rv; yv]
       (rv ~~> xv)
       (\v. cond (UNIT_TYPE () v) * rv ~~> yv)`,

  xcf ":=" initial_st \\ fs [cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_assign_def] \\ hsimpl \\ fs [UNIT_TYPE_def] \\
  qexists_tac `emp` \\ hsimpl
)

