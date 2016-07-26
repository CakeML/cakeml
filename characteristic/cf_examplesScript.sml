open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfAppTheory cfTheory
open cfTacticsTheory cfTacticsBaseLib cfTacticsLib

val basis_st =
  ml_progLib.unpack_ml_prog_state 
    cf_initialProgramTheory.basis_prog_state

val example_let0 = parse_topdecl
  "fun example_let0 n = let val a = 3; in a end"

val st0 = ml_progLib.add_prog example_let0 pick_name basis_st

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

val st1 = ml_progLib.add_prog example_let1 pick_name basis_st

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

val st2 = ml_progLib.add_prog example_let2 pick_name basis_st

val example_let2_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let2" st2) [uv]
          emp
          (\v. cond (v = uv))`,
  xcf "example_let2" st2 \\ xlet `\v. cond (v = uv)` `a`
  THEN1 (xret \\ hsimpl) \\
  xret \\ hsimpl
)

val example_let = parse_topdecl
  "fun example_let n = let val a = n + 1; val b = n - 1; in a+b end"

val st = ml_progLib.add_prog example_let pick_name basis_st

val example_let_spec = Q.prove (
  `!n nv.
     INT n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "example_let" st) [nv]
       emp (\v. cond (INT (2 * n) v))`,

  xcf "example_let" st \\
  xlet `\v. cond (INT (n+1) v)` `a`
  THEN1 (xapp \\ fs []) \\
  xlet `\v. cond (INT (n-1) v)` `b`
  THEN1 (xapp \\ fs []) \\
  xapp \\ xsimpl \\ fs [INT_def] \\ intLib.ARITH_TAC
)

