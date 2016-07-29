open HolKernel Parse boolLib bossLib preamble
open ml_translatorTheory cfTacticsBaseLib cfTacticsLib

val basis_st =
  ml_progLib.unpack_ml_prog_state 
    cf_initialProgramTheory.basis_prog_state

val example_let0 = parse_topdecl
  "fun example_let0 n = let val a = 3; in a end"

val st0 = ml_progLib.add_prog example_let0 pick_name basis_st

val example_let0_spec = Q.prove (
  `!nv. app (p:'ffi ffi_proj) ^(fetch_v "example_let0" st0) [nv]
          emp (\v. & INT 3 v)`,
  xcf "example_let0" st0 \\ xlet `\v. cond (INT 3 v)` `a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
)

val example_let1 = parse_topdecl
  "fun example_let1 _ = let val a = (); in a end"

val st1 = ml_progLib.add_prog example_let1 pick_name basis_st

val example_let1_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let1" st1) [uv]
          emp (\v. & UNIT_TYPE () v)`,
  xcf "example_let1" st1 \\ xlet `\v. cond (UNIT_TYPE () v)` `a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
)

val example_let2 = parse_topdecl
  "fun example_let2 u = let val a = u; in a end"

val st2 = ml_progLib.add_prog example_let2 pick_name basis_st

val example_let2_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let2" st2) [uv]
          emp (\v. & (v = uv))`,
  xcf "example_let2" st2 \\ xlet `\v. cond (v = uv)` `a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
)

val example_let = parse_topdecl
  "fun example_let n = let val a = n + 1; val b = n - 1; in a+b end"

val st = ml_progLib.add_prog example_let pick_name basis_st

val example_let_spec = Q.prove (
  `!n nv.
     INT n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "example_let" st) [nv]
       emp (\v. & INT (2 * n) v)`,

  xcf "example_let" st \\
  xlet `\v. & INT (n+1) v` `a`
  THEN1 (xapp \\ fs []) \\
  xlet `\v. & INT (n-1) v` `b`
  THEN1 (xapp \\ fs []) \\
  xapp \\ xsimpl \\ fs [INT_def] \\ intLib.ARITH_TAC
)


val alloc_ref2 = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun alloc_ref2 a b = let val r1 = ref a; val r2 = ref b in (r1, r2) end;"

val st = ml_progLib.add_prog alloc_ref2 pick_name basis_st

val alloc_ref2_spec = Q.prove (
  `!av bv a b r1v r2v r1 r2.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "alloc_ref2" st) [av; bv]
       emp
       (\p. SEP_EXISTS r1 r2.
              & PAIR_TYPE (=) (=) (r1, r2) p *
              REF r1 av * REF r2 bv)`,
  xcf "alloc_ref2" st \\
  xlet `\v. REF v av` `r1` THEN1 xapp \\
  xlet `\v. REF v bv * REF r1 av` `r2` THEN1 (xapp \\ xsimpl) \\
  xret \\ fs [PAIR_TYPE_def] \\ xsimpl
)

val swap = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun swap r1 r2 = let val x1 = !r1 val x2 = !r2 in r1 := x2; r2 := x1 end"

val st2 = ml_progLib.add_prog swap pick_name st

val swap_spec = Q.prove (
  `!xv yv r1v r2v.
     app (p:'ffi ffi_proj) ^(fetch_v "swap" st2) [r1v; r2v]
       (REF r1v xv * REF r2v yv)
       (\v. & UNIT_TYPE () v * REF r1v yv * REF r2v xv)`,
  xcf "swap" st2 \\
  xlet `\v. & (v = xv) * r1v ~~> xv * r2v ~~> yv` `xv'`
    THEN1 (xapp \\ xsimpl) \\
  xlet `\v. & (v = yv) * r1v ~~> xv * r2v ~~> yv` `yv'`
    THEN1 (xapp \\ xsimpl) \\
  xlet `\v. r1v ~~> yv * r2v ~~> yv` `u`
    THEN1 (xapp \\ xsimpl) \\
  xapp \\ xsimpl
)

val example_if = parse_topdecl
  "fun example_if n = let val b = n > 0 in if b then 1 else 2 end"

val st = ml_progLib.add_prog example_if pick_name basis_st

val example_if_spec = Q.prove (
  `!n nv.
     INT n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "example_if" st) [nv]
       emp (\v. &(if n > 0 then INT 1 v else INT 2 v))`,

  xcf "example_if" st \\ xlet `\v. & BOOL (n > 0) v` `bv`
  THEN1 (xapp \\ fs []) \\
  xif \\ xret \\ xsimpl
)
  
val is_nil = parse_topdecl
  "fun is_nil l = case l of [] => true | x::xs => false" 

val st = ml_progLib.add_prog is_nil pick_name basis_st

val is_nil_spec = Q.prove (
  `!lv a l.
     LIST_TYPE a l lv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "is_nil" st) [lv]
       emp (\bv. & BOOL (l = []) bv)`,

  xcf "is_nil" st \\ Cases_on `l` \\ fs [LIST_TYPE_def] \\
  xmatch \\ xret \\ xsimpl
)

(* unfortunately, "true" is not a value... *)
val example_and = parse_topdecl
  "fun example_and u = let val b = true in b andalso false end"

val st = ml_progLib.add_prog example_and pick_name basis_st

val example_and_spec = Q.prove (
  `!uv.
     UNIT_TYPE () uv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "example_and" st) [uv]
       emp (\bv. & BOOL F bv)`,
  xcf "example_and" st \\ xlet `\v. & BOOL T v` `b`
  THEN1 (xret \\ xsimpl) \\
  xlog \\ xret \\ xsimpl
)
