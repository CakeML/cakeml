open preamble
open ml_translatorTheory cfTacticsBaseLib cfTacticsLib
local open ml_progLib cf_initialProgramTheory in end

val basis_st =
  ml_progLib.unpack_ml_prog_state 
    cf_initialProgramTheory.basis_prog_state

val example_let0 = parse_topdecl
  "fun example_let0 n = let val a = 3; in a end"

val st0 = ml_progLib.add_prog example_let0 pick_name basis_st

val example_let0_spec = Q.prove (
  `!nv. app (p:'ffi ffi_proj) ^(fetch_v "example_let0" st0) [nv]
          emp (\v. & INT 3 v)`,
  xcf "example_let0" st0 \\ xlet `\a. & INT 3 a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
)

val example_let1 = parse_topdecl
  "fun example_let1 _ = let val a = (); in a end"

val st1 = ml_progLib.add_prog example_let1 pick_name basis_st

val example_let1_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let1" st1) [uv]
          emp (\v. & UNIT_TYPE () v)`,
  xcf "example_let1" st1 \\ xlet `\a. & UNIT_TYPE () a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
)

val example_let2 = parse_topdecl
  "fun example_let2 u = let val a = u; in a end"

val st2 = ml_progLib.add_prog example_let2 pick_name basis_st

val example_let2_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let2" st2) [uv]
          emp (\v. & (v = uv))`,
  xcf "example_let2" st2 \\ xlet `\v. & (v = uv)`
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
  xlet `\a. & INT (n+1) a`
  THEN1 (xapp \\ fs []) \\
  xlet `\b. & INT (n-1) b`
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
  xlet `\r1. REF r1 av` THEN1 xapp \\
  xlet `\r2. REF r2 bv * REF r1 av` THEN1 (xapp \\ xsimpl) \\
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
  xlet `\xv'. & (xv' = xv) * r1v ~~> xv * r2v ~~> yv`
    THEN1 (xapp \\ xsimpl) \\
  xlet `\yv'. & (yv' = yv) * r1v ~~> xv * r2v ~~> yv`
    THEN1 (xapp \\ xsimpl) \\
  xlet `\u. r1v ~~> yv * r2v ~~> yv`
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

  xcf "example_if" st \\ xlet `\bv. & BOOL (n > 0) bv`
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

val example_eq = parse_topdecl
  "fun example_eq x = (x = 3)"

val st = ml_progLib.add_prog example_eq pick_name basis_st

val example_eq_spec = Q.prove (
  `!x xv.
     INT x xv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "example_eq" st) [xv]
       emp (\bv. & BOOL (x = 3) bv)`,
  xcf "example_eq" st \\ xapp \\
  (* instantiate *) qexists_tac `INT` \\ fs [] \\
  fs [EqualityType_NUM_BOOL]
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
  xcf "example_and" st \\ xlet `\b. & BOOL T b`
  THEN1 (xret \\ xsimpl) \\
  xlog \\ xret \\ xsimpl
)

val list_length = parse_topdecl
  "fun length l = \
 \    case l of \
 \      [] => 0 \
 \    | x::xs => \
 \      let val xs_len = length xs \
 \      in xs_len + 1 end"

val bytearray_fromlist = parse_topdecl
  "fun fromList ls = \
 \    let val len = length ls \
 \        val w8z = Word8.fromInt 0 \
 \        val a = Word8Array.array len w8z \
 \        fun f ls i = \
 \          case ls of \
 \            [] => a \
 \          | h::t => \
 \            let val ipp = i + 1 in \
 \              (Word8Array.update a i h; f t ipp) \
 \            end \
 \    in f ls 0 end"

val st = basis_st
  |> ml_progLib.add_prog list_length pick_name
  |> ml_progLib.add_prog bytearray_fromlist pick_name

val list_length_spec = store_thm ("list_length_spec",
  ``!a l lv.
     LIST_TYPE a l lv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "length" st) [lv]
       emp (\v. & NUM (LENGTH l) v)``,
  Induct_on `l`
  THEN1 (
    xcf "length" st \\ fs [LIST_TYPE_def] \\ 
    xmatch \\ xret \\ xsimpl
  )
  THEN1 (
    xcf "length" st \\ fs [LIST_TYPE_def] \\
    rename1 `a x xv` \\ rename1 `LIST_TYPE a xs xvs` \\
    xmatch \\ xlet `\xs_len. & NUM (LENGTH xs) xs_len`
    THEN1 (xapp \\ metis_tac []) \\
    xapp \\ xsimpl \\ fs [NUM_def] \\ asm_exists_tac \\ fs [] \\
    (* meh? *) fs [INT_def] \\ intLib.ARITH_TAC
  )
)

val bytearray_fromlist_spec = Q.prove (
  `!l lv.
     LIST_TYPE WORD l lv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "fromList" st) [lv]
       emp (\av. W8ARRAY av l)`,
  xcf "fromList" st \\
  xlet `\len_v. & NUM (LENGTH l) len_v` THEN1 (xapp \\ metis_tac []) \\
  xlet `\w8z. & WORD (i2w 0: word8) w8z` THEN1 (xapp \\ fs []) \\
  xlet `\av. W8ARRAY av (REPLICATE (LENGTH l) (i2w 0))`
    THEN1 (xapp \\ fs []) \\
  xfun_spec `f`
    `!ls lvs i iv l_pre rest.
       NUM i iv /\ LIST_TYPE WORD ls lvs /\
       LENGTH rest = LENGTH ls /\ i = LENGTH l_pre
        ==>
       app p f [lvs; iv]
         (W8ARRAY av (l_pre ++ rest))
         (\ret. & (ret = av) * W8ARRAY av (l_pre ++ ls))`
  THEN1 (
    Induct_on `ls` \\ fs [LIST_TYPE_def, LENGTH_NIL] \\ rpt strip_tac
    THEN1 (xapp \\ xmatch \\ xret \\ xsimpl)
    THEN1 (
      fs [] \\ last_assum xapp_spec \\ xmatch \\
      xlet `\ippv. & NUM (LENGTH l_pre + 1) ippv * W8ARRAY av (l_pre ++ rest)`
      THEN1 (
        xapp \\ xsimpl \\ fs [NUM_def] \\ instantiate \\
        (* meh *) fs [INT_def] \\ intLib.ARITH_TAC
      ) \\
      rename1 `lvs = Conv _ [hv; tv]` \\ rename1 `WORD h hv` \\
      fs [LENGTH_CONS] \\ rename1 `rest = rest_h :: rest_t` \\
      xlet `\_. W8ARRAY av (l_pre ++ h :: rest_t)` THEN1 (
        xapp \\ xsimpl \\ fs [UNIT_TYPE_def] \\ instantiate \\
        fs [lupdate_append]
      ) \\
      once_rewrite_tac [
        Q.prove(`l_pre ++ h::ls = (l_pre ++ [h]) ++ ls`, fs [])
      ] \\ xapp \\ fs []
    )
  ) \\
  xapp \\ fs [] \\ xsimpl \\
  Q.LIST_EXISTS_TAC [`REPLICATE (LENGTH l) (i2w 0)`, `l`, `[]`] \\
  fs [LENGTH_REPLICATE]
)
