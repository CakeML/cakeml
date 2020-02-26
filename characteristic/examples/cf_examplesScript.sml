(*
  A collection of small examples that show (and test) what can be done
  in CF proofs.
*)
open preamble
open ml_translatorTheory ml_translatorLib cfTacticsBaseLib cfTacticsLib
open ml_progLib basisFunctionsLib
local open basisProgTheory in end

val _ = new_theory "cf_examples";
val _ = translation_extends "basisProg"

fun xcf' s = xcf_with_def s (DB.fetch "-" (s ^ "_v_def"))
val _ = (append_prog o process_topdecs)
  `fun example_let0 n = let val a = 3; in a end`;
val example_let0_v_def = DB.fetch "-" "example_let0_v_def"

Theorem example_let0_spec[local]:
  !nv. app (p:'ffi ffi_proj) example_let0_v [nv] emp (POSTv v. & INT 3 v)
Proof
  xcf' "example_let0" \\ xlet `POSTv a. & INT 3 a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun example_let1 _ = let val a = (); in a end`

Theorem example_let1_spec[local]:
  !uv. app (p:'ffi ffi_proj) example_let1_v [uv] emp (POSTv v. & UNIT_TYPE () v)
Proof
  xcf' "example_let1" \\ xmatch \\
  xlet `POSTv a. & UNIT_TYPE () a`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun example_let2 u = let val a = u; in a end`

Theorem example_let2_spec[local]:
  !uv. app (p:'ffi ffi_proj) example_let2_v [uv] emp (POSTv v. & (v = uv))
Proof
  xcf' "example_let2" \\ xlet `POSTv v. & (v = uv)`
  THEN1 (xret \\ xsimpl) \\
  xret \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun example_let n = let val a = n + 1; val b = n - 1; in a+b end`

Theorem example_let_spec[local]:
  !n nv.
     INT n nv ==>
     app (p:'ffi ffi_proj) example_let_v [nv] emp (POSTv v. & INT (2 * n) v)
Proof
  xcf' "example_let" \\
  xlet `POSTv a. & INT (n+1) a`
  THEN1 (xapp \\ fs []) \\
  xlet `POSTv b. & INT (n-1) b`
  THEN1 (xapp \\ fs []) \\
  xapp \\ xsimpl \\ fs [INT_def] \\ intLib.ARITH_TAC
QED

val _ = (append_prog o process_topdecs)
  `fun alloc_ref2 a b = (Ref a, Ref b);`
val alloc_ref2_v_def = fetch "-" "alloc_ref2_v_def"

Theorem alloc_ref2_spec[local]:
  !av bv a b r1v r2v r1 r2.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) alloc_ref2_v [av; bv]
       emp
       (POSTv p. SEP_EXISTS r1 r2.
                 & PAIR_TYPE (=) (=) (r1, r2) p *
                 REF r1 av * REF r2 bv)
Proof
  xcf' "alloc_ref2" \\
  xlet `POSTv r2. REF r2 bv` THEN1 (xref >> xsimpl) \\
  xlet `POSTv r1. REF r1 av * REF r2 bv` THEN1 (xref \\ xsimpl) \\
  xret \\ fs [PAIR_TYPE_def] \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun swap r1 r2 = let val x1 = !r1 in r1 := !r2; r2 := x1 end`

Theorem swap_spec[local]:
  !xv yv r1v r2v.
     app (p:'ffi ffi_proj) swap_v [r1v; r2v]
       (REF r1v xv * REF r2v yv)
       (POSTv v. & UNIT_TYPE () v * REF r1v yv * REF r2v xv)
Proof
  xcf' "swap" \\
  xlet `POSTv xv'. & (xv' = xv) * r1v ~~> xv * r2v ~~> yv`
    THEN1 (xapp \\ xsimpl) \\
  xlet `POSTv yv'. & (yv' = yv) * r1v ~~> xv * r2v ~~> yv`
    THEN1 (xapp \\ xsimpl) \\
  xlet `POSTv u. r1v ~~> yv * r2v ~~> yv`
    THEN1 (xapp \\ xsimpl) \\
  xapp \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun example_if n = if n > 0 then 1 else 2`

Theorem example_if_spec[local]:
  !n nv.
     INT n nv ==>
     app (p:'ffi ffi_proj) example_if_v [nv]
       emp (POSTv v. &(if n > 0 then INT 1 v else INT 2 v))
Proof
  xcf' "example_if" \\
  xlet `POSTv bv. & BOOL (n > 0) bv`
  THEN1 (xapp \\ fs []) \\
  xif \\ xret \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun is_nil l = case l of [] => True | x::xs => False`

Theorem is_nil_spec[local]:
  !lv a l.
     LIST_TYPE a l lv ==>
     app (p:'ffi ffi_proj) is_nil_v [lv]
       emp (POSTv bv. & BOOL (l = []) bv)
Proof
  xcf' "is_nil" \\ Cases_on `l` \\
  fs [LIST_TYPE_def] \\
  xmatch \\ xret \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun is_none opt = case opt of None => True | Some _ => False`

val OPTION_TYPE_def = std_preludeTheory.OPTION_TYPE_def;

Theorem is_none_spec[local]:
  !ov a opt.
     OPTION_TYPE a opt ov ==>
     app (p:'ffi ffi_proj) is_none_v [ov]
       emp (POSTv bv. & BOOL (opt = NONE) bv)
Proof
  xcf' "is_none" \\ Cases_on `opt` \\
  fs [OPTION_TYPE_def] \\
  xmatch \\ xcon \\ xsimpl
)

val example_eq = (append_prog o process_topdecs)
  `fun example_eq x = (x = 3)`

Theorem example_eq_spec[local]:
  !x xv.
     INT x xv ==>
     app (p:'ffi ffi_proj) example_eq_v [xv]
       emp (POSTv bv. & BOOL (x = 3) bv)
Proof
  xcf' "example_eq" \\ xapp \\
  (* instantiate *) qexists_tac `INT` \\ fs [] \\
  fs [EqualityType_NUM_BOOL]
QED

val example_and = (append_prog o process_topdecs)
  `fun example_and u = True andalso False`

Theorem example_and_spec[local]:
  !uv.
     UNIT_TYPE () uv ==>
     app (p:'ffi ffi_proj) example_and_v [uv]
       emp (POSTv bv. & BOOL F bv)
Proof
  xcf' "example_and" \\ xlet `POSTv b. & BOOL T b`
  THEN1 (xret \\ xsimpl) \\
  xlog \\ xret \\ xsimpl
QED

val example_raise = (append_prog o process_topdecs)
  `exception Foo
   fun example_raise u = raise Foo`


val example_raise_spec = Q.prove (
  `!uv.
     UNIT_TYPE () uv ==>
     app (p:'ffi ffi_proj) example_raise_v [uv]
       emp (POSTe v. & (v = Conv (SOME (ExnStamp 8)) []))`,
  xcf' "example_raise" \\
  xlet `POSTv ev. & (ev = Conv (SOME (ExnStamp 8)) [])`
  THEN1 (xcon \\ xsimpl) \\
  xraise \\ xsimpl
);

val example_handle = (append_prog o process_topdecs)
  `exception Foo int
   fun example_handle x = (raise Foo 3) handle Foo i => i`

Definition Foo_exn_def:
  Foo_exn st i v = (v = Conv (SOME (ExnStamp st)) [Litv (IntLit i)])
End

val example_handle_spec = Q.prove (
  `!uv.
     UNIT_TYPE () uv ==>
     app (p:'ffi ffi_proj) example_handle_v [uv]
       emp (POSTv v. & INT 3 v)`,
  xcf' "example_handle" \\
  xhandle `POSTe v. & Foo_exn 9 3 v`
  THEN1 (
    xlet `POSTv v. & Foo_exn 9 3 v`
    THEN1 (xcon \\ fs [Foo_exn_def] \\ xsimpl) \\
    xraise \\ xsimpl
  ) \\
  fs [Foo_exn_def] \\ xcases \\ xvar \\ xsimpl
);

val _ = (append_prog o process_topdecs)
  `exception Foo int
   fun example_handle2 x =
     (if x > 0 then
        1
      else
        raise (Foo (~1)))
     handle Foo i => i`

val example_handle2_spec = Q.prove (
  `!x xv.
     INT x xv ==>
     app (p:'ffi ffi_proj) example_handle2_v [xv]
       emp (POSTv v. & INT (if x > 0 then 1 else (-1)) v)`,
  xcf' "example_handle2" \\
  xhandle ‘POSTve (\v. & (x > 0 /\ INT 1 v))
                  (\e. & (x <= 0 /\ Foo_exn 10 (-1) e))’
  THEN1 (
    xlet `POSTv bv. & (BOOL (x > 0) bv)`
    THEN1 (xapp \\ fs []) \\
    xif
    THEN1 (
      xret \\ xsimpl \\ rpt strip_tac \\
      irule FALSITY \\ intLib.ARITH_TAC
    )
    THEN1 (
      xlet `POSTv ev. & Foo_exn 10 (-1) ev`
      THEN1 (xret \\ fs [Foo_exn_def] \\ xsimpl) \\
      xraise \\ xsimpl \\ intLib.ARITH_TAC
    )
  )
  THEN1 xsimpl \\
  fs [Foo_exn_def] \\ xcases \\ xret \\ xsimpl \\ intLib.ARITH_TAC
);

val example_nested_apps = (append_prog o process_topdecs)
  `fun f i = ~ (~ (~ i))`;

val example_nested_apps_spec = Q.prove (
  `!x xv.
     INT x xv ==>
     app (p:'ffi ffi_proj) f_v [xv]
       emp (POSTv v. & INT (~ x) v)`,
  xcf' "f" \\
  xlet `POSTv v. & INT (~ x) v` THEN1 (xapp \\ fs []) \\
  xlet `POSTv v. & INT x v` THEN1 (xapp \\ xsimpl \\ instantiate) \\
  xapp \\ fs []
);

val bytearray_fromlist = (append_prog o process_topdecs)
  `fun length l =
     case l of
         [] => 0
       | x::xs => (length xs) + 1

   fun fromList ls =
     let val a = Word8Array.array (length ls) (Word8.fromInt 0)
         fun f ls i =
           case ls of
               [] => a
             | h::t => (Word8Array.update a i h; f t (i+1))
     in f ls 0 end`

Theorem list_length_spec:
   !a l lv.
     LIST_TYPE a l lv ==>
     app (p:'ffi ffi_proj) length_v [lv]
       emp (POSTv v. & NUM (LENGTH l) v)
Proof
  Induct_on `l`
  THEN1 (
    xcf' "length" \\ fs [LIST_TYPE_def] \\
    xmatch \\ xret \\ xsimpl
  )
  THEN1 (
    xcf' "length" \\ fs [LIST_TYPE_def] \\
    rename1 `a x xv` \\ rename1 `LIST_TYPE a xs xvs` \\
    xmatch \\ xlet `POSTv xs_len. & NUM (LENGTH xs) xs_len`
    THEN1 (xapp \\ metis_tac []) \\
    xapp \\ xsimpl \\ fs [NUM_def] \\ asm_exists_tac \\ fs [] \\
    (* meh? *) fs [INT_def] \\ intLib.ARITH_TAC
  )
QED

val bytearray_fromlist_spec = Q.prove (
  `!l lv.
     LIST_TYPE WORD l lv ==>
     app (p:'ffi ffi_proj) fromList_v [lv]
       emp (POSTv av. W8ARRAY av l)`,
  xcf' "fromList" \\
  xlet `POSTv w8z. & WORD (n2w 0: word8) w8z` THEN1 (xapp \\ fs []) \\
  xlet `POSTv len_v. & NUM (LENGTH l) len_v` THEN1 (xapp \\ metis_tac []) \\
  xlet `POSTv av. W8ARRAY av (REPLICATE (LENGTH l) 0w)`
    THEN1 (xapp \\ fs []) \\
  xfun_spec `f`
    `!ls lvs i iv l_pre rest.
       NUM i iv /\ LIST_TYPE WORD ls lvs /\
       LENGTH rest = LENGTH ls /\ i = LENGTH l_pre
        ==>
       app p f [lvs; iv]
         (W8ARRAY av (l_pre ++ rest))
         (POSTv ret. & (ret = av) * W8ARRAY av (l_pre ++ ls))`
  THEN1 (
    Induct_on `ls` \\ fs [LIST_TYPE_def, LENGTH_NIL] \\ rpt strip_tac
    THEN1 (xapp \\ xmatch \\ xret \\ xsimpl)
    THEN1 (
      fs [] \\ last_assum xapp_spec \\ xmatch \\ fs [LENGTH_CONS] \\
      rename1 `rest = rest_h :: rest_t` \\ rw [] \\
      xlet `POSTv _. W8ARRAY av (l_pre ++ h :: rest_t)` THEN1 (
        xapp \\ xsimpl \\ fs [UNIT_TYPE_def] \\ instantiate \\
        fs [lupdate_append]
      ) \\
      xlet `POSTv ippv. & NUM (LENGTH l_pre + 1) ippv * W8ARRAY av (l_pre ++ h::rest_t)`
      THEN1 (
        xapp \\ xsimpl \\ fs [NUM_def] \\ instantiate \\
        fs [INT_def] \\ intLib.ARITH_TAC
      ) \\
      once_rewrite_tac [
        Q.prove(`l_pre ++ h::ls = (l_pre ++ [h]) ++ ls`, fs [])
      ] \\ xapp \\ fs []
    )
  ) \\
  xapp \\ fs [] \\ xsimpl \\ fs [LENGTH_NIL_SYM, LENGTH_REPLICATE]
)

val strcat_foo = (append_prog o process_topdecs)
  `fun strcat_foo r = r := !r ^ "foo"`

val xlet_auto = cfLetAutoLib.xlet_auto

val strcat_foo_spec = Q.prove (
  `!rv sv s.
     STRING_TYPE s sv ==>
     app (p:'ffi ffi_proj) strcat_foo_v [rv]
       (REF rv sv)
       (POSTv uv. SEP_EXISTS sv'.
            &(UNIT_TYPE () uv /\ STRING_TYPE (s ^ implode "foo") sv') *
            REF rv sv')`,
  xcf' "strcat_foo" >>
  xlet_auto >- xsimpl >>
  xlet `POSTv sv'. &(STRING_TYPE (s ^ implode "foo") sv') * rv ~~> sv`
  >- (xapp >> xsimpl >> simp[mlstringTheory.implode_def] >> metis_tac[]) >>
  rveq >> xapp >> xsimpl);

val example_ffidiv = (append_prog o process_topdecs) `
   fun example_ffidiv b = if b then Runtime.abort () else ()`

val example_ffidiv_spec = Q.prove (
  `!b bv.
     BOOL b bv ==>
     app (p:'ffi ffi_proj) example_ffidiv_v [bv]
       (RUNTIME)
       (POST
          (λuv. &(UNIT_TYPE () uv) * &(¬b) * RUNTIME)
          (λev. &F)
          (λn conf bytes. &b * &(n = "exit" /\ conf = [] /\ bytes = [1w])
                   * RUNTIME)
          (λio. F))`,
  xcf' "example_ffidiv"
  >> xif
  >- (xlet_auto
      >- (xcon >- xsimpl)
      >> xapp >> xsimpl >> rw[] >> qexists_tac `x` >> xsimpl)
  >> xcon >> xsimpl);

val _ = export_theory();
