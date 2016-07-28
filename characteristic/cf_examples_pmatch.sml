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

val lnull_spec = Q.prove (
  `!lv a l.
     app (p:'ffi ffi_proj) ^(fetch_v "lnull" st) [lv]
       (cond (LIST_TYPE a l lv))
       (\bv. cond (BOOL (l = []) bv))`,

  xcf "lnull" st \\ xpull \\
  Cases_on `l` \\ fs [LIST_TYPE_def] \\
  xmatch \\ xret \\ xsimpl \\ EVAL_TAC
)

