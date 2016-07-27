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

  xcf "lnull" st \\
  fs [cf_mat_def] \\ irule local_elim \\ reduce_tac \\
  strip_tac THEN1 cheat (* nvm that for the moment *) \\
  fs [PMATCH_ROW_of_pat_def] \\
  (* - first row:
         + pat = Pcon (SOME (Short "nil") [])
         + pat_bindings pat [] = []
         therefore, insts can be replaced by ()
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(uv: unit). P []) (\_. T) (\(uv: unit). Q []))
     - second row:
         + pat = Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"]
         + pat_bindings pat [] = ["xs"; "x"]
         therefore, insts can be replaced by (vx, vxs)
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(vx, vxs). P [vx; vxs]) (\_. T) (\(vx, vxs). Q [vx; vxs]))
  *)
  cheat
)
