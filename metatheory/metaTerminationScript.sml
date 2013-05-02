open preamble 
open TypeSoundInvariantsTheory BigSmallInvariantsTheory;

val _ = new_theory "metaTermination";

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end

val (consistent_mod_env_def, consistent_mod_env_ind) =
  tprove_no_defn ((consistent_mod_env_def, consistent_mod_env_ind),
  WF_REL_TAC `measure (λ(a,b,c,d). LENGTH c)` >>
  rw []);
val _ = register "consistent_mod_env" consistent_mod_env_def consistent_mod_env_ind;
val _ = export_rewrites["consistent_mod_env_def"];

val _ = export_theory ();
