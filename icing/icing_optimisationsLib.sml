structure icing_optimisationsLib =
struct

open source_to_sourceProofsTheory listTheory;

local
  fun mk_single_rewriteFPexp_correct_thm th1 th2 =
    let
    val arglist =
      th1 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand;
    val arg =
      th2 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand
      |> listSyntax.dest_list |> fst |> hd (* TODO: Check length *);
    in
    SIMP_RULE std_ss [GSYM AND_IMP_INTRO] rewriteExp_compositional
    |> SPECL [arglist,arg]
    |> (fn th => MP th th1)
    |> (fn th => MP th th2)
    |> SIMP_RULE std_ss [APPEND]
    end;
  fun mk_rewriteFPexp_correct_thm_list thms correctthm =
  case thms of
   [] => correctthm
  | th1::thms =>
    mk_rewriteFPexp_correct_thm_list thms (mk_single_rewriteFPexp_correct_thm correctthm th1);
  fun mk_rewriteFPexp_list_correct_thm th1 =
    let
    val arglist =
      th1 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand;
    in
      SPEC arglist lift_rewriteFPexp_correct_list
      |> (fn th => MP th th1)
    end;
  fun mk_optimise_correct_thm th1 =
    let
    val arglist =
      th1 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand;
    in
      SPEC arglist (GEN_ALL is_optimise_correct_lift)
      |> (fn th => MP th th1)
    end;
in
  fun mk_opt_correct_thm thms =
  mk_rewriteFPexp_correct_thm_list (List.rev thms) empty_rw_correct
  |> mk_rewriteFPexp_list_correct_thm
  |> mk_optimise_correct_thm
end;

end
