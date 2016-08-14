open preamble;
open libTheory astTheory evaluateTheory semanticPrimitivesTheory;
open semanticsTheory;
open semanticPrimitivesPropsTheory;
open evaluateComputeLib;
open primTypesTheory;
open terminationTheory;

val _ = new_theory "primSemEnv";

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
``add_to_sem_env (<| clock := 0; ffi := ffi; refs := []; defined_types := {}; defined_mods := {} |>,
                  <| c := eEmpty; v := eEmpty |>)
                 prim_types_program``
  |> SIMP_CONV(srw_ss())[add_to_sem_env_def, prim_types_program_def]
  |> CONV_RULE evaluate_conv
  |> (fn th => let
        val pth = SPEC_ALL prim_sem_env_def
        val th1 = mk_eq(rhs(concl pth),lhs(concl th)) |> EVAL |> EQT_ELIM
        in TRANS (TRANS pth th1) th end));

val prim_tdecs_def = Define
  `prim_tdecs =
    <|defined_mods := {};
      defined_exns :=
        {Short"Subscript"
        ;Short"Div"
        ;Short"Chr"
        ;Short"Bind"};
      defined_types :=
        {Short"option"
        ;Short"list"
        ;Short"bool"}|>`;

val prim_tenv_def = Define`
  prim_tenv = <|c := eEmpty; v := eEmpty; t := eEmpty|>`;

(* TODO: rename semantics and call semantics_init semantics instead? *)
val semantics_init_def = Define`
  semantics_init ffi =
    semantics <| sem_st := FST(THE (prim_sem_env ffi));
                 sem_env := SND(THE (prim_sem_env ffi));
                 tdecs := prim_tdecs;
                 tenv := prim_tenv |>`;

val _ = export_theory ();
