(*
  First test of Icing infrastructure
*)

open compilerTheory basisFunctionsLib basisComputeLib inferenceComputeLib basisProgTheory;
open machine_ieeeTheory;
open ml_translatorLib cfTacticsLib;
open preamble;

val _ = new_theory "icingTest";

Theorem extend_dec_ienv_empty:
   !ienv.
    extend_dec_ienv ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |> = ienv ∧
    extend_dec_ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |> ienv = ienv
Proof
  rw [extend_dec_ienv_def, inf_env_component_equality]
QED

Theorem nsAppend_assoc:
nsAppend (nsAppend A B) C = nsAppend A (nsAppend B C)
Proof
 Cases_on `A` \\ Cases_on `B` \\ Cases_on `C` \\ fs[namespaceTheory.nsAppend_def]
QED

Theorem infer_ds_split:
 ∀ prog1 prog2 conf1 state.
   infer_ds conf1 (prog1 ++ prog2) state =
   case (infer_ds conf1 prog1 state) of
   | (infer$Success ienv1, state2) =>
     (case infer_ds (extend_dec_ienv ienv1 conf1) prog2 state2 of
     | (infer$Success ienv2, state3) => (infer$Success (extend_dec_ienv ienv2 ienv1), state3)
     | res => res)
   | res => res
Proof
  Induct_on `prog1`  \\ rpt strip_tac \\ fs[]
  >- (
   fs [infer_d_def, st_ex_return_def, extend_dec_ienv_empty] \\ rpt (TOP_CASE_TAC \\ fs[]))
  \\ simp[infer_d_def, st_ex_return_def, st_ex_bind_def, extend_dec_ienv_empty]
  \\ rename1 `infer_d conf1 h state1`
  \\ Cases_on `infer_d conf1 h state1` \\ fs[]
  \\ Cases_on `q` \\ fs[]
  \\ rename1 `infer_ds (extend_dec_ienv conf2 conf1) prog1 r`
  \\ Cases_on `infer_ds (extend_dec_ienv conf2 conf1) prog1 r` \\ fs[]
  \\ Cases_on `q` \\ fs[extend_dec_ienv_def, Once nsAppend_assoc]
  \\ qmatch_goalsub_abbrev_tac `infer_ds ienv3 prog2 r'`
  \\ Cases_on `infer_ds ienv3 prog2 r'` \\ fs[]
  \\ Cases_on `q` \\ fs[]
QED

SIMP_RULE std_ss [infer_ds_split] (GEN_ALL (Q.SPECL [`ienv`, `prog1 ++ prog2`] infertype_prog_def));

val doppler_cml =
  process_topdecs `
  fun doppler (u:Word64.word, v:Word64.word, t:Word64.word) =
  let
  val t1 = Double.+ (Double.fromString "331.4") (Double.* (Double.fromString "0.6") t);
  in
  Double./ (Double.* (Double.~ t1) v) (Double.* (Double.+ t1 u) (Double.+ t1 u))
  end;`

val theEnv = rand (rhs (concl (basisTypeCheckTheory.basis_types)));

  EVAL  (Parse.Term `infertype_prog (^theEnv) (^doppler_cml)`);

val dopper_opt =
  EVAL (Parse.Term `source_to_source$compile_decs <| optimisations:= [fp_comm_gen FP_Add]; canOpt := T |> ^doppler_cml`)


val doppler_cml =
  ``"fun doppler (u:Word64.word, v:Word64.word, t:Word64.word) = let val t1 = Double.+ (Double.fromString \"331.4\") (Double.* (Double.fromString \"0.6\") t); in Double./ (Double.* (Double.~ t1) v) (Double.* (Double.+ t1 u) (Double.+ t1 u)) end"``;

Definition test_def:
  test x = fp64_add roundTiesToEven x x
End

val r = translate test_def;

val simple_fun =
  ``"fun f () = print \"Hello\";"``;

val [empty_ffi] = decls "empty_ffi";
val _ = computeLib.monitoring := SOME (same_const empty_ffi);

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
      basicComputeLib.add_basic_compset
      ],
     computeLib.Defs
      [basisProgTheory.basis_def
      ],
    computeLib.Tys
    [    ]
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp

val test = EVAL (Parse.Term `compile_icing basis init_config source_to_source$no_fp_opt_conf (^doppler_cml)`);
EVAL (Parse.term `infertype_prog
