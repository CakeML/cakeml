(*
  First test of Icing infrastructure
*)
(* CakeML *)
open compilerTheory basisFunctionsLib basisComputeLib basisProgTheory;
(* FloVer *)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
(* Icing *)
open CakeMLtoFloVerTheory;
(* HOL libs *)
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "icingTest";

Definition doppler_hol_def:
  doppler (u:word64, v:word64, t:word64) =
  let
  t1 = fp64_add roundTiesToEven (4644537666646730342w:word64)
         (fp64_mul roundTiesToEven (4603579539098121011w:word64) t)
  in
  fp64_div roundTiesToEven
  (fp64_mul roundTiesToEven
   (fp64_negate t1)
   v)
  (fp64_mul roundTiesToEven
   (fp64_add roundTiesToEven t1 u)
   (fp64_add roundTiesToEven t1 u))
End

Definition doppler_cml_def:
  doppler_cml =
  Dletrec
    (Locs <|row := 2; col := 3; offset := 0|>
     <|row := 7; col := 5; offset := 0|>)
    [("doppler","",
      FpOptimise Opt
      (Mat (Var (Short ""))
        [(Pcon NONE [Pvar "u"; Pvar "v"; Pvar "t"],
          Let (SOME "t1")
            (App (FP_bop FP_Add)
              [
                Lit (Word64 (4644537666646730342w:word64));
                (App (FP_bop FP_Mul)
                 [
                   Lit (Word64 (4603579539098121011w:word64));
                   Var (Short  "t")
                 ])
              ])
            (App (FP_bop FP_Div)
             [
               (App (FP_bop FP_Mul)
                [
                  (App (FP_uop FP_Neg)
                   [Var (Short "t1")]);
                  Var (Short "v")
                ]);
               (App (FP_bop FP_Mul)
                [
                  (App (FP_bop FP_Add)
                  [Var (Short "t1");
                   Var (Short "u")]);
                  (App (FP_bop FP_Add)
                  [Var (Short "t1");
                   Var (Short "u")])
                ])
             ])
           )]))]
End

Theorem doppler_opt =
  EVAL ``HD (source_to_source$compile_decs
           <| optimisations := [
               (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
                Terop FP_Fma (Var 0) (Var 1) (Var 2))];
               canOpt := T |>
           [doppler_cml])``;

Definition doppler_body_def:
  doppler_body =
    case doppler_cml of
    | Dletrec _ [ (_, _, e)] => e
End

Definition optimised_doppler_body_def:
  optimised_doppler_body =
    case (^(rhs (concl doppler_opt))) of
    | Dletrec _ [ (_, _, e)] => e
End

(*
Definition isMorePrecise_def:
  isMorePrecise f1 f2 Gamma P =
  let
    floverF1 = THE (toFloVerCmd [] 0 (rm_top_match (strip f1)));
    floverF2 = THE (toFloVerCmd [] 0 (rm_top_match (strip f2)));
    errsF1 = THE (getErrorbounds f1 Gamma P);
    errsF2 = THE (getErrorbounds f2 Gamma P);
  in
    case FloverMapTree_find (getRetExp floverF1) errsF1 of
    | NONE => F
    | SOME (iv1, err1) =>
    (case FloverMapTree_find (getRetExp floverF2) errsF2 of
    | NONE => F
    | SOME (iv2, err2) => (err2:real <= err1))
End
*)

val Gamma = EVAL ``FloverMapTree_insert (Var 0) M64 (
FloverMapTree_insert (Var 1) M64 (
FloverMapTree_insert (Var 2) M64 (
FloverMapTree_insert (Var 3) M64 (
FloverMapTree_insert (Var 4) M64 (
FloverMapTree_insert (Var 5) M64 FloverMapTree_empty)))))``;

val P = ``λ x:num. (1,2):(real#real)``;

val test =
EVAL (Parse.Term `
      getErrorbounds
      optimised_doppler_body
      ^(rhs (concl Gamma))
      ^P`);

(*
val test2 =
EVAL (Parse.Term `
      isMorePrecise
      doppler_body
      optimised_doppler_body
      ^(rhs (concl Gamma))
      ^P`)
*)
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER, binary_ieeeTheory.float_to_real_def];

val doppler_def = EVAL ``
(THE (toFloVerCmd [] 0 (rm_top_match (strip optimised_doppler_body))))``

val real_iv_bounds = EVAL ``inferIntervalboundsCmd
(SND (THE (toFloVerCmd [] 0 (rm_top_match (strip optimised_doppler_body)))))
(λ x. (1,2)) FloverMapTree_empty``;

val typeMap = EVAL (Parse.Term `case (TypeValidator$getValidMapCmd  ^(rhs (concl Gamma))
(SND (THE (toFloVerCmd [] 0 (rm_top_match (strip optimised_doppler_body)))))
FloverMapTree_empty) of Succes t => t`);

val error_bounds = curry save_thm "error_bounds_thm" (EVAL (Parse.Term `inferErrorboundCmd
(SND (THE (toFloVerCmd [] 0 (rm_top_match (strip optimised_doppler_body)))))
^(rhs (concl typeMap))
(THE (^(rhs (concl real_iv_bounds))))
FloverMapTree_empty`));

(* The "additional"/meta-theorem theorem:
Theorem optimised_doppler_more_accuracte:
  error (optimised_doppler) ≤ error (doppler_cml)
Proof
  (* TODO *)
  cheat
QED
 *)

val _ = export_theory();

(** FAILED ATTEMPTS below

Definition strip_noopt_def:
  strip_noopt (Lit l) = Lit l /\
  strip_noopt (Var x) = Var x /\
  strip_noopt (Raise e) =
    Raise (strip_noopt e) /\
  strip_noopt (Handle e pes) =
    Handle (strip_noopt e) (MAP (\ (p,e). (p, strip_noopt e)) pes) /\
  strip_noopt (Con mod exps) =
    Con mod (MAP strip_noopt exps) ∧
  strip_noopt (Fun s e) =
    Fun s (strip_noopt e) /\
  strip_noopt (ast$App op exps) =
    (App op (MAP strip_noopt exps)) /\
  strip_noopt (Log lop e2 e3) =
    Log lop (strip_noopt e2) (strip_noopt e3) /\
  strip_noopt (If e1 e2 e3) =
    If (strip_noopt e1) (strip_noopt e2) (strip_noopt e3) /\
  strip_noopt (Mat e pes) =
    Mat (strip_noopt e) (MAP (\ (p,e). (p, strip_noopt e)) pes) /\
  strip_noopt (Let so e1 e2) =
    Let so (strip_noopt e1) (strip_noopt e2) /\
  strip_noopt (Letrec ses e) =
    Letrec (MAP (\ (s1,s2,e). (s1, s2, strip_noopt e)) ses) (strip_noopt e) /\
  strip_noopt (Tannot e t) =
    Tannot (strip_noopt e) t /\
  strip_noopt (Lannot e l) =
    Lannot (strip_noopt e) l /\
  strip_noopt (FpOptimise NoOpt e) =
    (strip_noopt e) ∧
  strip_noopt (FpOptimise sc e) =
    FpOptimise sc (strip_noopt e)
Termination
  WF_REL_TAC `measure exp_size` \\ fs[]
  \\ rpt conj_tac
  >- (Induct_on `ses` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod'` assume_tac) \\ fs[])
End

Definition strip_noopt_exps_def:
  strip_noopt_exps [] = [] ∧
  strip_noopt_exps [e] = [strip_noopt e] ∧
  strip_noopt_exps (e1::es) = (strip_noopt_exps [e1]) ++ (strip_noopt_exps es)
End

Definition strip_noopt_decs_def:
  strip_noopt_decs [] = [] /\
  strip_noopt_decs [Dlet l p e] = [Dlet l p (HD (strip_noopt_exps [e]))] /\
  strip_noopt_decs [Dletrec ls vexps] =
    [Dletrec ls (MAP (\ (v1,v2,e). (v1,v2,HD (strip_noopt_exps [e]))) vexps)] /\
  strip_noopt_decs [Dtype l t] = [Dtype l t] /\
  strip_noopt_decs [Dtabbrev l vars t ast] = [Dtabbrev l vars t ast] /\
  strip_noopt_decs [Dexn l c asts] = [Dexn l c asts] /\
  strip_noopt_decs [Dmod m decls] = [Dmod m (strip_noopt_decs decls)] /\
  strip_noopt_decs [Dlocal decls1 decls2] =
    [Dlocal (strip_noopt_decs decls1) (strip_noopt_decs decls2)] /\
  strip_noopt_decs (d1::d2::ds) = strip_noopt_decs [d1] ++ strip_noopt_decs (d2::ds)
Termination
  wf_rel_tac `measure dec1_size`
End

val cml_thm = translate doppler_def;
val cml_def = fetch "-" "doppler_v_def";

EVAL “rewriteFPexp [fp_comm_gen FP_Add] (App (FP_bop FP_Add) [Var (Short "t1"); Var (Short "t2")])”
                    (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
                      Terop FP_Fma (Var 0) (Var 1) (Var 2))] ”

val cml_opt = let val theDef = rhs (concl cml_def); in EVAL (Parse.Term `strip_noopt_decs ^theDef`) end;


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
(*
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
*)
*)
