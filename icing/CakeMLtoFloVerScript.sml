(*
 Definition of translation to FloVer
*)
(* CakeML *)
open compilerTheory;
(* FloVer *)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory
     CertificateCheckerTheory ExpressionsTheory CommandsTheory
     IEEE_connectionTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVer";

(** Translation from CakeML AST to FloVer AST **)

Definition fpBopToFloVer_def:
  fpBopToFloVer (FP_Add) = Expressions$Plus ∧
  fpBopToFloVer (FP_Sub) = Sub ∧
  fpBopToFloVer (FP_Mul) = Mult ∧
  fpBopToFloVer (FP_Div) = Div
End

Type nameP[pp] = “:(string, string) id # num”;

Definition lookupCMLVar_def:
  lookupCMLVar n (ns:nameP list) = FIND (λ (m,i). n = m) ns
End

Definition lookupFloVerVar_def:
  lookupFloVerVar n (ns:nameP list) = FIND (λ (m,i). n = i) ns
End

Definition appendCMLVar_def:
  appendCMLVar n i ns =
  case (lookupCMLVar n ns) of
  | SOME _ => ns
  | NONE => (n,i)::ns
End

(** WAS: prepareVars **)
Definition getFloVerVarMap_def:
  getFloVerVarMap ([]:(((string,string) id) list)) = SOME ([],[], 0:num) ∧
  getFloVerVarMap (v1::vs) =
  case getFloVerVarMap vs of
  | NONE => NONE
  | SOME (ns, ids, freshId) =>
  case lookupCMLVar v1 ids of
  | SOME _ => NONE (* Double occurrence of variable *)
  | NONE =>
  case v1 of
  | Short s => SOME (ns++[freshId], appendCMLVar v1 freshId ids, freshId+1)
  | _ => NONE
End

(* WAS: prepareGamma *)
Definition buildFloVerTypeMap_def:
  buildFloVerTypeMap [] = FloverMapTree_empty ∧
  buildFloVerTypeMap (n1::ns) = FloverMapTree_insert (Var n1) M64 (buildFloVerTypeMap ns)
End

Definition toFloVerConst_def:
  toFloVerConst (ast$Lit (Word64 w)) = SOME w  ∧
  toFloVerConst _ = NONE
End

Definition toFloVerExp_def:
  toFloVerExp ids (ast$Var x) =
  (case (lookupCMLVar x ids) of
  | SOME (_,i) => SOME (Expressions$Var i)
  | _ => NONE) ∧
  toFloVerExp ids (App op exps) =
  (case (op, exps) of
   | (FpFromWord, [e1]) =>
   (case toFloVerConst e1 of
    | NONE => NONE
    |SOME w => SOME (Expressions$Const M64 w))
   | (FP_uop FP_Neg, [e1]) =>
   (case toFloVerExp ids e1 of
    | NONE => NONE
    | SOME fexp1 => SOME (Expressions$Unop Neg fexp1))
   | (FP_bop bop, [e1; e2]) =>
   (case toFloVerExp ids e1, toFloVerExp ids e2 of
    | (SOME fexp1, SOME fexp2) =>
      SOME (Expressions$Binop (fpBopToFloVer bop) fexp1 fexp2)
    | _, _ => NONE)
   | (FP_top _, [e1; e2; e3]) =>
   (case toFloVerExp ids e1, toFloVerExp ids e2, toFloVerExp ids e3 of
    | SOME fexp1, SOME fexp2, SOME fexp3 =>
      SOME (Expressions$Fma fexp2 fexp3 fexp1)
    | _, _, _ => NONE)
   | (_, _) => NONE)
  ∧
  toFloVerExp ids (FpOptimise NoOpt e) = toFloVerExp ids e ∧
  toFloVerExp _ _ = NONE
End

(* Better induction theorem *)
val toFloVerExp_ind = curry save_thm "toFloVerExp_ind"
  (SIMP_RULE std_ss [] toFloVerExp_ind);

Definition toFloVerCmd_def:
  toFloVerCmd ids freshId (ast$Let so e1 e2) =
    (case so of
     | NONE => NONE
     | SOME x =>
     (case toFloVerExp ids e1 of
      |NONE => NONE
      |SOME fexp1 =>
      (case lookupCMLVar (Short x) ids of
       | SOME _ => NONE (* no SSA form*)
       | NONE =>
       case toFloVerCmd (appendCMLVar (Short x) freshId ids) (freshId+1) e2 of
       | NONE => NONE
       | SOME (ids2, freshId2, cmd1) =>
         SOME (ids2, freshId2, Commands$Let M64 freshId fexp1 cmd1)))) ∧
  toFloVerCmd ids freshId (ast$App op es) =
    (case toFloVerExp ids (App op es) of
    | NONE => NONE
    | SOME fexp1 => SOME (ids, freshId, Commands$Ret fexp1)) ∧
  toFloVerCmd ids freshId (ast$Var x) =
    (case toFloVerExp ids (Var x) of
    | NONE => NONE
    | SOME fexp1 => SOME (ids, freshId, Commands$Ret fexp1)) ∧
  toFloVerCmd ids freshId (ast$Lit l) =
    (case toFloVerExp ids (Lit l) of
    | NONE => NONE
    | SOME fexp1 => SOME (ids, freshId, Commands$Ret fexp1)) ∧
  toFloVerCmd ids freshId (FpOptimise NoOpt e) = toFloVerCmd ids freshId e ∧
  toFloVerCmd _ _ _ = NONE
End

Definition toFloVerEnv_def:
  toFloVerEnv (env:v sem_env)
              (idMap:((string, string) id # num) list)=
  λ (x:num).
  case lookupFloVerVar x idMap of
  |NONE => NONE
  |SOME (n,i) =>
  (case nsLookup env.v n of
   |SOME (Real r) => SOME r
   |_ => NONE)
End

(** Translation from FP ops to Real ops **)

Definition getRealCmp_def:
  getRealCmp (FP_Less) = Real_Less ∧
  getRealCmp (FP_LessEqual) = Real_LessEqual ∧
  getRealCmp (FP_Greater) = Real_Greater ∧
  getRealCmp (FP_GreaterEqual) = Real_GreaterEqual ∧
  getRealCmp (FP_Equal) = Real_Equal
End

Definition getRealUop_def:
  getRealUop (FP_Abs) = Real_Abs ∧
  getRealUop (FP_Neg) = Real_Neg ∧
  getRealUop (FP_Sqrt) = Real_Sqrt
End

Definition getRealBop_def:
  getRealBop (FP_Add) = Real_Add ∧
  getRealBop (FP_Sub) = Real_Sub ∧
  getRealBop (FP_Mul) = Real_Mul ∧
  getRealBop (FP_Div) = Real_Div
End

(* WAS: toRealExp : CakeML AST -> CakeML AST *)
Definition realify_def:
  realify (Lit (Word64 w)) = Lit (Word64 w) (* RealFromFP added in App case *)∧
  realify (Lit l) = Lit l ∧
  realify (Var x) = Var x ∧
  realify (Raise e) = Raise (realify e) ∧
  realify (Handle e pes) =
    Handle (realify e) (MAP (\ (p,e). (p, realify e)) pes) ∧
  realify (Con mod exps) = Con mod (MAP realify exps) ∧
  realify (Fun s e) = Fun s (realify e) ∧
  realify (App op exps) =
    (let exps_real = MAP realify exps in
     case op of
     | FpFromWord => App  RealFromFP exps_real
     | FP_cmp cmp => App (Real_cmp (getRealCmp cmp)) exps_real
     | FP_uop uop => App (Real_uop (getRealUop uop)) exps_real
     | FP_bop bop => App (Real_bop (getRealBop bop)) exps_real
     | FP_top _ =>
     (case exps of
      | [e1; e2; e3] => App (Real_bop (Real_Add)) [
                          App (Real_bop (Real_Mul)) [realify e2; realify e3]; realify e1]
      | _ => App op exps_real) (* malformed expression, return garbled output *)
     | _ => App op exps_real) ∧
  realify (Log lop e2 e3) =
    Log lop (realify e2) (realify e3) ∧
  realify (If e1 e2 e3) =
    If (realify e1) (realify e2) (realify e3) ∧
  realify (Mat e pes) =
    Mat (realify e) (MAP (λ(p,e). (p, realify e)) pes) ∧
  realify (Let so e1 e2) =
    Let so (realify e1) (realify e2) ∧
  realify (Letrec ses e) =
    Letrec (MAP (λ (s1,s2,e). (s1, s2, realify e)) ses) (realify e) ∧
  realify (Tannot e t) = Tannot (realify e) t ∧
  realify (Lannot e l) = Lannot (realify e) l ∧
  realify (FpOptimise sc e) = FpOptimise sc (realify e)
Termination
  wf_rel_tac ‘measure exp_size’ \\ fs[astTheory.exp_size_def] \\ rpt conj_tac
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

Definition stripFuns_def:
  stripFuns (Fun var body):(((string, string) id) list# ast$exp)=
    (let (vars, body) = stripFuns body in
    (Short var :: vars, body)) ∧
  stripFuns e = ([], e)
End

Definition freevars_list_def:
  freevars_list [] = [] /\
  freevars_list [ast$Var n] = [ n ] /\
  freevars_list [Lit l] = [] /\
  freevars_list [Raise e] = freevars_list [e] /\
  freevars_list [Handle e pes] =
    FOLDL (\ vars. \ (p,e). (freevars_list [e]) ++ vars) (freevars_list [e]) pes /\
  freevars_list [Con id es] = freevars_list es /\
  freevars_list [Fun s e] = FILTER (λ x. x ≠ Short s) (freevars_list [e]) /\
  freevars_list [App op es] = freevars_list es /\
  freevars_list [Log lop e1 e2] = (freevars_list [e1] ++ freevars_list [e2]) /\
  freevars_list [If e1 e2 e3] = (freevars_list [e1] ++ freevars_list [e2] ++ freevars_list [e3]) /\
  freevars_list [Mat e pes] =
    FOLDL (\ vars. \ (p,e). (freevars_list [e]) ++ vars) (freevars_list [e]) pes /\
  freevars_list [Let x e1 e2] =
    freevars_list [e1] ++
    (case x of
     | NONE => freevars_list [e2]
     | SOME s => FILTER (λ x. x ≠ Short s) (freevars_list [e2])) ∧
  freevars_list [Letrec fs e] = [] (* TODO *) /\
  freevars_list [Tannot e t] = freevars_list [e] /\
  freevars_list [Lannot e l] = freevars_list [e] /\
  freevars_list [FpOptimise opt e] = freevars_list [e] /\
  freevars_list (e1::es) =
    freevars_list [e1] ++ freevars_list es
Termination
  wf_rel_tac `measure exp6_size` \\ fs[]
  \\ Induct_on `pes` \\ fs[]
  \\ rpt strip_tac \\ simp[astTheory.exp_size_def]  \\ rveq
  \\ res_tac
  >- (simp[astTheory.exp_size_def])
  \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]
End

Definition checkFreevars_def:
  checkFreevars [] _ = T ∧
  checkFreevars (x::xs) fVars = if (MEM x fVars) then checkFreevars xs fVars else F
End

Definition computeErrorbounds_def:
  computeErrorbounds theCmd P Gamma =
  let theCmd = toRCmd theCmd in
    case inferIntervalboundsCmd theCmd P FloverMapTree_empty of
    | NONE => NONE
    | SOME theRealBounds =>
    case getValidMapCmd Gamma theCmd FloverMapTree_empty of
    | Fail _ => NONE
    | FailDet _ _ => NONE
    | Succes typeMap =>
    case inferErrorboundCmd theCmd typeMap theRealBounds FloverMapTree_empty of
    | NONE => NONE
    | SOME theErrBounds =>
    case (CertificateCheckerCmd theCmd theErrBounds P Gamma)
    of SOME Gamma => SOME theErrBounds
    | _ => NONE
End

Definition mkFloVerPre_def:
  mkFloVerPre (P:(string,string) id -> (real#real)) (varMap:nameP list) =
  λ n:num.
  case lookupFloVerVar n varMap of
  | NONE => (0,0)
  | SOME (x,m) => P x
End

Definition getErrorbounds_def:
  getErrorbounds decl P =
  if (LENGTH decl ≠ 1) then (NONE, SOME "Only a single kernel is currently supported") else
  case decl of
  | [Dlet loc (Pvar p) e] =>
    (let (vars, body) = stripFuns e in
     case body of
     | FpOptimise NoOpt body' =>
     (case getFloVerVarMap vars of
      | NONE =>
      (NONE,
       SOME "Could not build a valid variable map for kernel. Possibly due to double binding of variables")
      | SOME (floverVars, varMap, freshId) =>
      (* check that freevars and vars agree: *)
      if (checkFreevars vars (freevars_list [body]))
      then
      let
      Gamma = buildFloVerTypeMap floverVars;
      in
      case (toFloVerCmd varMap freshId body) of
      | NONE => (NONE, SOME "Could not translate body to valid FloVer AST")
      | SOME (theIds, freshId, theCmd) =>
      case computeErrorbounds theCmd (mkFloVerPre P varMap) Gamma of
      | SOME theBounds => (SOME (theBounds, theCmd, vars), NONE)
      | NONE => (NONE, SOME "Could not compute or check roundoff errors for FloVer AST")
      else (NONE,SOME "The free variables of the function body do not agree with the parameters specified"))
     | _ => (NONE, SOME "Body must start with NoOpt annotation"))
    | _ => (NONE, SOME "Only Dlet is currently supported")
End

Definition isOkError_def:
  isOkError decl P (err:real) =
  case getErrorbounds decl P of
  | (NONE, err) => (NONE, err)
  | (SOME (bounds, cmd, _), _) =>
    case FloverMapTree_find (getRetExp (toRCmd cmd)) bounds of
    | NONE => (NONE, SOME "Something went wrong internally. Please report this")
    | SOME (iv,errD) => (SOME (errD ≤ err), NONE)
End

val _ = export_theory ();

    (**
Definition Eval_oracle_def:
  Eval_oracle env exp P oracle =
  ∀ refs.
  ∃ res.
End


Theorem evaluate_const:
  Eval env (App FpFromWord [Lit (Word64 w)]) ((=) (FP_WordTree (Fp_const w)))
Proof
  fs[ml_translatorTheory.Eval_def, ml_progTheory.eval_rel_def]
  \\ EVAL_TAC \\ fs[]
QED

Theorem evaluate_var:
  nsLookup env.v (Short x) = SOME fp ⇒
  Eval env (Var (Short x)) ((=) fp)
Proof
  fs[ml_translatorTheory.Eval_def, ml_progTheory.eval_rel_def]
  \\ EVAL_TAC \\ fs[]
QED

Theorem evaluate_bop:
  Eval env e1 ((=) (FP_WordTree fp1)) ∧
  Eval env e2 ((=) (FP_WordTree fp2)) ⇒
  Eval env (App (FP_bop bop) [e1;e2]) ((=) (FP_WordTree (Fp_bop bop fpT1 fpT2)))
Proof
  rpt strip_tac
  \\ simp [ml_translatorTheory.Eval_def, ml_progTheory.eval_rel_def]
  \\ simp[terminationTheory.evaluate_def, astTheorsemanticPrimitivesTheoryy.getOpClass_def]
  \\ EVAL_TAC \\ fs[]



exception valError of string;

fun translate t =
  case free_vars t of
  v::vs => raise valError "No free vars allowed"
  | [] =>
**)

(** UNUSED:

Definition isFloVerExps_def:
  isFloVerExps [Var x] = T ∧
  isFloVerExps [App op exps] =
    (isFloVerExps exps  ∧
    (case op of
     | FP_bop _ => LENGTH exps = 2
     | FP_uop FP_Neg => LENGTH exps = 1
     | FP_top _ => LENGTH exps = 3
     | _ =>  F)) ∧
  isFloVerExps [e] = F ∧
  isFloVerExps (e1::es) = (isFloVerExps [e1] ∧ isFloVerExps es)
Termination
  wf_rel_tac `measure exp6_size`
End

Definition isFloVerCmd_def:
  isFloVerCmd (Let so e1 e2) =
  (case so of
   | SOME x => isFloVerExps [e1] ∧ isFloVerCmd e2
   | NONE => F) ∧
  isFloVerCmd (App op exps) = isFloVerExps [App op exps] ∧
  isFloVerCmd (Var x) = T ∧
  isFloVerCmd _ = F
End

Definition stripAssert_def:
  stripAssert (Let NONE P body) =
    (case P of
    | App op [fN; P] =>
      if (op = Opapp ∧ fN = Var (Long "Runtime" (Short "assert")))
      then SOME (P, body)
      else NONE
    | _ => NONE) ∧
  stripAssert _ = NONE
End

Definition prepareKernel_def:
  prepareKernel exps =
    case exps of
    | NONE => NONE
    | SOME exps =>
      if (LENGTH exps ≠ 1)
      then NONE
      else
        case exps of
        | [(n1, n2, e)] =>
        let
          fN = stripNoOpt e;
          (vars, body) = stripFuns fN in
        do
          (P, body) <- stripAssert body;
          (* FIXME: should not need to strip noopt annotations here *)
          return (n2::vars, P, stripNoOpt body);
        od
        | _ => NONE
End

(**
  Function getInterval
  Argument:
    A single CakeML AST describing an interval constraint
    The argument must have the shape (lo ≤ x) ∧ (x ≤ hi)
  Returns:
    The CakeML variable constraint by the interval, the lower bound,
    the upper bound
**)
Definition getInterval_def:
  getInterval (Log lop e1 e2) =
    (if (lop <> And) then NONE
    else
      case e1 of
      | App (FP_cmp FP_LessEqual) [c1; var1] =>
        (case e2 of
         | App (FP_cmp FP_LessEqual) [var2; c2] =>
         if (var1 ≠ var2) then NONE
         else
           (case c1 of
           | App FpFromWord [Lit (Word64 w1)] =>
             (case c2 of
             | App FpFromWord [Lit (Word64 w2)] =>
               (case var1 of
               | Var (Short x) =>
               if (fp64_isFinite w1 ∧ fp64_isFinite w2)
               then SOME (x, (fp64_to_real w1, fp64_to_real w2))
               else NONE
               | _ => NONE)
             | _ => NONE)
           | _ => NONE)
         | _ => NONE)
      | _ => NONE) ∧
  getInterval _ = NONE
End

(**
  Function toFloVerPre
  Arguments:
    CakeML AST of a precondition
    a 1-1 map from CakeML to FloVer variables
    The AST of the precondition must be encoded exactly that the top-most
    conjunct joins either a single constraint (lo ≤ x) ∧ (x ≤ hi), or
    that it joins a single constraint with the remainder of the precondition
    ((lo ≤ x) ∧ (x ≤ hi)) ∧ precondition_remainder
  Returns:
    A FloVer encoding of the precondition as a function from numbers to
    reals, and a list of variables bound in the precondition
    The list is used to make sure that a variable can only be bound once
    by the precondition in CakeML
**)
Definition toFloVerPre_def:
  toFloVerPre [] ids = NONE ∧
  toFloVerPre [Log And e1 e2] ids =
    (* base case: (lo ≤ x ∧ x <= hi) *)
    (case getInterval (Log And e1 e2) of
    | SOME (x, lo, hi) =>
      (case lookupCMLVar (Short x) ids of
      | NONE => NONE
      | SOME (y, n) =>
        SOME ((λ (z:num). if z = n then (lo,hi) else (0:real, 0:real)), [n]))
    (* compound case: ((lo <= x ∧ x ≤ hi) ∧ remainder *)
    | NONE =>
      (* get an interval for the left-hand side of the conjunct *)
      case getInterval e1 of
      | NONE => NONE
      | SOME (x, lo, hi) =>
      (* get a FloVer variable for the CakeML var from the mapping *)
      case lookupCMLVar (Short x) ids of
      | NONE => NONE
      | SOME (y, n) =>
      (* recursive translation *)
      case toFloVerPre [e2] ids of
      | NONE => NONE
      | SOME (P, bVars) =>
      (* check whether the variable is already bound *)
      case FIND (λ m. n = m) bVars of
      | SOME _ => NONE  (* cannot rebind variable *)
      | NONE =>
        SOME ((λ (z:num). if z = n then (lo,hi) else P z), n :: bVars)) ∧
  toFloVerPre _ _ = NONE
End

**)
