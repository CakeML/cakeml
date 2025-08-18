(*
  Translation from CakeML floating-point kernels to FloVer input
*)

Theory CakeMLtoFloVer
Ancestors
  (* CakeML *)
  semantics
  (* FloVer *)
  RealIntervalInference ErrorIntervalInference
  CertificateChecker Expressions Commands IEEE_connection
  update
Libs
  preamble

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
   | (FP_uop FP_Sqrt, [e1]) =>
   (case toFloVerExp ids e1 of
    | NONE => NONE
    | SOME fexp1 => SOME (Expressions$Unop Sqrt fexp1))
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
Theorem toFloVerExp_ind[allow_rebind] = SIMP_RULE std_ss [] toFloVerExp_ind;

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

Definition getError_def:
  getError decl P (err:real) =
  case getErrorbounds decl P of
  | (NONE, err) => (NONE)
  | (SOME (bounds, cmd, _), _) =>
    case FloverMapTree_find (getRetExp (toRCmd cmd)) bounds of
    | NONE => NONE
    | SOME (iv,errD) => (SOME errD)
End
