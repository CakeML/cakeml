(*
 Functional big-step semantics for evaluation of Dafny programs.
*)

open preamble
open dafny_astTheory
open result_monadTheory
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluate";

Type dafny_result = “:'a dafny_semanticPrimitives$result”
Type resultM = “:'a result_monad$result”
Type program = “:module list”

(* TODO? Move to dafny_ast *)
Definition method_name_def:
  method_name (Method _ _ _ _ _ _ nam _ _ _ _ _ _) = nam
End

Definition method_body_def:
  method_body (Method _ _ _ _ _ _ _ _ _ _ body _ _) = body
End

Definition dest_classitem_def:
  dest_classitem (ClassItem_Method m) = m
End

(* Helper functions to factor out deep pattern matching and simplifying
 * assumptions*)

(* TODO Check whether there is overlap with definitions in dafny_to_cakeml *)

(* Destructs a simple module, stripping away the ClassItem_Method wrapper in the
 * process
 *
 * A simple module has no attributes, does not require extern, and only contains
 * the default class without type parameters, super classes, fields or
 * attributes. *)
Definition dest_simple_module_def:
  dest_simple_module (Module mod_nam [] F
                             (SOME
                              [ModuleItem_Class
                               (Class cls_nam cls_enclosingM [] []
                                      [] cls_body [])])) =
  (if cls_nam ≠ (Name "__default") then
     fail "dest_simple_module: class name was not __default"
   else if mod_nam ≠ dest_Ident cls_enclosingM then
     fail "dest_simple_module: unexpectedly, mod_nam and cls_enclosingM did not \
         \match"
   else
     return (mod_nam, MAP dest_classitem cls_body)) ∧
  dest_simple_module _ = fail "dest_simple_module: Not a simple module"
End

(* Simple call = calling a method without arguments, return value, or inheritance *)
Definition dest_simple_call_def:
  dest_simple_call c =
  case c of
  | Call (Companion (Ident mod_nam::rest) [])
         (CallName method_nam NONE NONE F (CallSignature [] []))
         [] [] NONE =>
      if rest ≠ [] ∧ rest ≠ [Ident (Name "__default")] then
        fail "dest_simple_call: not a simple call"
      else
        return (mod_nam, method_nam)
  | _ => fail "dest_simple_call: not a simple call"
End

Definition is_simple_method_def:
  is_simple_method (m: method): bool =
  let (_, isStatic, hasBody,
       outVarsAreUninitFieldsToAssign,
       wasFunction, overridingPath, _,
       typeParams, params, inheritedParams, _, outTypes, outVars) = dest_Method m in
    isStatic ∧ hasBody ∧
    ¬outVarsAreUninitFieldsToAssign ∧ ¬wasFunction ∧
    overridingPath = NONE ∧ typeParams = [] ∧
    params = [Formal (VarName "__noArgsParameter")
                     (Seq (Primitive String)) []] ∧
    inheritedParams = [Formal (VarName "__noArgsParameter")
                              (Seq (Primitive String)) []] ∧
    outTypes = [] ∧ outVars = SOME []
End

(* Find main function in environment *)

Definition is_main_def:
  (* Derived by looking at how Main is compiled *)
  is_main (m: method): bool =
  (is_simple_method m ∧ method_name m = Name "Main")
End

Definition main_call_def:
  main_call (env: sem_env): statement resultM =
  let main = FILTER (λ(_, m). is_main m) env.methods in
    case main of
    | [((mod_nam, method_nam), m)] =>
        do
          (* Derived by looking at how a function like Main is called *)
          on <<- Companion [Ident mod_nam] [];
          callName <<- CallName method_nam NONE NONE F (CallSignature [] []);
          return (Call on callName [] [] NONE)
        od
    | [] => fail "main_call: Found no Main"
    | _ => fail "main_call: Found more than one Main"
End

(* Set up initial environment containing all methods defined in the Dafny
   program *)

Definition env_from_mod_def:
  env_from_mod (mod: module) =
  do
    (mod_name, methods) <- dest_simple_module mod;
    method_names <<- MAP method_name methods;
    method_path <<- MAP (λy. (mod_name, y)) method_names;
    return (ZIP (method_path, methods))
  od
End

Definition init_env_def:
  init_env (p: program): sem_env resultM =
  do
    methods <- result_mmap env_from_mod p;
    methods <<- FLAT methods;
    return <| methods := methods |>
  od
End

(* Functional big-step semantics *)

(* following three definitions/theorems were adapted from
 * semantics/evaluateScript.sml *)
Definition fix_clock_def:
  fix_clock s (s', res) =
  (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End

Triviality fix_clock_IMP:
  fix_clock s x = (s1, res) ==> s1.clock <= s.clock
Proof
  Cases_on ‘x’ \\ rw[fix_clock_def] \\ gvs[]
QED

Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End

(* TODO move to semantic primitives? *)
Datatype:
  exp_or_val = Exp dafny_ast$expression | Val dafny_semanticPrimitives$value
End

(* TODO move to semantic primitives? *)
Definition is_lop_def[simp]:
  is_lop And = T ∧
  is_lop Or = T ∧
  is_lop _ = F
End

(* TODO move to semantic primitives? *)
Definition do_lop_def:
  do_lop bop v e =
  if (bop = And ∧ v = BoolV T) ∨ (bop = Or ∧ v = BoolV F) then SOME (Exp e)
  else if (bop = And ∧ v = BoolV F) ∨ (bop = Or ∧ v = BoolV T) then SOME (Val v)
  else NONE
End

Definition do_bop_def:
  do_bop Lt el er =
  (case (el, er) of
   | (IntV vl, IntV vr) => SOME (BoolV (vl < vr))
   | _ => NONE)
  ∧
  do_bop (Plus F) el er =
  (case (el, er) of
   | (IntV vl, IntV vr) => SOME (IntV (vl + vr))
   | _ => NONE)
  ∧
  do_bop (Minus F) el er =
  (case (el, er) of
   | (IntV vl, IntV vr) => SOME (IntV (vl - vr))
   | _ => NONE)
  ∧
  do_bop (Times F) el er =
  (case (el, er) of
   | (IntV vl, IntV vr) => SOME (IntV (vl * vr))
   | _ => NONE)
  ∧
  do_bop _ _ _ = NONE
End

(* TODO move to semantic primitives? *)
Definition literal_to_value_def:
  literal_to_value (BoolLiteral b) = SOME (BoolV b) ∧
  literal_to_value (IntLiteral s (Primitive Int)) =
  (case fromString (implode s) of
   | NONE => NONE
   | SOME i => SOME (IntV i)) ∧
  literal_to_value _ = NONE
End

(* Do an if-then-else *)
(* TODO move to semantic primitives? *)
Definition do_if_def:
  do_if cnd thn els =
    if cnd = BoolV T then SOME thn
    else if cnd = BoolV F then SOME els
    else NONE
End

(* Returns a list of names if none of the Formals has any attributes. *)
Definition simple_formal_names_def:
  simple_formal_names [] = SOME []
  ∧
  simple_formal_names ((Formal n _ [])::rest) =
  (case (simple_formal_names rest) of
   | SOME rest => SOME (n::rest)
   | NONE => NONE)
  ∧
  simple_formal_names _ = NONE
End

Definition name_sig_call_def:
  name_sig_call (Companion [mod_name] []) (CallName met_name NONE NONE F (CallSignature params inheritedParams)) =
  SOME (dest_Ident mod_name, met_name, params, inheritedParams)
  ∧
  name_sig_call _ _ = NONE
End

Definition resolve_call_def:
  resolve_call (env: sem_env) (exp_call: bool) (call_on: expression) (call_name: callName) call_typeArgs =
  (case (name_sig_call call_on call_name) of
   | NONE => INL Runsupported
   | SOME (call_mod_name, call_met_name, call_params, call_inheritedParams) =>
       (case (ALOOKUP env.methods (call_mod_name, call_met_name)) of
        | NONE => INL Rtype_error
        | SOME (Method met_attrs met_isStatic met_hasBody _ _
                       met_overridingPath met_nam met_typeParams
                       met_params met_inheritedParams met_body met_outTypes
                       met_outVars) =>
            (* Ignore outVarsAreUninitFieldsToAssign, wasFunction *)
            if met_attrs ≠ [] ∨ ¬met_isStatic ∨ met_overridingPath ≠ NONE
               ∨ met_typeParams ≠ [] ∨ call_typeArgs ≠ [] then
              INL Runsupported
            else if ¬met_hasBody ∨ met_nam ≠ call_met_name
                    ∨ met_params ≠ call_params
                    ∨ met_inheritedParams ≠ call_inheritedParams
                    ∨ (exp_call ∧
                       (LENGTH met_outTypes ≠ 1 ∨ met_outVars ≠ NONE)) then
              INL Rtype_error
            else
              (* NOTE I believe that inheritedParams are mainly used in the Rust *)
              (*   compiler to determine whether something needs to be borrowed. *)
              (case (simple_formal_names met_params) of
               | NONE => INL Runsupported
               | SOME param_names => INR (param_names, met_body))))
End

(* Annotated with fix_clock *)
Definition evaluate_stmts_ann_def[nocompute]:
  evaluate_exp (st: state) (env: sem_env) (Literal l) : (state # value dafny_result) =
  (case literal_to_value l of
   | NONE => (st, Rerr Runsupported)  (* TODO Could also be Rtype_error *)
   | SOME v => (st, Rval v))
  ∧
  evaluate_exp st env (BinOp (TypedBinOp bop _ _ _) el er) =
  (case fix_clock st (evaluate_exp st env el) of
   | (st', Rval vl) =>
       if is_lop bop then
         (case do_lop bop vl er of
          | NONE => (st', Rerr Rtype_error)
          | SOME (Exp er) => evaluate_exp st' env er
          | SOME (Val vl) => (st', Rval vl))
       else
         (case evaluate_exp st' env er of
          | (st'', Rval vr) =>
              (case do_bop bop vl vr of
               (* TODO Could also be Runsupported *)
               | NONE => (st'', Rerr Rtype_error)
               | SOME r => (st'', Rval r))
          | r => r)
   | r => r)
  ∧
  evaluate_exp st env (Expression_Call call_on call_name call_typeArgs call_args) =
  (case (resolve_call env T call_on call_name call_typeArgs) of
   | INL err => (st, Rerr err)
   | INR (param_names, met_body) =>
       (case fix_clock st (evaluate_exps st env call_args) of
        | (st', Rval vals) =>
            (case (push_param_frame st' param_names vals) of
             | NONE => (st', Rerr Rtype_error)
             | SOME st'' =>
                 if st''.clock = 0
                 then (st'', Rerr Rtimeout_error)
                 else (evaluate_stmts (dec_clock st'') env met_body))
        (* We mention this case explicitly to avoid type errors *)
        | (st', Rerr err) => (st', Rerr err)))
  ∧
  evaluate_exp st env _ = (st, Rerr Runsupported)
  ∧
  evaluate_exps st env [] : (state # (value list) dafny_result) =
    (st, Rval [])
  ∧
  evaluate_exps st env (exp::exps) : (state # (value list) dafny_result) =
  (case fix_clock st (evaluate_exp st env exp) of
   | (st', Rval v) =>
       (case (evaluate_exps st' env exps) of
        | (sf, Rval vs) => (sf, Rval (v::vs))
        | r => r)
   (* We mention this case explicitly to avoid type errors *)
   | (st', Rerr err) => (st', Rerr err))
  ∧
  evaluate_stmt st env (DeclareVar varNam _ (SOME e) in_stmts) =
  (let varNam = dest_varName varNam in
     (case fix_clock st (evaluate_exp st env e) of
      | (st', Rval v) =>
          (case add_local st' varNam v of
           | NONE => (st', Rerr Rtype_error)
           | SOME st'' => evaluate_stmts st'' env in_stmts)
      | r => r))
  ∧
  evaluate_stmt st env (DeclareVar varNam t NONE in_stmts) =
  (let varNam = dest_varName varNam in
     (case init_val t of
      | NONE => (st, Rerr Runsupported)
      | SOME v =>
          (case add_local st varNam v of
              | NONE => (st, Rerr Rtype_error)
              | SOME st' => evaluate_stmts st' env in_stmts)))
  ∧
  evaluate_stmt st env (Assign (AssignLhs_Ident varNam) e) =
  (let varNam = dest_varName varNam in
     (case evaluate_exp st env e of
      | (st', Rval v) =>
          (case assign_to_local st' varNam v of
           | NONE => (st', Rerr Rtype_error)
           | SOME st'' => (st'', Rval UnitV))
      | r => r))
  ∧
  evaluate_stmt st env (If cnd thn els) =
  (case fix_clock st (evaluate_exp st env cnd) of
     (st', Rval v) =>
       (case do_if v thn els of
          NONE => (st', Rerr Rtype_error)
        | SOME stmts => evaluate_stmts (dec_clock st') env stmts)
   | r => r)
  ∧
  evaluate_stmt st env (While e stmts) =
  (case fix_clock st (evaluate_exp st env e) of
   | (st', Rval v) =>
       if v = BoolV F then (st', Rval UnitV)
       else if v = BoolV T then
         (case fix_clock st' (evaluate_stmts st' env stmts) of
          | (st'', Rerr e) => (st'', Rerr e)
          | (st'', _) =>
              if st''.clock = 0 then
                (st'', Rerr Rtimeout_error)
              else
                evaluate_stmt (dec_clock st'') env (While e stmts))
       else
         (st', Rerr Rtype_error)
   | r => r)
  ∧
  evaluate_stmt (st: state) (env: sem_env) _ =
  (st, Rerr Runsupported)
  ∧
  evaluate_stmts (st: state) (env: sem_env) [] =
  (st, Rval UnitV)
  ∧
  evaluate_stmts (st: state) (env: sem_env) (stmt::stmts) =
  (case fix_clock st (evaluate_stmt st env stmt) of
   | (st', Rval _) =>
       evaluate_stmts st' env stmts
   | r => r)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
              (λx. case x of
                   | INL (s, _, exp) =>
                       (s.clock, expression_size exp)
                   | INR (INL (s, _, exps)) =>
                       (s.clock, list_size expression_size exps)
                   | INR (INR (INL (s, _, stmt))) =>
                       (s.clock, statement_size stmt)
                   | INR (INR (INR (s, _, stmts))) =>
                       (s.clock, list_size statement_size stmts))’
  >> rpt strip_tac
  >> imp_res_tac fix_clock_IMP
  >> gvs [dec_clock_def, AllCaseEqs(), assignLhs_size_eq, do_if_def,
          add_local_def, do_lop_def, push_param_frame_def]
End

Theorem evaluate_stmts_clock:
  (∀s₁ env exp r s₂.
     evaluate_exp s₁ env exp = (s₂, r) ⇒ s₂.clock ≤ s₁.clock) ∧
  (∀s₁ env exps r s₂.
     evaluate_exps s₁ env exps = (s₂, r) ⇒ s₂.clock ≤ s₁.clock) ∧
  (∀s₁ env stmt r s₂.
     evaluate_stmt s₁ env stmt = (s₂, r) ⇒ s₂.clock ≤ s₁.clock) ∧
  (∀s₁ env stmts r s₂.
     evaluate_stmts s₁ env stmts = (s₂, r) ⇒ s₂.clock ≤ s₁.clock)
Proof
  ho_match_mp_tac evaluate_stmts_ann_ind
  >> rpt strip_tac
  >> pop_assum mp_tac >> simp [Once evaluate_stmts_ann_def] >> strip_tac
  >> gvs [AllCaseEqs (), dec_clock_def, fix_clock_def]
  >> EVERY (map imp_res_tac [add_local_clock, assign_to_local_clock,
                             push_param_frame_clock, fix_clock_IMP]) >> gvs[]
QED

Theorem fix_clock_evaluate_stmts:
  (fix_clock s₁ (evaluate_exp s₁ env exp) = evaluate_exp s₁ env exp) ∧
  (fix_clock s₁ (evaluate_exps s₁ env exps) = evaluate_exps s₁ env exps) ∧
  (fix_clock s₁ (evaluate_stmt s₁ env stmt) = evaluate_stmt s₁ env stmt) ∧
  (fix_clock s₁ (evaluate_stmts s₁ env stmts) = evaluate_stmts s₁ env stmts)
Proof
  Cases_on ‘evaluate_exp s₁ env exp’ >> Cases_on ‘evaluate_exps s₁ env exps’
  >> Cases_on ‘evaluate_stmt s₁ env stmt’ >> Cases_on ‘evaluate_stmts s₁ env stmts’
  >> imp_res_tac evaluate_stmts_clock
  >> gvs [fix_clock_def, state_component_equality]
QED

Theorem evaluate_stmts_def[compute] =
  REWRITE_RULE [fix_clock_evaluate_stmts] evaluate_stmts_ann_def;

Theorem evaluate_stmts_ind =
  REWRITE_RULE [fix_clock_evaluate_stmts] evaluate_stmts_ann_ind;

Definition evaluate_def:
  evaluate (p: program): (state # value dafny_result) resultM =
  do
    env <- init_env p;
    main <- main_call env;
    return (evaluate_stmt init_state env main)
  od
End

(* (* Testing *) *)
(* open dafny_sexpTheory *)
(* open sexp_to_dafnyTheory *)
(* open fromSexpTheory simpleSexpParseTheory *)
(* open TextIO *)

(* val exp = “(Literal (BoolLiteral T))” *)

(* val eval_exp_r = EVAL “(evaluate_exp init_state <||> ^exp)” *)
(*                    |> concl |> rhs |> rand; *)

(* val stmt = “[DeclareVar (VarName "foo") (Primitive Int) *)
(*                         (SOME (Literal (IntLiteral "999" (Primitive Int)))) *)
(*                         [If (Literal (BoolLiteral F)) *)
(*                             [(Assign (AssignLhs_Ident (VarName "foo")) *)
(*                                      (Literal (IntLiteral "4" (Primitive Int))))] *)
(*                             [(Assign (AssignLhs_Ident (VarName "foo")) *)
(*                                      (Literal (IntLiteral "2" (Primitive Int))))]; *)
(*                          If (Literal (BoolLiteral T)) *)
(*                             [(Assign (AssignLhs_Ident (VarName "foo")) *)
(*                                      (Literal (IntLiteral "4" (Primitive Int))))] *)
(*                             [(Assign (AssignLhs_Ident (VarName "foo")) *)
(*                                      (Literal (IntLiteral "2" (Primitive Int))))]]]” *)

(* val stmt_exp_r = EVAL “(evaluate_stmts init_state <||> ^stmt)” *)
(*                    |> concl |> rhs; *)

(* val inStream = TextIO.openIn "../tests/basic/binary_search.sexp"; *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)

(* val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand; *)
(* val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand; *)
(* val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand; *)
(* val eval_r = EVAL “(evaluate ^dafny_r)” |> concl |> rhs |> rand; *)

val _ = export_theory();
