(*
 Functional big-step semantics for evaluation of Dafny programs.
*)

open preamble
open dafny_astTheory
open result_monadTheory
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluate";

Type dafny_result = “:dafny_semanticPrimitives$result”
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
    params = [] ∧ inheritedParams = [] ∧ outTypes = [] ∧ outVars = SOME []
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
    | _ =>
        fail "main_call: Found no, or more than one Main"
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

(* TODO Commented out because we postpone print (since IO isn't trivial) *)
(* Definition value_to_string_def: *)
(*   value_to_string UnitV : string = "()" ∧ *)
(*   value_to_string (BoolV b) = (if b then "true" else "false") ∧ *)
(*   value_to_string (IntV i) = (explode (toString i)) ∧ *)
(*   value_to_string (CharV c) = [c] ∧ *)
(*   value_to_string (StrV s) = s *)
(* End *)

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

(* TODO Is this good style of pattern matching? Maybe (el, er) would be better? *)
Definition do_bop_def:
  do_bop Lt el er =
  (case el of
   | IntV vl => (case er of IntV vr => SOME (BoolV (vl < vr)) | _ => NONE)
   | _ => NONE)
  ∧
  do_bop (Plus F) el er =
  (case el of
   | IntV vl => (case er of IntV vr => SOME (IntV (vl + vr)) | _ => NONE)
   | _ => NONE)
  ∧
  do_bop (Minus F) el er =
  (case el of
   | IntV vl => (case er of IntV vr => SOME (IntV (vl - vr)) | _ => NONE)
   | _ => NONE)
  ∧
  do_bop (Times F) el er =
  (case el of
   | IntV vl => (case er of IntV vr => SOME (IntV (vl * vr)) | _ => NONE)
   | _ => NONE)
  ∧
  do_bop _ _ _ = NONE
End

(* TODO move to semantic primitives? *)
Definition literal_to_value_def:
  literal_to_value (BoolLiteral b) = SOME (BoolV b) ∧
  literal_to_value (IntLiteral s (Primitive String)) =
  (case fromString (implode s) of
   | NONE => NONE
   | SOME i => SOME (IntV i)) ∧
  (* TODO Commented because I don't want to deal with lists/chars right now *)
  (* literal_to_value (StringLiteral s verbatim) = *)
  (* SOME (StrV (unescape_string s verbatim)) ∧ *)
  (* literal_to_value (CharLiteral c) = SOME (CharV c) ∧ *)
  literal_to_value _ = NONE
End

Definition evaluate_exp_def:
  evaluate_exp (st: state) (env: sem_env)
               (Literal l): (state # dafny_result) =
  (case literal_to_value l of
   | NONE => (st, Rerr Runsupported)  (* TODO Could also be Rtype_error *)
   | SOME v => (st, Rval v))
  ∧
  evaluate_exp st env (BinOp (TypedBinOp bop _ _ _) el er) =
  (case evaluate_exp st env el of
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
  evaluate_exp st env _ = (st, Rerr Runsupported)
Termination
  WF_REL_TAC ‘measure $ expression_size o (λ(_,_,c). c)’ >> rw[]
  >> gvs[do_lop_def, AllCaseEqs()]
End

Theorem evaluate_exp_clock:
  ∀s1 env e r s2. evaluate_exp s1 env e = (s2, r) ⇒ s2.clock ≤ s1.clock
Proof
  ho_match_mp_tac evaluate_exp_ind >> rw[]
  >> gvs[evaluate_exp_def, AllCaseEqs()]
QED

(* Annotated with fix_clock *)
Definition evaluate_stmt_ann_def[nocompute]:
  (* TODO Commented, since we do not want to think about calls for now *)
  (* evaluate_stmt (st: state) (env: sem_env) *)
  (*               (Call on callName typeArgs args outs) : (state # dafny_result) = *)
  (* (let stmt = (Call on callName typeArgs args outs) in *)
  (*    (case dest_simple_call stmt of *)
  (*     | INL _ => (st, Rerr Runsupported) *)
  (*     | INR m_path => *)
  (*         (case ALOOKUP env.methods m_path of *)
  (*          | NONE => (st, Rerr Rtype_error) *)
  (*          | SOME m => *)
  (*              if ¬is_simple_method m then *)
  (*                (st, Rerr Rtimeout_error) *)
  (*              else if st.clock = 0 then *)
  (*                (st, Rerr Rtimeout_error) *)
  (*              else *)
  (*                let body = method_body m in *)
  (*                  evaluate_stmts (dec_clock st) env body))) *)
  (* ∧ *)
  (* evaluate_stmt (st: state) (env: sem_env) *)
  (*               EarlyReturn : (state # dafny_result) = *)
  (*   (st, Rret UnitV) *)
  (* ∧ *)
  (* TODO Commented, since we do not want to think about IO for now *)
  (* evaluate_stmt (st: state) (env: sem_env) *)
  (*               (Print e) : (state # dafny_result) = *)
  (*   (case evaluate_exp st env e of *)
  (*    | (st', Rval v) => *)
  (*        (st with cout := st.cout ++ (value_to_string v), Rret UnitV) *)
  (*    | r => r) *)
  (* ∧ *)
  evaluate_stmt st env (DeclareVar varNam _ (SOME e)) =
  (let varNam = dest_varName varNam in
     (case evaluate_exp st env e of
      | (st', Rval v) =>
          (case add_local st' varNam v of
           | NONE => (st', Rerr Rtype_error)
           | SOME st'' => (st'', Rval UnitV))
      | r => r))
  ∧
  evaluate_stmt st env (DeclareVar varNam t NONE) =
  (let varNam = dest_varName varNam in
     (case init_val t of
      | NONE => (st, Rerr Runsupported)
      | SOME v => (st, Rval v)))
  ∧
  evaluate_stmt st env (Assign (AssignLhs_Ident varNam) e) =
  (let varNam = dest_varName varNam in
     (case evaluate_exp st env e of
      | (st', Rval v) =>
          (case assign_to_local st varNam v of
           | NONE => (st, Rerr Rtype_error)
           | SOME st'' => (st'', Rval UnitV))
      | r => r))
  ∧
  evaluate_stmt st env (While e stmts) =
  (case evaluate_exp st env e of
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
  evaluate_stmt (st: state) (env: sem_env) _ : (state # dafny_result) =
    (st, Rerr Runsupported)
  ∧
  evaluate_stmts (st: state) (env: sem_env) [] : (state # dafny_result) =
    (st, Rval UnitV)
  ∧
  evaluate_stmts (st: state) (env: sem_env) [stmt] : (state # dafny_result) =
    evaluate_stmt st env stmt
  ∧
  evaluate_stmts (st: state) (env: sem_env)
                 (stmt1::stmt2::stmts') : (state # dafny_result) =
    (case fix_clock st (evaluate_stmt st env stmt1) of
     | (st', Rval _) =>
         evaluate_stmts st' env (stmt2::stmts')
     | r => r)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
              (λx. case x of
                   | INL (s, _, stmt) =>
                       (s.clock, statement_size stmt)
                   | INR (s, _, stmts) =>
                       (s.clock, list_size statement_size stmts))’ >> rw[]
  >> imp_res_tac evaluate_exp_clock
  >> imp_res_tac fix_clock_IMP
  >> gvs[dec_clock_def, AllCaseEqs()]
End

Theorem evaluate_stmt_clock:
  (∀s1 env stmt r s2.
    evaluate_stmt s1 env stmt = (s2, r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀s1 env stmts r s2.
    evaluate_stmts s1 env stmts = (s2, r) ⇒ s2.clock ≤ s1.clock)
Proof
  ho_match_mp_tac evaluate_stmt_ann_ind >> rw[]
  >> pop_assum mp_tac >> simp[Once evaluate_stmt_ann_def] >> strip_tac
  >> gvs[AllCaseEqs(), dec_clock_def, fix_clock_def]
  >> EVERY (map imp_res_tac [add_local_clock, assign_to_local_clock,
                             evaluate_exp_clock, fix_clock_IMP]) >> gvs[]
QED

Theorem fix_clock_evaluate_stmt:
  fix_clock s1 (evaluate_stmt s1 env stmt) = evaluate_stmt s1 env stmt
Proof
  Cases_on ‘evaluate_stmt s1 env stmt’
  \\ imp_res_tac evaluate_stmt_clock
  \\ fs[fix_clock_def, state_component_equality]
QED

Theorem evaluate_stmt_def[compute] =
  REWRITE_RULE [fix_clock_evaluate_stmt] evaluate_stmt_ann_def;

Theorem evaluate_stmt_ind =
  REWRITE_RULE [fix_clock_evaluate_stmt] evaluate_stmt_ann_ind;

Definition evaluate_def:
  evaluate (p: program): (state # dafny_result) resultM =
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

(* val inStream = TextIO.openIn "../tests/test.sexp"; *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)

(* val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand; *)
(* val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand; *)
(* val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand; *)
(* val eval_r = EVAL “(evaluate ^dafny_r)” |> concl |> rhs |> rand; *)

val _ = export_theory();
