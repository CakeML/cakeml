(*
    This script defines Eval and other core definitions used by the
    translator. The theorems about Eval serve as an interface between
    the source semantics and the translator's automation.
*)
open integerTheory ml_progTheory
     astTheory libTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory;
open mlvectorTheory mlstringTheory packLib;
open integer_wordSyntax
open terminationTheory
local open integer_wordSyntax in end;
open preamble;

val _ = new_theory "ml_translator";

infix \\ val op \\ = op THEN;

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(* Definitions *)

val empty_state_def = Define`
  empty_state = <|
    clock := 0;
    refs := empty_store;
    (* force the ffi state to unit
       the monadic translator must be used for FFI calls *)
    ffi := initial_ffi_state ARB ();
    next_type_stamp := 0;
    next_exn_stamp := 0|>`;

val Eval_def = Define `
  Eval env exp P =
    !refs. ?res refs'.
      eval_rel (empty_state with refs := refs) env exp
               (empty_state with refs := refs ++ refs') res /\
      P (res:v)`;

val AppReturns_def = Define ` (* think of this as a Hoare triple {P} cl {Q} *)
  AppReturns P cl Q =
    !v. P v ==>
      !refs. ?env exp refs' u.
        do_opapp [cl;v] = SOME (env,exp) /\
        eval_rel (empty_state with refs := refs) env exp
                 (empty_state with refs := refs++refs') u /\
        Q u`;

val Arrow_def = Define `
  Arrow a b =
    \f v. !x. AppReturns (a x) v (b (f x))`;

val _ = overload_on ("-->",``Arrow``)

val Eq_def = Define `
  Eq (abs:'a->v->bool) x =
    (\y v. (x = y) /\ abs y v)`;

val And_def = Define `And a P x v = (P x /\ a (x:'a) (v:v))`;

val UNIT_TYPE_def = Define `
  UNIT_TYPE (u:unit) (v:v) = (v = Conv NONE [])`;

val INT_def = Define `
  INT i = \v:v. (v = Litv (IntLit i))`;

val NUM_def = Define `
  NUM n = INT (& n)`;

val BOOL_def = Define `
  BOOL b = \v:v. (v = Boolv b)`;

val WORD_def = Define `
  WORD (w:'a word) =
    \v:v. dimindex (:'a) <= 64 /\
          (v = Litv (if dimindex (:'a) <= 8
                     then Word8 (w2w w << (8 - dimindex (:'a)))
                     else Word64 (w2w w << (64 - dimindex (:'a)))))`;

val CHAR_def = Define`
  CHAR (c:char) = \v:v. (v = Litv (Char c))`;

val STRING_TYPE_def = Define`
  STRING_TYPE (strlit s) = \v:v. (v = Litv (StrLit s))`;

val CONTAINER_def = Define `CONTAINER x = x`;

val TAG_def = Define `TAG n x = x`;

val PRECONDITION_def = Define `PRECONDITION b = (b:bool)`;

val PreImp_def = Define `
  PreImp b1 b2 = (PRECONDITION b1 ==> b2)`;

val PreImpEval_def = Define`
  PreImpEval b env code P = PreImp b (Eval env code P)`;

(* Theorems *)

local
  val Eval_lemma = prove(
    ``∀env exp P.
        Eval env exp P ⇔
         ∀refs.
             ∃ck1 res refs' ck2.
                 evaluate (empty_state with <|clock := ck1; refs := refs|>)
                   env [exp] =
                 (empty_state with <|clock := ck2; refs := refs ⧺ refs'|>,
                  Rval [res]) ∧ P res``,
     metis_tac [Eval_def |> SIMP_RULE (srw_ss()) [eval_rel_def,PULL_EXISTS]]);
in
  val Eval_rw = CONJ evaluate_def Eval_lemma
end;

Theorem evaluate_empty_state_IMP:
   eval_rel (empty_state with refs := s.refs) env exp (empty_state with refs := s.refs ++ refs') x ⇒
   eval_rel (s:'ffi state) env exp (s with refs := s.refs ++ refs') x
Proof
  rw [eval_rel_def]
  \\ drule (INST_TYPE[alpha|->oneSyntax.one_ty,beta|->``:'ffi``]
              (CONJUNCT1 evaluatePropsTheory.evaluate_ffi_intro))
  \\ disch_then (qspec_then `s with clock := ck1` mp_tac)
  \\ fs [empty_state_def]
  \\ strip_tac \\ asm_exists_tac \\ fs []
QED

Theorem Eval_Arrow:
    Eval env x1 ((a --> b) f) ==>
    Eval env x2 (a x) ==>
    Eval env (App Opapp [x1;x2]) (b (f x))
Proof
  rw[Eval_rw,Arrow_def,AppReturns_def]
  \\ pop_assum (qspec_then `refs` strip_assume_tac) \\ fs []
  \\ drule evaluate_add_to_clock
  \\ first_x_assum (qspec_then `refs ++ refs'` strip_assume_tac) \\ fs []
  \\ drule evaluate_add_to_clock
  \\ first_x_assum drule
  \\ disch_then (qspec_then `refs ++ refs' ++ refs''` strip_assume_tac)
  \\ fs [eval_rel_def]
  \\ disch_then (qspec_then `ck2+1+ck1''` strip_assume_tac)
  \\ disch_then (qspec_then `ck1'+1+ck1''` strip_assume_tac) \\ fs []
  \\ qexists_tac `ck1+ck1'+1+ck1''` \\ fs []
  \\ fs [evaluateTheory.dec_clock_def,eval_rel_def]
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule evaluate_add_to_clock \\ fs []
  \\ fs [empty_state_def,state_component_equality]
QED

Theorem Eval_Fun:
   (!v x. a x v ==> Eval (write name v env) body (b ((f:'a->'b) x))) ==>
    Eval env (Fun name body) ((a --> b) f)
Proof
  rw[Eval_rw,Arrow_def,AppReturns_def]
  \\ fs [empty_state_def,state_component_equality]
  \\ rw [] \\ first_x_assum drule
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ fs [do_opapp_def,eval_rel_def,PULL_EXISTS]
  \\ metis_tac [write_def]
QED

Theorem Eval_Fun_Eq:
   (!v. a x v ==> Eval (write name v env) body (b (f x))) ==>
    Eval env (Fun name body) ((Eq a x --> b) f)
Proof
  rw[Eval_rw,Arrow_def,AppReturns_def]
  \\ fs [empty_state_def,state_component_equality,Eq_def]
  \\ rw [] \\ first_x_assum drule
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ fs [do_opapp_def,eval_rel_def,PULL_EXISTS]
  \\ metis_tac [write_def]
QED

Theorem And_IMP_Eq:
   Eval env exp ((And a P --> b) f) ==>
    (P x ==> Eval env exp ((Eq a x --> b) f))
Proof
  fs [Eval_rw,Arrow_def,AppReturns_def,And_def,Eq_def] \\ metis_tac []
QED

Theorem Eq_IMP_And:
   (!x. P x ==> Eval env (Fun name exp) ((Eq a x --> b) f)) ==>
    Eval env (Fun name exp) ((And a P --> b) f)
Proof
  simp[Eval_rw,Arrow_def,AppReturns_def,And_def,Eq_def]
  \\ fs[state_component_equality]
QED

Theorem Eval_Fun_And:
   (!v x. P x ==> a x v ==> Eval (write name v env) body (b (f x))) ==>
    Eval env (Fun name body) ((And a P --> b) f)
Proof
  fs [GSYM And_def,AND_IMP_INTRO]
  \\ rw [] \\ match_mp_tac Eval_Fun \\ simp []
QED

Theorem Eval_Let:
   Eval env exp (a res) /\
    (!v. a res v ==> Eval (write name v env) body (b (f res))) ==>
    Eval env (Let (SOME name) exp body) (b (LET f res))
Proof
  rw[Eval_rw,write_def]
  \\ last_x_assum (qspec_then `refs` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ first_x_assum drule
  \\ disch_then (qspec_then `refs++refs'` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` strip_assume_tac)
  \\ disch_then (qspec_then `ck1'` strip_assume_tac)
  \\ fs [] \\ qexists_tac `ck1+ck1'`
  \\ fs [namespaceTheory.nsOptBind_def]
  \\ fs [empty_state_def,state_component_equality]
QED

Theorem Eval_Var_general:
   P v ==> !iden. nsLookup env.v iden = SOME v ==> Eval env (Var iden) P
Proof
  fs [Eval_rw,state_component_equality]
QED

Theorem Eval_Var_Short:
   P v ==> !name env.
               (nsLookup env.v (Short name) = SOME v) ==>
               Eval env (Var (Short name)) P
Proof
  fs [Eval_Var_general]
QED

Theorem Eval_Var_Long:
   P v ==> !m name env.
               (nsLookup env.v (Long m (Short name)) = SOME v) ==>
               Eval env (Var (Long m (Short name))) P
Proof
  fs [Eval_Var_general]
QED

Theorem Eval_Var_SWAP_ENV:
   !env1.
      Eval env1 (Var (Short name)) P /\
      (lookup_var name env = lookup_var name env1) ==>
      Eval env (Var (Short name)) P
Proof
  fs [FORALL_PROD,lookup_var_def,Eval_rw]
QED

val LOOKUP_VAR_def = Define `
  LOOKUP_VAR name env x = (lookup_var name env = SOME x)`;

Theorem LOOKUP_VAR_THM:
   LOOKUP_VAR name env x ==> Eval env (Var (Short name)) ($= x)
Proof
  fs [FORALL_PROD,lookup_var_def,Eval_rw,LOOKUP_VAR_def]
  \\ fs [state_component_equality]
QED

Theorem LOOKUP_VAR_SIMP:
   LOOKUP_VAR name (write x v  env) y =
    if x = name then (v = y) else LOOKUP_VAR name env y
Proof
  simp [LOOKUP_VAR_def,write_def,lookup_var_def] \\ rw []
QED

Theorem Eval_Val_INT:
   !n. Eval env (Lit (IntLit n)) (INT n)
Proof
  simp [Eval_rw,state_component_equality,INT_def]
QED

Theorem Eval_Val_NUM:
   !n. Eval env (Lit (IntLit (&n))) (NUM n)
Proof
  simp [Eval_rw,state_component_equality,INT_def,NUM_def]
QED

Theorem Eval_Val_UNIT:
   Eval env (Con NONE []) (UNIT_TYPE ())
Proof
  simp [Eval_rw,state_component_equality,UNIT_TYPE_def]
  \\ fs [EVAL ``do_con_check env.c NONE 0``,state_component_equality,
         EVAL ``build_conv env.c NONE []``]
QED

Theorem Eval_Val_BOOL_T:
   Eval env (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL T)
Proof
  fs [Eval_rw,do_app_def,empty_state_def,state_component_equality]
  \\ EVAL_TAC
QED

Theorem Eval_Val_BOOL_F:
   Eval env (App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL F)
Proof
  fs [Eval_rw,do_app_def,empty_state_def,state_component_equality]
  \\ EVAL_TAC
QED

Theorem Eval_Val_CHAR:
   !c. Eval env (Lit (Char c)) (CHAR c)
Proof
  fs [Eval_rw,empty_state_def,state_component_equality,CHAR_def]
QED

Theorem Eval_Val_STRING:
   !s. Eval env (Lit (StrLit s)) (STRING_TYPE (strlit s))
Proof
  fs [Eval_rw,empty_state_def,state_component_equality,STRING_TYPE_def]
QED

Theorem Eval_Val_WORD:
   !w:'a word.
    dimindex(:'a) ≤ 64 ⇒
    Eval env (Lit (if dimindex(:'a) ≤ 8
                   then Word8 (w2w w << (8-dimindex(:'a)))
                   else Word64 (w2w w << (64-dimindex(:'a)))))
             (WORD w)
Proof
  simp [WORD_def,Eval_rw,state_component_equality]
QED

(* Equality *)

val no_closures_def = tDefine "no_closures" `
  (no_closures (Litv l) = T) /\
  (no_closures (Conv name vs) = EVERY no_closures vs) /\
  (no_closures _ = F)`
 (WF_REL_TAC `measure v_size` \\ REPEAT STRIP_TAC
  \\ Induct_on `vs` \\ FULL_SIMP_TAC (srw_ss()) [MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [MEM,v_size_def]
  \\ DECIDE_TAC)

val types_match_def = tDefine "types_match" `
  (types_match (Litv l1) (Litv l2) = lit_same_type l1 l2) /\
  (types_match (Loc l1) (Loc l2) = T) /\
  (types_match (Conv cn1 vs1) (Conv cn2 vs2) =
    (ctor_same_type cn1 cn2 /\ ((cn1 = cn2) ⇒ types_match_list vs1 vs2))) /\
  (types_match _ _ = F) /\
  (types_match_list [] [] = T) /\
  (types_match_list (v1::vs1) (v2::vs2) =
    (types_match v1 v2 /\ types_match_list vs1 vs2)) /\
(* We could change this case to T, or change the semantics to have a type error
 * when equality reaches unequal-length lists *)
  (types_match_list _ _ = F)`
  (WF_REL_TAC `measure (\x. case x of INL (v1,v2) => v_size v1 |
                                      INR (vs1,vs2) => v7_size vs1)`);

val EqualityType_def = Define `
  EqualityType (abs:'a->v->bool) <=>
    (!x1 v1. abs x1 v1 ==> no_closures v1) /\
    (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> ((v1 = v2) = (x1 = x2))) /\
    (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2)`;

val Eq_lemma = Q.prove(
  `n < dimword (:'a) /\ dimindex (:α) <= k ==>
    (n * 2n ** (k − dimindex (:α))) < 2 ** k`,
  fs [dimword_def] \\ rw []
  \\ fs [LESS_EQ_EXISTS] \\ rw [] \\ fs [EXP_ADD]
  \\ simp_tac std_ss [Once MULT_COMM] \\ fs []);

Theorem EqualityType_NUM_BOOL:
    EqualityType NUM /\ EqualityType INT /\
    EqualityType BOOL /\ EqualityType WORD /\
    EqualityType CHAR /\ EqualityType STRING_TYPE /\
    EqualityType UNIT_TYPE
Proof
  EVAL_TAC \\ fs [no_closures_def,
    types_match_def, lit_same_type_def,
    stringTheory.ORD_11,mlstringTheory.explode_11]
  \\ SRW_TAC [] [] \\ EVAL_TAC
  \\ fs [w2w_def] \\ Cases_on `x1`
  \\ fs[STRING_TYPE_def] \\ EVAL_TAC
  \\ Cases_on `x2` \\ fs[STRING_TYPE_def] \\ EVAL_TAC
  \\ fs [WORD_MUL_LSL,word_mul_n2w]
  \\ imp_res_tac Eq_lemma \\ fs []
  \\ fs [MULT_EXP_MONO |> Q.SPECL [`p`,`1`] |> SIMP_RULE bool_ss [EVAL ``SUC 1``]]
QED

Theorem EqualityType_measure:
   !m. (!n : num. EqualityType (And TY (\x. m x < n))) ==> EqualityType TY
Proof
  rpt strip_tac
  \\ RULE_ASSUM_TAC (Q.GENL [`x`, `y`] o Q.SPEC `MAX (SUC (m x)) (SUC (m y))`)
  \\ fs [EqualityType_def, And_def]
  \\ metis_tac [prim_recTheory.LESS_SUC_REFL]
QED

val trivial4_def = Define `trivial4 x y a b = T`;

val Conv_args_def = Define `Conv_args v = (case v of
  | Conv _ vs => vs
  | _ => [v])`;

Theorem EqualityType_def_rearranged:
   EqualityType abs = (!x y vx vy. trivial4 x y vx vy
    ==> abs x vx /\ abs y vy
    ==> (x = y ==> vx = vy ==> no_closures vx)
        /\ (vx = vy <=> x = y) /\ types_match vx vy)
Proof
  fs [EqualityType_def, trivial4_def] \\ metis_tac []
QED

Theorem EqualityType_from_ONTO:
   (!a. ?r. (a = num2a r) ∧ r < (N : num))
    ==> (!TY stamps stn. (GENLIST (\n v. TY (num2a n) v) N
                = MAP (\st v. v = Conv (SOME (TypeStamp st stn)) []) stamps)
        ==> ALL_DISTINCT stamps
        ==> EqualityType TY)
Proof
  rpt strip_tac
  \\ fs [EqualityType_def_rearranged]
  \\ rpt GEN_TAC
  \\ FIRST_X_ASSUM (fn a => ((dest_exists o snd o dest_forall o concl) a;
        ASSUME_TAC (CONJ (Q.SPEC `x` a) (Q.SPEC `y` a))))
  \\ fs []
  \\ FIRST_X_ASSUM (fn a => MP_TAC (LIST_CONJ [Q.AP_TERM `LENGTH` a,
        Q.AP_TERM `EL r` a, Q.AP_TERM `EL r'` a]))
  \\ fs [EL_MAP, satTheory.AND_IMP, FUN_EQ_THM, no_closures_def,
        types_match_def, ctor_same_type_def, listTheory.EL_ALL_DISTINCT_EL_EQ,
        same_type_def]
  \\ metis_tac (map TypeBase.one_one_of [``:stamp``, ``:'a option``, ``: v``])
QED

Theorem EqualityType_from_ONTO_Exn:
   (!a. ?r. (a = num2a r) ∧ r < (N : num))
    ==> (!TY stamps. (GENLIST (\n v. TY (num2a n) v) N
                = MAP (\st v. v = Conv (SOME (ExnStamp st)) []) stamps)
        ==> ALL_DISTINCT stamps
        ==> EqualityType TY)
Proof
  rpt strip_tac
  \\ fs [EqualityType_def_rearranged]
  \\ rpt GEN_TAC
  \\ FIRST_X_ASSUM (fn a => ((dest_exists o snd o dest_forall o concl) a;
        ASSUME_TAC (CONJ (Q.SPEC `x` a) (Q.SPEC `y` a))))
  \\ fs []
  \\ FIRST_X_ASSUM (fn a => MP_TAC (LIST_CONJ [Q.AP_TERM `LENGTH` a,
        Q.AP_TERM `EL r` a, Q.AP_TERM `EL r'` a]))
  \\ fs [EL_MAP, satTheory.AND_IMP, FUN_EQ_THM, no_closures_def,
        types_match_def, ctor_same_type_def, listTheory.EL_ALL_DISTINCT_EL_EQ,
        same_type_def]
  \\ metis_tac (map TypeBase.one_one_of [``:stamp``, ``:'a option``, ``: v``])
QED

Theorem types_match_list_length:
   !vs1 vs2. types_match_list vs1 vs2 ==> LENGTH vs1 = LENGTH vs2
Proof
  Induct \\ Cases_on`vs2` \\ rw[types_match_def]
QED

Theorem type_match_implies_do_eq_succeeds:
   (!v1 v2. types_match v1 v2 ==> (do_eq v1 v2 = Eq_val (v1 = v2))) /\
    (!vs1 vs2.
       types_match_list vs1 vs2 ==> (do_eq_list vs1 vs2 = Eq_val (vs1 = vs2)))
Proof
  ho_match_mp_tac do_eq_ind
  \\ rw [do_eq_def, types_match_def]
  \\ imp_res_tac types_match_list_length
  \\ fs[] \\ Cases_on`cn1=cn2`\\fs[]
  \\ imp_res_tac types_match_list_length
QED

val do_eq_succeeds = Q.prove(`
  (!a x1 v1 x2 v2. EqualityType a /\ a x1 v1 /\ a x2 v2 ==>
                   (do_eq v1 v2 = Eq_val (x1 = x2)))`,
 rw [EqualityType_def]
 \\ res_tac
 \\ imp_res_tac type_match_implies_do_eq_succeeds
 \\ Cases_on `v1 = v2`
 \\ fs []);

val empty_state_with_refs_eq = Q.prove(
  `empty_state with refs := r =
   s2 with <| refs := r'; ffi := f |> ⇔
   ∃refs ffi.
   s2 = empty_state with <| refs := refs; ffi := ffi |> ∧
   r' = r ∧ f = empty_state.ffi`,
  rw[state_component_equality,EQ_IMP_THM]);

val empty_state_with_ffi_elim = Q.prove(
   `empty_state with <| refs := r; ffi := empty_state.ffi |> =
    empty_state with refs := r`,
  rw[state_component_equality]);

val Eval2_tac =
  first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ first_x_assum (qspec_then `refs++refs'` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` strip_assume_tac)
  \\ disch_then (qspec_then `ck1'` strip_assume_tac)
  \\ fs [] \\ qexists_tac `ck1+ck1'` \\ fs [];

Theorem Eval_Equality:
   Eval env x1 (a y1) /\ Eval env x2 (a y2) ==>
    EqualityType a ==>
    Eval env (App Equality [x1;x2]) (BOOL (y1 = y2))
Proof
  simp [Eval_rw,BOOL_def] \\ rw []
  \\ Eval2_tac
  \\ fs [do_app_def] \\ imp_res_tac do_eq_succeeds \\ fs []
  \\ rw[state_component_equality]
QED

(* booleans *)

Theorem Eval_Or:
   (a1 ==> Eval env x1 (BOOL b1)) /\
   (a2 ==> Eval env x2 (BOOL b2))
   ==>
   (a1 /\ (~CONTAINER b1 ==> a2) ==>
    Eval env (Log Or x1 x2) (BOOL (b1 \/ b2)))
Proof
  Cases_on `b1`
  \\ rw[Eval_rw,BOOL_def,CONTAINER_def] \\ fs []
  THEN1
   (pop_assum kall_tac
    \\ pop_assum (qspec_then `refs` strip_assume_tac)
    \\ qexists_tac `ck1`
    \\ fs [EVAL``do_log Or (Boolv T) x``]
    \\ fs [EVAL``Boolv T``,state_component_equality])
  \\ last_x_assum assume_tac
  \\ Eval2_tac
  \\ fs [EVAL``do_log Or (Boolv F) x``]
  \\ fs [EVAL``Boolv F``,state_component_equality]
QED

Theorem Eval_And:
   (a1 ==> Eval env x1 (BOOL b1)) /\
   (a2 ==> Eval env x2 (BOOL b2))
   ==>
   (a1 /\ (CONTAINER b1 ==> a2) ==>
    Eval env (Log And x1 x2) (BOOL (b1 /\ b2)))
Proof
  reverse (Cases_on `b1`)
  \\ rw[Eval_rw,BOOL_def,CONTAINER_def] \\ fs []
  THEN1
   (pop_assum kall_tac
    \\ pop_assum (qspec_then `refs` strip_assume_tac)
    \\ qexists_tac `ck1`
    \\ fs [EVAL``do_log And (Boolv F) x``]
    \\ fs [EVAL``Boolv F``,state_component_equality])
  \\ last_x_assum assume_tac
  \\ Eval2_tac
  \\ fs [EVAL``do_log And (Boolv T) x``]
  \\ fs [EVAL``Boolv F``,state_component_equality]
QED

Theorem Eval_If:
   (a1 ==> Eval env x1 (BOOL b1)) /\
   (a2 ==> Eval env x2 (a b2)) /\
   (a3 ==> Eval env x3 (a b3))
   ==>
   (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
    Eval env (If x1 x2 x3) (a (if b1 then b2 else b3)))
Proof
  rw[Eval_rw,BOOL_def,CONTAINER_def] \\ fs []
  \\ qpat_x_assum `_ ==> _` kall_tac
  \\ last_x_assum assume_tac
  \\ Eval2_tac
  \\ fs [EVAL``do_if (Boolv T) x y``,EVAL``do_if (Boolv F) x y``,
         state_component_equality]
QED

Theorem Eval_Bool_Not:
    Eval env x1 (BOOL b1) ==>
    Eval env (App Equality
      [x1; App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]]) (BOOL (~b1))
Proof
  rw[Eval_rw,BOOL_def,do_app_def,opb_lookup_def]
  \\ pop_assum (qspec_then `refs` strip_assume_tac)
  \\ qexists_tac `ck1` \\ fs [empty_state_def]
  \\ Cases_on `b1` \\ fs []
  \\ fs [EVAL``do_eq (Boolv T) (Boolv F)``,EVAL``do_eq (Boolv F) (Boolv F)``]
QED

Theorem Eval_Implies:
    Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (If x1 x2 (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]))
      (BOOL (b1 ==> b2))
Proof
  reverse (Cases_on `b1`)
  \\ rw[Eval_rw,BOOL_def,CONTAINER_def] \\ fs []
  THEN1
   (last_assum (qspec_then `refs` strip_assume_tac)
    \\ qexists_tac `ck1` \\ fs [EVAL ``do_if (Boolv F) x2 x1``]
    \\ fs [Eval_rw,do_app_def,state_component_equality] \\ EVAL_TAC)
  \\ last_x_assum assume_tac \\ Eval2_tac
  \\ fs [EVAL ``do_if (Boolv T) x2 x1``,state_component_equality]
QED

(* misc *)

Theorem Eval_Var_SIMP:
   Eval (write x v env) (Var (Short y)) p =
      if x = y then p v else Eval env (Var (Short y)) p
Proof
  simp [LOOKUP_VAR_def,write_def,lookup_var_def,Eval_rw]
  \\ rw [] \\ fs [state_component_equality]
QED

Theorem Eval_Eq:
   Eval env exp (a x) ==> Eval env exp ((Eq a x) x)
Proof
  simp [Eval_def,Eq_def]
QED

val FUN_FORALL = new_binder_definition("FUN_FORALL",
  ``($FUN_FORALL) = \(abs:'a->'b->v->bool) a v. !y. abs y a v``);

val FUN_EXISTS = new_binder_definition("FUN_EXISTS",
  ``($FUN_EXISTS) = \(abs:'a->'b->v->bool) a v. ?y. abs y a v``);

Theorem FUN_FORALL_INTRO:
   (!x. p x f v) ==> (FUN_FORALL x. p x) f v
Proof
  fs [FUN_FORALL]
QED

Theorem eval_rel_11:
   eval_rel s1 env e s2 x2 /\ eval_rel s1 env e s3 x3 ==>
    s2 = s3 /\ x2 = x3
Proof
  rw [eval_rel_def]
  \\ drule evaluate_add_to_clock
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck1'` strip_assume_tac)
  \\ strip_tac
  \\ disch_then (qspec_then `ck1` strip_assume_tac)
  \\ fs [state_component_equality]
QED

Theorem Eval_FUN_FORALL:
   (!x. Eval env exp ((p x) f)) ==>
    Eval env exp ((FUN_FORALL x. p x) f)
Proof
  rw[Eval_def,FUN_FORALL]
  \\ first_assum (qspecl_then [`ARB`,`refs`] strip_assume_tac)
  \\ asm_exists_tac \\ fs [] \\ rw []
  \\ first_assum (qspecl_then [`y`,`refs`] strip_assume_tac)
  \\ imp_res_tac eval_rel_11 \\ fs []
QED

Theorem Eval_FUN_FORALL_EQ:
   (!x. Eval env exp ((p x) f)) =
    Eval env exp ((FUN_FORALL x. p x) f)
Proof
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [Eval_FUN_FORALL]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_FORALL] \\ METIS_TAC []
QED

val FUN_FORALL_PUSH1 = Q.prove(
  `(FUN_FORALL x. a --> (b x)) = (a --> FUN_FORALL x. b x)`,
  rw [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL]
  \\ METIS_TAC[eval_rel_11,PAIR_EQ,result_11,SOME_11]) |> GEN_ALL;

val FUN_FORALL_PUSH2 = Q.prove(
  `(FUN_FORALL x. (a x) --> b) = ((FUN_EXISTS x. a x) --> b)`,
  FULL_SIMP_TAC std_ss [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,FUN_EXISTS,
    Eval_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = Q.prove(
  `(FUN_EXISTS x. Eq a x) = a`,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val FUN_QUANT_SIMP = save_thm("FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,FUN_FORALL_PUSH1,FUN_FORALL_PUSH2]);

Theorem Eval_Recclosure_ALT:
   !funs fname name body.
      (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ==>
      (!v. a n v ==>
           Eval (write name v (write_rec funs env2 env2)) body (b (f n))) ==>
      LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
      (find_recfun fname funs = SOME (name,body)) ==>
      Eval env (Var (Short fname)) ((Eq a n --> b) f)
Proof
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_rw,Arrow_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `nsLookup env.v (Short fname)` \\ fs [state_component_equality]
  \\ rveq
  \\ rw[AppReturns_def,Eq_def,do_opapp_def,PULL_EXISTS]
  \\ fs[build_rec_env_def,FOLDR,eval_rel_def]
  \\ METIS_TAC[APPEND_ASSOC]
QED

Theorem Eval_Recclosure:
   (!v. a n v ==>
         Eval (write name v (write_rec [(fname,name,body)] env2 env2))
              body (b (f n))) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    Eval env (Var (Short fname)) ((Eq a n --> b) f)
Proof
  (Eval_Recclosure_ALT |> Q.SPECL [`[(fname,name,body)]`,`fname`]
    |> SIMP_RULE (srw_ss()) [Once find_recfun_def] |> ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss []
QED

val SafeVar_def = Define `SafeVar = Var`;

Theorem Eval_Eq_Recclosure:
   LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
    (P f (Recclosure x1 x2 x3) =
     Eval env (Var (Short name)) (P f))
Proof
  simp [Eval_Var_SIMP,Eval_rw,LOOKUP_VAR_def,lookup_var_def]
  \\ simp [state_component_equality]
QED

Theorem Eval_Eq_Fun:
   Eval env (Fun v x) p ==>
    !env2. Eval env2 (Var name) ($= (Closure env v x)) ==>
           Eval env2 (Var name) p
Proof
  simp [Eval_Var_SIMP,Eval_rw] \\ rw []
  \\ Cases_on `nsLookup env2.v name` \\ fs []
  \\ fs [state_component_equality]
QED

Theorem Eval_WEAKEN:
   Eval env exp P ==> (!v. P v ==> Q v) ==> Eval env exp Q
Proof
  simp [Eval_def] \\ metis_tac []
QED

Theorem Eval_CONST:
   (!v. P v = (v = x)) ==>
    Eval env (Var name) ($= x) ==> Eval env (Var name) P
Proof
  simp [Eval_def]
QED

(* arithmetic for integers *)

val Eval_Opn = Q.prove(
  `!f n1 n2.
        Eval env x1 (INT n1) ==>
        Eval env x2 (INT n2) ==>
        PRECONDITION (((f = Divide) \/ (f = Modulo)) ==> ~(n2 = 0)) ==>
        Eval env (App (Opn f) [x1;x2]) (INT (opn_lookup f n1 n2))`,
  rw[Eval_rw,INT_def,PRECONDITION_def]
  \\ Eval2_tac \\ fs [do_app_def] \\ rw []
  \\ fs [state_component_equality]);

local
  fun f name q =
    save_thm("Eval_" ^ name,SIMP_RULE (srw_ss()) [opn_lookup_def,EVAL ``PRECONDITION T``]
                              (Q.SPEC q Eval_Opn))
in
  val Eval_INT_ADD  = f "INT_ADD" `Plus`
  val Eval_INT_SUB  = f "INT_SUB" `Minus`
  val Eval_INT_MULT = f "INT_MULT" `Times`
  val Eval_INT_DIV  = f "INT_DIV" `Divide`
  val Eval_INT_MOD  = f "INT_MOD" `Modulo`
end;

val Eval_Opb = Q.prove(
  `!f n1 n2.
        Eval env x1 (INT n1) ==>
        Eval env x2 (INT n2) ==>
        Eval env (App (Opb f) [x1;x2]) (BOOL (opb_lookup f n1 n2))`,
  rw[Eval_rw,INT_def,PRECONDITION_def,BOOL_def]
  \\ Eval2_tac \\ fs [do_app_def] \\ rw []
  \\ fs [state_component_equality]);

local
  fun f name q = let
    val th = SIMP_RULE (srw_ss()) [opb_lookup_def] (Q.SPEC q Eval_Opb)
    val _ = save_thm("Eval_" ^ name,SPEC_ALL th)
   in th end
in
  val Eval_INT_LESS = f "INT_LESS" `Lt`
  val Eval_INT_LESS_EQ = f "INT_LESS_EQ" `Leq`
  val Eval_INT_GREATER = f "INT_GREATER" `Gt`
  val Eval_INT_GREATER_EQ = f "INT_GREATER_EQ" `Geq`
end;

Theorem Eval_Num:
   Eval env x1 (INT i) ==> PRECONDITION (0 <= i) ==>
   Eval env x1 (NUM (Num i))
Proof
  SIMP_TAC std_ss [NUM_def,PRECONDITION_def] \\ rw []
  \\ `&Num i = i` by intLib.COOPER_TAC \\ fs []
QED

local

val th0 = Q.SPEC `0` Eval_Val_INT
val th_sub = MATCH_MP (MATCH_MP Eval_INT_SUB (Q.SPEC `0` Eval_Val_INT))
            (ASSUME ``Eval env (Var (Short "k")) (INT k)``)
val th1 = ASSUME ``Eval env (Var (Short "k")) (INT k)``
val th2 = Eval_INT_LESS  |> Q.SPECL [`k`,`0`]
          |> (fn th => MATCH_MP th th1) |> (fn th => MATCH_MP th th0)
val th = MATCH_MP Eval_If (LIST_CONJ (map (DISCH T) [th2,th_sub,th1]))
         |> REWRITE_RULE [CONTAINER_def]
val code =
  ``Let (SOME "k") x1
       (If (App (Opb Lt) [Var (Short "k"); Lit (IntLit 0)])
          (App (Opn Minus) [Lit (IntLit 0); Var (Short "k")])
          (Var (Short "k")))``

in

Theorem Eval_Num_ABS:
   Eval env x1 (INT i) ==>
   Eval env ^code (NUM (Num (ABS i)))
Proof
  SIMP_TAC std_ss [NUM_def]
  \\ `&(Num (ABS i)) = let k = i in if k < 0 then 0 - k else k` by
    (FULL_SIMP_TAC std_ss [LET_DEF] THEN intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL Eval_Let)
  \\ Q.EXISTS_TAC `INT` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL (DISCH_ALL th))
  \\ FULL_SIMP_TAC std_ss [Eval_Var_SIMP]
QED

end;

val num_of_int_def = Define `
  num_of_int i = Num (ABS i)`;

Theorem num_of_int_num[simp]:
   num_of_int (& n) = n /\ num_of_int (- & n) = n
Proof
  fs [num_of_int_def] \\ intLib.COOPER_TAC
QED

val Eval_num_of_int = save_thm("Eval_num_of_int",
  Eval_Num_ABS |> REWRITE_RULE [GSYM num_of_int_def]);

Theorem Eval_int_of_num:
   Eval env x1 (NUM n) ==>
   Eval env x1 (INT (int_of_num n))
Proof
  SIMP_TAC std_ss [NUM_def]
QED

Theorem Eval_int_of_num_o:
   Eval env x1 ((A --> NUM) f) ==>
   Eval env x1 ((A --> INT) (int_of_num o f))
Proof
  SIMP_TAC std_ss [NUM_def,Arrow_def]
QED

Theorem Eval_o_int_of_num:
   Eval env x1 ((INT --> A) f) ==>
   Eval env x1 ((NUM --> A) (f o int_of_num))
Proof
  SIMP_TAC std_ss [NUM_def,Arrow_def,Eval_def]
  \\ METIS_TAC[]
QED

Theorem Eval_int_negate:
   Eval env x1 (INT i) ==>
   Eval env (App (Opn Minus) [Lit (IntLit 0); x1]) (INT (-i))
Proof
  rw[Eval_rw]
  \\ first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ qexists_tac `ck1`
  \\ fs [do_app_def,INT_def,state_component_equality,opn_lookup_def]
QED

(* arithmetic for num *)

val sub_nocheck_def = Define`
  sub_nocheck (n:num) m = n - m`;

val Eval_NUM_SUB_nocheck = save_thm("Eval_NUM_SUB_nocheck",
  Eval_INT_SUB |> Q.SPECL [`&n`,`&m`]
  |> UNDISCH_ALL |> DISCH ``PRECONDITION ((m:num) <= n)``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_SUB,PRECONDITION_def]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM PRECONDITION_def]))
  |> DISCH ``Eval env x2 (INT (&m))``
  |> DISCH ``Eval env x1 (INT (&n))``
  |> SIMP_RULE std_ss [GSYM NUM_def,GSYM sub_nocheck_def]);

val Eval_NUM_ADD = save_thm("Eval_NUM_ADD",
  Eval_INT_ADD |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_ADD]);

val Eval_NUM_MULT = save_thm("Eval_NUM_MULT",
  Eval_INT_MULT |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_MUL]);

val Eval_NUM_DIV = save_thm("Eval_NUM_DIV",
  Eval_INT_DIV |> Q.SPECL [`&n1`,`&n2`]
  |> UNDISCH_ALL |> DISCH ``PRECONDITION (&n2 <> 0:int)``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_DIV,PRECONDITION_def,INT_INJ]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM PRECONDITION_def]))
  |> DISCH ``Eval env x2 (INT (&n2))``
  |> DISCH ``Eval env x1 (INT (&n1))``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_DIV]);

val Eval_NUM_MOD = save_thm("Eval_NUM_MOD",
  Eval_INT_MOD |> Q.SPECL [`&n1`,`&n2`]
  |> UNDISCH_ALL |> DISCH ``PRECONDITION (&n2 <> 0:int)``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_MOD,PRECONDITION_def,INT_INJ]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM PRECONDITION_def]))
  |> DISCH ``Eval env x2 (INT (&n2))``
  |> DISCH ``Eval env x1 (INT (&n1))``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_MOD]);

val Eval_NUM_MULT =
  Eval_INT_MULT |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_MUL]

local

val th0 = Q.SPEC `0` Eval_Val_INT
val th1 = ASSUME ``Eval env (Var (Short "k")) (INT k)``
val th2 = Eval_INT_LESS  |> Q.SPECL [`k`,`0`]
          |> (fn th => MATCH_MP th th1) |> (fn th => MATCH_MP th th0)
val th = MATCH_MP Eval_If (LIST_CONJ (map (DISCH T) [th2,th0,th1]))
         |> REWRITE_RULE [CONTAINER_def]
val code =
  ``Let (SOME "k") (App (Opn Minus) [x1; x2])
      (If (App (Opb Lt) [Var (Short "k"); Lit (IntLit 0)])
          (Lit (IntLit 0)) (Var (Short "k"))): exp``

in

Theorem Eval_NUM_SUB:
   Eval env x1 (NUM m) ==>
    Eval env x2 (NUM n) ==>
    Eval env ^code (NUM (m - n))
Proof
  SIMP_TAC std_ss [NUM_def]
  \\ `&(m - n:num) = let k = &m - &n in if k < 0 then 0 else k:int` by
   (FULL_SIMP_TAC std_ss [LET_DEF,INT_LT_SUB_RADD,INT_ADD,INT_LT]
    \\ Cases_on `m<n` \\ FULL_SIMP_TAC std_ss []
    THEN1 (`m - n = 0` by DECIDE_TAC \\ ASM_REWRITE_TAC [])
    \\ FULL_SIMP_TAC std_ss [NOT_LESS,INT_SUB])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC (GEN_ALL Eval_Let)
  \\ Q.EXISTS_TAC `INT` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_INT_SUB]
  \\ MATCH_MP_TAC (GEN_ALL (DISCH_ALL th))
  \\ FULL_SIMP_TAC std_ss [Eval_Var_SIMP]
QED

end;

val Eval_NUM_LESS = save_thm("Eval_NUM_LESS",
  Eval_INT_LESS |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]);

val Eval_NUM_LESS_EQ = save_thm("Eval_NUM_LESS_EQ",
  Eval_INT_LESS_EQ |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]);

val Eval_NUM_GREATER = save_thm("Eval_NUM_GREATER",
  Eval_INT_GREATER |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]
  |> REWRITE_RULE [GSYM GREATER_DEF, GSYM GREATER_EQ]);

val Eval_NUM_GREATER_EQ = save_thm("Eval_NUM_GREATER_EQ",
  Eval_INT_GREATER_EQ |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]
  |> REWRITE_RULE [GSYM GREATER_DEF, GSYM GREATER_EQ]);

Theorem Eval_NUM_EQ_0:
   !n. Eval env x (NUM n) ==>
        Eval env (App Equality [x; Lit (IntLit 0)]) (BOOL (n = 0))
Proof
  REPEAT STRIP_TAC \\ ASSUME_TAC (Q.SPEC `0` Eval_Val_NUM)
  \\ pop_assum mp_tac
  \\ drule (GEN_ALL Eval_Equality)
  \\ rw [] \\ res_tac
  \\ first_x_assum match_mp_tac
  \\ fs [EqualityType_NUM_BOOL]
QED

(* word operations *)

val tac =
  qmatch_goalsub_abbrev_tac`Opw wx`
  \\ rw[Eval_rw] \\ Eval2_tac \\ fs [do_app_def,WORD_def]
  \\ rw [] \\ fs [WORD_def,Abbr`wx`,state_component_equality]
  \\ fs [do_app_def,opw8_lookup_def,opw64_lookup_def]
  \\ fs [GSYM WORD_w2w_OVER_BITWISE]

Theorem Eval_word_and:
    Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Andw) [x1;x2])
      (WORD (word_and w1 w2))
Proof
  tac
QED

Theorem Eval_word_or:
    Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Orw) [x1;x2])
      (WORD (word_or w1 w2))
Proof
  tac
QED

Theorem Eval_word_xor:
    Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Xor) [x1;x2])
      (WORD (word_xor w1 w2))
Proof
  tac
QED

val DISTRIB_ANY = Q.prove(
  `(p * m + p * n = p * (m + n)) /\
    (p * m + n * p = p * (m + n)) /\
    (m * p + p * n = p * (m + n)) /\
    (m * p + n * p = p * (m + n:num)) /\
    (p * m - p * n = p * (m - n)) /\
    (p * m - n * p = p * (m - n)) /\
    (m * p - p * n = p * (m - n)) /\
    (m * p - n * p = p * (m - n:num))`,
  fs [LEFT_ADD_DISTRIB]);

val MOD_COMMON_FACTOR_ANY = Q.prove(
  `!n p q. 0 < n ∧ 0 < q ==>
            ((n * p) MOD (n * q) = n * p MOD q) /\
            ((p * n) MOD (n * q) = n * p MOD q) /\
            ((n * p) MOD (q * n) = n * p MOD q) /\
            ((p * n) MOD (q * n) = n * p MOD q)`,
  fs [GSYM MOD_COMMON_FACTOR]);

val Eval_word_add_lemma = Q.prove(
  `dimindex (:'a) <= k ==>
    (2 ** (k − dimindex (:α)) * q MOD dimword (:α)) MOD 2 ** k =
    (2 ** (k − dimindex (:α)) * q) MOD 2 ** k`,
  rw [] \\ fs [LESS_EQ_EXISTS]
  \\ rw [EXP_ADD,dimword_def,MOD_COMMON_FACTOR_ANY]);

Theorem Eval_word_add:
    Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Add) [x1;x2])
      (WORD (word_add w1 w2))
Proof
  tac
  \\ Cases_on `w1` \\ Cases_on `w2`
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ imp_res_tac Eval_word_add_lemma \\ fs []
QED

val Eval_word_sub_lemma = Q.prove(
  `dimindex (:'a) <= k /\ n' < dimword (:α) ==>
    (n * 2 ** (k − dimindex (:α)) +
      (2 ** k − (n' * 2 ** (k − dimindex (:α))) MOD 2 ** k) MOD 2 ** k) MOD 2 ** k =
    ((n + dimword (:α) − n') * 2 ** (k − dimindex (:α))) MOD 2 ** k`,
  fs [LESS_EQ_EXISTS,dimword_def] \\ rw []
  \\ fs [RIGHT_ADD_DISTRIB,RIGHT_SUB_DISTRIB,EXP_ADD]
  \\ full_simp_tac std_ss [DISTRIB_ANY,MOD_COMMON_FACTOR_ANY] \\ AP_TERM_TAC
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [Once (GSYM MOD_PLUS)]
  \\ `n + 2 ** dimindex (:α) − n' = n + (2 ** dimindex (:α) − n')` by decide_tac
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [Once (GSYM MOD_PLUS)]);

Theorem Eval_word_sub:
    Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Sub) [x1;x2])
      (WORD (word_sub w1 w2))
Proof
  tac
  \\ Cases_on `w1` \\ Cases_on `w2`
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ once_rewrite_tac [WORD_ADD_COMM]
  \\ fs [GSYM (SIMP_CONV (srw_ss()) [word_sub_def] ``w-v:'a word``)]
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ imp_res_tac Eval_word_add_lemma
  \\ fs [word_2comp_n2w,word_add_n2w]
  \\ imp_res_tac Eval_word_sub_lemma \\ fs []
QED

val w2n_w2w_8 = Q.prove(
  `dimindex (:α) < 8 ==>
    w2n ((w2w:'a word ->word8) w << (8 − dimindex (:α)) >>>
            (8 − dimindex (:α))) = w2n w`,
  Cases_on `w` \\ fs [w2n_lsr,w2w_def,WORD_MUL_LSL,word_mul_n2w,dimword_def]
  \\ rw []  \\ drule (DECIDE ``n<m ==> n <= m:num``)
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw []
  \\ fs [] \\ full_simp_tac bool_ss [GSYM (EVAL ``2n ** 8``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]);

val w2n_w2w_64 = Q.prove(
  `dimindex (:α) < 64 ==>
    w2n ((w2w:'a word ->word64) w << (64 − dimindex (:α)) >>>
            (64 − dimindex (:α))) = w2n w`,
  Cases_on `w` \\ fs [w2n_lsr,w2w_def,WORD_MUL_LSL,word_mul_n2w,dimword_def]
  \\ rw []  \\ drule (DECIDE ``n<m ==> n <= m:num``)
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw []
  \\ fs [] \\ full_simp_tac bool_ss [GSYM (EVAL ``2n ** 64``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]);

Theorem Eval_w2n:
    Eval env x1 (WORD (w:'a word)) ==>
    Eval env
      (if dimindex (:'a) = 8 then
         App (WordToInt W8) [x1]
       else if dimindex (:'a) = 64 then
         App (WordToInt W64) [x1]
       else if dimindex (:'a) < 8 then
         App (WordToInt W8) [App (Shift W8 Lsr (8 - dimindex (:'a))) [x1]]
       else
         App (WordToInt W64) [App (Shift W64 Lsr (64 - dimindex (:'a))) [x1]])
      (NUM (w2n w))
Proof
  rw[Eval_rw,WORD_def] \\ fs []
  \\ first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ qexists_tac `ck1`
  \\ fs [do_app_def,state_component_equality,NUM_def,INT_def]
  \\ TRY (fs [w2w_def] \\ assume_tac w2n_lt \\ rfs [dimword_def] \\ NO_TAC)
  \\ EVAL_TAC \\ fs [w2n_w2w_64,w2n_w2w_8]
QED

local
  val lemma = Q.prove(
    `(∀v. NUM (w2n w) v ⇒ Eval (write "x" v env)
                 (If (App (Opb Lt) [Var (Short "x"); Lit (IntLit (& k))])
                    (Var (Short "x"))
                    (App (Opn Minus) [Var (Short "x"); Lit (IntLit (& d))]))
        (INT ((\n. if n < k then &n else &n - &d) (w2n w))))`,
    fs [] \\ rpt strip_tac
    \\ match_mp_tac (MP_CANON Eval_If |> GEN_ALL)
    \\ qexists_tac `~(w2n w < k)`
    \\ qexists_tac `w2n w < k`
    \\ qexists_tac `T`
    \\ fs [CONTAINER_def]
    \\ rw []
    THEN1
     (match_mp_tac (MP_CANON Eval_NUM_LESS)
      \\ fs [Eval_Val_NUM] \\ fs [Eval_Var_SIMP])
    THEN1 (fs [Eval_Var_SIMP,NUM_def])
    \\ match_mp_tac (MP_CANON Eval_INT_SUB)
    \\ fs [Eval_Val_INT] \\ fs [Eval_Var_SIMP,NUM_def])
  val th1 = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Eval_Let) (UNDISCH Eval_w2n)
  val th2 = MATCH_MP th1 lemma |> Q.INST [`k`|->`INT_MIN (:α)`,`d`|->`dimword (:'a)`]
  val th3 = th2 |> SIMP_RULE std_ss [LET_THM,GSYM integer_wordTheory.w2i_eq_w2n]
  val th4 = th3 |> DISCH_ALL |> SIMP_RULE std_ss [INT_MIN_def,dimword_def]
  val _ = th4 |> concl |> rand |> rand |> rand
              |> integer_wordSyntax.is_w2i orelse failwith "Eval_w2i failed"
in
  val Eval_w2i = save_thm("Eval_w2i",th4)
end;

Theorem Eval_i2w:
    dimindex (:'a) <= 64 ==>
    Eval env x1 (INT n) ==>
    Eval env
      (if dimindex (:'a) = 8 then
         App (WordFromInt W8) [x1]
       else if dimindex (:'a) = 64 then
         App (WordFromInt W64) [x1]
       else if dimindex (:'a) < 8 then
         App (Shift W8 Lsl (8 - dimindex (:'a))) [App (WordFromInt W8) [x1]]
       else
         App (Shift W64 Lsl (64 - dimindex (:'a))) [App (WordFromInt W64) [x1]])
      (WORD ((i2w n):'a word))
Proof
  rw[Eval_rw,WORD_def] \\ fs [] \\ rfs []
  \\ first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ qexists_tac `ck1` \\ fs [do_app_def,INT_def]
  \\ fs [state_component_equality]
  \\ TRY
   (fs [do_app_def,NUM_def,INT_def,w2w_def,integer_wordTheory.i2w_def]
    \\ rw [] \\ fs [dimword_def]
    \\ fs [wordsTheory.word_2comp_n2w,dimword_def] \\ NO_TAC)
  \\ fs [shift8_lookup_def,shift64_lookup_def,
         w2w_def,integer_wordTheory.i2w_def,WORD_MUL_LSL,word_mul_n2w]
  \\ rw []
  \\ fs [shift8_lookup_def,shift64_lookup_def,wordsTheory.word_2comp_n2w,
         w2w_def,integer_wordTheory.i2w_def,WORD_MUL_LSL,word_mul_n2w,dimword_def]
  \\ rw [dimword_def] \\ TRY (drule (DECIDE ``n<m ==> n <= m:num``))
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw [] \\ fs []
  \\ full_simp_tac bool_ss
       [GSYM (EVAL ``2n ** 8``),GSYM (EVAL ``2n ** 64``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]
  \\ Cases_on `n` \\ fs []
  \\ match_mp_tac MOD_MINUS \\ fs []
QED

Theorem Eval_n2w:
    dimindex (:'a) <= 64 ==>
    Eval env x1 (NUM n) ==>
    Eval env
      (if dimindex (:'a) = 8 then
         App (WordFromInt W8) [x1]
       else if dimindex (:'a) = 64 then
         App (WordFromInt W64) [x1]
       else if dimindex (:'a) < 8 then
         App (Shift W8 Lsl (8 - dimindex (:'a))) [App (WordFromInt W8) [x1]]
       else
         App (Shift W64 Lsl (64 - dimindex (:'a))) [App (WordFromInt W64) [x1]])
      (WORD ((n2w n):'a word))
Proof
  qsuff_tac `n2w n = i2w (& n)` THEN1 fs [Eval_i2w,NUM_def]
  \\ fs [integer_wordTheory.i2w_def]
QED

Theorem Eval_w2w:
    dimindex (:'a) <= 64 /\ dimindex (:'b) <= 64 ==>
    Eval env x1 (WORD (w:'b word)) ==>
    Eval env
      (if (dimindex (:'a) <= 8 <=> dimindex (:'b) <= 8) then
         let w = if dimindex (:'a) <= 8 then W8 else W64 in
           if dimindex (:'b) <= dimindex (:'a) then
             App (Shift w Lsr (dimindex (:'a) - dimindex (:'b))) [x1]
           else
             App (Shift w Lsl (dimindex (:'b) - dimindex (:'a))) [x1]
       else if dimindex (:'b) <= 8 then
         App (Shift W64 Lsl (64 - dimindex (:'a)))
           [App (Shift W64 Lsr (8 - dimindex (:'b)))
              [App (WordFromInt W64) [App (WordToInt W8) [x1]]]]
       else
         App (Shift W8 Lsl (8 - dimindex (:'a)))
           [App (WordFromInt W8) [App (WordToInt W64)
              [App (Shift W64 Lsr (64 - dimindex (:'b))) [x1]]]])
      (WORD ((w2w w):'a word))
Proof
  IF_CASES_TAC THEN1
   (Cases_on `dimindex (:'a) ≤ 8` \\ fs []
    \\ IF_CASES_TAC
    \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ fs [Eval_rw,WORD_def] \\ rpt strip_tac
    \\ pop_assum (qspec_then `refs` mp_tac) \\ strip_tac
    \\ qexists_tac `ck1` \\ fs []
    \\ fs [empty_state_def]
    \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
    \\ fs [fcpTheory.CART_EQ,w2w,fcpTheory.FCP_BETA,word_lsl_def,word_lsr_def]
    \\ rw []
    \\ Cases_on `i + dimindex (:'a) < dimindex (:'b) + 8` \\ fs []
    \\ Cases_on `i + dimindex (:'a) < dimindex (:'b) + 64` \\ fs []
    \\ fs [fcpTheory.CART_EQ,w2w,fcpTheory.FCP_BETA,word_lsl_def,word_lsr_def])
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  THEN1
   (fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ fs [Eval_rw,WORD_def] \\ rpt strip_tac \\ rfs []
    \\ pop_assum (qspec_then `refs` mp_tac) \\ strip_tac
    \\ qexists_tac `ck1` \\ fs []
    \\ simp [do_app_def,empty_state_def]
    \\ fs [shift64_lookup_def,shift8_lookup_def]
    \\ fs [fcpTheory.CART_EQ,w2w,fcpTheory.FCP_BETA,word_lsl_def,word_lsr_def]
    \\ rpt strip_tac
    \\ eq_tac \\ strip_tac \\ fs []
    \\ rfs [fcpTheory.FCP_BETA,w2w]
    \\ fs [fcpTheory.FCP_BETA,w2w,EVAL ``dimindex (:8)``]
    \\ rfs [fcpTheory.FCP_BETA,w2w,EVAL ``dimindex (:8)``]
    \\ Cases_on `i + dimindex (:α) − 64 < 8`
    \\ fs [fcpTheory.FCP_BETA,w2w,EVAL ``dimindex (:8)``])
  THEN1
   (fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ fs [Eval_rw,WORD_def] \\ rpt strip_tac \\ rfs []
    \\ pop_assum (qspec_then `refs` mp_tac) \\ strip_tac
    \\ qexists_tac `ck1` \\ fs []
    \\ simp [do_app_def,empty_state_def]
    \\ fs [shift64_lookup_def,shift8_lookup_def]
    \\ fs [fcpTheory.CART_EQ,w2w,fcpTheory.FCP_BETA,word_lsl_def,word_lsr_def])
QED

Theorem Eval_word_lsl:
   !n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (App (Shift (if dimindex (:'a) <= 8 then W8 else W64) Lsl n) [x1])
        (WORD (word_lsl w1 n))
Proof
  rw[Eval_rw,WORD_def]
  \\ pop_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ fs [LESS_EQ_EXISTS]
  \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_lsl_def,fcpTheory.FCP_BETA,w2w] \\ rw []
  \\ Cases_on `w1 ' (i − (n + p))` \\ fs []
QED

Theorem Eval_word_lsr:
   !n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (let w = (if dimindex (:'a) <= 8 then W8 else W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex(:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    App (Shift w Lsr n) [x1]
                  else
                    App (Shift w Lsl k) [App (Shift w Lsr (n+k)) [x1]])
        (WORD (word_lsr w1 n))
Proof
  rw[Eval_rw,WORD_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ TRY
   (fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
    \\ fs [fcpTheory.CART_EQ,word_lsr_def,fcpTheory.FCP_BETA,w2w] \\ rw []
    \\ eq_tac \\ rfs [w2w] \\ rw [] \\ rfs [w2w] \\ NO_TAC)
  \\ fs [LESS_EQ_EXISTS,do_app_def]
  \\ fs [shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_lsr_def,word_lsl_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [fcpTheory.FCP_BETA,w2w]
  \\ imp_res_tac (DECIDE  ``p <= i ==> (i - p + n = (i + n) - p:num)``) \\ fs []
  \\ TRY (`i − p + (n + p) < 8` by decide_tac \\ fs [fcpTheory.FCP_BETA,w2w])
  \\ TRY (`i − p + (n + p) < 64` by decide_tac \\ fs [fcpTheory.FCP_BETA,w2w])
QED

Theorem Eval_word_asr:
   !n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (let w = (if dimindex (:'a) <= 8 then W8 else W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex(:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    App (Shift w Asr n) [x1]
                  else
                    App (Shift w Lsl k) [App (Shift w Asr (n+k)) [x1]])
        (WORD (word_asr w1 n))
Proof
  rw[Eval_rw,WORD_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ TRY (* takes care of = 8 and = 64 cases *)
   (fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
    \\ fs [fcpTheory.CART_EQ,word_asr_def,fcpTheory.FCP_BETA,w2w] \\ rw []
    \\ fs [word_msb_def] \\ rfs [w2w] \\ rw [] \\ rfs [w2w] \\ NO_TAC)
  \\ fs [LESS_EQ_EXISTS,do_app_def]
  \\ fs [shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_asr_def,word_lsl_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [fcpTheory.FCP_BETA,w2w,word_msb_def]
  \\ imp_res_tac (DECIDE ``8 = k ==> 7 = k - 1n``) \\ fs []
  \\ imp_res_tac (DECIDE ``64 = k ==> 63 = k - 1n``) \\ fs []
QED

Theorem Eval_word_ror:
   !n.
      Eval env x1 (WORD (w1:'a word)) ==>
      (dimindex (:'a) <> 8 ==> dimindex (:'a) = 64) ==>
      Eval env (App (Shift (if dimindex (:'a) <= 8 then W8 else W64) Ror n) [x1])
        (WORD (word_ror w1 n))
Proof
  Cases_on `dimindex (:'a) = 8` \\ fs []
  \\ Cases_on `dimindex (:'a) = 64` \\ fs []
  \\ rw[Eval_rw,WORD_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ fs [LESS_EQ_EXISTS]
  \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_ror_def,fcpTheory.FCP_BETA,w2w] \\ rw []
QED

(* arithmetic for doubles (word64) *)
Theorem Eval_FP_top:
  ! f w1 w2 w3.
        Eval env x2 (WORD (w2:64 word)) ==>
        Eval env x3 (WORD (w3:64 word)) ==>
        Eval env x1 (WORD (w1:64 word)) ==>
        Eval env (App (FP_top f) [x1;x2;x3]) (WORD (fp_top f w1 w2 w3))
Proof
  rw[Eval_rw,WORD_def]
  \\ first_x_assum mp_tac
  \\ first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ strip_tac
  \\ drule evaluate_add_to_clock
  \\ last_x_assum (qspec_then `refs++refs'` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ first_x_assum (qspec_then `refs++refs'++refs''` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ rpt (disch_then assume_tac)
  \\ pop_assum (qspec_then `ck1' + ck1''` strip_assume_tac)
  \\ fs[] \\ qexists_tac `ck1 + ck1' + ck1''` \\ fs[]
  \\ fs [do_app_def] \\ rw []
  \\ fs [state_component_equality]
QED

local
  fun f name q =
    save_thm("Eval_" ^ name,SIMP_RULE (srw_ss()) [fp_top_def, fpfma_def]
              (Q.SPEC q Eval_FP_top))
in
  val Eval_FLOAT_FMA = f "FLOAT_FMA" `FP_Fma`
end;

val Eval_FP_bop = Q.prove(
  `!f w1 w2.
        Eval env x1 (WORD (w1:64 word)) ==>
        Eval env x2 (WORD (w2:64 word)) ==>
        Eval env (App (FP_bop f) [x1;x2]) (WORD (fp_bop f w1 w2))`,
  rw[Eval_rw,WORD_def]
  \\ Eval2_tac \\ fs [do_app_def] \\ rw []
  \\ fs [state_component_equality]);

local
  fun f name q =
    save_thm("Eval_" ^ name,SIMP_RULE (srw_ss()) [fp_bop_def]
              (Q.SPEC q Eval_FP_bop))
in
  val Eval_FLOAT_ADD  = f "FLOAT_ADD" `FP_Add`
  val Eval_FLOAT_SUB  = f "FLOAT_SUB" `FP_Sub`
  val Eval_FLOAT_MULT = f "FLOAT_MULT" `FP_Mul`
  val Eval_FLOAT_DIV  = f "FLOAT_DIV" `FP_Div`
end;

val Eval_FP_cmp = Q.prove(
  `!f w1 w2.
        Eval env x1 (WORD (w1:64 word)) ==>
        Eval env x2 (WORD (w2:64 word)) ==>
        Eval env (App (FP_cmp f) [x1;x2]) (BOOL (fp_cmp f w1 w2))`,
  rw[Eval_rw,WORD_def,BOOL_def]
  \\ Eval2_tac \\ fs [do_app_def] \\ rw []
  \\ fs [state_component_equality]);

local
  fun f name q = let
    val th = SIMP_RULE (srw_ss()) [fp_cmp_def] (Q.SPEC q Eval_FP_cmp)
    val _ = save_thm("Eval_" ^ name,SPEC_ALL th)
   in th end
in
  val Eval_FLOAT_LESS = f "FLOAT_LESS" `FP_Less`
  val Eval_FLOAT_LESS_EQ = f "FLOAT_LESS_EQ" `FP_LessEqual`
  val Eval_FLOAT_GREATER = f "FLOAT_GREATER" `FP_Greater`
  val Eval_FLOAT_GREATER_EQ = f "FLOAT_GREATER_EQ" `FP_GreaterEqual`
  val Eval_FLOAT_EQ = f "FLOAT_EQ" `FP_Equal`
end;

val Eval_FP_uop = Q.prove(
  `!f w1 w2.
        Eval env x1 (WORD (w1:64 word)) ==>
        Eval env (App (FP_uop f) [x1]) (WORD (fp_uop f w1))`,
  rw[Eval_rw,WORD_def,BOOL_def]
  \\ first_x_assum (qspec_then `refs` strip_assume_tac)
  \\ qexists_tac `ck1` \\ fs[do_app_def, state_component_equality]);

local
  fun f name q = let
    val th = SIMP_RULE (srw_ss()) [fp_uop_def] (Q.SPEC q Eval_FP_uop)
    val _ = save_thm("Eval_" ^ name,SPEC_ALL th)
   in th end
in
  val Eval_FLOAT_ABS = f "FLOAT_ABS" `FP_Abs`
  val Eval_FLOAT_NEG = f "FLOAT_NEG" `FP_Neg`
  val Eval_FLOAT_SQRT = f "FLOAT_SQRT" `FP_Sqrt`
end;

(* list definition *)

val LIST_TYPE_def = Define `
  (!a x_2 x_1 v.
     LIST_TYPE a (x_2::x_1) v <=>
     ?v2_1 v2_2.
       v = Conv (SOME (TypeStamp "::" 1)) [v2_1; v2_2] /\
       a x_2 v2_1 /\ LIST_TYPE a x_1 v2_2) /\
  !a v.
     LIST_TYPE a [] v <=>
     v = Conv (SOME (TypeStamp "[]" 1)) []`

val LIST_TYPE_SIMP' = Q.prove(
  `!xs b. CONTAINER LIST_TYPE
              (\x v. if b x \/ MEM x xs then p x v else ARB) xs =
           LIST_TYPE (p:('a -> v -> bool)) xs`,
  Induct THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,LIST_TYPE_def,MEM,
    DISJ_ASSOC,CONTAINER_def]) |> GSYM
  |> curry save_thm "LIST_TYPE_SIMP'";

val LIST_TYPE_SIMP = LIST_TYPE_SIMP'
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss []
  |> curry save_thm "LIST_TYPE_SIMP";

Theorem LIST_TYPE_IF_ELIM:
 !v. LIST_TYPE (\x v. if MEM x l then P x v else Q x v) l v = LIST_TYPE P l v
Proof
  `!l' v. (!x. MEM x l ⇒ MEM x l') ⇒
  LIST_TYPE (\x v. if MEM x l' then P x v else Q x v) l v = LIST_TYPE P l v`
   suffices_by metis_tac[]
  >> Induct_on `l`
  >> fs[LIST_TYPE_def]
QED

Theorem LIST_TYPE_mono:
   ∀P Q l v.
   LIST_TYPE P l v ∧ (∀x v. MEM x l ∧ P x v ⇒ Q x v) ⇒
   LIST_TYPE Q l v
Proof
  ntac 2 gen_tac \\ Induct \\ rw[LIST_TYPE_def]
QED

(* pair definition *)

val PAIR_TYPE_def = Define `
  !b c x_2 x_1 v.
    PAIR_TYPE b c (x_2:'b,x_1:'c) v <=>
    ?v1_1 v1_2. v = Conv NONE [v1_1; v1_2] /\ b x_2 v1_1 /\ c x_1 v1_2`;

val PAIR_TYPE_SIMP = Q.prove(
  `!x. CONTAINER PAIR_TYPE (\y v. if y = FST x then a y v else ARB)
                           (\y v. if y = SND x then b y v else ARB) x =
        PAIR_TYPE (a:('a -> v -> bool)) (b:('b -> v -> bool)) x`,
  Cases \\ SIMP_TAC std_ss [PAIR_TYPE_def,CONTAINER_def,FUN_EQ_THM])
  |> GSYM |> SPEC_ALL |> curry save_thm "PAIR_TYPE_SIMP";

(* characters *)

Theorem Eval_Ord:
    Eval env x (CHAR c) ==>
    Eval env (App Ord [x]) (NUM (ORD c))
Proof
  rw[Eval_rw,CHAR_def,NUM_def,INT_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
QED

Theorem Eval_Chr:
    Eval env x (NUM n) ==>
    n < 256 ==>
    Eval env (App Chr [x]) (CHAR (CHR n))
Proof
  rw[Eval_rw,CHAR_def,NUM_def,INT_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ simp[integerTheory.INT_ABS_NUM]
  \\ srw_tac[DNF_ss][]
  \\ intLib.COOPER_TAC
QED

Theorem Boolv_11:
   (Boolv b1 = Boolv b2) <=> (b1 = b2)
Proof
  Cases_on `b1` \\ Cases_on `b2` \\ EVAL_TAC
QED

val tac =
  rw[Eval_rw,CHAR_def,NUM_def,INT_def]
  \\ Eval2_tac \\ fs [do_app_def,empty_state_def]
  \\ rw[BOOL_def,opb_lookup_def,Boolv_11]

Theorem Eval_char_lt:
   !c1 c2.
      Eval env x1 (CHAR c1) ==>
      Eval env x2 (CHAR c2) ==>
      Eval env (App (Chopb Lt) [x1;x2]) (BOOL (c1 < c2))
Proof
  tac \\ rw[stringTheory.char_lt_def]
  \\ metis_tac[APPEND_ASSOC]
QED

Theorem Eval_char_le:
   !c1 c2.
      Eval env x1 (CHAR c1) ==>
      Eval env x2 (CHAR c2) ==>
      Eval env (App (Chopb Leq) [x1;x2]) (BOOL (c1 ≤ c2))
Proof
  tac \\ rw[stringTheory.char_le_def]
  \\ metis_tac[APPEND_ASSOC]
QED

Theorem Eval_char_gt:
   !c1 c2.
      Eval env x1 (CHAR c1) ==>
      Eval env x2 (CHAR c2) ==>
      Eval env (App (Chopb Gt) [x1;x2]) (BOOL (c1 > c2))
Proof
  tac \\ rw[stringTheory.char_gt_def,int_gt,GREATER_DEF]
  \\ metis_tac[APPEND_ASSOC]
QED

Theorem Eval_char_ge:
   !c1 c2.
      Eval env x1 (CHAR c1) ==>
      Eval env x2 (CHAR c2) ==>
      Eval env (App (Chopb Geq) [x1;x2]) (BOOL (c1 ≥ c2))
Proof
  tac \\ rw[stringTheory.char_ge_def,int_ge,GREATER_EQ]
  \\ metis_tac[APPEND_ASSOC]
QED

(* strings *)

Theorem LIST_TYPE_CHAR_v_to_char_list:
   ∀l v. LIST_TYPE CHAR l v ⇒ v_to_char_list v = SOME l
Proof
  Induct
  \\ simp[LIST_TYPE_def,v_to_char_list_def,PULL_EXISTS,CHAR_def]
  \\ EVAL_TAC \\ simp []
QED

val tac1 =
  rw[Eval_rw,WORD_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ rw[BOOL_def,opb_lookup_def,Boolv_11]
  \\ fs[STRING_TYPE_def,mlstringTheory.implode_def]

val tac2 =
  rw[Eval_rw,CHAR_def,NUM_def,INT_def]
  \\ Eval2_tac \\ fs [do_app_def,empty_state_def]
  \\ rw[BOOL_def,opb_lookup_def,Boolv_11]
  \\ fs[STRING_TYPE_def,mlstringTheory.implode_def]

Theorem Eval_implode:
   !env x1 l.
      Eval env x1 (LIST_TYPE CHAR l) ==>
      Eval env (App Implode [x1]) (STRING_TYPE (implode l))
Proof
  tac1 \\ fs [option_case_eq,pair_case_eq]
  \\ metis_tac[LIST_TYPE_CHAR_v_to_char_list,
               stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem Eval_strlen:
   !env x1 s.
      Eval env x1 (STRING_TYPE s) ==>
      Eval env (App Strlen [x1]) (NUM (strlen s))
Proof
  Cases_on`s` \\ tac1
  \\ fs[NUM_def,INT_def,mlstringTheory.strlen_def]
  \\ metis_tac[]
QED

Theorem Eval_strsub:
   !env x1 x2 s n.
      Eval env x1 (STRING_TYPE s) ==>
      Eval env x2 (NUM n) ==>
      n < strlen s ==>
      Eval env (App Strsub [x1; x2]) (CHAR (strsub s n))
Proof
  tac2 \\ Cases_on `s` \\ fs [STRING_TYPE_def,NUM_def,INT_def]
  \\ fs[STRING_TYPE_def,CHAR_def,stringTheory.IMPLODE_EXPLODE_I,NUM_def,INT_def]
QED

Theorem Eval_concat:
   ∀env x ls.
     Eval env x (LIST_TYPE STRING_TYPE ls) ==>
     Eval env (App Strcat [x]) (STRING_TYPE (concat ls))
Proof
  tac1 \\ fs [option_case_eq,pair_case_eq,PULL_EXISTS]
  \\ qhdtm_x_assum`evaluate`kall_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac`res`
  \\ Induct_on`ls`
  \\ rw[LIST_TYPE_def,v_to_list_def,vs_to_string_def,STRING_TYPE_def]
  THEN1 EVAL_TAC
  \\ fs[v_to_list_def,LIST_TYPE_def]
  \\ first_x_assum drule \\ rw[]
  \\ rename1`concat (s::ls)`
  \\ Cases_on`s` \\ fs[STRING_TYPE_def]
  \\ rw[vs_to_string_def]
  \\ fs[concat_def,STRING_TYPE_def] \\ EVAL_TAC
QED

Theorem Eval_substring:
   ∀env x1 x2 x3 len off st.
    Eval env x1 (STRING_TYPE st) ==>
    Eval env x2 (NUM off) ==>
    Eval env x3 (NUM len) ==>
      off + len <= strlen st ==>
    Eval env (App CopyStrStr [x1; x2; x3]) (STRING_TYPE (substring st off len))
Proof
  fs [Eval_rw] \\ rw []
  \\ rw[Eval_rw,WORD_def]
  \\ first_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ first_x_assum (qspec_then `refs++refs'` mp_tac) \\ strip_tac
  \\ first_x_assum (qspec_then `refs++refs'++refs''` mp_tac) \\ strip_tac
  \\ drule evaluate_add_to_clock
  \\ qpat_x_assum `evaulate _ _ _ = _` kall_tac \\ fs []
  \\ drule evaluate_add_to_clock
  \\ qpat_x_assum `evaulate _ _ _ = _` kall_tac \\ fs []
  \\ drule evaluate_add_to_clock
  \\ qpat_x_assum `evaulate _ _ _ = _` kall_tac \\ fs []
  \\ disch_then (qspec_then `ck1' + ck1''` assume_tac)
  \\ disch_then (qspec_then `ck2 + ck1''` assume_tac)
  \\ disch_then (qspec_then `ck2 + ck2'` assume_tac)
  \\ qexists_tac `ck1+ck1'+ck1''` \\ fs [do_app_def]
  \\ Cases_on`st` \\ fs[STRING_TYPE_def,empty_state_def]
  \\ fs[NUM_def,INT_def,IMPLODE_EXPLODE_I]
  \\ rw[copy_array_def,INT_ABS_NUM,INT_ADD,
        substring_def,SEG_TAKE_DROP,STRING_TYPE_def]
QED

(* char list as string *)

val HOL_STRING_TYPE_def = Define `
  HOL_STRING_TYPE cs = STRING_TYPE (implode cs)`

Theorem Eval_HOL_STRING_INTRO:
  Eval env x (LIST_TYPE CHAR cs) ==>
  Eval env (App Implode [x]) (HOL_STRING_TYPE cs)
Proof
  rw [HOL_STRING_TYPE_def]
  \\ imp_res_tac Eval_implode
QED

Theorem Eval_HOL_STRING_LENGTH:
   !env x1 s.
      Eval env x1 (HOL_STRING_TYPE s) ==>
      Eval env (App Strlen [x1]) (NUM (LENGTH s))
Proof
  rw [HOL_STRING_TYPE_def]
  \\ imp_res_tac Eval_strlen
  \\ fs [strlen_def]
QED

Theorem Eval_HOL_STRING_TYPE_EL:
   !env x1 x2 s n.
      Eval env x2 (NUM n) ==>
      Eval env x1 (HOL_STRING_TYPE s) ==>
      n < LENGTH s ==>
      Eval env (App Strsub [x1; x2]) (CHAR (EL n s))
Proof
  rw [HOL_STRING_TYPE_def]
  \\ imp_res_tac Eval_strsub
  \\ rfs [strlen_def,strsub_def,implode_def]
QED

Theorem Eval_HOL_STRING_APPEND:
   !env x1 x2 s1 s2 n.
      Eval env x1 (HOL_STRING_TYPE s1) ==>
      Eval env x2 (HOL_STRING_TYPE s2) ==>
      nsLookup env.c (Short "::") = SOME (2,TypeStamp "::" 1) /\
      nsLookup env.c (Short "[]") = SOME (0,TypeStamp "[]" 1) ==>
      Eval env
        (App Strcat [Con (SOME (Short "::"))
                    [x1; Con (SOME (Short "::"))
                         [x2; Con (SOME (Short "[]")) []]]])
        (HOL_STRING_TYPE (s1++s2))
Proof
  rw [HOL_STRING_TYPE_def] \\ fs [implode_def]
  \\ `strlit (STRCAT s1 s2) =
      concat [strlit s1; strlit s2]` by EVAL_TAC
  \\ fs [] \\ match_mp_tac (Eval_concat)
  \\ fs [Eval_def,eval_rel_def]
  \\ fs [evaluate_def,do_con_check_def,build_conv_def] \\ gen_tac
  \\ first_x_assum (qspecl_then [`refs`] strip_assume_tac)
  \\ first_x_assum (qspecl_then [`refs++refs'`] strip_assume_tac)
  \\ qpat_x_assum `_ [x2] = _` assume_tac
  \\ drule evaluate_set_clock \\ simp []
  \\ disch_then (qspec_then `ck1'` strip_assume_tac)
  \\ fs [LIST_TYPE_def,STRING_TYPE_def]
  \\ qexists_tac `refs' ++ refs''`
  \\ qexists_tac `ck1''` \\ fs []
  \\ fs [state_component_equality]
QED

(* vectors *)

val VECTOR_TYPE_def = Define `
  VECTOR_TYPE a (Vector l) v <=>
    ?l'. v = Vectorv l' /\ LENGTH l = LENGTH l' /\ LIST_REL a l l'`;

Theorem Eval_sub:
  !env x1 x2 a n v.
     Eval env x1 (VECTOR_TYPE a v) ==>
     Eval env x2 (NUM n) ==>
     n < length v ==>
     Eval env (App Vsub [x1; x2]) (a (sub v n))
Proof
  tac2
  \\ `?l. v = Vector l` by metis_tac [vector_nchotomy]
  \\ rw []
  \\ fs [VECTOR_TYPE_def, length_def, NUM_def, sub_def, INT_def]
  \\ fs [LIST_REL_EL_EQN]
QED

Theorem Eval_vector:
  !env x1 a l.
     Eval env x1 (LIST_TYPE a l) ==>
     Eval env (App VfromList [x1]) (VECTOR_TYPE a (Vector l))
Proof
  tac1 \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ Q.SPEC_TAC (`res`, `res`)
  \\ Induct_on `l` \\ rw []
  \\ fs [LIST_TYPE_def, v_to_list_def, PULL_EXISTS]
  THEN1 (EVAL_TAC \\ fs [])
  \\ fs [bool_case_eq,option_case_eq,pair_case_eq,PULL_EXISTS]
  \\ fs [EVAL ``list_type_num``,VECTOR_TYPE_def]
QED

Theorem Eval_length:
   !env x1 x2 a n v.
      Eval env x1 (VECTOR_TYPE a v) ==>
      Eval env (App Vlength [x1]) (NUM (length v))
Proof
  tac1 \\ Cases_on `v`
  \\ fs [bool_case_eq,option_case_eq,pair_case_eq,PULL_EXISTS,
         VECTOR_TYPE_def,NUM_def,INT_def,length_def]
QED

Theorem list_to_v_LIST_TYPE:
   !xs v ys.
     LIST_TYPE a xs v /\
     v_to_list v = SOME ys ==>
       LIST_TYPE a xs (list_to_v ys)
Proof
  Induct
  \\ fs [LIST_TYPE_def, v_to_list_def, list_to_v_def]
  \\ rw [] \\ fs [v_to_list_def]
  \\ FULL_CASE_TAC \\ fs [] \\ rw []
  \\ fs [list_to_v_def]
  \\ res_tac \\ fs []
QED

(* ListAppend theorems *)

Theorem list_to_v_LIST_TYPE_APPEND:
   !xs ys x y.
     LIST_TYPE a x (list_to_v xs) /\
     LIST_TYPE a y (list_to_v ys) ==>
       LIST_TYPE a (x ++ y) (list_to_v (xs ++ ys))
Proof
  Induct \\ EVAL_TAC \\ rw []
  \\ Cases_on `x` \\ fs [list_to_v_def, LIST_TYPE_def]
QED

Theorem v_to_list_LIST_TYPE:
   !x v.
     LIST_TYPE a x v ==> ?xs. v_to_list v = SOME xs
Proof
  Induct \\ EVAL_TAC \\ rw [] \\ fs [v_to_list_def]
  \\ res_tac \\ fs [] \\ EVAL_TAC
QED

Theorem Eval_ListAppend:
   !env x1 x2 a l1 l2.
     Eval env x2 (LIST_TYPE a l1) ==>
     Eval env x1 (LIST_TYPE a l2) ==>
     Eval env (App ListAppend [x2;x1]) (LIST_TYPE a (l1 ++ l2))
Proof
  tac2 \\ fs [option_case_eq,PULL_EXISTS]
  \\ imp_res_tac v_to_list_LIST_TYPE \\ fs []
  \\ metis_tac [list_to_v_LIST_TYPE, list_to_v_LIST_TYPE_APPEND]
QED

Theorem Eval_length:
   !env x1 x2 a n v.
      Eval env x1 (VECTOR_TYPE a v) ==>
      Eval env (App Vlength [x1]) (NUM (length v))
Proof
  tac1 \\ fs []
  \\ `?l. v = Vector l` by metis_tac [vector_nchotomy]
  \\ rw [] \\ fs [VECTOR_TYPE_def, length_def, NUM_def, INT_def]
QED

(* This is useful to force the type inferencer to give the type unit
   to an unused argument. *)
val force_unit_type_def = Define `
  force_unit_type (u:unit) x = x`
  |> curry save_thm "force_unit_type_def[simp,compute]";

Theorem Eval_force_unit_type:
    Eval env x1 (UNIT_TYPE u) ==>
    Eval env x2 ((a:'a -> v -> bool) y) ==>
    Eval env (Mat x1 [(Pcon NONE [], x2)]) (a (force_unit_type u y))
Proof
 fs [Eval_rw] \\ rw []
  \\ fs[Eval_rw,UNIT_TYPE_def]
  \\ last_x_assum (qspec_then `refs` mp_tac) \\ strip_tac
  \\ first_x_assum (qspec_then `refs++refs'` mp_tac) \\ fs []
  \\ drule evaluate_set_clock
  \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
  \\ drule evaluate_add_to_clock
  \\ rpt (pop_assum kall_tac) \\ rw []
  \\ first_x_assum (qspec_then `ck1` assume_tac)
  \\ qexists_tac `ck1' + ck1` \\ fs [pat_bindings_def,pmatch_def]
  \\ fs [state_component_equality]
QED

val force_gc_to_run_def = Define `
  force_gc_to_run (i1:int) (i2:int) = ()`;

Theorem Eval_force_gc_to_run:
    Eval env x1 (INT i1) ==>
    Eval env x2 (INT i2) ==>
    Eval env (App ConfigGC [x1; x2]) (UNIT_TYPE (force_gc_to_run i1 i2))
Proof
  tac2 \\ fs [do_app_def,INT_def,UNIT_TYPE_def]
QED

val force_out_of_memory_error_def = Define `
  force_out_of_memory_error (x:'a) = x`;

val two_pow_64 = EVAL ``2i**64`` |> concl |> rand

Theorem Eval_force_out_of_memory_error:
    Eval env x (a i) ==>
    Eval env (Let (SOME "a") x
             (Let (SOME "n") (Lit (IntLit ^two_pow_64))
             (Let NONE (App Aalloc [Var (Short "n"); Var (Short "n")])
               (Var (Short "a"))))) (a (force_out_of_memory_error i))
Proof
  tac1 \\ fs [namespaceTheory.nsOptBind_def,store_alloc_def,
               force_out_of_memory_error_def]
QED

Theorem Eval_empty_ffi:
   Eval env x (STRING_TYPE s) ==>
   Eval env (App (FFI "") [x; App Aw8alloc [Lit (IntLit 0); Lit (Word8 0w)]])
     (UNIT_TYPE (empty_ffi s))
Proof
  rw[Eval_rw,WORD_def] \\ fs [store_alloc_def,do_app_def]
  \\ first_x_assum (qspec_then `refs ++ [W8array []]` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1` \\ fs [do_app_def,empty_state_def]
  \\ Cases_on `s` \\ fs [STRING_TYPE_def]
  \\ rveq \\ fs [store_lookup_def]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [EL_LENGTH_APPEND]
  \\ fs [ffiTheory.call_FFI_def]
  \\ fs [store_assign_def]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [EL_LENGTH_APPEND]
  \\ EVAL_TAC \\ fs []
QED

(* a few misc. lemmas that help the automation *)

Theorem IMP_PreImp:
   !b1 b2 b3. (b1 /\ b2 ==> b3) ==> b1 ==> PreImp b2 b3
Proof
  REPEAT Cases \\ EVAL_TAC
QED

(*
Theorem evaluate_list_SIMP:
   (evaluate_list F env s [] (s',Rval ([])) = (s = s')) /\
    (evaluate_list F env s (x::xs) (s',Rval ((y::ys))) <=>
     ?s''. evaluate F env s x (s'',Rval (y)) /\
     evaluate_list F env s'' xs (s',Rval (ys)))
Proof
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [EQ_IMP_THM]
QED
*)

val UNCURRY1 = Q.prove(
  `!f. UNCURRY f = \x. case x of (x,y) => f x y`,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]);

val UNCURRY2 = Q.prove(
  `!x y f. pair_CASE x f y  = pair_CASE x (\z1 z2. f z1 z2 y)`,
  Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val UNCURRY3 = Q.prove(
  `pair_CASE (x,y) f = f x y`,
  EVAL_TAC) |> GEN_ALL;

val UNCURRY_SIMP = save_thm("UNCURRY_SIMP",
  LIST_CONJ [UNCURRY1,UNCURRY2,UNCURRY3]);

Theorem num_case_thm:
   num_CASE = \n b f. if n = 0 then b else f (n-1)
Proof
  SIMP_TAC std_ss [FUN_EQ_THM,num_case_def] \\ Cases_on `n`
  \\ EVAL_TAC \\ SIMP_TAC std_ss []
QED

val PUSH_FORALL_INTO_IMP = save_thm("PUSH_FORALL_INTO_IMP",
  METIS_PROVE [] ``!P Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)``);

val FALSE_def = Define `FALSE = F`;
val TRUE_def = Define `TRUE = T`;

Theorem Eval_Val_BOOL_FALSE:
   Eval env (App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL FALSE)
Proof
  SIMP_TAC (srw_ss()) [Eval_Val_BOOL_F,FALSE_def]
QED

Theorem Eval_Val_BOOL_TRUE:
   Eval env (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL TRUE)
Proof
  SIMP_TAC (srw_ss()) [Eval_Val_BOOL_T,TRUE_def]
QED

val MEMBER_def = Define `
  (MEMBER (x:'a) [] <=> F) /\
  (MEMBER x (y::ys) <=> (x = y) \/ MEMBER x ys)`;

val MEM_EQ_MEMBER = Q.prove(
  `!ys x. MEM x ys = MEMBER x ys`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [MEMBER_def]);

Theorem MEMBER_INTRO:
   (MEM = MEMBER) /\ (MEM x = MEMBER x) /\ (MEM x ys = MEMBER x ys)
Proof
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,MEM_EQ_MEMBER]
QED

(* lookup cons *)

Theorem lookup_cons_write:
   !funs n x env name env1.
      (lookup_cons name (write n x env) = lookup_cons name env) /\
      (lookup_cons name (write_rec funs env1 env) = lookup_cons name env)
Proof
  Induct \\ REPEAT STRIP_TAC
  \\ fs [write_rec_thm,write_def,lookup_cons_def]
QED

Theorem DISJOINT_set_SIMP:
    (DISJOINT (set []) s <=> T) /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)
Proof
  REPEAT STRIP_TAC THEN1 (SRW_TAC [] []) \\ Cases_on `x IN s` \\ fs []
QED

(* removing shadowed elements from an alist *)

val ASHADOW_def = tDefine "ASHADOW" `
  (ASHADOW [] = []) /\
  (ASHADOW (x::xs) =
     if EXISTS (\y. FST x = FST y) xs
     then x :: ASHADOW (FILTER (\y. FST x <> FST y) xs)
     else x :: ASHADOW xs)`
 (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH xs` \\ fs [rich_listTheory.LENGTH_FILTER_LEQ])

val ASHADOW_PREFIX = Q.prove(
  `!xs ys.
      ALL_DISTINCT (MAP FST xs) /\
      EVERY (\y. ~(MEM y (MAP FST ys))) (MAP FST xs) ==>
      (ASHADOW (xs ++ ys) = xs ++ ASHADOW ys)`,
  Induct \\ fs [FORALL_PROD,ASHADOW_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ fs [EVERY_MEM,FORALL_PROD,EXISTS_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
  \\ Cases_on `y` \\ fs [] \\ RES_TAC);

val MEM_MAP_ASHADOW = Q.prove(
  `!xs y. MEM y (MAP FST (ASHADOW xs)) = MEM y (MAP FST xs)`,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs[] THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ fs [FORALL_PROD,ASHADOW_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ `LENGTH (FILTER (\y. FST h <> FST y) t) <= LENGTH t` by
     fs [rich_listTheory.LENGTH_FILTER_LEQ]
  \\ `LENGTH (FILTER (\y. FST h <> FST y) t) < SUC (LENGTH t)` by DECIDE_TAC
  \\ RES_TAC \\ fs[]
  \\ fs [MEM_MAP,MEM_FILTER] \\ METIS_TAC []);

val EVERY_ALOOKUP_LEMMA = Q.prove(
  `!xs. ALL_DISTINCT (MAP FST xs) ==>
         EVERY (\(x,y,z). ALOOKUP xs x = SOME (y,z)) xs`,
  Induct \\ srw_tac [] [] \\ PairCases_on `h` \\ fs []
  \\ fs [EVERY_MEM,FORALL_PROD] \\ rpt strip_tac
  \\ res_tac \\ Cases_on `h0 = p_1`
  \\ fs [MEM_MAP,FORALL_PROD] \\ metis_tac []);

val ALOOKUP_FILTER = Q.prove(
  `!t a q. q <> a ==> (ALOOKUP (FILTER (\y. q <> FST y) t) a = ALOOKUP t a)`,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ fs [alistTheory.ALOOKUP_def,FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ Cases_on `p_1 = a` \\ fs []
  \\ SRW_TAC [] []);

val ALOOKUP_ASHADOW = Q.prove(
  `!xs a. ALOOKUP (ASHADOW xs) a = ALOOKUP xs a`,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs [] THEN1 EVAL_TAC
  \\ Cases_on `h` \\ fs [FORALL_PROD,ASHADOW_def]
  \\ SRW_TAC [] []
  \\ sg `LENGTH (FILTER (\y. q <> FST y) t) < SUC (LENGTH t)`
  \\ RES_TAC \\ fs [ALOOKUP_FILTER]
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH t`
  \\ fs [rich_listTheory.LENGTH_FILTER_LEQ]);

val ALL_DISTINCT_MAP_FST_ASHADOW = Q.prove(
  `!xs. ALL_DISTINCT (MAP FST (ASHADOW xs))`,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs [] THEN1 EVAL_TAC
  \\ Cases_on `h` \\ fs [ASHADOW_def]
  \\ SRW_TAC [] [MEM_MAP_ASHADOW]
  \\ fs [EXISTS_MEM,MEM_MAP,MEM_FILTER,FORALL_PROD,EVERY_MEM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH t` \\ fs []
  \\ fs [rich_listTheory.LENGTH_FILTER_LEQ]);

(* size lemmas *)

val v7_size = Q.prove(
  `!vs v. (MEM v vs ==> v_size v < v7_size vs)`,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

(* TODO: what are the correct size lemmas? One of them should be replacin lists with namespaces

val v3_size = Q.prove(
  `!env x v. (MEM (x,v) env ==> v_size v < v5_size env)`,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

val v2_size = Q.prove(
  `!xs a. MEM a xs ==> v3_size a < v1_size xs`,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

Theorem v_size_lemmas:
   (MEM (x,y) envE ==> v_size y <= v3_size envE) /\
    (MEM (x,y) xs /\ MEM (t,xs) p1 ==> v_size y <= v2_size p1) /\
    (MEM v vs ==> v_size v < v7_size vs)
Proof
  FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC v4_size
  \\ IMP_RES_TAC v2_size
  \\ IMP_RES_TAC v6_size
  \\ FULL_SIMP_TAC std_ss [semanticPrimitivesTheory.v_size_def]
  \\ DECIDE_TAC
QED
*)

(* introducing a module (Tmod) *)

val type_names_def = Define `
  (type_names [] names = names) /\
  (type_names (Dtype _ tds :: xs) names =
     type_names xs (MAP (FST o SND) tds ++ names)) /\
  (type_names (x :: xs) names = type_names xs names)`;

val type_names_eq = Q.prove(
  `!ds names .
      type_names ds names =
      (FLAT (REVERSE (MAP (\d.
                case d of
                  Dlet _ v6 v7 => []
                | Dletrec _ v8 => []
                | Dmod _ ds => []
                | Dtype _ tds => MAP (\(tvs,tn,ctors). tn) tds
                | Dtabbrev _ tvs tn t => []
                | Dlocal _ _ => []
                | Dexn _ v10 v11 => []) ds))) ++ names`,
  Induct \\ fs [type_names_def] \\ Cases_on `h`
  \\ fs [type_names_def] \\ fs [FORALL_PROD,listTheory.MAP_EQ_f]);

val lookup_APPEND = Q.prove(
  `!xs ys n. ~(MEM n (MAP FST ys)) ==>
              (ALOOKUP (xs ++ ys) n = ALOOKUP xs n)`,
  Induct THEN1
   (FULL_SIMP_TAC std_ss [APPEND] \\ Induct
    \\ FULL_SIMP_TAC std_ss [MAP,MEM,FORALL_PROD] >>
    rw [])
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,APPEND]
  \\ rw []);

Theorem FEVERY_DRESTRICT_FUPDATE:
   FEVERY P (DRESTRICT (f |+ (x,y)) (COMPL s)) <=>
    (~(x IN s) ==> P (x,y)) /\
    FEVERY P (DRESTRICT f (COMPL (x INSERT s)))
Proof
  fs [] \\ SRW_TAC [] [finite_mapTheory.FEVERY_FUPDATE]
  THEN1 (`COMPL s INTER COMPL {x} = COMPL (x INSERT s)` by
      (fs [Once pred_setTheory.EXTENSION] \\ METIS_TAC []) \\ fs [])
  \\ `COMPL s = COMPL (x INSERT s)` by
     (fs [Once pred_setTheory.EXTENSION] \\ METIS_TAC []) \\ fs []
QED

Theorem PULL_EXISTS_EXTRA:
   (Q ==> ?x. P x) <=> ?x. Q ==> P x
Proof
  metis_tac []
QED

Theorem Eval_Fun_rw:
   Eval env (Fun n exp) P <=> P (Closure env n exp)
Proof
  rw[Eval_rw,EQ_IMP_THM,empty_state_def]
QED

val evaluate_Var_nsLookup = Q.prove(
   `eval_rel s env (Var id) s' r <=>
    ?v. nsLookup env.v id = SOME r ∧ s' = s`,
  fs [eval_rel_def,evaluate_def,lookup_var_def,option_case_eq,
      state_component_equality] \\ rw [] \\ eq_tac \\ rw []);

val evaluate_Var = Q.prove(
   `eval_rel s env (Var (Short n)) s' r <=>
    ?v. lookup_var n env = SOME r ∧ s' = s`,
  fs [evaluate_Var_nsLookup,lookup_var_def]);

Theorem Eval_Var_nsLookup:
   Eval env (Var id) P <=> case nsLookup env.v id of NONE => F | SOME v => P v
Proof
  fs [Eval_def,evaluate_Var_nsLookup, state_component_equality]
  \\ PURE_CASE_TAC \\ fs []
QED

Theorem Eval_Var:
   Eval env (Var (Short n)) P <=>
   ?v. lookup_var n env = SOME v /\ P v
Proof
  rw[Eval_Var_nsLookup,lookup_var_def] \\ PURE_CASE_TAC \\ fs[]
QED

Theorem Eval_Fun_Var_intro:
   Eval cl_env (Fun n exp) P ==>
   ∀name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
   Eval env (Var (Short name)) P
Proof
  rw[Eval_Fun_rw,Eval_Var,LOOKUP_VAR_def]
QED

Theorem Eval_Var_LOOKUP_VAR_elim:
   (!env. LOOKUP_VAR name env v ==> Eval env (Var (Short name)) P) ==> P v
Proof
  rw[Eval_Var,LOOKUP_VAR_def]
  \\ first_x_assum match_mp_tac
  \\ qexists_tac`<| v := nsSing name v |>`
  \\ EVAL_TAC
QED

val PRECONDITION_T = save_thm("PRECONDITION_T",EVAL ``PRECONDITION T``);

Theorem Eval_constant:
   !refs. Eval env exp P ==>
      ?v refs'. eval_rel (empty_state with refs := refs) env exp
                         (empty_state with refs := refs ++ refs') v
Proof
  rw[Eval_def]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs []
QED

Theorem Eval_evaluate_IMP:
    Eval env exp P /\
    eval_rel s env exp s' v ==>
    P v
Proof
  fs [Eval_def] \\ rw []
  \\ first_x_assum(qspec_then`s.refs`strip_assume_tac)
  \\ imp_res_tac evaluate_empty_state_IMP
  \\ imp_res_tac eval_rel_11 \\ fs []
QED

Theorem pair_CASE_UNCURRY:
   !x y. pair_CASE x y = UNCURRY y x
Proof
  Cases \\ EVAL_TAC \\ fs []
QED

Theorem IF_T:
  (if T then x else y) = x:'a
Proof
SIMP_TAC std_ss []
QED
Theorem IF_F:
  (if F then x else y) = y:'a
Proof
SIMP_TAC std_ss []
QED

Theorem sat_hyp_lemma:
   (b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y
Proof
  Cases_on `b1` \\ Cases_on `x1` \\ Cases_on `x2` \\ Cases_on `y` \\ EVAL_TAC
QED

Theorem IMP_EQ_F:
  ~b ==> (b = F)
Proof
REWRITE_TAC []
QED
Theorem IMP_EQ_T:
  b ==> (b = T)
Proof
REWRITE_TAC []
QED

Theorem IF_TAKEN:
   !b x y. b ==> ((if b then x else y) = x:'unlikely)
Proof
  SIMP_TAC std_ss []
QED

val EQ_COND_INTRO = save_thm("EQ_COND_INTRO",
  METIS_PROVE[]``(b ==> c) ==> (c = if b then T else c)``);

Theorem LIST_TYPE_And:
   LIST_TYPE (And a P) = And (LIST_TYPE a) (EVERY (P:'a->bool))
Proof
  SIMP_TAC std_ss [FUN_EQ_THM,And_def] \\ Induct
  \\ FULL_SIMP_TAC std_ss [MEM,LIST_TYPE_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [And_def]
QED

Theorem EVERY_MEM_CONTAINER:
   !P l. EVERY P l <=> !e. CONTAINER (MEM e l) ==> P (e:'a)
Proof
  SIMP_TAC std_ss [EVERY_MEM,CONTAINER_def]
QED

Theorem PRECONDITION_EQ_CONTAINER:
   (PRECONDITION p = CONTAINER p) /\
    (CONTAINER ~p = ~CONTAINER p) /\ CONTAINER T
Proof
  EVAL_TAC
QED

Theorem CONTAINER_NOT_ZERO:
   !P. (~(CONTAINER (b = 0)) ==> P b) =
        !n. (CONTAINER (b = SUC n)) ==> P (SUC n:num)
Proof
  REPEAT STRIP_TAC THEN Cases_on `b`
  THEN EVAL_TAC THEN SRW_TAC [] [ADD1]
QED

Theorem IMP_PreImp_LEMMA:
   !b1 b2 b3. (b1 ==> b3 ==> b2) ==> b3 ==> PreImp b1 b2
Proof
  REPEAT Cases THEN REWRITE_TAC [PreImp_def,PRECONDITION_def]
QED

Theorem PRE_IMP:
   T /\ PRECONDITION b ==> PRECONDITION b
Proof
  EVAL_TAC
QED

Theorem PreImp_IMP_T:
   PreImp b1 b2 /\ T ==> PreImp b1 b2
Proof
  EVAL_TAC
QED

Theorem CONJ_IMP = Q.prove(`
  !b1 b2 b12 b3 b4 b34.
      (b1 /\ b2 ==> b12) /\ (b3 /\ b4 ==> b34) ==>
      ((b1 /\ b3) /\ (b2 /\ b4) ==> b12 /\ b34)`,
  REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;

Theorem IMP_SPLIT = Q.prove(`
  !b12 b3 b4 b34.
      (b12 = b12) /\ (b3 /\ b4 ==> b34) ==>
      ((b12 ==> b3) /\ (b12 ==> b4) ==> (b12 ==> b34))`,
  REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;

Theorem FORALL_SPLIT:
   (!x. P1 x /\ P2 x ==> P (x:'a)) ==>
    ($! P1 ) /\ ($! P2 ) ==> $! P
Proof
  FULL_SIMP_TAC std_ss [FORALL_THM]
QED

Theorem DEFAULT_IMP:
   !b1. b1 /\ b1 ==> b1
Proof
  SIMP_TAC std_ss []
QED

Theorem combine_lemma:
   !b1 b2 b3 b4. (b1 /\ b2 ==> b3) /\ (b3 ==> b4) ==> b2 ==> b1 ==> b4
Proof
  REPEAT Cases THEN SIMP_TAC std_ss []
QED

Theorem IMP_PreImp_THM:
   (b ==> PreImp x y) ==> ((x ==> b) ==> PreImp x y)
Proof
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [PreImp_def,PRECONDITION_def]
QED

Theorem PreImp_IMP:
   (PRECONDITION x ==> PreImp x y) ==> PreImp x y
Proof
  SIMP_TAC std_ss [PreImp_def]
QED

Theorem PreImp_LEMMA:
   (b1 ==> PreImp b1 b2) ==> PreImp b1 b2
Proof
  fs [PreImp_def,PRECONDITION_def]
QED

val SUC_SUB1_LEMMA = save_thm("SUC_SUB1_LEMMA",
  Q.SPECL [`n`,`1`] ADD_SUB |> REWRITE_RULE [GSYM ADD1]);

Theorem LENGTH_EQ_SUC_IMP:
   LENGTH xs = SUC n ==> xs <> []
Proof
  Cases_on `xs` \\ fs []
QED

val prim_exn_list = let
  val tm = primSemEnvTheory.prim_sem_env_eq |> concl |> rand |> rand |> rand
  val (xs,ty) = ``^tm.c`` |> SIMP_CONV (srw_ss()) []
                |> concl |> rand |> rator |> rand |> listSyntax.dest_list
  val ys = filter (semanticPrimitivesSyntax.is_ExnStamp o rand o rand) xs
  in listSyntax.mk_list(ys, ty) end

(* pattern match translation *)

val Mat_cases_def = Define `
  Mat_cases (INL (vars,x:exp)) = [(Pcon NONE (MAP Pvar vars),x)] /\
  Mat_cases (INR ps) =
    MAP (\(name,vars,x:exp,t:stamp).
      (Pcon (SOME name) (MAP Pvar vars),x)) ps`;

val good_cons_env_def = Define `
  good_cons_env ps env <=>
    EVERY (\(name,vars,x,t).
      ALL_DISTINCT (pats_bindings (MAP Pvar vars) []) /\
      lookup_cons name env = SOME (LENGTH vars, t)) ps /\
    let (name,vars,x,t1) = HD ps in
      EVERY (\(name,vars,x,t2). same_type t1 t2) ps`

Theorem same_type_trans:
   same_type t1 t2 /\ same_type t1 t3 ==> same_type t2 t3
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ Cases_on `t3` \\ fs [same_type_def]
QED

Theorem evaluate_match_MAP = Q.prove(`
  !l1 xs.
      MEM (x1,x2,x3,t1) full_ps /\ full_ps <> [] /\
      good_cons_env full_ps env /\ set l1 SUBSET set full_ps /\
      ~MEM t1 (MAP (SND o SND o SND) l1) ==>
      evaluate_match (s:'ffi state) env
        (Conv (SOME t1) vals)
        (MAP (λ(name,vars,x,t). (Pcon (SOME name)
           (MAP Pvar vars),x)) l1 ++ xs) err =
      evaluate_match s env (Conv (SOME t1) vals) xs err`,
  Induct
  \\ fs [FORALL_PROD,evaluate_def,pmatch_def,pat_bindings_def]
  \\ rpt strip_tac
  \\ fs [good_cons_env_def,lookup_cons_def]
  \\ fs [EVERY_MEM]
  \\ res_tac \\ fs []
  \\ `?xx. HD full_ps = xx` by fs [] \\ PairCases_on `xx`
  \\ fs []
  \\ `MEM (HD full_ps) full_ps` by (Cases_on `full_ps` \\ fs [])
  \\ rfs [] \\ fs []
  \\ res_tac \\ fs []
  \\ imp_res_tac same_type_trans \\ fs []
  \\ fs [same_ctor_def]) |> GEN_ALL;

Theorem pmatch_list_MAP_Pvar:
   !vars vals aux.
      LENGTH vars = LENGTH vals ==>
      pmatch_list env refs (MAP Pvar vars) vals aux =
      Match (REVERSE (ZIP (vars, vals)) ++ aux)
Proof
  Induct \\ Cases_on `vals` \\ fs [] \\ fs [pmatch_def]
QED

val write_list_def = Define `
  write_list [] (env:v sem_env) = env /\
  write_list ((n,v)::xs) env = write_list xs (write n v env)`;

Theorem write_list_thm:
   !xs env.
      write_list xs (env:v sem_env) =
       (env with v := nsAppend (alist_to_ns (REVERSE xs)) env.v)
Proof
  Induct
  \\ fs [write_list_def,FORALL_PROD,namespaceTheory.alist_to_ns_def,
         write_def,namespaceTheory.nsBind_def]
  \\ rw [] \\ Cases_on `env.v`
  \\ fs [namespaceTheory.nsBind_def,namespaceTheory.nsAppend_def]
  \\ fs [sem_env_component_equality]
QED

Theorem IMP_Eval_Mat_cases:
   !a (r1:'a) env exp r2 y.
      Eval env exp (a r1) /\
      (case y of
       | INL (vars,exp) =>
                   (ALL_DISTINCT (pats_bindings (MAP Pvar vars) []) /\
                    (!v. a r1 v ==>
                         ?name vals t.
                           v = Conv NONE vals /\
                           LENGTH vals = LENGTH vars /\
                           Eval (write_list (ZIP (vars,vals)) env) exp r2))
       | INR ps => ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
                   good_cons_env ps env /\
                   (!v. a r1 v ==>
                        ?name vals t vars exp.
                          v = Conv (SOME t) vals /\
                          MEM (name,vars,exp,t) ps /\
                          LENGTH vals = LENGTH vars /\
                          Eval (write_list (ZIP (vars,vals)) env) exp r2)) ==>
      Eval env (Mat exp (Mat_cases y)) r2
Proof
  rpt gen_tac \\ Cases_on `y`
  THEN1
   (Cases_on `x`
    \\ fs [Eval_def,EXISTS_MEM,EXISTS_PROD,eval_rel_def]
    \\ rpt strip_tac
    \\ last_x_assum (qspec_then `refs` strip_assume_tac)
    \\ first_x_assum drule \\ strip_tac
    \\ last_x_assum (qspec_then `refs++refs'` strip_assume_tac)
    \\ rveq \\ fs []
    \\ fs [PULL_EXISTS,evaluate_def]
    \\ drule evaluate_add_to_clock
    \\ disch_then (qspec_then `ck2` assume_tac) \\ fs []
    \\ qpat_x_assum `_ env [exp] = _` assume_tac
    \\ drule evaluate_add_to_clock
    \\ disch_then (qspec_then `ck1'` assume_tac) \\ fs []
    \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS]
    \\ asm_exists_tac \\ fs [Mat_cases_def]
    \\ fs [evaluate_def,pmatch_def,pat_bindings_def]
    \\ fs [pmatch_list_MAP_Pvar,GSYM write_list_thm]
    \\ fs [state_component_equality])
  \\ fs [Eval_def,EXISTS_MEM,EXISTS_PROD,eval_rel_def]
  \\ rpt strip_tac
  \\ last_x_assum (qspec_then `refs` strip_assume_tac)
  \\ first_x_assum drule \\ strip_tac
  \\ last_x_assum (qspec_then `refs++refs'` strip_assume_tac)
  \\ rveq \\ fs []
  \\ fs [PULL_EXISTS,evaluate_def]
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` assume_tac) \\ fs []
  \\ qpat_x_assum `_ env [exp] = _` assume_tac
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck1'` assume_tac) \\ fs []
  \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS]
  \\ asm_exists_tac \\ fs [Mat_cases_def]
  \\ drule (evaluate_match_MAP |> INST_TYPE [``:'ffi``|->``:unit``])
  \\ qpat_x_assum `MEM _ y` (assume_tac o REWRITE_RULE [MEM_SPLIT])
  \\ fs [] \\ fs [ALL_DISTINCT_APPEND]
  \\ disch_then drule
  \\ `set l1 ⊆ set l1 ∪ {(name,vars,exp',t)} ∪ set l2` by fs [SUBSET_DEF,IN_UNION]
  \\ disch_then drule \\ fs []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ disch_then (fn th => rewrite_tac [th]) \\ fs []
  \\ fs [evaluate_def,pmatch_def,pat_bindings_def]
  \\ fs [good_cons_env_def,lookup_cons_def]
  \\ `same_type t t /\ same_ctor t t` by (Cases_on `t` \\ EVAL_TAC) \\ fs []
  \\ fs [pmatch_list_MAP_Pvar,GSYM write_list_thm]
  \\ fs [state_component_equality]
QED

val Eval_Con_lemma = prove(
  ``!ps refs.
      (∀p_1 p_2. MEM (p_1,p_2) ps ⇒ Eval env p_2 p_1) ==>
      ?ck1 ck2 refs' vals.
        evaluate (empty_state with <|clock := ck1; refs := refs|>) env
                 (MAP SND ps) =
        (empty_state with <|clock := ck2; refs := refs ⧺ refs'|>,Rval vals) /\
        LIST_REL (λ(p,x) v. p v) ps vals``,
  Induct THEN1 fs [state_component_equality]
  \\ fs [FORALL_PROD,Eval_def,eval_rel_def,PULL_EXISTS]
  \\ rw [] \\ once_rewrite_tac [evaluate_cons]
  \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS]
  \\ first_assum (qspecl_then [`p_1`,`p_2`] mp_tac)
  \\ rewrite_tac []
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ last_x_assum (qspec_then `refs++refs'` strip_assume_tac)
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` assume_tac) \\ fs []
  \\ qpat_x_assum `_ env [p_2] = _` assume_tac
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck1'` assume_tac) \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ fs [state_component_equality]);

Theorem Eval_Con:
   !ps stamp.
      lookup_cons name env = SOME (LENGTH ps,stamp) /\
      EVERY (\(p,x). Eval env x p) ps /\
      (!vals.
         LIST_REL (\(p,x) v. p v) ps vals ==>
         q (Conv (SOME stamp) vals)) ==>
      Eval env (Con (SOME name) (MAP SND ps)) q
Proof
  rpt strip_tac \\ fs [EVERY_MEM,FORALL_PROD] \\ rw [Eval_def]
  \\ simp [eval_rel_def,PULL_EXISTS,evaluate_def,do_con_check_def]
  \\ fs [lookup_cons_def,build_conv_def]
  \\ `∀p_1 p_2. MEM (p_1,p_2) (REVERSE ps) ⇒ Eval env p_2 p_1` by fs []
  \\ drule Eval_Con_lemma
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS,MAP_REVERSE]
  \\ asm_exists_tac \\ fs []
  \\ fs [GSYM EVERY2_REVERSE1]
QED

Theorem Eval_Con_NONE:
   !ps.
      EVERY (\(p,x). Eval env x p) ps /\
      (!vals.
         LIST_REL (\(p,x) v. p v) ps vals ==>
         q (Conv NONE vals)) ==>
      Eval env (Con NONE (MAP SND ps)) q
Proof
  rpt strip_tac \\ fs [EVERY_MEM,FORALL_PROD] \\ rw [Eval_def]
  \\ simp [eval_rel_def,PULL_EXISTS,evaluate_def,do_con_check_def]
  \\ fs [lookup_cons_def,build_conv_def]
  \\ `∀p_1 p_2. MEM (p_1,p_2) (REVERSE ps) ⇒ Eval env p_2 p_1` by fs []
  \\ drule Eval_Con_lemma
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS,MAP_REVERSE]
  \\ asm_exists_tac \\ fs []
  \\ fs [GSYM EVERY2_REVERSE1]
QED

(* terms used by the Lib file *)



val translator_terms = save_thm("translator_terms",
  pack_list (pack_pair pack_string pack_term)
    [("find_recfun",``find_recfun name funs : ('a # 'b) option``),
     ("eq type",``EqualityType (a:'a->v->bool)``),
     ("lookup_cons",``lookup_cons s e = SOME x``),
     ("nsLookup",``nsLookup e s = SOME (x:v)``), (*TODO: Should this be e or e.v?*)
     ("eq remove",``!b x. Eq b x = (b:'a->v->bool)``),
     ("map pat",``MAP (f:'a->'b)``),
     ("filter pat",``FILTER (f:'a->bool)``),
     ("every pat",``EVERY (f:'a->bool)``),
     ("exists pat",``EXISTS (f:'a->bool)``),
     ("n = 0",``(n = (0:num))``),
     ("0 = n",``(0 = (n:num))``),
     ("bind",``(Con(SOME(Short"Bind")) [])``),
     ("eq arrow",``Eq (a:'a->v->bool) x --> (b:'b->v->bool)``),
     ("arrow eq",``Arrow (Eq a (x:'a)) (b:'b->v->bool)``),
     ("precond = T",``!b. PRECONDITION b = T``),
     ("WF",``WF:('a -> 'a -> bool) -> bool``),
     ("COND",``COND:bool -> 'a -> 'a -> 'a``),
     ("not eq",``~(x = y:'a)``),
     ("lookup_cons eq",``lookup_cons n env = x``),
     ("Eval Var",``Eval env (Var n) (a (y:'a))``),
     ("PMATCH_ROW",``(PMATCH_ROW f1 f2):('a -> 'c) -> 'b -> 'c option``),
     ("PMATCH_ROW_T",``(PMATCH_ROW (f1:'a->'b) (K T) f3):'b -> 'c option``),
     ("PMATCH",``PMATCH x (l :('a -> 'b option) list)``),
     ("evaluate_pat",``evaluate _ _ _``),
     ("PreImp_Eval",``PreImp _ (Eval _ _ _)``),
     ("nsLookup_pat",``nsLookup env name``),
     ("pmatch_eq_Match_type_error",``pmatch _ _ _ _ _ = Match_type_error``),
     ("auto eq proof 1",``!x1 x2 x3 x4. bbb``),
     ("auto eq proof 2",``!x1 x2. bbb ==> bbbb``),
     ("remove lookup_cons",``!x1 x2 x3. (lookup_cons x1 x2 = SOME x3) = T``),
     ("no_closure_pat",``!x v. p x v ==> no_closures v``),
     ("types_match_pat",``!x1 v1 x2 v2. p x1 v1 /\ p x2 v2 ==> types_match v1 v2``),
     ("prim_exn_list",prim_exn_list),
     ("OPTION_TYPE_SIMP",``!OPTION_TYPE x. CONTAINER OPTION_TYPE
              (\y v. if x = SOME y then p y v else ARB) x =
           (OPTION_TYPE (p:('a -> v -> bool)) x):v->bool``)]);

val _ = export_theory();
