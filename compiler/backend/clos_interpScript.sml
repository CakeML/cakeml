(*
  Implementation of interpreter for closLang expressions written in closLang.
*)
open preamble closLangTheory backend_commonTheory;

val _ = new_theory "clos_interp";

val _ = set_grammar_ancestry ["closLang", "backend_common"];

(* fits in subset *)

Definition can_interpret_op_def:
  can_interpret_op (Cons tag) l = (l = 0n ∨ tag < 3n) ∧
  can_interpret_op (Const i) l = (l = 0) ∧
  can_interpret_op (Global n) l = (l = 0) ∧
  can_interpret_op (Constant c) l = (l = 0) ∧
  can_interpret_op _ l = F
End

Definition can_interpret_def:
  can_interpret ((Var t n):closLang$exp) = T ∧
  can_interpret (If t e1 e2 e3) =
    (can_interpret e1 ∧ can_interpret e2 ∧ can_interpret e3) ∧
  can_interpret (Let t es e) = (can_interpret e ∧ can_interpret_list es) ∧
  can_interpret (Op t p es) =
    (can_interpret_op p (LENGTH es) ∧ can_interpret_list es) ∧
  can_interpret (Raise t e) = can_interpret e ∧
  can_interpret (Tick t e) = can_interpret e ∧
  can_interpret (Fn _ _ _ _ e) = F ∧
  can_interpret (Handle t e1 e2) = (can_interpret e1 ∧ can_interpret e2) ∧
  can_interpret (Call _ _ _ es) = F ∧
  can_interpret (App _ opt e es) =
    (IS_NONE opt ∧ can_interpret e ∧ can_interpret_list es ∧ LENGTH es = 1) ∧
  can_interpret (Letrec _ _ _ fns e) = F ∧
  can_interpret_list [] = T ∧
  can_interpret_list (x::xs) = (can_interpret x ∧ can_interpret_list xs)
End

(* check size *)

Definition check_size_op_def:
  check_size_op k (Cons tag) l = (if l = 0:num then k else k-1:num) ∧
  check_size_op k (Const i) l = (k:num) ∧
  check_size_op k (Global n) l = k ∧
  check_size_op k _ l = k-1
End

Definition check_size_def:
  check_size k ((Var t n):closLang$exp) = (k:num) ∧
  check_size k (If t e1 e2 e3) =
    (let k = check_size k e1 in if k = 0 then 0 else
       let k = check_size k e2 in if k = 0 then 0 else
         check_size k e3) ∧
  check_size k (Let t es e) =
    (let k = check_size_list k es in if k = 0 then 0 else
       check_size k e) ∧
  check_size k (Op t p es) =
    (let k = check_size_op k p (LENGTH es) in if k = 0 then 0 else
       check_size_list k es) ∧
  check_size k (Raise t e) = check_size k e ∧
  check_size k (Tick t e) = check_size k e ∧
  check_size k (Fn _ _ _ _ e) = k ∧
  check_size k (Handle t e1 e2) =
    (let k = check_size k e1 in if k = 0 then 0 else
       check_size k e2) ∧
  check_size k (Call _ _ _ es) = k ∧
  check_size k (App _ _ e es) =
    (let k = check_size (k - 1) e in if k = 0 then 0 else
       check_size_list k es) ∧
  check_size k (Letrec _ _ _ fns e) = k ∧
  check_size_list k [] = k ∧
  check_size_list k (x::xs) =
    (let k = check_size k x in if k = 0 then 0 else
       check_size_list k xs)
End

Definition nontrivial_size_def:
  nontrivial_size e = (check_size 8 e = 0)
End

(* convert to const *)

Definition to_constant_op_def:
  to_constant_op (Const i) l cs = ConstCons 1 [ConstInt i] ∧
  to_constant_op (Constant c) l cs = ConstCons 1 [c] ∧
  to_constant_op (Global n) l cs = ConstCons 2 [ConstInt (& n)] ∧
  to_constant_op (Cons tag) l cs =
    (if l = 0n then ConstCons 1 [ConstCons tag []]
               else ConstCons (tag + 5) [cs]) ∧
  to_constant_op _ l cs = ConstInt 0
End

Definition to_constant_def:
  to_constant ((Var t n):closLang$exp) =
    ConstCons 0 [ConstInt (& n)] ∧
  to_constant (App _ _ e es) =
    ConstCons 0 [to_constant e; case es of [] => ConstInt 0 | (e1::_) => to_constant e1] ∧
  to_constant (If t e1 e2 e3) =
    ConstCons 0 [to_constant e1; to_constant e2; to_constant e3] ∧
  to_constant (Let t es e) = ConstCons 1 [to_constant_list es; to_constant e] ∧
  to_constant (Op t p es) = to_constant_op p (LENGTH es) (to_constant_list es) ∧
  to_constant (Raise t e) = ConstCons 3 [to_constant e] ∧
  to_constant (Tick t e) = ConstCons 4 [to_constant e] ∧
  to_constant (Handle t e1 e2) = ConstCons 2 [to_constant e1; to_constant e2] ∧
  to_constant (Fn _ _ _ _ e) = ConstInt 0 ∧
  to_constant (Call _ _ _ es) = ConstInt 0 ∧
  to_constant (Letrec _ _ _ fns e) = ConstInt 0 ∧
  to_constant_list [] = ConstCons 0 [] ∧
  to_constant_list (x::xs) = ConstCons 0 [to_constant x; to_constant_list xs]
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL e => closLang$exp_size e
                                    | INR es => list_size closLang$exp_size es’
End

(* interpreter as closLang program *)

Overload V[local] = “Var None”;

Overload IsCase[local] = “λtag len. If None (Op None (TagLenEq tag len) [V 0])”;

Overload GetEl[local] = “λn x. Op None (ElemAt n) [x]”;

Overload CallInterp[local] =
  “λenv x. App None NONE (App None NONE (App None NONE (Op None (Global 0) [])
            [env]) [Op None (Cons 0) []]) [x]”

Overload CallInterpList[local] =
  “λenv x. App None NONE (App None NONE (App None NONE (Op None (Global 0) [])
            [env]) [Op None (Cons 1) []]) [x]”

Definition clos_interp_el_def:
  clos_interp_el =
    If None (Op None (EqualConst (Int 0)) [V 1])
      (GetEl 0 $ V 0) $
    App None NONE (App None NONE (V 2)
      [Op None Sub [Op None (Const 1) []; V 1]]) [GetEl 1 $ V 0]
End

Definition clos_interp_rev_def:
  clos_interp_rev =
    If None (Op None (LenEq 0) [V 1])
      (V 0) $
    App None NONE (App None NONE (V 2)
      [GetEl 1 $ V 1]) [Op None (Cons 0) [V 0; GetEl 0 $ V 1]]
End

Definition clos_interpreter_body_def:
  clos_interpreter_body =
      If None (V 1) (* is _list version *)
        (If None (Op None (LenEq 0) [V 0]) (V 0) $
           Let None [CallInterp (V 2) (GetEl 0 $ V 0);
                     CallInterpList (V 2) (GetEl 1 $ V 0)] $
             (Op None (Cons 0) [V 1; V 0])) $
      (* normal cases *)
      IsCase 0 2 (* App *)
        (App None NONE (CallInterp (V 2) (GetEl 0 $ V 0))
                       [CallInterp (V 2) (GetEl 1 $ V 0)]) $
      IsCase 1 1 (* Constant *)
        (GetEl 0 $ V 0) $
      IsCase 2 1 (* Global *)
        (Op None (Global 0) [GetEl 0 $ V 0]) $
      IsCase 0 1 (* Var *)
        (Letrec [] NONE NONE
           [(1,Fn (mlstring$strlit "") NONE NONE 1 clos_interp_el)] $
           App None NONE (App None NONE (V 0) [GetEl 0 $ V 1]) [V 3]) $
      IsCase 1 2 (* Let *)
        (Let None [CallInterpList (V 2) (GetEl 0 $ V 0)] $
           CallInterp (Op None ListAppend [V 3; V 0]) (GetEl 1 $ V 1)) $
      IsCase 2 2 (* Handle *)
        (Handle None (CallInterp (V 2) (GetEl 0 $ V 0)) $
           CallInterp (Op None (Cons 0) [V 3; V 0]) (GetEl 1 $ V 1)) $
      IsCase 0 3 (* If *)
        (If None (CallInterp (V 2) (GetEl 0 $ V 0))
                 (CallInterp (V 2) (GetEl 1 $ V 0))
                 (CallInterp (V 2) (GetEl 2 $ V 0))) $
      IsCase 3 1 (* Raise *)
        (Raise None (CallInterp (V 2) (GetEl 0 $ V 0))) $
      IsCase 4 1 (* Tick *)
        (CallInterp (V 2) (GetEl 0 $ V 0)) $
      (* Cons for non-empty payload *)
      Let None [CallInterpList (V 2) (GetEl 0 $ V 0)] $
      Letrec [] NONE NONE
        [(1,Fn (mlstring$strlit "") NONE NONE 1 clos_interp_rev)] $
      Let None [App None NONE (App None NONE (V 0) [V 1]) [Op None (Cons 0) []]] $
      Let None [V 3] $
      IsCase 5 1 (* Cons 0 *) (Op None (FromList 0) [V 1]) $
      IsCase 6 1 (* Cons 1 *) (Op None (FromList 1) [V 1]) $
      IsCase 7 1 (* Cons 2 *) (Op None (FromList 2) [V 1]) $
      Op None (Cons 0) []
End

Definition clos_interpreter_def:
  clos_interpreter =
    Fn (mlstring$strlit "env") NONE NONE 1 $
    Fn (mlstring$strlit "exp") NONE NONE 1 $
      clos_interpreter_body
End

(* functions that insert calls to interpreter *)

Definition opt_interp_def:
  opt_interp e =
    if can_interpret e ∧ nontrivial_size e then
      SOME $ CallInterp (Op None (Cons 0) []) (Op None (Constant (to_constant e)) [])
    else NONE
End

Definition opt_interp1_def:
  opt_interp1 e =
    case opt_interp e of
    | SOME x => x
    | NONE => e
End

Definition insert_interp1_def:
  insert_interp1 e =
    case opt_interp e of
    | SOME x => x
    | NONE =>
        case e of
        | Let t ys y => Let None (MAP opt_interp1 ys) y
        | _ => e
End

Definition compile_init_def:
  compile_init b =
    Let None [Op None AllocGlobal [Op None (Const 1) []];
              if b then
                Fn (mlstring$strlit "clos_interpreter") NONE NONE 1 clos_interpreter
              else
                Op None (Cons 0) []]
      (Op None (SetGlobal 0) [Var None 1])
End

Definition attach_interpreter_def:
  attach_interpreter xs =
    compile_init (has_install_list xs) :: xs
End

Definition insert_interp_def:
  insert_interp xs = MAP insert_interp1 xs
End

(* pmatch versions of the op-functions *)

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Theorem can_interpret_op_pmatch:
  can_interpret_op p l =
    case p of
    | Cons tag => (l = 0n ∨ tag < 3n)
    | Const i => (l = 0)
    | Global n => (l = 0)
    | Constant c => (l = 0)
    | _ => F
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘p’ \\ fs [can_interpret_op_def]
QED

Theorem check_size_op_pmatch:
  check_size_op k p l =
    case p of
    | Cons tag => (if l = 0:num then k else k-1:num)
    | Const i => k
    | Global n => k
    | _ => k-1
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘p’ \\ fs [check_size_op_def]
QED

Theorem to_constant_op_pmatch:
  to_constant_op p l cs =
    case p of
    | Const i => ConstCons 1 [ConstInt i]
    | Constant c => ConstCons 1 [c]
    | Global n => ConstCons 2 [ConstInt (& n)]
    | Cons tag => (if l = 0n then ConstCons 1 [ConstCons tag []]
                             else ConstCons (tag + 5) [cs])
    | _ => ConstInt 0
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘p’ \\ fs [to_constant_op_def]
QED

val _ = export_theory();
