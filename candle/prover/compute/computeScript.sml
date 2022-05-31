(*
  Implementation of the compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holKernelTheory
     holKernelProofTheory ml_monadBaseTheory;
open compute_syntaxTheory compute_evalTheory;

val _ = new_theory "compute";

val _ = numLib.prefer_num ();

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = SOME “raise_Failure”,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

Overload return[local] = “st_ex_return”;
Overload failwith[local] = “raise_Failure”;
Overload handle[local] = “handle_Failure”;

(* -------------------------------------------------------------------------
 * Theory initialization
 * ------------------------------------------------------------------------- *)

Definition compute_thms_def:
  compute_thms = MAP (Sequent []) [
    (* COND_TRUE  *) _COND _TRUE _M _N === _M;
    (* COND_FALSE *) _COND _FALSE _M _N === _N;
    (* NUMERAL    *) _NUMERAL _N === _N;
    (* BIT0       *) _BIT0 _N === _ADD _N _N;
    (* BIT1       *) _BIT1 _N === _SUC (_ADD _N _N);
    (* ADD        *) _ADD (_NUMERAL _0) _N === _N;
    (* ADD        *) _ADD (_SUC _M) _N === _SUC (_ADD _M _N);
    (* SUB        *) _SUB (_NUMERAL _0) _N === _NUMERAL _0;
    (* SUB        *) _SUB _M (_NUMERAL _0) === _M;
    (* SUB        *) _SUB (_SUC _M) (_SUC _N) === _SUB _M _N;
    (* MUL        *) _MUL (_NUMERAL _0) _N === _NUMERAL _0;
    (* MUL        *) _MUL (_SUC _M) _N === _ADD _N (_MUL _M _N);
    (* DIV        *) _DIV _M _N ===
                     _COND (_N === _NUMERAL _0) (_NUMERAL _0)
                           (_COND (_LESS _M _N) (_NUMERAL _0)
                                  (_SUC (_DIV (_SUB _M _N) _N)));
    (* MOD        *) _MOD _M _N ===
                     _COND (_N === _NUMERAL _0) _M
                           (_COND (_LESS _M _N) _M
                                  (_MOD (_SUB _M _N) _N));
    (* LESS       *) _LESS _M (_NUMERAL _0) === _FALSE;
    (* LESS       *) _LESS (_NUMERAL _0) (_SUC _N) === _TRUE;
    (* LESS       *) _LESS (_SUC _M) (_SUC _N) === _LESS _M _N;
    (* EQ         *) (_NUMERAL _0 === _NUMERAL _0) === _TRUE;
    (* EQ         *) (_NUMERAL _0 === _SUC _N) === _FALSE;
    (* EQ         *) (_SUC _M === _NUMERAL _0) === _FALSE;
    (* EQ         *) (_SUC _M === _SUC _N) === (_M === _N);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_ADD _M _N);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM _M;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM _N;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_SUB   *) _CVAL_SUB (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_SUB _M _N);
    (* CVAL_SUB   *) _CVAL_SUB (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM _M;
    (* CVAL_SUB   *) _CVAL_SUB (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_SUB   *) _CVAL_SUB (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_MUL   *) _CVAL_MUL (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_MUL _M _N);
    (* CVAL_MUL   *) _CVAL_MUL (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_MUL   *) _CVAL_MUL (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_MUL   *) _CVAL_MUL (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_DIV   *) _CVAL_DIV (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_DIV _M _N);
    (* CVAL_DIV   *) _CVAL_DIV (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_DIV   *) _CVAL_DIV (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_DIV   *) _CVAL_DIV (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_MOD   *) _CVAL_MOD (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_MOD _M _N);
    (* CVAL_MOD   *) _CVAL_MOD (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM _M;
    (* CVAL_MOD   *) _CVAL_MOD (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_MOD   *) _CVAL_MOD (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_LESS  *) _CVAL_LESS (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_COND (_LESS _M _N) (_SUC (_NUMERAL _0))
                                                    (_NUMERAL _0));
    (* CVAL_LESS  *) _CVAL_LESS (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_LESS  *) _CVAL_LESS (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_LESS  *) _CVAL_LESS (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_IF    *) _CVAL_IF (_CVAL_NUM (_SUC _M)) _P1 _Q1 === _P1;
    (* CVAL_IF    *) _CVAL_IF (_CVAL_PAIR _P2 _Q2) _P1 _Q1 === _P1;
    (* CVAL_IF    *) _CVAL_IF (_CVAL_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1;
    (* CVAL_FST   *) _CVAL_FST (_CVAL_PAIR _P1 _Q1) === _P1;
    (* CVAL_FST   *) _CVAL_FST (_CVAL_NUM _M) === _CVAL_NUM (_NUMERAL _0);
    (* CVAL_SND   *) _CVAL_SND (_CVAL_PAIR _P1 _Q1) === _Q1;
    (* CVAL_SND   *) _CVAL_SND (_CVAL_NUM _M) === _CVAL_NUM (_NUMERAL _0);
  ]
End

Theorem compute_thms_def = SIMP_RULE list_ss [] compute_thms_def;

Definition compute_init_def:
  compute_init ths ⇔ ths = compute_thms
End

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

Definition compute_add_def:
  compute_add ths tm =
    if ¬ (compute_init ths) then
      failwith «compute_add: wrong theorems provided for initialization»
    else
    do (l,r) <- dest_binary _ADD_TM tm;
       x <- dest_numeral l;
       y <- dest_numeral r;
       res <<- num2bit (x + y);
       c <- mk_eq (tm,_NUMERAL res);
       return (Sequent [] c)
    od ++ failwith «compute_add»
End

(* -------------------------------------------------------------------------
 * compute
 * ------------------------------------------------------------------------- *)

Definition const_list_def:
  const_list (Var n) = [] ∧
  const_list (Num n) = [] ∧
  const_list (Pair x y) = const_list x ++ const_list y ∧
  const_list (Fst x) = const_list x ∧
  const_list (Snd x) = const_list x ∧
  const_list (Binop bop x y) = const_list x ++ const_list y ∧
  const_list (If x y z) = const_list x ++ const_list y ++ const_list z ∧
  const_list (App s xs) = (s,LENGTH xs)::FLAT (MAP const_list xs)
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Definition var_list_def:
  var_list (Var n) = [n] ∧
  var_list (Num n) = [] ∧
  var_list (Pair x y) = var_list x ++ var_list y ∧
  var_list (Fst x) = var_list x ∧
  var_list (Snd x) = var_list x ∧
  var_list (Binop bop x y) = var_list x ++ var_list y ∧
  var_list (If x y z) = var_list x ++ var_list y ++ var_list z ∧
  var_list (App s xs) = FLAT (MAP var_list xs)
Termination
  wf_rel_tac ‘measure compute_val_size’
End

(* A valid equation is:
 *   [] |- const var1 ... varN = expr
 * where:
 * - var1 ... varN all have type cval_ty
 * - expr contains only the variables var1 ... varN, and has type cval_ty
 *)

Definition check_var_def:
  check_var (Var s ty) =
    (if ty = cval_ty then return s else
      failwith («Kernel.compute: ill-typed variable: » ^ s)) ∧
  check_var _ =
    failwith «Kernel.compute: non-variable argument on lhs of equation»
End

Definition check_eqn_def:
  check_eqn (Sequent h c) =
      do
        if h = [] then return () else
          failwith «Kernel.compute: non-empty hypotheses in equation»;
        (ls,r) <- dest_eq c;
        (f,vs) <- case list_dest_comb [] ls of
                  | f::vs =>
                      if ALL_DISTINCT vs then return (f,vs)
                      else failwith «Kernel.compute: variables not distinct»
                  | _ => failwith «»;
        (nm,ty) <- dest_const f ++
                failwith «Kernel.compute: not a constant being applied on lhs»;
        args <- map check_var vs;
        case dest_cval r of
        | NONE => failwith «Kernel.compute: rhs is not a cval»
        | SOME cv =>
            do
              if EVERY (λv. MEM v args) (var_list cv) then return () else
                failwith «Kernel.compute: rhs contains free variable»;
              return (nm,args,cv)
            od
      od
End

Definition compute_default_clock:
  compute_default_clock = 1000000000
End

Definition check_consts_def:
  check_consts ars fn rhs =
    if EVERY (λ(c,n). MEM (c,n) ars) (const_list rhs) then return () else
    failwith («Kernel.compute: rhs of » ^ fn ^ « has a constant » ^
              «with no equation associated to it.»)
End

Definition check_cval_closed_def:
  check_cval_closed (Var n) = F ∧
  check_cval_closed (Num n) = T ∧
  check_cval_closed (Pair p q) =
    EVERY check_cval_closed [p;q] ∧
  check_cval_closed (Fst p) =
    check_cval_closed p ∧
  check_cval_closed (Snd p) =
    check_cval_closed p ∧
  check_cval_closed (Binop bop p q) =
    EVERY check_cval_closed [p;q] ∧
  check_cval_closed (If p q r) =
    EVERY check_cval_closed [p;q;r] ∧
  check_cval_closed (App f cs) =
    EVERY check_cval_closed cs
Termination
  wf_rel_tac ‘measure compute_val_size’ \\ rw [] \\ gs []
End

Definition compute_def:
  compute ths ceqs tm =
    flip handle_Clash (λe. failwith «impossible» ) $
    if ¬compute_init ths then
      failwith «Kernel.compute: wrong theorems provided for initialization»
    else
    case dest_cval tm of
    | NONE => failwith «Kernel.compute: term is not a compute_val»
    | SOME cval =>
        do
          if check_cval_closed cval then return () else
            failwith «Kernel.compute: free variables in starting expression»;
          ceqs <- map check_eqn ceqs;
          ars <<- MAP (λ(f,(n,r)). (f,LENGTH n)) ceqs;
          map (λ(f,(n,r)). check_consts ars f r) ceqs;
          case compute_eval_run compute_default_clock ceqs cval of
          | M_failure _ => failwith «Kernel.compute: timeout»
          | M_success res =>
              do
                c <- mk_eq (tm, cval2term res);
                return (Sequent [] c)
              od
        od
End

val _ = export_theory ();

