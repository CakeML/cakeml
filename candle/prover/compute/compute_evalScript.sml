(*
   Interpreter function for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory compute_syntaxTheory;
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "compute_eval";

val _ = numLib.prefer_num ();

fun SIMPR ths = SIMP_RULE (srw_ss()) ths;
fun SIMPC ths = SIMP_CONV (srw_ss()) ths;

(* -------------------------------------------------------------------------
 * st_ex_monad setup
 * ------------------------------------------------------------------------- *)

Datatype:
  cv_state = <| dummy : int; |>
End

Datatype:
  cv_exn = Timeout | Type_error
End

val [("dummy", get_dummy_def, set_dummy_def)] =
  define_monad_access_funs “:cv_state”;

val [(raise_Timeout_def, handle_Timeout_def),
     (raise_Type_error_def, handle_Type_error_def)] =
  define_monad_exception_functions “:cv_exn” “:cv_state”;

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = NONE,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

(* cv_state / cv_exn monad *)

Overload return[local] = “st_ex_return”;
Overload timeout[local] = “raise_Timeout”;
Overload error[local] = “raise_Type_error”;

(* Candle monad *)

Overload failwith[local] = “raise_Failure”;
Overload handle[local] = “handle_Failure”;

(* -------------------------------------------------------------------------
 * Destructuring
 * ------------------------------------------------------------------------- *)

Definition dest_num_def:
  dest_num tm =
    case tm of
      Const n t => if tm = _0 then SOME 0 else NONE
    | Comb (Const nm t) r =>
        (case dest_num r of
        | NONE => NONE
        | SOME n => if Const nm t = _BIT0_TM then SOME (2 * n)
                    else if Const nm t = _BIT1_TM then SOME (2 * n + 1)
                    else NONE)
    | _ => NONE
End

Definition dest_numeral_def:
  dest_numeral tm =
    case tm of
      Comb (Const n t) r =>
        if Const n t = _NUMERAL_TM then
          case dest_num r of
          | NONE => failwith «dest_numeral»
          | SOME n => return n
        else
          failwith «dest_numeral»
    | _ => failwith «dest_numeral»
End

Definition dest_numeral_opt_def:
  dest_numeral_opt tm =
    case tm of
      Comb (Const n t) r =>
        if Const n t = _NUMERAL_TM then
          case dest_num r of
          | NONE => NONE
          | SOME n => SOME n
        else
          NONE
    | _ => NONE
End

Definition dest_binary_def:
  dest_binary tm' tm =
    case tm of
      Comb (Comb (Const n t) l) r =>
        if tm' = Const n t then return (l, r)
        else failwith «dest_binary»
    | _ => failwith «dest_binary»
End

Definition list_dest_comb_def:
  list_dest_comb sofar (Comb f x) = list_dest_comb (x::sofar) f ∧
  list_dest_comb sofar tm = tm::sofar
End

Theorem list_dest_comb_not_nil[simp]:
  ∀sofar tm. list_dest_comb sofar tm ≠ []
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def]
QED

Theorem list_dest_comb_folds_back:
  ∀sofar tm h t.
    list_dest_comb sofar tm = h::t ⇒
      ∃xs. t = xs ++ sofar ∧
           FOLDL Comb h xs = tm
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gvs [FOLDL_APPEND]
QED

Definition term_size_alt_def:
  term_size_alt (Comb s t) = term_size_alt s + term_size_alt t ∧
  term_size_alt (Abs s t) = term_size_alt s + term_size_alt t ∧
  term_size_alt _ = 1
End

Definition list_term_size_alt_def:
  list_term_size_alt [] = 0 ∧
  list_term_size_alt (x::xs) = term_size_alt x + list_term_size_alt xs
End

Theorem list_dest_comb_term_size[local]:
  ∀sofar tm res.
    list_dest_comb sofar tm = res ⇒
      list_term_size_alt res = list_term_size_alt sofar + term_size_alt tm
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gs [list_term_size_alt_def, term_size_alt_def]
QED

Theorem list_term_size_MEM[local]:
  MEM x xs ⇒ term_size_alt x ≤ list_term_size_alt xs
Proof
  Induct_on ‘xs’
  \\ rw [list_term_size_alt_def] \\ fs []
QED

Definition mapOption_def:
  mapOption f [] = SOME [] ∧
  mapOption f (x::xs) =
    case f x of
    | NONE => NONE
    | SOME y =>
        case mapOption f xs of
        | NONE => NONE
        | SOME ys => SOME (y::ys)
End

Theorem mapOption_CONG[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      mapOption f xs = mapOption g ys
Proof
  Induct \\ rw [] \\ rw [mapOption_def]
  \\ TOP_CASE_TAC \\ gs [SF DNF_ss]
  \\ first_x_assum drule_all \\ rw []
QED

Theorem mapOption_LENGTH:
  ∀xs ys. mapOption f xs = SOME ys ⇒ LENGTH xs = LENGTH ys
Proof
  Induct \\ rw [mapOption_def]
  \\ gvs [CaseEq "option"]
QED

Definition dest_cval_def:
  dest_cval tm =
    case list_dest_comb [] tm of
    | [Var n ty] => if ty = cval_ty then SOME (Var n) else NONE
    | Const n ty :: args =>
        (case args of
        | [arg] =>
           if Const n ty = _CVAL_NUM_TM then
             case dest_numeral_opt arg of
             | NONE => NONE
             | SOME n => SOME (Num n)
           else if ty = Fun cval_ty cval_ty then
             case dest_cval arg of
             | NONE => NONE
             | SOME cv =>
                if Const n ty = _CVAL_FST_TM then
                  SOME (Fst cv)
                else if Const n ty = _CVAL_SND_TM then
                  SOME (Snd cv)
                else
                 SOME (App n [cv])
           else
             NONE
        | [l; r] =>
            (case dest_cval l of
            | NONE => NONE
            | SOME p =>
                case dest_cval r of
                | NONE => NONE
                | SOME q =>
                    if Const n ty = _CVAL_PAIR_TM then
                      SOME (Pair p q)
                    else if Const n ty = _CVAL_ADD_TM then
                      SOME (Binop Add p q)
                    else if Const n ty = _CVAL_SUB_TM then
                      SOME (Binop Sub p q)
                    else if Const n ty = _CVAL_LESS_TM then
                      SOME (Binop Less p q)
                    else if ty = Fun cval_ty (Fun cval_ty cval_ty) then
                      SOME (App n [p; q])
                    else
                      NONE)
        | [i; t; e] =>
            (case dest_cval i of
            | NONE => NONE
            | SOME p =>
                case dest_cval t of
                | NONE => NONE
                | SOME q =>
                    case dest_cval e of
                    | NONE => NONE
                    | SOME r =>
                        if Const n ty = _CVAL_IF_TM then
                          SOME (If p q r)
                        else if ty = Fun cval_ty
                                         (Fun cval_ty (Fun cval_ty cval_ty))
                             then SOME (App n [p; q; r])
                        else
                          NONE)
        | _ =>
            (case mapOption dest_cval args of
            | NONE => NONE
            | SOME cvs =>
                if ty = app_type (LENGTH cvs) then
                  SOME (App n cvs)
                else NONE))
    | _ => NONE
Termination
  wf_rel_tac ‘measure term_size_alt’ \\ rw []
  \\ drule_then assume_tac list_dest_comb_term_size
  \\ gs [list_term_size_alt_def, term_size_alt_def]
  \\ drule_then assume_tac list_term_size_MEM \\ gs []
End

(* TODO use term_size and list_size as measure instead *)

Definition do_arith_def:
  do_arith opn (Num m) (Num n) = return (Num (opn m n)) ∧
  do_arith opn (Num m) _ = return (Num m) ∧
  do_arith opn _ (Num n) = return (Num n) ∧
  do_arith opn _ _ = return (Num 0)
End

Definition do_reln_def:
  do_reln opn (Num m) (Num n) = return (Num (if opn m n then SUC 0 else 0)) ∧
  do_reln opn _ _ = return (Num 0)
End

Definition do_binop_def:
  do_binop Add p q = do_arith $+ p q ∧
  do_binop Sub p q = do_arith $- p q ∧
  do_binop Less p q = do_reln $< p q
End

Definition do_fst_def:
  do_fst (Pair p q) = return p ∧
  do_fst _ = return (Num 0)
End

Definition do_snd_def:
  do_snd (Pair p q) = return q ∧
  do_snd _ = return (Num 0)
End

Definition map_def:
  map f [] = return [] ∧
  map f (x::xs) =
    do y <- f x;
       ys <- map f xs;
       return (y::ys)
    od
End

Theorem map_CONG[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      map f xs = map g ys
Proof
  simp [FUN_EQ_THM] \\ Induct \\ rw [map_def]
  \\ once_rewrite_tac [st_ex_bind_def] \\ gs []
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ ‘map f ys = map g ys’
    suffices_by rw []
  \\ rw [FUN_EQ_THM]
QED

Theorem map_LENGTH:
  ∀xs f ys s s'.
    map f xs s = (M_success ys, s') ⇒
      LENGTH xs = LENGTH ys
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ rpt gen_tac
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ rw [] \\ fs [SF SFY_ss]
QED

Theorem map_thm:
  ∀xs f ys s s'.
    map f xs s = (M_success ys, s') ⇒
      LENGTH xs = LENGTH ys ∧
      ∀n. n < LENGTH xs ⇒ ∃r r'. f (EL n xs) r = (M_success (EL n ys), r')
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ qx_gen_tac ‘x’ \\ rpt gen_tac
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ strip_tac \\ gvs [SF SFY_ss, SF DNF_ss]
  \\ rename [‘M_success (EL _ (y::ys))’]
  \\ Cases \\ simp [SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * Interpreter for compute values
 * ------------------------------------------------------------------------- *)

Definition check_def:
  check P = if P then return () else error
End

Definition option_def:
  option f x = case f x of SOME r => return r | _ => error
End

Definition subst_def:
  subst env (Var n) =
    (case ALOOKUP env n of
     | NONE => Var n
     | SOME cv => cv) ∧
  subst env (Num n) = Num n ∧
  subst env (Pair p q) = Pair (subst env p) (subst env q) ∧
  subst env (Fst p) = Fst (subst env p) ∧
  subst env (Snd p) = Snd (subst env p) ∧
  subst env (Binop bop p q) = Binop bop (subst env p) (subst env q) ∧
  subst env (App f cs) = App f (MAP (subst env) cs) ∧
  subst env (If p q r) = If (subst env p) (subst env q) (subst env r)
Termination
  wf_rel_tac ‘measure (compute_val_size o SND)’
End

Theorem subst_empty[simp]:
  subst [] x = x
Proof
  ‘∀xs x. xs = [] ⇒ subst xs x = x’
    suffices_by rw []
  \\ ho_match_mp_tac subst_ind
  \\ rw [subst_def]
  \\ irule LIST_EQ
  \\ gs [MEM_EL, PULL_EXISTS, EL_MAP]
QED

Definition compute_eval_def:
  compute_eval ck ceqs cv =
    case cv of
    | Var s => error
    | Num n => return (Num n)
    | Pair p q =>
        do
          x <- compute_eval ck ceqs p;
          y <- compute_eval ck ceqs q;
          return (Pair x y)
        od
    | Fst p =>
        do x <- compute_eval ck ceqs p;
           do_fst x
        od
    | Snd p =>
        do x <- compute_eval ck ceqs p;
           do_snd x
        od
    | Binop bop p q =>
        do
          x <- compute_eval ck ceqs p;
          y <- compute_eval ck ceqs q;
          do_binop bop x y
        od
    | App f cs =>
        if ck = 0 then timeout else
          do
            (args,exp) <- option (ALOOKUP ceqs) f;
            check (LENGTH args = LENGTH cs);
            cs <- map (compute_eval ck ceqs) cs;
            compute_eval (ck - 1) ceqs (subst (ZIP (args,cs)) exp)
          od
    | If p q r =>
        do
          x <- compute_eval ck ceqs p;
          case x of
          | Num 0 => compute_eval ck ceqs r
          | Num _ => compute_eval ck ceqs q
          | Pair _ _ => compute_eval ck ceqs q
          | _ => error
        od
Termination
  wf_rel_tac ‘inv_image ($< LEX $<) (λ(ck,_,cv). (ck, compute_val_size cv))’
End

Definition compute_init_state_def:
  compute_init_state = <| dummy := 0 |>
End

Definition compute_eval_run_def:
  compute_eval_run ck ceqs cv =
    run (compute_eval ck ceqs cv) compute_init_state
End

val _ = export_theory ();

