(*
  Convert OCaml parse trees into abstract syntax trees and pretty-print them.
 *)

open preamble mlstringTheory mlintTheory;
open caml_lexTheory;

val _ = new_theory "ast";

(* Some OCaml abstract syntax.
 *)

(* -------------------------------------------------------------------------
 * Some OCaml abstract syntax.
 * ------------------------------------------------------------------------- *)

Datatype:
  lit = Lstring string
      | Lchar char
      | Lint int
      | Lbool bool
      ;
  exp = Id string
      | Lit lit
      | Binop exp exp
      | If exp exp exp
      | List (exp list)
      | Seq exp exp
      | Let bool ((string # exp) list)
      | Cons string (exp list)
      | Fun string exp
      | Match exp ((pat # exp) list)
      ;
  pat = PAny
      | PVar string
      | PCons string (pat list)
      ;
  type = TAny
       | TAs type string
       | TVar string
       | TProd type type
       | TFun type type
       | TCons string (type list)
End

Theorem type_size_lemma:
  (∀ts t. MEM t ts ⇒ type_size t < type1_size ts)
Proof
  Induct_on ‘ts’ \\ rw [] \\ gs [fetch"-""type_size_def"]
  \\ res_tac \\ fs []
QED

Theorem exp_size_lemma:
  (∀ts t. MEM t ts ⇒ exp_size t < exp5_size ts)
Proof
  Induct_on ‘ts’ \\ rw [] \\ gs [fetch"-""exp_size_def"]
  \\ res_tac \\ fs []
QED

(* -------------------------------------------------------------------------
 * Pretty-printer code copied from the OpenTheory proof checker's pretty
 * printer.
 * ------------------------------------------------------------------------- *)

Datatype:
  t = Block (t list) num num
    | String mlstring
    | Break num
End

(* Compute the distance until the next break token *)

Definition breakdist_def:
  breakdist after [] = after ∧
  breakdist after (h::t) =
    case h of
      Block _ _ n => n + breakdist after t
    | String s => strlen s + breakdist after t
    | Break _ => 0
End

Definition blanks_def:
  blanks sp n = (sp - n, List (REPLICATE n « »))
End

Definition newline_def:
  newline = «\n»
End

Definition print_list_def:
  print_list bs af sp mr [] = (sp, Nil) ∧
  print_list bs af sp mr (h::t) =
    case h of
      Block bes ind ln =>
        let (s1,r1) = print_list (sp-ind) (breakdist af t) sp mr bes;
            (s2,r2) = print_list bs af s1 mr t
        in (s2, SmartAppend r1 r2)
    | String s =>
        let (s1,r1) = print_list bs af (sp-strlen s) mr t
        in (s1, SmartAppend (List [s]) r1)
    | Break ln =>
        if ln + breakdist af t < sp then
          let (s1,r1) = blanks sp ln;
              (s2,r2) = print_list bs af s1 mr t
          in (s2, SmartAppend r1 r2)
        else
          let (s1,r1) = (mr, List [newline]);
              (s2,r2) = blanks s1 (mr-bs);
              (s3,r3) = print_list bs af s2 mr t
          in (s3, SmartAppend r1 (SmartAppend r2 r3))
Termination
  WF_REL_TAC ‘measure (t1_size o SND o SND o SND o SND)’
End

Definition pr_def:
  pr e m = SND (print_list m 0 m m [e])
End

Definition tlength_def:
  tlength t =
    case t of
      Block _ _ len => len
    | String s => strlen s
    | Break len => len
End

Definition mk_str_def:
  mk_str x = String x
End

Definition mk_brk_def:
  mk_brk x = Break x
End

Definition mk_blo_def:
  mk_blo indent es = Block es indent (SUM (MAP tlength es))
End

Definition pp_margin_def:
  pp_margin = 78n
End

(* -------------------------------------------------------------------------
 * Type printer.
 * ------------------------------------------------------------------------- *)

Definition pp_with_sep_aux_def:
  pp_with_sep_aux sep [] = [] ∧
  pp_with_sep_aux sep (h::t) = mk_str sep :: h :: pp_with_sep_aux sep t
End

Definition pp_with_sep_def:
  pp_with_sep sep p xs =
    case xs of
      [] => mk_blo 0 []
    | x::xs =>
      let ts = pp_with_sep_aux sep xs in
        if p then mk_blo 0 (mk_str «(»::x::ts ++ [mk_str «)»])
        else mk_blo 0 (x::ts)
End

Definition pp_type_def:
  pp_type (prec:num) ty =
    case ty of
      TAny => mk_str «_»
    | TVar v => mk_str («'» ^ implode v)
    | TProd s t =>
        pp_with_sep « * » (prec > 1) [pp_type 2 s; pp_type 1 t]
    | TFun s t =>
        pp_with_sep « -> » (prec > 0) [pp_type 1 s; pp_type 0 t]
    | TCons nm ts =>
        mk_blo 0 [pp_with_sep «, » T (MAP (pp_type 0) ts); mk_str (implode nm)]
Termination
  WF_REL_TAC ‘measure (type_size o SND)’ \\ rw []
  \\ imp_res_tac type_size_lemma \\ gs []
End
(*
EVAL “concat (append (pr (pp_type 0 (TFun (TFun (TVar "a") (TVar "c")) (TProd (TVar "c") (TVar "d")))) 77))”
 *)

(* -------------------------------------------------------------------------
 * Expression printer.
 * ------------------------------------------------------------------------- *)

Definition pp_paren_blk_def:
  pp_paren_blk ind p xs =
    mk_blo ind
      ((if p then [mk_str «(»] else []) ++
       xs ++
       (if p then [mk_str «)»] else []))
End

Definition pp_lit_def:
  pp_lit lit =
    case lit of
      Lstring s => mk_str («\"» ^ implode s ^ «\"»)
    | Lchar c => mk_str ( «'» ^ implode [c] ^ «'»)
    | Lint n => mk_str (toString n)
    | Lbool b => mk_str (if b then «true» else «false»)
End

Definition pp_exp_def:
  pp_exp (prec:num) exp =
    case exp of
      Id s => mk_str (implode s)
    | Lit l => pp_lit l
    | List xs =>
        mk_blo 0 [mk_str «[»; pp_with_sep «; » F (MAP (pp_exp 0) xs);
                  mk_str «]»]
    | Binop x y =>
        pp_paren_blk 0 (prec = 1001) [pp_exp 1001 x; mk_str «+»; pp_exp 1000 y]
    | Seq x y =>
        pp_paren_blk 0 (prec = 1000) [pp_exp 999 x; pp_exp 1000 y]
    | If x y z =>
        pp_paren_blk 0 (prec = 999) [mk_str «if »; pp_exp 0 x;
                                     mk_str « then »; pp_exp 0 y;
                                     mk_str « else »; pp_exp 0 z]
    | Let r binds => ARB
Termination
  WF_REL_TAC ‘measure (exp_size o SND)’ \\ rw []
  \\ imp_res_tac exp_size_lemma \\ gs []
End

(*
EVAL “concat (append (pr (pp_exp 0 (If (Id "foo") (Lit (Lchar #"c")) (Id "bar"))) 82))”
 *)

val _ = export_theory ();

