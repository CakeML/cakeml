open preamble astTheory mlintTheory
open flatLangTheory patLangTheory closLangTheory
     displayLangTheory source_to_flatTheory;

val _ = new_theory"presLang";

(*
(*
* presLang is a presentation language, encompassing intermediate languages from
* flatLang to patLang of the compiler, adopting their constructors. However, the
* constructors for patLang differ a bit since we don't want to present
* information using de bruijn indices but rather variable names.
*
* The purpose of presLang is to be an intermediate representation between an
* intermediate language of the compiler and the display language. By translating
* an intermediate language to presLang, it can be given a display representation
* by calling pres_to_display on the presLang representation. presLang has no
* semantics, as it is never evaluated, and may therefore mix operators,
* declarations, patterns and expressions.
*)

(* Special operator wrapper for presLang *)
val _ = Datatype`
  op =
    | Ast_op ast$op
    | Modlang_op flatLang$op
    | Conlang_op conLang$op
    | Patlang_op patLang$op
    | Closlang_op closLang$op`;

(* The format of a constructor, which differs by language. A Nothing constructor
* indicates a tuple pattern. *)
val _ = Datatype`
  conF =
    | Modlang_con (((modN, conN) id) option)
    | Conlang_con ((num # tid_or_exn) option)
    | Exhlang_con num`;

val _ = Datatype`
  exp =
    (* An entire program. Is divided into any number of top level prompts. *)
    | Prog (exp(*prompt*) list)
    | Prompt (modN option) (exp(*dec*) list)
    | CodeTable ((num # (varN list) # exp) list)
    (* Declarations *)
    | Dlet num exp(*exp*)
    | Dletrec ((varN # varN # exp(*exp*)) list)
    | Dtype (modN list)
    | Dexn (modN list) conN (t list)
    (* Patterns *)
    | Pany
    | Pvar varN
    | Plit lit
    | Pcon conF (exp(*pat*) list)
    | Pref exp(*pat*)
    | Ptannot exp(*pat*) t
    (* Expressions *)
    | Raise tra exp
    | Handle tra exp ((exp(*pat*) # exp) list)
    | Handle' tra exp varN exp
    | Var tra varN
    | Var_local tra varN
    | Var_global tra num
    | Extend_global tra num (* Introduced in conLang *)
    | Lit tra lit
    | Con tra conF (exp list)
      (* Application of a primitive operator to arguments.
       Includes function application. *)
    | App tra op (exp list)
    | Fun tra varN exp
    | Op tra op (exp list)
    | App' tra (num option) exp (exp list)
    | Call tra num num (exp list)
      (* Logical operations (and, or) *)
    | Log tra lop exp exp
    | If tra exp exp exp
      (* Pattern matching *)
    | Mat tra exp ((exp(*pat*) # exp) list)
      (* A let expression
         A Nothing value for the binding indicates that this is a
         sequencing expression, that is: (e1; e2). *)
    | Let tra (varN option) exp exp
    | Let' tra ((varN # exp) list) exp
      (* Local definition of (potentially) mutually recursive
         functions.
         The first varN is the function's name, and the second varN
         is its parameter. *)
    | Letrec tra ((varN # varN # exp) list) exp
    | Letrec' tra (num option) (num list option)
        ((varN # varN list # exp) list) exp
    | Fn tra (num option) (num list option) (varN list) exp
    | Seq tra exp exp
    | Tick tra exp`;

val exp_size_def = fetch "-" "exp_size_def";

(* Functions for converting intermediate languages to presLang. *)

(* flatLang *)

val MEM_pat_size = prove(
  ``!pats a. MEM a (pats:ast$pat list) ==> pat_size a < pat1_size pats``,
  Induct \\ rw [] \\ rw [astTheory.pat_size_def] \\ res_tac \\ fs []);

val flat_to_pres_pat_def = tDefine "flat_to_pres_pat" `
  flat_to_pres_pat p =
    case p of
       | ast$Pvar varN => presLang$Pvar varN
       | Pany => presLang$Pany
       | Plit lit => Plit lit
       | Pcon id pats => Pcon (Modlang_con id) (MAP flat_to_pres_pat pats)
       | Pref pat => Pref (flat_to_pres_pat pat)
       (* Won't happen, these are removed in compilation from source to flat. *)
       | Ptannot pat t => Ptannot (flat_to_pres_pat pat) t`
  (WF_REL_TAC `measure pat_size` \\ rw []
   \\ imp_res_tac MEM_pat_size \\ fs [])

val MEM_funs_size = prove(
  ``!fs v1 v2 e. MEM (v1,v2,e) fs ==> flatLang$exp_size e < exp1_size fs``,
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []);

val MEM_exps_size = prove(
  ``!exps e. MEM a exps ==> flatLang$exp_size a < exp6_size exps``,
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []);

val flat_to_pres_exp_def = tDefine"flat_to_pres_exp" `
  (flat_to_pres_exp (flatLang$Raise tra exp) = presLang$Raise tra (flat_to_pres_exp exp))
  /\
  (flat_to_pres_exp (Handle tra exp pes) =
    Handle tra (flat_to_pres_exp exp) (flat_to_pres_pes pes))
  /\
  (flat_to_pres_exp (Lit tra lit) = Lit tra lit)
  /\
  (flat_to_pres_exp (Con tra id_opt exps) = Con tra (Modlang_con id_opt) (MAP flat_to_pres_exp exps))
  /\
  (flat_to_pres_exp (Var_local tra varN) = Var_local tra varN)
  /\
  (flat_to_pres_exp (Var_global tra num) = Var_global tra num)
  /\
  (flat_to_pres_exp (Fun tra varN exp) = Fun tra varN (flat_to_pres_exp exp))
  /\
  (flat_to_pres_exp (App tra op exps) = App tra (Modlang_op op) (MAP flat_to_pres_exp exps))
  /\
  (flat_to_pres_exp (If tra exp1 exp2 exp3) =
    If tra (flat_to_pres_exp exp1) (flat_to_pres_exp exp2) (flat_to_pres_exp exp3))
  /\
  (flat_to_pres_exp (Mat tra exp pes) =
    Mat tra (flat_to_pres_exp exp) (flat_to_pres_pes pes))
  /\
  (flat_to_pres_exp (Let tra varN_opt exp1 exp2) =
    Let tra varN_opt (flat_to_pres_exp exp1) (flat_to_pres_exp exp2))
  /\
  (flat_to_pres_exp (Letrec tra funs exp) =
    Letrec tra
          (MAP (\(v1,v2,e).(v1,v2,flat_to_pres_exp e)) funs)
          (flat_to_pres_exp exp))
  /\
  (* Pattern-expression pairs *)
  (flat_to_pres_pes [] = [])
  /\
  (flat_to_pres_pes ((p,e)::pes) =
    (flat_to_pres_pat p, flat_to_pres_exp e)::flat_to_pres_pes pes)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL e => flatLang$exp_size e
                                         | INR pes => flatLang$exp3_size pes)`
   \\ rw [flatLangTheory.exp_size_def]
   \\ imp_res_tac MEM_funs_size \\ fs []
   \\ imp_res_tac MEM_exps_size \\ fs []);

val flat_to_pres_dec_def = Define`
  flat_to_pres_dec d =
    case d of
       | flatLang$Dlet num exp => presLang$Dlet num (flat_to_pres_exp exp)
       | Dletrec funs => Dletrec (MAP (\(v1,v2,e). (v1,v2,flat_to_pres_exp e)) funs)
       | Dtype mods type_def => Dtype mods
       | Dexn mods conN ts => Dexn mods conN ts`;

val flat_to_pres_prompt_def = Define`
  flat_to_pres_prompt (Prompt flatN decs) =
    Prompt flatN (MAP flat_to_pres_dec decs)`;

val flat_to_pres_def = Define`
  flat_to_pres prompts = Prog (MAP flat_to_pres_prompt prompts)`;

(* con_to_pres *)

val MEM_pat_size = prove(
  ``!pats p. MEM p pats ==> conLang$pat_size p < pat1_size pats``,
  Induct \\ rw [conLangTheory.pat_size_def]  \\ rw [] \\ res_tac \\ fs []);

val con_to_pres_pat_def = tDefine"con_to_pres_pat" `
  con_to_pres_pat p =
    case p of
       | conLang$Pvar varN => presLang$Pvar varN
       | Pany => Pany
       | Plit lit => Plit lit
       | Pcon opt ps => Pcon (Conlang_con opt) (MAP con_to_pres_pat ps)
       | Pref pat => Pref (con_to_pres_pat pat)`
  (WF_REL_TAC `measure pat_size` \\ rw []
   \\ imp_res_tac MEM_pat_size \\ fs []);

val MEM_funs_size = prove(
  ``!fs v1 v2 e. MEM (v1,v2,e) fs ==> conLang$exp_size e < exp1_size fs``,
  Induct \\ fs [conLangTheory.exp_size_def] \\ rw []
  \\ fs [conLangTheory.exp_size_def] \\ res_tac \\ fs []);

val MEM_exps_size = prove(
  ``!exps e. MEM a exps ==> conLang$exp_size a < exp6_size exps``,
  Induct \\ fs [conLangTheory.exp_size_def] \\ rw []
  \\ fs [conLangTheory.exp_size_def] \\ res_tac \\ fs []);

val con_to_pres_exp_def = tDefine"con_to_pres_exp" `
  (con_to_pres_exp (conLang$Raise t e) = Raise t (con_to_pres_exp e))
  /\
  (con_to_pres_exp (Handle t e pes) = Handle t (con_to_pres_exp e) (con_to_pres_pes pes))
  /\
  (con_to_pres_exp (Lit t l) = Lit t l)
  /\
  (con_to_pres_exp (Con t ntOpt exps) = Con t (Conlang_con ntOpt) (MAP con_to_pres_exp exps))
  /\
  (con_to_pres_exp (Var_local t varN) = Var_local t varN)
  /\
  (con_to_pres_exp (Var_global t num) = Var_global t num)
  /\
  (con_to_pres_exp (Fun t varN e) = Fun t varN (con_to_pres_exp e))
  /\
  (con_to_pres_exp (App t op exps) = App t (Conlang_op op) (MAP con_to_pres_exp exps))
  /\
  (con_to_pres_exp (Mat t e pes) = Mat t (con_to_pres_exp e) (con_to_pres_pes pes))
  /\
  (con_to_pres_exp (Let t varN e1 e2) = Let t varN (con_to_pres_exp e1)
  (con_to_pres_exp e2))
  /\
  (con_to_pres_exp (Letrec t funs e) = Letrec t (MAP (\(v1,v2,e).(v1,v2,con_to_pres_exp e)) funs) (con_to_pres_exp e))
  /\
  (con_to_pres_exp (Extend_global t num) = Extend_global t num)
  /\
  (con_to_pres_pes [] = [])
  /\
  (con_to_pres_pes ((p,e)::pes) =
    (con_to_pres_pat p, con_to_pres_exp e)::con_to_pres_pes pes)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL e => conLang$exp_size e
                                         | INR pes => conLang$exp3_size pes)`
   \\ rw [conLangTheory.exp_size_def]
   \\ imp_res_tac MEM_funs_size \\ fs []
   \\ imp_res_tac MEM_exps_size \\ fs []);

val con_to_pres_dec_def = Define`
  con_to_pres_dec d =
    case d of
       | conLang$Dlet num exp => presLang$Dlet num (con_to_pres_exp exp)
       | Dletrec funs => Dletrec (MAP (\(v1,v2,e). (v1,v2,con_to_pres_exp e)) funs)`;

val con_to_pres_prompt_def = Define`
  con_to_pres_prompt (Prompt decs) = Prompt NONE (MAP con_to_pres_dec decs)`;

val con_to_pres_def = Define`
  con_to_pres prompts = Prog (MAP con_to_pres_prompt prompts)`;

(* exh_to_pres *)

val MEM_pat_size = prove(
  ``!pats p. MEM p pats ==> exhLang$pat_size p < pat1_size pats``,
  Induct \\ rw [exhLangTheory.pat_size_def]  \\ rw [] \\ res_tac \\ fs []);

val exh_to_pres_pat_def = tDefine"exh_to_pres_pat"`
  exh_to_pres_pat p =
    case p of
       | exhLang$Pvar varN => presLang$Pvar varN
       | Pany => Pany
       | Plit lit => Plit lit
       | Pcon num ps => Pcon (Exhlang_con num) (MAP exh_to_pres_pat ps)
       | Pref pat => Pref (exh_to_pres_pat pat)`
  (WF_REL_TAC `measure pat_size` \\ rw []
   \\ imp_res_tac MEM_pat_size \\ fs []);

val MEM_funs_size = prove(
  ``!fs v1 v2 e. MEM (v1,v2,e) fs ==> exhLang$exp_size e < exp1_size fs``,
  Induct \\ fs [exhLangTheory.exp_size_def] \\ rw []
  \\ fs [exhLangTheory.exp_size_def] \\ res_tac \\ fs []);

val MEM_exps_size = prove(
  ``!exps e. MEM a exps ==> exhLang$exp_size a < exp6_size exps``,
  Induct \\ fs [exhLangTheory.exp_size_def] \\ rw []
  \\ fs [exhLangTheory.exp_size_def] \\ res_tac \\ fs []);

val exh_to_pres_exp_def = tDefine"exh_to_pres_exp"`
  (exh_to_pres_exp (exhLang$Raise t e) = Raise t (exh_to_pres_exp e))
  /\
  (exh_to_pres_exp (Handle t e pes) = Handle t (exh_to_pres_exp e) (exh_to_pres_pes pes))
  /\
  (exh_to_pres_exp (Lit t l) = Lit t l)
  /\
  (exh_to_pres_exp (Con t n es) = Con t (Exhlang_con n) (MAP exh_to_pres_exp es))
  /\
  (exh_to_pres_exp (Var_local t varN) = Var_local t varN)
  /\
  (exh_to_pres_exp (Var_global t n) = Var_global t n)
  /\
  (exh_to_pres_exp (Fun t varN e) = Fun t varN (exh_to_pres_exp e))
  /\
  (exh_to_pres_exp (App t op es) = App t (Conlang_op op) (MAP exh_to_pres_exp es))
  /\
  (exh_to_pres_exp (Mat t e pes) = Mat t (exh_to_pres_exp e) (exh_to_pres_pes pes))
  /\
  (exh_to_pres_exp (Let t varN e1 e2) = Let t varN (exh_to_pres_exp e1) (exh_to_pres_exp e2))
  /\
  (exh_to_pres_exp (Letrec t funs e1) = Letrec t (MAP (\(v1,v2,e).(v1,v2,exh_to_pres_exp e)) funs) (exh_to_pres_exp e1))
  /\
  (exh_to_pres_exp (Extend_global t n) = Extend_global t n)
  /\
  (exh_to_pres_pes [] = [])
  /\
  (exh_to_pres_pes ((p,e)::pes) =
    (exh_to_pres_pat p, exh_to_pres_exp e)::exh_to_pres_pes pes)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL e => exhLang$exp_size e
                                         | INR pes => exhLang$exp3_size pes)`
   \\ rw [exhLangTheory.exp_size_def]
   \\ imp_res_tac MEM_funs_size \\ fs []
   \\ imp_res_tac MEM_exps_size \\ fs []);

(* pat to pres. *)

val num_to_varn_def = tDefine "num_to_varn" `
  num_to_varn n = if n < 26 then [CHR (97 + n)]
                  else (num_to_varn ((n DIV 26)-1)) ++ ([CHR (97 + (n MOD 26))])`
  (WF_REL_TAC `measure I` \\ rw [] \\ fs [DIV_LT_X]);

val MEM_exps_size = prove(
  ``!exps e. MEM a exps ==> patLang$exp_size a < exp1_size exps``,
  Induct \\ fs [patLangTheory.exp_size_def] \\ rw []
  \\ fs [patLangTheory.exp_size_def] \\ res_tac \\ fs []);

(* The constructors in pat differ a bit because of de bruijn indices. This is
* solved with the argument h, referring to head of our indexing. Combined with
* num_to_varn this means we create varNs to match the presLang-constructors
* where either nums or no name at all were provided. *)
val pat_to_pres_exp_def = tDefine "pat_to_pres_exp" `
  (pat_to_pres_exp h (Raise t e) = Raise t (pat_to_pres_exp h e))
  /\
  (pat_to_pres_exp h (Handle t e1 e2) =
    Handle t (pat_to_pres_exp h e1) [(Pvar (num_to_varn h), pat_to_pres_exp (h+1) e2)])
  /\
  (pat_to_pres_exp h (Lit t lit) = Lit t lit)
  /\
  (pat_to_pres_exp h (Con t num es) =
    Con t (Exhlang_con num) (MAP (pat_to_pres_exp h) es))
  /\
  (pat_to_pres_exp h (Var_local t var_index) = Var_local t (num_to_varn (h-var_index-1)))
  /\
  (pat_to_pres_exp h (Var_global t num) = Var_global t num)
  /\
  (pat_to_pres_exp h (Fun t e) = Fun t (num_to_varn h) (pat_to_pres_exp (h+1) e))
  /\
  (pat_to_pres_exp h (App t op es) =
    App t (Patlang_op op) (MAP (pat_to_pres_exp h) es))
  /\
  (pat_to_pres_exp h (If t e1 e2 e3) =
    If t (pat_to_pres_exp h e1) (pat_to_pres_exp h e2) (pat_to_pres_exp h e3))
  /\
  (pat_to_pres_exp h (Let t e1 e2) =
    Let t (SOME (num_to_varn h)) (pat_to_pres_exp h e1) (pat_to_pres_exp (h+1) e2))
  /\
  (pat_to_pres_exp h (Seq t e1 e2) = Seq t (pat_to_pres_exp h e1) (pat_to_pres_exp h e2))
  /\
  (pat_to_pres_exp h (Letrec t es e) =
    let len = LENGTH es in
      Letrec t (es_to_pres_tups h (len-1) len es) (pat_to_pres_exp (h+len) e))
  /\
  (pat_to_pres_exp h (Extend_global t num) = Extend_global t num)
  /\
  (* Gives letrec functions names and variable names. *)
  (es_to_pres_tups _ _ _ [] = [])
  /\
  (es_to_pres_tups h i len (e::es) =
    (num_to_varn (h+i), num_to_varn (h+len), pat_to_pres_exp (h+len+1) e)
    ::es_to_pres_tups h (i-1) len es)`
 (WF_REL_TAC `measure (\x. case x of INL (_,e) => exp_size e
                                   | INR (_,_,_,es) => exp1_size es)`
  \\ rw [patLangTheory.exp_size_def]
  \\ imp_res_tac MEM_exps_size \\ fs []);

(* clos to pres. *)

val num_to_varn_list_def = Define `
  num_to_varn_list h n =
    if n = 0 then [] else
      num_to_varn (h + n) :: num_to_varn_list h (n-1)`

(* The clos_to_pres function uses the same approach to de bruijn
* indices as the pat_to_pres function *)
val clos_to_pres_def = tDefine "clos_to_pres" `
  (clos_to_pres h (Var t n) = Var t (num_to_varn (h-n-1))) /\
  (clos_to_pres h (closLang$Let t xs x) =
     presLang$Let' t
       (clos_to_pres_tups h (LENGTH xs - 1) xs)
       (clos_to_pres (h + LENGTH xs) x)) /\
  (clos_to_pres h (If t x1 x2 x3) =
     If t (clos_to_pres h x1) (clos_to_pres h x2) (clos_to_pres h x3)) /\
  (clos_to_pres h (Raise t x) = Raise t (clos_to_pres h x)) /\
  (clos_to_pres h (Tick t x) = Tick t (clos_to_pres h x)) /\
  (clos_to_pres h (Handle t x y) =
     Handle' t (clos_to_pres h x) (num_to_varn h) (clos_to_pres (h+1) y)) /\
  (clos_to_pres h (Call t n1 n2 xs) = Call t n1 n2 (clos_to_pres_list h xs)) /\
  (clos_to_pres h (App t n0 x xs) =
     App' t n0 (clos_to_pres h x) (clos_to_pres_list h xs)) /\
  (clos_to_pres h (Op t op xs) =
     Op t (Closlang_op op) (clos_to_pres_list h xs)) /\
  (clos_to_pres h (Fn t n1 n2 vn x) =
     Fn t n1 n2 (num_to_varn_list h vn) (clos_to_pres h x)) /\
  (clos_to_pres h (closLang$Letrec t n1 n2 es e) =
    let len = LENGTH es in
      Letrec' t n1 n2 (fun_to_pres_tups h (len-1) len es)
        (clos_to_pres (h+len) e)) /\
  (clos_to_pres_list h [] = []) /\
  (clos_to_pres_list h (x::xs) =
     clos_to_pres h x :: clos_to_pres_list h xs) /\
  (clos_to_pres_tups h i [] = []) /\
  (clos_to_pres_tups h i (x::xs) =
     (num_to_varn (h+i), clos_to_pres h x) :: clos_to_pres_tups h (i-1) xs) /\
  (fun_to_pres_tups h i len [] = []:(varN # varN list # exp) list) /\
  (fun_to_pres_tups h i len ((vn,e)::es) =
    ((num_to_varn (h+i)):string,
     num_to_varn_list (h+len-1) vn,
     (clos_to_pres (h+len+vn) e):exp)
    :: ((fun_to_pres_tups h (i-1) len es : (varN # varN list # exp) list)))`
 (WF_REL_TAC `measure (\x. case x of
    | INL (_,e) => exp_size e
    | INR (INL (_,es)) => exp3_size es
    | INR (INR (INL (_,_,es))) => exp3_size es
    | INR (INR (INR (_,_,_,es))) => exp1_size es)`)

val clos_to_pres_code_def = Define `
  clos_to_pres_code code_table =
    CodeTable
      (MAP (\(n,arity,body). (n,num_to_varn_list 0 arity,
         clos_to_pres arity body)) code_table)`

(* Helpers for converting pres to display. *)
val empty_item_def = Define`
  empty_item name = Item NONE name []`;

val string_to_display_def = Define`
  string_to_display s = empty_item ("\"" ++ s ++ "\"")`;

val num_to_display_def = Define`
  num_to_display n = empty_item (explode (toString (&n)))`;

val word_size_to_display_def = Define`
  (word_size_to_display W8 = empty_item "W8")
  /\
  (word_size_to_display W64 = empty_item "W64")`;

val opn_to_display_def = Define`
  (opn_to_display Plus = empty_item "Plus")
  /\
  (opn_to_display Minus = empty_item "Minus")
  /\
  (opn_to_display Times = empty_item "Times")
  /\
  (opn_to_display Divide = empty_item "Divide")
  /\
  (opn_to_display Modulo = empty_item "Modulo")`;

val opb_to_display_def = Define`
  (opb_to_display Lt = empty_item "Lt")
  /\
  (opb_to_display Gt = empty_item "Gt")
  /\
  (opb_to_display Leq = empty_item "Leq")
  /\
  (opb_to_display Geq = empty_item "Geq")`;

val opw_to_display_def = Define`
  (opw_to_display Andw = empty_item "Andw")
  /\
  (opw_to_display Orw = empty_item "Orw")
  /\
  (opw_to_display Xor = empty_item "Xor")
  /\
  (opw_to_display Add = empty_item "Add")
  /\
  (opw_to_display Sub = empty_item "Sub")`;

val shift_to_display_def = Define`
  (shift_to_display Lsl = empty_item "Lsl")
  /\
  (shift_to_display Lsr = empty_item "Lsr")
  /\
  (shift_to_display Asr = empty_item "Asr")
  /\
  (shift_to_display Ror = empty_item "Ror")`;

val op_to_display_def = tDefine "op_to_display"`
  (op_to_display (Patlang_op (Tag_eq n1 n2)) =
    Item NONE "Tag_eq" [(num_to_display n1);(num_to_display n2)])
  /\
  (op_to_display (Patlang_op (El num)) = Item NONE "El" [num_to_display num])
  /\
  (op_to_display (Patlang_op (Op op)) = op_to_display (Conlang_op op))
  /\
  (op_to_display (Conlang_op (Init_global_var num)) =
    Item NONE "Init_global_var" [num_to_display num])
  /\
  (op_to_display (Conlang_op (Op astop)) = Item NONE "Op" [op_to_display (Modlang_op (astop))])
  /\
  (op_to_display (Ast_op AallocEmpty) = empty_item "AallocEmpty")
  /\
  (op_to_display (Ast_op astop) = op_to_display (Modlang_op (astOp_to_flatOp astop)))
  /\
  (op_to_display (Modlang_op (Opn opn)) = Item NONE "Opn" [opn_to_display opn])
  /\
  (op_to_display (Modlang_op (Opb opb)) = Item NONE "Opb" [opb_to_display opb])
  /\
  (op_to_display (Modlang_op (Opw word_size opw)) =
    Item NONE "Opw" [ word_size_to_display word_size; opw_to_display opw ])
  /\
  (op_to_display (Modlang_op (Shift word_size shift num)) =
    Item NONE "Shift" [
      word_size_to_display word_size;
      shift_to_display shift;
      num_to_display num
  ])
  /\
  (op_to_display (Modlang_op Equality) = empty_item "Equality")
  /\
  (op_to_display (Modlang_op Opapp) = empty_item "Opapp")
  /\
  (op_to_display (Modlang_op Opassign) = empty_item "Opassign")
  /\
  (op_to_display (Modlang_op Opref) = empty_item "Opref")
  /\
  (op_to_display (Modlang_op Opderef) = empty_item "Opderef")
  /\
  (op_to_display (Modlang_op Aw8alloc) = empty_item "Aw8alloc")
  /\
  (op_to_display (Modlang_op Aw8sub) = empty_item "Aw8sub")
  /\
  (op_to_display (Modlang_op Aw8length) = empty_item "Aw8length")
  /\
  (op_to_display (Modlang_op Aw8update) = empty_item "Aw8update")
  /\
  (op_to_display (Modlang_op (WordFromInt word_size)) =
    Item NONE "WordFromInt" [word_size_to_display word_size])
  /\
  (op_to_display (Modlang_op (WordToInt word_size)) =
    Item NONE "WordToInt" [word_size_to_display word_size])
  /\
  (op_to_display (Modlang_op CopyStrStr) = empty_item "CopyStrStr")
  /\
  (op_to_display (Modlang_op CopyStrAw8) = empty_item "CopyStrAw8")
  /\
  (op_to_display (Modlang_op CopyAw8Str) = empty_item "CopyAw8Str")
  /\
  (op_to_display (Modlang_op CopyAw8Aw8) = empty_item "CopyAw8Aw8")
  /\
  (op_to_display (Modlang_op Ord) = empty_item "Ord")
  /\
  (op_to_display (Modlang_op Chr) = empty_item "Chr")
  /\
  (op_to_display (Modlang_op (Chopb opb)) =
    Item NONE "Chopb" [opb_to_display opb])
  /\
  (op_to_display (Modlang_op Implode) = empty_item "Implode")
  /\
  (op_to_display (Modlang_op Strsub) = empty_item "Strsub")
  /\
  (op_to_display (Modlang_op Strlen) = empty_item "Strlen")
  /\
  (op_to_display (Modlang_op Strcat) = empty_item "Strcat")
  /\
  (op_to_display (Modlang_op VfromList) = empty_item "VfromList")
  /\
  (op_to_display (Modlang_op Vsub) = empty_item "Vsub")
  /\
  (op_to_display (Modlang_op Vlength) = empty_item "Vlength")
  /\
  (op_to_display (Modlang_op Aalloc) = empty_item "Aalloc")
  /\
  (op_to_display (Modlang_op Asub) = empty_item "Asub")
  /\
  (op_to_display (Modlang_op Alength) = empty_item "Alength")
  /\
  (op_to_display (Modlang_op Aupdate) = empty_item "Aupdate")
  /\
  (op_to_display (Modlang_op (FFI str)) =
    Item NONE "FFI" [string_to_display str])
  /\
  (op_to_display (Closlang_op op) = empty_item "TODO_some_closLang_op")
  ∧
  (op_to_display _ = empty_item "Unknown")`
( wf_rel_tac`inv_image ($< LEX $<)
    (λx. case x of (Ast_op op) => (1,op_size op) | x => (0n,op_size x))` )

val lop_to_display_def = Define`
  (lop_to_display ast$And = empty_item "And")
  /\
  (lop_to_display Or = empty_item "Or")
  /\
  (lop_to_display _ = empty_item "Unknown")`;

val num_to_hex_digit_def = Define `
  num_to_hex_digit n =
    if n < 10 then [CHR (48 + n)] else
    if n < 16 then [CHR (55 + n)] else []`;

val num_to_hex_def = Define `
  num_to_hex n =
    (if n < 16 then [] else num_to_hex (n DIV 16)) ++
    num_to_hex_digit (n MOD 16)`;

val word_to_hex_string_def = Define `
  word_to_hex_string w = "0x" ++ num_to_hex (w2n (w:'a word))`;

val lit_to_display_def = Define`
  (lit_to_display (IntLit i) =
    Item NONE "IntLit" [empty_item (explode (toString i))])
  /\
  (lit_to_display (Char c) =
    Item NONE "Char" [empty_item ("#\"" ++ [c] ++ "\"")])
  /\
  (lit_to_display (StrLit s) =
    Item NONE "StrLit" [string_to_display s])
  /\
  (lit_to_display (Word8 w) =
    Item NONE "Word8" [empty_item (word_to_hex_string w)])
  /\
  (lit_to_display (Word64 w) =
    Item NONE "Word64" [empty_item (word_to_hex_string w)])`;

val list_to_display_def = Define`
  (list_to_display f xs = List (MAP f xs))`

val option_to_display_def = Define`
  (option_to_display f opt = case opt of
                      | NONE => empty_item "NONE"
                      | SOME opt' => Item NONE "SOME" [f opt'])`

val option_string_to_display_def = Define`
  (option_string_to_display opt = case opt of
                      | NONE => empty_item "NONE"
                      | SOME opt' => Item NONE "SOME" [string_to_display opt'])`

val id_to_display_def = Define`
  (id_to_display (Long name i) = Item NONE "Long" [id_to_display i; string_to_display name])
  /\
  (id_to_display (Short name) = Item NONE "Short" [string_to_display name])`;

val tctor_to_display_def = Define`
  (tctor_to_display (ast$TC_name ids) =
    let ids' = id_to_display ids in
      Item NONE "TC_name" [ids'])
  /\
  (tctor_to_display TC_int = empty_item "TC_int")
  /\
  (tctor_to_display TC_char = empty_item "TC_char")
  /\
  (tctor_to_display TC_string = empty_item "TC_string")
  /\
  (tctor_to_display TC_ref = empty_item "TC_ref")
  /\
  (tctor_to_display TC_word8 = empty_item "TC_word8")
  /\
  (tctor_to_display TC_word64 = empty_item "TC_word64")
  /\
  (tctor_to_display TC_word8array = empty_item "TC_word8array")
  /\
  (tctor_to_display TC_fn = empty_item "TC_fn")
  /\
  (tctor_to_display TC_tup = empty_item "TC_tup")
  /\
  (tctor_to_display TC_exn = empty_item "TC_exp")
  /\
  (tctor_to_display TC_vector = empty_item "TC_vector")
  /\
  (tctor_to_display TC_array = empty_item "TC_array")`

val MEM_t_size = prove(
  ``!ts t. MEM t ts ==> t_size t < t1_size ts``,
  Induct \\ fs [t_size_def] \\ rw [] \\ res_tac \\ fs []);

val t_to_display_def = tDefine "t_to_display" `
  (t_to_display (Tvar tvarN) = Item NONE "Tvar" [string_to_display tvarN])
  /\
  (t_to_display (Tvar_db n) = Item NONE "Tvar_db" [num_to_display n])
  /\
  (t_to_display (Tapp ts tctor) = Item NONE "Tapp" [List (MAP t_to_display ts); tctor_to_display tctor])`
  (WF_REL_TAC `measure t_size` \\ rw []
   \\ imp_res_tac MEM_t_size \\ fs []);

val tid_or_exn_to_display_def = Define`
  tid_or_exn_to_display te =
   let (name, id) =
     case te of
       | TypeId id => ("TypeId", id)
       | TypeExn id => ("TypeExn", id) in
     Item NONE name [id_to_display id]`;

val conf_to_display_def = Define`
  conf_to_display con =
    let none = empty_item "NONE" in
      case con of
         | Modlang_con NONE => none
         | Conlang_con NONE => none
         | Modlang_con (SOME id) => Item NONE "SOME" [id_to_display id]
         | Conlang_con (SOME (n,t)) =>
            Item NONE "SOME" [Tuple [num_to_display n; tid_or_exn_to_display t]]
         | Exhlang_con c => Item NONE "SOME" [num_to_display c]`;

(* Takes a presLang$exp and produces jsonLang$obj that mimics its structure. *)

val MEM_exp_size = prove(
  ``!xs x. MEM x xs ==> exp_size x < exp12_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val MEM_expTup_size = prove(
  ``!xs x y. MEM (x,y) xs ==>
             exp_size x < exp10_size xs /\ exp_size y < exp10_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val MEM_varexpTup_size = prove(
  ``!xs x y z. MEM (x,y,z) xs ==> exp_size z < exp4_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val MEM_varexpTup1_size = prove(
  ``!xs x y z. MEM (x,y,z) xs ==> exp_size z < exp1_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val MEM_varexpTup3_size = prove(
  ``!xs x y z. MEM (x,y,z) xs ==> exp_size z < exp3_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val MEM_varexpTup6_size = prove(
  ``!xs x z. MEM (x,z) xs ==> exp_size z < exp8_size xs``,
  Induct \\ fs [exp_size_def] \\ rw [] \\ res_tac \\ fs [exp_size_def]);

val pres_to_display_def = tDefine"pres_to_display" `
  (* Top level *)
  (pres_to_display (presLang$Prog tops) =
    let tops' = List (MAP pres_to_display tops) in
      Item NONE "Prog" [tops'])
  /\
  (pres_to_display (Prompt modN decs) =
    let decs' = List (MAP pres_to_display decs) in
    let modN' = option_string_to_display modN in
      Item NONE "Prompt" [modN'; decs'])
  /\
  (pres_to_display (Dlet num exp) =
      Item NONE "Dlet" [num_to_display num; pres_to_display exp])
  /\
  (pres_to_display (Dletrec lst) =
    let fields =
      List (MAP (\ (v1, v2, exp) . Tuple [string_to_display v1; string_to_display v2; pres_to_display exp]) lst) in
      Item NONE "Dletrec" [fields] )
  /\
  (pres_to_display (Dtype modNs) =
    let modNs' = List (MAP string_to_display modNs) in
      Item NONE "Dtype" [modNs'])
  /\
  (pres_to_display (Dexn modNs conN ts) =
    let modNs' = List (MAP string_to_display modNs) in
    let ts' = List (MAP t_to_display ts) in
      Item NONE "Dexn" [modNs'; string_to_display conN; ts'])
  /\
  (pres_to_display Pany = empty_item "Pany")
  /\
  (pres_to_display (Pvar varN) =
      Item NONE "Pvar" [string_to_display varN])
  /\
  (pres_to_display (Plit lit) =
      Item NONE "Plit" [lit_to_display lit])
  /\
  (pres_to_display (Pcon conF exps) =
    let exps' = List (MAP pres_to_display exps) in
      Item NONE "Pcon" [conf_to_display conF; exps'])
  /\
  (pres_to_display (Pref exp) =
      Item NONE "Pref" [pres_to_display exp])
  /\
  (pres_to_display (Ptannot exp t) =
      Item NONE "Ptannot" [pres_to_display exp; t_to_display t])
  /\
  (pres_to_display (Raise tra exp) =
      Item (SOME tra) "Raise" [pres_to_display exp])
  /\
  (pres_to_display (Tick tra exp) =
      Item (SOME tra) "Tick" [pres_to_display exp])
  /\
  (pres_to_display (Handle tra exp expsTup) =
    let expsTup' = List (MAP (\(e1, e2) . Tuple [pres_to_display e1; pres_to_display e2]) expsTup) in
      Item (SOME tra) "Handle" [pres_to_display exp; expsTup'])
  /\
  (pres_to_display (Handle' tra exp varN exp2) =
    Item (SOME tra) "Handle" [pres_to_display exp;
                              string_to_display varN;
                              pres_to_display exp])
  /\
  (pres_to_display (Var tra varN) =
      Item (SOME tra) "Var" [string_to_display varN])
  /\
  (pres_to_display (Var_local tra varN) =
      Item (SOME tra) "Var_local" [string_to_display varN])
  /\
  (pres_to_display (Var_global tra num) =
      Item (SOME tra) "Var_global" [num_to_display num])
  /\
  (pres_to_display (Extend_global tra num) =
      Item (SOME tra) "Extend_global" [num_to_display num])
  /\
  (pres_to_display (Lit tra lit) =
      Item (SOME tra) "Lit" [lit_to_display lit])
  /\
  (pres_to_display (Con tra conF exps) =
    let exps' = List (MAP pres_to_display exps) in
      Item (SOME tra) "Pcon" [conf_to_display conF; exps'])
  /\
  (pres_to_display (App tra op exps) =
    let exps' = List (MAP pres_to_display exps) in
      Item (SOME tra) "App" [op_to_display op; exps'])
  /\
  (pres_to_display (Op tra op exps) =
    let exps' = List (MAP pres_to_display exps) in
      Item (SOME tra) "Op" [op_to_display op; exps'])
  /\
  (pres_to_display (Fun tra varN exp) =
      Item (SOME tra) "Fun" [string_to_display varN; pres_to_display exp])
  /\
  (pres_to_display (Fn tra n0 n1 varN exp) =
      Item (SOME tra) "Fn"
        [option_to_display num_to_display n0;
         option_to_display (list_to_display num_to_display) n1;
         list_to_display string_to_display varN;
         pres_to_display exp])
  /\
  (pres_to_display (Log tra lop exp1 exp2) =
      Item (SOME tra) "Log" [lop_to_display lop; pres_to_display exp1; pres_to_display exp2])
  /\
  (pres_to_display (If tra exp1 exp2 exp3) =
      Item (SOME tra) "If" [pres_to_display exp1; pres_to_display exp2; pres_to_display exp3])
  /\
  (pres_to_display (Mat tra exp expsTup) =
    let expsTup' = List (MAP (\(e1, e2) . Tuple [pres_to_display e1; pres_to_display e2]) expsTup) in
      Item (SOME tra) "Mat" [pres_to_display exp; expsTup'])
  /\
  (pres_to_display (Let tra varN exp1 exp2) =
    let varN' = option_string_to_display varN in
      Item (SOME tra) "Let" [varN'; pres_to_display exp1; pres_to_display exp2])
  /\
  (pres_to_display (Letrec tra varexpTup exp) =
    let varexpTup' = List (MAP (\ (v1, v2, e) . Tuple [
      string_to_display v1;
      string_to_display v2;
      pres_to_display e
    ]) varexpTup) in
      Item (SOME tra) "Letrec" [varexpTup'; pres_to_display exp])
  /\
  (pres_to_display (Letrec' tra n1 n2 varexpTup exp) =
    let varexpTup' = List (MAP (\ (v1, args, e) . Tuple [
      string_to_display v1;
      List (MAP string_to_display args);
      pres_to_display e
    ]) varexpTup) in
      Item (SOME tra) "Letrec"
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         varexpTup';
         pres_to_display exp])
  /\
  (pres_to_display (Let' tra varexpTup exp) =
    let varexpTup' = List (MAP (\ (v1, e) . Tuple [
      string_to_display v1;
      pres_to_display e
    ]) varexpTup) in
      Item (SOME tra) "Let"
        [varexpTup';
         pres_to_display exp])
  /\
  (pres_to_display (Seq tra e1 e2) =
    Item (SOME tra) "Seq" [pres_to_display e1; pres_to_display e2])
  /\
  (pres_to_display (Call tra ticks dest es) =
    Item (SOME tra) "Call"
      [num_to_display ticks;
       num_to_display dest;
       List (MAP (\e. pres_to_display e) es)])
  /\
  (pres_to_display (App' tra n1 e exps) =
      Item (SOME tra) "App"
        [option_to_display num_to_display n1;
         pres_to_display e;
         List (MAP (\e. pres_to_display e) exps)]) /\
  (pres_to_display (CodeTable code_table) =
    Item NONE "CodeTable"
      [List (MAP (\(n,args,e).
         Tuple [num_to_display n;
                list_to_display string_to_display args;
                pres_to_display e]) code_table)])`
 (WF_REL_TAC `measure exp_size` \\ rw []
  \\ imp_res_tac MEM_exp_size \\ fs []
  \\ imp_res_tac MEM_expTup_size \\ fs []
  \\ imp_res_tac MEM_varexpTup_size \\ fs []
  \\ imp_res_tac MEM_varexpTup1_size \\ fs []
  \\ imp_res_tac MEM_varexpTup3_size \\ fs []
  \\ imp_res_tac MEM_varexpTup6_size \\ fs []);

(* Function to construct general functions from a language to JSON. Call with
* the name of the language and what fucntion to use to convert it to preslang to
* obtain a function which takes a program in an intermediate language and
* returns a JSON representation of that program. *)
val lang_to_json_def = Define`
  lang_to_json langN func =
    \ p . Object [
      ("lang", String langN);
      ("prog", display_to_json (pres_to_display (func p)))]`;

val flat_to_json_def = Define`
  flat_to_json = lang_to_json "flatLang" flat_to_pres`;

val con_to_json_def = Define`
  con_to_json = lang_to_json "conLang" con_to_pres`;

(* decLang uses the same structure as conLang, but the compilation step from con
* to dec returns an expression rather than a prompt. *)
val dec_to_json_def = Define`
  dec_to_json = lang_to_json "decLang" con_to_pres_exp`;

val exh_to_json_def = Define`
  exh_to_json = lang_to_json "exhLang" exh_to_pres_exp`;

(* pat_to_pres is initiated with a 0 because of how we want to convert de bruijn
* indices to variable names and need to keep track of where head is at
* currently, beginning at 0 *)
val pat_to_json_def = Define`
  pat_to_json = lang_to_json "patLang" (pat_to_pres_exp 0)`;

val clos_to_json_def = Define`
  clos_to_json suffix = lang_to_json ("closLang" ++ suffix) (clos_to_pres 0)`;

val clos_to_json_table_def = Define`
  clos_to_json_table suffix =
    lang_to_json ("closLang" ++ suffix) clos_to_pres_code`;
    *)

val _ = export_theory();
