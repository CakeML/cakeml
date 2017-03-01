open preamble astTheory jsonTheory backend_commonTheory;
open modLangTheory;

val _ = new_theory"presLang";

(* 
* presLang is a presentation language, encompassing many intermediate languages
* of the compiler, adopting their constructors. The purpose of presLang is to be
* an intermediate representation between an intermediate language of the
* compiler and JSON. By translating an intermediate language to presLang, it can
* be given a JSON representation by calling to_json on the presLang
* representation. presLang has no semantics, as it is never evaluated, and may
* therefore mix operators, declarations, patterns and expressions.
*)

(* Special operator wrapper for presLang *)
val _ = Datatype`
  op =
    Ast ast$op`;

val _ = Datatype`
  exp =
    (* An entire program. Is divided into any number of top level prompts. *)
    | Prog (exp(*prompt*) list)
    | Prompt (modN option) (exp(*dec*) list)
    (* Declarations *)
    | Dlet num exp(*exp*)
    | Dletrec ((varN # varN # exp(*exp*)) list)
    | Dtype (modN list) type_def
    | Dexn (modN list) conN (t list)
    (* Patterns *)
    | Pvar varN
    | Plit lit
    | Pcon (((modN, conN) id) option) (exp(*pat*) list)
    | Pref exp(*pat*)
    | Ptannot exp(*pat*) t
    (* Expressions *)
    | Raise tra exp
    | Handle tra exp ((exp(*pat*) # exp) list)
    | Var_local tra varN
    | Var_global tra num
    | Lit tra lit
      (* Constructor application.
       A Nothing constructor indicates a tuple pattern. *)
    | Con tra (((modN, conN) id) option) (exp list)
      (* Application of a primitive operator to arguments.
       Includes function application. *)
    | App tra op (exp list)
    | Fun tra varN exp
      (* Logical operations (and, or) *)
    | Log tra lop exp exp
    | If tra exp exp exp
      (* Pattern matching *)
    | Mat tra exp ((exp(*pat*) # exp) list)
      (* A let expression
         A Nothing value for the binding indicates that this is a
         sequencing expression, that is: (e1; e2). *)
    | Let tra (varN option) exp exp
      (* Local definition of (potentially) mutually recursive
         functions.
         The first varN is the function's name, and the second varN
         is its parameter. *)
    | Letrec tra ((varN # varN # exp) list) exp`;

(* TODO: Implement to_json based on presLang structure. *)
val to_json_def = tDefine "to_json"`
  to_json _ = json$Null`
  cheat;

(* Functions for converting intermediate languages to presLang. *)

(* modLang *)

val mod_to_pres_pat_def = tDefine "mod_to_pres_pat"`
  mod_to_pres_pat p =
    case p of
       | ast$Pvar varN => presLang$Pvar varN
       | Plit lit => Plit lit
       | Pcon id pats => Pcon id (MAP mod_to_pres_pat pats)
       | Pref pat => Pref (mod_to_pres_pat pat)
       (* Won't happen, these are removed in compilation from source to mod. *)
       | Ptannot pat t => Ptannot (mod_to_pres_pat pat) t`
   cheat;

val mod_to_pres_exp_def = tDefine"mod_to_pres_exp"`
  (mod_to_pres_exp (modLang$Raise tra exp) = presLang$Raise tra (mod_to_pres_exp exp))
  /\
  (mod_to_pres_exp (Handle tra exp pes) =
    Handle tra (mod_to_pres_exp exp) (mod_to_pres_pes pes))
  /\
  (mod_to_pres_exp (Lit tra lit) = Lit tra lit)
  /\
  (mod_to_pres_exp (Con tra id_opt exps) = Con tra id_opt (MAP mod_to_pres_exp exps))
  /\
  (mod_to_pres_exp (Var_local tra varN) = Var_local tra varN)
  /\
  (mod_to_pres_exp (Var_global tra num) =  Var_global tra num)
  /\
  (mod_to_pres_exp (Fun tra varN exp) =  Fun tra varN (mod_to_pres_exp exp))
  /\
  (mod_to_pres_exp (App tra op exps) =  App tra (Ast op) (MAP mod_to_pres_exp exps))
  /\
  (mod_to_pres_exp (If tra exp1 exp2 exp3) =
    If tra (mod_to_pres_exp exp1) (mod_to_pres_exp exp2) (mod_to_pres_exp exp3))
  /\
  (mod_to_pres_exp (Mat tra exp pes) =
    Mat tra (mod_to_pres_exp exp) (mod_to_pres_pes pes))
  /\
  (mod_to_pres_exp (Let tra varN_opt exp1 exp2) =
    Let tra varN_opt (mod_to_pres_exp exp1) (mod_to_pres_exp exp2))
  /\
  (mod_to_pres_exp (Letrec tra funs exp) =
    Letrec tra
          (MAP (\(v1,v2,e).(v1,v2,mod_to_pres_exp e)) funs)
          (mod_to_pres_exp exp))
  /\
  (* Pattern-expression pairs *)
  (mod_to_pres_pes [] = [])
  /\
  (mod_to_pres_pes ((p,e)::pes) =
    (mod_to_pres_pat p, mod_to_pres_exp e)::mod_to_pres_pes pes)`
  cheat;

val mod_to_pres_dec_def = Define`
  mod_to_pres_dec d =
    case d of
       | modLang$Dlet num exp => presLang$Dlet num (mod_to_pres_exp exp)
       | Dletrec funs => Dletrec (MAP (\(v1,v2,e). (v1,v2,mod_to_pres_exp e)) funs)
       | Dtype mods type_def => Dtype mods type_def
       | Dexn mods conN ts => Dexn mods conN ts`;

val mod_to_pres_prompt_def = Define`
  mod_to_pres_prompt (Prompt modN decs) =
    Prompt modN (MAP mod_to_pres_dec decs)`;

val mod_to_pres_def = Define`
  mod_to_pres prompts = Prog (MAP mod_to_pres_prompt prompts)`;

val mod_to_json_def = Define`
  mod_to_json prog = to_json (mod_to_pres prog)`;


val _ = export_theory();
