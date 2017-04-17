open preamble astTheory;
open conLangTheory modLangTheory exhLangTheory structuredLangTheory;

val _ = new_theory"presLang";

(*
* presLang is a presentation language, encompassing many intermediate languages
* of the compiler, adopting their constructors. The purpose of presLang is to be
* an intermediate representation between an intermediate language of the
* compiler and the structured language. By translating an intermediate language
* to presLang, it can be given a structured representation by calling
* pres_to_strucutred on the presLang representation. presLang has no semantics,
* as it is never evaluated, and may therefore mix operators, declarations,
* patterns and expressions.
*)

(* Special operator wrapper for presLang *)
val _ = Datatype`
  op =
    | Ast_op ast$op
    | Conlang_op conLang$op`;

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
    (* Declarations *)
    | Dlet num exp(*exp*)
    | Dletrec ((varN # varN # exp(*exp*)) list)
    | Dtype (modN list)
    | Dexn (modN list) conN (t list)
    (* Patterns *)
    | Pvar varN
    | Plit lit
    | Pcon conF (exp(*pat*) list)
    | Pref exp(*pat*)
    | Ptannot exp(*pat*) t
    (* Expressions *)
    | Raise tra exp
    | Handle tra exp ((exp(*pat*) # exp) list)
    | Var_local tra varN
    | Var_global tra num
    | Extend_global tra num (* Introduced in conLang *)
    | Lit tra lit
    | Con tra conF (exp list)
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

(* Functions for converting intermediate languages to presLang. *)

(* modLang *)

val mod_to_pres_pat_def = tDefine "mod_to_pres_pat"`
  mod_to_pres_pat p =
    case p of
       | ast$Pvar varN => presLang$Pvar varN
       | Plit lit => Plit lit
       | Pcon id pats => Pcon (Modlang_con id) (MAP mod_to_pres_pat pats)
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
  (mod_to_pres_exp (Con tra id_opt exps) = Con tra (Modlang_con id_opt) (MAP mod_to_pres_exp exps))
  /\
  (mod_to_pres_exp (Var_local tra varN) = Var_local tra varN)
  /\
  (mod_to_pres_exp (Var_global tra num) = Var_global tra num)
  /\
  (mod_to_pres_exp (Fun tra varN exp) = Fun tra varN (mod_to_pres_exp exp))
  /\
  (mod_to_pres_exp (App tra op exps) = App tra (Ast_op op) (MAP mod_to_pres_exp exps))
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
       | Dtype mods type_def => Dtype mods
       | Dexn mods conN ts => Dexn mods conN ts`;

val mod_to_pres_prompt_def = Define`
  mod_to_pres_prompt (Prompt modN decs) =
    Prompt modN (MAP mod_to_pres_dec decs)`;

val mod_to_pres_def = Define`
  mod_to_pres prompts = Prog (MAP mod_to_pres_prompt prompts)`;

(* con_to_pres *)
val con_to_pres_pat_def = tDefine"con_to_pres_pat"`
  con_to_pres_pat p =
    case p of
       | conLang$Pvar varN => presLang$Pvar varN
       | Plit lit => Plit lit
       | Pcon opt ps => Pcon (Conlang_con opt) (MAP con_to_pres_pat ps)
       | Pref pat => Pref (con_to_pres_pat pat)`
    cheat;

val con_to_pres_exp_def = tDefine"con_to_pres_exp"`
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
  cheat;

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
val exh_to_pres_pat_def = tDefine"exh_to_pres_pat"`
  exh_to_pres_pat p =
    case p of
       | exhLang$Pvar varN => presLang$Pvar varN
       | Plit lit => Plit lit
       | Pcon num ps => Pcon (Exhlang_con num) (MAP exh_to_pres_pat ps)
       | Pref pat => Pref (exh_to_pres_pat pat)`
    cheat;

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
  cheat;

(* Helpers for converting pres to structured. *)
val empty_item_def = Define`
  empty_item name = Item NONE name []`;

val string_to_structured_def = Define`
  string_to_structured s = empty_item ("\"" ++ s ++ "\"")`;

val num_to_structured_def = Define`
  num_to_structured n = empty_item (num_to_str n)`;

val word_size_to_structured_def = Define`
  (word_size_to_structured W8 = empty_item "W8")
  /\
  (word_size_to_structured W64 = empty_item "W64")`;

val opn_to_structured_def = Define`
  (opn_to_structured Plus = empty_item "Plus")
  /\
  (opn_to_structured Minus = empty_item "Minus")
  /\
  (opn_to_structured Times = empty_item "Times")
  /\
  (opn_to_structured Divide = empty_item "Divide")
  /\
  (opn_to_structured Modulo = empty_item "Modulo")`;

val opb_to_structured_def = Define`
  (opb_to_structured Lt = empty_item "Lt")
  /\
  (opb_to_structured Gt = empty_item "Gt")
  /\
  (opb_to_structured Leq = empty_item "Leq")
  /\
  (opb_to_structured Geq = empty_item "Geq")`;

val opw_to_structured_def = Define`
  (opw_to_structured Andw = empty_item "Andw")
  /\
  (opw_to_structured Orw = empty_item "Orw")
  /\
  (opw_to_structured Xor = empty_item "Xor")
  /\
  (opw_to_structured Add = empty_item "Add")
  /\
  (opw_to_structured Sub = empty_item "Sub")`;

val shift_to_structured_def = Define`
  (shift_to_structured Lsl = empty_item "Lsl")
  /\
  (shift_to_structured Lsr = empty_item "Lsr")
  /\
  (shift_to_structured Asr = empty_item "Asr")
  /\
  (shift_to_structured Ror = empty_item "Ror")`;

val op_to_structured_def = Define`
  (op_to_structured (Conlang_op (Init_global_var num)) = Item NONE "Init_global_var" [num_to_structured num])
  /\
  (op_to_structured (Conlang_op (Op astop)) = Item NONE "Op" [op_to_structured (Ast_op (astop))])
  /\
  (op_to_structured (Ast_op (Opn opn)) = Item NONE "Opn" [opn_to_structured opn])
  /\
  (op_to_structured (Ast_op (Opb opb)) = Item NONE "Opb" [opb_to_structured opb])
  /\
  (op_to_structured (Ast_op (Opw word_size opw)) = Item NONE "Opw" [
    word_size_to_structured word_size;
    opw_to_structured opw
  ])
  /\
  (op_to_structured (Ast_op (Shift word_size shift num)) = Item NONE "Shift" [
    word_size_to_structured word_size;
    shift_to_structured shift;
    num_to_structured num
  ])
  /\
  (op_to_structured (Ast_op Equality) = empty_item "Equality")
  /\
  (op_to_structured (Ast_op Opapp) = empty_item "Opapp")
  /\
  (op_to_structured (Ast_op Opassign) = empty_item "Opassign")
  /\
  (op_to_structured (Ast_op Oprep) = empty_item "Oprep")
  /\
  (op_to_structured (Ast_op Opderep) = empty_item "Opderep")
  /\
  (op_to_structured (Ast_op Aw8alloc) = empty_item "Aw8alloc")
  /\
  (op_to_structured (Ast_op Aw8sub) = empty_item "Aw8sub")
  /\
  (op_to_structured (Ast_op Aw8length) = empty_item "Aw8length")
  /\
  (op_to_structured (Ast_op Aw8update) = empty_item "Aw8update")
  /\
  (op_to_structured (Ast_op (WordFromInt word_size)) =
    Item NONE "WordFromInt" [word_size_to_structured word_size])
  /\
  (op_to_structured (Ast_op (WordToInt word_size)) =
    Item NONE "WordToInt" [word_size_to_structured word_size])
  /\
  (op_to_structured (Ast_op Ord) = empty_item "Ord")
  /\
  (op_to_structured (Ast_op Chr) = empty_item "Chr")
  /\
  (op_to_structured (Ast_op (Chopb opb)) =
    Item NONE "Chopb" [opb_to_structured opb])
  /\
  (op_to_structured (Ast_op Implode) = empty_item "Implode")
  /\
  (op_to_structured (Ast_op Strsub) = empty_item "Strsub")
  /\
  (op_to_structured (Ast_op Strlen) = empty_item "Strlen")
  /\
  (op_to_structured (Ast_op VfromList) = empty_item "VfromList")
  /\
  (op_to_structured (Ast_op Vsub) = empty_item "Vsub")
  /\
  (op_to_structured (Ast_op Vlength) = empty_item "Vlength")
  /\
  (op_to_structured (Ast_op Aalloc) = empty_item "Aalloc")
  /\
  (op_to_structured (Ast_op Asub) = empty_item "Asub")
  /\
  (op_to_structured (Ast_op Alength) = empty_item "Alength")
  /\
  (op_to_structured (Ast_op Aupdate) = empty_item "Aupdate")
  /\
  (op_to_structured (Ast_op (FFI str)) =
    Item NONE "FFI" [string_to_structured str])`;

val lop_to_structured_def = Define`
  (lop_to_structured ast$And = empty_item "And")
  /\
  (lop_to_structured Or = empty_item "Or")
  /\
  (lop_to_structured _ = empty_item "Unknown")`;

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

val lit_to_structured_def = Define`
  (lit_to_structured (IntLit i) =
    Item NONE "IntLit" [empty_item (int_to_str i)])
  /\
  (lit_to_structured (Char c) =
    Item NONE "Char" ["#\"" ++ [c] ++ "\""])
  /\
  (lit_to_structured (StrLit s) =
    Item NONE "StrLit" [string_to_structured s])
  /\
  (lit_to_structured (Word8 w) =
    Item NONE "Word8" [empty_item (word_to_hex_string w)])
  /\
  (lit_to_structured (Word64 w) =
    Item NONE "Word64" [empty_item (word_to_hex_string w)])`;

val option_string_to_structured_def = Define`
  (option_string_to_structured opt = case opt of
                      | NONE => empty_item "NONE"
                      | SOME opt' => Item NONE "SOME" [string_to_structured opt'])`

val id_to_structured_def = Define`
  (id_to_structured (Long name i) = Item NONE "Long" [id_to_structured i; string_to_structured name])
  /\
  (id_to_structured (Short name) = Item NONE "Short" [string_to_structured name])`;

val tctor_to_structured_def = Define`
  (tctor_to_structured (ast$TC_name ids) =
    let ids' = id_to_structured ids in
      Item NONE "TC_name" [ids'])
  /\
  (tctor_to_structured TC_int = empty_item "TC_int")
  /\
  (tctor_to_structured TC_char = empty_item "TC_char")
  /\
  (tctor_to_structured TC_string = empty_item "TC_string")
  /\
  (tctor_to_structured TC_ref = empty_item "TC_ref")
  /\
  (tctor_to_structured TC_word8 = empty_item "TC_word8")
  /\
  (tctor_to_structured TC_word64 = empty_item "TC_word64")
  /\
  (tctor_to_structured TC_word8array = empty_item "TC_word8array")
  /\
  (tctor_to_structured TC_fn = empty_item "TC_fn")
  /\
  (tctor_to_structured TC_tup = empty_item "TC_tup")
  /\
  (tctor_to_structured TC_exn = empty_item "TC_exp")
  /\
  (tctor_to_structured TC_vector = empty_item "TC_vector")
  /\
  (tctor_to_structured TC_array = empty_item "TC_array")`

val t_to_structured_def = tDefine"t_to_json"`
  (t_to_structured (Tvar tvarN) = Item NONE "Tvar" [string_to_structured tvarN])
  /\
  (t_to_structured (Tvar_db n) = Item NONE "Tvar_db" [num_to_structured n])
  /\
  (t_to_structured (Tapp ts tctor) = Item NONE "Tapp" [List (MAP t_to_structured ts); tctor_to_structured tctor])`
  cheat;

val tid_or_exn_to_structured_def = Define`
  tid_or_exn_to_structured te =
   let (name, id) =
     case te of
       | TypeId id => ("TypeId", id)
       | TypeExn id => ("TypeExn", id) in
     Item NONE name [id_to_structured id]`;

val conf_to_structured_def = Define`
  conf_to_structured con =
    let none = empty_item "NONE" in
      case con of
         | Modlang_con NONE => none
         | Conlang_con NONE => none
         | Modlang_con (SOME id) => Item NONE "SOME" [id_to_structured id]
         | Conlang_con (SOME (n,t)) =>
            Item NONE "SOME" [Tuple [num_to_structured n; tid_or_exn_to_structured t]]
         | Exhlang_con c => Item NONE "SOME" [num_to_structured c]`;

(* Takes a presLang$exp and produces json$obj that mimics its structure. *)
val pres_to_structured_def = tDefine"pres_to_structured"`
  (* Top level *)
  (pres_to_structured (presLang$Prog tops) =
    let tops' = List (MAP pres_to_structured tops) in
      Item NONE "Prog" [tops'])
  /\
  (pres_to_structured (Prompt modN decs) =
    let decs' = List (MAP pres_to_structured decs) in
    let modN' = option_string_to_structured modN in
      Item NONE "Prompt" [modN'; decs'])
  /\
  (pres_to_structured (Dlet num exp) =
      Item NONE "Dlet" [num_to_structured num; pres_to_structured exp])
  /\
  (pres_to_structured (Dletrec lst) =
    let fields =
      List (MAP (\ (v1, v2, exp) . Tuple [string_to_structured v1; string_to_structured v2; pres_to_structured exp]) lst) in
      Item NONE "Dletrec" [fields] )
  /\
  (pres_to_structured (Dtype modNs) =
    let modNs' = List (MAP string_to_structured modNs) in
      Item NONE "Dtype" [modNs'])
  /\
  (pres_to_structured (Dexn modNs conN ts) =
    let modNs' = List (MAP string_to_structured modNs) in
    let ts' = List (MAP t_to_structured ts) in
      Item NONE "Dexn" [modNs'; string_to_structured conN; ts'])
  /\
  (pres_to_structured (Pvar varN) =
      Item NONE "Pvar" [string_to_structured varN])
  /\
  (pres_to_structured (Plit lit) =
      Item NONE "Plit" [lit_to_structured lit])
  /\
  (pres_to_structured (Pcon conF exps) =
    let exps' = List (MAP pres_to_structured exps) in
      Item NONE "Pcon" [conf_to_structured conF; exps'])
  /\
  (pres_to_structured (Pref exp) =
      Item NONE "Pref" [pres_to_structured exp])
  /\
  (pres_to_structured (Ptannot exp t) =
      Item NONE "Ptannot" [pres_to_structured exp; t_to_structured t])
  /\
  (pres_to_structured (Raise tra exp) =
      Item (SOME tra) "Raise" [pres_to_structured exp])
  /\
  (pres_to_structured (Handle tra exp expsTup) =
    let expsTup' = List (MAP (\(e1, e2) . Tuple [pres_to_structured e1; pres_to_structured e2]) expsTup) in
      Item (SOME tra) "Handle" [pres_to_structured exp; expsTup'])
  /\
  (pres_to_structured (Var_local tra varN) =
      Item (SOME tra) "Var_local" [string_to_structured varN])
  /\
  (pres_to_structured (Var_global tra num) =
      Item (SOME tra) "Var_global" [num_to_structured num])
  /\
  (pres_to_structured (Extend_global tra num) =
      Item (SOME tra) "Extend_global" [num_to_structured num])
  /\
  (pres_to_structured (Lit tra lit) =
      Item (SOME tra) "Lit" [lit_to_structured lit])
  /\
  (pres_to_structured (Con tra conF exps) =
    let exps' = List (MAP pres_to_structured exps) in
      Item (SOME tra) "Pcon" [conf_to_structured conF; exps'])
  /\
  (pres_to_structured (App tra op exps) =
    let exps' = List (MAP pres_to_structured exps) in
      Item (SOME tra) "App" [op_to_structured op; exps'])
  /\
  (pres_to_structured (Fun tra varN exp) =
      Item (SOME tra) "Fun" [string_to_structured varN; pres_to_structured exp])
  /\
  (pres_to_structured (Log tra lop exp1 exp2) =
      Item (SOME tra) "Log" [lop_to_structured lop; pres_to_structured exp1; pres_to_structured exp2])
  /\
  (pres_to_structured (If tra exp1 exp2 exp3) =
      Item (SOME tra) "If" [pres_to_structured exp1; pres_to_structured exp2; pres_to_structured exp3])
  /\
  (pres_to_structured (Mat tra exp expsTup) =
    let expsTup' = List (MAP (\(e1, e2) . Tuple [pres_to_structured e1; pres_to_structured e2]) expsTup) in
      Item (SOME tra) "Mat" [pres_to_structured exp; expsTup'])
  /\
  (pres_to_structured (Let tra varN exp1 exp2) =
    let varN' = option_string_to_structured varN in
      Item (SOME tra) "Let" [varN'; pres_to_structured exp1; pres_to_structured exp2])
  /\
  (pres_to_structured (Letrec tra varexpTup exp) =
    let varexpTup' = List (MAP (\ (v1, v2, e) . Tuple [
      string_to_structured v1;
      string_to_structured v2;
      pres_to_structured e
    ]) varexpTup) in
      Item (SOME tra) "Letrec" [varexpTup'; pres_to_structured exp])
  `cheat;

(* Function to construct general functions from a language to JSON. Call with
* the name of the language and what fucntion to use to convert it to preslang to
* obtain a function which takes a program in an intermediate language and
* returns a JSON representation of that program. *)
val lang_to_json_def = Define`
  lang_to_json langN func =
    \ p . Object [
      ("lang", String langN);
      ("prog", structured_to_json (pres_to_structured (func p)))]`;

val mod_to_json_def = Define`
  mod_to_json = lang_to_json "modLang" mod_to_pres`;

val con_to_json_def = Define`
  con_to_json = lang_to_json "conLang" con_to_pres`;

(* decLang uses the same structure as conLang, but the compilation step from con
* to dec returns an expression rather than a prompt. *)
val dec_to_json_def = Define`
  dec_to_json = lang_to_json "decLang" con_to_pres_exp`;

val exh_to_json_def = Define`
  exh_to_json = lang_to_json "exhLang" exh_to_pres_exp`;

val _ = export_theory();
