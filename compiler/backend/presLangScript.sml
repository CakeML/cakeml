open preamble astTheory jsonTheory backend_commonTheory;
open conLangTheory modLangTheory;

val _ = new_theory"presLang";

(*
* presLang is a presentation language, encompassing many intermediate languages
* of the compiler, adopting their constructors. The purpose of presLang is to be
* an intermediate representation between an intermediate language of the
* compiler and JSON. By translating an intermediate language to presLang, it can
* be given a JSON representation by calling pres_to_json on the presLang
* representation. presLang has no semantics, as it is never evaluated, and may
* therefore mix operators, declarations, patterns and expressions.
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
    | Conlang_con ((num # tid_or_exn) option)`;

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
  (mod_to_pres_exp (Var_global tra num) =  Var_global tra num)
  /\
  (mod_to_pres_exp (Fun tra varN exp) =  Fun tra varN (mod_to_pres_exp exp))
  /\
  (mod_to_pres_exp (App tra op exps) =  App tra (Ast_op op) (MAP mod_to_pres_exp exps))
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

(* Create a new json$Object with keys and values as in the tuples. Every object
* has constructor name field, cons *)
val new_obj_def = Define`
  new_obj cons fields = json$Object (("cons", String cons)::fields)`;

val num_to_json_def = Define`
  num_to_json n = Int (int_of_num n)`;

val trace_to_json_def = Define`
  (trace_to_json (backend_common$Cons tra num) =
    new_obj "Cons" [("num", num_to_json num); ("trace", trace_to_json tra)])
  /\
  (trace_to_json (Union tra1 tra2) =
    new_obj "Union"
      [("trace1", trace_to_json tra1); ("trace2", trace_to_json tra2)])
  /\
  (trace_to_json Empty = Null)
  /\
  (* TODO: cancel entire trace when None, or verify that None will always be at
  * the top level of a trace. *)
  (trace_to_json None = Null)`;

val word_size_to_json_def = Define`
  (word_size_to_json W8 = new_obj "W8" [])
  /\
  (word_size_to_json W64 = new_obj "W64" [])`;

val opn_to_json_def = Define`
  (opn_to_json Plus = new_obj "Plus" [])
  /\
  (opn_to_json Minus = new_obj "Minus" [])
  /\
  (opn_to_json Times = new_obj "Times" [])
  /\
  (opn_to_json Divide = new_obj "Divide" [])
  /\
  (opn_to_json Modulo = new_obj "Modulo" [])`;

val opb_to_json_def = Define`
  (opb_to_json Lt = new_obj "Lt" [])
  /\
  (opb_to_json Gt = new_obj "Gt" [])
  /\
  (opb_to_json Leq = new_obj "Leq" [])
  /\
  (opb_to_json Geq = new_obj "Geq" [])`;

val opw_to_json_def = Define`
  (opw_to_json Andw = new_obj "Andw" [])
  /\
  (opw_to_json Orw = new_obj "Orw" [])
  /\
  (opw_to_json Xor = new_obj "Xor" [])
  /\
  (opw_to_json Add = new_obj "Add" [])
  /\
  (opw_to_json Sub = new_obj "Sub" [])`;

val shift_to_json_def = Define`
  (shift_to_json Lsl = new_obj "Lsl" [])
  /\
  (shift_to_json Lsr = new_obj "Lsr" [])
  /\
  (shift_to_json Asr = new_obj "Asr" [])
  /\
  (shift_to_json Ror = new_obj "Ror" [])`;

val op_to_json_def = Define`
  (op_to_json (Conlang_op (Init_global_var num)) = new_obj "Init_global_var" [("num", num_to_json num)])
  /\
  (op_to_json (Conlang_op (Op astop)) = new_obj "Op" [("op", op_to_json (Ast_op (astop)))])
  /\
  (op_to_json (Ast_op (Opn opn)) = new_obj "Opn" [("opn", opn_to_json opn)])
  /\
  (op_to_json (Ast_op (Opb opb)) = new_obj "Opb" [("opb", opb_to_json opb)])
  /\
  (op_to_json (Ast_op (Opw word_size opw)) = new_obj "Opw" [
    ("word_size", word_size_to_json word_size);
    ("opw", opw_to_json opw)
  ])
  /\
  (op_to_json (Ast_op (Shift word_size shift num)) = new_obj "Shift" [
    ("word_size", word_size_to_json word_size);
    ("shift", shift_to_json shift);
    ("num", num_to_json num)
  ])
  /\
  (op_to_json (Ast_op Equality) = new_obj "Equality" [])
  /\
  (op_to_json (Ast_op Opapp) = new_obj "Opapp" [])
  /\
  (op_to_json (Ast_op Opassign) = new_obj "Opassign" [])
  /\
  (op_to_json (Ast_op Oprep) = new_obj "Oprep" [])
  /\
  (op_to_json (Ast_op Opderep) = new_obj "Opderep" [])
  /\
  (op_to_json (Ast_op Aw8alloc) = new_obj "Aw8alloc" [])
  /\
  (op_to_json (Ast_op Aw8sub) = new_obj "Aw8sub" [])
  /\
  (op_to_json (Ast_op Aw8length) = new_obj "Aw8length" [])
  /\
  (op_to_json (Ast_op Aw8update) = new_obj "Aw8update" [])
  /\
  (op_to_json (Ast_op (WordFromInt word_size)) = new_obj "WordFromInt" [
    ("word_size", word_size_to_json word_size)
  ])
  /\
  (op_to_json (Ast_op (WordToInt word_size)) = new_obj "WordToInt" [
    ("word_size", word_size_to_json word_size)
  ])
  /\
  (op_to_json (Ast_op Ord) = new_obj "Ord" [])
  /\
  (op_to_json (Ast_op Chr) = new_obj "Chr" [])
  /\
  (op_to_json (Ast_op (Chopb opb)) = new_obj "Chopb" [("opb", opb_to_json opb)])
  /\
  (op_to_json (Ast_op Implode) = new_obj "Implode" [])
  /\
  (op_to_json (Ast_op Strsub) = new_obj "Strsub" [])
  /\
  (op_to_json (Ast_op Strlen) = new_obj "Strlen" [])
  /\
  (op_to_json (Ast_op VfromList) = new_obj "VfromList" [])
  /\
  (op_to_json (Ast_op Vsub) = new_obj "Vsub" [])
  /\
  (op_to_json (Ast_op Vlength) = new_obj "Vlength" [])
  /\
  (op_to_json (Ast_op Aalloc) = new_obj "Aalloc" [])
  /\
  (op_to_json (Ast_op Asub) = new_obj "Asub" [])
  /\
  (op_to_json (Ast_op Alength) = new_obj "Alength" [])
  /\
  (op_to_json (Ast_op Aupdate) = new_obj "Aupdate" [])
  /\
  (op_to_json (Ast_op (FFI str)) = new_obj "FFI" [("str", String str)])
  /\
  (op_to_json _ = new_obj "Unknown" [])`;

val lop_to_json_def = Define`
  (lop_to_json ast$And = String "And")
  /\
  (lop_to_json Or = String "Or")
  /\
  (lop_to_json _ = String "Unknown")`

val id_to_list_def = Define`
  id_to_list i = case i of
                      | Long modN i' => modN::id_to_list i'
                      | Short conN => [conN]`;

val id_to_object_def = Define`
    id_to_object ids = Array (MAP String (id_to_list ids))`

val tctor_to_json_def = Define`
  (tctor_to_json (ast$TC_name tuple) =
    let tuple' = id_to_object tuple in
     Object [("TC_name", tuple')])
  /\
  (tctor_to_json TC_int = String "TC_int")
  /\
  (tctor_to_json TC_char = String "TC_char")
  /\
  (tctor_to_json TC_string = String "TC_string")
  /\
  (tctor_to_json TC_ref = String "TC_ref")
  /\
  (tctor_to_json TC_word8 = String "TC_word8")
  /\
  (tctor_to_json TC_word64 = String "TC_word64")
  /\
  (tctor_to_json TC_word8array = String "TC_word8array")
  /\
  (tctor_to_json TC_fn = String "TC_fn")
  /\
  (tctor_to_json TC_tup = String "TC_tup")
  /\
  (tctor_to_json TC_exn = String "TC_exp")
  /\
  (tctor_to_json TC_vector = String "TC_vector")
  /\
  (tctor_to_json TC_array = String "TC_array")`

val t_to_json_def = tDefine"t_to_json"`
  (t_to_json (Tvar tvarN) = String tvarN)
  /\
  (t_to_json (Tvar_db n) = num_to_json n)
  /\
  (t_to_json (Tapp ts tctor) = Object [("Tapp", Array (MAP t_to_json ts));
  ("tctor", tctor_to_json tctor)])`
  cheat;

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

val lit_to_json_def = Define`
  (lit_to_json (IntLit i) = new_obj "IntLit" [("value", Int i)])
  /\
  (lit_to_json (Char c) = new_obj "Char" [("value", String [c])])
  /\
  (lit_to_json (StrLit s) = new_obj "StrLit" [("value", String s)])
  /\
  (lit_to_json (Word8 w) = new_obj "Word8" [("value", String (word_to_hex_string w))])
  /\
  (lit_to_json (Word64 w) = new_obj "Word64" [("value",  String (word_to_hex_string w))])`

val option_to_json_def = Define`
  (option_to_json opt = case opt of
                      | NONE => Null
                      | SOME opt' => String opt')`

(* Takes a presLang$exp and produces json$obj that mimics its structure. *)
val pres_to_json_def = tDefine"pres_to_json"`
  (* Top level *)
  (pres_to_json (presLang$Prog tops) =
    let tops' = Array (MAP pres_to_json tops) in
      new_obj "Prog" [("tops", tops')])
  /\
  (pres_to_json (Prompt modN decs) =
    let decs' = Array (MAP pres_to_json decs) in
    let modN' = option_to_json modN in
      new_obj "Prompt" [("modN", modN'); ("decs", decs')])
  /\
  (pres_to_json (Dlet num exp) =
      new_obj "Dlet" [("num", num_to_json num); ("exp", pres_to_json exp)])
  /\
  (pres_to_json (Dletrec lst) =
    let fields = Array (MAP (\(v1, v2, exp) . Object [("var1", String v1); ("var2", String v2); ("exp", pres_to_json exp)]) lst) in
      new_obj "Dletrec" [("exps", fields)])
  /\
  (pres_to_json (Dtype modNs) =
    let modNs' = Array (MAP String modNs) in
      new_obj "Dtype" [("modNs", modNs')])
  /\
  (pres_to_json (Dexn modNs conN ts) =
    let modNs' = Array (MAP String modNs) in
    let ts' = Array (MAP t_to_json ts) in
      new_obj "Dexn" [("modNs", modNs'); ("con", String conN); ("ts", ts')])
  /\
  (pres_to_json (Pvar varN) =
      new_obj "Pvar" [("varN", String varN)])
  /\
  (pres_to_json (Plit lit) =
      new_obj "Plit" [("lit", lit_to_json lit)])
  /\
  (* TODO: Unify the two conjunctions for Pcon. *)
  (pres_to_json (Pcon (Modlang_con con) exps) =
    let exps' = ("pats", Array (MAP pres_to_json exps)) in
    let ids' = case con of
                  | NONE => ("modscon", Null)
                  | SOME con' => ("modscon", (id_to_object con')) in
      new_obj "Pcon-modLang" [ids'; exps'])
  /\
  (pres_to_json (Pcon (Conlang_con con) exps) =
    let exps' = Array (MAP pres_to_json exps) in
    let tup' = case con of
                  | NONE => Null
                  | SOME (num, te) => case te of
                      | TypeId id => Array [num_to_json num; new_obj "TypeId" [("id", id_to_object id)]]
                      | TypeExn id => Array [num_to_json num; new_obj "TypeExn" [("id", id_to_object id)]]
    in
      new_obj "Pcon-conLang" [("numtid", tup'); ("pats", exps')])
  /\
  (pres_to_json (Pref exp) =
      new_obj "Pref" [("pat", pres_to_json exp)])
  /\
  (pres_to_json (Ptannot exp t) =
      new_obj "Ptannot" [("pat", pres_to_json exp); ("t", t_to_json t)])
  /\
  (pres_to_json (Raise tra exp) =
      new_obj "Raise" [("tra", trace_to_json tra); ("exp", pres_to_json exp)])
  /\
  (pres_to_json (Handle tra exp expsTup) =
    let expsTup' = Array (MAP (\(e1, e2) . Object [
      ("pat", pres_to_json e1);
      ("exp", pres_to_json e2)
    ]) expsTup) in
      new_obj "Handle" [("tra", trace_to_json tra); ("exp", pres_to_json exp); ("exps", expsTup')])
  /\
  (pres_to_json (Var_local tra varN) =
      new_obj "Var_local" [("tra", trace_to_json tra); ("varN", String varN)])
  /\
  (pres_to_json (Var_global tra num) =
      new_obj "Var_global" [("tra", trace_to_json tra); ("num", num_to_json num)])
  /\
  (pres_to_json (Extend_global tra num) =
      new_obj "Extend_global" [("tra", trace_to_json tra); ("num", num_to_json num)])
  /\
  (pres_to_json (Lit tra lit) =
      new_obj "Lit" [("tra", trace_to_json tra); ("lit", lit_to_json lit)])
  /\
  (* TODO: Unify the two conjunctions for Con. *)
  (pres_to_json (Con tra (Modlang_con con) exps) =
    let exps' = ("exps", Array (MAP pres_to_json exps)) in
    let ids' = case con of
                  | NONE => ("modscon", Null)
                  | SOME con' => ("modscon", (id_to_object con')) in
      new_obj "Con-modLang" [("tra", trace_to_json tra); ids'; exps'])
  /\
  (pres_to_json (Con tra (Conlang_con con) exps) =
    let exps' = Array (MAP pres_to_json exps) in
    let tup' = case con of
                  | NONE => Null
                  | SOME (num, te) => case te of
                      | TypeId id => Array [num_to_json num; new_obj "TypeId" [("id", id_to_object id)]]
                      | TypeExn id => Array [num_to_json num; new_obj "TypeExn" [("id", id_to_object id)]] in
      new_obj "Con-conLang" [("tra", trace_to_json tra); ("numtid", tup'); ("pats", exps')])
  /\
  (pres_to_json (App tra op exps) =
    let exps' = ("exps", Array (MAP pres_to_json exps)) in
      new_obj "App" [("tra", trace_to_json tra); ("op", op_to_json op); exps'])
  /\
  (pres_to_json (Fun tra varN exp) =
      new_obj "Fun" [("tra", trace_to_json tra); ("varN", String varN); ("exp", pres_to_json exp)])
  /\
  (pres_to_json (Log tra lop exp1 exp2) =
      new_obj "Log" [("tra", trace_to_json tra); ("lop", lop_to_json lop); ("exp1", pres_to_json exp1); ("exp2", pres_to_json exp2)])
  /\
  (pres_to_json (If tra exp1 exp2 exp3) =
      new_obj "If" [("tra", trace_to_json tra); ("exp1", pres_to_json exp1); ("exp2", pres_to_json exp2); ("exp3", pres_to_json exp3)])
  /\
  (pres_to_json (Mat tra exp expsTup) =
    let expsTup' = Array (MAP (\(e1, e2) . Object [("pat", pres_to_json e1); ("exp", pres_to_json e2)]) expsTup) in
      new_obj "Mat" [("tra", trace_to_json tra); ("exp", pres_to_json exp); ("exps", expsTup')])
  /\
  (pres_to_json (Let tra varN exp1 exp2) =
    let varN' = option_to_json varN in
      new_obj "Let" [("tra", trace_to_json tra); ("varN", varN'); ("exp1", pres_to_json exp1); ("exp2", pres_to_json exp2)])
  /\
  (pres_to_json (Letrec tra varexpTup exp) =
    let varexpTup' = Array (MAP (\(v1, v2, e) . Object [
      ("var1", String v1);
      ("var2", String v2);
      ("exp", pres_to_json e)
    ]) varexpTup) in
      new_obj "Letrec" [("tra", trace_to_json tra); ("varsexp", varexpTup'); ("exp", pres_to_json exp)])
  /\
  (pres_to_json _ = Null)`
  cheat;

(* Function to construct general functions from a language to JSON. Call with
* the name of the language and what fucntion to use to convert it to preslang to
* obtain a function which takes a program in an intermediate language and
* returns a JSON representation of that program. *)
val lang_to_json_def = Define`
  lang_to_json langN func = \ p . Object [("lang", String langN); ("prog", pres_to_json (func p))]`;

val mod_to_json_def = Define`
  mod_to_json = lang_to_json "modLang" mod_to_pres`;

val con_to_json_def = Define`
  con_to_json = lang_to_json "conLang" con_to_pres`;

(* decLang uses the same structure as conLang, but the compilation step from con
* to dec returns an expression rather than a prompt. *)
val dec_to_json_def = Define`
  dec_to_json = lang_to_json "decLang" con_to_pres_exp`;

val _ = export_theory();
