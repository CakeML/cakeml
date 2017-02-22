open preamble astTheory jsonTheory;

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

val _ = Datatype`
  exp =
    (* An entire program. Is divided into any number of top level declarations. *)
    | Prog (exp(*top*) list)
    (* Top level declarations. May contain module, and spec. The exp is always a declaration. *)
    | Tdec exp(*dec*)
    | Tmod modN (specs option) (exp(*dec*) list)
    (* Declarations *)
    | Dlet exp(*pat*) exp(*exp*)
    | Dletrec ((varN # varN # exp(*exp*)) list)
    | Dtype type_def
    | Dtabbrev (tvarN list) typeN t
    | Dexn conN (t list)
    (* Patterns *)
    | Pvar varN
    | Plit lit
    | Pcon (((modN, conN) id) option) (exp(*pat*) list)
    | Pref exp(*pat*)
    | Ptannot exp(*pat*) t
    (* Expressions *)
    | Raise exp
    | Handle exp ((exp(*pat*) # exp) list)
    | Var ((modN, varN) id)
    | Lit lit
      (* Constructor application.
       A Nothing constructor indicates a tuple pattern. *)
    | Con (((modN, conN) id) option) (exp list)
      (* Application of a primitive operator to arguments.
       Includes function application. *)
    | App op (exp list)
    | Fun varN exp
      (* Logical operations (and, or) *)
    | Log lop exp exp
    | If exp exp exp
      (* Pattern matching *)
    | Mat exp ((exp(*pat*) # exp) list)
      (* A let expression
         A Nothing value for the binding indicates that this is a
         sequencing expression, that is: (e1; e2). *)
    | Let (varN option) exp exp
      (* Local definition of (potentially) mutually recursive
         functions.
         The first varN is the function's name, and the second varN
         is its parameter. *)
    | Letrec ((varN # varN # exp) list) exp
    | Tannot exp t
      (* Location annotated expressions, not expected in source programs *)
    | Lannot exp locn`;

(* TODO: Implement to_json based on presLang structure. *)
val to_json_def = tDefine "to_json"`
  to_json _ = json$Null`
  cheat;

val _ = export_theory();
