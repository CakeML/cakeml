(*
  Parser for Scheme
*)
Theory scheme_parsing
Ancestors
  mlstring scheme_values scheme_ast
Libs
  preamble

val _ = monadsyntax.declare_monad("sum", {
  unit = “INR”,
  bind = “λ s f . case s of
    | INL l => INL l
    | INR r => f r”,
  ignorebind = NONE,
  fail = NONE,
  guard = NONE,
  choice = SOME “λ x y . case x of
    | INL l => y
    | INR r => INR r”
});

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "sum";

Definition mapM_def:
  mapM f [] = return [] ∧
  mapM f (x::xs) = do
      e <- f x;
      es <- mapM f xs;
      return (e::es)
    od
End

(* lexing *)

Datatype:
  token = OPEN | CLOSE | DOT | NUM num | QUOTE num
    | PLUS | MINUS | TIMES | BOOL bool | WORD string
End

Definition delimits_next_def:
  delimits_next [] = T ∧
  delimits_next (c::cs) = MEM c " \t\n()#;"
End

Definition read_bool_def:
  read_bool (#"#"::c::cs) = (
    if delimits_next cs then
      if MEM c "tT" then SOME (T, cs) else
      if MEM c "fF" then SOME (F, cs) else
        NONE
    else NONE) ∧
  read_bool _ = NONE
End

Theorem read_bool_length:
  ∀ b c cs ys .
    read_bool (c::cs) = SOME (b,ys) ⇒
    LENGTH ys ≤ LENGTH cs
Proof
  Cases_on ‘cs’ >> rw [read_bool_def, delimits_next_def]
QED

Definition read_num_def:
  read_num l h f x acc (c::cs) =
    if ORD l ≤ ORD c ∧ ORD c ≤ ORD h then
      let newacc = (f * acc + (ORD c - x)) in
        if delimits_next cs then SOME (newacc, cs) else
          read_num l h f x newacc cs
    else NONE
End

Theorem read_num_length:
  ∀l h c cs n ys f acc x.
    read_num l h f x acc (c::cs) = SOME (n,ys) ⇒
    LENGTH ys ≤ LENGTH cs
Proof
  Induct_on ‘cs’ >> rw [Once read_num_def, delimits_next_def] >> rw[]
  >> last_assum $ drule >> rw[]
QED

Definition read_word_def:
  read_word (c::cs) = if delimits_next cs then SOME ([c], cs) else
    case read_word cs of
    | NONE => NONE
    | SOME (ws, cs') => SOME (c::ws, cs')
End

Theorem read_word_length:
  ∀ w c cs ys .
    read_word (c::cs) = SOME (w,ys) ⇒
    LENGTH ys ≤ LENGTH cs
Proof
  Induct_on ‘cs’ >> rw [Once read_word_def, delimits_next_def] >> gvs[]
  >> Cases_on ‘read_word (STRING h cs)’ >> gvs[]
  >> PairCases_on ‘x’ >> gvs[]
  >> last_assum $ drule >> rw[]
QED

Definition end_line_def:
  end_line [] = [] ∧
  end_line (c::cs) = if c = #"\n" then cs else end_line cs
End

Theorem end_line_length:
  ∀cs. STRLEN (end_line cs) < SUC (STRLEN cs)
Proof
  Induct \\ rw [end_line_def]
QED

Definition lex_def:
  lex [] acc = INR acc ∧
  lex (c::cs) acc =
      if MEM c " \t\n" then lex cs acc else
      if c = #";" then lex (end_line cs) acc else
      if c = #"." then lex cs (DOT::acc) else
      if c = #"(" then lex cs (OPEN::acc) else
      if c = #")" then lex cs (CLOSE::acc) else
      if c = #"+" then lex cs (PLUS::acc) else
      if c = #"-" then lex cs (MINUS::acc) else
      if c = #"*" then lex cs (TIMES::acc) else
      (*if c = #"'" then lex QUOTE cs acc else*)
        case read_bool (c::cs) of
        | SOME (b, rest) => lex rest (BOOL b::acc)
        | NONE => case read_num #"0" #"9" 10 (ORD #"0") 0 (c::cs) of
          | SOME (n, rest) => lex rest (NUM n::acc)
          | NONE => case read_word (c::cs) of
            | SOME (w, rest) => lex rest (WORD w::acc)
            | NONE => INL ("Failed to parse at character " ++ [c])
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw []
  >- (dxrule read_bool_length >> rw[])
  >- (dxrule read_word_length >> rw[])
  >- (dxrule read_num_length >> rw[])
  >> simp [end_line_length]
End

Definition lexer_def:
  lexer input = lex input []
End


(* parsing *)

(*Definition quote_def:
  quote n = list [Num (name "'"); Num n]
End*)

Definition parse_def:
  parse [] x [] = INR x ∧
  parse [] x s = INL "Too many close brackets" ∧
  parse (CLOSE :: rest) x s = parse rest Nil (x::s) ∧
  parse (OPEN :: rest) x s =
    (case s of [] => INL "Too many open brackets"
     | (y::ys) => parse rest (Pair x y) ys) ∧
  parse (NUM n :: rest) x s = parse rest (Pair (Num &n) x) s ∧
  parse (BOOL b :: rest) x s = parse rest (Pair (Bool b) x) s ∧
  parse (WORD w :: rest) x s = parse rest (Pair (Word w) x) s ∧
  parse (PLUS :: rest) x s = parse rest (Pair (Word "+") x) s ∧
  parse (MINUS :: rest) x s = parse rest (Pair (Word "-") x) s ∧
  parse (TIMES :: rest) x s = parse rest (Pair (Word "*") x) s ∧
  (*parse (QUOTE n :: rest) x s = parse rest (Pair (quote n) x) s ∧*)
  parse (DOT :: rest) x s = parse rest (head x) s
End

(*
EVAL “case lexer "(print hi)" of
| INL x => INL x
| INR y => case parse y Nil [] of
  | INL x => INL x
  | INR y => INR (head y)”
*)


(* conversion to AST *)

Definition pair_to_list_def:
  pair_to_list Nil = SOME [] ∧
  pair_to_list (Pair x y) = (case pair_to_list y of
  | NONE => NONE
  | SOME xs => SOME (x::xs)) ∧
  pair_to_list v = NONE
End

Theorem pair_to_list_size:
  ∀ p ls . pair_to_list p = SOME ls ⇒ v_size p = list_size v_size ls
Proof
  ho_match_mp_tac pair_to_list_ind
  >> simp[pair_to_list_def, list_size_def]
  >> rpt strip_tac
  >> Cases_on ‘pair_to_list p’ >> gvs[list_size_def]
QED

Theorem list_size_snoc[simp]:
  ∀ f x xs .
    list_size f (SNOC x xs) = 1 + (f x + list_size f xs)
Proof
  Induct_on ‘xs’
  >> simp[list_size_def]
QED

Definition cons_formals_def:
  cons_formals ps Nil = INR (REVERSE ps, NONE) ∧
  cons_formals ps (Word w) = INR (REVERSE ps, SOME (implode w)) ∧
  cons_formals ps (Pair (Word x) y) = cons_formals (implode x::ps) y ∧
  cons_formals ps _ = INL "Invalid lambda formals"
End

Definition cons_ast_def:
  cons_ast (Num n) = INR (Lit (LitNum n)) ∧
  cons_ast (Bool b) = INR (Lit (LitBool b)) ∧
  cons_ast (Word w) = (
    if w = "+" then INR (Lit (LitPrim SAdd)) else
    if w = "-" then INR (Lit (LitPrim SMinus)) else
    if w = "*" then INR (Lit (LitPrim SMul)) else
    if w = "eqv?" then INR (Lit (LitPrim SEqv)) else
    if w = "call/cc" then INR (Lit (LitPrim CallCC)) else
    if w = "cons" then INR (Lit (LitPrim Cons)) else
    if w = "car" then INR (Lit (LitPrim Car)) else
    if w = "cdr" then INR (Lit (LitPrim Cdr)) else
    if w = "null?" then INR (Lit (LitPrim IsNull)) else
    if w = "pair?" then INR (Lit (LitPrim IsPair)) else
      INR (Ident (implode w))) ∧
  cons_ast Nil = INL "Empty S expression" ∧
  cons_ast (Pair x y) = (case pair_to_list y of
  | NONE => INL "Invalid S expression"
  | SOME ys => (case x of
    | Word "if" => (case ys of
      | [c;t;f] => do
          ce <- cons_ast c;
          te <- cons_ast t;
          fe <- cons_ast f;
          return (Cond ce te fe)
        od
      | _ => INL "Wrong number of expressions in if statement")
    | Word "begin" => (if NULL ys
        then INL "Wrong number of expressions to begin"
        else do
          es <- cons_ast_list (FRONT ys);
          e <- cons_ast (LAST ys);
          return (Begin es e)
        od)
    | Word "lambda" => (case ys of
      | [xs;y'] => do
          (ps,lp) <- cons_formals [] xs;
          e <- cons_ast y';
          return (Lambda ps lp e)
        od
      | _ => INL "Wrong number of expressions in lambda statement")
    | Word "letrec" => (case ys of
      | [xs;y'] => (case pair_to_list xs of
        | NONE => INL "Invalid S expression"
        | SOME xs' => do
            bs <- cons_ast_bindings xs';
            e <- cons_ast y';
            return (Letrec bs e)
          od)
      | _ => INL "Wrong number of expressions in letrec statement")
    | Word "letrec*" => (case ys of
      | [xs;y'] => (case pair_to_list xs of
        | NONE => INL "Invalid S expression"
        | SOME xs' => do
            bs <- cons_ast_bindings xs';
            e <- cons_ast y';
            return (Letrecstar bs e)
          od)
      | _ => INL "Wrong number of expressions in letrec statement")
    | Word "set!" => (case ys of
      | [Word w;y'] => do
          e <- cons_ast y';
          return (Set (implode w) e)
        od
      | _ => INL "Invalid set expression")
    | fn => do
        e <- cons_ast fn;
        es <- cons_ast_list ys;
        return (Apply e es)
      od)) ∧

  cons_ast_list [] = INR [] ∧
  cons_ast_list (x::xs) = (do
      e <- cons_ast x;
      es <- cons_ast_list xs;
      return (e::es)
    od) ∧

  cons_ast_bindings [] = INR [] ∧
  cons_ast_bindings (x::xs) = (case pair_to_list x of
  | NONE => INL "Invalid S expression"
  | SOME ys => (case ys of
    | [Word w;b] => do
        e <- cons_ast b;
        es <- cons_ast_bindings xs;
        return ((implode w, e)::es)
      od
    | _ => INL "Invalid letrec binding"))
Termination
  WF_REL_TAC ‘measure $ λ x . case x of
    | INL v => v_size v
    | INR (INL vs) => list_size v_size vs
    | INR (INR vs') => list_size v_size vs'’
  >> rpt strip_tac
  >> rpt (
    dxrule_then (assume_tac o GSYM) pair_to_list_size
    >> gvs[list_size_def]
  )
  >> Cases_on ‘ys’ using SNOC_CASES
  >> gvs[]
End

Definition static_scope_check_def:
  static_scope_check p = if static_scope ∅ p
    then INR p
    else INL "Not statically scoped or duplicate parameter in lambda or letrec"
End

Definition parse_to_ast_def:
  parse_to_ast s = do
      lxs <- lexer s;
      e <- parse lxs Nil [];
      p <- cons_ast (head e);
      static_scope_check p
    od
End

(*
EVAL “cons_ast (Pair (Word "print") (Pair (Word "hi") Nil))”
EVAL “do e <- do es' <- mapM cons_ast [Word "t"; Word "h"]; return (Apply (Val (SNum 0)) es') od; es <- mapM cons_ast [Pair (Word "+") Nil; Word "-"]; return (Apply e es) od”
EVAL “parse_to_ast "((if #t + * ) 2 3)"”
EVAL “parse_to_ast "(lambda (x y . l) 2)"”
EVAL “parse_to_ast "(letrec ((x 3) (y x)) 2)"”
EVAL “parse_to_ast "(cons 3 2)"”
*)

