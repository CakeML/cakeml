(*
  Parsing of Lisp s-expressions
*)
Theory lisp_parsing
Ancestors
  arithmetic list pair finite_map string lisp_values
Libs
  term_tactic

(* lexing *)

Datatype:
  token = OPEN | CLOSE | DOT | NUM num | QUOTE num
End

Definition read_num_def:
  read_num l h f x acc [] = (acc,[]) ∧
  read_num l h f x acc (c::cs) =
    if ORD l ≤ ORD c ∧ ORD c ≤ ORD h then
      read_num l h f x (f * acc + (ORD c - x)) cs
    else (acc,c::cs)
End

Theorem read_num_length:
  ∀l h xs n ys f acc x.
    read_num l h f x acc xs = (n,ys) ⇒
    LENGTH ys ≤ LENGTH xs ∧ (xs ≠ ys ⇒ LENGTH ys < LENGTH xs)
Proof
  Induct_on ‘xs’ \\ rw [read_num_def]
  \\ TRY pairarg_tac \\ fs [] \\ rw [] \\ res_tac \\ fs []
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
  lex q [] acc = acc ∧
  lex q (c::cs) acc =
      if MEM c " \t\n" then lex NUM cs acc else
      if c = #"#" then lex NUM (end_line cs) acc else
      if c = #"." then lex NUM cs (DOT::acc) else
      if c = #"(" then lex NUM cs (OPEN::acc) else
      if c = #")" then lex NUM cs (CLOSE::acc) else
      if c = #"'" then lex QUOTE cs acc else
        let (n,rest) = read_num #"0" #"9" 10 (ORD #"0") 0 (c::cs) in
          if rest ≠ c::cs then lex NUM rest (q n::acc) else
            let (n,rest) = read_num #"*" #"z" 256 0 0 (c::cs) in
              if rest ≠ c::cs then lex NUM rest (q n::acc) else
                lex NUM cs acc
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’ \\ rw []
  \\ imp_res_tac (GSYM read_num_length) \\ fs [end_line_length]
End

Definition lexer_def:
  lexer input = lex NUM input []
End


(* parsing *)

Definition quote_def:
  quote n = list [Num (name "'"); Num n]
End

Definition parse_def:
  parse [] x s = x ∧
  parse (CLOSE :: rest) x s = parse rest (Num 0) (x::s) ∧
  parse (OPEN :: rest) x s =
    (case s of [] => parse rest x s
     | (y::ys) => parse rest (Pair x y) ys) ∧
  parse (NUM n :: rest) x s = parse rest (Pair (Num n) x) s ∧
  parse (QUOTE n :: rest) x s = parse rest (Pair (quote n) x) s ∧
  parse (DOT :: rest) x s = parse rest (head x) s
End


