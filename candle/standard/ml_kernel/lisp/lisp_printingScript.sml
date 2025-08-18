(*
  Pretty printing for Lisp s-expressions
*)
Theory lisp_printing
Ancestors
  arithmetic list pair finite_map string lisp_values
Libs
  mp_then

(* pretty printing v *)

Definition num2str_def:
  num2str n = if n < 10 then [CHR (48 + n)] else
                num2str (n DIV 10) ++ [CHR (48 + (n MOD 10))]
End

Definition num2ascii_def:
  num2ascii n =
    if n = 0 then NONE else
      let k = n MOD 256 in
        if (ORD #"*" ≤ k ∧ k ≤ ORD #"z" ∧ k ≠ ORD #".") then
          if n < 256 then SOME [CHR k] else
            case num2ascii (n DIV 256) of
            | NONE => NONE
            | SOME s => SOME (s ++ [CHR k])
        else NONE
End

Definition ascii_name_def:
  ascii_name n =
    case num2ascii n of
    | NONE => NONE
    | SOME s => let k = ORD (HD s) in
                  if ORD #"0" ≤ k ∧ k ≤ ORD #"9" then NONE else SOME s
End

Definition name2str_def:
  name2str n =
    case ascii_name n of NONE => num2str n | SOME s => s
End

Definition dest_quote_def:
  dest_quote v =
    case v of
    | (Pair x (Pair (Num n) (Num 0))) =>
        (if x = Num (name "'") then SOME ("'" ++ name2str n) else NONE)
    | _ => NONE
End

Definition dest_list_def:
  dest_list (Num n) = ([],Num n) ∧
  dest_list (Pair x y) = let (l,e) = dest_list y in (x::l,e)
End

Theorem dest_list_size:
  ∀v e l.
    (l,e) = dest_list v ⇒
    lisp_v_size e ≤ lisp_v_size v ∧
    (~isNum v ⇒ lisp_v_size e < lisp_v_size v) ∧
    ∀x. MEM x l ⇒ lisp_v_size x < lisp_v_size v
Proof
  Induct_on ‘v’ \\ fs [dest_list_def,isNum_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ res_tac \\ fs [lisp_v_size_def]
QED

Datatype:
  pretty = Parenthesis pretty
         | Str string | Append pretty bool pretty | Size num pretty
End

Definition newlines_def:
  newlines [] = Str "" ∧
  newlines [x] = x ∧
  newlines (x::xs) = Append x T (newlines xs)
End

Definition v2pretty_def:
  v2pretty v =
    case v of Num n => Str (name2str n) | _ =>
    case dest_quote v of SOME s => Str s | NONE =>
      let (l,e) = dest_list v in
        Parenthesis
          (if e = Num 0 then newlines (MAP v2pretty l) else
             Append (newlines (MAP v2pretty l)) T
               (Append (Str " . ") T (v2pretty e)))
Termination
  WF_REL_TAC ‘measure lisp_v_size’ \\ rw []
  \\ imp_res_tac dest_list_size \\ fs [lisp_v_size_def,isNum_def]
End

Definition get_size_def:
  get_size (Size n x) = n ∧
  get_size (Append x _ y) = get_size x + get_size y + 1 ∧
  get_size (Parenthesis x) = get_size x + 2 ∧
  get_size _ = 0
End

Definition get_next_size_def:
  get_next_size (Size n x) = n ∧
  get_next_size (Append x _ y) = get_next_size x ∧
  get_next_size (Parenthesis x) = get_next_size x + 2 ∧
  get_next_size _ = 0
End

Definition annotate_def:
  annotate (Str s) = Size (LENGTH s) (Str s) ∧
  annotate (Parenthesis b) =
    (let b = annotate b in
       Size (get_size b + 2) (Parenthesis b)) ∧
  annotate (Append b1 n b2) =
    (let b1 = annotate b1 in
     let b2 = annotate b2 in
       (* Size (get_size b1 + get_size b2 + 1) *) (Append b1 n b2)) ∧
  annotate (Size n b) = annotate b
End

Definition remove_all_def:
  remove_all (Parenthesis v) = Parenthesis (remove_all v) ∧
  remove_all (Str v1) = Str v1 ∧
  remove_all (Append v2 _ v3) = Append (remove_all v2) F (remove_all v3) ∧
  remove_all (Size v4 v5) = remove_all v5
End

Definition smart_remove_def:
  smart_remove i k (Size n b) =
    (if k + n < 70 then remove_all b else smart_remove i k b) ∧
  smart_remove i k (Parenthesis v) = Parenthesis (smart_remove (i+1) (k+1) v) ∧
  smart_remove i k (Str v1) = Str v1 ∧
  smart_remove i k (Append v2 b v3) =
    let n2 = get_size v2 in
    let n3 = get_next_size v3 in
      if k + n2 + n3 < 50 then
        Append (smart_remove i k v2) F (smart_remove i (k+n2) v3)
      else
        Append (smart_remove i k v2) T (smart_remove i i v3)
End

Definition flatten_def:
  flatten indent (Size n p) s = flatten indent p s ∧
  flatten indent (Parenthesis p) s = "(" ++ flatten (indent ++ "   ") p (")" ++ s) ∧
  flatten indent (Str t) s = t ++ s ∧
  flatten indent (Append p1 b p2) s =
    flatten indent p1 ((if b then indent else " ") ++ flatten indent p2 s)
End

Definition v2str_def:
  v2str v = flatten "\n" (smart_remove 0 0 (annotate (v2pretty v))) ""
End

Definition is_comment_def:
  is_comment [] = T ∧
  is_comment (c::cs) =
    if c = CHR 35 then
      (case dropWhile (λx. x ≠ CHR 10) cs of
       | [] => F
       | (c::cs) => is_comment cs)
    else if c = CHR 10 then is_comment cs else F
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ rename [‘dropWhile f xs’]
  \\ qspecl_then [‘f’,‘xs’] mp_tac LENGTH_dropWhile_LESS_EQ
  \\ fs []
End

Definition vs2str_def:
  vs2str [] coms = "\n" ∧
  vs2str (x::xs) coms =
    ((case coms of [] => [] | (c::cs) => if is_comment c then c else []) ++
    ("\n" ++ (v2str x ++ ("\n" ++ vs2str xs (case coms of [] => [] | c::cs => cs)))))
End


