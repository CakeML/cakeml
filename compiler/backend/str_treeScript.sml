(*
  A Lisp inspired tree of mlstrings and a pretty printing function
*)
Theory str_tree
Ancestors
  arithmetic list pair mlstring

(* datatype and helper functions *)

Datatype:
  str_tree = Str mlstring | Pair str_tree str_tree | GrabLine str_tree
End

Definition isPair_def[simp]:
  isPair (Pair _ _) = T ∧
  isPair _ = F
End

Definition mk_list_def:
  mk_list [] = Str (strlit "") ∧
  mk_list (x::xs) = Pair x (mk_list xs)
End

(* pretty printing *)

Definition dest_list_def:
  dest_list (Pair x y) = (let (l,e) = dest_list y in (x::l,e)) ∧
  dest_list other = ([],other)
End

Theorem dest_list_size[local]:
  ∀v e l.
    (l,e) = dest_list v ⇒
    str_tree_size e ≤ str_tree_size v ∧
    (isPair v ⇒ str_tree_size e < str_tree_size v) ∧
    ∀x. MEM x l ⇒ str_tree_size x < str_tree_size v
Proof
  Induct_on ‘v’ \\ fs [dest_list_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ res_tac \\ fs [fetch "-" "str_tree_size_def"]
QED

Datatype:
  pretty = Parenthesis pretty
         | String mlstring
         | Append pretty bool pretty
         | Size num pretty
End

Definition newlines_def:
  newlines [] = String (strlit "") ∧
  newlines [x] = x ∧
  newlines (x::xs) = Append x T (newlines xs)
End

Definition v2pretty_def:
  v2pretty v =
    case v of
    | Str s => String s
    | GrabLine w => Size 100000 (v2pretty w)
    | _ =>
      let (l,e) = dest_list v in
        Parenthesis
          (if e = Str (strlit "") then
            newlines (MAP v2pretty l)
           else
             Append (newlines (MAP v2pretty l)) T
               (Append (String (strlit " . ")) T (v2pretty e)))
Termination
  WF_REL_TAC ‘measure str_tree_size’ \\ rw []
  \\ imp_res_tac dest_list_size \\ fs [fetch "-" "str_tree_size_def"]
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
  annotate (String s) = Size (strlen s) (String s) ∧
  annotate (Parenthesis b) =
    (let b = annotate b in
       Size (get_size b + 2) (Parenthesis b)) ∧
  annotate (Append b1 n b2) =
    (let b1 = annotate b1 in
     let b2 = annotate b2 in
       (* Size (get_size b1 + get_size b2 + 1) *) (Append b1 n b2)) ∧
  annotate (Size n b) = Size n (annotate b)
End

Definition remove_all_def:
  remove_all (Parenthesis v) = Parenthesis (remove_all v) ∧
  remove_all (String v1) = String v1 ∧
  remove_all (Append v2 _ v3) = Append (remove_all v2) F (remove_all v3) ∧
  remove_all (Size v4 v5) = remove_all v5
End

Definition smart_remove_def:
  smart_remove i k (Size n b) =
    (if k + n < 70 then remove_all b else smart_remove i k b) ∧
  smart_remove i k (Parenthesis v) = Parenthesis (smart_remove (i+1) (k+1) v) ∧
  smart_remove i k (String v1) = String v1 ∧
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
  flatten indent (Parenthesis p) s =
    strlit "(" :: flatten (concat [indent; strlit "   "]) p (strlit ")" :: s) ∧
  flatten indent (String t) s = t :: s ∧
  flatten indent (Append p1 b p2) s =
    flatten indent p1 ((if b then indent else strlit " ") :: flatten indent p2 s)
End

Definition v2strs_def:
  v2strs end v = flatten (strlit "\n") (smart_remove 0 0 (annotate (v2pretty v))) [end]
End

Theorem test1[local]:
  concat (v2strs (strlit "")
                 (Pair (Str (strlit "hello"))
                       (Pair (Str (strlit "there")) (Str (strlit ""))))) =
  strlit "(hello there)"
Proof
  EVAL_TAC
QED

Theorem test2[local]:
  concat (v2strs (strlit "")
                 (mk_list (Str (strlit "test") ::
                  MAP GrabLine [Str (strlit "hi"); Str (strlit "there")]))) =
  strlit "(test\n   hi\n   there)"
Proof
  EVAL_TAC
QED

(*
Definition vs2str_def:
  vs2str [] coms = "\n" ∧
  vs2str (x::xs) coms =
    ((case coms of [] => [] | (c::cs) => if is_comment c then c else []) ++
    ("\n" ++ (v2str x ++ ("\n" ++ vs2str xs (case coms of [] => [] | c::cs => cs)))))
End
*)

