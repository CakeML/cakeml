module Main = struct
  let name = "Knuth-Bendix"

  type term = Var of int | Term of string * term list

  let length xs =
    let rec j k = function
      | [] -> k
      | _ :: xs -> j (k + 1) xs
    in
    j 0 xs
  let rev xs =
    let rec f acc = function
      | [] -> acc
      | x :: xs -> f (x :: acc) xs
    in
    f [] xs
  let app f =
    let rec app_rec = function
      | [] -> ()
      | x :: xs -> f x; app_rec xs
    in
    app_rec
  let map f =
    let rec map_rec = function
      | [] -> []
      | x :: xs -> f x :: map_rec xs
    in
    map_rec

  let it_list f =
    let rec it_rec acc = function
      | [] -> acc
      | x :: xs -> it_rec (f acc x) xs
    in
    it_rec

  let it_list2 f =
    let rec it_rec acc xs ys =
      match xs, ys with
      | [], [] -> acc
      | x :: xs, y :: ys -> it_rec (f acc (x, y)) xs ys
      | _ -> failwith "it_list2"
    in
    it_rec

  let exists p =
    let rec exists_rec = function
      | [] -> false
      | x :: xs -> p x || exists_rec xs
    in
    exists_rec

  let for_all p =
    let rec for_all_rec = function
      | [] -> true
      | x :: xs -> p x && for_all_rec xs
    in
    for_all_rec

  let try_find f =
    let rec try_find_rec = function
      | [] -> failwith "try_find"
      | x :: xs -> try f x with Failure _ -> try_find_rec xs
    in
    try_find_rec

  let partition p =
    let rec part_rec = function
      | [] -> [], []
      | x :: xs ->
        let pos, neg = part_rec xs in
        if p x then x :: pos, neg else pos, x :: neg
    in
    part_rec

  let mem x =
    let rec mem_rec = function
      | [] -> false
      | y :: ys -> (x = y) || mem_rec ys
    in mem_rec

  let union xs =
    let rec union_rec = function
      | [] -> xs
      | y :: ys -> if mem y xs then union_rec ys else y :: union_rec ys
    in
    union_rec

  let mem_assoc x =
    let rec mem_rec = function
      | [] -> false
      | (y, v) :: ys -> (x = y) || mem_rec ys
    in mem_rec

  let assoc x =
    let rec assoc_rec = function
      | [] -> failwith "find"
      | (y, v) :: ys -> if x = y then v else assoc_rec ys
    in
    assoc_rec

  let print _ = ()
  let print_num _ = ()
  let message s = print s; print "\n"

  (* Term manipulations *)

  let rec vars = function
    | Var n -> [n]
    | Term (_, ts) -> vars_of_list ts
  and vars_of_list = function
    | [] -> []
    | t :: ts -> union (vars t) (vars_of_list ts)

  let substitute subst =
    let rec subst_rec = function
      | Term (oper, sons) -> Term (oper, map subst_rec sons)
      | Var n as t -> try assoc n subst with Failure _ -> t
    in
    subst_rec

  let change f =
    let rec change_rec = function
      | x :: xs -> fun n -> if n = 1 then f x :: xs
                                     else x :: change_rec xs (n - 1)
      | _ -> fun _ -> failwith "change"
    in
    change_rec

  (* Term replacement: replace m u n => m[u<-n] *)
  let replace m u n =
    let rec reprec = function
      | _, [] -> n
      | Term (oper, sons), n :: u ->
        Term (oper, change (fun p -> reprec (p, u)) sons n)
      | _ -> failwith "replace"
    in
    reprec (m, u)

  (* matching : term -> term -> subst *)
  let matching t0 t1 =
    let rec match_rec subst = function
      | Var v, m ->
        if mem_assoc v subst then
          if m = assoc v subst then subst else failwith "missing"
        else
          (v, m) :: subst
      | Term (op0, sons0), Term (op1, sons1) when op0 = op1 ->
        it_list2 match_rec subst sons0 sons1
      | _ -> failwith "missing"
    in
    match_rec [] (t0, t1)

  (* A naive unification algorithm *)

  let compsubst subst0 subst1 =
    map (fun (v, t) -> (v, substitute subst0 t)) subst1 @ subst0

  let occurs n =
    let rec occur_rec = function
      | Var m -> m = n
      | Term (_, sons) -> exists occur_rec sons
    in
    occur_rec

  let rec unify = function
    | Var n0 as t0, t1 ->
      if t0 = t1 then []
      else if occurs n0 t0 then failwith "unify"
      else [n0, t1]
    | t0, Var n1 ->
      if occurs n1 t0 then failwith "unify"
      else [n1, t0]
    | Term (op0, sons0), Term (op1, sons1) ->
      if op0 = op1 then
        it_list2 (fun s (t0, t1) -> compsubst (unify (substitute s t0,
                                                      substitute s t1)) s)
                 [] sons0 sons1
      else failwith "unify"

  (* We need to print terms with variables independently from input terms
     obtained by parsing. We give arbitrary names v1, v2, ... to their
     variables. *)

  let infixes = ["+"; "*"]

  let rec pretty_term = function
    | Var n -> print_string "v"; print_num n
    | Term (oper, sons) ->
      if mem oper infixes then
        match sons with
        | [s0; s1] -> pretty_close s0; print_string oper; pretty_close s1
        | _ -> failwith "pretty_term : infix arity <> 2"
      else
        print_string oper;
        match sons with
        | [] -> ()
        | t :: ts ->
          print_string "(";
          pretty_term t;
          app (fun t -> print_string ","; pretty_term t) ts;
          print_string ")"
  and pretty_close = function
    | Term (oper, _) as m ->
      if mem oper infixes then
        (print_string "("; pretty_term m; print_string ")")
      else pretty_term m
    | m -> pretty_term m

  (* Equation manipulations *)

  (* standardizes an equation so its variables are 1, 2, 3, ... *)
  let mk_rule m n =
    let all_vars = union (vars m) (vars n) in
    let k, subst =
      it_list (fun (i, sigma) v -> i + 1, (v, Var i) :: sigma) (1, []) all_vars
    in
    k - 1, (substitute subst m, substitute subst n)

  (* checks that rules are numbered in seqence and returns their number *)
  let check_rules xs = it_list (fun n (k, _) ->
    if k = n + 1 then k else failwith "Rule numbers not in sequence") 0 xs

  let pretty_rule (k, (_, (m, n))) =
    print_num k; print_string " : ";
    pretty_term m; print_string " = "; pretty_term n;
    print_newline ()

  let pretty_rules xs = app pretty_rule xs

  (* Rewriting *)

  (* Top-level rewriting. Let eq : l = r be an equation, and m be a term such
     that l <= m. With sigma = matching l m, we define the image of m by eq as
     sigma r *)
  let reduce l m = substitute (matching l m)

  (* A more efficient version of can (rewrite1 (l, r)) for r arbitrary *)
  let reducible l =
    let rec redrec m =
      try matching l m; true
      with Failure _ ->
        match m with
        | Term (_, sons) -> exists redrec sons
        | _ -> false
    in
    redrec

  (* mreduce : rules -> term -> term *)
  let mreduce rules m =
    let redex (_, (_, (l, r))) = reduce l m r in try_find redex rules

  (* One step of rewirting in leftmost-outermost strategy, with multiple
     rules *)
  (* fails if no redex is found *)
  (* mrewrite1 : rules -> term -> term *)
  let mrewrite1 rules =
    let rec rewrec m =
      try mreduce rules m
      with Failure _ ->
        let rec tryrec = function
          | [] -> failwith "mrewrite1"
          | son :: sons ->
            try rewrec son :: sons with Failure _ -> son :: tryrec sons
        in
        match m with
        | Term (f, sons) -> Term (f, tryrec sons)
        | _ -> failwith "mrewrite1"
    in
    rewrec

  (* Iterating rewrite1. Returns a normal form. May loop forever *)
  (* mrewrite_all : rules -> term -> term *)
  let mrewrite_all rules =
    let rec rew_loop m =
      try rew_loop (mrewrite1 rules m) with Failure _ -> m
    in
    rew_loop

  (*
  pretty_term (mrewrite_all Group_rules m where m, _ = <<A*(I(B)*B)>>);;
  ==> A*U
  *)

  (* Recursive path ordering *)

  type ordering = Greater | Equal | NotGE

  let ge_ord order pair = match order pair with NotGE -> false | _ -> true
  let gt_ord order pair = match order pair with Greater -> true | _ -> false
  let eq_ord order pair = match order pair with Equal -> true | _ -> false

  let rem_eq equiv =
    let rec remrec x = function
      | [] -> failwith "rem_eq"
      | y :: ys -> if equiv (x, y) then ys else y :: remrec x ys
    in
    remrec

  let diff_eq equiv (xs, ys) =
    let rec diffrec = function
      | ([], _) as p -> p
      | (x :: xs, ys) ->
        try diffrec (xs, rem_eq equiv x ys)
        with Failure _ ->
          let xs', ys' = diffrec (xs, ys) in (x :: xs', ys')
    in
    if length xs > length ys then diffrec (ys, xs) else diffrec (xs, ys)

  (* multiselt extension of order *)
  let mult_ext order = function
    | Term (_, sons0), Term (_, sons1) ->
      (match diff_eq (eq_ord order) (sons0, sons1) with
      | [], [] -> Equal
      | l0, l1 ->
        if for_all (fun n -> exists (fun m -> order (m, n) = Greater) l0) l1
          then Greater
          else NotGE
      )
    | _ -> failwith "mult_ext"

  (* lexicographic extension of order *)
  let lex_ext order = function
    | (Term (_, sons0) as m), (Term (_, sons1) as n) ->
      let rec lexrec = function
        | [], [] -> Equal
        | [], _ -> NotGE
        | _, [] -> Greater
        | x :: xs, y :: ys ->
          match order (x, y) with
          | Greater ->
            if for_all (fun n' -> gt_ord order (m, n')) ys
              then Greater
              else NotGE
          | Equal -> lexrec (xs, ys)
          | NotGE ->
            if exists (fun m' -> ge_ord order (m', n)) xs
              then Greater
              else NotGE
      in
      lexrec (sons0, sons1)
    | _ -> failwith "lex_ext"

  (* recursive path ordering *)
  let rpo op_order ext =
    let rec rporec (m, n) =
      if m = n then Equal else
      match n with
      | Var _ -> NotGE
      | Term (op0, sons0) ->
        match n with
        | Var n -> if occurs n m then Greater else NotGE
        | Term (op1, sons1) ->
          match op_order op0 op1 with
          | Greater ->
            if for_all (fun n' -> gt_ord rporec (m, n')) sons1
              then Greater
              else NotGE
          | Equal -> ext rporec (m, n)
          | NotGE ->
            if exists (fun m' -> gt_ord rporec (m', n)) sons0
              then Greater
              else NotGE
    in
    rporec

  (* Critical pairs *)

  (* All (u, sig) such that n/u (&var) unifies with m,
     with principal unifier sig *)

  let super m =
    let rec suprec = function
      | Term (_, sons) as n ->
        let collate (pairs, n) son =
          pairs @ map (fun (u, sigma) -> n :: u, sigma) (suprec son), n + 1 in
        let insides = fst (it_list collate ([], 1) sons) in
        (try ([], unify (m, n)) :: insides
        with Failure _ -> insides)
      | _ -> []
    in
    suprec

  (* Ex:
  let (m, _) = <<F (A, B)>>
  and (n, _) = <<H (F (A, x), F (x, y))>> in super m n;;
  ==> [[1], [2, Term ("B", [])];                          x <- B
       [2], [2, Term ("A", []); 1, Term ("B", [])]]       x <- A  y <- B
  *)

  (* All (u, sigma), u&[], such that n/u unifies with m *)
  (* super_strict : term -> term -> (num list & subst) list *)
  let super_strict m = function
    | Term (_, sons) ->
      let collate (pairs, n) son =
        pairs @ map (fun (u, sigma) -> n :: u, sigma) (super m son), n + 1 in
      fst (it_list collate ([], 1) sons)
    | _ -> []

  (* Critical pairs of l0=r0 with l1=r1 *)
  (* critical_pairs : term_pair -> term_pair -> term_pair list *)
  let critical_pairs (l0, r0) (l1, r1) =
    let mk_pair (u, sigma) =
      substitute sigma (replace l1 u r0), substitute sigma r1 in
    map mk_pair (super l0 l1)

  (* Strict critical pairs of l0=r0 with l1=r1 *)
  (* strict_critical_pairs : term_pair -> term_pair -> term_pair list *)
  let strict_critical_pairs (l0, r0) (l1, r1) =
    let mk_pair (u, sigma) =
      substitute sigma (replace l1 u r0), substitute sigma r1 in
    map mk_pair (super_strict l0 l1)

  (* All critical pairs of eq0 with eq1 *)
  let mutual_critical_pairs eq0 eq1 =
    strict_critical_pairs eq0 eq1 @ critical_pairs eq0 eq1

  (* Renaming variables *)
  let rename n (t0, t1) =
    let rec ren_rec = function
      | Var k -> Var (k + n)
      | Term (oper, sons) -> Term (oper, map ren_rec sons)
    in
    ren_rec t0, ren_rec t1

  (* Completion *)

  let deletion_message (k, _) =
    print_string "Rule "; print_num k; message " deleted"

  (* Generate failure message *)
  let non_orientable (m, n) =
    pretty_term m; print_string " = "; pretty_term n; print_newline ()

  (* Improved Knuth-Bendix completion procedure *)
  (* kb_completion : (term_pair -> bool) -> num -> rules -> term_pair list ->
                     (num & num) -> term_pair list -> rules *)
  let kb_completion greater =
    let rec kbrec n rules =
      let normal_form = mrewrite_all rules in
      let get_rule k = assoc k rules in
      let rec process failures =
        let rec processf (k, l) =
          let rec processkl = function
            | [] ->
              if k < l then next_criticals (k + 1, l) else
              if l < n then next_criticals (1, l + 1) else
              (match failures with
              | [] -> rules
              | _ -> message "Non-orientable equations:";
                     app non_orientable failures;
                     failwith "kb_completion"
              )
            | (m_, n_) :: eqs ->
              let m_' = normal_form m_
              and n_' = normal_form n_ in
              let enter_rule (left, right) =
                let new_rule = (n + 1, mk_rule left right) in
                pretty_rule new_rule;
                let left_reducible (_, (_, (l, _))) = reducible left l in
                let (reds, irreds) = partition left_reducible rules in
                app deletion_message reds;
                let right_reduce (m, (_, (l, r))) =
                  m, mk_rule l (mrewrite_all (new_rule :: rules) r) in
                let irreds' = map right_reduce irreds in
                let eqs' = map (fun (_, (_, pair)) -> pair) reds in
                kbrec (n + 1) (new_rule :: irreds') [] (k, l)
                      (eqs @ eqs' @ failures)
              in
              if m_' = n_' then processkl eqs else
              if greater (m_', n_') then enter_rule (m_', n_') else
              if greater (n_', m_') then enter_rule (n_', m_') else
              process ((m_', n_') :: failures) (k, l) eqs
          in
          processkl
        and next_criticals (k, l) =
          try
            let (v, el) = get_rule l in
            if k = l then
              processf (k, l) (strict_critical_pairs el (rename v el))
            else
              try
                let (_, ek) = get_rule k in
                processf (k, l) (mutual_critical_pairs el (rename v ek))
              with Failure "find" ->
                (* rule k deleted *)
                next_criticals (k + 1, l)
          with Failure "find" ->
            (* rule l deleted *)
            next_criticals (1, l + 1)
        in
        processf
      in
      process
    in
    kbrec

  let kb_complete greater complete_rules rules =
    let n = check_rules complete_rules in
    let eqs = map (fun (_, (_, pair)) -> pair) rules in
    let completed_rules =
      kb_completion greater n complete_rules [] (n, n) eqs in
    message "Canonical set found:";
    pretty_rules (rev completed_rules);
    ()

  let group_rules = [
    (1, (1, (Term("*", [Term("U",[]); Var 1]), Var 1)));
    (2, (1, (Term("*", [Term("I",[Var 1]); Var 1]), Term("U",[]))));
    (3, (3, (Term("*", [Term("*", [Var 1; Var 2]); Var 3]),
             Term("*", [Var 1; Term("*", [Var 2; Var 3])]))))]

  let geom_rules = [
    (1,(1,(Term ("*",[(Term ("U",[])); (Var 1)]),(Var 1))));
    (2,(1,(Term ("*",[(Term ("I",[(Var 1)])); (Var 1)]),(Term ("U",[])))));
    (3,(3,(Term ("*",[(Term ("*",[(Var 1); (Var 2)])); (Var 3)]),
     (Term ("*",[(Var 1); (Term ("*",[(Var 2); (Var 3)]))])))));
    (4,(0,(Term ("*",[(Term ("A",[])); (Term ("B",[]))]),
     (Term ("*",[(Term ("B",[])); (Term ("A",[]))])))));
    (5,(0,(Term ("*",[(Term ("C",[])); (Term ("C",[]))]),(Term ("U",[])))));
    (6,(0,
     (Term
      ("*",
       [(Term ("C",[]));
        (Term ("*",[(Term ("A",[])); (Term ("I",[(Term ("C",[]))]))]))]),
     (Term ("I",[(Term ("A",[]))])))));
    (7,(0,
     (Term
      ("*",
       [(Term ("C",[]));
        (Term ("*",[(Term ("B",[])); (Term ("I",[(Term ("C",[]))]))]))]),
     (Term ("B",[])))))
  ]

  let group_rank = function
    | "U" -> 0
    | "*" -> 1
    | "I" -> 2
    | "B" -> 3
    | "C" -> 4
    | "A" -> 5

  let group_precedence op0 op1 =
    let r0 = group_rank op0
    and r1 = group_rank op1 in
    if r0 = r1 then Equal else
    if r0 > r1 then Greater else
    NotGE

  let group_order = rpo group_precedence lex_ext

  let greater pair = match group_order pair with Greater -> true | _ -> false

  let doit () = kb_complete greater [] geom_rules

  let doit i =
    let rec loop n =
      if n = 0 then () else
      doit (); loop (n - 1)
    in
    loop i

  let testit _ = ()
end
