let map f =
  let rec map_rec = function
    | [] -> []
    | x :: xs -> f x :: map_rec xs
  in
  map_rec

module Terms = struct
  type head = MkHead of string * (term * term) list ref
  and term = Var of int | Prop of head * term list

  let lemmas = ref ([] : head list)

  let headname (MkHead (n, _)) = n

  let get name =
    let rec get_rec = function
      | hd :: hdl -> if headname hd = name then hd else get_rec hdl
      | [] -> let entry = MkHead (name, ref []) in
              lemmas := entry :: !lemmas;
              entry
    in
    get_rec (!lemmas)

  let r = ref ([] : (term * term) list)
  let add_lemma = function
    | Prop (_, [left; right]) -> r := (left, right) :: !r
    | _ -> invalid_arg ""

  exception Failure of string

  type binding = Bind of int * term

  let get_binding v =
    let rec get_rec = function
      | [] -> raise (Failure "unbound")
      | Bind (w, t) :: rest -> if v = w then t else get_rec rest
    in
    get_rec

  let apply_subst alist =
    let rec as_rec = function
      | Var v -> (try get_binding v alist with Failure _ -> Var v)
      | Prop (head, argl) -> Prop (head, map as_rec argl)
    in
    as_rec

  exception Unify

  let rec unify term1 term2 = unify1 term1 term2 []
  and unify1 term1 term2 unify_subst =
    match term2 with
    | Var v ->
      (try
        if get_binding v unify_subst = term1 then unify_subst else raise Unify
      with
      | Failure _ -> Bind (v, term1) :: unify_subst
      )
    | Prop (head2, argl2) ->
      (match term1 with
      | Var _ -> raise Unify
      | Prop (head1, argl1) ->
        if head1 = head2 then
          unify1_lst argl1 argl2 unify_subst
        else
          raise Unify
      )
  and unify1_lst x y z =
    match x, y, z with
    | [], [], unify_subst -> unify_subst
    | h1 :: r1, h2 :: r2, unify_subst ->
      unify1_lst r1 r2 (unify1 h1 h2 unify_subst)
    | _ -> raise Unify

  let rec rewrite = function
    | Var v -> Var v
    | Prop (MkHead (n, p), argl) ->
      rewrite_with_lemmas (Prop (MkHead (n, p), map rewrite argl)) !p
  and rewrite_with_lemmas term = function
    | [] -> term
    | (t1, t2) :: rest ->
      (try
        rewrite (apply_subst (unify term t1) t2)
      with
      | Unify -> rewrite_with_lemmas term rest
      )
end
