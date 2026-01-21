(*
  Formalization of the min coloring problem
*)
Theory color
Ancestors
  pbc graph_basic pbc_normalise
Libs
  preamble

val _ = numLib.temp_prefer_num();

(* f is a k-coloring function on the vertices {0..<v}
  iff it uses at most k colors ({0..<k}) and
      no two adjacent vertices have the same color *)
Definition is_k_color_def:
  is_k_color k f (v,e) ⇔
  (∀x. x < v ⇒ f x < k) ∧
  (∀x y.
    x < v ∧ y < v ∧
    is_edge e x y ⇒ f x ≠ f y)
End

Definition min_color_size_def:
  min_color_size g =
  MIN_SET ({k | ∃f. is_k_color k f g})
End

(* TODO: define an encoding, the annot and var types might not be correct *)
(* Type annot = ``:(num # num)``; *)
(* Type var = ``:num``; *)
Datatype:
  annot = EdgeColor num (* vertex 1 *) num (* vertex 2 *) num (* color *)
        | VertexHasColor num (* color constraint for specific color *)
End
Datatype:
  var = X num (* vertex *) num (* color *)
End

Definition gen_constraint_def:
  gen_constraint (n:num) ((v,e):graph) (EdgeColor x y c) =
    (if is_edge e x y then
       SOME (GreaterEqual, [(1i, Neg (X x c)); (1i, Neg (X y c))], 1i)
     else NONE) ∧
  gen_constraint (n:num) ((v,e):graph) (VertexHasColor vertex) =
    SOME (GreaterEqual, GENLIST (λcolor. (1i,Pos (X vertex color))) n, 1i)
End

Definition gen_named_constraint_def:
  gen_named_constraint n (v,e) a =
    case gen_constraint n (v,e) a of
    | NONE => []
    | SOME c => [(a,c)]
End

Definition flat_genlist_def:
  flat_genlist n f = FLAT (GENLIST f n)
End

(* TODO: define the encoding, assuming at most n colors are used *)
Definition encode_def:
  encode (n:num) ((v,e):graph) =
    (* every vertex has at least one color *)
    flat_genlist v (λvertex.
      gen_named_constraint n (v,e) (VertexHasColor vertex)) ++
    (* for each color: at least one end of each edge does not have that color *)
    flat_genlist n (λcolor.
      flat_genlist v (λx.
        flat_genlist v (λy.
          gen_named_constraint n (v,e) (EdgeColor x y color))))
  :(annot # var pbc) list
End

(* TODO: define the objective function, on at most n colors *)
Definition color_obj_def:
  color_obj (n:num) = SOME ([],0): ((var lin_term # int) option)
End

(* TODO: something along the lines of:
  for all k ≤ n
    there exists a k-coloring of the graph iff
    there exists a satisfying solution, with objective value k
*)
Theorem encode_correct:
  good_graph (v,e) ∧
  encode n (v,e) = constraints ⇒
  ARB
Proof
  cheat
QED

(* TODO Encode the variables as strings *)
Definition enc_string_def:
  (enc_string (x:var) = strlit "TODO")
End

(* TODO *)
Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  cheat
QED

(* TODO: not sure if annotation is necessary *)
Definition annot_string_def:
  annot_string (_:annot) = (SOME (strlit "TODO"):mlstring option)
End

Definition full_encode_def:
  full_encode n g =
  (map_obj enc_string (color_obj n),
  MAP (annot_string ## map_pbc enc_string) (encode n g))
End

(* TODO: some kind of key to be used to lazily index clauses; could be the same
  as the annot type *)
Type key = ``:annot``;

(* TODO: The input OPB will give mlstring option annotations.
  We may want to map it back to a key (or key option) *)
Definition mk_key_def:
  mk_key (ann:mlstring option) = SOME ARB:key option
End

(*
  TODO: for initial simplicity, we may wish to compare the
    input and lazy formulas by exact equality.

  However, for improved flexibility, we should perhaps
    allow for them to be equal up to normalization.
*)

(* TODO: return T iff
  the input data keyed corresponds to c *)
Definition lazy_constraint_aux_def:
  lazy_constraint_aux n g (i:key) (c: mlstring pbc) ⇔ T
End

Definition lazy_constraint_def:
  lazy_constraint n g (c: mlstring option # mlstring pbc) ⇔
    case mk_key (FST c) of
      NONE => F
    | SOME i => lazy_constraint_aux n g i (SND c)
End

Definition lazy_encode_def:
  lazy_encode n g fml =
  let le = lazy_constraint n g in
    EVERY le fml
End

(* Check that the objective actually matches up,
  e.g.:
    map_obj enc_string (color_obj n) = SOME obj
*)
Definition lazy_color_obj_def:
  lazy_color_obj n (obj: mlstring lin_term # int) ⇔ T
End

(* TODO: a theorem for full_lazy_encode.
  namely, every constraint it accepts is from full_encode *)

(* TODO: a top-level theorem for full_lazy_encode.
  namely, given a list of constraints cs, such that
    every c \in cs is lazy_encoded.

  If there is some PB conclusion about those constraints,
    then what can we conclude about the graph? *)

(* Attempt to guess the value of "n" based on the objective.
  The literals variables in the objective are all Pos literals *)
Definition parse_cu_def:
  parse_cu (c,l) =
  case l of
    Pos s =>
      if 3 ≤ strlen s then
        case mlint$fromNatString (substring s 3 (strlen s - 3)) of
          NONE => 0
        | SOME n => n
      else 0
  | _ => 0
End

Definition guess_n_def:
  guess_n (obj:mlstring lin_term # int) =
    MAX_LIST (MAP parse_cu (FST obj))
End

Definition lazy_full_encode_def:
  lazy_full_encode (g:graph) prob =
  case prob of
    (NONE:mlstring option,SOME obj, fml) =>
    let n = guess_n obj in
      if lazy_encode n g fml ∧ lazy_color_obj n obj
      then SOME n
      else NONE
  | _ => NONE
End

(* If the palette allowed is n, then we can claim a lower
  bound with at most n colors.
  No upper bound is to be used in the PB proof. *)
Definition conv_concl_def:
  (conv_concl n (OBounds lbi ubi) =
  if ubi = NONE then
    case lbi of NONE => SOME 0 (* Baseline bound *)
    | SOME lb =>
      if 0 ≤ lb ∧ Num lb ≤ n then SOME (Num lb)
      else NONE
  else NONE) ∧
  (conv_concl _ _ = NONE)
End
