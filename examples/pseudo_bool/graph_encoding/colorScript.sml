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
  iff it uses k colors {0..<k} and
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
Type annot = ``:(num # num)``;
Type var = ``:num``;

(* TODO: define the encoding, on at most n colors are used *)
Definition encode_def:
  encode (n:num) ((v,e):graph) = ARB:(annot # var pbc) list
End

(* TODO: define the objective function, on at most n colors *)
Definition color_obj_def:
  color_obj (n:num) = ARB : ((var lin_term # int) option)
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
  (enc_string (x:var) = ARB:mlstring)
End

(* TODO *)
Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  cheat
QED

(* TODO: not sure if annotation is necessary *)
Definition annot_string_def:
  annot_string ((x,y):annot) = (ARB:mlstring option)
End

Definition full_encode_def:
  full_encode n g =
  (map_obj enc_string (color_obj n),
  MAP (annot_string ## map_pbc enc_string) (encode n g))
End

(* TODO: SOME KIND OF ind TO BE USED TO LAZILY INDEX CLAUSES *)
Type ind = ``:mlstring``;

(* TODO: return T iff
  the input data indeed corresponds to c *)
Definition lazy_encode_def:
  lazy_encode n g (data:ind) (c: mlstring pbc) <=> T
End

(* TODO: a theorem for lazy_encode.
  namely, every constraint it accepts is from full_encode *)

(* TODO: a top-level theorem for lazy_encode.
  namely, given a list of constraints cs, such that
    every c \in cs is lazy_encoded.

  If there is some PB conclusion about those constraints,
    then what can we conclude about the graph? *)

