open preamble MiniMLTheory; 
open unifPropsTheory;

val _ = new_theory "unify";

val _ = Hol_datatype `
infer_t = 
    Infer_Tvar_db of num
  | Infer_Tapp of infer_t list => tc0
  | Infer_Tfn of infer_t => infer_t
  | Infer_Tuvar of num`;

val infer_t_size_def = fetch "-" "infer_t_size_def";

val _ = Hol_datatype `
atom = 
    TC_tag of tc0
  | DB_tag of num
  | Tfn_tag
  | Tapp_tag
  | Null_tag`;

val encode_infer_t_def = Define `
(encode_infer_t (Infer_Tvar_db n) =
  Const (DB_tag n)) ∧
(encode_infer_t (Infer_Tfn t1 t2) =
  Pair (Const Tfn_tag) (Pair (encode_infer_t t1) (encode_infer_t t2))) ∧
(encode_infer_t (Infer_Tapp ts tc) =
  Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) (encode_infer_ts ts))) ∧
(encode_infer_t (Infer_Tuvar n) =
  Var n) ∧
(encode_infer_ts [] =
  Const Null_tag) ∧
(encode_infer_ts (t::ts) =
  Pair (encode_infer_t t) (encode_infer_ts ts))`;

val decode_infer_t_def = Define `
(decode_infer_t (Var n) =
  Infer_Tuvar n) ∧
(decode_infer_t (Const (DB_tag n)) =
  Infer_Tvar_db n) ∧
(decode_infer_t (Pair (Const Tfn_tag) (Pair s1 s2)) =
  Infer_Tfn (decode_infer_t s1) (decode_infer_t s2)) ∧
(decode_infer_t (Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) s)) =
  Infer_Tapp (decode_infer_ts s) tc) ∧
(decode_infer_ts (Const Null_tag) =
  []) ∧ 
(decode_infer_ts (Pair s1 s2) =
  decode_infer_t s1 :: decode_infer_ts s2)`;

val decode_left_inverse = Q.prove (
`(!t. decode_infer_t (encode_infer_t t) = t) ∧
 (!ts. decode_infer_ts (encode_infer_ts ts) = ts)`,
Induct >>
rw [encode_infer_t_def, decode_infer_t_def]);

val t_unify_def = Define `
t_unify subst t1 t2 = unify subst (encode_infer_t t1) (encode_infer_t t2)`;

val apply_subst_t = Define `
apply_subst_t subst t = decode_infer_t (subst_APPLY subst (encode_infer_t t))`;

val _ = export_theory ();
