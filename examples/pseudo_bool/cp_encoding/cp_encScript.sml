(*
  The end-to-end encoder from CP to PB
*)
Theory cp_enc
Libs
  preamble
Ancestors
  cp pbc cp_to_ilp cp_to_ilp_all ilp_to_pb mlmap

Definition cencode_bound_var_def:
  cencode_bound_var bnd X =
  let (lb,ub) = bnd X in
  let bX = encode_ivar bnd (X:mlstring) in
  [
    (SOME(concat[«i[»;X;«][lb]»])
      ,(pbc$GreaterEqual,bX,lb));
    (SOME(concat[«i[»;X;«][ub]»])
      ,(pbc$LessEqual,bX,ub));
  ]
End

Definition cencode_bound_all_def:
  (cencode_bound_all bnd [] = Nil) ∧
  (cencode_bound_all bnd (x::xs) =
    Append (List (cencode_bound_var bnd x))
      (cencode_bound_all bnd xs))
End

(* Ordering-valued shortlex comparison on mlstring, via the native
  String.Fast primitives fast_lt/fast_le *)
Definition fast_compare_def:
  fast_compare s1 s2 =
  if fast_lt s1 s2 then LESS
  else if fast_le s1 s2 then EQUAL
  else GREATER
End

Theorem TotOrd_fast_compare:
  TotOrd fast_compare
Proof
  `fast_compare = TO_of_LinearOrder fast_lt` by
    (rw[FUN_EQ_THM,fast_compare_def,totoTheory.TO_of_LinearOrder,
      mlstringTheory.fast_le_thm]>>
    metis_tac[mlstringTheory.fast_lt_nonrefl])>>
  metis_tac[totoTheory.TotOrd_TO_of_Strong,
    mlstringTheory.StrongLinearOrder_fast_lt]
QED

(* Bounds map keyed by fast_compare; first occurrence of a key wins,
  matching ALOOKUP *)
Definition mk_bnd_map_def:
  (mk_bnd_map [] = mlmap$empty fast_compare) ∧
  (mk_bnd_map ((k,v)::bnd) = mlmap$insert (mk_bnd_map bnd) k v)
End

Theorem map_ok_mk_bnd_map:
  ∀bnd. map_ok (mk_bnd_map bnd)
Proof
  Induct
  >- rw[mk_bnd_map_def,mlmapTheory.empty_thm,TotOrd_fast_compare]>>
  Cases_on`h`>>
  rw[mk_bnd_map_def,mlmapTheory.insert_thm]
QED

Theorem lookup_mk_bnd_map:
  ∀bnd x. mlmap$lookup (mk_bnd_map bnd) x = ALOOKUP bnd x
Proof
  Induct
  >- rw[mk_bnd_map_def,mlmapTheory.lookup_thm,mlmapTheory.empty_thm,
        TotOrd_fast_compare]>>
  Cases_on`h`>>
  rw[mk_bnd_map_def,mlmapTheory.lookup_insert,map_ok_mk_bnd_map]
QED

Definition map_bnd_lookup_def:
  map_bnd_lookup m x =
  case mlmap$lookup m x of
    NONE => (0i,0i)
  | SOME v => v
End

Theorem map_bnd_lookup_mk_bnd_map:
  map_bnd_lookup (mk_bnd_map bnd) = bnd_lookup bnd
Proof
  rw[FUN_EQ_THM,map_bnd_lookup_def,bnd_lookup_def,lookup_mk_bnd_map]
QED

Definition encode_def:
  encode bnd cs =
  let m = mk_bnd_map bnd in
  let bndm = map_bnd_lookup m in
  let cs = append (FST (cencode_constraints bndm cs init_ec)) in
  let cs' = MAP (I ## encode_iconstraint_one bndm) cs in
  let bndcs = cencode_bound_all bndm (MAP FST bnd) in
  append (Append bndcs (List cs'))
End

Definition encode_nivar_def:
  encode_nivar bnd V =
  mul_lin_term (-1) (encode_ivar bnd V)
End

(* The projection variables for X *)
Definition proj_ivar_def:
  proj_ivar bnd (X:'a) =
  let (comp,h) = bit_width bnd X in
  let bits = GENLIST (λi. (Bit X i)) h in
  if comp then
      (Sign X :: bits)
  else bits
End

(* Returns the optional preserved set and the objective *)
Definition encode_prob_type_def:
  encode_prob_type bnd pty =
  case pty of
    Decision => (NONE, NONE)
  | Minimize v => (NONE, SOME (encode_ivar (bnd_lookup bnd) v, 0i))
  | Maximize v => (NONE, SOME (encode_nivar (bnd_lookup bnd) v, 0i))
  | Enumerate vs =>
    (SOME
      (FLAT (MAP (proj_ivar (bnd_lookup bnd)) vs)),
    NONE)
End

Theorem MAP_SND_MAP_I_FST:
  MAP SND (MAP (I ## f) ls) =
  MAP f (MAP SND ls)
Proof
  rw[MAP_MAP_o]
QED

Theorem MAP_SND_cencode_bound_all[simp]:
  ∀ls.
  MAP SND (append (cencode_bound_all bnd ls)) =
  encode_bound_all bnd ls
Proof
  Induct>>
  rw[cencode_bound_all_def,encode_bound_all_def,
    cencode_bound_var_def,encode_bound_var_def]>>
  pairarg_tac>>simp[]
QED

Theorem encode_sem_1:
  ALL_DISTINCT (MAP FST cs) ∧
  cp_sat (bnd_lookup bnd) (set (MAP SND cs)) wi ⇒
  ∃wb.
  satisfies (reify_epb (wi,wb))
    (set (MAP SND (encode bnd cs)))
Proof
  `∃es ec'. cencode_constraints (bnd_lookup bnd) cs init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def,map_bnd_lookup_mk_bnd_map,cp_sat_def,MAP_SND_MAP_I_FST]>>
  simp[GSYM encode_iconstraint_all_def,GSYM encode_iconstraint_all_sem_1]>>
  fs[GSYM EVERY_MEM,EVERY_MAP]>>
  drule_all cencode_constraints_thm_1>>
  rw[]>>
  fs[EVERY_MAP]>>
  metis_tac[encode_bound_all_sem_1]
QED

Theorem encode_sem_2:
  satisfies w (set (MAP SND (encode bnd cs))) ⇒
  cp_sat (bnd_lookup bnd) (set (MAP SND cs))
    (unreify_epb (bnd_lookup bnd) w)
Proof
  `∃es ec'. cencode_constraints (bnd_lookup bnd) cs init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def,map_bnd_lookup_mk_bnd_map]>>
  fs[MAP_SND_MAP_I_FST,cencode_bound_all_def,MAP_MAP_o,o_DEF]>>
  drule_at Any encode_bound_all_sem_2>>
  impl_tac >- (
    simp[bnd_lookup_def]>>
    strip_tac>>TOP_CASE_TAC>>
    drule ALOOKUP_MEM>>
    simp[MEM_MAP]>>
    metis_tac[FST])>>
  rw[]>>
  simp[cp_sat_def,GSYM EVERY_MEM,EVERY_MAP]>>
  irule cencode_constraints_thm_2>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  qexists_tac`λx. w (Var x)`>>
  simp[GSYM encode_iconstraint_all_sem_2]>>
  gvs[encode_iconstraint_all_def,MAP_MAP_o,o_DEF]
QED

(* Going into strings for the final encoder *)
Definition format_string_def:
  format_string epb =
  case epb of
    Sign x =>
      concat [«i[»; escape_bad_brackets x; «][sign]»]
  | Bit x n =>
      concat [«i[»; escape_bad_brackets x; «][b»;toString n;«]»]
  | Var v => format_var v
End

Definition find_open_def:
  find_open passed [] = SOME (passed, []) ∧
  find_open passed (c::cs) =
    if c = #"\\" then
      if cs = [] then NONE else
        find_open (passed ++ [HD cs]) (TL cs)
    else if c = #"[" then
      SOME (passed ++ "[", cs)
    else
      find_open (passed ++ [c]) cs
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ \\ rw []
End

Theorem find_open_less[local]:
  ∀passed xs ys zs.
    find_open passed xs = SOME (ys,zs) ⇒ LENGTH zs ≤ LENGTH xs
Proof
  ho_match_mp_tac find_open_ind \\ rw [find_open_def] \\ gvs []
QED

Definition split_bracket_def:
  split_bracket depth passed [] = NONE ∧
  split_bracket depth passed (c::cs) =
    if c = #"\\" then
      if cs = [] then NONE else
        split_bracket depth (passed ++ [#"\\"; HD cs]) (TL cs)
    else if c = #"[" then
      split_bracket (depth+1n) (passed ++ [c]) cs
    else if c = #"]" then
      if depth = 0 then SOME (passed ++ [c],cs) else
        split_bracket (depth-1n) (passed ++ [c]) cs
    else
      split_bracket depth (passed ++ [c]) cs
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND)’ \\ rw []
End

Theorem split_bracket_less[local]:
  ∀depth passed xs ys zs.
    split_bracket depth passed xs = SOME (ys,zs) ⇒ LENGTH zs < LENGTH xs
Proof
  ho_match_mp_tac split_bracket_ind \\ rw [split_bracket_def] \\ gvs []
QED

Definition split_brackets_def:
  split_brackets xs =
    case find_open "" xs of
    | NONE => [xs]
    | SOME (zs,xs) =>
      case split_bracket 0 "" xs of
      | NONE => [zs++xs]
      | SOME (xs,ys) => (zs ++ xs) :: split_brackets ys
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ imp_res_tac split_bracket_less \\ rw []
  \\ imp_res_tac find_open_less \\ fs []
End

Theorem case_implode_eq_explode[simp,local]:
  (case y of implode x => x) = explode y
Proof
  Cases_on ‘y’ \\ gvs []
QED

Theorem split_bracket_escape_chars:
  ∀s ys xs d.
    split_bracket d ys (escape_chars s ++ xs) =
    split_bracket d (ys ++ escape_chars s) xs
Proof
  Induct \\ simp [escape_chars_def]
  \\ simp [split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ rw []
  \\ simp [split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ fs []
QED

Theorem split_bracket_not:
  ∀n ys s rest d.
    ¬naive_needs_escaping n s ⇒
    split_bracket n ys (s ++ rest) =
    split_bracket 0 (ys ++ s) rest
Proof
  ho_match_mp_tac split_bracket_ind \\ rw []
  \\ simp [split_bracket_def]
  \\ Cases_on ‘c = #"\\"’ \\ gvs [naive_needs_escaping_def]
  \\ Cases_on ‘c = #"["’ \\ gvs [naive_needs_escaping_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ fs []
QED

Theorem split_bracket_escape_bad_brackets[simp,local]:
  split_bracket 0 ys (explode (escape_bad_brackets a) ++ rest) =
  split_bracket 0 (ys ++ explode (escape_bad_brackets a)) rest
Proof
  Cases_on ‘a’
  \\ rw [escape_bad_brackets_def,needs_escaping_eq]
  >-
   (simp [split_bracket_def,split_bracket_escape_chars]
    \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND])
  \\ drule split_bracket_not \\ fs []
QED

Theorem split_bracket_fast_forward:
  ∀xs ys rest.
    EVERY (λx. ~ MEM x "[]\\") xs ⇒
    split_bracket d ys (xs ++ rest) =
    split_bracket d (ys ++ xs) rest
Proof
  Induct \\ gvs [] \\ rw []
  \\ simp [Once split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
QED

Theorem MEM_intersperse[local]:
  ∀sep l x. MEM x (intersperse sep l) ⇒ x = sep ∨ MEM x l
Proof
  recInduct mllistTheory.intersperse_ind
  \\ rw [mllistTheory.intersperse_def]
  \\ metis_tac []
QED

Theorem EVERY_explode_concatWith[local]:
  EVERY P (explode sep) ∧ EVERY (λs. EVERY P (explode s)) l ⇒
  EVERY P (explode (concatWith sep l))
Proof
  rw [mlstringTheory.concatWith_def, mlstringTheory.concat_thm,
      mlstringTheory.explode_implode, EVERY_MEM, MEM_FLAT, MEM_MAP]
  \\ drule MEM_intersperse \\ strip_tac \\ gvs [] \\ res_tac \\ fs []
QED

Theorem split_bracket_format_int_list[simp,local]:
  split_bracket d ys (explode (format_int_list i) ++ rest) =
  split_bracket d (ys ++ explode (format_int_list i)) rest
Proof
  irule split_bracket_fast_forward
  \\ gvs [format_int_list_def]
  \\ irule EVERY_explode_concatWith
  \\ conj_tac >- EVAL_TAC
  \\ simp [EVERY_MAP] \\ Induct_on ‘i’ \\ gvs []
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ rename [‘num_to_dec_string nn’]
  \\ qspec_then ‘nn’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac
  \\ fs [isDigit_def]
  \\ var_eq_tac \\ fs []
QED

Theorem split_bracket_format_num_list[simp,local]:
  split_bracket d ys (explode (format_num_list i) ++ rest) =
  split_bracket d (ys ++ explode (format_num_list i)) rest
Proof
  irule split_bracket_fast_forward
  \\ gvs [format_num_list_def]
  \\ irule EVERY_explode_concatWith
  \\ conj_tac >- EVAL_TAC
  \\ simp [EVERY_MAP] \\ Induct_on ‘i’ \\ gvs []
  \\ gen_tac
  \\ rename [‘num_to_str nn’]
  \\ Cases_on ‘num_to_str nn’
  \\ imp_res_tac mlintTheory.num_to_str_every
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac \\ fs []
  \\ var_eq_tac \\ fs []
QED

Theorem split_bracket_num_to_string[simp,local]:
  split_bracket d ys (explode (num_to_str n) ++ rest) =
  split_bracket d (ys ++ explode (num_to_str n)) rest
Proof
  irule split_bracket_fast_forward
  \\ rename [‘num_to_str nn’]
  \\ Cases_on ‘num_to_str nn’
  \\ imp_res_tac mlintTheory.num_to_str_every
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac \\ fs []
  \\ var_eq_tac \\ fs []
QED

Theorem split_bracket_int_to_string[simp,local]:
  split_bracket d ys (explode (int_to_string #"-" n) ++ rest) =
  split_bracket d (ys ++ explode (int_to_string #"-" n)) rest
Proof
  irule split_bracket_fast_forward
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ rename [‘num_to_dec_string nn’]
  \\ qspec_then ‘nn’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac
  \\ fs [isDigit_def]
  \\ var_eq_tac \\ fs []
QED

Theorem split_Sign[local]:
  split_brackets (explode (format_string (Sign a))) =
  ["i[" ++ explode (escape_bad_brackets a) ++ "]"; "[sign]"; ""]
Proof
  simp [format_string_def, mlstringTheory.concat_def]
  \\ ntac 8 (simp [Once split_brackets_def]
             \\ simp [find_open_def]
             \\ simp [Once split_bracket_def])
QED

Theorem split_Bit[local]:
  split_brackets (explode (format_string (Bit a n))) =
  ["i[" ++ explode (escape_bad_brackets a) ++ "]"; "[b" ++ explode (toString n) ++ "]"; ""]
Proof
  simp [format_string_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
QED

Theorem avar_cases[local]:
  ∀x : mlstring avar.
    (∃s i. x = INL (Eq (INL s) i)) ∨
    (∃s i. x = INL (Ge (INL s) i)) ∨
    (∃s i. x = INL (Eq (INR s) i)) ∨
    (∃s i. x = INL (Ge (INR s) i)) ∨
    (∃q y. x = INR (q,Flag y)) ∨
    (∃q l. x = INR (q,Values l NONE)) ∨
    (∃q l y. x = INR (q,Values l (SOME y))) ∨
    (∃q l. x = INR (q,Indices l NONE)) ∨
    (∃q l y. x = INR (q,Indices l (SOME y)))
Proof
  Cases
  >- (Cases_on ‘x'’ \\ gvs [] \\ Cases_on ‘s’ \\ gvs [])
  \\ Cases_on ‘y’ \\ Cases_on ‘r’ \\ gvs []
  \\ Cases_on ‘o'’ \\ gvs []
QED

Theorem split_var_Eq_INL[local]:
  split_brackets (explode (format_var (INL (Eq (INL s) i)))) =
  ["i[" ++ explode (escape_bad_brackets s) ++ "]";
   "[eq" ++ explode (int_to_string #"-" i) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
QED

Theorem split_var_Eq_INR[local]:
  split_brackets (explode (format_var (INL (Eq (INR s) i)))) =
  ["n[" ++ explode (int_to_string #"-" s) ++ "]";
   "[eq" ++ explode (int_to_string #"-" i) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def, find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_int_to_string]
  \\ simp [Once split_bracket_def, find_open_def]
  \\ simp [Once split_bracket_def, find_open_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
QED

Theorem split_var_Ge_INL[local]:
  split_brackets (explode (format_var (INL (Ge (INL s) i)))) =
  ["i[" ++ explode (escape_bad_brackets s) ++ "]";
   "[ge" ++ explode (int_to_string #"-" i) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ EVAL_TAC
QED

Theorem split_var_Ge_INR[local]:
  split_brackets (explode (format_var (INL (Ge (INR s) i)))) =
  ["n[" ++ explode (int_to_string #"-" s) ++ "]";
   "[ge" ++ explode (int_to_string #"-" i) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ EVAL_TAC
QED

Theorem split_var_Flag[local]:
  split_brackets (explode (format_var (INR (q,Flag y)))) =
  ["b[" ++ explode (escape_bad_brackets q) ++ "]";
   "[" ++ explode (escape_bad_brackets y) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def, find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def, find_open_def]
  \\ EVAL_TAC
QED

Theorem split_var_Indices[local]:
  split_brackets (explode (format_var (INR (q,Indices l NONE)))) =
  ["x[" ++ explode (escape_bad_brackets q) ++ "]";
   "[" ++ explode (format_num_list l) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [split_bracket_def, format_annot_def,split_bracket_def, find_open_def]
  \\ EVAL_TAC
QED

Theorem split_var_Indices_SOME[local]:
  split_brackets (explode (format_var (INR (q,Indices l (SOME r))))) =
  ["x[" ++ explode (escape_bad_brackets q) ++ "]";
   "[" ++ explode (format_num_list l) ++ "]";
   "[" ++ explode (escape_bad_brackets r) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_format_num_list]
  \\ simp [split_bracket_def, format_annot_def,split_bracket_def,find_open_def]
QED

Theorem split_var_Values[local]:
  split_brackets (explode (format_var (INR (q,Values l NONE)))) =
  ["v[" ++ explode (escape_bad_brackets q) ++ "]";
   "[" ++ explode (format_int_list l) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_format_int_list]
  \\ simp [split_bracket_def, format_annot_def,find_open_def]
QED

Theorem split_var_Values_SOME[local]:
  split_brackets (explode (format_var (INR (q,Values l (SOME x))))) =
  ["v[" ++ explode (escape_bad_brackets q) ++ "]";
   "[" ++ explode (format_int_list l) ++ "]";
   "[" ++ explode (escape_bad_brackets x) ++ "]"; ""]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def, find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def, find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets]
  \\ simp [Once split_brackets_def,split_bracket_def,find_open_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_bad_brackets,
                  split_bracket_format_int_list]
  \\ simp [split_bracket_def, format_annot_def, find_open_def]
  \\ EVAL_TAC
QED

Theorem toString_lemma[local]:
  num_to_dec_string n ≠ STRING #"-" xs
Proof
  strip_tac
  \\ qspec_then ‘n’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ simp [isDigit_def]
QED

Theorem int_to_string_11[local]:
  int_to_string #"-" i = int_to_string #"-" j ⇔ i = j
Proof
  rw [mlintTheory.int_to_string_def, mlstringTheory.escape_char_def]
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ Cases_on ‘i’ \\ Cases_on ‘j’ \\ gvs []
  \\ rw [toString_lemma]
QED

Theorem str_divider_lemma[local]:
  ∀s1 s2 c xs1 xs2.
    STRCAT s1 (STRING c xs1) = STRCAT s2 (STRING c xs2) ∧ ~MEM c s1 ∧ ~MEM c s2 ⇒
    s1 = s2 ∧ xs1 = xs2
Proof
  Induct \\ Cases_on ‘s2’
  >- simp []
  >- simp []
  >- (pop_assum kall_tac \\ simp [])
  \\ simp_tac (srw_ss()) []
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
  \\ rpt strip_tac
  \\ last_x_assum drule_all \\ simp []
QED

Theorem concatWith_nil[local]:
  concatWith sep [] = «»
Proof
  rw [mlstringTheory.concatWith_def, mllistTheory.intersperse_def]
QED

Theorem concatWith_sing[local]:
  concatWith sep [x] = x
Proof
  rw [mlstringTheory.concatWith_def, mllistTheory.intersperse_def,
      mlstringTheory.concat_cons]
QED

Theorem concatWith_cons2[local]:
  concatWith sep (x::y::t) = x ^ sep ^ concatWith sep (y::t)
Proof
  rw [mlstringTheory.concatWith_def, mllistTheory.intersperse_def,
      mlstringTheory.concat_cons]
QED

Theorem MEM_sep_strcat[local]:
  MEM c (explode (a ^ implode [c] ^ b))
Proof
  simp [mlstringTheory.explode_strcat, mlstringTheory.explode_implode]
QED

Theorem concatWith_MAP_11[local]:
  INJ f UNIV UNIV ⇒
  ∀xs ys.
    EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ «») xs ∧
    EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ «») ys ∧
    concatWith (implode [c]) (MAP f xs) = concatWith (implode [c]) (MAP f ys) ⇒
    xs = ys
Proof
  strip_tac \\ Induct
  >- (rw [concatWith_nil]
      \\ Cases_on ‘ys’ \\ gvs []
      \\ Cases_on ‘t’
      \\ gvs [concatWith_sing, concatWith_cons2]
      \\ Cases_on ‘f h’
      \\ gvs [mlstringTheory.strcat_def, mlstringTheory.concat_def])
  \\ rw []
  \\ Cases_on ‘ys’ \\ gvs [concatWith_nil]
  >- (Cases_on ‘xs’
      \\ gvs [concatWith_sing, concatWith_cons2]
      \\ Cases_on ‘f h’
      \\ gvs [mlstringTheory.strcat_def, mlstringTheory.concat_def])
  \\ Cases_on ‘xs’ \\ Cases_on ‘t’
  \\ gvs [concatWith_sing, concatWith_cons2]
  >- metis_tac [INJ_DEF, IN_UNIV]
  >- metis_tac [MEM_sep_strcat]
  \\ qpat_x_assum ‘_ ^ _ = _ ^ _’ (mp_tac o Q.AP_TERM ‘explode’)
  \\ REWRITE_TAC [mlstringTheory.explode_strcat, mlstringTheory.explode_implode,
                  GSYM APPEND_ASSOC, APPEND]
  \\ strip_tac
  \\ drule_all str_divider_lemma
  \\ strip_tac
  \\ gvs [mlstringTheory.explode_11]
  \\ qmatch_asmsub_rename_tac ‘f x1 = f x2’
  \\ qmatch_asmsub_rename_tac
       ‘concatWith _ (f y1::MAP f z1) = concatWith _ (f y2::MAP f z2)’
  \\ ‘x1 = x2’ by metis_tac [INJ_DEF, IN_UNIV]
  \\ ‘y1::z1 = y2::z2’ by (first_x_assum irule \\ simp [])
  \\ gvs []
QED

Theorem concatWith_11:
  EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ «») xs ∧
  EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ «») ys ∧
  INJ f UNIV UNIV ⇒
  (concatWith (implode [c]) (MAP f xs) = concatWith (implode [c]) (MAP f ys) ⇔ xs = ys)
Proof
  strip_tac \\ eq_tac
  >- (strip_tac \\ metis_tac [concatWith_MAP_11])
  \\ rw []
QED

Theorem format_int_list_11[local]:
  format_int_list l = format_int_list l' ⇔ l = l'
Proof
  gvs [format_int_list_def]
  \\ irule concatWith_11
  \\ simp [INJ_DEF, int_to_string_11]
  \\ gvs [EVERY_MEM]
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ simp [mlstringTheory.escape_char_def]
  \\ rename [‘num_to_dec_string nn’]
  \\ qspec_then ‘nn’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac
  \\ fs [isDigit_def]
QED

Theorem format_num_list_11[local]:
  format_num_list l = format_num_list l' ⇔ l = l'
Proof
  gvs [format_num_list_def]
  \\ irule concatWith_11
  \\ simp [INJ_DEF, mlintTheory.num_to_str_11]
  \\ gvs [EVERY_MEM] \\ rw []
  \\ simp [mlstringTheory.escape_char_def]
  \\ rename [‘num_to_str nn’]
  \\ Cases_on ‘num_to_str nn’
  \\ imp_res_tac mlintTheory.num_to_str_every
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac \\ fs []
  \\ imp_res_tac mlintTheory.num_to_str_imp_cons
  \\ gvs []
QED

Theorem to_split_brackets[local]:
  x = y ⇒ split_brackets (explode x) = split_brackets (explode y)
Proof
  rw []
QED

Theorem format_string_INJ:
  INJ format_string UNIV UNIV
Proof
  gvs [INJ_DEF] \\ Cases \\ Cases_on ‘y’
  \\ disch_tac
  \\ dxrule to_split_brackets
  \\ gvs [split_Sign, split_Bit, escape_bad_brackets_11,
          mlintTheory.num_to_str_11]
  \\ rename [‘Var aa’] \\ Cases_on ‘aa’ using avar_cases
  \\ simp [format_string_def]
  \\ gvs [split_var_Eq_INL, split_var_Eq_INR, split_var_Ge_INL,
          split_var_Ge_INR, split_var_Flag, split_var_Values,
          split_var_Values_SOME, split_var_Indices,
          split_var_Indices_SOME]
  \\ rename [‘format_var bb’] \\ Cases_on ‘bb’ using avar_cases
  \\ gvs [split_var_Eq_INL, split_var_Eq_INR, split_var_Ge_INL,
          split_var_Ge_INR, split_var_Flag, split_var_Values,
          split_var_Values_SOME, split_var_Indices, int_to_string_11,
          split_var_Indices_SOME, escape_bad_brackets_11,
          format_num_list_11, format_int_list_11]
QED

Theorem int_bit_unreify_epb[local]:
  bit_width bnd X = (comp,h) ⇒
  int_bit n (unreify_epb bnd w X) =
    if n < h then w (Bit X n) else (comp ∧ w (Sign X))
Proof
  rw [unreify_epb_def] >> simp [int_bitwiseTheory.int_bit_int_of_bits, EL_GENLIST]
QED

Theorem unreify_reify[local]:
  valid_assignment bnd wi ⇒
  unreify_epb bnd (reify_epb (wi,wb)) X = wi X
Proof
  metis_tac [encode_ivar_sem_1, encode_ivar_sem_2]
QED

Theorem MEM_proj_ivar_Bit[local]:
  bit_width bnd X = (comp,h) ⇒ (MEM (Bit X i) (proj_ivar bnd X) ⇔ i < h)
Proof
  rw [proj_ivar_def, MEM_GENLIST]
QED

Theorem MEM_proj_ivar_Sign[local]:
  bit_width bnd X = (comp,h) ∧ comp ⇒ MEM (Sign X) (proj_ivar bnd X)
Proof
  rw [proj_ivar_def]
QED

Theorem unreify_epb_cong[local]:
  (∀e. MEM e (proj_ivar bnd X) ⇒ (w1 e ⇔ w2 e)) ⇒
  unreify_epb bnd w1 X = unreify_epb bnd w2 X
Proof
  strip_tac >>
  rw [unreify_epb_def] >> pairarg_tac >> gvs [] >>
  `GENLIST (λi. w1 (Bit X i)) h = GENLIST (λi. w2 (Bit X i)) h` by
    (simp [GENLIST_FUN_EQ] >> rw [] >> first_x_assum irule >>
     metis_tac [MEM_proj_ivar_Bit]) >>
  simp [] >>
  Cases_on`comp` >> gvs [] >>
  `w1 (Sign X) = w2 (Sign X)` by (first_x_assum irule >> metis_tac [MEM_proj_ivar_Sign]) >>
  simp []
QED

Theorem unreify_INTER[local]:
  MAP (unreify_epb bnd (set (FLAT (MAP (proj_ivar bnd) vs)) ∩ w)) vs =
  MAP (unreify_epb bnd w) vs
Proof
  irule MAP_CONG >> simp [] >> rw [] >>
  irule unreify_epb_cong >> rw [] >>
  `MEM e (FLAT (MAP (proj_ivar bnd) vs))` by
    (simp [MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac []) >>
  simp [IN_INTER, IN_APP]
QED

Theorem proj_ivar_bit[local]:
  MEM x (proj_ivar bnd y) ⇒
  ∃p. ∀ww. ww x ⇔ int_bit p (unreify_epb bnd ww y)
Proof
  strip_tac >>
  `∃comp h. bit_width bnd y = (comp,h)` by metis_tac [PAIR] >>
  Cases_on`comp` >> gvs [proj_ivar_def, MEM_GENLIST]
  >- (qexists_tac`h` >> rw [] >> drule int_bit_unreify_epb >> simp [])
  >- (qexists_tac`i` >> rw [] >> drule int_bit_unreify_epb >> simp [])
  >- (qexists_tac`i` >> rw [] >> drule int_bit_unreify_epb >> simp [])
QED

Theorem mem_proj_unreify_eq[local]:
  MEM x (proj_ivar bnd y) ∧ unreify_epb bnd w y = unreify_epb bnd w' y ⇒
  (w x ⇔ w' x)
Proof
  rw [] >> drule proj_ivar_bit >> rw [] >> metis_tac []
QED

Theorem proj_INJ[local]:
  MAP (unreify_epb bnd w) vs = MAP (unreify_epb bnd w') vs ⇒
  set (FLAT (MAP (proj_ivar bnd) vs)) ∩ w =
  set (FLAT (MAP (proj_ivar bnd) vs)) ∩ w'
Proof
  strip_tac >>
  `∀X. MEM X vs ⇒ unreify_epb bnd w X = unreify_epb bnd w' X` by fs [MAP_EQ_f] >>
  simp [EXTENSION, IN_INTER, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rw [] >> eq_tac >> rw [] >> qexists_tac`y` >> simp [] >>
  `w x ⇔ w' x` by
    (irule mem_proj_unreify_eq >> first_assum (irule_at Any) >>
     first_x_assum irule >> simp []) >>
  fs [IN_APP]
QED

Theorem encode_EEnum_BIJ[local]:
  ALL_DISTINCT (MAP FST cs) ⇒
  ∃f. BIJ f
    (proj_pres (set (FLAT (MAP (proj_ivar (bnd_lookup bnd)) vs)))
               {w | satisfies w (set (MAP SND (encode bnd cs)))})
    (cp_proj vs {w | cp_sat (bnd_lookup bnd) (set (MAP SND cs)) w})
Proof
  strip_tac >>
  qexists_tac`λt. MAP (unreify_epb (bnd_lookup bnd) t) vs` >>
  simp [proj_pres_def, cp_proj_def, BIJ_DEF, INJ_DEF, SURJ_DEF, PULL_EXISTS] >>
  rpt conj_tac
  >- (rw [] >> qexists_tac`unreify_epb (bnd_lookup bnd) w` >>
      simp [unreify_INTER] >> irule encode_sem_2 >> simp [])
  >- (rw [] >> irule proj_INJ >> fs [unreify_INTER])
  >- (rw [] >> qexists_tac`unreify_epb (bnd_lookup bnd) w` >>
      simp [unreify_INTER] >> irule encode_sem_2 >> simp [])
  >- (rw [] >> drule_all encode_sem_1 >> rw [] >>
      qexists_tac`reify_epb (w,wb)` >> simp [unreify_INTER] >>
      irule MAP_CONG >> simp [] >> rw [] >>
      irule unreify_reify >> fs [cp_sat_def])
QED

Definition full_encode_def:
  full_encode (bnd,cs,pty) =
  let (pres,obj) = encode_prob_type bnd pty in
  (OPTION_MAP (MAP format_string) pres,
    map_obj format_string obj,
    MAP (I ## map_pbc format_string) (encode bnd cs))
End

(* Check validity and convert a PB conclusion into a CP one *)
Definition conv_concl_def:
  (conv_concl pty (OBounds lbi ubi) =
    case pty of
      Maximize v =>
        SOME (OBounds (OPTION_MAP (λv. -v) ubi) (OPTION_MAP (λv. -v) lbi))
    | Minimize v => SOME (OBounds lbi ubi)
    | _ => NONE) ∧
  (conv_concl pty (EEnum n complete) =
    case pty of
      Enumerate vs => SOME (EEnum n complete)
    | _ => NONE) ∧
  (conv_concl pty concl = SOME concl)
End

Theorem full_encode_sem_concl:
  ALL_DISTINCT (MAP FST cs) ∧
  full_encode (bnd,cs,pty) = (pres,obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj (pres_set_list pres) concl ∧
  conv_concl pty concl = SOME concl' ⇒
  cp_inst_sem_concl (bnd,cs,pty) concl'
Proof
  strip_tac>>
  gvs[full_encode_def]>>
  qpat_x_assum`sem_concl _ _ _ _` mp_tac>>
  gvs[UNCURRY_EQ]>>
  rename1`_ = (pres,obj)`>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  simp[GSYM IMAGE_IMAGE, GSYM (Once LIST_TO_SET_MAP)]>>
  `pres_set_list (OPTION_MAP (MAP format_string) pres) =
    IMAGE format_string(pres_set_list pres)` by
      (simp[pres_set_list_def]>>
      every_case_tac>>fs[LIST_TO_SET_MAP])>>
  pop_assum SUBST1_TAC>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    simp[FINITE_pres_set_list]>>
    assume_tac format_string_INJ>>
    CONJ_TAC>- (
      drule INJ_SUBSET>>
      disch_then match_mp_tac>>
      simp[])>>
    gvs[INJ_DEF])>>
  Cases_on`concl`>>gvs[conv_concl_def]
  >~[`NoConcl`]
  >- fs[cp_inst_sem_concl_def,cp_sem_concl_def]
  >~[`DSat`]
  >- (
    fs[cp_inst_sem_concl_def,cp_sem_concl_def,sem_concl_def]>>
    simp[cp_satisfiable_def,satisfiable_def]>>
    metis_tac[encode_sem_1,encode_sem_2,PAIR])
  >~[`DUnsat`]
  >- (
    fs[cp_inst_sem_concl_def,cp_sem_concl_def,sem_concl_def]>>
    simp[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
    metis_tac[encode_sem_1,encode_sem_2,PAIR])
  >~[`OBounds lbi ubi`]
  >- (
    gvs[AllCaseEqs(),cp_inst_sem_concl_def,cp_sem_concl_def,
      sem_concl_def,encode_prob_type_def]>>
    strip_tac
    >- (
      simp[cp_is_lb_def,cp_has_ub_def]>>
      CONJ_TAC >- (
        Cases_on`lbi`>>fs[]
        >- (
          fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
          metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
        rw[]>>
        drule_all encode_sem_1>>
        strip_tac>>fs[]>>
        first_x_assum drule>>
        simp[eval_obj_def]>>
        DEP_REWRITE_TAC[encode_ivar_sem_1]>>
        fs[cp_sat_def])>>
      Cases_on`ubi`>>fs[]>>
      drule encode_sem_2>>
      disch_then (irule_at Any)>>
      fs[GSYM encode_ivar_sem_2,eval_obj_def])
    >- (
      simp[cp_is_ub_def,cp_has_lb_def]>>
      CONJ_TAC >- (
        Cases_on`ubi`>>fs[]>>
        drule encode_sem_2>>
        disch_then (irule_at Any)>>
        fs[GSYM encode_ivar_sem_2,eval_obj_def,encode_nivar_def]>>
        intLib.ARITH_TAC)>>
      Cases_on`lbi`>>fs[]
      >- (
        fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
        metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
      rw[]>>
      drule_all encode_sem_1>>
      rw[]>>fs[]>>
      first_x_assum drule>>
      simp[eval_obj_def,encode_nivar_def]>>
      DEP_REWRITE_TAC[encode_ivar_sem_1]>>
      fs[cp_sat_def]>>
      intLib.ARITH_TAC))
  >~[`EEnum n b`]
  >- (
    gvs[AllCaseEqs(),cp_inst_sem_concl_def,cp_sem_concl_def,
      sem_concl_def,encode_prob_type_def]>>
    qmatch_goalsub_abbrev_tac`CARD proj_pb_sols`>>
    qmatch_goalsub_abbrev_tac`_ ⇒ n ≤ CARD proj_cp_sols ∧ _`>>
    `?f. BIJ f proj_pb_sols proj_cp_sols` by
      (unabbrev_all_tac >> simp [pres_set_list_def] >>
       irule encode_EEnum_BIJ >> simp []) >>
    drule_at Any FINITE_BIJ_CARD>>
    impl_tac >- (
      fs[Abbr`proj_pb_sols`]>>
      irule FINITE_proj_pres>>
      irule FINITE_pres_set_list)>>
    rw[])
QED
