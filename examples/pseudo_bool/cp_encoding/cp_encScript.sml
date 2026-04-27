(*
  The end-to-end encoder from CP to PB
*)
Theory cp_enc
Libs
  preamble
Ancestors
  cp pbc cp_to_ilp cp_to_ilp_all ilp_to_pb

Definition cencode_bound_var_def:
  cencode_bound_var bnd X =
  let (lb,ub) = bnd X in
  let bX = encode_ivar bnd (X:mlstring) in
  [
    (SOME(concat[strlit"i[";X;strlit"][lb]"])
      ,(pbc$GreaterEqual,bX,lb));
    (SOME(concat[strlit"i[";X;strlit"][ub]"])
      ,(pbc$LessEqual,bX,ub));
  ]
End

Definition cencode_bound_all_def:
  (cencode_bound_all bnd [] = Nil) ∧
  (cencode_bound_all bnd (x::xs) =
    Append (List (cencode_bound_var bnd x))
      (cencode_bound_all bnd xs))
End

Definition encode_def:
  encode bnd cs =
  let bndm = bnd_lookup bnd in
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
  rw[encode_def,cp_sat_def,MAP_SND_MAP_I_FST]>>
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
  rw[encode_def]>>
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
      concat [strlit"i["; escape_open_bracket x; strlit"][sign]"]
  | Bit x n =>
      concat [strlit"i["; escape_open_bracket x; strlit"][b";toString n;strlit"]"]
  | Var v => format_var v
End

Definition split_bracket_def:
  split_bracket passed [] = NONE ∧
  split_bracket passed (c::cs) =
    if c = CHR 91 (* [ *) ∧ ~(passed ≠ [] ⇒ LAST passed = CHR 92) then
      SOME (passed, cs)
    else
      split_bracket (passed ++ [c]) cs
End

Theorem split_bracket_less[local]:
  ∀xs passed ys zs.
    split_bracket passed xs = SOME (ys,zs) ⇒ LENGTH zs < LENGTH xs
Proof
  Induct \\ gvs [split_bracket_def] \\ rw [] \\ res_tac \\ gvs []
QED

Definition split_brackets_def:
  split_brackets xs =
    case split_bracket "" xs of
    | NONE => [xs]
    | SOME (xs,ys) => xs :: split_brackets ys
Termination
  WF_REL_TAC ‘measure LENGTH’
  \\ rw [] \\ imp_res_tac split_bracket_less
End

Theorem escape_open_bracket_eq:
  escape_open_bracket s = implode (escape_chars (explode s))
Proof
  rw [escape_open_bracket_def]
  \\ gvs [has_char_to_escape_thm, o_DEF]
  \\ Cases_on ‘s’ \\ gvs [mlstringTheory.implode_def]
  \\ rename [‘EVERY _ xs’] \\ Induct_on ‘xs’ \\ gvs []
  \\ simp [escape_chars_def]
QED

Theorem mlstring_forall:
  (∀s. P s) = ∀xs. P (implode xs)
Proof
  eq_tac \\ rw []
  \\ first_x_assum $ qspec_then ‘explode s’ mp_tac
  \\ gvs []
QED

Theorem escape_open_bracket_11:
  ∀a a'. escape_open_bracket a = escape_open_bracket a' ⇔ a = a'
Proof
  simp [escape_open_bracket_eq, mlstringTheory.implode_def, mlstring_forall]
  \\ Induct \\ Cases_on ‘xs'’ \\ gvs []
  \\ gvs [escape_chars_def]
  \\ rw [] \\ gvs []
QED

Theorem case_strlit_eq_explode[simp,local]:
  (case y of strlit x => x) = explode y
Proof
  Cases_on ‘y’ \\ gvs []
QED

Theorem split_bracket_escape_open_bracket[simp,local]:
  split_bracket ys (explode (escape_open_bracket a) ++ rest) =
  split_bracket (ys ++ explode (escape_open_bracket a)) rest
Proof
  fs [escape_open_bracket_eq]
  \\ qid_spec_tac ‘rest’
  \\ qid_spec_tac ‘ys’
  \\ qspec_tac (‘explode a’,‘xs’)
  \\ Induct
  \\ rw [escape_chars_def]
  \\ simp [Once split_bracket_def]
  \\ simp [Once split_bracket_def]
  \\ rw []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
QED

Theorem split_bracket_fast_forward:
  ∀xs ys rest.
    EVERY (λx. x ≠ CHR 91) xs ⇒
    split_bracket ys (xs ++ rest) =
    split_bracket (ys ++ xs) rest
Proof
  Induct \\ gvs [] \\ rw []
  \\ simp [Once split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
QED

Theorem split_bracket_format_int_list[simp,local]:
  split_bracket ys (explode (format_int_list i) ++ rest) =
  split_bracket (ys ++ explode (format_int_list i)) rest
Proof
  irule split_bracket_fast_forward
  \\ gvs [format_int_list_def, mlstringTheory.concatWith_def]
  \\ rename [‘concatWith_aux _ _ b’]
  \\ qid_spec_tac ‘b’
  \\ Induct_on ‘i’ \\ gvs []
  \\ gvs [format_int_list_def, mlstringTheory.concatWith_def,
          mlstringTheory.concatWith_aux_def]
  \\ rw [] \\ Cases_on ‘b’
  \\ gvs [format_int_list_def, mlstringTheory.concatWith_def,
          mlstringTheory.concatWith_aux_def]
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ rename [‘num_to_dec_string nn’]
  \\ qspec_then ‘nn’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac
  \\ fs [isDigit_def]
QED

Theorem split_bracket_format_num_list[simp,local]:
  split_bracket ys (explode (format_num_list i) ++ rest) =
  split_bracket (ys ++ explode (format_num_list i)) rest
Proof
  irule split_bracket_fast_forward
  \\ gvs [format_num_list_def, mlstringTheory.concatWith_def]
  \\ rename [‘concatWith_aux _ _ b’]
  \\ qid_spec_tac ‘b’
  \\ Induct_on ‘i’ \\ gvs []
  \\ gvs [format_int_list_def, mlstringTheory.concatWith_def,
          mlstringTheory.concatWith_aux_def]
  \\ rw [] \\ Cases_on ‘b’
  \\ gvs [format_int_list_def, mlstringTheory.concatWith_def,
          mlstringTheory.concatWith_aux_def]
  \\ rename [‘num_to_str nn’]
  \\ Cases_on ‘num_to_str nn’
  \\ imp_res_tac mlintTheory.num_to_str_every
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac \\ fs []
QED

Theorem split_bracket_num_to_string[simp,local]:
  split_bracket ys (explode (num_to_str n) ++ rest) =
  split_bracket (ys ++ explode (num_to_str n)) rest
Proof
  irule split_bracket_fast_forward
  \\ rename [‘num_to_str nn’]
  \\ Cases_on ‘num_to_str nn’
  \\ imp_res_tac mlintTheory.num_to_str_every
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac \\ fs []
QED

Theorem split_bracket_int_to_string[simp,local]:
  split_bracket ys (explode (int_to_string #"-" n) ++ rest) =
  split_bracket (ys ++ explode (int_to_string #"-" n)) rest
Proof
  irule split_bracket_fast_forward
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ rename [‘num_to_dec_string nn’]
  \\ qspec_then ‘nn’ mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
  \\ gvs [EVERY_MEM]
  \\ rw [] \\ strip_tac \\ res_tac
  \\ fs [isDigit_def]
QED

Theorem split_Sign[local]:
  split_brackets (explode (format_string (Sign a))) =
  ["i"; explode (escape_open_bracket a) ++ "]"; "sign]"]
Proof
  simp [format_string_def, mlstringTheory.concat_def]
  \\ ntac 3 (simp [Once split_brackets_def] \\ simp [split_bracket_def])
QED

Theorem split_Bit[local]:
  split_brackets (explode (format_string (Bit a n))) =
  ["i"; explode (escape_open_bracket a) ++ "]"; "b" ++ explode (toString n) ++ "]"]
Proof
  simp [format_string_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
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
  ["i"; explode (escape_open_bracket s) ++ "]";
   "eq" ++ explode (int_to_string #"-" i) ++ "]"]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Eq_INR[local]:
  split_brackets (explode (format_var (INL (Eq (INR s) i)))) =
  ["n"; explode (int_to_string #"-" s) ++ "]";
   STRING #"e" (STRING #"q" (STRCAT (explode (int_to_string #"-" i)) "]"))]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Ge_INL[local]:
  split_brackets (explode (format_var (INL (Ge (INL s) i)))) =
  ["i"; STRCAT (explode (escape_open_bracket s)) "]";
   STRING #"g" (STRING #"e" (STRCAT (explode (int_to_string #"-" i)) "]"))]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Ge_INR[local]:
  split_brackets (explode (format_var (INL (Ge (INR s) i)))) =
  ["n"; STRCAT (explode (int_to_string #"-" s)) "]";
   STRING #"g" (STRING #"e" (STRCAT (explode (int_to_string #"-" i)) "]"))]
Proof
  simp [format_var_def, format_reif_def, format_varc_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Flag[local]:
  split_brackets (explode (format_var (INR (q,Flag y)))) =
  ["b"; STRCAT (explode (escape_open_bracket q)) "]";
   STRCAT (explode (escape_open_bracket y)) "]"]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Indices[local]:
  split_brackets (explode (format_var (INR (q,Indices l NONE)))) =
  ["x"; STRCAT (explode (escape_open_bracket q)) "]";
   STRCAT (explode (format_num_list l)) "]"]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_format_num_list]
  \\ simp [split_bracket_def, format_annot_def,split_bracket_def]
QED

Theorem split_var_Indices_SOME[local]:
  split_brackets (explode (format_var (INR (q,Indices l (SOME r))))) =
  ["x"; STRCAT (explode (escape_open_bracket q)) "]";
   STRCAT (explode (format_num_list l)) "]";
   STRCAT (explode (escape_open_bracket r)) "]"]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_format_num_list]
  \\ simp [split_bracket_def, format_annot_def,split_bracket_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
QED

Theorem split_var_Values[local]:
  split_brackets (explode (format_var (INR (q,Values l NONE)))) =
  ["v"; STRCAT (explode (escape_open_bracket q)) "]";
   STRCAT (explode (format_int_list l)) "]"]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_format_int_list]
  \\ simp [split_bracket_def, format_annot_def]
QED

Theorem split_var_Values_SOME[local]:
  split_brackets (explode (format_var (INR (q,Values l (SOME x))))) =
  ["v"; STRCAT (explode (escape_open_bracket q)) "]";
   STRCAT (explode (format_int_list l)) "]";
   STRCAT (explode (escape_open_bracket x)) "]"]
Proof
  simp [format_var_def, format_reif_def, format_flag_def, mlstringTheory.concat_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_int_to_string]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket]
  \\ simp [Once split_brackets_def,split_bracket_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND, split_bracket_escape_open_bracket,
                  split_bracket_format_int_list]
  \\ simp [split_bracket_def, format_annot_def]
  \\ simp [Once split_brackets_def,split_bracket_def]
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
  rw [mlintTheory.int_to_string_def, mlstringTheory.implode_def]
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

Theorem concatWith_11:
  EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ strlit "") xs ∧
  EVERY (λx. ~MEM c (explode (f x)) ∧ f x ≠ strlit "") ys ∧
  INJ f UNIV UNIV ⇒
  (concatWith (strlit [c]) (MAP f xs) = concatWith (strlit [c]) (MAP f ys) ⇔ xs = ys)
Proof
  gvs [mlstringTheory.concatWith_def]
  \\ rename [‘concatWith_aux _ _ b’]
  \\ simp [EQ_IMP_THM]
  \\ qid_spec_tac ‘b’
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct
  \\ Cases_on ‘ys’ \\ gvs []
  \\ Cases_on ‘b’
  \\ gvs [mlstringTheory.concatWith_aux_def]
  \\ rpt $ disch_then strip_assume_tac
  \\ Cases_on ‘f h’
  \\ gvs [mlstringTheory.strcat_def,mlstringTheory.implode_def,
          mlstringTheory.concat_def]
  \\ rpt gen_tac
  \\ Cases_on ‘f h'’
  \\ gvs [mlstringTheory.strcat_def,mlstringTheory.implode_def,
          mlstringTheory.concat_def]
  \\ rpt $ disch_then strip_assume_tac
  \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘F’ assume_tac
  \\ ‘s = s' ⇒ h = h'’ by gvs [INJ_DEF]
  \\ Cases_on ‘xs’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
  \\ gvs [mlstringTheory.concatWith_aux_def]
  \\ gvs [mlstringTheory.strcat_def,mlstringTheory.implode_def,
          mlstringTheory.concat_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule_all str_divider_lemma
  \\ strip_tac \\ gvs []
QED

Theorem format_int_list_11[local]:
  format_int_list l = format_int_list l' ⇔ l = l'
Proof
  gvs [format_int_list_def]
  \\ irule concatWith_11
  \\ simp [INJ_DEF, int_to_string_11]
  \\ gvs [EVERY_MEM]
  \\ rw [mlintTheory.int_to_string_def,mlintTheory.num_to_chars_thm]
  \\ simp [mlstringTheory.implode_def]
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
  \\ simp [mlstringTheory.implode_def]
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
  \\ gvs [split_Sign, split_Bit, escape_open_bracket_11,
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
          split_var_Indices_SOME, escape_open_bracket_11,
          format_num_list_11, format_int_list_11]
End

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
    `?f. BIJ f proj_pb_sols proj_cp_sols` by cheat>>
    drule_at Any FINITE_BIJ_CARD>>
    impl_tac >- (
      fs[Abbr`proj_pb_sols`]>>
      irule FINITE_proj_pres>>
      irule FINITE_pres_set_list)>>
    rw[])
QED
