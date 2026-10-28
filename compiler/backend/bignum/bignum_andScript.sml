(*
  Bignum and operation implementation in Pancake
*)
Theory bignum_and
Ancestors
  errorLogMonad panPtreeConversion panLang panStatic multiword multiword_ext
  stackTest set_sep address backend_common wordLang integer_word wordSem panSem
Libs
  stringLib numLib intLib preamble helperLib

(* TODO Check for consistent naming *)

(* TODO
   Refactor tactics; should be stepable (i.e. modular and composed of things),
   and have good error messages. *)

(** set_sep and word helpers **************************************************)

(* TODO move to set_sep *)
Definition ones_def:
  ones a [] = emp ∧
  ones a (x::xs) = one (a,x) * ones (a + bytes_in_word) xs
End

(* TODO move to set_sep *)
Theorem ones_append:
  ∀xs ys a.
    ones a (xs ++ ys) =
    ones a xs * ones (a + n2w (LENGTH xs) * bytes_in_word) ys
Proof
  Induct
  >> rw [ones_def, SEP_CLAUSES]
  >> simp [ADD1, WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w]
  >> fs [AC STAR_ASSOC STAR_COMM]
QED

(* TODO move to set_sep *)
Theorem ones_SNOC:
  ones a (SNOC x xs) =
  ones a xs * one (a + n2w (LENGTH xs) * bytes_in_word, x)
Proof
  simp [SNOC_APPEND, ones_append, ones_def, SEP_CLAUSES]
QED

(* TODO Move somewhere better *)
Definition byte_dimindex_def:
  byte_dimindex (:α) ⇔ ∃k. dimindex(:α) = 2 ** k ∧ 3 ≤ k
End

(* TODO Move somewhere better *)
Theorem dimindex_DIV_8_lt_dimword:
  (dimindex (:α) DIV 8) < dimword (:α)
Proof
  simp [dimword_def]
  >> irule LESS_TRANS
  >> irule_at (Pos hd) DIV_LESS
  >> simp []
QED

(* TODO Move somewhere better *)
Theorem one_lt_w2n_bytes_in_word:
  8 < dimindex (:α) ∧ byte_dimindex (:α) ⇒ 1 < w2n (bytes_in_word: α word)
Proof
  rw [byte_dimindex_def, bytes_in_word_def]
  >> simp [dimindex_DIV_8_lt_dimword]
  >> qpat_x_assum ‘2 ** k = _’ $ SUBST_ALL_TAC o GSYM >> simp []
  >> ‘8n = 2 ** 3’ by simp []
  >> pop_assum SUBST_ALL_TAC
  >> DEP_REWRITE_TAC [GSYM EXP_SUB] >> simp []
  >> Cases_on ‘k = 3’ >> gvs []
QED

(* TODO Move somewhere better *)
Theorem dimword_MOD_bytes_in_word:
  byte_dimindex (:α) ⇒
  dimword (:α) MOD w2n (bytes_in_word: α word) = 0
Proof
  rw [bytes_in_word_def]
  >> ‘(dimindex (:α) DIV 8) MOD dimword (:α) = dimindex (:α) DIV 8’ by
    (simp [dimindex_DIV_8_lt_dimword])
  >> fs [byte_dimindex_def, dimword_def]
  >> ‘0 < dimindex (:α) DIV 8’ by
    (irule dividesTheory.DIV_POS >> simp []
     >> qpat_x_assum ‘2 ** k = _’ $ SUBST_ALL_TAC o GSYM >> simp [])
  >> ‘∃k. 2 ** dimindex (:α) = k * (dimindex (:α) DIV 8)’ by
    (qpat_x_assum ‘2 ** _ = dimindex (:α)’ $ SUBST_ALL_TAC o GSYM
     >> ‘8n = 2 ** 3’ by simp []
     >> pop_assum SUBST_ALL_TAC
     >> DEP_REWRITE_TAC [GSYM EXP_SUB] >> simp []
     >> qexists ‘2 ** (2 ** k − (k − 3))’
     >> rewrite_tac [GSYM EXP_ADD]
     >> DEP_REWRITE_TAC [SUB_ADD]
     >> irule LESS_EQ_TRANS
     >> irule_at (Pos hd) LESS_IMP_LESS_OR_EQ
     >> irule_at (Pos hd) LESS_2_EXP
     >> simp [])
  >> simp []
QED

(* TODO move to set_sep *)
Theorem ones_leq_dimword:
  ∀(frame: (α word # β -> bool) -> bool).
    byte_dimindex (:α) ∧ (ones a xs * frame) (fun2set (f, d)) ⇒
    LENGTH xs * w2n (bytes_in_word: α word) ≤ dimword (:α)
Proof
  rw []
  >> qabbrev_tac ‘bytes = w2n (bytes_in_word: α word)’
  >> qabbrev_tac ‘max_index = dimword (:α) DIV bytes’
  >> Cases_on ‘bytes = 0’ >- simp []
  >> ‘1 ≤ max_index’ by
    (unabbrev_all_tac >> simp [Req0 X_LE_DIV, w2n_lt, LESS_IMP_LESS_OR_EQ])
  >> simp [Req0 $ GSYM X_LE_DIV]
  >> CCONTR_TAC
  >> ‘∃ys zs. xs = ys ++ zs ∧ LENGTH ys = max_index ∧ 1 ≤ LENGTH zs’ by (
    qexistsl [‘TAKE max_index xs’, ‘DROP max_index xs’]
    >> unabbrev_all_tac >> Cases_on ‘xs’ >> gvs [])
  >> Cases_on ‘zs’ >> gvs [ones_append, ones_def]
  >> Cases_on ‘ys’ >> gvs [ones_def]
  >> qpat_x_assum ‘dimword _ DIV _ = _’ $ assume_tac o GSYM
  >> fs []
  >> qmatch_asmsub_abbrev_tac ‘one (a + more, _)’
  >> ‘a ≠ a + more’ by SEP_NEQ_TAC
  >> ‘more = 0w’ by
    (simp [Abbr ‘more’]
     >> ‘bytes_in_word = n2w bytes’ by simp [Abbr ‘bytes’]
     >> simp [word_mul_n2w]
     >> ‘bytes * (dimword (:α) DIV bytes) = dimword (:α)’ by
       (qspec_then ‘bytes’ mp_tac $ GSYM DIVISION >> simp []
        >> disch_then $ qspec_then ‘dimword (:α)’ mp_tac
        >> drule_then assume_tac dimword_MOD_bytes_in_word
        >> simp [Abbr ‘bytes’])
     >> simp [])
  >> gvs []
QED

Theorem i2w_one:
  i2w 1 = 1w
Proof
  simp [i2w_def]
QED

Theorem b2w_b2n:
  (if b2w b = 0w then 0n else 1) = b2n b
Proof
  Cases_on ‘b’ >> simp [b2w_def, b2n_def]
QED

Theorem WORD_NEG1_MUL_NOT:
  -1w * x  = ¬(x + -1w)
Proof
  simp [WORD_NOT, WORD_LEFT_ADD_DISTRIB]
QED

Theorem single_sub_0w_co[local]:
  single_sub (x: α word) 0w ci = (r, co)
  ⇒
  r = (x + -1w + b2w ci) ∧
  co = (dimword (:α) ≤ w2n x + w2n (-1w :α word) + b2n ci)
Proof
  strip_tac >> gvs [single_sub_def, single_add_def]
QED

(** Pancake semantics rewrites ************************************************)

(** misc **********************************************************************)

Theorem FLOOKUP_res_var_neq[local,simp]:
  n' ≠ n ⇒ FLOOKUP (res_var s (n, opt)) n' = FLOOKUP s n'
Proof
  Cases_on ‘opt’ >> rw [res_var_def, FLOOKUP_SIMP, DOMSUB_FLOOKUP_NEQ]
QED

Theorem FLOOKUP_res_var[simp]:
  FLOOKUP (res_var s (n, NONE))   n = NONE ∧
  FLOOKUP (res_var s (n, SOME v)) n = SOME v
Proof
  simp [res_var_def, FLOOKUP_SIMP]
QED

(*
Theorem FLOOKUP_set_var_neq[local,simp]:
  n' ≠ n ⇒ FLOOKUP (set_var n value s).locals n' = FLOOKUP s.locals n'
Proof
  simp [set_var_def, FLOOKUP_SIMP]
QED

Theorem FLOOKUP_set_var[simp]:
  FLOOKUP (set_var n value s).locals n = SOME value
Proof
  simp [set_var_def, FLOOKUP_SIMP]
QED
*)

Theorem shape_of_ValWord[simp]:
  shape_of (ValWord x) = One
Proof
  simp [shape_of_def]
QED

Theorem shape_of_RStruct_One_One[simp]:
  shape_of (RStruct [ValWord x; ValWord y]) = Comb [One; One]
Proof
  simp [shape_of_def]
QED

(*
Theorem set_var_record[simp]:
  (set_var v value s).clock = s.clock ∧
  (set_var v value s).memaddrs = s.memaddrs ∧
  (set_var v value s).memory = s.memory ∧
  (set_var v value s).globals = s.globals ∧
  (set_var v value s).code = s.code ∧
  (set_var v value s).eshapes = s.eshapes ∧
  (set_var v value s).sh_memaddrs = s.sh_memaddrs ∧
  (set_var v value s).be = s.be ∧
  (set_var v value s).ffi = s.ffi ∧
  (set_var v value s).base_addr = s.base_addr ∧
  (set_var v value s).top_addr = s.top_addr ∧
  (set_var v value s).structs = s.structs
Proof
  simp [set_var_def]
QED
*)

Theorem dec_clock_record[simp]:
  (dec_clock s).locals = s.locals ∧
  (dec_clock s).memaddrs = s.memaddrs ∧
  (dec_clock s).memory = s.memory
Proof
  simp [dec_clock_def]
QED

(** eval **********************************************************************)

Theorem eval_Const[simp]:
  eval s (Const i) = SOME (ValWord (i2w i))
Proof
  simp [eval_def]
QED

Theorem eval_RStruct_One_One:
  r = RStruct [xv; yv] ∧
  eval s x = SOME xv ∧
  eval s y = SOME yv
  ⇒
  eval s (RStruct [x; y]) = SOME r
Proof
  simp [eval_def]
QED

Theorem eval_Var_Local[simp]:
  eval s (Var Local n) = FLOOKUP s.locals n
Proof
  simp [eval_def]
QED

Theorem eval_RField_Var_Local:
  FLOOKUP s.locals n = SOME (RStruct vs) ∧
  LLOOKUP vs i = SOME r
  ⇒
  eval s (RField i (Var Local n)) = SOME r
Proof
  simp [eval_def, LLOOKUP_THM]
QED

Theorem eval_BytesInWord[simp]:
  eval s BytesInWord = SOME (ValWord bytes_in_word)
Proof
  simp [eval_def]
QED

Theorem eval_Op_And_SOME:
  r = ValWord (v₁ && v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op And [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_Sub_SOME:
  r = ValWord (v₁ - v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Sub [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_Add_SOME:
  r = ValWord (v₁ + v₂) ∧
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Add [x₁; x₂]) = SOME r
Proof
  simp [eval_def, word_op_def]
QED

Theorem eval_Op_BitwiseNot_SOME:
  r = (ValWord ¬v₁) ∧
  eval s x₁ = SOME (ValWord (v₁: α word))
  ⇒
  eval s (Op Xor [x₁; Const (-1)]) = SOME r
Proof
  simp [eval_def, word_op_def, i2w_minus_1]
QED

Theorem eval_Cmp_NotEqual_SOME:
  eval s e₁ = SOME (ValWord v₁) ∧
  eval s e₂ = SOME (ValWord v₂)
  ⇒
  eval s (Cmp NotEqual e₁ e₂) = SOME (ValWord (if v₁ ≠ v₂ then 1w else 0w))
Proof
  simp [eval_def, asmTheory.word_cmp_def]
QED

Theorem eval_Load_One_Local_SOME:
  r = (Val (s.memory v)) ∧
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  v ∈ s.memaddrs
  ⇒
  eval s (Load One (Var Local n)) = SOME r
Proof
  simp [eval_def, mem_load_def, is_wf_shape_def]
QED

(** evaluate ******************************************************************)

Theorem evaluate_Annot[simp]:
  evaluate (Annot s₁ s₂, s) = (NONE, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot_Left[simp]:
  evaluate (Seq (Annot s₁ s₂) c, s) = evaluate (c, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot_Right[simp]:
  evaluate (Seq c (Annot s₁ s₂), s) = evaluate (c, s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> simp []
QED


Theorem evaluate_Seq_assoc[simp]:
  evaluate (Seq (Seq s₁ s₂) (Seq s₃ s₄), s) =
  evaluate (Seq s₁ (Seq s₂ (Seq s₃ s₄)), s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rpt (IF_CASES_TAC >> gvs [])
QED

Theorem evaluate_While_True_NONE:
  s.clock ≠ 0 ∧
  eval s e = SOME (ValWord w) ∧
  w ≠ 0w ∧
  evaluate (c, dec_clock s) = (NONE, s₁) ∧
  evaluate (While e c, s₁) = (NONE, s')
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_While_NONE:
  eval s e = SOME (ValWord (i2w i)) ∧
  evaluate (If (Const i) (Seq Tick (Seq c (While e c))) Skip, s) = (NONE, s')
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  once_rewrite_tac [evaluate_def]
  >> qabbrev_tac ‘hidden = While e c’
  >> simp []
  >> reverse IF_CASES_TAC >> gvs []
  >- simp [evaluate_def]
  >> simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘s.clock = 0’ >> gvs []
  >> IF_CASES_TAC >> gvs []
QED

Theorem evaluate_If_NONE:
  eval s e = SOME (ValWord (i2w i)) ∧
  evaluate (If (Const i) c1 c2,s) = (NONE, s')
  ⇒
  evaluate (If e c1 c2,s) = (NONE, s')
Proof
  once_rewrite_tac [evaluate_def]
  >> rw []
QED

Theorem evaluate_Dec_NONE:
  (s₂ = s₁ with locals := res_var s₁.locals (v, FLOOKUP s.locals v)) ∧
  eval s e = SOME value ∧
  shape = shape_of value ∧
  evaluate (prog,s with locals := s.locals |+ (v,value)) = (NONE,s₁)
  ⇒
  evaluate (Dec v shape e prog, s) = (NONE, s₂)
Proof
  rw [] >> simp [Once evaluate_def]
QED

Theorem evaluate_Seq_NONE:
  evaluate (c₁, s) = (NONE, s₁) ∧
  evaluate (c₂, s₁) = (NONE, s')
  ⇒
  evaluate (Seq c₁ c₂, s) = (NONE, s')
Proof
  rw [] >> simp [evaluate_def]
QED

Theorem evaluate_Store_Local_NONE:
  s' = s with memory := s.memory⦇addr ↦ v⦈ ∧
  FLOOKUP s.locals dst = SOME (ValWord addr) ∧
  addr ∈ s.memaddrs ∧
  eval s e = SOME (Val v)
  ⇒
  evaluate (Store (Var Local dst) e, s) = (NONE, s')
Proof
  simp [evaluate_def, flatten_def, mem_stores_def, mem_store_def]
QED

Theorem evaluate_Assign_Local:
  s' = s with locals := s.locals⟨dst ↦ value⟩ ∧
  eval s src = SOME value ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of value = shape_of old_value
  ⇒
  evaluate ((Assign Local dst src), s) = (NONE, s')
Proof
  simp [evaluate_def, is_valid_value_def, set_var_def]
QED

Theorem evaluate_Primitive_AddCarry:
  s' =
    s with locals :=
      s.locals⟨
       dst ↦
       (RStruct
          [ValWord (n2w res : α word);
           ValWord (if dimword (:α) ≤ res then 1w else 0w)])⟩ ∧
  eval s l = SOME (ValWord lv) ∧
  eval s r = SOME (ValWord rv) ∧
  eval s ci = SOME (ValWord civ) ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of old_value = Comb [One; One] ∧
  res = w2n lv + w2n rv + (if civ = 0w then 0 else 1)
  ⇒
  evaluate (Primitive dst AddCarry [l; r; ci], s) = (NONE, s')
Proof
  simp [evaluate_def, pan_primop_def, isValWord_def, theValWord_def,
        is_valid_value_def, word_add_carry_def, set_var_def]
QED

Theorem evaluate_Tick_NONE:
  s' = dec_clock s
  ∧
  s.clock ≠ 0
  ⇒
  evaluate (Tick, s) = (NONE, s')
Proof
  simp [evaluate_def]
QED

(** Pancake implementation ****************************************************)

(* Pancake woes
  - Pancake parser is not very fast
  - Error messages are not very good
  - What if I don't want to return anything?
  - nested else-if?
*)

(* Following copied from panConcreteExamples*)

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_topdecs_to_ast ^code” |> concl |> rand |> rand
  end

(* TODO rewrite this slop properly *)
fun get_function name prog =
  let
    val target = ``strlit ^(stringSyntax.fromMLstring name)``
    fun field_of fld r =
      Option.map snd
        (List.find (fn (f, _) => f = fld) (snd (TypeBase.dest_record r)))
    fun is_named d =
      (case strip_comb d of
         (c, [r]) =>
           fst (dest_const c) = "Function" andalso
           (case field_of "name" r of
              SOME v => aconv v target
            | NONE => false)
       | _ => false)
      handle HOL_ERR _ => false
  in
    case List.find is_named (fst (listSyntax.dest_list prog)) of
      SOME d => d
    | NONE => raise mk_HOL_ERR "get_function" "get_function"
                      ("no function named " ^ name)
  end;

(* TODO rewrite this slop properly *)
fun get_field fld name prog =
  let
    val (_, args) = strip_comb (get_function name prog)
    val r = case args of
              [r] => r
            | _ => raise mk_HOL_ERR "get_field" "get_field" "unexpected shape"
  in
    case List.find (fn (f, _) => f = fld) (snd (TypeBase.dest_record r)) of
      SOME (_, v) => v
    | NONE => raise mk_HOL_ERR "get_field" "get_field" ("no field " ^ fld)
  end;

fun state_alpha ty =
  case dest_thy_type ty of
    {Thy = "panSem", Tyop = "state", Args = [a, _]} => a
  | _ => raise mk_HOL_ERR "bignum_and" "state_alpha" "not a panSem$state type";

Quote pan_playground = parse_pancake:
End

(* TODO go through Pancake code and see whether it could be improved with
   additions to Pancake *)
Quote and_prog = parse_pancake:
fun copy(to, from, num) {
  while num {
    var tmp = lds 1 from;
    st to, tmp;
    to   = to + @biw;
    from = from + @biw;
    num  = num - 1;
  }
  return 0;
}

(* Assumes x points to the end *)
fun mw_fix(x_len, x) {
  while x_len {
    var t1 = lds 1 x;
    if t1 { x_len = x_len - 1; } else { break; }
    x = x - @biw;
  }
  return x_len;
}

fun mw_and_pan(x_len, xs, ys, zs) {
  while x_len {
    var x = lds 1 x;
    var y = lds 1 y;
    st zs, x & y;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    x_len = x_len - 1;
  }
  return 0;
}

fun mw_and_flip_pan(x_len, x, y_len, y, z) {
  if x_len <= y_len { mw_and(x_len, x, y, z); return x_len; }
  else { mw_and(y_len, y, x, z); return y_len; }
}

fun and_neg_pos_geq(y_len, c, xs, ys, zs) {
  while y_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} y1c1 = __add_with_carry__(y, -1, c);
    var y2 = y1c1.0 ^ -1;
    st zs, x & y2;
    c = y1c1.1;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    y_len = y_len - 1;
  }
  return 0;
}

fun mwi_and_neg_pos_lt(c, x_len, xs, y_len, ys, zs) {
  var diff = y_len - x_len;
  while x_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} x1c1 = __add_with_carry__(x, -1, c);
    var x2 = x1c1.1 ^ -1;
    st zs, x2 & y;
    c = y1c1.1;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    x_len = x_len - 1;
  }
  return copy(y, x, diff);
}

fun mwi_and_neg_neg(c, d, e, x_len, xs, y_len, ys, zs) {
  while x_len {
    var x = lds 1 xs;
    var y = lds 1 ys;
    var {1,1} x1c1 = __add_with_carry__(x, -1, c);
    var {1,1} y1d1 = __add_with_carry__(y, -1, d);
    var {1,1} z1e1 = __add_with_carry__(x1c1.1 | y1d1.1, 0, e);
    st zs, z1e1.1;
    c = x1c1.2;
    d = y1d1.2;
    e = z1e1.2;
    xs = xs + @biw;
    ys = ys + @biw;
    zs = zs + @biw;
    x_len = x_len - 1;
    y_len = y_len - 1;
  }
  while y_len {
    var y = lds 1 ys;
    var {1,1} y1d1 = __add_with_carry__(y, -1, d);
    var {1,1} z1e1 = __add_with_carry__(y1d1.1, 0, e);
    st zs, z1e1.1;
    d = y1d1.2;
    e = z1e1.2;
    ys = ys + @biw;
    zs = zs + @biw;
    y_len = y_len - 1;
  }
  if e { st zs, 1; } else { st zs, 0; }
}

fun mwi_and_fused_pan(s, x_len, x, t, y_len, y, z) {
  if s {
    if t {
      if x_len <= y_len {
        var t1 = mwi_and_neg_neg_pan(0, 0, 1, x, y_len, y, z);
      } else {
        var t1 = mwi_and_neg_neg_pan(0, 0, 1, y, x_len, x, z);
      }
      var z_len = mw_fix(t1, z);
      return <1, z_len>;
    } else {
      if x_len < y_len {
        var t1 = mwi_and_neg_pos_lt_pan(0, x, x_len, y, y_len, z);
      } else {
        var t1 = mwi_and_neg_pos_geq_pan(0, y, x, x_len, z);
      }
      var z_len = mw_fix(t1, z);
      return <0, z_len>;
    }
  } else {
    if t {
      if y_len < x_len {
        var t1 = mwi_and_neg_pos_lt_pan(0, y_len, y, x_len, x, z);
      } else {
        var t1 = mwi_and_neg_pos_geq_pan(0, x, y, y_len, z);
      }
      var z_len = mw_fix(t1, z);
      return <0, z_len>;
    } else {
      var t1 = mw_and_flip_pan(x_len, x, y_len, y, z);
      var z_len = mw_fix(t1, z);
      return <0, z_len>;
    }
  }
}
End

val mw_and_pan     = get_field "body" "mw_and_pan" and_prog
val and_neg_pos_geq = get_field "body" "and_neg_pos_geq" and_prog

Definition mw_and_pan_loop_def:
  mw_and_pan_loop =
    ^(find_term (can $ match_term “panLang$While _ _”) mw_and_pan)
End

Definition and_neg_pos_geq_loop_def:
  and_neg_pos_geq_loop =
    ^(find_term (can $ match_term “panLang$While _ _”) and_neg_pos_geq)
End

(** Correctness ***************************************************************)

(*
Theorem mw_and_pan_thm:
  ∀(xs: α word list) ys zs rs s x y z frame.
    mw_and xs ys = zs ∧ LENGTH xs ≤ LENGTH ys ∧
    LENGTH rs = LENGTH xs ∧ LENGTH xs ≤ s.clock ∧
    FLOOKUP s.locals «x_len» = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals «x» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «y» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «z» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (mw_and_pan_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH xs |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp []
  >> Induct >> rw [mw_and_def]
  >-
   (simp [mw_and_pan_loop_def]
    >> simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
    >> simp [state_component_equality])
  >> simp [mw_and_pan_loop_def]
  >> rename1 ‘evaluate (While (Var Local «x_len») _, _)’
  >> irule_at (Pos hd) evaluate_While_True_NONE
  >> simp []
  >> ‘SUC (LENGTH xs) < dimword (:α)’ by
    (drule_then assume_tac $
       INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
     >> SEP_F_TAC >> simp [] >> strip_tac
     >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
     >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
     >> first_assum $ irule_at (Pos last)
     >> simp [])
  >> simp []
  >> rename1 ‘evaluate (Dec «t1» One (Load One (Var Local «x»)) _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Load_One_Local_SOME
  >> simp []
  >> fs [ones_def] >> SEP_R_TAC
  >> simp []
  >> rename1 ‘evaluate (Dec «t2» One (Load One (Var Local «y»)) _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Load_One_Local_SOME
  >> simp [FLOOKUP_SIMP]
  >> Cases_on ‘ys’ >> gvs []
  >> fs [ones_def] >> SEP_R_TAC
  >> simp []
  (**)
  >> rename1 ‘evaluate (Seq (Store (Var Local «z») _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Store_Local_NONE
  >> simp [FLOOKUP_SIMP]
  >> Cases_on ‘rs’ >> gvs []
  >> fs [ones_def] >> SEP_R_TAC >> simp []
  >> irule_at (Pos hd) eval_Op_And_SOME
  >> simp [FLOOKUP_SIMP]
  (* NOTE SEP_W_TAC seems to have an issue with this record access? *)
  >> qabbrev_tac ‘memory = s.memory’
  >> SEP_W_TAC
  >> simp [Abbr ‘memory’]
  >> rename1 ‘evaluate (Seq (Assign Local «x» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Seq (Assign Local «y» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Seq (Assign Local «z» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Assign Local «x_len» _, _)’
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Sub_SOME
  >> simp [FLOOKUP_SIMP]
  >> simp [Req0 $ GSYM mw_and_pan_loop_def]
  >> rename1 ‘evaluate (mw_and_pan_loop, _)’
  >> last_x_assum drule
  >> disch_then drule
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >> disch_then $ qspec_then ‘s'’ mp_tac
  >> simp [Abbr ‘s'’]
  >> simp [dec_clock_def]
  >> simp [n2w_SUC]
  >> simp [mw_and_def]
  >> strip_tac >> SEP_F_TAC
  >> disch_then $ qx_choosel_then [‘m’, ‘l’] assume_tac
  >> qexistsl [‘m’, ‘l’]
  >> fs [state_component_equality, ones_def, ADD1]
  >> fs [AC STAR_ASSOC STAR_COMM]
QED

Theorem and_neg_pos_geq_thm:
  ∀(ys: α word list) xs zs rs s c x y z frame.
    mwi_and_neg_pos_geq c xs ys = zs ∧ LENGTH ys ≤ LENGTH xs ∧
    LENGTH rs = LENGTH ys ∧ LENGTH ys ≤ s.clock ∧
    FLOOKUP s.locals «y_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «c» = SOME (Val (Word (b2w c))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (and_neg_pos_geq_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH ys |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp [] >> Induct >> rw [and_neg_pos_geq_loop_def]
  >- (simp [Once evaluate_def, state_component_equality])
  >> rename1 ‘ones _ (Word h::MAP Word _)’
  >> rename1 ‘evaluate (While (Var Local «y_len») _, _)’
  >> irule_at (Pos hd) evaluate_While_True_NONE
  >> simp []
  >> ‘SUC (LENGTH ys) < dimword (:α)’ by
    (drule_then mp_tac $
       INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
     >> disch_then $ qspec_then ‘Word h::MAP Word ys’ assume_tac
     >> SEP_F_TAC >> simp [] >> strip_tac
     >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
     >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
     >> first_assum $ irule_at (Pos last)
     >> simp [])
  >> simp []
  >> rename1 ‘evaluate (Dec «x» _ _ _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Load_One_Local_SOME
  >> simp []
  >> Cases_on ‘xs’ >> fs []
  >> fs [ones_def] >> SEP_R_TAC
  >> simp []
  >> rename1 ‘evaluate (Dec «y» _ _ _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Load_One_Local_SOME
  >> simp [FLOOKUP_SIMP]
  >> SEP_R_TAC
  >> simp []
  >> rename1 ‘evaluate (Dec «y1c1» _ _ _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_RStruct_One_One
  >> simp []
  >> rename1 ‘evaluate (Seq (Primitive «y1c1» AddCarry _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Primitive_AddCarry
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Dec «y2» _ _ _, _)’
  >> irule_at (Pos hd) evaluate_Dec_NONE
  >> irule_at (Pos hd) eval_Op_BitwiseNot_SOME
  >> irule_at (Pos hd) eval_RField_Var_Local_SOME_ValWord
  >> simp [FLOOKUP_SIMP, LLOOKUP_def]
  >> rename1 ‘evaluate (Seq (Store (Var Local «zs») _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Store_Local_NONE
  >> simp [FLOOKUP_SIMP]
  >> Cases_on ‘rs’ >> gvs []
  >> fs [ones_def] >> SEP_R_TAC >> simp []
  >> irule_at (Pos hd) eval_Op_And_SOME
  >> simp [FLOOKUP_SIMP]
  >> qabbrev_tac ‘memory = s.memory’
  >> SEP_W_TAC
  >> simp [Abbr ‘memory’]
  >> rename1 ‘evaluate (Seq (Assign Local «c» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_RField_Var_Local_SOME_ValWord
  >> simp [FLOOKUP_SIMP, LLOOKUP_def]
  >> rename1 ‘evaluate (Seq (Assign Local «xs» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Seq (Assign Local «ys» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Seq (Assign Local «zs» _) _, _)’
  >> irule_at (Pos hd) evaluate_Seq_NONE
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Add_SOME
  >> simp [FLOOKUP_SIMP]
  >> rename1 ‘evaluate (Assign Local «y_len» _, _)’
  >> irule_at (Pos hd) evaluate_Assign_Local
  >> irule_at (Pos hd) eval_Op_Sub_SOME
  >> simp [FLOOKUP_SIMP]
  >> simp [Req0 $ GSYM and_neg_pos_geq_loop_def]
  >> rename1 ‘evaluate (and_neg_pos_geq_loop, _)’
  >> last_x_assum drule
  >> disch_then drule
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >> disch_then $ qspec_then ‘s'’ mp_tac
  >> simp [Abbr ‘s'’]
  >> fs [GSYM b2w_ite, n2w_SUC, dec_clock_def]
  >> disch_then $ qspec_then
       ‘dimword (:α) ≤ w2n h + (dimword (:α) − 1 + if b2w c = 0w :α word then 0 else 1)’
       mp_tac
  >> simp []
  >> strip_tac >> SEP_F_TAC
  >> disch_then $ qx_choosel_then [‘m’, ‘l’] assume_tac
  >> qexistsl [‘m’, ‘l’]
  >> simp [mwi_and_neg_pos_geq_def]
  >> rpt (pairarg_tac >> gvs [])
  >> drule_then assume_tac single_sub_0w_co
  >> fs [ones_def, AC STAR_ASSOC STAR_COMM, n2w_SUC, state_component_equality]
QED
*)

(** tactics playground ********************************************************)

val _ = max_print_depth := 13;

Theorem stack_T:
  stack (T::xs) = stack xs
Proof
  simp [stack_def]
QED

Theorem stack_pull:
  x ∧ stack xs
  ⇒
  stack (x::xs)
Proof
  simp [stack_def]
QED

Theorem stack_evaluate:
  stack [evaluate (stmt, s) = (res, s')] ⇔ evaluate (stmt, s) = (res, s')
Proof
  simp [stack_def]
QED

Theorem add_rest[local]:
  (stack P ⇒ stack Q) ⇒ stack (P ++ rest) ⇒ stack (Q ++ rest)
Proof
  simp [stack_def]
QED

Theorem stack_mono[local]:
  (P ⇒ Q) ⇒ stack [P] ⇒ stack [Q]
Proof
  simp [stack_def]
QED

Theorem stack_conj[local]:
  stack ((P ∧ Q)::rest) = stack (P::Q::rest)
Proof
  simp [stack_def, CONJ_ASSOC]
QED

val ERR = mk_HOL_ERR "bignum_and";
val WRAP_EXN = wrap_exn "bignum_and";

fun stackify_imp_th th = let
  val RRULE = REWRITE_RULE
  val ADD_STACK = MATCH_MP stack_mono
  fun FLATTEN_STACK th = th |> RRULE [CONJ_ASSOC] |> RRULE [stack_conj];
  fun ADD_REST th = th |> MATCH_MP add_rest |> RRULE [APPEND]
in
  th |> ADD_STACK |> FLATTEN_STACK |> ADD_REST
    handle e => raise WRAP_EXN "stackify_imp_th" e
end

(* TODO Add comments *)
(* TODO make LLM look over it *)

(* TODO Add more hints/make it easy to step through *)

(* todo add tactic to turn head into subgoal *)

(* Adds the assumptions asl to thl. Useful for rewriters/simplifiers that make
   use of the assumptions. *)
fun add_asms asl thl = map ASSUME asl @ thl

val it = stackify_imp_th evaluate_Dec_NONE

val (stack_tm, mk_stack, dest_stack, is_stack) = syntax_fns1 "stackTest" "stack"
fun is_stack_cons tm = is_stack tm andalso listSyntax.is_cons (dest_stack tm)
val (eval_tm, mk_eval, dest_eval, is_eval) = syntax_fns2 "panSem" "eval"
val (evaluate_tm, mk_evaluate, dest_evaluate, is_evaluate) = syntax_fns1 "panSem" "evaluate"
val (While_tm, mk_While, dest_While, is_While) = syntax_fns2 "panLang" "While"
val (If_tm, mk_If, dest_If, is_If) = syntax_fns3 "panLang" "If"
val (Const_tm, mk_Const, dest_Const, is_Const) = syntax_fns1 "panLang" "Const"

(* Returns i2w tm ≠ 0w, given that tm is of type word. *)
fun mk_i2w_neq_0w ty tm = let
  val w = integer_wordSyntax.mk_i2w (tm, ty)
    handle e => raise WRAP_EXN "mk_i2w_neq_0w" e
  val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, ty)
in mk_neg (mk_eq (w, zero)) end

(* Returns whether tm is of form evaluate (While ..., ...). *)
fun is_evaluate_While tm =
  if not $ is_evaluate tm then false
  else is_While $ fst $ dest_pair $ dest_evaluate tm

(* Returns whether tm is of form evaluate (If ..., ...). *)
fun is_evaluate_If tm =
  if not $ is_evaluate tm then false
  else is_If $ fst $ dest_pair $ dest_evaluate tm

(* Returns w if tm is of the form (If (Const w) ... , ...)*)
fun dest_evaluate_If_Const tm =
  let val (cond, _, _,) = dest_If $ fst $ dest_pair $ dest_evaluate tm in
    dest_Const cond end

(* Returns whether tm is of form evaluate (If (Const ...) ... , ...). *)
val is_evaluate_If_Const = can $ dest_evaluate_If_Const

(* Applies a conversion to the first instance of stack in the top-level
   conjuncts (modulo leading quantifiers) *)
fun STACK_CONV c =
  let
    fun search tm =
      if is_stack tm then c tm
      else if is_conj tm then
        let val (l, _) = dest_conj tm in
          if is_stack l then LAND_CONV c tm
          else RAND_CONV search tm
        end
      else raise ERR "STACK_CONV" "no stack conjunct found"
  in
    STRIP_QUANT_CONV search
  end

(* Applies a conversion to the head of the first instance of stack
   in the top-level conjuncts (modulo leading quantifiers) *)
fun STACK_HEAD_CONV conv =
  let
    fun head_conv tm =
      if is_stack_cons tm then RAND_CONV (LAND_CONV conv) tm
      else raise ERR "STACK_HEAD_CONV" "stack is empty"
  in
    STACK_CONV head_conv
  end

(* Theorems of the form {evaluate,eval} ... = ...  *)
val (step_eq_thl: thm list) =
  [eval_Var_Local, evaluate_Seq_Annot_Left, eval_Const, eval_BytesInWord]
val _ =
  if not (all (is_eq o concl) step_eq_thl) then
    raise ERR "assertion failure" "non-equality found in step_eq_thl"

(* Theorems of the form stack (...) ⇒ stack ({evaluate,eval} ...) *)
val (step_imp_thl: thm list) =
  [evaluate_Dec_NONE, eval_Load_One_Local_SOME, eval_RStruct_One_One,
   evaluate_Primitive_AddCarry, evaluate_Seq_NONE, eval_Op_BitwiseNot_SOME,
   eval_RField_Var_Local, evaluate_Store_Local_NONE,
   eval_Op_And_SOME, evaluate_Assign_Local, eval_Op_Add_SOME, eval_Op_Sub_SOME,
   evaluate_Tick_NONE]
  |> map stackify_imp_th

(* Given ⊢ A = B, returns A. *)
fun eq_thm_lhs thm = thm |> concl |> dest_eq |> fst

(* Given ⊢ A ⇒ B, returns B. *)
fun imp_thm_rhs thm = thm |> concl |> dest_imp |> snd

(* Rewrites with the theorems in step_eq_thl at the stack head, failing if
   the goal remains unchanged. *)
val step_eq_tac : tactic =
  CHANGED_TAC (CONV_TAC (STACK_HEAD_CONV (REWRITE_CONV step_eq_thl)))
    handle e => raise WRAP_EXN "step_eq_tac" e

(* Returns the first stack term in a list of terms. *)
fun first_stack tms =
  Lib.first is_stack tms
  handle e => raise WRAP_EXN "first_stack: could not find stack term" e

(* Given a stack term, returns the appropriate irule instantiation using an
   appropriate theorem from thl. *)
fun stack_imp_tac thl (stack: term) = let
  val candidates =
    filter (fn thm => can (match_term (imp_thm_rhs thm)) stack) thl
  val count = length candidates
  val winner =
    if count = 1 then hd candidates
    else if count = 0 then
      raise ERR "stack_imp_tac" "no matching stack theorem found."
    else raise ERR "stack_imp_tac" "found multiple candidate stack theorems."
in irule_at (Pos first_stack) winner end

val step_imp_tac = stack_imp_tac step_imp_thl

(* Unfolds evaluate (While ...) = ... at the head. *)
val step_While = irule_at (Pos first_stack) (stackify_imp_th evaluate_While_NONE)

(* Reduces evaluate (If ...) = ... at the head to
   evaluate (If (Const ...) ...) = ... . This tactic should not be used on
   If with a Const condition, as it will not lead to progress in the proof. *)
val step_If = irule_at (Pos first_stack) (stackify_imp_th evaluate_If_NONE)

(* Finds the "redex" of the stack (lhs of wants at the top of the stack) . *)
fun find_redex tm = let
  val stack = find_term is_stack tm
    handle HOL_ERR _ => raise ERR "find_redex" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "find_redex" "stack is empty"
in
  lhs head handle HOL_ERR _ => raise ERR "find_redex" "not an equality"
end

(* For use in step_If_Const *)
Theorem evaluate_If_Const_T:
  (i2w i ≠ (0w :α word) ⇔ T)
  ⇒
  evaluate (c1, s: (α, γ) state) = (NONE, s')
  ⇒
  evaluate (If (Const i) c1 c2,s) = (NONE, s')
Proof
  simp [evaluate_def]
QED

(* For use in step_If_Const *)
Theorem evaluate_If_Const_F:
  (i2w i ≠ (0w :α word) ⇔ F)
  ⇒
  evaluate (c2, s: (α, γ) state) = (NONE, s')
  ⇒
  evaluate (If (Const i) c1 c2,s) = (NONE, s')
Proof
  simp [evaluate_def]
QED

(* Given a head of the form  evaluate (If (Const w) ...) = ..., tries to
   reduce w ≠ 0w to T or F and choose the branch accordingly. *)
val step_If_Const : tactic = fn (g as (asl, w)) => fn ctxt => let
  val redex = find_redex w
  val word_ty = state_alpha $ el 2 $ snd $ dest_type $ type_of redex
  val cond = mk_i2w_neq_0w word_ty (dest_evaluate_If_Const redex)
    handle e => raise WRAP_EXN "step_If_Const" e
  val thl = [i2w_pos, n2w_11, LESS_MOD, ZERO_MOD, ZERO_LT_dimword]
  val reduced_th = QCONV (SIMP_CONV arith_ss (add_asms asl thl)) cond
  val reduced = rhs $ concl $ reduced_th
in
  if aconv reduced boolSyntax.T then
    irule_at (Pos first_stack)
      (stackify_imp_th $ MATCH_MP evaluate_If_Const_T reduced_th) g ctxt
  else if aconv reduced boolSyntax.F then
    irule_at (Pos first_stack)
      (stackify_imp_th $ MATCH_MP evaluate_If_Const_F reduced_th) g ctxt
  else raise ERR "step_If_Const" $
    concat [
      "failed to reduce condition ", term_to_string cond, " to a boolean.\n",
      "Hint: no assumption determines this; add one and try again.\n",
      "debug: reduced_th: ", thm_to_string reduced_th
      ]
end

(* Reduces a goal that contains stack (({evaluate,eval} ... = ...)::...).
   unfold indicates whether while-loops should be unfolded. *)
fun step_core unfold : tactic = fn (g as (asl, w)) => fn ctxt => let
  val stack = find_term is_stack w
    handle HOL_ERR _ => raise ERR "step_core" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "step_core" "stack is empty"
  val _ =
    if not (is_eq head) then
      raise ERR "step_core" "stack head is not an equality"
  val redex = lhs head
  val matches_eq =
    exists (fn thm => can (match_term (eq_thm_lhs thm)) redex) step_eq_thl
in
  (if is_evaluate_While redex then
     if unfold then step_While else
       raise ERR "step_core"
         "unfolding while-loops disabled. Hint: use the step tactic."
   else if is_evaluate_If_Const redex then step_If_Const
   else if is_evaluate_If redex then step_If
   else if matches_eq then
     step_eq_tac handle e => raise WRAP_EXN "step_core" e
   else
     step_imp_tac stack handle e => raise WRAP_EXN "step_core" e) g ctxt
end

(* step tactic for the user. Unfolds while-loops. *)
val step = step_core true

(* Rewrites stack (T::rest) to stack rest. Fails if the rewrite does not apply. *)
val head_pop_T : tactic = fn (g as (asl, w)) => fn ctxt =>
  (CHANGED_TAC (CONV_TAC (STACK_CONV (REWRITE_CONV [stack_T])))) g ctxt

(* Rewrites the head of the stack using the assumptions and the passed
   theorem list. *)
(*
fun head_asm_rewrite thl : tactic = fn (g as (asl, w)) =>
    CONV_TAC (STACK_HEAD_CONV (ASM_REWRITE_CONV asl thl)) g
*)

(* Simplifies the head of the stack using the assumptions, the simpset and
   the passed theorem list. *)
fun head_asm_simp ss thl : tactic = fn (g as (asl, w)) => fn ctxt =>
  CONV_TAC (STACK_HEAD_CONV (SIMP_CONV ss (add_asms asl thl))) g ctxt


Theorem n2w_i2w_eq:
  &n = i ⇒ n2w n = i2w i
Proof
  rw [] >> simp [i2w_pos]
QED

(* Theorems of the form stack (...) ⇒ stack (...) for reducing side conditions. *)
val (side_imp_thl: thm list) = [n2w_i2w_eq] |> map stackify_imp_th

val side_imp_tac : tactic = let
  val side_imp_tac_core = stack_imp_tac side_imp_thl
in
  fn (g as (asl, w)) => fn ctxt => let
    val stack = find_term is_stack w
      handle HOL_ERR _ => raise ERR "side_imp_tac" "could not find stack"
    in
    (side_imp_tac_core stack handle e => raise WRAP_EXN "side_imp_tac" e) g ctxt
  end
end

(* "cleaned up" tactic *)

(* Given a term of the form ∃x₁ ... xₙ. t₁ ∧ ... ∧ tₙ, returns
   ([x₁, ..., xₙ], [t₁, ..., tₙ]). *)
fun dest_exists_conj tm =
  let val (evars, rest) = strip_exists tm
  in (evars, strip_conj rest) end

(* Given a list of terms, finds the stack and returns its head. *)
fun get_stack_head tms = let
  val stack = Lib.first is_stack tms
    handle HOL_ERR _ => raise ERR "get_stack_head" "could not find stack"
  val (head, _) = listSyntax.dest_cons (rand stack)
    handle HOL_ERR _ => raise ERR "get_stack_head" "stack is empty"
in head end

(* Returns the first variable from evars that can be unwound using tm.
   This function mirrors check_var from Unwind.sml. *)
fun find_unwind_var (evars: term list) (tm: term) =
  if is_eq tm then let
    val (arg1, arg2) = dest_eq tm in
      if op_mem aconv arg1 (free_vars arg2) orelse
         op_mem aconv arg2 (free_vars arg1)
      then raise ERR "find_unwind_var" "duplicate values"
      else
        (Lib.first (fn e => aconv arg1 e orelse aconv arg2 e) evars
           handle HOL_ERR _ => raise ERR "find_unwind_var" "no value")
    end
  else if is_neg tm andalso List.exists (aconv (dest_neg tm)) evars then
    Lib.first (aconv (dest_neg tm)) evars
  else
    (Lib.first (aconv tm) evars
       handle HOL_ERR _ => raise ERR "find_unwind_var" "no value")

(* Applies UNWIND_EXISTS_CONV to the first (top-level) existential quantifier
   that is equal to tm. *)
fun UNWIND_EXISTS_VAR_CONV v tm =
  if is_exists tm then let
    val (bv, _) = dest_exists tm in
      if aconv bv v then Unwind.UNWIND_EXISTS_CONV tm
      else QUANT_CONV (UNWIND_EXISTS_VAR_CONV v) tm
    end
  else ALL_CONV tm

(* Eliminates existentials that are restricted to a point at the head of the
   stack. *)
val head_unwind : tactic = fn (g as (_, w)) => fn ctxt =>
  let
    val (evars, conjs) = dest_exists_conj w
    val head = get_stack_head conjs
      handle e => raise WRAP_EXN "head_unwind" e
    val target = find_unwind_var evars head
      handle e => raise WRAP_EXN "head_unwind" e
  in
    (irule_at (Pos first_stack) stack_pull
     >> CONV_TAC (UNWIND_EXISTS_VAR_CONV target)) g ctxt
  end

(* Variant of simp that only applies to the stack head for the use in user
   proof-scripts. Makes sure to reduce stack (T::...) and apply unwind for
   existentials. *)
val hsimp : thm list -> tactic = let
  val hsimp_core = head_asm_simp (boss_ss())
in
  fn thl => fn g => fn ctxt =>
    (hsimp_core thl >> TRY (head_pop_T ORELSE head_unwind)) g ctxt
end

(* Simplifier used to automatically discharge side-conditions.
   Since it does not fail, it is useful for debugging side. *)
val side_simp =
  head_asm_simp arith_ss [
    v_11, word_lab_11, mlstringTheory.mlstring_11, list_11, NOT_CONS_NIL, CHR_11,
    shape_of_ValWord, shape_of_RStruct_One_One,
    dec_clock_record, panSemTheory.state_accfupds,
    FLOOKUP_UPDATE, (* FLOOKUP_set_var_neq, FLOOKUP_set_var, *) LLOOKUP_def,
  ]

(* Attempts to prove side-conditions produced by step. Fails if a
   side-condition cannot be discharged. *)
val side : tactic = fn g => fn ctxt =>
  (side_simp >> TRY side_imp_tac >> (head_pop_T ORELSE head_unwind)) g ctxt
    handle HOL_ERR _ => raise ERR "side" "failed to discharge side-condition"

(* Tries to apply step or side. *)
fun step_or_side_core unfold : tactic = fn (g as (_, w)) => fn ctxt => let
  val is_step =
    case total find_redex w of
      NONE => false
    | SOME redex => is_evaluate redex orelse is_eval redex
in
  (if is_step then step_core unfold else side) g ctxt
    handle e => raise WRAP_EXN "step_or_side_core" e
end

(* Tries to apply step or side, including unfolding of loops. *)
val step_or_side = step_or_side_core true
    handle e => raise WRAP_EXN "step_or_side" e

(* Apply tactic one or more times. *)
fun rpt1 tac : tactic = tac >> rpt tac

(* Takes as many steps as possible, except unfold while-loops. *)
val walk : tactic = fn (g as (asl, w)) => fn ctxt =>
  (rpt1 (step_or_side_core false)) g ctxt handle e => raise WRAP_EXN "walk" e

(*
val g as (asl, w) = top_goal ();
*)

val _ = max_print_depth := ~1

Theorem and_neg_pos_geq_thm:
  ∀(ys: α word list) xs zs rs s c x y z frame.
    mwi_and_neg_pos_geq c xs ys = zs ∧ LENGTH ys ≤ LENGTH xs ∧
    LENGTH rs = LENGTH ys ∧ LENGTH ys ≤ s.clock ∧
    FLOOKUP s.locals «y_len» = SOME (Val (Word (n2w (LENGTH ys)))) ∧
    FLOOKUP s.locals «c» = SOME (Val (Word (b2w c))) ∧
    FLOOKUP s.locals «xs» = SOME (Val (Word x)) ∧
    FLOOKUP s.locals «ys» = SOME (Val (Word y)) ∧
    FLOOKUP s.locals «zs» = SOME (Val (Word z)) ∧
    (ones x (MAP Word xs) *
     ones y (MAP Word ys) *
     ones z rs *
     frame) (fun2set (s.memory, s.memaddrs)) ∧
    byte_dimindex (:α) ∧ 8 < dimindex (:α)
    ⇒
    ∃m l.
      evaluate (and_neg_pos_geq_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH ys |>) ∧
      (ones x (MAP Word xs) *
       ones y (MAP Word ys) *
       ones z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp [] >> Induct >> rw [and_neg_pos_geq_loop_def]
  >- (simp [Once evaluate_def, state_component_equality, i2w_def])
  >> rename1 ‘ones _ (Word h::MAP Word _)’
  >> once_rewrite_tac [GSYM stack_evaluate]
  >> step >> walk
  >> ‘SUC (LENGTH ys) < dimword (:α)’ by
    (drule_then mp_tac $
       INST_TYPE [“:β” |-> “:α word_lab”] ones_leq_dimword
     >> disch_then $ qspec_then ‘Word h::MAP Word ys’ assume_tac
     >> SEP_F_TAC >> simp [] >> strip_tac
     >> drule_all_then assume_tac one_lt_w2n_bytes_in_word
     >> irule_at (Pos hd) LESS_LESS_EQ_TRANS
     >> first_assum $ irule_at (Pos last)
     >> simp [])
  >> walk
  >> Cases_on ‘xs’ >> fs [ones_def] >> SEP_R_TAC
  >> walk
  >> hsimp [] >> SEP_R_TAC >> hsimp []
  >> walk
  >> Cases_on ‘rs’ >> gvs []
  >> fs [ones_def] >> SEP_R_TAC >> hsimp []
  >> step_or_side
  >> walk
  >> rewrite_tac [stack_evaluate]
  >> simp [Req0 $ GSYM and_neg_pos_geq_loop_def]
  >> rename1 ‘evaluate (and_neg_pos_geq_loop, _)’
  >> last_x_assum drule
  >> disch_then drule
  >> qmatch_goalsub_abbrev_tac ‘evaluate (_, s')’
  >> disch_then $ qspec_then ‘s'’ mp_tac
  >> simp [Abbr ‘s'’]
  >> qabbrev_tac ‘memory = s.memory’
  >> SEP_W_TAC
  >> simp [Abbr ‘memory’]
  >> fs [GSYM b2w_ite, dec_clock_def, FLOOKUP_SIMP, i2w_one, n2w_SUC]
  >> qmatch_goalsub_abbrev_tac ‘b2w (dimword (:α) ≤ r)’
  >> disch_then $ qspec_then ‘dimword (:α) ≤ r’ mp_tac
  >> simp []
  >> strip_tac >> SEP_F_TAC
  >> disch_then $ qx_choosel_then [‘m’, ‘l’] assume_tac
  >> qexistsl [‘m’, ‘l’]
  >> simp [mwi_and_neg_pos_geq_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘single_sub _ 0w _ = (y₂, c₁)’
  >> have ‘(-1w * (n2w r + 1w) = ¬y₂) ∧ (dimword (:α) ≤ r ⇔ c₁)’
  >- (
    drule_then assume_tac single_sub_0w_co
    >> simp [Abbr ‘r’, i2w_minus_1, w2n_minus1, b2w_b2n, GSYM word_add_n2w,
             GSYM b2w_def, WORD_NEG1_MUL_NOT]
  )
  >> fs [ones_def, AC STAR_ASSOC STAR_COMM, n2w_SUC, state_component_equality]
QED
