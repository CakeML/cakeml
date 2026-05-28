(*
  fib_heap merge implementation in Pancake
*)
Theory fib_heap_pan
Ancestors
  errorLogMonad panPtreeConversion panStatic set_sep address panSem panLang fibonacci_heap
Libs
  stringLib numLib intLib preamble helperLib

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


(*--------------------------------------------------------
Copied from bignum
---------------------------------------------------------*)

(** eval **********************************************************************)

Theorem eval_Const[simp]:
  eval s (Const w) = SOME (ValWord w)
Proof
  simp [eval_def]
QED

Theorem eval_Var_Local[simp]:
  eval s (Var Local n) = FLOOKUP s.locals n
Proof
  simp [eval_def]
QED

Theorem eval_BytesInWord[simp]:
  eval s BytesInWord = SOME (ValWord bytes_in_word)
Proof
  simp [eval_def]
QED


Theorem eval_Op_And_SOME:
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op And [x₁; x₂]) = SOME (ValWord (v₁ && v₂))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED

Theorem eval_Op_Sub_SOME:
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Sub [x₁; x₂]) = SOME (ValWord (v₁ - v₂))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED

Theorem eval_Op_Add_SOME:
  eval s x₁ = SOME (ValWord v₁) ∧
  eval s x₂ = SOME (ValWord v₂)
  ⇒
  eval s (Op Add [x₁; x₂]) = SOME (ValWord (v₁ + v₂))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED


Theorem eval_Op_Add_SOME_Const:
  eval s x₁ = SOME (ValWord v₁)
  ⇒
  eval s (Op Add [x₁; Const c]) = SOME (ValWord (v₁ + c))
Proof
  simp [eval_def, wordLangTheory.word_op_def]
QED



Theorem eval_Cmp_NotEqual_SOME:
  eval s e₁ = SOME (ValWord v₁) ∧
  eval s e₂ = SOME (ValWord v₂)
  ⇒
  eval s (Cmp NotEqual e₁ e₂) = SOME (ValWord (if v₁ ≠ v₂ then 1w else 0w))
Proof
  simp [eval_def, asmTheory.word_cmp_def]
QED


Theorem eval_Cmp_Equal_SOME_Const:
  eval s e₁ = SOME (ValWord v₁)
  ⇒
  eval s (Cmp Equal e₁ (Const c)) = SOME (ValWord (if v₁ = c then 1w else 0w))
Proof
  simp[eval_def,asmTheory.word_cmp_def]
QED





Theorem eval_Load_One_Local_SOME:
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  v ∈ s.memaddrs
  ⇒
  eval s (Load One (Var Local n)) = SOME (Val (s.memory v))
Proof
  simp [eval_def, mem_load_def]
QED


Theorem eval_Load_One_Local_Add_SOME:
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  v + off ∈ s.memaddrs
  ⇒
  eval s (Load One (Op Add [Var Local n;Const off])) =
    SOME (Val (s.memory (v + off)))
Proof
  simp [eval_def] >>
  simp [wordLangTheory.word_op_def] >>
  simp [mem_load_def]
QED



















(** evaluate ******************************************************************)

Theorem evaluate_Annot[simp]:
  evaluate (Annot s₁ s₂, s) = (NONE, s)
Proof
  simp [evaluate_def]
QED

Theorem evaluate_Seq_Annot[simp]:
  evaluate (Seq (Annot s₁ s₂) c, s) = evaluate (c, s) ∧
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
  eval s e = SOME (ValWord w) ∧ w ≠ 0w ∧ s.clock ≠ 0 ∧
  evaluate (c, dec_clock s) = (NONE, s₁) ∧
  evaluate (While e c, s₁) = (NONE, s')
  ⇒
  evaluate (While e c,s) = (NONE, s')
Proof
  rw [] >> simp [Once evaluate_def]
QED



Theorem evaluate_Dec:
  eval s e = SOME value ∧
  evaluate (prog,s with locals := s.locals |+ (v,value)) = (x,s₁)
  ⇒
  evaluate (Dec v shape e prog, s) =
    (x, s₁ with locals := res_var s₁.locals (v, FLOOKUP s.locals v))
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
  FLOOKUP s.locals dst = SOME (ValWord addr) ∧
  addr ∈ s.memaddrs ∧
  eval s e = SOME (Val v)
  ⇒
  evaluate (Store (Var Local dst) e, s) =
    (NONE, s with memory := s.memory⦇addr ↦ v⦈)
Proof
  simp [evaluate_def, flatten_def, mem_stores_def, mem_store_def]
QED



Theorem evaluate_Assign_Local:
  eval s src = SOME value ∧
  FLOOKUP s.locals dst = SOME old_value ∧
  shape_of value = shape_of old_value
  ⇒
  evaluate ((Assign Local dst src), s) = (NONE, set_var dst value s)
Proof
  simp [evaluate_def, is_valid_value_def]
QED


(*----------------------------------------------------------
 Pancake code
-----------------------------------------------------------*)

(** Copied from panPtreeConversion *)
fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_topdecs_to_ast ^code” |> concl |> rand |> rand |> rator |> rand
  end


Quote meld_pan = parse_pancake:
  fun meld (a1,a2) {
    if (a2 == 0) {
      return a1;
    }
    if (a1 == 0) {
      return a2;
    }

    var l_a1 = lds 1 (a1 + 4);
    var l_a2 = lds 1 (a2 + 4);

    st l_a1 + 5, a2;
    st a2   + 4, l_a1;
    st l_a2 + 5, a1;
    st a1   + 4, l_a2;

    var v1 = lds 1 a1;
    var v2 = lds 1 a2;

    if v1 <=+ v2 {
        return a1;
    } else {
        return a2;
    }
  }
End


Definition meld_body_def:
  meld_body =
    ^(find_term (can $ match_term “panLang$Seq _ _”) meld_pan)
End


(*
Definition one_list_def:
  one_list a [] = emp ∧
  one_list a (x::xs) = one (a,x) * one_list (a + bytes_in_word) xs
End
*)

Theorem evaluate_Annot[simp]:
  evaluate (Annot s₁ s₂, s) = (NONE, s)
Proof
  simp [evaluate_def]
QED


Theorem evaluate_Seq_Annot[simp]:
  evaluate (Seq (Annot s₁ s₂) c, s) = evaluate (c, s) ∧
  evaluate (Seq c (Annot s₁ s₂), s) = evaluate (c, s)
Proof
  simp [evaluate_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> simp []
QED

Theorem dec_clock_eq[simp]:
  (dec_clock s).locals = s.locals ∧
  (dec_clock s).memaddrs = s.memaddrs ∧
  (dec_clock s).memory = s.memory
Proof
  simp [dec_clock_def]
QED




(* Theorem evaluate_Dec: *)
(*   eval s e = SOME value ⇒ *)
(*   evaluate (Dec v shape e prog, s) = *)
(*   let (res,st) = evaluate (prog,s with locals := s.locals |+ (v,value)) in *)
(*     (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v)) *)
(* Proof *)
(*   simp [evaluate_def] *)
(* QED *)

(* Theorem evaluate_While_True_NONE: *)
(*   eval s e = SOME (ValWord w) ∧ w ≠ 0w ∧ s.clock ≠ 0 ∧ *)
(*   evaluate (c, dec_clock s) = (NONE, s₁) *)
(*   ⇒ *)
(*   (evaluate (While e c,s) = (NONE, s') ⇔ *)
(*    evaluate (While e c, s₁) = (NONE, s')) *)
(* Proof *)
(*   rw [Once evaluate_def] *)
(* QED *)
(*
Theorem and_pos_pos_thm:
  ∀xs ys zs rs x y z dm m frame s s1.
    mw_and xs ys = zs ∧ LENGTH xs ≤ LENGTH ys ∧
    LENGTH rs = LENGTH xs ∧ LENGTH xs ≤ s.clock ∧
    FLOOKUP s.locals (strlit "x_len") = SOME (Val (Word (n2w (LENGTH xs)))) ∧
    FLOOKUP s.locals (strlit "x") = SOME (Val (Word x)) ∧
    FLOOKUP s.locals (strlit "y") = SOME (Val (Word y)) ∧
    FLOOKUP s.locals (strlit "z") = SOME (Val (Word z)) ∧
    (one_list x (MAP Word xs) *
     one_list y (MAP Word ys) *
     one_list z rs *
     frame) (fun2set (s.memory, s.memaddrs))
    ⇒
    ∃m l.
      evaluate (and_pos_pos_loop,s) = (NONE,
        s with <| memory := m;
                  locals := l;
                  clock := s.clock - LENGTH xs |>) ∧
      (one_list x (MAP Word xs) *
       one_list y (MAP Word ys) *
       one_list z (MAP Word zs) *
       frame) (fun2set (m, s.memaddrs))
Proof
  simp []
  >> Induct >> rw [mw_and_def]
  >-
   (simp [and_pos_pos_loop_def]
    >> simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
    >> simp [state_component_equality])
  >> simp [and_pos_pos_loop_def]
  >> simp [Once evaluate_def,eval_def,asmTheory.word_cmp_def]
  >> simp [GSYM and_pos_pos_loop_def]
  >> ‘SUC (LENGTH xs) < dimword (:α)’ by cheat
  >> gvs []
  >> simp [Once evaluate_def, eval_def]
  >> cheat
QED
*)
(*
  SEP_R_TAC
  SEP_W_TAC
  SEP_F_TAC
*)

Theorem evaluate_if_Equal_0w_false:
  FLOOKUP s.locals l  = SOME (ValWord v) /\
  v <> 0w
  ==>
  (evaluate ((If (Cmp Equal (Var Local l) (Const 0w)) stm1 stm2), s)) =
    (evaluate (stm2,s))
Proof
  simp[evaluate_def,eval_def,asmTheory.word_cmp_def]
QED



Theorem evaluate_if_Equal_0w_true:
  FLOOKUP s.locals l = SOME (ValWord v) /\
  v = 0w
  ==>
  (evaluate ((If (Cmp Equal (Var Local l) (Const 0w)) stm1 stm2), s)) =
    (evaluate (stm1,s))
Proof
  simp[evaluate_def,eval_def,asmTheory.word_cmp_def]
QED



Theorem evaluate_if_Equal_SOME_0w:
  eval s.locals l = SOME (ValWord v) /\
  v <> 0w
  ==>
  evaluate ((If (Cmp Equal (Var Local l) (Const 0w)) stm1 stm2), s) = (SOME x,s1)
  evaluate (stm2,s) = (SOME x, s1)
Proof
  fs[evaluate
  strip_tac >>
  `eval s (Cmp Equal exp1 exp2) = SOME (ValWord (if v1 = v2 then 1w else 0w))` by
    imp_res_tac eval_Cmp_Equal_SOME >>
  simp[evaluate_def] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[]
QED


Theorem evaluate_skip:
  evaluate (Skip,s) = (NONE,s)
Proof
  simp[evaluate_def,eval_def]
QED


Theorem get_is_Word:
  is_Word(m a) ==> ?w. m a = Word w
Proof
  Cases_on `m a` >> simp[]
QED


Theorem eval_Load_One_SOME_Const:
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  (v + c) ∈ s.memaddrs
  ⇒
  eval s (Load One (Op Add [Var Local n;Const (c:'a word)])) =
  SOME (Val (s.memory (v + c)))
Proof
  simp[eval_def] >>
  simp[wordLangTheory.word_op_def,mem_load_def]
QED


Theorem eval_Load_One_SOME_Const_fupdate:
  FLOOKUP s.locals n = SOME (ValWord v) ∧
  (v + c) ∈ s.memaddrs
  ⇒
  eval (s with locals := (s.locals |+ (x,Val y)))
       (Load One (Op Add [Var Local n;Const (c:'a word)])) =
  SOME (Val (s.memory (v + c)))
Proof
  simp[eval_def] >>
  simp[FLOOKUP_SIMP] >>
  IF_CASES_TAC >> simp[] >> strip_tac
  >- (
    simp[wordLangTheory.word_op_def,mem_load_def] >>
    CASE_TAC
    simp[word_
  CASE_TAC
  simp[wordLangTheory.word_op_def,mem_load_def]
QED





Theorem meld_pan_thm:
  ∀(a1:'a word) a2 dm m s a' m'.
    fib_heap_meld (a1,a2,m,dm) = (a',m',T) /\
    FLOOKUP s.locals (strlit "a1") = SOME (Val (Word a1)) ∧
    FLOOKUP s.locals (strlit "a2") = SOME (Val (Word a2)) ∧
    dimindex(:'a) = 8 /\
    m = s.memory /\ dm = s.memaddrs
    ⇒
    ∃l.
      evaluate (meld_body,s) = (SOME (Return (ValWord a')),
        s with <| memory := m';
                  locals := l |>)
Proof
  rpt strip_tac >>
  rw[fib_heap_meld_def] >>
  simp[meld_body_def] >>
  simp[Once evaluate_def] >>
(**)
  Cases_on `a2 = 0w`
  >- (
    simp[evaluate_if_Equal_0w_true] >>
    pairarg_tac >> simp[] >>
    pop_assum mp_tac >> simp[Once evaluate_def,shape_of_def,size_of_shape_def] >>
    strip_tac >> gvs[] >>
    qexists `FEMPTY` >> simp[empty_locals_def,state_component_equality] >>
    fs[fib_heap_meld_def]
    ) >>
  simp[evaluate_if_Equal_0w_false] >>
  simp[evaluate_skip] >>
  simp[Once evaluate_def] >>
(**)
  Cases_on `a1 = 0w`
  >- (
    simp[evaluate_if_Equal_0w_true] >>
    pairarg_tac >> simp[] >>
    pop_assum mp_tac >> simp[Once evaluate_def,shape_of_def,size_of_shape_def] >>
    strip_tac >> gvs[] >>
    qexists `FEMPTY` >> simp[empty_locals_def,state_component_equality] >>
    fs[fib_heap_meld_def]
    ) >>
  simp[evaluate_if_Equal_0w_false] >>
  simp[evaluate_skip] >>
(**)
  simp[Once evaluate_def] >>
  `a1 + 4w ∈ s.memaddrs` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  simp[eval_def,FLOOKUP_SIMP] >>
  simp[wordLangTheory.word_op_def,mem_load_def] >>
  pairarg_tac >> simp[] >> pop_assum mp_tac >>
(**)
  simp[Once evaluate_def] >>
  `a2 + 4w ∈ s.memaddrs` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  simp[eval_def,FLOOKUP_SIMP] >>
  simp[wordLangTheory.word_op_def,mem_load_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> pop_assum mp_tac >>
(**)
  simp[Once evaluate_def] >>
  pairarg_tac >> simp[] >> pop_assum mp_tac >>
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  `is_Word(s.memory (a1 + 4w))` by
    (qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  drule_all get_is_Word >> strip_tac >> simp[] >>
  simp[wordLangTheory.word_op_def,mem_store_def,mem_stores_def,flatten_def] >>
  `w + 5w IN s.memaddrs` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  simp[] >>
  strip_tac >> gvs[] >>
(**)
  simp[Once evaluate_def,eval_def] >>
  pairarg_tac >> simp[] >> pop_assum mp_tac >>
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  simp[wordLangTheory.word_op_def,mem_store_def,mem_stores_def,flatten_def] >>
  strip_tac >> gvs[] >>
(**)
  simp[Once evaluate_def,eval_def] >>
  pairarg_tac >> simp[] >> pop_assum mp_tac >>
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  simp[wordLangTheory.word_op_def,mem_store_def,mem_stores_def,flatten_def] >>
  `is_Word(s.memory (a2 + 4w))` by
    (qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  drule_all get_is_Word >> strip_tac >> simp[] >>
  `w' + 5w IN s.memaddrs` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  simp[] >>
  strip_tac >> gvs[] >>
(**)
  simp[Once evaluate_def,eval_def] >>
  pairarg_tac >> simp[] >> pop_assum mp_tac >>
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  simp[wordLangTheory.word_op_def,mem_store_def,mem_stores_def,flatten_def] >>
  strip_tac >> gvs[] >>
(**)
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  simp[mem_load_def] >>
  `a1 IN s.memaddrs /\ a2 IN s.memaddrs` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> pop_assum mp_tac >>
(**)
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  simp[mem_load_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> pop_assum mp_tac >>
(**)
  simp[Once evaluate_def,eval_def,FLOOKUP_SIMP] >>
  `is_Word(s.memory⦇
    a1 + 4w ↦ Word w'; w' + 5w ↦ Word a1; a2 + 4w ↦ Word w;
    w + 5w ↦ Word a2⦈ a1) /\
   is_Word(s.memory⦇
    a1 + 4w ↦ Word w'; w' + 5w ↦ Word a1; a2 + 4w ↦ Word w;
    w + 5w ↦ Word a2⦈ a2) ` by (
    qpat_x_assum `fib_heap_meld_def (a1,a2,s.memory,s.memaddrs) = (a',m',T)`
      mp_tac >> fs[fib_heap_meld_def,read_mem_def,write_mem_def] >>
    rw[before_off_def,next_off_def,bytes_in_word_def]) >>
  imp_res_tac get_is_Word >> simp[] >>
  simp[wordLangTheory.word_op_def,mem_store_def,mem_stores_def,flatten_def] >>
  simp[evaluate_def,eval_def,asmTheory.word_cmp_def] >>
(**)
  Cases_on `w''' <=+ w''` >> simp[WORD_NOT_LOWER]
  >- (
    simp[Once evaluate_def,FLOOKUP_SIMP] >>
    simp[shape_of_def,size_of_shape_def] >>
    strip_tac >> gvs[] >>
    simp[empty_locals_def,state_component_equality,res_var_def] >>
    qpat_x_assum `fib_heap_meld (a1,a2,s.memory,s.memaddrs) = (a',m',T)` mp_tac >>
    simp[fib_heap_meld_def,read_mem_def,write_mem_def,
         before_off_def,next_off_def,bytes_in_word_def]
    ) >>
  simp[Once evaluate_def,FLOOKUP_SIMP] >>
  simp[shape_of_def,size_of_shape_def] >>
  strip_tac >> gvs[] >>
  simp[empty_locals_def,state_component_equality,res_var_def] >>
  qpat_x_assum `fib_heap_meld (a1,a2,s.memory,s.memaddrs) = (a',m',T)` mp_tac >>
  simp[fib_heap_meld_def,read_mem_def,write_mem_def,
       before_off_def,next_off_def,bytes_in_word_def]
QED


(*--------------------------------------------------------------
End to End Proof
---------------------------------------------------------------*)
Theorem end_to_end_meld:
  (fts_mem (ann_fts 0w fts1) * fts_mem (ann_fts 0w fts2) * frame)
    (fun2set(m,dm)) /\
  fib_heap_inv fh1 fts1 /\
  fib_heap_inv fh2 fts2 /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  FLOOKUP s.locals «a1» = SOME (ValWord ((head_key fts1):'a word)) ∧
  FLOOKUP s.locals «a2» = SOME (ValWord (head_key fts2)) ∧ dimindex (:α) = 8 ∧
  m = s.memory ∧ dm = s.memaddrs
  ⇒
  ∃fts' l m'. evaluate (meld_body,s) =
    (SOME (Return (ValWord (head_key fts'))),
     s with <|memory := m'; locals := l|>) /\
  (fts_mem (ann_fts 0w fts') * frame) (fun2set(m',dm)) /\
  fib_heap_inv (FUNION fh1 fh2) fts'
Proof
  rpt strip_tac >>
  qexists `fts_meld fts1 fts2` >>
  qabbrev_tac `fts' = fts_meld fts1 fts2` >>
  `fts_meld fts1 fts2 = fts'` by simp[] >>
  drule_all fts_meld >> strip_tac >> simp[] >>
  drule_all fib_heap_meld_mem_thm >> strip_tac >> simp[] >>
  drule_all meld_pan_thm >> strip_tac >> simp[] >>
  qexistsl [`l`,`m'`] >>
  gvs[]
QED








