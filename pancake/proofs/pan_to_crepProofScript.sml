(*
  Correctness proof for pan_simp
*)

open preamble
     panSemTheory crepSemTheory
     listRangeTheory
     pan_to_crepTheory


val _ = new_theory "pan_to_crepProof";

val _ = set_grammar_ancestry  ["panSem", "crepSem", "listRange", "pan_to_crep"];

Datatype:
  context =
  <| var_nums : panLang$varname |-> shape # num list;
     max_var : num|>
End

Definition with_shape_def:
  (with_shape [] _ = []) ∧
  (with_shape (sh::shs) e =
     TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))
End


(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es) of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End


Definition comp_field_def:
  (comp_field i [] es = ([Const 0w], One)) ∧
  (comp_field i (sh::shs) es =
   if i = (0:num) then (TAKE (size_of_shape sh) es, sh)
   else comp_field (i-1) shs (DROP (size_of_shape sh) es))
End

Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) =
   ([(Const c): 'a crepLang$exp], One)) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME (shape, ns) => (MAP Var ns, shape)
   | NONE => ([Const 0w], One)) /\
  (compile_exp ctxt (Label fname) = ([Label fname], One)) /\

  (compile_exp ctxt (Struct es) =
   let cexps = MAP (compile_exp ctxt) es in
   (FLAT (MAP FST cexps), Comb (MAP SND cexps))) /\
  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes => comp_field index shapes cexp) /\
  (compile_exp ctxt (Load sh e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | e::es => (load_shape (0w) (size_of_shape sh) e, sh)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case (cexp, shape) of
   | (e::es, One) => ([LoadByte e], One)
   | (_, _) => ([Const 0w], One)) /\
  (* have a check here for the shape *)
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   case cexp_heads cexps of
   | SOME es => ([Op bop es], One)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (Cmp cmp e e') =
   let ce  = FST (compile_exp ctxt e);
       ce' = FST (compile_exp ctxt e') in
   case (ce, ce') of
   | (e::es, e'::es') => ([Cmp cmp e e'], One)
   | (_, _) => ([Const 0w], One)) /\
  (compile_exp ctxt (Shift sh e n) = (* TODISC: to avoid [], and MAP [] *)
   case FST (compile_exp ctxt e) of
   | [] => ([Const 0w], One)
   | e::es => ([Shift sh e n], One))
Termination
  cheat
End

val s = ``(s:('a,'ffi) panSem$state)``

Definition code_rel_def:
  code_rel s_code t_code = ARB
End

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  code_rel s.code t.code
End

Definition flatten_def:
  (flatten (Val w) = [w]) ∧
  (flatten (Struct vs) = FLAT (MAP flatten vs))
Termination
  wf_rel_tac `measure (\v. v_size ARB v)` >>
  fs [MEM_IMP_v_size]
End

Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals =
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃sh ns vs. FLOOKUP (ctxt.var_nums) vname = SOME (sh, ns) ∧
    shape_of v = sh ∧
    OPT_MMAP (FLOOKUP t_locals) ns = SOME vs ∧ flatten v = vs
End

Theorem lookup_locals_eq_map_vars:
  ∀ns t.
  OPT_MMAP (FLOOKUP t.locals) ns =
  OPT_MMAP (eval t) (MAP Var ns)
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_MAP_o] >>
  fs [MAP_EQ_f] >> rw [] >>
  fs [crepSemTheory.eval_def]
QED

Theorem opt_mmap_eq_some:
  ∀xs f ys.
  OPT_MMAP f xs = SOME ys <=>
   MAP f xs = MAP SOME ys
Proof
  Induct >> rw [OPT_MMAP_def]
  >- metis_tac [] >>
  eq_tac >> rw [] >> fs [] >>
  cases_on ‘ys’ >> fs []
QED

Theorem length_flatten_eq_size_of_shape:
  !v.
   LENGTH (flatten v) = size_of_shape (shape_of v)
Proof
  ho_match_mp_tac flatten_ind >> rw []
  >- (cases_on ‘w’ >> fs [shape_of_def, flatten_def, panLangTheory.size_of_shape_def]) >>
  fs [shape_of_def, flatten_def, panLangTheory.size_of_shape_def] >>
  fs [LENGTH_FLAT, MAP_MAP_o] >> fs[SUM_MAP_FOLDL] >>
  match_mp_tac FOLDL_CONG >> fs []
QED


Theorem map_append_eq_drop:
  !xs ys zs f.
   MAP f xs = ys ++ zs ==>
     MAP f (DROP (LENGTH ys) xs) = zs
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs [DROP]
QED

Definition cexp_heads_simp_def:
  cexp_heads_simp es =
  if (MEM [] es) then NONE
  else SOME (MAP HD es)
End


Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

Theorem opt_mmap_mem_func:
  ∀l f n g.
  OPT_MMAP f l = SOME n ∧ MEM g l ==>
  ?m. f g = SOME m
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_mem_defined:
  !l f m e n.
   OPT_MMAP f l = SOME m ∧
   MEM e l ∧ f e = SOME n ==>
    MEM n m
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq
  >- fs [MEM] >>
  res_tac >> fs []
QED

Definition v2word_def:
  v2word (ValWord v) = Word v
End

Theorem opt_mmap_el:
  ∀l f x n.
  OPT_MMAP f l = SOME x ∧
  n < LENGTH l ==>
  f (EL n l) = SOME (EL n x)
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  cases_on ‘n’ >> fs []
QED

Theorem opt_mmap_length_eq:
  ∀l f n.
  OPT_MMAP f l = SOME n ==>
  LENGTH l = LENGTH n
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_opt_map:
  !l f n g.
  OPT_MMAP f l = SOME n ==>
  OPT_MMAP (λa. OPTION_MAP g (f a)) l = SOME (MAP g n)
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq >>
  res_tac >> fs []
QED

Theorem length_load_shape_eq_shape:
  !n a e.
   LENGTH (load_shape a n e) = n
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [] >>
  every_case_tac >> fs []
QED


Theorem mem_load_some_shape_eq:
  ∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==>
  shape_of v = sh
Proof
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==> shape_of v = sh) /\
  (∀sh adr dm (m: 'a word -> 'a word_lab) v.
   mem_loads sh adr dm m = SOME v ==> MAP shape_of v = sh)’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >> rw [panSemTheory.mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >>
  rveq >> TRY (cases_on ‘m adr’) >> fs [shape_of_def] >>
  metis_tac []
QED


Theorem mem_load_flat_rel:
  ∀sh adr s v n.
  mem_load sh adr s.memaddrs (s.memory: 'a word -> 'a word_lab) = SOME v ∧
  n < LENGTH (flatten v) ==>
  crepSem$mem_load (adr + bytes_in_word * n2w (LENGTH (TAKE n (flatten v)))) s =
  SOME (EL n (flatten v))
Proof
  rw [] >>
  qmatch_asmsub_abbrev_tac `mem_load _ adr dm m = _` >>
  ntac 2 (pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘n’,‘s’, `v`,`m`,`dm`,`adr`, `sh`] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_load sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (flatten v) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (flatten v))) /\
       (∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_loads sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (FLAT (MAP flatten v)) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (FLAT (MAP flatten v))))’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >>
  rpt strip_tac >> rveq
  >- (
   fs [panSemTheory.mem_load_def] >>
   cases_on ‘sh’ >> fs [option_case_eq] >>
   rveq
   >- (fs [flatten_def] >> rveq  >> fs [mem_load_def]) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘s’ mp_tac) >>
   fs [flatten_def, ETA_AX])
  >-  (
   fs [panSemTheory.mem_load_def] >>
   rveq >> fs [flatten_def]) >>
  fs [panSemTheory.mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >> rveq
  >- (
   fs [flatten_def] >>
   cases_on ‘n’ >> fs [EL] >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [n2w_SUC, WORD_LEFT_ADD_DISTRIB]) >>
  first_x_assum drule >>
  disch_then (qspec_then ‘s’ mp_tac) >>
  fs [] >>
  strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >>
  strip_tac >> fs [] >>
  fs [flatten_def, ETA_AX] >>
  cases_on ‘0 <= n /\ n < LENGTH (FLAT (MAP flatten vs))’ >>
  fs []
  >- fs [EL_APPEND_EQN] >>
  fs [NOT_LESS] >>
  ‘n - LENGTH (FLAT (MAP flatten vs)) < LENGTH (FLAT (MAP flatten vs'))’ by
    DECIDE_TAC >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [EL_APPEND_EQN] >>
  ‘size_of_shape (Comb l) = LENGTH (FLAT (MAP flatten vs))’ by (
    ‘mem_load (Comb l) adr s.memaddrs s.memory = SOME (Struct vs)’ by
       rw [panSemTheory.mem_load_def] >>
    drule mem_load_some_shape_eq >>
    strip_tac >> pop_assum (assume_tac o GSYM) >>
    fs [] >>
    metis_tac [GSYM length_flatten_eq_size_of_shape, flatten_def]) >>
  fs [] >>
  drule n2w_sub >>
  strip_tac >> fs [] >>
  fs [WORD_LEFT_ADD_DISTRIB] >>
  fs [GSYM WORD_NEG_RMUL]
QED


Theorem eval_load_shape_el_rel:
  !m n a t e.
  n < m ==>
  eval t (EL n (load_shape a m e)) =
  eval t (Load (Op Add [e; Const (a + bytes_in_word * n2w n)]))
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [ADD1] >>
  cases_on ‘n’ >> fs []
  >- (
   TOP_CASE_TAC >> fs [] >>
   fs [eval_def, OPT_MMAP_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   fs [wordLangTheory.word_op_def]) >>
  rw [] >>
  fs [ADD1] >>
  fs [GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB]
QED

Theorem compile_exp_val_rel:
  ∀s e v t ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  MAP (eval t) es = MAP SOME (flatten v) ∧
  LENGTH es = size_of_shape sh ∧
  shape_of v = sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, crepSemTheory.eval_def,
       panLangTheory.size_of_shape_def, shape_of_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum drule >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [lookup_locals_eq_map_vars] >>
   fs [opt_mmap_eq_some] >>
   fs [MAP_MAP_o] >>
   metis_tac [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> cheat (* should come from code_rel, define it later*))
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [MAP_MAP_o, MAP_FLAT, flatten_def] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs []
   >-  fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   rename [‘_ = SOME vs’] >>
   fs [] >>
   last_x_assum mp_tac >>
   impl_tac >-
    metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
    disch_then drule >> disch_then drule >>
    cases_on ‘compile_exp ct h’ >> fs [])
  >-
   (
   (* Field case *)
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   qpat_x_assum ‘_ = SOME (Struct _)’ kall_tac >>
   qpat_x_assum ‘compile_exp _ _ = _’ kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac
             [‘ct’,‘cexp’ ,‘sh’ , ‘es’, ‘t’, ‘s’, ‘index’, ‘vs’] >>
   Induct >> rpt gen_tac >- fs [] >>
   rewrite_tac [AND_IMP_INTRO] >>
   strip_tac >> fs [] >>
   cases_on ‘index’ >> fs []
   >- (
    fs [comp_field_def] >> rveq >>
    fs [MAP_TAKE, flatten_def] >>
    fs [panLangTheory.size_of_shape_def] >>
    fs [GSYM length_flatten_eq_size_of_shape] >>
    metis_tac [LENGTH_MAP, TAKE_LENGTH_APPEND]) >>
   fs [comp_field_def] >>
   last_x_assum drule >>
   ntac 3 (disch_then drule) >>
   fs [panLangTheory.size_of_shape_def, flatten_def] >>
   drule map_append_eq_drop >>
   fs [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   last_x_assum drule_all >>
   strip_tac >>
   fs [shape_of_def, panLangTheory.size_of_shape_def,flatten_def] >>
   rveq >> fs [] >> rveq >>
   fs [length_load_shape_eq_shape] >>
   drule mem_load_some_shape_eq >>
   strip_tac >> fs [] >>
   fs [MAP_EQ_EVERY2] >> fs [length_load_shape_eq_shape] >>
   rveq >> fs [GSYM length_flatten_eq_size_of_shape] >>
   fs [LIST_REL_EL_EQN] >>  fs [length_load_shape_eq_shape] >>
   rw [] >> fs [state_rel_def] >>
   drule mem_load_flat_rel >>
   disch_then drule >>
   strip_tac >> fs [] >>
   drule eval_load_shape_el_rel >>
   disch_then (qspecl_then [‘0w’, ‘t’,‘x0’] mp_tac) >> fs [] >>
   strip_tac >>
   fs [eval_def, OPT_MMAP_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs[EVERY_DEF] >> cases_on ‘h’ >> fs [] >>
   fs [wordLangTheory.word_op_def] >> rveq >>
   qpat_x_assum ‘mem_load _ _ = _’ (mp_tac o GSYM) >>
   strip_tac >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   cases_on ‘cexp’ >> fs [panLangTheory.size_of_shape_def, flatten_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [eval_def, state_rel_def])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   ‘~MEM [] (MAP FST (MAP (λa. compile_exp ct a) es))’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     fs [MEM_MAP] >> rveq >>
     drule opt_mmap_mem_func >>
     disch_then drule >>
     strip_tac >> fs [] >>
     rename1 ‘MEM e es’ >>
     cases_on ‘compile_exp ct e’ >> fs [] >>
     ‘shape_of m = One’ by (
       ‘MEM m ws’ by (
         drule opt_mmap_mem_defined >>
         strip_tac >> res_tac >> fs []) >>
       qpat_x_assum ‘EVERY _ ws’ mp_tac >>
       fs [EVERY_MEM] >>
       disch_then (qspec_then ‘m’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [shape_of_def]) >>
     last_x_assum drule_all >>
     strip_tac >> rveq >> rfs [panLangTheory.size_of_shape_def]) >>
     fs [] >> rveq >>
     fs [panLangTheory.size_of_shape_def, shape_of_def] >>
     fs [flatten_def, eval_def, MAP_MAP_o] >>
     ‘OPT_MMAP (λa. eval t a)
      (MAP (HD ∘ FST ∘ (λa. compile_exp ct a)) es) =
      OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es’ by (
       ho_match_mp_tac IMP_OPT_MMAP_EQ >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
       rw [] >>
       drule opt_mmap_length_eq >>
       strip_tac >> fs [] >>
       first_x_assum (qspec_then ‘EL n es’ mp_tac) >>
       impl_tac >- metis_tac [EL_MEM] >>
       drule opt_mmap_el >> fs [] >>
       disch_then drule >>
       strip_tac >> fs [] >>
       disch_then drule >>
       disch_then drule >>
       disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                                ‘SND(compile_exp ct (EL n es))’] mp_tac) >>
       fs [] >>
       strip_tac >>
       fs [EVERY_EL] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [] >>
       qpat_x_assum ‘LENGTH es = LENGTH _’ (mp_tac o GSYM) >>
       strip_tac >> fs [] >>
       drule (INST_TYPE [``:'a``|->``:'a panLang$exp``,
                         ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
       disch_then (qspec_then ‘(HD ∘ FST ∘ (λa. compile_exp ct a))’ mp_tac) >>
       strip_tac >> fs [] >>
       fs [flatten_def, v2word_def] >> rveq) >>
     fs [] >>
     ‘OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es =
      SOME (MAP v2word ws)’ by (
       ho_match_mp_tac opt_mmap_opt_map >> fs []) >>
     fs [EVERY_MAP, MAP_MAP_o] >>
     ‘∀x. (λw. case w of ValWord v6 => T | ValLabel v7 => F | Struct v3 => F) x ==>
      (λx. case v2word x of Word v2 => T | Label v3 => F) x’ by (
       rw [] >> every_case_tac >> fs [v2word_def]) >>
     drule MONO_EVERY >>
     disch_then (qspec_then ‘ws’ mp_tac) >> fs [] >>
     strip_tac >> fs [flatten_def] >>
     fs [GSYM MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘word_op op ins’ >>
     qmatch_asmsub_abbrev_tac ‘word_op op ins'’ >>
     ‘ins = ins'’ by (
       unabbrev_all_tac >> fs [MAP_EQ_EVERY2] >>
       fs [LIST_REL_EL_EQN] >>
       rw [] >>
       fs [EVERY_EL] >> (* for some reason, drule EL_MAP is not being inst. properly*)
       ‘EL n (MAP v2word ws) = v2word (EL n ws)’ by (
         match_mp_tac EL_MAP >> fs []) >>
       fs [] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [v2word_def]) >>
     unabbrev_all_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq, v_case_eq, panSemTheory.word_lab_case_eq] >> rveq >>
   (* open compile_exp *)
   fs [compile_exp_def] >>
   cases_on ‘compile_exp ct e’ >>
   cases_on ‘compile_exp ct e'’ >>
   first_x_assum drule_all >>
   first_x_assum drule_all >>
   strip_tac >> strip_tac >>
   fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [crepSemTheory.eval_def] >>
   every_case_tac >> fs [] >> EVAL_TAC) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, panSemTheory.word_lab_case_eq] >> rveq >>
  fs [compile_exp_def] >>
  cases_on ‘compile_exp ct e’ >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
  rveq >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
  fs [eval_def] >>  every_case_tac >>
  fs [panLangTheory.size_of_shape_def, shape_of_def]
QED

(* compiler for prog *)

(* Assignment *)

(*
Definition var_in_exp_def:
  (var_in_exp (Const w:'a panLang$exp) = ([]:mlstring list)) ∧
  (var_in_exp (Var v) = [v]) ∧
  (var_in_exp (Label funname) = []) ∧
  (var_in_exp (Struct es) = FLAT (MAP var_in_exp es)) ∧
  (var_in_exp (Field i e) = var_in_exp e) ∧
  (var_in_exp (Load sh e) = var_in_exp e) ∧
  (var_in_exp (LoadByte e) = var_in_exp e) ∧
  (var_in_exp (Op bop es) = FLAT (MAP var_in_exp es)) ∧
  (var_in_exp (Cmp c e1 e2) = var_in_exp e1 ++ var_in_exp e2) ∧
  (var_in_exp (Shift sh e num) = var_in_exp e)
Termination
  cheat
End
*)

Definition var_cexp_def:
  (var_cexp (Const w:'a crepLang$exp) = ([]:num list)) ∧
  (var_cexp (Var v) = [v]) ∧
  (var_cexp (Label f) = []) ∧
  (var_cexp (Load e) = var_cexp e) ∧
  (var_cexp (LoadByte e) = var_cexp e) ∧
  (var_cexp (Op bop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Cmp c e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp (Shift sh e num) = var_cexp e)
Termination
  cheat
End

Definition nested_seq_def:
  (nested_seq [] = (Skip:'a crepLang$prog)) /\
  (nested_seq [e] = e) /\
  (nested_seq (e::e'::es) = Seq e (nested_seq (e::es)))
End


Definition nested_decs_def:
  (nested_decs [] [] p = p) /\
  (nested_decs (n::ns) (e::es) p = Dec n e (nested_decs ns es p)) /\
  (nested_decs [] _ p = p) /\
  (nested_decs _ [] p = p)
End

Definition distinct_lists_def:
  distinct_lists xs ys =
    EVERY (\x. ~MEM x ys) xs
End

Definition stores_def:
  (stores ad [] a = []) /\
  (stores ad (e::es) a =
     if a = 0w then Store ad e :: stores ad es (a + byte$bytes_in_word)
     else Store (Op Add [ad; Const a]) e :: stores ad es (a + byte$bytes_in_word))
End

Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.max_var;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|var_nums := ctxt.var_nums |+ (v, (sh, nvars));
                            max_var := ctxt.max_var + size_of_shape sh |> in
    nested_seq (MAP2 Assign nvars es ++ [compile_prog nctxt p])) /\

  (compile_prog ctxt (Assign v e) =
   let (es, sh) = compile_exp ctxt e in
   case FLOOKUP ctxt.var_nums v of
    | SOME (vshp, ns) =>
      if LENGTH ns = LENGTH es
      then if distinct_lists ns (FLAT (MAP var_cexp es))
      then nested_seq (MAP2 Assign ns es)
      else let vmax = ctxt.max_var;
               temps = GENLIST (λx. vmax + SUC x) (LENGTH ns) in
           nested_decs temps es
                       (nested_seq (MAP2 Assign ns (MAP Var temps)))
      else Skip:'a crepLang$prog
    | NONE => Skip) /\
  (compile_prog ctxt (Store dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (es, sh) => nested_seq (stores ad es 0w)
    | _ => Skip) /\
  (compile_prog ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile_prog ctxt (Seq p p') =
    Seq (compile_prog ctxt p) (compile_prog ctxt p')) /\
  (compile_prog ctxt (If e p p') =
   case compile_exp ctxt e of
    | (ce::ces, _) =>
      If ce (compile_prog ctxt p) (compile_prog ctxt p')
    | _ => Skip) /\
  (compile_prog ctxt (While e p) =
   case compile_exp ctxt e of
   | (ce::ces, _) =>
     While ce (compile_prog ctxt p)
   | _ => Skip) /\
  (compile_prog ctxt Break = Break) /\
  (compile_prog ctxt Continue = Continue) /\
  (compile_prog ctxt (Call rt e es) = ARB) /\
  (compile_prog ctxt (ExtCall f v1 v2 v3 v4) = ARB) /\
  (compile_prog ctxt (Raise e) = ARB) /\
  (compile_prog ctxt (Return e) = ARB) /\
  (compile_prog ctxt Tick = Tick)
End





(* Assign example using EVAL *)

EVAL “evaluate (Assign (strlit "v") ((Const 2w):'a panLang$exp),
                (p with locals := FEMPTY |+ (strlit "v", ValWord 1w)))”;

EVAL “evaluate (Assign (strlit "x") (Struct [Field 1 (Var (strlit "x")); Field 0 (Var (strlit "x"))]),
                (p with locals := FEMPTY |+ (strlit "x", (Struct [ValWord 22w; ValWord 33w]))))”;
(*
Comb [One; One]
*)

Theorem compile_Skip:
  ^(get_goal "comp _ panLang$Skip")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, crepSemTheory.evaluate_def,
      compile_prog_def] >> rveq >> fs []
QED

Theorem compile_Dec:
  ^(get_goal "comp _ (panLang$Dec _ _ _)")
Proof
 cheat
QED

Theorem compile_Dec:
  ^(get_goal "comp _ (panLang$Assign _ _ _)")
Proof
 cheat
QED

(*


(* Add INJ, or some form of distinctiveness *)

(*
(* vs are variable names, how to include shapes *)
Definition assigned_vars_def:
  (assigned_vars Skip vs = vs) /\
  (assigned_vars (Dec v e prog) vs = ARB)
End

(*
v union (assigned_vars prog vs))
*)

(*
Definition make_ctxt_def:
  make_ctxt n [] l = l ∧
  make_ctxt n (x::xs) l = make_ctxt (n+2:num) xs (insert x n l)
End

Definition compile_def:
  compile name params body =
    let vs = fromNumSet (difference (assigned_vars body LN) (toNumSet params)) in
    let ctxt = make_ctxt 2 (params ++ vs) LN in
      FST (comp ctxt body (name,2))
End
*)

Definition make_ctxt_def:
  make_ctxt name vlist prog =  ARB
  (* assigned_vars in prog, and params but how do we get their values?
     and it will compile the program *)
End

(* type_of ``$++`` *)

Definition compile_def:
  compile name params body =
    let vs = ARB body params in
    let ctxt = make_ctxt name (params++vs) body in
    compile_prog ctxt body
End

(* var_nums : panLang$varname |-> shape # num list *)

Definition code_rel_def:
  code_rel s_code t_code =
  ∀name params prog.
   FLOOKUP s_code name = SOME (params, prog) ==>
   FLOOKUP t_code name = SOME (compile name params prog) /\
   ALL_DISTINCT (MAP FST params)
End
(* forall f. f is in domain of code, then f is also in domain of code'
  length of varnamelist for the first of code f is equal to shape
 *)

(*
 funname |-> ((varname # shape) list # ('a panLang$prog))
 funname |-> (varname list # ('a crepLang$prog))
*)
*)

(* Extra defs  *)

(*
  another version
Definition arrange_exp_def:
  arrange_exp sh e =
   TAKE (size_of_shape (HD sh)) e ::
   arrange_exp (TL sh) (DROP (size_of_shape (HD sh)) e)
End
*)


(*
  (* take this version for simplification *)
*)

(*
Definition flatten_def:
  (flatten (Val w) = [p2cw w]) ∧
  (flatten (Struct vs) = flatten' vs) ∧

  (flatten' [] = []) ∧
  (flatten' (v::vs) = flatten v ++ flatten' vs)
End
*)

(*
Definition to_struct_def:
  (to_struct One [v] = Val (c2pw v)) ∧
  (to_struct (Comb sh) vs = Struct (to_struct' sh vs)) ∧

  (to_struct' [] vs = []) ∧
  (to_struct' (sh::shs) vs =
     to_struct  sh  (TAKE (size_of_shape sh) vs) ::
    to_struct' shs (DROP (size_of_shape sh) vs))
Termination
  cheat
End
*)

(*


Theorem load_shape_simp:
  !i e c.
   load_shape 0w i e =
    MAP (\c. Load (Op Add [e; c]))
    (MAP (\n. Const (bytes_in_word * n2w n)) (GENLIST (λn. n) i))
Proof
  Induct >> rw []
  >- metis_tac [load_shape_def] >>
  once_rewrite_tac [load_shape_def] >> fs [] >>
  first_x_assum (qspec_then ‘e’ mp_tac) >>
  once_rewrite_tac [load_shape_def] >> fs [] >>
  strip_tac >> every_case_tac >> fs [] >> cheat
QED

(*
Theorem load_shape_simp:
  !i ne c t.
   n < i ==>
   eval t (EL n (load_shape 0w i e)) =
   eval t (EL n (MAP (\c. Load (Op Add [e; c]))
    (MAP (\n. Const (bytes_in_word * n2w n)) (GENLIST I i))))
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >> fs [] >>
  cases_on ‘n’ >> fs []
  >- cheat (* should be fine *) >>
  fs [EL] >>
  fs [GENLIST_CONS] >>
  fs [MAP_MAP_o] >>
  ‘n' < LENGTH (GENLIST SUC i)’ by cheat >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'c crepLang$exp``] EL_MAP) >>
   disch_then (qspec_then ‘((λc. Load (Op Add [e; c])) ∘
                            (λn. Const (bytes_in_word * n2w n)))’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [Once load_shape_def] >> fs []
  first_x_assum (qspec_then ‘e’ mp_tac) >>
  once_rewrite_tac [load_shape_def] >> fs [] >>
  strip_tac >> every_case_tac >> fs [] >> cheat
QED
*)

*)

val _ = export_theory();
