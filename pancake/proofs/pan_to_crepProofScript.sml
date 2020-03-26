(*
  Correctness proof for pan_simp
*)

open preamble
     pan_to_crepTheory
     panSemTheory crepSemTheory
     listRangeTheory


val _ = new_theory "pan_to_crepProof";

val _ = set_grammar_ancestry ["pan_to_crep", "panSem", "crepSem", "listRange"];

Datatype:
  context =
  <| var_nums : panLang$varname |-> shape # num list;
     dec_nums : panLang$varname |-> shape # num list|>
End

(* following this style to avoid using HD *)
Definition with_shape_def:
  (with_shape [] _ = []) ∧
  (with_shape (sh::shs) e =
     TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))
End


(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es)  of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End

Definition load_shape_def:
  (load_shape One e = [Load e]) /\
  (load_shape (Comb shp) e = load_shapes shp e) /\

  (load_shapes [] _ =  []) /\
  (load_shapes (sh::shs) e =
   load_shape sh e ++ load_shapes shs (Op Add [e; Const byte$bytes_in_word]))
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
   | Comb shapes =>
     if index < LENGTH shapes then
     (EL index (with_shape shapes cexp), EL index shapes)
     else ([Const 0w], One)) /\


  (compile_exp ctxt (Load sh e) =
   let (cexp, shape) = compile_exp ctxt e in
   case (cexp, shape) of
   | (e::es, One) => (load_shape sh e, sh)
   | (_, _) => ([Const 0w], One)) /\ (* TODISC: what shape should we emit? *)
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case (cexp, shape) of
   | (e::es, One) => ([LoadByte e], One)
   | (_, _) => ([Const 0w], One)) /\
  (* have a check here for the shape *)
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   case cexp_heads cexps of
   | SOME (e::es) => ([Op bop (e::es)], One) (* TODISC: to avoid [], and MAP [] *)
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


(* assoc? *)
Definition list_seq_def:
  (list_seq [] = (Skip:'a crepLang$prog)) /\
  (list_seq [e] = e) /\
  (list_seq (e::e'::es) = Seq e (list_seq (e::es)))
End


Definition store_cexps_def:
  (store_cexps [] _ = []) /\
  (store_cexps (e::es) ad =
   [Store ad e] ++
   store_cexps es (Op Add [ad; Const byte$bytes_in_word]))
End

(*
  look into the context for v, if v is already an assigned variable,
  take it and store it in dec_nums, see the last conunter in the domain of
  context, and rewrite v to store shape + these numbers *)

Definition declare_ctxt:
  declare_ctxt ctxt v es shape = ARB
End

Definition exp_vars_def:
  (exp_vars (Const w:'a panLang$exp) = ([]:mlstring list)) ∧
  (exp_vars (Var v) = [v]) ∧
  (exp_vars (Label funname) = []) ∧
  (exp_vars (Struct es) = FLAT (MAP exp_vars es)) ∧
  (exp_vars (Field i e) = exp_vars e) ∧
  (exp_vars (Load sh e) = exp_vars e) ∧
  (exp_vars (LoadByte e) = exp_vars e) ∧
  (exp_vars (Op bop es) = FLAT (MAP exp_vars es)) ∧
  (exp_vars (Cmp c e1 e2) = exp_vars e1 ++ exp_vars e2) ∧
  (exp_vars (Shift sh e num) = exp_vars e)
Termination
  cheat
End

(* TO fix ARB later *)
Definition temp_vars_def:
  temp_vars ctxt n =
    [list_max (ARB (IMAGE SND (FRANGE (ctxt.var_nums)))) .. n]
End

Definition compile_prog_def:
  (compile_prog ctxt (Assign vname e) =
   case (FLOOKUP ctxt.var_nums vname, compile_exp ctxt e) of
   | SOME (One, n::ns), (cexp::cexps, One) => Assign n cexp
   | SOME (Comb shapes, ns), (cexps, Comb shapes') =>
     if LENGTH ns = LENGTH cexps
     then (
       if (MEM vname (exp_vars e)) then
       ARB
       else list_seq (MAP2 Assign ns cexps))
     else Skip
   | _ => Skip)
End

val s = ``(s:('a,'ffi) panSem$state)``

Definition code_rel_def:
  code_rel s_code t_code = ARB
End

(* crep-to-pan word_lab cast *)
Definition c2pw_def:
  c2pw (n:'a crepSem$word_lab) =
  case n of
  | Word w => (Word w:'a panSem$word_lab)
  | Label lab => Label lab
End

Definition mcast_def:
  mcast (m:'a word -> 'a crepSem$word_lab) = (λa. c2pw (m a))
End

(* pan-to-crep word_lab cast *)
Definition p2cw_def:
  p2cw (n:'a panSem$word_lab) =
  case n of
  | Word w => (Word w:'a crepSem$word_lab)
  | Label lab => Label lab
End

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = mcast t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  code_rel s.code t.code
End

(*
Definition flat_struct_def:
  flat_struct vs =
   FLAT (MAP (λv. case v of
         | Val w => [p2cw w]
         | Struct ns => flat_struct ns) vs)
Termination
  cheat
End

Definition flatten_def:
  (flatten (Val w) = [p2cw w]) ∧
  (flatten (Struct vs) = flat_struct vs)
End
*)

Definition flatten_def:
  (flatten (Val w) = [p2cw w]) ∧
  (flatten (Struct vs) = FLAT (MAP flatten vs))
Termination
  cheat
End


Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals =
  (∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃sh ns vs. FLOOKUP (ctxt.var_nums) vname = SOME (sh, ns) ∧
    shape_of v = sh /\ size_of_shape sh = LENGTH ns /\
    OPT_MMAP (FLOOKUP t_locals) ns = SOME vs ∧ flatten v = vs)
End


Definition wf_ctxt_def:
  wf_ctxt ctxt s_locals =
  (∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃sh ns. FLOOKUP (ctxt.var_nums) vname = SOME (sh, ns) ∧
    shape_of v = sh /\ size_of_shape sh = LENGTH ns)
End

Theorem locals_rel_imp_wf_ctxt:
  locals_rel ctxt s_locals t_locals ==>
   wf_ctxt ctxt s_locals
Proof
  rw [locals_rel_def, wf_ctxt_def] >>
  metis_tac []
QED

Definition assigned_vars_def:
  assigned_vars p l = ARB
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
      assigned_vars prog FEMPTY ⊆ FDOM (ctxt.var_nums) ⇒
      ∃res1 t1. evaluate (compile_prog ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Return (ARB v)) (* many return values *)


       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt s1.locals t1.locals /\
                       code_rel ctxt s1.code t1.code


       | SOME Continue => res1 = SOME Continue /\
                       locals_rel ctxt s1.locals t1.locals /\
                       code_rel ctxt s1.code t1.code
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | SOME (Exception v) => res1 = SOME (Exception (ARB v))
       | _ => F``

local
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem opt_mmap_length_eq:
  ∀l f n.
  OPT_MMAP f l = SOME n ==>
  LENGTH l = LENGTH n
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

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

Theorem mem_load_some_shape_eq:
  ∀sh adr dm m v.
  mem_load sh adr dm m = SOME v ==>
  shape_of v = sh
Proof
  cheat
  (*
  ho_match_mp_tac panLangTheory.shape_induction *)
  (* for later *)
  (*
  Induct >> rw [panSemTheory.mem_load_def]
  >- (cases_on ‘m adr’ >> fs [shape_of_def]) >>
  fs [option_case_eq] >> rveq >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘vs’, ‘m’, ‘dm’, ‘adr’, ‘l’] >>
  Induct >> rw [panSemTheory.mem_load_def]
  >- fs [shape_of_def] >>
  fs [option_case_eq] >> rveq >>
  fs [shape_of_def] >>
  conj_tac >> cheat *)
QED


Theorem load_shape_length_shape_eq:
  LENGTH (load_shape sh (e:'a crepLang$exp)) = size_of_shape sh
Proof
  cheat
  (* ho_match_mp_tac panLangTheory.shape_induction *)
QED

Theorem with_shape_el_len:
  ∀sh i es.
  i < LENGTH sh ∧
  size_of_shape (Comb sh) = LENGTH es ==>
  LENGTH (EL i (with_shape sh es)) = size_of_shape (EL i sh)
Proof
  Induct >> rw [] >>
  fs [Once with_shape_def] >>
  cases_on ‘i’ >> fs[]
  >- fs [size_of_shape_def] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  disch_then (qspec_then ‘DROP (size_of_shape h) es’ mp_tac) >>
  impl_tac
  >- fs [size_of_shape_def] >>
  strip_tac >>
  fs [] >>
  once_rewrite_tac [with_shape_def] >>
  metis_tac []
QED


Theorem compile_exp_length_rel:
  ∀s e v ct cexp sh.
  panSem$eval s e = SOME v ∧
  wf_ctxt ct s.locals ∧
  compile_exp ct e = (cexp, sh) ==>
  LENGTH cexp = size_of_shape sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rw []
  >- (
   fs [shape_of_def,compile_exp_def] >> rveq >>
   fs [size_of_shape_def])
  >- (
   rename1 ‘eval s (Var vname)’ >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [wf_ctxt_def] >>
   first_x_assum (qspecl_then [‘vname’, ‘v’] mp_tac) >>
   fs [] >> strip_tac >> fs [compile_exp_def] >>
   rveq >> fs [])
  >- (
   fs [compile_exp_def] >> rveq >>
   fs[size_of_shape_def])
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >>
   rveq >> fs [compile_exp_def] >> rveq >>
   fs [LENGTH_FLAT, size_of_shape_def, SUM_MAP_FOLDL, FOLDL_MAP] >>
   match_mp_tac FOLDL_CONG >>
   fs [] >> rw [] >>
   first_x_assum (qspec_then ‘x’ mp_tac) >>
   fs [] >>
   fs [MEM_EL] >> rveq >>
   drule opt_mmap_el >>
   disch_then drule >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                            ‘SND(compile_exp ct (EL n es))’] mp_tac) >>
   fs [])
  >- (
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq] >>
   fs [v_case_eq] >> rveq >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   fs [panLangTheory.shape_case_eq] >> rveq
   >- fs [size_of_shape_def] >> (* trivial *)
   reverse FULL_CASE_TAC
   >- (fs [] >> rveq >> fs [size_of_shape_def]) >>
   fs [] >> rveq >>
   first_x_assum (qspecl_then [‘ct’, ‘cexp'’, ‘Comb shapes’] mp_tac) >>
   fs [] >> strip_tac >>
   rename1 ‘i < LENGTH vs’ >>
   metis_tac [with_shape_el_len])
  >- (
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq] >>
   rename1 ‘eval s e = SOME adr’ >>
   fs [v_case_eq] >> rveq >> fs [] >>
   fs [panSemTheory.word_lab_case_eq] >> rveq >>
   fs [] >>
   (* unfold compiler def *)
   fs [compile_exp_def] >> pairarg_tac >> fs [] >>
   fs [list_case_eq] >> rveq
   >- fs [size_of_shape_def] >>
   reverse (fs [panLangTheory.shape_case_eq]) >> rveq
   >- fs [size_of_shape_def] >>
   fs [load_shape_length_shape_eq]) >>
  (* trivial *)
  fs [compile_exp_def] >> TRY (pairarg_tac) >>
  fs [] >> every_case_tac >> fs [] >> rveq >>
  fs [size_of_shape_def]
QED


Theorem compile_exp_shape_rel:
  ∀s e v ct cexp sh.
  panSem$eval s e = SOME v ∧
  wf_ctxt ct s.locals ∧
  compile_exp ct e = (cexp, sh) ==>
  shape_of v = sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rw []
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [shape_of_def,compile_exp_def])
  >- (
   rename1 ‘eval s (Var vname)’ >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [wf_ctxt_def] >>
   first_x_assum (qspecl_then [‘vname’, ‘v’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def])
  >- (  (* does not depend on ctxt *)
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def, shape_of_def])
  >- ( (* Struct *)
   fs [panSemTheory.eval_def, option_case_eq,
       compile_exp_def] >>
   rveq >>
   fs [shape_of_def] >>
   fs [MAP_EQ_EVERY2] >>
   conj_tac
   >- (drule opt_mmap_length_eq >> fs []) >>
   fs [LIST_REL_MAP2] >>
   fs [Once LIST_REL_EL_EQN] >>
   conj_tac >- (drule opt_mmap_length_eq >> fs []) >>
   rw [] >>
   fs [MEM_EL] >>
   ‘LENGTH vs =  LENGTH es’ by (drule opt_mmap_length_eq >> fs []) >>
   fs [] >>
   first_x_assum (qspec_then ‘EL n es’ mp_tac) >>
   impl_tac >- metis_tac [] >>
   drule opt_mmap_el >>
   disch_then drule >>
   strip_tac >> fs [] >>
   disch_then drule >>
   disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                            ‘SND(compile_exp ct (EL n es))’] mp_tac) >> fs [])
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >>
   fs [v_case_eq] >> rveq >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   first_x_assum (qspecl_then [‘ct’, ‘cexp'’, ‘shape’] mp_tac) >>
   fs [] >>
   strip_tac >> rveq >> fs [shape_of_def] >> rfs [] >>
   rveq >>
   drule (INST_TYPE [``:'b``|->``:shape``] EL_MAP) >>
   disch_then (qspec_then ‘(λa. shape_of a)’ mp_tac) >>
   fs [])
  >- ( (* Load*)
   fs [panSemTheory.eval_def, option_case_eq] >>
   fs [v_case_eq, panSemTheory.word_lab_case_eq] >>
   rveq >>
   (* proving that shape = sh *)
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   first_x_assum (qspecl_then [‘ct’, ‘cexp'’, ‘shape'’] mp_tac) >>
   fs [shape_of_def] >> strip_tac >> rveq >>
   fs [] >>
   drule compile_exp_length_rel >>
   disch_then (qspecl_then [‘ct’, ‘cexp'’, ‘One’] mp_tac) >>
   fs [size_of_shape_def] >> strip_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [] >> rveq >>
   drule mem_load_some_shape_eq >> fs [])
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >>
   fs [v_case_eq, panSemTheory.word_lab_case_eq] >>
   rveq >>
   fs [option_case_eq] >> rveq >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   first_x_assum (qspecl_then [‘ct’, ‘cexp'’, ‘shape’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [shape_of_def] >> rveq >>
   drule compile_exp_length_rel >>
   disch_then (qspecl_then [‘ct’, ‘cexp'’, ‘One’] mp_tac) >>
   fs [size_of_shape_def] >>
   FULL_CASE_TAC >> fs [])
  >- (
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq] >> rveq >>
   fs [compile_exp_def] >>
   (* this is almost trivial the way Op is written, but make to sure once the
   length theorem has been proved *)
   every_case_tac >> fs [shape_of_def])
  >- (
   (* Trivially true, clean later *)
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq] >> rveq >>
   fs [v_case_eq, panSemTheory.word_lab_case_eq] >>
   rveq >> fs [option_case_eq] >> rveq >>
   fs [v_case_eq, panSemTheory.word_lab_case_eq] >>
   rveq >> fs [compile_exp_def] >>
   every_case_tac >> fs [shape_of_def])
  >- (
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq] >> rveq >>
   fs [v_case_eq, panSemTheory.word_lab_case_eq] >> rveq >>
   fs [compile_exp_def] >>
   every_case_tac >> fs [shape_of_def])
QED

Theorem compile_exp_type_rel:
  ∀s e v ct cexp sh.
  panSem$eval s e = SOME v ∧
  wf_ctxt ct s.locals ∧
  compile_exp ct e = (cexp, sh) ==>
  shape_of v = sh ∧  LENGTH cexp = size_of_shape sh
Proof
  metis_tac [compile_exp_shape_rel, compile_exp_length_rel]
QED

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

(* OPT_MMAP does not appear in the compiler defs, but in semantics,
try not to use it in the proofs *)

Theorem opt_mmap_mem_func:
  ∀l f n g.
  OPT_MMAP f l = SOME n ∧ MEM g l ==>
  ?m. f g = SOME m
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_some_none:
  ∀l f n.
  OPT_MMAP f l = SOME n ==>
  ~MEM NONE (MAP f l)
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem size_of_shape_flatten_eq:
  !v. size_of_shape (shape_of v) =
   LENGTH (flatten v)
Proof
  ho_match_mp_tac flatten_ind >> rw []
  >- (cases_on ‘w’ >> fs [shape_of_def, flatten_def, size_of_shape_def]) >>
  fs [shape_of_def, flatten_def, size_of_shape_def] >>
  fs [LENGTH_FLAT, MAP_MAP_o] >> fs[SUM_MAP_FOLDL] >>
  match_mp_tac FOLDL_CONG >> fs []
QED


Theorem drop_append:
  !a b c.
   a ++ b = c ==>
    b = DROP (LENGTH a) c
Proof
  Induct >> rw [] >>
  fs [LENGTH_CONS]
QED

Theorem opt_mmap_some_ep_map_the:
  !l f v.
  OPT_MMAP f l = SOME v ==>
  MAP THE (MAP f l) = v
Proof
  Induct >> rw [OPT_MMAP_def]
QED

(* to simplfy later: (eval t) can be f *)
Theorem flatten_struct_eval_value_eq_el:
  ∀shapes t vs cexp index.
  index < LENGTH shapes /\
  flatten (Struct vs) = MAP THE (MAP (eval t) cexp) /\
  LENGTH vs = LENGTH shapes /\
  LENGTH cexp = size_of_shape (Comb shapes) /\
  shape_of (Struct vs) = Comb shapes ==>
  flatten (EL index vs) =
  MAP THE (MAP (eval t) (EL index (with_shape shapes cexp)))
Proof
  Induct >> rw [] >>
  cases_on ‘index’ >> fs[]
  >- (
   fs [with_shape_def, shape_of_def, flatten_def] >>
   fs [MAP_TAKE] >>
   fs [LENGTH_CONS, size_of_shape_def] >>
   cases_on ‘h'’ >> fs []
   >- (
    fs [flatten_def] >> rveq >> fs[MAP] >>
    cases_on ‘w’ >> fs [shape_of_def] >> rveq >>
    fs[size_of_shape_def] >> rveq >>
    qpat_x_assum ‘p2cw _:: _ = _’ (mp_tac o GSYM ) >> fs []) >>
   fs [with_shape_def, shape_of_def] >>
   fs [MAP_TAKE] >>
   fs [LENGTH_CONS, size_of_shape_def] >>
   qpat_x_assum ‘flatten _ ++ _ = _’ (mp_tac o GSYM ) >> fs [] >> strip_tac >> rveq >>
   fs [MAP] >> rveq >> fs [size_of_shape_flatten_eq] >>
   metis_tac [TAKE_LENGTH_APPEND])  >>
  (* induction case *)
  fs [flatten_def, EL] >> fs [with_shape_def] >>
  first_x_assum (qspecl_then [‘t’, ‘TL vs’, ‘(DROP (size_of_shape h) cexp)’, ‘n’] mp_tac) >>
  impl_tac
  >- (
   fs [] >> conj_tac
  >- (
   fs [MAP_MAP_o, size_of_shape_def, shape_of_def, LENGTH_CONS] >>
   rveq >> fs [MAP] >> rveq >>
   fs [size_of_shape_flatten_eq] >> fs [MAP_DROP] >>
   fs [drop_append]) >>
  conj_tac >- fs [LENGTH_CONS] >>
  conj_tac
  >- (
   fs [MAP_MAP_o, size_of_shape_def, shape_of_def, LENGTH_CONS] >>
   rveq >> fs [MAP] >> rveq >>
   fs [size_of_shape_flatten_eq] >> fs [MAP_DROP] >>
   fs [drop_append]) >>
  fs [shape_of_def, LENGTH_CONS] >> rveq >> fs [MAP]) >>
  fs []
QED


Theorem compile_exp_val_rel:
  ∀s e v t ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
   flatten v = MAP THE (MAP (eval t) es)
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rw []
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, crepSemTheory.eval_def])
  >- (
   rename1 ‘eval s (Var vname)’ >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum (qspecl_then [‘vname’, ‘v’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [lookup_locals_eq_map_vars] >>
   metis_tac [opt_mmap_some_ep_map_the])
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> cheat (* should come from code_rel, define it later*))
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o] >>
   fs [MAP_FLAT] >>
   fs [MAP_MAP_o] >>
   fs [flatten_def] >>
   qmatch_goalsub_abbrev_tac ‘FLAT a = FLAT b’ >>
   ‘a = b’ suffices_by fs [] >>
   unabbrev_all_tac >>
   fs [MAP_EQ_EVERY2] >>
   conj_tac
   >- (drule opt_mmap_length_eq >> fs []) >>
   fs [LIST_REL_EL_EQN] >>
   conj_tac
   >- (drule opt_mmap_length_eq >> fs []) >>
   rw [] >>
   first_x_assum(qspec_then ‘EL n es’ mp_tac) >>
   ‘n <  LENGTH es’ by cheat >> (* trivial *)
   drule EL_MEM >> strip_tac >> fs [] >>
   drule opt_mmap_el >>
   disch_then drule >>
   strip_tac >> fs [] >>
   disch_then (qspecl_then [‘t’, ‘ct’,
                            ‘FST (compile_exp ct (EL n es))’,
                            ‘SND (compile_exp ct (EL n es))’] mp_tac) >>
   fs [] >>
   TOP_CASE_TAC >> fs [])
  >-
   (
   (* Field case *)
   drule locals_rel_imp_wf_ctxt >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >>
   fs [panLangTheory.shape_case_eq] >> rveq
   >- (
    drule compile_exp_shape_rel >>
    disch_then (qspecl_then [‘ct’, ‘cexp’, ‘One’] mp_tac) >>
    fs [shape_of_def]) >>
   FULL_CASE_TAC >> fs [] >> rveq >>
   first_x_assum (qspecl_then
                  [‘t’, ‘ct’, ‘cexp’, ‘Comb shapes’] mp_tac) >> fs [] >>
   strip_tac >>
   ‘LENGTH vs = LENGTH shapes’ by (
     drule compile_exp_shape_rel >>
     disch_then (qspecl_then [‘ct’, ‘cexp’, ‘Comb shapes’] mp_tac) >>
     fs [] >> strip_tac >>
     fs [shape_of_def] >> metis_tac [LENGTH_MAP]) >>
   ‘index < LENGTH shapes’ by metis_tac [] >> fs [] >> rveq >>
   drule compile_exp_length_rel >>
   disch_then (qspecl_then [‘ct’, ‘cexp’, ‘Comb shapes’] mp_tac) >>
   fs [] >> strip_tac >>
   drule compile_exp_shape_rel >>
   disch_then (qspecl_then [‘ct’, ‘cexp’, ‘Comb shapes’] mp_tac) >>
   fs [] >> strip_tac >>
   metis_tac [flatten_struct_eval_value_eq_el]) >>
  cheat

QED






Theorem compile_exp_val_rel:
  ∀s e v t ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
   ~MEM NONE (MAP (eval t) es)
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rw []
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, crepSemTheory.eval_def])
  >- (
   rename1 ‘eval s (Var vname)’ >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum (qspecl_then [‘vname’, ‘v’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [lookup_locals_eq_map_vars] >>
   metis_tac [opt_mmap_some_none])
  >- (
   CCONTR_TAC >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> cheat (* should come from code_rel, define it later*))
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   (* remove es' *)
   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o] >>
   fs [MAP_FLAT] >>
   fs [MAP_MAP_o] >>
   CCONTR_TAC >>
   fs [] >>
   fs [MEM_FLAT] >>
   fs [MEM_MAP] >>
   rveq >>
   rename1 ‘MEM e es’ >>
   dxrule opt_mmap_mem_func >>
   disch_then (qspec_then ‘e’ mp_tac) >>
   strip_tac >> rfs [] >>
   fs [MEM_MAP] >> rveq >>
   first_x_assum (qspec_then ‘e’ mp_tac) >>
   strip_tac >> rfs [] >>
   first_x_assum (qspecl_then
                  [‘t’, ‘ct’,
                   ‘FST (compile_exp ct e)’,
                   ‘SND (compile_exp ct e)’] mp_tac) >>
   strip_tac >> rfs [] >>
   metis_tac [])
  >- (
   CCONTR_TAC >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [v_case_eq] >> rveq >>
   fs [panLangTheory.shape_case_eq] >>  rveq
   >- fs [MAP, crepSemTheory.eval_def] >>
   reverse FULL_CASE_TAC >> fs [] >> rveq
   >- fs [MAP, crepSemTheory.eval_def] >>
   (* to remove cexp *)
   fs [compile_exp_def] >>





   fs [MEM_MAP] >> rveq >> fs [MEM_EL] >>
   first_x_assum (qspecl_then [‘t’, ‘ct’, ‘cexp’, ‘Comb shapes’] mp_tac) >>
   strip_tac >> rfs [] >>
   first_x_assum (qspec_then ‘EL n (EL index (with_shape shapes cexp))’ mp_tac) >>
                 fs [] >>







   (* remaining *) ) >> cheat

QED




vs'' =

Theorem length_shape:
  LENGTH es = size_of_shape (Comb sh) /\
  i < LENGTH sh ==>
  size_of_shape (EL i sh) = LENGTH (EL i (with_shape sh es))


Proof
QED



(*

  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes =>
     if index < LENGTH shapes then
     (EL index (with_shape shapes cexp), EL index shapes)
     else ([Const 0w], One)) /\

*)




   )







   )







  drule opt_mmap_length_eq >>
  strip_tac >> fs [] >> rveq

  fs [] >>






  TOP_CASE_TAC >> fs [] >>










QED






(* to state this goal differrently *)
Theorem compile_exp_val_rel:
  ∀s e v t ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  ?vs. OPT_MMAP (eval t) es = SOME vs ∧
       vs = flatten v
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rw []
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, crepSemTheory.eval_def])
  >- (
   rename1 ‘eval s (Var vname)’ >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum (qspecl_then [‘vname’, ‘v’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   metis_tac [lookup_locals_eq_map_vars])
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def, p2cw_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> cheat (* should come from code_rel, define it later*))
  >- (
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   dxrule opt_mmap_mem_func >>
   strip_tac >> fs [] >>






   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o] >>
   qmatch_goalsub_abbrev_tac ‘OPT_MMAP (eval t) es'’ >>







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

   fs [flatten_def] >>





   v = Struct vs
     es = es'



   fs [] >> cheat) >>
  cheat
QED


Theorem eassign_flookup_of_length:
  evaluate (Assign v src,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  locals_rel ctxt s.locals t.locals ==>
  FLOOKUP ctxt.var_nums v <> SOME (One,[])
Proof
  CCONTR_TAC >>
  fs [panSemTheory.evaluate_def] >>
  FULL_CASE_TAC >> fs [] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  fs [is_valid_value_def] >>
  FULL_CASE_TAC >> fs [] >>
  fs [locals_rel_def] >>
  first_x_assum (qspecl_then [‘v’,‘x'’] assume_tac) >>
  rfs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [size_of_shape_def]
QED

Theorem shape_of_one_word:
  shape_of v = One ==>
  ?w. v = Val w
Proof
  cases_on ‘v’ >>
  fs [shape_of_def]
QED

Theorem compile_Assign:
  ^(get_goal "comp _ (panLang$Assign _ _)")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [option_case_eq] >>
  cases_on ‘is_valid_value s.locals v value’ >>
  fs [] >> rveq >>
  rename1 ‘eval s e = SOME value’ >>
  fs [is_valid_value_def] >>
  cases_on ‘FLOOKUP s.locals v’ >> fs [] >>
  rename1 ‘shape_of ev = shape_of vv’ >>
  drule locals_rel_imp_wf_ctxt >>
  strip_tac >>
  (* unfolding compile_prog *)
  fs [compile_prog_def] >>
  fs [wf_ctxt_def] >>
  first_x_assum (qspecl_then [‘v’, ‘vv’] mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >> fs [] >>
  cases_on ‘shape_of vv’ >> fs []
  >- (
   fs [size_of_shape_def] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   TOP_CASE_TAC >>
   drule locals_rel_imp_wf_ctxt >> (* putting it back again *)
   strip_tac >>
   drule compile_exp_type_rel >>
   disch_then drule_all >>
   strip_tac >> rfs [] >> rveq >>
   fs [size_of_shape_def] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   fs [crepSemTheory.evaluate_def] >>
   dxrule shape_of_one_word >>
   dxrule shape_of_one_word >>
   rpt strip_tac >> fs [] >> rveq >>
   ‘eval t h' = SOME (p2cw w)’ by cheat >>
   fs [] >>
   cheat)

QED


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
Definition evals_def:
  (evals (s:('a,'ffi) crepSem$state) [] = []) /\
  (evals s (e::es) = eval s e :: evals s es)
End


Theorem compile_exp_correct:
  !s t ctxt e v es sh.
  state_rel s t /\
  locals_rel ctxt s t /\
  eval s e = SOME v /\
  compile_exp ctxt e = (es, sh) ==>
  flatten_func v = evals t es
  (* may be to do cases on v, if it is a word, or a label or a struct,
     but may be not  *)
Proof
  cheat
QED
*)


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


val _ = export_theory();
