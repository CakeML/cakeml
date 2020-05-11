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
  <| var_nums  : panLang$varname |-> shape # num list;
     code_vars : panLang$funname |-> ((panLang$varname # shape) list # num list);
     max_var   : num|>
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

(* compiler for prog *)

Definition var_cexp_def:
  (var_cexp (Const w:'a crepLang$exp) = ([]:num list)) ∧
  (var_cexp (Var v) = [v]) ∧
  (var_cexp (Label f) = []) ∧
  (var_cexp (Load e) = var_cexp e) ∧
  (var_cexp (LoadByte e) = var_cexp e) ∧
  (var_cexp (LoadGlob a) = []) ∧
  (var_cexp (Op bop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Cmp c e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp (Shift sh e num) = var_cexp e)
Termination
  wf_rel_tac `measure (\e. crepLang$exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac crepLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition nested_seq_def:
  (nested_seq [] = (Skip:'a crepLang$prog)) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
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


Definition nested_decs_def:
  (nested_decs [] [] p = p) /\
  (nested_decs (n::ns) (e::es) p = Dec n e (nested_decs ns es p)) /\
  (nested_decs [] _ p = Skip) /\
  (nested_decs _ [] p = Skip)
End

(* def in this style so that easier to reason about *)
Definition store_globals_def:
  (store_globals ad [] = []) ∧
  (store_globals ad (e::es) =
   StoreGlob ad e :: store_globals (ad+1w) es)
End

(*
Definition store_globals_def:
  store_globals es = MAP2 StoreGlob (GENLIST (λn. n2w n) (LENGTH es)) es
End
*)

Definition load_globals_def:
  (load_globals _ 0 = []) ∧
  (load_globals ad (SUC n) = (LoadGlob ad) :: load_globals (ad+1w) n)
End

(*
Definition load_globals_def:
  load_globals sz = MAP LoadGlob (GENLIST (λn. n2w n) sz)
End
*)

Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.max_var;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|var_nums := ctxt.var_nums |+ (v, (sh, nvars));
                            max_var := ctxt.max_var + size_of_shape sh|> in
            if size_of_shape sh = LENGTH es
            then nested_decs nvars es (compile_prog nctxt p)
            else Skip) /\
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
  (compile_prog ctxt (Store ad v) =
   case compile_exp ctxt ad of
    | (e::es',sh') =>
       let (es,sh) = compile_exp ctxt v;
            adv = ctxt.max_var + 1;
            temps = GENLIST (λx. adv + SUC x) (size_of_shape sh) in
            if size_of_shape sh = LENGTH es
            then nested_decs (adv::temps) (e::es)
                 (nested_seq (stores (Var adv) (MAP Var temps) 0w))
            else Skip
    | (_,_) => Skip) /\
  (compile_prog ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile_prog ctxt (Return rt) =
   let (ces,sh) = compile_exp ctxt rt in
   if size_of_shape sh = 0 then Return (Const 0w)
   else case ces of
         | [] => Skip
         | e::es => if size_of_shape sh = 1 then (Return e) else
          let temps = GENLIST (λx. ctxt.max_var + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH (e::es)
           then Seq (nested_decs temps (e::es)
                                 (nested_seq (store_globals 0w (MAP Var temps)))) (Return (Const 0w))
        else Skip) /\
  (compile_prog ctxt (Raise excp) =
   let (ces,sh) = compile_exp ctxt excp in
   if size_of_shape sh = 0 then Raise (Const 0w)
   else case ces of
         | [] => Skip
         | e::es => if size_of_shape sh = 1 then (Raise e) else
          let temps = GENLIST (λx. ctxt.max_var + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH (e::es)
           then Seq (nested_decs temps (e::es)
                                 (nested_seq (store_globals 0w (MAP Var temps)))) (Raise (Const 0w))
        else Skip) /\
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


  (compile_prog ctxt (Call rtyp e es) =
   let (cs, sh) = compile_exp ctxt e;
       cexps = MAP (compile_exp ctxt) es;
       args = FLAT (MAP FST cexps) in
    case cs of
    | ce::ces =>
       (case rtyp of
       | Tail => Call Tail ce args
       | Ret rt =>
         (case FLOOKUP ctxt.var_nums rt of
         | SOME (One, n::ns) => Call (Ret n) ce args
         | SOME (One, []) => Tick
         | SOME (Comb sh, ns) =>
            if size_of_shape (Comb sh) = 1 then Call (Ret (HD ns)) ce args   (* HD here *)
            else nested_seq (Call (Ret (ctxt.max_var + 1)) ce args ::
                                             MAP2 Assign ns (load_globals 0w (LENGTH ns)))
         | NONE => Tick)
       | Handle rt excp sh p => Call (Handle 1 1 (compile_prog ctxt p)) ce args)
    | [] => Skip) /\

  (compile_prog ctxt (ExtCall f v1 v2 v3 v4) = ARB) /\
  (compile_prog ctxt Tick = Tick)
End

(* state relation *)

val s = ``(s:('a,'ffi) panSem$state)``

Definition no_overlap_def:
  no_overlap fm <=>
    (!x a xs.
       FLOOKUP fm x = SOME (a,xs) ==> ALL_DISTINCT xs) /\
    (!x y a b xs ys.
       FLOOKUP fm x = SOME (a,xs) /\
       FLOOKUP fm y = SOME (b,ys) /\
       ~DISJOINT (set xs) (set ys) ==> x = y)
End

Definition ctxt_max_def:
  ctxt_max (n:num) fm <=>
    0 <= n ∧
    (!v a xs.
       FLOOKUP fm v = SOME (a,xs) ==> !x. MEM x xs ==> x <= n)
End

Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ns. FLOOKUP ctxt.code_vars f = SOME (vshs, ns) /\
       ALL_DISTINCT ns /\
       let vs = MAP FST vshs;
           shs = MAP SND vshs;
           nctxt = <|var_nums := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
                     code_vars := ctxt.code_vars; max_var := list_max ns |> in
       size_of_shape (Comb shs) = LENGTH ns /\
       FLOOKUP t_code f = SOME (ns, compile_prog nctxt prog)
End

(*
Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ns. FLOOKUP ctxt.code_vars f = SOME (vshs, ns) /\
       ALL_DISTINCT ns /\
       let vs = MAP FST vshs;
           shs = MAP SND vshs;
           nctxt = <|var_nums := alist_to_fmap (ZIP (vs,(ZIP (shs, with_shape shs ns))));
                     code_vars := ctxt.code_vars; max_var := list_max ns |> in
       size_of_shape (Comb shs) = LENGTH ns /\
       FLOOKUP t_code f = SOME (ns, compile_prog nctxt prog)
End
*)

(*
Definition code_rel_def:
  code_rel cctxt s_code t_code <=>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ctxt. FLOOKUP cctxt f = SOME ctxt /\
   no_overlap ctxt.var_nums /\
   ctxt_max ctxt.max_var ctxt.var_nums /\
   (!v sh. MEM (v, sh) vshs ==>
     ?ns. FLOOKUP ctxt.var_nums v = SOME (sh, ns) /\
     FLOOKUP t_code f = SOME (ns, compile_prog ctxt prog))
End
*)

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi
End

Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals <=>
  no_overlap ctxt.var_nums /\ ctxt_max ctxt.max_var ctxt.var_nums /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃ns vs. FLOOKUP (ctxt.var_nums) vname = SOME (shape_of v, ns) ∧
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
  ∀s e v (t :('a, 'b) state) ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
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
   fs [eval_def] >> fs [code_rel_def] >>
   cases_on ‘v1’ >>
   last_x_assum drule_all >> strip_tac >>
   fs [panLangTheory.size_of_shape_def, shape_of_def])
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
   ntac 4 (disch_then drule) >>
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


Definition globals_lookup_def:
  globals_lookup t v =
    OPT_MMAP (FLOOKUP t.globals)
             (GENLIST (λx. n2w x) (size_of_shape (shape_of v)))
End


val goal =
  ``λ(prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ code_rel ctxt s.code t.code /\
      locals_rel ctxt s.locals t.locals ⇒
      ∃res1 t1. evaluate (compile_prog ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧ code_rel ctxt s1.code t1.code /\
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt s1.locals t1.locals
       | SOME Continue => res1 = SOME Continue /\
                       locals_rel ctxt s1.locals t1.locals
       | SOME (Return v) =>
          (size_of_shape (shape_of v) = 0 ==> res1 = SOME (Return (Word 0w))) ∧
          (size_of_shape (shape_of v) = 1 ==> res1 = SOME (Return (HD(flatten v)))) ∧
          (1 < size_of_shape (shape_of v) ==>
               res1 = SOME (Return (Word 0w)) /\ globals_lookup t1 v = SOME (flatten v) ∧
               size_of_shape (shape_of v) <= 32)
       | SOME (Exception v) =>
          (size_of_shape (shape_of v) = 0 ==> res1 = SOME (Exception (Word 0w))) ∧
          (size_of_shape (shape_of v) = 1 ==> res1 = SOME (Exception (HD(flatten v)))) ∧
          (1 < size_of_shape (shape_of v) ==>
               res1 = SOME (Exception (Word 0w)) /\ globals_lookup t1 v = SOME (flatten v) ∧
               size_of_shape (shape_of v) <= 32)
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
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
  fun compile_prog_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end


Theorem compile_Skip_Break_Continue:
  ^(get_goal "compile_prog _ panLang$Skip") /\
  ^(get_goal "compile_prog _ panLang$Break") /\
  ^(get_goal "compile_prog _ panLang$Continue")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, crepSemTheory.evaluate_def,
      compile_prog_def] >> rveq >> fs []
QED


Theorem compile_Tick:
  ^(get_goal "compile_prog _ panLang$Tick")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, crepSemTheory.evaluate_def,
      compile_prog_def] >> rveq >> fs [] >>
  every_case_tac >> fs [panSemTheory.empty_locals_def, empty_locals_def,
                        panSemTheory.dec_clock_def, dec_clock_def] >>
  rveq >> fs [state_rel_def]
QED


Theorem locals_rel_lookup_ctxt:
  locals_rel ctxt lcl lcl' /\
  FLOOKUP lcl vr = SOME v ==>
  ?ns. FLOOKUP ctxt.var_nums vr = SOME (shape_of v,ns) /\
   LENGTH ns = LENGTH (flatten v) /\
   OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v)
Proof
  rw [locals_rel_def] >>
  metis_tac [opt_mmap_length_eq]
QED


Theorem distinct_lists_append:
  ALL_DISTINCT (xs ++ ys)  ==>
  distinct_lists xs ys
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_commutes:
  distinct_lists xs ys = distinct_lists ys xs
Proof
  EQ_TAC >>
  rw [] >>
  fs [distinct_lists_def, EVERY_MEM] >>
  metis_tac []
QED

Theorem distinct_lists_cons:
  distinct_lists (ns ++ xs) (ys ++ zs) ==>
  distinct_lists xs zs
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_simp_cons:
  distinct_lists xs (y :: ys) ==>
  distinct_lists xs ys
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_append_intro:
  distinct_lists xs ys /\
  distinct_lists xs zs ==>
  distinct_lists xs (ys ++ zs)
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem opt_mmap_flookup_update:
  OPT_MMAP (FLOOKUP fm) xs = SOME ys /\
  ~MEM x xs ==>
  OPT_MMAP (FLOOKUP (fm |+ (x,y))) xs = SOME ys
Proof
  rw [] >>
  fs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  fs [FLOOKUP_UPDATE, MEM_EL] >>
  metis_tac []
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_cexp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (fs [eval_def])
  >- fs [eval_def, var_cexp_def, FLOOKUP_UPDATE]
  >- fs [eval_def]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- fs [var_cexp_def, eval_def, CaseEq "option"]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def, ETA_AX] >>
   fs [eval_def, CaseEq "option", ETA_AX] >>
   qexists_tac ‘ws’ >>
   fs [opt_mmap_eq_some, ETA_AX,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   fs [MEM_FLAT, MEM_MAP] >>
   metis_tac [EL_MEM]) >>
  rpt gen_tac >>
  strip_tac >> fs [var_cexp_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
QED

Theorem eval_nested_assign_distinct_eq:
  !es ns t ev vs.
  MAP (eval t) es = MAP SOME ev /\
  OPT_MMAP (FLOOKUP t.locals) ns = SOME vs /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ==>
  evaluate (nested_seq (MAP2 Assign ns es),t) =
      (NONE, t with locals := t.locals |++ ZIP (ns, ev))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM,
       state_component_equality]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [MAP_EQ_CONS] >>
  rveq >> rfs [] >>
  fs [OPT_MMAP_def] >>
  rveq >> rfs [] >>
  rveq >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘FLOOKUP t.locals n = SOME nv’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  drule opt_mmap_flookup_update >>
  disch_then drule >>
  disch_then (qspec_then ‘v’ assume_tac) >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule >>
  fs [state_accfupds] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  fs [FUPDATE_LIST_THM]
QED

Theorem opt_mmap_some_eq_zip_flookup:
  ∀xs f ys.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,ys))) xs =
  SOME ys
Proof
  Induct >> rw [OPT_MMAP_def] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem all_distinct_flookup_all_distinct:
  no_overlap fm /\
   FLOOKUP fm x = SOME (y,zs) ==>
  ALL_DISTINCT zs
Proof
  rw [] >>
  fs [no_overlap_def] >>
  metis_tac []
QED

Theorem no_overlap_flookup_distinct:
  no_overlap fm /\
  x ≠ y /\
  FLOOKUP fm x = SOME (a,xs) /\
  FLOOKUP fm y = SOME (b,ys) ==>
  distinct_lists xs ys
Proof
  rw [] >>
  match_mp_tac distinct_lists_append >>
  fs [no_overlap_def, ALL_DISTINCT_APPEND, DISJOINT_ALT] >>
  metis_tac []
QED

Theorem opt_mmap_disj_zip_flookup:
  ∀xs f ys zs.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
  OPT_MMAP (FLOOKUP f) ys
Proof
  Induct >> rw [] >>
  fs [distinct_lists_def]
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘zs’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ho_match_mp_tac IMP_OPT_MMAP_EQ >>
  ho_match_mp_tac MAP_CONG >> fs [] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  metis_tac []
QED

Theorem res_var_commutes:
  n ≠ h ==>
  res_var (res_var lc (h,FLOOKUP lc' h))
  (n,FLOOKUP lc' n) =
  res_var (res_var lc (n,FLOOKUP lc' n))
  (h,FLOOKUP lc' h)
Proof
  rw [] >>
  cases_on ‘FLOOKUP lc' h’ >>
  cases_on ‘FLOOKUP lc' n’ >>
  fs[res_var_def] >>
  fs [DOMSUB_COMMUTES, DOMSUB_FUPDATE_NEQ] >>
  metis_tac [FUPDATE_COMMUTES]
QED


Theorem eval_nested_decs_seq_res_var_eq:
  !es ns t ev p.
  MAP (eval t) es = MAP SOME ev /\
  LENGTH ns = LENGTH es /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns ==>
  let (q,r) = evaluate (p, t with locals := t.locals |++ ZIP (ns, ev)) in
  evaluate (nested_decs ns es p, t) =
  (q, r with locals :=
        FOLDL res_var r.locals (ZIP (ns, MAP (FLOOKUP t.locals) ns)))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [nested_decs_def, FUPDATE_LIST_THM] >>
   cases_on ‘t’ >> cases_on ‘r’ >>
   fs [state_component_equality, state_locals_fupd]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_decs_def] >>
  fs [evaluate_def] >>
  fs [MAP_EQ_CONS] >>
  pairarg_tac >> fs [] >>
  rveq >> rfs [] >>
  pairarg_tac >> fs [] >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘~MEM n t'’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [FUPDATE_LIST_THM] >>
  fs [state_component_equality] >>
  ‘MAP (FLOOKUP (t.locals |+ (n,v))) t' =
   MAP (FLOOKUP t.locals) t'’ by
    metis_tac [MAP_EQ_f, FLOOKUP_UPDATE] >>
  fs [] >>
  pop_assum kall_tac >>
  qpat_x_assum ‘~MEM n t'’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘r’, ‘n’,‘t’, ‘t'’] >>
  Induct >> rw [] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  disch_then (qspec_then ‘r with locals :=
                          res_var r.locals (h,FLOOKUP t.locals h)’ mp_tac) >>
  fs [] >>
  metis_tac [res_var_commutes]
QED

Theorem mem_comp_field:
  !sh i e shp ce es vs.
   i < LENGTH vs /\
  LENGTH e = size_of_shape (shape_of (Struct vs)) /\
  comp_field i sh e = (es,shp) /\
  Comb sh = shape_of (Struct vs) /\
  MEM ce es ==> MEM ce e
Proof
  Induct >> rw [comp_field_def] >>
  fs [] >> rveq
  >- fs [shape_of_def]
  >- (
   cases_on ‘vs’ >> fs [] >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >> fs [] >>
   ‘size_of_shape (shape_of h') <= LENGTH e’ by DECIDE_TAC >>
   metis_tac [MEM_TAKE]) >>
  cases_on ‘vs’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >>
  rveq >> fs [] >>
  first_x_assum (qspecl_then  [‘i-1’, ‘(DROP (size_of_shape (shape_of h')) e)’,
                               ‘shp’, ‘ce’, ‘es’, ‘t’] mp_tac) >>
  fs [] >>
  metis_tac [MEM_DROP_IMP]
QED

Theorem var_exp_load_shape:
  !i a e n.
   MEM n (load_shape a i e) ==>
   var_cexp n = var_cexp e
Proof
  Induct >>
  rw [load_shape_def] >>
  fs [var_cexp_def] >>
  metis_tac []
QED


Theorem genlist_distinct_max:
  !n ys m.
   (!y. MEM y ys ==> y <= m) ==>
   distinct_lists (GENLIST (λx. SUC x + m) n) ys
Proof
  rw [] >>
  fs [distinct_lists_def, EVERY_GENLIST] >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  first_x_assum drule >>
  DECIDE_TAC
QED

Theorem genlist_distinct_max':
  !n ys m p.
   (!y. MEM y ys ==> y <= m) ==>
   distinct_lists (GENLIST (λx. SUC x + (m + p)) n) ys
Proof
  rw [] >>
  fs [distinct_lists_def, EVERY_GENLIST] >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  first_x_assum drule >>
  DECIDE_TAC
QED

Theorem eval_var_cexp_present_ctxt:
  ∀(s :('a, 'b) panSem$state) e v (t :('a, 'b) state) ct es sh.
  state_rel s t /\
  eval s e = SOME v /\
  code_rel ct s.code t.code /\
  locals_rel ct s.locals t.locals /\
  compile_exp ct e = (es,sh) ==>
  (∀n. MEM n (FLAT (MAP var_cexp es)) ==>
   ?v shp ns. FLOOKUP ct.var_nums v = SOME (shp,ns)  /\
       MEM n ns)
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def] >>
   fs [CaseEq "option"] >> rveq
   >- fs [var_cexp_def] >>
   cases_on ‘v'’ >> fs [] >>
   rveq >>
   fs [MEM_MAP, MEM_FLAT] >>
   rveq >>
   fs [var_cexp_def] >>
   metis_tac [])
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o, MAP_FLAT] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [OPT_MMAP_def] >>
   strip_tac >>
   strip_tac >>
   rveq >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
   disch_then drule >>
   cases_on ‘compile_exp ct h’ >> fs [] >>
   strip_tac >>
   strip_tac >>
   metis_tac [])
  >- (
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq
   >- rw [var_cexp_def] >>
   rpt gen_tac >> strip_tac >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >>
   first_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   fs [] >> rveq >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >>
    qexists_tac ‘y’ >> fs [] >>
    drule compile_exp_val_rel >>
    disch_then drule_all >>
    strip_tac >> fs [] >> rveq >>
    metis_tac [mem_comp_field]) >>
   fs [])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   rpt gen_tac >>
   strip_tac >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   rveq >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   rveq >> fs [] >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >>
    qexists_tac ‘h’ >> fs [] >>
    metis_tac [var_exp_load_shape]) >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   reverse (cases_on ‘shape’) >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   rw [] >>
   fs [var_cexp_def] >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   FULL_CASE_TAC >>
   fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   fs [var_cexp_def, ETA_AX] >>
   rveq >>
   rw [] >>
   ntac 4 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 3 (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘n’,‘ws’, ‘x’, ‘es’] >>
   Induct
   >- (
    rw [] >> fs [cexp_heads_def, var_cexp_def] >>
    rveq  >> fs [MAP, FLAT]) >>
   rpt gen_tac >> strip_tac >>
   fs [OPT_MMAP_def] >>
   rpt strip_tac >>
   rveq >>
   fs [cexp_heads_def] >>
   fs [CaseEq "list", CaseEq "option"] >>
   rveq >>
   fs [MAP, MEM_FLAT, MEM_MAP] >> rveq
   >- (
    first_x_assum (qspec_then ‘h’ mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then (qspec_then ‘ct’ mp_tac) >>
    cases_on ‘compile_exp ct h’ >> fs []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >> metis_tac []) >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [CaseEq "list", CaseEq "option"] >>
   rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
   rw []
   >- (
    last_x_assum drule >>
    disch_then (qspec_then ‘ct’ mp_tac) >>
    cases_on ‘compile_exp ct e’ >> fs []) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e'’ >> fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
      CaseEq "word_lab"] >> rveq >>
  fs [compile_exp_def] >> rveq >>
  fs [CaseEq "list", CaseEq "option"] >>
  rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
  rw [] >> last_x_assum drule >>
  disch_then (qspec_then ‘ct’ mp_tac) >>
  cases_on ‘compile_exp ct e’ >> fs []
QED

Theorem update_eq_zip_flookup:
  ∀xs f ys n.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys /\
  n < LENGTH xs ⇒
  FLOOKUP (f |++ ZIP (xs,ys)) (EL n xs) =
        SOME (EL n ys)
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  cases_on ‘n’ >> fs [] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem map_var_cexp_eq_var:
  !vs. FLAT (MAP var_cexp (MAP Var vs)) = vs
Proof
  Induct >> rw [var_cexp_def] >>
  fs [var_cexp_def]
QED


Theorem flookup_fupdate_zip_not_mem:
  ∀xs ys f n.
  LENGTH xs = LENGTH ys /\
  ~MEM n xs ⇒
  FLOOKUP (f |++ ZIP (xs,ys)) n =
  FLOOKUP f n
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >>
  fs [FUPDATE_LIST_THM] >>
  metis_tac [FLOOKUP_UPDATE]
QED

Theorem map_flookup_fupdate_zip_not_mem:
  ∀xs ys f n.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ⇒
  MAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
  MAP (FLOOKUP f) ys
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2] >>
  ho_match_mp_tac EVERY2_refl >>
  rw [] >>
  fs [distinct_lists_def, EVERY_MEM] >>
  ho_match_mp_tac flookup_fupdate_zip_not_mem >>
  metis_tac []
QED

Theorem flookup_res_var_distinct_eq:
  !xs x fm.
  ~MEM x (MAP FST xs) ==>
  FLOOKUP (FOLDL res_var fm xs) x =
  FLOOKUP fm x
Proof
  Induct >> rw [] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED


Theorem flookup_res_var_distinct_zip_eq:
  LENGTH xs = LENGTH ys /\
  ~MEM x xs ==>
  FLOOKUP (FOLDL res_var fm (ZIP (xs,ys))) x =
  FLOOKUP fm x
Proof
  rw [] >>
  qmatch_goalsub_abbrev_tac `FOLDL res_var _ l` >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`x`,`ys`,`xs`,`fm`, `l`] >>
  Induct >> rw [] >> rveq >>
  cases_on ‘xs’ >> cases_on ‘ys’ >> fs [ZIP] >>
  rveq >>
  cases_on ‘h''’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED


Theorem flookup_res_var_distinct:
  !ys xs zs fm.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ==>
  MAP (FLOOKUP (FOLDL res_var fm (ZIP (xs,zs)))) ys =
  MAP (FLOOKUP fm) ys
Proof
  Induct
  >- rw[MAP] >> rw []
  >- (
   fs [distinct_lists_def, EVERY_MEM, FUPDATE_LIST_THM] >>
   ‘~MEM h xs’ by metis_tac [] >>
   drule flookup_res_var_distinct_zip_eq >>
   disch_then (qspecl_then [‘h’,‘fm’] mp_tac) >>
   fs [] >>
   strip_tac >> fs [] >>
   metis_tac [flookup_fupdate_zip_not_mem]) >>
  fs [FUPDATE_LIST_THM] >>
  drule distinct_lists_simp_cons >>
  strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then ‘zs’ mp_tac) >> fs []
QED


Theorem flookup_res_var_zip_distinct:
!ys xs as cs fm.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH as /\
  LENGTH xs = LENGTH cs ==>
  MAP (FLOOKUP (FOLDL res_var (fm |++ ZIP (xs,as)) (ZIP (xs,cs)))) ys =
  MAP (FLOOKUP fm) ys
Proof
  rw [] >>
  drule flookup_res_var_distinct >>
  disch_then (qspecl_then [‘cs’,‘fm |++ ZIP (xs,as)’] mp_tac) >>
  fs [] >>
  metis_tac [map_flookup_fupdate_zip_not_mem]
QED


Theorem flookup_res_var_some_eq_lookup:
  FLOOKUP (panSem$res_var lc (v,FLOOKUP lc' v)) v = SOME value ==>
  FLOOKUP lc' v = SOME value
Proof
  rw [] >> cases_on ‘FLOOKUP lc' v’ >>
  fs [panSemTheory.res_var_def, FLOOKUP_UPDATE]
QED


Theorem compile_Assign:
  ^(get_goal "compile_prog _ (panLang$Assign _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  rename [‘Assign vr e’] >>
  fs [panSemTheory.evaluate_def, is_valid_value_def] >>
  fs [CaseEq "option", CaseEq "bool"] >> rveq >> fs [] >>
  rename [‘eval _ e = SOME ev’] >>
  rename [‘FLOOKUP _ vr = SOME v’] >>
  (* open compiler def *)
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  drule locals_rel_lookup_ctxt >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  fs [length_flatten_eq_size_of_shape] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   ‘ALL_DISTINCT ns’
     by metis_tac [locals_rel_def, no_overlap_def] >>
   drule eval_nested_assign_distinct_eq >>
   disch_then drule >>
   strip_tac >> fs [] >>
   conj_tac
   >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   cases_on ‘vr = vname’ >> fs [] >> rveq
   >- (
    pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
    fs [] >> rveq >>
    match_mp_tac opt_mmap_some_eq_zip_flookup >>
    fs [] >>
    metis_tac [all_distinct_flookup_all_distinct,
               length_flatten_eq_size_of_shape]) >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   rfs [] >>
   drule no_overlap_flookup_distinct >>
   disch_then drule_all >>
   strip_tac >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  (* non-distinct Assign  *)
  qmatch_goalsub_abbrev_tac ‘nested_decs temps es _’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  ‘ALL_DISTINCT ns’ by metis_tac [locals_rel_def, no_overlap_def] >>
  ‘distinct_lists ns temps’ by (
    unabbrev_all_tac >>
    once_rewrite_tac [distinct_lists_commutes] >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten ev’,
                          ‘nested_seq (MAP2 Assign ns (MAP Var temps))’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  ‘MAP (eval (t with locals := t.locals |++ ZIP (temps,flatten ev)))
   (MAP Var temps) = MAP SOME (flatten ev)’ by (
    fs [MAP_MAP_o, MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >> rfs [] >>
    ‘n < LENGTH temps’ by (
      unabbrev_all_tac >> fs [MAP_MAP_o, MAP_EQ_EVERY2]>>
      metis_tac []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
    disch_then (qspec_then ‘Var’ assume_tac) >> fs [] >>
    fs [eval_def] >>
    metis_tac [update_eq_zip_flookup]) >>
  drule eval_nested_assign_distinct_eq >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  disch_then (qspec_then ‘flatten v’ mp_tac) >>
  impl_tac
  >- (
   fs [map_var_cexp_eq_var] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  rveq >>
  fs [state_rel_def] >>
  fs [locals_rel_def] >>
  rw [] >> fs [] >>
  (* writing in this style for druling below *)
  ‘DISJOINT (set (MAP FST (ZIP (temps,flatten ev))))
   (set (MAP FST (ZIP (ns,flatten ev))))’ by (
    ‘LENGTH ns = LENGTH (flatten ev)’ by
      fs [length_flatten_eq_size_of_shape] >>
    fs [GSYM length_flatten_eq_size_of_shape, MAP_ZIP] >>
    fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
    metis_tac []) >>
  drule FUPDATE_LIST_APPEND_COMMUTES >>
  disch_then (qspec_then ‘t.locals’ assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  cases_on ‘vr = vname’ >> fs [] >> rveq
  >- (
   pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
   fs [] >> rveq >>
   fs [opt_mmap_eq_some] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten ev’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape] >>
   strip_tac >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >> rfs [] >>
   ‘n < LENGTH ns’ by metis_tac [] >>
   metis_tac [update_eq_zip_flookup]) >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  rfs [] >>
  fs [opt_mmap_eq_some] >>
  ‘distinct_lists temps ns'’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``]
         flookup_res_var_zip_distinct) >>
  disch_then (qspecl_then [‘flatten ev’,
                           ‘MAP (FLOOKUP t.locals) temps’,
                           ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule no_overlap_flookup_distinct >>
  disch_then drule_all >>
  strip_tac >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >> rfs [] >>
  qpat_x_assum ‘LENGTH _ = LENGTH _’ (assume_tac o GSYM) >>
  fs [] >>
  last_x_assum drule >> strip_tac >>
  ‘~MEM (EL n ns') ns’ by (
    fs [Once distinct_lists_commutes] >>
    fs [distinct_lists_def, EVERY_MEM, EL_MEM]) >>
  metis_tac [flookup_fupdate_zip_not_mem]
QED

Definition assigned_vars_def:
  (assigned_vars (Skip:'a crepLang$prog) = ([]:num list)) ∧
  (assigned_vars (Dec n e p) = (n::assigned_vars p)) ∧
  (assigned_vars (Assign n e) = [n]) ∧
  (assigned_vars (Seq p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (If e p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (While e p) = assigned_vars p) ∧
  (assigned_vars (Call (Handle rt v p) e es) = rt :: v :: assigned_vars p) ∧
  (assigned_vars (Call (Ret v) e es) = [v]) ∧
  (assigned_vars _ = [])
End



Theorem flookup_res_var_diff_eq:
  n <> m ==>
  FLOOKUP (res_var l (m,v)) n = FLOOKUP l n
Proof
  rw [] >> cases_on ‘v’ >>
  fs [res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_NEQ]
QED

Theorem flookup_res_var_diff_eq_org:
  n <> m ==>
  FLOOKUP (panSem$res_var lc (n,v)) m = FLOOKUP lc m
Proof
  rw [] >> cases_on ‘v’ >>
 fs [panSemTheory.res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_NEQ]
QED


Theorem unassigned_vars_evaluate_same:
  !p s res t n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_vars p) ==>
  FLOOKUP t.locals n = FLOOKUP s.locals n
Proof
  recInduct evaluate_ind >> rw [] >> fs [] >>
  TRY (rename1 ‘While _ _’ >> cheat) >>
  TRY
  (fs [evaluate_def, assigned_vars_def, CaseEq "option", CaseEq "word_lab",
       set_globals_def, state_component_equality] >>
   TRY (pairarg_tac) >> rveq >> fs [] >> rveq >>
   FULL_CASE_TAC >> metis_tac [] >>
   NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >>
   first_x_assum drule  >>
   fs [state_component_equality, FLOOKUP_UPDATE] >>
   metis_tac [flookup_res_var_diff_eq] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [state_component_equality, FLOOKUP_UPDATE] >>
   fs [mem_store_def, state_component_equality] >> NO_TAC) >>
  TRY
  (cases_on ‘caltyp’ >>
   fs [evaluate_def, assigned_vars_def, CaseEq "option",  CaseEq "ret", CaseEq "word_lab"]  >>
   rveq >> cases_on ‘v2’ >> fs[] >>
   every_case_tac >> fs [set_var_def, state_component_equality] >>
   TRY (qpat_x_assum ‘s.locals |+ (_,_) = t.locals’ (mp_tac o GSYM) >>
        fs [FLOOKUP_UPDATE] >> NO_TAC) >>
   res_tac >> fs [FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >>
   metis_tac [] >> NO_TAC) >>
  fs [evaluate_def, assigned_vars_def, dec_clock_def, CaseEq "option",
      CaseEq "word_lab", CaseEq "ffi_result"]  >>
  rveq >> TRY (FULL_CASE_TAC) >>fs [state_component_equality]
QED

Theorem assigned_vars_nested_decs_append:
  !ns es p.
  LENGTH ns = LENGTH es ==>
  assigned_vars (nested_decs ns es p) = ns ++ assigned_vars p
Proof
  Induct >> rw [] >> fs [nested_decs_def] >>
  cases_on ‘es’ >>
  fs [nested_decs_def, assigned_vars_def]
QED


Theorem nested_seq_assigned_vars_eq:
  !ns vs.
  LENGTH ns = LENGTH vs ==>
  assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns
Proof
  Induct >> rw [] >- fs [nested_seq_def, assigned_vars_def] >>
  cases_on ‘vs’ >> fs [nested_seq_def, assigned_vars_def]
QED


Theorem assigned_vars_seq_store_empty:
  !es ad a.
  assigned_vars (nested_seq (stores ad es a)) =  []
Proof
  Induct >> rw [] >>
  fs [stores_def, assigned_vars_def, nested_seq_def] >>
  FULL_CASE_TAC >> fs [stores_def, assigned_vars_def, nested_seq_def]
QED

Theorem assigned_vars_store_globals_empty:
  !es ad.
  assigned_vars (nested_seq (store_globals ad es)) =  []
Proof
  Induct >> rw [] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def]
QED

Theorem not_mem_context_assigned_mem_gt:
  !p ctxt x.
   ctxt_max ctxt.max_var ctxt.var_nums /\
   (!v sh ns'. FLOOKUP ctxt.var_nums v = SOME (sh, ns') ==> ~MEM x ns') ∧
   x <= ctxt.max_var  ==>
   ~MEM x (assigned_vars (compile_prog ctxt p))
Proof
  Induct >> rw []
  >- fs [compile_prog_def, assigned_vars_def]
  >- (
   fs [compile_prog_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   qmatch_goalsub_abbrev_tac ‘compile_prog nctxt p’ >>
   disch_then (qspec_then ‘compile_prog nctxt p’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   first_x_assum (qspecl_then [‘nctxt’, ‘x’] mp_tac) >>
   disch_then match_mp_tac >>
   fs [Abbr ‘nctxt’, Abbr ‘dvs’] >>
   conj_tac >- (fs [ctxt_max_def] >> rw [FLOOKUP_UPDATE] >> fs [MEM_GENLIST] >> res_tac >> fs [] ) >>
   rw [FLOOKUP_UPDATE] >>  fs [] >> res_tac >> fs [])
  >- (
   fs [compile_prog_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   FULL_CASE_TAC >> FULL_CASE_TAC >> fs []
   >- (
    FULL_CASE_TAC >> fs [assigned_vars_def] >>
    drule nested_seq_assigned_vars_eq >>
    fs [] >> res_tac >> fs []) >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (MAP2 Assign r (MAP Var dvs))’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   ‘LENGTH r = LENGTH (MAP Var dvs)’ by fs [Abbr ‘dvs’, LENGTH_GENLIST] >>
   drule nested_seq_assigned_vars_eq >>
   fs [] >> res_tac >> fs [])
  >- (
   fs [compile_prog_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   fs [nested_decs_def] >>
   fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (stores (Var (ctxt.max_var + 1))
                                       (MAP Var dvs) 0w)’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   fs [assigned_vars_seq_store_empty]) >>
  TRY (fs [compile_prog_def, assigned_vars_def] >> every_case_tac >>
       fs [assigned_vars_def] >> metis_tac [] >> NO_TAC)
  >- cheat
  >- cheat >> (
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  ntac 4 (TOP_CASE_TAC >> fs [assigned_vars_def]) >>
  qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
  ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
  drule assigned_vars_nested_decs_append >>
  disch_then (qspec_then ‘nested_seq (store_globals 0w (MAP Var dvs))’ assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  conj_asm1_tac
  >- (
   fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
  fs [assigned_vars_store_globals_empty])
QED


Theorem rewritten_context_unassigned:
 !p nctxt v ctxt ns nvars sh sh'.
  nctxt = ctxt with
   <|var_nums := ctxt.var_nums |+ (v,sh,nvars);
     max_var  := ctxt.max_var + size_of_shape sh|> /\
  FLOOKUP ctxt.var_nums v = SOME (sh',ns) /\
  no_overlap ctxt.var_nums /\
  ctxt_max ctxt.max_var ctxt.var_nums /\
  no_overlap nctxt.var_nums ∧
  ctxt_max nctxt.max_var nctxt.var_nums /\
  distinct_lists nvars ns ==>
  distinct_lists ns (assigned_vars (compile_prog nctxt p))
Proof
  rw [] >> fs [] >>
  fs [distinct_lists_def] >>
  rw [] >>
  fs [EVERY_MEM] >> rw []>>
  CCONTR_TAC >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘compile_prog nctxt p’ >>
  assume_tac not_mem_context_assigned_mem_gt >>
  pop_assum (qspecl_then [‘p’, ‘nctxt’, ‘x’] mp_tac) >>
  impl_tac
  >- (
   unabbrev_all_tac >> fs[fetch "-" "context_component_equality"] >>
   rw [FLOOKUP_UPDATE]  >- metis_tac []
   >- (
    fs [no_overlap_def] >>
    first_x_assum (qspecl_then [‘v’, ‘v'’] mp_tac) >>
    fs [FLOOKUP_UPDATE] >>
    metis_tac [IN_DISJOINT]) >>
   fs [ctxt_max_def] >>
   res_tac >> fs [] >>
   DECIDE_TAC) >>
  fs []
QED


Theorem compile_Dec:
  ^(get_goal "compile_prog _ (panLang$Dec _ _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [CaseEq "option"] >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  qmatch_goalsub_abbrev_tac ‘nested_decs nvars es _’ >>
  ‘ALL_DISTINCT nvars ∧ LENGTH nvars = LENGTH es’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST]) >>
  ‘distinct_lists nvars (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘nvars’, ‘t’,
                          ‘flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  last_x_assum (qspecl_then [‘t with locals := t.locals |++ ZIP (nvars,flatten value)’,
                             ‘ctxt with <|var_nums := ctxt.var_nums |+ (v,shape_of value,nvars);
                               max_var := ctxt.max_var + size_of_shape (shape_of value)|>’ ]
                mp_tac) >>
  impl_tac
  >- (
   fs [state_rel_def] >>
   conj_tac >- fs [code_rel_def] >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [no_overlap_def] >>
    conj_tac
    >- (
     rw [] >>
     cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >>
     metis_tac []) >>
    rw [] >>
    cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
    rveq
    >- (
     qsuff_tac ‘distinct_lists nvars ys’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    qsuff_tac ‘distinct_lists nvars xs’
    >- (
     fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
     metis_tac []) >>
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    fs [ctxt_max_def] >> res_tac >> fs []) >>
   conj_tac
   >- (
    fs [ctxt_max_def]  >> rw [] >>
    cases_on ‘v = v'’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rw [] >>
   cases_on ‘v = vname’ >>  fs [FLOOKUP_UPDATE] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``]
           opt_mmap_some_eq_zip_flookup) >>
    disch_then (qspecl_then [‘t.locals’, ‘flatten v'’] mp_tac) >>
    fs [length_flatten_eq_size_of_shape]) >>
   res_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten value’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape])  >>
  strip_tac >> unabbrev_all_tac >> fs [] >> rveq >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac >- fs [code_rel_def] >>
  cases_on ‘res = NONE ∨ res = SOME Continue ∨ res = SOME Break’ >>
  fs [] >> rveq >> rfs [] >>
  TRY
  (qmatch_goalsub_abbrev_tac ‘ZIP (nvars, _)’ >>
   qmatch_asmsub_abbrev_tac ‘locals_rel nctxt st.locals r.locals’ >>
   rewrite_tac [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   rw [] >>
   reverse (cases_on ‘v = vname’) >> fs [] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:mlstring``,
                      ``:'b``|->``:'a v``] flookup_res_var_diff_eq_org) >>
    disch_then (qspecl_then [‘FLOOKUP s.locals v’, ‘st.locals’] (mp_tac o GSYM)) >>
    fs [] >> strip_tac >>
    fs [locals_rel_def] >> rfs [] >>
    first_x_assum drule_all >> strip_tac >> fs [] >>
    fs [Abbr ‘nctxt’] >>
    fs [FLOOKUP_UPDATE] >> rfs [] >>
    fs [opt_mmap_eq_some] >>
    ‘distinct_lists nvars ns’ by (
      fs [Abbr ‘nvars’] >> ho_match_mp_tac genlist_distinct_max >>
      rw [] >> fs [ctxt_max_def] >> res_tac >> fs []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``] flookup_res_var_distinct) >>
    disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                             ‘r.locals’] mp_tac) >>
    fs [LENGTH_MAP]) >>
   drule flookup_res_var_some_eq_lookup >>
   strip_tac >>
   qpat_x_assum ‘locals_rel ctxt s.locals t.locals’ mp_tac >>
   rewrite_tac [locals_rel_def] >>
   strip_tac >> fs [] >>
   pop_assum drule  >>
   strip_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   fs [opt_mmap_eq_some] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_distinct) >>
   disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                            ‘r.locals’] mp_tac) >>
   fs [LENGTH_MAP] >>
   strip_tac >>
   pop_assum kall_tac >>
   assume_tac rewritten_context_unassigned >>
   fs [] >>
   first_x_assum drule >>
   disch_then (qspecl_then [‘prog’, ‘nvars’,
                            ‘shape_of value’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    conj_tac
    >- (
     fs [no_overlap_def] >>
     rw []
     >- (cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >> metis_tac []) >>
     rw [] >>
     cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
     rveq
     >- (
      qsuff_tac ‘distinct_lists nvars ys’
      >- (
       fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
       metis_tac []) >>
      unabbrev_all_tac >>
      ho_match_mp_tac genlist_distinct_max >>
      rw [] >>
      fs [ctxt_max_def] >> res_tac >> fs []) >>
     qsuff_tac ‘distinct_lists nvars xs’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    fs [ctxt_max_def] >> rw [] >>
    cases_on ‘v = v''’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rewrite_tac [distinct_lists_def] >>
   strip_tac >> fs [EVERY_MEM] >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   first_x_assum (qspec_then ‘EL n ns’ mp_tac) >>
   fs [EL_MEM] >>
   strip_tac >>
   drule unassigned_vars_evaluate_same >> fs [] >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [] >>
   ‘LENGTH nvars = LENGTH (flatten value)’ by (
     unabbrev_all_tac >> fs [LENGTH_GENLIST]) >>
   drule flookup_fupdate_zip_not_mem >>
   fs [Once distinct_lists_commutes] >>
   disch_then (qspecl_then [‘t.locals’, ‘EL n ns’] mp_tac) >>
   fs [distinct_lists_def, EVERY_MEM] >>
   impl_tac >- metis_tac [EL_MEM] >> fs [] >> NO_TAC) >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >> fs [globals_lookup_def]
QED


Theorem evaluate_seq_stroes_locals_eq:
  !es ad a s res t.
   evaluate (nested_seq (stores ad es a),s) = (res,t) ==>
   t.locals = s.locals
Proof
  Induct >> rw []
  >- fs [stores_def, nested_seq_def, evaluate_def] >>
  fs [stores_def] >> FULL_CASE_TAC >> rveq >> fs [] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs [] >> rveq >>
  last_x_assum drule >>
  fs [mem_store_def,state_component_equality]
QED

Theorem domsub_commutes_fupdate:
  !xs ys fm x.
   ~MEM x xs ∧ LENGTH xs = LENGTH ys ==>
    (fm |++ ZIP (xs,ys)) \\ x = (fm \\ x) |++ ZIP (xs,ys)
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  metis_tac [DOMSUB_FUPDATE_NEQ]
QED



Triviality FUPDATE_LIST_APPLY_NOT_MEM_ZIP:
  ∀l1 l2 f k.
  LENGTH l1 = LENGTH l2 ∧ ¬MEM k l1 ⇒ (f |++ ZIP (l1, l2)) ' k = f ' k
Proof
 metis_tac [FUPDATE_LIST_APPLY_NOT_MEM, MAP_ZIP]
QED

Theorem fm_multi_update:
  !xs ys a b c d fm.
  ~MEM a xs ∧ ~MEM c xs ∧ a ≠ c ∧ LENGTH xs = LENGTH ys ==>
   fm |++ ((a,b)::(c,d)::ZIP (xs,ys)) |++ ((a,b)::ZIP (xs,ys)) =
   fm |++ ((a,b)::(c,d)::ZIP (xs,ys))
Proof
  fs [FUPDATE_LIST_THM, GSYM fmap_EQ_THM, FDOM_FUPDATE, FDOM_FUPDATE_LIST] >>
  rpt strip_tac
  >- (fs [pred_setTheory.EXTENSION] >> metis_tac []) >>
  fs [FUPDATE_LIST_APPLY_NOT_MEM_ZIP, FAPPLY_FUPDATE_THM] >>
  (Cases_on ‘MEM x xs’
   >- (match_mp_tac FUPDATE_SAME_LIST_APPLY >> simp [MAP_ZIP])
   >- rw [FUPDATE_LIST_APPLY_NOT_MEM_ZIP, FAPPLY_FUPDATE_THM])
QED


Theorem evaluate_seq_stores_mem_state_rel:
  !es vs ad a s res t addr m.
   LENGTH es = LENGTH vs /\ ~MEM ad es /\ ALL_DISTINCT es /\
   mem_stores (addr+a) vs s.memaddrs s.memory = SOME m /\
   evaluate (nested_seq (stores (Var ad) (MAP Var es) a),
             s with locals := s.locals |++
               ((ad,Word addr)::ZIP (es,vs))) = (res,t) ==>
   res = NONE ∧ t.memory = m ∧
   t.memaddrs = s.memaddrs ∧ (t.be ⇔ s.be) ∧
   t.ffi = s.ffi ∧ t.code = s.code /\ t.clock = s.clock
Proof
  Induct >> rpt gen_tac >> strip_tac >> rfs [] >> rveq
  >- fs [stores_def, nested_seq_def, evaluate_def,
         mem_stores_def, state_component_equality] >>
  cases_on ‘vs’ >> fs [] >>
  fs [mem_stores_def, CaseEq "option"] >>
  qmatch_asmsub_abbrev_tac ‘s with locals := lc’ >>
  ‘eval (s with locals := lc) (Var h) = SOME h'’ by (
    fs [Abbr ‘lc’, eval_def] >>
    fs [FUPDATE_LIST_THM] >>
    ‘~MEM h (MAP FST (ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘s.locals |+ (ad,Word addr)’] assume_tac) >>
   fs [FLOOKUP_UPDATE]) >>
  ‘lc |++ ((ad,Word addr)::ZIP (es,t')) = lc’ by (
    fs [Abbr ‘lc’] >> metis_tac [fm_multi_update]) >>
  fs [stores_def] >>
  FULL_CASE_TAC >> fs []
  >- (
   fs [nested_seq_def, evaluate_def] >>
   pairarg_tac >> fs [] >>
   ‘eval (s with locals := lc) (Var ad) = SOME (Word addr)’ by (
     fs [Abbr ‘lc’, eval_def] >>
     fs [Once FUPDATE_LIST_THM] >>
     ‘~MEM ad (MAP FST ((h,h')::ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘Word addr’, ‘s.locals’] assume_tac) >>
    fs [FLOOKUP_UPDATE]) >> fs [] >>
   rfs [] >> rveq >> fs [] >>
   last_x_assum (qspecl_then [‘t'’, ‘ad’, ‘bytes_in_word’] mp_tac) >> fs [] >>
   disch_then (qspec_then ‘s with <|locals := lc; memory := m'|>’ mp_tac) >> fs [] >>
   disch_then drule >> fs []) >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  ‘eval (s with locals := lc) (Op Add [Var ad; Const a]) = SOME (Word (addr+a))’ by (
    fs [eval_def, OPT_MMAP_def, Abbr ‘lc’] >>
    fs [Once FUPDATE_LIST_THM] >>
    ‘~MEM ad (MAP FST ((h,h')::ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘Word addr’, ‘s.locals’] assume_tac) >>
    fs [FLOOKUP_UPDATE, wordLangTheory.word_op_def]) >> fs [] >>
   rfs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   last_x_assum (qspecl_then [‘t'’, ‘ad’, ‘a + bytes_in_word’] mp_tac) >> fs [] >>
   disch_then (qspec_then ‘s with <|locals := lc; memory := m'|>’ mp_tac) >> fs [] >>
   disch_then drule >> fs []
QED

Theorem compile_Store:
  ^(get_goal "compile_prog _ (panLang$Store _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘stores (Var ad) (MAP Var temps) _’ >>
  ‘ALL_DISTINCT (ad::temps) ∧ LENGTH (ad::temps) = LENGTH (h::es)’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST, MEM_GENLIST]) >>
  ‘distinct_lists (ad::temps) (FLAT (MAP var_cexp (h::es)))’ by (
    unabbrev_all_tac >> fs [MAP] >>
    ‘ctxt.max_var + 1:: GENLIST (λx. SUC x + (ctxt.max_var + 1)) (LENGTH es) =
     GENLIST (λx. SUC x + ctxt.max_var) (SUC(LENGTH es))’ by (
     fs [GENLIST_CONS, o_DEF] >> fs [GENLIST_FUN_EQ])>>
    fs [] >> pop_assum kall_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw []
    >- (
     qpat_x_assum ‘compile_exp _ src = (_,_)’ mp_tac >>
     qpat_x_assum ‘eval _ src = _’ mp_tac >>
     drule eval_var_cexp_present_ctxt >>
     ntac 3 (disch_then drule) >>
     fs [MAP] >> disch_then drule >>
     rw [] >> fs [] >>
     rfs [] >>
     fs [locals_rel_def, ctxt_max_def] >>
     first_x_assum drule >> fs []) >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘h::es’, ‘ad::temps’, ‘t’,
                          ‘Word addr::flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  fs [state_rel_def] >>
  fs [Abbr ‘p’] >>
  assume_tac evaluate_seq_stores_mem_state_rel >>
  pop_assum (qspecl_then [‘temps’, ‘flatten value’, ‘ad’ ,‘0w’, ‘t’,
                          ‘q’, ‘r’, ‘addr’, ‘m’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule evaluate_seq_stroes_locals_eq >> strip_tac >> fs [] >>
  rfs [] >>
  fs [GSYM length_flatten_eq_size_of_shape] >>
  cases_on ‘FLOOKUP t.locals ad’
  >- (
   fs [res_var_def] >>
   fs [FUPDATE_LIST_THM] >>
   ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
     drule MAP_ZIP >>
     strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘Word addr’, ‘t.locals’] assume_tac) >>
   fs []  >>
   qpat_x_assum ‘~MEM ad temps’ assume_tac >>
   drule_all domsub_commutes_fupdate >>
   disch_then (qspec_then ‘t.locals’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [flookup_thm] >>
   drule DOMSUB_NOT_IN_DOM >> strip_tac >> fs [] >>

   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []) >>
  fs [res_var_def] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
    drule MAP_ZIP >>
    strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘x’, ‘t.locals |+ (ad,Word addr)’] assume_tac o GSYM) >>
   fs [flookup_thm] >>
   drule_all FUPDATE_ELIM >>
   strip_tac >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []
QED

Theorem compile_StoreByte:
  ^(get_goal "compile_prog _ (panLang$StoreByte _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  TOP_CASE_TAC >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  fs [flatten_def] >> rveq >>
  fs [evaluate_def] >> TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [state_rel_def]
QED


Theorem evaluate_seq_store_globals_res:
  !vars vs t a.
   ALL_DISTINCT vars ∧ LENGTH vars = LENGTH vs ∧ w2n a + LENGTH vs <= 32 ==>
   evaluate (nested_seq (store_globals a (MAP Var vars)),
             t with locals := t.locals |++ ZIP (vars,vs)) =
   (NONE,t with <|locals := t.locals |++ ZIP (vars,vs);
                  globals := t.globals |++ ZIP (GENLIST (λx. a + n2w x) (LENGTH vs), vs)|>)
Proof
  Induct >> rw []
  >- fs [store_globals_def, nested_seq_def, evaluate_def,
         FUPDATE_LIST_THM, state_component_equality] >>
  cases_on ‘vs’ >> fs [] >>
  fs [store_globals_def, nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def, FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (vars, t')))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘t.locals’] assume_tac) >>
  fs [FLOOKUP_UPDATE] >> rveq >>
  fs [set_globals_def] >>
  cases_on ‘t' = []’
  >- (
   rveq >> fs [] >> rveq >>
   fs [store_globals_def, nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM, state_component_equality]) >>
  qmatch_goalsub_abbrev_tac ‘nested_seq _, st’ >>
  last_x_assum (qspecl_then [‘t'’, ‘st’, ‘a + 1w’] mp_tac) >>
  fs [] >> impl_tac
  >- (
   fs [ADD1] >>
   qmatch_asmsub_abbrev_tac ‘m + (w2n a + 1) <= 32’ >>
   ‘0 < m’ by (fs [Abbr ‘m’] >> cases_on ‘t'’ >> fs []) >>
   ‘(w2n a + 1) <= 32 - m’ by DECIDE_TAC >>
   fs [w2n_plus1] >>
   FULL_CASE_TAC >>
   fs []) >>
  ‘st.locals |++ ZIP (vars,t') = st.locals’ by (
    fs [Abbr ‘st’] >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘h'’, ‘t.locals |++ ZIP (vars,t')’] assume_tac) >>
    fs [] >> metis_tac [FUPDATE_LIST_CANCEL, MEM_ZIP]) >>
  fs [Abbr ‘st’]  >> fs [] >> strip_tac >> fs [state_component_equality] >>
  fs [GENLIST_CONS, FUPDATE_LIST_THM, o_DEF, n2w_SUC]
QED


Theorem res_var_lookup_original_eq:
  !xs ys lc. ALL_DISTINCT xs ∧ LENGTH xs = LENGTH ys ==>
   FOLDL res_var (lc |++ ZIP (xs,ys)) (ZIP (xs,MAP (FLOOKUP lc) xs)) = lc
Proof
  Induct >> rw [] >- fs [FUPDATE_LIST_THM] >>
  fs [] >> cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs, t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘lc’] mp_tac) >>
  fs [] >> strip_tac >>
  cases_on ‘FLOOKUP lc h’ >> fs [] >>
  fs [res_var_def] >>
  qpat_x_assum ‘~MEM h xs’ assume_tac
  >- (
   drule domsub_commutes_fupdate >>
   disch_then (qspecl_then [‘t’, ‘lc’] mp_tac) >>
   fs [] >>
   metis_tac [flookup_thm, DOMSUB_NOT_IN_DOM]) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘x’, ‘lc’] assume_tac o GSYM) >>
  fs [] >>
  metis_tac [FUPDATE_ELIM, flookup_thm]
QED

(* strange function *)
Definition exps_def:
  (exps (Const w:'a crepLang$exp) = [Const w]) ∧
  (exps (Var v) = [Var v]) ∧
  (exps (Label f) = [Label f]) ∧
  (exps (Load e) = exps e) ∧
  (exps (LoadByte e) = exps e) ∧
  (exps (LoadGlob a) = [LoadGlob a]) ∧
  (exps (Op bop es) = FLAT (MAP exps es)) ∧
  (exps (Cmp c e1 e2) = exps e1 ++ exps e2) ∧
  (exps (Shift sh e num) = exps e)
Termination
  cheat
End


Theorem eval_exps_not_load_global_eq:
  !s e v g. eval s e = SOME v ∧
   (!ad. ~MEM (LoadGlob ad) (exps e))  ==>
    eval (s with globals := g) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- fs [eval_def]
  >- fs [eval_def]
  >- fs [eval_def]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def] >> rveq >> metis_tac [])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> metis_tac [])
  >- fs [exps_def, eval_def, CaseEq "option"]

  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def, ETA_AX] >>
   fs [eval_def, CaseEq "option", ETA_AX] >>
   qexists_tac ‘ws’ >>
   fs [opt_mmap_eq_some, ETA_AX,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   fs [MEM_FLAT, MEM_MAP] >>
   metis_tac [EL_MEM]) >>
  rpt gen_tac >>
  strip_tac >> fs [exps_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
QED


Theorem load_glob_not_mem_load:
  !i a h ad.
  ~MEM (LoadGlob ad) (exps h) ==>
  ~MEM (LoadGlob ad) (FLAT (MAP exps (load_shape a i h)))
Proof
  Induct >> rw [] >- fs [load_shape_def] >>
  fs [load_shape_def] >>
  TOP_CASE_TAC >> fs [MAP, load_shape_def, exps_def]
QED



Theorem compile_exp_not_mem_load_glob:
  ∀s e v (t :('a, 'b) state) ct es sh ad.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  ~MEM (LoadGlob ad) (FLAT (MAP exps es))
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def, compile_exp_def] >> rveq >>
   fs [exps_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   CCONTR_TAC >> fs [] >>
   FULL_CASE_TAC >> fs [] >> rveq >> fs [exps_def] >>
   FULL_CASE_TAC >> fs [] >> rveq >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >> fs [exps_def])
  >- (
   fs [compile_exp_def] >>
   CCONTR_TAC >> fs [] >>
   rveq >> fs [exps_def])
  >- (
   rpt strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> rw [] >>
   fs [OPT_MMAP_def] >> rveq
   >- (
    CCONTR_TAC >> fs [] >>
    cases_on ‘compile_exp ct h’ >> fs [] >>
    first_x_assum (qspec_then ‘h’ assume_tac) >> fs [] >>
    metis_tac []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >> rfs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >> rfs [] >>
   disch_then drule >> disch_then drule >>
   cases_on ‘FST (compile_exp ct h)’ >> fs [] >> rveq >>
   cases_on ‘compile_exp ct h’ >> fs [])
  >- (
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >- fs [exps_def] >>
   first_x_assum drule >> disch_then drule >>
   disch_then drule >>  disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >>
   CCONTR_TAC >> fs [] >>
   ‘!m. MEM m (FLAT (MAP exps es)) ==> MEM m (FLAT (MAP exps cexp))’
   suffices_by metis_tac [] >>
   pop_assum kall_tac >>  pop_assum kall_tac >>
   rw [] >> fs [MEM_FLAT, MEM_MAP] >> rveq >>
   drule mem_comp_field >>
   disch_then (qspecl_then [‘shapes’, ‘cexp’, ‘sh’, ‘y’, ‘es’] mp_tac) >>
   impl_tac
   >- (
    drule compile_exp_val_rel >> disch_then drule_all >> fs [] >>
    strip_tac >> rfs []) >>
   strip_tac >> metis_tac [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   FULL_CASE_TAC >> fs [] >> rveq >- fs [exps_def] >>
   first_x_assum drule >> disch_then drule >>
   disch_then drule >> disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >>
   CCONTR_TAC >> fs [] >>
   metis_tac [load_glob_not_mem_load])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
   drule compile_exp_val_rel >> disch_then drule_all >> fs [] >>
   strip_tac >> fs [panLangTheory.size_of_shape_def] >> rveq >>
   last_x_assum drule >> disch_then drule >> disch_then drule >>
   disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   FULL_CASE_TAC >> fs [] >> rveq >- fs [exps_def] >>
   fs [exps_def] >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   CCONTR_TAC >> fs [] >>
   fs [MAP_MAP_o] >>
   fs [EVERY_MEM] >>
   ‘EVERY (\x. LENGTH x = 1) (MAP (FST ∘ compile_exp ct) es)’ by (
     fs [EVERY_MEM] >>
     rw [] >>
     fs [MEM_MAP] >>
     cases_on ‘compile_exp ct y’ >> fs [] >>
     rveq >> drule opt_mmap_mem_func >>
     disch_then drule >>
     strip_tac >> fs [] >>
     drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
     drule opt_mmap_mem_defined >> disch_then drule >> fs [] >> strip_tac >>
     first_x_assum drule >>
     TOP_CASE_TAC >> fs [] >>  TOP_CASE_TAC >>
     fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
     fs [panLangTheory.size_of_shape_def]) >>
   ntac 7 (pop_assum mp_tac) >>
   ntac 2 (pop_assum kall_tac) >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘x’ ,‘ws’, ‘es’] >>
   Induct >> rpt gen_tac >> rpt strip_tac >>
   fs [OPT_MMAP_def] >> rveq >> fs []
   >- (
    last_x_assum mp_tac >>
    impl_tac >- metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >>
    impl_tac >- fs [] >>
    ntac 3 (disch_then drule) >>
    cases_on ‘compile_exp ct h’ >> fs [] >>
    cases_on ‘q’ >> fs [] >> metis_tac []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   impl_tac >- fs [] >>
   fs [EVERY_MEM])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
   cases_on ‘compile_exp ct e'’ >>
   cases_on ‘compile_exp ct e’ >> fs [] >> rveq >>
   drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
   qpat_x_assum ‘eval s e = SOME (ValWord w1)’ assume_tac >>
   drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
   fs [flatten_def] >>
   rveq >> fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
   last_x_assum drule >> last_x_assum drule >>
   rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
   strip_tac >>
   rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
   fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
      CaseEq "word_lab"] >> rveq >>
  fs [compile_exp_def] >> rveq >>
  every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
  cases_on ‘compile_exp ct e’ >> fs [] >> rveq >>
  drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
  qpat_x_assum ‘eval s e = SOME (ValWord w)’ assume_tac >>
  fs [flatten_def] >>
  rveq >> fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
  last_x_assum drule >>
  rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
  fs []
QED


Triviality el_reduc_tl:
  !l n. 0 < n ∧ n < LENGTH l ==> EL n l = EL (n-1) (TL l)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
QED



Theorem zero_not_mem_genlist_offset:
  !t. LENGTH t <= 31 ==>
  ~MEM 0w (MAP (n2w:num -> word5) (GENLIST (λi. i + 1) (LENGTH t)))
Proof
  Induct >> rw [] >>
  CCONTR_TAC >> fs [MEM_MAP, MEM_GENLIST] >> rveq >>
  fs [ADD1] >>
  ‘(i + 1) MOD 32 = i + 1’ by (
    match_mp_tac LESS_MOD >> DECIDE_TAC) >>
  fs []
QED


Theorem compile_Return_Raise:
  ^(get_goal "compile_prog _ (panLang$Return _)") /\
  ^(get_goal "compile_prog _ (panLang$Raise _)")
Proof
  rpt gen_tac >> rpt strip_tac >> (
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "bool"] >>
  rveq >> fs [] >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> rveq >> rfs [] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   fs [evaluate_def, eval_def] >>
   fs [state_rel_def,panSemTheory.empty_locals_def,
       empty_locals_def, state_component_equality]) >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   fs [evaluate_def, eval_def] >>
   fs [state_rel_def,panSemTheory.empty_locals_def,
       empty_locals_def, state_component_equality]) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def] >>
  qmatch_asmsub_abbrev_tac ‘nested_decs temps es p’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    fs [Abbr ‘temps’] >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten value’,
                          ‘nested_seq (store_globals 0w (MAP Var temps))’] mp_tac) >>
  impl_tac >- (unabbrev_all_tac >> fs []) >>
  fs [] >> pairarg_tac >> fs [] >> rveq >> strip_tac >> rveq >>
  fs [Abbr ‘p’] >>
  drule evaluate_seq_store_globals_res >>
  disch_then (qspecl_then [‘flatten value’, ‘t’, ‘0w’] mp_tac) >>
  fs [Abbr ‘es’, length_flatten_eq_size_of_shape] >>
  strip_tac >> fs [] >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``] res_var_lookup_original_eq) >>
  disch_then (qspecl_then [‘flatten value’, ‘t.locals’] assume_tac) >>
  rfs [length_flatten_eq_size_of_shape] >> rveq >>
  conj_tac
  >- fs [state_rel_def,panSemTheory.empty_locals_def,
         empty_locals_def, state_component_equality] >>
  conj_tac >- fs [empty_locals_def, panSemTheory.empty_locals_def] >>
  fs [empty_locals_def] >>
  qmatch_goalsub_abbrev_tac ‘t with <|locals := _; globals := g|>’ >>
  cases_on ‘flatten value’ >> fs [] >>
  fs [globals_lookup_def, Abbr ‘g’] >>
  qpat_x_assum ‘LENGTH temps = _’ (assume_tac o GSYM) >>
  fs [opt_mmap_eq_some] >>
  fs [] >>
  cases_on ‘temps = []’ >> fs [] >>
  ‘GENLIST (λx. (n2w x):word5) (LENGTH temps) = MAP n2w (0 :: [1 .. (LENGTH temps)-1])’ by (
    fs [GENLIST_eq_MAP] >>
    fs [listRangeINC_def] >> rw [] >>
    cases_on ‘0 < x’ >> fs [NOT_LT_ZERO_EQ_ZERO] >>
    drule (INST_TYPE [``:'a``|->``:num``] el_reduc_tl) >>
    disch_then (qspec_then ‘0::GENLIST (λi. i + 1) (LENGTH temps - 1)’ assume_tac) >> fs []) >>
  fs [] >> conj_tac
  >- (
   fs [FUPDATE_LIST_THM] >>
   ‘~MEM (0w:word5) (MAP FST (ZIP (MAP n2w [1 .. LENGTH temps - 1],t'')))’ by (
     once_rewrite_tac [listRangeINC_def] >> fs [] >>
     ‘LENGTH temps - 1 = LENGTH t''’ by rfs [GSYM length_flatten_eq_size_of_shape] >>
     fs [] >>
     qmatch_goalsub_abbrev_tac ‘ZIP (gn,_)’ >>
     ‘MAP FST (ZIP (gn,t'')) = gn’ by fs [Abbr ‘gn’, MAP_ZIP, LENGTH_GENLIST] >>
     fs [] >> fs [Abbr ‘gn’] >>
     match_mp_tac zero_not_mem_genlist_offset >> DECIDE_TAC) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘t.globals’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  fs [MAP_EQ_EVERY2] >> conj_tac >- fs [listRangeINC_def] >>
  fs [LIST_REL_EL_EQN] >> conj_tac >- fs [listRangeINC_def] >>
  fs [FUPDATE_LIST_THM] >> rw [] >>
  match_mp_tac update_eq_zip_flookup >>
  fs [] >> fs [listRangeINC_def] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw [] >> fs [ALL_DISTINCT_GENLIST] >>
  fs [MEM_GENLIST] >> rveq  >>
  ‘i < 32 ∧ i' < 32’ by fs [] >>
  rfs [])
QED


Theorem compile_Seq:
  ^(get_goal "compile_prog _ (panLang$Seq _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [compile_prog_def] >>
  fs [panSemTheory.evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘res' = NONE’ >> fs [] >>
  rveq  >> fs []
  >- (
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >>
   first_x_assum drule_all >> fs []) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>

  first_x_assum drule_all >> strip_tac >>
  fs [] >> rveq >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
  cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
QED


Theorem compile_If:
  ^(get_goal "compile_prog _ (panLang$If _ _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_prog_def] >>
  cases_on ‘eval s e’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  cases_on ‘w’ >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [flatten_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  last_x_assum drule_all >>
  strip_tac >> fs [] >>
  rfs [] >>
  cases_on ‘res’ >> fs [] >>
  rveq  >> fs [] >>
  cases_on ‘c = 0w’ >> fs []
QED

Theorem compile_While:
  ^(get_goal "compile_prog _ (panLang$While _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  cheat
QED


Theorem eval_map_comp_exp_flat_eq:
  !argexps args s t ctxt. MAP (eval s) argexps = MAP SOME args /\
  state_rel s t ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt s.locals t.locals ==>
   MAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) =
        MAP SOME (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs []) >>
  cases_on ‘args’ >> fs [] >>
  fs [MAP_APPEND] >>
  cases_on ‘compile_exp ctxt h’ >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  last_x_assum (qspecl_then [‘t'’] mp_tac) >>
  fs [] >>
  disch_then drule_all >>
  fs []
QED


Theorem code_rel_imp:
   code_rel ctxt s_code t_code ==>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ns. FLOOKUP ctxt.code_vars f = SOME (vshs, ns) /\
       ALL_DISTINCT ns /\
       let vs = MAP FST vshs;
           shs = MAP SND vshs;
           nctxt = <|var_nums := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
                     code_vars := ctxt.code_vars; max_var := list_max ns |> in
       size_of_shape (Comb shs) = LENGTH ns /\
       FLOOKUP t_code f = SOME (ns, compile_prog nctxt prog)
Proof
  fs [code_rel_def]
QED


Theorem list_rel_length_shape_of_flatten:
  !vshapes args ns.
  LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args /\
  size_of_shape (Comb (MAP SND vshapes)) = LENGTH ns ==>
  LENGTH ns = LENGTH (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs [panLangTheory.size_of_shape_def]) >>
  cases_on ‘args’ >> fs [] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  ‘size_of_shape (SND h) <= LENGTH ns’ by DECIDE_TAC >>
  last_x_assum (qspecl_then [‘t’,
                             ‘DROP (size_of_shape (SND h)) ns’] mp_tac) >>
  fs [] >> last_x_assum (assume_tac o GSYM) >>
  fs [] >>
  fs [length_flatten_eq_size_of_shape]
QED


Theorem code_rel_empty_locals:
  code_rel ctxt s.code t.code ==>
  code_rel ctxt (empty_locals s).code (empty_locals t).code
Proof
  fs [code_rel_def, empty_locals_def, panSemTheory.empty_locals_def]
QED



Theorem length_with_shape_eq_shape:
  !sh ns.
  LENGTH ns = size_of_shape (Comb sh) ==>
  LENGTH sh = LENGTH (with_shape sh ns)
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  fs [panLangTheory.size_of_shape_def]
QED


Theorem all_distinct_take:
  !ns n.
  ALL_DISTINCT ns /\ n <= LENGTH ns  ==>
  ALL_DISTINCT (TAKE n ns)
Proof
  Induct >> rw [] >> fs [] >>
  cases_on ‘n’ >> fs [TAKE] >>
   metis_tac [MEM_TAKE]
QED

Theorem all_distinct_drop:
  !ns n.
  ALL_DISTINCT ns /\ n <= LENGTH ns  ==>
  ALL_DISTINCT (DROP n ns)
Proof
  Induct >> rw [] >> fs [] >>
  cases_on ‘n’ >> fs [DROP] >>
   metis_tac [MEM_DROP]
QED

Theorem all_distinct_with_shape:
  !sh ns n.
  ALL_DISTINCT ns /\ n < LENGTH sh /\
  LENGTH ns = size_of_shape (Comb sh) ==>
  ALL_DISTINCT (EL n (with_shape sh ns))
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [panLangTheory.size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >>
   drule all_distinct_take >> fs []) >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’] mp_tac) >>
  impl_tac
  >- (
   fs [panLangTheory.size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >>
   drule all_distinct_drop >> fs []) >> fs []
QED

Theorem el_mem_with_shape:
  !sh ns n x.
  n < LENGTH (with_shape sh ns) /\
  LENGTH ns = size_of_shape (Comb sh) /\
  MEM x (EL n (with_shape sh ns)) ==>
  MEM x ns
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [panLangTheory.size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >> drule MEM_TAKE >> fs []) >>
  fs [panLangTheory.size_of_shape_def] >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’, ‘x’] mp_tac) >>
  fs [] >>
  strip_tac >> drule MEM_DROP_IMP >>
  fs []
QED


Theorem disjoint_take_drop_sum:
  !n m p ns.
   ALL_DISTINCT ns ==>
   DISJOINT (set (TAKE n ns)) (set (TAKE p (DROP (n + m) ns)))
Proof
  Induct >> rw [] >>
  cases_on ‘ns’ >> fs [LESS_EQ_ADD_SUB, SUC_SUB1] >>
  CCONTR_TAC >> fs [] >>
  drule MEM_TAKE_IMP >>
  strip_tac >>
  drule MEM_DROP_IMP >> fs []
QED


Theorem disjoint_drop_take_sum:
  !n m p ns.
   ALL_DISTINCT ns ==>
   DISJOINT (set (TAKE p (DROP (n + m) ns))) (set (TAKE n ns))
Proof
  Induct >> rw [] >>
  cases_on ‘ns’ >> fs [LESS_EQ_ADD_SUB, SUC_SUB1] >>
  CCONTR_TAC >> fs [] >>
  drule MEM_TAKE_IMP >>
  strip_tac >>
  drule MEM_DROP_IMP >> fs []
QED


Theorem mem_with_shape_length:
  !sh ns n.
   LENGTH ns = size_of_shape (Comb sh) ∧ n < LENGTH sh ==>
   MEM (EL n (with_shape sh ns)) (with_shape sh ns)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs [] >>
  fs [with_shape_def] >>
  disj2_tac >>
  first_x_assum match_mp_tac >>
  fs [panLangTheory.size_of_shape_def]
QED

Theorem with_shape_el_take_drop_eq:
 !sh ns n.
   LENGTH ns = size_of_shape (Comb sh) ∧
    n < LENGTH sh ==>
    EL n (with_shape sh ns) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh))) ns)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
  >- fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’] mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >> fs [DROP_DROP_T]
QED

Theorem all_distinct_with_shape_distinct:
  !sh ns x y.
   ALL_DISTINCT ns ∧ LENGTH ns = size_of_shape (Comb sh) ∧
   MEM x (with_shape sh ns) ∧ MEM y (with_shape sh ns) ∧ x <> y ∧
   x <> [] ∧ y <> [] ==>
   DISJOINT (set x) (set y)
Proof
  Induct >> rw [] >>
  fs [with_shape_def]
  >- (
   cases_on ‘size_of_shape h = 0’ >> fs [] >>
   ‘x = y’ suffices_by fs [] >>
   ‘size_of_shape h <= LENGTH ns’ by
     fs [panLangTheory.size_of_shape_def] >>
   qpat_x_assum ‘x ≠ y’ kall_tac >>
   fs [TAKE])
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [panLangTheory.size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [panLangTheory.size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_take_drop_sum >>
   fs [])
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [panLangTheory.size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [panLangTheory.size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_drop_take_sum >>
   fs []) >>
  last_x_assum (qspec_then ‘DROP (size_of_shape h) ns’ mp_tac) >>
  disch_then (qspecl_then [‘x’,‘y’] mp_tac) >>
  impl_tac
  >- fs [ALL_DISTINCT_DROP, panLangTheory.size_of_shape_def] >>
  fs []
QED


Theorem all_distinct_disjoint_with_shape:
  !sh ns n n'.
   ALL_DISTINCT ns /\ n < LENGTH sh /\ n' < LENGTH sh /\
   n <> n' /\
   LENGTH ns = size_of_shape (Comb sh) ==>
   DISJOINT (set (EL n (with_shape sh ns))) (set (EL n' (with_shape sh ns)))
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> cases_on ‘n'’ >> fs []
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [panLangTheory.size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [panLangTheory.size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_take_drop_sum >>
   fs [])
  >- (
   fs [MEM_EL] >>
   ‘EL n'' (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n'' sh)) (DROP (size_of_shape (Comb (TAKE n'' sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [panLangTheory.size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [panLangTheory.size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_drop_take_sum >>
   fs []) >>
  last_x_assum match_mp_tac >>
  fs [panLangTheory.size_of_shape_def, ALL_DISTINCT_DROP]
QED


Theorem all_distinct_mem_zip_disjoint_with_shape:
  LENGTH l = LENGTH sh /\ LENGTH sh = LENGTH (with_shape sh ns) /\
  ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
  MEM (x,a,xs) (ZIP (l,ZIP (sh,with_shape sh ns))) /\
  MEM (y,b,ys) (ZIP (l,ZIP (sh,with_shape sh ns))) /\
  x ≠ y ==>
   DISJOINT (set xs) (set ys)
Proof
  rw [] >>
  ‘LENGTH l = LENGTH (ZIP (sh,with_shape sh ns))’ by fs [] >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(x,a,xs)’ assume_tac) >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(y,b,ys)’ assume_tac) >>
  fs [] >> rveq >>
  cases_on ‘n = n'’ >> fs [] >>
  drule EL_ZIP >> drule EL_ZIP >>
  disch_then (qspec_then ‘n’ assume_tac) >>
  disch_then (qspec_then ‘n'’ assume_tac) >>
  rfs [] >> rveq >> fs [] >>
  match_mp_tac all_distinct_disjoint_with_shape >>
  fs []
QED


Theorem fm_empty_zip_alist:
  !xs ys. LENGTH xs = LENGTH ys /\
  ALL_DISTINCT xs ==>
  FEMPTY |++ ZIP (xs,ys) =
  alist_to_fmap (ZIP (xs,ys))
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  last_x_assum (qspecl_then [‘t’] assume_tac) >>
  fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  match_mp_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  CCONTR_TAC >> fs [MEM_MAP] >> rveq >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘y’ mp_tac) >>
  strip_tac >> fs [] >> rveq >> fs [FST] >>
  fs [MEM_EL] >> metis_tac  []
QED

Theorem fm_empty_zip_flookup:
  !xs ys x y.
  LENGTH xs = LENGTH ys /\ ALL_DISTINCT xs /\
  FLOOKUP (FEMPTY |++ ZIP (xs,ys)) x = SOME y ==>
  ?n. n < LENGTH xs /\ EL n (ZIP (xs,ys)) = (x,y)
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  cases_on ‘x = h’ >> fs [] >> rveq
  >- (
   qexists_tac ‘0’ >> fs [] >>
   ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
     metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
  fs [] >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum (qspec_then ‘t’ mp_tac) >>
  fs [] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  qexists_tac ‘SUC n’ >> fs []
QED

Theorem fm_empty_zip_flookup_el:
  !xs ys zs n x.
   ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ LENGTH ys = LENGTH zs /\
   n < LENGTH xs /\ EL n xs = x ==>
    FLOOKUP (FEMPTY |++ ZIP (xs,ZIP (ys,zs))) x = SOME (EL n ys,EL n zs)
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> cases_on ‘zs’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  cases_on ‘n’ >> fs []
  >- (
   ‘~MEM h (MAP FST (ZIP (xs,ZIP (t,t'))))’ by (
     ‘LENGTH xs = LENGTH (ZIP (t,t'))’ by fs [] >>
     metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL]) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘(h', h'')’, ‘FEMPTY’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  ‘~MEM h (MAP FST (ZIP (xs,ZIP (t,t'))))’ by (
    ‘LENGTH xs = LENGTH (ZIP (t,t'))’ by fs [] >>
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL]) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘(h', h'')’, ‘FEMPTY’] assume_tac) >>
  fs [] >>
  fs [FLOOKUP_UPDATE] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> drule EL_MEM >> fs []
QED


Theorem all_distinct_alist_no_overlap:
  ALL_DISTINCT (ns:num list) /\
  LENGTH ns = size_of_shape (Comb (MAP SND (q:(mlstring # shape) list))) ⇒
  no_overlap (alist_to_fmap (ZIP (MAP FST q,ZIP (MAP SND q,with_shape (MAP SND q) ns))))
Proof
  rw [] >>
  fs [no_overlap_def] >>
  conj_tac
  >- (
   rw [] >>
   drule ALOOKUP_MEM >>
   strip_tac >> fs [] >>
   drule length_with_shape_eq_shape >>
   strip_tac >>
   drule LENGTH_ZIP >>
   strip_tac >> fs [] >>
   ‘LENGTH (MAP FST q) = LENGTH (ZIP (MAP SND q,with_shape (MAP SND q) ns))’ by fs [] >>
   drule MEM_ZIP >>
   disch_then (qspec_then ‘(x,a,xs)’ mp_tac) >>
   strip_tac >> fs [] >> rveq >>
   ‘LENGTH (MAP SND q) = LENGTH (with_shape (MAP SND q) ns)’ by fs [] >>
   drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >> fs [] >>
   match_mp_tac all_distinct_with_shape >>
   fs []) >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  dxrule ALOOKUP_MEM >>
  dxrule ALOOKUP_MEM >>
  rpt strip_tac >>
  ‘LENGTH (MAP FST q) = LENGTH (MAP SND q)’ by fs [] >>
  ‘LENGTH ns = size_of_shape (Comb (MAP SND q))’ by fs [] >>
  drule length_with_shape_eq_shape >>
  strip_tac >>
  drule length_with_shape_eq_shape >>
  drule (INST_TYPE [``:'b``|->``:num``] all_distinct_mem_zip_disjoint_with_shape) >>
  disch_then (qspecl_then [‘ys’, ‘y’, ‘xs’, ‘x’, ‘ns’, ‘b’, ‘a’] assume_tac) >>
  rfs []
QED

Theorem all_distinct_alist_ctxt_max:
  ALL_DISTINCT (ns:num list) /\
  LENGTH ns = size_of_shape (Comb (MAP SND (q:(mlstring # shape) list))) ⇒
   ctxt_max (list_max ns)
      (alist_to_fmap (ZIP (MAP FST q,ZIP (MAP SND q,with_shape (MAP SND q) ns))))
Proof
  rw [] >> fs [ctxt_max_def] >>
  rw [] >>
  ‘MEM x ns’ suffices_by (
             assume_tac list_max_max >>
             pop_assum (qspec_then ‘ns’ assume_tac) >>
             fs [EVERY_MEM]) >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  ‘LENGTH ns = size_of_shape (Comb (MAP SND q))’ by fs [] >>
  drule length_with_shape_eq_shape >>
  strip_tac >>
  drule LENGTH_ZIP >>
  strip_tac >> fs [] >>
  ‘LENGTH (MAP FST q) = LENGTH (ZIP (MAP SND q,with_shape (MAP SND q) ns))’ by fs [] >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(v,a,xs)’ mp_tac) >>
  strip_tac >> fs [] >>
  rveq >> ‘LENGTH (MAP SND q) = LENGTH (with_shape (MAP SND q) ns)’ by fs [] >>
  drule EL_ZIP >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >> fs [] >> rveq >>
  drule el_mem_with_shape >>
  fs []
QED

Theorem list_rel_flatten_with_shape_length:
  !sh ns args v n.
  LENGTH ns = LENGTH (FLAT (MAP flatten args))/\
  size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
  EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
  LIST_REL (λsh arg. sh = shape_of arg) sh args ==>
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)
Proof
  Induct >> rw []
  >- fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  cases_on ‘n’ >> fs []
  >-  fs [length_flatten_eq_size_of_shape] >>
  last_x_assum match_mp_tac >>
  ‘LENGTH (flatten arg) = size_of_shape (shape_of arg)’ by
    fs [length_flatten_eq_size_of_shape] >>
  fs []
QED

Theorem all_distinct_take_frop_disjoint:
  !ns n.
   ALL_DISTINCT ns ∧ n <= LENGTH ns ==>
  DISJOINT (set (TAKE n ns)) (set (DROP n ns))
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs [] >>
  CCONTR_TAC >> fs [] >>
  fs[MEM_DROP, MEM_EL] >>
  metis_tac []
QED

Theorem fupdate_flookup_zip_elim:
  !xs ys zs as x.
   FLOOKUP (FEMPTY |++ ZIP (xs, ys)) x = NONE ∧
   LENGTH zs = LENGTH as ∧ LENGTH xs = LENGTH ys /\
   ALL_DISTINCT xs ==>
   FLOOKUP (FEMPTY |++ ZIP (xs, ys) |++ ZIP (zs, as)) x =  FLOOKUP (FEMPTY |++ ZIP (zs, as)) x
Proof
  Induct >> rw []
  >- (fs [FUPDATE_LIST_THM]) >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘FLOOKUP (FEMPTY |++ ZIP (xs,t)) x = NONE’ by (
    ‘~MEM h (MAP FST (ZIP (xs,t)))’ by (
      CCONTR_TAC >> fs [MAP_ZIP, MEM_MAP] >> drule MEM_ZIP >>
      disch_then (qspec_then ‘y’ assume_tac) >> fs [] >> rveq >> rfs [MEM_EL] >>
      metis_tac []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs []) >>
  ‘FLOOKUP (FEMPTY |+ (h,h') |++ ZIP (xs,t) |++ ZIP (zs,as)) x =
   FLOOKUP (FEMPTY |++ ZIP (xs,t) |++ ZIP (zs,as)) x’ by (
    cases_on ‘FLOOKUP (FEMPTY |++ ZIP (xs,t) |++ ZIP (zs,as)) x’ >> fs []
    >- fs [flookup_update_list_none] >>
    fs [flookup_update_list_some]) >>
  fs [] >>
  last_x_assum match_mp_tac >> fs []
QED

Theorem not_mem_fst_zip_flookup_empty:
  !xs ys x.
   ~MEM x xs ∧ ALL_DISTINCT xs ∧
   LENGTH xs = LENGTH ys ==>
   FLOOKUP (FEMPTY |++ ZIP (xs, ys)) x = NONE
Proof
  Induct >> rw []
  >- (fs [FUPDATE_LIST_THM]) >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by (
    CCONTR_TAC >> fs [MAP_ZIP, MEM_MAP] >> drule MEM_ZIP >>
    disch_then (qspec_then ‘y’ assume_tac) >> fs [] >> rveq >> rfs [MEM_EL] >>
    metis_tac []) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
  fs [FLOOKUP_UPDATE]
QED


Theorem fm_zip_append_take_drop:
  !xs ys zs f.
   ALL_DISTINCT xs ∧ LENGTH xs = LENGTH (ys ++ zs) ==>
   f |++ ZIP (xs,ys ++ zs) = f |++ ZIP (TAKE (LENGTH ys) xs,ys)
                               |++ ZIP (DROP (LENGTH ys) xs,zs)
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [FUPDATE_LIST_THM]
QED

Theorem disjoint_not_mem_el:
  !xs ys n.
   DISJOINT (set xs) (set ys) ∧ n < LENGTH xs ==>
   ~MEM (EL n xs) ys
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
QED

Theorem list_rel_flatten_with_shape_flookup:
  !sh ns args v n n'.
  ALL_DISTINCT ns ∧ LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
  size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
  EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
  LIST_REL (λsh arg. sh = shape_of arg) sh args /\
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v) /\
  n' < LENGTH (EL n (with_shape sh ns)) ==>
   FLOOKUP (FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)))
     (EL n' (EL n (with_shape sh ns))) =
   SOME (EL n' (flatten v))
Proof
  Induct >> rw []
  >- fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  fs [with_shape_def, panLangTheory.size_of_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   ‘FLOOKUP (FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)))
    (EL n' (TAKE (size_of_shape (shape_of arg)) ns)) =
    SOME (EL n' (flatten arg ++ FLAT (MAP flatten ys)))’ by (
     ‘size_of_shape (shape_of arg) = LENGTH (flatten arg)’ by
       fs [length_flatten_eq_size_of_shape] >>
     fs [] >>
     ‘EL n' (flatten arg ++ FLAT (MAP flatten ys)) = EL n' (flatten arg)’ by (
       match_mp_tac EL_APPEND1 >> fs []) >>
     fs [] >>
     ‘FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns ++ DROP (LENGTH (flatten arg)) ns,
                      flatten arg ++ FLAT (MAP flatten ys)) =
      FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys))’ by (
       drule ZIP_APPEND >>
       disch_then (qspecl_then [‘DROP (LENGTH (flatten arg)) ns’, ‘FLAT (MAP flatten ys)’]mp_tac) >>
       impl_tac >- fs [] >>
       strip_tac >> pop_assum (assume_tac o GSYM) >>
       fs [] >>
       fs [FUPDATE_LIST_APPEND]) >>
     fs [] >> pop_assum kall_tac >>
     ‘FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys)) =
      FEMPTY  |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys)) |++
      ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg)’ by (
       match_mp_tac FUPDATE_LIST_APPEND_COMMUTES >>
       fs [MAP_ZIP] >> match_mp_tac all_distinct_take_frop_disjoint >> fs []) >>
     fs [] >> pop_assum kall_tac >>
     match_mp_tac update_eq_zip_flookup >>
     fs [] >>
     match_mp_tac all_distinct_take >>
     fs []) >>
   fs [] >>
   pop_assum kall_tac >>
   metis_tac [EL_APPEND1]) >>
  ‘FLOOKUP (FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)))
    (EL n'
     (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns))))  =
    FLOOKUP (FEMPTY |++ ZIP (DROP (size_of_shape (shape_of arg)) ns,FLAT (MAP flatten ys)))
    (EL n'
     (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns))))’ by (
    ‘FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)) =
     FEMPTY  |++
     ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
     ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys))’ by (
      match_mp_tac fm_zip_append_take_drop >>
      fs []) >>
    fs [] >> pop_assum kall_tac >>
    ‘FLOOKUP
     (FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg))
     (EL n'
      (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns)))) = NONE’ by (
      match_mp_tac not_mem_fst_zip_flookup_empty >>
      fs [] >> drule all_distinct_take >> disch_then (qspec_then ‘LENGTH (flatten arg)’ assume_tac) >>
      fs [] >>
      CCONTR_TAC >> fs [] >>
      fs [GSYM length_flatten_eq_size_of_shape] >>
      ‘TAKE (LENGTH (flatten arg)) ns =
       EL 0 (with_shape (shape_of arg::sh) ns)’ by
        fs [with_shape_def, length_flatten_eq_size_of_shape] >>
      ‘EL n'' (with_shape sh (DROP (LENGTH (flatten arg)) ns)) =
       EL (SUC n'') (with_shape (shape_of arg::sh) ns)’ by
        fs [with_shape_def, length_flatten_eq_size_of_shape] >>
      drule all_distinct_disjoint_with_shape >>
      disch_then (qspecl_then [‘shape_of arg::sh’, ‘SUC n''’, ‘0’] mp_tac) >>
      impl_tac >- fs [length_flatten_eq_size_of_shape, panLangTheory.size_of_shape_def] >>
      strip_tac >> fs [] >> drule disjoint_not_mem_el >> metis_tac []) >>
    drule fupdate_flookup_zip_elim >>
    disch_then (qspecl_then [‘DROP (LENGTH (flatten arg)) ns’, ‘FLAT (MAP flatten ys)’] mp_tac) >>
    impl_tac >- (fs [] >> match_mp_tac all_distinct_take >> fs []) >>
    fs [] >> strip_tac >>
    fs [length_flatten_eq_size_of_shape]) >>
  fs [] >>
  pop_assum kall_tac >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape (shape_of arg)) ns’,
                             ‘ys’, ‘n''’, ‘n'’] mp_tac) >>
  impl_tac >-  fs [ALL_DISTINCT_DROP, GSYM length_flatten_eq_size_of_shape] >> fs []
QED


Theorem ctxt_max_el_leq:
  ctxt_max ctxt.max_var ctxt.var_nums /\
  FLOOKUP ctxt.var_nums v = SOME (sh,ns) /\
  n < LENGTH ns ==> EL n ns <= ctxt.max_var
Proof
  rw [ctxt_max_def] >>
  first_x_assum drule >>
  disch_then (qspec_then ‘EL n ns’ assume_tac) >>
  drule EL_MEM >>
  fs []
QED

Theorem evaluate_seq_assign_load_globals:
  !ns t a.
  ALL_DISTINCT ns /\ w2n a + LENGTH ns <= 32 /\
  (!n. MEM n ns ==> FLOOKUP t.locals n <> NONE) /\
  (!n. MEM n (GENLIST (λx. a + n2w x) (LENGTH ns)) ==> FLOOKUP t.globals n <> NONE) ==>
  evaluate (nested_seq (MAP2 Assign ns (load_globals a (LENGTH ns))), t) =
  (NONE, t with locals := t.locals |++
           ZIP (ns, MAP (\n. THE (FLOOKUP t.globals n)) (GENLIST (λx. a + n2w x) (LENGTH ns))))
Proof
  Induct >> rw []
  >- (
   fs [nested_seq_def, evaluate_def] >>
   fs [FUPDATE_LIST_THM, state_component_equality]) >>
  fs [nested_seq_def, GENLIST_CONS, load_globals_def] >>
  fs [evaluate_def] >> pairarg_tac >> fs [] >>
  fs [eval_def] >>
  cases_on ‘FLOOKUP t.globals a’
  >- (
   first_assum (qspec_then ‘a’ mp_tac) >>
   fs []) >>
  fs [] >>
  cases_on ‘FLOOKUP t.locals h’
  >- (
   first_assum (qspec_then ‘h’ mp_tac) >>
   fs []) >>
  fs [] >> rveq >>
  fs [FUPDATE_LIST_THM] >>
  last_x_assum (qspecl_then [‘t with locals := t.locals |+ (h,x)’, ‘a + 1w’] mp_tac) >>
  impl_tac
  >- (
   conj_tac
   >- (
    ‘w2n a <= 31 - LENGTH ns’ by fs [] >>
    cases_on ‘a = 31w:word5’ >> fs [] >>
    ‘w2n (a + 1w) = w2n a + 1’ by (
      fs [w2n_plus1] >>
      FULL_CASE_TAC >> fs []) >>
    fs []) >>
   conj_tac
   >- (
    rw [] >> fs [FLOOKUP_UPDATE] >>
    TOP_CASE_TAC >> fs []) >>
   rw [] >> fs [MEM_GENLIST] >>
   first_x_assum match_mp_tac >>
   disj2_tac >> fs [] >>
   qexists_tac ‘x''’ >> fs [] >>
   fs [n2w_SUC]) >>
  strip_tac >> fs [] >>
  fs [state_component_equality] >>
  ‘GENLIST (λx. a + n2w x + 1w) (LENGTH ns)=
   GENLIST ((λx. a + n2w x) ∘ SUC) (LENGTH ns)’
  suffices_by fs [] >>
  fs [GENLIST_FUN_EQ] >>
  rw [] >>
  fs [n2w_SUC]
QED

Theorem local_rel_gt_max_var_preserved:
  !ct l l' n v.
  locals_rel ct l l' /\ ct.max_var < n ==>
  locals_rel ct l (l' |+ (n,v))
Proof
  rw [] >>
  fs [locals_rel_def] >>
  rw [] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' ns <= ct.max_var’ by (
    drule ctxt_max_el_leq >> metis_tac []) >>
  fs [FLOOKUP_UPDATE]
QED

Theorem local_rel_le_zip_update_preserved:
  !ct l l' x v sh ns v'.
  locals_rel ct l l' /\
  FLOOKUP l x = SOME v /\
  FLOOKUP ct.var_nums x = SOME (sh,ns) /\
  shape_of v = shape_of v' ∧ ALL_DISTINCT ns  ==>
  locals_rel ct (l |+ (x,v')) (l' |++ ZIP (ns,flatten v'))
Proof
  rw [] >>
  drule_all locals_rel_lookup_ctxt >>
  strip_tac >> fs [] >>
  fs [locals_rel_def] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  first_x_assum drule_all >> fs []
  >- (
   match_mp_tac opt_mmap_some_eq_zip_flookup >>
   fs [opt_mmap_eq_some, MAP_EQ_EVERY2,
       length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  match_mp_tac opt_mmap_disj_zip_flookup >>
  fs [length_flatten_eq_size_of_shape] >>
  fs [no_overlap_def] >>
  first_x_assum (qspecl_then [‘x’, ‘vname’, ‘shape_of v’,
                              ‘shape_of v''’, ‘ns’, ‘ns''’] mp_tac) >>
  fs []  >> fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
  metis_tac []
QED


Theorem map_some_the_map:
  !xs ys f.
  MAP f xs = MAP SOME ys ==>
  MAP (λn. THE (f n)) xs = ys
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs []
QED

Theorem state_code_locals_rel_preserved_call:
   ALL_DISTINCT (MAP FST vshs) /\
   LIST_REL (λvshape arg. SND vshape = shape_of arg) vshs args /\
   state_rel s t /\
   code_rel ctxt s.code t.code  /\
   locals_rel ctxt s.locals t.locals  /\
   FLOOKUP s.code fname = SOME (vshs,prog)  /\
   FLOOKUP ctxt.code_vars fname = SOME (vshs,ns)  /\
   ALL_DISTINCT ns  /\
   size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))  /\
   FLOOKUP t.code fname =
   SOME
     (ns,
      compile_prog
        <|var_nums :=
            FEMPTY |++
            ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns));
          code_vars := ctxt.code_vars; max_var := list_max ns|> prog)  /\
   LENGTH ns = LENGTH (FLAT (MAP flatten args)) ==>
   state_rel (dec_clock s with locals := FEMPTY |++ ZIP (MAP FST vshs,args))
     (dec_clock t with locals := FEMPTY |++ ZIP (ns,FLAT (MAP flatten args))) ∧
   code_rel
     <|var_nums :=
         FEMPTY |++ ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns));
       code_vars := ctxt.code_vars; max_var := list_max ns|>
     (dec_clock s).code (dec_clock t).code ∧
   locals_rel
     <|var_nums :=
         FEMPTY |++ ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns));
       code_vars := ctxt.code_vars; max_var := list_max ns|>
     (FEMPTY |++ ZIP (MAP FST vshs,args))
     (FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)))
Proof
  strip_tac >> fs [] >>
  conj_tac >- fs [state_rel_def, dec_clock_def, panSemTheory.dec_clock_def] >>
  conj_tac
  >- (
   fs [code_rel_def] >>
   rw [] >>
   fs [panSemTheory.dec_clock_def] >>
   last_x_assum drule_all >>
   fs [dec_clock_def]) >>
  fs [locals_rel_def] >>
  conj_tac (* replicating because needs to preserve fm in the third conjunct *)
  >- (
   ‘FEMPTY |++
    ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)) =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [] >>
   metis_tac [all_distinct_alist_no_overlap]) >>
  conj_tac
  >- (
   ‘FEMPTY |++
    ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)) =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [] >>
   match_mp_tac all_distinct_alist_ctxt_max >> fs []) >>
  rw [] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by (drule LIST_REL_LENGTH >> fs []) >>
  drule fm_empty_zip_flookup >> fs [] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  qexists_tac ‘EL n (with_shape (MAP SND vshs) ns)’ >>
  conj_tac
  >- (
   ‘FLOOKUP (FEMPTY |++ ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns))) vname =
    SOME (EL n (MAP SND vshs),EL n (with_shape (MAP SND vshs) ns))’ by (
     match_mp_tac fm_empty_zip_flookup_el >>
     fs [] >> ‘LENGTH ns = size_of_shape (Comb (MAP SND vshs))’ by fs [] >>
     drule length_with_shape_eq_shape >> fs [] >> strip_tac >>
     ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
     disch_then (qspec_then ‘n’ mp_tac) >> fs []) >>
   fs [] >>
   ‘n < LENGTH (MAP FST vshs)’ by fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >>
   drule EL_ZIP >>
   disch_then (qspec_then ‘n’ assume_tac) >>
   rfs [] >> rveq >>
   fs [LIST_REL_EL_EQN] >>
   last_x_assum drule >> fs [EL_MAP]) >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rewrite_tac [LIST_REL_EL_EQN] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rw [] >> match_mp_tac list_rel_flatten_with_shape_flookup >> fs [] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
  disch_then (qspec_then ‘n’ mp_tac) >> fs [] >> strip_tac >>
  fs [EVERY2_MAP] >>
  match_mp_tac list_rel_flatten_with_shape_length >>
  qexists_tac ‘args’ >> fs [] >>
  fs [EVERY2_MAP]
QED

Theorem compile_Call:
  ^(get_goal "compile_prog _ (panLang$Call _ _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_prog_def] >>
  fs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [flatten_def] >> rveq >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq
  >- (
   TOP_CASE_TAC >> fs [] >> rveq
   >- (
    fs [evaluate_def] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    strip_tac >>
    drule code_rel_empty_locals >>
    fs [state_rel_def, panSemTheory.empty_locals_def, empty_locals_def])
   >- (
    cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
    TOP_CASE_TAC >> fs []
    >- (drule_all locals_rel_lookup_ctxt >> fs []) >>
    TOP_CASE_TAC >> fs [] >> TOP_CASE_TAC >> fs []
    >- (
     TOP_CASE_TAC >> fs []
     >- (
      drule_all locals_rel_lookup_ctxt >> strip_tac >>
      fs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def]) >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     drule code_rel_empty_locals >>
     fs [state_rel_def, panSemTheory.empty_locals_def, empty_locals_def]) >>
    TOP_CASE_TAC >> fs []
    >- (
     drule_all locals_rel_lookup_ctxt >> strip_tac >>
     fs [] >> rveq  >>
     ‘LENGTH ns = 1’ by fs [shape_of_def, panLangTheory.size_of_shape_def,
                            length_flatten_eq_size_of_shape]  >>
     cases_on ‘ns’ >> fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     fs [state_rel_def, panSemTheory.empty_locals_def, empty_locals_def]) >>
    fs [nested_seq_def] >>
    fs [evaluate_def] >>
    pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >> rveq >>
    fs [panSemTheory.lookup_code_def] >>
    cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    strip_tac >> fs [] >>
    fs [state_rel_def] >> rveq >> rfs [] >>
    rveq >> fs [] >>
    drule code_rel_empty_locals >> fs [panSemTheory.empty_locals_def, empty_locals_def]) >>
   fs [evaluate_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
   disch_then (qspec_then ‘ns’ mp_tac) >>
   fs [] >>
   strip_tac >>
   drule code_rel_empty_locals >>
   fs [state_rel_def, panSemTheory.empty_locals_def, empty_locals_def]) >>
  TOP_CASE_TAC >> fs []
  >- (
   fs [evaluate_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def] >>
   cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
   disch_then (qspec_then ‘ns’ mp_tac) >>
   fs [] >>
   strip_tac >>
   TOP_CASE_TAC >- fs [state_rel_def] >>
   cases_on ‘evaluate
             (prog,
              dec_clock s with locals := FEMPTY |++ ZIP (MAP FST q,args))’ >>
   fs [] >>
   cases_on ‘q'’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
   first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
   impl_tac >>
   TRY (
   fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
   match_mp_tac state_code_locals_rel_preserved_call >>
   fs [])
   >- (
    strip_tac >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def, code_rel_def])
   >- (
    strip_tac >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def,
        code_rel_def, globals_lookup_def])
   >- (
    strip_tac >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def,
        code_rel_def, globals_lookup_def]) >>
   strip_tac >>
   fs [Abbr ‘nctxt’, state_rel_def,
       empty_locals_def, panSemTheory.empty_locals_def, code_rel_def])
   (* Return case *)
  >- (
   cases_on ‘evaluate (prog,dec_clock s with locals := newlocals)’ >>
   cases_on ‘q’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   TRY (cases_on ‘FLOOKUP s.locals m’ >> fs [] >> NO_TAC)
   >- (
    cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
    TOP_CASE_TAC
    >- (fs [locals_rel_def] >> first_x_assum drule >> fs []) >>
    TOP_CASE_TAC  >>
    TOP_CASE_TAC
    >- (
     TOP_CASE_TAC
     >- (
      fs [locals_rel_def] >> first_x_assum drule >> fs [] >>
      fs [OPT_MMAP_def] >>
      strip_tac >> fs [] >>
      pop_assum (assume_tac o GSYM) >>
      ‘size_of_shape (shape_of x) = 1’ by
        fs [panLangTheory.size_of_shape_def, shape_of_def] >>
      fs [GSYM length_flatten_eq_size_of_shape] >> rfs [flatten_def]) >>
     fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >> rveq >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
     strip_tac >> fs [] >>
     fs [Abbr ‘nctxt’, state_rel_def,
         empty_locals_def, panSemTheory.empty_locals_def, code_rel_def]) >>
    TOP_CASE_TAC >> fs []
    >- (
     ‘LENGTH r' = 1’ by (
       drule_all locals_rel_lookup_ctxt >> strip_tac >>
       fs [length_flatten_eq_size_of_shape] >>
       rfs [panLangTheory.size_of_shape_def]) >>
     cases_on ‘r'’ >> fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     fs [] >> rveq >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
     strip_tac >>
     fs [state_rel_def, Abbr ‘nctxt’, code_rel_def,
         panSemTheory.empty_locals_def, empty_locals_def]) >>
    fs [nested_seq_def] >>
    fs [evaluate_def] >> pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    cases_on ‘ t.clock = 0’ >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_asmsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
     match_mp_tac state_code_locals_rel_preserved_call >>
     fs []) >>
    strip_tac >> fs [] >>
    rveq >> fs [] >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def, code_rel_def])
   >- (
    cases_on ‘is_valid_value s.locals m v’ >> fs [] >> rveq >>
    fs [is_valid_value_def] >>
    cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
    TOP_CASE_TAC >> fs []
    >- (fs [locals_rel_def] >> first_x_assum drule >> fs []) >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs []
    >- (
     TOP_CASE_TAC >> fs []
     >- (
      fs [locals_rel_def] >> first_x_assum drule >> fs [] >>
      fs [OPT_MMAP_def] >>
      strip_tac >> fs [] >>
      pop_assum (assume_tac o GSYM) >>
      ‘size_of_shape (shape_of x) = 1’ by
        fs [panLangTheory.size_of_shape_def, shape_of_def] >>
      fs [GSYM length_flatten_eq_size_of_shape] >> rfs [flatten_def]) >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
      strip_tac >> fs [] >>
      ‘size_of_shape (shape_of x) = 1’ by (
        fs [locals_rel_def] >>
        last_x_assum drule >>
        fs [shape_of_def]) >>
      fs [shape_of_def] >>
      conj_tac
      >- fs [state_rel_def, panSemTheory.set_var_def,set_var_def] >>
      conj_tac
      >- fs [Abbr ‘nctxt’, code_rel_def, panSemTheory.set_var_def,set_var_def] >>
      ‘size_of_shape (shape_of v) = 1’ by fs [] >>
      drule locals_rel_lookup_ctxt >>
      disch_then drule >> strip_tac >> fs [] >>
      rveq >> fs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def] >>
      fs [locals_rel_def, panSemTheory.set_var_def,set_var_def] >>
      rw [] >> rveq >>
      fs [FLOOKUP_UPDATE] >>
      FULL_CASE_TAC >> fs [] >> rveq
      >- (
       fs [OPT_MMAP_def, FLOOKUP_UPDATE] >> rveq >>
       fs [length_flatten_eq_size_of_shape, panLangTheory.size_of_shape_def]) >>
      last_x_assum drule >>
      strip_tac >> fs [] >>
      match_mp_tac opt_mmap_flookup_update >>
      fs [] >>
      drule no_overlap_flookup_distinct >>
      disch_then drule_all >> fs [distinct_lists_def]) >>
    TOP_CASE_TAC >> fs []
    >- (
     ‘LENGTH r' = 1’ by (
       drule_all locals_rel_lookup_ctxt >> strip_tac >>
       fs [length_flatten_eq_size_of_shape] >>
       rfs [panLangTheory.size_of_shape_def]) >>
     fs [] >>
     cases_on ‘r'’ >> fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
      strip_tac >> fs [] >>
      ‘size_of_shape (shape_of x) = 1’ by (
        drule_all locals_rel_lookup_ctxt >> strip_tac >>
        fs [length_flatten_eq_size_of_shape] >>
        rfs [panLangTheory.size_of_shape_def]) >>
      fs [shape_of_def, panLangTheory.size_of_shape_def] >>
      conj_tac
      >- fs [state_rel_def, panSemTheory.set_var_def,set_var_def] >>
      conj_tac
      >- fs [Abbr ‘nctxt’, code_rel_def, panSemTheory.set_var_def,set_var_def] >>
      ‘size_of_shape (shape_of v) = 1’ by fs [] >>
      drule locals_rel_lookup_ctxt >>
      disch_then drule >> strip_tac >> fs [] >>
      rveq >> fs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def] >>
      fs [locals_rel_def, panSemTheory.set_var_def,set_var_def] >>
      rw [] >> rveq >>
      fs [FLOOKUP_UPDATE] >>
      FULL_CASE_TAC >> fs [] >> rveq
      >- (
       fs [OPT_MMAP_def, FLOOKUP_UPDATE] >> rveq >>
       fs [length_flatten_eq_size_of_shape, panLangTheory.size_of_shape_def]) >>
      last_x_assum drule >>
      strip_tac >> fs [] >>
      match_mp_tac opt_mmap_flookup_update >>
      fs [] >>
      drule no_overlap_flookup_distinct >>
      disch_then drule_all >> fs [distinct_lists_def]) >>
    fs [nested_seq_def, evaluate_def] >> pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    cases_on ‘ t.clock = 0’ >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_asmsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
     match_mp_tac state_code_locals_rel_preserved_call >>
     fs []) >>
    strip_tac >> fs [] >>
    cases_on ‘res1’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >> rveq >> fs [] >>
    fs [shape_of_def, panLangTheory.size_of_shape_def,
        panSemTheory.set_var_def, set_var_def] >>
    cases_on ‘size_of_shape (shape_of x) = 0’ >> fs []
    >- (
     rveq >> drule locals_rel_lookup_ctxt >>
     disch_then (qspecl_then [‘m’, ‘x’] assume_tac) >>
     fs [length_flatten_eq_size_of_shape] >> rfs [] >> rveq >>
     fs [nested_seq_def, evaluate_def] >>
     conj_tac >- fs [state_rel_def] >>
     conj_tac >- fs [Abbr ‘nctxt’, code_rel_def] >>
     fs [locals_rel_def] >> rw [] >>
     fs [FLOOKUP_UPDATE] >> FULL_CASE_TAC >> fs [] >> rveq
     >- (
      fs [OPT_MMAP_def] >>
      ‘LENGTH (flatten v) = 0’ suffices_by fs[] >>
      rewrite_tac [length_flatten_eq_size_of_shape] >>
      fs []) >>
     first_x_assum drule >> strip_tac >> fs [] >>
     fs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
     rw [] >> fs [FLOOKUP_UPDATE] >>
     TOP_CASE_TAC >> fs [] >>
     drule ctxt_max_el_leq >>
     qpat_x_assum ‘LENGTH _ = LENGTH (flatten _)’ (assume_tac o GSYM) >>
     fs [] >> disch_then drule_all >> fs []) >>
    ‘1 < size_of_shape (shape_of x)’ by (
      drule locals_rel_lookup_ctxt >>
      disch_then drule >>
      strip_tac >> fs [] >> rfs [] >>
      fs [panLangTheory.size_of_shape_def] >>
      DECIDE_TAC) >>
    fs [] >>
    ‘ALL_DISTINCT r'’ by
      (fs [locals_rel_def] >> imp_res_tac all_distinct_flookup_all_distinct) >>
    fs [globals_lookup_def] >>
    drule evaluate_seq_assign_load_globals >>
    disch_then (qspecl_then [‘t1 with locals :=
                              t.locals |+ (ctxt.max_var + 1,Word 0w)’, ‘0w’] mp_tac) >>
    impl_tac
    >- (
     conj_tac
     >- (
      fs [word_0_n2w] >>
      imp_res_tac locals_rel_lookup_ctxt >> rveq >>
      fs [length_flatten_eq_size_of_shape] >> rfs []) >>
     conj_tac
     >- (
      rw [] >>
      ‘n <> ctxt.max_var + 1’ suffices_by (
         fs [FLOOKUP_UPDATE, locals_rel_def] >>
         first_x_assum drule_all >> strip_tac >> fs [] >> rveq >>
         imp_res_tac opt_mmap_mem_func >> fs []) >>
      fs [locals_rel_def, ctxt_max_def] >>
      last_x_assum drule_all >> strip_tac >> fs []) >>
     rw [] >> rfs [] >>
     drule locals_rel_lookup_ctxt >>
     ‘size_of_shape (shape_of x) = LENGTH r'’ by (
       drule locals_rel_lookup_ctxt >>
       disch_then drule >>
       strip_tac >> fs [] >> rveq >>
       fs [length_flatten_eq_size_of_shape] >> rfs []) >>
     fs [] >> drule opt_mmap_mem_func >>
     disch_then drule >> strip_tac >> fs []) >>
    strip_tac >> fs [] >>
    conj_tac >- fs [state_rel_def] >>
    conj_tac >- fs [Abbr ‘nctxt’, code_rel_def] >>
    ‘MAP (λn. THE (FLOOKUP t1.globals n)) (GENLIST (λx. n2w x) (LENGTH r')) =
     flatten v’ by (
      fs [opt_mmap_eq_some] >>
      ‘size_of_shape (shape_of v) = LENGTH r'’ by (
        drule locals_rel_lookup_ctxt >>
        disch_then drule >>
        strip_tac >> fs [] >> rveq >>
        fs [length_flatten_eq_size_of_shape] >> rfs []) >>
      fs [] >> drule map_some_the_map >> fs []) >>
    fs [] >>
    match_mp_tac local_rel_le_zip_update_preserved >> fs [] >>
    match_mp_tac local_rel_gt_max_var_preserved >>
    fs [])
   >- (
    cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
    TOP_CASE_TAC
    >- (fs [locals_rel_def] >> first_x_assum drule >> fs []) >>
    TOP_CASE_TAC  >>
    TOP_CASE_TAC
    >- (
     TOP_CASE_TAC
     >- (
      fs [locals_rel_def] >> first_x_assum drule >> fs [] >>
      fs [OPT_MMAP_def] >>
      strip_tac >> fs [] >>
      pop_assum (assume_tac o GSYM) >>
      ‘size_of_shape (shape_of x) = 1’ by
        fs [panLangTheory.size_of_shape_def, shape_of_def] >>
      fs [GSYM length_flatten_eq_size_of_shape] >> rfs [flatten_def]) >>
     fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >> rveq >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >-  fs [Abbr ‘nctxt’, state_rel_def,
             empty_locals_def, panSemTheory.empty_locals_def, code_rel_def] >>
     fs [shape_of_def, panLangTheory.size_of_shape_def] >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >>
     fs [Abbr ‘nctxt’, state_rel_def,
         empty_locals_def, panSemTheory.empty_locals_def, code_rel_def,
         globals_lookup_def]) >>
    TOP_CASE_TAC >> fs []
    >- (
     ‘LENGTH r' = 1’ by (
       drule_all locals_rel_lookup_ctxt >> strip_tac >>
       fs [length_flatten_eq_size_of_shape] >>
       rfs [panLangTheory.size_of_shape_def]) >>
     cases_on ‘r'’ >> fs [] >>
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     fs [] >> rveq >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
      match_mp_tac state_code_locals_rel_preserved_call >>
      fs []) >>
     strip_tac >> cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >-  fs [Abbr ‘nctxt’, state_rel_def,
             empty_locals_def, panSemTheory.empty_locals_def, code_rel_def] >>
     fs [shape_of_def, panLangTheory.size_of_shape_def] >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >>
     fs [Abbr ‘nctxt’, state_rel_def,
         empty_locals_def, panSemTheory.empty_locals_def, code_rel_def,
         globals_lookup_def]) >>
    fs [nested_seq_def] >>
    fs [evaluate_def] >> pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    cases_on ‘ t.clock = 0’ >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_asmsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
     match_mp_tac state_code_locals_rel_preserved_call >>
     fs []) >>
    strip_tac >> fs [] >>
    rveq >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >> rveq
    >-  fs [Abbr ‘nctxt’, state_rel_def,
            empty_locals_def, panSemTheory.empty_locals_def, code_rel_def] >>
    fs [shape_of_def, panLangTheory.size_of_shape_def] >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs [] >> rveq >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def, code_rel_def,
        globals_lookup_def]) >>
   cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
   TOP_CASE_TAC
   >- (fs [locals_rel_def] >> first_x_assum drule >> fs []) >>
   TOP_CASE_TAC  >>
   TOP_CASE_TAC
   >- (
    TOP_CASE_TAC
    >- (
     fs [locals_rel_def] >> first_x_assum drule >> fs [] >>
     fs [OPT_MMAP_def] >>
     strip_tac >> fs [] >>
     pop_assum (assume_tac o GSYM) >>
     ‘size_of_shape (shape_of x) = 1’ by
       fs [panLangTheory.size_of_shape_def, shape_of_def] >>
     fs [GSYM length_flatten_eq_size_of_shape] >> rfs [flatten_def]) >>
    fs [] >>
    fs [evaluate_def] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    strip_tac >>
    TOP_CASE_TAC >- fs [state_rel_def] >>
    qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
     match_mp_tac state_code_locals_rel_preserved_call >>
     fs []) >>
    strip_tac >> fs [] >>
    fs [Abbr ‘nctxt’, state_rel_def,
        empty_locals_def, panSemTheory.empty_locals_def, code_rel_def]) >>
   TOP_CASE_TAC >> fs []
   >- (
    ‘LENGTH r' = 1’ by (
      drule_all locals_rel_lookup_ctxt >> strip_tac >>
      fs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def]) >>
    cases_on ‘r'’ >> fs [] >>
    fs [evaluate_def] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    strip_tac >>
    TOP_CASE_TAC >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
     match_mp_tac state_code_locals_rel_preserved_call >>
     fs []) >>
    strip_tac >>
    fs [state_rel_def, Abbr ‘nctxt’, code_rel_def,
        panSemTheory.empty_locals_def, empty_locals_def]) >>
   fs [nested_seq_def] >>
   fs [evaluate_def] >> pairarg_tac >> fs [] >>
   cases_on ‘eval t x0’ >> fs [] >>
   cases_on ‘x'’ >> fs [] >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
   disch_then (qspec_then ‘ns’ mp_tac) >>
   fs [] >>
   cases_on ‘ t.clock = 0’ >- fs [state_rel_def] >>
   fs [] >> rveq >>
   qmatch_asmsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
   first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
   impl_tac
   >- (
    fs [Abbr ‘nctxt’, Abbr ‘nt’] >>
    match_mp_tac state_code_locals_rel_preserved_call >>
    fs []) >>
   strip_tac >> fs [] >>
   rveq >> fs [] >>
   fs [Abbr ‘nctxt’, state_rel_def,
       empty_locals_def, panSemTheory.empty_locals_def, code_rel_def]) >>
   cheat
QED




val _ = export_theory();
