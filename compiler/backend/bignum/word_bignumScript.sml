open preamble astTheory wordLangTheory wordSemTheory tailrecTheory;

val _ = new_theory "word_bignum";

(* syntax of a little language *)

val _ = Datatype `
  address = In1 | In2 | Out`

val _ = Datatype `
  prog = Skip
       | Assign num ('a wordLang$exp)
       | Load num address ('a wordLang$exp)
       | Store address ('a wordLang$exp) ('a wordLang$exp)
       | Seq prog prog
       | If cmp num ('a reg_imm) prog prog
       | Loop prog
       | Continue`

(* syntax helper funs *)

val Skip_tm = ``Skip:'a word_bignum$prog``
val Continue_tm = ``Continue:'a word_bignum$prog``

local val s = HolKernel.syntax_fns1 "word_bignum" in
  val (Loop_tm,mk_Loop,dest_Loop,is_Loop) = s "Loop"
end
local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (Assign_tm,mk_Assign,dest_Assign,is_Assign) = s "Assign"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
  val (Store_tm,mk_Store,dest_Store,is_Store) = s "Store"
end

local val s = HolKernel.syntax_fns1 "asm" in
  val (Imm_tm,mk_Imm,dest_Imm,is_Imm) = s "Imm"
  val (Reg_tm,mk_Reg,dest_Reg,is_Reg) = s "Reg"
end

val If_pat = ``word_bignum$If c r (ri:'a reg_imm) p1 p2``
fun dest_If tm = let
  val i = fst (match_term If_pat tm)
  val ts = helperLib.list_dest dest_comb If_pat
  in (subst i (el 2 ts),
      subst i (el 3 ts),
      subst i (el 4 ts),
      subst i (el 5 ts),
      subst i (el 6 ts)) end
fun mk_If (c,r,ri,p1,p2) = ``word_bignum$If ^c ^r ^ri ^p1 ^p2``;

(* semantics of the little language *)

val _ = Datatype `
  state = <| regs : num |-> 'a word
           ; arrays : address -> ('a word) list
           |>`

val eval_exp_def = Define `
  eval_exp s (Const w) = w /\
  eval_exp s (Var v) = s.regs ' v /\
  eval_exp s (Op Add [x1;x2]) = eval_exp s x1 + eval_exp s x2 /\
  eval_exp s (Op Sub [x1;x2]) = eval_exp s x1 - eval_exp s x2 /\
  eval_exp s (Op And [x1;x2]) = word_and (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Op Or [x1;x2]) = word_or (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Op Xor [x1;x2]) = word_xor (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Shift sh x (Nat n)) = THE (word_sh sh (eval_exp s x) n)`

val eval_exp_pre_def = Define `
  (eval_exp_pre s (Const w) <=> T) /\
  (eval_exp_pre s (Var v) <=> v IN FDOM s.regs) /\
  (eval_exp_pre s (Op _ [x;y]) <=> eval_exp_pre s x /\ eval_exp_pre s y) /\
  (eval_exp_pre s (Shift sh x (Nat n)) <=> eval_exp_pre s x /\
                                           IS_SOME (word_sh sh (eval_exp s x) n)) /\
  (eval_exp_pre s _ <=> F)`

val eval_ri_pre_def = Define `
  (eval_ri_pre s (Reg r) <=> eval_exp_pre (s:'a state) ((Var r):'a wordLang$exp)) /\
  (eval_ri_pre s (Imm (w:'a word)) <=> T)`;

val eval_ri_def = Define `
  eval_ri s (Reg r) = eval_exp s (Var r) /\
  eval_ri s (Imm w) = w`

val (eval_rules,eval_ind,raw_eval_cases) = Hol_reln `
  (!s. Eval s Skip (INR (s:'a state))) /\
  (!s. Eval s Continue (INL s)) /\
  (!s x n.
     eval_exp_pre s x ==>
     Eval s (Assign n x) (INR (s with regs := s.regs |+ (n,eval_exp s x)))) /\
  (!s1 s2 s3 p1 p2.
     Eval s1 p1 (INR s2) /\ Eval s2 p2 s3 ==>
     Eval s1 (Seq p1 p2) s3) /\
  (!s1 c r ri p1 p2 s2.
     r IN FDOM s.regs /\ eval_ri_pre s ri /\
     Eval s1 (if word_cmp c (eval_exp s (Var r)) (eval_ri s ri)
              then p1 else p2) s2 ==>
     Eval s1 (If c r ri p1 p2) s2) /\
  (!s1 p s2.
     Eval s1 p (INR s2) ==>
     Eval s1 (Loop p) (INR s2)) /\
  (!s1 s2 s3 p.
     Eval s1 p (INL s2) /\ Eval s2 (Loop p) (INR s3) ==>
     Eval s1 (Loop p) (INR s3))`

val eval_cases =
  map (SIMP_CONV (srw_ss()) [Once raw_eval_cases])
    [``Eval s1 Skip s2``,
     ``Eval s1 Continue s2``,
     ``Eval s1 (Seq p1 p2) s2``,
     ``Eval s1 (Assign n x) s2``,
     ``Eval s1 (If c r ri p1 p2) s2``,
     ``Eval s1 (Loop p) s2``] |> LIST_CONJ;

(* correctenss judgement *)

val Corr_def = Define `
  Corr prog f <=>
    !s:'a state. SND (f s) ==> Eval s prog (FST (f s))`;

val TERM_def = Define `TERM f = \s. let (s1,b) = f s in (INR s1,b)`;

val Corr_Skip = prove(
  ``Corr Skip (TERM (\s. (s,T)))``,
  fs [Corr_def,TERM_def,eval_cases]);

val COMB_def = Define `
  COMB g f = \s. let (s1,b2) = g s in
                 let (s2,b3) = f s1 in (s2,b2 /\ b3)`;

val Corr_Seq = prove(
  ``Corr p1 (TERM g) ==> Corr p2 f ==>
    Corr (Seq p1 p2) (COMB g f)``,
  fs [Corr_def,TERM_def,COMB_def,eval_cases] \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ Cases_on `g s` \\ fs [] \\ Cases_on `f q` \\ fs []
  \\ metis_tac [SND,FST,PAIR]);

val Corr_Continue = prove(
  ``Corr Continue (\s. (INL s,T))``,
  fs [Corr_def,eval_cases]);

val Corr_Assign = prove(
  ``Corr (Assign n x)
      (TERM (\s. (s with regs := s.regs |+ (n,eval_exp s x),
                  eval_exp_pre s x)))``,
  fs [Corr_def,eval_cases,TERM_def]);

val Corr_If = prove(
  ``Corr p1 f1 /\ Corr p2 f2 ==>
    Corr (If c r ri p1 p2)
         (\s. (I ## (\b. b /\ r IN FDOM s.regs /\ eval_ri_pre s ri))
              (if word_cmp c (eval_exp s (Var r)) (eval_ri s ri)
               then f1 s else f2 s))``,
  fs [Corr_def,eval_cases] \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs [] \\ rw [] \\ fs []);

val LOOP_def = Define `
  LOOP f = \s. (SHORT_TAILREC f s, SHORT_TAILREC_PRE f s)`;

val Corr_Loop = prove(
  ``Corr p f ==> Corr (Loop p) (TERM (LOOP f))``,
  fs [Corr_def,TERM_def]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [LOOP_def,SHORT_TAILREC_def,SHORT_TAILREC_PRE_def]
  \\ strip_tac \\ ho_match_mp_tac TAILREC_PRE_INDUCT \\ reverse (rw [])
  \\ once_rewrite_tac [eval_cases] THENL [disj1_tac,disj2_tac]
  \\ once_rewrite_tac [TAILREC_THM]
  \\ fs [] \\ res_tac
  \\ Cases_on `f s` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ asm_exists_tac \\ fs []);

val Corr_STRENGTHEN = prove(
  ``Corr p f ==>
    !f'.
      (!s. FST (f' s) = FST (f s)) /\
      (!s. SND (f' s) ==> SND (f s)) ==>
      Corr p f'``,
  fs [Corr_def] \\ metis_tac []);

val Corr_STRENGTHEN_TERM = prove(
  ``Corr p (TERM f) ==>
    !f'.
      (!s. FST (f' s) = FST (f s)) /\
      (!s. SND (f' s) ==> SND (f s)) ==>
      Corr p (TERM f')``,
  fs [Corr_def,TERM_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

(* examples *)

fun tailrec_define name tm =
  tailrecLib.tailrec_define_from_step name tm NONE;

val (foo_def, _,foo_pre_def, _) =
  tailrec_define "foo" ``
    (\(r8,r10).
      let r10 = r10 - 8w in
      let r8 = r8 + r10 in
        if r8 <+ r10 then (INR r8,T) else (INL (r8,r10),T))
    :('a word) # ('a word) -> (((('a word) # ('a word)) + ('a word)) # bool)``

(* generate deep embeddings *)

fun my_dest_let tm = let
  val (x,y) = pairSyntax.dest_anylet tm
  in if length x = 1 then (hd x,y) else fail() end

local
  val word_ty = ``:'a word``
in
  fun dest_reg v = let
    val (n,ty) = dest_var v
    val _ = ty = word_ty orelse fail()
    val n = String.substring(n,1,String.size(n)-1) |> string_to_int
    val n = numSyntax.term_of_int n
    in n end handle Subscript => fail()
end;

val binops = [(word_add_def,``asm$Add``),
              (word_sub_def,``asm$Sub``),
              (word_and_def,``asm$And``),
              (word_xor_def,``asm$Xor``),
              (word_or_def, ``asm$Or``)]
  |> map (fn (x,y) => (x |> SPEC_ALL |> concl |> dest_eq |> fst, y))

fun get_exp x =
  (* Var *) let
  val n = dest_reg x
  in wordLangSyntax.mk_Var n end handle HOL_ERR _ =>
  (* Const *) let
  val _ = wordsSyntax.dest_n2w x
  in wordLangSyntax.mk_Const x end handle HOL_ERR _ =>
  (* Op *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) x) binops
  val x1 = get_exp (x |> rator |> rand)
  val x2 = get_exp (x |> rand)
  in wordLangSyntax.mk_Op(name,listSyntax.mk_list([x1,x2],type_of x1)) end

val cmps = [(word_lo_def,``asm$Lower``),
            (word_lt_def,``asm$Less``),
            (GSYM w2n_11,``asm$Equal``)]
  |> map (fn (x,y) => (x |> SPEC_ALL |> concl |> dest_eq |> fst, y))

fun dest_reg_imm ri =
  mk_Reg (dest_reg ri) handle HOL_ERR _ =>
  if can wordsSyntax.dest_n2w ri then mk_Imm ri else fail()

fun get_guard b = (* Op *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) b) cmps
  val x1 = dest_reg (b |> rator |> rand)
  val x2 = dest_reg_imm (b |> rand)
  in (name,x1,x2) end handle HOL_ERR _ => let
  val _ = can (match_term ``(w && n2w n) = 0w:'a word``) b orelse fail()
  val x1 = b |> rator |> rand |> rator |> rand
  val x2 = b |> rator |> rand |> rand
  in (``asm$Test``,dest_reg x1,dest_reg_imm x2) end

fun get_prog tm =
  (* return *)
  if is_var tm then Skip_tm else
  if pairSyntax.is_pair tm then Skip_tm else
  (* Assign *) let
  val ((v,x),rest) = my_dest_let tm
  val n = dest_reg v
  val e = get_exp x
  val r = get_prog rest
  in mk_Seq(mk_Assign(n,e),r) end handle HOL_ERR _ => let
  val (b,t1,t2) = dest_cond tm
  val (x1,x2,x3) = get_guard b
  in mk_If(x1,x2,x3,get_prog t1,get_prog t2) end handle HOL_ERR _ =>
  if is_const (rator tm) andalso (is_var (rand tm) orelse is_pair (rand tm))
  then Continue_tm
  else fail()

fun get_full_prog tm = mk_Loop(get_prog tm);

(*
val tm = foo_def |> SPEC_ALL |> concl |> rand
*)

(* derive Corr thm from AST *)

(*
  val tm = foo_def |> SPEC_ALL |> concl |> rand
  val tm = get_full_prog tm
*)

fun get_pat thm = thm |> SPEC_ALL |> UNDISCH_ALL |> concl |> rator |> rand;

fun get_corr tm =
  if tm = Skip_tm then Corr_Skip else
  if tm = Continue_tm then Corr_Continue else let
  val i = fst (match_term (get_pat Corr_Assign) tm)
  in REWRITE_RULE [eval_exp_def,eval_exp_pre_def] (INST i Corr_Assign) end
  handle HOL_ERR _ => let
  val (p1,p2) = dest_Seq tm
  val th1 = get_corr p1
  val th2 = get_corr p2
  in MATCH_MP (MATCH_MP Corr_Seq th1) th2 end
  handle HOL_ERR _ => let
  val i = fst (match_term (get_pat Corr_Loop) tm)
  val th = get_corr (tm |> rand)
  in MATCH_MP Corr_Loop th end handle HOL_ERR _ => let
  val i = fst (match_term (get_pat Corr_If) tm)
  val p1 = get_corr (tm |> rator |> rand)
  val p2 = get_corr (tm |> rand)
  val th = REWRITE_RULE [eval_exp_def,eval_exp_pre_def,asmSemTheory.word_cmp_def,
             eval_ri_pre_def,eval_ri_def] (INST i Corr_If)
  in MATCH_MP th (CONJ p1 p2) end

(*
  get_corr tm
*)

val foo_corr = get_corr tm

val foo_raw_def = Define `
  foo_raw = ^(foo_corr |> concl |> rand |> rand)`

val foo_corr = foo_corr |> REWRITE_RULE [GSYM foo_raw_def]

val v = mk_var("foo_new",type_of (foo_raw_def |> concl |> rator |> rand))

val foo_new_def = Define `
  ^v = \s.
    (let r8 = foo (s.regs ' 8, s.regs ' 10) in
     let s1 = FST (foo_raw s) in
       s with regs := (s.regs |++ [(8,r8); (10,s1.regs ' 10)]),
     8 IN FDOM s.regs /\
     10 IN FDOM s.regs /\
     foo_pre (s.regs ' 8, s.regs ' 10))`

val foo_corr_lemma =
  MATCH_MP Corr_STRENGTHEN_TERM foo_corr
  |> SPEC (foo_new_def |> concl |> rator |> rand)

val lemma = prove(``^(foo_corr_lemma |> concl |> dest_imp |> fst)``,
  reverse conj_tac
  \\ fs [foo_new_def,fetch "-" "foo_pre",foo_raw_def,LOOP_def]
  \\ cheat);

val corr_foo_new = MP foo_corr_lemma lemma |> REWRITE_RULE [foo_new_def];

val _ = export_theory();
