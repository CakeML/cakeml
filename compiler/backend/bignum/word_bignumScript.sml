open preamble astTheory wordLangTheory wordSemTheory tailrecTheory;
open mc_multiwordTheory

val _ = new_theory "word_bignum";


(* ---- This part will go into word_bignumScript.sml file ---- *)

(* syntax of a little language *)

val _ = Datatype `
  address = In1 | In2 | Out`

val _ = Datatype `
  prog = Skip
       | Assign num ('a wordLang$exp)
       | Seq prog prog
       | Load num num address
       | Store num num
       | If cmp num ('a reg_imm) prog prog
       | Swap
       | Add num num num ('a reg_imm) ('a reg_imm)
       | Sub num num num ('a reg_imm) ('a reg_imm)
       | Mul num num num num
       | Div num num num num num
       | Loop prog
       | Continue
       (* the following are only used by the semantics *)
       | LoopBody prog `


(* syntax helper funs *)

val Skip_tm = ``Skip:'a word_bignum$prog``
val Continue_tm = ``Continue:'a word_bignum$prog``

local val s = HolKernel.syntax_fns1 "word_bignum" in
  val (Loop_tm,mk_Loop,dest_Loop,is_Loop) = s "Loop"
end
local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (Assign_tm,mk_Assign,dest_Assign,is_Assign) = s "Assign"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
  val (Store_tm,mk_Store,dest_Store,is_Store) = s "Store"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
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

val shifts = [(word_lsr_def,``ast$Lsr``),
              (word_lsl_def,``ast$Lsl``),
              (word_asr_def,``ast$Asr``)]
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
  handle HOL_ERR _ =>
  (* Shift *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) x) shifts
  val x1 = get_exp (x |> rator |> rand)
  val x2 = x |> rand
  in wordLangSyntax.mk_Shift(name,x1,``Nat ^x2``) end
  handle HOL_ERR _ =>
  (* ~ *) let
  val r = wordsSyntax.dest_word_1comp x
  in get_exp ``word_xor ^r (0w - 1w)`` end

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

local
  val LUPDATE_pat = ``LUPDATE a (w2n (r:'a word)) (zs:'b list)``
in
  fun dest_lupdate_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_abs rest
    val _ = (v = rand r) orelse fail ()
    val _ = can (match_term LUPDATE_pat) r orelse fail()
    val x = r |> rator |> rator |> rand
    val y = r |> rator |> rand |> rand
    in (x,y,body) end
end

local
  val EL_pat = ``EL (w2n (r:'a word)) (zs:'b list)``
in
  fun dest_el_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_abs rest
    val _ = can (match_term EL_pat) r orelse fail()
    val a = r |> rand |> dest_var |> fst
    val a = if a = "xs" then ``In1`` else
            if a = "ys" then ``In2`` else
            if a = "zs" then ``Out`` else fail()
    val y = r |> rator |> rand |> rand
    in (v,y,a,body) end
end

local
  val add_pat = ``single_add_word r0 r1 ri``
  val sub_pat = ``single_sub_word r0 r1 ri``
  fun dest_single_add_sub_let pat tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg_imm (el 2 args)
    val r3 = dest_reg_imm (el 3 args)
    in (a1,a2,r1,r2,r3,body) end
in
  val dest_single_add_let = dest_single_add_sub_let add_pat
  val dest_single_sub_let = dest_single_add_sub_let sub_pat
end

local
  val mul_pat = ``single_mul r0 r2 0w``
in
  fun dest_single_mul_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term mul_pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg (el 2 args)
    in (a1,a2,r1,r2,body) end
end

local
  val div_pat = ``single_div r2 r0 r1``
in
  fun dest_single_div_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term div_pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg (el 2 args)
    val r3 = dest_reg (el 3 args)
    in (a1,a2,r1,r2,r3,body) end
end

fun get_let tm =
  (* Load *)
  let
    val (r,i,a,rest) = dest_el_let tm
  in (mk_Load(dest_reg r, dest_reg i, a),rest) end handle HOL_ERR _ =>
  (* Store *)
  let
    val (r,i,rest) = dest_lupdate_let tm
  in (mk_Store(dest_reg r, dest_reg i),rest) end handle HOL_ERR _ =>
  (* Assign *)
  let
    val ((v,x),rest) = my_dest_let tm
    val n = dest_reg v
    val e = get_exp x
  in (mk_Assign(n,e),rest) end handle HOL_ERR _ =>
  (* Swap *)
  let
    val ((v,x),rest) = my_dest_let tm
    val _ = pairSyntax.is_pair x orelse fail()
  in (``Swap``,rest) end handle HOL_ERR _ =>
  (* Add *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_add_let tm
  in (``Add ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  (* Sub *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_sub_let tm
  in (``Sub ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  (* Mul *)
  let
    val (a1,a2,r1,r2,rest) = dest_single_mul_let tm
  in (``Mul ^a1 ^a2 ^r1 ^r2``,rest) end handle HOL_ERR _ =>
  (* Div *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_div_let tm
  in (``Div ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  fail ()

val code_defs = ref TRUTH;
val prev_trans = ref ([]: (term * term) list);

exception UnableToTranslate of string;

fun get_prog tm =
  (* return *)
  if is_var tm then Skip_tm else
  if pairSyntax.is_pair tm then Skip_tm else
  (* let *) let
  val (x,rest) = get_let tm
  in mk_Seq(x,get_prog rest) end handle HOL_ERR _ =>
  (* previous translation *) let
  val ((v,x),rest) = my_dest_let tm
  val f = x |> repeat rator
  val (_,code) = first (fn (x,y) => same_const x f) (!prev_trans)
  in mk_Seq(code,get_prog rest) end handle HOL_ERR _ =>
  (* If *) let
  val (b,t1,t2) = dest_cond tm
  val (x1,x2,x3) = get_guard b
  in mk_If(x1,x2,x3,get_prog t1,get_prog t2) end handle HOL_ERR _ =>
  if is_const (rator tm) andalso (is_var (rand tm) orelse is_pair (rand tm))
  then Continue_tm
  else let
    val ((v,x),rest) = my_dest_let tm
    val str = repeat rator x |> dest_const |> fst
    in raise UnableToTranslate str end
    handle HOL_ERR e =>
      (print "Unable to translate\n\n";
       print_term tm;
       print "\n\n";
       raise HOL_ERR e);

fun to_deep def = let
  (* produce deep embedding *)
  val f = def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tm = def |> SPEC_ALL |> concl |> rand
  val is_rec = can (find_term (fn tm => (tm = f))) tm
  val deep = get_prog tm
             handle UnableToTranslate str =>
               (to_deep (find (str ^ "_def") |> hd |> snd |> fst);
                get_prog tm)
  val deep = if is_rec then mk_Loop deep else deep
  (* store deep embedding *)
  val name = mk_var((f |> dest_const |> fst) ^ "_code", type_of deep)
  val code_def = Define `^name = ^deep`
  val code_const = code_def |> concl |> dest_eq |> fst
  val _ = (code_defs := CONJ code_def (!code_defs))
  val _ = (prev_trans := (f,code_const) :: (!prev_trans))
  in code_def end
  handle HOL_ERR e =>
    (print ("Failed at " ^ term_to_string
       (def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator) ^ "\n");
     raise (HOL_ERR e))

(*
val tm = def |> SPEC_ALL |> concl |> rand
*)

val def = mc_cmp_def |> to_deep
val def = mc_compare_def |> to_deep
val def = mc_iadd1_def |> to_deep
val def = mc_iadd2_def |> to_deep
val def = mc_iadd3_def |> to_deep
val def = mc_add_loop2_def |> to_deep
val def = mc_add_loop1_def |> to_deep
val def = mc_add_loop_def |> to_deep
val def = mc_add_def |> to_deep
val def = mc_sub_loop2_def |> to_deep
val def = mc_sub_loop1_def |> to_deep
val def = mc_sub_loop_def |> to_deep
val def = mc_fix_def |> to_deep
val def = mc_sub_def |> to_deep
val def = mc_iadd_def |> to_deep
val def = mc_mul_zero_def |> to_deep
val def = mc_single_mul_add_def |> to_deep
val def = mc_mul_pass_def |> to_deep
val def = mc_mul_def |> to_deep
val def = mc_imul1_def |> to_deep
val def = mc_imul_def |> to_deep
val def = mc_isub_flip_def |> to_deep
val def = mc_div_r1_def |> to_deep
val def = mc_sub1_def |> to_deep
val def = mc_cmp2_def |> to_deep
val def = mc_cmp3_def |> to_deep
val def = mc_div_guess_def |> to_deep
val def = mc_single_div_def |> to_deep
val def = mc_simple_div_def |> to_deep
val def = mc_mul_by_single_def |> to_deep
val def = mc_div_adjust_def |> to_deep
val def = mc_calc_d_def |> to_deep
val def = mc_top_two_def |> to_deep
val def = mc_div_loop_def |> to_deep
val def = mc_copy_down_def |> to_deep
val def = mc_simple_div1_def |> to_deep
val def = mc_add1_call_def |> to_deep
val def = mc_idiv_mod_header_def |> to_deep
val def = mc_div_sub_call_def |> to_deep
val def = mc_idiv_def |> to_deep
val def = mc_iop_def |> to_deep



(* ---- This part will go into word_bignumProofScript.sml file ---- *)

(* semantics of the little language *)

val _ = Datatype `
  state = <| regs : num |-> 'a word
           ; arrays : address -> ('a word) list
           ; clock : num
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

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`;

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
  (!s r i a w.
     (FLOOKUP s.regs i = SOME w) /\
     w2n w < LENGTH (s.arrays a) ==>
     Eval s (Load r i a) (INR (s with regs :=
       s.regs |+ (r,EL (w2n w) (s.arrays a))))) /\
  (!s r i w wr.
     (FLOOKUP s.regs i = SOME w) /\ (FLOOKUP s.regs r = SOME wr) /\
     w2n w < LENGTH (s.arrays Out) ==>
     Eval s (Store r i) (INR (s with arrays :=
       (Out =+ LUPDATE wr (w2n w) (s.arrays Out)) s.arrays))) /\
  (!s1 p s2.
     Eval (dec_clock s1) (LoopBody p) s2 /\ s1.clock <> 0 ==>
     Eval s1 (Loop p) s2) /\
  (!s1 p s2.
     Eval s1 p (INR s2) ==>
     Eval s1 (LoopBody p) (INR s2)) /\
  (!s1 s2 s3 p.
     Eval s1 p (INL s2) /\ s2.clock <> 0 /\
     Eval (dec_clock s2) (LoopBody p) (INR s3) ==>
     Eval s1 (LoopBody p) (INR s3))`

val eval_cases =
  map (SIMP_CONV (srw_ss()) [Once raw_eval_cases])
    [``Eval s1 Skip s2``,
     ``Eval s1 Continue s2``,
     ``Eval s1 (Seq p1 p2) s2``,
     ``Eval s1 (Assign n x) s2``,
     ``Eval s1 (If c r ri p1 p2) s2``,
     ``Eval s1 (Load r i a) s2``,
     ``Eval s1 (Store r i) s2``,
     ``Eval s1 (Loop p) s2``,
     ``Eval s1 (LoopBody p) s2``] |> LIST_CONJ;


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

val Corr_Load = prove(
  ``!r i a.
      Corr (Load r i a)
        (TERM (\s. (s with regs := s.regs |+ (r,EL (w2n (s.regs ' i)) (s.arrays a)),
                   i IN FDOM s.regs /\ w2n (s.regs ' i) < LENGTH (s.arrays a))))``,
  fs [Corr_def,eval_cases,TERM_def,FLOOKUP_DEF]);

val Corr_Store = prove(
  ``!r i.
      Corr (Store r i)
        (TERM (\s. (s with arrays :=
                     (Out =+ LUPDATE (s.regs ' r) (w2n (s.regs ' i))
                       (s.arrays Out)) s.arrays),
                   r IN FDOM s.regs /\ i IN FDOM s.regs /\
                   w2n (s.regs ' i) < LENGTH (s.arrays Out)))``,
  fs [Corr_def,eval_cases,TERM_def,FLOOKUP_DEF]);

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

val tick_def = Define `
  tick f = \s. case f s of
               | (INR t,b) => (INR t,b)
               | (INL t,b) => (INL (dec_clock t),b /\ t.clock <> 0)`

val Corr_LoopBody = prove(
  ``Corr p f ==> Corr (LoopBody p) (TERM (LOOP (tick f)))``,
  fs [Corr_def,TERM_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [LOOP_def,SHORT_TAILREC_def,SHORT_TAILREC_PRE_def]
  \\ strip_tac \\ ho_match_mp_tac TAILREC_PRE_INDUCT \\ reverse (rw [])
  \\ once_rewrite_tac [eval_cases] THENL [disj1_tac,disj2_tac]
  \\ once_rewrite_tac [TAILREC_THM]
  \\ fs [] \\ res_tac
  \\ Cases_on `f s` \\ fs [tick_def]
  \\ Cases_on `q` \\ fs []
  \\ `SND (f s)` by fs []
  \\ res_tac \\ fs []
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ asm_rewrite_tac []
  \\ strip_tac
  \\ asm_exists_tac \\ fs []);

val tick_before_def = Define `
  tick_before f s =
    if s.clock = 0 then (s,F) else f (dec_clock s)`

val Corr_Loop_lemma = prove(
  ``Corr (LoopBody p) (TERM f) ==>
    Corr (Loop p) (TERM (tick_before f))``,
  fs [Corr_def] \\ rw []
  \\ once_rewrite_tac [eval_cases]
  \\ fs [tick_before_def,TERM_def]
  \\ Cases_on `s.clock = 0` \\ fs []);

val Corr_Loop = prove(
  ``Corr p f ==>
    Corr (Loop p) (TERM (tick_before (LOOP (tick f))))``,
  rw []
  \\ imp_res_tac Corr_LoopBody
  \\ imp_res_tac Corr_Loop_lemma);

val Corr_STRENGTHEN_TERM = prove(
  ``Corr p (TERM f) ==>
    !f'.
      (!s. SND (f' s) ==> SND (f s) /\ (FST (f' s) = FST (f s))) ==>
      Corr p (TERM f')``,
  fs [Corr_def,TERM_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val Corr_STRENGTHEN_TERM_NEW = prove(
  ``Corr p (TERM f) ==>
    !f'. (!s. SND (f' s) ==> f s = (FST (f' s),T)) ==> Corr p (TERM f')``,
  fs [Corr_def,TERM_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ rpt strip_tac \\ res_tac
  \\ Cases_on `f s` \\ fs []
  \\ `SND (f s)` by fs []
  \\ res_tac \\ metis_tac [FST]);


(* derive Corr thm from AST *)

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
  val i = fst (match_term (get_pat Corr_Load) tm)
  in INST i (SPEC_ALL Corr_Load) end handle HOL_ERR _ => let
  val i = fst (match_term (get_pat Corr_If) tm)
  val p1 = get_corr (tm |> rator |> rand)
  val p2 = get_corr (tm |> rand)
  val th = REWRITE_RULE [eval_exp_def,eval_exp_pre_def,asmTheory.word_cmp_def,
             eval_ri_pre_def,eval_ri_def] (INST i Corr_If)
  in MATCH_MP th (CONJ p1 p2) end
  handle HOL_ERR _ =>
    (print_term tm ; print "\n\n" ; fail())

(*
  get_corr tm


val tm = mc_cmp_def |> SPEC_ALL |> concl |> rand
val tm = (mk_Loop (get_prog tm))
val foo_corr = get_corr tm

val foo_raw_def = Define `
  foo_raw = ^(foo_corr |> concl |> rand |> rand)`

val foo_corr = foo_corr |> REWRITE_RULE [GSYM foo_raw_def]

val v = mk_var("foo_new",type_of (foo_raw_def |> concl |> rator |> rand))

val MARKER_def = Define `MARKER x = x`

val foo_new_def = Define `
  ^v = \s.
    (MARKER (\s r1 r2. s with regs := (s.regs |++ [(8,r1); (10,r2.regs ' 10)]))
       s (foo (s.clock, s.regs ' 8, s.regs ' 10)) (FST (foo_raw s)),
     foo_pre (s.clock, s.regs ' 8, s.regs ' 10) /\
     8 IN FDOM s.regs /\ 10 IN FDOM s.regs)`

val foo_corr_lemma =
  MATCH_MP Corr_STRENGTHEN_TERM_NEW foo_corr
  |> SPEC (foo_new_def |> concl |> rator |> rand)

val ggg =
  foo_raw_def
  |> REWRITE_RULE [LOOP_def]
  |> concl |> rand |> dest_abs |> snd |> rator |> rand |> rator |> rand

val foo_raw_step_def = Define `foo_raw_step = ^ggg`;

val th = SHORT_TAILREC_SIM
  |> ISPEC (fetch "-" "foo" |> concl |> rand |> rand)
  |> REWRITE_RULE [GSYM (fetch "-" "foo_pre"),GSYM (fetch "-" "foo")]
  |> ISPEC ggg
  |> REWRITE_RULE [GSYM foo_raw_step_def]
  |> Q.SPEC `\(r8,r10) s. s0 with regs := s0.regs |++ [(8,r8);(10,r10)] = s`
  |> Q.SPEC `\x s. s0 with regs := s0.regs |++ [(8,x);(10,s.regs ' 10)] = s`
  |> SIMP_RULE std_ss [FORALL_PROD]

val lemma = prove(
  ``^(th |> concl |> dest_imp |> fst)``,
  rw [] \\ fs [foo_raw_step_def,COMB_def,TERM_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
  \\ fs [fmap_EXT,fetch "-" "state_component_equality"]
  \\ rw [EXTENSION]
  \\ TRY eq_tac \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs []);

val foo_pre_imp = MP th lemma

val lemma = prove(
  ``^(foo_corr_lemma |> concl |> dest_imp |> fst)``,
  fs [foo_new_def] \\ rw []
  \\ `(s with regs := s.regs |++ [(8,s.regs ' 8); (10,s.regs ' 10)]) = s` by
   (fs [fmap_EXT,fetch "-" "state_component_equality",FUPDATE_LIST]
    \\ rw [EXTENSION] \\ TRY eq_tac \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
    \\ rw [] \\ NO_TAC)
  \\ first_assum (fn th =>
       assume_tac (Q.INST [`s0`|->`s`] (MATCH_MP foo_pre_imp th)))
  \\ fs [MARKER_def,foo_raw_def]
  \\ fs [foo_raw_step_def,LOOP_def]
  \\ rfs []);

val foo_corr = MP foo_corr_lemma lemma
  |> SIMP_RULE std_ss [foo_new_def,MARKER_def];

(*
  foo_corr |> SIMP_RULE std_ss [Corr_def,TERM_def,LET_THM]
*)

*)

val _ = export_theory();
