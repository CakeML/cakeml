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

(* semantics of the little language *)

val _ = Datatype `
  state = <| regs : num |-> 'a word
           ; arrays : address -> ('a word) list
           |>`

val eval_exp_pre_def = Define `
  (eval_exp_pre s (Const w) <=> T) /\
  (eval_exp_pre s (Var v) <=> v IN FDOM s.regs)`

val eval_exp_def = Define `
  eval_exp s (Const w) = w /\
  eval_exp s (Var v) = s.regs ' v /\
  eval_exp s (Op Add [x1;x2]) = eval_exp s x1 + eval_exp s x2`

val (eval_rules,eval_ind,raw_eval_cases) = Hol_reln `
  (!s. Eval s Skip (INR (s:'a state))) /\
  (!s. Eval s Continue (INL s)) /\
  (!s x n.
     eval_exp_pre s x ==>
     Eval s (Assign n x) (INR (s with regs := s.regs |+ (n,eval_exp s x)))) /\
  (!s1 s2 s3 p1 p2.
     Eval s1 p1 (INR s2) /\ Eval s2 p2 s3 ==>
     Eval s1 (Seq p1 p2) s3) /\
  (!s1 p s2.
     Eval s1 p (INR s2) ==>
     Eval s1 (Loop p) (INR s2)) /\
  (!s1 s2 s3 p.
     Eval s1 p (INL s2) /\ Eval s2 (Loop p) (INR s3) ==>
     Eval s1 (Loop p) (INR s3))`

val eval_cases =
  map (SIMP_CONV (srw_ss()) [Once raw_eval_cases])
    [``Eval s1 Skip s2``,
     ``Eval s1 (Seq p1 p2) s2``,
     ``Eval s1 (Assign n x) s2``,
     ``Eval s1 Continue s2``,
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
  ``Corr p1 (TERM g) /\ Corr p2 f ==>
    Corr (Seq p1 p2) (COMB g f)``,
  fs [Corr_def,TERM_def,COMB_def,eval_cases] \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ Cases_on `g s` \\ fs [] \\ Cases_on `f q` \\ fs []
  \\ metis_tac [SND,FST,PAIR]);

val Corr_Continue = prove(
  ``Corr Continue (\s. (INL s,b))``,
  fs [Corr_def,eval_cases]);

val Corr_Assign = prove(
  ``Corr (Assign n x)
      (TERM (\s. (s with regs := s.regs |+ (n,eval_exp s x),
                  eval_exp_pre s x)))``,
  fs [Corr_def,eval_cases,TERM_def]);

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

val _ = export_theory();
