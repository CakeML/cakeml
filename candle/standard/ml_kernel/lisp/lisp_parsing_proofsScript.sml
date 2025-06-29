(*
  Proof that pretty printong then parsing returns the same
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open lisp_valuesTheory lisp_printingTheory lisp_parsingTheory;

val _ = new_theory "lisp_parsing_proofs";

Definition dest_quote_def:
  dest_quote v =
    case v of
    | (Pair x (Pair (Num n) (Num 0))) =>
        (if x = Num (name "'") then SOME (QUOTE n) else NONE)
    | _ => NONE
End

Definition v2toks_def:
  v2toks v =
    case v of Num n => [NUM n] | _ =>
    case dest_quote v of SOME s => [s] | NONE =>
      let (l,e) = dest_list v in
        [OPEN] ++
          (if e = Num 0 then FLAT (MAP v2toks l) else
             FLAT (MAP v2toks l) ++ [DOT] ++ (v2toks e)) ++
        [CLOSE]
Termination
  WF_REL_TAC ‘measure lisp_v_size’ \\ rw []
  \\ imp_res_tac dest_list_size \\ fs [lisp_v_size_def,isNum_def]
End

Definition pretty2toks_def:
  pretty2toks (Str s) = lexer s ∧
  pretty2toks (Append p _ q) = pretty2toks q ++ pretty2toks p ∧
  pretty2toks (Parenthesis p) = [CLOSE] ++ pretty2toks p ++ [OPEN] ∧
  pretty2toks (Size _ p) = pretty2toks p
End

Theorem flatten_acc:
  ∀indent p acc. flatten indent p acc = flatten indent p [] ++ acc
Proof
  Induct_on ‘p’ \\ simp_tac std_ss [flatten_def]
  \\ rpt (pop_assum (once_rewrite_tac o single)) \\ fs []
QED

Theorem lex_acc:
  ∀p xs acc. lex p xs acc = lex p xs [] ++ acc
Proof
  qsuff_tac ‘∀p xs (a:token list) acc. lex p xs [] ++ acc = lex p xs acc’
  THEN1 metis_tac []
  \\ ho_match_mp_tac lex_ind \\ rw []
  \\ once_rewrite_tac [lex_def]
  \\ simp_tac (srw_ss()) []
  \\ rpt IF_CASES_TAC
  \\ rw [] \\ fs [] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ metis_tac [APPEND,APPEND_ASSOC]
QED

Theorem read_num_suffix:
  ∀a b c d xs y ys n1 n2 acc rest1 rest2.
    read_num a b c d acc (xs ++ y::ys) = (n1,rest1) ∧
    read_num a b c d acc xs  = (n2,rest2) ∧
    ~(ORD a ≤ ORD y ∧ ORD y ≤ ORD b) ⇒
    n1 = n2 ∧ rest1 = rest2 ++ y::ys
Proof
  Induct_on ‘xs’ \\ fs [read_num_def] THEN1 rw []
  \\ rpt gen_tac \\ rpt (pairarg_tac \\ fs [])
  \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs[]
  \\ first_x_assum drule \\ fs []
QED

Theorem read_num_EVERY_IMP:
  ∀s x1 x2 y1 y2 y3 n rest.
    read_num x1 x2 y1 y2 y3 s = (n,rest) ∧ EVERY p s ⇒ EVERY p rest
Proof
  Induct \\ fs [read_num_def] \\ rw [] \\ res_tac \\ fs []
QED

Theorem lex_APPEND_split:
  ∀c.
    ORD c < ORD #"*" ⇒
    ∀xs ys acc p.
      EVERY (\x. x ≠ CHR 35) xs ⇒
      lex p (STRCAT xs (STRING c ys)) acc = lex NUM (c::ys) (lex p xs acc)
Proof
  gen_tac \\ strip_tac \\ gen_tac \\ completeInduct_on ‘LENGTH xs’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on ‘xs’
  THEN1 (fs [lex_def] \\ rw [] \\ fs [read_num_def])
  \\ fs []
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [lex_def]))
  \\ CONV_TAC (PATH_CONV "rr" (SIMP_CONV std_ss [lex_def]))
  \\ rw [] \\ fs []
  \\ pairarg_tac \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pairarg_tac \\ fs []
  \\ qabbrev_tac ‘ss = h::t’
  \\ ‘STRING h (STRCAT (STRCAT t [c]) ys) = ss ++ c::ys’ by fs []
  \\ qpat_x_assum ‘_ = (n,rest)’ mp_tac
  \\ asm_rewrite_tac [] \\ strip_tac
  \\ drule read_num_suffix \\ fs []
  \\ strip_tac \\ IF_CASES_TAC \\ fs []
  THEN1
   (‘LENGTH rest' < LENGTH (h::t)’ by
      (imp_res_tac read_num_length \\ rfs [] \\ rw [] \\ fs [])
    \\ fs [AND_IMP_INTRO]
    \\ first_x_assum drule
    \\ imp_res_tac read_num_EVERY_IMP \\ rw [])
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ pop_assum mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND] \\ strip_tac
  \\ drule read_num_suffix \\ fs []
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ ‘LENGTH rest'' < LENGTH (h::t)’ by
      (imp_res_tac read_num_length \\ rfs [] \\ rw [] \\ fs [])
  \\ fs [] \\ first_x_assum drule
  \\ imp_res_tac read_num_EVERY_IMP \\ rw []
QED

Theorem lex_indent:
  ∀t. EVERY (λc. c = #" " ∨ c = #"\n") t ⇒
      lex NUM (t ++ s) acc = lex NUM s acc
Proof
  Induct \\ fs [] \\ rw [] \\ fs [] \\ fs [lex_def]
QED

Definition no_hash_def[simp]:
  no_hash (Str s) = EVERY (λx. x ≠ #"#") s ∧
  no_hash (Append p1 b p2) = (no_hash p1 ∧ no_hash p2) ∧
  no_hash (Parenthesis p) = no_hash p ∧
  no_hash (Size _ p) = no_hash p
End

Theorem no_hash_flatten:
  ∀x s1 s2.
    EVERY (λx. x ≠ #"#") s1 ∧ EVERY (λx. x ≠ #"#") s2 ⇒
    EVERY (λx. x ≠ #"#") (flatten s1 x s2) = no_hash x
Proof
  Induct_on ‘x’ \\ fs [flatten_def] \\ rw []
  \\ once_rewrite_tac [flatten_acc] \\ fs []
QED

Theorem lex_flatten:
  ∀p indent.
    EVERY (λc. MEM c " \n") indent ∧ indent ≠ [] ∧ no_hash p ⇒
    lex NUM (flatten indent p []) [] = pretty2toks p
Proof
  Induct
  THEN1
   (rw [flatten_def,pretty2toks_def,lex_def]
    \\ once_rewrite_tac [lex_acc] \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘flatten ss’
    \\ first_x_assum (qspec_then ‘ss’ mp_tac)
    \\ fs [Abbr‘ss’] \\ rw []
    \\ once_rewrite_tac [flatten_acc] \\ fs []
    \\ ‘ORD #")" < ORD #"*"’ by EVAL_TAC
    \\ drule lex_APPEND_split
    \\ ‘EVERY (λx. x ≠ #"#") (flatten (STRCAT indent "   ") p "")’ by
     (‘EVERY (λx. x ≠ #"#") "" ∧
       EVERY (λx. x ≠ #"#") (STRCAT indent "   ")’ by
        (fs [] \\ fs [EVERY_MEM] \\ strip_tac \\ res_tac \\ fs [])
      \\ imp_res_tac no_hash_flatten)
    \\ disch_then drule \\ fs []
    \\ disch_then (qspecl_then [‘[]’,‘[]’] mp_tac)
    \\ fs [] \\ rw [] \\ EVAL_TAC)
  THEN1 fs [flatten_def,pretty2toks_def,lexer_def]
  \\ fs [pretty2toks_def,flatten_def]
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘white_space:string ++ _’
  \\ ‘EVERY (λc. c = #" " ∨ c = #"\n") white_space ∧ white_space ≠ []’
        by (fs [Abbr‘white_space’] \\ rw [])
  \\ ‘∃hws tws. white_space = hws :: tws’ by
        (Cases_on ‘white_space’ \\ fs [])
  \\ pop_assum (fn th => once_rewrite_tac [th] \\ assume_tac (GSYM th))
  \\ ‘ORD hws < ORD #"*"’ by gvs[]
  \\ drule lex_APPEND_split
  \\ once_rewrite_tac [flatten_acc]
  \\ ‘EVERY (λc. c = #" " ∨ c = #"\n") tws’ by gvs[]
  \\ simp[]
  \\ ‘EVERY (λx. x ≠ #"#") (flatten indent p "")’
    by (irule $ iffRL no_hash_flatten >> gs[EVERY_MEM] >> strip_tac >>
        first_x_assum drule >> simp[])
  \\ asm_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [lex_acc]
  \\ gvs [lex_indent, lex_def]
QED

Theorem pretty2toks_annotate:
  ∀p. pretty2toks (annotate p) = pretty2toks p
Proof
  Induct \\ fs [annotate_def,pretty2toks_def]
QED

Theorem pretty2toks_smart_remove_all:
  ∀p. pretty2toks (remove_all p) = pretty2toks p
Proof
  Induct \\ fs [remove_all_def,pretty2toks_def]
QED

Theorem pretty2toks_smart_remove:
  ∀p n i. pretty2toks (smart_remove i n p) = pretty2toks p
Proof
  Induct \\ fs [smart_remove_def,pretty2toks_def]
  \\ rw [pretty2toks_smart_remove_all,pretty2toks_def]
QED

Theorem read_num_append:
  ∀xs acc ys.
    read_num c1 c2 x y acc (xs ++ ys) =
      let (k,t) = read_num c1 c2 x y acc xs in
        if t = [] then read_num c1 c2 x y k ys else (k,t ++ ys)
Proof
  Induct \\ fs [read_num_def] \\ rw []
QED

Theorem read_num_num2str:
  ∀n acc.
    read_num #"0" #"9" 10 48 acc (num2str n) = (acc * 10 ** LENGTH (num2str n) + n,[])
Proof
  ho_match_mp_tac num2str_ind
  \\ gen_tac \\ strip_tac
  \\ once_rewrite_tac [num2str_def] \\ fs []
  \\ IF_CASES_TAC \\ fs []
  THEN1 fs [read_num_def]
  \\ fs [read_num_append]
  \\ fs [read_num_def]
  \\ ‘n MOD 10 < 10’ by fs [MOD_LESS]
  \\ ‘n MOD 10 + 48 < 256’ by simp []
  \\ simp [ORD_CHR] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [GSYM ADD1,EXP]
  \\ ‘0 < 10n’ by fs []
  \\ drule DIVISION
  \\ disch_then (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
  \\ fs []
  \\ once_rewrite_tac [ADD_COMM]
  \\ once_rewrite_tac [MULT_COMM]
  \\ simp [ADD_DIV_ADD_DIV]
QED

Theorem read_num_num2ascii:
  ∀n x acc.
    num2ascii n = SOME x ⇒
    read_num #"*" #"z" 256 0 acc x = (acc * 256 ** LENGTH x + n,[])
Proof
  ho_match_mp_tac num2ascii_ind
  \\ gen_tac \\ strip_tac
  \\ once_rewrite_tac [num2ascii_def] \\ fs []
  \\ IF_CASES_TAC \\ fs [AllCaseEqs(),PULL_EXISTS]
  THEN1 fs [read_num_def]
  \\ rw [] \\ fs []
  \\ fs [read_num_append]
  \\ fs [read_num_def]
  \\ fs [GSYM ADD1,EXP]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ ‘0 < 256n’ by fs []
  \\ drule DIVISION
  \\ disch_then (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
  \\ fs []
  \\ once_rewrite_tac [ADD_COMM]
  \\ once_rewrite_tac [MULT_COMM]
  \\ simp [ADD_DIV_ADD_DIV]
QED

Theorem num2str_not_nil:
  num2str n ≠ []
Proof
  once_rewrite_tac [num2str_def] \\ rw [] \\ fs []
QED

Theorem num2str_cons_IMP:
  ∀n h t.
    num2str n = STRING h t ⇒
    ORD #"0" ≤ ORD h ∧ ORD h ≤ ORD #"9"
Proof
  ho_match_mp_tac num2str_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [num2str_def] \\ rw [] \\ fs []
  \\ Cases_on ‘num2str (n DIV 10)’ \\ gvs[num2str_not_nil]
QED

Theorem num2ascii_SOME_IMP:
  ∀n x.
    num2ascii n = SOME x ⇒
    ∃c cs. x = c::cs ∧ (ORD #"*" ≤ ORD c ∧ ORD c ≤ ORD #"z" ∧ ORD c ≠ ORD #".")
Proof
  ho_match_mp_tac num2ascii_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [num2ascii_def]
  \\ rw [] \\ fs [AllCaseEqs()] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem lex_name2str:
  lex p (name2str n) [] = [p n]
Proof
  fs [name2str_def]
  \\ BasicProvers.CASE_TAC
  THEN1
   (pop_assum kall_tac
    \\ Cases_on ‘num2str n’
    \\ fs [lex_def,num2str_not_nil]
    \\ imp_res_tac num2str_cons_IMP
    \\ rw [] \\ fs [lex_def]
    \\ last_assum (assume_tac o GSYM) \\ fs []
    \\ rewrite_tac [read_num_num2str] \\ fs [num2str_not_nil,lex_def])
  \\ fs [ascii_name_def,AllCaseEqs()]
  \\ imp_res_tac num2ascii_SOME_IMP
  \\ fs [lex_def]
  \\ rw [] \\ fs []
  \\ fs [read_num_def]
  \\ drule read_num_num2ascii \\ fs [read_num_def]
  \\ disch_then (qspec_then ‘0’ mp_tac) \\ fs [lex_def]
QED

Definition any_list_def:
  any_list [] e = e ∧
  any_list (x::xs) e = Pair x (any_list xs e)
End

Theorem dest_list_IMP:
  ∀v l e. dest_list v = (l,e) ⇒ v = any_list l e ∧ isNum e
Proof
  Induct_on ‘l’ \\ fs []
  \\ Cases_on ‘v’ \\ fs [dest_list_def,any_list_def]
  \\ rw [] \\ pairarg_tac \\ fs [] \\ rw [] \\ res_tac
QED

Theorem any_list_eq_list[simp]:
  ∀xs. any_list xs (Num 0) = list xs
Proof
  Induct \\ fs [any_list_def,list_def]
QED

Theorem pretty2toks_v2pretty:
  ∀h. pretty2toks (v2pretty h) = REVERSE (v2toks h)
Proof
  gen_tac \\ completeInduct_on ‘lisp_v_size h’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ once_rewrite_tac [v2pretty_def]
  \\ reverse (Cases_on ‘h’) \\ simp []
  THEN1 simp [pretty2toks_def,Once v2toks_def,lex_name2str,lexer_def]
  \\ simp [Once v2toks_def]
  \\ ‘~isNum (Pair v v0)’ by fs []
  \\ rename [‘lisp_v_size vv’]
  \\ reverse BasicProvers.CASE_TAC
  THEN1
   (fs [dest_quote_def,lisp_printingTheory.dest_quote_def,AllCaseEqs()]
    \\ rw [pretty2toks_def,lex_def,lexer_def,lex_name2str])
  \\ reverse BasicProvers.CASE_TAC
  THEN1 (fs [dest_quote_def,lisp_printingTheory.dest_quote_def,AllCaseEqs()] \\ rw [])
  \\ pairarg_tac \\ fs [pretty2toks_def] \\ rw []
  \\ imp_res_tac dest_list_IMP \\ fs []
  \\ rpt (qpat_x_assum ‘_ = NONE’ kall_tac)
  THEN1
   (rw [] \\ Induct_on ‘l’ \\ fs [EVAL “pretty2toks (newlines [])”]
    \\ fs [list_def,dest_list_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ Cases_on ‘l = []’ \\ rw [] \\ fs [newlines_def]
    \\ Cases_on ‘l’ \\ fs [newlines_def,list_def]
    \\ fs [pretty2toks_def])
  \\ rw [] \\ Induct_on ‘l’ \\ fs []
  THEN1
   (fs [any_list_def,pretty2toks_def]
    \\ Cases_on ‘e’ \\ fs [] \\ rw []
    \\ simp [dest_list_def,Once v2pretty_def,pretty2toks_def,v2toks_def,lexer_def,
          EVAL “lexer " . "”,EVAL “pretty2toks (newlines [])”,lex_name2str])
  \\ fs [any_list_def,dest_list_def] \\ rw []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ Cases_on ‘l = []’ \\ rw [] \\ fs [newlines_def]
  THEN1 (fs [pretty2toks_def,any_list_def] \\ EVAL_TAC)
  \\ Cases_on ‘l’ \\ fs [newlines_def,any_list_def]
  \\ fs [pretty2toks_def]
QED

Theorem dropWhile_cons_imp:
  ∀s c h t.
    dropWhile (λx. x ≠ c) s = h::t ⇒
    ∃prefix. s = prefix ++ c :: t ∧ h = c ∧ EVERY (λx. x ≠ c) prefix
Proof
  Induct \\ fs [] \\ rw [] \\ res_tac \\ fs []
QED

Theorem end_line_prefix:
  ∀prefix xs.
    EVERY (λx. x ≠ #"\n") prefix ⇒
    end_line (STRCAT prefix (STRING #"\n" xs)) = xs
Proof
  Induct \\ fs [end_line_def]
QED

Theorem lex_is_comment:
  ∀c rest. is_comment c ⇒ lex NUM (c ++ rest) [] = lex NUM rest []
Proof
  ho_match_mp_tac is_comment_ind \\ rw []
  \\ fs [is_comment_def]
  \\ reverse (Cases_on ‘c = #"#"’) \\ fs []
  \\ simp [Once lex_def]
  \\ rename [‘dropWhile (λx. x ≠ #"\n") s’]
  \\ Cases_on ‘dropWhile (λx. x ≠ #"\n") s’ \\ fs []
  \\ rw [] \\ imp_res_tac dropWhile_cons_imp \\ rw []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ drule end_line_prefix \\ strip_tac \\ asm_rewrite_tac []
QED

Theorem num2ascii_no_hash:
  ∀n x. num2ascii n = SOME x ⇒ EVERY (λx. x ≠ #"#") x
Proof
  ho_match_mp_tac num2ascii_ind \\ rw [] \\ fs []
  \\ pop_assum mp_tac \\ rw [Once num2ascii_def] \\ fs [AllCaseEqs()]
  \\ res_tac \\ fs [] \\ rw []
QED

Theorem no_hash_name2str:
  EVERY (λx. x ≠ #"#") (name2str n)
Proof
  fs [name2str_def]
  \\ Cases_on ‘ascii_name n’ \\ fs []
  THEN1
   (pop_assum kall_tac \\ qid_spec_tac ‘n’
    \\ ho_match_mp_tac num2str_ind
    \\ rw [] \\ simp [Once num2str_def] \\ rw []
    \\ ‘n MOD 10 < 10’ by fs []
    \\ ‘(n MOD 10) + 48 < 256 ∧ 35 < 256’ by decide_tac
    \\ imp_res_tac CHR_11 \\ fs [])
  \\ fs [ascii_name_def,AllCaseEqs()]
  \\ imp_res_tac num2ascii_no_hash \\ fs []
QED

Theorem no_hash_smart_remove_annotate_v2pretty[simp]:
  no_hash (smart_remove m n (annotate (v2pretty h)))
Proof
  ‘∀p. no_hash (annotate p) = no_hash p’ by
    (Induct_on ‘p’ \\ rw [annotate_def,no_hash_def])
  \\ ‘∀p. no_hash (remove_all p) = no_hash p’ by
       (Induct_on ‘p’ \\ rw [remove_all_def,no_hash_def])
  \\ ‘∀m n p. no_hash (smart_remove m n p) = no_hash p’ by
       (Induct_on ‘p’ \\ rw [smart_remove_def,no_hash_def])
  \\ fs [] \\ qid_spec_tac ‘h’
  \\ ho_match_mp_tac v2pretty_ind
  \\ rw [] \\ once_rewrite_tac [v2pretty_def]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs []) \\ rw [no_hash_def]
  THEN1
   (pop_assum mp_tac \\ rpt (pop_assum kall_tac)
    \\ Induct_on ‘l'’ \\ fs [newlines_def,no_hash_def]
    \\ rw [] \\ last_x_assum mp_tac
    \\ impl_tac THEN1 fs []
    \\ Cases_on ‘l'’ \\ fs [newlines_def])
  \\ fs []
  THEN1
   (qpat_x_assum ‘∀h._’ mp_tac \\ rpt (pop_assum kall_tac)
    \\ Induct_on ‘l'’ \\ fs [newlines_def,no_hash_def]
    \\ rw [] \\ last_x_assum mp_tac
    \\ impl_tac THEN1 fs []
    \\ Cases_on ‘l'’ \\ fs [newlines_def])
  \\ fs [lisp_printingTheory.dest_quote_def,AllCaseEqs()]
  \\ rw [no_hash_name2str]
QED

Theorem lexer_vs2str:
  ∀vs coms. lexer (vs2str vs coms) = REVERSE (FLAT (MAP v2toks vs))
Proof
  Induct THEN1 (EVAL_TAC \\ fs [])
  \\ fs [vs2str_def,lexer_def] \\ gen_tac
  \\ ‘EVERY (λx. x ≠ #"#") (v2str h)’ by fs [v2str_def,no_hash_flatten]
  \\ drule (lex_APPEND_split |> Q.SPEC ‘#"\n"’
            |> CONV_RULE (PATH_CONV "lr" EVAL) |> REWRITE_RULE [])
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND] \\ fs [] \\ rw []
  \\ Cases_on ‘coms’ \\ fs []
  \\ TRY IF_CASES_TAC \\ fs []
  \\ TRY (drule lex_is_comment)
  \\ rpt strip_tac
  \\ asm_rewrite_tac [GSYM APPEND_ASSOC]
  \\ simp [Once lex_def]
  \\ simp [Once lex_def]
  \\ once_rewrite_tac [lex_acc]
  \\ fs [] \\ simp [v2str_def]
  \\ fs [lex_flatten,pretty2toks_annotate,pretty2toks_smart_remove]
  \\ fs [pretty2toks_v2pretty]
QED

Theorem lisp_v_size_any_list:
  ∀l e.
    lisp_v_size (any_list l e) = SUM (MAP lisp_v_size l) + LENGTH l + lisp_v_size e
Proof
  Induct \\ fs [any_list_def]
QED

Theorem parse_v2toks:
   ∀vs ys xs ts e.
     isNum e ⇒
     parse (REVERSE (FLAT (MAP v2toks vs)) ++ ts) (any_list ys e) xs =
     parse ts (any_list (vs ++ ys) e) xs
Proof
  gen_tac \\ completeInduct_on ‘SUM (MAP lisp_v_size vs) + LENGTH vs’
  \\ rpt strip_tac \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on ‘vs = []’ THEN1 rw []
  \\ ‘∃x l. vs = SNOC x l’ by metis_tac [SNOC_CASES]
  \\ fs [REVERSE_APPEND,SNOC_APPEND]
  \\ Cases_on ‘l ≠ []’ THEN1
   (first_assum
       (qspecl_then [‘[x]’,‘ys’,‘xs’,‘REVERSE (FLAT (MAP v2toks l)) ⧺ ts’,‘e’] mp_tac)
    \\ impl_tac THEN1 (Cases_on ‘l’ \\ fs [SUM_APPEND])
    \\ fs [] \\ strip_tac \\ fs [] \\ pop_assum kall_tac
    \\ first_assum (qspecl_then [‘l’,‘x::ys’,‘xs’,‘ts’,‘e’] mp_tac)
    \\ impl_tac THEN1 fs [SUM_APPEND]
    \\ fs [] \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND])
  \\ once_rewrite_tac [v2toks_def]
  \\ reverse (Cases_on ‘x’) \\ simp []
  THEN1 (fs [parse_def,any_list_def])
  \\ rename [‘dest_quote (Pair v1 v2)’]
  \\ ‘~isNum (Pair v1 v2)’ by fs []
  \\ rename [‘~isNum v’]
  \\ reverse (Cases_on ‘dest_quote v’) \\ fs []
  THEN1
   (rw [] \\ fs [dest_quote_def,AllCaseEqs()] \\ rw[] \\ fs []
    \\ fs [parse_def,any_list_def,quote_def,list_def])
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘e' = Num 0’ \\ fs []
  THEN1
   (fs [REVERSE_APPEND,parse_def]
    \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ rw []
    \\ first_assum (qspecl_then [‘l''’,‘[]’,‘any_list ys e::xs’,‘OPEN::ts’,‘Num 0’] mp_tac)
    \\ impl_tac THEN1
     (rw [] \\ imp_res_tac dest_list_IMP
      \\ full_simp_tac std_ss [lisp_v_size_any_list] \\ fs [])
    \\ strip_tac \\ fs [list_def]
    \\ fs [parse_def,any_list_def]
    \\ imp_res_tac dest_list_IMP \\ fs [])
  \\ fs [REVERSE_APPEND,parse_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ qpat_abbrev_tac ‘ts1 = DOT::_’
  \\ first_assum (qspecl_then [‘[e']’,‘[]’,‘any_list ys e::xs’,‘ts1’,‘Num 0’] mp_tac)
  \\ impl_tac THEN1
   (rw [] \\ imp_res_tac dest_list_IMP \\ rw [] \\ fs [lisp_v_size_any_list]
    \\ Cases_on ‘l''’ \\ fs [any_list_def]
    \\ Cases_on ‘e'’ \\ fs [dest_list_def]
    \\ pairarg_tac \\ fs [])
  \\ fs [list_def] \\ strip_tac \\ fs []
  \\ qunabbrev_tac ‘ts1’ \\ fs [parse_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND] \\ rw []
  \\ first_assum (qspecl_then [‘l''’,‘[]’,‘any_list ys e::xs’,‘OPEN::ts’,‘e'’] mp_tac)
  \\ impl_tac
  THEN1 (rw [] \\ imp_res_tac dest_list_IMP \\ rw [] \\ fs [lisp_v_size_any_list])
  \\ fs [any_list_def,parse_def]
  \\ imp_res_tac dest_list_IMP \\ fs []
QED

Theorem parse_lexer_vs2str:
  ∀vs coms ys xs. (parse (lexer (vs2str vs coms)) (Num 0) []) = list vs
Proof
  fs [lexer_vs2str] \\ rw []
  \\ assume_tac (parse_v2toks |> Q.SPECL [‘vs’,‘[]’,‘[]’,‘[]’,‘Num 0’])
  \\ fs [parse_def,any_list_def,list_def]
QED

val _ = export_theory();
