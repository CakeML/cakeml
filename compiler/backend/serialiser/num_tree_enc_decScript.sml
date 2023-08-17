(*
  Encoders and decoders to/from types represented as trees
  consisting of natural numbers.
*)
open integerTheory ml_progTheory
     astTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory mlvectorTheory mlstringTheory
     ml_translatorTheory miscTheory num_list_enc_decTheory;
open preamble;

val _ = new_theory "num_tree_enc_dec";

Datatype:
  num_tree = Tree num (num_tree list)
End

Definition num_tree_enc'_def:
  num_tree_enc' [] = List [] ∧
  num_tree_enc' ((Tree k xs)::ts) =
    Append (Append (List [k; LENGTH xs]) (num_tree_enc' xs))
           (num_tree_enc' ts)
Termination
  WF_REL_TAC ‘measure num_tree1_size’
End

Theorem fix_res_IMP:
  (x,ns1) = fix_res ns res ⇒ LENGTH ns1 ≤ LENGTH ns
Proof
  PairCases_on ‘res’ \\ rw [fix_res_def] \\ gvs []
QED

Theorem dec_ok_fix_res:
  dec_ok d ⇒ ∀ns. fix_res ns (d ns) = d ns
Proof
  fs [dec_ok_def] \\ rw [] \\ Cases_on ‘d ns’
  \\ first_x_assum (qspec_then ‘ns’ mp_tac) \\ fs []
  \\ fs [fix_res_def]
QED

Definition num_tree_dec'_def:
  num_tree_dec' c ns =
    if c = 0 then ([],ns) else
       case ns of
       | [] => ([],ns)
       | [t] => ([],ns)
       | (t::l::ns) =>
            let (ts1,ns1) = fix_res ns (num_tree_dec' l ns) in
            let (ts2,ns2) = fix_res ns1 (num_tree_dec' (c-1) ns1) in
              (Tree t ts1 :: ts2, ns2)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’
  \\ rw [] \\ imp_res_tac fix_res_IMP  \\ fs []
End

Theorem dec_ok_num_tree_dec':
  ∀l. dec_ok (num_tree_dec' l)
Proof
  fs [dec_ok_def]
  \\ ho_match_mp_tac num_tree_dec'_ind \\ rw []
  \\ once_rewrite_tac [num_tree_dec'_def]
  \\ rw [] \\ Cases_on ‘i’ \\ fs []
  \\ Cases_on ‘t’ \\ fs [fix_res_def]
  \\ Cases_on ‘num_tree_dec' h' t'’ \\ fs [fix_res_def]
  \\ Cases_on ‘num_tree_dec' (l − 1) r’ \\ fs [fix_res_def]
QED

Theorem num_tree_dec'_def = num_tree_dec'_def
  |> SIMP_RULE std_ss [MATCH_MP dec_ok_fix_res (SPEC_ALL dec_ok_num_tree_dec')];

Theorem num_tree_dec'_ind = num_tree_dec'_ind
  |> SIMP_RULE std_ss [MATCH_MP dec_ok_fix_res (SPEC_ALL dec_ok_num_tree_dec')];

Definition num_tree_enc_def:
  num_tree_enc t = num_tree_enc' [t]
End

Definition num_tree_dec_def:
  num_tree_dec ns =
    case num_tree_dec' 1 ns of
    | ([],ns) => (Tree 0 [],ns)
    | (t::ts,ns) => (t,ns)
End

Theorem dec_ok_num_tree_dec:
  dec_ok num_tree_dec
Proof
  fs [dec_ok_def,num_tree_dec_def] \\ rw []
  \\ mp_tac dec_ok_num_tree_dec' \\ fs [dec_ok_def]
  \\ disch_then (qspecl_then [‘1’,‘i’] mp_tac) \\ rpt CASE_TAC  \\ fs []
QED

Theorem num_tree_enc_dec_ok:
  enc_dec_ok num_tree_enc num_tree_dec
Proof
  fs [enc_dec_ok_def,dec_ok_num_tree_dec]
  \\ fs [num_tree_enc_def,num_tree_dec_def] \\ rw []
  \\ qsuff_tac
    ‘∀ts xs. num_tree_dec' (LENGTH ts) (append (num_tree_enc' ts) ++ xs) = (ts,xs)’
  THEN1 (disch_then (qspec_then ‘[x]’ mp_tac) \\ fs [])
  \\ ho_match_mp_tac num_tree_enc'_ind \\ rw []
  \\ once_rewrite_tac [num_tree_dec'_def] \\ fs [num_tree_enc'_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
QED

Theorem imp_enc_dec_ok:
  ∀e d.
    (∀x. d (e x) = x) ⇒
    enc_dec_ok (num_tree_enc ∘ e) ((d ## I) ∘ num_tree_dec)
Proof
  rw [] \\ irule enc_dec_ok_o \\ fs [num_tree_enc_dec_ok]
QED

Definition nth_def[simp]:
  nth n [] = Tree 0 [] ∧
  nth n (x::xs) = if n = 0 then x else nth (n-1n) xs
End

Theorem MEM_num_tree_size:
  ∀xs x. MEM x xs ⇒ num_tree_size x ≤ num_tree1_size xs
Proof
  Induct \\ fs [fetch "-" "num_tree_size_def"] \\ rw [] \\ res_tac \\ fs []
QED

(* num *)

Definition num_enc'_def:
  num_enc' n = Tree n []
End

Definition num_dec'_def[simp]:
  num_dec' (Tree n xs) = n
End

Theorem num_dec_enc'[simp]:
  num_dec' (num_enc' n) = n
Proof
  fs [num_dec'_def,num_enc'_def]
QED

(* int *)

Definition int_enc'_def:
  int_enc' n = if n < 0i then Tree (Num (0 - n)) [Tree 0 []] else Tree (Num n) []
End

Definition int_dec'_def:
  int_dec' (Tree n []) = & n ∧
  int_dec' (Tree n _) = - (& n):int
End

Theorem int_dec_enc'[simp]:
  int_dec' (int_enc' n) = n
Proof
  rw [int_dec'_def,int_enc'_def] \\ intLib.COOPER_TAC
QED

(* bool *)

Definition bool_enc'_def:
  bool_enc' F = Tree 0 [] ∧
  bool_enc' T = Tree 1 []
End

Definition bool_dec'_def:
  bool_dec' (Tree n xs) = (n = 1)
End

Theorem bool_dec_enc'[simp]:
  bool_dec' (bool_enc' b) = b
Proof
  Cases_on ‘b’ \\ fs [bool_dec'_def,bool_enc'_def]
QED

(* chr *)

Definition chr_enc'_def:
  chr_enc' c = Tree (ORD c) []
End

Definition chr_dec'_def:
  chr_dec' (Tree n xs) = if n < 256 then CHR n else CHR 32
End

Theorem chr_enc'_thm[simp]:
  chr_dec' (chr_enc' c) = c
Proof
  fs [chr_enc'_def,chr_dec'_def,ORD_BOUND,CHR_ORD]
QED

(* list *)

Definition list_enc'_def:
  list_enc' f xs = Tree 0 (MAP f xs)
End

Definition list_dec'_def:
  list_dec' f (Tree _ xs) = MAP f xs
End

Theorem list_enc'_mem:
  (∀x. MEM x xs ⇒ g (f x) = x) ⇒
  list_dec' g (list_enc' f xs) = xs
Proof
  fs [list_enc'_def,list_dec'_def,MAP_MAP_o,o_DEF]
  \\ Induct_on ‘xs’ \\ fs []
QED

Theorem list_enc'_thm[simp]:
  (∀x. g (f x) = x) ⇒
  list_dec' g (list_enc' f xs) = xs
Proof
  fs [list_enc'_def,list_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem list_enc'_cong:
  ∀l1 l2 f f'.
    (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒
    (list_enc' f l1 = list_enc' f' l2)
Proof
  fs [] \\ Induct \\ fs [list_enc'_def]
QED

Theorem list_dec'_cong:
  ∀l1 l2 f f'.
    (l1 = l2) ∧ (∀x. MEM x (list_dec' I l2) ⇒ (f x = f' x)) ⇒
    (list_dec' f l1 = list_dec' f' l2)
Proof
  fs [] \\ Induct \\ fs [list_dec'_def,MAP_EQ_f]
QED

val _ = app DefnBase.export_cong ["list_enc'_cong", "list_dec'_cong"];

(* string *)

Definition list_chr_dec'_def:
  list_chr_dec' [] = [] ∧
  list_chr_dec' (x::xs) = chr_dec' x :: list_chr_dec' xs
End

Definition string_dec'_def:
  string_dec' (Tree _ xs) = IMPLODE (list_chr_dec' xs)
End

Theorem string_dec'_intro:
  list_dec' chr_dec' = string_dec'
Proof
  fs [FUN_EQ_THM] \\ Cases
  \\ fs [list_dec'_def,string_dec'_def]
  \\ Induct_on ‘l’ \\ fs [list_chr_dec'_def]
QED

(* pair *)

Definition pair_enc'_def:
  pair_enc' f f' (x,y) = Tree 0 [f x; f' y]
End

Definition pair_dec'_def:
  pair_dec' f f' (Tree _ xs) = (f (nth 0 xs), f' (nth 1 xs))
End

Theorem pair_enc'_fst_snd:
  g (f (FST x)) = FST x ∧ g' (f' (SND x)) = SND x ⇒
  pair_dec' g g' (pair_enc' f f' x) = x
Proof
  PairCases_on ‘x’ \\ fs [pair_enc'_def,pair_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem pair_enc'_thm[simp]:
  (∀x. g (f x) = x) ∧  (∀x. g' (f' x) = x) ⇒
  pair_dec' g g' (pair_enc' f f' x) = x
Proof
  PairCases_on ‘x’ \\ fs [pair_enc'_def,pair_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem pair_enc'_cong:
  ∀l1 l2 f f' g g'.
    (l1 = l2) ∧
    (∀x. x = FST l1 ⇒ (f x = f' x)) ∧
    (∀x. x = SND l1 ⇒ (g x = g' x)) ⇒
    (pair_enc' f g l1 = pair_enc' f' g' l2)
Proof
  fs [] \\ Cases \\ fs [pair_enc'_def]
QED

Theorem pair_dec'_cong:
  ∀l1 l2 f f' g g'.
    (l1 = l2) ∧
    (∀x. x = nth 0 (list_dec' I l1) ⇒ (f x = f' x)) ∧
    (∀x. x = nth 1 (list_dec' I l1) ⇒ (g x = g' x)) ⇒
    (pair_dec' f g l1 = pair_dec' f' g' l2)
Proof
  fs [] \\ Cases \\ fs [pair_dec'_def,list_dec'_def]
QED

val _ = app DefnBase.export_cong ["pair_enc'_cong", "pair_dec'_cong"];

(* option *)

Definition option_enc'_def:
  option_enc' f NONE = Tree 0 [] ∧
  option_enc' f (SOME x) = Tree 1 [f x]
End

Definition option_dec'_def:
  option_dec' f (Tree n xs) = if n = 0 then NONE else SOME (f (nth 0 xs))
End

Theorem option_enc'_thm[simp]:
  (∀x. g (f x) = x) ⇒
  option_dec' g (option_enc' f x) = x
Proof
  Cases_on ‘x’ \\ fs [option_enc'_def,option_dec'_def,MAP_MAP_o,o_DEF]
QED

(* word64 *)

Definition word64_enc'_def:
  word64_enc' (n:word64) = Tree (w2n n) []
End

Definition word64_dec'_def[simp]:
  word64_dec' (Tree n xs) = n2w n :word64
End

Theorem word64_dec_enc'[simp]:
  word64_dec' (word64_enc' n) = n
Proof
  fs [word64_dec'_def,word64_enc'_def]
QED

val _ = export_theory();
