(*
  Encoders and decoders to/from types represented as prefixes of lists
  of natural numbers.
*)
open integerTheory ml_progTheory
     astTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory mlvectorTheory mlstringTheory
     ml_translatorTheory miscTheory backend_commonTheory;
open preamble;

val _ = new_theory "num_list_enc_dec";

Definition dec_ok_def:
  dec_ok dec ⇔
    ∀i. LENGTH ((SND (dec i)):num list) ≤ LENGTH (i:num list)
End

Definition enc_dec_ok_def:
  enc_dec_ok enc dec ⇔
    dec_ok dec ∧
    ∀x (xs:num list). dec (append (enc x) ++ xs) = (x,xs)
End

Theorem dec_ok_simp[simp]:
  dec_ok ((f ## I) ∘ d) = dec_ok d
Proof
  fs [dec_ok_def]
QED

Theorem enc_dec_ok_o:
  enc_dec_ok e d ∧ (∀x. f (g x) = x) ⇒
  enc_dec_ok (e ∘ g) ((f ## I) ∘ d)
Proof
  fs [enc_dec_ok_def]
QED

(* unit *)

Definition unit_enc_def:
  unit_enc (n:unit) = List []
End

Definition unit_dec_def:
  unit_dec ns = ((),ns:num list)
End

Theorem unit_enc_dec_ok:
  enc_dec_ok unit_enc unit_dec
Proof
  fs [enc_dec_ok_def,unit_dec_def,unit_enc_def,dec_ok_def]
QED

(* num *)

Definition num_enc_def:
  num_enc n = List [n:num]
End

Definition num_dec_def:
  num_dec ns =
    case ns of
    | [] => (0:num,[])
    | (r::rs) => (r,rs)
End

Theorem num_enc_dec_ok:
  enc_dec_ok num_enc num_dec
Proof
  fs [enc_dec_ok_def,num_dec_def,num_enc_def]
  \\ fs [dec_ok_def,num_dec_def]
  \\ Cases \\ fs []
QED

(* list *)

Definition list_enc_def:
  list_enc e xs =
    Append (List [LENGTH xs]) (FOLDR (\x y. Append (e x) y) (List []) xs)
End

Definition list_dec'_def:
  list_dec' 0 d ns = ([],ns) ∧
  list_dec' (SUC k) d ns =
    let (x1,ns1) = d ns in
    let (xs1,ns2) = list_dec' k d ns1 in
      (x1 :: xs1, ns2)
End

Definition list_dec_def:
  list_dec d ns =
    case ns of
    | [] => ([],[])
    | (n::ns) => list_dec' n d ns
End

Theorem list_dec'_length:
  ∀k d ns x ns1.
    list_dec' k d ns = (x,ns1) ∧ dec_ok d ⇒
    LENGTH ns1 ≤ LENGTH ns
Proof
  Induct \\ fs [list_dec'_def]
  \\ rw [] \\ Cases_on ‘d ns’ \\ fs []
  \\ Cases_on ‘list_dec' k d r’ \\ fs []
  \\ rw [] \\ res_tac \\ fs [dec_ok_def]
  \\ first_x_assum (qspec_then ‘ns’ mp_tac) \\ fs []
QED

Theorem list_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (list_enc e) (list_dec d)
Proof
  fs [enc_dec_ok_def,list_dec_def,list_enc_def] \\ strip_tac
  \\ conj_tac THEN1
   (fs [dec_ok_def]
    \\ fs [list_dec_def]
    \\ Cases \\ fs []
    \\ Cases_on ‘list_dec' h d t’ \\ fs []
    \\ drule list_dec'_length
    \\ fs [dec_ok_def])
  \\ Induct \\ fs [list_dec'_def] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
QED

(* bool *)

Definition bool_enc_def:
  bool_enc = num_enc o (λb. if b then 1 else 0)
End

Definition bool_dec_def:
  bool_dec = (((=) 1) ## I) o num_dec
End

Theorem bool_enc_dec_ok:
  enc_dec_ok bool_enc bool_dec
Proof
  fs [bool_enc_def,bool_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_enc_dec_ok]
  \\ Cases \\ fs []
QED

(* int *)

Definition int_enc_def:
  int_enc =
    num_enc o (λn. if n < 0 then 2 * Num (ABS n) + 1 else 2 * Num (ABS n))
End

Definition int_dec_def:
  int_dec =
    ((λr. if ODD r then 0i - & (r DIV 2) else & (r DIV 2)) ## I) o num_dec
End

Theorem int_enc_dec_ok:
  enc_dec_ok int_enc int_dec
Proof
  fs [int_enc_def,int_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_enc_dec_ok]
  \\ Cases \\ fs [] \\ fs [int_dec_def]
  \\ fs [ODD_EVEN,EVEN_DOUBLE,EVEN_ADD,TWOxDIV2]
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs [DIV_MULT]
QED

(* word *)

Definition word_enc_def:
  word_enc = num_enc o w2n
End

Definition word_dec_def:
  word_dec = (n2w ## I) o num_dec
End

Theorem word_enc_dec_ok:
  enc_dec_ok word_enc word_dec
Proof
  fs [word_enc_def,word_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_enc_dec_ok]
QED

(* char *)

Definition char_enc_def:
  char_enc = num_enc o ORD
End

Definition char_dec_def:
  char_dec = (CHR ## I) o num_dec
End

Theorem char_enc_dec_ok:
  enc_dec_ok char_enc char_dec
Proof
  fs [char_enc_def,char_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_enc_dec_ok,CHR_ORD]
QED

(* prod *)

Definition prod_enc_def:
  prod_enc e1 e2 (x,y) = Append (e1 x) (e2 y)
End

Definition prod_dec_def:
  prod_dec d1 d2 ns =
    let (x,ns1) = d1 ns in
    let (y,ns2) = d2 ns1 in
      ((x,y),ns2)
End

Theorem prod_enc_dec_ok:
  enc_dec_ok e1 d1 ∧
  enc_dec_ok e2 d2 ⇒
  enc_dec_ok (prod_enc e1 e2) (prod_dec d1 d2)
Proof
  fs [enc_dec_ok_def,prod_enc_def,FORALL_PROD]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,prod_dec_def,LET_THM] \\ rw []
  \\ fs [dec_ok_def,prod_dec_def] \\ rw []
  \\ Cases_on ‘d1 i’ \\ fs []
  \\ Cases_on ‘d2 r’ \\ fs []
  \\ last_x_assum (qspec_then ‘i’ assume_tac)
  \\ last_x_assum (qspec_then ‘r’ assume_tac)
  \\ rfs []
QED

(* option *)

Definition option_enc_def:
  option_enc e NONE = List [0n] ∧
  option_enc e (SOME y) = Append (List [1n]) (e y)
End

Definition option_dec_def:
  option_dec d ns =
    case ns of
    | [] => (NONE, ns)
    | (n::ns) => if n = 0n then (NONE,ns) else (SOME ## I) (d ns)
End

Theorem option_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (option_enc e) (option_dec d)
Proof
  fs [enc_dec_ok_def,option_enc_def]
  \\ rpt strip_tac
  THEN1
   (fs [dec_ok_def,option_dec_def]
    \\ Cases \\ fs [] \\ rw []
    \\ rpt (last_x_assum (qspec_then ‘t’ mp_tac))
    \\ Cases_on ‘d t’ \\ fs [])
  \\ Cases_on ‘x’ \\ fs [option_enc_def] \\ fs [option_dec_def]
QED

(* sum *)

Definition sum_enc_def:
  sum_enc e1 e2 (INL x) = Append (List [0n]) (e1 x) ∧
  sum_enc e1 e2 (INR y) = Append (List [1n]) (e2 y)
End

Definition sum_dec_def:
  sum_dec d1 d2 ns =
    case ns of
    | [] => (INL ## I) (d1 ns)
    | (n::ns) => if n = 0n then (INL ## I) (d1 ns) else (INR ## I) (d2 ns)
End

Theorem sum_enc_dec_ok:
  enc_dec_ok e1 d1 ∧
  enc_dec_ok e2 d2 ⇒
  enc_dec_ok (sum_enc e1 e2) (sum_dec d1 d2)
Proof
  fs [enc_dec_ok_def,sum_enc_def]
  \\ rpt strip_tac
  THEN1
   (fs [dec_ok_def,sum_dec_def]
    \\ Cases \\ fs []
    THEN1 (last_x_assum (qspec_then ‘[]’ mp_tac) \\ Cases_on ‘d1 []’ \\ fs [])
    \\ rw []
    \\ rpt (last_x_assum (qspec_then ‘t’ mp_tac))
    \\ Cases_on ‘d1 t’ \\ fs [] \\ Cases_on ‘d2 t’ \\ fs [])
  \\ Cases_on ‘x’ \\ fs [sum_enc_def] \\ fs [sum_dec_def] \\ fs [AllCaseEqs()]
QED

(* sptree *)

Definition spt_enc'_def:
  spt_enc' e LN = List [0n] ∧
  spt_enc' e (LS x) = Append (List [1]) (e x) ∧
  spt_enc' e (BN t1 t2) =
    Append (List [2]) (Append (spt_enc' e t1) (spt_enc' e t2)) ∧
  spt_enc' e (BS t1 x t2) =
    Append (List [3]) (Append (spt_enc' e t1) (Append (e x) (spt_enc' e t2)))
End

Definition fix_res_def:
  fix_res ns (x,ns') =
    if LENGTH ns < LENGTH ns' then (x,ns) else (x,ns')
End

Triviality fix_res_IMP:
  (x,ns2) = fix_res ns1 y ⇒ LENGTH ns2 ≤ LENGTH ns1
Proof
  Cases_on ‘y’ \\ rw [fix_res_def]
QED

Definition spt_dec'_def:
  spt_dec' d ns =
    if PRECONDITION (dec_ok d) then
    case ns of
    | [] => (LN,ns)
    | (n::ns) =>
       if n = 0:num then (LN,ns)
       else if n = 1 then
         let (x,ns) = d ns in (LS x,ns)
       else if n = 2 then
         let (t1,ns') = fix_res ns (spt_dec' d ns) in
         let (t2,ns') = spt_dec' d ns' in
           (BN t1 t2,ns')
       else
         let (t1,ns1) = fix_res ns (spt_dec' d ns) in
         let (x, ns2) = fix_res ns1 (d ns1) in
         let (t2,ns3) = spt_dec' d ns2 in
           (BS t1 x t2,ns3)
    else (LN,ns)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ \\ rw []
  \\ imp_res_tac fix_res_IMP \\ fs []
End

Theorem spt_dec'_ok:
  dec_ok (spt_dec' d)
Proof
  fs [dec_ok_def]
  \\ qid_spec_tac ‘d’
  \\ ho_match_mp_tac spt_dec'_ind \\ rw []
  \\ once_rewrite_tac [spt_dec'_def]
  \\ rw [] \\ Cases_on ‘i’ \\ fs []
  \\ rw [] \\ fs []
  THEN1
    (fs [PRECONDITION_def,dec_ok_def]
     \\ Cases_on ‘d t’ \\ fs []
     \\ first_x_assum (qspec_then ‘t’ mp_tac) \\ fs [])
  THEN1
    (Cases_on ‘spt_dec' d t’ \\ fs []
     \\ Cases_on ‘spt_dec' d r’ \\ fs [fix_res_def])
  \\ Cases_on ‘spt_dec' d t’ \\ fs []
  \\ fs [PRECONDITION_def,dec_ok_def]
  \\ Cases_on ‘d r’ \\ fs []
  \\ Cases_on ‘spt_dec' d r'’ \\ fs []
  \\ first_x_assum (qspec_then ‘r’ mp_tac) \\ fs [fix_res_def]
  \\ rw [] \\ fs []
QED

Theorem dec_ok_fix_res:
  dec_ok d ⇒ ∀ns. fix_res ns (d ns) = d ns
Proof
  fs [dec_ok_def] \\ rw [] \\ Cases_on ‘d ns’
  \\ first_x_assum (qspec_then ‘ns’ mp_tac) \\ fs []
  \\ fs [fix_res_def]
QED

Theorem remove_fix_res:
  (dec_ok d ⇒ ∀ns. fix_res ns (d ns) = d ns) ∧
  (PRECONDITION (dec_ok d) ⇒ ∀ns. fix_res ns (d ns) = d ns)
Proof
  fs [PRECONDITION_def,dec_ok_fix_res]
QED

Theorem spt_dec'_def =
    spt_dec'_def |> SIMP_RULE std_ss [remove_fix_res,
       MATCH_MP dec_ok_fix_res spt_dec'_ok];

Theorem spt_dec'_ind =
    spt_dec'_ind |> SIMP_RULE std_ss [remove_fix_res,GSYM AND_IMP_INTRO,
       MATCH_MP dec_ok_fix_res spt_dec'_ok]
       |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Theorem spt_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (spt_enc' e) (spt_dec' d)
Proof
  fs [enc_dec_ok_def,spt_dec'_ok] \\ rw []
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘x’
  \\ Induct
  \\ simp [spt_enc'_def,Once spt_dec'_def] \\ rw []
  \\ fs [PRECONDITION_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ fs []
QED

Definition spt_enc_def:
  spt_enc e =
    sum_enc
      (list_enc (prod_enc num_enc e)) (spt_enc' e) o
      (λt. if wf t then INL (toAList t) else INR t)
End

Definition spt_dec_def:
  spt_dec d =
    ((λx. case x of INL xs => fromAList xs | INR t => t) ## I) o
     sum_dec (list_dec (prod_dec num_dec d)) (spt_dec' d)
End

Theorem spt_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (spt_enc e) (spt_dec d)
Proof
  rw [spt_enc_def,spt_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ conj_tac
  THEN1
   (match_mp_tac sum_enc_dec_ok
    \\ fs [spt_enc_dec_ok]
    \\ match_mp_tac list_enc_dec_ok
    \\ match_mp_tac prod_enc_dec_ok
    \\ fs [num_enc_dec_ok])
  \\ rw [] \\ fs [fromAList_toAList]
QED

(* num_tree *)

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

(* namespace -- instantiated to (string, string, 'a) *)

Definition namespace_enc_def:
  namespace_enc e (Bind xs ys) =
    (let ns1 = list_enc (prod_enc (list_enc char_enc) (list_enc char_enc)) xs in
     let ns2 = namespace_enc_list e ys in
       Append ns1 ns2) ∧
  namespace_enc_list e [] = List [0] ∧
  namespace_enc_list e ((m,x)::xs) =
    Append (Append (List [1]) (e m))
      (Append (namespace_enc e x) (namespace_enc_list e xs))
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (_,x) => namespace_size (K 0) (K 0) (K 0) x
                           | INR (_,x) => namespace1_size (K 0) (K 0) (K 0) x)’
End

Definition namespace_dec_def:
  namespace_dec d ns =
    (if PRECONDITION (dec_ok d) then
     if ns = [] then (Bind [] [],ns) else
       let (xs,ns1) = list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)) ns in
       let (ys,ns2) = namespace_dec_list d ns1 in
         (Bind xs ys,ns2)
     else (Bind [] [],ns)) ∧
  namespace_dec_list d ns =
    if PRECONDITION (dec_ok d) then
      case ns of
      | [] => ([],ns)
      | (n::rest) =>
        if n = 0n then ([],rest) else
          let (m,ns) = d rest in
          let (x,ns) = fix_res ns (namespace_dec d ns) in
          let (ys,ns) = namespace_dec_list d ns in
            ((m,x)::ys,ns)
    else ([],ns)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (_,ns) => LENGTH ns
                           | INR (_,ns) => LENGTH ns)’
  \\ reverse (rw [] \\ imp_res_tac fix_res_IMP \\ fs [])
  \\ TRY
   (fs [PRECONDITION_def,dec_ok_def]
    \\ rpt (qpat_x_assum ‘(_,_) = _’ (assume_tac o GSYM))
    \\ first_x_assum (qspec_then ‘rest’ mp_tac) \\ fs [] \\ NO_TAC)
  \\ Cases_on ‘ns’ \\ fs []
  \\ fs [list_dec_def]
  \\ pop_assum (assume_tac o GSYM)
  \\ imp_res_tac list_dec'_length
  \\ pop_assum mp_tac \\ impl_tac \\ fs []
  \\ qsuff_tac ‘enc_dec_ok
                (prod_enc (list_enc char_enc) (list_enc char_enc))
                (prod_dec (list_dec char_dec) (list_dec char_dec))’
  THEN1 (fs [enc_dec_ok_def])
  \\ match_mp_tac prod_enc_dec_ok \\ fs []
  \\ match_mp_tac list_enc_dec_ok \\ fs [char_enc_dec_ok]
End

Theorem dec_ok_namespace_dec:
  dec_ok d ⇒ dec_ok (namespace_dec d)
Proof
  rw [] \\ simp [dec_ok_def]
  \\ qsuff_tac ‘
    (∀(d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec d i)) ≤ LENGTH i) ∧
    (∀(d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec_list d i)) ≤ LENGTH i)’
  THEN1 metis_tac [] \\ pop_assum kall_tac
  \\ ho_match_mp_tac namespace_dec_ind \\ rw []
  \\ once_rewrite_tac [namespace_dec_def]
  \\ fs [ml_translatorTheory.PRECONDITION_def,UNCURRY]
  \\ rw [] \\ fs []
  THEN1
   (Cases_on ‘list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)) i’ \\ fs []
    \\ ‘dec_ok (list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)))’ by
      metis_tac [list_enc_dec_ok, prod_enc_dec_ok, char_enc_dec_ok, enc_dec_ok_def]
    \\ fs [dec_ok_def] \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ fs [])
  \\ Cases_on ‘i’ \\ fs []
  \\ Cases_on ‘h=0’ \\ fs []
  \\ Cases_on ‘d t’ \\ fs []
  \\ Cases_on ‘namespace_dec d r’ \\ fs []
  \\ Cases_on ‘fix_res r (q',r')’ \\ fs []
  \\ match_mp_tac LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
  \\ imp_res_tac (GSYM fix_res_IMP)
  \\ fs [dec_ok_def]
  \\ first_x_assum (qspec_then ‘t’ mp_tac) \\ fs []
QED

Triviality fix_res_namespace_dec:
  PRECONDITION (dec_ok d) ⇒
  fix_res ns (namespace_dec d ns) = namespace_dec d ns
Proof
  metis_tac [dec_ok_namespace_dec,dec_ok_fix_res,
             ml_translatorTheory.PRECONDITION_def]
QED

Theorem namespace_dec_def = namespace_dec_def
  |> SIMP_RULE std_ss [fix_res_namespace_dec];

Theorem namespace_dec_ind = namespace_dec_ind
  |> SIMP_RULE std_ss [fix_res_namespace_dec,GSYM AND_IMP_INTRO]
  |> SIMP_RULE bool_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Theorem namespace_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (namespace_enc e) (namespace_dec d)
Proof
  fs [enc_dec_ok_def,dec_ok_namespace_dec]
  \\ strip_tac
  \\ strip_tac \\ pop_assum mp_tac
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘e’
  \\ qsuff_tac ‘
        (∀e x.
            (∀x xs. d (append (e x) ++ xs) = (x,xs)) ⇒
            ∀xs. namespace_dec d (append (namespace_enc e x) ++ xs) = (x,xs)) ∧
        (∀e x.
            (∀x xs. d (append (e x) ++ xs) = (x,xs)) ⇒
            ∀xs. namespace_dec_list d (append (namespace_enc_list e x) ++ xs) = (x,xs))’
  THEN1 metis_tac []
  \\ ho_match_mp_tac namespace_enc_ind \\ rw [] \\ fs []
  \\ fs [namespace_enc_def]
  \\ once_rewrite_tac [namespace_dec_def] \\ fs []
  \\ fs [ml_translatorTheory.PRECONDITION_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ IF_CASES_TAC THEN1 fs [list_enc_def]
  \\ pop_assum kall_tac
  \\ ‘enc_dec_ok
      (list_enc (prod_enc (list_enc char_enc) (list_enc char_enc)))
      (list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)))’ by
    metis_tac [list_enc_dec_ok, prod_enc_dec_ok, char_enc_dec_ok, enc_dec_ok_def]
  \\ fs [enc_dec_ok_def] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
QED

(* tra *)

Definition num_enc'_def:
  num_enc' n = Tree n []
End

Definition num_dec'_def:
  num_dec' (Tree n xs) = n
End

Theorem num_dec_enc'[simp]:
  num_dec' (num_enc' n) = n
Proof
  fs [num_dec'_def,num_enc'_def]
QED

Definition tra_enc'_def:
  tra_enc' None = Tree 0 [] ∧
  tra_enc' (Union t1 t2) = Tree 1 [tra_enc' t1; tra_enc' t2] ∧
  tra_enc' (Cons t n) = Tree 2 [tra_enc' t; num_enc' n] ∧
  tra_enc' (SourceLoc n1 n2 n3 n4) =
    Tree 3 [num_enc' n1; num_enc' n2; num_enc' n3; num_enc' n4]
End

Definition tra_dec'_def:
  tra_dec' (Tree n xs) =
    if n = 0 then None
    else if n = 1 then
      case xs of
      | [x1;x2] => Union (tra_dec' x1) (tra_dec' x2)
      | _ => None
    else if n = 2 then
      case xs of
      | [x1;x2] => Cons (tra_dec' x1) (num_dec' x2)
      | _ => None
    else
      case xs of
      | [x1;x2;x3;x4] => SourceLoc (num_dec' x1) (num_dec' x2) (num_dec' x3) (num_dec' x4)
      | _ => None
End

Definition tra_enc_def:
  tra_enc = num_tree_enc o tra_enc'
End

Definition tra_dec_def:
  tra_dec = (tra_dec' ## I) o num_tree_dec
End

Theorem tra_enc_dec_ok:
  enc_dec_ok tra_enc tra_dec
Proof
  fs [tra_enc_def,tra_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_tree_enc_dec_ok]
  \\ Induct
  \\ fs [tra_enc'_def,tra_dec'_def]
QED

Definition enc_def:
  enc [] = [] ∧
  enc (n::ns) = if n < 40n then CHR n :: enc ns
                else CHR ((n MOD 40) + 40) :: enc ((n DIV 40)::ns)
End

Definition dec_next_def:
  dec_next k l [] = (k,[]) ∧
  dec_next k l (n::ns) =
    if ORD n < 40 then (k + l * ORD n, ns)
    else dec_next (k + l * (ORD n - 40)) (l * 40) ns
End

Triviality dec_next_LENGTH:
  ∀k ks n l t. (k,ks) = dec_next n l t ⇒ LENGTH ks ≤ LENGTH t
Proof
  Induct_on ‘t’ \\ fs [dec_next_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Definition dec_def:
  dec ns =
    if NULL ns then [] else
      let (k,ks) = dec_next 0 1 ns in
        k :: dec ks
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ pop_assum mp_tac
  \\ Cases_on ‘ns’ \\ fs []
  \\ once_rewrite_tac [dec_next_def]
  \\ rw [] \\ imp_res_tac dec_next_LENGTH \\ fs []
End

Theorem dec_next_enc:
  ∀h l ns k.
    dec_next k (40 ** l) (enc (h::ns)) = (k + (40 ** l) * h, enc ns)
Proof
  completeInduct_on ‘h’ \\ rw []
  \\ simp [Once enc_def] \\ rw []
  \\ fs [dec_next_def,ORD_CHR]
  THEN1 (‘h < 256’ by fs [] \\ fs [ORD_CHR])
  \\ ‘ORD (CHR (h MOD 40 + 40)) = h MOD 40 + 40’ by
   (‘h MOD 40 < 40’ by fs []
    \\ ‘h MOD 40 + 40 < 256’ by decide_tac
    \\ full_simp_tac std_ss [ORD_CHR])
  \\ fs []
  \\ ‘h DIV 40 < h’ by fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘SUC l’ mp_tac) \\ fs [EXP]
  \\ disch_then kall_tac
  \\ fs []
  \\ ‘0 < 40n’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘h’ assume_tac)
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp [Once th])
QED

Theorem dec_enc:
  ∀ns. dec (enc ns) = ns
Proof
  Induct THEN1 EVAL_TAC
  \\ simp [Once dec_def] \\ rw []
  \\ fs [dec_next_enc |> SPEC_ALL |> Q.INST [‘l’|->‘0’] |> SIMP_RULE std_ss []]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ fs [] \\ completeInduct_on ‘h’
  \\ simp [Once enc_def] \\ rw []
QED


(*
  closLang$exp (* rec *)
  val_approx (* rec *)
  bvl$exp (* rec *)
  var_name

  closLang$exp = Var tra num
      | If tra exp exp exp
      | Let tra (exp list) exp
      | Raise tra exp
      | Handle tra exp exp
      | Tick tra exp
      | Call tra num (* ticks *) num (* loc *) (exp list) (* args *)
      | App tra (num option) exp (exp list)
      | Fn mlstring (num option) (num list option) num exp
      | Letrec (mlstring list) (num option) (num list option) ((num # exp) list) exp
      | Op tra op (exp list)

  bvl$exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (num option) (exp list)
      | Op closLang$op (exp list)

  val_approx =
    ClosNoInline num num        (* location in code table, arity *)
  | Clos num num exp num        (* loc, arity, body, body size *)
  | Tuple num (val_approx list) (* conses or tuples *)
  | Int int                     (* used to index tuples *)
  | Other                       (* unknown *)
  | Impossible`                 (* value 'returned' by Raise *)

  var_name = Glob tra num | Local tra string

------

  <| source_conf : source_to_flat$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : bvl_to_bvi$config
   ; data_conf : data_to_word$config
   ; word_to_word_conf : word_to_word$config
   ; word_conf : 'a word_to_stack$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; tap_conf : tap_config

  source_to_flat$config =
           <| next : next_indices
            ; mod_env : environment
            ; pattern_cfg : flat_pattern$config

  where

  next_indices = <| vidx : num; tidx : num; eidx : num |>

  var_name = Glob tra num | Local tra string

  environment =
    <| c : (modN, conN, num # num option) namespace;
       v : (modN, varN, var_name) namespace; |>

  flat_pattern$config =
  <| pat_heuristic : (* pattern_matching$branch list *) unit -> num ;  (* problem! *)
    type_map : (num # num) list spt |>

  clos_to_bvl$config =
           <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; known_conf : clos_known$config option
            ; do_call : bool
            ; call_state : num_set # (num, num # closLang$exp) alist
            ; max_app : num
            |>

  clos_known$config =
           <| inline_max_body_size : num
            ; inline_factor : num
            ; initial_inline_factor : num
            ; val_approx_spt : val_approx spt
            |>`;

  bvl_to_bvi$config =
           <| inline_size_limit : num (* zero disables inlining *)
            ; exp_cut : num (* huge number effectively disables exp splitting *)
            ; split_main_at_seq : bool (* split main expression at Seqs *)
            ; next_name1 : num (* there should be as many of       *)
            ; next_name2 : num (* these as bvl_to_bvi_namespaces-1 *)
            ; inlines : (num # bvl$exp) spt
            |>

  data_to_word$config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *)
            ; has_div : bool (* Div available in target *)
            ; has_longdiv : bool (* LongDiv available in target *)
            ; has_fp_ops : bool (* can compile floating-point ops *)
            ; has_fp_tern : bool (* can compile FMA *)
            ; call_empty_ffi : bool (* emit (T) / omit (F) calls to FFI "" *)
            ; gc_kind : gc_kind (* GC settings *) |>

  word_to_word$config =
  <| reg_alg : num
   ; col_oracle : num -> (num num_map) option |>

  word_to_stack$config = <| bitmaps : 'a word list ;
                            stack_frame_size : num spt |>

  stack_to_lab$config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>

  lab_to_target$config =
           <| labels : num num_map num_map
            ; pos : num
            ; asm_conf : 'a asm_config
            ; init_clock : num
            ; ffi_names : string list option
            ; hash_size : num
            |>

  asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; fp_reg_count   : num  (* set to 0 if float not available *)
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>

  tap_config = Tap_Config
    (* save filename prefix *) mlstring
    (* bits which should be saved. the boolean indicates
       the presence of a '*' suffix, and matches all suffixes *)
    ((mlstring # bool) list)

*)

val _ = export_theory();
