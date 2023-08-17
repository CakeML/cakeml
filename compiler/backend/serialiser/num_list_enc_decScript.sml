(*
  Encoders and decoders to/from types represented as prefixes of lists
  of natural numbers.
*)
open preamble integerTheory miscTheory namespaceTheory ml_translatorTheory;

val _ = new_theory "num_list_enc_dec";

(* definitions of what good enc/dec functions are *)

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

(* conditional enc/dec functions *)

Definition enc_dec_ok'_def:
  enc_dec_ok' p enc dec ⇔
    dec_ok dec ∧
    ∀x (xs:num list). p x ⇒ dec (append (enc x) ++ xs) = (x,xs)
End

Theorem IMP_enc_dec_ok:
  enc_dec_ok enc dec ⇒ enc_dec_ok' (K T) enc dec
Proof
  fs [enc_dec_ok_def,enc_dec_ok'_def]
QED

Theorem enc_dec_ok'_IMP:
  enc_dec_ok' (λx. T) enc dec ⇒ enc_dec_ok enc dec
Proof
  fs [enc_dec_ok_def,enc_dec_ok'_def]
QED

Definition const_dec_def:
  const_dec a xs = (a,xs:num list)
End

Theorem enc_dec_ok'_const:
  ∀x. enc_dec_ok' ($= x) (K $ List []) (const_dec x)
Proof
  fs [enc_dec_ok'_def,dec_ok_def,const_dec_def]
QED

Theorem enc_dec_ok'_o:
  enc_dec_ok' p e d ∧ (∀x. f (g x) = x) ⇒
  enc_dec_ok' (p ∘ g) (e ∘ g) ((f ## I) ∘ d)
Proof
  fs [enc_dec_ok'_def]
QED

(* misc *)

Definition fix_res_def:
  fix_res ns (x,ns') =
    if LENGTH ns < LENGTH ns' then (x,ns) else (x,ns')
End

Theorem fix_res_IMP:
  (x,ns2) = fix_res ns1 y ⇒ LENGTH ns2 ≤ LENGTH ns1
Proof
  Cases_on ‘y’ \\ rw [fix_res_def]
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

(* word64 *)

Definition word64_enc_def:
  word64_enc (w:word64) = List [w2n w]
End

Definition word64_dec_def:
  word64_dec ns =
    case ns of
    | [] => (0w:word64,[])
    | (r::rs) => (n2w r,rs)
End

Theorem word64_enc_dec_ok:
  enc_dec_ok word64_enc word64_dec
Proof
  fs [enc_dec_ok_def,word64_dec_def,word64_enc_def]
  \\ fs [dec_ok_def,word64_dec_def]
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

Theorem list_dec_ok:
  dec_ok d ⇒
  dec_ok (list_dec d)
Proof
  fs [list_dec_def,dec_ok_def]
  \\ fs [list_dec_def] \\ strip_tac
  \\ Cases \\ fs []
  \\ Cases_on ‘list_dec' h d t’ \\ fs []
  \\ drule list_dec'_length
  \\ fs [dec_ok_def]
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
  word_dec = ((λn. n2w n) ## I) o num_dec
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

Definition safe_chr_def:
  safe_chr n = CHR (n MOD 256)
End

Definition char_dec_def:
  char_dec = (safe_chr ## I) o num_dec
End

Theorem char_enc_dec_ok:
  enc_dec_ok char_enc char_dec
Proof
  fs [char_enc_def,char_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_enc_dec_ok,CHR_ORD,ORD_BOUND,safe_chr_def]
QED

(* string *)

Definition safe_chr_list_def:
  safe_chr_list ns = MAP safe_chr ns
End

Definition take_pad_def:
  take_pad n (ns:num list) =
    if n = 0:num then ([],ns) else
      let (xs,ys) = take_pad (n-1) (TL ns) in
        case ns of
        | [] => (0::xs,ys)
        | (x::_) => (x::xs,ys)
End

Definition string_dec_def:
  string_dec ns =
    case ns of
    | [] => ("",[])
    | (n::ns) =>
        let (xs,ys) = take_pad n ns in
          (IMPLODE (safe_chr_list xs), ys)
End

Theorem string_dec_thm:
  string_dec = list_dec char_dec
Proof
  fs [FUN_EQ_THM] \\ Cases THEN1 EVAL_TAC
  \\ fs [string_dec_def,list_dec_def,safe_chr_list_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘h’
  \\ Induct THEN1 (EVAL_TAC \\ fs [])
  \\ simp [Once take_pad_def]
  \\ fs [list_dec'_def]
  \\ Cases \\ fs []
  \\ fs [char_dec_def,num_dec_def]
  \\ rpt (pairarg_tac \\ gvs [safe_chr_def])
QED

Theorem string_enc_dec_ok:
  enc_dec_ok (list_enc char_enc) string_dec
Proof
  fs [string_dec_thm]
  \\ irule list_enc_dec_ok
  \\ fs [char_enc_dec_ok]
QED

Theorem string_dec_ok:
  dec_ok string_dec
Proof
  assume_tac string_enc_dec_ok
  \\ fs [enc_dec_ok_def]
QED

(* mlstring *)

Definition mlstring_enc_def:
  mlstring_enc (strlit s) = list_enc char_enc s
End

Definition mlstring_dec_def:
  mlstring_dec = (implode ## I) o (list_dec char_dec)
End

Theorem mlstring_enc_dec_ok:
  enc_dec_ok mlstring_enc mlstring_dec
Proof
  fs [enc_dec_ok_def,mlstring_enc_def]
  \\ fs [mlstring_dec_def,PULL_FORALL]
  \\ Cases \\ fs [] \\ strip_tac
  \\ Cases_on ‘list_dec char_dec (append (mlstring_enc (strlit s)) ++ xs)’ \\ fs []
  \\ assume_tac (MATCH_MP list_enc_dec_ok char_enc_dec_ok)
  \\ fs [enc_dec_ok_def,mlstring_enc_def,mlstringTheory.implode_def]
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

Theorem prod_dec_ok:
  dec_ok d1 ∧
  dec_ok d2 ⇒
  dec_ok (prod_dec d1 d2)
Proof
  full_simp_tac std_ss [GSYM APPEND_ASSOC,prod_dec_def,LET_THM] \\ rw []
  \\ fs [dec_ok_def,prod_dec_def] \\ rw []
  \\ Cases_on ‘d1 i’ \\ fs []
  \\ Cases_on ‘d2 r’ \\ fs []
  \\ last_x_assum (qspec_then ‘i’ assume_tac)
  \\ last_x_assum (qspec_then ‘r’ assume_tac)
  \\ rfs []
QED

Theorem prod_enc_dec_ok:
  enc_dec_ok e1 d1 ∧
  enc_dec_ok e2 d2 ⇒
  enc_dec_ok (prod_enc e1 e2) (prod_dec d1 d2)
Proof
  fs [enc_dec_ok_def,prod_enc_def,FORALL_PROD,prod_dec_ok]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,prod_dec_def,LET_THM] \\ rw []
QED

Theorem prod_enc_dec_ok':
  enc_dec_ok' p1 e1 d1 ∧
  enc_dec_ok' p2 e2 d2 ⇒
  enc_dec_ok' (λx. p1 (FST x) ∧ p2 (SND x)) (prod_enc e1 e2) (prod_dec d1 d2)
Proof
  fs [enc_dec_ok'_def,prod_enc_def,FORALL_PROD]
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

Definition spt_depth_def:
  spt_depth (BN t1 t2) = MAX (spt_depth t1) (spt_depth t2) + 1 ∧
  spt_depth (BS t1 _ t2) = MAX (spt_depth t1) (spt_depth t2) + 1 ∧
  spt_depth _ = 0:num
End

Definition spt_enc''_def:
  spt_enc'' e t = prod_enc num_enc (spt_enc' e) (spt_depth t, t)
End

Definition spt_dec'_def:
  spt_dec' k d ns =
    case ns of
    | [] => (LN,ns)
    | (n::ns) =>
       if n = 0:num then (LN,ns)
       else if n = 1 then
         let (x,ns) = d ns in (LS x,ns)
       else if k = 0:num then
         (LN,ns)
       else if n = 2 then
         let (t1,ns') = spt_dec' (k-1) d ns in
         let (t2,ns') = spt_dec' (k-1) d ns' in
           (BN t1 t2,ns')
       else
         let (t1,ns1) = spt_dec' (k-1) d ns in
         let (x, ns2) = d ns1 in
         let (t2,ns3) = spt_dec' (k-1) d ns2 in
           (BS t1 x t2,ns3)
End

Definition spt_dec''_def:
  spt_dec'' d ns =
    case ns of
    | [] => (LN,ns)
    | (m::ms) => spt_dec' m d ms
End

Theorem spt_enc''_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (spt_enc'' e) (spt_dec'' d)
Proof
  fs [enc_dec_ok_def] \\ rw []
  \\ fs [spt_dec''_def,dec_ok_def,spt_enc''_def,prod_enc_def,append_thm,num_enc_def]
  THEN1
   (Cases \\ fs []
    \\ qid_spec_tac ‘t’ \\ completeInduct_on ‘h’ \\ rw []
    \\ once_rewrite_tac [spt_dec'_def]
    \\ Cases_on ‘t’ \\ fs [] \\ rw [] \\ gvs []
    THEN1
     (Cases_on ‘d t'’ \\ fs []
      \\ last_x_assum (qspec_then ‘t'’ mp_tac) \\ fs [])
    \\ first_x_assum (qspec_then ‘h-1’ assume_tac) \\ gvs []
    \\ Cases_on ‘spt_dec' (h − 1) d t'’ \\ fs []
    \\ first_assum (qspec_then ‘t'’ assume_tac) \\ fs []
    THEN1 (first_x_assum (qspec_then ‘r’ assume_tac) \\ gvs []
           \\ Cases_on ‘spt_dec' (h − 1) d r’ \\ fs [])
    \\ Cases_on ‘d r’
    \\ first_x_assum (qspec_then ‘r'’ assume_tac) \\ gvs []
    \\ Cases_on ‘spt_dec' (h − 1) d r'’ \\ fs []
    \\ last_x_assum (qspec_then ‘r’ mp_tac) \\ fs [])
  \\ qabbrev_tac ‘l = spt_depth x’
  \\ ‘spt_depth x ≤ l’ by fs [Abbr‘l’]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘l’
  \\ qid_spec_tac ‘x’
  \\ Induct
  \\ fs [spt_enc'_def,append_thm,spt_depth_def] \\ simp [Once spt_dec'_def]
  \\ rw []
  \\ ‘spt_depth x ≤ l - 1 ∧ spt_depth x' ≤ l - 1’ by fs [MAX_DEF]
  \\ res_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ fs []
QED

Definition spt_enc_def:
  spt_enc e =
    sum_enc
      (list_enc (prod_enc num_enc e)) (spt_enc'' e) o
      (λt. if wf t then INL (toAList t) else INR t)
End

Definition spt_dec_def:
  spt_dec d =
    ((λx. case x of INL xs => fromAList xs | INR t => t) ## I) o
     sum_dec (list_dec (prod_dec num_dec d)) (spt_dec'' d)
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
    \\ fs [spt_enc''_dec_ok]
    \\ match_mp_tac list_enc_dec_ok
    \\ match_mp_tac prod_enc_dec_ok
    \\ fs [num_enc_dec_ok])
  \\ rw [] \\ fs [fromAList_toAList]
QED

(* namespace -- instantiated to (string, string, 'a) *)

Definition namespace_enc'_def:
  namespace_enc' e (Bind xs ys) =
    (let ns1 = list_enc (prod_enc (list_enc char_enc) e) xs in
     let ns2 = namespace_enc'_list e ys in
       Append ns1 ns2) ∧
  namespace_enc'_list e [] = List [0] ∧
  namespace_enc'_list e ((m,x)::xs) =
    Append (Append (List [1]) (list_enc char_enc m))
      (Append (namespace_enc' e x) (namespace_enc'_list e xs))
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (_,x) => namespace_size (K 0) (K 0) (K 0) x
                           | INR (_,x) => namespace1_size (K 0) (K 0) (K 0) x)’
End

Definition namespace_depth_def:
  namespace_depth (Bind xs ys) = 1 + namespace_depth_list ys ∧
  namespace_depth_list [] = 0 ∧
  namespace_depth_list ((m,x)::xs) =
    1 + MAX (namespace_depth x) (namespace_depth_list xs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL x => namespace_size (K 0) (K 0) (K 0) x
                           | INR x => namespace1_size (K 0) (K 0) (K 0) x)’
End

Definition namespace_enc_def:
  namespace_enc e t = prod_enc num_enc (namespace_enc' e) (namespace_depth t, t)
End

Definition namespace_dec'_def:
  namespace_dec' k d ns =
    (if k = 0:num then (Bind [] [],ns) else
       let (xs,ns1) = list_dec (prod_dec (string_dec) d) ns in
       let (ys,ns2) = namespace_dec'_list (k-1) d ns1 in
         (Bind xs ys,ns2)) ∧
  namespace_dec'_list k d ns =
    case ns of
    | [] => ([],ns)
    | (n::rest) =>
      if n = 0n then ([],rest) else
      if k = 0:num then ([],ns) else
        let (m,ns) = string_dec rest in
        let (x,ns) = namespace_dec' (k-1) d ns in
        let (ys,ns) = namespace_dec'_list (k-1) d ns in
          ((m,x)::ys,ns)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (k,_,ns) => k
                           | INR (k,_,ns) => k)’ \\ fs []
End

Definition namespace_dec_def:
  namespace_dec d ns =
    case ns of
    | [] => (Bind [] [], ns)
    | (m::ms) => namespace_dec' m d ms
End

Theorem dec_ok_namespace_dec':
  ∀k. dec_ok d ⇒ dec_ok (namespace_dec' k d)
Proof
  rw [] \\ simp [dec_ok_def]
  \\ qsuff_tac ‘
    (∀k (d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec' k d i)) ≤ LENGTH i) ∧
    (∀k (d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec'_list k d i)) ≤ LENGTH i)’
  THEN1 metis_tac [] \\ pop_assum kall_tac
  \\ ho_match_mp_tac namespace_dec'_ind \\ rw []
  \\ once_rewrite_tac [namespace_dec'_def]
  \\ fs [UNCURRY] \\ rw [] \\ fs []
  THEN1
   (Cases_on ‘list_dec (prod_dec string_dec d) i’ \\ fs []
    \\ ‘dec_ok (list_dec (prod_dec string_dec d))’ by
     (irule list_dec_ok \\ irule prod_dec_ok \\ fs [string_dec_ok])
    \\ fs [dec_ok_def] \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ fs [])
  \\ Cases_on ‘i’ \\ fs []
  \\ Cases_on ‘h=0’ \\ fs []
  \\ Cases_on ‘string_dec t’ \\ fs []
  \\ Cases_on ‘k’ \\ fs []
  \\ Cases_on ‘namespace_dec' n d r’ \\ fs []
  \\ Cases_on ‘namespace_dec'_list n d r'’ \\ fs []
  \\ ‘dec_ok string_dec’ by fs [string_dec_ok]
  \\ fs [dec_ok_def]
  \\ first_x_assum (qspec_then ‘t’ mp_tac) \\ fs []
QED

Theorem namespace_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (namespace_enc e) (namespace_dec d)
Proof
  fs [enc_dec_ok_def] \\ rw []
  \\ fs [namespace_dec_def,dec_ok_def,namespace_enc_def,prod_enc_def,
         append_thm,num_enc_def]
  THEN1
   (Cases \\ fs []
    \\ qspec_then ‘h’ assume_tac dec_ok_namespace_dec'
    \\ gvs [dec_ok_def]
    \\ pop_assum (qspec_then ‘t’ assume_tac) \\ fs [])
  \\ qabbrev_tac ‘l = namespace_depth x’
  \\ ‘namespace_depth x ≤ l’ by fs [Abbr‘l’]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ qsuff_tac ‘(∀e x xs l.
        namespace_depth x ≤ l ∧ enc_dec_ok e d ⇒
        namespace_dec' l d (append (namespace_enc' e x) ++ xs) = (x,xs)) ∧
      (∀e x xs l.
        namespace_depth_list x ≤ l ∧ enc_dec_ok e d ⇒
        namespace_dec'_list l d (append (namespace_enc'_list e x) ++ xs) = (x,xs))’
  THEN1 metis_tac [enc_dec_ok_def,dec_ok_def]
  \\ rpt (pop_assum kall_tac)
  \\ ho_match_mp_tac namespace_enc'_ind \\ rw []
  \\ fs [namespace_enc'_def,append_thm,namespace_depth_def]
  \\ simp [Once namespace_dec'_def]
  THEN1
   (‘enc_dec_ok
        (list_enc (prod_enc (list_enc char_enc) e))
        (list_dec (prod_dec string_dec d))’ by
     (irule list_enc_dec_ok
      \\ irule prod_enc_dec_ok \\ fs [string_enc_dec_ok])
    \\ fs [enc_dec_ok_def] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ ‘namespace_depth_list x ≤ l - 1’ by fs []
    \\ res_tac \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ ‘enc_dec_ok (list_enc char_enc) string_dec’ by fs [string_enc_dec_ok]
  \\ fs [enc_dec_ok_def] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ gvs [] \\ rev_full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ gvs []
  \\ ‘namespace_depth x ≤ l - 1’ by fs [MAX_DEF]
  \\ ‘namespace_depth_list x' ≤ l - 1’ by fs [MAX_DEF]
  \\ res_tac \\ fs []
  \\ gvs [] \\ rev_full_simp_tac std_ss [GSYM APPEND_ASSOC] \\ gvs []
QED

(* app_rev *)

Definition append_rev_def:
  append_rev Nil res = res ∧
  append_rev (List xs) res = REV xs res ∧
  append_rev (Append l1 l2) res = append_rev l2 (append_rev l1 res)
End

Theorem append_rev_thm:
  ∀l res. append_rev l res = REVERSE (append l) ++ res
Proof
  Induct \\ fs [append_thm,append_rev_def,listTheory.REV_REVERSE_LEM]
QED

(* encoding decoding from characters *)

Overload CUT[local] = “30:num”
Overload SHIFT[local] = “32:num”

Triviality good_chars:
  ORD #" " ≤ SHIFT ∧ SHIFT + CUT + CUT ≤ ORD #"\\"
Proof
  EVAL_TAC
QED

Definition num_to_chars_def:
  num_to_chars n =
    if n < CUT then [CHR (n + SHIFT)]
    else CHR ((n MOD CUT) + SHIFT + CUT) :: num_to_chars (n DIV CUT)
End

Definition rev_nums_to_chars_def:
  rev_nums_to_chars [] res = res ∧
  rev_nums_to_chars (n::ns) res =
    rev_nums_to_chars ns (num_to_chars n ++ res)
End

Definition nums_to_chars_def:
  nums_to_chars [] = [] ∧
  nums_to_chars (n::ns) =
    if n < CUT then CHR (n + SHIFT) :: nums_to_chars ns
    else CHR ((n MOD CUT) + SHIFT + CUT) :: nums_to_chars ((n DIV CUT)::ns)
End

Definition dec_next_def:
  dec_next k l [] = (k,[]) ∧
  dec_next k l (n::ns) =
    let m = ORD n - SHIFT in
      if m < CUT then (k + l * m, ns)
      else dec_next (k + l * (m - CUT)) (l * CUT) ns
End

Triviality dec_next_LENGTH:
  ∀k ks n l t. (k,ks) = dec_next n l t ⇒ LENGTH ks ≤ LENGTH t
Proof
  Induct_on ‘t’ \\ fs [dec_next_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Definition chars_to_nums_def:
  chars_to_nums ns =
    if NULL ns then [] else
      let (k,ks) = dec_next 0 1 ns in
        k :: chars_to_nums ks
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ pop_assum mp_tac
  \\ Cases_on ‘ns’ \\ fs []
  \\ once_rewrite_tac [dec_next_def]
  \\ rw [] \\ imp_res_tac dec_next_LENGTH \\ fs []
End

Theorem dec_next_nums_to_chars:
  ∀h l ns k.
    dec_next k (CUT ** l) (nums_to_chars (h::ns)) = (k + (CUT ** l) * h, nums_to_chars ns)
Proof
  completeInduct_on ‘h’ \\ rw []
  \\ simp [Once nums_to_chars_def] \\ rw []
  \\ fs [dec_next_def,ORD_CHR]
  THEN1 (‘h + SHIFT < 256’ by fs [] \\ simp [ORD_CHR])
  \\ ‘ORD (CHR (h MOD CUT + SHIFT)) = h MOD CUT + SHIFT’ by
   (‘h MOD CUT < CUT’ by fs []
    \\ ‘h MOD CUT + SHIFT < 256’ by decide_tac
    \\ full_simp_tac std_ss [ORD_CHR])
  \\ fs []
  \\ ‘h MOD CUT < CUT’ by fs []
  \\ simp []
  \\ ‘h DIV CUT < h’ by fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘SUC l’ mp_tac) \\ fs [EXP]
  \\ disch_then kall_tac
  \\ ‘0 < CUT’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘h’ assume_tac)
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp [Once th])
QED

Theorem chars_to_nums_nums_to_chars:
  ∀ns. chars_to_nums (nums_to_chars ns) = ns
Proof
  Induct THEN1 EVAL_TAC
  \\ simp [Once chars_to_nums_def] \\ rw []
  \\ fs [dec_next_nums_to_chars |> SPEC_ALL |> Q.INST [‘l’|->‘0’] |> SIMP_RULE std_ss []]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ fs [] \\ completeInduct_on ‘h’
  \\ simp [Once nums_to_chars_def] \\ rw []
QED

Triviality nums_to_chars_APPEND:
  ∀xs ys. nums_to_chars (xs ++ ys) = nums_to_chars xs ++ nums_to_chars ys
Proof
  ho_match_mp_tac nums_to_chars_ind \\ rw []
  \\ once_rewrite_tac [nums_to_chars_def] \\ fs [] \\ rw []
QED

Theorem rev_nums_to_chars_thm:
  ∀ns res. rev_nums_to_chars ns res = nums_to_chars (REVERSE ns) ++ res
Proof
  Induct \\ fs [rev_nums_to_chars_def,nums_to_chars_def]
  \\ fs [nums_to_chars_APPEND]
  \\ ho_match_mp_tac num_to_chars_ind
  \\ rw [] \\ once_rewrite_tac [num_to_chars_def,nums_to_chars_def]
  \\ rw [] \\ EVAL_TAC
QED

val _ = export_theory();
