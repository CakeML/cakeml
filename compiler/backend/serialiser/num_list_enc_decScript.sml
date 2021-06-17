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

(* encoding decoding from characters *)

Overload CUT[local] = “30:num”
Overload SHIFT[local] = “32:num”

Triviality good_chars:
  ORD #" " ≤ SHIFT ∧ SHIFT + CUT + CUT ≤ ORD #"\\"
Proof
  EVAL_TAC
QED

Definition enc_def:
  enc [] = [] ∧
  enc (n::ns) = if n < CUT then CHR (n + SHIFT) :: enc ns
                else CHR ((n MOD CUT) + SHIFT + CUT) :: enc ((n DIV CUT)::ns)
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
    dec_next k (CUT ** l) (enc (h::ns)) = (k + (CUT ** l) * h, enc ns)
Proof
  completeInduct_on ‘h’ \\ rw []
  \\ simp [Once enc_def] \\ rw []
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

val _ = export_theory();
