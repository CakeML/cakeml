(*
  Correctness proof for word_to_stack
r
*)
open preamble semanticsPropsTheory stackSemTheory wordSemTheory
     word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory
     parmoveTheory helperLib;

val _ = new_theory "word_to_stackProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_insert",
                       "domain_inter", "domain_map", "domain_difference",
                       "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty","misc.max3_def"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = set_grammar_ancestry [
  "semanticsProps", (* for extend_with_resource_limit *)
  "stackProps", (* for extract_labels *)
  "wordProps",
  "stackSem", "wordSem", "word_to_stack"
]

val get_labels_def = stackSemTheory.get_labels_def;
val extract_labels_def = stackPropsTheory.extract_labels_def
Type state[pp] = “:(α,β,γ)wordSem$state”
Overload word_cmp[local] = “labSem$word_cmp”;
val _ = Parse.hide "B"

fun init_timer () =
let
  val timer = Lib.start_time ()
  val realtimer = Lib.start_real_time ()
  val m = Count.mk_meter()
in
  (timer,realtimer,m)
end;

fun get_time (timer,realtimer,m) =
let
  val () = Lib.end_time timer
  val () = Lib.end_real_time realtimer
  val () = Count.report (Count.read m)
in
  ()
end;

val timer = init_timer ();
val _ = get_time timer;
val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``

val s = ``s:('a,num # 'c,'ffi) wordSem$state``
val t = ``t:('a,'c,'ffi) stackSem$state``
(* TODO: Move to stackProps*)
Theorem set_var_with_memory:
   stackSem$set_var a b c with memory := m = set_var a b (c with memory := m)
Proof
  EVAL_TAC
QED

Theorem set_var_swap:
   a ≠ a' ⇒ stackSem$set_var a b (set_var a' b' c) = set_var a' b' (set_var a b c)
Proof
  EVAL_TAC \\ simp[stackSemTheory.state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE]
  \\ rw[] \\ rw[]
QED

Theorem set_var_swap_word:
   a ≠ a' ⇒ wordSem$set_var a b (set_var a' b' c) = set_var a' b' (set_var a b c)
Proof
  EVAL_TAC \\ simp[wordSemTheory.state_component_equality,insert_swap]
  \\ rw[] \\ rw[]
QED

Theorem set_var_cancel:
   stackSem$set_var a b (set_var a b' t) = set_var a b t
Proof
  EVAL_TAC \\ simp[stackSemTheory.state_component_equality]
QED

Theorem set_var_cancel_word:
   wordSem$set_var a b (set_var a b' s) = set_var a b s
Proof
  EVAL_TAC \\ simp[wordSemTheory.state_component_equality,insert_shadow]
QED

Theorem get_var_set_var[simp]:
    stackSem$get_var k (set_var k v st) = SOME v
Proof
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def]>>
  fs[FLOOKUP_UPDATE]
QED

Theorem state_with_const[simp]:
    (t with clock := t.clock) = ^t
Proof
  fs [stackSemTheory.state_component_equality]
QED

Theorem set_store_set_var:
   stackSem$set_store a b (set_var c d e) = set_var c d (set_store a b e)
Proof
  EVAL_TAC
QED

(* Move to stackProps END*)

(* TODO delete*)
Theorem DROP_DROP_EQ:
   !n m xs. DROP m (DROP n xs) = DROP (m + n) xs
Proof
   MATCH_ACCEPT_TAC DROP_DROP_T
QED

Triviality TAKE_TAKE_MIN:
  !xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs
Proof
  simp[Once MIN_COMM] >>
  MATCH_ACCEPT_TAC TAKE_TAKE_MIN
QED

Triviality TAKE_DROP_EQ:
  !xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)
Proof
  pure_rewrite_tac[Once ADD_COMM] >>
  MATCH_ACCEPT_TAC TAKE_DROP_SWAP
QED

Triviality DROP_TAKE_NIL:
  DROP n (TAKE n xs) = []
Proof
  MATCH_ACCEPT_TAC DROP_TAKE_EQ_NIL
QED

(* delete END *)
(* list_max stuff the whole compiler should be done in terms of MAX_LIST
and some should be deleted, some can be generalized and the rest can be moved up.
 some should be generalized and moved up*)

Theorem list_max_APPEND:
    ∀a b.
  list_max (a++b) = MAX (list_max a) (list_max b)
Proof
  Induct>>fs[list_max_def,LET_THM,MAX_DEF]>>rw[]>>
  DECIDE_TAC
QED

Theorem list_max_SNOC:
    list_max (SNOC x ls) = MAX x (list_max ls)
Proof
  fs[SNOC_APPEND,list_max_APPEND,list_max_def,LET_THM,MAX_DEF]>>
  DECIDE_TAC
QED

Theorem list_max_GENLIST_evens:
    ∀n. list_max (GENLIST (λx. 2*x) n) = 2*(n-1)
Proof
  Induct>>
  fs[list_max_def]>>rw[]>>
  fs[GENLIST,list_max_SNOC,MAX_DEF]>>
  DECIDE_TAC
QED

Theorem list_max_GENLIST_evens2:
    ∀n. list_max (GENLIST (λx. 2*(x+1)) n) = 2*n
Proof
  Induct>>
  fs[list_max_def]>>rw[]>>
  fs[GENLIST,list_max_SNOC,MAX_DEF]>>
  DECIDE_TAC
QED
(*list_max end*)

(*misc word stuff*)

Triviality word_or_eq_0:
  ((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ metis_tac []
QED

Triviality shift_shift_lemma:
  ~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + 1 < dimindex (:α)`
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac
  \\ simp []
QED

Theorem word_shift_or_1:
  (n ≪ 1) ‖ 1w = (n ≪ 1) + 1w
Proof
  `?x. n = bitstring$v2w x`
    by METIS_TAC[ bitstringTheory.v2w_w2v]
  >> `1w = bitstring$v2w [T]`
   by fs[GSYM bitstringTheory.n2w_v2n,bitstringTheory.v2n]
  >> fs[bitstringTheory.word_lsl_v2w,bitstringTheory.word_or_v2w]
  >> fs[bitstringTheory.shiftl_def,listTheory.PAD_RIGHT]
  >> fs[bitstringTheory.bor_def,bitstringTheory.bitwise_def,MAX_DEF]
  >> fs[bitstringTheory.fixwidth_def]
  >> reverse $ rw[]
  >- fs[GSYM bitstringTheory.n2w_v2n,bitstringTheory.v2n]
  >> fs[bitstringTheory.zero_extend_def,listTheory.PAD_LEFT]
  >> pop_assum kall_tac >> Induct_on `x`
  >> fs[GSYM bitstringTheory.n2w_v2n,bitstringTheory.v2n,
     rich_listTheory.GENLIST_K_CONS]
  >> fs[COND_RAND,COND_RATOR]
  >> fs[GSYM wordsTheory.word_add_n2w]
QED
(*misc word_stuff end*)
(*TODO figure a normal form
Should set_store be pushed out always?*)
Triviality push_env_set_store:
  push_env env ^nn (set_store AllocSize (Word c) s) =
    set_store AllocSize (Word c) (push_env env ^nn s)
Proof
  fs [push_env_def,set_store_def,env_to_list_def,LET_DEF]
QED

(*Some of this use look like garbage need to figure out and
remove usage of garbage*)
Triviality LASTN_LENGTH_ID2:
  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack
Proof
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID]
QED

Triviality LASTN_MORE:
  ∀ls n.
  ¬(n < LENGTH ls) ⇒ LASTN n ls = ls
Proof
  fs[LASTN_LENGTH_LESS_EQ]
QED

(*Equality theorems available if n ≤ LENGTH ls*)
Triviality LASTN_LENGTH_BOUNDS:
  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls
Proof
  fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]>>rw[]>>
  decide_tac
QED

Triviality LASTN_CONS_ID:
  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)
Proof
  rw[]>>EVAL_TAC>>fs[]
QED

(*Strengthened version of LASTN_DROP after change to make it total*)
Triviality LASTN_DROP2:
  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l
Proof
  Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]>>
  Cases_on`n > LENGTH l`>>fs[ADD1]>>
  `LENGTH l - n = 0` by fs[]>>
  simp[DROP_def]
QED

Triviality EVERY_IMP_EVERY_LASTN:
  !xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys
Proof
  fs [EVERY_MEM] \\ rw [] \\ imp_res_tac MEM_LASTN \\ res_tac \\ fs []
QED

Triviality LASTN_HD:
  ∀ls x.
  x ≤ LENGTH ls ⇒
  HD (LASTN x ls) =
  EL (LENGTH ls - x) ls
Proof
  fs[LASTN_def]>>
  Induct>>rw[]>>
  Cases_on`x = SUC(LENGTH ls)`
  >-
    simp[TAKE_APPEND2,REVERSE_APPEND]
  >>
    `x ≤ LENGTH ls` by DECIDE_TAC>>fs[TAKE_APPEND1]>>
    `SUC (LENGTH ls) -x = SUC(LENGTH ls - x)` by DECIDE_TAC>>
    simp[]
QED

Theorem LLOOKUP_TAKE:
  n < f ==>
  LLOOKUP (TAKE f xs) (n) = LLOOKUP xs (n) 
Proof
  fs[LLOOKUP_THM,LENGTH_TAKE_EQ_MIN] >>
  rw[] >>DEP_REWRITE_TAC[EL_TAKE] >> simp[]
QED
(* TODO: many things in this file need moving *)

val the_eqn = backendPropsTheory.the_eqn

Definition index_list_def:
  (index_list [] n = []) /\
  (index_list (x::xs) n = (n + LENGTH xs,x) :: index_list xs n)
End

val drule = old_drule
Theorem LENGTH_index_list:
   !l n. LENGTH (index_list l n) = LENGTH l
Proof
  Induct \\ fs [index_list_def]
QED

Theorem EL_index_list:
   !xs i. i < LENGTH xs ==>
          (EL i (index_list xs k) = (k + LENGTH xs - i - 1, EL i xs))
Proof
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac
QED

Theorem EL_index_list2:
   ∀xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = (k + LENGTH xs - (i+1), EL i xs))
Proof
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac
QED

Theorem MAP_SND_index_list:
   !xs k. MAP SND (index_list xs k) = xs
Proof
  Induct \\ fs [index_list_def]
QED

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)
Theorem MAP_FST_index_list:
   ∀xs k. MAP FST (index_list xs k) = REVERSE (MAP ($+ k) (COUNT_LIST (LENGTH xs)))
Proof
  Induct \\ simp[index_list_def,COUNT_LIST_def,MAP_MAP_o]
  \\ simp[LIST_EQ_REWRITE] \\ rw[]
  \\ Cases_on`x < LENGTH xs`
  >- (
    simp[EL_APPEND1,LENGTH_COUNT_LIST]
    \\ simp[EL_REVERSE,LENGTH_COUNT_LIST]
    \\ simp[EL_MAP,LENGTH_COUNT_LIST]
    \\ simp[EL_COUNT_LIST]
    \\ Cases_on`x` \\ simp[]
    \\ simp[EL_REVERSE,LENGTH_COUNT_LIST]
    \\ simp[EL_MAP,LENGTH_COUNT_LIST]
    \\ simp[EL_COUNT_LIST]
    \\ simp[PRE_SUB1] )
  \\ fs[LENGTH_COUNT_LIST]
  \\ simp[EL_APPEND2,LENGTH_COUNT_LIST]
  \\ `x = LENGTH xs` by decide_tac
  \\ Cases_on`LENGTH xs`
  \\ simp[]
  \\ simp[EL_REVERSE,LENGTH_COUNT_LIST]
  \\ simp[COUNT_LIST_def]
QED

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)
Theorem index_list_eq_ZIP:
   index_list xs k = ZIP(REVERSE(MAP($+ k)(COUNT_LIST (LENGTH xs))),xs)
Proof
  metis_tac[MAP_FST_index_list,MAP_SND_index_list,ZIP_MAP_FST_SND_EQ]
QED

(*MEM to an EL characterization for index lists*)
Triviality MEM_index_list_LIM:
  ∀ls n v k.
  MEM (n,v) (index_list ls k) ⇒
  n-k < LENGTH ls
Proof
  Induct>>fs[index_list_def]>>rw[]
  >-
    DECIDE_TAC
  >>
  res_tac>>
  DECIDE_TAC
QED

Triviality MEM_index_list_EL:
  ∀ls n v.
  MEM (n,v) (index_list ls k) ⇒
  EL (LENGTH ls - (n-k+1)) ls = v
Proof
  Induct>>fs[index_list_def,FORALL_PROD]>>rw[]>>
  simp[ADD1]>>
  res_tac>>
  fs[]>>
  imp_res_tac MEM_index_list_LIM>>
  `LENGTH ls +1 - (n-k+1) = SUC(LENGTH ls - (n-k+1))` by DECIDE_TAC>>
  pop_assum SUBST_ALL_TAC>>
  simp[]
QED

Theorem ALOOKUP_index_list:
  ∀ls n.
  n < LENGTH ls + k ⇒
  ALOOKUP (index_list ls k) n =
  LLOOKUP ls ((LENGTH ls + k) - (n+1))
Proof
  Induct>>rw[index_list_def,LLOOKUP_def]>>
  gvs[ADD1]
QED

Theorem IMP_filter_bitmap_EQ_SOME_NIL:
   !xs ys zs.
     (LENGTH xs = LENGTH ys) /\
     zs = MAP FST (FILTER SND (ZIP (ys, xs))) ==>
     (filter_bitmap xs ys = SOME (zs,[]))
Proof
  Induct \\ Cases_on `ys` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def]
QED

Theorem filter_bitmap_length:
   ∀bs ls xs ys.
  filter_bitmap bs ls = SOME(xs,ys) ⇒
  LENGTH xs ≤ LENGTH bs
Proof
  ho_match_mp_tac filter_bitmap_ind>>fs[filter_bitmap_def]>>rw[]>>
  EVERY_CASE_TAC>>rveq>>fs[]>>res_tac>>
  rveq>>fs[]>>DECIDE_TAC
QED

Theorem filter_bitmap_length_input:
   ∀xs ys ls. filter_bitmap xs ys = SOME ls ⇒ LENGTH xs ≤ LENGTH ys
Proof
  ho_match_mp_tac filter_bitmap_ind
  \\ simp[filter_bitmap_def,LENGTH_NIL_SYM]
  \\ rw[]
  \\ every_case_tac \\ fs[]
QED

Theorem filter_bitmap_MAP_IMP:
   ∀ys xs l.
    filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[]) ∧
    filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])
    ⇒
    filter_bitmap ys xs = SOME (l,[])
Proof
  Induct \\ Cases_on`xs` \\ fs[filter_bitmap_def]
  \\ Cases \\ fs[filter_bitmap_def] \\ rpt strip_tac
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ Cases_on`l` \\ fs[]
  \\ rveq
  \\ first_x_assum drule
  \\ impl_tac >- metis_tac[]
  \\ simp[]
  \\ rw[]
  \\ metis_tac[PAIR]
QED

Theorem filter_bitmap_IMP_MAP_SND:
   !ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])
Proof
  Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem filter_bitmap_IMP_MAP_FST:
   !ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])
Proof
  Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem filter_bitmap_TAKE_LENGTH_IMP:
   !h5 x4 l.
     filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[]) ==>
     filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)
Proof
  Induct \\ Cases_on `x4` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ Cases_on `l` \\ fs [] \\ rw [] \\ res_tac \\ fs []
QED

Theorem filter_bitmap_lemma:
   filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[]) ==>
   filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4)
Proof
  rpt strip_tac \\ imp_res_tac filter_bitmap_IMP_MAP_SND
  \\ fs [MAP_SND_index_list] \\ imp_res_tac filter_bitmap_TAKE_LENGTH_IMP
QED

Theorem filter_bitmap_MEM:
   ∀b ls ls' x.
  filter_bitmap b ls = SOME (ls',[]) ∧
  MEM x ls' ⇒ MEM x ls
Proof
  ho_match_mp_tac filter_bitmap_ind>>
  rw[filter_bitmap_def]>>
  EVERY_CASE_TAC>>fs[]>>rveq>>
  fs[MEM]
QED

Theorem TAKE_LUPDATE[simp]:
   !xs n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)
Proof
  Induct \\ fs [LUPDATE_def] \\ Cases_on `i` \\ fs [LUPDATE_def] \\ rw [LUPDATE_def]
  >-
    (Cases_on`n`>>fs[LUPDATE_def])
  >>
    Cases_on`n'`>>fs[LUPDATE_def]
QED

local
  val DROP_LUPDATE_lemma1 = Q.prove(
    `!xs n m h. n <= m ==>
                 DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs)`,
    MATCH_ACCEPT_TAC DROP_LUPDATE)
  val DROP_LUPDATE_lemma2 = Q.prove(
    `!xs n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs`,
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def])
in
  Theorem DROP_LUPDATE:
     !n h m xs.
        DROP n (LUPDATE h m xs) =
        if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs)
Proof
    rw [DROP_LUPDATE_lemma2]
    \\ match_mp_tac DROP_LUPDATE_lemma1
    \\ fs [NOT_LESS]
QED
end

Triviality MIN_ADD:
  MIN m1 m2 + n = MIN (m1 + n) (m2 + n)
Proof
  fs [MIN_DEF] \\ decide_tac
QED

Definition list_LUPDATE_def:
  (list_LUPDATE [] n ys = ys) /\
  (list_LUPDATE (x::xs) n ys = list_LUPDATE xs (n+1) (LUPDATE x n ys))
End

Theorem LENGTH_list_LUPDATE[simp]:
   !xs n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys
Proof
  Induct \\ fs [list_LUPDATE_def]
QED

Theorem TAKE_list_LUPDATE[simp]:
   !ys xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs)
Proof
  Induct \\ fs [list_LUPDATE_def]
QED

Triviality LLOOKUP_list_LUPDATE_IGNORE:
  !xs i n ys.
      i + LENGTH xs <= n ==>
      LLOOKUP (list_LUPDATE xs i ys) n = LLOOKUP ys n
Proof
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `(i+1) + LENGTH xs <= n` by decide_tac \\ res_tac
  \\ `i <> n` by decide_tac \\ fs [LLOOKUP_LUPDATE]
QED

Triviality DROP_list_LUPDATE:
  !ys n m xs.
      n <= m ==>
      DROP n (list_LUPDATE ys m xs) =
      list_LUPDATE ys (m - n) (DROP n xs)
Proof
  Induct
  \\ fs [list_LUPDATE_def,LENGTH_NIL,PULL_FORALL]
  \\ rpt strip_tac \\ `n <= m + 1` by decide_tac
  \\ rw [] \\ `m + 1 - n = m - n + 1 /\ ~(m < n)` by decide_tac
  \\ fs [DROP_LUPDATE]
QED

Triviality DROP_list_LUPDATE_IGNORE:
  !xs i ys n.
      LENGTH xs + i <= n ==>
      DROP n (list_LUPDATE xs i ys) = DROP n ys
Proof
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `LENGTH xs + (i+1) <= n /\ i < n` by decide_tac
  \\ fs [DROP_LUPDATE]
QED

Theorem list_LUPDATE_NIL[simp]:
   !xs i. list_LUPDATE xs i [] = []
Proof
  Induct \\ fs [list_LUPDATE_def,LUPDATE_def]
QED

Triviality LUPDATE_TAKE_LEMMA:
  !xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)
Proof
  Induct \\ Cases_on `n` \\ fs [LUPDATE_def]
QED

Theorem list_LUPDATE_TAKE_DROP:
   !xs (ys:'a list) n.
       list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP n ys)
Proof
  Induct \\ simp_tac std_ss [Once list_LUPDATE_def]
  \\ once_rewrite_tac [list_LUPDATE_def] THEN1 fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [DROP_LUPDATE,DROP_DROP_EQ,AC ADD_COMM ADD_ASSOC]
  \\ simp_tac std_ss [Once LUPDATE_TAKE_LEMMA,TAKE_TAKE_MIN] \\ rpt strip_tac
  \\ `MIN (n + 1) n = n`  by (fs [MIN_DEF] \\ decide_tac) \\ fs []
  \\ AP_TERM_TAC \\ fs [TAKE_DROP_EQ,AC ADD_COMM ADD_ASSOC]
QED

Theorem list_LUPDATE_0_CONS[simp]:
   !xs x ys y. list_LUPDATE (x::xs) 0 (y::ys) = x :: list_LUPDATE xs 0 ys
Proof
  fs [list_LUPDATE_def,LUPDATE_def]
  \\ simp_tac std_ss [Once list_LUPDATE_TAKE_DROP] \\ fs []
QED

Theorem list_LUPDATE_APPEND:
   !xs ys zs.
      LENGTH xs = LENGTH ys ==> (list_LUPDATE xs 0 (ys ++ zs) = xs ++ zs)
Proof
  Induct \\ Cases_on `ys` \\ fs [list_LUPDATE_def]
QED

(* move to stackProps? *)

Triviality DIV_ADD_1:
  0 < d ==> (m DIV d + 1 = (m + d) DIV d)
Proof
  rpt strip_tac
  \\ ASSUME_TAC (ADD_DIV_ADD_DIV |> Q.SPECL [`d`] |> UNDISCH
      |> Q.SPECL [`1`,`m`] |> ONCE_REWRITE_RULE [ADD_COMM]) \\ fs []
QED

Triviality LENGTH_word_list_lemma:
  !xs d. 0 < d ==> (LENGTH (word_list xs d) = (LENGTH xs - 1) DIV d + 1)
Proof
  recInduct word_list_ind
  \\ rpt strip_tac \\ fsrw_tac[] []
  \\ once_rewrite_tac [word_list_def] \\ fsrw_tac[] [] \\ rw []
  \\ imp_res_tac ZERO_DIV \\ fsrw_tac[] [] \\ res_tac
  \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fsrw_tac[] []
  \\ fsrw_tac[] [ADD1] \\ fsrw_tac[] [NOT_LESS]
  \\ imp_res_tac (ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_EXISTS)
  THEN1 (`LENGTH xs - 1 < d` by decide_tac
         \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fsrw_tac[] [])
  \\ imp_res_tac DIV_ADD_1 \\ fsrw_tac[] []
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac
QED

Theorem LENGTH_word_list:
   !xs d. LENGTH (word_list xs d) =
           if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1
Proof
  rw [] THEN1 (once_rewrite_tac [word_list_def] \\ fs [])
  \\ match_mp_tac LENGTH_word_list_lemma \\ decide_tac
QED

(* move to wordProps? *)

Triviality list_rearrange_I:
  (list_rearrange I = I)
Proof
  fs [list_rearrange_def,FUN_EQ_THM]
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF,GENLIST_ID]
QED

(* state relation *)

(*Abstracts a stackLang stack w.r.t. wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel
  TODO: The length checks may be inconvenient for handler frames
*)
Definition abs_stack_def:
  (abs_stack (bitmaps:'a word list) [] stack [] =
    if stack = [Word (0w:'a word)] then SOME [] else NONE) ∧
  (abs_stack bitmaps ((StackFrame n l0 l NONE)::xs) (w::stack) (len::lens) =
    (*Should cover the stack = [] case automatically*)
    case full_read_bitmap bitmaps w of
    | NONE => NONE
    (*read_bitmap reads a bitmap and returns the liveness bits,
      the words read and the rest of the stack*)
    | SOME bits =>
        if LENGTH bits ≠ len then NONE else
        if LENGTH stack < len then NONE else
(*        if the (len + 1) n ≠ len + 1 then NONE else*)
          let frame = TAKE len stack in
          let rest = DROP len stack in
            case abs_stack bitmaps xs rest lens of
            | NONE => NONE
            | SOME ys => SOME ((NONE,bits,frame)::ys)) ∧
  (abs_stack bitmaps ((StackFrame n l0 l (SOME _))::xs) (w::stack) (len::lens) =
    (*Index for bitmap for a handler frame*)
    if w ≠ Word 1w then NONE
    else
      (case stack of
      (*Read next 2 elements on the stack for the handler*)
      | loc::hv::w::stack =>
         (case full_read_bitmap bitmaps w of
          | NONE => NONE
          (*read_bitmap reads a bitmap and returns the liveness bits,
            the words read and the rest of the stack*)
          | SOME bits =>
              if LENGTH bits ≠ len then NONE else
              if LENGTH stack < len then NONE else
(*              if the (len + 1) n ≠ len + 1 then NONE else*)
                let frame = TAKE len stack in
                let rest = DROP len stack in
                  case abs_stack bitmaps xs rest lens of
                  | NONE => NONE
                  | SOME ys => SOME ((SOME(loc,hv),bits,frame)::ys))
      | _ => NONE)) ∧
  (abs_stack bitmaps _ _ _ = NONE)
End

val abs_stack_ind = theorem"abs_stack_ind";

Theorem read_bitmap_append_extra:
   ∀l1 l2 bits.
   read_bitmap l1 = SOME bits ⇒
   read_bitmap (l1 ++ l2) = SOME bits
Proof
  Induct >> simp[read_bitmap_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC >> simp[]
  \\ BasicProvers.CASE_TAC >> simp[]
  \\ fs[] \\ rfs[]
QED

Theorem full_read_bitmap_append:
   ∀bitmaps w bits more_bitmaps.
   full_read_bitmap bitmaps w = SOME bits ⇒
   full_read_bitmap (bitmaps ++ more_bitmaps) w = SOME bits
Proof
  recInduct full_read_bitmap_ind
  \\ rw[full_read_bitmap_def]
  \\ rw[DROP_APPEND]
  \\ metis_tac[read_bitmap_append_extra]
QED

Theorem abs_stack_bitmaps_prefix:
   ∀bitmaps frames stack lens more_bitmaps result.
   abs_stack bitmaps frames stack lens = SOME result ⇒
   abs_stack (bitmaps ++ more_bitmaps) frames stack lens = SOME result
Proof
  recInduct abs_stack_ind
  \\ rw[abs_stack_def]
  \\ fs[case_eq_thms]
  \\ rveq
  \\ imp_res_tac full_read_bitmap_append
  \\ simp[]
QED

(*TODO this should probably be an Overload*)
Definition MAP_FST_def:
  MAP_FST f xs = MAP (\(x,y). (f x, y)) xs
End

Triviality MAP_SND_MAP_FST:
  !xs f. MAP SND (MAP_FST f xs) = MAP SND xs
Proof
  Induct \\ fs [MAP,MAP_FST_def,FORALL_PROD]
QED

Definition adjust_names_def:
  adjust_names n = n DIV 2
End

(*handler_val counts the total number of words in the list of frames*)
Definition handler_val_def:
  (handler_val [] = 1n) ∧
  (handler_val ((NONE,_,frame)::stack) =
    1+LENGTH frame+handler_val stack) ∧
  (handler_val ((SOME _,_,frame)::stack) =
    (*  1 for handler bitmaps pointer
      + 2 more for the pointer and locs
      + 1 for the next bitmap pointer
    *)
    4+LENGTH frame+handler_val stack)
End

(*TODO: Maybe switch to this alternative index_list that goes from
stackLang vars to wordLang vars more directly*)
(*
Definition index_list_def:
  (index_list [] k = []) /\
  (index_list (x::xs) k = (2*(k+LENGTH xs),x) :: index_list xs k)
End
*)

Definition is_handler_frame_def:
  (is_handler_frame (StackFrame n l0 l NONE) = F) ∧
  (is_handler_frame _ = T)
End

(*Checks for consistency of the values*)
Definition stack_rel_aux_def:
  (stack_rel_aux k len [] [] ⇔ T) ∧
  (stack_rel_aux k len ((StackFrame n l0 l NONE)::xs) ((NONE,bits,frame)::stack) ⇔
    (∀n v.
      ALOOKUP l0 n = SOME v ∧ ALOOKUP l n = NONE ⇒
      ALOOKUP (index_list frame k) (n DIV 2) = SOME v) ∧
    filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
    the (LENGTH frame + 1) n = LENGTH frame + 1 ∧
    stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len ((StackFrame n l0 l (SOME (h1,l1,l2)))::xs) ((SOME(loc,hv),bits,frame)::stack) ⇔
      (h1 < LENGTH stack ∧
      is_handler_frame (EL (LENGTH stack - (h1+1)) xs) ⇒
      hv = Word (n2w (len - handler_val (LASTN (h1+1) stack)))) ∧
      loc = Loc l1 l2 ∧
      (∀n v.
        ALOOKUP l0 n = SOME v ∧ ALOOKUP l n = NONE ⇒
        ALOOKUP (index_list frame k) (n DIV 2) = SOME v) ∧
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
      the (LENGTH frame + 1) n = LENGTH frame + 1 ∧
      stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len _ _ = F)
End

Definition sorted_env_def:
  sorted_env (StackFrame n l0 l _) = SORTED (\x y. FST x > FST y) l
End

Definition stack_rel_def:
  stack_rel k s_handler s_stack t_handler t_rest_of_stack t_stack_length t_bitmaps lens <=>
    EVERY sorted_env s_stack /\
    ∃stack.
      abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack ∧
      (s_handler < LENGTH s_stack ∧
      is_handler_frame (EL (LENGTH s_stack - (s_handler+1)) s_stack)
      ⇒
      t_handler = SOME(Word (n2w (t_stack_length - handler_val (LASTN (s_handler+1) stack))))) ∧
      stack_rel_aux k t_stack_length s_stack stack
End

(*f is the size of the current frame + 1 most of the time
  (extra word for the bitmap pointer)
  f' is the size of the current frame
  lens tracks the size of each remaining stack frame on the stackLang stack
*)

(* Stack size as predicted by the wordLang state is a conservative estimate of the
   actual stack usage. *)
Definition stack_size_rel_def:
  stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack
    t_stack t_stack_space (extra : num) ⇔
    (f ≠ 0 ==> the f s_locals_size = f) ∧
    s_stack_limit = LENGTH t_stack ∧
    ∀sm. s_stack_max = SOME sm ⇒
      LENGTH t_stack - t_stack_space - f - extra ≤ sm ∧
      IS_SOME s_locals_size ∧
      (?ss. stack_size s_stack = SOME ss ∧
        ss = LENGTH t_stack - t_stack_space - f - extra)
End

Definition state_rel_def:
  state_rel ac k f f' (s:('a,num # 'c,'ffi) wordSem$state)
    (t:('a,'c,'ffi) stackSem$state) lens extra ⇔
    (s.clock = t.clock) /\ (s.gc_fun = t.gc_fun) /\ (s.permute = K I) /\
    (t.ffi = s.ffi) /\ t.use_stack /\ t.use_store /\ t.use_alloc /\
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\ 4 < k /\
    (t.sh_mdomain = s.sh_mdomain) /\
    (s.store = t.store \\ Handler) /\ gc_fun_ok t.gc_fun /\ s.termdep = 0 /\
    t.be = s.be /\ t.ffi = s.ffi /\ Handler ∈ FDOM t.store ∧
    t.fp_regs = s.fp_regs ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    s.compile = (λ(bm0,cfg) progs.
      let (progs,fs,bm) = word_to_stack$compile_word_to_stack ac k progs (Nil, bm0) in
      OPTION_MAP (λ(bytes,cfg). (bytes,append (FST bm),(SND bm,cfg)))
        (t.compile cfg progs)) ∧
    t.compile_oracle = (λn.
      let ((bm0,cfg),progs) = s.compile_oracle n in
      let (progs,fs,bm) = word_to_stack$compile_word_to_stack ac k progs (Nil, bm0) in
        (cfg,progs,append (FST bm))) ∧
    (∀n. let ((bm0,cfg),progs) = s.compile_oracle n in
        EVERY (post_alloc_conventions k o SND o SND) progs ∧
        EVERY (flat_exp_conventions o SND o SND) progs ∧
        EVERY ((<>) raise_stub_location o FST) progs ∧
        EVERY ((<>) store_consts_stub_location o FST) progs ∧
        (n = 0 ⇒ bm0 = LENGTH t.bitmaps)) ∧
    domain t.code = raise_stub_location INSERT
                      store_consts_stub_location INSERT domain s.code ∧
    (!n word_prog arg_count.
       (lookup n s.code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       ?bs i bs2 i2 f stack_prog.
         word_to_stack$compile_prog ac word_prog arg_count k (bs,i) = (stack_prog,f,(bs2,i2)) /\
         LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH t.bitmaps /\
         isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) t.bitmaps) /\
         (lookup n t.code = SOME stack_prog) /\
         the f (lookup n s.stack_size) = f
    ) /\
    (lookup raise_stub_location t.code = SOME (raise_stub k)) /\
    (lookup store_consts_stub_location t.code = SOME (store_consts_stub k)) /\
    good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    LENGTH t.bitmaps + LENGTH s.data_buffer.buffer + s.data_buffer.space_left +1 < dimword (:α) /\
    1 ≤ LENGTH t.bitmaps ∧ HD t.bitmaps = 4w ∧
    t.stack_space + f <= LENGTH t.stack /\ LENGTH t.stack < dimword (:'a) /\
    (if f' = 0 then f = 0 else (f = f' + 1)) /\
    wf s.locals /\
    stack_size_rel f s.locals_size s.stack_limit s.stack_max s.stack
      t.stack t.stack_space (extra : num) ∧
    let stack = DROP (t.stack_space + extra) t.stack in
    (*First f things on stack are the live stack vars*)
    let current_frame = TAKE f stack in
    let rest_of_stack = DROP f stack in
      stack_rel k s.handler s.stack (FLOOKUP t.store Handler)
        rest_of_stack (LENGTH t.stack) t.bitmaps lens /\
      (!n v.
        (lookup n s.locals = SOME v) ==>
        EVEN n /\
        if n DIV 2 < k then (FLOOKUP t.regs (n DIV 2) = SOME v)
        else (LLOOKUP current_frame (f-1 -(n DIV 2 - k)) = SOME v) /\
             n DIV 2 < k + f')
End

(* correctness proof *)

Triviality evaluate_SeqStackFree:
  t.use_stack /\ t.stack_space <= LENGTH t.stack ==>
    evaluate (SeqStackFree f p,t) =
    evaluate (Seq (StackFree f) p,t)
Proof
   simp[SeqStackFree_def] >>
   simp[COND_RAND,COND_RATOR] >>
   simp[stackSemTheory.evaluate_def] >>
   (*TODO state as default simp*)
   `t with stack_space := t.stack_space = t`
     by simp[stackSemTheory.state_component_equality] >>
   simp[]
QED

val convs_def = LIST_CONJ
  [wordConvsTheory.post_alloc_conventions_def,
   wordConvsTheory.call_arg_convention_def,
   wordConvsTheory.flat_exp_conventions_def,
   wordLangTheory.every_var_def,
   wordLangTheory.every_var_imm_def,
   wordLangTheory.every_stack_var_def,
   wordLangTheory.every_name_def]

val _ = get_time timer;
(*
Triviality LENGTH_write_bitmap:
  state_rel ac k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap (names:num_set) k f'):'a word list) + f' = f)
Proof
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac
QED
*)

Triviality DROP_list_LUPDATE_lemma =
  MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL) |> SIMP_RULE std_ss []

Triviality bits_to_word_bit:
  !bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)
Proof
  Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1] \\ rpt strip_tac
  \\ first_x_assum match_mp_tac \\ fs [] \\ decide_tac
QED

Triviality bits_to_word_miss:
  !bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)
Proof
  Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]
QED

Triviality bits_to_word_SNOC:
 !bs b.
  bits_to_word (SNOC b bs) =
 (if b then 1w else 0w) ≪ (LENGTH bs) ‖ (bits_to_word bs)
Proof
  Induct
  >> simp[Once $ oneline bits_to_word_def, bits_to_word_def]
  >> qpat_abbrev_tac `bits_to_word_bs = bits_to_word bs`
  >> simp[Once $ oneline bits_to_word_def, bits_to_word_def]
  >> rw[] >> simp[ADD1]
QED

Triviality list_LUPDATE_write_bitmap_NOT_NIL:
  8 <= dimindex (:'a) ==>
    (list_LUPDATE (MAP Word (write_bitmap names k f')) 0 xs <>
     [Word (0w:'a word)])
Proof
  Cases_on `xs` >- fs [list_LUPDATE_NIL]
  \\ full_simp_tac(srw_ss()) [write_bitmap_def,LET_DEF,Once word_list_def]
  \\ strip_tac \\ `~(dimindex (:'a) <= 1)` by decide_tac \\ fs []
  \\ IF_CASES_TAC \\ simp[list_LUPDATE_def] 
  \\ simp[GSYM SNOC_APPEND,bits_to_word_SNOC,Excl "LIST_EQ_SIMP_CONV"]
  \\ simp[word_or_eq_0,EXP_EQ_0]
  \\ simp[word_1_lsl] \\simp[dimword_def]
QED


Triviality bit_length_bits_to_word:
  !qs.
      LENGTH qs + 1 < dimindex (:'a) ==>
      bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs + 1
Proof
  Induct THEN1
   (fs [] \\ fs [Once bit_length_def] \\ fs [Once bit_length_def]
    \\ fs [bits_to_word_def] \\ EVAL_TAC)
  \\ Cases \\ fs [bits_to_word_def]
  \\ once_rewrite_tac [bit_length_def]
  \\ fs [ADD_CLAUSES]
  \\ rpt strip_tac \\ fs [EVAL ``1w >>> 1``]
  \\ `(LENGTH qs + 1) < dimindex (:'a)` by decide_tac \\ fs []
  \\ `bits_to_word (qs ++ [T]) << 1 <> 0w` by
   (fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_0,word_lsl_def]
    \\ Q.EXISTS_TAC `LENGTH qs + 1`
    \\ fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fs []
    \\ fs [EL_LENGTH_APPEND] \\ decide_tac)
  \\ `bits_to_word (qs ++ [T]) ≪ 1 ⋙ 1 =
      bits_to_word (qs ++ [T]):'a word` by
   (match_mp_tac shift_shift_lemma \\ fs [word_msb_def]
    \\ match_mp_tac bits_to_word_miss \\ fs [] \\ decide_tac)
  \\ fs [ADD1,word_or_eq_0]
QED

Theorem bits_to_word_bitstring_reverse:
  (bits_to_word xs:'a word) = bitstring$v2w (REVERSE xs)
Proof
  Induct_on `xs`
  >- simp[bitstringTheory.v2n,GSYM bitstringTheory.n2w_v2n, bits_to_word_def]
  >> fs[GSYM bitstringTheory.n2w_v2n]
  >> simp[bitstringTheory.v2n,bitstringTheory.v2n_APPEND,Once $ oneline bits_to_word_def]
  >> reverse $ rw[]
  >- fs[word_add_n2w,wordsTheory.LSL_ONE]
  >> fs[word_shift_or_1]
  >> fs[wordsTheory.LSL_ONE]
  >> fs[wordsTheory.word_mul_n2w,wordsTheory.word_add_n2w]
QED

Triviality GENLIST_bits_to_word_alt:
  LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs
Proof
  fs[Cong GENLIST_CONG,bits_to_word_bit,EL_APPEND1] >>
  fs[GENLIST_EL_MAP]
QED

Triviality GENLIST_bits_to_word:
  LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'
Proof
  fs[GENLIST_bits_to_word_alt]
QED

Triviality read_bitmap_word_list:
  8 <= dimindex (:'a) ==>
    read_bitmap
      ((word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++ (xs:'a word list)) =
    SOME qs
Proof
  completeInduct_on `LENGTH (qs:bool list)` \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rw [] \\ once_rewrite_tac [word_list_def]
  \\ `dimindex (:'a) - 1 <> 0` by decide_tac \\ fs []
  \\ Cases_on `LENGTH qs + 1 <= dimindex (:'a) - 1` \\ fs []
  THEN1
   (fs [read_bitmap_def]
    \\ `~word_msb (bits_to_word (qs ++ [T]))` by
     (fs [word_msb_def] \\ match_mp_tac bits_to_word_miss
      \\ fs [] \\ decide_tac) \\ fs []
    \\ `LENGTH qs + 1 < dimindex (:'a)` by decide_tac
    \\ fs [bit_length_bits_to_word,GENLIST_bits_to_word])
  \\ fs [read_bitmap_def]
  \\ `dimindex (:'a) - 1 =
        LENGTH (TAKE (dimindex (:'a) - 1) (qs ++ [T]))` by
    (fs [LENGTH_TAKE_EQ,MIN_DEF] \\ decide_tac)
  \\ `word_msb (bits_to_word (TAKE (dimindex (:'a) - 1)
         (qs ++ [T]) ++ [T]) :'a word)` by
   (fsrw_tac[] [word_msb_def]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fsrw_tac[] []
    \\ reverse (rpt strip_tac) THEN1 decide_tac THEN1 decide_tac
    \\ pop_assum (fn th => simp_tac std_ss [Once th])
    \\ fsrw_tac[] [EL_LENGTH_APPEND]) \\ fs []
  \\ `DROP (dimindex (:'a) - 1) (qs ++ [T]) =
      DROP (dimindex (:'a) - 1) qs ++ [T]` by
   (match_mp_tac DROP_APPEND1 \\ fs [NOT_LESS] \\ decide_tac)
  \\ `TAKE (dimindex (:'a) - 1) (qs ++ [T]) =
      TAKE (dimindex (:'a) - 1) qs` by
   (match_mp_tac TAKE_APPEND1 \\ fs [NOT_LESS] \\ decide_tac) \\ fs []
  \\ first_x_assum (mp_tac o Q.SPEC `DROP (dimindex (:'a) - 1) qs`)
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [LENGTH_DROP] \\ decide_tac)
  \\ rpt strip_tac \\ fs []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV
        [GSYM (Q.SPEC `dimindex (:'a) - 1`
          (INST_TYPE [``:'a``|->``:bool``] TAKE_DROP))]))
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ Q.ABBREV_TAC `ts = TAKE (dimindex (:'a) - 1) qs` \\ fs []
  \\ match_mp_tac GENLIST_bits_to_word_alt \\ fs []
  \\ decide_tac
QED

Triviality APPEND_LEMMA:
  n1 + n2 + n3 <= LENGTH xs ==>
    ?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2
Proof
  rpt strip_tac
  \\ `n1 <= LENGTH xs` by decide_tac
  \\ Q.PAT_X_ASSUM `n1 + n2 + n3 <= LENGTH xs` MP_TAC
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [DROP_LENGTH_APPEND]  \\ fs []
  \\ rename [‘n2 + (n3 + LENGTH xs1) ≤ LENGTH xs1 + LENGTH xs2’]
  \\ `n2 <= LENGTH xs2` by decide_tac
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [] \\ metis_tac []
QED

Theorem read_bitmap_write_bitmap:
   8 ≤ dimindex (:α) ⇒
   read_bitmap ((write_bitmap names k f'):α word list) =
   SOME (GENLIST (λx. MEM x (MAP (λ(r,y). f' - 1 - (r DIV 2 - k)) (toAList names))) f')
Proof
  rw[write_bitmap_def]
  \\ imp_res_tac read_bitmap_word_list
  \\ first_x_assum(qspec_then`[]`mp_tac)
  \\ simp[]
QED

Theorem read_bitmap_insert_bitmap:
   ∀bs n bs' n' i cur.
   i < dimword (:α) ∧
   IS_SOME (read_bitmap bm) ∧
   n = LENGTH cur + LENGTH (append bs) ∧
   insert_bitmap bm (bs, n) = ((bs',n'),i)
   ⇒ read_bitmap (DROP (i MOD dimword (:α)) (cur++append bs')) = read_bitmap bm
Proof
  simp[insert_bitmap_def] \\ rw[] \\ simp[DROP_LENGTH_APPEND]>>
  metis_tac[DROP_LENGTH_APPEND,LENGTH_APPEND]
QED

(*
TODO
Theorem insert_bitmap_length:
   ∀ls n ls' n' i.
   insert_bitmap bm (ls,n) = ((ls',n'),i) ∧
   n ≤ LENGTH (append ls) ⇒
   i ≤ LENGTH (append ls) ∧ LENGTH (append ls) ≤ LENGTH (append ls')
Proof
  simp[insert_bitmap_def]
QED
*)

(*

val read_bitmap_write_bitmap = Q.prove(
  `t.stack_space + f <= LENGTH t.stack /\ 8 <= dimindex (:'a) /\
    (LENGTH (write_bitmap names k f': 'a word list) + f' = f) /\
    (if f' = 0 then f = 0 else f = f' + f' DIV (dimindex (:'a) - 1) + 1) /\
    (1 <= f) ==>
    read_bitmap
      (list_LUPDATE (MAP Word (write_bitmap (names:num_set) k f')) 0
         (DROP t.stack_space t.stack)) =
    SOME (GENLIST (\x. MEM x (MAP (\(r,y). (f'-1) - (r DIV 2 - k)) (toAList names))) f',
          MAP Word (write_bitmap names k f'): 'a word_loc list,
          (DROP (f - f') (DROP t.stack_space t.stack)))`,
  fs [write_bitmap_def,LET_DEF]
  \\ Q.ABBREV_TAC `qs = GENLIST
           (\x. MEM x (MAP (\(r,y). (f'-1) - (r DIV 2 -k) ) (toAList names))) f'`
  \\ rpt strip_tac
  \\ `t.stack_space + (f - f') + f' <= LENGTH t.stack` by
    (`f <> 0` by decide_tac \\ fs [] \\ decide_tac)
  \\ imp_res_tac APPEND_LEMMA
  \\ fs [DROP_LENGTH_APPEND]
  \\ `LENGTH (MAP Word (word_list (qs ++ [T]) (dimindex (:'a) - 1) :'a word list)) =
      LENGTH xs2` by (fs [] \\ decide_tac)
  \\ imp_res_tac list_LUPDATE_APPEND \\ fs [read_bitmap_word_list])
  |> INST_TYPE [beta|->``:'ffi``];

*)

Triviality abs_stack_IMP_LENGTH:
  ∀bs wstack sstack lens stack.
    abs_stack bs wstack sstack lens = SOME stack ⇒ LENGTH stack = LENGTH wstack ∧ LENGTH lens = LENGTH wstack
Proof
  recInduct (theorem "abs_stack_ind")
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
QED

Triviality SORTED_FST_LESS_IMP:
  !xs x.
      SORTED (\x y. FST x > FST y:num) (x::xs) ==>
      SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
      (!y. MEM y xs ==> FST x > FST y)
Proof
  Induct \\ fs [SORTED_DEF]
  \\ ntac 3 strip_tac \\ res_tac \\ rpt strip_tac
  \\ rw [] \\ fs [] \\ res_tac \\ decide_tac
QED

Triviality SORTED_IMP_EQ_LISTS:
  !xs ys.
      SORTED (\x y. FST x > FST y:num) ys /\
      SORTED (\x y. FST x > FST y) xs /\
      (!x. MEM x ys <=> MEM x xs) ==>
      (xs = ys)
Proof
  Induct \\ fs [] \\ Cases_on `ys` \\ fs [] THEN1 metis_tac []
  THEN1 (CCONTR_TAC THEN fs [] THEN metis_tac [])
  \\ ntac 2 strip_tac
  \\ Cases_on `h = h'` \\ fs [] THEN1
   (first_x_assum match_mp_tac
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ metis_tac [])
  \\ Cases_on `FST h > FST h'`
  THEN1
   (first_assum (mp_tac o Q.SPEC `h`)
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ rpt strip_tac \\ fs [] \\ fs []
    \\ res_tac \\ decide_tac)
  THEN1
   (first_assum (mp_tac o Q.SPEC `h'`)
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ rpt strip_tac \\ fs [] \\ fs [])
QED

Theorem transitive_key_val_compare:
   transitive key_val_compare
Proof
  fs[transitive_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ imp_res_tac WORD_LESS_EQ_TRANS \\ fs []
QED

Theorem total_key_val_compare:
   total key_val_compare
Proof
  fs[total_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ CCONTR_TAC \\ fs [] \\ TRY decide_tac
  \\ fs [GSYM WORD_NOT_LESS]
  \\ wordsLib.WORD_DECIDE_TAC
QED

Triviality SORTS_QSORT_key_val_compare:
  SORTS QSORT key_val_compare
Proof
  match_mp_tac QSORT_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare)
QED

val MEM_QSORT = SORTS_QSORT_key_val_compare
  |> SIMP_RULE std_ss [SORTS_DEF]
  |> SPEC_ALL |> CONJUNCT1
  |> MATCH_MP MEM_PERM |> GSYM |> GEN_ALL

Triviality SORTED_weaken2:
  ∀ls. SORTED R ls ∧
  ALL_DISTINCT ls ∧
  (∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ∧ R x y ⇒ R' x y) ⇒
  SORTED R' ls
Proof
  Induct>>rw[]>>Cases_on`ls`>>fs[SORTED_DEF]>>
  metis_tac[]
QED

Triviality EVEN_GT:
  ∀a b.
  EVEN a ∧ EVEN b ∧
  a > b ⇒
  a DIV 2 > b DIV 2
Proof
  fs[EVEN_EXISTS]>>rw[]>>
  fsrw_tac[][MULT_DIV,MULT_COMM]>>
  DECIDE_TAC
QED

Triviality transitive_GT:
  transitive ($> : (num->num->bool))
Proof
  fs[transitive_def]>>DECIDE_TAC
QED

Triviality env_to_list_K_I_IMP:
  !env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l
Proof
  fs [env_to_list_def,LET_DEF,FUN_EQ_THM,list_rearrange_I] \\ rw []
  \\ pop_assum kall_tac
  \\ qspec_then `toAList env` mp_tac (SORTS_QSORT_key_val_compare
        |> REWRITE_RULE [SORTS_DEF])
  \\ Q.SPEC_TAC (`QSORT key_val_compare (toAList env)`,`l`) \\ rw []
  \\ `PERM (MAP FST (toAList env)) (MAP FST l)` by (match_mp_tac PERM_MAP \\ fs [])
  \\ `ALL_DISTINCT (MAP FST l)` by metis_tac [ALL_DISTINCT_MAP_FST_toAList,
         sortingTheory.ALL_DISTINCT_PERM]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ Induct_on `l` \\ fs []
  \\ Cases_on `l` \\ fs [SORTED_DEF] \\ rw []
  \\ res_tac \\ fs [key_val_compare_def,LET_DEF]
  \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs []
QED

Theorem isPREFIX_DROP:
  ∀s t i.
  isPREFIX s t ⇒
  isPREFIX (DROP i s) (DROP i t)
Proof
  Induct>>rw[]>>
  every_case_tac>>fs[]>>
  Cases_on`i`>>simp[]
QED

Triviality LLOOKUP_cons_SUC:
  m < n ⇒
  LLOOKUP (h::xs) (n - m) =
  LLOOKUP xs (n - (m+1))
Proof
  rw[]>>
  `n - m = SUC (n - (m+1))` by simp[]>>
  simp[LLOOKUP_def]
QED

Theorem evaluate_wLive[local]:
  wLive names (bs,n) (k,f,f') = (wlive_prog,(bs',n')) /\
  (∀x. x ∈ domain (FST names) ⇒ EVEN x /\ k ≤ x DIV 2) /\
  (∀x. x ∈ domain (SND names) ⇒ EVEN x /\ k ≤ x DIV 2) /\
  state_rel ac k f f' (s:('a,num # 'c,'ffi) wordSem$state) t lens 0 /\
  1 <= f /\
  (cut_envs names s.locals = SOME envs) /\
  LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
  isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ==>
  ?t5:('a,'c,'ffi) stackSem$state bs5.
    (evaluate (wlive_prog,t) = (NONE,t5)) /\
    state_rel ac k 0 0 (push_env envs ^nn s with <|locals := LN; locals_size := SOME 0|>) t5 (f'::lens) 0 /\
    state_rel ac k f f' s t5 lens 0 /\
    LENGTH t5.stack = LENGTH t.stack /\ t5.stack_space = t.stack_space /\
    !i. i ≠ k ==> get_var i t5 = get_var i t
Proof
  rw[wLive_def]
  \\ pairarg_tac \\ gvs[]
  \\ fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
         stackSemTheory.assign_def,stackSemTheory.word_exp_def]
  \\ `t.stack_space <= LENGTH t.stack /\
     t.use_stack /\ ~(LENGTH t.stack ≤ t.stack_space)` by
        (fsrw_tac[][state_rel_def,LET_THM,stack_rel_def] \\ decide_tac) \\ fsrw_tac[] []
  \\ fsrw_tac[] [stackSemTheory.set_var_def,stackSemTheory.get_var_def,
         FLOOKUP_UPDATE,DECIDE ``i<n ==> i<>n:num``]
  \\ fsrw_tac[] [state_rel_def,push_env_def,LET_THM,FUN_EQ_THM,env_to_list_def,
         lookup_def,FLOOKUP_UPDATE,DECIDE ``i<n ==> i<>n:num``,
         DROP_list_LUPDATE_lemma |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def]]
  \\ reverse (rpt strip_tac)
  THEN1
   (res_tac \\ srw_tac[] [] \\ fsrw_tac[] []
    \\ qpat_x_assum `xx = SOME v` (fn th => once_rewrite_tac [GSYM th])
    \\ match_mp_tac (LLOOKUP_list_LUPDATE_IGNORE |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def])
    \\ fsrw_tac[] [] \\ Cases_on `f' = 0` \\ fsrw_tac[] [] \\ decide_tac)
  THEN1
   (qpat_x_assum `stack_rel k s.handler s.stack xx yy tt _ _` mp_tac
    \\ match_mp_tac (METIS_PROVE [] ``(b1 = b2) ==> (b1 ==> b2)``)
    \\ AP_THM_TAC \\ AP_THM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ match_mp_tac (GSYM DROP_list_LUPDATE_IGNORE |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def])
    \\ fsrw_tac[] [] \\ decide_tac)
  >>~[`flat_exp_conventions word_prog`]
  >- metis_tac[]
  >- metis_tac[]
  >>~[`post_alloc_conventions k word_prog`]
  >- metis_tac[]
  >- metis_tac[]
  >~[`stack_rel k s.handler _ _ _ _ _ (f'::lens)`]
  >- (
    fsrw_tac[][wf_def]
    \\ fsrw_tac[] [stack_rel_def,stack_rel_aux_def,abs_stack_def]
    \\ Cases_on `DROP t.stack_space t.stack` \\ fsrw_tac[] []
    \\ fsrw_tac[] [LUPDATE_def,abs_stack_def]
    \\ conj_tac
    >- (
      Q.ISPEC_THEN `SND envs` mp_tac  env_to_list_K_I_IMP
      \\ fsrw_tac[] [env_to_list_def,sorted_env_def,LET_DEF] \\ srw_tac[] []
      \\ `s.permute 0 = I` by fsrw_tac[] [FUN_EQ_THM] \\ fsrw_tac[] [])
    \\ fsrw_tac[] [full_read_bitmap_def,GSYM word_add_n2w]
    \\ `i < dimword(:α) ∧ (i+1) MOD dimword(:'a) ≠ 0` by (
        fs[insert_bitmap_def] >> rveq>>
        drule IS_PREFIX_LENGTH>>
        simp[])
    \\ drule (GEN_ALL read_bitmap_insert_bitmap |> INST_TYPE [beta |-> alpha])
    \\ simp[IS_SOME_EXISTS,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ qpat_x_assum `insert_bitmap _ _ = _` mp_tac
    \\ `n = LENGTH (TAKE (n-LENGTH (append bs)) t.bitmaps) + LENGTH (append bs)` by fs[LENGTH_TAKE]
    \\ pop_assum SUBST1_TAC
    \\ strip_tac
    \\ disch_then drule
    \\ simp[read_bitmap_write_bitmap]
    \\ strip_tac
    \\ `isPREFIX (DROP i (TAKE (n − LENGTH (append bs)) t.bitmaps ++ append bs')) (DROP i t.bitmaps)` by (
      fs[LENGTH_TAKE,insert_bitmap_def]>>rveq>>fs[]>>
      qmatch_goalsub_abbrev_tac`DROP a b`>>
      `DROP a b = write_bitmap (SND names) k f'` by
        (unabbrev_all_tac>> simp[DROP_APPEND])>>
      drule isPREFIX_DROP>>
      disch_then(qspec_then`LENGTH (append bs)` mp_tac)>>
      simp[DROP_APPEND,DROP_LENGTH_NIL]>>
      simp[Abbr`a`]>>
      DEP_REWRITE_TAC[DROP_DROP,LENGTH_TAKE]>>
      simp[]>>
      drule IS_PREFIX_LENGTH>>
      simp[])
    \\ fsrw_tac[][IS_PREFIX_APPEND]
    \\ imp_res_tac read_bitmap_append_extra
    \\ simp[DROP_APPEND]
    \\ gvs[]
    \\ ntac 2 (pop_assum kall_tac)
    \\ conj_tac
    >- (
      srw_tac[][]
      \\ imp_res_tac abs_stack_IMP_LENGTH
      \\ Cases_on`s.handler<LENGTH s.stack`>>fsrw_tac[][]
      \\ qpat_x_assum`is_handler_frame _`mp_tac
      >- (simp[ADD1,EL_CONS,PRE_SUB1,LASTN_CONS])
      \\ simp[ADD1]
      \\ `LENGTH s.stack - s.handler = 0` by DECIDE_TAC
      \\ simp[is_handler_frame_def])
    \\ simp[stack_rel_aux_def]
    \\ `∀x. s.permute x = I` by simp[FUN_EQ_THM]
    \\ simp[list_rearrange_I]
    \\ qmatch_assum_abbrev_tac`DROP nn ll = _`
    \\ qispl_then[`nn`,`ll`]mp_tac LENGTH_DROP
    \\ asm_simp_tac(std_ss)[Abbr`ll`,Abbr`nn`]
    \\ simp[]
    \\ fs[stack_size_rel_def]
    \\ rpt strip_tac
    >- (
      qpat_x_assum`cut_envs _ _ = SOME _` mp_tac>>
      simp[cut_envs_def,cut_names_def,AllCaseEqs()]>>
      rw[]>>
      gvs[ALOOKUP_toAList,lookup_inter,AllCaseEqs(),domain_lookup]>>
      last_x_assum drule>>
      strip_tac>>
      first_x_assum drule>>
      simp[]>>
      strip_tac>>
      DEP_REWRITE_TAC[ALOOKUP_index_list]>>
      rw[LENGTH_TAKE_EQ]>>
      gvs[LLOOKUP_cons_SUC])
    \\ match_mp_tac IMP_filter_bitmap_EQ_SOME_NIL
    \\ fsrw_tac[] [] \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ conj_asm1_tac THEN1 (
        fsrw_tac[] [LENGTH_index_list,LENGTH_TAKE_EQ,MIN_DEF]
        \\ srw_tac[][] >> decide_tac )
    \\ fsrw_tac[] [ZIP_GENLIST] \\ pop_assum kall_tac
    \\ `?names0 names1. names = (names0,names1)` by metis_tac[PAIR]
    \\ gvs[cut_envs_def,AllCaseEqs(),cut_names_def]
    \\ qmatch_goalsub_abbrev_tac`QSORT _ (toAList envs1)`
    \\ qpat_abbrev_tac`ls = MAP _ (toAList _)`
    \\ `!x. MEM x ls <=>
            ?n. x = f' - 1 - (n DIV 2 - k) /\ n IN domain envs1` by (
      fs[MEM_MAP,EXISTS_PROD,MEM_toAList,Abbr`ls`,lookup_inter_alt,domain_lookup,SUBSET_DEF,Abbr`envs1`]
      \\ metis_tac [])
    \\ fsrw_tac[] []
    \\ ntac 2 (pop_assum kall_tac)
    \\ fsrw_tac[] [MAP_FST_def,adjust_names_def]
    \\ match_mp_tac SORTED_IMP_EQ_LISTS
    \\ conj_tac
    >- (
      REWRITE_TAC[GSYM inv_image_def,sorted_map] >>
      qmatch_abbrev_tac`SORTED R' (QSORT R ls)` >>
      `SORTED R (QSORT R ls)` by (
        match_mp_tac QSORT_SORTED >>
        metis_tac[transitive_key_val_compare,total_key_val_compare] ) >>
      match_mp_tac SORTED_weaken2>>fsrw_tac[][]>>CONJ_ASM1_TAC
      >-
        metis_tac[ALL_DISTINCT_MAP_FST_toAList,QSORT_PERM,ALL_DISTINCT_PERM,ALL_DISTINCT_MAP]
      >>
        simp[MEM_QSORT,Abbr`R`] >>
        simp[Abbr`R'`,inv_image_def,FORALL_PROD,Abbr`ls`,MEM_toAList] >>
        fsrw_tac[][key_val_compare_def,LET_THM]>>
        `∀p v. lookup p envs1 = SOME v ⇒ lookup p s.locals = SOME v` by (
          simp[Abbr`envs1`,lookup_inter_EQ])>>
        srw_tac[][]>>fsrw_tac[][]>>res_tac>>res_tac>>
        fsrw_tac[][EVEN_GT])
    \\ conj_tac
    >- (
      ONCE_REWRITE_TAC[sorted_map] >>
      REWRITE_TAC[GSYM inv_image_def] >>
      match_mp_tac (MP_CANON sorted_filter) >>
      conj_tac >- metis_tac[transitive_inv_image,transitive_GT] >>
      ONCE_REWRITE_TAC[GSYM sorted_map] >>
      simp[MAP_GENLIST,combinTheory.o_DEF] >>
      ONCE_REWRITE_TAC[GSYM sorted_map] >>
      simp[MAP_GENLIST,combinTheory.o_DEF] >>
      qmatch_abbrev_tac`SORTED R (GENLIST g m)` >>
      `GENLIST g m = GENLIST (λx. k + m - (x + 1)) m` by (
        simp[LIST_EQ_REWRITE,Abbr`g`] >>
        srw_tac[][] >>
        qmatch_abbrev_tac`FST (EL x (index_list ls k)) = Z` >>
        qmatch_assum_abbrev_tac`DROP nn ll = _`
        \\ qispl_then[`nn`,`ll`]mp_tac LENGTH_DROP
        \\ asm_simp_tac(std_ss)[Abbr`ll`,Abbr`nn`]
        \\ simp[] >>
        `x < LENGTH ls` by ( simp[Abbr`ls`] ) >>
        asm_simp_tac std_ss [EL_index_list] >>
        simp[Abbr`ls`,Abbr`Z`] ) >>
      pop_assum SUBST1_TAC >>
      fsrw_tac[][Abbr`R`]>>
      fsrw_tac[][SORTED_EL_SUC]>>srw_tac[][]>>
      `n'' < m` by DECIDE_TAC>>
      fsrw_tac[][EL_GENLIST]>>DECIDE_TAC)
    \\ simp[MEM_MAP,MEM_FILTER,MEM_GENLIST,PULL_EXISTS,MEM_QSORT,
              MEM_toAList,EXISTS_PROD,FORALL_PROD,Abbr`envs1`]
    \\ rw[]
    \\ simp[lookup_inter_alt,domain_inter]
    \\ fsrw_tac[][SUBSET_DEF]
    \\ `LENGTH (TAKE f' t') = f'` by ( simp[LENGTH_TAKE_EQ] )
    \\ srw_tac[][EQ_IMP_THM]
    >- (
      fsrw_tac[][domain_lookup,PULL_EXISTS]
      \\ ONCE_REWRITE_TAC[CONJ_COMM]
      \\ asm_exists_tac \\ simp[]
      \\ first_x_assum drule >> strip_tac
      \\ first_x_assum drule
      \\ last_x_assum drule
      \\ IF_CASES_TAC >- simp[]
      \\ simp[LLOOKUP_THM,EVEN_EXISTS]
      \\ strip_tac >> rveq
      \\ fsrw_tac[][MULT_COMM,MULT_DIV]
      \\ fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1]
      \\ simp[EL_index_list] )
    \\ fsrw_tac[][domain_lookup]
    \\ first_x_assum drule >> strip_tac
    \\ first_x_assum drule
    \\ last_x_assum drule
    \\ IF_CASES_TAC >- simp[]
    \\ simp[LLOOKUP_THM,EVEN_EXISTS]
    \\ strip_tac >> rveq
    \\ fsrw_tac[][MULT_COMM,MULT_DIV]
    \\ fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1]
    \\ rfs[]
    \\ qpat_x_assum`_ = EL _ (index_list _ _)`(mp_tac o SYM)
    \\ simp[EL_index_list] >> strip_tac >> rveq
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[]
    \\ simp_tac (srw_ss()) [MULT_COMM,MULT_DIV]
  ) >>
  fs[stack_size_rel_def] >> rw[]
  >- (
    rw[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF] >>
    fs[the_eqn,stack_size_eq] >> fs[])
  >- (
    fs[IS_SOME_EXISTS,OPTION_MAP2_DEF,PULL_EXISTS] >> fs[] >>
    fs[the_eqn,CaseEq"option",stack_size_eq] >>
    rveq >> fs[])
QED

Triviality state_rel_set_store_0:
  state_rel ac k 0 0 s5 t5 len extra ⇒
  state_rel ac k 0 0 (set_store AllocSize w s5) (set_store AllocSize w t5) len extra
Proof
  rpt strip_tac
  \\ fs [state_rel_def,set_store_def,stackSemTheory.set_store_def,LET_DEF,
         FLOOKUP_DEF] \\ REPEAT STRIP_TAC \\ rfs[]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [fmap_EXT,DRESTRICT_DEF,EXTENSION]
  \\ rpt strip_tac  THEN1 (Cases_on `x = Handler` \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]
  \\ metis_tac[]
QED

Triviality read_bitmap_not_empty:
  read_bitmap stack = SOME a ⇒
  stack ≠ []
Proof
  rw[]>>CCONTR_TAC>>
  fs[]>>
  fs[read_bitmap_def]
QED

Triviality n2w_lsr_1:
  n < dimword (:'a) ==> n2w n >>> 1 = (n2w (n DIV 2)):'a word
Proof
  once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr] \\ fs []
  \\ fs [DIV_LT_X] \\ decide_tac
QED

Triviality handler_bitmap_props:
  good_dimindex(:'a) ⇒
  read_bitmap ((4w:'a word)::stack) = SOME [F;F]
Proof
  fs [read_bitmap_def,good_dimindex_def] \\ strip_tac
  \\ `~(word_msb 4w)` by fs [word_msb_def,wordsTheory.word_index] \\ fs []
  \\ `4 < dimword (:'a) /\ 2 < dimword (:'a)` by fs [dimword_def]
  \\ `bit_length 4w = 3` by
   (NTAC 4 (fs [dimword_def,Once bit_length_def,n2w_lsr_1,EVAL ``1w ⋙ 1``]))
  \\ fs [] \\ EVAL_TAC \\ rw [] \\ decide_tac
QED

Triviality enc_stack_lemma:
  ∀bs (wstack:'a stack_frame list) sstack lens astack bs'.
      good_dimindex(:'a) ∧
      LENGTH bs + 1 < dimword (:'a) ∧
      abs_stack bs wstack sstack lens = SOME astack ∧
      (*The first bitmap is the handler one*)
      1 ≤ LENGTH bs ∧
      HD bs = 4w ∧
      stack_rel_aux k len wstack astack ⇒
      enc_stack bs sstack = SOME (enc_stack wstack)
Proof
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  fs[enc_stack_def]>>
  rw[]>>
  fs[Once stackSemTheory.enc_stack_def,abs_stack_def]>>
  qpat_x_assum`A=SOME astack` mp_tac>>
  TOP_CASE_TAC>>fs[]
  >- (
    simp[]
    \\ TOP_CASE_TAC \\ strip_tac>>
    rveq>>fs[stack_rel_aux_def]>>
    imp_res_tac filter_bitmap_lemma>>
    fs[]>>rfs[]>>
    qpat_x_assum`A=SOME(enc_stack wstack)` mp_tac>>
    Cases_on`w`>>fs[full_read_bitmap_def]
    \\ fs[MAP_SND_MAP_FST]
    \\ IF_CASES_TAC \\ simp[]
    \\ rveq \\ fs[]
    \\ fs[w2n_minus1]
    \\ qmatch_assum_abbrev_tac`read_bitmap ls = _`
    \\ `ls = []` by (
      simp[Abbr`ls`,DROP_LENGTH_TOO_LONG] )
    \\ fs[read_bitmap_def] )
  >>
  Cases_on`bs`>>fs[]>>
  ntac 3 TOP_CASE_TAC>>fs[]>>
  simp[]
  \\ TOP_CASE_TAC
  \\ strip_tac
  \\ pop_assum (assume_tac o SYM)
  \\ qmatch_assum_rename_tac`stack_rel_aux _ _ (StackFrame _ _ _ (SOME p)::_) _`
  \\ PairCases_on`p`
  \\ fs[stack_rel_aux_def]
  \\ rfs[]
  \\ qmatch_assum_rename_tac`full_read_bitmap _ ww = _`
  \\ Cases_on`ww` \\ fs[full_read_bitmap_def]
  \\ rveq
  \\ imp_res_tac filter_bitmap_lemma
  \\ simp[handler_bitmap_props] >>
  simp[filter_bitmap_def]>>
  simp[Once stackSemTheory.enc_stack_def]>>
  simp[full_read_bitmap_def,MAP_SND_MAP_FST]
QED

Triviality IMP_enc_stack:
  state_rel ac k 0 0 s1 t1 lens 0
    ==>
    (enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
       SOME (enc_stack s1.stack))
Proof
  fs [state_rel_def,LET_DEF] \\ rpt strip_tac
  \\ fs [stack_rel_def] \\ imp_res_tac enc_stack_lemma>>
  simp[]
QED

Triviality map_bitmap_success:
  ∀bs stack a b ls.
  filter_bitmap bs stack = SOME(a,b) ∧
  LENGTH ls = LENGTH a ⇒
  ∃x z.
  map_bitmap bs ls stack = SOME(x,[],DROP (LENGTH bs) stack) ∧
  filter_bitmap bs x = SOME(ls,[])
Proof
  ho_match_mp_tac filter_bitmap_ind>>fs[filter_bitmap_def,map_bitmap_def]>>
  rw[LENGTH_NIL]
  >-
    (res_tac>>fs[filter_bitmap_def])
  >>
    EVERY_CASE_TAC>>fs[]>>
    rveq>>Cases_on`ls`>>fs[map_bitmap_def,filter_bitmap_def]>>
    res_tac>>fs[filter_bitmap_def]
QED

(*Might need to extend c as well*)
Triviality map_bitmap_more:
  ∀bs ls stack n a c ls'.
  map_bitmap bs ls stack = SOME(a,[],c) ⇒
  map_bitmap bs (ls++ls') stack = SOME(a,ls',c)
Proof
  ho_match_mp_tac map_bitmap_ind>>fs[map_bitmap_def]>>rw[]>>
  pop_assum mp_tac>>ntac 3 TOP_CASE_TAC>>fs[]
QED

Triviality map_bitmap_more_simp:
  map_bitmap bs (TAKE (LENGTH l) ls) stack = SOME (a,[],c) ⇒
  map_bitmap bs ls stack = SOME (a,DROP (LENGTH l) ls,c)
Proof
  metis_tac[TAKE_DROP,map_bitmap_more]
QED

(*These two are actually implied by s_key_eq*)
Triviality word_stack_dec_stack_shape:
  ∀ls wstack res n.
  dec_stack ls wstack = SOME res ∧ n < LENGTH wstack ⇒
  (is_handler_frame (EL n wstack) ⇔ is_handler_frame (EL n res))
Proof
  ho_match_mp_tac dec_stack_ind>>fs[dec_stack_def,is_handler_frame_def]>>
  rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  rveq>>
  rename1 `EL m _` >>
  Cases_on`m`>-
    (Cases_on`handler`>>
    simp[is_handler_frame_def])>>
  simp[]
QED

Triviality sorted_env_zip:
  ∀l:(num,'a word_loc) alist ls:'a word_loc list x n.
  sorted_env (StackFrame n l0 l x) ∧
  LENGTH ls = LENGTH l ⇒
  sorted_env (StackFrame n l0 (ZIP (MAP FST l, ls)) x)
Proof
  fs[sorted_env_def]>>
  Induct>>fs[LENGTH_NIL]>>rw[]>>
  Cases_on`ls`>>fs[]>>
  qmatch_abbrev_tac`SORTED R _`>>
  `transitive R` by
    (fs[Abbr`R`,transitive_def]>>
    DECIDE_TAC)>>
  fs[SORTED_EQ,MEM_ZIP,PULL_EXISTS,MEM_EL]>>
  rw[]>>res_tac>>
  fs[Abbr`R`,EL_MAP]
QED

Triviality word_stack_dec_stack_sorted:
  ∀(ls:'a word_loc list) (wstack:'a stack_frame list) res.
  dec_stack ls wstack = SOME res ∧
  EVERY sorted_env wstack ⇒
  EVERY sorted_env res
Proof
  ho_match_mp_tac dec_stack_ind>>fs[dec_stack_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>rveq>>
  rfs[]>>
  match_mp_tac sorted_env_zip>>
  simp[]
QED

Triviality abs_stack_empty:
  ∀bs ls stack lens.
  abs_stack bs [] ls lens = SOME stack ⇒ ls = [Word 0w] ∧ lens = []
Proof
  rpt Cases>>fs[abs_stack_def]
QED

Definition abs_frame_eq_def:
  abs_frame_eq p q ⇔
  FST p = FST q ∧
  FST (SND p) = FST (SND q) ∧
  LENGTH (SND (SND p)) = LENGTH (SND (SND q))
End

Triviality LIST_REL_abs_frame_eq_handler_val:
  ∀xs ys.
  LIST_REL abs_frame_eq xs ys ⇒
  handler_val xs = handler_val ys
Proof
  ho_match_mp_tac LIST_REL_ind>>
  fs[handler_val_def,abs_frame_eq_def,FORALL_PROD]>>rw[]>>
  Cases_on`p_1`>>fs[handler_val_def]
QED

(*Prove the inductive bits first...*)
Triviality dec_stack_lemma1:
  ∀bs (wstack:'a stack_frame list) sstack lens astack wdec ls.
  good_dimindex(:'a) ∧
  1 ≤ LENGTH bs ∧
  HD bs = 4w ∧
  (*The things going into GC are the same*)
  abs_stack bs wstack sstack lens = SOME astack ∧
  stack_rel_aux k len wstack astack ∧
  (*The word stack is successfully decoded*)
  dec_stack ls wstack = SOME wdec ⇒
  ∃sdec bstack.
  (*The stackLang stack is successfully decoded*)
  dec_stack bs ls sstack = SOME sdec ∧
  abs_stack bs wdec sdec lens = SOME bstack ∧
  stack_rel_aux k len wdec bstack ∧
  (*They have exactly the same shape*)
  LIST_REL abs_frame_eq astack bstack
Proof
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  fsrw_tac[][dec_stack_def,enc_stack_def]>>
  srw_tac[][]>>
  fsrw_tac[][Once stackSemTheory.enc_stack_def,abs_stack_def]
  >- (
    rveq>>
    Cases_on`ls`>>fsrw_tac[][dec_stack_def]>>
    simp[stackSemTheory.dec_stack_def]>>rveq>>simp[abs_stack_def])
  >- (
    qpat_x_assum`A=SOME wdec` mp_tac>>
    qpat_x_assum`A=SOME astack`mp_tac>>
    rpt TOP_CASE_TAC>>fsrw_tac[][LET_THM]>>
    TOP_CASE_TAC>>
    srw_tac[][]>>rveq >>
    simp[stackSemTheory.dec_stack_def]>>
    Cases_on`w`>>fsrw_tac[][full_read_bitmap_def,stack_rel_aux_def]>>
    imp_res_tac filter_bitmap_lemma>>
    fsrw_tac[][MAP_SND_MAP_FST]>>
    imp_res_tac map_bitmap_success>>
    pop_assum kall_tac>>
    pop_assum(qspec_then `TAKE (LENGTH l) ls` assume_tac)>>
    `LENGTH l ≤ LENGTH ls` by DECIDE_TAC>>
    fsrw_tac[][]>>
    imp_res_tac map_bitmap_more_simp>>
    simp[]>>
    res_tac>>rveq>>fsrw_tac[][]>>
    simp[abs_stack_def,full_read_bitmap_def]>>
    imp_res_tac map_bitmap_length>>
    simp[DROP_APPEND2]>>
    simp[stack_rel_aux_def,TAKE_APPEND2]>>
    rpt CONJ_TAC
    >- (
      rw[]>>
      last_x_assum drule>>
      impl_tac >- (
        pop_assum mp_tac>>
        simp[ALOOKUP_NONE,MEM_MAP,MEM_ZIP,FORALL_PROD]>>
        simp[MEM_EL]>>
        metis_tac[PAIR,EL_MAP,FST])>>
      (* TODO: need to show it is not in the bitmap
        using filter_bitmap then use map_bitmap assumption *)
      cheat)
    >- (
      simp[ZIP_MAP,MAP_FST_def,MAP_MAP_o,o_DEF]
      \\ imp_res_tac filter_bitmap_IMP_MAP_FST
      \\ fsrw_tac[][index_list_eq_ZIP]
      \\ fsrw_tac[][MAP_ZIP,LENGTH_COUNT_LIST]
      \\ match_mp_tac filter_bitmap_MAP_IMP
      \\ simp[MAP_ZIP,LENGTH_COUNT_LIST]
      \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[]
      \\ simp[MAP_MAP_o,o_DEF,ETA_AX]
      \\ simp[MAP_ZIP]
      \\ simp[GSYM o_DEF]
      \\ ONCE_REWRITE_TAC[o_ASSOC]
      \\ simp[MAP_ZIP]
      \\ simp[MAP_FST_def,o_DEF,LAMBDA_PROD,MAP_MAP_o])
    >- fs[LENGTH_TAKE] >>
    fsrw_tac[][abs_frame_eq_def]>>
    simp[])
  >> (
    qpat_x_assum`A=SOME wdec` mp_tac>>
    qpat_x_assum`A=SOME astack`mp_tac>>
    rpt TOP_CASE_TAC>>fsrw_tac[][LET_THM]>>
    TOP_CASE_TAC>>
    srw_tac[][]>>rveq >>
    simp[stackSemTheory.dec_stack_def]>>
    fsrw_tac[][full_read_bitmap_def]>>Cases_on`bs`>>fsrw_tac[][]>>
    imp_res_tac handler_bitmap_props>>
    pop_assum(qspec_then`t'` assume_tac)>>fsrw_tac[][map_bitmap_def]>>
    Cases_on`h''`>>PairCases_on`v0`>>
    simp[stackSemTheory.dec_stack_def]>>
    fsrw_tac[][full_read_bitmap_def,stack_rel_aux_def]>>
    rfs[]>>
    imp_res_tac filter_bitmap_lemma>>
    fsrw_tac[][MAP_SND_MAP_FST]>>
    imp_res_tac map_bitmap_success>>
    pop_assum kall_tac>>
    pop_assum(qspec_then `TAKE (LENGTH l) ls` assume_tac)>>
    `LENGTH l ≤ LENGTH ls` by DECIDE_TAC>>
    fsrw_tac[][]>>
    imp_res_tac map_bitmap_more_simp>>
    simp[]>>
    res_tac>>rveq>>fsrw_tac[][]>>
    simp[abs_stack_def,full_read_bitmap_def]>>
    imp_res_tac map_bitmap_length>>
    simp[DROP_APPEND2]>>
    simp[stack_rel_aux_def,TAKE_APPEND2]>>
    srw_tac[][]
    >-
      (qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
      imp_res_tac abs_stack_IMP_LENGTH>>
      simp[]>>
      impl_tac>-
        (imp_res_tac word_stack_dec_stack_shape>>
        simp[]>>fsrw_tac[][])>>
      imp_res_tac list_rel_lastn>>
      pop_assum(qspec_then`v00+1` mp_tac)>>impl_tac>-
        DECIDE_TAC>>
      metis_tac[LIST_REL_abs_frame_eq_handler_val])
    >- (
      last_x_assum drule>>
      impl_tac >- (
        pop_assum mp_tac>>
        simp[ALOOKUP_NONE,MEM_MAP,MEM_ZIP,FORALL_PROD]>>
        simp[MEM_EL]>>
        metis_tac[PAIR,EL_MAP,FST])>>
      (* TODO: need to show it is not in the bitmap
        using filter_bitmap then use map_bitmap assumption *)
      cheat)
    >- (
      imp_res_tac filter_bitmap_IMP_MAP_FST
      \\ imp_res_tac filter_bitmap_IMP_MAP_SND
      \\ fsrw_tac[][index_list_eq_ZIP,LENGTH_COUNT_LIST,MAP_ZIP]
      \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[]
      \\ match_mp_tac filter_bitmap_MAP_IMP
      \\ simp[MAP_ZIP,LENGTH_COUNT_LIST]
      \\ simp[MAP_FST_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[MAP_ZIP]
      \\ simp[GSYM o_DEF]
      \\ simp[MAP_ZIP,MAP_MAP_o])
    >>
    fsrw_tac[][abs_frame_eq_def]>>
    simp[] >>
    fs[LENGTH_TAKE])
QED

val _ = get_time timer;
Triviality dec_stack_lemma:
  good_dimindex(:'a) ∧
  1 ≤ LENGTH t1.bitmaps ∧
  HD t1.bitmaps = 4w ∧
  (t1:('a,'c,'ffi) stackSem$state).stack_space ≤ LENGTH t1.stack ∧
  enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
      SOME (enc_stack s1.stack) /\
    (dec_stack x0 (s1:('a,num # 'c,'ffi) wordSem$state).stack = SOME x) /\
    stack_rel k s1.handler s1.stack (SOME (t1.store ' Handler))
      (DROP t1.stack_space t1.stack) (LENGTH t1.stack) t1.bitmaps lens /\
    (LENGTH (enc_stack s1.stack) = LENGTH x0) ==>
    ?yy:'a word_loc list. dec_stack t1.bitmaps x0 (DROP t1.stack_space t1.stack) = SOME yy /\
         (t1.stack_space + LENGTH yy = LENGTH t1.stack) /\
         stack_rel k s1.handler x (SOME (t1.store ' Handler)) yy
            (LENGTH t1.stack) t1.bitmaps lens
Proof
  rw[]>>
  fs[stack_rel_def]>>
  drule (GEN_ALL dec_stack_lemma1)>>
  disch_then(qspecl_then [`LENGTH t1.stack`,`k`,`t1.bitmaps`] assume_tac)>>
  rfs[]>>
  res_tac>>fs[]>>rveq>>fs[]>>rw[]
  >-
    (imp_res_tac dec_stack_length>>
    fs[LENGTH_DROP]>>
    simp[])
  >-
    metis_tac[word_stack_dec_stack_sorted]
  >>
    (qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
    imp_res_tac abs_stack_IMP_LENGTH>>
    simp[]>>
    impl_tac>-
      (imp_res_tac word_stack_dec_stack_shape>>
      simp[]>>fs[])>>
    imp_res_tac list_rel_lastn>>
    pop_assum(qspec_then`s1.handler+1` mp_tac)>>impl_tac>-
      DECIDE_TAC>>
    metis_tac[LIST_REL_abs_frame_eq_handler_val])
QED

Triviality dec_stack_stack_size:
  !xs st st'.
   dec_stack xs st = SOME st' ==>
   stack_size st = stack_size st'
Proof
  ho_match_mp_tac dec_stack_ind >>
  rw[dec_stack_def,stack_size_eq2,CaseEq "option"] >>
  rw[stack_size_eq2] >>
  Cases_on `handler` >> rw[stack_size_frame_def] >>
  res_tac >> simp[]
QED

Triviality gc_state_rel:
  gc (s1:('a,num # 'c,'ffi) wordSem$state) = SOME s2 /\
  state_rel ac k 0 0 s1 (t1:('a,'c,'ffi) stackSem$state) lens 0 ⇒
  ?(t2:('a,'c,'ffi) stackSem$state).
    gc t1 = SOME t2 /\
    state_rel ac k 0 0 (s2 with locals:= LN) t2 lens 0 /\
    LENGTH t2.stack = LENGTH t1.stack /\ t2.stack_space = t1.stack_space
Proof
  fs [gc_def,LET_DEF]
  \\ Cases_on `s1.gc_fun (enc_stack s1.stack,s1.memory,s1.mdomain,s1.store)` \\ fs []
  \\ PairCases_on `x` \\ fs [] \\ Cases_on `dec_stack x0 s1.stack` \\ fs []
  \\ rw [] \\ fs [stackSemTheory.gc_def]
  \\ `~(LENGTH t1.stack < t1.stack_space)` by
         (fs [state_rel_def] \\ decide_tac)
  \\ imp_res_tac IMP_enc_stack \\ fs [LET_DEF]
  \\ `t1.memory = s1.memory /\ t1.mdomain = s1.mdomain /\
      t1.gc_fun = s1.gc_fun /\ gc_fun_ok s1.gc_fun` by fs [state_rel_def] \\ fs []
  \\ `s1.store = t1.store \\ Handler` by
   (fs [state_rel_def] \\ Cases_on `FLOOKUP t1.store Handler`
    \\ fs [FLOOKUP_DEF,stack_rel_def,LET_DEF])
  \\ fs [gc_fun_ok_def] \\ res_tac \\ fs []
  \\ mp_tac dec_stack_lemma \\ fs [] \\ rpt strip_tac \\ fs []
  \\ fs [state_rel_def,FLOOKUP_UPDATE,LET_DEF,lookup_def,FLOOKUP_DEF]
  \\ rfs [FLOOKUP_DEF] \\ rw[]
  THEN1 (fs [fmap_EXT,EXTENSION,DOMSUB_FAPPLY_THM] \\ metis_tac [])
  \\ fs [DROP_APPEND,DROP_TAKE_NIL]
  \\ gvs[stack_size_rel_def]
  \\ metis_tac[dec_stack_stack_size]
QED

Triviality alloc_alt:
  FST (alloc c names (s:('a,num # 'c,'ffi) wordSem$state)) <>
    SOME (Error:'a wordSem$result) ==>
    (alloc c names (s:('a,num # 'c,'ffi) wordSem$state) =
     case cut_envs names s.locals of
       NONE => (SOME Error,s)
     | SOME env =>
         case gc (set_store AllocSize (Word c)
                    (push_env env ^nn s with <|locals := LN; locals_size := SOME 0|>)) of
           NONE => (SOME Error,s)
         | SOME s' =>
             case pop_env s' of
               NONE => (SOME Error,s')
             | SOME s' =>
                 case get_store AllocSize s' of
                   NONE => (SOME Error,s')
                 | SOME w =>
                     case has_space w s' of
                       NONE => (SOME Error,s')
                     | SOME T => (NONE,s')
                     | SOME F =>
                         (SOME NotEnoughSpace, flush_state T s'))
Proof
  fs [alloc_def]
  \\ Cases_on `cut_envs names s.locals` \\ fs []
  \\ simp[push_env_set_store]
  \\ every_case_tac \\ rw[]
QED


Type result = ``:'a wordSem$result``

Theorem s_key_eq_stack_size:
  !stack stack'. s_key_eq stack stack' ==> stack_size stack = stack_size stack'
Proof
  ho_match_mp_tac s_key_eq_ind >>
  rw[s_key_eq_def,stack_size_eq] >>
  rename1 `s_frame_key_eq x y` >>
  Cases_on `x` >>Cases_on `y` >>
  rename1 `s_frame_key_eq (StackFrame _ _ _ handler1) (StackFrame _ _ _ handler2)` >>
  Cases_on `handler1` >> Cases_on `handler2` >>
  fs[s_frame_key_eq_def,stack_size_eq]
QED

Theorem s_key_eq_push_env_locals_size:
  s_key_eq (push_env env opt1 s).stack
           (StackFrame n l0 l opt2::stack')
  ==>
  n = s.locals_size /\ stack_size s.stack = stack_size stack'
Proof
  MAP_EVERY qid_spec_tac [`s`,`opt1`,`env`] >>
  ho_match_mp_tac push_env_ind >>
  rw[push_env_def,s_key_eq_def,ELIM_UNCURRY] >>
  Cases_on `opt2` >> fs[s_frame_key_eq_def,s_key_eq_stack_size]
QED

Triviality alloc_IMP_alloc:
  (wordSem$alloc c names (s:('a,num # 'c,'ffi) wordSem$state) = (res:'a result option,s1)) /\
    (∀x. x ∈ domain (FST names) ⇒ EVEN x /\ k ≤ x DIV 2) /\
    (∀x. x ∈ domain (SND names) ⇒ EVEN x /\ k ≤ x DIV 2) /\
    1 ≤ f /\
    state_rel ac k f f' s t5 lens 0 /\
    state_rel ac k 0 0 (push_env envs ^nn s with <|locals := LN; locals_size := SOME 0|>) t5 (f'::lens) 0 /\
    (cut_envs names s.locals = SOME envs) /\
    res <> SOME Error ==>
    ?t1:('a,'c,'ffi) stackSem$state res1.
      (stackSem$alloc c t5 = (res1:'a stackSem$result option,t1)) /\
      if res = NONE then
        res1 = NONE /\
        state_rel ac k f f' s1 t1 lens 0 /\
        LENGTH t1.stack = LENGTH t5.stack /\
        t1.stack_space = t5.stack_space
      else
        res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) /\
        s1.clock = t1.clock /\ s1.ffi = t1.ffi
Proof
  Cases_on `FST (alloc c names (s:('a,num # 'c,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fsrw_tac[] [] \\ rfs [])
  \\ fsrw_tac[] [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fsrw_tac[] [push_env_set_store]
  \\ imp_res_tac state_rel_set_store_0
  \\ pop_assum (mp_tac o Q.SPEC `Word c`) \\ REPEAT STRIP_TAC
  \\ qmatch_asmsub_abbrev_tac `gc a`
  \\ Cases_on `gc a`
  \\ gvs[] \\ unabbrev_all_tac
  \\ drule_at (Pos last) gc_state_rel
  \\ rw[] \\ gvs[]
  \\ rename1`pop_env x`
  \\ Cases_on `pop_env x` \\ fsrw_tac[] []
  \\ Q.MATCH_ASSUM_RENAME_TAC `pop_env s2 = SOME s3`
  \\ `state_rel ac k f f' s3 t2 lens 0` by (
    imp_res_tac gc_s_key_eq>>
    fsrw_tac[][set_store_def]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    rveq>>
    fsrw_tac[][state_rel_def]>>
    fsrw_tac[][pop_env_def]>>rfs[]>>
    `opt = NONE` by
      (Cases_on`opt`>>
      fsrw_tac[][s_key_eq_def,push_env_def,env_to_list_def,LET_THM,s_frame_key_eq_def])>>
    fsrw_tac[][state_component_equality]>>
    qpat_x_assum`A=SOME t2` mp_tac>>
    simp[stackSemTheory.gc_def]>>
    ntac 5 TOP_CASE_TAC>>fsrw_tac[][stackSemTheory.set_store_def]>>
    strip_tac>>rveq>>fsrw_tac[][]>>
    CONJ_TAC>- metis_tac[]>>
    CONJ_TAC>- simp[wf_fromAList,wf_union] >>
    CONJ_TAC>-
      (fs[stack_size_rel_def] >>
      CONJ_ASM1_TAC >- (imp_res_tac s_key_eq_push_env_locals_size >>
                  metis_tac[]) >>
      CONJ_ASM1_TAC >-
      (imp_res_tac dec_stack_length>>
      fsrw_tac[][LENGTH_DROP,LENGTH_TAKE_EQ]>>
      rfs[]>>
      simp[the_eqn] >>
      CASE_TAC >> simp[] >>
      fs[miscTheory.the_def,IS_SOME_EXISTS]) >>
      rpt (GEN_TAC ORELSE DISCH_TAC) >> gvs[stack_size_eq] >>
      gvs[the_eqn,TypeBase.case_eq_of ``:'a option``]) >>
    CONJ_TAC>- (
      fsrw_tac[][stack_rel_def,LET_THM]>>
      qpat_x_assum`abs_stack A B C D = E` mp_tac>>
      simp[DROP_APPEND,DROP_TAKE_NIL]>>
      Cases_on`x'`>>simp[abs_stack_def]>>
      ntac 4 TOP_CASE_TAC>>
      Cases_on`f'=0`>>fsrw_tac[][]>>
      srw_tac[][]
      >-
        (qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
        impl_tac>-
          (srw_tac[][]>-
            DECIDE_TAC>>
          `SUC (LENGTH s3.stack) - (s3.handler+1) =
           SUC(LENGTH s3.stack - (s3.handler+1))` by DECIDE_TAC>>
          fsrw_tac[][])>>
        `s3.handler+1 ≤ LENGTH x''` by
          (imp_res_tac abs_stack_IMP_LENGTH>>
          DECIDE_TAC)>>
        simp[LASTN_CONS])
      >>
        qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        fsrw_tac[][stack_rel_aux_def]>>
        simp[])>>
    `f' ≠ 0` by (CCONTR_TAC>>fsrw_tac[][]>>DECIDE_TAC)>>
    fsrw_tac[][]>>rfs[]>>
    fsrw_tac[][stack_rel_def,LET_THM]>>
    qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
    qpat_x_assum`A = SOME stack'''` mp_tac>>
    fsrw_tac[][stack_rel_def,LET_THM,DROP_APPEND,DROP_TAKE_NIL]>>
    Cases_on`DROP t5.stack_space t5.stack`>>fsrw_tac[][]
    >- (fsrw_tac[] [DROP_NIL,DECIDE ``m>=n<=>n<=m:num``] \\ `F` by decide_tac)>>
    qpat_x_assum`A=SOME x'`mp_tac>>
    simp[stackSemTheory.dec_stack_def]>>
    rpt TOP_CASE_TAC>>strip_tac>>rveq
    >-
      simp[abs_stack_def,full_read_bitmap_def]>>
    fsrw_tac[][abs_stack_def,LET_THM]>>
    TOP_CASE_TAC>>simp[]>>
    strip_tac>>rveq>>
    simp[stack_rel_aux_def]>>
    ntac 3 strip_tac>>
    simp[lookup_union,AllCaseEqs(),lookup_fromAList_toAList]>>
    strip_tac
    >- (
      Cases_on`envs`>>
      pop_assum mp_tac>>
      qpat_x_assum`cut_envs _ _ = _` mp_tac>>
      simp[cut_envs_def,cut_names_def,AllCaseEqs()]>>
      strip_tac>>gvs[]>>
      simp[lookup_inter,AllCaseEqs()]>>
      strip_tac>>
      `n ∈ domain (FST names)` by metis_tac[domain_lookup]>>
      first_x_assum drule>>
      first_x_assum drule>>
      simp[]>>
      strip_tac>>
      first_x_assum(qspecl_then [`n`,`v`] mp_tac)>>
      gvs[lookup_fromAList,ALOOKUP_toAList]>>
      simp[lookup_inter]>>strip_tac>>
      drule ALOOKUP_MEM>>
      strip_tac>>
      simp[LLOOKUP_THM]>>
      imp_res_tac MEM_index_list_EL>>
      pop_assum mp_tac>>
      simp[LENGTH_TAKE]>>
      gvs[]>>
      ntac 2 strip_tac>>
      `k + LENGTH x'' - n DIV 2 =
        SUC ( k+ LENGTH x'' - (n DIV 2 +1))` by
        DECIDE_TAC>>
      simp[])
    >- (
      Cases_on`envs`>>
      qpat_x_assum`cut_envs _ _ = _` mp_tac>>
      simp[cut_envs_def,cut_names_def,AllCaseEqs()]>>
      strip_tac>>gvs[]>>
      `n ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
      `n ∈ domain (union (FST names) (SND names)) ∧ n ∈ domain s.locals` by (
        qpat_x_assum`_ ∪ _ = _`mp_tac>>
        simp[EXTENSION,domain_inter,domain_union]>>
        disch_then(qspec_then`n` mp_tac)>>
        (* TODO: metis_tac fails without the abbrev *)
        qmatch_goalsub_abbrev_tac`P ∧ Q ∨ P ∧ R`>>
        metis_tac[]) >>
      `EVEN n ∧ k ≤ n DIV 2` by gvs[domain_union]>>
      simp[]>>
      qpat_x_assum`n ∈ domain s.locals` mp_tac>>
      simp[domain_lookup]>>
      strip_tac>>
      first_x_assum drule>>
      simp[]>>
      fsrw_tac[][domain_lookup,lookup_fromAList]>>
      `MEM (n,v) l` by metis_tac[ALOOKUP_MEM]>>
      `MEM (n DIV 2,v) (MAP_FST adjust_names l)` by
        (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
        metis_tac[])>>
      simp[LLOOKUP_THM]>>
      qpat_abbrev_tac`ls = TAKE A B`>>
      imp_res_tac filter_bitmap_MEM>>
      imp_res_tac MEM_index_list_EL>>
      fsrw_tac[][Abbr`ls`]>>
      pop_assum mp_tac>>
      simp[LENGTH_TAKE]>>
      gvs[]>>
      ntac 2 strip_tac>>
      `k + LENGTH x'' - n DIV 2 =
        SUC ( k+ LENGTH x'' - (n DIV 2 +1))` by
        DECIDE_TAC>>
      simp[]))
  \\ `s3.store SUBMAP t2.store` by (
    fsrw_tac[] [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM] \\ NO_TAC)
  \\ gvs[AllCaseEqs(),get_store_def]
  \\ drule_all FLOOKUP_SUBMAP \\ simp[]
  \\ gvs[has_space_def,AllCaseEqs(),stackSemTheory.has_space_def,get_store_def]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fsrw_tac[] []
  \\ fsrw_tac[] [state_rel_def]
QED

Triviality word_gc_empty_frame:
  gc (s with stack:= (StackFrame n [] [] NONE::s.stack)) = SOME x ∧
  pop_env x = SOME y ⇒
  y.locals = LN ∧
  gc s = SOME (y with <|locals:=s.locals; locals_size:=s.locals_size|>)
Proof
  fs[gc_def,enc_stack_def,dec_stack_def,LET_THM]>>EVERY_CASE_TAC>>
  rw[]>>fs[pop_env_def]>>
  rveq>>fs[fromAList_def]>>
  rw[]>>rveq>>fs[pop_env_def]>>
  fs[state_component_equality]
QED

Triviality inter_eq_empty_2:
  domain t = {} ⇒
  inter s t = LN
Proof
  rw[inter_eq_LN]
QED

Triviality alloc_IMP_alloc2:
  (wordSem$alloc c names (s:('a,num # 'c,'ffi) wordSem$state) = (res:'a result option,s1)) ∧
  state_rel ac k 0 0 s t lens 0 ∧
  domain (FST names) = {} ∧
  domain (SND names) = {} ∧
  res ≠ SOME Error ⇒
  ∃(t1:('a,'c,'ffi) stackSem$state) res1.
    (stackSem$alloc c t = (res1:'a stackSem$result option,t1)) ∧
    if res = NONE then
      res1 = NONE ∧
      state_rel ac k 0 0 s1 t1 lens 0 /\
      LENGTH t1.stack = LENGTH t.stack /\
      t1.stack_space = t.stack_space
    else
      res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) ∧
      s1.clock = t1.clock /\ s1.ffi = t1.ffi
Proof
  Cases_on `FST (alloc c names (s:('a,num # 'c,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fs [] \\ rfs [])
  \\ fs [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fs [push_env_set_store]
  \\ imp_res_tac state_rel_set_store_0
  \\ pop_assum (mp_tac o Q.SPEC `Word c`)
  \\ REPEAT STRIP_TAC>>
  qpat_x_assum`A=(res,s1)` mp_tac>>
  ntac 2 TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  qmatch_asmsub_abbrev_tac`gc A = SOME _`>>
  qabbrev_tac`B = A with stack:= s.stack`>>
  `A = B with <|stack:=StackFrame (s.locals_size) [] [] NONE::B.stack|>` by (
    unabbrev_all_tac>>
    fs[state_component_equality,set_store_def]>>
    fs [set_store_def,push_env_def,LET_THM,env_to_list_def]>>
    gvs[cut_envs_def,cut_names_def,AllCaseEqs()]>>
    DEP_REWRITE_TAC[inter_eq_empty_2]>>
    simp[]>>
    EVAL_TAC)>>
  fs[]>>
  drule_all word_gc_empty_frame>> strip_tac>>
  drule (GEN_ALL gc_state_rel)>>
  disch_then(qspecl_then [`set_store AllocSize (Word c) t`,`lens`,`k`,`ac`] mp_tac)>>
  impl_tac>- (
    fs[markerTheory.Abbrev_def,state_component_equality,set_store_def,push_env_def,state_rel_def,LET_THM,env_to_list_def,lookup_def]>>
    fs[FUN_EQ_THM,wf_def]>>
    conj_tac >- metis_tac[] >>
    fs[stack_size_rel_def,stack_size_eq] >>
    rpt (GEN_TAC ORELSE DISCH_TAC) >> fs[] >>
    gvs[MAX_DEF]) >>
  rw[]>>
  fs[]>>
  rename1`isEmpty xx.locals`>>
  pop_assum mp_tac>>
  ntac 2 TOP_CASE_TAC>>fs[]
  \\ `xx.store SUBMAP t2.store` by
    fs [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ fs [has_space_def,stackSemTheory.has_space_def]
  \\ gvs[AllCaseEqs(),get_store_def]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ TOP_CASE_TAC>>fs[]
  \\ rw []
  \\ fs [state_rel_def,flush_state_def]
  \\ conj_tac >- metis_tac[]
  \\ fs[stack_size_rel_def]
  \\ fs[IS_SOME_EXISTS,markerTheory.Abbrev_def,set_store_const,set_store_def,pop_env_def,
        CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"]
  \\ rw[] \\ rveq \\ fs[]
  \\ imp_res_tac gc_const
  \\ fs[push_env_def,ELIM_UNCURRY,stack_size_eq]
  \\ fs[gc_def,dec_stack_def,CaseEq"option",CaseEq"prod",CaseEq"bool"]
  \\ rveq
  \\ fs[push_env_def,ELIM_UNCURRY,stack_size_eq]
  \\ rveq
  \\ fs[dec_stack_def,CaseEq"option",CaseEq"prod",CaseEq"bool"]
  \\ fs[state_component_equality] >> rveq >> fs[]
  \\ imp_res_tac dec_stack_stack_size
  \\ fs[]
QED

Definition compile_result_def:
  (compile_result (Result w1 w2) = Result w1) ∧
  (compile_result (Exception w1 w2) = Exception w1) ∧
  (compile_result TimeOut = TimeOut) ∧
  (compile_result NotEnoughSpace = Halt (Word 1w)) ∧
  (compile_result (FinalFFI f) = FinalFFI f) ∧
  (compile_result Error = Error)
End
val _ = export_rewrites["compile_result_def"];

Triviality Halt_EQ_compile_result:
  (Halt (Word 1w) = compile_result z <=> z = NotEnoughSpace) /\
    (good_dimindex (:'a) ==> Halt (Word (2w:'a word)) <> compile_result z)
Proof
  Cases_on `z` \\ fs [] \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]
QED

val stack_evaluate_add_clock_NONE =
  stackPropsTheory.evaluate_add_clock
  |> Q.SPECL [`p`,`s`,`NONE`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL

(* TODO: this is used for exceptions. Not quite right *)
Definition push_locals_def:
  push_locals cs s = s with <| locals := LN; locals_size := SOME 0;
    stack := StackFrame s.locals_size
      (FST (env_to_list (difference s.locals cs) (K I)))
      (FST (env_to_list (inter s.locals cs) (K I))) NONE :: s.stack |>
End

Triviality stack_rel_aux_LENGTH:
  ∀k len xs ys.
  stack_rel_aux k len xs ys ⇒
  LENGTH xs = LENGTH ys
Proof
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>fs[stack_rel_aux_def]
QED


Triviality stack_rel_aux_LASTN:
  ∀k len xs ys n.
  stack_rel_aux k len xs ys ⇒
  stack_rel_aux k len (LASTN n xs) (LASTN n ys)
Proof
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>
  fs[stack_rel_aux_def]>>rw[]>>
  imp_res_tac stack_rel_aux_LENGTH
  >-
    fs[LASTN_def,stack_rel_aux_def]
  >>
    rename1 `LASTN m`>>
    Cases_on`m ≤ LENGTH xs`>>rfs[LASTN_CONS]>>
    `¬(m < SUC(LENGTH ys))` by DECIDE_TAC>>
    fs[LASTN_MORE,stack_rel_aux_def]
QED

Triviality abs_stack_to_stack_LENGTH:
  ∀bs wstack sstack lens stack.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val stack = LENGTH sstack
Proof
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
  fs[abs_stack_def,LET_THM]>>TRY(Cases_on`w`)>>
  fs[full_read_bitmap_def]
  >-
    (pop_assum sym_sub_tac>>fs[handler_val_def])
  >-
    (pop_assum mp_tac>>
    ntac 4 TOP_CASE_TAC>>fs[]>>rw[]>>
    simp[handler_val_def])
  >>
    (pop_assum mp_tac>>
    ntac 7 TOP_CASE_TAC>>fs[]>>
    rw[]>>
    simp[handler_val_def])
QED

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
*)
Triviality abs_stack_prefix_drop:
  ∀bs wstack sstack lens stack h wrest k len.
  h ≤ LENGTH wstack ∧
  LASTN h wstack = wrest ∧
  abs_stack bs wstack sstack lens = SOME stack ∧
  stack_rel_aux k len wstack stack ⇒
  let rest = LASTN h stack in
  let lrest = LASTN h lens in
  let srest = LASTN (handler_val rest) sstack in
  abs_stack bs wrest srest lrest = SOME rest ∧
  stack_rel_aux k len wrest rest
Proof
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  rpt strip_tac>>fs[LET_THM,abs_stack_def]
  >-
    (fs[LASTN_def,handler_val_def]>>
    rveq>>
    fs[abs_stack_def,handler_val_def])
  >-
    (qpat_x_assum`A=SOME stack'`mp_tac>>
    Cases_on`w`>>fs[full_read_bitmap_def]>>
    ntac 4 TOP_CASE_TAC>>fs[]>>
    strip_tac>>rveq>>
    imp_res_tac abs_stack_IMP_LENGTH>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]
    >-
      (fs[LASTN_CONS,stack_rel_aux_def]>>
      first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
      res_tac>>
      fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_x_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>>AP_TERM_TAC>>
      qpat_abbrev_tac`lengt = handler_val A`>>
      Q.ISPECL_THEN [`lengt`,`DROP(LENGTH x)stack`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      simp[LASTN_DROP2,DROP_DROP]>>
      AP_THM_TAC>>
      AP_TERM_TAC>>DECIDE_TAC)
    >>
      qpat_abbrev_tac`frame = (a,x,TAKE A B)`>>
      `h = LENGTH (frame::x')` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      `LASTN (handler_val (frame::x')) (Word c::stack) = Word c::stack` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`frame`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      fs[Abbr`frame`,abs_stack_def,LET_THM,full_read_bitmap_def])
  >>
    qpat_x_assum`A=SOME stack'` mp_tac>>
    ntac 7 TOP_CASE_TAC>>
    PairCases_on`v0`>>
    fs[stack_rel_aux_def]>>
    strip_tac>>rveq>>
    imp_res_tac abs_stack_IMP_LENGTH>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]
    >-
      (fs[LASTN_CONS,stack_rel_aux_def]>>
      res_tac>>
      fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_x_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>> AP_TERM_TAC>>
      qpat_abbrev_tac`lengt = handler_val A`>>
      Q.ISPECL_THEN [`lengt`,`DROP(LENGTH x)t`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      simp[LASTN_DROP2,DROP_DROP]>>
      AP_THM_TAC>>
      AP_TERM_TAC>>DECIDE_TAC)
    >>
      qpat_abbrev_tac`frame = (a,x,TAKE A B)`>>
      `h = LENGTH (frame::x')` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      qpat_abbrev_tac`ls=Word 1w::A`>>
      `LASTN (handler_val (frame::x')) ls = ls` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`ls`,Abbr`frame`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      fs[Abbr`frame`,Abbr`ls`,abs_stack_def,LET_THM,full_read_bitmap_def]
QED

Triviality abs_stack_len:
  ∀bs wstack sstack lens stack handler.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val (LASTN handler stack) ≤ LENGTH sstack
Proof
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
  fs[abs_stack_def,LET_THM]
  >-
    (rveq>>fs[LASTN_def,handler_val_def])
  >>
    (pop_assum mp_tac>>rpt TOP_CASE_TAC>>fs[]>>
    rw[]>>
    Cases_on`handler ≤ LENGTH x'`
    >-
      (fs[LASTN_CONS]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      DECIDE_TAC)
    >>
      fs[]>>qpat_abbrev_tac`frame = (a,b,c)`>>
      `¬(handler < LENGTH (frame::x'))` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE,Abbr`frame`,handler_val_def]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      `¬(handler < LENGTH x')` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE]>>rw[]>>
      fs[LENGTH_TAKE_EQ]>>IF_CASES_TAC>>
      DECIDE_TAC)
QED

Triviality EL_REVERSE_REWRITE:
  ∀l n k. n < LENGTH l ∧ k < n ⇒
  EL (LENGTH l - n + k) l = EL (n-k -1) (REVERSE l)
Proof
  rw[]>> fs[EL_REVERSE,PRE_SUB1]
QED

Triviality LASTN_LESS:
  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs
Proof
  Induct>>rw[]>>
  Cases_on`n+1 ≤ LENGTH ls`>>fs[]
  >-
    (fs[LASTN_CONS]>>
    res_tac>>fs[]>>
    `n ≤ LENGTH ls` by (fs[]>>decide_tac)>>
    fs[LASTN_CONS])
  >>
  `n = LENGTH ls` by DECIDE_TAC>>
  `n+1 = LENGTH (h::ls)` by (fs[]>>DECIDE_TAC)>>
  imp_res_tac LASTN_LENGTH_ID2>>
  fs[LASTN_CONS]
QED

Triviality ALOOKUP_IFF_MEM:
  ALL_DISTINCT (MAP FST l) ==>
    (ALOOKUP l q = SOME r <=> MEM (q,r) l)
Proof
  Induct_on `l` \\ fs [FORALL_PROD,MEM_MAP] \\ rw [] \\ metis_tac []
QED

Triviality SORTED_CONS_IMP:
  SORTED (\x y. FST x > (FST y):num) (h::t) ==>
    ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
    !x. MEM x t ==> FST h > FST x
Proof
  Induct_on `t` \\ fs [SORTED_DEF] \\ rw []
  \\ `SORTED (\x y. FST x > FST y) (h::t)` by
    (Cases_on `t` \\ fs [SORTED_DEF] \\ decide_tac)
  \\ fs [] \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ disj1_tac \\ decide_tac
QED

Triviality SORTED_IMP_ALL_DISTINCT_LEMMA:
  !l. SORTED (\x y. FST x > (FST y):num) l ==> ALL_DISTINCT (MAP FST l)
Proof
  Induct \\ fs [] \\ rw [MEM_MAP]
  \\ metis_tac [DECIDE ``m>n ==> m<>n:num``,SORTED_CONS_IMP]
QED

Triviality MEM_toAList_fromAList:
  SORTED (\x y. FST x > (FST y):num) l ==>
    MEM a (toAList (fromAList l)) = MEM a l
Proof
  Cases_on `a` \\ fs [MEM_toAList,lookup_fromAList] \\ rw []
  \\ imp_res_tac SORTED_IMP_ALL_DISTINCT_LEMMA \\ fs [ALOOKUP_IFF_MEM]
QED

Triviality SORTED_FST_PERM_IMP_ALIST_EQ:
  SORTED (\x y. FST x > FST y) l /\
  SORTED (\x y. FST x > FST y) q /\
  PERM (toAList (fromAList l)) q ==>
  q = l
Proof
  rw [] \\ drule MEM_PERM \\ fs [MEM_toAList_fromAList]
  \\ pop_assum kall_tac \\ rpt (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Induct_on `q` \\ fs [MEM]
  THEN1 (Cases \\ fs[] \\ metis_tac [])
  \\ Cases_on `l` THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rw []
  \\ imp_res_tac SORTED_CONS_IMP
  \\ `!m n:num. m > n /\ n > m ==> F` by decide_tac
  \\ metis_tac []
QED

Theorem inter_union_left:
  wf s ⇒
  inter (union s t) s = s
Proof
  rw[]>>DEP_REWRITE_TAC[spt_eq_thm]>>
  simp[lookup_inter,lookup_union,AllCaseEqs()]>>
  metis_tac[option_CLAUSES]
QED

(* TODO: This isn't quite right ... *)
Triviality stack_rel_raise:
  n ≤ LENGTH sstack /\
  handler+1 ≤ LENGTH wstack /\ SORTED (\x y. FST x > FST y) l /\
  LASTN (handler + 1) wstack = StackFrame m l0 l (SOME (h1,l3,l4))::rest /\
  abs_stack bs wstack (DROP n sstack) lens = SOME stack /\
  stack_rel_aux k (LENGTH sstack) wstack stack ==>
  ?ex payload.
    LASTN (handler+1) stack = (SOME ex,payload) :: LASTN handler stack /\
    3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler+1) stack) /\
    EL (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 1)
          sstack = Loc l3 l4 /\
    ((h1 < LENGTH rest /\
    is_handler_frame (EL (LENGTH rest - (h1+1)) rest) ⇒
    EL (LENGTH sstack − handler_val (LASTN (handler+1) stack) + 2) sstack =
        Word (n2w
          (LENGTH sstack - handler_val (LASTN (h1+1) (LASTN (handler+1) stack)))))) /\
    stack_rel_aux k (LENGTH sstack)
      (StackFrame m
        (FST (env_to_list (difference (union (fromAList l) (fromAList l0)) (fromAList l)) (K I)))
        (FST (env_to_list (inter (union (fromAList l) (fromAList l0)) (fromAList l)) (K I))) NONE::rest)
          ((NONE,payload) :: LASTN handler stack) /\
    abs_stack bs
      (StackFrame m
        (FST (env_to_list (difference (union (fromAList l) (fromAList l0)) (fromAList l)) (K I)))
        (FST (env_to_list (inter (union (fromAList l) (fromAList l0)) (fromAList l)) (K I))) NONE::rest)
      (DROP (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 3)
         sstack) (LASTN (handler+1) lens) = SOME ((NONE,payload) :: LASTN handler stack)
Proof
  rw[]>>
  imp_res_tac abs_stack_prefix_drop>>
  fs[LET_THM]>>
  Cases_on`LASTN (handler+1) stack`>>fs[stack_rel_aux_def]>>
  PairCases_on`h`>>Cases_on`h0`>>fs[stack_rel_aux_def]>>
  PairCases_on`x`>>fs[stack_rel_aux_def]>>
  DEP_REWRITE_TAC[inter_union_left]>>
  simp[wf_fromAList]>>
  `FST (env_to_list (fromAList l) (K I)) = l` by
   (Cases_on `env_to_list (fromAList l) (K I)` \\ fs []
    \\ imp_res_tac env_to_list_K_I_IMP \\ rw []
    \\ metis_tac [SORTED_FST_PERM_IMP_ALIST_EQ]) >>
  imp_res_tac abs_stack_IMP_LENGTH>>fs[]>>
  CONJ_TAC>- fs[LASTN_LESS]>>
  imp_res_tac abs_stack_len>>
  fs[handler_val_def]>>
  CONJ_ASM1_TAC>- (
    qhdtm_x_assum `abs_stack` mp_tac>>
    Cases_on`LASTN (handler+1) lens`>>fs[]>>
    (*The DROP must have length ≥ 3*)
    Cases_on`DROP n sstack`>>simp[abs_stack_def,LASTN_def]>>
    Cases_on`t''`>>simp[abs_stack_def]>>
    Cases_on`t'''`>>simp[abs_stack_def]>>
    `3 ≤ LENGTH (DROP n sstack)` by
      (pop_assum SUBST_ALL_TAC>>
      simp[])>>
    Q.ISPECL_THEN [`n`,`sstack`] assume_tac LENGTH_DROP >>
    `LENGTH (DROP n sstack) ≤ LENGTH sstack` by DECIDE_TAC>>
    simp[])>>
  qhdtm_x_assum `abs_stack` mp_tac>>
  qpat_abbrev_tac`ls = LASTN A B`>>
  qpat_abbrev_tac`lens' = LASTN A lens`>>
  strip_tac>>
  simp[LASTN_CONS]>>
  qpat_abbrev_tac`w = Word A`>>
  qpat_abbrev_tac`preconds = (h1 < LENGTH rest ∧ B)`>>
  `EL 1 ls = Loc l3 l4 ∧ (preconds ⇒ EL 2 ls = w)` by
    (qhdtm_x_assum`abs_stack` mp_tac>>
    Cases_on`lens'`>>fs[]>>
    Cases_on`ls`>-simp[abs_stack_def]>>
    Cases_on`h'`>>simp[abs_stack_def,LET_THM]>>
    ntac 7 TOP_CASE_TAC>>fs[])>>
  fs[Abbr`ls`,LASTN_DROP2]>>
  qpat_abbrev_tac`offset = (LENGTH _ + (_ + 4))`>>
  (*Using DROP_DROP and more assumptions on the lengths*)
  `n + offset ≤ LENGTH sstack` by
    (first_x_assum(qspec_then`handler+1` mp_tac)>>
    simp[handler_val_def,Abbr`offset`])>>
  `DROP (LENGTH sstack - n - offset) (DROP n sstack) =
   DROP (LENGTH sstack - offset) sstack` by
     simp[DROP_DROP]>>
  `EL 1 (DROP (LENGTH sstack - offset) sstack) = Loc l3 l4 ∧
   (preconds ⇒ EL 2 (DROP (LENGTH sstack - offset) sstack) = w)` by fs[]>>
  conj_asm1_tac >- (
    first_x_assum sym_sub_tac >>
    dep_rewrite.DEP_REWRITE_TAC[EL_DROP] >>
    simp[Abbr`offset`] ) >>
  conj_asm1_tac >- (
    rw[] >> fs[] >> rw[] >>
    dep_rewrite.DEP_REWRITE_TAC[EL_DROP] >>
    simp[Abbr`offset`] ) >>
  qpat_x_assum`DROP A stack = C` mp_tac>>
  qpat_x_assum`LENGTH stack =A` sym_sub_tac>>
  simp[GSYM LASTN_DROP2]>>
  strip_tac >> imp_res_tac LASTN_LESS>>
  simp[]>>
  qpat_x_assum`abs_stack A B C D = E` mp_tac>>
  simp[]>>
  qpat_abbrev_tac`ls = DROP A B`>>
  qpat_abbrev_tac`ls' = DROP A B`>>
  `ls' = DROP 3 ls` by
    (unabbrev_all_tac>>
    simp[DROP_DROP])>>
  Cases_on`lens'`>>
  Cases_on`ls`>>simp[abs_stack_def]>>
  Cases_on`t''`>>simp[]>>
  Cases_on`t'''`>>simp[]>>
  ntac 5 TOP_CASE_TAC>>
  rw[]>>
  fs[abs_stack_def,LET_THM]>>
  first_x_assum irule>>
  simp[]>>
  cheat
QED

Theorem insert_bitmap_isPREFIX:
   ∀bs bs' i.
   insert_bitmap bm bs = (bs',i) ⇒
   append (FST bs) ≼ append (FST bs')
Proof
  Cases>>simp[insert_bitmap_def]
QED

Theorem wLive_isPREFIX:
   ∀a bs c q bs'. wLive a bs c = (q,bs') ⇒
   append (FST bs) ≼ append (FST bs')
Proof
  rw[]
  \\ PairCases_on`c`
  \\ fs[wLive_def,LET_THM]
  \\ Cases_on`c1=0` \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ imp_res_tac insert_bitmap_isPREFIX
QED

Theorem comp_IMP_isPREFIX:
  ∀ac c1 bs r q1 bs'.
  comp ac c1 bs r = (q1,bs') ==> append (FST bs) ≼ append (FST bs')
Proof
  ho_match_mp_tac comp_ind
  \\ rw[comp_def,LET_THM]
  \\ every_case_tac \\ fs[]
  \\ rpt (pairarg_tac >> fs[])
  \\ rveq
  \\ metis_tac[IS_PREFIX_TRANS,wLive_isPREFIX,insert_bitmap_isPREFIX]
QED

Triviality compile_prog_isPREFIX:
  compile_prog ac x y k bs = (prog,fs,bs1) ==>
  append (FST bs) ≼ append (FST bs1)
Proof
  fs [compile_prog_def,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ imp_res_tac comp_IMP_isPREFIX
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
QED

Theorem compile_word_to_stack_isPREFIX:
  ∀code k bs progs1 fs1 bs1.
  compile_word_to_stack ac k code bs = (progs1,fs1,bs1) ==>
  append (FST bs) ≼ append (FST bs1)
Proof
  Induct \\ fs [compile_word_to_stack_def,FORALL_PROD,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ imp_res_tac compile_prog_isPREFIX
  \\ fs[]
  \\ Cases_on`bitmaps'` \\ fs[]
  \\ first_x_assum drule
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
QED

Theorem EVEN_DIV2_INJ:
   EVEN x ∧ EVEN y ∧ DIV2 x = DIV2 y ⇒ x = y
Proof
  srw_tac[][EVEN_EXISTS,DIV2_def,MULT_COMM]
  \\ fs[MULT_DIV]
QED

Theorem wMoveAux_thm:
   evaluate (wMoveAux [] kf,s) = (NONE,s) ∧
   evaluate (wMoveAux (x::xs) kf,s) =
   evaluate (Seq (wMoveSingle x kf) (wMoveAux xs kf), s)
Proof
  rw[wMoveAux_def] >- rw[stackSemTheory.evaluate_def]
  \\ Cases_on`xs` >> rw[wMoveAux_def]
  \\ rw[stackSemTheory.evaluate_def]
  \\ pairarg_tac
  \\ rw[]
QED

Theorem state_rel_get_var_imp:
  state_rel ac k f f' s t lens extra ∧
  get_var (2 * x) s = SOME v ∧
  x < k ⇒
  FLOOKUP t.regs x = SOME v
Proof
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ first_x_assum drule
  \\ simp[EVEN_MULT]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ rw[]
QED

Theorem state_rel_get_var_imp':
  state_rel ac k f f' s t lens extra ∧
  get_var n s = SOME v ∧
  EVEN n /\
  (n DIV 2) < k ⇒
  get_var (n DIV 2) t = SOME v
Proof
  rw[EVEN_EXISTS] >> fs[stackSemTheory.get_var_def] >>
  METIS_TAC[state_rel_get_var_imp]
QED

Theorem state_rel_get_var_imp2:
  state_rel ac k f f' s t lens 0 ∧
  get_var (2 * x) s = SOME v ∧
  ¬(x < k)
  ⇒
  (EL (t.stack_space + (f + k - (x + 1))) t.stack = v)
Proof
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ first_x_assum drule
  \\ simp[EVEN_MULT]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ simp[LLOOKUP_THM]
  \\ strip_tac
  \\ qhdtm_x_assum`EL`mp_tac
  \\ simp[EL_TAKE]
  \\ simp[EL_DROP]
  \\ simp[ADD_COMM]
QED

Theorem state_rel_set_var_k[simp]:
   (state_rel ac k f f' s (set_var (k+1) v t) lens extra ⇔
    state_rel ac k f f' s t lens extra) ∧
   (state_rel ac k f f' s (set_var k v t) lens extra ⇔
    state_rel ac k f f' s t lens extra)
Proof
  conj_tac
  \\ simp[state_rel_def,EQ_IMP_THM,stackSemTheory.set_var_def]
  \\ ntac 2 strip_tac
  \\ fs[FLOOKUP_UPDATE]
  \\ metis_tac[DECIDE``¬(k + 1n < k) ∧ ¬(k < k)``]
QED

Theorem state_rel_set_var:
    state_rel ac k f f' s t lens extra ∧
    x < k ⇒
    state_rel ac k f f' (set_var (2*x) v s) (set_var x v t) lens extra
Proof
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ strip_tac
  \\ fs[lookup_insert,FLOOKUP_UPDATE,wf_insert]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ strip_tac
  \\ Cases_on`x = n DIV 2` \\ simp[]
  \\ rveq
  \\ fs[bitTheory.DIV_MULT_THM2]
  \\ `EVEN n` by metis_tac[]
  \\ fs[EVEN_MOD2]
QED

Theorem state_rel_set_var':
    state_rel ac k f f' s t lens extra ∧
    x < k ∧ y = x * 2 ⇒
    state_rel ac k f f' (set_var y v s) (set_var x v t) lens extra
Proof
  simp[] >> METIS_TAC[state_rel_set_var]
QED


Theorem state_rel_set_var2:
  state_rel ac k f f' s t lens 0 ∧
  ¬(x < k) ∧ x < f' + k ∧ st = t.stack ∧ sp = t.stack_space ⇒
  state_rel ac k f f' (set_var (2*x) v s)
    (t with stack := LUPDATE v (sp + (f + k − (x + 1))) st) lens 0
Proof
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def,stack_size_rel_def]
  \\ strip_tac \\ rveq
  \\ fs[lookup_insert,FLOOKUP_UPDATE,wf_insert]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ `0<f` by
      (Cases_on`f'`>>fs[]>>DECIDE_TAC)
  \\ simp[DROP_LUPDATE]
  \\ CONJ_TAC >-  gvs[stack_rel_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    strip_tac \\ rveq \\
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV]
    \\ simp[LLOOKUP_THM]
    \\ simp[EL_LUPDATE])
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ IF_CASES_TAC >> fs[]
  \\ imp_res_tac LLOOKUP_TAKE_IMP
  \\ fs[LLOOKUP_DROP,LLOOKUP_LUPDATE]
  \\ fs[EVEN_EXISTS]
  \\ rfs[]
QED

val _ = get_time timer;

Theorem wMoveSingle_thm:
   state_rel ac k f f' s t lens 0 ∧
   (case x of NONE => get_var (k+1) t = SOME v
    | SOME x => get_var (x * 2) s = SOME v ) ∧
   (case y of SOME x => x < f' + k | _ => T)
   ⇒
   ∃t'.
     evaluate (wMoveSingle (format_var k y,format_var k x) (k,f,f'), t) = (NONE,t') ∧
     state_rel ac k f f' (case y of NONE => s | SOME y => set_var (y*2) v s) t' lens 0 ∧
     (y = NONE ⇒ get_var (k+1) t' = SOME v) ∧
     (y ≠ NONE ⇒ get_var (k+1) t' = get_var (k+1) t) /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  rw[wMoveSingle_def]
  \\ Cases_on`y` \\ simp[format_var_def]
  \\ Cases_on`x` \\ fs[format_var_def]
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    \\ fs[stackSemTheory.get_var_def]
    \\ fs[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    >- (
      imp_res_tac state_rel_get_var_imp
      \\ simp[] )
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC
    THEN1 (simp[]\\ imp_res_tac state_rel_get_var_imp2)
    \\
      fs[state_rel_def,LET_THM,get_var_def,TWOxDIV2]>>
      res_tac>>
      `x'*2 DIV 2 = x'` by metis_tac[TWOxDIV2,MULT_COMM]>>
      fs[]>>
      rfs[]>>
      Cases_on`f'`>>fs[])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    >- (
      fs[stackSemTheory.get_var_def]
      \\ conj_tac
      >- (match_mp_tac state_rel_set_var
          \\ simp[] )
      \\ simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE] )
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC >-
      (fs[state_rel_def,LET_THM]>>
      Cases_on`f'`>>fs[]>>
      `F` by DECIDE_TAC)
    \\ simp[]
    \\ conj_tac
    >- (
      match_mp_tac state_rel_set_var2
      \\ simp[])
    \\ fs[stackSemTheory.get_var_def])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    \\ TRY (
      imp_res_tac state_rel_get_var_imp \\ fs[]
      \\ conj_tac >- (
           match_mp_tac state_rel_set_var
          \\ simp[])
      \\ fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
      \\ rw[]
      \\ `F` by decide_tac)
    \\ (IF_CASES_TAC >- fs[state_rel_def])
    \\ IF_CASES_TAC
    \\
    TRY(
      fs[state_rel_def,LET_THM,get_var_def]>>
      res_tac>>
      `x''*2 DIV 2 = x''` by metis_tac[MULT_COMM,TWOxDIV2]>>
      fs[]>>rfs[]>>
      Cases_on`f'`>>fs[]>>
      `F` by DECIDE_TAC>>NO_TAC)
    \\ fs[]
    >- (
      imp_res_tac state_rel_get_var_imp2
      \\ reverse conj_tac
      >- (
        EVAL_TAC \\ rw[]
        \\ `F` by decide_tac )
      \\ rw[]
      \\ simp[]
      \\ match_mp_tac state_rel_set_var \\ simp[])
    >- (
      imp_res_tac state_rel_get_var_imp
      \\ fs[stackSemTheory.get_var_def]
      \\ simp[]
      \\ match_mp_tac state_rel_set_var2
      \\ simp[] )
    >- (
      IF_CASES_TAC
      >- (
        `F` suffices_by rw[]
        \\ fs[state_rel_def,LET_THM,wordSemTheory.get_var_def]
        \\ every_case_tac >> fs[]
        \\ rveq \\ fs[]
        \\ decide_tac )
      \\ rpt(qpat_x_assum`¬(_ < k)`mp_tac)
      \\ simp_tac (srw_ss()++ARITH_ss)[]
      \\ ntac 2 strip_tac
      \\ imp_res_tac state_rel_get_var_imp2
      \\ rveq
      \\ reverse conj_tac
      >- (
        EVAL_TAC \\ rw[]
        \\ `F` by decide_tac )
      \\ match_mp_tac state_rel_set_var2
      \\ simp[]))
QED

Theorem IS_SOME_get_vars_set_var:
   ∀ls s.
    IS_SOME (wordSem$get_vars ls s) ⇒
    IS_SOME (get_vars ls (set_var k v s))
Proof
  Induct \\ simp[get_vars_def]
  \\ rw[] \\ every_case_tac \\ fs[IS_SOME_EXISTS,PULL_EXISTS]
  \\ rpt (pop_assum mp_tac)
  \\ EVAL_TAC \\ simp[lookup_insert] \\ rw[]
  \\ res_tac \\ fs[]
QED

Theorem IS_SOME_get_vars_EVERY:
   ∀xs s.
     IS_SOME (wordSem$get_vars xs s) ⇔ EVERY (λx. IS_SOME (get_var x s)) xs
Proof
  Induct \\ simp[get_vars_def,EVERY_MEM]
  \\ rw[] \\ every_case_tac \\ fs[EVERY_MEM]
  \\ metis_tac[IS_SOME_EXISTS,NOT_SOME_NONE,option_CASES]
QED

Theorem with_same_locals[simp] =
  EQT_ELIM(SIMP_CONV(srw_ss())[state_component_equality]``s with locals := s.locals = (s:('a,'b,'c) wordSem$state)``)

Theorem evaluate_wMoveAux_seqsem:
   ∀ms s t r.
   state_rel ac k f f' s t lens 0 ∧
   (∀i v. r (SOME i) = SOME v ⇔ get_var (2*i) s = SOME v) ∧
   (∀v. r NONE = SOME v ⇒ get_var (k+1) t = SOME v) ∧
   IS_SOME (get_vars (MAP ($* 2 o THE) (FILTER IS_SOME (MAP SND ms))) s) ∧
   (case find_index NONE (MAP SND ms) 0 of
    | NONE => T
    | SOME i =>
      case find_index NONE (MAP FST ms) 0 of
      | NONE => IS_SOME (r NONE)
      | SOME j => i ≤ j ⇒ IS_SOME (r NONE)) ∧
   EVERY (λ(x,y). ∀a. (x = SOME a ∨ y = SOME a) ⇒ a < f' + k) ms ∧
   ALL_DISTINCT (FILTER IS_SOME (MAP FST ms))
   ⇒
   ∃t'.
     evaluate (wMoveAux (MAP (format_var k ## format_var k) ms) (k,f,f'),t) = (NONE,t') ∧
     state_rel ac k f f'
       (set_vars
         (MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
         (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
         s) t' lens 0 /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  Induct
  \\ simp[wMoveAux_thm]
  >- simp[set_vars_def,alist_insert_def]
  \\ qx_gen_tac`h`
  \\ rpt gen_tac
  \\ Cases_on`h`
  \\ strip_tac
  \\ simp[]
  \\ simp[stackSemTheory.evaluate_def]
  \\ drule (GEN_ALL wMoveSingle_thm)
  \\ simp[]
  \\ qpat_abbrev_tac`wms = wMoveSingle _`
  \\ qmatch_assum_abbrev_tac`_ (y,x)`
  \\ disch_then(qspecl_then[`y`,`x`]mp_tac)
  \\ unabbrev_all_tac
  \\ fs[]
  \\ qho_match_abbrev_tac`(∀v. P v ⇒ Q v) ⇒ _`
  \\ `∃v. P v`
  by (
    simp[Abbr`P`,Abbr`Q`]
    \\ simp[LEFT_EXISTS_AND_THM]
    \\ conj_tac
    >- (
      BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (
        `IS_SOME (r NONE)` suffices_by metis_tac[IS_SOME_EXISTS]
        \\ fs[find_index_def]
        \\ BasicProvers.FULL_CASE_TAC \\ fs[]
        \\ BasicProvers.FULL_CASE_TAC \\ fs[])
      \\ fs[get_vars_def]
      \\ pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[] )
  \\ simp[Abbr`P`,Abbr`Q`] \\ fs[]
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ simp[parmoveTheory.seqsem_def]
  \\ first_x_assum drule
  \\ qpat_abbrev_tac`rr = (_ =+ r _) _`
  \\ disch_then(qspec_then`rr`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`rr`,APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      rw[]
      >- (
        EVAL_TAC
        \\ simp[lookup_insert]
        \\ fs[]
        \\ BasicProvers.FULL_CASE_TAC \\ fs[]
        \\ rw[EQ_IMP_THM]
        \\ fs[find_index_def]
        \\ BasicProvers.FULL_CASE_TAC \\ fs[IS_SOME_EXISTS])
      \\ BasicProvers.FULL_CASE_TAC \\ fs[]
      \\ EVAL_TAC
      \\ simp[lookup_insert]
      \\ fs[get_var_def] )
    \\ conj_tac
    >- (
      rw[] \\ fs[] \\ rw[]
      \\ BasicProvers.FULL_CASE_TAC \\ fs[]
      \\ res_tac
      \\ fs[] )
    \\ conj_tac
    >- (
      qpat_x_assum`IS_SOME _`mp_tac
      \\ reverse IF_CASES_TAC \\ fs[get_vars_def]
      >- (
        BasicProvers.CASE_TAC \\ simp[]
        \\ metis_tac[IS_SOME_get_vars_set_var] )
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ metis_tac[IS_SOME_get_vars_set_var,IS_SOME_EXISTS])
    \\ reverse conj_tac
    >- (
      qhdtm_x_assum`ALL_DISTINCT`mp_tac
      \\ IF_CASES_TAC \\ simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ qpat_x_assum`option_CASE (find_index _ _ _) _ _`mp_tac
    \\ simp[find_index_def]
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC \\ rw[]
    >- (BasicProvers.TOP_CASE_TAC \\ fs[])
    >- (
      pop_assum mp_tac
      \\ simp[Once find_index_shift_0]
      \\ strip_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[] )
    >- (
      fs[]
      \\ qmatch_assum_rename_tac`ss ≠ NONE`
      \\ Cases_on`r ss`
      \\ Cases_on`ss`\\ fs[]
      \\ BasicProvers.CASE_TAC \\ fs[]
      \\ res_tac \\ fs[])
    >- (
      pop_assum mp_tac
      \\ simp[Once find_index_shift_0]
      \\ simp[Once find_index_shift_0]
      \\ strip_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[] ))
  \\ strip_tac
  \\ simp[]
  \\ qhdtm_x_assum `state_rel` mp_tac
  \\ qmatch_abbrev_tac`a ⇒ b`
  \\ `a = b` suffices_by rw[]
  \\ unabbrev_all_tac
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[set_vars_def]
  \\ simp[state_component_equality,set_var_def]
  \\ BasicProvers.CASE_TAC \\ simp[] \\ fs[FILTER_APPEND]
  \\ simp[alist_insert_append]
  \\ simp[alist_insert_def]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ qpat_abbrev_tac`rr = _ r`
  \\ qispl_then[`SOME x`,`ms`,`rr`]mp_tac (Q.GEN`k`seqsem_move_unchanged)
  \\ impl_tac >- ( fs[MEM_FILTER] )
  \\ simp[] \\ disch_then kall_tac
  \\ simp[Abbr`rr`,APPLY_UPDATE_THM]
  \\ fs[find_index_def]
  \\ BasicProvers.FULL_CASE_TAC \\ fs[]
  >- (
    BasicProvers.FULL_CASE_TAC \\ fs[IS_SOME_EXISTS]
    \\ BasicProvers.FULL_CASE_TAC \\ fs[] )
  \\ qmatch_rename_tac`v = THE (r z)`
  \\ Cases_on`z` \\ fs[]
  \\ res_tac \\ fs[]
QED

Theorem evaluate_SeqStackFree:
   s.use_stack /\ s.stack_space <= LENGTH s.stack ==>
    evaluate (SeqStackFree n p,s) = evaluate (Seq (StackFree n) p,s)
Proof
  RW_TAC std_ss [SeqStackFree_def,stackSemTheory.evaluate_def]
  THEN1 (`F` by decide_tac)
  \\ AP_TERM_TAC \\ fs [stackSemTheory.state_component_equality]
QED

Theorem get_vars_eq[local]:
  ∀ls z.
    get_vars ls st = SOME z ⇒
    let lookups = MAP (\x. lookup x st.locals) ls in
      EVERY IS_SOME lookups ∧
      z = MAP THE lookups
Proof
  Induct>>fs[get_vars_def,get_var_def]>>rw[]>>unabbrev_all_tac>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[]
QED

Theorem LAST_add_ret_loc[local]:
  args' ≠ [] ⇒
  LAST (add_ret_loc ret args') = LAST args'
Proof
  Cases_on`ret`>>TRY(PairCases_on`x`)>>fs[add_ret_loc_def]>>
  Cases_on`args'`>>fs[LAST_CONS]
QED

Theorem call_dest_lemma[local]:
  ¬bad_dest_args dest args /\
  state_rel ac k f f' (s:('a,num # 'c,'ffi) state) t lens 0 /\
  call_dest dest args (k,f,f') = (q0,dest') /\
  get_vars args s = SOME args' ==>
  ?t4:('a,'c,'ffi) stackSem$state.
    evaluate (q0,t) = (NONE,t4) /\
    state_rel ac k f f' s t4 lens 0 /\
    LENGTH t4.stack = LENGTH t.stack /\
    t4.stack_space = t.stack_space /\
    !real_args prog ssize.
      find_code dest
                (add_ret_loc (ret:(num list # (cutsets) # 'a wordLang$prog#num#num)option)
                             args':'a word_loc list)
                s.code s.stack_size = SOME (real_args,prog,ssize) ==>
      ?bs i bs2 i2 fs stack_prog.
        compile_prog ac prog (LENGTH real_args) k (bs,i) = (stack_prog,fs,(bs2,i2)) ∧
        LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH t.bitmaps /\
        isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) t.bitmaps) ∧
        the fs ssize = fs ∧
        find_code dest' t4.regs t4.code = SOME stack_prog
Proof
  Cases_on`dest`>>fs[call_dest_def,bad_dest_args_def,LENGTH_NIL]>>rw[]
  >- (
    fs[wReg2_def,TWOxDIV2,LET_THM]>>
    pairarg_tac>>fs[]>>rveq>>
    EVERY_CASE_TAC>>rw[]
    >- (
      fs[wStackLoad_def,stackSemTheory.evaluate_def,state_rel_def]>>
      CONJ_TAC>-
        metis_tac[]>>
      fs[find_code_def,stackSemTheory.find_code_def]>>
      rw[]>>
      pop_assum mp_tac>>
      ntac 4 TOP_CASE_TAC>>rw[]>>
      imp_res_tac get_vars_length_lemma>>
      `args' ≠ []` by metis_tac[LENGTH_NIL]>>
      fs[LAST_add_ret_loc]>>
      res_tac>>
      simp[LENGTH_FRONT,PRE_SUB1]>>
      `lookup (LAST args) s.locals = SOME (LAST args')` by
        (imp_res_tac get_vars_eq>>
        fs[LET_THM,LAST_MAP,MAP_MAP_o]>>
        `IS_SOME (lookup (LAST args) s.locals)` by
          (Cases_on`args`>>
          FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP]>>
          metis_tac[MEM_LAST])>>
        qpat_x_assum`A=Loc n 0` sym_sub_tac>>
        simp[LAST_MAP,option_CLAUSES])>>
      qexists_tac`bs`>>fs[LET_THM]>>
      res_tac>>
      qpat_x_assum`if A then B else C` mp_tac>>
      IF_CASES_TAC>>fs[]>>
      strip_tac>>qexists_tac`i`>>simp[])
    >>
      rw[stackSemTheory.evaluate_def,wStackLoad_def]>>
      TRY(fs[state_rel_def] \\ `F` by decide_tac)
      >- (
        fs[find_code_def,stackSemTheory.find_code_def,state_rel_def]>>
        rw[]>>
        ntac 2 (pop_assum mp_tac)>>
        ntac 4 TOP_CASE_TAC>>rw[]>>
        imp_res_tac get_vars_length_lemma>>
        `args' ≠ []` by metis_tac[LENGTH_NIL]>>
        fs[LAST_add_ret_loc]>>
        res_tac>>
        simp[LENGTH_FRONT,PRE_SUB1]>>
        `lookup (LAST args) s.locals = SOME (LAST args')` by
          (imp_res_tac get_vars_eq>>
          fs[LET_THM,LAST_MAP,MAP_MAP_o]>>
          `IS_SOME (lookup (LAST args) s.locals)` by
            (Cases_on`args`>>
            FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP]>>
            metis_tac[MEM_LAST])>>
          qpat_x_assum`A=Loc n 0` sym_sub_tac>>
          simp[LAST_MAP,option_CLAUSES])>>
        qexists_tac`bs`>>fs[LET_THM]>>
        res_tac>>
        qpat_x_assum`if A then B else C` mp_tac>>
        IF_CASES_TAC>>fs[]>>
        simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE,LLOOKUP_THM]>>
        `k < LAST args DIV 2 +1` by DECIDE_TAC>>
        rw[]>>
        `f + k - (LAST args DIV 2 +1) <f` by simp[]>>
        qpat_x_assum`A=Loc n 0` mp_tac>>
        simp[EL_DROP,EL_TAKE]>>
        fs[]>>
        strip_tac>>qexists_tac`i`>>simp[]) >>
      imp_res_tac get_vars_eq>>
      fs[state_rel_def,LET_THM]>>
      `∃x.lookup (LAST args) s.locals = SOME x` by
        (fs[LAST_EL,EVERY_EL,EL_MAP,IS_SOME_EXISTS]>>
        first_assum match_mp_tac>>
        Cases_on`args`>>fs[])>>
      res_tac>>fs[]>>
      pop_assum mp_tac>>
      IF_CASES_TAC>>fs[]>>
      Cases_on`f'`>>fs[]) >>
  fs[stackSemTheory.evaluate_def,state_rel_def]>>
  CONJ_TAC>-
    metis_tac[]>>
  fs[find_code_def,stackSemTheory.find_code_def]>>
  ntac 2 TOP_CASE_TAC>>rw[]>>
  res_tac>>
  simp[]>>
  metis_tac[]
QED

Triviality compile_result_NOT_2:
  good_dimindex (:'a) ==>
    compile_result x ≠ Halt (Word (2w:'a word))
Proof
  Cases_on `x` \\ fs [compile_result_def]
  \\ rw [good_dimindex_def] \\ fs [dimword_def]
QED

Theorem MAP_o_THE_FILTER_IS_SOME:
   MAP (f o THE) (FILTER IS_SOME ls) =
   MAP (THE o OPTION_MAP f) (FILTER IS_SOME ls)
Proof
  simp[MAP_EQ_f,MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
QED

Theorem MAP_OPTION_MAP_FILTER_IS_SOME:
   MAP (OPTION_MAP (f:α->α)) (FILTER IS_SOME ls) =
   FILTER IS_SOME (MAP (OPTION_MAP f) ls)
Proof
  match_mp_tac MAP_FILTER \\ Cases \\ simp[]
QED

Theorem MAP_FILTER_IS_SOME:
   MAP f (FILTER IS_SOME ls) = MAP (f o SOME o THE) (FILTER IS_SOME ls)
Proof
  simp[MAP_EQ_f,MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
QED

Triviality TIMES2_DIV2_lemma:
  windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves))))
    = MAP THE (FILTER IS_SOME (MAP FST (parmove moves)))
Proof
  strip_tac
  \\ simp[MAP_o_THE_FILTER_IS_SOME]
  \\ simp[GSYM MAP_MAP_o]
  \\ simp[MAP_OPTION_MAP_FILTER_IS_SOME]
  \\ ntac 2 AP_TERM_TAC
  \\ qispl_then[`moves`,`DIV2`]mp_tac(Q.GENL[`ls`,`f`]parmove_MAP_INJ)
  \\ impl_tac
  >- (
    simp[]
    \\ fs[EVERY_MEM]
    \\ metis_tac[EVEN_DIV2_INJ] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[MAP_MAP_o,o_DEF]
  \\ simp[MAP_EQ_f]
  \\ simp[FORALL_PROD]
  \\ Cases \\ simp[]
  \\ rw[]
  \\ simp[DIV2_def,bitTheory.DIV_MULT_THM2]
  \\ `EVEN x` suffices_by metis_tac[EVEN_MOD2,SUB_0]
  \\ `MEM x (MAP FST moves)` suffices_by metis_tac[EVERY_MEM]
  \\ match_mp_tac MEM_MAP_FST_parmove
  \\ simp[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem PAIR_MAP_SOME_SWAP:
   (SOME ## SOME) o (f ## g) = (OPTION_MAP f ## OPTION_MAP g) o (SOME ## SOME)
Proof
  rw[FUN_EQ_THM,FORALL_PROD]
QED

Theorem IS_SOME_o_OPTION_MAP:
   IS_SOME o OPTION_MAP f = IS_SOME
Proof
  simp[FUN_EQ_THM] \\ Cases \\ simp[]
QED

Triviality parsem_parmove_DIV2_lemma:
  windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
      (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves)))) =
   (MAP (parsem (MAP (SOME ## SOME) moves) (r o OPTION_MAP DIV2))
     (FILTER IS_SOME (MAP FST (parmove moves))))
Proof
  rw[]
  \\ drule(Q.ISPEC`DIV2`(Q.GEN`f`(ONCE_REWRITE_RULE[CONJ_COMM]parmove_MAP_INJ)))
  \\ impl_tac
  >- ( simp[] \\ rw[] \\ metis_tac[EVERY_MEM,EVEN_DIV2_INJ] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[MAP_MAP_o,o_PAIR_MAP]
  \\ simp[PAIR_MAP_SOME_SWAP]
  \\ simp[FILTER_MAP]
  \\ REWRITE_TAC[o_ASSOC]
  \\ REWRITE_TAC[IS_SOME_o_OPTION_MAP]
  \\ simp[MAP_MAP_o]
  \\ simp[MAP_EQ_f]
  \\ simp[MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
  \\ rw[]
  \\ simp[GSYM MAP_MAP_o]
  \\ qpat_abbrev_tac`mvs = MAP _ moves`
  \\ `windmill mvs`
  by (
    fs[parmoveTheory.windmill_def,Abbr`mvs`]
    \\ simp[MAP_MAP_o,o_PAIR_MAP]
    \\ simp[GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ qispl_then[`OPTION_MAP DIV2`,`r`]drule(Q.GENL[`f`,`r`]parsem_MAP_INJ)
  \\ simp[GSYM PULL_FORALL, GSYM AND_IMP_INTRO] >> impl_tac
  >- (
    simp[INJ_DEF]
    \\ Cases \\ simp[]
    \\ Cases \\ simp[]
    \\ fs[EVERY_MEM,Abbr`mvs`,MAP_MAP_o,o_PAIR_MAP,MEM_MAP,EXISTS_PROD]
    \\ metis_tac[EVEN_DIV2_INJ,SOME_11] )
  \\ simp[Abbr`mvs`,MEM_MAP,PULL_EXISTS]
  \\ qmatch_assum_rename_tac`MEM e (parmove moves)`
  \\ `MEM (FST e) (MAP FST (parmove moves))` by metis_tac[MEM_MAP]
  \\ rfs[]
  \\ imp_res_tac MEM_MAP_FST_parmove
  \\ fs[MEM_MAP]
  \\ disch_then drule
  \\ simp[] \\ disch_then kall_tac
  \\ rveq \\ fs[]
QED

Theorem ALOOKUP_MAP_any:
   ∀f k h ls a x.
   (INJ k (a INSERT (set (MAP FST ls))) UNIV) ∧
   (∀x y. MEM (x,y) ls ⇒ f (x,y) = (k x, h (k x) y)) ∧ k a = x ⇒
   ALOOKUP (MAP f ls) x = OPTION_MAP (h x) (ALOOKUP ls a)
Proof
  ntac 3 gen_tac
  \\ Induct \\ simp[]
  \\ Cases \\ simp[]
  \\ rw[]
  >- (
    `F` suffices_by rw[]
    \\ qhdtm_x_assum`INJ`mp_tac
    \\ simp[INJ_DEF]
    \\ PROVE_TAC[] )
  \\ first_x_assum match_mp_tac
  \\ simp[]
  \\ qhdtm_x_assum`INJ`mp_tac
  \\ REWRITE_TAC[INJ_DEF,IN_INSERT,MEM_MAP]
  \\ PROVE_TAC[FST,PAIR]
QED

Theorem wf_alist_insert:
   ∀xs ys z. wf z ⇒ wf (alist_insert xs ys z)
Proof
  ho_match_mp_tac alist_insert_ind \\ rw[alist_insert_def] \\ fs[wf_insert]
QED

Theorem ALOOKUP_MAP_INJ_FST:
   ∀ls f x k.
   INJ (FST o f) (x INSERT set ls) UNIV ∧
   FST (f x) = k
   ⇒
   ALOOKUP (MAP f ls) k =
   ALOOKUP (MAP (λx. (x, SND(f x))) ls) x
Proof
  Induct \\ simp[]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on`f h` \\ simp[]
  \\ Cases_on`f x` \\ fs[]
  \\ qmatch_assum_abbrev_tac`f h = v1`
  \\ qmatch_assum_abbrev_tac`f x = v2`
  \\ `h = x ⇔ FST v1 = FST v2`
  by (
    qhdtm_x_assum`INJ`mp_tac
    \\ REWRITE_TAC[INJ_DEF,IN_INSERT,IN_UNIV,o_DEF]
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ metis_tac[] )
  \\ fs[Abbr`v1`,Abbr`v2`]
  \\ IF_CASES_TAC \\ fs[]
  \\ first_x_assum(qspecl_then[`f`,`x`]mp_tac)
  \\ simp[] \\ disch_then match_mp_tac
  \\ qhdtm_x_assum`INJ`mp_tac
  \\ REWRITE_TAC[INJ_DEF,IN_INSERT,IN_UNIV]
  \\ metis_tac[]
QED

Theorem ALOOKUP_ID_TABULATE:
   ALOOKUP (MAP (λx. (x,x)) ls) x =
   if MEM x ls then SOME x else NONE
Proof
  Induct_on`ls`\\simp[]\\rw[]\\fs[]
QED

Theorem alist_insert_get_vars:
   ∀moves s x ls.
   ALL_DISTINCT (MAP FST moves) ∧
   get_vars (MAP SND moves) s = SOME x ∧
   ALL_DISTINCT (FILTER IS_SOME ls) ∧
   wf s.locals ∧
   (∀x. MEM (SOME x) ls ⇒ MEM x (MAP FST moves)) ∧
   (∀x y. MEM (x,y) moves ∧ x ≠ y ⇒ MEM (SOME x) ls)
   ⇒
   alist_insert
     (MAP THE (FILTER IS_SOME ls))
     (MAP (λx. THE (get_var (THE (ALOOKUP moves (THE x))) s)) (FILTER IS_SOME ls)) s.locals =
   alist_insert (MAP FST moves) x s.locals
Proof
  Induct \\ simp[wordSemTheory.get_vars_def]
  >- (
    rw[]
    \\ `FILTER IS_SOME ls = []`
    by (
      simp[FILTER_EQ_NIL,EVERY_MEM]
      \\ Cases \\ simp[] )
    \\ simp[] )
  \\ Cases \\ simp[]
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ strip_tac \\ rveq
  \\ simp[alist_insert_def]
  \\ fs[]
  \\ first_x_assum drule
  \\ qmatch_assum_rename_tac`get_var a s = SOME c`
  \\ qmatch_assum_rename_tac`¬MEM b _`
  \\ disch_then(qspec_then`FILTER ($<> (SOME b)) ls`mp_tac)
  \\ impl_tac
  >- (
    simp[MEM_FILTER]
    \\ conj_tac
    >- (
      simp[FILTER_FILTER]
      \\ fs[ALL_DISTINCT_FILTER,MEM_FILTER]
      \\ fs[FILTER_FILTER]
      \\ rw[]
      \\ res_tac
      \\ qmatch_assum_abbrev_tac`FILTER p1 _ = _`
      \\ qmatch_abbrev_tac`FILTER p2 _ = _`
      \\ `p1 = p2`
      by (
        simp[Abbr`p1`,Abbr`p2`,FUN_EQ_THM]
        \\ metis_tac[] )
      \\ fs[])
    \\ conj_tac >- metis_tac[]
    \\ fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD]
    \\ metis_tac[] )
  \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
  \\ `a ≠ b ⇒ MEM (SOME b) ls` by metis_tac[]
  \\ dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_alist_insert,wf_insert]
  \\ simp[lookup_insert]
  \\ simp[lookup_alist_insert]
  \\ simp[ALOOKUP_ZIP_MAP_SND]
  \\ simp[ZIP_MAP]
  \\ qx_gen_tac`x`
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (MAP f ll)`
  \\ qispl_then[`ll`,`f`,`SOME x`]mp_tac ALOOKUP_MAP_INJ_FST
  \\ simp[]
  \\ impl_tac
  >- (
    simp[INJ_DEF,Abbr`f`,Abbr`ll`,MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
    \\ rw[] \\ fs[] )
  \\ simp[Abbr`f`]
  \\ disch_then kall_tac
  \\ simp[ALOOKUP_ID_TABULATE]
  \\ simp[Abbr`ll`,MEM_FILTER]
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (MAP f ll)`
  \\ qispl_then[`ll`,`f`,`SOME x`]mp_tac ALOOKUP_MAP_INJ_FST
  \\ simp[]
  \\ impl_tac
  >- (
    simp[INJ_DEF,Abbr`f`,Abbr`ll`,MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
    \\ rw[] \\ fs[] )
  \\ simp[Abbr`f`]
  \\ disch_then kall_tac
  \\ simp[ALOOKUP_ID_TABULATE]
  \\ simp[Abbr`ll`,MEM_FILTER]
  \\ reverse(Cases_on`MEM (SOME x) ls`) \\ fs[]
  >- (
    IF_CASES_TAC \\ fs[]
    \\ fs[get_var_def] )
  \\ IF_CASES_TAC \\ fs[]
QED

Triviality wf_fromList2:
  ∀ls. wf(fromList2 ls)
Proof
  ho_match_mp_tac SNOC_INDUCT>>
  fs[fromList2_def,FOLDL_SNOC,wf_def]>>rw[]>>
  pairarg_tac>>fs[wf_insert]
QED

Theorem wStackLoad_append:
   wStackLoad (l1 ++ l2) = wStackLoad l1 o (wStackLoad l2)
Proof
  qid_spec_tac`l2`
  \\ simp[FUN_EQ_THM]
  \\ CONV_TAC SWAP_FORALL_CONV
  \\ qid_spec_tac`l1`
  \\ ho_match_mp_tac wStackLoad_ind
  \\ simp[wStackLoad_def]
QED

Theorem wRegWrite1_thm1:
   state_rel ac k f f' s t lens 0 ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' (set_var (2 * m) v s) t' lens 0 /\
   LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2]
  >- ( metis_tac[ state_rel_set_var, LESS_OR_EQ] )
  \\ rw[stackSemTheory.evaluate_def]
  >- fs[state_rel_def]
  >-
    (fs[state_rel_def]>>
    Cases_on`f'`>>fs[])
  \\ simp[]
  \\ match_mp_tac state_rel_set_var2
  \\ simp[]
QED

Theorem wRegWrite1_thm1_weak:
   state_rel ac k f f' s t lens 0 ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' (set_var (2 * m) v s) t' lens 0
Proof
  metis_tac[wRegWrite1_thm1]
QED

Theorem wRegWrite1_thm2:
   state_rel ac k f f' s t lens 0 ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var 0 v' (set_var n v t)))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' (set_var 0 v' (set_var (2 * m) v s)) t' lens 0 /\
   LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2]
  >-
    (match_mp_tac (state_rel_set_var |> Q.GEN`x`|>Q.SPEC`0`|>SIMP_RULE std_ss[])>>
    fs[]>>
    metis_tac[state_rel_set_var, LESS_OR_EQ] )
  \\ rw[stackSemTheory.evaluate_def]
  >- fs[state_rel_def]
  >-
    (fs[state_rel_def]>>
    Cases_on`f'`>>fs[])
  >>
  `0 ≠ k` by fs[state_rel_def]
  \\ simp[stackSemTheory.get_var_def,Once stackSemTheory.set_var_def]
  \\ simp[Once stackSemTheory.set_var_def]
  \\ simp[FLOOKUP_UPDATE]>>
  `∀A:('a,'b,'c) stackSem$state B. stackSem$set_var 0 v' A with stack:= B =
         set_var 0 v' (A with stack:=B)` by
    fs[stackSemTheory.set_var_def]>>
  pop_assum (asm_simp_tac(bool_ss) o single) >>
  match_mp_tac (state_rel_set_var |> Q.GEN`x`|>Q.SPEC`0`|>SIMP_RULE std_ss[])>>
  fs[]
  \\ match_mp_tac state_rel_set_var2
  \\ simp[]
QED
(*
Theorem wRegWrite1_thm3 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm4 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm5 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm6 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];
*)
Theorem wRegWrite2_thm1:
   state_rel ac k f f' s t lens 0 ∧
   m < f' + k ∧
   (∀n.  n ≤ k+1 ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite2 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' (set_var (2 * m) v s) t' lens 0
Proof
  rw[wRegWrite2_def,LET_THM,TWOxDIV2]
  >- ( metis_tac[ state_rel_set_var, LESS_OR_EQ] )
  \\ rw[stackSemTheory.evaluate_def]
  >- fs[state_rel_def]
  >-
    (fs[state_rel_def]>>
    Cases_on`f'`>>fs[])
  \\ simp[]
  \\ match_mp_tac state_rel_set_var2
  \\ simp[]
QED

Theorem state_rel_mem_store:
   state_rel ac k f f' s t lens extra ∧
   mem_store a b s = SOME s' ⇒
   ∃t'.
     mem_store a b t = SOME t' ∧
     state_rel ac k f f' s' t' lens extra
Proof
  simp[state_rel_def,stackSemTheory.mem_store_def,wordSemTheory.mem_store_def]
  \\ strip_tac \\ rveq \\ simp[] \\ metis_tac[]
QED

(* TODO: Delete?

Theorem wRegWrite1_thm2:
   state_rel ac k f f' s t lens ∧
   m < f' + k ∧
   get_var (2 * m) s = SOME w ∧
   mem_store a w s = SOME s' ∧
   (∀n. get_var n t = SOME w ⇒
     evaluate (kont n, t) = (NONE, THE(mem_store a w t)))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' s' t' lens
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2] \\ fs[]
  >- (
    drule (GEN_ALL state_rel_get_var_imp)
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ disch_then drule
    \\ simp[GSYM stackSemTheory.get_var_def]
    \\ imp_res_tac state_rel_mem_store
    \\ simp[] )
  \\ rw[stackSemTheory.evaluate_def]
  \\ imp_res_tac state_rel_mem_store
  \\ fs[] \\ rveq \\ fs[]
  \\ fs[stackSemTheory.mem_store_def,wordSemTheory.mem_store_def]
  \\ rveq \\ fs[]
  \\ IF_CASES_TAC >- fs[state_rel_def]
  \\ IF_CASES_TAC >- (fs[state_rel_def] \\ `F` by decide_tac)
  \\ fs[stackSemTheory.get_var_def]
  \\ qpat_abbrev_tac`w = EL _ _`
  \\ qmatch_assum_abbrev_tac`state_rel _ _ _ _ t1 _`
  \\ qmatch_abbrev_tac`state_rel _ _ _ _ t2 _`
  \\ `t1 = t2`
  by (
    unabbrev_all_tac
    \\ simp[stackSemTheory.state_component_equality]
    \\ match_mp_tac (GSYM LUPDATE_SAME)
    \\ fs[state_rel_def]
    \\ Cases_on`f = 0`\\fs[]
    \\ decide_tac )
  \\ fs[]
QED
*)

(*
Theorem wRegWrite1_thm2:
   state_rel ac k f f' s t lens ∧
   mem_store a b s = SOME s' ∧
   m < f' + k ∧
   (∀n. n ≤ k ⇒
      evaluate (kont n, t) =
        (NONE, THE(mem_store a b (if n < k then t else set_var k (EL (t.stack_space + (f-1-(m-k))) t.stack) t))))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' s' t' lens
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2]
  \\ `s.memory = t.memory ∧ s.mdomain = t.mdomain` by fs[state_rel_def]
  >- (
    first_x_assum(qspec_then`m`mp_tac)
    \\ simp[]
    \\ fs[wordSemTheory.mem_store_def,stackSemTheory.mem_store_def]
    \\ rw[]
    \\ fs[state_rel_def]
    \\ metis_tac[] )
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[wordSemTheory.mem_store_def,stackSemTheory.mem_store_def]
  \\ IF_CASES_TAC >- fs[state_rel_def]
  \\ IF_CASES_TAC >- (fs[state_rel_def] \\ `F` by decide_tac)
  \\ simp[stackSemTheory.get_var_def,Once stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ qmatch_goalsub_abbrev_tac`EL n t.stack`
  \\ `n < LENGTH t.stack`
  by (
    fs[state_rel_def]
    \\ simp[Abbr`n`]
    \\ rw[]
    \\ Cases_on`f'=0`\\fs[]
    \\ decide_tac )
  \\ simp[LUPDATE_SAME]
  \\ qpat_abbrev_tac`t'':('a,'b)stackSem$state = _ _`
  \\ `t'' = set_var k (EL n t.stack) (t with memory := (a =+ b) t.memory)`
  by (
    simp[Abbr`t''`,stackSemTheory.set_var_def,stackSemTheory.state_component_equality] )
  \\ simp[]
  \\ rveq
  \\ fs[state_rel_def]
  \\ metis_tac[]
QED
*)
(*
Theorem wStackLoad_thm1:
   wReg1 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)wordSem$state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
                  state_rel ac k f f' s' t' lens extra /\
                  LENGTH t'.stack = LENGTH t.stack /\
                  t'.stack_space = t.stack_space) ∧
   (¬(n1 < k) ⇒
    ∃t'. evaluate (kont k,
                   set_var k (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) =
         (NONE, t') ∧
         state_rel ac k f f' s' t' lens extra /\
         LENGTH t'.stack = LENGTH t.stack /\
         t'.stack_space = t.stack_space)
   ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\
     t'.stack_space = t.stack_space
Proof
  simp[wReg1_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
val _ = get_time timer;
(*
Theorem wStackLoad_thm1_weak:
   wReg1 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒
     ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont k, set_var k (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra
Proof
  simp[wReg1_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm2:
   wReg2 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont (k+1), set_var (k+1) (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra /\ LENGTH t'.stack = LENGTH t.stack /\
    t'.stack_space = t.stack_space)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\
     t'.stack_space = t.stack_space
Proof
  simp[wReg2_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm2_weak:
   wReg2 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont (k+1), set_var (k+1) (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra
Proof
  simp[wReg2_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm3 =
 wStackLoad_thm2
 |> Q.INST [`t`|->`set_var v1 v2 t`]
 |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const]
*)
Definition map_var_def:
  (map_var f (Var num) = Var (f num)) ∧
  (map_var f (Load exp) = Load (map_var f exp)) ∧
  (map_var f (Op wop ls) = Op wop (MAP (map_var f) ls)) ∧
  (map_var f (Shift sh e1 e2) = Shift sh (map_var f e1) e2) ∧
  (map_var f (Const c) = Const c) ∧
  (map_var f (Lookup v) = Lookup v)
Termination
  WF_REL_TAC`measure (exp_size ARB o SND)`
 \\ simp[]
 \\ Induct \\ simp[] \\ rw[]
 \\ EVAL_TAC \\ simp[] \\ res_tac \\ simp[]
End
val _ = export_rewrites["map_var_def"];

Theorem the_words_EVERY_IS_SOME_Word:
   ∀ls x. the_words ls = SOME x ⇒ ∀a. MEM a ls ⇒ ∃w. a = SOME (Word w)
Proof
  Induct \\ EVAL_TAC \\ rw[] \\ every_case_tac \\ fs[]
QED

Theorem the_words_SOME_eq:
   ∀ls x. the_words ls = SOME x ⇒ x = MAP (λx. case x of SOME (Word y) => y) ls
Proof
  Induct \\ EVAL_TAC \\ rw[] \\ every_case_tac \\ fs[]
QED

Theorem the_words_MAP_exists:
   ∀ls x a f.
  the_words (MAP f ls) = SOME x ∧
  MEM a ls ⇒
  ∃w. f a = SOME (Word w)
Proof
  Induct>>EVAL_TAC>>rw[]>>
  every_case_tac>>fs[]
QED
(*
Theorem word_exp_thm1:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   every_var_exp is_phy_var e ∧
   DIV2 (max_var_exp e) < k ∧
   state_rel ac k f f' s t lens extra ⇒
   word_exp t (map_var DIV2 e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,get_store_def]
  \\ TRY (
    qmatch_assum_rename_tac`option_CASE (the_words _) _ _ = SOME (Word _)`
    \\ qpat_x_assum`_ = SOME (Word _)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ imp_res_tac the_words_EVERY_IS_SOME_Word
    \\ fs[MEM_MAP,PULL_EXISTS] )
  \\ TRY (
    first_x_assum drule
    \\ ntac 2 strip_tac
    \\ last_x_assum drule
    \\ disch_then drule
    \\ impl_tac
    >- (
      qmatch_asmsub_abbrev_tac`list_max ls`
      \\ qspec_then`ls`mp_tac list_max_max
      \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
      \\ disch_then drule
      \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
      \\ simp[]
      \\ fs[DIV2_def]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ decide_tac )
    \\ simp[] )
  \\ TRY(
    first_x_assum drule \\ strip_tac
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ first_x_assum drule \\ simp[]
    \\ impl_tac
    >- (
      qmatch_asmsub_abbrev_tac`list_max ls`
      \\ qspec_then`ls`mp_tac list_max_max
      \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
      \\ disch_then drule
      \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
      \\ simp[]
      \\ fs[DIV2_def]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ decide_tac )
    \\ simp[] )
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2,get_var_def]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2] )
  \\ strip_tac
  \\ fs[MAP_MAP_o,o_DEF]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ imp_res_tac the_words_SOME_eq \\ rw[]
  \\ simp[MAP_EQ_f,MAP_MAP_o]
  \\ rw[]
  \\ res_tac \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`list_max ls`
  \\ qspec_then`ls`mp_tac list_max_max
  \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
  \\ disch_then drule
  \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
  \\ simp[]
  \\ fs[DIV2_def]
  \\ ntac 2 strip_tac
  \\ first_x_assum drule
  \\ simp[]
QED

Theorem word_exp_thm2:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp ($= (2 * v)) e ∧
   ¬(v < k) ⇒
   word_exp (set_var k (EL (t.stack_space + (f + k - (v + 1))) t.stack) t) (map_var (K k) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >- (
    strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm3:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k+1 else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm4:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var k (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm5:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   ¬(v1 < k) ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v2 + 1))) t.stack)
       (set_var k (EL (t.stack_space + (f + k - (v1 + 1))) t.stack) t))
     (map_var (λx. if x = 2*v1 then k else k+1) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm6:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   e = Op b [Var (2 * v1); Var (2 * v1)] ∧
   ¬(v1 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v1 + 1))) t.stack)
       (set_var k (EL (t.stack_space + (f + k - (v1 + 1))) t.stack) t))
     (Op b [Var k; Var (k+1)]) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ fs[wordSemTheory.word_exp_def,the_words_def]
  \\ rpt(qpat_x_assum`_ = SOME _`mp_tac)
  \\ rpt(FULL_CASE_TAC>>fs[])
  \\ fs[state_rel_def,LET_THM]
  \\ rfs[DOMSUB_FLOOKUP_THM]
  \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
  \\ fs[DIV2_def,TWOxDIV2,get_var_def]
  \\ first_x_assum drule
  \\ simp[TWOxDIV2]
  \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
  \\ simp[ADD_COMM]
QED
*)

Theorem state_rel_with_memory:
   state_rel ac k f f' s t lens extra ⇒
   state_rel ac k f f' (s with memory := m) (t with memory := m) lens extra
Proof
  simp[state_rel_def]
  \\ strip_tac \\ simp[]
  \\ metis_tac[]
QED

Theorem word_exp_Op_SOME_Word:
   word_exp s (Op op wexps) = SOME x ⇒ ∃w. x = Word w
Proof
  rw[word_exp_def] \\ every_case_tac \\ fs[]
QED

Theorem state_rel_get_fp_var:
   state_rel ac k f f' s t lens extra ⇒
  get_fp_var n s = get_fp_var n t
Proof
  fs[state_rel_def,get_fp_var_def,stackSemTheory.get_fp_var_def]
QED

Theorem state_rel_set_fp_var:
  state_rel ac k f f' s t lens extra ⇒
  state_rel ac k f f' (set_fp_var n v s) (set_fp_var n v t) lens extra
Proof
  fs[state_rel_def,set_fp_var_def,stackSemTheory.set_fp_var_def]>>rw[]>>
  metis_tac[]
QED

Triviality evaluate_wStackLoad_wReg1:
  wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,num # 'c,'ffi)state) = SOME c ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  t'.bitmaps = t.bitmaps /\
   (∀r. r ≠ k ⇒ get_var r t' = get_var r t) ∧
  r' ≠ k+1 ∧
  get_var r' t' = SOME c
Proof
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]
    >-
    (drule_all state_rel_get_var_imp>>simp[]) >>
  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
  fs[TWOxDIV2]
QED

Triviality evaluate_wStackLoad_wReg1_with_const:
  wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  word_exp (s:('a,num # 'c,'ffi)state) (Op Add [Var r;Const c]) = SOME (
Word w) ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  r' ≠ k+1 ∧
  (stackSem$word_exp t' (Op Add [Var r';Const c])) = SOME (w)
Proof
  rw[] >>
  gvs[wordSemTheory.word_exp_def,wordSemTheory.the_words_def,AllCaseEqs()] >>
  drule_all evaluate_wStackLoad_wReg1 >>
  strip_tac >> fs[] >>
  fs[stackSemTheory.word_exp_def] >>
  (* TODO remove this line by changing word_exp_def*)
  fs[GSYM stackSemTheory.get_var_def]
QED

Triviality evaluate_wStackLoad_clock:
  ∀x t.
  evaluate(wStackLoad x Skip,t with clock:= clk) =
  (I ## (\s. s with clock := clk)) (evaluate(wStackLoad x Skip,t))
Proof
  Induct>>fs[wStackLoad_def,FORALL_PROD,stackSemTheory.evaluate_def,LET_THM]>>rw[]
QED

Triviality evaluate_wStackLoad_wReg2:
  wReg2 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,num # 'c,'ffi)state) = SOME c ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  t.bitmaps = t'.bitmaps /\
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  (∀r. r ≠ k+1 ⇒ get_var r t' = get_var r t) ∧
  (∀r c. r ≠ k + 1 ⇒
  word_exp t' (Op Add [Var r;Const c]) = word_exp t (Op Add [Var r; Const c])) /\
  get_var r' t' = SOME c
Proof
  rw[wReg2_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,
  stackSemTheory.get_var_def,stackSemTheory.word_exp_def]>>simp[]>-
    (
    imp_res_tac state_rel_get_var_imp>>
    first_assum match_mp_tac>>
    simp[TWOxDIV2])>>

  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]
QED

Theorem evaluate_wStackLoad_seq:
   ∀ls prog s.
  evaluate(wStackLoad ls prog,s) =
  evaluate (Seq (wStackLoad ls Skip) prog,s)
Proof
  Induct>>rw[]>>fs[stackSemTheory.evaluate_def,wStackLoad_def,LET_THM]>>rw[]>>
  Cases_on`h`>>
  simp[wStackLoad_def]>>
  pop_assum (qspec_then`prog` assume_tac)>>
  simp[stackSemTheory.evaluate_def]>>
  EVERY_CASE_TAC>>fs[]
QED

(*The last two are weakened to allow easy irule
*)
Triviality evaluate_wStackStore_wReg1:
  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' ^s ^t lens 0 ∧
  LENGTH t.stack = LENGTH_t_stack ∧
  t.stack_space = t_stack_space
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var r' c t)) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space
Proof
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]>-
   (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  irule state_rel_set_var2 >> fs[]
QED

Triviality evaluate_wStackStore_wReg1_strong:
  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' ^s ^t lens 0
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var r' c t)) = (NONE,set_var r' c t') ∧
  state_rel ac k f f' (set_var r c s) (set_var r' c t') lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM,
  stackSemTheory.get_var_def]>>simp[]>-
   (irule_at (Pos hd) EQ_REFL >> fs[] >>
   irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `set_var _ _ t with stack := t_stack` >>
  qexists_tac `t with stack := t_stack` >>
  fs[set_var_with_const,Abbr`t_stack`] >>
  irule state_rel_set_var2 >> fs[]
QED


Triviality evaluate_wStackStore_wReg1_new:
  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  (?t'.
  evaluate (kont,t) = (NONE,set_var r' c t') /\
  state_rel ac k f f' s t' lens 0 /\
  LENGTH t'.stack = LENGTH_t_stack ∧ t'.stack_space = t_stack_space)
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(Seq kont (wStackStore x Skip),t) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space
Proof
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM]>>simp[]>-
  (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac `evaluate _ = (NONE,t'')` >>
  full_simp_tac(bool_ss)[GSYM stackSemTheory.state_fupdcanon] >>
  irule state_rel_set_var2 >> fs[Abbr `t''`,GSYM stackSemTheory.set_var_def]
QED

Triviality evaluate_wStackStore_wReg2_new:
  wReg2 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  (?t'.
  evaluate (kont,t) = (NONE,set_var r' c t') /\
  state_rel ac k f f' s t' lens 0 /\
  LENGTH t'.stack = LENGTH_t_stack ∧ t'.stack_space = t_stack_space)
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(Seq kont (wStackStore x Skip),t) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space
Proof
  rw[wReg2_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM]>>simp[]>-
  (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac `evaluate _ = (NONE,t'')` >>
  full_simp_tac(bool_ss)[GSYM stackSemTheory.state_fupdcanon] >>
  irule state_rel_set_var2 >> fs[Abbr `t''`,GSYM stackSemTheory.set_var_def]
QED

Triviality evaluate_wStackStore_wReg1_0:
  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' ^s ^t lens 0 ∧
  LENGTH t.stack = LENGTH_t_stack ∧
  t.stack_space = t_stack_space
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var 0 c1 (set_var r' c t))) = (NONE,t') ∧
  state_rel ac k f f' (set_var 0 c1 (set_var r c s)) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space
Proof
  rw[] >>  Cases_on `r = 0`
  >-(`r' = 0` by gvs[wReg1_def,AllCaseEqs()] >>
    simp[set_var_cancel,set_var_cancel_word] >>
    match_mp_tac  evaluate_wStackStore_wReg1 >> gvs[])
  >-(
   `~(r' = 0)` by
        (gvs[wReg1_def,AllCaseEqs(),EVEN_EXISTS] >>
        fs[state_rel_def]) >>
    simp[Once set_var_swap,Once set_var_swap_word] >>
    match_mp_tac evaluate_wStackStore_wReg1 >> simp[] >>
    match_mp_tac state_rel_set_var' >> simp[] >>
    fs[state_rel_def])
QED

Theorem evaluate_wRegWrite1_seq:
  evaluate (wRegWrite1 g r (k,f,f'),t) =
  (let (l,n) = wReg1 r (k,f,f') in
  evaluate ((Seq (g n) (wStackStore l Skip)),t))
Proof
  rw[] >> pairarg_tac >> fs[] >>
  simp[stackSemTheory.evaluate_def,wRegWrite1_def] >>
  IF_CASES_TAC >> gvs[wStackStore_def,wReg1_def]
  >-(pairarg_tac >> simp[] >>
    IF_CASES_TAC >> simp[stackSemTheory.evaluate_def])
  >-(
   pairarg_tac >> simp[] >>
   simp[el 10 $ CONJUNCTS stackSemTheory.evaluate_def] >>
   simp[el 1 $ CONJUNCTS stackSemTheory.evaluate_def])
QED

Theorem evaluate_wRegWrite2_seq:
  evaluate (wRegWrite2 g r (k,f,f'),t) =
  (let (l,n) = wReg2 r (k,f,f') in
  evaluate ((Seq (g n) (wStackStore l Skip)),t))
Proof
  rw[] >> pairarg_tac >> fs[] >>
  simp[stackSemTheory.evaluate_def,wRegWrite2_def] >>
  IF_CASES_TAC >> gvs[wStackStore_def,wReg2_def]
  >-(pairarg_tac >> simp[] >>
    IF_CASES_TAC >> simp[stackSemTheory.evaluate_def])
  >-(
   pairarg_tac >> simp[] >>
   simp[el 10 $ CONJUNCTS stackSemTheory.evaluate_def] >>
   simp[el 1 $ CONJUNCTS stackSemTheory.evaluate_def])
QED

Theorem evaluate_wInst:
   ∀i s t s'.
   inst i s = SOME s' ∧
   every_var_inst is_phy_var i ∧
   max_var_inst i < 2 * f' + 2 * k ∧
   inst_arg_convention i ∧
   state_rel ac k f f' s t lens 0
  ⇒
   ∃t'.
     evaluate (wInst i (k,f,f'), t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens 0 /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  rpt strip_tac
  \\ fs[inst_def]
  \\ gvs[Once $ AllCaseEqs()]
  \\ simp[wInst_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def]
  \\ fs[wordLangTheory.every_var_inst_def,wordLangTheory.max_var_inst_def]
  \\ rw[] \\ rw[]
  >- (
    fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
    gvs[wordSemTheory.assign_def,wordSemTheory.word_exp_def] >>
    simp[evaluate_wRegWrite1_seq] >>
    pairarg_tac >> simp[] >>
    fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
       stackSemTheory.assign_def,stackSemTheory.word_exp_def] >>
    match_mp_tac evaluate_wStackStore_wReg1 >>
    simp[])
  >- (
    reverse BasicProvers.FULL_CASE_TAC
    \\ fs[wordLangTheory.every_var_inst_def,
          wordLangTheory.max_var_inst_def,inst_arg_convention_def]
    \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
    >-( (* SubOverflow *)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        match_mp_tac evaluate_wStackStore_wReg1_0 >>
        simp[])
    >-( (* AddOverflow *)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        match_mp_tac evaluate_wStackStore_wReg1_0 >>
        simp[])
    >-( (*AddCarry*)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        `get_var 0 t'' = SOME (Word c)` by
           (`0 < k` by fs[state_rel_def] >>
           imp_res_tac state_rel_get_var_imp' >>
           fs[]) >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        match_mp_tac evaluate_wStackStore_wReg1_0 >>
        simp[])
    >-( (*LongDiv*)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        pairarg_tac >> fs[] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        imp_res_tac state_rel_get_var_imp' >> fs[] >>
        rpt (pop_assum (fn x => (if is_forall (concl x) then kall_tac x else NO_TAC))) >>
        `4 < k` by fs[state_rel_def] >>
        fs[] >>
        simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        irule state_rel_set_var' >> simp[] >>
        irule state_rel_set_var' >> simp[])
    >- ( (*LongMul*)
        (* Note: this is greatly simplified because no stack loading is done*)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        imp_res_tac state_rel_get_var_imp' >> fs[] >>
        rpt (pop_assum (fn x => (if is_forall (concl x) then kall_tac x else NO_TAC))) >>
        `4 < k` by fs[state_rel_def] >>
        fs[] >>
        simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        irule state_rel_set_var' >> simp[] >>
        irule state_rel_set_var' >> simp[])
    >- ( (* Div *)
        gvs[get_vars_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.get_vars_def] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        `!a b c. max3 a b c = MAX a (MAX b c)`
            by simp[MAX_DEF,max3_def] >>
        fs[])
    >- ( (* Shift *)
        gvs[assign_def,word_exp_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        (pairarg_tac >> fs[]) >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
           stackSemTheory.assign_def,stackSemTheory.word_exp_def] >>
        (*TODO remove this line by changing word_exp_def*)
        fs[GSYM stackSemTheory.get_var_def] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[])
    (* Binop *)
    \\ full_simp_tac(bool_ss)[GSYM max3_def]
    \\ `!x y z. max3 x y z = (MAX (MAX x y) z)`
        by fs[MAX_DEF,max3_def]
    \\ POP_ASSUM (full_simp_tac(bool_ss) o single)
    \\ Cases_on `r` \\ fs[]
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,
        wordLangTheory.every_var_imm_def] >>
        gvs[assign_def,word_exp_def,the_words_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.assign_def,stackSemTheory.word_exp_def] >>
        (*TODO remove this line by changing word_exp_def*)
        fs[GSYM stackSemTheory.get_var_def] >>
        qmatch_goalsub_abbrev_tac `if bool then A else B` >>
        `(if bool then A else B) =
         SOME (set_var n1 (Word z) t'')` by
          (UNABBREV_ALL_TAC >>
          IF_CASES_TAC >> gvs[wordLangTheory.word_op_def]) >>
        POP_ASSUM SUBST_ALL_TAC >>
        simp[] >> UNABBREV_ALL_TAC >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,
        wordLangTheory.every_var_imm_def] >>
        gvs[assign_def,word_exp_def,the_words_def,AllCaseEqs()] >>
        simp[wInst_def] >>
        (pairarg_tac >> fs[]) >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
        stackSemTheory.assign_def,stackSemTheory.word_exp_def] >>
        (*TODO remove this line by changing word_exp_def*)
        fs[GSYM stackSemTheory.get_var_def] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[]))
  >- ( (* Mem *)
    last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ fs[wordLangTheory.every_var_inst_def,wordLangTheory.max_var_inst_def]
    \\ strip_tac
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        (pairarg_tac >> fs[]) >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        `!w. mem_load w t' = mem_load w s`
           by fs[state_rel_def,
          wordSemTheory.mem_load_def,stackSemTheory.mem_load_def] >>
        fs[] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        (pairarg_tac >> fs[]) >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        `t'.memory = s.memory /\ t'.mdomain =
         s.mdomain /\ t'.be = s.be`
           by fs[state_rel_def] >>
        fs[] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 1 (pairarg_tac >> fs[]) >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        `t'.memory = s.memory /\ t'.mdomain =
         s.mdomain /\ t'.be = s.be`
           by fs[state_rel_def] >>
        fs[] >>
        match_mp_tac evaluate_wStackStore_wReg1 >>
        fs[])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        dxrule_all state_rel_mem_store >>
        strip_tac >> fs[] >>
        (*TODO write mem_store_const theorem*)
        gvs[stackSemTheory.mem_store_def,AllCaseEqs()])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        `t''.memory = s.memory /\ t''.mdomain = s.mdomain /\
        t''.be = s.be` by fs[state_rel_def] >>
        fs[] >>
        irule state_rel_with_memory >> fs[])
    >-(
        fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2] >>
        gvs[AllCaseEqs()] >>
        simp[wInst_def] >>
        ntac 2 (pairarg_tac >> fs[]) >>
        simp[wStackLoad_append] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg1_with_const >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        simp[evaluate_wStackLoad_seq] >>
        dxrule_all evaluate_wStackLoad_wReg2 >>
        strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        `t''.memory = s.memory /\ t''.mdomain = s.mdomain /\
        t''.be = s.be` by fs[state_rel_def] >>
        fs[] >>
        irule state_rel_with_memory >> fs[]))
  >- ( (*FP*)
    qpat_x_assum`A=SOME s'` mp_tac>>
    TOP_CASE_TAC >> fs[] >> strip_tac \\
    fs[wordLangTheory.every_var_inst_def,wordLangTheory.max_var_inst_def,
    reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
    >~ [`FPMovToReg`]
    >-
      (gvs[AllCaseEqs()]
      >-(
        simp[wInst_def] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        imp_res_tac $ GSYM state_rel_get_fp_var >>
        simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        match_mp_tac evaluate_wStackStore_wReg1 >> simp[])
      (* This case is a little bit harder than the rest because it is the only one
         involving a double write
      *)
      >-(
        simp[wInst_def] >>
        simp[evaluate_wRegWrite2_seq] >>
        pairarg_tac >> simp[] >>
        irule evaluate_wStackStore_wReg2_new >>
        simp[] >>
        simp[evaluate_wRegWrite1_seq] >>
        pairarg_tac >> simp[] >>
        gvs[wReg1_def,bool_case_eq] >>
        imp_res_tac $ GSYM state_rel_get_fp_var >>
        simp[wStackStore_def,
        stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
        simp[] >-
        (irule_at (Pos hd) EQ_REFL >> simp[] >>
        irule state_rel_set_var' >> fs[EVEN_EXISTS]) >>
        IF_CASES_TAC >- fs[state_rel_def] >>
        IF_CASES_TAC >- (fs[state_rel_def] >>
          Cases_on `f' = 0` >> gvs[EVEN_EXISTS]) >>
        fs[Once stackSemTheory.get_var_def,Ntimes stackSemTheory.set_var_def 2] >>
        fs[FLOOKUP_UPDATE,GSYM COND_RAND] >>
        `(r2 ≠ k)` by gvs[wReg2_def,bool_case_eq] >>
        fs[] >>
        qmatch_goalsub_abbrev_tac `set_var r2 _ t' with stack := stack` >>
        qexists_tac `t' with stack := stack` >>
        fs[set_var_with_const] >>
        UNABBREV_ALL_TAC >> simp[] >>
        full_simp_tac (bool_ss)[GSYM set_var_with_const,state_rel_set_var_k] >>
        gvs[EVEN_EXISTS] >>
        irule state_rel_set_var2 >> fs[]))
    >~ [`FPMovFromReg`]
    >- (
        gvs[AllCaseEqs()]
        >- (
           fs[wInst_def] >>
           (pairarg_tac >> fs[]) >>
           simp[evaluate_wStackLoad_seq] >>
           dxrule_all evaluate_wStackLoad_wReg1 >>
           strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[])
        >- (
           fs[wInst_def] >>
           ntac 2 (pairarg_tac >> fs[]) >>
           simp[wStackLoad_append] >>
           simp[evaluate_wStackLoad_seq] >>
           dxrule_all evaluate_wStackLoad_wReg1 >>
           strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
           simp[evaluate_wStackLoad_seq] >>
           dxrule_all evaluate_wStackLoad_wReg2 >>
           strip_tac >> simp[Once stackSemTheory.evaluate_def] >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[]))
    >~ [`FPToInt`]
    >- (
        gvs[AllCaseEqs(),UNCURRY_EQ]
        >- (fs[wInst_def] >>
           imp_res_tac $ GSYM state_rel_get_fp_var >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[])
        >- (fs[wInst_def] >>
           imp_res_tac $ GSYM state_rel_get_fp_var >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[])
        >- (fs[wInst_def] >>
           imp_res_tac $ GSYM state_rel_get_fp_var >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[]))
    >~ [`FPFromInt`]
    >- (
        gvs[AllCaseEqs()]
        >- (fs[wInst_def] >>
           imp_res_tac $ GSYM state_rel_get_fp_var >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[])
        >- (fs[wInst_def] >>
           imp_res_tac $ GSYM state_rel_get_fp_var >>
           fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
           irule state_rel_set_fp_var >> simp[]))
    >> (gvs[TypeBase.case_eq_of``:'a option``]>>
    simp[wInst_def] >>
    imp_res_tac state_rel_get_fp_var>>
    (*Reading 1 reg*)
    TRY (CHANGED_TAC $ simp[evaluate_wRegWrite1_seq] >>
    pairarg_tac >> simp[]) >>
    imp_res_tac $ GSYM state_rel_get_fp_var>>
    simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def] >>
    MAP_FIRST match_mp_tac
    [state_rel_set_fp_var,evaluate_wStackStore_wReg1] >>
    simp[]))
QED

val _ = get_time timer;
Theorem state_rel_set_store:
   state_rel ac k f f' s t lens extra ∧ v ≠ Handler ⇒
   state_rel ac k f f' (set_store v x s) (set_store v x t) lens extra
Proof
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.set_store_def,stackSemTheory.set_store_def]
  \\ simp[FLOOKUP_UPDATE]
  \\ conj_tac
  >- (
    simp[fmap_eq_flookup]
    \\ simp[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM]
    \\ rw[] )
  \\ metis_tac[]
QED

(*For calls*)
Triviality get_vars_fromList2_eq:
  get_vars (GENLIST (λx. 2*x) (LENGTH args)) s = SOME x ∧
    lookup n (fromList2 x) = SOME y ⇒
    lookup n s.locals = SOME y
Proof
  rw[]>>imp_res_tac get_vars_eq>>
    fs[lookup_fromList2,lookup_fromList,LET_THM]>>
    fs[EVERY_MAP,EVERY_GENLIST,MAP_GENLIST]>>rfs[EL_GENLIST]>>
    qpat_x_assum`A=y` sym_sub_tac>>
    res_tac>>
    simp[option_CLAUSES]>>
    AP_THM_TAC>>AP_TERM_TAC>>
    Q.ISPECL_THEN [`2n`] assume_tac DIVISION>>fs[]>>
    pop_assum(qspec_then`n` assume_tac)>>
    fs[EVEN_MOD2]>>
    simp[]
QED

(*For returning calls*)
Triviality get_vars_fromList2_eq_cons:
  get_vars (GENLIST (λx. 2*(x+1)) (LENGTH args)) s = SOME x ∧
    lookup n (fromList2 (Loc x3 x4::x)) = SOME y ∧ n ≠ 0 ⇒
    lookup n s.locals = SOME y
Proof
  rw[]>>imp_res_tac get_vars_eq>>
  fs[lookup_fromList2,lookup_fromList,LET_THM]>>
  Cases_on`n`>>fs[]>>
  Cases_on`n'`>>
  fs[EVEN,ADD1]>>
  `(n+2) DIV 2 = (n DIV 2) +1` by simp[ADD_DIV_RWT]>>
  fs[EVERY_MAP,EVERY_GENLIST,MAP_GENLIST,GSYM ADD1]>>rfs[EL_GENLIST]>>
  qpat_x_assum`A=y` sym_sub_tac>>
  res_tac>>
  simp[option_CLAUSES]>>
  AP_THM_TAC>>AP_TERM_TAC>>
  fs[ADD1]>>
  Q.ISPECL_THEN [`2n`] assume_tac DIVISION>>fs[]>>
  pop_assum(qspec_then`n` assume_tac)>>
  fs[EVEN_MOD2]>>simp[]
QED

Triviality lookup_fromList2_prefix:
  ∀x z y.
  IS_PREFIX z x ∧
  lookup n (fromList2 x) = SOME y ⇒
  lookup n (fromList2 z) = SOME y
Proof
  fs[lookup_fromList2,lookup_fromList]>>rw[]>>
  imp_res_tac IS_PREFIX_LENGTH >- DECIDE_TAC>>
  fs[IS_PREFIX_APPEND]>>
  fs[EL_APPEND1]
QED


(*
Triviality evaluate_wStackLoad_wRegImm2:
  wRegImm2 ri (k,f,f') = (x,r') ∧
  (case ri of Reg r => EVEN r | _ => T) ∧
  get_var_imm ri (s:('a,num # 'c,'ffi)state) = SOME (Word c) ∧
  state_rel ac k f f' s t lens ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip, t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  get_var_imm r' t' = SOME(Word c) ∧
  (∀r. r ≠ k+1 ⇒ get_var r t' = get_var r t) ∧
  state_rel ac k f f' s t' lens ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  Cases_on`ri`>>rw[wRegImm2_def,LET_THM,wReg2_def,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def,stackSemTheory.get_var_imm_def,get_var_imm_def]>>simp[]>-
    (imp_res_tac state_rel_get_var_imp>>
    first_assum match_mp_tac>>
    simp[TWOxDIV2])>>
  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
  fs[TWOxDIV2]
QED
*)

Triviality evaluate_call_dest_clock:
  call_dest dest args (k,f,f') = (q0,dest') ⇒
  evaluate(q0,t with clock := clk) =
  (I ## (\t. t with clock := clk)) (evaluate(q0,t:('a,'c,'ffi)stackSem$state))
Proof
  Cases_on`dest`>>fs[call_dest_def,LET_THM]>>rw[]>>
  simp[stackSemTheory.evaluate_def]>>
  pairarg_tac>>fs[]>>rveq>>fs[evaluate_wStackLoad_clock]
QED

Triviality evaluate_wLive_clock:
  ∀x t q bs bs'.
  wLive x bs kf = (q,bs') ⇒
  evaluate(q, t with clock:= clk) =
  (FST (evaluate(q,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(q,t)) with clock:=clk))
Proof
  PairCases_on`kf`>>fs[wLive_def,LET_THM]>>rw[]
  >-
    simp[stackSemTheory.evaluate_def]
  >>
    pairarg_tac>>fs[]>>rveq>>
    simp[stackSemTheory.evaluate_def,FORALL_PROD,stackSemTheory.inst_def,stackSemTheory.assign_def,stackSemTheory.set_var_def,stackSemTheory.word_exp_def,empty_env_def,stackSemTheory.get_var_def]>>
    EVERY_CASE_TAC>>fs[]
QED

Triviality state_rel_IMP_LENGTH:
  state_rel ac k f f' s t lens extra ⇒
  LENGTH lens = LENGTH s.stack
Proof
  fs[state_rel_def,stack_rel_def,LET_THM]>>rw[]>>
  metis_tac[abs_stack_IMP_LENGTH]
QED

(*NB this lemma can be slightly simpler with
EL (x + offset) stack' = EL (x) stack'*)
Triviality evaluate_stack_move:
  ∀n tar t offset.
  t.use_stack ∧
  t.stack_space + tar + n + offset ≤ LENGTH t.stack ∧
  n ≤ offset
  ⇒
  ∃t'.
  evaluate(stack_move n tar offset k Skip, t) = (NONE,t') ∧
  ?t'_stack t'_regs.
  t' = t with <|stack:=t'_stack; regs:=t'_regs|> ∧
  (*All regs fixed except k*)
  (∀i. i ≠ k ⇒ get_var i t' = get_var i t) ∧
  (*Unnecessary*)
  LENGTH t.stack = LENGTH t'_stack ∧
  t'.stack_space = t.stack_space ∧
  (*Rest of stack is unchanged*)
  DROP (t'.stack_space+tar+n) t'_stack =
  DROP (t.stack_space+tar+n) t.stack ∧
  (*Copying the first frame*)
  let stack' = DROP (t'.stack_space + tar) t'_stack in
  let stack = DROP (t.stack_space + tar) t.stack in
  ∀x. x < n ⇒
   EL (x + offset) stack = EL (x) stack'
Proof
  Induct>>fsrw_tac[][stack_move_def,stackSemTheory.evaluate_def]>-
    simp[stackSemTheory.state_component_equality]>>
  ntac 4 strip_tac>>
  simp[]>>
  first_x_assum(qspecl_then[`tar+1`,`t`,`offset`] mp_tac)>>
  impl_tac>-
    simp[]>>
  strip_tac>>fsrw_tac[][stackSemTheory.state_component_equality]>>
  reverse IF_CASES_TAC>-
    `F` by DECIDE_TAC>>
  fsrw_tac[][stackSemTheory.set_var_def]>>
  IF_CASES_TAC>-
    `F` by DECIDE_TAC>>
  fsrw_tac[][]>>srw_tac[][]
  >-
    fs[stackSemTheory.get_var_def,FLOOKUP_UPDATE]
  >-
    (qpat_x_assum`A=B` mp_tac>>
    simp[DROP_LUPDATE,ADD1])
  >>
    simp[EL_DROP,EL_LUPDATE]
  >> Cases_on `x = 0` >-
       (simp[] >>
       `?y. offset = y + SUC n`
          by(imp_res_tac LESS_EQ_ADD_EXISTS >>gvs[]) >>
        simp[GSYM EL_DROP,DROP_DROP] >>
        rfs[] >>
        qmatch_asmsub_abbrev_tac `DROP a _ = DROP a _` >>
        qmatch_goalsub_abbrev_tac `DROP b _` >>
        `a = b` by simp[Abbr`a`,Abbr`b`] >>
        gvs[]) >>
    fsrw_tac[][LET_THM] >>
    first_x_assum(qspec_then`x -1` mp_tac)>>
    simp[EL_DROP]
QED

Triviality evaluate_stack_move_seq:
  ∀a b c d prog (t:('a,'c,'ffi)stackSem$state).
  evaluate (stack_move a b c d prog,t) =
  evaluate (Seq prog (stack_move a b c d Skip),t)
Proof
  Induct>>rw[]>>fs[stack_move_def,LET_THM]
  >-
    (simp[stackSemTheory.evaluate_def]>>
    pairarg_tac>>simp[]>>IF_CASES_TAC>>fs[])
  >>
    simp[Once stackSemTheory.evaluate_def]>>
    pop_assum kall_tac>>
    simp[stackSemTheory.evaluate_def]>>
    rpt(pairarg_tac>>fs[])>>
    rpt (pop_assum mp_tac)>>
    IF_CASES_TAC>>fs[]>>
    rpt IF_CASES_TAC>>fs[]
QED

val evaluate_stack_move_clock = Q.prove(`
  ∀a b c d (t:('a,'c,'ffi)stackSem$state).
  let prog = stack_move a b c d Skip in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))`,
  Induct>>fs[LET_THM,stack_move_def,stackSemTheory.evaluate_def]>>rw[]>>
  TRY(pairarg_tac>>fs[])>>
  simp[]>>
  (*get_var_set_var?*)
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE])|>SIMP_RULE arith_ss [LET_THM];

Triviality pop_env_ffi:
  pop_env s = SOME s' ⇒
  s.ffi = s'.ffi
Proof
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[state_component_equality]
QED

Triviality stack_rel_DROP_NONE:
  stack_rel k whandler (StackFrame n l0 l NONE::wstack) shandler sstack len bs (f'::lens) ⇒
  stack_rel k whandler wstack shandler (DROP (f'+1) sstack) len bs lens
Proof
  simp[stack_rel_def]>>rw[]>>
  Cases_on`sstack`>>fs[abs_stack_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
  rpt (TOP_CASE_TAC>>simp[])>>
  rw[]>>fs[stack_rel_aux_def]>>
  qpat_x_assum`P ⇒A=B` mp_tac>>
  simp[]>>
  `SUC (LENGTH wstack) - (whandler+1) = SUC(LENGTH wstack - (whandler +1))` by DECIDE_TAC>>
  simp[]>>rw[]>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[LASTN_CONS]
QED

Triviality stack_rel_DROP_SOME:
  stack_rel k whandler (StackFrame n l0 l (SOME (whandler',b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  stack_rel k whandler' wstack (SOME(EL 2 sstack)) (DROP (f'+4) sstack) len bs lens
Proof
  simp[stack_rel_def]>>rw[]>>
  Cases_on`sstack`>>fs[abs_stack_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
  rpt (TOP_CASE_TAC>>simp[])>>
  rw[]>>fs[stack_rel_aux_def]>>
  qpat_x_assum`P ⇒A=B` mp_tac>>
  simp[]>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[]
QED

Triviality LAST_GENLIST_evens:
  n ≠ 0 ⇒
  let reg = LAST (GENLIST (λx. 2 * (x+1)) n) in
  reg ≠ 0 ∧ EVEN reg
Proof
  Cases_on`n`>>
  simp[LAST_EL,GENLIST_CONS]>>
  `0 < 2n` by DECIDE_TAC>>
  metis_tac[EVEN_MOD2,MULT_COMM,MOD_EQ_0]
QED

Triviality stack_rel_cons_LEN_NONE:
  stack_rel k whandler (StackFrame n l0 l NONE::wstack) shandler sstack len bs (f'::lens) ⇒
  f'+1 ≤ LENGTH sstack
Proof
  simp[stack_rel_def]>>Cases_on`sstack`>>simp[abs_stack_def]>>
  rpt TOP_CASE_TAC>>simp[]
QED

Triviality stack_rel_cons_LEN_SOME:
  stack_rel k whandler (StackFrame n l0 l (SOME(a,b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  f'+4 ≤ LENGTH sstack
Proof
  simp[stack_rel_def]>>Cases_on`sstack`>>simp[abs_stack_def]>>
  rpt TOP_CASE_TAC>>simp[]
QED

Theorem stack_rel_cons_locals_size:
  stack_rel k whandler (StackFrame n l0 l opt::t'')
    shandler rest_of_stack len
    bitmaps (f'::lens)
  ==>
  the (f' + 1) n = (f' + 1)
Proof
  Cases_on `opt` >> TRY(PairCases_on `x`) >>
  rw[stack_rel_def] >> Cases_on `rest_of_stack` >>
  fs[abs_stack_def,CaseEq "option", CaseEq "bool", CaseEq "list"] >>
  rveq >>
  fs[stack_rel_aux_def,LENGTH_TAKE_EQ] >> rfs[]
QED

Theorem IS_SOME_OPTION_MAP2_EQ:
 IS_SOME (OPTION_MAP2 f A B) <=>
 (IS_SOME A /\ IS_SOME B)
Proof
 rw[OPTION_MAP2_DEF]
QED

Triviality DROP_SUB:
  a ≤ LENGTH ls ∧ b ≤ a ⇒
  DROP (a-b) ls = (DROP(a-b) (TAKE a ls))++ DROP a ls
Proof
  rw[]>>
  Q.ISPECL_THEN[`a`,`ls`] mp_tac(GSYM TAKE_DROP)>>
  disch_then SUBST_ALL_TAC>>
  simp[GSYM DROP_APPEND1]
QED

Triviality DROP_SUB2:
  ∀a ls b.
  b ≤ a ∧
  a = LENGTH ls ⇒
  ∃rest.
  DROP (a-b) ls = rest ∧ LENGTH rest = b
Proof
  Induct>>
  fs[]>>rw[]>>
  simp[]
QED

(* TODO: maybe extra = 0 *)
Triviality evaluate_PushHandler:
  3 ≤ t.stack_space ∧
  state_rel ac k 0 0 (push_env x' NONE s with <|locals:=LN; locals_size:=SOME 0|>) t (f'::lens) extra ∧
  loc_check t.code (x''2,x''3) ⇒
  ∃t':('a,'c,'ffi)stackSem$state.
  evaluate(PushHandler (x''2:num) (x''3:num) (k,f:num,f'),t) = (NONE,t') ∧
  t' = t with <|stack_space:=t'.stack_space; regs:=t'.regs;stack:=t'.stack;store:=t'.store|> ∧
  (∀n.
    n < LENGTH t.stack - t.stack_space ⇒
    EL n (DROP t.stack_space t.stack) = EL (n+3) (DROP t'.stack_space t'.stack)) ∧
  (∀i. i ≠ k ⇒ get_var i t' = get_var i t) ∧
  t'.stack_space +3 = t.stack_space ∧
  LENGTH t'.stack = LENGTH t.stack ∧
  state_rel ac k 0 0 (push_env x' (SOME (x''0,x''1:'a wordLang$prog,x''2,x''3)) s with <|locals:=LN; locals_size:=SOME 0|>) t' (f'::lens) extra
Proof
  cheat
  (*
  rw[]>>
  `t.use_stack ∧ t.use_store ∧ t.stack_space -3 < LENGTH t.stack ∧ ∃h. FLOOKUP t.store Handler = SOME h` by
    (fs[state_rel_def,flookup_thm]>>
    simp[])>>
  simp[PushHandler_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
       stackSemTheory.word_exp_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,stackSemTheory.set_store_def]>>
  fs[state_rel_def]>>
  simp[FLOOKUP_UPDATE]>>
  fs[push_env_def,env_to_list_def,LET_THM,lookup_def]>>
  CONJ_TAC>-
    simp[DROP_LUPDATE,EL_LUPDATE,EL_DROP]>>
  CONJ_TAC>-
    metis_tac[]>>
  CONJ_TAC>- (
    fs[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF,the_eqn,stack_size_eq,
        CaseEq"bool",CaseEq"option"] >>
     rw[] >> fs[] >> every_case_tac >>
     fs[] >>
     rw[] >> rfs[]) >>
  CONJ_TAC >- (fs[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF,the_eqn,stack_size_eq,
        CaseEq"bool",CaseEq"option"] >>
     rw[] >> fs[] >> every_case_tac >>
     fs[] >> rw[] >> rfs[]) >>
  CONJ_TAC >- (fs[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF,the_eqn,stack_size_eq,
        CaseEq"bool",CaseEq"option"] >>
     rw[] >> fs[] >> every_case_tac >>
     fs[] >> rw[] >> rfs[])
 >>
  fs[stack_rel_def]>>
  CONJ_TAC>-
    fs[sorted_env_def]>>
  simp[DROP_LUPDATE]>>
  `∃a b c ts. DROP (t.stack_space-3) t.stack = a::b::c::DROP t.stack_space t.stack` by
    (simp[DROP_SUB]>>
    simp[TAKE_TAKE_MIN,LENGTH_TAKE,DROP_LENGTH_NIL_rwt]>>
    imp_res_tac (DROP_SUB2|>INST_TYPE[alpha|->``:'a word_loc``])>>
    first_x_assum(qspec_then`TAKE t.stack_space t.stack` mp_tac)>>
    impl_tac>- simp[]>>
    strip_tac>>
    qpat_x_assum`A=rest` SUBST_ALL_TAC>>
    Cases_on`rest`>>fs[]>>
    Cases_on`t'`>>fs[]>>
    Cases_on`t''`>>fs[ADD1]>>
    Cases_on`t'`>>fs[ADD1]>>
    DECIDE_TAC)>>
  fs[LUPDATE_compute]>>
  qpat_x_assum`abs_stack A B C D = SOME stack` mp_tac>>
  Cases_on`DROP t.stack_space t.stack`>>simp[abs_stack_def]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[ADD1]>>rw[]
  >- (
    (*stackLang handler needs to be updated*)
    simp[handler_val_def,LASTN_LENGTH_ID2,LASTN_CONS]>>
    qpat_x_assum`LENGTH x'' =LENGTH s.stack` sym_sub_tac>>
    simp[LASTN_LENGTH_ID]>>
    imp_res_tac abs_stack_to_stack_LENGTH>>
    simp[]>>
    qpat_x_assum `A=h'::t'` (mp_tac o Q.AP_TERM `LENGTH`)>>
    simp[]) >>
  fs[stack_rel_aux_def]>>
  rw[]>>
  qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
  simp[]>>
  `SUC (LENGTH s.stack) - (s.handler+1) = SUC(LENGTH s.stack - (s.handler+1))` by DECIDE_TAC>>
  fs[handler_val_def,GSYM ADD1]>>
  rw[]>>
  simp[LASTN_CONS] *)
QED

(* TODO: maybe extra = 0 *)
Theorem evaluate_PopHandler:
  state_rel ac k 0 0 r t1 (f'::lens) extra ∧
  pop_env r = SOME x'' /\
  s_key_eq (call_env q r'
             (push_env env (SOME (2,handler1,handler2,handler3))
                s)).stack r.stack /\
  f + (t1.stack_space + 3) <= LENGTH t1.stack /\
  f = f' + 1 /\
  1 <= f' /\
  FLOOKUP t1.regs 1 = SOME w0 /\
  (!n v.
        lookup n x''.locals = SOME v /\ n <> 2 ==>
        EVEN n /\
        if n DIV 2 < k then (FLOOKUP t1.regs (n DIV 2) = SOME v)
        else (LLOOKUP (TAKE f (DROP (t1.stack_space + 3) t1.stack)) (f-1 -(n DIV 2 - k)) = SOME v) /\
             n DIV 2 < k + f')
  ⇒
  ∃t':('a,'c,'ffi)stackSem$state.
  evaluate(PopHandler (k,f,f') Skip,t1) = (NONE,t') ∧
  state_rel ac k f f' (set_var 2 w0 x'') t' lens extra ∧
  x''.handler = s.handler /\
  LENGTH t'.stack = LENGTH t1.stack /\
  t'.stack_space = t1.stack_space + 3
Proof
  cheat
  (*
  rpt strip_tac >>
  fs[state_rel_def,stackSemTheory.evaluate_def,PopHandler_def,pop_env_def,
     CaseEq "list", CaseEq "stack_frame", CaseEq "prod", CaseEq "option",
     call_env_def,push_env_def,ELIM_UNCURRY
    ]>>
  rveq >> fs[stackSemTheory.set_var_def,wordSemTheory.set_var_def] >>
  rfs[] >> fs[s_key_eq_def,s_frame_key_eq_def,stack_size_eq,env_to_list_def] >>
  rveq >> fs[IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stackSemTheory.set_store_def,
             FLOOKUP_UPDATE] >>
  imp_res_tac stack_rel_cons_locals_size >>
  fs[] >>
  CONJ_TAC>-
    metis_tac[evaluate_mono,subspt_def]>>
  CONJ_TAC>-
    metis_tac[wf_insert,wf_fromAList,wf_union]>>
  CONJ_TAC >-
    (rw[the_eqn] >> TOP_CASE_TAC >>
     fs[the_eqn]) >>
  CONJ_TAC >-
    (strip_tac >> fs[IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP] >>
     res_tac >> fs[IS_SOME_EXISTS,miscTheory.the_def] >>
     rfs[miscTheory.the_def]) >>
  imp_res_tac stack_rel_DROP_SOME >>
  rfs[DROP_DROP_T,EL_DROP] >>
  ntac 2 strip_tac >>
  fsrw_tac[][lookup_insert,convs_def]>>
  IF_CASES_TAC >- rw[] >>
  strip_tac >> res_tac >>
  metis_tac[] *)
QED

Triviality evaluate_PushHandler_clock:
  ∀(t:('a,'c,'ffi)stackSem$state).
  evaluate (PushHandler a b (k,f:num,f':num),t with clock:=clk) =
  (FST (evaluate(PushHandler a b (k,f:num,f':num),t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(PushHandler a b (k,f:num,f':num),t)) with clock:=clk))
Proof
  simp[PushHandler_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
       stackSemTheory.word_exp_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,stackSemTheory.set_store_def]>>rw[]>>
  TOP_CASE_TAC>>fs[empty_env_def,FLOOKUP_UPDATE]>>
  rpt(TOP_CASE_TAC>>fs[])
QED

Triviality evaluate_PopHandler_clock:
  ∀(t:('a,'c,'ffi)stackSem$state).
  let prog = PopHandler (k,f:num,f':num) Skip in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))
Proof
  simp[stackSemTheory.evaluate_def,PopHandler_def,stackSemTheory.set_var_def,stackSemTheory.get_var_def,stackSemTheory.set_store_def,empty_env_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]
QED

Triviality evaluate_PopHandler_seq:
  ∀prog (t:('a,'c,'ffi)stackSem$state).
  evaluate (PopHandler (k,f,f') prog,t) =
  evaluate (Seq (PopHandler (k,f,f') Skip) prog,t)
Proof
  simp[stackSemTheory.evaluate_def,PopHandler_def]>>
  rw[]>>EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]
QED

Triviality word_cmp_Word_Word:
  word_cmp cmp (Word c) (Word c') = SOME (word_cmp cmp c c')
Proof
  Cases_on `cmp`
  \\ rw [labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
QED

Triviality ALL_DISTINCT_MEM_toAList_fromAList:
  ALL_DISTINCT (MAP FST ls) ⇒
  (MEM x (toAList (fromAList ls)) ⇔
  MEM x ls)
Proof
  Cases_on`x`>>fs[MEM_toAList,lookup_fromAList]>>
  rw[]>>
  metis_tac[ALOOKUP_MEM,ALOOKUP_ALL_DISTINCT_MEM]
QED

Triviality state_rel_code_domain:
  state_rel ac k f f' s t lens extra ⇒
  domain s.code ⊆ domain t.code
Proof
  strip_tac>>fs[state_rel_def,SUBSET_DEF,domain_lookup,EXISTS_PROD]>>
  metis_tac[]
QED

Theorem get_labels_wStackLoad:
   !xs p. get_labels (wStackLoad xs p) = get_labels p
Proof
  Induct \\ fs [wStackLoad_def]
  \\ Cases \\ fs [wStackLoad_def,get_labels_def]
QED

Theorem loc_check_SUBSET:
    subspt s t ⇒
  loc_check s ⊆ loc_check t
Proof
  fs[SUBSET_DEF,IN_DEF,loc_check_def,FORALL_PROD,subspt_def]>>rw[]>>
  metis_tac[domain_lookup,IN_DEF]
QED

Theorem MAP_FST_compile_word_to_stack:
   ∀ac k ps bm ps' bm'.
    compile_word_to_stack ac k ps bm = (ps',bm') ⇒ MAP FST ps' = MAP FST ps
Proof
  recInduct compile_word_to_stack_ind
  \\ rw[compile_word_to_stack_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
QED

Theorem wLive_LENGTH:
   ∀a bs c q bs'.
   wLive a bs c = (q,bs')  ∧
   LENGTH (append (FST bs)) ≤ SND bs ⇒
   LENGTH (append (FST bs')) ≤ SND bs' ∧
   SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs'))
Proof
  rw[]
  \\ PairCases_on`c`
  \\ fs[wLive_def,LET_THM]
  \\ Cases_on`c1=0` \\ gs[]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ Cases_on`bs`
  \\ gs[insert_bitmap_def]
  \\ rw[]
QED

Theorem comp_IMP_LENGTH:
  ∀ac c1 bs r q1 bs'.
  comp ac c1 bs r = (q1,bs') ∧
  LENGTH (append (FST bs)) ≤ SND bs ⇒
  LENGTH (append (FST bs')) ≤ SND bs' ∧
  SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs'))
Proof
  ho_match_mp_tac comp_ind
  \\ rw[comp_def,LET_THM]
  \\ every_case_tac \\ fs[]
  \\ rpt (pairarg_tac >> fs[])
  \\ rveq \\ fs[]
  \\ TRY (Cases_on`bs`>>fs[insert_bitmap_def] \\ rw[] \\ NO_TAC)
  \\ drule wLive_LENGTH \\ simp[]
QED

Theorem compile_prog_LENGTH:
  compile_prog ac prog arg reg (bm,i) = (prog',fs',bm',i') ∧
  LENGTH (append bm) ≤ i ⇒
  LENGTH (append bm') ≤ i' ∧
  i - LENGTH (append bm) = i' - LENGTH (append bm')
Proof
  fs[compile_prog_def] \\ rw[]
  \\ pairarg_tac \\ fs []
  \\ imp_res_tac comp_IMP_LENGTH
  \\ rfs[]
QED

Theorem compile_word_to_stack_IMP_LENGTH:
  !code k bm i progs fs bm' i'.
  compile_word_to_stack ac k code (bm,i) = (progs,fs,bm',i') /\
  LENGTH (append bm) ≤ i ⇒
  LENGTH (append bm') ≤ i' ∧
  i - LENGTH (append bm) = i' - LENGTH (append bm')
Proof
  Induct >> strip_tac>>fs[compile_word_to_stack_def]>>
  PairCases_on`h`>>fs[compile_word_to_stack_def]>>
  rw[]>>
  rpt(pairarg_tac>>fs[])>>
  rw[]>>
  Cases_on`bitmaps'`>>
  drule compile_prog_LENGTH>>rw[]>>
  first_x_assum drule>>rw[]
QED

(* Used in backendProof *)
Theorem compile_word_to_stack_bitmaps:
   word_to_stack$compile c p = (bitmaps,c2,prog1) ==>
    (case bitmaps of [] => F | h::v1 => 4w = h) ∧ c2.bitmaps_length = LENGTH bitmaps
Proof
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
  >- (imp_res_tac compile_word_to_stack_isPREFIX \\ fs[])
  \\ Cases_on`bitmaps'`  \\ imp_res_tac compile_word_to_stack_IMP_LENGTH
  \\ fs[]
QED

Triviality compile_word_to_stack_IMP_ALOOKUP:
  !code k bs i progs fs bs' i' n arg_count word_prog x.
    compile_word_to_stack ac k code (bs,i) = (progs,fs,bs',i') /\
    ALOOKUP code n = SOME (arg_count,word_prog) /\
    LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH x ∧
    isPREFIX (append bs') (DROP (i - LENGTH (append bs)) x) ⇒
    ∃bs i bs2 i2 f stack_prog.
      compile_prog ac word_prog arg_count k (bs,i) = (stack_prog,f,(bs2,i2)) ∧
      LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH x ∧
      isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) x) ∧
      ALOOKUP progs n = SOME stack_prog
Proof
  Induct \\ fs [] \\ strip_tac \\ PairCases_on `h`
  \\ fs [compile_word_to_stack_def] \\ rw [] \\ fs [LET_THM]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  THEN1 (
    Cases_on`bitmaps'`
    \\ asm_exists_tac \\ fs [] \\ imp_res_tac IS_PREFIX_TRANS)
  \\ first_x_assum match_mp_tac
  \\ Cases_on`bitmaps'`
  \\ asm_exists_tac \\ fs []
  \\ drule compile_prog_LENGTH
  \\ rw[] \\ fs[]
QED

val goal = ``
   λ(prog:'a wordLang$prog,s:('a,num # 'c,'ffi) wordSem$state).
     ∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     comp ac prog (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (*
              list positions:  0 1 2 3 ... k-2 k-1 k  k+1 ...
              registers:       1 2 3 4 ... k-1
              stack    :                       0   1  2   ...
              TODO: LLOOKUP probably off by one or two *)
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃cs.
           state_rel ac k 0 0 (push_locals cs s1) t1 (LASTN (s.handler+1) lens) 0 /\
           FLOOKUP t1.regs 1 = SOME y
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``

local
  val gst = goal |> Ho_Rewrite.PURE_ONCE_REWRITE_CONV [Once PFORALL_THM] |> concl |> rhs
  val ind_thm = evaluate_ind |> ISPEC goal |> GEN_BETA_RULE
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem comp_Skip_correct:
  ^(get_goal "Skip")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0` \\
  fs[comp_def] \\ rw[] \\
  fs [wordSemTheory.evaluate_def,
                         stackSemTheory.evaluate_def,comp_def] \\ rw []
QED

Theorem comp_Alloc_correct:
  ^(get_goal "Alloc")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0`
  \\ fs [wordSemTheory.evaluate_def,stackSemTheory.evaluate_def,comp_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ `n = 2` by (fs [convs_def]) \\ rveq 
  \\ `1 < k` by fs[state_rel_def]
  \\ `get_var 1 t = get_var 2 s`
     by (`EVEN 2` by fs[]  \\
     imp_res_tac state_rel_get_var_imp' \\
     rfs[] \\ fs[])
  \\ Cases_on `cut_envs names s.locals`
  THEN1 fs [wordSemTheory.alloc_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC `cut_envs names s.locals = SOME envs`
  \\ Cases_on`1 ≤ f`
  THEN1 (
    drule $ GEN_ALL evaluate_wLive
    \\ rpt $ (disch_then (drule_at Any))
    \\ impl_keep_tac
    THEN1 (
      fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
      fs[GSYM toAList_domain,EVERY_MEM]>>
      fs[X_LE_DIV,reg_allocTheory.is_phy_var_def,LET_THM]>>
      rw[]>>res_tac>>DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ rw[]
    \\ fs [stackSemTheory.evaluate_def,LET_THM]
    \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
    \\ Cases_on `alloc c t5` \\ fs []
    \\ rename1 `alloc c t5 = (res1,t1)` \\ fs []
    \\ drule_all alloc_IMP_alloc
    \\ simp[PULL_EXISTS]
    \\ rpt GEN_TAC \\ Cases_on `res = NONE` \\ fs[]) >>
  `f=0` by DECIDE_TAC>>
  `f' = 0` by fs[state_rel_def]>>
  `t.use_alloc` by fs[state_rel_def] >>
  fs[wLive_def]>>rveq>>fs[stackSemTheory.evaluate_def,LET_THM]>>
  fs[cut_env_def]>>
  `domain (FST names) = {}` by (
    CCONTR_TAC>>fs[]>>
    `∃x. x ∈ domain (FST names)` by fs[MEMBER_NOT_EMPTY]>>
    fs[convs_def,GSYM toAList_domain]>>
    assume_tac list_max_max>>
    fs[EVERY_MEM]>>res_tac>>
    fs[wordLangTheory.max_var_def])>>
  `domain (SND names) = {}` by
    (CCONTR_TAC>>fs[]>>
    `∃x. x ∈ domain (SND names)` by fs[MEMBER_NOT_EMPTY]>>
    fs[convs_def,GSYM toAList_domain]>>
    assume_tac list_max_max>>
    fs[EVERY_MEM]>>res_tac>>
    fs[wordLangTheory.max_var_def])>>
  drule_all alloc_IMP_alloc2>>
  fs[PULL_EXISTS]>>
  Cases_on`res=NONE`>>fs[]
QED

Theorem chunk_to_bits_bound:
  ∀ws.
    LENGTH ws < dimindex (:α) ⇒
    (chunk_to_bits ws : 'a word) ' (LENGTH ws) ∧
    ∀i. LENGTH ws < i ∧ i < dimindex (:'a) ⇒ ~(chunk_to_bits ws : 'a word) ' i
Proof
  Induct \\ fs [chunk_to_bits_def,word_index,FORALL_PROD]
  \\ gen_tac \\ strip_tac \\ gvs []
  \\ ‘chunk_to_bits ws ≪ 1 + 1w = (chunk_to_bits ws ≪ 1) || 1w’ by
   (irule WORD_ADD_OR
    \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,word_index]
QED

Theorem chunk_to_bits_0:
  chunk_to_bits ((b,w)::words) ' 0 ⇔ b
Proof
  fs [chunk_to_bits_def]
  \\ ‘chunk_to_bits words ≪ 1 + 1w = (chunk_to_bits words ≪ 1) || 1w’ by
    (irule WORD_ADD_OR
     \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
  \\ fs [] \\ rw []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,word_index]
QED

Theorem copy_words_for_pattern_thm:
  ∀words xs a off ys dm m.
    LENGTH words < dimindex (:α) ∧ const_addresses a words dm ⇒
    copy_words_for_pattern (chunk_to_bits words) (LENGTH xs) (a:'a word) off
      (xs ++ MAP SND words ++ ys) dm m =
    SOME (LENGTH xs + LENGTH words,
          a + bytes_in_word * n2w (LENGTH words),
          const_writes a off words m)
Proof
  Induct \\ fs [FORALL_PROD]
  THEN1 (EVAL_TAC \\ fs [])
  \\ rw [] \\ gvs [const_addresses_def]
  \\ once_rewrite_tac [copy_words_for_pattern_def]
  \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND,chunk_to_bits_0]
  \\ ‘LENGTH ((p_1,p_2)::words) < dimindex (:α)’ by fs []
  \\ drule chunk_to_bits_bound \\ strip_tac \\ gvs []
  \\ conj_tac
  THEN1 (fs [fcpTheory.CART_EQ,word_index] \\ qexists_tac ‘(SUC (LENGTH words))’ \\ fs [])
  \\ IF_CASES_TAC
  THEN1
   (qsuff_tac ‘F’ \\ simp [] \\ pop_assum mp_tac \\ simp []
    \\ simp [fcpTheory.CART_EQ,word_index]
    \\ qexists_tac ‘(SUC (LENGTH words))’ \\ simp [fcpTheory.CART_EQ,word_index])
  \\ last_x_assum drule
  \\ ‘(chunk_to_bits ((p_1,p_2)::words) ⋙ 1) = chunk_to_bits words’ by
   (fs [chunk_to_bits_def]
    \\ ‘chunk_to_bits words ≪ 1 + 1w = (chunk_to_bits words ≪ 1) || 1w’ by
      (irule WORD_ADD_OR
       \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
    \\ simp []
    \\ qsuff_tac ‘(chunk_to_bits words ≪ 1) ⋙ 1 = chunk_to_bits words’
    THEN1
     (rw []
      \\ fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_or_def,word_lsl_def,word_lsr_def]
      \\ rw []
      \\ Cases_on ‘chunk_to_bits words ' i'’ \\ fs []
      \\ CCONTR_TAC \\ fs [] \\ gvs [word_index])
    \\ qsuff_tac ‘~word_msb (chunk_to_bits words)’
    THEN1
     (simp [word_msb_def,fcpTheory.CART_EQ,fcpTheory.FCP_BETA,
            word_or_def,word_lsl_def,word_lsr_def]
      \\ rw []
      \\ Cases_on ‘i = dimindex (:'a) - 1’
      \\ gvs [fcpTheory.FCP_BETA])
    \\ ‘LENGTH words < dimindex (:α)’ by fs []
    \\ drule chunk_to_bits_bound
    \\ strip_tac \\ fs [word_msb_def])
  \\ fs []
  \\ disch_then (qspecl_then [‘xs ++ [p_2]’,‘off’,‘ys’,
        ‘m⦇a ↦ Word (if p_1 then off + p_2 else p_2)⦈’] mp_tac)
  \\ fs [ADD1] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [const_writes_def]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem word_msb_chunk_to_bits:
  LENGTH words < dimindex (:α) ∧ good_dimindex (:α) ⇒
  word_msb (chunk_to_bits words : 'a word) = (LENGTH words = dimindex (:α) − 1)
Proof
  rw [] \\ drule chunk_to_bits_bound
  \\ Cases_on ‘LENGTH words = dimindex (:α) − 1’ \\ fs []
  \\ fs [word_msb_def] \\ rw []
  \\ first_x_assum irule \\ fs []
QED

Theorem copy_words:
   const_addresses a words dm ∧ good_dimindex (:α) ∧
   LENGTH words < dimindex (:α) ⇒
   copy_words (LENGTH xs) a off (xs ++ chunk_to_bitmap words ++ ys) dm m =
     if LENGTH words = dimindex (:α) - 1 then
       copy_words (LENGTH xs + (LENGTH words + 1))
             (a + bytes_in_word * n2w (LENGTH words)) off
             (xs ++ chunk_to_bitmap words ++ ys) dm
             (const_writes a off words m)
     else
       SOME (a + bytes_in_word * n2w (LENGTH words),
             const_writes (a:'a word) off words m)
Proof
  fs [chunk_to_bitmap_def]
  \\ simp [Once copy_words_def]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,EL_LENGTH_APPEND,NULL]
  \\ fs [EL_LENGTH_APPEND,NULL]
  \\ strip_tac
  \\ drule copy_words_for_pattern_thm
  \\ disch_then (qspec_then ‘xs ++ [chunk_to_bits words]’ mp_tac)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] \\ fs []
  \\ fs [word_msb_chunk_to_bits]
QED

val _ = get_time timer;

Theorem const_writes_append:
  ∀h t a off m.
    const_writes a off (h ++ t) m =
    const_writes (a + bytes_in_word * n2w (LENGTH h)) off t
      (const_writes a off h m)
Proof
  Induct \\ fs [const_writes_def,FORALL_PROD]
  \\ fs [ADD1] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem const_addresses_append:
  ∀xs ys dm a.
    const_addresses a (xs ++ ys) dm ⇔
    const_addresses a xs dm ∧
    const_addresses (a + bytes_in_word * n2w (LENGTH xs)) ys dm
Proof
  Induct \\ fs [const_addresses_def]
  \\ fs [ADD1] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem copy_words_correct:
  ∀words xs ys a off dm m.
    const_addresses a words dm ∧ good_dimindex (:'a) ⇒
    copy_words (LENGTH xs) (a:'a word) off
      (xs ++ const_words_to_bitmap words (LENGTH words) ++ ys) dm m =
    SOME (a + bytes_in_word * n2w (LENGTH words), const_writes a off words m)
Proof
  strip_tac
  \\ completeInduct_on ‘LENGTH words’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
  \\ rw [Once const_words_to_bitmap_def]
  THEN1
   (‘LENGTH words < dimindex (:α)’ by fs []
    \\ drule_all copy_words \\ fs [])
  THEN1 gvs [good_dimindex_def]
  \\ qabbrev_tac ‘h = (TAKE (dimindex (:α) − 1) words)’
  \\ qabbrev_tac ‘t = (DROP (dimindex (:α) − 1) words)’
  \\ gvs []
  \\ ‘LENGTH h < dimindex (:α)’ by fs [Abbr‘h’]
  \\ ‘const_addresses a h dm’ by
   (‘words = h ++ t’ by metis_tac [TAKE_DROP]
    \\ gvs [const_addresses_append])
  \\ drule_all copy_words
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ disch_then kall_tac
  \\ reverse IF_CASES_TAC THEN1 gvs [Abbr‘h’,LENGTH_TAKE]
  \\ first_x_assum (qspecl_then [‘t’,‘xs ++ chunk_to_bitmap h’,‘ys’,
       ‘a + bytes_in_word * n2w (LENGTH h)’,‘off’,‘dm’,
       ‘const_writes a off h m’] mp_tac)
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (‘words = h ++ t’ by metis_tac [TAKE_DROP]
    \\ gvs [const_addresses_append])
  \\ strip_tac \\ gvs []
  \\ ‘LENGTH t = LENGTH words + 1 - dimindex (:α)’ by
    (unabbrev_all_tac \\ fs [])
  \\ ‘LENGTH (chunk_to_bitmap h) = dimindex (:α)’ by
    fs [chunk_to_bitmap_def]
  \\ fs []
  \\ qpat_x_assum ‘LENGTH t = _’ (assume_tac o GSYM)
  \\ ‘dimindex (:α) − 1 = LENGTH h’ by fs [Abbr‘h’] \\ fs []
  \\ ‘words = h ++ t’ by metis_tac [TAKE_DROP]
  \\ gvs [] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [const_writes_append]
QED

(* ?
Theorem insert_bitmap_append:
  ∀bs xs new_bs i.
    insert_bitmap xs (bs,n) = ((new_bs,n'),i) ⇒
    ∃ys zs. new_bs = ys ++ xs ++ zs ∧ i = LENGTH ys
Proof
  Induct \\ rw [insert_bitmap_def]
  \\ TRY (qexists_tac ‘[]’ \\ fs [IS_PREFIX_APPEND] \\ NO_TAC)
  \\ pairarg_tac \\ gvs []
  \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys'’ \\ fs []
QED *)

Theorem comp_StoreConsts_correct:
  ^(get_goal "StoreConsts")
Proof
  gvs [wordSemTheory.evaluate_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt strip_tac \\ gvs [comp_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘0’
  \\ ‘t.use_store ∧ t.use_alloc ∧ good_dimindex (:'a)’ by fs [state_rel_def]
  \\ gvs [stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
          stackSemTheory.word_exp_def,post_alloc_conventions_def,call_arg_convention_def]
  \\ IF_CASES_TAC
  THEN1
   (qsuff_tac ‘F’ \\ fs []
    \\ fs [check_store_consts_opt_def]
    \\ gvs [state_rel_def,store_consts_stub_def])
  \\ gvs [store_const_sem_def]
  \\ IF_CASES_TAC THEN1 fs [state_rel_def] \\ fs []
  \\ fs [stackSemTheory.get_var_def,stackSemTheory.set_var_def,lookup_insert,
         FLOOKUP_UPDATE]
  \\ ‘FLOOKUP t.regs 2 = SOME (Word a) ∧ FLOOKUP t.regs 3 = SOME (Word off)’ by
    (fs [state_rel_def,get_var_def] \\ res_tac \\ ‘3 < k’ by fs [] \\ fs [])
  \\ fs [stackSemTheory.unset_var_def]
  \\ ‘LENGTH t.bitmaps < dimword (:α)’ by fs [state_rel_def]
  \\ ‘∃xs ys. t.bitmaps = xs ++ const_words_to_bitmap words (LENGTH words) ++ ys ∧
              LENGTH xs = i’ by (
    fs[insert_bitmap_def]>>rw[]>>
    fs[append_thm]>>
    drule isPREFIX_DROP>>
    disch_then(qspec_then`LENGTH(append bs)` mp_tac)>>
    simp[DROP_APPEND,DROP_LENGTH_NIL]>>
    DEP_REWRITE_TAC[DROP_DROP]>> simp[]>>
    drule IS_PREFIX_LENGTH>> simp[]>>
    strip_tac>>
    gvs [IS_PREFIX_APPEND]>>
    strip_tac>>
    qexists_tac`TAKE i t.bitmaps`>>qexists_tac`l'`>>simp[]>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>> pop_assum sym_sub_tac>>
    simp[])
  \\ gvs []
  \\ ‘s.mdomain = t.mdomain’ by fs [state_rel_def]
  \\ drule (GEN_ALL copy_words_correct)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [state_rel_def,set_var_def,unset_var_def,lookup_insert]
  \\ rpt strip_tac
  \\ TRY (res_tac \\ NO_TAC)
  \\ rpt (irule wf_insert)
  \\ rpt (irule wf_delete)
  \\ fs []\\ gvs [AllCaseEqs(),lookup_delete]
  \\ gvs [DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
  \\ fs [DIV_LT_X]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [DIV_EQ_X]
  \\ res_tac
  \\ rename1`nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rw [] \\ fs []
QED

(* ?
Theorem insert_bitmap_append:
  ∀bs xs new_bs i.
    insert_bitmap xs (bs,n) = ((new_bs,n'),i) ⇒
    ∃ys zs. new_bs = ys ++ xs ++ zs ∧ i = LENGTH ys
Proof
  Induct \\ rw [insert_bitmap_def]
  \\ TRY (qexists_tac ‘[]’ \\ fs [IS_PREFIX_APPEND] \\ NO_TAC)
  \\ pairarg_tac \\ gvs []
  \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys'’ \\ fs []
QED *)

Theorem comp_Move_correct:
  ^(get_goal "Move")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def]
  \\ fs[comp_def] \\ rveq
  \\ fs[evaluate_def]
  \\ last_x_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ rveq
  \\ simp[]
  \\ qabbrev_tac`mvs = MAP (DIV2 ## DIV2) moves`
  \\ `windmill mvs ∧ windmill moves ∧ (EVERY EVEN (MAP FST moves) ∧ EVERY EVEN (MAP SND moves))`
  by (
    simp[parmoveTheory.windmill_def,Abbr`mvs`]
    \\ simp[MAP_MAP_o,o_PAIR_MAP]
    \\ simp[GSYM MAP_MAP_o]
    \\ reverse conj_asm2_tac
    >- (
      qhdtm_x_assum`post_alloc_conventions`mp_tac
      \\ simp[convs_def,EVERY_MEM,reg_allocTheory.is_phy_var_def,EVEN_MOD2] )
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ rw[]
    \\ match_mp_tac EVEN_DIV2_INJ \\ simp[]
    \\ fs[EVERY_MEM])
  \\ simp[wMove_def]
  \\ qexists_tac`0` \\ simp[]
  \\ drule evaluate_wMoveAux_seqsem
  \\ simp[]
  \\ disch_then(qspec_then`parmove mvs`mp_tac)
  \\ qabbrev_tac`r = λx.
       case x of NONE => get_var (k+1) t
               | SOME i => get_var (2*i) s`
  \\ disch_then(qspec_then`r`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`r`]
    \\ conj_tac
    >- (
      `IS_SOME (get_vars (MAP SND moves) s)` by metis_tac[IS_SOME_EXISTS]
      \\ fs[IS_SOME_get_vars_EVERY]
      \\ fs[EVERY_FILTER,EVERY_MEM,MEM_MAP,PULL_EXISTS]
      \\ simp[MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
      \\ rw[] \\ imp_res_tac MEM_MAP_SND_parmove
      \\ pop_assum mp_tac
      \\ simp[Abbr`mvs`,MAP_MAP_o,o_PAIR_MAP]
      \\ fs[IS_SOME_EXISTS]
      \\ simp[MEM_MAP,PULL_EXISTS]
      \\ simp[DIV2_def,bitTheory.DIV_MULT_THM2]
      \\ rw[] \\ res_tac
      \\ qhdtm_x_assum`post_alloc_conventions`mp_tac
      \\ simp[convs_def,EVERY_MEM,reg_allocTheory.is_phy_var_def,EVEN_MOD2]
      \\ simp[MEM_MAP,PULL_EXISTS] )
    \\ conj_tac
    >- (
      qpat_abbrev_tac`ff = IS_SOME _`
      \\ every_case_tac \\ fs[]
      \\ Q.ISPEC_THEN`mvs`mp_tac(Q.GEN`mvs` parmove_not_use_temp_before_assign)
      \\ simp[] )
    \\ conj_tac
    >- (
      fs[EVERY_MEM,UNCURRY,PULL_FORALL]
      \\ rw[]
      \\ imp_res_tac (SIMP_RULE std_ss [MEM_MAP,PULL_EXISTS] MEM_MAP_SND_parmove)
      \\ imp_res_tac (SIMP_RULE std_ss [MEM_MAP,PULL_EXISTS] MEM_MAP_FST_parmove)
      \\ rfs[]
      \\ fs[Abbr`mvs`,MEM_MAP,EXISTS_PROD]
      \\ fs[wordLangTheory.max_var_def]
      \\ qmatch_assum_abbrev_tac`list_max ls < _`
      \\ qspec_then`ls`strip_assume_tac list_max_max
      \\ fs[EVERY_MEM,Abbr`ls`,MEM_MAP,PULL_EXISTS]
      \\ res_tac \\ fs[]
      \\ qmatch_abbrev_tac`DIV2 aa < bb`
      \\ qmatch_assum_abbrev_tac`aa ≤ cc`
      \\ `cc < 2 * bb` by simp[Abbr`bb`]
      \\ `aa < 2 * bb` by metis_tac[LESS_EQ_LESS_TRANS]
      \\ simp[DIV2_def]
      \\ simp[DIV_LT_X])
    \\ match_mp_tac ALL_DISTINCT_parmove
    \\ fs[parmoveTheory.windmill_def])
  \\ strip_tac \\ simp[]
  \\ last_assum(Q.ISPEC_THEN`r`mp_tac o MATCH_MP parmoveTheory.parmove_correct)
  \\ simp[parmoveTheory.eqenv_def]
  \\ strip_tac
  \\ qhdtm_x_assum`state_rel`mp_tac
  \\ rveq
  \\ qmatch_abbrev_tac`state_rel _ _ _ _ a _ _ _ ⇒ state_rel _ _ _ _ b _ _ _`
  \\ `a = b` suffices_by rw[]
  \\ simp[Abbr`a`,Abbr`b`]
  \\ qpat_abbrev_tac`ls = FILTER A B`
  \\ `MAP (seqsem (parmove mvs) r) ls =
      MAP (parsem (MAP (SOME ## SOME) mvs) r) ls`
  by (
    fs[MAP_EQ_f,Abbr`ls`,MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
    \\ rw[] \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
    \\ simp[FUN_EQ_THM,FORALL_PROD])
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[Abbr`ls`]
  \\ simp[MAP_REVERSE,FILTER_REVERSE]
  \\ drule TIMES2_DIV2_lemma
  \\ simp[] \\ disch_then kall_tac
  \\ simp[Abbr`mvs`]
  \\ Q.ISPEC_THEN`r`drule (Q.GEN`r`parsem_parmove_DIV2_lemma)
  \\ impl_tac >- simp[]
  \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC)
  \\ qpat_abbrev_tac`ls = FILTER _ _`
  \\ simp[set_vars_def]
  \\ simp[state_component_equality]
  \\ dep_rewrite.DEP_REWRITE_TAC[alist_insert_REVERSE]
  \\ conj_asm1_tac
  >- (
    simp[Abbr`ls`]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
    \\ match_mp_tac ALL_DISTINCT_parmove
    \\ simp[] )
  \\ fs[]
  \\ simp[parmoveTheory.parsem_def]
  \\ simp[ZIP_MAP]
  \\ simp[MAP_MAP_o]
  \\ simp[o_DEF]
  \\ `∀x. r (SOME x) = get_var (2 * x) s` by (simp[Abbr`r`] )
  \\ simp[]
  \\ simp[APPLY_UPDATE_LIST_ALOOKUP]
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (REVERSE ll)`
  \\ `ALL_DISTINCT (MAP FST ll)`
  by (
    simp[Abbr`ll`,MAP_MAP_o,o_DEF]
    \\ simp[GSYM o_DEF,GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ simp[alookup_distinct_reverse]
  \\ simp[Abbr`ll`]
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (MAP ff moves)`
  \\ Q.ISPEC_THEN`ff`mp_tac ALOOKUP_MAP_any
  \\ disch_then(qspec_then`SOME`mp_tac)
  \\ simp[Abbr`ff`]
  \\ disch_then(qspec_then`λx y. get_var (2 * DIV2 y) s`mp_tac)
  \\ disch_then(qspec_then`moves`mp_tac)
  \\ simp[INJ_DEF]
  \\ strip_tac
  \\ simp[Abbr`ls`]
  \\ qpat_abbrev_tac`ignore = MAP _ _`
  \\ simp[Once MAP_FILTER_IS_SOME]
  \\ simp[o_DEF]
  \\ qmatch_goalsub_abbrev_tac`MAP ff (FILTER _ _)`
  \\ qpat_abbrev_tac`ls = FILTER _ _`
  \\ `MAP ff ls =
      MAP (λx. THE (get_var (THE (ALOOKUP moves (THE x))) s)) ls`
  by (
    simp[MAP_EQ_f]
    \\ simp[Abbr`ls`,MEM_FILTER]
    \\ simp[Abbr`ff`,IS_SOME_EXISTS,PULL_EXISTS]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ Cases_on`ALOOKUP moves z`
    >- (
      fs[ALOOKUP_FAILS,MEM_MAP]
      \\ imp_res_tac(SIMP_RULE std_ss [MEM_MAP,PULL_EXISTS] MEM_MAP_FST_parmove)
      \\ fs[] \\ metis_tac[FST,PAIR] )
    \\ simp[]
    \\ AP_TERM_TAC \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[bitTheory.DIV_MULT_THM2,DIV2_def]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs[EVERY_MAP,EVERY_MEM]
    \\ res_tac \\ fs[EVEN_MOD2] )
  \\ pop_assum SUBST1_TAC
  \\ simp[Abbr`ignore`]
  \\ simp[Abbr`ls`]
  \\ match_mp_tac alist_insert_get_vars
  \\ conj_tac >- fs[parmoveTheory.windmill_def]
  \\ simp[]
  \\ conj_tac >- metis_tac[ALL_DISTINCT_parmove]
  \\ conj_tac >- fs[state_rel_def]
  \\ conj_tac >- metis_tac[MEM_MAP_FST_parmove]
  \\ metis_tac[parmove_preserves_moves]
QED

Theorem comp_Inst_correct:
  ^(get_goal "Inst")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ last_x_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ rveq
  \\ qexists_tac`0` \\ simp[]
  \\ fs[convs_def,wordLangTheory.max_var_def]
  \\ drule evaluate_wInst \\ simp[]
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED

Theorem comp_Assign_correct:
  ^(get_goal "Assign")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
QED

Theorem comp_Get_correct:
  ^(get_goal "Get")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def,get_store_def]
  \\ last_x_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ strip_tac \\ rveq \\ simp[]
  \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
  \\ rw[]
  \\ qexists_tac`0` \\ simp[]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`NONE` \\ simp[]
  \\ qmatch_goalsub_abbrev_tac `wRegWrite1 kont (2 * m)`
  \\ qmatch_goalsub_abbrev_tac `state_rel _ _ _ _ (set_var _ v _)`
  \\ drule_then(qspecl_then [`v`,`m`,`kont`] mp_tac) (GEN_ALL wRegWrite1_thm1)
  \\ unabbrev_all_tac
  \\ simp[stackSemTheory.evaluate_def]
  \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
  \\ impl_tac >- (fs[state_rel_def] \\ rfs[DOMSUB_FLOOKUP_THM])
  \\ metis_tac[]
QED

Theorem comp_Set_correct:
  ^(get_goal "wordLang$Set")
Proof
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ Cases_on`exp`>>fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ fs[wordSemTheory.word_exp_def]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[stackSemTheory.evaluate_def]
  \\ `t'.use_store` by fs[state_rel_def]
  \\ fs[]
  \\ irule state_rel_set_store \\ fs[]
QED

Theorem comp_OpCurrHeap_correct:
  ^(get_goal "OpCurrHeap")
Proof
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,the_words_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wRegWrite1_seq]
  \\ pairarg_tac \\ fs[]
  \\ `t'.use_store` by fs[state_rel_def]
  \\ simp[stackSemTheory.evaluate_def,stackSemTheory.word_exp_def]
  (*TODO remove by changing word_exp_def*)
  \\ fs[GSYM stackSemTheory.get_var_def]
  (*TODO remove by changing get_store_def*)
  \\ fs[wordSemTheory.get_store_def]
  \\ ‘FLOOKUP t'.store CurrHeap = FLOOKUP s.store CurrHeap’ by
    fs [state_rel_def,DOMSUB_FLOOKUP_THM] \\ fs []
  \\ drule (GEN_ALL evaluate_wStackStore_wReg1)
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `Word z` strip_assume_tac)
  \\ simp[]
QED

Theorem comp_Store_correct:
  ^(get_goal "Store")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
QED

Theorem comp_Tick_correct:
  ^(get_goal "Tick")
Proof
  REPEAT STRIP_TAC \\
  fs [comp_def] \\ rw[] \\
  fs[get_labels_def] \\
  qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,stackSemTheory.evaluate_def,comp_def]
  \\ rw []
  \\ simp[wordSemTheory.evaluate_def,stackSemTheory.evaluate_def,comp_def]
  \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
  \\ fs [state_rel_def,wordSemTheory.dec_clock_def,stackSemTheory.dec_clock_def]
  \\ metis_tac[]
QED

Theorem comp_MustTerminate_correct:
  ^(get_goal "MustTerminate")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,LET_DEF,
      stackSemTheory.evaluate_def,comp_def]
  \\ Cases_on `s.termdep = 0` \\ fs [state_rel_def]
QED

Theorem comp_Seq_correct:
  ^(get_goal "wordLang$Seq")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [get_labels_def]
  \\ `max_var c1 < 2 * f' + 2 * k /\ max_var c2 < 2 * f' + 2 * k` by
    (fs [wordLangTheory.max_var_def] \\ decide_tac)
  \\ `post_alloc_conventions k c1 /\
      post_alloc_conventions k c2 /\
      flat_exp_conventions c1 /\
      flat_exp_conventions c2` by fs [convs_def]
  \\ imp_res_tac comp_IMP_isPREFIX
  \\ imp_res_tac comp_IMP_LENGTH
  \\ rfs[]
  \\ reverse (Cases_on `res' = NONE`) \\ fs [] \\ rpt var_eq_tac
  THEN1 (
    first_x_assum drule \\ fs []
    \\ Cases_on`bs''`
    \\ disch_then drule \\ fs []
    \\ impl_tac >- (
      fs[get_labels_def]>>
      metis_tac[IS_PREFIX_TRANS] )
    \\ strip_tac
    \\ qexists_tac `ck` \\ fs [] \\ Cases_on `res` \\ fs []
    \\ Cases_on `res1 = NONE`
    \\ fs [stackSemTheory.evaluate_def,LET_THM])
  \\ first_x_assum drule \\ fs []
  \\ Cases_on`bs''`
  \\ disch_then drule \\ fs []
  \\ impl_tac >- (
    fs[get_labels_def]>>
    metis_tac[IS_PREFIX_TRANS] )
  \\ strip_tac
  \\ reverse (Cases_on `res1 = NONE`) \\ fs []
  >- (
    qexists_tac `ck`
    \\ last_x_assum kall_tac
    \\ `good_dimindex (:'a)` by fs [state_rel_def]
    \\ fs [Halt_EQ_compile_result,stackSemTheory.evaluate_def,LET_THM]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ `s.ffi = t.ffi` by fs [state_rel_def]
    \\ imp_res_tac evaluate_io_events_mono \\ fs []
    \\ imp_res_tac wordPropsTheory.evaluate_io_events_mono \\ fs []
    \\ rfs [] \\ fs [] \\ metis_tac [IS_PREFIX_TRANS,evaluate_stack_limit_stack_max])
  \\ first_x_assum drule \\ fs []
  \\ disch_then drule
  \\ impl_tac >- (
    fs[]>>imp_res_tac evaluate_mono>>fs[]>> rw[]
    >- (drule IS_PREFIX_LENGTH>>fs[])
    >- metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]
    >>
      fs[get_labels_def]>>
      metis_tac[SUBSET_TRANS,loc_check_SUBSET])
  \\ rw [] \\ fs []
  \\ fs [stackSemTheory.evaluate_def,LET_THM]
  \\ imp_res_tac stack_evaluate_add_clock_NONE \\ fs []
  \\ pop_assum (qspec_then `ck'` assume_tac)
  \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ `s.handler = s1'.handler` by
    (Q.ISPECL_THEN [`c1`,`s`] assume_tac evaluate_stack_swap>>rfs[])
  \\ fs[]
QED

Theorem comp_Return_correct:
  ^(get_goal "Return")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0` \\
  gvs[wordSemTheory.evaluate_def,AllCaseEqs()] \\
  gvs[comp_def,UNCURRY_EQ] \\
  `EVEN n` by (fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]) \\
  simp[evaluate_wStackLoad_seq] \\
  dxrule_all evaluate_wStackLoad_wReg1 \\
  rw[] \\
  simp[Once stackSemTheory.evaluate_def] \\
  DEP_REWRITE_TAC[evaluate_SeqStackFree] \\
  CONJ_ASM1_TAC >- (fs [state_rel_def] \\ decide_tac) \\
  fs [stackSemTheory.evaluate_def] \\
  `(t.stack_space + skip_free (k,f,f') ms) <= LENGTH t.stack`
      by fs[state_rel_def,skip_free_def] \\
  fs[] \\
  CONJ_TAC >- (
      fs[state_rel_def,flush_state_def] \\
      CONJ_TAC >- METIS_TAC[] \\
      CONJ_TAC >- (
        fs[stack_size_rel_def]>>rw[]
        >- (
          gvs[skip_free_def,num_stack_ret_def]>>
          imp_res_tac get_vars_length_lemma >>
          simp[])
        >- (
          (* should be provable with appropriate bounds and cancellation *)
          PURE_REWRITE_TAC[skip_free_def,num_stack_ret_def]>>
          imp_res_tac get_vars_length_lemma >>
          fs[list_max_def, wordLangTheory.max_var_def,GSYM MAX_DEF] >>
          fs[convs_def] >>
          qpat_x_assum `ms = _` SUBST_ALL_TAC >>
          fs[list_max_GENLIST_evens2] >>
          fs[GSYM LEFT_ADD_DISTRIB] >>
          gvs[IS_SOME_EXISTS,the_eqn] >>
          Cases_on `f' = 0` >> fs[])) >>
      CONJ_TAC >- (
        simp[skip_free_def,num_stack_ret_def]>>
        imp_res_tac get_vars_length_lemma >>
        simp[] >>
        `f = (f - (LENGTH ms + 1 - k) + (LENGTH ms + 1 - k))` suffices_by fs[DROP_DROP_EQ] >>
        fs[list_max_def, wordLangTheory.max_var_def,GSYM MAX_DEF] >>
        fs[convs_def] >>
        qpat_x_assum `ms = _` SUBST_ALL_TAC >>
        fs[list_max_GENLIST_evens2] >>
        fs[GSYM LEFT_ADD_DISTRIB] >>
        gvs[IS_SOME_EXISTS,the_eqn] >>
        Cases_on `f' = 0` >> fs[]) >>
      simp[lookup_def]) \\
  rpt strip_tac \\
  `get_var (EL i ms) s = SOME (EL i ys)`
    by(
       qpat_x_assum `get_vars _ _ = _` mp_tac \\
       qpat_x_assum `i < LENGTH ys` mp_tac \\
       rpt (pop_assum kall_tac) \\
       map_every qid_spec_tac [`i`,`ys`,`ms`] \\
       Induct_on `i` \\ fs[] \\ rw[]
       >- (Cases_on `ms` >> gvs[get_vars_def,AllCaseEqs()])
       >- (Cases_on `ys` >> fs[] >>
           Cases_on `ms` >> gvs[get_vars_def,AllCaseEqs()])
           ) \\
  `EL i ms = 2 * ((i + 1))`
     by(
       imp_res_tac get_vars_length_lemma \\
       fs[convs_def] \\
       qpat_assum `ms = _` (ONCE_REWRITE_TAC o single) \\
       DEP_REWRITE_TAC[EL_GENLIST] \\ fs[]) \\
  pop_assum SUBST_ALL_TAC \\
  pop_assum (assume_tac o SRULE[get_var_def]) \\
  fs[state_rel_def] \\
  first_x_assum drule \\
  simp[EVEN_DOUBLE] \\
  IF_CASES_TAC >- simp[] >>
  strip_tac >> simp[] \\
  imp_res_tac LLOOKUP_TAKE_IMP \\
  fs[LLOOKUP_DROP,skip_free_def,num_stack_ret_def] \\
  gvs[] \\
  imp_res_tac get_vars_length_lemma \\
  fs[] \\
  `f' + k > LENGTH ms`
     by(
        fs[convs_def,wordLangTheory.max_var_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS] \\
        rveq \\ fs[list_max_def] \\
        qpat_x_assum `ms = GENLIST _ _` SUBST_ALL_TAC \\
        fs[list_max_GENLIST_evens2]) \\
      fs[]
QED

Theorem stack_rel_aux_stack_size:
  !len k frame bits.
  stack_rel_aux len k frame bits ==>
  the (handler_val bits) (stack_size frame) = handler_val bits
Proof
  ho_match_mp_tac (fetch "-" "stack_rel_aux_ind") >>
  rw[stack_rel_aux_def,stack_size_eq,handler_val_def,the_eqn,OPTION_MAP2_DEF,
     IS_SOME_EXISTS,CaseEq "option"] >>
  res_tac >> fs[]
QED

Theorem abs_stack_CONS_NIL:
  abs_stack bm (x::rest) [] l = NONE
Proof
  Cases_on `l` >> Cases_on `x` >>
  rename1 `StackFrame _ _ handler` >> Cases_on `handler` >>
  rw[abs_stack_def]
QED

Triviality SUB_ADD_EQ:
  a <= b ==> a + (b - a:num) = b
Proof
  DECIDE_TAC
QED

Theorem abs_stack_LENGTH:
  !bitmaps wstack tstack lens astack.
  abs_stack bitmaps wstack tstack lens = SOME astack ==>
  handler_val astack = LENGTH tstack
Proof
 recInduct abs_stack_ind >>
 rw[abs_stack_def,handler_val_def,CaseEq"bool",CaseEq"option",CaseEq"list"] >>
 rw[handler_val_def]
QED

Theorem abs_stack_empty':
  abs_stack bs xs [] lens = SOME stack <=> F
Proof
  rw[EQ_IMP_THM] >>
  strip_tac >>
  imp_res_tac abs_stack_LENGTH >>
  Cases_on `stack` >> fs[handler_val_def] >>
  PairCases_on `h` >> Cases_on `h0` >> fs[handler_val_def]
QED

Theorem comp_Raise_correct:
  ^(get_goal "wordLang$Raise")
Proof
  cheat (*
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,jump_exc_def]
  \\ `1 < k` by (fs [state_rel_def] \\ decide_tac)
  \\ qpat_x_assum `xxx = (aa,bb)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ qpat_x_assum `_ = (_,s1)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ pop_assum mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ qexists_tac `1`
  \\ rename1 `LASTN (s.handler + 1) s.stack =
        StackFrame o' ll0 ll (SOME (h1,l3,l4))::rest`
  \\ fs[comp_def] \\ rw[]
  \\ fs [wordSemTheory.evaluate_def,LET_DEF,
      stackSemTheory.evaluate_def,jump_exc_def,
      stackSemTheory.find_code_def]
  \\ `lookup raise_stub_location t.code = SOME (raise_stub k)` by fs [state_rel_def]
  \\ fs []
  \\ pop_assum kall_tac
  \\ fs [stackSemTheory.dec_clock_def,raise_stub_def,wordLangTheory.max_var_def]
  \\ fs [state_rel_def,LET_DEF,push_locals_def,stackSemTheory.evaluate_def,LET_THM]
  \\ fs [DROP_DROP_EQ] \\ fs [stack_rel_def]
  \\ qpat_x_assum` A ⇒ B` mp_tac
  \\ impl_tac >- (
    `s.handler+1 ≤ LENGTH s.stack` by DECIDE_TAC>>
    imp_res_tac LASTN_HD>>
    ntac 3 (pop_assum sym_sub_tac)>>
    fs[is_handler_frame_def])
  \\ strip_tac
  \\ fs[LET_DEF,get_var_set_var]
  \\ fs [stackSemTheory.set_var_def]
  \\ `(LENGTH t.stack - handler_val (LASTN (s.handler+1) stack)) < dimword (:'a)`
       by decide_tac \\ fs []
  \\ `SORTED (\x y. FST x > FST y) ll` by
    (imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [sorted_env_def])
  \\ `LENGTH t.stack - handler_val (LASTN (s.handler+1) stack) + 3 <= LENGTH t.stack` by
       (imp_res_tac stack_rel_raise \\ rfs[]
        \\ PairCases_on`payload`\\simp[handler_val_def])
  \\ IF_CASES_TAC \\ fs []
  \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,stackSemTheory.set_store_def]
  \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,push_locals_def,lookup_def]
  \\ drule_at (Pos (el 5)) stack_rel_raise
  \\ rpt (disch_then (drule_at Any))
  \\ simp[]
  \\ strip_tac
  \\ fsrw_tac[][]
  \\ conj_tac THEN1 metis_tac[]
  \\ conj_tac THEN1 (
     imp_res_tac stack_rel_aux_stack_size >>
     rw[the_eqn] >> PURE_TOP_CASE_TAC >> rw[handler_val_def] >>
     qpat_x_assum `IS_SOME _ ==> IS_SOME (stack_size _)` assume_tac >>
     fsrw_tac[][IS_SOME_EXISTS,miscTheory.the_def] >>
     drule_then drule LASTN_stack_size_SOME >>
     impl_tac >- simp[] >>
     strip_tac >>
     fs[stack_size_eq2] >>
     Cases_on `payload` >> fs[handler_val_def,stack_size_frame_def] >>
     rveq >> fs[miscTheory.the_def]
   )
  \\ conj_tac THEN1
     (
       strip_tac >> last_x_assum drule >> simp[IS_SOME_EXISTS] >>
       strip_tac >>
       drule_then drule LASTN_stack_size_SOME >>
       impl_tac >- simp[] >>
       rw[stack_size_eq2,stack_size_frame_def]
     )
  \\ conj_tac THEN1
     (
       rw [handler_val_def]>>
       imp_res_tac stack_rel_aux_stack_size >>
       rw[the_eqn] >>
       PURE_TOP_CASE_TAC >> rw[handler_val_def] >>
       Cases_on `payload` >>
       fsrw_tac[][miscTheory.the_def,handler_val_def,stack_size_eq] >>
       `LENGTH t.stack -
        (LENGTH r + (handler_val (LASTN s.handler stack) + 4)) <=
        LENGTH t.stack` by intLib.COOPER_TAC >>
       simp[SUB_RIGHT_ADD] >>
       reverse IF_CASES_TAC
       >- intLib.COOPER_TAC >>
       imp_res_tac abs_stack_LENGTH >>
       qpat_x_assum `handler_val (_::_) = LENGTH (DROP _ _)` (mp_tac o GSYM) >>
       simp[handler_val_def,LENGTH_DROP]
     )
  \\ conj_tac THEN1 (
    fs [sorted_env_def] \\ Cases_on `env_to_list (union (fromAList ll) (fromAList ll0)) (K I)`
    \\ imp_res_tac env_to_list_K_I_IMP \\ fs [])
  \\ conj_tac >-
     (rpt (qpat_x_assum`∀x. _`kall_tac)
     \\imp_res_tac LASTN_LENGTH_BOUNDS
     \\imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
     \\imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [])
  \\ reverse CONJ_TAC>- (
    fs [get_var_def,FLOOKUP_UPDATE,convs_def]>>
    `1 < k` by fs[state_rel_def]>>
    res_tac>>qpat_x_assum`!n.P` kall_tac>>rfs[])
  \\ rfs[]
  \\ rw[]
  \\ Cases_on`h1+1 = SUC (LENGTH rest)`>- (
      fs[is_handler_frame_def])>>
  `h1 < LENGTH rest ∧ SUC(LENGTH rest) - (h1+1) = SUC(LENGTH rest - (h1+1))` by DECIDE_TAC>>
  fs[]
  \\ sg `h1 <= LENGTH (LASTN (s.handler+1) stack)`
  \\ fs [LASTN_CONS]
  \\ imp_res_tac abs_stack_IMP_LENGTH \\ fs[] >>
  simp[LASTN_CONS] >>
  simp[FLOOKUP_UPDATE] *)
QED

Triviality evaluate_const_inst:
  state_rel ac k f f' s t lens extra  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(const_inst (k + 1) i,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens extra∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  stackSem$get_var (k + 1) t' = (SOME (Word i))
Proof
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.inst_def] >>
    simp[stackSemTheory.assign_def] >>
    simp[stackSemTheory.word_exp_def]
QED

Triviality evaluate_const_inst_clock:
  evaluate(const_inst k i,t with clock:= clk) =
  (I ## (\t. t with clock := clk)) (evaluate(const_inst k i,t))
Proof
  fs[stackSemTheory.evaluate_def] >>
  Cases_on `inst (Const k i) t` >>
  fs[]
QED

Theorem comp_If_correct:
  ^(get_goal "wordLang$If")
Proof
  rw[] >> fs[comp_def]>>
  rpt(pairarg_tac>>gvs[])>>
  rename1`_ = (q1,bss)`>>
  Cases_on`bss`>>
  qpat_x_assum`evaluate _ =_` mp_tac >>
  simp[evaluate_def, CaseEq "option", CaseEq"word_loc"]>>rw[]>>
  (* prevent splitting *)
  qmatch_asmsub_abbrev_tac`ifcase = (res,s1)`>>
  `EVEN r1 ∧ (case ri of Reg r => EVEN r | _ => T)` by (
    Cases_on`ri`>>
    fs[convs_def,EVEN_MOD2,reg_allocTheory.is_phy_var_def]
  )>>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  gvs[wordSemTheory.get_var_imm_def]
  >~ [`If _ _ (Reg _) _ _`]
  >- ( (* Reg case *)
    fs[get_labels_wStackLoad,get_labels_def]>>
    simp[wStackLoad_append]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1>>
    strip_tac >>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg2>>
    strip_tac >>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock] >>
    simp[stackSemTheory.get_var_imm_def,word_cmp_Word_Word]>>
    gvs[markerTheory.Abbrev_def,word_cmp_Word_Word,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (drule )>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[]))
  >~[`If _ _ (Imm _) _ _`]
  >- (
    fs[get_labels_wStackLoad,get_labels_def]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1>>
    rw[]>>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock,stackSemTheory.get_var_imm_def]>>
    simp[word_cmp_Word_Word] >>
    gvs[markerTheory.Abbrev_def,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (drule )>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[])
     )
  >- (
    fs[get_labels_wStackLoad,get_labels_def]>>
    dxrule_all evaluate_const_inst>>
    disch_then (qspec_then `i` mp_tac) >>
    rw[] >>
    simp[Once stackSemTheory.evaluate_def,evaluate_const_inst_clock]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1 >>
    rw[]>>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.get_var_imm_def,word_cmp_Word_Word] >>
    gvs[markerTheory.Abbrev_def,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac IS_PREFIX_LENGTH>>fs[])
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule_at Any)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac IS_PREFIX_LENGTH>>fs[])
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[])
     )
QED
val _ = get_time timer;

Theorem comp_LocValue_correct:
  ^(get_goal "wordLang$LocValue")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ qexists_tac`0` \\ simp[]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`NONE` \\ simp[]
  \\ match_mp_tac wRegWrite1_thm1_weak
  \\ simp[stackSemTheory.evaluate_def]
  \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
  \\ imp_res_tac state_rel_code_domain
  \\ fs[SUBSET_DEF]
  \\ Cases_on `loc_check t.code (l1,0)` \\ fs []
  \\ fs [wRegWrite1_def]
  \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs [IN_DEF]
  \\ fs [loc_check_def,IN_DEF]
QED

Theorem EXISTS_PULL_FORALL1:
  ((?x. !y . (Abbrev (y = P)) ==> Q x y) <=> (!y. (Abbrev (y = P)) ==> ?x. Q x y))
Proof
  METIS_TAC[]
QED

Theorem EXISTS_PULL_FORALL2:
  ((?x. !y z. P = (y, z) ==> Q x y z) <=> (!y z. P = (y, z) ==> ?x. Q x y z))
Proof
Cases_on `P` >> simp[]
QED

Theorem EXISTS_PULL_FORALL3:
  ((?x. !y z a. P = (y, z, a) ==> Q x y z a) <=> (!y z a. P = (y, z, a) ==> ?x. Q x y z a))
Proof
PairCases_on `P` >> simp[]
QED

Theorem comp_Install_correct:
  ^(get_goal "wordLang$Install")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac`0` \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ gvs[convs_def,case_eq_thms,UNCURRY_EQ]
  \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac \\ simp[Once stackSemTheory.evaluate_def]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac \\ simp[Once stackSemTheory.evaluate_def]
  \\ imp_res_tac state_rel_get_var_imp' \\ fs[]
  \\ (rpt (pop_assum (fn x => (if is_forall (concl x) then kall_tac x else NO_TAC))))
  \\ `4 < k` by fs[state_rel_def]
  \\ fs[]
  \\ `t''.code_buffer = s.code_buffer /\
     t''.data_buffer = s.data_buffer /\
     t''.use_stack` by fs[state_rel_def]
  \\ full_simp_tac(srw_ss())[stackSemTheory.evaluate_def]
  \\ qhdtm_assum`state_rel`(fn th =>
       let val conjs = th |> REWRITE_RULE[state_rel_def] |> CONJUNCTS
           val conjs =(filter ((fn tm => is_eq tm andalso is_pabs(rhs tm)) o concl) conjs)
       in
           map_every assume_tac conjs
       end)
  \\ full_simp_tac(srw_ss())[]
  \\ rename1 `(cfg,(k',prog)::progs)`
  \\ LET_ELIM_TAC
  \\ fs[EXISTS_PULL_FORALL1,EXISTS_PULL_FORALL2,EXISTS_PULL_FORALL3]
  \\ rpt strip_tac
  \\ `? prog' progs'. progs'' = (k',prog')::progs'`
      by (Cases_on `prog`
      \\ fs[compile_word_to_stack_def]
      \\ rpt (pairarg_tac \\ gvs[]))
  \\ fs[]
  \\ fs[CONV_RULE (LHS_CONV SYM_CONV) UNCURRY_EQ]
  \\ gvs[Abbr`new_oracle`]
  \\ fs[shift_seq_def]
  \\ Cases_on `s.compile_oracle 1` >> gvs[]
  \\ pairarg_tac \\ fs[]
  \\ qpat_x_assum`compile_word_to_stack ac k r _ = _`kall_tac
  \\ qmatch_assum_rename_tac`compile_word_to_stack ac k ps (_,_) = (ps',_)`
  \\ fs[state_rel_def]
  \\ CONJ_TAC
  >- (
    qx_gen_tac`z`
    \\ last_x_assum(qspec_then`0`kall_tac)
    \\ last_assum(qspec_then`0`mp_tac)
    \\ last_x_assum(qspec_then`z+1`mp_tac)
    \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rw[] \\ gvs[]
    \\ Cases_on `bm`
    \\ drule (GEN_ALL compile_word_to_stack_IMP_LENGTH)
    \\ fs[])
  \\ conj_tac
  >- (
    simp[domain_union,domain_fromAList]
    \\ imp_res_tac MAP_FST_compile_word_to_stack
    \\ rw[INSERT_UNION_EQ]
    \\ fs[] )
  \\ conj_tac
  >- (
    fs[lookup_union,lookup_fromAList]
    \\ rpt gen_tac
    \\ reverse TOP_CASE_TAC
    >- (
      strip_tac \\ rveq
      \\ last_x_assum drule
      \\ fs[]
      \\ strip_tac \\ fs[]
      \\ asm_exists_tac \\ fs[]
      \\ fs[IS_PREFIX_APPEND]
      \\ fs[lookup_def,the_eqn]
      \\ qexists_tac`l' ++append (FST bm)`
      \\ simp[DROP_APPEND]
      \\ `i - (LENGTH (append bs') + LENGTH t.bitmaps) = 0` by
        fs[]
      \\ simp[])
    \\ strip_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ last_x_assum(qspec_then`0`kall_tac)
    \\ last_x_assum(qspec_then`0`mp_tac)
    \\ simp[EVERY_MEM]
    \\ strip_tac
    \\ res_tac \\ fs[]
    \\ Cases_on`bm`
    \\ drule compile_word_to_stack_IMP_ALOOKUP
    \\ disch_then drule
    \\ fs[]
    \\ disch_then(qspec_then`t.bitmaps ++ append q`mp_tac)
    \\ simp[DROP_APPEND,DROP_LENGTH_NIL]
    \\ strip_tac
    \\ asm_exists_tac \\ simp[]
    \\ CASE_TAC
    \\ fs[EXTENSION,domain_lookup]
    \\ last_x_assum(qspec_then`n'`mp_tac)
    \\ simp[lookup_def,the_eqn]
  )
  \\ conj_tac >- simp[lookup_union]
  \\ conj_tac >- simp[lookup_union]
  \\ conj_tac >- (
    fs[buffer_flush_def]
    \\ rveq \\ fs[] \\rfs[] )
  \\ conj_tac >- ( Cases_on`t.bitmaps` \\ gvs[] )
  \\ conj_tac >- ( Cases_on`t.bitmaps` \\ gvs[] )
  \\ conj_tac >- (
    match_mp_tac wf_insert
    \\ gvs[cut_env_def,case_eq_thms,cut_envs_def,cut_names_def]
    \\ match_mp_tac wf_union
    \\ simp[])
  \\ conj_tac >- ( fs[stack_size_rel_def])
  \\ conj_tac >- (
    fs[stack_rel_def]
    \\ metis_tac[abs_stack_bitmaps_prefix] )
  \\ fs[lookup_insert]
  \\ rpt gen_tac
  \\ gvs[cut_env_def,cut_envs_def,cut_names_def,case_eq_thms,lookup_union,lookup_inter]
  \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
  \\ strip_tac \\ rveq \\ fs[]
  \\ fs[EVERY_MAP,EVERY_MEM,MEM_toAList,FORALL_PROD]
  \\ rpt(first_x_assum drule)
  \\ simp[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ rveq \\ fs[TWOxDIV2]
  \\ rfs[]
QED

Theorem comp_CodeBufferWrite_correct:
  ^(get_goal "wordLang$CodeBufferWrite")
Proof
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ fs[stackSemTheory.evaluate_def]
  \\ `t''.code_buffer = s.code_buffer` by fs[state_rel_def]
  \\ fs[]
  \\ fs[state_rel_def]
  \\ gvs[]
  \\ metis_tac[]
QED

Theorem comp_DataBufferWrite_correct:
  ^(get_goal "wordLang$DataBufferWrite")
Proof
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ fs[stackSemTheory.evaluate_def]
  \\ `t''.use_stack` by fs[state_rel_def]
  \\ `t''.data_buffer = s.data_buffer` by fs[state_rel_def]
  \\ fs[]
  \\ fs[state_rel_def,buffer_write_def]
  \\ gvs[]
  \\ metis_tac[]
QED

Theorem comp_FFI_correct:
  ^(get_goal "wordLang$FFI")
Proof
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [EVAL ``post_alloc_conventions k (FFI ffi_index ptr1 len1 ptr2 len2 names)``]
  \\ rw [] \\ fs [] \\ rw []
  \\ fs [wordSemTheory.evaluate_def]
  \\ qpat_x_assum `aaa = (res,s1)` mp_tac
  \\ rpt (ntac 2 (TOP_CASE_TAC \\ fs []))
  \\ fs [LET_DEF] \\ fs [] \\ rw [] \\ fs []
  \\ fs [comp_def]
  \\ rw[]
  \\ fs[stackSemTheory.evaluate_def]
  \\ fs [stackSemTheory.get_var_def]
  \\ `FLOOKUP t.regs 1 = get_var 2 s /\
      FLOOKUP t.regs 2 = get_var 4 s` by
   (fs [state_rel_def,LET_DEF,wordSemTheory.get_var_def] \\ res_tac
     \\ `4 < k * 2 /\ 1 < k` by decide_tac \\ fs [DIV_LT_X]) \\ fs []
  \\ `FLOOKUP t.regs 3 = get_var 6 s /\
      FLOOKUP t.regs 4 = get_var 8 s` by
   (fs [state_rel_def,LET_DEF,wordSemTheory.get_var_def] \\ res_tac
    \\ `8 < k * 2 /\ 6 < k * 2` by decide_tac \\ fs [DIV_LT_X]) \\ fs []
  \\ `t.be = s.be /\ t.mdomain = s.mdomain /\
      s.memory = t.memory /\ s.ffi = t.ffi /\
      s.sh_mdomain = t.sh_mdomain` by
        fs [state_rel_def] \\ fs [LET_THM]
  \\ qexists_tac `0` \\ fs []
  \\ fs [state_rel_def,LET_THM]
  \\ conj_tac THEN1 metis_tac[]
  \\ conj_tac
  >- (
    gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()]
    \\ simp[wf_union])
  \\ ntac 3 strip_tac
  \\ gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()]
  \\ fs [lookup_union,lookup_inter_alt,AllCaseEqs()]
  \\ fs [CONV_RULE (DEPTH_CONV ETA_CONV) (GSYM toAList_def)
         |> INST_TYPE [``:'a``|->``:unit``] |> SIMP_RULE (srw_ss()) []]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,DIV_LT_X,FORALL_PROD,MEM_toAList]
  \\ fs [domain_lookup] \\ res_tac
  \\ `~(n' < k * 2)` by decide_tac \\ fs []
QED

Theorem flat_exp_conventions_ShareInst_exp_simp:
  flat_exp_conventions (ShareInst op v exp) ==>
  (?ad.exp = Var ad) \/
  (?ad offset. exp = Op Add [Var ad; Const offset])
Proof
  gvs[DefnBase.one_line_ify NONE flat_exp_conventions_def] >>
  rpt (every_case_tac >> fs[])
QED

Theorem word_exp_Op_Add_0:
  wordSem$word_exp s exp = SOME $ Word x <=>
    word_exp s (Op Add [exp;Const 0w]) = SOME $ Word x
Proof
  eq_tac >>
  gvs[wordSemTheory.word_exp_def,the_words_def,
    AllCaseEqs(),wordLangTheory.word_op_def] >>
  rpt strip_tac >>
  gvs[]
QED

Theorem evaluate_ShareInst_Var_eq_Op_Add:
  wordSem$evaluate (ShareInst op v (Var ad),s) =
    evaluate (ShareInst op v (Op Add [Var ad;Const 0w]),s)
Proof
  gvs[wordSemTheory.evaluate_def] >>
  TOP_CASE_TAC
  >- (
    TOP_CASE_TAC >>
    drule word_exp_Op_SOME_Word >>
    rpt strip_tac >>
    fs[GSYM word_exp_Op_Add_0] ) >>
  TOP_CASE_TAC
  >- (
    drule $ iffLR word_exp_Op_Add_0 >>
    simp[] ) >>
  TOP_CASE_TAC  >>
  drule word_exp_Op_SOME_Word >>
  rpt strip_tac >>
  fs[GSYM word_exp_Op_Add_0]
QED

Theorem share_load_lemma1:
  share_inst op (2 * v) ad' s = (res,s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  k <= v /\
  (op = Load \/ op = Load8 \/ op = Load32) /\
  res <> SOME Error ==>
  ?t1. sh_mem_op op k ad' t =
      (OPTION_MAP compile_result res, t1) /\
  (((?f. (res = SOME $ wordSem$FinalFFI f) /\
    (s1.ffi = t1.ffi) /\ (s1.clock = t1.clock))) \/
  (res = NONE /\
    state_rel ac k f f' s1
      (t1 with stack := (LUPDATE (THE $ FLOOKUP t1.regs k)
        (t1.stack_space + (f + k - (v + 1))) t1.stack)) lens 0 /\
      (?x. FLOOKUP t1.regs k = SOME x) /\
      (t1.stack_space = t.stack_space) /\
      (LENGTH t1.stack = LENGTH t.stack)))
Proof
  qpat_abbrev_tac `ops = (op = _ \/ op = _ \/ op = _)` >>
  rpt strip_tac >>
  `t.sh_mdomain = s.sh_mdomain /\
   t.ffi = s.ffi /\ t.clock = s.clock` by fs[state_rel_def] >>
  gvs[Abbr`ops`,share_inst_def,sh_mem_op_def,
    sh_mem_load_def,sh_mem_load_byte_def,
    sh_mem_load32_def,sh_mem_store32_def,
    stackSemTheory.sh_mem_load_byte_def,
    stackSemTheory.sh_mem_load32_def,
    stackSemTheory.sh_mem_load_def,
    DefnBase.one_line_ify NONE sh_mem_set_var_def,
    AllCaseEqs()] >>
  fs[FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `state_rel _ _ _ _ (set_var _ WORD _ with ffi := new_ffi)  t' _ _` >>
  qabbrev_tac `t'' = t with ffi := new_ffi` >>
  `t' = set_var k WORD t'' with stack := t'.stack`
     by fs[Abbr`t'`,Abbr`t''`,Abbr`WORD`,stackSemTheory.set_var_def] >>
   pop_assum (SUBST_TAC o single) >>
  fs[Abbr`t'`] >>
  full_simp_tac(bool_ss)[state_rel_set_var_k,
  GSYM wordPropsTheory.set_var_with_const,GSYM set_var_with_const] >>
  irule state_rel_set_var2 >> fs[Abbr `t''`] >>
  fs[state_rel_def] >> gvs[] >>
  METIS_TAC[]
QED

Theorem share_load_lemma2:
  share_inst op (2 * v) ad' s = (res,s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < k /\
  (op = Load \/ op = Load8 \/ op = Load32) /\
  res <> SOME Error ==>
  ?t1.
    sh_mem_op op v ad' t =
      (OPTION_MAP compile_result res, t1) /\
    ((?f. (res = SOME $ wordSem$FinalFFI f) /\
      (s1.ffi = t1.ffi) /\ (s1.clock = t1.clock)) \/
    (res = NONE /\
      state_rel ac k f f' s1 t1 lens 0))
Proof
  rpt strip_tac >>
  `s.sh_mdomain = t.sh_mdomain /\
    s.ffi = t.ffi /\
    s.clock = t.clock` by fs[state_rel_def] >>
  gvs[share_inst_def,sh_mem_op_def,
    sh_mem_load_def,sh_mem_load_byte_def,
    sh_mem_load32_def,sh_mem_store32_def,
    stackSemTheory.sh_mem_load_byte_def,
    stackSemTheory.sh_mem_load32_def,
    stackSemTheory.sh_mem_load_def,AllCaseEqs(),
    DefnBase.one_line_ify NONE sh_mem_set_var_def] >>
  rpt strip_tac >>
  fs[PULL_EXISTS] >>
  gvs[state_rel_def,set_var_def,state_component_equality] >>
  (conj_tac >- metis_tac[] >>
  conj_tac >- simp[wf_insert] >>
  simp[lookup_insert] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(),EVEN_DOUBLE]
  >-  simp[FLOOKUP_UPDATE] >>
  IF_CASES_TAC >>
  first_x_assum drule >>
  gvs[FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  IF_CASES_TAC >>
  gvs[EVEN_EXISTS])
QED

Theorem share_store_lemma1:
  share_inst op (2 * v) ad' s = (res,s1) /\
  state_rel ac k f f' s t lens 0 /\
  ~(v < k) /\
  (op = Store \/ op = Store8 \/ op = Store32) /\
  res <> SOME Error ==>
  ?t1.
    sh_mem_op op (k + 1) ad'
      (t with
        regs := t.regs |+
          (k+1,EL (t.stack_space + (f + k - (v + 1)))
                t.stack)) =
      (OPTION_MAP compile_result res,t1) /\
    ((?fv. (res = SOME $ wordSem$FinalFFI fv) /\
      (s1.ffi = t1.ffi) /\ (s1.clock = t1.clock)) \/
    (res = NONE /\
      state_rel ac k f f' s1 t1 lens 0))
Proof
  rpt strip_tac >>
  (`s.sh_mdomain = t.sh_mdomain /\
   s.ffi = t.ffi /\
   s.clock = t.clock` by fs[state_rel_def] >>
  gvs[share_inst_def,sh_mem_op_def,
    sh_mem_store_def,sh_mem_store_byte_def,
    sh_mem_load32_def,sh_mem_store32_def,
    stackSemTheory.sh_mem_store_byte_def,
    stackSemTheory.sh_mem_store32_def,
    stackSemTheory.sh_mem_store_def,AllCaseEqs(),
    PULL_EXISTS] >>
  gvs[stackSemTheory.get_var_def,FLOOKUP_UPDATE] >>
  `EL (t.stack_space + (f + k − (v + 1))) t.stack = Word v'` by (
    gvs[get_var_def,state_rel_def] >>
    last_x_assum drule >>
    rpt strip_tac >>
    gvs[] >>
    drule LLOOKUP_TAKE_IMP >>
    simp[LLOOKUP_DROP,LLOOKUP_THM] ) >>
  rpt strip_tac >>
  gvs[] >>
  gvs[state_rel_def,set_var_def,state_component_equality] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  IF_CASES_TAC >>
  simp[FLOOKUP_UPDATE] >>
  first_x_assum drule >>
  gvs[])
QED

Theorem share_store_lemma2:
  share_inst op (2 * v) ad' s = (res,s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < k /\
  (op = Store \/ op = Store8 \/ op = Store32) /\
  res <> SOME Error ==>
  ?t1.
    sh_mem_op op v ad' t =
      (OPTION_MAP compile_result res, t1) /\
    ((?fv. (res = SOME $ wordSem$FinalFFI fv) /\
      (s1.ffi = t1.ffi) /\ (s1.clock = t1.clock)) \/
    (res = NONE /\
      state_rel ac k f f' s1 t1 lens 0))
Proof
  rpt strip_tac >>
  (`s.sh_mdomain = t.sh_mdomain /\
    s.ffi = t.ffi /\
    s.clock = t.clock` by fs[state_rel_def] >>
  gvs[share_inst_def,sh_mem_op_def,
    sh_mem_store_def,sh_mem_store_byte_def,
    sh_mem_load32_def,sh_mem_store32_def,
    stackSemTheory.sh_mem_store_byte_def,
    stackSemTheory.sh_mem_store32_def,
    stackSemTheory.sh_mem_store_def,AllCaseEqs()] >>
  rpt strip_tac >>
  fs[PULL_EXISTS] >>
  gvs[state_rel_def,set_var_def,state_component_equality] >>
  simp[GSYM PULL_EXISTS] >>
  first_assum $ irule_at Any >>
  fs[GSYM get_var_def,stackSemTheory.get_var_def] >>
  first_x_assum drule >>
  gvs[] >>
  rpt strip_tac >>
  metis_tac[])
QED

Theorem evaluate_ShareInst_Load:
  evaluate (ShareInst op (2 * v)
    (Op Add [Var (2 * ad);Const offset]),s) = (res,s1) /\
  res <> SOME Error /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k /\
  (op = Load \/ op = Load8 \/ op = Load32) ==>
  ?ck t1.
    evaluate
      (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
        t with clock := ck + t.clock) =
        (OPTION_MAP compile_result res,t1) /\
    ((?fv. res = SOME (FinalFFI fv) /\
        s1.ffi = t1.ffi /\ s1.clock = t1.clock) \/
    (res = NONE /\ state_rel ac k f f' s1 t1 lens 0))
Proof
  rpt strip_tac >>
  gvs[evaluate_def,wShareInst_def,AllCaseEqs()]
  >> (
    pairarg_tac >>
    gvs[word_exp_def,AllCaseEqs(),the_words_def,GSYM get_var_def] >>
    simp[evaluate_wStackLoad_seq]>>
    simp[stackSemTheory.evaluate_def] >>
    simp[evaluate_wStackLoad_clock]>>
    `EVEN (2 * ad)` by simp[EVEN_DOUBLE] >>
    drule_all $ GEN_ALL evaluate_wStackLoad_wReg1>>
    rpt strip_tac >>
    gvs[] >>
    simp[wRegWrite1_def] >>
    IF_CASES_TAC >>
    simp[stackSemTheory.evaluate_def,
      stackSemTheory.dec_clock_def,AllCaseEqs()] >>
    gvs[stackSemTheory.word_exp_def,
      stackSemTheory.get_var_def,AllCaseEqs()]
    >- (
      drule $ GEN_ALL share_load_lemma2 >>
      simp[] >>
      disch_then drule >>
      simp[] >>
      rpt strip_tac >>
      gvs[]
      >- (
        irule_at (Pos last) EQ_REFL >>
        simp[] >>
        qexists_tac `1` >>
        simp[] ) >>
      first_x_assum $ irule_at (Pos last) >>
      qexists_tac `1` >>
      simp[] ) >>
    drule $ GEN_ALL share_load_lemma1 >>
    simp[] >>
    disch_then drule >>
    simp[] >>
    rpt strip_tac >>
    qexists_tac `1` >>
    simp[] >>
    first_assum $ irule_at (Pos last) >>
    gvs[state_rel_def,state_component_equality] )
QED

Theorem evaluate_ShareInst_Store:
  evaluate (ShareInst op (2 * v)
    (Op Add [Var (2 * ad);Const offset]),s) = (res,s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k /\
  res <> SOME Error /\
  (op = Store \/ op = Store8 \/ op = Store32) ==>
  ?ck t1.
    evaluate
      (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
        t with clock := ck + t.clock) =
        (OPTION_MAP compile_result res,t1) /\
    ((?fv. res = SOME (FinalFFI fv) /\
        s1.ffi = t1.ffi /\ s1.clock = t1.clock) \/
    (res = NONE /\ state_rel ac k f f' s1 t1 lens 0))
Proof
  rpt strip_tac >>
  (gvs[evaluate_def,wShareInst_def,AllCaseEqs()] >>
  pairarg_tac >>
  gvs[word_exp_def,AllCaseEqs(),the_words_def,GSYM get_var_def] >>
  pairarg_tac >>
  simp[evaluate_wStackLoad_seq,wStackLoad_append]>>
  simp[stackSemTheory.evaluate_def] >>
  simp[evaluate_wStackLoad_clock]>>
  `EVEN (2 * ad)` by simp[EVEN_DOUBLE] >>
  drule_all $ GEN_ALL evaluate_wStackLoad_wReg1>>
  rpt strip_tac >>
  gvs[wReg2_def,AllCaseEqs()] >>
  simp[wStackLoad_def]
  >- (
    qexists_tac `1` >>
    simp[Once stackSemTheory.evaluate_def,
      stackSemTheory.dec_clock_def] >>
    gvs[stackSemTheory.word_exp_def,
      stackSemTheory.get_var_def] >>
    drule_then drule $ GEN_ALL share_store_lemma2 >>
    simp[]
  ) >>
  qexists_tac `1` >>
  simp[stackSemTheory.evaluate_def,stackSemTheory.set_var_def,
    stackSemTheory.dec_clock_def] >>
  `t'.use_stack` by gvs[state_rel_def] >>
  `t.stack_space + (f + k - ( v + 1)) < LENGTH t.stack` by (
    fs [state_rel_def,get_var_def] >>
    res_tac >> rfs []
  ) >>
  drule_then drule $ GEN_ALL share_store_lemma1 >>
  rpt strip_tac >>
  gvs[stackSemTheory.word_exp_def,
    stackSemTheory.get_var_def,
    FLOOKUP_UPDATE])
QED

Theorem evaluate_ShareInst_correct_lemma:
  evaluate (ShareInst op (2 * v)
    (Op Add [Var (2 * ad);Const offset]),s) = (res,s1) /\
  res <> SOME Error /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k ==>
  ?ck t1.
    evaluate
      (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
        t with clock := ck + t.clock) =
      (OPTION_MAP compile_result res,t1) /\
    ((res = NONE /\ state_rel ac k f f' s1 t1 lens 0) \/
      (?fv. res = SOME (FinalFFI fv) /\
        s1.ffi = t1.ffi /\ s1.clock = t1.clock))
Proof
  rpt strip_tac >>
  drule evaluate_ShareInst_Load >>
  simp[] >>
  strip_tac >>
  drule evaluate_ShareInst_Store >>
  simp[] >>
  strip_tac >>
  Cases_on `op` >>
  metis_tac[]
QED

Theorem comp_ShareInst_correct:
  ^(get_goal "wordLang$ShareInst")
Proof
  rpt strip_tac >>
  gvs[EVAL ``post_alloc_conventions k (ShareInst op v exp)``,comp_def] >>
  drule flat_exp_conventions_ShareInst_exp_simp >>
  rpt strip_tac >>
  gvs[wordLangTheory.exp_to_addr_def,evaluate_ShareInst_Var_eq_Op_Add] >>
  gvs[wordLangTheory.every_var_exp_def,
      reg_allocTheory.is_phy_var_def,
      wordLangTheory.max_var_def,
      wordLangTheory.max_var_exp_def,
      GSYM FOLDR_MAX_0_list_max] >>
  gvs[GSYM EVEN_MOD2,EVEN_EXISTS,GSYM LEFT_ADD_DISTRIB] >>
  drule_all evaluate_ShareInst_correct_lemma >>
  rpt strip_tac >>
  gvs[] >>
  first_x_assum $ irule_at (Pos hd) >>
  gvs[]
QED

Theorem compile_prog_stack_size:
  compile_prog ac word_prog x k bs = (stack_prog,fs,bs2) ==>
  x - k <= fs
Proof
  rw[compile_prog_def,ELIM_UNCURRY,MAX_DEF]
QED

(* TODO: clean up *)
val cruft_tac =
    rpt(PRED_ASSUM is_forall kall_tac) >>
    rpt(qpat_x_assum `_.compile_oracle = _` kall_tac) >>
    rpt(qpat_x_assum `_.compile = _` kall_tac) >>
    rpt(qpat_x_assum `_.clock = _` kall_tac) >>
    rpt(qpat_x_assum `domain _ = _` kall_tac) >>
    rpt(qpat_x_assum `_.store = _` kall_tac) >>
    rpt(qpat_x_assum `_.memory = _` kall_tac) >>
    rpt(qpat_x_assum `_.code_buffer = _` kall_tac) >>
    rpt(qpat_x_assum `_.data_buffer = _` kall_tac) >>
    rpt(qpat_x_assum `_.gc_fun = _` kall_tac) >>
    rpt(qpat_x_assum `_.fp_regs = _` kall_tac) >>
    rpt(qpat_x_assum `_.ffi = _` kall_tac) >>
    rpt(qpat_x_assum `_.be = _` kall_tac) >>
    rpt(qpat_x_assum `_ ∈ _` kall_tac) >>
    rpt(qpat_x_assum `_.mdomain = _` kall_tac) >>
    rpt(qpat_x_assum `(λbm0 cfg progs. _) = (λbm0 cfg progs. _)` kall_tac) >>
    rpt(qpat_x_assum `_.use_stack` kall_tac) >>
    rpt(qpat_x_assum `_.use_store` kall_tac) >>
    rpt(qpat_x_assum `_.use_alloc` kall_tac) >>
    rpt(qpat_x_assum `gc_fun_ok _` kall_tac) >>
    rpt(qpat_x_assum `_.ffi_save_regs = _` kall_tac) >>
    rpt(qpat_x_assum `_.code = _.code` kall_tac) >>
    rpt(qpat_x_assum `T` kall_tac) >>
    rpt(qpat_x_assum `_.termdep = _` kall_tac) >>
    rpt(qhdtm_x_assum `stack_rel` kall_tac) >>
    rpt(qhdtm_x_assum `list$isPREFIX` kall_tac) >>
    rpt(qhdtm_x_assum `wf` kall_tac) >>
    rpt(qhdtm_x_assum `post_alloc_conventions` kall_tac) >>
    rpt(qhdtm_x_assum `flat_exp_conventions` kall_tac) >>
    rpt(qhdtm_x_assum `good_dimindex` kall_tac) >>
    rpt(qpat_x_assum `_.clock <> _` kall_tac) >>
    rpt(qpat_x_assum `_.store \\ _ = _` kall_tac) >>
    rpt(qpat_x_assum `_ < dimword _` kall_tac)

Triviality SUB_SUB_SUB_MAX:
  a - b - (c - b) =
  a - MAX b c
Proof
  rw[MAX_DEF]
QED

Triviality MAX_LE:
  a <= b ==> MAX a b = b
Proof
  rw[MAX_DEF]
QED

Triviality copy_ret_aux_thm:
  (copy_ret_aux k f 0 = Skip) /\
  (copy_ret_aux k f (SUC n) =
  list_Seq [StackLoad k n; StackStore k (n + f); copy_ret_aux k f n])
Proof
  fs[Once copy_ret_aux_def] >>
  fs[Once copy_ret_aux_def]
QED

Theorem evaluate_copy_ret_Seq:
  evaluate (copy_ret b kf vs k0,t) =
  evaluate (Seq (copy_ret b kf vs Skip) k0,t)
Proof
 fs[oneline copy_ret_def, SeqStackFree_def,stackSemTheory.evaluate_def] >>
 rpt (TOP_CASE_TAC >> fs[]) >>
 fs[stackSemTheory.evaluate_def] >>
 pairarg_tac >> fs[] >>
 rpt (TOP_CASE_TAC >> fs[])
QED

Theorem evaluate_copy_ret_Seq':
  evaluate (copy_ret is_handle (k,f,f') vs k0,t) =
  let n = num_stack_ret k vs in
  evaluate (Seq (copy_ret_aux k (if is_handle then f + 3 else f) n) (SeqStackFree n k0),t)
Proof
 fs[copy_ret_def,stackSemTheory.evaluate_def] >>
 Cases_on `num_stack_ret k vs = 0` >> fs[]
 >- fs[copy_ret_aux_thm,stackSemTheory.evaluate_def,SeqStackFree_def]
 >- fs[stackSemTheory.evaluate_def]
QED

Theorem get_labels_copy_ret:
  get_labels (copy_ret is_handle kf vs q) = get_labels q
Proof
  fs[oneline copy_ret_def,SeqStackFree_def] \\
  rpt (TOP_CASE_TAC \\ fs[get_labels_def]) \\
  qmatch_goalsub_abbrev_tac `copy_ret_aux _ _ n` \\
  rpt $ pop_assum kall_tac \\
  Induct_on `n` >> fs[copy_ret_aux_thm,get_labels_def,stackLangTheory.list_Seq_def]
QED

Theorem evaluate_copy_ret_aux:
  !k f n t.
  t.use_stack /\ f <> 0 /\ f <= LENGTH t.stack - (t.stack_space + n)  ==>
  ?t'.
  evaluate (copy_ret_aux k f n,t) = (NONE,t') /\
  ?t'_stack t'_regs.
   t' = t with <| stack := t'_stack; regs := t'_regs|> /\
   LENGTH t'_stack = LENGTH t.stack /\
   t'.stack_space = t.stack_space /\
   DROP (f + n + t'.stack_space) t'_stack =
   DROP (f + n + t.stack_space) t.stack /\
   (!i. i <> k ==> get_var i t' = get_var i t) /\
   (let
     stack' = DROP (t'.stack_space) t'_stack; 
     stack  = DROP (t.stack_space) t.stack; 
   in
     ∀x. x < n ⇒ EL (x + f) stack' = EL x stack)
Proof
  Induct_on `n` >> rpt strip_tac >> simp[copy_ret_aux_thm]
  >- (
  fs[stackSemTheory.evaluate_def] >>
  fs[stackSemTheory.state_component_equality])
  >- (
  fs[stackLangTheory.list_Seq_def,stackSemTheory.evaluate_def] >>
  qmatch_goalsub_abbrev_tac `(copy_ret_aux _ _ _, t')` >>
  first_x_assum (qspecl_then [`k`,`f`,`t'`] mp_tac) >>
  impl_tac >- (
    simp[Abbr`t'`] >> metis_tac[]) >>
  strip_tac >> simp[] >>
  simp[ADD_CLAUSES,DROP_SUC] >>
  rveq >> fs[Abbr`t'`] >>
  fs[stackSemTheory.state_component_equality] >>
  CONJ_TAC >- simp[stackSemTheory.set_var_def] >>
  CONJ_TAC >- simp[DROP_LUPDATE] >>
  CONJ_TAC >- fs[stackSemTheory.get_var_def,
    stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  rw[] >>
  Cases_on `n = x` >> gvs[]
  >- (
    PURE_REWRITE_TAC[Once ADD_COMM] >>
    DEP_REWRITE_TAC[GSYM EL_DROP] >>
    `n = 0 + n` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    DEP_REWRITE_TAC[GSYM EL_DROP] >>
    simp[] >> fs[DROP_DROP_T] >>
    simp[HD_DROP,EL_LUPDATE])
  >- (
    `x < n` by fs[] >>
     res_tac >>
     fs[EL_DROP,EL_LUPDATE]))
QED

Theorem evaluate_copy_ret_aux_clock:
 !t.
   evaluate (copy_ret_aux k f n,t with clock := clk) =
   (I ## (\t. t with clock := clk)) (evaluate (copy_ret_aux k f n,t))
Proof
 Induct_on `n` >> rw[] >> fs[copy_ret_aux_thm,stackSemTheory.evaluate_def,
 stackLangTheory.list_Seq_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  full_simp_tac(bool_ss)[GSYM stackSemTheory.state_fupdcanon]
QED

(*
Theorem evaluate_copy_ret_clock:
  !t.
  evaluate (copy_ret b kf vs Skip, t with clock := clk) =
  (I ## (λt. t with clock := clk)) (evaluate (copy_ret b kf vs Skip, t))
Proof
  simp[oneline copy_ret_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  fs[SeqStackFree_def]
  >- fs[stackSemTheory.evaluate_def]
  >> fs[stackSemTheory.evaluate_def]
  >> fs[evaluate_copy_ret_aux_clock]
  >> rw[] >> pairarg_tac >> fs[]
  >> rpt (TOP_CASE_TAC >> gvs[])
QED
*)
fun uncurry_case_rand x = x
                         |> TypeBase.case_rand_of
                         |> ISPEC ``(UNCURRY (A:'uniquea -> 'uniqueb -> 'uniquec))``
                         |> GEN ``(A:'uniquea -> 'uniqueb -> 'uniquec)``;

val _ = get_time timer;

fun note_tac s g = (print ("comp_Call_correct: " ^ s ^ "\n"); ALL_TAC g);

Theorem comp_Call_correct:
  ^(get_goal "wordLang$Call")
Proof
  REPEAT GEN_TAC \\
  DISCH_THEN $ ASSUME_NAMED_TAC "IND" \\
  REPEAT STRIP_TAC \\
  fs[comp_def,UNCURRY_EQ]\\ rveq \\
  Cases_on `ret` \\ fs[] \\ rveq \\
  fs[get_labels_def]
  THEN1 (
    note_tac "comp_correct tail call case"
    \\ fs[AllCaseEqs()] \\ rveq
    \\ qpat_x_assum `_ = (res,s1)` mp_tac
    \\ simp[wordSemTheory.evaluate_def,Ntimes (AllCaseEqs()) 6,PULL_EXISTS]
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ drule_all call_dest_lemma
    \\ disch_then (Q.SPEC_THEN `NONE` mp_tac)
    \\ simp[] \\ strip_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ fsrw_tac[] []
    \\ simp[Once stackSemTheory.evaluate_def]
    \\ disch_then kall_tac
    \\ `t4.clock = s.clock /\ t4.use_stack` by fsrw_tac[] [state_rel_def]
    \\ `!n p ck. evaluate (SeqStackFree n p,t4 with clock := ck) =
                 evaluate (Seq (StackFree n) p,t4 with clock := ck)` by
     (rw [] \\ match_mp_tac evaluate_SeqStackFree
      \\ fsrw_tac[] [state_rel_def] \\ decide_tac) \\ fsrw_tac[][]
    \\ pop_assum kall_tac
    \\ qmatch_goalsub_abbrev_tac `(Seq _ CALL)`
    \\ fsrw_tac[] [stackSemTheory.evaluate_def]
    \\ `~ (LENGTH t.stack <
         t.stack_space + stack_free dest' (LENGTH args) (k,f,f'))`
        by (fsrw_tac[] [stack_free_def]
         \\ Cases_on `dest'` \\ fsrw_tac[] [stack_arg_count_def]
         \\ fsrw_tac[] [state_rel_def,LET_DEF] \\ decide_tac)
    \\ fsrw_tac[] [LET_DEF,Abbr`CALL`]
    \\ simp[Once stackSemTheory.evaluate_def]
    \\ simp[Once (AllCaseEqs())] \\ strip_tac \\ rveq
    THEN1 (qexists_tac `0` \\ simp[flush_state_def] \\ fs[state_rel_def])
    \\ fs[TypeBase.case_eq_of ``:'a option``,TypeBase.case_eq_of ``:'a # 'b``]
    \\ rveq \\ fs[]
    \\ fsrw_tac[][]
    \\ imp_res_tac compile_prog_stack_size
    \\ qhdtm_x_assum `compile_prog` mp_tac
    \\ fsrw_tac[][compile_prog_def]
    \\ LET_ELIM_TAC \\ fsrw_tac[][] \\ rveq
    \\ simp[stackSemTheory.evaluate_def]
    \\ fsrw_tac[][stack_free_def]
    \\ `Abbrev (stack_arg_count' = stack_arg_count dest' (LENGTH args) k) `
          by (
          simp[Abbr`stack_arg_count'`,markerTheory.Abbrev_def] \\
          `LENGTH xs = LENGTH args` by
          (imp_res_tac get_vars_length_lemma) \\
          pop_assum mp_tac \\
          qhdtm_x_assum `wordSem$find_code` (mp_tac) \\
          qhdtm_x_assum `call_dest` (mp_tac) \\
          rpt (pop_assum kall_tac) \\
          rpt strip_tac \\
          Cases_on `dest` \\
          fs[find_code_def,call_dest_def,CaseEq"option",CaseEq"prod",CaseEq"word_loc",CaseEq"num",
            add_ret_loc_def] \\
          rveq \\ fs[] \\
          rfs[LENGTH_FRONT] \\
          fs[stack_arg_count_def] \\
          `args <> []` by(CCONTR_TAC \\ fs[]) \\
          fs[UNCURRY_EQ] \\
          rveq \\ fs[])
    \\ fs[]
    \\ `LENGTH args - 1 < f' + k`
       by
         (
         fsrw_tac[][convs_def] \\
         qpat_x_assum `max_var _ < _` mp_tac \\
         qpat_x_assum `args = _` SUBST_ALL_TAC \\
         simp[wordLangTheory.max_var_def] \\
         simp[list_max_GENLIST_evens] \\
         simp[GSYM LEFT_ADD_DISTRIB])
    \\ `LENGTH xs >= (LENGTH args1)`
           by (qpat_x_assum`A=SOME(q,q',r')` mp_tac>>
              Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
              simp[AllCaseEqs()] >> strip_tac >>
              rveq >> fsrw_tac[][] >>
              simp[LENGTH_FRONT])
    \\ `LENGTH xs = LENGTH args` by
       (imp_res_tac get_vars_length_lemma)
    (*preconditions for negation rules*)
    \\ `stack_arg_count' <= f /\ stack_arg_count' <= f''`
        by  (fsrw_tac[][state_rel_def] \\
         `stack_arg_count' <= stack_var_count`
              by (fs[Abbr `stack_var_count`]) \\
         `stack_var_count <= f''`
              by(fs[Abbr`f''`]) \\
         `stack_arg_count' = LENGTH args1 -k`
            by (UNABBREV_ALL_TAC  \\ fsrw_tac[][]) \\
          Cases_on `f' = 0` >> fs[])
    \\ fs[SF CONJ_ss]
    \\ PURE_TOP_CASE_TAC
    THEN1 ( (* Hit stack limit case *)
      fsrw_tac[][PULL_EXISTS] \\
      `compile_result res' ≠ Halt (Word 2w)` by
         fs[state_rel_def,compile_result_NOT_2] \\
      fsrw_tac[][] \\
      `t4.ffi = s.ffi` by fs[state_rel_def] \\
      fsrw_tac[][] \\
      imp_res_tac wordPropsTheory.evaluate_io_events_mono \\
      fs[] \\
      imp_res_tac evaluate_stack_limit \\
      imp_res_tac evaluate_stack_max \\
      fsrw_tac[][call_env_def] \\
      PURE_FULL_CASE_TAC >- fs[the_eqn] \\
      fsrw_tac[][] \\ rveq \\
      fsrw_tac[][state_rel_def] \\
      qhdtm_x_assum `stack_size_rel` mp_tac \\
      fsrw_tac[][stack_size_rel_def] \\
      Cases_on `s'.stack_max` \\ fsrw_tac[][the_eqn] \\
      rveq \\ fs[GREATER_EQ])
    \\ fsrw_tac[][stackSemTheory.dec_clock_def]
    \\ (fn g =>
         qabbrev_tac `t5 = ^((qexists_tac`0`
         \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t5)`) g
         |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g)
    \\ `state_rel ac k f'' stack_var_count (call_env args1 ss (dec_clock s)) t5 lens 0` by
        (
        fsrw_tac[][state_rel_def,dec_clock_def,Abbr`t5`] \\
        fsrw_tac[][call_env_def] \\
        CONJ_TAC >-
        (rpt (PRED_ASSUM (not o is_forall) kall_tac) \\
        METIS_TAC[]) \\
        CONJ_TAC >- (fs[Abbr`f''`]) \\
        CONJ_TAC >- (fs[Abbr`f''`]) \\
        CONJ_TAC >- (fs[wf_fromList2]) \\
        CONJ_TAC >- (
          qhdtm_x_assum `stack_size_rel` mp_tac \\
          simp[stack_size_rel_def] \\
          rpt (gen_tac ORELSE disch_tac) \\
          rpt (CHANGED_TAC (fsrw_tac[][] \\ rveq)) \\
          TIDY_ABBREVS \\ fs[MAX_DEF]) \\
        fsrw_tac[][LET_THM] \\
        CONJ_TAC >- (TIDY_ABBREVS \\ fs[DROP_DROP_EQ]) \\
        rpt (GEN_TAC ORELSE DISCH_TAC) \\ fsrw_tac[][] \\
        imp_res_tac (GSYM domain_lookup)>>
        imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
        `lookup n' s.locals = SOME v`
           by (
            fsrw_tac[][convs_def] >>
            qpat_x_assum`args=_` SUBST_ALL_TAC>>
            imp_res_tac get_vars_fromList2_eq>>
            `isPREFIX args1 xs` by (
              qpat_x_assum`_=SOME(q,q',r')` mp_tac>>
              Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
              simp[AllCaseEqs()] >> strip_tac >>
              fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
              Cases_on`xs`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
            imp_res_tac lookup_fromList2_prefix >>
            res_tac) >>
        IF_CASES_TAC>-
          (res_tac \\
          rpt (PRED_ASSUM
          (fn x => is_forall x orelse is_eq x orelse markerSyntax.is_abbrev x) kall_tac) \\ rfs[]) \\
        fsrw_tac[][LLOOKUP_THM]>>
        `stack_var_count <> 0`
          by
           (fsrw_tac[] [markerTheory.Abbrev_def] \\ rpt var_eq_tac \\ fsrw_tac[] []
            \\ fsrw_tac[] [lookup_fromList2,lookup_fromList]
            \\ decide_tac) >>
        simp[Abbr`f''`]>>
        fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        CONJ_ASM2_TAC
          >- (
            TIDY_ABBREVS \\
            first_x_assum(qspecl_then[`n'`,`v`] mp_tac)>>
            simp[EL_TAKE,EL_DROP]>>
            strip_tac>>
            qpat_x_assum`_=v` mp_tac>>
            simp[EL_TAKE,EL_DROP]>>
            disch_then sym_sub_tac>>
            AP_THM_TAC>>AP_TERM_TAC>>
            `(n' DIV 2 +1) ≤ f+k` by
              (Cases_on`f'`>>fsrw_tac[][]>>
              DECIDE_TAC)>>
            simp[])>>
        unabbrev_all_tac>>
        fsrw_tac[][] >>
        simp[MAX_DEF]) \\
    LABEL_X_ASSUM "IND" mp_tac
    \\ simp[]
    \\ DISCH_THEN drule
    \\ disch_then (drule_at Any) \\ fsrw_tac[] []
    \\ impl_tac THEN1 (
      CONJ_ASM1_TAC>-
        (qpat_x_assum`_=SOME(q,q',r')`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][add_ret_loc_def,wordSemTheory.find_code_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
        fsrw_tac[][state_rel_def] >>
        metis_tac[])>>
      CONJ_ASM1_TAC>-
        (qpat_x_assum`_=SOME(q,q',r')`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][add_ret_loc_def,wordSemTheory.find_code_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
        fsrw_tac[][state_rel_def] >>
        metis_tac[])>>
      imp_res_tac evaluate_mono>>fs[]>>
      CONJ_TAC>- (drule IS_PREFIX_LENGTH>>fs[Abbr`t5`]) >>
      CONJ_TAC>- (fs[Abbr`t5`]>>metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]) >>
      CONJ_TAC >-
       (qunabbrev_tac `t5` \\ simp_tac (srw_ss()) []
        \\ drule find_code_IMP_get_labels
        \\ fs [get_labels_def])
      >>
        (`EVEN (max_var prog)` by
            (ho_match_mp_tac max_var_intro>>
            fsrw_tac[][convs_def]>>
            match_mp_tac every_var_mono>>
            HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def,EVEN_MOD2])>>
        simp[Abbr`stack_var_count`] >>
        fsrw_tac[][EVEN_EXISTS,GSYM LEFT_ADD_DISTRIB]>>
        simp[GSYM LEFT_ADD_DISTRIB ] >>
        fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
        DECIDE_TAC))
    \\ strip_tac \\ fsrw_tac[] []
    \\ qunabbrev_tac `t5` \\ fsrw_tac[] []
    \\ `ck + (s.clock - 1) = ck + s.clock - 1` by decide_tac
    \\ qexists_tac `ck` \\ fsrw_tac[] []
    \\ Cases_on `res1` \\ fsrw_tac[] [PULL_EXISTS])
  \\ note_tac "comp_correct returning call case(s)"
  \\ fs[UNCURRY_EQ,TypeBase.case_eq_of ``:'a # 'b``] \\ rveq
  \\ qpat_x_assum `_ = (res,s1)` mp_tac
  \\ simp[wordSemTheory.evaluate_def,Ntimes (AllCaseEqs()) 7,PULL_EXISTS]
  \\ rpt strip_tac
  \\ rveq \\ fsrw_tac[][]
  \\ drule_all call_dest_lemma
  \\ disch_then (qspec_then `SOME (vs,live,ret_code,l1,l2)` mp_tac)
  \\ strip_tac \\ rfs[] \\ fsrw_tac[][]
  \\ imp_res_tac evaluate_call_dest_clock
  \\ pop_assum(qspec_then`t` assume_tac)
  (*TODO fix lemma*)
  \\ Cases_on `bs''`
  \\ drule ((GEN_ALL evaluate_wLive)|> REWRITE_RULE[GSYM AND_IMP_INTRO])
  \\ rpt $ disch_then (drule_at Any)
  \\ simp[]
  \\ impl_keep_tac>- (
      rpt(qpat_x_assum`!x. _` kall_tac) >>
      LABEL_X_ASSUM "IND" kall_tac >>
      fsrw_tac[][convs_def,lambdify reg_allocTheory.is_phy_var_def,
      GSYM EVEN_MOD2,SF ETA_ss]>>
      fsrw_tac[][GSYM toAList_domain,EVERY_MEM]>>
      fsrw_tac[][X_LE_DIV,LET_THM]>>
      qhdtm_x_assum `cut_envs` mp_tac >>
      Cases_on `live` >> simp[cut_envs_def,AllCaseEqs()] >>
      rpt (disch_then strip_assume_tac) >>
      rveq >> fsrw_tac[][] >>
      qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
      pure_rewrite_tac[wordLangTheory.max_var_def] >>
      `!x y z. max3 x y z = MAX x (MAX y z)`
        by fs[MAX_DEF,max3_def] >>
      pop_assum (pure_rewrite_tac o single) >>
      fsrw_tac[][LET_DEF] >> strip_tac >>
      namedCases_on `handler`["","h"] >>
      TRY (PairCases_on `h`) >>
      rveq >> fs[] >>
      rveq >> fs[] >>
      (* Two subgoals *)
      (CONJ_TAC
      >- (qpat_abbrev_tac`ls = MAP FST A`>>
        Q.ISPEC_THEN `ls` assume_tac list_max_max>>
        fsrw_tac[][EVERY_MEM]>>
        rw[] >>
        res_tac >>
        DECIDE_TAC) >>
      CONJ_TAC
      >- (qpat_abbrev_tac`ls = MAP FST A`>>
        Q.ISPEC_THEN `ls` assume_tac list_max_max>>
        fsrw_tac[][EVERY_MEM]>>
        rw[] >>
        res_tac >>
        DECIDE_TAC)>>
      CONJ_TAC
      >- (
      `∃nn. MEM nn (MAP FST (toAList q'))` by
        (CCONTR_TAC>>
        fsrw_tac[][toAList_domain]>>
        `domain q' = {}` by
          fsrw_tac[][EXTENSION])>>
      first_x_assum drule>>
      qabbrev_tac`ls = MAP FST (toAList q')`>>
      Q.ISPEC_THEN `ls` assume_tac list_max_max>>
      fsrw_tac[][EVERY_MEM]>>
      `nn < 2*f'+2*k` by
        (res_tac>>DECIDE_TAC)>>
      strip_tac>>
      `f' ≠ 0` by DECIDE_TAC>>
      fsrw_tac[][state_rel_def]) >>
      CONJ_TAC
      >- (
      drule evaluate_mono>> strip_tac>>
      drule IS_PREFIX_LENGTH>>
      simp[])>>
      fs[UNCURRY_EQ] >>
      imp_res_tac comp_IMP_isPREFIX>> fsrw_tac[][]>>
      drule evaluate_mono>>
      metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])) >>
  strip_tac>>
  imp_res_tac evaluate_wLive_clock>>
  pop_assum (qspec_then`t4` assume_tac)>>
  Cases_on`handler`>> fs[] >> rveq >> fs[]
  THEN1 (
    note_tac "No handler case">>
    simp[Ntimes stackSemTheory.evaluate_def 2]>>
    imp_res_tac compile_prog_stack_size >>
    qhdtm_x_assum `compile_prog` mp_tac >>
    fsrw_tac[][compile_prog_def] >>
    LET_ELIM_TAC >> fs[] >> rveq >>
    (*TODO shouldn't be unfolding here*)
    simp[StackArgs_def,stackSemTheory.evaluate_def,
    Once evaluate_stack_move_seq]>>
    simp[uncurry_case_rand ``:bool``] >>
    (*Get through the eval of stack_move*)
    `t5.use_stack` by fsrw_tac[][state_rel_def] >>
    pop_assum (simp o single) >>
    `Abbrev (stack_arg_count' = stack_arg_count dest' (LENGTH args + 1) k)`
       by(
       simp[Abbr`stack_arg_count'`,markerTheory.Abbrev_def,stack_arg_count_def] >>
       `LENGTH args = LENGTH xs`
          by (imp_res_tac get_vars_length_lemma >> fsrw_tac[][]) >>
       pop_assum mp_tac >>
       qhdtm_x_assum `call_dest` mp_tac >>
       qpat_x_assum `¬bad_dest_args _ _` mp_tac >>
       qhdtm_x_assum `wordSem$find_code` mp_tac >>
       rpt (pop_assum kall_tac) >>
       simp[oneline call_dest_def,AllCaseEqs()] >>
       rpt strip_tac >> fs[bad_dest_args_def] >>
       gvs[UNCURRY_EQ] >>
       qhdtm_x_assum `wordSem$find_code` mp_tac >>
       simp[wordSemTheory.find_code_def,add_ret_loc_def,AllCaseEqs()] >>
       strip_tac >> fs[] >> rveq >>
       fs[LENGTH_FRONT,ADD1]) >>
    fs[] >>
    Cases_on `t.stack_space < stack_arg_count'` >> fs[]
    >- (
       `!x. compile_result x ≠ Halt (Word 2w)`
          by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
        fsrw_tac[][] >>
        `t5.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
        `stack_arg_count' = LENGTH args1 − k` by
        fsrw_tac[][Abbr`stack_arg_count'`] >>
        `the (s.stack_limit + 1)
          (call_env args1 ss (push_env envs NONE s)).stack_max >
        s.stack_limit`
          by (simp[call_env_def,the_eqn] >>
          PURE_TOP_CASE_TAC >- simp[] >>
          fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
          rveq >>
          fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
          rveq >> fsrw_tac[][the_eqn] >>
          rveq >> fsrw_tac[][] >>
          rfs[]) >>
        qpat_x_assum `_ = (res,s1)` mp_tac >>
        simp[Once $ AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        CONJ_TAC >-(
            pop_assum mp_tac >>
            simp[AllCaseEqs()] >>
            strip_tac >> rveq >> fs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const >>
            fsrw_tac[][] >>
            rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
            rpt (pop_assum kall_tac) >>
            METIS_TAC[IS_PREFIX_TRANS]) >>
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def])  >>
    qabbrev_tac`t6 = t5 with <|stack_space :=t5.stack_space - stack_arg_count'|>` >>
    `!ck. t5 with <|stack_space:=t5.stack_space - stack_arg_count'; clock:=ck+t.clock|> =
        t6 with clock:=ck+t.clock` by
       simp[stackSemTheory.state_component_equality,Abbr`t6`]>>
     rev_full_simp_tac std_ss [] >>
    Q.ISPECL_THEN [`stack_arg_count'`,`0n`,`t6`,`f`] mp_tac evaluate_stack_move>>
    impl_tac
       >- (simp[Abbr`t6`] >>
       fsrw_tac[][state_rel_def] >>
       qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
       pure_rewrite_tac[wordLangTheory.max_var_def] >>
       `!x y z. max3 x y z = MAX x (MAX y z)`
         by fs[MAX_DEF,max3_def] >>
       pop_assum (pure_rewrite_tac o single) >>
       fsrw_tac[][LET_DEF] >> strip_tac >>
       fsrw_tac[][convs_def]>>
       qpat_x_assum`args = A` SUBST_ALL_TAC>>
       fsrw_tac[][list_max_GENLIST_evens2]>>
       rveq >>
       Cases_on `f' = 0` >> fsrw_tac[][] >>
       Cases_on `dest'` >>
       fsrw_tac[][stack_arg_count_def] >>
       fsrw_tac[][Abbr`stack_arg_count'`] >>
       (*TODO this very slow*)
       gvs[]) >>
    strip_tac  >>
    rfs[evaluate_stack_move_clock] >>
    fs[Abbr`t6`] >>
    `find_code dest' (t'_regs \\0) t5.code = find_code dest' t4.regs t4.code` by (
      `subspt t4.code t5.code` by
        (unabbrev_all_tac>>
        fs[stackSemTheory.state_component_equality]>>
        imp_res_tac evaluate_mono>>fs[]>>
        metis_tac[evaluate_consts])>>
      Cases_on`dest'`>>fs[stackSemTheory.find_code_def]
      >- metis_tac[subspt_def,domain_lookup] >>
      qpat_x_assum`A=SOME stack_prog` mp_tac>>
      qpat_x_assum`A=(q0,INR y)` mp_tac>>
      Cases_on`dest`>>simp[call_dest_def]>>
      IF_CASES_TAC>>simp[]>>
      simp[wReg2_def]>>IF_CASES_TAC>>fs[]
      >- (
        `LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by (
          fs[convs_def]>>
          qpat_x_assum`args = A` SUBST_ALL_TAC>>
          `LENGTH args <> 0` by (strip_tac \\ fs[]) >>
          drule LAST_GENLIST_evens>>
          LET_ELIM_TAC>>simp[]>>
          Cases_on`reg`>>fs[]>>
          rename1`SUC xx DIV _ ≠ _`>>
          Cases_on`xx`>>fs[]>>
          simp[ADD_DIV_RWT,ADD1])>>
        strip_tac>>rveq>>
        simp[DOMSUB_FLOOKUP_THM]>>
        fs[stackSemTheory.get_var_def]>>
        qpat_x_assum`subspt _ _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        EVERY_CASE_TAC>>rw[]>>
        metis_tac[subspt_def,domain_lookup])
      >>
        strip_tac>>rveq>>
        simp[DOMSUB_FLOOKUP_THM]>>
        fs[stackSemTheory.get_var_def]>>
        qpat_x_assum`subspt _ _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        EVERY_CASE_TAC>>rw[]>>
        metis_tac[subspt_def,domain_lookup])>>
    pop_assum SUBST_ALL_TAC >>
    fsrw_tac[][] >>
    `t.clock = s.clock` by fs[state_rel_def] >>
    pop_assum SUBST_ALL_TAC >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    IF_CASES_TAC>- (
      rw[]>>qexists_tac`0`>>
      simp[] >>
      fsrw_tac[][state_rel_def]) >>
    fsrw_tac[][] >>
    rpt $ (qpat_x_assum `!_. evaluate (_,_ with clock := _) = _` kall_tac) >>
    strip_tac >>
    simp[stackSemTheory.evaluate_def]>>
    `stack_arg_count' <= f''`
        by  (fsrw_tac[][state_rel_def] \\
         `stack_arg_count' <= stack_var_count`
              by (fs[Abbr `stack_var_count`]) \\
         `stack_var_count <= f''`
              by(fs[Abbr`f''`]) \\
         `stack_arg_count' = LENGTH args1 -k`
            by (UNABBREV_ALL_TAC  \\ fsrw_tac[][]) \\
          Cases_on `f' = 0` >> fs[]) >>
    fs[SF CONJ_ss] >>
    `t5.use_stack` by fsrw_tac[][state_rel_def] >>
    pop_assum (simp o single) >>
    PURE_TOP_CASE_TAC
    THEN1 ( (* Hit stack limit case *)
       `!x. compile_result x ≠ Halt (Word 2w)`
          by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
        fsrw_tac[][] >>
        `t5.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
        `stack_arg_count' = LENGTH args1 − k` by
        fsrw_tac[][Abbr`stack_arg_count'`] >>
        `the (s.stack_limit + 1)
          (call_env args1 ss (push_env envs NONE s)).stack_max >
        s.stack_limit`
          by (simp[call_env_def,the_eqn] >>
          PURE_TOP_CASE_TAC >- simp[] >>
          fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
          rveq >>
          fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
          rveq >> fsrw_tac[][the_eqn] >>
          rveq >> fsrw_tac[][] >>
          rfs[]) >>
        qpat_x_assum `_ = (res,s1)` mp_tac >>
        simp[Once $ AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        CONJ_TAC >-(
            pop_assum mp_tac >>
            simp[AllCaseEqs()] >>
            strip_tac >> rveq >> fs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const >>
            fsrw_tac[][] >>
            rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
            rpt (pop_assum kall_tac) >>
            METIS_TAC[IS_PREFIX_TRANS]) >>
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def])  >>
    fsrw_tac[][] >>
    simp[]>>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    qpat_abbrev_tac`word_state = call_env args1 ss st`>>
    strip_tac >>
    (*This looks hacky but it works*)
    (fn g =>
         qabbrev_tac `stack_state = ^((qexists_tac`0`
         \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
         |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
    `state_rel ac k f'' stack_var_count word_state stack_state (f'::lens) 0`
        by(
       `stack_arg_count' = (LENGTH args1 -k)` by
          (simp[Abbr`stack_arg_count'`]) >>
       `stack_arg_count' <= stack_var_count` by fsrw_tac[][Abbr`stack_var_count`] >>
      fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
      PURE_ONCE_REWRITE_TAC [dec_clock_def, stackSemTheory.dec_clock_def,
        call_env_def, push_env_def, env_to_list_def] >>
      fsrw_tac[][] >>
      conj_tac >- (simp[push_env_def,env_to_list_def] >> simp[FUN_EQ_THM]) >>
      conj_tac >- metis_tac [] >>
      conj_tac >- (cruft_tac >> rveq >>
                   `f'' <= LENGTH t.stack` by intLib.COOPER_TAC >>
                   qsuff_tac `t.stack_space <= LENGTH t.stack` >-
                     (qpat_x_assum `¬(t.stack_space < LENGTH args1 - k)` mp_tac >>
                      qpat_x_assum `t4.stack_space = t.stack_space` mp_tac >>
                      `LENGTH t4.stack = LENGTH t.stack` by rw[] >>
                      rw[SUB_RIGHT_SUB,SUB_RIGHT_ADD]) >>
                   intLib.COOPER_TAC) >>
      conj_tac >- (fsrw_tac[][Abbr`f''`]) >>
      conj_tac >- simp[wf_fromList2] >>
      conj_tac >- (cruft_tac >>
                  qhdtm_x_assum `stack_size_rel` mp_tac >>
                  fsrw_tac[][stack_size_rel_def,LET_THM] >>
                  simp[env_to_list_def,stack_size_eq,push_env_def] >>
                  strip_tac >> gvs[the_eqn] >>
                  strip_tac >> gvs[the_eqn] >>
                  simp[MAX_DEF]) >>
      fsrw_tac[][LET_THM]>>
      conj_tac >-
        (
         qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
         qpat_x_assum `DROP _ _ = DROP _ _` mp_tac >>
         fsrw_tac[][push_env_def,env_to_list_def,dec_clock_def]>>
         fsrw_tac[][DROP_DROP_EQ,LET_THM,ELIM_UNCURRY]>>
         simp[]) >>
      ntac 3 strip_tac>>
      rpt(WEAKEN_TAC (can (find_term (same_const ``the``)))) >>
      rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
      imp_res_tac (GSYM domain_lookup)>>
      imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
      fsrw_tac[][wordConvsTheory.post_alloc_conventions_def,wordConvsTheory.call_arg_convention_def]>>
      `isPREFIX args1 (Loc l1 l2::xs)` by (
        qpat_x_assum`A=SOME(args1,_)` mp_tac>>
        Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        rveq >> fsrw_tac[][IS_PREFIX_BUTLAST]) >>
      drule_all_then assume_tac lookup_fromList2_prefix>>
      rename1`nn DIV 2 < k`>>
      Cases_on`nn=0`>- (
        fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        simp[FLOOKUP_UPDATE,stackSemTheory.set_var_def]) >>
      `lookup nn s.locals = SOME v` by (
        qpat_x_assum`args=A` SUBST_ALL_TAC>>
        imp_res_tac get_vars_fromList2_eq_cons)>>
      IF_CASES_TAC>- (
        `nn DIV 2 ≠ 0 ∧ nn DIV 2 ≠ k` by (
          fsrw_tac[][lookup_fromList2,lookup_fromList]>>
          full_simp_tac(srw_ss())[EVEN_EXISTS] >>
          rev_full_simp_tac(srw_ss())[] >>
          DECIDE_TAC) >>
        fsrw_tac[][FLOOKUP_UPDATE,stackSemTheory.set_var_def,
        stackSemTheory.get_var_def]>>
        metis_tac[])>>
       `f'' = stack_var_count + 1`
         by ( 
         `k ≤ LENGTH args1` by (
          fsrw_tac[][lookup_fromList2,lookup_fromList]
          \\ rpt(qpat_x_assum`nn DIV 2 < _`mp_tac)
          \\ qpat_x_assum`¬(nn DIV 2 < _)`mp_tac
          \\ rpt(pop_assum kall_tac)
          \\ decide_tac) >>
          fsrw_tac[] [lookup_fromList2,lookup_fromList,Abbr`f''`]>>
          Cases_on `stack_var_count = 0` >> fsrw_tac[][] >> simp[]) >>
       pop_assum SUBST_ALL_TAC >>
       DEP_REWRITE_TAC[LLOOKUP_TAKE] >> CONJ_TAC >- simp[] >>
       simp_tac(srw_ss()++ARITH_ss)[] >>
       simp[LLOOKUP_DROP] >>
       fsrw_tac[][LLOOKUP_THM,lookup_fromList2,lookup_fromList]>>
       simp_tac(srw_ss()++ARITH_ss)[] >>
       TIDY_ABBREVS >> fsrw_tac[][] >>
      `LENGTH args1 ≤ k+stack_var_count` by
        (qpat_x_assum`_ ≤ stack_var_count`mp_tac >>
        qpat_x_assum`stack_arg_count' = _`mp_tac >>
        rpt(pop_assum kall_tac) >> rw[] ) >>
      reverse conj_tac >- (
        qpat_x_assum`nn DIV 2 < _`mp_tac >>
        qpat_x_assum`nn DIV 2 < _`mp_tac >>
        pop_assum mp_tac >>
        rpt(pop_assum kall_tac) >> rw[] ) >>
      `stack_var_count +1 ≤ t.stack_space` by ( simp[] ) >>
      qpat_x_assum`_ ≤ LENGTH t.stack`mp_tac >>
      ntac 5 (pop_assum mp_tac) >>
      simp_tac(srw_ss()++ARITH_ss)[EL_DROP,EL_TAKE] >>
      rpt strip_tac >>
      first_x_assum(qspecl_then[`nn`,`v`] mp_tac)>>
      `k < nn DIV 2+1` by simp[]>>
      simp[EL_TAKE,GSYM AND_IMP_INTRO]>>
      disch_then (sym_sub_tac)>>
      simp[EL_DROP]>>
      strip_tac>>
      qpat_x_assum`!x. A ⇒ B = C` (mp_tac o GSYM) >>
      rpt(qpat_x_assum`!n.P` kall_tac)>>
      simp[EL_DROP]>>
      disch_then(qspec_then`LENGTH args1 - (nn DIV 2 +1)` mp_tac)>>
      simp[] >>
      rw[] >> fs[])>>
    Cases_on`evaluate(prog,word_state)`>>fsrw_tac[][]>>
    LABEL_X_ASSUM "IND" (fn x => mp_tac (CONJUNCT2 x) >>
    ASSUME_NAMED_TAC "IND" (CONJUNCT1 x)) >>
    simp[] >>
    disch_then (drule_at (Pos (el 2))) >>
    disch_then (drule_at Any)>>
    disch_then (drule_at Any)>>
    rename1`qres ≠ SOME Error ∧ _`>>
    Cases_on`qres = SOME Error`>>fsrw_tac[][]>>
    impl_tac>- (
      CONJ_ASM1_TAC>- (
        qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      CONJ_TAC>- (
        qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      simp[CONJ_ASSOC] >>
      reverse CONJ_TAC >-
        (`EVEN (max_var prog)` by
            (ho_match_mp_tac max_var_intro>>
            fsrw_tac[][convs_def]>>
            match_mp_tac every_var_mono>>
            HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def,EVEN_MOD2])>>
        unabbrev_all_tac>>fsrw_tac[][EVEN_EXISTS]>>
        rpt (pop_assum kall_tac)>>
        `m * 2 DIV 2 = m` by
          (Q.ISPECL_THEN[`2n`,`m`]assume_tac MULT_DIV>>fsrw_tac[][])>>
        fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
        DECIDE_TAC)>>
      unabbrev_all_tac>>fsrw_tac[][]>>
      imp_res_tac evaluate_mono>>
      rpt (qpat_x_assum`!x. _` kall_tac)>>
      fsrw_tac[][]>>rw[]
      >- (imp_res_tac IS_PREFIX_LENGTH>>
        simp[])
      >- (imp_res_tac comp_IMP_isPREFIX>>
        fsrw_tac[][]>>
        metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
      >>
        drule find_code_IMP_get_labels
        \\ simp[get_labels_def]
        \\ metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])>>
    strip_tac>>
    (*hit stack limit during function call*)
    Cases_on `OPTION_MAP compile_result qres ≠ res1` >> fsrw_tac[][]
    >- (
       rveq >> fsrw_tac[][] >>
       `!x. compile_result x ≠ Halt (Word 2w)`
          by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
        fsrw_tac[][] >>
        fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
        fsrw_tac[][stackSemTheory.set_var_def] >>
        qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
        qpat_x_assum `_ = (res1,t1)` mp_tac >>
        simp[AC ADD_COMM ADD_ASSOC] >>
        disch_tac >>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
        imp_res_tac stackPropsTheory.evaluate_io_events_mono >>
        fs[] >>
        CONJ_TAC >-
            (qpat_x_assum `_ = (res,s1)` mp_tac >>
            simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const>>
            fs[] >>
            metis_tac[IS_PREFIX_TRANS]) >>
        qpat_x_assum `_ = (res,s1)` mp_tac >>
        simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
        dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fs[] >>
        imp_res_tac wordPropsTheory.pop_env_const>>
        fs[]) >>
    fsrw_tac[][] >>
    Cases_on `res1 = SOME TimeOut` >> fs[]
    >- (
        `z = TimeOut` by (Cases_on `z` >> fsrw_tac[][]) >>
        fsrw_tac[][] >> rveq >>
        fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
        fsrw_tac[][stackSemTheory.set_var_def] >>
        qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
        qpat_x_assum `_ = (res1,t1)` mp_tac >>
        simp[AC ADD_COMM ADD_ASSOC] >>
        rveq >> fs[]) >>
    qrefine `ck + clk'` >>
    drule_all $ GEN_ALL evaluate_add_clock >>
    fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
    fsrw_tac[][stackSemTheory.set_var_def] >>
    simp[AC ADD_COMM ADD_ASSOC] >>
    disch_then kall_tac >> fs[] >>
    fs[] >> gvs[] >>
    Cases_on `qres` >> fs[] >>
    (Cases_on `x`) >> fs[] >> rveq >> fs[]
    >> fs[DECIDE ``!a b.  (a :num) = b + a <=> b = 0``]
    (*2 subgoals*)
    >- ( (* Normal return *)
      qpat_x_assum `_ = (res,s1)` mp_tac >>
      ntac 3 (PURE_TOP_CASE_TAC >> fsrw_tac[][]) >>
      rveq >> fsrw_tac[][] >> strip_tac >>
      Q.ISPECL_THEN [`prog`,`word_state`] mp_tac evaluate_stack_swap>>
      simp[] >> simp[Abbr`word_state`] >>
      simp[push_env_def,ELIM_UNCURRY,s_key_eq_def2] >>
      strip_tac >>
      qpat_x_assum `s_frame_key_eq (StackFrame _ _ _ _) _` mp_tac >>
      simp[oneline s_frame_key_eq_def2] >> TOP_CASE_TAC >> fs[] >>
      strip_tac >> gvs[] >>
      qpat_x_assum `state_rel _ _ 0 0 _ _ _ _` (strip_assume_tac o SRULE[state_rel_def]) >>
      rfs[] >>
      drule_then assume_tac stack_rel_cons_LEN_NONE >>
      fs[] >>
      simp[evaluate_copy_ret_Seq'] >>
      simp[num_stack_ret_def] >>
      qmatch_goalsub_abbrev_tac `copy_ret_aux k f num_stack_ret'` >>
      Q.ISPECL_THEN [`k`,`f`,`num_stack_ret'`,`t1`] mp_tac evaluate_copy_ret_aux >>
      impl_tac >- (
        fs[Abbr`num_stack_ret'`] >>
        Cases_on `f' = 0` >>
        fsrw_tac[][state_rel_def]) >>
      strip_tac >>
      simp[Once stackSemTheory.evaluate_def,evaluate_copy_ret_aux_clock] >>
      `!n p ck. evaluate (SeqStackFree n p,t' with clock := ck) =
                 evaluate (Seq (StackFree n) p,t' with clock := ck)` by
            (rw [] \\ match_mp_tac evaluate_SeqStackFree
      \\ fsrw_tac[] [state_rel_def] \\ decide_tac) \\
      rev_full_simp_tac(srw_ss())[] \\
      pop_assum kall_tac \\
      fsrw_tac[][stackSemTheory.evaluate_def] \\
      `LENGTH t'_stack' >= t1.stack_space + num_stack_ret'`
        by (fsrw_tac[][Abbr`num_stack_ret'`,state_rel_def] >>
            qpat_abbrev_tac `FREE = (LENGTH vs + 1 - k)` >>
            fs[]) \\
      fs[] \\ gvs[] \\
      (fn g =>
         qabbrev_tac `stack_state2 = ^((qexists_tac`0`
         \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
         |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
      `state_rel ac k f f' (set_vars vs l x) stack_state2 lens 0` by (
        fsrw_tac[][state_rel_def,set_vars_def,Abbr`stack_state2`]>>
        qhdtm_x_assum `pop_env` mp_tac >>
        simp[pop_env_def] >> strip_tac >> rveq >>
        simp[] >>
        CONJ_TAC>-
          metis_tac[evaluate_consts]>>
        CONJ_TAC >- (Cases_on `f' = 0` >> fs[]) >>
        CONJ_TAC>-
          simp[wf_alist_insert,wf_fromAList,wf_union]>>
        CONJ_TAC >-
           (rpt (qhdtm_x_assum `stack_size_rel` mp_tac) >>
            simp[stack_size_rel_def] >> rw[]
            >- (res_tac >> fs[])
            >- (res_tac >> fs[IS_SOME_EXISTS,stack_size_eq])
            >- (res_tac >> fsrw_tac[][IS_SOME_EXISTS,stack_size_eq] >>
               fs[the_eqn])) >>
        CONJ_ASM1_TAC >- (
           drule stack_rel_DROP_NONE >>
           `f' + 1 = f` by (Cases_on `f' = 0` >> fsrw_tac[][]) >>
           POP_ASSUM SUBST_ALL_TAC >>
           simp[DROP_DROP_T]) >>
       rpt gen_tac >>
       simp[lookup_alist_insert] >>
       reverse TOP_CASE_TAC
       >- (*Arg from return*)
       (strip_tac >> rveq >>
        `MEM (n'',v) (ZIP (vs,l))`
           by (DEP_REWRITE_TAC[ MEM_ALOOKUP ] >>
               simp[MAP_ZIP] >>
               fsrw_tac[][convs_def] >>
               qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
               simp[ALL_DISTINCT_GENLIST]) >>
         imp_res_tac MEM_ZIP2 >>
         fsrw_tac[][convs_def] >>
         qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
         DEP_REWRITE_TAC[EL_GENLIST] >>
         fsrw_tac[][] >>
         simp[EVEN_DOUBLE] >>
         res_tac >>
         IF_CASES_TAC >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[stackSemTheory.get_var_def]
         >- (
           `n''' + 1 <> k` by DECIDE_TAC >>
           res_tac >> full_simp_tac(srw_ss())[]) >>
         DEP_REWRITE_TAC[LLOOKUP_TAKE] >>
         CONJ_ASM1_TAC >-
         (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
         simp[LLOOKUP_DROP] >>
         fsrw_tac[][Abbr`num_stack_ret'`] >>
         `LENGTH vs + 1 >= k` by 
         (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
         simp[] >>
         `LENGTH vs + (t1.stack_space + 1) >= k` by 
         (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
         reverse CONJ_ASM2_TAC >-
           (qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
           full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
           `!a b c. max3 a b c = MAX a (MAX b c)`
             by simp[max3_def,MAX_DEF] >>
           fsrw_tac[][list_max_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
           simp_tac(srw_ss())[LET_THM] >>
           strip_tac >> DECIDE_TAC) >>
         `f + k >= n''' + 2`
             by (
             Cases_on `f' = 0` >> full_simp_tac(srw_ss())[] >> simp[]) >>
         `f = f' + 1` by (Cases_on `f' = 0` >> full_simp_tac(srw_ss())[]) >> 
         full_simp_tac(srw_ss())[] >>
         qpat_x_assum `!_. _ ==> _ = _` mp_tac >>
         disch_then (qspec_then `LENGTH vs - (n''' + 1)` mp_tac) >>
         qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
         disch_tac >>
         simp[EL_DROP] >>
         qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
         full_simp_tac(srw_ss())[LLOOKUP_THM] >>
         simp[EL_DROP]) >>
         `~ MEM (n'') (vs)`
           by (
              imp_res_tac ALOOKUP_NONE >>
              pop_assum mp_tac >>
              simp[MAP_ZIP]) >>
          fsrw_tac[][convs_def] >>
          qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
          fs[MEM_GENLIST] >>
          qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
          full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
           `!a b c. max3 a b c = MAX a (MAX b c)`
             by simp[max3_def,MAX_DEF] >>
           pop_assum (full_simp_tac(srw_ss()) o single)>>
           fsrw_tac[][list_max_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
         simp[] >>
         strip_tac >>
          `n'' > 0 /\ EVEN n'' ==> (n'' DIV 2 >= LENGTH vs + 1)`
               by (simp[EVEN_EXISTS] >> strip_tac  >>
               first_x_assum (qspec_then `n'' DIV 2 - 1` mp_tac) >>
               impl_tac >- simp[DECIDE ``m = m - 1 + 1 <=> (m :num) > 0``] >>
               fs[GSYM GREATER_DEF,GSYM GREATER_EQ,SF DISJ_ss]) >>
         simp[lookup_union,lookup_fromAList,ALOOKUP_toAList] >>
         (*GC cutset*)
         reverse TOP_CASE_TAC >- (
        rveq>>simp[stack_rel_aux_def]>>
        strip_tac>>
        rename1`EVEN nn`>>
        `nn ∈ domain (fromAList l0)` by metis_tac[domain_lookup,lookup_fromAList]>>
        rveq >> fs[] >>
        `MEM (nn,v) l0` by metis_tac[ALOOKUP_MEM]>>
        `MEM nn (MAP FST l0)`
           by (
           ntac 3 (pop_assum mp_tac) >>
           rpt (pop_assum $ K ALL_TAC) >>
           simp[MEM_MAP,EXISTS_PROD] >>
           metis_tac[]) >>
        `MEM nn (MAP FST (FST (env_to_list (SND envs) s.permute)))`
           by simp[] >>
        `MEM nn (MAP FST (toAList (SND envs)))`
           by (pop_assum mp_tac >>
           rpt (pop_assum $ K ALL_TAC) >>
           simp[MEM_MAP,env_to_list_def,PULL_EXISTS,mem_list_rearrange,QSORT_MEM] >> 
           METIS_TAC[]) >>
        qhdtm_x_assum  `cut_envs`
        (strip_assume_tac o SRULE[AllCaseEqs(),cut_envs_def,cut_names_def]) >> 
        rveq >> full_simp_tac(srw_ss())[domain_inter]  >>
        `nn ∈ domain (inter s.locals (SND live))`
           by (fs[toAList_domain]) >>
        `nn ∈ domain (SND live) ∧ nn ∈ domain s.locals` by (
            full_simp_tac(srw_ss())[domain_inter]) >>
        rveq >> fs[] >>
        res_tac>>simp[]>>
        fsrw_tac[][domain_inter] >>
        fsrw_tac[][domain_lookup]>>
        `v' = v` by fs[lookup_fromAList] >>
        last_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
        simp[]>>
        strip_tac>>
        fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack'''''` mp_tac>>
        qpat_abbrev_tac`ls = DROP A B`>>
        Cases_on`ls`>>simp[abs_stack_def]>>
        DISCH_THEN (strip_assume_tac o SRULE[AllCaseEqs()]) >>
        rveq >> fs[] >>
        ntac 2 $ qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        ntac 2 strip_tac>>
        `MEM (nn DIV 2,v) (MAP_FST adjust_names l0)` by
          (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
          metis_tac[])>>
        imp_res_tac filter_bitmap_MEM>>
        imp_res_tac MEM_index_list_EL>>
        gvs[] >>
        res_tac >> fs[] >>
        gvs[] >>
        fs[LLOOKUP_TAKE] >>
        qmatch_goalsub_abbrev_tac `EL A B` >>
        `SOME (EL A B) = LLOOKUP B A`
          by 
           (fs[LLOOKUP_THM,Abbr`A`,Abbr`B`] >>
           fs[LENGTH_TAKE_EQ_MIN] >>
           fs[MIN_DEF]) >>
        POP_ASSUM SUBST_ALL_TAC >>
        fs[Abbr`B`,Abbr`A`] >>
        simp[LLOOKUP_THM] >>
        `0 < LENGTH bits` by fs[LLOOKUP_THM,LENGTH_TAKE_EQ_MIN,MIN_DEF] >>
        simp[] >>
        IF_CASES_TAC >> simp[] >>
        simp[EL_TAKE] >>
        `t' = TL (DROP (num_stack_ret' + t1.stack_space) t1.stack)`
           by (TIDY_ABBREVS >> simp[]) >>
        POP_ASSUM (SUBST_ALL_TAC) >>
        TIDY_ABBREVS >>
        qpat_x_assum `DROP (num_stack_ret' + t1.stack_space) t1.stack = h :: _` kall_tac >>
        simp[GSYM EL,ADD1] >>
        `nn > 0` by 
           (`EVEN nn` by fs[] >>
            fs[EVEN_EXISTS] >>
            simp[DECIDE ``2 * (m :num) > 0 <=> m > 0``] >>
            fs[])
        fs[] >>
        fs[LLOOKUP_THM,LENGTH_TAKE_EQ_MIN,MIN_ADD, ONCE_REWRITE_RULE[ADD_SYM] MIN_ADD] >>
        qpat_x_assum `DROP _ _ = DROP _ _` mp_tac
        simp[Abbr`num_stack_ret'`,EL_DROP] >>
        fs[] >>
        cheat
        )
        (*NON-GC cutset*)
        strip_tac >>
        qhdtm_x_assum  `cut_envs`
        (strip_assume_tac o SRULE[AllCaseEqs(),cut_envs_def,cut_names_def]) >> 
        rveq >> full_simp_tac(srw_ss())[domain_inter] >>
        fs[lookup_inter]
(*
        ntac 2 strip_tac>>
        fsrw_tac[][lookup_insert,convs_def]>>
        IF_CASES_TAC>-
          simp[]>>
        `nn ∈ domain (fromAList l0)` by metis_tac[domain_lookup]>>
        `nn ∈ domain x1 ∧ nn ∈ domain s.locals` by (
          fsrw_tac[][cut_env_def]>>
          `nn ∈ domain x'` by rfs[]>>
          rveq>>
          fsrw_tac[][domain_inter])>>
        res_tac>>simp[]>>
        fsrw_tac[][domain_lookup]>>
        fs[] >>
        last_x_assum (qspecl_then [`nn`,`v'`]mp_tac)>>
        fs[] >>
        strip_tac>>
        fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack'''''` mp_tac>>
        qpat_abbrev_tac`ls = DROP A B`>>
        Cases_on`ls`>>simp[abs_stack_def]>>
        rpt (TOP_CASE_TAC >>simp[])>>
        strip_tac>>
        qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        strip_tac>>
        fsrw_tac[][lookup_fromAList]>>
        `MEM (nn,v) l` by metis_tac[ALOOKUP_MEM]>>
        `MEM (nn DIV 2,v) (MAP_FST adjust_names l)` by
          (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
          metis_tac[])>>
        simp[LLOOKUP_THM]>>
        imp_res_tac filter_bitmap_MEM>>
        imp_res_tac MEM_index_list_EL>>
        pop_assum mp_tac>>
        simp[LENGTH_TAKE,EL_TAKE]>>
        Cases_on`LENGTH x''`>>
        fsrw_tac[][]>>simp[]>>
        fsrw_tac[][state_rel_def]>>
        `k + SUC n'' - nn DIV 2 = SUC (k+ SUC n'' - (nn DIV 2+1))` by intLib.COOPER_TAC>>
        pop_assum mp_tac >>
        qpat_x_assum `if x'' = [] then f = 0 else f = SUC n'' + 1` mp_tac >>
        pop_assum mp_tac >>
        qpat_x_assum `nn DIV 2 < _` mp_tac >>
        qpat_x_assum `_ <= nn DIV 2` mp_tac >>
        qpat_x_assum `¬(LENGTH _ < SUC n'')` mp_tac >>
        rpt(pop_assum kall_tac) >> rpt strip_tac >>
        rev_full_simp_tac(std_ss ++ ARITH_ss)[GSYM LENGTH_NIL] >>
        simp[EL_TAKE] >>
        rw[EL_CONS_IF,PRE_SUB1] >>
        match_mp_tac EL_TAKE >>
        intLib.COOPER_TAC
*)
        rename1`EVEN nn`>>
        `nn ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
        `nn ∈ domain x1 ∧ nn ∈ domain s.locals` by (
          fsrw_tac[][cut_env_def]>>
          `nn ∈ domain x'` by rfs[]>>
          rveq>>
          fsrw_tac[][domain_inter])>>
        res_tac>>simp[]>>
        fsrw_tac[][domain_lookup]>>
        last_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
        simp[LLOOKUP_THM]>>
        strip_tac>>
        fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack'''''` mp_tac>>
        qpat_abbrev_tac`ls = DROP A B`>>
        Cases_on`ls`>>simp[abs_stack_def]>>
        rpt (TOP_CASE_TAC >>simp[])>>
        strip_tac>>
        qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        strip_tac>>
        fsrw_tac[][lookup_fromAList]>>
        `MEM (nn,v) l` by metis_tac[ALOOKUP_MEM]>>
        `MEM (nn DIV 2,v) (MAP_FST adjust_names l)` by
          (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
          metis_tac[])>>
        simp[LLOOKUP_THM]>>
        imp_res_tac filter_bitmap_MEM>>
        imp_res_tac MEM_index_list_EL>>
        pop_assum mp_tac>>
        simp[LENGTH_TAKE,EL_TAKE]>>
        Cases_on`LENGTH x''`>>
        fsrw_tac[][]>>simp[]>>
        fsrw_tac[][state_rel_def]>>
        `k + SUC n'' - nn DIV 2 = SUC (k+ SUC n'' - (nn DIV 2+1))` by intLib.COOPER_TAC>>
        pop_assum mp_tac >>
        qpat_x_assum `if x'' = [] then f = 0 else f = SUC n'' + 1` mp_tac >>
        pop_assum mp_tac >>
        qpat_x_assum `nn DIV 2 < _` mp_tac >>
        qpat_x_assum `_ <= nn DIV 2` mp_tac >>
        qpat_x_assum `¬(LENGTH _ < SUC n'')` mp_tac >>
        rpt(pop_assum kall_tac) >> rpt strip_tac >>
        rev_full_simp_tac(std_ss ++ ARITH_ss)[GSYM LENGTH_NIL] >>
        simp[EL_TAKE] >>
        rw[EL_CONS_IF,PRE_SUB1] >>
        match_mp_tac EL_TAKE >>
        intLib.COOPER_TAC
        )>>
      LABEL_X_ASSUM "IND" mp_tac \\ simp[] \\
      disch_then drule \\
      disch_then (drule_at (Pos (el 3))) \\
      impl_tac >-
        (fsrw_tac[][convs_def,Abbr`stack_state2`]>>
        simp[CONJ_ASSOC]>>
        REVERSE CONJ_TAC
        >- (
          qpat_x_assum`A<2 * _ + 2 * _:num` mp_tac>>
          simp[wordLangTheory.max_var_def])>>
        REVERSE CONJ_TAC
        >- (
          fs [comp_def,get_labels_def,get_labels_copy_ret] \\
          imp_res_tac evaluate_mono \\ fs[] \\
          rpt (qpat_x_assum `subspt _ _` mp_tac) \\
          rpt (qpat_x_assum `get_labels _  ⊆ _` mp_tac) \\
          rpt (pop_assum kall_tac) \\
          metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
        rw[]
        >- (
          imp_res_tac wLive_LENGTH>>
          fs[])
        >- (
          imp_res_tac wLive_LENGTH>>
          rfs[]>>
          imp_res_tac evaluate_mono >>
          fs[]>>
          imp_res_tac IS_PREFIX_LENGTH>>
          fs[])
        >> (
          imp_res_tac wLive_LENGTH>>
          rfs[]>>
          imp_res_tac evaluate_mono >>
          fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
      rw[]>>
      `x.handler = s.handler`
        by (qhdtm_x_assum `pop_env` mp_tac >>
            rw[pop_env_def] >> simp[]) >>
      fs[] >>
      qexists_tac`ck'`>>
      fsrw_tac[][Abbr`stack_state2`])
    >- ( (*Exception*)
      qexists_tac`0`>> fs[]>>
      `word_state.handler = s.handler` by
        simp[Abbr`word_state`,call_env_def,push_env_def,env_to_list_def,dec_clock_def]>>
      imp_res_tac state_rel_IMP_LENGTH>>
      Q.ISPECL_THEN [`prog`,`word_state`] assume_tac evaluate_stack_swap>>rfs[]>>
      fs[push_env_def,env_to_list_def,LET_THM]>>
      `s.handler+1 ≤ LENGTH lens` by
        (*because it can't be the top frame of word_state, which is NONE*)
        (CCONTR_TAC>>
        `s.handler+1 =LENGTH s.stack+1` by DECIDE_TAC>>
        fs[Abbr`word_state`,call_env_def,dec_clock_def,LASTN_CONS]>>
        fs[LASTN_CONS_ID,GSYM ADD1])>>
      fs[LASTN_CONS] >>
      asm_exists_tac >> fs[]))

      >- (
        (*the stackLang evaluation halts*)
        rev_full_simp_tac std_ss [] >>
        rw[]>>
        qexists_tac`ck`>>
        fs[Abbr`stack_state`]>>
        `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
        fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
        conj_tac >- metis_tac[IS_PREFIX_TRANS,pop_env_ffi,wordPropsTheory.evaluate_io_events_mono] >>
        cruft_tac >>
        dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
        rveq >>
        PURE_REWRITE_TAC [set_var_def,state_accfupds] >>
        rpt(qhdtm_x_assum `LET` kall_tac) >>
        qpat_x_assum `pop_env _ = _` mp_tac >>
        SIMP_TAC std_ss [pop_env_def,CaseEq"list",CaseEq"stack_frame",PULL_EXISTS,
                         CaseEq"option",CaseEq"prod"] >>
        rpt strip_tac >> rveq >> rw[])>>
      strip_tac>>
      `state_rel ac k f f' (set_vars x0 l x'') t1 lens ∧ x''.handler = s.handler` by (
        rev_full_simp_tac std_ss [] >>
        qpat_x_assum`!a b c d e f. P` kall_tac>>
        Q.ISPECL_THEN [`q'`,`word_state`] assume_tac evaluate_stack_swap>>
        rfs[Abbr`word_state`]>>
        fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
        qpat_x_assum`pop_env A = B` mp_tac>>
        simp[pop_env_def]>>
        rpt(TOP_CASE_TAC>>fsrw_tac[][s_key_eq_def,s_frame_key_eq_def])>>
        pop_assum kall_tac>>
        strip_tac>>
        rveq>>fsrw_tac[][state_rel_def,set_vars_def]>>
        CONJ_TAC>-
          metis_tac[evaluate_consts]>>
        CONJ_ASM1_TAC>- (
          fsrw_tac[][LET_THM]>>
          imp_res_tac stack_rel_cons_LEN_NONE>>
          fsrw_tac[][LENGTH_DROP]>>
          Cases_on`f'`>>fsrw_tac[][]>>
          simp[])>>
        CONJ_TAC>-
          simp[wf_alist_insert,wf_fromAList,wf_union]>>
        CONJ_TAC >-
          (cruft_tac >>
           srw_tac[][the_eqn,OPTION_MAP2_DEF,IS_SOME_EXISTS] >>
           TOP_CASE_TAC >> fsrw_tac[][the_eqn] >> intLib.COOPER_TAC) >>
        CONJ_ASM1_TAC >-
          (cruft_tac >>
           fsrw_tac[][the_eqn,stack_size_eq,stack_size_eq,IS_SOME_EXISTS,OPTION_MAP2_DEF]
          ) >>
        CONJ_ASM1_TAC >-
          (cruft_tac >>
           fsrw_tac[][the_eqn,stack_size_eq,stack_size_eq,IS_SOME_EXISTS,OPTION_MAP2_DEF]
          ) >>
        CONJ_TAC >-
          (strip_tac >> res_tac >>
           cruft_tac >>
           qpat_x_assum `evaluate _ = (_,r'')` assume_tac >>
           dxrule_then drule evaluate_stack_max_IS_SOME >>
           strip_tac >>
           fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,stack_size_eq] >>
           fsrw_tac[][the_eqn,OPTION_MAP2_DEF,IS_SOME_EXISTS] >>
           fsrw_tac[][the_eqn,stack_size_eq,stack_size_eq,
                      PULL_EXISTS] >>
           imp_res_tac s_key_eq_stack_size >>
           fsrw_tac[][] >> fsrw_tac[][OPTION_MAP2_DEF] >>
           rveq >> fsrw_tac[][] >>
           fsrw_tac[][Abbr `stack_state`] >>
           qpat_x_assum `_ = LENGTH t1.stack - t1.stack_space` (mp_tac o GSYM) >>
           fsrw_tac[][] >>
           strip_tac >>
           rename1 `s.locals_size = SOME lsize` >>
           `lsize = f` suffices_by metis_tac[SUB_ADD_EQ] >>
           fsrw_tac[][LET_THM] >>
           imp_res_tac stack_rel_cons_locals_size >>
           fsrw_tac[][miscTheory.the_def] >>
           Cases_on `f' = 0` >- fsrw_tac[][]
           >- (qpat_x_assum `if f' = 0 then f = 0 else f = f' + 1` mp_tac >>
               pop_assum mp_tac >>
               rpt(pop_assum kall_tac) >> rw[])
          ) >>
        ntac 3 (pop_assum kall_tac) >>
        rpt(WEAKEN_TAC (can (find_term (same_const ``the``)))) >>
        rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
        fsrw_tac[][LET_THM]>>
        CONJ_TAC>-
          (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
          metis_tac[stack_rel_DROP_NONE])>>
        ntac 2 strip_tac>>
        fsrw_tac[][lookup_alist_insert,convs_def]
        reverse TOP_CASE_TAC>-(
             `MEM (n'',x'') (ZIP (x0,l))`
               by (DEP_REWRITE_TAC[ MEM_ALOOKUP ] >>
               simp[MAP_ZIP] >>
               qpat_assum `x0 = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
               simp[ALL_DISTINCT_GENLIST]) >>
             pop_assum mp_tac >>
             simp[MEM_ZIP] >>
             ntac 2 strip_tac >>
             rveq >>
             qpat_assum `x0 = _` (fn x => SUBST_TAC [x]) >>
             simp[EL_GENLIST,EVEN_DOUBLE] >>
             first_x_assum drule >>
             IF_CASES_TAC >> simp[] >>
             cheat) >>
        (**)
        rename1`EVEN nn`>>
        `nn ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
        `nn ∈ domain x1 ∧ nn ∈ domain s.locals` by (
          fsrw_tac[][cut_env_def]>>
          `nn ∈ domain x'` by rfs[]>>
          rveq>>
          fsrw_tac[][domain_inter])>>
        res_tac>>simp[]>>
        fsrw_tac[][domain_lookup]>>
        last_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
        simp[LLOOKUP_THM]>>
        strip_tac>>
        fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack'''''` mp_tac>>
        qpat_abbrev_tac`ls = DROP A B`>>
        Cases_on`ls`>>simp[abs_stack_def]>>
        rpt (TOP_CASE_TAC >>simp[])>>
        strip_tac>>
        qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        strip_tac>>
        fsrw_tac[][lookup_fromAList]>>
        `MEM (nn,v) l` by metis_tac[ALOOKUP_MEM]>>
        `MEM (nn DIV 2,v) (MAP_FST adjust_names l)` by
          (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
          metis_tac[])>>
        simp[LLOOKUP_THM]>>
        imp_res_tac filter_bitmap_MEM>>
        imp_res_tac MEM_index_list_EL>>
        pop_assum mp_tac>>
        simp[LENGTH_TAKE,EL_TAKE]>>
        Cases_on`LENGTH x''`>>
        fsrw_tac[][]>>simp[]>>
        fsrw_tac[][state_rel_def]>>
        `k + SUC n'' - nn DIV 2 = SUC (k+ SUC n'' - (nn DIV 2+1))` by intLib.COOPER_TAC>>
        pop_assum mp_tac >>
        qpat_x_assum `if x'' = [] then f = 0 else f = SUC n'' + 1` mp_tac >>
        pop_assum mp_tac >>
        qpat_x_assum `nn DIV 2 < _` mp_tac >>
        qpat_x_assum `_ <= nn DIV 2` mp_tac >>
        qpat_x_assum `¬(LENGTH _ < SUC n'')` mp_tac >>
        rpt(pop_assum kall_tac) >> rpt strip_tac >>
        rev_full_simp_tac(std_ss ++ ARITH_ss)[GSYM LENGTH_NIL] >>
        simp[EL_TAKE] >>
        rw[EL_CONS_IF,PRE_SUB1] >>
        match_mp_tac EL_TAKE >>
        intLib.COOPER_TAC
        )>>
      imp_res_tac stackPropsTheory.evaluate_add_clock>>
      ntac 3 (pop_assum kall_tac)>>
      rveq>>fsrw_tac[][]>>
      first_x_assum(qspecl_then[`k`,`f`,`f'`,`t1`] mp_tac)>>
      disch_then (drule_at Any)>>
      qpat_x_assum`comp ac x2 _ _ = _` assume_tac>>
      disch_then (drule_at Any)>>
      impl_tac>-
        (fsrw_tac[][convs_def]>>
        simp[CONJ_ASSOC]>>
        REVERSE CONJ_TAC
        >- (
          qpat_x_assum`A<2 * _ + 2 * _:num` mp_tac>>
          simp[wordLangTheory.max_var_def])>>
        REVERSE CONJ_TAC
        >- (
          fs [comp_def,get_labels_def,get_labels_copy_ret] \\
          imp_res_tac evaluate_mono \\ fs[] \\
          rpt (qpat_x_assum `subspt _ _` mp_tac) \\
          rpt (qpat_x_assum `get_labels _  ⊆ _` mp_tac) \\
          rpt (pop_assum kall_tac) \\
          metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
        rw[]
        >- (
          imp_res_tac wLive_LENGTH>>
          fs[])
        >- (
          imp_res_tac wLive_LENGTH>>
          rfs[]>>
          imp_res_tac evaluate_mono >>
          fs[]>>
          imp_res_tac IS_PREFIX_LENGTH>>
          fs[])
        >> (
          imp_res_tac wLive_LENGTH>>
          rfs[]>>
          imp_res_tac evaluate_mono >>
          fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
      rw[]>>
      qexists_tac`ck'`>>
      fsrw_tac[][Abbr`stack_state2`]>>
      IF_CASES_TAC >> fs[]
      Cases_on `res` >> fs[]
      Cases_on `x'` >> fs[]
      fs[]
      first_x_assum(qspec_then`ck'` mp_tac)>>
      simp[]>>
      fsrw_tac[][ADD_COMM]>>
      pop_assum mp_tac>>
      simp[set_var_def])
    >- ( (*Exception*)
      strip_tac>>
      qexists_tac`ck`>>
      fs[Abbr`stack_state`]>>
      `t.clock -1 + ck = ck +t.clock -1` by DECIDE_TAC>>
      fs[]>>
      rveq>>simp[]>>
      qpat_x_assum `if A then B else C` mp_tac>>
      IF_CASES_TAC>>fs[]>>rveq>>
      fs[]>>
      strip_tac>>
      `word_state.handler = s.handler` by
        simp[Abbr`word_state`,call_env_def,push_env_def,env_to_list_def,dec_clock_def]>>
      imp_res_tac state_rel_IMP_LENGTH>>
      Q.ISPECL_THEN [`q'`,`word_state`] assume_tac evaluate_stack_swap>>rfs[]>>
      fs[push_env_def,env_to_list_def,LET_THM]>>
      `s.handler+1 ≤ LENGTH lens` by
        (*because it can't be the top frame of word_state, which is NONE*)
        (CCONTR_TAC>>
        `s.handler+1 =LENGTH s.stack+1` by DECIDE_TAC>>
        fs[Abbr`word_state`,call_env_def,dec_clock_def,LASTN_CONS]>>
        fs[LASTN_CONS_ID,GSYM ADD1])>>
      fs[LASTN_CONS])
    >> ( (*Timeout, NotEnoughSpace, and Halt*)
      strip_tac>>rev_full_simp_tac std_ss []>>
      qexists_tac`ck`>>
      fsrw_tac[][Abbr`stack_state`]>>
      rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
      `t.clock -1 + ck = ck + t.clock - 1` by DECIDE_TAC>>
      fs[]>>
      rveq>>srw_tac[][]>>
      qpat_x_assum `if A then B else C` mp_tac>>
      IF_CASES_TAC>>fsrw_tac[][]>>rveq>>
      fsrw_tac[][]>>
      strip_tac>>
      fsrw_tac[][state_rel_def])) >>
  note_tac "Handler case">>
  rename1 `push_env _ (SOME handler)` >>
  PairCases_on`handler` >> fs[] >>
  pairarg_tac >> fs[]>>
  qpat_x_assum`_=sprog` sym_sub_tac>>
  simp[stackSemTheory.evaluate_def]>>
  reverse(Cases_on`3 ≤ t5.stack_space`) >- (
    qpat_x_assum `_.stack_space = _.stack_space` kall_tac >>
    qpat_x_assum `LENGTH _.stack = LENGTH _.stack` kall_tac >>
    simp[PushHandler_def,stackSemTheory.evaluate_def]>>
    fsrw_tac[][state_rel_def,compile_result_NOT_2] >>
    IF_CASES_TAC>>fsrw_tac[][] >-
      (simp[call_env_def,flush_state_def]>>
      rw[]>>simp[]>>
      cruft_tac>>
      simp[the_eqn,push_env_def,stack_size_eq,ELIM_UNCURRY]>>
      TOP_CASE_TAC >- fs[OPTION_MAP2_NONE] >>
      fs[OPTION_MAP2_SOME] >>
      rveq >>
      fs[push_env_def,ELIM_UNCURRY,the_eqn] >>
      rveq >>
      fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,stack_size_eq] >>
      imp_res_tac compile_prog_stack_size >>
      fs[GREATER_EQ,GREATER_DEF] >>
      Cases_on `dest` >>
      fsrw_tac[][find_code_def,call_dest_def,CaseEq"option",CaseEq"prod",CaseEq"word_loc",CaseEq"num",
                 add_ret_loc_def] >>
      rveq >> fs[] >>
      imp_res_tac get_vars_length_lemma >>
      rfs[LENGTH_FRONT,prim_recTheory.PRE_DEF,ADD1] >>
      fs[Abbr`sargs`,stack_arg_count_def] >>
      Cases_on `dest'` >> fs[])>>
    qpat_x_assum`res ≠ A` mp_tac>>
    cruft_tac>>
    rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
    fsrw_tac[][dec_clock_def]>>rw[]>>
    imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
    fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
    TRY(qmatch_goalsub_abbrev_tac `_.ffi.io_events ≼ _.ffi.io_events` >>
        metis_tac[pop_env_ffi,IS_PREFIX_TRANS]) >>
    rpt(PRED_ASSUM (is_forall o rand) kall_tac)
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fs[pop_env_def] >>
        fs[CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fs[] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fs[push_env_def] >>
        rw[OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
        rw[] >>
        fs[ELIM_UNCURRY,miscTheory.the_def] >>
        rveq >> fs[stack_size_eq,the_eqn] >>
        rfs[] >>
        (qsuff_tac `fs + LENGTH t.stack + 3 - t.stack_space > LENGTH t.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
         Cases_on `the_right_dest` >>
         fs[add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
            CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"]))
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fs[pop_env_def] >>
        fs[CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fs[] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fs[push_env_def] >>
        rw[OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
        rw[] >>
        fs[ELIM_UNCURRY,miscTheory.the_def] >>
        rveq >> fs[stack_size_eq,the_eqn] >>
        rfs[] >>
        (qsuff_tac `fs + LENGTH t.stack + 3 - t.stack_space > LENGTH t.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         qsuff_tac `t.stack_space <= fs + 3` >- intLib.COOPER_TAC >>
         rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
         Cases_on `the_right_dest` >>
         fs[add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
            CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"])) >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    fs[push_env_def] >>
    rw[OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
    rw[] >>
    fs[ELIM_UNCURRY,miscTheory.the_def] >>
    rveq >> fs[stack_size_eq,the_eqn] >>
    rfs[] >>
    (qsuff_tac `fs + LENGTH t.stack + 3 - t.stack_space > LENGTH t.stack` >-
       (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
     qsuff_tac `t.stack_space < fs + 3` >- intLib.COOPER_TAC >>
     rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
     Cases_on `the_right_dest` >>
     fs[add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
        CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"])
    )>>
  (* Needs to go in wordSem?*)
  drule_then drule (GEN_ALL evaluate_PushHandler)>>
  disch_then(qspecl_then[`handler3`,`handler2`,`handler1`,`handler0`,`f`] mp_tac)>>
  simp[evaluate_PushHandler_clock]>>
  impl_tac THEN1 (
   fs [comp_def,get_labels_def] >>
   imp_res_tac evaluate_mono>>
   `loc_check t.code ⊆ loc_check t5.code` by
     metis_tac[subspt_trans,SUBSET_DEF,loc_check_SUBSET]>>
    fs[SUBSET_DEF,FORALL_PROD,IN_DEF]
   )>>
  strip_tac>>
  simp[StackHandlerArgs_def,StackArgs_def,evaluate_stack_move_seq]>>
  simp[stackSemTheory.evaluate_def]>>
  `t'.use_stack` by fsrw_tac[][state_rel_def]>>fsrw_tac[][]>>
  qpat_abbrev_tac`sargs = stack_arg_count A B C`>>
  Cases_on`t'.stack_space < sargs`>-(
    rpt (qpat_x_assum`!x. _` kall_tac)>>
    qpat_x_assum`_ ⇒ !x. _` kall_tac >>
    IF_CASES_TAC>>fsrw_tac[][]>- (
      simp[call_env_def,flush_state_def]>>
      rw[]>>simp[]>>
      cruft_tac>>
      simp[the_eqn,push_env_def,stack_size_eq,ELIM_UNCURRY]>>
      CONJ_TAC>-
        fsrw_tac[][state_rel_def]>>
      TOP_CASE_TAC >-
        fs[OPTION_MAP2_NONE] >>
      fs[OPTION_MAP2_SOME] >>
      rveq >>
      fsrw_tac[][state_rel_def] >> cruft_tac>>
      fs[push_env_def,ELIM_UNCURRY,the_eqn] >>
      rveq >>
      fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,stack_size_eq] >>
      imp_res_tac compile_prog_stack_size >>
      fs[GREATER_EQ,GREATER_DEF] >>
      Cases_on `dest` >>
      fsrw_tac[][find_code_def,call_dest_def,CaseEq"option",CaseEq"prod",CaseEq"word_loc",CaseEq"num",
                 add_ret_loc_def] >>
      rveq >> fs[] >>
      imp_res_tac get_vars_length_lemma >>
      rfs[LENGTH_FRONT,prim_recTheory.PRE_DEF,ADD1] >>
      fs[Abbr`sargs`,stack_arg_count_def] >>
      Cases_on `dest'` >> fs[] >>
      fs[bad_dest_args_def,ELIM_UNCURRY])>>
    qpat_x_assum`res ≠ A` mp_tac>>
    cruft_tac>>
    qpat_x_assum`t'=_` SUBST_ALL_TAC>>fs[]>>
    rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
    fsrw_tac[][dec_clock_def]>>rw[]>>
    imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
    fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
    TRY(qmatch_goalsub_abbrev_tac `_.ffi.io_events ≼ _.ffi.io_events` >>
        fsrw_tac[][state_rel_def]>>
        metis_tac[pop_env_ffi,IS_PREFIX_TRANS]) >>
    TRY(qpat_x_assum`2 MOD dimword _ = 1`mp_tac>>
      fsrw_tac[][state_rel_def,good_dimindex_def,dimword_def])>>
    fsrw_tac[][state_rel_def]>>
    cruft_tac>>
    rpt(PRED_ASSUM (is_forall o rand) kall_tac)
    (* 5 subgoals *)
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fsrw_tac[][pop_env_def] >>
        fsrw_tac[][CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fsrw_tac[][] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fsrw_tac[][push_env_def] >>
        rw[LET_THM,OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
        rw[] >>
        fsrw_tac[][ELIM_UNCURRY,miscTheory.the_def] >>
        rveq >> fsrw_tac[][stack_size_eq,the_eqn] >>
        rfs[] >>
        (qsuff_tac `fs + LENGTH t4.stack + 3 - t.stack_space > LENGTH t4.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                    stack_size_eq,IS_SOME_OPTION_MAP2_EQ,
                    CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
         rveq >> fsrw_tac[][ADD1] >> rveq >> fsrw_tac[][] >>
         imp_res_tac compile_prog_stack_size >>
         imp_res_tac get_vars_length_lemma >> fsrw_tac[][] >>
         rveq >> fsrw_tac[][bad_dest_args_def] >>
         `t.stack_space = t5.stack_space` by intLib.COOPER_TAC >>
         fs[] >>
         `sargs <= fs` suffices_by intLib.COOPER_TAC >>
         simp[Abbr `sargs`] >> simp[stack_arg_count_def] >>
         Cases_on `dest'` >> rw[stack_arg_count_def]))
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fsrw_tac[][pop_env_def] >>
        fsrw_tac[][CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fsrw_tac[][] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fsrw_tac[][push_env_def] >>
        rw[LET_THM,OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
        rw[] >>
        fsrw_tac[][ELIM_UNCURRY,miscTheory.the_def] >>
        rveq >> fsrw_tac[][stack_size_eq,the_eqn] >>
        rfs[] >>
        (qsuff_tac `fs + LENGTH t4.stack + 3 - t.stack_space > LENGTH t4.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                    stack_size_eq,IS_SOME_OPTION_MAP2_EQ,
                    CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
         rveq >> fsrw_tac[][ADD1] >> rveq >> fsrw_tac[][] >>
         imp_res_tac compile_prog_stack_size >>
         imp_res_tac get_vars_length_lemma >> fsrw_tac[][] >>
         rveq >> fsrw_tac[][bad_dest_args_def] >>
         `t.stack_space = t5.stack_space` by intLib.COOPER_TAC >>
         fs[] >>
         `sargs <= fs` suffices_by intLib.COOPER_TAC >>
         simp[Abbr `sargs`] >> simp[stack_arg_count_def] >>
         Cases_on `dest'` >> rw[stack_arg_count_def])) >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    fsrw_tac[][push_env_def] >>
    rw[LET_THM,OPTION_MAP2_DEF,IS_SOME_EXISTS,the_eqn,ELIM_UNCURRY,stack_size_eq] >>
    rw[] >>
    fsrw_tac[][ELIM_UNCURRY,miscTheory.the_def] >>
    rveq >> fsrw_tac[][stack_size_eq,the_eqn] >>
    rfs[] >>
    (qsuff_tac `fs + LENGTH t4.stack + 3 - t.stack_space > LENGTH t4.stack` >-
      (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
     rename1 `find_code the_right_dest _ _ _ = SOME (_,_,SOME fs)` >>
     Cases_on `the_right_dest` >>
     fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                stack_size_eq,IS_SOME_OPTION_MAP2_EQ,
                CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
     rveq >> fsrw_tac[][ADD1] >> rveq >> fsrw_tac[][] >>
     imp_res_tac compile_prog_stack_size >>
     imp_res_tac get_vars_length_lemma >> fsrw_tac[][] >>
     rveq >> fsrw_tac[][bad_dest_args_def] >>
     `t.stack_space = t5.stack_space` by intLib.COOPER_TAC >>
     fs[] >>
     `sargs <= fs` suffices_by intLib.COOPER_TAC >>
     simp[Abbr `sargs`] >> simp[stack_arg_count_def] >>
     Cases_on `dest'` >> rw[stack_arg_count_def])
    )>>
  simp[]>>fsrw_tac[][]>>
  qabbrev_tac`t6 = t' with stack_space :=t'.stack_space -sargs`>>
  `!ck. t' with <|stack_space:=t'.stack_space - sargs; clock:=ck+t.clock|> = t6 with clock:=ck+t.clock` by
      simp[stackSemTheory.state_component_equality,Abbr`t6`]>>
  simp[evaluate_stack_move_clock]>>
  Q.ISPECL_THEN [`sargs`,`0n`,`t6`,`f+3`] mp_tac evaluate_stack_move>>
  impl_keep_tac>- (
    qpat_x_assum`s.clock ≠ 0 ⇒ P` kall_tac>>
    qpat_x_assum`∀a b c. P` kall_tac>>
    qpat_x_assum`∀a b. P` kall_tac>>
    unabbrev_all_tac>>simp[]>>
    fsrw_tac[][state_rel_def,ADD_COMM]>>
    fsrw_tac[][convs_def]>>
    qpat_x_assum`args = A` SUBST_ALL_TAC>>
    fsrw_tac[][wordLangTheory.max_var_def,LET_THM]>>
    fsrw_tac[][list_max_GENLIST_evens2]>>
    `2*LENGTH args < 2*f'+2*k` by
      (qpat_x_assum`A<2*f' +2*k` mp_tac>>
      simp[MAX_DEF])>>
    `LENGTH args < f' +k` by simp[]>>
    simp[stack_arg_count_def]>>
    TOP_CASE_TAC>>
    Cases_on`f'`>>fsrw_tac[][]>>
    qpat_x_assum`A<B:num` mp_tac>>
    rpt (pop_assum kall_tac)>>
    DECIDE_TAC)>>
  strip_tac>>simp[]>>
  `find_code dest' (t''.regs \\0) t''.code = find_code dest' t4.regs t4.code` by (
    `subspt t4.code t''.code` by
       (unabbrev_all_tac>>
       fs[stackSemTheory.state_component_equality]>>
       metis_tac[evaluate_mono])>>
     Cases_on`dest'`>>fsrw_tac[][stackSemTheory.find_code_def]>>
     qpat_x_assum`A=SOME stack_prog` mp_tac
     >-
       metis_tac[subspt_def,domain_lookup]>>
     qpat_x_assum`A=(q0,INR y)` mp_tac>>
     Cases_on`dest`>>simp[call_dest_def]>>
     IF_CASES_TAC>>simp[]>>
     simp[wReg2_def]>>IF_CASES_TAC>>fsrw_tac[][]
     >- (
        `LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by (
          fs[convs_def]>>
          qpat_x_assum`args = A` SUBST_ALL_TAC>>
          `LENGTH args <> 0` by (strip_tac \\ fs[]) >>
          drule LAST_GENLIST_evens>>
          LET_ELIM_TAC>>simp[]>>
          Cases_on`reg`>>fs[]>>
          rename1`SUC xx DIV _ ≠ _`>>
          Cases_on`xx`>>fs[]>>
          simp[ADD_DIV_RWT,ADD1])>>
        strip_tac>>rveq>>
        simp[DOMSUB_FLOOKUP_THM]>>
        fs[stackSemTheory.get_var_def,Abbr`t6`]>>
        qpat_x_assum`subspt _ _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        EVERY_CASE_TAC>>rw[]>>
        metis_tac[subspt_def,domain_lookup])
     >-
       (strip_tac>>rveq>>
       simp[DOMSUB_FLOOKUP_THM]>>
       fsrw_tac[][stackSemTheory.get_var_def,Abbr`t6`,FLOOKUP_UPDATE]>>
       qpat_x_assum`subspt _ _` mp_tac>>
       rpt (pop_assum kall_tac)>>
       every_case_tac>>fs[subspt_def]>>
       metis_tac[domain_lookup]))>>
  simp[]>>
  IF_CASES_TAC>-
    (strip_tac >> fsrw_tac[][] >> rveq >>qexists_tac`0`>>fsrw_tac[][state_rel_def]>>
    fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality])>>
  `t.clock ≠ 0` by
    metis_tac[state_rel_def]>>
  fsrw_tac[][compile_prog_def,LET_THM]>>
  pairarg_tac>>fsrw_tac[][]>>
  rveq>>
  qpat_abbrev_tac `m = MAX (max_var q' DIV 2 +1 - k) (LENGTH q - k)`>>
  qpat_abbrev_tac `m' = (if _ then 0 else m + 1)`>>
  simp[stackSemTheory.evaluate_def]>>
  `t''.use_stack` by
    fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality]>>
  simp[stackSemTheory.set_var_def,stackSemTheory.dec_clock_def]>>
  Cases_on`t''.stack_space < m' - (LENGTH q-k)`>- (
    cruft_tac>>
    qpat_x_assum `t''.stack_space = t6.stack_space` assume_tac >>
    fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
    MAP_EVERY qunabbrev_tac [`sargs`,`t6`]>>
    fsrw_tac[][stackSemTheory.state_component_equality]>>
    qpat_x_assum`res ≠ A` mp_tac>>
    rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
    fsrw_tac[][dec_clock_def]>>rw[]>>
    imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
    fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
    TRY(qmatch_goalsub_abbrev_tac `_.ffi.io_events ≼ _.ffi.io_events` >>
        metis_tac[IS_PREFIX_TRANS,pop_env_ffi]) >>
    cruft_tac >>
    rpt(PRED_ASSUM (is_forall o rand) kall_tac) >>
    rpt(PRED_ASSUM is_forall kall_tac)
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fsrw_tac[][pop_env_def] >>
        fsrw_tac[][CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fsrw_tac[][] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
                   IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP] >>
        fsrw_tac[][the_eqn] >>
        TOP_CASE_TAC >> fsrw_tac[][OPTION_MAP2_SOME,OPTION_MAP2_NONE] >>
        rveq >> fsrw_tac[][stack_size_eq,miscTheory.the_def] >>
        TRY(qmatch_goalsub_abbrev_tac `LENGTH a1 + 1 > LENGTH a1` >>
            rpt(WEAKEN_TAC (K true)) >> rw[] >> NO_TAC) >>
        rev_full_simp_tac std_ss [] >>
        rveq >>
        (qsuff_tac `LENGTH t4.stack - t'.stack_space + m' > LENGTH t4.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         qsuff_tac `t'.stack_space < m'` >- DECIDE_TAC >>
         rename1 `_ < stack_arg_count the_right_dest _ _ + _` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][stack_arg_count_def] >>
         imp_res_tac get_vars_length_lemma >>
         fsrw_tac[][] >>
         rename1 `find_code the_right_dest _ _ _ = _` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                    CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
         rveq >> fsrw_tac[][ADD1] >> rveq >>
         fsrw_tac[][bad_dest_args_def,LET_THM] >>
         `f <> 0` by(CCONTR_TAC >> fsrw_tac[][]) >> fsrw_tac[][] >>
         rveq >>
         qpat_x_assum `0 < m' - _` mp_tac >>
         qpat_x_assum `t'.stack_space < _ + _` mp_tac >>
         rpt(pop_assum kall_tac) >> intLib.COOPER_TAC))
    >- (drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[] >>
        fsrw_tac[][pop_env_def] >>
        fsrw_tac[][CaseEq"list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
        rveq >> fsrw_tac[][] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
                   IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP] >>
        fsrw_tac[][the_eqn] >>
        TOP_CASE_TAC >> fsrw_tac[][OPTION_MAP2_SOME,OPTION_MAP2_NONE] >>
        rveq >> fsrw_tac[][stack_size_eq,miscTheory.the_def] >>
        TRY(qmatch_goalsub_abbrev_tac `LENGTH a1 + 1 > LENGTH a1` >>
            rpt(WEAKEN_TAC (K true)) >> rw[] >> NO_TAC) >>
        rev_full_simp_tac std_ss [] >>
        rveq >>
        (qsuff_tac `LENGTH t4.stack - t'.stack_space + m' > LENGTH t4.stack` >-
          (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
         qsuff_tac `t'.stack_space < m'` >- DECIDE_TAC >>
         rename1 `_ < stack_arg_count the_right_dest _ _ + _` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][stack_arg_count_def] >>
         imp_res_tac get_vars_length_lemma >>
         fsrw_tac[][] >>
         rename1 `find_code the_right_dest _ _ _ = _` >>
         Cases_on `the_right_dest` >>
         fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                    CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
         rveq >> fsrw_tac[][ADD1] >> rveq >>
         fsrw_tac[][bad_dest_args_def,LET_THM] >>
         `f <> 0` by(CCONTR_TAC >> fsrw_tac[][]) >> fsrw_tac[][] >>
         rveq >>
         qpat_x_assum `0 < m' - _` mp_tac >>
         qpat_x_assum `t'.stack_space < _ + _` mp_tac >>
         rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)) >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
               IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP] >>
    fsrw_tac[][the_eqn] >>
    TOP_CASE_TAC >> fsrw_tac[][OPTION_MAP2_SOME,OPTION_MAP2_NONE] >>
    rveq >> fsrw_tac[][stack_size_eq,miscTheory.the_def] >>
    TRY(qmatch_goalsub_abbrev_tac `LENGTH a1 + 1 > LENGTH a1` >>
        rpt(WEAKEN_TAC (K true)) >> rw[] >> NO_TAC) >>
    rev_full_simp_tac std_ss [] >>
    rveq >>
    (qsuff_tac `LENGTH t4.stack - t'.stack_space + m' > LENGTH t4.stack` >-
      (rpt (pop_assum kall_tac) >> rw[MAX_DEF]) >>
     qsuff_tac `t'.stack_space < m'` >- DECIDE_TAC >>
     rename1 `_ < stack_arg_count the_right_dest _ _ + _` >>
     Cases_on `the_right_dest` >>
     fsrw_tac[][stack_arg_count_def] >>
     imp_res_tac get_vars_length_lemma >>
     fsrw_tac[][] >>
     rename1 `find_code the_right_dest _ _ _ = _` >>
     Cases_on `the_right_dest` >>
     fsrw_tac[][add_ret_loc_def,find_code_def,call_dest_def,ELIM_UNCURRY,
                CaseEq "option",CaseEq "word_loc",CaseEq "prod",CaseEq"num",CaseEq "bool"] >>
     rveq >> fsrw_tac[][ADD1] >> rveq >>
     fsrw_tac[][bad_dest_args_def,LET_THM] >>
     `f <> 0` by(CCONTR_TAC >> fsrw_tac[][]) >> fsrw_tac[][] >>
     rveq >>
     qpat_x_assum `0 < m' - _` mp_tac >>
     qpat_x_assum `t'.stack_space < _ + _` mp_tac >>
     rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
    )>>
  simp[]>>
  qpat_abbrev_tac`word_state = call_env q r' st`>>
  qabbrev_tac`stack_state =
    t'' with <|regs:=t''.regs|+(0,Loc x3 x4);
              stack_space:=t''.stack_space - (m'-(LENGTH q-k));
              clock:=t.clock-1|>`>>
  `state_rel ac k m' m word_state stack_state (f'::lens)` by (
    ntac 3 (qpat_x_assum`!a b. P` kall_tac)>>
    `sargs = (LENGTH q -k)` by
      (simp[stack_arg_count_def,Abbr`sargs`]>>
      qpat_x_assum`call_dest A B C =(q0,dest')` mp_tac>>
      qpat_x_assum`A=SOME(q,q',r')` mp_tac>>
      imp_res_tac get_vars_length_lemma>>
      Cases_on`dest`>-
        (fsrw_tac[][bad_dest_args_def]>>
        simp[find_code_def,call_dest_def,add_ret_loc_def]>>
        `LENGTH args ≠ 0` by fsrw_tac[][LENGTH_NIL]>>
        rpt TOP_CASE_TAC>>simp[]>>
        rw[]>>
        pairarg_tac>>fsrw_tac[][]>>
        Cases_on`x`>>fsrw_tac[][]>>
        simp[])>>
      fsrw_tac[][bad_dest_args_def]>>
      simp[find_code_def,call_dest_def,add_ret_loc_def]>>
      rpt TOP_CASE_TAC>>simp[]>>
      rw[]>>
      simp[])>>
    `sargs ≤ m ∧ m ≤ m'` by
     (fs[markerTheory.Abbrev_def]
      \\ rveq \\ rw[MAX_DEF])>>
    fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
    PURE_ONCE_REWRITE_TAC[dec_clock_def,call_env_def,push_env_def,env_to_list_def]>>
    fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality]>>
    fsrw_tac[][state_rel_def]>>
    conj_tac >- (simp[dec_clock_def, call_env_def, push_env_def]>>
                 simp[env_to_list_def] >> simp[FUN_EQ_THM]) >>
    conj_tac >- (simp[dec_clock_def, call_env_def, push_env_def]>>
                 simp[env_to_list_def] >> simp[FUN_EQ_THM]) >>
    conj_tac >- (fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,dec_clock_def]) >>
    conj_tac >- (simp[dec_clock_def, call_env_def, push_env_def]>>
                 simp[env_to_list_def] >> simp[FUN_EQ_THM]) >>
    conj_tac >- (simp[dec_clock_def, call_env_def, push_env_def]>>
                 simp[env_to_list_def] >> simp[FUN_EQ_THM]) >>
    conj_tac >- metis_tac[] >>
    conj_tac >- (cruft_tac >> rveq >>
                 `m' <= LENGTH t4.stack` by intLib.COOPER_TAC >>
                 qsuff_tac `t'.stack_space <= LENGTH t4.stack` >-
                   (qpat_x_assum `¬(t'.stack_space < LENGTH q - k)` mp_tac >>
                    ntac 3 (pop_assum mp_tac) >>
                    rpt(pop_assum kall_tac) >>
                    rw[SUB_RIGHT_SUB,SUB_RIGHT_ADD]) >>
                 intLib.COOPER_TAC
                ) >>
    conj_tac >- (simp_tac(srw_ss())[Abbr`m`,Abbr`m'`,MAX_DEF]
                   \\ rpt(pop_assum kall_tac) \\ rw[]) >>
    conj_tac >- simp[wf_fromList2] >>
    conj_tac >- (cruft_tac >>
                 rw[the_eqn,OPTION_MAP2_DEF,IS_SOME_EXISTS,push_env_def,ELIM_UNCURRY,
                    stack_size_eq] >>
                 fsrw_tac[][miscTheory.the_def] >>
                 rveq >>
                 `f ≠ 0` by(CCONTR_TAC >> full_simp_tac std_ss []) >>
                 full_simp_tac std_ss [] >>
                 fsrw_tac[][push_env_def,miscTheory.the_def,LET_THM,ELIM_UNCURRY,
                            IS_SOME_OPTION_MAP2_EQ,stack_size_eq] >>
                 rveq >>
                 qpat_x_assum `t4.stack_space = t.stack_space` (assume_tac o GSYM) >>
                 srw_tac[][] >>
                 qmatch_goalsub_abbrev_tac `MAX _ a1` >>
                 `LENGTH t4.stack <= t'.stack_space + a1`
                   suffices_by (pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
                                srw_tac[][MAX_DEF] >> DECIDE_TAC) >>
                 qunabbrev_tac `a1` >>
                 DECIDE_TAC) >>
    conj_tac >- (cruft_tac >>
                 fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
                          IS_SOME_OPTION_MAP2_EQ]) >>
    conj_tac >- (cruft_tac >>
                 fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
                          IS_SOME_OPTION_MAP2_EQ]) >>
    conj_tac >- (cruft_tac >>
                 fsrw_tac[][push_env_def,LET_THM,ELIM_UNCURRY,stack_size_eq,
                          IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP] >>
                 rpt strip_tac >> fsrw_tac[][IS_SOME_EXISTS,miscTheory.the_def] >>
                 rveq >>
                 drule stack_rel_cons_locals_size >>
                 srw_tac[][miscTheory.the_def] >>
                 fsrw_tac[][miscTheory.the_def] >>
                 rveq >>
                 `f' <> 0` by(CCONTR_TAC >> fsrw_tac[][]) >>
                 qpat_x_assum `if f' = 0 then f = 0 else f = f' + 1` mp_tac >>
                 srw_tac[][] >>
                 `LENGTH q - k <= m'` by DECIDE_TAC >>
                 srw_tac[][SUB_SUB_SUB_MAX,MAX_LE] >>
                 `m' <= t'.stack_space` suffices_by
                   (pop_assum mp_tac >> rpt(pop_assum kall_tac) >> DECIDE_TAC) >>
                 DECIDE_TAC) >>
    rpt(WEAKEN_TAC (can (find_term (same_const ``the``)))) >>
    rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
    fsrw_tac[][LET_THM]>>
    conj_tac >-
        (qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
         simp[push_env_def,env_to_list_def,dec_clock_def]>>
         fsrw_tac[][DROP_DROP_EQ]>>
         qpat_x_assum `DROP _ _ = DROP _ _` mp_tac >>
         simp[]) >>
    ntac 3 strip_tac>>
    rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
    imp_res_tac (GSYM domain_lookup)>>
    imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
    fsrw_tac[][wordConvsTheory.post_alloc_conventions_def,wordConvsTheory.call_arg_convention_def]>>
    `isPREFIX q (Loc x3 x4::x)` by
       (qpat_x_assum`A=SOME(q,q',r')` mp_tac>>
       Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
       EVERY_CASE_TAC>>rw[]>>
       Cases_on`x`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
    imp_res_tac lookup_fromList2_prefix>>
    rename1`nn DIV 2 < k`>>
    Cases_on`nn=0`>-
      (fsrw_tac[][lookup_fromList2,lookup_fromList]>>
      simp[FLOOKUP_UPDATE])>>
    `lookup nn s.locals = SOME v` by
     (qpat_x_assum`args=A` SUBST_ALL_TAC>>
     imp_res_tac get_vars_fromList2_eq_cons)>>
    fsrw_tac[][LET_THM]>>
    IF_CASES_TAC>- (
      `nn DIV 2 ≠ 0 ∧ nn DIV 2 ≠ k` by (
        Cases_on`nn`>>fsrw_tac[][]>>
        rename1`SUC nn DIV 2`>>
        Cases_on`nn`>>fsrw_tac[][]>>
        fsrw_tac[][ADD_DIV_RWT,ADD1]>>
        pop_assum mp_tac >> rpt(WEAKEN_TAC (K true)) >>
        rw[ADD_DIV_RWT])>>
      fsrw_tac[][FLOOKUP_UPDATE,stackSemTheory.get_var_def]>>
      metis_tac[])>>
    `k ≤ LENGTH q` by (
      fsrw_tac[][lookup_fromList2,lookup_fromList]
      \\ rpt(qpat_x_assum`nn DIV 2 < _`mp_tac)
      \\ qpat_x_assum`¬(nn DIV 2 < _)`mp_tac
      \\ rpt(pop_assum kall_tac)
      \\ decide_tac) >>
    ntac 3 (qpat_x_assum`!a b.P` kall_tac)>>
    fsrw_tac[][]>>
    `LENGTH q = k + sargs` by (
      pop_assum mp_tac >>
      qpat_x_assum`sargs = _ `mp_tac >>
      rpt(pop_assum kall_tac) >> rw[] ) >>
    first_assum SUBST1_TAC >>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    `sargs ≤ m'` by metis_tac[LESS_EQ_TRANS] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    Cases_on `m=0` \\ fsrw_tac[] []
    THEN1
      (fsrw_tac[] [lookup_fromList2,lookup_fromList,Abbr`m'`]>>
       qpat_x_assum`¬(nn DIV 2 < _)`mp_tac >>
       qpat_x_assum`(nn DIV 2 < k + _)`mp_tac >>
       qpat_x_assum`LENGTH q = _`mp_tac >>
       qpat_x_assum`sargs = 0`mp_tac >>
       rpt(pop_assum kall_tac) >>
       decide_tac)>>
    `m' = m+1` by (
      qunabbrev_tac`m'` >>
      IF_CASES_TAC >- (
        qpat_x_assum`m ≤ _`mp_tac >>
        pop_assum(SUBST1_TAC o EQT_INTRO) >>
        qpat_x_assum`m ≠ 0`mp_tac >>
        rpt(pop_assum kall_tac) >>
        rw[] ) >>
      REFL_TAC ) >>
    pop_assum SUBST_ALL_TAC >>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    `m+1 ≤ t'.stack_space` by simp[] >>
    pop_assum mp_tac >>
    qpat_x_assum`_.stack_space ≤ LENGTH t''.stack`mp_tac >>
    simp_tac(srw_ss()++ARITH_ss)[LLOOKUP_THM,EL_TAKE,EL_DROP] >>
    ntac 3 strip_tac >>
    fsrw_tac[][lookup_fromList2,lookup_fromList] >>
    reverse conj_asm2_tac >- simp[] >>
    pop_assum mp_tac >>
    qpat_x_assum`¬(_ < _)`mp_tac >>
    qpat_x_assum`m + 1 ≤ _`mp_tac >>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    ntac 3 strip_tac >>
   first_x_assum(qspecl_then[`nn`,`v`] kall_tac)>>
   first_x_assum(qspecl_then[`nn`,`v`] mp_tac)>>
   rpt(qpat_x_assum`!a b. P` kall_tac)>>
   fsrw_tac[][]>>
   simp[LLOOKUP_THM]>>
   `f+k - (nn DIV 2 +1) < f` by simp[]>>
   fsrw_tac[][EL_TAKE]>>
   qpat_assum`∀x. A ⇒ EL B (DROP t.stack_space t5.stack) = EL D E` mp_tac>>
   disch_then (qspec_then `f+k-(nn DIV 2 +1)` mp_tac)>>
   impl_tac>- (
     rpt(first_x_assum(mp_tac o assert(can (find_term (same_const numSyntax.less_tm)) o concl)))
     \\ rpt(first_x_assum(mp_tac o assert(can (find_term (same_const numSyntax.leq_tm)) o concl)))
     \\ rpt(first_x_assum(mp_tac o assert(can (find_term (aconv ``(=):num->num->bool``)) o concl)))
     \\ rpt (pop_assum kall_tac)
     \\ rw[]) >>
   disch_then SUBST_ALL_TAC>>
   qpat_x_assum`DROP A B = DROP C D` mp_tac>>
   ntac 6 (pop_assum mp_tac) >>
   simp_tac(srw_ss()++ARITH_ss)[] >>
   ntac 5 strip_tac >>
   disch_then sym_sub_tac >>
   first_x_assum (qspec_then`LENGTH q - (nn DIV 2 +1)` mp_tac)>>
   impl_tac>- simp[]>>
   fs[EL_DROP]>>
   qpat_x_assum `t'.stack_space + 3 = t.stack_space` mp_tac>>
   rpt(pop_assum kall_tac)>>
   rw[]>>
   `f' + k - nn DIV 2 + 3 + t'.stack_space = f' + k + t.stack_space - nn DIV 2` by fs[]>>
   fs[])>>
  Cases_on`evaluate(q',word_state)`>>fsrw_tac[][]>>
  first_x_assum(qspecl_then[`k`,`m'`,`m`,`stack_state`] mp_tac)>>
  disch_then (drule_at Any)>>
  disch_then (drule_at Any)>>
  rename1`qres ≠ SOME Error ∧ _`>>
  Cases_on`qres = SOME Error`>>fsrw_tac[][]>>
  impl_tac>- (
    CONJ_ASM1_TAC>- (
      qpat_x_assum`A=SOME(q,q',r')`mp_tac>>
      Cases_on`dest`>>
      fsrw_tac[][state_rel_def,find_code_def]>>
      rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
    CONJ_TAC>- (
      qpat_x_assum`A=SOME(q,q',r')`mp_tac>>
      Cases_on`dest`>>
      fsrw_tac[][state_rel_def,find_code_def]>>
      rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
    simp[CONJ_ASSOC] >>
    reverse CONJ_TAC >-
      (`EVEN (max_var q')` by
          (ho_match_mp_tac max_var_intro>>
          fsrw_tac[][convs_def]>>
          match_mp_tac every_var_mono>>
          HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def,EVEN_MOD2])>>
      unabbrev_all_tac>>fsrw_tac[][EVEN_EXISTS]>>
      rpt (pop_assum kall_tac)>>
      `m * 2 DIV 2 = m` by
        (Q.ISPECL_THEN[`2n`,`m`]assume_tac MULT_DIV>>fsrw_tac[][])>>
      fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
      DECIDE_TAC)>>
    unabbrev_all_tac>>fsrw_tac[][]>>
    imp_res_tac evaluate_mono>>
    rpt (qpat_x_assum`!x. _` kall_tac)>>
    fsrw_tac[][]>>rw[]
    >- (imp_res_tac IS_PREFIX_LENGTH>>
      simp[])
    >- (imp_res_tac comp_IMP_isPREFIX>>
      fsrw_tac[][]>>
      metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
    >>
      drule find_code_IMP_get_labels
      \\ simp[get_labels_def]
      \\ metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])>>
  strip_tac>>
  Cases_on`qres`>>simp[]>>
  Cases_on`x''`>>simp[]
  >- (
    IF_CASES_TAC>>fsrw_tac[][]>>
    Cases_on`pop_env r''`>>fsrw_tac[][]>>
    IF_CASES_TAC>>fsrw_tac[][]>>
    strip_tac>>
    imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
    qpat_x_assum`if A then B else C` mp_tac>>
    IF_CASES_TAC>>fsrw_tac[][]
    >-
      (*the stackLang evaluation halts*)
      (rev_full_simp_tac std_ss[] >>
      rw[]>>
      qexists_tac`ck`>>
      fsrw_tac[][Abbr`stack_state`]>>
      `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
      fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
      conj_tac >- metis_tac[IS_PREFIX_TRANS,pop_env_ffi,wordPropsTheory.evaluate_io_events_mono] >>
      cruft_tac >>
      dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
      rveq >>
      PURE_REWRITE_TAC [set_var_def,state_accfupds] >>
      rpt(qhdtm_x_assum `LET` kall_tac) >>
      qpat_x_assum `pop_env _ = _` mp_tac >>
      SIMP_TAC std_ss [pop_env_def,CaseEq"list",CaseEq"stack_frame",PULL_EXISTS,
                       CaseEq"option",CaseEq"prod"] >>
      rpt strip_tac >> rveq >> rw[])
    >>
    strip_tac>>
    drule_then (drule_then (qspecl_then [`w0`,`dec_clock s`,`r'`,`q`,`handler3`,`handler2`,`handler1`,`f`,`x'`] mp_tac))
      (GEN_ALL evaluate_PopHandler) >>
    impl_tac >-
      (simp[] >>
      Q.ISPECL_THEN [`q'`,`word_state`] assume_tac evaluate_stack_swap>>
      rfs[Abbr`word_state`,convs_def]>>
      `f = f' + 1` by(CCONTR_TAC >> fs[state_rel_def]) >>
      conj_asm1_tac >-
        (fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
         qpat_x_assum`pop_env A = B` mp_tac>>
         simp[pop_env_def]>>
         ntac 4 (TOP_CASE_TAC>>fsrw_tac[][s_key_eq_def,s_frame_key_eq_def])>>
         pop_assum kall_tac>>
         strip_tac>>
         fsrw_tac[][PopHandler_def,stackSemTheory.evaluate_def,LET_THM]>>
         rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
         imp_res_tac stack_rel_cons_LEN_SOME>>
         fsrw_tac[][LENGTH_DROP]>>
         pop_assum mp_tac>>
         simp[SUB_LEFT_LESS_EQ])>>
      conj_tac >-
        (first_x_assum ACCEPT_TAC) >>
      conj_tac >-
         (CCONTR_TAC >> fs[state_rel_def]) >>
      qpat_x_assum`!a b c d e f. P` kall_tac>>
      fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
      qpat_x_assum`pop_env A = B` mp_tac>>
      simp[pop_env_def]>>
      ntac 4 (TOP_CASE_TAC>>fs[s_key_eq_def,s_frame_key_eq_def])>>
      pop_assum kall_tac>>
      strip_tac>>
      rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
      imp_res_tac stack_rel_cons_LEN_SOME>>
      fsrw_tac[][LENGTH_DROP]>>
      rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
      rpt(PRED_ASSUM (exists (curry op = "the") o map (fst o dest_const)
                      o find_terms is_const)
                     kall_tac) >>
      ntac 2 strip_tac>>
      fsrw_tac[][lookup_insert,convs_def]>>
      strip_tac>>
      rename1`EVEN nn`>>
      `nn ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
      `nn ∈ domain x1 ∧ nn ∈ domain s.locals` by
        (fsrw_tac[][cut_env_def]>>
        `nn ∈ domain x'` by rfs[]>>
        rveq>>
        fsrw_tac[][domain_inter])>>
      res_tac>>simp[]>>
      fsrw_tac[][domain_lookup]>>
      last_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
      simp[LLOOKUP_THM]>>
      strip_tac>>
      fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack''''` mp_tac>>
      qpat_abbrev_tac`ls = DROP A B`>>
      Cases_on`ls`>>simp[abs_stack_def]>>
      rpt (TOP_CASE_TAC >>simp[])>>
      strip_tac>>
      qpat_x_assum`stack_rel_aux A B C stack''''` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      strip_tac>>
      fsrw_tac[][lookup_fromAList]>>
      `MEM (nn,v) l` by metis_tac[ALOOKUP_MEM]>>
      `MEM (nn DIV 2,v) (MAP_FST adjust_names l)` by
        (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
        metis_tac[])>>
      simp[LLOOKUP_THM]>>
      imp_res_tac filter_bitmap_MEM>>
      imp_res_tac MEM_index_list_EL>>
      pop_assum mp_tac>>
      simp[LENGTH_TAKE,EL_TAKE]>>
      Cases_on`LENGTH x''`>>
      fsrw_tac[][]>>simp[]>>
      fsrw_tac[][markerTheory.Abbrev_def]>>
      `t1.stack_space+3 = 3+t1.stack_space` by fsrw_tac[][ADD_COMM]>>
      pop_assum SUBST1_TAC>>
      simp[GSYM DROP_DROP]>>
      qpat_x_assum`A=DROP t1.stack_space t1.stack` sym_sub_tac>>
      simp[]>>
      `k + SUC n'' - nn DIV 2 = SUC (k+ SUC n'' - (nn DIV 2+1))` by
        (ntac 30 (pop_assum mp_tac)>>
        rpt (pop_assum kall_tac)>>
        simp[])>>
      simp[]) >>
    strip_tac >>
    imp_res_tac stackPropsTheory.evaluate_add_clock>>
    ntac 4 (pop_assum kall_tac)>>
    rveq>>fsrw_tac[][]>>
    rename1 `evaluate (PopHandler _ _, _) = (_,t2)` >>
    first_x_assum(qspecl_then[`k`,`f`,`f'`,`t2`,`q''`,`r`] mp_tac)>>
    disch_then (drule_at Any)>>
    qpat_x_assum`comp ac x2 _ _ = _` assume_tac>>
    Cases_on`bs'''`>>
    disch_then (drule_at Any)>>
    disch_then (qspec_then`lens` mp_tac)>>
    impl_tac>- (
      fsrw_tac[][convs_def]>>
      simp[CONJ_ASSOC]>>
      REVERSE CONJ_TAC
      >- (
        qpat_x_assum`A<B:num` mp_tac>>
        simp[wordLangTheory.max_var_def])>>
      REVERSE CONJ_TAC
      >- (
        fs [comp_def,get_labels_def,PopHandler_def] \\
        imp_res_tac evaluate_mono \\ fs[Abbr`stack_state`,Abbr`t6`] \\
        metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
      rw[]
      >- (
        imp_res_tac wLive_LENGTH>>
        fs[])
      >- (
        imp_res_tac wLive_LENGTH>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fs[Abbr`stack_state`,Abbr`t6`]>>
        imp_res_tac IS_PREFIX_LENGTH>>
        fs[])
      >> (
        imp_res_tac wLive_LENGTH>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fs[Abbr`stack_state`,Abbr`t6`]>>
        imp_res_tac comp_IMP_isPREFIX>>
        fs[]>>
        metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
    rw[]>>
    qexists_tac`ck+ck'`>>
    fsrw_tac[][Abbr`stack_state`]>>
    first_x_assum(qspec_then`ck'` mp_tac)>>
    simp[Once evaluate_PopHandler_seq,stackSemTheory.evaluate_def,evaluate_PopHandler_clock]>>
    first_x_assum(qspec_then`ck'` mp_tac)>>simp[]>>
    fsrw_tac[][ADD_COMM]>>
    ntac 2 (disch_then kall_tac)>>
    pop_assum mp_tac>>
    simp[set_var_def,dec_clock_def])
  >- (
    (*Exception*)
    IF_CASES_TAC>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    qpat_x_assum`if A then B else C` mp_tac>>
    IF_CASES_TAC>>fs[]
    >-(
      rw[]>>
      qexists_tac`ck`>>
      fsrw_tac[][Abbr`stack_state`]>>
      `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
      rev_full_simp_tac std_ss [] >>
      fsrw_tac[][state_rel_def,compile_result_NOT_2,set_var_def]>>
      imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
      fsrw_tac[][]>>
      conj_tac >-
        (match_mp_tac IS_PREFIX_TRANS >>
         goal_assum drule >>
         first_x_assum MATCH_ACCEPT_TAC) >>
      cruft_tac >>
      dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
      SIMP_TAC std_ss [state_accfupds] >>
      first_x_assum MATCH_ACCEPT_TAC) >>
    fs[push_locals_def]>>strip_tac>>
    strip_tac>>
    `state_rel ac k f f' (set_var handler0 w0 r'') t1 lens ∧ s.handler = r''.handler` by (
      qpat_x_assum`!a b c d e f. P` kall_tac>>
      Q.ISPECL_THEN [`q'`,`word_state`] assume_tac evaluate_stack_swap>>
      rfs[Abbr`word_state`]>>
      Cases_on`n''`>>
      qpat_x_assum`!a b c.P` kall_tac>>
      fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
      rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
      `LENGTH lens = LENGTH s.stack` by
         (fsrw_tac[][stack_rel_def,LET_THM]>>
         imp_res_tac abs_stack_IMP_LENGTH)>>
      qpat_x_assum`LASTN A B = C` mp_tac>>
      qpat_x_assum`stack_rel k r''.handler A B C D E (LASTN _ (f'::lens))` mp_tac>>
      PURE_ONCE_REWRITE_TAC[GSYM ADD1] >>
      fsrw_tac [] [LASTN_CONS_ID]>>
      ntac 2 strip_tac>>
      CONJ_TAC>-
        metis_tac[evaluate_consts]>>
      CONJ_ASM1_TAC>-
        (imp_res_tac stack_rel_cons_LEN_NONE>>
        fsrw_tac[][LENGTH_DROP]>>
        Cases_on`f'`>>fsrw_tac[][]>>
        ntac 2 (pop_assum mp_tac) >>
        rpt(WEAKEN_TAC (K true)) >>
        simp[])>>
      CONJ_TAC>-
        fsrw_tac[][wf_insert,wf_fromAList]>>
      CONJ_TAC >-
        (imp_res_tac stack_rel_cons_locals_size >>
         strip_tac >> fsrw_tac[][miscTheory.the_def])>>
      CONJ_TAC >-
        (Cases_on `r''.stack_max` >>
         fsrw_tac[][miscTheory.the_def] >-
           (ntac 2 (pop_assum mp_tac) >>
            qpat_x_assum `LENGTH t1.stack <= _` mp_tac >>
            rpt(WEAKEN_TAC (K true)) >>
            simp[]) >>
         rveq >> imp_res_tac evaluate_stack_max >>
         rev_full_simp_tac std_ss [state_accfupds] >>
         pop_assum mp_tac >> TOP_CASE_TAC >>
         strip_tac >>
         fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stack_size_eq] >>
         rveq >> fsrw_tac[][IS_SOME_EXISTS,the_eqn] >>
         fsrw_tac[][] >> rveq >>
         cruft_tac >> DECIDE_TAC) >>
      CONJ_TAC >-
        (strip_tac >> res_tac >>
         fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stack_size_eq]) >>
      CONJ_TAC >-
        (strip_tac >> res_tac >>
         fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stack_size_eq]) >>
      CONJ_TAC >-
        (imp_res_tac stack_rel_cons_locals_size >>
         cruft_tac >>
          strip_tac >> res_tac >>
         fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stack_size_eq] >>
         rveq >> res_tac >>
         imp_res_tac evaluate_stack_max >>
         rev_full_simp_tac std_ss [state_accfupds] >>
         pop_assum mp_tac >> TOP_CASE_TAC >>
         strip_tac >>
         fsrw_tac[][IS_SOME_OPTION_MAP2_EQ,IS_SOME_MAP,stack_size_eq] >>
         rveq >> fsrw_tac[][IS_SOME_EXISTS,the_eqn] >>
         rev_full_simp_tac std_ss [] >>
         rveq >>
         fsrw_tac[][] >>
         `f' <> 0` by(spose_not_then strip_assume_tac >> fsrw_tac[][]) >>
         qpat_x_assum `if f' = 0 then f = 0 else f = f' + 1` mp_tac >>
         IF_CASES_TAC >- metis_tac[] >>
         disch_then SUBST_ALL_TAC >>
         rveq >>
         qpat_x_assum `f' + 1 + _  = LENGTH t1.stack - t1.stack_space` (assume_tac o GSYM) >>
         fsrw_tac[][]) >>
      CONJ_TAC>-
        (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
        metis_tac[stack_rel_DROP_NONE])>>
      rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
      rpt(PRED_ASSUM (exists (curry op = "the") o map (fst o dest_const)
                      o find_terms is_const)
                     kall_tac) >>
      ntac 2 strip_tac>>
      fsrw_tac[][lookup_insert,convs_def]>>
      IF_CASES_TAC>-
        simp[]>>
      strip_tac>>
      rename1`EVEN nn`>>
      `nn ∈ domain (fromAList lss)` by metis_tac[domain_lookup]>>
      `nn ∈ domain x1 ∧ nn ∈ domain s.locals` by
        (fsrw_tac[][cut_env_def]>>
        `nn ∈ domain x'` by rfs[]>>
        rveq>>
        fsrw_tac[][domain_inter])>>
      res_tac>>simp[]>>
      fsrw_tac[][domain_lookup]>>
      last_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
      simp[LLOOKUP_THM]>>
      strip_tac>>
      fsrw_tac[][stack_rel_def]>>
      qpat_x_assum`abs_stack _ _ _ _ =SOME _` mp_tac>>
      qpat_abbrev_tac`L = DROP A B`>>
      Cases_on`L`>>simp[abs_stack_def]>>
      cruft_tac>>
      rpt (TOP_CASE_TAC >>simp[])>>
      strip_tac>>
      qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      strip_tac>>
      fsrw_tac[][lookup_fromAList]>>
      `MEM (nn,v) lss` by metis_tac[ALOOKUP_MEM]>>
      `MEM (nn DIV 2,v) (MAP_FST adjust_names lss)` by
        (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
        metis_tac[])>>
      simp[LLOOKUP_THM]>>
      imp_res_tac filter_bitmap_MEM>>
      ntac 2 (pop_assum kall_tac)>>
      pop_assum (qspec_then`(nn DIV 2 ,v)` mp_tac)>>
      impl_tac>-
        (fs[MEM_MAP,MAP_FST_def]>>
        qexists_tac`y`>>
        simp[mem_list_rearrange,MEM_QSORT]>>
        `ALL_DISTINCT (MAP FST lss)` by
          (qpat_x_assum`A=MAP FST lss` sym_sub_tac>>
          rpt (pop_assum kall_tac)>>
          simp[MAP_FST_def,list_rearrange_I]>>
          match_mp_tac ALL_DISTINCT_MAP_INJ>>
          Q.ISPEC_THEN `x'` assume_tac ALL_DISTINCT_MAP_FST_toAList>>
          rw[]
          >-
            (fs[MEM_QSORT,EL_ALL_DISTINCT_EL_EQ,MEM_EL,EL_MAP]>>
            metis_tac[])
          >>
          metis_tac[QSORT_PERM,ALL_DISTINCT_PERM,ALL_DISTINCT_MAP])>>
        metis_tac[ALL_DISTINCT_MEM_toAList_fromAList])>>
      strip_tac>>
      imp_res_tac MEM_index_list_EL>>
      pop_assum mp_tac>>
      simp[LENGTH_TAKE,EL_TAKE]>>
      Cases_on`LENGTH x''`>>fs[]>>
      simp[]>>
      qpat_x_assum`COND (_ = []) _ _`mp_tac >>
      rename1`ls = []` >> Cases_on`ls` \\ fs[] >>
      `k + (SUC n'') - nn DIV 2 = SUC (k + SUC n'' - (nn DIV 2 + 1))` by DECIDE_TAC>>
      simp[EL_TAKE]
      )>>
    imp_res_tac stackPropsTheory.evaluate_add_clock>>
    ntac 4 (pop_assum kall_tac)>>
    rveq>>fsrw_tac[][]>>
    first_x_assum(qspecl_then[`k`,`f`,`f'`,`t1`] mp_tac)>>
    Cases_on`bs'''`>>fs[]>>
    qpat_x_assum`comp ac handler1 _ _ = _` assume_tac>>
    disch_then (drule_at Any)>>
    disch_then (drule_at Any)>>
    impl_tac>- (
      fsrw_tac[][convs_def]>>
      simp[CONJ_ASSOC]>>
      REVERSE CONJ_TAC
      >- (
        qpat_x_assum`A<B:num` mp_tac>>
        simp[wordLangTheory.max_var_def])>>
      REVERSE CONJ_TAC
      >- (
        fs [comp_def,get_labels_def,PopHandler_def] \\
        imp_res_tac evaluate_mono \\ fs[Abbr`stack_state`,Abbr`t6`] \\
        metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
      rw[]
      >- (
        imp_res_tac wLive_LENGTH>>
        imp_res_tac comp_IMP_LENGTH>>
        fs[]>>
        rfs[])
      >- (
        imp_res_tac wLive_LENGTH>>
        imp_res_tac comp_IMP_LENGTH>>
        fsrw_tac[][]>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fsrw_tac[][Abbr`stack_state`,Abbr`t6`]>>
        imp_res_tac IS_PREFIX_LENGTH>>
        fs[])
      >> (
        imp_res_tac wLive_LENGTH>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fs[Abbr`stack_state`,Abbr`t6`]>>
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>
        fsrw_tac[][]>>
        rfs[]>>
        metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
    rw[]>>
    qexists_tac`ck+ck'`>>
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[][Abbr`stack_state`]>>
    first_x_assum(qspec_then`ck'` mp_tac)>>
    fs[set_var_def])
  >>
    (*Timeout, Halt, and FinalFFI *)
    (strip_tac>>
    qexists_tac`ck`>>
    fs[Abbr`stack_state`]>>
    `t.clock -1 + ck = ck +t.clock -1` by DECIDE_TAC>>
    fs[]>>
    rveq>>simp[]>>
    qpat_x_assum `if A then B else C` mp_tac>>
    IF_CASES_TAC>>fs[]>>rveq>>
    fs[]>>
    strip_tac>>
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[][state_rel_def])
  *)
QED

val _ = get_time timer;
(*still wrong somewhere*)
Theorem comp_correct:
   !(prog:'a wordLang$prog) (s:('a,num # 'c,'ffi) wordSem$state) k f f' res s1 t bs lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     comp ac prog (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ y) =>
            (state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ⇒
                    if i + 1 < k then
                      FLOOKUP t1.regs (i + 1) = SOME (EL i ys)
                    else
                      LLOOKUP (DROP t1.stack_space t1.stack)
                        (LENGTH ys − (i + 1)) = SOME (EL i ys)))
         | SOME (Exception _ y) =>
            (state_rel ac k 0 0 (push_locals cs s1) t1 (LASTN (s.handler+1) lens) 0 /\
            FLOOKUP t1.regs 1 = SOME y)
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock
Proof
  cheat (*
  match_mp_tac (the_ind_thm()) >>
  rpt conj_tac >>
  MAP_FIRST MATCH_ACCEPT_TAC [comp_Skip_correct, comp_Alloc_correct,
    comp_StoreConsts_correct, comp_Move_correct, comp_Inst_correct,
    comp_Assign_correct, comp_Get_correct, comp_Set_correct,
    comp_Store_correct, comp_Tick_correct, comp_MustTerminate_correct,
    comp_Seq_correct, comp_Return_correct, comp_Raise_correct,
    comp_If_correct, comp_LocValue_correct, comp_Install_correct,
    comp_CodeBufferWrite_correct, comp_DataBufferWrite_correct,
    comp_FFI_correct, comp_OpCurrHeap_correct, comp_Call_correct,comp_ShareInst_correct]
  *)
QED

Triviality evaluate_Seq_Skip:
  stackSem$evaluate (Seq Skip p,s) = evaluate (p,s)
Proof
  fs [stackSemTheory.evaluate_def,LET_THM]
QED

val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,call_dest_def,LET_THM]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       list_max_def,evaluate_Seq_Skip,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0] NONE)``,
       EVAL  ``flat_exp_conventions (Call NONE (SOME start) [0] NONE)``,
       wordLangTheory.max_var_def,LET_DEF,MAX_DEF] |> GEN_ALL

Triviality comp_Call:
  ∀start (s:('a,num # 'c,'ffi) wordSem$state) k res s1 t lens.
      evaluate (Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
      res ≠ SOME Error /\ state_rel ac k 0 0 s t lens ⇒
      ∃ck t1:(α,'c,'ffi)stackSem$state res1.
        evaluate (Call NONE (INL start) NONE,t with clock := t.clock + ck) =
        (res1,t1) /\ 1w <> (0w:'a word) /\ 2w <> (0w:'a word) /\
        if OPTION_MAP compile_result res = res1 then
          s1.ffi = t1.ffi /\ s1.clock = t1.clock
        else
          res1 = SOME (Halt (Word 2w)) /\
          t1.ffi.io_events ≼ s1.ffi.io_events /\
          the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
Proof
  rw [] \\ drule comp_Call_lemma \\ fs [get_labels_def]
  \\ disch_then drule
  \\ disch_then(qspecl_then[`LENGTH t.bitmaps`,`Nil`] mp_tac)
  \\ fs [] \\ strip_tac
  \\ `0 < 2 * k` by (fs [state_rel_def] \\ decide_tac) \\ fs []
  \\ fs[evaluate_Seq_Skip]
  \\ asm_exists_tac \\ fs []
  \\ conj_tac THEN1 (fs [state_rel_def,good_dimindex_def,dimword_def])
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs [state_rel_def,push_locals_def,LET_DEF]
QED

Theorem state_rel_with_clock:
   state_rel ac a 0 0 s t lens ⇒ state_rel ac a 0 0 (s with clock := k) (t with clock := k) lens
Proof
  rw[state_rel_def]\\metis_tac[]
QED

val s = ``(s:(α,num # γ,'ffi)wordSem$state)``;
val s' = ``(s:(α,'c,'ffi)stackSem$state)``;
val t = ``(t:(α,'c,'ffi)stackSem$state)``;
val clock_simps =
  LIST_CONJ [
    EVAL``(^s with clock := c).clock``,
    EVAL``(^s with clock := c) with clock := d``,
    EVAL``(^s' with clock := c).clock``,
    EVAL``(^s' with clock := c) with clock := d``];

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = get_time timer;
Theorem state_rel_IMP_semantics:
   state_rel ac k 0 0 ^s ^t lens /\ semantics s start <> Fail ==>
   semantics start t IN extend_with_resource_limit { semantics s start }
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 1 strip_tac >>
  `2 MOD (dimword(:'a)) ≠ 0` by (
    fs[state_rel_def] >>
    `8 < dimword(:'a)` by (assume_tac dimindex_lt_dimword >> simp[]) >>
    simp[] ) >>
  simp[wordSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[] >>
    simp[stackSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      fs[] >> rveq >> fs[] >>
      qhdtm_x_assum`wordSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k''`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      drule0 comp_Call >> fs[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- ( strip_tac >> fs[] ) >>
      drule0(GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k''`strip_assume_tac) >> fs[] >>
      disch_then drule0 >> simp[] >>
      Cases_on`q`>>fs[]>>
      strip_tac >>
      qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >> fs[] >>
      drule0 (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >>
      simp[] >> strip_tac >> rveq >> fs[] >>
      every_case_tac >> fs[] >> rveq >> fs[]
      ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[extend_with_resource_limit_def] >> fs[] >>
      drule0 comp_Call >>
      `r <> SOME Error` by(CCONTR_TAC >> fs[]) >>
      simp[] >> drule0 (GEN_ALL state_rel_with_clock) >> simp[] >>
      disch_then(qspec_then`k'`mp_tac)>>simp[]>>strip_tac>>
      disch_then drule >> strip_tac >>
      drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
      disch_then(qspec_then `k''` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
      qpat_x_assum `evaluate _ = (SOME r', _)` assume_tac >>
      drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
      disch_then(qspec_then `ck + k'` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      ntac 2 strip_tac >> fs[] >> rveq >> fs[] >>
      Cases_on `r` >> fs[] >> Cases_on `x` >> fs[] >>
      Cases_on `r'` >> fs[] >> rveq >> fs[stackSemTheory.state_component_equality] >>
      every_case_tac >> fs[]) >>
    rw[] >> fs[] >>
    drule0 comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      rw[] >> strip_tac >> fs[] ) >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule0 >>
    simp[] >> strip_tac >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >> simp[] >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >> simp[] >>
    every_case_tac >> fs[] >> rw[] >> rfs[]) >>
  rw[] >>
  simp[stackSemTheory.semantics_def] >>
  IF_CASES_TAC >- (
    fs[] >> rveq >> fs[] >>
    last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule0 comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- ( strip_tac >> fs[] ) >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule0 >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`FST p ≠ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule0 (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> fs[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    simp[] >> rw[] >> fs[] >>
    every_case_tac >> fs[] >> rw[] >> fs[]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[extend_with_resource_limit_def] >> fs[] >>
    qpat_x_assum`∀x y. _`(qspec_then`k'`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule0 comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      strip_tac >> fs[] >>
      last_x_assum(qspec_then`k'`mp_tac) >>
      simp[] ) >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule0 >>
    simp[] >> strip_tac >>
    `t'.ffi.io_events ≼ t1.ffi.io_events` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
      fs[Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    fs[] >>
    first_assum(qspec_then`k'`mp_tac) >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][] >>
    qhdtm_x_assum`stackSem$evaluate`mp_tac >>
    drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
    simp[]>>
    disch_then(qspec_then`ck`mp_tac)>>
    last_x_assum(qspec_then`k'`mp_tac) >>
    every_case_tac >> fs[] >> rfs[]>>rw[]>>fs[] >>
    qpat_abbrev_tac`ll = IMAGE _ _` >>
    `lprefix_chain ll` by (
      unabbrev_all_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      simp[LESS_EQ_EXISTS] >>
      metis_tac[
        wordPropsTheory.evaluate_add_clock_io_events_mono,
        clock_simps]) >>
    drule0 build_lprefix_lub_thm >>
    simp[lprefix_lub_def] >> strip_tac >>
    match_mp_tac (GEN_ALL LPREFIX_TRANS) >>
    simp[LPREFIX_fromList] >>
    QUANT_TAC[("l2",`fromList x`,[`x`])] >>
    simp[from_toList] >>
    asm_exists_tac >> simp[] >>
    first_x_assum irule >>
    simp[Abbr`ll`] >>
    qexists_tac`k'`>>simp[] ) >>
  rw[extend_with_resource_limit_def] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    simp[LESS_EQ_EXISTS] >>
    metis_tac[
      wordPropsTheory.evaluate_add_clock_io_events_mono,
      stackPropsTheory.evaluate_add_clock_io_events_mono,
      clock_simps]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac >- (
    qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
    Cases_on`p`>>pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule0 comp_Call >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
      strip_tac >> fs[] ) >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule0 >>
    simp[] >> strip_tac >>
    qexists_tac`k'+ck`>>simp[]>>
    pop_assum mp_tac >>
    IF_CASES_TAC >> simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspec_then`ck+k'`mp_tac)>>simp[]>>
    BasicProvers.TOP_CASE_TAC >> simp[]) >>
    (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k':num``}] (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule0 comp_Call >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
    strip_tac >> fs[] ) >>
  drule0(state_rel_with_clock) >>
  simp[] >> strip_tac >>
  disch_then drule0 >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (stackSem$evaluate (exps,ss))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`ss`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`ss`]>>strip_tac>>
  qexists_tac`k'`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 4 (pop_assum mp_tac) >>
    CASE_TAC >> fs[] >> rw[] >>
    first_x_assum(qspec_then`ck+k'`mp_tac)>>simp[]>>
    CASE_TAC>>simp[]) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]
QED

Definition init_state_ok_def:
  init_state_ok ac k ^t coracle <=>
    4n < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    t.use_stack /\ t.use_store /\ t.use_alloc /\ gc_fun_ok t.gc_fun /\
    t.stack_space <= LENGTH t.stack /\
    FLOOKUP t.regs 0 = SOME (Loc 1 0) /\
    LENGTH t.bitmaps + 1 < dimword (:'a) /\
    [4w] ≼ t.bitmaps /\
    LENGTH t.stack < dimword (:'a) /\
    DROP t.stack_space t.stack = [Word 0w] /\
    Handler IN FDOM t.store /\
    LENGTH t.bitmaps + LENGTH t.data_buffer.buffer +
       t.data_buffer.space_left + 1 < dimword (:'a) /\
    t.compile_oracle = (λn.
      let ((bm0,cfg),progs) = coracle n in
      let (progs,fs,bm) = word_to_stack$compile_word_to_stack ac k progs (Nil, bm0) in
        (cfg,progs,append (FST bm))) ∧
    (∀n. let ((bm0,cfg),progs) = coracle n in
        EVERY (post_alloc_conventions k o SND o SND) progs ∧
        EVERY (flat_exp_conventions o SND o SND) progs ∧
        EVERY ((<>) raise_stub_location o FST) progs ∧
        EVERY ((<>) store_consts_stub_location o FST) progs ∧
        (n = 0 ⇒ bm0 = LENGTH t.bitmaps))
End

Definition make_init_def:
  make_init ac k ^t code coracle =
    <| locals  := insert 0 (Loc 1 0) LN
     ; fp_regs := t.fp_regs
     ; store   := t.store \\ Handler
     ; stack   := []
     ; memory  := t.memory
     ; mdomain := t.mdomain
     ; sh_mdomain := t.sh_mdomain
     ; permute := K I
     ; gc_fun  := t.gc_fun
     ; handler := 0
     ; clock   := t.clock
     ; code    := code
     ; data_buffer := t.data_buffer
     ; code_buffer := t.code_buffer
     ; compile := (λ(bm0,cfg) progs.
      let (progs,fs,bm) = word_to_stack$compile_word_to_stack ac k progs (Nil, bm0) in
      OPTION_MAP (λ(bytes,cfg). (bytes,append (FST bm),(SND bm,cfg)))
        (t.compile cfg progs))
     ; compile_oracle := coracle
     ; be      := t.be
     ; ffi     := t.ffi
     ; termdep := 0
     ; stack_limit := LENGTH t.stack
     ; stack_max   := stack_size([]:'a stack_frame list)
      (* Not sure about Nil,0 *)
     ; stack_size  := mapi (λn (arg_count,prog). FST (SND (compile_prog ac prog arg_count k (Nil,0)))) code
     ; locals_size := SOME 0|>
End

Triviality init_state_ok_IMP_state_rel:
   lookup raise_stub_location t.code = SOME (raise_stub k) /\
   lookup store_consts_stub_location t.code = SOME (store_consts_stub k) /\
    (!n word_prog arg_count.
       (lookup n code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       ?bs i bs2 i2 f stack_prog.
         word_to_stack$compile_prog ac word_prog arg_count k (bs,i) = (stack_prog,f,(bs2,i2)) /\
         LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH t.bitmaps /\
         isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) t.bitmaps) /\
         (lookup n t.code = SOME stack_prog)) /\
    domain t.code =
      raise_stub_location INSERT store_consts_stub_location INSERT domain code ∧
    init_state_ok ac k t coracle ==>
    state_rel ac k 0 0 (make_init ac k t code coracle) (t:('a,'c,'ffi)stackSem$state) []
Proof
  fs [state_rel_def,make_init_def,LET_DEF,lookup_def,init_state_ok_def]
   \\ strip_tac
   \\ conj_tac>-
     (rw[] >> res_tac >>
      goal_assum drule >> rw[lookup_mapi,miscTheory.the_def] >>
      qpat_x_assum `compile_prog _ _ _ _ _ = _` mp_tac >>
      rpt(pop_assum kall_tac) >>
      rw[compile_prog_def,ELIM_UNCURRY])
   \\ fs [stack_rel_def,sorted_env_def,abs_stack_def,LET_THM]
   \\ fs [handler_val_def,LASTN_def,stack_rel_aux_def]
   \\ fs [filter_bitmap_def,MAP_FST_def,index_list_def]
   \\ fs[flookup_thm,wf_def] \\ every_case_tac \\ fs []
   \\ fs [lookup_insert,lookup_def] \\ rpt var_eq_tac
   \\ fs [sptreeTheory.wf_def,Once insert_def,lookup_insert]
   \\ fs[stack_size_def,miscTheory.the_def]
   \\ qmatch_asmsub_abbrev_tac `a1 = [a2]`
   \\ `LENGTH a1 = 1` by simp[]
   \\ unabbrev_all_tac
   \\ fs[LENGTH_DROP]
QED

val init_state_ok_semantics =
  state_rel_IMP_semantics |> Q.INST [`s`|->`make_init ac k t code coracle`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

Theorem state_rel_IMP_semantics':
   state_rel ac k 0 0 ^s ^t lens /\ semantics s start <> Fail /\
   word_lang_safe_for_space ^s start ==>
   semantics start t = semantics s start
Proof
  rw [] >>
  `2 MOD (dimword(:'a)) ≠ 0` by (
    fs[state_rel_def] >>
    `8 < dimword(:'a)` by (assume_tac dimindex_lt_dimword >> simp[]) >>
    simp[]) >>
   reverse (Cases_on `semantics s start`) >> fs []
  >- (
    (* the termination case of word semantics *)
    fs [wordSemTheory.semantics_def] >>
    pop_assum mp_tac >>
    IF_CASES_TAC >> fs [] >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    rw [] >>
    rw[stackSemTheory.semantics_def]
   (*  the fail case of stack semantics *)
    >- (
      fs[] >> rveq >> fs[] >>
      qhdtm_x_assum`wordSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k''`mp_tac) >> simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      CCONTR_TAC >>
      drule0 comp_Call >> fs[] >>
      drule0(GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k''`strip_assume_tac) >>
      map_every qexists_tac [`k`, `t with clock := k''`, `lens`] >>
      fs [] >>
      conj_tac >-
        (strip_tac >> fs[]) >>
      Cases_on`q`>>fs[]>>
      CCONTR_TAC >> fs [] >>
      qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >> fs[] >>
      drule0 (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >>
      simp[] >> CCONTR_TAC >> fs [] >> rveq >> fs[] >>
      every_case_tac >> fs[] >> rveq >> fs[])
    >>
    (* the termination/diverging case of stack semantics *)
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac
    (* the termination case of stack semantics *)
    >- (
      rw [] >> fs [] >>
      drule0 comp_Call >>
      `r <> SOME Error` by(CCONTR_TAC >> fs[]) >>
      simp[] >>
      drule0 (GEN_ALL state_rel_with_clock) >> simp[] >>
      disch_then(qspec_then`k'`mp_tac)>>simp[] >>
      strip_tac>>
      disch_then drule >> strip_tac >>
      drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
      disch_then(qspec_then `k''` mp_tac) >>
      impl_tac >-
        (CCONTR_TAC >> fs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
      qpat_x_assum `evaluate _ = (SOME r', _)` assume_tac >>
      drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
      disch_then(qspec_then `ck + k'` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      ntac 2 strip_tac >> fs[] >> rveq >> fs[] >>
      Cases_on `r` >> fs[] >>
      Cases_on `r' = compile_result x`
      >- (
        Cases_on `x` >> fs [] >>
        fs[stackSemTheory.state_component_equality]) >>
      (* when the compile results are not equal *)
      fs [] >>
      Cases_on `x` >> fs [] >>
      rveq >>
      fs [word_lang_safe_for_space_def] >>
      res_tac >> fs [miscTheory.the_def]) >>
    (* the diverging case of stack semantics *)
    rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
    drule0 comp_Call >>
    `r ≠ SOME Error` by (
      last_x_assum(qspec_then`k'`mp_tac) >> simp[] >>
      rw[] >> strip_tac >> fs[]) >>
    simp [] >>  map_every qexists_tac [`k`, `t with clock := k'`, `lens`] >>
    drule0 (GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    simp [] >> CCONTR_TAC >> fs [] >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >> simp[] >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >> simp[] >>
    every_case_tac >> fs[] >> rw[] >> rfs[]) >>
  (* the diverging case of word semantics *)
  fs [wordSemTheory.semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw [] >>
  rw[stackSemTheory.semantics_def]
  (*  the fail case of stack semantics *)
  >- (
    fs[] >> rveq >> fs[] >>
    last_x_assum(qspec_then`k'`mp_tac)>> simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    CCONTR_TAC >>
    drule0 comp_Call >> fs[] >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    map_every qexists_tac [`k`, `t with clock := k'`, `lens`] >>
    fs [] >>
    conj_tac >-
    (strip_tac >> fs[]) >>
    Cases_on`q`>> fs[] >>
    CCONTR_TAC >> fs [] >>
    qmatch_assum_abbrev_tac`FST p ≠ _` >>
    Cases_on`p` >>
    pop_assum (strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule0 (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac) >>
    impl_tac >- (strip_tac >> fs[]) >>
    simp[] >> rw[] >> fs[] >>
    CCONTR_TAC >> fs [] >>
    every_case_tac >> fs[] >> rw[] >> fs[]) >>
  (* the termination/diverging case of stack semantics *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* the termination case of stack semantics *)
  >- (
    rw [] >>  fs[] >>
    qpat_x_assum`∀x y. _`(qspec_then`k'`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule0 comp_Call >> fs [] >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    map_every qexists_tac [`k`, `t with clock := k'`, `lens`] >>
    fs [] >>
    conj_tac >- (
      strip_tac >> fs[] >>
      last_x_assum(qspec_then`k'`mp_tac) >>
      simp[]) >>
     CCONTR_TAC >> fs [] >>
    `t'.ffi.io_events ≼ t1.ffi.io_events` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`](mp_tac o Q.GEN`extra`)
       stackPropsTheory.evaluate_add_clock_io_events_mono >>
      fs[Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    fs[] >>
    first_assum(qspec_then`k'`mp_tac) >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][] >>
    qhdtm_x_assum`stackSem$evaluate`mp_tac >>
    drule0(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
    simp[]>>
    disch_then(qspec_then`ck`mp_tac)>>
    last_x_assum(qspec_then`k'`mp_tac) >>
    every_case_tac >> fs[] >> rfs[]>>rw[]>>fs[] >>
    CCONTR_TAC >> fs [] >> rveq >>
    fs [word_lang_safe_for_space_def] >>
    res_tac >> fs [miscTheory.the_def]) >>
  (* the diverging case of stack semantics *)
  rw [] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    simp[LESS_EQ_EXISTS] >>
    metis_tac[
      wordPropsTheory.evaluate_add_clock_io_events_mono,
      stackPropsTheory.evaluate_add_clock_io_events_mono,
      clock_simps]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac >- (
    qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
    Cases_on`p`>>pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule0 comp_Call >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
      strip_tac >> fs[] ) >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule0 >>
    simp[] >> strip_tac >>
    qexists_tac`k'+ck`>>simp[]>>
    pop_assum mp_tac >>
    IF_CASES_TAC >> simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspec_then`ck+k'`mp_tac)>>simp[]>>
    BasicProvers.TOP_CASE_TAC >> simp[]) >>
    (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k':num``}]
      (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule0 comp_Call >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
    strip_tac >> fs[] ) >>
  drule0(state_rel_with_clock) >>
  simp[] >> strip_tac >>
  disch_then drule0 >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (stackSem$evaluate (exps,ss))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`ss`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`ss`]>>strip_tac>>
  qexists_tac`k'`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 4 (pop_assum mp_tac) >>
    CASE_TAC >> fs[] >> rw[] >>
    first_x_assum(qspec_then`ck+k'`mp_tac)>>simp[]>>
    CASE_TAC>>simp[]) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]
QED

val init_state_ok_semantics' =
  state_rel_IMP_semantics' |> Q.INST [`s`|->`make_init ac k t code coracle`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

Theorem compile_semantics:
    ^t.code = fromAList (SND (SND (SND (compile asm_conf code)))) /\
    k = (asm_conf.reg_count - (5 + LENGTH asm_conf.avoid_regs)) /\
    init_state_ok asm_conf k t coracle /\
    (ALOOKUP code raise_stub_location = NONE) /\
    (ALOOKUP code store_consts_stub_location = NONE) /\
    FST (compile asm_conf code) ≼ t.bitmaps /\
    EVERY (λn,m,prog. flat_exp_conventions prog /\
    post_alloc_conventions (asm_conf.reg_count - (5 + LENGTH asm_conf.avoid_regs)) prog) code /\
    semantics (make_init asm_conf k t (fromAList code) coracle) start <> Fail ==>
    semantics start t IN
    extend_with_resource_limit' (word_lang_safe_for_space
                   (make_init asm_conf k t (fromAList code) coracle) start)
        {semantics (make_init asm_conf k t (fromAList code) coracle) start}
Proof
  Cases_on `(word_lang_safe_for_space
    (make_init asm_conf k t (fromAList code) coracle) start)`
  >- (
   rw [compile_def, extend_with_resource_limit'_def] >>
   match_mp_tac (GEN_ALL init_state_ok_semantics') >>
   fs [compile_word_to_stack_def,lookup_fromAList,LET_THM,domain_fromAList] >>
   rw [] >> fs [] >> TRY (pairarg_tac >> fs []) >>
   imp_res_tac MAP_FST_compile_word_to_stack >> fs[] >>
   fs [EVAL “raise_stub_location = store_consts_stub_location”] >>
   Cases_on `n=raise_stub_location` >> fs [] >>
   Cases_on `n=store_consts_stub_location` >> fs [] >>
   TRY (imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,FORALL_PROD] >>
    metis_tac[]) >>
   match_mp_tac (compile_word_to_stack_IMP_ALOOKUP |> SIMP_RULE std_ss[SUB_LEFT_LESS_EQ])>>
   HINT_EXISTS_TAC>>simp[]>>
   qexists_tac`List [4w]`>>qexists_tac`1`>>simp[]>>
   metis_tac[PAIR])>>
  rw [compile_def, extend_with_resource_limit'_def]
  \\ match_mp_tac (GEN_ALL init_state_ok_semantics)
  \\ fs [compile_word_to_stack_def,lookup_fromAList,LET_THM,domain_fromAList] \\ rw [] \\ fs []
  \\ TRY (pairarg_tac \\ fs [])
  \\ imp_res_tac MAP_FST_compile_word_to_stack \\ fs[]
  \\ fs [EVAL “raise_stub_location = store_consts_stub_location”]
  \\ Cases_on `n=raise_stub_location` \\ fs []
  \\ Cases_on `n=store_consts_stub_location` \\ fs []
  \\ TRY
    (imp_res_tac ALOOKUP_MEM>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  \\ match_mp_tac (compile_word_to_stack_IMP_ALOOKUP |> SIMP_RULE std_ss[SUB_LEFT_LESS_EQ])
  \\ HINT_EXISTS_TAC>>simp[]
  \\ qexists_tac`List [4w]`>>qexists_tac`1`>>simp[]
  \\ metis_tac[PAIR]
QED

Triviality stack_move_no_labs:
  ∀n a b c p.
  extract_labels p = [] ⇒
  extract_labels (stack_move n a b c p) = []
Proof
  Induct>>rw[stack_move_def]>>
  EVAL_TAC>>metis_tac[]
QED

Theorem word_to_stack_lab_pres:
  ∀ac p bs kf.
    extract_labels p = extract_labels (FST (comp ac p bs kf))
Proof
  ho_match_mp_tac comp_ind>>
  rw[comp_def,extract_labels_def,wordConvsTheory.extract_labels_def]>>
  TRY(PairCases_on`kf`)>>TRY(PairCases_on`kf'`)>>
  fs[wReg1_def]
  >-
    (fs[wMove_def]>>qpat_abbrev_tac `ls = MAP f A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,FORALL_PROD,extract_labels_def]>>
    Cases_on`ls`>>rw[]>>EVAL_TAC>>EVERY_CASE_TAC>>EVAL_TAC)
  >-
    (Cases_on`i`>>TRY(Cases_on`m`)>>TRY(Cases_on`a`)>>
    TRY(Cases_on`f`)>>
    TRY(Cases_on`b`>>Cases_on`r`)>>EVAL_TAC>>
    EVERY_CASE_TAC>>EVAL_TAC)
  >- rpt (EVERY_CASE_TAC>>EVAL_TAC)
  >- rpt (EVERY_CASE_TAC>>EVAL_TAC)
  >- (rpt(pairarg_tac>>fs[])>>EVAL_TAC)
  >-(
    Cases_on`ri`>>fs[wReg2_def]>>EVERY_CASE_TAC>>
    fs[wStackLoad_def]>>
    rpt(pairarg_tac>>fs[])>>
    EVAL_TAC)
  >- (EVERY_CASE_TAC>>fs[]>>EVAL_TAC)
  >- (EVAL_TAC>>EVERY_CASE_TAC>>EVAL_TAC)
  >-
    (pairarg_tac>>fs[]>>
    `extract_labels q0 = []` by
      (Cases_on`dest`>>fs[call_dest_def,wReg2_def]>>pop_assum mp_tac>>
      EVERY_CASE_TAC>>fs[]>>
      rw[]>>EVAL_TAC)>>
    Cases_on`ret`>>fs[]
    >-
      (EVAL_TAC>>EVERY_CASE_TAC>>EVAL_TAC)
    >>
      EVERY_CASE_TAC>>fs[wLive_def]>>
      EVERY_CASE_TAC>>fs[]>>
      rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
      Cases_on`dest'`>>EVAL_TAC>>fs[]>>
      match_mp_tac stack_move_no_labs>>
      EVAL_TAC)
  >-
    (fs[wLive_def]>>rpt(pairarg_tac>>fs[])>>
    EVERY_CASE_TAC>>fs[]>>rveq>>fs[]>>EVAL_TAC)
  >~ [`wShareInst`]
  >- (
    gvs[DefnBase.one_line_ify NONE wShareInst_def] >>
    TOP_CASE_TAC >- simp[extract_labels_def] >>
    TOP_CASE_TAC >>
    TOP_CASE_TAC >>
    pairarg_tac >>
    gvs[wRegWrite1_def,wReg1_def,wReg2_def,AllCaseEqs()] >>
    IF_CASES_TAC >>
    simp[wStackLoad_def] >>
    simp[extract_labels_def])
  >> rpt(pairarg_tac \\ fs[wReg2_def])
  \\ every_case_tac \\ rw[] \\ EVAL_TAC
  \\ EVAL_TAC>>EVERY_CASE_TAC>>EVAL_TAC
QED

Theorem word_to_stack_compile_lab_pres:
  EVERY (λn,m,p.
  let labs = extract_labels p in
  EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
  ALL_DISTINCT labs) prog ⇒
  let (bytes,c,f,p) = compile asm_conf prog in
    MAP FST p = (raise_stub_location::store_consts_stub_location::MAP FST prog) ∧
    EVERY (λn,p.
      let labs = extract_labels p in
      EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
      ALL_DISTINCT labs) p
Proof
  fs[compile_def]>>pairarg_tac>>rw[]>>
  pairarg_tac>>fs[]>>rveq>>fs[]>>
  EVAL_TAC>>
  rename1`compile_word_to_stack _ _ _ b= _`>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [`fs`, `progs`,`bitmaps`,`prog`,`b`]>>
  Induct_on`prog`>>
  fs[compile_word_to_stack_def,FORALL_PROD]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]
  >-
    metis_tac[PAIR] >>
  Cases_on`bitmaps'`>>
  res_tac>>fs[]>>
  qpat_x_assum`compile_prog _ _ _ _ _ = _` mp_tac>>
  qpat_x_assum`ALL_DISTINCT _` mp_tac>>
  qpat_x_assum`EVERY _ (extract_labels p_2)` mp_tac>>
  rpt(pop_assum kall_tac)>>
  FULL_SIMP_TAC std_ss [compile_prog_def,LET_THM]>>
  qpat_abbrev_tac`m = if _ then _ else _`>>
  pairarg_tac>>rw[]>>EVAL_TAC>>
  metis_tac[FST,word_to_stack_lab_pres,PAIR]
QED

Theorem compile_word_to_stack_lab_pres:
   ∀p b q r.
   compile_word_to_stack ac k p b = (q,r) ∧
   EVERY (λ(l,m,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0) ∧ (l2 ≠ 1)) (extract_labels e) ∧
     ALL_DISTINCT (extract_labels e)) p
   ⇒
   EVERY (λ(l,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0) ∧ (l2 ≠ 1)) (extract_labels e) ∧
     ALL_DISTINCT (extract_labels e)) q
Proof
  Induct
  \\ simp[word_to_stackTheory.compile_word_to_stack_def]
  \\ simp[FORALL_PROD]
  \\ rw[word_to_stackTheory.compile_word_to_stack_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ simp[]
  \\ first_x_assum drule
  \\ simp[] \\ strip_tac
  \\ fs[Once word_to_stackTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ EVAL_TAC \\ pop_assum mp_tac
  \\ specl_args_of_then``word_to_stack$comp``word_to_stack_lab_pres mp_tac
  \\ ntac 2 strip_tac \\ fs[]
QED

Triviality EVEN_DIV_2_props:
  a MOD 2 = 0 ∧ b MOD 2 = 0 ⇒
  (a ≠ b ⇒ a DIV 2 ≠ b DIV 2) ∧ (a ≠ 0 ⇒ a DIV 2 ≠ 0)
Proof
  strip_tac
  \\ qspec_then `a` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<2n``))
  \\ qpat_x_assum `a = _` (fn th => once_rewrite_tac [th])
  \\ qspec_then `b` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<2n``))
  \\ qpat_x_assum `b = _` (fn th => once_rewrite_tac [th])
  \\ asm_simp_tac std_ss [DIV_MULT] \\ fs []
QED

val wconvs = [post_alloc_conventions_def,wordConvsTheory.full_inst_ok_less_def,call_arg_convention_def,wordLangTheory.every_var_def,wordLangTheory.every_stack_var_def]

Triviality call_dest_stack_asm_name:
  call_dest d a k = (q0,d') ⇒
  stack_asm_name c q0 ∧
  case d' of
    INR r => r ≤ (FST k)+1
  | INL l => T
Proof
  Cases_on`d`>>EVAL_TAC>>rw[]>>
  EVAL_TAC>>
  pairarg_tac>>fs[]>>
  pop_assum mp_tac>>PairCases_on`k`>>
  EVAL_TAC>>rw[]>>
  EVAL_TAC>>rw[]
QED

Triviality wLive_stack_asm_name:
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  wLive q bs kf = (q1,bs') ⇒
  stack_asm_name c q1
Proof
  PairCases_on`kf`>>
  fs[wLive_def]>>
  rw[]>-EVAL_TAC>>
  rpt(pairarg_tac>>fs[])>>
  rveq>>EVAL_TAC>>fs[]
QED

Theorem word_to_stack_stack_asm_name_lem:
  ∀c p bs kf.
  post_alloc_conventions (FST kf) p ∧
  full_inst_ok_less c p ∧
  (c.two_reg_arith ⇒ every_inst two_reg_inst p) ∧
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  4 < (FST kf) ⇒
  stack_asm_name c (FST (comp c p bs kf))
Proof
  ho_match_mp_tac comp_ind>>rw[]>>fs[comp_def,stack_asm_name_def]
  >-
    (PairCases_on`kf`>>fs[wMove_def]>>
    qpat_abbrev_tac`ls = parmove f`>>
    pop_assum kall_tac >> Induct_on`ls`>>EVAL_TAC>>
    fs[FORALL_PROD]>>
    Cases_on`ls`>>EVAL_TAC>>rw[]>>
    fs[]>>
    Cases_on`p_1`>>Cases_on`p_2`>>EVAL_TAC>>fs[]>>every_case_tac>>fs[]>>
    EVAL_TAC>>fs[])
  >-
    (Cases_on`i`>>TRY(Cases_on`m`)>>TRY(Cases_on`a`)>>
    TRY(Cases_on`b`>>Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    PairCases_on`kf`>>
    fs wconvs>>
    fs[inst_ok_less_def,inst_arg_convention_def,every_inst_def,two_reg_inst_def,wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,asmTheory.fp_reg_ok_def] >>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>fs[]>>
    rw[]>>
    TRY(metis_tac[EVEN_DIV_2_props])>>
    (qpat_assum`addr_offset_ok c c'` mp_tac ORELSE
     qpat_assum`byte_offset_ok c c'` mp_tac) >>EVAL_TAC>>fs[])
  >-
    (PairCases_on`kf`>>
    ntac 3 (EVAL_TAC>>rw[])>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (PairCases_on`kf` \\ EVAL_TAC
    \\ rw [] \\ EVAL_TAC
    \\ fs[inst_ok_less_def,inst_arg_convention_def,every_inst_def,
          two_reg_inst_def,wordLangTheory.every_var_inst_def,full_inst_ok_less_def,
          reg_allocTheory.is_phy_var_def,asmTheory.fp_reg_ok_def]
    \\ rw [] \\ EVAL_TAC \\ fs [] \\ gvs []
    \\ CCONTR_TAC \\ gvs [])
  >-
    (fs wconvs>>
    ntac 4 (pop_assum mp_tac)>>
    EVAL_TAC>>rw[])
  >-
    (fs wconvs>>rpt (pairarg_tac>>fs[])>>
    ntac 6 (pop_assum mp_tac)>>
    EVAL_TAC>>rw[])
  >-
    (fs wconvs>>rpt (pairarg_tac>>fs[])>>
    fs[every_inst_def]>>
    ntac 4 (pop_assum mp_tac)>>
    PairCases_on`kf`>>
    Cases_on`ri`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
  >-
    (every_case_tac>>
    PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (every_case_tac>>rpt(pairarg_tac >>fs[])>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[]>>
    fs wconvs>>
    imp_res_tac call_dest_stack_asm_name>>
    imp_res_tac wLive_stack_asm_name>>
    fs[]>>
    TRY(CASE_TAC>>fs[])>>
    TRY(PairCases_on`kf`>>EVAL_TAC>>rw[])>>
    TRY(first_assum match_mp_tac>>fs wconvs>>fs[every_inst_def])>>
    qmatch_goalsub_abbrev_tac`stack_move n w x y z`>>
    `stack_asm_name c z` by (unabbrev_all_tac>>EVAL_TAC)>>
    pop_assum mp_tac>>
    rpt (pop_assum kall_tac)>>
    map_every qid_spec_tac [`z`,`w`,`n`]>>
    Induct>>EVAL_TAC>>fs[])
  >-
    (pairarg_tac>>fs[]>>EVAL_TAC>>
    metis_tac[wLive_stack_asm_name])
  >- (pairarg_tac \\ fs [] \\ EVAL_TAC \\ fs [])
  >-
    (PairCases_on`kf`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
  >~[`wShareInst`]
  >-
    (PairCases_on`kf` >>
    Cases_on `exp_to_addr exp` >> fs[] >- EVAL_TAC >>
    rename1 ‘SOME x’ >> Cases_on ‘x’>>
    Cases_on `op` >>
    simp[wShareInst_def] >>
    fs wconvs >>
    fs[inst_ok_less_def,inst_arg_convention_def,every_inst_def,two_reg_inst_def,wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,asmTheory.fp_reg_ok_def] >>
    ntac 3 (EVAL_TAC >> rw[]) >>
    EVERY_CASE_TAC >>
    fs[wordLangTheory.exp_to_addr_def,asmTheory.offset_ok_def,aligned_def,align_def]
  )
  >> PairCases_on`kf` \\ EVAL_TAC
  \\ rw[] \\ EVAL_TAC \\ fs[]
QED

Theorem call_dest_stack_asm_remove[local]:
  (FST k)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  call_dest d a k = (q0,d') ⇒
  stack_asm_remove c q0 ∧
  case d' of
    INR r => r ≤ (FST k)+1
  | INL l => T
Proof
  Cases_on`d`>>EVAL_TAC>>rw[]>>
  EVAL_TAC>>
  pairarg_tac>>fs[]>>
  pop_assum mp_tac>>PairCases_on`k`>>
  EVAL_TAC>>rw[]>>
  EVAL_TAC>>rw[]
QED

Theorem wLive_stack_asm_remove[local]:
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  wLive q bs kf = (q1,bs') ⇒
  stack_asm_remove c q1
Proof
  PairCases_on`kf`>>
  fs[wLive_def]>>
  rw[]>-EVAL_TAC>>
  rpt(pairarg_tac>>fs[])>>
  rveq>>EVAL_TAC>>fs[]
QED

Theorem word_to_stack_stack_asm_remove_lem:
  ∀(c:'a asm_config) (p:'a wordLang$prog) bs kf.
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ⇒
  stack_asm_remove c (FST (comp c p bs kf))
Proof
  ho_match_mp_tac comp_ind>>rw[]>>fs[comp_def,stack_asm_remove_def]
  >-
    (PairCases_on`kf`>>fs[wMove_def]>>
    qpat_abbrev_tac`ls = parmove f`>>
    pop_assum kall_tac >> Induct_on`ls`>>EVAL_TAC>>
    fs[FORALL_PROD]>>
    Cases_on`ls`>>EVAL_TAC>>rw[]>>
    fs[]>>
    Cases_on`p_1`>>Cases_on`p_2`>>EVAL_TAC>>fs[]>>every_case_tac>>fs[]>>
    EVAL_TAC>>fs[])
  >-
    (Cases_on`i`>>TRY(Cases_on`m`)>>TRY(Cases_on`a`)>>
    TRY(Cases_on`f`)>>
    TRY(Cases_on`b`>>Cases_on`r`)>>
    PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (rpt(pairarg_tac>>fs[])>>
    EVAL_TAC>>fs[])
  >-
    (rpt(pairarg_tac>>fs[])>>
    ntac 4 (pop_assum mp_tac)>>
    PairCases_on`kf`>>
    Cases_on`ri`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
  >-
    (every_case_tac>>
    PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (PairCases_on`kf`>>
    rpt(EVAL_TAC>>rw[]))
  >-
    (every_case_tac>>rpt(pairarg_tac >>fs[])>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[]>>
    imp_res_tac call_dest_stack_asm_remove>>
    imp_res_tac wLive_stack_asm_remove>>
    fs[]>>
    PairCases_on`kf`>>EVAL_TAC>>rw[]>>
    qmatch_goalsub_abbrev_tac`stack_move n w x y z`>>
    `stack_asm_remove c z` by (unabbrev_all_tac>>EVAL_TAC)>>
    pop_assum mp_tac>>
    qpat_assum`A < B` mp_tac>>
    rpt (pop_assum kall_tac)>>
    map_every qid_spec_tac [`z`,`w`,`n`]>>
    Induct>>EVAL_TAC>>fs[])
  >-
    (pairarg_tac>>fs[]>>EVAL_TAC>>
    metis_tac[wLive_stack_asm_remove])
  >- (rpt(pairarg_tac \\ fs[]) \\ EVAL_TAC \\ fs [])
  >-
    (PairCases_on`kf`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
  >~ [`wShareInst`]
  >-
    (PairCases_on`kf` >>
    Cases_on `exp_to_addr exp` >> fs[] >- EVAL_TAC >>
    rename1 ‘SOME x’ >> Cases_on ‘x’>>
    Cases_on `op` >>
    every_case_tac >>
    rpt (EVAL_TAC >> rw[]))
  \\ rpt(pairarg_tac \\ fs[])
  \\ PairCases_on`kf` \\ fs[wReg1_def,wReg2_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ EVAL_TAC \\ fs[]
QED

Theorem word_to_stack_stack_asm_convs:
  EVERY (λ(n,m,p).
    full_inst_ok_less c p ∧
    (c.two_reg_arith ⇒ every_inst two_reg_inst p) ∧
    post_alloc_conventions (c.reg_count - (LENGTH c.avoid_regs +5)) p) progs ∧
    4 < (c.reg_count - (LENGTH c.avoid_regs +5)) ⇒
  EVERY (λ(n,p). stack_asm_name c p ∧ stack_asm_remove c p) (SND(SND(SND(compile c progs))))
Proof
  fs[compile_def]>>pairarg_tac>>rw[]
  >- (EVAL_TAC>>fs[])
  >- (EVAL_TAC>>fs[])
  >- (EVAL_TAC>>fs[])
  >- (EVAL_TAC>>fs[])
  >>
    rename1`compile_word_to_stack _ _ _ f = _`>>
    rpt (pop_assum mp_tac)>>
    map_every qid_spec_tac[`fs`, `progs'`,`f`,`bitmaps`,`progs`]>>
    Induct>>fs[FORALL_PROD,compile_word_to_stack_def]>>
    rpt strip_tac>>
    FULL_SIMP_TAC (srw_ss())[compile_prog_def]>>
    qpat_assum`A=(progs',fs,bitmaps)`mp_tac>>LET_ELIM_TAC>>
    rpt (pairarg_tac>>fs[])>>
    qpat_assum`A=progs'` sym_sub_tac>>simp[]>>CONJ_TAC
    >- (
      rveq>>
      qmatch_asmsub_abbrev_tac`comp _ p_2 ff kff`>>
      Q.ISPECL_THEN [`c`,`p_2`,`ff`,`kff`] assume_tac word_to_stack_stack_asm_name_lem>>
      Q.ISPECL_THEN [`c`,`p_2`,`ff`,`kff`] assume_tac word_to_stack_stack_asm_remove_lem>>
      rfs[Abbr`kff`]>>
      rw[]>>EVAL_TAC>>fs[])
    >>
      metis_tac[PAIR]
QED

val _ = get_time timer;
Theorem stack_move_alloc_arg:
  ∀n st off i p.
    alloc_arg p ⇒
    alloc_arg (stack_move n st off i p)
Proof
  Induct>>rw[stack_move_def,alloc_arg_def]
QED

Theorem word_to_stack_alloc_arg:
  ∀c p n args.
    alloc_arg (FST(word_to_stack$comp c p n args))
Proof
  recInduct comp_ind >>
  fs[comp_def,alloc_arg_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>
  rw[]>>
  fs[alloc_arg_def]
  >-
    (fs[wMove_def]>>qpat_abbrev_tac`ls = MAP f A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,alloc_arg_def]>>
    Cases_on`ls`>>fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    BasicProvers.EVERY_CASE_TAC>>fs [alloc_arg_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def,wRegWrite2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,alloc_arg_def])
  >-
    (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[alloc_arg_def,wStackLoad_def])
  >-
    (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[alloc_arg_def,wStackLoad_def])
  >- (rpt (pairarg_tac>>fs[alloc_arg_def])>>metis_tac[PAIR])
  >- (rpt (pairarg_tac>>fs[alloc_arg_def])>>Cases_on`bs'`>>
  Cases_on`ri`>>fs[wReg1_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,alloc_arg_def])
  >- (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>fs[alloc_arg_def,wStackLoad_def])
  >- (
    Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs [alloc_arg_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,alloc_arg_def]) >>
    PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs [alloc_arg_def]>>
    rpt(pairarg_tac>>fs[StackArgs_def,alloc_arg_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    TRY(Cases_on`bs'`)>>
    TRY(Cases_on`bs''`)>>
    rpt(pairarg_tac>>fs[StackArgs_def,alloc_arg_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs [alloc_arg_def]>>
    match_mp_tac stack_move_alloc_arg>>fs [alloc_arg_def])
  >~[`wShareInst`]
  >- (Cases_on `exp_to_addr exp` >> fs[] >- EVAL_TAC>>
      rename1 ‘SOME xx’ >> Cases_on ‘xx’ >>
      Cases_on `op` >>
      gvs[wShareInst_def,alloc_arg_def] >>
      fs[wReg1_def,wReg2_def,wRegWrite1_def] >>
      every_case_tac >> fs[] >>
      rw[alloc_arg_def,wStackLoad_def])
  >>
    rpt(pairarg_tac>>fs[alloc_arg_def])>>rveq>>fs[alloc_arg_def]
  >> fs[wReg1_def,wReg2_def]
  >> every_case_tac \\ fs[] \\ rw[alloc_arg_def,wStackLoad_def]
QED

Theorem stack_move_reg_bound:
  ∀n st off i p k.
    i < k ∧
    reg_bound p k ⇒
    reg_bound (stack_move n st off i p) k
Proof
  Induct>>rw[stack_move_def,reg_bound_def]
QED

Theorem word_to_stack_reg_bound:
  ∀c p n args.
    post_alloc_conventions (FST args) p ∧
    4 ≤ FST args ⇒
    reg_bound (FST(word_to_stack$comp c p n args)) (FST args+2)
Proof
  recInduct comp_ind >>fs[comp_def,reg_bound_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>rw[]>>
  fs[reg_bound_def,convs_def]
  >- (
    fs[wMove_def]>>
    qpat_abbrev_tac`ls = parmove A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,reg_bound_def]>>
    Cases_on`ls`>>
    fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    Cases_on`p_1`>>Cases_on`p_2`>>fs[format_var_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs [reg_bound_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def,wRegWrite2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,reg_bound_def]>>fs [reg_bound_def,convs_def,inst_arg_convention_def])
  >-
    (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[reg_bound_def,wStackLoad_def])
  >-
    (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[reg_bound_def,wStackLoad_def])
  >- (rpt (pairarg_tac>>fs [reg_bound_def])>>metis_tac[PAIR])
  >- (rpt (pairarg_tac>>fs [reg_bound_def])>>
  Cases_on`bs'`>>Cases_on`ri`>>fs[wReg1_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,reg_bound_def])
  >-
    (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[reg_bound_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs [reg_bound_def])>>
    fs[wStackLoad_def,reg_bound_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs [reg_bound_def])>>
    Cases_on`handler`>>TRY(PairCases_on`x`)>>TRY(PairCases_on`x'`)>>
    fs [reg_bound_def]>>
    rpt(pairarg_tac>>fs[StackArgs_def,reg_bound_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    TRY(Cases_on`bs'`)>>
    TRY(Cases_on`bs''`)>>
    rpt(pairarg_tac>>fs[StackArgs_def,reg_bound_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs [reg_bound_def]>>
    match_mp_tac stack_move_reg_bound>>fs [reg_bound_def]))
  >- (rpt(pairarg_tac>>fs[reg_bound_def])>>rveq>>fs[reg_bound_def])
  >~ [`wShareInst`]
  >- (Cases_on `exp_to_addr exp` >> fs[] >- EVAL_TAC >>
    rename1 ‘SOME xx’ >> Cases_on ‘xx’>>
    Cases_on `op` >>
    rpt(pairarg_tac>>fs[reg_bound_def])>>rveq>>fs[reg_bound_def] >>
    fs[wReg1_def,wReg2_def,wRegWrite1_def] >>
    every_case_tac >>
    rpt (EVAL_TAC >> rw[]))
  \\ rpt(pairarg_tac>>fs[reg_bound_def])>>rveq>>fs[reg_bound_def]
  \\ fs[wReg1_def,wReg2_def]
  \\ every_case_tac \\ fs[] \\ rw[] \\ EVAL_TAC \\ fs[]
QED

Theorem stack_move_call_args:
  ∀n st off i p.
    call_args p 1 2 3 4 0 ⇒
    call_args (stack_move n st off i p) 1 2 3 4 0
Proof
  Induct>>rw[stack_move_def,call_args_def]
QED

Theorem word_to_stack_call_args:
  ∀c p n args.
    post_alloc_conventions (FST args) p ⇒
    call_args (FST(word_to_stack$comp c p n args)) 1 2 3 4 0
Proof
  ho_match_mp_tac comp_ind >>
  fs[comp_def,call_args_def,FORALL_PROD,wRegWrite1_def,wLive_def,convs_def]>>rw[]>>
  fs[call_args_def]
  >-
    (fs[wMove_def]>>
    qpat_abbrev_tac`ls = MAP f A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,call_args_def]>>
    Cases_on`ls`>>
    fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    BasicProvers.EVERY_CASE_TAC>>fs[call_args_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def,wRegWrite2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,convs_def]>>fs [call_args_def])
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[call_args_def,wStackLoad_def])
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[call_args_def,wStackLoad_def])
  >- (rpt (pairarg_tac>>fs [call_args_def,convs_def])>>metis_tac[PAIR])
  >- (rpt (pairarg_tac>>fs [call_args_def])>>
    Cases_on`bs'`>>Cases_on`ri`>>fs[wReg1_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,call_args_def])
  >- (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>fs[call_args_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs [call_args_def])>>
    fs[wStackLoad_def,call_args_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs [call_args_def])>>
    Cases_on`handler`>>TRY(PairCases_on`x`)>>TRY(PairCases_on`x'`)>>
    fs [call_args_def]>>
    rpt(pairarg_tac>>fs[StackArgs_def,call_args_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    TRY(Cases_on`bs'`)>>
    TRY(Cases_on`bs''`)>>
    rpt(pairarg_tac>>fs[StackArgs_def,call_args_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs [call_args_def]>>
    match_mp_tac stack_move_call_args>>fs [call_args_def]))
  >- (rpt(pairarg_tac>>fs[call_args_def])>>rveq>>fs[call_args_def])
  >~ [`wShareInst`]
  >- (
    Cases_on `exp_to_addr exp` >> fs[] >- EVAL_TAC>>
    rename1 ‘SOME xx’ >> Cases_on ‘xx’>>
    Cases_on `op` >>
    rpt(pairarg_tac>>fs[call_args_def])>>rveq>>fs[call_args_def] >>
    fs[wReg1_def,wReg2_def,wRegWrite1_def] >>
    every_case_tac >>
    rpt (EVAL_TAC >> rw[]))
  \\ rpt(pairarg_tac>>fs[call_args_def])>>rveq>>fs[call_args_def]
  \\ fs[wReg1_def,wReg2_def]
  \\ every_case_tac \\ fs[] \\ rw[] \\ EVAL_TAC \\ fs[]
QED

val reg_bound_ind = stackPropsTheory.reg_bound_ind
val reg_bound_def = stackPropsTheory.reg_bound_def
val reg_bound_inst_def = stackPropsTheory.reg_bound_inst_def

Theorem reg_bound_mono:
  ∀p k k'.
    reg_bound p k ∧
    k ≤ k' ⇒
    reg_bound p k'
Proof
  ho_match_mp_tac reg_bound_ind>>rw[reg_bound_def]>>
  rpt(TOP_CASE_TAC>>fs[])>>
  Cases_on`i`>>
  TRY(Cases_on`a`)>>
  TRY(Cases_on`m`)>>
  TRY(Cases_on`f`)>>
  fs[reg_bound_inst_def]>>
  rpt(TOP_CASE_TAC>>fs[])
QED

(* Gluing all the conventions together *)
Theorem word_to_stack_stack_convs:
  word_to_stack$compile ac p = (bytes,c',f', p') ∧
  EVERY (post_alloc_conventions k) (MAP (SND o SND) p) ∧
  k = (ac.reg_count- (5 +LENGTH ac.avoid_regs)) ∧
  4 ≤ k
  ⇒
  EVERY alloc_arg (MAP SND p') ∧
  EVERY (λp. reg_bound p (k+2)) (MAP SND p') ∧
  EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p')
Proof
  fs[EVERY_MEM,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM]>>
  ntac 3 strip_tac>>
  fs[compile_def]>>
  pairarg_tac>>fs[]>>rveq>>fs[]
  >- (rw[]>> EVAL_TAC>>fs[])
  >- (rw[]>> EVAL_TAC>>fs[]) >>
  qabbrev_tac`k=ac.reg_count-(LENGTH ac.avoid_regs+5)`>>
  `ac.reg_count-(LENGTH ac.avoid_regs+3) = k+2` by fs[Abbr`k`]>>
  pop_assum SUBST_ALL_TAC>>
  pop_assum kall_tac>>
  rpt (pop_assum mp_tac)>>
  rename1`compile_word_to_stack ac k p bm = _`>>
  map_every qid_spec_tac [`bm`,`p''`,`progs`, `fs`, `bitmaps`,`p`]>>
  Induct>>fs[compile_word_to_stack_def,FORALL_PROD]>>
  ntac 13 strip_tac>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]
  >- (
    qpat_x_assum`_ = (prog,f, bitmaps')` mp_tac>>
    SIMP_TAC (std_ss++LET_ss) [Once compile_prog_def]>>
    qpat_abbrev_tac`mm = if _ then _ else _`>>
    pop_assum kall_tac>>
    pairarg_tac >> fs[]>>
    strip_tac>> strip_tac>>
    rveq>>fs[]>>
    EVAL_TAC>>
    first_x_assum(qspec_then`p_2` assume_tac)>>
    rw[]
    >-
      metis_tac[word_to_stack_alloc_arg,FST]
    >>
      qmatch_asmsub_abbrev_tac`word_to_stack$comp _ _ _ xxx `>>
      `k = FST xxx` by fs[Abbr`xxx`]>>
      pop_assum SUBST_ALL_TAC>>
      imp_res_tac word_to_stack_reg_bound >>
      imp_res_tac word_to_stack_call_args >>
      metis_tac[FST,PAIR])
  >>
  fs[AND_IMP_INTRO]>>
  first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem compile_word_to_stack_convs:
  ∀p bm q bm'.
   compile_word_to_stack c k p bm = (q,bm') ∧
   EVERY (λ(n,m,p).
     full_inst_ok_less c p ∧
     (c.two_reg_arith ⇒ every_inst two_reg_inst p) ∧
     post_alloc_conventions k p) p ∧ 4 < k ∧ k + 1 < c.reg_count - LENGTH c.avoid_regs
   ⇒
   EVERY (λ(x,y).
     stack_asm_name c y ∧
     stack_asm_remove c y ∧
     alloc_arg y ∧
     reg_bound y (k+2) ∧
     call_args y 1 2 3 4 0) q
Proof
  Induct>>fs[FORALL_PROD,compile_word_to_stack_def]>>
  rpt strip_tac>>
  FULL_SIMP_TAC (srw_ss())[compile_prog_def]>>
  rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ qmatch_asmsub_abbrev_tac`comp c p_2 bm (k,f)`
  \\ Q.ISPECL_THEN[`c`,`p_2`,`bm`,`(k,f)`]mp_tac
        word_to_stack_stack_asm_name_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ Q.ISPECL_THEN[`c`,`p_2`,`bm`,`(k,f)`]mp_tac
        word_to_stack_stack_asm_remove_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ simp_tac(srw_ss())[]
  \\ simp_tac(srw_ss())[GSYM CONJ_ASSOC]
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_alloc_arg,FST])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_reg_bound,FST,LESS_OR_EQ])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_call_args,FST])
  \\ metis_tac[PAIR]
QED

(* this is the only property needed of the wRegs  *)
val get_code_labels_wReg = Q.prove(`
  (∀n. get_code_labels (f n) = {}) ⇒
  get_code_labels (wRegWrite1 f n kf) = {} ∧
  get_code_labels (wRegWrite2 f n kf) = {}
  `,
  PairCases_on`kf`>>rw[wRegWrite1_def,wRegWrite2_def]) |> SIMP_RULE std_ss [IMP_CONJ_THM];

Triviality get_code_handler_labels_wStackLoad:
  ∀ls.
  get_code_labels (wStackLoad ls x) = get_code_labels x ∧
  stack_get_handler_labels n (wStackLoad ls x) = stack_get_handler_labels n x
Proof
  Induct>>fs[wStackLoad_def,FORALL_PROD]
QED

Triviality wLive_code_labels:
  wLive q bs kf = (q',bs') ⇒
  get_code_labels q' = {}
Proof
  PairCases_on`kf`>>rw[wLive_def]>>fs[]>>
  pairarg_tac>>fs[]>>rw[]
QED

Triviality stack_move_code_labels:
  ∀a b c d e.
  get_code_labels (stack_move a b c d e) = get_code_labels e
Proof
  Induct>>rw[stack_move_def]
QED

Theorem word_to_stack_comp_code_labels:
  ∀c prog bs kf n.
    good_handlers n prog ⇒
    get_code_labels (FST (comp c prog bs kf)) ⊆
    (raise_stub_location,0n) INSERT
      (store_consts_stub_location,0n) INSERT
        ((IMAGE (λn.(n,0)) (get_code_labels prog)) ∪
         stack_get_handler_labels n (FST (comp c prog bs kf)))
Proof
  ho_match_mp_tac word_to_stackTheory.comp_ind>>
  rw[word_to_stackTheory.comp_def]>>
  TRY(PairCases_on`kf`)>>
  fs[get_code_labels_def]>>
  rpt (fs[]>>pairarg_tac>>fs[])>>
  fs[get_code_handler_labels_wStackLoad]>>
  rw[SeqStackFree_def]
  >-
    (* move *)
    (simp[wMove_def]>>
    rename1`wMoveAux ls _`>>
    Induct_on`ls`>>fs[wMoveAux_def]>>
    Cases_on`ls`>>simp[wMoveAux_def,wMoveSingle_def,FORALL_PROD]>>
    rw[]>>every_case_tac>>simp[])
  >-
    (map_every (fn q=> TRY(Cases_on q)) [`i`,`a`,`b`,`r`,`f`,`m`]>>
    fs[wInst_def]>>
    rpt (pairarg_tac>>fs[])>>
    fs[get_code_handler_labels_wStackLoad]>>
    rpt(dep_rewrite.DEP_REWRITE_TAC [get_code_labels_wReg]>>rw[]))
  >>
    rpt(first_x_assum drule)>>rw[]>>
    TRY(fs[SUBSET_DEF]>>metis_tac[])
  >- (rw [wRegWrite1_def])
  >- (
    every_case_tac>>gvs[]>>
    rpt (pairarg_tac>>fs[])>>
    fs[get_code_handler_labels_wStackLoad]>>
    fs[SUBSET_DEF]>>metis_tac[])
  >-
    (TOP_CASE_TAC>>fs[]>>pairarg_tac>>fs[get_code_handler_labels_wStackLoad])
  >-
    rpt(dep_rewrite.DEP_REWRITE_TAC [get_code_labels_wReg]>>rw[])
  >~[`wShareInst`]
  >- (
    Cases_on `exp_to_addr exp` >> fs[]>>
    rename1 ‘SOME xx’>> Cases_on ‘xx’>>
    Cases_on `op` >>
    fs[wShareInst_def] >>
    rpt (pairarg_tac>>fs[])>>
    fs[get_code_handler_labels_wStackLoad] >>
    rw[wRegWrite1_def]
  )
  >> TRY (
    TOP_CASE_TAC>>fs[]>>
    every_case_tac>>fs[call_dest_def]>>
    every_case_tac>>fs[]>>rw[]>>
    rpt(pairarg_tac>>fs[])>>rw[]>>
    fs[get_code_handler_labels_wStackLoad]>>
    fs[StackArgs_def,stack_move_code_labels,PushHandler_def,StackHandlerArgs_def,PopHandler_def]>>
    TRY(drule wLive_code_labels>>fs[])>>
    fs[SUBSET_DEF]>>metis_tac[])
  >-
    (drule wLive_code_labels>>fs[])
  >>
    rw[wRegWrite1_def]
QED;

Theorem compile_word_to_stack_code_labels:
  ∀ac k p bs p' bs'.
  EVERY (λ(n,m,pp). good_handlers n pp) p ∧
  compile_word_to_stack ac k p bs = (p',bs') ⇒
  (* every label in the compiled code *)
  BIGUNION (IMAGE get_code_labels (set (MAP SND p'))) ⊆
  (raise_stub_location,0n) INSERT
  (store_consts_stub_location,0n) INSERT
  (* either came from wordLang *)
  IMAGE (\n.(n,0n)) (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) UNION
  (* or has been introduced into the handler labels *)
  BIGUNION (set (MAP (λ(n,pp). (stack_get_handler_labels n pp)) p'))
Proof
  ho_match_mp_tac compile_word_to_stack_ind>>
  fs[compile_word_to_stack_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>fs[]
  >- (
    qpat_x_assum `compile_prog _ _ _ _ _ = _` mp_tac>>
    PURE_REWRITE_TAC [compile_prog_def,LET_THM]>>
    rpt(pairarg_tac>>fs[])>>
    rw[]>>simp[]>>
    drule word_to_stack_comp_code_labels>>
    qmatch_asmsub_abbrev_tac`comp ac p bs kf`>>
    disch_then(qspecl_then [`ac`,`bs`,`kf`] assume_tac)>>rfs[]>>
    fs[SUBSET_DEF]>>
    metis_tac[])
  >>
  fs[SUBSET_DEF]>>
  metis_tac[]
QED

Theorem word_to_stack_good_code_labels:
  compile asm_conf progs = (bytes,bs,fs,prog') ∧
  good_code_labels progs elabs ⇒
  stack_good_code_labels prog' elabs
Proof
  fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[good_code_labels_def,stack_good_code_labels_def]>>
  rw[]>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]
  >- simp[raise_stub_def,store_consts_stub_def]
  >- simp[raise_stub_def,store_consts_stub_def]
  >>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  rw[]
  >-
    (match_mp_tac IMAGE_SUBSET_gen>>
    asm_exists_tac>>simp[SUBSET_DEF]>>
    metis_tac[])
  >>
    fs[SUBSET_DEF]
QED

Theorem word_to_stack_good_code_labels_incr:
  raise_stub_location ∈ elabs ∧
  store_consts_stub_location ∈ elabs ∧
  compile_word_to_stack ac k prog bs = (prog',fs', bs') ⇒
  good_code_labels prog elabs ⇒
  stack_good_code_labels prog' elabs
Proof
  fs[good_code_labels_def,stack_good_code_labels_def]>>
  rw[]>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]>>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  rw[]
  >-
    (match_mp_tac IMAGE_SUBSET_gen>>
    asm_exists_tac>>simp[SUBSET_DEF]>>
    metis_tac[])
  >>
    fs[SUBSET_DEF]
QED

Triviality sub_union_lemma:
  x SUBSET y ==> x SUBSET y UNION z
Proof
  fs [SUBSET_DEF]
QED

Theorem word_to_stack_good_handler_labels:
  EVERY (λ(n,m,pp). good_handlers n pp) prog ⇒
  compile asm_conf prog = (bytes,bs,fs,prog') ⇒
  stack_good_handler_labels prog'
Proof
  fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[stack_good_handler_labels_def]>>
  rw[]>>match_mp_tac sub_union_lemma>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]>>
  simp[raise_stub_def,store_consts_stub_def]>>
  drule backendPropsTheory.restrict_nonzero_SUBSET_left>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  REWRITE_TAC[UNION_ASSOC]>>
  strip_tac>>
  drule backendPropsTheory.restrict_nonzero_left_union>>
  qmatch_goalsub_abbrev_tac`_ ⊆ restrict_nonzero xxx ∪ _`>>
  `restrict_nonzero xxx = {}` by
    (simp[backendPropsTheory.restrict_nonzero_def,Abbr`xxx`,EXTENSION,MEM_MAP]>>
    metis_tac[SND])>>
  simp[]
QED

Theorem word_to_stack_good_handler_labels_incr:
  EVERY (λ(n,m,pp). good_handlers n pp) prog ⇒
  compile_word_to_stack ac k prog bs = (prog',fs', bs') ⇒
  stack_good_handler_labels prog'
Proof
  fs[stack_good_handler_labels_def]>>
  rw[]>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]>>match_mp_tac sub_union_lemma>>
  simp[raise_stub_def,store_consts_stub_def]>>
  drule backendPropsTheory.restrict_nonzero_SUBSET_left>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  REWRITE_TAC[UNION_ASSOC]>>
  strip_tac>>
  drule backendPropsTheory.restrict_nonzero_left_union>>
  qmatch_goalsub_abbrev_tac`_ ⊆ restrict_nonzero xxx ∪ _`>>
  `restrict_nonzero xxx = {}` by
    (simp[backendPropsTheory.restrict_nonzero_def,Abbr`xxx`,EXTENSION,MEM_MAP]>>
    metis_tac[SND])>>
  simp[]
QED

(* no_install is preserved *)

Theorem wMoveAux_no_install_lem:
  !xs kf. no_install $ wMoveAux xs kf
Proof
  ho_match_mp_tac wMoveAux_ind >>
  rw[wMoveAux_def,no_install_def] >>
  rw[DefnBase.one_line_ify NONE wMoveSingle_def] >>
  rpt (TOP_CASE_TAC >> gvs[no_install_def])
QED

Theorem wStackLoad_no_install_lem:
  !l prog. no_install (wStackLoad l prog) = no_install prog
Proof
  ho_match_mp_tac wStackLoad_ind >>
  rw[wStackLoad_def,no_install_def]
QED

Theorem wRegWrite1_no_install_lem:
  (!reg. no_install $ prog reg) ==>
  no_install (wRegWrite1 prog r kf)
Proof
  PairCases_on `kf` >>
  gvs[wRegWrite1_def] >>
  IF_CASES_TAC >>
  metis_tac[no_install_def]
QED

Theorem wRegWrite2_no_install_lem:
  (!reg. no_install $ prog reg) ==>
  no_install (wRegWrite2 prog r kf)
Proof
  PairCases_on `kf` >>
  gvs[wRegWrite2_def] >>
  IF_CASES_TAC >>
  metis_tac[no_install_def]
QED

Theorem wLive_no_install_lem:
  no_install $ FST (wLive live bs kf)
Proof
  simp[DefnBase.one_line_ify NONE wLive_def] >>
  rpt (TOP_CASE_TAC >> gvs[no_install_def]) >>
  pairarg_tac >>
  gvs[no_install_def]
QED

Theorem stack_move_no_install_lem:
  !n start offset i p.
  no_install (stack_move n start offset i p) = no_install p
Proof
  Induct >>
  gvs[stack_move_def,no_install_def]
QED

Theorem comp_no_install:
  !ac prog bs kf prog' bs'.
    wordConvs$no_install prog /\
    comp ac prog bs kf = (prog',bs') ==>
    stackProps$no_install prog'
Proof
  ho_match_mp_tac comp_ind >>
  simp[no_install_def,comp_def] >>
  rw[]
  >- ((* Move *)
    gvs[no_install_def,DefnBase.one_line_ify NONE wMove_def] >>
    rpt TOP_CASE_TAC >>
    metis_tac[wMoveAux_no_install_lem])
  >- ( (* Inst *)
    gvs[no_install_def,DefnBase.one_line_ify NONE wInst_def] >>
    rpt (TOP_CASE_TAC >>
      gvs[ELIM_UNCURRY,no_install_def,wStackLoad_no_install_lem])
    >~ [`wRegWrite2`]
    >- (irule wRegWrite2_no_install_lem >>
      rw[] >>
      irule wRegWrite1_no_install_lem >>
      rw[no_install_def]
    ) >>
    irule wRegWrite1_no_install_lem >>
    rw[no_install_def]
  )
  >- ( (* Return *)
    pairarg_tac >>
    gvs[wStackLoad_no_install_lem,SeqStackFree_def] >>
    IF_CASES_TAC >>
    rw[no_install_def]
  )
  >- ( (* OpCurrHeap *)
    pairarg_tac >>
    gvs[wStackLoad_no_install_lem] >>
    irule wRegWrite1_no_install_lem >>
    rw[no_install_def]
  )
  >- gvs[wordConvsTheory.no_install_def] (* MustTerminate *)
  >- ( (* Seq *)
    pairarg_tac >>
    gvs[wordConvsTheory.no_install_def,ELIM_UNCURRY,no_install_def] >>
    first_x_assum irule >>
    metis_tac[FST_EQ_EQUIV]
  )
  >- (* If *)
    rpt (
      pairarg_tac >>
      gvs[no_install_def,wStackLoad_no_install_lem,
        wordConvsTheory.no_install_def,AllCaseEqs()])
  >- simp[no_install_def] (* Set BitmapBase *)
  >- gvs[no_install_def,wStackLoad_no_install_lem,
    ELIM_UNCURRY,AllCaseEqs()] (* Set *)
  >- ( (* Get *)
    irule wRegWrite1_no_install_lem >>
    rw[no_install_def]
  )
  >- ( (* Call *)
    pairarg_tac >>
    PairCases_on `kf` >>
    gvs[AllCaseEqs(),no_install_def,
      wordConvsTheory.no_install_def,
      DefnBase.one_line_ify NONE call_dest_def,
      SeqStackFree_def,ELIM_UNCURRY] >>
    rpt TOP_CASE_TAC >>
    gvs[no_install_def,wStackLoad_no_install_lem,
      wLive_no_install_lem,stack_move_no_install_lem,
      StackArgs_def,StackHandlerArgs_def,
      PushHandler_def,PopHandler_def] >>
    metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
  )
  >- ( (* Alloc *)
    gvs[no_install_def,ELIM_UNCURRY] >>
    irule wLive_no_install_lem
  )
  >- gvs[no_install_def,ELIM_UNCURRY] (* StoreConsts *)
  >- ( (* LocValue *)
    irule wRegWrite1_no_install_lem >>
    rw[no_install_def]
  )
  >- fs[wordConvsTheory.no_install_def] (* Install *)
  >- gvs[no_install_def,wStackLoad_no_install_lem,ELIM_UNCURRY] (* CodeBufferWrite *)
  >- gvs[no_install_def,wStackLoad_no_install_lem,ELIM_UNCURRY] (* DataBufferWrite *)
  >- ( (* ShareInst *)
    Cases_on `exp_to_addr exp` >> fs[] >- gvs[no_install_def]>>
    rename1 ‘SOME x’ >> Cases_on ‘x’>>
    gvs[DefnBase.one_line_ify NONE wShareInst_def,no_install_def,ELIM_UNCURRY] >>
    TOP_CASE_TAC >>
    gvs[wStackLoad_no_install_lem,no_install_def] >>
    irule wRegWrite1_no_install_lem >>
    rw[no_install_def]
  )
QED

Theorem compile_word_to_stack_no_install:
  !ac k prog bs prog' fs' bs'.
    EVERY (\(n,m,pp). wordConvs$no_install pp) prog /\
    compile_word_to_stack ac k prog bs = (prog',fs', bs') ⇒
    EVERY (\(a,p). no_install p) prog'
Proof
  ho_match_mp_tac compile_word_to_stack_ind >>
  rw[] >>
  gvs[compile_word_to_stack_def,ELIM_UNCURRY,compile_prog_def] >>
  conj_tac
  >- (
    simp[no_install_def] >>
    irule comp_no_install >>
    metis_tac[FST_EQ_EQUIV]
  ) >>
  last_x_assum irule >>
  metis_tac[FST_EQ_EQUIV]
QED


(* no_share_mem is preserved *)
Theorem wMoveAux_no_shmemop_lem:
  !xs kf. no_shmemop $ wMoveAux xs kf
Proof
  ho_match_mp_tac wMoveAux_ind >>
  rw[wMoveAux_def,no_shmemop_def] >>
  rw[DefnBase.one_line_ify NONE wMoveSingle_def] >>
  rpt (TOP_CASE_TAC >> gvs[no_shmemop_def])
QED

Theorem wStackLoad_no_shmemop_lem:
  !l prog. no_shmemop (wStackLoad l prog) = no_shmemop prog
Proof
  ho_match_mp_tac wStackLoad_ind >>
  rw[wStackLoad_def,no_shmemop_def]
QED

Theorem wRegWrite1_no_shmemop_lem:
  (!reg. no_shmemop $ prog reg) ==>
  no_shmemop (wRegWrite1 prog r kf)
Proof
  PairCases_on `kf` >>
  gvs[wRegWrite1_def] >>
  IF_CASES_TAC >>
  metis_tac[no_shmemop_def]
QED

Theorem wRegWrite2_no_shmemop_lem:
  (!reg. no_shmemop $ prog reg) ==>
  no_shmemop (wRegWrite2 prog r kf)
Proof
  PairCases_on `kf` >>
  gvs[wRegWrite2_def] >>
  IF_CASES_TAC >>
  metis_tac[no_shmemop_def]
QED

Theorem wLive_no_shmemop_lem:
  no_shmemop $ FST (wLive live bs kf)
Proof
  simp[DefnBase.one_line_ify NONE wLive_def] >>
  rpt (TOP_CASE_TAC >> gvs[no_shmemop_def]) >>
  pairarg_tac >>
  gvs[no_shmemop_def]
QED

Theorem stack_move_no_shmemop_lem:
  !n start offset i p.
  no_shmemop (stack_move n start offset i p) = no_shmemop p
Proof
  Induct >>
  gvs[stack_move_def,no_shmemop_def]
QED

Theorem comp_no_shmemop:
  !ac prog bs kf prog' bs'.
    no_share_inst prog /\
    comp ac prog bs kf = (prog',bs') ==>
    no_shmemop prog'
Proof
  ho_match_mp_tac comp_ind >>
  simp[no_shmemop_def,comp_def] >>
  rw[]
  >- ((* Move *)
    gvs[no_shmemop_def,DefnBase.one_line_ify NONE wMove_def] >>
    rpt TOP_CASE_TAC >>
    metis_tac[wMoveAux_no_shmemop_lem])
  >- ( (* Inst *)
    gvs[no_shmemop_def,DefnBase.one_line_ify NONE wInst_def] >>
    rpt (TOP_CASE_TAC >>
      gvs[ELIM_UNCURRY,no_shmemop_def,wStackLoad_no_shmemop_lem])
    >~ [`wRegWrite2`]
    >- (irule wRegWrite2_no_shmemop_lem >>
      rw[] >>
      irule wRegWrite1_no_shmemop_lem >>
      rw[no_shmemop_def]
    ) >>
    irule wRegWrite1_no_shmemop_lem >>
    rw[no_shmemop_def]
  )
  >- ( (* Return *)
    pairarg_tac >>
    gvs[wStackLoad_no_shmemop_lem,SeqStackFree_def] >>
    IF_CASES_TAC >>
    rw[no_shmemop_def]
  )
  >- ( (* OpCurrHeap *)
    pairarg_tac >>
    gvs[wStackLoad_no_shmemop_lem] >>
    irule wRegWrite1_no_shmemop_lem >>
    rw[no_shmemop_def]
  )
  >- gvs[no_share_inst_def] (* MustTerminate *)
  >- ( (* Seq *)
    pairarg_tac >>
    gvs[no_share_inst_def,ELIM_UNCURRY,no_shmemop_def] >>
    first_x_assum irule >>
    metis_tac[FST_EQ_EQUIV]
  )
  >- (* If *)
    rpt (
      pairarg_tac >>
      gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,
        no_share_inst_def,AllCaseEqs()])
  >- simp[no_shmemop_def] (* Set BitmapBase *)
  >- gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,
    ELIM_UNCURRY,AllCaseEqs()] (* Set *)
  >- ( (* Get *)
    irule wRegWrite1_no_shmemop_lem >>
    rw[no_shmemop_def]
  )
  >- ( (* Call *)
    pairarg_tac >>
    PairCases_on `kf` >>
    gvs[AllCaseEqs(),no_shmemop_def,
      no_share_inst_def,
      DefnBase.one_line_ify NONE call_dest_def,
      SeqStackFree_def,ELIM_UNCURRY] >>
    rpt TOP_CASE_TAC >>
    gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,
      wLive_no_shmemop_lem,stack_move_no_shmemop_lem,
      StackArgs_def,StackHandlerArgs_def,
      PushHandler_def,PopHandler_def] >>
    metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
  )
  >- ( (* Alloc *)
    gvs[no_shmemop_def,ELIM_UNCURRY] >>
    irule wLive_no_shmemop_lem
  )
  >- gvs[no_shmemop_def,ELIM_UNCURRY] (* StoreConsts *)
  >- ( (* LocValue *)
    irule wRegWrite1_no_shmemop_lem >>
    rw[no_shmemop_def]
  )
  >- ( (* Install *)
      pairarg_tac >>
      gvs[] >>
      pairarg_tac >>
      gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,
        no_share_inst_def])
  >- gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,ELIM_UNCURRY] (* CodeBufferWrite *)
  >- gvs[no_shmemop_def,wStackLoad_no_shmemop_lem,ELIM_UNCURRY] (* DataBufferWrite *)
  >- fs[no_share_inst_def] (* ShareInst *)
QED

Theorem compile_word_to_stack_no_share_inst:
  !ac k prog bs prog' fs' bs'.
    EVERY (\(n,m,pp). no_share_inst pp) prog /\
    compile_word_to_stack ac k prog bs = (prog',fs', bs') ⇒
    EVERY (\(a,p). no_shmemop p) prog'
Proof
  ho_match_mp_tac compile_word_to_stack_ind >>
  rw[] >>
  gvs[compile_word_to_stack_def,ELIM_UNCURRY,compile_prog_def] >>
  conj_tac
  >- (
    simp[no_shmemop_def] >>
    irule comp_no_shmemop >>
    metis_tac[FST_EQ_EQUIV]
  ) >>
  last_x_assum irule >>
  metis_tac[FST_EQ_EQUIV]
QED

Theorem compile_no_shmemop:
  compile cf prog = (bs,fs,ns,prog') /\
  EVERY (\(n,m,pp). no_share_inst pp) prog ==>
  EVERY (\(a,p). no_shmemop p) prog'
Proof
  rw[compile_def] >>
  pairarg_tac >>
  gvs[] >>
  drule_all_then (irule_at $ Pos last) compile_word_to_stack_no_share_inst
  >>
  simp[no_shmemop_def,
    raise_stub_def,store_consts_stub_def]
QED

Theorem word_to_stack_compile_no_install:
  ALL_DISTINCT (MAP FST prog) ∧
  no_install_code (fromAList prog) ∧
  word_to_stack$compile ac prog = (bm, c, fs, p) ⇒
  EVERY (λ(n,x). no_install x) p
Proof
  strip_tac>>
  fs[compile_def]>>
  pairarg_tac>>fs[]>>
  gvs[]>>
  conj_tac >- EVAL_TAC>>
  conj_tac >- EVAL_TAC>>
  irule compile_word_to_stack_no_install>>
  first_assum $ irule_at Any>>
  fs[wordPropsTheory.no_install_code_def,lookup_fromAList]>>
  fs[EVERY_MEM]>>rpt strip_tac>>
  pairarg_tac>>fs[]>>
  drule_all ALOOKUP_ALL_DISTINCT_MEM>>
  strip_tac>>res_tac
QED

val _ = get_time timer;
val _ = export_theory();
