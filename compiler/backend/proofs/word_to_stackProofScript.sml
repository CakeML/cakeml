(*
  Correctness proof for word_to_stack
*)
open preamble semanticsPropsTheory stackSemTheory wordSemTheory
     word_to_stackTheory wordPropsTheory stackPropsTheory
     parmoveTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_stackProof";
val _ = set_grammar_ancestry [
  "semanticsProps", (* for extend_with_resource_limit *)
  "stackProps", (* for extract_labels *)
  "wordProps",
  "labProps", (* for good_dimindex *)
  "stackSem", "wordSem", "word_to_stack"
]

val _ = Parse.hide "B"

(* TODO: many things in this file need moving *)

val index_list_def = Define `
  (index_list [] n = []) /\
  (index_list (x::xs) n = (n + LENGTH xs,x) :: index_list xs n)`

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

Theorem index_list_eq_ZIP:
   index_list xs k = ZIP(REVERSE(MAP($+ k)(COUNT_LIST (LENGTH xs))),xs)
Proof
  metis_tac[MAP_FST_index_list,MAP_SND_index_list,ZIP_MAP_FST_SND_EQ]
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

Theorem get_var_set_var[simp]:
    stackSem$get_var k (set_var k v st) = SOME v
Proof
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def]>>
  fs[FLOOKUP_UPDATE]
QED

val MEM_TAKE = Q.prove(
  `!xs n x. MEM x (TAKE n xs) ==> MEM x xs`,
  Induct \\ fs [TAKE_def] \\ rw [] \\ res_tac \\ fs []);

val MEM_LASTN_ALT = Q.prove(
  `!xs n x. MEM x (LASTN n xs) ==> MEM x xs`,
  fs [LASTN_def] \\ rw [] \\ imp_res_tac MEM_TAKE \\ fs []);

Theorem clock_add_0[simp]:
   ((t with clock := t.clock + 0) = t:('a,'c,'ffi) stackSem$state) /\
    ((t with clock := t.clock) = t:('a,'c,'ffi) stackSem$state)
Proof
  fs [stackSemTheory.state_component_equality]
QED

Theorem DROP_DROP_EQ:
   !n m xs. DROP m (DROP n xs) = DROP (m + n) xs
Proof
  Induct \\ fs [] \\ Cases_on `xs` \\ fs []
  \\ rpt strip_tac \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac
QED

val TAKE_TAKE_MIN = Q.prove(
    `!xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs`,
    Induct \\ Cases_on `m` \\ Cases_on `n` \\ fs [MIN_DEF]
    \\ rw [] \\ fs [] \\ Cases_on`n` \\ fs[]);

val TAKE_DROP_EQ = Q.prove(
  `!xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)`,
  Induct \\ fs [] \\ rw [] \\ fs [] \\ Cases_on`n` \\ fs[]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac);

val DROP_TAKE_NIL = Q.prove(
  `DROP n (TAKE n xs) = []`,
  rw[DROP_NIL,LENGTH_TAKE_EQ]);

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
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def]
    \\ qmatch_assum_rename_tac `n <= SUC i`
    \\ Cases_on`n`>>fs[LUPDATE_def])
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

val MIN_ADD = Q.prove(
  `MIN m1 m2 + n = MIN (m1 + n) (m2 + n)`,
  fs [MIN_DEF] \\ decide_tac);

val list_LUPDATE_def = Define `
  (list_LUPDATE [] n ys = ys) /\
  (list_LUPDATE (x::xs) n ys = list_LUPDATE xs (n+1) (LUPDATE x n ys))`

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

val LLOOKUP_list_LUPDATE_IGNORE = Q.prove(
  `!xs i n ys.
      i + LENGTH xs <= n ==>
      LLOOKUP (list_LUPDATE xs i ys) n = LLOOKUP ys n`,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `(i+1) + LENGTH xs <= n` by decide_tac \\ res_tac
  \\ `i <> n` by decide_tac \\ fs [LLOOKUP_LUPDATE]);

val DROP_list_LUPDATE = Q.prove(
  `!ys n m xs.
      n <= m ==>
      DROP n (list_LUPDATE ys m xs) =
      list_LUPDATE ys (m - n) (DROP n xs)`,
  Induct
  \\ fs [list_LUPDATE_def,LENGTH_NIL,PULL_FORALL]
  \\ rpt strip_tac \\ `n <= m + 1` by decide_tac
  \\ rw [] \\ `m + 1 - n = m - n + 1 /\ ~(m < n)` by decide_tac
  \\ fs [DROP_LUPDATE]);

val DROP_list_LUPDATE_IGNORE = Q.prove(
  `!xs i ys n.
      LENGTH xs + i <= n ==>
      DROP n (list_LUPDATE xs i ys) = DROP n ys`,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `LENGTH xs + (i+1) <= n /\ i < n` by decide_tac
  \\ fs [DROP_LUPDATE]);

Theorem list_LUPDATE_NIL[simp]:
   !xs i. list_LUPDATE xs i [] = []
Proof
  Induct \\ fs [list_LUPDATE_def,LUPDATE_def]
QED

val LUPDATE_TAKE_LEMMA = Q.prove(
  `!xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)`,
  Induct \\ Cases_on `n` \\ fs [LUPDATE_def]);

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

val DIV_ADD_1 = Q.prove(
  `0 < d ==> (m DIV d + 1 = (m + d) DIV d)`,
  rpt strip_tac
  \\ ASSUME_TAC (ADD_DIV_ADD_DIV |> Q.SPECL [`d`] |> UNDISCH
      |> Q.SPECL [`1`,`m`] |> ONCE_REWRITE_RULE [ADD_COMM]) \\ fs []);

val LENGTH_word_list_lemma = Q.prove(
  `!xs d. 0 < d ==> (LENGTH (word_list xs d) = (LENGTH xs - 1) DIV d + 1)`,
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
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac);

Theorem LENGTH_word_list:
   !xs d. LENGTH (word_list xs d) =
           if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1
Proof
  rw [] THEN1 (once_rewrite_tac [word_list_def] \\ fs [])
  \\ match_mp_tac LENGTH_word_list_lemma \\ decide_tac
QED

(* move to wordProps? *)

val list_rearrange_I = Q.prove(
  `(list_rearrange I = I)`,
  fs [list_rearrange_def,FUN_EQ_THM]
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF,GENLIST_ID]);

(* state relation *)

(*Abstracts a stackLang stack w.r.t. to wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel
  TODO: The length checks may be inconvenient for handler frames
*)
val abs_stack_def = Define`
  (abs_stack (bitmaps:'a word list) [] stack [] =
    if stack = [Word (0w:'a word)] then SOME [] else NONE) ∧
  (abs_stack bitmaps ((StackFrame l NONE)::xs) (w::stack) (len::lens) =
    (*Should cover the stack = [] case automatically*)
    case full_read_bitmap bitmaps w of
    | NONE => NONE
    (*read_bitmap reads a bitmap and returns the liveness bits,
      the words read and the rest of the stack*)
    | SOME bits =>
        if LENGTH bits ≠ len then NONE else
        if LENGTH stack < len then NONE else
          let frame = TAKE len stack in
          let rest = DROP len stack in
            case abs_stack bitmaps xs rest lens of
            | NONE => NONE
            | SOME ys => SOME ((NONE,bits,frame)::ys)) ∧
  (abs_stack bitmaps ((StackFrame l (SOME _))::xs) (w::stack) (len::lens) =
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
                let frame = TAKE len stack in
                let rest = DROP len stack in
                  case abs_stack bitmaps xs rest lens of
                  | NONE => NONE
                  | SOME ys => SOME ((SOME(loc,hv),bits,frame)::ys))
      | _ => NONE)) ∧
  (abs_stack bitmaps _ _ _ = NONE)`

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

val MAP_FST_def = Define `
  MAP_FST f xs = MAP (\(x,y). (f x, y)) xs`

val adjust_names_def = Define `
  adjust_names n = n DIV 2`;

(*handler_val counts the total number of words in the list of frames*)
val handler_val_def = Define`
  (handler_val [] = 1n) ∧
  (handler_val ((NONE,_,frame)::stack) =
    1+LENGTH frame+handler_val stack) ∧
  (handler_val ((SOME _,_,frame)::stack) =
    (*  1 for handler bitmaps pointer
      + 2 more for the pointer and locs
      + 1 for the next bitmap pointer
    *)
    4+LENGTH frame+handler_val stack)`

(*TODO: Maybe switch to this alternative index_list that goes from
stackLang vars to wordLang vars more directly*)
(*
val index_list_def = Define `
  (index_list [] k = []) /\
  (index_list (x::xs) k = (2*(k+LENGTH xs),x) :: index_list xs k)`
*)

val is_handler_frame_def = Define`
  (is_handler_frame (StackFrame l NONE) = F) ∧
  (is_handler_frame _ = T)`

(*Checks for consistency of the values*)
val stack_rel_aux_def = Define`
  (stack_rel_aux k len [] [] ⇔ T) ∧
  (stack_rel_aux k len ((StackFrame l NONE)::xs) ((NONE,bits,frame)::stack) ⇔
    filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
    stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len ((StackFrame l (SOME (h1,l1,l2)))::xs) ((SOME(loc,hv),bits,frame)::stack) ⇔
      (h1 < LENGTH stack ∧
      is_handler_frame (EL (LENGTH stack - (h1+1)) xs) ⇒
      hv = Word (n2w (len - handler_val (LASTN (h1+1) stack)))) ∧
      loc = Loc l1 l2 ∧
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
      stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len _ _ = F)`

val sorted_env_def = Define `
  sorted_env (StackFrame l _) = SORTED (\x y. FST x > FST y) l`

val stack_rel_def = Define `
  stack_rel k s_handler s_stack t_handler t_rest_of_stack t_stack_length t_bitmaps lens <=>
    EVERY sorted_env s_stack /\
    ∃stack.
      abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack ∧
      (s_handler < LENGTH s_stack ∧
      is_handler_frame (EL (LENGTH s_stack - (s_handler+1)) s_stack)
      ⇒
      t_handler = SOME(Word (n2w (t_stack_length - handler_val (LASTN (s_handler+1) stack))))) ∧
      stack_rel_aux k t_stack_length s_stack stack`

(*f is the size of the current frame + 1 most of the time
  (extra word for the bitmap pointer)
  f' is the size of the current frame
  lens tracks the size of each remaining stack frame on the stackLang stack
*)
val state_rel_def = Define `
  state_rel k f f' (s:('a,'a word list # 'c,'ffi) wordSem$state) (t:('a,'c,'ffi) stackSem$state) lens ⇔
    (s.clock = t.clock) /\ (s.gc_fun = t.gc_fun) /\ (s.permute = K I) /\
    (t.ffi = s.ffi) /\ t.use_stack /\ t.use_store /\ t.use_alloc /\
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\ 4 < k /\
    (s.store = t.store \\ Handler) /\ gc_fun_ok t.gc_fun /\ s.termdep = 0 /\
    t.be = s.be /\ t.ffi = s.ffi /\ Handler ∈ FDOM t.store ∧
    t.fp_regs = s.fp_regs ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    s.compile = (λ(bm0,cfg) progs.
      let (progs,bm) = word_to_stack$compile_word_to_stack k progs bm0 in
      OPTION_MAP (λ(bytes,cfg). (bytes,DROP (LENGTH bm0) bm,(bm,cfg)))
        (t.compile cfg progs)) ∧
    t.compile_oracle = (λn.
      let ((bm0,cfg),progs) = s.compile_oracle n in
      let (progs,bm) = word_to_stack$compile_word_to_stack k progs bm0 in
        (cfg,progs,DROP (LENGTH bm0) bm)) ∧
    (∀n. let ((bm0,cfg),progs) = s.compile_oracle n in
        EVERY (post_alloc_conventions k o SND o SND) progs ∧
        EVERY (flat_exp_conventions o SND o SND) progs ∧
        EVERY ((<>) raise_stub_location o FST) progs ∧
        (n = 0 ⇒ bm0 = t.bitmaps)) ∧
    domain t.code = raise_stub_location INSERT domain s.code ∧
    (!n word_prog arg_count.
       (lookup n s.code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       ?bs bs2 stack_prog.
         word_to_stack$compile_prog word_prog arg_count k bs = (stack_prog,bs2) /\
         isPREFIX bs2 t.bitmaps /\
         (lookup n t.code = SOME stack_prog)) /\
    (lookup raise_stub_location t.code = SOME (raise_stub k)) /\
    good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    LENGTH t.bitmaps + LENGTH s.data_buffer.buffer + s.data_buffer.space_left +1 < dimword (:α) /\
    1 ≤ LENGTH t.bitmaps ∧ HD t.bitmaps = 4w ∧
    t.stack_space + f <= LENGTH t.stack /\ LENGTH t.stack < dimword (:'a) /\
    (if f' = 0 then f = 0 else (f = f' + 1)) /\
    wf s.locals /\
    let stack = DROP t.stack_space t.stack in
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
             n DIV 2 < k + f')`

(* correctness proof *)

val evaluate_SeqStackFree = Q.prove(
  `t.use_stack /\ t.stack_space <= LENGTH t.stack ==>
    evaluate (SeqStackFree f p,t) =
    evaluate (Seq (StackFree f) p,t)`,
  fsrw_tac[] [SeqStackFree_def] \\ srw_tac[] [stackSemTheory.evaluate_def]
  THEN1 (`F` by decide_tac) \\ AP_TERM_TAC
  \\ fs [stackSemTheory.state_component_equality]);

val convs_def = LIST_CONJ
  [wordPropsTheory.post_alloc_conventions_def,
   wordPropsTheory.call_arg_convention_def,
   wordPropsTheory.flat_exp_conventions_def,
   wordLangTheory.every_var_def,
   wordLangTheory.every_var_imm_def,
   wordLangTheory.every_stack_var_def,
   wordLangTheory.every_name_def]

val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``

(*
val LENGTH_write_bitmap = Q.prove(
  `state_rel k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap (names:num_set) k f'):'a word list) + f' = f)`,
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac);
*)

val DROP_list_LUPDATE_lemma =
  MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL) |> SIMP_RULE std_ss []

val bits_to_word_bit = Q.prove(
  `!bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)`,
  Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1] \\ rpt strip_tac
  \\ first_x_assum match_mp_tac \\ fs [] \\ decide_tac);

val bits_to_word_miss = Q.prove(
  `!bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)`,
  Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);

val bits_to_word_NOT_0 = Q.prove(
  `!bs. LENGTH bs <= dimindex (:'a) /\ EXISTS I bs ==>
         (bits_to_word bs <> 0w:'a word)`,
  fs [fcpTheory.CART_EQ] \\ rpt strip_tac
  \\ fs [EXISTS_MEM,MEM_EL]
  \\ Q.EXISTS_TAC `n`   \\ fs []
  \\ `n < dimindex (:'a)` by decide_tac \\ fs [word_0]
  \\ fs [bits_to_word_bit]);

val list_LUPDATE_write_bitmap_NOT_NIL = Q.prove(
  `8 <= dimindex (:'a) ==>
    (list_LUPDATE (MAP Word (write_bitmap names k f')) 0 xs <>
     [Word (0w:'a word)])`,
  Cases_on `xs` \\ fs [list_LUPDATE_NIL]
  \\ fs [write_bitmap_def,LET_DEF,Once word_list_def]
  \\ strip_tac \\ `~(dimindex (:'a) <= 1)` by decide_tac \\ fs []
  \\ rw [] \\ rpt disj1_tac
  \\ match_mp_tac bits_to_word_NOT_0 \\ fs [LENGTH_TAKE_EQ]
  \\ fs [MIN_LE,MIN_ADD] \\ decide_tac);

val word_or_eq_0 = Q.prove(
  `((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ metis_tac [])

val shift_shift_lemma = Q.prove(
  `~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + 1 < dimindex (:α)`
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac
  \\ simp [])

val bit_length_bits_to_word = Q.prove(
  `!qs.
      LENGTH qs + 1 < dimindex (:'a) ==>
      bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs + 1`,
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
  \\ fs [ADD1,word_or_eq_0]);

val GENLIST_bits_to_word_alt = Q.prove(
  `LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs`,
  fs [LIST_EQ_REWRITE] \\ rpt strip_tac
  \\ `EL x xs = EL x (xs ++ ys)` by fs [EL_APPEND1]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ match_mp_tac bits_to_word_bit
  \\ fs [] \\ decide_tac);

val GENLIST_bits_to_word = Q.prove(
  `LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'`,
  rpt strip_tac \\ match_mp_tac GENLIST_bits_to_word_alt
  \\ fs [] \\ decide_tac);

val read_bitmap_word_list = Q.prove(
  `8 <= dimindex (:'a) ==>
    read_bitmap
      ((word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++ (xs:'a word list)) =
    SOME qs`,
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
  \\ decide_tac);

val APPEND_LEMMA = Q.prove(
  `n1 + n2 + n3 <= LENGTH xs ==>
    ?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2`,
  rpt strip_tac
  \\ `n1 <= LENGTH xs` by decide_tac
  \\ Q.PAT_X_ASSUM `n1 + n2 + n3 <= LENGTH xs` MP_TAC
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [DROP_LENGTH_APPEND]  \\ fs []
  \\ rename [‘n2 + (n3 + LENGTH xs1) ≤ LENGTH xs1 + LENGTH xs2’]
  \\ `n2 <= LENGTH xs2` by decide_tac
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [] \\ metis_tac []);

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
   ∀bs bs' i.
   i < dimword (:α) ∧
   IS_SOME (read_bitmap bm) ∧
   insert_bitmap bm (bs:α word list) = (bs',i)
   ⇒ read_bitmap (DROP (i MOD dimword (:α)) bs') = read_bitmap bm
Proof
  Induct >> simp[insert_bitmap_def] \\ rw[] \\ simp[]
  >- (
    fs[IS_PREFIX_APPEND,IS_SOME_EXISTS]
    \\ match_mp_tac read_bitmap_append_extra
    \\ simp[] )
  \\ pairarg_tac >> fsrw_tac[][]
  \\ rveq
  \\ REWRITE_TAC[GSYM ADD1]
  \\ REWRITE_TAC[DROP]
  \\ first_x_assum match_mp_tac
  \\ simp[]
QED

Theorem insert_bitmap_length:
   ∀ls ls' i. insert_bitmap bm ls = (ls',i) ⇒ i ≤ LENGTH ls ∧ LENGTH ls ≤ LENGTH ls'
Proof
  Induct >> simp[insert_bitmap_def]
  \\ rw[] >> simp[]
  \\ pairarg_tac >> fs[]
  \\ rw[] >> simp[]
QED

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

val abs_stack_IMP_LENGTH = Q.prove(
  `∀bs wstack sstack lens stack.
    abs_stack bs wstack sstack lens = SOME stack ⇒ LENGTH stack = LENGTH wstack ∧ LENGTH lens = LENGTH wstack`,
  recInduct (theorem "abs_stack_ind")
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw [])

val SORTED_FST_LESS_IMP = Q.prove(
  `!xs x.
      SORTED (\x y. FST x > FST y:num) (x::xs) ==>
      SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
      (!y. MEM y xs ==> FST x > FST y)`,
  Induct \\ fs [SORTED_DEF]
  \\ ntac 3 strip_tac \\ res_tac \\ rpt strip_tac
  \\ rw [] \\ fs [] \\ res_tac \\ decide_tac);

val SORTED_IMP_EQ_LISTS = Q.prove(
  `!xs ys.
      SORTED (\x y. FST x > FST y:num) ys /\
      SORTED (\x y. FST x > FST y) xs /\
      (!x. MEM x ys <=> MEM x xs) ==>
      (xs = ys)`,
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
    \\ rpt strip_tac \\ fs [] \\ fs []));

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

val SORTS_QSORT_key_val_compare = Q.prove(
  `SORTS QSORT key_val_compare`,
  match_mp_tac QSORT_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare))

val MEM_QSORT = SORTS_QSORT_key_val_compare
  |> SIMP_RULE std_ss [SORTS_DEF]
  |> SPEC_ALL |> CONJUNCT1
  |> MATCH_MP MEM_PERM |> GSYM |> GEN_ALL

val SORTED_weaken2 = Q.prove(`
  ∀ls. SORTED R ls ∧
  ALL_DISTINCT ls ∧
  (∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ∧ R x y ⇒ R' x y) ⇒
  SORTED R' ls`,
  Induct>>rw[]>>Cases_on`ls`>>fs[SORTED_DEF]>>
  metis_tac[])

val EVEN_GT = Q.prove(`
  ∀a b.
  EVEN a ∧ EVEN b ∧
  a > b ⇒
  a DIV 2 > b DIV 2`,
  fs[EVEN_EXISTS]>>rw[]>>
  fsrw_tac[][MULT_DIV,MULT_COMM]>>
  DECIDE_TAC)

val transitive_GT = Q.prove(`
  transitive ($> : (num->num->bool))`,
  fs[transitive_def]>>DECIDE_TAC)

val env_to_list_K_I_IMP = Q.prove(
  `!env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l`,
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
  \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs [])

val evaluate_wLive = Q.prove(
  `wLive names bs (k,f,f') = (wlive_prog,bs') /\
   (∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
   state_rel k f f' (s:('a,'a word list # 'c,'ffi) wordSem$state) t lens /\ 1 <= f /\
   (cut_env names s.locals = SOME env) /\
   isPREFIX bs' t.bitmaps ==>
   ?t5:('a,'c,'ffi) stackSem$state bs5.
     (evaluate (wlive_prog,t) = (NONE,t5)) /\
     state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 (f'::lens) /\
     state_rel k f f' s t5 lens /\
     !i. i ≠ k ==> get_var i t5 = get_var i t`,
  fsrw_tac[] [wLive_def,LET_THM] \\ rpt strip_tac \\
  `f ≠ 0` by DECIDE_TAC \\ fsrw_tac[][] \\ pop_assum kall_tac
  \\ pairarg_tac \\ fsrw_tac[] [] \\ rpt var_eq_tac
  \\ fsrw_tac[] [stackSemTheory.evaluate_def,stackSemTheory.inst_def,
         stackSemTheory.assign_def,stackSemTheory.word_exp_def,LET_THM]
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
  \\ TRY(rename1`flat_exp_conventions A`>>metis_tac[])
  \\ TRY(rename1`post_alloc_conventions A B`>>metis_tac[])
  \\ fsrw_tac[][wf_def]
  \\ fsrw_tac[] [stack_rel_def,stack_rel_aux_def,abs_stack_def]
  \\ Cases_on `DROP t.stack_space t.stack` \\ fsrw_tac[] []
  THEN1 (fsrw_tac[] [listTheory.DROP_NIL,DECIDE ``m>=n<=>n<=m:num``] \\ `F` by decide_tac)
  \\ fsrw_tac[] [LUPDATE_def,abs_stack_def]
  \\ conj_tac THEN1
   (mp_tac (Q.SPEC `env` env_to_list_K_I_IMP)
    \\ fsrw_tac[] [env_to_list_def,sorted_env_def,LET_DEF] \\ srw_tac[] []
    \\ `s.permute 0 = I` by fsrw_tac[] [FUN_EQ_THM] \\ fsrw_tac[] [])
  \\ fsrw_tac[] [full_read_bitmap_def,GSYM word_add_n2w]
  \\ `i < dimword(:α) ∧ (i+1) MOD dimword(:'a) ≠ 0` by (
    fsrw_tac[][state_rel_def]
    \\ imp_res_tac insert_bitmap_length
    \\ fsrw_tac[][IS_PREFIX_APPEND] >> fsrw_tac[][]
    \\ simp[] )
  \\ drule (GEN_ALL read_bitmap_insert_bitmap)
  \\ simp[IS_SOME_EXISTS,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ disch_then drule
  \\ simp[read_bitmap_write_bitmap]
  \\ strip_tac
  \\ fsrw_tac[][IS_PREFIX_APPEND]
  \\ imp_res_tac read_bitmap_append_extra
  \\ simp[DROP_APPEND]
  \\ fsrw_tac[ARITH_ss][] \\ rveq
  \\ fsrw_tac[ARITH_ss][]
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
    \\ simp[is_handler_frame_def] )
  \\ simp[stack_rel_aux_def]
  \\ `∀x. s.permute x = I` by simp[FUN_EQ_THM]
  \\ simp[list_rearrange_I]
  \\ qmatch_assum_abbrev_tac`DROP nn ll = _`
  \\ qispl_then[`nn`,`ll`]mp_tac LENGTH_DROP
  \\ asm_simp_tac(std_ss)[Abbr`ll`,Abbr`nn`]
  \\ simp[] \\ rpt strip_tac
  \\ match_mp_tac IMP_filter_bitmap_EQ_SOME_NIL
  \\ fsrw_tac[] [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ conj_asm1_tac THEN1 (
      fsrw_tac[] [LENGTH_index_list,LENGTH_TAKE_EQ,MIN_DEF]
      \\ srw_tac[][] >> decide_tac )
  \\ fsrw_tac[] [ZIP_GENLIST] \\ pop_assum kall_tac
  \\ qpat_abbrev_tac`ls = MAP _ (toAList _)`
  \\ `!x. MEM x ls <=>
          ?n. x = f' - 1 - (n DIV 2 - k) /\ n IN domain env` by
   (fsrw_tac[] [MEM_MAP,EXISTS_PROD,MEM_toAList,cut_env_def,Abbr`ls`] \\ srw_tac[][]
    \\ fsrw_tac[] [lookup_inter_alt,domain_lookup,SUBSET_DEF]
  \\ metis_tac []) \\ fsrw_tac[] [] \\ ntac 2 (pop_assum kall_tac)
  \\ fsrw_tac[] [MAP_FST_def,adjust_names_def]
  \\ match_mp_tac SORTED_IMP_EQ_LISTS
  \\ conj_tac
  >- (
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> snd
    |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    REWRITE_TAC[GSYM inv_image_def] >>
    conj_tac >-(
      match_mp_tac transitive_inv_image >>
      ACCEPT_TAC transitive_GT ) >>
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
      `∀p v. lookup p env = SOME v ⇒ lookup p s.locals = SOME v` by
        (fsrw_tac[][cut_env_def]>>qpat_x_assum`A=env` (SUBST_ALL_TAC o SYM)>>
        fsrw_tac[][lookup_inter_EQ])>>
      srw_tac[][]>>fsrw_tac[][]>>res_tac>>res_tac>>
      fsrw_tac[][EVEN_GT])
  \\ conj_tac
  >- (
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> snd
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    REWRITE_TAC[GSYM inv_image_def] >>
    conj_tac >-(
      match_mp_tac transitive_inv_image >>
      ACCEPT_TAC transitive_GT ) >>
    match_mp_tac (MP_CANON sorted_filter) >>
    conj_tac >- metis_tac[transitive_inv_image,transitive_GT] >>
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> fst
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    conj_tac >- metis_tac[transitive_inv_image,transitive_GT] >>
    simp[MAP_GENLIST,combinTheory.o_DEF] >>
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> fst
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    conj_tac >- ACCEPT_TAC transitive_GT>>
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
    fsrw_tac[][SORTED_EL_SUC]>>srw_tac[][]>>`n < m` by DECIDE_TAC>>
    fsrw_tac[][EL_GENLIST]>>DECIDE_TAC)
  \\ qhdtm_x_assum`cut_env`mp_tac
  \\ simp[MEM_MAP,MEM_FILTER,MEM_GENLIST,PULL_EXISTS,MEM_QSORT,
            MEM_toAList,EXISTS_PROD,FORALL_PROD,cut_env_def]
  \\ strip_tac >> rveq
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
  \\ simp_tac (srw_ss()) [MULT_COMM,MULT_DIV]);

val push_env_set_store = Q.prove(
  `push_env env ^nn (set_store AllocSize (Word c) s) =
    set_store AllocSize (Word c) (push_env env ^nn s)`,
  fs [push_env_def,set_store_def,env_to_list_def,LET_DEF])|> INST_TYPE [beta|-> alpha, gamma|->beta];

val state_rel_set_store_0 = Q.prove(
  `state_rel k 0 0 s5 t5 len ==>
    state_rel k 0 0 (set_store AllocSize w s5) (set_store AllocSize w t5) len`,
  rpt strip_tac
  \\ fs [state_rel_def,set_store_def,stackSemTheory.set_store_def,LET_DEF,
         FLOOKUP_DEF] \\ REPEAT STRIP_TAC \\ rfs[]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [fmap_EXT,DRESTRICT_DEF,EXTENSION]
  \\ rpt strip_tac  THEN1 (Cases_on `x = Handler` \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]
  \\ metis_tac[]);

val MAP_SND_MAP_FST = Q.prove(
  `!xs f. MAP SND (MAP_FST f xs) = MAP SND xs`,
  Induct \\ fs [MAP,MAP_FST_def,FORALL_PROD]);

val read_bitmap_not_empty = Q.prove(`
  read_bitmap stack = SOME a ⇒
  stack ≠ []`,
  rw[]>>CCONTR_TAC>>
  fs[]>>
  fs[read_bitmap_def])

val n2w_lsr_1 = Q.prove(
  `n < dimword (:'a) ==> n2w n >>> 1 = (n2w (n DIV 2)):'a word`,
  once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr] \\ fs []
  \\ fs [DIV_LT_X] \\ decide_tac);

val handler_bitmap_props = Q.prove(`
  good_dimindex(:'a) ⇒
  read_bitmap ((4w:'a word)::stack) = SOME [F;F]`,
  fs [read_bitmap_def,good_dimindex_def] \\ strip_tac
  \\ `~(word_msb 4w)` by fs [word_msb_def,wordsTheory.word_index] \\ fs []
  \\ `4 < dimword (:'a) /\ 2 < dimword (:'a)` by fs [dimword_def]
  \\ `bit_length 4w = 3` by
   (NTAC 4 (fs [dimword_def,Once bit_length_def,n2w_lsr_1,EVAL ``1w ⋙ 1``]))
  \\ fs [] \\ EVAL_TAC \\ rw [] \\ decide_tac)

val enc_stack_lemma = Q.prove(
  `∀bs (wstack:'a stack_frame list) sstack lens astack bs'.
      good_dimindex(:'a) ∧
      LENGTH bs + 1 < dimword (:'a) ∧
      abs_stack bs wstack sstack lens = SOME astack ∧
      (*The first bitmap is the handler one*)
      1 ≤ LENGTH bs ∧
      HD bs = 4w ∧
      stack_rel_aux k len wstack astack ⇒
      enc_stack bs sstack = SOME (enc_stack wstack)`,
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
  \\ qmatch_assum_rename_tac`stack_rel_aux _ _ (StackFrame _ (SOME p)::_) _`
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
  simp[full_read_bitmap_def,MAP_SND_MAP_FST]);

val IMP_enc_stack = Q.prove(
  `state_rel k 0 0 s1 t1 lens
    ==>
    (enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
       SOME (enc_stack s1.stack))`,
  fs [state_rel_def,LET_DEF] \\ rpt strip_tac
  \\ fs [stack_rel_def] \\ imp_res_tac enc_stack_lemma>>
  simp[]);

val map_bitmap_success = Q.prove(`
  ∀bs stack a b ls.
  filter_bitmap bs stack = SOME(a,b) ∧
  LENGTH ls = LENGTH a ⇒
  ∃x z.
  map_bitmap bs ls stack = SOME(x,[],DROP (LENGTH bs) stack) ∧
  filter_bitmap bs x = SOME(ls,[])`,
  ho_match_mp_tac filter_bitmap_ind>>fs[filter_bitmap_def,map_bitmap_def]>>
  rw[LENGTH_NIL]
  >-
    (res_tac>>fs[filter_bitmap_def])
  >>
    EVERY_CASE_TAC>>fs[]>>
    rveq>>Cases_on`ls`>>fs[map_bitmap_def,filter_bitmap_def]>>
    res_tac>>fs[filter_bitmap_def])

(*Might need to extend c as well*)
val map_bitmap_more = Q.prove(`
  ∀bs ls stack n a c ls'.
  map_bitmap bs ls stack = SOME(a,[],c) ⇒
  map_bitmap bs (ls++ls') stack = SOME(a,ls',c)`,
  ho_match_mp_tac map_bitmap_ind>>fs[map_bitmap_def]>>rw[]>>
  pop_assum mp_tac>>ntac 3 TOP_CASE_TAC>>fs[])

val map_bitmap_more_simp = Q.prove(`
  map_bitmap bs (TAKE (LENGTH l) ls) stack = SOME (a,[],c) ⇒
  map_bitmap bs ls stack = SOME (a,DROP (LENGTH l) ls,c)`,
  metis_tac[TAKE_DROP,map_bitmap_more])

(*These two are actually implied by s_key_eq*)
val word_stack_dec_stack_shape = Q.prove(`
  ∀ls wstack res n.
  dec_stack ls wstack = SOME res ∧ n < LENGTH wstack ⇒
  (is_handler_frame (EL n wstack) ⇔ is_handler_frame (EL n res))`,
  ho_match_mp_tac dec_stack_ind>>fs[dec_stack_def,is_handler_frame_def]>>
  rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  rveq>>
  Cases_on`n`>-
    (Cases_on`handler`>>
    simp[is_handler_frame_def])>>
  simp[]);

val sorted_env_zip = Q.prove(`
  ∀l:(num,'a word_loc) alist ls:'a word_loc list x.
  sorted_env (StackFrame l x) ∧
  LENGTH ls = LENGTH l⇒
  sorted_env (StackFrame (ZIP (MAP FST l, ls)) x)`,
  fs[sorted_env_def]>>
  Induct>>fs[LENGTH_NIL]>>rw[]>>
  Cases_on`ls`>>fs[]>>
  qmatch_abbrev_tac`SORTED R _`>>
  `transitive R` by
    (fs[Abbr`R`,transitive_def]>>
    DECIDE_TAC)>>
  fs[SORTED_EQ,MEM_ZIP,PULL_EXISTS,MEM_EL]>>
  rw[]>>res_tac>>
  fs[Abbr`R`,EL_MAP]);

val word_stack_dec_stack_sorted = Q.prove(`
  ∀(ls:'a word_loc list) (wstack:'a stack_frame list) res.
  dec_stack ls wstack = SOME res ∧
  EVERY sorted_env wstack ⇒
  EVERY sorted_env res`,
  ho_match_mp_tac dec_stack_ind>>fs[dec_stack_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>rveq>>
  rfs[]>>
  match_mp_tac sorted_env_zip>>
  simp[])

val abs_stack_empty = Q.prove(`
  ∀bs ls stack lens.
  abs_stack bs [] ls lens = SOME stack ⇒ ls = [Word 0w] ∧ lens = []`,
  rpt Cases>>fs[abs_stack_def])

val abs_frame_eq_def = Define`
  abs_frame_eq p q ⇔
  FST p = FST q ∧
  FST (SND p) = FST (SND q) ∧
  LENGTH (SND (SND p)) = LENGTH (SND (SND q))`

val LIST_REL_abs_frame_eq_handler_val = Q.prove(`
  ∀xs ys.
  LIST_REL abs_frame_eq xs ys ⇒
  handler_val xs = handler_val ys`,
  ho_match_mp_tac LIST_REL_ind>>
  fs[handler_val_def,abs_frame_eq_def,FORALL_PROD]>>rw[]>>
  Cases_on`p_1`>>fs[handler_val_def])

(*Prove the inductive bits first...*)
val dec_stack_lemma1 = Q.prove(`
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
  LIST_REL abs_frame_eq astack bstack`,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  fsrw_tac[][dec_stack_def,enc_stack_def]>>
  srw_tac[][]>>
  fsrw_tac[][Once stackSemTheory.enc_stack_def,abs_stack_def]
  >-
    (rveq>>
    Cases_on`ls`>>fsrw_tac[][dec_stack_def]>>
    simp[stackSemTheory.dec_stack_def]>>rveq>>simp[abs_stack_def])
  >-
    (qpat_x_assum`A=SOME wdec` mp_tac>>
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
    CONJ_TAC>- (
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
      \\ simp[MAP_FST_def,o_DEF,LAMBDA_PROD,MAP_MAP_o]) >>
    fsrw_tac[][abs_frame_eq_def]>>
    simp[])
  >>
    (qpat_x_assum`A=SOME wdec` mp_tac>>
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
    simp[]))

val dec_stack_lemma = Q.prove(`
  good_dimindex(:'a) ∧
  1 ≤ LENGTH t1.bitmaps ∧
  HD t1.bitmaps = 4w ∧
  (t1:('a,'c,'ffi) stackSem$state).stack_space ≤ LENGTH t1.stack ∧
  enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
      SOME (enc_stack s1.stack) /\
    (dec_stack x0 (s1:('a,'a word list # 'c,'ffi) wordSem$state).stack = SOME x) /\
    stack_rel k s1.handler s1.stack (SOME (t1.store ' Handler))
      (DROP t1.stack_space t1.stack) (LENGTH t1.stack) t1.bitmaps lens /\
    (LENGTH (enc_stack s1.stack) = LENGTH x0) ==>
    ?yy:'a word_loc list. dec_stack t1.bitmaps x0 (DROP t1.stack_space t1.stack) = SOME yy /\
         (t1.stack_space + LENGTH yy = LENGTH t1.stack) /\
         stack_rel k s1.handler x (SOME (t1.store ' Handler)) yy
            (LENGTH t1.stack) t1.bitmaps lens`,
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
  );

val gc_state_rel = Q.prove(
  `(gc (s1:('a,'a word list # 'c,'ffi) wordSem$state) = SOME s2) /\ state_rel k 0 0 s1 (t1:('a,'c,'ffi) stackSem$state) lens /\ (s1.locals = LN) ==>
    ?(t2:('a,'c,'ffi) stackSem$state). gc t1 = SOME t2 /\ state_rel k 0 0 s2 t2 lens`,
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
  \\ metis_tac[]);

val alloc_alt = Q.prove(
  `FST (alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state)) <>
    SOME (Error:'a wordSem$result) ==>
    (alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state) =
     case cut_env names s.locals of
       NONE => (SOME Error,s)
     | SOME env =>
         case gc (set_store AllocSize (Word c)
                    (push_env env ^nn s with locals := LN)) of
           NONE => (SOME Error,s)
         | SOME s' =>
             case pop_env s' of
               NONE => (SOME Error,s')
             | SOME s' =>
                 case FLOOKUP s'.store AllocSize of
                   NONE => (SOME Error,s')
                 | SOME w =>
                     case has_space w s' of
                       NONE => (SOME Error,s')
                     | SOME T => (NONE,s')
                     | SOME F =>
                         (SOME NotEnoughSpace,
                          call_env [] s' with stack := []))`,
  fs [alloc_def]
  \\ Cases_on `cut_env names s.locals` \\ fs []
  \\ fs [gc_def,set_store_def,push_env_def,LET_DEF,
         env_to_list_def,pop_env_def]
  \\ BasicProvers.EVERY_CASE_TAC
   \\ fs [state_component_equality] \\ rw []
   \\ fs [state_component_equality] \\ rw []);

(*MEM to an EL characterization for index lists*)
val MEM_index_list_LIM = Q.prove(`
  ∀ls n v k.
  MEM (n,v) (index_list ls k) ⇒
  n-k < LENGTH ls`,
  Induct>>fs[index_list_def]>>rw[]
  >-
    DECIDE_TAC
  >>
  res_tac>>
  DECIDE_TAC)

val MEM_index_list_EL = Q.prove(`
  ∀ls n v.
  MEM (n,v) (index_list ls k) ⇒
  EL (LENGTH ls - (n-k+1)) ls = v`,
  Induct>>fs[index_list_def,FORALL_PROD]>>rw[]>>
  simp[ADD1]>>
  res_tac>>
  fs[]>>
  imp_res_tac MEM_index_list_LIM>>
  `LENGTH ls +1 - (n-k+1) = SUC(LENGTH ls - (n-k+1))` by DECIDE_TAC>>
  pop_assum SUBST_ALL_TAC>>
  simp[])

val _ = type_abbrev("result", ``:'a wordSem$result``)
val alloc_IMP_alloc = Q.prove(
  `(wordSem$alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state) = (res:'a result option,s1)) /\
    (∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
    1 ≤ f /\
    state_rel k f f' s t5 lens /\
    state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 (f'::lens) /\
    (cut_env names s.locals = SOME env) /\
    res <> SOME Error ==>
    ?t1:('a,'c,'ffi) stackSem$state res1.
      (stackSem$alloc c t5 = (res1:'a stackSem$result option,t1)) /\
      if res = NONE then
        res1 = NONE /\ state_rel k f f' s1 t1 lens
      else
        res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) /\
        s1.clock = t1.clock /\ s1.ffi = t1.ffi`,
  Cases_on `FST (alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fsrw_tac[] [] \\ rfs [])
  \\ fsrw_tac[] [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fsrw_tac[] [push_env_set_store]
  \\ imp_res_tac state_rel_set_store_0
  \\ pop_assum (mp_tac o Q.SPEC `Word c`) \\ REPEAT STRIP_TAC
  \\ Cases_on `gc (set_store AllocSize (Word c)
                     (push_env env ^nn s with locals := LN))`
  \\ fsrw_tac[] [] \\ imp_res_tac gc_state_rel \\ NTAC 3 (POP_ASSUM (K ALL_TAC)) \\ fsrw_tac[] []
  \\ pop_assum mp_tac \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fsrw_tac[] [set_store_def,push_env_def]) \\ rpt strip_tac
  \\ fsrw_tac[] [] \\ Cases_on `pop_env x` \\ fsrw_tac[] []
  \\ Q.MATCH_ASSUM_RENAME_TAC `pop_env s2 = SOME s3`
  \\ `state_rel k f f' s3 t2 lens` by
    (imp_res_tac gc_s_key_eq>>
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
    CONJ_TAC>-
      metis_tac[]>>
    CONJ_ASM1_TAC>-
      (imp_res_tac dec_stack_length>>
      fsrw_tac[][LENGTH_DROP]>>
      DECIDE_TAC)>>
    simp[wf_fromAList] >>
    CONJ_TAC>-
      (fsrw_tac[][stack_rel_def,LET_THM]>>
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
    >- (fsrw_tac[] [listTheory.DROP_NIL,DECIDE ``m>=n<=>n<=m:num``] \\ `F` by decide_tac)>>
    qpat_x_assum`A=SOME x'`mp_tac>>
    simp[stackSemTheory.dec_stack_def]>>
    rpt TOP_CASE_TAC>>strip_tac>>rveq
    >-
      simp[abs_stack_def,full_read_bitmap_def]>>
    fsrw_tac[][abs_stack_def,LET_THM]>>
    TOP_CASE_TAC>>simp[]>>
    strip_tac>>rveq>>
    simp[stack_rel_aux_def]>>
    ntac 4 strip_tac>>
    `n ∈ domain (fromAList l)` by
      metis_tac[domain_lookup]>>
    `n ∈ domain names ∧ n ∈ domain s.locals` by
      (fsrw_tac[][cut_env_def]>>
      `n ∈ domain env` by fsrw_tac[][]>>
      rveq>>
      fsrw_tac[][domain_inter])>>
    res_tac>>simp[]>>
    qpat_x_assum` ∀n v. A ⇒ B` mp_tac>>
    fsrw_tac[][domain_lookup]>>
    disch_then (qspecl_then [`n`,`v''`] mp_tac)>>fsrw_tac[][]>>
    `~ (n DIV 2 < k)` by DECIDE_TAC>>
    simp[]>>strip_tac>>
    fsrw_tac[][lookup_fromAList]>>
    `MEM (n,v') l` by metis_tac[ALOOKUP_MEM]>>
    `MEM (n DIV 2,v') (MAP_FST adjust_names l)` by
      (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
      metis_tac[])>>
    simp[LLOOKUP_THM]>>
    qpat_abbrev_tac`ls = TAKE A B`>>
    imp_res_tac filter_bitmap_MEM>>
    imp_res_tac MEM_index_list_EL>>
    fsrw_tac[][Abbr`ls`]>>
    pop_assum mp_tac>>
    simp[LENGTH_TAKE]>>
    ` k + LENGTH x'' - n DIV 2 =
      SUC ( k+ LENGTH x'' - (n DIV 2 +1))` by
        DECIDE_TAC>>
    simp[])
  \\ Cases_on `FLOOKUP s3.store AllocSize` \\ fsrw_tac[] []
  \\ Cases_on `has_space x s3` \\ fsrw_tac[] []
  \\ `s3.store SUBMAP t2.store` by
    (fsrw_tac[] [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM] \\ NO_TAC)
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fsrw_tac[] []
  \\ fsrw_tac[] [has_space_def,stackSemTheory.has_space_def]
  \\ EVERY_CASE_TAC \\ fsrw_tac[] []
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fsrw_tac[] [] \\ srw_tac[] [] \\ fsrw_tac[] []
  \\ fsrw_tac[] [state_rel_def]);

val word_gc_empty_frame = Q.prove(`
  gc (s with stack:= (StackFrame [] NONE::s.stack)) = SOME x ∧
  pop_env x = SOME y ⇒
  y.locals = LN ∧
  gc s = SOME (y with locals:=s.locals)`,
  fs[gc_def,enc_stack_def,dec_stack_def,LET_THM]>>EVERY_CASE_TAC>>
  rw[]>>fs[pop_env_def]>>
  rveq>>fs[fromAList_def]>>
  rw[]>>rveq>>fs[pop_env_def]>>
  fs[state_component_equality])

val alloc_IMP_alloc2 = Q.prove(`
  (wordSem$alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state) = (res:'a result option,s1)) ∧
  state_rel k 0 0 s t lens ∧
  domain names = {} ∧
  res ≠ SOME Error ⇒
  ∃(t1:('a,'c,'ffi) stackSem$state) res1.
    (stackSem$alloc c t = (res1:'a stackSem$result option,t1)) ∧
    if res = NONE then
      res1 = NONE ∧ state_rel k 0 0 s1 t1 lens
    else
      res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) ∧
      s1.clock = t1.clock /\ s1.ffi = t1.ffi`,
  Cases_on `FST (alloc c names (s:('a,'a word list # 'c,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fs [] \\ rfs [])
  \\ fs [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fs [push_env_set_store]
  \\ imp_res_tac state_rel_set_store_0
  \\ pop_assum (mp_tac o Q.SPEC `Word c`)
  \\ REPEAT STRIP_TAC>>
  qpat_x_assum`A=(res,s1)` mp_tac>>
  ntac 2 TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  qmatch_assum_abbrev_tac`gc A = SOME x'`>>
  qabbrev_tac`B = A with stack:= s.stack`>>
  `A = B with stack:=StackFrame [] NONE::B.stack` by
    (unabbrev_all_tac>>fs[state_component_equality,set_store_def]>>
    fs [set_store_def,push_env_def,LET_THM,env_to_list_def]>>
    fs[cut_env_def]>>
    `domain x = {}` by (rveq>>fs[domain_inter])>>
    `toAList x = []` by
      (Cases_on`toAList x`>>fs[]>>
      `MEM (FST h) (MAP FST(toAList x))` by fs[]>>
      rfs[toAList_domain])>>
    fs[]>>
    EVAL_TAC)>>
  fs[]>>imp_res_tac word_gc_empty_frame>>
  imp_res_tac gc_state_rel>>
  ntac 6 (pop_assum kall_tac)>>
  pop_assum mp_tac>>
  disch_then(qspecl_then [`set_store AllocSize (Word c) t`,`lens`,`k`] mp_tac)>>
  impl_tac>-
    (fs[markerTheory.Abbrev_def,state_component_equality,set_store_def,push_env_def,state_rel_def,LET_THM,env_to_list_def,lookup_def]>>
    fs[FUN_EQ_THM,wf_def]>>
    metis_tac[])>>
  impl_keep_tac>-
    (fs[markerTheory.Abbrev_def,state_component_equality,set_store_def,push_env_def])>>
  rw[]>>
  fs[]>>
  pop_assum mp_tac>>
  ntac 2 TOP_CASE_TAC>>fs[]
  \\ `x''.store SUBMAP t2.store` by
    fs [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ fs [has_space_def,stackSemTheory.has_space_def]
  \\ qpat_x_assum`Z=SOME x''''` mp_tac
  \\ ntac 2 TOP_CASE_TAC>>fs[]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ ntac 2 TOP_CASE_TAC \\ fs[]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ TOP_CASE_TAC>>fs[]
  \\ rw []
  \\ fs [state_rel_def]
  \\ metis_tac[]);

val compile_result_def = Define`
  (compile_result (Result w1 w2) = Result w1) ∧
  (compile_result (Exception w1 w2) = Exception w1) ∧
  (compile_result TimeOut = TimeOut) ∧
  (compile_result NotEnoughSpace = Halt (Word 1w)) ∧
  (compile_result (FinalFFI f) = FinalFFI f) ∧
  (compile_result Error = Error)`;
val _ = export_rewrites["compile_result_def"];

val Halt_EQ_compile_result = Q.prove(
  `(Halt (Word 1w) = compile_result z <=> z = NotEnoughSpace) /\
    (good_dimindex (:'a) ==> Halt (Word (2w:'a word)) <> compile_result z)`,
  Cases_on `z` \\ fs [] \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]);

val stack_evaluate_add_clock_NONE =
  stackPropsTheory.evaluate_add_clock
  |> Q.SPECL [`p`,`s`,`NONE`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL

val push_locals_def = Define `
  push_locals s = s with <| locals := LN;
    stack := StackFrame (FST (env_to_list s.locals (K I))) NONE :: s.stack |>`

val LASTN_LENGTH_ID2 = Q.prove(`
  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack`,
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID])

val stack_rel_aux_LENGTH = Q.prove(`
  ∀k len xs ys.
  stack_rel_aux k len xs ys ⇒
  LENGTH xs = LENGTH ys`,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>fs[stack_rel_aux_def])

val LASTN_MORE = Q.prove(`
  ∀ls n.
  ¬(n < LENGTH ls) ⇒ LASTN n ls = ls`,
  fs[LASTN_def]>>Induct>>rw[]>>
  Cases_on`n < LENGTH ls`>>
  fs[TAKE_APPEND1,LENGTH_REVERSE] >>
    res_tac>>
    fs[TAKE_APPEND]>>
    IF_CASES_TAC>>fs[]>>
    DECIDE_TAC)

val stack_rel_aux_LASTN = Q.prove(`
  ∀k len xs ys n.
  stack_rel_aux k len xs ys ⇒
  stack_rel_aux k len (LASTN n xs) (LASTN n ys)`,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>
  fs[stack_rel_aux_def]>>rw[]>>
  imp_res_tac stack_rel_aux_LENGTH
  >-
    fs[LASTN_def,stack_rel_aux_def]
  >>
    Cases_on`n ≤ LENGTH xs`>>rfs[LASTN_CONS]>>
    `¬(n < SUC(LENGTH ys))` by DECIDE_TAC>>
    fs[LASTN_MORE,stack_rel_aux_def])

val abs_stack_to_stack_LENGTH = Q.prove(`
  ∀bs wstack sstack lens stack.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val stack = LENGTH sstack`,
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
    simp[handler_val_def]))

(*Equality theorems available if n ≤ LENGTH ls*)
val LASTN_LENGTH_BOUNDS = Q.prove(`
  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls`,
  fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]>>rw[]>>
  decide_tac)

val LASTN_CONS_ID = Q.prove(`
  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)`,
  rw[]>>EVAL_TAC>>fs[])

(*Strengthened version of LASTN_DROP after change to make it total*)
val LASTN_DROP2 = Q.prove(`
  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l`,
  Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]>>
  Cases_on`n > LENGTH l`>>fs[ADD1]>>
  `LENGTH l - n = 0` by fs[]>>
  simp[DROP_def]);

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
*)
val abs_stack_prefix_drop = Q.prove(`
  ∀bs wstack sstack lens stack h wrest k len.
  h ≤ LENGTH wstack ∧
  LASTN h wstack = wrest ∧
  abs_stack bs wstack sstack lens = SOME stack ∧
  stack_rel_aux k len wstack stack ⇒
  let rest = LASTN h stack in
  let lrest = LASTN h lens in
  let srest = LASTN (handler_val rest) sstack in
  abs_stack bs wrest srest lrest = SOME rest ∧
  stack_rel_aux k len wrest rest`,
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
      fs[Abbr`frame`,Abbr`ls`,abs_stack_def,LET_THM,full_read_bitmap_def]);

val abs_stack_len = Q.prove(`
  ∀bs wstack sstack lens stack handler.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val (LASTN handler stack) ≤ LENGTH sstack`,
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
      DECIDE_TAC));

val EL_REVERSE_REWRITE = Q.prove(`
  ∀l n k. n < LENGTH l ∧ k < n ⇒
  EL (LENGTH l - n + k) l = EL (n-k -1) (REVERSE l)`,
  rw[]>> fs[EL_REVERSE,PRE_SUB1]);

val LASTN_LESS = Q.prove(`
  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs`,
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
  fs[LASTN_CONS]);

val ALOOKUP_IFF_MEM = Q.prove(
  `ALL_DISTINCT (MAP FST l) ==>
    (ALOOKUP l q = SOME r <=> MEM (q,r) l)`,
  Induct_on `l` \\ fs [FORALL_PROD,MEM_MAP] \\ rw [] \\ metis_tac []);

val SORTED_CONS_IMP = Q.prove(
  `SORTED (\x y. FST x > (FST y):num) (h::t) ==>
    ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
    !x. MEM x t ==> FST h > FST x`,
  Induct_on `t` \\ fs [SORTED_DEF] \\ rw []
  \\ `SORTED (\x y. FST x > FST y) (h::t)` by
    (Cases_on `t` \\ fs [SORTED_DEF] \\ decide_tac)
  \\ fs [] \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ disj1_tac \\ decide_tac);

val SORTED_IMP_ALL_DISTINCT_LEMMA = Q.prove(
  `!l. SORTED (\x y. FST x > (FST y):num) l ==> ALL_DISTINCT (MAP FST l)`,
  Induct \\ fs [] \\ rw [MEM_MAP]
  \\ metis_tac [DECIDE ``m>n ==> m<>n:num``,SORTED_CONS_IMP]);

val MEM_toAList_fromAList = Q.prove(
  `SORTED (\x y. FST x > (FST y):num) l ==>
    MEM a (toAList (fromAList l)) = MEM a l`,
  Cases_on `a` \\ fs [MEM_toAList,lookup_fromAList] \\ rw []
  \\ imp_res_tac SORTED_IMP_ALL_DISTINCT_LEMMA \\ fs [ALOOKUP_IFF_MEM]);

val SORTED_FST_PERM_IMP_ALIST_EQ = Q.prove(
  `SORTED (\x y. FST x > FST y) l /\
    SORTED (\x y. FST x > FST y) q /\
    PERM (toAList (fromAList l)) q ==>
    q = l`,
  rw [] \\ drule MEM_PERM \\ fs [MEM_toAList_fromAList]
  \\ pop_assum kall_tac \\ rpt (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Induct_on `q` \\ fs [MEM]
  THEN1 (Cases \\ fs[] \\ metis_tac [])
  \\ Cases_on `l` THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rw []
  \\ imp_res_tac SORTED_CONS_IMP
  \\ `!m n:num. m > n /\ n > m ==> F` by decide_tac
  \\ metis_tac []);

val stack_rel_raise = Q.prove(`
    n ≤ LENGTH sstack /\
    handler+1 ≤ LENGTH wstack /\ SORTED (\x y. FST x > FST y) l /\
    LASTN (handler + 1) wstack = StackFrame l (SOME (h1,l3,l4))::rest /\
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
        (StackFrame (FST (env_to_list (fromAList l) (K I))) NONE::rest)
            ((NONE,payload) :: LASTN handler stack) /\
      abs_stack bs (StackFrame (FST (env_to_list (fromAList l) (K I))) NONE::rest)
        (DROP (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 3)
           sstack) (LASTN (handler+1) lens) = SOME ((NONE,payload) :: LASTN handler stack)`,
  rw[]>>
  imp_res_tac abs_stack_prefix_drop>>
  fs[LET_THM]>>
  Cases_on`LASTN (handler+1) stack`>>fs[stack_rel_aux_def]>>
  PairCases_on`h`>>Cases_on`h0`>>fs[stack_rel_aux_def]>>
  PairCases_on`x`>>fs[stack_rel_aux_def]>>
  `FST (env_to_list (fromAList l) (K I)) = l` by
   (Cases_on `env_to_list (fromAList l) (K I)` \\ fs []
    \\ imp_res_tac env_to_list_K_I_IMP \\ rw []
    \\ metis_tac [SORTED_FST_PERM_IMP_ALIST_EQ]) >>
  imp_res_tac abs_stack_IMP_LENGTH>>fs[]>>
  CONJ_TAC>- fs[LASTN_LESS]>>
  imp_res_tac abs_stack_len>>
  fs[handler_val_def]>>CONJ_ASM1_TAC>-
    (qhdtm_x_assum `abs_stack` mp_tac>>
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
  `EL 1 ls = Loc l3 l4
   ∧ (preconds ⇒ EL 2 ls = w)` by
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
  fs[abs_stack_def,LET_THM]);

val EVERY_IMP_EVERY_LASTN = Q.prove(
  `!xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys`,
  fs [EVERY_MEM] \\ rw [] \\ imp_res_tac MEM_LASTN_ALT \\ res_tac \\ fs []);

val LASTN_HD = Q.prove(`
  ∀ls x.
  x ≤ LENGTH ls ⇒
  HD (LASTN x ls) =
  EL (LENGTH ls - x) ls`,
  fs[LASTN_def]>>
  Induct>>rw[]>>
  Cases_on`x = SUC(LENGTH ls)`
  >-
    simp[TAKE_APPEND2,REVERSE_APPEND]
  >>
    `x ≤ LENGTH ls` by DECIDE_TAC>>fs[TAKE_APPEND1]>>
    `SUC (LENGTH ls) -x = SUC(LENGTH ls - x)` by DECIDE_TAC>>
    simp[])

Theorem insert_bitmap_isPREFIX:
   ∀bs bs' i. insert_bitmap bm bs = (bs',i) ⇒ bs ≼ bs'
Proof
  Induct
  \\ rw[insert_bitmap_def,LET_THM]
  \\ fs[IS_PREFIX_APPEND]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ simp[]
QED

Theorem wLive_isPREFIX:
   ∀a bs c q bs'. wLive a bs c = (q,bs') ⇒ bs ≼ bs'
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
   ∀c1 bs r q1 bs'. comp c1 bs r = (q1,bs') ==> bs ≼ bs'
Proof
  ho_match_mp_tac comp_ind
  \\ rw[comp_def,LET_THM]
  \\ every_case_tac \\ fs[]
  \\ rpt (pairarg_tac >> fs[])
  \\ rveq
  \\ metis_tac[IS_PREFIX_TRANS,wLive_isPREFIX]
QED

val compile_prog_isPREFIX = Q.prove(
  `compile_prog x y k bs = (prog,bs1) ==> bs ≼ bs1`,
  fs [compile_prog_def,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ imp_res_tac comp_IMP_isPREFIX
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []);

Theorem compile_word_to_stack_isPREFIX:
   !code k bs progs1 bs1.
       compile_word_to_stack k code bs = (progs1,bs1) ==> bs ≼ bs1
Proof
  Induct \\ fs [compile_word_to_stack_def,FORALL_PROD,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ imp_res_tac compile_prog_isPREFIX
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
QED

Theorem compile_word_to_stack_bitmaps:
   word_to_stack$compile c p = (c2,prog1) ==>
    (case c2.bitmaps of [] => F | h::v1 => 4w = h)
Proof
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  \\ Cases_on `bitmaps` \\ fs []
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

val with_same_locals = save_thm("with_same_locals[simp]",
  EQT_ELIM(SIMP_CONV(srw_ss())[state_component_equality]``s with locals := s.locals = (s:('a,'b,'c) wordSem$state)``));

Theorem state_rel_get_var_imp:
   state_rel k f f' s t lens ∧ get_var (2 * x) s = SOME v ∧ x < k ⇒ FLOOKUP t.regs x = SOME v
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

Theorem state_rel_get_var_imp2:
   state_rel k f f' s t lens ∧
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
   (state_rel k f f' s (set_var (k+1) v t) lens ⇔ state_rel k f f' s t lens) ∧
   (state_rel k f f' s (set_var k v t) lens ⇔ state_rel k f f' s t lens)
Proof
  conj_tac
  \\ simp[state_rel_def,EQ_IMP_THM,stackSemTheory.set_var_def]
  \\ ntac 2 strip_tac
  \\ fs[FLOOKUP_UPDATE]
  \\ metis_tac[DECIDE``¬(k + 1n < k) ∧ ¬(k < k)``]
QED

Theorem state_rel_set_var:
    state_rel k f f' s t lens ∧ x < k ⇒
    state_rel k f f' (set_var (2*x) v s) (set_var x v t) lens
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

Theorem state_rel_set_var2:
    state_rel k f f' s t lens ∧ ¬(x < k) ∧ x < f' + k ∧ st = t.stack ∧ sp = t.stack_space ⇒
    state_rel k f f' (set_var (2*x) v s)
    (t with stack := LUPDATE v (sp + (f + k − (x + 1))) st) lens
Proof
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ strip_tac
  \\ `0<f` by
      (Cases_on`f'`>>fs[]>>DECIDE_TAC)
  \\ fs[lookup_insert,FLOOKUP_UPDATE,wf_insert]
  \\ simp[DROP_LUPDATE]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ CONJ_TAC THEN1 metis_tac[]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV]
    \\ strip_tac >> rveq
    \\ simp[LLOOKUP_THM]
    \\ simp[EL_LUPDATE])
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ IF_CASES_TAC >> fs[]
  \\ simp[LLOOKUP_THM]
  \\ simp[EL_LUPDATE]
  \\ fs[EVEN_EXISTS]
  \\ rveq
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ fs [LLOOKUP_THM]
  \\ rveq
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ ntac 2 (pop_assum mp_tac)
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ ntac 2 strip_tac
  \\ rw[]
  \\ fsrw_tac[ARITH_ss][]
QED

Theorem wMoveSingle_thm:
   state_rel k f f' s t lens ∧
   (case x of NONE => get_var (k+1) t = SOME v
    | SOME x => get_var (x * 2) s = SOME v ) ∧
   (case y of SOME x => x < f' + k | _ => T)
   ⇒
   ∃t'.
     evaluate (wMoveSingle (format_var k y,format_var k x) (k,f,f'), t) = (NONE,t') ∧
     state_rel k f f' (case y of NONE => s | SOME y => set_var (y*2) v s) t' lens ∧
     (y = NONE ⇒ get_var (k+1) t' = SOME v) ∧
     (y ≠ NONE ⇒ get_var (k+1) t' = get_var (k+1) t)
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

Theorem evaluate_wMoveAux_seqsem:
   ∀ms s t r.
   state_rel k f f' s t lens ∧
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
     state_rel k f f'
       (set_vars
         (MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
         (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
         s) t' lens
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
  \\ pop_assum mp_tac
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

val get_vars_eq = Q.prove(
  `∀ls z.
  get_vars ls st = SOME z ⇒
  let lookups = MAP (\x. lookup x st.locals) ls in
  EVERY IS_SOME lookups ∧
  z = MAP THE lookups`,
  Induct>>fs[get_vars_def,get_var_def]>>rw[]>>unabbrev_all_tac>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[])

val LAST_add_ret_loc = Q.prove(`
  args' ≠ [] ⇒
  LAST (add_ret_loc ret args') =
  LAST args'`,
  Cases_on`ret`>>TRY(PairCases_on`x`)>>fs[add_ret_loc_def]>>
  Cases_on`args'`>>fs[LAST_CONS])

val call_dest_lemma = Q.prove(
  `¬bad_dest_args dest args /\
    state_rel k f f' (s:('a,'a word list # 'c,'ffi) state) t lens /\
    call_dest dest args (k,f,f') = (q0,dest') /\
    get_vars args s = SOME args' ==>
    ?t4:('a,'c,'ffi) stackSem$state. evaluate (q0,t) = (NONE,t4) /\
         state_rel k f f' s t4 lens /\
         !real_args prog.
            find_code dest (add_ret_loc (ret:(num#num_set#'a wordLang$prog#num#num)option) args':'a word_loc list) s.code = SOME (real_args,prog) ==>
            ?bs bs2 stack_prog.
              compile_prog prog (LENGTH real_args) k bs = (stack_prog,bs2) ∧
              bs2 ≼ t4.bitmaps /\
              find_code dest' t4.regs t4.code = SOME stack_prog`,
  Cases_on`dest`>>fs[call_dest_def,bad_dest_args_def,LENGTH_NIL]>>rw[]
  >-
    (fs[wReg2_def,TWOxDIV2,LET_THM]>>
    pairarg_tac>>fs[]>>rveq>>
    EVERY_CASE_TAC>>rw[]
    >-
      (fs[wStackLoad_def,stackSemTheory.evaluate_def,state_rel_def]>>
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
      IF_CASES_TAC>>fs[])
    >>
      rw[stackSemTheory.evaluate_def,wStackLoad_def]>>
      TRY(fs[state_rel_def] \\ `F` by decide_tac)
      >-
      (fs[find_code_def,stackSemTheory.find_code_def,state_rel_def]>>
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
      fs[])
      >>
      imp_res_tac get_vars_eq>>
      fs[state_rel_def,LET_THM]>>
      `∃x.lookup (LAST args) s.locals = SOME x` by
        (fs[LAST_EL,EVERY_EL,EL_MAP,IS_SOME_EXISTS]>>
        first_assum match_mp_tac>>
        Cases_on`args`>>fs[])>>
      res_tac>>fs[]>>
      pop_assum mp_tac>>
      IF_CASES_TAC>>fs[]>>
      Cases_on`f'`>>fs[])
  >>
    fs[stackSemTheory.evaluate_def,state_rel_def]>>
    CONJ_TAC>-
      metis_tac[]>>
    fs[find_code_def,stackSemTheory.find_code_def]>>
    ntac 2 TOP_CASE_TAC>>rw[]>>
    res_tac>>
    simp[]);

val compile_result_NOT_2 = Q.prove(
  `good_dimindex (:'a) ==>
    compile_result x ≠ Halt (Word (2w:'a word))`,
  Cases_on `x` \\ fs [compile_result_def]
  \\ rw [good_dimindex_def] \\ fs [dimword_def]);

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

val TIMES2_DIV2_lemma = Q.prove(
  `windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves))))
    = MAP THE (FILTER IS_SOME (MAP FST (parmove moves)))`,
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
  \\ metis_tac[]);

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

val parsem_parmove_DIV2_lemma = Q.prove(
  `windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
      (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves)))) =
   (MAP (parsem (MAP (SOME ## SOME) moves) (r o OPTION_MAP DIV2))
     (FILTER IS_SOME (MAP FST (parmove moves))))`,
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
  \\ rveq \\ fs[]);

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

val wf_fromList2 = Q.prove(`
  ∀ls. wf(fromList2 ls)`,
  ho_match_mp_tac SNOC_INDUCT>>
  fs[fromList2_def,FOLDL_SNOC,wf_def]>>rw[]>>
  pairarg_tac>>fs[wf_insert])

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
   state_rel k f f' s t lens ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel k f f' (set_var (2 * m) v s) t' lens
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

Theorem wRegWrite1_thm2:
   state_rel k f f' s t lens ∧
   m < f' + k ∧
   (∀n.  n ≤ k ⇒
     evaluate (kont n, t) = (NONE, set_var 0 v' (set_var n v t)))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel k f f' (set_var 0 v' (set_var (2 * m) v s)) t' lens
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
  simp[]>>
  match_mp_tac (state_rel_set_var |> Q.GEN`x`|>Q.SPEC`0`|>SIMP_RULE std_ss[])>>
  fs[]
  \\ match_mp_tac state_rel_set_var2
  \\ simp[]
QED

Theorem wRegWrite2_thm1:
   state_rel k f f' s t lens ∧
   m < f' + k ∧
   (∀n.  n ≤ k+1 ⇒
     evaluate (kont n, t) = (NONE, set_var n v t))
   ⇒
   ∃t'.
   evaluate (wRegWrite2 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel k f f' (set_var (2 * m) v s) t' lens
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
   state_rel k f f' s t lens ∧
   mem_store a b s = SOME s' ⇒
   ∃t'.
     mem_store a b t = SOME t' ∧
     state_rel k f f' s' t' lens
Proof
  simp[state_rel_def,stackSemTheory.mem_store_def,wordSemTheory.mem_store_def]
  \\ strip_tac \\ rveq \\ simp[] \\ metis_tac[]
QED

(* TODO: Delete?

Theorem wRegWrite1_thm2:
   state_rel k f f' s t lens ∧
   m < f' + k ∧
   get_var (2 * m) s = SOME w ∧
   mem_store a w s = SOME s' ∧
   (∀n. get_var n t = SOME w ⇒
     evaluate (kont n, t) = (NONE, THE(mem_store a w t)))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel k f f' s' t' lens
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
   state_rel k f f' s t lens ∧
   mem_store a b s = SOME s' ∧
   m < f' + k ∧
   (∀n. n ≤ k ⇒
      evaluate (kont n, t) =
        (NONE, THE(mem_store a b (if n < k then t else set_var k (EL (t.stack_space + (f-1-(m-k))) t.stack) t))))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel k f f' s' t' lens
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

Theorem wStackLoad_thm1:
   wReg1 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,'a word list # 'c,'ffi)state) = SOME x ∧
   state_rel k f f' s t lens ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧ state_rel k f f' s' t' lens) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont k, set_var k (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel k f f' s' t' lens)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel k f f' s' t' lens
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

Theorem wStackLoad_thm2:
   wReg2 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,'a word list # 'c,'ffi)state) = SOME x ∧
   state_rel k f f' s t lens ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧ state_rel k f f' s' t' lens) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont (k+1), set_var (k+1) (EL (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel k f f' s' t' lens)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel k f f' s' t' lens
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

val map_var_def = tDefine"map_var"`
  (map_var f (Var num) = Var (f num)) ∧
  (map_var f (Load exp) = Load (map_var f exp)) ∧
  (map_var f (Op wop ls) = Op wop (MAP (map_var f) ls)) ∧
  (map_var f (Shift sh e1 e2) = Shift sh (map_var f e1) e2) ∧
  (map_var f (Const c) = Const c) ∧
  (map_var f (Lookup v) = Lookup v)`
(WF_REL_TAC`measure (exp_size ARB o SND)`
 \\ simp[]
 \\ Induct \\ simp[] \\ rw[]
 \\ EVAL_TAC \\ simp[] \\ res_tac \\ simp[]);
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

Theorem word_exp_thm1:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   every_var_exp is_phy_var e ∧
   DIV2 (max_var_exp e) < k ∧
   state_rel k f f' s t lens ⇒
   word_exp t (map_var DIV2 e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS]
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
    \\ fs[DIV2_def,TWOxDIV2]
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
   state_rel k f f' s t lens ∧
   every_var_exp ($= (2 * v)) e ∧
   ¬(v < k) ⇒
   word_exp (set_var k (EL (t.stack_space + (f + k - (v + 1))) t.stack) t) (map_var (K k) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
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

Theorem word_exp_thm3:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel k f f' s t lens ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k+1 else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
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
   state_rel k f f' s t lens ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var k (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
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
   state_rel k f f' s t lens ∧
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
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
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
   state_rel k f f' s t lens ∧
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
  \\ fs[DIV2_def,TWOxDIV2]
  \\ first_x_assum drule
  \\ simp[TWOxDIV2]
  \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
  \\ simp[ADD_COMM]
QED

Theorem set_var_with_memory:
   stackSem$set_var a b c with memory := m = set_var a b (c with memory := m)
Proof
  EVAL_TAC
QED

Theorem set_var_memory[simp]:
   (stackSem$set_var a b c).memory = c.memory
Proof
  EVAL_TAC
QED

Theorem state_rel_with_memory:
   state_rel k f f' s t lens ⇒
   state_rel k f f' (s with memory := m) (t with memory := m) lens
Proof
  simp[state_rel_def]
  \\ strip_tac \\ simp[]
  \\ metis_tac[]
QED

Theorem set_var_swap:
   a ≠ a' ⇒ stackSem$set_var a b (set_var a' b' c) = set_var a' b' (set_var a b c)
Proof
  EVAL_TAC \\ simp[stackSemTheory.state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE]
  \\ rw[] \\ rw[]
QED

Theorem set_var_cancel:
   stackSem$set_var a b (set_var a b c) = set_var a b c
Proof
  EVAL_TAC \\ simp[stackSemTheory.state_component_equality]
QED

Theorem word_exp_Op_SOME_Word:
   word_exp s (Op op wexps) = SOME x ⇒ ∃w. x = Word w
Proof
  rw[word_exp_def] \\ every_case_tac \\ fs[]
QED

Theorem state_rel_get_fp_var:
   state_rel k f f' s t lens ⇒
  get_fp_var n s = get_fp_var n t
Proof
  fs[state_rel_def,get_fp_var_def,stackSemTheory.get_fp_var_def]
QED

Theorem state_rel_set_fp_var:
   state_rel k f f' s t lens ⇒
  state_rel k f f' (set_fp_var n v s) (set_fp_var n v t) lens
Proof
  fs[state_rel_def,set_fp_var_def,stackSemTheory.set_fp_var_def]>>rw[]>>
  metis_tac[]
QED

Theorem evaluate_wInst:
   ∀i s t s'.
   inst i s = SOME s' ∧
   every_var_inst is_phy_var i ∧
   max_var_inst i < 2 * f' + 2 * k ∧
   inst_arg_convention i ∧
   state_rel k f f' s t lens
  ⇒
   ∃t'.
     evaluate (wInst i (k,f,f'), t) = (NONE,t') ∧
     state_rel k f f' s' t' lens
Proof
  simp[inst_def]
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ simp[wInst_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def]
  \\ fs[wordLangTheory.every_var_inst_def,wordLangTheory.max_var_inst_def]
  \\ rw[] \\ rw[]
  >- (
    fs[assign_def,word_exp_def,reg_allocTheory.is_phy_var_def,
       GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ rveq
    \\ match_mp_tac wRegWrite1_thm1
    \\ fs[GSYM LEFT_ADD_DISTRIB]
    \\ rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
          stackSemTheory.assign_def,stackSemTheory.word_exp_def])
  >- (
    reverse BasicProvers.FULL_CASE_TAC
    \\ fs[wordLangTheory.every_var_inst_def,
          wordLangTheory.max_var_inst_def,inst_arg_convention_def]
    >- (* SubOverflow *)
      (fs[get_vars_def]>>pop_assum mp_tac>>
      ntac 4 (FULL_CASE_TAC)>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      simp[wInst_def,TWOxDIV2]>>
      pairarg_tac >> fs[]>>
      pairarg_tac >> fs[]>>
      fs[wStackLoad_append]>>
      strip_tac>> rpt var_eq_tac>>
      qho_match_abbrev_tac`∃t'. evaluate (wStackLoad (l) (kont n2'),t) = (NONE,t') ∧ _ t'`>>fs[]>>
      match_mp_tac (GEN_ALL wStackLoad_thm1)>>
      asm_exists_tac >> simp[]>>
      asm_exists_tac >> simp[]
      \\ simp[Abbr`kont`]
      \\ CONJ_TAC \\ strip_tac
      \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n3),tt) = (NONE,t') ∧ _ t'`
      \\ simp[]
      \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
      \\ asm_exists_tac \\ simp[Abbr`tt`]
      \\ asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ conj_tac \\ strip_tac
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ simp[] \\ disch_then imp_res_tac
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ simp[] \\ disch_then imp_res_tac>>
      rfs[]>>
      match_mp_tac wRegWrite1_thm2>>fs[]>>
      rpt strip_tac>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
           stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
    >- (* AddOverflow *)
      (fs[get_vars_def]>>pop_assum mp_tac>>
      ntac 4 (FULL_CASE_TAC)>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      simp[wInst_def,TWOxDIV2]>>
      pairarg_tac >> fs[]>>
      pairarg_tac >> fs[]>>
      fs[wStackLoad_append]>>
      strip_tac>> rpt var_eq_tac>>
      qho_match_abbrev_tac`∃t'. evaluate (wStackLoad (l) (kont n2'),t) = (NONE,t') ∧ _ t'`>>fs[]>>
      match_mp_tac (GEN_ALL wStackLoad_thm1)>>
      asm_exists_tac >> simp[]>>
      asm_exists_tac >> simp[]
      \\ simp[Abbr`kont`]
      \\ CONJ_TAC \\ strip_tac
      \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n3),tt) = (NONE,t') ∧ _ t'`
      \\ simp[]
      \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
      \\ asm_exists_tac \\ simp[Abbr`tt`]
      \\ asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ conj_tac \\ strip_tac
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ simp[] \\ disch_then imp_res_tac
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ simp[] \\ disch_then imp_res_tac>>
      rfs[]>>
      match_mp_tac wRegWrite1_thm2>>fs[]>>
      rpt strip_tac>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,
           stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
    >- (*AddCarry*)
      (fs[get_vars_def]>>pop_assum mp_tac>>
      ntac 6 (FULL_CASE_TAC)>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      simp[wInst_def,TWOxDIV2]>>
      pairarg_tac >> fs[]>>
      pairarg_tac >> fs[]>>
      fs[wStackLoad_append]>>
      qpat_abbrev_tac`ab = w2n c + A`>> strip_tac>>
      rpt var_eq_tac>>
      qho_match_abbrev_tac`∃t'. evaluate (wStackLoad (l) (kont n2'),t) = (NONE,t') ∧ _ t'`>>fs[]>>
      match_mp_tac (GEN_ALL wStackLoad_thm1)>>
      asm_exists_tac \\ simp[]>>
      asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ CONJ_TAC \\ strip_tac
      \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n3),tt) = (NONE,t') ∧ _ t'`
      \\ simp[]
      \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
      \\ asm_exists_tac \\ simp[Abbr`tt`]
      \\ asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ conj_tac \\ strip_tac
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ simp[] \\ disch_then imp_res_tac
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ simp[] \\ disch_then imp_res_tac>>
      rfs[]>>
      `0 < k ∧ FLOOKUP t.regs 0 = SOME (Word c'')` by
        (CONJ_ASM1_TAC>>fs[get_var_def,state_rel_def]>>res_tac>>
        fs[]>>rfs[])>>
      match_mp_tac wRegWrite1_thm2>>fs[]>>
      rpt strip_tac>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
    >- (*LongDiv*)
      (pop_assum mp_tac>>fs[get_vars_def]>>
      every_case_tac>>fs[wInst_def]>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      fs[TWOxDIV2]>>
      pairarg_tac>>fs[]>>
      strip_tac>>
      qho_match_abbrev_tac`∃t'. evaluate (wStackLoad (l) (kont),t) = (NONE,t') ∧ _ t'`>>fs[]>>
      `kont = (λn. Inst(Arith (LongDiv 0 3 3 0 n))) n5` by fs[]>>
      pop_assum SUBST1_TAC>>
      match_mp_tac (GEN_ALL wStackLoad_thm1)>>
      asm_exists_tac >> simp[]>>
      rfs[]>> asm_exists_tac >> simp[]>>
      drule (GEN_ALL state_rel_get_var_imp)>>
      disch_then assume_tac>>
      first_assum (qspecl_then [`3`,`Word c`] mp_tac)>>
      impl_tac>- fs[state_rel_def]>>
      first_x_assum (qspecl_then [`0`,`Word c'`] mp_tac)>>
      impl_tac>- fs[state_rel_def]>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      `3 < k` by fs[state_rel_def]>>
      rw[]
      >-
        (imp_res_tac state_rel_get_var_imp>>
        fs[]>>
        assume_tac (GEN_ALL state_rel_set_var)>>
        first_assum (qspec_then`0` assume_tac)>>fs[]>>
        pop_assum match_mp_tac>>fs[]>>
        first_assum (qspec_then`3` assume_tac)>>fs[])
      >-
        (imp_res_tac state_rel_get_var_imp2>>
        qpat_abbrev_tac`A = FLOOKUP B 3n`>>
        `A = SOME (Word c)` by fs[Abbr`A`,stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
        qpat_abbrev_tac`Z = FLOOKUP C 0n`>>
        `Z = SOME (Word c')` by fs[Abbr`Z`,stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
        fs[]>>
        assume_tac (GEN_ALL state_rel_set_var)>>
        first_assum (qspec_then`0` assume_tac)>>fs[]>>
        pop_assum match_mp_tac>>fs[]>>
        first_assum (qspec_then`3` assume_tac)>>fs[]))
    >-
      (* LongMul Note: this is greatly simplified because no stack loading is done*)
      (pop_assum mp_tac>>fs[get_vars_def]>>
      every_case_tac>>fs[wInst_def]>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      fs[TWOxDIV2]>>
      drule (GEN_ALL state_rel_get_var_imp)>>
      disch_then assume_tac>>
      first_assum (qspecl_then [`0`,`Word c`] mp_tac)>>
      first_x_assum (qspecl_then [`2`,`Word c'`] mp_tac)>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      `4 < k` by fs[state_rel_def]>>
      rw[]>>
      assume_tac (GEN_ALL state_rel_set_var)>>
      first_assum (qspec_then`0` assume_tac)>>fs[]>>
      pop_assum match_mp_tac>>fs[]>>
      first_assum (qspec_then`3` assume_tac)>>fs[])
    >- (* Div *)
      (fs[get_vars_def]>>pop_assum mp_tac>>
      ntac 5 (FULL_CASE_TAC)>>
      fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      simp[wInst_def,TWOxDIV2]>>
      pairarg_tac >> fs[]>>
      pairarg_tac >> fs[]>>
      fs[wStackLoad_append]>>
      strip_tac>>
      rpt var_eq_tac>>
      qho_match_abbrev_tac`∃t'. evaluate (wStackLoad (l) (kont n2),t) = (NONE,t') ∧ _ t'`>>fs[]>>
      match_mp_tac (GEN_ALL wStackLoad_thm1)>>
      asm_exists_tac \\ simp[]>>
      asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ CONJ_TAC \\ strip_tac
      \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n3),tt) = (NONE,t') ∧ _ t'`
      \\ simp[]
      \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
      \\ asm_exists_tac \\ simp[Abbr`tt`]
      \\ asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ conj_tac \\ strip_tac
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ simp[] \\ disch_then imp_res_tac
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ simp[] \\ disch_then imp_res_tac>>
      rfs[]>>
      match_mp_tac wRegWrite1_thm1>>fs[]>>
      rpt strip_tac>>
      simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.get_vars_def,stackSemTheory.get_var_def]>>
      simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
    >- (
      fs[assign_def,word_exp_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
      \\ simp[wInst_def,TWOxDIV2]
      \\ fs[GSYM LEFT_ADD_DISTRIB]
      \\ fs[GSYM wordSemTheory.get_var_def]
      \\ rveq
      \\ qmatch_asmsub_rename_tac`get_var (2 * v) s`
      \\ Cases_on`get_var (2 * v) s`\\fs[]
      \\ pairarg_tac \\ fs[]
      \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧ _ t'`
      \\ simp[]
      \\ match_mp_tac (GEN_ALL wStackLoad_thm1)
      \\ asm_exists_tac \\ simp[]
      \\ asm_exists_tac \\ simp[]
      \\ simp[Abbr`kont`]
      \\ qpat_x_assum`_ _ _ _ = SOME _`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ strip_tac \\ rveq
      \\ pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ pop_assum mp_tac
      \\ strip_tac \\ rveq
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ simp[] \\ disch_then drule
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ simp[] \\ disch_then drule
      \\ ntac 3 strip_tac
      \\ conj_tac \\ strip_tac \\ fs[]
      \\ match_mp_tac wRegWrite1_thm1
      \\ simp[]
      \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,stackSemTheory.word_exp_def]
      \\ simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE] )
    (* Binop *)
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[wordLangTheory.every_var_imm_def]
    \\ strip_tac \\ fs[GSYM LEFT_ADD_DISTRIB,assign_def]
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq
    \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ imp_res_tac word_exp_Op_SOME_Word
    \\ rveq
    \\ fs[GSYM LEFT_ADD_DISTRIB]
    \\ simp[wInst_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ simp[wStackLoad_append]
    \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧ _ t'`
    \\ simp[]
    \\ match_mp_tac (GEN_ALL wStackLoad_thm1)
    \\ `∃x. get_var (2*m') s = SOME (Word x)` by
        (fs[word_exp_def,get_var_def,LET_THM]>>
         qpat_x_assum`_ = SOME _`mp_tac >>
         BasicProvers.TOP_CASE_TAC \\ simp[]
         \\ imp_res_tac the_words_EVERY_IS_SOME_Word
         \\ fs[])
    \\ asm_exists_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ simp[Abbr`kont`]
    \\ conj_tac \\ strip_tac
    \\ TRY (
      match_mp_tac wRegWrite1_thm1
      \\ simp[]
      \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def]
      \\ TRY (
        drule word_exp_thm1
        \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
                reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
                wordLangTheory.max_var_exp_def,list_max_def]
        \\ impl_tac
        >- (
          TRY (conj_tac >- metis_tac[])
          \\ rw[] \\ fs[TWOxDIV2] )
        \\ simp[] )
      \\ drule (GEN_ALL word_exp_thm2)
      \\ simp[wordLangTheory.every_var_exp_def]
      \\ disch_then drule
      \\ simp[]
      \\ NO_TAC)
    \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n3),tt) = (NONE,t') ∧ _ t'`
    \\ simp[]
    \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
    \\ `∃x. get_var (2*m'') s = SOME x` by
       (fs[word_exp_def,get_var_def,LET_THM]>>
         qpat_x_assum`option_CASE _ _ _ = SOME _`mp_tac >>
         BasicProvers.TOP_CASE_TAC \\ simp[]
         \\ imp_res_tac the_words_EVERY_IS_SOME_Word
         \\ fsrw_tac[DNF_ss][])
    \\ asm_exists_tac \\ simp[Abbr`tt`]
    \\ asm_exists_tac \\ simp[]
    \\ simp[Abbr`kont`]
    \\ conj_tac \\ strip_tac
    \\ match_mp_tac wRegWrite1_thm1
    \\ simp[]
    \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def]
    \\ gen_tac \\ strip_tac
    \\ TRY (
      drule word_exp_thm1
      \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
              reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
              wordLangTheory.max_var_exp_def,list_max_def]
      \\ impl_tac
      >- (
        TRY(conj_tac >- metis_tac[])
        \\ rw[] \\ fs[TWOxDIV2] )
      \\ simp[]
      \\ rw[]
      \\ pop_assum mp_tac
      \\ CHANGED_TAC(simp[stackSemTheory.word_exp_def])
      \\ simp[IS_SOME_EXISTS] \\ strip_tac
      \\ BasicProvers.CASE_TAC \\ fs[]
      \\ fs[wordLangTheory.word_op_def]
      \\ rveq
      \\ BasicProvers.FULL_CASE_TAC \\ fs[]
      \\ NO_TAC)
    \\ TRY (
      drule (GEN_ALL word_exp_thm3)
      \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
              reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
              wordLangTheory.max_var_exp_def,list_max_def]
      \\ disch_then drule
      \\ simp[EQ_MULT_LCANCEL]
      \\ NO_TAC)
    \\ TRY (
      drule (GEN_ALL word_exp_thm4)
      \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
              reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
              wordLangTheory.max_var_exp_def,list_max_def]
      \\ disch_then drule
      \\ simp[EQ_MULT_LCANCEL]
      \\ NO_TAC)
    \\ drule (GEN_ALL word_exp_thm5)
    \\ simp[wordLangTheory.every_var_exp_def]
    \\ disch_then drule
    \\ simp[EQ_MULT_LCANCEL]
    \\ simp_tac(srw_ss()++DNF_ss)[]
    \\ simp[]
    \\ strip_tac \\ simp[]
    \\ qmatch_asmsub_rename_tac`if v1 = v2 then k else k+1`
    \\ Cases_on`v1=v2`\\fs[]
    \\ rw[]
    \\ rpt(first_x_assum(qspec_then`v1`mp_tac)) \\ rw[]
    \\ drule (GEN_ALL word_exp_thm6)
    \\ simp[]
    \\ disch_then drule
    \\ simp[EQ_MULT_LCANCEL])
  >- (
    last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ fs[wordLangTheory.every_var_inst_def,wordLangTheory.max_var_inst_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ TRY(BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ strip_tac \\ rveq
    \\ fs[GSYM wordSemTheory.get_var_def]
    \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,LET_THM]
    \\ rveq
    \\ fs[GSYM LEFT_ADD_DISTRIB]
    \\ simp[wInst_def]
    \\ pairarg_tac \\ fs[]
    \\ TRY(pairarg_tac \\ fs[])
    \\ simp[wStackLoad_append]
    \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧ _ t'`
    \\ simp[]
    \\ match_mp_tac (GEN_ALL wStackLoad_thm1)
    \\ `∃x. get_var (2*m') s = SOME x` by
      (fs[word_exp_def,get_var_def,LET_THM]>>
       qpat_x_assum`option_CASE (the_words _) _ _ = SOME _`mp_tac >>
       BasicProvers.TOP_CASE_TAC \\ simp[]
       \\ imp_res_tac the_words_EVERY_IS_SOME_Word
       \\ fsrw_tac[DNF_ss][])
    \\ asm_exists_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ simp[Abbr`kont`]
    \\ TRY (
      conj_tac \\ strip_tac
      \\ match_mp_tac wRegWrite1_thm1
      \\ simp[]
      \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def]
      \\ TRY (
        drule word_exp_thm1
        \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
                reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
                wordLangTheory.max_var_exp_def,list_max_def]
        \\ impl_tac
        >- (
          TRY(conj_tac >- metis_tac[])
          \\ rw[] \\ fs[TWOxDIV2] )
        \\ simp[]
        \\ fs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def,state_rel_def])
      \\ drule (GEN_ALL word_exp_thm2)
      \\ simp[wordLangTheory.every_var_exp_def]
      \\ disch_then drule
      \\ simp[]
      \\ fs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def,state_rel_def]
      \\ fs[stackSemTheory.set_var_def]
      \\ NO_TAC)
    \\ simp[Abbr`l`]
    \\ TRY (
      qpat_x_assum`word_loc_CASE _ _ _ = SOME _`mp_tac
      \\ BasicProvers.TOP_CASE_TAC
      \\ strip_tac )
    \\ conj_tac \\ strip_tac
    \\ qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n1),tt) = (NONE,t') ∧ _ t'`
    \\ simp[]
    \\ match_mp_tac (GEN_ALL wStackLoad_thm2)
    \\ `∃x. get_var (2*m) s = SOME x` by
       (fs[word_exp_def,get_var_def,LET_THM]>>
         qpat_x_assum`option_CASE (the_words _) _ _ = SOME _`mp_tac >>
         BasicProvers.TOP_CASE_TAC \\ simp[]
         \\ imp_res_tac the_words_EVERY_IS_SOME_Word
         \\ fsrw_tac[DNF_ss][])
    \\ asm_exists_tac \\ simp[Abbr`tt`]
    \\ asm_exists_tac \\ simp[Abbr`l`]
    \\ simp[Abbr`kont`]
    \\ TRY (
      drule (GEN_ALL word_exp_thm1)
      \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
              reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
              wordLangTheory.max_var_exp_def,list_max_def]
      \\ simp[EQ_MULT_LCANCEL]
      \\ qpat_abbrev_tac`tt = set_var _ _ t`
      \\ `state_rel k f f' s tt lens` by simp[Abbr`tt`]
      \\ ONCE_REWRITE_TAC[CONJ_COMM]
      \\ disch_then (fn th => drule th >> mp_tac th)
      \\ pop_assum kall_tac
      \\ disch_then drule
      \\ impl_tac >- (rw[] \\ simp[TWOxDIV2])
      \\ strip_tac
      \\ impl_tac >- (rw[] \\ simp[TWOxDIV2])
      \\ strip_tac
      \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
      \\ simp[Abbr`tt`]
      \\ drule (GEN_ALL state_rel_get_var_imp)
      \\ disch_then drule \\ strip_tac
      \\ drule (GEN_ALL state_rel_get_var_imp2)
      \\ disch_then drule \\ strip_tac
      \\ conj_tac \\ strip_tac \\ fs[stackSemTheory.get_var_def]
      \\ `s.mdomain = t.mdomain ∧ s.memory = t.memory ∧ s.be = t.be` by ( fs[state_rel_def])
      \\ fs[stackSemTheory.mem_store_def,wordSemTheory.mem_store_def,wordSemTheory.mem_store_byte_aux_def]
      \\ rveq \\ simp[]
      \\ simp[set_var_with_memory]
      \\ BasicProvers.CASE_TAC \\ fs[]
      \\ TRY BasicProvers.CASE_TAC \\ fs[]
      \\ rveq \\ simp[]
      \\ simp[set_var_with_memory]
      \\ match_mp_tac state_rel_with_memory
      \\ simp[])
    \\ drule (GEN_ALL word_exp_thm2)
    \\ simp[DIV2_def,TWOxDIV2,wordLangTheory.every_var_exp_def,
            reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,
            wordLangTheory.max_var_exp_def,list_max_def]
    \\ simp[EQ_MULT_LCANCEL]
    \\ qpat_abbrev_tac`tt = stackSem$set_var (k+1) _ _`
    \\ `state_rel k f f' s tt lens` by simp[Abbr`tt`]
    \\ disch_then (fn th => drule th >> mp_tac th)
    \\ pop_assum kall_tac
    \\ disch_then drule
    \\ simp[Abbr`tt`]
    \\ simp[Once set_var_swap]
    \\ simp[set_var_cancel]
    \\ ntac 2 strip_tac
    \\ simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    \\ drule (GEN_ALL state_rel_get_var_imp)
    \\ disch_then drule \\ strip_tac
    \\ drule (GEN_ALL state_rel_get_var_imp2)
    \\ disch_then drule \\ strip_tac
    \\ conj_tac \\ strip_tac \\ fs[stackSemTheory.get_var_def]
    \\ TRY (simp[Once stackSemTheory.set_var_def] \\ CHANGED_TAC(simp[FLOOKUP_UPDATE]))
    \\ `s.mdomain = t.mdomain ∧ s.memory = t.memory ∧ s.be = t.be` by ( fs[state_rel_def])
    \\ fs[stackSemTheory.mem_store_def,wordSemTheory.mem_store_def,wordSemTheory.mem_store_byte_aux_def]
    \\ rveq \\ simp[]
    \\ BasicProvers.CASE_TAC \\ fs[]
    \\ TRY BasicProvers.CASE_TAC \\ fs[]
    \\ rveq \\ simp[]
    \\ simp[set_var_with_memory]
    \\ match_mp_tac state_rel_with_memory
    \\ simp[])
  >- ( (*FP*)
    qpat_x_assum`A=SOME s'` mp_tac>>
    TOP_CASE_TAC>>fs[wInst_def,evaluate_def,wordLangTheory.max_var_inst_def]>>
    (* Cases not interfering with normal registers *)
    TRY
      (simp[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>EVERY_CASE_TAC>>fs[]>>
      strip_tac>>
      imp_res_tac state_rel_get_fp_var>>
      fs[]>>metis_tac[state_rel_set_fp_var])>>
    (* Cases reading 1 register *)
    TRY
      (ntac 2 TOP_CASE_TAC >>fs[]>>
      strip_tac>>
      fs[wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      pop_assum sym_sub_tac >> rveq>>
      match_mp_tac wRegWrite1_thm1 >> fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
      imp_res_tac state_rel_get_fp_var>>
      fs[])
    (* FPMovToReg *)
    >-
      (every_case_tac>>fs[]
      >-
        (strip_tac>>
        fs[wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
        rw[]>>
        match_mp_tac wRegWrite1_thm1 >> fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
        imp_res_tac state_rel_get_fp_var>>
        fs[])
      >>
      fs[wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
      strip_tac>>
      (* This case is a little bit harder than the rest because it is the only one
         involving a double write
      *)
      rw[wRegWrite2_def]
      >-
        (rw[wRegWrite1_def]
        >-
          (fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
          imp_res_tac state_rel_get_fp_var>>fs[TWOxDIV2]>>
          simp[state_rel_set_var])
        >>
          (fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
          imp_res_tac state_rel_get_fp_var>>fs[TWOxDIV2]>>
          simp[state_rel_set_var]>>
          fs[state_rel_def]>>
          `∀v tt. get_var k (set_var m' v (tt:('a,'b,'c)stackSem$state)) =  get_var k tt` by
            (EVAL_TAC>>fs[lookup_insert])>>
          simp[set_var_def,stackSemTheory.set_var_def,wf_insert]>>
          CONJ_TAC>-
            metis_tac[]>>
          CONJ_TAC>-
            rfs[DROP_LUPDATE]>>
          rw[lookup_insert]>>fs[EVEN_DOUBLE,TWOxDIV2,FLOOKUP_UPDATE]
          >-
            fs[DROP_LUPDATE,LLOOKUP_LUPDATE]
          >-
            (first_x_assum drule>>rw[]>>
            fs[EVEN_EXISTS]>>rw[]>>fs[TWOxDIV2])
          >-
            (fs[DROP_LUPDATE,LLOOKUP_LUPDATE]>>
            first_x_assum drule>>rw[]>>
            fs[EVEN_EXISTS]>>rw[]>>fs[TWOxDIV2])
          >-
            metis_tac[]))
      >>
        (rw[wRegWrite1_def]
        >-
          (fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
          imp_res_tac state_rel_get_fp_var>>fs[TWOxDIV2]>>
          simp[state_rel_set_var]>>
          fs[state_rel_def]>>
          simp[set_var_def,stackSemTheory.set_var_def,wf_insert]>>
          CONJ_TAC>-
            metis_tac[]>>
          CONJ_TAC>-
            rfs[DROP_LUPDATE]>>
          rw[lookup_insert]>>fs[EVEN_DOUBLE,TWOxDIV2,FLOOKUP_UPDATE]
          >-
            fs[DROP_LUPDATE,LLOOKUP_LUPDATE]
          >-
            (first_x_assum drule>>rw[]>>
            fs[EVEN_EXISTS]>>rw[]>>fs[TWOxDIV2])
          >-
            (fs[DROP_LUPDATE,LLOOKUP_LUPDATE]>>
            first_x_assum drule>>rw[]>>
            fs[EVEN_EXISTS]>>rw[]>>fs[TWOxDIV2])
          >-
            metis_tac[])
        >>
          (fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
          imp_res_tac state_rel_get_fp_var>>fs[TWOxDIV2]>>
          simp[state_rel_set_var]>>
          fs[state_rel_def]>>
          `∀v tt. get_var k (set_var (k+1) v (tt:('a,'b,'c)stackSem$state)) =  get_var k tt` by
            (EVAL_TAC>>fs[lookup_insert])>>
          simp[set_var_def,stackSemTheory.set_var_def,wf_insert,stackSemTheory.get_var_def,FLOOKUP_UPDATE]>>
          CONJ_TAC>-
            metis_tac[]>>
          CONJ_TAC>-
            rfs[DROP_LUPDATE]>>
          rw[lookup_insert]>>fs[EVEN_DOUBLE,TWOxDIV2,FLOOKUP_UPDATE]>>
          fs[DROP_LUPDATE,LLOOKUP_LUPDATE]
          >-
            (first_x_assum drule>>rw[])
          >-
            (first_x_assum drule>>rw[]>>
            fs[EVEN_EXISTS]>>rw[]>>fs[TWOxDIV2])
          >-
            metis_tac[])))
    >-
      (* FPMovFromReg *)
      (IF_CASES_TAC >> fs[]
      >-
        (every_case_tac>>fs[]>>strip_tac>>
        fs[wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
        pairarg_tac>>fs[]>>
        qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n1'),t) = (NONE,t') ∧ _ t'`>>
        simp[]>>
        match_mp_tac (GEN_ALL wStackLoad_thm1)>>
        rw[]>>
        asm_exists_tac>>fs[]>>
        asm_exists_tac>>fs[Abbr`kont`]>>rw[]>>
        fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
        >-
          (imp_res_tac state_rel_get_var_imp>>
          simp[stackSemTheory.get_var_def]>>
          fs[state_rel_set_fp_var])
        >>
          imp_res_tac state_rel_get_var_imp2>>
          simp[]>>
          fs[state_rel_set_fp_var])
      >-
        (every_case_tac>>fs[]>>strip_tac>>
        pairarg_tac>>fs[]>>
        pairarg_tac>>fs[]>>
        simp[wStackLoad_append]>>
        qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l (kont n1'),t) = (NONE,t') ∧ _ t'`>>
        simp[]>>
        match_mp_tac (GEN_ALL wStackLoad_thm1)>>
        fs[wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]>>
        rw[]>>
        asm_exists_tac>>fs[]>>
        asm_exists_tac>>fs[Abbr`kont`]>>rw[]
        >-
          (qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n2),tt) = (NONE,t') ∧ _ t'`>>
          simp[]>>
          match_mp_tac (GEN_ALL wStackLoad_thm2)>>
          asm_exists_tac>>fs[]>>
          asm_exists_tac>>unabbrev_all_tac>>rw[]>>
          fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
          >-
            (imp_res_tac state_rel_get_var_imp>>
            simp[stackSemTheory.get_var_def]>>
            fs[state_rel_set_fp_var])
          >>
            `∀v. get_var m (set_var (k+1) v t) = get_var m t` by
              (rw[]>>EVAL_TAC>>rw[])>>
            imp_res_tac state_rel_get_var_imp>>
            imp_res_tac state_rel_get_var_imp2>>
            simp[stackSemTheory.get_var_def]>>
            fs[state_rel_set_fp_var])
        >>
          qho_match_abbrev_tac`∃t'. evaluate (wStackLoad l' (kont n2),tt) = (NONE,t') ∧ _ t'`>>
          simp[]>>
          match_mp_tac (GEN_ALL wStackLoad_thm2)>>
          asm_exists_tac>>fs[]>>
          asm_exists_tac>>unabbrev_all_tac>>rw[]>>
          fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
          imp_res_tac state_rel_get_var_imp>>
          imp_res_tac state_rel_get_var_imp2>>
          simp[stackSemTheory.get_var_def]>>
          simp[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
          simp[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
          match_mp_tac state_rel_set_fp_var>>
          simp[GSYM stackSemTheory.set_var_def]))
    >>
      every_case_tac>>fs[stackSemTheory.evaluate_def,stackSemTheory.inst_def]>>
      imp_res_tac state_rel_get_fp_var>>
      rw[]>>fs[state_rel_set_fp_var])
QED

Theorem set_store_set_var:
   stackSem$set_store a b (set_var c d e) = set_var c d (set_store a b e)
Proof
  EVAL_TAC
QED

Theorem state_rel_set_store:
   state_rel k f f' s t lens ∧ v ≠ Handler ⇒
   state_rel k f f' (set_store v x s) (set_store v x t) lens
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
val get_vars_fromList2_eq = Q.prove(`
    get_vars (GENLIST (λx. 2*x) (LENGTH args)) s = SOME x ∧
    lookup n (fromList2 x) = SOME y ⇒
    lookup n s.locals = SOME y`,
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
    simp[]);

(*For returning calls*)
val get_vars_fromList2_eq_cons = Q.prove(`
    get_vars (GENLIST (λx. 2*(x+1)) (LENGTH args)) s = SOME x ∧
    lookup n (fromList2 (Loc x3 x4::x)) = SOME y ∧ n ≠ 0 ⇒
    lookup n s.locals = SOME y`,
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
  fs[EVEN_MOD2]>>simp[])

val lookup_fromList2_prefix = Q.prove(`
  ∀x z y.
  IS_PREFIX z x ∧
  lookup n (fromList2 x) = SOME y ⇒
  lookup n (fromList2 z) = SOME y`,
  fs[lookup_fromList2,lookup_fromList]>>rw[]>>
  imp_res_tac IS_PREFIX_LENGTH >- DECIDE_TAC>>
  fs[IS_PREFIX_APPEND]>>
  fs[EL_APPEND1])

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

val evaluate_wStackLoad_wReg1 = Q.prove(`
  wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,'a word list # 'c,'ffi)state) = SOME (Word c) ∧
  state_rel k f f' s t lens ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel k f f' s t' lens ∧
  r' ≠ k+1 ∧
  get_var r' t' = SOME (Word c)`,
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]>-
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
  fs[TWOxDIV2])

val evaluate_wStackLoad_clock = Q.prove(`
  ∀x t.
  evaluate(wStackLoad x Skip,t with clock:= clk) =
  (FST (evaluate(wStackLoad x Skip,t)),
   (SND (evaluate(wStackLoad x Skip,t))) with clock:=clk)`,
  Induct>>fs[wStackLoad_def,FORALL_PROD,stackSemTheory.evaluate_def,LET_THM]>>rw[])

val evaluate_wStackLoad_wRegImm2 = Q.prove(`
  wRegImm2 ri (k,f,f') = (x,r') ∧
  (case ri of Reg r => EVEN r | _ => T) ∧
  get_var_imm ri (s:('a,'a word list # 'c,'ffi)state) = SOME (Word c) ∧
  state_rel k f f' s t lens ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip, t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  get_var_imm r' t' = SOME(Word c) ∧
  (∀r. r ≠ k+1 ⇒ get_var r t' = get_var r t) ∧
  state_rel k f f' s t' lens`,
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
  fs[TWOxDIV2])

val evaluate_call_dest_clock = Q.prove(`
  call_dest dest args (k,f,f') = (q0,dest') ⇒
  evaluate(q0,t with clock := clk) =
  (FST(evaluate(q0,t:('a,'c,'ffi)stackSem$state)),
   (SND(evaluate(q0,t))) with clock := clk)`,
  Cases_on`dest`>>fs[call_dest_def,LET_THM]>>rw[]>>
  simp[stackSemTheory.evaluate_def]>>
  pairarg_tac>>fs[]>>rveq>>fs[evaluate_wStackLoad_clock])

val evaluate_wLive_clock = Q.prove(`
  ∀x t q bs bs'.
  wLive x bs kf = (q,bs') ⇒
  evaluate(q, t with clock:= clk) =
  (FST (evaluate(q,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(q,t)) with clock:=clk))`,
  PairCases_on`kf`>>fs[wLive_def,LET_THM]>>rw[]
  >-
    simp[stackSemTheory.evaluate_def]
  >>
    pairarg_tac>>fs[]>>rveq>>
    simp[stackSemTheory.evaluate_def,FORALL_PROD,stackSemTheory.inst_def,stackSemTheory.assign_def,stackSemTheory.set_var_def,stackSemTheory.word_exp_def,empty_env_def,stackSemTheory.get_var_def]>>
    EVERY_CASE_TAC>>fs[])

val state_rel_IMP_LENGTH = Q.prove(`
  state_rel k f f' s t lens ⇒
  LENGTH lens = LENGTH s.stack`,
  fs[state_rel_def,stack_rel_def,LET_THM]>>rw[]>>
  metis_tac[abs_stack_IMP_LENGTH])

val evaluate_stack_move = Q.prove(`
  ∀n tar t offset.
  t.use_stack ∧
  t.stack_space + tar + n + offset ≤ LENGTH t.stack ∧
  n ≤ offset
  ⇒
  ∃t'.
  evaluate(stack_move n tar offset k Skip, t) = (NONE,t') ∧
  t' = t with <|stack:=t'.stack; regs:=t'.regs|> ∧
  (*All regs fixed except k*)
  (∀i. i ≠ k ⇒ get_var i t' = get_var i t) ∧
  (*Unnecessary*)
  LENGTH t.stack = LENGTH t'.stack ∧
  (*Rest of stack is unchanged*)
  DROP (t'.stack_space+tar+n) t'.stack =
  DROP (t.stack_space+tar+n) t.stack ∧
  (*Copying the first frame*)
  let stack = DROP (t'.stack_space+tar) t'.stack in
  ∀x. x < n ⇒
  EL x stack = EL (x+offset) stack`,
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
    simp[EL_DROP,EL_LUPDATE]>>IF_CASES_TAC
    >-
      simp[]>>
    fs[LET_THM]>>
    first_x_assum(qspec_then`x-1` mp_tac)>>
    simp[EL_DROP])

val evaluate_stack_move_seq = Q.prove(`
  ∀a b c d prog (t:('a,'c,'ffi)stackSem$state).
  evaluate (stack_move a b c d prog,t) =
  evaluate (Seq prog (stack_move a b c d Skip),t)`,
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
    rpt IF_CASES_TAC>>fs[]);

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

val pop_env_ffi = Q.prove(`
  pop_env s = SOME s' ⇒
  s.ffi = s'.ffi`,
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[state_component_equality]);

val stack_rel_DROP_NONE = Q.prove(`
  stack_rel k whandler (StackFrame l NONE::wstack) shandler sstack len bs (f'::lens) ⇒
  stack_rel k whandler wstack shandler (DROP (f'+1) sstack) len bs lens`,
  simp[stack_rel_def]>>rw[]>>
  Cases_on`sstack`>>fs[abs_stack_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
  rpt (TOP_CASE_TAC>>simp[])>>
  rw[]>>fs[stack_rel_aux_def]>>
  qpat_x_assum`P ⇒A=B` mp_tac>>
  simp[]>>
  `SUC (LENGTH wstack) - (whandler+1) = SUC(LENGTH wstack - (whandler +1))` by DECIDE_TAC>>
  simp[]>>rw[]>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[LASTN_CONS]);

val stack_rel_DROP_SOME = Q.prove(`
  stack_rel k whandler (StackFrame l (SOME (whandler',b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  stack_rel k whandler' wstack (SOME(EL 2 sstack)) (DROP (f'+4) sstack) len bs lens`,
  simp[stack_rel_def]>>rw[]>>
  Cases_on`sstack`>>fs[abs_stack_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
  rpt (TOP_CASE_TAC>>simp[])>>
  rw[]>>fs[stack_rel_aux_def]>>
  qpat_x_assum`P ⇒A=B` mp_tac>>
  simp[]>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[]);

val LAST_GENLIST_evens = Q.prove(`
  n ≠ 0 ⇒
  let reg = LAST (GENLIST (λx. 2 * (x+1)) n) in
  reg ≠ 0 ∧ EVEN reg`,
  Cases_on`n`>>
  simp[LAST_EL,GENLIST_CONS]>>
  `0 < 2n` by DECIDE_TAC>>
  metis_tac[EVEN_MOD2,MULT_COMM,MOD_EQ_0]);

val stack_rel_cons_LEN_NONE = Q.prove(`
  stack_rel k whandler (StackFrame l NONE::wstack) shandler sstack len bs (f'::lens) ⇒
  f'+1 ≤ LENGTH sstack`,
  simp[stack_rel_def]>>Cases_on`sstack`>>simp[abs_stack_def]>>
  rpt TOP_CASE_TAC>>simp[])

val stack_rel_cons_LEN_SOME = Q.prove(`
  stack_rel k whandler (StackFrame l (SOME(a,b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  f'+4 ≤ LENGTH sstack`,
  simp[stack_rel_def]>>Cases_on`sstack`>>simp[abs_stack_def]>>
  rpt TOP_CASE_TAC>>simp[]);

val DROP_SUB = Q.prove(`
  a ≤ LENGTH ls ∧ b ≤ a ⇒
  DROP (a-b) ls = (DROP(a-b) (TAKE a ls))++ DROP a ls`,
  rw[]>>
  Q.ISPECL_THEN[`a`,`ls`] mp_tac(GSYM TAKE_DROP)>>
  disch_then SUBST_ALL_TAC>>
  simp[GSYM DROP_APPEND1]);

val DROP_SUB2 = Q.prove(`
  ∀a ls b.
  b ≤ a ∧
  a = LENGTH ls ⇒
  ∃rest.
  DROP (a-b) ls = rest ∧ LENGTH rest = b`,
  Induct>>
  fs[]>>rw[]>>
  simp[]);

val evaluate_PushHandler = Q.prove(`
  3 ≤ t.stack_space ∧
  state_rel k 0 0 (push_env x' NONE s with locals:=LN) t (f'::lens) ∧
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
  state_rel k 0 0 (push_env x' (SOME (x''0,x''1:'a wordLang$prog,x''2,x''3)) s with locals:=LN) t' (f'::lens)`,
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
  fs[stack_rel_def]>>
  CONJ_TAC>-
    fs[sorted_env_def]>>
  simp[DROP_LUPDATE]>>
  `∃a b c ts. DROP (t.stack_space-3) t.stack = a::b::c::DROP t.stack_space t.stack` by
    (simp[DROP_SUB]>>
    simp[TAKE_TAKE_MIN,LENGTH_TAKE,DROP_LENGTH_NIL_rwt]>>
    imp_res_tac (DROP_SUB2|>INST_TYPE[alpha|->``:'a word_loc``])>>
    pop_assum(qspec_then`TAKE t.stack_space t.stack` mp_tac)>>
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
  >-
    (*stackLang handler needs to be updated*)
    (simp[handler_val_def,LASTN_LENGTH_ID2,LASTN_CONS]>>
    qpat_x_assum`LENGTH x'' =LENGTH s.stack` sym_sub_tac>>
    simp[LASTN_LENGTH_ID]>>
    imp_res_tac abs_stack_to_stack_LENGTH>>
    simp[]>>
    qpat_x_assum `A=h'::t'` (mp_tac o Q.AP_TERM `LENGTH`)>>
    simp[])
  >>
  fs[stack_rel_aux_def]>>
  rw[]>>
  qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
  simp[]>>
  `SUC (LENGTH s.stack) - (s.handler+1) = SUC(LENGTH s.stack - (s.handler+1))` by DECIDE_TAC>>
  fs[handler_val_def,GSYM ADD1]>>
  rw[]>>
  simp[LASTN_CONS])|> INST_TYPE[beta|->alpha];

val evaluate_PushHandler_clock = Q.prove(`
  ∀(t:('a,'c,'ffi)stackSem$state).
  let prog = PushHandler a b (k,f:num,f':num) in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))`,
  simp[PushHandler_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
       stackSemTheory.word_exp_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,stackSemTheory.set_store_def]>>rw[]>>
  TOP_CASE_TAC>>fs[empty_env_def,FLOOKUP_UPDATE]>>
  rpt(TOP_CASE_TAC>>fs[]))|>SIMP_RULE arith_ss [LET_THM];

val evaluate_PopHandler_clock = Q.prove(`
  ∀(t:('a,'c,'ffi)stackSem$state).
  let prog = PopHandler (k,f:num,f':num) Skip in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))`,
  simp[stackSemTheory.evaluate_def,PopHandler_def,stackSemTheory.set_var_def,stackSemTheory.get_var_def,stackSemTheory.set_store_def,empty_env_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]);

val evaluate_PopHandler_seq = Q.prove(`
  ∀prog (t:('a,'c,'ffi)stackSem$state).
  evaluate (PopHandler (k,f,f') prog,t) =
  evaluate (Seq (PopHandler (k,f,f') Skip) prog,t)`,
  simp[stackSemTheory.evaluate_def,PopHandler_def]>>
  rw[]>>EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]);

val word_cmp_Word_Word = Q.prove(
  `word_cmp cmp (Word c) (Word c') = SOME (word_cmp cmp c c')`,
  Cases_on `cmp`
  \\ rw [labSemTheory.word_cmp_def,asmTheory.word_cmp_def]);

val ALL_DISTINCT_MEM_toAList_fromAList = Q.prove(`
  ALL_DISTINCT (MAP FST ls) ⇒
  (MEM x (toAList (fromAList ls)) ⇔
  MEM x ls)`,
  Cases_on`x`>>fs[MEM_toAList,lookup_fromAList]>>
  rw[]>>
  metis_tac[ALOOKUP_MEM,ALOOKUP_ALL_DISTINCT_MEM]);

val state_rel_code_domain = Q.prove(`
  state_rel k f f' s t lens ⇒
  domain s.code ⊆ domain t.code`,
  strip_tac>>fs[state_rel_def,SUBSET_DEF,domain_lookup,EXISTS_PROD]>>
  metis_tac[]);

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
   ∀k ps bm ps' bm'.
    compile_word_to_stack k ps bm = (ps',bm') ⇒ MAP FST ps' = MAP FST ps
Proof
  recInduct compile_word_to_stack_ind
  \\ rw[compile_word_to_stack_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
QED

val compile_word_to_stack_IMP_ALOOKUP = Q.prove(
  `!code k bs progs bitmaps n arg_count word_prog x.
      compile_word_to_stack k code bs = (progs,bitmaps) /\
      ALOOKUP code n = SOME (arg_count,word_prog) /\
      bitmaps ≼ x ⇒
      ∃bs bs2 stack_prog.
        compile_prog word_prog arg_count k bs = (stack_prog,bs2) ∧
        bs2 ≼ x ∧ ALOOKUP progs n = SOME stack_prog`,
  Induct \\ fs [] \\ strip_tac \\ PairCases_on `h`
  \\ fs [compile_word_to_stack_def] \\ rw [] \\ fs [LET_THM]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  THEN1 (asm_exists_tac \\ fs [] \\ imp_res_tac IS_PREFIX_TRANS)
  \\ first_x_assum match_mp_tac
  \\ asm_exists_tac \\ fs []);

val Install_tac =
      drule (GEN_ALL state_rel_get_var_imp)
      \\ `1 < k ∧ 2 < k` by fs[state_rel_def]
      \\ disch_then imp_res_tac
      \\ TRY(drule (GEN_ALL state_rel_get_var_imp2)
             \\ disch_then imp_res_tac)
      \\ rfs[]
      \\ simp[stackSemTheory.evaluate_def,stackSemTheory.get_var_def]
      \\ `t.data_buffer = s.data_buffer` by fs[state_rel_def]
      \\ `t.code_buffer = s.code_buffer` by fs[state_rel_def]
      \\ fs[stackSemTheory.set_var_def,FLOOKUP_UPDATE] \\ rfs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ `t.use_stack` by fs[state_rel_def]
      \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ qhdtm_assum`state_rel`(fn th =>
           let val conjs = th |> REWRITE_RULE[state_rel_def] |> CONJUNCTS  in
           map_every assume_tac (filter ((fn tm => is_eq tm andalso is_pabs(rhs tm)) o concl) conjs) end)
      \\ fs[]
      \\ Cases_on`cfg` \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ rveq
      \\ Cases_on`progs` >- fs[compile_word_to_stack_def]
      \\ Cases_on`progs'` >- (PairCases_on`h` \\ fs[compile_word_to_stack_def] \\ rpt(pairarg_tac\\fs[]))
      \\ fs[]
      \\ PairCases_on`h` \\ PairCases_on`h'` \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ fs[shift_seq_def]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ fs[case_eq_thms]
      \\ rveq
      \\ `h0 = h'0` by (fs[compile_word_to_stack_def] \\ rpt(pairarg_tac \\ fs[]))
      \\ rveq
      \\ qpat_x_assum`compile_word_to_stack k progs _ = _`kall_tac
      \\ qmatch_assum_rename_tac`compile_word_to_stack k ps bm = (ps',bm')`
      \\ fs[state_rel_def]
      \\ conj_tac
      >- (
        qx_gen_tac`z`
        \\ last_assum(qspec_then`0`mp_tac)
        \\ last_x_assum(qspec_then`z+1`mp_tac)
        \\ simp[]
        \\ pairarg_tac \\ fs[]
        \\ rw[]
        \\ imp_res_tac compile_word_to_stack_isPREFIX
        \\ fs[]
        \\ pop_assum mp_tac
        \\ simp[IS_PREFIX_APPEND] \\ strip_tac
        \\ simp[DROP_LENGTH_NIL_rwt,DROP_APPEND] )
      \\ conj_tac
      >- (
        simp[domain_union,domain_fromAList]
        \\ imp_res_tac MAP_FST_compile_word_to_stack
        \\ rw[INSERT_UNION_EQ] )
      \\ conj_tac
      >- (
        fs[lookup_union,lookup_fromAList]
        \\ rpt gen_tac
        \\ reverse TOP_CASE_TAC
        >- (
          strip_tac \\ rveq
          \\ first_x_assum drule
          \\ strip_tac \\ fs[]
          \\ asm_exists_tac \\ fs[]
          \\ fs[IS_PREFIX_APPEND] )
        \\ strip_tac
        \\ imp_res_tac ALOOKUP_MEM
        \\ last_x_assum(qspec_then`0`mp_tac)
        \\ simp[EVERY_MEM]
        \\ strip_tac
        \\ res_tac \\ fs[]
        \\ drule compile_word_to_stack_IMP_ALOOKUP
        \\ disch_then drule
        \\ disch_then(qspec_then`bm'`mp_tac)
        \\ simp[] \\ strip_tac
        \\ asm_exists_tac \\ simp[]
        \\ conj_tac
        >- (
          match_mp_tac IS_PREFIX_TRANS
          \\ once_rewrite_tac[CONJ_COMM]
          \\ asm_exists_tac \\ simp[]
          \\ imp_res_tac compile_word_to_stack_isPREFIX
          \\ pop_assum mp_tac
          \\ simp[IS_PREFIX_APPEND] \\ strip_tac
          \\ simp[DROP_LENGTH_NIL_rwt,DROP_APPEND] )
        \\ CASE_TAC
        \\ fs[EXTENSION,domain_lookup]
        \\ last_x_assum(qspec_then`n`mp_tac)
        \\ simp[])
      \\ conj_tac >- simp[lookup_union]
      \\ conj_tac >- (
        fs[buffer_flush_def]
        \\ rveq \\ fs[] )
      \\ conj_tac >- ( Cases_on`t.bitmaps` \\ fs[] )
      \\ conj_tac >- (
        match_mp_tac wf_insert
        \\ fs[cut_env_def,case_eq_thms]
        \\ rveq \\ simp[] )
      \\ conj_tac >- (
        fs[stack_rel_def]
        \\ metis_tac[abs_stack_bitmaps_prefix] )
      \\ fs[lookup_insert]
      \\ rpt gen_tac
      \\ fs[cut_env_def,case_eq_thms]
      \\ rveq
      \\ fs[lookup_inter,case_eq_thms]
      \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
      \\ strip_tac \\ rveq \\ fs[]
      \\ fs[EVERY_MAP,EVERY_MEM,MEM_toAList,FORALL_PROD]
      \\ rpt(first_x_assum drule)
      \\ simp[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
      \\ strip_tac \\ strip_tac
      \\ rveq \\ fs[TWOxDIV2]
      \\ rfs[]

Theorem comp_correct:
   !(prog:'a wordLang$prog) (s:('a,'a word list # 'c,'ffi) wordSem$state) k f f' res s1 t bs lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel k f f' s t lens /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     get_labels (FST (comp prog bs (k,f,f'))) SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k /\
     SND (comp prog bs (k,f,f')) ≼ t.bitmaps ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (FST (comp prog bs (k,f,f')),t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events
       else
         case res of
         | NONE => state_rel k f f' s1 t1 lens
         (*lens might be wrong*)
         | SOME (Result _ y) => state_rel k 0 0 s1 t1 lens /\ FLOOKUP t1.regs 1 = SOME y
         | SOME (Exception _ y) => state_rel k 0 0 (push_locals s1) t1 (LASTN (s.handler+1) lens) /\ FLOOKUP t1.regs 1 = SOME y
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs[get_labels_def]
  THEN1 (* Skip *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw [])
  THEN1 (* Alloc *)
   (qexists_tac `0`
    \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `n = 2` by (fs [convs_def]) \\ rw []
    \\ `1 < k ∧ 1 ≠ k` by (fs [state_rel_def] \\ decide_tac) \\ res_tac
    \\ Cases_on `get_var 2 s` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ `t.use_alloc /\ (get_var 1 t = SOME (Word c))` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_x_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
    \\ Cases_on `cut_env names s.locals`
    THEN1 fs [wordSemTheory.alloc_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `cut_env names s.locals = SOME env`
    \\ Cases_on `wLive names bs (k,f,f')`
    \\ rename1 `wLive names bs (k,f,f') = (wlive_prog,bs1)`
    \\ Cases_on`1 ≤ f`
    THEN1
      (drule evaluate_wLive
      \\ impl_keep_tac
      THEN1
        (fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
        fs[GSYM toAList_domain,EVERY_MEM]>>
        fs[X_LE_DIV,reg_allocTheory.is_phy_var_def,LET_THM]>>
        rw[]>>res_tac>>DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ fs []
      \\ fs [stackSemTheory.evaluate_def,LET_THM]
      \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
      \\ Cases_on `alloc c t5` \\ fs []
      \\ rename1 `alloc c t5 = (res1,t1)` \\ fs []
      \\ drule alloc_IMP_alloc \\ impl_tac >- (fs[])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [] \\ Cases_on `res = NONE` \\ fs [])
    \\
      `f=0` by DECIDE_TAC>>
      `f' = 0` by fs[state_rel_def]>>
      fs[wLive_def]>>rveq>>fs[stackSemTheory.evaluate_def,LET_THM]>>
      fs[cut_env_def]>>
      `domain names = {}` by
        (CCONTR_TAC>>fs[]>>
        `∃x. x ∈ domain names` by fs[MEMBER_NOT_EMPTY]>>
        fs[convs_def,GSYM toAList_domain]>>
        assume_tac list_max_max>>
        fs[EVERY_MEM]>>res_tac>>
        fs[wordLangTheory.max_var_def]>>
        DECIDE_TAC)>>
      imp_res_tac alloc_IMP_alloc2>>
      ntac 14 (pop_assum kall_tac)>>
      fs[]>>
      Cases_on`res=NONE`>>fs[])
  THEN1 (* Move *) (
    simp[comp_def]
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
    \\ qmatch_abbrev_tac`_ _ _ _ a _ _ ⇒ _ _ _ _ b _ _`
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
    \\ metis_tac[parmove_preserves_moves])
  THEN1 (* Inst *)
    (fs[comp_def,wordSemTheory.evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq
    \\ qexists_tac`0` \\ simp[]
    \\ fs[convs_def,wordLangTheory.max_var_def]
    \\ drule evaluate_wInst \\ simp[]
    \\ disch_then drule
    \\ strip_tac \\ simp[])
  THEN1 (* Assign *)
    fs[flat_exp_conventions_def]
  THEN1 (* Get *) (
    fs[flat_exp_conventions_def]
    \\ fs[comp_def]
    \\ fs[wordSemTheory.evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq \\ simp[]
    \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ rw[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ match_mp_tac wRegWrite1_thm1
    \\ simp[stackSemTheory.evaluate_def]
    \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
    \\ fs[state_rel_def]
    \\ rfs[DOMSUB_FLOOKUP_THM])
  THEN1 (* Set *) (
    Cases_on`exp`>>fs[flat_exp_conventions_def]
    \\ fs[comp_def,LET_THM]
    \\ pairarg_tac \\ fs[]
    \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ simp[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ match_mp_tac (GEN_ALL wStackLoad_thm1)
    \\ fs[convs_def,wordLangTheory.every_var_exp_def]
    \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS,get_var_def]
    \\ rveq \\ fs[]
    \\ asm_exists_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ fs[GSYM wordSemTheory.get_var_def]
    \\ drule (GEN_ALL state_rel_get_var_imp)
    \\ disch_then drule \\ strip_tac
    \\ drule (GEN_ALL state_rel_get_var_imp2)
    \\ disch_then drule \\ strip_tac
    \\ simp[stackSemTheory.evaluate_def]
    \\ `t.use_store` by fs[state_rel_def]
    \\ simp[]
    \\ conj_tac \\ strip_tac \\ fs[stackSemTheory.get_var_def]
    \\ simp[set_store_set_var]
    \\ metis_tac[state_rel_set_store])
  THEN1 (* Store *)
    fs[flat_exp_conventions_def]
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [state_rel_def,wordSemTheory.dec_clock_def,stackSemTheory.dec_clock_def]
    \\ metis_tac[])
  THEN1 (* MustTerminate *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
    \\ Cases_on `s.termdep = 0` \\ fs [state_rel_def])
  THEN1 (* Seq *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
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
    \\ `SND (comp c1 bs (k,f,f')) ≼ t.bitmaps /\
        SND (comp c2 bs' (k,f,f')) ≼ t.bitmaps /\
        get_labels (FST (comp c1 bs (k,f,f'))) SUBSET loc_check t.code /\
        get_labels (FST (comp c2 bs' (k,f,f'))) SUBSET loc_check t.code` by
         (fs [] \\ imp_res_tac IS_PREFIX_TRANS \\ NO_TAC)
    \\ reverse (Cases_on `res' = NONE`) \\ fs [] \\ rpt var_eq_tac
    THEN1
     (first_x_assum drule \\ fs [] \\ rw [] \\ fs []
      \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
      \\ qexists_tac `ck` \\ fs [] \\ Cases_on `res` \\ fs []
      \\ Cases_on `res1 = NONE`
      \\ fs [stackSemTheory.evaluate_def,LET_THM])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ reverse (Cases_on `res1 = NONE`) \\ fs [] THEN1
     (qexists_tac `ck`
      \\ `good_dimindex (:'a)` by fs [state_rel_def]
      \\ fs [Halt_EQ_compile_result,stackSemTheory.evaluate_def,LET_THM]
      \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
      \\ `s.ffi = t.ffi` by fs [state_rel_def]
      \\ imp_res_tac evaluate_io_events_mono \\ fs []
      \\ imp_res_tac wordPropsTheory.evaluate_io_events_mono \\ fs []
      \\ rfs [] \\ fs [] \\ metis_tac [IS_PREFIX_TRANS])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ `SND (comp c2 bs' (k,f,f')) ≼ t1.bitmaps /\
        get_labels (FST (comp c2 bs' (k,f,f'))) SUBSET loc_check t1.code` by
         (fs[]>>imp_res_tac evaluate_mono>>fs[]>>
         metis_tac[IS_PREFIX_TRANS,SUBSET_TRANS,loc_check_SUBSET])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ fs [stackSemTheory.evaluate_def,LET_THM]
    \\ imp_res_tac stack_evaluate_add_clock_NONE \\ fs []
    \\ pop_assum (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ `s.handler = s1'.handler` by
      (Q.ISPECL_THEN [`c1`,`s`] assume_tac evaluate_stack_swap>>rfs[])>>
    fs[])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,wReg1_def]
    \\ `1 < k` by (fs [state_rel_def] \\ decide_tac) \\ res_tac
    \\ Cases_on `get_var n s` \\ fs []
    \\ Cases_on `get_var m s` \\ fs [] \\ rw []
    \\ Cases_on `x` \\ fs []
    \\ rename1 `get_var n s = SOME (Loc l1 l2)`
    \\ fs [wStackLoad_def] \\ fs [convs_def] \\ rw []
    \\ fs [reg_allocTheory.is_phy_var_def,wordLangTheory.max_var_def]
    \\ `t.use_stack /\ ~(LENGTH t.stack < t.stack_space + f) /\
        t.stack_space <= LENGTH t.stack` by
     (fs [state_rel_def] \\ decide_tac) \\ fs [LET_DEF]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    THEN1
     (`(get_var (n DIV 2) t = SOME (Loc l1 l2)) /\ (get_var 1 t = SOME x')` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_x_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
      \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF]
      \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
             fromList2_def,lookup_def]
      \\ conj_tac >- metis_tac[]
      \\ simp[wf_def,GSYM DROP_DROP])
    \\ `(t.stack_space + (f +k - (n DIV 2 + 1)) < LENGTH t.stack) /\
        (EL (t.stack_space + (f +k - (n DIV 2 + 1))) t.stack = Loc l1 l2) /\
        (get_var 1 t = SOME x')` by
     (fs [state_rel_def,get_var_def,LET_DEF]
      \\ res_tac \\ qpat_x_assum `!x.bbb` (K ALL_TAC) \\ rfs []
      \\ fs [stackSemTheory.get_var_def]
      \\ imp_res_tac LLOOKUP_TAKE_IMP
      \\ fs [LLOOKUP_DROP] \\ fs [LLOOKUP_THM] \\ rw[]
      \\ rfs[EL_TAKE])
    \\ fs [LET_DEF]
    \\ `(set_var k (Loc l1 l2) t).use_stack /\
        (set_var k (Loc l1 l2) t).stack_space <=
         LENGTH (set_var k (Loc l1 l2) t).stack` by
      fs [stackSemTheory.set_var_def]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    \\ fs [stackSemTheory.set_var_def,LET_DEF]
    \\ `k <> 1` by (fs [state_rel_def] \\ decide_tac)
    \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF,FLOOKUP_UPDATE]
    \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
           fromList2_def,lookup_def]
    \\ conj_tac >- metis_tac[]
    \\ simp[wf_def,GSYM DROP_DROP])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def]
    \\ `1 < k` by (fs [state_rel_def] \\ decide_tac)
    \\ qpat_x_assum `xxx = (aa,bb)` mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ pop_assum mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ qexists_tac `1`
    \\ rename1 `LASTN (s.handler + 1) s.stack =
          StackFrame l (SOME (h1,l3,l4))::rest`
    \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,jump_exc_def,
        stackSemTheory.find_code_def]
    \\ `lookup raise_stub_location t.code = SOME (raise_stub k)` by fs [state_rel_def] \\ fs []
    \\ pop_assum kall_tac
    \\ fs [stackSemTheory.dec_clock_def,raise_stub_def,wordLangTheory.max_var_def]
    \\ fs [state_rel_def,LET_DEF,push_locals_def,stackSemTheory.evaluate_def,LET_THM]
    \\ fs [DROP_DROP_EQ] \\ fs [stack_rel_def]
    \\ qpat_x_assum` A ⇒ B` mp_tac
    \\ impl_tac>-
      (`s.handler+1 ≤ LENGTH s.stack` by DECIDE_TAC>>
      imp_res_tac LASTN_HD>>
      ntac 3 (pop_assum sym_sub_tac)>>
      fs[is_handler_frame_def])
    \\ strip_tac
    \\ fs[LET_DEF,get_var_set_var]
    \\ fs [stackSemTheory.set_var_def]
    \\ `(LENGTH t.stack - handler_val (LASTN (s.handler+1) stack)) < dimword (:'a)`
         by decide_tac \\ fs []
    \\ `SORTED (\x y. FST x > FST y) l` by
      (imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [sorted_env_def])
    \\ `LENGTH t.stack - handler_val (LASTN (s.handler+1) stack) + 3 <= LENGTH t.stack` by
         (imp_res_tac stack_rel_raise \\ rfs[]
          \\ PairCases_on`payload`\\simp[handler_val_def])
    \\ IF_CASES_TAC \\ fs []
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,stackSemTheory.set_store_def]
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,push_locals_def,lookup_def]
    \\ imp_res_tac stack_rel_raise
    \\ pop_assum mp_tac
    \\ ntac 25 (pop_assum kall_tac)
    \\ strip_tac
    \\ rfs[]
    \\ fs [FLOOKUP_UPDATE]
    \\ rfs[wf_def]
    \\ conj_tac THEN1 metis_tac[]
    \\ conj_tac THEN1
     (fs [sorted_env_def] \\ Cases_on `env_to_list (fromAList l) (K I)`
      \\ imp_res_tac env_to_list_K_I_IMP \\ fs [])
    \\ conj_tac >-
       (rpt (qpat_x_assum`∀x. _`kall_tac)
       \\imp_res_tac LASTN_LENGTH_BOUNDS
       \\imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
       \\imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [])
    \\ rw[]
    >-
      (Cases_on`h1+1 = SUC (LENGTH rest)`>-
        fs[is_handler_frame_def]>>
      `h1 < LENGTH rest ∧
      SUC(LENGTH rest) - (h1+1) = SUC(LENGTH rest - (h1+1))` by DECIDE_TAC>>
      fs[]
      \\ rfs[]
      \\ sg `h1 <= LENGTH (LASTN (s.handler+1) stack)`
      \\ fs [LASTN_CONS]
      \\ imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
      >> simp[LASTN_CONS])
    >>
      fs [get_var_def,FLOOKUP_UPDATE,convs_def]>>
      `1 < k` by fs[state_rel_def]>>
      res_tac>>qpat_x_assum`!n.P` kall_tac>>rfs[])
  THEN1 (* If *)
    (fsrw_tac[][comp_def]>> pop_assum mp_tac>>
    LET_ELIM_TAC>>
    fs[evaluate_def]>>
    qpat_x_assum`A=(res,s1)`mp_tac>>
    ntac 2 TOP_CASE_TAC>>fs[]>>
    ntac 2 TOP_CASE_TAC>>fs[]>>
    simp[evaluate_wStackLoad_seq,wStackLoad_append]>>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_seq]>>
    ntac 3 (simp[Once stackSemTheory.evaluate_def])>>
    `EVEN r1 ∧ (case ri of Reg r => EVEN r | _ => T)` by
      (Cases_on`ri`>>
      fs[convs_def,EVEN_MOD2,reg_allocTheory.is_phy_var_def])>>
    simp[evaluate_wStackLoad_clock]>>
    drule evaluate_wStackLoad_wReg1>>
    fs[]>>strip_tac>>
    simp[]>>
    drule (GEN_ALL evaluate_wStackLoad_wRegImm2)>>
    disch_then (Q.ISPECL_THEN[`t'`,`s`,`lens`,`c'`] assume_tac)>>
    rfs[]>>
    fs[stackSemTheory.get_var_def,word_cmp_Word_Word]>>
    rw[]>>fs[get_labels_wStackLoad,get_labels_def]
    >-
      (first_x_assum(qspecl_then[`k`,`f`,`f'`,`t''`,`bs`,`lens`] mp_tac)>>
      impl_tac>-
       (fs[convs_def,wordLangTheory.max_var_def]>>
        imp_res_tac evaluate_mono>>fs[]>>
        metis_tac[IS_PREFIX_TRANS,SUBSET_TRANS,loc_check_SUBSET,subspt_trans,comp_IMP_isPREFIX])>>
      strip_tac>>qexists_tac`ck`>>rfs[])>>
    first_x_assum(qspecl_then[`k`,`f`,`f'`,`t''`,`bs'`,`lens`] mp_tac)>>
    impl_tac>-
      (fs[convs_def,wordLangTheory.max_var_def]>>
      imp_res_tac evaluate_mono>>fs[]>>
      metis_tac[IS_PREFIX_TRANS,SUBSET_TRANS,loc_check_SUBSET,subspt_trans,comp_IMP_isPREFIX])>>
    strip_tac>>qexists_tac`ck`>>rfs[])
  THEN1 (* LocValue *) (
    fs[comp_def,wordSemTheory.evaluate_def]
    \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ every_case_tac \\ fs[]
    \\ rw[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ match_mp_tac wRegWrite1_thm1
    \\ simp[stackSemTheory.evaluate_def]
    \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
    \\ imp_res_tac state_rel_code_domain
    \\ fs[SUBSET_DEF]
    \\ Cases_on `loc_check t.code (l1,0)` \\ fs []
    \\ fs [wRegWrite1_def]
    \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs [IN_DEF]
    \\ fs [loc_check_def,IN_DEF])
  THEN1 (* Install *) (
    fs[comp_def,wordSemTheory.evaluate_def]
    \\ fs[case_eq_thms]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ reverse(Cases_on`res`)
    >- ( fs[case_eq_thms] ) \\ fs[]
    \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ fs[TWOxDIV2]
    \\ rveq
    \\ fs[wStackLoad_append]
    \\ drule (GEN_ALL wStackLoad_thm1)
    \\ disch_then drule
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac
    \\ conj_tac \\ strip_tac
    \\ drule (GEN_ALL wStackLoad_thm2)
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac
    \\ (conj_tac >- simp[state_rel_set_var_k])
    \\ conj_tac \\ strip_tac \\ Install_tac)
  THEN1 (* CodeBufferWrite *) (
    fs[comp_def,wordSemTheory.evaluate_def]
    \\ fs[case_eq_thms]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ rveq \\ fs[]
    \\ fs[wStackLoad_append]
    \\ drule (GEN_ALL wStackLoad_thm1)
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac \\ fs[]
    \\ drule (GEN_ALL state_rel_get_var_imp)
    \\ disch_then imp_res_tac
    \\ drule (GEN_ALL state_rel_get_var_imp2)
    \\ disch_then imp_res_tac
    \\ `t.code_buffer = s.code_buffer ∧ t.data_buffer = s.data_buffer` by fs[state_rel_def]
    \\ conj_tac \\ strip_tac
    \\ drule (GEN_ALL wStackLoad_thm2)
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac \\ fs[]
    \\ conj_tac \\ strip_tac
    \\ fs[stackSemTheory.evaluate_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
    \\ fs[state_rel_def,FLOOKUP_UPDATE]
    \\ metis_tac[])
  THEN1 (* DataBufferWrite *) (
    fs[comp_def,wordSemTheory.evaluate_def]
    \\ fs[case_eq_thms]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ qexists_tac`0` \\ simp[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`NONE` \\ simp[]
    \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
    \\ rveq \\ fs[]
    \\ fs[wStackLoad_append]
    \\ drule (GEN_ALL wStackLoad_thm1)
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac \\ fs[]
    \\ drule (GEN_ALL state_rel_get_var_imp)
    \\ disch_then imp_res_tac
    \\ drule (GEN_ALL state_rel_get_var_imp2)
    \\ disch_then imp_res_tac
    \\ `t.code_buffer = s.code_buffer ∧ t.data_buffer = s.data_buffer` by fs[state_rel_def]
    \\ conj_tac \\ strip_tac
    \\ drule (GEN_ALL wStackLoad_thm2)
    \\ disch_then drule
    \\ disch_then ho_match_mp_tac \\ fs[]
    \\ conj_tac \\ strip_tac
    \\ fs[stackSemTheory.evaluate_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
    \\ fs[state_rel_def,FLOOKUP_UPDATE,buffer_write_def]
    \\ rveq \\ fs[]
    \\ metis_tac[])
  THEN1 (* FFI *)
   (fs [EVAL ``post_alloc_conventions k (FFI ffi_index ptr1 len1 ptr2 len2 names)``]
    \\ rw [] \\ fs [] \\ rw []
    \\ fs [wordSemTheory.evaluate_def]
    \\ qpat_x_assum `aaa = (res,s1)` mp_tac
    \\ rpt (ntac 2 (TOP_CASE_TAC \\ fs []))
    \\ fs [LET_DEF] \\ fs [] \\ rw [] \\ fs []
    \\ fs [comp_def,stackSemTheory.evaluate_def]
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
        s.memory = t.memory /\ s.ffi = t.ffi` by
          fs [state_rel_def] \\ fs [LET_THM]
    \\ qexists_tac `0` \\ fs []
    \\ fs [state_rel_def,LET_THM]
    \\ conj_tac THEN1 metis_tac[]
    \\ conj_tac
    >- ( fs[cut_env_def] \\ rveq \\ simp[wf_inter] )
    \\ ntac 3 strip_tac
    \\ fs [cut_env_def] \\ rpt var_eq_tac
    \\ fs [lookup_inter_alt]
    \\ fs [CONV_RULE (DEPTH_CONV ETA_CONV) (GSYM toAList_def)
           |> INST_TYPE [``:'a``|->``:unit``] |> SIMP_RULE (srw_ss()) []]
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,DIV_LT_X,FORALL_PROD,MEM_toAList]
    \\ fs [domain_lookup] \\ res_tac
    \\ `~(n < k * 2)` by decide_tac \\ fs [])
  \\ (* Call *)
     (* gets us quickly to the Call case *)
    (*reverse (recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [])*)
    simp [Once LET_DEF,comp_def]
    \\ pairarg_tac \\ fs []
    \\ Cases_on `ret` \\ fs []
    THEN1
     (goalStack.print_tac "comp_correct tail call case">>
     fsrw_tac[] [stackSemTheory.evaluate_def]
      \\ `¬bad_dest_args dest args` by
        (qpat_x_assum`A=(res,s1)` mp_tac \\
        fsrw_tac[][evaluate_def]\\ntac 2 (TOP_CASE_TAC>>fsrw_tac[][]))
       \\ fsrw_tac[] [LET_THM,wordSemTheory.evaluate_def]
      \\ qpat_x_assum `_ = (res,s1)` mp_tac
      \\ TOP_CASE_TAC THEN1 rw []
      \\ TOP_CASE_TAC THEN1 rw []
      \\ imp_res_tac call_dest_lemma
      \\ pop_assum(qspec_then`NONE` assume_tac) \\ fsrw_tac[][]
      \\ drule (GEN_ALL evaluate_add_clock) \\ fsrw_tac[] []
      \\ fsrw_tac[] [ADD_COMM,ADD_ASSOC,LET_THM]
      \\ disch_then kall_tac
      \\ `!n p ck. evaluate (SeqStackFree n p,t4 with clock := ck) =
                   evaluate (Seq (StackFree n) p,t4 with clock := ck)` by
       (rw [] \\ match_mp_tac evaluate_SeqStackFree
        \\ fsrw_tac[] [state_rel_def] \\ decide_tac)
      \\ `t4.clock = s.clock /\ t4.use_stack` by fsrw_tac[] [state_rel_def] \\ fsrw_tac[] []
      \\ fsrw_tac[] [stackSemTheory.evaluate_def]
      \\ Cases_on `LENGTH t4.stack <
           t4.stack_space + stack_free dest' (LENGTH args) (k,f,f')` \\ fsrw_tac[] []
      THEN1
       (fsrw_tac[] [stack_free_def]
        \\ Cases_on `dest'` \\ fsrw_tac[] [stack_arg_count_def]
        \\ fsrw_tac[] [state_rel_def,LET_DEF] \\ `F` by decide_tac)
      \\ TOP_CASE_TAC
      \\ reverse TOP_CASE_TAC THEN1 rw[]
      \\ last_x_assum(qspecl_then[`q`,`r`] assume_tac) \\ rfs[]
      \\ TOP_CASE_TAC \\ fsrw_tac[] []
      THEN1
       (rw [] \\ qexists_tac `0` \\ fsrw_tac[] [] \\ res_tac \\ fsrw_tac[] [state_rel_def])
      \\ TOP_CASE_TAC
      \\ TOP_CASE_TAC THEN1 rw []
      \\ strip_tac \\ rpt var_eq_tac \\ fsrw_tac[] [] \\ rfs []
      \\ res_tac \\ fsrw_tac[] [stackSemTheory.dec_clock_def]
      \\ fsrw_tac[] [compile_prog_def,LET_THM]
      \\ pairarg_tac \\ fsrw_tac[] []
      \\ rpt var_eq_tac \\ fsrw_tac[] [] \\ rfs[]
      \\ fsrw_tac[] [stackSemTheory.evaluate_def]
      \\ qpat_abbrev_tac `m = MAX (max_var r DIV 2 +1 - k) (LENGTH q - k)`
      \\ qpat_abbrev_tac `m' = (if _ then 0 else m + 1)` \\ rw []
      \\ Cases_on `t4.stack_space + stack_free dest' (LENGTH args) (k,f,f') <
             m' - (LENGTH q - k)` \\ fsrw_tac[] []
      THEN1 (* Hit stack limit case *)
       (fsrw_tac[] [state_rel_def]
        \\ fsrw_tac[] [compile_result_NOT_2]
        \\ imp_res_tac stackPropsTheory.evaluate_io_events_mono
        \\ imp_res_tac wordPropsTheory.evaluate_io_events_mono
        \\ fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
      \\ (fn g =>
           qabbrev_tac `t5 = ^((qexists_tac`0`
           \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t5)`) g
           |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g)
      \\ `state_rel k m' m (call_env q (dec_clock s)) t5 lens` by
           (fsrw_tac[][state_rel_def,LET_THM,Abbr`t5`,call_env_def,dec_clock_def]>>
            fsrw_tac[][stack_free_def]>>
            `stack_arg_count dest' (LENGTH args) k = (LENGTH q -k)` by
              (simp[stack_arg_count_def]>>
              qpat_x_assum`call_dest A B C =(q0,dest')` mp_tac>>
              qpat_x_assum`A=SOME(q,r)` mp_tac>>
              imp_res_tac get_vars_length_lemma>>
              Cases_on`dest`>>simp[find_code_def,call_dest_def,add_ret_loc_def]>>
              rpt TOP_CASE_TAC>>simp[]>>
              rw[]>>TRY pairarg_tac>>fsrw_tac[][]>>
              Cases_on`x`>>fsrw_tac[][]>>
              simp[])>>
            fsrw_tac[][wf_fromList2]>>
            qpat_abbrev_tac`len = LENGTH q -k`>>
            (*This seems too long for a trivial property..*)
            `len ≤ f` by
              (fsrw_tac[][convs_def]>>
              qpat_x_assum`args = A` SUBST_ALL_TAC>>
              imp_res_tac get_vars_length_lemma>>
              fsrw_tac[][wordLangTheory.max_var_def,LET_THM]>>
              fsrw_tac[][list_max_GENLIST_evens]>>
              `LENGTH q ≤ LENGTH args` by
                (qpat_x_assum`A=SOME(q,r)` mp_tac>>
                Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
                EVERY_CASE_TAC>>rw[]>>
                simp[LENGTH_FRONT])>>
              `LENGTH args -1 +1 < f' +1 +k` by simp[]>>
              Cases_on`f'`>-
                (fsrw_tac[][]>>
                `LENGTH args ≤ k` by DECIDE_TAC>>
                unabbrev_all_tac>>
                simp[])>>
              `LENGTH args -1 +1 -k < SUC n +1` by DECIDE_TAC>>
              fsrw_tac[][Abbr`len`]>>
              ntac 5 (pop_assum mp_tac)>>
              rpt (pop_assum kall_tac)>>
              DECIDE_TAC)>>
            `len ≤ m ∧ m ≤ m'` by
              (unabbrev_all_tac>>
              rpt (pop_assum kall_tac)>>
              rw[MAX_DEF]>>DECIDE_TAC)>>
            CONJ_TAC THEN1 metis_tac[]>>
            CONJ_TAC THEN1 decide_tac >>
            CONJ_TAC THEN1 (unabbrev_all_tac>>
              rpt (pop_assum kall_tac)>>
              rw [] \\ decide_tac) >>
            fsrw_tac[][DROP_DROP_EQ]>>
            CONJ_TAC THEN1 simp[]>>
            ntac 3 strip_tac>>
            imp_res_tac (GSYM domain_lookup)>>
            imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
            fsrw_tac[][wordPropsTheory.post_alloc_conventions_def,wordPropsTheory.call_arg_convention_def]>>
            `lookup n s.locals = SOME v` by
              (qpat_x_assum`args=A` SUBST_ALL_TAC>>
              imp_res_tac get_vars_fromList2_eq>>
              `isPREFIX q x` by
                (qpat_x_assum`A=SOME(q,r)` mp_tac>>
                Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
                EVERY_CASE_TAC>>rw[]>>
                Cases_on`x`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
              imp_res_tac lookup_fromList2_prefix>>
              metis_tac[])>>
            IF_CASES_TAC>-
              metis_tac[]>>
            fsrw_tac[][LLOOKUP_THM]>>
            Cases_on `m=0` \\ fsrw_tac[] []
            THEN1
             (fsrw_tac[] [markerTheory.Abbrev_def] \\ rpt var_eq_tac \\ fsrw_tac[] []
              \\ fsrw_tac[] [lookup_fromList2,lookup_fromList]
              \\ decide_tac) >>
            simp[Abbr`m'`]>>
            fsrw_tac[][lookup_fromList2,lookup_fromList]>>
            CONJ_ASM2_TAC
            >-
              (first_x_assum(qspecl_then[`n`,`v`] mp_tac)>>
              simp[EL_TAKE,EL_DROP]>>
              strip_tac>>
              qpat_x_assum`A=v` mp_tac>>
              simp[EL_TAKE,EL_DROP]>>
              disch_then sym_sub_tac>>
              AP_THM_TAC>>AP_TERM_TAC>>
              `(n DIV 2 +1) ≤ f+k` by
                (Cases_on`f'`>>fsrw_tac[][]>>
                DECIDE_TAC)>>
              simp[])>>
            unabbrev_all_tac>>
            simp[])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `bs'` mp_tac) \\ fsrw_tac[] []
      \\ impl_tac THEN1
        (CONJ_ASM1_TAC>-
          (qpat_x_assum`A=SOME(q,r)`mp_tac>>
          Cases_on`dest`>>
          fsrw_tac[][state_rel_def,wordSemTheory.find_code_def]>>
          rpt TOP_CASE_TAC>>
          rw[]>>
          metis_tac[])>>
        CONJ_TAC>-
          (qpat_x_assum`A=SOME(q,r)`mp_tac>>
          Cases_on`dest`>>
          fsrw_tac[][state_rel_def,wordSemTheory.find_code_def]>>
          rpt TOP_CASE_TAC>>
          rw[]>>
          metis_tac[])>>
        CONJ_TAC >-
         (qunabbrev_tac `t5` \\ simp_tac (srw_ss()) []
          \\ drule find_code_IMP_get_labels
          \\ fs [get_labels_def])>>
        CONJ_TAC>-
          (`EVEN (max_var r)` by
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
          fsrw_tac[][Abbr`t5`])
      \\ strip_tac \\ fsrw_tac[] []
      \\ qunabbrev_tac `t5` \\ fsrw_tac[] []
      \\ `ck + (s.clock - 1) = ck + s.clock - 1` by decide_tac
      \\ qexists_tac `ck` \\ fsrw_tac[] []
      \\ Cases_on `res1` \\ fsrw_tac[] []
      \\ fsrw_tac[] [EVAL ``(call_env q (dec_clock s)).handler``,
                     AC ADD_COMM ADD_ASSOC])
    \\ goalStack.print_tac "comp_correct returning call case(s)"
    \\ PairCases_on `x` \\ fs [LET_DEF]
    \\ pairarg_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ qhdtm_x_assum`wordSem$evaluate`mp_tac
    \\ simp[wordSemTheory.evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (Q.SPECL[`x`,`SOME(x0,x1,x2,x3,x4)`] (Q.GENL[`args'`,`ret`]call_dest_lemma)) \\ strip_tac \\rfs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]>>
    imp_res_tac evaluate_call_dest_clock>>
    pop_assum(qspec_then`t` assume_tac)>>
    first_assum (mp_tac o MATCH_MP ((GEN_ALL evaluate_wLive)|>REWRITE_RULE[GSYM AND_IMP_INTRO]))>>
    disch_then ((qspecl_then [`t4`,`s`,`lens`,`x'`] mp_tac) o REWRITE_RULE[AND_IMP_INTRO])>>
    simp[]>>
    impl_keep_tac>-
      (Cases_on`handler`>>TRY(PairCases_on`x''`)>>
      fsrw_tac[][convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
      fsrw_tac[][GSYM toAList_domain,EVERY_MEM]>>
      fsrw_tac[][X_LE_DIV,reg_allocTheory.is_phy_var_def,LET_THM]>>
      (rw[]>>res_tac
      >-
        DECIDE_TAC>>
      fsrw_tac[][wordLangTheory.max_var_def,LET_THM]
      >-
        (`∃n. MEM n (MAP FST (toAList x1))` by
        (CCONTR_TAC>>
        fsrw_tac[][toAList_domain]>>
        `domain x1 = {}` by
          fsrw_tac[][EXTENSION])>>
        res_tac>>
        qpat_x_assum`A<B:num` mp_tac>>
        qpat_abbrev_tac`ls = MAP FST A`>>
        simp[]>>
        strip_tac>>
        `list_max ls < 2*f' + 2*k` by
          (pop_assum mp_tac>>
          simp[MAX_DEF])>>
        Q.ISPEC_THEN `ls` assume_tac list_max_max>>
        fsrw_tac[][EVERY_MEM]>>
        `n < 2*f'+2*k` by
          (res_tac>>DECIDE_TAC)>>
        `n - 2*k < 2*f'` by DECIDE_TAC>>
        `f' ≠ 0` by DECIDE_TAC>>
        fsrw_tac[][state_rel_def])
      >>
      fsrw_tac[][comp_def,LET_THM]>>
      TRY(pairarg_tac>>fsrw_tac[][])>>
      imp_res_tac comp_IMP_isPREFIX>>
      metis_tac[evaluate_mono,IS_PREFIX_TRANS]))>>
    strip_tac>>
    imp_res_tac evaluate_wLive_clock>>
    pop_assum(qspec_then`t4` assume_tac)>>
    Cases_on`handler`>>simp[]
    >-
      (goalStack.print_tac"No handler case">>
      simp[stackSemTheory.evaluate_def]>>
      simp[StackArgs_def,evaluate_stack_move_seq]>>
      qpat_abbrev_tac`sargs = stack_arg_count A B C`>>
      simp[stackSemTheory.evaluate_def]>>
      (*Get through the eval of stack_move*)
      Cases_on`¬t5.use_stack`>-
        fs[state_rel_def]>>
      Cases_on`t5.stack_space < sargs`>>fs[] >-
        (fs[state_rel_def,compile_result_NOT_2]>>
        IF_CASES_TAC>>fs[]>-
          (simp[call_env_def]>>
          rw[]>>simp[])>>
        qpat_x_assum`res ≠ A` mp_tac>>
        rpt (pop_assum kall_tac)>>
        rpt(TOP_CASE_TAC>>fs[])>>
        fs[dec_clock_def]>>rw[]>>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
        fs [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
        metis_tac[pop_env_ffi,IS_PREFIX_TRANS])>>
      qabbrev_tac`t6 = t5 with <|stack_space :=t5.stack_space -sargs|>`>>
      `!ck. t5 with <|stack_space:=t5.stack_space - sargs; clock:=ck+t.clock|> = t6 with clock:=ck+t.clock` by
        simp[stackSemTheory.state_component_equality,Abbr`t6`]>>
      simp[evaluate_stack_move_clock]>>
      Q.ISPECL_THEN [`sargs`,`0n`,`t6`,`f`] mp_tac evaluate_stack_move>>
      impl_keep_tac>-
        (qpat_x_assum`s.clock ≠ 0 ⇒ P` kall_tac>>
        qpat_x_assum`∀a b c. P` kall_tac>>
        unabbrev_all_tac>>simp[]>>
        fsrw_tac[][state_rel_def,ADD_COMM]>>
        fsrw_tac[][convs_def]>>
        qpat_x_assum`args = A` SUBST_ALL_TAC>>
        fsrw_tac[][wordLangTheory.max_var_def,LET_THM]>>
        fsrw_tac[][list_max_GENLIST_evens2]>>
        `2*LENGTH args < 2*f'+2*k` by
          (qpat_x_assum`A<2*f' +2*k` mp_tac>>
          simp[MAX_DEF])>>
        `LENGTH args < f' +k` by DECIDE_TAC>>
        simp[stack_arg_count_def]>>
        TOP_CASE_TAC>>
        Cases_on`f'`>>fsrw_tac[][]>>
        DECIDE_TAC)>>
      strip_tac>>simp[]>>
      `find_code dest' (t'.regs \\0) t'.code = find_code dest' t4.regs t4.code` by
       (`subspt t4.code t'.code` by
         (unabbrev_all_tac>>
         fs[stackSemTheory.state_component_equality]>>
         imp_res_tac evaluate_mono>>fs[]>>
         metis_tac[evaluate_consts])>>
       Cases_on`dest'`>>fs[stackSemTheory.find_code_def]
       >-
         metis_tac[subspt_def,domain_lookup]
       >>
       qpat_x_assum`A=SOME stack_prog` mp_tac>>
       qpat_x_assum`A=(q0,INR y)` mp_tac>>
       Cases_on`dest`>>simp[call_dest_def]>>
       IF_CASES_TAC>>simp[]>>
       simp[wReg2_def]>>IF_CASES_TAC>>fs[]
       >-
         (`LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by
          (fs[convs_def]>>
          qpat_x_assum`args = A` SUBST_ALL_TAC>>
          `LENGTH args <> 0` by (strip_tac \\ fs[]) >>
          drule LAST_GENLIST_evens>>
          LET_ELIM_TAC>>simp[]>>
          Cases_on`reg`>>fs[]>>
          Cases_on`n`>>fs[]>>
          simp[ADD_DIV_RWT,ADD1])>>
         strip_tac>>rveq>>
         simp[DOMSUB_FLOOKUP_THM]>>
         fs[stackSemTheory.get_var_def,Abbr`t6`]>>
         qpat_x_assum`subspt _ _` mp_tac>>
         rpt (pop_assum kall_tac)>>
         EVERY_CASE_TAC>>rw[]>>
         metis_tac[subspt_def,domain_lookup])
       >>
         strip_tac>>rveq>>
         simp[DOMSUB_FLOOKUP_THM]>>
         fs[stackSemTheory.get_var_def,Abbr`t6`]>>
         qpat_x_assum`subspt _ _` mp_tac>>
         rpt (pop_assum kall_tac)>>
         EVERY_CASE_TAC>>rw[]>>
         metis_tac[subspt_def,domain_lookup])>>
      simp[]>>
      IF_CASES_TAC>-
        (rw[]>>qexists_tac`0`>>fs[state_rel_def]>>
        fs[Abbr`t6`,stackSemTheory.state_component_equality])>>
      `t.clock ≠ 0` by
        metis_tac[state_rel_def]>>
      fs [compile_prog_def,LET_THM]>>
      pairarg_tac>>fs[]>>
      rveq>>
      qpat_abbrev_tac `m = MAX (max_var r DIV 2 +1 - k) (LENGTH q - k)`>>
      qpat_abbrev_tac `m' = (if _ then 0 else m + 1)`>>
      simp[stackSemTheory.evaluate_def]>>
      `t'.use_stack` by
        fs[Abbr`t6`,stackSemTheory.state_component_equality]>>
      simp[stackSemTheory.set_var_def,stackSemTheory.dec_clock_def]>>
      Cases_on`t'.stack_space < m' - (LENGTH q-k)`>-
        (fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
        unabbrev_all_tac>>fsrw_tac[][stackSemTheory.state_component_equality]>>
        simp[]>>
        qpat_x_assum`res ≠ A` mp_tac>>
        rpt (pop_assum kall_tac)>>
        rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
        fsrw_tac[][dec_clock_def]>>rw[]>>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
        fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
        metis_tac[IS_PREFIX_TRANS,pop_env_ffi])>>
      simp[]>>
      qpat_abbrev_tac`word_state = call_env q st`>>
      qabbrev_tac`stack_state =
        t' with <|regs:=t'.regs|+(0,Loc x3 x4);
                  stack_space:=t'.stack_space - (m'-(LENGTH q-k));
                  clock:=t.clock-1|>`>>
      `state_rel k m' m word_state stack_state (f'::lens)` by
        (
        ntac 2 (qpat_x_assum`!a b c. P` kall_tac)>>
        `sargs = (LENGTH q -k)` by
          (simp[stack_arg_count_def,Abbr`sargs`]>>
          qpat_x_assum`call_dest A B C =(q0,dest')` mp_tac>>
          qpat_x_assum`A=SOME(q,r)` mp_tac>>
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
        fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
        simp[dec_clock_def,call_env_def,push_env_def]>>
        simp[env_to_list_def]>>
        fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality]>>
        `sargs ≤ m ∧ m ≤ m'` by
           (fs[markerTheory.Abbrev_def]
            \\ rveq \\ rw[MAX_DEF])>>
        CONJ_TAC>-
          simp[FUN_EQ_THM]>>
        CONJ_TAC>-
          metis_tac[]>>
        CONJ_TAC>- fs[push_env_def] >>
        CONJ_TAC>-
          metis_tac[]>>
        CONJ_TAC>-
          metis_tac[]>>
        CONJ_TAC>- fs[push_env_def] >>
        CONJ_ASM1_TAC>-
          DECIDE_TAC>>
        CONJ_TAC>-
          (simp_tac(srw_ss())[Abbr`m`,Abbr`m'`,MAX_DEF]
           \\ rpt(pop_assum kall_tac) \\ rw[] ) >>
        CONJ_TAC>-
          simp[wf_fromList2]>>
        fsrw_tac[][DROP_DROP_EQ]>>
        CONJ_TAC>-
          (fsrw_tac[][LET_THM]>>
          qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
          simp[push_env_def,env_to_list_def]>>
          qpat_x_assum`DROP A B = DROP C D` mp_tac>>
          simp[])>>
        ntac 3 strip_tac>>
        rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
        imp_res_tac (GSYM domain_lookup)>>
        imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
        fsrw_tac[][wordPropsTheory.post_alloc_conventions_def,wordPropsTheory.call_arg_convention_def]>>
        `isPREFIX q (Loc x3 x4::x)` by
           (qpat_x_assum`A=SOME(q,r)` mp_tac>>
           Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
           EVERY_CASE_TAC>>srw_tac[][]>>
           Cases_on`x`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
        imp_res_tac lookup_fromList2_prefix>>
        Cases_on`n=0`>-
          (fsrw_tac[][lookup_fromList2,lookup_fromList]>>
          simp[FLOOKUP_UPDATE])>>
        `lookup n s.locals = SOME v` by
         (qpat_x_assum`args=A` SUBST_ALL_TAC>>
         imp_res_tac get_vars_fromList2_eq_cons)>>
        fsrw_tac[][LET_THM]>>
        IF_CASES_TAC>-
          (`n DIV 2 ≠ 0 ∧ n DIV 2 ≠ k` by
            (Cases_on`n`>>simp[]>>
            Cases_on`n'`>>fsrw_tac[][]>>
            simp[ADD_DIV_RWT,ADD1])>>
          simp[FLOOKUP_UPDATE]>>
          fsrw_tac[][stackSemTheory.get_var_def]>>
          metis_tac[])>>
        `k ≤ LENGTH q` by (
          fsrw_tac[][lookup_fromList2,lookup_fromList]
          \\ rpt(qpat_x_assum`n DIV 2 < _`mp_tac)
          \\ qpat_x_assum`¬(n DIV 2 < _)`mp_tac
          \\ rpt(pop_assum kall_tac)
          \\ decide_tac) >>
        simp[LLOOKUP_THM] >>
        Cases_on `m=0` \\ fsrw_tac[] []
        THEN1
          (fsrw_tac[] [lookup_fromList2,lookup_fromList,Abbr`m'`]>>
           qpat_x_assum`¬(n DIV 2 < _)`mp_tac >>
           qpat_x_assum`(n DIV 2 < LENGTH _)`mp_tac >>
           qpat_x_assum`k ≤ _`mp_tac >>
           qpat_x_assum`_ ≤ k`mp_tac >>
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
        fsrw_tac[][LLOOKUP_THM,lookup_fromList2,lookup_fromList]>>
        `LENGTH q ≤ k+m` by (
          qpat_x_assum`_ ≤ m`mp_tac >>
          qpat_x_assum`sargs = _`mp_tac >>
          rpt(pop_assum kall_tac) >> rw[] ) >>
        reverse conj_tac >- (
          qpat_x_assum`n DIV 2 < _`mp_tac >>
          qpat_x_assum`n DIV 2 < _`mp_tac >>
          pop_assum mp_tac >>
          rpt(pop_assum kall_tac) >> rw[] ) >>
        `m+1 ≤ t5.stack_space` by ( simp[] ) >>
        qpat_x_assum`_ ≤ LENGTH t'.stack`mp_tac >>
        ntac 5 (pop_assum mp_tac) >>
        simp_tac(srw_ss()++ARITH_ss)[EL_DROP,EL_TAKE] >>
        rpt strip_tac >>
        first_x_assum(qspecl_then[`n`,`v`] mp_tac)>>
        qpat_x_assum`DROP A B = DROP C D` mp_tac>>
        `k < (n DIV 2+1)` by simp[]>>
        simp[EL_TAKE]>>
        disch_then sym_sub_tac>>
        simp[EL_DROP]>>
        strip_tac>>
        qpat_x_assum`!x. A ⇒ B = C` mp_tac>>
        rpt(qpat_x_assum`!n.P` kall_tac)>>
        simp[EL_DROP]>>
        disch_then(qspec_then`LENGTH q - (n DIV 2 +1)` mp_tac)>>
        simp[])>>
      Cases_on`evaluate(r,word_state)`>>fsrw_tac[][]>>
      first_x_assum(qspecl_then[`k`,`m'`,`m`,`stack_state`,`bs'''`,`(f'::lens)`] mp_tac)>>
      Cases_on`q' = SOME Error`>>fsrw_tac[][]>>
      impl_tac>-
        (CONJ_ASM1_TAC>-
          (qpat_x_assum`A=SOME(q,r)`mp_tac>>
          Cases_on`dest`>>
          fsrw_tac[][state_rel_def,find_code_def]>>
          rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
        CONJ_TAC>-
          (qpat_x_assum`A=SOME(q,r)`mp_tac>>
          Cases_on`dest`>>
          fsrw_tac[][state_rel_def,find_code_def]>>
          rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
        CONJ_TAC>-
         (qunabbrev_tac `stack_state` \\ simp_tac (srw_ss()) []
          \\ drule find_code_IMP_get_labels
          \\ fs [get_labels_def]
          \\ imp_res_tac evaluate_mono
          \\ fs[Abbr`t6`]
          \\ metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])>>
        CONJ_TAC>-
          (`EVEN (max_var r)` by
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
        fsrw_tac[][stackSemTheory.state_component_equality]>>
        metis_tac[evaluate_mono,IS_PREFIX_TRANS])>>
      strip_tac>>
      Cases_on`q'`>>simp[]>>
      Cases_on`x''`>>simp[]
      >-
        (IF_CASES_TAC>>fsrw_tac[][]>>
        Cases_on`pop_env r'`>>fsrw_tac[][]>>
        IF_CASES_TAC>>fsrw_tac[][]>>
        strip_tac>>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
        qpat_x_assum`if A then B else C` mp_tac>>
        IF_CASES_TAC>>fsrw_tac[][]
        >-
          (*the stackLang evaluation halts*)
          (rw[]>>
          qexists_tac`ck`>>
          fs[Abbr`stack_state`]>>
          `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
          fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
          metis_tac[IS_PREFIX_TRANS,pop_env_ffi,wordPropsTheory.evaluate_io_events_mono])>>
        strip_tac>>
        `state_rel k f f' (set_var x0 w0 x'') t1 lens ∧ x''.handler = s.handler` by
          (qpat_x_assum`!a b c d e f. P` kall_tac>>
          Q.ISPECL_THEN [`r`,`word_state`] assume_tac evaluate_stack_swap>>
          rfs[Abbr`word_state`]>>
          fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
          qpat_x_assum`pop_env A = B` mp_tac>>
          simp[pop_env_def]>>
          rpt(TOP_CASE_TAC>>fsrw_tac[][s_key_eq_def,s_frame_key_eq_def])>>
          pop_assum kall_tac>>
          strip_tac>>
          rveq>>fsrw_tac[][state_rel_def,set_var_def]>>
          CONJ_TAC>-
            metis_tac[evaluate_consts]>>
          CONJ_ASM1_TAC>-
            (fsrw_tac[][LET_THM]>>
            imp_res_tac stack_rel_cons_LEN_NONE>>
            fsrw_tac[][LENGTH_DROP]>>
            Cases_on`f'`>>fsrw_tac[][]>>
            simp[])>>
          CONJ_TAC>-
            simp[wf_insert,wf_fromAList]>>
          fsrw_tac[][LET_THM]>>
          CONJ_TAC>-
            (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
            metis_tac[stack_rel_DROP_NONE])>>
          ntac 2 strip_tac>>
          fsrw_tac[][lookup_insert,convs_def]>>
          IF_CASES_TAC>-
            simp[]>>
          strip_tac>>
          `n ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
          `n ∈ domain x1 ∧ n ∈ domain s.locals` by
            (fsrw_tac[][cut_env_def]>>
            `n ∈ domain x'` by rfs[]>>
            rveq>>
            fsrw_tac[][domain_inter])>>
          res_tac>>simp[]>>
          fsrw_tac[][domain_lookup]>>
          last_x_assum (qspecl_then [`n`,`v''`]mp_tac)>>
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
          `MEM (n,v) l` by metis_tac[ALOOKUP_MEM]>>
          `MEM (n DIV 2,v) (MAP_FST adjust_names l)` by
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
          `k + SUC n' - n DIV 2 = SUC (k+ SUC n' - (n DIV 2+1))` by DECIDE_TAC>>
          full_simp_tac(std_ss ++ ARITH_ss)[GSYM LENGTH_NIL] >>
          simp[EL_TAKE])>>
        imp_res_tac stackPropsTheory.evaluate_add_clock>>
        ntac 3 (pop_assum kall_tac)>>
        rveq>>fsrw_tac[][]>>
        first_x_assum(qspecl_then[`k`,`f`,`f'`,`t1`,`bs'`,`lens`] mp_tac)>>
        impl_tac>-
          (fsrw_tac[][convs_def]>>rw[]
          >-
            (fs [comp_def,get_labels_def] \\
            imp_res_tac evaluate_mono \\ fs[Abbr`stack_state`,Abbr`t6`] \\
            metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans])
          >-
            (qpat_x_assum`A<B:num` mp_tac>>
            simp[wordLangTheory.max_var_def])
          >>
            unabbrev_all_tac>>
            imp_res_tac evaluate_mono>>
            rpt (qpat_x_assum`isPREFIX _ _` mp_tac)>>
            simp[comp_def]>>
            metis_tac[IS_PREFIX_TRANS])>>
        rw[]>>
        qexists_tac`ck+ck'`>>
        fsrw_tac[][Abbr`stack_state`]>>
        first_x_assum(qspec_then`ck'` mp_tac)>>
        simp[]>>
        fsrw_tac[][ADD_COMM]>>
        pop_assum mp_tac>>
        simp[set_var_def])
      >-
        (*Exception*)
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
        `word_state.handler = s.handler` by
          simp[Abbr`word_state`,call_env_def,push_env_def,env_to_list_def,dec_clock_def]>>
        imp_res_tac state_rel_IMP_LENGTH>>
        Q.ISPECL_THEN [`r`,`word_state`] assume_tac evaluate_stack_swap>>rfs[]>>
        fs[push_env_def,env_to_list_def,LET_THM]>>
        `s.handler+1 ≤ LENGTH lens` by
          (*because it can't be the top frame of word_state, which is NONE*)
          (CCONTR_TAC>>
          `s.handler+1 =LENGTH s.stack+1` by DECIDE_TAC>>
          fs[Abbr`word_state`,call_env_def,dec_clock_def,LASTN_CONS]>>
          fs[LASTN_CONS_ID,GSYM ADD1])>>
        fs[LASTN_CONS])
      >>
        (*Timeout and Halt*)
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
        fs[state_rel_def]))
    >>
    goalStack.print_tac"Handler case">>
    PairCases_on`x''`>>simp[]>>
    pairarg_tac>>simp[stackSemTheory.evaluate_def]>>
    reverse(Cases_on`3 ≤ t5.stack_space`)>-
      (simp[PushHandler_def,stackSemTheory.evaluate_def]>>
      fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
      IF_CASES_TAC>>fsrw_tac[][]>-
        (simp[call_env_def]>>
        rw[]>>simp[])>>
      qpat_x_assum`res ≠ A` mp_tac>>
      rpt (pop_assum kall_tac)>>
      rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
      fsrw_tac[][dec_clock_def]>>rw[]>>
      imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
      fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
      metis_tac[pop_env_ffi,IS_PREFIX_TRANS])>>
    (* Needs to go in wordSem?*)
    drule evaluate_PushHandler>>
    simp[evaluate_PushHandler_clock]>>
    impl_tac THEN1 (
     fs [comp_def,get_labels_def] >>
     imp_res_tac evaluate_mono>>
     `loc_check t.code ⊆ loc_check t5.code` by
       metis_tac[subspt_trans,SUBSET_DEF,loc_check_SUBSET]>>
      fs[SUBSET_DEF,FORALL_PROD,IN_DEF])>>
    strip_tac>>
    simp[StackHandlerArgs_def,StackArgs_def,evaluate_stack_move_seq]>>
    simp[stackSemTheory.evaluate_def]>>
    `t'.use_stack` by fsrw_tac[][state_rel_def]>>fsrw_tac[][]>>
    qpat_abbrev_tac`sargs = stack_arg_count A B C`>>
    Cases_on`t'.stack_space < sargs`>-
      (simp[]>>
      fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
      IF_CASES_TAC>>fsrw_tac[][]>-
        (simp[call_env_def]>>
        rw[]>>simp[])>>
      qpat_x_assum`res ≠ A` mp_tac>>
      rpt (pop_assum kall_tac)>>
      rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
      fsrw_tac[][dec_clock_def]>>rw[]>>
      imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
      fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
      metis_tac[pop_env_ffi,IS_PREFIX_TRANS])>>
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
    `find_code dest' (t''.regs \\0) t''.code = find_code dest' t4.regs t4.code` by
       (`subspt t4.code t''.code` by
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
       >-
         (`LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by
          (fsrw_tac[][convs_def]>>
          qpat_x_assum`args = A` SUBST_ALL_TAC>>
          full_simp_tac std_ss [GSYM LENGTH_NIL] >>
          drule LAST_GENLIST_evens>>
          LET_ELIM_TAC>>simp[]>>
          Cases_on`reg`>>fsrw_tac[][]>>
          Cases_on`n`>>fsrw_tac[][]>>
          simp[ADD_DIV_RWT,ADD1])>>
         strip_tac>>rveq>>
         simp[DOMSUB_FLOOKUP_THM]>>
         fsrw_tac[][stackSemTheory.get_var_def,Abbr`t6`,FLOOKUP_UPDATE]>>
         qpat_x_assum`subspt _ _` mp_tac>>
         rpt (pop_assum kall_tac)>>
         every_case_tac>>fs[subspt_def]>>
         metis_tac[domain_lookup])
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
      (rw[]>>qexists_tac`0`>>fs[state_rel_def]>>
      fs[Abbr`t6`,stackSemTheory.state_component_equality])>>
    `t.clock ≠ 0` by
      metis_tac[state_rel_def]>>
    fsrw_tac[][compile_prog_def,LET_THM]>>
    pairarg_tac>>fsrw_tac[][]>>
    rveq>>
    qpat_abbrev_tac `m = MAX (max_var r DIV 2 +1 - k) (LENGTH q - k)`>>
    qpat_abbrev_tac `m' = (if _ then 0 else m + 1)`>>
    simp[stackSemTheory.evaluate_def]>>
    `t''.use_stack` by
      fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality]>>
    simp[stackSemTheory.set_var_def,stackSemTheory.dec_clock_def]>>
    Cases_on`t''.stack_space < m' - (LENGTH q-k)`>-
      (fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
      unabbrev_all_tac>>fsrw_tac[][stackSemTheory.state_component_equality]>>
      simp[]>>
      qpat_x_assum`res ≠ A` mp_tac>>
      ntac 90 (last_x_assum kall_tac)>>
      rpt(TOP_CASE_TAC>>fsrw_tac[][])>>
      fsrw_tac[][dec_clock_def]>>rw[]>>
      imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
      fsrw_tac[] [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,set_var_def]>>
      metis_tac[IS_PREFIX_TRANS,pop_env_ffi])>>
    simp[]>>
    qpat_abbrev_tac`word_state = call_env q st`>>
    qabbrev_tac`stack_state =
      t'' with <|regs:=t''.regs|+(0,Loc x3 x4);
                stack_space:=t''.stack_space - (m'-(LENGTH q-k));
                clock:=t.clock-1|>`>>
    `state_rel k m' m word_state stack_state (f'::lens)` by
      (ntac 3 (qpat_x_assum`!a b. P` kall_tac)>>
      `sargs = (LENGTH q -k)` by
        (simp[stack_arg_count_def,Abbr`sargs`]>>
        qpat_x_assum`call_dest A B C =(q0,dest')` mp_tac>>
        qpat_x_assum`A=SOME(q,r)` mp_tac>>
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
      fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
      fsrw_tac[][dec_clock_def,call_env_def,push_env_def,env_to_list_def,LET_THM]>>
      fsrw_tac[][Abbr`t6`,stackSemTheory.state_component_equality]>>
      `sargs ≤ m ∧ m ≤ m'` by
       (fs[markerTheory.Abbrev_def]
        \\ rveq \\ rw[MAX_DEF])>>
      fsrw_tac[][state_rel_def]>>
      CONJ_TAC>-
        simp[FUN_EQ_THM]>>
      CONJ_TAC>-
        fsrw_tac[][push_env_def,env_to_list_def,LET_THM]>>
      CONJ_ASM1_TAC>-
        DECIDE_TAC>>
      CONJ_TAC>-
        (simp_tac(srw_ss())[Abbr`m`,Abbr`m'`,MAX_DEF]
         \\ rpt(pop_assum kall_tac) \\ rw[] ) >>
      CONJ_TAC>-
        simp[wf_fromList2]>>
      fsrw_tac[][DROP_DROP_EQ]>>
      CONJ_TAC>-
        (qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
        simp[push_env_def,env_to_list_def]>>
        qpat_x_assum`DROP A B = DROP C D` mp_tac>>
        simp[])>>
      ntac 3 strip_tac>>
      rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
      imp_res_tac (GSYM domain_lookup)>>
      imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
      fsrw_tac[][wordPropsTheory.post_alloc_conventions_def,wordPropsTheory.call_arg_convention_def]>>
      `isPREFIX q (Loc x3 x4::x)` by
         (qpat_x_assum`A=SOME(q,r)` mp_tac>>
         Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
         EVERY_CASE_TAC>>rw[]>>
         Cases_on`x`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
      imp_res_tac lookup_fromList2_prefix>>
      Cases_on`n=0`>-
        (fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        simp[FLOOKUP_UPDATE])>>
      `lookup n s.locals = SOME v` by
       (qpat_x_assum`args=A` SUBST_ALL_TAC>>
       imp_res_tac get_vars_fromList2_eq_cons)>>
      fsrw_tac[][LET_THM]>>
      IF_CASES_TAC>-
        (`n DIV 2 ≠ 0 ∧ n DIV 2 ≠ k` by
          (Cases_on`n`>>simp[]>>
          Cases_on`n'`>>fsrw_tac[][]>>
          simp[ADD_DIV_RWT,ADD1])>>
        rw[FLOOKUP_UPDATE]>>
        fsrw_tac[][stackSemTheory.get_var_def,FLOOKUP_UPDATE]>>
        metis_tac[])>>
      `k ≤ LENGTH q` by (
        fsrw_tac[][lookup_fromList2,lookup_fromList]
        \\ rpt(qpat_x_assum`n DIV 2 < _`mp_tac)
        \\ qpat_x_assum`¬(n DIV 2 < _)`mp_tac
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
         qpat_x_assum`¬(n DIV 2 < _)`mp_tac >>
         qpat_x_assum`(n DIV 2 < k + _)`mp_tac >>
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
      qpat_x_assum`LENGTH t'.stack = _`(mp_tac o SYM) >>
      qpat_x_assum`_.stack_space ≤ LENGTH t''.stack`mp_tac >>
      simp_tac(srw_ss()++ARITH_ss)[LLOOKUP_THM,EL_TAKE,EL_DROP] >>
      ntac 4 strip_tac >>
      fsrw_tac[][lookup_fromList2,lookup_fromList] >>
      reverse conj_asm2_tac >- simp[] >>
      pop_assum mp_tac >>
      qpat_x_assum`¬(_ < _)`mp_tac >>
      qpat_x_assum`m + 1 ≤ _`mp_tac >>
      simp_tac(srw_ss()++ARITH_ss)[] >>
      ntac 3 strip_tac >>
     first_x_assum(qspecl_then[`n`,`v`] kall_tac)>>
     first_x_assum(qspecl_then[`n`,`v`] mp_tac)>>
     rpt(qpat_x_assum`!a b. P` kall_tac)>>
     fsrw_tac[][]>>
     simp[LLOOKUP_THM]>>
     `f+k - (n DIV 2 +1) < f` by simp[]>>
     fsrw_tac[][EL_TAKE]>>
     qpat_assum`∀x. A ⇒ EL B (DROP t5.stack_space t5.stack) = EL D E` mp_tac>>
     disch_then (qspec_then `f+k-(n DIV 2 +1)` mp_tac)>>
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
     first_x_assum (qspec_then`LENGTH q - (n DIV 2 +1)` mp_tac)>>
     impl_tac>- simp[]>>
     fs[EL_DROP]>>
     qpat_x_assum `t'.stack_space + 3 = t5.stack_space` mp_tac>>
     rpt(pop_assum kall_tac)>>
     rw[]>>
     `f' + k - n DIV 2 + 3 + t'.stack_space =
     f' + k + t5.stack_space - n DIV 2` by fs[]>>
     fs[])>>
    Cases_on`evaluate(r,word_state)`>>fsrw_tac[][]>>
    first_x_assum(qspecl_then[`k`,`m'`,`m`,`stack_state`,`bs'''`,`(f'::lens)`] mp_tac)>>
    Cases_on`q' = SOME Error`>>fsrw_tac[][]>>
    impl_tac>-
      (CONJ_ASM1_TAC>-
        (qpat_x_assum`A=SOME(q,r)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      CONJ_TAC>-
        (qpat_x_assum`A=SOME(q,r)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      CONJ_TAC>-
       (fs [comp_def,get_labels_def]
        \\ drule find_code_IMP_get_labels
        \\ fs [get_labels_def]
        \\ fs [Abbr `stack_state`,Abbr`t6`]
        \\ imp_res_tac evaluate_mono
        \\ fs[]
        \\ metis_tac[SUBSET_TRANS,subspt_trans,loc_check_SUBSET])>>
      CONJ_TAC>-
        (`EVEN (max_var r)` by
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
      fsrw_tac[][stackSemTheory.state_component_equality]>>
      imp_res_tac evaluate_mono>>
      metis_tac[IS_PREFIX_TRANS])>>
    strip_tac>>
    Cases_on`q'`>>simp[]>>
    Cases_on`x''`>>simp[]
    >-
      (IF_CASES_TAC>>fsrw_tac[][]>>
      Cases_on`pop_env r'`>>fsrw_tac[][]>>
      IF_CASES_TAC>>fsrw_tac[][]>>
      strip_tac>>
      imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
      qpat_x_assum`if A then B else C` mp_tac>>
      IF_CASES_TAC>>fsrw_tac[][]
      >-
        (*the stackLang evaluation halts*)
        (rw[]>>
        qexists_tac`ck`>>
        fsrw_tac[][Abbr`stack_state`]>>
        `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
        fsrw_tac[][state_rel_def,compile_result_NOT_2]>>
        metis_tac[IS_PREFIX_TRANS,pop_env_ffi,wordPropsTheory.evaluate_io_events_mono])
      >>
      strip_tac>>
      `∃t2. evaluate(PopHandler (k,f,f') Skip,t1) = (NONE,t2) ∧ state_rel k f f' (set_var x0 w0 x'') t2 lens ∧ x''.handler = s.handler` by
        (qpat_x_assum`!a b c d e f. P` kall_tac>>
        Q.ISPECL_THEN [`r`,`word_state`] assume_tac evaluate_stack_swap>>
        rfs[Abbr`word_state`]>>
        fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
        qpat_x_assum`pop_env A = B` mp_tac>>
        simp[pop_env_def]>>
        ntac 4 (TOP_CASE_TAC>>fsrw_tac[][s_key_eq_def,s_frame_key_eq_def])>>
        pop_assum kall_tac>>
        strip_tac>>
        fsrw_tac[][PopHandler_def,stackSemTheory.evaluate_def,LET_THM]>>
        rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
        imp_res_tac stack_rel_cons_LEN_SOME>>
        fsrw_tac[][LENGTH_DROP]>>
        simp[stackSemTheory.set_store_def,stackSemTheory.set_var_def,stackSemTheory.get_var_def,FLOOKUP_UPDATE]>>
        CONJ_TAC>-
          metis_tac[evaluate_mono,subspt_def]>>
        CONJ_ASM1_TAC>-
          (fsrw_tac[][LENGTH_DROP]>>
          Cases_on`f'`>>fsrw_tac[][]>>
          simp[])>>
        CONJ_TAC>-
          simp[wf_insert,wf_fromAList]>>
        fsrw_tac[][LET_THM]>>
        CONJ_TAC>-
          (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
          imp_res_tac stack_rel_DROP_SOME>>
          pop_assum mp_tac>>
          simp[EL_DROP,DROP_DROP])>>
        ntac 2 strip_tac>>
        fsrw_tac[][lookup_insert,convs_def]>>
        IF_CASES_TAC>-
          simp[]>>
        strip_tac>>
        `n ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
        `n ∈ domain x1 ∧ n ∈ domain s.locals` by
          (fsrw_tac[][cut_env_def]>>
          `n ∈ domain x'` by rfs[]>>
          rveq>>
          fsrw_tac[][domain_inter])>>
        res_tac>>simp[]>>
        fsrw_tac[][domain_lookup]>>
        last_x_assum (qspecl_then [`n`,`v''`]mp_tac)>>
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
        `MEM (n,v) l` by metis_tac[ALOOKUP_MEM]>>
        `MEM (n DIV 2,v) (MAP_FST adjust_names l)` by
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
        `k + SUC n' - n DIV 2 = SUC (k+ SUC n' - (n DIV 2+1))` by
          (ntac 30 (pop_assum mp_tac)>>
          rpt (pop_assum kall_tac)>>
          simp[])>>
        qpat_x_assum`COND (_ = []) _ _`mp_tac >>
        rename1`ls = []` >>
        qpat_x_assum`LENGTH ls = _`mp_tac >>
        Cases_on`ls` >> simp_tac(srw_ss())[] >>
        `SUC n' + 1 + k - (n DIV 2 + 1) = SUC (k + SUC n' - (n DIV 2 + 1))`
        by (
          ntac 30 (pop_assum mp_tac) >>
          rpt(pop_assum kall_tac) >>
          rw[]) >>
        pop_assum SUBST1_TAC >>
        simp_tac(srw_ss())[])>>
      imp_res_tac stackPropsTheory.evaluate_add_clock>>
      ntac 4 (pop_assum kall_tac)>>
      rveq>>fsrw_tac[][]>>
      first_x_assum(qspecl_then[`k`,`f`,`f'`,`t2`,`bs'`,`lens`] mp_tac)>>
      impl_tac>-
        (fsrw_tac[][convs_def]>>rw[]
        >-
          (fs [comp_def,get_labels_def,PopHandler_def]>>
          imp_res_tac evaluate_mono >>
          fs [Abbr `stack_state`,Abbr`t6`]>>
          metis_tac[SUBSET_TRANS,subspt_trans,loc_check_SUBSET])
        >-
          (qpat_x_assum`A<B:num` mp_tac>>
          simp[wordLangTheory.max_var_def])
        >>
          unabbrev_all_tac>>
          imp_res_tac evaluate_mono>>
          imp_res_tac comp_IMP_isPREFIX>>
          rpt (qpat_x_assum`isPREFIX _ _` mp_tac)>>
          simp[comp_def]>>
          metis_tac[IS_PREFIX_TRANS])>>
      rw[]>>
      qexists_tac`ck+ck'`>>
      fsrw_tac[][Abbr`stack_state`]>>
      first_x_assum(qspec_then`ck'` mp_tac)>>
      simp[Once evaluate_PopHandler_seq,stackSemTheory.evaluate_def,evaluate_PopHandler_clock]>>
      first_x_assum(qspec_then`ck'` mp_tac)>>simp[]>>
      fsrw_tac[][ADD_COMM]>>
      pop_assum mp_tac>>
      simp[set_var_def])
    >-
      (*Exception*)
      (IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      qpat_x_assum`if A then B else C` mp_tac>>
      IF_CASES_TAC>>fs[]
      >-
        (rw[]>>
        qexists_tac`ck`>>
        fsrw_tac[][Abbr`stack_state`]>>
        `ck + (t.clock -1) = ck +t.clock -1` by DECIDE_TAC>>
        fsrw_tac[][state_rel_def,compile_result_NOT_2,set_var_def]>>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono>>
        fsrw_tac[][]>>
        metis_tac[IS_PREFIX_TRANS,pop_env_ffi])
      >>
      fs[push_locals_def]>>strip_tac>>
      strip_tac>>
      `state_rel k f f' (set_var x''0 w0 r') t1 lens ∧ s.handler = r'.handler` by
        (qpat_x_assum`!a b c d e f. P` kall_tac>>
        Q.ISPECL_THEN [`r`,`word_state`] assume_tac evaluate_stack_swap>>
        rfs[Abbr`word_state`]>>
        Cases_on`n`>>
        qpat_x_assum`!a b c.P` kall_tac>>
        fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,s_key_eq_def]>>
        rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
        `LENGTH lens = LENGTH s.stack` by
           (fs[stack_rel_def]>>
           imp_res_tac abs_stack_IMP_LENGTH)>>
        qpat_x_assum`LASTN A B = C` mp_tac>>
        qpat_x_assum`stack_rel k r'.handler A B C D E (LASTN n (f'::lens))` mp_tac>>
        simp[LASTN_CONS_ID,GSYM ADD1]>>
        ntac 2 strip_tac>>
        CONJ_TAC>-
          metis_tac[evaluate_consts]>>
        CONJ_ASM1_TAC>-
          (imp_res_tac stack_rel_cons_LEN_NONE>>
          fsrw_tac[][LENGTH_DROP]>>
          Cases_on`f'`>>fsrw_tac[][]>>
          simp[])>>
        CONJ_TAC>-
          simp[wf_insert,wf_fromAList]>>
        CONJ_TAC>-
          (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
          metis_tac[stack_rel_DROP_NONE])>>
        ntac 2 strip_tac>>
        fsrw_tac[][lookup_insert,convs_def]>>
        IF_CASES_TAC>-
          simp[]>>
        strip_tac>>
        `n ∈ domain (fromAList lss)` by metis_tac[domain_lookup]>>
        `n ∈ domain x1 ∧ n ∈ domain s.locals` by
          (fsrw_tac[][cut_env_def]>>
          `n ∈ domain x'` by rfs[]>>
          rveq>>
          fsrw_tac[][domain_inter])>>
        res_tac>>simp[]>>
        fsrw_tac[][domain_lookup]>>
        last_x_assum (qspecl_then [`n`,`v''`]mp_tac)>>
        simp[LLOOKUP_THM]>>
        strip_tac>>
        fsrw_tac[][stack_rel_def]>>
        qpat_x_assum`A=SOME stack''''''` mp_tac>>
        qpat_abbrev_tac`L = DROP A B`>>
        Cases_on`L`>>simp[abs_stack_def]>>
        ntac 100 (last_x_assum kall_tac)>>
        rpt (TOP_CASE_TAC >>simp[])>>
        strip_tac>>
        qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        strip_tac>>
        fsrw_tac[][lookup_fromAList]>>
        `MEM (n,v) lss` by metis_tac[ALOOKUP_MEM]>>
        `MEM (n DIV 2,v) (MAP_FST adjust_names lss)` by
          (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
          metis_tac[])>>
        simp[LLOOKUP_THM]>>
        imp_res_tac filter_bitmap_MEM>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum (qspec_then`(n DIV 2 ,v)` mp_tac)>>
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
        Cases_on`LENGTH x`>>fs[]>>
        simp[]>>
        qpat_x_assum`COND (_ = []) _ _`mp_tac >>
        rename1`ls = []` >> Cases_on`ls` \\ fs[] >>
        `k + (SUC n'+1) - SUC(n DIV 2) = SUC (k+ SUC n' - (n DIV 2+1))` by DECIDE_TAC>>
        simp[EL_TAKE])>>
      imp_res_tac stackPropsTheory.evaluate_add_clock>>
      ntac 4 (pop_assum kall_tac)>>
      rveq>>fsrw_tac[][]>>
      first_x_assum(qspecl_then[`k`,`f`,`f'`,`t1`,`bs''`,`lens`] mp_tac)>>
      impl_tac>-
        (fsrw_tac[][convs_def]>>rw[]
        >-
          (fs [comp_def,get_labels_def,PopHandler_def] >>
          fs [Abbr `stack_state`,Abbr`t6`]>>
          imp_res_tac evaluate_mono>>
          fs[]>>
          metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])
        >-
          fs[wordLangTheory.max_var_def]
        >>
          unabbrev_all_tac>>
          imp_res_tac evaluate_mono>>
          rpt(qpat_x_assum`isPREFIX _ _` mp_tac)>>
          simp[comp_def]>>
          metis_tac[IS_PREFIX_TRANS])>>
      rw[]>>
      qexists_tac`ck+ck'`>>
      fsrw_tac[][Abbr`stack_state`]>>
      first_x_assum(qspec_then`ck'` mp_tac)>>
      fs[set_var_def])
    >>
      (*Timeout and Halt*)
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
      fs[state_rel_def])
QED

val evaluate_Seq_Skip = Q.prove(
  `stackSem$evaluate (Seq Skip p,s) = evaluate (p,s)`,
  fs [stackSemTheory.evaluate_def,LET_THM]);

val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,call_dest_def,LET_THM]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       list_max_def,evaluate_Seq_Skip,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0] NONE)``,
       EVAL  ``flat_exp_conventions (Call NONE (SOME start) [0] NONE)``,
       wordLangTheory.max_var_def,LET_DEF,MAX_DEF] |> GEN_ALL

val comp_Call = Q.prove(
  `∀start (s:('a,'a word list # 'c,'ffi) wordSem$state) k res s1 t lens.
      evaluate (Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
      res ≠ SOME Error /\ state_rel k 0 0 s t lens ⇒
      ∃ck t1:(α,'c,'ffi)stackSem$state res1.
        evaluate (Call NONE (INL start) NONE,t with clock := t.clock + ck) =
        (res1,t1) /\ 1w <> (0w:'a word) /\ 2w <> (0w:'a word) /\
        if OPTION_MAP compile_result res = res1 then
          s1.ffi = t1.ffi /\ s1.clock = t1.clock
        else
          res1 = SOME (Halt (Word 2w)) /\
          t1.ffi.io_events ≼ s1.ffi.io_events(* /\
          (IS_SOME t1.ffi.final_event ⇒ t1.ffi = s1.ffi)*)`,
  rw [] \\ drule comp_Call_lemma \\ fs [get_labels_def]
  \\ disch_then drule \\ disch_then(qspecl_then[`t.bitmaps`] mp_tac)
  \\ fs [] \\ strip_tac
  \\ `0 < 2 * k` by (fs [state_rel_def] \\ decide_tac) \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ conj_tac THEN1 (fs [state_rel_def,good_dimindex_def,dimword_def])
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs [state_rel_def,push_locals_def,LET_DEF]);

Theorem state_rel_with_clock:
   state_rel a 0 0 s t lens ⇒ state_rel a 0 0 (s with clock := k) (t with clock := k) lens
Proof
  rw[state_rel_def]\\metis_tac[]
QED

val s = ``(s:(α,α word list # γ,'ffi)wordSem$state)``;
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

Theorem state_rel_IMP_semantics:
   state_rel k 0 0 ^s ^t lens /\ semantics s start <> Fail ==>
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

val init_state_ok_def = Define `
  init_state_ok k ^t coracle <=>
    4n < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    t.stack_space <= LENGTH t.stack /\
    t.use_stack /\ t.use_store /\ t.use_alloc /\ gc_fun_ok t.gc_fun /\
    t.stack_space <= LENGTH t.stack /\
    FLOOKUP t.regs 0 = SOME (Loc 1 0) /\
    LENGTH t.bitmaps + 1 < dimword (:'a) /\
    [4w] ≼ t.bitmaps /\
    LENGTH t.stack < dimword (:'a) /\
    DROP t.stack_space t.stack = [Word 0w] /\
    Handler IN FDOM t.store /\
    LENGTH t.bitmaps + LENGTH t.data_buffer.buffer + t.data_buffer.space_left + 1 < dimword (:'a) /\
    t.compile_oracle = (λn.
      let ((bm0,cfg),progs) = coracle n in
      let (progs,bm) = word_to_stack$compile_word_to_stack k progs bm0 in
        (cfg,progs,DROP (LENGTH bm0) bm)) ∧
    (∀n. let ((bm0,cfg),progs) = coracle n in
        EVERY (post_alloc_conventions k o SND o SND) progs ∧
        EVERY (flat_exp_conventions o SND o SND) progs ∧
        EVERY ((<>) raise_stub_location o FST) progs ∧
        (n = 0 ⇒ bm0 = t.bitmaps))`

val make_init_def = Define `
  make_init k ^t code coracle =
    <| locals  := insert 0 (Loc 1 0) LN
     ; fp_regs := t.fp_regs
     ; store   := t.store \\ Handler
     ; stack   := []
     ; memory  := t.memory
     ; mdomain := t.mdomain
     ; permute := K I
     ; gc_fun  := t.gc_fun
     ; handler := 0
     ; clock   := t.clock
     ; code    := code
     ; data_buffer := t.data_buffer
     ; code_buffer := t.code_buffer
     ; compile := (λ(bm0,cfg) progs.
        let (progs,bm) = word_to_stack$compile_word_to_stack k progs bm0 in
        OPTION_MAP (λ(bytes,cfg). (bytes,DROP (LENGTH bm0) bm,(bm,cfg)))
          (t.compile cfg progs))
     ; compile_oracle := coracle
     ; be      := t.be
     ; ffi     := t.ffi
     ; termdep := 0 |> `;

val init_state_ok_IMP_state_rel = Q.prove(
  `lookup raise_stub_location t.code = SOME (raise_stub k) /\
    (!n word_prog arg_count.
       (lookup n code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       ?bs bs2 stack_prog.
         word_to_stack$compile_prog word_prog arg_count k bs = (stack_prog,bs2) /\
         isPREFIX bs2 t.bitmaps /\
         (lookup n t.code = SOME stack_prog)) /\
    domain t.code = raise_stub_location INSERT domain code ∧
    init_state_ok k t coracle ==>
    state_rel k 0 0 (make_init k t code coracle) (t:('a,'c,'ffi)stackSem$state) []`,
  fs [state_rel_def,make_init_def,LET_DEF,lookup_def,init_state_ok_def]
  \\ strip_tac
  \\ conj_tac>-
    metis_tac[]
  \\ fs [stack_rel_def,sorted_env_def,abs_stack_def,LET_THM]
  \\ fs [handler_val_def,LASTN_def,stack_rel_aux_def]
  \\ fs [filter_bitmap_def,MAP_FST_def,index_list_def]
  \\ fs[flookup_thm,wf_def] \\ every_case_tac \\ fs []
  \\ fs [lookup_insert,lookup_def] \\ rpt var_eq_tac
  \\ fs [sptreeTheory.wf_def,Once insert_def,lookup_insert] \\ metis_tac[]);

val init_state_ok_semantics =
  state_rel_IMP_semantics |> Q.INST [`s`|->`make_init k t code coracle`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

Theorem compile_semantics:
   ^t.code = fromAList (SND (compile asm_conf code)) /\
    k = (asm_conf.reg_count - (5 + LENGTH asm_conf.avoid_regs)) /\
    init_state_ok k t coracle /\ (ALOOKUP code raise_stub_location = NONE) /\
    (FST (compile asm_conf code)).bitmaps ≼ t.bitmaps /\
    EVERY (λn,m,prog. flat_exp_conventions prog /\ post_alloc_conventions (asm_conf.reg_count - (5 + LENGTH asm_conf.avoid_regs)) prog) code /\
    semantics (make_init k t (fromAList code) coracle) start <> Fail ==>
    semantics start t IN
    extend_with_resource_limit {semantics (make_init k t (fromAList code) coracle) start}
Proof
  rw [compile_def] \\ match_mp_tac (GEN_ALL init_state_ok_semantics)
  \\ fs [compile_word_to_stack_def,lookup_fromAList,LET_THM,domain_fromAList] \\ rw [] \\ fs []
  \\ TRY (pairarg_tac \\ fs [])
  \\ imp_res_tac MAP_FST_compile_word_to_stack \\ fs[]
  \\ Cases_on `n=raise_stub_location` \\ fs []
  \\ TRY
    (imp_res_tac ALOOKUP_MEM>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  \\ match_mp_tac compile_word_to_stack_IMP_ALOOKUP
  \\ metis_tac []
QED

val stack_move_no_labs = Q.prove(`
  ∀n a b c p.
  extract_labels p = [] ⇒
  extract_labels (stack_move n a b c p) = []`,
  Induct>>rw[stack_move_def]>>
  EVAL_TAC>>metis_tac[])

Theorem word_to_stack_lab_pres:
    ∀p bs kf.
  extract_labels p = extract_labels (FST (comp p bs kf))
Proof
  ho_match_mp_tac comp_ind>>
  rw[comp_def,extract_labels_def,wordPropsTheory.extract_labels_def]>>
  TRY(PairCases_on`kf`)>>TRY(PairCases_on`kf'`)>>
  fs[wReg1_def,wRegImm2_def]
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
  >- (rpt(pairarg_tac>>fs[])>>EVAL_TAC)
  >-
    (Cases_on`ri`>>fs[wRegImm2_def,wReg2_def]>>EVERY_CASE_TAC>>
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
  >- (EVAL_TAC>>EVERY_CASE_TAC>>EVAL_TAC)
  >> rpt(pairarg_tac \\ fs[wReg2_def])
  \\ every_case_tac \\ rw[] \\ EVAL_TAC
QED

Theorem word_to_stack_compile_lab_pres:
    EVERY (λn,m,p.
    let labs = extract_labels p in
    EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0) labs ∧
    ALL_DISTINCT labs) prog ⇒
  let (c,p) = compile asm_conf prog in
    MAP FST p = (raise_stub_location::MAP FST prog) ∧
    EVERY (λn,p.
      let labs = extract_labels p in
      EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0) labs ∧
      ALL_DISTINCT labs) p
Proof
  fs[compile_def]>>pairarg_tac>>rw[]>>
  pairarg_tac>>fs[]>>rveq>>fs[]>>
  EVAL_TAC>>
  qabbrev_tac`b=[4w]`>>pop_assum kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [`progs`,`bitmaps`,`prog`,`b`]>>
  Induct_on`prog`>>
  fs[compile_word_to_stack_def,FORALL_PROD]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]
  >-
    metis_tac[]
  >>
  res_tac>>fs[]>>
  qpat_x_assum`compile_prog _ _ _ _ = _` mp_tac>>
  qpat_x_assum`ALL_DISTINCT _` mp_tac>>
  qpat_x_assum`EVERY _ (extract_labels p_2)` mp_tac>>
  rpt(pop_assum kall_tac)>>
  FULL_SIMP_TAC std_ss [compile_prog_def,LET_THM]>>
  qpat_abbrev_tac`m = if _ then _ else _`>>
  pairarg_tac>>rw[]>>EVAL_TAC>>
  metis_tac[FST,word_to_stack_lab_pres]
QED

Theorem compile_word_to_stack_lab_pres:
   ∀p b q r.
   compile_word_to_stack k p b = (q,r) ∧
   EVERY (λ(l,m,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0)) (extract_labels e) ∧
     ALL_DISTINCT (extract_labels e)) p
   ⇒
   EVERY (λ(l,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0)) (extract_labels e) ∧
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

val EVEN_DIV_2_props = Q.prove(`
  a MOD 2 = 0 ∧ b MOD 2 = 0 ⇒
  (a ≠ b ⇒ a DIV 2 ≠ b DIV 2) ∧ (a ≠ 0 ⇒ a DIV 2 ≠ 0)`,
  strip_tac
  \\ qspec_then `a` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<2n``))
  \\ qpat_x_assum `a = _` (fn th => once_rewrite_tac [th])
  \\ qspec_then `b` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<2n``))
  \\ qpat_x_assum `b = _` (fn th => once_rewrite_tac [th])
  \\ asm_simp_tac std_ss [DIV_MULT] \\ fs []);

val wconvs = [post_alloc_conventions_def,wordPropsTheory.full_inst_ok_less_def,call_arg_convention_def,wordLangTheory.every_var_def,wordLangTheory.every_stack_var_def]

val call_dest_stack_asm_name = Q.prove(`
  call_dest d a k = (q0,d') ⇒
  stack_asm_name c q0 ∧
  case d' of
    INR r => r ≤ (FST k)+1
  | INL l => T`,
  Cases_on`d`>>EVAL_TAC>>rw[]>>
  EVAL_TAC>>
  pairarg_tac>>fs[]>>
  pop_assum mp_tac>>PairCases_on`k`>>
  EVAL_TAC>>rw[]>>
  EVAL_TAC>>rw[])

val wLive_stack_asm_name = Q.prove(`
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  wLive q bs kf = (q1,bs') ⇒
  stack_asm_name c q1`,
  PairCases_on`kf`>>
  fs[wLive_def]>>
  rw[]>-EVAL_TAC>>
  rpt(pairarg_tac>>fs[])>>
  rveq>>EVAL_TAC>>fs[])

Theorem word_to_stack_stack_asm_name_lem:
    ∀p bs kf c.
  post_alloc_conventions (FST kf) p ∧
  full_inst_ok_less c p ∧
  (c.two_reg_arith ⇒ every_inst two_reg_inst p) ∧
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  4 < (FST kf) ⇒
  stack_asm_name c (FST (comp p bs kf))
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
    fs[inst_ok_less_def,inst_arg_convention_def,every_inst_def,two_reg_inst_def,wordLangTheory.every_var_inst_def,reg_allocTheory.is_phy_var_def,asmTheory.fp_reg_ok_def]>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>fs[]>>
    rw[]>>
    TRY(metis_tac[EVEN_DIV_2_props])>>
    (qpat_assum`addr_offset_ok c c'` mp_tac ORELSE
     qpat_assum`byte_offset_ok c c'` mp_tac) >>EVAL_TAC>>fs[])
  >-
    (PairCases_on`kf'`>>
    ntac 3 (EVAL_TAC>>rw[])>>
    rpt(EVAL_TAC>>rw[]))
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
  >-
    (PairCases_on`kf`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
  >> PairCases_on`kf` \\ EVAL_TAC
  \\ rw[] \\ EVAL_TAC \\ fs[]
QED

val call_dest_stack_asm_remove = Q.prove(`
  (FST k)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  call_dest d a k = (q0,d') ⇒
  stack_asm_remove c q0 ∧
  case d' of
    INR r => r ≤ (FST k)+1
  | INL l => T`,
  Cases_on`d`>>EVAL_TAC>>rw[]>>
  EVAL_TAC>>
  pairarg_tac>>fs[]>>
  pop_assum mp_tac>>PairCases_on`k`>>
  EVAL_TAC>>rw[]>>
  EVAL_TAC>>rw[])

val wLive_stack_asm_remove = Q.prove(`
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ∧
  wLive q bs kf = (q1,bs') ⇒
  stack_asm_remove c q1`,
  PairCases_on`kf`>>
  fs[wLive_def]>>
  rw[]>-EVAL_TAC>>
  rpt(pairarg_tac>>fs[])>>
  rveq>>EVAL_TAC>>fs[])

Theorem word_to_stack_stack_asm_remove_lem:
    ∀(p:'a wordLang$prog) bs kf (c:'a asm_config).
  (FST kf)+1 < c.reg_count - LENGTH c.avoid_regs ⇒
  stack_asm_remove c (FST (comp p bs kf))
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
    (PairCases_on`kf'`>>
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
  >-
    (PairCases_on`kf`>>
    EVAL_TAC>>rw[]>>
    EVAL_TAC>>rw[])
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
  EVERY (λ(n,p). stack_asm_name c p ∧ stack_asm_remove c p) (SND(compile c progs))
Proof
  fs[compile_def]>>pairarg_tac>>rw[]
  >- (EVAL_TAC>>fs[])
  >- (EVAL_TAC>>fs[])
  >>
    qabbrev_tac`f = [4w]`>> pop_assum kall_tac>>
    rpt (pop_assum mp_tac)>>
    map_every qid_spec_tac[`progs'`,`f`,`bitmaps`,`progs`]>>
    Induct>>fs[FORALL_PROD,compile_word_to_stack_def]>>
    rpt strip_tac>>
    FULL_SIMP_TAC (srw_ss())[compile_prog_def]>>
    qpat_assum`A=(progs',bitmaps)`mp_tac>>LET_ELIM_TAC>>
    rpt (pairarg_tac>>fs[])>>
    qpat_assum`A=progs'` sym_sub_tac>>simp[]>>CONJ_TAC
    >-
      (qmatch_asmsub_abbrev_tac`comp p_2 f kf`>>
      Q.ISPECL_THEN [`p_2`,`f`,`kf`,`c`] assume_tac word_to_stack_stack_asm_name_lem>>
      Q.ISPECL_THEN [`p_2`,`f`,`kf`,`c`] assume_tac word_to_stack_stack_asm_remove_lem>>
      rfs[Abbr`kf`]>>
      rw[]>>EVAL_TAC>>fs[])
    >>
      metis_tac[]
QED

Theorem stack_move_alloc_arg:
    ∀n st off i p.
  alloc_arg p ⇒
  alloc_arg (stack_move n st off i p)
Proof
  Induct>>rw[stack_move_def,alloc_arg_def]
QED

Theorem word_to_stack_alloc_arg:
    ∀p n args.
  alloc_arg (FST(word_to_stack$comp p n args))
Proof
  recInduct comp_ind >>
  fs[comp_def,alloc_arg_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>
  rw[]>>fs[alloc_arg_def]
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
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[alloc_arg_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs[alloc_arg_def])
  >- (rpt (pairarg_tac>>fs[alloc_arg_def])>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,alloc_arg_def])
  >- (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>fs[alloc_arg_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs [alloc_arg_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,alloc_arg_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs [alloc_arg_def]>>
    rpt(pairarg_tac>>fs[StackArgs_def,alloc_arg_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs [alloc_arg_def]>>
    match_mp_tac stack_move_alloc_arg>>fs [alloc_arg_def]))
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
    ∀p n args.
  post_alloc_conventions (FST args) p ∧
  4 ≤ FST args ⇒
  reg_bound (FST(word_to_stack$comp p n args)) (FST args+2)
Proof
  recInduct comp_ind >>fs[comp_def,reg_bound_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>rw[]>>
  fs[reg_bound_def,convs_def]
  >-
    (fs[wMove_def]>>
    qpat_abbrev_tac`ls = parmove A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,reg_bound_def]>>
    Cases_on`ls`>>
    fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    Cases_on`p_1''`>>Cases_on`p_2'`>>fs[format_var_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs [reg_bound_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def,wRegWrite2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,reg_bound_def]>>fs [reg_bound_def,convs_def,inst_arg_convention_def])
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[reg_bound_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs [reg_bound_def])
  >- (rpt (pairarg_tac>>fs [reg_bound_def])>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,reg_bound_def])
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
    rveq>>fs [reg_bound_def]>>
    match_mp_tac stack_move_reg_bound>>fs [reg_bound_def]))
  >- (rpt(pairarg_tac>>fs[reg_bound_def])>>rveq>>fs[reg_bound_def])
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
    ∀p n args.
  post_alloc_conventions (FST args) p ⇒
  call_args (FST(word_to_stack$comp p n args)) 1 2 3 4 0
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
  >- rpt (pairarg_tac>>fs [call_args_def,convs_def])
  >- (rpt (pairarg_tac>>fs [call_args_def])>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,call_args_def])
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
    rveq>>fs [call_args_def]>>
    match_mp_tac stack_move_call_args>>fs [call_args_def]))
  >- (rpt(pairarg_tac>>fs[call_args_def])>>rveq>>fs[call_args_def])
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
    word_to_stack$compile ac p = (c',p') ∧
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
  >-
    (rw[]>>
    EVAL_TAC>>fs[])
  >>
    qabbrev_tac`k=ac.reg_count-(LENGTH ac.avoid_regs+5)`>>
    `ac.reg_count-(LENGTH ac.avoid_regs+3) = k+2` by fs[Abbr`k`]>>
    pop_assum SUBST_ALL_TAC>>
    pop_assum kall_tac>>
    rpt (pop_assum mp_tac)>>
    qspec_tac(`[4w]`,`bm`)>>
    map_every qid_spec_tac [`p''`,`progs`,`bitmaps`,`p`]>>
    Induct>>fs[compile_word_to_stack_def,FORALL_PROD]>>
    ntac 11 strip_tac>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    rveq>>fs[]
    >-
      (qpat_x_assum`_ = (prog,bitmaps')` mp_tac>>
      SIMP_TAC (std_ss++LET_ss) [Once compile_prog_def]>>
      qpat_abbrev_tac`mm = if _ then _ else _`>>
      pop_assum kall_tac>>
      pairarg_tac >> fs[]>> strip_tac>> rveq>>fs[]>>
      EVAL_TAC>>
      first_x_assum(qspec_then`p_2` assume_tac)>>
      rw[]
      >-
        metis_tac[word_to_stack_alloc_arg,FST]
      >>
        qmatch_asmsub_abbrev_tac`word_to_stack$comp _ _ xxx `>>
        `k = FST xxx` by fs[Abbr`xxx`]>>
        pop_assum SUBST_ALL_TAC>>
        imp_res_tac word_to_stack_reg_bound >>
        imp_res_tac word_to_stack_call_args >>
        metis_tac[FST])
    >>
    fs[AND_IMP_INTRO]>>
    first_x_assum match_mp_tac>>
    metis_tac[]
QED

Theorem compile_word_to_stack_convs:
   ∀p bm q bm'.
   compile_word_to_stack k p bm = (q,bm') ∧
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
  \\ qmatch_asmsub_abbrev_tac`comp p_2 bm (k,f)`
  \\ Q.ISPECL_THEN[`p_2`,`bm`,`(k,f)`,`c`]mp_tac
        word_to_stack_stack_asm_name_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ Q.ISPECL_THEN[`p_2`,`bm`,`(k,f)`,`c`]mp_tac
        word_to_stack_stack_asm_remove_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ simp_tac(srw_ss())[]
  \\ simp_tac(srw_ss())[GSYM CONJ_ASSOC]
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_alloc_arg,FST])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_reg_bound,FST,LESS_OR_EQ])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_call_args,FST])
  \\ metis_tac[]
QED

(* this is the only property needed of the wRegs  *)
val get_code_labels_wReg = Q.prove(`
  (∀n. get_code_labels (f n) = {}) ⇒
  get_code_labels (wRegWrite1 f n kf) = {} ∧
  get_code_labels (wRegWrite2 f n kf) = {}
  `,
  PairCases_on`kf`>>rw[wRegWrite1_def,wRegWrite2_def]) |> SIMP_RULE std_ss [IMP_CONJ_THM];

val get_code_handler_labels_wStackLoad = Q.prove(`
  ∀ls.
  get_code_labels (wStackLoad ls x) = get_code_labels x ∧
  stack_get_handler_labels n (wStackLoad ls x) = stack_get_handler_labels n x`,
  Induct>>fs[wStackLoad_def,FORALL_PROD]);

val wLive_code_labels = Q.prove(`
  wLive q bs kf = (q',bs') ⇒
  get_code_labels q' = {}`,
  PairCases_on`kf`>>rw[wLive_def]>>fs[]>>
  pairarg_tac>>fs[]>>rw[]);

val stack_move_code_labels = Q.prove(`
  ∀a b c d e.
  get_code_labels (stack_move a b c d e) = get_code_labels e`,
  Induct>>rw[stack_move_def]);

val word_to_stack_comp_code_labels = Q.prove(`
  ∀prog bs kf n.
  good_handlers n prog ⇒
  get_code_labels (FST (comp prog bs kf)) ⊆
  (raise_stub_location,0n) INSERT ((IMAGE (λn.(n,0)) (get_code_labels prog)) ∪ stack_get_handler_labels n (FST (comp prog bs kf)))`,
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
  >-
    (TOP_CASE_TAC>>fs[]>>pairarg_tac>>fs[get_code_handler_labels_wStackLoad])
  >-
    rpt(dep_rewrite.DEP_REWRITE_TAC [get_code_labels_wReg]>>rw[])
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
    rw[wRegWrite1_def]);

val compile_word_to_stack_code_labels = Q.prove(`
  ∀ac p bs p' bs'.
  EVERY (λ(n,m,pp). good_handlers n pp) p ∧
  compile_word_to_stack ac p bs = (p',bs') ⇒
  (* every label in the compiled code *)
  BIGUNION (IMAGE get_code_labels (set (MAP SND p'))) ⊆
  (raise_stub_location,0n) INSERT
  (* either came from wordLang *)
  IMAGE (\n.(n,0n)) (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) UNION
  (* or has been introduced into the handler labels *)
  BIGUNION (set (MAP (λ(n,pp). (stack_get_handler_labels n pp)) p'))`,
  ho_match_mp_tac compile_word_to_stack_ind>>
  fs[compile_word_to_stack_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>fs[]
  >- (
    qpat_x_assum `compile_prog _ _ _ _ = _` mp_tac>>
    PURE_REWRITE_TAC [compile_prog_def,LET_THM]>>
    rpt(pairarg_tac>>fs[])>>
    rw[]>>simp[]>>
    drule word_to_stack_comp_code_labels>>
    qmatch_asmsub_abbrev_tac`comp p bs kf`>>
    disch_then(qspecl_then [`bs`,`kf`] assume_tac)>>rfs[]>>
    fs[SUBSET_DEF]>>
    metis_tac[])
  >>
  fs[SUBSET_DEF]>>
  metis_tac[]);

Theorem word_to_stack_good_code_labels:
    compile asm_conf progs = (bs,prog') ∧
  good_code_labels progs ⇒
  stack_good_code_labels prog'
Proof
  fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[good_code_labels_def,stack_good_code_labels_def]>>
  rw[]>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]
  >-
    simp[raise_stub_def]
  >>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  rw[]
  >-
    (match_mp_tac IMAGE_SUBSET_gen>>
    asm_exists_tac>>simp[SUBSET_DEF])
  >>
    fs[SUBSET_DEF]
QED

val _ = export_theory();
