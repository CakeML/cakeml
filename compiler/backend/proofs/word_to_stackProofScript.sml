open preamble BasicProvers stackSemTheory wordSemTheory
     word_to_stackTheory wordPropsTheory stackPropsTheory
     word_allocProofTheory semanticsPropsTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_stackProof";

(* TODO: many things in this file need moving *)

val get_var_set_var = store_thm("get_var_set_var[simp]",``
  stackSem$get_var k (set_var k v st) = SOME v``,
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def]>>
  fs[FLOOKUP_UPDATE])

val MEM_TAKE = prove(
  ``!xs n x. MEM x (TAKE n xs) ==> MEM x xs``,
  Induct \\ fs [TAKE_def] \\ rw [] \\ res_tac \\ fs []);

val MEM_LASTN_ALT = prove(
  ``!xs n x. MEM x (LASTN n xs) ==> MEM x xs``,
  fs [LASTN_def] \\ rw [] \\ imp_res_tac MEM_TAKE \\ fs []);

(* TODO: remove LASTN, only use LAST_N *)
val LAST_N_LASTN_eq = store_thm("LAST_N_LASTN_eq[simp]",
  ``∀ls n. LAST_N n ls = LASTN n ls``,
  fs[LAST_N_def,LASTN_def])

val clock_add_0 = store_thm("clock_add_0[simp]",
  ``((t with clock := t.clock + 0) = t:('a,'ffi) stackSem$state) /\
    ((t with clock := t.clock) = t:('a,'ffi) stackSem$state)``,
  fs [stackSemTheory.state_component_equality]);

val DROP_DROP_EQ = store_thm("DROP_DROP_EQ",
  ``!n m xs. DROP m (DROP n xs) = DROP (m + n) xs``,
  Induct \\ fs [] \\ Cases_on `xs` \\ fs []
  \\ rpt strip_tac \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac);

val TAKE_TAKE_MIN = prove(
  ``!xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs``,
  Induct \\ Cases_on `m` \\ Cases_on `n` \\ fs [MIN_DEF]
  \\ rw [] \\ fs [] \\ TRY (`F` by decide_tac)
  \\ `n = 1` by decide_tac \\ fs []);

val TAKE_DROP_EQ = prove(
  ``!xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)``,
  Induct \\ fs [] \\ rw [] \\ fs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac);

val DROP_TAKE_NIL = prove(
  ``DROP n (TAKE n xs) = []``,
  fs [GSYM LENGTH_NIL,LENGTH_TAKE_EQ] >> simp[]);

val TAKE_LUPDATE = store_thm("TAKE_LUPDATE[simp]",
  ``!xs n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)``,
  Induct \\ fs [LUPDATE_def]
  \\ Cases_on `i` \\ fs [LUPDATE_def] \\ rw [LUPDATE_def]);

local
  val DROP_LUPDATE_lemma1 = prove(
    ``!xs n m h. n <= m ==>
                 DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs)``,
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def]
    \\ qmatch_assum_rename_tac `n <= SUC i`
    \\ `n - 1 <= i /\ (SUC i - n = i - (n - 1))` by decide_tac \\ fs [])
  val DROP_LUPDATE_lemma2 = prove(
    ``!xs n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs``,
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def]
    \\ qmatch_assum_rename_tac `SUC i < n`
    \\ first_x_assum match_mp_tac \\ decide_tac)
in
  val DROP_LUPDATE = store_thm("DROP_LUPDATE",
    ``!n h m xs.
        DROP n (LUPDATE h m xs) =
        if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs)``,
    rw [DROP_LUPDATE_lemma2]
    \\ match_mp_tac DROP_LUPDATE_lemma1
    \\ fs [NOT_LESS])
end

val alist_insert_append = Q.store_thm("alist_insert_append",
  `∀a1 a2 s b1 b2.
   LENGTH a1 = LENGTH a2 ⇒
   alist_insert (a1++b1) (a2++b2) s =
   alist_insert a1 a2 (alist_insert b1 b2 s)`,
  ho_match_mp_tac alist_insert_ind
  \\ simp[alist_insert_def,LENGTH_NIL_SYM]);

val MIN_ADD = prove(
  ``MIN m1 m2 + n = MIN (m1 + n) (m2 + n)``,
  fs [MIN_DEF] \\ decide_tac);

val list_LUPDATE_def = Define `
  (list_LUPDATE [] n ys = ys) /\
  (list_LUPDATE (x::xs) n ys = list_LUPDATE xs (n+1) (LUPDATE x n ys))`

val LENGTH_list_LUPDATE = store_thm("LENGTH_list_LUPDATE[simp]",
  ``!xs n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys``,
  Induct \\ fs [list_LUPDATE_def]);

val TAKE_list_LUPDATE = store_thm("TAKE_list_LUPDATE[simp]",
  ``!ys xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs)``,
  Induct \\ fs [list_LUPDATE_def]);

val el_opt_list_LUPDATE_IGNORE = prove(
  ``!xs i n ys.
      i + LENGTH xs <= n ==>
      el_opt n (list_LUPDATE xs i ys) = el_opt n ys``,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `(i+1) + LENGTH xs <= n` by decide_tac \\ res_tac
  \\ `i <> n` by decide_tac \\ fs [el_opt_LUPDATE]);

val DROP_list_LUPDATE = prove(
  ``!ys n m xs.
      n <= m ==>
      DROP n (list_LUPDATE ys m xs) =
      list_LUPDATE ys (m - n) (DROP n xs)``,
  Induct
  \\ fs [list_LUPDATE_def,LENGTH_NIL,PULL_FORALL]
  \\ rpt strip_tac \\ `n <= m + 1` by decide_tac
  \\ rw [] \\ `m + 1 - n = m - n + 1 /\ ~(m < n)` by decide_tac
  \\ fs [DROP_LUPDATE]);

val DROP_list_LUPDATE_IGNORE = prove(
  ``!xs i ys n.
      LENGTH xs + i <= n ==>
      DROP n (list_LUPDATE xs i ys) = DROP n ys``,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `LENGTH xs + (i+1) <= n /\ i < n` by decide_tac
  \\ fs [DROP_LUPDATE]);

val list_LUPDATE_NIL = store_thm("list_LUPDATE_NIL[simp]",
  ``!xs i. list_LUPDATE xs i [] = []``,
  Induct \\ fs [list_LUPDATE_def,LUPDATE_def]);

val LUPDATE_TAKE_LEMMA = prove(
  ``!xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)``,
  Induct \\ Cases_on `n` \\ fs [LUPDATE_def]);

val list_LUPDATE_TAKE_DROP = store_thm("list_LUPDATE_TAKE_DROP",
  ``!xs (ys:'a list) n.
       list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP n ys)``,
  Induct \\ simp_tac std_ss [Once list_LUPDATE_def]
  \\ once_rewrite_tac [list_LUPDATE_def] THEN1 fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [DROP_LUPDATE,DROP_DROP_EQ,AC ADD_COMM ADD_ASSOC]
  \\ simp_tac std_ss [Once LUPDATE_TAKE_LEMMA,TAKE_TAKE_MIN] \\ rpt strip_tac
  \\ `MIN (n + 1) n = n`  by (fs [MIN_DEF] \\ decide_tac) \\ fs []
  \\ AP_TERM_TAC \\ fs [TAKE_DROP_EQ,AC ADD_COMM ADD_ASSOC]);

val list_LUPDATE_0_CONS = store_thm("list_LUPDATE_0_CONS[simp]",
  ``!xs x ys y. list_LUPDATE (x::xs) 0 (y::ys) = x :: list_LUPDATE xs 0 ys``,
  fs [list_LUPDATE_def,LUPDATE_def]
  \\ simp_tac std_ss [Once list_LUPDATE_TAKE_DROP] \\ fs []);

val list_LUPDATE_APPEND = store_thm("list_LUPDATE_APPEND",
  ``!xs ys zs.
      LENGTH xs = LENGTH ys ==> (list_LUPDATE xs 0 (ys ++ zs) = xs ++ zs)``,
  Induct \\ Cases_on `ys` \\ fs [list_LUPDATE_def]);

(* move to stackProps? *)

val DIV_ADD_1 = prove(
  ``0 < d ==> (m DIV d + 1 = (m + d) DIV d)``,
  rpt strip_tac
  \\ ASSUME_TAC (ADD_DIV_ADD_DIV |> Q.SPECL [`d`] |> UNDISCH
      |> Q.SPECL [`1`,`m`] |> ONCE_REWRITE_RULE [ADD_COMM]) \\ fs []);

val LENGTH_word_list_lemma = prove(
  ``!xs d. 0 < d ==> (LENGTH (word_list xs d) = (LENGTH xs - 1) DIV d + 1)``,
  recInduct word_list_ind
  \\ rpt strip_tac \\ fs []
  \\ once_rewrite_tac [word_list_def] \\ fs [] \\ rw []
  \\ imp_res_tac ZERO_DIV \\ fs [] \\ res_tac
  \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fs []
  \\ fs [ADD1] \\ fs [NOT_LESS]
  \\ imp_res_tac (ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_EXISTS)
  THEN1 (`LENGTH xs - 1 < d` by decide_tac
         \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fs [])
  \\ imp_res_tac DIV_ADD_1 \\ fs []
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac);

val LENGTH_word_list = store_thm("LENGTH_word_list",
  ``!xs d. LENGTH (word_list xs d) =
           if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1``,
  rw [] THEN1 (once_rewrite_tac [word_list_def] \\ fs [])
  \\ match_mp_tac LENGTH_word_list_lemma \\ decide_tac);

(* move to wordProps? *)

val list_rearrange_I = prove(
  ``(list_rearrange I = I)``,
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

val index_list_def = Define `
  (index_list [] n = []) /\
  (index_list (x::xs) n = (n + LENGTH xs,x) :: index_list xs n)`

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

val gc_fun_ok_def = Define `
  gc_fun_ok (f:'a gc_fun_type) =
    !wl m d s wl1 m1 s1.
      Handler IN FDOM s /\
      (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
      (LENGTH wl = LENGTH wl1) /\
      ~(Handler IN FDOM s1) /\
      (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,s ' Handler)))`

(*f is the size of the current frame + 1 most of the time
  (extra word for the bitmap pointer)
  f' is the size of the current frame
  lens tracks the size of each remaining stack frame on the stackLang stack
*)
val state_rel_def = Define `
  state_rel k f f' (s:('a,'ffi) wordSem$state) (t:('a,'ffi) stackSem$state) lens ⇔
    (s.clock = t.clock) /\ (s.gc_fun = t.gc_fun) /\ (s.permute = K I) /\
    (t.ffi = s.ffi) /\ t.use_stack /\ t.use_store /\ t.use_alloc /\
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\ 1 < k /\
    (s.store = t.store \\ Handler) /\ gc_fun_ok t.gc_fun /\
    t.be = s.be /\ t.ffi = s.ffi /\ Handler ∈ FDOM t.store ∧
    (!n word_prog arg_count.
       (lookup n s.code = SOME (arg_count,word_prog)) ==>
       ?bs bs2 stack_prog.
         word_to_stack$compile_prog word_prog arg_count k bs = (stack_prog,bs2) /\
         isPREFIX bs2 t.bitmaps /\
         (lookup n t.code = SOME stack_prog)) /\
    (lookup 5 t.code = SOME (raise_stub k)) /\
    good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    LENGTH t.bitmaps +1 < dimword (:α) /\
    1 ≤ LENGTH t.bitmaps ∧ HD t.bitmaps = 4w ∧
    t.stack_space + f <= LENGTH t.stack /\ LENGTH t.stack < dimword (:'a) /\
    (if f' = 0 then f = 0 else (f = f' + 1)) /\
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
        else (el_opt (f-1 -(n DIV 2 - k)) current_frame = SOME v) /\
             n DIV 2 < k + f')`

(* correctness proof *)

val evaluate_SeqStackFree = prove(
  ``t.use_stack /\ t.stack_space <= LENGTH t.stack ==>
    evaluate (SeqStackFree f p,t) =
    evaluate (Seq (StackFree f) p,t)``,
  fs [SeqStackFree_def] \\ rw [stackSemTheory.evaluate_def]
  THEN1 (`F` by decide_tac) \\ AP_TERM_TAC
  \\ fs [stackSemTheory.state_component_equality]);

val convs_def = LIST_CONJ
  [word_allocTheory.post_alloc_conventions_def,
   word_allocTheory.call_arg_convention_def,
   wordLangTheory.every_var_def,
   wordLangTheory.every_stack_var_def,
   wordLangTheory.every_name_def]

val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``

(*
val LENGTH_write_bitmap = prove(
  ``state_rel k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap (names:num_set) k f'):'a word list) + f' = f)``,
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac);
*)

val DROP_list_LUPDATE_lemma =
  MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL) |> SIMP_RULE std_ss []

val bits_to_word_bit = prove(
  ``!bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)``,
  Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1] \\ rpt strip_tac
  \\ first_x_assum match_mp_tac \\ fs [] \\ decide_tac);

val bits_to_word_miss = prove(
  ``!bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)``,
  Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);

val bits_to_word_NOT_0 = prove(
  ``!bs. LENGTH bs <= dimindex (:'a) /\ EXISTS I bs ==>
         (bits_to_word bs <> 0w:'a word)``,
  fs [fcpTheory.CART_EQ] \\ rpt strip_tac
  \\ fs [EXISTS_MEM,MEM_EL]
  \\ Q.EXISTS_TAC `n`   \\ fs []
  \\ `n < dimindex (:'a)` by decide_tac \\ fs [word_0]
  \\ fs [bits_to_word_bit]);

val list_LUPDATE_write_bitmap_NOT_NIL = prove(
  ``8 <= dimindex (:'a) ==>
    (list_LUPDATE (MAP Word (write_bitmap names k f')) 0 xs <>
     [Word (0w:'a word)])``,
  Cases_on `xs` \\ fs [list_LUPDATE_NIL]
  \\ fs [write_bitmap_def,LET_DEF,Once word_list_def]
  \\ strip_tac \\ `~(dimindex (:'a) <= 1)` by decide_tac \\ fs []
  \\ rw [] \\ rpt disj1_tac
  \\ match_mp_tac bits_to_word_NOT_0 \\ fs [LENGTH_TAKE_EQ]
  \\ fs [MIN_LE,MIN_ADD] \\ decide_tac);

val LESS_EQ_LENGTH = prove(
  ``!xs n. n <= LENGTH xs ==> ?xs1 xs2. xs = xs1 ++ xs2 /\ n = LENGTH xs1``,
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct_on `n` \\ fs [LENGTH_NIL] \\ rpt strip_tac
  \\ Cases_on `xs` \\ fs [] \\ res_tac \\ rw []
  \\ Q.LIST_EXISTS_TAC [`h::xs1`,`xs2`] \\ fs []);

val word_or_eq_0 = prove(
  ``((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,
  fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_0]
  \\ metis_tac []);

val shift_shift_lemma = prove(
  ``~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)``,
  fs [fcpTheory.CART_EQ,word_lsl_def,word_lsr_def,fcpTheory.FCP_BETA,word_msb_def]
  \\ rpt strip_tac \\ Cases_on `i + 1 < dimindex (:α)`
  \\ fs [fcpTheory.FCP_BETA] \\ fs [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac \\ fs []);

val bit_length_bits_to_word = prove(
  ``!qs.
      LENGTH qs + 1 < dimindex (:'a) ==>
      bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs + 1``,
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

val GENLIST_bits_to_word_alt = prove(
  ``LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs``,
  fs [LIST_EQ_REWRITE] \\ rpt strip_tac
  \\ `EL x xs = EL x (xs ++ ys)` by fs [EL_APPEND1]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ match_mp_tac bits_to_word_bit
  \\ fs [] \\ decide_tac);

val GENLIST_bits_to_word = prove(
  ``LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'``,
  rpt strip_tac \\ match_mp_tac GENLIST_bits_to_word_alt
  \\ fs [] \\ decide_tac);

val read_bitmap_word_list = prove(
  ``8 <= dimindex (:'a) ==>
    read_bitmap
      ((word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++ (xs:'a word list)) =
    SOME qs``,
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
   (fs [word_msb_def]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fs []
    \\ reverse (rpt strip_tac) THEN1 decide_tac THEN1 decide_tac
    \\ pop_assum (fn th => simp_tac std_ss [Once th])
    \\ fs [EL_LENGTH_APPEND]) \\ fs []
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

val APPEND_LEMMA = prove(
  ``n1 + n2 + n3 <= LENGTH xs ==>
    ?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2``,
  rpt strip_tac
  \\ `n1 <= LENGTH xs` by decide_tac
  \\ Q.PAT_ASSUM `n1 + n2 + n3 <= LENGTH xs` MP_TAC
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [DROP_LENGTH_APPEND]  \\ fs []
  \\ `n2 <= LENGTH xs2` by decide_tac
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [] \\ metis_tac []);

val read_bitmap_append_extra = Q.store_thm("read_bitmap_append_extra",
  `∀l1 l2 bits.
   read_bitmap l1 = SOME bits ⇒
   read_bitmap (l1 ++ l2) = SOME bits`,
  Induct >> simp[read_bitmap_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC >> simp[]
  \\ BasicProvers.CASE_TAC >> simp[]
  \\ fs[] \\ rfs[]);

val read_bitmap_write_bitmap = Q.store_thm("read_bitmap_write_bitmap",
  `8 ≤ dimindex (:α) ⇒
   read_bitmap ((write_bitmap names k f'):α word list) =
   SOME (GENLIST (λx. MEM x (MAP (λ(r,y). f' - 1 - (r DIV 2 - k)) (toAList names))) f')`,
  rw[write_bitmap_def]
  \\ imp_res_tac read_bitmap_word_list
  \\ first_x_assum(qspec_then`[]`mp_tac)
  \\ simp[]);

val read_bitmap_insert_bitmap = Q.store_thm("read_bitmap_insert_bitmap",
  `∀bs bs' i.
   i < dimword (:α) ∧
   IS_SOME (read_bitmap bm) ∧
   insert_bitmap bm (bs:α word list) = (bs',i)
   ⇒ read_bitmap (DROP (i MOD dimword (:α)) bs') = read_bitmap bm`,
  Induct >> simp[insert_bitmap_def] \\ rw[] \\ simp[]
  >- (
    fs[IS_PREFIX_APPEND,IS_SOME_EXISTS]
    \\ match_mp_tac read_bitmap_append_extra
    \\ simp[] )
  \\ split_pair_tac >> fs[]
  \\ rveq
  \\ REWRITE_TAC[GSYM ADD1]
  \\ REWRITE_TAC[DROP]
  \\ first_x_assum match_mp_tac
  \\ simp[]);

val insert_bitmap_length = Q.store_thm("insert_bitmap_length",
  `∀ls ls' i. insert_bitmap bm ls = (ls',i) ⇒ i ≤ LENGTH ls ∧ LENGTH ls ≤ LENGTH ls'`,
  Induct >> simp[insert_bitmap_def]
  \\ rw[] >> simp[]
  \\ split_pair_tac >> fs[]
  \\ rw[] >> simp[]);

(*

val read_bitmap_write_bitmap = prove(
  ``t.stack_space + f <= LENGTH t.stack /\ 8 <= dimindex (:'a) /\
    (LENGTH (write_bitmap names k f': 'a word list) + f' = f) /\
    (if f' = 0 then f = 0 else f = f' + f' DIV (dimindex (:'a) - 1) + 1) /\
    (1 <= f) ==>
    read_bitmap
      (list_LUPDATE (MAP Word (write_bitmap (names:num_set) k f')) 0
         (DROP t.stack_space t.stack)) =
    SOME (GENLIST (\x. MEM x (MAP (\(r,y). (f'-1) - (r DIV 2 - k)) (toAList names))) f',
          MAP Word (write_bitmap names k f'): 'a word_loc list,
          (DROP (f - f') (DROP t.stack_space t.stack)))``,
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

val abs_stack_IMP_LENGTH = prove(
  ``∀bs wstack sstack lens stack.
    abs_stack bs wstack sstack lens = SOME stack ⇒ LENGTH stack = LENGTH wstack ∧ LENGTH lens = LENGTH wstack``,
  recInduct (theorem "abs_stack_ind")
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw [])

val IMP_filter_bitmap_EQ_SOME_NIL = prove(
  ``!xs ys zs.
      (LENGTH xs = LENGTH ys) /\
      zs = MAP FST (FILTER SND (ZIP (ys, xs))) ==>
      (filter_bitmap xs ys = SOME (zs,[]))``,
  Induct \\ Cases_on `ys` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def]);

val LENGTH_index_list = prove(
  ``!l n. LENGTH (index_list l n) = LENGTH l``,
  Induct \\ fs [index_list_def]);

val SORTED_FST_LESS_IMP = prove(
  ``!xs x.
      SORTED (\x y. FST x > FST y:num) (x::xs) ==>
      SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
      (!y. MEM y xs ==> FST x > FST y)``,
  Induct \\ fs [SORTED_DEF]
  \\ ntac 3 strip_tac \\ res_tac \\ rpt strip_tac
  \\ rw [] \\ fs [] \\ res_tac \\ decide_tac);

val SORTED_IMP_EQ_LISTS = prove(
  ``!xs ys.
      SORTED (\x y. FST x > FST y:num) ys /\
      SORTED (\x y. FST x > FST y) xs /\
      (!x. MEM x ys <=> MEM x xs) ==>
      (xs = ys)``,
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

val transitive_key_val_compare = Q.store_thm("transitive_key_val_compare",
  `transitive key_val_compare`,
  fs[transitive_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ imp_res_tac WORD_LESS_EQ_TRANS \\ fs [])

val total_key_val_compare = Q.store_thm("total_key_val_compare",
  `total key_val_compare`,
  fs[total_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ CCONTR_TAC \\ fs [] \\ TRY decide_tac
  \\ fs [GSYM WORD_NOT_LESS]
  \\ wordsLib.WORD_DECIDE_TAC)

val SORTS_QSORT_key_val_compare = prove(
  ``SORTS QSORT key_val_compare``,
  match_mp_tac QSORT_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare))

val MEM_QSORT = SORTS_QSORT_key_val_compare
  |> SIMP_RULE std_ss [SORTS_DEF]
  |> SPEC_ALL |> CONJUNCT1
  |> MATCH_MP MEM_PERM |> GSYM |> GEN_ALL

val EL_index_list = prove(
  ``!xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = (k + LENGTH xs - i - 1, EL i xs))``,
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac);

val EL_index_list2 = prove(``
 ∀xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = (k + LENGTH xs - (i+1), EL i xs))``,
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac);

val SORTED_weaken2 = Q.prove(`
  ∀ls. SORTED R ls ∧
  ALL_DISTINCT ls ∧
  (∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ∧ R x y ⇒ R' x y) ⇒
  SORTED R' ls`,
  Induct>>rw[]>>Cases_on`ls`>>fs[SORTED_DEF]>>
  metis_tac[])

val EVEN_GT = prove(``
  ∀a b.
  EVEN a ∧ EVEN b ∧
  a > b ⇒
  a DIV 2 > b DIV 2``,
  fs[EVEN_EXISTS]>>rw[]>>
  fs[MULT_DIV,MULT_COMM]>>
  DECIDE_TAC)

val transitive_GT = prove(``
  transitive ($> : (num->num->bool))``,
  fs[transitive_def]>>DECIDE_TAC)

val env_to_list_K_I_IMP = prove(
  ``!env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l``,
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
  \\ split_pair_tac \\ fs [] \\ split_pair_tac \\ fs [])

val evaluate_wLive = Q.prove(
  `wLive names bs (k,f,f') = (wlive_prog,bs') /\
   (∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
   state_rel k f f' (s:('a,'ffi) wordSem$state) t lens /\ 1 <= f /\
   (cut_env names s.locals = SOME env) /\
   isPREFIX bs' t.bitmaps ==>
   ?t5 bs5.
     (evaluate (wlive_prog,t) = (NONE,t5)) /\
     state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 (f'::lens) /\
     state_rel k f f' s t5 lens /\
     !i. i < k ==> get_var i t5 = get_var i t`,
  fs [wLive_def,LET_THM] \\ rpt strip_tac
  \\ split_pair_tac \\ fs [] \\ rpt var_eq_tac
  \\ fs [stackSemTheory.evaluate_def,stackSemTheory.inst_def,
         stackSemTheory.assign_def,stackSemTheory.word_exp_def,LET_THM]
 \\ `t.stack_space <= LENGTH t.stack /\
     t.use_stack /\ ~(LENGTH t.stack < t.stack_space)` by
        (fs[state_rel_def,LET_THM,stack_rel_def] \\ decide_tac) \\ fs []
  \\ fs [stackSemTheory.set_var_def,stackSemTheory.get_var_def,
         FLOOKUP_UPDATE,DECIDE ``i<n ==> i<>n:num``]
  \\ fs [state_rel_def,push_env_def,LET_THM,FUN_EQ_THM,env_to_list_def,
         lookup_def,FLOOKUP_UPDATE,DECIDE ``i<n ==> i<>n:num``,
         DROP_list_LUPDATE_lemma |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def]]
  \\ reverse (rpt strip_tac)
  THEN1
   (res_tac \\ rw [] \\ fs []
    \\ qpat_assum `xx = SOME v` (fn th => once_rewrite_tac [GSYM th])
    \\ match_mp_tac (el_opt_list_LUPDATE_IGNORE |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def])
    \\ fs [] \\ Cases_on `f' = 0` \\ fs [] \\ decide_tac)
  THEN1
   (qpat_assum `stack_rel k s.handler s.stack xx yy tt _ _` mp_tac
    \\ match_mp_tac (METIS_PROVE [] ``(b1 = b2) ==> (b1 ==> b2)``)
    \\ AP_THM_TAC \\ AP_THM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ match_mp_tac (GSYM DROP_list_LUPDATE_IGNORE |> Q.SPEC `[x]`
           |> SIMP_RULE std_ss [list_LUPDATE_def])
    \\ fs [] \\ decide_tac)
  \\ fs [stack_rel_def,stack_rel_aux_def,abs_stack_def]
  \\ Cases_on `DROP t.stack_space t.stack` \\ fs []
  THEN1 (fs [listTheory.DROP_NIL,DECIDE ``m>=n<=>n<=m:num``] \\ `F` by decide_tac)
  \\ fs [LUPDATE_def,abs_stack_def]
  \\ conj_tac THEN1
   (mp_tac (Q.SPEC `env` env_to_list_K_I_IMP)
    \\ fs [env_to_list_def,sorted_env_def,LET_DEF] \\ rw []
    \\ `s.permute 0 = I` by fs [FUN_EQ_THM] \\ fs [])
  \\ fs [full_read_bitmap_def,GSYM word_add_n2w]
  \\ `i < dimword(:α) ∧ (i+1) MOD dimword(:'a) ≠ 0` by (
    fs[state_rel_def]
    \\ imp_res_tac insert_bitmap_length
    \\ fs[IS_PREFIX_APPEND] >> fs[]
    \\ simp[] )
  \\ drule (GEN_ALL read_bitmap_insert_bitmap)
  \\ simp[IS_SOME_EXISTS,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ disch_then drule
  \\ simp[read_bitmap_write_bitmap]
  \\ strip_tac
  \\ fs[IS_PREFIX_APPEND]
  \\ imp_res_tac read_bitmap_append_extra
  \\ simp[DROP_APPEND]
  \\ fsrw_tac[ARITH_ss][] \\ rveq
  \\ fsrw_tac[ARITH_ss][]
  \\ ntac 2 (pop_assum kall_tac)
  \\ conj_tac
  >- (
    rw[]
    \\ imp_res_tac abs_stack_IMP_LENGTH
    \\ Cases_on`s.handler<LENGTH s.stack`>>fs[]
    \\ qpat_assum`is_handler_frame _`mp_tac
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
  \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ conj_asm1_tac THEN1 (
      fs [LENGTH_index_list,LENGTH_TAKE_EQ,MIN_DEF]
      \\ rw[] >> decide_tac )
  \\ fs [ZIP_GENLIST] \\ pop_assum kall_tac
  \\ qpat_abbrev_tac`ls = MAP _ (toAList _)`
  \\ `!x. MEM x ls <=>
          ?n. x = f' - 1 - (n DIV 2 - k) /\ n IN domain env` by
   (fs [MEM_MAP,EXISTS_PROD,MEM_toAList,cut_env_def,Abbr`ls`] \\ rw[]
    \\ fs [lookup_inter_alt,domain_lookup,SUBSET_DEF]
  \\ metis_tac []) \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ fs [MAP_FST_def,adjust_names_def]
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
    match_mp_tac SORTED_weaken2>>fs[]>>CONJ_ASM1_TAC
    >-
      metis_tac[ALL_DISTINCT_MAP_FST_toAList,QSORT_PERM,ALL_DISTINCT_PERM,ALL_DISTINCT_MAP]
    >>
      simp[MEM_QSORT,Abbr`R`] >>
      simp[Abbr`R'`,inv_image_def,FORALL_PROD,Abbr`ls`,MEM_toAList] >>
      fs[key_val_compare_def,LET_THM]>>
      `∀p v. lookup p env = SOME v ⇒ lookup p s.locals = SOME v` by
        (fs[cut_env_def]>>qpat_assum`A=env` (SUBST_ALL_TAC o SYM)>>
        fs[lookup_inter_EQ])>>
      rw[]>>fs[]>>res_tac>>res_tac>>
      fs[EVEN_GT])
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
      rw[] >>
      qmatch_abbrev_tac`FST (EL x (index_list ls k)) = Z` >>
      qmatch_assum_abbrev_tac`DROP nn ll = _`
      \\ qispl_then[`nn`,`ll`]mp_tac LENGTH_DROP
      \\ asm_simp_tac(std_ss)[Abbr`ll`,Abbr`nn`]
      \\ simp[] >>
      `x < LENGTH ls` by ( simp[Abbr`ls`] ) >>
      asm_simp_tac std_ss [EL_index_list] >>
      simp[Abbr`ls`,Abbr`Z`] ) >>
    pop_assum SUBST1_TAC >>
    fs[Abbr`R`]>>
    fs[SORTED_EL_SUC]>>rw[]>>`n < m` by DECIDE_TAC>>
    fs[EL_GENLIST]>>DECIDE_TAC)
  \\ rator_x_assum`cut_env`mp_tac
  \\ simp[MEM_MAP,MEM_FILTER,MEM_GENLIST,PULL_EXISTS,MEM_QSORT,
            MEM_toAList,EXISTS_PROD,FORALL_PROD,cut_env_def]
  \\ strip_tac >> rveq
  \\ simp[lookup_inter_alt,domain_inter]
  \\ fs[SUBSET_DEF]
  \\ `LENGTH (TAKE f' t') = f'` by ( simp[LENGTH_TAKE_EQ] )
  \\ rw[EQ_IMP_THM]
  >- (
    fs[domain_lookup,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac \\ simp[]
    \\ first_x_assum drule >> strip_tac
    \\ first_x_assum drule
    \\ last_x_assum drule
    \\ IF_CASES_TAC >- simp[]
    \\ simp[el_opt_THM,EVEN_EXISTS]
    \\ strip_tac >> rveq
    \\ fs[MULT_COMM,MULT_DIV]
    \\ fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1]
    \\ simp[EL_index_list] )
  \\ fs[domain_lookup]
  \\ first_x_assum drule >> strip_tac
  \\ first_x_assum drule
  \\ last_x_assum drule
  \\ IF_CASES_TAC >- simp[]
  \\ simp[el_opt_THM,EVEN_EXISTS]
  \\ strip_tac >> rveq
  \\ fs[MULT_COMM,MULT_DIV]
  \\ fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1]
  \\ rfs[]
  \\ qpat_assum`_ = EL _ (index_list _ _)`(mp_tac o SYM)
  \\ simp[EL_index_list] >> strip_tac >> rveq
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ asm_exists_tac
  \\ simp[]
  \\ simp_tac (srw_ss()) [MULT_COMM,MULT_DIV]);

val push_env_set_store = prove(
  ``push_env env ^nn (set_store AllocSize (Word c) s) =
    set_store AllocSize (Word c) (push_env env ^nn s)``,
  fs [push_env_def,set_store_def,env_to_list_def,LET_DEF])|> INST_TYPE [beta|-> alpha, gamma|->beta];

val state_rel_set_store = prove(
  ``state_rel k 0 0 s5 t5 len ==>
    state_rel k 0 0 (set_store AllocSize w s5) (set_store AllocSize w t5) len``,
  rpt strip_tac
  \\ fs [state_rel_def,set_store_def,stackSemTheory.set_store_def,LET_DEF,
         FLOOKUP_DEF] \\ REPEAT STRIP_TAC \\ rfs[]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [fmap_EXT,DRESTRICT_DEF,EXTENSION]
  \\ rpt strip_tac  THEN1 (Cases_on `x = Handler` \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]);

val filter_bitmap_IMP_MAP_SND = prove(
  ``!ys xs l.
      filter_bitmap ys xs = SOME (l,[]) ==>
      filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])``,
  Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []);

val MAP_SND_index_list = prove(
  ``!xs k. MAP SND (index_list xs k) = xs``,
  Induct \\ fs [index_list_def]);

val filter_bitmap_TAKE_LENGTH_IMP = prove(
  ``!h5 x4 l.
      filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[]) ==>
      filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)``,
  Induct \\ Cases_on `x4` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ Cases_on `l` \\ fs [] \\ rw [] \\ res_tac \\ fs []);

val filter_bitmap_lemma = prove(
  ``filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[]) ==>
    filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4)``,
  rpt strip_tac \\ imp_res_tac filter_bitmap_IMP_MAP_SND
  \\ fs [MAP_SND_index_list] \\ imp_res_tac filter_bitmap_TAKE_LENGTH_IMP);

val MAP_SND_MAP_FST = prove(
  ``!xs f. MAP SND (MAP_FST f xs) = MAP SND xs``,
  Induct \\ fs [MAP,MAP_FST_def,FORALL_PROD]);

val read_bitmap_not_empty = prove(``
  read_bitmap stack = SOME a ⇒
  stack ≠ []``,
  rw[]>>CCONTR_TAC>>
  fs[]>>
  fs[read_bitmap_def])

val n2w_lsr_1 = prove(
  ``n < dimword (:'a) ==> n2w n >>> 1 = (n2w (n DIV 2)):'a word``,
  once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr] \\ fs []
  \\ fs [DIV_LT_X] \\ decide_tac);

val handler_bitmap_props = prove(``
  good_dimindex(:'a) ⇒
  read_bitmap ((4w:'a word)::stack) = SOME [F;F]``,
  fs [read_bitmap_def,good_dimindex_def] \\ strip_tac
  \\ `~(word_msb 4w)` by fs [word_msb_def,wordsTheory.word_index] \\ fs []
  \\ `4 < dimword (:'a) /\ 2 < dimword (:'a)` by fs [dimword_def]
  \\ `bit_length 4w = 3` by
   (NTAC 4 (fs [dimword_def,Once bit_length_def,n2w_lsr_1,EVAL ``1w ⋙ 1``]))
  \\ fs [] \\ EVAL_TAC \\ rw [] \\ decide_tac)

val enc_stack_lemma = prove(
  ``∀bs (wstack:'a stack_frame list) sstack lens astack bs'.
      good_dimindex(:'a) ∧
      LENGTH bs + 1 < dimword (:'a) ∧
      abs_stack bs wstack sstack lens = SOME astack ∧
      (*The first bitmap is the handler one*)
      1 ≤ LENGTH bs ∧
      HD bs = 4w ∧
      stack_rel_aux k len wstack astack ⇒
      enc_stack bs sstack = SOME (enc_stack wstack)``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  fs[enc_stack_def]>>
  rw[]>>
  fs[Once stackSemTheory.enc_stack_def,abs_stack_def]>>
  qpat_assum`A=SOME astack` mp_tac>>
  TOP_CASE_TAC>>fs[]
  >- (
    simp[]
    \\ TOP_CASE_TAC \\ strip_tac>>
    rveq>>fs[stack_rel_aux_def]>>
    imp_res_tac filter_bitmap_lemma>>
    fs[]>>rfs[]>>
    qpat_assum`A=SOME(enc_stack wstack)` mp_tac>>
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

val IMP_enc_stack = prove(
  ``state_rel k 0 0 s1 t1 lens
    ==>
    (enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
       SOME (enc_stack s1.stack))``,
  fs [state_rel_def,LET_DEF] \\ rpt strip_tac
  \\ fs [stack_rel_def] \\ imp_res_tac enc_stack_lemma>>
  simp[]);

(*Might be wrong?*)
val dec_stack_lemma = prove(
  ``enc_stack t1.bitmaps (DROP t1.stack_space t1.stack) =
      SOME (enc_stack s1.stack) /\
    (dec_stack x0 s1.stack = SOME x) /\
    stack_rel k s1.handler s1.stack (SOME (t1.store ' Handler))
      (DROP t1.stack_space t1.stack) (LENGTH t1.stack) t1.bitmaps lens /\
    (LENGTH (enc_stack s1.stack) = LENGTH x0) ==>
    ?yy. dec_stack t1.bitmaps x0 (DROP t1.stack_space t1.stack) = SOME yy /\
         (t1.stack_space + LENGTH yy = LENGTH t1.stack) /\
         stack_rel k s1.handler x (SOME (t1.store ' Handler)) yy
            (LENGTH t1.stack) t1.bitmaps lens``,
  cheat) |> INST_TYPE [beta|->``:'ffi``,gamma|->``:'ffi``];

val gc_state_rel = prove(
  ``(gc (s1:('a,'ffi) wordSem$state) = SOME s2) /\ state_rel k 0 0 s1 t1 lens /\ (s1.locals = LN) ==>
    ?t2. gc t1 = SOME t2 /\ state_rel k 0 0 s2 t2 lens``,
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
  \\ fs [DROP_APPEND,DROP_TAKE_NIL]);

val alloc_alt = prove(
  ``FST (alloc c names (s:('a,'ffi) wordSem$state)) <> SOME (Error:'a result) ==>
    (alloc c names (s:('a,'ffi) wordSem$state) =
     case cut_env names s.locals of
       NONE => (SOME Error,s)
     | SOME env =>
         case gc (set_store AllocSize (Word c)
                    (push_env env ^nn s with locals := LN)) of
           NONE => (SOME Error,s)
         | SOME s' =>
             case pop_env s' of
               NONE => (SOME (Error:'a result),s')
             | SOME s' =>
                 case FLOOKUP s'.store AllocSize of
                   NONE => (SOME Error,s')
                 | SOME w =>
                     case has_space w s' of
                       NONE => (SOME Error,s')
                     | SOME T => (NONE,s')
                     | SOME F =>
                         (SOME NotEnoughSpace,
                          call_env [] s' with stack := []))``,
  fs [alloc_def]
  \\ Cases_on `cut_env names s.locals` \\ fs []
  \\ fs [gc_def,set_store_def,push_env_def,LET_DEF,
         env_to_list_def,pop_env_def]
  \\ BasicProvers.EVERY_CASE_TAC
   \\ fs [state_component_equality] \\ rw []
   \\ fs [state_component_equality] \\ rw []);

val map_bitmap_remainder = prove(``
  ∀a b c d e.
  map_bitmap a b c = SOME (d,e) ⇒
  e = DROP (LENGTH a) c``,
  ho_match_mp_tac map_bitmap_ind>>rw[map_bitmap_def]>>
  pop_assum mp_tac >> EVERY_CASE_TAC>>fs[])

val map_bitmap_length = prove(``
  ∀a b c x y.
  map_bitmap a b c = SOME(x,y) ⇒
  LENGTH c = LENGTH x + LENGTH y ∧
  LENGTH x = LENGTH a``,
  Induct>>rw[]>>
  Cases_on`b`>>TRY(Cases_on`h`)>>Cases_on`c`>>
  fs[map_bitmap_def]>>
  TRY(qpat_assum`A=x` (SUBST_ALL_TAC o SYM))>>
  TRY(qpat_assum`A=y` (SUBST_ALL_TAC o SYM))>>
  fs[LENGTH_NIL]>>
  pop_assum mp_tac>>EVERY_CASE_TAC>>rw[]>>res_tac>>
  fs[]>>DECIDE_TAC)

val dec_stack_length = prove(``
  ∀bs enc orig_stack new_stack.
  dec_stack bs enc orig_stack = SOME new_stack ⇒
  LENGTH orig_stack = LENGTH new_stack``,
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  fs[stackSemTheory.dec_stack_def,LENGTH_NIL]>>rw[]>>
  pop_assum mp_tac>>Cases_on`w`>>fs[full_read_bitmap_def]>>
  EVERY_CASE_TAC>>fs[]>>
  fs[map_bitmap_def]>>rveq>>
  fs[]>>
  rw[]>>
  simp[]>>
  imp_res_tac map_bitmap_length>>
  metis_tac[])

(*TODO: abs_stack changed
val dec_stack_LIST_REL = prove(``
  ∀enc orig_stack new_stack abs_orig abs_new.
  stackSem$dec_stack enc orig_stack = SOME new_stack ∧
  abs_stack orig_stack = SOME abs_orig
  ⇒
  ∃abs_new.
  abs_stack new_stack = SOME abs_new ∧
  LIST_REL (λ(a,b,c) (x,y,z). a = x ∧ b = y ∧ LENGTH c = LENGTH z) abs_orig abs_new``,
  cheat (*
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  rw[stackSemTheory.dec_stack_def]>>
  pop_assum mp_tac>> simp[Once abs_stack_def]>>
  Cases_on`orig_stack = [Word 0w]`>>fs[read_bitmap_def]
  >-
    (fs[Once bit_length_def]>>Cases_on`ts`>>fs[map_bitmap_def]>>
    Cases_on`enc`>>fs[stackSemTheory.dec_stack_def,read_bitmap_def]>>
    qpat_assum`A=new_stack` (SUBST_ALL_TAC o SYM)>>
    fs[Once abs_stack_def]>>rw[]>>
    match_mp_tac quotient_listTheory.LIST_REL_REFL>>
    fs[FORALL_PROD,FUN_EQ_THM]>>metis_tac[])
  >>
    qpat_assum`A = SOME new_stack` mp_tac>>
    ntac 6 FULL_CASE_TAC>>
    fs[]>>
    imp_res_tac map_bitmap_remainder>>
    FULL_CASE_TAC>>fs[]>>rw[]>>
    qabbrev_tac`ls = q'++q''++x`>>
    simp[Once abs_stack_def]>>
    `ls ≠ [] ∧ ls ≠ [Word 0w]` by cheat>>
    imp_res_tac read_bitmap_replace>>
    pop_assum(qspec_then`q''++x` assume_tac)>>fs[]>>
    rfs[]>>
    imp_res_tac map_bitmap_length>>
    pop_assum(SUBST_ALL_TAC o SYM)>>
    fs[DROP_LENGTH_APPEND]>>
    DECIDE_TAC *))

val gc_stack_shape = prove(``
  gc s = SOME s' ∧
  abs_stack (DROP s.stack_space s.stack) = SOME as
  ⇒
  s.stack_space = s'.stack_space ∧
  LENGTH s.stack = LENGTH s'.stack ∧
  ∃as'.
  abs_stack (DROP s.stack_space s'.stack) = SOME as' ∧
  LIST_REL (λ(a,b,c) (x,y,z). a = x ∧ b = y ∧ LENGTH c = LENGTH z) as as'``,
  fs[stackSemTheory.gc_def,LET_THM]>>
  EVERY_CASE_TAC>>rw[]>>
  `s.stack_space ≤ LENGTH s.stack` by DECIDE_TAC>>
  fs[DROP_TAKE_NIL,DROP_APPEND1]
  >-
    (imp_res_tac dec_stack_length>>fs[]>>DECIDE_TAC)
  >>
  metis_tac[dec_stack_LIST_REL,dec_stack_length])

(*Will need a version of this for SOME ... cases*)
val joined_ok_drop = prove(``
  abs_stack ls = SOME x ∧
  ls ≠ [] ∧ ls ≠ [Word 0w] ∧
  read_bitmap ls = SOME (names, bmap , rest) ∧
  join_stacks (StackFrame l NONE::s3.stack) x = SOME j ∧
  joined_ok k j len ⇒
  ∃y j'.
  abs_stack (DROP (LENGTH names) (DROP (LENGTH bmap) ls)) = SOME y ∧
  join_stacks s3.stack y = SOME j' ∧
  joined_ok k j' len
  ``,
  simp[Once abs_stack_def,LET_THM]>>rw[]>>
  qpat_assum`A=SOME x` mp_tac>>
  ntac 2 FULL_CASE_TAC>>rw[]>>fs[]>>
  imp_res_tac read_bitmap_split>>
  fs[DROP_LENGTH_APPEND,join_stacks_def]>>
  qpat_assum`A=SOME j` mp_tac>>FULL_CASE_TAC>>rw[]>>
  fs[joined_ok_def])
*)

(*MEM to an EL characterization for index lists*)
val MEM_index_list_LIM = prove(``
  ∀ls n v k.
  MEM (n,v) (index_list ls k) ⇒
  n-k < LENGTH ls``,
  Induct>>fs[index_list_def]>>rw[]
  >-
    DECIDE_TAC
  >>
  res_tac>>
  DECIDE_TAC)

val MEM_index_list_EL = prove(``
  ∀ls n v.
  MEM (n,v) (index_list ls k) ⇒
  EL (LENGTH ls - (n-k+1)) ls = v``,
  Induct>>fs[index_list_def,FORALL_PROD]>>rw[]>>
  simp[ADD1]>>
  res_tac>>
  fs[]>>
  imp_res_tac MEM_index_list_LIM>>
  `LENGTH ls +1 - (n-k+1) = SUC(LENGTH ls - (n-k+1))` by DECIDE_TAC>>
  pop_assum SUBST_ALL_TAC>>
  simp[])

val filter_bitmap_MEM = prove(``
  ∀b ls ls' x.
  filter_bitmap b ls = SOME (ls',[]) ∧
  MEM x ls' ⇒ MEM x ls``,
  ho_match_mp_tac filter_bitmap_ind>>
  rw[filter_bitmap_def]>>
  EVERY_CASE_TAC>>fs[]>>rveq>>
  fs[MEM])

val alloc_IMP_alloc = prove(
  ``(wordSem$alloc c names (s:('a,'ffi) wordSem$state) = (res:'a result option,s1)) /\
    (∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
    1 ≤ f /\
    state_rel k f f' s t5 lens /\
    state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 (f'::lens) /\
    (cut_env names s.locals = SOME env) /\
    res <> SOME Error ==>
    ?t1 res1.
      (stackSem$alloc c t5 = (res1:'a stackSem$result option,t1)) /\
      if res = NONE then
        res1 = NONE /\ state_rel k f f' s1 t1 lens
      else
        res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) /\
        s1.clock = t1.clock /\ s1.ffi = t1.ffi``,
  Cases_on `FST (alloc c names (s:('a,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fs [] \\ rfs [])
  \\ fs [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fs [push_env_set_store]
  \\ imp_res_tac state_rel_set_store
  \\ pop_assum (mp_tac o Q.SPEC `Word c`) \\ REPEAT STRIP_TAC
  \\ Cases_on `gc (set_store AllocSize (Word c)
                     (push_env env ^nn s with locals := LN))`
  \\ fs [] \\ imp_res_tac gc_state_rel \\ NTAC 3 (POP_ASSUM (K ALL_TAC)) \\ fs []
  \\ pop_assum mp_tac \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [set_store_def,push_env_def]) \\ rpt strip_tac
  \\ fs [] \\ Cases_on `pop_env x` \\ fs []
  \\ Q.MATCH_ASSUM_RENAME_TAC `pop_env s2 = SOME s3`
  \\ `state_rel k f f' s3 t2 lens` by ALL_TAC
  THEN1
    (imp_res_tac gc_s_key_eq>>
    fs[set_store_def]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    rveq>>
    fs[state_rel_def]>>
    fs[pop_env_def]>>rfs[]>>
    `opt = NONE` by
      (Cases_on`opt`>>
      fs[s_key_eq_def,push_env_def,env_to_list_def,LET_THM,s_frame_key_eq_def])>>
    fs[state_component_equality]>>
    qpat_assum`A=SOME t2` mp_tac>>
    simp[stackSemTheory.gc_def]>>
    ntac 5 TOP_CASE_TAC>>fs[stackSemTheory.set_store_def]>>
    strip_tac>>rveq>>fs[]>>
    CONJ_ASM1_TAC>-
      (imp_res_tac dec_stack_length>>
      fs[LENGTH_DROP]>>
      DECIDE_TAC)>>
    CONJ_TAC>-
      (fs[stack_rel_def,LET_THM]>>
      qpat_assum`abs_stack A B C D = E` mp_tac>>
      simp[DROP_APPEND,DROP_TAKE_NIL]>>
      Cases_on`x'`>>simp[abs_stack_def]>>
      ntac 4 TOP_CASE_TAC>>
      Cases_on`f'=0`>>fs[]>>
      rw[]
      >-
        (qpat_assum`A ∧ B ⇒ C` mp_tac>>
        discharge_hyps>-
          (rw[]>-
            DECIDE_TAC>>
          `SUC (LENGTH s3.stack) - (s3.handler+1) =
           SUC(LENGTH s3.stack - (s3.handler+1))` by DECIDE_TAC>>
          fs[])>>
        `s3.handler+1 ≤ LENGTH x''` by
          (imp_res_tac abs_stack_IMP_LENGTH>>
          DECIDE_TAC)>>
        simp[LASTN_CONS])
      >>
        qpat_assum`stack_rel_aux A B C D` mp_tac>>
        fs[stack_rel_aux_def]>>
        simp[])>>
    `f' ≠ 0` by (CCONTR_TAC>>fs[]>>DECIDE_TAC)>>
    fs[]>>rfs[]>>
    fs[stack_rel_def,LET_THM]>>
    qpat_assum`stack_rel_aux A B C D` mp_tac>>
    qpat_assum`A = SOME stack'''` mp_tac>>
    fs[stack_rel_def,LET_THM,DROP_APPEND,DROP_TAKE_NIL]>>
    Cases_on`DROP t5.stack_space t5.stack`>>fs[]
    >- (fs [listTheory.DROP_NIL,DECIDE ``m>=n<=>n<=m:num``] \\ `F` by decide_tac)>>
    qpat_assum`A=SOME x'`mp_tac>>
    Cases_on`q`>>simp[stackSemTheory.dec_stack_def]>>
    ntac 5 TOP_CASE_TAC>>strip_tac>>rveq>>
    fs[abs_stack_def,LET_THM]>>
    TOP_CASE_TAC>>simp[]>>
    strip_tac>>rveq>>
    simp[stack_rel_aux_def]>>
    strip_tac>>
    ntac 3 strip_tac>>
    `n ∈ domain (fromAList l)` by
      metis_tac[domain_lookup]>>
    `n ∈ domain names ∧ n ∈ domain s.locals` by
      (fs[cut_env_def]>>
      `n ∈ domain env` by fs[]>>
      rveq>>
      fs[domain_inter])>>
    res_tac>>simp[]>>
    qpat_assum` ∀n v. A ⇒ B` mp_tac>>
    fs[domain_lookup]>>
    disch_then (qspecl_then [`n`,`v''`] mp_tac)>>fs[]>>
    `~ (n DIV 2 < k)` by DECIDE_TAC>>
    simp[]>>strip_tac>>
    fs[lookup_fromAList]>>
    `MEM (n,v') l` by metis_tac[ALOOKUP_MEM]>>
    `MEM (n DIV 2,v') (MAP_FST adjust_names l)` by
      (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
      metis_tac[])>>
    simp[el_opt_THM]>>
    qpat_abbrev_tac`ls = TAKE A B`>>
    imp_res_tac filter_bitmap_MEM>>
    imp_res_tac MEM_index_list_EL>>
    fs[Abbr`ls`]>>
    pop_assum mp_tac>>
    simp[LENGTH_TAKE]>>
    ` k + LENGTH x'' - n DIV 2 =
      SUC ( k+ LENGTH x'' - (n DIV 2 +1))` by
        DECIDE_TAC>>
    simp[])
  \\ Cases_on `FLOOKUP s3.store AllocSize` \\ fs []
  \\ Cases_on `has_space x s3` \\ fs []
  \\ `s3.store SUBMAP t2.store` by
    (fs [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM] \\ NO_TAC)
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ fs [has_space_def,stackSemTheory.has_space_def]
  \\ EVERY_CASE_TAC \\ fs []
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs [] \\ rw [] \\ fs []
  \\ fs [state_rel_def]);

val compile_result_def = Define`
  (compile_result (Result w1 w2) = Result w1) ∧
  (compile_result (Exception w1 w2) = Exception w1) ∧
  (compile_result TimeOut = TimeOut) ∧
  (compile_result NotEnoughSpace = Halt (Word 1w)) ∧
  (compile_result Error = Error)`;
val _ = export_rewrites["compile_result_def"];

val Halt_EQ_compile_result = prove(
  ``(Halt (Word 1w) = compile_result z <=> z = NotEnoughSpace) /\
    (good_dimindex (:'a) ==> Halt (Word (2w:'a word)) <> compile_result z)``,
  Cases_on `z` \\ fs [] \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]);

val stack_evaluate_add_clock_NONE =
  stackPropsTheory.evaluate_add_clock
  |> Q.SPECL [`p`,`s`,`NONE`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL

val push_locals_def = Define `
  push_locals s = s with <| locals := LN;
    stack := StackFrame (FST (env_to_list s.locals (K I))) NONE :: s.stack |>`

val abs_stack_empty = prove(``
  ∀bs ls stack lens.
  abs_stack bs [] ls lens = SOME stack ⇒ ls = [Word 0w] ∧ lens = []``,
  rpt Cases>>fs[abs_stack_def])

val LASTN_LENGTH_ID2 = prove(``
  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack``,
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID])

val stack_rel_aux_LENGTH = prove(``
  ∀k len xs ys.
  stack_rel_aux k len xs ys ⇒
  LENGTH xs = LENGTH ys``,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>fs[stack_rel_aux_def])

val LASTN_MORE = prove(``
  ∀ls n.
  ¬(n < LENGTH ls) ⇒ LASTN n ls = ls``,
  fs[LASTN_def]>>Induct>>rw[]>>
  Cases_on`n < LENGTH ls`>>
  fs[TAKE_APPEND1,LENGTH_REVERSE]
  >-
    `¬(n < (LENGTH ls))` by DECIDE_TAC
  >>
    res_tac>>
    fs[TAKE_APPEND]>>
    IF_CASES_TAC>>fs[]>>
    DECIDE_TAC)

val stack_rel_aux_LASTN = prove(``
  ∀k len xs ys n.
  stack_rel_aux k len xs ys ⇒
  stack_rel_aux k len (LASTN n xs) (LASTN n ys)``,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>
  fs[stack_rel_aux_def]>>rw[]>>
  imp_res_tac stack_rel_aux_LENGTH
  >-
    fs[LASTN_def,stack_rel_aux_def]
  >>
    Cases_on`n ≤ LENGTH xs`>>rfs[LASTN_CONS]>>
    `¬(n < SUC(LENGTH ys))` by DECIDE_TAC>>
    fs[LASTN_MORE,stack_rel_aux_def])

val abs_stack_to_stack_LENGTH = prove(``
  ∀bs wstack sstack lens stack.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val stack = LENGTH sstack``,
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
val LASTN_LENGTH_BOUNDS = prove(``
  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls``,
  fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]>>rw[]>>
  decide_tac)

val LASTN_CONS_ID = prove(``
  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)``,
  rw[]>>EVAL_TAC>>fs[])

(*Strengthened version of LASTN_DROP after change to make it total*)
val LASTN_DROP2 = prove(``
  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l``,
  Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]
  >-
    `¬ (n ≤ LENGTH l)` by DECIDE_TAC
  >-
    (fs[ADD1]>>
    `LENGTH l +1 - n -1 = LENGTH l -n` by DECIDE_TAC>>
    fs[])
  >-
    (`LENGTH l -n = 0` by DECIDE_TAC >>
    pop_assum SUBST_ALL_TAC>>fs[DROP])
  >>
    `n = LENGTH l` by DECIDE_TAC>>
    simp[])

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
*)
val abs_stack_prefix_drop = prove(``
  ∀bs wstack sstack lens stack h wrest k len.
  h ≤ LENGTH wstack ∧
  LASTN h wstack = wrest ∧
  abs_stack bs wstack sstack lens = SOME stack ∧
  stack_rel_aux k len wstack stack ⇒
  let rest = LASTN h stack in
  let lrest = LASTN h lens in
  let srest = LASTN (handler_val rest) sstack in
  abs_stack bs wrest srest lrest = SOME rest ∧
  stack_rel_aux k len wrest rest``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  rpt strip_tac>>fs[LET_THM,abs_stack_def]
  >-
    (fs[LASTN_def,handler_val_def]>>
    rveq>>
    fs[abs_stack_def,handler_val_def])
  >-
    (qpat_assum`A=SOME stack'`mp_tac>>
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
      qpat_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>>AP_TERM_TAC>>
      qpat_abbrev_tac`length = handler_val A`>>
      Q.ISPECL_THEN [`length`,`DROP(LENGTH x)stack`] assume_tac LASTN_LENGTH_BOUNDS>>
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
    qpat_assum`A=SOME stack'` mp_tac>>
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
      qpat_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>> AP_TERM_TAC>>
      qpat_abbrev_tac`length = handler_val A`>>
      Q.ISPECL_THEN [`length`,`DROP(LENGTH x)t`] assume_tac LASTN_LENGTH_BOUNDS>>
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
      fs[Abbr`frame`,Abbr`ls`,abs_stack_def,LET_THM,full_read_bitmap_def])

val abs_stack_len = prove(``
  ∀bs wstack sstack lens stack handler.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val (LASTN handler stack) ≤ LENGTH sstack``,
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
      DECIDE_TAC))

val EL_REVERSE_REWRITE = prove(``
  ∀l n k. n < LENGTH l ∧ k < n ⇒
  EL (LENGTH l - n + k) l = EL (n-k -1) (REVERSE l)``,
  rw[]>>
  `n-k-1 < LENGTH l` by DECIDE_TAC>>
  fs[EL_REVERSE]>>
  `LENGTH l - (n- k-1) = LENGTH l -n +k +1` by DECIDE_TAC>>
  fs[GSYM ADD1])

val LASTN_LESS = prove(``
  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs``,
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
  fs[LASTN_CONS])

val ALOOKUP_IFF_MEM = prove(
  ``ALL_DISTINCT (MAP FST l) ==>
    (ALOOKUP l q = SOME r <=> MEM (q,r) l)``,
  Induct_on `l` \\ fs [FORALL_PROD,MEM_MAP] \\ rw [] \\ metis_tac []);

val SORTED_CONS_IMP = prove(
  ``SORTED (\x y. FST x > (FST y):num) (h::t) ==>
    ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
    !x. MEM x t ==> FST h > FST x``,
  Induct_on `t` \\ fs [SORTED_DEF] \\ rw []
  \\ `SORTED (\x y. FST x > FST y) (h::t)` by
    (Cases_on `t` \\ fs [SORTED_DEF] \\ decide_tac)
  \\ fs [] \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ disj1_tac \\ decide_tac);

val SORTED_IMP_ALL_DISTINCT_LEMMA = prove(
  ``!l. SORTED (\x y. FST x > (FST y):num) l ==> ALL_DISTINCT (MAP FST l)``,
  Induct \\ fs [] \\ rw [MEM_MAP]
  \\ metis_tac [DECIDE ``m>n ==> m<>n:num``,SORTED_CONS_IMP]);

val MEM_toAList_fromAList = prove(
  ``SORTED (\x y. FST x > (FST y):num) l ==>
    MEM a (toAList (fromAList l)) = MEM a l``,
  Cases_on `a` \\ fs [MEM_toAList,lookup_fromAList] \\ rw []
  \\ imp_res_tac SORTED_IMP_ALL_DISTINCT_LEMMA \\ fs [ALOOKUP_IFF_MEM]);

val SORTED_FST_PERM_IMP_ALIST_EQ = prove(
  ``SORTED (\x y. FST x > FST y) l /\
    SORTED (\x y. FST x > FST y) q /\
    PERM (toAList (fromAList l)) q ==>
    q = l``,
  rw [] \\ drule MEM_PERM \\ fs [MEM_toAList_fromAList]
  \\ pop_assum kall_tac \\ rpt (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Induct_on `q` \\ fs [MEM]
  THEN1 (Cases \\ fs[] \\ metis_tac [])
  \\ Cases_on `l` THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rw []
  \\ imp_res_tac SORTED_CONS_IMP
  \\ `!m n:num. m > n /\ n > m ==> F` by decide_tac
  \\ metis_tac []);

val stack_rel_raise = prove(``
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
           sstack) (LASTN (handler+1) lens) = SOME ((NONE,payload) :: LASTN handler stack)``,
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
    (rator_x_assum `abs_stack` mp_tac>>
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
  CONJ_ASM1_TAC>-
    DECIDE_TAC>>
  rator_x_assum `abs_stack` mp_tac>>
  qpat_abbrev_tac`ls = LASTN A B`>>
  qpat_abbrev_tac`lens' = LASTN A lens`>>
  strip_tac>>
  simp[LASTN_CONS]>>
  qpat_abbrev_tac`w = Word A`>>
  qpat_abbrev_tac`preconds = (h1 < LENGTH rest ∧ B)`>>
  `EL 1 ls = Loc l3 l4
   ∧ (preconds ⇒ EL 2 ls = w)` by
    (rator_x_assum`abs_stack` mp_tac>>
    Cases_on`lens'`>>fs[]>>
    Cases_on`ls`>-simp[abs_stack_def]>>
    Cases_on`h'`>>simp[abs_stack_def,LET_THM]>>
    ntac 7 TOP_CASE_TAC>>fs[])>>
  fs[Abbr`ls`,LASTN_DROP2]>>
  qabbrev_tac`offset = (4+LENGTH h2 +handler_val t)`>>
  (*Using DROP_DROP and more assumptions on the lengths*)
  `n + offset ≤ LENGTH sstack` by
    (first_x_assum(qspec_then`handler+1` mp_tac)>>
    simp[handler_val_def,Abbr`offset`])>>
  `DROP (LENGTH sstack - n - offset) (DROP n sstack) =
   DROP (LENGTH sstack - offset) sstack` by
     simp[DROP_DROP]>>
  `EL 1 (DROP (LENGTH sstack - offset) sstack) = Loc l3 l4 ∧
   (preconds ⇒ EL 2 (DROP (LENGTH sstack - offset) sstack) = w)` by fs[]>>
  `EL (1+(LENGTH sstack - offset)) sstack = Loc l3 l4 ∧
   (preconds ⇒ EL (2+(LENGTH sstack - offset)) sstack = w)` by
     (rw[]>>fs[]>>
     first_x_assum (sym_sub_tac)>>
     rw[]>>match_mp_tac (GSYM EL_DROP)>>
     unabbrev_all_tac>>
     DECIDE_TAC)>>
  CONJ_TAC>-
    (rw[]>>fs[]>>first_x_assum sym_sub_tac>>
    simp[Abbr`offset`])>>
  CONJ_TAC>-
    (rw[]>>fs[]>>first_x_assum sym_sub_tac>>
    simp[Abbr`offset`])>>
  qpat_assum`DROP A stack = C` mp_tac>>
  qpat_assum`LENGTH stack =A` sym_sub_tac>>
  simp[GSYM LASTN_DROP2]>>
  strip_tac >> imp_res_tac LASTN_LESS>>
  simp[]>>
  qpat_assum`abs_stack A B C D = E` mp_tac>>
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
  fs[abs_stack_def,LET_THM])

val EVERY_IMP_EVERY_LASTN = prove(
  ``!xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys``,
  fs [EVERY_MEM] \\ rw [] \\ imp_res_tac MEM_LASTN_ALT \\ res_tac \\ fs []);

val is_tail_call_def = Define `
  (is_tail_call (Call NONE _ [0] NONE) = T) /\
  (is_tail_call _ = F)`

val LASTN_HD = prove(``
  ∀ls x.
  x ≤ LENGTH ls ⇒
  HD (LASTN x ls) =
  EL (LENGTH ls - x) ls``,
  fs[LASTN_def]>>
  Induct>>rw[]>>
  Cases_on`x = SUC(LENGTH ls)`
  >-
    simp[TAKE_APPEND2,REVERSE_APPEND]
  >>
    `x ≤ LENGTH ls` by DECIDE_TAC>>fs[TAKE_APPEND1]>>
    `SUC (LENGTH ls) -x = SUC(LENGTH ls - x)` by DECIDE_TAC>>
    simp[])

val insert_bitmap_isPREFIX = Q.store_thm("insert_bitmap_isPREFIX",
  `∀bs bs' i. insert_bitmap bm bs = (bs',i) ⇒ bs ≼ bs'`,
  Induct
  \\ rw[insert_bitmap_def,LET_THM]
  \\ fs[IS_PREFIX_APPEND]
  \\ split_pair_tac \\ fs[]
  \\ rveq \\ simp[]);

val wLive_isPREFIX = Q.store_thm("wLive_isPREFIX",
  `∀a bs c q bs'. wLive a bs c = (q,bs') ⇒ bs ≼ bs'`,
  rw[]
  \\ PairCases_on`c`
  \\ fs[wLive_def,LET_THM]
  \\ split_pair_tac \\ fs[]
  \\ rw[]
  \\ imp_res_tac insert_bitmap_isPREFIX);

val comp_IMP_isPREFIX = Q.store_thm("comp_IMP_isPREFIX",
  `∀c1 bs r q1 bs'. comp c1 bs r = (q1,bs') ==> bs ≼ bs'`,
  ho_match_mp_tac comp_ind
  \\ rw[comp_def,LET_THM]
  \\ every_case_tac \\ fs[]
  \\ rpt (split_pair_tac >> fs[])
  \\ rveq
  \\ metis_tac[IS_PREFIX_TRANS,wLive_isPREFIX]);

val compile_prog_isPREFIX = prove(
  ``compile_prog x y k bs = (prog,bs1) ==> bs ≼ bs1``,
  fs [compile_prog_def,LET_THM] \\ rw []
  \\ split_pair_tac \\ fs []
  \\ imp_res_tac comp_IMP_isPREFIX
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []);

val compile_word_to_stack_isPREFIX = prove(
  ``!code k bs progs1 bs1.
       compile_word_to_stack k code bs = (progs1,bs1) ==> bs ≼ bs1``,
  Induct \\ fs [compile_word_to_stack_def,FORALL_PROD,LET_THM] \\ rw []
  \\ split_pair_tac \\ fs []
  \\ split_pair_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ imp_res_tac compile_prog_isPREFIX
  \\ imp_res_tac IS_PREFIX_TRANS \\ fs []);

val SND_o_pair_swap = Q.store_thm("SND_o_pair_swap",
  `SND o pair_swap = DIV2 o FST`,
  simp[FUN_EQ_THM,FORALL_PROD,pair_swap_def,DIV2_def]);

val EVEN_DIV2_INJ = Q.store_thm("EVEN_DIV2_INJ",
  `EVEN x ∧ EVEN y ∧ DIV2 x = DIV2 y ⇒ x = y`,
  rw[EVEN_EXISTS,DIV2_def,MULT_COMM]
  \\ fs[MULT_DIV]);

val wMoveAux_thm = Q.store_thm("wMoveAux_thm",
  `evaluate (wMoveAux [] kf,s) = (NONE,s) ∧
   evaluate (wMoveAux (x::xs) kf,s) =
   evaluate (Seq (wMoveSingle x kf) (wMoveAux xs kf), s)`,
  rw[wMoveAux_def] >- rw[stackSemTheory.evaluate_def]
  \\ Cases_on`xs` >> rw[wMoveAux_def]
  \\ rw[stackSemTheory.evaluate_def]
  \\ rw[]);

val with_same_locals = save_thm("with_same_locals[simp]",
  EQT_ELIM(SIMP_CONV(srw_ss())[state_component_equality]``s with locals := s.locals = (s:('a,'b) wordSem$state)``));

val state_rel_get_var_imp = Q.store_thm("state_rel_get_var_imp",
  `state_rel k f f' s t lens ∧ get_var (x * 2) s = SOME v ∧ x < k ⇒ FLOOKUP t.regs x = SOME v`,
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ first_x_assum drule
  \\ simp[EVEN_MULT]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ rw[]);

val state_rel_get_var_imp2 = Q.store_thm("state_rel_get_var_imp2",
  `state_rel k f f' s t lens ∧
  get_var (x * 2) s = SOME v ∧
  ¬(x < k)
  ⇒
  (EL (t.stack_space + (f + k - (x + 1))) t.stack = v)`,
  simp[state_rel_def]
  \\ strip_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ first_x_assum drule
  \\ simp[EVEN_MULT]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ simp[el_opt_THM]
  \\ strip_tac
  \\ rator_x_assum`EL`mp_tac
  \\ simp[EL_TAKE]
  \\ simp[EL_DROP]
  \\ simp[ADD_COMM]);

val state_rel_set_var_k = Q.store_thm("state_rel_set_var_k[simp]",
  `(state_rel k f f' s (set_var (k+1) v t) lens ⇔ state_rel k f f' s t lens) ∧
   (state_rel k f f' s (set_var k v t) lens ⇔ state_rel k f f' s t lens)`,
  conj_tac
  \\ simp[state_rel_def,EQ_IMP_THM,stackSemTheory.set_var_def]
  \\ ntac 2 strip_tac
  \\ fs[FLOOKUP_UPDATE]
  \\ metis_tac[DECIDE``¬(k + 1n < k) ∧ ¬(k < k)``]);

val state_rel_set_var = Q.store_thm("state_rel_set_var",
   `state_rel k f f' s t lens ∧ x < k ⇒
    state_rel k f f' (set_var (2*x) v s) (set_var x v t) lens`,
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ strip_tac
  \\ fs[lookup_insert,FLOOKUP_UPDATE]
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
  \\ fs[EVEN_MOD2]);

val state_rel_set_var2 = Q.store_thm("state_rel_set_var2",
   `state_rel k f f' s t lens ∧ ¬(x < k) ∧ 0 < f ∧ x < f' + k ∧ st = t.stack ∧ sp = t.stack_space ⇒
    state_rel k f f' (set_var (2*x) v s)
    (t with stack := LUPDATE v (sp + (f + k − (x + 1))) st) lens`,
  simp[state_rel_def,stackSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ strip_tac
  \\ fs[lookup_insert,FLOOKUP_UPDATE]
  \\ simp[DROP_LUPDATE]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp[]
  >- (
    simp[EVEN_MULT]
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ simp[MULT_DIV]
    \\ strip_tac >> rveq
    \\ simp[el_opt_THM]
    \\ simp[EL_LUPDATE])
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ IF_CASES_TAC >> fs[]
  \\ simp[el_opt_THM]
  \\ simp[EL_LUPDATE]
  \\ fs[EVEN_EXISTS]
  \\ rveq
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ fs [el_opt_THM]
  \\ rveq
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ ntac 2 (pop_assum mp_tac)
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ ntac 2 strip_tac
  \\ rw[]
  \\ fsrw_tac[ARITH_ss][]);

val wMoveSingle_thm = Q.store_thm("wMoveSingle_thm",
  `state_rel k f f' s t lens ∧ 0 < f ∧
   (case x of NONE => get_var (k+1) t = SOME v
    | SOME x => get_var (x * 2) s = SOME v ) ∧
   (case y of SOME x => x < f' + k | _ => T)
   ⇒
   ∃t'.
     evaluate (wMoveSingle (format_result k (y,x)) (k,f,f'), t) = (NONE,t') ∧
     state_rel k f f' (case y of NONE => s | SOME y => set_var (y*2) v s) t' lens ∧
     (y = NONE ⇒ get_var (k+1) t' = SOME v) ∧
     (y ≠ NONE ⇒ get_var (k+1) t' = get_var (k+1) t)`,
  rw[format_result_def,wMoveSingle_def]
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
    \\ IF_CASES_TAC >- fsrw_tac[ARITH_ss][state_rel_def]
    \\ simp[]
    \\ imp_res_tac state_rel_get_var_imp2 )
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    >- (
      fs[stackSemTheory.get_var_def]
      \\ conj_tac
      >- (match_mp_tac state_rel_set_var
          \\ simp[] )
      \\ simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE] )
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC >- fsrw_tac[ARITH_ss][state_rel_def]
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
    \\ (IF_CASES_TAC >- fsrw_tac[ARITH_ss][state_rel_def])
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
      \\ rpt(qpat_assum`¬(_ < k)`mp_tac)
      \\ simp_tac (srw_ss()++ARITH_ss)[]
      \\ ntac 2 strip_tac
      \\ imp_res_tac state_rel_get_var_imp2
      \\ rveq
      \\ reverse conj_tac
      >- (
        EVAL_TAC \\ rw[]
        \\ `F` by decide_tac )
      \\ match_mp_tac state_rel_set_var2
      \\ simp[])))

val IS_SOME_get_vars_set_var = Q.store_thm("IS_SOME_get_vars_set_var",
  `∀ls s.
    IS_SOME (get_vars ls s) ⇒
    IS_SOME (get_vars ls (set_var k v s))`,
  Induct \\ simp[get_vars_def]
  \\ rw[] \\ every_case_tac \\ fs[IS_SOME_EXISTS,PULL_EXISTS]
  \\ rpt (pop_assum mp_tac)
  \\ EVAL_TAC \\ simp[lookup_insert] \\ rw[]
  \\ res_tac \\ fs[]);

val evaluate_wMoveAux_seqsem = Q.store_thm("evaluate_wMoveAux_seqsem",
  `∀ms s t r.
   state_rel k f f' s t lens ∧ 0 < f ∧
   (* these two probably need to be ⇔ *)
   (∀i v. r (SOME i) = SOME v ⇒ get_var (2*i) s = SOME v) ∧
   (∀v. r NONE = SOME v ⇒ get_var (k+1) t = SOME v) ∧
   (∀v. r (SOME v) ≠ NONE) ∧
   IS_SOME (get_vars (MAP ($* 2 o THE) (FILTER IS_SOME (MAP SND ms))) s) ∧
   (case find_index NONE (MAP SND ms) 0 of
    | NONE => T
    | SOME i =>
      case find_index NONE (MAP FST ms) 0 of
      | NONE => IS_SOME (r NONE)
      | SOME j => i ≤ j ⇒ IS_SOME (r NONE)) ∧
   EVERY (λ(x,y). ∀a. (x = SOME a ∨ y = SOME a) ⇒ a < f' + k) ms ∧
   (* this is for a seqsem lemma (unstated) *)
   ALL_DISTINCT (MAP FST ms)
   ⇒
   ∃t'.
     evaluate (wMoveAux (MAP (format_result k) ms) (k,f,f'),t) = (NONE,t') ∧
     state_rel k f f'
       (set_vars
         (MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
         (MAP THE (MAP (seqsem (MAP (λ(x,y). (y,x)) ms) r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
         s) t' lens`,
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
  \\ qmatch_assum_abbrev_tac`Abbrev(wms = _ (_ (y,x)))`
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
  \\ discharge_hyps
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
        \\ res_tac \\ fs[] )
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
      rw[]
      \\ qpat_assum`option_CASE (find_index _ _ _) _ _`mp_tac
      \\ simp[find_index_def]
      \\ IF_CASES_TAC \\ simp[]
      >- (
        BasicProvers.CASE_TAC \\ simp[IS_SOME_EXISTS] \\ rw[] \\ rw[] )
      \\ strip_tac
      \\ metis_tac[option_CASES,NOT_SOME_NONE] )
    \\ conj_tac
    >- (
      qpat_assum`IS_SOME _`mp_tac
      \\ reverse IF_CASES_TAC \\ fs[get_vars_def]
      >- (
        BasicProvers.CASE_TAC \\ simp[]
        \\ metis_tac[IS_SOME_get_vars_set_var] )
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ metis_tac[IS_SOME_get_vars_set_var,IS_SOME_EXISTS])
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ qpat_assum`option_CASE (find_index _ _ _) _ _`mp_tac
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
      \\ rfs[] )
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
  \\ cheat);

val comp_correct = store_thm("comp_correct",
  ``!(prog:'a wordLang$prog) (s:('a,'ffi) wordSem$state) k f f' res s1 t bs lens.
      (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
      state_rel k f f' s t lens /\ post_alloc_conventions k prog /\
      max_var prog <= 2 * f' + 2 * k /\
      (~(is_tail_call prog) ==> 1 <= f /\ SND (comp prog bs (k,f,f')) ≼ t.bitmaps) ==>
      ?ck t1 res1.
        (stackSem$evaluate (FST (comp prog bs (k,f,f')),t with clock := t.clock + ck) = (res1,t1)) /\
        if OPTION_MAP compile_result res <> res1
        then res1 = SOME (Halt (Word 2w)) /\
             t1.ffi.io_events ≼ s1.ffi.io_events /\
             (IS_SOME t1.ffi.final_event ==> t1.ffi = s1.ffi)
        else
          case res of
          | NONE => state_rel k f f' s1 t1 lens
          (*lens might be wrong*)
          | SOME (Result _ _) => state_rel k 0 0 s1 t1 lens
          | SOME (Exception _ _) => state_rel k 0 0 (push_locals s1) t1 (LASTN (s.handler+1) lens)
          | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [is_tail_call_def]
  THEN1 (* Skip *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw [])
  THEN1 (* Alloc *)
   (qexists_tac `0`
    \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `n = 2` by (fs [convs_def]) \\ rw []
    \\ Cases_on `get_var 2 s` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ `t.use_alloc /\ (get_var 1 t = SOME (Word c))` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
    \\ Cases_on `cut_env names s.locals`
    THEN1 fs [wordSemTheory.alloc_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `cut_env names s.locals = SOME env`
    \\ Cases_on `wLive names bs (k,f,f')`
    \\ qcase_tac `wLive names bs (k,f,f') = (wlive_prog,bs1)`
    \\ drule evaluate_wLive
    \\ discharge_hyps_keep
    THEN1
      (fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
      fs[GSYM toAList_domain,EVERY_MEM]>>
      fs[X_LE_DIV,reg_allocTheory.is_phy_var_def,LET_THM]>>
      rw[]>>res_tac>>DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ `1 < k` by fs [state_rel_def] \\ res_tac
    \\ fs [stackSemTheory.evaluate_def,LET_THM]
    \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
    \\ Cases_on `alloc c t5` \\ fs []
    \\ qcase_tac `alloc c t5 = (res1,t1)` \\ fs []
    \\ drule alloc_IMP_alloc \\ discharge_hyps >- (fs[])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [] \\ Cases_on `res = NONE` \\ fs [])
  THEN1 (* Move *) (
    simp[comp_def]
    \\ fs[evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq
    \\ simp[]
    \\ qabbrev_tac`mvs = MAP pair_swap moves`
    \\ `windmill mvs`
    by (
      simp[parmoveTheory.windmill_def,Abbr`mvs`]
      \\ simp[MAP_MAP_o,SND_o_pair_swap]
      \\ simp[GSYM MAP_MAP_o]
      \\ match_mp_tac ALL_DISTINCT_MAP_INJ
      \\ rw[]
      \\ match_mp_tac EVEN_DIV2_INJ \\ simp[]
      \\ rator_x_assum`post_alloc_conventions`mp_tac
      \\ simp[convs_def,EVERY_MEM,reg_allocTheory.is_phy_var_def,EVEN_MOD2] )
    \\ simp[wMove_def]

    \\ cheat)
  THEN1 (* Inst *) cheat
  THEN1 (* Assign *) cheat
  THEN1 (* Get *) cheat
  THEN1 (* Set *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [state_rel_def,wordSemTheory.dec_clock_def,stackSemTheory.dec_clock_def])
  THEN1 (* Seq *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
    \\ split_pair_tac \\ fs []
    \\ split_pair_tac \\ fs []
    \\ split_pair_tac \\ fs []
    \\ `max_var c1 <= 2 * f' + 2 * k /\ max_var c2 <= 2 * f' + 2 * k` by
      (fs [word_allocTheory.max_var_def] \\ decide_tac)
    \\ `post_alloc_conventions k c1 /\
        post_alloc_conventions k c2` by fs [convs_def]
    \\ imp_res_tac comp_IMP_isPREFIX
    \\ `SND (comp c1 bs (k,f,f')) ≼ t.bitmaps /\
        SND (comp c2 bs' (k,f,f')) ≼ t.bitmaps` by
         (fs [] \\ imp_res_tac IS_PREFIX_TRANS)
    \\ reverse (Cases_on `res' = NONE`) \\ fs [] \\ rpt var_eq_tac
    THEN1
     (first_x_assum drule \\ fs [] \\ rw [] \\ fs []
      \\ `¬is_tail_call c1 ⇒ SND (comp c1 bs (k,f,f')) ≼ t.bitmaps` by fs []
      \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
      \\ qexists_tac `ck` \\ fs [] \\ Cases_on `res` \\ fs []
      \\ Cases_on `res1 = NONE`
      \\ fs [stackSemTheory.evaluate_def,LET_THM])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ `¬is_tail_call c1 ⇒ SND (comp c1 bs (k,f,f')) ≼ t.bitmaps` by fs []
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
    \\ `¬is_tail_call c2 ⇒ SND (comp c2 bs' (k,f,f')) ≼ t1.bitmaps` by
         (imp_res_tac stackPropsTheory.evaluate_consts \\ fs [])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ fs [stackSemTheory.evaluate_def,LET_THM]
    \\ imp_res_tac stack_evaluate_add_clock_NONE \\ fs []
    \\ pop_assum (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    (*Not sure if already proved, handler is unchanged when
    result is NONE*)
    \\ `s.handler = s1'.handler` by cheat>>
    fs[])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,wReg1_def]
    \\ Cases_on `get_var n s` \\ fs []
    \\ Cases_on `get_var m s` \\ fs [] \\ rw []
    \\ Cases_on `x` \\ fs []
    \\ qcase_tac `get_var n s = SOME (Loc l1 l2)`
    \\ fs [wStackLoad_def] \\ fs [convs_def] \\ rw []
    \\ fs [reg_allocTheory.is_phy_var_def,word_allocTheory.max_var_def]
    \\ `t.use_stack /\ ~(LENGTH t.stack < t.stack_space + f) /\
        t.stack_space <= LENGTH t.stack` by
     (fs [state_rel_def] \\ decide_tac) \\ fs [LET_DEF]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    THEN1
     (`(get_var (n DIV 2) t = SOME (Loc l1 l2)) /\ (get_var 1 t = SOME x')` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
      \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF]
      \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
             fromList2_def,lookup_def]
      \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ imp_res_tac DROP_DROP \\ fs [])
    \\ `~(LENGTH t.stack < t.stack_space + (f -1 - (n DIV 2 - k))) /\
        (EL (t.stack_space + (f -1 - (n DIV 2 - k))) t.stack = Loc l1 l2) /\
        (get_var 1 t = SOME x')` by
     (fs [state_rel_def,get_var_def,LET_DEF]
      \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
      \\ fs [stackSemTheory.get_var_def]
      \\ imp_res_tac el_opt_TAKE_IMP
      \\ fs [el_opt_DROP] \\ fs [el_opt_THM] \\
      qpat_abbrev_tac `A=f-1-B`>>
      rw[]>>DECIDE_TAC)
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
    \\ fs [AC ADD_ASSOC ADD_COMM]
    \\ imp_res_tac DROP_DROP \\ fs [])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def]
    \\ qpat_assum `xxx = (aa,bb)` mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ pop_assum mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ qexists_tac `1`
    \\ qcase_tac `LASTN (s.handler + 1) s.stack =
          StackFrame l (SOME (h1,l3,l4))::rest`
    \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,jump_exc_def,
        stackSemTheory.find_code_def]
    \\ `lookup 5 t.code = SOME (raise_stub k)` by fs [state_rel_def] \\ fs []
    \\ pop_assum kall_tac
    \\ fs [stackSemTheory.dec_clock_def,raise_stub_def,word_allocTheory.max_var_def]
    \\ fs [state_rel_def,LET_DEF,push_locals_def,stackSemTheory.evaluate_def,LET_THM]
    \\ fs [DROP_DROP_EQ] \\ fs [stack_rel_def]
    \\ qpat_assum` A ⇒ B` mp_tac
    \\ discharge_hyps>-
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
         (imp_res_tac stack_rel_raise \\
         pop_assum mp_tac >>
         ntac 16 (pop_assum kall_tac)>>
         discharge_hyps>-
           DECIDE_TAC>>
         discharge_hyps>-
            simp[]>>
         rw[]>>
         decide_tac)
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,stackSemTheory.set_store_def]
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,push_locals_def,lookup_def]
    \\ imp_res_tac stack_rel_raise \\
    pop_assum mp_tac >>
    ntac 32 (pop_assum kall_tac)>>
    discharge_hyps>- DECIDE_TAC>>
    discharge_hyps >- simp[]>>
    rw[] >>
    fs [FLOOKUP_UPDATE]>>
    rfs[]
    \\ conj_tac THEN1
     (fs [sorted_env_def] \\ Cases_on `env_to_list (fromAList l) (K I)`
      \\ imp_res_tac env_to_list_K_I_IMP \\ fs [])
    \\ conj_tac >-
       (imp_res_tac LASTN_LENGTH_BOUNDS
       \\imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
       \\imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [])
    \\ rw[]>>
    Cases_on`h1+1 = SUC (LENGTH rest)`>-
      fs[is_handler_frame_def]>>
    `h1 < LENGTH rest ∧
    SUC(LENGTH rest) - (h1+1) = SUC(LENGTH rest - (h1+1))` by DECIDE_TAC>>
    fs[]
    \\ rfs[]
    \\ `h1 <= LENGTH (LAST_N (s.handler+1) stack)` by all_tac
    \\ fs [LASTN_CONS]
    \\ imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
    >-
      DECIDE_TAC
    >>
      simp[LASTN_CONS])
  THEN1 (* If *) cheat
  THEN1 (* FFI *)
   (fs [EVAL ``post_alloc_conventions k (FFI ffi_index ptr len names)``]
    \\ rw [] \\ fs [] \\ rw []
    \\ fs [wordSemTheory.evaluate_def]
    \\ qpat_assum `aaa = (res,s1)` mp_tac
    \\ rpt (ntac 2 (TOP_CASE_TAC \\ fs []))
    \\ fs [LET_DEF] \\ split_pair_tac \\ fs [] \\ rw [] \\ fs []
    \\ fs [comp_def,stackSemTheory.evaluate_def]
    \\ fs [stackSemTheory.get_var_def]
    \\ `FLOOKUP t.regs 1 = get_var 2 s /\
        FLOOKUP t.regs 2 = get_var 4 s` by cheat \\ fs []
    \\ `t.be = s.be /\ t.mdomain = s.mdomain /\
        s.memory = t.memory /\ s.ffi = t.ffi` by
          fs [state_rel_def] \\ fs [LET_THM]
    \\ qexists_tac `0` \\ fs []
    \\ fs [state_rel_def,LET_THM]
    \\ ntac 3 strip_tac
    \\ fs [cut_env_def] \\ rpt var_eq_tac
    \\ fs [lookup_inter_alt]
    \\ fs [CONV_RULE (DEPTH_CONV ETA_CONV) (GSYM toAList_def)
           |> INST_TYPE [``:'a``|->``:unit``] |> SIMP_RULE (srw_ss()) []]
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,DIV_LT_X,FORALL_PROD,MEM_toAList]
    \\ fs [domain_lookup] \\ res_tac
    \\ `~(n < k * 2)` by decide_tac \\ fs [])
  \\ (* Call *) cheat);

val make_init_def = Define `
  make_init (t:('a,'ffi)stackSem$state) code =
    <| locals  := LN
     ; store   := t.store \\ Handler
     ; stack   := []
     ; memory  := t.memory
     ; mdomain := t.mdomain
     ; permute := K I
     ; gc_fun  := t.gc_fun
     ; handler := 0
     ; clock   := t.clock
     ; code    := code
     ; be      := t.be
     ; ffi     := t.ffi |> `;

val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,CallAny_def]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       word_allocTheory.list_max_def,is_tail_call_def,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0] NONE)``,
       word_allocTheory.max_var_def,LET_DEF,word_allocTheory.max2_def] |> GEN_ALL

val comp_Call = prove(
  ``∀start (s:('a,'ffi) wordSem$state) k res s1 t lens.
      evaluate (Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
      res ≠ SOME Error /\ state_rel k 0 0 s t lens ⇒
      ∃ck t1 res1.
        evaluate (Call NONE (INL start) NONE,t with clock := t.clock + ck) =
        (res1,t1) /\ 1w <> (0w:'a word) /\ 2w <> (0w:'a word) /\
        if lift compile_result res = res1 then
          s1.ffi = t1.ffi /\ s1.clock = t1.clock
        else
          res1 = SOME (Halt (Word 2w)) /\
          t1.ffi.io_events ≼ s1.ffi.io_events /\
          (IS_SOME t1.ffi.final_event ⇒ t1.ffi = s1.ffi)``,
  rw [] \\ drule comp_Call_lemma \\ fs []
  \\ disch_then drule \\ fs [] \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ conj_tac THEN1 (fs [state_rel_def,good_dimindex_def,dimword_def])
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs [state_rel_def,push_locals_def,LET_DEF]);

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel a 0 0 s t lens ⇒ state_rel a 0 0 (s with clock := k) (t with clock := k) lens`,
  rw[state_rel_def]);

val s = ``(s:(α,'ffi)wordSem$state)``;
val s' = ``(s:(α,'ffi)stackSem$state)``;
val clock_simps =
  LIST_CONJ [
    EVAL``(^s with clock := c).clock``,
    EVAL``(^s with clock := c) with clock := d``,
    EVAL``(^s' with clock := c).clock``,
    EVAL``(^s' with clock := c) with clock := d``];

val state_rel_IMP_semantics = Q.store_thm("state_rel_IMP_semantics",
  `state_rel k 0 0 ^s t lens /\ semantics s start <> Fail ==>
   semantics start t IN extend_with_resource_limit { semantics s start }`,
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
      rator_x_assum`wordSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k''`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      drule comp_Call >> fs[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      discharge_hyps >- ( strip_tac >> fs[] ) >>
      drule(GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k''`strip_assume_tac) >> fs[] >>
      disch_then drule >> simp[] >>
      Cases_on`q`>>fs[]>>
      strip_tac >>
      qpat_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >> fs[] >>
      drule (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >>
      simp[] >> strip_tac >> rveq >> fs[] >>
      every_case_tac >> fs[] >> rveq >> fs[]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[extend_with_resource_limit_def] >> fs[] >>
      Cases_on`t'.ffi.final_event`>>fs[] >- (
        Cases_on`r`>>fs[] >> rveq >>
        drule(GEN_ALL wordPropsTheory.evaluate_add_clock)>>
        simp[RIGHT_FORALL_IMP_THM] >>
        discharge_hyps >- (strip_tac >> fs[]) >>
        disch_then(qspec_then`k''`mp_tac)>>simp[]>>strip_tac>>
        drule comp_Call >>
        simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
        discharge_hyps >- (strip_tac >> fs[]) >>
        drule (GEN_ALL state_rel_with_clock) >> simp[] >>
        disch_then(qspec_then`k'+k''`mp_tac)>>simp[]>>strip_tac>>
        disch_then drule>>
        simp[]>>strip_tac>>
        `t''.ffi.io_events ≼ t1.ffi.io_events ∧
         (IS_SOME t''.ffi.final_event ⇒ t1.ffi = t''.ffi)` by (
           qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t'')` >>
           Q.ISPECL_THEN[`exps`,`tt`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
           fs[Abbr`tt`] >>
           disch_then(qspec_then`k'+ck`mp_tac)>>simp[]) >>
        first_x_assum(qspec_then`k''`mp_tac)>>simp[]>>
        strip_tac >> fs[] >- (
          Cases_on`t''.ffi.final_event`>>fs[]>>
          `t'.ffi = t''.ffi` by (every_case_tac >> fs[]) >>
          fs[]) >>
        rator_x_assum`stackSem$evaluate`mp_tac >>
        drule(GEN_ALL stackPropsTheory.evaluate_add_clock) >>
        simp[] >>
        disch_then(qspec_then`ck+k'`mp_tac) >>
        simp[] >>
        ntac 2 strip_tac >>
        rveq >> fs[] >>
        every_case_tac >> fs[] >> rw[] ) >>
      `∃r s'.
        evaluate
          (Call NONE (SOME start) [0] NONE, s with clock := (k' + k'')) = (r,s') ∧
        s'.ffi = t'.ffi` by (
          srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
          metis_tac[wordPropsTheory.evaluate_add_clock_io_events_mono,SND,
                    IS_SOME_EXISTS,
                    clock_simps
                    ]) >>
      drule comp_Call >>
      simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (
        last_x_assum(qspec_then`k'+k''`mp_tac)>>rw[]>>
        strip_tac>>fs[])>>
      drule(GEN_ALL state_rel_with_clock)>>simp[]>>
      disch_then(qspec_then`k'+k''`mp_tac)>>simp[]>>strip_tac>>
      disch_then drule>>
      simp[]>>strip_tac>>
      `t''.ffi.io_events ≼ t1.ffi.io_events ∧
       (IS_SOME t''.ffi.final_event ⇒ t1.ffi = t''.ffi)` by (
        qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t'')` >>
        Q.ISPECL_THEN[`exps`,`tt`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
        fs[Abbr`tt`] >>
        disch_then(qspec_then`k'+ck`mp_tac)>>simp[]) >>
      reverse(Cases_on`t''.ffi.final_event`)>>fs[] >- (
        `t'.ffi = t''.ffi` by (every_case_tac >> fs[]) >>
        fs[] ) >>
      first_x_assum(qspec_then`k''`mp_tac)>>simp[]>>
      strip_tac >> fs[]>>
      rator_x_assum`stackSem$evaluate`mp_tac >>
      drule(GEN_ALL stackPropsTheory.evaluate_add_clock) >>
      disch_then(qspec_then`k'+ck`mp_tac) >>
      simp[] >> strip_tac >>
      TRY strip_tac >> fs[] >>
      spose_not_then strip_assume_tac >> fs[] >>
      rveq >> fs[] >>
      every_case_tac>>fs[]>>rveq>>rfs[]) >>
    rw[] >> fs[] >>
    drule comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- (
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      rw[] >> strip_tac >> fs[] ) >>
    drule(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule >>
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
    drule comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- ( strip_tac >> fs[] ) >>
    drule(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`FST p ≠ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule (GEN_ALL stackPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    discharge_hyps >- (strip_tac >> fs[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    simp[] >> rw[] >> fs[] >>
    every_case_tac >> fs[] >> rw[] >> fs[]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[extend_with_resource_limit_def] >> fs[] >>
    qpat_assum`∀x y. _`(qspec_then`k'`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule comp_Call >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- (
      strip_tac >> fs[] >>
      last_x_assum(qspec_then`k'`mp_tac) >>
      simp[] ) >>
    drule(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule >>
    simp[] >> strip_tac >>
    `t'.ffi.io_events ≼ t1.ffi.io_events ∧
     (IS_SOME t'.ffi.final_event ⇒ t1.ffi = t'.ffi)` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
      fs[Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    fs[] >>
    first_assum(qspec_then`k'`mp_tac) >>
    first_x_assum(qspec_then`k'+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][] >>
    rator_x_assum`stackSem$evaluate`mp_tac >>
    drule(GEN_ALL stackPropsTheory.evaluate_add_clock)>>
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
    drule build_lprefix_lub_thm >>
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
    drule comp_Call >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    discharge_hyps >- (
      last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
      strip_tac >> fs[] ) >>
    drule(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k'`strip_assume_tac) >>
    disch_then drule >>
    simp[] >> strip_tac >>
    qexists_tac`k'+ck`>>simp[]>>
    pop_assum mp_tac >>
    IF_CASES_TAC >> simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspec_then`ck+k'`mp_tac)>>simp[]>>
    BasicProvers.TOP_CASE_TAC >> simp[]) >>
  (fn g => subterm (fn tm => Cases_on`^(replace_term(#1(dest_exists(#2 g)))(``k':num``)(assert(has_pair_type)tm))`) (#2 g) g) >>
  drule comp_Call >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  discharge_hyps >- (
    last_x_assum(qspec_then`k'`mp_tac)>>rw[]>>
    strip_tac >> fs[] ) >>
  drule(state_rel_with_clock) >>
  simp[] >> strip_tac >>
  disch_then drule >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (evaluate (exps,ss))).ffi.io_events` >>
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
  simp[EL_APPEND1]);

val init_state_ok_def = Define `
  init_state_ok k (t:('a,'ffi)stackSem$state) <=>
    1n < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    t.stack_space <= LENGTH t.stack /\
    t.use_stack /\ t.use_store /\ t.use_alloc /\ gc_fun_ok t.gc_fun /\
    t.stack_space <= LENGTH t.stack /\
    LENGTH t.bitmaps + 1 < dimword (:'a) /\
    [4w] ≼ t.bitmaps /\
    LENGTH t.stack < dimword (:'a) /\
    DROP t.stack_space t.stack = [Word 0w] /\
    FLOOKUP t.store Handler = SOME (Word (n2w (LENGTH t.stack - 2)))`

val init_state_ok_IMP_state_rel = prove(
  ``lookup 5 t.code = SOME (raise_stub k) /\
    (!n word_prog arg_count.
       (lookup n code = SOME (arg_count,word_prog)) ==>
       ?bs bs2 stack_prog.
         word_to_stack$compile_prog word_prog arg_count k bs = (stack_prog,bs2) /\
         isPREFIX bs2 t.bitmaps /\
         (lookup n t.code = SOME stack_prog)) /\
    init_state_ok k t ==>
    state_rel k 0 0 (make_init t code) (t:('a,'ffi)stackSem$state) []``,
  fs [state_rel_def,make_init_def,LET_DEF,lookup_def,init_state_ok_def] \\ rw []
  \\ fs [stack_rel_def,sorted_env_def,abs_stack_def,LET_THM]
  \\ fs [handler_val_def,LASTN_def,stack_rel_aux_def]
  \\ fs [filter_bitmap_def,MAP_FST_def,index_list_def]
  \\ fs[flookup_thm] \\ every_case_tac \\ fs [] \\ decide_tac);

val init_state_ok_semantics =
  state_rel_IMP_semantics |> Q.INST [`s`|->`make_init t code`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val compile_word_to_stack_IMP_ALOOKUP = prove(
  ``!code k bs progs bitmaps n arg_count word_prog x.
      compile_word_to_stack k code bs = (progs,bitmaps) /\
      ALOOKUP code n = SOME (arg_count,word_prog) /\
      bitmaps ≼ x ⇒
      ∃bs bs2 stack_prog.
        compile_prog word_prog arg_count k bs = (stack_prog,bs2) ∧
        bs2 ≼ x ∧ ALOOKUP progs n = SOME stack_prog``,
  Induct \\ fs [] \\ strip_tac \\ PairCases_on `h`
  \\ fs [compile_word_to_stack_def] \\ rw [] \\ fs [LET_THM]
  \\ split_pair_tac \\ fs []
  \\ split_pair_tac \\ fs [] \\ rw []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  THEN1 (asm_exists_tac \\ fs [] \\ imp_res_tac IS_PREFIX_TRANS)
  \\ first_x_assum match_mp_tac
  \\ asm_exists_tac \\ fs []);

val compile_semantics = store_thm("compile_semantics",
  ``(t:(α,'ffi)stackSem$state).code = fromAList (SND (compile asm_conf code)) /\
    init_state_ok (asm_conf.reg_count - 4) t /\ (ALOOKUP code 5 = NONE) /\
    (FST (compile asm_conf code)).bitmaps ≼ t.bitmaps /\
    semantics (make_init t (fromAList code)) start <> Fail ==>
    semantics start t IN
    extend_with_resource_limit {semantics (make_init t (fromAList code)) start}``,
  qabbrev_tac `k = asm_conf.reg_count - 4`
  \\ rw [compile_def] \\ match_mp_tac (GEN_ALL init_state_ok_semantics)
  \\ qexists_tac `k` \\ fs []
  \\ fs [compile_word_to_stack_def,lookup_fromAList,LET_THM] \\ rw [] \\ fs []
  THEN1 (split_pair_tac \\ fs [])
  \\ Cases_on `n=5` \\ fs []
  \\ split_pair_tac \\ fs []
  \\ match_mp_tac compile_word_to_stack_IMP_ALOOKUP
  \\ metis_tac []);

val _ = export_theory();
