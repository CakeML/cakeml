(*
  fixed size oprations on bitstrings
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open integerTheory arithmeticTheory integer_wordTheory;
open metisLib;
open fcpTheory;
open listTheory;
open combinTheory;
open bitstringLib;

val _ = numLib.prefer_num();

val _ = new_theory "bitstring_extra"

val fixadd_def = Define`
   fixadd a b =
     let m = MAX (LENGTH a) (LENGTH b) in
        fixwidth m (n2v (v2n a + v2n b))`

(* subtraction is negate b and add a, then add 1 *)

val fixsub_def = Define`
   (fixsub [] [] =  []) /\
   (fixsub a b =
     let m = MAX (LENGTH a) (LENGTH b) in
     let fa = fixwidth m a in
     let fb = fixwidth m b
      in
        fixadd (fixadd fa (bnot fb)) (fixwidth m (n2v 1)))`
(*
val fixadd_def2 = Define`
   (fixadd2 [] [] = []) /\
   (fixadd2 a b =
     let m = LENGTH a in
     let fa = fixwidth m a in
     let fb = fixwidth m b in
        fixwidth m (n2v (v2n a + v2n b)))`
*)
(* makes the proofs simpler *)
(* TODO prove properties of fixadd and fixsub *)

val fixadd_comm = Q.store_thm("fixadd_comm",
  `!x y. fixadd x y = fixadd y x`,
  REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> FULL_SIMP_TAC arith_ss [MAX_COMM]
);

val fixadd_length = Q.store_thm("fixadd_length",
  `!x y. LENGTH (fixadd x y) = MAX (LENGTH x) (LENGTH y)`,
   REPEAT STRIP_TAC >> simp [fixadd_def]);


val fixadd_assoc = Q.store_thm("fixadd_assoc",
  `!x y z. fixadd (fixadd x y) z = fixadd x (fixadd y z)`,
  (REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> simp[fixadd_length]) >> cheat);


val fixadd_word_add2 = Q.store_thm("fixadd_word_add2",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y))
     ==> (v2n (fixadd x y) = w2n (word_add (v2w x:'a word) (v2w y:'a word)))`,
      REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> cheat
    );

(* this one is from CakeML/hardware translator/verilog *)
val w2v_n2w = Q.store_thm("w2v_n2w",
 `!n. w2v ((n2w n):'a word) = fixwidth (dimindex (:'a)) (n2v n)`,
rewrite_tac [GSYM v2w_n2v, w2v_v2w]);

(* this one is from CakeML/hardware hardwareMisc *)
val v2n_w2v = Q.store_thm("v2n_w2v",
 `!w. v2n (w2v w) = w2n w`,
 gen_tac
  \\ bitstringLib.Cases_on_v2w `w`
  \\ fs [w2v_v2w, w2n_v2w, bitTheory.MOD_2EXP_def, v2n_lt])

val fixadd_word_add = Q.store_thm("fixadd_word_add",
  `!x y. fixadd (w2v x) (w2v y) = w2v (x + y)`,
   rpt STRIP_TAC
     >> simp[fixadd_def]
     >> simp[GSYM w2v_n2w]
     >> simp[v2n_w2v]
     >> simp[word_add_def]
);

val fixsub_lemma1 = Q.store_thm("fixsub_lemma1",
  `!x y. ((v2w x:'a word) - (v2w y:'a word)
             = ((v2w x:'a word) + ~(v2w y:'a word) + (1w:'a word)))`,
        REPEAT STRIP_TAC >> REWRITE_TAC [word_sub_def]
        >> REWRITE_TAC [WORD_NEG] >> METIS_TAC [WORD_ADD_ASSOC]);

val fixsub_word_sub2 = Q.store_thm("fixsub_word_sub2",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y))
     ==> (v2n (fixsub x y) = w2n ((v2w x:'a word) - (v2w y:'a word)))`,
   REPEAT STRIP_TAC >> simp[fixsub_def]
   >> REWRITE_TAC [fixsub_lemma1] >> ASM_REWRITE_TAC [fixadd_word_add] >> cheat);

val fixsub_lemma = Q.store_thm("fixsub_lemma",
  `!x y. x - y = x + ~y + 1w`,
   rpt STRIP_TAC
   >> REWRITE_TAC [word_sub_def,WORD_NEG]
   >> simp[WORD_ADD_ASSOC]);

val fixwidth_length_l = Q.store_thm("fixwidth_length_l",
  `!h t. (fixwidth (SUC (LENGTH t)) (h::t)) = (h::t)`,
   rpt STRIP_TAC >> Cases_on `(LENGTH (h::t)) < (SUC (LENGTH t))`
   >> rw[fixwidth_def]
);


val fixsub_length = Q.store_thm("fixsub_length", `!x y. (LENGTH (fixsub x y))
                                                   = MAX (LENGTH x) (LENGTH y)`,
            rpt STRIP_TAC >> Cases_on `x` >> Cases_on `y` >> fs[fixsub_def]
            >> fs[fixsub_def] >> fs[fixadd_length]
            >> FULL_SIMP_TAC arith_ss [bnot_def]
            >> REWRITE_TAC[LENGTH_MAP]
            >> simp[length_fixwidth]
);


val SUC_LENGTH = Q.store_thm("SUC_LENGTH",
`!(w:'a word) h t. (w2v w = (h::t)) ==> (LENGTH t = (dimindex(:'a) - 1))`,
cheat
);

val fixsub_word_sub_length_lemma = Q.store_thm("fixsub_word_sub_lemma",
    `!(x:'a word) (y:'a word) h t h' t'.
         ((w2v x = (h::t)) /\ (w2v y = (h'::t')))
           ==> (MAX (SUC (LENGTH t)) (SUC (LENGTH t')) = SUC (LENGTH t))`,
    rpt STRIP_TAC >> IMP_RES_TAC SUC_LENGTH >> ASM_SIMP_TAC arith_ss []
)

val fixsub_word_sub_length_lemma2 = Q.store_thm("fixsub_word_sub_lemma2",
    `!(x:'a word) (y:'a word) h t h' t'.
       ((w2v x = (h::t)) /\ (w2v y = (h'::t')))
         ==> (MAX (SUC (LENGTH t)) (SUC (LENGTH t')) = SUC (LENGTH t'))`,
    rpt STRIP_TAC >> IMP_RES_TAC SUC_LENGTH >> ASM_SIMP_TAC arith_ss []
)

val word_not_bnot = Q.store_thm("word_not_bnot",
  `!x. w2v (~x) = bnot (w2v x)`,
  rpt STRIP_TAC
   >> simp[w2v_def,bnot_def,word_1comp_def]
   >> simp[MAP_GENLIST,FCP_BETA]
   >> rw[o_ABS_R]
);

val fixsub_word_sub = Q.store_thm("fixsub_word_sub",
  `!x:('a word) y. fixsub (w2v x) (w2v y) = w2v (x - y)`,
  (rpt STRIP_TAC) THEN (Cases_on `w2v x`)
        THENL [cheat,Cases_on `w2v y`]
        THENL [cheat,fs [fixsub_lemma]]
        THENL [simp [fixsub_def]]
        THENL [REWRITE_TAC[GSYM fixadd_word_add]]
        THENL [MK_COMB_TAC]
        THENL [MK_COMB_TAC,cheat]
        THENL [simp [],MK_COMB_TAC]
        THENL [MK_COMB_TAC,simp[word_not_bnot]]
        THENL [simp [],IMP_RES_TAC fixsub_word_sub_length_lemma,MK_COMB_TAC]
        THENL [ASM_SIMP_TAC arith_ss [],simp[],ASM_SIMP_TAC arith_ss[]]
        THENL [simp [fixwidth_length_l],simp[fixsub_word_sub_length_lemma]]
        THENL [IMP_RES_TAC fixsub_word_sub_length_lemma2]
        THENL [ASM_SIMP_TAC arith_ss []]
        THENL [simp [fixwidth_length_l]]
);

val fixshiftr_def = Define`
   fixshiftr a n =
     let m = LENGTH a in
        fixwidth m (shiftr a n)`

val fixasr_def = Define`
   (fixasr a 0 = a) /\
   (fixasr a (SUC n) = fixasr
        (sign_extend (LENGTH a) (TAKE (LENGTH a - 1) a)) n)`

val fixshiftl_def = Define`
   fixshiftl a n =
     let m = LENGTH a in
        fixwidth m (shiftl a n)`

val rotate_w2v = Q.store_thm("rotate_word_ror_lemma",
`!w:('a word) n. rotate (w2v w) n = w2v (word_ror w n)`,
   rpt STRIP_TAC >> simp [rotate_def,word_ror]
        >> Cases_on `(dimindex (:'a) = 0)`
         (* dimindex (:'a) = 0 never happens*) >> cheat >> cheat
)

(* TODO prove properties of fixed size shifts *)
(* COPIED from miscTheory, as it builds after this directory *)
val TAKE_GENLIST = Q.store_thm("TAKE_GENLIST",
`TAKE n (GENLIST f m) = GENLIST f (MIN n m)`,cheat)

val MIN_SUB = Q.store_thm("MIN_SUB",
`!x y. MIN (x-y) x = x-y`,
   rpt strip_tac >> REWRITE_TAC [MIN_DEF]
   >> Cases_on `x-y < x`
    >> simp []
    >> simp []
)

val SUB_LT = Q.store_thm("SUB_LT",
`!x y. (x - y > x) ==> (x - (x-y) = 0)`,
      FULL_SIMP_TAC arith_ss []
)

val SUB_LEMMA2 = Q.store_thm("SUB_LEMMA2",
`!x y. ~(x-SUC y > x) ==> (x-SUC y <= x)`,
  Cases_on `x-SUC y > x`
    >> simp []
    >> simp []
)


val fixshift_add_rwt = Q.store_thm("fixshift_add_rwt",
          `!b a. a = a - (a - b) + (a - b)`,FULL_SIMP_TAC arith_ss []);

val GENLIST_APPEND_REVERSE = Q.store_thm("GENLIST_APPEND_REVERSE",
 `!f a b. GENLIST f (a + b) = (GENLIST f a) ++ (GENLIST (\t. f (t + a)) b)`,
    rpt STRIP_TAC >>
    CONV_TAC (PATH_CONV "lrr" (REWR_CONV ADD_COMM))
    >> simp [GENLIST_APPEND]
)


val fixshiftr_lemma1 = Q.store_thm("fixshiftr_lemma1",
  `!n (w : 'a word) i.
     (i < (dimindex (:'a) − (dimindex (:'a) − SUC n)))
        ==>
      (dimindex (:'a) − (i + 1) + SUC n < dimindex (:'a)
       ∧ w ' (dimindex (:'a) − (i + 1) + SUC n) = F)`,
   cheat)


val fixshiftr_word_lsr_SUC = Q.store_thm("fixshiftr_word_lsr_SUC",
  `!n w. ((w2v (word_lsr w (SUC n)) = fixshiftr (w2v w) (SUC n)))`,
   rpt strip_tac >> REWRITE_TAC[w2v_def]
     >> simp[fixshiftr_def,fixwidth_def,shiftr_def,zero_extend_def,TAKE_GENLIST]
     >> simp[MIN_SUB]
     >> simp[word_lsr_def]
     >> simp [FCP,FCP_BETA,CART_EQ]
     >> simp [PAD_LEFT]
     (* rewrite rightmost occurence of `dimindex(:'a)`
        on LHS using fixshift_add_rwt and *)
     >> CONV_TAC (PATH_CONV "lrr" (REWR_CONV (SPEC ``SUC n`` fixshift_add_rwt)))
     (* GENLIST_APPEND splits the addition in reverse
        thus we use our REVERSE theorem *)
     >> REWRITE_TAC[GENLIST_APPEND_REVERSE]
     >> cheat
)

val fixshiftr_word_lsr = Q.store_thm("fixshiftr_word_lsr",
  `!n w. ((w2v (word_lsr w n)) = (fixshiftr (w2v w) n))`,
   rpt strip_tac >> Cases_on `n`
      (* ZERO *)
      >> simp[fixshiftr_def,word_lsr_def,shiftr_def,w2v_def,TAKE_GENLIST]
      >> FULL_SIMP_TAC arith_ss [MIN_SUB]
      >> simp [FCP,FCP_BETA,CART_EQ]
      (* SUCCESSOR *)
      >> cheat
)
(*  simp [fixshiftr_def,w2v_def,word_lsr_def,shiftr_def,fixwidth_def,
          zero_extend_def,PAD_LEFT]
       >> Cases_on `dimindex(:'a)-SUC n' > dimindex(:'a)`
        >> CCONTR_TAC
         >> simp []
        >> FULL_SIMP_TAC arith_ss [SUB_LEMMA2] *)
        (* >> UNDISCH_TAC ``T`` >> EVAL_TAC *)

val fixshiftl_word_lsl = Q.store_thm("fixshiftl_word_lsl",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_lsl w n)) = (fixshiftl a n))`,cheat);

val fixasr_word_asr = Q.store_thm("fixasr_word_asr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_asr w n)) = (fixasr a n))`,cheat);

(* TODO prove that `i2vN x N` represents the same value as `(i2w x): N word` *)
val i2vN_def = Define`
    i2vN (i : int) (n : num) : bitstring = if i < 0
                      then fixsub (fixwidth n [F]) (fixwidth n (n2v (Num (-i))))
                      else fixwidth n (n2v (Num i))`

val i2vN_length = Q.store_thm("i2vN_length", `!i n. (LENGTH (i2vN i n)) = n`,
    rpt STRIP_TAC >> REWRITE_TAC[i2vN_def] >> Cases_on `i < 0` >>
    simp[length_fixwidth,fixsub_length]
);
val v2w_i2vN = Q.store_thm("v2w_i2vN",`!i n. ((i2w i):'a word)
                           = ((v2w (i2vN i (dimindex (:'a)))):'a word)`,cheat);

val w2v_i2w = Q.store_thm("w2v_i2w",`!i. w2v ((i2w i):'a word)
                          = i2vN i (dimindex (:'a))`,cheat);

val v2comp_def = Define`
    v2comp (v : bitstring) : bitstring
    = fixwidth (LENGTH v) (n2v (2**(LENGTH v) - (v2n v)))`

(* TODO prove a theorem relating w2i and v2i *)
val v2i_def = Define`
    (v2i ([] : bitstring) : int = 0) /\
    (v2i ([T] : bitstring) : int = -1) /\
    (v2i ([F] : bitstring) : int = 0) /\
    (v2i ((h::t) : bitstring) : int = if ~h
                     then int_of_num (v2n t)
                     else -(int_of_num (v2n (v2comp t))))`

val v2i_w2v = Q.store_thm("v2i_w2v",`!w. v2i (w2v w) = &w2n w`,cheat);

val v2i_w2i = Q.store_thm("v2i_w2i",`!v w. (v = w2v w) = (v2i v = w2i w)`,cheat);

val blt_def = Define`
    blt x y = v2n x < v2n y`

val bgt_def = Define`
    bgt x y = v2n x > v2n y`

val bleq_def = Define`
    bleq x y = v2n x <= v2n y`

val bgeq_def = Define`
    bgeq x y = v2n x >= v2n y`

val blt_sign_def = Define`
    blt_sign x y = v2i x < v2i y`

val bgt_sign_def = Define`
    bgt_sign x y = v2i x > v2i y`

val bleq_sign_def = Define`
    bleq_sign x y = v2i x <= v2i y`

val bgeq_sign_def = Define`
    bgeq_sign x y = v2i x >= v2i y`

val btest_def = Define`
    btest x y =
      let m = MAX (LENGTH x) (LENGTH y)
       in
         band x y = fixwidth m (n2v 0)`

val _ = export_theory()
