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
open rich_listTheory;

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
  REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> simp[fixadd_length] >> cheat);


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

val length_empty = Q.prove(`!l. (l = []) ==> (LENGTH l = 0)`, STRIP_TAC >> simp[LENGTH]);

val length_dimindex = Q.prove(`!w:('a word) x. (LENGTH (w2v w) = x) ==> (dimindex (:'a) = x)`,
   rpt STRIP_TAC >> fs[length_w2v]);

val SUC_LENGTH_2 = Q.store_thm("SUC_LENGTH_2",
`!f n h t. (GENLIST f (SUC n) = (h::t)) ==> (LENGTH t = n)`,
    rpt STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (AP_TERM ``LENGTH``)) >> fs[LENGTH_GENLIST]
);

val SUC_LENGTH_1 = Q.store_thm("SUC_LENGTH_1",
`!(w:'a word) h t n. ((w2v w = (h::t)) /\ (dimindex(:'a) = (SUC n))) ==> (LENGTH t = n)`,
   rpt STRIP_TAC >> FULL_SIMP_TAC arith_ss [w2v_def] >> IMP_RES_TAC SUC_LENGTH_2
);

val SUC_LENGTH = Q.store_thm("SUC_LENGTH",
`!(w:'a word) h t. (w2v w = (h::t)) ==> (LENGTH t = (dimindex(:'a) - 1))`,
  rpt STRIP_TAC >> ASSUME_TAC (SPEC ``w:'a word`` length_w2v)
    >> Cases_on `dimindex(:'a)`
      >- (simp[] >> ASSUME_TAC DIMINDEX_GT_0 >> FULL_SIMP_TAC arith_ss [])
      >> simp[] >> IMP_RES_TAC SUC_LENGTH_1
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
   STRIP_TAC
   >> simp[w2v_def,bnot_def,word_1comp_def]
   >> simp[MAP_GENLIST,FCP_BETA]
   >> rw[o_ABS_R]
);

val w2v_nonempty = Q.store_thm("w2v_nonempty",
  `!w. ~(w2v w = [])`,
  STRIP_TAC >> CCONTR_TAC
    >> fs []
    >> IMP_RES_TAC length_empty
    >> IMP_RES_TAC length_dimindex
    >> ASSUME_TAC DIMINDEX_GT_0
    >> simp[]
);

val fixsub_word_sub_length_dimindex_lemma = Q.store_thm("fixsub_word_sub_length_dimindex_lemma",
 `!w:('a word) h t. (w2v w = (h::t)) ==> (SUC (LENGTH t) = dimindex(:'a))`,
   rpt STRIP_TAC >> POP_ASSUM (ASSUME_TAC o Q.AP_TERM `LENGTH`) >> fs[]
);

val word_1_lemma1 = Q.store_thm("word_1_lemma1",
 `1w = (n2w (w2n (1w:'a word))):('a word)`,
 simp[n2w_w2n]
);

val word_1_lemma = Q.store_thm("word_1_lemma",
 `!w:('a word). (w2v (1w:'a word)) = fixwidth (dimindex (:'a)) (n2v 1)`,
  STRIP_TAC >> ONCE_REWRITE_TAC[word_1_lemma1] >> simp[w2v_n2w]
);

val fixsub_word_sub = Q.store_thm("fixsub_word_sub",
  `!x:('a word) y. fixsub (w2v x) (w2v y) = w2v (x - y)`,
  rpt STRIP_TAC >> Cases_on `w2v x`
        >- (CCONTR_TAC >> ASSUME_TAC w2v_nonempty >> RES_TAC) >> (Cases_on `w2v y`
          >- (CCONTR_TAC >> ASSUME_TAC w2v_nonempty >> RES_TAC) >> (fs [fixsub_lemma]
  >> simp [fixsub_def]
  >> REWRITE_TAC[GSYM fixadd_word_add]
  >> MK_COMB_TAC
    >- (MK_COMB_TAC
          >- simp []
          >> (MK_COMB_TAC
                  >- (MK_COMB_TAC
                         >- simp []
                         >> (ASM_SIMP_TAC arith_ss []
                             >> IMP_RES_TAC fixsub_word_sub_length_lemma
                             >> ASM_SIMP_TAC arith_ss []
                             >> simp[fixwidth_length_l]
                            )
                     )
                  >> (simp[word_not_bnot]
                        >> MK_COMB_TAC
                              >- simp []
                              >> (ASM_SIMP_TAC arith_ss[]
                                 >> simp[fixsub_word_sub_length_lemma]
                                 >> IMP_RES_TAC fixsub_word_sub_length_lemma2
                                 >> ASM_SIMP_TAC arith_ss []
                                 >> simp[fixwidth_length_l])
                     )
             )
       )
    >> (
      IMP_RES_TAC fixsub_word_sub_length_lemma
        >> ASM_SIMP_TAC arith_ss []
        >> IMP_RES_TAC fixsub_word_sub_length_dimindex_lemma
        >> fs[]
        >> ASM_SIMP_TAC arith_ss []
        >> REWRITE_TAC[ISPEC ``1w:('a word)`` word_1_lemma]
 )))
);

val fixshiftr_def = Define`
   fixshiftr a n =
     let m = LENGTH a in
        fixwidth m (shiftr a n)`
(*
val fixasr_def = Define`
   (fixasr a 0 = a) /\
   (fixasr a (SUC n) = fixasr
        (sign_extend (LENGTH a) (TAKE (LENGTH a - 1) a)) n)`
*)
val fixshiftl_def = Define`
   fixshiftl a n =
     let m = LENGTH a in
        fixwidth m (shiftl a n)`

(* TODO prove properties of fixed size shifts *)
(* The following 2 lemmas are COPIED from miscTheory, as it builds after this directory *)
val TAKE_GENLIST = Q.store_thm("TAKE_GENLIST",
`TAKE n (GENLIST f m) = GENLIST f (MIN n m)`,
 rw[LIST_EQ_REWRITE,LENGTH_TAKE_EQ,MIN_DEF,EL_TAKE]
)

Theorem DROP_GENLIST
  `DROP n (GENLIST f m) = GENLIST (f o ((+)n)) (m-n)`
(rw[LIST_EQ_REWRITE,EL_DROP]);

val MIN_SUB = Q.store_thm("MIN_SUB",
`!x y. MIN (x-y) x = x-y`,
  rpt strip_tac >> REWRITE_TAC [MIN_DEF]
   >> Cases_on `x-y < x`
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
)

val fixshiftr_add_rwt = Q.store_thm("fixshiftr_add_rwt",
          `!b a. a = a - (a - b) + (a - b)`,FULL_SIMP_TAC arith_ss []);

val GENLIST_APPEND_REVERSE = Q.store_thm("GENLIST_APPEND_REVERSE",
 `!f a b. GENLIST f (a + b) = (GENLIST f a) ++ (GENLIST (\t. f (t + a)) b)`,
    rpt STRIP_TAC >>
    CONV_TAC (PATH_CONV "lrr" (REWR_CONV ADD_COMM))
    >> simp[GENLIST_APPEND]
)

val fixshiftr_word_lsr_SUC = Q.store_thm("fixshiftr_word_lsr_SUC",
  `!n w. (w2v (word_lsr w (SUC n)) = fixshiftr (w2v w) (SUC n))`,
   rpt strip_tac
     >> simp[word_lsr_def,fixshiftr_def]
     >> simp[shiftr_def]
     >> REWRITE_TAC[w2v_def]
     >> simp[fixwidth_def,zero_extend_def,TAKE_GENLIST]
     >> simp[PAD_LEFT]
     >> simp[MIN_SUB]
     >> simp[FCP,FCP_BETA,CART_EQ]
     (* rewrite rightmost occurence of `dimindex(:'a)`
        on LHS using fixshiftr_add_rwt *)
     >> CONV_TAC (PATH_CONV "lrr" (REWR_CONV (SPEC ``SUC n`` fixshiftr_add_rwt)))
     (* GENLIST_APPEND splits the addition in reverse
        thus we use our REVERSE theorem *)
     >> REWRITE_TAC[GENLIST_APPEND_REVERSE]
     >> MK_COMB_TAC
        >- ( MK_COMB_TAC
           >- simp[]
           >> srw_tac[ARITH_ss][GENLIST_FUN_EQ]
        )
        >> srw_tac[ARITH_ss][GENLIST_FUN_EQ])


val fixshiftr_word_lsr = Q.store_thm("fixshiftr_word_lsr",
  `!n w. (w2v (word_lsr w n)) = (fixshiftr (w2v w) n)`,
   rpt strip_tac >> Cases_on `n`
      (* ZERO *)
      >- (simp[fixshiftr_def,word_lsr_def,w2v_def] >> simp[shiftr_def] >> simp[TAKE_GENLIST])
      (* SUCCESSOR *)
      >> simp[fixshiftr_word_lsr_SUC]
)

val drop_sub_lemma = Q.store_thm("drop_sub_lemma",
  `!n x. (n < x) ==> (n - x = 0)`,
   rpt STRIP_TAC >> DECIDE_TAC
);

val fixshiftl_word_lsl_lemma1 = Q.store_thm("fixshiftl_word_lsl_lemma1",
  `!f g n x. (n < x) ==> ((DROP n (GENLIST f x ++ GENLIST g n)) = ((DROP n (GENLIST f x)) ++ GENLIST g n))`,
  rpt STRIP_TAC >> simp[DROP_APPEND] >> ASM_SIMP_TAC arith_ss [drop_sub_lemma] >> simp [DROP_0]
);

val fixshiftl_word_lsl_lemma2 = Q.store_thm("fixshiftl_word_lsl_lemma2",
  `!f g n x. ~(n < x) ==> ((DROP n (GENLIST f x ++ GENLIST g n)) = (DROP (n-x) (GENLIST g n)))`,
  rpt STRIP_TAC >> simp[DROP_APPEND] >> ASM_SIMP_TAC arith_ss [DROP_NIL,LENGTH_GENLIST]
);

val fixshiftl_add_rwt = Q.store_thm("fixshiftl_add_rwt", `!b a. (b<a) ==> (a = (a - b) + b)`,FULL_SIMP_TAC arith_ss [])

val fixshiftl_word_lsl_SUC = Q.store_thm("fixshiftl_word_lsl_SUC",
  `!n w:('a word). (w2v (word_lsl w (SUC n)) = fixshiftl (w2v w) (SUC n))`,
   rpt strip_tac
     >> simp[word_lsl_def,fixshiftl_def]
     >> simp[shiftl_def]
     >> REWRITE_TAC[w2v_def]
     >> simp[fixwidth_def]
     >> simp[FCP,FCP_BETA,CART_EQ]
     >> simp[PAD_RIGHT]
     >> Cases_on `SUC n < dimindex(:'a)`
        >- ( ASSUME_TAC (SPEC
                      ``dimindex(:'a)``
                      (SPEC ``SUC n``
                            (ISPEC ``(K F):(num->bool)``
                                (ISPEC ``\i. (w : 'a word) ' (dimindex(:'a) - (i + 1))`` fixshiftl_word_lsl_lemma1))))
          >> RES_TAC
          >> fs[]
          >> simp[DROP_GENLIST]
          >> IMP_RES_TAC (SPEC ``dimindex(:'a)`` (SPEC ``SUC n`` fixshiftl_add_rwt))
          >> ONCE_ASM_REWRITE_TAC []
          >> ONCE_REWRITE_TAC [GENLIST_APPEND_REVERSE]
          >> fs[]
          >> MK_COMB_TAC
             >- (MK_COMB_TAC
                 >> simp []
                 >> srw_tac[ARITH_ss][GENLIST_FUN_EQ])
          >> simp[K_DEF]
          )
     >> ASSUME_TAC (SPEC
                      ``dimindex(:'a)``
                      (SPEC ``SUC n``
                            (ISPEC ``(K F):(num->bool)``
                                (ISPEC ``\i. (w : 'a word) ' (dimindex(:'a) - (i + 1))`` fixshiftl_word_lsl_lemma2))))
    >> RES_TAC
    >> fs[]
    >> simp[DROP_GENLIST]
    >> simp[K_DEF]
)

val fixshiftl_word_lsl = Q.store_thm("fixshiftl_word_lsl",
  `!n w. (w2v (word_lsl w n)) = (fixshiftl (w2v w) n)`,
   rpt strip_tac >> Cases_on `n`
      (* ZERO *)
      >- (simp[fixshiftl_def,word_lsl_def,w2v_def] >> simp[shiftl_def] >> simp[PAD_RIGHT])
      (* SUCCESSOR *)
      >> simp[fixshiftl_word_lsl_SUC]
)

(* edge case: if n>=LENGTH a then it's just the sign *)
val fixasr_def = Define `(fixasr [] n = []) /\
                         (fixasr a n = if n>=LENGTH a
                                        then GENLIST (K (HD a)) (LENGTH a)
                                        else
                                          sign_extend (LENGTH a) (TAKE (LENGTH a - n) a))`



val fixasr_word_asr_lemma1 = Q.prove(
 `!(n:num) (w:'a word). ((n<dimindex(:'a)) /\ (w2v w = (h::t)))
                                     ==> ~(n>=(SUC (LENGTH t)))`,
   rpt strip_tac >> IMP_RES_TAC SUC_LENGTH >> fs[]
)

val fixasr_word_asr_lemma2 = Q.prove(
 `!(n:num) (w:'a word). (~(n<dimindex(:'a)) /\ (w2v w = (h::t)))
                                      ==> (n>=(SUC (LENGTH t)))`,
   rpt strip_tac >> IMP_RES_TAC fixsub_word_sub_length_dimindex_lemma >> FULL_SIMP_TAC arith_ss [])

val fixasr_word_asr_lemma3 = Q.prove(`!(w:'a word) h t. (w2v w = (h::t)) ==> (h = word_msb w)`,
  simp[w2v_def,word_msb_def] >> simp[FCP,FCP_BETA,CART_EQ] >> rpt STRIP_TAC
  >> POP_ASSUM (ASSUME_TAC o (Q.AP_TERM `HD`)) >> fs[]
  >> Cases_on `dimindex(:'a)` >> fs[] >- (CCONTR_TAC >> ASSUME_TAC DIMINDEX_GT_0 >> simp[])
  >> srw_tac[ARITH_ss][HD_GENLIST]
)

val fixasr_word_asr_lemma4 = Q.prove(`!(w:'a word) h t. (w2v w = (h::t)) ==> (SUC (LENGTH t) = dimindex(:'a))`,
   rpt strip_tac >> POP_ASSUM (ASSUME_TAC o (Q.AP_TERM `LENGTH`)) >> fs[]
)

val fixasr_word_asr_lemma5 = Q.prove(`!n t. (n+(LENGTH t+1)-(SUC (LENGTH t))) = n`,FULL_SIMP_TAC arith_ss [])

val fixasr_word_asr_lemma6 = Q.prove(`!h n. (GENLIST (K h) n) ++ [h] = GENLIST (K h) (SUC n)`,simp[GENLIST])

val fixasr_word_asr_lemma7 = Q.prove(`!x y. (SUC x - (y+1)) = x - y`,FULL_SIMP_TAC arith_ss [])

val suc_dimindex_sub1 = Q.prove(`SUC(dimindex(:'a)-1) = dimindex(:'a)`,
  Cases_on `dimindex(:'a)-1` >> fs[DIMINDEX_GT_0]
)

val lem9 = Q.prove(`!f n h t. (GENLIST f n = h::t) ==> (t = GENLIST (f o SUC) (n-1))`,
  rpt STRIP_TAC >> Cases_on `n` >> fs[] >> POP_ASSUM (ASSUME_TAC o (AP_TERM ``TL``)) >> fs[TL_GENLIST]
)

val lem10 = Q.prove(`!x y. MIN (x - (y + 1)) (x - 1) = x-(y+1)`,rpt STRIP_TAC >> simp[MIN_DEF])

val fixasr_word_asr_lemma8 = Q.prove(`!(w:'a word) (n:num) t h. (w2v w = (h::t))
                                      ==>
                                      (GENLIST (\x. w ' (dimindex(:'a) - (n+(x+2)) + n)) (dimindex(:'a) - (n + 1))
                                      =
                                      TAKE (dimindex(:'a) - (n+1)) t)`,
rpt STRIP_TAC >> fs[w2v_def] >> IMP_RES_TAC lem9 >> fs[TAKE_GENLIST,lem10] >> srw_tac[ARITH_ss][GENLIST_FUN_EQ] >> MK_COMB_TAC
  >> simp[]
)

val fixasr_word_asr = Q.store_thm("fixasr_word_asr",
 `!(n:num) (w:'a word). (w2v (word_asr w n)) = (fixasr (w2v w) n)`,
   rpt strip_tac
   >> simp[word_asr_def]
   >> Cases_on `w2v w`
      >- (CCONTR_TAC >> ASSUME_TAC w2v_nonempty >> RES_TAC)
      >> simp[fixasr_def]
      >> simp[sign_extend_def,PAD_LEFT,w2v_def]
      >> Cases_on `n<dimindex(:'a)`
      >> fs[FCP,FCP_BETA,CART_EQ]
         >-(IMP_RES_TAC (ISPEC ``n:num`` fixasr_word_asr_lemma1)
         >> ASM_SIMP_TAC arith_ss [fixasr_word_asr_lemma5,fixasr_word_asr_lemma6,fixasr_word_asr_lemma7]
         >> IMP_RES_TAC SUC_LENGTH >> ASM_SIMP_TAC arith_ss []
         >> CONV_TAC (PATH_CONV "lrr" (REWR_CONV (SPEC ``SUC n`` fixshiftr_add_rwt)))
         >> REWRITE_TAC[GENLIST_APPEND_REVERSE]
         >> MK_COMB_TAC
            >- (MK_COMB_TAC
                >> srw_tac[ARITH_ss][GENLIST_FUN_EQ]
                >> BasicProvers.TOP_CASE_TAC
                >- fs[fixasr_word_asr_lemma3]
                >> FULL_SIMP_TAC arith_ss [suc_dimindex_sub1]
                >> IMP_RES_TAC fixasr_word_asr_lemma3
                >> ASM_SIMP_TAC arith_ss [word_msb_def]
                >> MK_COMB_TAC >> simp[]
               )
            >> fs[]
            >> srw_tac[ARITH_ss][GENLIST_FUN_EQ,ADD1]
            >> FULL_SIMP_TAC arith_ss [suc_dimindex_sub1]
            >> IMP_RES_TAC (ISPEC ``n:num`` (ISPEC ``w:'a word`` fixasr_word_asr_lemma8))
            >> fs[]
        )
        >> IMP_RES_TAC (ISPEC ``n:num`` fixasr_word_asr_lemma2)
        >> ASM_SIMP_TAC arith_ss []
        >> IMP_RES_TAC fixasr_word_asr_lemma3
        >> IMP_RES_TAC fixasr_word_asr_lemma4
        >> ASM_SIMP_TAC arith_ss [K_DEF]
)

val MOD_elim = Q.prove(`!i m n. ((0<m) /\ (n MOD m = 0)) ==> ((i+n) MOD m = (i MOD m))`,
rpt STRIP_TAC >> IMP_RES_TAC ADD_MOD
>> POP_ASSUM (ASSUME_TAC o SPEC ``0``)
>> POP_ASSUM (ASSUME_TAC o ISPEC ``n:num``)
>> IMP_RES_TAC ZERO_MOD
>> FULL_SIMP_TAC arith_ss []
>> RES_TAC
>> POP_ASSUM (ASSUME_TAC o ISPEC ``i:num``)
>> ONCE_REWRITE_TAC [ADD_COMM]
>> fs[]
)

val WORD_ss = rewrites [word_extract_def, word_slice_def,word_bits_def,
  word_bit_def,word_lsl_def,word_lsr_def,word_and_def,word_or_def,word_xor_def,
  word_reverse_def,word_modify_def,n2w_def,w2w,sw2sw,word_msb_def];
val fcp_ss = std_ss ++ fcpLib.FCP_ss;

val FIELD_WORD_TAC = RW_TAC (fcp_ss++WORD_ss++ARITH_ss) [];
val wrw = srw_tac[boolSimps.LET_ss, fcpLib.FCP_ss, ARITH_ss];

val rotate_w2v_lemma = Q.prove(`!x. ~(x = 0) ==> (SUC (x - 1) = x)`,
rpt STRIP_TAC >> simp[])

val rotate_w2v_lemma2 = Q.prove(`!x y. ~(y = 0) ==> ((x MOD y) - y = 0)`,
rpt STRIP_TAC
>> FULL_SIMP_TAC arith_ss []
>> IMP_RES_TAC NOT_ZERO_LT_ZERO
>> IMP_RES_TAC MOD_LESS
>> POP_ASSUM (ASSUME_TAC o (ISPEC ``x:num``))
>> DECIDE_TAC
)

val rotate_w2v_lemma3 = Q.prove(`!a b. ~(a<b) ==> (a = b+(a-b))`,
FULL_SIMP_TAC arith_ss []
)

val rotate_w2v_contr = Q.prove(`!x:num n:num. (0<x) ==> ~(x < n MOD x)`,
NTAC 3 STRIP_TAC >> FULL_SIMP_TAC arith_ss []
 >> CCONTR_TAC >> fs[] >> FULL_SIMP_TAC arith_ss []
 >> ASSUME_TAC MOD_LESS
 >> RES_TAC
 >> POP_ASSUM (ASSUME_TAC o (ISPEC ``n:num``))
 >> fs[]
)

val rotate_w2v_lemma4 = Q.prove(`!n i. SUC n - (i+1) = n-i`,
   rpt STRIP_TAC >> ASM_SIMP_TAC arith_ss []
)

val add_suc = Q.prove(`SUC x + y = SUC (x+y)`,DECIDE_TAC)

val lt_add_sub = Q.prove(`!x y z. (z<=x) ==> ((x+y)-z = (x-z)+y)`,rpt STRIP_TAC >> ASM_SIMP_TAC arith_ss [])

val lem1 = Q.prove(`!i m n. (i < (SUC n) MOD m /\ 0 < m) ==> i <= n`,
   rpt STRIP_TAC
>> ASSUME_TAC MOD_LESS
>> POP_ASSUM (ASSUME_TAC o (ISPEC ``m:num`` o SPEC ``SUC n``))
>> RES_TAC
>> ASM_SIMP_TAC arith_ss []
>> Cases_on `SUC n < m`
>> FULL_SIMP_TAC arith_ss []
)
val rotate_w2v_lemma5 = Q.prove(`!n i (w:'a word).
(i<(n MOD dimindex(:'a)))
              ==>
((((n+dimindex(:'a))-(i+1)) MOD (dimindex(:'a))) = ((n-(i+1)) MOD (dimindex(:'a))))`,
  rpt STRIP_TAC
  >> Cases_on `n`
  >> fs[]
  >> rename1 `i<SUC n' MOD dimindex(:'a)`
  >> REWRITE_TAC [rotate_w2v_lemma4]
  >> REWRITE_TAC [add_suc]
  >> REWRITE_TAC [rotate_w2v_lemma4]
  >> ASSUME_TAC DIMINDEX_GT_0
  >> IMP_RES_TAC lem1
  >> IMP_RES_TAC lt_add_sub
  >> POP_ASSUM (ASSUME_TAC o (SPEC ``dimindex(:'a)``))
  >> ONCE_ASM_REWRITE_TAC []
  >> IMP_RES_TAC ADD_MODULUS_LEFT
  >> POP_ASSUM (ASSUME_TAC o (SPEC ``n'-i``))
  >> ASM_SIMP_TAC arith_ss []
)
val rotate_w2v_lemma6 = Q.prove(`!i x y. ((i<x) /\ (y = x)) ==> (i<y)`,
   rpt STRIP_TAC >> fs[])

val rotate_w2v_mod_lemma2 = Q.prove(`!(x:num) (y:num) m. (0 < m /\ (x < y MOD m)) ==> (x MOD m = x)`,
   rpt STRIP_TAC
   >> IMP_RES_TAC MOD_LESS
   >> POP_ASSUM (ASSUME_TAC o (ISPEC ``y:num``))
   >> fs[]
)


val rotate_w2v_mod_lemma4 = Q.prove(`!(x:num) (y:num) m. (0 < m /\ (x < y MOD m)) ==> ((x+1) MOD m <= y MOD m)`,
   rpt STRIP_TAC
   >> IMP_RES_TAC MOD_LESS
   >> POP_ASSUM (ASSUME_TAC o (ISPEC ``y:num``))
   >> fs[]
)


val rotate_w2v_mod_lemma3 = Q.prove(`!b x. (b < x /\ ~(b+1 < x)) ==> (b = x-1)`,rpt STRIP_TAC >> fs[])

val rotate_w2v_mod_lemma5 = Q.prove(`!x n. SUC n - (x+1) = n-x`,rpt STRIP_TAC >> FULL_SIMP_TAC arith_ss [])

val MOD_LESS2 =  Q.prove(`!(a:num) m b. 0<m ==> ((a MOD m) < b+m)`,
  rpt STRIP_TAC
  >> ASM_SIMP_TAC arith_ss []
  >> IMP_RES_TAC MOD_LESS
  >> POP_ASSUM (ASSUME_TAC o (ISPEC ``a:num``))
  >> ASM_SIMP_TAC arith_ss []
)

val MOD_DIV_ADD = Q.prove(`!(a:num) (m:num) b. 0<m ==> (a=m*(a DIV m)+(a MOD m))`,
   rpt STRIP_TAC >> IMP_RES_TAC DIVISION >> POP_ASSUM (fn x => ALL_TAC)
   >> POP_ASSUM (ASSUME_TAC o (ISPEC ``a:num``))
   >> ASM_SIMP_TAC arith_ss []
)

val rotate_w2v_mod_lemma_sub_lt = Q.prove(`!(b:num) (a:num) (m:num). (0 < m /\ b<a MOD m) ==> ((a-b) MOD m = a MOD m - b)`,
  rpt STRIP_TAC
  >> MATCH_MP_TAC MOD_UNIQUE
  >> Q.EXISTS_TAC `a DIV m`
  >> simp[SUB_LESS]
  >> simp[MOD_LESS2]
  >> MK_COMB_TAC >-(
     MK_COMB_TAC >- simp[] >> ASM_SIMP_TAC arith_ss [MOD_DIV_ADD]
  ) >> simp[]
)


val lesstrans2 = Q.prove(`!a b c. (a<b /\ b<c) ==> (a+1)<c`,rpt STRIP_TAC >> ASM_SIMP_TAC arith_ss [])

val modlemma1 = Q.prove(`!x y m. (0 < m /\ x < y MOD m) ==> (((x+1) MOD m = x+1) /\ ((x+1) DIV m = 0))`,
   rpt STRIP_TAC
   >> IMP_RES_TAC MOD_LESS
   >> POP_ASSUM (ASSUME_TAC o (ISPEC ``y:num``))
   >> ASM_SIMP_TAC arith_ss[LESS_DIV_EQ_ZERO,lesstrans2]
)

val rotate_w2v_mod_lemma = Q.prove(`!(x:num) (y:num) (m:num). (0 < m /\ (x<y MOD m)) ==> ((y-(x+1)) MOD m = (y MOD m)-((x+1) MOD m))`,
   rpt STRIP_TAC
   >> MATCH_MP_TAC MOD_UNIQUE
   >> simp[]
   >> Q.EXISTS_TAC `(y DIV m)-((x+1) DIV m)`
   >> CONJ_TAC
   >- (REWRITE_TAC [LEFT_SUB_DISTRIB] >> IMP_RES_TAC modlemma1 >> ASM_SIMP_TAC arith_ss [] >> metis_tac[DIVISION,MULT_COMM,ADD_COMM])
   >> IMP_RES_TAC MOD_LESS
   >> POP_ASSUM (ASSUME_TAC o (ISPEC ``y:num``))
   >> ASM_SIMP_TAC arith_ss []
)


val lemma7_simp = Q.prove(`!x y. (SUC x <= y+1) = (x <= y)`, FULL_SIMP_TAC arith_ss [])

val lemma7_mod_eq_self = Q.prove(`!x m. 0<m ==> ((x MOD m = x)=(x<m))`,
   rpt STRIP_TAC
   >> EQ_TAC
   >> STRIP_TAC
   >- (POP_ASSUM (fn thm => ONCE_REWRITE_TAC[GSYM thm]) >> simp[MOD_LESS])
   >> MATCH_MP_TAC MOD_UNIQUE
   >> Q.EXISTS_TAC `0`
   >> simp[]
)


val lemma7_exists_SUC = Q.prove(`!b n m n'. (0 < m /\ b < n' /\ (n MOD m = SUC n'))
                             ==> (?x. (n-(b+1)) MOD m = SUC x)`,
   rpt STRIP_TAC >> simp[rotate_w2v_mod_lemma]
   >> `(b+1) MOD m = b+1` by (simp[lemma7_mod_eq_self] >> ASSUME_TAC (ISPEC ``n:num`` MOD_LESS) >> RES_TAC >> fs[ADD1])
   >> Q.EXISTS_TAC `(n' - (b+1))`
   >> fs[]
)


val rotate_w2v_lemma7 = Q.prove(`!n b a m. (0 < m /\ b < SUC a /\ (n MOD m=SUC a)) ==> ((a-b) = ((n-(b+1)) MOD m))`,
   rpt STRIP_TAC
   >> POP_ASSUM (ASSUME_TAC o GSYM)
   >> fs[] >> IMP_RES_TAC rotate_w2v_mod_lemma
   >> POP_ASSUM (ASSUME_TAC o AP_TERM ``\x. x-1``) >> fs[]
   >> Cases_on `(n-(b+1)) MOD m`
      >- (FULL_SIMP_TAC arith_ss [] >> Cases_on `n MOD m` >> FULL_SIMP_TAC arith_ss [lemma7_simp] >>
          Cases_on `n<m` >- FULL_SIMP_TAC arith_ss [MOD_LESS] >> Cases_on `n=m`
            >- (CCONTR_TAC >> IMP_RES_TAC DIVMOD_ID >> fs[]) >> CCONTR_TAC >> fs[NOT_LESS_EQUAL]
            >> `~((n-(b+1)) MOD m = 0)` by (IMP_RES_TAC lemma7_exists_SUC >> fs[])
          )
   >> ASM_SIMP_TAC arith_ss []
   >> POP_ASSUM (ASSUME_TAC o GSYM)
   >> ASM_SIMP_TAC arith_ss []
   >> IMP_RES_TAC rotate_w2v_mod_lemma
   >> ASM_SIMP_TAC arith_ss []
   >> POP_ASSUM (fn t => ALL_TAC)
   >> POP_ASSUM (fn t => ALL_TAC)
   >> POP_ASSUM (fn t => ALL_TAC)
   >> POP_ASSUM (ASSUME_TAC o GSYM)
   >> ASM_SIMP_TAC arith_ss []
   >> Cases_on `b+1 < n MOD m`
   >- (IMP_RES_TAC rotate_w2v_mod_lemma2 >> ASM_SIMP_TAC arith_ss []
        >> IMP_RES_TAC rotate_w2v_mod_lemma3)
   >> IMP_RES_TAC rotate_w2v_mod_lemma3
   >> ASM_SIMP_TAC arith_ss []
   >> rw[GSYM ADD1]
   >> POP_ASSUM (fn t => ALL_TAC)
   >> POP_ASSUM (fn t => ALL_TAC)
   >> POP_ASSUM (ASSUME_TAC o GSYM)
   >> ASM_SIMP_TAC arith_ss []
)

val DIV_TIMES = Q.prove(`!x y. (0 < y) ==> (y*(x DIV y) = x - (x MOD y))`,
  rpt STRIP_TAC
  >> IMP_RES_TAC DIVISION
  >> POP_ASSUM (fn modassum => POP_ASSUM (fn divassum => ASSUME_TAC (AP_TERM ``\l. l - x MOD y`` (ISPEC ``x:num`` divassum))))
  >> fs[]
)

val rotate_w2v_lemma8 = Q.prove(`!x y n t. ((0 < x) /\ ((n MOD x) = y) /\ (t<x-y)) ==>  (x-(t+1) = ((n+x-(t+(n MOD x)+1)) MOD x))`,
   rpt STRIP_TAC
   >> MATCH_MP_TAC (GSYM MOD_UNIQUE)
   >> Q.EXISTS_TAC `n DIV x`
   >> CONJ_TAC
   >- (POP_ASSUM (fn assum1 => POP_ASSUM (fn assum2 => ASSUME_TAC assum1 >> ASSUME_TAC (GSYM assum2)))
       >> simp[DIV_TIMES]
       >> `n MOD x <= n` by simp[MOD_LESS_EQ]
       >> `n − n MOD x + (x − (t + 1)) = n + (x − (t + 1)) - n MOD x` by FULL_SIMP_TAC arith_ss []
       >> simp[]
   )

   >> simp[]
)

val rotate_w2v = Q.store_thm("rotate_w2v",
`!w:('a word) (n:num). rotate (w2v w) n = w2v (word_ror w n)`,
   rpt STRIP_TAC >> simp [rotate_def] >> rw[word_ror_def]
         (* dimindex (:'a) = 0 never happens*)
         >- (CCONTR_TAC >> FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0])
         >- (MK_COMB_TAC >> simp[] >> FIELD_WORD_TAC >> MK_COMB_TAC >> simp[] >> ASM_SIMP_TAC arith_ss [MOD_elim])
         >> rw[field_def,shiftr_def,fixwidth_def,w2v_def]
            >-( simp[TAKE_GENLIST]
              >> REWRITE_TAC[DROP_GENLIST]
              >> REWRITE_TAC[MIN_SUB]
              >> simp[]
              >> simp[zero_extend_def]
              >> simp[PAD_LEFT]
              >> simp[FCP,FCP_BETA,CART_EQ]
              >> fs[]
              >> ASM_SIMP_TAC arith_ss [suc_dimindex_sub1]
              >> IMP_RES_TAC rotate_w2v_lemma
              >> ASM_SIMP_TAC arith_ss []
              >> IMP_RES_TAC rotate_w2v_lemma2
              >> ASM_SIMP_TAC arith_ss []
              >> simp[]
              >> CCONTR_TAC
              >> fs[rotate_w2v_contr]
            )
        >> simp[TAKE_GENLIST]
        >> REWRITE_TAC[DROP_GENLIST]
        >> simp[suc_dimindex_sub1,MIN_SUB]
        >> fs[]
        >> Cases_on `n MOD dimindex(:'a)`
        >> fs[]
        >> simp[FCP,FCP_BETA,CART_EQ]
        >> IMP_RES_TAC rotate_w2v_lemma3
        >> POP_ASSUM (CONV_TAC o (PATH_CONV "rr" o REWR_CONV))
        >> REWRITE_TAC[GENLIST_APPEND_REVERSE]
        >> MK_COMB_TAC
             >- ( MK_COMB_TAC
                >> srw_tac[ARITH_ss][GENLIST_FUN_EQ]
                >> MK_COMB_TAC
                >> simp []
                >> ASM_SIMP_TAC arith_ss [rotate_w2v_lemma4]
                >> ASSUME_TAC DIMINDEX_GT_0
                >> IMP_RES_TAC rotate_w2v_lemma6
                >> IMP_RES_TAC rotate_w2v_lemma5
                >> IMP_RES_TAC rotate_w2v_lemma4
                >> ASM_SIMP_TAC arith_ss []
                >> fs[]
                >> ASSUME_TAC DIMINDEX_GT_0
                >> IMP_RES_TAC rotate_w2v_lemma7
                )
        >> srw_tac[ARITH_ss][GENLIST_FUN_EQ]
        >> MK_COMB_TAC >> simp[] >> IMP_RES_TAC rotate_w2v_lemma8 >> fs[]
)


(* TODO prove that `i2vN x N` represents the same value as `(i2w x): N word` *)
val i2vN_def = Define`
    i2vN (i : int) (n : num) : bitstring = if i < 0
                      then fixsub (fixwidth n [F]) (fixwidth n (n2v (Num (-i))))
                      else fixwidth n (n2v (Num i))`

val i2vN_length = Q.store_thm("i2vN_length", `!i n. (LENGTH (i2vN i n)) = n`,
    rpt STRIP_TAC >> REWRITE_TAC[i2vN_def] >> Cases_on `i < 0` >>
    simp[length_fixwidth,fixsub_length]
);

val w2v_0w = Q.store_thm("w2v_0w",`w2v (0w:'a word) = fixwidth (dimindex(:'a)) [F]`,
   simp[w2v_n2w] >> EVAL_TAC)


val w2v_i2w = Q.store_thm("w2v_i2w",`!i. w2v ((i2w i):'a word)
                          = i2vN i (dimindex (:'a))`,
  STRIP_TAC >> simp[i2w_def] >> BasicProvers.TOP_CASE_TAC >> simp[i2vN_def]
   >- (fs[GSYM w2v_0w]
       >> ONCE_REWRITE_TAC[GSYM w2v_n2w]
       >> simp[fixsub_word_sub]
       >> MK_COMB_TAC
       >> simp[])
   >> simp[w2v_n2w]

);

val v2comp_def = Define`
    v2comp (v : bitstring) : bitstring
    = fixwidth (LENGTH v) (n2v (2**(LENGTH v) - (v2n v)))`

val v2i_def = Define`
     (v2i [] : int = 0) /\
     (v2i v : int = if HD v then ~(int_of_num (v2n (v2comp v))) else int_of_num (v2n v))`

val v2i_w2v = Q.store_thm("v2i_w2v",`!w. v2i (w2v w) = w2i w`,
    STRIP_TAC >> REWRITE_TAC[w2i_def] >> Cases_on `w2v w` >- fs[w2v_nonempty]
    >> REWRITE_TAC[v2i_def,HD] >> IMP_RES_TAC fixasr_word_asr_lemma3
    >> ASM_REWRITE_TAC[] >> BasicProvers.PURE_TOP_CASE_TAC >> ASM_REWRITE_TAC[]
    >> rpt (MK_COMB_TAC >- simp[]) >> REWRITE_TAC[GSYM v2n_w2v]
    >> (MK_COMB_TAC >- simp[])
    >- (REWRITE_TAC[v2comp_def,word_2comp_def] >> simp[GSYM fixsub_word_sub,w2v_n2w]
       >> MK_COMB_TAC >> simp[]
          >- (IMP_RES_TAC SUC_LENGTH >> fs[suc_dimindex_sub1])
          >> simp[dimword_def] >> MK_COMB_TAC >> simp[GSYM v2n_w2v] >> rpt (MK_COMB_TAC >> fs[])
          >> IMP_RES_TAC SUC_LENGTH >> simp[suc_dimindex_sub1]
       )
    >> fs[]
)

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
