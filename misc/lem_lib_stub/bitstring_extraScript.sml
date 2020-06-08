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
open numposrepTheory;

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

(* TODO prove properties of fixadd and fixsub *)

Theorem fixadd_comm:
   !x y. fixadd x y = fixadd y x
Proof
  REPEAT STRIP_TAC
  >> REWRITE_TAC [fixadd_def]
  >> FULL_SIMP_TAC arith_ss [MAX_COMM]
QED

Theorem fixadd_length:
   !x y. LENGTH (fixadd x y) = MAX (LENGTH x) (LENGTH y)
Proof
   REPEAT STRIP_TAC
   >> simp [fixadd_def]
QED

(*
Theorem fixadd_assoc:
   !x y z. fixadd (fixadd x y) z = fixadd x (fixadd y z)
Proof
  REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> simp[fixadd_length] >> cheat
QED
*)

(* this one is from CakeML/hardware translator/verilog *)
Theorem w2v_n2w:
  !n. w2v ((n2w n):'a word) = fixwidth (dimindex (:'a)) (n2v n)
Proof
  rewrite_tac [GSYM v2w_n2v, w2v_v2w]
QED

(* this one is from CakeML/hardware hardwareMisc *)
Theorem v2n_w2v:
 !w. v2n (w2v w) = w2n w
Proof
 gen_tac
  \\ bitstringLib.Cases_on_v2w `w`
  \\ fs [w2v_v2w, w2n_v2w, bitTheory.MOD_2EXP_def, v2n_lt]
QED

Theorem fixadd_word_add:
  !x y. fixadd (w2v x) (w2v y) = w2v (x + y)
Proof
  rpt STRIP_TAC
  >> simp[fixadd_def]
  >> simp[GSYM w2v_n2w]
  >> simp[v2n_w2v]
  >> simp[word_add_def]
QED

Theorem l2n_2_append:
  !y x. l2n 2 (x ++ y) = l2n 2 x + (2**LENGTH x) * (l2n 2 y)
Proof
  INDUCT_THEN list_INDUCT ASSUME_TAC \\ fs[] \\ STRIP_TAC \\ INDUCT_THEN list_INDUCT ASSUME_TAC \\ fs[]
  \\ rw[] \\ simp[Once l2n_def] \\ ONCE_REWRITE_TAC[ADD_SYM] \\ simp[EXP] \\ simp[LEFT_ADD_DISTRIB]
  \\ simp[l2n_def]
QED

Theorem v2n_append:
  !y x. v2n (x++y) = (2**LENGTH y) *(v2n x) + v2n y
Proof
  simp[v2n_def,num_from_bin_list_def,bitify_reverse_map,REVERSE_APPEND,l2n_2_append]
QED

val GENLIST_K_REVERSE_SUC = Q.prove(`!x y. GENLIST (K x) (SUC y) = [x] ++ GENLIST (K x) y`,
  rw[LIST_EQ_REWRITE] \\ rename1 `EL i _` \\ Cases_on `i` \\ simp[EL]
)

val EVERY_EQ_GENLIST = Q.prove(`!l x. EVERY ($= x) l = (l = GENLIST (K x) (LENGTH l))`,
     Induct \\ fs[] \\ rpt STRIP_TAC \\ EQ_TAC \\ rw[] \\ fs[GENLIST_K_REVERSE_SUC]
)

val GENLIST_K_EVERY = Q.prove(`!x y. (y = GENLIST (K x) (LENGTH y)) = EVERY ($=x) y`,
 simp[EVERY_EQ_GENLIST]
)

Theorem v2n_eq0:
  !x. (v2n x = 0) <=> (x = GENLIST (K F) (LENGTH x))
Proof
  simp[v2n_def,bitify_reverse_map,num_from_bin_list_def,l2n_eq_0,EVERY_REVERSE,EVERY_MAP]
  \\ simp[GENLIST_K_EVERY] \\ STRIP_TAC \\ rpt (MK_COMB_TAC \\ simp[]) \\ srw_tac[][FUN_EQ_THM]
  \\ BasicProvers.TOP_CASE_TAC \\ EVAL_TAC
QED

Theorem v2n_zero_extend:
  !x n. v2n (zero_extend n x) = v2n x
Proof
  rw[zero_extend_def] \\ rw[PAD_LEFT] \\ rw[v2n_append] \\ simp[v2n_eq0]
QED

Theorem fixadd_word_add2:
  !x y. (MAX (LENGTH x) (LENGTH y) = dimindex(:'a))
     ==> (v2n (fixadd x y) = w2n (word_add (v2w x:'a word) (v2w y:'a word)))
Proof
      rpt STRIP_TAC >> simp[GSYM v2n_w2v] \\ MK_COMB_TAC \\ simp[] \\ simp[GSYM fixadd_word_add]
      \\ simp[w2v_v2w] \\ simp[fixadd_def]
      \\ simp[fixwidth_eq,testbit_el] \\ rpt STRIP_TAC \\ ntac 2 (MK_COMB_TAC \\ simp[])
      \\ fs[MAX_DEF] \\ Cases_on `LENGTH x < LENGTH y` \\ fs[] \\ simp[fixwidth_def]
      \\ TRY (BasicProvers.TOP_CASE_TAC) \\ fs[v2n_zero_extend]
      \\ `LENGTH y - dimindex(:'a) = 0` by fs[] \\ ASM_REWRITE_TAC[] \\ simp[]
QED

val fixsub_lemma1 = Q.prove(
  `!x y. ((v2w x:'a word) - (v2w y:'a word)
             = ((v2w x:'a word) + ~(v2w y:'a word) + (1w:'a word)))`,
        REPEAT STRIP_TAC >> REWRITE_TAC [word_sub_def]
        >> REWRITE_TAC [WORD_NEG] >> METIS_TAC [WORD_ADD_ASSOC]);

val fixsub_lemma = Q.prove(
  `!x y. x - y = x + ~y + 1w`,
   rpt STRIP_TAC
   >> REWRITE_TAC [word_sub_def,WORD_NEG]
   >> simp[WORD_ADD_ASSOC]);

val fixwidth_length_l = Q.prove(
  `!h t. (fixwidth (SUC (LENGTH t)) (h::t)) = (h::t)`,
   rpt STRIP_TAC >> Cases_on `(LENGTH (h::t)) < (SUC (LENGTH t))`
   >> rw[fixwidth_def]
);


Theorem fixsub_length:
   !x y. (LENGTH (fixsub x y)) = MAX (LENGTH x) (LENGTH y)
Proof
            rpt STRIP_TAC >> Cases_on `x` >> Cases_on `y` >> fs[fixsub_def]
            >> fs[fixsub_def] >> fs[fixadd_length]
            >> FULL_SIMP_TAC arith_ss [bnot_def]
            >> REWRITE_TAC[LENGTH_MAP]
            >> simp[length_fixwidth]
QED

val length_empty = Q.prove(`!l. (l = []) ==> (LENGTH l = 0)`, STRIP_TAC >> simp[LENGTH]);

val length_dimindex = Q.prove(`!w:('a word) x. (LENGTH (w2v w) = x) ==> (dimindex (:'a) = x)`,
   rpt STRIP_TAC >> fs[length_w2v]);

val SUC_LENGTH_2 = Q.prove(
`!f n h t. (GENLIST f (SUC n) = (h::t)) ==> (LENGTH t = n)`,
    rpt STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (AP_TERM ``LENGTH``)) >> fs[LENGTH_GENLIST]
);

val SUC_LENGTH_1 = Q.prove(
`!(w:'a word) h t n. ((w2v w = (h::t)) /\ (dimindex(:'a) = (SUC n))) ==> (LENGTH t = n)`,
   rpt STRIP_TAC >> FULL_SIMP_TAC arith_ss [w2v_def] >> IMP_RES_TAC SUC_LENGTH_2
);

val SUC_LENGTH = Q.prove(
`!(w:'a word) h t. (w2v w = (h::t)) ==> (LENGTH t = (dimindex(:'a) - 1))`,
  rpt STRIP_TAC >> ASSUME_TAC (SPEC ``w:'a word`` length_w2v)
    >> Cases_on `dimindex(:'a)`
      >- (simp[] >> ASSUME_TAC DIMINDEX_GT_0 >> FULL_SIMP_TAC arith_ss [])
      >> simp[] >> IMP_RES_TAC SUC_LENGTH_1
);

val fixsub_word_sub_length_lemma = Q.prove(
    `!(x:'a word) (y:'a word) h t h' t'.
         ((w2v x = (h::t)) /\ (w2v y = (h'::t')))
           ==> (MAX (SUC (LENGTH t)) (SUC (LENGTH t')) = SUC (LENGTH t))`,
    rpt STRIP_TAC >> IMP_RES_TAC SUC_LENGTH >> ASM_SIMP_TAC arith_ss []
)

val fixsub_word_sub_length_lemma2 = Q.prove(
    `!(x:'a word) (y:'a word) h t h' t'.
       ((w2v x = (h::t)) /\ (w2v y = (h'::t')))
         ==> (MAX (SUC (LENGTH t)) (SUC (LENGTH t')) = SUC (LENGTH t'))`,
    rpt STRIP_TAC >> IMP_RES_TAC SUC_LENGTH >> ASM_SIMP_TAC arith_ss []
)

Theorem word_not_bnot:
  !x. w2v (~x) = bnot (w2v x)
Proof
   STRIP_TAC
   >> simp[w2v_def,bnot_def,word_1comp_def]
   >> simp[MAP_GENLIST,FCP_BETA]
   >> rw[o_ABS_R]
QED

Theorem w2v_nonempty:
  !w. ~(w2v w = [])
Proof
  STRIP_TAC >> CCONTR_TAC
  >> fs []
  >> IMP_RES_TAC length_empty
  >> IMP_RES_TAC length_dimindex
  >> ASSUME_TAC DIMINDEX_GT_0
  >> simp[]
QED

val fixsub_word_sub_length_dimindex_lemma = Q.prove(
 `!w:('a word) h t. (w2v w = (h::t)) ==> (SUC (LENGTH t) = dimindex(:'a))`,
   rpt STRIP_TAC >> POP_ASSUM (ASSUME_TAC o Q.AP_TERM `LENGTH`) >> fs[]
);

val word_1_lemma1 = Q.prove(
 `1w = (n2w (w2n (1w:'a word))):('a word)`,
 simp[n2w_w2n]
);

val word_1_lemma = Q.prove(
 `!w:('a word). (w2v (1w:'a word)) = fixwidth (dimindex (:'a)) (n2v 1)`,
  STRIP_TAC >> ONCE_REWRITE_TAC[word_1_lemma1] >> simp[w2v_n2w]
);

Theorem fixsub_word_sub:
  !x:('a word) y. fixsub (w2v x) (w2v y) = w2v (x - y)
Proof
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
QED

(*
val fixwidth_w2v_swap = Q.prove(`!x:'b word. fixwidth (dimindex(:'a)) (w2v x) = w2v ((w2w x):'a word)`,
   rw[LIST_EQ_REWRITE] \\ ASM_SIMP_TAC arith_ss [el_fixwidth,length_w2v,el_w2v]
   \\ rw[] \\ cheat
)

val length_bnot = Q.prove(`!x. LENGTH (bnot x) = LENGTH x`,cheat)

Theorem fixsub_word_sub2:
  `!x y.  (MAX (LENGTH x) (LENGTH y) = dimindex(:'a))
     ==> (v2n (fixsub x y) = w2n ((v2w x:'a word) - (v2w y:'a word)))`,
   REPEAT STRIP_TAC >> simp[GSYM v2n_w2v] >> MK_COMB_TAC \\ simp[]
   \\ simp[GSYM fixadd_word_add] \\ Cases_on `(x = []) \/ (y = [])`
   \\ fs[]
   \\ fs[DIMINDEX_GT_0,fixsub_def,w2v_v2w]
   \\ simp[fixadd_word_add]
   \\ Cases_on `y`
   \\ Cases_on `x`
   \\ fs[DIMINDEX_GT_0]
   >- (simp[fixadd_def] \\ simp[v2n_w2v]
       \\ `v2n (fixwidth (dimindex(:'a)) []) = 0` by cheat
       \\ fs[]
       \\ simp[fixsub_def]
       \\ `fixwidth (dimindex (:α)) [] = w2v (0w:'a word)` by cheat
       \\ fs[]
       \\ simp[Once fixadd_def] \\ simp[fixadd_length,length_bnot]
       (* \\ simp[n2v_w2n]
       \\ `!x. fixadd (w2v (0w:'a word)) x = fixwidth (MAX (LENGTH x) (dimindex(:'a))) x` by cheat
       \\ fs[]
       \\ `v2n (fixwidth (dimindex (:α)) (n2v 1)) = 1` by cheat
       \\ fs[]
       \\ simp[length_bnot]
       \\ simp[fixwidth_eq]
       \\ rw[]
       \\ simp[n2v_w2n,w2v_v2w,v2n_n2v]
       \\ cheat
       \\ simp[fixadd_def]
       \\ simp[length_bnot]
       \\ Cases_on `dimindex(:'a)`
       \\ fs[DIMINDEX_GT_0]
       \\ simp[MAX_DEF]
       \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ fs[]
       \\ `bnot [T] = [F]` by EVAL_TAC
       \\ fs[]
       \\ `v2n [F] = 0` by EVAL_TAC
       \\ fs[]*) \\ cheat)
   >- cheat
   \\ rename1 `fixsub (a::b) (c::d)`
   \\ `?v. (a::b) = w2v v` by cheat
   \\ `?w. (c::d) = w2v w` by cheat
   \\ ASM_SIMP_TAC arith_ss [fixsub_word_sub,v2w_w2v,fixwidth_w2v_swap,fixadd_word_add,w2w_id,word_sub_def]
   \\ `-1w * w = -w` by (simp[Once WORD_NEG_1])
   \\ fs[]
);
*)
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

Theorem MIN_SUB:
  !x y. MIN (x-y) x = x-y
Proof
  rpt strip_tac >> REWRITE_TAC [MIN_DEF]
  >> Cases_on `x-y < x`
  >> simp []
QED

Theorem SUB_LT:
  !x y. (x - y > x) ==> (x - (x-y) = 0)
Proof
      FULL_SIMP_TAC arith_ss []
QED

val SUB_LEMMA2 = Q.prove(
`!x y. ~(x-SUC y > x) ==> (x-SUC y <= x)`,
  Cases_on `x-SUC y > x`
    >> simp []
)

val fixshiftr_add_rwt = Q.prove(
          `!b a. a = a - (a - b) + (a - b)`,FULL_SIMP_TAC arith_ss []);

Theorem GENLIST_APPEND_REVERSE:
 !f a b. GENLIST f (a + b) = (GENLIST f a) ++ (GENLIST (\t. f (t + a)) b)
Proof
    rpt STRIP_TAC >>
    CONV_TAC (PATH_CONV "lrr" (REWR_CONV ADD_COMM))
    >> simp[GENLIST_APPEND]
QED

val fixshiftr_word_lsr_SUC = Q.prove(
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


Theorem fixshiftr_word_lsr:
   !n w. (w2v (word_lsr w n)) = (fixshiftr (w2v w) n)
Proof
   rpt strip_tac >> Cases_on `n`
      (* ZERO *)
      >- (simp[fixshiftr_def,word_lsr_def,w2v_def] >> simp[shiftr_def] >> simp[TAKE_GENLIST])
      (* SUCCESSOR *)
      >> simp[fixshiftr_word_lsr_SUC]
QED

Theorem DROP_NIL[local]:
  ∀xs n. DROP n xs = [] ⇔ LENGTH xs <= n
Proof
  Induct \\ Cases_on ‘n’ \\ fs []
QED

val drop_sub_lemma = Q.prove(
  `!n x. (n < x) ==> (n - x = 0)`,
   rpt STRIP_TAC >> DECIDE_TAC
);

val fixshiftl_word_lsl_lemma1 = Q.prove(
  `!f g n x. (n < x) ==> ((DROP n (GENLIST f x ++ GENLIST g n)) = ((DROP n (GENLIST f x)) ++ GENLIST g n))`,
  rpt STRIP_TAC >> simp[DROP_APPEND] >> ASM_SIMP_TAC arith_ss [drop_sub_lemma] >> simp [DROP_0]
);

val fixshiftl_word_lsl_lemma2 = Q.prove(
  `!f g n x. ~(n < x) ==> ((DROP n (GENLIST f x ++ GENLIST g n)) = (DROP (n-x) (GENLIST g n)))`,
  rpt STRIP_TAC >> simp[DROP_APPEND] >> ASM_SIMP_TAC arith_ss [LENGTH_GENLIST,DROP_NIL]
);

val fixshiftl_add_rwt = Q.prove(`!b a. (b<a) ==> (a = (a - b) + b)`,FULL_SIMP_TAC arith_ss [])

val fixshiftl_word_lsl_SUC = Q.prove(
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

Theorem fixshiftl_word_lsl:
  !n w. (w2v (word_lsl w n)) = (fixshiftl (w2v w) n)
Proof
   rpt strip_tac >> Cases_on `n`
      (* ZERO *)
      >- (simp[fixshiftl_def,word_lsl_def,w2v_def] >> simp[shiftl_def] >> simp[PAD_RIGHT])
      (* SUCCESSOR *)
      >> simp[fixshiftl_word_lsl_SUC]
QED

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

val fixasr_word_asr_lemma3 = Q.prove(
  `!(w:'a word) h t. (w2v w = (h::t)) ==> (h = word_msb w)`,
  simp[w2v_def,word_msb_def] >> simp[FCP,FCP_BETA,CART_EQ] >> rpt STRIP_TAC
  >> POP_ASSUM (ASSUME_TAC o (Q.AP_TERM `HD`)) >> fs[]
  >> Cases_on `dimindex(:'a)` >> fs[] >- (CCONTR_TAC >> ASSUME_TAC DIMINDEX_GT_0 >> simp[])
  >> pop_assum (assume_tac o GSYM)
  >> full_simp_tac std_ss [HD_GENLIST]
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

Theorem fixasr_word_asr:
  !(n:num) (w:'a word). (w2v (word_asr w n)) = (fixasr (w2v w) n)
Proof
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
QED

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

Theorem DIV_TIMES:
  !x y. (0 < y) ==> (y*(x DIV y) = x - (x MOD y))
Proof
  rpt STRIP_TAC
  >> IMP_RES_TAC DIVISION
  >> POP_ASSUM (fn modassum => POP_ASSUM (fn divassum => ASSUME_TAC (AP_TERM ``\l. l - x MOD y`` (ISPEC ``x:num`` divassum))))
  >> fs[]
QED

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

Theorem rotate_w2v:
 !w:('a word) (n:num). rotate (w2v w) n = w2v (word_ror w n)
Proof
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
QED


(* TODO prove that `i2vN x N` represents the same value as `(i2w x): N word` *)
val i2vN_def = Define`
    i2vN (i : int) (n : num) : bitstring = if i < 0
                      then fixsub (fixwidth n [F]) (fixwidth n (n2v (Num (-i))))
                      else fixwidth n (n2v (Num i))`

Theorem i2vN_length:
  !i n. (LENGTH (i2vN i n)) = n
Proof
    rpt STRIP_TAC >> REWRITE_TAC[i2vN_def] >> Cases_on `i < 0` >>
    simp[length_fixwidth,fixsub_length]
QED

Theorem w2v_0w:
   w2v (0w:'a word) = fixwidth (dimindex(:'a)) [F]
Proof
   simp[w2v_n2w] >> EVAL_TAC
QED

Theorem w2v_i2w:
  !i. w2v ((i2w i):'a word)
                          = i2vN i (dimindex (:'a))
Proof
  STRIP_TAC >> simp[i2w_def] >> BasicProvers.TOP_CASE_TAC >> simp[i2vN_def]
   >- (fs[GSYM w2v_0w]
       >> ONCE_REWRITE_TAC[GSYM w2v_n2w]
       >> simp[fixsub_word_sub]
       >> MK_COMB_TAC
       >> simp[])
   >> simp[w2v_n2w]
QED

val v2comp_def = Define`
    v2comp (v : bitstring) : bitstring
    = fixwidth (LENGTH v) (n2v (2**(LENGTH v) - (v2n v)))`

val v2i_def = Define`
     (v2i [] : int = 0) /\
     (v2i v : int = if HD v then ~(int_of_num (v2n (v2comp v))) else int_of_num (v2n v))`

Theorem v2i_w2v:
  !w. v2i (w2v w) = w2i w
Proof
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
QED

val blt_def = Define`
    blt x y <=> v2n x < v2n y`

val bgt_def = Define`
    bgt x y <=> v2n x > v2n y`

val bleq_def = Define`
    bleq x y <=> v2n x <= v2n y`

val bgeq_def = Define`
    bgeq x y <=> v2n x >= v2n y`

val blt_sign_def = Define`
    blt_sign x y <=> v2i x < v2i y`

val bgt_sign_def = Define`
    bgt_sign x y <=> v2i x > v2i y`

val bleq_sign_def = Define`
    bleq_sign x y <=> v2i x <= v2i y`

val bgeq_sign_def = Define`
    bgeq_sign x y <=> v2i x >= v2i y`

val btest_def = Define`
    btest x y =
      let m = MAX (LENGTH x) (LENGTH y)
       in
         band x y = fixwidth m (n2v 0)`

Theorem CART_EQ_INV:
  !x:('a ** 'b) y. (x = y) = (!i. i < dimindex(:'b)
  ==> (x ' (dimindex(:'b) - (i+1)) = y ' (dimindex(:'b) - (i+1))))
Proof
   rpt STRIP_TAC >> simp[fcpTheory.CART_EQ] >> EQ_TAC >> rpt STRIP_TAC
    \\ `dimindex(:'b) - (i+1) < dimindex(:'b)`
        by (Cases_on `dimindex(:'b)` \\ fs[DIMINDEX_GT_0])
    \\ RES_TAC
    \\ `i = dimindex(:'b) - (dimindex(:'b) - (i+1) + 1)` by (
          Cases_on `dimindex(:'b)`
       \\ simp[INST_TYPE [alpha |-> Type`:'b`] DIMINDEX_GT_0,Once SUB_PLUS,ADD1])
    \\ fs[]
QED

Theorem w2v_eq[simp]:
   !x:('a word) y. (w2v x = w2v y) = (x = y)
Proof
  simp[w2v_def,GENLIST_FUN_EQ,CART_EQ_INV]
QED

Theorem v2n_singleton:
  v2n[F] = 0 /\ v2n [T] = 1
Proof
  rw[numposrepTheory.num_from_bin_list_def,v2n_def]
  \\ simp[Once numposrepTheory.l2n_def,bitify_reverse_map]
  \\ simp[Once numposrepTheory.l2n_def]
QED

Theorem v2n_same_length_11:
  !x y.
    LENGTH x = LENGTH y ==>
    (v2n x = v2n y <=> x = y)
Proof
  Induct \\ fs[]
  \\ strip_tac \\ Induct \\ fs[]
  \\ rw[]
  \\ eq_tac \\ rw[] \\ fs[]
  \\ rename1`v2n (a::x) = v2n(b::y)`
  \\ `a :: x = [a] ++ x` by simp[]
  \\ pop_assum(fn a => SUBST_ALL_TAC a)
  \\ `b :: y = [b] ++ y` by simp[]
  \\ pop_assum(fn a => SUBST_ALL_TAC a)
  \\ fs[v2n_append]
  >- (reverse(Cases_on`a` \\ fs[v2n_singleton])
      \\ reverse(Cases_on`b` \\ fs[v2n_singleton])
      >- (assume_tac(Q.SPEC`x` v2n_lt)
          \\ rfs[]
      )
      \\ assume_tac(Q.SPEC`y` v2n_lt)
      \\ rfs[])
  \\ Cases_on`a` \\ fs[v2n_singleton]
  \\ Cases_on`b` \\ fs[v2n_singleton] \\ rfs[]
  >-(assume_tac(Q.SPEC`y` v2n_lt) \\ rfs[])
  >-(assume_tac(Q.SPEC`x` v2n_lt) \\ rfs[])
  \\ first_x_assum(assume_tac o Q.SPEC `y`)
  \\ fs[]
QED

Theorem length_shiftl:
    !x n. LENGTH (shiftl x n) = LENGTH x + n
Proof
    simp[shiftl_def]
    \\ simp[PAD_RIGHT]
QED

Theorem EL_bitwise:
    i < LENGTH (bitwise f xs ys) /\ LENGTH xs = LENGTH ys ==>
    EL i (bitwise f xs ys) = f (EL i xs) (EL i ys)
Proof
  fs [bitstringTheory.bitwise_def]
  \\ qid_spec_tac `xs`
  \\ qid_spec_tac `ys`
  \\ qid_spec_tac `i`
  \\ Induct_on `xs` \\ Cases_on `ys` \\ fs []
  \\ rpt gen_tac \\ Cases_on `i` \\ fs []
QED

Theorem EL_w2v:
  !w i. i < dimindex (:'a) ==>
          EL i (w2v (w:'a word)) = w ' (dimindex (:'a) − (i + 1))
Proof
  fs [bitstringTheory.w2v_def]
QED

Theorem bitwise_w2v_w2v:
  !(w1:'a word) (w2:'a word) f.
      bitwise f (w2v w1) (w2v w2) = w2v ((FCP i. f (w1 ' i) (w2 ' i)) :'a word)
Proof
  fs [listTheory.LIST_EQ_REWRITE]
  \\ rpt gen_tac
  \\ conj_asm1_tac
  THEN1 fs [bitstringTheory.bitwise_def]
  \\ fs [] \\ rw []
  \\ fs [EL_bitwise,EL_w2v]
  \\ fs [fcpTheory.FCP_BETA]
QED

Theorem length_zero_extend2:
   !x n. LENGTH (zero_extend n x) = MAX n (LENGTH x)
Proof
 rw[zero_extend_def,PAD_LEFT] \\ simp[MAX_DEF]
QED


Theorem zero_extend_eq:
  LENGTH v <= n ⇒
  zero_extend n v = REPLICATE (n - LENGTH v) F ++ v
Proof
  rw[]>> match_mp_tac LIST_EQ>>
  rw[length_zero_extend,el_zero_extend]>>
  simp[EL_APPEND_EQN,EL_REPLICATE]>>
  simp[NOT_LESS]>>
  simp[length_zero_extend2]>>
  simp[MAX_DEF]
QED

Theorem v2n_fixwidth:
  LENGTH v ≤ n ⇒
  v2n(fixwidth n v) = v2n v
Proof
  rw[fixwidth_def]>>fs[]
  >- (
    simp[zero_extend_eq]>>
    simp[v2n_append,v2n_eq0]>>
    simp[REPLICATE_GENLIST])
  >>
    `LENGTH v=n` by fs[]>>
    fs[]
QED

Theorem LENGTH_n2v:
  !n. LENGTH (n2v n) = if n = 0 then 1 else SUC (LOG 2 n)
Proof
 simp[n2v_def,num_to_bin_list_def,boolify_reverse_map] \\ rw[]
 \\ ASSUME_TAC (Q.SPEC `2` LENGTH_n2l) \\ fs[]
QED

(* v2n ignores all falses *)
val v2n_irrel = Q.prove(`
  ∀ls.
  v2n ls = v2n (SND (SPLITP I ls))`,
  Induct>>
  fs[v2n_def,bitify_reverse_map,num_from_bin_list_def]
  >-
    EVAL_TAC
  >>
  rw[]
  >-
    simp[SPLITP]
  >>
    simp[l2n_2_append,SPLITP]);

Theorem EVERY_F_IMP_REPLICATE:
  ∀fs.EVERY $~ fs ⇒
  REPLICATE (LENGTH fs) F = fs
Proof
  Induct>>fs[]
QED

val v2n_cons = Q.prove(`
  (v2n (T::ls) = 2**LENGTH ls + v2n ls) ∧
  (v2n (F::ls) = v2n ls)`,
  rw[]>>
  ONCE_REWRITE_TAC[CONS_APPEND]>>
  simp[v2n_append]>>
  EVAL_TAC>>fs[]);

Theorem n2l_DIV_MOD:
   !b n k. 1 < b /\ 0 < k /\ b ** k <= n ==>
   (n2l b (n MOD (b ** k)) ++ REPLICATE (k - LENGTH (n2l b (n MOD (b ** k)))) 0 ++
    n2l b (n DIV (b ** k)) = n2l b n)
Proof
  ho_match_mp_tac numposrepTheory.n2l_ind
  \\ rw[]
  \\ Cases_on`b < 2` \\ fs[]
  \\ Cases_on`n < b` \\ fs[]
  >- ( `b <= b ** k` by ( Cases_on`k` \\ fs[EXP] ) \\ fs[] )
  \\ Cases_on`k` \\ fs[EXP]
  \\ fs[GSYM DIV_DIV_DIV_MULT]
  \\ fs[DIV_MOD_MOD_DIV]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ qmatch_assum_rename_tac`b * b ** k <= n`
  \\ Cases_on`k=0` \\ fs[EXP]
  >- (
    rw[Once numposrepTheory.n2l_def,REPLICATE_NIL] \\
    rw[numposrepTheory.LENGTH_n2l])
  \\ simp[Once numposrepTheory.n2l_def]
  \\ simp[MOD_MULT_MOD]
  \\ fs[numposrepTheory.LENGTH_n2l]
  \\ first_x_assum(qspec_then`k`mp_tac)
  \\ impl_tac >- simp[X_LE_DIV]
  \\ disch_then(assume_tac o SYM) \\ simp[]
  \\ rfs[DIV_EQ_0]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- simp[logrootTheory.LOG_DIV,ADD1]
  \\ IF_CASES_TAC \\ fs[]
  >- (
    `0 < b ** k` by simp[] \\
    `0 < b * b ** k` by simp[LESS_MULT2] \\
    fs[MOD_EQ_0_DIVISOR,ZERO_DIV,Once numposrepTheory.n2l_def]
    \\ Cases_on`k` \\ fs[REPLICATE]
    \\ metis_tac[MULT_ASSOC] )
  \\ conj_asm1_tac
  >- (
    qspecl_then[`b ** k`,`b`]mp_tac MOD_MULT_MOD
    \\ simp[]
    \\ disch_then(qspec_then`n`mp_tac)
    \\ simp[LESS_MOD])
  \\ simp[]
  \\ `n MOD b DIV b = 0` by simp[DIV_EQ_0]
  \\ simp[Once numposrepTheory.n2l_def]
  \\ rewrite_tac[GSYM REPLICATE,ADD1]
  \\ `LOG b (n MOD b) = 0`
  by ( simp[logrootTheory.LOG_EQ_0] )
  \\ simp[]
QED

val n2v_v2n_T = Q.prove(`
  n2v (v2n (T::ls)) = T::ls`,
  completeInduct_on`LENGTH ls`>>
  rw[]>>
  simp[v2n_cons]>>
  Cases_on`LENGTH ls = 0`
  >-
    (fs[]>>EVAL_TAC>>fs[])
  >>
  simp[n2v_def,boolify_reverse_map,num_to_bin_list_def]>>
  qspecl_then [`2`,`v2n ls + 2**LENGTH ls`,`LENGTH ls`] mp_tac (GSYM n2l_DIV_MOD)>>
  simp[]>>
  `v2n ls < 2** LENGTH ls` by simp[v2n_lt]>> simp[]>>
  rw[]>>
  drule bitTheory.DIV_MULT_1>>
  simp[]>>rw[]>>
  `?fs rest. SPLITP I ls = (fs,rest)` by
    (Cases_on`SPLITP I ls`>>fs[])>>
  drule SPLITP_JOIN>>
  rw[]>>
  `v2n (fs++rest) = v2n rest` by
    simp[Once v2n_irrel]>>
  simp[map_replicate]>>
  Cases_on`fs = []`>>fs[]
  >-
    (Cases_on`rest`>>fs[]>>
    first_x_assum(qspec_then`LENGTH t` mp_tac)>>
    simp[]>>
    disch_then(qspec_then`t` assume_tac)>>fs[]>>
    imp_res_tac SPLITP_IMP>>
    fs[n2v_def,boolify_reverse_map,num_to_bin_list_def]>>
    first_x_assum(mp_tac o Q.AP_TERM `LENGTH`)>>
    simp[])
  >>
  Cases_on`rest`>>fs[]
  >-
    (`n2l 2 (v2n []) = [0]` by EVAL_TAC>>
    imp_res_tac SPLITP_IMP>>
    fs[]>>
    REWRITE_TAC[GSYM(Once SNOC_APPEND)]>>
    REWRITE_TAC[SNOC_REPLICATE]>>
    drule EVERY_F_IMP_REPLICATE>>
    `SUC(LENGTH fs -1) = LENGTH fs` by
      (Cases_on`fs`>>fs[ADD1])>>
    metis_tac[])
  >>
    (first_x_assum(qspec_then`LENGTH t` mp_tac)>>
    simp[]>>
    disch_then(qspec_then`t` assume_tac)>>fs[]>>
    imp_res_tac SPLITP_IMP>>
    fs[n2v_def,boolify_reverse_map,num_to_bin_list_def]>>
    first_x_assum(mp_tac o Q.AP_TERM `LENGTH`)>>
    simp[]>>
    metis_tac[EVERY_F_IMP_REPLICATE]));

Theorem n2v_v2n:
  n2v (v2n ls) =
  if SND (SPLITP I ls) = [] then [F]
  else SND (SPLITP I ls)
Proof
  Cases_on`SPLITP I ls`>>
  imp_res_tac SPLITP_IMP>>fs[]>>
  drule SPLITP_JOIN>>
  rw[]>>fs[]
  >-
    (simp [Once v2n_irrel]>>
    EVAL_TAC)
  >>
  simp [Once v2n_irrel]>>
  Cases_on`r`>>fs[]>>
  metis_tac[n2v_v2n_T]
QED

val _ = export_theory()
