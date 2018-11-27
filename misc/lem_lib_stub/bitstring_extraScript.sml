open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory integerTheory arithmeticTheory;
open metisLib;

val _ = numLib.prefer_num();

val _ = new_theory "bitstring_extra"

val fixadd_def = Define`
   fixadd a b =
     let m = MAX (LENGTH a) (LENGTH b) in
        fixwidth m (n2v (v2n a + v2n b))`

(* subtraction is negate b and add a, then add 1 *)

val fixsub_def = Define`
   fixsub a b = 
     let m = MAX (LENGTH a) (LENGTH b) in
     let fa = fixwidth m a in
     let fb = fixwidth m b
      in
        fixadd (fixadd fa (bnot fb)) (n2v 1)`
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


val fixadd_word_add = Q.store_thm("fixadd_word_add",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y))
     ==> (v2n (fixadd x y) = w2n (word_add (v2w x:'a word) (v2w y:'a word)))`, 
      REPEAT STRIP_TAC >> REWRITE_TAC [fixadd_def] >> cheat
    );

val fixsub_lemma1 = Q.store_thm("fixsub_lemma1",
  `!x y. ((v2w x:'a word) - (v2w y:'a word) = ((v2w x:'a word) + ~(v2w y:'a word) + (1w:'a word)))`,
        REPEAT STRIP_TAC >> REWRITE_TAC [word_sub_def] >> REWRITE_TAC [WORD_NEG] >> METIS_TAC [WORD_ADD_ASSOC]); 



val fixsub_word_sub = Q.store_thm("fixsub_word_sub",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y)) 
     ==> (v2n (fixsub x y) = w2n ((v2w x:'a word) - (v2w y:'a word)))`,
   REPEAT STRIP_TAC >> simp[fixsub_def] >> REWRITE_TAC [fixsub_lemma1] >> ASM_REWRITE_TAC [fixadd_word_add] >> cheat
           );

val fixshiftr_def = Define`
   fixshiftr a n =
     let m = LENGTH a in
        fixwidth m (shiftr a n)`

val fixasr_def = Define`
   (fixasr a 0 = a) /\
   (fixasr a (SUC n) = fixasr (sign_extend (LENGTH a) (TAKE (LENGTH a - 1) a)) n)`

val fixshiftl_def = Define`
   fixshiftl a n =
     let m = LENGTH a in
        fixwidth m (shiftl a n)`

(* TODO prove properties of fixed size shifts *)

val fixshiftr_word_lsr = Q.store_thm("fixshiftr_word_lsr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_lsr w n)) = (fixshitr a n))`,cheat);

val fixshiftl_word_lsl = Q.store_thm("fixshiftl_word_lsl",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_lsl w n)) = (fixshitl a n))`,cheat);

val fixasr_word_asr = Q.store_thm("fixasr_word_asr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_asr w n)) = (fixasr a n))`,cheat);

(* TODO prove that `i2vN x N` represents the same value as `(i2w x): N word` *)
val i2vN_def = Define`
    i2vN (i : int) (n : num) : bitstring = if i < 0 then fixsub (fixwidth n [F]) (fixwidth n (n2v (Num (-i)))) else fixwidth n (n2v (Num i))`


val i2vN_length = Q.store_thm("i2vN_length",`!i n. (LENGTH (i2vN i n)) = n`,cheat);
val i2vN_i2w = Q.store_thm("i2vN_i2w",`!i n. ((i2w i):'a word) = ((v2w (i2vN i (dimindex (:'a)))):'a word)`,cheat);

val v2comp_def = Define`
    v2comp (v : bitstring) : bitstring = fixwidth (LENGTH v) (n2v (2**(LENGTH v) - (v2n v)))`

(* TODO prove a theorem relating w2i and v2i *)
val v2i_def = Define`
    (v2i ([] : bitstring) : int = 0) /\
    (v2i ([T] : bitstring) : int = -1) /\
    (v2i ([F] : bitstring) : int = 0) /\
    (v2i ((h::t) : bitstring) : int = if ~h then int_of_num (v2n t) else -(int_of_num (v2n (v2comp t))))`
val v2i_w2i = Q.store_thm("v2i_w2i",`!v w. (v = w2v w) = (v2i v = w2i w)`,cheat);

val _ = export_theory()
