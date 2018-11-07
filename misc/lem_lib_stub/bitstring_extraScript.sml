open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory integerTheory;

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

val fixadd_word_add = Q.store_thm("fixadd_word_add",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y))
     ==> (v2n (fixadd x y) = w2n (word_add (v2w x:'a word) (v2w y:'a word)))`,cheat);

val fixsub_word_sub = Q.store_thm("fixsub_word_sub",
  `!x y. (dimindex (:'a) = MAX (LENGTH x) (LENGTH y)) 
     ==> (v2n (fixsub x y) = w2n (word_sub (v2w x:'a word) (v2w y:'a word)))`,cheat);

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

val fixshiftr_word_lsr = Q.store_thm("fixshiftr_word_shiftr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_lsr w n)) = (fixshitr a n))`,cheat);

val fixshiftl_word_lsl = Q.store_thm("fixshiftl_word_shiftr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_lsl w n)) = (fixshitl a n))`,cheat);

val fixasr_word_asr = Q.store_thm("fixasr_word_asr",
  `!a n w. (w2v w = a)
     ==> ((w2v (word_asr w n)) = (fixasr a n))`,cheat);

(* TODO define i2vN and prove that `i2vN x N` represents the same value as `(i2w x): N word` *)
val i2vN_def = Define`
    i2vN (i : int) (n : num) : bitstring = n2v n`


val i2vN_length = Q.store_thm("i2vN_length",`!i n. (LENGTH (i2vN i n)) = n`,cheat);
val i2vN_i2w = Q.store_thm("i2vN_i2w",`!i n. ((i2w i):'a word) = ((v2w (i2vN i (dimindex (:'a)))):'a word)`,cheat);

(* TODO define v2i and prove a theorem relating w2i and v2i *)
val v2i_def = Define`
    v2i (v : bitstring) : int = 0`
val v2i_w2i = Q.store_thm("v2i_w2i",`!v w. (v = w2v w) = (v2i v = w2i w)`,cheat);

val _ = export_theory()
