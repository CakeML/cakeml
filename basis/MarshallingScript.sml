(*
  HOL functions that aid converting to and from the byte arrays that
  CakeML foreign-function interface (FFI) uses.
*)
open preamble

val _ = new_theory "Marshalling";

(* encode/decode nums as 2 or 8 bytes *)
(* similar to n2l & l2n but with padding *)
val n2w2_def = Define`
  n2w2 (i : num) : word8 list = [n2w (i DIV 256); n2w i]`

val n2w8_def = Define`
  n2w8 (i : num) : word8 list =
   [n2w (i DIV 256**7); n2w (i DIV 256**6);
    n2w (i DIV 256**5); n2w (i DIV 256**4);
    n2w (i DIV 256**3); n2w (i DIV 256**2);
    n2w (i DIV 256); n2w i]`

val w22n_def = Define`
  w22n ([b1; b0] : word8 list) = w2n b1 * 256 + w2n b0`

val w82n_def = Define`
  w82n ([b7; b6; b5; b4; b3; b2; b1; b0] : word8 list) =
  256 * ( 256 * ( 256 * ( 256 * ( 256 * ( 256 * ( 256 *
  w2n b7 + w2n b6) + w2n b5) + w2n b4) + w2n b3) + w2n b2) + w2n b1) + w2n b0`

Theorem w22n_n2w2:
   !i. i < 2**(2*8) ==> w22n (n2w2 i) = i
Proof
  rw[w22n_def,n2w2_def] >>
  `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >>
  first_x_assum (assume_tac o Q.SPEC`i`) >> fs[]
QED

Theorem n2w2_w22n:
   !b. LENGTH b = 2 ==> n2w2 (w22n b) = b
Proof
  Cases_on`b` >> fs[] >> Cases_on`t` >> rw[w22n_def,n2w2_def]
  >-(PURE_REWRITE_TAC[Once MULT_COMM] >> fs[ADD_DIV_ADD_DIV] >>
     fs[LESS_DIV_EQ_ZERO,w2n_lt_256]) >>
  fs[GSYM word_add_n2w,GSYM word_mul_n2w] >>
  `256w : word8 = 0w` by fs[GSYM n2w_dimword] >>
  first_x_assum (fn x => PURE_REWRITE_TAC[x]) >> fs[]
QED

Theorem w82n_n2w8:
   !i. i <= 256**8 - 1 ==> w82n (n2w8 i) = i
Proof
  rw[w82n_def,n2w8_def] >>
  `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >> rw[] >>
  NTAC 6(qmatch_abbrev_tac`256* i0 + x MOD 256 = x` >>
      `i0 = x DIV 256` suffices_by fs[] >>
      unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT]) >>
  PURE_REWRITE_TAC[Once ADD_COMM] >>
  qmatch_abbrev_tac`256* i0 + x MOD 256 = x` >>
  `i0 = x DIV 256` suffices_by fs[] >>
  unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT] >>
  `i DIV 256**7 <= 255` suffices_by fs[] >>
  fs[DIV_LE_X]
QED


Theorem nw8_w8n:
   !b. LENGTH b = 8 ==> n2w8 (w82n b) = b
Proof
  Cases_on`b` >> fs[] >>
  NTAC 4 (Cases_on`t` >> fs[] >> Cases_on`t'` >> fs[]) >>
  fs[w82n_def,n2w8_def] >> rpt (TRY strip_tac
  >-(rpt(qmatch_goalsub_abbrev_tac`(a + 256 * b) DIV m` >>
         `m = 256 * (m DIV 256)` by fs[Abbr`m`] >>
         first_x_assum (fn x => PURE_REWRITE_TAC[Once x]) >>
         `0 < m DIV 256` by fs[Abbr`m`] >>
         fs[GSYM DIV_DIV_DIV_MULT] >>
         `0 < 256 : num` by fs[] >> imp_res_tac ADD_DIV_ADD_DIV >>
         fs[] >>
         unabbrev_all_tac >> rw[LESS_DIV_EQ_ZERO,w2n_lt_256]) >>
     PURE_REWRITE_TAC[Once ADD_COMM] >>
     TRY (first_x_assum(fn x => PURE_REWRITE_TAC[x])) >>
     rw[LESS_DIV_EQ_ZERO,w2n_lt_256] >>
     fs[GSYM word_add_n2w,GSYM word_mul_n2w] >>
     `256w : word8 = 0w` by fs[GSYM n2w_dimword] >>
     first_x_assum (fn x => PURE_REWRITE_TAC[x]) >> fs[]))
QED

Theorem LENGTH_n2w2:
   !n. LENGTH(n2w2 n) = 2
Proof
  fs[n2w2_def]
QED

Theorem LENGTH_n2w8:
   !n. LENGTH(n2w8 n) = 8
Proof
  fs[n2w8_def]
QED
val _ = export_theory()
