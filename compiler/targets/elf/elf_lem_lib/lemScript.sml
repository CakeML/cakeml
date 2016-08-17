(*========================================================================*)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

open finite_mapTheory finite_mapLib
open HolKernel Parse boolLib bossLib;
open pred_setSimps pred_setTheory
open finite_mapTheory
open set_relationTheory
open integerTheory intReduce quantHeuristicsLib;
open wordsTheory

val _ = numLib.prefer_num();

val _ = new_theory "lem"

val failwith_def = Define `failwith (s:'a) = (ARB:'b)`;

val set_CASE_def = zDefine `
  set_CASE s c_emp c_sing c_else =
    (if s = {} then c_emp else (
     if (FINITE s /\ (CARD s = 1)) then c_sing (CHOICE s) else
     c_else))`

val set_CASE_emp = prove ( 
``!c_emp c_sing c_else. set_CASE {} c_emp c_sing c_else = c_emp``,
  SIMP_TAC std_ss [set_CASE_def])



val set_CASE_sing = prove (
``!x c_emp c_sing c_else. set_CASE {x} c_emp c_sing c_else = c_sing x``,
  SIMP_TAC (std_ss++PRED_SET_ss) [set_CASE_def])


val set_CASE_infinite = prove (``~(FINITE s) ==> (set_CASE s c_emp c_sing c_else = c_else)``,
REPEAT STRIP_TAC THEN
`~ (s = {})` by METIS_TAC [FINITE_EMPTY] THEN
ASM_SIMP_TAC (std_ss++PRED_SET_ss) [set_CASE_def])

val set_CASE_else_two_elems = store_thm ("set_CASE_else_two_elems",
``(x1 IN s /\ x2 IN s /\ ~(x1 = x2)) ==>
  (set_CASE s c_emp c_sing c_else = c_else)``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FINITE s`) THEN1 (
  ASM_SIMP_TAC std_ss [set_CASE_infinite]
) THEN

`~(s = {})` by (PROVE_TAC [MEMBER_NOT_EMPTY]) THEN

`2 <= CARD s` by ALL_TAC THEN1 (
  `CARD {x1; x2} = 2` by ASM_SIMP_TAC (std_ss++PRED_SET_ss) [] THEN
  `{x1; x2} SUBSET s` by ASM_SIMP_TAC (std_ss++PRED_SET_ss) [] THEN
  PROVE_TAC [CARD_SUBSET]
) THEN

ASM_SIMP_TAC arith_ss [set_CASE_def]);


val set_CASE_else_1 = prove (``~(x1 = x2) ==> (set_CASE (x1 INSERT (x2 INSERT s)) c_emp c_sing c_else = c_else)``,
REPEAT STRIP_TAC THEN
MATCH_MP_TAC set_CASE_else_two_elems THEN
ASM_SIMP_TAC (std_ss++PRED_SET_ss) [])


val set_CASE_else_2 = prove (``(x1 = x2) ==> (set_CASE (x1 INSERT (x2 INSERT s)) c_emp c_sing c_else = set_CASE (x2 INSERT s) c_emp c_sing c_else)``,
SIMP_TAC (std_ss++PRED_SET_ss) [])


val set_CASE_REWRITES = save_thm ("set_CASE_REWRITES",
  LIST_CONJ (map GEN_ALL [set_CASE_emp, set_CASE_sing, set_CASE_else_1, set_CASE_else_2, set_CASE_infinite]));

val _ = export_rewrites ["set_CASE_REWRITES"]


val set_CASE_compute = store_thm ("set_CASE_compute", ``
   (!c_sing c_emp c_else. set_CASE {} c_emp c_sing c_else = c_emp) /\
   (!x c_sing c_emp c_else.
      set_CASE {x} c_emp c_sing c_else = c_sing x) /\
   (!x2 x1 s c_sing c_emp c_else.
      x1 <> x2 ==>
      (set_CASE (x1 INSERT x2 INSERT s) c_emp c_sing c_else =
       c_else)) /\
   (!x2 x1 s c_sing c_emp c_else.
      (set_CASE (x1 INSERT x2 INSERT s) c_emp c_sing c_else =
       if (x1 = x2) then set_CASE (x2 INSERT s) c_emp c_sing c_else else c_else))``,
METIS_TAC[set_CASE_REWRITES]);


val SET_FILTER_def = zDefine `
 (SET_FILTER P s = ({e | e | (e IN s) /\ P e}))`;

val SET_FILTER_REWRITES = store_thm ("SET_FILTER_REWRITES",``
  (!P. (SET_FILTER P {} = {})) /\
  (!P x s. P x ==> (SET_FILTER P (x INSERT s) = x INSERT (SET_FILTER P s))) /\
  (!P x s. (~(P x) ==> (SET_FILTER P (x INSERT s) = SET_FILTER P s)))``,

SIMP_TAC (std_ss++PRED_SET_ss) [SET_FILTER_def, EXTENSION] THEN
METIS_TAC[])

val _ = export_rewrites ["SET_FILTER_REWRITES"]


val SET_FILTER_compute = store_thm ("SET_FILTER_compute",``
  (!P. (SET_FILTER P {} = {})) /\
  (!P x s. (SET_FILTER P (x INSERT s) = if P x then 
        x INSERT (SET_FILTER P s) else (SET_FILTER P s)))``,
METIS_TAC [SET_FILTER_REWRITES])


val _ = computeLib.add_persistent_funs ["set_CASE_compute", "SET_FILTER_compute"]


val SET_SIGMA_def = zDefine 
  `SET_SIGMA P Q = { (x, y) | x IN P /\ y IN Q x }`;

val SET_SIGMA_EMPTY = store_thm(
  "SET_SIGMA_EMPTY",
  ``!Q. SET_SIGMA {} Q = {}``,
  SIMP_TAC (std_ss++PRED_SET_ss) [SET_SIGMA_def, EXTENSION]);
val _ = export_rewrites ["SET_SIGMA_EMPTY"]
val _ = computeLib.add_persistent_funs ["SET_SIGMA_EMPTY"]

val SET_SIGMA_INSERT_LEFT = store_thm(
  "SET_SIGMA_INSERT_LEFT",
  ``!P Q x. SET_SIGMA (x INSERT P) Q = 
     (IMAGE (\y. (x, y)) (Q x)) UNION (SET_SIGMA P Q)``,
  SIMP_TAC (std_ss++PRED_SET_ss) [SET_SIGMA_def, EXTENSION] THEN
  METIS_TAC[])
val _ = export_rewrites ["SET_SIGMA_INSERT_LEFT"]
val _ = computeLib.add_persistent_funs ["SET_SIGMA_INSERT_LEFT"]


val _ = computeLib.add_persistent_funs ["list.LIST_TO_SET"]


val FMAP_TO_SET_def = zDefine 
  `FMAP_TO_SET m = IMAGE (\k. (k, FAPPLY m k)) (FDOM m)`;

val FMAP_TO_SET_FEMPTY = store_thm ("FMAP_TO_SET_FEMPTY",
  ``FMAP_TO_SET FEMPTY = {}``,
SIMP_TAC std_ss [FMAP_TO_SET_def, FDOM_FEMPTY, IMAGE_EMPTY]);
val _ = export_rewrites ["FMAP_TO_SET_FEMPTY"]
val _ = computeLib.add_persistent_funs ["FMAP_TO_SET_FEMPTY"]

val FMAP_TO_SET_FUPDATE = store_thm ("FMAP_TO_SET_FUPDATE",
  ``FMAP_TO_SET (FUPDATE m (k, v)) = (k, v) INSERT (FMAP_TO_SET (m \\ k))``,
SIMP_TAC (std_ss ++ PRED_SET_ss) [FMAP_TO_SET_def, FDOM_FUPDATE, FAPPLY_FUPDATE_THM, EXTENSION,
  FDOM_DOMSUB, DOMSUB_FAPPLY_THM] THEN
METIS_TAC[]);
val _ = export_rewrites ["FMAP_TO_SET_FUPDATE"]
val _ = computeLib.add_persistent_funs ["FMAP_TO_SET_FUPDATE"]


val IN_FMAP_TO_SET = store_thm ("IN_FMAP_TO_SET",
  ``(k, v) IN FMAP_TO_SET m = (FLOOKUP m k = SOME v)``,
SIMP_TAC (std_ss++PRED_SET_ss) [FMAP_TO_SET_def, FLOOKUP_DEF] THEN
METIS_TAC[optionTheory.option_CLAUSES])

val FUPDATE_NEQ_FEMPTY = store_thm ("FUPDATE_NEQ_FEMPTY", ``(FUPDATE m (k, v) = FEMPTY) = F``,
  SIMP_TAC (std_ss++PRED_SET_ss) [fmap_EXT, FDOM_FUPDATE, FDOM_FEMPTY])
val _ = export_rewrites ["FUPDATE_NEQ_FEMPTY"]
val _ = computeLib.add_persistent_funs ["FUPDATE_NEQ_FEMPTY"]

val FUPDATE_EQ_FUPDATE = store_thm ("FUPDATE_EQ_FUPDATE", 
  ``(FUPDATE m (k, v) = FUPDATE m' (k', v')) = 
    (k IN FDOM (FUPDATE m' (k', v')) /\
     (FUPDATE m' (k', v') ' k = v) /\
     (m \\ k = (FUPDATE m' (k', v') \\ k))) ``,

  EQ_TAC THEN STRIP_TAC THEN1 (
     POP_ASSUM (ASSUME_TAC o GSYM) THEN
     ASM_REWRITE_TAC [] THEN
     SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE, DOMSUB_FUPDATE]
  ) THEN
  FULL_SIMP_TAC std_ss [fmap_EXT, EXTENSION, FDOM_DOMSUB, IN_DELETE, FDOM_FUPDATE, IN_INSERT,
     DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM] THEN
  METIS_TAC[]
)

val _ = export_rewrites ["FUPDATE_EQ_FUPDATE"]
val _ = computeLib.add_persistent_funs ["FUPDATE_EQ_FUPDATE"]


val FEVERY_FUPDATE_DOMSUB = store_thm ("FEVERY_FUPDATE_DOMSUB",
  ``(FEVERY P (FUPDATE m (k, v))) = (P (k, v) /\ FEVERY P (m \\ k))``,
SIMP_TAC std_ss [FEVERY_FUPDATE, fmap_domsub]);

val _ = computeLib.add_persistent_funs ["finite_map.FRANGE_FEMPTY", "finite_map.FRANGE_FUPDATE_DOMSUB", 
  "finite_map.FEVERY_FEMPTY", "FEVERY_FUPDATE_DOMSUB"]

val _ = computeLib.add_persistent_funs ["finite_map.o_f_FUPDATE", "finite_map.o_f_FEMPTY", 
   "finite_map.FCARD_FEMPTY", "finite_map.FCARD_FUPDATE"]





val rcomp_empty_1 = store_thm ("rcomp_empty_1",
  ``({} OO r) = {}``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [rcomp_def, EXTENSION])

val rcomp_empty_2 = store_thm ("rcomp_empty_2",
  ``(r OO {}) = {}``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [rcomp_def, EXTENSION])

val rcomp_insert_compute = store_thm ("rcomp_insert_compute",
  ``(r1 OO ((x, y) INSERT r2)) = ((r1 OO r2) UNION (IMAGE (\ xy'. (FST xy', y)) (SET_FILTER (\ xy'. SND xy' = x) r1)))``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++quantHeuristicsLib.QUANT_INST_ss [std_qp]) [rcomp_def, EXTENSION, SET_FILTER_def] THEN
METIS_TAC[])

val _ = computeLib.add_persistent_funs ["rcomp_insert_compute", "rcomp_empty_1", "rcomp_empty_2"]


val rrestrict_eval = store_thm ("rrestrict_eval",
  ``rrestrict r s = SET_FILTER (\ (x, y). x IN s /\ y IN s) r``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++quantHeuristicsLib.QUANT_INST_ss [std_qp]) [rrestrict_def, EXTENSION, SET_FILTER_def])

val domain_eval = store_thm ("domain_eval",
  ``domain r = IMAGE FST r``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++QUANT_INST_ss [std_qp]) [domain_def, EXTENSION])

val range_eval = store_thm ("range_eval",
  ``range r = IMAGE SND r``,
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++QUANT_INST_ss [std_qp]) [range_def, EXTENSION])

val _ = computeLib.add_persistent_funs ["rrestrict_eval", "domain_eval", "range_eval"]

val w2int_def = Define `w2int (w : 'a word) = 
  let i1 = (w2n w) in
  let i2 = (INT_MAX (:'a)) in
  if i1 > i2 then (int_of_num i1 - (int_of_num (UINT_MAX (:'a)))) - 1 else int_of_num i1`


val _ = Define `MAP_TO_LIST m = SET_TO_LIST (\(x, y). FAPPLY m x = y)`

val _ = export_theory()
