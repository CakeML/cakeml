open preamble llistTheory 

(* Some temporal logic definitiosn based on lazy lists *)

val _ = new_theory"ltemporal"

val (eventually_rules,eventually_ind,eventually_cases) = Hol_reln`
  (!ll. P ll ==> eventually P ll) /\
  (!h t. ¬P (h:::t) /\ eventually P t ==> eventually P (h:::t)) `;

val eventually_thm = store_thm(
  "eventually_thm",
  ``(eventually P [||] = P [||]) /\
    (eventually P (h:::t) = (P (h:::t) \/(¬ P (h:::t) /\ eventually P t)))``,
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [eventually_cases])) THEN
  SRW_TAC [][]);

val _ = export_rewrites ["eventually_thm"]

val (always_rules,always_ind,always_cases) = Hol_reln`
  (!h t. (P (h ::: t) /\ always P t) ==> always P (h ::: t)) `;

val always_thm = store_thm(
  "always_thm",
  ``!h t. (always P (h ::: t) = (P (h ::: t) /\ always P t)) ∧
           ¬ always P [||]``,
  rw[Once always_cases] >> rw[Once always_cases]);
val _ = export_rewrites ["always_thm"]

val always_eventually = Q.store_thm("always_eventually", 
  `!ll. always (eventually P) ll ==> 
    ?k. (P (THE (LDROP k ll)) /\ always(eventually P) (THE(LDROP k ll)))`,
    HO_MATCH_MP_TAC always_ind >> 
    rw[always_thm,eventually_thm] >>
    qexists_tac`SUC k` >> fs[LDROP]);

val always_eventually_ind = Q.store_thm("always_eventually_ind",
  `(!ll. (P ll \/ (¬ P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
   !ll. always(eventually P) ll ==> Q ll`,
   strip_tac >> HO_MATCH_MP_TAC always_ind >> rw[] >> fs[]);

val always_DROP = Q.store_thm("always_DROP",
  `!ll. always P ll ==> always P (THE(LDROP k ll))`,
  Induct_on`k` >> Cases_on`ll` >> fs[always_thm,LDROP]);

val always_NOT_LFINITE = Q.store_thm("always_NOT_LFINITE",
    `!ll. always P ll ==> ¬ LFINITE ll`,
    HO_MATCH_MP_TAC always_ind >> rw[]);

val LDROP_1 = Q.store_thm("LDROP_1",
  `LDROP (1: num) (h:::t) = SOME t`,
  `LDROP (SUC 0) (h:::t) = SOME t` by fs[LDROP] >>
  metis_tac[arithmeticTheory.ONE]);

val Lnext_def = tDefine "Lnext" `
  Lnext P ll = if eventually P ll then
                        if P ll then 0
                        else SUC(Lnext P (THE (LTL ll)))
                     else ARB` 
 (exists_tac``\(P,ll') (P',ll). 
    ((P = P') /\ eventually P ll /\ eventually P ll' /\
    (LTL ll = SOME ll') /\ ¬ P ll)`` >>
    reverse(rw[relationTheory.WF_DEF,eventually_thm])
  >-(Cases_on`ll` >> fs[])
  >-(Cases_on`ll` >> fs[]) >>
  Cases_on`w` >> rename[`B(P, ll)`] >> rename[`B(P, ll)`] >>
  reverse(Cases_on`eventually P ll`)
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  rpt(LAST_X_ASSUM MP_TAC) >> qid_spec_tac `ll` >> 
  HO_MATCH_MP_TAC eventually_ind >> rw[]
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  Cases_on`B(P,ll)` >-(metis_tac[]) >>
  qexists_tac`(P,h:::ll)` >> fs[] >> rw[] >> pairarg_tac >> fs[]);

val _ = export_theory();
