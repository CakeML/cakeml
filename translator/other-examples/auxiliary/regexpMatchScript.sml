(*
  Regular expression matcher
  Author: Scott Owens
*)

(*---------------------------------------------------------------------------*)
(* SML code                                                                  *)
(*                                                                           *)
(*  datatype ''a re                                                          *)
(*        = Epsilon                                                          *)
(*           | Charset of ''a list                                           *)
(*           | Or      of ''a re * ''a re                                    *)
(*           | Then    of ''a re * ''a re                                    *)
(*           | Repeat  of ''a re;                                            *)
(*                                                                           *)
(* Match: ''a re list -> ''a list -> ''a re list option -> bool              *)
(*                                                                           *)
(* fun Match [] [] _ = true                                                  *)
(*   | Match [] _  _ = false                                                 *)
(*   | Match (Epsilon::t) w s = Match t w s                                  *)
(*   | Match (Charset c::t) [] s = false                                     *)
(*   | Match (Charset c::t) (d::w) s = c d andalso Match t w NONE            *)
(*   | Match (Or(r1,r2)::t) w s = Match (r1::t) w s orelse Match (r2::t) w s *)
(*   | Match (Then(r1,r2)::t) w s = Match (r1::r2::t) w s                    *)
(*   | Match (Repeat r::t) w s =                                             *)
(*       let val R = SOME (Repeat r::t)                                      *)
(*       in if s = R then false                                              *)
(*          else Match t w s orelse Match (r::Repeat r::t) w R               *)
(*       end                                                                 *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)


(* ------------------------------------------------------------------------- *)
(*  HOL Preliminaries                                                        *)
(* ------------------------------------------------------------------------- *)
open HolKernel bossLib Theory Parse Tactic boolLib Lib
open stringLib pairTheory arithmeticTheory listTheory optionTheory;

val thm_counter = Count.mk_meter();

(*---------------------------------------------------------------------------*)
(* Change free variable names to desired ones. Takes a list of (old,new)     *)
(* pairs (strings).                                                          *)
(*---------------------------------------------------------------------------*)

fun RENAME_FREES_TAC [] = ALL_TAC
  | RENAME_FREES_TAC ((old,new)::t) =
     Q.SPEC_TAC([QUOTE old],[QUOTE new]) THEN GEN_TAC THEN RENAME_FREES_TAC t;

(*---------------------------------------------------------------------------*)
(* Miscellaneous lemma; should already exist in HOL                          *)
(*---------------------------------------------------------------------------*)

val MEM_EXISTS_LEM = Q.prove
(`!x l. MEM x l = EXISTS (\y. y = x) l`,
 Induct_on `l` THEN EVAL_TAC THEN METIS_TAC []);

val _ = new_theory "regexpMatch";

(*--------------------------------------------------------------------------*)
(* Datatype of regular expressions. Note that by having Charset take a      *)
(* characteristic function means that regexp is not computably testable for *)
(* equality. Alternative: have Charset be a list or a finite map ...        *)
(*--------------------------------------------------------------------------*)

Hol_datatype
 `regexp = Epsilon                   (* Empty string *)
         | Charset of 'a list        (* Character set *)
         | Or of regexp => regexp    (* Union *)
         | Then of regexp => regexp  (* Concatenation *)
         | Repeat of regexp`;        (* Iterated concat, >= 0 *)

(*---------------------------------------------------------------------------*)
(* Parser fiddling to get | and # as infixes - we have to first get rid      *)
(* of their pre-defined behaviour.                                           *)
(*---------------------------------------------------------------------------*)

val _ = overload_on ("+", Term`$Or`);
val _ = overload_on ("#", Term`$Then`);

val _ = set_fixity "+" (Infixr 501);
val _ = set_fixity "#" (Infixr 601);

val regexp_cases = TypeBase.nchotomy_of ``:'a regexp``;

(*---------------------------------------------------------------------------*)
(* Semantics of regular expressions. sem r w means that word w (represented  *)
(* as a list) is in the language of regular expression r.                    *)
(*---------------------------------------------------------------------------*)

val sem_def =
 Define
  `(sem Epsilon w     = (w = []))                                         /\
   (sem (Charset C) w = (?x. (w = [x]) /\ MEM x C))                       /\
   (sem (r1 + r2) w   = sem r1 w \/ sem r2 w)                             /\
   (sem (r1 # r2) w   = ?w1 w2. (w = w1 ++ w2) /\ sem r1 w1 /\ sem r2 w2) /\
   (sem (Repeat r) w  = ?wlist. (w = FLAT wlist) /\ EVERY (sem r) wlist)`;

(*---------------------------------------------------------------------------*)
(* Some basic equivalences for regular expressions.                          *)
(*---------------------------------------------------------------------------*)

val regexp_repeat_thm = Q.prove
(`!r w.sem (Repeat r) w = sem (Epsilon + (r # (Repeat r))) w`,
 RW_TAC std_ss [] THEN EQ_TAC THEN RW_TAC list_ss [sem_def, FLAT]
 THENL [Cases_on `wlist` THEN RW_TAC list_ss [FLAT], ALL_TAC, ALL_TAC]
 THEN METIS_TAC [FLAT,EVERY_DEF]);

val repeat_to_ncat_thm = Q.prove
(`!r w.sem (Repeat r) w ==> ?n. sem (FUNPOW ($# r) n Epsilon) w`,
 RW_TAC list_ss [sem_def, FLAT, FUNPOW_SUC]
   THEN Q.EXISTS_TAC `LENGTH wlist`
   THEN Induct_on `wlist`
   THEN RW_TAC list_ss [sem_def, FLAT, FUNPOW_SUC]
   THEN EVAL_TAC THEN METIS_TAC []);

val ncat_to_repeat_thm = Q.prove
(`!r w n. sem (FUNPOW ($# r) n Epsilon) w ==> sem (Repeat r) w`,
 Induct_on `n` THENL [ALL_TAC, POP_ASSUM MP_TAC] THEN EVAL_TAC
   THEN RW_TAC list_ss [sem_def,FUNPOW_SUC] THENL
   [METIS_TAC [FLAT, EVERY_DEF],
    RES_TAC THEN Q.EXISTS_TAC `w1::wlist` THEN METIS_TAC [EVERY_DEF,FLAT]]);

val repeat_equals_ncat_thm = Q.prove
(`!r w. sem (Repeat r) w = ?n. sem (FUNPOW ($# r) n Epsilon) w`,
 METIS_TAC [ncat_to_repeat_thm, repeat_to_ncat_thm]);


(* ------------------------------------------------------------------------- *)
(* Regular expression matching algorithm                                     *)
(* ------------------------------------------------------------------------- *)

val match_defn =
 Hol_defn
   "match"
  `(match [] [] _                 = T)
/\ (match [] _  _                 = F)
/\ (match (Epsilon::t) w s        = match t w s)
/\ (match (Charset C::t) [] s     = F)
/\ (match (Charset C::t) (d::w) s = MEM d C /\ match t w NONE)
/\ (match ((r1 + r2)::t) w s      = match (r1::t) w s \/ match (r2::t) w s)
/\ (match ((r1 # r2)::t) w s      = match (r1::r2::t) w s)
/\ (match (Repeat r::t) w s       =
       if s = SOME (Repeat r::t) then
         F
       else
         match t w s \/ match (r::Repeat r::t) w (SOME (Repeat r::t)))`;

(*---------------------------------------------------------------------------*)
(* Termination proof                                                         *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Size of a regular expression, needed because the default metric gives     *)
(* Epsilon size 0 which won't work for the matcher's termination proof.      *)
(*---------------------------------------------------------------------------*)

val my_regexp_size_def =
 Define
  `(my_regexp_size Epsilon     = 1) /\
   (my_regexp_size (Charset _) = 1) /\
   (my_regexp_size (r1 + r2)   = 1 + my_regexp_size r1 + my_regexp_size r2) /\
   (my_regexp_size (r1 # r2)   = 1 + my_regexp_size r1 + my_regexp_size r2) /\
   (my_regexp_size (Repeat r)  = 1 + my_regexp_size r)`;

(*---------------------------------------------------------------------------*)
(* Star height of a regular expression                                       *)
(*---------------------------------------------------------------------------*)

val starHeight_def =
 Define
  `(starHeight Epsilon     = 0:num) /\
   (starHeight (Charset _) = 0) /\
   (starHeight (r1 + r2)   = MAX (starHeight r1) (starHeight r2)) /\
   (starHeight (r1 # r2)   = MAX (starHeight r1) (starHeight r2)) /\
   (starHeight (Repeat r)  = 1 + starHeight r)`;

val front_starHeight_def =
 Define
  `(front_starHeight [] sl = 0) /\
   (front_starHeight (h::t) sl =
      if (sl = SOME (h::t)) /\ ?r. h = Repeat r
       then 0
       else MAX (starHeight h) (front_starHeight t sl))`;

(*---------------------------------------------------------------------------*)
(* SUM (MAP my_regexp_size res) doesn't count the conses in the list like    *)
(* the builtin list measure does.  This is important for termination proof.  *)
(*---------------------------------------------------------------------------*)

val term_meas_def =
 Define
   `term_meas (res, str, stop) =
     (LENGTH str,
      front_starHeight res stop,
      SUM (MAP my_regexp_size res))`;

val (match_def, match_ind) = Defn.tprove
(match_defn,
 WF_REL_TAC `inv_image ($< LEX $< LEX $<) term_meas` THEN
   RW_TAC list_ss [term_meas_def, my_regexp_size_def] THEN
   PURE_ONCE_REWRITE_TAC [GSYM arithmeticTheory.LESS_OR_EQ] THEN
   RW_TAC list_ss [front_starHeight_def, starHeight_def]);

val _ = save_thm ("match_def", match_def);
val _ = save_thm ("match_ind", match_ind);

(* ------------------------------------------------------------------------- *)
(* Correctness Proof                                                         *)
(* ------------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------*)
(* Match implies the semantics                                               *)
(*---------------------------------------------------------------------------*)

val match_implies_sem = Q.prove
(`!rl w s. match rl w s ==> sem (FOLDR $# Epsilon rl) w`,
 recInduct match_ind THEN RW_TAC list_ss [match_def, sem_def] THENL
 [METIS_TAC [APPEND],
  METIS_TAC [],
  METIS_TAC [],
  FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
  MAP_EVERY Q.EXISTS_TAC [`[]`, `w`]
    THEN RW_TAC list_ss [] THEN METIS_TAC [FLAT,EVERY_DEF],
  FULL_SIMP_TAC list_ss []
    THEN MAP_EVERY Q.EXISTS_TAC [`w1 ++ FLAT wlist`, `w2'`]
    THEN RW_TAC list_ss []
    THEN METIS_TAC [FLAT,EVERY_DEF]]);

(*---------------------------------------------------------------------------*)
(* Semantics imply match                                                     *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* A match sequence is a witness to a path through the match algorithm that  *)
(* ends with T.                                                              *)
(*---------------------------------------------------------------------------*)

val m_def =
 Define
  `(m (Epsilon::t,w,s)  x     = (x = (t,w,s))) /\
   (m (Charset C::t,d::w,s) x = (x = (t,w,NONE)) /\ MEM d C) /\
   (m ((r1 + r2)::t, w, s) x  = (x = (r1::t,w,s)) \/ (x = (r2::t,w,s))) /\
   (m ((r1 # r2)::t, w, s) x  = (x = (r1::r2::t,w,s))) /\
   (m (Repeat r::t, w,s) x    = (x = (t, w, s)) \/
                                (x = (r::Repeat r::t, w, SOME(Repeat r::t))))/\
   (m _ _ = F)`;


val match_seq_def =
 Define
  `(match_seq [] = T) /\
   (match_seq [a] = (FST a = []) /\ (FST (SND a) = [])) /\
   (match_seq (a::b::rest) = m a b /\ match_seq (b::rest))`;

(*---------------------------------------------------------------------------*)
(* Induction and case analysis theorems for match sequences                  *)
(*---------------------------------------------------------------------------*)

val m_ind  = fetch "-" "m_ind";
val ms_ind = fetch "-" "match_seq_ind";

val m_ind_thm = Q.prove
(`!P:'a regexp list # 'a list # 'a regexp list option ->
     'a regexp list # 'a list # 'a regexp list option -> bool.
  (!t w s x. P (Epsilon::t,w,s) x) /\
  (!c t d w s x. P (Charset c::t,d::w,s) x) /\
  (!r1 r2 t w s x. P ((r1 + r2)::t,w,s) x) /\
  (!r1 r2 t w s x. P ((r1 # r2)::t,w,s) x) /\
  (!r t w s x. P (Repeat r::t,w,s) x) /\
  (!c t s x. P (Charset c::t,[],s) x) /\
  (!w s. P ([],w) s) ==>
  !v v1 v2 v3 v4 v5. P (v,v1,v2) (v3,v4,v5)`,
 METIS_TAC [ABS_PAIR_THM,m_ind]);

val m_thm = SIMP_RULE list_ss [] (Q.prove
(`!rl w s rl' w' s' r l.
      ~(s = SOME (Repeat r::l))   ==>
       (s' =  SOME (Repeat r::l)) ==>
       m (rl, w, s) (rl', w', s') ==>
      ((rl = Repeat r::l) /\ (w = w'))`,
 recInduct m_ind_thm THEN RW_TAC list_ss [m_def]));

val m_thm2 = Q.prove
(`!rl w s rl' w' s'. ~(w = w') ==> m (rl, w, s) (rl',w',s') ==> (s' = NONE)`,
 recInduct m_ind_thm THEN RW_TAC list_ss [m_def]);

val cases_lemma = Q.prove
(`!a: 'a regexp list # 'a list # 'a regexp list option.
     (?x. a = ([],[],x)) \/ (?h t x. a = ([],h::t,x)) \/
     (?t w s. a = (Epsilon::t,w,s)) \/
     (?c t w s. a = (Charset c::t,[],s)) \/
     (?c d t w s. a = (Charset c::t,d::w,s)) \/
     (?r1 r2 t w s. a = ((r1+r2)::t,w,s)) \/
     (?r1 r2 t w s. a = ((r1#r2)::t,w,s)) \/
     (?r t w s. a = (Repeat r::t,w,s))`,
 METIS_TAC [list_CASES,ABS_PAIR_THM,regexp_cases]);

val ms_ind_thm = Q.prove
(`!P:('a regexp list # 'a list # 'a regexp list option) list -> bool.
    P [] /\
    (!x. P [([],[],x)]) /\
    (!r t w s. P [(Repeat r::t,w,s)]) /\
    (!r1 r2 t w s. P [((r1 # r2)::t,w,s)]) /\
    (!r1 r2 t w s. P [((r1 + r2)::t,w,s)]) /\
    (!c d t w s. P [(Charset c::t,d::w,s)]) /\
    (!c t s. P [(Charset c::t,[],s)]) /\
    (!t w s. P [(Epsilon::t,w,s)]) /\
    (!h t s. P [([],h::t,s)]) /\
    (!t w s t' w' s' rst.
        P ((t',w',s')::rst) ==> P((Epsilon::t,w,s)::(t',w',s')::rst)) /\
    (!c t d w s t' w' s' rst.
        P ((t',w',s')::rst) ==> P((Charset c::t,d::w,s)::(t',w',s')::rst)) /\
    (!r1 r2 t w s t' w' s' rst.
        P ((t',w',s')::rst) ==> P(((r1 + r2)::t,w,s)::(t',w',s')::rst)) /\
    (!r1 r2 t w s t' w' s' rst.
        P ((t',w',s')::rst) ==> P(((r1 # r2)::t,w,s)::(t',w',s')::rst)) /\
    (!r t w s t' w' s' rst.
        P ((t',w',s')::rst) ==> P((Repeat r::t,w,s)::(t',w',s')::rst)) /\
    (!c t s h1 t1. P ((Charset c::t,[],s)::h1::t1)) /\
    (!c w s h1 t1. P (([],c::w,s)::h1::t1)) /\
    (!s h1 t1. P (([],[],s)::h1::t1))
   ==>
       !v. P v`,
 GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ms_ind THEN
 METIS_TAC [ABS_PAIR_THM, cases_lemma]);

val match_seq_down_closed = Q.prove
(`!L1 L2. match_seq (L1 ++ L2) ==> match_seq L2`,
 Induct THEN RW_TAC list_ss [match_seq_def]
   THEN Cases_on `L1++L2`
   THEN FULL_SIMP_TAC list_ss [match_seq_def]);


(*---------------------------------------------------------------------------*)
(* Concatenation of match sequences requires the "stopper" to be changed.    *)
(* change_stop_on_prefix sets the stop argument in the first element in a    *)
(* match sequence to the specified value.  This requires changing the stop   *)
(* argument in subsequent entries in the match sequence until a entry is     *)
(* reached that sets a new stop argument instead of just propogating the     *)
(* previous one.                                                             *)
(*---------------------------------------------------------------------------*)

val change_stop_on_prefix_def =
 Define
  `(change_stop_on_prefix ([] : ('a regexp list # 'a list #
                                 'a regexp list option) list) ns = []) /\
   (change_stop_on_prefix ((Repeat r::t,w,s)::b::c) ns =
     if b = (r::Repeat r::t, w, SOME (Repeat r::t))
      then(Repeat r::t,w,ns)::b::c
      else (Repeat r::t,w,ns)::change_stop_on_prefix (b::c) ns) /\
   (change_stop_on_prefix ((Charset c1::t,w,s)::c) ns
       = (Charset c1::t,w,ns)::c) /\
   (change_stop_on_prefix ((rl,w,s)::c) ns
       = (rl,w,ns)::change_stop_on_prefix c ns)`;

val csp_def = change_stop_on_prefix_def;
val csp_ind = fetch "-" "change_stop_on_prefix_ind";

val csp_step_lem = Q.prove
(`!alist stop rl w s x.
    (alist = ((rl,w,s)::x)) ==>
    ?t. change_stop_on_prefix alist stop = (rl,w,stop)::t`,
 recInduct csp_ind THEN RW_TAC list_ss [csp_def]);

val csp_step = SIMP_RULE list_ss [] csp_step_lem;

val change_stop_on_prefix_thm = Q.prove
(`!L stop. match_seq L ==> match_seq (change_stop_on_prefix L stop)`,
 recInduct ms_ind_thm THEN RW_TAC list_ss [match_seq_def,m_def,csp_def] THEN
 METIS_TAC [match_seq_def, m_def, csp_step]);

val LENGTH_CSP = Q.prove
(`!l s. LENGTH (change_stop_on_prefix l s) = LENGTH l`,
 recInduct csp_ind THEN RW_TAC list_ss [csp_def]);

(*---------------------------------------------------------------------------*)
(* If match sequences m1 and m2 represent matching rl1 against w1 and rl2    *)
(* against w2 respectively, then the composing m1 and m2 should represent    *)
(* matching rl1++rl2 against w1++w2.  Thus the first element of m2           *)
(* (rl2, w2, s2) should be appended to the end of all the elements in m1,    *)
(* and s2 should be changed to the last stop argument of m1.  Then the       *)
(* sequences can be joined.                                                  *)
(*---------------------------------------------------------------------------*)

val compose_m_seq_def =
 Define
  `(compose_m_seq [] x2 = x2) /\
   (compose_m_seq x1 [] = x1) /\
   (compose_m_seq x1 ((r1,w1,s1)::x2) =
     let x1 = MAP (\(r,w,s). (r++r1, w++w1, OPTION_MAP (\e. e++r1) s)) x1 in
     let x2 = change_stop_on_prefix ((r1,w1,s1)::x2) (SND (SND (LAST x1)))
     in
       x1 ++ TL x2)`;

val compose_m_seq_null = Q.prove
(`(!x. compose_m_seq [] x = x) /\ (!x. compose_m_seq x [] = x)`,
 CONJ_TAC THEN Cases THEN RW_TAC list_ss [compose_m_seq_def] THEN
 Q.ID_SPEC_TAC `h` THEN SIMP_TAC list_ss [FORALL_PROD,compose_m_seq_def]);

val lem = Q.prove
(`!mseq r w s r1 w1 s1 s2 x.
     (mseq = ((r1,w1,s1)::x)) ==>
      match_seq mseq ==>
      m (r,w,s) (r1,w1, s2) ==>
      match_seq ((r,w,s)::change_stop_on_prefix ((r1,w1,s1)::x) s2)`,
 recInduct ms_ind_thm
  THEN NTAC 2 (RW_TAC list_ss
         [csp_step, change_stop_on_prefix_def, match_seq_def, m_def])
  THEN METIS_TAC [CONS_ACYCLIC,list_CASES, CONS_11]);

val compose_m_seq_thm = Q.prove
(`!x1 x2. match_seq x1 ==> match_seq x2 ==> match_seq (compose_m_seq x1 x2)`,
 REPEAT STRIP_TAC
   THEN Induct_on `x1`
   THEN RW_TAC list_ss []
   THEN `(?rl w s. h = (rl,w,s)) /\
         ((x1 = []) \/ ?g t1. x1 = g::t1) /\
         ((x2 = []) \/ ?rl' w' s' t2 . x2 = (rl',w',s')::t2)`
      by METIS_TAC [list_CASES,ABS_PAIR_THM]
   THEN RW_TAC list_ss [compose_m_seq_null] THENL
   [(*Base Case*)
      `(rl' = []) \/ ?h t. rl' = h::t` by METIS_TAC [list_CASES]
      THEN `(t2 = []) \/ ?a z. t2 = a::z` by METIS_TAC [list_CASES]
      THEN FULL_SIMP_TAC list_ss [match_seq_def]
      THEN `(h = Epsilon) \/ (?c. h = Charset c) \/
            (?r1 r2. h = r1+r2) \/ (?r1 r2. h = r1#r2) \/
            (?r. h = Repeat r)` by METIS_TAC [regexp_cases]
      THEN RW_TAC list_ss [] THEN EVAL_TAC THEN FULL_SIMP_TAC list_ss [m_def]
      THEN RW_TAC list_ss [m_def, match_seq_def, SIMP_RULE std_ss [] lem]
      THEN METIS_TAC [list_CASES, m_def, CONS_ACYCLIC, CONS_11],
    (*Step Case*)
    `?rlist w1 s1. g = (rlist,w1,s1)` by METIS_TAC [ABS_PAIR_THM]
       THEN `((rl = []) \/ ?h t. rl = h::t) /\
             ((w = []) \/ ?b y. w = b::y)` by METIS_TAC [list_CASES]
       THEN `(h = Epsilon) \/ (?c. h = Charset c) \/
             (?r1 r2. h = r1+r2) \/ (?r1 r2. h = r1#r2) \/
             (?r. h = Repeat r)` by METIS_TAC [regexp_cases]
       THEN NTAC 2 (RW_TAC list_ss [] THEN
                    FULL_SIMP_TAC list_ss [LET_THM, m_def, match_seq_def,
                                           compose_m_seq_def])]);

(*---------------------------------------------------------------------------*)
(* Match sequence suffixes can be swapped out.                               *)
(*---------------------------------------------------------------------------*)

val match_seq_lemma = Q.prove
(`!a x y z. match_seq (x++[a]++z) /\ match_seq ([a]++y)
            ==> match_seq (x++[a]++y)`,
 Induct_on `x`
   THEN RW_TAC list_ss []
   THEN Cases_on `x`
   THEN METIS_TAC [APPEND, match_seq_def]);


(*---------------------------------------------------------------------------*)
(* If r matches w, then we can inductively build up a match sequence that    *)
(* starts with ([r], w, NONE).                                               *)
(*---------------------------------------------------------------------------*)

val lem = Q.prove
(`!(r: 'a regexp list) (w:'a list) s r' w' s' x x'.
  ?t. compose_m_seq ((r, w, s)::x) ((r', w', s')::x')
        =
      (r++r', w++w', OPTION_MAP (\e.e++r') s)::t`,
 RW_TAC list_ss [compose_m_seq_def, LET_THM]);

val sem_implies_match_seq_exists = Q.prove
(`!r w. sem r w ==> ?x. match_seq (([r], w, NONE)::x)`,
 Induct THENL
 [RW_TAC list_ss [sem_def]
    THEN Q.EXISTS_TAC `[([],[],NONE)]`
    THEN RW_TAC list_ss [match_seq_def, m_def],
  RW_TAC list_ss [sem_def]
    THEN Q.EXISTS_TAC `[([],[],NONE)]`
    THEN RW_TAC list_ss [match_seq_def, m_def],
  RW_TAC list_ss [sem_def] THEN RES_TAC THENL
    [Q.EXISTS_TAC `([r],w,NONE)::x` THEN RW_TAC list_ss [match_seq_def, m_def],
     Q.EXISTS_TAC `([r'],w,NONE)::x`
       THEN RW_TAC list_ss [match_seq_def, m_def]],
  RW_TAC list_ss [sem_def] THEN RES_TAC
    THEN Q.EXISTS_TAC `compose_m_seq (([r],w1,NONE)::x') (([r'],w2,NONE)::x)`
    THEN STRIP_ASSUME_TAC
           (Q.SPECL [`[r]`, `w1`, `NONE`, `[r']`, `w2`,`NONE`, `x'`, `x`] lem)
    THEN FULL_SIMP_TAC list_ss [match_seq_def]
    THEN METIS_TAC [m_def, compose_m_seq_thm],
  SIMP_TAC list_ss [repeat_equals_ncat_thm, GSYM LEFT_FORALL_IMP_THM]
    THEN Induct_on `n` THENL
    [RW_TAC list_ss [FUNPOW]
       THEN FULL_SIMP_TAC list_ss [sem_def]
       THEN Q.EXISTS_TAC `[([],[],NONE)]`
       THEN RW_TAC list_ss [match_seq_def, m_def],
     FULL_SIMP_TAC list_ss [FUNPOW_SUC]
       THEN RW_TAC list_ss [sem_def]
       THEN `?x1 x2. match_seq (([r],w1,NONE)::x1) /\
                     match_seq (([Repeat r],w2,NONE)::x2)` by METIS_TAC []
       THEN Q.EXISTS_TAC `change_stop_on_prefix
                              (compose_m_seq (([r],w1,NONE)::x1)
                              (([Repeat r],w2,NONE)::x2)) (SOME [Repeat r])`
       THEN STRIP_ASSUME_TAC
               (Q.SPECL [`[r]`, `w1`, `NONE`, `[Repeat r]`,
                         `w2`,`NONE`, `x1`, `x2`] lem)
       THEN STRIP_ASSUME_TAC
               (Q.SPECL [`SOME[Repeat r]`, `[r]++[Repeat r]`,
                         `w1++w2`, `NONE`, `t`] csp_step)
       THEN FULL_SIMP_TAC list_ss [match_seq_def]
       THEN METIS_TAC [m_def, compose_m_seq_thm, change_stop_on_prefix_thm]]]);


(*---------------------------------------------------------------------------*)
(* Given a match sequence starting with (rl,w,s), then (match rl w s) holds  *)
(* as long as the match sequence avoids cycles in the matcher.               *)
(*---------------------------------------------------------------------------*)

val witness_implies_match_thm =
let val thms = [match_def, match_seq_def, m_def] in
Q.prove
(`!rl w s x y.
    (((rl,w,s)::y) = x)
    ==> match_seq x /\
        (!r1 t1 w1. ~MEM (Repeat r1::t1, w1, SOME (Repeat r1::t1)) x)
    ==> match rl w s`,
 Induct_on `x` THEN RW_TAC list_ss [] THEN
 `((x=[])  \/ ?h t. x = h::t) /\
  ((rl=[]) \/ (?rst. rl = Epsilon::rst)
           \/ (?c rst. rl = Charset c::rst)
           \/ (?r1 r2 rst. rl = (r1+r2)::rst)
           \/ (?r1 r2 rst. rl = (r1#r2)::rst)
           \/ (?r2 rst. rl = Repeat r2::rst))`
      by METIS_TAC [list_CASES,regexp_cases]
   THEN RW_TAC list_ss []
   THEN FULL_SIMP_TAC list_ss thms THENL
   [Cases_on `w` THEN FULL_SIMP_TAC list_ss thms,
    RW_TAC list_ss [] THEN METIS_TAC thms,
    RW_TAC list_ss [] THEN METIS_TAC thms])
end;

(*---------------------------------------------------------------------------*)
(* Split a list in two around the first point where predicate P holds.       *)
(*---------------------------------------------------------------------------*)

val split_def =
 Define
  `(split P [] acc = NONE) /\
   (split P (h::t) acc = if P h then SOME (acc, h, t)
                                else split P t (acc++[h]))`;

val split_thm = Q.prove
(`!P l acc l1 v l2.
     (split P l acc = (SOME (l1, v, l2))) ==> (l1 ++ [v] ++ l2 = acc ++ l)`,
 Induct_on `l`
   THEN RW_TAC list_ss [split_def]
   THEN METIS_TAC [APPEND, APPEND_ASSOC]);

val split_thm2 = Q.prove
(`!P l acc l1 v l2.
     (split P l acc = (SOME (l1, v, l2))) ==> ?l3. (l1 = acc++l3)`,
 Induct_on `l`
   THEN RW_TAC list_ss [split_def] THENL
   [Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [],
    RES_TAC THEN Q.EXISTS_TAC `[h]++l3` THEN RW_TAC list_ss []]);

val split_thm3 = Q.prove
(`!P l acc l1 v l2 l3.
    (split P l (l3 ++ acc) = SOME (l3++l1, v, l2))
       =
    (split P l acc = (SOME (l1, v, l2)))`,
 Induct_on `l`
    THEN RW_TAC list_ss [split_def]
    THEN METIS_TAC [APPEND_ASSOC]);

val split_thm4 = Q.prove
(`!P l acc. (split P l acc = NONE) ==> ~EXISTS P l`,
 Induct_on `l`
   THEN RW_TAC list_ss [split_def]
   THEN FULL_SIMP_TAC list_ss []
   THEN METIS_TAC []);

val split_thm5 = Q.prove
(`!P l acc acc2. (split P l acc = NONE) ==> (split P l acc2 = NONE)`,
 Induct_on `l`
   THEN RW_TAC list_ss [split_def]
   THEN METIS_TAC [split_def]);

val split_prop_thm = Q.prove
(`!L P a b c acc. (split P L acc = SOME(a,b,c)) ==> P b`,
 Induct
   THEN RW_TAC list_ss [split_def]
   THEN METIS_TAC []);

val split_cong_thm = Q.prove
(`!l P acc P' l' acc'.
     (l=l') /\ (!x. MEM x l ==> (P x = P' x)) /\ (acc=acc')
       ==> (split P l acc = split P' l' acc')`,
 Induct_on `l`
   THEN RW_TAC list_ss [split_def]
   THEN FULL_SIMP_TAC list_ss [split_def]);

(*---------------------------------------------------------------------------*)
(* If a cycle exists in a match sequence, then the part of the sequence      *)
(* before the cycle contains the Repeat expressions that lead to the cycle.  *)
(*---------------------------------------------------------------------------*)

val match_seq_find_lemma = Q.prove
(`!ms l1 r l w z.
  match_seq ms
   ==> (split (\x. ?r l w. x = (Repeat r::l, w, SOME (Repeat r::l))) ms [] =
        SOME (l1,(Repeat r::l,w,SOME(Repeat r::l)), z))
   ==> (~((SND(SND(HD ms))) = SOME (Repeat r::l)) \/ ~((FST(SND(HD ms))) = w))
   ==> ?s. MEM (Repeat r::l, w, s) l1`,
 Induct
    THEN FULL_SIMP_TAC list_ss [split_def, match_seq_def, m_def]
    THEN REPEAT GEN_TAC
    THEN `(l1 = []) \/ ?h1 t1. l1 = h1::t1` by METIS_TAC [list_CASES]
    THEN RW_TAC list_ss [split_def, match_seq_def, m_def]
    THEN TRY (IMP_RES_TAC split_thm2 THEN FULL_SIMP_TAC list_ss [] THEN NO_TAC)
    (* 2 cases left, almost identical; do both cases with same tactic *)
    THEN
    (Q.PAT_X_ASSUM `$! M `(MP_TAC o Q.SPECL [`t1`, `r`, `l`, `w`, `z`])
    THEN RW_TAC list_ss [split_def, match_seq_def, m_def]
    THEN `match_seq ms` by METIS_TAC [match_seq_down_closed, APPEND]
    THEN FULL_SIMP_TAC list_ss [split_def, match_seq_def, m_def]
    THEN IMP_RES_TAC split_thm2
    THEN FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []
    THEN ASSUME_TAC (Q.SPECL
             [`\x. ?r l w. x = (Repeat r::l,w,SOME (Repeat r::l))`,
              `ms`, `[]`, `l3`, `(Repeat r::l,w,SOME (Repeat r::l))`, `z`,
              `[h]`]
     (INST_TYPE [alpha |-> Type`:'a regexp list#'a list#'a regexp list option`]
                   split_thm3))
   THEN FULL_SIMP_TAC list_ss []
   THEN RES_TAC THEN FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []
   THEN Cases_on `~(SND (SND (HD ms)) = SOME (Repeat r::l))`
   THENL [METIS_TAC [],FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []]
   THEN Cases_on `~(FST (SND (HD ms)) = w)`
   THENL [METIS_TAC [],FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []]
   THEN `(ms = []) \/ ?a b c mst. ms = (a,b,c)::mst`
        by METIS_TAC [list_CASES,ABS_PAIR_THM]
   THENL [FULL_SIMP_TAC list_ss [split_def, match_seq_def, m_def],
          FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []
            THEN `?a1 b1 c1. h = (a1,b1,c1)` by METIS_TAC [ABS_PAIR_THM]
            THEN RW_TAC list_ss [] THEN FULL_SIMP_TAC list_ss [match_seq_def]
            THEN METIS_TAC [m_thm,m_thm2,NOT_SOME_NONE]]));


(*---------------------------------------------------------------------------*)
(* Normalize a match sequence to cut the cycles out of it.                   *)
(* To remove a cycle, find it and the regexp that started the cycle and cut  *)
(* out the intermediate parts of the match sequence.                         *)
(*---------------------------------------------------------------------------*)

val NS_DEF =
 tDefine
  "NS"
  `NS ms =
     case split (\x. ?r l w. x = (Repeat r::l, w, SOME (Repeat r::l))) ms [] of
         NONE => ms
      |  SOME (l1, (bad_r, bad_w, bad_s), z) =>
           let opt = split (\x. ?s. x = (bad_r, bad_w, s)) l1 []
           in if opt = NONE then []
              else
                let (x1, (rl, w1, s1), y) = THE opt in
                if (?ra L. (rl = Repeat ra::L) /\ (FST(HD z) = L))
                  then NS (x1 ++ [(rl,w1,s1)] ++ change_stop_on_prefix z s1)
                  else NS (x1 ++ [(rl,w1,s1)] ++ z)`
(WF_REL_TAC `measure LENGTH`
  THEN RW_TAC list_ss [LENGTH_CSP]
  THEN IMP_RES_TAC split_thm THEN FULL_SIMP_TAC list_ss []
  THEN RW_TAC list_ss []
  THEN Cases_on `(split (λx. ∃s. x = (p_1',p_1'',s)) p_1 [])`
  THEN RW_TAC list_ss []
  THEN FULL_SIMP_TAC list_ss []
  THEN Cases_on `x` THEN Cases_on `r`
  THEN IMP_RES_TAC split_thm THEN FULL_SIMP_TAC list_ss []
  THEN RW_TAC list_ss []);

val NS_IND = fetch "-" "NS_ind";

(*---------------------------------------------------------------------------*)
(* One step of NS preserves match sequences                                  *)
(*---------------------------------------------------------------------------*)

val match_seq_surg_thm = Q.prove
(`!ms l1 bad_r bad_w z x1 rl w1 s1 y.
        match_seq ms ==>
        (split (\x. ?r l w. x = (Repeat r::l, w, SOME (Repeat r::l))) ms [] =
         SOME (l1, (bad_r, bad_w, bad_s), z)) ==>
        (split (\x. ?s. x = (bad_r, bad_w, s)) l1 [] =
         SOME (x1, (rl, w1, s1), y)) ==>
        if (?ra L. (rl = Repeat ra::L) /\ (FST(HD z) = L)) then
          match_seq (x1 ++ [(rl, w1, s1)] ++ change_stop_on_prefix z s1)
        else
          match_seq (x1 ++ [(rl, w1, s1)] ++ z)`,
 Induct THENL
 [RW_TAC list_ss []
    THEN IMP_RES_TAC split_thm
    THEN FULL_SIMP_TAC list_ss [],
  REPEAT STRIP_TAC
    THEN `(bad_r = rl) /\ (bad_w = w1)`
         by (IMP_RES_TAC split_prop_thm THEN POP_ASSUM (K ALL_TAC)
             THEN FULL_SIMP_TAC list_ss [LAMBDA_PROD])
    THEN IMP_RES_TAC split_thm THEN FULL_SIMP_TAC list_ss []
    THEN `match_seq (x1 ++ [(rl,w1,s1)] ++ y ++ [(rl,w1,bad_s)] ++ z)`
         by METIS_TAC []
    THEN `(z=[]) \/ ?a b c t1. z = (a,b,c)::t1`
         by METIS_TAC [list_CASES,ABS_PAIR_THM] THENL
    [FULL_SIMP_TAC list_ss [match_seq_def]
       THEN `match_seq [(bad_r,bad_w,bad_s)]`
            by METIS_TAC [match_seq_down_closed]
       THEN FULL_SIMP_TAC list_ss [match_seq_def]
       THEN RW_TAC list_ss [change_stop_on_prefix_def, match_seq_def]
       THEN `match_seq ([([],[],s1)] ++ y ++ [([],[],bad_s)])`
             by METIS_TAC [match_seq_down_closed,APPEND_ASSOC]
       THEN Cases_on `y`  THEN FULL_SIMP_TAC list_ss [match_seq_def,m_def],
     RW_TAC list_ss [] THENL
     [`match_seq (change_stop_on_prefix ((a,b,c)::t1) s1)`
          by METIS_TAC [match_seq_down_closed,change_stop_on_prefix_thm]
        THEN ASSUME_TAC (Q.SPECL
              [`(Repeat ra::a,bad_w,s1)`, `x1`,
               `change_stop_on_prefix ((a,b,c)::t1) s1`,
               `y ++ [(Repeat ra::a,bad_w,bad_s)] ++ ((a,b,c)::t1)`]
              match_seq_lemma)
        THEN FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC list_ss []
        THEN `?t2. change_stop_on_prefix ((a,b,c)::t1) s1 = (a,b,s1)::t2`
             by METIS_TAC[csp_step]
        THEN POP_ASSUM SUBST_ALL_TAC
        THEN RW_TAC list_ss [match_seq_def]
        THEN `m (Repeat ra::a,bad_w,bad_s) (a,b,c)`
             by METIS_TAC [match_seq_down_closed,APPEND,APPEND_ASSOC,
                           match_seq_def]
        THEN FULL_SIMP_TAC list_ss [m_def],
      match_mp_tac match_seq_lemma
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ first_assum(part_match_exists_tac (fst o dest_conj) o concl)
        \\ simp[match_seq_def]
        \\ reverse conj_tac >- metis_tac[match_seq_down_closed]
        THEN `m (bad_r,bad_w,bad_s) (a,b,c)`
             by METIS_TAC [match_seq_down_closed,APPEND,APPEND_ASSOC,
                           match_seq_def]
        THEN `?r l. bad_r = Repeat r::l` by (IMP_RES_TAC split_prop_thm \\ fs[])
        THEN POP_ASSUM MP_TAC THEN EVAL_TAC THEN RW_TAC list_ss []
        \\ fs[m_def]]]]);

val NS_match_thm = Q.prove
(`!ms. match_seq ms ==> match_seq (NS ms)`,
 recInduct NS_IND THEN RW_TAC list_ss []
   THEN ONCE_REWRITE_TAC [NS_DEF] THEN CASE_TAC THENL
   [METIS_TAC [],
    REPEAT CASE_TAC
     THEN RW_TAC list_ss [match_seq_def, LET_THM]
     THEN REPEAT (POP_ASSUM MP_TAC)
     THEN RENAME_FREES_TAC [("q","l1"), ("r'","l2"),
                            ("q''","a"),("q'","b"),("r''","c")]
     THEN REPEAT STRIP_TAC
     THEN `(split (\x. ?s. x = (a,b,s)) l1 [] = NONE) \/
           ?a1 b1a b1b b1c c1.
              split (\x. ?s. x = (a,b,s)) l1 [] = SOME (a1,(b1a,b1b,b1c),c1)`
          by METIS_TAC [optionTheory.option_nchotomy,ABS_PAIR_THM]
     THEN RW_TAC list_ss [match_seq_def]
     THEN IMP_RES_TAC match_seq_surg_thm
     THEN FULL_SIMP_TAC list_ss []
     THEN RW_TAC list_ss [] THEN METIS_TAC []]);

val NS_is_normal_thm = Q.prove
(`!ms r w t. ~MEM (Repeat r::t, w, SOME (Repeat r::t)) (NS ms)`,
 recInduct NS_IND THEN RW_TAC list_ss []
   THEN ONCE_REWRITE_TAC [NS_DEF]
   THEN CASE_TAC THENL
   [IMP_RES_TAC split_thm4
      THEN FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []
      THEN Induct_on `ms`
      THEN RW_TAC list_ss []
      THEN FULL_SIMP_TAC list_ss [split_def]
      THEN METIS_TAC [split_thm5],
    REPEAT CASE_TAC THEN RW_TAC list_ss [LET_THM]
      THEN REPEAT (POP_ASSUM MP_TAC)
      THEN RENAME_FREES_TAC [("q","l1"), ("r''","l2"),
                             ("q''","a"),("q'","b"),("r'''","c")]
      THEN NTAC 4 STRIP_TAC
      THEN `(split (\x. ?s. x = (a,b,s)) l1 [] = NONE) \/
            ?a1 b1a b1b b1c c1.
               split (\x. ?s. x = (a,b,s)) l1 [] = SOME (a1,(b1a,b1b,b1c),c1)`
           by METIS_TAC [optionTheory.option_nchotomy,ABS_PAIR_THM]
      THEN FULL_SIMP_TAC list_ss []
      THEN RW_TAC list_ss []
      THEN FULL_SIMP_TAC list_ss []
      THEN METIS_TAC []]);

val lem = Q.prove
(`EXISTS (\y. y = (a,b,c)) L ==> EXISTS (\y. ?c. y = (a,b,c)) L`,
Induct_on `L` THEN EVAL_TAC THEN RW_TAC list_ss [] THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* Normalizing a match sequence doesn't change the first element             *)
(*---------------------------------------------------------------------------*)

val  NS_HD_THM = Q.prove
(`!t t' r w. (t = (r,w,NONE)::t') ==>
              match_seq t ==>
             ?t''. (NS t = (r, w, NONE)::t'')`,
 recInduct NS_IND THEN RW_TAC list_ss []
   THEN ONCE_REWRITE_TAC [NS_DEF]
   THEN REPEAT CASE_TAC
   THEN REPEAT (POP_ASSUM MP_TAC)
   THEN RENAME_FREES_TAC [("q","l1"), ("r''","l2"),
                          ("q''","a"),("q'","b"),("r'''","c")]
   THEN NTAC 4 STRIP_TAC
   THEN RW_TAC list_ss [LET_THM] THENL
   [IMP_RES_TAC split_prop_thm THEN FULL_SIMP_TAC list_ss []
     THEN IMP_RES_TAC match_seq_find_lemma THEN FULL_SIMP_TAC list_ss []
     THEN IMP_RES_TAC split_thm4
     THEN `(a=[]) \/ ?d u. a = d::u` by METIS_TAC [list_CASES]
     THEN RW_TAC list_ss [] THEN METIS_TAC [MEM_EXISTS_LEM,lem],
    `?a1 b1a b1b b1c c1.
         split (\x. ?s. x = (a,b,s)) l1 [] = SOME (a1,(b1a,b1b,b1c),c1)`
         by METIS_TAC [optionTheory.option_nchotomy,ABS_PAIR_THM]
     THEN Cases_on `l1` THEN FULL_SIMP_TAC list_ss []
     THENL [FULL_SIMP_TAC list_ss [split_def], ALL_TAC]
     THEN `h = (r,w,NONE)` by (IMP_RES_TAC split_thm THEN FULL_SIMP_TAC list_ss [])
     THEN IMP_RES_TAC match_seq_surg_thm
     THEN Cases_on `a1` THEN RW_TAC list_ss [match_seq_def]
     THEN IMP_RES_TAC split_thm THEN FULL_SIMP_TAC list_ss []]);

(*---------------------------------------------------------------------------*)
(* The semantics imply match.                                                *)
(*---------------------------------------------------------------------------*)

val sem_implies_match = Q.prove
(`!r w. sem r w ==> match [r] w NONE`,
 METIS_TAC [sem_implies_match_seq_exists, NS_match_thm,
            NS_is_normal_thm, NS_HD_THM, witness_implies_match_thm]);

(*---------------------------------------------------------------------------*)
(* match correctly implements the semantics.                                 *)
(*---------------------------------------------------------------------------*)

Theorem match_is_correct:
 !r w. sem r w = match [r] w NONE
Proof
 REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [RW_TAC list_ss [sem_implies_match],
    IMP_RES_TAC match_implies_sem THEN FULL_SIMP_TAC list_ss [FOLDR,sem_def]]
QED

val _ = export_theory ();

val _ = Count.report (Count.read thm_counter);
