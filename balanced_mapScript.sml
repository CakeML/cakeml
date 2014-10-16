open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open lcsymtacs;

val _ = new_theory "balanced_map";

(* Balanced binary trees. There is the following rough correspondence between
 * this library and the finite_map Theory.

 DRESTRICT
 FAPPLY
 FCARD          size
 FDOM
 FEMPTY         empty
 FEVERY         TODO
 FLOOKUP        lookup
 FMAP_MAP2
 FMERGE
 FRANGE
 FUNION         union
 FUN_FMAP
 FUPDATE        insert
 FUPDATE_LIST
 MAP_KEYS
 RRESTRICT
 SUBMAP         isSubmapOfBy
 f_o            map
 f_o_f
 fmap_EQ_UPTO
 fmap_ISO
 fmap_TY
 fmap_domsub
 fmap_inverse
 fmap_rel
 fmap_size
 is_fmap
 o_f

 *)

(* ------------------------ Preliminaries ------------------------ *)

val _ = temp_tight_equality ();

val _ = bossLib.augment_srw_ss [rewrites 
  [FUNION_FUPDATE_1,FUNION_ASSOC,FUNION_FEMPTY_2,FUNION_FEMPTY_1,FDOM_DRESTRICT,
   DRESTRICT_UNIV]]

fun fs x = full_simp_tac (srw_ss()++ARITH_ss) x;
fun rfs x = REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss) x;
val rw = srw_tac [ARITH_ss];

val fmrw = srw_tac [ARITH_ss, rewrites [FLOOKUP_UPDATE,FLOOKUP_FUNION,FLOOKUP_DRESTRICT,
                    FUNION_FUPDATE_2,FAPPLY_FUPDATE_THM,FUNION_DEF, DRESTRICT_DEF]];

fun inv_to_front_tac tm (g as (asl,w)) = let
  val tms = strip_conj w
  val (tms1,tms2) = List.partition (fn x => can (find_term (can (match_term tm))) x) tms
  val tms = tms1@tms2
  val thm = prove (``^w ⇔ ^(list_mk_conj tms)``, SIMP_TAC (std_ss) [AC CONJ_COMM CONJ_ASSOC])
in
  ONCE_REWRITE_TAC [thm] g
end

val inv_mp_tac = let 
  val lemma = PROVE [] ``!A B C D. (A ⇒ B ∧ C) ⇒ (A ∧ (B ∧ C ⇒  D)) ⇒ (B ∧ D)``
in
  fn th => fn (g as (asl,w)) => let
    val c = th |> concl
    val (xs,b) = strip_forall c
    val tm = b |> dest_imp |> snd |> strip_conj |> hd
    val tm2 = hd (strip_conj w)
    val s = fst (match_term tm tm2)
    val th2 = SPECL (map (Term.subst s) xs) th
    val th3 = MATCH_MP lemma th2
  in 
    MATCH_MP_TAC (GEN_ALL th3) g
  end 
end

val fdom_eq = PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``;

val TIMES_MIN = Q.prove (
`!x y z. x * MIN y z = MIN (x * y) (x * z)`,
 rw [MIN_DEF] >>
 fs []);

val FCARD_DISJOINT_UNION = Q.prove (
`!m1 m2.
  DISJOINT (FDOM m1) (FDOM m2) ∨ DISJOINT (FDOM m2) (FDOM m1)
  ⇒
  FCARD (FUNION m1 m2) = FCARD m1 + FCARD m2`,
 rw [DISJOINT_DEF, FCARD_DEF] >>
 metis_tac [CARD_UNION, FDOM_FINITE, CARD_DEF, ADD_0, INTER_COMM]);

val CARD_DISJOINT_UNION = Q.prove (
`!s1 s2.
  FINITE s1 ∧ FINITE s2
  ⇒
  DISJOINT s1 s2 ∨ DISJOINT s2 s1
  ⇒
  CARD (s1 ∪ s2) = CARD s1 + CARD s2`,
 rw [DISJOINT_DEF] >>
 metis_tac [CARD_UNION, CARD_DEF, ADD_0, INTER_COMM]);

val FCARD_DRESTRICT = Q.prove (
`∀m s. FCARD (DRESTRICT m s) = CARD (FDOM m ∩ s)`,
 rw [FCARD_DEF, FDOM_DRESTRICT]);

val DELETE_INTER2 = Q.prove (
`∀s t x. t ∩ (s DELETE x) = s ∩ t DELETE x`,
 metis_tac [DELETE_INTER, INTER_COMM]);

val every_case_tac = BasicProvers.EVERY_CASE_TAC;

(* ------------------------ Comparison ------------------------ *)

val _ = Datatype `comparison = Less | Greater | Equal`;

val comparison_distinct = fetch "-" "comparison_distinct";
val comparison_case_def = fetch "-" "comparison_case_def";
val comparison_nchotomy = fetch "-" "comparison_nchotomy";

val good_cmp_def = Define `
good_cmp cmp ⇔
  (!x. cmp x x = Equal) ∧
  (!x y. cmp x y = Equal ⇒ cmp y x = Equal) ∧
  (!x y. cmp x y = Greater ⇔ cmp y x = Less) ∧
  (!x y z. cmp x y = Equal ∧ cmp y z = Less ⇒ cmp x z = Less) ∧
  (!x y z. cmp x y = Less ∧ cmp y z = Equal ⇒ cmp x z = Less) ∧
  (!x y z. cmp x y = Equal ∧ cmp y z = Equal ⇒ cmp x z = Equal) ∧
  (!x y z. cmp x y = Less ∧ cmp y z = Less ⇒ cmp x z = Less)`;

val cmp_thms = LIST_CONJ [comparison_distinct, comparison_case_def, comparison_nchotomy, good_cmp_def]

val option_cmp_def = Define `
(option_cmp cmp NONE NONE = Equal) ∧
(option_cmp cmp NONE (SOME x) = Less) ∧
(option_cmp cmp (SOME x) NONE = Greater) ∧
(option_cmp cmp (SOME x) (SOME y) = cmp x y)`;

val option_cmp2_def = Define `
(option_cmp2 cmp NONE NONE = Equal) ∧
(option_cmp2 cmp NONE (SOME x) = Greater) ∧
(option_cmp2 cmp (SOME x) NONE = Less) ∧
(option_cmp2 cmp (SOME x) (SOME y) = cmp x y)`;

val list_cmp_def = Define `
(list_cmp cmp [] [] = Equal) ∧
(list_cmp cmp [] (x::y) = Less) ∧
(list_cmp cmp (x::y) [] = Greater) ∧
(list_cmp cmp (x1::y1) (x2::y2) =
  case cmp x1 x2 of
     | Equal => list_cmp cmp y1 y2
     | Less => Less
     | Greater => Greater)`;

val list_cmp_ind = fetch "-" "list_cmp_ind";

val option_cmp_good = Q.store_thm ("option_cmp_good",
`!cmp. good_cmp cmp ⇒ good_cmp (option_cmp cmp)`,
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp_def, comparison_distinct]);

val option_cmp2_good = Q.store_thm ("option_cmp2_good",
`!cmp. good_cmp cmp ⇒ good_cmp (option_cmp2 cmp)`,
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp2_def, comparison_distinct]);

val list_cmp_good = Q.store_thm ("list_cmp_good",
`!cmp. good_cmp cmp ⇒ good_cmp (list_cmp cmp)`,
 simp [good_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 rpt conj_tac >>
 Induct_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [list_cmp_def] >>
 rpt strip_tac >>
 every_case_tac >>
 metis_tac [list_cmp_def, comparison_distinct, comparison_case_def, comparison_nchotomy]);

val good_cmp_trans = Q.store_thm ("good_cmp_trans",
`!cmp. good_cmp cmp ⇒ transitive (λ(k,v) (k',v'). cmp k k' = Less)`,
 rw [relationTheory.transitive_def] >>
 Cases_on `x` >>
 Cases_on `y` >>
 Cases_on `z` >>
 fs [] >>
 metis_tac [cmp_thms]);


(* ------------------------ Finite maps up to key equivalence ------------------------ *)

val key_set_def = Define `
key_set cmp k = { k' | cmp k k' = Equal }`;

val key_set_equiv = Q.store_thm ("key_set_equiv",
`!cmp.
  good_cmp cmp 
  ⇒
  (!k. k ∈ key_set cmp k) ∧
  (!k1 k2. k1 ∈ key_set cmp k2 ⇒ k2 ∈ key_set cmp k1) ∧
  (!k1 k2 k3. k1 ∈ key_set cmp k2 ∧ k2 ∈ key_set cmp k3 ⇒ k1 ∈ key_set cmp k3)`,
 rw [key_set_def] >>
 metis_tac [good_cmp_def]);

val key_set_partition = Q.store_thm ("key_set_partition",
`!cmp k1 k2.
  good_cmp cmp ∧
  key_set cmp k1 ≠ key_set cmp k2 
  ⇒ 
  DISJOINT (key_set cmp k1) (key_set cmp k2)`,
 rw [DISJOINT_DEF, EXTENSION] >>
 metis_tac [key_set_equiv]);

val key_set_eq = Q.store_thm ("key_set_eq",
`!cmp k1 k2.
  good_cmp cmp
  ⇒
  (key_set cmp k1 = key_set cmp k2 ⇔ cmp k1 k2 = Equal)`,
 rw [key_set_def, EXTENSION] >>
 metis_tac [cmp_thms, key_set_equiv]);

val key_set_cmp_def = Define `
key_set_cmp cmp k ks res ⇔
  !k'. k' ∈ ks ⇒ cmp k k' = res`;

val key_set_cmp_thm = Q.store_thm ("key_set_cmp_thm",
`!cmp k k' res. 
  good_cmp cmp
  ⇒
  (key_set_cmp cmp k (key_set cmp k') res ⇔ cmp k k' = res)`,
 rw [key_set_cmp_def, key_set_def] >>
 metis_tac [cmp_thms]);

val key_set_cmp2_def = Define `
key_set_cmp2 cmp ks1 ks2 res ⇔
  !k1 k2. k1 ∈ ks1 ∧ k2 ∈ ks2 ⇒ cmp k1 k2 = res`;

val key_set_cmp2_thm = Q.store_thm ("key_set_cmp2_thm",
`!cmp k k' res. 
  good_cmp cmp
  ⇒
  (key_set_cmp2 cmp (key_set cmp k) (key_set cmp k') res ⇔ cmp k k' = res)`,
 rw [key_set_cmp2_def, key_set_def] >>
 metis_tac [cmp_thms]);

(* Maps based on balanced binary trees. Copied from ghc-7.8.3
 * libraries/containers/Data/Map/Base.hs. It starts with the following comment:
 
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Map.Base
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of maps from keys to values (dictionaries).
--
-- Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.Map (Map)
-- >  import qualified Data.Map as Map
--
-- The implementation of 'Map' is based on /size balanced/ binary trees (or
-- trees of /bounded balance/) as described by:
--
--    * Stephen Adams, \"/Efficient sets: a balancing act/\",
--     Journal of Functional Programming 3(4):553-562, October 1993,
--     <http://www.swiss.ai.mit.edu/~adams/BB/>.
--
--    * J. Nievergelt and E.M. Reingold,
--      \"/Binary search trees of bounded balance/\",
--      SIAM journal of computing 2(1), March 1973.
--
-- Note that the implementation is /left-biased/ -- the elements of a
-- first argument are always preferred to the second, for example in
-- 'union' or 'insert'.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation <http://en.wikipedia.org/wiki/Big_O_notation>.
-----------------------------------------------------------------------------

*) 

val _ = Datatype `
balanced_map = Tip | Bin num 'k 'v balanced_map balanced_map`;

val ratio_def = Define `
ratio = 2`;

val delta_def = Define `
delta = 3:num`;

val size_def = Define `
(size Tip = 0) ∧
(size (Bin s k v l r) = s)`;

val bin_def = Define `
bin k x l r = Bin (size l + size r + 1) k x l r`;

val null_def = Define `
(null Tip = T) ∧
(null (Bin s k v m1 m2) = F)`;

val lookup_def = Define `
(lookup cmp k Tip = NONE) ∧
(lookup cmp k (Bin s k' v l r) =
  case cmp k k' of
     | Less => lookup cmp k l
     | Greater => lookup cmp k r
     | Equal => SOME v)`;

val member_def = Define `
(member cmp k Tip = F) ∧
(member cmp k (Bin s k' v l r) =
  case cmp k k' of
     | Less => member cmp k l
     | Greater => member cmp k r
     | Equal => T)`;

val empty_def = Define `
empty = Tip`;

val singleton_def = Define `
singleton k x = Bin 1 k x Tip Tip`;

(* Just like the Haskell, but w/o @ patterns *)
val balanceL'_def = Define `
balanceL' k x l r = 
  case r of
     | Tip => 
         (case l of
            | Tip => Bin 1 k x Tip Tip
            | (Bin _ _ _ Tip Tip) => Bin 2 k x l Tip
            | (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) => Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
            | (Bin _ lk lx (Bin s' k' v' l' r') Tip) => Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)
            | (Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr)) =>
                if lrs < ratio*lls then Bin (1+ls) lk lx (Bin lls k' v' l' r') (Bin (1+lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
                else  Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx (Bin lls k' v' l' r') lrl) (Bin (1+size lrr) k x lrr Tip))
     | (Bin rs _ _ _ _) => 
         case l of
            | Tip => Bin (1+rs) k x Tip r
            | (Bin ls lk lx ll lr) =>
                if ls > delta*rs  then
                  case (ll, lr) of
                     | (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
                         if lrs < ratio*lls then Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                         else Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                     | (_, _) => Tip (* error "Failure in Data.Map.balanceL" *)
                         else Bin (1+ls+rs) k x l r`;

val balanceR'_def = Define `
balanceR' k x l r = 
  case l of
    | Tip =>
        (case r of
           | Tip => Bin 1 k x Tip Tip
           | (Bin _ _ _ Tip Tip) => Bin 2 k x Tip r
           | (Bin _ rk rx Tip (Bin s' k' v' l' r')) => Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')
           | (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) => Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           | (Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r')) =>
               if rls < ratio*rrs then Bin (1+rs) rk rx (Bin (1+rls) k x Tip (Bin rls rlk rlx rll rlr)) (Bin rrs k' v' l' r')
               else Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr (Bin rrs k' v' l' r')))
   | (Bin ls _ _ _ _) => 
       case r of
          | Tip => Bin (1+ls) k x l Tip
          | (Bin rs rk rx rl rr) =>
              if rs > delta*ls then
                case (rl, rr) of
                   | (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
                     if  rls < ratio*rrs then Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     else Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   | (_, _) => Tip (* error "Failure in Data.Map.balanceR" *)
              else Bin (1+ls+rs) k x l r`;

val balanceL_def = Define `
(balanceL k x Tip Tip = 
  Bin 1 k x Tip Tip) ∧
(balanceL k x (Bin s' k' v' Tip Tip) Tip = 
  Bin 2 k x (Bin s' k' v' Tip Tip) Tip) ∧
(balanceL k x (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) Tip =
  Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)) ∧
(balanceL k x  (Bin _ lk lx (Bin s' k' v' l' r') Tip) Tip =
  Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)) ∧
(balanceL k x (Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr)) Tip =
  if lrs < ratio*lls then 
    Bin (1+ls) lk lx (Bin lls k' v' l' r') 
                     (Bin (1+lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
  else  
    Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx (Bin lls k' v' l' r') lrl) 
                       (Bin (1+size lrr) k x lrr Tip)) ∧
(balanceL k x Tip (Bin rs k' v' l' r') = 
  Bin (1+rs) k x Tip (Bin rs k' v' l' r')) ∧
(balanceL k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r') =
  if ls > delta*rs  then
    case (ll, lr) of
       | (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
           if lrs < ratio*lls then 
             Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr (Bin rs k' v' l' r'))
           else 
             Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) 
                                   (Bin (1+rs+size lrr) k x lrr (Bin rs k' v' l' r'))
       | (_, _) => Tip (* error "Failure in Data.Map.balanceL" *)
  else 
    Bin (1+ls+rs) k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r'))`;

val balanceR_def = Define `
(balanceR k x Tip Tip = 
  Bin 1 k x Tip Tip) ∧
(balanceR k x Tip (Bin s' k' v' Tip Tip) =
  Bin 2 k x Tip (Bin s' k' v' Tip Tip)) ∧
(balanceR k x Tip (Bin _ rk rx Tip (Bin s' k' v' l' r')) =
  Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')) ∧
(balanceR k x Tip (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) =
  Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)) ∧
(balanceR k x Tip (Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r')) =
  if rls < ratio*rrs then 
    Bin (1+rs) rk rx (Bin (1+rls) k x Tip (Bin rls rlk rlx rll rlr)) (Bin rrs k' v' l' r')
  else 
    Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) 
                       (Bin (1+rrs+size rlr) rk rx rlr (Bin rrs k' v' l' r'))) ∧
(balanceR k x (Bin ls k' v' l' r') Tip =
  Bin (1+ls) k x (Bin ls k' v' l' r') Tip) ∧
(balanceR k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr) =
  if rs > delta*ls then
    case (rl, rr) of
       | (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
           if rls < ratio*rrs then 
             Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x (Bin ls k' v' l' r') rl) rr
           else 
             Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x (Bin ls k' v' l' r') rll) 
                                   (Bin (1+rrs+size rlr) rk rx rlr rr)
       | (_, _) => Tip (* error "Failure in Data.Map.balanceR" *)
  else
    Bin (1+ls+rs) k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr))`;

val insert_def = Define `
(insert cmp k v Tip = singleton k v) ∧
(insert cmp k v (Bin s k' v' l r) =
  case cmp k k' of
     | Less => balanceL k' v' (insert cmp k v l) r
     | Greater => balanceR k' v' l (insert cmp k v r)
     | Equal => Bin s k v l r)`;

val insertR_def = Define `
(insertR cmp k v Tip = singleton k v) ∧
(insertR cmp k v (Bin s k' v' l r) =
  case cmp k k' of
     | Less => balanceL k' v' (insertR cmp k v l) r
     | Greater => balanceR k' v' l (insertR cmp k v r)
     | Equal => Bin s k' v' l r)`;

val insertMax_def = Define `
(insertMax k v Tip = singleton k v) ∧
(insertMax k v (Bin s k' v' l r) = balanceR k' v' l (insertMax k v r))`;

val insertMin_def = Define `
(insertMin k v Tip = singleton k v) ∧
(insertMin k v (Bin s k' v' l r) = balanceL k' v' (insertMin k v l) r)`;

val deleteFindMax_def = Define `
(deleteFindMax (Bin s k x l Tip) = ((k,x),l)) ∧
(deleteFindMax (Bin s k x l r) =
  let (km,r') = deleteFindMax r in 
    (km,balanceL k x l r')) ∧
(deleteFindMax Tip =
  (ARB,Tip))`; (*(error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)*)

val deleteFindMin_def = Define `
(deleteFindMin (Bin s k x Tip r) = ((k,x),r)) ∧
(deleteFindMin (Bin s k x l r) =
  let (km,l') = deleteFindMin l in 
    (km,balanceR k x l' r)) ∧
(deleteFindMin Tip =
  (ARB,Tip))`; (*(error "Map.deleteFindMin: can not return the maximal element of an empty map", Tip)*)

val glue_def = Define `
(glue Tip r = r) ∧
(glue l Tip = l) ∧
(glue l r =
  if size l > size r then
    let ((km,m),l') = deleteFindMax l in 
      balanceR km m l' r
  else
    let ((km,m),r') = deleteFindMin r in 
      balanceL km m l r')`;

val delete_def = Define `
(delete cmp k Tip = Tip) ∧
(delete cmp k (Bin s k' v l r) =
  case cmp k k' of
     | Less => balanceR k' v (delete cmp k l) r
     | Greater => balanceL k' v l (delete cmp k r)
     | Eq => glue l r)`;

val trim_help_greater_def = Define `
(trim_help_greater cmp lo (Bin s' k v' l' r) = 
  if cmp k lo = Less ∨ cmp k lo = Equal then
    trim_help_greater cmp lo r
  else
    Bin s' k v' l' r) ∧
(trim_help_greater cmp lo Tip = Tip)`;

val trim_help_lesser_def = Define `
(trim_help_lesser cmp hi (Bin s' k v' l r') = 
  if cmp k hi = Greater ∨ cmp k hi = Equal then
    trim_help_lesser cmp hi l
  else
    Bin s' k v' l r') ∧
(trim_help_lesser cmp lo Tip = Tip)`;

val trim_help_middle_def = Define `
(trim_help_middle cmp lo hi (Bin s' k v' l r) = 
  if cmp k lo = Less ∨ cmp k lo = Equal then
    trim_help_middle cmp lo hi r
  else if cmp k hi = Greater ∨ cmp k hi = Equal then
    trim_help_middle cmp lo hi l
  else
    Bin s' k v' l r) ∧
(trim_help_middle lo cmp hi Tip = Tip)`;

val trim_def = Define `
(trim cmp NONE NONE t = t) ∧
(trim cmp (SOME lk) NONE t = trim_help_greater cmp lk t) ∧
(trim cmp NONE (SOME hk) t = trim_help_lesser cmp hk t) ∧
(trim cmp (SOME lk) (SOME hk) t = trim_help_middle cmp lk hk t)`;

val link_def = Define `
(link k v Tip r = insertMin k v r) ∧
(link k v l Tip = insertMax k v l) ∧
(link k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz) =
  if delta*sizeL < sizeR then
    balanceL kz z (link k v (Bin sizeL ky y ly ry) lz) rz
  else if delta*sizeR < sizeL then
    balanceR ky y ly (link k v ry (Bin sizeR kz z lz rz))
  else
    bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz))`;

val filterLt_help_def = Define `
(filterLt_help cmp b Tip = Tip) ∧
(filterLt_help cmp b' (Bin s kx x l r) =
  case cmp kx b' of
     | Less => link kx x l (filterLt_help cmp b' r)
     | Equal => l
     | Greater => filterLt_help cmp b' l)`;

val filterLt_def = Define `
(filterLt cmp NONE t = t) ∧
(filterLt cmp (SOME b) t = filterLt_help cmp b t)`;

val filterGt_help_def = Define `
(filterGt_help cmp b Tip = Tip) ∧
(filterGt_help cmp b' (Bin s kx x l r) =
  case cmp b' kx of
     | Less => link kx x (filterGt_help cmp b' l) r
     | Equal => r
     | Greater => filterGt_help cmp b' r)`;

val filterGt_def = Define `
(filterGt cmp NONE t = t) ∧
(filterGt cmp (SOME b) t = filterGt_help cmp b t)`;

val hedgeUnion_def = Define `
(hedgeUnion cmp blo bhi t1 Tip = t1) ∧
(hedgeUnion cmp blo bhi Tip (Bin _ kx x l r) = 
  link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) ∧
(hedgeUnion cmp blo bhi t1 (Bin _ kx x Tip Tip) = insertR cmp kx x t1) ∧
(hedgeUnion cmp blo bhi (Bin s kx x l r) t2 =
  link kx x (hedgeUnion cmp blo (SOME kx) l (trim cmp blo (SOME kx) t2))
            (hedgeUnion cmp (SOME kx) bhi r (trim cmp (SOME kx) bhi t2)))`;

val union_def = Define `
(union cmp Tip t2 = t2) ∧
(union cmp t1 Tip = t1) ∧
(union cmp t1 t2 = hedgeUnion cmp NONE NONE t1 t2)`;

val foldrWithKey_def = Define `
(foldrWithKey f z' Tip = z') ∧
(foldrWithKey f z' (Bin _ kx x l r) = 
  foldrWithKey f (f kx x (foldrWithKey f z' r)) l)`;

val toAscList_def = Define `
toAscList t = foldrWithKey (\k x xs. (k,x)::xs) [] t`;

val compare_def = Define `
compare cmp t1 t2 = list_cmp cmp (toAscList t1) (toAscList t2)`;

val map_def = Define `
(map _ Tip ⇔ Tip) ∧
(map f (Bin sx kx x l r) ⇔ Bin sx kx (f x) (map f l) (map f r))`;

val splitLookup_def = Define `
(splitLookup cmp k Tip = (Tip,NONE,Tip)) ∧
(splitLookup cmp k (Bin _ kx x l r) =
  case cmp k kx of
     | Less => 
         let (lt,z,gt) = splitLookup cmp k l in
         let gt' = link kx x gt r in
           (lt,z,gt')
     | Greater => 
         let (lt,z,gt) = splitLookup cmp k r in
         let lt' = link kx x l lt in
           (lt',z,gt)
     | Equal => 
         (l,SOME x,r))`;

val submap'_def = Define `
(submap' cmp _ Tip _ = T) ∧
(submap' cmp _ _ Tip = F) ∧
(submap' cmp f (Bin _ kx x l r) t = 
  case splitLookup cmp kx t of
     | (lt,NONE,gt) => F
     | (lt,SOME y,gt) => f x y ∧ submap' cmp f l lt ∧ submap' cmp f r gt)`;

val isSubmapOfBy_def = Define `
isSubmapOfBy cmp f t1 t2 ⇔ size t1 ≤ size t2 ∧ submap' cmp f t1 t2`;

val isSubmapOf_def = Define `
isSubmapOf cmp t1 t2 ⇔ isSubmapOfBy cmp (=) t1 t2`;


(* ----------------------- proofs ------------------------ *)

val balanceL_ind = fetch "-" "balanceL_ind";
val balanceR_ind = fetch "-" "balanceR_ind";

val balanceL'_thm = Q.prove (
`!k v l r. balanceL k v l r = balanceL' k v l r`,
 ho_match_mp_tac balanceL_ind >>
 rw [balanceL_def, balanceL'_def]);

val balanceR'_thm = Q.prove (
`!k v l r. balanceR k v l r = balanceR' k v l r`,
 ho_match_mp_tac balanceR_ind >>
 rw [balanceR_def, balanceR'_def]);

val to_fmap_def = Define `
(to_fmap cmp Tip = FEMPTY) ∧
(to_fmap cmp (Bin s k v l r) =
  (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v))`;

val to_fmap_key_set = Q.store_thm ("to_fmap_key_set",
`!cmp ks t.
  ks ∈ FDOM (to_fmap cmp t) ⇒ ?k. ks = key_set cmp k`,
 Induct_on `t` >>
 rw [to_fmap_def] >>
 metis_tac []);

val balanced_def = Define `
balanced l r ⇔
  l + r ≤ 1 ∨ MAX l r ≤ delta * MIN l r`;

val structure_size_def = Define `
(structure_size Tip = 0) ∧
(structure_size (Bin n k v l r) = 1 + structure_size l + structure_size r)`;

val key_ordered_def = Define `
(key_ordered cmp k Tip res ⇔ T) ∧
(key_ordered cmp k (Bin n k' v l r) res ⇔ 
  cmp k k' = res ∧
  key_ordered cmp k l res ∧
  key_ordered cmp k r res)`;

val key_ordered_to_fmap = Q.prove (
`!cmp k t res.
  good_cmp cmp ⇒
  (key_ordered cmp k t res
   ⇔
   (!ks. ks ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k ks res))`,
 Induct_on `t` >>
 rw [key_ordered_def, to_fmap_def] >>
 eq_tac >>
 rw [] >>
 metis_tac [key_set_cmp_thm]);

val invariant_def = Define `
(invariant cmp Tip ⇔ T) ∧
(invariant cmp (Bin s k v l r) ⇔
  s = 1 + structure_size l + structure_size r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  balanced (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r)`;

val invariant_eq = Q.prove (
`(invariant cmp Tip ⇔ T) ∧
 (invariant cmp (Bin s k v l r) ⇔
  (good_cmp cmp ⇒ DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))) ∧
  (good_cmp cmp ⇒ key_set cmp k ∉ FDOM (to_fmap cmp l)) ∧
  (good_cmp cmp ⇒ key_set cmp k ∉ FDOM (to_fmap cmp r)) ∧
  s = 1 + structure_size l + structure_size r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  balanced (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r)`,
 rw [invariant_def] >>
 eq_tac >>
 rw [DISJOINT_DEF, EXTENSION] >>
 CCONTR_TAC >>
 fs [] >>
 imp_res_tac key_ordered_to_fmap >>
 fs [] >>
 imp_res_tac to_fmap_key_set >>
 rw [] >>
 rfs [key_set_cmp_thm] >>
 metis_tac [cmp_thms]);

val inv_props = Q.prove (
`!cmp s k v l r.
  good_cmp cmp ∧
  invariant cmp (Bin s k v l r)
  ⇒
  DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp l) ⇒ cmp k x = Greater) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp r) ⇒ cmp k x = Less)`,
 rw [invariant_eq] >>
 imp_res_tac key_ordered_to_fmap >>
 rfs [key_set_cmp_thm]);

val structure_size_thm = Q.prove (
`!cmp t. invariant cmp t ⇒ size t = structure_size t`,
 Cases_on `t` >>
 rw [size_def, invariant_def, structure_size_def]);

val structure_size_to_fmap = Q.prove (
`!cmp t. good_cmp cmp ∧ invariant cmp t ⇒ FCARD (to_fmap cmp t) = structure_size t`,
 Induct_on `t` >>
 rw [invariant_eq, structure_size_def, to_fmap_def, FCARD_FEMPTY] >>
 rw [FCARD_FUPDATE, FCARD_DISJOINT_UNION]);

val size_thm = Q.store_thm ("size_thm",
`!cmp t. good_cmp cmp ∧ invariant cmp t ⇒ size t = FCARD (to_fmap cmp t)`,
 metis_tac [structure_size_thm, structure_size_to_fmap]);

val null_thm = Q.store_thm ("null_thm",
`!cmp t. null t ⇔ (to_fmap cmp t = FEMPTY)`,
 Cases_on `t` >>
 rw [null_def, to_fmap_def]);

val lookup_thm = Q.store_thm ("lookup_thm",
`!cmp k t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  lookup cmp k t = FLOOKUP (to_fmap cmp t) (key_set cmp k)`,
 Induct_on `t` >>
 rw [lookup_def, to_fmap_def] >>
 imp_res_tac inv_props >>
 every_case_tac >>
 fs [invariant_eq, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 rfs [key_set_eq] >>
 fs [FLOOKUP_DEF] >> 
 metis_tac [cmp_thms]);

val member_thm = Q.store_thm ("member_thm",
`!cmp k t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  (member cmp k t ⇔ key_set cmp k ∈ FDOM (to_fmap cmp t))`,
 Induct_on `t` >>
 rw [member_def, to_fmap_def] >>
 imp_res_tac inv_props >>
 every_case_tac >>
 fs [invariant_def, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 rfs [key_set_eq] >>
 fs [FLOOKUP_DEF] >>
 metis_tac [cmp_thms]);

val empty_thm = Q.store_thm ("empty_thm",
`!cmp. invariant cmp empty ∧ to_fmap cmp empty = FEMPTY`,
 rw [invariant_def, empty_def, to_fmap_def, FCARD_DEF]);

val singleton_thm = Q.store_thm ("singleton_thm",
`!cmp k v. invariant cmp (singleton k v) ∧ to_fmap cmp (singleton k v) = FEMPTY |+ (key_set cmp k,v)`,
 rw [balanced_def, invariant_def, singleton_def, to_fmap_def, size_def, structure_size_def,
     key_ordered_def]);

(* The balance routine from the comments in the Haskell file *)

val singleL_def = Define `
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3`;

val singleR_def = Define `
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)`;

val doubleL_def = Define `
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = 
  bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)`;

val doubleR_def = Define `
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = 
  bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)`;

val rotateL_def = Define `
(rotateL k x l (Bin s' k' x' ly ry) =
  if size ly < ratio * size ry then
    singleL k x l (Bin s' k' x' ly ry)
  else
    doubleL k x l (Bin s' k' x' ly ry)) ∧
(rotateL k x l Tip = 
  doubleL k x l Tip)`;

val rotateR_def = Define `
(rotateR k x (Bin s' k' x' ly ry) r =
  if size ry < ratio * size ly then
    singleR k x (Bin s' k' x' ly ry) r
  else
    doubleR k x (Bin s' k' x' ly ry) r) ∧
(rotateR k x Tip r = 
  doubleR k x Tip r)`;

val bal_def = Define `
bal k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size r > delta * size l then
    rotateL k x l r
  else if size l > delta * size r then
    rotateR k x l r
  else
    Bin (size l + size r + 1) k x l r`;
    
val balL_def = Define `
balL k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size l > delta * size r then
    rotateR k x l r
  else
    Bin (size l + size r + 1) k x l r`;

val balR_def = Define `
balR k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size r > delta * size l then
    rotateL k x l r
  else
    Bin (size l + size r + 1) k x l r`;

(* We want a formula that states how unbalanced two trees can be 
 * and still be re-balanced by the balancer. It also has to allow the
 * trees to be as unbalanced as the link, insert and delete functions need. The
 * formula below is the result of guesswork. *)
val almost_balancedL_def = Define `
almost_balancedL l r =
  if l + r ≤ 1 ∨ l ≤ delta * r then
    balanced l r
  else if r = 0 then
    l < 5
  else if r = 1 then
    l < 8
  else
    2 * l < (2 * delta + 3) * r + 2`;

val almost_balancedR_def = Define `
almost_balancedR l r =
  if l + r ≤ 1 ∨ r ≤ delta * l then
    balanced l r
  else if l = 0 then
    r < 5
  else if l = 1 then
    r < 8
  else
    2 * r < (2 * delta + 3) * l + 2`;

val balanced_lem1 = Q.prove (
`!l r. l + r ≤ 1 ⇒ balanced l r`,
 rw [balanced_def]);

val balanced_lem2 = Q.prove (
`!l r. 
  ¬(l > delta * r) ∧
  almost_balancedL l r ∧
  ¬(l + r ≤ 1)
  ⇒
  balanced l r`,
 rw [almost_balancedL_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER, TIMES_MIN, delta_def]);

val balanced_lem3 = Q.prove (
`!b b0 r.
 almost_balancedL (b + b0 + 1) r ∧
 b + b0 + 1 > delta * r ∧
 b0 < ratio * b ∧
 balanced b b0
 ⇒
 balanced b (b0 + r + 1) ∧ 
 balanced b0 r`,
 rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]);

val balanced_lem4 = Q.prove (
`!b b' b0' r.
  almost_balancedL (b + b' + b0' + 2) r ∧
  b + b' + b0' + 2 > delta * r ∧
  ¬(b' + b0' + 1 < ratio * b) ∧
  balanced b (b' + b0' + 1) ∧
  balanced b' b0'
  ⇒
  balanced (b + b' + 1) (b0' + r + 1) ∧
  balanced b b' ∧
  balanced b0' r`,
 rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]);

val balanced_lem5 = Q.prove (
`!l r. 
  ¬(r > delta * l) ∧
  almost_balancedR l r
  ⇒
  balanced l r`,
 rw [almost_balancedR_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER, TIMES_MIN, delta_def]);

val balanced_lem6 = Q.prove (
`!b b0 l.
 almost_balancedR l (b + b0 + 1) ∧
 b + b0 + 1 > delta * l ∧
 b < ratio * b0 ∧
 balanced b b0
 ⇒
 balanced (b + l + 1) b0 ∧ balanced l b`,
 rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]);

val balanced_lem7 = Q.prove (
`!b b0 b0' l b'.
  almost_balancedR l (b' + b0 + b0' + 2) ∧
  b' + b0 + b0' + 2 > delta * l ∧
  ¬(b' + b0' + 1 < ratio * b0) ∧
  balanced (b' + b0' + 1) b0 ∧
  balanced b' b0'
  ⇒
  balanced (b' + l + 1) (b0 + b0' + 1) ∧
  balanced l b' ∧
  balanced b0' b0`,
 rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]);

val singleR_thm = Q.prove (
`!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  size b0 < ratio * size b ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
  ⇒
  invariant cmp (singleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (singleR k v (Bin n k' v' b b0) r) = 
    (FUNION (to_fmap cmp (Bin n k' v' b b0)) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 rw [singleR_def] >>
 imp_res_tac inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def, key_ordered_def] >>
     imp_res_tac structure_size_thm >>
     rw [size_def] >>
     rfs [size_def, key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, balanced_lem3, ADD_ASSOC])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES, FUNION_ASSOC]));

val doubleR_thm = Q.prove (
`!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  ¬(size b0 < ratio * size b) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
  ⇒
  invariant cmp (doubleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (doubleR k v (Bin n k' v' b b0) r) = 
    (FUNION (to_fmap cmp (Bin n k' v' b b0)) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 rw [] >>
 `structure_size b0 ≠ 0` 
          by (fs [delta_def, ratio_def, invariant_def, size_def, 
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >> 
              imp_res_tac structure_size_thm >>
              fs []) >>
 Cases_on `b0` >>
 fs [structure_size_def, doubleR_def, bin_def] >>
 imp_res_tac inv_props >>
 fs [Once invariant_def] >>
 imp_res_tac inv_props >>
 fs [invariant_def, to_fmap_def]
 >- (fs [size_def, bin_def, to_fmap_def] >>
     imp_res_tac structure_size_thm >>
     simp [structure_size_def, key_ordered_def] >>
     fs [structure_size_def, to_fmap_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     rw []
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms] >>
     metis_tac [ADD_ASSOC, balanced_lem4])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms] >>
     `key_set cmp k' ≠ key_set cmp k'' ∧ 
      key_set cmp k ≠ key_set cmp k' ∧ 
      key_set cmp k ≠ key_set cmp k''` 
                   by metis_tac [key_set_eq, cmp_thms] >>
     metis_tac [FUPDATE_COMMUTES, FUNION_ASSOC]));

val rotateR_thm = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  ¬(size l + size r ≤ 1) ∧
  size l > delta * size r ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateR k v l r) ∧
  to_fmap cmp (rotateR k v l r) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
  Cases_on `l`
  >- fs [size_def] >>
  rw [size_def, rotateR_def] >>
  metis_tac [singleR_thm, doubleR_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]);

val balanceL_balL = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r 
  ⇒
  balanceL k v l r = balL k v l r`,
 ho_match_mp_tac balanceL_ind >>
 rw [] >>
 rw [balanceL_def, balL_def, rotateR_def, doubleR_def, bin_def, singleR_def] >>
 imp_res_tac structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 imp_res_tac structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 every_case_tac >>
 fs [size_def, structure_size_def, ratio_def, delta_def] >>
 imp_res_tac structure_size_thm >>
 fs [invariant_def, doubleR_def, bin_def, size_def] >>
 imp_res_tac structure_size_thm >>
 rw []);

val balanceL_thm = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceL k v l r) ∧
  to_fmap cmp (balanceL k v l r) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 rw [] >>
 `balanceL k v l r = balL k v l r` by metis_tac [balanceL_balL] >>
 rw [] >>
 rw [balL_def, invariant_def] >>
 imp_res_tac structure_size_thm >>
 rw [balanced_lem1, balanced_lem2, to_fmap_def] >>
 metis_tac [rotateR_thm]);

val singleL_thm = Q.prove (
`!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(size l + n ≤ 1) ∧
  n > delta * size l ∧
  size b < ratio * size b0 ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (singleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (singleL k v l (Bin n k' v' b b0)) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp (Bin n k' v' b b0))) |+ (key_set cmp k,v)`,
 rw [singleL_def] >>
 imp_res_tac inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def, key_ordered_def] >>
     imp_res_tac structure_size_thm >>
     rw [size_def] >>
     rfs [size_def, key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, balanced_lem6, ADD_ASSOC])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES, FUNION_ASSOC]));

val doubleL_thm = Q.prove (
`!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(n + size l ≤ 1) ∧
  n > delta * size l ∧
  ¬(size b < ratio * size b0) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (doubleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (doubleL k v l (Bin n k' v' b b0)) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp (Bin n k' v' b b0))) |+ (key_set cmp k,v)`,
 rw [] >>
 `structure_size b ≠ 0` 
          by (fs [delta_def, ratio_def, invariant_def, size_def, 
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >> 
              imp_res_tac structure_size_thm >>
              fs []) >>
 Cases_on `b` >>
 fs [structure_size_def, doubleL_def, bin_def] >>
 imp_res_tac inv_props >>
 fs [Once invariant_def] >>
 imp_res_tac inv_props >>
 fs [invariant_def, to_fmap_def]
 >- (fs [size_def, bin_def, to_fmap_def] >>
     imp_res_tac structure_size_thm >>
     simp [structure_size_def, key_ordered_def] >>
     fs [structure_size_def, to_fmap_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     rw []
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms] >>
     metis_tac [ADD_ASSOC, balanced_lem7])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- (`key_set cmp k' ≠ key_set cmp k'' ∧ 
          key_set cmp k ≠ key_set cmp k' ∧ 
          key_set cmp k ≠ key_set cmp k''` 
                   by metis_tac [key_set_eq, cmp_thms] >>
         metis_tac [FUPDATE_COMMUTES, FUNION_ASSOC])));

val rotateL_thm = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  ¬(size l + size r ≤ 1) ∧
  size r > delta * size l ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateL k v l r) ∧
  to_fmap cmp (rotateL k v l r) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 Cases_on `r`
 >- fs [size_def] >>
 rw [size_def, rotateL_def] >>
 metis_tac [singleL_thm, doubleL_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]);

val balanceR_balR = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r 
  ⇒
  balanceR k v l r = balR k v l r`,
 ho_match_mp_tac balanceR_ind >>
 rw [] >>
 rw [balanceR_def, balR_def, rotateL_def, doubleL_def, bin_def, singleL_def] >>
 imp_res_tac structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 imp_res_tac structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `v4` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 every_case_tac >>
 fs [size_def, structure_size_def, ratio_def, delta_def] >>
 imp_res_tac structure_size_thm >>
 fs [invariant_def, doubleL_def, bin_def, size_def] >>
 imp_res_tac structure_size_thm >>
 rw []);

val balanceR_thm = Q.prove (
`!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceR k v l r) ∧
  to_fmap cmp (balanceR k v l r) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 rw [] >>
 `balanceR k v l r = balR k v l r` by metis_tac [balanceR_balR] >>
 rw [balR_def, invariant_def] >>
 imp_res_tac structure_size_thm >>
 rw [balanced_lem1, balanced_lem5, to_fmap_def] >>
 metis_tac [rotateL_thm]);

val almost_balancedL_thm = Q.prove (
`!l r. 
  balanced l r ⇒ 
  almost_balancedL l r ∧ almost_balancedL (l + 1) r ∧ almost_balancedL l (r - 1)`,
 rw [almost_balancedL_def] >>
 fs [balanced_def, NOT_LESS_EQUAL, TIMES_MIN] >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 fs [NOT_LESS_EQUAL] >>
 fs [delta_def, MIN_DEF]);

val almost_balancedR_thm = Q.prove (
`!l r. 
  balanced l r ⇒ 
  almost_balancedR l r ∧ almost_balancedR l (r + 1) ∧ almost_balancedR (l - 1) r`,
 rw [almost_balancedR_def] >>
 fs [balanced_def, NOT_LESS_EQUAL, TIMES_MIN] >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 fs [NOT_LESS_EQUAL] >>
 fs [delta_def, MIN_DEF] >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 rw [] >>
 decide_tac);

val insert_thm = Q.store_thm ("insert_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (insert cmp k v t) ∧
  to_fmap cmp (insert cmp k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insert_def, singleton_def, to_fmap_def, invariant_eq, 
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 simp [invariant_eq] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insert_def] >>
 Cases_on `cmp k k'` >>
 fs [] >>
 simp [] >>
 TRY (inv_mp_tac balanceL_thm) >>
 TRY (inv_mp_tac balanceR_thm) >>
 conj_asm1_tac >>
 rw [to_fmap_def]
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedL_thm])
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     `key_set cmp k ≠ key_set cmp k'` by metis_tac [key_set_eq, cmp_thms] >>
     metis_tac [FUPDATE_COMMUTES])
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedR_thm])
 >- (rw [FUNION_FUPDATE_2, to_fmap_def] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [FUPDATE_COMMUTES, cmp_thms, to_fmap_key_set, key_set_cmp_thm])
 >- (fs [invariant_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms])
 >- metis_tac [key_set_eq, FUPDATE_EQ]);

val insertR_thm = Q.store_thm ("insertR_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (insertR cmp k v t) ∧
  to_fmap cmp (insertR cmp k v t) = 
    if key_set cmp k ∈ FDOM (to_fmap cmp t) then to_fmap cmp t else to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertR_def, singleton_def, to_fmap_def, invariant_def, 
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 imp_res_tac inv_props >>
 fs [insertR_def, invariant_def] >>
 Cases_on `cmp k k'` >>
 fs [] >>
 simp [to_fmap_def]
 >- (`almost_balancedL (size (insertR cmp k v t)) (size t')` 
             by (imp_res_tac size_thm >>
                 rw [FCARD_FUPDATE] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [almost_balancedL_thm]) >>
     `key_ordered cmp k' (insertR cmp k v t) Greater` 
              by (rfs [key_ordered_to_fmap] >>
                  rw [] >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [good_cmp_def]) >>
     rw [balanceL_thm] >>
     imp_res_tac balanceL_thm >>
     rw [FUNION_FUPDATE_1] >>
     metis_tac [FUPDATE_COMMUTES, good_cmp_def, comparison_distinct])
 >- (`almost_balancedR (size t) (size (insertR cmp k v t'))` 
             by (imp_res_tac size_thm >>
                 rw [FCARD_FUPDATE] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [almost_balancedR_thm]) >>
     `key_ordered cmp k' (insertR cmp k v t') Less` 
              by (fs [key_ordered_to_fmap] >>
                  rw [] >>
                  imp_res_tac to_fmap_key_set >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [cmp_thms]) >>
     rw [balanceR_thm] >>
     imp_res_tac balanceR_thm >>
     rw [FUNION_FUPDATE_2] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [FUPDATE_COMMUTES, good_cmp_def, comparison_distinct])
 >- (fs [invariant_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms,key_set_eq, FUPDATE_EQ]));

val insertMax_thm = Q.store_thm ("insertMax_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t ∧
  (!k1. k1 ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k k1 Greater)
  ⇒
  invariant cmp (insertMax k v t) ∧
  to_fmap cmp (insertMax k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertMax_def, singleton_def, to_fmap_def, invariant_def, 
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insertMax_def, invariant_def, to_fmap_def] >>
 inv_mp_tac balanceR_thm >>
 conj_asm1_tac >>
 simp []
 >- (rfs [key_ordered_to_fmap] >>
     imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [] >>
     metis_tac [almost_balancedR_thm, good_cmp_def, key_set_cmp_thm]) >>
 rw [FUNION_FUPDATE_2] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [FUPDATE_COMMUTES, cmp_thms, key_set_cmp_thm]);

val insertMin_thm = Q.store_thm ("insertMin_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t ∧
  (!k1. k1 ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k k1 Less)
  ⇒
  invariant cmp (insertMin k v t) ∧
  to_fmap cmp (insertMin k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertMin_def, singleton_def, to_fmap_def, invariant_def, 
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insertMin_def, invariant_def, to_fmap_def] >>
 simp [] >>
 `almost_balancedL (size (insertMin k v t)) (size t')` 
         by (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE] >>
             fs [key_ordered_to_fmap] >>
             metis_tac [almost_balancedL_thm]) >>
 `key_ordered cmp k' (insertMin k v t) Greater` 
              by (rfs [key_ordered_to_fmap] >>
                  rw [] >>
                  imp_res_tac to_fmap_key_set >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [cmp_thms, key_set_cmp_thm]) >>
 rw [balanceL_thm] >>
 imp_res_tac balanceL_thm >>
 rw [FUNION_FUPDATE_1] >>
 metis_tac [FUPDATE_COMMUTES, cmp_thms, key_set_cmp_thm]);

val deleteFindMin_thm = Q.store_thm ("deleteFindMin",
`∀t t' k v.
  good_cmp cmp ∧
  invariant cmp t ∧
  ~null t ∧
  deleteFindMin t = ((k,v),t')
  ⇒
  invariant cmp t' ∧
  key_ordered cmp k t' Less ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v ∧
  to_fmap cmp t' = 
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 ho_match_mp_tac (fetch "-" "deleteFindMin_ind") >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac >>
 rpt gen_tac >>
 TRY DISCH_TAC >>
 fs [deleteFindMin_def, invariant_eq, to_fmap_def] >>
 fs [null_def, to_fmap_def, FUNION_FEMPTY_1, deleteFindMin_def] >>
 BasicProvers.VAR_EQ_TAC >>
 fs [to_fmap_def, FLOOKUP_UPDATE, key_ordered_def, LET_THM, null_def]
 >- (rw [] >>
     fs [key_ordered_to_fmap] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     rw [flookup_thm] >>
     fs [] >>
     metis_tac [comparison_distinct, good_cmp_def]) >>
 `?km l. deleteFindMin (Bin (structure_size v8 + (structure_size v9 + 1)) v6 v7 v8 v9) = (km,l)`
            by metis_tac [pairTheory.pair_CASES] >>
 fs [] >>            
 rpt BasicProvers.VAR_EQ_TAC >>
 inv_mp_tac balanceR_thm >>
 simp [] >>
 Cases_on `key_set cmp v6 = key_set cmp k'` >>
 fs []
 >- (`FDOM (to_fmap cmp l) = FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
             by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                 fs [FDOM_DRESTRICT, EXTENSION] >>
                 rfs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             metis_tac [])
         >- (fs [size_def] >>
             imp_res_tac size_thm >>
             rw [DELETE_INSERT, FCARD_DRESTRICT] >>
             `key_set cmp k' ∉ FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
                          by (fs [key_ordered_to_fmap] >>
                              metis_tac [good_cmp_def, comparison_distinct]) >>
             imp_res_tac DELETE_NON_ELEMENT >>
             rw [CARD_DISJOINT_UNION] >>
             imp_res_tac almost_balancedR_thm >>
             fs [] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm])
 >- (`key_set cmp k' ∈ FDOM (to_fmap cmp v8 ⊌ to_fmap cmp v9)` 
           by (every_case_tac >>
               fs [FLOOKUP_DEF]) >>
     `key_set cmp k ≠ key_set cmp k' ∧ cmp k' k = Less`
             by (rfs [key_ordered_to_fmap] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms, to_fmap_key_set, key_set_cmp_thm]) >>
     simp [] >>
     `FDOM (to_fmap cmp l) = (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) DELETE key_set cmp k'`
                   by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                       fs [FDOM_DRESTRICT, EXTENSION] >>
                       rfs [key_ordered_to_fmap] >>
                       metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             fs [key_ordered_to_fmap] >>
             rw [key_set_cmp_thm] >>
             metis_tac [key_set_cmp_thm, to_fmap_key_set])
         >- (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE, FDOM_DRESTRICT] >>
             rw [FCARD_DRESTRICT, DELETE_INSERT] >>
             `(FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) ∩ 
              (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k')
              =
              FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k'`
                       by (rw [EXTENSION] >> 
                           metis_tac [key_set_eq, EXTENSION]) >>
             simp [CARD_UNION_EQN] >>
             fs [DISJOINT_DEF] >|
             [`CARD (FDOM (to_fmap cmp v8)) ≠ 0` 
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v8))` by decide_tac,
              `CARD (FDOM (to_fmap cmp v9)) ≠ 0` 
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v9))` by decide_tac] >>
             rw [] >>
             imp_res_tac almost_balancedR_thm >>
             fs [size_def] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]));

val deleteFindMax_thm = Q.store_thm ("deleteFindMax",
`∀t t' k v.
  good_cmp cmp ∧
  invariant cmp t ∧
  ~null t ∧
  deleteFindMax t = ((k,v),t')
  ⇒
  invariant cmp t' ∧
  key_ordered cmp k t' Greater ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v ∧
  to_fmap cmp t' = 
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 ho_match_mp_tac (fetch "-" "deleteFindMax_ind") >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac >>
 rpt gen_tac >>
 TRY DISCH_TAC >>
 fs [deleteFindMax_def, invariant_eq, to_fmap_def] >>
 fs [null_def, to_fmap_def, FUNION_FEMPTY_2, deleteFindMax_def] >>
 BasicProvers.VAR_EQ_TAC >>
 fs [to_fmap_def, FLOOKUP_UPDATE, key_ordered_def, LET_THM, null_def]
 >- (rw [] >>
     fs [key_ordered_to_fmap] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     rw [flookup_thm] >>
     fs [] >>
     metis_tac [comparison_distinct, good_cmp_def]) >>
 `?km l. deleteFindMax (Bin (structure_size v8 + (structure_size v9 + 1)) v6 v7 v8 v9) = (km,l)`
            by metis_tac [pairTheory.pair_CASES] >>
 fs [] >>            
 rpt BasicProvers.VAR_EQ_TAC >>
 inv_mp_tac balanceL_thm >>
 simp [] >>
 Cases_on `key_set cmp v6 = key_set cmp k'` >>
 fs []
 >- (`FDOM (to_fmap cmp l') = FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
             by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                 fs [FDOM_DRESTRICT, EXTENSION] >>
                 rfs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             metis_tac [])
         >- (fs [size_def] >>
             imp_res_tac size_thm >>
             rw [DELETE_INSERT, FCARD_DRESTRICT] >>
             `key_set cmp k' ∉ FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
                          by (fs [key_ordered_to_fmap] >>
                              metis_tac [good_cmp_def, comparison_distinct]) >>
             imp_res_tac DELETE_NON_ELEMENT >>
             rw [CARD_DISJOINT_UNION] >>
             imp_res_tac almost_balancedL_thm >>
             fs [] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm])
 >- (`key_set cmp k' ∈ FDOM (to_fmap cmp v8 ⊌ to_fmap cmp v9)` 
             by (every_case_tac >>
                 fs [FLOOKUP_DEF]) >>
     `key_set cmp k' ≠ key_set cmp k ∧ cmp k' k = Greater`
             by (rfs [key_ordered_to_fmap] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms, to_fmap_key_set, key_set_cmp_thm]) >>
     simp [] >>
     `FDOM (to_fmap cmp l') = (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) DELETE key_set cmp k'`
                   by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                       fs [FDOM_DRESTRICT, EXTENSION] >>
                       metis_tac [comparison_distinct, key_ordered_to_fmap, good_cmp_def]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             fs [key_ordered_to_fmap] >>
             rw [key_set_cmp_thm] >>
             metis_tac [key_set_cmp_thm, to_fmap_key_set])
         >- (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE, FDOM_DRESTRICT] >>
             rw [FCARD_DRESTRICT, DELETE_INSERT] >>
             `(FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) ∩ 
              (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k')
              =
              FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k'`
                       by (rw [EXTENSION] >> 
                           metis_tac [key_set_eq, EXTENSION]) >>
             simp [CARD_UNION_EQN] >>
             fs [DISJOINT_DEF] >|
             [`CARD (FDOM (to_fmap cmp v8)) ≠ 0` 
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v8))` by decide_tac,
              `CARD (FDOM (to_fmap cmp v9)) ≠ 0` 
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v9))` by decide_tac] >>
             rw [] >>
             imp_res_tac almost_balancedL_thm >>
             fs [size_def] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION]
    >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]));

val glue_thm = Q.store_thm ("glue_thm",
`!l r.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r ∧
  (!ks ks'. ks ∈ FDOM (to_fmap cmp l) ∧ ks' ∈ FDOM (to_fmap cmp r) ⇒ key_set_cmp2 cmp ks ks' Less) ∧
  balanced (size l) (size r)
  ⇒
  invariant cmp (glue l r) ∧
  to_fmap cmp (glue l r) = FUNION (to_fmap cmp l) (to_fmap cmp r)`,
 Cases_on `l` >>
 Cases_on `r` >>
 simp [size_def, glue_def] >>
 TRY (simp [to_fmap_def, FUNION_FEMPTY_2, FUNION_FEMPTY_1] >> NO_TAC) >>
 strip_tac >>
 Cases_on `n > n'` >>
 simp []
 >- (`?k' v' l. deleteFindMax (Bin n k v b b0) = ((k',v'),l)`
              by metis_tac [pairTheory.pair_CASES] >>
     simp [] >>
     inv_mp_tac balanceR_thm >>
     simp [] >>
     inv_to_front_tac ``invariant`` >>
     inv_mp_tac deleteFindMax_thm >>
     simp [Once SWAP_EXISTS_THM] >>
     qexists_tac `Bin n k v b b0` >>
     simp [null_def] >>
     strip_tac >>
     imp_res_tac fdom_eq >>
     fs [FDOM_DRESTRICT, DELETE_INSERT, FLOOKUP_UPDATE] >>
     fs [DELETE_INTER2] >>
     rw []
     >- (rw [fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
         every_case_tac >>
         fs [invariant_eq, FLOOKUP_DEF] >>
         metis_tac [good_cmp_def, comparison_distinct])
     >- (rfs [key_ordered_to_fmap] >>
         fs [FLOOKUP_DEF] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (fs [invariant_eq] >>
         `size l = size (Bin n k v b b0) - 1`
                     by (rw [size_def] >>
                         imp_res_tac size_thm >>
                         rw [FCARD_DEF, FDOM_FUPDATE, FDOM_DRESTRICT, to_fmap_def,
                             CARD_DISJOINT_UNION, DELETE_INTER2] >>
                         fs [to_fmap_def, FLOOKUP_DEF] >>
                         metis_tac [structure_size_thm, FCARD_DEF]) >>
         imp_res_tac almost_balancedR_thm >>
         fs [size_def] >>
         rw [] >>
         FULL_SIMP_TAC (srw_ss()++ARITH_ss) []))
 >- (`?k v l. deleteFindMin (Bin n' k' v' b' b0') = ((k,v),l)`
              by metis_tac [pairTheory.pair_CASES] >>
     simp [] >>
     inv_mp_tac balanceL_thm >>
     simp [] >>
     inv_to_front_tac ``invariant`` >>
     inv_mp_tac deleteFindMin_thm >>
     simp [Once SWAP_EXISTS_THM] >>
     qexists_tac `Bin n' k' v' b' b0'` >>
     simp [null_def] >>
     strip_tac >>
     imp_res_tac fdom_eq >>
     fs [FDOM_DRESTRICT, DELETE_INSERT, FLOOKUP_UPDATE] >>
     fs [DELETE_INTER2] >>
     rw []
     >- (rw [fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
         every_case_tac
         >- metis_tac [] >>
         fs [invariant_eq, FLOOKUP_DEF]
         >- metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (rfs [key_ordered_to_fmap] >>
         fs [FLOOKUP_DEF] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (fs [invariant_eq] >>
         `size l = size (Bin n' k' v' b' b0') - 1`
                     by (rw [size_def] >>
                         imp_res_tac size_thm >>
                         rw [FCARD_DEF, FDOM_FUPDATE, FDOM_DRESTRICT, to_fmap_def,
                             CARD_DISJOINT_UNION, DELETE_INTER2] >>
                         fs [to_fmap_def, FLOOKUP_DEF] >>
                         metis_tac [structure_size_thm, FCARD_DEF]) >>
         imp_res_tac almost_balancedL_thm >>
         fs [size_def] >>
         rw [] >>
         FULL_SIMP_TAC (srw_ss()++ARITH_ss) [])));

val to_fmap_tac =
  rw [to_fmap_def] >>
  rw [fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [FLOOKUP_DEF] >>
  fs [to_fmap_def] >>
  fs [key_ordered_to_fmap] >>
  rfs [key_ordered_to_fmap] >>
  metis_tac [cmp_thms, to_fmap_key_set, key_set_eq, key_set_cmp_thm];

val delete_thm = Q.store_thm ("delete_thm",
`!t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (delete cmp k t) ∧
  to_fmap cmp (delete cmp k t) = 
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 Induct_on `t`
 >- rw [delete_def, to_fmap_def] >>
 rpt gen_tac >>
 strip_tac >>
 simp [delete_def] >>
 fs [invariant_eq] >>
 Cases_on `cmp k k'` >>
 simp []
 >- (inv_mp_tac balanceR_thm >>
     simp [] >>
     rw [] 
     >- (fs [key_ordered_to_fmap] >>
         rfs [key_ordered_to_fmap] >>
         rw [FDOM_DRESTRICT] >>
         metis_tac [to_fmap_key_set, key_set_cmp_thm])
     >- (imp_res_tac size_thm >>
         rw [FCARD_DRESTRICT, DELETE_INTER2] >>
         imp_res_tac almost_balancedR_thm >>
         metis_tac [FCARD_DEF])
     >- to_fmap_tac)
 >- (inv_mp_tac balanceL_thm >>
     simp [] >>
     rw [] 
     >- (fs [key_ordered_to_fmap] >>
         rfs [key_ordered_to_fmap] >>
         rw [FDOM_DRESTRICT] >>
         metis_tac [to_fmap_key_set, key_set_cmp_thm])
     >- (imp_res_tac size_thm >>
         rw [FCARD_DRESTRICT, DELETE_INTER2] >>
         imp_res_tac almost_balancedL_thm >>
         metis_tac [FCARD_DEF])
     >- to_fmap_tac)
 >- (inv_mp_tac glue_thm >>
     rw [] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [key_set_cmp2_thm, to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- to_fmap_tac));     

val restrict_set_def = Define `
restrict_set cmp lo hi =
{ k | option_cmp cmp lo (SOME k) = Less ∧
      option_cmp2 cmp (SOME k) hi = Less }`;

val restrict_domain_def = Define `
  restrict_domain cmp lo hi m =
    DRESTRICT m (IMAGE (key_set cmp) (restrict_set cmp lo hi))`;

val restrict_domain_union = Q.prove (
`restrict_domain cmp lo hi (FUNION m1 m2) =
  FUNION (restrict_domain cmp lo hi m1) (restrict_domain cmp lo hi m2)`,
 rw [restrict_domain_def, fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >>
 rw [FLOOKUP_DRESTRICT, FLOOKUP_FUNION]);

val restrict_domain_update = Q.prove (
`good_cmp cmp
 ⇒
 restrict_domain cmp lo hi (m1 |+ (key_set cmp k,v)) =
   if k ∈ restrict_set cmp lo hi then 
     restrict_domain cmp lo hi m1 |+ (key_set cmp k,v)
   else
     restrict_domain cmp lo hi m1`,
 rw [restrict_domain_def, fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >>
 rfs [key_set_eq] >>
 fs [restrict_set_def] >>
 Cases_on `hi` >>
 Cases_on `lo` >>
 fs [option_cmp_def, option_cmp2_def] >>
 metis_tac [cmp_thms]);

val bounded_root_def = Define `
  bounded_root cmp lk hk t ⇔
    !s k v l r. t = Bin s k v l r ⇒ k ∈ restrict_set cmp lk hk`;

val trim_thm = Q.prove (
`!t lk hk cmp.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (trim cmp lk hk t) ∧
  bounded_root cmp lk hk (trim cmp lk hk t) ∧
  to_fmap cmp (trim cmp lk hk t) SUBMAP to_fmap cmp t ∧
  restrict_domain cmp lk hk (to_fmap cmp (trim cmp lk hk t)) = 
     restrict_domain cmp lk hk (to_fmap cmp t)`,
 Cases_on `lk` >> 
 Cases_on `hk` >> 
 simp [bounded_root_def, trim_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
 Induct_on `t` >>
 simp [trim_help_lesser_def, trim_help_greater_def, trim_help_middle_def, key_ordered_def] >>
 fs [invariant_eq] >>
 rpt gen_tac >>
 strip_tac >>
 every_case_tac >>
 fs [] >>
 simp [to_fmap_def] >>
 fs [SUBMAP_DEF, restrict_domain_def, DRESTRICTED_FUNION, DRESTRICT_FUPDATE] >>
 rw [invariant_def] >>
 rw [FAPPLY_FUPDATE_THM, FUNION_DEF, fmap_eq_flookup, FLOOKUP_DRESTRICT, 
     FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
 rw [] >>
 every_case_tac >>
 fs [flookup_thm, key_ordered_to_fmap, restrict_set_def, option_cmp_def, option_cmp2_def] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm, to_fmap_key_set]);

val link_balanced_lem1 = Q.prove (
`!r rz l.
  balanced r rz ∧
  delta * (l + 1) < r + (rz + 1)
  ⇒
  almost_balancedL (l + (r + 2)) rz`,
 fs [almost_balancedL_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 fs [MIN_DEF] >>
 rw [] >>
 every_case_tac >>
 fs [NOT_LESS, LESS_OR_EQ]);

val link_balanced_lem2 = Q.prove (
`!r l ly.
  balanced ly l ∧
  ¬(delta * (l + (ly + 1)) < r + 1) ∧
  delta * (r + 1) < l + (ly + 1)
  ⇒
  almost_balancedR ly (SUC (l + r) + 1)`,
 fs [ADD1, almost_balancedR_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 fs [MIN_DEF] >>
 rw [] >>
 every_case_tac >>
 fs [NOT_LESS, LESS_OR_EQ]);

val link_balanced_lem3 = Q.prove (
`!r l.
  ¬(delta * (l + 1) < r + 1) ∧
  ¬(delta * (r + 1) < l + 1)
  ⇒
  balanced (l + 1) (r + 1)`,
 fs [ADD1, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ, MIN_DEF]);

val link_thm = Q.prove (
`!k v l r.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less
  ⇒
  invariant cmp (link k v l r) ∧
  to_fmap cmp (link k v l r) = 
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)`,
 ho_match_mp_tac (fetch "-" "link_ind") >>
 rpt conj_tac >>
 simp [link_def] >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac
 >- (inv_mp_tac insertMin_thm >>
     rw []
     >- metis_tac [key_ordered_to_fmap] >>
     rw [to_fmap_def, FUNION_FEMPTY_1])
 >- (inv_mp_tac insertMax_thm >>
     rw []
     >- metis_tac [key_ordered_to_fmap] >>
     rw [to_fmap_def, FUNION_FEMPTY_2]) >>
 Cases_on `sizeL * delta < sizeR` >>
 simp [] >>
 fs []
 >- (strip_tac >>
     fs [invariant_eq, link_def, key_ordered_def] >>
     inv_mp_tac balanceL_thm >>
     simp [] >>
     rw []
     >- (rfs [key_ordered_to_fmap, to_fmap_def] >>
         rw [] >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
     >- (imp_res_tac size_thm >>
         rw [to_fmap_def] >>
         fs [] >>
         rfs [key_ordered_to_fmap] >>
         simp [FCARD_FUPDATE, key_set_eq] >>
         `key_set cmp k ∉ FDOM (to_fmap cmp ly) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp ky ∉ FDOM (to_fmap cmp r) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp r)`
                  by metis_tac [cmp_thms, key_set_cmp_thm] >>
         simp [FCARD_DEF] >>
         `DISJOINT (FDOM (to_fmap cmp ly) ∪ FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >> 
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         rw [CARD_DISJOINT_UNION] >>
         imp_res_tac structure_size_to_fmap >>
         fs [GSYM FCARD_DEF] >>
         metis_tac [link_balanced_lem1, ADD_ASSOC])
     >- to_fmap_tac) >>
 Cases_on `sizeR * delta < sizeL` >>
 simp [] >>
 fs []
 >- (strip_tac >>
     fs [invariant_eq, link_def, key_ordered_def] >>
     inv_mp_tac balanceR_thm >>
     simp [] >>
     rw []
     >- (rfs [key_ordered_to_fmap, to_fmap_def] >>
         rw [] >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
     >- (imp_res_tac size_thm >>
         rw [to_fmap_def] >>
         fs [] >>
         rfs [key_ordered_to_fmap] >>
         simp [FUNION_FUPDATE_2, FCARD_FUPDATE, key_set_eq] >>
         `key_set cmp k ∉ FDOM (to_fmap cmp rz) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp kz ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp r)`
                  by metis_tac [cmp_thms, key_set_cmp_thm] >>
         simp [FCARD_DEF] >>
         `DISJOINT (FDOM (to_fmap cmp l) ∪ FDOM (to_fmap cmp r)) (FDOM (to_fmap cmp rz))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >> 
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         `DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >> 
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         rw [CARD_DISJOINT_UNION] >>
         imp_res_tac structure_size_to_fmap >>
         fs [GSYM FCARD_DEF] >>
         metis_tac [link_balanced_lem2, ADD_ASSOC])
     >- to_fmap_tac)
 >- (simp [bin_def, size_def] >>
     rw [invariant_def, structure_size_def] >>
     fs [invariant_eq, size_def]
     >- metis_tac [link_balanced_lem3, structure_size_thm, ADD_ASSOC] >>
     to_fmap_tac));

val filter_lt_help_thm = Q.prove (
`!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterLt_help cmp bound t) ∧
  to_fmap cmp (filterLt_help cmp bound t) = restrict_domain cmp NONE (SOME bound) (to_fmap cmp t)`,
 Induct_on `t` >>
 simp [to_fmap_def, filterLt_help_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp k bound` >>
 simp []
 >- (inv_mp_tac link_thm >>
     conj_asm1_tac >>
     rw [] >>
     fs [invariant_eq]
     >- (rfs [key_ordered_to_fmap] >>
         rw [restrict_domain_def]) >>
     rw [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     to_fmap_tac)
 >- (first_x_assum inv_mp_tac >>
     fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac)
 >- (fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac));

val filterLt_thm = Q.prove (
`!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterLt cmp bound t) ∧
  to_fmap cmp (filterLt cmp bound t) = restrict_domain cmp NONE bound (to_fmap cmp t)`,
 Cases_on `bound` >>
 simp [to_fmap_def, filterLt_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rw [] >>
 imp_res_tac filter_lt_help_thm 
 >- (rw [fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
     rw [] >>
     fs [FLOOKUP_DEF] >>
     metis_tac [to_fmap_key_set]) >>
 rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]);

val filter_gt_help_thm = Q.prove (
`!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterGt_help cmp bound t) ∧
  to_fmap cmp (filterGt_help cmp bound t) = restrict_domain cmp (SOME bound) NONE (to_fmap cmp t)`,
 Induct_on `t` >>
 simp [to_fmap_def, filterGt_help_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp bound k` >>
 simp []
 >- (inv_mp_tac link_thm >>
     conj_asm1_tac >>
     rw [] >>
     fs [invariant_eq]
     >- (rfs [key_ordered_to_fmap] >>
         rw [restrict_domain_def]) >>
     rw [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     to_fmap_tac)
 >- (first_x_assum inv_mp_tac >>
     fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac)
 >- (fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac));

val filterGt_thm = Q.prove (
`!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterGt cmp bound t) ∧
  to_fmap cmp (filterGt cmp bound t) = restrict_domain cmp bound NONE (to_fmap cmp t)`,
 Cases_on `bound` >>
 simp [to_fmap_def, filterGt_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rw [] >>
 imp_res_tac filter_gt_help_thm 
 >- (rw [fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
     rw [] >>
     fs [FLOOKUP_DEF] >>
     metis_tac [to_fmap_key_set]) >>
 rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]);

val restrict_domain_partition = Q.prove (
`!cmp x l h t1 t2.
  good_cmp cmp ∧
  x ∈ restrict_set cmp l h ∧
  restrict_domain cmp l (SOME x) t2 SUBMAP t1 ∧
  restrict_domain cmp (SOME x) h t1 SUBMAP t2 ∧
  key_set cmp x ∉ FDOM t1 ∧
  key_set cmp x ∉ FDOM t2
  ⇒ 
  FUNION (restrict_domain cmp l h t1) (restrict_domain cmp l h t2) =
    FUNION (restrict_domain cmp l (SOME x) t1) (restrict_domain cmp (SOME x) h t2)`,
 rw [restrict_domain_def, fmap_eq_flookup] >>
 every_case_tac >>
 rw [] >>
 fs [restrict_set_def] >>
 `h = NONE ∨ ?h'. h = SOME h'` by Cases_on `h` >>
 `l = NONE ∨ ?l'. l = SOME l'` by Cases_on `l` >>
 fs [option_cmp_def, option_cmp2_def, SUBMAP_DEF, EXTENSION, FDOM_DRESTRICT, FLOOKUP_DEF,
     DRESTRICT_DEF, FAPPLY_FUPDATE_THM] >>
 fmrw [] >>
 metis_tac [cmp_thms, EXTENSION, key_set_eq]);

val restrict_domain_union_swap = Q.prove (
` good_cmp cmp
  ⇒ 
  a ⊌
  restrict_domain cmp blo (SOME kx) (to_fmap cmp r2) ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1')
  =
  a ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1') ⊌
  restrict_domain cmp blo (SOME kx) (to_fmap cmp r2)`,
 rw [restrict_domain_def] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 rw [restrict_set_def, fmap_eq_flookup] >>
 fmrw [] >>
 fs [option_cmp_def, option_cmp2_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [cmp_thms, key_set_eq]);

val restrict_domain_extend = Q.prove (
` good_cmp cmp ∧
  invariant cmp (Bin s kx x t1 t1') ∧
  kx ∈ restrict_set cmp blo bhi
  ⇒ 
  restrict_domain cmp blo (SOME kx) (to_fmap cmp t1) =
  restrict_domain cmp blo bhi (to_fmap cmp t1) ∧
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1') =
  restrict_domain cmp blo bhi (to_fmap cmp t1')`,
 rw [invariant_eq, restrict_domain_def] >>
 rfs [key_ordered_to_fmap] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 rw [restrict_set_def, fmap_eq_flookup] >>
 fmrw [] >>
 fs [option_cmp_def, option_cmp2_def, restrict_set_def] >>
 every_case_tac >>
 rw [FLOOKUP_DEF] >>
 metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm, to_fmap_key_set]);

val restrict_domain_combine = Q.prove (
` good_cmp cmp ∧
  key_set cmp kx ≠ k ∧
  kx ∈ restrict_set cmp blo bhi
  ⇒
  FLOOKUP (restrict_domain cmp (SOME kx) bhi (to_fmap cmp r2) ⊌
           restrict_domain cmp blo (SOME kx) (to_fmap cmp r2)) k =
  FLOOKUP (restrict_domain cmp blo bhi (to_fmap cmp r2)) k`,
 fmrw [restrict_domain_def] >>
 every_case_tac >>
 rw [] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fs [restrict_set_def, option_cmp2_def, option_cmp_def, FLOOKUP_DEF] >>
 metis_tac [key_set_eq, cmp_thms, to_fmap_key_set, key_set_cmp_thm]);

val bounded_all_def = Define `
(bounded_all cmp lk hk Tip ⇔ T) ∧
(bounded_all cmp lk hk (Bin s k v t1 t2) ⇔
  k ∈ restrict_set cmp lk hk ∧
  bounded_all cmp lk hk t1 ∧
  bounded_all cmp lk hk t2)`;

val bounded_all_shrink1 = Q.prove (
`!t blo bhi.
 good_cmp cmp ∧
 bounded_all cmp blo bhi t ∧
 key_ordered cmp kx t Greater
 ⇒
 bounded_all cmp blo (SOME kx) t`,
 Induct_on `t` >>
 rw [bounded_all_def, key_ordered_def]
 >- (Cases_on `blo` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct]) >>
 metis_tac []);

val bounded_all_shrink2 = Q.prove (
`!t blo bhi.
 good_cmp cmp ∧
 bounded_all cmp blo bhi t ∧
 key_ordered cmp kx t Less
 ⇒
 bounded_all cmp (SOME kx) bhi t`,
 Induct_on `t` >>
 rw [bounded_all_def, key_ordered_def]
 >- (Cases_on `bhi` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct]) >>
 metis_tac []);

val bounded_restrict_id = Q.prove (
`!t.
  good_cmp cmp ∧
  bounded_all cmp blo bhi t
  ⇒ 
  restrict_domain cmp blo bhi (to_fmap cmp t) = to_fmap cmp t`,
 Induct_on `t` >>
 rw [bounded_all_def, to_fmap_def, restrict_domain_union, restrict_domain_update] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def]);

val restrict_domain_empty = Q.prove (
`good_cmp cmp ⇒ 
  restrict_domain cmp blo (SOME kx) (restrict_domain cmp (SOME kx) bhi t) = FEMPTY ∧
  restrict_domain cmp (SOME kx) bhi (restrict_domain cmp blo (SOME kx) t) = FEMPTY`,
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fmrw [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def, fmap_eq_flookup] >>
 metis_tac [good_cmp_def, comparison_distinct, key_set_eq]);

val hedgeUnion_thm = Q.prove (
`!cmp blo bhi t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2 ∧
  bounded_all cmp blo bhi t1 ∧
  bounded_root cmp blo bhi t2
  ⇒
  invariant cmp (hedgeUnion cmp blo bhi t1 t2) ∧
  to_fmap cmp (hedgeUnion cmp blo bhi t1 t2) = 
     restrict_domain cmp blo bhi (to_fmap cmp t1 ⊌ to_fmap cmp t2)`,
 ho_match_mp_tac (fetch "-" "hedgeUnion_ind") >>
 rpt conj_tac >>
 simp [hedgeUnion_def] >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac 
 >- rw [to_fmap_def, FUNION_FEMPTY_2, bounded_restrict_id]
 >- (inv_mp_tac link_thm >>
     simp [GSYM CONJ_ASSOC] >>
     inv_mp_tac filterGt_thm >>
     simp [] >>
     fs [invariant_eq] >>
     strip_tac >>
     inv_mp_tac filterLt_thm >>
     simp [] >>
     strip_tac >>
     conj_tac
     >- (rfs [key_ordered_to_fmap, restrict_domain_def] >>
         Cases_on `blo` >>
         fs [restrict_set_def, option_cmp_def, option_cmp2_def]) >>
     conj_tac
     >- (rfs [key_ordered_to_fmap, restrict_domain_def] >>
         Cases_on `bhi` >>
         fs [restrict_set_def, option_cmp_def, option_cmp2_def]) >>
     `restrict_domain cmp blo bhi FEMPTY = FEMPTY` by rw [restrict_domain_def] >>
     rw [to_fmap_def, restrict_domain_union, restrict_domain_update] >>
     fmrw [restrict_domain_def, fmap_eq_flookup] >>
     rw [] >>
     Cases_on `blo` >>
     Cases_on `bhi` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def, bounded_root_def] >>
     fs [] >>
     rw [FLOOKUP_DEF] >>
     metis_tac [key_ordered_to_fmap, cmp_thms, to_fmap_key_set, key_set_cmp_thm])
 >- (inv_mp_tac insertR_thm >>
     imp_res_tac bounded_restrict_id >>
     rw [restrict_domain_union, to_fmap_def, restrict_domain_update] >>
     rw [restrict_domain_def, fmap_eq_flookup] >>
     fmrw [] >>
     every_case_tac >>
     fs [FLOOKUP_DEF, bounded_root_def]) >|
 [qabbrev_tac `r1 = Bin v39 v40 v41 v42 v43` >>
      qabbrev_tac `r2 = Bin v9 v10 v11 Tip r1`,
  qabbrev_tac `r1 = Bin v29 v30 v31 v32 v33` >>
      qabbrev_tac `r2 = Bin v9 v10 v11 r1 v13`] >>
(simp [bounded_all_def] >>
 strip_tac >>
 inv_mp_tac link_thm >>
 `invariant cmp t1'` by metis_tac [invariant_def] >>
 `invariant cmp t1` by metis_tac [invariant_def] >>
 simp [bounded_all_def, GSYM CONJ_ASSOC] >>
 FIRST_X_ASSUM inv_mp_tac >>
 simp [GSYM CONJ_ASSOC] >>
 inv_mp_tac trim_thm >>
 simp [bounded_all_def] >>
 strip_tac >>
 conj_tac
 >- (fs [invariant_eq] >>
     metis_tac [bounded_all_shrink1]) >>
 strip_tac >>
 FIRST_X_ASSUM inv_mp_tac >>
 simp [GSYM CONJ_ASSOC] >>
 inv_mp_tac trim_thm >>
 simp [bounded_all_def] >>
 strip_tac >>
 conj_tac
 >- (fs [invariant_eq] >>
     metis_tac [bounded_all_shrink2]) >>
 strip_tac >>
 qabbrev_tac `m1 = hedgeUnion cmp blo (SOME kx) t1 (trim cmp blo (SOME kx) r2)` >>
 qabbrev_tac `m2 = hedgeUnion cmp (SOME kx) bhi t1' (trim cmp (SOME kx) bhi r2)` >>
 conj_asm1_tac
 >- (rw [key_ordered_to_fmap, restrict_domain_union] >>
     Cases_on `blo` >>
     fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct, key_set_cmp_thm]) >>
 conj_asm1_tac
 >- (rw [key_ordered_to_fmap, restrict_domain_union] >>
     Cases_on `bhi` >>
     fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct, key_set_cmp_thm]) >>
 rw [restrict_domain_union, restrict_domain_update] >>
 `key_set cmp kx ∉ FDOM (to_fmap cmp m1) ∧ key_set cmp kx ∉ FDOM (to_fmap cmp m2)` 
             by metis_tac [key_ordered_to_fmap, cmp_thms, to_fmap_key_set, key_set_cmp_thm] >>
 `restrict_domain cmp blo (SOME kx) (to_fmap cmp m2) SUBMAP (to_fmap cmp m1) ∧
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp m1) SUBMAP (to_fmap cmp m2)`
              by (qunabbrev_tac `m1` >>
                  qunabbrev_tac `m2` >>
                  rw [restrict_domain_union, SUBMAP_DEF, restrict_domain_empty]) >>
 `restrict_domain cmp blo bhi (to_fmap cmp m1) ⊌
  restrict_domain cmp blo bhi (to_fmap cmp m2) =
  restrict_domain cmp blo (SOME kx) (to_fmap cmp m1) ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp m2)`
              by metis_tac [restrict_domain_partition] >>
 simp [restrict_domain_union, restrict_domain_update, to_fmap_def] >>
 rw [restrict_domain_union_swap] >>
 imp_res_tac restrict_domain_extend >>
 rw [] >>
 simp [fmap_eq_flookup] >>
 rw [FLOOKUP_UPDATE] >>
 REWRITE_TAC [GSYM FUNION_ASSOC] >>
 ONCE_REWRITE_TAC [FLOOKUP_FUNION] >>
 every_case_tac >>
 ONCE_REWRITE_TAC [FLOOKUP_FUNION] >>
 every_case_tac >>
 metis_tac [restrict_domain_combine]));

val bounded_all_NONE = Q.prove (
`!cmp t. bounded_all cmp NONE NONE t`,
 Induct_on `t` >>
 rw [bounded_all_def, restrict_set_def, option_cmp_def, option_cmp2_def]);

val union_thm = Q.store_thm ("union_thm",
`!cmp blo bhi t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2
  ⇒
  invariant cmp (union cmp t1 t2) ∧
  to_fmap cmp (union cmp t1 t2) = (to_fmap cmp t1 ⊌ to_fmap cmp t2)`,
 Cases_on `t1` >>
 Cases_on `t2` >>
 simp [union_def, to_fmap_def] >>
 gen_tac >>
 strip_tac >>
 inv_mp_tac hedgeUnion_thm >>
 rw [bounded_all_NONE, bounded_root_def, restrict_set_def, option_cmp_def,
     restrict_domain_def, option_cmp2_def, to_fmap_def] >>
 rw [fmap_eq_flookup] >>
 fmrw [] >>
 every_case_tac >>
 fs [FLOOKUP_DEF, invariant_eq] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [cmp_thms, to_fmap_key_set]);

val EXT2 = Q.prove (
`!s1 s2. s1 = s2 ⇔ (!k v. (k,v) ∈ s1 ⇔ (k,v) ∈ s2)`,
 rw [EXTENSION] >>
 EQ_TAC >>
 rw [] >>
 PairCases_on `x` >>
 rw []);

val lift_key_def = Define `
lift_key cmp kvs = IMAGE (\(k,v). (key_set cmp k, v)) kvs`;

val toAscList_helper = Q.prove (
`!cmp l t.
  good_cmp cmp ∧
  invariant cmp t ∧
  SORTED (\(x,y) (x',y'). cmp x x' = Less) l ∧
  (!k1 v1 k2 v2. MEM (k1,v1) l ∧ FLOOKUP (to_fmap cmp t) (key_set cmp k2) = SOME v2 ⇒ cmp k2 k1 = Less)
  ⇒
  SORTED (\(x,y) (x',y'). cmp x x' = Less) (foldrWithKey (λk x xs. (k,x)::xs) l t) ∧
  lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t)) = 
    set (fmap_to_alist (to_fmap cmp t)) ∪ lift_key cmp (set l)`,
 Induct_on `t` >>
 simp [foldrWithKey_def, to_fmap_def] >>
 fs [invariant_eq, EXT2] >>
 rpt gen_tac >>
 strip_tac >>
 simp [FLOOKUP_UPDATE, FLOOKUP_FUNION, PULL_FORALL] >>
 rpt gen_tac >>
 first_x_assum (qspecl_then [`cmp`, `l`] mp_tac) >>
 first_x_assum (qspecl_then [`cmp`, `(k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t'`] mp_tac) >>
 simp [] >>
 strip_tac >>
 strip_tac >>
 fs [FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 `SORTED (λ(x,y) (x',y'). cmp x x' = Less) (foldrWithKey (λk x xs. (k,x)::xs) l t') ∧
  ∀k v.
     (k,v) ∈ lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t')) ⇔
     FLOOKUP (to_fmap cmp t') k = SOME v ∨ (k,v) ∈ lift_key cmp (set l)`
              by (first_x_assum match_mp_tac >>
                  rw [] >>
                  last_x_assum match_mp_tac >>
                  rw []
                  >- metis_tac [] >>
                  qexists_tac `v1` >>
                  rw [] >>
                  qexists_tac `v2` >>
                  rw [] >>
                  every_case_tac >>
                  fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
                  metis_tac []) >>
 `SORTED (λ(x,y) (x',y'). cmp x x' = Less)
         (foldrWithKey (λk x xs. (k,x)::xs)
            ((k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t') t) ∧
       ∀k' v'.
         (k',v') ∈ lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) ((k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t') t)) ⇔
         FLOOKUP (to_fmap cmp t) k' = SOME v' ∨
         (k',v') ∈ lift_key cmp ((k,v) INSERT set (foldrWithKey (λk x xs. (k,x)::xs) l t'))`
              by (first_x_assum match_mp_tac >>
                  simp [good_cmp_trans, SORTED_EQ, FORALL_PROD] >>
                  rw []
                  >- (`(key_set cmp p_1, p_2) ∈ lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t'))`
                              by (fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
                                  metis_tac []) >>
                      rfs [FLOOKUP_DEF] >>
                      rfs [key_ordered_to_fmap]
                      >- metis_tac [cmp_thms, key_set_cmp_thm] >>
                      fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
                      metis_tac [cmp_thms, key_set_eq])
                  >- (rfs [key_ordered_to_fmap, FLOOKUP_DEF] >>
                      metis_tac [cmp_thms, key_set_cmp_thm])
                  >- (`(key_set cmp k1, v1) ∈ lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t'))`
                              by (fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
                                  metis_tac []) >>
                      rfs [FLOOKUP_DEF] >>
                      rfs [key_ordered_to_fmap]
                      >- metis_tac [cmp_thms, key_set_cmp_thm] >>
                      fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
                      metis_tac [cmp_thms, key_set_cmp_thm, key_set_eq])) >>
 simp [] >>
 eq_tac >>
 rw [] >>
 fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
 every_case_tac >>
 rw [] >>
 fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
 metis_tac []);

val toAscList_thm = Q.store_thm ("toAscList_thm",
`!cmp t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  SORTED (\(x,y) (x',y'). cmp x x' = Less) (toAscList t) ∧
  lift_key cmp  (set (toAscList t)) = set (fmap_to_alist (to_fmap cmp t))`,
 rpt gen_tac >>
 strip_tac >>
 qspecl_then [`cmp`, `[]`, `t`] mp_tac toAscList_helper >>
 simp [toAscList_def, lift_key_def]);

val compare_thm = Q.store_thm ("compare_thm",
`!cmp. good_cmp cmp ⇒ good_cmp (compare cmp)`,
 ntac 2 strip_tac >>
 imp_res_tac list_cmp_good >>
 rpt (pop_assum mp_tac) >>
 REWRITE_TAC [good_cmp_def, compare_def] >>
 metis_tac []);

val map_thm = Q.store_thm ("map_thm",
`!t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (map f t) ∧
  to_fmap cmp (map f t) = f o_f to_fmap cmp t`,
 Induct_on `t` >>
 simp [map_def, to_fmap_def]
 >- rw [invariant_def] >>
 rpt gen_tac >>
 strip_tac >>
 simp [invariant_def, GSYM CONJ_ASSOC] >>
 inv_to_front_tac ``invariant`` >>
 first_x_assum inv_mp_tac >>
 simp [] >>
 fs [invariant_eq] >>
 strip_tac >>
 imp_res_tac (GSYM structure_size_thm) >>
 imp_res_tac size_thm >>
 simp [FCARD_DEF] >>
 rw []
 >- rfs [key_ordered_to_fmap]
 >- rfs [key_ordered_to_fmap]
 >- fs [FCARD_DEF]
 >- (fmrw [fmap_eq_flookup] >>
     fmrw [FLOOKUP_o_f, DOMSUB_FLOOKUP_THM] >>
     every_case_tac >>
     fs []));

val splitLookup_thm = Q.store_thm ("splitLookup_thm",
`!t lt v gt.
  good_cmp cmp ∧
  invariant cmp t ∧
  (lt,v,gt) = splitLookup cmp k t
  ⇒
  invariant cmp lt ∧
  invariant cmp gt ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = v ∧
  key_ordered cmp k lt Greater ∧
  key_ordered cmp k gt Less ∧
  to_fmap cmp t = 
    case v of
       | NONE => FUNION (to_fmap cmp lt) (to_fmap cmp gt)
       | SOME v => (FUNION (to_fmap cmp lt) (to_fmap cmp gt)) |+ (key_set cmp k, v)`,
 Induct_on `t` >>
 simp [splitLookup_def, to_fmap_def, key_ordered_to_fmap] >>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp k k'` >>
 fs []
 >- (`?lt v gt. splitLookup cmp k t = (lt,v,gt)` by metis_tac [pair_CASES] >>
     fs [] >>
     last_x_assum inv_mp_tac >>
     simp [] >>
     fs [invariant_eq] >>
     strip_tac >>
     inv_mp_tac link_thm >>
     simp [] >>
     conj_asm1_tac
     >- (rfs [key_ordered_to_fmap] >>
         rw [] >>
         first_x_assum match_mp_tac >>
         rw [] >>
         every_case_tac >>
         fs []) >>
     strip_tac >>
     Cases_on `v''` >>
     fs [] >>
     fmrw [] >>
     rfs [FLOOKUP_FUNION] >>
     every_case_tac >>
     fs [] >>
     TRY (match_mp_tac FUPDATE_COMMUTES) >>
     rfs [key_ordered_to_fmap, flookup_thm] >>
     res_tac >>
     metis_tac [cmp_thms, key_set_cmp_def, key_set_cmp_thm])
 >- (`?lt v gt. splitLookup cmp k t' = (lt,v,gt)` by metis_tac [pair_CASES] >>
     fs [] >>
     fs [invariant_eq] >>
     inv_mp_tac link_thm >>
     simp [] >>
     conj_asm1_tac
     >- (rfs [key_ordered_to_fmap] >>
         rw [] >>
         first_x_assum match_mp_tac >>
         rw [] >>
         every_case_tac >>
         fs []) >>
     strip_tac >>
     Cases_on `v''` >>
     fs [] >>
     fmrw [] >>
     rfs [FLOOKUP_FUNION] >>
     every_case_tac >>
     fs [] >>
     TRY (match_mp_tac FUPDATE_COMMUTES) >>
     rfs [key_ordered_to_fmap, flookup_thm] >>
     fs [key_ordered_to_fmap, flookup_thm] >>
     res_tac >>
     metis_tac [cmp_thms, key_set_cmp_def, key_set_cmp_thm])
 >- (fs [invariant_eq] >>
     fmrw [key_set_eq] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     fs [key_set_cmp_def] >>
     fmrw [fmap_eq_flookup] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     rfs [key_set_eq] >>
     metis_tac [cmp_thms]));

     (*
val submap'_thm = Q.prove (
`!cmp f t1 t2.
 good_cmp cmp ∧
 invariant cmp t1 ∧
 invariant cmp t2
 ⇒
 (submap' cmp f t1 t2 ⇔ !k v. lookup cmp k t1 = SOME v ⇒ ?v'. lookup cmp k t2 = SOME v' ∧ f v v')`, 
 ho_match_mp_tac (fetch "-" "submap'_ind") >>
 rpt conj_tac
 >- rw [lookup_def, submap'_def]
 >- (rw [lookup_def, submap'_def, invariant_eq] >>
     qexists_tac `v11` >>
     qexists_tac `v12` >>
     every_case_tac >>
     fs [] >>
     metis_tac [cmp_thms]) >>
 rw [] >>
 qabbrev_tac `t = Bin v20 v21 v22 v23 v24` >>
 `?lt v gt. splitLookup cmp kx t = (lt,v,gt)` by metis_tac [pair_CASES] >>
 fs [] >>
 `invariant cmp lt ∧ invariant cmp gt ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp kx) = v ∧
  key_ordered cmp kx lt Greater ∧ key_ordered cmp kx gt Less ∧
  to_fmap cmp t =
  case v of
    NONE => to_fmap cmp lt ⊌ to_fmap cmp gt
  | SOME v' => (to_fmap cmp lt ⊌ to_fmap cmp gt) |+ (key_set cmp kx,v')`
                 by metis_tac [splitLookup_thm] >>
 unabbrev_all_tac >>
 Cases_on `v` >>
 fs []
 >- (rw [submap'_def, lookup_def] >>
     qexists_tac `kx` >>
     qexists_tac `x` >>
     rw []
     >- metis_tac [cmp_thms] >>
     every_case_tac >>
     fs [] >>
     CCONTR_TAC >>
     fs [] >>
     imp_res_tac lookup_thm >>
     fs [lookup_def, to_fmap_def] >>
     metis_tac [cmp_thms, NOT_SOME_NONE])
 >- (fs [to_fmap_def, invariant_eq] >>
     rw [submap'_def, lookup_def] >>
     eq_tac >>
     simp []
     >- (rw [] >>
         `FLOOKUP ((to_fmap cmp v23 ⊌ to_fmap cmp v24) |+ (key_set cmp v21,v22)) (key_set cmp k) =
          FLOOKUP ((to_fmap cmp lt ⊌ to_fmap cmp gt) |+ (key_set cmp kx,x')) (key_set cmp k)` 
                      by metis_tac [] >>
         fs [FLOOKUP_UPDATE] >>
         cheat) >>
     strip_tac >>
     cheat));
     *)

val _ = export_theory ();
