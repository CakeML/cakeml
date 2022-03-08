(*
Formalization written by Alexander Cox
*)

open preamble;

open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;

val _ = new_theory"LZSS";


Datatype:
  LZSS = Lit 'a | LenDist (num # num)
End

Overload LAST32k = “LASTN 32768”

Definition matchLength_def[simp]:
  (matchLength s []:num = 0) ∧
  (matchLength [] l = 0) ∧
  (matchLength (s::ss) (l::ls) =
   if (s = l)
   then (1 + (matchLength ss ls))
   else 0)
End

(* find the longest, right-most match *)
Definition getMatch_def[simp]:
  (getMatch [] l : num # num = (0,0)) ∧
  (getMatch s [] = (0,0)) ∧
  (getMatch (s::ss) (l::ls) =
   let ml = matchLength (s::ss) (l::ls);
       (next_ml,next_md) = getMatch ss (l::ls)
   in if next_ml < ml then (ml,0)
      else (next_ml,next_md+1))
End

Definition LZmatch_def[simp]:
  (LZmatch b [] = NONE) ∧
  (LZmatch buffer lookahead =
  let match = getMatch buffer lookahead
  in if FST match < 3                       (* This looks like LZSS and not LZ77 *)
     then SOME $ Lit (HD lookahead)
     else SOME $ LenDist (FST match, (LENGTH buffer - (SND match))))
End

(* fixed parameter ordering to here FIXME *)

Definition LZinit_def:
  LZinit s = ([],
              TAKE (MIN 258 (LENGTH s))   s,
              DROP ((MIN 258 (LENGTH s))) s)
End

Definition tripleLength_def:
  tripleLength (a,b,c) = LENGTH a + LENGTH b + LENGTH c
End


(*
s:
split:
bufsize:
looksize:
        *)

(* new version which takes buffer size as a parameter and searches into lookahead *)
Definition LZcomp_def:
  LZcomp s split bufSize lookSize =
  if LENGTH s ≤ split ∨ s = [] ∨ split = 0 ∨ bufSize = 0 ∨ lookSize = 0 then []
  else
    let match = LZmatch s (TAKE lookSize (DROP split s));
        len = case match of
              | NONE => 1
              | SOME $ LenDist (ml,_) => MAX ml 1
              | SOME $ Lit _ => 1;
        bufDrop = (split + len) - bufSize;
        recurse = (LZcomp (DROP bufDrop s) (split + len) bufSize lookSize)
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination
  WF_REL_TAC ‘measure $ λ(s,split,_,_). MIN (LENGTH s) (LENGTH s - split)’ >>
  rw[NOT_LESS_EQUAL] >>
  CASE_TAC
  >- (Cases_on ‘split + 1 < bufSize’ >> gs[NOT_LESS,MIN_DEF]) >>
  CASE_TAC
  >- (Cases_on ‘split + 1 < bufSize’ >> gs[NOT_LESS,MIN_DEF]) >>
  CASE_TAC >>
  simp[MAX_DEF,MIN_DEF]
End

EVAL “LZcomp "aaaaaabbcbbbbaaaacaaaaada" 0 10 5 ”;


(* new version which takes buffer size as a parameter and searches into lookahead *)
Definition LZcompLP_def:
  LZcompLP s split bufSize lookSize =
  if LENGTH s ≤ split ∨ s = [] ∨ bufSize = 0 ∨ lookSize = 0 then []
  else
    let match = LZmatch (TAKE split s) (TAKE lookSize (DROP split s));
        len = case match of
              | NONE => 1
              | SOME $ LenDist (ml,_) => MAX ml 1
              | SOME $ Lit _ => 1;
        bufDrop = (split + len) - bufSize;
        recurse = (LZcompLP (DROP bufDrop s) (split + len - bufDrop) bufSize lookSize)
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination
  WF_REL_TAC ‘measure $ λ(s,split,_,_). MIN (LENGTH s) (LENGTH s - split)’ >>
  rw[NOT_LESS_EQUAL] >>
  CASE_TAC
  >- (Cases_on ‘split + 1 < bufSize’ >> gs[NOT_LESS,MIN_DEF]) >>
  CASE_TAC
  >- (Cases_on ‘split + 1 < bufSize’ >> gs[NOT_LESS,MIN_DEF]) >>
  CASE_TAC >>
  simp[MAX_DEF,MIN_DEF]
End

EVAL “LZcompLP "aaaaaabbcbbbbaaaacaaaaada" 0 258 258”;

(* old and broken, but has stuff proved about it *)
Definition LZcompress_def:
  (LZcompress s [] [] = []) ∧
  (LZcompress s [] t = []) ∧
  (LZcompress search lookahead [] =
   let match = LZmatch search lookahead;
       len = case match of
             | NONE => 1
             | SOME $ LenDist (ml,_) => MAX ml 1
             | SOME $ Lit _ => 1;
       search = search ++ (TAKE len lookahead);
       lookahead = DROP len lookahead ;
       recurse = (LZcompress (LAST32k search) lookahead [])
   in case match of
      | NONE => recurse
      | SOME m => m::recurse) ∧
  (LZcompress search lookahead remainder =
   let match = LZmatch search lookahead;
       len = case match of
             | NONE => 1
             | SOME $ LenDist (ml,_) => MAX ml 1
             | SOME $ Lit _ => 1;
       search = search ++ (TAKE len lookahead);
       lookahead = (DROP len lookahead) ++ (TAKE len remainder) ;
       remainder = DROP len remainder;
       recurse = (LZcompress (LAST32k search) lookahead remainder)
   in case match of
      | NONE => recurse
      | SOME m => m::recurse)
Termination
  WF_REL_TAC ‘measure $ λ(s,l,r). LENGTH l + LENGTH r’ >>
  rw[] >>
  Cases_on ‘getMatch (v10::v11) search’ >>
  gvs[MAX_DEF] >>
  simp[LENGTH_TAKE_EQ] >>
  cheat
End

Definition LZSS_compress_def:
  LZSS_compress s =
   let (searchBuffer,lookaheadBuffer,remainder) = LZinit s;
   in LZcompress searchBuffer lookaheadBuffer remainder
End

Definition resolveLenDist_def[simp]:
  (resolveLenDist [] _ = NONE) ∧
  (resolveLenDist s (l,d) =
   if (LENGTH s < d) ∨ (LENGTH s < l) ∨ d < 1 ∨ l < 1
   then NONE
   else
     SOME $ TAKE l $ DROP (LENGTH s - d) s)
End

Definition LZdecompress_def:
  (LZdecompress de [] = de) ∧
  (LZdecompress de (next::t) =
   let
     newde =
     case next of
     | Lit a => SNOC a de
     | LenDist ld => case (resolveLenDist de ld) of
                     | NONE => de
                     | SOME s => de ++ s
   in
     LZdecompress newde t)
End

Definition LZSS_decompress_def:
  LZSS_decompress s = LZdecompress [] s
End


(****************************************
*****                              ******
*****       Used by theorems       ******
*****                              ******
****************************************)

Definition matches_def:
  matches s l = {(len,dist)| TAKE len l = TAKE len $ DROP dist s}
End

Definition longestMatches_def:
  longestMatches s l = {(len,dist) | ((len,dist) IN matches s l) ∧
  (∀ len' dist'. (len',dist') IN matches s l ⇒ len' ≤ len )}
End


Definition backMatches_def:
  backMatches s l = {(bl,bd)| TAKE bl l = TAKE bl $ DROP (LENGTH s - bd) s}
End

Definition matchLengthRB_def:
  (matchLengthRB (rb,0):num = 0) ∧
  (matchLengthRB (rb,split) =
  let
    l = list_of_ringBuffer rb;
  in
    matchLength l (DROP split l))
End

Definition matchLengthRB'_def:
  (matchLengthRB' (rb,split) si li :num =
  if rb.size ≤ li
  then 0
  else if rbEL si rb = rbEL li rb ∧ rbEL li rb ≠ NONE ∧ rbEL si rb ≠ NONE
  then 1 + (matchLengthRB' (rb,split) (SUC si) (SUC li))
  else 0)
Termination
  WF_REL_TAC ‘measure (λ (rb,split), si, li. rb.size - li)’
End


(***************************************
******                            ******
******          Theorems          ******
******                            ******
***************************************)




Theorem matchLength_nil[simp]: matchLength [] l = 0
Proof Cases_on ‘l’ >> simp[]
QED

Theorem matchLength_nil2[simp]: matchLength s [] = 0
Proof Cases_on ‘s’ >> simp[]
QED

Theorem matchLengthWorks:
  ∀ s l len. matchLength s l  = len ⇒ (TAKE len s) = (TAKE len l)
Proof
  Induct_on ‘l’ >- simp[] >>
  Cases_on ‘s’ >- simp[] >>
  rw[]
QED


Theorem MOD_lemma:
  0 < y ∧ y ≤ x ∧ x < 2 * y ⇒ (x MOD y = x - y)
Proof
  strip_tac >> drule_then (qspec_then ‘x’ strip_assume_tac) DIVISION >>
  qabbrev_tac ‘q = x DIV y’ >> qabbrev_tac ‘r = x MOD y’ >>
  markerLib.RM_ALL_ABBREVS_TAC >> gvs[] >> ‘q = 1’ suffices_by simp[] >>
  ‘r < 2*y - q * y’ by simp[] >>
  fs[GSYM RIGHT_SUB_DISTRIB] >>
  ‘q < 2’ by (CCONTR_TAC >> ‘2 - q = 0’ by simp[] >> pop_assum SUBST_ALL_TAC >>
              gs[]) >>
  ‘q ≠ 0’ by (strip_tac >> gs[]) >> simp[]
QED

Theorem rbEL_EL:
  WFrb rb ⇒
  (rbEL i rb = SOME e ⇔
     i < rb.size ∧ EL i (list_of_ringBuffer rb) = e)
Proof
  simp[rbEL_def, list_of_ringBuffer_def, WFrb_def, oEL_THM] >>
  Cases_on ‘i < rb.size’ >> simp[] >>
  Cases_on ‘rb.buffer = []’ >> gs[] >> strip_tac >>
  Cases_on ‘i + rb.start < iMAX rb’ >> simp[]
  >- (‘LENGTH (DROP rb.start rb.buffer) = iMAX rb - rb.start’ by simp[] >>
      Cases_on ‘rb.size ≤ iMAX rb - rb.start’
      >- simp[EL_APPEND1, EL_TAKE, EL_DROP] >>
      simp[TAKE_LENGTH_TOO_LONG] >> simp[EL_APPEND1, EL_DROP]) >>
  ‘(i + rb.start) MOD iMAX rb = i + rb.start - iMAX rb’
    by (irule MOD_lemma >> simp[]) >>
  simp[] >>
  ‘LENGTH (DROP rb.start rb.buffer) = iMAX rb - rb.start’ by simp[] >>
  Cases_on ‘rb.size ≤ iMAX rb - rb.start’
  >- (simp[EL_APPEND2, EL_TAKE, EL_DROP] >>
      ‘i + rb.start - iMAX rb = i - rb.size’ by simp[] >> simp[]) >>
  simp[EL_APPEND2, EL_TAKE, EL_DROP, TAKE_LENGTH_TOO_LONG]
QED

Theorem TAKE_EL_DROP:
  n < LENGTH l ∧ EL n l = a ⇒ l = TAKE n l ++ [a] ++ DROP (n + 1) l
Proof
  rpt strip_tac >>
  ‘l = TAKE n l ++ DROP n l’ by simp[GSYM TAKE_DROP] >>
  ‘DROP n l = [a] ++ DROP (n + 1) l’ by simp[DROP_EL_CONS] >>
  Cases_on ‘DROP n l’
  >- gs[CONS_APPEND] >>
  gs[DROP_EL_CONS]
QED

Theorem matchLengthRB'_correct:
  ∀rb split si li.
    WFrb rb ∧ split < rb.size ∧ split ≤ li ∧ si ≤ li ⇒
    matchLengthRB' (rb,split) si li =
    matchLength (DROP si $ list_of_ringBuffer rb) (DROP li $ list_of_ringBuffer rb)
Proof
  cheat
  (*\\
  recInduct matchLengthRB'_ind >> rw[] >>
  simp[Once matchLengthRB'_def] >> rw[] >> gs[] (* 3 *)
  >- (drule list_of_ringBuffer_LENGTH >>
      simp[DROP_LENGTH_TOO_LONG])
  >- (drule_then assume_tac list_of_ringBuffer_LENGTH >>
      ‘0 < rb.size’ by simp[] >>
      Cases_on ‘list_of_ringBuffer rb’ >> gs[] >>
      Cases_on ‘rbEL li rb’ >> gs[] >>
      gs[rbEL_EL] >>
      ‘h::t = (TAKE si (h::t)) ++ [x] ++ (DROP si t)’
        by (Cases_on ‘si’ >> gs[EL,ADD1] >>
            irule TAKE_EL_DROP >> simp[]) >>
      ‘DROP si (h::t) = [x] ++ DROP si t’ by simp[DROP_EL_CONS] >>
      ‘DROP li (h::t) = [x] ++ DROP li t’ by simp[DROP_EL_CONS] >>
      simp[])
  >-


  Induct_on ‘l’
  >- csimp[list_of_ringBuffer_nil] >>
     cheat
*)
QED


Theorem getMatch_nil2[simp]:
  getMatch s [] = (0,0)
Proof
  Cases_on ‘s’ >> simp[]
QED

Theorem getMatchWorks:
  ∀ bl bd. getMatch s l = (bl,bd) ⇒
           ((TAKE bl l) = (TAKE bl (DROP bd s)))
Proof
  Induct_on ‘s’
  >- simp[] >>
  Cases_on ‘l’ >> simp[] >>
  rename [‘getMatch s (l::ls)’] >>
  Cases_on ‘getMatch s (l::ls)’ >>
  gs[] >>
  rw[] >- (simp[] >>
           metis_tac[matchLengthWorks]) >>
  simp[]
QED


Theorem matches_alt:
  (len,dist) IN matches s l ⇒ TAKE len l = TAKE len $ DROP dist s
Proof simp[matches_def]
QED

Theorem matches_alt2:
  TAKE len l = TAKE len $ DROP dist s ⇒ (len,dist) IN matches s l
Proof simp[matches_def]
QED

Theorem getMatchMatches:
  getMatch s l IN matches s l
Proof
  simp[matches_def] >>
  Cases_on ‘getMatch s l’ >>
  metis_tac[matches_def, getMatchWorks]
QED


(* Theorem getMatchLongestMatches: *)
(*   ∀s t. getMatch s t IN longestMatches s t *)
(* Proof *)
(*   rw[longestMatches_def,matches_def] >> *)
(*   Cases_on ‘getMatch s t’ >> *)
(*   ‘(q,r) IN matches s t’ by metis_tac[getMatchMatches] >> *)
(*            completeInduct_on ‘q’ >> *)
(*   gs[matches_def] >> rw[LESS_OR_EQ]  *)

(* QED *)

Theorem matches_has_zeros:
  (0,a) IN matches s l
Proof simp[matches_def]
QED


Theorem backMatches_alt:
  (len,dist) IN backMatches s l ⇒ TAKE len l = TAKE len $ DROP (LENGTH s - dist) s
Proof simp[backMatches_def]
QED

Theorem backMatchesMatches:
  ∀s l len dist. (len,(LENGTH s - dist)) IN (matches s l) <=> (len,dist) IN (backMatches s l)
Proof
  rpt (strip_tac) >>
  eq_tac
  >- (
  simp[matches_def,backMatches_def] >>
  rw[] >> drule matches_alt >> rw[])
  >- (
  rw[] >> drule backMatches_alt >> rw[] >>
  simp[matches_def])
QED

Theorem matchLengthInBounds[simp]:
  ∀s l. matchLength s l ≤ LENGTH l ∧ matchLength s l ≤ LENGTH s
Proof
  Induct_on ‘l’ >> simp[] >>
  Cases_on ‘s’ >> simp[] >>
  rw[ADD1]
QED

Theorem getMatchInBounds:
  ∀len dist. getMatch s l = (len,dist) ⇒ dist + len ≤ LENGTH s
Proof
  Induct_on ‘s’ >> simp[] >>
  Cases_on ‘l’ >> simp[] >>
  pairarg_tac >> gs[] >> rw[ADD1] >> rw[]
QED

Theorem LZmatch_findsMatches:
  ∀ s l len dist.(LZmatch s l = SOME $ LenDist (len,dist)) ==> (len,dist) IN backMatches s l
Proof
  Cases_on ‘l’ >> simp[] >>
  rw[] >>
  rename [‘getMatch s (l::ls)’]  >>
  Cases_on ‘getMatch s (l::ls)’ >>
  rename [‘getMatch s (l::ls) = (len,dist)’] >> gs[] >>
  ‘(len,dist) ∈ matches s (l::ls)’ by metis_tac[getMatchMatches] >>
  simp[GSYM backMatchesMatches] >>
  ‘dist ≤ LENGTH s’ suffices_by (simp[] >> metis_tac[getMatchMatches]) >>
  drule getMatchInBounds >> simp[]
QED


Theorem LZinit_sameLength:
  ∀s. tripleLength $ LZinit s = LENGTH s
Proof
  Induct_on ‘s’ >- simp[tripleLength_def,LZinit_def] >>
  gs[tripleLength_def,LZinit_def] >>
  rw[MIN_DEF,LENGTH_TAKE_EQ]
QED


(* put into rich list theory *)
Theorem LASTN_NILL[simp]:
  ∀n. LASTN n [] = []
Proof simp[LASTN_def]
QED

Theorem LASTN_LASTN_SAME[simp]:
  ∀n l. LASTN n (LASTN n l) = LASTN n l
Proof
  rpt strip_tac >>
  Cases_on ‘n ≤ LENGTH l’
  >- (irule LASTN_LASTN >> simp[]) >>
  CCONTR_TAC >>
  gs[NOT_LESS_EQUAL,LASTN_def] >>
  ‘(LENGTH $ REVERSE l) = LENGTH l’ by simp[LENGTH_REVERSE] >>
  ‘LENGTH (TAKE n (REVERSE l)) = LENGTH l’ by simp[LENGTH_TAKE_EQ] >>
  simp[]
QED

Theorem LASTN_APPEND[simp]:
  ∀n s t. LASTN n (LASTN n s ⧺ t) = LASTN n (s ⧺ t)
Proof
  cheat
        (*
        rpt strip_tac >>
  Induct_on ‘s’ >> simp[] >>
  gs[LASTN_def] >> strip_tac >>
  Cases_on ‘n ≤ LENGTH t’
  >- gs[TAKE_APPEND1] >>
  gs[TAKE_APPEND2] >>
  Cases_on ‘n ≤ LENGTH s’
  >- (gs[TAKE_APPEND1] >> simp[TAKE_APPEND]) >>
  gs[TAKE_APPEND2] >> simp[TAKE_APPEND]
        *)
QED


Theorem resolveLenDist_thm[simp]:
  resolveLenDist t (l,d) = SOME s ⇒ s = TAKE l $ DROP (LENGTH t - d) t
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem resolveLenDistLength:
  resolveLenDist t (l,d) = SOME s ⇒ LENGTH s ≤ l
Proof
  rw[] >>
  ‘s = TAKE l $ DROP (LENGTH t - d) t’ by simp[] >> simp[] >>
  simp[LENGTH_TAKE_EQ]
QED

Theorem resolveLenDistBackMatch:
  ∀s t l d. resolveLenDist t (l,d) = SOME s ⇒ (l,d) ∈ backMatches s t
Proof
  cheat
(*  simp[backMatches_def] >>
  rpt strip_tac >>
  Cases_on ‘t’
  >- (rw[] >>
      Cases_on ‘s’ >> simp[] >>
      gs[resolveLenDist_def]) >>
  rename [‘resolveLenDist (t::ts) _’] >>
  Cases_on ‘s’ >> simp[] >>
  (*rename borks*)
  rename ‘SOME (s::ss)’ >>
  ‘LENGTH (s::ss) ≤ l’ by metis_tac[resolveLenDistLength] >>
  gs[resolveLenDist_def]*)
QED

Theorem LASTN_LENGTH_UB:
  LENGTH $ LASTN n s ≤ LENGTH s
Proof simp[LASTN_def,LENGTH_TAKE_EQ]
QED

Theorem getMatch_doesnt_lie:
  getMatch search (LAST32k buf) = (len,dist) ∧ ~(len<3) ∧ buf ≠ []
  ⇒ resolveLenDist buf (len, LENGTH (LAST32k buf) - dist) =
    SOME $ TAKE len search
Proof
  cheat
(*  rw[] >>
  ‘(len,dist) IN matches search (LAST32k buf)’ by metis_tac[getMatchMatches] >>
  gs[matches_def] >>
  Cases_on ‘buf’ >> simp[resolveLenDist_def]
  >- metis_tac[] >>
  rw[NOT_LESS]
  >- (
  irule LESS_EQ_TRANS >>
  irule_at Any LASTN_LENGTH_UB >>
  simp[])
  >- (
  drule getMatchInBounds >>
  rw[] >>
  ‘dist+len ≤ LENGTH (h::t)’ by metis_tac[LASTN_LENGTH_UB,LESS_EQ_TRANS] >>
  gs[])
  >- (
  drule getMatchInBounds >>
  rw[])
  >- (
  simp[LASTN_DROP_UNCOND,DROP_DROP_T] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[])*)
QED


Theorem LZdecompress_NIL:
  ∀s t. LZdecompress s t = [] ⇒ s = []
Proof
  Induct_on ‘t’
  >- simp[LZdecompress_def] >>
  Cases_on ‘s’ >> simp[] >>
  simp[LZdecompress_def] >>
  rpt strip_tac >>
  FIRST_X_ASSUM drule >>
  simp[AllCaseEqs ()]
QED

(* Theorem LZdecompress_NOT_NIL: *)
(*   ∀s h t. LZdecompress (h::t) s ≠ [] *)
(* Proof *)
(*   (* Induct using SNOC_INDUCT >- rw[Once LZdecompress_def] >> *) *)
(*   Induct >- rw[Once LZdecompress_def] >> *)
(*   CCONTR_TAC >> gs[] >> *)
(*   ‘(h'::t) = []’ by metis_tac[LZdecompress_NIL] >> *)
(*   metis_tac[NOT_CONS_NIL] *)
(* QED *)

Theorem isPREFIX_SAME[simp]:
  ∀a. isPREFIX a a
Proof rw[isPREFIX]
QED

(* Theorem LZdecompress_isPREFIX: *)
(*   ∀s t res. (LZdecompress s t = res) ⇒ isPREFIX s res *)
(* Proof *)
(*   Induct_on ‘t’ *)
(*   >- rw[Once LZdecompress_def] >> *)
(*   CASE_TAC *)
(*   >- ( *)
(*   ‘(h::s) = []’ by metis_tac[LZdecompress_NIL] >> *)
(*   rw[]) >> *)

Theorem LZ_inv_thm:
  ∀a b c a0. (b=[] ⇒ c=[]) ⇒ (a = LAST32k a0) ⇒ LZdecompress a0 (LZcompress a b c) = a0 ++ b ++ c
Proof
  cheat(*
        recInduct LZcompress_ind  >>  rpt strip_tac >>
  simp[Once LZcompress_def, Once LZdecompress_def]
  >- gs[]
  >- (Cases_on ‘getMatch (v8::v9) (LASTN 32768 a0)’ >> simp[] >>
      Cases_on ‘q<3’ >> simp[LZdecompress_def]
      >> gs[] >>
      CASE_TAC
      >- (drule_then drule getMatch_doesnt_lie >>
          impl_tac
          >- (rpt strip_tac >> gvs[getMatch_def])
          >- simp[]) >>
      gs[MAX_DEF] >>
      drule getMatch_doesnt_lie >> simp[] >>
      ‘getMatch (v8::v9) (LAST32k a0) ∈ matches (v8::v9) (LAST32k a0)’ by metis_tac[getMatchMatches] >>
      drule resolveLenDistBackMatch >>
      rw[] >>
      ‘a0 ≠ []’ by (CCONTR_TAC >> gvs[]) >>
      gs[backMatches_def,TAKE_TAKE_T]) >>
  Cases_on ‘getMatch (v10::v11) (LAST32k a0)’ >> simp[] >>
  Cases_on ‘q<3’ >> gvs[LZdecompress_def,MAX_DEF] >>
  CASE_TAC
  >- (‘resolveLenDist a0 (q, LENGTH (LAST32k a0) - r) = SOME $ TAKE q (v10::v11)’
        by (irule getMatch_doesnt_lie >> simp[] >> CCONTR_TAC >> gvs[]) >> gvs[])
  >- (drule getMatch_doesnt_lie >> simp[] >>
      impl_tac >- (CCONTR_TAC >> gvs[]) >>
      rw[]) *)
QED

Theorem LZ_inv'_thm:
  ∀s split bufSize lookSize. LZdecompress [] (LZcomp s split bufSize lookSize) = s
Proof
  cheat
QED

Theorem LZcompress_LENGTH:
  ∀s l r. LENGTH $ LZcompress s l r ≤ LENGTH l + LENGTH r
Proof
  cheat
  (*
        recInduct LZcompress_ind >> rpt strip_tac
  >- (simp[LZcompress_def])
  >- (simp[LZcompress_def])
  >- (simp[LZcompress_def] >>
      Cases_on ‘getMatch (v8::v9) search’ >> simp[] >>
      CASE_TAC >> simp[]
      >- gs[LENGTH_NIL]
      >- gs[LENGTH_NIL,NOT_LESS,MAX_DEF]
     )
  >- (simp[LZcompress_def] >>
      Cases_on ‘getMatch (v10::v11) search’ >> simp[] >>
      CASE_TAC >> simp[]
      >- gs[]
      >- gs[MAX_DEF,LENGTH_TAKE_EQ])
      *)
QED

Theorem LZcompress_LENGTH_NIL_REMAINDER:
  ∀s l. LENGTH $ LZcompress s l [] ≤ LENGTH l
Proof
  rpt strip_tac >>
  ‘LENGTH (LZcompress s l []) ≤ LENGTH l + LENGTH []’ suffices_by simp[] >>
  qspecl_then [‘s’,‘l’,‘[]’] MP_TAC LZcompress_LENGTH >>
  simp[]
QED

Theorem LZSS_compressLength:
  ∀s. LENGTH (LZSS_compress s) ≤ LENGTH s
Proof
  strip_tac >>
  simp[LZSS_compress_def,LZinit_def,MIN_DEF] >>
  rw[]
  >- (qspecl_then [‘[]’,‘TAKE 258 s’,‘DROP 258 s’] MP_TAC LZcompress_LENGTH >> simp[])
  >- (gs[DROP_LENGTH_NIL,NOT_LESS] >>
      metis_tac[LZcompress_LENGTH_NIL_REMAINDER])
QED


Theorem LZSS_decompressWindow:
  ∀s.LZSS_decompress(LZSS_compress s) = s
Proof
  strip_tac >> simp[LZSS_compress_def,LZSS_decompress_def,LZinit_def] >>
  simp[LZ_inv_thm]
QED


(* lookup data refinement *)

val _ = export_theory();
