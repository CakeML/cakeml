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


Datatype:
  LZSS = Lit 'a | LenDist (num # num)
End

Definition LZmatch_def[simp]:
  (LZmatch b [] = NONE) ∧
  (LZmatch buffer lookahead =
  let match = getMatch buffer lookahead
  in if FST match < 3                       (* This looks like LZSS and not LZ77 *)
     then SOME $ Lit (HD lookahead)
     else SOME $ LenDist (FST match, (LENGTH buffer - (SND match))))
End



(* new version which takes buffer size as a parameter and searches into lookahead

s: vår buffer ++ allt vi inte hanterat
split: hur långt vi kommit i s
bufsize: hur långt bak vi får titta
looksize: hur långt fram vi får titta *)

Definition LZcomp_def:
  LZcomp s split bufSize lookSize =
  if LENGTH s ≤ split ∨ s = [] ∨ bufSize = 0 ∨ lookSize = 0 then []
  else
    let match = LZmatch (TAKE split s) (TAKE lookSize (DROP split s));
        len = case match of
              | NONE => 1
              | SOME $ LenDist (ml,_) => MAX ml 1
              | SOME $ Lit _ => 1;
        bufDrop = (split + len) - bufSize;
        recurse = (LZcomp (DROP bufDrop s) (split + len - bufDrop) bufSize lookSize)
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

EVAL “LZcomp "hej jag heter heter jag nej heterogen" 0 258 258”;

(*
Definition LZSS_to_string_def:
  LZSS_to_string [] = [] ∧
  LZSS_to_string ((Lit a)::ss) =
  "0" ++ a::LZSS_to_string ss ∧
  LZSS_to_string ((LenDist (ml, md))::ss) =
  "1" ++ num_to_dec_string ml ++ num_to_dec_string md ++ LZSS_to_string ss
End

Definition string_to_LZSS_def:
  string_to_LZSS [] = [] ∧
  string_to_LZSS (a::ss) = if a = #"0" then Lit HD ss else if
                           End
*)

Definition LZSS_compress_def:
  LZSS_compress s = LZcomp s 0 258 258
End


(******************************************************
*****                                             *****
*****               Decopmression                 *****
*****                                             *****
******************************************************)

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

EVAL “LZSS_compress "hejsan jag heter bert ert ert ert jag har lagt en fjert "”;
EVAL “LZSS_decompress (LZSS_compress "hejsan jag heter bert ert ert ert jag har lagt en fjert ")”;


(******************************************************
*****                                             *****
*****              Main functions                 *****
*****                                             *****
******************************************************)

(*Definition LZSS_compress_main_def:
  LZSS_compress_main s =
  if LZSS_decompress (LZSS_compress s) = s
  then (Lit #"C")::(LZSS_compress s)
  else (Lit #"U")::s
End

Definition LZSS_decompress_main_def:
  LZSS_decompress_main s =
  if IS_PREFIX s (Lit #"C")
  then LZSS_decompress (DROP (LENGTH 1 s))
  else DROP 1 s
End

Theorem compress_main_inv:
 ∀s. LZSS_decompress_main (LZSS_compress_main s) = s
Proof
  REWRITE_TAC[decompress_main_def, compress_main_def]
  \\ strip_tac
  \\ CASE_TAC
  \\ simp[]
QED
*)

(****************************************
*****                              ******
*****       Used by theorems       ******
*****                              ******
****************************************)

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

(* lookup data refinement *)

val _ = export_theory();
