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

EVAL “getMatch "hejsan" "ejsa"”;

Definition LZmatch_def[simp]:
  (LZmatch b [] = NONE) ∧
  (LZmatch buffer lookahead =
  let match = getMatch buffer lookahead
  in if FST match < 3                       (* This looks like LZSS and not LZ77 *)
     then SOME $ Lit (HD lookahead)
     else SOME $ LenDist (FST match, (LENGTH buffer - (SND match))))
End


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



EVAL “
 let
   s = "aabbccddeeffgghhiijjkkllmmnnooppaabbccddeeffgghhiijjkkllmmnnooppqqrrssttuuvvxxyyzz";
   dict = 32;
   look = 8;
   rb_size = dict + look;
   rb = empty_rb rb_size #" ";
   rb = rbAPPEND rb (TAKE rb_size s);
   rb = rbAPPEND rb (TAKE look (DROP rb_size s));
 in
   list_of_ringBuffer rb
     ”;


Definition matchLengthRB_def:
  (matchLengthRB rb si li :num =
   if rb.size ≤ li
   then 0
   else if rbEL si rb = rbEL li rb ∧ rbEL li rb ≠ NONE ∧ rbEL si rb ≠ NONE
   then 1 + (matchLengthRB rb (SUC si) (SUC li))
   else 0)
Termination
  WF_REL_TAC ‘measure (λ rb, si, li. rb.size - li)’
End

EVAL “
 let
   s = "aabbccddeeffgghhiijjkkllmmnnooppaabbccddeeffgghhiijjkkllmmnnooppqqrrssttuuvvxxyyzz";
   dict = 32;
   look = 8;
   rb_size = dict + look;
   rb = empty_rb rb_size #" ";
   rb = rbAPPEND rb (TAKE rb_size s);
   rb = rbAPPEND rb (TAKE look (DROP rb_size s));
 in
   matchLengthRB rb 2 34
     ”;


(* find the longest, right-most match *)
Definition getMatchRB_def[simp]:
  getMatchRB rb si li : num # num =
  if li < si + 2
  then (0,0)
  else
    let ml = matchLengthRB rb si li;
       (next_ml,next_md) = getMatchRB rb (SUC si) li
    in if next_ml < ml then (ml,0)
       else (next_ml,next_md+1)
Termination
  WF_REL_TAC ‘measure (λ rb, si, li. li - si + 2)’
End


EVAL “
 let
   s = "hej nej ja men ejej jomen vissthej nej ja men ejej jomen vissthej nej ja men ejej jomen vissthej nej ja men ejej jomen visst";
   dict = 40;
   look = 8;
   rb_size = dict + look;
   rb = empty_rb rb_size #" ";
   rb = rbAPPEND rb (TAKE rb_size s);
   rb = rbAPPEND rb (TAKE look (DROP rb_size s));
 in
  (rb, getMatchRB rb 0 (rb.size-look))
     ”;

Overload DICT_SIZE = “32 :num”
Overload LOOK_SIZE = “8 :num”

Overload DICTIONARY = “TAKE DICT_SIZE”
Overload LOOKAHEAD = “LASTN LOOK_SIZE”


Definition LZmatchRB_def[simp]:
  LZmatchRB rb li =
   let match = getMatchRB rb 0 li
   in if FST match < 3
      then
        case rbEL li rb of
          SOME a => SOME $ Lit a
        | NONE => NONE
      else SOME $ LenDist (FST match, (rb.size - LOOK_SIZE  - (SND match)))
End


EVAL “
 let
   s = "hej nej ja men ejej jomen vissthej nej ja men ejej jomen vissthej nej ja men ejej jomen vissthej nej ja men ejej jomen visst";
   dict = 40;
   look = 8;
   rb_size = dict + look;
   rb = empty_rb rb_size #" ";
   rb = rbAPPEND rb (TAKE rb_size s);
   rb = rbAPPEND rb (TAKE look (DROP rb_size s));
 in
  (list_of_ringBuffer rb, LZmatchRB rb (rb.size-look))
     ”;

(* new version which takes buffer size as a parameter and searches into lookahead

s: vår buffer ++ allt vi inte hanterat
split: hur långt vi kommit i s
bufsize: hur långt bak vi får titta
looksize: hur långt fram vi får titta *)

Definition LZinit:
  LZinit s =
  (rb_of_list (TAKE (DICT_SIZE + LOOK_SIZE) s), DROP (DICT_SIZE + LOOK_SIZE) s)
End

EVAL “LZinit "hej nej jag heter faktiskt inte ejnar jag heter gudrud hejsan nej hej"”;

Definition LZcompRB_def:
  LZcompRB rb s =
  if s = [] then [] (* Call LZend() *)
  else
    let match = LZmatchRB  rb (rb.size - LOOK_SIZE);
        len = case match of
              | NONE => 1
              | SOME $ LenDist (ml,_) => MAX ml 1
              | SOME $ Lit _ => 1;
        recurse = LZcompRB (rbAPPEND rb (TAKE len s)) (DROP len s);
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination

  WF_REL_TAC ‘measure $ λ(rb,s). LENGTH s’
  \\ rpt strip_tac
  \\ CASE_TAC
  \\ simp[]
  \\ Cases_on ‘s’


  \\ CASE_TAC
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

(* lookup data refinement *)

val _ = export_theory();
