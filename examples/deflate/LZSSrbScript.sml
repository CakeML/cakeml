(*
Formalization written by Alexander Cox
*)

open preamble;

open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;

val _ = new_theory"LZSSrb";

Datatype:
  LZSS = Lit 'a | LenDist (num # num)
End

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

(* find the longest, right-most match *)
Definition getMatchRB_def[simp]:
  getMatchRB rb (si:num) (li:num) : num # num =
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
  LZinit s  =
  let
    rb = empty_rb (DICT_SIZE - LOOK_SIZE) #"0";
    rb = rbAPPEND rb (TAKE LOOK_SIZE s);
    s = DROP LOOK_SIZE s;
  in
    (rb, s)
End

EVAL “LZinit "hej nej jag heter faktiskt inte ejnar jag heter gudrud hejsan nej hej"”;

Definition LZcompRB_def:
  LZcompRB (rb : char ringBuffer) (s :string) =
  if LENGTH s = 0 then [] (* Call LZend() *)
  else
    let
      match = LZmatchRB  rb (rb.size - LOOK_SIZE);
      len = case match of
            | NONE => 1
            | SOME $ LenDist (ml,_) => MAX 1 ml
            | SOME $ Lit _ => 1;
      recurse = LZcompRB (rbAPPEND rb (TAKE len s)) (DROP len s);
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination
  WF_REL_TAC ‘measure $ λ(rb,s). LENGTH s’
  \\ rpt strip_tac
  \\ rpt (CASE_TAC \\ simp[])
End

(*
Definition LZcompRB_def:
  LZcompRB (rb : char ringBuffer) (s :string) look =
  if look ≤ 0 ∧ s = [] then []
  else
    let
      match = LZmatchRB  rb (rb.size - look);
      len = case match of
              NONE => 1
            | SOME $ LenDist (ml,_) => MAX 1 ml
            | SOME $ Lit _ => 1;
      recurse = if s = []
                then LZcompRB rb [] (look - len)
                else LZcompRB (rbAPPEND rb (TAKE len s)) (DROP len s) look;
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination

  WF_REL_TAC ‘measure $ λ(rb,s,look). look + LENGTH s’
  \\ rpt strip_tac
  \\ rpt (CASE_TAC \\ simp[])


         rw[]
  \\ Cases_on ‘s’
  \\ simp[]

End
*)

Definition LZSSRB_compress_def:
  LZSSRB_compress s =
  let
    (rb, remainder) = LZinit s
  in
    LZcompRB rb remainder
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

EVAL “LZSSRB_compress "hejsan hejsan hejsan jag heter bert ert ert ert jag har lagt en fjert"”;
EVAL “LZSS_decompress (LZSSRB_compress "hejsan jag heter bert ert ert ert jag har lagt en fjert")”;


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
