(*
Implementation of LZSS using ringbuffer
*)
Theory LZSSrb
Ancestors
  string list rich_list option pair arithmetic ringBuffer
Libs
  preamble


Datatype:
  LZSS = Lit 'a | LenDist (num # num)
End

Overload DICT_SIZE = “32768 :num”
Overload LOOK_SIZE = “258 :num”

Definition matchLengthRB_def:
  matchLengthRB rb si li split :num =
   if rb.size ≤ li ∨ split ≤ si
   then 0
   else if rbEL si rb = rbEL li rb ∧ rbEL li rb ≠ NONE ∧ rbEL si rb ≠ NONE
   then 1 + (matchLengthRB rb (SUC si) (SUC li) split)
   else 0
Termination
  WF_REL_TAC ‘measure (λ rb, si, li, split. MIN (rb.size - li) (split - si))’
  \\ simp[MIN_DEF]
End

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

Definition matchLength_def[simp]:
  (matchLength s [] :num = 0) ∧
  (matchLength [] l = 0) ∧
  (matchLength (s::ss) (l::ls) =
   if (s = l)
   then (1 + (matchLength ss ls))
   else 0)
End

Theorem matchLengthRB_correct:
  ∀rb si li.
    WFrb rb ∧ li < rb.size ∧ si ≤ li ⇒
    (matchLengthRB rb si li li =
    matchLength (DROP si $ list_of_ringBuffer rb) (DROP li $ list_of_ringBuffer rb))
Proof
cheat (*
        recInduct matchLengthRB_ind >> rw[] >>
  simp[Once matchLengthRB_def] >> rw[] >> gs[] (* 3 *)
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

(* find the longest, right-most match *)
Definition getMatchRB_def[simp]:
  getMatchRB rb (si:num) (li:num): num # num =
  if li <= si
  then (0,0)
  else
    let
      ml = matchLengthRB rb si li li;
      (next_ml,next_md) = getMatchRB rb (SUC si) li;
    in
      if next_ml < ml
      then (ml,0)
      else (next_ml,next_md+1)
Termination
  WF_REL_TAC ‘measure (λ rb, si, li. li - si)’
End

Definition LZmatchRB_def[simp]:
  LZmatchRB rb li =
   let match = getMatchRB rb 0 li
   in if FST match < 3 ∨ li = 0
      then
        case rbEL li rb of
          SOME a => SOME $ Lit a
        | NONE => NONE
      else SOME $ LenDist (FST match, (li  - (SND match)))
End

Definition LZinit:
  LZinit s  =
  let
    (dict, look) = (if LENGTH s ≤ LOOK_SIZE
                    then (0, LENGTH s)
                    else
                      if LENGTH s <= (LOOK_SIZE + DICT_SIZE)
                      then (LENGTH s - LOOK_SIZE, LOOK_SIZE)
                      else (DICT_SIZE, LOOK_SIZE));
    rb = empty_rb (dict + look) #"0";
    rb = rbAPPEND rb (TAKE look s);
    s = DROP look s;
  in
    (rb, s, look)
End

Definition LZcompRB_def:
  LZcompRB (rb : char ringBuffer) (s :string) look =
  if  look = 0 then []
  else
    let
      match = LZmatchRB  rb (rb.size - look);
      len = (case match of
               NONE => 1
             | SOME $ LenDist (ml,_) => MAX 1 ml
             | SOME $ Lit _ => 1);
      look = (case s of
                [] => look-len
              | _  => look);
      recurse = LZcompRB (rbAPPEND rb (TAKE len s)) (DROP len s) look;
    in case match of
       | NONE => recurse
       | SOME m => m::recurse
Termination
  WF_REL_TAC ‘measure $ λ(rb,s,look). look + LENGTH s’
  \\ rpt strip_tac
  \\ rpt (CASE_TAC \\ simp[])
End

Definition LZSSRB_compress_def:
  LZSSRB_compress s =
  let
    (rb, remainder, look) = LZinit s
  in
    LZcompRB rb remainder look
End

(*******************************************************
 *****                                             *****
 *****               Decopmression                 *****
 *****                                             *****
 *******************************************************)

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
