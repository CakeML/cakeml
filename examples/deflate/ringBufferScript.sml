(*
Implementation written by Alexander Cox
*)

open preamble;
open listTheory rich_listTheory  arithmeticTheory;

val _ = new_theory"ringBuffer";

(* a ringBuffer is a list with the current size and index of the start *)
(* do I need an end index, i.e. to avoid deletions *)
Datatype: ringBuffer = <| buffer : 'a list ;
                          size : num ;
                          start: num |>
End

Overload rbNIL = “λx. x.buffer = []”
Overload iMAX = “λx.LENGTH x.buffer”

(* Definitions for counting successors, predecessors and MOD with regards to the circular nature of the ring buffer  *)
Definition iSUC[simp]:
  iSUC rb i = (SUC i) MOD iMAX rb
End

Definition iPRE[simp]:
  iPRE rb i = PRE (iMAX rb + i) MOD iMAX rb
End

Definition iMOD[simp]:
  iMOD rb i = i MOD iMAX rb
End

Definition rbEL_def:
  rbEL n rb =
  if rbNIL rb ∨ rb.size ≤ n
  then NONE
  else oEL (iMOD rb (n+rb.start)) rb.buffer
End

Definition rbHD_def[simp]:
  rbHD rb = rbEL 0 rb
End

Definition rbTL_def[simp]:
  rbTL rb = rb with
               <| start := iMOD rb (rb.start + 1) ;
                  size := (rb.size - 1) |>
End

Theorem ADD1_MOD_LT:
  ∀x d. 0 < d ∧ (x + 1) MOD d < x MOD d ⇒ (x + 1) MOD d = 0
Proof
  rw[] >>
  ‘∃q r. q * d + r = x ∧ r < d’ by metis_tac[DIVISION] >>
  gvs[] >>
  ‘0 < d’ by simp[] >>
  ‘∃q r'. r + 1 = q * d + r' ∧ r' < d’ by metis_tac[DIVISION] >>
  gs[] >>
  ‘q=1’ suffices_by (strip_tac >> gs[]) >>
  ‘∀e. q ≠ 2 + e’ by (rpt strip_tac >> gvs[]) >>
  ‘q<2’ by (CCONTR_TAC >> gs[NOT_LESS,LESS_EQ_EXISTS]) >>
  ‘q≠0’ suffices_by simp[] >>
  strip_tac >> gvs[]
QED


Definition list_of_ringBuffer_def:
  list_of_ringBuffer rb =
  TAKE rb.size (DROP rb.start rb.buffer) ++
  TAKE ((rb.start + rb.size) - iMAX rb) rb.buffer
End

Theorem list_of_ringBuffer_size0:
  ∀rb. rb.size = 0 ⇒ rb.start ≤ rb.size ⇒ list_of_ringBuffer rb = []
Proof
  rw[list_of_ringBuffer_def]
QED

Definition WFrb_def:
  WFrb rb ⇔ rb.size ≤ iMAX rb ∧ rb.start < iMAX rb
End



Theorem list_of_ringBuffer_nil:
  WFrb rb ⇒ (list_of_ringBuffer rb = [] ⇔ rb.size = 0)
Proof
  rw[list_of_ringBuffer_def,EQ_IMP_THM,WFrb_def] >> gs[]
QED

Theorem TAKE_DROP_CONS_EL:
  TAKE n (DROP m l) = h::t ⇒ oEL m l = SOME h
Proof
  simp[oEL_EQ_EL] >>
  Cases_on ‘l’ >> simp[] >>
  Cases_on ‘n’ >> simp[] >>
  Cases_on ‘m’ >> simp[] >>
  rw[] >- (CCONTR_TAC >>
           gs[NOT_LESS] >>
           ‘DROP n t' = []’ by simp[] >>
           ‘TAKE (SUC n') (DROP n t') = []’ by simp[] >>
           metis_tac[NOT_CONS_NIL]) >>
  Cases_on ‘DROP n t'’ >> gs[] >>
  Cases_on ‘n < LENGTH t'’ >> gs[NOT_LESS,DROP_EL_CONS,DROP_LENGTH_TOO_LONG]
QED

Theorem list_of_ringBuffer_CONS:
  WFrb rb ⇒
  (list_of_ringBuffer rb = h::t ⇔
     0 < rb.size ∧ (rbHD rb) = SOME h ∧
     list_of_ringBuffer (rbTL rb) = t)
Proof
  simp[WFrb_def,list_of_ringBuffer_def,rbEL_def,rbHD_def,rbTL_def] >>
  Cases_on ‘rb.size’ >> simp[]
  >- (strip_tac >>
      ‘rb.start - iMAX rb = 0 ’ by simp[] >>
      simp[]) >>
  Cases_on ‘SUC n + rb.start < iMAX rb’
  >- (‘SUC n + rb.start - iMAX rb = 0’ by simp[] >> simp[] >>
      ‘SUC n + (rb.start + 1) - iMAX rb = 0’ by simp[] >> simp[] >>
      ‘LENGTH (TAKE (SUC n) (DROP rb.start rb.buffer)) ≤ LENGTH rb.buffer’ by simp[] >>
      ‘0 < LENGTH rb.buffer’ by simp[] >>
      simp[NOT_NIL_EQ_LENGTH_NOT_0] >>
      ‘SUC n + (rb.start + 1) ≤ iMAX rb’ by simp[SUB_EQ_0] >>
      rw[EQ_IMP_THM]
      >- (Cases_on ‘DROP rb.start rb.buffer’ >- gs[] >>
          simp[oEL_EQ_EL] >>
          ‘rb.start MOD SUC n < SUC n’ by simp[MOD_LESS] >> simp[] >>
          Cases_on ‘rb.start < SUC n’ >> gs[NOT_LESS]
          >> gs[DROP_CONS_EL])
      >- (Cases_on ‘DROP rb.start rb.buffer’ >- gs[] >>
          ‘DROP (rb.start +1) rb.buffer = t'’ by gs[DROP_EL_CONS] >>
          simp[] >>
          gvs[])
      >- gs[oEL_EQ_EL,DROP_EL_CONS]
     )
  >- (gs[NOT_LESS,oEL_EQ_EL] >>
      strip_tac >>
      rw[EQ_IMP_THM]
      >- (irule (iffLR $ GSYM NOT_NIL_EQ_LENGTH_NOT_0) >> simp[])
      >- (gs[DROP_EL_CONS,ADD1])
      >- (
       ‘∃ prefix suffix. rb.buffer = prefix ++ suffix ∧ rb.start = LENGTH prefix ’ by
          (qexistsl_tac [‘TAKE rb.start rb.buffer’,‘DROP rb.start rb.buffer’] >> simp[]) >>
       gs[DROP_LENGTH_APPEND] >>
       Cases_on ‘suffix’ >> gvs[] >>
       rename [‘LENGTH t ≤ n’] >>
       gs[ADD_CLAUSES] >>
       Cases_on ‘t = []’
       >- gs[ADD1,EL_APPEND] >>
       ‘0 < LENGTH t’ by
          (Cases_on`t`>>gvs[])>>
       gs[ADD1] >>
       ‘LENGTH prefix + 1 = LENGTH (prefix ++ [h])’ suffices_by simp[DROP_LENGTH_APPEND, Excl "LENGTH_APPEND"] >>
       simp[])
      >- (
       ‘∃ prefix suffix. rb.buffer = prefix ++ suffix ∧ rb.start = LENGTH prefix ’ by
          (qexistsl_tac [‘TAKE rb.start rb.buffer’,‘DROP rb.start rb.buffer’] >> simp[]) >>
       gs[DROP_LENGTH_APPEND] >>
       Cases_on ‘suffix’ >> gvs[] >>
       simp[EL_APPEND1,EL_APPEND2] >>
       gs[ADD_CLAUSES] >> gs[ADD1] >>
       Cases_on ‘t = []’ >> gs[] >>
       ‘0 < LENGTH t’ by
         (Cases_on`t`>>gvs[])>>
       simp[] >>
       ‘LENGTH prefix + 1 = LENGTH (prefix ++ [h])’ suffices_by simp[DROP_LENGTH_APPEND, Excl "LENGTH_APPEND"] >>
       simp[]))
QED

(* Theorem list_of_ringBuffer_eq_cons:
  ∀rb. WFrb rb ∧ 0 < rb.size ⇒ list_of_ringBuffer rb = THE $ rbEL 0 rb::(list_of_ringBuffer $ rbTL rb)
Proof
  rw[WFrb_def] >>
*)






Definition ringBuffer_of_list_def:
  ringBuffer_of_list l size start =
  <| buffer := l ;
     size := size ;
     start := start |>
End

Definition empty_rb_def:
  empty_rb size default = ringBuffer_of_list (GENLIST (λx. default) size) 0 0
End

Definition rb_of_list_def:
  rb_of_list l = ringBuffer_of_list l (LENGTH l) 0
End

Theorem list_of_ringBuffer_inv_thm:
  ∀l. list_of_ringBuffer $ rb_of_list l = l
Proof
  simp[ringBuffer_of_list_def,rb_of_list_def,list_of_ringBuffer_def]
QED

Theorem list_of_ringBuffer_LENGTH:
  WFrb rb ⇒ LENGTH $ list_of_ringBuffer rb = rb.size
Proof
  simp[list_of_ringBuffer_def] >>
  Cases_on ‘rb.size + rb.start < iMAX rb’ >>
  simp[] >>
  gs[NOT_LESS,WFrb_def] >>
  rpt strip_tac >>
  simp[LENGTH_TAKE_EQ]
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


Definition rbUPDATE_def:
  rbUPDATE e n rb =
  rb with buffer updated_by
     (LUPDATE e ((n+rb.start) MOD rb.size))
End

Definition rbUPDATEL_def:
  (rbUPDATEL [] n rb = rb) ∧
  (rbUPDATEL (s::ss) n rb = rbUPDATEL ss (SUC n) (rbUPDATE s n rb))
End

EVAL “rb_of_list [1;2;3;4;5;6]”;

EVAL “rbCONS 1 (empty_rb 4 0)”;

EVAL “rbCONS 9 (rb_of_list [1;2;3;4;5;6])”;

EVAL “rbAPPEND (empty_rb 4 0) [10;11]”;

EVAL “rbAPPEND_REVERSE (empty_rb 4 0) [10;11]”;

EVAL “rbPREPEND (empty_rb 4 0) [10;11]”;

EVAL “rbPREPEND_REVERSE (empty_rb 4 0) [10;11]”;


Definition rbCONS_def:
  rbCONS e rb =
  let index = iPRE rb rb.start
  in
    if rb.size < LENGTH rb.buffer
    then rb with <| buffer := (LUPDATE e index rb.buffer);
                    size := rb.size + 1;
                    start  := index |>
    else rb with <| buffer := (LUPDATE e index rb.buffer);
                    start  := index |>
End

Definition rbSNOC_def:
  rbSNOC e rb =
  if rb.size < LENGTH rb.buffer
  then let index = iMOD rb (rb.start + rb.size)
       in rb with
             <| buffer := LUPDATE e index rb.buffer;
                       size := rb.size + 1 |>
  else rb with <| buffer := LUPDATE e rb.start rb.buffer;
                  start := iSUC rb rb.start |>
End

Definition rbAPPEND_def:
  (rbAPPEND rb [] = rb) ∧
  (rbAPPEND rb (l::ls)  = (rbAPPEND (rbSNOC l rb) ls))
End

Theorem rbAPPEND_NIL[simp]:
  ∀rb. rbAPPEND rb [] = rb
Proof
  EVAL_TAC >> simp[]
QED

val ringBuffer_ce = theorem "ringBuffer_component_equality";

(* Theorem rbAPPEND_size: *)
(*         ∀rb l. (rbAPPEND rb l).size = rb.size *)
(* Proof *)
(*   Induct_on ‘l’ >> *)
(*   simp[rbAPPEND_def,rbSNOC_def] >> *)
(*   rw[] *)
(* QED *)

(* Theorem rbAPPEND_NIL_BUFFER[simp]: *)
(*   ∀rb l. (rb.buffer = [] ∧ LENGTH l ≤ rb.size ∧ rb.start = 0) ⇒ *)
(*          rbAPPEND rb l = rb with buffer := l *)
(* Proof *)
(*   Induct_on ‘l’ using SNOC_INDUCT  *)
(*   >- (simp[rbAPPEND_def] >> *)
(*       gvs[ringBuffer_ce]) >> *)
(*   Cases_on ‘rb’ >> *)
(*   gvs[rbAPPEND_def,ringBuffer_ce] >> *)
(*   simp[rbAPPEND_size] >> *)
(*   rw[] *)
(*   >- ( *)
(*   EVAL_TAC *)
(*   simp[rbAPPEND_def] *)



Definition rbAPPEND_REVERSE_def:
  (rbAPPEND_REVERSE rb [] = rb) ∧
  (rbAPPEND_REVERSE rb (l::ls)  = rbSNOC l (rbAPPEND_REVERSE rb ls))
End

Theorem rbAPPEND_REVERSE_NIL[simp]:
  ∀rb. rbAPPEND_REVERSE rb [] = rb
Proof EVAL_TAC >> simp[]
QED

Definition rbPREPEND_def:
  (rbPREPEND rb [] = rb) ∧
  (rbPREPEND rb (l::ls)  =
   rbCONS l (rbPREPEND rb ls))
End

Theorem rbPREPEND_NIL[simp]:
  ∀rb. rbPREPEND rb [] = rb
Proof EVAL_TAC >> simp[]
QED

Definition rbPREPEND_REVERSE_def:
  (rbPREPEND_REVERSE rb [] = rb) ∧
  (rbPREPEND_REVERSE rb (l::ls)  =
   (rbPREPEND_REVERSE (rbCONS l rb) ls))
End

Theorem rbPREPEND_REVERSE_NIL[simp]:
  ∀rb. rbPREPEND_REVERSE rb [] = rb
Proof EVAL_TAC >> simp[]
QED


val _ = export_theory();
