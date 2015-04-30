open HolKernel Parse boolLib bossLib;

val _ = new_theory "bc_compile";

open listTheory lcsymtacs wordsTheory integerTheory bytecodeTheory;

val inst_compile_def = Define `
  (inst_compile (i :num) (Stack Pop) = [(72w :word8); (88w :word8)]) /\
  (inst_compile i (Stack (Pops (k :num))) =
   if k < (268435456 :num) then
     [(77w :word8); (49w :word8); (255w :word8); (72w :word8); (129w
        :word8); (196w :word8);
      (w2w (n2w ((8 :num) * k) :word32) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (24 :num)) :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Stack (Load k)) =
   if k < (268435456 :num) then
     [(72w :word8); (80w :word8); (72w :word8); (139w :word8); (132w
        :word8); (36w :word8);
      (w2w (n2w ((8 :num) * k) :word32) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (24 :num)) :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Stack (Store k)) =
   if k < (268435456 :num) then
     [(72w :word8); (137w :word8); (132w :word8); (36w :word8);
      (w2w (n2w ((8 :num) * k) :word32) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((8 :num) * k) :word32) >>> (24 :num)) :word8); (72w
        :word8); (88w :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Stack Add) =
   [(72w :word8); (89w :word8); (72w :word8); (83w :word8); (187w
      :word8); (0w :word8); (0w :word8); (0w :word8); (0w :word8); (77w
      :word8); (139w :word8); (105w :word8); (56w :word8); (73w
      :word8); (255w :word8); (213w :word8); (72w :word8); (91w
      :word8)]) /\
  (inst_compile i (Stack Sub) =
   [(72w :word8); (89w :word8); (72w :word8); (135w :word8); (193w
      :word8); (72w :word8); (83w :word8); (187w :word8); (4w :word8);
    (0w :word8); (0w :word8); (0w :word8); (77w :word8); (139w :word8);
    (105w :word8); (56w :word8); (73w :word8); (255w :word8); (213w
      :word8); (72w :word8); (91w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i (Stack Mult) =
   [(72w :word8); (89w :word8); (72w :word8); (83w :word8); (187w
      :word8); (16w :word8); (0w :word8); (0w :word8); (0w :word8);
    (77w :word8); (139w :word8); (105w :word8); (56w :word8); (73w
      :word8); (255w :word8); (213w :word8); (72w :word8); (91w
      :word8)]) /\
  (inst_compile i (Stack Div) =
   [(72w :word8); (89w :word8); (72w :word8); (135w :word8); (193w
      :word8); (72w :word8); (83w :word8); (187w :word8); (20w :word8);
    (0w :word8); (0w :word8); (0w :word8); (77w :word8); (139w :word8);
    (105w :word8); (56w :word8); (73w :word8); (255w :word8); (213w
      :word8); (72w :word8); (91w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i (Stack Mod) =
   [(72w :word8); (89w :word8); (72w :word8); (135w :word8); (193w
      :word8); (72w :word8); (83w :word8); (187w :word8); (24w :word8);
    (0w :word8); (0w :word8); (0w :word8); (77w :word8); (139w :word8);
    (105w :word8); (56w :word8); (73w :word8); (255w :word8); (213w
      :word8); (72w :word8); (91w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i (Stack Less) =
   [(72w :word8); (89w :word8); (72w :word8); (135w :word8); (193w
      :word8); (72w :word8); (83w :word8); (187w :word8); (8w :word8);
    (0w :word8); (0w :word8); (0w :word8); (77w :word8); (139w :word8);
    (105w :word8); (56w :word8); (73w :word8); (255w :word8); (213w
      :word8); (72w :word8); (91w :word8); (72w :word8); (247w :word8);
    (216w :word8); (72w :word8); (131w :word8); (192w :word8); (42w
      :word8)]) /\
  (inst_compile i (Stack Equal) =
   [(72w :word8); (89w :word8); (77w :word8); (49w :word8); (255w
      :word8); (77w :word8); (139w :word8); (121w :word8); (64w
      :word8); (73w :word8); (255w :word8); (215w :word8)]) /\
  (inst_compile i (Stack IsBlock) =
   [(72w :word8); (169w :word8); (1w :word8); (0w :word8); (0w :word8);
    (0w :word8); (72w :word8); (117w :word8); (16w :word8); (76w
      :word8); (139w :word8); (248w :word8); (73w :word8); (247w
      :word8); (215w :word8); (73w :word8); (247w :word8); (199w
      :word8); (2w :word8); (0w :word8); (0w :word8); (0w :word8); (72w
      :word8); (235w :word8); (11w :word8); (76w :word8); (139w
      :word8); (120w :word8); (1w :word8); (73w :word8); (247w :word8);
    (199w :word8); (7w :word8); (0w :word8); (0w :word8); (0w :word8);
    (72w :word8); (117w :word8); (8w :word8); (184w :word8); (38w
      :word8); (0w :word8); (0w :word8); (0w :word8); (72w :word8);
    (235w :word8); (5w :word8); (184w :word8); (42w :word8); (0w
      :word8); (0w :word8); (0w :word8)]) /\
  (inst_compile i (Stack (TagEq k)) =
   if k < (268435456 :num) then
     [(72w :word8); (49w :word8); (201w :word8); (129w :word8); (193w
        :word8); (w2w (n2w ((4 :num) * k) :word32) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (24 :num)) :word8); (72w
        :word8); (169w :word8); (1w :word8); (0w :word8); (0w :word8);
      (0w :word8); (72w :word8); (117w :word8); (7w :word8); (72w
        :word8); (131w :word8); (232w :word8); (2w :word8); (72w
        :word8); (235w :word8); (14w :word8); (72w :word8); (139w
        :word8); (64w :word8); (1w :word8); (72w :word8); (37w :word8);
      (255w :word8); (255w :word8); (0w :word8); (0w :word8); (72w
        :word8); (193w :word8); (232w :word8); (2w :word8); (72w
        :word8); (57w :word8); (200w :word8); (72w :word8); (117w
        :word8); (8w :word8); (184w :word8); (38w :word8); (0w :word8);
      (0w :word8); (0w :word8); (72w :word8); (235w :word8); (5w
        :word8); (184w :word8); (42w :word8); (0w :word8); (0w :word8);
      (0w :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Stack El) =
   [(72w :word8); (89w :word8); (72w :word8); (139w :word8); (68w
      :word8); (65w :word8); (9w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i (Stack LengthBlock) =
   [(72w :word8); (169w :word8); (1w :word8); (0w :word8); (0w :word8);
    (0w :word8); (72w :word8); (117w :word8); (13w :word8); (72w
      :word8); (184w :word8); (0w :word8); (0w :word8); (0w :word8);
    (0w :word8); (0w :word8); (0w :word8); (0w :word8); (0w :word8);
    (72w :word8); (235w :word8); (12w :word8); (72w :word8); (139w
      :word8); (64w :word8); (1w :word8); (72w :word8); (193w :word8);
    (232w :word8); (16w :word8); (72w :word8); (193w :word8); (224w
      :word8); (2w :word8)]) /\
  (inst_compile i (Stack (Cons (tag :num))) =
   if tag < (4096 :num) then
     [(72w :word8); (131w :word8); (248w :word8); (0w :word8); (72w
        :word8); (116w :word8); (111w :word8); (72w :word8); (169w
        :word8); (3w :word8); (0w :word8); (0w :word8); (0w :word8);
      (72w :word8); (117w :word8); (9w :word8); (72w :word8); (61w
        :word8); (0w :word8); (0w :word8); (2w :word8); (0w :word8);
      (72w :word8); (114w :word8); (4w :word8); (73w :word8); (255w
        :word8); (97w :word8); (40w :word8); (76w :word8); (139w
        :word8); (240w :word8); (73w :word8); (209w :word8); (230w
        :word8); (73w :word8); (131w :word8); (198w :word8); (8w
        :word8); (76w :word8); (139w :word8); (255w :word8); (73w
        :word8); (41w :word8); (247w :word8); (77w :word8); (57w
        :word8); (247w :word8); (115w :word8); (7w :word8); (77w
        :word8); (139w :word8); (105w :word8); (48w :word8); (73w
        :word8); (255w :word8); (213w :word8); (65w :word8); (190w
        :word8); (w2w (n2w tag :word32) :word8);
      (w2w ((n2w tag :word32) >>> (8 :num)) :word8);
      (w2w ((n2w tag :word32) >>> (16 :num)) :word8);
      (w2w ((n2w tag :word32) >>> (24 :num)) :word8); (73w :word8);
      (193w :word8); (230w :word8); (4w :word8); (76w :word8); (139w
        :word8); (248w :word8); (73w :word8); (193w :word8); (231w
        :word8); (14w :word8); (77w :word8); (1w :word8); (254w
        :word8); (77w :word8); (139w :word8); (254w :word8); (73w
        :word8); (193w :word8); (239w :word8); (16w :word8); (72w
        :word8); (88w :word8); (72w :word8); (131w :word8); (239w
        :word8); (8w :word8); (72w :word8); (137w :word8); (71w
        :word8); (1w :word8); (73w :word8); (255w :word8); (207w
        :word8); (73w :word8); (131w :word8); (255w :word8); (0w
        :word8); (72w :word8); (117w :word8); (236w :word8); (72w
        :word8); (131w :word8); (239w :word8); (8w :word8); (76w
        :word8); (137w :word8); (119w :word8); (1w :word8); (72w
        :word8); (139w :word8); (199w :word8); (72w :word8); (235w
        :word8); (5w :word8); (184w :word8);
      (w2w (n2w ((4 :num) * tag + (2 :num)) :word32) :word8);
      (w2w ((n2w ((4 :num) * tag + (2 :num)) :word32) >>> (8 :num)) :
         word8);
      (w2w ((n2w ((4 :num) * tag + (2 :num)) :word32) >>> (16 :num)) :
         word8);
      (w2w ((n2w ((4 :num) * tag + (2 :num)) :word32) >>> (24 :num)) :
         word8); (77w :word8); (49w :word8); (255w :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Stack (PushInt (j :int))) =
   if (Num (ABS j) :num) < (268435456 :num) then
     if j < (0 :int) then
       [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]
     else
       [(72w :word8); (80w :word8); (72w :word8); (49w :word8); (192w
          :word8); (5w :word8);
        (w2w (n2w ((4 :num) * (Num j :num)) :word32) :word8);
        (w2w ((n2w ((4 :num) * (Num j :num)) :word32) >>> (8 :num)) :
           word8);
        (w2w ((n2w ((4 :num) * (Num j :num)) :word32) >>> (16 :num)) :
           word8);
        (w2w ((n2w ((4 :num) * (Num j :num)) :word32) >>> (24 :num)) :
           word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i LengthByte =
   [(72w :word8); (139w :word8); (64w :word8); (1w :word8); (72w
      :word8); (193w :word8); (232w :word8); (11w :word8); (72w
      :word8); (131w :word8); (232w :word8); (32w :word8)]) /\
  (inst_compile i Length =
   [(72w :word8); (139w :word8); (64w :word8); (1w :word8); (72w
      :word8); (193w :word8); (232w :word8); (14w :word8)]) /\
  (inst_compile i (Jump (Addr (l :num))) =
   if l < (268435456 :num) then
     if i < (268435456 :num) then
       [(72w :word8); (233w :word8);
        (w2w
           ((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
              :word32)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (8 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (16 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (24 :num)) :word8)]
     else
       [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
          :word8); (192w :word8)]
   else
     [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
        :word8); (192w :word8)]) /\
  (inst_compile i (JumpIf (Addr l)) =
   if l < (268435456 :num) then
     if i < (268435456 :num) then
       [(72w :word8); (131w :word8); (248w :word8); (42w :word8); (72w
          :word8); (88w :word8); (15w :word8); (133w :word8);
        (w2w
           ((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (12w
              :word32)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (12w
               :word32)) >>> (8 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (12w
               :word32)) >>> (16 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (12w
               :word32)) >>> (24 :num)) :word8)]
     else
       [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
          :word8); (192w :word8); (255w :word8); (192w :word8); (255w
          :word8); (192w :word8); (255w :word8); (192w :word8)]
   else
     [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
        :word8); (192w :word8); (255w :word8); (192w :word8); (255w
        :word8); (192w :word8); (255w :word8); (192w :word8)]) /\
  (inst_compile i (Call (Addr l)) =
   if l < (268435456 :num) then
     if i < (268435456 :num) then
       [(72w :word8); (232w :word8);
        (w2w
           ((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
              :word32)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (8 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (16 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (6w
               :word32)) >>> (24 :num)) :word8)]
     else
       [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
          :word8); (192w :word8)]
   else
     [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
        :word8); (192w :word8)]) /\
  (inst_compile i (PushPtr (Addr l)) =
   if l < (268435456 :num) then
     if i < (268435456 :num) then
       [(72w :word8); (80w :word8); (72w :word8); (232w :word8); (0w
          :word8); (0w :word8); (0w :word8); (0w :word8); (72w :word8);
        (88w :word8); (72w :word8); (5w :word8);
        (w2w
           ((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (8w
              :word32)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (8w
               :word32)) >>> (8 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (8w
               :word32)) >>> (16 :num)) :word8);
        (w2w
           (((n2w ((2 :num) * l) :word32) - (n2w i :word32) - (8w
               :word32)) >>> (24 :num)) :word8)]
     else
       [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
          :word8); (192w :word8); (255w :word8); (192w :word8); (255w
          :word8); (192w :word8); (255w :word8); (192w :word8); (255w
          :word8); (192w :word8); (255w :word8); (192w :word8)]
   else
     [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
        :word8); (192w :word8); (255w :word8); (192w :word8); (255w
        :word8); (192w :word8); (255w :word8); (192w :word8); (255w
        :word8); (192w :word8); (255w :word8); (192w :word8)]) /\
  (inst_compile i (Jump (Lab (v0 :num))) =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
      :word8); (192w :word8)]) /\
  (inst_compile i (JumpIf (Lab (v1 :num))) =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
      :word8); (192w :word8); (255w :word8); (192w :word8); (255w
      :word8); (192w :word8); (255w :word8); (192w :word8)]) /\
  (inst_compile i (Call (Lab (v2 :num))) =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
      :word8); (192w :word8)]) /\
  (inst_compile i (PushPtr (Lab (v3 :num))) =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8); (255w
      :word8); (192w :word8); (255w :word8); (192w :word8); (255w
      :word8); (192w :word8); (255w :word8); (192w :word8); (255w
      :word8); (192w :word8); (255w :word8); (192w :word8)]) /\
  (inst_compile i CallPtr =
   [(72w :word8); (139w :word8); (200w :word8); (72w :word8); (88w
      :word8); (72w :word8); (255w :word8); (209w :word8)]) /\
  (inst_compile i Return = [(72w :word8); (195w :word8)]) /\
  (inst_compile i Deref =
   [(72w :word8); (89w :word8); (72w :word8); (139w :word8); (68w
      :word8); (65w :word8); (9w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i Ref =
   [(72w :word8); (89w :word8); (72w :word8); (169w :word8); (3w
      :word8); (0w :word8); (0w :word8); (0w :word8); (72w :word8);
    (117w :word8); (9w :word8); (72w :word8); (61w :word8); (0w
      :word8); (0w :word8); (2w :word8); (0w :word8); (72w :word8);
    (114w :word8); (4w :word8); (73w :word8); (255w :word8); (97w
      :word8); (40w :word8); (76w :word8); (139w :word8); (240w
      :word8); (73w :word8); (209w :word8); (230w :word8); (73w
      :word8); (131w :word8); (198w :word8); (8w :word8); (76w :word8);
    (139w :word8); (255w :word8); (73w :word8); (41w :word8); (247w
      :word8); (77w :word8); (57w :word8); (247w :word8); (115w
      :word8); (7w :word8); (77w :word8); (139w :word8); (105w :word8);
    (48w :word8); (73w :word8); (255w :word8); (213w :word8); (76w
      :word8); (139w :word8); (240w :word8); (73w :word8); (193w
      :word8); (230w :word8); (14w :word8); (73w :word8); (131w
      :word8); (198w :word8); (1w :word8); (77w :word8); (139w :word8);
    (254w :word8); (73w :word8); (193w :word8); (239w :word8); (16w
      :word8); (73w :word8); (131w :word8); (255w :word8); (0w :word8);
    (72w :word8); (116w :word8); (14w :word8); (73w :word8); (255w
      :word8); (207w :word8); (72w :word8); (131w :word8); (239w
      :word8); (8w :word8); (72w :word8); (137w :word8); (79w :word8);
    (1w :word8); (72w :word8); (235w :word8); (235w :word8); (72w
      :word8); (131w :word8); (239w :word8); (8w :word8); (76w :word8);
    (137w :word8); (119w :word8); (1w :word8); (72w :word8); (139w
      :word8); (199w :word8)]) /\
  (inst_compile i Update =
   [(72w :word8); (89w :word8); (72w :word8); (90w :word8); (72w
      :word8); (137w :word8); (68w :word8); (74w :word8); (9w :word8);
    (72w :word8); (88w :word8); (77w :word8); (49w :word8); (255w
      :word8)]) /\
  (inst_compile i (Galloc k) =
   [(73w :word8); (131w :word8); (199w :word8); (0w :word8)]) /\
  (inst_compile i (Gread k) =
   if k < (10000 :num) then
     [(72w :word8); (80w :word8); (72w :word8); (139w :word8); (203w
        :word8); (72w :word8); (49w :word8); (192w :word8); (5w
        :word8); (0w :word8); (0w :word8); (0w :word8); (0w :word8);
      (72w :word8); (139w :word8); (68w :word8); (65w :word8); (9w
        :word8); (72w :word8); (139w :word8); (200w :word8); (72w
        :word8); (49w :word8); (192w :word8); (5w :word8);
      (w2w (n2w ((4 :num) * k) :word32) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (24 :num)) :word8); (72w
        :word8); (139w :word8); (68w :word8); (65w :word8); (9w
        :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i (Gupdate k) =
   if k < (10000 :num) then
     [(72w :word8); (80w :word8); (72w :word8); (139w :word8); (203w
        :word8); (72w :word8); (49w :word8); (192w :word8); (5w
        :word8); (0w :word8); (0w :word8); (0w :word8); (0w :word8);
      (72w :word8); (139w :word8); (68w :word8); (65w :word8); (9w
        :word8); (72w :word8); (139w :word8); (208w :word8); (72w
        :word8); (49w :word8); (201w :word8); (72w :word8); (129w
        :word8); (193w :word8);
      (w2w (n2w ((4 :num) * k) :word32) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (8 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (16 :num)) :word8);
      (w2w ((n2w ((4 :num) * k) :word32) >>> (24 :num)) :word8); (72w
        :word8); (88w :word8); (72w :word8); (137w :word8); (68w
        :word8); (74w :word8); (9w :word8); (72w :word8); (88w :word8)]
   else [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i PopExc =
   [(73w :word8); (129w :word8); (235w :word8); (8w :word8); (0w
      :word8); (0w :word8); (0w :word8); (73w :word8); (139w :word8);
    (227w :word8); (73w :word8); (91w :word8)]) /\
  (inst_compile i PushExc =
   [(72w :word8); (80w :word8); (73w :word8); (139w :word8); (195w
      :word8); (76w :word8); (139w :word8); (220w :word8)]) /\
  (inst_compile i (Label l) = ([] :word8 list)) /\
  (inst_compile i Tick =
   [(73w :word8); (131w :word8); (199w :word8); (0w :word8)]) /\
  (inst_compile i Print =
   [(77w :word8); (49w :word8); (255w :word8); (77w :word8); (139w
      :word8); (121w :word8); (72w :word8); (73w :word8); (255w
      :word8); (215w :word8); (72w :word8); (88w :word8)]) /\
  (inst_compile i (PrintC (c :char)) =
   [(77w :word8); (139w :word8); (185w :word8); (144w :word8); (0w
      :word8); (0w :word8); (0w :word8); (77w :word8); (133w :word8);
    (255w :word8); (72w :word8); (116w :word8); (52w :word8); (72w
      :word8); (80w :word8); (72w :word8); (81w :word8); (72w :word8);
    (82w :word8); (72w :word8); (83w :word8); (72w :word8); (86w
      :word8); (72w :word8); (87w :word8); (73w :word8); (80w :word8);
    (73w :word8); (81w :word8); (73w :word8); (82w :word8); (73w
      :word8); (83w :word8); (191w :word8); (n2w (ORD c) :word8); (0w
      :word8); (0w :word8); (0w :word8); (73w :word8); (139w :word8);
    (65w :word8); (24w :word8); (72w :word8); (255w :word8); (208w
      :word8); (73w :word8); (91w :word8); (73w :word8); (90w :word8);
    (73w :word8); (89w :word8); (73w :word8); (88w :word8); (72w
      :word8); (95w :word8); (72w :word8); (94w :word8); (72w :word8);
    (91w :word8); (72w :word8); (90w :word8); (72w :word8); (89w
      :word8); (72w :word8); (88w :word8); (77w :word8); (49w :word8);
    (255w :word8)]) /\
  (inst_compile i (Stop T) =
   [(72w :word8); (80w :word8); (77w :word8); (49w :word8); (255w
      :word8); (184w :word8); (38w :word8); (0w :word8); (0w :word8);
    (0w :word8); (77w :word8); (139w :word8); (169w :word8); (136w
      :word8); (0w :word8); (0w :word8); (0w :word8); (73w :word8);
    (255w :word8); (229w :word8)]) /\
  (inst_compile i (Stop F) =
   [(72w :word8); (80w :word8); (77w :word8); (49w :word8); (255w
      :word8); (184w :word8); (42w :word8); (0w :word8); (0w :word8);
    (0w :word8); (77w :word8); (139w :word8); (169w :word8); (136w
      :word8); (0w :word8); (0w :word8); (0w :word8); (73w :word8);
    (255w :word8); (229w :word8)]) /\
  (inst_compile i RefByte =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i DerefByte =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i UpdateByte =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8)]) /\
  (inst_compile i PrintWord8 =
   [(73w :word8); (255w :word8); (97w :word8); (40w :word8)])`;

val inst_length_def = Define `
  inst_length bc = LENGTH (inst_compile 0 bc)`;

val bc_compile_def = zDefine `
  (bc_compile i [] = []) /\
  (bc_compile i (b::bs) = inst_compile i b ++ bc_compile (i + inst_length b) bs)`;

val bc_compile_rev_def = Define `
  (bc_compile_rev i [] res = res) /\
  (bc_compile_rev i (b::bs) res =
     let c = inst_compile i b in
       bc_compile_rev (i + LENGTH c) bs (REVERSE c ++ res))`;

val LENGTH_IF = prove(
  ``LENGTH (if b then xs else ys) = if b then LENGTH xs else LENGTH ys``,
  SRW_TAC [] []);

val IF_AND = prove(
  ``(if (b1 /\ b2) then c else d) =
    if b1 then (if b2 then c else d) else d``,
  SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val APPEND_IF = prove(
  ``(if b then xs else ys) ++ zs = if b then xs ++ zs else ys ++ zs:'a list``,
  SRW_TAC [] []);

val REVERSE_IF = prove(
  ``REVERSE (if b then xs else ys) =
    if b then REVERSE xs else REVERSE ys``,
  SRW_TAC [] []);

val bc_compile_rev_eval =
  ([],``!b. bc_compile_rev i (b::bs) res =
          let c = inst_compile i b in
            bc_compile_rev (i + LENGTH c) bs (REVERSE c ++ res)``)
  |> (Cases \\ TRY (Cases_on `b'`) \\ TRY (Cases_on `l`)) |> fst
  |> map (SIMP_RULE std_ss [LET_DEF] o REWRITE_CONV [bc_compile_rev_def] o snd)
  |> (fn thms => LIST_CONJ (SPEC_ALL (CONJUNCT1 bc_compile_rev_def)::thms))
  |> SIMP_RULE std_ss [inst_compile_def,LET_DEF,APPEND,LENGTH,
       REVERSE_DEF,LENGTH_IF,REVERSE_IF]
  |> REWRITE_RULE [APPEND_IF,APPEND,IF_AND]
  |> SIMP_RULE std_ss []
  |> REWRITE_RULE [GSYM IF_AND]

val _ = save_thm("bc_compile_rev_eval",bc_compile_rev_eval);

val LENGTH_inst_compile_IGNORE = prove(
  ``!i n. LENGTH (inst_compile n i) = LENGTH (inst_compile 0 i)``,
  Cases \\ TRY (Cases_on `b`)  \\ TRY (Cases_on `l`)
  \\ EVAL_TAC \\ SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC);

val bc_compile_ALT = store_thm("bc_compile_ALT",
  ``!b. bc_compile i (b::bs) =
          let c = inst_compile i b in c ++ bc_compile (i + LENGTH c) bs``,
  SIMP_TAC std_ss [bc_compile_def,LET_DEF,inst_length_def,
    LENGTH_inst_compile_IGNORE]);

val bc_compile_rev_thm = prove(
  ``!bs i res. bc_compile_rev i bs res = REVERSE (bc_compile i bs) ++ res``,
  Induct THEN1 (SRW_TAC [] [bc_compile_def,bc_compile_rev_def])
  \\ SRW_TAC [] [bc_compile_ALT,bc_compile_rev_def] \\ SRW_TAC [] []);

val bc_compile_rev_thm = store_thm("bc_compile_rev_thm",
  ``!bs i. bc_compile i bs = REVERSE (bc_compile_rev i bs [])``,
  SRW_TAC [] [bc_compile_rev_thm]);

val _ = computeLib.add_persistent_funs
          ["bc_compile_rev_eval",
           "bc_compile_rev_thm"];

val _ = export_theory();
