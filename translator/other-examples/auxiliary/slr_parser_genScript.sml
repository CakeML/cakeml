(*
  The following definitions are from HOL4 sources found on Aditi
  Barthwal's webpage: http://users.cecs.anu.edu.au/~aditi/
  Her definitions are reproduced below so that we can try our
  hol2miniml translator on them.
*)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "slr_parser_gen";
open arithmeticTheory listTheory combinTheory stringTheory;

val push_def = Define `push l e = e::l`;

Definition pop_def:
  (pop [] _ = []) /\
  (pop (h::t) n = if (n = 0) then (h::t) else pop t (n-1))
End

val take1_def = tDefine "take1" `
  (take1 0 [] = []) /\
  (take1 n (x::xs) = (if n=0 then [] else x::take1 (n - 1) xs))`
  (WF_REL_TAC (`measure (\(n,l).LENGTH l)`) THEN SRW_TAC [] []);

Definition take_def:
  (take n l = if (LENGTH l >= n) then SOME (take1 n l)
                                 else NONE)
End

Datatype:
  symbol = TS string | NTS string
End

Definition isNonTmnlSym:
  (isNonTmnlSym (NTS _) = T) /\
  (isNonTmnlSym _ = F)
End

val sym2Str = Define `(sym2Str (TS s) = s) /\ (sym2Str (NTS s) = s)`;

Datatype:
  rule = rule string (symbol list)
End

val ruleRhs = Define `ruleRhs (rule l r) = r`;
val ruleLhs = Define `ruleLhs (rule l r) = l`;

Datatype:
  ptree = Leaf string | Node string (ptree list)
End

Datatype:
  grammar = G (rule list) string
End

Datatype:
  item = item string (symbol list # symbol list)
End

Type state = ``:item list``

Datatype:
  action = REDUCE rule | GOTO state | NA
End

Definition ptree2Sym:
  (ptree2Sym (Node nt ptl) = NTS nt) /\
  (ptree2Sym (Leaf tm) = TS tm)
End

Definition buildTree:
  (buildTree p r =
     let s = take (LENGTH r) (MAP (ptree2Sym o SND) p) in
       if s = NONE then
         NONE
       else if r = THE s then
         take (LENGTH r) (MAP SND p)
       else
         NONE)
End

Definition addRule:
  (addRule p (rule l r) =
         let x =  buildTree p (REVERSE r) in
              if (x = NONE) then NONE
              else SOME (Node l (REVERSE (THE x))))
End

Definition findItemInRules:
  (findItemInRules (item l1 (r1,[])) [] = F) /\
  (findItemInRules (item l1 (r1,[])) ((rule l2 r2)::rst) = T) /\
  (findItemInRules (item l1 (r1,[])) (_::rst) = findItemInRules (item l1 (r1,[])) rst) /\
  (findItemInRules _ _ = F)
End

val itemEqRuleList_defn = tDefine "itemEqRuleList" `
  (itemEqRuleList [] [] = T) /\
  (itemEqRuleList [] _ = T) /\
  (itemEqRuleList _ [] = F) /\
  (itemEqRuleList l1 l2 =
     if ~(LENGTH l1 = LENGTH l2) then F else
       if (findItemInRules (HD l1) l2) then itemEqRuleList (TL l1) l2 else F)`
  (WF_REL_TAC (`measure (\(l1,l2).LENGTH l1)`) THEN SRW_TAC [] [])

Definition getState:
   getState (sg,red) (itl:item list) sym =
      let newitl = sg itl sym and rl = red itl (sym2Str sym) in
        case (newitl,rl) of
          ([],[]) => NA
        | ([],y::ys) => if LENGTH rl = 1 then REDUCE (HD rl) else NA
        | (x::xs,[]) => GOTO newitl
        | (x::xs,y'::ys') =>
            if itemEqRuleList (x::xs) (y'::ys') then
              REDUCE (HD rl)
            else
              NA
End

val stackSyms = Define `stackSyms stl = (REVERSE (MAP FST (MAP FST stl)))`

Definition exitCond:
  exitCond (eof,oldSym)  (inp,stl,csl) =
    (~(stl=([]:((symbol # state) # ptree) list)) /\
     (stackSyms stl = [oldSym]) /\
     (inp = [TS eof]))
End

Definition init:
  init inis sl =  (sl,([]:((symbol# state) # ptree) list),[inis])
End

Definition doReduce:
  doReduce m ((sym::rst), os, ((s, itl)::rem)) ru =
     if isNonTmnlSym sym then
       NONE
     else
       (let l = ruleLhs ru and r = ruleRhs ru in
        let ptree = addRule os ru
        in
          case ptree of
            NONE => NONE
          | SOME p =>
              (let newStk = pop os (LENGTH r) in
               let newStateStk = pop ((s,itl)::rem) (LENGTH r)
               in
                 if newStateStk = [] then
                   NONE
                 else
                   (let topitl = SND (HD newStateStk) in
                    let nx = FST m topitl (NTS l)
                    in
                      if nx = [] then
                        NONE
                      else
                        (let ns = (NTS l,nx)
                         in
                           SOME
                             (sym::rst,[(ns,p)] ++ newStk,
                              push newStateStk ns)))))
End

Definition parse:
  parse mac (inp, os, ((s, itl)::rem)) =
    case mac of NONE => NONE
    | (SOME m) =>
        case inp of [] => NONE
            | [e] =>
                (let newState = getState m itl e in
                     case newState of NA => NONE
                       | (GOTO st) => NONE
                       | (REDUCE ru) => doReduce m ([e], os, ((s, itl)::rem)) ru)
            | (sym::rst) =>
                 (let newState = getState m itl sym in
                     case newState of NA => NONE
                       | (GOTO st) =>
                         if (isNonTmnlSym sym) then NONE
                         else (* shift goto *)
                             SOME (rst,((sym,st),Leaf (sym2Str sym))::os, push ((s, itl)::rem) (sym,st))
                           | (REDUCE ru) => doReduce m ((sym::rst), os, ((s, itl)::rem)) ru)
End

Definition mwhile:
  mwhile g f s =
    OWHILE (\opt. case opt of NONE => F | SOME s => g s)
           (\opt. case opt of NONE => NONE | SOME s => f s)
           (SOME s)
End

Definition parser:
  parser (initState, eof, oldS) m sl =
    let
      out = (mwhile (\s. ~(exitCond (eof,NTS oldS) s))
                    (\(sli,stli,csli).parse m (sli,stli, csli))
                    (init initState sl))
    in
      case out of NONE => NONE
                | (SOME (SOME (slo,[(st1,pt)],cs))) => SOME (SOME pt)
                | SOME (NONE) => SOME (NONE)
                | SOME _ => SOME NONE
End


val _ = export_theory ();
