(*
  Compilation from timeLang to panLang
*)

open preamble pan_commonTheory mlintTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry
        ["pan_common", "mlint", "timeLang", "panLang"];

Definition ohd_def:
  (ohd [] = (0:num,[])) ∧
  (ohd (x::xs) = x)
End


Definition ffiBufferAddr_def:
  ffiBufferAddr = 4000w:'a word
End


Definition ffiBufferSize_def:
  ffiBufferSize =  (bytes_in_word + 1w): 'a word
End


Definition genShape_def:
  genShape n = Comb (REPLICATE n One)
End


Definition mkClks_def:
  mkClks vname n = REPLICATE n (Var vname)
End


Definition emptyConsts_def:
  emptyConsts n = REPLICATE n (Const 0w)
End


Definition indicesOf_def:
  indicesOf xs ys = MAP (λn. findi n xs) ys
End


Definition resetTermClocks_def:
  resetTermClocks v clks tclks =
  MAPi (λn e.
         if (MEM e tclks)
         then (Const 0w)
         else Field n (Var v))
       clks
End


Definition waitTimes_def:
  waitTimes =
    list$MAP2 (λt e. Op Sub [Const (n2w t); e])
End


Definition minOp_def:
  (minOp v [] = Skip) ∧
  (minOp v (e::es) =
    Seq (If (Cmp Lower e (Var v)) (Assign v e) Skip)
        (minOp v es))
End


Definition minExp_def:
  (minExp v [] = Skip) ∧
  (minExp v (e::es) = Seq (Assign v e) (minOp v es))
End


Definition compTerm_def:
  (compTerm (clks:mlstring list) (Tm io cnds tclks loc wt)) : 'a prog =
  let waitClks = indicesOf clks (MAP SND wt);
      return   = Return
                 (Struct
                  [Var «newClks»;  Var «waitSet»;
                   Var «wakeUpAt»; Label (toString loc)])
  in
    decs [
        («waitSet»,   case wt of [] => Const 1w | wt => Const 0w); (* not waitSet *)
        («wakeUpAt»,  Const 0w);
        («newClks»,   Struct (resetTermClocks «clks» clks tclks));
        («waitTimes», Struct (emptyConsts (LENGTH wt)))
      ]
         (nested_seq
          [Assign «waitTimes»
                  (Struct (
                    waitTimes
                     (MAP FST wt)
                     (MAP (λn. Field n (Var «newClks»)) waitClks)));
           minExp «wakeUpAt» (MAPi (λn wt. Field n (Var «waitTimes»)) wt);
           case io of
           | (Input insig)   => return
           | (Output outsig) =>
               decs
               [(«ptr1»,Const 0w);
                («len1»,Const 0w);
                («ptr2»,Const ffiBufferAddr);
                («len2»,Const ffiBufferSize)
               ] (Seq
                  (ExtCall (strlit (toString outsig)) «ptr1» «len1» «ptr2» «len2»)
                  return)
          ])
End


Definition compExp_def:
  (compExp _ _ (ELit t) = Const (n2w t)) ∧
  (compExp clks vname (EClock clk) =
     Field (findi clk clks) (Var vname)) ∧
  (compExp clks vname (ESub e1 e2) =
     Op Sub [compExp clks vname e1;
             compExp clks vname e2])
End

Definition compCondition_def:
  (compCondition clks vname (CndLt e1 e2) =
     Cmp Lower
         (compExp clks vname e1)
         (compExp clks vname e2)) ∧
  (compCondition clks vname (CndLe e1 e2) =
     Op Or [Cmp Lower
                (compExp clks vname e1)
                (compExp clks vname e2);
            Cmp Equal
                (compExp clks vname e1)
                (compExp clks vname e2)])
End

Definition compConditions_def:
  (compConditions clks vname [] = Const 1w) ∧
  (compConditions clks vname cs =
     Op And (MAP (compCondition clks vname) cs))
End

Definition compTerms_def:
  (compTerms clks vname [] = Skip) ∧
  (compTerms clks vname (t::ts) =
   let cds = termConditions t
   in
   If (compConditions clks vname cds)
      (compTerm clks t)
      (compTerms clks vname ts))
End

Definition compLocation_def:
  compLocation clks (loc,ts) =
  let n = LENGTH clks in
    (toString loc,
     [(«clks», genShape n)],
     compTerms clks «clks» ts)
End

Definition compProg_def:
  (compProg clks [] = []) ∧
  (compProg clks (p::ps) =
    compLocation clks p :: compProg clks ps)
End

Definition comp_def:
  comp prog =
    compProg (clksOf prog) prog
End


Definition fieldsOf_def:
  fieldsOf e n =
    MAP (λn. Field n e) (GENLIST I n)
End


Definition normalisedClks_def:
  normalisedClks v1 v2 n =
  MAP2 (λx y. Op Sub [x;y])
       (mkClks v1 n)
       (fieldsOf (Var v2) n)
End

Definition adjustClks_def:
  adjustClks systime (e:'a panLang$exp) v2 n =
  MAP2 (λx y. if x = Const 0w then ((Var systime):'a panLang$exp)
              else y)
       (destruct e)
       (fieldsOf (Var v2) n)
End


Definition check_input_time_def:
  check_input_time =
    nested_seq [
        ExtCall «get_ffi» «ptr1» «len1» «ptr2» «len2» ;
        Assign  «sysTime» (Load One (Var «ptr2»)) ;
        Assign  «isInput» (Load One
                           (Op Add [Var «ptr2»;
                                    Const bytes_in_word]))
      ]
End

(*
Definition check_input_time_def:
  check_input_time =
    nested_seq [
        ExtCall «get_time» «ptr1» «len1» «ptr2» «len2» ;
        Assign  «sysTime» (Load One (Var «ptr2»)) ;
        ExtCall «check_input» «ptr1» «len1» «ptr2» «len2» ;
        Assign  «isInput» (Load One (Var «ptr2»))]
End
*)

Definition wait_def:
  wait =
    Op And [Var «isInput»; (* Not *)
            Op Or
            [Var «waitSet»; (* Not *)
             Cmp Lower (Var «sysTime») (Var «wakeUpAt»)]]
End


Definition wait_input_time_limit_def:
  wait_input_time_limit =
    While wait check_input_time
End


Definition task_controller_def:
  task_controller clksLength =
  let
    rt = Var «taskRet» ;
    nClks     = Field 0 rt;
    nWaitSet  = Field 1 rt;
    nwakeUpAt = Field 2 rt;
    nloc      = Field 3 rt
  in
    (nested_seq [
        wait_input_time_limit;
        Call (Ret «taskRet» NONE) (Var «loc»)
             [Struct (normalisedClks «sysTime» «clks» clksLength)];
        Assign «clks» (Struct (adjustClks «sysTime» nClks «clks» clksLength));
        Assign «waitSet» nWaitSet ;
        Assign «wakeUpAt» (Op Add [Var «sysTime»; nwakeUpAt]);
        Assign «loc» nloc;
        check_input_time])
End


Definition start_controller_def:
  start_controller (ta_prog:program) =
  let
    prog = FST ta_prog;
    initLoc = FST (ohd prog);
    initWakeUp = SND ta_prog;
    clksLength = nClks prog
  in
    decs
    [(«loc», Label (toString initLoc));
     («waitSet»,
      case initWakeUp of NONE => Const 1w | _ => Const 0w);  (* not waitSet *)
     («isInput», Const 1w); (* not isInput, active low *)
     («wakeUpAt», Const 0w);
     («sysTime», Const 0w);
     («ptr1», Const 0w);
     («len1», Const 0w);
     («ptr2», Const ffiBufferAddr);
     («len2», Const ffiBufferSize);
     («taskRet»,
      Struct [Struct (emptyConsts clksLength);
              Const 0w; Const 0w; Const 0w]);
     («clks»,Struct (emptyConsts clksLength))
    ]
    (nested_seq
     [
       check_input_time;
       Assign «clks» (Struct (mkClks «sysTime» clksLength));
       Assign «wakeUpAt»
              (case initWakeUp of
               | NONE => Const 0w
               | SOME n => Op Add [Var «sysTime»; Const (n2w n)]);
       While (Const 1w)
             (task_controller clksLength)
     ])
End



val _ = export_theory();
