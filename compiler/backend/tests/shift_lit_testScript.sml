(*
  End-to-end test that word64 shifts by a literal amount, including calls
  of the Word64 basis wrappers, compile to shifts by a constant in ClosLang.
  This checks that source_lift_consts does not lift the shift amount.
*)
Theory shift_lit_test[no_sig_docs]
Ancestors
  backend
Libs
  preamble

(*
  A Word64 module with a shift wrapper, a call of the wrapper with a literal
  shift amount (f), a primitive shift by a literal amount (g), and a use of
  both so that dead-code elimination keeps them.
*)
Definition shift_prog_def:
  shift_prog =
    [Dmod «Word64»
       [Dlet NoLocs (Pvar «<<»)
          (Fun «a» (Fun «b» (App (Arith (Shift Lsl) (WordT W64))
                                 [Var (Short «a»); Var (Short «b»)])))];
     Dlet NoLocs (Pvar «f»)
       (Fun «w» (App Opapp [App Opapp [Var (Long «Word64» (Short «<<»));
                                       Var (Short «w»)];
                            Lit (Word64 3w)]));
     Dlet NoLocs (Pvar «g»)
       (Fun «w» (App (Arith (Shift Lsl) (WordT W64))
                     [Var (Short «w»); Lit (Word64 5w)]));
     Dlet NoLocs Pany
       (Con NONE [App Opapp [Var (Short «f»); Lit (Word64 1w)];
                  App Opapp [Var (Short «g»); Lit (Word64 1w)]])]
End

(*
  After all source-to-source passes and source_to_flat, both shift amounts
  are still literals, and the wrapper call has been inlined to the primitive.
*)
Theorem to_flat_shift_lit[local]:
  SND (to_flat (c with source_conf := prim_src_config) shift_prog)
  =
    [Let (SourceLoc 2 2 1 1 ▷ 1) NONE
       (App (SourceLoc 2 2 1 1 ▷ 1) (GlobalVarAlloc 4) [])
       (Con (SourceLoc 2 2 1 1 ▷ 1) NONE []);
     App None (GlobalVarInit 0) [App None (Src Opref) [Con None NONE []]];
     Let None (SOME «..%»)
       (Fun «Word64_<<» «a»
          (Fun «Word64_<<» «b»
             (App None (Src (Arith (Shift Lsl) (WordT W64)))
                [Var_local None «a»; Var_local None «b»])))
       (Let None (SOME «<<») (Var_local None «..%»)
          (App None (GlobalVarInit 1) [Var_local None «<<»]));
     Let None (SOME «..%»)
       (Fun «f» «w»
          (App None (Src (Arith (Shift Lsl) (WordT W64)))
             [Var_local None «w»; Lit None (Word64 3w)]))
       (Let None (SOME «f») (Var_local None «..%»)
          (App None (GlobalVarInit 2) [Var_local None «f»]));
     Let None (SOME «..%»)
       (Fun «g» «w»
          (App None (Src (Arith (Shift Lsl) (WordT W64)))
             [Var_local None «w»; Lit None (Word64 5w)]))
       (Let None (SOME «g») (Var_local None «..%»)
          (App None (GlobalVarInit 3) [Var_local None «g»]));
     Let None (SOME «..%»)
       (Con None NONE
          [App None (Src Opapp)
             [App None (GlobalVarLookup 2) []; Lit None (Word64 1w)];
           App None (Src Opapp)
             [App None (GlobalVarLookup 3) []; Lit None (Word64 1w)]])
       (Con None NONE [])]
Proof
  EVAL_TAC
QED

(*
  Consequently flat_to_clos compiles both to shifts by a constant
  (WordShift), while the wrapper itself uses a variable shift (WordShiftVar).
*)
Theorem to_clos_shift_lit[local]:
  SND (to_clos (c with source_conf := prim_src_config) shift_prog)
  =
    [Let None
       [Op None (GlobOp AllocGlobal) [Op None (IntOp (Const 1)) []];
        Op None (BlockOp (Cons 0)) []]
       (Op None (GlobOp (SetGlobal 0)) [Var None 1]);
     Let (SourceLoc 2 2 1 1 ▷ 1)
       [Let (SourceLoc 2 2 1 1 ▷ 1) []
          (Op (SourceLoc 2 2 1 1 ▷ 1) (GlobOp AllocGlobal)
             [Op (SourceLoc 2 2 1 1 ▷ 1) (IntOp (Const 4)) []])]
       (Op (SourceLoc 2 2 1 1 ▷ 1) (BlockOp (Cons 0)) []);
     Op None (GlobOp (SetGlobal 1))
       [Op None (MemOp Ref) [Op None (BlockOp (Cons 0)) []]];
     Let None
       [Fn «Word64_<<» NONE NONE 1
          (Fn «Word64_<<» NONE NONE 1
             (Op None (WordOp (WordShiftVar W64 Lsl)) [Var None 0; Var None 1]))]
       (Let None [Var None 0] (Op None (GlobOp (SetGlobal 2)) [Var None 0]));
     Let None
       [Fn «f» NONE NONE 1 (Op None (WordOp (WordShift W64 Lsl 3)) [Var None 0])]
       (Let None [Var None 0] (Op None (GlobOp (SetGlobal 3)) [Var None 0]));
     Let None
       [Fn «g» NONE NONE 1 (Op None (WordOp (WordShift W64 Lsl 5)) [Var None 0])]
       (Let None [Var None 0] (Op None (GlobOp (SetGlobal 4)) [Var None 0]));
     Let None
       [Op None (BlockOp (Cons 0))
          [App None NONE (Op None (GlobOp (Global 4)) [])
             [Op None (BlockOp (Constant (ConstWord64 1w))) []];
           App None NONE (Op None (GlobOp (Global 3)) [])
             [Op None (BlockOp (Constant (ConstWord64 1w))) []]]]
       (Op None (BlockOp (Cons 0)) [])]
Proof
  EVAL_TAC
QED
